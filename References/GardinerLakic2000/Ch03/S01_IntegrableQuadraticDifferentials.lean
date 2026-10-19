import References.GardinerLakic2000.Ch02.S10_DimensionQuadraticDifferentials

/-!
# Gardiner–Lakic 2000, Ch. 3 §3.1 Integrable quadratic differentials (with the chapter introduction)

Source `teichmuller.txt`, lines 1988–2213 (Chapter 3, introduction and §3.1).

* Formula (3.1) (the norm `‖φ‖ = ∬_R |φ|`, l. 1996) — exists: `LiZhongQC.quadDiffNorm`
* Formulas (3.2), (3.6) (the pairing `(φ, μ) = ∬_R φμ`, l. 2006, 2149) — `pairingRS`
* Formula (3.3) (`V = Pμ`, l. 2016) — exists: `LiZhongQC.normalizedCauchyTOn` (the same kernel
  1/(ζ − z) + (z − 1)/ζ − z/(ζ − 1) = z(z − 1)/(ζ(ζ − 1)(ζ − z)), over the whole plane)
* Formula (3.4) (Zygmund-bounded vector fields on the unit circle, l. 2066–2071; cited in Ch. 16, l. 12381) —
  `IsZygmundBoundedVF`
* Definition (quadratic differential, l. 2079) — exists: `LiZhongQC.IsDiffFamilyAE` (with m = 2, n = 0)
* Definition (`L₁(R)` and `A(R)`, l. 2079) — `integrableQDSet`, `integrableHolQDSet`
* Theorem 1 (l. 2081; its argument is cited in Ch. 4) — `thm3_1`
* Definition (Beltrami differentials `L∞(R)`, l. 2085–2097) — exists: `GardinerLakic2000.beltramiSpace` (§2.4)
* Theorem 2 (l. 2099) — `IsBoundedFunctionalOn`, `dualNormOn`, `thm3_2_a`, `thm3_2_b`
* Definition 1 (degenerating sequence, l. 2122; used throughout Ch. 4, 14, 15) — `IsDegeneratingSeq`
* Unlabelled (no degenerating sequences when `A(R)` is finite dimensional, l. 2124) — `para3_1_finite_dim`
* Theorem 3 (l. 2126; cited in Ch. 4, l. 4176) — `thm3_3`
* Definition (`Z(R)`, the dual of `A(R)`, with the dual norm, l. 2139–2149) — `zSpace`
* Definition (`L₁(Δ, Γ)` and `L∞(Δ, Γ)`, automorphic forms (3.7), (3.8), l. 2159–2197) — `integrableAutomorphicL1`,
  `beltramiSpaceGamma` (on the project's automorphy predicate for Beltrami coefficients, which is (3.8))
* Definition (`A(Δ, Γ)`, l. 2167–2180) — exists: `LiZhongQC.integrableAutomorphicQD` (in the ℍ model, leader ruling
  A0.2)
* Unlabelled (`φ ↦ φ̃` is an isometry of `A(R)` onto `A(Δ, Γ)`, with the same correspondence for Beltrami
  differentials and pairings, l. 2153–2210; used throughout) — `liftQD`, `liftBeltrami`, `para3_1_lift_isometry`
* Unlabelled (`A(Δ, Γ)* ≅ L∞(Δ, Γ)/N`, l. 2210) — `para3_1_dual_gamma`

Not items: the introduction's claims on tangent spaces (l. 2023–2076, announced for later chapters); (3.5) (l. 2132, a
step of the proof of Theorem 3); "`A(R)` is not reflexive when infinite dimensional" (l. 2120, an announcement); the
non-integrability over Δ (l. 2212, U−). Modelling: the book's disc model of §3.1 is read in the ℍ model (leader ruling
A0.2: `Γ ≤ SL(2,ℝ)`, `p : ℍ → R` a uniformization, `F` a measurable fundamental domain). Chart families are indexed
by the points of `R` (the coefficient in the preferred chart at `x`). `pairingRS` computes `∬_R φμ` on one chart
partition (chosen); the form `φμ` is a density, so the value does not depend on the partition. Functionals on the
sets of chart families (or of functions) are arbitrary maps `V`, restricted by `IsBoundedFunctionalOn` (additive and
homogeneous on the set, bounded by `C‖φ‖`); their values off the set are never read.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsDiffFamilyAE holQuadDiffSubmodule quadDiffNorm IsChartPartition IsGammaCompatible
  IsBeltramiCoeff upperHalf phiArea integrableAutomorphicQD beltramiPairing IsFuchsian ActsFreely IsUniformization
  IsFundamentalDomainH)

/-- **Formula (3.4)** (Ch. 3 introduction, l. 2066–2071). `V` is a Zygmund-bounded vector field on the unit circle:
`V(e^{iθ})/(i e^{iθ})` is real and `|V(e^{i(θ+t)}) + V(e^{i(θ−t)}) − 2V(e^{iθ})| ≤ M |t|`. -/
def IsZygmundBoundedVF (V : ℂ → ℂ) : Prop :=
  (∀ θ : ℝ, (V (exp (θ * I)) / (I * exp (θ * I))).im = 0) ∧
    ∃ M : ℝ, ∀ θ t : ℝ, ‖V (exp ((θ + t) * I)) + V (exp ((θ - t) * I)) - 2 * V (exp (θ * I))‖ ≤ M * |t|

section Surface

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

open scoped Classical in
/-- **Formulas (3.2), (3.6)** (l. 2006, 2102). The pairing `(φ, μ) = ∬_R φ μ dx dy` of a quadratic differential and a
Beltrami differential (a density), computed on a chosen chart partition of `R` (junk `0` if there is none). -/
def pairingRS (φ μ : R → ℂ → ℂ) : ℂ :=
  if h : ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P then
    ∑' i, ∫ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i, φ (h.choose i) z * μ (h.choose i) z
  else 0

/-- **Definition** (§3.1, l. 2079). `L₁(R)`: the integrable (measurable) quadratic differentials on `R`. -/
def integrableQDSet (R : Type u) [TopologicalSpace R] [ChartedSpace ℂ R] : Set (R → ℂ → ℂ) :=
  {q | IsDiffFamilyAE 2 0 q ∧ (∀ x : R, AEStronglyMeasurable (q x) (volume.restrict (chartAt ℂ x).target)) ∧
    quadDiffNorm q < ⊤}

/-- **Definition** (§3.1, l. 2079). `A(R)`: the integrable holomorphic quadratic differentials on `R`. -/
def integrableHolQDSet (R : Type u) [TopologicalSpace R] [ChartedSpace ℂ R] : Set (R → ℂ → ℂ) :=
  {q | q ∈ holQuadDiffSubmodule R ∧ quadDiffNorm q < ⊤}

/-- Helper (B-SURF, §3.1). A surface uniformized by `ℍ` is second countable: the uniformization `p` is continuous,
surjective and open (a covering map), hence an open quotient map of the second countable `ℍ`. -/
theorem gl31_secondCountable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) : SecondCountableTopology R := by
  exact Topology.IsOpenQuotientMap.secondCountableTopology ⟨hp.2.2.1, hp.1.continuous, hp.1.isOpenMap⟩

/-- Helper (B-SURF, §3.1). On a second countable nonempty charted space there is a chart partition subordinate to
given open neighbourhoods `V y ∋ y` inside the chart sources (`P i ⊆ V (x i)`): the countable version of
`LiZhongQC.s26_exists_chartPartition` (a countable subcover replaces the finite one). -/
theorem gl31_exists_chartPartition [SecondCountableTopology R] [Nonempty R] (V : R → Set R)
    (hVo : ∀ y, IsOpen (V y)) (hVy : ∀ y, y ∈ V y) (hVs : ∀ y, V y ⊆ (chartAt ℂ y).source) :
    ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P ∧ ∀ i, P i ⊆ V (x i) := by
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  have hcov : ∀ y : R, ∃ t ∈ T, y ∈ V t := fun y => by
    have hy : y ∈ ⋃ i, V i := mem_iUnion.2 ⟨y, hVy y⟩
    rw [← hTU] at hy
    obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.1 hy
    exact ⟨t, ht, hyt⟩
  obtain ⟨y₀⟩ := ‹Nonempty R›
  have hTne : T.Nonempty := by
    obtain ⟨t, ht, -⟩ := hcov y₀
    exact ⟨t, ht⟩
  obtain ⟨x, rfl⟩ := hTc.exists_eq_range hTne
  refine ⟨x, disjointed (fun i => V (x i)), ⟨fun i => ⟨?_, ?_⟩, disjoint_disjointed _, ?_⟩,
    fun i => disjointed_subset _ i⟩
  · exact (disjointed_subset _ i).trans (hVs (x i))
  · rw [disjointed_eq_inter_compl]
    exact LiZhongQC.s26_measurableSet_chart_image (x i) (fun j => V (x j)) (fun j => hVo (x j)) i (hVs (x i))
  · rw [iUnion_disjointed, eq_univ_iff_forall]
    intro y
    obtain ⟨t, ⟨i, rfl⟩, hyt⟩ := hcov y
    exact mem_iUnion.2 ⟨i, hyt⟩

/-- Helper (B-SURF, §3.1). Change of variables on a sheet. If `W ⊆ ℍ` is open, `p̂ = LiZhongQC.utm_pext p` is
injective on `W` and maps `W` into the source of the chart at `x`, then for measurable `E ⊆ W` and any `G ≥ 0`,
`∫_{φₓ(p̂ E)} G = ∫_E |h′|² · G ∘ h` with `h = φₓ ∘ p̂` (holomorphic and injective on `W`, Jacobian `|h′|²`). -/
theorem gl31_lintegral_sheet [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) (x : R) {W : Set ℂ} (hWo : IsOpen W)
    (hWH : W ⊆ upperHalf) (hWi : InjOn (LiZhongQC.utm_pext p) W)
    (hWx : ∀ z ∈ W, LiZhongQC.utm_pext p z ∈ (chartAt ℂ x).source) {E : Set ℂ} (hEm : MeasurableSet E)
    (hEW : E ⊆ W) (G : ℂ → ℝ≥0∞) :
    ∫⁻ w in chartAt ℂ x '' (LiZhongQC.utm_pext p '' E), G w =
      ∫⁻ z in E, ENNReal.ofReal (‖deriv (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) z‖ ^ 2) *
        G (chartAt ℂ x (LiZhongQC.utm_pext p z)) := by
  -- `W` open is not needed: the chart expression is holomorphic at every point of `W` because `p̂` maps it into the
  -- chart source (`utm_a_differentiableAt`); the statement stays true without `hWo`.
  have _hWo := hWo
  have hd : ∀ z ∈ W, DifferentiableAt ℂ (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) z := fun z hz =>
    LiZhongQC.utm_a_differentiableAt hp.2.1 x (hWH hz) (hWx z hz)
  have hinj : InjOn (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) E := fun z hz w hw hzw =>
    hWi (hEW hz) (hEW hw) ((chartAt ℂ x).injOn (hWx z (hEW hz)) (hWx w (hEW hw)) hzw)
  rw [image_image, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hEm
    (fun z hz => ((hd z (hEW hz)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt) hinj]
  refine setLIntegral_congr_fun hEm fun z hz => ?_
  have hdz := hd z (hEW hz)
  have hdet : (fderiv ℝ (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) z).det =
      ‖deriv (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) z‖ ^ 2 := by
    have e := LiZhongQC.det_fderiv_eq_jacobian (hdz.restrictScalars ℝ)
    rw [show (fderiv ℝ (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) z).det =
      LinearMap.det (fderiv ℝ (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) z : ℂ →ₗ[ℝ] ℂ) from rfl, e]
    show ‖LiZhongQC.dz (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) z‖ ^ 2 -
      ‖LiZhongQC.dzbar (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) z‖ ^ 2 = _
    rw [LiZhongQC.dz_eq_deriv hdz, (LiZhongQC.cauchyRiemann_iff.1 hdz).2, norm_zero]
    ring
  rw [hdet, abs_of_nonneg (by positivity)]

/-- Helper (B-SURF, §3.1). For `E ⊆ ℍ` and `z ∈ ℍ`, `p̂ z` lies in `p̂ E` iff some `γ ∈ Γ` moves `z` into `E` (the
fibres of the uniformization are the orbits; `p̂ = LiZhongQC.utm_pext p`). -/
theorem gl31_mem_over {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) {E : Set ℂ} (hEH : E ⊆ upperHalf) {z : ℂ} (hz : z ∈ upperHalf) :
    LiZhongQC.utm_pext p z ∈ LiZhongQC.utm_pext p '' E ↔ ∃ γ ∈ Γ, LiZhongQC.h36p_m γ z ∈ E := by
  have hpe : ∀ w (hw : 0 < w.im), LiZhongQC.utm_pext p w = p ⟨w, hw⟩ := fun w hw => by
    rw [LiZhongQC.utm_a_pext_eq p hw, UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  constructor
  · rintro ⟨e, he, hez⟩
    have heH : 0 < e.im := hEH he
    rw [hpe e heH, hpe z hz] at hez
    obtain ⟨γ, hγ, hγz⟩ := (hp.2.2.2 ⟨z, hz⟩ ⟨e, heH⟩).1 hez.symm
    refine ⟨γ, hγ, ?_⟩
    have h1 : LiZhongQC.h36p_m γ z = e := (LiZhongQC.h36p_m_coe γ ⟨z, hz⟩).trans (by rw [hγz])
    rw [h1]
    exact he
  · rintro ⟨γ, hγ, hγE⟩
    refine ⟨LiZhongQC.h36p_m γ z, hγE, ?_⟩
    exact LiZhongQC.utm_b_pext_mob hp hγ hz

/-- Helper (B-SURF, §3.1). For measurable `E ⊆ ℍ` and measurable `F ⊆ ℍ`, the part of `F` over `p̂ E` is measurable:
it is `F ∩ ⋃_{γ ∈ Γ} γ⁻¹(E)`, a countable union (a Fuchsian group is countable). -/
theorem gl31_measurableSet_over {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {F : Set ℂ} (hFm : MeasurableSet F)
    (hFH : F ⊆ upperHalf) {E : Set ℂ} (hEm : MeasurableSet E) (hEH : E ⊆ upperHalf) :
    MeasurableSet (F ∩ LiZhongQC.utm_pext p ⁻¹' (LiZhongQC.utm_pext p '' E)) := by
  have hΓc : Countable Γ := (LiZhongQC.h36p_countable hΓ).to_subtype
  have heq : F ∩ LiZhongQC.utm_pext p ⁻¹' (LiZhongQC.utm_pext p '' E) =
      F ∩ ⋃ γ : Γ, LiZhongQC.h36p_m γ.1 ⁻¹' E := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_iUnion]
    constructor
    · rintro ⟨hzF, hz⟩
      obtain ⟨γ, hγ, hγE⟩ := (gl31_mem_over hp hEH (hFH hzF)).1 hz
      exact ⟨hzF, ⟨γ, hγ⟩, hγE⟩
    · rintro ⟨hzF, γ, hγE⟩
      exact ⟨hzF, (gl31_mem_over hp hEH (hFH hzF)).2 ⟨γ.1, γ.2, hγE⟩⟩
  rw [heq]
  exact hFm.inter (MeasurableSet.iUnion fun γ => LiZhongQC.h36p_m_measurable γ.1 hEm)

/-- Helper (B-SURF, §3.1). Folding onto a fundamental domain. For a `Γ`-invariant density `h ≥ 0` on `ℍ`
(`h(γz) |cz + d|⁻⁴ = h(z)`) and a measurable `E ⊆ ℍ` on which `p̂` is injective, `∫_E h = ∫_{F ∩ p̂⁻¹(p̂ E)} h`: both
sides are `1/m` times the integral of `h` against the `Γ`-translates of `F` (`LiZhongQC.h36p_c_sum_measure`), and
for `z ∈ F` the `γ ∈ Γ` with `γz ∈ E` form one class `±γ₀` (freeness of the action). -/
theorem gl31_lintegral_fold {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {h : ℂ → ℝ≥0∞} (hh : AEMeasurable h (volume.restrict upperHalf))
    (hinv : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      h (LiZhongQC.h36p_m γ z) * ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) = h z)
    {E : Set ℂ} (hEm : MeasurableSet E) (hEH : E ⊆ upperHalf) (hEi : InjOn (LiZhongQC.utm_pext p) E) :
    ∫⁻ z in E, h z = ∫⁻ z in F ∩ LiZhongQC.utm_pext p ⁻¹' (LiZhongQC.utm_pext p '' E), h z := by
  classical
  have hsum := LiZhongQC.h36p_c_sum_measure hΓ hF
  obtain ⟨hFH, hFm, -, -, -⟩ := hF
  have hΓc : Countable Γ := (LiZhongQC.h36p_countable hΓ).to_subtype
  have hm0 : (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (LiZhongQC.h36p_mult_pos (Γ := Γ)).ne'
  have hmtop : (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  set ν : Γ → Measure ℂ := fun γ => ((volume.restrict F).withDensity
    (fun z => ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4))).map (LiZhongQC.h36p_m γ.1) with hν
  set T : Set ℂ := ⋃ γ : Γ, LiZhongQC.h36p_m γ.1 ⁻¹' E with hTdef
  have hTm : MeasurableSet T := MeasurableSet.iUnion fun γ => LiZhongQC.h36p_m_measurable γ.1 hEm
  have hFT : F ∩ LiZhongQC.utm_pext p ⁻¹' (LiZhongQC.utm_pext p '' E) = F ∩ T := by
    ext z
    simp only [mem_inter_iff, mem_preimage, hTdef, mem_iUnion]
    constructor
    · rintro ⟨hzF, hz⟩
      obtain ⟨γ, hγ, hγE⟩ := (gl31_mem_over hp hEH (hFH hzF)).1 hz
      exact ⟨hzF, ⟨γ, hγ⟩, hγE⟩
    · rintro ⟨hzF, γ, hγE⟩
      exact ⟨hzF, (gl31_mem_over hp hEH (hFH hzF)).2 ⟨γ.1, γ.2, hγE⟩⟩
  have hhs : AEMeasurable h (Measure.sum ν) := by
    rw [hsum]
    exact hh.smul_measure _
  have hhF : AEMeasurable h (volume.restrict F) := hh.mono_measure (Measure.restrict_mono hFH le_rfl)
  -- each term of the measure identity, folded back to `F` by the invariance of `h`
  have hterm : ∀ γ : Γ, ∫⁻ z, E.indicator h z ∂(ν γ) =
      ∫⁻ z in F, E.indicator (fun _ => (1 : ℝ≥0∞)) (LiZhongQC.h36p_m γ.1 z) * h z := by
    intro γ
    have hhγ : AEMeasurable (E.indicator h) (ν γ) := (hhs.mono_measure (Measure.le_sum ν γ)).indicator hEm
    have hρ : Measurable fun z : ℂ => ENNReal.ofReal (‖(γ.1 1 0 : ℂ) * z + γ.1 1 1‖⁻¹ ^ 4) := by
      fun_prop
    rw [hν, lintegral_map' hhγ (LiZhongQC.h36p_m_measurable γ.1).aemeasurable,
      lintegral_withDensity_eq_lintegral_mul_non_measurable _ hρ (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine setLIntegral_congr_fun hFm fun z hz => ?_
    simp only [Pi.mul_apply]
    by_cases hzE : LiZhongQC.h36p_m γ.1 z ∈ E
    · rw [indicator_of_mem hzE, indicator_of_mem hzE, one_mul, mul_comm]
      exact hinv γ.1 γ.2 z (hFH hz)
    · rw [indicator_of_notMem hzE, indicator_of_notMem hzE, mul_zero, zero_mul]
  -- the count of the translates of `z ∈ F` in `E`
  have hcount : ∀ z ∈ F, ∑' γ : Γ, E.indicator (fun _ => (1 : ℝ≥0∞)) (LiZhongQC.h36p_m γ.1 z) =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * T.indicator (fun _ => (1 : ℝ≥0∞)) z := by
    intro z hzF
    have hzH : z ∈ upperHalf := hFH hzF
    by_cases hzT : z ∈ T
    · rw [indicator_of_mem hzT, mul_one]
      obtain ⟨γ₀, hγ₀⟩ := mem_iUnion.1 hzT
      have hP : ∀ γ ∈ Γ, LiZhongQC.h36p_m γ z ∈ E ↔ γ = γ₀.1 ∨ γ = -γ₀.1 := by
        intro γ hγ
        constructor
        · intro hγE
          have h1 : LiZhongQC.utm_pext p (LiZhongQC.h36p_m γ z) =
              LiZhongQC.utm_pext p (LiZhongQC.h36p_m γ₀.1 z) :=
            (LiZhongQC.utm_b_pext_mob hp hγ hzH).trans (LiZhongQC.utm_b_pext_mob hp γ₀.2 hzH).symm
          have h2 : LiZhongQC.h36p_m γ z = LiZhongQC.h36p_m γ₀.1 z := hEi hγE hγ₀ h1
          have h3 : γ • (⟨z, hzH⟩ : UpperHalfPlane) = γ₀.1 • ⟨z, hzH⟩ := by
            refine UpperHalfPlane.ext ?_
            rw [← LiZhongQC.h36p_m_coe, ← LiZhongQC.h36p_m_coe]
            exact h2
          have h4 : (γ₀.1⁻¹ * γ) • (⟨z, hzH⟩ : UpperHalfPlane) = ⟨z, hzH⟩ := by
            rw [mul_smul, h3, inv_smul_smul]
          rcases hfree _ (Γ.mul_mem (Γ.inv_mem γ₀.2) hγ) _ h4 with h5 | h5
          · exact Or.inl (inv_mul_eq_one.1 h5).symm
          · refine Or.inr ?_
            calc γ = γ₀.1 * (γ₀.1⁻¹ * γ) := (mul_inv_cancel_left _ _).symm
              _ = -γ₀.1 := by rw [h5, mul_neg_one]
        · rintro (rfl | rfl)
          · exact hγ₀
          · rw [LiZhongQC.h36p_a_m_neg]
            exact hγ₀
      have hc := LiZhongQC.h36p_a_count (Γ := Γ) (P := fun γ => LiZhongQC.h36p_m γ z ∈ E) γ₀.2 hP 1
      rw [mul_one] at hc
      rw [← hc]
      refine tsum_congr fun γ => ?_
      simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    · rw [indicator_of_notMem hzT, mul_zero]
      have h0 : ∀ γ : Γ, E.indicator (fun _ => (1 : ℝ≥0∞)) (LiZhongQC.h36p_m γ.1 z) = 0 := fun γ =>
        indicator_of_notMem (s := E) (f := fun _ => (1 : ℝ≥0∞)) (fun hγE => hzT (mem_iUnion.2 ⟨γ, hγE⟩))
      simp only [h0, tsum_zero]
  have key : (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * ∫⁻ z in E, h z =
      (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * ∫⁻ z in F ∩ T, h z := by
    have e1 : ∫⁻ z, E.indicator h z ∂(Measure.sum ν) =
        (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * ∫⁻ z in E, h z := by
      rw [hsum, lintegral_smul_measure, lintegral_indicator hEm, Measure.restrict_restrict hEm,
        inter_eq_left.2 hEH, smul_eq_mul]
    rw [← e1, lintegral_sum_measure]
    calc ∑' γ : Γ, ∫⁻ z, E.indicator h z ∂(ν γ)
        = ∑' γ : Γ, ∫⁻ z in F, E.indicator (fun _ => (1 : ℝ≥0∞)) (LiZhongQC.h36p_m γ.1 z) * h z :=
          tsum_congr hterm
      _ = ∫⁻ z in F, ∑' γ : Γ, E.indicator (fun _ => (1 : ℝ≥0∞)) (LiZhongQC.h36p_m γ.1 z) * h z := by
          refine (lintegral_tsum fun γ => ?_).symm
          exact ((measurable_const.indicator hEm).comp (LiZhongQC.h36p_m_measurable γ.1)).aemeasurable.mul hhF
      _ = ∫⁻ z in F, (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * T.indicator h z := by
          refine setLIntegral_congr_fun hFm fun z hz => ?_
          rw [ENNReal.tsum_mul_right, hcount z hz, mul_assoc]
          congr 1
          by_cases hzT : z ∈ T
          · rw [indicator_of_mem hzT, indicator_of_mem hzT, one_mul]
          · rw [indicator_of_notMem hzT, indicator_of_notMem hzT, zero_mul]
      _ = (Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1)) : ℝ≥0∞) * ∫⁻ z in F ∩ T, h z := by
          rw [lintegral_const_mul' _ _ hmtop, lintegral_indicator hTm, Measure.restrict_restrict hTm,
            inter_comm]
  rw [hFT]
  exact (ENNReal.mul_right_inj hm0 hmtop).1 key

/-- Helper (B-SURF, §3.1). Countably many sheets of `p` cover `R`: partial homeomorphisms `e j` of `ℍ` onto open sets of
`R` agreeing with `p` on their sources, whose targets cover `R` (`p` is a covering map, `R` is second countable). -/
theorem gl31_sheet_cover {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) :
    ∃ e : ℕ → OpenPartialHomeomorph UpperHalfPlane R, (∀ j, ∀ τ ∈ (e j).source, p τ = e j τ) ∧
      ∀ y : R, ∃ j, y ∈ (e j).target := by
  have hsc := gl31_secondCountable hp
  choose τ hτ using hp.2.2.1
  choose e he hpe using fun y => hp.1.isLocalHomeomorph (τ y)
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun y => (e y).target)
    fun y => (e y).open_target
  have hself : ∀ y, y ∈ (e y).target := fun y => by
    have h1 : e y (τ y) = y := by
      rw [← hpe y]
      exact hτ y
    have hm := (e y).map_source (he y)
    rwa [h1] at hm
  have hcov : ∀ y : R, ∃ t ∈ T, y ∈ (e t).target := fun y => by
    have hy : y ∈ ⋃ t, (e t).target := mem_iUnion.2 ⟨y, hself y⟩
    rw [← hTU] at hy
    obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.1 hy
    exact ⟨t, ht, hyt⟩
  have hTne : T.Nonempty := by
    obtain ⟨t, ht, -⟩ := hcov (p UpperHalfPlane.I)
    exact ⟨t, ht⟩
  obtain ⟨s, rfl⟩ := hTc.exists_eq_range hTne
  refine ⟨fun j => e (s j), fun j σ _ => by rw [hpe (s j)], fun y => ?_⟩
  obtain ⟨t, ⟨j, rfl⟩, hyt⟩ := hcov y
  exact ⟨j, hyt⟩

/-- Helper (B-SURF, §3.1). For an open `W ⊆ ℍ` mapped by `p̂` into the source of the chart at `x` and a measurable
`M ⊆ ℂ`, the set `W ∩ (φₓ ∘ p̂)⁻¹(M)` is measurable (`φₓ ∘ p̂` is continuous on `W`). -/
theorem gl31_measurableSet_lift {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (x : R) {W : Set ℂ} (hWo : IsOpen W) (hWH : W ⊆ upperHalf)
    (hWx : ∀ z ∈ W, LiZhongQC.utm_pext p z ∈ (chartAt ℂ x).source) {M : Set ℂ} (hM : MeasurableSet M) :
    MeasurableSet (W ∩ (fun z => chartAt ℂ x (LiZhongQC.utm_pext p z)) ⁻¹' M) := by
  classical
  have hc : ContinuousOn (fun z => chartAt ℂ x (LiZhongQC.utm_pext p z)) W := fun z hz =>
    (((chartAt ℂ x).continuousAt (hWx z hz)).comp
      (LiZhongQC.utm_a_continuousAt hp.1.continuous (hWH hz))).continuousWithinAt
  have hpw := hc.measurable_piecewise (continuousOn_const (c := (0 : ℂ))) hWo.measurableSet
  have heq : W ∩ (fun z => chartAt ℂ x (LiZhongQC.utm_pext p z)) ⁻¹' M =
      W ∩ (W.piecewise (fun z => chartAt ℂ x (LiZhongQC.utm_pext p z)) (fun _ => (0 : ℂ))) ⁻¹' M := by
    ext z
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hzW, hz⟩
      exact ⟨hzW, by rwa [piecewise_eq_of_mem _ _ _ hzW]⟩
    · rintro ⟨hzW, hz⟩
      exact ⟨hzW, by rwa [piecewise_eq_of_mem _ _ _ hzW] at hz⟩
  rw [heq]
  exact hWo.measurableSet.inter (hpw hM)

/-- Helper (B-SURF, §3.1). The unfolding identity on one chart piece: for `A` inside the source of the chart at `x`
with measurable chart image, the part of `F` over `A` is measurable and `∫_{φₓ(A)} g = ∫_{F ∩ p̂⁻¹(A)} h` (countably
many sheets, `gl31_sheet_cover`; `gl31_lintegral_sheet` and `gl31_lintegral_fold` on each). -/
theorem gl31_piece [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {h : ℂ → ℝ≥0∞} (hh : AEMeasurable h (volume.restrict upperHalf))
    (hinv : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      h (LiZhongQC.h36p_m γ z) * ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) = h z)
    (x : R) {A : Set R} (hAx : A ⊆ (chartAt ℂ x).source) (hAm : MeasurableSet (chartAt ℂ x '' A))
    (g : ℂ → ℝ≥0∞)
    (hg : ∀ z ∈ upperHalf, LiZhongQC.utm_pext p z ∈ A →
      ENNReal.ofReal (‖deriv (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) z‖ ^ 2) *
        g (chartAt ℂ x (LiZhongQC.utm_pext p z)) = h z) :
    MeasurableSet (F ∩ LiZhongQC.utm_pext p ⁻¹' A) ∧
      ∫⁻ w in chartAt ℂ x '' A, g w = ∫⁻ z in F ∩ LiZhongQC.utm_pext p ⁻¹' A, h z := by
  classical
  have hF' := hF
  obtain ⟨hFH, hFm, -, -, -⟩ := hF'
  obtain ⟨e, hpe, hcov⟩ := gl31_sheet_cover hp
  have hpe_coe : ∀ τ : UpperHalfPlane, LiZhongQC.utm_pext p τ = p τ := fun τ => by
    rw [LiZhongQC.utm_a_pext_eq p τ.coe_im_pos, UpperHalfPlane.ofComplex_apply]
  -- the disjointed sheet targets and the pieces of `A`
  set Q : ℕ → Set R := disjointed (fun j => (e j).target) with hQ
  set W' : ℕ → Set R := fun j => (e j).target ∩ (chartAt ℂ x).source with hW'
  have hAQ : ∀ j, A ∩ Q j = A ∩ (W' j ∩ ⋂ k < j, (W' k)ᶜ) := by
    intro j
    ext y
    simp only [hQ, hW', disjointed_eq_inter_compl, mem_inter_iff, mem_iInter, mem_compl_iff]
    constructor
    · rintro ⟨hyA, hyj, hyk⟩
      exact ⟨hyA, ⟨hyj, hAx hyA⟩, fun k hk h' => hyk k hk h'.1⟩
    · rintro ⟨hyA, ⟨hyj, -⟩, hyk⟩
      exact ⟨hyA, hyj, fun k hk h' => hyk k hk ⟨h', hAx hyA⟩⟩
  have hAjm : ∀ j, MeasurableSet (chartAt ℂ x '' (A ∩ Q j)) := by
    intro j
    rw [hAQ j, (chartAt ℂ x).injOn.image_inter hAx (inter_subset_left.trans inter_subset_right)]
    exact hAm.inter (LiZhongQC.s26_measurableSet_chart_image x W'
      (fun k => (e k).open_target.inter (chartAt ℂ x).open_source) j inter_subset_right)
  -- the lifts of the pieces
  set W : ℕ → Set ℂ := fun j => UpperHalfPlane.coe '' ((e j).source ∩ p ⁻¹' (chartAt ℂ x).source) with hW
  set E : ℕ → Set ℂ := fun j => UpperHalfPlane.coe '' ((e j).source ∩ p ⁻¹' (A ∩ Q j)) with hE
  have hWo : ∀ j, IsOpen (W j) := fun j => UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _
    ((e j).open_source.inter ((chartAt ℂ x).open_source.preimage hp.1.continuous))
  have hWH : ∀ j, W j ⊆ upperHalf := by
    rintro j _ ⟨τ, -, rfl⟩
    exact τ.coe_im_pos
  have hWi : ∀ j, InjOn (LiZhongQC.utm_pext p) (W j) := by
    rintro j _ ⟨τ, hτ, rfl⟩ _ ⟨σ, hσ, rfl⟩ hτσ
    rw [hpe_coe, hpe_coe, hpe j τ hτ.1, hpe j σ hσ.1] at hτσ
    rw [(e j).injOn hτ.1 hσ.1 hτσ]
  have hWx : ∀ j, ∀ z ∈ W j, LiZhongQC.utm_pext p z ∈ (chartAt ℂ x).source := by
    rintro j _ ⟨τ, hτ, rfl⟩
    rw [hpe_coe]
    exact hτ.2
  have hEW : ∀ j, E j ⊆ W j := by
    rintro j _ ⟨τ, hτ, rfl⟩
    exact ⟨τ, ⟨hτ.1, hAx hτ.2.1⟩, rfl⟩
  have hEH : ∀ j, E j ⊆ upperHalf := fun j => (hEW j).trans (hWH j)
  have himE : ∀ j, LiZhongQC.utm_pext p '' E j = A ∩ Q j := by
    intro j
    ext y
    constructor
    · rintro ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
      rw [hpe_coe]
      exact hτ.2
    · intro hy
      have hyt : y ∈ (e j).target := disjointed_subset _ j hy.2
      have hsy : p ((e j).symm y) = y := by
        rw [hpe j _ ((e j).map_target hyt), (e j).right_inv hyt]
      refine ⟨((e j).symm y : ℂ), ⟨(e j).symm y, ⟨(e j).map_target hyt, ?_⟩, rfl⟩, ?_⟩
      · show p ((e j).symm y) ∈ A ∩ Q j
        rw [hsy]
        exact hy
      · rw [hpe_coe, hsy]
  have hEm : ∀ j, MeasurableSet (E j) := by
    intro j
    have heq : E j = W j ∩ (fun z => chartAt ℂ x (LiZhongQC.utm_pext p z)) ⁻¹' (chartAt ℂ x '' (A ∩ Q j)) := by
      ext z
      constructor
      · rintro ⟨τ, hτ, rfl⟩
        exact ⟨⟨τ, ⟨hτ.1, hAx hτ.2.1⟩, rfl⟩, ⟨p τ, hτ.2, by beta_reduce; rw [hpe_coe]⟩⟩
      · rintro ⟨⟨τ, hτ, rfl⟩, ⟨y, hy, hyz⟩⟩
        refine ⟨τ, ⟨hτ.1, ?_⟩, rfl⟩
        beta_reduce at hyz
        rw [hpe_coe] at hyz
        have hy' : y = p τ := (chartAt ℂ x).injOn (hAx hy.1) hτ.2 hyz
        show p τ ∈ A ∩ Q j
        rw [← hy']
        exact hy
    rw [heq]
    exact gl31_measurableSet_lift hp x (hWo j) (hWH j) (hWx j) (hAjm j)
  have hEi : ∀ j, InjOn (LiZhongQC.utm_pext p) (E j) := fun j => (hWi j).mono (hEW j)
  -- each piece: chart side → sheet → fundamental domain
  have hpiece : ∀ j, ∫⁻ w in chartAt ℂ x '' (A ∩ Q j), g w =
      ∫⁻ z in F ∩ LiZhongQC.utm_pext p ⁻¹' (A ∩ Q j), h z := by
    intro j
    rw [← himE j, gl31_lintegral_sheet hp x (hWo j) (hWH j) (hWi j) (hWx j) (hEm j) (hEW j) g,
      ← gl31_lintegral_fold hΓ hfree hp hF hh hinv (hEm j) (hEH j) (hEi j)]
    refine setLIntegral_congr_fun (hEm j) fun z hz => hg z (hEH j hz) ?_
    have hz' : LiZhongQC.utm_pext p z ∈ LiZhongQC.utm_pext p '' E j := mem_image_of_mem _ hz
    rw [himE j] at hz'
    exact hz'.1
  have hFm' : ∀ j, MeasurableSet (F ∩ LiZhongQC.utm_pext p ⁻¹' (A ∩ Q j)) := fun j => by
    rw [← himE j]
    exact gl31_measurableSet_over hΓ hp hFm hFH (hEm j) (hEH j)
  have hQc : ⋃ j, Q j = univ := by
    rw [hQ, iUnion_disjointed, eq_univ_iff_forall]
    intro y
    obtain ⟨j, hj⟩ := hcov y
    exact mem_iUnion.2 ⟨j, hj⟩
  have hQd : Pairwise (fun i j => Disjoint (Q i) (Q j)) := disjoint_disjointed _
  have hFA : F ∩ LiZhongQC.utm_pext p ⁻¹' A = ⋃ j, F ∩ LiZhongQC.utm_pext p ⁻¹' (A ∩ Q j) := by
    rw [← inter_iUnion, ← preimage_iUnion, ← inter_iUnion, hQc, inter_univ]
  have hAU : chartAt ℂ x '' A = ⋃ j, chartAt ℂ x '' (A ∩ Q j) := by
    rw [← image_iUnion, ← inter_iUnion, hQc, inter_univ]
  refine ⟨hFA ▸ MeasurableSet.iUnion hFm', ?_⟩
  rw [hAU, hFA, lintegral_iUnion hAjm, lintegral_iUnion hFm']
  · exact tsum_congr hpiece
  · intro i j hij
    exact Disjoint.mono (inter_subset_right.trans (preimage_mono inter_subset_right))
      (inter_subset_right.trans (preimage_mono inter_subset_right)) ((hQd hij).preimage _)
  · intro i j hij
    exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hQd hij)) (chartAt ℂ x).injOn
      (inter_subset_left.trans hAx) (inter_subset_left.trans hAx)

/-- Helper (B-SURF, §3.1). The unfolding identity. For a chart partition `(x, P)` of a uniformized `R`, a
`Γ`-invariant density `h ≥ 0` on `ℍ` and chart functions `g i` lifting to `h` (`|hᵢ′|² · (g i ∘ hᵢ) = h` on
`p̂⁻¹(Pᵢ)`, `hᵢ = φ_{xᵢ} ∘ p̂`), `∑ᵢ ∫_{φ_{xᵢ}(Pᵢ)} g i = ∫_F h` (sheets of `p`, `gl31_lintegral_sheet`,
`gl31_lintegral_fold`). -/
theorem gl31_lintegral_unfold [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {x : ℕ → R} {P : ℕ → Set R} (hP : IsChartPartition R x P) {h : ℂ → ℝ≥0∞}
    (hh : AEMeasurable h (volume.restrict upperHalf))
    (hinv : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      h (LiZhongQC.h36p_m γ z) * ENNReal.ofReal (‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4) = h z)
    (g : ℕ → ℂ → ℝ≥0∞)
    (hg : ∀ i, ∀ z ∈ upperHalf, LiZhongQC.utm_pext p z ∈ P i →
      ENNReal.ofReal (‖deriv (fun v => chartAt ℂ (x i) (LiZhongQC.utm_pext p v)) z‖ ^ 2) *
        g i (chartAt ℂ (x i) (LiZhongQC.utm_pext p z)) = h z) :
    ∑' i, ∫⁻ w in chartAt ℂ (x i) '' P i, g i w = ∫⁻ z in F, h z := by
  obtain ⟨hPs, hPd, hPc⟩ := hP
  have hpiece := fun i => gl31_piece hΓ hfree hp hF hh hinv (x i) (hPs i).1 (hPs i).2 (g i) (hg i)
  have hF' := hF
  obtain ⟨-, -, -, -, -⟩ := hF'
  rw [tsum_congr fun i => (hpiece i).2, ← lintegral_iUnion (fun i => (hpiece i).1)]
  · congr 1
    rw [← inter_iUnion, ← preimage_iUnion, hPc, preimage_univ, inter_univ]
  · intro i j hij
    exact Disjoint.mono inter_subset_right inter_subset_right ((hPd hij).preimage _)

/-- Helper (B-SURF, §3.1, l. 2153–2176). `‖φ‖ = ∬_F |φ̃|` for a holomorphic quadratic differential `φ` on a
uniformized surface, with the lift `φ̃ = LiZhongQC.utm_liftQD φ p` (partition independence
`LiZhongQC.s26v_surfaceIntegral_eq_tsum` and `gl31_lintegral_unfold`). -/
theorem gl31_quadDiffNorm_eq [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {φ : R → ℂ → ℂ} (hφ : LiZhongQC.IsHolQuadDiff φ) :
    quadDiffNorm φ = phiArea (LiZhongQC.utm_liftQD φ p) F := by
  have hF' := hF
  obtain ⟨hFH, hFm, -, -, -⟩ := hF'
  have hsc := gl31_secondCountable hp
  have hne : Nonempty R := ⟨p UpperHalfPlane.I⟩
  obtain ⟨x, P, hP, -⟩ := gl31_exists_chartPartition (R := R) (fun y => (chartAt ℂ y).source)
    (fun y => (chartAt ℂ y).open_source) (fun y => mem_chart_source ℂ y) (fun _ => subset_rfl)
  have h1 : quadDiffNorm φ = ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖φ (x i) z‖ := by
    have h2 := LiZhongQC.s26v_surfaceIntegral_eq_tsum hφ (fun _ => 1) hP
    simp only [one_mul] at h2
    exact h2
  have hcont : ContinuousOn (LiZhongQC.utm_liftQD φ p) upperHalf :=
    (LiZhongQC.utm_liftQD_differentiableOn hφ hp).continuousOn
  have hHm : MeasurableSet upperHalf := LiZhongQC.isOpen_upperHalf.measurableSet
  rw [h1, gl31_lintegral_unfold hΓ hfree hp hF hP
    (h := upperHalf.indicator fun z => ENNReal.ofReal ‖LiZhongQC.utm_liftQD φ p z‖)
    ((hcont.norm.aemeasurable hHm).ennreal_ofReal.indicator hHm) ?_ (fun i z => ENNReal.ofReal ‖φ (x i) z‖) ?_]
  · show _ = ∫⁻ z in F, ENNReal.ofReal ‖LiZhongQC.utm_liftQD φ p z‖
    exact setLIntegral_congr_fun hFm fun z hz => indicator_of_mem (hFH hz) _
  · intro γ hγ z hz
    have hmz := LiZhongQC.h36p_m_mem γ hz
    rw [indicator_of_mem hmz, indicator_of_mem hz, ← ENNReal.ofReal_mul (norm_nonneg _)]
    congr 1
    have h2 := LiZhongQC.utm_b_liftQD_automorphic φ hp hγ hz
    have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := LiZhongQC.h36t_den_ne γ ⟨z, hz⟩
    have hm : LiZhongQC.h36p_m γ z = LiZhongQC.utm_b_mob γ z := rfl
    rw [← h2, hm, norm_mul, norm_pow, norm_div, norm_one, norm_pow]
    have hd : ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ≠ 0 := norm_ne_zero_iff.2 hden
    field_simp
  · intro i z hz hzP
    have hzP' : p ⟨z, hz⟩ ∈ (chartAt ℂ (x i)).source := by
      have h3 := hP.1 i
      rw [LiZhongQC.utm_a_pext_eq p hz, UpperHalfPlane.ofComplex_apply_of_im_pos hz] at hzP
      exact h3.1 hzP
    obtain ⟨U, -, hzU, -, -, hU⟩ := LiZhongQC.utm_liftQD_local hφ hp ⟨z, hz⟩ (x i) hzP'
    obtain ⟨-, -, -, heq⟩ := hU z hzU
    rw [indicator_of_mem hz, heq, ← ENNReal.ofReal_mul (by positivity), norm_mul, norm_pow, mul_comm]

/-- Helper (B-SURF, §3.1). `gl31_lintegral_unfold` for a part `κ ∘ f` of a complex density, `κ : ℂ → ℝ` continuous and
positively homogeneous (real or imaginary part, their negatives, the norm), under the hypotheses of
`gl31_integral_unfold`: `∑ᵢ ∫_{φ_{xᵢ}(Pᵢ)} (κ ∘ g i)⁺ = ∫_F (κ ∘ f)⁺`. -/
theorem gl31_part_unfold [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {x : ℕ → R} {P : ℕ → Set R} (hP : IsChartPartition R x P) {f : ℂ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict upperHalf))
    (hinv : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      ((‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4 : ℝ) : ℂ) * f (LiZhongQC.h36p_m γ z) = f z)
    (g : ℕ → ℂ → ℂ)
    (hg : ∀ i, ∀ z ∈ upperHalf, LiZhongQC.utm_pext p z ∈ P i →
      ((‖deriv (fun v => chartAt ℂ (x i) (LiZhongQC.utm_pext p v)) z‖ ^ 2 : ℝ) : ℂ) *
        g i (chartAt ℂ (x i) (LiZhongQC.utm_pext p z)) = f z)
    (κ : ℂ → ℝ) (hκc : Continuous κ) (hκ : ∀ c : ℝ, 0 ≤ c → ∀ w : ℂ, κ ((c : ℂ) * w) = c * κ w) :
    ∑' i, ∫⁻ w in chartAt ℂ (x i) '' P i, ENNReal.ofReal (κ (g i w)) =
      ∫⁻ z in F, ENNReal.ofReal (κ (f z)) := by
  refine gl31_lintegral_unfold hΓ hfree hp hF hP (h := fun z => ENNReal.ofReal (κ (f z)))
    ((hκc.measurable.comp_aemeasurable hfm.aemeasurable).ennreal_ofReal) ?_
    (fun i w => ENNReal.ofReal (κ (g i w))) ?_
  · intro γ hγ z hz
    rw [← hinv γ hγ z hz, hκ _ (by positivity), ENNReal.ofReal_mul (by positivity), mul_comm]
  · intro i z hz hzP
    rw [← hg i z hz hzP, hκ _ (by positivity), ENNReal.ofReal_mul (by positivity)]

/-- Helper (B-SURF, §3.1). The unfolding identity for integrable complex densities (`gl31_lintegral_unfold` applied
to real and imaginary, positive and negative parts): every chart function is integrable on its piece and
`∑ᵢ ∫_{φ_{xᵢ}(Pᵢ)} g i = ∫_F f`. -/
theorem gl31_integral_unfold [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {x : ℕ → R} {P : ℕ → Set R} (hP : IsChartPartition R x P) {f : ℂ → ℂ}
    (hfm : AEStronglyMeasurable f (volume.restrict upperHalf)) (hfi : IntegrableOn f F)
    (hinv : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      ((‖(γ 1 0 : ℂ) * z + γ 1 1‖⁻¹ ^ 4 : ℝ) : ℂ) * f (LiZhongQC.h36p_m γ z) = f z)
    (g : ℕ → ℂ → ℂ) (hgm : ∀ i, AEStronglyMeasurable (g i) (volume.restrict (chartAt ℂ (x i) '' P i)))
    (hg : ∀ i, ∀ z ∈ upperHalf, LiZhongQC.utm_pext p z ∈ P i →
      ((‖deriv (fun v => chartAt ℂ (x i) (LiZhongQC.utm_pext p v)) z‖ ^ 2 : ℝ) : ℂ) *
        g i (chartAt ℂ (x i) (LiZhongQC.utm_pext p z)) = f z) :
    (∀ i, IntegrableOn (g i) (chartAt ℂ (x i) '' P i)) ∧
      ∑' i, ∫ w in chartAt ℂ (x i) '' P i, g i w = ∫ z in F, f z := by
  have hF' := hF
  obtain ⟨hFH, hFm, -, -, -⟩ := hF'
  have hpart := gl31_part_unfold hΓ hfree hp hF hP hfm hinv g hg
  have hnorm := hpart (fun w => ‖w‖) continuous_norm fun c hc w => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc]
  have hFi : Integrable f (volume.restrict F) := hfi
  have hfin : ∫⁻ z in F, ENNReal.ofReal ‖f z‖ ≠ ⊤ := by
    have h1 := hFi.2
    simp only [HasFiniteIntegral, ← ofReal_norm] at h1
    exact h1.ne
  have hsumfin : ∑' i, ∫⁻ w in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖g i w‖ ≠ ⊤ := by
    rw [hnorm]
    exact hfin
  have hgi : ∀ i, IntegrableOn (g i) (chartAt ℂ (x i) '' P i) := fun i => by
    refine ⟨hgm i, ?_⟩
    show ∫⁻ w in chartAt ℂ (x i) '' P i, ‖g i w‖ₑ < ⊤
    simp only [← ofReal_norm]
    exact lt_of_le_of_lt
      (ENNReal.le_tsum (f := fun i => ∫⁻ w in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖g i w‖) i) hsumfin.lt_top
  refine ⟨hgi, ?_⟩
  -- the real and imaginary parts of an integral, as differences of positive parts
  have hsplit : ∀ (S : Set ℂ) (u : ℂ → ℂ), IntegrableOn u S →
      (∫ a in S, u a).re = (∫⁻ a in S, ENNReal.ofReal (u a).re).toReal -
        (∫⁻ a in S, ENNReal.ofReal (-(u a).re)).toReal ∧
      (∫ a in S, u a).im = (∫⁻ a in S, ENNReal.ofReal (u a).im).toReal -
        (∫⁻ a in S, ENNReal.ofReal (-(u a).im)).toReal := by
    intro S u hu
    constructor
    · have h1 := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hu.re
      rw [integral_re hu] at h1
      exact h1
    · have h1 := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hu.im
      rw [integral_im hu] at h1
      exact h1
  -- the four parts, through `gl31_part_unfold`
  have hle : ∀ (κ : ℂ → ℝ), (∀ w, κ w ≤ ‖w‖) →
      ∑' i, ∫⁻ w in chartAt ℂ (x i) '' P i, ENNReal.ofReal (κ (g i w)) ≤
        ∑' i, ∫⁻ w in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖g i w‖ := fun κ hκ =>
    ENNReal.tsum_le_tsum fun i => lintegral_mono fun w => ENNReal.ofReal_le_ofReal (hκ (g i w))
  have hfinκ : ∀ (κ : ℂ → ℝ), (∀ w, κ w ≤ ‖w‖) →
      ∑' i, ∫⁻ w in chartAt ℂ (x i) '' P i, ENNReal.ofReal (κ (g i w)) ≠ ⊤ := fun κ hκ =>
    ne_top_of_le_ne_top hsumfin (hle κ hκ)
  have hterm : ∀ (κ : ℂ → ℝ), (∀ w, κ w ≤ ‖w‖) → ∀ i,
      ∫⁻ w in chartAt ℂ (x i) '' P i, ENNReal.ofReal (κ (g i w)) ≠ ⊤ := fun κ hκ i =>
    ne_top_of_le_ne_top (hfinκ κ hκ)
      (ENNReal.le_tsum (f := fun i => ∫⁻ w in chartAt ℂ (x i) '' P i, ENNReal.ofReal (κ (g i w))) i)
  have hpos : ∀ (κ : ℂ → ℝ) (hκc : Continuous κ) (hκ : ∀ c : ℝ, 0 ≤ c → ∀ w : ℂ, κ ((c : ℂ) * w) = c * κ w),
      (∀ w, κ w ≤ ‖w‖) →
      ∑' i, (∫⁻ w in chartAt ℂ (x i) '' P i, ENNReal.ofReal (κ (g i w))).toReal =
        (∫⁻ z in F, ENNReal.ofReal (κ (f z))).toReal := fun κ hκc hκ hκn => by
    rw [← ENNReal.tsum_toReal_eq (hterm κ hκn), hpart κ hκc hκ]
  have hre_le : ∀ w : ℂ, w.re ≤ ‖w‖ := fun w => Complex.re_le_norm w
  have hnre_le : ∀ w : ℂ, -w.re ≤ ‖w‖ := fun w => by
    have := Complex.abs_re_le_norm w
    linarith [neg_abs_le w.re, neg_le_abs w.re]
  have him_le : ∀ w : ℂ, w.im ≤ ‖w‖ := fun w => Complex.im_le_norm w
  have hnim_le : ∀ w : ℂ, -w.im ≤ ‖w‖ := fun w => by
    have := Complex.abs_im_le_norm w
    linarith [neg_abs_le w.im, neg_le_abs w.im]
  have hsumm : Summable fun i => ∫ w in chartAt ℂ (x i) '' P i, g i w :=
    Summable.of_norm_bounded (ENNReal.summable_toReal hsumfin) fun i => norm_integral_le_lintegral_norm _
  have hsr : ∀ (κ : ℂ → ℝ), (∀ w, κ w ≤ ‖w‖) →
      Summable fun i => (∫⁻ w in chartAt ℂ (x i) '' P i, ENNReal.ofReal (κ (g i w))).toReal := fun κ hκ =>
    ENNReal.summable_toReal (hfinκ κ hκ)
  apply Complex.ext
  · rw [Complex.re_tsum hsumm, (hsplit F f hFi).1]
    rw [tsum_congr fun i => (hsplit _ _ (hgi i)).1, Summable.tsum_sub (hsr _ hre_le) (hsr _ hnre_le)]
    rw [hpos (fun w => w.re) Complex.continuous_re (fun c _ w => by simp) hre_le,
      hpos (fun w => -w.re) Complex.continuous_re.neg (fun c _ w => by simp) hnre_le]
  · rw [Complex.im_tsum hsumm, (hsplit F f hFi).2]
    rw [tsum_congr fun i => (hsplit _ _ (hgi i)).2, Summable.tsum_sub (hsr _ him_le) (hsr _ hnim_le)]
    rw [hpos (fun w => w.im) Complex.continuous_im (fun c _ w => by simp) him_le,
      hpos (fun w => -w.im) Complex.continuous_im.neg (fun c _ w => by simp) hnim_le]

/-- Helper (B-SURF II, §3.1). A finite surface integral forces a chart partition: `surfaceIntegral` is an infimum over
chart partitions, and the infimum over the empty family is `⊤`. -/
theorem gl31_exists_partition_of_ne_top {q : R → ℂ → ℂ} {u : R → ℂ → ℝ≥0∞}
    (h : LiZhongQC.surfaceIntegral q u ≠ ⊤) : ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P := by
  by_contra hne
  exact h (iInf_eq_top.2 fun x => iInf_eq_top.2 fun P => iInf_eq_top.2 fun hP => (hne ⟨x, P, hP⟩).elim)

/-- Helper (B-SURF II, §3.1). A charted space with a chart partition is second countable: the chart sources of the
partition form a countable cover by second countable open sets (Mathlib
`ChartedSpace.secondCountable_of_countable_cover`). -/
theorem gl31_secondCountable_of_partition {x : ℕ → R} {P : ℕ → Set R} (hP : IsChartPartition R x P) :
    SecondCountableTopology R := by
  refine ChartedSpace.secondCountable_of_countable_cover ℂ (s := range x) ?_ (countable_range x)
  refine eq_univ_of_forall fun y => ?_
  have hy : y ∈ ⋃ i, P i := by
    rw [hP.2.2]
    exact mem_univ y
  obtain ⟨i, hi⟩ := mem_iUnion.1 hy
  exact mem_iUnion₂.2 ⟨x i, mem_range_self i, (hP.1 i).1 hi⟩

/-- Helper (B-SURF II, §3.1, §3.3). On a second countable nonempty surface, for a compact `C ⊆ R`: a chart partition
whose pieces lie in chart balls `B(φₓ(x), r)` with `r ≤ 1` and closed ball inside the chart target, of which only the
first `N` meet `C` (a finite subcover of `C` is enumerated first). -/
theorem gl31_exists_chartPartition_cpt [SecondCountableTopology R] [Nonempty R] {C : Set R} (hC : IsCompact C) :
    ∃ (x : ℕ → R) (P : ℕ → Set R) (r : ℕ → ℝ) (N : ℕ), IsChartPartition R x P ∧
      (∀ i, 0 < r i ∧ r i ≤ 1 ∧ closedBall (chartAt ℂ (x i) (x i)) (r i) ⊆ (chartAt ℂ (x i)).target ∧
        chartAt ℂ (x i) '' P i ⊆ ball (chartAt ℂ (x i) (x i)) (r i)) ∧
      ∀ i, N ≤ i → Disjoint (P i) C := by
  -- a radius `r y ∈ (0, 1]` at every point, with the closed chart ball inside the chart target
  have hr : ∀ y : R, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ closedBall (chartAt ℂ y y) r ⊆ (chartAt ℂ y).target := by
    intro y
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (chartAt ℂ y).open_target (chartAt ℂ y y) (mem_chart_target ℂ y)
    refine ⟨min (ε / 2) 1, lt_min (half_pos hε) one_pos, min_le_right _ _, ?_⟩
    exact (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε))).trans hball
  choose r hr0 hr1 hrt using hr
  -- the neighbourhoods `V y = φ_y⁻¹(B(φ_y(y), r y))` inside the chart sources
  set V : R → Set R := fun y => (chartAt ℂ y).source ∩ chartAt ℂ y ⁻¹' ball (chartAt ℂ y y) (r y)
  have hVo : ∀ y, IsOpen (V y) := fun y =>
    (chartAt ℂ y).continuousOn.isOpen_inter_preimage (chartAt ℂ y).open_source isOpen_ball
  have hVy : ∀ y, y ∈ V y := fun y => ⟨mem_chart_source ℂ y, mem_ball_self (hr0 y)⟩
  have hVs : ∀ y, V y ⊆ (chartAt ℂ y).source := fun y => inter_subset_left
  -- a finite subcover of `C`, and a countable subcover of `R`
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover V hVo (fun c _ => mem_iUnion.2 ⟨c, hVy c⟩)
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable V hVo
  have hcov : ∀ y : R, ∃ s ∈ T, y ∈ V s := fun y => by
    have hy : y ∈ ⋃ i, V i := mem_iUnion.2 ⟨y, hVy y⟩
    rw [← hTU] at hy
    obtain ⟨s, hs, hys⟩ := mem_iUnion₂.1 hy
    exact ⟨s, hs, hys⟩
  obtain ⟨y₀⟩ := ‹Nonempty R›
  have hTne : T.Nonempty := by
    obtain ⟨s, hs, -⟩ := hcov y₀
    exact ⟨s, hs⟩
  obtain ⟨e, he⟩ := hTc.exists_eq_range hTne
  -- the centres: first the finite subcover of `C` (indices `< #t`), then the countable subcover
  obtain ⟨x, hxt, hxe⟩ : ∃ x : ℕ → R, (∀ s ∈ t, ∃ j < t.card, x j = s) ∧ ∀ k, x (t.card + k) = e k := by
    refine ⟨fun i => if h : i < t.card then ((t.equivFin.symm ⟨i, h⟩ : t) : R) else e (i - t.card),
      fun s hs => ⟨t.equivFin ⟨s, hs⟩, (t.equivFin ⟨s, hs⟩).2, ?_⟩, fun k => ?_⟩
    · simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
    · simp only [show ¬ t.card + k < t.card by omega, ↓reduceDIte, Nat.add_sub_cancel_left]
  refine ⟨x, disjointed (fun i => V (x i)), fun i => r (x i), t.card,
    ⟨fun i => ⟨(disjointed_subset _ i).trans (hVs (x i)), ?_⟩, disjoint_disjointed _, ?_⟩,
    fun i => ⟨hr0 (x i), hr1 (x i), hrt (x i), ?_⟩, fun i hi => ?_⟩
  · rw [disjointed_eq_inter_compl]
    exact LiZhongQC.s26_measurableSet_chart_image (x i) (fun j => V (x j)) (fun j => hVo (x j)) i (hVs (x i))
  · rw [iUnion_disjointed, eq_univ_iff_forall]
    intro y
    obtain ⟨s, hs, hys⟩ := hcov y
    rw [he] at hs
    obtain ⟨k, rfl⟩ := hs
    exact mem_iUnion.2 ⟨t.card + k, by rw [hxe k]; exact hys⟩
  · -- the chart image of a piece lies in the chart ball
    rintro _ ⟨y, hy, rfl⟩
    exact ((disjointed_subset _ i) hy).2
  · -- the pieces with index `≥ #t` avoid `C`
    rw [disjointed_eq_inter_compl]
    refine Set.disjoint_left.2 fun y hy hyC => ?_
    obtain ⟨s, hs, hys⟩ := mem_iUnion₂.1 (ht hyC)
    obtain ⟨j, hj, rfl⟩ := hxt s hs
    exact (mem_iInter₂.1 hy.2 j (by omega)) hys

/-- Helper (B-SURF II, §3.1). Unit cells for a chart partition `(x, P)`: measurable pieces
`piece m ⊆ φ_{x(ι m)}(P (ι m))`, each `φ_{xᵢ}(Pᵢ)` being the disjoint union of the pieces with `ι m = i`, moved by
translations `w ↦ w + t m` onto pairwise disjoint subsets of `ℂ` (the cells `[a, a+1) × [b, b+1)` of `ℂ`, shifted to
`[4m, 4m+1) × [0, 1)`). -/
theorem gl31_cells {x : ℕ → R} {P : ℕ → Set R} (hP : IsChartPartition R x P) :
    ∃ (ι : ℕ → ℕ) (piece : ℕ → Set ℂ) (t : ℕ → ℂ),
      (∀ m, MeasurableSet (piece m) ∧ piece m ⊆ chartAt ℂ (x (ι m)) '' P (ι m)) ∧
      (∀ i, chartAt ℂ (x i) '' P i = ⋃ (m : ℕ) (_ : ι m = i), piece m) ∧
      (Pairwise fun m m' => ι m = ι m' → Disjoint (piece m) (piece m')) ∧
      Pairwise fun m m' => Disjoint ((fun w => w + t m) '' piece m) ((fun w => w + t m') '' piece m') := by
  -- the unit cells `Q (a, b) = [a, a + 1) × [b, b + 1)` of `ℂ`, enumerated with the partition index by
  -- `e : ℕ ≃ ℕ × ℤ × ℤ`; the cell piece `m` is moved to `[4m, 4m + 1) × [0, 1)`
  set e : ℕ ≃ ℕ × ℤ × ℤ := (Denumerable.eqv (ℕ × ℤ × ℤ)).symm
  set Q : ℤ × ℤ → Set ℂ := fun ab => re ⁻¹' Ico (ab.1 : ℝ) (ab.1 + 1) ∩ im ⁻¹' Ico (ab.2 : ℝ) (ab.2 + 1)
  have hQm : ∀ ab, MeasurableSet (Q ab) := fun ab =>
    (measurableSet_Ico.preimage measurable_re).inter (measurableSet_Ico.preimage measurable_im)
  have hQ : ∀ w : ℂ, w ∈ Q (⌊w.re⌋, ⌊w.im⌋) := fun w =>
    ⟨⟨Int.floor_le _, Int.lt_floor_add_one _⟩, ⟨Int.floor_le _, Int.lt_floor_add_one _⟩⟩
  have hQd : ∀ ab ab', ab ≠ ab' → Disjoint (Q ab) (Q ab') := by
    intro ab ab' hne
    refine Set.disjoint_left.2 fun w hw hw' => hne (Prod.ext ?_ ?_)
    · rw [← Int.floor_eq_iff.2 hw.1, ← Int.floor_eq_iff.2 hw'.1]
    · rw [← Int.floor_eq_iff.2 hw.2, ← Int.floor_eq_iff.2 hw'.2]
  refine ⟨fun m => (e m).1, fun m => chartAt ℂ (x (e m).1) '' P (e m).1 ∩ Q (e m).2,
    fun m => (⟨4 * (m : ℝ) - ((e m).2.1 : ℝ), -((e m).2.2 : ℝ)⟩ : ℂ),
    fun m => ⟨(hP.1 _).2.inter (hQm _), inter_subset_left⟩, fun i => ?_, fun m m' hmm' hι => ?_, fun m m' hmm' => ?_⟩
  · ext w
    simp only [mem_iUnion, exists_prop]
    constructor
    · intro hw
      refine ⟨e.symm (i, (⌊w.re⌋, ⌊w.im⌋)), by simp, ?_⟩
      simp only [Equiv.apply_symm_apply]
      exact ⟨hw, hQ w⟩
    · rintro ⟨m, rfl, hw, -⟩
      exact hw
  · exact Disjoint.mono inter_subset_right inter_subset_right
      (hQd _ _ fun h => hmm' (e.injective (Prod.ext hι h)))
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨w, hw, rfl⟩ ⟨w', hw', hww'⟩
    have hre := congrArg Complex.re hww'
    simp only [add_re] at hre
    obtain ⟨⟨h1a, h1b⟩, -⟩ := hw.2
    obtain ⟨⟨h2a, h2b⟩, -⟩ := hw'.2
    have h3 : 4 * m < 4 * m' + 1 := by
      have : (4 * m : ℝ) < 4 * m' + 1 := by linarith
      exact_mod_cast this
    have h4 : 4 * m' < 4 * m + 1 := by
      have : (4 * m' : ℝ) < 4 * m + 1 := by linarith
      exact_mod_cast this
    exact hmm' (by omega)

/-- Helper (B-SURF II, §3.1). With cells as in `gl31_cells`, the function `F = Σₘ 𝟙_{piece m + t m} · f_{ι m}(· − t m)`
assembled from chart functions `f i` has `∫⁻_{⋃ₘ (piece m + t m)} ‖F‖ = Σᵢ ∫⁻_{φ_{xᵢ}(Pᵢ)} ‖f i‖`; when the `f i` are
a.e.-strongly measurable so is `F`, and when moreover the sum is finite
`∫_{⋃ₘ (piece m + t m)} F = Σᵢ ∫_{φ_{xᵢ}(Pᵢ)} f i` (translation invariance of area, disjointness). -/
theorem gl31_cells_integral {x : ℕ → R} {P : ℕ → Set R} {ι : ℕ → ℕ} {piece : ℕ → Set ℂ} {t : ℕ → ℂ}
    (hpm : ∀ m, MeasurableSet (piece m) ∧ piece m ⊆ chartAt ℂ (x (ι m)) '' P (ι m))
    (hpU : ∀ i, chartAt ℂ (x i) '' P i = ⋃ (m : ℕ) (_ : ι m = i), piece m)
    (hpd : Pairwise fun m m' => ι m = ι m' → Disjoint (piece m) (piece m'))
    (htd : Pairwise fun m m' => Disjoint ((fun w => w + t m) '' piece m) ((fun w => w + t m') '' piece m'))
    (f : ℕ → ℂ → ℂ) :
    ∫⁻ w in ⋃ m, (fun w => w + t m) '' piece m,
        ‖∑' m, ((fun w => w + t m) '' piece m).indicator (fun w => f (ι m) (w - t m)) w‖ₑ =
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖f i z‖ₑ ∧
    ((∀ i, AEStronglyMeasurable (f i) (volume.restrict (chartAt ℂ (x i) '' P i))) →
      AEStronglyMeasurable (fun w => ∑' m, ((fun w => w + t m) '' piece m).indicator (fun w => f (ι m) (w - t m)) w)
        (volume.restrict (⋃ m, (fun w => w + t m) '' piece m)) ∧
      (∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖f i z‖ₑ < ⊤ →
        ∫ w in ⋃ m, (fun w => w + t m) '' piece m,
            ∑' m, ((fun w => w + t m) '' piece m).indicator (fun w => f (ι m) (w - t m)) w =
          ∑' i, ∫ z in chartAt ℂ (x i) '' P i, f i z)) := by
  -- the translated pieces are measurable and pairwise disjoint, and `F = f (ι m) (· − t m)` on the `m`-th one
  have hQm : ∀ m, MeasurableSet ((fun w => w + t m) '' piece m) := fun m => by
    rw [image_add_right]
    exact measurable_add_const (-t m) (hpm m).1
  have htd' : Pairwise (Function.onFun Disjoint fun m => (fun w => w + t m) '' piece m) := fun m m' h => htd h
  have hval : ∀ m, ∀ w ∈ (fun w => w + t m) '' piece m,
      ∑' m', ((fun w => w + t m') '' piece m').indicator (fun w => f (ι m') (w - t m')) w = f (ι m) (w - t m) := by
    intro m w hw
    rw [tsum_eq_single m fun m' hm' => indicator_of_notMem (fun hw' => Set.disjoint_left.1 (htd hm') hw' hw) _,
      indicator_of_mem hw]
  -- translation invariance of area
  have hemb : ∀ m, MeasurableEmbedding fun z : ℂ => z + t m := fun m => measurableEmbedding_addRight (t m)
  have hmp : ∀ m, MeasurePreserving (fun z : ℂ => z + t m) volume volume := fun m =>
    measurePreserving_add_right volume (t m)
  have htrL : ∀ m (g : ℂ → ℝ≥0∞), ∫⁻ w in (fun w => w + t m) '' piece m, g (w - t m) = ∫⁻ z in piece m, g z := by
    intro m g
    rw [← (hmp m).setLIntegral_comp_emb (hemb m) (fun w => g (w - t m)) (piece m)]
    simp only [add_sub_cancel_right]
  -- regrouping the pieces by the index `ι`
  have hfib : ∀ i, chartAt ℂ (x i) '' P i = ⋃ m : ι ⁻¹' {i}, piece m := fun i => by
    rw [hpU i]
    ext w
    simp only [mem_iUnion, exists_prop, Subtype.exists, mem_preimage, mem_singleton_iff]
  have hfibd : ∀ i, Pairwise (Function.onFun Disjoint fun m : ι ⁻¹' {i} => piece m) := fun i m m' h =>
    hpd (fun h' => h (Subtype.ext h')) ((show ι m = i from m.2).trans (show ι m' = i from m'.2).symm)
  have hL : ∀ g : ℕ → ℂ → ℝ≥0∞,
      ∑' m, ∫⁻ z in piece m, g (ι m) z = ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, g i z := by
    intro g
    refine (ENNReal.tsum_fiberwise (fun m => ∫⁻ z in piece m, g (ι m) z) ι).symm.trans (tsum_congr fun i => ?_)
    rw [hfib i, lintegral_iUnion (s := fun m : ι ⁻¹' {i} => piece m) (fun m => (hpm m).1) (hfibd i)]
    refine tsum_congr fun m => ?_
    rw [show ι m = i from m.2]
  have hLf : ∑' m, ∫⁻ z in piece m, ‖f (ι m) z‖ₑ = ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖f i z‖ₑ :=
    hL fun i z => ‖f i z‖ₑ
  have h1 : ∫⁻ w in ⋃ m, (fun w => w + t m) '' piece m,
      ‖∑' m, ((fun w => w + t m) '' piece m).indicator (fun w => f (ι m) (w - t m)) w‖ₑ =
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖f i z‖ₑ := by
    rw [lintegral_iUnion hQm htd', ← hLf]
    refine tsum_congr fun m => ?_
    rw [← htrL m fun z => ‖f (ι m) z‖ₑ]
    exact setLIntegral_congr_fun (hQm m) fun w hw => by simp only [hval m w hw]
  refine ⟨h1, fun hf => ⟨?_, fun hfin => ?_⟩⟩
  · -- a.e.-strong measurability, piece by piece
    refine aestronglyMeasurable_iUnion_iff.2 fun m => ?_
    have hmpr := (hmp m).restrict_image_emb (hemb m) (piece m)
    refine AEStronglyMeasurable.congr ?_ ((ae_restrict_iff' (hQm m)).2
      (Eventually.of_forall fun w hw => (hval m w hw).symm))
    rw [← hmpr.map_eq, (hemb m).aestronglyMeasurable_map_iff]
    simpa [Function.comp_def] using (hf (ι m)).mono_measure (Measure.restrict_mono (hpm m).2 le_rfl)
  · -- the Bochner integral: over the translated pieces, back by translation, regrouped by `ι`
    have hint : IntegrableOn (fun w => ∑' m, ((fun w => w + t m) '' piece m).indicator
        (fun w => f (ι m) (w - t m)) w) (⋃ m, (fun w => w + t m) '' piece m) := by
      refine ⟨?_, ?_⟩
      · refine aestronglyMeasurable_iUnion_iff.2 fun m => ?_
        have hmpr := (hmp m).restrict_image_emb (hemb m) (piece m)
        refine AEStronglyMeasurable.congr ?_ ((ae_restrict_iff' (hQm m)).2
          (Eventually.of_forall fun w hw => (hval m w hw).symm))
        rw [← hmpr.map_eq, (hemb m).aestronglyMeasurable_map_iff]
        simpa [Function.comp_def] using (hf (ι m)).mono_measure (Measure.restrict_mono (hpm m).2 le_rfl)
      · show ∫⁻ w in ⋃ m, (fun w => w + t m) '' piece m,
          ‖∑' m, ((fun w => w + t m) '' piece m).indicator (fun w => f (ι m) (w - t m)) w‖ₑ < ⊤
        rw [h1]
        exact hfin
    have hfinm : ∑' m, ∫⁻ z in piece m, ‖f (ι m) z‖ₑ ≠ ⊤ := by
      rw [hLf]
      exact hfin.ne
    have hsumm : Summable fun m => ∫ z in piece m, f (ι m) z :=
      Summable.of_norm_bounded (ENNReal.summable_toReal hfinm) fun m =>
        (norm_integral_le_lintegral_norm _).trans_eq (by simp only [ofReal_norm])
    have hintP : ∀ i, IntegrableOn (f i) (chartAt ℂ (x i) '' P i) := fun i =>
      ⟨hf i, lt_of_le_of_lt (ENNReal.le_tsum (f := fun i => ∫⁻ z in chartAt ℂ (x i) '' P i, ‖f i z‖ₑ) i) hfin⟩
    have hterm : ∀ m, ∫ w in (fun w => w + t m) '' piece m,
        ∑' m', ((fun w => w + t m') '' piece m').indicator (fun w => f (ι m') (w - t m')) w =
        ∫ z in piece m, f (ι m) z := by
      intro m
      have e := (hmp m).setIntegral_image_emb (hemb m) (fun w => f (ι m) (w - t m)) (piece m)
      simp only [add_sub_cancel_right] at e
      rw [← e]
      exact setIntegral_congr_fun (hQm m) fun w hw => hval m w hw
    rw [integral_iUnion hQm htd' hint, tsum_congr hterm, ← ((hsumm.hasSum).tsum_fiberwise ι).tsum_eq]
    refine tsum_congr fun i => ?_
    have hi := hintP i
    rw [hfib i] at hi ⊢
    rw [integral_iUnion (s := fun m : ι ⁻¹' {i} => piece m) (fun m => (hpm m).1) (hfibd i) hi]
    refine tsum_congr fun m => ?_
    rw [show ι m = i from m.2]

/-- Helper (B-SURF II, §3.1). The `L¹` model of `A(R)` on a chart partition `(x, P)`: a measurable `S ⊆ ℂ` and a linear
`E` (the cell picture of `gl31_cells`: `E φ = φ_{x(ι m)}(· − t m)` on `piece m + t m`) with `∫_S |E φ| = ‖φ‖` for
holomorphic `φ` (`gl31_cells_integral`, partition independence `LiZhongQC.s26v_surfaceIntegral_eq_tsum`); a bounded
`ν` on `S` pulls back to chart functions `gᵢ = ν(· + t m)` with the same bound, and `∬_S ν E φ = Σᵢ ∬_{φ_{xᵢ}(Pᵢ)} φ gᵢ`
for `φ ∈ A(R)`. -/
theorem gl31_model [IsManifold 𝓘(ℂ) ω R] {x : ℕ → R} {P : ℕ → Set R} (hP : IsChartPartition R x P) :
    ∃ (S : Set ℂ) (E : (R → ℂ → ℂ) → ℂ → ℂ), MeasurableSet S ∧
      (∀ φ ψ, E (φ + ψ) = E φ + E ψ) ∧ (∀ (c : ℂ) φ, E (c • φ) = c • E φ) ∧
      (∀ φ ∈ holQuadDiffSubmodule R,
        AEStronglyMeasurable (E φ) (volume.restrict S) ∧ ∫⁻ w in S, ‖E φ w‖ₑ = quadDiffNorm φ) ∧
      ∀ ν : ℂ → ℂ, AEStronglyMeasurable ν (volume.restrict S) → ∀ c : ℝ, (∀ᵐ w ∂(volume.restrict S), ‖ν w‖ ≤ c) →
        ∃ g : ℕ → ℂ → ℂ, (∀ i, AEStronglyMeasurable (g i) (volume.restrict (chartAt ℂ (x i) '' P i))) ∧
          (∀ i, ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)), ‖g i z‖ ≤ c) ∧
          ∀ φ ∈ integrableHolQDSet R,
            ∫ w in S, ν w * E φ w = ∑' i, ∫ z in chartAt ℂ (x i) '' P i, φ (x i) z * g i z := by
  obtain ⟨ι, piece, t, hpm, hpU, hpd, htd⟩ := gl31_cells hP
  have hQm : ∀ m, MeasurableSet ((fun w => w + t m) '' piece m) := fun m => by
    rw [image_add_right]
    exact measurable_add_const (-t m) (hpm m).1
  have hSm : MeasurableSet (⋃ m, (fun w => w + t m) '' piece m) := MeasurableSet.iUnion hQm
  have hemb : ∀ m, MeasurableEmbedding fun z : ℂ => z + t m := fun m => measurableEmbedding_addRight (t m)
  have hmpr : ∀ m, MeasurePreserving (fun z : ℂ => z + t m) (volume.restrict (piece m))
      (volume.restrict ((fun w => w + t m) '' piece m)) := fun m =>
    (measurePreserving_add_right volume (t m)).restrict_image_emb (hemb m) (piece m)
  have hfib : ∀ i, chartAt ℂ (x i) '' P i = ⋃ m : ι ⁻¹' {i}, piece m := fun i => by
    rw [hpU i]
    ext w
    simp only [mem_iUnion, exists_prop, Subtype.exists, mem_preimage, mem_singleton_iff]
  -- the sum of the translated indicators picks the unique piece containing the point
  have hval : ∀ (F : ℕ → ℂ → ℂ) m, ∀ w ∈ (fun w => w + t m) '' piece m,
      ∑' m', ((fun w => w + t m') '' piece m').indicator (F m') w = F m w := by
    intro F m w hw
    rw [tsum_eq_single m fun m' hm' => indicator_of_notMem (fun hw' => Set.disjoint_left.1 (htd hm') hw' hw) _,
      indicator_of_mem hw]
  have hval0 : ∀ (F : ℕ → ℂ → ℂ) w, w ∉ ⋃ m, (fun w => w + t m) '' piece m →
      ∑' m', ((fun w => w + t m') '' piece m').indicator (F m') w = 0 := fun F w hw =>
    (tsum_congr fun m => indicator_of_notMem (fun h => hw (mem_iUnion.2 ⟨m, h⟩)) _).trans tsum_zero
  obtain ⟨E, hEdef⟩ : ∃ E : (R → ℂ → ℂ) → ℂ → ℂ, E = fun φ w =>
      ∑' m, ((fun w => w + t m) '' piece m).indicator (fun w => φ (x (ι m)) (w - t m)) w := ⟨_, rfl⟩
  have hE : ∀ φ m, ∀ w ∈ (fun w => w + t m) '' piece m, E φ w = φ (x (ι m)) (w - t m) := by
    intro φ m w hw
    rw [hEdef]
    exact hval (fun m w => φ (x (ι m)) (w - t m)) m w hw
  have hE0 : ∀ φ w, w ∉ ⋃ m, (fun w => w + t m) '' piece m → E φ w = 0 := by
    intro φ w hw
    rw [hEdef]
    exact hval0 (fun m w => φ (x (ι m)) (w - t m)) w hw
  -- the chart functions of a holomorphic `φ` are continuous on the chart targets
  have hcont : ∀ φ ∈ holQuadDiffSubmodule R, ∀ i,
      AEStronglyMeasurable (φ (x i)) (volume.restrict (chartAt ℂ (x i) '' P i)) := fun φ hφ i =>
    ((hφ.2 (x i)).continuousOn.mono (image_subset_iff.2 fun y hy =>
      (chartAt ℂ (x i)).map_source ((hP.1 i).1 hy))).aestronglyMeasurable (hP.1 i).2
  have hnorm : ∀ φ ∈ holQuadDiffSubmodule R,
      quadDiffNorm φ = ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z‖ₑ := by
    intro φ hφ
    have e := LiZhongQC.s26v_surfaceIntegral_eq_tsum hφ (fun _ => (1 : ℝ≥0∞)) hP
    simp only [one_mul, ofReal_norm] at e
    exact e
  refine ⟨⋃ m, (fun w => w + t m) '' piece m, E, hSm, fun φ ψ => ?_, fun c φ => ?_, fun φ hφ => ?_, ?_⟩
  · funext w
    by_cases hw : w ∈ ⋃ m, (fun w => w + t m) '' piece m
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hw
      simp only [Pi.add_apply, hE (φ + ψ) m w hm, hE φ m w hm, hE ψ m w hm]
    · simp only [Pi.add_apply, hE0 (φ + ψ) w hw, hE0 φ w hw, hE0 ψ w hw, add_zero]
  · funext w
    by_cases hw : w ∈ ⋃ m, (fun w => w + t m) '' piece m
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hw
      simp only [Pi.smul_apply, hE (c • φ) m w hm, hE φ m w hm]
    · simp only [Pi.smul_apply, hE0 (c • φ) w hw, hE0 φ w hw, smul_zero]
  · have hci := gl31_cells_integral hpm hpU hpd htd (fun i => φ (x i))
    have hEe : E φ = fun w =>
        ∑' m, ((fun w => w + t m) '' piece m).indicator (fun w => φ (x (ι m)) (w - t m)) w := by
      rw [hEdef]
    refine ⟨?_, ?_⟩
    · rw [hEe]
      exact (hci.2 (hcont φ hφ)).1
    · rw [hEe, hci.1, hnorm φ hφ]
  · intro ν hν c hc
    obtain ⟨g, hgdef⟩ : ∃ g : ℕ → ℂ → ℂ, g = fun i z =>
        ∑' m, if ι m = i then (piece m).indicator (fun z => ν (z + t m)) z else 0 := ⟨_, rfl⟩
    -- `gᵢ = ν(· + t m)` on the pieces `m` of `φ_{xᵢ}(Pᵢ)`
    have hg : ∀ i m, ι m = i → ∀ z ∈ piece m, g i z = ν (z + t m) := by
      intro i m hmi z hz
      rw [hgdef]
      refine (tsum_eq_single m fun m' hm' => ?_).trans (by rw [ite_eq_left hmi, indicator_of_mem hz])
      by_cases h' : ι m' = i
      · rw [ite_eq_left h']
        exact indicator_of_notMem (fun hz' => Set.disjoint_left.1 (hpd hm' (h'.trans hmi.symm)) hz' hz) _
      · rw [ite_eq_right h']
    have hνm : ∀ m, AEStronglyMeasurable (fun z => ν (z + t m)) (volume.restrict (piece m)) := fun m =>
      (hν.mono_measure (Measure.restrict_mono (subset_iUnion (fun m => (fun w => w + t m) '' piece m) m)
        le_rfl)).comp_quasiMeasurePreserving (hmpr m).quasiMeasurePreserving
    have hνb : ∀ m, ∀ᵐ z ∂(volume.restrict (piece m)), ‖ν (z + t m)‖ ≤ c := fun m =>
      (hmpr m).quasiMeasurePreserving.ae
        (ae_restrict_of_ae_restrict_of_subset (subset_iUnion (fun m => (fun w => w + t m) '' piece m) m) hc)
    have hgm : ∀ i, AEStronglyMeasurable (g i) (volume.restrict (chartAt ℂ (x i) '' P i)) := by
      intro i
      rw [hfib i]
      refine aestronglyMeasurable_iUnion_iff.2 fun m => (hνm m).congr ?_
      exact (ae_restrict_iff' (hpm m).1).2 (Eventually.of_forall fun z hz => (hg i m m.2 z hz).symm)
    have hgb : ∀ i, ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)), ‖g i z‖ ≤ c := by
      intro i
      rw [hfib i]
      refine (ae_restrict_iUnion_iff _ _).2 fun m => ?_
      filter_upwards [hνb m, ae_restrict_mem (hpm m).1] with z hz hzm
      rw [hg i m m.2 z hzm]
      exact hz
    refine ⟨g, hgm, hgb, fun φ hφ => ?_⟩
    -- `ν · Eφ` is the cell picture of the chart functions `φ_{xᵢ} gᵢ`
    have hci := gl31_cells_integral hpm hpU hpd htd (fun i z => φ (x i) z * g i z)
    have hfm : ∀ i, AEStronglyMeasurable (fun z => φ (x i) z * g i z) (volume.restrict (chartAt ℂ (x i) '' P i)) :=
      fun i => (hcont φ hφ.1 i).mul (hgm i)
    have hfin : ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z * g i z‖ₑ < ⊤ := by
      calc _ ≤ ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal c * ‖φ (x i) z‖ₑ :=
            ENNReal.tsum_le_tsum fun i => lintegral_mono_ae (by
              filter_upwards [hgb i] with z hz
              rw [enorm_mul, mul_comm ‖φ (x i) z‖ₑ, ← ofReal_norm (g i z)]
              exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hz) _)
        _ = ENNReal.ofReal c * quadDiffNorm φ := by
            rw [hnorm φ hφ.1, ← ENNReal.tsum_mul_left]
            exact tsum_congr fun i => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφ.2
    refine (setIntegral_congr_fun hSm fun w hw => ?_).trans ((hci.2 hfm).2 hfin)
    obtain ⟨m, hm⟩ := mem_iUnion.1 hw
    rw [hE φ m w hm, hval _ m w hm]
    obtain ⟨z, hz, rfl⟩ := hm
    simp only [add_sub_cancel_right, hg (ι m) m rfl z hz]
    ring

/-- Helper (B-SURF II, §3.1, used by §3.2 Corollary 1). `A(R)` is separable when `R` is second countable: `gl31_model`
on a chart partition embeds `A(R)` isometrically into `L¹` of a subset of `ℂ`, a second countable space
(`Lp.SecondCountableTopology`). -/
theorem gl31_separable [IsManifold 𝓘(ℂ) ω R] [SecondCountableTopology R] [Nonempty R] :
    ∃ D ⊆ integrableHolQDSet R, D.Countable ∧
      ∀ φ ∈ integrableHolQDSet R, ∀ ε > (0 : ℝ≥0∞), ∃ ψ ∈ D, quadDiffNorm (φ - ψ) < ε := by
  obtain ⟨x, P, hP, -⟩ := gl31_exists_chartPartition (R := R) (fun y => (chartAt ℂ y).source)
    (fun y => (chartAt ℂ y).open_source) (fun y => mem_chart_source ℂ y) (fun _ => subset_rfl)
  obtain ⟨S, E, -, hadd, hsmul, hnorm, -⟩ := gl31_model hP
  -- `φ ↦ E φ` embeds `A(R)` isometrically into `L¹(vol|S)`
  have hmem : ∀ φ ∈ integrableHolQDSet R, MemLp (E φ) 1 (volume.restrict S) := fun φ hφ =>
    memLp_one_iff_integrable.2 ⟨(hnorm φ hφ.1).1, by
      show ∫⁻ w, ‖E φ w‖ₑ ∂(volume.restrict S) < ⊤
      rw [(hnorm φ hφ.1).2]
      exact hφ.2⟩
  have hsub : ∀ φ ψ, E (φ - ψ) = E φ - E ψ := fun φ ψ => by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ, hadd, hsmul, neg_one_smul, ← sub_eq_add_neg]
  have hd : ∀ φ (hφ : φ ∈ integrableHolQDSet R) ψ (hψ : ψ ∈ integrableHolQDSet R),
      quadDiffNorm (φ - ψ) = ENNReal.ofReal (dist ((hmem φ hφ).toLp (E φ)) ((hmem ψ hψ).toLp (E ψ))) := by
    intro φ hφ ψ hψ
    have hφψ : φ - ψ ∈ holQuadDiffSubmodule R := (holQuadDiffSubmodule R).sub_mem hφ.1 hψ.1
    rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp,
      ENNReal.ofReal_toReal ((hmem φ hφ).sub (hmem ψ hψ)).eLpNorm_ne_top,
      eLpNorm_one_eq_lintegral_enorm ((hnorm φ hφ.1).1.sub (hnorm ψ hψ.1).1),
      ← hsub, (hnorm _ hφψ).2]
  -- a countable dense subset of the image, inside the second countable space `L¹(vol|S)`
  have : Fact ((1 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.one_ne_top⟩
  obtain ⟨D', hD'c, hD'd⟩ := TopologicalSpace.exists_countable_dense
    {f : Lp ℂ 1 (volume.restrict S) | ∃ φ, ∃ hφ : φ ∈ integrableHolQDSet R, (hmem φ hφ).toLp (E φ) = f}
  choose sec hsec hsecF using fun f : {f : Lp ℂ 1 (volume.restrict S) |
    ∃ φ, ∃ hφ : φ ∈ integrableHolQDSet R, (hmem φ hφ).toLp (E φ) = f} => f.2
  refine ⟨sec '' D', ?_, hD'c.image _, fun φ hφ ε hε => ?_⟩
  · rintro _ ⟨f, -, rfl⟩
    exact hsec f
  obtain ⟨δ, hδ0, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
    rcases eq_or_ne ε ⊤ with rfl | hεt
    · exact ⟨1, one_pos, le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hεt, (ENNReal.ofReal_toReal hεt).le⟩
  obtain ⟨f, hfD, hf⟩ := hD'd.exists_dist_lt ⟨(hmem φ hφ).toLp (E φ), φ, hφ, rfl⟩ hδ0
  rw [Subtype.dist_eq] at hf
  refine ⟨sec f, ⟨f, hfD, rfl⟩, ?_⟩
  rw [hd φ hφ (sec f) (hsec f), hsecF f]
  exact ((ENNReal.ofReal_lt_ofReal_iff hδ0).2 hf).trans_le hδε

/-- Helper (B-SURF II, §3.1). A Beltrami differential with prescribed coefficients on a chart partition `(x, P)`:
given a.e.-strongly measurable `g i` on `φ_{xᵢ}(Pᵢ)` bounded a.e. by `c ≥ 0`, the family
`μ_y(w) = g_i(T w) conj(T′ w)/T′ w` (where `φ_y⁻¹(w) ∈ Pᵢ` and `T = φ_{xᵢ} ∘ φ_y⁻¹`) is a Beltrami differential with
`μ_{xᵢ} = g i` on `φ_{xᵢ}(Pᵢ)` and `‖μ‖∞ ≤ c`. -/
theorem gl31_beltrami_extend [IsManifold 𝓘(ℂ) ω R] {x : ℕ → R} {P : ℕ → Set R} (hP : IsChartPartition R x P)
    (g : ℕ → ℂ → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hgm : ∀ i, AEStronglyMeasurable (g i) (volume.restrict (chartAt ℂ (x i) '' P i)))
    (hgc : ∀ i, ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)), ‖g i z‖ ≤ c) :
    ∃ μ ∈ beltramiSpace R, (∀ i, ∀ z ∈ chartAt ℂ (x i) '' P i, μ (x i) z = g i z) ∧
      beltramiNormRS μ ≤ ENNReal.ofReal c := by
  classical
  -- `0 ≤ c` is not needed: if `c < 0` the chart images are null and every bound below holds vacuously a.e.
  have _hc := hc
  -- the piece of the partition containing a point
  have hcov : ∀ y : R, ∃ i, y ∈ P i := fun y => mem_iUnion.1 (by rw [hP.2.2]; exact mem_univ y)
  choose idx hidx using hcov
  have hidx' : ∀ y i, y ∈ P i → idx y = i := fun y i hy => by
    by_contra hne
    exact Set.disjoint_left.1 (hP.2.1 hne) (hidx y) hy
  -- `μ_y(w) = g_i(T w) conj(T′ w)/T′ w`, `T = φ_{xᵢ} ∘ φ_y⁻¹`, `i` the piece of `φ_y⁻¹(w)`
  obtain ⟨μ, hμdef⟩ : ∃ μ : R → ℂ → ℂ, μ = fun y w =>
      g (idx ((chartAt ℂ y).symm w)) (LiZhongQC.chartTransition (x (idx ((chartAt ℂ y).symm w))) y w) *
        (conj (deriv (LiZhongQC.chartTransition (x (idx ((chartAt ℂ y).symm w))) y) w) /
          deriv (LiZhongQC.chartTransition (x (idx ((chartAt ℂ y).symm w))) y) w) := ⟨_, rfl⟩
  have hμ : ∀ y w i, (chartAt ℂ y).symm w ∈ P i → μ y w = g i (LiZhongQC.chartTransition (x i) y w) *
      (conj (deriv (LiZhongQC.chartTransition (x i) y) w) / deriv (LiZhongQC.chartTransition (x i) y) w) := by
    intro y w i hw
    simp only [hμdef]
    rw [hidx' _ i hw]
  -- on its own chart target the transition `φ_{xᵢ} ∘ φ_{xᵢ}⁻¹` is the identity
  have hself : ∀ i, ∀ z ∈ (chartAt ℂ (x i)).target, LiZhongQC.chartTransition (x i) (x i) z = z ∧
      deriv (LiZhongQC.chartTransition (x i) (x i)) z = 1 := by
    intro i z hz
    have hev : LiZhongQC.chartTransition (x i) (x i) =ᶠ[𝓝 z] id := by
      filter_upwards [(chartAt ℂ (x i)).open_target.mem_nhds hz] with w hw
      exact (chartAt ℂ (x i)).right_inv hw
    exact ⟨hev.eq_of_nhds, by rw [hev.deriv_eq, deriv_id]⟩
  have hval : ∀ i, ∀ z ∈ chartAt ℂ (x i) '' P i, μ (x i) z = g i z := by
    rintro i _ ⟨q, hq, rfl⟩
    have hqs := (hP.1 i).1 hq
    have hzt := (chartAt ℂ (x i)).map_source hqs
    rw [hμ (x i) _ i (by rw [(chartAt ℂ (x i)).left_inv hqs]; exact hq), (hself i _ hzt).1, (hself i _ hzt).2]
    simp
  -- the transformation law holds everywhere on the overlaps (chain rule; `conj t / t` is multiplicative)
  have hlaw : ∀ x' y : R, ∀ z ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x').source,
      μ y z = μ x' (LiZhongQC.chartTransition x' y z) * deriv (LiZhongQC.chartTransition x' y) z ^ (-1 : ℤ) *
        conj (deriv (LiZhongQC.chartTransition x' y) z) ^ (1 : ℤ) := by
    rintro x' y z ⟨hz, hzx⟩
    have hmem := LiZhongQC.s23_transition_mem hz hzx
    have hpi : (chartAt ℂ y).symm z ∈ P (idx ((chartAt ℂ y).symm z)) := hidx _
    have hpis := (hP.1 _).1 hpi
    have hev : LiZhongQC.chartTransition (x (idx ((chartAt ℂ y).symm z))) y =ᶠ[𝓝 z]
        LiZhongQC.chartTransition (x (idx ((chartAt ℂ y).symm z))) x' ∘ LiZhongQC.chartTransition x' y := by
      filter_upwards [((chartAt ℂ y).continuousAt_symm hz).preimage_mem_nhds
        ((chartAt ℂ x').open_source.mem_nhds hzx)] with w hwx
      show chartAt ℂ (x (idx ((chartAt ℂ y).symm z))) ((chartAt ℂ y).symm w) =
        chartAt ℂ (x (idx ((chartAt ℂ y).symm z))) ((chartAt ℂ x').symm (chartAt ℂ x' ((chartAt ℂ y).symm w)))
      rw [(chartAt ℂ x').left_inv hwx]
    have hd1 := LiZhongQC.s23_transition_differentiableAt (x (idx ((chartAt ℂ y).symm z))) x' hmem.1
      (by rw [hmem.2.2]; exact hpis)
    have hd2 := LiZhongQC.s23_transition_differentiableAt x' y hz hzx
    have hderiv : deriv (LiZhongQC.chartTransition (x (idx ((chartAt ℂ y).symm z))) y) z =
        deriv (LiZhongQC.chartTransition (x (idx ((chartAt ℂ y).symm z))) x') (LiZhongQC.chartTransition x' y z) *
          deriv (LiZhongQC.chartTransition x' y) z := by
      rw [hev.deriv_eq, deriv_comp z hd1 hd2]
    rw [hμ y z _ hpi, hμ x' _ (idx ((chartAt ℂ y).symm z)) (by rw [hmem.2.2]; exact hpi), hev.eq_of_nhds,
      hderiv, map_mul, zpow_neg_one, zpow_one]
    simp only [Function.comp_apply]
    ring
  -- measurability and the bound `|μ_y| ≤ c` in every chart, piece by piece
  have hcoef : ∀ y : R, AEStronglyMeasurable (μ y) (volume.restrict (chartAt ℂ y).target) ∧
      ∀ᵐ w ∂(volume.restrict (chartAt ℂ y).target), ‖μ y w‖ ≤ c := by
    intro y
    have hOU : (chartAt ℂ y).target = ⋃ i, (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i := by
      rw [← inter_iUnion, ← preimage_iUnion, hP.2.2, preimage_univ, inter_univ]
    have key : ∀ i, AEStronglyMeasurable (μ y)
        (volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i)) ∧
        ∀ᵐ w ∂(volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i)), ‖μ y w‖ ≤ c := by
      intro i
      set A := LiZhongQC.chartTransition (x i) y with hAdef
      set W := (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ (x i)).source with hWdef
      have hWo : IsOpen W := (chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ (x i)).open_source
      have hAc : ContinuousOn A W := fun w hw =>
        (LiZhongQC.s23_transition_differentiableAt (x i) y hw.1 hw.2).continuousAt.continuousWithinAt
      -- `Oᵢ = W ∩ A⁻¹(φ_{xᵢ}(Pᵢ))` is measurable
      have hpre : ∀ M : Set ℂ, MeasurableSet M → MeasurableSet (W ∩ A ⁻¹' M) := by
        intro M hM
        have hpw := hAc.measurable_piecewise (continuousOn_const (c := (0 : ℂ))) hWo.measurableSet
        have heq : W ∩ A ⁻¹' M = W ∩ (W.piecewise A (fun _ => (0 : ℂ))) ⁻¹' M := by
          ext w
          simp only [mem_inter_iff, mem_preimage]
          constructor
          · rintro ⟨hwW, hw⟩
            exact ⟨hwW, by rwa [piecewise_eq_of_mem _ _ _ hwW]⟩
          · rintro ⟨hwW, hw⟩
            exact ⟨hwW, by rwa [piecewise_eq_of_mem _ _ _ hwW] at hw⟩
        rw [heq]
        exact hWo.measurableSet.inter (hpw hM)
      have hOeq : (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i = W ∩ A ⁻¹' (chartAt ℂ (x i) '' P i) := by
        ext w
        constructor
        · rintro ⟨hwt, hwP⟩
          exact ⟨⟨hwt, (hP.1 i).1 hwP⟩, ⟨_, hwP, rfl⟩⟩
        · rintro ⟨⟨hwt, hws⟩, q, hq, hqe⟩
          exact ⟨hwt, mem_preimage.2 ((chartAt ℂ (x i)).injOn ((hP.1 i).1 hq) hws hqe ▸ hq)⟩
      have hOm : MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i) := by
        rw [hOeq]
        exact hpre _ (hP.1 i).2
      have hOW : (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i ⊆ W := fun w hw => ⟨hw.1, (hP.1 i).1 hw.2⟩
      have hAm : AEMeasurable A (volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i)) :=
        (hAc.mono hOW).aemeasurable hOm
      -- `A` pulls null subsets of `φ_{xᵢ}(Pᵢ)` back to null sets (the inverse transition maps null sets to null sets)
      have hac : (volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i)).map A ≪
          volume.restrict (chartAt ℂ (x i) '' P i) := by
        refine Measure.AbsolutelyContinuous.mk fun N hNm hN0 => ?_
        rw [Measure.map_apply_of_aemeasurable hAm hNm, Measure.restrict_apply' hOm]
        rw [Measure.restrict_apply hNm] at hN0
        refine measure_mono_null (t := LiZhongQC.chartTransition y (x i) ''
          (N ∩ chartAt ℂ (x i) '' P i ∩ ((chartAt ℂ (x i)).target ∩ (chartAt ℂ (x i)).symm ⁻¹' (chartAt ℂ y).source)))
          ?_ ?_
        · rintro w ⟨hwN, hwO⟩
          have hm := LiZhongQC.s23_transition_mem hwO.1 ((hP.1 i).1 hwO.2)
          refine ⟨A w, ⟨⟨hwN, _, hwO.2, rfl⟩, hm.1, hm.2.1⟩, ?_⟩
          show chartAt ℂ y ((chartAt ℂ (x i)).symm (A w)) = w
          rw [hm.2.2, (chartAt ℂ y).right_inv hwO.1]
        · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (fun v hv => ?_)
            (measure_mono_null (fun v hv => hv.1) hN0)
          exact ((LiZhongQC.s23_transition_differentiableAt y (x i) hv.2.1 hv.2.2).restrictScalars
            ℝ).differentiableWithinAt
      have hu : Measurable fun w => conj (deriv A w) / deriv A w :=
        (Complex.continuous_conj.measurable.comp (measurable_deriv A)).div (measurable_deriv A)
      have hgA : AEStronglyMeasurable (fun w => g i (A w))
          (volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i)) :=
        ((hgm i).mono_ac hac).comp_aemeasurable hAm
      have hbd : ∀ᵐ w ∂(volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i)),
          ‖g i (A w)‖ ≤ c := ae_of_ae_map hAm (hac.ae_le (hgc i))
      refine ⟨(hgA.mul hu.aestronglyMeasurable).congr ?_, ?_⟩
      · exact (ae_restrict_iff' hOm).2 (Eventually.of_forall fun w hw => (hμ y w i hw.2).symm)
      · filter_upwards [hbd, ae_restrict_mem hOm] with w hw hwO
        rw [hμ y w i hwO.2, norm_mul]
        calc ‖g i (A w)‖ * ‖conj (deriv A w) / deriv A w‖ ≤ ‖g i (A w)‖ * 1 := by
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              rw [norm_div, Complex.norm_conj]
              exact div_self_le_one _
          _ ≤ c := by
              rw [mul_one]
              exact hw
    rw [hOU]
    exact ⟨aestronglyMeasurable_iUnion_iff.2 fun i => (key i).1, (ae_restrict_iUnion_iff _ _).2 fun i => (key i).2⟩
  refine ⟨μ, ⟨c, fun x' y => ?_, fun y => ⟨(hcoef y).1, (hcoef y).2⟩⟩, hval, ?_⟩
  · have hm : MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x').source) :=
      ((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x').open_source).measurableSet
    exact (ae_restrict_iff' hm).2 (Eventually.of_forall (hlaw x' y))
  · refine iSup_le fun y => ?_
    rw [eLpNorm_exponent_top (hcoef y).1]
    exact eLpNormEssSup_le_of_ae_bound (hcoef y).2

/-- Helper (B-SURF II, §3.1, §3.3). Splitting the pairing along a set `C ⊆ R`:
`|(φ, μ)| ≤ ‖μ‖∞ ∬_C |φ| + ‖μ|_{R∖C}‖∞ ‖φ‖` for `φ ∈ A(R)` and a Beltrami differential `μ` (on the partition chosen in
`pairingRS`, with the partition independence `LiZhongQC.s26v_surfaceIntegral_eq_tsum` of the surface integrals). -/
theorem gl31_pairingRS_split [IsManifold 𝓘(ℂ) ω R] {φ μ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R)
    (hμ : μ ∈ beltramiSpace R) (C : Set R) :
    ‖pairingRS φ μ‖ₑ ≤ beltramiNormRS μ *
        LiZhongQC.surfaceIntegral φ (fun y z => C.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z)) +
      (⨆ x : R, eLpNorm (μ x) ⊤ (volume.restrict ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Cᶜ))) *
        quadDiffNorm φ := by
  have hμ' := hμ
  obtain ⟨k, -, hbd⟩ := hμ'
  have h := gl31_exists_partition_of_ne_top hφ.2.ne
  set B := ⨆ y : R, eLpNorm (μ y) ⊤ (volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Cᶜ))
  have ha : beltramiNormRS μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal k) ENNReal.ofReal_ne_top (iSup_le fun y => ?_)
    rw [eLpNorm_exponent_top (hbd y).1]
    exact eLpNormEssSup_le_of_ae_bound (hbd y).2
  -- `|μ| ≤ ‖μ‖∞` a.e. in every chart
  have hA : ∀ y : R, ∀ᵐ z ∂(volume.restrict (chartAt ℂ y).target), ‖μ y z‖ₑ ≤ beltramiNormRS μ := by
    intro y
    filter_upwards [ae_le_eLpNormEssSup (μ := volume.restrict (chartAt ℂ y).target) (f := μ y)] with z hz
    rw [← eLpNorm_exponent_top (hbd y).1] at hz
    exact hz.trans (le_iSup (fun y => eLpNorm (μ y) ⊤ (volume.restrict (chartAt ℂ y).target)) y)
  -- `|μ| ≤ B` off a null set of the part of every chart over `R ∖ C` (a set that need not be measurable)
  have hB : ∀ y : R, volume ({z | ¬ ‖μ y z‖ₑ ≤ B} ∩ ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Cᶜ)) = 0 := by
    intro y
    have hm : AEStronglyMeasurable (μ y) (volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Cᶜ)) :=
      (hbd y).1.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
    have h0 : ∀ᵐ z ∂(volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Cᶜ)), ‖μ y z‖ₑ ≤ B := by
      filter_upwards [ae_le_eLpNormEssSup
        (μ := volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Cᶜ)) (f := μ y)] with z hz
      rw [← eLpNorm_exponent_top hm] at hz
      exact hz.trans (le_iSup (fun y => eLpNorm (μ y) ⊤
        (volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' Cᶜ))) y)
    exact le_antisymm ((Measure.le_restrict_apply _ _).trans (ae_iff.1 h0).le) zero_le
  -- the bound on every piece of a chart partition: `|φμ| ≤ ‖μ‖∞ 𝟙_C |φ| + B |φ|` a.e.
  have hpt : ∀ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P → ∀ i,
      ∫⁻ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z * μ (x i) z‖ₑ ≤
        beltramiNormRS μ * (∫⁻ z in chartAt ℂ (x i) '' P i,
          C.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ (x i)).symm z) * ENNReal.ofReal ‖φ (x i) z‖) +
        B * ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖φ (x i) z‖ := by
    intro x P hP i
    have hGm := (hP.1 i).2
    have hGt : chartAt ℂ (x i) '' P i ⊆ (chartAt ℂ (x i)).target :=
      image_subset_iff.2 fun y hy => (chartAt ℂ (x i)).map_source ((hP.1 i).1 hy)
    have hφm : AEMeasurable (fun z => ENNReal.ofReal ‖φ (x i) z‖) (volume.restrict (chartAt ℂ (x i) '' P i)) :=
      (((hφ.1.2 (x i)).continuousOn.mono hGt).aemeasurable (μ := volume) hGm).norm.ennreal_ofReal
    have hA' := ae_restrict_of_ae_restrict_of_subset hGt (hA (x i))
    have hB' : ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)),
        z ∈ (chartAt ℂ (x i)).target ∩ (chartAt ℂ (x i)).symm ⁻¹' Cᶜ → ‖μ (x i) z‖ₑ ≤ B := by
      refine ae_iff.2 (measure_mono_null (t := {z | ¬ ‖μ (x i) z‖ₑ ≤ B} ∩
        ((chartAt ℂ (x i)).target ∩ (chartAt ℂ (x i)).symm ⁻¹' Cᶜ))
        (fun z hz => ⟨(not_imp.1 hz).2, (not_imp.1 hz).1⟩) ?_)
      exact le_antisymm ((Measure.restrict_apply_le _ _).trans (hB (x i)).le) zero_le
    calc ∫⁻ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z * μ (x i) z‖ₑ
        ≤ ∫⁻ z in chartAt ℂ (x i) '' P i, (beltramiNormRS μ *
            (C.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ (x i)).symm z) * ENNReal.ofReal ‖φ (x i) z‖) +
          B * ENNReal.ofReal ‖φ (x i) z‖) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hA', hB', ae_restrict_mem hGm] with z hzA hzB hzG
          rw [enorm_mul, ← ofReal_norm]
          by_cases hc : (chartAt ℂ (x i)).symm z ∈ C
          · simp only [indicator_of_mem hc, one_mul]
            exact le_add_right ((mul_comm _ _).trans_le (mul_le_mul_left hzA _))
          · simp only [indicator_of_notMem hc, zero_mul, mul_zero, zero_add]
            exact (mul_comm _ _).trans_le (mul_le_mul_left (hzB ⟨hGt hzG, hc⟩) _)
      _ = _ := by
          rw [lintegral_add_right' _ (hφm.const_mul B), lintegral_const_mul' _ _ ha,
            lintegral_const_mul'' _ hφm]
  -- sum over the partition chosen in `pairingRS`, with the partition independence of both surface integrals
  have hS1 := LiZhongQC.s26v_surfaceIntegral_eq_tsum hφ.1 (C.indicator fun _ => (1 : ℝ≥0∞))
    h.choose_spec.choose_spec
  have hS2 : quadDiffNorm φ = ∑' i, ∫⁻ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i,
      ENNReal.ofReal ‖φ (h.choose i) z‖ := by
    have e := LiZhongQC.s26v_surfaceIntegral_eq_tsum hφ.1 (fun _ => (1 : ℝ≥0∞)) h.choose_spec.choose_spec
    simp only [one_mul] at e
    exact e
  rw [pairingRS, dite_eq_left h, hS1, hS2, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  calc _ ≤ ∑' i, ‖∫ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i,
        φ (h.choose i) z * μ (h.choose i) z‖ₑ := enorm_tsum_le_tsum_enorm
    _ ≤ ∑' i, ∫⁻ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i,
        ‖φ (h.choose i) z * μ (h.choose i) z‖ₑ := ENNReal.tsum_le_tsum fun i => enorm_integral_le_lintegral_enorm _
    _ ≤ _ := ENNReal.tsum_le_tsum fun i => hpt _ _ h.choose_spec.choose_spec i

/-- Helper (B-SURF II, §3.1). `|(φ, μ)| ≤ ‖μ‖∞ ‖φ‖` for `φ ∈ A(R)` and a Beltrami differential `μ` (the case `C = ∅`
of `gl31_pairingRS_split`). -/
theorem gl31_pairingRS_le [IsManifold 𝓘(ℂ) ω R] {φ μ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R)
    (hμ : μ ∈ beltramiSpace R) :
    ‖pairingRS φ μ‖ ≤ (beltramiNormRS μ).toReal * (quadDiffNorm φ).toReal := by
  obtain ⟨x, P, hP⟩ := gl31_exists_partition_of_ne_top hφ.2.ne
  have h1 := gl31_pairingRS_split hφ hμ ∅
  have h0 := LiZhongQC.s26v_surfaceIntegral_eq_tsum hφ.1 ((∅ : Set R).indicator fun _ => (1 : ℝ≥0∞)) hP
  simp only [indicator_empty, zero_mul, lintegral_zero, tsum_zero] at h0
  simp only [indicator_empty, compl_empty, preimage_univ, inter_univ] at h1
  rw [h0, mul_zero, zero_add] at h1
  have h2 : ‖pairingRS φ μ‖ₑ ≤ beltramiNormRS μ * quadDiffNorm φ := h1
  have ha : beltramiNormRS μ ≠ ⊤ := by
    obtain ⟨k, -, hbd⟩ := hμ
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal k) ENNReal.ofReal_ne_top (iSup_le fun y => ?_)
    rw [eLpNorm_exponent_top (hbd y).1]
    exact eLpNormEssSup_le_of_ae_bound (hbd y).2
  calc ‖pairingRS φ μ‖ = (‖pairingRS φ μ‖ₑ).toReal := (toReal_enorm _).symm
    _ ≤ (beltramiNormRS μ * quadDiffNorm φ).toReal := ENNReal.toReal_mono (ENNReal.mul_ne_top ha hφ.2.ne) h2
    _ = (beltramiNormRS μ).toReal * (quadDiffNorm φ).toReal := ENNReal.toReal_mul

/-- Helper (B-SURF II, §3.1). `A(R)` is closed under addition (the triangle inequality on one chart partition, with
the partition independence `LiZhongQC.s26v_surfaceIntegral_eq_tsum`). -/
theorem gl31_add_mem [IsManifold 𝓘(ℂ) ω R] {φ ψ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R)
    (hψ : ψ ∈ integrableHolQDSet R) : φ + ψ ∈ integrableHolQDSet R := by
  obtain ⟨x, P, hP⟩ := gl31_exists_partition_of_ne_top hφ.2.ne
  obtain ⟨S, E, -, hadd, -, hnorm, -⟩ := gl31_model hP
  have hm := (holQuadDiffSubmodule R).add_mem hφ.1 hψ.1
  refine ⟨hm, ?_⟩
  rw [← (hnorm _ hm).2, hadd]
  calc ∫⁻ w in S, ‖(E φ + E ψ) w‖ₑ ≤ ∫⁻ w in S, (‖E φ w‖ₑ + ‖E ψ w‖ₑ) :=
        lintegral_mono fun w => enorm_add_le _ _
    _ = (∫⁻ w in S, ‖E φ w‖ₑ) + ∫⁻ w in S, ‖E ψ w‖ₑ := lintegral_add_left' (hnorm φ hφ.1).1.enorm _
    _ < ⊤ := by
        rw [(hnorm φ hφ.1).2, (hnorm ψ hψ.1).2]
        exact ENNReal.add_lt_top.2 ⟨hφ.2, hψ.2⟩

/-- Helper (B-SURF II, §3.1). The norm of `A(R)` is homogeneous: `‖c φ‖ = |c| ‖φ‖` (on one chart partition). -/
theorem gl31_quadDiffNorm_smul [IsManifold 𝓘(ℂ) ω R] {φ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R) (c : ℂ) :
    quadDiffNorm (c • φ) = ‖c‖ₑ * quadDiffNorm φ := by
  obtain ⟨x, P, hP⟩ := gl31_exists_partition_of_ne_top hφ.2.ne
  obtain ⟨S, E, -, -, hsmul, hnorm, -⟩ := gl31_model hP
  have hm := (holQuadDiffSubmodule R).smul_mem c hφ.1
  rw [← (hnorm _ hm).2, ← (hnorm _ hφ.1).2, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul]
  exact lintegral_const_mul' _ _ enorm_ne_top

/-- Helper (B-SURF II, §3.1). The integral of a holomorphic quadratic differential over one chart target is at most its
norm: `∬_{φ_y(U_y)} |φ_y| ≤ ‖φ‖` (a chart partition whose first piece is the source of the chart at `y`). -/
theorem gl31_chart_integral_le [IsManifold 𝓘(ℂ) ω R] {φ : R → ℂ → ℂ} (hφ : φ ∈ holQuadDiffSubmodule R) (y : R) :
    ∫⁻ z in (chartAt ℂ y).target, ‖φ y z‖ₑ ≤ quadDiffNorm φ := by
  rcases eq_or_ne (quadDiffNorm φ) ⊤ with htop | hne
  · rw [htop]
    exact le_top
  obtain ⟨x, P, hP⟩ := gl31_exists_partition_of_ne_top hne
  -- the partition `Q`: the source of the chart at `y` first, then the pieces of `P` with that source removed
  have hQP : IsChartPartition R (fun i => Nat.casesOn (motive := fun _ => R) i y x)
      (fun i => Nat.casesOn (motive := fun _ => Set R) i (chartAt ℂ y).source
        fun j => P j \ (chartAt ℂ y).source) := by
    refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
    · rcases i with _ | j
      · exact ⟨subset_rfl, by
          show MeasurableSet (chartAt ℂ y '' (chartAt ℂ y).source)
          rw [(chartAt ℂ y).image_source_eq_target]
          exact (chartAt ℂ y).open_target.measurableSet⟩
      · refine ⟨sdiff_subset.trans (hP.1 j).1, ?_⟩
        show MeasurableSet (chartAt ℂ (x j) '' (P j \ (chartAt ℂ y).source))
        have heq : chartAt ℂ (x j) '' (P j \ (chartAt ℂ y).source) = chartAt ℂ (x j) '' P j \
            ((chartAt ℂ (x j)).target ∩ (chartAt ℂ (x j)).symm ⁻¹' (chartAt ℂ y).source) := by
          ext z
          constructor
          · rintro ⟨q, ⟨hq, hqy⟩, rfl⟩
            refine ⟨⟨q, hq, rfl⟩, fun hz => hqy ?_⟩
            have h2 := hz.2
            rwa [mem_preimage, (chartAt ℂ (x j)).left_inv ((hP.1 j).1 hq)] at h2
          · rintro ⟨⟨q, hq, rfl⟩, hz⟩
            refine ⟨q, ⟨hq, fun hqy => hz ⟨(chartAt ℂ (x j)).map_source ((hP.1 j).1 hq), ?_⟩⟩, rfl⟩
            rw [mem_preimage, (chartAt ℂ (x j)).left_inv ((hP.1 j).1 hq)]
            exact hqy
        rw [heq]
        exact (hP.1 j).2.diff ((chartAt ℂ (x j)).isOpen_inter_preimage_symm
          (chartAt ℂ y).open_source).measurableSet
    · rcases i with _ | i <;> rcases j with _ | j
      · exact absurd rfl hij
      · exact Set.disjoint_left.2 fun q hq hq' => hq'.2 hq
      · exact Set.disjoint_left.2 fun q hq hq' => hq.2 hq'
      · exact (hP.2.1 fun h => hij (by rw [h])).mono sdiff_subset sdiff_subset
    · refine eq_univ_of_forall fun q => ?_
      by_cases hq : q ∈ (chartAt ℂ y).source
      · exact mem_iUnion.2 ⟨0, hq⟩
      · have hq' : q ∈ ⋃ j, P j := by
          rw [hP.2.2]
          exact mem_univ q
        obtain ⟨j, hj⟩ := mem_iUnion.1 hq'
        exact mem_iUnion.2 ⟨j + 1, hj, hq⟩
  have e := LiZhongQC.s26v_surfaceIntegral_eq_tsum hφ (fun _ => (1 : ℝ≥0∞)) hQP
  simp only [one_mul, ofReal_norm] at e
  rw [show quadDiffNorm φ = _ from e]
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum 0)
  show ∫⁻ z in (chartAt ℂ y).target, ‖φ y z‖ₑ = ∫⁻ z in chartAt ℂ y '' (chartAt ℂ y).source, ‖φ y z‖ₑ
  rw [(chartAt ℂ y).image_source_eq_target]

/-- Helper (B-SURF II, §3.1). A holomorphic quadratic differential of norm `0` vanishes (in every chart it is `0` a.e.
on the open target by `gl31_chart_integral_le`, hence `0` there by continuity, and `0` off the target). -/
theorem gl31_norm_eq_zero [IsManifold 𝓘(ℂ) ω R] {φ : R → ℂ → ℂ} (hφ : φ ∈ holQuadDiffSubmodule R)
    (h0 : quadDiffNorm φ = 0) : φ = 0 := by
  funext y z
  by_cases hz : z ∈ (chartAt ℂ y).target
  · have h0' : ∫⁻ w in (chartAt ℂ y).target, ‖φ y w‖ₑ = 0 :=
      le_antisymm ((gl31_chart_integral_le hφ y).trans h0.le) zero_le
    have hc : ContinuousOn (φ y) (chartAt ℂ y).target := (hφ.2 y).continuousOn
    have hae : φ y =ᵐ[volume.restrict (chartAt ℂ y).target] 0 := by
      have h1 := (lintegral_eq_zero_iff'
        (hc.aemeasurable (μ := volume) (chartAt ℂ y).open_target.measurableSet).enorm).1 h0'
      filter_upwards [h1] with w hw
      simpa using hw
    exact (Measure.eqOn_open_of_ae_eq hae (chartAt ℂ y).open_target hc continuousOn_const) hz
  · exact hφ.1.1 y z hz

/-- Helper (B-SURF II, §3.1, the Cauchy estimate of Theorem 1). Uniform local bounds by the norm: near every point of a
chart target, `π δ² |φ_y(w)| ≤ ‖φ‖` (mean value on discs, `LiZhongQC.h36p_meanvalue`, and
`gl31_chart_integral_le`). -/
theorem gl31_locBounded [IsManifold 𝓘(ℂ) ω R] (y : R) {z : ℂ} (hz : z ∈ (chartAt ℂ y).target) :
    ∃ δ > (0 : ℝ), ball z δ ⊆ (chartAt ℂ y).target ∧ ∀ φ ∈ holQuadDiffSubmodule R, ∀ w ∈ ball z δ,
      ENNReal.ofReal (π * δ ^ 2) * ‖φ y w‖ₑ ≤ quadDiffNorm φ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (chartAt ℂ y).open_target z hz
  refine ⟨r / 2, half_pos hr, (ball_subset_ball (half_le_self hr.le)).trans hball, fun φ hφ w hw => ?_⟩
  have hsub : closedBall w (r / 2) ⊆ (chartAt ℂ y).target := fun v hv => hball (by
    rw [mem_closedBall] at hv
    rw [mem_ball] at hw ⊢
    linarith [dist_triangle v w z])
  have hmv := LiZhongQC.h36p_meanvalue (hφ.2 y) (half_pos hr) hsub
  calc ENNReal.ofReal (π * (r / 2) ^ 2) * ‖φ y w‖ₑ
      = ENNReal.ofReal (π * (r / 2) ^ 2) * ENNReal.ofReal ‖φ y w‖ := by rw [ofReal_norm]
    _ ≤ ∫⁻ v in ball w (r / 2), ENNReal.ofReal ‖φ y v‖ := hmv
    _ ≤ ∫⁻ v in (chartAt ℂ y).target, ENNReal.ofReal ‖φ y v‖ :=
        lintegral_mono_set (ball_subset_closedBall.trans hsub)
    _ = ∫⁻ v in (chartAt ℂ y).target, ‖φ y v‖ₑ := by simp only [ofReal_norm]
    _ ≤ quadDiffNorm φ := gl31_chart_integral_le hφ y

/-- Helper (B-SURF II, §3.1, the normal-family argument of Theorems 1 and 3). A sequence in `Q(R)` of bounded norm has
a subsequence converging locally uniformly in every chart: Montel (`LiZhongQC.h35_montel_loc`) on the disjoint
translates of countably many chart balls covering `R`, with the bounds of `gl31_locBounded`, then the transformation
law carries the convergence to every chart. -/
theorem gl31_montel [IsManifold 𝓘(ℂ) ω R] {φ : ℕ → R → ℂ → ℂ} (hφ : ∀ n, φ n ∈ holQuadDiffSubmodule R)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hb : ∀ n, quadDiffNorm (φ n) ≤ C) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ g : R → ℂ → ℂ, ∀ y : R,
      TendstoLocallyUniformlyOn (fun k => φ (σ k) y) (g y) atTop (chartAt ℂ y).target := by
  classical
  -- a chart partition exists (finite norms), so `R` is second countable and nonempty
  obtain ⟨x₀, P₀, hP₀⟩ := gl31_exists_partition_of_ne_top (ne_top_of_le_ne_top hC (hb 0))
  have := gl31_secondCountable_of_partition hP₀
  have : Nonempty R := ⟨x₀ 0⟩
  -- chart balls `Bᵢ = B(cᵢ, rᵢ)` (`rᵢ ≤ 1`, inside the targets) containing the chart images of pieces covering `R`
  obtain ⟨x, P, r, -, hP, hr, -⟩ := gl31_exists_chartPartition_cpt (C := (∅ : Set R)) isCompact_empty
  -- the translates `B(4i, rᵢ) = Bᵢ + tᵢ` are pairwise disjoint
  have hdisj : ∀ i j : ℕ, ∀ w : ℂ, w ∈ ball (4 * ((i : ℕ) : ℂ)) (r i) → w ∈ ball (4 * ((j : ℕ) : ℂ)) (r j) → i = j := by
    intro i j w hi hj
    rw [mem_ball, dist_eq_norm] at hi hj
    have h1 := (abs_re_le_norm (w - 4 * ((i : ℕ) : ℂ))).trans_lt (hi.trans_le (hr i).2.1)
    have h2 := (abs_re_le_norm (w - 4 * ((j : ℕ) : ℂ))).trans_lt (hj.trans_le (hr j).2.1)
    simp only [sub_re, mul_re, natCast_re, natCast_im, mul_zero, sub_zero] at h1 h2
    norm_num at h1 h2
    rw [abs_lt] at h1 h2
    have h3 : (4 * i : ℝ) < 4 * j + 2 := by linarith
    have h4 : (4 * j : ℝ) < 4 * i + 2 := by linarith
    have h5 : 4 * i < 4 * j + 2 := by exact_mod_cast h3
    have h6 : 4 * j < 4 * i + 2 := by exact_mod_cast h4
    omega
  set t : ℕ → ℂ := fun i => 4 * ((i : ℕ) : ℂ) - chartAt ℂ (x i) (x i) with htdef
  have hmemB : ∀ i, ∀ w ∈ ball (4 * ((i : ℕ) : ℂ)) (r i), w - t i ∈ ball (chartAt ℂ (x i) (x i)) (r i) := by
    intro i w hw
    rw [mem_ball, dist_eq_norm] at hw ⊢
    rw [htdef]
    convert hw using 2
    ring
  set U : Set ℂ := ⋃ i, ball (4 * ((i : ℕ) : ℂ)) (r i) with hUdef
  have hUo : IsOpen U := isOpen_iUnion fun i => isOpen_ball
  set f : ℕ → ℂ → ℂ := fun n w => ∑' i, (ball (4 * ((i : ℕ) : ℂ)) (r i)).indicator (fun w => φ n (x i) (w - t i)) w
    with hfdef
  have hfval : ∀ n i, ∀ w ∈ ball (4 * ((i : ℕ) : ℂ)) (r i), f n w = φ n (x i) (w - t i) := by
    intro n i w hw
    rw [hfdef]
    dsimp only
    rw [tsum_eq_single i fun j hj => indicator_of_notMem (fun hw' => hj (hdisj j i w hw' hw)) _,
      indicator_of_mem hw]
  have hφd : ∀ n i, ∀ z ∈ ball (chartAt ℂ (x i) (x i)) (r i), DifferentiableAt ℂ (φ n (x i)) z := fun n i z hz =>
    ((hφ n).2 (x i)).differentiableAt ((chartAt ℂ (x i)).open_target.mem_nhds
      ((hr i).2.2.1 (ball_subset_closedBall hz)))
  -- Montel on `U`
  have hdiff : ∀ n, DifferentiableOn ℂ (f n) U := by
    intro n w hw
    obtain ⟨i, hi⟩ := mem_iUnion.1 hw
    have hev : (fun v => φ n (x i) (v - t i)) =ᶠ[𝓝 w] f n := by
      filter_upwards [isOpen_ball.mem_nhds hi] with v hv
      exact (hfval n i v hv).symm
    exact (((hφd n i _ (hmemB i w hi)).comp w ((differentiableAt_id).sub_const (t i))).congr_of_eventuallyEq
      hev.symm).differentiableWithinAt
  have hbd : ∀ w ∈ U, ∃ δ > 0, ball w δ ⊆ U ∧ ∃ M : ℝ, ∀ n, ∀ v ∈ ball w δ, ‖f n v‖ ≤ M := by
    intro w hw
    obtain ⟨i, hi⟩ := mem_iUnion.1 hw
    have hz := (hr i).2.2.1 (ball_subset_closedBall (hmemB i w hi))
    obtain ⟨δ₁, hδ₁, hball₁, hbound⟩ := gl31_locBounded (x i) hz
    have hδ₂ : 0 < r i - dist w (4 * ((i : ℕ) : ℂ)) := sub_pos.2 (mem_ball.1 hi)
    refine ⟨min δ₁ (r i - dist w (4 * ((i : ℕ) : ℂ))), lt_min hδ₁ hδ₂, fun v hv => mem_iUnion.2 ⟨i, ?_⟩,
      C.toReal / (π * δ₁ ^ 2), fun n v hv => ?_⟩
    · rw [mem_ball] at hv ⊢
      linarith [dist_triangle v w (4 * ((i : ℕ) : ℂ)), min_le_right δ₁ (r i - dist w (4 * ((i : ℕ) : ℂ)))]
    · have hvi : v ∈ ball (4 * ((i : ℕ) : ℂ)) (r i) := by
        rw [mem_ball] at hv ⊢
        linarith [dist_triangle v w (4 * ((i : ℕ) : ℂ)), min_le_right δ₁ (r i - dist w (4 * ((i : ℕ) : ℂ)))]
      rw [hfval n i v hvi]
      have hvz : v - t i ∈ ball (w - t i) δ₁ := by
        rw [mem_ball, dist_sub_right]
        exact (mem_ball.1 hv).trans_le (min_le_left _ _)
      have h1 := (hbound (φ n) (hφ n) _ hvz).trans (hb n)
      have hpos : 0 < π * δ₁ ^ 2 := by positivity
      rw [← ofReal_norm, ← ENNReal.ofReal_mul hpos.le, ENNReal.ofReal_le_iff_le_toReal hC] at h1
      rw [le_div_iff₀ hpos]
      linarith
  obtain ⟨σ, hσ, G, -, hG⟩ := LiZhongQC.h35_montel_loc hUo f hdiff hbd
  -- convergence in the charts at the `xᵢ`, on the balls `Bᵢ`
  have hconv : ∀ i, TendstoLocallyUniformlyOn (fun k => φ (σ k) (x i)) (fun z => G (z + t i)) atTop
      (ball (chartAt ℂ (x i) (x i)) (r i)) := by
    intro i
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε z hz
    have hzU : z + t i ∈ ball (4 * ((i : ℕ) : ℂ)) (r i) := by
      rw [mem_ball, dist_eq_norm] at hz ⊢
      rw [htdef]
      convert hz using 2
      ring
    obtain ⟨u, hu, hev⟩ := Metric.tendstoLocallyUniformlyOn_iff.1 hG ε hε (z + t i) (mem_iUnion.2 ⟨i, hzU⟩)
    rw [nhdsWithin_eq_nhds.2 (hUo.mem_nhds (mem_iUnion.2 ⟨i, hzU⟩))] at hu
    have hu' : (fun v => v + t i) ⁻¹' (u ∩ ball (4 * ((i : ℕ) : ℂ)) (r i)) ∈ 𝓝 z :=
      (continuous_id.add continuous_const : Continuous fun v : ℂ => v + t i).continuousAt.preimage_mem_nhds
        (inter_mem hu (isOpen_ball.mem_nhds hzU))
    refine ⟨_, mem_nhdsWithin_of_mem_nhds hu', ?_⟩
    filter_upwards [hev] with k hk v hv
    have h := hk (v + t i) hv.1
    rwa [hfval (σ k) i _ hv.2, add_sub_cancel_right] at h
  -- every chart: `φ_y = φ_{xᵢ}(T) T′²` near each point (`T = φ_{xᵢ} ∘ φ_y⁻¹`), uniformly on a closed disc
  refine ⟨σ, hσ, fun y w => limUnder atTop fun k => φ (σ k) y w, fun y => ?_⟩
  refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun w₀ hw₀ => ?_
  have hcovP : (chartAt ℂ y).symm w₀ ∈ ⋃ i, P i := by
    rw [hP.2.2]
    exact mem_univ _
  obtain ⟨i, hi⟩ := mem_iUnion.1 hcovP
  have hsrc := (hP.1 i).1 hi
  set T := LiZhongQC.chartTransition (x i) y with hTdef
  set W := (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ (x i)).source with hWdef
  have hWo : IsOpen W := (chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ (x i)).open_source
  have hTd : DifferentiableOn ℂ T W := fun w hw =>
    (LiZhongQC.s23_transition_differentiableAt (x i) y hw.1 hw.2).differentiableWithinAt
  have hTw₀ : T w₀ ∈ ball (chartAt ℂ (x i) (x i)) (r i) := (hr i).2.2.2 ⟨_, hi, rfl⟩
  have hN : W ∩ T ⁻¹' ball (chartAt ℂ (x i) (x i)) (r i) ∈ 𝓝 w₀ :=
    inter_mem (hWo.mem_nhds ⟨hw₀, hsrc⟩) ((hTd.continuousOn.continuousAt (hWo.mem_nhds ⟨hw₀, hsrc⟩)).preimage_mem_nhds
      (isOpen_ball.mem_nhds hTw₀))
  obtain ⟨ρ, hρ, hρN⟩ := Metric.mem_nhds_iff.1 hN
  have hKN : closedBall w₀ (ρ / 2) ⊆ W ∩ T ⁻¹' ball (chartAt ℂ (x i) (x i)) (r i) :=
    (closedBall_subset_ball (half_lt_self hρ)).trans hρN
  have hK : IsCompact (closedBall w₀ (ρ / 2)) := isCompact_closedBall _ _
  refine ⟨closedBall w₀ (ρ / 2), mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds _ (half_pos hρ)), ?_⟩
  -- uniform convergence of `φ_{xᵢ}` on the compact image `T(K) ⊆ Bᵢ`
  have hTK : T '' closedBall w₀ (ρ / 2) ⊆ ball (chartAt ℂ (x i) (x i)) (r i) := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hKN hw).2
  have hUi := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).1 (hconv i) _ hTK
    (hK.image_of_continuousOn (hTd.continuousOn.mono fun w hw => (hKN hw).1))
  rw [Metric.tendstoUniformlyOn_iff] at hUi
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (((hTd.deriv hWo).continuousOn).mono fun w hw => (hKN hw).1)
  -- the limit `H = G(T + tᵢ) T′²` on `K`
  have hlaw : ∀ k, ∀ w ∈ closedBall w₀ (ρ / 2), φ (σ k) y w = φ (σ k) (x i) (T w) * deriv T w ^ 2 := fun k w hw =>
    LiZhongQC.s26u_law (hφ (σ k)) y (x i) (hKN hw).1.1 (hKN hw).1.2
  have hunif : TendstoUniformlyOn (fun k => φ (σ k) y) (fun w => G (T w + t i) * deriv T w ^ 2) atTop
      (closedBall w₀ (ρ / 2)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM w₀ (mem_closedBall_self (half_pos hρ).le))
    filter_upwards [hUi (ε / (M ^ 2 + 1)) (by positivity)] with k hk w hw
    have h1 := hk (T w) ⟨w, hw, rfl⟩
    rw [hlaw k w hw, dist_eq_norm, ← sub_mul, norm_mul, norm_pow]
    rw [dist_eq_norm] at h1
    have hMw : ‖deriv T w‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hM w hw) 2
    calc ‖G (T w + t i) - φ (σ k) (x i) (T w)‖ * ‖deriv T w‖ ^ 2
        ≤ ‖G (T w + t i) - φ (σ k) (x i) (T w)‖ * (M ^ 2 + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ < ε / (M ^ 2 + 1) * (M ^ 2 + 1) := mul_lt_mul_of_pos_right h1 (by positivity)
      _ = ε := div_mul_cancel₀ ε (by positivity)
  -- the pointwise limit is `limUnder`
  refine hunif.congr_right fun w hw => ?_
  exact ((hunif.tendsto_at hw).limUnder_eq).symm

/-- Helper for `gl31_surfaceIntegral_eq_tsum_ae` (§3.1). Chart change of variables for a differential with the
transformation law almost everywhere: for a piece `A` in the charts at `x` and `y` with measurable image in the chart at
`x`, `∬_A |q|` is the same in both charts (`LiZhongQC.s26v_a_lintegral_chart_change`, with an a.e. law). -/
theorem gl31_lintegral_chart_change_ae [IsManifold 𝓘(ℂ) ω R] {q : R → ℂ → ℂ} (hq : IsDiffFamilyAE 2 0 q)
    (x y : R) {A : Set R} (hAx : A ⊆ (chartAt ℂ x).source) (hAy : A ⊆ (chartAt ℂ y).source)
    (hAm : MeasurableSet (chartAt ℂ x '' A)) :
    ∫⁻ w in chartAt ℂ y '' A, ENNReal.ofReal ‖q y w‖ = ∫⁻ z in chartAt ℂ x '' A, ENNReal.ofReal ‖q x z‖ := by
  set τ := LiZhongQC.chartTransition y x with hτ
  set s := chartAt ℂ x '' A with hs
  have hmem : ∀ z ∈ s, z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ (chartAt ℂ y).source := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨(chartAt ℂ x).map_source (hAx ha), ?_⟩
    rw [(chartAt ℂ x).left_inv (hAx ha)]
    exact hAy ha
  have hdiff : ∀ z ∈ s, DifferentiableAt ℂ τ z := fun z hz =>
    LiZhongQC.s23_transition_differentiableAt y x (hmem z hz).1 (hmem z hz).2
  have hinj : InjOn τ s := by
    intro z₁ hz₁ z₂ hz₂ h
    have h' : (chartAt ℂ x).symm z₁ = (chartAt ℂ x).symm z₂ :=
      (chartAt ℂ y).injOn (hmem z₁ hz₁).2 (hmem z₂ hz₂).2 h
    rw [← (chartAt ℂ x).right_inv (hmem z₁ hz₁).1, ← (chartAt ℂ x).right_inv (hmem z₂ hz₂).1, h']
  have himg : τ '' s = chartAt ℂ y '' A := by
    ext w
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨a, ha, ?_⟩
      show chartAt ℂ y a = chartAt ℂ y ((chartAt ℂ x).symm (chartAt ℂ x a))
      rw [(chartAt ℂ x).left_inv (hAx ha)]
    · rintro ⟨a, ha, rfl⟩
      refine ⟨chartAt ℂ x a, ⟨a, ha, rfl⟩, ?_⟩
      show chartAt ℂ y ((chartAt ℂ x).symm (chartAt ℂ x a)) = chartAt ℂ y a
      rw [(chartAt ℂ x).left_inv (hAx ha)]
  rw [← himg, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hAm
    (fun z hz => ((hdiff z hz).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt) hinj]
  have hset : s ⊆ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source := fun z hz =>
    ⟨(hmem z hz).1, (hmem z hz).2⟩
  have hlaw : ∀ᵐ z ∂(volume.restrict s), q x z = q y (τ z) * deriv τ z ^ 2 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hset (hq y x)] with z hz
    simpa using hz
  refine lintegral_congr_ae ?_
  filter_upwards [hlaw, ae_restrict_mem hAm] with z hl hz
  have hd := hdiff z hz
  have hdet : (fderiv ℝ τ z).det = ‖deriv τ z‖ ^ 2 := by
    have e := LiZhongQC.det_fderiv_eq_jacobian (hd.restrictScalars ℝ)
    have hj : LiZhongQC.jacobian τ z = ‖LiZhongQC.dz τ z‖ ^ 2 - ‖LiZhongQC.dzbar τ z‖ ^ 2 := rfl
    rw [show (fderiv ℝ τ z).det = LinearMap.det (fderiv ℝ τ z : ℂ →ₗ[ℝ] ℂ) from rfl, e, hj,
      LiZhongQC.dz_eq_deriv hd, (LiZhongQC.cauchyRiemann_iff.1 hd).2, norm_zero]
    ring
  rw [hdet, abs_of_nonneg (by positivity), hl, norm_mul, norm_pow, ENNReal.ofReal_mul (norm_nonneg _)]
  ring

/-- Helper for `gl31_surfaceIntegral_eq_tsum_ae` (§3.1). Two chart partitions give the same partition sum of `|q|` for
a differential with the transformation law a.e. (`LiZhongQC.s26v_a_partition_sum_eq`). -/
theorem gl31_partition_sum_eq_ae [IsManifold 𝓘(ℂ) ω R] {q : R → ℂ → ℂ} (hq : IsDiffFamilyAE 2 0 q)
    {x : ℕ → R} {P : ℕ → Set R} (hP : IsChartPartition R x P) {y : ℕ → R} {Q : ℕ → Set R}
    (hQ : IsChartPartition R y Q) :
    ∑' j, ∫⁻ w in chartAt ℂ (y j) '' Q j, ENNReal.ofReal ‖q (y j) w‖ =
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖q (x i) z‖ := by
  obtain ⟨hPsm, hPd, hPc⟩ := hP
  obtain ⟨hQsm, hQd, hQc⟩ := hQ
  have hAm : ∀ i j, MeasurableSet (chartAt ℂ (x i) '' (P i ∩ Q j)) := fun i j =>
    LiZhongQC.s26v_a_measurableSet_inter (x i) (y j) (hPsm i).1 (hQsm j).1 (hPsm i).2 (hQsm j).2
  have hBm : ∀ i j, MeasurableSet (chartAt ℂ (y j) '' (P i ∩ Q j)) := fun i j => by
    rw [inter_comm]
    exact LiZhongQC.s26v_a_measurableSet_inter (y j) (x i) (hQsm j).1 (hPsm i).1 (hQsm j).2 (hPsm i).2
  have hsrc : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖q (x i) z‖ =
      ∑' j, ∫⁻ z in chartAt ℂ (x i) '' (P i ∩ Q j), ENNReal.ofReal ‖q (x i) z‖ := by
    intro i
    have hU : chartAt ℂ (x i) '' P i = ⋃ j, chartAt ℂ (x i) '' (P i ∩ Q j) := by
      rw [← image_iUnion, ← inter_iUnion, hQc, inter_univ]
    rw [hU, lintegral_iUnion (hAm i)]
    intro j j' hjj'
    exact Disjoint.image (Disjoint.mono inter_subset_right inter_subset_right (hQd hjj'))
      (chartAt ℂ (x i)).injOn (inter_subset_left.trans (hPsm i).1) (inter_subset_left.trans (hPsm i).1)
  have htgt : ∀ j, ∫⁻ w in chartAt ℂ (y j) '' Q j, ENNReal.ofReal ‖q (y j) w‖ =
      ∑' i, ∫⁻ w in chartAt ℂ (y j) '' (P i ∩ Q j), ENNReal.ofReal ‖q (y j) w‖ := by
    intro j
    have hU : chartAt ℂ (y j) '' Q j = ⋃ i, chartAt ℂ (y j) '' (P i ∩ Q j) := by
      rw [← image_iUnion, ← iUnion_inter, hPc, univ_inter]
    rw [hU, lintegral_iUnion (hBm · j)]
    intro i i' hii'
    exact Disjoint.image (Disjoint.mono inter_subset_left inter_subset_left (hPd hii'))
      (chartAt ℂ (y j)).injOn (inter_subset_right.trans (hQsm j).1) (inter_subset_right.trans (hQsm j).1)
  simp only [htgt, hsrc]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun i => tsum_congr fun j => ?_
  exact gl31_lintegral_chart_change_ae hq (x i) (y j) (inter_subset_left.trans (hPsm i).1)
    (inter_subset_right.trans (hQsm j).1) (hAm i j)

/-- Helper for **Theorem 1** (§3.1). Partition independence for differentials with the transformation law only almost
everywhere (`IsDiffFamilyAE 2 0`): `‖q‖` is the partition sum over *any* chart partition. This is
`LiZhongQC.s26v_surfaceIntegral_eq_tsum` (holomorphic `q`) with the chart change of variables
`LiZhongQC.s26v_a_lintegral_chart_change` redone for an a.e. law; measurability of `q` is not needed (the Jacobian
formula is applied to the set, not to `q`). -/
theorem gl31_surfaceIntegral_eq_tsum_ae [IsManifold 𝓘(ℂ) ω R] {q : R → ℂ → ℂ} (hq : IsDiffFamilyAE 2 0 q)
    {x : ℕ → R} {P : ℕ → Set R} (hP : IsChartPartition R x P) :
    quadDiffNorm q = ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖q (x i) z‖ := by
  show (⨅ (y : ℕ → R) (Q : ℕ → Set R) (_ : IsChartPartition R y Q),
    ∑' i, ∫⁻ z in chartAt ℂ (y i) '' Q i, (fun (_ : R) (_ : ℂ) => (1 : ℝ≥0∞)) (y i) z *
      ENNReal.ofReal ‖q (y i) z‖) = _
  refine le_antisymm (iInf_le_of_le x (iInf_le_of_le P (iInf_le_of_le hP ?_)))
    (le_iInf fun y => le_iInf fun Q => le_iInf fun hQ => ?_)
  · simp only [one_mul]
    exact le_rfl
  · simp only [one_mul]
    exact (gl31_partition_sum_eq_ae hq hP hQ).ge

/-- Helper for **Theorem 1** (§3.1). The triangle inequality for the (partition-sum) norm of differentials with the
transformation law a.e. and measurable chart coefficients (`gl31_surfaceIntegral_eq_tsum_ae` on one partition; the
case without a chart partition is `⊤ ≤ ⊤`). -/
theorem gl31_qdn_add_le [IsManifold 𝓘(ℂ) ω R] {q₁ q₂ : R → ℂ → ℂ} (h₁ : IsDiffFamilyAE 2 0 q₁)
    (h₂ : IsDiffFamilyAE 2 0 q₂) (hm₁ : ∀ x : R, AEStronglyMeasurable (q₁ x) (volume.restrict (chartAt ℂ x).target))
    (hm₂ : ∀ x : R, AEStronglyMeasurable (q₂ x) (volume.restrict (chartAt ℂ x).target)) :
    quadDiffNorm (q₁ + q₂) ≤ quadDiffNorm q₁ + quadDiffNorm q₂ := by
  classical
  by_cases h : ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P
  · obtain ⟨x, P, hP⟩ := h
    have haddAE : IsDiffFamilyAE 2 0 (q₁ + q₂) := by
      intro a b
      filter_upwards [h₁ a b, h₂ a b] with z e1 e2
      simp only [Pi.add_apply]
      rw [e1, e2]
      ring
    rw [gl31_surfaceIntegral_eq_tsum_ae haddAE hP, gl31_surfaceIntegral_eq_tsum_ae h₁ hP,
      gl31_surfaceIntegral_eq_tsum_ae h₂ hP, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun i => ?_
    have hGt : chartAt ℂ (x i) '' P i ⊆ (chartAt ℂ (x i)).target :=
      image_subset_iff.2 fun y hy => (chartAt ℂ (x i)).map_source ((hP.1 i).1 hy)
    have hm : AEMeasurable (fun z => ENNReal.ofReal ‖q₁ (x i) z‖) (volume.restrict (chartAt ℂ (x i) '' P i)) :=
      (((hm₁ (x i)).mono_measure (Measure.restrict_mono hGt le_rfl)).aemeasurable.norm).ennreal_ofReal
    rw [← lintegral_add_left' hm]
    refine lintegral_mono fun z => ?_
    simp only [Pi.add_apply]
    rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
  · have h0 : ∀ q : R → ℂ → ℂ, quadDiffNorm q = ⊤ := fun q => by
      by_contra h'
      exact h (gl31_exists_partition_of_ne_top h')
    rw [h0 q₁, h0 q₂, h0 (q₁ + q₂)]
    simp

/-- Helper for **Theorem 1** (§3.1). `A(R)` is complete: a sequence of `A(R)` that is Cauchy for `‖·‖` has a limit
`φ₀ ∈ A(R)`. By `gl31_locBounded` it is locally uniformly Cauchy in every chart, so it converges locally uniformly to a
holomorphic differential (the transformation law passes to the limit pointwise, as in `gl84_limit`), and Fatou along a
chart partition gives `‖φₙ − φ₀‖ ≤ liminf ‖φₙ − φₘ‖`. -/
theorem gl31_complete [IsManifold 𝓘(ℂ) ω R] {φ : ℕ → R → ℂ → ℂ} (hφ : ∀ n, φ n ∈ integrableHolQDSet R)
    (hC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, quadDiffNorm (φ m - φ n) < ENNReal.ofReal ε) :
    ∃ φ₀ ∈ integrableHolQDSet R, Tendsto (fun n => quadDiffNorm (φ n - φ₀)) atTop (𝓝 0) := by
  classical
  have hφh : ∀ n, φ n ∈ holQuadDiffSubmodule R := fun n => (hφ n).1
  have hdh : ∀ m n, φ m - φ n ∈ holQuadDiffSubmodule R := fun m n =>
    (holQuadDiffSubmodule R).sub_mem (hφh m) (hφh n)
  -- uniformly Cauchy near every point of a chart target (`gl31_locBounded`)
  have hloc : ∀ y : R, ∀ z ∈ (chartAt ℂ y).target, ∃ δ > 0, Metric.ball z δ ⊆ (chartAt ℂ y).target ∧
      UniformCauchySeqOn (fun n => φ n y) atTop (Metric.ball z δ) := by
    intro y z hz
    obtain ⟨δ, hδ, hball, hbd⟩ := gl31_locBounded y hz
    refine ⟨δ, hδ, hball, Metric.uniformCauchySeqOn_iff.2 fun ε hε => ?_⟩
    have hc : 0 < π * δ ^ 2 := by positivity
    obtain ⟨N, hN⟩ := hC (ε * (π * δ ^ 2)) (by positivity)
    refine ⟨N, fun m hm n hn w hw => ?_⟩
    have h1 := hbd (φ m - φ n) (hdh m n) w hw
    have h2 := lt_of_le_of_lt h1 (hN m hm n hn)
    rw [← ofReal_norm, ← ENNReal.ofReal_mul hc.le, ENNReal.ofReal_lt_ofReal_iff (by positivity)] at h2
    rw [dist_eq_norm]
    have h3 : ‖(φ m - φ n) y w‖ < ε := by
      nlinarith [h2, hc]
    simpa using h3
  have hcauchy : ∀ y : R, ∀ z ∈ (chartAt ℂ y).target, CauchySeq (fun n => φ n y z) := by
    intro y z hz
    obtain ⟨δ, hδ, -, hu⟩ := hloc y z hz
    exact hu.cauchySeq (Metric.mem_ball_self hδ)
  set g : R → ℂ → ℂ := fun y z => limUnder atTop (fun n => φ n y z) with hg
  have hgt : ∀ y z, z ∈ (chartAt ℂ y).target → Tendsto (fun n => φ n y z) atTop (𝓝 (g y z)) :=
    fun y z hz => (hcauchy y z hz).tendsto_limUnder
  have hgl : ∀ y : R, TendstoLocallyUniformlyOn (fun n => φ n y) (g y) atTop (chartAt ℂ y).target := by
    intro y
    refine tendstoLocallyUniformlyOn_of_forall_exists_nhds fun z hz => ?_
    obtain ⟨δ, hδ, hball, hu⟩ := hloc y z hz
    exact ⟨Metric.ball z δ, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z hδ),
      hu.tendstoUniformlyOn_of_tendsto fun w hw => hgt y w (hball hw)⟩
  -- the limit differential
  set ψ : R → ℂ → ℂ := fun y z => (chartAt ℂ y).target.indicator (g y) z with hψ
  have hψt : ∀ y z, z ∈ (chartAt ℂ y).target → ψ y z = g y z := fun y z hz => indicator_of_mem hz _
  have hlim : ∀ y z, z ∈ (chartAt ℂ y).target → Tendsto (fun n => φ n y z) atTop (𝓝 (ψ y z)) := by
    intro y z hz
    rw [hψt y z hz]
    exact hgt y z hz
  have hψhol : ψ ∈ holQuadDiffSubmodule R := by
    refine ⟨⟨fun y z hz => indicator_of_notMem hz _, fun x y z hz hzs => ?_⟩, fun y => ?_⟩
    · have hτ : LiZhongQC.chartTransition x y z ∈ (chartAt ℂ x).target :=
        (chartAt ℂ x).map_source hzs
      have h1 := hlim y z hz
      have h2 : Tendsto (fun n => φ n y z) atTop
          (𝓝 (ψ x (LiZhongQC.chartTransition x y z) * deriv (LiZhongQC.chartTransition x y) z ^ (2 : ℤ) *
            conj (deriv (LiZhongQC.chartTransition x y) z) ^ (0 : ℤ))) := by
        have h3 := ((hlim x _ hτ).mul_const (deriv (LiZhongQC.chartTransition x y) z ^ (2 : ℤ))).mul_const
          (conj (deriv (LiZhongQC.chartTransition x y) z) ^ (0 : ℤ))
        refine h3.congr fun k => ?_
        exact ((hφh k).1.2 x y z hz hzs).symm
      exact tendsto_nhds_unique h1 h2
    · have h1 : DifferentiableOn ℂ (g y) (chartAt ℂ y).target :=
        (hgl y).differentiableOn (Eventually.of_forall fun k => (hφh k).2 y) (chartAt ℂ y).open_target
      exact h1.congr fun z hz => hψt y z hz
  -- a chart partition and the partition sums
  obtain ⟨x, P, hP⟩ := gl31_exists_partition_of_ne_top (hφ 0).2.ne
  have hGt : ∀ i, chartAt ℂ (x i) '' P i ⊆ (chartAt ℂ (x i)).target := fun i =>
    image_subset_iff.2 fun y hy => (chartAt ℂ (x i)).map_source ((hP.1 i).1 hy)
  have hsum : ∀ χ ∈ holQuadDiffSubmodule R, quadDiffNorm χ =
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖χ (x i) z‖ := by
    intro χ hχ
    have e := LiZhongQC.s26v_surfaceIntegral_eq_tsum hχ (fun _ => (1 : ℝ≥0∞)) hP
    simp only [one_mul] at e
    exact e
  have hdψ : ∀ n, φ n - ψ ∈ holQuadDiffSubmodule R := fun n =>
    (holQuadDiffSubmodule R).sub_mem (hφh n) hψhol
  have hmeas : ∀ χ ∈ holQuadDiffSubmodule R, ∀ i, AEMeasurable (fun z => ENNReal.ofReal ‖χ (x i) z‖)
      (volume.restrict (chartAt ℂ (x i) '' P i)) := fun χ hχ i =>
    (((hχ.2 (x i)).continuousOn.mono (hGt i)).aemeasurable (μ := volume) (hP.1 i).2).norm.ennreal_ofReal
  -- Fatou: `‖φₙ − ψ‖ ≤ liminf_m ‖φₙ − φₘ‖`
  have hfatou : ∀ n, quadDiffNorm (φ n - ψ) ≤ Filter.liminf (fun m => quadDiffNorm (φ n - φ m)) atTop := by
    intro n
    set f : ℕ → ℕ → ℝ≥0∞ := fun m i => ∫⁻ z in chartAt ℂ (x i) '' P i,
      ENNReal.ofReal ‖(φ n - φ m) (x i) z‖ with hf
    have hA : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖(φ n - ψ) (x i) z‖ ≤
        Filter.liminf (fun m => f m i) atTop := by
      intro i
      calc ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖(φ n - ψ) (x i) z‖
          = ∫⁻ z in chartAt ℂ (x i) '' P i, Filter.liminf (fun m => ENNReal.ofReal ‖(φ n - φ m) (x i) z‖) atTop := by
            refine lintegral_congr_ae ?_
            filter_upwards [ae_restrict_mem (hP.1 i).2] with z hz
            symm
            have h1 : Tendsto (fun m => (φ n - φ m) (x i) z) atTop (𝓝 ((φ n - ψ) (x i) z)) :=
              (tendsto_const_nhds.sub (hlim (x i) z (hGt i hz)))
            exact ((ENNReal.continuous_ofReal.tendsto _).comp (h1.norm)).liminf_eq
        _ ≤ Filter.liminf (fun m => ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖(φ n - φ m) (x i) z‖) atTop :=
            lintegral_liminf_le' (u := atTop) fun m => hmeas _ (hdh n m) i
    have hB : ∑' i, Filter.liminf (fun m => f m i) atTop ≤ Filter.liminf (fun m => ∑' i, f m i) atTop := by
      have := lintegral_liminf_le' (μ := (Measure.count : Measure ℕ)) (u := atTop) (f := fun m i => f m i)
        (fun m => (measurable_from_top).aemeasurable)
      simpa [lintegral_count] using this
    rw [hsum _ (hdψ n)]
    refine (ENNReal.tsum_le_tsum hA).trans (hB.trans ?_)
    refine le_of_eq ?_
    congr 1
    funext m
    exact (hsum _ (hdh n m)).symm
  -- the rate
  have hrate : Tendsto (fun n => quadDiffNorm (φ n - ψ)) atTop (𝓝 0) := by
    refine tendsto_order.2 ⟨fun a ha => absurd ha (by simp), fun a ha => ?_⟩
    obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 ha
    obtain ⟨N, hN⟩ := hC r (ENNReal.ofReal_pos.1 hr1)
    filter_upwards [eventually_ge_atTop N] with n hn
    refine lt_of_le_of_lt ((hfatou n).trans ?_) hr2
    exact Filter.liminf_le_of_frequently_le'
      ((eventually_ge_atTop N).mono fun m hm => (hN n hn m hm).le).frequently
  -- `ψ` has finite norm
  have hfin : quadDiffNorm ψ < ⊤ := by
    have hlawH : ∀ f : R → ℂ → ℂ, f ∈ holQuadDiffSubmodule R → IsDiffFamilyAE 2 0 f := by
      intro f hf a b
      have hset : MeasurableSet ((chartAt ℂ b).target ∩ (chartAt ℂ b).symm ⁻¹' (chartAt ℂ a).source) :=
        ((chartAt ℂ b).isOpen_inter_preimage_symm (chartAt ℂ a).open_source).measurableSet
      filter_upwards [ae_restrict_mem hset] with z hz
      exact hf.1.2 a b z hz.1 hz.2
    have hmH : ∀ f : R → ℂ → ℂ, f ∈ holQuadDiffSubmodule R → ∀ a : R,
        AEStronglyMeasurable (f a) (volume.restrict (chartAt ℂ a).target) := fun f hf a =>
      ((hf.2 a).continuousOn).aestronglyMeasurable (chartAt ℂ a).open_target.measurableSet
    obtain ⟨n, hn⟩ := (hrate.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 from one_pos))).exists
    have hd0 : ψ - φ n ∈ holQuadDiffSubmodule R := (holQuadDiffSubmodule R).sub_mem hψhol (hφh n)
    have h := gl31_qdn_add_le (hlawH _ (hφh n)) (hlawH _ hd0) (hmH _ (hφh n)) (hmH _ hd0)
    rw [add_sub_cancel] at h
    have hsw : quadDiffNorm (ψ - φ n) = quadDiffNorm (φ n - ψ) := by
      rw [hsum _ hd0, hsum _ (hdψ n)]
      simp only [Pi.sub_apply, norm_sub_rev]
    refine lt_of_le_of_lt h (ENNReal.add_lt_top.2 ⟨(hφ n).2, ?_⟩)
    rw [hsw]
    exact lt_trans hn ENNReal.one_lt_top
  refine ⟨ψ, ⟨hψhol, hfin⟩, hrate⟩

/-- **Theorem 1** (§3.1, l. 2081). `A(R)` is a closed subspace of `L₁(R)`: an `L₁`-limit of elements of `A(R)` agrees
(in norm) with an element of `A(R)`.
[CORRECTION/modelling] The binder `[IsManifold 𝓘(ℂ) ω R]` (the holomorphic atlas of `R`) is added: the proof needs the
chart transitions to be holomorphic, and the printed statement assumes `R` is a Riemann surface. -/
theorem thm3_1 [IsManifold 𝓘(ℂ) ω R] {φ : ℕ → R → ℂ → ℂ} (hφ : ∀ n, φ n ∈ integrableHolQDSet R)
    {ψ : R → ℂ → ℂ}
    (hψ : ψ ∈ integrableQDSet R) (hlim : Tendsto (fun n => quadDiffNorm (φ n - ψ)) atTop (𝓝 0)) :
    ∃ φ₀ ∈ integrableHolQDSet R, quadDiffNorm (φ₀ - ψ) = 0 := by
  classical
  have hψlaw : IsDiffFamilyAE 2 0 ψ := hψ.1
  have hψm : ∀ x : R, AEStronglyMeasurable (ψ x) (volume.restrict (chartAt ℂ x).target) := hψ.2.1
  -- holomorphic differentials satisfy the a.e. law and have measurable coefficients
  have hlawH : ∀ f : R → ℂ → ℂ, f ∈ holQuadDiffSubmodule R → IsDiffFamilyAE 2 0 f := by
    intro f hf x y
    have hset : MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) :=
      ((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source).measurableSet
    filter_upwards [ae_restrict_mem hset] with z hz
    exact hf.1.2 x y z hz.1 hz.2
  have hmH : ∀ f : R → ℂ → ℂ, f ∈ holQuadDiffSubmodule R → ∀ x : R,
      AEStronglyMeasurable (f x) (volume.restrict (chartAt ℂ x).target) := fun f hf x =>
    ((hf.2 x).continuousOn).aestronglyMeasurable (chartAt ℂ x).open_target.measurableSet
  have hsubAE : ∀ f g : R → ℂ → ℂ, IsDiffFamilyAE 2 0 f → IsDiffFamilyAE 2 0 g → IsDiffFamilyAE 2 0 (f - g) := by
    intro f g hf hg x y
    filter_upwards [hf x y, hg x y] with z h1 h2
    simp only [Pi.sub_apply]
    rw [h1, h2]
    ring
  have hnegAE : ∀ f : R → ℂ → ℂ, IsDiffFamilyAE 2 0 f → IsDiffFamilyAE 2 0 (-f) := by
    intro f hf x y
    filter_upwards [hf x y] with z h1
    simp only [Pi.neg_apply]
    rw [h1]
    ring
  have hneg : ∀ f : R → ℂ → ℂ, IsDiffFamilyAE 2 0 f → quadDiffNorm (-f) = quadDiffNorm f := by
    intro f hf
    by_cases h : ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P
    · obtain ⟨x, P, hP⟩ := h
      rw [gl31_surfaceIntegral_eq_tsum_ae (hnegAE f hf) hP, gl31_surfaceIntegral_eq_tsum_ae hf hP]
      simp only [Pi.neg_apply, norm_neg]
    · have h1 : quadDiffNorm (-f) = ⊤ := by
        by_contra h'
        exact h (gl31_exists_partition_of_ne_top h')
      have h2 : quadDiffNorm f = ⊤ := by
        by_contra h'
        exact h (gl31_exists_partition_of_ne_top h')
      rw [h1, h2]
  -- triangle inequality for the differences
  have htri : ∀ m n, quadDiffNorm (φ m - φ n) ≤ quadDiffNorm (φ m - ψ) + quadDiffNorm (φ n - ψ) := by
    intro m n
    have hm1 := hsubAE _ _ (hlawH _ (hφ m).1) hψlaw
    have hm2 := hsubAE _ _ hψlaw (hlawH _ (hφ n).1)
    have h := gl31_qdn_add_le hm1 hm2 (fun x => (hmH _ (hφ m).1 x).sub (hψm x))
      (fun x => (hψm x).sub (hmH _ (hφ n).1 x))
    rw [sub_add_sub_cancel] at h
    rw [← neg_sub (φ n) ψ, hneg _ (hsubAE _ _ (hlawH _ (hφ n).1) hψlaw)] at h
    exact h
  -- `φₙ` is Cauchy
  have hC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, quadDiffNorm (φ m - φ n) < ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hlim).2 _ (ENNReal.ofReal_pos.2 (half_pos hε)))
    refine ⟨N, fun m hm n hn => ?_⟩
    calc quadDiffNorm (φ m - φ n) ≤ quadDiffNorm (φ m - ψ) + quadDiffNorm (φ n - ψ) := htri m n
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add (hN m hm) (hN n hn)
      _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; ring_nf
  obtain ⟨φ₀, hφ₀, hl0⟩ := gl31_complete hφ hC
  refine ⟨φ₀, hφ₀, ?_⟩
  -- `‖φ₀ − ψ‖ ≤ ‖φₙ − φ₀‖ + ‖φₙ − ψ‖ → 0`
  have hle : ∀ n, quadDiffNorm (φ₀ - ψ) ≤ quadDiffNorm (φ n - φ₀) + quadDiffNorm (φ n - ψ) := by
    intro n
    have hm1 := hsubAE _ _ (hlawH _ hφ₀.1) (hlawH _ (hφ n).1)
    have hm2 := hsubAE _ _ (hlawH _ (hφ n).1) hψlaw
    have h := gl31_qdn_add_le hm1 hm2 (fun x => (hmH _ hφ₀.1 x).sub (hmH _ (hφ n).1 x))
      (fun x => (hmH _ (hφ n).1 x).sub (hψm x))
    rw [sub_add_sub_cancel] at h
    rw [← neg_sub (φ n) φ₀, hneg _ (hsubAE _ _ (hlawH _ (hφ n).1) (hlawH _ hφ₀.1))] at h
    exact h
  have := ge_of_tendsto' (hl0.add hlim) hle
  rw [add_zero] at this
  exact le_antisymm this bot_le

end Surface

/-- Helper for **Theorem 2** (§3.1, l. 2099) and for `Z(·)`. `V` is a bounded complex-linear functional on the set
`A` (with the norm `nrm`): additive and homogeneous on `A`, and `|V a| ≤ C ‖a‖`. -/
def IsBoundedFunctionalOn {X : Type*} [Add X] [SMul ℂ X] (A : Set X) (nrm : X → ℝ≥0∞) (V : X → ℂ) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, V (a + b) = V a + V b) ∧ (∀ c : ℂ, ∀ a ∈ A, V (c • a) = c * V a) ∧
    ∃ C : ℝ, ∀ a ∈ A, ‖V a‖ ≤ C * (nrm a).toReal

/-- Helper (l. 2142). The dual norm `‖V‖ = sup_{‖a‖ = 1} |V(a)|` of a functional on `A`. -/
def dualNormOn {X : Type*} (A : Set X) (nrm : X → ℝ≥0∞) (V : X → ℂ) : ℝ :=
  ⨆ (a : X) (_ : a ∈ A ∧ nrm a = 1), ‖V a‖

/-- Helper for `gl3_dual_repr` and `gl3_dual_le`: the dual norm bounds a bounded functional, `|V φ| ≤ ‖V‖ ∬_S |φ|`
for `φ ∈ A` of finite area (normalize `φ` to area `1`; area `0` gives `V φ = 0` by boundedness). -/
theorem gl3_dual_bound {S : Set ℂ} {A : Set (ℂ → ℂ)} (hsmul : ∀ c : ℂ, ∀ φ ∈ A, c • φ ∈ A)
    {V : (ℂ → ℂ) → ℂ} (hV : IsBoundedFunctionalOn A (fun φ => phiArea φ S) V) {φ : ℂ → ℂ} (hφ : φ ∈ A)
    (hfin : phiArea φ S ≠ ⊤) :
    ‖V φ‖ ≤ dualNormOn A (fun φ => phiArea φ S) V * (phiArea φ S).toReal := by
  obtain ⟨-, hVs, C, hC⟩ := hV
  have hle : ∀ ψ : ℂ → ℂ, ψ ∈ A ∧ phiArea ψ S = 1 → ‖V ψ‖ ≤ dualNormOn A (fun φ => phiArea φ S) V := by
    intro ψ hψ
    have hbdd : BddAbove (range fun ψ : ℂ → ℂ => ⨆ (_ : ψ ∈ A ∧ phiArea ψ S = 1), ‖V ψ‖) := by
      refine ⟨max C 0, ?_⟩
      rintro _ ⟨χ, rfl⟩
      refine Real.iSup_le (fun hχ => ?_) (le_max_right _ _)
      have := hC χ hχ.1
      simp only at this
      rw [hχ.2, ENNReal.toReal_one, mul_one] at this
      exact this.trans (le_max_left _ _)
    calc ‖V ψ‖ = ⨆ (_ : ψ ∈ A ∧ phiArea ψ S = 1), ‖V ψ‖ := (ciSup_pos (f := fun _ => ‖V ψ‖) hψ).symm
      _ ≤ _ := le_ciSup hbdd ψ
  set t := (phiArea φ S).toReal with ht
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  rcases ht0.lt_or_eq with htpos | ht0'
  · -- `φ / t` has area `1`
    have hψA : ((t : ℂ)⁻¹ • φ) ∈ A := hsmul _ φ hφ
    have harea : phiArea ((t : ℂ)⁻¹ • φ) S = 1 := by
      have e : phiArea ((t : ℂ)⁻¹ • φ) S = ENNReal.ofReal t⁻¹ * phiArea φ S := by
        unfold phiArea
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun z => ?_
        rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht0,
          ENNReal.ofReal_mul (inv_nonneg.2 ht0)]
      rw [e, ← ENNReal.ofReal_toReal hfin, ← ht, ← ENNReal.ofReal_mul (inv_nonneg.2 ht0),
        inv_mul_cancel₀ htpos.ne', ENNReal.ofReal_one]
    have h1 := hle _ ⟨hψA, harea⟩
    rw [hVs _ φ hφ, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht0,
      inv_mul_le_iff₀ htpos] at h1
    linarith
  · -- area `0`: `|V φ| ≤ C · 0`
    have h := hC φ hφ
    rw [← ht, ← ht0', mul_zero] at h
    rw [← ht0', mul_zero]
    exact h

/-- Helper for `para3_1_dual_gamma`, `para3_4_z_quotient` (§3.1, §3.4) and Ch. 6 `cor6_5_2_c`, the Hahn–Banach `L∞`
representation. A bounded functional `V` on a set `A` of functions integrable on the measurable set `S`, closed under
the linear operations, with the norm `∬_S |·|`, is `φ ↦ ∬_S νφ` for some `ν` with `|ν| ≤ ‖V‖` a.e. on `S`
(Hahn–Banach on `L¹(S)`, and `L¹* = L∞` through the finite measure `(1 + |z|)⁻³ dx dy` on `S`, as in the proof of
`LiZhongQC.h36p_duality_F`). -/
theorem gl3_dual_repr {S : Set ℂ} (hS : MeasurableSet S) {A : Set (ℂ → ℂ)} (hA : ∀ φ ∈ A, IntegrableOn φ S)
    (h0 : (0 : ℂ → ℂ) ∈ A) (hadd : ∀ φ ∈ A, ∀ ψ ∈ A, φ + ψ ∈ A) (hsmul : ∀ c : ℂ, ∀ φ ∈ A, c • φ ∈ A)
    {V : (ℂ → ℂ) → ℂ} (hV : IsBoundedFunctionalOn A (fun φ => phiArea φ S) V) :
    ∃ ν : ℂ → ℂ, AEStronglyMeasurable ν (volume.restrict S) ∧
      (∀ᵐ z ∂(volume.restrict S), ‖ν z‖ ≤ dualNormOn A (fun φ => phiArea φ S) V) ∧
      ∀ φ ∈ A, V φ = ∫ z in S, ν z * φ z := by
  -- `S` need not be measurable: restriction to any set is a measure
  have _hS := hS
  set D := dualNormOn A (fun φ => phiArea φ S) V with hDdef
  have hD0 : 0 ≤ D := Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hVadd := hV.1
  have hVsmul := hV.2.1
  -- the finite measure `P = ρ · volume|_S`, `ρ = (1 + |z|)⁻³`
  set ρ : ℂ → ℝ := fun z => ((1 + ‖z‖) ^ 3)⁻¹ with hρdef
  have hρpos : ∀ z, 0 < ρ z := fun z => by simp only [hρdef]; positivity
  have hρm : Measurable ρ := by simp only [hρdef]; fun_prop
  set P : Measure ℂ := (volume.restrict S).withDensity (fun z => ENNReal.ofReal (ρ z)) with hPdef
  have hfin : IsFiniteMeasure P :=
    isFiniteMeasure_withDensity_ofReal (LiZhongQC.b36_p_profile_integrable.integrableOn (s := S)).2
  have hSP : volume.restrict S ≪ P := withDensity_absolutelyContinuous' hρm.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun z => (ENNReal.ofReal_pos.2 (hρpos z)).ne')
  have hPint : ∀ g : ℂ → ℂ, ∫ z, g z ∂P = ∫ z in S, (ρ z : ℂ) * g z := by
    intro g
    rw [hPdef, integral_withDensity_eq_integral_toReal_smul hρm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [ENNReal.toReal_ofReal (hρpos z).le, Complex.real_smul]
  have hPintR : ∀ g : ℂ → ℝ, ∫ z, g z ∂P = ∫ z in S, ρ z * g z := by
    intro g
    rw [hPdef, integral_withDensity_eq_integral_toReal_smul hρm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [ENNReal.toReal_ofReal (hρpos z).le, smul_eq_mul]
  have hPi : ∀ g : ℂ → ℂ, Integrable g P ↔ Integrable (fun z => (ρ z : ℂ) * g z) (volume.restrict S) := by
    intro g
    rw [hPdef, integrable_withDensity_iff_integrable_smul' hρm.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    refine integrable_congr (ae_of_all _ fun z => ?_)
    simp only [ENNReal.toReal_ofReal (hρpos z).le, Complex.real_smul]
  have hdiv : ∀ φ : ℂ → ℂ, ∀ z, (ρ z : ℂ) * (φ z / ρ z) = φ z := fun φ z => by
    have : (ρ z : ℂ) ≠ 0 := by exact_mod_cast (hρpos z).ne'
    field_simp
  have hnorm : ∀ φ : ℂ → ℂ, ∀ z, ρ z * ‖φ z / ρ z‖ = ‖φ z‖ := fun φ z => by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hρpos z).le]
    field_simp [(hρpos z).ne']
  have hAi : ∀ φ ∈ A, Integrable (fun z => φ z / ρ z) P := by
    intro φ hφ
    rw [hPi]
    exact (hA φ hφ).congr (ae_of_all _ fun z => (hdiv φ z).symm)
  -- `A` as a submodule, its image `W` in `L¹(P)` and the functional `[φ/ρ] ↦ V φ` on `W`
  let Asub : Submodule ℂ (ℂ → ℂ) :=
    { carrier := A
      add_mem' := fun {φ ψ} hφ hψ => hadd φ hφ ψ hψ
      zero_mem' := h0
      smul_mem' := fun c φ hφ => hsmul c φ hφ }
  let T : Asub →ₗ[ℂ] Lp ℂ 1 P :=
    { toFun := fun φ => (hAi φ.1 φ.2).toL1 (fun z => φ.1 z / ρ z)
      map_add' := fun φ ψ => by
        rw [← Integrable.toL1_add]
        exact (Integrable.toL1_eq_toL1_iff _ _ _ _).2 (ae_of_all _ fun z => by simp [add_div])
      map_smul' := fun c φ => by
        rw [RingHom.id_apply, ← Integrable.toL1_smul']
        exact (Integrable.toL1_eq_toL1_iff _ _ _ _).2 (ae_of_all _ fun z => by simp [mul_div_assoc]) }
  let Vl : Asub →ₗ[ℂ] ℂ :=
    { toFun := fun φ => V φ.1
      map_add' := fun φ ψ => hVadd φ.1 φ.2 ψ.1 ψ.2
      map_smul' := fun c φ => hVsmul c φ.1 φ.2 }
  -- `V` factors through `T`: `T φ = 0` forces `∬_S |φ| = 0`, hence `V φ = 0`
  have hareaT : ∀ φ : Asub, phiArea φ.1 S = ENNReal.ofReal ‖T φ‖ := by
    intro φ
    have e : ‖T φ‖ = ∫ z, ‖φ.1 z / ρ z‖ ∂P := by
      rw [L1.norm_eq_integral_norm]
      exact integral_congr_ae (by
        filter_upwards [(hAi φ.1 φ.2).coeFn_toL1] with z hz
        exact congrArg norm hz)
    rw [e, hPintR, integral_congr_ae (ae_of_all _ fun z => hnorm φ.1 z),
      ofReal_integral_eq_lintegral_ofReal (hA φ.1 φ.2).norm (ae_of_all _ fun _ => norm_nonneg _)]
    rfl
  have hVT : ∀ φ : Asub, ‖Vl φ‖ ≤ D * ‖T φ‖ := by
    intro φ
    have h := gl3_dual_bound hsmul hV φ.2 (by rw [hareaT φ]; exact ENNReal.ofReal_ne_top)
    rwa [hareaT φ, ENNReal.toReal_ofReal (norm_nonneg _)] at h
  have hker : LinearMap.ker T ≤ LinearMap.ker Vl := fun φ hφ => by
    rw [LinearMap.mem_ker] at hφ ⊢
    have h := hVT φ
    rw [hφ, norm_zero, mul_zero] at h
    exact norm_le_zero_iff.1 h
  -- the functional on `W = range T`, bounded by `D`
  let ℓ₀ : LinearMap.range T →ₗ[ℂ] ℂ :=
    (LinearMap.ker T).liftQ Vl hker ∘ₗ (LinearMap.quotKerEquivRange T).symm.toLinearMap
  have hℓ₀ : ∀ φ : Asub, ℓ₀ ⟨T φ, LinearMap.mem_range_self T φ⟩ = Vl φ := by
    intro φ
    simp only [ℓ₀, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [show (⟨T φ, LinearMap.mem_range_self T φ⟩ : LinearMap.range T) = LinearMap.quotKerEquivRange T
      (Submodule.Quotient.mk φ) from rfl, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  have hℓ₀b : ∀ G : LinearMap.range T, ‖ℓ₀ G‖ ≤ D * ‖G‖ := by
    rintro ⟨G, φ, rfl⟩
    rw [hℓ₀ φ]
    exact hVT φ
  let ℓ : StrongDual ℂ (LinearMap.range T) := ℓ₀.mkContinuous D hℓ₀b
  -- Hahn–Banach, then `L¹(P)* = L∞(P)`
  obtain ⟨L, hLext, hLnorm⟩ := exists_extension_norm_eq (LinearMap.range T) ℓ
  obtain ⟨ν, hνm, hνb, hνrep⟩ := LiZhongQC.h35a_L1_dual_repr L
  have hLD : ‖L‖ ≤ D := hLnorm ▸ LinearMap.mkContinuous_norm_le _ hD0 hℓ₀b
  refine ⟨ν, hνm.mono_ac hSP, hSP.ae_le ?_, fun φ hφ => ?_⟩
  · filter_upwards [hνb] with z hz
    exact hz.trans hLD
  · have h1 := hLext ⟨T ⟨φ, hφ⟩, LinearMap.mem_range_self T _⟩
    have h2 : ℓ ⟨T ⟨φ, hφ⟩, LinearMap.mem_range_self T _⟩ = V φ := hℓ₀ ⟨φ, hφ⟩
    rw [h2] at h1
    rw [← h1]
    show L ((hAi φ hφ).toL1 (fun z => φ z / ρ z)) = _
    rw [hνrep _ (hAi φ hφ), hPint]
    exact integral_congr_ae (ae_of_all _ fun z => by dsimp only; rw [mul_left_comm, hdiv])

/-- Helper for `para3_1_dual_gamma`, `para3_4_z_quotient` and Ch. 6 `cor6_5_2_c`: a representing function is at least
as large as the functional, `‖V‖ ≤ ‖ν‖_{L∞(T)}` whenever `V = ∬_S ν ·` on `A` and `S ⊆ T`
(`|∬_S νφ| ≤ ‖ν‖∞ ∬_S |φ|`). -/
theorem gl3_dual_le {S T : Set ℂ} (hST : S ⊆ T) {A : Set (ℂ → ℂ)} {V : (ℂ → ℂ) → ℂ} {ν : ℂ → ℂ}
    (hrep : ∀ φ ∈ A, V φ = ∫ z in S, ν z * φ z) :
    ENNReal.ofReal (dualNormOn A (fun φ => phiArea φ S) V) ≤ eLpNorm ν ⊤ (volume.restrict T) := by
  by_cases htop : eLpNorm ν ⊤ (volume.restrict T) = ⊤
  · rw [htop]
    exact le_top
  set M := (eLpNorm ν ⊤ (volume.restrict T)).toReal with hMdef
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  -- `|ν| ≤ M` a.e. on `T`, hence on `S`
  have hbT : ∀ᵐ z ∂(volume.restrict T), ‖ν z‖ₑ ≤ ENNReal.ofReal M := by
    filter_upwards [ae_le_eLpNormEssSup (μ := volume.restrict T) (f := ν)] with z hz
    rw [hMdef, ENNReal.ofReal_toReal htop, eLpNorm_exponent_top (aestronglyMeasurable_of_eLpNorm_ne_top htop)]
    exact hz
  have hbS : ∀ᵐ z ∂(volume.restrict S), ‖ν z‖ₑ ≤ ENNReal.ofReal M := ae_restrict_of_ae_restrict_of_subset hST hbT
  rw [← ENNReal.ofReal_toReal htop, ← hMdef]
  refine ENNReal.ofReal_le_ofReal (Real.iSup_le (fun φ => Real.iSup_le (fun hφ => ?_) hM0) hM0)
  -- `|V φ| = |∬_S νφ| ≤ M ∬_S |φ| = M` for `φ` of area `1`
  rw [hrep φ hφ.1, ← ENNReal.ofReal_le_ofReal_iff hM0, ofReal_norm]
  calc ‖∫ z in S, ν z * φ z‖ₑ ≤ ∫⁻ z in S, ‖ν z * φ z‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ z in S, ENNReal.ofReal M * ENNReal.ofReal ‖φ z‖ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hbS] with z hz
        rw [enorm_mul, ofReal_norm]
        exact mul_le_mul' hz le_rfl
    _ = ENNReal.ofReal M * phiArea φ S := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal M := by rw [show phiArea φ S = 1 from hφ.2, mul_one]

section Surface

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition** (§3.1, l. 2139). `Z(R)`: the bounded complex-linear functionals on `A(R)` (dual norm
`dualNormOn (integrableHolQDSet R) quadDiffNorm`). -/
def zSpace (R : Type u) [TopologicalSpace R] [ChartedSpace ℂ R] : Set ((R → ℂ → ℂ) → ℂ) :=
  {V | IsBoundedFunctionalOn (integrableHolQDSet R) quadDiffNorm V}

/-- Helper for **Theorem 2** (§3.1, l. 2099), as in the proof of `gl31_beltrami_extend`. For a chart partition `(x, P)`,
a chart `y` and a piece `Pᵢ`: the set `φ_y(U_y ∩ Pᵢ)` is measurable, the transition `T = φ_{xᵢ} ∘ φ_y⁻¹` is measurable
on it, and `T` pulls null sets of `φ_{xᵢ}(Pᵢ)` back to null sets (the inverse transition is differentiable, so it maps
null sets to null sets). -/
theorem gl31_transition_ac [IsManifold 𝓘(ℂ) ω R] {x : ℕ → R} {P : ℕ → Set R} (hP : IsChartPartition R x P) (y : R)
    (i : ℕ) :
    MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i) ∧
      AEMeasurable (LiZhongQC.chartTransition (x i) y)
        (volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i)) ∧
      (volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i)).map
        (LiZhongQC.chartTransition (x i) y) ≪ volume.restrict (chartAt ℂ (x i) '' P i) := by
  classical
  set A := LiZhongQC.chartTransition (x i) y with hAdef
  set W := (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ (x i)).source with hWdef
  have hWo : IsOpen W := (chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ (x i)).open_source
  have hAc : ContinuousOn A W := fun w hw =>
    (LiZhongQC.s23_transition_differentiableAt (x i) y hw.1 hw.2).continuousAt.continuousWithinAt
  have hpre : ∀ M : Set ℂ, MeasurableSet M → MeasurableSet (W ∩ A ⁻¹' M) := by
    intro M hM
    have hpw := hAc.measurable_piecewise (continuousOn_const (c := (0 : ℂ))) hWo.measurableSet
    have heq : W ∩ A ⁻¹' M = W ∩ (W.piecewise A (fun _ => (0 : ℂ))) ⁻¹' M := by
      ext w
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨hwW, hw⟩
        exact ⟨hwW, by rwa [piecewise_eq_of_mem _ _ _ hwW]⟩
      · rintro ⟨hwW, hw⟩
        exact ⟨hwW, by rwa [piecewise_eq_of_mem _ _ _ hwW] at hw⟩
    rw [heq]
    exact hWo.measurableSet.inter (hpw hM)
  have hOeq : (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i = W ∩ A ⁻¹' (chartAt ℂ (x i) '' P i) := by
    ext w
    constructor
    · rintro ⟨hwt, hwP⟩
      exact ⟨⟨hwt, (hP.1 i).1 hwP⟩, ⟨_, hwP, rfl⟩⟩
    · rintro ⟨⟨hwt, hws⟩, q, hq, hqe⟩
      exact ⟨hwt, mem_preimage.2 ((chartAt ℂ (x i)).injOn ((hP.1 i).1 hq) hws hqe ▸ hq)⟩
  have hOm : MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i) := by
    rw [hOeq]
    exact hpre _ (hP.1 i).2
  have hOW : (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i ⊆ W := fun w hw => ⟨hw.1, (hP.1 i).1 hw.2⟩
  have hAm : AEMeasurable A (volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i)) :=
    (hAc.mono hOW).aemeasurable hOm
  -- `A` pulls null subsets of `φ_{xᵢ}(Pᵢ)` back to null sets
  have hac : (volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i)).map A ≪
      volume.restrict (chartAt ℂ (x i) '' P i) := by
    refine Measure.AbsolutelyContinuous.mk fun N hNm hN0 => ?_
    rw [Measure.map_apply_of_aemeasurable hAm hNm, Measure.restrict_apply' hOm]
    rw [Measure.restrict_apply hNm] at hN0
    refine measure_mono_null (t := LiZhongQC.chartTransition y (x i) ''
      (N ∩ chartAt ℂ (x i) '' P i ∩ ((chartAt ℂ (x i)).target ∩ (chartAt ℂ (x i)).symm ⁻¹' (chartAt ℂ y).source)))
      ?_ ?_
    · rintro w ⟨hwN, hwO⟩
      have hm := LiZhongQC.s23_transition_mem hwO.1 ((hP.1 i).1 hwO.2)
      refine ⟨A w, ⟨⟨hwN, _, hwO.2, rfl⟩, hm.1, hm.2.1⟩, ?_⟩
      show chartAt ℂ y ((chartAt ℂ (x i)).symm (A w)) = w
      rw [hm.2.2, (chartAt ℂ y).right_inv hwO.1]
    · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume (fun v hv => ?_)
        (measure_mono_null (fun v hv => hv.1) hN0)
      exact ((LiZhongQC.s23_transition_differentiableAt y (x i) hv.2.1 hv.2.2).restrictScalars
        ℝ).differentiableWithinAt
  exact ⟨hOm, hAm, hac⟩

/-- Helper for **Theorem 2** (§3.1, l. 2099), the integrable analogue of `gl31_beltrami_extend`. Chart functions `f i`
on the pieces `φ_{xᵢ}(Pᵢ)` of a chart partition, a.e.-strongly measurable with `Σᵢ ∬ |f i| < ⊤`, extend to an integrable
quadratic differential `ψ ∈ L₁(R)` with `ψ_{xᵢ} = f i` on `φ_{xᵢ}(Pᵢ)`: `ψ_y(w) = f_i(T w) (T′ w)²` where
`φ_y⁻¹(w) ∈ Pᵢ` and `T = φ_{xᵢ} ∘ φ_y⁻¹` (the transformation law holds everywhere on the overlaps by the chain rule,
and `T` pulls null sets back to null sets, as in `gl31_beltrami_extend`; the norm is at most the partition sum by
`iInf_le`). -/
theorem gl31_qd_extend [IsManifold 𝓘(ℂ) ω R] {x : ℕ → R} {P : ℕ → Set R} (hP : IsChartPartition R x P)
    (f : ℕ → ℂ → ℂ)
    (hfm : ∀ i, AEStronglyMeasurable (f i) (volume.restrict (chartAt ℂ (x i) '' P i)))
    (hfin : ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖f i z‖ₑ < ⊤) :
    ∃ ψ ∈ integrableQDSet R, ∀ i, ∀ z ∈ chartAt ℂ (x i) '' P i, ψ (x i) z = f i z := by
  classical
  -- the piece of the partition containing a point
  have hcov : ∀ y : R, ∃ i, y ∈ P i := fun y => mem_iUnion.1 (by rw [hP.2.2]; exact mem_univ y)
  choose idx hidx using hcov
  have hidx' : ∀ y i, y ∈ P i → idx y = i := fun y i hy => by
    by_contra hne
    exact Set.disjoint_left.1 (hP.2.1 hne) (hidx y) hy
  -- `ψ_y(w) = f_i(T w) (T′ w)²`, `T = φ_{xᵢ} ∘ φ_y⁻¹`, `i` the piece of `φ_y⁻¹(w)`
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : R → ℂ → ℂ, ψ = fun y w =>
      f (idx ((chartAt ℂ y).symm w)) (LiZhongQC.chartTransition (x (idx ((chartAt ℂ y).symm w))) y w) *
        deriv (LiZhongQC.chartTransition (x (idx ((chartAt ℂ y).symm w))) y) w ^ 2 := ⟨_, rfl⟩
  have hψ : ∀ y w i, (chartAt ℂ y).symm w ∈ P i → ψ y w = f i (LiZhongQC.chartTransition (x i) y w) *
      deriv (LiZhongQC.chartTransition (x i) y) w ^ 2 := by
    intro y w i hw
    simp only [hψdef]
    rw [hidx' _ i hw]
  -- on its own chart target the transition `φ_{xᵢ} ∘ φ_{xᵢ}⁻¹` is the identity
  have hself : ∀ i, ∀ z ∈ (chartAt ℂ (x i)).target, LiZhongQC.chartTransition (x i) (x i) z = z ∧
      deriv (LiZhongQC.chartTransition (x i) (x i)) z = 1 := by
    intro i z hz
    have hev : LiZhongQC.chartTransition (x i) (x i) =ᶠ[𝓝 z] id := by
      filter_upwards [(chartAt ℂ (x i)).open_target.mem_nhds hz] with w hw
      exact (chartAt ℂ (x i)).right_inv hw
    exact ⟨hev.eq_of_nhds, by rw [hev.deriv_eq, deriv_id]⟩
  have hval : ∀ i, ∀ z ∈ chartAt ℂ (x i) '' P i, ψ (x i) z = f i z := by
    rintro i _ ⟨q, hq, rfl⟩
    have hqs := (hP.1 i).1 hq
    have hzt := (chartAt ℂ (x i)).map_source hqs
    rw [hψ (x i) _ i (by rw [(chartAt ℂ (x i)).left_inv hqs]; exact hq), (hself i _ hzt).1, (hself i _ hzt).2]
    simp
  -- the transformation law holds everywhere on the overlaps (chain rule)
  have hlaw : ∀ x' y : R, ∀ z ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x').source,
      ψ y z = ψ x' (LiZhongQC.chartTransition x' y z) * deriv (LiZhongQC.chartTransition x' y) z ^ (2 : ℤ) *
        conj (deriv (LiZhongQC.chartTransition x' y) z) ^ (0 : ℤ) := by
    rintro x' y z ⟨hz, hzx⟩
    have hmem := LiZhongQC.s23_transition_mem hz hzx
    have hpi : (chartAt ℂ y).symm z ∈ P (idx ((chartAt ℂ y).symm z)) := hidx _
    have hpis := (hP.1 _).1 hpi
    have hev : LiZhongQC.chartTransition (x (idx ((chartAt ℂ y).symm z))) y =ᶠ[𝓝 z]
        LiZhongQC.chartTransition (x (idx ((chartAt ℂ y).symm z))) x' ∘ LiZhongQC.chartTransition x' y := by
      filter_upwards [((chartAt ℂ y).continuousAt_symm hz).preimage_mem_nhds
        ((chartAt ℂ x').open_source.mem_nhds hzx)] with w hwx
      show chartAt ℂ (x (idx ((chartAt ℂ y).symm z))) ((chartAt ℂ y).symm w) =
        chartAt ℂ (x (idx ((chartAt ℂ y).symm z))) ((chartAt ℂ x').symm (chartAt ℂ x' ((chartAt ℂ y).symm w)))
      rw [(chartAt ℂ x').left_inv hwx]
    have hd1 := LiZhongQC.s23_transition_differentiableAt (x (idx ((chartAt ℂ y).symm z))) x' hmem.1
      (by rw [hmem.2.2]; exact hpis)
    have hd2 := LiZhongQC.s23_transition_differentiableAt x' y hz hzx
    have hderiv : deriv (LiZhongQC.chartTransition (x (idx ((chartAt ℂ y).symm z))) y) z =
        deriv (LiZhongQC.chartTransition (x (idx ((chartAt ℂ y).symm z))) x') (LiZhongQC.chartTransition x' y z) *
          deriv (LiZhongQC.chartTransition x' y) z := by
      rw [hev.deriv_eq, deriv_comp z hd1 hd2]
    rw [hψ y z _ hpi, hψ x' _ (idx ((chartAt ℂ y).symm z)) (by rw [hmem.2.2]; exact hpi), hev.eq_of_nhds,
      hderiv]
    simp only [Function.comp_apply, zpow_ofNat, zpow_zero, mul_one]
    ring
  have hlawAE : IsDiffFamilyAE 2 0 ψ := by
    intro x' y
    have hm : MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x').source) :=
      ((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x').open_source).measurableSet
    exact (ae_restrict_iff' hm).2 (Eventually.of_forall (hlaw x' y))
  -- measurability in every chart, piece by piece
  have hcoef : ∀ y : R, AEStronglyMeasurable (ψ y) (volume.restrict (chartAt ℂ y).target) := by
    intro y
    have hOU : (chartAt ℂ y).target = ⋃ i, (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i := by
      rw [← inter_iUnion, ← preimage_iUnion, hP.2.2, preimage_univ, inter_univ]
    have key : ∀ i, AEStronglyMeasurable (ψ y)
        (volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i)) := by
      intro i
      obtain ⟨hOm, hAm, hac⟩ := gl31_transition_ac hP y i
      set A := LiZhongQC.chartTransition (x i) y with hAdef
      have hu : Measurable fun w => deriv A w ^ 2 := (measurable_deriv A).pow_const 2
      have hfA : AEStronglyMeasurable (fun w => f i (A w))
          (volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i)) :=
        ((hfm i).mono_ac hac).comp_aemeasurable hAm
      exact (hfA.mul hu.aestronglyMeasurable).congr
        ((ae_restrict_iff' hOm).2 (Eventually.of_forall fun w hw => (hψ y w i hw.2).symm))
    rw [hOU]
    exact aestronglyMeasurable_iUnion_iff.2 fun i => key i
  refine ⟨ψ, ⟨hlawAE, hcoef, ?_⟩, hval⟩
  rw [gl31_surfaceIntegral_eq_tsum_ae hlawAE hP]
  calc ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖ψ (x i) z‖
      = ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖f i z‖ₑ :=
        tsum_congr fun i => setLIntegral_congr_fun (hP.1 i).2 fun z hz => by rw [hval i z hz, ofReal_norm]
    _ < ⊤ := hfin

/-- Helper for **Theorem 2** (§3.1, l. 2099). The `L¹` model of `L₁(R)` on a chart partition `(x, P)`: the cell picture
of `gl31_model` for differentials with the transformation law only almost everywhere and a.e.-strongly measurable
coefficients (`gl31_cells_integral` for arbitrary chart functions; the norm is the partition sum by
`gl31_surfaceIntegral_eq_tsum_ae`). A bounded `ν` on `S` pulls back to bounded chart functions `gᵢ` with
`∬_S ν E φ = Σᵢ ∬_{φ_{xᵢ}(Pᵢ)} φ gᵢ` for `φ ∈ L₁(R)`. -/
theorem gl31_model_l1 [IsManifold 𝓘(ℂ) ω R] {x : ℕ → R} {P : ℕ → Set R} (hP : IsChartPartition R x P) :
    ∃ (S : Set ℂ) (E : (R → ℂ → ℂ) → ℂ → ℂ), MeasurableSet S ∧
      (∀ φ ψ, E (φ + ψ) = E φ + E ψ) ∧ (∀ (c : ℂ) φ, E (c • φ) = c • E φ) ∧
      (∀ φ : R → ℂ → ℂ, IsDiffFamilyAE 2 0 φ →
        (∀ y : R, AEStronglyMeasurable (φ y) (volume.restrict (chartAt ℂ y).target)) →
        AEStronglyMeasurable (E φ) (volume.restrict S) ∧ ∫⁻ w in S, ‖E φ w‖ₑ = quadDiffNorm φ) ∧
      ∀ ν : ℂ → ℂ, AEStronglyMeasurable ν (volume.restrict S) → ∀ c : ℝ, (∀ᵐ w ∂(volume.restrict S), ‖ν w‖ ≤ c) →
        ∃ g : ℕ → ℂ → ℂ, (∀ i, AEStronglyMeasurable (g i) (volume.restrict (chartAt ℂ (x i) '' P i))) ∧
          (∀ i, ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)), ‖g i z‖ ≤ c) ∧
          ∀ φ ∈ integrableQDSet R,
            ∫ w in S, ν w * E φ w = ∑' i, ∫ z in chartAt ℂ (x i) '' P i, φ (x i) z * g i z := by
  obtain ⟨ι, piece, t, hpm, hpU, hpd, htd⟩ := gl31_cells hP
  have hQm : ∀ m, MeasurableSet ((fun w => w + t m) '' piece m) := fun m => by
    rw [image_add_right]
    exact measurable_add_const (-t m) (hpm m).1
  have hSm : MeasurableSet (⋃ m, (fun w => w + t m) '' piece m) := MeasurableSet.iUnion hQm
  have hemb : ∀ m, MeasurableEmbedding fun z : ℂ => z + t m := fun m => measurableEmbedding_addRight (t m)
  have hmpr : ∀ m, MeasurePreserving (fun z : ℂ => z + t m) (volume.restrict (piece m))
      (volume.restrict ((fun w => w + t m) '' piece m)) := fun m =>
    (measurePreserving_add_right volume (t m)).restrict_image_emb (hemb m) (piece m)
  have hfib : ∀ i, chartAt ℂ (x i) '' P i = ⋃ m : ι ⁻¹' {i}, piece m := fun i => by
    rw [hpU i]
    ext w
    simp only [mem_iUnion, exists_prop, Subtype.exists, mem_preimage, mem_singleton_iff]
  -- the sum of the translated indicators picks the unique piece containing the point
  have hval : ∀ (F : ℕ → ℂ → ℂ) m, ∀ w ∈ (fun w => w + t m) '' piece m,
      ∑' m', ((fun w => w + t m') '' piece m').indicator (F m') w = F m w := by
    intro F m w hw
    rw [tsum_eq_single m fun m' hm' => indicator_of_notMem (fun hw' => Set.disjoint_left.1 (htd hm') hw' hw) _,
      indicator_of_mem hw]
  have hval0 : ∀ (F : ℕ → ℂ → ℂ) w, w ∉ ⋃ m, (fun w => w + t m) '' piece m →
      ∑' m', ((fun w => w + t m') '' piece m').indicator (F m') w = 0 := fun F w hw =>
    (tsum_congr fun m => indicator_of_notMem (fun h => hw (mem_iUnion.2 ⟨m, h⟩)) _).trans tsum_zero
  obtain ⟨E, hEdef⟩ : ∃ E : (R → ℂ → ℂ) → ℂ → ℂ, E = fun φ w =>
      ∑' m, ((fun w => w + t m) '' piece m).indicator (fun w => φ (x (ι m)) (w - t m)) w := ⟨_, rfl⟩
  have hE : ∀ φ m, ∀ w ∈ (fun w => w + t m) '' piece m, E φ w = φ (x (ι m)) (w - t m) := by
    intro φ m w hw
    rw [hEdef]
    exact hval (fun m w => φ (x (ι m)) (w - t m)) m w hw
  have hE0 : ∀ φ w, w ∉ ⋃ m, (fun w => w + t m) '' piece m → E φ w = 0 := by
    intro φ w hw
    rw [hEdef]
    exact hval0 (fun m w => φ (x (ι m)) (w - t m)) w hw
  -- the chart functions of a holomorphic `φ` are continuous on the chart targets
  have hcont : ∀ φ : R → ℂ → ℂ, (∀ y : R, AEStronglyMeasurable (φ y) (volume.restrict (chartAt ℂ y).target)) →
      ∀ i, AEStronglyMeasurable (φ (x i)) (volume.restrict (chartAt ℂ (x i) '' P i)) := fun φ hφ i =>
    (hφ (x i)).mono_measure (Measure.restrict_mono (image_subset_iff.2 fun y hy =>
      (chartAt ℂ (x i)).map_source ((hP.1 i).1 hy)) le_rfl)
  have hnorm : ∀ φ : R → ℂ → ℂ, IsDiffFamilyAE 2 0 φ →
      quadDiffNorm φ = ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z‖ₑ := by
    intro φ hφ
    have e := gl31_surfaceIntegral_eq_tsum_ae hφ hP
    simp only [ofReal_norm] at e
    exact e
  refine ⟨⋃ m, (fun w => w + t m) '' piece m, E, hSm, fun φ ψ => ?_, fun c φ => ?_, fun φ hl hm => ?_, ?_⟩
  · funext w
    by_cases hw : w ∈ ⋃ m, (fun w => w + t m) '' piece m
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hw
      simp only [Pi.add_apply, hE (φ + ψ) m w hm, hE φ m w hm, hE ψ m w hm]
    · simp only [Pi.add_apply, hE0 (φ + ψ) w hw, hE0 φ w hw, hE0 ψ w hw, add_zero]
  · funext w
    by_cases hw : w ∈ ⋃ m, (fun w => w + t m) '' piece m
    · obtain ⟨m, hm⟩ := mem_iUnion.1 hw
      simp only [Pi.smul_apply, hE (c • φ) m w hm, hE φ m w hm]
    · simp only [Pi.smul_apply, hE0 (c • φ) w hw, hE0 φ w hw, smul_zero]
  · have hci := gl31_cells_integral hpm hpU hpd htd (fun i => φ (x i))
    have hEe : E φ = fun w =>
        ∑' m, ((fun w => w + t m) '' piece m).indicator (fun w => φ (x (ι m)) (w - t m)) w := by
      rw [hEdef]
    refine ⟨?_, ?_⟩
    · rw [hEe]
      exact (hci.2 (hcont φ hm)).1
    · rw [hEe, hci.1, hnorm φ hl]
  · intro ν hν c hc
    obtain ⟨g, hgdef⟩ : ∃ g : ℕ → ℂ → ℂ, g = fun i z =>
        ∑' m, if ι m = i then (piece m).indicator (fun z => ν (z + t m)) z else 0 := ⟨_, rfl⟩
    -- `gᵢ = ν(· + t m)` on the pieces `m` of `φ_{xᵢ}(Pᵢ)`
    have hg : ∀ i m, ι m = i → ∀ z ∈ piece m, g i z = ν (z + t m) := by
      intro i m hmi z hz
      rw [hgdef]
      refine (tsum_eq_single m fun m' hm' => ?_).trans (by rw [ite_eq_left hmi, indicator_of_mem hz])
      by_cases h' : ι m' = i
      · rw [ite_eq_left h']
        exact indicator_of_notMem (fun hz' => Set.disjoint_left.1 (hpd hm' (h'.trans hmi.symm)) hz' hz) _
      · rw [ite_eq_right h']
    have hνm : ∀ m, AEStronglyMeasurable (fun z => ν (z + t m)) (volume.restrict (piece m)) := fun m =>
      (hν.mono_measure (Measure.restrict_mono (subset_iUnion (fun m => (fun w => w + t m) '' piece m) m)
        le_rfl)).comp_quasiMeasurePreserving (hmpr m).quasiMeasurePreserving
    have hνb : ∀ m, ∀ᵐ z ∂(volume.restrict (piece m)), ‖ν (z + t m)‖ ≤ c := fun m =>
      (hmpr m).quasiMeasurePreserving.ae
        (ae_restrict_of_ae_restrict_of_subset (subset_iUnion (fun m => (fun w => w + t m) '' piece m) m) hc)
    have hgm : ∀ i, AEStronglyMeasurable (g i) (volume.restrict (chartAt ℂ (x i) '' P i)) := by
      intro i
      rw [hfib i]
      refine aestronglyMeasurable_iUnion_iff.2 fun m => (hνm m).congr ?_
      exact (ae_restrict_iff' (hpm m).1).2 (Eventually.of_forall fun z hz => (hg i m m.2 z hz).symm)
    have hgb : ∀ i, ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)), ‖g i z‖ ≤ c := by
      intro i
      rw [hfib i]
      refine (ae_restrict_iUnion_iff _ _).2 fun m => ?_
      filter_upwards [hνb m, ae_restrict_mem (hpm m).1] with z hz hzm
      rw [hg i m m.2 z hzm]
      exact hz
    refine ⟨g, hgm, hgb, fun φ hφ => ?_⟩
    -- `ν · Eφ` is the cell picture of the chart functions `φ_{xᵢ} gᵢ`
    have hci := gl31_cells_integral hpm hpU hpd htd (fun i z => φ (x i) z * g i z)
    have hfm : ∀ i, AEStronglyMeasurable (fun z => φ (x i) z * g i z) (volume.restrict (chartAt ℂ (x i) '' P i)) :=
      fun i => (hcont φ hφ.2.1 i).mul (hgm i)
    have hfin : ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖φ (x i) z * g i z‖ₑ < ⊤ := by
      calc _ ≤ ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal c * ‖φ (x i) z‖ₑ :=
            ENNReal.tsum_le_tsum fun i => lintegral_mono_ae (by
              filter_upwards [hgb i] with z hz
              rw [enorm_mul, mul_comm ‖φ (x i) z‖ₑ, ← ofReal_norm (g i z)]
              exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hz) _)
        _ = ENNReal.ofReal c * quadDiffNorm φ := by
            rw [hnorm φ hφ.1, ← ENNReal.tsum_mul_left]
            exact tsum_congr fun i => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφ.2.2
    refine (setIntegral_congr_fun hSm fun w hw => ?_).trans ((hci.2 hfm).2 hfin)
    obtain ⟨m, hm⟩ := mem_iUnion.1 hw
    rw [hE φ m w hm, hval _ m w hm]
    obtain ⟨z, hz, rfl⟩ := hm
    simp only [add_sub_cancel_right, hg (ι m) m rfl z hz]
    ring

/-- Helper for **Theorem 2** (§3.1, l. 2099). `L₁(R)` is closed under addition (`gl31_qdn_add_le`, the law and
measurability pass to sums). -/
theorem gl31_l1_add_mem [IsManifold 𝓘(ℂ) ω R] {φ ψ : R → ℂ → ℂ} (hφ : φ ∈ integrableQDSet R)
    (hψ : ψ ∈ integrableQDSet R) : φ + ψ ∈ integrableQDSet R := by
  obtain ⟨h1, hm1, hn1⟩ := hφ
  obtain ⟨h2, hm2, hn2⟩ := hψ
  refine ⟨?_, fun y => (hm1 y).add (hm2 y),
    lt_of_le_of_lt (gl31_qdn_add_le h1 h2 hm1 hm2) (ENNReal.add_lt_top.2 ⟨hn1, hn2⟩)⟩
  intro a b
  filter_upwards [h1 a b, h2 a b] with z e1 e2
  simp only [Pi.add_apply]
  rw [e1, e2]
  ring

/-- Helper for **Theorem 2** (§3.1, l. 2099). `L₁(R)` is closed under scalar multiples (the norm is the partition sum
`gl31_surfaceIntegral_eq_tsum_ae` on a chart partition, which exists because the norm is finite). -/
theorem gl31_l1_smul_mem [IsManifold 𝓘(ℂ) ω R] (c : ℂ) {φ : R → ℂ → ℂ} (hφ : φ ∈ integrableQDSet R) :
    c • φ ∈ integrableQDSet R := by
  obtain ⟨h1, hm1, hn1⟩ := hφ
  have hlaw : IsDiffFamilyAE 2 0 (c • φ) := by
    intro a b
    filter_upwards [h1 a b] with z e1
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [e1]
    ring
  refine ⟨hlaw, fun y => (hm1 y).const_smul c, ?_⟩
  obtain ⟨x, P, hP⟩ := gl31_exists_partition_of_ne_top hn1.ne
  rw [gl31_surfaceIntegral_eq_tsum_ae hlaw hP]
  have e := gl31_surfaceIntegral_eq_tsum_ae h1 hP
  calc ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖(c • φ) (x i) z‖
      = ENNReal.ofReal ‖c‖ * ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖φ (x i) z‖ := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun i => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun z => ?_
        simp only [Pi.smul_apply, smul_eq_mul, norm_mul, ENNReal.ofReal_mul (norm_nonneg c)]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (e ▸ hn1)

/-- Helper for **Theorem 2** (§3.1, l. 2099). `|(φ, μ)| ≤ ‖μ‖∞ ‖φ‖` for `φ ∈ L₁(R)` and a Beltrami differential `μ`
(on the partition chosen in `pairingRS`: `‖∫ φ μ‖ ≤ ∫ |φ μ| ≤ ‖μ‖∞ ∫ |φ|`, summed with
`gl31_surfaceIntegral_eq_tsum_ae`). -/
theorem gl31_l1_pairing_le [IsManifold 𝓘(ℂ) ω R] {φ μ : R → ℂ → ℂ} (hφ : φ ∈ integrableQDSet R)
    (hμ : μ ∈ beltramiSpace R) :
    ‖pairingRS φ μ‖ ≤ (beltramiNormRS μ).toReal * (quadDiffNorm φ).toReal := by
  have hμ' := hμ
  obtain ⟨k, -, hbd⟩ := hμ'
  have h := gl31_exists_partition_of_ne_top hφ.2.2.ne
  have hP := h.choose_spec.choose_spec
  have ha : beltramiNormRS μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal k) ENNReal.ofReal_ne_top (iSup_le fun y => ?_)
    rw [eLpNorm_exponent_top (hbd y).1]
    exact eLpNormEssSup_le_of_ae_bound (hbd y).2
  -- `|μ| ≤ ‖μ‖∞` a.e. in every chart
  have hA : ∀ y : R, ∀ᵐ z ∂(volume.restrict (chartAt ℂ y).target), ‖μ y z‖ₑ ≤ beltramiNormRS μ := by
    intro y
    filter_upwards [ae_le_eLpNormEssSup (μ := volume.restrict (chartAt ℂ y).target) (f := μ y)] with z hz
    rw [← eLpNorm_exponent_top (hbd y).1] at hz
    exact hz.trans (le_iSup (fun y => eLpNorm (μ y) ⊤ (volume.restrict (chartAt ℂ y).target)) y)
  have hS := gl31_surfaceIntegral_eq_tsum_ae hφ.1 hP
  have h2 : ‖pairingRS φ μ‖ₑ ≤ beltramiNormRS μ * quadDiffNorm φ := by
    rw [pairingRS, dite_eq_left h, hS, ← ENNReal.tsum_mul_left]
    calc _ ≤ ∑' i, ‖∫ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i,
          φ (h.choose i) z * μ (h.choose i) z‖ₑ := enorm_tsum_le_tsum_enorm
      _ ≤ ∑' i, ∫⁻ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i,
          ‖φ (h.choose i) z * μ (h.choose i) z‖ₑ := ENNReal.tsum_le_tsum fun i => enorm_integral_le_lintegral_enorm _
      _ ≤ _ := ENNReal.tsum_le_tsum fun i => by
          have hGt : chartAt ℂ (h.choose i) '' h.choose_spec.choose i ⊆ (chartAt ℂ (h.choose i)).target :=
            image_subset_iff.2 fun y hy => (chartAt ℂ (h.choose i)).map_source ((hP.1 i).1 hy)
          rw [← lintegral_const_mul' _ _ ha]
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hGt (hA (h.choose i))] with z hz
          rw [enorm_mul, ofReal_norm]
          calc ‖φ (h.choose i) z‖ₑ * ‖μ (h.choose i) z‖ₑ ≤ ‖φ (h.choose i) z‖ₑ * beltramiNormRS μ :=
                mul_le_mul' le_rfl hz
            _ = _ := mul_comm _ _
  calc ‖pairingRS φ μ‖ = (‖pairingRS φ μ‖ₑ).toReal := (toReal_enorm _).symm
    _ ≤ (beltramiNormRS μ * quadDiffNorm φ).toReal := ENNReal.toReal_mono (ENNReal.mul_ne_top ha hφ.2.2.ne) h2
    _ = (beltramiNormRS μ).toReal * (quadDiffNorm φ).toReal := ENNReal.toReal_mul

/-- Helper for **Theorem 2** (§3.1, l. 2099). For a Beltrami differential `μ`, `ψ ↦ (ψ, μ)` is a bounded linear
functional on `L₁(R)` (the partition terms are integrable and norm-summable by `gl31_l1_pairing_le`'s estimate, so the
sum splits; `gl31_l1_add_mem`, `gl31_l1_smul_mem`). -/
theorem gl31_l1_pairing_bdd [IsManifold 𝓘(ℂ) ω R] {μ : R → ℂ → ℂ} (hμ : μ ∈ beltramiSpace R) :
    IsBoundedFunctionalOn (integrableQDSet R) quadDiffNorm (fun ψ => pairingRS ψ μ) := by
  have hμ' := hμ
  obtain ⟨k, -, hbd⟩ := hμ'
  have ha : beltramiNormRS μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal k) ENNReal.ofReal_ne_top (iSup_le fun y => ?_)
    rw [eLpNorm_exponent_top (hbd y).1]
    exact eLpNormEssSup_le_of_ae_bound (hbd y).2
  have hA : ∀ y : R, ∀ᵐ z ∂(volume.restrict (chartAt ℂ y).target), ‖μ y z‖ₑ ≤ beltramiNormRS μ := by
    intro y
    filter_upwards [ae_le_eLpNormEssSup (μ := volume.restrict (chartAt ℂ y).target) (f := μ y)] with z hz
    rw [← eLpNorm_exponent_top (hbd y).1] at hz
    exact hz.trans (le_iSup (fun y => eLpNorm (μ y) ⊤ (volume.restrict (chartAt ℂ y).target)) y)
  -- the terms of the partition sum are integrable and norm-summable
  have hterm : ∀ {x : ℕ → R} {P : ℕ → Set R}, IsChartPartition R x P → ∀ a ∈ integrableQDSet R,
      (∀ i, IntegrableOn (fun z => a (x i) z * μ (x i) z) (chartAt ℂ (x i) '' P i)) ∧
        Summable (fun i => ∫ z in chartAt ℂ (x i) '' P i, a (x i) z * μ (x i) z) := by
    intro x P hP a haL
    have hS := gl31_surfaceIntegral_eq_tsum_ae haL.1 hP
    have hGt : ∀ i, chartAt ℂ (x i) '' P i ⊆ (chartAt ℂ (x i)).target := fun i =>
      image_subset_iff.2 fun y hy => (chartAt ℂ (x i)).map_source ((hP.1 i).1 hy)
    have hlint : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖a (x i) z * μ (x i) z‖ₑ ≤
        beltramiNormRS μ * ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖a (x i) z‖ := by
      intro i
      rw [← lintegral_const_mul' _ _ ha]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (hGt i) (hA (x i))] with z hz
      rw [enorm_mul, ofReal_norm]
      calc ‖a (x i) z‖ₑ * ‖μ (x i) z‖ₑ ≤ ‖a (x i) z‖ₑ * beltramiNormRS μ := mul_le_mul' le_rfl hz
        _ = _ := mul_comm _ _
    have hsum : ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖a (x i) z * μ (x i) z‖ₑ ≠ ⊤ := by
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ha haL.2.2.ne) ?_
      calc _ ≤ ∑' i, beltramiNormRS μ * ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖a (x i) z‖ :=
            ENNReal.tsum_le_tsum hlint
        _ = beltramiNormRS μ * quadDiffNorm a := by rw [ENNReal.tsum_mul_left, hS]
    refine ⟨fun i => ⟨?_, ?_⟩, ?_⟩
    · exact ((haL.2.1 (x i)).mono_measure (Measure.restrict_mono (hGt i) le_rfl)).mul
        ((hbd (x i)).1.mono_measure (Measure.restrict_mono (hGt i) le_rfl))
    · exact (ENNReal.le_tsum (f := fun i => ∫⁻ z in chartAt ℂ (x i) '' P i, ‖a (x i) z * μ (x i) z‖ₑ) i).trans_lt
        (lt_top_iff_ne_top.2 hsum)
    · exact Summable.of_norm_bounded (ENNReal.summable_toReal hsum) fun i =>
        (norm_integral_le_lintegral_norm _).trans_eq (by simp only [ofReal_norm])
  refine ⟨fun a haL b hbL => ?_, fun c a haL => ?_, (beltramiNormRS μ).toReal,
    fun a haL => gl31_l1_pairing_le haL hμ⟩
  · have h := gl31_exists_partition_of_ne_top haL.2.2.ne
    have hP := h.choose_spec.choose_spec
    simp only [pairingRS, dif_pos h]
    rw [← Summable.tsum_add (hterm hP a haL).2 (hterm hP b hbL).2]
    refine tsum_congr fun i => ?_
    rw [← integral_add ((hterm hP a haL).1 i) ((hterm hP b hbL).1 i)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [Pi.add_apply, add_mul]
  · have h := gl31_exists_partition_of_ne_top haL.2.2.ne
    simp only [pairingRS, dif_pos h]
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- Helper for **Theorem 2** (§3.1, l. 2099). A bounded functional `V` on `L₁(R)` is `ψ ↦ (ψ, μ)` for some Beltrami
differential `μ` with `‖μ‖∞ ≤ ‖V‖`, when `R` has a chart partition: `V` factors through the `L¹` model of
`gl31_model_l1` (a function of `E φ`: `‖φ − ψ‖ = ∫_S |E φ − E ψ|`), Hahn–Banach on `L¹(S)` (`gl3_dual_repr`) gives `ν`
with `|ν| ≤ ‖V‖`, which pulls back to chart functions `gᵢ` (`gl31_model_l1`), and `gl31_beltrami_extend` extends them
to `μ` (as in `gl31_dual_rep` and `thm3_2_b`). -/
theorem gl31_l1_rep [IsManifold 𝓘(ℂ) ω R] {V : (R → ℂ → ℂ) → ℂ}
    (hV : IsBoundedFunctionalOn (integrableQDSet R) quadDiffNorm V)
    (h : ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P) :
    ∃ μ ∈ beltramiSpace R, (∀ ψ ∈ integrableQDSet R, V ψ = pairingRS ψ μ) ∧
      beltramiNormRS μ ≤ ENNReal.ofReal (dualNormOn (integrableQDSet R) quadDiffNorm V) := by
  classical
  obtain ⟨S, E, hSm, hadd, hsmul, hnorm, hrep⟩ := gl31_model_l1 h.choose_spec.choose_spec
  obtain ⟨hVadd, hVsmul, C, hC⟩ := hV
  set D := dualNormOn (integrableQDSet R) quadDiffNorm V
  have hD0 : 0 ≤ D := Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hEn : ∀ φ ∈ integrableQDSet R, quadDiffNorm φ = ∫⁻ w in S, ‖E φ w‖ₑ := fun φ hφ =>
    (hnorm φ hφ.1 hφ.2.1).2.symm
  have hE0 : E 0 = 0 := by
    have e := hsmul 0 0
    rwa [zero_smul, zero_smul] at e
  have hsub : ∀ φ ψ, E (φ - ψ) = E φ - E ψ := fun φ ψ => by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ, hadd, hsmul, neg_one_smul, ← sub_eq_add_neg]
  -- `A(R)` is closed under the linear operations
  have hAadd : ∀ φ ∈ integrableQDSet R, ∀ ψ ∈ integrableQDSet R, φ + ψ ∈ integrableQDSet R :=
    fun φ hφ ψ hψ => gl31_l1_add_mem hφ hψ
  have hAsmul : ∀ c : ℂ, ∀ φ ∈ integrableQDSet R, c • φ ∈ integrableQDSet R :=
    fun c φ hφ => gl31_l1_smul_mem c hφ
  have harea : ∀ φ ∈ integrableQDSet R, phiArea (E φ) S = quadDiffNorm φ := by
    intro φ hφ
    rw [hEn φ hφ]
    show ∫⁻ z in S, ENNReal.ofReal ‖E φ z‖ = _
    simp only [ofReal_norm]
  -- `V` is well defined on the image `E(A(R))`: `‖φ − ψ‖ = ∫_S |Eφ − Eψ|`
  have hwd : ∀ φ ∈ integrableQDSet R, ∀ ψ ∈ integrableQDSet R, E φ = E ψ → V φ = V ψ := by
    intro φ hφ ψ hψ he
    have hmem : φ - ψ ∈ integrableQDSet R := by
      rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ]
      exact hAadd φ hφ _ (hAsmul _ ψ hψ)
    have h0 : quadDiffNorm (φ - ψ) = 0 := by
      rw [hEn _ hmem, hsub, he, sub_self]
      simp
    have hV0 : V (φ - ψ) = 0 := by
      have e := hC _ hmem
      rw [h0, ENNReal.toReal_zero, mul_zero] at e
      exact norm_le_zero_iff.1 e
    rw [← sub_add_cancel φ ψ, hVadd _ hmem _ hψ, hV0, zero_add]
  obtain ⟨V', hV'def⟩ : ∃ V' : (ℂ → ℂ) → ℂ, V' = fun f =>
      if hf : ∃ φ ∈ integrableQDSet R, E φ = f then V hf.choose else 0 := ⟨_, rfl⟩
  have hV' : ∀ φ ∈ integrableQDSet R, V' (E φ) = V φ := by
    intro φ hφ
    have hex : ∃ ψ ∈ integrableQDSet R, E ψ = E φ := ⟨φ, hφ, rfl⟩
    simp only [hV'def]
    rw [dite_eq_left hex]
    exact hwd _ hex.choose_spec.1 _ hφ hex.choose_spec.2
  -- Hahn–Banach on `L¹(S)` (`gl3_dual_repr`) for `V′` on `E(A(R))`
  have hA'int : ∀ f ∈ E '' integrableQDSet R, IntegrableOn f S := by
    rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨(hnorm φ hφ.1 hφ.2.1).1, ?_⟩
    show ∫⁻ w, ‖E φ w‖ₑ ∂(volume.restrict S) < ⊤
    rw [(hnorm φ hφ.1 hφ.2.1).2]
    exact hφ.2.2
  have h00 : (0 : R → ℂ → ℂ) ∈ integrableQDSet R := by
    have hlaw : IsDiffFamilyAE 2 0 (0 : R → ℂ → ℂ) := fun a b => ae_of_all _ fun z => by simp
    refine ⟨hlaw, fun y => aestronglyMeasurable_const, ?_⟩
    rw [gl31_surfaceIntegral_eq_tsum_ae hlaw h.choose_spec.choose_spec]
    simp
  have hA'0 : (0 : ℂ → ℂ) ∈ E '' integrableQDSet R := ⟨0, h00, hE0⟩
  have hA'add : ∀ f ∈ E '' integrableQDSet R, ∀ f' ∈ E '' integrableQDSet R,
      f + f' ∈ E '' integrableQDSet R := by
    rintro _ ⟨φ, hφ, rfl⟩ _ ⟨ψ, hψ, rfl⟩
    exact ⟨φ + ψ, hAadd φ hφ ψ hψ, hadd φ ψ⟩
  have hA'smul : ∀ c : ℂ, ∀ f ∈ E '' integrableQDSet R, c • f ∈ E '' integrableQDSet R := by
    rintro c _ ⟨φ, hφ, rfl⟩
    exact ⟨c • φ, hAsmul c φ hφ, hsmul c φ⟩
  have hV'b : IsBoundedFunctionalOn (E '' integrableQDSet R) (fun f => phiArea f S) V' := by
    refine ⟨?_, ?_, C, ?_⟩
    · rintro _ ⟨φ, hφ, rfl⟩ _ ⟨ψ, hψ, rfl⟩
      rw [← hadd, hV' _ (hAadd φ hφ ψ hψ), hV' φ hφ, hV' ψ hψ, hVadd φ hφ ψ hψ]
    · rintro c _ ⟨φ, hφ, rfl⟩
      rw [← hsmul, hV' _ (hAsmul c φ hφ), hV' φ hφ, hVsmul c φ hφ]
    · rintro _ ⟨φ, hφ, rfl⟩
      show ‖V' (E φ)‖ ≤ C * (phiArea (E φ) S).toReal
      rw [hV' φ hφ, harea φ hφ]
      exact hC φ hφ
  obtain ⟨ν, hνm, hνb, hνrep⟩ := gl3_dual_repr hSm hA'int hA'0 hA'add hA'smul hV'b
  -- the dual norm of `V′` on the image is at most `‖V‖`
  have hle : dualNormOn (E '' integrableQDSet R) (fun f => phiArea f S) V' ≤ D := by
    refine Real.iSup_le (fun f => Real.iSup_le (fun hf => ?_) hD0) hD0
    obtain ⟨⟨φ, hφ, rfl⟩, h1⟩ := hf
    rw [hV' φ hφ]
    have hφ1 : quadDiffNorm φ = 1 := by
      rw [← harea φ hφ]
      exact h1
    have hbdd : BddAbove (range fun a => ⨆ (_ : a ∈ integrableQDSet R ∧ quadDiffNorm a = 1), ‖V a‖) := by
      refine ⟨max C 0, ?_⟩
      rintro _ ⟨χ, rfl⟩
      refine Real.iSup_le (fun hχ => ?_) (le_max_right _ _)
      have e := hC χ hχ.1
      rw [hχ.2, ENNReal.toReal_one, mul_one] at e
      exact e.trans (le_max_left _ _)
    calc ‖V φ‖ = ⨆ (_ : φ ∈ integrableQDSet R ∧ quadDiffNorm φ = 1), ‖V φ‖ :=
          (ciSup_pos (f := fun _ => ‖V φ‖) ⟨hφ, hφ1⟩).symm
      _ ≤ D := le_ciSup hbdd φ
  -- pull `ν` back to the charts of the chosen partition
  obtain ⟨g, hgm, hgb, hgrep⟩ := hrep ν hνm D (by
    filter_upwards [hνb] with z hz
    exact hz.trans hle)
  obtain ⟨μ, hμ, hμg, hμn⟩ := gl31_beltrami_extend h.choose_spec.choose_spec g hD0 hgm hgb
  refine ⟨μ, hμ, fun φ hφ => ?_, hμn⟩
  rw [← hV' φ hφ, hνrep _ ⟨φ, hφ, rfl⟩, hgrep φ hφ, pairingRS, dite_eq_left h]
  refine tsum_congr fun i => setIntegral_congr_fun (h.choose_spec.choose_spec.1 i).2 fun z hz => ?_
  rw [hμg i z hz]

/-- Helper for **Theorem 2** (§3.1, l. 2099). Beltrami differentials representing the same functional on `L₁(R)` have
the same norm, when `R` has a chart partition: testing against the integrable differentials `ψ` of `gl31_qd_extend`
with `ψ_{xᵢ} = \overline{d}/|d| · 𝟙_{B(0,n)}` on one piece (`d = μ_{xᵢ} − μ′_{xᵢ}`) gives `μ = μ′` a.e. on every piece,
and the law `(−1, 1)` (a.e. on the overlaps) carries this to every chart. -/
theorem gl31_l1_unique [IsManifold 𝓘(ℂ) ω R] {μ μ' : R → ℂ → ℂ} (hμ : μ ∈ beltramiSpace R)
    (hμ' : μ' ∈ beltramiSpace R) (h : ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P)
    (heq : ∀ ψ ∈ integrableQDSet R, pairingRS ψ μ = pairingRS ψ μ') :
    beltramiNormRS μ ≤ beltramiNormRS μ' := by
  obtain ⟨k, hlaw, hbd⟩ := hμ
  obtain ⟨k', hlaw', hbd'⟩ := hμ'
  have main : ∀ {x : ℕ → R} {P : ℕ → Set R}, IsChartPartition R x P →
      (∀ ψ ∈ integrableQDSet R, ∑' i, ∫ z in chartAt ℂ (x i) '' P i, ψ (x i) z * μ (x i) z =
        ∑' i, ∫ z in chartAt ℂ (x i) '' P i, ψ (x i) z * μ' (x i) z) →
      beltramiNormRS μ ≤ beltramiNormRS μ' := by
    intro x P hP hpair
    -- step 1: `μ = μ′` a.e. on every piece `φ_{xᵢ}(Pᵢ)`
    have hpiece : ∀ i0, ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i0) '' P i0)), μ (x i0) z = μ' (x i0) z := by
      intro i0
      obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℂ → ℝ, ρ = fun z => ((1 + ‖z‖) ^ 3)⁻¹ := ⟨_, rfl⟩
      have hρpos : ∀ z, 0 < ρ z := fun z => by simp only [hρdef]; positivity
      have hρint : Integrable ρ := by
        rw [hρdef]
        exact LiZhongQC.b36_p_profile_integrable
      have hρm : Measurable ρ := by simp only [hρdef]; fun_prop
      have hGt : chartAt ℂ (x i0) '' P i0 ⊆ (chartAt ℂ (x i0)).target :=
        image_subset_iff.2 fun y hy => (chartAt ℂ (x i0)).map_source ((hP.1 i0).1 hy)
      have hm1 : AEStronglyMeasurable (μ (x i0)) (volume.restrict (chartAt ℂ (x i0) '' P i0)) :=
        (hbd (x i0)).1.mono_measure (Measure.restrict_mono hGt le_rfl)
      have hm2 : AEStronglyMeasurable (μ' (x i0)) (volume.restrict (chartAt ℂ (x i0) '' P i0)) :=
        (hbd' (x i0)).1.mono_measure (Measure.restrict_mono hGt le_rfl)
      have hb1 : ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i0) '' P i0)), ‖μ (x i0) z‖ ≤ k :=
        ae_restrict_of_ae_restrict_of_subset hGt (hbd (x i0)).2
      have hb2 : ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i0) '' P i0)), ‖μ' (x i0) z‖ ≤ k' :=
        ae_restrict_of_ae_restrict_of_subset hGt (hbd' (x i0)).2
      -- the phase `u = \bar d / |d|` of the difference `d = μ − μ′`
      obtain ⟨d, hddef⟩ : ∃ d : ℂ → ℂ, d = fun z => μ (x i0) z - μ' (x i0) z := ⟨_, rfl⟩
      obtain ⟨u, hudef⟩ : ∃ u : ℂ → ℂ, u = fun z => conj (d z) / ((‖d z‖ : ℝ) : ℂ) := ⟨_, rfl⟩
      have hdm : AEStronglyMeasurable d (volume.restrict (chartAt ℂ (x i0) '' P i0)) := by
        rw [hddef]
        exact hm1.sub hm2
      have hum : AEStronglyMeasurable u (volume.restrict (chartAt ℂ (x i0) '' P i0)) := by
        rw [hudef]
        exact ((Complex.continuous_conj.measurable.comp_aemeasurable hdm.aemeasurable).div
          (Complex.measurable_ofReal.comp_aemeasurable hdm.aemeasurable.norm)).aestronglyMeasurable
      have hule : ∀ z, ‖u z‖ ≤ 1 := by
        intro z
        rw [hudef]
        show ‖conj (d z) / ((‖d z‖ : ℝ) : ℂ)‖ ≤ 1
        by_cases hz : d z = 0
        · rw [hz]
          simp
        · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self
            (norm_ne_zero_iff.2 hz)]
      have hdu : ∀ z, d z * u z = ((‖d z‖ : ℝ) : ℂ) := by
        intro z
        rw [hudef]
        show d z * (conj (d z) / ((‖d z‖ : ℝ) : ℂ)) = ((‖d z‖ : ℝ) : ℂ)
        by_cases hz : d z = 0
        · rw [hz]
          simp
        · have hn : ((‖d z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
          rw [mul_div_assoc', mul_comm, Complex.conj_mul', div_eq_iff hn]
          push_cast
          ring
      -- the test chart functions: `ρ u` on the piece `i0`, `0` elsewhere
      obtain ⟨f, hfdef⟩ : ∃ f : ℕ → ℂ → ℂ, f = fun i z => if i = i0 then (ρ z : ℂ) * u z else 0 := ⟨_, rfl⟩
      have hfm : ∀ i, AEStronglyMeasurable (f i) (volume.restrict (chartAt ℂ (x i) '' P i)) := by
        intro i
        by_cases hi : i = i0
        · subst hi
          simp only [hfdef, if_true]
          exact (Complex.measurable_ofReal.comp hρm).aestronglyMeasurable.mul hum
        · simp only [hfdef, hi, if_false]
          exact aestronglyMeasurable_const
      have hfin : ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ‖f i z‖ₑ < ⊤ := by
        rw [tsum_eq_single i0 (fun i hi => by simp [hfdef, hi])]
        calc ∫⁻ z in chartAt ℂ (x i0) '' P i0, ‖f i0 z‖ₑ ≤ ∫⁻ z, ‖ρ z‖ₑ := by
              refine (setLIntegral_le_lintegral _ _).trans' (lintegral_mono fun z => ?_)
              simp only [hfdef, if_true, enorm_mul]
              calc ‖(ρ z : ℂ)‖ₑ * ‖u z‖ₑ ≤ ‖(ρ z : ℂ)‖ₑ * 1 :=
                    mul_le_mul' le_rfl (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_one.2 (hule z))
                _ = ‖ρ z‖ₑ := by rw [mul_one, ← ofReal_norm, ← ofReal_norm, Complex.norm_real]
          _ < ⊤ := hρint.hasFiniteIntegral
      obtain ⟨ψ, hψ, hψv⟩ := gl31_qd_extend hP f hfm hfin
      have hcalc : ∀ m : R → ℂ → ℂ, ∑' i, ∫ z in chartAt ℂ (x i) '' P i, ψ (x i) z * m (x i) z =
          ∫ z in chartAt ℂ (x i0) '' P i0, (ρ z : ℂ) * u z * m (x i0) z := by
        intro m
        rw [tsum_eq_single i0]
        · refine setIntegral_congr_fun (hP.1 i0).2 fun z hz => ?_
          rw [hψv i0 z hz]
          simp [hfdef]
        · intro i hi
          rw [setIntegral_congr_fun (hP.1 i).2 (g := fun _ => (0 : ℂ)) fun z hz => by
            rw [hψv i z hz]
            simp [hfdef, hi]]
          simp
      have hint : ∀ (m : R → ℂ → ℂ) (kk : ℝ), AEStronglyMeasurable (m (x i0))
          (volume.restrict (chartAt ℂ (x i0) '' P i0)) →
          (∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i0) '' P i0)), ‖m (x i0) z‖ ≤ kk) →
          IntegrableOn (fun z => (ρ z : ℂ) * u z * m (x i0) z) (chartAt ℂ (x i0) '' P i0) := by
        intro m kk hm hb
        refine Integrable.mono' (hρint.integrableOn.const_mul kk) ?_ ?_
        · exact ((Complex.measurable_ofReal.comp hρm).aestronglyMeasurable.mul hum).mul hm
        · filter_upwards [hb] with z hz
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρpos z).le]
          calc ρ z * ‖u z‖ * ‖m (x i0) z‖ ≤ ρ z * 1 * kk :=
                mul_le_mul (mul_le_mul_of_nonneg_left (hule z) (hρpos z).le) hz (norm_nonneg _)
                  (mul_nonneg (hρpos z).le zero_le_one)
            _ = kk * ρ z := by ring
      have h1 := hint μ k hm1 hb1
      have h2 := hint μ' k' hm2 hb2
      have hz := hpair ψ hψ
      rw [hcalc μ, hcalc μ'] at hz
      -- the difference is `∫ ρ |d| = 0`
      have hr : ∫ z in chartAt ℂ (x i0) '' P i0, (((ρ z * ‖d z‖ : ℝ)) : ℂ) = 0 := by
        have e : ∫ z in chartAt ℂ (x i0) '' P i0, (((ρ z * ‖d z‖ : ℝ)) : ℂ) =
            (∫ z in chartAt ℂ (x i0) '' P i0, (ρ z : ℂ) * u z * μ (x i0) z) -
              ∫ z in chartAt ℂ (x i0) '' P i0, (ρ z : ℂ) * u z * μ' (x i0) z := by
          rw [← integral_sub h1 h2]
          refine integral_congr_ae (ae_of_all _ fun z => ?_)
          have e1 := hdu z
          rw [hddef] at e1
          simp only [hddef] at e1 ⊢
          push_cast
          rw [← e1]
          ring
        rw [e, hz, sub_self]
      have hrint : Integrable (fun z => ρ z * ‖d z‖) (volume.restrict (chartAt ℂ (x i0) '' P i0)) := by
        refine Integrable.mono' (hρint.integrableOn.const_mul (k + k')) ?_ ?_
        · exact ((hρm.aestronglyMeasurable).mul hdm.norm)
        · filter_upwards [hb1, hb2] with z e1 e2
          rw [Real.norm_of_nonneg (mul_nonneg (hρpos z).le (norm_nonneg _)), hddef]
          calc ρ z * ‖μ (x i0) z - μ' (x i0) z‖ ≤ ρ z * (k + k') :=
                mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add e1 e2)) (hρpos z).le
            _ = (k + k') * ρ z := by ring
      have hr0 : ∫ z in chartAt ℂ (x i0) '' P i0, ρ z * ‖d z‖ = 0 := by
        have e := hr
        rw [integral_complex_ofReal] at e
        exact_mod_cast e
      have hae := (integral_eq_zero_iff_of_nonneg (fun z => mul_nonneg (hρpos z).le (norm_nonneg _)) hrint).1 hr0
      filter_upwards [hae] with z hz'
      have hz2 : ρ z * ‖d z‖ = 0 := hz'
      have hdz : ‖d z‖ = 0 := (mul_eq_zero.1 hz2).resolve_left (hρpos z).ne'
      rw [hddef] at hdz
      exact sub_eq_zero.1 (norm_eq_zero.1 hdz)
    -- step 2: `μ = μ′` a.e. on every chart target, through the law almost everywhere
    have hchart : ∀ y : R, μ y =ᵐ[volume.restrict (chartAt ℂ y).target] μ' y := by
      intro y
      have hOU : (chartAt ℂ y).target = ⋃ i, (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i := by
        rw [← inter_iUnion, ← preimage_iUnion, hP.2.2, preimage_univ, inter_univ]
      rw [hOU]
      refine (ae_restrict_iUnion_iff _ _).2 fun i => ?_
      obtain ⟨hOm, hAm, hac⟩ := gl31_transition_ac hP y i
      have h1 := ae_of_ae_map hAm (hac.ae_le (hpiece i))
      have hWO : (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' P i ⊆
          (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ (x i)).source :=
        fun w hw => ⟨hw.1, (hP.1 i).1 hw.2⟩
      have h2 := ae_restrict_of_ae_restrict_of_subset hWO (hlaw (x i) y)
      have h3 := ae_restrict_of_ae_restrict_of_subset hWO (hlaw' (x i) y)
      filter_upwards [h1, h2, h3] with w e1 e2 e3
      rw [e2, e3, e1]
    exact iSup_mono fun y => (eLpNorm_congr_ae (hchart y)).le
  refine main h.choose_spec.choose_spec fun ψ hψ => ?_
  have e := heq ψ hψ
  simpa only [pairingRS, dif_pos h] using e

/-- **Theorem 2** (§3.1, l. 2099), first part. The pairing induces an isometric isomorphism of `L₁(R)*` onto `L∞(R)`:
every `μ ∈ L∞(R)` gives a bounded functional of norm `‖μ‖∞`, and every bounded functional on `L₁(R)` is
`ψ ↦ (ψ, μ)` for such a `μ`.

[CORRECTION/modelling] The binder `[SecondCountableTopology R]` is added. The book's Riemann surfaces are connected,
hence second countable (Radó's theorem, which the project does not have), but a charted space need not be: for the
disjoint union `R` of uncountably many discs (all transitions are identities) no chart partition exists, so
`quadDiffNorm q = ⊤` for every `q` and `integrableQDSet R = ∅`, the dual norm is `0` (an empty supremum) while the
constant Beltrami differential `μ = 1/2` has `beltramiNormRS μ = 1/2`: the first conjunct fails. With the binder the
statement is true (an empty `R` has no norm and no functional; a nonempty `R` has chart partitions
`gl31_exists_chartPartition`). -/
theorem thm3_2_a [IsManifold 𝓘(ℂ) ω R] [SecondCountableTopology R] :
    (∀ μ ∈ beltramiSpace R, IsBoundedFunctionalOn (integrableQDSet R) quadDiffNorm (fun ψ => pairingRS ψ μ) ∧
      ENNReal.ofReal (dualNormOn (integrableQDSet R) quadDiffNorm (fun ψ => pairingRS ψ μ)) = beltramiNormRS μ) ∧
    ∀ ℓ : (R → ℂ → ℂ) → ℂ, IsBoundedFunctionalOn (integrableQDSet R) quadDiffNorm ℓ →
      ∃ μ ∈ beltramiSpace R, ∀ ψ ∈ integrableQDSet R, ℓ ψ = pairingRS ψ μ := by
  classical
  by_cases h : ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P
  · -- the dual norm is at most the norm of `μ` (`gl31_l1_pairing_le`)
    have hdual : ∀ μ ∈ beltramiSpace R,
        ENNReal.ofReal (dualNormOn (integrableQDSet R) quadDiffNorm (fun ψ => pairingRS ψ μ)) ≤
          beltramiNormRS μ := by
      intro μ hμ
      by_cases hfin : beltramiNormRS μ = ⊤
      · rw [hfin]
        exact le_top
      rw [← ENNReal.ofReal_toReal hfin]
      refine ENNReal.ofReal_le_ofReal (Real.iSup_le (fun φ => Real.iSup_le (fun hφ => ?_) ENNReal.toReal_nonneg)
        ENNReal.toReal_nonneg)
      calc ‖pairingRS φ μ‖ ≤ (beltramiNormRS μ).toReal * (quadDiffNorm φ).toReal := gl31_l1_pairing_le hφ.1 hμ
        _ = (beltramiNormRS μ).toReal := by rw [hφ.2, ENNReal.toReal_one, mul_one]
    refine ⟨fun μ hμ => ⟨gl31_l1_pairing_bdd hμ, le_antisymm (hdual μ hμ) ?_⟩, fun ℓ hℓ => ?_⟩
    · -- `V_μ` is represented by some `μ′` with `‖μ′‖∞ ≤ ‖V_μ‖`, and `‖μ‖∞ = ‖μ′‖∞`
      obtain ⟨μ', hμ', hrep, hn⟩ := gl31_l1_rep (gl31_l1_pairing_bdd hμ) h
      exact (gl31_l1_unique hμ hμ' h hrep).trans hn
    · obtain ⟨μ, hμ, hrep, -⟩ := gl31_l1_rep hℓ h
      exact ⟨μ, hμ, hrep⟩
  · -- no chart partition: `L₁(R) = ∅` (every norm is `⊤`), and `R` is empty by second countability
    have hA : ∀ φ, φ ∉ integrableQDSet R := fun φ hφ => h (gl31_exists_partition_of_ne_top hφ.2.2.ne)
    have hR : IsEmpty R := by
      by_contra hne
      rw [not_isEmpty_iff] at hne
      obtain ⟨x, P, hP, -⟩ := gl31_exists_chartPartition (R := R) (fun y => (chartAt ℂ y).source)
        (fun y => (chartAt ℂ y).open_source) (fun y => mem_chart_source ℂ y) (fun _ => subset_rfl)
      exact h ⟨x, P, hP⟩
    have h0 : (0 : R → ℂ → ℂ) ∈ beltramiSpace R := by
      refine ⟨0, fun x y => ae_of_all _ fun z => ?_, fun x => ⟨aestronglyMeasurable_const, ae_of_all _ fun z => ?_⟩⟩
      · simp
      · simp
    refine ⟨fun μ hμ => ⟨⟨fun a ha => absurd ha (hA a), fun c a ha => absurd ha (hA a), 0,
      fun a ha => absurd ha (hA a)⟩, ?_⟩, fun ℓ hℓ => ⟨0, h0, fun ψ hψ => absurd hψ (hA ψ)⟩⟩
    have hD : dualNormOn (integrableQDSet R) quadDiffNorm (fun ψ => pairingRS ψ μ) = 0 :=
      le_antisymm (Real.iSup_le (fun φ => Real.iSup_le (fun hφ => absurd hφ.1 (hA φ)) le_rfl) le_rfl)
        (Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _)
    have hn : beltramiNormRS μ = 0 := by
      haveI := hR
      simp [beltramiNormRS]
    rw [hD, hn, ENNReal.ofReal_zero]

/-- Helper for **Theorem 2** (§3.1, l. 2099). A bounded functional on `A(R)` is represented on the partition `(x, P)`
chosen in `pairingRS` by chart functions bounded by its dual norm: `V φ = Σᵢ ∬_{φ_{xᵢ}(Pᵢ)} φ_{xᵢ} gᵢ` (`V` moves to
the image of `A(R)` in the `L¹` model of `gl31_model`, where `gl3_dual_repr` applies). -/
theorem gl31_dual_rep [IsManifold 𝓘(ℂ) ω R] {V : (R → ℂ → ℂ) → ℂ} (hV : V ∈ zSpace R)
    (h : ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P) :
    ∃ g : ℕ → ℂ → ℂ,
      (∀ i, AEStronglyMeasurable (g i) (volume.restrict (chartAt ℂ (h.choose i) '' h.choose_spec.choose i))) ∧
      (∀ i, ∀ᵐ z ∂(volume.restrict (chartAt ℂ (h.choose i) '' h.choose_spec.choose i)),
        ‖g i z‖ ≤ dualNormOn (integrableHolQDSet R) quadDiffNorm V) ∧
      ∀ φ ∈ integrableHolQDSet R,
        V φ = ∑' i, ∫ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i, φ (h.choose i) z * g i z := by
  classical
  obtain ⟨S, E, hSm, hadd, hsmul, hnorm, hrep⟩ := gl31_model h.choose_spec.choose_spec
  obtain ⟨hVadd, hVsmul, C, hC⟩ := hV
  set D := dualNormOn (integrableHolQDSet R) quadDiffNorm V
  have hD0 : 0 ≤ D := Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hEn : ∀ φ ∈ integrableHolQDSet R, quadDiffNorm φ = ∫⁻ w in S, ‖E φ w‖ₑ := fun φ hφ =>
    (hnorm φ hφ.1).2.symm
  have hE0 : E 0 = 0 := by
    have e := hsmul 0 0
    rwa [zero_smul, zero_smul] at e
  have hsub : ∀ φ ψ, E (φ - ψ) = E φ - E ψ := fun φ ψ => by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ, hadd, hsmul, neg_one_smul, ← sub_eq_add_neg]
  -- `A(R)` is closed under the linear operations
  have hAadd : ∀ φ ∈ integrableHolQDSet R, ∀ ψ ∈ integrableHolQDSet R, φ + ψ ∈ integrableHolQDSet R := by
    intro φ hφ ψ hψ
    have hm := (holQuadDiffSubmodule R).add_mem hφ.1 hψ.1
    refine ⟨hm, ?_⟩
    rw [← (hnorm _ hm).2, hadd]
    calc ∫⁻ w in S, ‖(E φ + E ψ) w‖ₑ ≤ ∫⁻ w in S, (‖E φ w‖ₑ + ‖E ψ w‖ₑ) :=
          lintegral_mono fun w => enorm_add_le _ _
      _ = (∫⁻ w in S, ‖E φ w‖ₑ) + ∫⁻ w in S, ‖E ψ w‖ₑ := lintegral_add_left' (hnorm φ hφ.1).1.enorm _
      _ < ⊤ := by
          rw [(hnorm φ hφ.1).2, (hnorm ψ hψ.1).2]
          exact ENNReal.add_lt_top.2 ⟨hφ.2, hψ.2⟩
  have hAsmul : ∀ c : ℂ, ∀ φ ∈ integrableHolQDSet R, c • φ ∈ integrableHolQDSet R := by
    intro c φ hφ
    have hm := (holQuadDiffSubmodule R).smul_mem c hφ.1
    refine ⟨hm, ?_⟩
    rw [← (hnorm _ hm).2, hsmul]
    simp only [Pi.smul_apply, smul_eq_mul, enorm_mul]
    rw [lintegral_const_mul' _ _ enorm_ne_top, (hnorm φ hφ.1).2]
    exact ENNReal.mul_lt_top enorm_lt_top hφ.2
  have harea : ∀ φ ∈ integrableHolQDSet R, phiArea (E φ) S = quadDiffNorm φ := by
    intro φ hφ
    rw [hEn φ hφ]
    show ∫⁻ z in S, ENNReal.ofReal ‖E φ z‖ = _
    simp only [ofReal_norm]
  -- `V` is well defined on the image `E(A(R))`: `‖φ − ψ‖ = ∫_S |Eφ − Eψ|`
  have hwd : ∀ φ ∈ integrableHolQDSet R, ∀ ψ ∈ integrableHolQDSet R, E φ = E ψ → V φ = V ψ := by
    intro φ hφ ψ hψ he
    have hmem : φ - ψ ∈ integrableHolQDSet R := by
      rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ]
      exact hAadd φ hφ _ (hAsmul _ ψ hψ)
    have h0 : quadDiffNorm (φ - ψ) = 0 := by
      rw [hEn _ hmem, hsub, he, sub_self]
      simp
    have hV0 : V (φ - ψ) = 0 := by
      have e := hC _ hmem
      rw [h0, ENNReal.toReal_zero, mul_zero] at e
      exact norm_le_zero_iff.1 e
    rw [← sub_add_cancel φ ψ, hVadd _ hmem _ hψ, hV0, zero_add]
  obtain ⟨V', hV'def⟩ : ∃ V' : (ℂ → ℂ) → ℂ, V' = fun f =>
      if hf : ∃ φ ∈ integrableHolQDSet R, E φ = f then V hf.choose else 0 := ⟨_, rfl⟩
  have hV' : ∀ φ ∈ integrableHolQDSet R, V' (E φ) = V φ := by
    intro φ hφ
    have hex : ∃ ψ ∈ integrableHolQDSet R, E ψ = E φ := ⟨φ, hφ, rfl⟩
    simp only [hV'def]
    rw [dite_eq_left hex]
    exact hwd _ hex.choose_spec.1 _ hφ hex.choose_spec.2
  -- Hahn–Banach on `L¹(S)` (`gl3_dual_repr`) for `V′` on `E(A(R))`
  have hA'int : ∀ f ∈ E '' integrableHolQDSet R, IntegrableOn f S := by
    rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨(hnorm φ hφ.1).1, ?_⟩
    show ∫⁻ w, ‖E φ w‖ₑ ∂(volume.restrict S) < ⊤
    rw [(hnorm φ hφ.1).2]
    exact hφ.2
  have hA'0 : (0 : ℂ → ℂ) ∈ E '' integrableHolQDSet R := by
    refine ⟨0, ⟨(holQuadDiffSubmodule R).zero_mem, ?_⟩, hE0⟩
    rw [← (hnorm 0 (holQuadDiffSubmodule R).zero_mem).2, hE0]
    simp
  have hA'add : ∀ f ∈ E '' integrableHolQDSet R, ∀ f' ∈ E '' integrableHolQDSet R,
      f + f' ∈ E '' integrableHolQDSet R := by
    rintro _ ⟨φ, hφ, rfl⟩ _ ⟨ψ, hψ, rfl⟩
    exact ⟨φ + ψ, hAadd φ hφ ψ hψ, hadd φ ψ⟩
  have hA'smul : ∀ c : ℂ, ∀ f ∈ E '' integrableHolQDSet R, c • f ∈ E '' integrableHolQDSet R := by
    rintro c _ ⟨φ, hφ, rfl⟩
    exact ⟨c • φ, hAsmul c φ hφ, hsmul c φ⟩
  have hV'b : IsBoundedFunctionalOn (E '' integrableHolQDSet R) (fun f => phiArea f S) V' := by
    refine ⟨?_, ?_, C, ?_⟩
    · rintro _ ⟨φ, hφ, rfl⟩ _ ⟨ψ, hψ, rfl⟩
      rw [← hadd, hV' _ (hAadd φ hφ ψ hψ), hV' φ hφ, hV' ψ hψ, hVadd φ hφ ψ hψ]
    · rintro c _ ⟨φ, hφ, rfl⟩
      rw [← hsmul, hV' _ (hAsmul c φ hφ), hV' φ hφ, hVsmul c φ hφ]
    · rintro _ ⟨φ, hφ, rfl⟩
      show ‖V' (E φ)‖ ≤ C * (phiArea (E φ) S).toReal
      rw [hV' φ hφ, harea φ hφ]
      exact hC φ hφ
  obtain ⟨ν, hνm, hνb, hνrep⟩ := gl3_dual_repr hSm hA'int hA'0 hA'add hA'smul hV'b
  -- the dual norm of `V′` on the image is at most `‖V‖`
  have hle : dualNormOn (E '' integrableHolQDSet R) (fun f => phiArea f S) V' ≤ D := by
    refine Real.iSup_le (fun f => Real.iSup_le (fun hf => ?_) hD0) hD0
    obtain ⟨⟨φ, hφ, rfl⟩, h1⟩ := hf
    rw [hV' φ hφ]
    have hφ1 : quadDiffNorm φ = 1 := by
      rw [← harea φ hφ]
      exact h1
    have hbdd : BddAbove (range fun a => ⨆ (_ : a ∈ integrableHolQDSet R ∧ quadDiffNorm a = 1), ‖V a‖) := by
      refine ⟨max C 0, ?_⟩
      rintro _ ⟨χ, rfl⟩
      refine Real.iSup_le (fun hχ => ?_) (le_max_right _ _)
      have e := hC χ hχ.1
      rw [hχ.2, ENNReal.toReal_one, mul_one] at e
      exact e.trans (le_max_left _ _)
    calc ‖V φ‖ = ⨆ (_ : φ ∈ integrableHolQDSet R ∧ quadDiffNorm φ = 1), ‖V φ‖ :=
          (ciSup_pos (f := fun _ => ‖V φ‖) ⟨hφ, hφ1⟩).symm
      _ ≤ D := le_ciSup hbdd φ
  -- pull `ν` back to the charts of the chosen partition
  obtain ⟨g, hgm, hgb, hgrep⟩ := hrep ν hνm D (by
    filter_upwards [hνb] with z hz
    exact hz.trans hle)
  refine ⟨g, hgm, hgb, fun φ hφ => ?_⟩
  rw [← hV' φ hφ, hνrep _ ⟨φ, hφ, rfl⟩, hgrep φ hφ]

/-- **Theorem 2** (§3.1, l. 2099), second part. The pairing induces an isometric isomorphism of `A(R)*` onto
`L∞(R)/N`, `N` the annihilator of `A(R)`: every `V ∈ Z(R)` is represented by some `μ ∈ L∞(R)`, and `‖V‖` is the
quotient norm `min ‖μ‖∞` over the representatives. -/
theorem thm3_2_b [IsManifold 𝓘(ℂ) ω R] {V : (R → ℂ → ℂ) → ℂ} (hV : V ∈ zSpace R) :
    ∃ μ ∈ beltramiSpace R, (∀ φ ∈ integrableHolQDSet R, V φ = pairingRS φ μ) ∧
      beltramiNormRS μ = ENNReal.ofReal (dualNormOn (integrableHolQDSet R) quadDiffNorm V) ∧
      ∀ ν ∈ beltramiSpace R, (∀ φ ∈ integrableHolQDSet R, V φ = pairingRS φ ν) →
        ENNReal.ofReal (dualNormOn (integrableHolQDSet R) quadDiffNorm V) ≤ beltramiNormRS ν := by
  have hD0 : 0 ≤ dualNormOn (integrableHolQDSet R) quadDiffNorm V :=
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
  -- the dual norm is at most the norm of every representative (`gl31_pairingRS_le`)
  have hlow : ∀ ν ∈ beltramiSpace R, (∀ φ ∈ integrableHolQDSet R, V φ = pairingRS φ ν) →
      ENNReal.ofReal (dualNormOn (integrableHolQDSet R) quadDiffNorm V) ≤ beltramiNormRS ν := by
    intro ν hν hrep
    by_cases hfin : beltramiNormRS ν = ⊤
    · rw [hfin]
      exact le_top
    rw [← ENNReal.ofReal_toReal hfin]
    refine ENNReal.ofReal_le_ofReal (Real.iSup_le (fun φ => Real.iSup_le (fun hφ => ?_) ENNReal.toReal_nonneg)
      ENNReal.toReal_nonneg)
    rw [hrep φ hφ.1]
    calc ‖pairingRS φ ν‖ ≤ (beltramiNormRS ν).toReal * (quadDiffNorm φ).toReal := gl31_pairingRS_le hφ.1 hν
      _ = (beltramiNormRS ν).toReal := by rw [hφ.2, ENNReal.toReal_one, mul_one]
  by_cases h : ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P
  · -- represent `V` on the partition chosen in `pairingRS`, then extend to a Beltrami differential
    obtain ⟨g, hgm, hgb, hrep⟩ := gl31_dual_rep hV h
    obtain ⟨μ, hμ, hμg, hμn⟩ := gl31_beltrami_extend h.choose_spec.choose_spec g hD0 hgm hgb
    have hpair : ∀ φ ∈ integrableHolQDSet R, V φ = pairingRS φ μ := by
      intro φ hφ
      rw [hrep φ hφ, pairingRS, dite_eq_left h]
      refine tsum_congr fun i => setIntegral_congr_fun (h.choose_spec.choose_spec.1 i).2 fun z hz => ?_
      rw [hμg i z hz]
    exact ⟨μ, hμ, hpair, le_antisymm hμn (hlow μ hμ hpair), hlow⟩
  · -- no chart partition: `A(R) = ∅` (every norm is `⊤`), the dual norm is `0` and `μ = 0` works
    have hA : ∀ φ, φ ∉ integrableHolQDSet R := fun φ hφ => h (gl31_exists_partition_of_ne_top hφ.2.ne)
    have hD : dualNormOn (integrableHolQDSet R) quadDiffNorm V = 0 := by
      refine le_antisymm (Real.iSup_le (fun φ => Real.iSup_le (fun hφ => absurd hφ.1 (hA φ)) le_rfl) le_rfl) hD0
    have h0 : (0 : R → ℂ → ℂ) ∈ beltramiSpace R := by
      refine ⟨0, fun x y => ae_of_all _ fun z => ?_, fun x => ⟨aestronglyMeasurable_const, ae_of_all _ fun z => ?_⟩⟩
      · simp
      · simp
    have hn0 : beltramiNormRS (0 : R → ℂ → ℂ) = 0 := by
      refine le_antisymm (iSup_le fun x => ?_) bot_le
      simp
    refine ⟨0, h0, fun φ hφ => absurd hφ (hA φ), ?_, hlow⟩
    rw [hn0, hD, ENNReal.ofReal_zero]

/-- **Definition 1** (§3.1, l. 2122). A degenerating sequence in `A(R)`: `‖φₙ‖ = 1` and `φₙ → 0` uniformly on compact
subsets of `R` (in every chart). -/
def IsDegeneratingSeq (φ : ℕ → R → ℂ → ℂ) : Prop :=
  (∀ n, φ n ∈ integrableHolQDSet R ∧ quadDiffNorm (φ n) = 1) ∧
    ∀ x : R, TendstoLocallyUniformlyOn (fun n => φ n x) 0 atTop (chartAt ℂ x).target

/-- Helper (B-SURF II, §3.1, §3.3). A degenerating sequence has vanishing mass on every compact set, `∬_C |φₙ| → 0`: on
a chart partition of which only finitely many pieces meet `C`, each inside a chart ball whose closed ball lies in the
chart target (`gl31_exists_chartPartition_cpt`), the convergence `φₙ → 0` is uniform. -/
theorem gl31_degenerating_cpt [IsManifold 𝓘(ℂ) ω R] {φ : ℕ → R → ℂ → ℂ} (hφ : IsDegeneratingSeq φ) {C : Set R}
    (hC : IsCompact C) :
    Tendsto (fun n => LiZhongQC.surfaceIntegral (φ n)
      (fun y z => C.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z))) atTop (𝓝 0) := by
  -- the norms are finite, so `R` has a chart partition: it is second countable and nonempty
  obtain ⟨x₀, P₀, hP₀⟩ := gl31_exists_partition_of_ne_top (hφ.1 0).1.2.ne
  have := gl31_secondCountable_of_partition hP₀
  have : Nonempty R := ⟨x₀ 0⟩
  obtain ⟨x, P, r, N, hP, hr, hN⟩ := gl31_exists_chartPartition_cpt hC
  -- `∬_C |φₙ| = Σ_{i < N} ∬_{φ_{xᵢ}(Pᵢ)} 𝟙_C |φₙ|` (partition independence; the pieces `i ≥ N` avoid `C`)
  have hsum : ∀ n, LiZhongQC.surfaceIntegral (φ n)
      (fun y z => C.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z)) =
      ∑ i ∈ Finset.range N, ∫⁻ z in chartAt ℂ (x i) '' P i,
        C.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ (x i)).symm z) * ENNReal.ofReal ‖φ n (x i) z‖ := by
    intro n
    rw [LiZhongQC.s26v_surfaceIntegral_eq_tsum (hφ.1 n).1.1 _ hP]
    refine tsum_eq_sum fun i hi => ?_
    have hiN : N ≤ i := by simpa using hi
    calc _ = ∫⁻ _ in chartAt ℂ (x i) '' P i, (0 : ℝ≥0∞) := by
          refine setLIntegral_congr_fun (hP.1 i).2 fun z hz => ?_
          obtain ⟨y, hy, rfl⟩ := hz
          rw [(chartAt ℂ (x i)).left_inv ((hP.1 i).1 hy),
            indicator_of_notMem (Set.disjoint_left.1 (hN i hiN) hy), zero_mul]
      _ = 0 := lintegral_zero
  -- each of the finitely many terms tends to `0`: `φₙ → 0` uniformly on the closed chart ball `K ⊇ φ_{xᵢ}(Pᵢ)`
  have hlim : ∀ i, Tendsto (fun n => ∫⁻ z in chartAt ℂ (x i) '' P i,
      C.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ (x i)).symm z) * ENNReal.ofReal ‖φ n (x i) z‖) atTop (𝓝 0) := by
    intro i
    have hK : IsCompact (closedBall (chartAt ℂ (x i) (x i)) (r i)) := isCompact_closedBall _ _
    have hU := (tendstoLocallyUniformlyOn_iff_forall_isCompact (chartAt ℂ (x i)).open_target).1 (hφ.2 (x i))
      _ (hr i).2.2.1 hK
    rw [Metric.tendstoUniformlyOn_iff] at hU
    have hKfin : volume (closedBall (chartAt ℂ (x i) (x i)) (r i)) ≠ ⊤ := hK.measure_lt_top.ne
    refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
    rcases eq_or_ne ε ⊤ with rfl | hεt
    · exact Eventually.of_forall fun n => le_top
    set M := (volume (closedBall (chartAt ℂ (x i) (x i)) (r i))).toReal with hM
    have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
    have hε0 : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
    set δ : ℝ := ε.toReal / (M + 1) with hδ
    have hδ0 : 0 < δ := div_pos hε0 (by linarith)
    filter_upwards [hU δ hδ0] with n hn
    calc _ ≤ ∫⁻ _ in chartAt ℂ (x i) '' P i, ENNReal.ofReal δ := by
          refine lintegral_mono_ae ((ae_restrict_iff' (hP.1 i).2).2 (Eventually.of_forall fun z hz => ?_))
          have hzK : z ∈ closedBall (chartAt ℂ (x i) (x i)) (r i) := ball_subset_closedBall ((hr i).2.2.2 hz)
          have h1 := hn z hzK
          rw [Pi.zero_apply, dist_zero_left] at h1
          calc _ ≤ 1 * ENNReal.ofReal ‖φ n (x i) z‖ :=
                mul_le_mul_left (Set.indicator_apply_le' (s := C) (f := fun _ => (1 : ℝ≥0∞))
                  (fun _ => le_rfl) fun _ => zero_le_one) _
            _ ≤ ENNReal.ofReal δ := by
                rw [one_mul]
                exact ENNReal.ofReal_le_ofReal h1.le
      _ ≤ ∫⁻ _ in closedBall (chartAt ℂ (x i) (x i)) (r i), ENNReal.ofReal δ :=
          lintegral_mono_set ((hr i).2.2.2.trans ball_subset_closedBall)
      _ = ENNReal.ofReal δ * volume (closedBall (chartAt ℂ (x i) (x i)) (r i)) := setLIntegral_const _ _
      _ ≤ ε := by
          rw [← ENNReal.ofReal_toReal hKfin, ← hM, ← ENNReal.ofReal_mul hδ0.le, ← ENNReal.ofReal_toReal hεt]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by linarith), mul_add, mul_one]
          linarith
  rw [show (fun n => LiZhongQC.surfaceIntegral (φ n)
      (fun y z => C.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z))) = fun n =>
      ∑ i ∈ Finset.range N, ∫⁻ z in chartAt ℂ (x i) '' P i,
        C.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ (x i)).symm z) * ENNReal.ofReal ‖φ n (x i) z‖ from funext hsum]
  simpa using tendsto_finsetSum (Finset.range N) fun i _ => hlim i

/-- Helper for **Theorem 1** part (§3.1, l. 2124). If `A(R)` is finite dimensional, finitely many point evaluations
`φ ↦ φ_y(z)` separate it: the kernels of the evaluations at all points have intersection `0`, and a decreasing chain of
subspaces of a finite dimensional space is stationary. -/
theorem gl31_eval_separates [IsManifold 𝓘(ℂ) ω R]
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (integrableHolQDSet R))) :
    ∃ J : Finset (R × ℂ), ∀ φ ∈ integrableHolQDSet R, (∀ p ∈ J, φ p.1 p.2 = 0) → φ = 0 := by
  classical
  set V := Submodule.span ℂ (integrableHolQDSet R) with hV
  let ev : R × ℂ → V →ₗ[ℂ] ℂ := fun p => (LinearMap.proj p.2).comp ((LinearMap.proj p.1).comp V.subtype)
  have hev : ∀ p v, ev p v = (v : R → ℂ → ℂ) p.1 p.2 := fun p v => rfl
  let K : Finset (R × ℂ) → Submodule ℂ V := fun J => ⨅ p ∈ J, LinearMap.ker (ev p)
  haveI : IsArtinian ℂ V := inferInstance
  obtain ⟨_, ⟨J, rfl⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Submodule ℂ V)) (Set.range K)
    ⟨K ∅, ⟨∅, rfl⟩⟩
  refine ⟨J, fun φ hφ hz => ?_⟩
  have hφV : φ ∈ V := Submodule.subset_span hφ
  have hKJ : (⟨φ, hφV⟩ : V) ∈ K J := by
    simp only [K, Submodule.mem_iInf, LinearMap.mem_ker]
    exact fun p hp => by rw [hev]; exact hz p hp
  have hall : ∀ p : R × ℂ, (⟨φ, hφV⟩ : V) ∈ LinearMap.ker (ev p) := by
    intro p
    have hle : K (insert p J) ≤ K J := by
      simp only [K]
      exact iInf_mono' fun q => ⟨q, iInf_mono' fun hq => ⟨Finset.mem_insert_of_mem hq, le_rfl⟩⟩
    have heq : K (insert p J) = K J := by
      by_contra hne
      exact hmin (K (insert p J)) ⟨insert p J, rfl⟩ (lt_of_le_of_ne hle hne)
    have hKp : K J ≤ LinearMap.ker (ev p) := by
      rw [← heq]
      simp only [K]
      exact iInf₂_le p (Finset.mem_insert_self p J)
    exact hKp hKJ
  funext y z
  have := hall (y, z)
  rw [LinearMap.mem_ker, hev] at this
  exact this

/-- Helper for **Theorem 1** part (§3.1, l. 2124). Norm equivalence on the finite dimensional `A(R)`: if finitely many
evaluations `J` separate `A(R)`, then `‖φ‖ ≤ C Σ_{p ∈ J} |φ_p|` (the right-hand side is a norm, and `‖·‖` is a norm by
`gl31_norm_eq_zero`, `gl31_qdn_add_le` and `gl31_quadDiffNorm_smul`; coordinates in a basis). -/
theorem gl31_fd_estimate [IsManifold 𝓘(ℂ) ω R]
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (integrableHolQDSet R))) {J : Finset (R × ℂ)}
    (hJ : ∀ φ ∈ integrableHolQDSet R, (∀ p ∈ J, φ p.1 p.2 = 0) → φ = 0) :
    ∃ C : ℝ, ∀ φ ∈ integrableHolQDSet R, (quadDiffNorm φ).toReal ≤ C * ∑ p ∈ J, ‖φ p.1 p.2‖ := by
  classical
  by_cases hne : ∃ a₀, a₀ ∈ integrableHolQDSet R
  swap
  · exact ⟨0, fun φ hφ => absurd ⟨φ, hφ⟩ hne⟩
  obtain ⟨a₀, ha₀⟩ := hne
  set V := Submodule.span ℂ (integrableHolQDSet R) with hV
  -- closure of `A(R)` under the linear operations
  have hsmulA : ∀ (c : ℂ) a, a ∈ integrableHolQDSet R → c • a ∈ integrableHolQDSet R := fun c a ha =>
    ⟨(holQuadDiffSubmodule R).smul_mem c ha.1, by
      rw [gl31_quadDiffNorm_smul ha c]
      exact ENNReal.mul_lt_top enorm_lt_top ha.2⟩
  have h0A : (0 : R → ℂ → ℂ) ∈ integrableHolQDSet R := by
    have := hsmulA 0 a₀ ha₀
    rwa [zero_smul] at this
  have hVA : ∀ v ∈ V, v ∈ integrableHolQDSet R := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem a ha => exact ha
    | zero => exact h0A
    | add a b _ _ ha hb => exact gl31_add_mem ha hb
    | smul c a _ ha => exact hsmulA c a ha
  -- the evaluation map at the points of `J`
  let ev : V →ₗ[ℂ] (↥J → ℂ) :=
    LinearMap.pi fun p => (LinearMap.proj p.1.2).comp ((LinearMap.proj p.1.1).comp V.subtype)
  have hev : ∀ v p, ev v p = (v : R → ℂ → ℂ) p.1.1 p.1.2 := fun v p => rfl
  have hinj : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hz : ∀ p ∈ J, (v : R → ℂ → ℂ) p.1 p.2 = 0 := fun p hp => by
      have := congrFun hv ⟨p, hp⟩
      rwa [hev] at this
    exact Subtype.ext (hJ v (hVA v v.2) hz)
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective ev hinj
  set u : ↥J → R → ℂ → ℂ := fun p => ((L (Pi.single p 1) : V) : R → ℂ → ℂ) with hu
  have huA : ∀ p, u p ∈ integrableHolQDSet R := fun p => hVA _ (L (Pi.single p 1)).2
  -- laws and measurability of holomorphic differentials, for the triangle inequality
  have hlawH : ∀ f : R → ℂ → ℂ, f ∈ holQuadDiffSubmodule R → IsDiffFamilyAE 2 0 f := by
    intro f hf a b
    have hset : MeasurableSet ((chartAt ℂ b).target ∩ (chartAt ℂ b).symm ⁻¹' (chartAt ℂ a).source) :=
      ((chartAt ℂ b).isOpen_inter_preimage_symm (chartAt ℂ a).open_source).measurableSet
    filter_upwards [ae_restrict_mem hset] with z hz
    exact hf.1.2 a b z hz.1 hz.2
  have hmH : ∀ f : R → ℂ → ℂ, f ∈ holQuadDiffSubmodule R → ∀ a : R,
      AEStronglyMeasurable (f a) (volume.restrict (chartAt ℂ a).target) := fun f hf a =>
    ((hf.2 a).continuousOn).aestronglyMeasurable (chartAt ℂ a).open_target.measurableSet
  -- the triangle inequality for finite combinations
  have key : ∀ (s : Finset ↥J) (c : ↥J → ℂ), (∑ p ∈ s, c p • u p) ∈ integrableHolQDSet R ∧
      quadDiffNorm (∑ p ∈ s, c p • u p) ≤ ∑ p ∈ s, ENNReal.ofReal ‖c p‖ * quadDiffNorm (u p) := by
    intro s c
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨by simpa using h0A, ?_⟩
      have h := gl31_quadDiffNorm_smul ha₀ 0
      rw [zero_smul] at h
      simp [h]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hsa := hsmulA (c a) (u a) (huA a)
      refine ⟨gl31_add_mem hsa ih.1, ?_⟩
      refine (gl31_qdn_add_le (hlawH _ hsa.1) (hlawH _ ih.1.1) (hmH _ hsa.1) (hmH _ ih.1.1)).trans ?_
      rw [gl31_quadDiffNorm_smul (huA a), ← ofReal_norm]
      exact add_le_add le_rfl ih.2
  -- `φ = Σ φ(p) u_p`
  have hrep : ∀ φ ∈ integrableHolQDSet R, φ = ∑ p : ↥J, (φ p.1.1 p.1.2) • u p := by
    intro φ hφ
    have hφV : φ ∈ V := Submodule.subset_span hφ
    have h1 : (⟨φ, hφV⟩ : V) = L (ev ⟨φ, hφV⟩) := by
      have := LinearMap.congr_fun hL ⟨φ, hφV⟩
      exact this.symm
    have h2 : ev ⟨φ, hφV⟩ = ∑ p : ↥J, (φ p.1.1 p.1.2) • Pi.single p (1 : ℂ) := by
      funext q
      simp [hev, Finset.sum_apply, Pi.single_apply]
    have h3 : (⟨φ, hφV⟩ : V) = ∑ p : ↥J, (φ p.1.1 p.1.2) • L (Pi.single p (1 : ℂ)) := by
      rw [h1, h2, map_sum]
      simp only [map_smul]
    have := congrArg (fun v : V => (v : R → ℂ → ℂ)) h3
    simpa [hu] using this
  refine ⟨∑ p : ↥J, (quadDiffNorm (u p)).toReal, fun φ hφ => ?_⟩
  set C := ∑ p : ↥J, (quadDiffNorm (u p)).toReal with hC
  have hq : ∀ p, (quadDiffNorm (u p)).toReal ≤ C := fun p =>
    Finset.single_le_sum (f := fun p => (quadDiffNorm (u p)).toReal) (fun q _ => ENNReal.toReal_nonneg)
      (Finset.mem_univ p)
  have hk := (key Finset.univ fun p => φ p.1.1 p.1.2).2
  rw [← hrep φ hφ] at hk
  have hfin : (∑ p : ↥J, ENNReal.ofReal ‖φ p.1.1 p.1.2‖ * quadDiffNorm (u p)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun p _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (huA p).2.ne
  calc (quadDiffNorm φ).toReal ≤ (∑ p : ↥J, ENNReal.ofReal ‖φ p.1.1 p.1.2‖ * quadDiffNorm (u p)).toReal :=
        ENNReal.toReal_mono hfin hk
    _ = ∑ p : ↥J, ‖φ p.1.1 p.1.2‖ * (quadDiffNorm (u p)).toReal := by
        rw [ENNReal.toReal_sum fun p _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (huA p).2.ne]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
    _ ≤ ∑ p : ↥J, ‖φ p.1.1 p.1.2‖ * C :=
        Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hq p) (norm_nonneg _)
    _ = C * ∑ p ∈ J, ‖φ p.1 p.2‖ := by
        rw [← Finset.sum_mul, mul_comm]
        congr 1
        exact Finset.sum_coe_sort J fun p => ‖φ p.1 p.2‖

/-- **Unlabelled** (§3.1, l. 2124). If `A(R)` is finite dimensional there are no degenerating sequences.
[CORRECTION/modelling] The binder `[IsManifold 𝓘(ℂ) ω R]` (the holomorphic atlas of `R`) is added: the proof needs the
chart transitions to be holomorphic, and the printed statement assumes `R` is a Riemann surface. -/
theorem para3_1_finite_dim [IsManifold 𝓘(ℂ) ω R]
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (integrableHolQDSet R))) :
    ¬ ∃ φ : ℕ → R → ℂ → ℂ, IsDegeneratingSeq φ := by
  classical
  rintro ⟨φ, hφ⟩
  obtain ⟨J, hJ⟩ := gl31_eval_separates hfin
  obtain ⟨C, hC⟩ := gl31_fd_estimate hfin hJ
  have hs : Tendsto (fun n => ∑ p ∈ J, ‖φ n p.1 p.2‖) atTop (𝓝 0) := by
    have h : Tendsto (fun n => ∑ p ∈ J, ‖φ n p.1 p.2‖) atTop (𝓝 (∑ p ∈ J, (0 : ℝ))) :=
      tendsto_finset_sum _ fun p _ => by
        by_cases hz : p.2 ∈ (chartAt ℂ p.1).target
        · have := ((hφ.2 p.1).tendsto_at hz).norm
          simpa using this
        · have h0 : ∀ n, φ n p.1 p.2 = 0 := fun n => (hφ.1 n).1.1.1.1 _ _ hz
          simp [h0]
    simpa using h
  have h1 : ∀ n, (1 : ℝ) ≤ C * ∑ p ∈ J, ‖φ n p.1 p.2‖ := fun n => by
    have := hC (φ n) (hφ.1 n).1
    rwa [(hφ.1 n).2, ENNReal.toReal_one] at this
  have h2 := ge_of_tendsto' (hs.const_mul C) h1
  rw [mul_zero] at h2
  linarith

/-- Helper for **Theorem 3** (§3.1, l. 2126). When `A(R)` is infinite dimensional it contains a bounded sequence with
pairwise distances `≥ 1` (Riesz: `exists_seq_norm_le_one_le_norm_sub` in the infinite dimensional image of `A(R)` in
the `L¹` model of `gl31_model`, an isometric injection by `gl31_norm_eq_zero`). -/
theorem gl31_separated_seq [IsManifold 𝓘(ℂ) ω R]
    (hinf : ¬ FiniteDimensional ℂ (Submodule.span ℂ (integrableHolQDSet R))) :
    ∃ (C : ℝ≥0∞) (φ : ℕ → R → ℂ → ℂ), C ≠ ⊤ ∧ (∀ n, φ n ∈ integrableHolQDSet R ∧ quadDiffNorm (φ n) ≤ C) ∧
      Pairwise fun m n => 1 ≤ quadDiffNorm (φ m - φ n) := by
  -- `A(R)` is nonempty (its span is not `⊥`), so `R` has a chart partition
  obtain ⟨φ₀, hφ₀⟩ : (integrableHolQDSet R).Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Submodule.span_empty] at hinf
    exact hinf inferInstance
  obtain ⟨x, P, hP⟩ := gl31_exists_partition_of_ne_top hφ₀.2.ne
  obtain ⟨S, E, -, hadd, hsmul, hnorm, -⟩ := gl31_model hP
  have hsmulA : ∀ (c : ℂ) {ψ : R → ℂ → ℂ}, ψ ∈ integrableHolQDSet R → c • ψ ∈ integrableHolQDSet R :=
    fun c ψ hψ => ⟨(holQuadDiffSubmodule R).smul_mem c hψ.1, by
      rw [gl31_quadDiffNorm_smul hψ]
      exact ENNReal.mul_lt_top enorm_lt_top hψ.2⟩
  have h0A : (0 : R → ℂ → ℂ) ∈ integrableHolQDSet R := by
    have h := hsmulA 0 hφ₀
    rwa [zero_smul] at h
  -- `A(R)` is a submodule, equal to its span
  let W : Submodule ℂ (R → ℂ → ℂ) :=
    { carrier := integrableHolQDSet R
      add_mem' := fun ha hb => gl31_add_mem ha hb
      zero_mem' := h0A
      smul_mem' := fun c _ hψ => hsmulA c hψ }
  have hspan : Submodule.span ℂ (integrableHolQDSet R) = W := Submodule.span_eq W
  rw [hspan] at hinf
  -- the isometric injection into `L¹(vol|S)`
  have hmem : ∀ φ ∈ integrableHolQDSet R, MemLp (E φ) 1 (volume.restrict S) := fun φ hφ =>
    memLp_one_iff_integrable.2 ⟨(hnorm φ hφ.1).1, by
      show ∫⁻ w, ‖E φ w‖ₑ ∂(volume.restrict S) < ⊤
      rw [(hnorm φ hφ.1).2]
      exact hφ.2⟩
  let T : W →ₗ[ℂ] Lp ℂ 1 (volume.restrict S) :=
    { toFun := fun φ => (hmem φ.1 φ.2).toLp (E φ.1)
      map_add' := fun φ ψ => by
        rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
        exact Filter.EventuallyEq.of_eq (hadd φ.1 ψ.1)
      map_smul' := fun c φ => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
        exact Filter.EventuallyEq.of_eq (hsmul c φ.1) }
  have hTn : ∀ φ : W, ENNReal.ofReal ‖T φ‖ = quadDiffNorm (φ : R → ℂ → ℂ) := by
    intro φ
    show ENNReal.ofReal ‖(hmem φ.1 φ.2).toLp (E φ.1)‖ = _
    rw [Lp.norm_toLp, ENNReal.ofReal_toReal (hmem φ.1 φ.2).eLpNorm_ne_top,
      eLpNorm_one_eq_lintegral_enorm (hnorm φ.1 φ.2.1).1, (hnorm φ.1 φ.2.1).2]
  have hinj : Function.Injective T := (injective_iff_map_eq_zero T).2 fun φ hφ0 => by
    have h := hTn φ
    rw [hφ0, norm_zero, ENNReal.ofReal_zero] at h
    exact Subtype.ext (gl31_norm_eq_zero φ.2.1 h.symm)
  -- the image is infinite dimensional: Riesz gives a bounded sequence with pairwise distances `≥ 1`
  have hinf' : ¬ FiniteDimensional ℂ (LinearMap.range T) := fun hfin =>
    hinf (LinearEquiv.finiteDimensional (LinearEquiv.ofInjective T hinj).symm)
  obtain ⟨R₀, f, -, hfR, hfsep⟩ := exists_seq_norm_le_one_le_norm_sub hinf'
  have hTe : ∀ v, T ((LinearEquiv.ofInjective T hinj).symm v) = (v : Lp ℂ 1 (volume.restrict S)) := fun v =>
    LinearEquiv.ofInjective_symm_apply (f := T) (h := hinj) v
  refine ⟨ENNReal.ofReal R₀, fun n => ((LinearEquiv.ofInjective T hinj).symm (f n) : R → ℂ → ℂ),
    ENNReal.ofReal_ne_top, fun n => ⟨((LinearEquiv.ofInjective T hinj).symm (f n)).2, ?_⟩, fun m n hmn => ?_⟩
  · rw [← hTn, hTe]
    exact ENNReal.ofReal_le_ofReal (hfR n)
  · have hsub := hTn ((LinearEquiv.ofInjective T hinj).symm (f m) - (LinearEquiv.ofInjective T hinj).symm (f n))
    rw [map_sub, hTe, hTe] at hsub
    show 1 ≤ quadDiffNorm (((LinearEquiv.ofInjective T hinj).symm (f m) -
      (LinearEquiv.ofInjective T hinj).symm (f n) : W) : R → ℂ → ℂ)
    rw [← hsub]
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hfsep hmn)

/-- **Theorem 3** (§3.1, l. 2126). Whenever `A(R)` is infinite dimensional, it contains degenerating sequences. -/
theorem thm3_3 [IsManifold 𝓘(ℂ) ω R] (hinf : ¬ FiniteDimensional ℂ (Submodule.span ℂ (integrableHolQDSet R))) :
    ∃ φ : ℕ → R → ℂ → ℂ, IsDegeneratingSeq φ := by
  -- a bounded separated sequence (Riesz), a subsequence converging in every chart (Montel), and the normalized
  -- consecutive differences
  obtain ⟨C, φ, hC, hφ, hsep⟩ := gl31_separated_seq hinf
  obtain ⟨σ, hσ, g, hg⟩ := gl31_montel (fun n => (hφ n).1.1) hC fun n => (hφ n).2
  have hsmulA : ∀ (c : ℂ) {ψ : R → ℂ → ℂ}, ψ ∈ integrableHolQDSet R → c • ψ ∈ integrableHolQDSet R :=
    fun c ψ hψ => ⟨(holQuadDiffSubmodule R).smul_mem c hψ.1, by
      rw [gl31_quadDiffNorm_smul hψ]
      exact ENNReal.mul_lt_top enorm_lt_top hψ.2⟩
  have hψA : ∀ k, φ (σ (k + 1)) - φ (σ k) ∈ integrableHolQDSet R := fun k => by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (φ (σ k))]
    exact gl31_add_mem (hφ _).1 (hsmulA _ (hφ _).1)
  have hψ1 : ∀ k, 1 ≤ (quadDiffNorm (φ (σ (k + 1)) - φ (σ k))).toReal := fun k => by
    have h := ENNReal.toReal_mono (hψA k).2.ne (hsep (hσ.injective.ne (Nat.succ_ne_self k)))
    rwa [ENNReal.toReal_one] at h
  refine ⟨fun k => (((quadDiffNorm (φ (σ (k + 1)) - φ (σ k))).toReal)⁻¹ : ℂ) • (φ (σ (k + 1)) - φ (σ k)),
    fun k => ⟨hsmulA _ (hψA k), ?_⟩, fun y => ?_⟩
  · -- norm `1`
    have hpos : 0 < (quadDiffNorm (φ (σ (k + 1)) - φ (σ k))).toReal := lt_of_lt_of_le one_pos (hψ1 k)
    rw [gl31_quadDiffNorm_smul (hψA k), ← ofReal_norm, norm_inv, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    nth_rewrite 2 [← ENNReal.ofReal_toReal (hψA k).2.ne]
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hpos.le), inv_mul_cancel₀ hpos.ne', ENNReal.ofReal_one]
  · -- `→ 0` locally uniformly in every chart: the differences of a convergent sequence, scaled by at most `1`
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε w hw
    obtain ⟨u, hu, hev⟩ := Metric.tendstoLocallyUniformlyOn_iff.1 (hg y) (ε / 2) (half_pos hε) w hw
    refine ⟨u, hu, ?_⟩
    filter_upwards [hev, (tendsto_add_atTop_nat 1).eventually hev] with k hk hk1 v hv
    have hc : ‖(((quadDiffNorm (φ (σ (k + 1)) - φ (σ k))).toReal)⁻¹ : ℂ)‖ ≤ 1 := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact inv_le_one_of_one_le₀ (hψ1 k)
    rw [Pi.zero_apply, dist_zero_left]
    show ‖(((quadDiffNorm (φ (σ (k + 1)) - φ (σ k))).toReal)⁻¹ : ℂ) * (φ (σ (k + 1)) y v - φ (σ k) y v)‖ < ε
    calc _ = ‖(((quadDiffNorm (φ (σ (k + 1)) - φ (σ k))).toReal)⁻¹ : ℂ)‖ * ‖φ (σ (k + 1)) y v - φ (σ k) y v‖ :=
          norm_mul _ _
      _ ≤ ‖φ (σ (k + 1)) y v - φ (σ k) y v‖ := mul_le_of_le_one_left (norm_nonneg _) hc
      _ = dist (φ (σ (k + 1)) y v) (φ (σ k) y v) := (dist_eq_norm _ _).symm
      _ ≤ dist (g y v) (φ (σ (k + 1)) y v) + dist (g y v) (φ (σ k) y v) := dist_triangle_left _ _ _
      _ < ε := by linarith [hk v hv, hk1 v hv]

/-- **Definition** (§3.1, l. 2153–2157). The lift `φ̃(τ) = φ(p(τ)) p′(τ)²` of a quadratic differential to `ℍ` through
`p : ℍ → R` (computed in the chart at `p(τ)`; `0` off `ℍ`). -/
def liftQD (p : UpperHalfPlane → R) (φ : R → ℂ → ℂ) (w : ℂ) : ℂ :=
  if hw : 0 < w.im then
    φ (p ⟨w, hw⟩) (chartAt ℂ (p ⟨w, hw⟩) (p ⟨w, hw⟩)) *
      deriv (fun v => chartAt ℂ (p ⟨w, hw⟩) (p (UpperHalfPlane.ofComplex v))) w ^ 2
  else 0

open scoped Classical in
/-- **Definition** (§3.1, l. 2189). The lift `μ̃(τ) = μ(p(τ)) conj(p′(τ))/p′(τ)` of a Beltrami differential to `ℍ`
(`0` off `ℍ`), read in the charts of the chart partition chosen in `pairingRS` (the same `Classical.choose`; junk `0`
if there is none).
[CORRECTION] (leader -ea, ruling D1 on worker3's G1 scout, 2026-10-06): the coefficient was read in the chart at
`p(τ)` at the single point `p(τ)`. A Beltrami differential is determined only almost everywhere in each chart, so that
lift did not depend on `μ`, and `para3_1_lift_isometry` was false (conjuncts 3b and 4; counterexample `R = ℍ`,
`Γ = ⟨−1⟩`, `p = id`, `μ = 0` a.e. in every chart with value `1/2` at the chart centres). -/
def liftBeltrami (p : UpperHalfPlane → R) (μ : R → ℂ → ℂ) (w : ℂ) : ℂ :=
  if hw : 0 < w.im then
    if h : ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P then
      ∑' i, (h.choose_spec.choose i).indicator (fun y => μ (h.choose i) (chartAt ℂ (h.choose i) y) *
        (conj (deriv (fun v => chartAt ℂ (h.choose i) (p (UpperHalfPlane.ofComplex v))) w) /
          deriv (fun v => chartAt ℂ (h.choose i) (p (UpperHalfPlane.ofComplex v))) w)) (p ⟨w, hw⟩)
    else 0
  else 0

/-- Helper (§3.1). A uniformized surface has a chart partition: it is second countable (`gl31_secondCountable`) and
nonempty (`p` maps `ℍ` onto it), so `gl31_exists_chartPartition` applies to the chart sources. -/
theorem gl31_exists_chartPartition_of_uniformization {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) :
    ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P := by
  have hsc := gl31_secondCountable hp
  have hne : Nonempty R := ⟨p UpperHalfPlane.I⟩
  obtain ⟨x, P, hP, -⟩ := gl31_exists_chartPartition (R := R) (fun y => (chartAt ℂ y).source)
    (fun y => (chartAt ℂ y).open_source) (fun y => mem_chart_source ℂ y) (fun _ => subset_rfl)
  exact ⟨x, P, hP⟩

/-- Helper (§3.1). On `ℍ`, `liftQD p φ` is LiZhongQC's lift `utm_liftQD φ p`: the same formula, since
`LiZhongQC.utm_pext p` is `p ∘ ofComplex` near every point of `ℍ`. -/
theorem gl31_liftQD_eqOn (p : UpperHalfPlane → R) (φ : R → ℂ → ℂ) :
    EqOn (liftQD p φ) (LiZhongQC.utm_liftQD φ p) upperHalf := by
  intro z hz
  have hz' : 0 < z.im := hz
  have hpe : LiZhongQC.utm_pext p z = p ⟨z, hz'⟩ := by
    rw [LiZhongQC.utm_a_pext_eq p hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  have hev : (fun v => chartAt ℂ (p ⟨z, hz'⟩) (p (UpperHalfPlane.ofComplex v))) =ᶠ[𝓝 z]
      fun v => chartAt ℂ (p ⟨z, hz'⟩) (LiZhongQC.utm_pext p v) := by
    filter_upwards [LiZhongQC.isOpen_upperHalf.mem_nhds hz] with v hv
    rw [LiZhongQC.utm_a_pext_eq p hv]
  show liftQD p φ z = φ (LiZhongQC.utm_pext p z) (chartAt ℂ (LiZhongQC.utm_pext p z) (LiZhongQC.utm_pext p z)) *
    deriv (fun w => chartAt ℂ (LiZhongQC.utm_pext p z) (LiZhongQC.utm_pext p w)) z ^ 2
  rw [liftQD, dite_eq_left hz', hev.deriv_eq, hpe]

/-- Helper (§3.1). When `R` has a chart partition, `pairingRS φ μ` is the sum over the partition chosen in its
definition, which is the partition `liftBeltrami` reads. -/
theorem gl31_pairingRS_eq (φ μ : R → ℂ → ℂ) (h : ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P) :
    pairingRS φ μ = ∑' i, ∫ z in chartAt ℂ (h.choose i) '' h.choose_spec.choose i,
      φ (h.choose i) z * μ (h.choose i) z := by
  rw [pairingRS, dite_eq_left h]

/-- Helper (§3.1). The local form of the lift: at `z ∈ ℍ` with `p̂ z` in the piece `Pᵢ` of the chosen chart partition
`(x, P)`, `μ̃(z) = μ_{xᵢ}(hᵢ z) conj(hᵢ′ z)/hᵢ′ z`, `hᵢ = φ_{xᵢ} ∘ p̂` (`p̂ = LiZhongQC.utm_pext p`). -/
theorem gl31_liftBeltrami_apply (p : UpperHalfPlane → R) (μ : R → ℂ → ℂ)
    (h : ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P) {z : ℂ} (hz : 0 < z.im) {i : ℕ}
    (hi : LiZhongQC.utm_pext p z ∈ h.choose_spec.choose i) :
    liftBeltrami p μ z = μ (h.choose i) (chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p z)) *
      (conj (deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) z) /
        deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) z) := by
  have hP := h.choose_spec.choose_spec
  have hz' : 0 < z.im := hz
  have hpe : LiZhongQC.utm_pext p z = p ⟨z, hz'⟩ := by
    rw [LiZhongQC.utm_a_pext_eq p hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  have hi' : p ⟨z, hz'⟩ ∈ h.choose_spec.choose i := by
    rw [← hpe]
    exact hi
  have hev : (fun v => chartAt ℂ (h.choose i) (p (UpperHalfPlane.ofComplex v))) =ᶠ[𝓝 z]
      fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v) := by
    filter_upwards [LiZhongQC.isOpen_upperHalf.mem_nhds hz] with v hv
    rw [LiZhongQC.utm_a_pext_eq p hv]
  rw [liftBeltrami, dite_eq_left hz', dite_eq_left h, tsum_eq_single i]
  · rw [indicator_of_mem hi', hev.deriv_eq, hpe]
  · intro j hj
    exact indicator_of_notMem (fun hj' => Set.disjoint_left.1 (hP.2.1 hj) hj' hi') _

/-- Helper (§3.1). `O = ℍ ∩ p̂⁻¹(source of the chart at x)` is open (`p̂ = LiZhongQC.utm_pext p` is continuous on
`ℍ`). -/
theorem gl31_isOpen_over {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (x : R) :
    IsOpen (upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ x).source) :=
  ContinuousOn.isOpen_inter_preimage
    (fun z hz => (LiZhongQC.utm_a_continuousAt hp.1.continuous (show 0 < z.im from hz)).continuousWithinAt)
    LiZhongQC.isOpen_upperHalf (chartAt ℂ x).open_source

/-- Helper (§3.1). For `A` inside the source of the chart at `x` with measurable chart image, `ℍ ∩ p̂⁻¹(A)` is
measurable: it is `O ∩ (φₓ ∘ p̂)⁻¹(φₓ(A))` with `O` as in `gl31_isOpen_over`. -/
theorem gl31_measurableSet_upper {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (x : R) {A : Set R} (hAx : A ⊆ (chartAt ℂ x).source)
    (hAm : MeasurableSet (chartAt ℂ x '' A)) : MeasurableSet (upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' A) := by
  have heq : upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' A = (upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ x).source) ∩
      (fun z => chartAt ℂ x (LiZhongQC.utm_pext p z)) ⁻¹' (chartAt ℂ x '' A) := by
    ext z
    constructor
    · rintro ⟨hzH, hzA⟩
      exact ⟨⟨hzH, hAx hzA⟩, ⟨_, hzA, rfl⟩⟩
    · rintro ⟨⟨hzH, hzs⟩, ⟨y, hyA, hyz⟩⟩
      refine ⟨hzH, ?_⟩
      have hy : y = LiZhongQC.utm_pext p z := (chartAt ℂ x).injOn (hAx hyA) hzs hyz
      show LiZhongQC.utm_pext p z ∈ A
      rw [← hy]
      exact hyA
  rw [heq]
  exact gl31_measurableSet_lift hp x (gl31_isOpen_over hp x) inter_subset_left (fun z hz => hz.2) hAm

/-- Helper (§3.1). The chart expression `h = φₓ ∘ p̂` pulls null sets back to null sets on
`O = ℍ ∩ p̂⁻¹(source)`: near every point of `O`, `h` is injective with `h′ ≠ 0` (`LiZhongQC.utm_liftQD_local`), so on
such an open set `∫ |h′|²` over `h⁻¹(N)` is `vol h(h⁻¹ N) = 0` (`gl31_lintegral_sheet`); countably many cover `O`. -/
theorem gl31_null_preimage [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) (x : R) {N : Set ℂ} (hN : volume N = 0) :
    volume (upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ x).source ∩
      (fun z => chartAt ℂ x (LiZhongQC.utm_pext p z)) ⁻¹' N) = 0 := by
  set N' := toMeasurable volume N with hN'
  have hN'm : MeasurableSet N' := measurableSet_toMeasurable _ _
  have hN'0 : volume N' = 0 := by
    rw [hN', measure_toMeasurable]
    exact hN
  have hq0 : LiZhongQC.IsHolQuadDiff (0 : R → ℂ → ℂ) := (holQuadDiffSubmodule R).zero_mem
  have hloc : ∀ z : ↥(upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ x).source), ∃ U : Set ℂ, IsOpen U ∧
      (z : ℂ) ∈ U ∧ U ⊆ upperHalf ∧ InjOn (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) U ∧
      ∀ w ∈ U, LiZhongQC.utm_pext p w ∈ (chartAt ℂ x).source ∧
        deriv (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) w ≠ 0 := by
    rintro ⟨z, hzH, hzs⟩
    have hz' : 0 < z.im := hzH
    have hzs' : LiZhongQC.utm_pext p z ∈ (chartAt ℂ x).source := hzs
    have hsrc : p ⟨z, hz'⟩ ∈ (chartAt ℂ x).source := by
      rw [LiZhongQC.utm_a_pext_eq p hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz'] at hzs'
      exact hzs'
    obtain ⟨U, hUo, hzU, hUH, hUi, hU⟩ := LiZhongQC.utm_liftQD_local hq0 hp ⟨z, hz'⟩ x hsrc
    exact ⟨U, hUo, hzU, hUH, hUi, fun w hw => ⟨(hU w hw).1, (hU w hw).2.2.1⟩⟩
  choose U hUo hzU hUH hUi hU using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hUo
  have hsub : upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ x).source ∩
      (fun z => chartAt ℂ x (LiZhongQC.utm_pext p z)) ⁻¹' N ⊆
      ⋃ t ∈ T, (U t ∩ (fun z => chartAt ℂ x (LiZhongQC.utm_pext p z)) ⁻¹' N') := by
    rintro z ⟨hzO, hzN⟩
    have hz : z ∈ ⋃ t, U t := mem_iUnion.2 ⟨⟨z, hzO⟩, hzU _⟩
    rw [← hTU] at hz
    obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.1 hz
    exact mem_iUnion₂.2 ⟨t, ht, hzt, subset_toMeasurable _ _ hzN⟩
  refine measure_mono_null hsub ((measure_biUnion_null_iff hTc).2 fun t _ => ?_)
  have hEm : MeasurableSet (U t ∩ (fun z => chartAt ℂ x (LiZhongQC.utm_pext p z)) ⁻¹' N') :=
    gl31_measurableSet_lift hp x (hUo t) (hUH t) (fun w hw => (hU t w hw).1) hN'm
  have hpi : InjOn (LiZhongQC.utm_pext p) (U t) := fun a ha b hb hab =>
    hUi t ha hb (by simp only [hab])
  have hcov := gl31_lintegral_sheet hp x (hUo t) (hUH t) hpi (fun w hw => (hU t w hw).1) hEm inter_subset_left
    (fun _ => 1)
  have hL : ∫⁻ w in chartAt ℂ x '' (LiZhongQC.utm_pext p ''
      (U t ∩ (fun z => chartAt ℂ x (LiZhongQC.utm_pext p z)) ⁻¹' N')), (1 : ℝ≥0∞) = 0 := by
    rw [setLIntegral_one]
    refine measure_mono_null ?_ hN'0
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact hz.2
  rw [hL] at hcov
  have hdiff : DifferentiableOn ℂ (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) (U t) := fun w hw =>
    (LiZhongQC.utm_a_differentiableAt hp.2.1 x (hUH t hw) (hU t w hw).1).differentiableWithinAt
  have hfm : AEMeasurable (fun z => ENNReal.ofReal (‖deriv (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) z‖ ^ 2) *
      (fun _ => (1 : ℝ≥0∞)) (chartAt ℂ x (LiZhongQC.utm_pext p z)))
      (volume.restrict (U t ∩ (fun z => chartAt ℂ x (LiZhongQC.utm_pext p z)) ⁻¹' N')) := by
    have h1 := (((hdiff.deriv (hUo t)).continuousOn.norm.pow 2).aemeasurable (μ := volume)
      (hUo t).measurableSet).ennreal_ofReal
    exact (h1.mul_const 1).mono_measure (Measure.restrict_mono inter_subset_left le_rfl)
  have hae := (lintegral_eq_zero_iff' hfm).1 hcov.symm
  have hfalse : ∀ᵐ z ∂(volume.restrict (U t ∩ (fun z => chartAt ℂ x (LiZhongQC.utm_pext p z)) ⁻¹' N')), False := by
    filter_upwards [hae, ae_restrict_mem hEm] with z hz hzE
    have hD := (hU t z hzE.1).2
    simp only [Pi.zero_apply, mul_one, ENNReal.ofReal_eq_zero] at hz
    exact hD (norm_eq_zero.1 (pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (le_antisymm hz (by positivity))))
  exact Measure.restrict_eq_zero.1 (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hfalse))

/-- Helper (§3.1). The chart expression `h = φₓ ∘ p̂` maps null subsets of `O = ℍ ∩ p̂⁻¹(source)` to null sets
(`h` is differentiable on `O`). -/
theorem gl31_null_image [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) (x : R) {M : Set ℂ}
    (hM : M ⊆ upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ x).source) (hM0 : volume M = 0) :
    volume ((fun z => chartAt ℂ x (LiZhongQC.utm_pext p z)) '' M) = 0 :=
  addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (fun _ hz => ((LiZhongQC.utm_a_differentiableAt hp.2.1 x (hM hz).1 (hM hz).2).restrictScalars
      ℝ).differentiableWithinAt) hM0

/-- Helper (§3.1). On `O = ℍ ∩ p̂⁻¹(source)` the chart expression `h = φₓ ∘ p̂` has a holomorphic, nowhere zero
derivative (`LiZhongQC.utm_liftQD_local`). -/
theorem gl31_deriv_over [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) (x : R) :
    DifferentiableOn ℂ (deriv (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)))
      (upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ x).source) ∧
    ∀ z ∈ upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ x).source,
      deriv (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v)) z ≠ 0 := by
  have hdiff : DifferentiableOn ℂ (fun v => chartAt ℂ x (LiZhongQC.utm_pext p v))
      (upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ x).source) := fun w hw =>
    (LiZhongQC.utm_a_differentiableAt hp.2.1 x hw.1 hw.2).differentiableWithinAt
  refine ⟨hdiff.deriv (gl31_isOpen_over hp x), fun z hz => ?_⟩
  have hq0 : LiZhongQC.IsHolQuadDiff (0 : R → ℂ → ℂ) := (holQuadDiffSubmodule R).zero_mem
  have hz' : 0 < z.im := hz.1
  have hzs : LiZhongQC.utm_pext p z ∈ (chartAt ℂ x).source := hz.2
  have hsrc : p ⟨z, hz'⟩ ∈ (chartAt ℂ x).source := by
    rw [LiZhongQC.utm_a_pext_eq p hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz'] at hzs
    exact hzs
  obtain ⟨U, -, hzU, -, -, hU⟩ := LiZhongQC.utm_liftQD_local hq0 hp ⟨z, hz'⟩ x hsrc
  exact (hU z hzU).2.2.1

/-- Helper (§3.1). The lift of a Beltrami differential of a uniformized surface is a.e.-strongly measurable on `ℍ`
and `‖μ̃‖∞ ≤ ‖μ‖∞`: on `p̂⁻¹(Pᵢ)` it is `μ_{xᵢ} ∘ hᵢ` times a unimodular factor, and the local biholomorphisms `hᵢ`
pull null sets back to null sets. -/
theorem gl31_liftBeltrami_ae [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {μ : R → ℂ → ℂ} (hμ : μ ∈ beltramiSpace R) :
    AEStronglyMeasurable (liftBeltrami p μ) (volume.restrict upperHalf) ∧
      eLpNorm (liftBeltrami p μ) ⊤ (volume.restrict upperHalf) ≤ beltramiNormRS μ := by
  classical
  obtain ⟨k, hlaw, hbd⟩ := hμ
  have h := gl31_exists_chartPartition_of_uniformization hp
  have hP : IsChartPartition R h.choose h.choose_spec.choose := h.choose_spec.choose_spec
  have hcovR : ∀ y : R, ∃ i, y ∈ h.choose_spec.choose i := fun y => by
    have hy : y ∈ ⋃ i, h.choose_spec.choose i := by
      rw [hP.2.2]
      exact mem_univ _
    exact mem_iUnion.1 hy
  have hSU : upperHalf = ⋃ i, (upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' h.choose_spec.choose i) := by
    rw [← inter_iUnion, ← preimage_iUnion, hP.2.2, preimage_univ, inter_univ]
  have hSm : ∀ i, MeasurableSet (upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' h.choose_spec.choose i) := fun i =>
    gl31_measurableSet_upper hp (h.choose i) (hP.1 i).1 (hP.1 i).2
  have hSO : ∀ i, upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' h.choose_spec.choose i ⊆
      upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ (h.choose i)).source := fun i z hz =>
    ⟨hz.1, (hP.1 i).1 hz.2⟩
  -- on each piece the lift is `μ_{xᵢ} ∘ hᵢ` times a factor of modulus one
  have hloc : ∀ i, ∀ z ∈ upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' h.choose_spec.choose i,
      liftBeltrami p μ z = μ (h.choose i) (chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p z)) *
        (conj (deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) z) /
          deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) z) := fun i z hz =>
    gl31_liftBeltrami_apply p μ h hz.1 hz.2
  have hunit : ∀ i, ∀ z ∈ upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ (h.choose i)).source,
      ‖conj (deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) z) /
        deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) z‖ = 1 := fun i z hz => by
    have hD := (gl31_deriv_over hp (h.choose i)).2 z hz
    rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hD)]
  -- the composition `μ_{xᵢ} ∘ hᵢ` is a.e.-strongly measurable on `O`: null sets pull back to null sets
  have hcomp : ∀ i, AEStronglyMeasurable (fun z => μ (h.choose i) (chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p z)))
      (volume.restrict (upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ (h.choose i)).source)) := by
    intro i
    have hO := gl31_isOpen_over hp (h.choose i)
    have hcont : ContinuousOn (fun z => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p z))
        (upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ (h.choose i)).source) := fun z hz =>
      (((chartAt ℂ (h.choose i)).continuousAt hz.2).comp
        (LiZhongQC.utm_a_continuousAt hp.1.continuous (show 0 < z.im from hz.1))).continuousWithinAt
    have hfm := hcont.aemeasurable (μ := volume) hO.measurableSet
    have hac : Measure.map (fun z => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p z))
        (volume.restrict (upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ (h.choose i)).source)) ≪
          volume.restrict (chartAt ℂ (h.choose i)).target := by
      refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
      rw [Measure.map_apply_of_aemeasurable hfm hs, Measure.restrict_apply' hO.measurableSet]
      rw [Measure.restrict_apply hs] at hs0
      refine measure_mono_null ?_ (gl31_null_preimage hp (h.choose i) hs0)
      rintro z ⟨hzs, hzO⟩
      exact ⟨hzO, hzs, (chartAt ℂ (h.choose i)).map_source hzO.2⟩
    exact ((hbd (h.choose i)).1.mono_ac hac).comp_aemeasurable hfm
  have hmeas : AEStronglyMeasurable (liftBeltrami p μ) (volume.restrict upperHalf) := by
    rw [hSU, aestronglyMeasurable_iUnion_iff]
    intro i
    have hfac : ContinuousOn (fun z => conj (deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) z) /
        deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) z)
        (upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ (h.choose i)).source) := by
      have hDc := (gl31_deriv_over hp (h.choose i)).1.continuousOn
      exact (Complex.continuous_conj.comp_continuousOn hDc).div hDc (gl31_deriv_over hp (h.choose i)).2
    have hm := (hcomp i).mul (hfac.aestronglyMeasurable (gl31_isOpen_over hp (h.choose i)).measurableSet)
    refine (hm.mono_measure (Measure.restrict_mono (hSO i) le_rfl)).congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' (hSm i)]
    exact ae_of_all _ fun z hz => (hloc i z hz).symm
  refine ⟨hmeas, ?_⟩
  -- `‖μ̃‖ ≤ ‖μ‖∞` a.e. on every piece
  have hle : ∀ i, ∀ᵐ w ∂(volume.restrict (chartAt ℂ (h.choose i)).target),
      ‖μ (h.choose i) w‖ₑ ≤ beltramiNormRS μ := fun i => by
    have h1 := ae_le_eLpNormEssSup (μ := volume.restrict (chartAt ℂ (h.choose i)).target) (f := μ (h.choose i))
    filter_upwards [h1] with w hw
    refine hw.trans ?_
    rw [← eLpNorm_exponent_top (hbd (h.choose i)).1]
    exact le_iSup (fun y => eLpNorm (μ y) ⊤ (volume.restrict (chartAt ℂ y).target)) (h.choose i)
  have hae : ∀ᵐ z ∂(volume.restrict upperHalf), ‖liftBeltrami p μ z‖ₑ ≤ beltramiNormRS μ := by
    rw [hSU, ae_restrict_iUnion_iff]
    intro i
    rw [ae_restrict_iff' (hSm i)]
    have hN := hle i
    rw [ae_restrict_iff' (chartAt ℂ (h.choose i)).open_target.measurableSet] at hN
    have hN0 : volume {w : ℂ | w ∈ (chartAt ℂ (h.choose i)).target ∧
        beltramiNormRS μ < ‖μ (h.choose i) w‖ₑ} = 0 :=
      measure_eq_zero_iff_ae_notMem.2 (hN.mono fun w hw hw' => (not_le.2 hw'.2) (hw hw'.1))
    have hpull := gl31_null_preimage hp (h.choose i) hN0
    rw [measure_eq_zero_iff_ae_notMem] at hpull
    filter_upwards [hpull] with z hz hzS
    have hb : ‖conj (deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) z) /
        deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) z‖ₑ = 1 := by
      rw [← ofReal_norm, hunit i z (hSO i hzS), ENNReal.ofReal_one]
    rw [hloc i z hzS, enorm_mul, hb, mul_one]
    by_contra hcon
    exact hz ⟨hSO i hzS, (chartAt ℂ (h.choose i)).map_source (hSO i hzS).2, not_le.1 hcon⟩
  rw [eLpNorm_exponent_top hmeas]
  exact essSup_le_of_ae_le _ hae

/-- Helper (§3.1). `‖μ‖∞ ≤ ‖μ̃‖∞`: in every chart `x`, `|μₓ| = |μ_{xᵢ} ∘ T|` a.e. on the overlaps (the law of `μ`, with
`|T′|⁻¹ |conj T′| = 1`), which is `|μ̃|` at the lifted points, and images of null sets under `φₓ ∘ p̂` are null. -/
theorem gl31_beltramiNormRS_le [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {μ : R → ℂ → ℂ} (hμ : μ ∈ beltramiSpace R) :
    beltramiNormRS μ ≤ eLpNorm (liftBeltrami p μ) ⊤ (volume.restrict upperHalf) := by
  classical
  obtain ⟨k, hlaw, hbd⟩ := hμ
  have h := gl31_exists_chartPartition_of_uniformization hp
  have hP : IsChartPartition R h.choose h.choose_spec.choose := h.choose_spec.choose_spec
  have hcovR : ∀ y : R, ∃ i, y ∈ h.choose_spec.choose i := fun y => by
    have hy : y ∈ ⋃ i, h.choose_spec.choose i := by
      rw [hP.2.2]
      exact mem_univ _
    exact mem_iUnion.1 hy
  by_cases hctop : eLpNorm (liftBeltrami p μ) ⊤ (volume.restrict upperHalf) = ⊤
  · rw [hctop]
    exact le_top
  have hmeas : AEStronglyMeasurable (liftBeltrami p μ) (volume.restrict upperHalf) :=
    aestronglyMeasurable_of_eLpNorm_ne_top hctop
  have hcae : ∀ᵐ z ∂(volume.restrict upperHalf),
      ‖liftBeltrami p μ z‖ₑ ≤ eLpNorm (liftBeltrami p μ) ⊤ (volume.restrict upperHalf) := by
    have h1 := ae_le_eLpNormEssSup (μ := volume.restrict upperHalf) (f := liftBeltrami p μ)
    rwa [← eLpNorm_exponent_top hmeas] at h1
  rw [ae_restrict_iff' LiZhongQC.isOpen_upperHalf.measurableSet] at hcae
  have hB0 : volume {z : ℂ | z ∈ upperHalf ∧
      eLpNorm (liftBeltrami p μ) ⊤ (volume.restrict upperHalf) < ‖liftBeltrami p μ z‖ₑ} = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hcae.mono fun z hz hzB => (not_le.2 hzB.2) (hz hzB.1))
  refine iSup_le fun y => ?_
  rw [eLpNorm_exponent_top (hbd y).1]
  refine essSup_le_of_ae_le _ ?_
  -- the exceptional sets of the transformation law between the chart at `y` and the charts of the partition
  have hTm : ∀ i, MeasurableSet ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ (h.choose i)).source) :=
    fun i => ((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ (h.choose i)).open_source).measurableSet
  have hexc : ∀ i, volume {w : ℂ | w ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ (h.choose i)).source ∧
      ¬ μ y w = μ (h.choose i) (LiZhongQC.chartTransition (h.choose i) y w) *
        deriv (LiZhongQC.chartTransition (h.choose i) y) w ^ (-1 : ℤ) *
          conj (deriv (LiZhongQC.chartTransition (h.choose i) y) w) ^ (1 : ℤ)} = 0 := fun i => by
    have h1 := hlaw (h.choose i) y
    rw [ae_restrict_iff' (hTm i)] at h1
    exact measure_eq_zero_iff_ae_notMem.2 (h1.mono fun w hw hw' => hw'.2 (hw hw'.1))
  have himg := gl31_null_image hp y (M := {z : ℂ | z ∈ upperHalf ∧
      eLpNorm (liftBeltrami p μ) ⊤ (volume.restrict upperHalf) < ‖liftBeltrami p μ z‖ₑ} ∩
        (upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ y).source)) inter_subset_right
    (measure_mono_null inter_subset_left hB0)
  have hnull := measure_union_null ((measure_iUnion_null_iff).2 hexc) himg
  rw [measure_eq_zero_iff_ae_notMem] at hnull
  rw [Filter.EventuallyLE, ae_restrict_iff' (chartAt ℂ y).open_target.measurableSet]
  filter_upwards [hnull] with w hw hwt
  by_contra hcon
  have hlt := not_le.1 hcon
  obtain ⟨i, hi⟩ := hcovR ((chartAt ℂ y).symm w)
  have hy'src : (chartAt ℂ y).symm w ∈ (chartAt ℂ (h.choose i)).source := (hP.1 i).1 hi
  have hwT : w ∈ (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ (h.choose i)).source := ⟨hwt, hy'src⟩
  have hlw : μ y w = μ (h.choose i) (LiZhongQC.chartTransition (h.choose i) y w) *
      deriv (LiZhongQC.chartTransition (h.choose i) y) w ^ (-1 : ℤ) *
        conj (deriv (LiZhongQC.chartTransition (h.choose i) y) w) ^ (1 : ℤ) := by
    by_contra hnl
    exact hw (Or.inl (mem_iUnion.2 ⟨i, hwT, hnl⟩))
  have hTne := (LiZhongQC.s23_transition (h.choose i) y hwt hy'src).2
  have hnorm1 : ‖μ y w‖ₑ = ‖μ (h.choose i) (LiZhongQC.chartTransition (h.choose i) y w)‖ₑ := by
    rw [hlw, ← ofReal_norm, ← ofReal_norm]
    congr 1
    rw [norm_mul, norm_mul, norm_zpow, norm_zpow, Complex.norm_conj, zpow_neg_one, zpow_one]
    have hb : ‖deriv (LiZhongQC.chartTransition (h.choose i) y) w‖ ≠ 0 := norm_ne_zero_iff.2 hTne
    field_simp
  -- lift `(chartAt y).symm w` to `ℍ`
  obtain ⟨τ, hτ⟩ := hp.2.2.1 ((chartAt ℂ y).symm w)
  have hzH : (τ : ℂ) ∈ upperHalf := τ.coe_im_pos
  have hpez : LiZhongQC.utm_pext p τ = (chartAt ℂ y).symm w := by
    rw [LiZhongQC.utm_a_pext_eq p τ.coe_im_pos, UpperHalfPlane.ofComplex_apply, hτ]
  have hz_i : LiZhongQC.utm_pext p τ ∈ h.choose_spec.choose i := by
    rw [hpez]
    exact hi
  have hzO : (τ : ℂ) ∈ upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ (h.choose i)).source :=
    ⟨hzH, (hP.1 i).1 hz_i⟩
  have hb : ‖conj (deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) τ) /
      deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) τ‖ₑ = 1 := by
    have hD := (gl31_deriv_over hp (h.choose i)).2 _ hzO
    rw [← ofReal_norm, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hD), ENNReal.ofReal_one]
  have hlift : ‖liftBeltrami p μ τ‖ₑ = ‖μ (h.choose i) (LiZhongQC.chartTransition (h.choose i) y w)‖ₑ := by
    rw [gl31_liftBeltrami_apply p μ h hzH hz_i, enorm_mul, hb, mul_one, hpez]
    rfl
  refine hw (Or.inr ⟨τ, ⟨⟨hzH, ?_⟩, hzH, ?_⟩, ?_⟩)
  · rw [hlift, ← hnorm1]
    exact hlt
  · show LiZhongQC.utm_pext p τ ∈ (chartAt ℂ y).source
    rw [hpez]
    exact (chartAt ℂ y).map_target hwt
  · show chartAt ℂ y (LiZhongQC.utm_pext p τ) = w
    rw [hpez]
    exact (chartAt ℂ y).right_inv hwt

/-- Helper (§3.1). The transformation rule of the lift under `γ ∈ Γ`, pointwise on `ℍ`:
`μ̃(z) = μ̃(γz) (cz + d)²/conj((cz + d)²)` (`gl31_liftBeltrami_apply` at `z` and `γz`, which lie in the same piece,
and `hᵢ′(z) = hᵢ′(γz)/(cz + d)²`, `LiZhongQC.utm_x2_deriv_mob`). -/
theorem gl31_liftBeltrami_mob {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (μ : R → ℂ → ℂ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {z : ℂ}
    (hz : z ∈ upperHalf) :
    liftBeltrami p μ z = liftBeltrami p μ (LiZhongQC.h36p_m γ z) *
      (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)) := by
  classical
  have hz' : 0 < z.im := hz
  have hmz : LiZhongQC.h36p_m γ z ∈ upperHalf := LiZhongQC.h36p_m_mem γ hz
  have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := LiZhongQC.h36t_den_ne γ ⟨z, hz'⟩
  by_cases h : ∃ (x : ℕ → R) (P : ℕ → Set R), IsChartPartition R x P
  · obtain ⟨i, hi⟩ : ∃ i, LiZhongQC.utm_pext p z ∈ h.choose_spec.choose i := by
      have hc : LiZhongQC.utm_pext p z ∈ ⋃ i, h.choose_spec.choose i := by
        rw [h.choose_spec.choose_spec.2.2]
        exact mem_univ _
      exact mem_iUnion.1 hc
    have hpm : LiZhongQC.utm_pext p (LiZhongQC.h36p_m γ z) = LiZhongQC.utm_pext p z :=
      LiZhongQC.utm_b_pext_mob hp hγ hz'
    have hi' : LiZhongQC.utm_pext p (LiZhongQC.h36p_m γ z) ∈ h.choose_spec.choose i := by
      rw [hpm]
      exact hi
    have hD : deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) z =
        deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) (LiZhongQC.h36p_m γ z) *
          (1 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) :=
      LiZhongQC.utm_x2_deriv_mob hp (h.choose i) hγ hz'
    rw [gl31_liftBeltrami_apply p μ h hz hi, gl31_liftBeltrami_apply p μ h hmz hi', hpm, hD]
    set a := deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) (LiZhongQC.h36p_m γ z)
    set j := (γ 1 0 : ℂ) * z + γ 1 1
    have hj2 : conj (j ^ 2) ≠ 0 := (map_ne_zero _).2 (pow_ne_zero 2 hden)
    by_cases ha : a = 0
    · simp [ha]
    · have hj2' : j ^ 2 ≠ 0 := pow_ne_zero 2 hden
      simp only [map_mul, map_div₀, map_one]
      field_simp
  · have h0 : ∀ w ∈ upperHalf, liftBeltrami p μ w = 0 := fun w hw => by
      rw [liftBeltrami, dite_eq_left (show 0 < w.im from hw), dite_eq_right h]
    rw [h0 z hz, h0 _ hmz, zero_mul]

/-- Helper (§3.1). The lift is `Γ`-compatible, pointwise on `ℍ`: `p̂(γz) = p̂(z)` gives the same piece and chart, and
`hᵢ′(γz) = hᵢ′(z) (cz + d)²` (`LiZhongQC.utm_x2_deriv_mob`). -/
theorem gl31_liftBeltrami_compatible {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (μ : R → ℂ → ℂ) : IsGammaCompatible Γ (liftBeltrami p μ) := by
  intro γ hγ
  rw [ae_restrict_iff' LiZhongQC.isOpen_upperHalf.measurableSet]
  exact ae_of_all _ fun z hz => gl31_liftBeltrami_mob hp μ hγ hz

/-- Helper (§3.1). The lift of `φ ∈ A(R)` lies in `A(Δ, Γ)` (ℍ model) and `∬_F |φ̃| = ‖φ‖`: holomorphy and automorphy
of `LiZhongQC.utm_liftQD` (`gl31_liftQD_eqOn`), and `gl31_quadDiffNorm_eq`. -/
theorem gl31_liftQD_mem [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {φ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R) :
    liftQD p φ ∈ integrableAutomorphicQD Γ F ∧ phiArea (liftQD p φ) F = quadDiffNorm φ := by
  have hF' := hF
  obtain ⟨hFH, hFm, -, -, -⟩ := hF'
  have hφh : LiZhongQC.IsHolQuadDiff φ := hφ.1
  have heq := gl31_liftQD_eqOn p φ
  have hnorm : phiArea (liftQD p φ) F = quadDiffNorm φ := by
    rw [gl31_quadDiffNorm_eq hΓ hfree hp hF hφh]
    show ∫⁻ z in F, ENNReal.ofReal ‖liftQD p φ z‖ = ∫⁻ z in F, ENNReal.ofReal ‖LiZhongQC.utm_liftQD φ p z‖
    exact setLIntegral_congr_fun hFm fun z hz => by rw [heq (hFH hz)]
  refine ⟨⟨(LiZhongQC.utm_liftQD_differentiableOn hφh hp).congr heq, ?_, ?_⟩, hnorm⟩
  · rw [hnorm]
    exact hφ.2
  · intro γ hγ z hz
    have hmz : LiZhongQC.h36p_m γ z ∈ upperHalf := LiZhongQC.h36p_m_mem γ hz
    have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := LiZhongQC.h36t_den_ne γ ⟨z, hz⟩
    show liftQD p φ (LiZhongQC.h36p_m γ z) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = liftQD p φ z
    rw [heq hmz, heq hz, ← LiZhongQC.utm_b_liftQD_automorphic φ hp hγ hz]
    have hm : LiZhongQC.h36p_m γ z = LiZhongQC.utm_b_mob γ z := rfl
    rw [hm]
    field_simp

/-- Helper (§3.1). Every `ψ ∈ A(Δ, Γ)` (ℍ model) is a lift: the descent `LiZhongQC.utm_x_descent` gives a holomorphic
`φ` with `φ̃ = ψ` on `ℍ`, and `‖φ‖ = ∬_F |ψ| < ∞` (`gl31_quadDiffNorm_eq`). -/
theorem gl31_descend [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {ψ : ℂ → ℂ} (hψ : ψ ∈ integrableAutomorphicQD Γ F) :
    ∃ φ ∈ integrableHolQDSet R, EqOn (liftQD p φ) ψ upperHalf := by
  have hF' := hF
  obtain ⟨hFH, hFm, -, -, -⟩ := hF'
  obtain ⟨hψd, hψa, hψΓ⟩ := hψ
  obtain ⟨q, hq, hqψ⟩ := LiZhongQC.utm_x_descent hp hψd hψΓ
  have heq : EqOn (liftQD p q) ψ upperHalf := fun z hz => (gl31_liftQD_eqOn p q hz).trans (hqψ z hz)
  refine ⟨q, ⟨hq, ?_⟩, heq⟩
  rw [gl31_quadDiffNorm_eq hΓ hfree hp hF hq]
  have h1 : phiArea (LiZhongQC.utm_liftQD q p) F = phiArea ψ F := by
    show ∫⁻ z in F, ENNReal.ofReal ‖LiZhongQC.utm_liftQD q p z‖ = ∫⁻ z in F, ENNReal.ofReal ‖ψ z‖
    exact setLIntegral_congr_fun hFm fun z hz => by rw [hqψ z (hFH hz)]
  rw [h1]
  exact hψa

/-- Helper (§3.1). The pairings correspond, `∬_R φμ = ∬_F μ̃ φ̃`: `gl31_integral_unfold` with `g i = φ_{xᵢ} μ_{xᵢ}` on
the partition chosen in `pairingRS` and `liftBeltrami`, where `|hᵢ′|² (g i ∘ hᵢ) = μ̃ φ̃` pointwise on `p̂⁻¹(Pᵢ)`. -/
theorem gl31_pairing_lift [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {φ μ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R) (hμ : μ ∈ beltramiSpace R) :
    pairingRS φ μ = beltramiPairing F (liftBeltrami p μ) (liftQD p φ) := by
  have hF' := hF
  obtain ⟨hFH, hFm, -, -, -⟩ := hF'
  have hφh : LiZhongQC.IsHolQuadDiff φ := hφ.1
  have hφ' : LiZhongQC.IsDiffFamily 2 0 φ ∧ ∀ x : R, DifferentiableOn ℂ (φ x) (chartAt ℂ x).target := hφh
  have hμ' := hμ
  obtain ⟨k, -, hbd⟩ := hμ'
  have h := gl31_exists_chartPartition_of_uniformization hp
  have hP : IsChartPartition R h.choose h.choose_spec.choose := h.choose_spec.choose_spec
  rw [gl31_pairingRS_eq φ μ h]
  have heq := gl31_liftQD_eqOn p φ
  have hae := gl31_liftBeltrami_ae hp hμ
  have hHm : MeasurableSet upperHalf := LiZhongQC.isOpen_upperHalf.measurableSet
  have hφc : ContinuousOn (liftQD p φ) upperHalf :=
    ((LiZhongQC.utm_liftQD_differentiableOn hφh hp).congr heq).continuousOn
  have hkb : beltramiNormRS μ ≤ ENNReal.ofReal k := iSup_le fun y => by
    rw [eLpNorm_exponent_top (hbd y).1]
    exact eLpNormEssSup_le_of_ae_bound (hbd y).2
  have hμb : ∀ᵐ z ∂(volume.restrict upperHalf), ‖liftBeltrami p μ z‖ ≤ max k 0 := by
    have h1 := ae_le_eLpNormEssSup (μ := volume.restrict upperHalf) (f := liftBeltrami p μ)
    filter_upwards [h1] with z hz
    have h2 : ‖liftBeltrami p μ z‖ₑ ≤ ENNReal.ofReal (max k 0) := by
      refine hz.trans ?_
      rw [← eLpNorm_exponent_top hae.1]
      exact hae.2.trans (hkb.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    rw [← ofReal_norm] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 h2
  have hφi : IntegrableOn (liftQD p φ) F := by
    refine ⟨(hφc.aestronglyMeasurable hHm).mono_measure (Measure.restrict_mono hFH le_rfl), ?_⟩
    show ∫⁻ z in F, ‖liftQD p φ z‖ₑ < ⊤
    have h1 := (gl31_liftQD_mem hΓ hfree hp hF hφ).2
    have h2 : phiArea (liftQD p φ) F < ⊤ := by
      rw [h1]
      exact hφ.2
    simp only [← ofReal_norm]
    exact h2
  have hfi : IntegrableOn (fun z => liftBeltrami p μ z * liftQD p φ z) F :=
    hφi.bdd_mul (hae.1.mono_measure (Measure.restrict_mono hFH le_rfl))
      (ae_restrict_of_ae_restrict_of_subset hFH hμb)
  have key := (gl31_integral_unfold hΓ hfree hp hF hP (f := fun z => liftBeltrami p μ z * liftQD p φ z)
    (hae.1.mul (hφc.aestronglyMeasurable hHm)) hfi ?_ (fun i w => φ (h.choose i) w * μ (h.choose i) w) ?_ ?_).2
  · exact key
  · -- the density `μ̃ φ̃ dx dy` is `Γ`-invariant
    intro γ hγ z hz
    have hmz : LiZhongQC.h36p_m γ z ∈ upperHalf := LiZhongQC.h36p_m_mem γ hz
    have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := LiZhongQC.h36t_den_ne γ ⟨z, hz⟩
    have hφa : liftQD p φ z = liftQD p φ (LiZhongQC.h36p_m γ z) * (1 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) ^ 2 := by
      rw [heq hz, heq hmz, ← LiZhongQC.utm_b_liftQD_automorphic φ hp hγ hz]
      rfl
    rw [gl31_liftBeltrami_mob hp μ hγ hz, hφa]
    have hj : ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 * conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) =
        (‖(γ 1 0 : ℂ) * z + γ 1 1‖ : ℂ) ^ 4 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow]
      push_cast
      ring
    have hj0 : conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) ≠ 0 := (map_ne_zero _).2 (pow_ne_zero 2 hden)
    have hn0 : (‖(γ 1 0 : ℂ) * z + γ 1 1‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hden
    push_cast
    rw [← sub_eq_zero]
    field_simp
    linear_combination (liftBeltrami p μ (LiZhongQC.h36p_m γ z) * liftQD p φ (LiZhongQC.h36p_m γ z)) * hj
  · -- the chart functions are a.e.-strongly measurable
    intro i
    have hsub : chartAt ℂ (h.choose i) '' h.choose_spec.choose i ⊆ (chartAt ℂ (h.choose i)).target := by
      rintro _ ⟨y, hy, rfl⟩
      exact (chartAt ℂ (h.choose i)).map_source ((hP.1 i).1 hy)
    have h1 := ((hφ'.2 (h.choose i)).continuousOn.aestronglyMeasurable
      (μ := volume) (chartAt ℂ (h.choose i)).open_target.measurableSet).mul (hbd (h.choose i)).1
    exact h1.mono_measure (Measure.restrict_mono hsub le_rfl)
  · -- the pointwise lifting identity `|hᵢ′|² φ_{xᵢ} μ_{xᵢ} ∘ hᵢ = μ̃ φ̃`
    intro i z hz hzP
    have hz' : 0 < z.im := hz
    have hzO : z ∈ upperHalf ∩ LiZhongQC.utm_pext p ⁻¹' (chartAt ℂ (h.choose i)).source := ⟨hz, (hP.1 i).1 hzP⟩
    have hD := (gl31_deriv_over hp (h.choose i)).2 z hzO
    have hsrc : p ⟨z, hz'⟩ ∈ (chartAt ℂ (h.choose i)).source := by
      have h1 : LiZhongQC.utm_pext p z ∈ (chartAt ℂ (h.choose i)).source := hzO.2
      rw [LiZhongQC.utm_a_pext_eq p hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz'] at h1
      exact h1
    obtain ⟨U, -, hzU, -, -, hU⟩ := LiZhongQC.utm_liftQD_local hφh hp ⟨z, hz'⟩ (h.choose i) hsrc
    obtain ⟨-, -, -, hφz⟩ := hU z hzU
    rw [gl31_liftBeltrami_apply p μ h hz hzP, heq hz, hφz]
    have hDD : deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) z *
        conj (deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) z) =
        ((‖deriv (fun v => chartAt ℂ (h.choose i) (LiZhongQC.utm_pext p v)) z‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← hDD]
    field_simp

/-- **Unlabelled** (§3.1, l. 2153–2210). For a uniformization `p : ℍ → R` with covering group `Γ` and a measurable
fundamental domain `F`: `φ ↦ φ̃` is an isometry of `A(R)` onto `A(Δ, Γ)` (ℍ model), `μ ↦ μ̃` maps `L∞(R)` into
`L∞(Δ, Γ)` preserving `‖·‖∞`, and the pairings correspond: `∬_R φμ = ∬_F φ̃ μ̃`. -/
theorem para3_1_lift_isometry [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → R} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    (∀ φ ∈ integrableHolQDSet R, liftQD p φ ∈ integrableAutomorphicQD Γ F ∧
      phiArea (liftQD p φ) F = quadDiffNorm φ) ∧
    (∀ ψ ∈ integrableAutomorphicQD Γ F, ∃ φ ∈ integrableHolQDSet R, EqOn (liftQD p φ) ψ upperHalf) ∧
    (∀ μ ∈ beltramiSpace R, IsGammaCompatible Γ (liftBeltrami p μ) ∧
      eLpNorm (liftBeltrami p μ) ⊤ (volume.restrict upperHalf) = beltramiNormRS μ) ∧
    ∀ φ ∈ integrableHolQDSet R, ∀ μ ∈ beltramiSpace R,
      pairingRS φ μ = beltramiPairing F (liftBeltrami p μ) (liftQD p φ) := by
  -- `[T2Space R]` and `[ConnectedSpace R]` are not used: the uniformization gives second countability
  -- (`gl31_secondCountable`) and nonemptiness; the statement stays true without them.
  refine ⟨fun φ hφ => gl31_liftQD_mem hΓ hfree hp hF hφ, fun ψ hψ => gl31_descend hΓ hfree hp hF hψ,
    fun μ hμ => ⟨gl31_liftBeltrami_compatible hp μ,
      le_antisymm (gl31_liftBeltrami_ae hp hμ).2 (gl31_beltramiNormRS_le hp hμ)⟩,
    fun φ hφ μ hμ => gl31_pairing_lift hΓ hfree hp hF hφ hμ⟩

end Surface

/-- **Definition** (§3.1, l. 2189–2197). `L∞(Δ, Γ)` (ℍ model): the bounded measurable functions on `ℍ` satisfying the
automorphy condition (3.8). -/
def beltramiSpaceGamma (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → ℂ) :=
  {μ | IsGammaCompatible Γ μ ∧ ∃ k : ℝ, IsBeltramiCoeff μ upperHalf k}

/-- **Definition** (§3.1, l. 2180–2187). `L₁(Δ, Γ)` (ℍ model): measurable functions on `ℍ` satisfying the automorphy
condition (3.7) almost everywhere, with `∬_F |ψ| < ∞` over a fundamental domain `F`. -/
def integrableAutomorphicL1 (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F : Set ℂ) : Set (ℂ → ℂ) :=
  {ψ | AEStronglyMeasurable ψ (volume.restrict upperHalf) ∧ phiArea ψ F < ⊤ ∧
    ∀ γ ∈ Γ, ∀ᵐ z ∂(volume.restrict upperHalf),
      ψ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = ψ z}

/-- **Unlabelled** (§3.1, l. 2210). The pairing over `F` induces an isomorphism of `A(Δ, Γ)*` onto
`L∞(Δ, Γ)/N`: every bounded functional on `A(Δ, Γ)` is `φ ↦ ∬_F μφ` for some `μ ∈ L∞(Δ, Γ)` with `‖μ‖∞` equal to the
dual norm, and no representative has smaller norm. -/
theorem para3_1_dual_gamma {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {F : Set ℂ}
    (hF : IsFundamentalDomainH Γ F) {V : (ℂ → ℂ) → ℂ}
    (hV : IsBoundedFunctionalOn (integrableAutomorphicQD Γ F) (fun φ => phiArea φ F) V) :
    ∃ μ ∈ beltramiSpaceGamma Γ, (∀ φ ∈ integrableAutomorphicQD Γ F, V φ = beltramiPairing F μ φ) ∧
      eLpNorm μ ⊤ (volume.restrict upperHalf) =
        ENNReal.ofReal (dualNormOn (integrableAutomorphicQD Γ F) (fun φ => phiArea φ F) V) ∧
      ∀ ν ∈ beltramiSpaceGamma Γ, (∀ φ ∈ integrableAutomorphicQD Γ F, V φ = beltramiPairing F ν φ) →
        ENNReal.ofReal (dualNormOn (integrableAutomorphicQD Γ F) (fun φ => phiArea φ F) V) ≤
          eLpNorm ν ⊤ (volume.restrict upperHalf) := by
  have hFH : F ⊆ upperHalf := hF.1
  have hFm : MeasurableSet F := hF.2.1
  -- Hahn–Banach on `L¹(F)`, then the automorphic folding of the representing function
  obtain ⟨ν, hνm, hνb, hνrep⟩ := gl3_dual_repr hFm (fun φ hφ => LiZhongQC.h36p_b_integrableOn_A hFH hFm hφ)
    LiZhongQC.h36p_b_A_zero (fun φ hφ ψ hψ => LiZhongQC.h36p_b_A_add hFm hFH hφ hψ)
    (fun c φ hφ => LiZhongQC.h36p_b_A_smul hφ c) hV
  have hD0 : 0 ≤ dualNormOn (integrableAutomorphicQD Γ F) (fun φ => phiArea φ F) V :=
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _
  -- the Γ-compatible extension of `ν` from `F` (`LiZhongQC.h36p_extend`)
  obtain ⟨μ, hμm, -, hμc, hμb', hμν⟩ := LiZhongQC.h36p_extend hΓ hF hD0 hνm hνb
  have hμ : μ ∈ beltramiSpaceGamma Γ :=
    ⟨hμc, dualNormOn (integrableAutomorphicQD Γ F) (fun φ => phiArea φ F) V, hμm.restrict, hμb'⟩
  have hμb : eLpNorm μ ⊤ (volume.restrict upperHalf) ≤
      ENNReal.ofReal (dualNormOn (integrableAutomorphicQD Γ F) (fun φ => phiArea φ F) V) := by
    rw [eLpNorm_exponent_top hμm.restrict]
    exact eLpNormEssSup_le_of_ae_bound hμb'
  have hrep : ∀ φ ∈ integrableAutomorphicQD Γ F, V φ = beltramiPairing F μ φ := fun φ hφ => by
    rw [hνrep φ hφ]
    show _ = ∫ z in F, μ z * φ z
    exact integral_congr_ae (by filter_upwards [hμν] with z hz; rw [hz])
  refine ⟨μ, hμ, hrep, le_antisymm hμb (gl3_dual_le hFH (ν := μ) hrep),
    fun ν' _ hν' => gl3_dual_le hFH (ν := ν') hν'⟩

end GardinerLakic2000
