import References.LehtoVirtanen1973.Ch03.S01_MeasureIntegral

/-!
# Lehto–Virtanen, Chapter III §5: Approximation of measurable functions

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. III §5
(pp. 136–143; `full.md` P1:4077–4324).

Conventions (see also §1). The measure is the Lebesgue area measure `volume` of the finite plane `ℂ`; the functions to
be approximated are defined and measurable in the whole finite plane (a function measurable in a set is extended by
zero, P1:4081). LV's "almost everywhere finite" complex functions are finite `ℂ`-valued here (leader decision D2); a
measurable function in the plane is `AEStronglyMeasurable` for `volume`. `sup_z |f(z)|` is the pointwise supremum
`⨆ z, ‖f z‖ₑ` in `[0, ∞]` (it is `∞` for unbounded `f`). The class `L^p`, `1 ≤ p < ∞` (§4.4), is
`MemLp f (ENNReal.ofReal p)` with a real exponent `p ≥ 1`. A polynomial `P(z, z̄)` in `z` and `z̄` (equivalently in
`x` and `y`) with complex coefficients is an element of `MvPolynomial (Fin 2) ℂ` evaluated at `(z, z̄)`. The
convolution `f * ϑ` of (5.2) with a real function `ϑ` is Mathlib's `f ⋆[L] ϑ` for the bilinear map
`L(a, t) = t a` (`(lsmul ℝ ℝ).flip`), i.e. LV's second form `∬ f(ζ) ϑ(z − ζ) dσ`. The sequences `ϑₙ` are indexed by
`n = 1, 2, …` as in the book: the hypotheses are made for `n ≥ 1`, and limits as `n → ∞` do not see `n = 0`.

* Unlabelled (§5.2, P1:4097–4121): an almost everywhere finite measurable function is the limit almost everywhere
  of uniformly continuous functions `fₙ` with `|fₙ| ≤ sup |f|` — `exists_continuous_ae_approx`
* Lusin's theorem (§5.2) — `lusin_theorem`
* Definition (net with mesh `δ`, the net becoming finer; step function, §5.3) — `netSquare`, `IsStepFunction`
* Unlabelled (§5.3, P1:4131): an almost everywhere finite measurable function is the limit almost everywhere of
  step functions `φₙ` with `sup |φₙ| ≤ sup |f|` — `exists_stepFunction_ae_approx`
* Unlabelled (§5.3, P1:4133–4149): an almost everywhere finite measurable function is the limit almost everywhere
  of polynomials `Pₙ(z, z̄)` which, in every bounded set, are from some `n` on at most `sup |f|` in absolute value —
  `exists_polynomial_ae_approx`
* Weierstrass's approximation theorem (§5.3, quoted) — `weierstrass_approximation`
* Definition (locally integrable function, §5.4) — exists: `MeasureTheory.LocallyIntegrable` (integrable over every
  compact subset of the plane, by MeasureTheory.locallyIntegrable_iff)
* Definition (the convolution `f * ϑ`, formula (5.2), §5.4) — exists: `MeasureTheory.convolution` (with a
  continuous bilinear map; for a real kernel the map is scalar multiplication, which gives the book's second form)
* Unlabelled (§5.4, P1:4161–4167, 4189–4191): for `f` locally integrable and `ϑ` finite, continuous and vanishing
  outside a disc, `f * ϑ` is continuous, belongs to `C^n` together with `ϑ` (`n ≤ ∞`), and has bounded support if
  `f` has — exists: `HasCompactSupport.continuous_convolution_right`, `HasCompactSupport.contDiff_convolution_right`,
  `HasCompactSupport.convolution` (for the area measure; a function vanishing outside a disc, resp. with bounded
  support, has compact support in the plane; the order n ranges over the natural numbers and infinity)
* Formula (5.3) (§5.4) — exists: `HasCompactSupport.hasFDerivAt_convolution_right`,
  `HasCompactSupport.continuous_convolution_right` (the total derivative of f * ϑ is the convolution of f with the
  derivative of the continuously differentiable ϑ; its values at 1 and at i are the partial derivatives, which are
  continuous by the second pointer applied to the partial derivatives of ϑ)
* Mean value theorem (§5.4, quoted in passing) — omitted: a classical tool inside the derivation of (5.3), not
  stated as a result of the book
* Definition (the classes `C^n`, `C^∞`, the support of a function, the class `C_0^n`, §5.4) — exists: `ContDiff`,
  `tsupport`, `HasCompactSupport` (C^∞ is ContDiff of order the coercion of the top element of ℕ∞; in the plane a
  function has bounded support if and only if its support is compact)
* Formula (5.4) (§5.5, the lemma on the continuity of translation in the `L^p` metric) — `eq3_5_4`
* Hölder's inequality (§5.6, footnote 37, quoted) — exists: `ENNReal.lintegral_mul_le_Lp_mul_Lq` (footnote 37
  states it for non-negative F, G and conjugate exponents p > 1, which is the pointer's form; it holds for every
  measure, hence also for the measure ϑₙ dσ)
* Lemma 5.1 (§5.6) — `lemma3_5_1`
* Definition (the functions `ϑₙ` of formula (5.11), §5.7) — `lvMollifier`
* Unlabelled (§5.7, P1:4289): a function of `L^p` in the finite plane can be approximated in the `L^p` metric by
  functions of the class `C_0^∞` — exists: `MeasureTheory.MemLp.exist_eLpNorm_sub_le` (for finite exponents at
  least 1 and the area measure; the approximant is smooth with compact support)
* Lemma 5.2 (§5.8) — `lemma3_5_2`

The construction of 5.1 (approximation by functions taking finitely many values, P1:4083–4095), the remark of 5.2
deducing Lusin's theorem from Egoroff's theorem (P1:4123) and the first sentence of 5.7 (the functions `f * ϑₙ` of
(5.11) belong to `C^∞` and approximate `f` in `L^p`, P1:4287, which is Lemma 5.1 together with the regularity of
convolutions) are steps of derivations and are not stated (inventory: omitted). Lemma 5.2 is stated for every
sequence `ϑₙ` with the properties of 5.6, which is all its proof uses; the functions (5.11) are one such sequence.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Convolution

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (openRect)
open ContinuousLinearMap (lsmul)

/-! ## §5.2 Pointwise approximation by continuous functions -/

/-- **Unlabelled** (Ch. III §5.2, P1:4097–4121). For every almost everywhere finite, measurable function `f` in the
finite plane there are functions `fₙ`, uniformly continuous in the finite plane, such that `fₙ → f` almost
everywhere; the values `|fₙ(z)|` can be greater than `|f(z)|` at certain points, but they cannot exceed
`sup |f(z)|`.
Modelling: `f` is finite `ℂ`-valued (D2) and measurable for the area measure; the supremum is taken in `[0, ∞]`. -/
theorem exists_continuous_ae_approx {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) :
    ∃ fn : ℕ → ℂ → ℂ, (∀ n, UniformContinuous (fn n)) ∧
      (∀ᵐ (z : ℂ), Tendsto (fun n => fn n z) atTop (𝓝 (f z))) ∧ ∀ n z, ‖fn n z‖ₑ ≤ ⨆ ζ, ‖f ζ‖ₑ := by
  sorry

/-- Helper (R2). A simple function `s` of the finite plane is continuous on a closed subset `C` of a measurable set `B`
of finite area with `m(B − C) ≤ δ`: take inner closed approximations of its finitely many level sets in `B`; on their
(finite, disjoint) union `s` is locally constant. -/
theorem lv35_simpleFunc_continuousOn {B : Set ℂ} (hB : MeasurableSet B) (hBfin : volume B ≠ ⊤)
    (s : SimpleFunc ℂ ℂ) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ C ⊆ B, IsClosed C ∧ volume (B \ C) ≤ δ ∧ ContinuousOn s C := by
  set V := s.range with hVdef
  set δ' : ℝ≥0∞ := δ / (V.card + 1) with hδ'def
  have hδ' : δ' ≠ 0 := ENNReal.div_ne_zero.2 ⟨hδ, by simp⟩
  -- closed inner approximations of the level sets `B ∩ s⁻¹{v}`
  have hlev : ∀ v : ℂ, ∃ K ⊆ B ∩ s ⁻¹' {v}, IsClosed K ∧ volume ((B ∩ s ⁻¹' {v}) \ K) < δ' := fun v =>
    (hB.inter (s.measurableSet_fiber v)).exists_isClosed_sdiff_lt
      ((measure_mono inter_subset_left).trans_lt (lt_top_iff_ne_top.2 hBfin)).ne hδ'
  choose K hKsub hKc hKm using hlev
  set C := ⋃ v ∈ V, K v with hCdef
  have hKs : ∀ v, ∀ z ∈ K v, s z = v := fun v z hz => (hKsub v hz).2
  refine ⟨C, iUnion₂_subset fun v _ => (hKsub v).trans inter_subset_left, isClosed_biUnion_finset fun v _ => hKc v,
    ?_, ?_⟩
  · -- `B \ C ⊆ ⋃ v ∈ V, (B ∩ s⁻¹{v}) \ K v`
    have hsub : B \ C ⊆ ⋃ v ∈ V, (B ∩ s ⁻¹' {v}) \ K v := by
      rintro z ⟨hzB, hzC⟩
      refine mem_iUnion₂.2 ⟨s z, s.mem_range_self z, ⟨hzB, rfl⟩, fun hzK => hzC ?_⟩
      exact mem_iUnion₂.2 ⟨s z, s.mem_range_self z, hzK⟩
    calc volume (B \ C) ≤ ∑ v ∈ V, volume ((B ∩ s ⁻¹' {v}) \ K v) :=
          (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
      _ ≤ ∑ _v ∈ V, δ' := Finset.sum_le_sum fun v _ => (hKm v).le
      _ = V.card * δ' := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (V.card + 1) * δ' := by gcongr; exact le_self_add
      _ = δ := ENNReal.mul_div_cancel (by simp) (by simp)
  · -- `s` is locally constant on `C`
    intro z hz
    obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.1 hz
    have hU : (⋃ u ∈ V.erase v, K u)ᶜ ∈ 𝓝 z := by
      refine (isClosed_biUnion_finset fun u _ => hKc u).isOpen_compl.mem_nhds ?_
      intro h
      obtain ⟨u, hu, hzu⟩ := mem_iUnion₂.1 h
      exact (Finset.mem_erase.1 hu).1 ((hKs u z hzu).symm.trans (hKs v z hzv))
    have hev : (s : ℂ → ℂ) =ᶠ[𝓝[C] z] fun _ => s z := by
      filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with y hyU hyC
      obtain ⟨u, hu, hyu⟩ := mem_iUnion₂.1 hyC
      by_cases huv : u = v
      · rw [hKs u y hyu, huv, hKs v z hzv]
      · exact absurd (mem_iUnion₂.2 ⟨u, Finset.mem_erase.2 ⟨huv, hu⟩, hyu⟩) hyU
    exact continuousWithinAt_const.congr_of_eventuallyEq hev rfl

/-- **Lusin's theorem** (Ch. III §5.2). Let `f` be a complex-valued, almost everywhere finite, measurable function
in a set `A` of finite measure. Then for every `ε > 0` there exists a closed set `F ⊂ A` with `m(A − F) < ε` such
that the restriction of `f` to `F` is finite and continuous.
Modelling: `A` measurable (null-measurable) of finite area; `f` measurable for the area measure restricted to `A`
and finite `ℂ`-valued (D2), so "finite" in the conclusion is automatic. -/
theorem lusin_theorem {A : Set ℂ} (hA : NullMeasurableSet A volume) (hAfin : volume A ≠ ⊤) {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict A)) {ε : ℝ} (hε : 0 < ε) :
    ∃ F ⊆ A, IsClosed F ∧ volume (A \ F) < ENNReal.ofReal ε ∧ ContinuousOn f F := by
  -- a measurable core `A'` of `A`, and simple approximations `φ n` of a measurable representative of `f`
  obtain ⟨A', hA'A, hA'm, hAA'⟩ := hA.exists_measurable_subset_ae_eq
  have hA'v : volume (A \ A') = 0 := (ae_eq_set.1 hAA').2
  have hA'fin : volume A' ≠ ⊤ := ((measure_mono hA'A).trans_lt (lt_top_iff_ne_top.2 hAfin)).ne
  have hh : StronglyMeasurable (hf.mk f) := hf.stronglyMeasurable_mk
  set φ : ℕ → SimpleFunc ℂ ℂ := hh.approx with hφdef
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  -- each `φ n` is continuous on a closed `C n ⊆ A'` with `m(A' − C n) ≤ (ε/3) 2^{-(n+1)}`
  have hδ : ∀ n : ℕ, ENNReal.ofReal (ε / 3) * (2⁻¹) ^ (n + 1) ≠ 0 := fun n =>
    mul_ne_zero (ENNReal.ofReal_pos.2 hε3).ne' (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top))
  choose C hCA hCc hCm hCcont using fun n => lv35_simpleFunc_continuousOn hA'm hA'fin (φ n) (hδ n)
  -- Egorov: `φ n → f` uniformly on a closed `E ⊆ A` with `m(A − E) < ε/3`
  have hconv : ∀ᵐ z ∂(volume.restrict A), Tendsto (fun n => φ n z) atTop (𝓝 (f z)) := by
    filter_upwards [hf.ae_eq_mk] with z hz
    rw [hz]
    exact hh.tendsto_approx z
  obtain ⟨E, hEA, hEc, hEm, hEu⟩ := egoroff_theorem hA hAfin (fun n => (φ n).aestronglyMeasurable) hconv hε3
  refine ⟨E ∩ ⋂ n, C n, inter_subset_left.trans hEA, hEc.inter (isClosed_iInter hCc), ?_, ?_⟩
  · -- `A \ F ⊆ (A \ E) ∪ (A \ A') ∪ ⋃ n, (A' \ C n)`
    have hsub : A \ (E ∩ ⋂ n, C n) ⊆ (A \ E) ∪ (A \ A') ∪ ⋃ n, (A' \ C n) := by
      rintro z ⟨hzA, hzF⟩
      by_cases h1 : z ∈ E
      · by_cases h2 : z ∈ A'
        · refine Or.inr (mem_iUnion.2 ?_)
          by_contra h
          simp only [not_exists] at h
          refine hzF ⟨h1, mem_iInter.2 fun n => ?_⟩
          by_contra hc
          exact h n ⟨h2, hc⟩
        · exact Or.inl (Or.inr ⟨hzA, h2⟩)
      · exact Or.inl (Or.inl ⟨hzA, h1⟩)
    have hsum : ∑' n : ℕ, volume (A' \ C n) ≤ ENNReal.ofReal (ε / 3) := by
      calc ∑' n : ℕ, volume (A' \ C n) ≤ ∑' n : ℕ, ENNReal.ofReal (ε / 3) * (2⁻¹) ^ (n + 1) :=
            ENNReal.tsum_le_tsum hCm
        _ = ENNReal.ofReal (ε / 3) := by
            rw [ENNReal.tsum_mul_left]
            simp only [pow_succ, ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two,
              inv_inv]
            rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    calc volume (A \ (E ∩ ⋂ n, C n)) ≤ volume (A \ E) + volume (A \ A') + ∑' n : ℕ, volume (A' \ C n) :=
          (measure_mono hsub).trans ((measure_union_le _ _).trans
            (add_le_add ((measure_union_le _ _)) (measure_iUnion_le _)))
      _ = volume (A \ E) + ∑' n : ℕ, volume (A' \ C n) := by rw [hA'v, add_zero]
      _ < ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) :=
          ENNReal.add_lt_add_of_lt_of_le (hsum.trans_lt ENNReal.ofReal_lt_top).ne hEm hsum
      _ ≤ ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add hε3.le hε3.le]
          exact ENNReal.ofReal_le_ofReal (by linarith)
  · -- a uniform limit of functions continuous on `F` is continuous on `F`
    exact (hEu.mono inter_subset_left).continuousOn
      (Frequently.of_forall fun n => (hCcont n).mono (inter_subset_right.trans (iInter_subset _ n)))

/-! ## §5.3 Special approximating sequences -/

/-- **Definition** (net, Ch. III §5.3). The open square
`Q_{hk} = {x + iy | (h − 1)δ < x < hδ, (k − 1)δ < y < kδ}`, `h, k = 0, ±1, ±2, …`; the set of these squares is the
net with mesh `δ > 0`, which becomes finer when `δ` is made smaller. -/
def netSquare (δ : ℝ) (h k : ℤ) : Set ℂ :=
  openRect (((h : ℝ) - 1) * δ) ((h : ℝ) * δ) (((k : ℝ) - 1) * δ) ((k : ℝ) * δ)

/-- **Definition** (step function, Ch. III §5.3). A function which takes a constant value in every square of some
net. (Its values on the sides of the squares are not restricted.) -/
def IsStepFunction (φ : ℂ → ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ h k : ℤ, ∃ c : ℂ, ∀ z ∈ netSquare δ h k, φ z = c

/-- **Unlabelled** (Ch. III §5.3, P1:4131). For any almost everywhere finite, measurable function `f` in the finite
plane we can construct a sequence of step functions `φₙ` such that `sup_z |φₙ(z)| ≤ sup_z |f(z)|` and
`f(z) = lim φₙ(z)` almost everywhere.
Modelling: as in `exists_continuous_ae_approx`. -/
theorem exists_stepFunction_ae_approx {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) :
    ∃ φ : ℕ → ℂ → ℂ, (∀ n, IsStepFunction (φ n)) ∧ (∀ n, ⨆ z, ‖φ n z‖ₑ ≤ ⨆ z, ‖f z‖ₑ) ∧
      ∀ᵐ (z : ℂ), Tendsto (fun n => φ n z) atTop (𝓝 (f z)) := by
  sorry

/-- **Unlabelled** (Ch. III §5.3, P1:4133–4149). An almost everywhere finite, measurable function `f` in the finite
plane can be approximated by polynomials: there are polynomials `Pₙ(z, z̄)` with `lim Pₙ(z, z̄) = f(z)` almost
everywhere, and such that from some `n` onwards the absolute value of `Pₙ` in an arbitrary given bounded set is not
larger than the supremum of `|f|` in the plane.
Modelling: `Pₙ ∈ MvPolynomial (Fin 2) ℂ`, evaluated at `(z, z̄)`; the supremum is taken in `[0, ∞]`, so for an
unbounded `f` the bound is void (the book's rescaling `(1 − 1/(n sup |f|)) Pₙ` presupposes `sup |f| < ∞`). -/
theorem exists_polynomial_ae_approx {f : ℂ → ℂ} (hf : AEStronglyMeasurable f volume) :
    ∃ P : ℕ → MvPolynomial (Fin 2) ℂ,
      (∀ᵐ (z : ℂ), Tendsto (fun n => MvPolynomial.eval ![z, conj z] (P n)) atTop (𝓝 (f z))) ∧
      ∀ S : Set ℂ, Bornology.IsBounded S →
        ∀ᶠ n in atTop, ∀ z ∈ S, ‖MvPolynomial.eval ![z, conj z] (P n)‖ₑ ≤ ⨆ ζ, ‖f ζ‖ₑ := by
  sorry

/-- **Weierstrass's approximation theorem** (Ch. III §5.3, quoted). For a continuous function `f` in the finite
plane there exists a sequence of polynomials `Pₖ(z, z̄)` such that `Pₖ(z, z̄) → f(z)` as `k → ∞`, uniformly in every
bounded set.
Modelling: the book applies it to the uniformly continuous functions `fₙ` of 5.2 (with the explicit polynomials
`P_{nk}` of P1:4136, a construction that is not stated); continuity of `f` suffices; `Pₖ ∈ MvPolynomial (Fin 2) ℂ`
evaluated at `(z, z̄)`. -/
theorem weierstrass_approximation {f : ℂ → ℂ} (hf : Continuous f) :
    ∃ P : ℕ → MvPolynomial (Fin 2) ℂ, ∀ S : Set ℂ, Bornology.IsBounded S →
      TendstoUniformlyOn (fun k z => MvPolynomial.eval ![z, conj z] (P k)) f atTop S := by
  sorry

/-! ## §5.5 A lemma on convergence in the `L^p` metric -/

/-- **Formula (5.4)** (Ch. III §5.5, the lemma of 5.5). If `f` belongs to `L^p` in the finite plane `Ω`, then
`lim_{λ → 0} ∬_Ω |f(z + λ) − f(z)|^p dσ = 0` (5.4), `λ` complex.
Modelling: `1 ≤ p < ∞` (LV's `L^p`, §4.4) with a real exponent `p`. -/
theorem eq3_5_4 {p : ℝ} (hp : 1 ≤ p) {f : ℂ → ℂ} (hf : MemLp f (ENNReal.ofReal p) volume) :
    Tendsto (fun t : ℂ => ∫⁻ z, ‖f (z + t) - f z‖ₑ ^ p) (𝓝 0) (𝓝 0) := by
  sorry

/-! ## §5.6 Approximation in the `L^p` metric -/

/-- **Lemma 5.1** (Ch. III §5.6). Let `ϑₙ`, `n = 1, 2, …`, be finite non-negative continuous functions which vanish
outside the squares `Qₙ = {x + iy | −1/n < x < 1/n, −1/n < y < 1/n}` and satisfy `∬_Ω ϑₙ dσ = 1` (5.8). If
`f ∈ L^p` in the finite plane `Ω`, then `lim_{n → ∞} ∬_Ω |f − f * ϑₙ|^p dσ = 0` (5.9).
Modelling: `ϑₙ` real-valued; the hypotheses are made for `n ≥ 1` (the book's indexing); `1 ≤ p < ∞` with a real
exponent; `f * ϑₙ` is `f ⋆[L] ϑₙ` (module docstring). -/
theorem lemma3_5_1 {ϑ : ℕ → ℂ → ℝ}
    (hϑ : ∀ n : ℕ, 0 < n → Continuous (ϑ n) ∧ (∀ z, 0 ≤ ϑ n z) ∧
      (∀ z : ℂ, ϑ n z ≠ 0 → |z.re| < (n : ℝ)⁻¹ ∧ |z.im| < (n : ℝ)⁻¹) ∧ ∫ z, ϑ n z = 1)
    {p : ℝ} (hp : 1 ≤ p) {f : ℂ → ℂ} (hf : MemLp f (ENNReal.ofReal p) volume) :
    Tendsto (fun n => ∫⁻ z, ‖f z - (f ⋆[(lsmul ℝ ℝ).flip] ϑ n) z‖ₑ ^ p) atTop (𝓝 0) := by
  sorry

/-! ## §5.7 `L^p`-approximation by `C_0^∞`-functions -/

/-- **Definition** (the functions `ϑₙ` of (5.11), Ch. III §5.7). For `n = 1, 2, …`,
`ϑₙ(z) = aₙ e^{1/(|z|² − n⁻²)}` for `|z| < 1/n` and `ϑₙ(z) = 0` for `|z| ≥ 1/n`, where the constant `aₙ` is chosen so
that (5.8) `∬ ϑₙ dσ = 1` holds: `aₙ` is the reciprocal of the integral of `e^{1/(|z|² − n⁻²)}` over the disc
`|z| < 1/n`. Junk value: for `n = 0` (outside the book's range `n ≥ 1`) the function is identically `0`. -/
def lvMollifier (n : ℕ) (z : ℂ) : ℝ :=
  if ‖z‖ < (n : ℝ)⁻¹ then
    (∫ ζ in Metric.ball (0 : ℂ) (n : ℝ)⁻¹, Real.exp (1 / (‖ζ‖ ^ 2 - ((n : ℝ)⁻¹) ^ 2)))⁻¹ *
      Real.exp (1 / (‖z‖ ^ 2 - ((n : ℝ)⁻¹) ^ 2))
  else 0

/-! ## §5.8 Pointwise convergence of an `L^p`-approximation -/

/-- **Lemma 5.2** (Ch. III §5.8). Let the integrable function `f` be finite and continuous in an open set `G`. Then
`f(z) = lim_{n → ∞} f * ϑₙ(z)` (5.12), the convergence being uniform in every compact subset `F` of `G`.
Modelling: `f` is integrable over the finite plane and finite `ℂ`-valued; `ϑₙ` is any sequence with the properties
of 5.6 (as in `lemma3_5_1`), the proof using nothing else, the functions (5.11) (`lvMollifier`) being one such
sequence. -/
theorem lemma3_5_2 {ϑ : ℕ → ℂ → ℝ}
    (hϑ : ∀ n : ℕ, 0 < n → Continuous (ϑ n) ∧ (∀ z, 0 ≤ ϑ n z) ∧
      (∀ z : ℂ, ϑ n z ≠ 0 → |z.re| < (n : ℝ)⁻¹ ∧ |z.im| < (n : ℝ)⁻¹) ∧ ∫ z, ϑ n z = 1)
    {f : ℂ → ℂ} (hf : Integrable f volume) {G : Set ℂ} (hG : IsOpen G) (hfG : ContinuousOn f G) :
    ∀ F ⊆ G, IsCompact F → TendstoUniformlyOn (fun n => f ⋆[(lsmul ℝ ℝ).flip] ϑ n) f atTop F := by
  sorry

end LehtoVirtanen1973
