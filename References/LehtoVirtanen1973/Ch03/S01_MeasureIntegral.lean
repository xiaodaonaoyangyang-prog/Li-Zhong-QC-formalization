import LiZhongQC.Ch01.S09_AnalyticProperties

/-!
# Lehto–Virtanen, Chapter III §1: Measure and integral

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. III §1
(pp. 110–117; `full.md` P1:3225–3420).

Chapter III works in the finite plane `ℂ` (footnote 32) and on the real line. LV's outer measures `μ*` (axioms 1–5)
are Mathlib measures applied to arbitrary sets (the measure of a set is the infimum of the measures of its measurable
supersets): the Lebesgue outer measures are `volume` on `ℝ`, `ℂ` and `ℂ × ℂ`, the Hausdorff outer measures are
`μH[α]`. LV's *measurable* sets (Carathéodory) are the null-measurable sets `NullMeasurableSet A μ` (the two notions
agree on σ-finite sets); *Borel* sets are the `MeasurableSet`s of the Borel σ-algebra. A measurable function on `A`
is `AEStronglyMeasurable` (or `AEMeasurable`) for the measure restricted to `A`; a Borel function is `Measurable`.
LV's real and complex functions may take infinite values; here they are finite `ℂ`-valued (real ones through
`ℝ ⊂ ℂ`), and non-negative integrands are `ℝ≥0∞`-valued (leader decision D2). Integrals of non-negative functions
are lower Lebesgue integrals `∫⁻` (whose `0 · ∞ = 0` is LV's convention); the Bochner integral `∫` is used only for
integrable functions. A point `x + iy` of the plane is written `⟨x, y⟩`.

* Definition (outer measure, axioms 1–3; outer measure in the sense of Carathéodory, axiom 4, §1.1, footnote 31) —
  exists: `MeasureTheory.OuterMeasure`, `MeasureTheory.OuterMeasure.IsMetric` (values in [0, ∞], which axioms 1
  and 2 force; IsMetric is additivity for sets at a positive distance, axiom 4)
* Definition (regular outer measure, axiom 5, §1.1) — omitted: no statement quantifies over abstract outer measures;
  the outer measures used, the Lebesgue and Hausdorff measures, satisfy axiom 5
* Definition (Lebesgue outer linear, area and volume measures `l*`, `m*`, §1.1, footnote 32) — exists:
  `MeasureTheory.MeasureSpace.volume` (on ℝ, on ℂ and on ℂ × ℂ = R⁴, applied to arbitrary sets; for Lebesgue
  measure the infimum over measurable supersets is the infimum over covers by open rectangles or intervals)
* Definition (measurable set, measure, completely additive class, null set, almost everywhere, §1.2) — exists:
  `MeasureTheory.OuterMeasure.IsCaratheodory`, `MeasureTheory.NullMeasurableSet`, `MeasurableSpace`,
  `MeasureTheory.ae` (Carathéodory measurability, which for the σ-finite sets of the book is null-measurability for
  the measure; a null set is a set of measure zero)
* Definition (Borel sets, §1.2, footnote 33) — exists: `MeasurableSet`, `borel`, `MeasurableEmbedding.subtype_coe`,
  `Subtype.borelSpace` (the sets of the Borel σ-algebra; footnote 33, cited P1:3433: the Borel sets of a Borel
  subspace are its Borel subsets, i.e. the subspace σ-algebra is the Borel σ-algebra of the subspace and the
  inclusion of a Borel set is a measurable embedding)
* Unlabelled (§1.2, P1:3245–3255; cited P1:3625): under axioms 1–4 the open, closed and Borel sets are measurable,
  the measurable sets form a completely additive class and the measure is completely additive on it — exists:
  `MeasureTheory.OuterMeasure.IsMetric.borel_le_caratheodory`, `MeasureTheory.OuterMeasure.caratheodory` (a metric
  outer measure is Carathéodory-measurable on the Borel sets; the Carathéodory sets form a σ-algebra on which the
  outer measure is a measure)
* Unlabelled (§1.2, P1:3255): every set is contained in a Borel set of the same outer measure — exists:
  `MeasureTheory.exists_measurable_superset` (for every measure and every set)
* Unlabelled (§1.2, P1:3257, quoted from Munroe): continuity of the outer measure along non-decreasing sequences of
  arbitrary sets, and of the measure along non-increasing sequences of measurable sets with `μ(A₁) < ∞` — exists:
  `MeasureTheory.tendsto_measure_iUnion_atTop`, `MeasureTheory.tendsto_measure_iInter_atTop` (the second assumes only
  null-measurable sets, some member of which has finite measure)
* Definition (σ-finite set, §1.2) — exists: `MeasureTheory.SigmaFinite` (of the measure restricted to the set; for
  every set this is equivalent to being a countable union of sets of finite outer measure)
* Unlabelled (§1.2, P1:3259): for a σ-finite measurable set `A` there are Borel sets `B₁ ⊂ A ⊂ B₂` with
  `μ(B₂ − B₁) = 0`, `B₁` a countable union of closed sets, and closed sets `Fₙ ⊂ A` with `μ(Fₙ) → μ(A)` —
  `sigmaFinite_borel_sandwich`
* Unlabelled (§1.2, P1:3261): if the space is a countable union of open sets of finite measure, `A` is measurable if
  and only if for every `ε > 0` there are a closed `F ⊂ A` and an open `G ⊃ A` with `μ(G − F) < ε` —
  `measurable_iff_closed_open_approx`
* Definition (inner measure, §1.2) — omitted: used later only at P2:307 (V.3.7, examples), where "inner area
  zero" restates V.3.1's "every compact subset has zero area"
* Definition (measurable function, Borel function, characteristic function, §1.3) — exists:
  `MeasureTheory.NullMeasurable`, `Measurable`, `Set.indicator` (preimages of open sets are measurable; for the real,
  complex and ℝ≥0∞-valued functions of the book this is AEMeasurable, equivalently AEStronglyMeasurable, for the
  measure restricted to the set of definition; the characteristic function of A is the indicator of A of the
  constant 1)
* Egoroff's theorem (§1.3) — `egoroff_theorem`
* Definition (integral of a non-negative function, integrable function, integral of a real or complex function,
  §1.4; Lebesgue integrals, §1.5) — exists: `MeasureTheory.lintegral`, `MeasureTheory.Integrable`,
  `MeasureTheory.integral` (the book's supremum over finite measurable partitions is the lower Lebesgue integral of
  an ℝ≥0∞-valued function; the Bochner integral of an integrable function is the book's integral)
* Unlabelled (§1.4, P1:3285; cited P1:3543 "by the remark made in 1.4"): over a σ-finite set the partitions in the
  definition of the integral may be taken Borel — exists: `MeasureTheory.lintegral_def` (the lower integral is by
  definition the supremum over the simple functions below the integrand, whose level sets are measurable)
* Fubini's theorem (§1.5, quoted from Munroe; footnote 34) — `fubini_theorem_i`, `fubini_theorem_ii`
* Fubini's theorem for R⁴ = ℂ × ℂ, formulas (1.1)′ and (1.2)′ (§1.5) — exists: `MeasureTheory.lintegral_lintegral_swap`,
  `MeasureTheory.integral_integral_swap` (for the area measures restricted to the two rectangles, whose product is
  the four-dimensional Lebesgue measure restricted to the product rectangle; measurability and integrability in R
  refer to that product measure)
* Lebesgue convergence theorem (§1.5, quoted from Munroe) — exists:
  `MeasureTheory.tendsto_integral_of_dominated_convergence` (for the area measure restricted to A and the limit
  function 0; the finiteness of the area of A is not needed)
* Definition (point of linear density, point of density of a plane set, §1.6) — `IsLinearDensityPoint`,
  `IsDensityPoint`
* Unlabelled (§1.6, P1:3367, quoted from Munroe and Saks): almost every point of a set of the line, resp. of the
  plane, is a point of density of the set — `lebesgue_density_theorem_i`, `lebesgue_density_theorem_ii`
* Definition (x-, y- and xy-point of density, §1.6) — `IsXDensityPoint`, `IsYDensityPoint`, `IsXYDensityPoint`
* Lemma 1.1 (§1.6, quoted from Saks) — `lemma3_1_1`
* Definition (α-dimensional Hausdorff outer measure, Hausdorff measure, §1.7) — exists:
  `MeasureTheory.Measure.hausdorffMeasure` (without a normalizing constant, as in the book; for α > 0 coverings by
  arbitrary sets of diameter at most r give the same outer measure as LV's coverings by open sets of diameter less
  than d)
* Definition (dimension, §1.7) — exists: `dimH` (the supremum of the exponents for which the Hausdorff measure is
  infinite)
* Unlabelled (§1.7, P1:3387–3393): `μ*_α(A)` does not increase with `α`, is positive and finite for at most one `α`,
  vanishes for `α > dim A` and is infinite for `α < dim A` — exists: `MeasureTheory.Measure.hausdorffMeasure_mono`,
  `MeasureTheory.Measure.hausdorffMeasure_zero_or_top`, `hausdorffMeasure_of_dimH_lt`, `hausdorffMeasure_of_lt_dimH`
  (the last two for non-negative exponents, which covers LV's α > 0)
* Lemma 1.2 (§1.7) — `lemma3_1_2`, `lemma3_1_2_interval` (corrected, false as printed: the true inequality and the
  case of a segment factor, which IV.2.2 uses, are stated)
* Definition (linear measure `l = μ₁`, §1.8) — exists: `MeasureTheory.Measure.hausdorffMeasure`,
  `MeasureTheory.hausdorffMeasure_real`, `Isometry.hausdorffMeasure_image` (the one-dimensional Hausdorff measure;
  on the real line it is the Lebesgue measure, and on every line of the plane it agrees with the Lebesgue linear
  measure by isometry invariance)
* Unlabelled (§1.8, P1:3403): a set of finite linear measure has area zero and (Gross) meets almost every horizontal
  line in finitely many points — `area_eq_zero_of_linearMeasure_lt_top`, `gross_finite_sections`
* Lemma 1.3 (§1.8) — `lemma3_1_3`

The remaining characterizations of measurability by the inner measure (P1:3261), the measurability criteria for
functions (P1:3265–3267), the remark of §1.4 that integrable functions are finite almost everywhere (P1:3293), the
agreement of `μ₁` with the Lebesgue linear measure on lines (P1:3401, the pointer `MeasureTheory.hausdorffMeasure_real`
above) and the intermediate claim of §1.8 that `l(A(y₀)) = 0` for almost all `y₀` (implied by Gross's claim) are used
only inside proofs and are not stated (inventory: omitted).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (closedRect openRect)

/-! ## §1.2 Measurable sets -/

/-- **Unlabelled** (Ch. III §1.2, P1:3259, cf. Munroe). Let `A` be a σ-finite measurable set. Then there are Borel
sets `B₁ ⊂ A ⊂ B₂` with `μ(B₂ − B₁) = 0`, where `B₁` can be chosen as a countable union of closed sets; hence there
is a sequence of closed sets `Fₙ ⊂ A` with `lim μ(Fₙ) = μ(A)`.
Modelling: the space is the finite plane and `μ` any measure on it (the book: any outer measure satisfying axioms
1–5; the uses are the area measure and the linear measure); "measurable" is null-measurable, "σ-finite" is the
σ-finiteness of `μ` restricted to `A`. -/
theorem sigmaFinite_borel_sandwich (μ : Measure ℂ) {A : Set ℂ} (hA : NullMeasurableSet A μ)
    (hσ : SigmaFinite (μ.restrict A)) :
    (∃ B₁ B₂ : Set ℂ, MeasurableSet B₁ ∧ MeasurableSet B₂ ∧ B₁ ⊆ A ∧ A ⊆ B₂ ∧ μ (B₂ \ B₁) = 0 ∧
      ∃ F : ℕ → Set ℂ, (∀ n, IsClosed (F n)) ∧ B₁ = ⋃ n, F n) ∧
    ∃ F : ℕ → Set ℂ, (∀ n, IsClosed (F n) ∧ F n ⊆ A) ∧ Tendsto (fun n => μ (F n)) atTop (𝓝 (μ A)) := by
  sorry

/-- **Unlabelled** (Ch. III §1.2, P1:3261, cf. Munroe). If the space is the union of countably many open sets with
finite measure (as for the Lebesgue measure), then a set `A` is measurable if and only if to every `ε > 0` there
correspond a closed set `F ⊂ A` and an open set `G ⊃ A` such that `μ(G − F) < ε`.
Modelling: the space is the finite plane and `μ` any measure on it; "measurable" is null-measurable (under the
hypothesis every set is σ-finite, so this is Carathéodory measurability). -/
theorem measurable_iff_closed_open_approx (μ : Measure ℂ)
    (hΩ : ∃ G : ℕ → Set ℂ, (∀ n, IsOpen (G n) ∧ μ (G n) < ⊤) ∧ ⋃ n, G n = univ) (A : Set ℂ) :
    NullMeasurableSet A μ ↔ ∀ ε : ℝ, 0 < ε → ∃ F G : Set ℂ, IsClosed F ∧ F ⊆ A ∧ IsOpen G ∧ A ⊆ G ∧
      μ (G \ F) < ENNReal.ofReal ε := by
  sorry

/-! ## §1.3 Measurable functions -/

/-- **Egoroff's theorem** (Ch. III §1.3, for the Lebesgue area measure). Let `fₙ` be a sequence of real or complex
measurable functions which converges almost everywhere in a set `A` of finite measure to a finite function `f`. Then
for every `ε > 0` there exists a closed set `F ⊂ A`, with `m(A − F) < ε`, where the convergence is uniform.
Modelling: `A` measurable (null-measurable) of finite area; the `fₙ` measurable in `A` (for the area measure
restricted to `A`); the functions are finite `ℂ`-valued (D2). -/
theorem egoroff_theorem {A : Set ℂ} (hA : NullMeasurableSet A volume) (hAfin : volume A ≠ ⊤)
    {fn : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hfn : ∀ n, AEStronglyMeasurable (fn n) (volume.restrict A))
    (hconv : ∀ᵐ z ∂(volume.restrict A), Tendsto (fun n => fn n z) atTop (𝓝 (f z))) {ε : ℝ} (hε : 0 < ε) :
    ∃ F ⊆ A, IsClosed F ∧ volume (A \ F) < ENNReal.ofReal ε ∧ TendstoUniformlyOn fn f atTop F := by
  -- measurable representatives and the exceptional null set
  have hfin : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.2 hAfin
  have hfm : AEStronglyMeasurable f (volume.restrict A) := aestronglyMeasurable_of_tendsto_ae atTop hfn hconv
  have hg : ∀ n, StronglyMeasurable ((hfn n).mk (fn n)) := fun n => (hfn n).stronglyMeasurable_mk
  have hgood : ∀ᵐ z ∂(volume.restrict A), (∀ n, fn n z = (hfn n).mk (fn n) z) ∧ f z = hfm.mk f z := by
    filter_upwards [ae_all_iff.2 fun n => (hfn n).ae_eq_mk, hfm.ae_eq_mk] with z h1 h2 using ⟨h1, h2⟩
  have hconv' : ∀ᵐ z ∂(volume.restrict A), Tendsto (fun n => (hfn n).mk (fn n) z) atTop (𝓝 (hfm.mk f z)) := by
    filter_upwards [hgood, hconv] with z h1 h2
    simp only [← h1.1, ← h1.2]
    exact h2
  -- Egorov for the finite measure `m|A`
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨t, htm, htμ, hunif⟩ := tendstoUniformlyOn_of_ae_tendsto'
    (fun n => (hg n).aestronglyMeasurable) hconv' (ENNReal.ofReal_pos.2 hε3)
  -- a measurable core of `A` avoiding `t` and the exceptional set
  obtain ⟨A', hA'A, hA'm, hAA'⟩ := hA.exists_measurable_subset_ae_eq
  have hA'v : volume (A \ A') = 0 := (ae_eq_set.1 hAA').2
  have hbad : volume ({z | ¬ ((∀ n, fn n z = (hfn n).mk (fn n) z) ∧ f z = hfm.mk f z)} ∩ A) = 0 := by
    rw [← Measure.restrict_apply₀' hA]
    exact ae_iff.1 hgood
  obtain ⟨M, hMsub, hMm, hM0⟩ := exists_measurable_superset_of_null hbad
  set S := A' \ (t ∪ M) with hSdef
  have hSm : MeasurableSet S := hA'm.diff (htm.union hMm)
  have hSfin : volume S ≠ ⊤ :=
    ((measure_mono (sdiff_subset.trans hA'A)).trans_lt (lt_top_iff_ne_top.2 hAfin)).ne
  obtain ⟨F, hFS, hFc, hFm⟩ := hSm.exists_isClosed_sdiff_lt hSfin (ENNReal.ofReal_pos.2 hε3).ne'
  have hFA : F ⊆ A := hFS.trans (sdiff_subset.trans hA'A)
  refine ⟨F, hFA, hFc, ?_, ?_⟩
  · -- `A \ F ⊆ (A \ A') ∪ (A ∩ t) ∪ M ∪ (S \ F)`
    have hsub : A \ F ⊆ (A \ A') ∪ (t ∩ A) ∪ M ∪ (S \ F) := by
      rintro z ⟨hzA, hzF⟩
      by_cases h1 : z ∈ A'
      · by_cases h2 : z ∈ t
        · exact Or.inl (Or.inl (Or.inr ⟨h2, hzA⟩))
        · by_cases h3 : z ∈ M
          · exact Or.inl (Or.inr h3)
          · exact Or.inr ⟨⟨h1, fun h => h.elim h2 h3⟩, hzF⟩
      · exact Or.inl (Or.inl (Or.inl ⟨hzA, h1⟩))
    have htA : volume (t ∩ A) ≤ ENNReal.ofReal (ε / 3) := by
      rw [← Measure.restrict_apply htm]
      exact htμ
    calc volume (A \ F) ≤ volume ((A \ A') ∪ (t ∩ A) ∪ M ∪ (S \ F)) := measure_mono hsub
      _ ≤ volume ((A \ A') ∪ (t ∩ A) ∪ M) + volume (S \ F) := measure_union_le _ _
      _ ≤ volume ((A \ A') ∪ (t ∩ A)) + volume M + volume (S \ F) := by
          gcongr
          exact measure_union_le _ _
      _ ≤ volume (A \ A') + volume (t ∩ A) + volume M + volume (S \ F) := by
          gcongr
          exact measure_union_le _ _
      _ = volume (t ∩ A) + volume (S \ F) := by rw [hA'v, hM0, zero_add, add_zero]
      _ < ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) :=
          ENNReal.add_lt_add_of_le_of_lt (htA.trans_lt ENNReal.ofReal_lt_top).ne htA hFm
      _ ≤ ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add hε3.le hε3.le]
          exact ENNReal.ofReal_le_ofReal (by linarith)
  · -- on `F` the functions agree with the representatives, which converge uniformly off `t`
    have hFt : F ⊆ tᶜ := fun z hz h => (hFS hz).2 (Or.inl h)
    have hgoodF : ∀ z ∈ F, (∀ n, fn n z = (hfn n).mk (fn n) z) ∧ f z = hfm.mk f z := fun z hz => by
      by_contra h
      exact (hFS hz).2 (Or.inr (hMsub ⟨h, hFA hz⟩))
    refine (hunif.mono hFt).congr (Eventually.of_forall fun n z hz => ((hgoodF z hz).1 n).symm) |>.congr_right ?_
    exact fun z hz => ((hgoodF z hz).2).symm

/-! ## §1.5 Lebesgue integrals -/

/-- **Fubini's theorem** (Ch. III §1.5, quoted from Munroe), first part. Let `f` be a real or complex measurable
function in the rectangle `R = {x + iy | x₁ < x < x₂, y₁ < y < y₂}`. Then `f` is measurable as a function of `x` for
almost all `y ∈ (y₁, y₂)` and as a function of `y` for almost all `x ∈ (x₁, x₂)`; the integrals
`∫_{y₁}^{y₂} |f(x, y)| dy` and `∫_{x₁}^{x₂} |f(x, y)| dx` are measurable as functions of `x` and `y`, respectively,
and (1.1) `∬_R |f| dσ = ∫ dx ∫ |f| dy = ∫ dy ∫ |f| dx`.
Modelling: `f` finite `ℂ`-valued (D2), measurable for the area measure restricted to `R`; the integrals of `|f|` are
`ℝ≥0∞`-valued. -/
theorem fubini_theorem_i {x₁ x₂ y₁ y₂ : ℝ} {f : ℂ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict (openRect x₁ x₂ y₁ y₂))) :
    (∀ᵐ y ∂(volume.restrict (Ioo y₁ y₂)),
      AEStronglyMeasurable (fun x : ℝ => f ⟨x, y⟩) (volume.restrict (Ioo x₁ x₂))) ∧
    (∀ᵐ x ∂(volume.restrict (Ioo x₁ x₂)),
      AEStronglyMeasurable (fun y : ℝ => f ⟨x, y⟩) (volume.restrict (Ioo y₁ y₂))) ∧
    AEMeasurable (fun x : ℝ => ∫⁻ y in Ioo y₁ y₂, ‖f ⟨x, y⟩‖ₑ) (volume.restrict (Ioo x₁ x₂)) ∧
    AEMeasurable (fun y : ℝ => ∫⁻ x in Ioo x₁ x₂, ‖f ⟨x, y⟩‖ₑ) (volume.restrict (Ioo y₁ y₂)) ∧
    (∫⁻ z in openRect x₁ x₂ y₁ y₂, ‖f z‖ₑ) = (∫⁻ x in Ioo x₁ x₂, ∫⁻ y in Ioo y₁ y₂, ‖f ⟨x, y⟩‖ₑ) ∧
    (∫⁻ z in openRect x₁ x₂ y₁ y₂, ‖f z‖ₑ) = ∫⁻ y in Ioo y₁ y₂, ∫⁻ x in Ioo x₁ x₂, ‖f ⟨x, y⟩‖ₑ := by
  -- transport to `ℝ × ℝ` by `z ↦ (re z, im z)`
  set e := Complex.measurableEquivRealProd with hedef
  have hR : openRect x₁ x₂ y₁ y₂ = e ⁻¹' (Ioo x₁ x₂ ×ˢ Ioo y₁ y₂) := by
    ext z
    simp [openRect, hedef, and_assoc]
  have hP : (volume : Measure (ℝ × ℝ)).restrict (Ioo x₁ x₂ ×ˢ Ioo y₁ y₂) =
      (volume.restrict (Ioo x₁ x₂)).prod (volume.restrict (Ioo y₁ y₂)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have he : MeasurePreserving e (volume.restrict (openRect x₁ x₂ y₁ y₂))
      ((volume.restrict (Ioo x₁ x₂)).prod (volume.restrict (Ioo y₁ y₂))) := by
    rw [hR, ← hP]
    exact Complex.volume_preserving_equiv_real_prod.restrict_preimage (measurableSet_Ioo.prod measurableSet_Ioo)
  have he' := MeasurePreserving.symm e he
  have hF : AEStronglyMeasurable (fun p : ℝ × ℝ => f ⟨p.1, p.2⟩)
      ((volume.restrict (Ioo x₁ x₂)).prod (volume.restrict (Ioo y₁ y₂))) := hf.comp_measurePreserving he'
  have hint : (∫⁻ z in openRect x₁ x₂ y₁ y₂, ‖f z‖ₑ) =
      ∫⁻ p, ‖f ⟨p.1, p.2⟩‖ₑ ∂((volume.restrict (Ioo x₁ x₂)).prod (volume.restrict (Ioo y₁ y₂))) :=
    (he'.lintegral_comp_emb e.symm.measurableEmbedding (fun z => ‖f z‖ₑ)).symm
  refine ⟨hF.prod_swap.prodMk_left, hF.prodMk_left, hF.enorm.lintegral_prod_right',
    hF.enorm.lintegral_prod_left', ?_, ?_⟩
  · rw [hint, lintegral_prod _ hF.enorm]
  · rw [hint, lintegral_prod_symm _ hF.enorm]

/-- **Fubini's theorem** (Ch. III §1.5, quoted from Munroe), second part. If `f` is integrable in the rectangle
`R = {x + iy | x₁ < x < x₂, y₁ < y < y₂}`, then the functions defined by the integrals `∫_{y₁}^{y₂} f(x, y) dy` and
`∫_{x₁}^{x₂} f(x, y) dx` (which exist for almost all `x` and `y`, respectively, footnote 34) are integrable in
`x₁ < x < x₂` and `y₁ < y < y₂`, respectively, and (1.2) `∬_R f dσ = ∫ dx ∫ f dy = ∫ dy ∫ f dx`.
Modelling: `f` finite `ℂ`-valued (D2); the almost-everywhere integrability of the sections (footnote 34) is stated,
so the partial integrals are the book's ones outside a null set. -/
theorem fubini_theorem_ii {x₁ x₂ y₁ y₂ : ℝ} {f : ℂ → ℂ} (hf : IntegrableOn f (openRect x₁ x₂ y₁ y₂)) :
    (∀ᵐ x ∂(volume.restrict (Ioo x₁ x₂)), IntegrableOn (fun y : ℝ => f ⟨x, y⟩) (Ioo y₁ y₂)) ∧
    (∀ᵐ y ∂(volume.restrict (Ioo y₁ y₂)), IntegrableOn (fun x : ℝ => f ⟨x, y⟩) (Ioo x₁ x₂)) ∧
    IntegrableOn (fun x : ℝ => ∫ y in Ioo y₁ y₂, f ⟨x, y⟩) (Ioo x₁ x₂) ∧
    IntegrableOn (fun y : ℝ => ∫ x in Ioo x₁ x₂, f ⟨x, y⟩) (Ioo y₁ y₂) ∧
    (∫ z in openRect x₁ x₂ y₁ y₂, f z) = (∫ x in Ioo x₁ x₂, ∫ y in Ioo y₁ y₂, f ⟨x, y⟩) ∧
    (∫ z in openRect x₁ x₂ y₁ y₂, f z) = ∫ y in Ioo y₁ y₂, ∫ x in Ioo x₁ x₂, f ⟨x, y⟩ := by
  -- transport to `ℝ × ℝ` by `z ↦ (re z, im z)`
  set e := Complex.measurableEquivRealProd with hedef
  have hR : openRect x₁ x₂ y₁ y₂ = e ⁻¹' (Ioo x₁ x₂ ×ˢ Ioo y₁ y₂) := by
    ext z
    simp [openRect, hedef, and_assoc]
  have hP : (volume : Measure (ℝ × ℝ)).restrict (Ioo x₁ x₂ ×ˢ Ioo y₁ y₂) =
      (volume.restrict (Ioo x₁ x₂)).prod (volume.restrict (Ioo y₁ y₂)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have he : MeasurePreserving e (volume.restrict (openRect x₁ x₂ y₁ y₂))
      ((volume.restrict (Ioo x₁ x₂)).prod (volume.restrict (Ioo y₁ y₂))) := by
    rw [hR, ← hP]
    exact Complex.volume_preserving_equiv_real_prod.restrict_preimage (measurableSet_Ioo.prod measurableSet_Ioo)
  have he' := MeasurePreserving.symm e he
  have hF : Integrable (fun p : ℝ × ℝ => f ⟨p.1, p.2⟩)
      ((volume.restrict (Ioo x₁ x₂)).prod (volume.restrict (Ioo y₁ y₂))) :=
    (he'.integrable_comp_emb e.symm.measurableEmbedding).2 hf
  have hint : (∫ z in openRect x₁ x₂ y₁ y₂, f z) =
      ∫ p, f ⟨p.1, p.2⟩ ∂((volume.restrict (Ioo x₁ x₂)).prod (volume.restrict (Ioo y₁ y₂))) :=
    (he'.integral_comp e.symm.measurableEmbedding f).symm
  refine ⟨hF.prod_right_ae, hF.prod_left_ae, hF.integral_prod_left, hF.integral_prod_right, ?_, ?_⟩
  · rw [hint, integral_prod _ hF]
  · rw [hint, integral_prod_symm _ hF]

/-! ## §1.6 Points of density of a set -/

/-- **Definition** (point of linear density, Ch. III §1.6). The finite point `x` is a point of (linear) density of
the set `A` of the line: `S(x) = liminf_{l(I_x) → 0} l*(A ∩ I_x)/l(I_x) = 1`, the lower limit being taken over the
intervals `I_x` which contain `x`.
Modelling: the quotient is at most `1`, so `S(x) = 1` says that for every `ε > 0` the quotient is at least `1 − ε`
for all short intervals containing `x`; this is written without division. Closed intervals `[a, b] ∋ x` represent
all intervals, the endpoints being null sets. `A` is arbitrary (outer measure). -/
def IsLinearDensityPoint (A : Set ℝ) (x : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a ≤ x → x ≤ b → a < b → b - a < δ →
    ENNReal.ofReal ((1 - ε) * (b - a)) ≤ volume (A ∩ Icc a b)

/-- **Definition** (point of density of a plane set, Ch. III §1.6). The finite point `z ∈ A` is a point of density
of the plane set `A`: `liminf_{m(Q_z) → 0} m*(A ∩ Q_z)/m(Q_z) = 1`, over the closed squares `Q_z` which contain `z`
and have sides parallel to the coordinate axes.
Modelling: as in `IsLinearDensityPoint`; the square `[x, x + r] × [y, y + r]` has area `r²`. -/
def IsDensityPoint (A : Set ℂ) (z : ℂ) : Prop :=
  z ∈ A ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y r : ℝ, 0 < r → r < δ →
    z ∈ closedRect x (x + r) y (y + r) →
      ENNReal.ofReal ((1 - ε) * r ^ 2) ≤ volume (A ∩ closedRect x (x + r) y (y + r))

/-- **Unlabelled** (Ch. III §1.6, P1:3367, quoted from Munroe and Saks), the case of the line. Almost every point of
a set `A` of the line is a point of density of `A`. -/
theorem lebesgue_density_theorem_i (A : Set ℝ) : volume {x ∈ A | ¬ IsLinearDensityPoint A x} = 0 := by
  sorry

/-- **Unlabelled** (Ch. III §1.6, P1:3367, quoted from Munroe and Saks), the case of the plane. Almost every point of
a plane set `A` is a point of density of `A`. -/
theorem lebesgue_density_theorem_ii (A : Set ℂ) : volume {z ∈ A | ¬ IsDensityPoint A z} = 0 := by
  sorry

/-- **Definition** (x-point of density, Ch. III §1.6). The finite point `z₀ = x₀ + iy₀` is an x-point of density of
the set `A`: `x₀` is a point of linear density of the one-dimensional set `{x | x + iy₀ ∈ A}`. -/
def IsXDensityPoint (A : Set ℂ) (z₀ : ℂ) : Prop :=
  IsLinearDensityPoint {x : ℝ | (⟨x, z₀.im⟩ : ℂ) ∈ A} z₀.re

/-- **Definition** (y-point of density, Ch. III §1.6). `y₀` is a point of linear density of
`{y | x₀ + iy ∈ A}`. -/
def IsYDensityPoint (A : Set ℂ) (z₀ : ℂ) : Prop :=
  IsLinearDensityPoint {y : ℝ | (⟨z₀.re, y⟩ : ℂ) ∈ A} z₀.im

/-- **Definition** (xy-point of density, Ch. III §1.6): both an x- and a y-point of density. -/
def IsXYDensityPoint (A : Set ℂ) (z₀ : ℂ) : Prop := IsXDensityPoint A z₀ ∧ IsYDensityPoint A z₀

/-- **Lemma 1.1** (Ch. III §1.6, quoted from Saks). Almost all points of a measurable set `A` in the finite plane
are xy-points of density of `A`. -/
theorem lemma3_1_1 {A : Set ℂ} (hA : NullMeasurableSet A volume) :
    volume {z ∈ A | ¬ IsXYDensityPoint A z} = 0 := by
  sorry

/-! ## §1.7 Hausdorff measure -/

/-- **Lemma 1.2** (Ch. III §1.7), the true inequality. Let `A` and `B` be nonempty compact sets on the finite `x`-
and `y`-axes. Then `dim A + dim B ≤ dim (A × B)` (the book's reference for this half is Marstrand).
[CORRECTION] LV's Lemma III.1.2 as printed asserts equality, which is false in general (counterexample: compact A, B
with dim A = dim B = 0 and dim (A × B) ≥ 1, Falconer, Fractal Geometry, Ex. 7.8); stated here: the inequality
`dim A + dim B ≤ dim (A × B)`, and, in `lemma3_1_2_interval`, the equality for a segment factor, the case used in
IV.2.2 (P1:5203).
Modelling: `A`, `B` are subsets of `ℝ` (their dimension on the axes is the same, the axes being isometric to `ℝ`);
`A × B = {x + iy | x ∈ A, y ∈ B}`; nonemptiness is needed (for `A = ∅` the product is empty). -/
theorem lemma3_1_2 {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B) (hA₀ : A.Nonempty) (hB₀ : B.Nonempty) :
    dimH A + dimH B ≤ dimH {z : ℂ | z.re ∈ A ∧ z.im ∈ B} := by
  sorry

/-- **Lemma 1.2** (Ch. III §1.7), the case of a segment factor. Let `A` be a nonempty compact set on the finite
`x`-axis and `[c, d]`, `c < d`, a segment of the `y`-axis. Then `dim (A × [c, d]) = dim A + 1`.
[CORRECTION] LV's Lemma III.1.2 as printed asserts equality, which is false in general (counterexample: compact A, B
with dim A = dim B = 0 and dim (A × B) ≥ 1, Falconer, Fractal Geometry, Ex. 7.8); stated here: the equality when
the second factor is a segment, which is the form used in IV.2.2 (P1:5203), and, in `lemma3_1_2`, the inequality
`dim A + dim B ≤ dim (A × B)`.
Modelling: as in `lemma3_1_2`. -/
theorem lemma3_1_2_interval {A : Set ℝ} (hA : IsCompact A) (hA₀ : A.Nonempty) {c d : ℝ} (hcd : c < d) :
    dimH {z : ℂ | z.re ∈ A ∧ z.im ∈ Icc c d} = dimH A + 1 := by
  sorry

/-! ## §1.8 Linear measure -/

/-- **Unlabelled** (Ch. III §1.8, P1:3403). For a set `A` of finite linear measure the Lebesgue area measure
vanishes. -/
theorem area_eq_zero_of_linearMeasure_lt_top {A : Set ℂ} (hA : μH[1] A < ⊤) : volume A = 0 := by
  -- `μH[2] A = 0`, and `μH[2]` is the area measure up to the bi-Lipschitz identification `ℂ ≃ ℝ²`
  have h2 : μH[2] A = 0 := (Measure.hausdorffMeasure_zero_or_top (by norm_num : (1 : ℝ) < 2) A).resolve_right hA.ne
  set e := Complex.measurableEquivPi with hedef
  have hval : ∀ w : ℂ, e w = ![w.re, w.im] := fun w => by
    ext i
    fin_cases i <;> simp [hedef, Complex.measurableEquivPi]
  have hL : LipschitzWith 1 (e : ℂ → Fin 2 → ℝ) := LipschitzWith.of_dist_le_mul fun z z' => by
    rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg, hval, hval]
    intro i
    fin_cases i
    · simpa [Real.dist_eq, Complex.dist_eq] using Complex.abs_re_le_norm (z - z')
    · simpa [Real.dist_eq, Complex.dist_eq] using Complex.abs_im_le_norm (z - z')
  have h2' : μH[2] (e '' A) = 0 :=
    le_antisymm ((hL.hausdorffMeasure_image_le (by norm_num) A).trans (by simp [h2])) bot_le
  have hvol : volume (e '' A) = 0 := by
    have hpi := hausdorffMeasure_pi_real (ι := Fin 2)
    simp only [Fintype.card_fin, Nat.cast_ofNat] at hpi
    rw [← hpi]
    exact h2'
  calc volume A = volume (e ⁻¹' (e '' A)) := by rw [e.preimage_image]
    _ = volume (e '' A) := Complex.volume_preserving_equiv_pi.measure_preimage_equiv _
    _ = 0 := hvol

/-- **Unlabelled** (Ch. III §1.8, P1:3403, Gross). If the set `A` has finite linear measure, then on every horizontal
line `y = y₀` there is only a finite number of points of `A`, with the possible exception of a null set of values
`y₀`. (Its source, Lemma 1.3, is cited as "Lemma III.4.3" at P2:221, a misprint for Lemma III.1.3.) -/
theorem gross_finite_sections {A : Set ℂ} (hA : μH[1] A < ⊤) :
    ∀ᵐ y ∂(volume : Measure ℝ), {x : ℝ | (⟨x, y⟩ : ℂ) ∈ A}.Finite := by
  sorry

/-- **Lemma 1.3** (Ch. III §1.8). Let `A` be a plane set, `N` a positive integer, and `E` the set of values `y₀` for
which `A(y₀) = {x | x + iy₀ ∈ A}` contains at least `N` points. Then `l*(E) ≤ l*(A)/N`.
Modelling: multiplied out, `N · l*(E) ≤ l*(A)`; on the left `l*` is the Lebesgue outer measure of the line, on the
right the (Hausdorff) linear outer measure of the plane set `A`; no measurability is assumed. Its consequence,
Gross's claim (P1:3403, `gross_finite_sections`), is applied in V.3, where P2:221 cites it as "Lemma III.4.3" (a
misprint for III.1.3). -/
theorem lemma3_1_3 (A : Set ℂ) {N : ℕ} (hN : 0 < N) :
    (N : ℝ≥0∞) * volume {y : ℝ | (N : ℕ∞) ≤ {x : ℝ | (⟨x, y⟩ : ℂ) ∈ A}.encard} ≤ μH[1] A := by
  sorry

end LehtoVirtanen1973
