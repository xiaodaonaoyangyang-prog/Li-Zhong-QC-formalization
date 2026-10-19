import References.LehtoVirtanen1973.Ch01.S01_TopologicalProperties
import References.LehtoVirtanen1973.Ch03.S01_MeasureIntegral

/-!
# Lehto–Virtanen, Chapter III §2: Absolute continuity

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. III §2
(pp. 117–127; `full.md` P1:3421–3704).

Conventions (see also §1). Completely additive set functions on the Borel sets are Mathlib measures (the non-negative
ones) and signed measures (the bounded real ones). Absolute continuity is LV's ε–δ condition (`IsAbsContIn`), not
the null-set relation `≪`. In §2.1–2.2 the book works with Borel sets `E`, `E′` of the finite plane and one Hausdorff
or Lebesgue measure `μ`; here `E` and `E′` are Borel sets of arbitrary Borel spaces `X` and `Y`, with a measure `μ`
on `X` (for absolute continuity) and a measure `ν` on `Y` (in `μ_f(B) = ν(f(B ∩ E))`), so that both later settings
are instances. From §2.3 on (P1:3461) `E` is either a domain of the finite plane with the area measure
(`X = Y = ℂ`, `μ = ν = volume`) or a bounded or unbounded segment with the linear measure: the segment is taken on the
real line (`X = ℝ` with `volume`, which is the linear measure there) and its image, a Jordan arc, lies in `Y = ℂ` with
the linear measure `μH[1]`. Both settings are stated, as paired declarations (leader decision D3): `_i` for domains
and `_ii` for segments (in Lemma 2.1: `_i`, `_ii` for domains and `_iii`, `_iv` for segments). A homeomorphism `f`
of `E` onto `f(E)` is `IsEmbedding (E.domRestrict f)`, for a domain `G` of the finite plane
`LiZhongQC.IsHomeomorphOnto f G (f '' G)`, and for a segment `IsArcParam I f`. The derivative `τ′(z)` of a set
function is the limit of `τ(Q_z ∩ E)/μ(Q_z)` over the closed squares (domains) or closed intervals (segments)
`Q_z ∋ z`; `setFnDeriv`, `setFnDerivReal` and `arealDeriv` return it where it exists and the junk value `0`
elsewhere, and every statement using them asserts its existence almost everywhere. Likewise `deriv` of an arc length
appears only together with the assertion that the arc length is differentiable almost everywhere.

* Definition (absolutely continuous and locally absolutely continuous set function in `E`, §2.1) — `IsAbsContIn`,
  `IsLocAbsContIn`
* Unlabelled (§2.1, P1:3425–3427, quoted from Munroe): a bounded completely additive set function is absolutely
  continuous in `E` if and only if it vanishes on the Borel null sets contained in `E` — `absCont_iff_null`
* Unlabelled (§2.1, P1:3429; cited "see 2.1" at P1:4223, used P1:4637, 5929): the integral of an integrable function
  is an absolutely continuous set function — exists: `MeasureTheory.exists_pos_setLIntegral_lt_of_measure_lt` (for
  a non-negative integrand with finite integral: for every ε > 0 there is δ > 0 such that the integral over s is
  less than ε for every set s of measure less than δ, no measurability of s being required; a complex integrand
  through its norm; "locally" at P1:4637, 5929 is the restriction to compact subsets)
* Radon–Nikodym theorem (§2.1, quoted from Munroe) — `radon_nikodym_theorem`
* Definition (the set function `μ_f` of a homeomorphism; absolutely continuous and locally absolutely continuous
  homeomorphism, §2.2; a homeomorphism of a segment onto a Jordan arc of the finite plane, the parametric
  representation of I.1.3) — `homeoSetFn`, `IsAbsContHomeo`, `IsLocAbsContHomeo`, `IsArcParam`
* Unlabelled (§2.2, P1:3441; used P1:3855, 3871, P2:239): the set function `μ_f` has all the properties of a
  measure; hence, when it is bounded, `f` is absolutely continuous if and only if it maps the null sets onto null
  sets — `homeoSetFn_eq_measure`, `absContHomeo_iff_null`
* Unlabelled (§2.2–2.3, P1:3447, 3463): an absolutely continuous homeomorphism maps all null sets onto null sets, and
  so does a locally absolutely continuous one when `E` is a domain or a segment — `absContHomeo_null`,
  `locAbsContHomeo_null_i`, `locAbsContHomeo_null_ii`
* Unlabelled (§2.2–2.3, P1:3453, 3463): an absolutely continuous homeomorphism maps every σ-finite measurable set onto
  a measurable set, and so does a locally absolutely continuous one when `E` is a domain or a segment —
  `absContHomeo_measurable`, `locAbsContHomeo_measurable_i`, `locAbsContHomeo_measurable_ii`
* Definition (derivative `τ′(z)` of a set function, §2.3) — `HasSetFnDerivAt`, `setFnDeriv`, `HasSetFnDerivAtReal`,
  `setFnDerivReal`
* Theorem of Lebesgue (§2.3, quoted from Saks), with formula (2.1) — `lebesgue_theorem_setFn_i`,
  `lebesgue_theorem_setFn_ii`
* Definition (areal derivative `μ′_f`, §2.4, footnote 35) — `arealDeriv`
* Formula (2.2) (§2.4) — `eq3_2_2_i`, `eq3_2_2_ii`
* Formula (2.3) (§2.4) — `eq3_2_3_i`, `eq3_2_3_ii`
* Lemma 2.1 (§2.5), with formula (2.4) (cited by number at P1:3877) — `lemma3_2_1_i`, `lemma3_2_1_ii`,
  `lemma3_2_1_iii`, `lemma3_2_1_iv`
* Definition (rectifiable arc and its length `l(C)`, locally rectifiable arc, rectifiable Jordan curve, §2.6) —
  `IsRectifiableArc`, `IsLocRectifiableArc`, `IsRectifiableJordanCurve`
* Definition (arc length `s`, length-preserving parametrization `ζ`, §2.6) — `IsArcLengthFn`,
  `IsLengthPreservingParam`
* Unlabelled (§2.6, P1:3589; used P1:5349): the length-preserving parametrization `ζ` and its inverse are absolutely
  continuous, and `l(ζ(A)) = l(A)` for every measurable `A` — `lengthPreservingParam_measure`
* Unlabelled (§2.6, P1:3591; used P1:5349 "by definition equivalent"): a mapping composed of two absolutely
  continuous homeomorphisms is absolutely continuous, and hence `f` and its arc length `s` are simultaneously
  locally absolutely continuous — `absContHomeo_comp`, `locAbsContHomeo_iff_arcLength_absCont`
* Formula (2.6) (§2.6) — `eq3_2_6`
* Formula (2.7) (§2.6) — `eq3_2_7_i`, `eq3_2_7_ii`
* Definition (variation (2.8) of a continuous function on a segment, §2.7) — exists: `eVariationOn` (the supremum
  over monotone finite sequences equals LV's supremum over non-intersecting intervals, the gaps adding non-negative
  terms)
* Formula (2.8) (§2.7, quoted from Saks) — `eq3_2_8`
* Definition (bounded variation, bounded local variation, §2.7) — exists: `BoundedVariationOn`,
  `LocallyBoundedVariationOn` (for an interval I the sets I ∩ [a, b] with a, b in I are its compact segments; a
  complex function has finite variation if and only if its real and imaginary parts have)
* Definition (the variation `V` as a completely additive set function on the Borel subsets of `I`, the outer measure
  `V*`, §2.7) — omitted: used only to phrase the absolute continuity of functions in §2.8, whose ε–δ
  characterization is taken as the definition; no statement evaluates V off segments
* Definition (the function `s` associated with a continuous function of bounded local variation, §2.7) —
  `IsVariationFn`
* Unlabelled (§2.7, P1:3639, first sentence; used P1:5047): a monotone function has a finite derivative almost
  everywhere — exists: `MonotoneOn.ae_differentiableWithinAt`, `Monotone.ae_differentiableAt` (for a real
  function monotone on a measurable set, differentiable within the set at almost every point, which at interior
  points of an interval is differentiability; no continuity is required)
* Unlabelled (§2.7, P1:3639): a continuous function of bounded local variation has a finite derivative almost
  everywhere, integrable over every compact subset — `bv_ae_deriv`
* Formula (2.9) (§2.7, quoted from Saks) — `eq3_2_9`
* Definition (absolutely continuous function on an interval, §2.8) — `IsAbsContOnInterval`
* Unlabelled (§2.7–2.8, P1:3627, 3649; used P1:5349, 5671–5673, P2:239–247): for a homeomorphism of a segment onto
  a Jordan arc, absolute continuity as a function and as a homeomorphism coincide, also on compact subsets —
  `absContOnInterval_iff_absContHomeo`, `locAbsContOnInterval_iff_locAbsContHomeo`
* Definition (singular function, §2.9) — `IsSingularFn`
* Definition (the Cantor set `E(p₁, p₂, …)`, its linear measure, and the singular function constructed from it,
  §2.9) — omitted: used later only in examples (IV.2.2, V.3.7), not in statements
* Definition (variation, bounded variation and absolute continuity on a Jordan arc, §2.10; variation on a Jordan
  curve, §2.6 and §2.10) — `variationOnArc`, `BoundedVariationOnArc`, `IsAbsContOnArc`, `variationOnCurve`
* Definition (classical Stieltjes integral; Stieltjes integral `∫_{C⁺} f dg` over an oriented closed rectifiable arc
  (2.10), §2.11) — `HasRiemannStieltjesIntegral`, `riemannStieltjesIntegral`, `HasArcStieltjesIntegral`,
  `arcStieltjesIntegral`
* Formula (2.11) (§2.11) — `eq3_2_11` (for Jordan curves, P1:3605, used P1:4633: eq3_2_11_curve in §6, after the
  boundary integral)

Unlabelled facts used only inside proofs or immediate are not stated (inventory: omitted): the term "measurable
mapping" and the ε–δ continuity of `μ_f` on measurable sets (P1:3457–3459); `τ′ = c_B` for
`τ = ∫ c_B dμ` (P1:3477–3483); the transfer of measurability in 2.5 (P1:3519); in 2.6 the continuity of `V`, the
inequality `∫_I s′ dx ≤ l(C)`, the boundedness of `I₀` for rectifiable `C` and the absolute continuity of compositions
(P1:3575–3591), and the extension to finitely many arcs (P1:3605; for Jordan curves see `variationOnCurve` and
`eq3_2_11_curve`); the Jordan decomposition `f = f₁ − f₂` (P1:3629–3637); the fundamental theorem for
absolutely continuous functions (P1:3651–3657); a function both singular and absolutely continuous is constant
(P1:3659); formula (2.5) (P1:3552, a step of the proof of Lemma 2.1).
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane toExt IsJordanCurve closedRect)

/-! ## §2.1 Absolutely continuous additive set functions -/

/-- **Definition** (absolutely continuous set function, Ch. III §2.1). The completely additive set function `τ` is
absolutely continuous in the set `E` (with respect to the measure `μ`): for every `ε > 0` there exists `δ > 0` such
that `|τ(B)| < ε` for every Borel set `B ⊂ E` with `μ(B) < δ`.
Modelling: `τ` enters only through `|τ(B)|` on Borel sets and is passed as the `ℝ≥0∞`-valued function `B ↦ |τ(B)|`:
a non-negative `τ` is a measure (coerced to a function), a bounded real `σ` a signed measure, passed as
`fun B => ‖σ B‖ₑ`. -/
def IsAbsContIn {X : Type*} [MeasurableSpace X] (τ : Set X → ℝ≥0∞) (μ : Measure X) (E : Set X) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ B : Set X, MeasurableSet B → B ⊆ E → μ B < ENNReal.ofReal δ →
    τ B < ENNReal.ofReal ε

/-- **Definition** (locally absolutely continuous set function, Ch. III §2.1): absolutely continuous in every compact
subset of `E`. -/
def IsLocAbsContIn {X : Type*} [TopologicalSpace X] [MeasurableSpace X] (τ : Set X → ℝ≥0∞) (μ : Measure X)
    (E : Set X) : Prop :=
  ∀ K ⊆ E, IsCompact K → IsAbsContIn τ μ K

/-- **Unlabelled** (Ch. III §2.1, P1:3425–3427). Let `τ` be a bounded completely additive set function. If `τ` is
absolutely continuous in `E`, then `τ(B) = 0` for every Borel set `B ⊂ E` with `μ(B) = 0` ("obviously"); conversely
(quoted from Munroe), `τ` is absolutely continuous in `E` if it vanishes for every such Borel null set.
Modelling: `τ` is a signed measure (a bounded real completely additive set function on the measurable sets) on an
arbitrary measurable space `X` with a measure `μ` (the book: the Borel sets of the finite plane, `μ` a Hausdorff or
Lebesgue measure; the statement is also used on the line, P2:239). -/
theorem absCont_iff_null {X : Type*} [MeasurableSpace X] (τ : SignedMeasure X) (μ : Measure X) (E : Set X) :
    IsAbsContIn (fun B => ‖τ B‖ₑ) μ E ↔ ∀ B : Set X, MeasurableSet B → B ⊆ E → μ B = 0 → τ B = 0 := by
  sorry

/-- **Radon–Nikodym theorem** (Ch. III §2.1, quoted from Munroe). A completely additive absolutely continuous set
function `τ` is the integral of an integrable function, provided that `τ` is bounded and vanishes outside a
σ-finite set: `τ(B) = ∫_B f dμ` for every Borel set `B`.
Modelling: `τ` is a signed measure on the finite plane, absolutely continuous in the whole plane; `μ` is any measure
(the book: a Hausdorff or Lebesgue measure); "`τ` vanishes outside the σ-finite set `S`" is `τ(B) = 0` for every
Borel set `B` disjoint from `S`, `S` being σ-finite for `μ`. -/
theorem radon_nikodym_theorem (τ : SignedMeasure ℂ) (μ : Measure ℂ)
    (hac : IsAbsContIn (fun B => ‖τ B‖ₑ) μ univ)
    (hσ : ∃ S : Set ℂ, SigmaFinite (μ.restrict S) ∧ ∀ B : Set ℂ, MeasurableSet B → Disjoint B S → τ B = 0) :
    ∃ f : ℂ → ℝ, Integrable f μ ∧ ∀ B : Set ℂ, MeasurableSet B → τ B = ∫ z in B, f z ∂μ := by
  sorry

/-! ## §2.2 Absolutely continuous homeomorphisms -/

/-- **Definition** (the set function `μ_f` of a homeomorphism, Ch. III §2.2). For a homeomorphism `f : E → E′`,
`μ_f(B) = μ(f(B ∩ E))` for the Borel sets `B`.
Modelling: `ν` is the measure of the image side (see the module docstring); `f` is meant to be a homeomorphism of
`E` onto `f(E)`, which every statement assumes. -/
def homeoSetFn {X Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (f : X → Y) (E : Set X) : Set X → ℝ≥0∞ :=
  fun B => ν (f '' (B ∩ E))

/-- **Definition** (absolutely continuous homeomorphism, Ch. III §2.2): the set function `μ_f` of the homeomorphism
`f : E → E′` is absolutely continuous in `E`. -/
def IsAbsContHomeo {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    (f : X → Y) (E : Set X) : Prop :=
  IsAbsContIn (homeoSetFn ν f E) μ E

/-- **Definition** (locally absolutely continuous homeomorphism, Ch. III §2.2): the set function `μ_f` of the
homeomorphism `f : E → E′` is locally absolutely continuous in `E`. -/
def IsLocAbsContHomeo {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    (ν : Measure Y) (f : X → Y) (E : Set X) : Prop :=
  IsLocAbsContIn (homeoSetFn ν f E) μ E

/-- `f` is a homeomorphism of the segment `I` (a nondegenerate interval of the real line, bounded or unbounded) onto
the Jordan arc `f(I)` of the finite plane: a parametric representation of the arc (Ch. I §1.3; the setting of the
linear case of Ch. III §2.2–2.5, restated in §2.6). -/
def IsArcParam (I : Set ℝ) (f : ℝ → ℂ) : Prop :=
  I.OrdConnected ∧ I.Nontrivial ∧ IsEmbedding (I.domRestrict f)

/-- **Unlabelled** (Ch. III §2.2, P1:3445–3449). An absolutely continuous homeomorphism `f : E → E′` maps all null
sets `A ⊂ E` (not only the Borel ones) onto null sets.
Modelling: `E` and `E′ = f(E)` are Borel sets of Borel spaces `X`, `Y` with measures `μ`, `ν` (module docstring). -/
theorem absContHomeo_null {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} {ν : Measure Y} {f : X → Y}
    {E : Set X} (hE : MeasurableSet E) (hE' : MeasurableSet (f '' E)) (hf : IsEmbedding (E.domRestrict f))
    (hac : IsAbsContHomeo μ ν f E) {A : Set X} (hAE : A ⊆ E) (hA : μ A = 0) : ν (f '' A) = 0 := by
  sorry

/-- **Unlabelled** (Ch. III §2.2, P1:3451–3453). An absolutely continuous homeomorphism `f : E → E′` maps every
σ-finite measurable set `A ⊂ E` onto a measurable set.
Modelling: as in `absContHomeo_null`; "measurable" is null-measurable, "σ-finite" the σ-finiteness of `μ` restricted
to `A`. -/
theorem absContHomeo_measurable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} {ν : Measure Y} {f : X → Y}
    {E : Set X} (hE : MeasurableSet E) (hE' : MeasurableSet (f '' E)) (hf : IsEmbedding (E.domRestrict f))
    (hac : IsAbsContHomeo μ ν f E) {A : Set X} (hAE : A ⊆ E) (hA : NullMeasurableSet A μ)
    (hσ : SigmaFinite (μ.restrict A)) : NullMeasurableSet (f '' A) ν := by
  sorry

/-- **Unlabelled** (Ch. III §2.2, P1:3441; used P1:3855, 3871, P2:239). The set function `μ_f` of a homeomorphism
`f : E → E′` "clearly has all the properties of a measure": it is the restriction to the Borel sets of a measure.
Modelling: as in `absContHomeo_null`; `f` carries the Borel subsets of `E` onto Borel sets, through the homeomorphism
of the Borel subspaces `E` and `f(E)` (footnote 33). -/
theorem homeoSetFn_eq_measure {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) {f : X → Y}
    {E : Set X} (hE : MeasurableSet E) (hE' : MeasurableSet (f '' E)) (hf : IsEmbedding (E.domRestrict f)) :
    ∃ τ : Measure X, ∀ B : Set X, MeasurableSet B → τ B = homeoSetFn ν f E B := by
  sorry

/-- **Unlabelled** (Ch. III §2.1–2.2, P1:3425–3427 applied to `μ_f`, P1:3441; used P1:3871 "By 2.1 and 2.2" and
P2:239 "By III.2.1-2 it is enough to show that `l(w(I))` is finite and null sets go to null sets"). Let
`f : E → E′` be a homeomorphism with `μ(E′) < ∞`. Then `f` is absolutely continuous if and only if it maps every
null set `A ⊂ E` onto a null set.
Modelling: as in `homeoSetFn_eq_measure`; `ν(f(E)) < ∞` is the boundedness of `μ_f`. -/
theorem absContHomeo_iff_null {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} {ν : Measure Y}
    {f : X → Y} {E : Set X} (hE : MeasurableSet E) (hE' : MeasurableSet (f '' E))
    (hf : IsEmbedding (E.domRestrict f)) (hfin : ν (f '' E) < ⊤) :
    IsAbsContHomeo μ ν f E ↔ ∀ A ⊆ E, μ A = 0 → ν (f '' A) = 0 := by
  sorry

/-! ## §2.3 Derivative of an additive set function -/

/-- **Unlabelled** (Ch. III §2.3, P1:3463), `E` a domain. Let `E` be a domain of the finite plane and `μ` the area
measure. A locally absolutely continuous homeomorphism `f : E → E′` maps all null sets `A ⊂ E` onto null sets.
Modelling: LV's hypothesis "`E` a bounded or unbounded segment or a domain of the finite plane" (P1:3461) is kept
(leader decision D6), here its domain case; the book's reason is that `E` is the union of countably many compact
sets (P1:3463). -/
theorem locAbsContHomeo_null_i {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {f : ℂ → ℂ}
    (hf : LiZhongQC.IsHomeomorphOnto f G (f '' G)) (hac : IsLocAbsContHomeo volume volume f G) {A : Set ℂ}
    (hAG : A ⊆ G) (hA : volume A = 0) : volume (f '' A) = 0 := by
  sorry

/-- **Unlabelled** (Ch. III §2.3, P1:3463), `E` a segment. Let `E = I` be a bounded or unbounded segment and `μ` the
linear measure. A locally absolutely continuous homeomorphism `f` of `I` onto a Jordan arc maps all null sets
`A ⊂ I` onto null sets (of the linear measure).
Modelling: LV's hypothesis "`E` a bounded or unbounded segment or a domain of the finite plane" (P1:3461) is kept
(leader decision D6), here its segment case, the segment being taken on the real line; the book's reason is that `E`
is the union of countably many compact sets (P1:3463). -/
theorem locAbsContHomeo_null_ii {I : Set ℝ} {f : ℝ → ℂ} (hf : IsArcParam I f)
    (hac : IsLocAbsContHomeo volume μH[1] f I) {A : Set ℝ} (hAI : A ⊆ I) (hA : volume A = 0) :
    μH[1] (f '' A) = 0 := by
  sorry

/-- **Unlabelled** (Ch. III §2.3, P1:3463), `E` a domain. Let `E` be a domain of the finite plane and `μ` the area
measure. A locally absolutely continuous homeomorphism `f : E → E′` maps every measurable set `A ⊂ E` onto a
measurable set.
Modelling: as in `locAbsContHomeo_null_i`; every set is σ-finite for the area measure. -/
theorem locAbsContHomeo_measurable_i {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {f : ℂ → ℂ}
    (hf : LiZhongQC.IsHomeomorphOnto f G (f '' G)) (hac : IsLocAbsContHomeo volume volume f G) {A : Set ℂ}
    (hAG : A ⊆ G) (hA : NullMeasurableSet A volume) : NullMeasurableSet (f '' A) volume := by
  sorry

/-- **Unlabelled** (Ch. III §2.3, P1:3463), `E` a segment. A locally absolutely continuous homeomorphism `f` of the
segment `I` onto a Jordan arc maps every measurable set `A ⊂ I` onto a set measurable for the linear measure.
Modelling: as in `locAbsContHomeo_null_ii`; every set of the line is σ-finite for the linear measure. -/
theorem locAbsContHomeo_measurable_ii {I : Set ℝ} {f : ℝ → ℂ} (hf : IsArcParam I f)
    (hac : IsLocAbsContHomeo volume μH[1] f I) {A : Set ℝ} (hAI : A ⊆ I) (hA : NullMeasurableSet A volume) :
    NullMeasurableSet (f '' A) μH[1] := by
  sorry

/-- **Definition** (derivative of a set function, Ch. III §2.3), `E` a domain. The set function `τ` has the
derivative `d` at `z`: `τ′(z) = lim_{μ(Q_z) → 0} τ(Q_z ∩ E)/μ(Q_z) = d`, over the squares `Q_z` which contain `z`
and have sides parallel to the coordinate axes (`μ` the area measure).
Modelling: closed squares `[x, x + r] × [y, y + r]`, of area `r²`, as for points of density (§1.6); the limit is
taken in `[0, ∞]` (it may be `∞`). -/
def HasSetFnDerivAt (τ : Set ℂ → ℝ≥0∞) (E : Set ℂ) (z : ℂ) (d : ℝ≥0∞) : Prop :=
  ∀ U ∈ 𝓝 d, ∃ δ : ℝ, 0 < δ ∧ ∀ x y r : ℝ, 0 < r → r < δ → z ∈ closedRect x (x + r) y (y + r) →
    τ (closedRect x (x + r) y (y + r) ∩ E) / ENNReal.ofReal (r ^ 2) ∈ U

open Classical in
/-- The derivative `τ′(z)` of the set function `τ` (Ch. III §2.3, `E` a domain): the limit of `HasSetFnDerivAt`,
which is unique when it exists. Junk value `0` where the limit does not exist (a null set, by Lebesgue's theorem,
under the book's hypotheses); every statement using it asserts the existence of the limit almost everywhere. -/
def setFnDeriv (τ : Set ℂ → ℝ≥0∞) (E : Set ℂ) (z : ℂ) : ℝ≥0∞ :=
  if h : ∃ d, HasSetFnDerivAt τ E z d then h.choose else 0

/-- **Definition** (derivative of a set function, Ch. III §2.3), `E` a segment of the real line. The set function
`τ` has the derivative `d` at `x`: the limit of `τ(Q_x ∩ E)/l(Q_x)` over the closed intervals `Q_x = [a, b]`
containing `x`, as `l(Q_x) → 0` (`μ` the linear measure). -/
def HasSetFnDerivAtReal (τ : Set ℝ → ℝ≥0∞) (E : Set ℝ) (x : ℝ) (d : ℝ≥0∞) : Prop :=
  ∀ U ∈ 𝓝 d, ∃ δ : ℝ, 0 < δ ∧ ∀ a b : ℝ, a ≤ x → x ≤ b → a < b → b - a < δ →
    τ (Icc a b ∩ E) / ENNReal.ofReal (b - a) ∈ U

open Classical in
/-- The derivative `τ′(x)` of the set function `τ` (Ch. III §2.3, `E` a segment): the limit of
`HasSetFnDerivAtReal`, unique when it exists. Junk value `0` where the limit does not exist; every statement using
it asserts the existence of the limit almost everywhere. -/
def setFnDerivReal (τ : Set ℝ → ℝ≥0∞) (E : Set ℝ) (x : ℝ) : ℝ≥0∞ :=
  if h : ∃ d, HasSetFnDerivAtReal τ E x d then h.choose else 0

/-- **Theorem of Lebesgue** (Ch. III §2.3, quoted from Saks), `E` a domain with the area measure. A non-negative,
completely additive set function `τ`, bounded in `E`, has almost everywhere in `E` a finite derivative `τ′(z)`,
which is measurable as a function of `z`. For every Borel set `B ⊂ E`, `τ(B) ≥ ∫_B τ′ dμ` (2.1), where equality
holds for every `B` if and only if `τ` is locally absolutely continuous in `E`.
Modelling: `τ` is a measure on the finite plane with `τ(E) < ∞`; the domain `E` is open and connected. -/
theorem lebesgue_theorem_setFn_i {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (τ : Measure ℂ) (hτ : τ G ≠ ⊤) :
    (∀ᵐ z ∂(volume.restrict G), ∃ d : ℝ≥0∞, d ≠ ⊤ ∧ HasSetFnDerivAt τ G z d) ∧
    AEMeasurable (setFnDeriv τ G) (volume.restrict G) ∧
    (∀ B : Set ℂ, MeasurableSet B → B ⊆ G → ∫⁻ z in B, setFnDeriv τ G z ≤ τ B) ∧
    ((∀ B : Set ℂ, MeasurableSet B → B ⊆ G → ∫⁻ z in B, setFnDeriv τ G z = τ B) ↔
      IsLocAbsContIn τ volume G) := by
  sorry

/-- **Theorem of Lebesgue** (Ch. III §2.3, quoted from Saks), `E` a segment with the linear measure. A non-negative,
completely additive set function `τ`, bounded in `E`, has almost everywhere in `E` a finite derivative `τ′(x)`,
which is measurable as a function of `x`. For every Borel set `B ⊂ E`, `τ(B) ≥ ∫_B τ′ dμ` (2.1), where equality
holds for every `B` if and only if `τ` is locally absolutely continuous in `E`.
Modelling: `τ` is a measure on the real line with `τ(E) < ∞`; the segment `E` is a nondegenerate interval, bounded
or unbounded. -/
theorem lebesgue_theorem_setFn_ii {I : Set ℝ} (hI : I.OrdConnected ∧ I.Nontrivial) (τ : Measure ℝ)
    (hτ : τ I ≠ ⊤) :
    (∀ᵐ x ∂(volume.restrict I), ∃ d : ℝ≥0∞, d ≠ ⊤ ∧ HasSetFnDerivAtReal τ I x d) ∧
    AEMeasurable (setFnDerivReal τ I) (volume.restrict I) ∧
    (∀ B : Set ℝ, MeasurableSet B → B ⊆ I → ∫⁻ x in B, setFnDerivReal τ I x ≤ τ B) ∧
    ((∀ B : Set ℝ, MeasurableSet B → B ⊆ I → ∫⁻ x in B, setFnDerivReal τ I x = τ B) ↔
      IsLocAbsContIn τ volume I) := by
  sorry

/-! ## §2.4 Derivative of the set function associated with a homeomorphism -/

/-- **Definition** (areal derivative, Ch. III §2.4, footnote 35). For a homeomorphism `f` of the domain `G` of the
finite plane (area measure), the areal derivative `μ′_f` is the derivative of the set function `μ_f`. Junk value `0`
where the derivative does not exist (a null set, by (2.2)); every statement using it asserts its existence almost
everywhere. -/
def arealDeriv (f : ℂ → ℂ) (G : Set ℂ) : ℂ → ℝ≥0∞ := setFnDeriv (homeoSetFn volume f G) G

/-- **Formula (2.2)** (Ch. III §2.4), domains. Let `f` be a homeomorphism of the domain `G` onto the domain `G′` of
the finite plane. The areal derivative `μ′_f` exists and is finite almost everywhere in `G`; it is measurable and
locally integrable in `G` (integrable over every compact subset of `G`), and `m(f(B)) ≥ ∬_B μ′_f dσ` (2.2) for every
Borel set `B ⊂ G`. -/
theorem eq3_2_2_i {G G' : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (hG' : IsOpen G' ∧ IsConnected G') {f : ℂ → ℂ}
    (hf : LiZhongQC.IsHomeomorphOnto f G G') :
    (∀ᵐ z ∂(volume.restrict G), ∃ d : ℝ≥0∞, d ≠ ⊤ ∧ HasSetFnDerivAt (homeoSetFn volume f G) G z d) ∧
    AEMeasurable (arealDeriv f G) (volume.restrict G) ∧
    (∀ K ⊆ G, IsCompact K → ∫⁻ z in K, arealDeriv f G z < ⊤) ∧
    ∀ B : Set ℂ, MeasurableSet B → B ⊆ G → ∫⁻ z in B, arealDeriv f G z ≤ volume (f '' B) := by
  sorry

/-- **Formula (2.2)** (Ch. III §2.4), the one-dimensional case. Let `f` be a homeomorphism of the segment `I` onto a
Jordan arc, with the linear measure, and suppose that `μ_f` is locally bounded (bounded in every compact subset of
`I`). Then the derivative `μ′_f` exists and is finite almost everywhere on `I`; it is measurable and locally
integrable on `I`, and `l(f(B)) ≥ ∫_B μ′_f dx` (2.2) for every Borel set `B ⊂ I`. -/
theorem eq3_2_2_ii {I : Set ℝ} {f : ℝ → ℂ} (hf : IsArcParam I f)
    (hbdd : ∀ K ⊆ I, IsCompact K → μH[1] (f '' K) < ⊤) :
    (∀ᵐ x ∂(volume.restrict I), ∃ d : ℝ≥0∞, d ≠ ⊤ ∧ HasSetFnDerivAtReal (homeoSetFn μH[1] f I) I x d) ∧
    AEMeasurable (setFnDerivReal (homeoSetFn μH[1] f I) I) (volume.restrict I) ∧
    (∀ K ⊆ I, IsCompact K → ∫⁻ x in K, setFnDerivReal (homeoSetFn μH[1] f I) I x < ⊤) ∧
    ∀ B : Set ℝ, MeasurableSet B → B ⊆ I →
      ∫⁻ x in B, setFnDerivReal (homeoSetFn μH[1] f I) I x ≤ μH[1] (f '' B) := by
  sorry

/-- **Formula (2.3)** (Ch. III §2.4), domains. If `f` is a locally absolutely continuous homeomorphism of the domain
`G` onto the domain `G′` of the finite plane, then `m(f(A)) = ∬_A μ′_f dσ` (2.3) for every measurable set `A ⊂ G`
(`μ_f` need not be bounded).
Modelling: the first conjunct restates the almost-everywhere existence of `μ′_f` from (2.2), so that the junk value
of `arealDeriv` is not relied on. -/
theorem eq3_2_3_i {G G' : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (hG' : IsOpen G' ∧ IsConnected G') {f : ℂ → ℂ}
    (hf : LiZhongQC.IsHomeomorphOnto f G G') (hac : IsLocAbsContHomeo volume volume f G) :
    (∀ᵐ z ∂(volume.restrict G), ∃ d : ℝ≥0∞, d ≠ ⊤ ∧ HasSetFnDerivAt (homeoSetFn volume f G) G z d) ∧
    ∀ A ⊆ G, NullMeasurableSet A volume → volume (f '' A) = ∫⁻ z in A, arealDeriv f G z := by
  sorry

/-- **Formula (2.3)** (Ch. III §2.4), the one-dimensional case. If `f` is a locally absolutely continuous
homeomorphism of the segment `I` onto a Jordan arc, then `l(f(A)) = ∫_A μ′_f dx` (2.3) for every measurable set
`A ⊂ I` (`μ_f` need not be bounded).
Modelling: the first conjunct restates the almost-everywhere existence of `μ′_f`, so that the junk value of
`setFnDerivReal` is not relied on. -/
theorem eq3_2_3_ii {I : Set ℝ} {f : ℝ → ℂ} (hf : IsArcParam I f) (hac : IsLocAbsContHomeo volume μH[1] f I) :
    (∀ᵐ x ∂(volume.restrict I), ∃ d : ℝ≥0∞, d ≠ ⊤ ∧ HasSetFnDerivAtReal (homeoSetFn μH[1] f I) I x d) ∧
    ∀ A ⊆ I, NullMeasurableSet A volume →
      μH[1] (f '' A) = ∫⁻ x in A, setFnDerivReal (homeoSetFn μH[1] f I) I x := by
  sorry

/-! ## §2.5 Transformation of variables in integrals -/

/-- **Lemma 2.1** (Ch. III §2.5), domains, `g` non-negative. Let `f : G → G′` be a locally absolutely continuous
homeomorphism of domains of the finite plane and `g` a non-negative function in `G′` such that `h = g ∘ f` is
measurable. If `A ⊂ G` is measurable and `A′ = f(A)`, then `∬_{A′} g dσ = ∬_A h μ′_f dσ` (2.4), where `h μ′_f = 0`
at the points where `h = ∞` and `μ′_f = 0`.
Modelling: `g` is `ℝ≥0∞`-valued, and `∞ · 0 = 0` in `ℝ≥0∞` is the book's convention; the first conjunct restates the
almost-everywhere existence of `μ′_f`. -/
theorem lemma3_2_1_i {G G' : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (hG' : IsOpen G' ∧ IsConnected G')
    {f : ℂ → ℂ} (hf : LiZhongQC.IsHomeomorphOnto f G G') (hac : IsLocAbsContHomeo volume volume f G)
    {g : ℂ → ℝ≥0∞} (hh : AEMeasurable (g ∘ f) (volume.restrict G)) {A : Set ℂ} (hAG : A ⊆ G)
    (hA : NullMeasurableSet A volume) :
    (∀ᵐ z ∂(volume.restrict G), ∃ d : ℝ≥0∞, d ≠ ⊤ ∧ HasSetFnDerivAt (homeoSetFn volume f G) G z d) ∧
    ∫⁻ w in f '' A, g w = ∫⁻ z in A, g (f z) * arealDeriv f G z := by
  sorry

/-- **Lemma 2.1** (Ch. III §2.5), domains, `g` integrable. Let `f : G → G′` be a locally absolutely continuous
homeomorphism of domains of the finite plane and `g` an integrable function in `G′` such that `h = g ∘ f` is
measurable. If `A ⊂ G` is measurable and `A′ = f(A)`, then `∬_{A′} g dσ = ∬_A h μ′_f dσ` (2.4).
Modelling: `g` is finite `ℂ`-valued (D2); the integrals are Bochner integrals, and the integrability of `h μ′_f` on
`A` (the right side of (2.4) being a finite integral in the book) is stated; `(μ′_f).toReal` is `μ′_f` wherever
`μ′_f` is finite, i.e. almost everywhere by the first conjunct. -/
theorem lemma3_2_1_ii {G G' : Set ℂ} (hG : IsOpen G ∧ IsConnected G) (hG' : IsOpen G' ∧ IsConnected G')
    {f : ℂ → ℂ} (hf : LiZhongQC.IsHomeomorphOnto f G G') (hac : IsLocAbsContHomeo volume volume f G)
    {g : ℂ → ℂ} (hg : IntegrableOn g G') (hh : AEStronglyMeasurable (g ∘ f) (volume.restrict G)) {A : Set ℂ}
    (hAG : A ⊆ G) (hA : NullMeasurableSet A volume) :
    (∀ᵐ z ∂(volume.restrict G), ∃ d : ℝ≥0∞, d ≠ ⊤ ∧ HasSetFnDerivAt (homeoSetFn volume f G) G z d) ∧
    IntegrableOn (fun z => g (f z) * ((arealDeriv f G z).toReal : ℂ)) A ∧
    ∫ w in f '' A, g w = ∫ z in A, g (f z) * ((arealDeriv f G z).toReal : ℂ) := by
  sorry

/-- **Lemma 2.1** (Ch. III §2.5), a segment, `g` non-negative. Let `f` be a locally absolutely continuous
homeomorphism of the segment `I` onto a Jordan arc `E′ = f(I)`, with the linear measure, and `g` a non-negative
function on `E′` such that `h = g ∘ f` is measurable. If `A ⊂ I` is measurable and `A′ = f(A)`, then
`∫_{A′} g dμ = ∫_A h μ′_f dμ` (2.4), where `h μ′_f = 0` at the points where `h = ∞` and `μ′_f = 0`.
Modelling: as in `lemma3_2_1_i`. -/
theorem lemma3_2_1_iii {I : Set ℝ} {f : ℝ → ℂ} (hf : IsArcParam I f) (hac : IsLocAbsContHomeo volume μH[1] f I)
    {g : ℂ → ℝ≥0∞} (hh : AEMeasurable (g ∘ f) (volume.restrict I)) {A : Set ℝ} (hAI : A ⊆ I)
    (hA : NullMeasurableSet A volume) :
    (∀ᵐ x ∂(volume.restrict I), ∃ d : ℝ≥0∞, d ≠ ⊤ ∧ HasSetFnDerivAtReal (homeoSetFn μH[1] f I) I x d) ∧
    ∫⁻ w in f '' A, g w ∂μH[1] = ∫⁻ x in A, g (f x) * setFnDerivReal (homeoSetFn μH[1] f I) I x := by
  sorry

/-- **Lemma 2.1** (Ch. III §2.5), a segment, `g` integrable. Let `f` be a locally absolutely continuous homeomorphism
of the segment `I` onto a Jordan arc `E′ = f(I)`, with the linear measure, and `g` an integrable function on `E′`
such that `h = g ∘ f` is measurable. If `A ⊂ I` is measurable and `A′ = f(A)`, then `∫_{A′} g dμ = ∫_A h μ′_f dμ`
(2.4).
Modelling: as in `lemma3_2_1_ii`. -/
theorem lemma3_2_1_iv {I : Set ℝ} {f : ℝ → ℂ} (hf : IsArcParam I f) (hac : IsLocAbsContHomeo volume μH[1] f I)
    {g : ℂ → ℂ} (hg : IntegrableOn g (f '' I) μH[1]) (hh : AEStronglyMeasurable (g ∘ f) (volume.restrict I))
    {A : Set ℝ} (hAI : A ⊆ I) (hA : NullMeasurableSet A volume) :
    (∀ᵐ x ∂(volume.restrict I), ∃ d : ℝ≥0∞, d ≠ ⊤ ∧ HasSetFnDerivAtReal (homeoSetFn μH[1] f I) I x d) ∧
    IntegrableOn (fun x => g (f x) * ((setFnDerivReal (homeoSetFn μH[1] f I) I x).toReal : ℂ)) A ∧
    ∫ w in f '' A, g w ∂μH[1] =
      ∫ x in A, g (f x) * ((setFnDerivReal (homeoSetFn μH[1] f I) I x).toReal : ℂ) := by
  sorry

/-! ## §2.6 Rectifiable arcs -/

/-- **Definition** (rectifiable arc, length, Ch. III §2.6). The Jordan arc `C` of the finite plane is rectifiable if
`V(I) = l(C)` is finite; `l(C)` is the length of `C`.
Modelling: the length `l(C)` is the linear measure `μH[1] C` (no separate definition): for a parametrization
`f : I → C`, `V(I) = μ_f(I) = l(f(I)) = l(C)`. -/
def IsRectifiableArc (C : Set ℂ) : Prop := IsJordanArc (toExt C) ∧ μH[1] C < ⊤

/-- **Definition** (locally rectifiable arc, Ch. III §2.6): every compact (i.e. closed) subarc of the Jordan arc `C`
is rectifiable. -/
def IsLocRectifiableArc (C : Set ℂ) : Prop :=
  IsJordanArc (toExt C) ∧ ∀ C' ⊆ C, IsClosedJordanArc (toExt C') → IsRectifiableArc C'

/-- **Definition** (rectifiable Jordan curve, Ch. III §2.6): a Jordan curve of the finite plane all of whose subarcs
are rectifiable. -/
def IsRectifiableJordanCurve (C : Set ℂ) : Prop :=
  IsJordanCurve (toExt C) ∧ ∀ C' ⊆ C, IsJordanArc (toExt C') → IsRectifiableArc C'

/-- **Definition** (arc length, Ch. III §2.6). For a homeomorphism `f` of the segment `I` onto a locally rectifiable
arc, `s` is an arc length: the growth of `s` on every subinterval `[a, b]` of `I` equals `V([a, b]) = l(f([a, b]))`.
Modelling: a predicate, `s` being determined up to an additive constant; `s a ≤ s b` is redundant here (for `a < b`
the arc `f([a, b])` has positive length) and is kept for uniformity with `IsVariationFn`, where it is essential. -/
def IsArcLengthFn (f : ℝ → ℂ) (I : Set ℝ) (s : ℝ → ℝ) : Prop :=
  ∀ a ∈ I, ∀ b ∈ I, a ≤ b → s a ≤ s b ∧ ENNReal.ofReal (s b - s a) = μH[1] (f '' Icc a b)

/-- **Definition** (length-preserving parametrization, Ch. III §2.6). `ζ : I₀ → C` is a length-preserving
parametrization of the locally rectifiable arc `C`: a homeomorphism of the segment `I₀` onto `C` which maps every
interval `Δ ⊂ I₀` onto an arc of length `l(Δ)`.
Modelling: a predicate (`ζ = f ∘ s⁻¹` is determined up to a translation of `I₀` and the orientation); the intervals
are represented by the closed ones `[a, b] ⊂ I₀`. -/
def IsLengthPreservingParam (I₀ : Set ℝ) (ζ : ℝ → ℂ) (C : Set ℂ) : Prop :=
  IsArcParam I₀ ζ ∧ ζ '' I₀ = C ∧ ∀ a ∈ I₀, ∀ b ∈ I₀, a ≤ b → μH[1] (ζ '' Icc a b) = ENNReal.ofReal (b - a)

/-- **Unlabelled** (Ch. III §2.6, P1:3589; used P1:5349). The length-preserving parametrization `ζ : I₀ → C` is
absolutely continuous and satisfies `l(ζ(A)) = l(A)` for every measurable set `A ⊂ I₀`; the inverse `ζ⁻¹` is also
absolutely continuous.
Modelling: absolute continuity of the homeomorphisms `ζ : I₀ → C` (linear measure on `C`) and `ζ⁻¹ : C → I₀`
(linear measure on the line), `ζ⁻¹` being `invFunOn ζ I₀`. -/
theorem lengthPreservingParam_measure {I₀ : Set ℝ} {ζ : ℝ → ℂ} {C : Set ℂ} (hζ : IsLengthPreservingParam I₀ ζ C) :
    IsAbsContHomeo volume μH[1] ζ I₀ ∧ IsAbsContHomeo μH[1] volume (Function.invFunOn ζ I₀) C ∧
      ∀ A ⊆ I₀, NullMeasurableSet A volume → μH[1] (ζ '' A) = volume A := by
  sorry

/-- **Unlabelled** (Ch. III §2.6, P1:3591, first half). A mapping composed of two absolutely continuous
homeomorphisms is absolutely continuous ("obviously").
Modelling: `f : E → E′` and `g : E′ → E″` homeomorphisms of Borel sets of Borel spaces with measures `μ`, `ν`, `ρ`
(as in `absContHomeo_null`). -/
theorem absContHomeo_comp {X Y Z : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    {μ : Measure X} {ν : Measure Y} {ρ : Measure Z} {f : X → Y} {g : Y → Z} {E : Set X}
    (hE : MeasurableSet E) (hE' : MeasurableSet (f '' E)) (hE'' : MeasurableSet (g '' (f '' E)))
    (hf : IsEmbedding (E.domRestrict f)) (hg : IsEmbedding ((f '' E).domRestrict g))
    (hfac : IsAbsContHomeo μ ν f E) (hgac : IsAbsContHomeo ν ρ g (f '' E)) :
    IsAbsContHomeo μ ρ (g ∘ f) E := by
  sorry

/-- **Formula (2.6)** (Ch. III §2.6). Let `f` be a homeomorphism of the segment `I` onto a locally rectifiable arc,
with arc length `s`. Then `∫_A s′ dx = l(f(A))` (2.6) holds for every measurable set `A ⊂ I` if and only if `f` is
locally absolutely continuous.
Modelling: the first conjunct states that `s` (continuous and increasing) is differentiable almost everywhere on `I`,
so that `deriv s` is the book's `s′ ≥ 0` outside a null set. -/
theorem eq3_2_6 {I : Set ℝ} {f : ℝ → ℂ} {s : ℝ → ℝ} (hf : IsArcParam I f) (hC : IsLocRectifiableArc (f '' I))
    (hs : IsArcLengthFn f I s) :
    (∀ᵐ x ∂(volume.restrict I), DifferentiableAt ℝ s x) ∧
    ((∀ A ⊆ I, NullMeasurableSet A volume → ∫⁻ x in A, ENNReal.ofReal (deriv s x) = μH[1] (f '' A)) ↔
      IsLocAbsContHomeo volume μH[1] f I) := by
  sorry

/-- **Formula (2.7)** (Ch. III §2.6), `g` non-negative. Let `f` be a locally absolutely continuous homeomorphism of
the segment `I` onto the locally rectifiable arc `C = f(I)`, with arc length `s`. Then
`∫_A (g ∘ f) s′ dx = ∫_{f(A)} g dl` (2.7) for every non-negative Borel function `g` on `C` and every measurable set
`A ⊂ I`. (The integral on the right is also written `∫_{f(A)} g |dz|`.)
Modelling: `g` is `ℝ≥0∞`-valued and Borel on the plane (its values off `C` do not enter); the first conjunct as in
`eq3_2_6`. -/
theorem eq3_2_7_i {I : Set ℝ} {f : ℝ → ℂ} {s : ℝ → ℝ} (hf : IsArcParam I f) (hC : IsLocRectifiableArc (f '' I))
    (hs : IsArcLengthFn f I s) (hac : IsLocAbsContHomeo volume μH[1] f I) {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    {A : Set ℝ} (hAI : A ⊆ I) (hA : NullMeasurableSet A volume) :
    (∀ᵐ x ∂(volume.restrict I), DifferentiableAt ℝ s x) ∧
    ∫⁻ x in A, g (f x) * ENNReal.ofReal (deriv s x) = ∫⁻ w in f '' A, g w ∂μH[1] := by
  sorry

/-- **Formula (2.7)** (Ch. III §2.6), `g` integrable. Let `f` be a locally absolutely continuous homeomorphism of the
segment `I` onto the locally rectifiable arc `C = f(I)`, with arc length `s`. Then
`∫_A (g ∘ f) s′ dx = ∫_{f(A)} g dl` (2.7) for every Borel function `g` integrable on `C` (with respect to the linear
measure) and every measurable set `A ⊂ I`.
Modelling: `g` is finite `ℂ`-valued (D2) and Borel on the plane; Bochner integrals, with the integrability of the
left integrand stated; the first conjunct as in `eq3_2_6`. -/
theorem eq3_2_7_ii {I : Set ℝ} {f : ℝ → ℂ} {s : ℝ → ℝ} (hf : IsArcParam I f) (hC : IsLocRectifiableArc (f '' I))
    (hs : IsArcLengthFn f I s) (hac : IsLocAbsContHomeo volume μH[1] f I) {g : ℂ → ℂ} (hg : Measurable g)
    (hgi : IntegrableOn g (f '' I) μH[1]) {A : Set ℝ} (hAI : A ⊆ I) (hA : NullMeasurableSet A volume) :
    (∀ᵐ x ∂(volume.restrict I), DifferentiableAt ℝ s x) ∧
    IntegrableOn (fun x => g (f x) * ((deriv s x : ℝ) : ℂ)) A ∧
    ∫ x in A, g (f x) * ((deriv s x : ℝ) : ℂ) = ∫ w in f '' A, g w ∂μH[1] := by
  sorry

/-! ## §2.7 Functions of bounded variation on an interval -/

/-- **Formula (2.8)** (Ch. III §2.7, quoted from Saks, IV §8). Let `f` be a homeomorphism of the segment `I` onto a
Jordan arc and `Δ ⊂ I` a segment. Then `l(f(Δ)) = V(Δ) = sup ∑ᵢ |f(bᵢ) − f(aᵢ)|` (2.8), the supremum being taken
over all finite sequences of non-intersecting intervals `aᵢ < x < bᵢ` which, together with their endpoints, are
contained in `Δ`. -/
theorem eq3_2_8 {I : Set ℝ} {f : ℝ → ℂ} (hf : IsArcParam I f) {Δ : Set ℝ} (hΔ : Δ.OrdConnected) (hΔI : Δ ⊆ I) :
    μH[1] (f '' Δ) = eVariationOn f Δ := by
  sorry

/-- **Definition** (the function `s` associated with `f`, Ch. III §2.7). For a continuous function `f` of bounded
local variation on the segment `I`, `s(b) − s(a) = V([a, b])` for `a ≤ b` in `I`, `V` being the variation (2.8).
Modelling: a predicate, `s` being determined up to an additive constant; `s a ≤ s b` is stated so that the
truncation of `ENNReal.ofReal` at `0` does not weaken the equation (without it `f ≡ 0`, `s(x) = -x` would qualify). -/
def IsVariationFn (f : ℝ → ℂ) (I : Set ℝ) (s : ℝ → ℝ) : Prop :=
  ∀ a ∈ I, ∀ b ∈ I, a ≤ b → s a ≤ s b ∧ ENNReal.ofReal (s b - s a) = eVariationOn f (Icc a b)

/-- **Unlabelled** (Ch. III §2.7, P1:3639). A continuous function `f` of bounded local variation on the segment `I`
has a finite derivative almost everywhere on `I`, and the derivative `f′` is integrable over every compact subset
of `I`.
Modelling: `f` is complex-valued; `deriv f` is `f′` outside the null set where `f` is not differentiable. -/
theorem bv_ae_deriv {I : Set ℝ} (hI : I.OrdConnected) {f : ℝ → ℂ} (hf : ContinuousOn f I)
    (hbv : LocallyBoundedVariationOn f I) :
    (∀ᵐ x ∂(volume.restrict I), DifferentiableAt ℝ f x) ∧ ∀ K ⊆ I, IsCompact K → IntegrableOn (deriv f) K := by
  sorry

/-- **Formula (2.9)** (Ch. III §2.7, quoted from Saks). The derivatives of a continuous function `f` of bounded local
variation on the segment `I` and of the function `s` associated with `f` satisfy `|f′(x)| = s′(x)` (2.9) for almost
all `x ∈ I`.
Modelling: both derivatives are named through `HasDerivAt`, which asserts their existence. -/
theorem eq3_2_9 {I : Set ℝ} (hI : I.OrdConnected) {f : ℝ → ℂ} (hf : ContinuousOn f I)
    (hbv : LocallyBoundedVariationOn f I) {s : ℝ → ℝ} (hs : IsVariationFn f I s) :
    ∀ᵐ x ∂(volume.restrict I), ∃ (a : ℂ) (b : ℝ), HasDerivAt f a x ∧ HasDerivAt s b x ∧ ‖a‖ = b := by
  sorry

/-! ## §2.8–2.9 Absolutely continuous and singular functions on an interval -/

/-- **Definition** (absolutely continuous function on an interval, Ch. III §2.8). The continuous function `f` on the
interval `I` is absolutely continuous: to every `ε > 0` there corresponds `δ > 0` such that `∑ |f(bᵢ) − f(aᵢ)| < ε`
for every finite sequence of non-intersecting intervals `aᵢ < x < bᵢ` which, together with their endpoints, lie in
`I` and have a total length `< δ`.
Modelling: LV defines the absolute continuity of `f` as that of its variation `V` and gives this characterization,
which is the definition here (the set function `V` is not formalized); `I` may be open or unbounded. -/
def IsAbsContOnInterval (f : ℝ → ℂ) (I : Set ℝ) : Prop :=
  ContinuousOn f I ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (a b : Fin n → ℝ),
    (∀ i, a i < b i ∧ a i ∈ I ∧ b i ∈ I) → Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) →
      ∑ i, (b i - a i) < δ → ∑ i, ‖f (b i) - f (a i)‖ < ε

/-- **Unlabelled** (Ch. III §2.7–2.8, P1:3627, 3649; used P1:5349 "by definition equivalent", P1:5671–5673,
P2:239–247). Let `f` be a homeomorphism of the segment `I` onto a Jordan arc. Then `f` is absolutely continuous as
a function on `I` (§2.8) if and only if it is an absolutely continuous homeomorphism (§2.2, with the linear measure
on the arc): in the book both are the absolute continuity of the variation `V`, which for a homeomorphism is the
set function `μ_f` (P1:3627, (2.8)). -/
theorem absContOnInterval_iff_absContHomeo {I : Set ℝ} {f : ℝ → ℂ} (hf : IsArcParam I f) :
    IsAbsContOnInterval f I ↔ IsAbsContHomeo volume μH[1] f I := by
  sorry

/-- **Unlabelled** (Ch. III §2.7–2.8, the local form, used P1:5349 "on compact subsets"). Let `f` be a
homeomorphism of the segment `I` onto a Jordan arc. Then `f` is absolutely continuous on every compact segment of
`I` if and only if it is a locally absolutely continuous homeomorphism. -/
theorem locAbsContOnInterval_iff_locAbsContHomeo {I : Set ℝ} {f : ℝ → ℂ} (hf : IsArcParam I f) :
    (∀ a ∈ I, ∀ b ∈ I, IsAbsContOnInterval f (Icc a b)) ↔ IsLocAbsContHomeo volume μH[1] f I := by
  sorry

/-- **Unlabelled** (Ch. III §2.6, P1:3591; used P1:5349 "by definition equivalent"). Let `f` be a homeomorphism of
the segment `I` onto a locally rectifiable arc, with arc length `s`. Then `f` and `s` are simultaneously locally
absolutely continuous (from `f = ζ ∘ s`, `s = ζ⁻¹ ∘ f`).
Modelling: `f` as a homeomorphism onto the arc with the linear measure (`IsLocAbsContHomeo`), `s` as a function on
the compact segments of `I` (§2.8; the declaration is placed after that definition). -/
theorem locAbsContHomeo_iff_arcLength_absCont {I : Set ℝ} {f : ℝ → ℂ} {s : ℝ → ℝ} (hf : IsArcParam I f)
    (hC : IsLocRectifiableArc (f '' I)) (hs : IsArcLengthFn f I s) :
    IsLocAbsContHomeo volume μH[1] f I ↔
      ∀ a ∈ I, ∀ b ∈ I, IsAbsContOnInterval (fun x => (s x : ℂ)) (Icc a b) := by
  sorry

/-- **Definition** (singular function, Ch. III §2.9). A function `f` of bounded variation on the interval `I` is
singular if its derivative `f′` vanishes almost everywhere on `I`.
Modelling: continuity is part of LV's notion of variation (§2.7); `f′ = 0` is written with `HasDerivAt`. -/
def IsSingularFn (f : ℝ → ℂ) (I : Set ℝ) : Prop :=
  ContinuousOn f I ∧ BoundedVariationOn f I ∧ ∀ᵐ x ∂(volume.restrict I), HasDerivAt f 0 x

/-! ## §2.10 Variation and absolute continuity on a Jordan arc -/

/-- **Definition** (variation on a Jordan arc, Ch. III §2.10). For a continuous function `f` on the locally
rectifiable arc `C`, the variation of `f ∘ t` over `I` is the same for all parametrizations `t : I → C`; it is the
variation of `f` on `C`.
Modelling: the infimum over all parametrizations (all values being equal); junk value `⊤` (empty infimum) when `C`
is not a Jordan arc of the finite plane. -/
def variationOnArc (f : ℂ → ℂ) (C : Set ℂ) : ℝ≥0∞ :=
  ⨅ (I : Set ℝ) (t : ℝ → ℂ) (_ : IsArcParam I t) (_ : t '' I = C), eVariationOn (f ∘ t) I

/-- **Definition** (bounded variation on a Jordan arc, Ch. III §2.10): the variation of `f` on `C` is finite. -/
def BoundedVariationOnArc (f : ℂ → ℂ) (C : Set ℂ) : Prop := variationOnArc f C < ⊤

/-- **Definition** (absolutely continuous on a Jordan arc, Ch. III §2.10). `f` is absolutely continuous on the
locally rectifiable arc `C` as a function of the arc length of `C`: `f ∘ ζ` is absolutely continuous for the
length-preserving parametrization `ζ : I₀ → C`.
Modelling: `ζ` is unique up to a translation of `I₀` and a reflection, which preserve absolute continuity, so `ζ` is
quantified existentially. -/
def IsAbsContOnArc (f : ℂ → ℂ) (C : Set ℂ) : Prop :=
  ∃ (I₀ : Set ℝ) (ζ : ℝ → ℂ), IsLengthPreservingParam I₀ ζ C ∧ IsAbsContOnInterval (f ∘ ζ) I₀

/-- **Definition** (variation on a Jordan curve, Ch. III §2.6, P1:3605, and §2.10). For a continuous function `f` on
the Jordan curve `C` of the finite plane, the variation of `f` on `C`: the variation of `f ∘ γ` over one period of a
parametrization `γ` of `C` (the sum of the variations on the two subarcs of a division of `C`).
Modelling: the infimum over the parametrizations by `ℝ/ℤ` (all values being equal); junk value `⊤` when `C` is not
a Jordan curve of the finite plane. -/
def variationOnCurve (f : ℂ → ℂ) (C : Set ℂ) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → ℂ) (_ : IsLoopParam (toExt C) (fun t => (γ t : ExtPlane))), eVariationOn (f ∘ γ) (Icc 0 1)

/-! ## §2.11 Integrals over oriented arcs -/

/-- **Definition** (classical Stieltjes integral, Ch. III §2.11). `∫_a^b φ dψ = L` in the Riemann–Stieltjes sense:
`a ≤ b`, and for every `ε > 0` there is `δ > 0` such that `|∑ φ(tᵢ)(ψ(xᵢ₊₁) − ψ(xᵢ)) − L| < ε` for every partition
`a = x₀ ≤ x₁ ≤ ⋯ ≤ xₙ = b` of mesh `< δ` and all intermediate points `tᵢ ∈ [xᵢ, xᵢ₊₁]`. (It exists for continuous
`φ` and continuous `ψ` of bounded variation.) -/
def HasRiemannStieltjesIntegral (φ ψ : ℝ → ℂ) (a b : ℝ) (L : ℂ) : Prop :=
  a ≤ b ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (x : Fin (n + 1) → ℝ) (t : Fin n → ℝ),
    Monotone x → x 0 = a → x (Fin.last n) = b →
      (∀ i : Fin n, x i.castSucc ≤ t i ∧ t i ≤ x i.succ ∧ x i.succ - x i.castSucc < δ) →
        ‖∑ i : Fin n, φ (t i) * (ψ (x i.succ) - ψ (x i.castSucc)) - L‖ < ε

open Classical in
/-- The classical Stieltjes integral `∫_a^b φ dψ` (Ch. III §2.11): the value `L` of `HasRiemannStieltjesIntegral`,
which is unique when it exists. Junk value `0` when it does not exist (outside the book's domain: continuous `φ`,
continuous `ψ` of bounded variation, `a ≤ b`); statements use `HasRiemannStieltjesIntegral`. -/
def riemannStieltjesIntegral (φ ψ : ℝ → ℂ) (a b : ℝ) : ℂ :=
  if h : ∃ L, HasRiemannStieltjesIntegral φ ψ a b L then h.choose else 0

/-- **Definition** (Stieltjes integral over an oriented arc, Ch. III §2.11, (2.10)). Let `C` be a closed rectifiable
Jordan arc with the orientation `α` from its endpoint `p`, and `ζ : [0, l] → C` its length-preserving
parametrization with `ζ(0) = p` (it belongs to `α`, so the sign in (2.10) is `+`). Then `∫_{C⁺} f dg = L` means
that the classical Stieltjes integral `∫_0^l f(ζ(s)) dg(ζ(s))` exists and equals `L`.
Modelling: the orientation `α` of the closed arc is represented by its initial point `p`. -/
def HasArcStieltjesIntegral (C : Set ℂ) (p : ℂ) (f g : ℂ → ℂ) (L : ℂ) : Prop :=
  ∃ (l : ℝ) (ζ : ℝ → ℂ), IsLengthPreservingParam (Icc 0 l) ζ C ∧ ζ 0 = p ∧
    HasRiemannStieltjesIntegral (f ∘ ζ) (g ∘ ζ) 0 l L

open Classical in
/-- The Stieltjes integral `∫_{C⁺} f dg` over the closed rectifiable arc `C` oriented from `p` (Ch. III §2.11,
(2.10)): the value of `HasArcStieltjesIntegral`, unique when it exists. Junk value `0` otherwise (`C` not a closed
rectifiable arc with endpoint `p`, or the classical integral not existing). -/
def arcStieltjesIntegral (C : Set ℂ) (p : ℂ) (f g : ℂ → ℂ) : ℂ :=
  if h : ∃ L, HasArcStieltjesIntegral C p f g L then h.choose else 0

/-- **Formula (2.11)** (Ch. III §2.11). Let `w` be a homeomorphism of the closed rectifiable arc `C` onto the
rectifiable arc `C′`; `w` carries the orientation `α` of `C` onto an orientation `α′` of `C′` (I.1.5), i.e. the
oriented arc `C⁺ = (C, α)` onto `w(C⁺) = (C′, α′)`. Then, for continuous functions `f`, `g` on `C`, `g` of bounded
variation, `∫_{C⁺} f dg = ∫_{w(C⁺)} (f ∘ w⁻¹) d(g ∘ w⁻¹)` (2.11).
[misprint] (2.11) is printed with `dg′` on the left (P1:3702; the tick is in the print); the definition (2.10)
requires `dg`.
Modelling: `C⁺` is oriented from its endpoint `p`, and `w(C⁺)` from `w(p)`; `w⁻¹` is `invFunOn w C`. The existence
of both integrals (taken by the book from the classical theory) and their equality are stated together. -/
theorem eq3_2_11 {C C' : Set ℂ} {p q : ℂ} (hC : IsArcFromTo (toExt C) p q) (hCr : IsRectifiableArc C)
    {w : ℂ → ℂ} (hw : LiZhongQC.IsHomeomorphOnto w C C') (hC'r : IsRectifiableArc C') {f g : ℂ → ℂ}
    (hf : ContinuousOn f C) (hg : ContinuousOn g C) (hgbv : BoundedVariationOnArc g C) :
    ∃ L : ℂ, HasArcStieltjesIntegral C p f g L ∧
      HasArcStieltjesIntegral C' (w p) (f ∘ Function.invFunOn w C) (g ∘ Function.invFunOn w C) L := by
  sorry

end LehtoVirtanen1973
