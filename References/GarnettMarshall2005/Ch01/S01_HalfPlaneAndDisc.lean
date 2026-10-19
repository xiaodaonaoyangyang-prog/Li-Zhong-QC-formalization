import References.LehtoVirtanen1973.Ch01.S01_TopologicalProperties

/-!
# Garnett–Marshall, Chapter I §1: The half-plane and the disc

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. I §1 (pp. 1–6;
`full.md` P1:225–473).

Conventions of the book, as modelled here (see the root file `References/GarnettMarshall2005.lean`): `ℍ` is
`LiZhongQC.upperHalf` and `𝔻` is `LiZhongQC.unitDisc`; `∂𝔻` is `Metric.sphere 0 1`, with `e^{iθ} = circleMap 0 1 θ`,
and a function "on `∂𝔻`" is a function on `ℂ` read on the circle. The extended plane is `ℂ* = LiZhongQC.ExtPlane`,
and `∂Ω` is the boundary in `ℂ*` (so `∂ℍ = ℝ ∪ {∞}`). Harmonic functions are Mathlib's
`InnerProductSpace.HarmonicOnNhd` on sets of `ℂ`, and `HarmonicOnExt` (harmonicity in the charts of `ℂ*`) on sets of
`ℂ*`; functions may be complex-valued (P1:286). `limsup_{z→ζ} u(z) ≤ 0` is written in `ε`-form. The measure `dθ` on
`∂𝔻` is `arcMeasure` (total mass `2π`, not normalized). Harmonic measure is a measure in its set variable
(`harmonicMeasureUHP z : Measure ℝ`, `harmonicMeasureDisc z : Measure ℂ`); the number `ω(z, E, Ω)` is its value on
`E`, compared in `[0, ∞]` where the book compares measures and written `(… E).toReal` where real arithmetic or real
limits follow (the measures are finite).

* Definition (the upper half-plane `ℍ`, §1) — exists: `LiZhongQC.upperHalf` (the plane set Im z > 0; the real line
  is Mathlib's ℝ, embedded in ℂ by the coercion)
* Definition (harmonic function, §1) — exists: `InnerProductSpace.HarmonicOnNhd` (Mathlib: twice differentiable
  with vanishing Laplacian near each point of the set; real- or complex-valued)
* Definition (harmonic measure `ω(z, E, ℍ)`: (1.1) for finite unions of open intervals, P1:238–248, and (1.5) for
  measurable `E`, P1:362; the Poisson kernel `P_z(t)` for `ℍ`, P1:370; §1) — `harmonicMeasureUHP`,
  `poissonKernelUHP` (defined once, by (1.5); the book's statement that (1.5) agrees with (1.1) is `eq1_1_1`)
* Unlabelled (§1, P1:252–256): properties (i) `0 < ω < 1`, (ii) `ω → 1` at `E`, (iii) `ω → 0` at `ℝ \ Ē` of
  `ω(z, E, ℍ)` for a finite union `E` of open intervals — `harmonicMeasureUHP_mem_Ioo`,
  `tendsto_harmonicMeasureUHP_one`, `tendsto_harmonicMeasureUHP_zero`
* Unlabelled (§1, P1:258): `ω(z, E, ℍ)` is the unique harmonic function on `ℍ` with (i)–(iii) —
  `harmonicMeasureUHP_unique`
* Definition (the extended plane `ℂ* = ℂ ∪ {∞}`, named in §3, P1:729; the boundary `∂Ω` of a region is taken in
  `ℂ*` from Lemma 1.1 on) — exists: `LiZhongQC.ExtPlane` (OnePoint ℂ)
* Definition (region, domain, §1) — exists: `References.IsDomainExt` (an open connected set of ℂ*; a plane region
  is written as an open connected subset of ℂ)
* Lemma 1.1 (Lindelöf's maximum principle, §1) — `lemma1_1_1`
* Definition (the Dirichlet problem for `f ∈ C(∂Ω)` on a domain `Ω`, its solution; harmonic functions on a set of
  `ℂ*`, §1) — `IsDirichletSolution`, `HarmonicOnExt`
* Theorem 1.2 (§1) — `thm1_1_2`
* Unlabelled (§1, P1:368): for a finite union of open intervals the definition (1.5) is the same as (1.1) —
  `eq1_1_1`
* Definition (Poisson integral of `f ∈ C(ℝ ∪ {∞})` on `ℍ`, §1, P1:374–380) — omitted: a name for the solution of
  Theorem 1.2 written as an integral against the Poisson kernel of the upper half-plane; no later statement uses it
  (it reappears only in exercises)
* Unlabelled (§1, P1:382): `ω(z, E, ℍ)` is a harmonic function of `z` and a probability measure in `E` —
  `harmonicMeasureUHP_harmonic`, `isProbabilityMeasure_harmonicMeasureUHP`
* Harnack's inequality (§1, P1:382–388, named) — `harnack_inequality_UHP`
* Definition (the unit disc `𝔻`, §1) — exists: `LiZhongQC.unitDisc` (the open ball of radius 1 about 0)
* Definition (conformal map of `𝔻` onto `ℍ`, §1) — exists: `LiZhongQC.IsConformalOnto` (holomorphic and one-to-one
  on the first set, with image the second set)
* Definition (the measure `dθ` on `∂𝔻`, from (1.6) on; `|E|` in §2) — `arcMeasure`
* Definition ((1.6), harmonic measure `ω(z, E, 𝔻)`, and its Poisson formula, §1, P1:390–400) —
  `harmonicMeasureDisc`
* Unlabelled (§1, P1:392–400): (1.6) does not depend on the conformal map `φ` of `𝔻` onto `ℍ` and equals the
  Poisson formula — `eq1_1_6`
* Definition ((1.7), the Poisson integral `u_f` of `f` on `𝔻`, §1, P1:404–419) — `poissonIntegral`
* Theorem 1.3 (§1) — `thm1_1_3`
* Definition (the Poisson kernel `P_z(θ)` for the disc, §1, P1:419) — exists: `poissonKernel` (Mathlib: poissonKernel
  0 z ζ = (1 − |z|²)/|ζ − z|² for |ζ| = 1; the factor 1/2π is written out in every use, as in poissonIntegral and
  harmonicMeasureDisc; no stated constant depends on it)

Helpers (not book notions): `nhdsExtWithin` (the filter of `z → ζ ∈ ℂ*`, `z ∈ Ω`, for a plane set `Ω`),
`IsFiniteUnionIoo` (`E = ⋃_{j=1}^n (a_j, b_j)`, `b_{j−1} < a_j < b_j`), `openArc` and `IsFiniteUnionOpenArcs`
(finite unions of open arcs of `∂𝔻`).

Not stated (inventory U−, immediate or used only in proofs): the angle function `θ(z) = arg((z − b)/(z − a))`
(P1:229–238, a motivation for (1.1)); the arctan formula for `ω(x + iy, (a, b), ℍ)` (P1:356–360, contained in
`eq1_1_1`); the analogues of (i)–(iii) for `ω(z, E, 𝔻)` (P1:396, the book's reason for the independence in `eq1_1_6`);
the remark that (1.8) survives a change of `f` on a null set away from `e^{iθ₀}` (P1:416); the Dirichlet problem on
`𝔻` for continuous `f` (P1:422–428, immediate from Theorem 1.3); the remarks P1:430–432 (Theorem 1.3 follows from
Theorem 1.2 when `f` is continuous, and Theorem 1.2 extends to `f ∈ L¹(dt/(1 + t²))`). (1.3) and (1.4) are steps of
the proof of Theorem 1.2.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt unitDisc upperHalf IsConformalOnto)
open InnerProductSpace (HarmonicAt HarmonicOnNhd)

/-- The filter "`z → ζ`, `z ∈ Ω`" for a plane set `Ω ⊆ ℂ` and a point `ζ ∈ ℂ*` (helper, not a book notion): at a
finite `ζ` it is `𝓝[Ω] ζ`, at `ζ = ∞` it is "`z → ∞` in `Ω`". -/
def nhdsExtWithin (ζ : ExtPlane) (Ω : Set ℂ) : Filter ℂ :=
  Filter.comap ((↑) : ℂ → ExtPlane) (𝓝 ζ) ⊓ 𝓟 Ω

/-- `E ⊆ ℝ` is a finite union of open intervals written `E = ⋃_{j=1}^n (a_j, b_j)` with `b_{j−1} < a_j < b_j`
(helper, Ch. I §1, P1:238): `n ≥ 1` intervals with finite endpoints, indexed by `Fin n`, with `a_j < b_j`, and
`b_i < a_j` for `i < j`.
Modelling: the book's strict separation `b_{j−1} < a_j`; touching unions (used in the proof of Theorem 1.2) change
none of (i)–(iii), the uniqueness or (1.5). -/
def IsFiniteUnionIoo (E : Set ℝ) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → ℝ), 0 < n ∧ (∀ j, a j < b j) ∧ (∀ i j, i < j → b i < a j) ∧
    E = ⋃ j, Ioo (a j) (b j)

/-- **Definition** (the Poisson kernel for `ℍ`, Ch. I §1, P1:370). For `z = x + iy ∈ ℍ` and `t ∈ ℝ`,
`P_z(t) = (1/π) · y/((x − t)² + y²)`. Junk: for `z ∉ ℍ` the value is `≤ 0`; it is never used there. B-cand.:
Mathlib's ProbabilityTheory.cauchyPDFReal (the same density for `z ∈ ℍ`, as a Cauchy density with location `x` and
scale `y`); the book's own formula is kept, with no comparison theorem. -/
def poissonKernelUHP (z : ℂ) (t : ℝ) : ℝ :=
  1 / π * (z.im / ((z.re - t) ^ 2 + z.im ^ 2))

/-- **Definition** (harmonic measure of `ℍ`, (1.5), Ch. I §1, P1:362; the book's (1.1), P1:248, for finite unions of
open intervals, see `eq1_1_1`). For `z = x + iy ∈ ℍ` and measurable `E ⊆ ℝ`,
`ω(z, E, ℍ) = ∫_E y/((t − x)² + y²) dt/π`: the measure on `ℝ` with density `P_z` with respect to Lebesgue measure.
Junk: the zero measure for `z ∉ ℍ` (the density is clamped at `0`); never used there. B-cand.: Mathlib's
ProbabilityTheory.cauchyMeasure (the same measure for `z ∈ ℍ`); the literal (1.5) is kept, with no comparison
theorem. -/
def harmonicMeasureUHP (z : ℂ) : Measure ℝ :=
  volume.withDensity fun t => ENNReal.ofReal (poissonKernelUHP z t)

/-- **Unlabelled** (Ch. I §1, P1:252, property (i)). If `E ⊆ ℝ` is a finite union of open intervals, then
`0 < ω(z, E, ℍ) < 1` for `z ∈ ℍ`. -/
theorem harmonicMeasureUHP_mem_Ioo {E : Set ℝ} (hE : IsFiniteUnionIoo E) {z : ℂ} (hz : z ∈ upperHalf) :
    harmonicMeasureUHP z E ∈ Ioo 0 1 := by
  sorry

/-- **Unlabelled** (Ch. I §1, P1:254, property (ii)). If `E ⊆ ℝ` is a finite union of open intervals, then
`ω(z, E, ℍ) → 1` as `z → E`.
Modelling: `z → t` for each `t ∈ E`, with `z ∈ ℍ` (as the property is used in the proof of Theorem 1.2). -/
theorem tendsto_harmonicMeasureUHP_one {E : Set ℝ} (hE : IsFiniteUnionIoo E) {t : ℝ} (ht : t ∈ E) :
    Tendsto (fun z => (harmonicMeasureUHP z E).toReal) (𝓝[upperHalf] (t : ℂ)) (𝓝 1) := by
  sorry

/-- **Unlabelled** (Ch. I §1, P1:256, property (iii)). If `E ⊆ ℝ` is a finite union of open intervals, then
`ω(z, E, ℍ) → 0` as `z → ℝ \ Ē`.
Modelling: `z → t` for each real `t ∉ Ē`, with `z ∈ ℍ`. -/
theorem tendsto_harmonicMeasureUHP_zero {E : Set ℝ} (hE : IsFiniteUnionIoo E) {t : ℝ} (ht : t ∉ closure E) :
    Tendsto (fun z => (harmonicMeasureUHP z E).toReal) (𝓝[upperHalf] (t : ℂ)) (𝓝 0) := by
  sorry

/-- **Unlabelled** (Ch. I §1, P1:258). For a finite union `E` of open intervals, `ω(z, E, ℍ)` is the unique harmonic
function on `ℍ` that satisfies (i), (ii) and (iii) (a consequence of Lemma 1.1). -/
theorem harmonicMeasureUHP_unique {E : Set ℝ} (hE : IsFiniteUnionIoo E) :
    HarmonicOnNhd (fun z => (harmonicMeasureUHP z E).toReal) upperHalf ∧
      ∀ v : ℂ → ℝ, HarmonicOnNhd v upperHalf → (∀ z ∈ upperHalf, 0 < v z ∧ v z < 1) →
        (∀ t ∈ E, Tendsto v (𝓝[upperHalf] (t : ℂ)) (𝓝 1)) →
        (∀ t : ℝ, t ∉ closure E → Tendsto v (𝓝[upperHalf] (t : ℂ)) (𝓝 0)) →
        EqOn v (fun z => (harmonicMeasureUHP z E).toReal) upperHalf := by
  sorry

/-- **Lemma 1.1** (Lindelöf; Ch. I §1). Suppose the function `u` is harmonic and bounded above on a region `Ω` such
that `Ω̄ ≠ ℂ`. Let `F` be a finite subset of `∂Ω` and suppose (1.2) `limsup_{z→ζ} u(z) ≤ 0` for all `ζ ∈ ∂Ω \ F`.
Then `u ≤ 0` on `Ω`.
Modelling: `Ω` is a plane region (open and connected in `ℂ`) and `u` is real-valued; `∂Ω` is the boundary in `ℂ*`,
which contains `∞` when `Ω` is unbounded (the proof maps `Ω` by `1/(z − z₀)`, and in the book's uses `F` may
contain `∞`, e.g. for `ℍ`); (1.2) is written in `ε`-form along the filter `nhdsExtWithin ζ Ω`. -/
theorem lemma1_1_1 {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩ : closure Ω ≠ univ) {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u Ω) (hub : BddAbove (u '' Ω)) {F : Set ExtPlane} (hF : F.Finite)
    (hFΩ : F ⊆ frontier (toExt Ω))
    (h12 : ∀ ζ ∈ frontier (toExt Ω) \ F, ∀ ε > 0, ∀ᶠ z in nhdsExtWithin ζ Ω, u z ≤ ε) :
    ∀ z ∈ Ω, u z ≤ 0 := by
  sorry

/-- **Definition** (harmonic function on a set of `ℂ*`, Ch. I §1; at `∞` as GM defines it, P1:3296). `u` is
harmonic at every point `z ∈ Ω`, read in the chart of `ℂ*` at `z` (`LehtoVirtanen1973.extChartInv`): at a finite `z`
this is harmonicity of `u` near `z`; at `z = ∞` it is harmonicity of `ζ ↦ u(1/ζ)` at `0`, with the value `u(∞)` at
`0`. -/
def HarmonicOnExt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (u : ExtPlane → V) (Ω : Set ExtPlane) :
    Prop :=
  ∀ z ∈ Ω, HarmonicAt (u ∘ LehtoVirtanen1973.extChartInv z) 0

/-- **Definition** (the Dirichlet problem, Ch. I §1, P1:282). Given a domain `Ω` and a function `f ∈ C(∂Ω)`, the
Dirichlet problem for `f` on `Ω` is to find a function `u ∈ C(Ω̄)` such that `Δu = 0` on `Ω` and `u|∂Ω = f`; such a
`u` is a solution of the Dirichlet problem for `f` on `Ω`.
Modelling: `Ω ⊆ ℂ*`, with closure and boundary in `ℂ*`; `Δu = 0` on `Ω` is `HarmonicOnExt u Ω`. -/
def IsDirichletSolution {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (Ω : Set ExtPlane)
    (f u : ExtPlane → V) : Prop :=
  ContinuousOn u (closure Ω) ∧ HarmonicOnExt u Ω ∧ EqOn u f (frontier Ω)

/-- **Theorem 1.2** (Ch. I §1). Suppose `f ∈ C(ℝ ∪ {∞})`. Then there exists a unique function
`u = u_f ∈ C(closure(ℍ ∪ {∞}))` such that `u` is harmonic on `ℍ` and `u|∂ℍ = f`.
Modelling: `f` is complex-valued (the proof reduces to real `f`, P1:286); `ℝ ∪ {∞} = ∂ℍ` is the boundary of `ℍ` in
`ℂ*` (the project's `LiZhongQC.extRealLine`, equal to it by `LiZhongQC.h36t_extRealLine_eq_frontier`); uniqueness
is on `closure(ℍ ∪ {∞})`, the only values the statement sees. -/
theorem thm1_1_2 {f : ExtPlane → ℂ} (hf : ContinuousOn f (frontier (toExt upperHalf))) :
    ∃ u : ExtPlane → ℂ, IsDirichletSolution (toExt upperHalf) f u ∧
      ∀ v : ExtPlane → ℂ, IsDirichletSolution (toExt upperHalf) f v → EqOn v u (closure (toExt upperHalf)) := by
  sorry

/-- **Unlabelled** (Ch. I §1, P1:368; the definition (1.1), P1:238–248). When `E = ⋃_{j=1}^n (a_j, b_j)` with
`b_{j−1} < a_j < b_j`, the definition (1.5) is the same as the definition (1.1):
`ω(z, E, ℍ) = Σ_j θ_j(z)/π` with `θ_j(z) = arg((z − b_j)/(z − a_j))`, for `z ∈ ℍ`.
Modelling: the intervals are indexed by `Fin n`; for `z ∈ ℍ` the quotient `(z − b_j)/(z − a_j)` lies in the upper
half-plane, where the principal value `Complex.arg ∈ (0, π)` is the book's branch. -/
theorem eq1_1_1 {n : ℕ} {a b : Fin n → ℝ} (hab : ∀ j, a j < b j) (hba : ∀ i j, i < j → b i < a j) {z : ℂ}
    (hz : z ∈ upperHalf) :
    (harmonicMeasureUHP z (⋃ j, Ioo (a j) (b j))).toReal = ∑ j, arg ((z - b j) / (z - a j)) / π := by
  sorry

/-- **Unlabelled** (Ch. I §1, P1:382, first half; cited at P1:4098, "As in Chapter I, `ω(z, A, Ω)` is a harmonic
function of `z`"). For measurable `E ⊆ ℝ`, the harmonic measure `ω(z, E, ℍ)` is a harmonic function of `z ∈ ℍ`. -/
theorem harmonicMeasureUHP_harmonic {E : Set ℝ} (hE : MeasurableSet E) :
    HarmonicOnNhd (fun z => (harmonicMeasureUHP z E).toReal) upperHalf := by
  sorry

/-- **Unlabelled** (Ch. I §1, P1:382, second half). For `z ∈ ℍ`, the harmonic measure `E ↦ ω(z, E, ℍ)` is a
probability measure. -/
theorem isProbabilityMeasure_harmonicMeasureUHP {z : ℂ} (hz : z ∈ upperHalf) :
    IsProbabilityMeasure (harmonicMeasureUHP z) := by
  sorry

/-- **Harnack's inequality** (Ch. I §1, P1:382–388, named). If `z₁, z₂ ∈ ℍ`, then
`0 < C⁻¹ ≤ ω(z₁, E, ℍ)/ω(z₂, E, ℍ) ≤ C < ∞`, where `C` depends on `z₁` and `z₂` but not on `E`.
Modelling: `∀ z₁ z₂, ∃ C, ∀ E` for measurable `E`; the ratio is multiplied out and the measures are compared in
`[0, ∞]`, so that no `0/0` arises when `ω(z₂, E, ℍ) = 0`. The later citations of "Harnack's inequality" (Ch. II–X)
refer to the general inequality of Exercise I.5(a), an exercise, not this statement. -/
theorem harnack_inequality_UHP {z₁ z₂ : ℂ} (h₁ : z₁ ∈ upperHalf) (h₂ : z₂ ∈ upperHalf) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ E : Set ℝ, MeasurableSet E →
      (C : ℝ≥0∞)⁻¹ * harmonicMeasureUHP z₂ E ≤ harmonicMeasureUHP z₁ E ∧
        harmonicMeasureUHP z₁ E ≤ C * harmonicMeasureUHP z₂ E := by
  sorry

/-- **Definition** (the measure `dθ` on `∂𝔻`, Ch. I §1, used from (1.6) on; written `|E|` from §2, P1:501). The
arc-length (Lebesgue) measure of the unit circle, as a measure on `ℂ`: the image of Lebesgue measure on `(0, 2π]`
under `θ ↦ e^{iθ}`, of total mass `2π`. So `f ∈ Lᵖ(∂𝔻)` is `MemLp f p arcMeasure` and `‖f‖_p` is
`eLpNorm f p arcMeasure`, taken with respect to `dθ` as in the book. -/
def arcMeasure : Measure ℂ :=
  Measure.map (circleMap 0 1) (volume.restrict (Ioc 0 (2 * π)))

/-- The open arc `{e^{iθ} : a < θ < b}` of `∂𝔻` (helper); an open arc (open interval) of `∂𝔻` is `openArc a b` with
`a < b ≤ a + 2π`, of length `b − a`. -/
def openArc (a b : ℝ) : Set ℂ := circleMap 0 1 '' Ioo a b

/-- `E ⊆ ∂𝔻` is a finite union of open arcs of `∂𝔻` (helper, Ch. I §1, P1:390). -/
def IsFiniteUnionOpenArcs (E : Set ℂ) : Prop :=
  ∃ s : Finset (ℝ × ℝ), (∀ p ∈ s, p.1 < p.2 ∧ p.2 ≤ p.1 + 2 * π) ∧ E = ⋃ p ∈ s, openArc p.1 p.2

/-- **Definition** (harmonic measure of `𝔻`, (1.6), Ch. I §1, P1:390–400). For `z ∈ 𝔻`,
`ω(z, E, 𝔻) = ∫_E (1 − |z|²)/|e^{iθ} − z|² dθ/2π`: the measure on `∂𝔻` with density `P_z(θ)` with respect to `dθ`
(`P_z(θ)` is Mathlib's `poissonKernel 0 z (e^{iθ})` times `1/2π`). The book defines (1.6) for finite unions of open
arcs through a conformal map of `𝔻` onto `ℍ` and derives this formula (`eq1_1_6`); it uses the formula for measurable
`E` from P1:725 on, and for Borel `E` in (3.3). Junk: the zero measure for `|z| ≥ 1` (the density is clamped at
`0`); never used there. -/
def harmonicMeasureDisc (z : ℂ) : Measure ℂ :=
  arcMeasure.withDensity fun ζ => ENNReal.ofReal (poissonKernel 0 z ζ / (2 * π))

/-- **Unlabelled** (Ch. I §1, P1:392–400; the definition (1.6)). Let `E` be a finite union of open arcs of `∂𝔻` and
`φ` any conformal map of `𝔻` onto `ℍ`. Then `ω(z, E, 𝔻) = ω(φ(z), φ(E), ℍ)`; so (1.6) does not depend on the choice
of `φ`, and by the change of variables `φ(z) = i(1 + z)/(1 − z)` it equals the Poisson formula of
`harmonicMeasureDisc`.
Modelling: `φ(E)` is the image of `E` under the continuous extension `Φ : 𝔻̄ → ℂ*` of `φ`; it lies in
`∂ℍ = ℝ ∪ {∞}`, and `ω(·, ·, ℍ)` sees its real part `φ(E) ∩ ℝ` (the point `∞` carries no mass). -/
theorem eq1_1_6 {φ : ℂ → ℂ} (hφ : IsConformalOnto φ unitDisc upperHalf) {Φ : ℂ → ExtPlane}
    (hΦ : ContinuousOn Φ (closedBall 0 1)) (hΦφ : ∀ z ∈ unitDisc, Φ z = ((φ z : ℂ) : ExtPlane)) {E : Set ℂ}
    (hE : IsFiniteUnionOpenArcs E) {z : ℂ} (hz : z ∈ unitDisc) :
    harmonicMeasureDisc z E = harmonicMeasureUHP (φ z) {t : ℝ | ((t : ℂ) : ExtPlane) ∈ Φ '' E} := by
  sorry

/-- **Definition** (the Poisson integral of `f` on `𝔻`, (1.7), Ch. I §1, P1:404–419).
`u_f(z) = ∫₀^{2π} f(e^{iθ}) (1 − |z|²)/|e^{iθ} − z|² dθ/2π`, for a function `f` on `∂𝔻` (a function on `ℂ` read on
the circle) valued in a real normed space. Junk: `0` when `f` is not integrable on `∂𝔻` or `V` is not complete (the
Bochner convention; every statement uses `V = ℂ` and assumes integrability); for `|z| ≥ 1` the kernel is not the
Poisson kernel (never used there). -/
def poissonIntegral {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : ℂ → V) (z : ℂ) : V :=
  Real.circleAverage (fun ζ => poissonKernel 0 z ζ • f ζ) 0 1

/-- **Theorem 1.3** (Ch. I §1). Let `f(e^{iθ})` be an integrable function on `∂𝔻` and let `u = u_f` be its Poisson
integral (1.7). Then `u` is harmonic on `𝔻`. If `f` is continuous at `e^{iθ₀} ∈ ∂𝔻`, then (1.8)
`lim_{𝔻∋z→e^{iθ₀}} u(z) = f(e^{iθ₀})`.
Modelling: `f` is complex-valued (the proof reduces to real `f`) and integrable with respect to `dθ`; "continuous at
`e^{iθ₀}`" is continuity of `f` as a function on `∂𝔻`. -/
theorem thm1_1_3 {f : ℂ → ℂ} (hf : Integrable f arcMeasure) :
    HarmonicOnNhd (poissonIntegral f) unitDisc ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1, ContinuousWithinAt f (sphere 0 1) ζ →
        Tendsto (poissonIntegral f) (𝓝[unitDisc] ζ) (𝓝 (f ζ)) := by
  sorry

end GarnettMarshall2005
