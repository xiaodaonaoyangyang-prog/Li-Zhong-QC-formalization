import References.Pommerenke1992.Ch02.S05_LimitsAndClusterSets

/-!
# Pommerenke 1992, Ch. 2 §2.6 Countability Theorems

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §2.6; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 1570–1694.

* Definition (coloured triod, §2.6) — `ColouredTriod`
* Proposition 2.18 (G. Jensen's colour version of Moore's triod theorem) — `prop2_18`
* Moore's triod theorem (quoted: "every system of disjoint triods in the plane is countable", l. 1583) —
  `moore_triod`
* Corollary 2.19 — `cor2_19`
* Definition (ambiguous point, (2.6.3); arcs ending at a point of `𝕋`) — `IsAmbiguousPoint`, `IsArcEndingAt`
* Corollary 2.20 (Bagemihl's ambiguous point theorem) — `cor2_20`
* Definition (the left- and right-hand cluster sets `C⁺`, `C⁻`, (2.6.5)) — `clusterSetLeft`, `clusterSetRight`
* Proposition 2.21 (Collingwood's symmetry theorem) — `prop2_21`
* Definition (symmetric prime end, §2.6) — `IsSymmetricPrimeEnd`
* Proposition 2.22 — `prop2_22`
* Definition (set of first category on `𝕋`, §2.6) — exists: `IsMeagre` (Mathlib, in the topology of `Circle`: a
  countable union of nowhere dense sets, and a subset of the circle is nowhere dense exactly when its closure contains
  no proper arc)
* Baire category theorem (quoted, §2.6: non-empty open sets are not of first category) — exists:
  `not_isMeagre_of_isOpen` (Mathlib, in the Baire space `Circle`)
* Proposition 2.23 (Collingwood's maximality theorem) — `prop2_23`
* Definition (the four kinds of prime ends; the sets `E_j`, §2.6) — `HasPrimeEndKind`, `kindSet`
* Unlabelled (§2.6, l. 1692: there is a domain with `E₁ = ∅`, where `E₂` has measure `2π` and is of first category and
  `E₃` has measure `0` and is not of first category; cited at l. 6067, "see Section 2.6") — `exists_domain_E1_empty`

Not items (DESIGN §3): (2.6.1) (a special case of Corollary 2.19); the example `exp[-(1 + z)/(1 - z)]`;
`C^± ⊆ C` (immediate); the remarks after Proposition 2.21 and 2.22; "`E₂`, `E₄` are of first category, `E₃`, `E₄`
have measure zero" (l. 1690, not cited); Frankl's example and the further references (quoted, not cited).

**Conventions.** As in §2.5. Triods lie in `ℂ`; their arcs are closed Jordan arcs with given endpoints
(`LehtoVirtanen1973.IsArcFromTo`). Arguments are measured relative to `ζ`: `arg z > arg ζ` is `arg (z/ζ) > 0`, which
avoids the branch cut. Measures of subsets of `𝕋` are the Lebesgue measures of their parameter sets in `(0, 2π]`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane toExt unitDisc IsHomeomorphOnto)
open LehtoVirtanen1973 (IsConformalMap IsArcFromTo)

/-- **Definition** (§2.6). A coloured triod in `ℂ`: the union of three Jordan arcs `B, R, Y` (blue, red, yellow) that
have one endpoint, the junction point (black), in common and are otherwise disjoint. -/
structure ColouredTriod where
  /-- The blue arc `B`. -/
  blue : Set ℂ
  /-- The red arc `R`. -/
  red : Set ℂ
  /-- The yellow arc `Y`. -/
  yellow : Set ℂ
  /-- The junction point. -/
  junction : ℂ
  blue_arc : ∃ q : ExtPlane, IsArcFromTo (toExt blue) junction q
  red_arc : ∃ q : ExtPlane, IsArcFromTo (toExt red) junction q
  yellow_arc : ∃ q : ExtPlane, IsArcFromTo (toExt yellow) junction q
  blue_red : blue ∩ red = {junction}
  blue_yellow : blue ∩ yellow = {junction}
  red_yellow : red ∩ yellow = {junction}

/-- **Proposition 2.18** (§2.6; G. Jensen's colour version of the Moore triod theorem). Let `𝓜` be a system of
coloured triods in `ℂ` with distinct junction points such that sets of different colours do not meet. Then `𝓜` is
countable.
Modelling: "sets of different colours do not meet" concerns distinct triods (the three arcs of one triod meet at its
junction point). -/
theorem prop2_18 {M : Set ColouredTriod} (hj : InjOn ColouredTriod.junction M)
    (hcol : ∀ T ∈ M, ∀ T' ∈ M, T ≠ T' →
      Disjoint T.blue T'.red ∧ Disjoint T.blue T'.yellow ∧ Disjoint T.red T'.blue ∧
        Disjoint T.red T'.yellow ∧ Disjoint T.yellow T'.blue ∧ Disjoint T.yellow T'.red) :
    M.Countable := by
  sorry

/-- **Moore's triod theorem** (§2.6, l. 1583, quoted as an immediate consequence of Proposition 2.18). Every system of
disjoint (uncoloured) triods in the plane is countable. -/
theorem moore_triod {M : Set ColouredTriod}
    (hdisj : ∀ T ∈ M, ∀ T' ∈ M, T ≠ T' →
      Disjoint (T.blue ∪ T.red ∪ T.yellow) (T'.blue ∪ T'.red ∪ T'.yellow)) :
    M.Countable := by
  sorry

/-- **Corollary 2.19** (§2.6). Let `f` be a homeomorphism of `𝔻` into `ℂ`. Then there are at most countably many points
`a ∈ ℂ` such that (2.6.2) `f(rζ_j) → a` as `r → 1-` (`j = 1, 2, 3`) for three distinct points `ζ₁, ζ₂, ζ₃` on `𝕋`.
(The OCR's "`ρ → 1-`" is `r → 1-`.) -/
theorem cor2_19 {f : ℂ → ℂ} (hf : IsHomeomorphOnto f unitDisc (f '' unitDisc)) :
    {a : ℂ | ∃ ζ : Fin 3 → ℂ, Function.Injective ζ ∧ (∀ j, ζ j ∈ sphere (0 : ℂ) 1) ∧
      ∀ j, Tendsto (fun r : ℝ => f (r * ζ j)) (𝓝[<] 1) (𝓝 a)}.Countable := by
  sorry

/-- **Definition** (§2.6). An arc in `𝔻` ending at `ζ ∈ 𝕋`: the point set of a half-open curve in `𝔻`, injective,
ending at `ζ`. -/
def IsArcEndingAt (Γ : Set ℂ) (ζ : ℂ) : Prop :=
  ∃ C : HalfOpenCurve, InjOn C.toFun (Ico C.α C.β) ∧ C.toFun '' Ico C.α C.β ⊆ unitDisc ∧ C.EndsAt ζ ∧
    Γ = C.toFun '' Ico C.α C.β

/-- **Definition (2.6.3)** (§2.6). `ζ ∈ 𝕋` is an ambiguous point of `f` (any function from `𝔻` to `Ĉ`): there are two
arcs `Γ₁, Γ₂` ending at `ζ` such that `C_{Γ₁}(f, ζ) ∩ C_{Γ₂}(f, ζ) = ∅`. -/
def IsAmbiguousPoint (f : ℂ → ExtPlane) (ζ : ℂ) : Prop :=
  ∃ Γ₁ Γ₂ : Set ℂ, IsArcEndingAt Γ₁ ζ ∧ IsArcEndingAt Γ₂ ζ ∧
    Disjoint (clusterSetAlong f Γ₁ ζ) (clusterSetAlong f Γ₂ ζ)

/-- **Corollary 2.20** (§2.6; Bagemihl's ambiguous point theorem). Any function from `𝔻` to `Ĉ` has at most countably
many ambiguous points. -/
theorem cor2_20 (f : ℂ → ExtPlane) : {ζ ∈ sphere (0 : ℂ) 1 | IsAmbiguousPoint f ζ}.Countable := by
  sorry

/-- **Definition (2.6.5)** (§2.6). The left-hand cluster set `C⁺(f, ζ)` at `ζ ∈ 𝕋`: the `ω ∈ Ĉ` for which there are
`z_n ∈ 𝔻` with `arg z_n > arg ζ`, `z_n → ζ` and `f(z_n) → ω`.
Modelling: `arg z_n > arg ζ` is `arg (z_n/ζ) > 0` (the side of the radius to `ζ`). -/
def clusterSetLeft (f : ℂ → ExtPlane) (ζ : ℂ) : Set ExtPlane :=
  {ω | ∃ z : ℕ → ℂ, (∀ n, z n ∈ unitDisc ∧ 0 < arg (z n / ζ)) ∧ Tendsto z atTop (𝓝 ζ) ∧
    Tendsto (f ∘ z) atTop (𝓝 ω)}

/-- **Definition** (§2.6). The right-hand cluster set `C⁻(f, ζ)`: as `C⁺(f, ζ)` with `arg z_n < arg ζ`. -/
def clusterSetRight (f : ℂ → ExtPlane) (ζ : ℂ) : Set ExtPlane :=
  {ω | ∃ z : ℕ → ℂ, (∀ n, z n ∈ unitDisc ∧ arg (z n / ζ) < 0) ∧ Tendsto z atTop (𝓝 ζ) ∧
    Tendsto (f ∘ z) atTop (𝓝 ω)}

/-- **Proposition 2.21** (§2.6; Collingwood's symmetry theorem). If `f` is any function from `𝔻` to `Ĉ`, then (2.6.6)
`C⁺(f, ζ) = C⁻(f, ζ) = C(f, ζ)` except for at most countably many `ζ ∈ 𝕋`. -/
theorem prop2_21 (f : ℂ → ExtPlane) :
    {ζ ∈ sphere (0 : ℂ) 1 |
      ¬ (clusterSetLeft f ζ = clusterSet f ζ ∧ clusterSetRight f ζ = clusterSet f ζ)}.Countable := by
  sorry

/-- **Definition** (§2.6). The prime end `p = f̂(ζ)` is symmetric if (2.6.6) holds at `ζ`:
`C⁺(f, ζ) = C⁻(f, ζ) = C(f, ζ)`.
Modelling: a predicate of the point `ζ ∈ 𝕋`; the prime end `p = f̂(ζ)` corresponds to `ζ` through the bijection of
Theorem 2.15. -/
def IsSymmetricPrimeEnd (f : ℂ → ExtPlane) (ζ : ℂ) : Prop :=
  clusterSetLeft f ζ = clusterSet f ζ ∧ clusterSetRight f ζ = clusterSet f ζ

/-- **Proposition 2.22** (§2.6). Let `f` map `𝔻` conformally onto `G`. Let `ζ` and `ζ'` be distinct points on `𝕋` where
`f` has radial limits `ω` and `ω'`. Suppose that the prime end `p = f̂(ζ)` is symmetric and that `ω' ∈ I(p)`. Then
`I(p)` is the smallest compact connected subset of `∂G` containing `ω` and `ω'`. In particular, if `ω = ω'`, then
`I(p) = {ω}`. -/
theorem prop2_22 {G : Set ExtPlane} {f : ExtPlane → ExtPlane} (hf : IsConformalMap f (toExt unitDisc))
    (hfG : f '' toExt unitDisc = G) {fhat : ℂ → Set (ℕ → Set ExtPlane)} (hfhat : IsPrimeEndCorrespondence G f fhat)
    {ζ ζ' : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) (hζ' : ζ' ∈ sphere (0 : ℂ) 1) (hne : ζ ≠ ζ') {ω ω' : ExtPlane}
    (hω : HasRadialLimit (fun z : ℂ => f z) ζ ω) (hω' : HasRadialLimit (fun z : ℂ => f z) ζ' ω')
    (hsym : IsSymmetricPrimeEnd (fun z : ℂ => f z) ζ) (hω'I : ω' ∈ impression G (fhat ζ)) :
    IsLeast {K | IsCompact K ∧ IsConnected K ∧ K ⊆ frontier G ∧ ω ∈ K ∧ ω' ∈ K} (impression G (fhat ζ)) ∧
      (ω = ω' → impression G (fhat ζ) = {ω}) := by
  sorry

/-- **Proposition 2.23** (§2.6; Collingwood's maximality theorem). If `f` is continuous in `𝔻`, then
`C(f, ζ) = C_{[0,ζ)}(f, ζ)` for `ζ ∈ 𝕋` except for a set of first category.
Modelling: the exceptional set is meagre in the topology of `Circle`. -/
theorem prop2_23 {f : ℂ → ExtPlane} (hf : ContinuousOn f unitDisc) :
    IsMeagre {ζ : Circle | clusterSet f ζ ≠ clusterSetAlong f (radius ζ) ζ} := by
  sorry

/-- **Definition** (§2.6, the table). The prime end `p` is of the `j`th kind (`j = 1, …, 4`):
first kind, `Π(p) = I(p)` a single point; second kind, `Π(p)` a single point `≠ I(p)`; third kind, `Π(p) = I(p)` not
a single point; fourth kind, `Π(p) ≠ I(p)` and `Π(p)` not a single point. -/
def HasPrimeEndKind (G : Set ExtPlane) (P : Set (ℕ → Set ExtPlane)) : ℕ → Prop
  | 1 => principalPoints P = impression G P ∧ ∃ a, principalPoints P = {a}
  | 2 => principalPoints P ≠ impression G P ∧ ∃ a, principalPoints P = {a}
  | 3 => principalPoints P = impression G P ∧ ¬ ∃ a, principalPoints P = {a}
  | 4 => principalPoints P ≠ impression G P ∧ ¬ ∃ a, principalPoints P = {a}
  | _ => False

/-- **Definition** (§2.6). `E_j = {ζ ∈ 𝕋 : f̂(ζ) is of the j-th kind}`, `j = 1, …, 4`. -/
def kindSet (G : Set ExtPlane) (fhat : ℂ → Set (ℕ → Set ExtPlane)) (j : ℕ) : Set ℂ :=
  {ζ ∈ sphere (0 : ℂ) 1 | HasPrimeEndKind G (fhat ζ) j}

/-- **Unlabelled claim** (§2.6, l. 1692, quoted from Carathéodory and Collingwood–Lohwater; cited at l. 6067, "see
Section 2.6"). There is a domain with `E₁ = ∅`, so that `C(f, ζ)` is a continuum for each `ζ ∈ 𝕋`. In this case `E₂`
has measure `2π` but is of first category, whereas `E₃` has measure `0` but is not of first category.
Modelling: the measures are those of the parameter sets `{t ∈ (0, 2π] : e^{it} ∈ E_j}` (outer measure; measurability
is not asserted). The facts of l. 1690 used here (`E₂`, `E₄` of first category; `E₃`, `E₄` of measure zero) hold for
every domain; the statement asserts the existence of one domain with `E₁ = ∅` and these properties. -/
theorem exists_domain_E1_empty :
    ∃ (G : Set ExtPlane) (f : ExtPlane → ExtPlane) (fhat : ℂ → Set (ℕ → Set ExtPlane)),
      IsConformalMap f (toExt unitDisc) ∧ f '' toExt unitDisc = G ∧ IsPrimeEndCorrespondence G f fhat ∧
      kindSet G fhat 1 = ∅ ∧ (∀ ζ ∈ sphere (0 : ℂ) 1, IsContinuum (clusterSet (fun z : ℂ => f z) ζ)) ∧
      volume {t ∈ Ioc (0 : ℝ) (2 * π) | exp (t * I) ∈ kindSet G fhat 2} = ENNReal.ofReal (2 * π) ∧
      IsMeagre {ζ : Circle | (ζ : ℂ) ∈ kindSet G fhat 2} ∧
      volume {t ∈ Ioc (0 : ℝ) (2 * π) | exp (t * I) ∈ kindSet G fhat 3} = 0 ∧
      ¬ IsMeagre {ζ : Circle | (ζ : ℂ) ∈ kindSet G fhat 3} := by
  sorry

end Pommerenke1992
