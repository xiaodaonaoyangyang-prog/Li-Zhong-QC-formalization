import References.GarnettMarshall2005.Ch02.S04_BoundarySmoothness

/-!
# Garnett–Marshall, Chapter III §1: Capacity and Green's functions

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. III, introduction and
§1 (pp. 73–77; `full.md` P1:3266–3485).

Conventions of Chapter III §1–§4, as modelled here. `E` is a compact plane set (`E : Set ℂ`); `ℂ* \ E` is the set
`(toExt E)ᶜ` of `ℂ*`, its component containing `∞` is `unboundedComponentExt E`, and `Ê = ℂ \ Ω` is `filledSet E`.
For a domain `Ω ∋ ∞` of `ℂ*` the plane set `ℂ* \ Ω` is `finitePart Ωᶜ`. Capacity and Robin's constant come in the
book's stages (leader ruling B1): for `E` whose complement is a finitely connected Jordan domain, `γ(E) = h(∞, ∞)`
(`robinConstantFC`) and `Cap(E) = e^{−γ(E)}` (`capacityFC`), real numbers; for compact `E`, (1.3)
`Cap(E) = lim Cap(E_n)` (`capacityCompact`, in `[0, ∞]`) and `γ(E) = log(1/Cap(E))` (`robinConstantCompact`, in
`[−∞, +∞]` through `ENNReal.log`, so that `γ(E) = +∞` exactly when `Cap(E) = 0` and no junk value `log 0` arises).
A statement uses the most general stage defined at its place in the book, except where it is set explicitly in the
finitely connected case. The sequences `{Ω_n}` of §1 are `IsSmoothExhaustion`; every notion built on them is the
value over all such sequences (the registered "value over all maps" pattern; a single value by
`capacityCompact_indep` and (1.7)); their existence is Exercise II.10(b), an exercise, not an item. Green's function
of an arbitrary domain, `g_Ω(z, w) = lim g_{Ω_n}(z, w)` (1.7), is `greenFunctionLim`, real-valued (leader ruling
B4); its junk value `0` at `z = w` and when the limit is `+∞` (`Cap(E) = 0`) is excluded by the hypotheses
`Cap(E) > 0` and `z ≠ w` of every statement. Limits `z → ∞` are taken along the cocompact filter of `ℂ`. The book
uses tacitly that the finitely connected stage and the compact stage agree for `E` with a smooth finitely connected
complement (P1:3342, and the proof of Theorem 4.1); this is not stated, so it is not an item. For discs the value
`r` at the compact stage is `example3_1_1_a` (with `ψ(z) = (z − c)/r`), and at the Borel stage (4.8) it is the
same by (1.5), `eq3_1_5`.

* Definition (Robin's constant `γ(E) = h(∞, ∞)` for `E` with a finitely connected Jordan complement, §1,
  P1:3284–3302) — `robinConstantFC`
* Definition (harmonic at `∞`: `u(1/z)` harmonic on a neighbourhood of `0`, recalled at P1:3296, §1) — exists:
  `GarnettMarshall2005.HarmonicOnExt` (harmonicity in the charts of ℂ*, the chart at ∞ being z ↦ 1/z)
* Formula (1.1) (§1, with the independence of `γ` from the point `a`) — `eq3_1_1`
* Definition (logarithmic capacity `Cap(E) = e^{−γ(E)}` for `E` with a finitely connected Jordan complement, §1,
  P1:3308–3312) — `capacityFC`
* Formula (1.2) (§1, with `g_{Ω₁}(z, ∞) = g_{Ω₂}(ψ(z), ∞)` and `γ(E₁) = γ(E₂) + log a`) — `eq3_1_2`
* Unlabelled (§1, P1:3340): the capacity of a closed disc is its radius — `capacityFC_closedBall`
* Definition (the component `Ω` of `ℂ* \ E` containing `∞`, and the sequences `{Ω_n}` of finitely connected domains
  with `C^{1+α}` boundary curves exhausting it, §1, P1:3342–3354) — `unboundedComponentExt`, `IsSmoothFCDomain`,
  `IsSmoothExhaustion`
* Unlabelled (§1, P1:3356 and P1:3362): Green's function is an increasing function of the domain, and along the
  sequence `γ(E_n)` increases and `Cap(E_n)` decreases — `greenFunction_mono`
* Definition ((1.3), the capacity of a compact set, §1) — `capacityCompact`
* Unlabelled (§1, P1:3362): the definition (1.3) does not depend on the choice of the sequence `{Ω_n}` —
  `capacityCompact_indep`
* Definition (`Ê = ℂ \ Ω`, §1, P1:3362) — `filledSet`
* Formula (1.4) (§1) — `eq3_1_4`
* Definition (Robin's constant `γ(E) = log(1/Cap(E))` of a compact set, §1, P1:3368–3372) — `robinConstantCompact`
* Formula (1.5) (§1) — `eq3_1_5`
* Definition (Green's function of `Ω`: `g_Ω(z, ∞) = lim g_{Ω_n}(z, ∞)`, P1:3382, and `g_Ω(z, w) = lim g_{Ω_n}(z, w)`,
  (1.7), P1:3400–3404, §1) — `greenFunctionLim`
* Formula (1.6) (§1, with `lim γ(E_n) = γ(E) < ∞` and the positivity and harmonicity of `g_Ω(·, ∞)`) — `eq3_1_6`
* Formula (1.7) (§1, with conditions (2.2), (2.4) and (2.5) of Chapter II for `g_Ω(z, w)`) — `eq3_1_7`
* Example 1.1 (§1; cited as a result at P1:3965, 4036 and in Ch. V, P1:7228) — `example3_1_1_a`, `example3_1_1_b`
* Example 1.2 (§1; cited as a result in Ch. V, P1:7037) — `example3_1_2`

Helpers (not book notions): `unboundedComponentExt`, `IsSmoothFCDomain`, `IsSmoothExhaustion` (names for the book's
`Ω` and `{Ω_n}` of P1:3342–3354, reused from §2 on and in §5), `HasExpansionAtInf` (the normalization
`ψ(z) = az + b₀ + b₁/z + …` for `|z|` large).

Not stated (inventory U−): the chapter introduction (the Wiener, Perron and Brownian-motion methods, P1:3268–3280;
the Perron solution is not defined in the book); "`Cap(E) > 0` in the case at hand" (P1:3314, immediate from
`Cap = e^{−γ}`); the announcement that all results are independent of the sequence (P1:3354; the independence claims
are stated where the book makes them); `γ(E) = lim γ(E_n)` for every compact `E` (P1:3371, continuity of `log` along
(1.3); the case `Cap(E) > 0`, where the book repeats it, is part of `eq3_1_6`); the symmetry step
`lim g_{Ω_n}(∞, w) = lim g_{Ω_n}(w, ∞)` (P1:3392–3398, a step towards (1.7)); in Example 1.1, the domains
`Ω_r = {|ψ| > r}` with `g_{Ω_r} = log |ψ/r|` and the map `z + 1/z` (P1:3412–3428, steps of the example's argument);
in Example 1.2, equality `Cap(E) = sin(|E|/4)` for an arc (P1:3446, a step of the proof).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt extInf IsJordanCurve)
open References (IsDomainExt finitePart)
open LehtoVirtanen1973 (IsConformalMap)
open InnerProductSpace (HarmonicAt)

/-- **Definition** (Robin's constant, Ch. III §1, P1:3284–3302). Let `E` be a compact plane set such that `Ω = ℂ* \ E`
is a finitely connected Jordan domain. For `a ∉ Ω̄`, `g_Ω(z, ∞) = log |z − a| + h(z, ∞)`, where `h(z, ∞)` is harmonic on
`Ω`, continuous on `Ω̄`, and `h(ζ, ∞) = −log |ζ − a|` for `ζ ∈ ∂Ω`. The quantity `γ = γ(E) = h(∞, ∞)` is called Robin's
constant for `E`.
Modelling: `Ω` is `(toExt E)ᶜ`; `h(·, ∞)` is the solution `dirichletSolution` of Theorem II.1.1 for the boundary values
`−log |ζ − a|` (the harmonic part of Green's function `g(z, ∞)` of Ch. II §2, P1:1952, written with its helper
`greenLogTerm`), read at the point `∞ ∈ Ω`; "`a ∋ Ω̄`" (P1:3284) is `a ∉ Ω̄` [OCR or misprint; inline, no crop]. The
value is taken over all finite `a ∉ Ω̄` (the registered "value over all maps" pattern), a single value by (1.1)
(`eq3_1_1`). Junk: unspecified (e.g. `0`) when `ℂ* \ E` is not a finitely connected Jordan domain; never used there. -/
def robinConstantFC (E : Set ℂ) : ℝ :=
  sSup {γ : ℝ | ∃ a : ℂ, (a : ExtPlane) ∉ closure (toExt E)ᶜ ∧
    γ = dirichletSolution (toExt E)ᶜ (fun ζ => -greenLogTerm a ζ extInf) extInf}

/-- **Formula (1.1)** (Ch. III §1, P1:3296–3306; cited at P1:3328, 3478, and restated in Ch. V, P1:7021, and App. H,
(H.16)). Let `E` be a compact plane set such that `Ω = ℂ* \ E` is a finitely connected Jordan domain. Then
`γ(E) = h(∞, ∞)` for every `a ∉ Ω̄`, and (1.1) `g_Ω(z, ∞) = log |z| + γ + o(1)` as `z → ∞`.
Modelling: the first conjunct is the definition of `γ` for each finite `a ∉ Ω̄`, which says that `h(∞, ∞)` does not
depend on `a` (the book derives it from (1.1), since `g_Ω` does not depend on `a`); `g_Ω(·, ∞)` is `greenFunction`
of Ch. II §2 and `z → ∞` is `z → ∞` in `ℂ`. -/
theorem eq3_1_1 {E : Set ℂ} (hE : IsCompact E) (hΩ : IsFCJordanDomain (toExt E)ᶜ) :
    (∀ a : ℂ, (a : ExtPlane) ∉ closure (toExt E)ᶜ →
      dirichletSolution (toExt E)ᶜ (fun ζ => -greenLogTerm a ζ extInf) extInf = robinConstantFC E) ∧
      Tendsto (fun z : ℂ => greenFunction (toExt E)ᶜ z extInf - Real.log ‖z‖) (cocompact ℂ)
        (𝓝 (robinConstantFC E)) := by
  sorry

/-- **Definition** (logarithmic capacity, Ch. III §1, P1:3308–3312). For `E` as in `robinConstantFC` (a compact
plane set whose complement `ℂ* \ E` is a finitely connected Jordan domain), the logarithmic capacity of `E` is
`Cap(E) = e^{−γ(E)}`. -/
def capacityFC (E : Set ℂ) : ℝ :=
  Real.exp (-robinConstantFC E)

/-- `ψ(z) = a z + b₀ + b₁/z + …` for `|z|` large (helper, Ch. III §1, P1:3316–3322 and P1:3406–3410; the
normalization at `∞` in (1.2) and Example 1.1): for some `R` and some function `φ` analytic at `0` (the convergent
series `b₀ + b₁ ζ + b₂ ζ² + …`), `ψ(z) = a z + φ(1/z)` for every finite `z` with `|z| > R`. -/
def HasExpansionAtInf (ψ : ExtPlane → ExtPlane) (a : ℝ) : Prop :=
  ∃ (R : ℝ) (φ : ℂ → ℂ), AnalyticAt ℂ φ 0 ∧ ∀ z : ℂ, R < ‖z‖ → ψ z = (((a : ℂ) * z + φ z⁻¹ : ℂ) : ExtPlane)

/-- **Formula (1.2)** (Ch. III §1, P1:3316–3337; cited at P1:3418, 3442 in Example 1.1). Suppose `Ω₁` and `Ω₂` are
finitely connected Jordan domains such that `∞ ∈ Ω_j`, and set `E_j = ℂ* \ Ω_j`. Assume there is a conformal map `ψ`
of `Ω₁` onto `Ω₂` such that `ψ(z) = a z + b₀ + b₁/z + …` for `|z|` large, with `a > 0`. Then
`g_{Ω₁}(z, ∞) = g_{Ω₂}(ψ(z), ∞)`, so that by (1.1) `γ(E₁) = γ(E₂) + log a` and (1.2) `Cap(E₂) = a Cap(E₁)`.
Modelling: `ψ` is a conformal map of `ℂ*`-domains (`LehtoVirtanen1973.IsConformalMap`) with `ψ(Ω₁) = Ω₂`; the
expansion is `HasExpansionAtInf ψ a` (it forces `ψ(∞) = ∞`); `E_j` is the plane set `finitePart Ω_jᶜ`; the identity
of Green's functions is stated at the finite points `z ∈ Ω₁` (at `z = ∞` both sides are the pole). The three
conclusions are one item: the book derives them in one chain; the constants were checked against the equation images
(`γ(E₁) = γ(E₂) + log a`, `Cap(E₂) = a Cap(E₁)`). -/
theorem eq3_1_2 {Ω₁ Ω₂ : Set ExtPlane} (h₁ : IsFCJordanDomain Ω₁) (h₂ : IsFCJordanDomain Ω₂) (hinf₁ : extInf ∈ Ω₁)
    (hinf₂ : extInf ∈ Ω₂) {ψ : ExtPlane → ExtPlane} (hψ : IsConformalMap ψ Ω₁) (hψΩ : ψ '' Ω₁ = Ω₂) {a : ℝ}
    (ha : 0 < a) (hexp : HasExpansionAtInf ψ a) :
    (∀ z : ℂ, (z : ExtPlane) ∈ Ω₁ → greenFunction Ω₁ z extInf = greenFunction Ω₂ (ψ z) extInf) ∧
      robinConstantFC (finitePart Ω₁ᶜ) = robinConstantFC (finitePart Ω₂ᶜ) + Real.log a ∧
      capacityFC (finitePart Ω₂ᶜ) = a * capacityFC (finitePart Ω₁ᶜ) := by
  sorry

/-- **Unlabelled** (Ch. III §1, P1:3340; cited at P1:3421 in Example 1.1, "`1 = Cap(D̄)`"). The capacity of a closed
disc is the radius of the disc (because `g_{ℂ*\D̄}(z, ∞) = log |z|`).
Modelling: the closed disc `B̄(c, r)` with `r > 0` (a disc of positive radius); its complement in `ℂ*` is a Jordan
domain, so the capacity of this stage (`capacityFC`) applies. -/
theorem capacityFC_closedBall (c : ℂ) {r : ℝ} (hr : 0 < r) : capacityFC (closedBall c r) = r := by
  sorry

/-- The component of `ℂ* \ E` containing `∞` (helper, Ch. III §1, P1:3342: "write `Ω` for the component of
`ℂ* \ E` such that `∞ ∈ Ω`"), for a plane set `E`. -/
def unboundedComponentExt (E : Set ℂ) : Set ExtPlane :=
  connectedComponentIn (toExt E)ᶜ extInf

/-- A domain of `ℂ*` bounded by finitely many pairwise disjoint Jordan curves of class `C^{1+α}`, `α > 0` (helper,
Ch. III §1, P1:3342–3354, the domains `Ω_n`; and §2, P1:3506, 3514, the complements `ℂ* \ E` of Theorem 2.2).
Modelling: the curves lie in `ℂ` and are of class `C^{1+α}` in the sense of Ch. II §4 (`IsCurveOfClass 1 α`, with
`0 < α < 1`, the range of the class), one `α` for all curves; such a domain is a finitely connected Jordan domain
(`IsFCJordanDomain`). -/
def IsSmoothFCDomain (Ω : Set ExtPlane) : Prop :=
  IsDomainExt Ω ∧ ∃ α : ℝ, 0 < α ∧ α < 1 ∧
    IsDisjointUnionOf (fun Γ => IsJordanCurve Γ ∧ ∃ Γ' : Set ℂ, Γ = toExt Γ' ∧ IsCurveOfClass 1 α Γ') (frontier Ω)

/-- The sequences `{Ω_n}` of Ch. III §1 (helper, P1:3342–3354; "the subdomains introduced in Section 1", P1:4046): a
sequence of finitely connected domains with `Ω_n ⊂ Ω̄_n ⊂ Ω_{n+1} ⊂ Ω` and `Ω = ⋃ Ω_n`, such that `∂Ω_n` consists of
`C^{1+α}` Jordan curves ("See Exercise II.10(b)" for their existence).
Modelling: for any domain `Ω` of `ℂ*` (§5 uses the same sequences for arbitrary domains); the condition `∞ ∈ Ω_n`
of §1 is required separately wherever the book requires it; closures are taken in `ℂ*`. -/
def IsSmoothExhaustion (Ω : Set ExtPlane) (Ωs : ℕ → Set ExtPlane) : Prop :=
  (∀ n, IsSmoothFCDomain (Ωs n)) ∧ (∀ n, closure (Ωs n) ⊆ Ωs (n + 1)) ∧ (∀ n, Ωs n ⊆ Ω) ∧ ⋃ n, Ωs n = Ω

/-- **Unlabelled** (Ch. III §1, P1:3356 and P1:3362; used for (1.3)–(1.7), in the proof of Corollary 4.3, P1:3882,
and of (5.2), P1:4078). Green's function is an increasing function of the domain: if `Ω ⊆ Ω'` are finitely connected
Jordan domains, then `g_Ω(z, w) ≤ g_{Ω'}(z, w)` for `z, w ∈ Ω`, `z ≠ w`. If `Ω̄ ⊆ Ω'`, then by the maximum principle
`g_{Ω'}(z, w) > g_Ω(z, w)`, and when `∞ ∈ Ω`, `γ(E') > γ(E)` and `Cap(E') < Cap(E)` for `E = ℂ \ Ω`, `E' = ℂ \ Ω'`
(for the sequences of §1: `γ(E_{n+1}) > γ(E_n)` and `Cap(E_{n+1}) < Cap(E_n)`).
Modelling: `z ≠ w` (junk: at the pole the values of `greenFunction` are junk); closures in `ℂ*`; `E` and `E'` are
the plane sets `finitePart Ωᶜ` and `finitePart Ω'ᶜ`. -/
theorem greenFunction_mono {Ω Ω' : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) (hΩ' : IsFCJordanDomain Ω')
    (hsub : Ω ⊆ Ω') :
    (∀ z ∈ Ω, ∀ w ∈ Ω, z ≠ w → greenFunction Ω z w ≤ greenFunction Ω' z w) ∧
      (closure Ω ⊆ Ω' → (∀ z ∈ Ω, ∀ w ∈ Ω, z ≠ w → greenFunction Ω z w < greenFunction Ω' z w) ∧
        (extInf ∈ Ω → robinConstantFC (finitePart Ωᶜ) < robinConstantFC (finitePart Ω'ᶜ) ∧
          capacityFC (finitePart Ω'ᶜ) < capacityFC (finitePart Ωᶜ))) := by
  sorry

/-- **Definition** ((1.3), the capacity of a compact set, Ch. III §1, P1:3342–3360). Let `E` be a compact plane set,
`Ω` the component of `ℂ* \ E` containing `∞`, and `{Ω_n}` a sequence of finitely connected domains with
`∞ ∈ Ω_n ⊂ Ω̄_n ⊂ Ω_{n+1} ⊂ Ω`, `Ω = ⋃ Ω_n`, and `∂Ω_n` consisting of `C^{1+α}` Jordan curves; with `E_n = ℂ \ Ω_n`,
(1.3) `Cap(E) = lim_n Cap(E_n)`.
Modelling (leader ruling B1): values in `[0, ∞]`; `Cap(E_n)` is `capacityFC` of the plane set `E_n` (the limit exists,
the sequence being decreasing). The value is taken over all such sequences, as the supremum of the set of limits, a
single value by `capacityCompact_indep`. Junk: `0` when there is no such sequence (for `E = ∅`: an increasing open
cover of the compact space `ℂ*` has a member `Ω_N = ℂ*`, whose boundary is empty, which the definition of the
sequences excludes); unspecified (e.g. `0`; for `D̄ \ {0}` it is `1`) for sets that are not compact; never used
there. -/
def capacityCompact (E : Set ℂ) : ℝ≥0∞ :=
  sSup {c : ℝ≥0∞ | ∃ Ωs : ℕ → Set ExtPlane, IsSmoothExhaustion (unboundedComponentExt E) Ωs ∧
    (∀ n, extInf ∈ Ωs n) ∧ Tendsto (fun n => ENNReal.ofReal (capacityFC (finitePart (Ωs n)ᶜ))) atTop (𝓝 c)}

/-- **Unlabelled** (Ch. III §1, P1:3362; the definition (1.3) rests on it). Because `g_Ω(z, w)` is an increasing
function of `Ω`, an interlacing of the domains `Ω_n` shows that the definition (1.3) does not depend on the choice of
the sequence `{Ω_n}`: for every such sequence, `Cap(E_n) → Cap(E)`. -/
theorem capacityCompact_indep {E : Set ℂ} (hE : IsCompact E) {Ωs : ℕ → Set ExtPlane}
    (hΩs : IsSmoothExhaustion (unboundedComponentExt E) Ωs) (hinf : ∀ n, extInf ∈ Ωs n) :
    Tendsto (fun n => ENNReal.ofReal (capacityFC (finitePart (Ωs n)ᶜ))) atTop (𝓝 (capacityCompact E)) := by
  sorry

/-- **Definition** (`Ê = ℂ \ Ω`, Ch. III §1, P1:3362): the complement in `ℂ` of the component `Ω` of `ℂ* \ E`
containing `∞` (for compact `E`: `E` together with the bounded components of `ℂ \ E`). -/
def filledSet (E : Set ℂ) : Set ℂ :=
  (finitePart (unboundedComponentExt E))ᶜ

/-- **Formula (1.4)** (Ch. III §1, P1:3362–3366; cited at P1:3868). If `Ê = ℂ \ Ω`, then by definition
(1.4) `Cap(∂E) = Cap(E) = Cap(Ê) = Cap(∂Ê)`.
Modelling: `E` compact; boundaries in `ℂ`; the capacity of compact sets (1.3). -/
theorem eq3_1_4 {E : Set ℂ} (hE : IsCompact E) :
    capacityCompact (frontier E) = capacityCompact E ∧ capacityCompact E = capacityCompact (filledSet E) ∧
      capacityCompact (filledSet E) = capacityCompact (frontier (filledSet E)) := by
  sorry

/-- **Definition** (Robin's constant of a compact set, Ch. III §1, P1:3368–3372). By definition, the quantity
`γ(E) ≡ log(1/Cap(E)) = lim_n γ(E_n)` is Robin's constant for the arbitrary compact set `E`.
Modelling (leader ruling B1): `γ(E) = −log Cap(E)` with values in `[−∞, +∞]` (`ENNReal.log`), so `γ(E) = +∞` exactly
when `Cap(E) = 0`. The equality with `lim γ(E_n)` is not part of the definition (for `Cap(E) > 0` it is in
`eq3_1_6`). -/
def robinConstantCompact (E : Set ℂ) : EReal :=
  -ENNReal.log (capacityCompact E)

/-- **Formula (1.5)** (Ch. III §1, P1:3374–3377; used at P1:4459, "the function `E ↦ γ(E)` is decreasing"). If
`E ⊂ F` (compact sets), then by (1.3) (1.5) `Cap(E) ≤ Cap(F)` and `γ(E) ≥ γ(F)`. -/
theorem eq3_1_5 {E F : Set ℂ} (hE : IsCompact E) (hF : IsCompact F) (hEF : E ⊆ F) :
    capacityCompact E ≤ capacityCompact F ∧ robinConstantCompact F ≤ robinConstantCompact E := by
  sorry

/-- **Definition** (Green's function `g_Ω(z, w)` of the component `Ω`, Ch. III §1: `g_Ω(z, ∞) = lim_n g_{Ω_n}(z, ∞)`,
P1:3380–3386, and (1.7) `g_Ω(z, w) = lim_n g_{Ω_n}(z, w)` for `z, w ∈ Ω`, `z ≠ w`, P1:3392–3404: "the function
`g_Ω(z, w)` is Green's function for `Ω` with pole at `w`"; used for arbitrary domains from §5 on).
Modelling (leader ruling B4): for any domain `Ω` of `ℂ*`, the limit of Green's functions `greenFunction` (Ch. II §2) of
the domains of any sequence `IsSmoothExhaustion Ω Ωs`, real-valued, taken over all such sequences (a single value by
(1.7), `eq3_1_7`, for the sequences with `∞ ∈ Ω_n`; a sequence exhausting `Ω ∋ ∞` contains `∞` from some index on).
Junk: `0` when the limit is `+∞` (for the component `Ω` of §1, exactly when `Cap(E) = 0`); unspecified (e.g. `0`) at
`z = w`, where it is the limit of the pole junk of Ch. II's `greenFunction`, and for `z` or `w` outside `Ω`; every
statement assumes `Cap > 0` (in Example 1.1 it follows from the hypotheses) and `z ≠ w`. -/
def greenFunctionLim (Ω : Set ExtPlane) (z w : ExtPlane) : ℝ :=
  sSup {g : ℝ | ∃ Ωs : ℕ → Set ExtPlane, IsSmoothExhaustion Ω Ωs ∧
    Tendsto (fun n => greenFunction (Ωs n) z w) atTop (𝓝 g)}

/-- **Formula (1.6)** (Ch. III §1, P1:3380–3390; restated in Ch. V, P1:7021, and App. H, (H.16)). If `Cap(E) > 0`,
then `lim_n γ(E_n) = γ(E) < ∞`, and by Harnack's principle `g_Ω(z, ∞) = lim_n g_{Ω_n}(z, ∞)` defines a positive
harmonic function on `Ω` having the expansion (1.6) `g_Ω(z, ∞) = log |z| + γ(E) + o(1)` at `∞`.
Modelling: `E` compact, `Ω` the component of `ℂ* \ E` containing `∞`, `{Ω_n}` any sequence of §1 (with `∞ ∈ Ω_n`);
the limits of `γ(E_n)` and of `g_Ω(z, ∞) − log |z|` are taken in `[−∞, +∞]` (with `γ(E) < ∞` they are real limits);
`g_Ω(·, ∞)` is harmonic and positive on `Ω \ {∞}` (it has its pole at `∞`). "Harnack's principle" is Exercise I.5, an
exercise. -/
theorem eq3_1_6 {E : Set ℂ} (hE : IsCompact E) (hcap : 0 < capacityCompact E) {Ω : Set ExtPlane}
    (hΩ : Ω = unboundedComponentExt E) :
    robinConstantCompact E < ⊤ ∧
      (∀ Ωs : ℕ → Set ExtPlane, IsSmoothExhaustion Ω Ωs → (∀ n, extInf ∈ Ωs n) →
        Tendsto (fun n => (robinConstantFC (finitePart (Ωs n)ᶜ) : EReal)) atTop (𝓝 (robinConstantCompact E)) ∧
          ∀ z ∈ Ω, z ≠ extInf →
            Tendsto (fun n => greenFunction (Ωs n) z extInf) atTop (𝓝 (greenFunctionLim Ω z extInf))) ∧
      HarmonicOnExt (fun z => greenFunctionLim Ω z extInf) (Ω \ {extInf}) ∧
      (∀ z ∈ Ω, z ≠ extInf → 0 < greenFunctionLim Ω z extInf) ∧
      Tendsto (fun z : ℂ => ((greenFunctionLim Ω z extInf - Real.log ‖z‖ : ℝ) : EReal)) (cocompact ℂ)
        (𝓝 (robinConstantCompact E)) := by
  sorry

/-- **Formula (1.7)** (Ch. III §1, P1:3392–3404; cited at P1:3418, 3580, 3908, 4078, and "Green's function" of
arbitrary domains in every later chapter). If `Cap(E) > 0`, the limit (1.7) `g_Ω(z, w) = lim_n g_{Ω_n}(z, w)` exists
for all `z, w ∈ Ω` with `z ≠ w`, and `g_Ω(z, w)` satisfies conditions (2.2), (2.4) and (2.5) of Chapter II: it is
positive, harmonic in `z ∈ Ω \ {w}`, and `g_Ω(z, w) − log (1/|z − w|)` is harmonic at `w`.
Modelling: `E` compact, `Ω` the component of `ℂ* \ E` containing `∞`; the limit exists for every sequence of §1 and
is `greenFunctionLim Ω z w` (so it does not depend on the sequence); (2.5) is written in the chart of `ℂ*` at `w`, as
in `eq2_2_5` (for `w = ∞`: `g_Ω(z, ∞) − log |z|` is harmonic at `∞`). -/
theorem eq3_1_7 {E : Set ℂ} (hE : IsCompact E) (hcap : 0 < capacityCompact E) {Ω : Set ExtPlane}
    (hΩ : Ω = unboundedComponentExt E) :
    (∀ Ωs : ℕ → Set ExtPlane, IsSmoothExhaustion Ω Ωs → (∀ n, extInf ∈ Ωs n) → ∀ z ∈ Ω, ∀ w ∈ Ω, z ≠ w →
      Tendsto (fun n => greenFunction (Ωs n) z w) atTop (𝓝 (greenFunctionLim Ω z w))) ∧
      (∀ z ∈ Ω, ∀ w ∈ Ω, z ≠ w → 0 < greenFunctionLim Ω z w) ∧
      (∀ w ∈ Ω, HarmonicOnExt (fun z => greenFunctionLim Ω z w) (Ω \ {w})) ∧
      ∀ w ∈ Ω, ∃ H : ℂ → ℝ, HarmonicAt H 0 ∧
        ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), H ζ = greenFunctionLim Ω (LehtoVirtanen1973.extChartInv w ζ) w + Real.log ‖ζ‖ := by
  sorry

/-- **Example 1.1** (Ch. III §1, P1:3406–3422), first part (cited at P1:4036, proof of Corollary 4.8, and in Ch. V,
P1:7228: "It follows from Example III.1.1 that `2πM(G) = γ_{∂G}`"). Suppose `E` is compact and connected. Let `Ω` be
the component of `ℂ* \ E` such that `∞ ∈ Ω` and let `ψ : Ω → ℂ* \ D̄` be the conformal mapping such that for `|z|`
large `ψ(z) = a z + b₀ + b₁/z + …`, with `a > 0`. Then `g_Ω(z, ∞) = log |ψ(z)|` and `1 = Cap(D̄) = a Cap(E)`.
Modelling: `ψ` is a conformal map of `ℂ*`-domains of `Ω` onto `ℂ* \ D̄` with the expansion `HasExpansionAtInf ψ a`;
such a map exists exactly when `E` has more than one point, which the book's "the conformal mapping" presupposes, so
no hypothesis is added; the identity for `g_Ω` is at the finite points of `Ω`, where `ψ(z)` is a finite point `x`;
`Cap(E)` is the capacity (1.3) of compact sets, and `a Cap(E) = 1` is written in `[0, ∞]`. -/
theorem example3_1_1_a {E : Set ℂ} (hE : IsCompact E) (hEc : IsConnected E) {Ω : Set ExtPlane}
    (hΩ : Ω = unboundedComponentExt E) {ψ : ExtPlane → ExtPlane} (hψ : IsConformalMap ψ Ω)
    (hψΩ : ψ '' Ω = (toExt (closedBall 0 1))ᶜ) {a : ℝ} (ha : 0 < a) (hexp : HasExpansionAtInf ψ a) :
    (∀ z : ℂ, (z : ExtPlane) ∈ Ω → ∀ x : ℂ, ψ z = x → greenFunctionLim Ω z extInf = Real.log ‖x‖) ∧
      ENNReal.ofReal a * capacityCompact E = 1 := by
  sorry

/-- **Example 1.1** (Ch. III §1, P1:3424–3442), second part (cited at P1:3965 in the proof of Theorem 4.5: "by
Example 1.1, `Cap(F) = |F|/4`"). The normalized conformal map of `ℂ* \ D̄` onto the complement of `[−2, 2]` is
`z + 1/z`, and so `Cap([−2, 2]) = 1`. Consequently `Cap([α, β]) = (β − α)/4` for every interval `[α, β] ⊂ ℝ`, by
(1.2).
Modelling: the interval `[α, β]` is the plane set `{t : α ≤ t ≤ β}` of real points, `α ≤ β` (the degenerate interval
`α = β`, a point, has capacity `0`, as the formula says); capacities of compact sets (1.3), in `[0, ∞]`; the constant
`(β − α)/4` was checked against the equation image. -/
theorem example3_1_1_b :
    capacityCompact (((↑) : ℝ → ℂ) '' Icc (-2) 2) = 1 ∧
      ∀ α β : ℝ, α ≤ β → capacityCompact (((↑) : ℝ → ℂ) '' Icc α β) = ENNReal.ofReal ((β - α) / 4) := by
  sorry

/-- **Example 1.2** (Ch. III §1, P1:3444–3484; cited in Ch. V, P1:7037: "because by Example III.1.2"). If
`E ⊂ ∂𝔻`, then `Cap(E) ≥ sin(|E|/4)`.
Modelling: the OCR of the statement is garbled ("I^r E ⊂ ∂𝔻, t h e n", P1:3444) [OCR]; the formula
`sin(|E|/4)` is confirmed by the last display of the proof (equation image). `E` is compact (capacity is defined for
compact sets at this point of the book; the proof approximates `E` from outside through (1.3)); `|E|` is the
arc-length measure `arcMeasure` of Chapter I (total mass `2π`, so `|E|/4 ∈ [0, π/2]`). -/
theorem example3_1_2 {E : Set ℂ} (hE : IsCompact E) (hE1 : E ⊆ sphere 0 1) :
    ENNReal.ofReal (Real.sin ((arcMeasure E).toReal / 4)) ≤ capacityCompact E := by
  sorry

end GarnettMarshall2005
