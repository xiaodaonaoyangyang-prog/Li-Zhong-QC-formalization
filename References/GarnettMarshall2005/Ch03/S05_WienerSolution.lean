import References.GarnettMarshall2005.Ch03.S04_EquilibriumDistribution

/-!
# Garnett–Marshall, Chapter III §5: Wiener's solution to the Dirichlet problem

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. III §5 (pp. 89–93;
`full.md` P1:4044–4204).

Conventions as in §1–§4. From this section on `Ω` is a domain of `ℂ*` (`References.IsDomainExt`), `∂Ω` and `Ω̄` are
taken in `ℂ*`, and `f ∈ C(∂Ω)` is a real function on `ℂ*` that is continuous on `∂Ω`. The book writes `Cap(ℂ \ Ω)`,
`Cap(ℂ* \ Ω)` and `Cap(∂Ω)` interchangeably; the set is the plane set `finitePart Ωᶜ` (resp. `finitePart (frontier Ω)`),
since capacity is defined for plane sets (a single point, such as `∞`, is polar). Capacity and Robin's constant are
those of (4.8) (`capacity`, `robinConstant`: the most general stage, leader ruling B1). The domains `{Ω_n}` "introduced
in Section 1" are the sequences `IsSmoothExhaustion Ω Ωs` (finitely connected domains with `C^{1+α}` boundary curves,
`Ω̄_n ⊂ Ω_{n+1}`, `⋃ Ω_n = Ω`), and their harmonic measure is that of Chapter II (`harmonicMeasureFC`). The harmonic
measure of an arbitrary domain is Wiener's (5.3) (`harmonicMeasureWiener`, leader ruling B5), a measure on `ℂ*`; it is
the book's `ω(z, A, Ω)` from here on (leader ruling D1), compared in `[0, ∞]` where the book compares measures. The
book's `ω(z, E, D \ E)` for a closed set `E` in a domain `D` (§9 and later chapters) is
`harmonicMeasureOpen (D \ E) z E`. Limits `Ω ∋ z → ζ` are taken along `𝓝[Ω] ζ` in `ℂ*`.

* Definition (the Wiener solution `u_f` of the Dirichlet problem with boundary values `f`, §5, P1:4046–4062) —
  `wienerSolution`
* Theorem 5.1 (Wiener, §5) — `thm3_5_1`
* Unlabelled (§5, P1:4075, in the proof of Theorem 5.1; cited as a result at P1:4112): formula (5.2),
  `Cap(∂Ω) > 0 ⟺ Cap(T(∂Ω)) > 0` for a Möbius transformation `T` — `eq3_5_2`
* Definition (the harmonic measure `ω(z, ·, Ω)` for `z` relative to an arbitrary domain `Ω`, the weak-star limit
  (5.3), §5, P1:4086–4098) — `harmonicMeasureWiener`
* Formula (5.3) (§5; the limit exists and does not depend on `{Ω_n}`) — `eq3_5_3`
* Unlabelled (§5, P1:4092–4098): `u_f(z) = ∫_{∂Ω} f dω(z, ·, Ω)` for `f ∈ C(∂Ω)` — `wienerSolution_eq_integral`
* Unlabelled (§5, P1:4098–4102): `ω(z, A, Ω)` is a harmonic function of `z`, and `0 ≤ ω ≤ 1` (a probability
  measure on `∂Ω`, as in Chapter I) — `harmonicMeasureWiener_harmonic`, `isProbabilityMeasure_harmonicMeasureWiener`
* Unlabelled (§5, P1:4104–4110): Harnack's inequality for `ω(·, E, Ω)`; the measures `ω(z, ·, Ω)` are mutually
  absolutely continuous — `harmonicMeasureWiener_harnack`
* Unlabelled (§5, P1:4112): `ω(∞, ·, Ω) = μ_{∂Ω}`, and `ω(z, A, Ω) = μ_{T(∂Ω)}(T(A))` for a Möbius `T` with
  `T(z) = ∞` — `harmonicMeasureWiener_infty`, `harmonicMeasureWiener_mobius`
* Formula (5.4) (§5) — `eq3_5_4`
* Unlabelled (§5, P1:4122): a finite set has capacity zero, and a finite `F ⊂ ∂Ω` has harmonic measure zero —
  `capacity_finite_eq_zero`, `harmonicMeasureWiener_finite_eq_zero`
* Proposition 5.2 (§5; (5.5)) — `prop3_5_2`
* Proposition 5.3 (§5) — `prop3_5_3_a`, `prop3_5_3_b`
* Unlabelled (§5, P1:4203): Proposition 5.3 remains valid with `B(0, R)` replaced by a bounded Jordan region `Ω'`
  with `E ∩ ∂Ω' = ∅` — `prop3_5_3_jordan`

Helper (not a book notion): `harmonicMeasureOpen` (Wiener's harmonic measure of the component of an open set of `ℂ*`
that contains the point: the book's `ω(z, E, D \ E)`).

Not stated (inventory U−): (5.1) `lim u_n(∞) = ∫ f dμ_E` (P1:4067, a step of the proof of Theorem 5.1; its
consequence `ω(∞, ·, Ω) = μ_{∂Ω}` is stated); "By Exercise 4 of Chapter II, this definition of harmonic measure agrees
with the definition in Chapter II for finitely connected Jordan domains" (P1:4098; an exercise, and no
identification theorem is stated, leader ruling D1); "if `Cap(ℂ* \ Ω) = 0`, each bounded or positive harmonic function
on `Ω` is constant, so harmonic measure cannot be defined" (P1:4120, a forward reference to §8, P1:4718); for `0 ∉ Ω̄`,
`h(z, ∞) = g(z, ∞) − log |z|` is the solution of the Dirichlet problem with boundary values `−log |z|` (P1:4167–4173,
the motivation for Proposition 5.3, not cited). The displays in the proofs of Propositions 5.2 and 5.3 are steps.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt extInf IsMobius)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-- **Definition** (the Wiener solution, Ch. III §5, P1:4046–4062). Let `Ω` be a domain in `ℂ*` such that
`Cap(ℂ \ Ω) > 0`, let `f ∈ C(∂Ω)`, and let `{Ω_n}` be the subdomains introduced in Section 1. Extend `f` to a
continuous function on `ℂ*`, still called `f`, and set `u_n(z) = ∫_{∂Ω_n} f(ζ) dω(z, ζ, Ω_n)`, `z ∈ Ω_n`. The limit
`u(z) = u_f(z) = lim u_n(z)` of Theorem 5.1 is called the Wiener solution to the Dirichlet problem with boundary values
`f(ζ)`.
Modelling (leader ruling B5): `{Ω_n}` is any sequence `IsSmoothExhaustion Ω Ωs` and the extension any continuous
`F : ℂ* → ℝ` equal to `f` on `∂Ω`; `ω(z, ·, Ω_n)` is the harmonic measure `harmonicMeasureFC` of the finitely
connected Jordan domain `Ω_n` (Ch. II §1); `u_n(z)` is read only for the `n` with `z ∈ Ω_n`, which are all large `n`
for `z ∈ Ω`, so the limit sees only meaningful values. The value is taken over all sequences and all extensions, as the
supremum of the set of limits (the registered "value over all maps" pattern): by Theorem 5.1 (`thm3_5_1`) the set is a
single point for `z ∈ Ω`. Junk: outside the book's discourse (`Cap(ℂ \ Ω) = 0`, or `z ∉ Ω`) the value is whatever
this supremum gives (`0` when no limit exists); never used there. -/
def wienerSolution (Ω : Set ExtPlane) (f : ExtPlane → ℝ) (z : ExtPlane) : ℝ :=
  sSup {u : ℝ | ∃ (Ωs : ℕ → Set ExtPlane) (F : ExtPlane → ℝ), IsSmoothExhaustion Ω Ωs ∧ Continuous F ∧
    EqOn F f (frontier Ω) ∧
    Tendsto (fun n => ∫ ζ in frontier (Ωs n), F ζ ∂(harmonicMeasureFC (Ωs n) z)) atTop (𝓝 u)}

/-- **Theorem 5.1** (Wiener; Ch. III §5; cited at P1:4086, 4167, and by name in the preface, P1:195–197). If
`Cap(ℂ \ Ω) > 0`, the sequence `{u_n(z)}` converges uniformly on all compact subsets of `Ω` to a harmonic function
`u(z)`, and `u(z)` does not depend on the choice of the sequence `{Ω_n}` nor on the choice of the extension of
`f ∈ C(∂Ω)`.
Modelling: `Ω` a domain of `ℂ*`, `Cap(ℂ \ Ω)` the capacity (4.8) of the plane set `finitePart Ωᶜ`, `f` continuous on
`∂Ω`; the limit along every sequence `IsSmoothExhaustion Ω Ωs` and every continuous extension `F` is the one function
`wienerSolution Ω f`, which is the independence claim; harmonic on the `ℂ*`-domain `Ω` is `HarmonicOnExt`. A compact
`K ⊆ Ω` lies in `Ω_n` for all large `n`, so uniform convergence on `K` sees only meaningful values of `u_n`. -/
theorem thm3_5_1 {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) (hcap : 0 < capacity (finitePart Ωᶜ))
    {f : ExtPlane → ℝ} (hf : ContinuousOn f (frontier Ω)) :
    HarmonicOnExt (wienerSolution Ω f) Ω ∧
      ∀ (Ωs : ℕ → Set ExtPlane) (F : ExtPlane → ℝ), IsSmoothExhaustion Ω Ωs → Continuous F →
        EqOn F f (frontier Ω) → ∀ K ⊆ Ω, IsCompact K →
          TendstoUniformlyOn (fun n z => ∫ ζ in frontier (Ωs n), F ζ ∂(harmonicMeasureFC (Ωs n) z))
            (wienerSolution Ω f) atTop K := by
  sorry

/-- **Unlabelled** (Ch. III §5, (5.2), P1:4072–4084, in the proof of Theorem 5.1; cited as a result at P1:4112, "By
(5.2) and Corollary 4.3"). For `z ∈ Ω` and `z ≠ ∞`, let `T` be a Möbius transformation such that `T z = ∞`; then
(5.2) `Cap(∂Ω) > 0 ⟺ Cap(T(∂Ω)) > 0`.
Modelling: the setting of the book's proof is kept (`Ω` a domain of `ℂ*`, `z`, `T` as there); `T` is a fractional
linear transformation of `ℂ*` (`LiZhongQC.IsMobius`); `Cap` of a subset of `ℂ*` is the capacity (4.8) of its finite
part. The equivalence was checked against the equation image. -/
theorem eq3_5_2 {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) {z : ExtPlane} (hz : z ∈ Ω) (hzinf : z ≠ extInf)
    {T : ExtPlane → ExtPlane} (hT : IsMobius T) (hTz : T z = extInf) :
    0 < capacity (finitePart (frontier Ω)) ↔ 0 < capacity (finitePart (T '' frontier Ω)) := by
  sorry

/-- **Definition** (harmonic measure of an arbitrary domain, Ch. III §5, P1:4086–4098). Theorem 5.1 enables us to
define harmonic measure for any domain `Ω` with `Cap(ℂ* \ Ω) > 0`, because it says the weak-star limit (5.3)
`ω(z, ·, Ω) = lim_n ω(z, ·, Ω_n)` exists and is independent of the choice of `{Ω_n}`. By definition, the limit measure
`ω(z, ·, Ω)` is the harmonic measure for `z` relative to `Ω`.
Modelling (leader rulings D1, B5): a measure on `ℂ*`; `ω(z, ·, Ω_n)` is `harmonicMeasureFC` of the finitely connected
Jordan domain `Ω_n` (Ch. II §1), read only for the `n` with `z ∈ Ω_n`; weak-star convergence is `TendstoWeakStar`
(integrals of bounded continuous functions on the compact space `ℂ*`). The value is taken over all sequences
`IsSmoothExhaustion Ω Ωs`, as the supremum of the set of weak-star limits (the registered "value over all maps"
pattern); by (5.3) (`eq3_5_3`) that set is a single measure for `z ∈ Ω` (a weak-star limit of finite Borel measures on
the compact metrizable space `ℂ*` is unique). For finitely connected Jordan domains the book identifies it with the
harmonic measure of Chapter II through Exercise II.4, an exercise; no identification is stated. Junk: outside the
book's discourse (`Cap(ℂ* \ Ω) = 0`, or `z ∉ Ω`) the value is whatever this supremum gives (the zero measure when no
limit exists); never used there. -/
def harmonicMeasureWiener (Ω : Set ExtPlane) (z : ExtPlane) : Measure ExtPlane :=
  sSup {μ : Measure ExtPlane | ∃ Ωs : ℕ → Set ExtPlane, IsSmoothExhaustion Ω Ωs ∧
    TendstoWeakStar (fun n => harmonicMeasureFC (Ωs n) z) atTop μ}

/-- Harmonic measure relative to an open set (helper, leader ruling B5: the book's `ω(z, E, D \ E)` for a closed set
`E` and a domain `D`, where `D \ E` need not be connected; §9 and passim in Ch. VI–IX). Wiener's harmonic measure
(`harmonicMeasureWiener`) of the component of the open set `W ⊆ ℂ*` that contains `z`. It is carried by the boundary
of that component, so its value on `E` is the harmonic measure of the part of `E` on that boundary. Junk: for `z ∉ W`
the component is empty, no sequence `IsSmoothExhaustion ∅ Ωs` exists, and the value is the zero measure; if the
component has a polar complement the value is the junk of `harmonicMeasureWiener`. Every statement takes `z ∈ W`
with `W ⊆ 𝔻` or `W ⊆ ℍ`, whose complement has positive capacity, so neither case is reached. -/
def harmonicMeasureOpen (W : Set ExtPlane) (z : ExtPlane) : Measure ExtPlane :=
  harmonicMeasureWiener (connectedComponentIn W z) z

/-- **Formula (5.3)** (Ch. III §5, P1:4086–4092; cited at P1:4736 and, as weak-star convergence, in the proof of
Theorem 8.1, P1:4658–4664). If `Cap(ℂ* \ Ω) > 0`, the weak-star limit (5.3) `ω(z, ·, Ω) = lim_n ω(z, ·, Ω_n)` exists
and is independent of the choice of `{Ω_n}`.
Modelling: `Ω` a domain of `ℂ*`, `z ∈ Ω`; along every sequence `IsSmoothExhaustion Ω Ωs` the measures
`harmonicMeasureFC (Ωs n) z` converge weak-star to the one measure `harmonicMeasureWiener Ω z`, which is the
independence claim. -/
theorem eq3_5_3 {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) (hcap : 0 < capacity (finitePart Ωᶜ)) :
    ∀ z ∈ Ω, ∀ Ωs : ℕ → Set ExtPlane, IsSmoothExhaustion Ω Ωs →
      TendstoWeakStar (fun n => harmonicMeasureFC (Ωs n) z) atTop (harmonicMeasureWiener Ω z) := by
  sorry

/-- **Unlabelled** (Ch. III §5, P1:4092–4098; cited in the proof of Proposition 5.3, P1:4189–4201, and for (8.4) in
the proof of Theorem 8.1, P1:4676). For any `f ∈ C(∂Ω)`, `u_f(z) = ∫_{∂Ω} f(ζ) dω(z, ζ, Ω)`, where `u_f(z)` is the
Wiener solution to the Dirichlet problem for `f(ζ)`.
Modelling: `Ω` a domain of `ℂ*` with `Cap(ℂ* \ Ω) > 0` (the setting of (5.3)), `z ∈ Ω`, `f` continuous on `∂Ω`. -/
theorem wienerSolution_eq_integral {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) (hcap : 0 < capacity (finitePart Ωᶜ))
    {f : ExtPlane → ℝ} (hf : ContinuousOn f (frontier Ω)) :
    ∀ z ∈ Ω, wienerSolution Ω f z = ∫ ζ in frontier Ω, f ζ ∂(harmonicMeasureWiener Ω z) := by
  sorry

/-- **Unlabelled** (Ch. III §5, P1:4098, first half; used throughout, e.g. in Corollary 8.4, P1:4716). As in
Chapter I, `ω(z, A, Ω)` is a harmonic function of `z ∈ Ω`.
Modelling: `Ω` a domain of `ℂ*` with `Cap(ℂ* \ Ω) > 0`; `A` a Borel set of `ℂ*`; the number `ω(z, A, Ω)` is the real
value of the finite measure; harmonic in the charts of `ℂ*` (`HarmonicOnExt`). -/
theorem harmonicMeasureWiener_harmonic {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω)
    (hcap : 0 < capacity (finitePart Ωᶜ)) {A : Set ExtPlane} (hA : MeasurableSet A) :
    HarmonicOnExt (fun z => (harmonicMeasureWiener Ω z A).toReal) Ω := by
  sorry

/-- **Unlabelled** (Ch. III §5, P1:4098–4102, second half). `0 ≤ ω(z, A, Ω) ≤ 1`.
Modelling: "as in Chapter I" (P1:4098) refers to Chapter I's claim that `ω(z, ·, ℍ)` is a probability measure
(P1:382); the bound `0 ≤ ω ≤ 1` is read the same way: for `z ∈ Ω`, `ω(z, ·, Ω)` is a probability measure, carried by
`∂Ω` (the integrals of (5.3) and of `wienerSolution_eq_integral` are over `∂Ω`). This is stronger than the printed
bound and holds under `Cap(ℂ* \ Ω) > 0` alone: the `ω(z, ·, Ω_n)` are probability measures carried by `∂Ω_n`, the
constant `1` is a test function of the weak-star limit on the compact `ℂ*`, and the limit gives no mass to the open
sets `Ω_m` and `ℂ* \ Ω̄`, which the `∂Ω_n`, `n > m`, avoid; the book uses the total mass at P1:4698
(`ω(∞, A ∩ ∂Ω, Ω) = μ_A(A) = 1`). -/
theorem isProbabilityMeasure_harmonicMeasureWiener {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω)
    (hcap : 0 < capacity (finitePart Ωᶜ)) :
    ∀ z ∈ Ω, IsProbabilityMeasure (harmonicMeasureWiener Ω z) ∧ harmonicMeasureWiener Ω z (frontier Ω)ᶜ = 0 := by
  sorry

/-- **Unlabelled** (Ch. III §5, P1:4104–4110; used in the proof of Theorem 8.1, P1:4650, and for (8.6), P1:4698). By
Harnack's inequality, `ω(z₁, E, Ω) ≤ C_{z₁,z₂} ω(z₂, E, Ω)` for every pair `z₁, z₂` of points in `Ω`, where the
constant `C_{z₁,z₂} > 0` depends only on `z₁`, `z₂` and `Ω`. Thus the measures `ω(z, ·, Ω)`, `z ∈ Ω`, are mutually
absolutely continuous.
Modelling: `Ω` a domain of `ℂ*` with `Cap(ℂ* \ Ω) > 0`; `∀ z₁ z₂, ∃ C, ∀ E`, as in the book; `E` any subset of `ℂ*`
(the measure's outer value), compared in `[0, ∞]`; mutual absolute continuity is `≪` for every ordered pair.
"Harnack's inequality" here is Exercise I.5, an exercise. -/
theorem harmonicMeasureWiener_harnack {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω)
    (hcap : 0 < capacity (finitePart Ωᶜ)) :
    ∀ z₁ ∈ Ω, ∀ z₂ ∈ Ω, ∃ C : ℝ≥0, 0 < C ∧
      (∀ E : Set ExtPlane, harmonicMeasureWiener Ω z₁ E ≤ C * harmonicMeasureWiener Ω z₂ E) ∧
      harmonicMeasureWiener Ω z₁ ≪ harmonicMeasureWiener Ω z₂ := by
  sorry

/-- **Unlabelled** (Ch. III §5, P1:4112, first sentence; cited at P1:4698 in the proof of Theorem 8.2,
"`ω(∞, A ∩ ∂Ω, Ω) = μ_A(A) = 1`"). If `z = ∞`, then (5.1) shows that `ω(∞, ·, Ω) = μ_{∂Ω}`.
Modelling: `Ω` a domain of `ℂ*` with `∞ ∈ Ω` and `Cap(ℂ* \ Ω) > 0`; then `∂Ω` is the compact plane set
`finitePart (frontier Ω)`, and `μ_{∂Ω}` is its equilibrium distribution (§4, a measure on `ℂ`), carried to `ℂ*` by the
inclusion `ℂ → ℂ*`. -/
theorem harmonicMeasureWiener_infty {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) (hcap : 0 < capacity (finitePart Ωᶜ))
    (hinf : extInf ∈ Ω) :
    harmonicMeasureWiener Ω extInf =
      Measure.map ((↑) : ℂ → ExtPlane) (equilibriumMeasure (finitePart (frontier Ω))) := by
  sorry

/-- **Unlabelled** (Ch. III §5, P1:4112, second sentence; the step to (5.4)). If `z ∈ Ω` and if `T` is a Möbius
transformation with `T(z) = ∞`, then for every Borel set `A`, `ω(z, A, Ω) = μ_{T(∂Ω)}(T(A))`.
Modelling: `Ω` a domain of `ℂ*` with `Cap(ℂ* \ Ω) > 0`; `T` a fractional linear transformation of `ℂ*`
(`LiZhongQC.IsMobius`); `T(∂Ω) = ∂T(Ω)` is a compact plane set, and `μ_{T(∂Ω)}` its equilibrium distribution (§4),
carried to `ℂ*` by the inclusion and evaluated at the Borel set `T(A)` of `ℂ*`. -/
theorem harmonicMeasureWiener_mobius {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) (hcap : 0 < capacity (finitePart Ωᶜ))
    {z : ExtPlane} (hz : z ∈ Ω) {T : ExtPlane → ExtPlane} (hT : IsMobius T) (hTz : T z = extInf)
    {A : Set ExtPlane} (hA : MeasurableSet A) :
    harmonicMeasureWiener Ω z A =
      Measure.map ((↑) : ℂ → ExtPlane) (equilibriumMeasure (finitePart (T '' frontier Ω))) (T '' A) := by
  sorry

/-- **Formula (5.4)** (Ch. III §5, P1:4112–4118; cited at P1:4122, 4429, 4698). By (5.2) and Corollary 4.3,
(5.4) `Cap(A) = 0 ⟹ ω(z, A, Ω) = 0` for every `Ω` with `Cap(ℂ \ Ω) > 0` and every `z ∈ Ω`.
Modelling: `Ω` a domain of `ℂ*`; `A` a Borel set of `ℂ*` (the Borel sets of P1:4112), and `Cap(A)` the capacity (4.8)
of its finite part. The formula was checked against the equation image. -/
theorem eq3_5_4 {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) (hcap : 0 < capacity (finitePart Ωᶜ)) {A : Set ExtPlane}
    (hA : MeasurableSet A) (hA0 : capacity (finitePart A) = 0) :
    ∀ z ∈ Ω, harmonicMeasureWiener Ω z A = 0 := by
  sorry

/-- **Unlabelled** (Ch. III §5, P1:4122, first part; cited at P1:4642, "Because a finite set has zero harmonic
measure"). `Cap(F) = 0` for every finite set `F`, by (4.1).
Modelling: `F` a finite plane set; `Cap` is `capacity` (4.8). -/
theorem capacity_finite_eq_zero {F : Set ℂ} (hF : F.Finite) : capacity F = 0 := by
  sorry

/-- **Unlabelled** (Ch. III §5, P1:4122, second part; cited at P1:4642). Every finite `F ⊂ ∂Ω` has harmonic measure
zero: `ω(z, F, Ω) = 0` for all `z ∈ Ω`.
Modelling: `Ω` a domain of `ℂ*` with `Cap(ℂ \ Ω) > 0` (the setting of the section); `F` a finite subset of `∂Ω ⊆ ℂ*`
(the point `∞` allowed). -/
theorem harmonicMeasureWiener_finite_eq_zero {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω)
    (hcap : 0 < capacity (finitePart Ωᶜ)) {F : Set ExtPlane} (hF : F.Finite) (hFΩ : F ⊆ frontier Ω) :
    ∀ z ∈ Ω, harmonicMeasureWiener Ω z F = 0 := by
  sorry

/-- **Proposition 5.2** (Ch. III §5; cited at P1:4281 in the proof of Theorem 6.1). Let `{Ω_n}` be the increasing
sequence of domains introduced in Section 1. If `E = ℂ \ Ω` satisfies `Cap(E) > 0`, then for any `ζ ∈ ∂Ω` and any
`ε > 0`, (5.5) `lim_{δ→0} sup_{z∈Ω_n\B_ε(ζ)} ω(z, ∂Ω_n ∩ B_δ(ζ), Ω_n) = 0` uniformly in `n`.
Modelling: `Ω` a domain of `ℂ*` and `E` the plane set `finitePart Ωᶜ`; `ζ` a finite point (the discs `B_δ(ζ)` are
euclidean; the proof reduces to `ζ = 0` with `∞ ∈ Ω`); `ω(·, ·, Ω_n)` is `harmonicMeasureFC` of the finitely
connected Jordan domain `Ω_n` (Ch. II §1), the measures of (5.3); `B_ε(ζ)` is removed from `Ω_n` as a subset of `ℂ*`;
the limit is written in `ε`-form, "uniformly in `n`" being one threshold `δ₀` for all `n`, and the bound is compared in
`[0, ∞]`. The formula was checked against the equation image. -/
theorem prop3_5_2 {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) (hcap : 0 < capacity (finitePart Ωᶜ))
    {Ωs : ℕ → Set ExtPlane} (hΩs : IsSmoothExhaustion Ω Ωs) {ζ : ℂ} (hζ : (ζ : ExtPlane) ∈ frontier Ω) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ η : ℝ, 0 < η → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ n, ∀ z ∈ Ωs n \ toExt (ball ζ ε),
      harmonicMeasureFC (Ωs n) z (frontier (Ωs n) ∩ toExt (ball ζ δ)) ≤ ENNReal.ofReal η := by
  sorry

/-- **Proposition 5.3** (Ch. III §5; cited at P1:4347 in the proof of Theorem 6.3 and at P1:4517 in the proof of
Theorem 7.1), first part. Let `E ⊂ {z : |z| < R}` be a compact set such that `Cap(E) > 0` and let `Ω = ℂ* \ E`. Then
`U_{μ_E}` is the solution to the Dirichlet problem on `Ω^R = Ω ∩ B(0, R)` with boundary data `f(ζ) = γ(E)` for
`ζ ∈ ∂Ω` and `f(ζ) = U_{μ_E}(ζ)` for `|ζ| = R`.
Modelling: "the solution" is the Wiener solution (the proof ends "`U_{μ_E}` is the Wiener solution to the Dirichlet
problem in `Ω^R`"); `Ω^R` is the open set `toExt (B(0, R) \ E)` of `ℂ*`, which need not be connected (`ℂ* \ E` may have
bounded components), and the solution is taken on the component containing the point (`connectedComponentIn`); the
data are any `f : ℂ* → ℝ` with the stated values on `∂Ω` and on the circle `|ζ| = R` (the boundary of each component
lies in their union, so only these values enter); `γ(E)` and `U_{μ_E}` are `robinConstant E` and
`logPotential (equilibriumMeasure E)`, and the identities are in `[−∞, +∞]` (both sides are finite here). -/
theorem prop3_5_3_a {E : Set ℂ} (hE : IsCompact E) {R : ℝ} (hER : E ⊆ ball 0 R) (hcap : 0 < capacity E)
    {f : ExtPlane → ℝ} (hf₁ : ∀ ζ ∈ frontier (toExt E)ᶜ, (f ζ : EReal) = robinConstant E)
    (hf₂ : ∀ ζ : ℂ, ‖ζ‖ = R → (f (ζ : ExtPlane) : EReal) = logPotential (equilibriumMeasure E) ζ) :
    ∀ z ∈ ball (0 : ℂ) R \ E, logPotential (equilibriumMeasure E) z =
      ((wienerSolution (connectedComponentIn (toExt (ball 0 R \ E)) (z : ExtPlane)) f z : ℝ) : EReal) := by
  sorry

/-- **Proposition 5.3** (Ch. III §5), second part. Under the hypotheses of the first part, `g_Ω(·, ∞)` is the solution
to the Dirichlet problem on `Ω^R` with boundary data `γ(E) − f(ζ)`.
Modelling: as in `prop3_5_3_a`; the data `γ(E) − f` are `0` on `∂Ω` and `γ(E) − U_{μ_E}` on the circle `|ζ| = R`;
`g_Ω(·, ∞)` is `greenFunctionLim` (1.7) of the component `unboundedComponentExt E` of `ℂ* \ E` containing `∞` (Green's
function with pole `∞` lives there), so the identity is stated at the points of `Ω^R` in that component. -/
theorem prop3_5_3_b {E : Set ℂ} (hE : IsCompact E) {R : ℝ} (hER : E ⊆ ball 0 R) (hcap : 0 < capacity E)
    {f : ExtPlane → ℝ} (hf₁ : ∀ ζ ∈ frontier (toExt E)ᶜ, f ζ = 0)
    (hf₂ : ∀ ζ : ℂ, ‖ζ‖ = R →
      (f (ζ : ExtPlane) : EReal) = robinConstant E - logPotential (equilibriumMeasure E) ζ) :
    ∀ z : ℂ, (z : ExtPlane) ∈ unboundedComponentExt E → ‖z‖ < R →
      greenFunctionLim (unboundedComponentExt E) z extInf =
        wienerSolution (connectedComponentIn (toExt (ball 0 R \ E)) (z : ExtPlane)) f z := by
  sorry

/-- **Unlabelled** (Ch. III §5, P1:4203; cited at P1:4411 in the proof of Theorem 6.3, for the Jordan region `W_ε`
bounded by the `C²` curve `σ_ε`, and at P1:4517). With the same proof, Proposition 5.3 is also valid if `B(0, R)` is
replaced by any bounded Jordan region `Ω'` such that `E ∩ ∂Ω' = ∅`.
Modelling: `E` compact with `Cap(E) > 0`, `Ω = ℂ* \ E`; `Ω'` a bounded plane domain whose image in `ℂ*` is a Jordan
domain (`References.IsJordanDomainExt`), with `E` disjoint from `∂Ω'` (`E` need not lie in `Ω'`, as in the book's use
at P1:4411); both parts of Proposition 5.3, with `Ω^R` replaced by `Ω ∩ Ω'` and the circle `|ζ| = R` by `∂Ω'`, read as
in `prop3_5_3_a` and `prop3_5_3_b`. -/
theorem prop3_5_3_jordan {E : Set ℂ} (hE : IsCompact E) (hcap : 0 < capacity E) {Ω' : Set ℂ}
    (hΩ' : IsJordanDomainExt (toExt Ω')) (hΩ'b : Bornology.IsBounded Ω') (hEΩ' : Disjoint E (frontier Ω')) :
    (∀ f : ExtPlane → ℝ, (∀ ζ ∈ frontier (toExt E)ᶜ, (f ζ : EReal) = robinConstant E) →
      (∀ ζ ∈ frontier Ω', (f (ζ : ExtPlane) : EReal) = logPotential (equilibriumMeasure E) ζ) →
      ∀ z ∈ Ω' \ E, logPotential (equilibriumMeasure E) z =
        ((wienerSolution (connectedComponentIn (toExt (Ω' \ E)) (z : ExtPlane)) f z : ℝ) : EReal)) ∧
    ∀ f : ExtPlane → ℝ, (∀ ζ ∈ frontier (toExt E)ᶜ, f ζ = 0) →
      (∀ ζ ∈ frontier Ω', (f (ζ : ExtPlane) : EReal) = robinConstant E - logPotential (equilibriumMeasure E) ζ) →
      ∀ z ∈ Ω', (z : ExtPlane) ∈ unboundedComponentExt E →
        greenFunctionLim (unboundedComponentExt E) z extInf =
          wienerSolution (connectedComponentIn (toExt (Ω' \ E)) (z : ExtPlane)) f z := by
  sorry

end GarnettMarshall2005
