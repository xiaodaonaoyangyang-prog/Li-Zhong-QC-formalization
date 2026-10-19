import References.GarnettMarshall2005.Ch03.S07_WienerSeries

/-!
# Garnett–Marshall, Chapter III §8: Polar sets and sets of harmonic measure zero

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. III §8 (pp. 102–104;
`full.md` P1:4616–4733).

Conventions as in §5–§7. A polar set is a plane set of capacity zero (`IsPolarSet`, §4; recalled at P1:4618). The
domains of the section are domains of `ℂ*`, and may contain `∞` (Corollary 8.4 works on `ℂ* \ E`). Subharmonic
functions are the shared planar notion `References.IsSubharmonicOn` (`EReal`-valued; the book uses the notion without
defining it, leader ruling B7), read on a domain of `ℂ*` in the charts of `ℂ*` (`IsSubharmonicOnExt`, as harmonic
functions are read by `HarmonicOnExt`). "`u` is bounded above in `Ω`" is a real bound; `limsup_{z→ζ} u(z)` is the
`limsup` along `𝓝[Ω] ζ` in `ℂ*`, taken in `[−∞, +∞]` (a complete lattice: no junk value). Harmonic measure is Wiener's
(`harmonicMeasureWiener`, §5); `Cap` of a subset of `ℂ*` is the capacity (4.8) of its finite part.

* Definition (subharmonic function on a domain of `ℂ*`, used without definition from Theorem 8.1 on, §8) —
  `IsSubharmonicOnExt`
* Theorem 8.1 (§8; (8.1), (8.2)) — `thm3_8_1`
* Theorem 8.2 (§8; (8.6)) — `thm3_8_2`
* Corollary 8.3 (§8) — `cor3_8_3`
* Corollary 8.4 (§8; "H" read "If" [OCR or misprint; inline, no crop]; [OCR?] "Ω ∩ E" read `Ω \ E`) —
  `cor3_8_4_a`, `cor3_8_4_b`, `cor3_8_4_c`

Not stated (inventory U−): the announcement of the section, "if a compact set `E` is polar and `u > 0` is harmonic on
`ℂ* \ E`, then `u` is constant" (P1:4618, restated after Corollary 8.4); the example showing that (8.1) is essential
for Theorem 8.1 (P1:4640, a remark); "Theorem 8.1 is a generalization of Lindelöf's maximum principle, Lemma I.1.1"
(P1:4642, a remark); "Nevanlinna called a polar set a set of absolute harmonic measure 0" (P1:4700, terminology);
"every positive harmonic function and every bounded harmonic function in `ℂ* \ E` is constant" for compact polar `E`
(P1:4718, immediate from Corollary 8.4). (8.3)–(8.5) are steps of the proof of Theorem 8.1.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt extInf)
open References (IsDomainExt IsJordanDomainExt finitePart)

/-- **Definition** (subharmonic function on a domain of `ℂ*`, Ch. III §8; used without definition in Theorem 8.1 and
Corollaries 8.3–8.4, where the domain may contain `∞`). `u : ℂ* → [−∞, +∞]` is subharmonic in `Ω` if near every point
`z ∈ Ω`, read in the chart of `ℂ*` at `z` (`LehtoVirtanen1973.extChartInv`: `ζ ↦ z + ζ` at a finite `z`, `ζ ↦ 1/ζ`
at `z = ∞`), it is subharmonic on some disc about `0`.
Modelling (leader ruling B7): the planar notion is the shared `References.IsSubharmonicOn` (`u < +∞`, upper
semicontinuous, harmonic majorants on closed discs; `u ≡ −∞` admitted); at `∞` the book reads functions through
`u(1/ζ)`, as for harmonic functions (`HarmonicOnExt`). Subharmonicity is a local property, so the local condition in
the charts is the notion; only the values of `u` on `Ω` matter (the discs may be taken inside `Ω`). -/
def IsSubharmonicOnExt (u : ExtPlane → EReal) (Ω : Set ExtPlane) : Prop :=
  ∀ z ∈ Ω, ∃ r : ℝ, 0 < r ∧ References.IsSubharmonicOn (u ∘ LehtoVirtanen1973.extChartInv z) (ball 0 r)

/-- **Theorem 8.1** (Ch. III §8; cited at P1:4640, 4642, 4714). Suppose `Ω` is a domain such that `Cap(ℂ* \ Ω) > 0`,
and suppose `A` is a Borel subset of `∂Ω` such that (8.1) `ω(z₀, A, Ω) = 0` holds for some `z₀ ∈ Ω`. Let `u(z)` be a
subharmonic function in `Ω`. If `u` is bounded above in `Ω` and if (8.2) `limsup_{z→ζ} u(z) ≤ m` for all
`ζ ∈ ∂Ω \ A`, then `u(z) ≤ m` for all `z ∈ Ω`.
Modelling: `Ω` a domain of `ℂ*`; `ω` is Wiener's harmonic measure (§5); `u : ℂ* → [−∞, +∞]` subharmonic in the charts
(`IsSubharmonicOnExt`), bounded above on `Ω` by a real constant; `m` real; the `limsup` in (8.2) is taken along
`z → ζ`, `z ∈ Ω`, in `[−∞, +∞]` (the filter is proper, `ζ` being in the closure of `Ω`). -/
theorem thm3_8_1 {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) (hcap : 0 < capacity (finitePart Ωᶜ)) {A : Set ExtPlane}
    (hA : MeasurableSet A) (hAΩ : A ⊆ frontier Ω) {z₀ : ExtPlane} (hz₀ : z₀ ∈ Ω)
    (h81 : harmonicMeasureWiener Ω z₀ A = 0) {u : ExtPlane → EReal} (hu : IsSubharmonicOnExt u Ω)
    (hub : ∃ M : ℝ, ∀ z ∈ Ω, u z ≤ (M : EReal)) {m : ℝ}
    (h82 : ∀ ζ ∈ frontier Ω \ A, limsup u (𝓝[Ω] ζ) ≤ (m : EReal)) :
    ∀ z ∈ Ω, u z ≤ (m : EReal) := by
  sorry

/-- **Theorem 8.2** (Ch. III §8; cited at P1:4700, 4714). Suppose `A` is a Borel set. Then `A` is a polar set if and
only if (8.6) `ω(z, A ∩ ∂Ω, Ω) = 0` for every domain `Ω` such that `Cap(ℂ* \ Ω) > 0` and for every `z ∈ Ω`.
Modelling: `A` a Borel set of the plane (polar sets are plane sets, (4.8)), seen in `ℂ*` as `toExt A`; `Ω` ranges over
the domains of `ℂ*`; `ω` is Wiener's harmonic measure (§5). -/
theorem thm3_8_2 {A : Set ℂ} (hA : MeasurableSet A) :
    IsPolarSet A ↔ ∀ Ω : Set ExtPlane, IsDomainExt Ω → 0 < capacity (finitePart Ωᶜ) →
      ∀ z ∈ Ω, harmonicMeasureWiener Ω z (toExt A ∩ frontier Ω) = 0 := by
  sorry

/-- **Corollary 8.3** (Ch. III §8; cited at P1:4720, 4732). Suppose `Ω` is a domain such that `Cap(ℂ* \ Ω) > 0`, and
suppose `u` is subharmonic and bounded above in `Ω`. If `limsup_{z→ζ} u(z) ≤ m` for all `ζ ∈ ∂Ω \ A`, where `A` is a
Borel set and `Cap(A) = 0`, then `sup_Ω u(z) ≤ m`.
Modelling: as in Theorem 8.1; `A` a Borel set of `ℂ*` and `Cap(A)` the capacity (4.8) of its finite part; the
supremum over `Ω` is taken in `[−∞, +∞]`. -/
theorem cor3_8_3 {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) (hcap : 0 < capacity (finitePart Ωᶜ))
    {u : ExtPlane → EReal} (hu : IsSubharmonicOnExt u Ω) (hub : ∃ M : ℝ, ∀ z ∈ Ω, u z ≤ (M : EReal)) {m : ℝ}
    {A : Set ExtPlane} (hA : MeasurableSet A) (hA0 : capacity (finitePart A) = 0)
    (hlim : ∀ ζ ∈ frontier Ω \ A, limsup u (𝓝[Ω] ζ) ≤ (m : EReal)) :
    (⨆ z ∈ Ω, u z) ≤ (m : EReal) := by
  sorry

/-- **Corollary 8.4** (Ch. III §8; cited at P1:4718 and in App. E, P3:3847, "by Theorem E.2 and Corollary III.8.4"),
first part. Suppose `E` is a compact polar set. If `u(z)` is subharmonic and bounded above in `ℂ* \ E`, then `u` is
constant.
Modelling: "H u(z) is subharmonic" (P1:4716) is "If u(z) is subharmonic" [OCR or misprint; inline, no crop]; `E` a
compact plane set with `IsPolarSet E`; `u : ℂ* → [−∞, +∞]` subharmonic on `(toExt E)ᶜ` in the charts of `ℂ*` (`∞`
included), bounded above by a real constant; "constant" on `ℂ* \ E`, the constant being in `[−∞, +∞)`. -/
theorem cor3_8_4_a {E : Set ℂ} (hE : IsCompact E) (hpol : IsPolarSet E) {u : ExtPlane → EReal}
    (hu : IsSubharmonicOnExt u (toExt E)ᶜ) (hub : ∃ M : ℝ, ∀ z ∈ (toExt E)ᶜ, u z ≤ (M : EReal)) :
    ∃ c : EReal, ∀ z ∈ (toExt E)ᶜ, u z = c := by
  sorry

/-- **Corollary 8.4** (Ch. III §8), second part. If `Ω ⊃ E` is a Jordan domain, then every bounded harmonic function
on `Ω \ E` extends to be harmonic on `Ω`.
Modelling: the printed "every bounded harmonic function on `Ω ∩ E` extends to be harmonic on `E`" is read with
`Ω \ E` [OCR?] (`E ⊂ Ω`, so `Ω ∩ E = E` carries no harmonic function, and the proof, "we shrink `Ω` so that `u` is
continuous on `∂Ω` … `v` is the harmonic extension of `u` to `Ω`", works on `Ω \ E`; the running text has no image to
check; in `layout.json` (page_idx 121) the inline formula is OCR'd `\Omega \cap E` with confidence 0.70, the lowest in
the statement, while "extends to be harmonic on E." is text with confidence 1.0);
"extends to be harmonic on `E`" is: agrees on `Ω \ E` with a function harmonic on `Ω`; `E` compact polar, the
hypothesis of the corollary; `Ω` a Jordan domain of `ℂ*` (`References.IsJordanDomainExt`), harmonic functions
real-valued and harmonic in the charts of `ℂ*` (`HarmonicOnExt`). -/
theorem cor3_8_4_b {E : Set ℂ} (hE : IsCompact E) (hpol : IsPolarSet E) {Ω : Set ExtPlane}
    (hΩ : IsJordanDomainExt Ω) (hEΩ : toExt E ⊆ Ω) {u : ExtPlane → ℝ} (hu : HarmonicOnExt u (Ω \ toExt E))
    (hub : ∃ M : ℝ, ∀ z ∈ Ω \ toExt E, |u z| ≤ M) :
    ∃ v : ExtPlane → ℝ, HarmonicOnExt v Ω ∧ EqOn v u (Ω \ toExt E) := by
  sorry

/-- **Corollary 8.4** (Ch. III §8), third part. Conversely, if `Cap(E) > 0`, if `Ω` is the unbounded component of
`ℂ* \ E`, and if `A` is a compact subset of `E` such that `0 < μ_E(A) < 1`, then `u(z) = ω(z, A, Ω)` is a
non-constant bounded harmonic function on `Ω`.
Modelling: here `E` is a compact plane set with `Cap(E) > 0` (the "Conversely" replaces the polarity of the first two
parts); `Ω` is the component `unboundedComponentExt E` of `ℂ* \ E` containing `∞`; `μ_E` is `equilibriumMeasure E`
(§4), compared in `[0, ∞]`; `ω` is Wiener's harmonic measure and `u(z)` its real value on `A` (a finite measure),
harmonic in the charts of `ℂ*`. -/
theorem cor3_8_4_c {E : Set ℂ} (hE : IsCompact E) (hcap : 0 < capacity E) {Ω : Set ExtPlane}
    (hΩ : Ω = unboundedComponentExt E) {A : Set ℂ} (hA : IsCompact A) (hAE : A ⊆ E)
    (hμA : 0 < equilibriumMeasure E A ∧ equilibriumMeasure E A < 1) :
    HarmonicOnExt (fun z => (harmonicMeasureWiener Ω z (toExt A)).toReal) Ω ∧
      (∃ M : ℝ, ∀ z ∈ Ω, |(harmonicMeasureWiener Ω z (toExt A)).toReal| ≤ M) ∧
      ¬ ∃ c : ℝ, ∀ z ∈ Ω, (harmonicMeasureWiener Ω z (toExt A)).toReal = c := by
  sorry

end GarnettMarshall2005
