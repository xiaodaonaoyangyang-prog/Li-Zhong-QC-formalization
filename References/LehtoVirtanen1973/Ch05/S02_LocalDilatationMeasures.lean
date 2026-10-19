import References.LehtoVirtanen1973.Ch01.S09_LocalCharacterization
import References.LehtoVirtanen1973.Ch02.S09_CircularDilatation

/-!
# Lehto–Virtanen, Chapter V §2: Local dilatation measures

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. V §2
(pp. 195–199; `full.md` second part P2:11–126).

The three local dilatation measures of a quasiconformal mapping `w` of `G` are the local maximal dilatation
`F = localMaxDil w G` (I.9.1), the dilatation quotient `D = dilQuot w` (I.3.3, I.9.4; the book's `D` is defined only at
the regular points of `w`) and the circular dilatation `H = circularDilatation w` (II.9.1); `F` and `H` are
`ℝ≥0∞`-valued, and `D` enters through `ENNReal.ofReal`. The area measure is that of the finite plane (∞ is a null
set). The book's essential supremum and essential upper limit ("as usual", P2:43–51) are
`sup ess_{z ∈ U} φ(z) = inf_{m(E) = 0} sup_{z ∈ U - E} φ(z)`, Mathlib's `essSup φ (volume.restrict (finitePart U))`,
and `lim sup ess_{z → z₀} φ(z) = inf_{U ∋ z₀} sup ess_{z ∈ U} φ(z)`, the `limsup` of `φ` along the filter
`𝓝 z₀ ⊓ map (↑) (ae volume)` (neighbourhoods of `z₀` with a set of finite points of area zero removed). A
non-essential upper limit `lim sup_{z → z₀}` is taken over `z ≠ z₀` (as for Theorem I.9.2), and for `D` over the
regular points only (P2:43).

* Formula (2.1) (§2.1) — exists: `LehtoVirtanen1973.thm1_9_3_cor`, `LehtoVirtanen1973.circularDilatation_eq_dilQuot`
  (F at least D, and D equal to H, at every regular point of a quasiconformal mapping: the results (9.9) of I.9.6
  and of II.9.1, recalled here and cited by number at P2:65, 71)
* Unlabelled (§2.1, P2:23–29, 55): for a subdomain `U`, `K(U) = sup_{z ∈ U} D(z) = sup ess_{z ∈ U} D(z)` —
  `maxDilatationK_eq_sup_dilQuot`
* Formula (2.2) (§2.1) — `thm5_2_1` (its fourth member: F at a point is the infimum over its neighbourhoods U of the
  supremum of D over the regular points in U, the upper limit of D; (2.2) admits the point itself, which gives the
  same value since D is at most F at a regular point; cited in the derivation of Theorem 2.1, P2:43, 77)
* Definition (essential supremum, essential upper limit, §2.1) — exists: `essSup`, `Filter.limsup`
  (the essential upper limit is the upper limit along the neighbourhood filter of the point with the null sets of
  finite points removed, as described above)
* Formulas (2.3) and (2.4) (§2.1) — `thm5_2_1` ((2.3) is the equality of the first and fifth members of its chain,
  (2.4) that of the first three)
* Theorem 2.1 (§2.1) — `thm5_2_1`
* Theorem 2.2 (§2.2) — `thm5_2_2`
* Theorem 2.3 (§2.3) — `thm5_2_3`

Not stated (inventory: omitted): the claim "`F` is the least upper semicontinuous majorant of `D`" (P2:41; U−, leader
decision): it is the conjunction of the upper semicontinuity of `F` (Theorem I.9.2, `thm1_9_2`), the majorant property
(2.1) (`thm1_9_3_cor`), and a leastness which is immediate from Theorem 2.1 (for an upper semicontinuous `Φ ≥ D`, `F(z₀)
= lim sup D ≤ lim sup Φ ≤ Φ(z₀)`), and it is not cited again. Not stated either (U−): the clause that `H(z)` can exceed
`F(z)` at a non-regular point (P2:19); that (2.1) holds almost everywhere (P2:21) and that `H = D` almost everywhere
(P2:71), both immediate from (2.1) and Theorem IV.1.4 (`thm4_1_4`); that `D` and `H` can be prescribed almost everywhere
(P2:87, immediate from the Existence theorem, `existence_theorem`, with `|κ| = (Φ - 1)/(Φ + 1)`); the remark after
Theorem 2.3 (P2:121–125: Theorem 2.3 with `H` in place of `D`; Gehring's examples; the non-regular points may form a set
of Hausdorff dimension 2), which quotes results that are not used later. [OCR or misprint] P2:23 reads "Lemma I.9.4"
for Lemma I.9.1 (`lemma1_9_1`).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane)
open References (IsDomainExt finitePart)

/-! ## §2.1 Connections between `D`, `F` and `H` -/

/-- **Unlabelled** (Ch. V §2.1, P2:23–29 and P2:43–55). Let `w` be a quasiconformal mapping of the domain `G` and `U`
a subdomain of `G`. Then the maximal dilatation of `w` in `U` is `K(U) = sup_{z ∈ U} D(z)`, where `z` runs through the
regular points of `w` in `U`, and also `K(U) = sup ess_{z ∈ U} D(z)` (an arbitrary null set may be omitted besides the
non-regular points, by the Analytic definition).
Modelling: both suprema in `ℝ≥0∞`; the regular points form a set of full measure (Theorem IV.1.4), so the first
supremum is not over the empty set; the essential supremum runs over the finite points of `U` and does not see the
null set of non-regular points, where `dilQuot` has no meaning. -/
theorem maxDilatationK_eq_sup_dilQuot {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    {U : Set ExtPlane} (hU : IsDomainExt U) (hUG : U ⊆ G) :
    maxDilatationK w U = (⨆ (z : ExtPlane) (_ : IsRegularPointOf w U z), ENNReal.ofReal (dilQuot w z)) ∧
      maxDilatationK w U = essSup (fun z : ℂ => ENNReal.ofReal (dilQuot w z)) (volume.restrict (finitePart U)) := by
  sorry

/-- **Theorem 2.1** (Ch. V §2.1). The dilatation measures `D`, `F` and `H` of a quasiconformal mapping `w : G → G′`
satisfy the relations
`F(z₀) = lim sup_{z → z₀} F(z) = lim sup ess_{z → z₀} F(z) = lim sup_{z → z₀} D(z) = lim sup ess_{z → z₀} D(z)`
`= lim sup ess_{z → z₀} H(z)` for every `z₀ ∈ G`.
Modelling: `z₀` may be `∞` or a preimage of `∞`. The non-essential upper limits are taken over `z ≠ z₀`, and the one
of `D` over the regular points of `w` only (the book's `D` is defined there, P2:43); the essential upper limits
(P2:50) are upper limits along `𝓝 z₀ ⊓ map (↑) (ae volume)`, which ignore the null set of non-regular points where
`dilQuot` has no meaning. -/
theorem thm5_2_1 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) {z₀ : ExtPlane}
    (hz₀ : z₀ ∈ G) :
    localMaxDil w G z₀ = limsup (localMaxDil w G) (𝓝[≠] z₀) ∧
      localMaxDil w G z₀ =
        limsup (localMaxDil w G) (𝓝 z₀ ⊓ Filter.map ((↑) : ℂ → ExtPlane) (ae (volume : Measure ℂ))) ∧
      localMaxDil w G z₀ =
        limsup (fun z => ENNReal.ofReal (dilQuot w z)) (𝓝[{z | IsRegularPointOf w G z} \ {z₀}] z₀) ∧
      localMaxDil w G z₀ = limsup (fun z => ENNReal.ofReal (dilQuot w z))
        (𝓝 z₀ ⊓ Filter.map ((↑) : ℂ → ExtPlane) (ae (volume : Measure ℂ))) ∧
      localMaxDil w G z₀ =
        limsup (circularDilatation w) (𝓝 z₀ ⊓ Filter.map ((↑) : ℂ → ExtPlane) (ae (volume : Measure ℂ))) := by
  sorry

/-! ## §2.2 Existence theorem for the local maximal dilatation -/

/-- **Theorem 2.2** (Ch. V §2.2). Let `Φ` be a real-valued, upper semicontinuous, bounded function defined in `G`, with
`inf Φ(z) ≥ 1`. Then there exists a quasiconformal mapping `w` of `G` whose local maximal dilatation `F(z)` coincides
with `Φ(z)` for almost all `z ∈ G` and exceeds `Φ(z)` nowhere in `G`.
Modelling: `G` is a domain of `ℂ̄`; `Φ : ℂ̄ → ℝ` matters only on `G`, where it is upper semicontinuous, bounded above
and at least `1` (so bounded). -/
theorem thm5_2_2 {G : Set ExtPlane} (hG : IsDomainExt G) {Φ : ExtPlane → ℝ} (husc : UpperSemicontinuousOn Φ G)
    (hbdd : BddAbove (Φ '' G)) (hge : ∀ z ∈ G, 1 ≤ Φ z) :
    ∃ w : ExtPlane → ExtPlane, IsQuasiconformalMap w G ∧
      (∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), localMaxDil w G z = ENNReal.ofReal (Φ z)) ∧
      ∀ z ∈ G, localMaxDil w G z ≤ ENNReal.ofReal (Φ z) := by
  sorry

/-! ## §2.3 An example where `F(z)` is greater than `D(z)` almost everywhere -/

/-- **Theorem 2.3** (Ch. V §2.3). Let `G` be a domain and `ε` and `M` two positive numbers. Then there exists a
quasiconformal mapping `w` of `G` for which `F(z) > D(z)` almost everywhere in `G` and `F(z) = D(z) + M` except for a
set of area `≤ ε`.
Modelling: the exceptional set `E` is a set of finite points; off `E` the point `z` is regular (the book's `D(z)` is
defined only at regular points, and the non-regular points form a null set which `E` may contain), so `dilQuot` is
read only where it is the book's `D`; the almost-everywhere inequality likewise ignores the null set of non-regular
points. -/
theorem thm5_2_3 {G : Set ExtPlane} (hG : IsDomainExt G) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) :
    ∃ w : ExtPlane → ExtPlane, IsQuasiconformalMap w G ∧
      (∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)), ENNReal.ofReal (dilQuot w z) < localMaxDil w G z) ∧
      ∃ E : Set ℂ, volume E ≤ ENNReal.ofReal ε ∧ ∀ z ∈ finitePart G \ E,
        IsRegularPointOf w G z ∧ localMaxDil w G z = ENNReal.ofReal (dilQuot w z + M) := by
  sorry

end LehtoVirtanen1973
