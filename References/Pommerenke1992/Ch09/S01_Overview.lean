import References.Pommerenke1992.Ch09.S04_PflugersTheorem

/-!
# Pommerenke 1992, Ch. 9 §9.1 An Overview

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 9 *Curve Families and Capacity*, §9.1; source
`full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 391–448. The
chapter occupies P2 l. 391–1664 (book pp. 195–221, all present). The chapter heading is lost in the OCR (P2 l. 389,
Exercise 8.6.7, is followed by `## 9.1 An Overview`); the title is that of the table of contents (P1 l. 144).

**Summary.** The chapter introduces two conformally invariant or conformally controlled measures of size. The module
of a curve family, `mod Γ = inf_ρ ∬_B ρ² dx dy` over the admissible `ρ` (9.1.1), (9.1.2) (Beurling–Ahlfors; its
inverse is the extremal length), is treated in §9.2. The logarithmic capacity of a compact set (Fekete's transfinite
diameter, (9.1.3)), its extension to arbitrary sets, the equilibrium measure and the Green's function with pole at `∞`
are treated in §9.3, where "nearly everywhere" (outside a set of zero capacity) is defined. Pfluger's theorem (9.1.5)
connects the two notions (§9.4). It gives precise estimates for conformal maps (§9.5): Beurling's theorem (9.1.6) on
the finiteness of `∫₀¹ |f'(rζ)| dr` for nearly all `ζ`, the estimate (9.1.7) (Corollary 9.20) and the analogue (9.1.8)
of Löwner's lemma (Theorem 9.21).

This section has one named result, Pfluger's theorem; it is Theorem 9.17 (9.4.9), so the file has no declarations.

* Pfluger's Theorem (named, §9.1, (9.1.5), P2 l. 423–427; index "Pfluger's theorem 196, 212") — exists:
  `Pommerenke1992.thm9_17_b` (Theorem 9.17 (9.4.9), the same statement for a Borel set on the unit circle and the family
  of the curves connecting the circle of radius r with it; (9.1.5) prints the family as Γ_E(r), where the crop of
  (9.4.9) prints Γ_r(r))

**Import order** (the exception of Ch. 2 §2.1, Ch. 4 §4.1 and Ch. 6 §6.1, leader ruling QD7). The overview names a
result that is stated in §9.4, so this file imports the file of §9.4; no other file imports it.

Not items (DESIGN §3): (9.1.1), (9.1.2), "`1/mod Γ` is called the extremal length" and the history of the module
(AhBeu50, LeVi73; previews of (9.2.1), (9.2.2) and of P2 l. 576); (9.1.3) (Fekete's capacity), "an alternative
definition is through potentials" and "the concept of capacity can be generalized to Borel (and even Souslin) sets"
(previews of (9.3.1), (9.3.7), (9.3.36) and of Theorem 9.12; remarks); "nearly everywhere" (P2 l. 415, the first
mention; the definition is restated formally at P2 l. 1105, `NearlyEverywhereOn`); "if `E ⊆ 𝕋` then
`cap E ≥ sin[Λ(E)/4]` with equality for an arc" (a preview of (9.3.33), (9.3.31)); (9.1.4) `cap E = 0 ⇒ Λ(E) = 0`,
"nearly everywhere implies almost everywhere" and the Cantor set (U−: not cited by number, restated at P2 l. 1105 with
the forward reference (10.1.3); false as literally stated for non-Borel sets under the inner capacity: a Bernstein set
of `𝕋` has capacity `0` and outer measure `2π`; the Cantor set is an example); (9.1.6) (Beu40; the crop prints
`|dζ|` for `dr` [misprint?]; a preview of (9.5.7), proved at the end of the proof of Theorem 9.19, not cited); (9.1.7)
(a preview of Corollary 9.20 with `a = π`, `1 + π² < 11`); (9.1.8) (a preview of Theorem 9.21, (9.5.12)); "an analogue
of Löwner's lemma that `Λ(f(A)) ≥ Λ(A)`" (the recall of `lowner_lemma`, (4.4.8)).

**Conventions of Chapter 9** (the files of §9.2–§9.5 refer to them as "as in §9.1").
- Maps: "`f` maps `𝔻` conformally into `ℂ`" is `DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc` (the Ch. 1
  convention); "onto `G`" is `IsConformalOnto f unitDisc G`; "into `𝔻`" adds `MapsTo f unitDisc unitDisc`. A map of `𝔻`
  onto a domain containing `∞` (Corollary 9.18) is a conformal map of `ℂ̂` (`LehtoVirtanen1973.IsConformalMap`); the
  map `h = cζ + c₀ + …` of `𝔻*` in Corollary 9.9 is `c g₁` with `g₁ ∈ Σ` (`IsClassSigma`), and `Σ` is the class of
  Theorem 9.23.
- Domains containing `∞`: `G : Set ExtPlane` with `References.IsDomainExt G` and `extInf ∈ G`; `E = ∂G` is the compact
  plane set `References.finitePart (frontier G)`. The outer domain of a compact `E ⊆ ℂ` is
  `GarnettMarshall2005.unboundedComponentExt E`.
- Curve families and the module (leader ruling QD2): a curve family is a set of point sets of `ℂ̂`
  (`Set (Set ExtPlane)`) whose members are Jordan arcs (open, half-open or closed) or Jordan curves; "`Γ` in `B`" is
  `IsCurveFamilyIn Γ B`; `mod Γ` is `LehtoVirtanen1973.arcFamilyModule Γ` in `[0, ∞]` (the same normalization, which
  Theorems 11.9 and 11.13 rely on); the book's independence of `B` is built in (the densities live on `ℂ`); the image
  family is `f(Γ) = (fun C => OnePoint.map f '' C) '' Γ`; the standard families are `joiningArcFamily`,
  `separatingCurveFamily` (§9.2) and `pflugerFamily` (`Γ_E(r)`, §9.4); `1/mod` is the inverse of `[0, ∞]`.
- Capacity (leader ruling QD1): the capacity of a compact set is `GarnettMarshall2005.capacityCompact` (GM's Robin
  capacity, one notion for Pommerenke and GM, with the same normalization: a disc has capacity equal to its radius, a
  segment one quarter of its length); Pommerenke's definition (9.3.7) by Fekete's transfinite diameter is the theorem
  `eq9_3_7`. The (inner) capacity (9.3.36) of an arbitrary set is `GarnettMarshall2005.capacity`, literally the same
  supremum over compact subsets. Values in `[0, ∞]` (an unbounded set can have infinite capacity). The Fekete
  quantities `Δ_n`, Fekete systems, `q_n`, `γ_n` are defined genuinely in §9.3.
- Junk-free forms: `log(b/cap)`, `1/log(b/cap)` (Proposition 9.11, Corollary 9.13) with positivity hypotheses or the
  book's convention `1/log(b/0) = 0` through `ENNReal.log`; `exp(−π/mod Γ)` (Theorem 9.17) and `exp(−πb²/area H)`
  (Theorem 9.24) as `EReal.exp` of a quotient in `[0, ∞]` (`exp(−π/0) = 0`); never `Real.log 0 = 0` or `x/0 = 0`.
- Potentials, Green's function, equilibrium measure (leader ruling QD4): Pommerenke's own notions `greenFnInf` and
  `IsEquilibriumMeasure` of §9.3 (GM states no item giving its `equilibriumMeasure` the properties Pommerenke uses as
  his definition); the potential `∫_E log |z − ζ| dμ(ζ)` is `−GarnettMarshall2005.logPotential μ z` (`EReal`); "harmonic
  in `G ∖ {∞}`" is `InnerProductSpace.HarmonicOnNhd` on `finitePart G`; "subharmonic in `ℂ`" is
  `References.IsSubharmonicOn`; `O(·)` as `z → ∞` is along `cocompact ℂ`.
- Measures: `Λ` of plane sets is `μH[1]`, of subsets of `𝕋` the arc length `circleMeasure` (Ch. 4); area is `volume`;
  "Borel" is `MeasurableSet`, "Souslin" `MeasureTheory.AnalyticSet`, "`F_σ`" `IsFSigma` (§6.2); "for almost all `ϑ`"
  is `∀ᵐ ϑ : ℝ`.
- Boundary values: `f(ζ)` is the angular limit (`HasAngularLimit`; for conformal maps equal to the radial limit), and
  `f(E)` the set of these limits (the finite part of `radialImage`, §6.2); `f⁻¹(B)` on `𝕋` is `radialPreimage`; for
  `g ∈ Σ` the angular limit from outside at `ζ` is the angular limit of `z ↦ g(1/z)` at `ζ̄` (Part C ruling Q6.9).
- The harmonic measure `ω(z, A)` of `A ⊆ 𝕋` with respect to `𝔻` is `harmonicMeasure z A` ((4.4.1)); `λ(z, z')` is
  `hypDistD` ((1.2.8)); `d_f` is `distToBoundary`; the non-euclidean segment is `nonEuclideanSegment`.
- Constants: "absolute constant" (`K` in Proposition 9.5, `K₁` in Theorem 9.19, `K₂` in Corollary 9.20) is
  `∃ K, ∀ …`; "`M` and `R₀` depend only on `f₁` and `f₂`" (Corollary 9.18) is `∀ f₁ f₂, ∃ M R₀, ∀ a R`.
- "Nearly all `ζ ∈ E`" is `NearlyEverywhereOn E P`: the set where `P` fails has inner capacity `0`.
-/

namespace Pommerenke1992

end Pommerenke1992
