import References.Pommerenke1992.Ch10.S05_SizeOfTheBoundary
import References.LehtoVirtanen1973.Ch03.S04_ModuleArcFamilies

/-!
# Pommerenke 1992, Ch. 11 §11.1 An Overview

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 11 *Local Boundary Behaviour*, §11.1; source
`full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 2689–2739.
The whole chapter is P2 l. 2689–3705 (book pp. 245–267; the references follow), so there is no seam. The chapter
heading is lost in the OCR (it survives only as a discarded layout block of book p. 245); the title is that of the
table of contents (P1 l. 157). A library due-date slip was scanned over the left column of book p. 247
(P2 l. 2774–2802): part of the proof of Theorem 11.1 (i) ⇒ (ii), with its local displays (1)–(4), is lost. No
statement is affected; the statement of Theorem 11.1 (P2 l. 2752–2772) is intact.

**Summary.** The chapter first considers quasicircles `J` with `|a - w| + |w - b| = (1 + o(1))|a - b|` as `a, b ∈ J`,
`|a - b| → 0`, where `w` lies on `J` between `a` and `b` (the asymptotically conformal curves of §11.2). The conformal
maps `f` of `𝔻` onto the inner domain of `J` are characterized by (11.1.1) `(1 - |z|)f''(z)/f'(z) → 0`, that is,
`log f' ∈ B₀` (Theorem 11.1 and (11.2.5)). Then it studies a general conformal map `f` of `𝔻` near a point `ζ ∈ 𝕋`
where `f` has a finite angular limit `ω`: the case that `ω` is well-accessible (a local version of the John domains;
§11.3), the local version (11.1.2) `(z - ζ)f''(z)/f'(z) → 0` in every Stolz angle of (11.1.1) (Proposition 11.4),
and a geometric characterization of isogonality (Theorem 11.6). The main tool of §11.2–§11.3 is the Carathéodory kernel
theorem (Theorem 1.8). The main tool of §11.4–§11.5 is the module of curve families of §9.2. For the domains (11.1.3)
`G = {ω + ρe^{iϑ} : 0 < ρ < c, ϑ₋(ρ) < ϑ < ϑ₊(ρ)}` and the notation of Fig. 11.1, `mod Γ(ρ₁, ρ₂)` is approximately
additive if and only if `f⁻¹(T(r))` is approximately a circular arc (RoWa76, JenOi77; Proposition 11.8). This gives
conditions for `f` to be conformal at a point (Theorems 11.9, 11.10), the simplest being the Warschawski condition
(Corollary 11.11); under a regularity condition on `ϑ_±` the asymptotic formula (11.1.4) with the Ahlfors integral
holds (Theorem 11.16).

**No items; see §11.2–§11.5.** The overview states no labelled result, and every claim in it is a preview of a
labelled result or definition of `Ch11/S02_AsymptoticallyConformalCurvesAndB0`, `Ch11/S03_VisserOstrowskiQuotient`,
`Ch11/S04_ModuleAndConformality` or `Ch11/S05_AhlforsIntegral`. This file holds only this module docstring (the
leader's ruling QD7, as for `Ch07/S01` and `Ch08/S01`); the chapter conventions below apply to `Ch11/S02`–`Ch11/S05`.

Not items (DESIGN §3), all previews: the display `|a - w| + |w - b| = (1 + o(1))|a - b|` (P2 l. 2694; the definition
(11.2.1)), (11.1.1) (the crop prints `z → 1` for `|z| → 1` [misprint?]; condition (ii) of Theorem 11.1) and
"`log f'` lies in the little Bloch space `B₀`" ((11.2.5)); "well-accessible, i.e. accessible through a curvilinear
sector in `G`", "a local version of the concept of a John domain" ((11.3.1)), (11.1.2) (Proposition 11.4) and "a
geometric characterization of isogonality" (Theorem 11.6); the Carathéodory kernel theorem, named as the main tool
(Theorem 1.8, used only in proofs of this chapter); the module of curve families "introduced in Section 9.2", the
domains (11.1.3) (the crop prints `w` for the point `ω`; (11.5.9) has `ω`) and Fig. 11.1, whose caption speaks of
"all curves in the shaded domain that separate the circular arcs `T(ρ₁)` and `T(ρ₂)`" (the family `Γ(ρ₁, ρ₂)` is
defined formally in §11.4 by crosscuts of `G`, and that definition is used); the "key fact" of RoWa76, JenOi77
(Proposition 11.8); the Warschawski condition (named, P2 l. 2719–2723: if `ϑ_±(ρ) = ±(π/2 - δ(ρ))` with `δ`
increasing, then `f` is conformal at `ζ` if and only if `∫₀^c δ(ρ)ρ⁻¹ dρ < ∞`), a preview of Corollary 11.11, which
carries the name; its form differs (domains (11.1.3) and "if and only if" here, `G₀ ⊆ f(𝔻) ⊆ 𝔻` and two separate parts
in Corollary 11.11), so it is not passed with a pointer; (11.1.4) and "the Ahlfors integral in (4) plays an important
role in a wider context" (Theorem 11.16, where "a certain regularity condition" is (11.5.10)). Omitted (U−, remarks):
the remark on strip domains and the boundary point `∞`, and the history (Ahlfors, Ostrowski, Wolff, Warschawski,
Ferrand; GaOs49a, GaOs49b, LeF55, the papers of Rodin and Warschawski).

**Conventions of Chapter 11** (the later files refer to them as "as in §11.1").
- *Where the chapter works.* §11.2: `J ⊆ ℂ` is a Jordan curve (`LiZhongQC.IsJordanCurve (toExt J)`) and `f` maps `𝔻`
  conformally onto its inner domain (`LiZhongQC.IsConformalOnto f unitDisc (innerDomain J)`); the boundary values
  `f(ζ)`, `ζ ∈ 𝕋`, are those of the continuous extension `F` of `f` to `𝔻̄` (`ContinuousOn F (closedBall 0 1)`,
  `EqOn F f unitDisc`; it exists by Theorem 2.6), the `quasicircle_theorem` pattern of §5.1. §11.3–§11.5
  (P2 l. 2957, 3208, 3492): `f` maps `𝔻` conformally onto `G ⊆ ℂ` (`IsConformalOnto f unitDisc G`) and has the finite
  angular limit `ω = f(ζ)` at the given `ζ ∈ 𝕋` (`HasAngularLimit (fun z => (f z : ExtPlane)) ζ ω`, §1.2, which
  contains `ζ ∈ 𝕋`); this standing assumption is explicit in every statement. Theorem 11.10 and Corollary 11.11 add
  `G ⊆ 𝔻` and `ω ∈ 𝕋` (P2 l. 3333). Since `ω` is the angular limit of the conformal map `f`, it lies on `∂G`, so
  `f(z) ≠ ω` for `z ∈ 𝔻`.
- *Limits.* "As `z → ζ` in every Stolz angle" is `HasAngularLimit` (§1.2). "Conformal at `ζ`" is the Ch. 4
  `IsConformalAtBoundary` (a finite nonzero angular derivative) and "isogonal at `ζ`" is `IsIsogonalAt` (§4.3).
  "`|z| → 1-`" is `∀ ε > 0, ∃ r < 1, ∀ z, r < |z| < 1 → …`; "`|z| → 1+`" (Theorem 11.1 (v)) is the essential version
  `∀ ε > 0, ∃ r > 1, ∀ᵐ z, 1 < |z| < r → …`, because the dilatation of a quasiconformal map exists only almost
  everywhere. Limits "as `ρ → 0`" and "as `ρ₁ < ρ₂ → 0`" are written with `ε` and `δ`; `∼` is
  `Asymptotics.IsEquivalent`.
- *Derivatives, branches.* `f'`, `f''` are `deriv f`, `deriv (deriv f)`; for a conformal `f`, `f' ≠ 0` in `𝔻`, so the
  quotients `f''/f'` are genuine. `log f'` is any `L` holomorphic in `𝔻` with `exp ∘ L = f'` there (the `cor4_5`
  pattern); the statements hold for every branch. `S_f` is the project's `LiZhongQC.schwarzian`.
- *Distance to the boundary.* `d_f(z) = dist(f(z), ∂G)` is `distToBoundary f z` (§1.3, (1.3.16); recalled at
  P2 l. 2957); diameters are `Metric.ediam` (`ℝ≥0∞`-valued, so an unbounded set has diameter `∞`).
- *Constants.* "`M₁, M₂, …` denote suitable constants" (P2 l. 2957): they depend on `f` and `ζ` (and on `α` in
  Theorem 11.3), so they are existential after the data. The only numerical constant in a statement is the `32` of
  (11.5.5).
- *Measures and module.* Linear measure `Λ` is `μH[1]` (the Part C ruling), so `λ(ρ) = Λ(T(ρ))` of (11.5.1) is
  `μH[1] (T ρ)` in `ℝ≥0∞`; `dim` is Mathlib's `dimH` (in `ℝ≥0∞`). The module of a curve family (§9.2, (9.2.1),
  (9.2.2)) is `LehtoVirtanen1973.arcFamilyModule` (the leader's ruling QD2): the families are sets of point sets
  (`Set (Set ExtPlane)`), and the normalization `inf ∬ρ²` is the same, which the constants of Theorems 11.9 and 11.13
  depend on. Modules are `ℝ≥0∞`-valued. The statements avoid `ℝ≥0∞`-subtraction: "`mod Γ - ∫ ≥ 0`, decreasing" and
  (11.5.4) are written additively, and `.toReal` of a module or an integral appears only where the statement also
  asserts its finiteness.
- *Crosscuts and separation.* Crosscuts and null-chains are those of Ch. 2 (`IsCrosscut`, `IsNullChain`, on `toExt G`;
  Ch. 2 works in `Ĉ`); "separate" is `LehtoVirtanen1973.SeparatesIn` (the Ch. 2 convention). Sequences "`ρ_n ↘ 0`"
  are `StrictAnti` in the null-chain condition of (11.4.1) (equal radii would repeat a crosscut) and `Antitone` with
  positive terms in Theorem 11.10 (a repeated radius gives a zero term there).
- *Harmonic measure* is not used in Chapter 11: `ω` always denotes the boundary point `f(ζ)`.
-/

namespace Pommerenke1992

end Pommerenke1992
