import LiZhongQC.Ch07.S27_TeichmullerExistence
import References.GardinerLakic2000.Ch02.S07_FuchsianGroups
import References.LehtoVirtanen1973.Ch01.S01_TopologicalProperties

/-!
# Imayoshi–Taniguchi, Chapter 2 §2.1–§2.4: Riemann surfaces, universal coverings, Fuchsian groups (W2 batch I2)

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 2 §2.1–§2.4 (`full.md` IT1:764–1400,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions as in `Ch03/S02_FenchelNielsen`: a Fuchsian group is a subgroup `Γ` of `SL(2, ℝ)` acting through Möbius transformations on
the upper half-plane `ℍ`; `Aut(H) = PSL(2, ℝ)` is read through `SL(2, ℝ)` (the topology of matrices; the elements `±γ` give the same
Möbius map), `ℝ̂ = ℝ ∪ {∞}` is `toExt realLine ∪ {∞}`, `LiZhongQC.IsFuchsian Γ` is proper discontinuity (IT Theorem 2.17), a
Fuchsian group in IT's sense (discrete) is `DiscreteTopology Γ`. The Möbius map of `γ` is `z ↦ (a z + b)/(c z + d)`.

All numbered results of §2.1–§2.4 except Lemmas 2.16, 2.18, 2.20 and Proposition 2.19 are passed by pointers; the omitted ones are
listed with a reason.

* Corollary to §2.1 (a closed genus-0 surface is `Ĉ`) — omitted: follows from the uniformization pointer of Theorem 2.2
* Lemma 2.1, Theorem 2.2 (the universal covering) — exists: `LiZhongQC.exists_universal_covering`, `LiZhongQC.thm22_2_uniformization`
* Lemma 2.3 (path lifting) — omitted: topological background (monodromy), cf. `Lehto1987.thm4_2_1`
* Theorem 2.4 (lifts of maps to universal coverings) — exists: `LiZhongQC.exists_lift`
* Theorem 2.5 (`π₁(R, p₀) ≅` covering group) — exists: `Lehto1987.thm4_2_4`
* Lemma 2.6 (the covering group is transitive on fibres, properly discontinuous, free) — exists: `Lehto1987.thm4_2_3`, `Lehto1987.thm4_2_5`
* Theorem 2.7 (`R̃/Γ ≅ R`) — exists: `Lehto1987.thm4_3_4`
* Lemma 2.8 (automorphism groups of `Ĉ`, `ℂ`, `H`) — exists: `GardinerLakic2000.lemma2_2`
* Lemma 2.9 (fixed points and normal forms of Möbius transformations) — exists: `LiZhongQC.mobius_fixed_points`
* Lemma 2.10 (type of a real Möbius map by its fixed points) — omitted: covered by the normal forms `GardinerLakic2000.para2_8_normal_form_hyp`
* Lemma 2.11 (type via `tr²`) — exists: `LiZhongQC.mobius_classification_trace`
* Theorems 2.12, 2.13, Corollary 2.13, Theorem 2.15 (classification of Riemann surfaces by their universal coverings) — exists:
  `LiZhongQC.thm22_3_classification`
* Lemma 2.14 (`H/Γ` is a Riemann surface for `Γ` free and properly discontinuous) — exists: `Lehto1987.thm4_3_2`
* Lemma 2.16 (Fuchsian iff no convergent sequence of distinct elements) — `lem2_16`
* Theorem 2.17 (Fuchsian iff properly discontinuous) — exists: `GardinerLakic2000.prop2_4`
* Lemma 2.18 (limits of automorphisms of `H`) — `lem2_18`
* Proposition 2.19 (orbits accumulate at every point of `ℝ̂`) — `fixSet`, `prop2_19`
* Lemma 2.20 (fixed point sets of a hyperbolic element and another element) — `lem2_20`
* Lemma 2.21 (Shimizu's lemma) — exists: `GardinerLakic2000.lemma10_1_a`
* Theorem 2.22 (a closed-surface group consists of the identity and hyperbolic elements) — exists: `LiZhongQC.cocompact_elements_hyperbolic`

Readings: Lemma 2.16 is stated in `SL(2, ℝ)`: `Γ` is a discrete subgroup of `SL(2, ℝ)` iff no sequence of distinct elements of `Γ`
converges in `SL(2, ℝ)`; for `Aut(H) = PSL(2, ℝ)` the same holds for the images (elements are distinct mod `±1` if their images are, and
`±γ_n → γ` is convergence in the quotient). In Lemma 2.18 `f` is the limit of the Möbius maps `γ_n` in the spherical metric
(`LehtoVirtanen1973.sphericalDist`), locally uniformly on `ℍ`.
-/

open Complex Set Metric Filter Topology
open scoped ComplexConjugate MatrixGroups

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (ExtPlane extInf toExt realLine mobiusSL IsFuchsian ActsFreely IsCocompact IsHyperbolic)
open LehtoVirtanen1973 (sphericalDist)

/-- The real Möbius transformation `z ↦ (a z + b)/(c z + d)` of an element of `SL(2, ℝ)`, as a map of the extended plane. -/
def mobiusR (γ : SL(2, ℝ)) : ExtPlane → ExtPlane :=
  mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ)

/-- The extended real line `ℝ̂ = ℝ ∪ {∞}`. -/
def realHat : Set ExtPlane := toExt realLine ∪ {extInf}

/-- **The fixed point set** `Fix(γ) ⊆ ℝ̂` of a real Möbius transformation (IT1:1097, Lemma 2.9). -/
def fixSet (γ : SL(2, ℝ)) : Set ExtPlane := {x ∈ realHat | mobiusR γ x = x}

/-- **Lemma 2.16** (Ch. 2 §2.4.3, IT1:1296). For a subgroup `Γ` of `Aut(H)` the following are equivalent: (i) `Γ` is a Fuchsian
group (discrete); (ii) there exist no sequences of mutually distinct elements of `Γ` which converge in `Aut(H)`. -/
theorem lem2_16 (Γ : Subgroup SL(2, ℝ)) :
    DiscreteTopology Γ ↔ ¬ ∃ (γs : ℕ → SL(2, ℝ)) (γ : SL(2, ℝ)), (∀ n, γs n ∈ Γ) ∧ Function.Injective γs ∧
      Tendsto γs atTop (𝓝 γ) := by
  sorry

/-- **Lemma 2.18** (Ch. 2 §2.4.3, IT1:1318). Let `{γ_n}` be a sequence of `Aut(H)` which converges uniformly on compact subsets of `H`
to a function `f` (a holomorphic function; it may be the constant `∞`). Then either (i) `f` is an element of `Aut(H)`, or
(ii) `f` is a constant function `c` with `c ∈ ℝ̂`. Modelling: convergence in the spherical metric on compact subsets of `ℍ`; `f`
takes values in `ℂ̂`. -/
theorem lem2_18 {γs : ℕ → SL(2, ℝ)} {f : UpperHalfPlane → ExtPlane}
    (hconv : ∀ C : Set UpperHalfPlane, IsCompact C → ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ C,
      sphericalDist (mobiusR (γs n) (z : ℂ)) (f z) < ε) :
    (∃ γ : SL(2, ℝ), ∀ z : UpperHalfPlane, f z = mobiusR γ (z : ℂ)) ∨ (∃ c ∈ realHat, ∀ z, f z = c) := by
  sorry

/-- **Proposition 2.19** (Ch. 2 §2.4.3, IT1:1326). Let `Γ` be a Fuchsian model of a closed Riemann surface of genus `g ≥ 2`. For an
arbitrary point `ζ ∈ ℝ̂`, there exists a sequence `{γ_n}` of `Γ` such that `{γ_n(z₀)}` converges to `ζ` for any point `z₀ ∈ H`.
Modelling: a Fuchsian model of a closed surface is a Fuchsian group acting freely and cocompactly (as in
`LiZhongQC.eq27_12_d_ne_one`). -/
theorem prop2_19 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hc : IsCocompact Γ) {ζ : ExtPlane}
    (hζ : ζ ∈ realHat) :
    ∃ γs : ℕ → Γ, ∀ z₀ : UpperHalfPlane, Tendsto (fun n => mobiusR (γs n : SL(2, ℝ)) (z₀ : ℂ)) atTop (𝓝 ζ) := by
  sorry

/-- **Lemma 2.20** (Ch. 2 §2.4.4, IT1:1336). Let `γ` and `δ` be two elements of a Fuchsian group `Γ`. If `γ` is hyperbolic and
`δ ≠ id`, then one of the following holds: (i) `Fix(γ) = Fix(δ)`; (ii) `Fix(γ) ∩ Fix(δ) = ∅`. -/
theorem lem2_20 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) {γ δ : SL(2, ℝ)} (hγ : γ ∈ Γ) (hδ : δ ∈ Γ)
    (hh : IsHyperbolic γ) (hδ1 : δ ≠ 1 ∧ δ ≠ -1) : fixSet γ = fixSet δ ∨ fixSet γ ∩ fixSet δ = ∅ := by
  sorry

end ImayoshiTaniguchi1992
