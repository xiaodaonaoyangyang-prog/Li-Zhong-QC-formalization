import References.GarnettMarshall2005.Ch03.S05_WienerSolution

/-!
# Garnett–Marshall, Chapter III §6: Regular points

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. III §6 (pp. 93–97;
`full.md` P1:4205–4430).

Conventions as in §5. The standing assumption of the section is `Cap(ℂ* \ Ω) > 0` (P1:4207), under which the Wiener
solution `u_f` (`wienerSolution`) and harmonic measure (`harmonicMeasureWiener`) are defined; every statement carries
it where the book does, or says why it is implied or not needed. A regular point is defined literally by (6.1) (leader
ruling B6); an irregular point is a point of `∂Ω` that is not regular (`¬ IsRegularPoint Ω ζ`, no separate name).
Discs `B(ζ, r)` and `{|z − ζ| < ρ}` are euclidean, so statements that use them take `ζ` finite (a boundary point `∞`
is moved to a finite point by a Möbius transformation in the book's arguments). Simply connected domains of `ℂ*` are
`LehtoVirtanen1973.IsSimplyConnectedDomain` (complement in `ℂ*` connected). Green's function `g_Ω` is
`greenFunctionLim` (1.7), `U_{μ_E}` and `γ(E)` are `logPotential (equilibriumMeasure E)` and `robinConstant E`.

* Definition (regular point: (6.1) holds for all `f ∈ C(∂Ω)`; irregular point: a point of `∂Ω` that is not regular,
  §6, P1:4207–4219) — `IsRegularPoint`
* Theorem 6.1 (§6; (6.2), (6.3), (6.4)) — `thm3_6_1`
* Definition (barrier at `ζ`: a harmonic function `V` on `Ω` with `V → 0` at `ζ` and `liminf V > 0` at the other
  points of `∂Ω`, §6, P1:4251–4263) — omitted: defined in running text together with the remark that multiples of a
  barrier satisfy (6.2)–(6.4); no statement or later proof uses the notion (leader ruling B6)
* Corollary 6.2 (§6) — `cor3_6_2_a`, `cor3_6_2_b`
* Theorem 6.3 (§6; (6.6), (6.7), (6.8)) — `thm3_6_3`
* Corollary 6.4 (Kellogg's theorem, §6) — `cor3_6_4`
* Corollary 6.5 (§6) — `cor3_6_5`

Not stated (inventory U−): the reformulation "equivalently, `ω(z, ·, Ω) → δ_ζ` weak-star as `Ω ∋ z → ζ`"
(P1:4213–4217, not cited); "if `∂Ω` consists of finitely many Jordan curves, then by Chapter II every boundary point is
regular" (P1:4219, which rests on Exercise II.4; it is also contained in Corollary 6.2) and the example `𝔻 \ {0}`, whose
boundary point `0` is irregular (P1:4219–4231, an example; see Exercise 6); "the regularity of `ζ` is a local question"
(P1:4321, a reading of Theorem 6.1; later proofs cite Theorem 6.1 itself); the set of irregular points is a Borel set
(P1:4429, a step of the proof of Corollary 6.5). (6.5) and (6.9)–(6.11) are steps of the proofs of Theorems 6.1 and
6.3.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt extInf)
open References (IsDomainExt finitePart)
open LehtoVirtanen1973 (IsSimplyConnectedDomain)
open InnerProductSpace (HarmonicOnNhd)

/-- **Definition** (regular point, (6.1); irregular point; Ch. III §6, P1:4207–4219). Assume `Cap(ℂ* \ Ω) > 0`, let
`ζ ∈ ∂Ω` and let `f ∈ C(∂Ω)`. The point `ζ ∈ ∂Ω` is a regular point for `Ω` if (6.1) `lim_{Ω∋z→ζ} u_f(z) = f(ζ)` for
all `f ∈ C(∂Ω)`. A point `ζ ∈ ∂Ω` not regular is called an irregular point.
Modelling (leader ruling B6): literally (6.1), with the Wiener solution `wienerSolution` of §5, `f : ℂ* → ℝ` continuous
on `∂Ω`, and the limit along `𝓝[Ω] ζ` in `ℂ*` (`ζ = ∞` allowed); "irregular" is `ζ ∈ ∂Ω ∧ ¬ IsRegularPoint Ω ζ`. The
predicate is read only at points `ζ ∈ ∂Ω` and under the standing assumption `Cap(ℂ* \ Ω) > 0`, where `u_f` is Wiener's
solution; every statement assumes both, or does not depend on the predicate outside them (Corollary 6.4). Off `∂Ω`
the value is not the book's notion and is never read: for `ζ ∉ Ω̄` the filter `𝓝[Ω] ζ` is `⊥` and the predicate
holds vacuously; for `ζ ∈ Ω` it fails (take `f = 0` on `∂Ω` and `f ζ = 1`). -/
def IsRegularPoint (Ω : Set ExtPlane) (ζ : ExtPlane) : Prop :=
  ∀ f : ExtPlane → ℝ, ContinuousOn f (frontier Ω) → Tendsto (wienerSolution Ω f) (𝓝[Ω] ζ) (𝓝 (f ζ))

/-- **Theorem 6.1** (Ch. III §6; cited at P1:4321, 4353, 4411, 4495, and in Exercise 9, P1:5340). The point
`ζ ∈ ∂Ω` is a regular point for `Ω` if and only if there is `ρ > 0` such that for every `ε > 0` there exists a function
`V_ε`, harmonic in `Ω ∩ {z : |z − ζ| < ρ}`, satisfying (6.2) `V_ε(z) ≥ 0`, (6.3) `limsup_{z→ζ} V_ε(z) ≤ ε`, and
(6.4) `V_ε(z) > 1/2` on `{z : ε < |z − ζ| ≤ ρ} ∩ Ω`.
Modelling: `Ω` a domain of `ℂ*` with `Cap(ℂ* \ Ω) > 0` (the standing assumption of §6); `ζ` a finite point (the discs
are euclidean); `V_ε : ℂ → ℝ` harmonic on the plane open set `Ω ∩ B(ζ, ρ)`; (6.2) on that set; (6.3) in `ε`-form along
`z → ζ`, `z ∈ Ω` (the Part A convention for real `limsup`); (6.4) literally, including the circle `|z − ζ| = ρ`, where
`V_ε` is defined but need not be harmonic (in the book's proof `V_ε = u_f` is defined on all of `Ω`). The constants
were checked against the equation images. -/
theorem thm3_6_1 {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) (hcap : 0 < capacity (finitePart Ωᶜ)) {ζ : ℂ}
    (hζ : (ζ : ExtPlane) ∈ frontier Ω) :
    IsRegularPoint Ω ζ ↔ ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ∃ V : ℂ → ℝ,
      HarmonicOnNhd V (finitePart Ω ∩ ball ζ ρ) ∧ (∀ z ∈ finitePart Ω ∩ ball ζ ρ, 0 ≤ V z) ∧
      (∀ η : ℝ, 0 < η → ∀ᶠ z in 𝓝[finitePart Ω] ζ, V z ≤ ε + η) ∧
      ∀ z ∈ finitePart Ω, ε < ‖z - ζ‖ → ‖z - ζ‖ ≤ ρ → 1 / 2 < V z := by
  sorry

/-- **Corollary 6.2** (Ch. III §6; cited at P1:4387 in the proof of Theorem 6.3), first part. Let `ζ ∈ ∂Ω`. If the
connected component of `∂Ω` containing `ζ` consists of more than one point, then `ζ` is a regular point for `Ω`.
Modelling: `Ω` a domain of `ℂ*` with `Cap(ℂ* \ Ω) > 0` (the standing assumption of §6; it also follows from the
hypothesis, since `ℂ* \ Ω` then contains a continuum with more than one point); `ζ ∈ ℂ*`; the component is taken in
`∂Ω ⊆ ℂ*`. -/
theorem cor3_6_2_a {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) (hcap : 0 < capacity (finitePart Ωᶜ)) {ζ : ExtPlane}
    (hζ : ζ ∈ frontier Ω) (hcomp : (connectedComponentIn (frontier Ω) ζ).Nontrivial) : IsRegularPoint Ω ζ := by
  sorry

/-- **Corollary 6.2** (Ch. III §6), second part. In particular, if `Ω` is simply connected, then every point of `∂Ω`
is a regular point.
Modelling: `Ω` a simply connected domain of `ℂ*` (`LehtoVirtanen1973.IsSimplyConnectedDomain`); `Cap(ℂ* \ Ω) > 0` is
the standing assumption of §6 (P1:4207), and it is needed: it excludes `Ω = ℂ*` minus a point, whose one boundary
point is a one-point component and for which the Wiener solution is not defined (P1:4120). -/
theorem cor3_6_2_b {Ω : Set ExtPlane} (hΩ : IsSimplyConnectedDomain Ω) (hcap : 0 < capacity (finitePart Ωᶜ)) :
    ∀ ζ ∈ frontier Ω, IsRegularPoint Ω ζ := by
  sorry

/-- **Theorem 6.3** (Ch. III §6; cited at P1:4419, and (6.8) at P1:4429). Assume `E = ℂ* \ Ω` is a compact plane set
with `Cap(E) > 0` and let `μ_E` be the equilibrium distribution for `E`. Then for `ζ ∈ ∂Ω` the following conditions
are equivalent: (6.6) `ζ` is a regular point; (6.7) `lim_{Ω∋z→ζ} g_Ω(z, ∞) = 0`; (6.8) `U_{μ_E}(ζ) = γ(E)`.
Modelling: `Ω = (toExt E)ᶜ` is a domain of `ℂ*` (the book's `Ω` is a domain) containing `∞`; `ζ ∈ ∂Ω ⊆ E` is a
finite point; `g_Ω(·, ∞)` is `greenFunctionLim` (1.7) (`Cap(E) > 0`, and `z → ζ` stays away from the pole `∞`);
`U_{μ_E}(ζ)` and `γ(E)` are compared in `[−∞, +∞]`; `Cap` is `capacity` (4.8). -/
theorem thm3_6_3 {E : Set ℂ} (hE : IsCompact E) (hΩ : IsDomainExt (toExt E)ᶜ) (hcap : 0 < capacity E) {ζ : ℂ}
    (hζ : (ζ : ExtPlane) ∈ frontier (toExt E)ᶜ) :
    List.TFAE [IsRegularPoint (toExt E)ᶜ ζ,
      Tendsto (fun z => greenFunctionLim (toExt E)ᶜ z extInf) (𝓝[(toExt E)ᶜ] (ζ : ExtPlane)) (𝓝 0),
      logPotential (equilibriumMeasure E) ζ = robinConstant E] := by
  sorry

/-- **Corollary 6.4** (Kellogg's theorem; Ch. III §6; cited at P1:4429 and in App. F, P3:4126, "By Kellogg's theorem
`Cap(K) = 0`"). Let `Ω` be any domain in `ℂ*`. Then `Cap({ζ ∈ ∂Ω : ζ is irregular}) = 0`.
Modelling: "any domain" is kept, with no capacity hypothesis: when `Cap(ℂ* \ Ω) = 0`, the set lies in `ℂ* \ Ω` and has
capacity `0` by (4.8) whatever the predicate says there, so no value off the book's discourse is relied on; the
capacity of a subset of `ℂ*` is that of its finite part. The book's other "Kellogg" result, Theorem II.4.3
(`thm2_4_3`), is a different statement. -/
theorem cor3_6_4 {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) :
    capacity (finitePart {ζ ∈ frontier Ω | ¬ IsRegularPoint Ω ζ}) = 0 := by
  sorry

/-- **Corollary 6.5** (Ch. III §6; cited at P1:4640). Let `Ω` be any domain in `ℂ*` with `Cap(ℂ* \ Ω) > 0`. Then
`ω(z, {ζ ∈ ∂Ω : ζ is irregular}, Ω) = 0` for all `z ∈ Ω`.
Modelling: `ω` is Wiener's harmonic measure (§5); the measure of the set is its outer measure (the proof shows, by
(6.8), that the set is Borel), so no measurability hypothesis is needed. -/
theorem cor3_6_5 {Ω : Set ExtPlane} (hΩ : IsDomainExt Ω) (hcap : 0 < capacity (finitePart Ωᶜ)) :
    ∀ z ∈ Ω, harmonicMeasureWiener Ω z {ζ ∈ frontier Ω | ¬ IsRegularPoint Ω ζ} = 0 := by
  sorry

end GarnettMarshall2005
