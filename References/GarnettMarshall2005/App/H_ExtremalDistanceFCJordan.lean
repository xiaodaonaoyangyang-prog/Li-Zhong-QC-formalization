import References.GarnettMarshall2005.Ch05.S03_ReducedExtremalDistance
import References.GarnettMarshall2005.App.C_DirichletPrinciple
import LiZhongQC.Lemmas.Umlaufsatz

/-!
# Garnett–Marshall, Appendix H: Extremal distance in finitely connected Jordan domains

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Appendix H (pp. 484–497;
`full.md` P3:4564–4920: the main text to P3:4904, the Notes at P3:4905–4907, Exercises H.1–H.5 at P3:4909–4919).

Conventions. Domains are finitely connected Jordan domains of `ℂ*` (`IsFCJordanDomain`, Ch. II §1); "a finite union
of closed (sub)arcs of `∂Ω`" is Ch. IV §4's `IsFiniteUnionOf` of closed Jordan arcs of `ℂ*` contained in `∂Ω` (at
least one; a whole boundary curve is a union of two), and a triple `(Ω, E, F)` bundles two disjoint such sets
(`IsFCTriple`). As in Chapter IV, extremal distances (`extremalDistGM`, `conjExtremalDistGM`, `joiningFamily`,
`IsExtremalMetricGM`) are taken on finite parts; "the extremal metrics are the constant multiples of `ρ₀`" is stated
as two claims: every `c ρ₀` with a real `c > 0` is extremal, and every extremal metric equals some such `c ρ₀`
almost everywhere on `Ω` (never an a.e. equivalence). The function `ω` of (H.1)–(H.3), "the harmonic measure of
`F_d` in the Riemann surface double `Ω_d`" (P3:4568, 4622), is `IsDoubleHarmonicMeasure` (leader ruling Fb1): the double
is encoded by App. B's charts (P3:2730) with even reflection (`HasEvenReflectionAt`). The Dirichlet integral
`D(u) = ∬_Ω |∇u|²` is App. C's `dirichletIntegralGM` on the finite part of `Ω`, applied to the planar function
`z ↦ u(z)`, and `|∇u|` is `‖fderiv ℝ u z‖ₑ`. The digression in the proof of Theorem H.1 (P3:4662–4715) works in a
bounded plane domain `W` whose boundary curves are the project's corner loops (`LiZhongQC.b2_IsCornerLoop`, leader
ruling Fb2), positively oriented (`IsPosBoundaryFC`); the interior angle at the vertex `k` of the loop `c` is
`π − LiZhongQC.b2_extAngle c k`, and `π` at every other boundary point; cusps are excluded [reading]: at a cusp
"`arg dz/ds` increases by `±π`" does not fix `θ₀ ∈ {0, 2π}`, and every use in the book has `θ ∈ {π/2, π, π/k}`.
"Meromorphic" is Mathlib's `MeromorphicNFOn` (leader ruling C5), and `N_z − N_p` is the sum of Mathlib's divisor. In
Theorems H.7 and H.8 `ω(z₀, E) = ω(z₀, E, Ω)` is the finitely connected harmonic measure `harmonicMeasureFC` (the
explicit setting, leader rulings D1/B5, Fb4), read as a real number where real arithmetic with `exp` follows. Robin's
constant `γ` is Ch. III (4.8)'s `robinConstant` (leader ruling B1), and `δ_Ω(z₀, E)` is Ch. V §3's
`reducedExtremalDist` (leader ruling C1).

* Definition (triple `(Ω, E, F)`, App. H, P3:4568) — `IsFCTriple`
* Unlabelled (App. H, P3:4568–4580; the one-component case of Theorem IV.4.1): if `E ∪ F` lies in one component
  `Γ₁` of `∂Ω`, there is a conformal map of `Ω` onto a rectangle with horizontal line segments removed so that `E`
  and `F` correspond to the vertical ends if and only if there is a subarc `σ ⊂ Γ₁` with `E ⊂ σ` and `F ∩ σ = ∅` —
  `fc_slitRectangleMap_iff`
* Definition (the mixed Dirichlet–Neumann problem (H.1)–(H.3) and its solution `ω`, the harmonic measure of `F_d` in
  the double `Ω_d`, App. H, P3:4568, 4584–4598, 4622) — `IsDoubleHarmonicMeasure`, `HasEvenReflectionAt` (helper)
* Theorem H.1 (App. H) — `thmH_1_a`, `thmH_1_b`, `thmH_1_c`, `thmH_1_d`
* Corollary H.2 (App. H; (H.4)) — `corH_2`
* Definition (critical point of order `k − 1`, (H.5), in the proof of Theorem H.1, P3:4624–4630) — `criticalOrder`
* Definition (interior angle `θ₀ ∈ [0, 2π]` of `∂W` at `ζ₀`: `arg dz/ds` increases by `π − θ₀`, App. H, P3:4662) —
  exists: `LiZhongQC.b2_extAngle` (the turning at the vertex k of a corner loop c, the principal argument of the
  outgoing over the incoming tangent, in (−π, π); the interior angle is π minus it, a renaming by θ ↦ π − θ; cusps
  are excluded, as in the module conventions)
* Definition (principal value integral `PV ∫_{∂W} g(z) dz = lim_{ε→0} ∫_{∂W_ε ∩ ∂W} g(z) dz`, App. H,
  P3:4662–4668) — `HasBoundaryPVIntegral`, `boundaryTruncatedIntegral` (helper)
* Formula (H.9) (App. H, P3:4668–4672; the total turning of the tangent of ∂W) — omitted: a step of the proof of
  Theorem H.1, cited only by the proofs of Theorem H.1 (P3:4724) and Proposition H.4 (P3:4778) in the same appendix;
  its case of one boundary curve is the project's Umlaufsatz LiZhongQC.b2_umlaufsatz
* Definition (singularity of order `α₀` at `ζ₀ ∈ ∂W`, (H.10), App. H, P3:4674–4680) — `HasBoundarySingularityOrder`
* Lemma H.3 (extended argument principle, App. H; (H.11)) — `lemmaH_3`
* Proposition H.4 (App. H; with the counts `N_c`, `N_e`, `N_z`, `N_z^b` of P3:4760–4770) — `propH_4`
* Example H.5 (App. H, P3:4780) — omitted: an example (the disc with two interleaved arcs each in E and F, the three
  possible configurations of critical points, Figure H.2); cited only by Exercise H.4
* Example H.6 (App. H, P3:4783–4788) — omitted: an example (the disc minus two discs, F the outer circle, one
  critical point, two quadrilaterals, Figure H.3); cited only by Exercise H.3
* Theorem H.7 (App. H) — `thmH_7`
* Theorem H.8 (App. H) — `thmH_8`
* Theorem H.9 (App. H) — `thmH_9`
* Formula (H.18) (App. H, P3:4889–4899) — `eqH_18`

Helpers (not book notions): `HasEvenReflectionAt` (App. B's chart of the double at a point of `J = ∂Ω \ (E ∪ F)`
with an even harmonic function in the chart), `IsPosBoundaryFC` (a bounded plane domain positively bounded by
finitely many corner loops), `boundaryTruncatedIntegral` (the integral over `∂W_ε ∩ ∂W`), `arcEndpoints` (the
endpoints of the arcs of `E ∪ F`).

Not stated (inventory U−, remarks, examples and proof steps): the introduction (P3:4566); the proof sketch of the
one-component case (the double, `∫_{Γ_j} ∂ω̃/∂s ds = 0`, `φ = ω + iω̃` single valued) and "the remainder of the
argument is exactly like the proof of Theorem IV.4.1" (P3:4568–4580); the finitely connected version of Theorem IV.4.2
(P3:4580–4582, Exercise H.1); the motivation `ρ₀ = |φ′| = |∇ω|` for analytic Jordan boundaries (P3:4584); "Theorem
H.1 also implies Corollary C.4 of Appendix C" (P3:4612, a remark); "this proof only needs `v ∈ C(Ω)` to be piecewise
`C¹`" (P3:4620); the proof of Theorem H.1 (the slit-rectangle picture, the critical values, "we can assume `∂Ω`
consists of analytic Jordan curves" by Corollary II.4.6, "by the Schwarz reflection principle `ω` is the only solution
to (H.1)–(H.3)" for analytic boundaries (the `C^{1+ε}` form is Theorem H.1(c)), the level curves of `ω̃`, (H.6)–(H.8),
Figure H.1, the proof of Lemma H.3 with (H.12), (H.13), then (H.14), (H.15), the endpoint cases (i)–(iii),
`2π(N_j − 2) + (π/2)K_j = 0` and the length–area argument, P3:4622–4756); the remark "if `f(z) ∼ (z − ζ₀)^{α₀}` then
`f` has a singularity of order `α₀`" (P3:4680); the example after Lemma H.3 for smooth `∂W` (P3:4690–4694, not cited);
the remark that `φ` maps onto a Riemann surface of rectangles (P3:4758); the proof of Proposition H.4 (P3:4778); the
announcement of Theorem H.7 (P3:4790); the remarks after Theorem H.7 ("`σ ∩ Ω` need not be connected", the proof
sketch through `z ↦ z²` and `Ω₁`, "Theorem H.7 also yields a more general version of Theorem IV.6.1", P3:4798); the
proof of Theorem H.8 (P3:4807–4821); the consequence `Cap(∂Ω) ≤ R e^{−2π d_Ω(C_R, ∂Ω)}` and the remarks after Theorem
H.9 (P3:4835–4843, not cited; the monotonicity is Ch. V's (3.1)); the proof of Theorem H.9 ((H.16), the expansion of
Green's function recalled from Ch. III, and (H.17), P3:4845–4887); around (H.18) the analogy sentence, the formula
`−log |f| = g_{Ω_d}(z, z₀′) + g_{Ω_d}(z, z₀″)` and "the radial slits do not affect `d_𝔻(C_R, ∂𝔻)`" (P3:4889–4897);
the remarks P3:4901–4903 (Theorem V.3.2 by (H.18); the analogue of Theorem H.1 for reduced extremal distance is
Exercise V.2). The Notes (P3:4905–4907) and Exercises H.1–H.5 are not items; Exercise H.5 has no part (a) (App. C,
P3:3177, cites "Exercise H.5(a)", recorded in App. C). OCR: Theorems H.7 and H.8 print `z` for `z₀` ("connecting `z`
to `Γ₁ \ E`", "separates `z` from `E`"); Lemma H.3 prints "`_{Iff}` is meromorphic" for "If `f` is meromorphic"; at
P3:4889 "the proof of Theorem V.3" is Theorem V.3.2.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References ComplexConjugate

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt extInf unitDisc b2_IsCornerLoop b2_IsAngleFn b2_extAngle)
open LehtoVirtanen1973 (IsJordanArc IsClosedJordanArc IsConformalMap IsArcFromTo)
open References (finitePart)
open InnerProductSpace (HarmonicOnNhd)

/-- **Definition** (triple, App. H, P3:4568; used in Theorem H.1, Corollary H.2 and Proposition H.4). Assume `Ω` is a
finitely connected Jordan domain, let `E` and `F` be finite unions of closed arcs on `∂Ω`, and assume `E ∩ F = ∅`. In
that case we call `(Ω, E, F)` a triple.
Modelling: Ch. IV §4's `IsFiniteUnionOf` of closed Jordan arcs of `ℂ*` contained in `∂Ω` (at least one, so `E` and
`F` are nonempty; a whole boundary curve is a union of two closed arcs). Theorem H.1's "disjoint closed subsets of
`∂Ω`, each consisting of finitely many subarcs of `∂Ω`" is the same notion. -/
def IsFCTriple (Ω E F : Set ExtPlane) : Prop :=
  IsFCJordanDomain Ω ∧ IsFiniteUnionOf (fun s => IsClosedJordanArc s ∧ s ⊆ frontier Ω) E ∧
    IsFiniteUnionOf (fun s => IsClosedJordanArc s ∧ s ⊆ frontier Ω) F ∧ Disjoint E F

/-- **Unlabelled** (App. H, P3:4568–4580; cited in the proof of Theorem H.7, P3:4798, "using a conformal map of `Ω₁`
onto a rectangle with horizontal line segments removed, as in the discussion in the first paragraph of this
appendix"). Let `(Ω, E, F)` be a triple and suppose there is one component `Γ₁` of `∂Ω` such that `E ∪ F ⊂ Γ₁`.
Then there is a conformal mapping of `Ω` onto a rectangle with horizontal line segments removed so that `E` and `F`
correspond to the vertical ends of the rectangle if and only if there is a subarc `σ ⊂ Γ₁` such that `E ⊂ σ` and
`F ∩ σ = ∅`.
Modelling: `Γ₁` is the component of `∂Ω` through a point `q ∈ ∂Ω`; the map is Ch. IV §4's `IsSlitRectangleMap`
(conformal onto the slit rectangle, continuous on `Ω̄`, `E` and `F` onto the vertical sides in either order; its
definition does not ask `Ω` to be a Jordan domain, and the other boundary curves of `Ω` go to slits traced twice, as
the book says at P3:4622); `σ` is a Jordan arc of `ℂ*` (any kind of parameter interval), as in Theorem IV.4.1
(`thm4_4_1_a`, the Jordan-domain case). -/
theorem fc_slitRectangleMap_iff {Ω E F : Set ExtPlane} (h : IsFCTriple Ω E F) {q : ExtPlane}
    (hq : q ∈ frontier Ω) (hEF : E ∪ F ⊆ connectedComponentIn (frontier Ω) q) :
    (∃ (φ : ExtPlane → ExtPlane) (x₁ x₂ y₁ y₂ : ℝ) (n : ℕ) (L : Fin n → Set ℂ),
        IsSlitRectangleMap Ω E F φ x₁ x₂ y₁ y₂ L) ↔
      ∃ σ : Set ExtPlane, IsJordanArc σ ∧ σ ⊆ connectedComponentIn (frontier Ω) q ∧ E ⊆ σ ∧ Disjoint F σ := by
  sorry

/-- App. B's chart of the double at a point of `J` with an even harmonic function (helper, App. H, P3:4568, 4622; App.
B, P3:2730): there are an open neighbourhood `W` of `p` with `W ∩ ∂Ω ⊆ J` and a conformal map `ψ` of `W ∩ Ω` onto
the half-disc `𝔻₊ = 𝔻 ∩ {Im z > 0}` whose continuous extension maps `W ∩ ∂Ω` onto `(−1, 1)`, and a harmonic function
`v` on `𝔻` with `v(z̄) = v(z)` such that `u = v ∘ ψ` on `W ∩ Ω`.
Modelling: App. B's basic neighbourhood of `p ∈ J` in `Ω_d` is the full disc, `W ∩ Ω` in the chart `ψ` and its
companion in the chart `z ↦ conj (ψ z)`; `u` is the restriction to `Ω` of a function harmonic on this neighbourhood and
symmetric under the swap of the copies exactly when such a `v` exists. `ψ` is LV's conformal map, with finite values
on `W ∩ Ω` (its image is a plane set). -/
def HasEvenReflectionAt (Ω J : Set ExtPlane) (u : ExtPlane → ℝ) (p : ExtPlane) : Prop :=
  ∃ (W : Set ExtPlane) (ψ : ExtPlane → ExtPlane), IsOpen W ∧ p ∈ W ∧ W ∩ frontier Ω ⊆ J ∧
    IsConformalMap ψ (W ∩ Ω) ∧ ψ '' (W ∩ Ω) = toExt (unitDisc ∩ {z : ℂ | 0 < z.im}) ∧
    ContinuousOn ψ (W ∩ closure Ω) ∧ ψ '' (W ∩ frontier Ω) = toExt ((fun t : ℝ => (t : ℂ)) '' Ioo (-1) 1) ∧
    ∃ v : ℂ → ℝ, HarmonicOnNhd v unitDisc ∧ (∀ z, v (conj z) = v z) ∧
      ∀ z ∈ W ∩ Ω, ∀ x : ℂ, ψ z = x → u z = v x

/-- **Definition** (the solution `ω` of the mixed Dirichlet–Neumann problem (H.1)–(H.3), "the harmonic measure of
`F_d` in `Ω_d`", App. H, P3:4568, 4584–4598, 4622; used in Theorem H.1, Corollary H.2 and Proposition H.4). The
problem is (H.1) `Δω(z) = 0`, `z ∈ Ω`; (H.2) `ω(z) = 0`, `z ∈ E`, and `ω(z) = 1`, `z ∈ F`; (H.3) `∂ω(z)/∂n = 0`,
`z ∈ ∂Ω \ (E ∪ F)`. If `∂Ω \ (E ∪ F) ≠ ∅`, take two copies of `Ω` joined along `∂Ω \ (E ∪ F)`, forming the Riemann
surface double `Ω_d`, and let `F_d` consist of those boundary curves of `∂Ω_d` corresponding to `F`. If
`∂Ω \ (E ∪ F) = ∅`, let `Ω_d = Ω` and `F_d = F`. Let `ω(z)` be the harmonic measure of `F_d` in `Ω_d`; we work with
the restriction of `ω(z)` to `Ω`.
Modelling (leader ruling Fb1): `ω` is harmonic on `Ω`, continuous on `Ω̄`, `0` on `E` and `1` on `F`, and at every
point of `J = ∂Ω \ (E ∪ F)` it extends across `J` to the double by even reflection in App. B's charts
(`HasEvenReflectionAt`); this is exactly the restriction to `Ω` of the harmonic function on `Ω_d` with the boundary
values `1` on `F_d` and `0` on the rest of `∂Ω_d`, which is symmetric under the swap of the copies. For
`E ∪ F = ∂Ω` the last condition is vacuous and `ω` is the solution of the Dirichlet problem, the book's `Ω_d = Ω`.
(H.1)–(H.3) were checked against the equation images; (H.3) holds for `C^{1+ε}` boundaries (Theorem H.1(c)). -/
def IsDoubleHarmonicMeasure (Ω E F : Set ExtPlane) (ω : ExtPlane → ℝ) : Prop :=
  HarmonicOnExt ω Ω ∧ ContinuousOn ω (closure Ω) ∧ (∀ ζ ∈ E, ω ζ = 0) ∧ (∀ ζ ∈ F, ω ζ = 1) ∧
    ∀ p ∈ frontier Ω \ (E ∪ F), HasEvenReflectionAt Ω (frontier Ω \ (E ∪ F)) ω p

/-- **Theorem H.1** (App. H; cited at P3:4612, 4614–4620, 4760, 4825, 4869, 4903, in the Notes P3:4907, in Ch. IV,
P1:5944, and in App. C, P3:3157), the extremal distance. Suppose `Ω` is a finitely connected Jordan domain and suppose
`E` and `F` are disjoint closed subsets of `∂Ω`, each consisting of finitely many subarcs of `∂Ω`. Then the extremal
distance between `E` and `F` is given by `d_Ω(E, F)^{−1} = D(ω) ≡ ∬_Ω |∇ω|² dx dy`, where `ω` is a solution to (H.1)
and (H.2).
Modelling: `(Ω, E, F)` is a triple; `d_Ω(E, F)` is `extremalDistGM` on finite parts and `D` is App. C's
`dirichletIntegralGM` on the finite part of `Ω`; the existence of `ω`, which the book presupposes, is stated.
[reading] (leader ruling Fb1) "`ω` is a solution to (H.1) and (H.2)" is the book's `ω`, the harmonic measure of the
double (`IsDoubleHarmonicMeasure`; P3:4568, 4622 define it so). The literal reading "any solution of (H.1), (H.2)" is
false as soon as `J = ∂Ω \ (E ∪ F) ≠ ∅`: for `Ω = 𝔻` and disjoint closed arcs `E`, `F` of `∂𝔻`, the Poisson harmonic
measure `u(z) = ω(z, F, 𝔻)` is harmonic, `0` on `E` and `1` on `F`, but near an endpoint `b` of `F` adjacent to `J`
it is `u ≈ θ/π` in polar coordinates `(r, θ)` at `b`, so `|∇u| ≈ 1/(πr)` and `D(u) ≥ c ∫∫ r^{−2} r dr dθ = ∞`, while
`d_𝔻(E, F)^{−1} < ∞`. The displayed formula was checked against the equation image. -/
theorem thmH_1_a {Ω E F : Set ExtPlane} (h : IsFCTriple Ω E F) :
    (∃ ω : ExtPlane → ℝ, IsDoubleHarmonicMeasure Ω E F ω) ∧
      ∀ ω : ExtPlane → ℝ, IsDoubleHarmonicMeasure Ω E F ω →
        (extremalDistGM (finitePart Ω) (finitePart E) (finitePart F))⁻¹ =
          dirichletIntegralGM (finitePart Ω) (fun z : ℂ => ω (z : ExtPlane)) := by
  sorry

/-- **Theorem H.1** (App. H), the extremal metrics. In the situation of `thmH_1_a`: extremal metrics exist and are
given by constant multiples of `ρ = |∇ω|` a.e. `dx dy`.
Modelling: `ω` is the book's (`IsDoubleHarmonicMeasure`, as in `thmH_1_a`); `|∇ω(z)|` is `‖fderiv ℝ ω z‖ₑ` for the
planar function `z ↦ ω(z)` (a metric: measurable, and `0 < ∬ ρ² = D(ω) = d_Ω(E, F)^{−1} < ∞` by `thmH_1_a`); the
constant multiples are positive; stated as the two claims of the module conventions (every `c |∇ω|`, `c > 0`, is an
extremal metric, which gives the existence; every extremal metric equals some `c |∇ω|` a.e. on `Ω`). -/
theorem thmH_1_b {Ω E F : Set ExtPlane} (h : IsFCTriple Ω E F) {ω : ExtPlane → ℝ}
    (hω : IsDoubleHarmonicMeasure Ω E F ω) :
    (∀ c : ℝ, 0 < c → IsExtremalMetricGM (finitePart Ω) (joiningFamily (finitePart Ω) (finitePart E) (finitePart F))
        (fun z => ENNReal.ofReal c * ‖fderiv ℝ (fun w : ℂ => ω (w : ExtPlane)) z‖ₑ)) ∧
      ∀ ρ : ℂ → ℝ≥0∞, IsExtremalMetricGM (finitePart Ω)
          (joiningFamily (finitePart Ω) (finitePart E) (finitePart F)) ρ →
        ∃ c : ℝ, 0 < c ∧ ρ =ᵐ[volume.restrict (finitePart Ω)]
          fun z => ENNReal.ofReal c * ‖fderiv ℝ (fun w : ℂ => ω (w : ExtPlane)) z‖ₑ := by
  sorry

/-- **Theorem H.1** (App. H), smooth boundaries. In the situation of `thmH_1_a`: if `∂Ω` consists of `C^{1+ε}`
curves then `ω` is the unique solution to (H.1), (H.2), and (H.3).
Modelling: every component of `∂Ω` is a plane curve of class `C^{1+ε}` (Ch. II §4's `IsCurveOfClass 1 ε`), with
`0 < ε < 1`, the range of the class (as in App. B; a curve of class `C^{1+ε}` is of class `C^{1+ε'}` for `ε' < ε`).
"`ω` is the unique solution of (H.1)–(H.3)" is stated as an equivalence for every `u`: `u` solves the classical mixed
problem (harmonic on `Ω`, continuous on `Ω̄`, (H.2), and (H.3) as Ch. II §2's `HasOuterNormalDeriv` with value `0` at
every point of `∂Ω \ (E ∪ F)`, which reads only values of `u` in `Ω`) if and only if `u` is the book's `ω`
(`IsDoubleHarmonicMeasure`). With `thmH_1_a` (existence) this says that `ω` solves the problem and every solution is
`ω`. The continuity on `Ω̄` is required because (H.2) reads `u`'s own values on `∂Ω` (leader ruling Fa2). -/
theorem thmH_1_c {Ω E F : Set ExtPlane} (h : IsFCTriple Ω E F) {ε : ℝ} (hε : 0 < ε) (hε₁ : ε < 1)
    (hC : ∀ q ∈ frontier Ω, ∃ Γ' : Set ℂ, toExt Γ' = connectedComponentIn (frontier Ω) q ∧ IsCurveOfClass 1 ε Γ')
    (u : ExtPlane → ℝ) :
    (HarmonicOnExt u Ω ∧ ContinuousOn u (closure Ω) ∧ (∀ ζ ∈ E, u ζ = 0) ∧ (∀ ζ ∈ F, u ζ = 1) ∧
        ∀ ζ : ℂ, (ζ : ExtPlane) ∈ frontier Ω \ (E ∪ F) → HasOuterNormalDeriv Ω u ζ 0) ↔
      IsDoubleHarmonicMeasure Ω E F u := by
  sorry

/-- **Theorem H.1** (App. H), the conjugate extremal distance. In the situation of `thmH_1_a`: the conjugate extremal
distance satisfies `d*_Ω(E, F) = 1/d_Ω(E, F)`.
Modelling: distances on finite parts; the identity is in `[0, ∞]` and holds for every triple (it does not involve
`ω`). The formula was checked against the equation image. -/
theorem thmH_1_d {Ω E F : Set ExtPlane} (h : IsFCTriple Ω E F) :
    conjExtremalDistGM (finitePart Ω) (finitePart E) (finitePart F) =
      (extremalDistGM (finitePart Ω) (finitePart E) (finitePart F))⁻¹ := by
  sorry

/-- **Corollary H.2** (App. H; cited in the Notes, P3:4907). Suppose `Ω` is a finitely connected Jordan domain and `E`
and `F` are disjoint closed subsets of `∂Ω`, each consisting of finitely many subarcs of `∂Ω`. Then `ω` is the unique
function in `C¹(Ω)` satisfying (H.4) `∫_Ω |∇ω|² dx dy = inf {∫_Ω |∇v|² dx dy : v ∈ C¹(Ω), limsup_{z→ζ∈E} v(z) ≤ 0,
liminf_{z→ζ∈F} v(z) ≥ 1}`.
Modelling: `ω` is the book's (`IsDoubleHarmonicMeasure`, Theorem H.1); the class of (H.4) is named by the hypothesis
`h𝒜`: planar functions `v` that are `C¹` on the finite part of `Ω`, with `limsup ≤ 0` at the points of `E` and
`liminf ≥ 1` at the points of `F` in `ε`-form along `z → ζ`, `z ∈ Ω` (`nhdsExtWithin`, so boundary points at `∞` are
allowed); `∫_Ω |∇v|²` is `dirichletIntegralGM` on the finite part. "`ω` is the unique function satisfying (H.4)" is:
`ω` lies in the class, attains the infimum, and every function of the class with the same Dirichlet integral equals
`ω` on `Ω` (two claims, not an equivalence). B-cand.: App. C's Corollary C.4 (`corC_4_a`: open arcs with disjoint
closures, piecewise smooth competitors). (H.4) was checked against the equation image. -/
theorem corH_2 {Ω E F : Set ExtPlane} (h : IsFCTriple Ω E F) {ω : ExtPlane → ℝ}
    (hω : IsDoubleHarmonicMeasure Ω E F ω) {𝒜 : Set (ℂ → ℝ)}
    (h𝒜 : 𝒜 = {v | ContDiffOn ℝ 1 v (finitePart Ω) ∧
      (∀ ζ ∈ E, ∀ ε > 0, ∀ᶠ z in nhdsExtWithin ζ (finitePart Ω), v z ≤ ε) ∧
      ∀ ζ ∈ F, ∀ ε > 0, ∀ᶠ z in nhdsExtWithin ζ (finitePart Ω), 1 - ε ≤ v z}) :
    (fun z : ℂ => ω (z : ExtPlane)) ∈ 𝒜 ∧
      dirichletIntegralGM (finitePart Ω) (fun z : ℂ => ω (z : ExtPlane)) =
        ⨅ v ∈ 𝒜, dirichletIntegralGM (finitePart Ω) v ∧
      ∀ v ∈ 𝒜, dirichletIntegralGM (finitePart Ω) v =
          dirichletIntegralGM (finitePart Ω) (fun z : ℂ => ω (z : ExtPlane)) →
        EqOn v (fun z : ℂ => ω (z : ExtPlane)) (finitePart Ω) := by
  sorry

/-- **Definition** (critical point of order `k − 1`, (H.5), in the proof of Theorem H.1, P3:4624–4630; used in the
statement of Proposition H.4). For each `ζ ∈ Ω̄ \ P` there is a conformal map `f_ζ` defined in a neighbourhood `U_ζ`
of `ζ` with `f_ζ(ζ) = 0` and a constant `a_ζ` so that (H.5) `ω + iω̃ = a_ζ + f_ζ^k` for some `k ≥ 1`. If `k ≥ 2`, we
call `ζ` a critical point of order `k − 1`.
Modelling (leader ruling Fb3): the order is the vanishing order (`analyticOrderAt`) at `ζ` of the holomorphic function
`φ′ = ω_x − iω_y` (the derivative of `φ = ω + iω̃`, which is `k f_ζ^{k−1} f_ζ′` by (H.5), of order `k − 1`), for a
boundary point `ζ` of its holomorphic extension across `∂Ω`: the infimum over all holomorphic `h` on an open `V ∋ ζ`
that agree with `ω_x − iω_y` on `V ∩ Ω` (for `ζ ∈ Ω̄` all such `h` have the same germ at `ζ`, so the infimum is that
order); `ω_x(z) = fderiv ℝ ω z 1` and `ω_y(z) = fderiv ℝ ω z I` for the planar function `z ↦ ω(z)`. Order `0` is a
regular point, order `k − 1 ≥ 1` a critical point counted `k − 1` times, as Proposition H.4 counts. Junk: `⊤` where no
extension exists (the endpoints `P` of the arcs of `E ∪ F`, never counted) and `0` at points off `Ω̄` (never read);
defined at finite points only. -/
def criticalOrder (Ω : Set ExtPlane) (ω : ExtPlane → ℝ) (ζ : ℂ) : ℕ∞ :=
  ⨅ (h : ℂ → ℂ) (V : Set ℂ) (_ : IsOpen V ∧ ζ ∈ V ∧ AnalyticOnNhd ℂ h V ∧
      ∀ z ∈ V, (z : ExtPlane) ∈ Ω → h z = (fderiv ℝ (fun w : ℂ => ω (w : ExtPlane)) z 1 : ℂ) -
        I * (fderiv ℝ (fun w : ℂ => ω (w : ExtPlane)) z I : ℂ)),
    analyticOrderAt h ζ

/-- A bounded plane domain positively bounded by finitely many corner loops (helper, App. H, P3:4662, 4682): "`W` is a
bounded, finitely connected Jordan domain and each boundary curve is piecewise continuously differentiable; orient
`∂W` so that it has index 1 about each point of `W`". The `j`-th boundary curve is the corner loop `c j` with the
`m j + 1` sides `c j k : [0, 1] → ℂ` (`LiZhongQC.b2_IsCornerLoop`: `C¹` sides with non-vanishing one-sided
derivatives, consecutive sides joined, injective, no cusps); `W` is open, connected and bounded, its boundary is the
union of the traces, the traces of different loops are disjoint, and for every `p ∉ ∂W` the angle changes of
`c j k − p` along all the sides (`LiZhongQC.b2_IsAngleFn`) add up to `2π` if `p ∈ W` and to `0` if `p ∉ W̄`.
Modelling (leader ruling Fb2): the index conditions fix the orientation of every boundary curve (index 1 about the
points of `W` fixes the outer curve, index 0 about the holes fixes the inner ones); each trace is a Jordan curve, so
`W` is a finitely connected Jordan domain; cusps are excluded [reading] (module conventions). -/
def IsPosBoundaryFC (W : Set ℂ) {N : ℕ} {m : Fin N → ℕ} (c : (j : Fin N) → Fin (m j + 1) → ℝ → ℂ) : Prop :=
  IsOpen W ∧ IsConnected W ∧ Bornology.IsBounded W ∧ (∀ j, b2_IsCornerLoop (c j)) ∧
    (Pairwise fun i j => Disjoint (⋃ k, c i k '' Icc 0 1) (⋃ k, c j k '' Icc 0 1)) ∧
    frontier W = ⋃ (j) (k), c j k '' Icc 0 1 ∧
    ∀ p : ℂ, p ∉ frontier W → ∀ L : (j : Fin N) → Fin (m j + 1) → ℝ → ℝ,
      (∀ j k, b2_IsAngleFn (fun t => c j k t - p) 0 1 (L j k)) →
        (p ∈ W → ∑ j, ∑ k, (L j k 1 - L j k 0) = 2 * π) ∧ (p ∉ W → ∑ j, ∑ k, (L j k 1 - L j k 0) = 0)

/-- The integral `∫_{∂W_ε ∩ ∂W} g(z) dz`, `W_ε = W \ ⋃_k {z : |z − ζ_k| ≤ ε}` (helper, App. H, P3:4662–4668): the sum
over the sides `c j k` of the positively oriented boundary of `∫₀¹ g(c(t)) c′(t) dt` restricted to the parameters `t`
with `|c(t) − ζ| > ε` for every `ζ ∈ P`.
Modelling: for `g` continuous on `∂W \ P` (the book's hypothesis) the integrand is bounded and measurable on each side,
since the closure of the truncated set stays at distance `≥ ε` from `P`, so the value is not the interval integral's
junk `0`. -/
def boundaryTruncatedIntegral {N : ℕ} {m : Fin N → ℕ} (c : (j : Fin N) → Fin (m j + 1) → ℝ → ℂ) (P : Set ℂ)
    (g : ℂ → ℂ) (ε : ℝ) : ℂ :=
  ∑ j, ∑ k, ∫ t in (0 : ℝ)..1,
    {t : ℝ | ∀ ζ ∈ P, ε < ‖c j k t - ζ‖}.indicator (fun t => g (c j k t) * deriv (c j k) t) t

/-- **Definition** (principal value integral, App. H, P3:4662–4668; used in (H.9), Lemma H.3 and (H.14)). Let
`F = {ζ_k}_{k=1}^m` be a finite subset of `∂W` and let `W_ε = W \ ⋃_k {z : |z − ζ_k| ≤ ε}`. If `g` is continuous on
`∂W \ F` then we define the principal value integral as `PV ∫_{∂W} g(z) dz = lim_{ε→0} ∫_{∂W_ε ∩ ∂W} g(z) dz`,
provided the limit exists.
Modelling: a predicate "the principal value integral exists and equals `L`" (no `limUnder`), for `W` positively
bounded by the corner loops `c` (`IsPosBoundaryFC`); the book's finite set is `P`. "`PV Im ∫`" in (H.9), (H.11) and
(H.14) is the limit of the imaginary parts of the truncated integrals, which may exist when the complex limit does
not (Lemma H.3 states it so). The formula was checked against the equation image. -/
def HasBoundaryPVIntegral {N : ℕ} {m : Fin N → ℕ} (c : (j : Fin N) → Fin (m j + 1) → ℝ → ℂ) (P : Set ℂ)
    (g : ℂ → ℂ) (L : ℂ) : Prop :=
  Tendsto (boundaryTruncatedIntegral c P g) (𝓝[>] 0) (𝓝 L)

/-- **Definition** (singularity of order `α₀`, (H.10), App. H, P3:4674–4680; used in Lemma H.3 and in the proof of
Theorem H.1). If `f` is meromorphic on `W`, then we say `f` has a singularity at `ζ₀ ∈ ∂W` of order `α₀ ∈ ℝ` if
(H.10) `lim_{W∋z→ζ₀} (f′(z)/f(z) − α₀/(z − ζ₀))` exists.
Modelling: "exists" is a finite limit along `z → ζ₀`, `z ∈ W` (no `limUnder`); the statements carry "meromorphic".
The existence of the limit excludes zeros and poles of `f` accumulating at `ζ₀` (near each of them `f′/f` is
unbounded), so the junk values of `f′/f` at zeros and poles do not affect it. (H.10) was checked against the equation
image. -/
def HasBoundarySingularityOrder (W : Set ℂ) (f : ℂ → ℂ) (ζ₀ : ℂ) (α₀ : ℝ) : Prop :=
  ∃ L : ℂ, Tendsto (fun z => deriv f z / f z - α₀ / (z - ζ₀)) (𝓝[W] ζ₀) (𝓝 L)

/-- **Lemma H.3** (extended argument principle; App. H, in the proof of Theorem H.1; cited at P3:4718–4724 and in the
proof of Proposition H.4, P3:4778). Suppose `W` is a bounded, finitely connected Jordan domain and suppose each boundary
curve in `∂W` is piecewise continuously differentiable. Let `P = {ζ_k}_{k=1}^m ⊂ ∂W` and suppose `∂W` has interior
angle `θ_k` at `ζ_k`, `k = 1, …, m`, and interior angle `π` at all `ζ ∈ ∂W \ P`. If `f` is meromorphic in a
neighbourhood of `W̄ \ P`, having no zeros or poles on `∂W \ P`, and if `f` has a singularity of order `α_k` at `ζ_k`,
`k = 1, …, m`, then (H.11) `PV Im ∫_{∂W} (f′(z)/f(z)) dz/2π = (N_z − N_p) + Σ_{k=1}^m α_k θ_k/2π`, where `N_z` and
`N_p` are the numbers of zeros and poles of `f` in `W`, counting multiplicity.
Modelling: a labelled lemma inside a proof (leader ruling C10), its context the digression's definitions. `W` is
positively bounded by corner loops (`IsPosBoundaryFC`, cusps excluded [reading]); the interior angle at the vertex
`c j k 0` is `π − LiZhongQC.b2_extAngle (c j) k` and `π` elsewhere, so the angle conditions say: every vertex outside
`P` has turning `0`, and each `ζ ∈ P` is a vertex with interior angle `θ ζ` or a non-vertex point with `θ ζ = π`; the
indexed families `θ_k`, `α_k` are functions of the point. "Meromorphic in a neighbourhood of `W̄ \ P`" is
`MeromorphicNFOn f U` on an open `U ⊇ W̄ \ P` (leader ruling C5); "no zeros or poles on `∂W \ P`" is: `f` is analytic
and non-zero there. `N_z − N_p` is the finite sum over `W` of Mathlib's divisor of `f` on `U` (its support in `W` is
finite: the zeros and poles do not accumulate at `∂W \ P`, and (H.10) excludes accumulation at `P`). `PV Im ∫` is the
limit of the imaginary parts of the truncated integrals (`boundaryTruncatedIntegral`). No candidate: Mathlib's argument
principle is for circles, and the project's winding facts LiZhongQC.b2_wind_in, LiZhongQC.b2_bwa concern one loop.
(H.11) was checked against the equation image. -/
theorem lemmaH_3 {W : Set ℂ} {N : ℕ} {m : Fin N → ℕ} {c : (j : Fin N) → Fin (m j + 1) → ℝ → ℂ}
    (hW : IsPosBoundaryFC W c) {P : Finset ℂ} (hP : (P : Set ℂ) ⊆ frontier W) {θ α : ℂ → ℝ}
    (hvert : ∀ j k, c j k 0 ∉ P → b2_extAngle (c j) k = 0)
    (hθ : ∀ ζ ∈ P, (∃ j k, c j k 0 = ζ ∧ π - b2_extAngle (c j) k = θ ζ) ∨ ((∀ j k, c j k 0 ≠ ζ) ∧ θ ζ = π))
    {U : Set ℂ} (hU : IsOpen U) (hWU : closure W \ P ⊆ U) {f : ℂ → ℂ} (hf : MeromorphicNFOn f U)
    (hfb : ∀ z ∈ frontier W \ P, AnalyticAt ℂ f z ∧ f z ≠ 0)
    (hα : ∀ ζ ∈ P, HasBoundarySingularityOrder W f ζ (α ζ)) :
    Tendsto (fun ε => (boundaryTruncatedIntegral c P (fun z => deriv f z / f z) ε).im / (2 * π)) (𝓝[>] 0)
      (𝓝 ((∑ᶠ z ∈ W, (MeromorphicOn.divisor f U z : ℝ)) + ∑ ζ ∈ P, α ζ * θ ζ / (2 * π))) := by
  sorry

/-- The endpoints of the arcs of `E ∪ F` (helper, App. H, P3:4584 "`P` is the set of endpoints of the arcs in
`E ∪ F`", P3:4766): the points of `E ∪ F` in the closure of `∂Ω \ (E ∪ F)`.
Modelling: the topological endpoints relative to `∂Ω` (overlapping or abutting arcs of `E` do not add endpoints); a
whole boundary curve contained in `E ∪ F` contributes none. -/
def arcEndpoints (Ω E F : Set ExtPlane) : Set ExtPlane :=
  (E ∪ F) ∩ closure (frontier Ω \ (E ∪ F))

/-- **Proposition H.4** (App. H; cited in Examples H.5, H.6, P3:4780, 4783). Suppose `∂Ω` consists of disjoint analytic
Jordan curves and that `E` and `F` are finite unions of closed arcs on `∂Ω`. Let `N_c` be the number of components of
`∂Ω`, `N_e` the number of endpoints of arcs in `E ∪ F`, `N_z` the number of critical points of `ω` in `Ω`, and `N_z^b`
the number of critical points of `ω` on `∂Ω`, where a critical point of order `k` is counted `k` times. Then
`N_z + N_z^b/2 = N_e/4 + (N_c − 2)`.
Modelling (leader ruling Fb3): `(Ω, E, F)` is a triple (the setting of Theorem H.1) and `ω` is the book's
(`IsDoubleHarmonicMeasure`; for analytic boundaries the classical solution of (H.1)–(H.3), Theorem H.1(c)); `∂Ω` is
the disjoint union of the `N = N_c` analytic Jordan curves `Γ j` (Ch. II §2's `IsAnalyticJordanCurve`); `N_z` and
`N_z^b` sum `criticalOrder` over `Ω` and over `∂Ω` minus the endpoints (at an endpoint `φ′` has the singularity of
order `−1/2`, case (i) of the proof of Theorem H.1, so it is not a critical point), and `N_e` is the number of points of
`arcEndpoints`. The identity is multiplied by `4` and written without subtraction in `[0, ∞]`
(`4 N_z + 2 N_z^b + 8 = N_e + 4 N_c`), which forces the sums to be finite. Added hypothesis: `∞ ∉ Ω` (meaning: the
derivative `ω_x − iω_y` of `criticalOrder` is planar, and the count is invariant under a Möbius map moving a point of
`ℂ* \ Ω̄` to `∞`, which keeps the boundary curves analytic; the analytic curves already lie in `ℂ`). The display was
checked against the equation image. -/
theorem propH_4 {Ω E F : Set ExtPlane} (h : IsFCTriple Ω E F) (hΩinf : extInf ∉ Ω) {N : ℕ}
    {Γ : Fin N → Set ExtPlane} (hΓ : ∀ j, IsAnalyticJordanCurve (Γ j))
    (hΓd : Pairwise fun i j => Disjoint (Γ i) (Γ j)) (hΩΓ : frontier Ω = ⋃ j, Γ j) {ω : ExtPlane → ℝ}
    (hω : IsDoubleHarmonicMeasure Ω E F ω) :
    4 * (∑' ζ : finitePart Ω, (criticalOrder Ω ω ζ : ℝ≥0∞)) +
        2 * (∑' ζ : finitePart (frontier Ω \ arcEndpoints Ω E F), (criticalOrder Ω ω ζ : ℝ≥0∞)) + 8 =
      ((arcEndpoints Ω E F).encard : ℝ≥0∞) + 4 * N := by
  sorry

/-- **Theorem H.7** (App. H; cited in the proof of Theorem H.8, P3:4819). Let `Ω` be a finitely connected Jordan
domain, and let `E` be a finite union of arcs contained in one component `Γ₁` of `∂Ω`. Suppose `σ` is a Jordan arc in
`ℂ` connecting `z₀` [OCR: printed `z`] to `Γ₁ \ E` and let `λ ≡ d_{Ω∖σ}(σ, E)`. Then `ω(z₀, E, Ω) ≤ (8/π) e^{−πλ}`.
Modelling: `Γ₁` is the component of `∂Ω` through a point `q ∈ ∂Ω` (the hypothesis `q ∈ ∂Ω` only names a component);
`E` is a union of finitely many, at least one, Jordan arcs of `ℂ*` in `Γ₁` (Ch. IV §5's reading of "a finite union of
arcs"); `z₀ ∈ Ω` is finite, and `σ` is a closed Jordan arc of the plane from `z₀` to a point `p ∈ Γ₁ \ E`, which may
leave `Ω` ("`σ ∩ Ω` need not be connected", P3:4798), so `Ω \ σ` may be disconnected (`extremalDistGM` takes any plane
set); `λ` is taken on finite parts, with values in `[0, ∞]`, and `λ < ∞` is part of the conclusion (the `thm4_5_3`
pattern: `λ = ∞` would give `ω(z₀, E, Ω) = 0`, impossible for a union of arcs); `ω` is `harmonicMeasureFC` (the
explicit setting). B-cand.: Theorem IV.5.3 (`thm4_5_3`, Jordan domains, arcs `σ ⊂ Ω`). The constant was checked
against the equation image. -/
theorem thmH_7 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {q : ExtPlane} (hq : q ∈ frontier Ω)
    {E : Set ExtPlane} (hE : IsFiniteUnionOf (fun s => IsJordanArc s ∧ s ⊆ connectedComponentIn (frontier Ω) q) E)
    {z₀ : ℂ} (hz₀ : (z₀ : ExtPlane) ∈ Ω) {σ : Set ℂ} {p : ExtPlane} (hσ : IsArcFromTo (toExt σ) z₀ p)
    (hp : p ∈ connectedComponentIn (frontier Ω) q \ E) :
    extremalDistGM (finitePart Ω \ σ) σ (finitePart E) < ⊤ ∧
      (harmonicMeasureFC Ω z₀ E).toReal ≤
        8 / π * Real.exp (-π * (extremalDistGM (finitePart Ω \ σ) σ (finitePart E)).toReal) := by
  sorry

/-- **Theorem H.8** (App. H; cited in Ch. IV, P1:6478, "Theorem H.8 in Appendix H extends Theorem 6.1 to finitely
connected domains", and in Exercise H.2). Suppose `Ω` is a finitely connected Jordan domain and suppose
`E ⊂ {z ∈ Ω̄ : Re z ≥ b}`. Let `z₀ ∈ Ω` with `x₀ = Re z₀ < b` and assume that for `x₀ < x < b`,
`I_x ⊂ {z ∈ Ω : Re z = x}` separates `z₀` [OCR: printed `z`] from `E`. If `θ(x) ≡ ℓ(I_x)` is measurable then
`ω(z₀, E) ≤ (8/π) exp(−π ∫_{x₀}^b dx/θ(x))`.
Modelling: as Theorem IV.6.1 (`thm4_6_1`): `E` is a set of the plane with `E ⊆ Ω̄` (closure in `ℂ*`), `z₀` is finite,
separation is `IsSeparatingIn` in the finite part of `Ω`, `θ(x) = μH[1](I_x)`, measurable as the book assumes; `ω(z₀,
E)` is `harmonicMeasureFC Ω z₀` (the explicit setting), a measure carried by `∂Ω`, so it measures `E ∩ ∂Ω` (the
reading of Theorem IV.6.2, `thm4_6_2`); the bound in two cases, as in Ch. IV §6: if the integral is `∞` then
`ω(z₀, E) = 0` (`exp(−π·∞) = 0`), otherwise the bound holds in `[0, ∞]`. B-cand.: `thm4_6_1` (Jordan domains,
`E ⊆ ∂Ω`). The constant was checked against the equation image. -/
theorem thmH_8 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {b : ℝ} {E : Set ℂ} (hE : toExt E ⊆ closure Ω)
    (hEb : ∀ z ∈ E, b ≤ z.re) {z₀ : ℂ} (hz₀ : (z₀ : ExtPlane) ∈ Ω) (hb : z₀.re < b) {I : ℝ → Set ℂ}
    (hI : ∀ x ∈ Ioo z₀.re b, I x ⊆ finitePart Ω ∩ {z : ℂ | z.re = x} ∧ IsSeparatingIn (finitePart Ω) (I x) {z₀} E)
    (hθ : AEMeasurable (fun x => μH[1] (I x)) (volume.restrict (Ioo z₀.re b))) :
    (∫⁻ x in Ioo z₀.re b, (μH[1] (I x))⁻¹ = ⊤ → harmonicMeasureFC Ω z₀ (toExt E) = 0) ∧
      (∫⁻ x in Ioo z₀.re b, (μH[1] (I x))⁻¹ < ⊤ →
        harmonicMeasureFC Ω z₀ (toExt E) ≤
          ENNReal.ofReal (8 / π * Real.exp (-π * (∫⁻ x in Ioo z₀.re b, (μH[1] (I x))⁻¹).toReal))) := by
  sorry

/-- **Theorem H.9** (App. H; cited at P3:4835–4843, 4889–4901, in Ch. V, Notes P2:421 "An extension of Theorem 3.2 to
finitely connected domains is given in Theorem H.9 of Appendix H", and in Exercise H.5). Suppose `Ω` is a finitely
connected Jordan domain and suppose `∞ ∈ Ω`. Let `C_R = {z : |z| = R}`. Then
`γ = lim_{R→∞} 2π d_Ω(C_R, ∂Ω) − log R`, where `γ` is Robin's constant for `∂Ω` defined by `Cap(∂Ω) = e^{−γ}`.
Modelling: `∂Ω` is a plane set (`∞ ∈ Ω`) and `γ` is `robinConstant` of it (Ch. III (4.8), `EReal`); the statement
includes that `γ` is finite (`∂Ω` is a finite union of Jordan curves, of positive capacity). `d_Ω(C_R, ∂Ω)` is taken on
finite parts; for large `R` the circle `C_R` lies in `Ω` and the distance is finite, which is stated, so that its real
value is not the `toReal` junk. Theorem V.3.2 (`thm5_3_2`) is "a special case of Theorem H.9" by the symmetry rule
(P3:4843). The formula was checked against the equation image. -/
theorem thmH_9 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) (hinf : extInf ∈ Ω) :
    ∃ γ : ℝ, robinConstant (finitePart (frontier Ω)) = γ ∧
      (∀ᶠ R in atTop, extremalDistGM (finitePart Ω) (sphere 0 R) (finitePart (frontier Ω)) < ⊤) ∧
      Tendsto (fun R : ℝ => 2 * π * (extremalDistGM (finitePart Ω) (sphere 0 R) (finitePart (frontier Ω))).toReal -
        Real.log R) atTop (𝓝 γ) := by
  sorry

/-- **Formula (H.18)** (App. H, P3:4889–4899; cited at P3:4901, "we can explicitly find the right side of (H.18) and
that is how we proved Theorem V.3.2"). Suppose `Ω` is a finitely connected Jordan domain, suppose `E` is contained in
one component of `∂Ω`, and let `z₀ ∈ Ω`. As in the proof of Theorem V.3.2 [OCR: printed "Theorem V.3"], there is a
conformal map `f` of `Ω` onto a region of the form `A = ℂ* \ (𝔻̄ ∪ ⋃_{j=1}^n L_j)`, where `L_1, …, L_n` are radial line
segments, `f(E) = ∂𝔻`, and `f(z₀) = ∞`. The radial slits do not affect `d_𝔻(C_R, ∂𝔻)`, so by Theorem H.9 and the
definition of reduced extremal distance (H.18) `δ_Ω(z₀, E) = δ_A(∞, ∂𝔻) = −γ_A/2π`.
Modelling: [reading] `E` is a finite union of closed arcs in the component of `∂Ω` through `q ∈ ∂Ω`, the setting in
which Ch. V §3 defines `δ`; `f` is LV's conformal map onto `A`, the slits are bounded radial segments
`{t e^{iθ} : a ≤ t ≤ b}`, `1 ≤ a < b ≤ R` (`IsRadialSlit 1 R`: they may start on `∂𝔻`, as the images of the arcs of
`Γ₁ \ E`), and "`f(E) = ∂𝔻`" is read through a continuous extension `F` of `f` to `Ω̄` (not one-to-one: the other
boundary arcs go to slits traced twice); `δ` is `reducedExtremalDist` (at `∞` through Ch. V §3's chart discs, leader
ruling C1); `γ_A` is Robin's constant for `∂A` (Theorem H.9's "Robin's constant for `∂Ω`"), stated finite, and the
value `−γ_A/2π` is a real number, as in Theorem V.3.2 (`thm5_3_2`). The display was checked against the equation
image. -/
theorem eqH_18 {Ω : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) {q : ExtPlane} (hq : q ∈ frontier Ω)
    {E : Set ExtPlane}
    (hE : IsFiniteUnionOf (fun s => IsClosedJordanArc s ∧ s ⊆ connectedComponentIn (frontier Ω) q) E)
    {z₀ : ExtPlane} (hz₀ : z₀ ∈ Ω) :
    ∃ (f F : ExtPlane → ExtPlane) (R : ℝ) (n : ℕ) (L : Fin n → Set ℂ) (A : Set ExtPlane),
      A = (toExt (closedBall 0 1 ∪ ⋃ j, L j))ᶜ ∧ (∀ j, IsRadialSlit 1 R (L j)) ∧ IsConformalMap f Ω ∧
      f '' Ω = A ∧ ContinuousOn F (closure Ω) ∧ EqOn F f Ω ∧ F '' E = toExt (sphere 0 1) ∧ f z₀ = extInf ∧
      reducedExtremalDist Ω z₀ E = reducedExtremalDist A extInf (toExt (sphere 0 1)) ∧
      ∃ g : ℝ, robinConstant (finitePart (frontier A)) = g ∧
        reducedExtremalDist A extInf (toExt (sphere 0 1)) = ((-g / (2 * π) : ℝ) : EReal) := by
  sorry

end GarnettMarshall2005
