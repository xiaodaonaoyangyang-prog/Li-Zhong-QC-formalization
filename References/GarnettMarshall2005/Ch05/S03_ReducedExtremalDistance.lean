import References.GarnettMarshall2005.Ch05.S02_LowerBounds

/-!
# Garnett–Marshall, Chapter V §3: Reduced extremal distance

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. V §3 (pp. 161–166;
`full.md` P1:6951–7168).

Conventions of Chapter V §3, as modelled here. Domains are domains of `ℂ*`. The disc `B_ε = B_ε(z₀)` is the chart disc
`ballExt z₀ ε` (`LehtoVirtanen1973.extChartInv z₀` applied to `{|ζ| < ε}`): `{|z − z₀| < ε}` for finite `z₀`, and
`{|z| > 1/ε} ∪ {∞}` for `z₀ = ∞` (Theorem 3.2 uses `δ` at `∞`); `∂B_ε` is its boundary circle, and the book's
`Ω \ B_ε` is the open set `Ω \ B̄_ε`. Extremal distances are taken on finite parts, as in Chapter IV (planar, leader
ruling B9); `d_{Ω∖B_ε}(∂B_ε, E)` is `extremalDistBall Ω z₀ E ε`, with values in `[0, ∞]`. "A finite union of closed
(sub)arcs of `∂Ω`" is a union of finitely many, at least one, closed Jordan arcs of `ℂ*` contained in `∂Ω`
(`IsFiniteUnionOf`, as in Ch. IV §4). The reduced extremal distance `δ_Ω(z₀, E)` is defined for every domain, point
and set as an `EReal` upper limit (leader ruling C1): the book defines it for finitely connected Jordan domains and
finite unions of arcs, where the limit exists and is finite (`reducedExtremalDist_tendsto`), but it also applies it
to `Ω = ψ(𝔻)` for any normalized univalent `ψ` and any `E` (Theorem 3.5, where `δ` may be `+∞`), to a disc minus
radial slits, and to `z₀ = ∞`. Robin's constant `γ_E` and the capacity `Cap(E) = e^{−γ_E}` are those of Ch. III
(4.8) (`robinConstant`, `capacity`: the most general stage, leader ruling B1), so `e^{−γ_E}` is `capacity E`; `|E|` is
the arc-length measure `arcMeasure` of `∂𝔻` and `ω(0, E)` on `𝔻` is `harmonicMeasureDisc 0`; for a Jordan domain
`ω(z₀, E)` is `harmonicMeasureJordan` (Corollary 3.3 is set in a Jordan domain, leader rulings B5, C6). A normalized
univalent function is a map `ψ` holomorphic and one-to-one on `𝔻` with `ψ(0) = 0` and `ψ'(0) = 1`, as in Ch. I §4.

* Formula (3.1) (§3) — `eq5_3_1`
* Definition (reduced extremal distance `δ_Ω(z₀, E)`, §3, P1:6986–6989) — `reducedExtremalDist` (with the
  helpers `ballExt`, `extremalDistBall`)
* Unlabelled (§3, P1:6967–6997): `h(ε) = d_{Ω∖B_ε}(∂B_ε, E) + (1/2π) log ε` is decreasing and bounded above, and
  the limits of `h(ε)`, of `d_{Ω∖B_ε}(∂B_ε, ∂Ω) + (1/2π) log ε` and of their difference exist and are finite —
  `reducedExtremalDist_tendsto`
* Lemma 3.1 (§3) — `lemma5_3_1`
* Definition (Robin's constant `γ_E` and the logarithmic capacity `Cap(E) = e^{−γ_E}` of a compact plane set,
  recalled, §3, P1:7021) — exists: `GarnettMarshall2005.robinConstant`, `GarnettMarshall2005.capacity` (the
  Borel-set stage (4.8) of Chapter III, the most general stage so far, with γ = log(1/Cap); the recalled expansion
  g(z, ∞) = log |z| + γ + o(1) is (III.1.6))
* Theorem 3.2 (Ahlfors–Beurling, §3) — `thm5_3_2`
* Formula (3.2) (§3) — `eq5_3_2`
* Unlabelled (§3, P1:7043): when `E` is a single arc of `∂𝔻`, equality holds in the first inequality of (3.2),
  `e^{−γ_E} = sin(|E|/4)` — `capacity_arc_eq`
* Corollary 3.3 (§3) — `cor5_3_3_a`, `cor5_3_3_b`
* Corollary 3.4 (Pfluger, §3) — `cor5_3_4`
* Definition (the euclidean distance `dist_Ω(z₀, w)` in `Ω`, §3, P1:7093–7099) — `innerDistGM`
* Theorem 3.5 (§3; (3.3)) — `thm5_3_5_a`, `thm5_3_5_b`
* Corollary 3.6 (Balogh–Bonk, §3) — `cor5_3_6`

Helpers (not book notions): `ballExt` (the chart disc `B_ε(z₀)` of `ℂ*`), `extremalDistBall` (the extremal distance
`d_{Ω∖B_ε}(∂B_ε, E)`).

Not stated (inventory U−): the motivating euclidean distance `inf {∫_γ ds : γ ⊂ Ω joins z₀ to E}` (P1:6953–6959,
motivation); the remark that the proof of Theorem 3.2 is a reprise of that of Theorem IV.4.1, with capacities in place
of harmonic measures (P1:7037); the sentence introducing Pfluger's corollary and the remark that Exercise 2 gives a
proof of Theorem 3.2 by logarithmic potentials, with the pointer to the metric of Bonk, Koskela and Rohde
(P1:7057, 7091); the remark that by (3.2) capacity can be replaced by length in Corollary 3.6, with the pointer to
Exercises III.22–III.23 (P1:7167). The bound for `h(ε)` through a component `E₁` of `E` (P1:6991–6997; the OCR lost
its second line, read from the equation image as `≤ d_{𝔻∖B(0,aε)}(∂B(0, aε), ∂𝔻) + (1/2π) log ε = (1/2π) log(1/a)`)
and (3.4) are steps of proofs.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt extInf unitDisc)
open LehtoVirtanen1973 (IsClosedJordanArc IsConformalMap extChartInv)
open References (IsJordanDomainExt finitePart)

/-- The disc `B_ε(z₀)` of `ℂ*` in the chart at `z₀` (helper, Ch. V §3, P1:6961): the image of `{|ζ| < ε}` under
`LehtoVirtanen1973.extChartInv z₀`, which is `{|z − z₀| < ε}` for finite `z₀` and `{|z| > 1/ε} ∪ {∞}` for
`z₀ = ∞`; empty for `ε ≤ 0`. -/
def ballExt (z₀ : ExtPlane) (ε : ℝ) : Set ExtPlane :=
  extChartInv z₀ '' ball 0 ε

/-- The extremal distance `d_{Ω∖B_ε}(∂B_ε, E)` from the circle `∂B_ε` to `E` in `Ω \ B̄_ε` (helper, Ch. V §3,
P1:6961), taken on finite parts as in Chapter IV. -/
def extremalDistBall (Ω : Set ExtPlane) (z₀ : ExtPlane) (E : Set ExtPlane) (ε : ℝ) : ℝ≥0∞ :=
  extremalDistGM (finitePart (Ω \ closure (ballExt z₀ ε))) (finitePart (frontier (ballExt z₀ ε))) (finitePart E)

/-- **Formula (3.1)** (Ch. V §3, P1:6961–6965; cited at P1:6967, in the proof of Corollary 3.4, P1:7065, at P1:7204
"As in (3.1)" for (4.4), and in App. H, P3:4835 "As we saw in Section V.3, `2π d_Ω(C_R, ∂Ω) − log R` increases with
`R`"). Let `Ω` be a finitely connected Jordan domain, `z₀ ∈ Ω`, and `E ⊆ ∂Ω`. If `β < ε`, then by the serial rule and
Example IV.1.2,
(3.1) `d_{Ω∖B_β}(∂B_β, E) ≥ d_{Ω∖B_ε}(∂B_ε, E) + d_{B_ε∖B_β}(∂B_β, ∂B_ε) = d_{Ω∖B_ε}(∂B_ε, E) + (1/2π) log(ε/β)`.
Modelling: `0 < β < ε` with `B̄_ε ⊆ Ω` (the discs of the book are small discs about `z₀ ∈ Ω`; this also gives
`z₀ ∈ Ω`); `z₀ = ∞` is allowed (chart discs; there `B_ε \ B̄_β` is the annulus `{1/ε < |z| < 1/β}`); the display
is stated as printed: the serial-rule inequality with the annulus term `d_{B_ε∖B_β}(∂B_β, ∂B_ε)` (taken in the open
annulus `B_ε \ B̄_β`, on finite parts), and its value by Example IV.1.2 (`example4_1_2_a`); sums in `[0, ∞]`. The
serial rule gives (3.1) for any set `E ⊆ ∂Ω`, which is how the second limit of `reducedExtremalDist_tendsto`
(`E = ∂Ω`) and App. H use it, so `E` is not restricted to finite unions of arcs. The constant was checked against the
equation image. -/
theorem eq5_3_1 {Ω E : Set ExtPlane} (hΩ : IsFCJordanDomain Ω) (hE : E ⊆ frontier Ω) {z₀ : ExtPlane} {β ε : ℝ}
    (hβ : 0 < β) (hβε : β < ε) (hB : closure (ballExt z₀ ε) ⊆ Ω) :
    extremalDistBall Ω z₀ E ε + extremalDistGM (finitePart (ballExt z₀ ε \ closure (ballExt z₀ β)))
        (finitePart (frontier (ballExt z₀ β))) (finitePart (frontier (ballExt z₀ ε))) ≤
        extremalDistBall Ω z₀ E β ∧
      extremalDistGM (finitePart (ballExt z₀ ε \ closure (ballExt z₀ β))) (finitePart (frontier (ballExt z₀ β)))
          (finitePart (frontier (ballExt z₀ ε))) = ENNReal.ofReal (1 / (2 * π) * Real.log (ε / β)) := by
  sorry

/-- **Definition** (reduced extremal distance, Ch. V §3, P1:6953 and P1:6986–6989; used in Theorems 3.2, 3.5,
Corollaries 3.3, 3.6, and in App. H, (H.18), P3:4889–4903, "the definition of reduced extremal distance"). Let `Ω`
be a finitely connected Jordan domain, `z₀ ∈ Ω`, and `E` a finite union of closed subarcs of `∂Ω`. The reduced
extremal distance is the limit
`δ(z₀, E) = δ_Ω(z₀, E) = lim_{ε→0} (d_{Ω∖B_ε}(∂B_ε, E) − d_{Ω∖B_ε}(∂B_ε, ∂Ω))`.
Modelling (leader ruling C1): for every `Ω`, `z₀` and `E`, the upper limit as `ε → 0⁺` of the difference, taken in
`[−∞, +∞]` (`EReal`, a complete lattice, so the upper limit has no junk value). It is the book's limit wherever that
limit exists, finite or `+∞`; in the book's setting it exists and is finite (`reducedExtremalDist_tendsto`), and in
the book's other uses (Theorem 3.5, its slit-disc case, `z₀ = ∞` in Theorem 3.2, (H.18)) it exists by the same
monotonicity (3.1) and may be `+∞` when `E` is small. Junk: when `d_{Ω∖B_ε}(∂B_ε, ∂Ω) = ∞` for small `ε` (a polar
boundary) the difference is `∞ − ∞ = −∞` in `EReal`; this is outside the book's discourse. -/
def reducedExtremalDist (Ω : Set ExtPlane) (z₀ : ExtPlane) (E : Set ExtPlane) : EReal :=
  limsup (fun ε : ℝ => (extremalDistBall Ω z₀ E ε : EReal) - (extremalDistBall Ω z₀ (frontier Ω) ε : EReal))
    (𝓝[>] 0)

/-- **Unlabelled** (Ch. V §3, P1:6967–6997; cited in the proof of Lemma 3.1, P1:7007 "`k(α)` … is decreasing and
bounded above", in the proof of Corollary 3.4, P1:7071 "increases to `γ_E/π`", and in App. H, P3:4835). Let `Ω` be
a finitely connected Jordan domain, `z₀ ∈ Ω`, and `E` a finite union of closed subarcs of `∂Ω`. By (3.1),
`h(ε) = d_{Ω∖B_ε}(∂B_ε, E) + (1/2π) log ε` is a decreasing function of `ε`, and `h(ε)` is bounded above. It follows
that the three limits `lim_{ε→0} d_{Ω∖B_ε}(∂B_ε, E) + (1/2π) log ε`, `lim_{ε→0} d_{Ω∖B_ε}(∂B_ε, ∂Ω) + (1/2π) log ε`
and `δ(z₀, E) = lim_{ε→0} (d_{Ω∖B_ε}(∂B_ε, E) − d_{Ω∖B_ε}(∂B_ε, ∂Ω))` all exist and are finite.
Modelling: for `0 < ε < ε₀` both extremal distances are finite (they are then read as real numbers), `h` is
decreasing on `(0, ε₀)`, the first two limits are `L₁`, `L₂`, and the last conjunct says that the upper limit of
`reducedExtremalDist` is the book's third limit `L₁ − L₂`; "bounded above" is contained in the existence of the
finite limit `L₁` of the decreasing `h`. `z₀ = ∞` is allowed (the chart discs; `ε` is the chart radius). -/
theorem reducedExtremalDist_tendsto {Ω E : Set ExtPlane} (hΩ : IsFCJordanDomain Ω)
    (hE : IsFiniteUnionOf (fun s => IsClosedJordanArc s ∧ s ⊆ frontier Ω) E) {z₀ : ExtPlane} (hz₀ : z₀ ∈ Ω) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ L₁ L₂ : ℝ,
      (∀ ε ∈ Ioo 0 ε₀, extremalDistBall Ω z₀ E ε < ⊤ ∧ extremalDistBall Ω z₀ (frontier Ω) ε < ⊤) ∧
      AntitoneOn (fun ε => (extremalDistBall Ω z₀ E ε).toReal + Real.log ε / (2 * π)) (Ioo 0 ε₀) ∧
      Tendsto (fun ε => (extremalDistBall Ω z₀ E ε).toReal + Real.log ε / (2 * π)) (𝓝[>] 0) (𝓝 L₁) ∧
      Tendsto (fun ε => (extremalDistBall Ω z₀ (frontier Ω) ε).toReal + Real.log ε / (2 * π)) (𝓝[>] 0)
        (𝓝 L₂) ∧
      reducedExtremalDist Ω z₀ E = ((L₁ - L₂ : ℝ) : EReal) := by
  sorry

/-- **Lemma 3.1** (Ch. V §3; label OCR'd as a heading, P1:6999; cited at P1:7031 "the proof of Lemma 3.1 yields",
and, as a method, at P1:7216 for the reduced modulus). The reduced extremal distance `δ(z₀, E)` is conformally
invariant: if `φ` is a conformal map defined on `Ω`, then `δ_{φ(Ω)}(φ(z₀), φ(E)) = δ_Ω(z₀, E)`.
Modelling: the setting of the definition (`Ω` a finitely connected Jordan domain, `z₀ ∈ Ω`, `E` a finite union of
closed subarcs of `∂Ω`); `φ` is a conformal map of `Ω` in the sense of LV (`LehtoVirtanen1973.IsConformalMap`, so
`z₀` or `φ(z₀)` may be `∞`), and `φ(E)` is the image of `E` under a homeomorphic extension `Φ` of `φ` to `Ω̄`
(continuous and one-to-one on the compact set `Ω̄`), which makes `φ(Ω)` again a finitely connected Jordan domain and
`Φ(E)` a finite union of closed arcs of its boundary; the proof's normalization `z₀ = 0 = φ(z₀)` is a proof step. -/
theorem lemma5_3_1 {Ω E : Set ExtPlane} (hΩ : IsFCJordanDomain Ω)
    (hE : IsFiniteUnionOf (fun s => IsClosedJordanArc s ∧ s ⊆ frontier Ω) E) {z₀ : ExtPlane} (hz₀ : z₀ ∈ Ω)
    {φ Φ : ExtPlane → ExtPlane} (hφ : IsConformalMap φ Ω) (hΦ : ContinuousOn Φ (closure Ω))
    (hΦi : InjOn Φ (closure Ω)) (hΦφ : EqOn Φ φ Ω) :
    reducedExtremalDist (φ '' Ω) (φ z₀) (Φ '' E) = reducedExtremalDist Ω z₀ E := by
  sorry

/-- **Theorem 3.2** (Ahlfors–Beurling; Ch. V §3; cited at P1:7037, 7057, 7077, 7091, in the proof of Corollary 3.6,
P1:7165, in the Notes, P2:421, in Exercise 2, P2:493, 517, and in App. H, P3:4841–4843 "Theorem V.3.2 is a special case
of Theorem H.9", P3:4889, 4901). If `E` is a finite union of closed arcs in `∂𝔻`, then
`δ_𝔻(0, E) = δ_{𝔻̄ᶜ}(∞, E) = γ_E/π`, where `γ_E` is Robin's constant for `E`.
Modelling: `E` is a union of finitely many, at least one, closed Jordan arcs contained in the unit circle (the whole
circle is a union of two); `𝔻̄ᶜ` is the domain `ℂ* \ 𝔻̄`, which contains `∞`; `γ_E` is `robinConstant E` (Ch. III
(4.8)), and the statement includes that it is finite (`Cap(E) > 0` for a union of arcs), so that `γ_E/π` is a real
number. The formula `γ_E/π` was checked against the equation image. -/
theorem thm5_3_2 {E : Set ℂ} (hE : IsFiniteUnionOf (fun s : Set ℂ => IsClosedJordanArc (toExt s) ∧ s ⊆ sphere 0 1) E) :
    ∃ g : ℝ, robinConstant E = g ∧
      reducedExtremalDist (toExt unitDisc) ((0 : ℂ) : ExtPlane) (toExt E) = ((g / π : ℝ) : EReal) ∧
      reducedExtremalDist (toExt (closedBall 0 1))ᶜ extInf (toExt E) = ((g / π : ℝ) : EReal) := by
  sorry

/-- **Formula (3.2)** (Ch. V §3, P1:7037–7041; cited at P1:7043 and P1:7167). Theorem 3.2 includes an estimate for the
harmonic measure of `E ⊂ ∂𝔻`, because by Example III.1.2, (3.2) `e^{−γ_E} ≥ sin(|E|/4) ≥ |E|/(2π) = ω(0, E)`.
Modelling: `E` is a Borel subset of `∂𝔻` (the book's "`E ⊂ ∂𝔻`", justified by Example III.1.2, which is stated for any
such `E`; P1:7167 applies (3.2) to the open set `{ζ : ∫₀¹ |ψ′(rζ)| dr > λ}` of Corollary 3.6, so `E` is not restricted
to the finite unions of arcs of Theorem 3.2); `e^{−γ_E}` is `Cap(E)` (`capacity E`, the (4.8) capacity of a Borel set,
since `γ_E = log(1/Cap(E))`), compared in `[0, ∞]`; `|E|` is `arcMeasure E` (total mass `2π`) and `ω(0, E)` is
`harmonicMeasureDisc 0 E`, read as real numbers (finite measures) where real arithmetic follows. The first inequality is
Example III.1.2 (`example3_1_2`, for compact sets, extended to Borel sets by (4.8) and the inner regularity of
`arcMeasure`), the second is the concavity of `sin` on `[0, π/2]`, the equality is (I.1.6); the chain is stated as
displayed. The display was checked against the equation image. -/
theorem eq5_3_2 {E : Set ℂ} (hE : MeasurableSet E) (hE1 : E ⊆ sphere 0 1) :
    ENNReal.ofReal (Real.sin ((arcMeasure E).toReal / 4)) ≤ capacity E ∧
      (arcMeasure E).toReal / (2 * π) ≤ Real.sin ((arcMeasure E).toReal / 4) ∧
      (harmonicMeasureDisc 0 E).toReal = (arcMeasure E).toReal / (2 * π) := by
  sorry

/-- **Unlabelled** (Ch. V §3, P1:7043; the step from (3.2) to the arc case of Corollary 3.3, P1:7043–7045; Part B had
the same equality as a step of the proof of Example III.1.2, P1:3446). When `E` is a single arc of `∂𝔻`, equality
holds in the first inequality in (3.2): `e^{−γ_E} = sin(|E|/4)`.
Modelling: the closed arc `E = {e^{it} : s ≤ t' ≤ t}` with `s < t < s + 2π` (a proper arc of length `|E| = t − s`);
`e^{−γ_E}` is `capacity E` (Ch. III (4.8)). -/
theorem capacity_arc_eq {s t : ℝ} (hst : s < t) (hts : t < s + 2 * π) :
    capacity (circleMap 0 1 '' Icc s t) = ENNReal.ofReal (Real.sin ((t - s) / 4)) := by
  sorry

/-- **Corollary 3.3** (Ch. V §3; cited in Exercise 3, P2:519), first part. If `Ω` is a Jordan domain and if `E` is a
finite union of closed arcs on `∂Ω`, then `ω(z₀, E) ≤ e^{−πδ(z₀, E)}`.
Modelling: `Ω` is a Jordan domain of `ℂ*` and `z₀ ∈ Ω` (the point of `δ(z₀, E)`); `ω(z₀, E)` is
`harmonicMeasureJordan Ω z₀ E` (the book states it for Jordan domains, leader ruling B5), read as a real number; the
statement includes that `δ(z₀, E)` is finite (true by `reducedExtremalDist_tendsto`, a Jordan domain being a
finitely connected Jordan domain), so that `e^{−πδ}` is read as a real number `e^{−πd}`. The bound was checked
against the equation image. -/
theorem cor5_3_3_a {Ω E : Set ExtPlane} (hΩ : IsJordanDomainExt Ω)
    (hE : IsFiniteUnionOf (fun s => IsClosedJordanArc s ∧ s ⊆ frontier Ω) E) {z₀ : ExtPlane} (hz₀ : z₀ ∈ Ω) :
    ∃ d : ℝ, reducedExtremalDist Ω z₀ E = d ∧ (harmonicMeasureJordan Ω z₀ E).toReal ≤ Real.exp (-π * d) := by
  sorry

/-- **Corollary 3.3** (Ch. V §3), second part. If `E` is a single arc, then
`ω(z₀, E) = (2/π) sin⁻¹(e^{−πδ(z₀, E)}) ≥ (2/π) e^{−πδ(z₀, E)}`.
Modelling: as in the first part, with `E` a closed Jordan arc of `ℂ*` contained in `∂Ω`; `sin⁻¹` is `Real.arcsin`
(its argument `e^{−πδ}` lies in `(0, 1]`, where no junk value is read). The formula was checked against the equation
image. -/
theorem cor5_3_3_b {Ω E : Set ExtPlane} (hΩ : IsJordanDomainExt Ω) (hE : IsClosedJordanArc E)
    (hEΩ : E ⊆ frontier Ω) {z₀ : ExtPlane} (hz₀ : z₀ ∈ Ω) :
    ∃ d : ℝ, reducedExtremalDist Ω z₀ E = d ∧
      (harmonicMeasureJordan Ω z₀ E).toReal = 2 / π * Real.arcsin (Real.exp (-π * d)) ∧
      2 / π * Real.exp (-π * d) ≤ (harmonicMeasureJordan Ω z₀ E).toReal := by
  sorry

/-- **Corollary 3.4** (Pfluger; Ch. V §3; cited in an exercise of Chapter VIII, P2:5321 "Pfluger's theorem V.3.4").
If `Ω = 𝔻`, if `E` is a finite union of closed arcs in `∂𝔻`, and if `∂B_ε` is the circle centered at `0` of radius
`ε`, then
`γ_E/π + log(1/ε)/(2π) + log(1 − ε)/π ≤ d_𝔻(∂B_ε, E) ≤ γ_E/π + log(1/ε)/(2π)`.
Modelling: `E` as in Theorem 3.2; `0 < ε < 1` (the circle lies in `𝔻`, and `log(1 − ε)` is defined); the statement
includes that `γ_E` and `d_𝔻(∂B_ε, E)` are finite, so that both are read as real numbers; `d_𝔻` is the extremal
distance in `𝔻` itself, as printed (it equals `d_{𝔻∖B_ε}(∂B_ε, E)` by the extension rule (IV.3.2), as the book
notes at P1:7142). The proof (P1:7071) cites Theorem III.2.2 for `γ_E − g(z) = U_μ(z)`, outside that
theorem's hypothesis (a complement bounded by `C^{1+α}` Jordan curves, `thm3_2_2_b`); the content used is
(III.4.10), `thm3_4_4_b`. The three terms were checked against the equation image. -/
theorem cor5_3_4 {E : Set ℂ} (hE : IsFiniteUnionOf (fun s : Set ℂ => IsClosedJordanArc (toExt s) ∧ s ⊆ sphere 0 1) E)
    {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) :
    ∃ g : ℝ, robinConstant E = g ∧ extremalDistGM unitDisc (sphere 0 ε) E < ⊤ ∧
      g / π + Real.log (1 / ε) / (2 * π) + Real.log (1 - ε) / π ≤
        (extremalDistGM unitDisc (sphere 0 ε) E).toReal ∧
      (extremalDistGM unitDisc (sphere 0 ε) E).toReal ≤ g / π + Real.log (1 / ε) / (2 * π) := by
  sorry

/-- **Definition** (the euclidean distance in `Ω`, Ch. V §3, P1:7093–7099; used in Theorem 3.5, in the proof of
Corollary 3.6 with the Gehring–Hayman inequality, Exercise III.16). For `z₀ ∈ Ω`,
`dist_Ω(z₀, w) = inf {∫_γ ds : γ is a curve in Ω and z₀, w ∈ γ̄}` is the euclidean distance in `Ω` from `z₀` to `w`.
Modelling: a curve in `Ω` is a map `γ : (0, 1) → Ω` continuous on the open interval, so that its closure `γ̄` may
contain boundary points `w ∈ ∂Ω`; `∫_γ ds` is its length, the total variation of `γ` on `(0, 1)`; the infimum is in
`[0, ∞]` (`∞` if no such curve exists). B-cand. LiZhongQC.metricDist with density `1` joins points of an open set
only. -/
def innerDistGM (Ω : Set ℂ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → ℂ) (_ : ContinuousOn γ (Ioo 0 1) ∧ γ '' Ioo 0 1 ⊆ Ω ∧ z ∈ closure (γ '' Ioo 0 1) ∧
      w ∈ closure (γ '' Ioo 0 1)), eVariationOn γ (Ioo 0 1)

/-- **Theorem 3.5** (Ch. V §3), (3.3) (cited in the proof of Corollary 3.6, P1:7165, and in an exercise of Chapter
VII, P2:3399, 3411). Let `ψ : 𝔻 → Ω` be a normalized univalent function, `ψ(0) = 0` and `ψ'(0) = 1`, and let
`E ⊂ {ζ ∈ ∂Ω : dist_Ω(0, ζ) ≥ R}`. Then (3.3) `δ_Ω(0, E) ≥ (1/2π) log R`.
Modelling: `Ω = ψ(𝔻)` is a plane domain (simply connected, not necessarily a Jordan domain), `∂Ω` its boundary in
the plane, and `δ_Ω(0, E)` is `reducedExtremalDist` of `Ω` and `E` in `ℂ*` (leader ruling C1: any `Ω` and `E`, the
value may be `+∞`, e.g. for `E = ∅`); `R > 0` (for `R ≤ 0` the condition on `E` is empty and `log R` is junk). The
bound was checked against the equation image. -/
theorem thm5_3_5_a {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ unitDisc) (hψi : InjOn ψ unitDisc) (hψ0 : ψ 0 = 0)
    (hψ'0 : deriv ψ 0 = 1) {Ω : Set ℂ} (hΩ : Ω = ψ '' unitDisc) {R : ℝ} (hR : 0 < R) {E : Set ℂ}
    (hE : E ⊆ {ζ ∈ frontier Ω | ENNReal.ofReal R ≤ innerDistGM Ω 0 ζ}) :
    ((1 / (2 * π) * Real.log R : ℝ) : EReal) ≤ reducedExtremalDist (toExt Ω) ((0 : ℂ) : ExtPlane) (toExt E) := by
  sorry

/-- **Theorem 3.5** (Ch. V §3), the equality case. Equality holds in (3.3) if `Ω` is a disc of radius `R`, with radial
slits removed.
Modelling: `E` is the circle of radius `R`, as the last line of the proof says ("when `E` is the circle of radius `R`
and `Ω` is the disc of radius `R` with radial slits removed", P1:7151; every point of that circle has
`dist_Ω(0, ζ) ≥ R`); the slits are finitely many closed radial segments `{t e^{iθ} : a ≤ t ≤ b}`, `0 ≤ a < b ≤ R`
(`IsRadialSlit 0 R`); `ψ` is a normalized univalent function of `𝔻` onto `Ω`, as in (3.3). This hypothesis forces
`Ω` to be simply connected and to contain `0`: the configurations in which a slit does not reach the circle or passes
through `0` admit no such `ψ`, and the others do (for suitable slits the conformal radius at `0` is `1`, with
`R ≥ 1`). -/
theorem thm5_3_5_b {R : ℝ} {n : ℕ} {L : Fin n → Set ℂ} (hL : ∀ j, IsRadialSlit 0 R (L j)) {Ω : Set ℂ}
    (hΩ : Ω = ball 0 R \ ⋃ j, L j) {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ unitDisc) (hψi : InjOn ψ unitDisc)
    (hψ0 : ψ 0 = 0) (hψ'0 : deriv ψ 0 = 1) (hψΩ : ψ '' unitDisc = Ω) :
    reducedExtremalDist (toExt Ω) ((0 : ℂ) : ExtPlane) (toExt (sphere 0 R)) =
      ((1 / (2 * π) * Real.log R : ℝ) : EReal) := by
  sorry

/-- **Corollary 3.6** (Balogh–Bonk; Ch. V §3; cited at P1:7167, in the Notes, P2:421, in Chapter VI, P2:891 "by
Corollary V.3.6", and in App. I, P3:5048). Let `ψ(z)` be a normalized univalent function, `ψ(0) = 0` and `ψ'(0) = 1`, in
`𝔻` and let `λ > 0` [printed "`R > 0`" and "independent of `ψ` and `R`", both P1:7153, misprint]. Then there is a
constant `C`, independent of `ψ` and `λ` [printed "`R`"], such that `Cap {ζ ∈ ∂𝔻 : ∫_0^1 |ψ'(rζ)| dr > λ} ≤ C λ^{−1/2}`.
Modelling: the displayed estimate is in `λ` (equation image checked) and `R` appears only in the proof (`R = λ/K`), so
the statement is read with `λ` (leader ruling C11(2)); `C` is quantified before `ψ` and `λ`; the radial integral
`∫_0^1 |ψ'(rζ)| dr` is a lower integral in `[0, ∞]` (it may be `+∞`); `Cap` is the capacity (4.8) of Ch. III (the set is
Borel); both sides are compared in `[0, ∞]`. -/
theorem cor5_3_6 :
    ∃ C : ℝ, ∀ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ unitDisc → InjOn ψ unitDisc → ψ 0 = 0 → deriv ψ 0 = 1 →
      ∀ lam : ℝ, 0 < lam →
        capacity {ζ ∈ sphere (0 : ℂ) 1 | ENNReal.ofReal lam < ∫⁻ r in Ioo (0 : ℝ) 1, ‖deriv ψ (↑r * ζ)‖ₑ} ≤
          ENNReal.ofReal (C * lam ^ (-(1 / 2 : ℝ))) := by
  sorry

end GarnettMarshall2005
