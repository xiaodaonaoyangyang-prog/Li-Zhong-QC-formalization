import References.Pommerenke1992.Ch01.S05_SomeUnivalenceCriteria
import LiZhongQC.ClusterSets

/-!
# Pommerenke 1992, Ch. 2 §2.2 Local Connection

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §2.2; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 1002–1145.

* Definition (locally connected closed set, (2.2.1); its spherical form) — `IsLocConn`, `IsLocConnSph`
* Unlabelled (§2.2, l. 1012: every curve is locally connected; cited in the proof of Theorem 2.1) —
  `curve_isLocConn`
* Theorem 2.1 — `thm2_1`
* Hahn–Mazurkiewicz theorem (quoted, §2.2) — exists: `LiZhongQC.hahn_mazurkiewicz`
  `LiZhongQC.hahn_mazurkiewicz_subset` (a Hausdorff space, resp. a nonempty set K ⊆ ℂ, is a continuous image of a
  segment if and only if it is a Peano continuum, resp. compact, connected and locally connected; for a compact
  metric space, topological local connectedness is the uniform local connectedness by continua of the book, a
  standard fact that the project does not state)
* Definition (the length `Λ(h(C(r)))` of the image of the circular arcs `C(r)`, §2.2) — `imageCircleLength`
* Proposition 2.2 (Wolff's lemma) — `prop2_2`
* Formula (2.2.6) (stated in the proof of Proposition 2.2; cited as a result, by number, in the proof of Theorem 2.16,
  l. 1504) — `eq2_2_6`
* Definition (uniformly locally connected sequence of closed sets, §2.2) — `IsUnifLocConn`
* Proposition 2.3 — `prop2_3`
* Definition (equicontinuous sequence in the closed disc, §2.2) — exists: `UniformEquicontinuousOn` (Mathlib; for
  maps into ℂ this is the book's ε–ρ definition, with ρ independent of n)
* Arzelà–Ascoli theorem (quoted, §2.2) — exists: `BoundedContinuousFunction.arzela_ascoli` (Mathlib: a set of
  bounded continuous functions on a compact space with values in a compact set, equicontinuous at every point, has a
  compact closure in the uniform metric; since this space is metric, a uniformly bounded equicontinuous sequence has
  a uniformly convergent subsequence)
* Corollary 2.4 — `cor2_4`

Not items (DESIGN §3): the facts quoted from Newman on continuous images and finite unions of locally connected sets
(l. 1012–1014, not cited); the comb domain (2.2.2) (an example); the conformal parametrization (2.2.3) of `∂G`
(notation, written out in the statements); the converse of Corollary 2.4 quoted from Pom75 (not cited).

**Standing assumption of §2.2–2.3** (l. 1004): `G` is a bounded domain of `ℂ`; "everything carries over to domains of
`Ĉ` with the spherical metric", which is the form of the overview theorems of §2.1 (file `S01_Overview`). A conformal
map of `𝔻` onto `G` is `LiZhongQC.IsConformalOnto`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane unitDisc IsConformalOnto)

/-- **Definition (2.2.1)** (§2.2). The closed set `A ⊆ ℂ` is locally connected: for every `ε > 0` there is `δ > 0`
such that for any two points `a, b ∈ A` with `|a - b| < δ` there is a continuum `B` with `a, b ∈ B ⊆ A` and
`diam B < ε`.
Modelling: "two points" are distinct, so `B` (compact, connected, containing both) has more than one point. For a
non-compact `A` (such as `ℂ ∖ G` in Theorem 2.1) this uniform notion is stronger than Mathlib's
`LocallyConnectedSpace`. -/
def IsLocConn (A : Set ℂ) : Prop :=
  IsClosed A ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ‖a - b‖ < δ →
    ∃ B ⊆ A, IsCompact B ∧ IsConnected B ∧ a ∈ B ∧ b ∈ B ∧ diam B < ε

/-- **Definition** (§2.2, l. 1004, the spherical form of (2.2.1)). The closed set `A ⊆ Ĉ` is locally connected for
the chordal metric `d#`: for every `ε > 0` there is `δ > 0` such that any two points `a ≠ b` of `A` with
`d#(a, b) < δ` lie in a continuum `B ⊆ A` with `diam# B < ε`. -/
def IsLocConnSph (A : Set ExtPlane) : Prop :=
  IsClosed A ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ a ∈ A, ∀ b ∈ A, a ≠ b → chordalDist a b < δ →
    ∃ B ⊆ A, IsContinuum B ∧ a ∈ B ∧ b ∈ B ∧ chordalDiam B < ε

/-- **Unlabelled claim** (§2.2, l. 1012; cited in the proof of Theorem 2.1). Every curve is locally connected (as the
continuous image of a segment). -/
theorem curve_isLocConn (C : Curve ℂ) : IsLocConn C.trace := by
  sorry

/-- **Theorem 2.1** (§2.2). Let `f` map `𝔻` conformally onto the bounded domain `G`. Then the following four
conditions are equivalent: (i) `f` has a continuous extension to `𝔻̄`; (ii) `∂G` is a curve, that is
`∂G = {φ(ζ) : ζ ∈ 𝕋}` with continuous `φ`; (iii) `∂G` is locally connected; (iv) `ℂ ∖ G` is locally connected.
(The project's `LiZhongQC.caratheodory_continuous_iff` has (i)–(iii) only.) -/
theorem thm2_1 {G : Set ℂ} (hG : Bornology.IsBounded G) {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc G) :
    List.TFAE
      [∃ F : ℂ → ℂ, ContinuousOn F (closedBall 0 1) ∧ EqOn F f unitDisc,
        ∃ φ : ℂ → ℂ, ContinuousOn φ (sphere 0 1) ∧ φ '' sphere 0 1 = frontier G,
        IsLocConn (frontier G),
        IsLocConn Gᶜ] := by
  sorry

/-- **Definition** (§2.2; the length `Λ(h(C(r)))` of Proposition 2.2). The length of the image under a conformal
map `h` of the arcs `C(r) = H ∩ {|z - c| = r}` of the circle about `c` of radius `r`:
`∫_{C(r)} |h'(z)| |dz| = ∫ |h'(c + r e^{it})| r dt` over the `t ∈ (-π, π]` with `c + r e^{it} ∈ H`. For conformal
`h` this is the total length (1.1.7) of the image curves. -/
def imageCircleLength (h : ℂ → ℂ) (H : Set ℂ) (c : ℂ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in {t : ℝ | t ∈ Ioc (-π) π ∧ c + r * exp (t * I) ∈ H}, ‖deriv h (c + r * exp (t * I))‖ₑ * ENNReal.ofReal r

/-- **Proposition 2.2** (§2.2; Wolff's lemma). Let `h` map the open set `H ⊆ ℂ` conformally into `D(0, R)`. If
`c ∈ ℂ` and `C(r) = H ∩ {|z - c| = r}`, then (2.2.4) `inf_{ρ < r < √ρ} Λ(h(C(r))) ≤ 2πR/√(log 1/ρ)` for `0 < ρ < 1`,
so that there is a decreasing sequence `rₙ → 0` with (2.2.5) `Λ(h(C(rₙ))) → 0` as `n → ∞`.
Modelling: `Λ(h(C(r)))` is `imageCircleLength h H c r`; "conformally into" is analytic and injective. -/
theorem prop2_2 {H : Set ℂ} (hH : IsOpen H) {R : ℝ} (hR : 0 < R) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h H)
    (hinj : InjOn h H) (hmaps : MapsTo h H (ball 0 R)) (c : ℂ) :
    (∀ ρ ∈ Ioo (0 : ℝ) 1,
      ⨅ r ∈ Ioo ρ (Real.sqrt ρ), imageCircleLength h H c r ≤
        ENNReal.ofReal (2 * π * R / Real.sqrt (Real.log (1 / ρ)))) ∧
      ∃ r : ℕ → ℝ, StrictAnti r ∧ (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
        Tendsto (fun n => imageCircleLength h H c (r n)) atTop (𝓝 0) := by
  sorry

/-- **Formula (2.2.6)** (§2.2; stated in the proof of Proposition 2.2 and cited by number, as a result, in the proof
of Theorem 2.16, l. 1504). If `h` maps the open set `H ⊆ ℂ` conformally into `ℂ` and `l(r) = Λ(h(C(r)))`,
`C(r) = H ∩ {|z - c| = r}`, then `∫₀^∞ l(r)² dr/r ≤ 2π ∬_H |h'(z)|² dx dy = 2π area h(H)`.
Modelling: lower integrals in `ℝ≥0∞`; "conformally" is analytic and injective. -/
theorem eq2_2_6 {H : Set ℂ} (hH : IsOpen H) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h H) (hinj : InjOn h H) (c : ℂ) :
    ∫⁻ r in Ioi 0, imageCircleLength h H c r ^ 2 / ENNReal.ofReal r ≤
        2 * ENNReal.ofReal π * ∫⁻ z in H, ‖deriv h z‖ₑ ^ 2 ∧
      ∫⁻ z in H, ‖deriv h z‖ₑ ^ 2 = volume (h '' H) := by
  sorry

/-- **Definition** (§2.2). The closed sets `Aₙ ⊆ ℂ` are uniformly locally connected: for every `ε > 0` there is
`δ > 0`, independent of `n`, such that any two points `aₙ, bₙ ∈ Aₙ` with `|aₙ - bₙ| < δ` can be joined by continua
`Bₙ ⊆ Aₙ` of diameter `< ε`. (Two points are distinct, as in `IsLocConn`.) -/
def IsUnifLocConn (A : ℕ → Set ℂ) : Prop :=
  (∀ n, IsClosed (A n)) ∧ ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ n, ∀ a ∈ A n, ∀ b ∈ A n, a ≠ b → ‖a - b‖ < δ →
    ∃ B ⊆ A n, IsCompact B ∧ IsConnected B ∧ a ∈ B ∧ b ∈ B ∧ diam B < ε

/-- **Proposition 2.3** (§2.2). Let `fₙ` map `𝔻` conformally onto `Gₙ` such that `fₙ(0) = 0`. Suppose that (2.2.10)
`D(0, R₀) ⊆ Gₙ ⊆ D(0, R)` for all `n`. If `ℂ ∖ Gₙ` is uniformly locally connected, then the functions `fₙ` are
equicontinuous in `𝔻̄`.
Modelling: the `fₙ` on `𝔻̄` are their continuous extensions (Theorem 2.1); equicontinuity is Mathlib's
`UniformEquicontinuousOn`. -/
theorem prop2_3 {f : ℕ → ℂ → ℂ} {G : ℕ → Set ℂ} (hf : ∀ n, IsConformalOnto (f n) unitDisc (G n))
    (hf0 : ∀ n, f n 0 = 0) {R₀ R : ℝ} (hR₀ : 0 < R₀) (hG : ∀ n, ball 0 R₀ ⊆ G n ∧ G n ⊆ ball 0 R)
    (hulc : IsUnifLocConn fun n => (G n)ᶜ) :
    ∃ F : ℕ → ℂ → ℂ, (∀ n, ContinuousOn (F n) (closedBall 0 1) ∧ EqOn (F n) (f n) unitDisc) ∧
      UniformEquicontinuousOn F (closedBall 0 1) := by
  sorry

/-- **Corollary 2.4** (§2.2). Let `fₙ` map `𝔻` conformally onto `Gₙ` with `fₙ(0) = 0`. Suppose that (2.2.10) holds
and that `ℂ ∖ Gₙ` is uniformly locally connected. If (2.2.11) `fₙ(z) → f(z)` as `n → ∞` for each `z ∈ 𝔻`, then the
convergence is uniform in `𝔻̄`.
Modelling: on `𝔻̄` the `fₙ` are their continuous extensions, and `f` has a continuous extension to which they
converge uniformly. -/
theorem cor2_4 {f : ℕ → ℂ → ℂ} {G : ℕ → Set ℂ} (hf : ∀ n, IsConformalOnto (f n) unitDisc (G n))
    (hf0 : ∀ n, f n 0 = 0) {R₀ R : ℝ} (hR₀ : 0 < R₀) (hG : ∀ n, ball 0 R₀ ⊆ G n ∧ G n ⊆ ball 0 R)
    (hulc : IsUnifLocConn fun n => (G n)ᶜ) {f₀ : ℂ → ℂ}
    (hlim : ∀ z ∈ unitDisc, Tendsto (fun n => f n z) atTop (𝓝 (f₀ z))) :
    ∃ F : ℕ → ℂ → ℂ, ∃ F₀ : ℂ → ℂ, (∀ n, ContinuousOn (F n) (closedBall 0 1) ∧ EqOn (F n) (f n) unitDisc) ∧
      EqOn F₀ f₀ unitDisc ∧ TendstoUniformlyOn F F₀ atTop (closedBall 0 1) := by
  sorry

end Pommerenke1992
