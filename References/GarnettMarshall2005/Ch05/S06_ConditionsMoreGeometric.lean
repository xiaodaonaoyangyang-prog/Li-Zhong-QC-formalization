import References.GarnettMarshall2005.Ch05.S05_BoundaryConformality

/-!
# Garnett–Marshall, Chapter V §6: Conditions more geometric

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. V §6 (pp. 184–193;
`full.md` of the second part, P2:92–416; the Notes, P2:417, and the Exercises, from P2:427, are not items).

Conventions of the section, as modelled here. The section studies the normalized domain `Ω̃ = {iπ/2 − log w : w ∈ Ω}`
of §5 and its point `+∞`; in the statements `Ω̃` is an arbitrary plane domain, written `Ω`, and the map
`z ↦ ie^{−z}` need not be one-to-one on it (P2:100). The standard strip `𝕊` and the half-strips `S_δ` are those of §5
(`standardStrip`, `halfStrip`). `F_x` is the component of `Ω̃ ∩ {Re z = x}` containing `x` (`verticalSection`). The
region `U_{s,t} = U ∩ {s < Re z < t}` (P2:102, 200) is written out. "Area" is Lebesgue measure `volume` on `ℂ`, in
`[0, ∞]`; areas of such regions enter real inequalities through `ENNReal.toReal` only where they are finite. The limits
"as `s, t → +∞`" are stated in `ε`-form, with the finiteness of the extremal distances `d_Ω̃(F_s, F_t)` as a conjunct.
An `M`-Lipschitz graph is the graph of a function `h : ℝ → ℝ` with `|h(s) − h(t)| ≤ M |s − t|`, i.e.
`LipschitzWith M.toNNReal h` (`M > 0`, P2:134). The triangles of `𝒯_M` are open isosceles triangles together with
their open base on `ℝ` (`lipschitzTriangles`): with the base excluded `Ω̃_M` would not contain `ℝ`, against the book's
"the largest domain with `ℝ ⊆ Ω̃_M`" (P2:156). Lemmas 6.2–6.4 are labelled but stated inside the proof of
Theorem 6.1, and use the proof's objects; the context is made explicit as hypotheses (leader ruling C10): the
hypotheses of Theorem 6.1, the functions `h₁`, `h₂` describing `∂Ω̃_M` (Lemma 6.2), a component `σ` of `∂Ω̃_M \ ∂Ω̃`
and its endpoints (Lemma 6.3, where the disc `B_j` enters through its area), and the assumption (6.4) "during the
remainder of the proof" (P2:190; Lemmas 6.3 and 6.4).

* Definition (angular derivative of `Ω̃` at `+∞`: (5.6) and (5.18), §6, P2:100) — `HasAngularDerivAtInfty`
* Definition (the sets `Ω_{s,t}`, `𝕊_{s,t}` and `U_{s,t}`, §6, P2:102, 200) — omitted: a notation, written out as the
  intersection with the vertical slab between Re z = s and Re z = t wherever it occurs
* Definition (M-Lipschitz graph, §6, P2:134–138) — exists: `LipschitzWith` (the graph of h is an M-Lipschitz graph
  exactly when h is Lipschitz with constant M, for M > 0)
* Definition (the triangles `𝒯_M` and the region `Ω̃_M`, (6.2), §6, P2:142–153) — `lipschitzTriangles`,
  `lipschitzSubregion`
* Unlabelled (§6, P2:156): `Ω̃_M` is the largest domain such that `ℝ ⊆ Ω̃_M ⊆ Ω̃` and `∂Ω̃_M` consists of two
  `M`-Lipschitz graphs — `lipschitzSubregion_isLargest`
* Theorem 6.1 (§6; (6.3)) — `thm5_6_1_a`, `thm5_6_1_b`
* Lemma 6.2 (Sastry, §6) — `lemma5_6_2`
* Lemma 6.3 (§6) — `lemma5_6_3`
* Lemma 6.4 (§6) — `lemma5_6_4`

Helper (not a book notion): `verticalSection` (the set `F_x`, P1:7808, P2:190).

Corrections and readings: the condition (i) of (6.2) is printed "`T ⊂ Ω`" (P2:144), read `T ⊂ Ω̃` [OCR, a dropped
tilde] (inventory C11(9)).

Not stated (inventory U−): the normalized domain `Ω̃` and the restatement "`Ω` has an inner tangent with vertical inner
normal iff (5.6) holds for `Ω̃`, and a positive angular derivative iff (5.6) and (5.18) hold for `Ω̃`" (P2:94–100, the
translation of §5 that motivates the definition; cited only in Exercises V.8, V.9); the area identity
`∫_s^t (π − θ) dx = Area(𝕊_{s,t} \ Ω_{s,t}) − Area(Ω_{s,t} \ 𝕊_{s,t})`, the bounds `π/2 ≤ θ ≤ 2π`, the two-sided
estimate (6.1) and "finite symmetric difference of areas implies (5.26)" (P2:102–132, remarks for the domains of
Corollary 5.8; (6.1) is not cited); "the hypothesis (6.3) is not crucial" and Marshall's example where `M` is small and
(b) fails (P2:182); the steps (6.4)–(6.7) of the proof of Theorem 6.1, including "if both areas are finite then (6.4)
and (5.9) hold", "an angular derivative at `+∞` gives (6.4) by Ostrowski's theorem" and the reformulation (6.5)
(P2:184–196, 336–354; (6.4) is a hypothesis of Lemmas 6.3 and 6.4); "there exist regions that do not satisfy the
hypotheses of Theorem 6.1 but have an angular derivative at `+∞`" (P2:415, Exercise 8).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (toExt)
open Gehring1978 (IsHypSimplyConnectedExt)

/-- The set `F_x` (helper, Ch. V §5–§6, P1:7808, P2:190): the component of `Ω ∩ {Re z = x}` containing the point `x`
(empty when `x ∉ Ω`; only large `x`, with `x ∈ Ω`, are used). -/
def verticalSection (Ω : Set ℂ) (x : ℝ) : Set ℂ :=
  connectedComponentIn (Ω ∩ {z : ℂ | z.re = x}) (x : ℂ)

/-- **Definition** (angular derivative at `+∞`, Ch. V §6, P2:100; cited in Theorem 6.1, in Exercises V.8, V.9,
P2:625–647, and in the index "angular derivative at +∞, 185"). If `Ω̃` is a simply connected domain satisfying (5.6)
and (5.18), we say that `Ω̃` has an angular derivative at `+∞`. Here (5.6) is: for each `δ ∈ (0, π/2)` there is
`x_δ > 0` such that `x_δ + S_δ ⊆ Ω̃`; and (5.18) is: `π d_Ω̃(F_s, F_t) − |s − t| → 0` as `s, t → +∞`. We do not
require that the map `z ↦ e^{−z}` be one-to-one on `Ω̃`.
Modelling: `Ω̃ ⊆ ℂ` (written `Ω`), simply connected in the sense of `Gehring1978.IsHypSimplyConnectedExt`; `F_s` is
`verticalSection`; `d_Ω̃` is `extremalDistGM`; (5.18) in `ε`-form: for every `η > 0` there is `x₀` such that for
all `s, t > x₀` the extremal distance is finite and `|π d_Ω̃(F_s, F_t) − |s − t|| < η`. The formulas (5.6) and (5.18)
were checked against the equation images. -/
def HasAngularDerivAtInfty (Ω : Set ℂ) : Prop :=
  IsHypSimplyConnectedExt (toExt Ω) ∧
    (∀ δ ∈ Ioo 0 (π / 2), ∃ x : ℝ, 0 < x ∧ (fun z => z + (x : ℂ)) '' halfStrip δ ⊆ Ω) ∧
    ∀ η : ℝ, 0 < η → ∃ x₀ : ℝ, ∀ s t : ℝ, x₀ < s → x₀ < t →
      extremalDistGM Ω (verticalSection Ω s) (verticalSection Ω t) < ⊤ ∧
        |π * (extremalDistGM Ω (verticalSection Ω s) (verticalSection Ω t)).toReal - (|s - t|)| < η

/-- **Definition** (the collection `𝒯_M`, (6.2), Ch. V §6, P2:142–150). Suppose `Ω̃` is a region such that
`ℝ ⊆ Ω̃`, and let `M > 0`. `𝒯_M` is the collection of isosceles triangles `T` such that (i) `T ⊆ Ω̃` [OCR: printed
`T ⊂ Ω`], (ii) `T` has base on `ℝ`, and (iii) `T` has sides with slope `±M`.
Modelling: a triangle with base `[c − w, c + w] ⊆ ℝ` (`w > 0`) above (`s = 1`) or below (`s = −1`) the real axis
and apex `c + i s M w`: the points `z` with `|Re z − c| < w` and `0 ≤ s Im z < M (w − |Re z − c|)`, i.e. the open
triangle together with its open base (module docstring); defined for every `Ω` and `M`. -/
def lipschitzTriangles (Ω : Set ℂ) (M : ℝ) : Set (Set ℂ) :=
  {T | ∃ c w s : ℝ, 0 < w ∧ (s = 1 ∨ s = -1) ∧
    T = {z : ℂ | |z.re - c| < w ∧ 0 ≤ s * z.im ∧ s * z.im < M * (w - |z.re - c|)} ∧ T ⊆ Ω}

/-- **Definition** (the region `Ω̃_M`, (6.2), Ch. V §6, P2:152–153; used in Theorem 6.1 and Lemmas 6.2–6.4).
`Ω̃_M = ⋃ {T : T ∈ 𝒯_M}`. -/
def lipschitzSubregion (Ω : Set ℂ) (M : ℝ) : Set ℂ :=
  ⋃₀ lipschitzTriangles Ω M

/-- **Unlabelled** (Ch. V §6, P2:156; the basis of the functions `h₁`, `h₂` of Lemma 6.2, P2:198, and used in the proof
of Lemma 6.4, P2:385, "Because `∂Ω̃_M` is Lipschitz"). `Ω̃_M` is the largest domain such that `ℝ ⊆ Ω̃_M ⊆ Ω̃` and
`∂Ω̃_M` consists of two `M`-Lipschitz graphs.
Modelling: `Ω̃ ⊇ ℝ` is a plane domain (written `Ω`) and `M > 0`; the two graphs are `y = h₁(x) + π/2` and
`y = −h₂(x) − π/2` as in the proof of Theorem 6.1 (P2:198), i.e. `Ω̃_M = {−h₂(x) − π/2 < y < h₁(x) + π/2}` with `h₁`,
`h₂` `M`-Lipschitz; "largest" is among the domains `U` of this form (two `M`-Lipschitz graphs) with `ℝ ⊆ U ⊆ Ω̃`.
[CORRECTION] Added hypothesis: the condition (6.3) of Theorem 6.1, under which the claim is used. The book states it for
any region `Ω̃ ⊇ ℝ`, where it fails (also whenever `Ω̃` contains a half-plane `{±Im z > c}`): for `Ω̃ = ℂ` every
triangle lies in `Ω̃` and `Ω̃_M = ℂ` has no boundary graphs; under (6.3) the upper and lower envelopes of the triangles
are `M`-Lipschitz and bounded by `π/2` at the points `z` with `Re z < 0`, hence finite. -/
theorem lipschitzSubregion_isLargest {Ω : Set ℂ} (hΩ : IsOpen Ω ∧ IsConnected Ω) (hR : ∀ x : ℝ, (x : ℂ) ∈ Ω)
    (h63 : frontier Ω ∩ {z : ℂ | z.re < 0} = frontier standardStrip ∩ {z : ℂ | z.re < 0}) {M : ℝ} (hM : 0 < M) :
    IsOpen (lipschitzSubregion Ω M) ∧ IsConnected (lipschitzSubregion Ω M) ∧
      (∀ x : ℝ, (x : ℂ) ∈ lipschitzSubregion Ω M) ∧ lipschitzSubregion Ω M ⊆ Ω ∧
      (∃ h₁ h₂ : ℝ → ℝ, LipschitzWith M.toNNReal h₁ ∧ LipschitzWith M.toNNReal h₂ ∧
        lipschitzSubregion Ω M = {z : ℂ | -h₂ z.re - π / 2 < z.im ∧ z.im < h₁ z.re + π / 2}) ∧
      ∀ g₁ g₂ : ℝ → ℝ, LipschitzWith M.toNNReal g₁ → LipschitzWith M.toNNReal g₂ →
        (∀ x : ℝ, -g₂ x - π / 2 < 0 ∧ 0 < g₁ x + π / 2) →
        {z : ℂ | -g₂ z.re - π / 2 < z.im ∧ z.im < g₁ z.re + π / 2} ⊆ Ω →
        {z : ℂ | -g₂ z.re - π / 2 < z.im ∧ z.im < g₁ z.re + π / 2} ⊆ lipschitzSubregion Ω M := by
  sorry

/-- **Theorem 6.1** (Ch. V §6), part (a) (cited at P2:393–413, in the Notes, P2:425, and in Exercises V.8, V.9,
P2:625, 627, 647; Chapter VI, P2:941, refers to its own Theorem 6.1). Suppose `Ω̃ ⊇ ℝ` is a simply connected domain
such that (6.3) `∂Ω̃ ∩ {Re z < 0} = ∂𝕊 ∩ {Re z < 0}`. Let `Ω̃_M ⊆ Ω̃` be the region defined by (6.2). Suppose
`Area(𝕊 \ Ω̃_M) < ∞`. Then `Ω̃` has an angular derivative at `+∞` if and only if `Area(Ω̃_M \ 𝕊) < ∞`.
Modelling: `Ω̃ ⊆ ℂ` (written `Ω`) with `Gehring1978.IsHypSimplyConnectedExt (toExt Ω)`; `M > 0` ("Let `M > 0`",
P2:134); frontiers in `ℂ`; areas in `[0, ∞]`. The formula (6.3) was checked against the equation image. -/
theorem thm5_6_1_a {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) (hR : ∀ x : ℝ, (x : ℂ) ∈ Ω)
    (h63 : frontier Ω ∩ {z : ℂ | z.re < 0} = frontier standardStrip ∩ {z : ℂ | z.re < 0}) {M : ℝ} (hM : 0 < M)
    (hA : volume (standardStrip \ lipschitzSubregion Ω M) < ⊤) :
    HasAngularDerivAtInfty Ω ↔ volume (lipschitzSubregion Ω M \ standardStrip) < ⊤ := by
  sorry

/-- **Theorem 6.1** (Ch. V §6), part (b). In the situation of `thm5_6_1_a`, suppose `Area(Ω̃_M \ 𝕊) < ∞`. Then `Ω̃`
has an angular derivative at `+∞` if and only if `Area(𝕊 \ Ω̃_M) < ∞`, provided that `M > 8π`.
Modelling: as in `thm5_6_1_a`. -/
theorem thm5_6_1_b {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) (hR : ∀ x : ℝ, (x : ℂ) ∈ Ω)
    (h63 : frontier Ω ∩ {z : ℂ | z.re < 0} = frontier standardStrip ∩ {z : ℂ | z.re < 0}) {M : ℝ} (hM : 8 * π < M)
    (hA : volume (lipschitzSubregion Ω M \ standardStrip) < ⊤) :
    HasAngularDerivAtInfty Ω ↔ volume (standardStrip \ lipschitzSubregion Ω M) < ⊤ := by
  sorry

/-- **Lemma 6.2** (Sastry, Ch. V §6; stated in the proof of Theorem 6.1 and used at P2:196, 393, 401). Suppose that
`∂Ω̃_M` is given by the two curves `y = h₁(x) + π/2` and `y = −h₂(x) − π/2`, `−∞ < x < +∞`, where `h₁ > −π/2` and
`h₂ > −π/2`, and let `U_{s,t} = U ∩ {s < Re z < t}`. Suppose `|h_j(x)| ≤ πM²` for `s < x < t`. Then
`d_Ω̃(F_s, F_t) − (t − s)/π ≤ (4M² + 2) Area(𝕊 \ Ω̃_M)_{s,t}/π² − Area(Ω̃_M \ 𝕊)_{s,t}/((4M² + 2)π²)`.
Modelling: the context is explicit (leader ruling C10): the hypotheses of Theorem 6.1 (`Ω̃ ⊆ ℂ` written `Ω`, `M > 0`),
and `h₁`, `h₂` with `Ω̃_M = {−h₂(x) − π/2 < y < h₁(x) + π/2}` and `h_j > −π/2` (they exist by
`lipschitzSubregion_isLargest`); `s < t`; `F_s` is `verticalSection`; `d_Ω̃` is `extremalDistGM`, finite here (a
conjunct); the two areas are finite, since the regions lie in the bounded set `{s < Re z < t, |Im z| < π/2 + πM²}`, so
`ENNReal.toReal` sees no junk. The assumption (6.4) of the rest of the proof is not used. The inequality was checked
against the equation image. -/
theorem lemma5_6_2 {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) (hR : ∀ x : ℝ, (x : ℂ) ∈ Ω)
    (h63 : frontier Ω ∩ {z : ℂ | z.re < 0} = frontier standardStrip ∩ {z : ℂ | z.re < 0}) {M : ℝ} (hM : 0 < M)
    {h₁ h₂ : ℝ → ℝ} (hh₁ : ∀ x : ℝ, -(π / 2) < h₁ x) (hh₂ : ∀ x : ℝ, -(π / 2) < h₂ x)
    (hΩM : lipschitzSubregion Ω M = {z : ℂ | -h₂ z.re - π / 2 < z.im ∧ z.im < h₁ z.re + π / 2}) {s t : ℝ}
    (hst : s < t) (hbd : ∀ x ∈ Ioo s t, |h₁ x| ≤ π * M ^ 2 ∧ |h₂ x| ≤ π * M ^ 2) :
    extremalDistGM Ω (verticalSection Ω s) (verticalSection Ω t) < ⊤ ∧
      (extremalDistGM Ω (verticalSection Ω s) (verticalSection Ω t)).toReal - (t - s) / π ≤
        (4 * M ^ 2 + 2) *
            (volume ((standardStrip \ lipschitzSubregion Ω M) ∩ {z : ℂ | s < z.re ∧ z.re < t})).toReal / π ^ 2 -
          (volume ((lipschitzSubregion Ω M \ standardStrip) ∩ {z : ℂ | s < z.re ∧ z.re < t})).toReal /
            ((4 * M ^ 2 + 2) * π ^ 2) := by
  sorry

/-- **Lemma 6.3** (Ch. V §6; stated in the proof of Theorem 6.1 and used at P2:286, 342). Write
`∂Ω̃_M \ ∂Ω̃ = ⋃_j σ_j` where each `σ_j` is an open arc with endpoints `z_j^l, z_j^r ∈ ∂Ω̃`, `Re z_j^l < Re z_j^r`. If
`|Im z_j^l| ≤ |Im z_j^r|`, let `B_j = {z : |z − z_j^l| < Re z_j^r − Re z_j^l}`; otherwise let
`B_j = {z : |z − z_j^r| < Re z_j^r − Re z_j^l}`. Then `Area(B_j) ≤ (8π/M) ∫_{z ∈ σ_j} ||Im z| − π/2| dx`,
`z = x + iy`.
Modelling: the context is explicit (leader ruling C10): the hypotheses of Theorem 6.1 (`Ω̃` written `Ω`, `M > 0`) and
the assumption (6.4) `lim_{Re z → +∞, z ∈ ∂Ω̃_M} dist(z, ∂𝕊) = 0` (P2:187–190, standing for the rest of the proof); `σ`
is a component of `∂Ω̃_M \ ∂Ω̃`, the open arc over `(Re z^l, Re z^r)` of a function `g` continuous on the closed
interval, with endpoints `z^l = Re z^l + i g(Re z^l)` and `z^r = Re z^r + i g(Re z^r)` in `∂Ω̃` (a component of the
boundary graphs of `Ω̃_M` is such an arc); `∫_{z ∈ σ} ||Im z| − π/2| dx` is `∫ ||g(x)| − π/2| dx` over
`(Re z^l, Re z^r)`; `B_j` is the open disc as printed, its area in `[0, ∞]` (finite). The inequality was checked against
the equation image. -/
theorem lemma5_6_3 {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) (hR : ∀ x : ℝ, (x : ℂ) ∈ Ω)
    (h63 : frontier Ω ∩ {z : ℂ | z.re < 0} = frontier standardStrip ∩ {z : ℂ | z.re < 0}) {M : ℝ} (hM : 0 < M)
    (h64 : Tendsto (fun z => infDist z (frontier standardStrip))
      (comap Complex.re atTop ⊓ 𝓟 (frontier (lipschitzSubregion Ω M))) (𝓝 0))
    {σ : Set ℂ} (hσ : ∃ z ∈ frontier (lipschitzSubregion Ω M) \ frontier Ω,
      connectedComponentIn (frontier (lipschitzSubregion Ω M) \ frontier Ω) z = σ)
    {zl zr : ℂ} (hzl : zl ∈ frontier Ω) (hzr : zr ∈ frontier Ω) (hlr : zl.re < zr.re) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc zl.re zr.re)) (hgl : zl = (zl.re : ℂ) + (g zl.re : ℂ) * I)
    (hgr : zr = (zr.re : ℂ) + (g zr.re : ℂ) * I)
    (hσg : σ = {z : ℂ | z.re ∈ Ioo zl.re zr.re ∧ z.im = g z.re}) :
    (volume (ball (if |zl.im| ≤ |zr.im| then zl else zr) (zr.re - zl.re))).toReal ≤
      8 * π / M * ∫ x in zl.re..zr.re, |(|g x| - π / 2)| := by
  sorry

/-- **Lemma 6.4** (Ch. V §6; stated in the proof of Theorem 6.1 and used at P2:196, 357, 391, 407). If `ε > 0` there
is an `s₀ < ∞` so that for `s₀ < s < t < ∞`
`d_Ω̃(F_s, F_t) − (t − s)/π ≥ (M − 8π) Area(𝕊 \ Ω̃_M)_{s,t}/(Mπ²) − (M + 8π) Area(Ω̃_M \ 𝕊)_{s,t}/(Mπ²) − ε`.
Modelling: the context is explicit (leader ruling C10): the hypotheses of Theorem 6.1 (`Ω̃` written `Ω`, `M > 0`) and
the assumption (6.4) (as in `lemma5_6_3`); `F_s` is `verticalSection`; for `s₀ < s < t` the extremal distance and the
area `Area(Ω̃_M \ 𝕊)_{s,t}` are finite (conjuncts: by (6.4) the graphs of `∂Ω̃_M` are bounded for large `x`), and
`Area(𝕊 \ Ω̃_M)_{s,t} ≤ π (t − s)` is finite anyway, so `ENNReal.toReal` sees no junk. The inequality was checked
against the equation image. -/
theorem lemma5_6_4 {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) (hR : ∀ x : ℝ, (x : ℂ) ∈ Ω)
    (h63 : frontier Ω ∩ {z : ℂ | z.re < 0} = frontier standardStrip ∩ {z : ℂ | z.re < 0}) {M : ℝ} (hM : 0 < M)
    (h64 : Tendsto (fun z => infDist z (frontier standardStrip))
      (comap Complex.re atTop ⊓ 𝓟 (frontier (lipschitzSubregion Ω M))) (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ s₀ : ℝ, ∀ s t : ℝ, s₀ < s → s < t →
      extremalDistGM Ω (verticalSection Ω s) (verticalSection Ω t) < ⊤ ∧
        volume ((lipschitzSubregion Ω M \ standardStrip) ∩ {z : ℂ | s < z.re ∧ z.re < t}) < ⊤ ∧
        (M - 8 * π) * (volume ((standardStrip \ lipschitzSubregion Ω M) ∩ {z : ℂ | s < z.re ∧ z.re < t})).toReal /
              (M * π ^ 2) -
            (M + 8 * π) *
                (volume ((lipschitzSubregion Ω M \ standardStrip) ∩ {z : ℂ | s < z.re ∧ z.re < t})).toReal /
              (M * π ^ 2) - ε ≤
          (extremalDistGM Ω (verticalSection Ω s) (verticalSection Ω t)).toReal - (t - s) / π := by
  sorry

end GarnettMarshall2005
