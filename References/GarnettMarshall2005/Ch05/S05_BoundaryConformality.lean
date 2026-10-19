import References.GarnettMarshall2005.Ch05.S04_TeichmullerModulsatz

/-!
# Garnett–Marshall, Chapter V §5: Boundary conformality and angular derivatives

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. V §5 (pp. 173–184;
`full.md` P1:7499–7873, continued in the second part, P2:1–91; the seam lies inside the proof of Theorem 5.7).

Conventions of the section, as modelled here. Domains are plane domains `Ω ⊆ ℂ` and `ζ ∈ ∂Ω` is a finite boundary
point (frontier in `ℂ`). "Simply connected domain" is `Gehring1978.IsHypSimplyConnectedExt (toExt Ω)` (§4). A
conformal mapping `F : Ω → Ω'` is `LiZhongQC.IsConformalOnto F Ω Ω'`, and `F⁻¹` is `Function.invFunOn F Ω` (the
inverse on `Ω'`). The truncated cone `Γ^ε_β(ζ, θ)` is `truncatedCone`, with `|arg(z − ζ) − θ| < β` read modulo `2π`.
The inner normal `e^{iθ}` of an inner tangent is a parameter `θ` of the notions (it need not be unique, and the book
fixes one, P1:7526); "vertical inner normal" is `θ = π/2`. A limit "`Γ^ε_β(ζ) ∋ z → ζ`" is a limit along the filter
`𝓝[Γ^1_β(ζ, θ)] ζ` (it does not depend on the truncation `ε`) for every `β ∈ (0, π/2)`. The limit of
`arg((F(z) − F(ζ))/(z − ζ))` in (5.2) is the limit of the direction `q/|q| → e^{iA}` of the quotient `q`, as for
Pommerenke's `Pommerenke1992.IsIsogonalAt` (inventory C4; equivalent to the limit of a continuous branch of `arg q` on
the connected cone, the angle `A` being determined modulo `2π`). The section opens with "Let Ω be a simply
connected domain" (P1:7501); Definitions 5.1–5.3, Lemma 5.4 and the unlabelled claims of P1:7554 and P1:7586 are
stated for every plane domain (open and connected), since the notions and the claims are local at `ζ`; every
later use has a simply connected `Ω` (mostly `𝔻`).

The GM notions carry the suffix `GM`, since the names clash with Pommerenke's (inventory C4): GM's "conformal at `ζ`"
(Definition 5.2, `IsConformalAtGM`) is Pommerenke's isogonality (`Pommerenke1992.IsIsogonalAt`), while Pommerenke's
`Pommerenke1992.IsConformalAtBoundary` is GM's "non-zero angular derivative" (`HasAngularDerivGM` with `L ≠ 0`).
Pommerenke's notions are for the unit disc and Stolz angles only.

Standing assumption for the rest of §5 (P1:7614–7624): `φ : ℍ → Ω` is a conformal map onto a domain `Ω` with
`0 ∈ ∂Ω`, and `φ` has the nontangential limit (5.4) `lim_{Γ_α(0) ∋ z → 0} φ(z) = 0`. Each statement below carries
it explicitly (`IsConformalOnto φ upperHalf Ω`, `HasNontangentialLimitAt upperHalf 0 (π / 2) φ 0`: `ℍ` has an inner
tangent with vertical inner normal at `0`).

* Definition (truncated cone `Γ^ε_β(ζ, θ)`, §5, P1:7509–7513) — `truncatedCone`
* Definition 5.1 (inner tangent, inner normal `e^{iθ}`, vertical inner normal, §5; (5.1)) — `HasInnerTangent`
* Definition (nontangential limit at a point where the boundary has an inner tangent, §5, P1:7532–7538) —
  `HasNontangentialLimitAt` (B-cand. the disc notion HasNontangentialLimit of Ch. I §2, Stolz cones at a point of the
  unit circle, and Pommerenke1992.HasAngularLimit; for the disc the cones are comparable)
* Definition 5.2 (conformal at a boundary point, §5; (5.2)) — `IsConformalAtGM` (B-cand. Pommerenke1992.IsIsogonalAt,
  the same notion for the unit disc and Stolz angles)
* Unlabelled (§5, P1:7554): if `F` is conformal at `ζ`, then `∂F(Ω)` has an inner tangent at `F(ζ)` and `F⁻¹` is
  conformal at `F(ζ)` — `isConformalAtGM_image`
* Unlabelled (§5, P1:7554): if `Ω` is a Jordan domain, `F : 𝔻 → Ω` is conformal and `∂Ω` has a tangent at `F(ζ)`,
  then (by the tangent theorem of Ch. II §4) `F` is conformal at `ζ`, with an unrestricted limit —
  `isConformalAtGM_of_hasTangent`
  (B-cand. Pommerenke1992.eq4_3_7, tangent implies isogonal for a locally connected boundary)
* Definition 5.3 (angular derivative, §5; (5.3)) — `HasAngularDerivGM` (B-cand. Pommerenke1992.HasAngularDerivative,
  the disc form with values in the extended plane; Pommerenke1992.IsConformalAtBoundary is its non-zero finite case)
* Lemma 5.4 (§5) — `lemma5_5_4` (B-cand. Pommerenke1992.prop4_7, the disc form)
* Unlabelled (§5, P1:7586): a non-zero angular derivative `F'(ζ)` makes `F` conformal at `ζ` with `A_ζ = arg F'(ζ)`,
  and `F⁻¹` has the non-zero angular derivative `1/F'(ζ)` at `F(ζ)` — `isConformalAtGM_of_hasAngularDerivGM`
  (B-cand. Pommerenke1992.eq4_3_6, conformal implies isogonal on the disc)
* Definition (the standard strip `𝕊` and the half-strips `S_δ`, §5, P1:7626–7648) — `standardStrip`, `halfStrip`
* Theorem 5.5 (Ostrowski, §5; (5.7)) — `thm5_5_5_a`, `thm5_5_5_b`
* Definition 5.6 (positive angular derivative at `0`, §5) — `HasPositiveAngularDeriv`
* Theorem 5.7 (Jenkins–Oikawa, Rodin–Warschawski, §5; (5.16)) — `thm5_5_7`
* Corollary 5.8 (§5; (5.24)) — `cor5_5_8`

Helper (not a book notion): `circleSection` (the set `E_r` of Theorem 5.7).

Not stated (inventory U−): the introduction of the section (P1:7501–7507); the non-uniqueness of the inner normal (at a
slit, and `𝔻 ∩ {0 < arg z < 3π/2}` at `0`) and "we fix one `e^{iθ}`" (P1:7526–7530; the normal is the parameter `θ`);
the remark that for `F` conformal at `ζ` and `|α − θ| < π/2` the image of the ray `{arg(z − ζ) = α}` is asymptotic to
the ray `{arg(w − F(ζ)) = α + A_ζ}`, "`F` preserves angles between nontangential rays" (P1:7554; the use in Chapter VI,
P2:838, that nontangential limits correspond under a map conformal at a point, follows from Definition 5.2 and
`isConformalAtGM_image`); "`F` can be conformal at `ζ ∈ ∂𝔻` even when `Γ` does not have a tangent at `F(ζ)`"
(P1:7554, Exercise VII.12 or Theorem 5.5); "`F` can be conformal at `ζ` without having an angular derivative"
(P1:7586, Exercise VI.8); the functions `f_ε`, and "for `F` conformal at `0` with vertical inner normal, `F` has an
angular derivative at `0` if and only if the vertical limit `lim (F(εi) − F(0))/(εi)` exists" (P1:7588–7612; cited
only in the hint of Exercise V.5, P2:573); the strip dictionary (P1:7626–7666: `τ(z) = ie^{−z}`, the map `ψ` of
(5.5), the domain `Ω̃`, and the translations of (5.4), (5.2) and of the inner tangent into conditions on `ψ` and
`Ω̃`, used as tools in the proofs; the condition (5.6) enters the definition of an angular derivative at `+∞` in §6);
the comb of Figure V.5 (P1:7681); "the existence of a non-zero angular derivative depends on the domain and not on the
choice of the conformal map" and its history (P1:7773, the motivation of Definition 5.6, which quantifies over the
map); under the Ostrowski condition (5.7), Theorem 5.7 holds with (b) replaced by (b') along `2^{−m}`, `2^{−n}`
(P1:7785–7791, proved in Exercise 5); "Exercises 4 and 5 include proofs of (5.21) without Teichmüller's Modulsatz"
and the smooth case (P2:32); "a related result can be found in Rodin and Warschawski [1976]" (P2:54). (5.8)–(5.23)
are steps of the proofs of Theorems 5.5 and 5.7, and (5.25), (5.26) steps of the proof of Corollary 5.8.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt unitDisc upperHalf IsConformalOnto)
open Gehring1978 (IsHypSimplyConnectedExt)

/-- **Definition** (truncated cone, Ch. V §5, P1:7509–7513; used in V §5–§6 and Chapter VI). Let `ζ ∈ ℂ`. For
`θ ∈ [0, 2π)`, `β ∈ (0, π/2)` and `ε > 0`, the truncated cone is
`Γ^ε_β(ζ, θ) = {z : |arg(z − ζ) − θ| < β, 0 < |z − ζ| < ε}`.
Modelling: `|arg(z − ζ) − θ| < β` is read modulo `2π`, as `|arg((z − ζ) e^{−iθ})| < β` with the principal argument
(the angular distance between the direction of `z − ζ` and `e^{iθ}`); `θ` is any real number (only `e^{iθ}` matters);
the set is defined for all `β`, `ε` and used for `β ∈ (0, π/2)`, `ε > 0`. -/
def truncatedCone (ζ : ℂ) (θ β ε : ℝ) : Set ℂ :=
  {z | |arg ((z - ζ) * Complex.exp (-((θ : ℂ) * I)))| < β ∧ 0 < ‖z - ζ‖ ∧ ‖z - ζ‖ < ε}

/-- **Definition 5.1** (Ch. V §5; cited passim in V §5–§6, in Chapter VI, P2:805, 941, 971, 987, 1108, and in
Chapter VII, P2:2272). We say that `∂Ω` has an inner tangent with inner normal `e^{iθ}` at `ζ ∈ ∂Ω` if for every
`β ∈ (0, π/2)` there is an `ε = ε(β) > 0` so that (5.1) `Γ^ε_β(ζ, θ) ⊆ Ω`. When `θ = π/2` we say `∂Ω` has vertical
inner normal.
Modelling: `Ω ⊆ ℂ`; `ζ ∈ ∂Ω` (the frontier in `ℂ`) is part of the definition; the inner normal is the parameter
`θ`, and "vertical inner normal" is `θ = π/2`. -/
def HasInnerTangent (Ω : Set ℂ) (ζ : ℂ) (θ : ℝ) : Prop :=
  ζ ∈ frontier Ω ∧ ∀ β ∈ Ioo 0 (π / 2), ∃ ε > 0, truncatedCone ζ θ β ε ⊆ Ω

/-- **Definition** (nontangential limit, Ch. V §5, P1:7532–7538). If `∂Ω` has an inner tangent at `ζ` (with the fixed
inner normal `e^{iθ}`) and if `lim_{Γ^ε_β(ζ) ∋ z → ζ} f(z) = A`, we say the function `f` has nontangential limit `A` at
`ζ`.
Modelling: the limit is required for every `β ∈ (0, π/2)` (the cones of Definition 5.1), along the filter
`𝓝[Γ^1_β(ζ, θ)] ζ`; the truncation does not change the filter, and near `ζ` the cone lies in `Ω` (by the inner
tangent), so values of `f` off `Ω` are not seen. Near miss: `HasNontangentialLimit` of Ch. I §2 is the disc notion
(Stolz cones `Γ_α(ζ)` at `ζ ∈ ∂𝔻`); for `Ω = 𝔻` and `e^{iθ} = −ζ` the two families of cones are comparable (a
comparison lemma, not a renaming). -/
def HasNontangentialLimitAt {V : Type*} [TopologicalSpace V] (Ω : Set ℂ) (ζ : ℂ) (θ : ℝ) (f : ℂ → V) (A : V) :
    Prop :=
  HasInnerTangent Ω ζ θ ∧ ∀ β ∈ Ioo 0 (π / 2), Tendsto f (𝓝[truncatedCone ζ θ β 1] ζ) (𝓝 A)

/-- **Definition 5.2** (conformal at a boundary point, Ch. V §5; cited in Chapter VI, P2:838, 941, 971, 1081, in
Chapter VII, P2:2272, and in the index "conformal at a boundary point, 174"). Suppose `F : Ω → Ω'` is a conformal
mapping and suppose `∂Ω` has an inner tangent at `ζ ∈ ∂Ω`. We say `F` is conformal at `ζ` if `F` has a nontangential
limit `F(ζ) ≡ lim_{Γ^ε_β(ζ) ∋ z → ζ} F(z)` and if the limit
(5.2) `A_ζ = lim_{Γ^ε_β(ζ) ∋ z → ζ} arg((F(z) − F(ζ))/(z − ζ))` exists for every `β ∈ (0, π/2)`.
Modelling: `IsConformalAtGM F Ω ζ θ A` says that `F` is conformal at `ζ` with `A_ζ = A` (modulo `2π`); "conformal at
`ζ`" is `∃ A`. The limit of `arg q`, `q = (F(z) − F(ζ))/(z − ζ)`, is the limit `q/|q| → e^{iA}` of its direction
(module docstring). For a conformal `F` the quotient `q` has no zero near `ζ` in the cone, since the nontangential limit
`F(ζ)` is a boundary point of `F(Ω)`, so `q/|q|` sees no division junk. The hypotheses "`F` conformal" (and the
inner tangent, contained in the nontangential limit) are carried by the statements. Name clash (inventory C4): this is
Pommerenke's isogonality `Pommerenke1992.IsIsogonalAt` (for `Ω = 𝔻`); Pommerenke's
`Pommerenke1992.IsConformalAtBoundary` is GM's non-zero angular derivative. -/
def IsConformalAtGM (F : ℂ → ℂ) (Ω : Set ℂ) (ζ : ℂ) (θ A : ℝ) : Prop :=
  ∃ w : ℂ, HasNontangentialLimitAt Ω ζ θ F w ∧ ∀ β ∈ Ioo 0 (π / 2),
    Tendsto (fun z => (F z - w) / (z - ζ) / ((‖(F z - w) / (z - ζ)‖ : ℝ) : ℂ)) (𝓝[truncatedCone ζ θ β 1] ζ)
      (𝓝 (Complex.exp ((A : ℂ) * I)))

/-- **Unlabelled** (Ch. V §5, P1:7554; cited in Chapter VI, P2:805, 971 (the chain "`φ` is conformal at `ζ` ⇒ `∂Ω` has
an inner tangent at `φ(ζ)`"), P2:838, and in Chapter VII, P2:2272). If `F` is conformal at `ζ`, then `∂(F(Ω))` has an
inner tangent at `F(ζ)` and `F⁻¹` is conformal at `F(ζ)`.
Modelling: `Ω` is a plane domain and `F` maps it conformally onto `Ω'`; `F(ζ) = w` is the nontangential limit; the
inner normal of `Ω'` at `w` is `e^{i(θ + A_ζ)}` (the image of the direction `e^{iθ}`), and the angle of `F⁻¹` at `w` is
`−A_ζ`; `F⁻¹` is `Function.invFunOn F Ω`. -/
theorem isConformalAtGM_image {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω ∧ IsConnected Ω) {F : ℂ → ℂ}
    (hF : IsConformalOnto F Ω Ω') {ζ w : ℂ} {θ A : ℝ} (hconf : IsConformalAtGM F Ω ζ θ A)
    (hw : HasNontangentialLimitAt Ω ζ θ F w) :
    HasInnerTangent Ω' w (θ + A) ∧ IsConformalAtGM (Function.invFunOn F Ω) Ω' w (θ + A) (-A) := by
  sorry

/-- **Unlabelled** (Ch. V §5, P1:7554; cited in Chapter VI, P2:1081, "If `w ∈ Tn(Γ)` then by Theorem II.4.2, `φ_j` is
conformal at `φ_j⁻¹(w)`"). If `Ω` is a Jordan domain, if `F : 𝔻 → Ω` is a conformal mapping, and if `∂Ω` has a
tangent at `F(ζ)`, then by Theorem II.4.2 `F` is conformal at `ζ`. Moreover, in this case the convergence `z → ζ` need
not be restricted to cones `Γ_β(ζ)`.
Modelling: the setting of Theorem II.4.2 (`IsJordanDiscMap Ω F Φ`: `Ω` a bounded plane Jordan domain, `F` a conformal
map of `𝔻` onto `Ω`, `Φ` its continuous extension to `𝔻̄`), `ζ = e^{it₀}`, and the tangent of `∂Ω` at `Φ(ζ) = F(ζ)` for
the parametrization `t ↦ Φ(e^{it})` (`HasTangentAt`, as in `thm2_4_2_i`); the inner normal of `𝔻` at `ζ` is `−ζ`,
i.e. `θ = arg(−ζ)`; "need not be restricted to cones" is the limit of the direction of
`(F(z) − F(ζ))/(z − ζ)` as `z → ζ` in `𝔻`, with the same angle. Unbounded Jordan domains (leader ruling F4): Theorem
II.4.2 is stated for bounded domains, and so is this claim; a Jordan domain of `ℂ*` with a tangent at the finite point
`F(ζ)` reduces to this case by the Möbius map `T(w) = 1/(w − a)`, `a` a finite point outside `Ω̄`: `T(Ω)` is a bounded
Jordan domain whose boundary has a tangent at `T(F(ζ))`, `T ∘ F` is conformal at `ζ`, and `F = T⁻¹ ∘ (T ∘ F)` is
conformal at `ζ` because `T⁻¹` is analytic with non-zero derivative near `T(F(ζ))` (the angle changes by
`arg (T⁻¹)'(T(F(ζ)))`). No extended-plane companion is stated: the claim concerns a finite boundary point, and the
use in Chapter VI (P2:1081, where `Ω₂` may contain `∞`) carries the same reduction there. -/
theorem isConformalAtGM_of_hasTangent {Ω : Set ℂ} {F Φ : ℂ → ℂ} (hS : IsJordanDiscMap Ω F Φ) {t₀ τ : ℝ}
    (hτ : HasTangentAt (fun t => Φ (circleMap 0 1 t)) t₀ τ) {ζ : ℂ} (hζ : ζ = circleMap 0 1 t₀) :
    ∃ A : ℝ, IsConformalAtGM F unitDisc ζ (arg (-ζ)) A ∧
      Tendsto (fun z => (F z - Φ ζ) / (z - ζ) / ((‖(F z - Φ ζ) / (z - ζ)‖ : ℝ) : ℂ)) (𝓝[unitDisc] ζ)
        (𝓝 (Complex.exp ((A : ℂ) * I))) := by
  sorry

/-- **Definition 5.3** (angular derivative, Ch. V §5; cited in the hint of Exercise V.5, P2:573, and as "(non-zero)
angular derivative" in Chapter VI §1, §4, §6, Chapter X §9, P3:1226, and App. I, P3:4925). Suppose `F : Ω → Ω'` is a
conformal map defined on `Ω` and suppose `∂Ω` has an inner tangent at `ζ ∈ ∂Ω`. We say `F` has angular derivative
`F'(ζ)` if for all `β ∈ (0, π/2)` the two limits `F(ζ) ≡ lim_{Γ^ε_β(ζ) ∋ z → ζ} F(z)` and
(5.3) `F'(ζ) ≡ lim_{Γ^ε_β(ζ) ∋ z → ζ} (F(z) − F(ζ))/(z − ζ)` exist and are finite.
Modelling: `HasAngularDerivGM F Ω ζ θ w L` says that `F` has the nontangential limit `F(ζ) = w` and the angular
derivative `F'(ζ) = L` (both finite complex numbers); "non-zero angular derivative" is `L ≠ 0`, which is
Pommerenke's `Pommerenke1992.IsConformalAtBoundary` for the disc (inventory C4). The hypothesis "`F` conformal" is
carried by the statements. Near miss: `Pommerenke1992.HasAngularDerivative` (the disc, Stolz angles, values in the
extended plane). -/
def HasAngularDerivGM (F : ℂ → ℂ) (Ω : Set ℂ) (ζ : ℂ) (θ : ℝ) (w L : ℂ) : Prop :=
  HasNontangentialLimitAt Ω ζ θ F w ∧ HasNontangentialLimitAt Ω ζ θ (fun z => (F z - w) / (z - ζ)) L

/-- **Lemma 5.4** (Ch. V §5; used in Chapter VI, P2:801, "by calculus, `φ` has a non-zero angular derivative at `ζ`
whenever `φ'` has a non-zero nontangential limit at `ζ`"). Suppose `F : Ω → Ω'` is a conformal map defined on `Ω` and
suppose `∂Ω` has an inner tangent at `ζ ∈ ∂Ω`. Then `F` has an angular derivative at `ζ` if and only if `F'` has a
finite nontangential limit at `ζ`.
Modelling: `Ω` is a plane domain; stated for each value `L`: the proof shows that the angular derivative `F'(ζ)` and
the nontangential limit of `F'` are the same number (the form in which Chapter VI uses the lemma, non-zero on both
sides); `F'` is `deriv F`, the complex derivative on the open set `Ω`. -/
theorem lemma5_5_4 {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω ∧ IsConnected Ω) {F : ℂ → ℂ} (hF : IsConformalOnto F Ω Ω')
    {ζ : ℂ} {θ : ℝ} (hζ : HasInnerTangent Ω ζ θ) (L : ℂ) :
    (∃ w : ℂ, HasAngularDerivGM F Ω ζ θ w L) ↔ HasNontangentialLimitAt Ω ζ θ (deriv F) L := by
  sorry

/-- **Unlabelled** (Ch. V §5, P1:7586; cited in Chapter VI, P2:941, "Recall from Chapter V that if `φ` has a non-zero
angular derivative at `ζ`, then `φ` is conformal at `ζ`", P2:805, and in the chain P2:969–971). If `F` has a non-zero
angular derivative at `ζ` then `F` is conformal at `ζ` and `A_ζ = arg F'(ζ)`. Furthermore, `F⁻¹` also has a non-zero
angular derivative at `F(ζ)`.
Modelling: `Ω` is a plane domain and `F` maps it conformally onto `Ω'`; the angular derivative of `F⁻¹`
(`Function.invFunOn F Ω`) at `F(ζ) = w` is `1/F'(ζ)`, with the inner normal `e^{i(θ + arg F'(ζ))}` of `Ω'` at `w` and
the nontangential limit `ζ`. -/
theorem isConformalAtGM_of_hasAngularDerivGM {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω ∧ IsConnected Ω) {F : ℂ → ℂ}
    (hF : IsConformalOnto F Ω Ω') {ζ w L : ℂ} {θ : ℝ} (hd : HasAngularDerivGM F Ω ζ θ w L) (hL : L ≠ 0) :
    IsConformalAtGM F Ω ζ θ (arg L) ∧ HasAngularDerivGM (Function.invFunOn F Ω) Ω' w (θ + arg L) ζ L⁻¹ := by
  sorry

/-- **Definition** (the standard strip, Ch. V §5, P1:7626–7629; used in §6 and in the index "standard strip, 176").
`𝕊 = {z : |Im z| < π/2}`. -/
def standardStrip : Set ℂ :=
  {z | |z.im| < π / 2}

/-- **Definition** (the half-strips, Ch. V §5, P1:7644–7648; used in (5.6) and §6).
`S_δ = {z : |Im z| < π/2 − δ and Re z > 0}`, `δ ∈ (0, π/2)`.
Modelling: defined for every real `δ` (used for `δ ∈ (0, π/2)`). -/
def halfStrip (δ : ℝ) : Set ℂ :=
  {z | |z.im| < π / 2 - δ ∧ 0 < z.re}

/-- **Theorem 5.5** (Ostrowski, Ch. V §5), the direct part (cited at P1:7554, in the proofs of Theorem 5.7, P1:7796,
7816, 7850, 7864, P2:1, and of Theorem 6.1, P2:190, in Chapter VI, P2:941, and in Exercise V.5, P2:561). Suppose `Ω`
is a simply connected domain in `ℂ` and suppose `0 ∈ ∂Ω`. Let `φ : ℍ → Ω` be a conformal map having nontangential limit
`φ(0) = 0`. If `φ` is conformal at `0` and if (5.2) holds with `A₀ = 0`, then `∂Ω` has an inner tangent at `0` with a
vertical inner normal and (5.7) `lim_{ℝ ∋ x → 0} dist(x, ∂Ω)/x = 0`.
Modelling: `Ω ⊆ ℂ` with `Gehring1978.IsHypSimplyConnectedExt (toExt Ω)`; the nontangential limit is taken in `ℍ` at
`0` with the vertical inner normal of `ℍ` (`θ = π/2`); the book treats only `ζ = 0`, `φ(0) = 0`, `A_ζ = 0` ("the other
cases reduce to this case by translations and rotations"), and so does the statement; in (5.7) `x → 0` through the
non-zero reals (both sides; the proof reduces to `x > 0`), `dist(x, ∂Ω)` is the distance to the frontier in `ℂ`. The
formula (5.7) was checked against the equation image. -/
theorem thm5_5_5_a {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) (h0 : (0 : ℂ) ∈ frontier Ω) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ upperHalf Ω) (hφ0 : HasNontangentialLimitAt upperHalf 0 (π / 2) φ 0)
    (hconf : IsConformalAtGM φ upperHalf 0 (π / 2) 0) :
    HasInnerTangent Ω 0 (π / 2) ∧
      Tendsto (fun x : ℝ => infDist (x : ℂ) (frontier Ω) / x) (𝓝[≠] 0) (𝓝 0) := by
  sorry

/-- **Theorem 5.5** (Ostrowski, Ch. V §5), the converse. Suppose `Ω` is a simply connected domain in `ℂ` and suppose
`0 ∈ ∂Ω`. If `∂Ω` has an inner tangent at `0` with a vertical inner normal and if (5.7) holds, then there exists a
conformal map `φ` of `ℍ` onto `Ω` having nontangential limit `φ(0) = 0` such that `φ` is conformal at `0` and the
limit `A₀` in (5.2) is `0`.
Modelling: as in `thm5_5_5_a`. -/
theorem thm5_5_5_b {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) (h0 : (0 : ℂ) ∈ frontier Ω)
    (htan : HasInnerTangent Ω 0 (π / 2))
    (h57 : Tendsto (fun x : ℝ => infDist (x : ℂ) (frontier Ω) / x) (𝓝[≠] 0) (𝓝 0)) :
    ∃ φ : ℂ → ℂ, IsConformalOnto φ upperHalf Ω ∧ HasNontangentialLimitAt upperHalf 0 (π / 2) φ 0 ∧
      IsConformalAtGM φ upperHalf 0 (π / 2) 0 := by
  sorry

/-- **Definition 5.6** (positive angular derivative, Ch. V §5; cited in Theorem 5.7, Corollary 5.8, and in Exercises
V.8, V.9, P2:625, 637–645). If `Ω` is simply connected and if `0 ∈ ∂Ω`, we say `Ω` has a positive angular derivative at
`0 ∈ ∂Ω` if there is a conformal map `φ` of `ℍ` onto `Ω` which has nontangential limit `φ(0) = 0` and which has
angular derivative `φ'(0)` such that `0 < φ'(0) < ∞`.
Modelling: `Ω ⊆ ℂ`; the angular derivative of `φ` at `0` in `ℍ` (vertical inner normal) with the value `φ(0) = 0` and
the derivative `φ'(0) = L`, a positive real number; the setting "`Ω` simply connected, `0 ∈ ∂Ω`" is carried by the
statements (it follows from the existence of `φ`). -/
def HasPositiveAngularDeriv (Ω : Set ℂ) : Prop :=
  ∃ (φ : ℂ → ℂ) (L : ℝ), 0 < L ∧ IsConformalOnto φ upperHalf Ω ∧
    HasAngularDerivGM φ upperHalf 0 (π / 2) 0 (L : ℂ)

/-- The set `E_r` of Theorem 5.7 (helper, Ch. V §5, P1:7777): the component of `Ω ∩ {|z| = r}` containing the point
`ir` (empty when `ir ∉ Ω`). -/
def circleSection (Ω : Set ℂ) (r : ℝ) : Set ℂ :=
  connectedComponentIn (Ω ∩ sphere 0 r) (I * (r : ℂ))

/-- **Theorem 5.7** (Jenkins–Oikawa, Rodin–Warschawski, Ch. V §5; cited at P1:7785, P2:7, 32, 84, in Chapter VI,
P2:801, "the pointwise theorems II.4.2 and V.5.7", in Exercise V.8, P2:625, and in Exercise IV.6, P1:6637). Suppose
`Ω` is a simply connected domain such that `0 ∈ ∂Ω` and `iℝ⁺ = {iy : y > 0} ⊆ Ω`. For `r > 0`, let `E_r` denote the
component of `Ω ∩ {|z| = r}` containing the point `ir`. Then `Ω` has positive angular derivative at `0` if and only if
(a) `Ω` has an inner tangent at `0` with a vertical inner normal, and
(b) (5.16) `lim_{s < r → 0} d_Ω(E_r, E_s) − (1/π) log(r/s) = 0`.
Modelling: `Ω ⊆ ℂ` with `Gehring1978.IsHypSimplyConnectedExt (toExt Ω)`; `E_r` is `circleSection Ω r`; `d_Ω` is
`extremalDistGM` (values in `[0, ∞]`); the double limit "`s < r → 0`" is stated in `ε`-form (for every `η > 0` there is
an `r₀ > 0` with the difference within `η` whenever `0 < s < r < r₀`), and the finiteness of `d_Ω(E_r, E_s)` for such
`s`, `r` is part of (b) (the difference is a real number that tends to `0`). -/
theorem thm5_5_7 {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) (h0 : (0 : ℂ) ∈ frontier Ω)
    (hiR : ∀ y : ℝ, 0 < y → I * (y : ℂ) ∈ Ω) :
    HasPositiveAngularDeriv Ω ↔ HasInnerTangent Ω 0 (π / 2) ∧
      ∀ η : ℝ, 0 < η → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ s r : ℝ, 0 < s → s < r → r < r₀ →
        extremalDistGM Ω (circleSection Ω r) (circleSection Ω s) < ⊤ ∧
          |(extremalDistGM Ω (circleSection Ω r) (circleSection Ω s)).toReal - 1 / π * Real.log (r / s)| < η := by
  sorry

/-- **Corollary 5.8** (Ch. V §5; cited in Chapter VI, P2:941, "Ostrowski's theorem and Corollary V.5.8"). Suppose `Ω`
is a simply connected domain given by `Ω = {re^{iα} : α₁(r) < α < α₂(r); r > 0}`, where `α_j` are absolutely
continuous in `(0, 1)`, `α₁(r) < π/2 < α₂(r)`, `α₁(0) = 0`, `α₂(0) = π`, and `∫₀¹ α_j'(r)² r dr < ∞` for `j = 1, 2`.
Let `Θ(r) = α₂(r) − α₁(r)`. Then `Ω` has a positive angular derivative at `0` if and only if
(5.24) `∫₀¹ (1/(rΘ(r)) − 1/(πr)) dr` exists.
Modelling: `α₁, α₂ : ℝ → ℝ` with the description of `Ω` for `r > 0`; `Ω` simply connected is
`Gehring1978.IsHypSimplyConnectedExt (toExt Ω)`; "absolutely continuous in `(0, 1)`" is local absolute continuity on
the open interval (`AbsolutelyContinuousOnInterval` on every compact subinterval, inventory C12(a)); `α₁(r) < π/2 <
α₂(r)` for every `r > 0`; `α₁(0) = 0`, `α₂(0) = π` are read as the limits at `0⁺` (the proof uses them so, for the
inner tangent); `∫₀¹ α_j'(r)² r dr` is a lower integral in `[0, ∞]` (`α_j'` is `deriv α_j`, a junk value only on a
null set). "(5.24) exists" is the convergence of the improper integral at its singular endpoint `0`: for each
`c ∈ (0, 1)`, `∫_t^c (1/(rΘ(r)) − 1/(πr)) dr` has a finite limit as `t → 0⁺`; the integrand is continuous on `(0, 1)`
(`Θ > 0` there), so these integrals see no junk, while with `α_j` only locally absolutely continuous the endpoint `1`
plays no role (the book's `∫₀¹`, equivalent when the integrand is integrable near `1`). The formula (5.24) was checked
against the equation image. -/
theorem cor5_5_8 {Ω : Set ℂ} {α₁ α₂ : ℝ → ℝ}
    (hΩeq : Ω = {z | ∃ r α : ℝ, 0 < r ∧ α₁ r < α ∧ α < α₂ r ∧ z = (r : ℂ) * Complex.exp ((α : ℂ) * I)})
    (hΩ : IsHypSimplyConnectedExt (toExt Ω))
    (hac₁ : ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 → AbsolutelyContinuousOnInterval α₁ a b)
    (hac₂ : ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 → AbsolutelyContinuousOnInterval α₂ a b)
    (hα : ∀ r : ℝ, 0 < r → α₁ r < π / 2 ∧ π / 2 < α₂ r)
    (h₁ : Tendsto α₁ (𝓝[>] 0) (𝓝 0)) (h₂ : Tendsto α₂ (𝓝[>] 0) (𝓝 π))
    (hd₁ : ∫⁻ r in Ioo 0 1, ENNReal.ofReal (deriv α₁ r ^ 2 * r) < ⊤)
    (hd₂ : ∫⁻ r in Ioo 0 1, ENNReal.ofReal (deriv α₂ r ^ 2 * r) < ⊤) :
    HasPositiveAngularDeriv Ω ↔ ∀ c ∈ Ioo (0 : ℝ) 1, ∃ L : ℝ,
      Tendsto (fun t : ℝ => ∫ r in t..c, (1 / (r * (α₂ r - α₁ r)) - 1 / (π * r))) (𝓝[>] 0) (𝓝 L) := by
  sorry

end GarnettMarshall2005
