import References.Pommerenke1992.Ch03.S03_ContinuityOfTheDerivatives

/-!
# Pommerenke 1992, Ch. 3 §3.4 Tangents and Corners

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §3.4; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 2169–2499.

* Definition (corner of opening `πα` at `f(ζ) ≠ ∞`, (3.4.1); tangent (`α = 1`); outward-pointing cusp (`α = 0`)
  and inward-pointing cusp (`α = 2`), l. 2184) — `HasCornerAt`, `HasTangentAt`
* Definition (the branch (3.4.2) of `log(z - e^{iϑ})` and of `(z - e^{iϑ})^α`; cited at l. 2303, 2338) — `logAt`,
  `powAt`
* Theorem 3.7 (Lindelöf) — `thm3_7`
* Proposition 3.8 — `prop3_8`
* Definition (Dini-smooth corner, §3.4) — `HasDiniSmoothCornerAt`
* Theorem 3.9 (Warschawski) — `thm3_9`
* Definition (corner at `∞`; Dini-smooth corner at `∞`, §3.4) — `HasCornerAtInf`, `HasDiniSmoothCornerAtInf`
* Unlabelled (§3.4, l. 2297: the characterization of a corner at `∞` and (3.4.11); cited at l. 2546) — `eq3_4_11`
* Proposition 3.10 — `prop3_10_a`, `prop3_10_b`, `prop3_10_c`
* Definition (the curvatures `κ^±` at `f(ζ)` of the arcs forming a corner, §3.4) — `HasCornerCurvatures`
* Theorem 3.11 — `thm3_11_a`, `thm3_11_b`, `thm3_11_c`

Helper definitions: `IsBoundarySetting` (the standing assumption), `cornerNbhd`, `extVal`, `IsDiniSmoothArc`.

Not items (DESIGN §3): the sector example and the examples `[(z + 1)/(z - 1)]^α`, (3.4.16), (3.4.23), (3.4.26); the
consequence of Theorem 3.9 for corners at `∞` (l. 2305, "follows at once", not cited); the analytic corners and the
expansions (3.4.24), (3.4.25) quoted from Lewy and Lehman (not cited; the notion "analytic corner" is used only there).

**Standing assumption** (l. 2171): `G ⊆ ℂ` is a simply connected domain with locally connected boundary (in `Ĉ`), and
`f` maps `𝔻` conformally onto `G`; then `f` has a continuous extension `F : 𝔻̄ → Ĉ` (§2.1). `ζ = e^{iϑ}`.

**Conventions.**
- The opening `πα` (`0 ≤ α ≤ 2`) of a corner is read through a continuous branch `θ` of `arg(F(z) - F(ζ))` on the
  points of `𝔻̄ ∩ D(ζ, δ)` where `F(z) ≠ F(ζ)` (a convex set minus boundary points), so that `α` is determined and
  not only modulo `2`; the limits (3.4.1) are taken over the `t` with `F(e^{it}) ≠ F(ζ)`.
- Limits of `arg q` for a quantity `q ≠ 0` are limits of the direction `q/|q|`.
- `(z - ζ)^α` is `powAt ϑ α z = exp(α logAt ϑ z)` with the branch (3.4.2), `ϑ + π/2 < arg(z - e^{iϑ}) < ϑ + 3π/2`
  for `z ∈ 𝔻`; it depends on the real number `ϑ`, as the book's formulas do.
- The finite values `F(e^{it})` near a corner at `∞` are written `extVal (F (e^{it}))`; the statements take limits
  only over the `t` with `F(e^{it}) ≠ ∞` or under a corner hypothesis that makes these values finite, so the junk
  value `extVal ∞ = 0` is not used.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsJordanCurve IsConformalOnto)

/-- The standing assumption of §3.4–§3.5 (helper): `f` maps `𝔻` conformally onto `G ⊆ ℂ`, `∂G` is locally connected
(in `Ĉ`, (2.2.1) with the chordal metric), and `F` is the continuous extension of `f` to `𝔻̄`, with values in `Ĉ`. -/
def IsBoundarySetting (f : ℂ → ℂ) (G : Set ℂ) (F : ℂ → ExtPlane) : Prop :=
  IsConformalOnto f unitDisc G ∧ IsLocConnSph (frontier (toExt G)) ∧ ContinuousOn F (closedBall 0 1) ∧
    ∀ z ∈ unitDisc, F z = f z

/-- The set `𝔻̄ ∩ D(e^{iϑ}, δ) ∖ {e^{iϑ}}` (helper). -/
def cornerNbhd (ϑ δ : ℝ) : Set ℂ :=
  {z | ‖z‖ ≤ 1 ∧ ‖z - exp (ϑ * I)‖ < δ ∧ z ≠ exp (ϑ * I)}

/-- The finite value of a point of `Ĉ` (helper): `extVal z = z` for `z ∈ ℂ`; the value `0` at `∞` is a junk value
that no statement uses. -/
def extVal (p : ExtPlane) : ℂ :=
  OnePoint.elim p 0 id

/-- **Definition** (§3.4, (3.4.1); cited at l. 2540). `∂G` has a corner of opening `πα` (`0 ≤ α ≤ 2`) at
`f(ζ) ≠ ∞`, `ζ = e^{iϑ}`: `arg[f(e^{it}) - f(e^{iϑ})] → β` as `t → ϑ+` and `→ β + πα` as `t → ϑ-`.
Modelling: `f(ζ) = F(ζ) = a` is finite; `arg(F(z) - a)` is a continuous branch `θ` on the points `z` of
`𝔻̄ ∩ D(ζ, δ) ∖ {ζ}` with `F(z) ≠ a` (see the file header), and the limits run over the `t` with `F(e^{it}) ≠ a` (the
arg in (3.4.1) is defined only there); the OCR's "`0 ≤ α ≤ 2π`" is read as `0 ≤ α ≤ 2`, as in Theorem 3.7. -/
def HasCornerAt (F : ℂ → ExtPlane) (ϑ α β : ℝ) : Prop :=
  0 ≤ α ∧ α ≤ 2 ∧ ∃ a : ℂ, F (exp (ϑ * I)) = a ∧ ∃ δ > (0 : ℝ), ∃ θ : ℂ → ℝ,
    ContinuousOn θ {z ∈ cornerNbhd ϑ δ | F z ≠ a} ∧
    (∀ z ∈ cornerNbhd ϑ δ, F z ≠ a → ∃ u : ℂ, F z = u ∧ u - a = (‖u - a‖ : ℂ) * exp (θ z * I)) ∧
    Tendsto (fun t : ℝ => θ (exp (t * I))) (𝓝[>] ϑ ⊓ 𝓟 {t | F (exp (t * I)) ≠ a}) (𝓝 β) ∧
    Tendsto (fun t : ℝ => θ (exp (t * I))) (𝓝[<] ϑ ⊓ 𝓟 {t | F (exp (t * I)) ≠ a}) (𝓝 (β + π * α))

/-- **Definition** (§3.4, l. 2184). `∂G` has a tangent of direction angle `β` at `f(ζ)`: a corner of opening `π`
(`α = 1`). -/
def HasTangentAt (F : ℂ → ExtPlane) (ϑ β : ℝ) : Prop :=
  HasCornerAt F ϑ 1 β

/-- **Definition** (§3.4, (3.4.2); cited at l. 2303, 2338). The branch of `log(z - e^{iϑ})` with
`ϑ + π/2 < Im log(z - e^{iϑ}) = arg(z - e^{iϑ}) < ϑ + 3π/2` for `z ∈ 𝔻`.
Modelling: `arg(z - e^{iϑ}) = ϑ + π + Arg(1 - z e^{-iϑ})`, where `Re(1 - z e^{-iϑ}) > 0` for `z ∈ 𝔻`. -/
def logAt (ϑ : ℝ) (z : ℂ) : ℂ :=
  (Real.log ‖z - exp (ϑ * I)‖ : ℂ) + ((ϑ + π + arg (1 - z * exp (-(ϑ * I))) : ℝ) : ℂ) * I

/-- **Definition** (§3.4, (3.4.2)). The power `(z - e^{iϑ})^α = exp(α log(z - e^{iϑ}))` with the branch (3.4.2). -/
def powAt (ϑ : ℝ) (α : ℂ) (z : ℂ) : ℂ :=
  exp (α * logAt ϑ z)

/-- **Theorem 3.7** (§3.4; Lindelöf). Let `f` map `𝔻` conformally onto `G` where `∂G` is locally connected. Let
`ζ = e^{iϑ} ∈ 𝕋` and `f(ζ) ≠ ∞`. Then `∂G` has a corner of opening `πα` (`0 ≤ α ≤ 2`) at `f(ζ)` if and only if
(3.4.3) `arg[(f(z) - f(ζ))/(z - ζ)^α] → β - α(ϑ + π/2)` as `z → ζ`, `z ∈ 𝔻`. -/
theorem thm3_7 {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {ϑ α β : ℝ} {a : ℂ}
    (ha : F (exp (ϑ * I)) = a) (hα0 : 0 ≤ α) (hα2 : α ≤ 2) :
    HasCornerAt F ϑ α β ↔
      Tendsto (fun z => (f z - a) / powAt ϑ α z / (‖(f z - a) / powAt ϑ α z‖ : ℂ)) (𝓝[unitDisc] (exp (ϑ * I)))
        (𝓝 (exp ((β - α * (ϑ + π / 2)) * I))) := by
  sorry

/-- **Proposition 3.8** (§3.4). If `f` maps `𝔻` conformally onto `G ⊆ ℂ` and if `a ≠ ∞`, `a ∉ G`, then
(3.4.4) `log(f(z) - a) = log|f(0) - a| + (i/2π) ∫₀^{2π} (e^{it} + z)/(e^{it} - z) arg(f(e^{it}) - a) dt`.
Modelling: the book's own hypotheses (no locally connected boundary is assumed). `log(f - a)` is a holomorphic
logarithm `L` of `f - a` in `𝔻`; `f(e^{it})` is the radial limit of `f`, and `arg(f(e^{it}) - a)` is the function `v`
of radial limits of `Im L`, which exist, with `f(e^{it}) ≠ a` finite and `v(t)` an argument of `f(e^{it}) - a`, for
almost all `t`. -/
theorem prop3_8 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {a : ℂ} (ha : a ∉ G) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L unitDisc ∧ (∀ z ∈ unitDisc, exp (L z) = f z - a) ∧
      ∃ v : ℝ → ℝ, IntervalIntegrable v volume 0 (2 * π) ∧
        (∀ᵐ t : ℝ, Tendsto (fun r : ℝ => (L (r * exp (t * I))).im) (𝓝[<] 1) (𝓝 (v t)) ∧
          ∃ u : ℂ, Tendsto (fun r : ℝ => f (r * exp (t * I))) (𝓝[<] 1) (𝓝 u) ∧ u ≠ a ∧
            u - a = (‖u - a‖ : ℂ) * exp (v t * I)) ∧
        ∀ z ∈ unitDisc, L z = (Real.log ‖f 0 - a‖ : ℂ) + I / (2 * π) *
          ∫ t in (0 : ℝ)..2 * π, (exp (t * I) + z) / (exp (t * I) - z) * (v t : ℂ) := by
  sorry

/-- A Dini-smooth Jordan arc `A ⊆ ℂ` (helper): `A = v([0, b])` for an injective `v` with a continuous, Dini-continuous
and non-vanishing derivative on `[0, b]`. -/
def IsDiniSmoothArc (A : Set ℂ) : Prop :=
  ∃ (v : ℝ → ℂ) (b : ℝ), 0 < b ∧ InjOn v (Icc 0 b) ∧ v '' Icc 0 b = A ∧ ContDiffOn ℝ 1 v (Icc 0 b) ∧
    (∀ τ ∈ Icc 0 b, derivWithin v (Icc 0 b) τ ≠ 0) ∧ IsDiniContinuous (derivWithin v (Icc 0 b)) (Icc 0 b)

/-- **Definition** (§3.4). `∂G` has a Dini-smooth corner at `f(ζ)`: there are closed arcs `A^± ⊆ 𝕋` ending at
`ζ ∈ 𝕋` and lying on opposite sides of `ζ` that are mapped onto Dini-smooth Jordan arcs `C^+` and `C^-` forming the
angle `πα` at `f(ζ)`.
Modelling: `A^+ = {e^{it} : ϑ ≤ t ≤ ϑ + δ}`, `A^- = {e^{it} : ϑ - δ ≤ t ≤ ϑ}`; "forming the angle `πα`" is a corner of
opening `πα` (3.4.1). -/
def HasDiniSmoothCornerAt (F : ℂ → ExtPlane) (ϑ α β : ℝ) : Prop :=
  HasCornerAt F ϑ α β ∧ ∃ δ > (0 : ℝ),
    IsDiniSmoothArc ((fun t : ℝ => extVal (F (exp (t * I)))) '' Icc ϑ (ϑ + δ)) ∧
    IsDiniSmoothArc ((fun t : ℝ => extVal (F (exp (t * I)))) '' Icc (ϑ - δ) ϑ)

/-- **Theorem 3.9** (§3.4; Warschawski). If `∂G` has a Dini-smooth corner of opening `πα` (`0 < α ≤ 2`) at
`f(ζ) ≠ ∞`, then the functions `(f(z) - f(ζ))/(z - ζ)^α` and `f'(z)/(z - ζ)^{α-1}` are continuous and `≠ 0, ∞` in
`𝔻̄ ∩ D(ζ, ρ)` for some `ρ > 0`.
Modelling: the two functions, given on `𝔻 ∩ D(ζ, ρ)`, have continuous non-vanishing (finite) extensions `Q₁`, `Q₂` to
`𝔻̄ ∩ D(ζ, ρ)`. -/
theorem thm3_9 {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {ϑ α β : ℝ} {a : ℂ}
    (ha : F (exp (ϑ * I)) = a) (hα0 : 0 < α) (hα2 : α ≤ 2) (hcorner : HasDiniSmoothCornerAt F ϑ α β) :
    ∃ ρ > (0 : ℝ), ∃ Q₁ Q₂ : ℂ → ℂ,
      ContinuousOn Q₁ (closedBall 0 1 ∩ ball (exp (ϑ * I)) ρ) ∧
      ContinuousOn Q₂ (closedBall 0 1 ∩ ball (exp (ϑ * I)) ρ) ∧
      (∀ z ∈ closedBall 0 1 ∩ ball (exp (ϑ * I)) ρ, Q₁ z ≠ 0 ∧ Q₂ z ≠ 0) ∧
      (∀ z ∈ unitDisc ∩ ball (exp (ϑ * I)) ρ,
        Q₁ z = (f z - a) / powAt ϑ α z ∧ Q₂ z = deriv f z / powAt ϑ (α - 1) z) := by
  sorry

/-- **Definition** (§3.4, l. 2297). `∂G` has a corner of opening `πα` (`0 ≤ α ≤ 2`) at `f(ζ) = ∞` if `w ↦ 1/w` leads
to a corner of opening `πα` at `0`.
Modelling: as `HasCornerAt` for the boundary values of `1/f`: `F(ζ) = ∞`, and `arg(1/F(z))` has a continuous branch
`θ` on the points of `𝔻̄ ∩ D(ζ, δ) ∖ {ζ}` where `F(z) ≠ ∞` (there `F(z) ≠ 0`), with the limits `β` (`t → ϑ+`) and
`β + πα` (`t → ϑ-`) over the `t` with `F(e^{it}) ≠ ∞`. -/
def HasCornerAtInf (F : ℂ → ExtPlane) (ϑ α β : ℝ) : Prop :=
  0 ≤ α ∧ α ≤ 2 ∧ F (exp (ϑ * I)) = extInf ∧ ∃ δ > (0 : ℝ), ∃ θ : ℂ → ℝ,
    ContinuousOn θ {z ∈ cornerNbhd ϑ δ | F z ≠ extInf} ∧
    (∀ z ∈ cornerNbhd ϑ δ, F z ≠ extInf → ∃ u : ℂ, F z = u ∧ u ≠ 0 ∧ u⁻¹ = (‖u⁻¹‖ : ℂ) * exp (θ z * I)) ∧
    Tendsto (fun t : ℝ => θ (exp (t * I))) (𝓝[>] ϑ ⊓ 𝓟 {t | F (exp (t * I)) ≠ extInf}) (𝓝 β) ∧
    Tendsto (fun t : ℝ => θ (exp (t * I))) (𝓝[<] ϑ ⊓ 𝓟 {t | F (exp (t * I)) ≠ extInf}) (𝓝 (β + π * α))

/-- **Definition** (§3.4, l. 2303). The corner at `∞` is Dini-smooth if the corresponding corner at `0` is
Dini-smooth.
Modelling: the arcs `{1/f(e^{it})}` on both sides of `ϑ`, with the end point `0` (the image of `∞`), are Dini-smooth
Jordan arcs. -/
def HasDiniSmoothCornerAtInf (F : ℂ → ExtPlane) (ϑ α β : ℝ) : Prop :=
  HasCornerAtInf F ϑ α β ∧ ∃ δ > (0 : ℝ),
    IsDiniSmoothArc (insert 0 ((fun t : ℝ => (extVal (F (exp (t * I))))⁻¹) '' Ioc ϑ (ϑ + δ))) ∧
    IsDiniSmoothArc (insert 0 ((fun t : ℝ => (extVal (F (exp (t * I))))⁻¹) '' Ico (ϑ - δ) ϑ))

/-- **Unlabelled claim** (§3.4, l. 2297, (3.4.11); cited at l. 2546). By Theorem 3.7, `∂G` has a corner of opening
`πα` at `f(ζ) = ∞` if and only if `arg[(z - ζ)^α f(z)] → γ + απ + αϑ` as `z → ζ` for some `γ`, and then
(3.4.11) `arg f(e^{it}) → γ ± απ/2` as `t → ϑ±`.
Modelling: `z → ζ` with `z ∈ 𝔻` (as in Theorem 3.7; the values on `𝕋` follow by continuity); the limits of the
direction of `F(e^{it})` run over the `t` with `F(e^{it}) ≠ ∞`. -/
theorem eq3_4_11 {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {ϑ α : ℝ}
    (hinf : F (exp (ϑ * I)) = extInf) (hα0 : 0 ≤ α) (hα2 : α ≤ 2) :
    ((∃ β, HasCornerAtInf F ϑ α β) ↔
      ∃ γ : ℝ, Tendsto (fun z => powAt ϑ α z * f z / (‖powAt ϑ α z * f z‖ : ℂ))
        (𝓝[unitDisc] (exp (ϑ * I))) (𝓝 (exp ((γ + α * π + α * ϑ) * I)))) ∧
    ∀ γ : ℝ, Tendsto (fun z => powAt ϑ α z * f z / (‖powAt ϑ α z * f z‖ : ℂ))
        (𝓝[unitDisc] (exp (ϑ * I))) (𝓝 (exp ((γ + α * π + α * ϑ) * I))) →
      Tendsto (fun t : ℝ => extVal (F (exp (t * I))) / (‖extVal (F (exp (t * I)))‖ : ℂ))
          (𝓝[>] ϑ ⊓ 𝓟 {t | F (exp (t * I)) ≠ extInf}) (𝓝 (exp ((γ + α * π / 2) * I))) ∧
        Tendsto (fun t : ℝ => extVal (F (exp (t * I))) / (‖extVal (F (exp (t * I)))‖ : ℂ))
          (𝓝[<] ϑ ⊓ 𝓟 {t | F (exp (t * I)) ≠ extInf}) (𝓝 (exp ((γ - α * π / 2) * I))) := by
  sorry

/-- **Proposition 3.10** (§3.4), the case `0 < α < 1`. Let `∂G` have a Dini-smooth corner of opening `πα` with
`0 < α < 2` at `f(ζ) = ∞`, `ζ = e^{iϑ}`, and suppose (3.4.12) `Im[e^{-iγ ∓ iπα/2} f(e^{it})] → ∓b^±` as `t → ϑ±`. If
`0 < α < 1`, then (3.4.13) `f(z) = a/(z - ζ)^α + w₀ + o(1)` as `z = rζ`, `r → 1`, with some constant `a ≠ 0`,
`arg a = γ + απ + αϑ`, where (3.4.15) `w₀ = e^{iγ}(b^- e^{iπα/2} + b^+ e^{-iπα/2})/sin(πα)`.
Modelling: `γ` is the midline angle of the corner, `γ = -β - απ/2` for the corner at `0` of `1/f` (see
`eq3_4_11`). -/
theorem prop3_10_a {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {ϑ α β bp bm : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (hcorner : HasDiniSmoothCornerAtInf F ϑ α β)
    (hp : Tendsto (fun t : ℝ => (exp (-((-β - α * π / 2 + π * α / 2) * I)) * extVal (F (exp (t * I)))).im)
      (𝓝[>] ϑ) (𝓝 (-bp)))
    (hm : Tendsto (fun t : ℝ => (exp (-((-β - α * π / 2 - π * α / 2) * I)) * extVal (F (exp (t * I)))).im)
      (𝓝[<] ϑ) (𝓝 bm)) :
    ∃ A : ℂ, A ≠ 0 ∧ A / (‖A‖ : ℂ) = exp ((-β - α * π / 2 + α * π + α * ϑ) * I) ∧
      Tendsto (fun r : ℝ => f (r * exp (ϑ * I)) - A / powAt ϑ α (r * exp (ϑ * I)) -
          exp ((-β - α * π / 2) * I) * (bm * exp (π * α / 2 * I) + bp * exp (-(π * α / 2) * I)) /
            (Real.sin (π * α) : ℂ))
        (𝓝[<] 1) (𝓝 0) := by
  sorry

/-- **Proposition 3.10** (§3.4), the case `α = 1`. Under the hypotheses of `prop3_10_a` with `α = 1`,
(3.4.14) `f(z) = a/(z - ζ) + i e^{iγ} (b^+ - b^-)/π · log(z - ζ) + o(log 1/(1 - r))` as `z = rζ`, `r → 1`.
Modelling: `log(z - ζ)` is the branch (3.4.2); `γ = -β - π/2`; the constant `a` is as in (3.4.13), `a ≠ 0` with
`arg a = γ + π + ϑ`. -/
theorem prop3_10_b {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {ϑ β bp bm : ℝ}
    (hcorner : HasDiniSmoothCornerAtInf F ϑ 1 β)
    (hp : Tendsto (fun t : ℝ => (exp (-((-β - π / 2 + π / 2) * I)) * extVal (F (exp (t * I)))).im)
      (𝓝[>] ϑ) (𝓝 (-bp)))
    (hm : Tendsto (fun t : ℝ => (exp (-((-β - π / 2 - π / 2) * I)) * extVal (F (exp (t * I)))).im)
      (𝓝[<] ϑ) (𝓝 bm)) :
    ∃ A : ℂ, A ≠ 0 ∧ A / (‖A‖ : ℂ) = exp ((-β - π / 2 + π + ϑ) * I) ∧
      Tendsto (fun r : ℝ => (f (r * exp (ϑ * I)) - A / (r * exp (ϑ * I) - exp (ϑ * I)) -
          I * exp ((-β - π / 2) * I) * ((bp - bm : ℝ) : ℂ) / π * logAt ϑ (r * exp (ϑ * I))) /
          (Real.log (1 / (1 - r)) : ℂ))
        (𝓝[<] 1) (𝓝 0) := by
  sorry

/-- **Proposition 3.10** (§3.4), the case `1 < α < 2`. Under the hypotheses of `prop3_10_a` with `1 < α < 2`,
(3.4.13) holds with an additional term `a'/(z - ζ)^{α-1}`, `a' ∈ ℂ`. -/
theorem prop3_10_c {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {ϑ α β bp bm : ℝ}
    (hα1 : 1 < α) (hα2 : α < 2) (hcorner : HasDiniSmoothCornerAtInf F ϑ α β)
    (hp : Tendsto (fun t : ℝ => (exp (-((-β - α * π / 2 + π * α / 2) * I)) * extVal (F (exp (t * I)))).im)
      (𝓝[>] ϑ) (𝓝 (-bp)))
    (hm : Tendsto (fun t : ℝ => (exp (-((-β - α * π / 2 - π * α / 2) * I)) * extVal (F (exp (t * I)))).im)
      (𝓝[<] ϑ) (𝓝 bm)) :
    ∃ A A' : ℂ, A ≠ 0 ∧ A / (‖A‖ : ℂ) = exp ((-β - α * π / 2 + α * π + α * ϑ) * I) ∧
      Tendsto (fun r : ℝ => f (r * exp (ϑ * I)) - A / powAt ϑ α (r * exp (ϑ * I)) -
          A' / powAt ϑ (α - 1) (r * exp (ϑ * I)) -
          exp ((-β - α * π / 2) * I) * (bm * exp (π * α / 2 * I) + bp * exp (-(π * α / 2) * I)) /
            (Real.sin (π * α) : ℂ))
        (𝓝[<] 1) (𝓝 0) := by
  sorry

/-- **Definition** (§3.4, used in Theorem 3.11). At a corner of opening `πα` at `f(ζ) = a` with the direction angles
`β` (arc `C^+`, `t → ϑ+`) and `β + πα` (arc `C^-`, `t → ϑ-`), the arcs `C^±` have the curvatures `κ^±` at `a`.
Modelling: the signed curvature at the end point `a`, for the boundary run through with increasing `t` (so that `G`
lies to the left), positive when the arc turns towards `G`: with `T^+ = e^{iβ}`, `T^- = -e^{i(β + πα)}` the tangent
directions,
`2 Im[conj(T^±) (f(e^{it}) - a)]/|f(e^{it}) - a|² → κ^±` as `t → ϑ±`. This is the sign convention of the proof of
Theorem 3.11 (l. 2450): `w ↦ 1/w` maps the circles of curvature to the lines `Im[e^{-iγ ∓ iπα/2} w] = ∓κ^±/2`,
`γ = -β - πα/2`. -/
def HasCornerCurvatures (F : ℂ → ExtPlane) (ϑ α β κp κm : ℝ) : Prop :=
  ∃ a : ℂ, F (exp (ϑ * I)) = a ∧
    Tendsto (fun t : ℝ => 2 * (conj (exp (β * I)) * (extVal (F (exp (t * I))) - a)).im /
      ‖extVal (F (exp (t * I))) - a‖ ^ 2) (𝓝[>] ϑ) (𝓝 κp) ∧
    Tendsto (fun t : ℝ => 2 * (conj (-exp ((β + π * α) * I)) * (extVal (F (exp (t * I))) - a)).im /
      ‖extVal (F (exp (t * I))) - a‖ ^ 2) (𝓝[<] ϑ) (𝓝 κm)

/-- **Theorem 3.11** (§3.4), the case `0 < α < 1`. Let `∂G` have a Dini-smooth corner of opening `πα` (`0 < α < 2`)
at `f(ζ) ≠ ∞` and suppose that the arcs `C^±` forming the corner have curvature `κ^±` at `f(ζ)`. If `0 < α < 1`, then,
as `z = rζ`, `r → 1-`, (3.4.20) `f(z) = f(ζ) + b₁(z - ζ)^α + b₂(z - ζ)^{2α} + o((1 - r)^{2α})`, where
`arg b₁ = β - πα/2 - αϑ` and (3.4.21) `b₂ = -e^{-iβ} b₁² (κ^- + κ^+ e^{-iπα})/(2 sin πα)`. -/
theorem thm3_11_a {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {ϑ α β κp κm : ℝ}
    {a : ℂ} (ha : F (exp (ϑ * I)) = a) (hα0 : 0 < α) (hα1 : α < 1) (hcorner : HasDiniSmoothCornerAt F ϑ α β)
    (hκ : HasCornerCurvatures F ϑ α β κp κm) :
    ∃ b₁ : ℂ, b₁ ≠ 0 ∧ b₁ / (‖b₁‖ : ℂ) = exp ((β - π * α / 2 - α * ϑ) * I) ∧
      Tendsto (fun r : ℝ => (f (r * exp (ϑ * I)) - a - b₁ * powAt ϑ α (r * exp (ϑ * I)) -
          (-exp (-(β * I)) * b₁ ^ 2 * (κm + κp * exp (-(π * α * I))) / (2 * Real.sin (π * α))) *
            powAt ϑ (2 * α) (r * exp (ϑ * I))) / ((1 - r) ^ (2 * α) : ℝ))
        (𝓝[<] 1) (𝓝 0) := by
  sorry

/-- **Theorem 3.11** (§3.4), the case `α = 1`. Under the hypotheses of `thm3_11_a` with `α = 1`, (3.4.22)
`f(z) = f(ζ) + b₁(z - ζ) + b₂(z - ζ)² log(z - ζ) + o((1 - r)² log 1/(1 - r))`, where
`b₂ = e^{-iβ} b₁² (κ^+ - κ^-)/(2π)`.
Modelling: `log(z - ζ)` is the branch (3.4.2); `b₁ ≠ 0` with `arg b₁ = β - π/2 - ϑ`, as in (3.4.20).
[CORRECTION] The sign of `b₂` is corrected to `b₂ = -e^{-iβ} b₁² (κ^+ - κ^-)/(2π)` (with the curvature convention of
(3.4.21), `HasCornerCurvatures`). As printed, (3.4.22) is false: `f(z) = z + ic(z - 1)² log(z - 1)` (`c > 0` small)
is conformal onto a Jordan domain with a Dini-smooth tangent at `f(1)`, `β = π/2`, `b₁ = 1`, `κ^+ = 1 - cπ`,
`κ^- = 1 - 3cπ`, and its `b₂ = ic`, while the printed formula gives `-ic`. The corrected sign agrees with (3.4.14)
applied to `1/f` (the proof's route) and with the limit `α → 1` of (3.4.21). The example is the function of
Exercise 3.4.2, `z + b(z - 1)² log(z - 1)`, with `b = ic`. -/
theorem thm3_11_b {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {ϑ β κp κm : ℝ}
    {a : ℂ} (ha : F (exp (ϑ * I)) = a) (hcorner : HasDiniSmoothCornerAt F ϑ 1 β)
    (hκ : HasCornerCurvatures F ϑ 1 β κp κm) :
    ∃ b₁ : ℂ, b₁ ≠ 0 ∧ b₁ / (‖b₁‖ : ℂ) = exp ((β - π / 2 - ϑ) * I) ∧
      Tendsto (fun r : ℝ => (f (r * exp (ϑ * I)) - a - b₁ * (r * exp (ϑ * I) - exp (ϑ * I)) -
          (-exp (-(β * I)) * b₁ ^ 2 * ((κp - κm : ℝ) : ℂ) / (2 * π)) * (r * exp (ϑ * I) - exp (ϑ * I)) ^ 2 *
            logAt ϑ (r * exp (ϑ * I))) / (((1 - r) ^ 2 * Real.log (1 / (1 - r)) : ℝ) : ℂ))
        (𝓝[<] 1) (𝓝 0) := by
  sorry

/-- **Theorem 3.11** (§3.4), the case `1 < α < 2`. Under the hypotheses of `thm3_11_a` with `1 < α < 2`, (3.4.20)
holds (with `arg b₁` and `b₂` as there) with an additional term `b'(z - ζ)^{α+1}`. -/
theorem thm3_11_c {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {ϑ α β κp κm : ℝ}
    {a : ℂ} (ha : F (exp (ϑ * I)) = a) (hα1 : 1 < α) (hα2 : α < 2) (hcorner : HasDiniSmoothCornerAt F ϑ α β)
    (hκ : HasCornerCurvatures F ϑ α β κp κm) :
    ∃ b₁ b' : ℂ, b₁ ≠ 0 ∧ b₁ / (‖b₁‖ : ℂ) = exp ((β - π * α / 2 - α * ϑ) * I) ∧
      Tendsto (fun r : ℝ => (f (r * exp (ϑ * I)) - a - b₁ * powAt ϑ α (r * exp (ϑ * I)) -
          (-exp (-(β * I)) * b₁ ^ 2 * (κm + κp * exp (-(π * α * I))) / (2 * Real.sin (π * α))) *
            powAt ϑ (2 * α) (r * exp (ϑ * I)) - b' * powAt ϑ (α + 1) (r * exp (ϑ * I))) /
          ((1 - r) ^ (2 * α) : ℝ))
        (𝓝[<] 1) (𝓝 0) := by
  sorry

end Pommerenke1992
