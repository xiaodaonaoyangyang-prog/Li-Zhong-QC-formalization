import References.Pommerenke1992.Ch03.S06_StarlikeAndCloseToConvexDomains

/-!
# Pommerenke 1992, Ch. 4 §4.2 Bloch Functions

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 4 *Distortion*, §4.2; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 3014–3322.

* Definition (Bloch function; the seminorm `‖g‖_B`, (4.2.1)) — `blochSeminorm`, `IsBloch`
* Formula (4.2.3) (cited in the proof of Theorem 4.2 and at l. 3673) — `eq4_2_3`
* Formula (4.2.4) (cited at l. 6652 and P2 l. 2453) — `eq4_2_4`
* Formula (4.2.5) (cited at l. 6043 and P2 l. 2357, 2363) — `eq4_2_5`
* Unlabelled (§4.2, l. 3054: every bounded analytic function is a Bloch function, since `|g| ≤ 1` implies
  `(1 - |z|²)|g'(z)| ≤ 1 - |g(z)|²`; used at P2 l. 2413) — `bounded_isBloch`
* Proposition 4.1 — `prop4_1_a`, `prop4_1_b`
* Definition (the angle between a circle and `𝕋` towards a domain, used in Theorem 4.2) — `luneFun`,
  `IsAngleTowards`
* Theorem 4.2 — `thm4_2_i`, `thm4_2_ii`, `thm4_2_iii`
* Formula (4.2.10) (cited in the proof of Proposition 4.6) — `eq4_2_10`
* Theorem 4.3 (Lehto–Virtanen) — `thm4_3`
* Definition (asymptotic value, §4.2; cited at P2 l. 257) — `HasAsymptoticValue`
* Proposition 4.4 — `prop4_4`
* Formula (4.2.19) (cited in the proof of Corollary 4.5 and at P2 l. 2429) — `eq4_2_19`
* Corollary 4.5 — `cor4_5`
* Proposition 4.6 — `prop4_6`
* Definition (the little Bloch space `B₀`, (4.2.22); cited at l. 6762) — `IsLittleBloch`

Not items (DESIGN §3): the Banach space structure (quoted from AnClPo74); (4.2.2) (a derivation step); the example
`log[(1 + z)/(1 - z)]`, "Bloch functions are normal" and the MacLane class (not cited); the remarks after Theorem 4.2
and Theorem 4.3; (4.2.18) (not cited); (4.2.21) (quoted from Ahlfors and Golusin, not cited); "functions continuous
in `𝔻 ∪ 𝕋` belong to `B₀`" (not cited).

**Conventions.** Functions analytic in `𝔻` are `g : ℂ → ℂ` with `DifferentiableOn ℂ g unitDisc`. The seminorm is
`ℝ≥0∞`-valued; for a Bloch function its real value is `(blochSeminorm g).toReal`. A conformal self-map `τ ∈ Möb(𝔻)`
is written `c (z - a)/(1 - ā z)`, `|c| = 1`, `|a| < 1` ((1.2.2)). `log h` for a zero-free `h` is a holomorphic
logarithm `L` of `h` (the seminorm of `L` does not depend on the branch).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto)

/-- **Definition (4.2.1)** (§4.2). The Bloch seminorm `‖g‖_B = sup_{z ∈ 𝔻} (1 - |z|²)|g'(z)|`.
Modelling: for a `g` that is not analytic in `𝔻` the terms use Lean's junk `deriv = 0`; every statement assumes `g`
analytic in `𝔻`. -/
def blochSeminorm (g : ℂ → ℂ) : ℝ≥0∞ :=
  ⨆ z ∈ unitDisc, ENNReal.ofReal ((1 - ‖z‖ ^ 2) * ‖deriv g z‖)

/-- **Definition (4.2.1)** (§4.2; cited). `g` is a Bloch function: `g` is analytic in `𝔻` and `‖g‖_B < ∞`. -/
def IsBloch (g : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ g unitDisc ∧ blochSeminorm g < ⊤

/-- **Formula (4.2.3)** (§4.2; cited in the proof of Theorem 4.2 and at l. 3673). `‖g ∘ τ‖_B = ‖g‖_B` for
`τ ∈ Möb(𝔻)`. -/
theorem eq4_2_3 {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) {c a : ℂ} (hc : ‖c‖ = 1) (ha : ‖a‖ < 1) :
    blochSeminorm (fun z => g (c * (z - a) / (1 - conj a * z))) = blochSeminorm g := by
  sorry

/-- **Formula (4.2.4)** (§4.2; cited at l. 6652 and P2 l. 2453). For `g ∈ B` and `z ∈ 𝔻`,
`|g(z) - g(0)| ≤ ½ ‖g‖_B log((1 + |z|)/(1 - |z|)) = ‖g‖_B λ(z, 0)`. -/
theorem eq4_2_4 {g : ℂ → ℂ} (hg : IsBloch g) {z : ℂ} (hz : z ∈ unitDisc) :
    ENNReal.ofReal ‖g z - g 0‖ ≤ blochSeminorm g * ENNReal.ofReal (1 / 2 * Real.log ((1 + ‖z‖) / (1 - ‖z‖))) ∧
      1 / 2 * Real.log ((1 + ‖z‖) / (1 - ‖z‖)) = hypDistD z 0 := by
  sorry

/-- **Formula (4.2.5)** (§4.2; cited at l. 6043 and P2 l. 2357, 2363). For `g ∈ B`,
`|g(z₁) - g(z₂)| ≤ ‖g‖_B λ(z₁, z₂)` for `z₁, z₂ ∈ 𝔻`. -/
theorem eq4_2_5 {g : ℂ → ℂ} (hg : IsBloch g) {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ unitDisc) (hz₂ : z₂ ∈ unitDisc) :
    ENNReal.ofReal ‖g z₁ - g z₂‖ ≤ blochSeminorm g * ENNReal.ofReal (hypDistD z₁ z₂) := by
  sorry

/-- **Unlabelled claim** (§4.2, l. 3054; used at P2 l. 2413). Every bounded analytic function belongs to `B`. Indeed
if `|g(z)| ≤ 1` for `z ∈ 𝔻`, then `(1 - |z|²)|g'(z)| ≤ 1 - |g(z)|² ≤ 1`. -/
theorem bounded_isBloch {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) :
    ((∀ z ∈ unitDisc, ‖g z‖ ≤ 1) → ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * ‖deriv g z‖ ≤ 1 - ‖g z‖ ^ 2) ∧
      ((∃ M : ℝ, ∀ z ∈ unitDisc, ‖g z‖ ≤ M) → IsBloch g) := by
  sorry

/-- **Proposition 4.1** (§4.2), first part. If `f` maps `𝔻` conformally into `ℂ`, then (4.2.6)
`‖log(f - a)‖_B ≤ 4` for `a ∉ f(𝔻)` and (4.2.7) `‖log f'‖_B ≤ 6`.
Modelling: `log(f - a)` and `log f'` are holomorphic logarithms (their seminorms do not depend on the branch); the OCR
splits the display numbers "(6)" and (7). -/
theorem prop4_1_a {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hinj : InjOn f unitDisc) :
    (∀ a ∉ f '' unitDisc, ∀ L : ℂ → ℂ, DifferentiableOn ℂ L unitDisc → (∀ z ∈ unitDisc, exp (L z) = f z - a) →
      blochSeminorm L ≤ 4) ∧
    ∀ L : ℂ → ℂ, DifferentiableOn ℂ L unitDisc → (∀ z ∈ unitDisc, exp (L z) = deriv f z) → blochSeminorm L ≤ 6 := by
  sorry

/-- **Proposition 4.1** (§4.2), second part. Conversely, if `‖g‖_B ≤ 1`, then `g = log f'` for some conformal map `f`
of `𝔻` into `ℂ`. -/
theorem prop4_1_b {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g unitDisc) (hn : blochSeminorm g ≤ 1) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f unitDisc ∧ InjOn f unitDisc ∧ ∀ z ∈ unitDisc, deriv f z = exp (g z) := by
  sorry

/-- The harmonic function `u(z) = arg(i + z) - arg(1 + iz)` of the proof of Theorem 4.2, (4.2.13) (helper). It is
positive in `𝔻`, tends to `0` on the arc of `𝕋` through `1` and to `π` on the arc through `-1` between `±i`; its level
set `u = γ` is the arc in `𝔻` of the circle through `±i` that forms the angle `γ` with `𝕋`. -/
def luneFun (z : ℂ) : ℝ :=
  arg (I + z) - arg (1 + I * z)

/-- **Definition** (§4.2, l. 3106; used in Theorem 4.2; Fig. 4.1). The circle or line `C` forms the angle `γ`
(`0 ≤ γ < π`) with `𝕋` towards the domain `G ⊆ 𝔻 ∖ C`.
Modelling: after a conformal self-map `τ(z) = c(z - a)/(1 - āz)` of `𝔻` (which preserves angles):
- `0 < γ < π`: `τ(C ∩ 𝔻)` is the level set `{u = γ}` of `luneFun` (the arc through `±i` forming the angle `γ` with
  `𝕋`), and `τ(G)` lies in the lune `{u < γ}` between this arc and the arc of `𝕋` through `1`;
- `γ = 0` (`C` touches `𝕋`): `τ(C ∩ 𝔻)` is the horocycle `{|z - 1/2| = 1/2} ∖ {1}` and `τ(G)` lies outside it. -/
def IsAngleTowards (C G : Set ℂ) (γ : ℝ) : Prop :=
  ∃ c a : ℂ, ‖c‖ = 1 ∧ ‖a‖ < 1 ∧
    ((0 < γ ∧ γ < π ∧ (fun z => c * (z - a) / (1 - conj a * z)) '' (C ∩ unitDisc) = {z ∈ unitDisc | luneFun z = γ} ∧
        (fun z => c * (z - a) / (1 - conj a * z)) '' G ⊆ {z ∈ unitDisc | luneFun z < γ}) ∨
      (γ = 0 ∧ (fun z => c * (z - a) / (1 - conj a * z)) '' (C ∩ unitDisc) = {z ∈ unitDisc | ‖z - 1 / 2‖ = 1 / 2} ∧
        (fun z => c * (z - a) / (1 - conj a * z)) '' G ⊆ {z ∈ unitDisc | 1 / 2 < ‖z - 1 / 2‖}))

/-- **Theorem 4.2** (§4.2), part (i). Let `C` be a circle or line with `C ∩ 𝕋 ≠ ∅` and let `G` be a domain with
(4.2.8) `G ⊆ 𝔻 ∖ C`, `A = ∂G ∖ C ⊆ 𝔻`. If `g ∈ B` and (4.2.9) `c = γ‖g‖_B/(2 sin γ)` (`0 ≤ γ < π`), where `γ` is
the angle between `C` and `𝕋` towards `G`, then `|g(z)| ≤ a ≤ c` for `z ∈ A` implies
`|g(z)| ≤ 2c/(log(c/a) + 1)` for `z ∈ G`.
Modelling: `c = ‖g‖_B/2` for `γ = 0` (the limit, l. 3127); `a > 0`. -/
theorem thm4_2_i {C G : Set ℂ} (hC : (∃ z₀ : ℂ, ∃ r > (0 : ℝ), C = sphere z₀ r) ∨
      ∃ p v : ℂ, v ≠ 0 ∧ C = {z | ∃ t : ℝ, z = p + t * v})
    (hCT : (C ∩ sphere 0 1).Nonempty) (hGo : IsOpen G) (hGc : IsConnected G) (hGC : G ⊆ unitDisc \ C)
    (hA : frontier G \ C ⊆ unitDisc) {γ : ℝ} (hγ : IsAngleTowards C G γ) {g : ℂ → ℂ} (hg : IsBloch g) {c : ℝ}
    (hc : c = if γ = 0 then (blochSeminorm g).toReal / 2 else γ * (blochSeminorm g).toReal / (2 * Real.sin γ))
    {a : ℝ} (ha0 : 0 < a) (hac : a ≤ c) (hgA : ∀ z ∈ frontier G \ C, ‖g z‖ ≤ a) :
    ∀ z ∈ G, ‖g z‖ ≤ 2 * c / (Real.log (c / a) + 1) := by
  sorry

/-- **Theorem 4.2** (§4.2), part (ii). Under the hypotheses of `thm4_2_i`, `|g(z)| ≥ a ≥ ec` for `z ∈ A` implies
`|g(z)| ≥ e⁻¹ a` for `z ∈ G`. -/
theorem thm4_2_ii {C G : Set ℂ} (hC : (∃ z₀ : ℂ, ∃ r > (0 : ℝ), C = sphere z₀ r) ∨
      ∃ p v : ℂ, v ≠ 0 ∧ C = {z | ∃ t : ℝ, z = p + t * v})
    (hCT : (C ∩ sphere 0 1).Nonempty) (hGo : IsOpen G) (hGc : IsConnected G) (hGC : G ⊆ unitDisc \ C)
    (hA : frontier G \ C ⊆ unitDisc) {γ : ℝ} (hγ : IsAngleTowards C G γ) {g : ℂ → ℂ} (hg : IsBloch g) {c : ℝ}
    (hc : c = if γ = 0 then (blochSeminorm g).toReal / 2 else γ * (blochSeminorm g).toReal / (2 * Real.sin γ))
    {a : ℝ} (hac : Real.exp 1 * c ≤ a) (hgA : ∀ z ∈ frontier G \ C, a ≤ ‖g z‖) :
    ∀ z ∈ G, Real.exp (-1) * a ≤ ‖g z‖ := by
  sorry

/-- **Theorem 4.2** (§4.2), part (iii). Under the hypotheses of `thm4_2_i`, `dist(g(z), g(A)) ≤ ec` for `z ∈ G`. -/
theorem thm4_2_iii {C G : Set ℂ} (hC : (∃ z₀ : ℂ, ∃ r > (0 : ℝ), C = sphere z₀ r) ∨
      ∃ p v : ℂ, v ≠ 0 ∧ C = {z | ∃ t : ℝ, z = p + t * v})
    (hCT : (C ∩ sphere 0 1).Nonempty) (hGo : IsOpen G) (hGc : IsConnected G) (hGC : G ⊆ unitDisc \ C)
    (hA : frontier G \ C ⊆ unitDisc) {γ : ℝ} (hγ : IsAngleTowards C G γ) {g : ℂ → ℂ} (hg : IsBloch g) {c : ℝ}
    (hc : c = if γ = 0 then (blochSeminorm g).toReal / 2 else γ * (blochSeminorm g).toReal / (2 * Real.sin γ)) :
    ∀ z ∈ G, infDist (g z) (g '' (frontier G \ C)) ≤ Real.exp 1 * c := by
  sorry

/-- **Formula (4.2.10)** (§4.2; cited in the proof of Proposition 4.6). With `c` as in (4.2.9),
`c ≤ π‖g‖_B/(2(π - γ)) ≤ (4/π) c` for `0 ≤ γ < π`.
Modelling: for any value `n = ‖g‖_B ≥ 0`, with `c = n/2` for `γ = 0`. -/
theorem eq4_2_10 {n γ : ℝ} (hn : 0 ≤ n) (hγ0 : 0 ≤ γ) (hγπ : γ < π) :
    (if γ = 0 then n / 2 else γ * n / (2 * Real.sin γ)) ≤ π * n / (2 * (π - γ)) ∧
      π * n / (2 * (π - γ)) ≤ 4 / π * (if γ = 0 then n / 2 else γ * n / (2 * Real.sin γ)) := by
  sorry

/-- **Theorem 4.3** (§4.2; Lehto–Virtanen). Let `Γ` be a Jordan arc in `𝔻` ending at `ζ ∈ 𝕋`. If `g ∈ B` and if
(4.2.14) `g(z) → b ∈ Ĉ` as `z → ζ`, `z ∈ Γ`, then `g` has the angular limit `b` at `ζ`. -/
theorem thm4_3 {g : ℂ → ℂ} (hg : IsBloch g) {Γ : Set ℂ} {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (hΓ : IsArcEndingAt Γ ζ) {b : ExtPlane} (hlim : Tendsto (fun z => (g z : ExtPlane)) (𝓝[Γ] ζ) (𝓝 b)) :
    HasAngularLimit (fun z => (g z : ExtPlane)) ζ b := by
  sorry

/-- **Definition** (§4.2, l. 3215; cited at P2 l. 257). `g` has the asymptotic value `b ∈ Ĉ` at `ζ ∈ 𝕋`: (4.2.14)
`g(z) → b` as `z → ζ`, `z ∈ Γ`, for some curve `Γ` in `𝔻` ending at `ζ`. -/
def HasAsymptoticValue (g : ℂ → ℂ) (ζ : ℂ) (b : ExtPlane) : Prop :=
  ζ ∈ sphere (0 : ℂ) 1 ∧ ∃ Γ : Set ℂ, IsCurveEndingAt Γ ζ ∧ Tendsto (fun z => (g z : ExtPlane)) (𝓝[Γ] ζ) (𝓝 b)

/-- **Proposition 4.4** (§4.2). Let `Γ` be a Jordan arc in `𝔻` ending at `ζ ∈ 𝕋` and let `g ∈ B`. For `0 < α < π/2`
there exists `K = K(α)` such that (4.2.17) `dist(g(z), g(Γ)) ≤ K ‖g‖_B` for `z ∈ Δ`, where
`Δ = {|arg(1 - ζ̄z)| < α, |z - ζ| < ρ}` with suitable `ρ > 0`.
Modelling: `K` depends only on `α`; `ρ` depends on `Γ` and `g`. -/
theorem prop4_4 {α : ℝ} (hα0 : 0 < α) (hα1 : α < π / 2) :
    ∃ K : ℝ, ∀ (g : ℂ → ℂ) (Γ : Set ℂ) (ζ : ℂ), IsBloch g → ζ ∈ sphere (0 : ℂ) 1 → IsArcEndingAt Γ ζ →
      ∃ ρ > (0 : ℝ), ∀ z ∈ stolzAngleP ζ α ρ, infDist (g z) (g '' Γ) ≤ K * (blochSeminorm g).toReal := by
  sorry

/-- **Formula (4.2.19)** (§4.2; cited in the proof of Corollary 4.5 and at P2 l. 2429). For `g ∈ B` and a Jordan arc
`Γ` ending at `ζ ∈ 𝕋`: `Re g → ±∞` on `Γ` implies that `Re g` has the angular limit `±∞` at `ζ`. -/
theorem eq4_2_19 {g : ℂ → ℂ} (hg : IsBloch g) {Γ : Set ℂ} {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (hΓ : IsArcEndingAt Γ ζ) :
    (Tendsto (fun z => (g z).re) (𝓝[Γ] ζ) atTop → ∀ α ρ : ℝ, 0 < α → α < π / 2 → 0 < ρ → ρ < 2 * Real.cos α →
      Tendsto (fun z => (g z).re) (𝓝[stolzAngleP ζ α ρ] ζ) atTop) ∧
    (Tendsto (fun z => (g z).re) (𝓝[Γ] ζ) atBot → ∀ α ρ : ℝ, 0 < α → α < π / 2 → 0 < ρ → ρ < 2 * Real.cos α →
      Tendsto (fun z => (g z).re) (𝓝[stolzAngleP ζ α ρ] ζ) atBot) := by
  sorry

/-- **Corollary 4.5** (§4.2). Let `h` be analytic and nonzero in `𝔻`. If `log h ∈ B` and if `h` has the asymptotic
value `b ∈ Ĉ` at `ζ ∈ 𝕋`, then `h` has the angular limit `b` at `ζ`. -/
theorem cor4_5 {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h unitDisc) (hh0 : ∀ z ∈ unitDisc, h z ≠ 0) {L : ℂ → ℂ}
    (hL : IsBloch L) (hLh : ∀ z ∈ unitDisc, exp (L z) = h z) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) {b : ExtPlane}
    (hb : HasAsymptoticValue h ζ b) :
    HasAngularLimit (fun z => (h z : ExtPlane)) ζ b := by
  sorry

/-- **Proposition 4.6** (§4.2). Let `I` be an arc of `𝕋` and let `g ∈ B`. Then there exists `ζ ∈ I` such that
(4.2.20) `|g(rζ) - g(0)| ≤ 22 ‖g‖_B/Λ(I)` for `0 ≤ r < 1`.
Modelling: `I = {e^{it} : t₁ ≤ t ≤ t₂}` with `t₁ < t₂ ≤ t₁ + 2π`, `Λ(I) = t₂ - t₁`. -/
theorem prop4_6 {g : ℂ → ℂ} (hg : IsBloch g) {t₁ t₂ : ℝ} (ht : t₁ < t₂) (ht' : t₂ ≤ t₁ + 2 * π) :
    ∃ t ∈ Icc t₁ t₂, ∀ r : ℝ, 0 ≤ r → r < 1 →
      ENNReal.ofReal ‖g (r * exp (t * I)) - g 0‖ ≤ ENNReal.ofReal (22 / (t₂ - t₁)) * blochSeminorm g := by
  sorry

/-- **Definition (4.2.22)** (§4.2; cited at l. 6762). The little Bloch space `B₀`: the Bloch functions `g` with
`(1 - |z|²)|g'(z)| → 0` as `|z| → 1-`. -/
def IsLittleBloch (g : ℂ → ℂ) : Prop :=
  IsBloch g ∧ ∀ ε > (0 : ℝ), ∃ r < (1 : ℝ), ∀ z : ℂ, r < ‖z‖ → ‖z‖ < 1 → (1 - ‖z‖ ^ 2) * ‖deriv g z‖ < ε

end Pommerenke1992
