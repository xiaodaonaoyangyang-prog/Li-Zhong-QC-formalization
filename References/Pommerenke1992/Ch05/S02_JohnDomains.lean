import References.Pommerenke1992.Ch05.S01_Overview

/-!
# Pommerenke 1992, Ch. 5 §5.2 John Domains

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §5.2; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 4007–4399.

* Definition (John domain, (5.2.1); Martio–Sarvas; cited at l. 4595) — `IsJohnDomainWith`, `IsJohnDomain`
* Unlabelled (§5.2, l. 4015: the boundary of a John domain is locally connected; used at l. 4082 with Theorem 2.1) —
  `johnDomain_isLocConn`
* Proposition 5.1 — `prop5_1`
* Definition (the sets `B(z)`, (5.2.3), and `I(z)`, (5.2.4); cited at l. 4425, 4599) — `boxB`, `arcI`
* Theorem 5.2 — `thm5_2`
* Corollary 5.3 — `cor5_3`
* Theorem 5.4 (Smith–Stegenga) — `thm5_4`
* Theorem 5.5 — `thm5_5_i`, `thm5_5_ii`

Not items (DESIGN §3): the characterization for piecewise smooth curves (l. 4015, not cited); (5.2.6)–(5.2.11)
(steps of the proof of Theorem 5.2; P2 l. 2987 reuses the method); (5.2.20), (5.2.21) and the remarks after Theorem
5.5 (FiLe87, "every John domain is a Hölder domain but not conversely"; not cited).

**Conventions.** As in §5.1. `G ⊆ ℂ` is a bounded simply connected domain (`IsSimplyConnectedDomain (toExt G)`),
`f` maps `𝔻` conformally onto `G` and `F` is the continuous extension of `f` to `𝔻̄` (Theorem 2.1). A rectilinear
crosscut `[a, b]` of `G` has `a ≠ b` in `∂G` and `(a, b) ⊆ G`. Arcs of `𝕋` are `arcT t₁ t₂`, with length `t₂ - t₁`.
Diameters are `Metric.ediam`; `d_f(z) = dist(f(z), ∂G)` is `distToBoundary f z` (§1.3). The constants `M_j` are, as
the book says, "suitable positive constants": `∃ M` after the domain, except in Theorem 5.2, where the book states
their dependence.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto IsJordanCurve)
open LehtoVirtanen1973 (IsSimplyConnectedDomain)

/-- **Definition (5.2.1)** (§5.2; Martio–Sarvas; cited at l. 4595). The bounded simply connected domain `G` is a John
domain with constant `M₁`: for every rectilinear crosscut `[a, b]` of `G`, `diam H ≤ M₁ |a - b|` holds for one of the
two components `H` of `G ∖ [a, b]`. -/
def IsJohnDomainWith (G : Set ℂ) (M₁ : ℝ) : Prop :=
  Bornology.IsBounded G ∧ IsOpen G ∧ IsConnected G ∧ IsSimplyConnectedDomain (toExt G) ∧
    ∀ a ∈ frontier G, ∀ b ∈ frontier G, a ≠ b → openSegment ℝ a b ⊆ G →
      ∃ x ∈ G \ segment ℝ a b,
        Metric.ediam (connectedComponentIn (G \ segment ℝ a b) x) ≤ ENNReal.ofReal (M₁ * ‖a - b‖)

/-- **Definition** (§5.2). `G` is a John domain: `IsJohnDomainWith G M₁` for some `M₁`. -/
def IsJohnDomain (G : Set ℂ) : Prop :=
  ∃ M₁ : ℝ, IsJohnDomainWith G M₁

/-- **Unlabelled claim** (§5.2, l. 4015; used at l. 4082, "`f` is continuous in `𝔻̄` by Theorem 2.1"). It is clear
that the boundary of a John domain is locally connected.
Modelling: `IsLocConn` of §2.2; with `thm2_1` it gives the continuous extension of a conformal map onto `G`. -/
theorem johnDomain_isLocConn {G : Set ℂ} (hG : IsJohnDomain G) : IsLocConn (frontier G) := by
  sorry

/-- **Proposition 5.1** (§5.2). Let `G` be a John domain. If `C` is a crosscut of `G`, then (5.2.2)
`diam H ≤ M₂ diam C` holds for one of the components `H` of `G ∖ C`.
Modelling: crosscuts as in §2.4 (`IsCrosscut`, in `Ĉ`); `M₂` depends only on the constant `M₁` of (5.2.1) (the
proof gives `M₂ = 2M₁ + 2`; Theorem 5.2 relies on this dependence). -/
theorem prop5_1 (M₁ : ℝ) :
    ∃ M₂ : ℝ, ∀ G : Set ℂ, IsJohnDomainWith G M₁ → ∀ C : Set ℂ, IsCrosscut (toExt G) (toExt C) →
      ∃ x ∈ G \ C, Metric.ediam (connectedComponentIn (G \ C) x) ≤ ENNReal.ofReal M₂ * Metric.ediam C := by
  sorry

/-- **Definition (5.2.3)** (§5.2; cited at l. 4599). `B(re^{it}) = {ρe^{iϑ} : r ≤ ρ ≤ 1, |ϑ - t| ≤ π(1 - r)}`
(`0 ≤ r < 1`); `B(0) = 𝔻̄`.
Modelling: `t = arg z` (for `z = 0` the set is `𝔻̄` for every `t`). -/
def boxB (z : ℂ) : Set ℂ :=
  {w | ∃ ρ ϑ : ℝ, ‖z‖ ≤ ρ ∧ ρ ≤ 1 ∧ |ϑ - arg z| ≤ π * (1 - ‖z‖) ∧ w = ρ * exp (ϑ * I)}

/-- **Definition (5.2.4)** (§5.2; cited at l. 4425). `I(re^{it}) = 𝕋 ∩ ∂B(re^{it}) = {e^{iϑ} : |ϑ - t| ≤ π(1 - r)}`;
`I(0) = 𝕋`. -/
def arcI (z : ℂ) : Set ℂ :=
  {w | ∃ ϑ : ℝ, |ϑ - arg z| ≤ π * (1 - ‖z‖) ∧ w = exp (ϑ * I)}

/-- **Theorem 5.2** (§5.2). Let `f` map `𝔻` conformally onto `G` such that (5.2.5) `d_f(0) ≥ c diam G`. Then the
following conditions are equivalent:
(i) `G` is a John domain;
(ii) `diam f(B(z)) ≤ M₃ d_f(z)` for `z ∈ 𝔻`;
(iii) there exists `α` with `0 < α ≤ 1` such that `|f'(ζ)| ≤ M₄ |f'(z)| ((1 - |ζ|)/(1 - |z|))^{α-1}` for
`ζ ∈ 𝔻 ∩ B(z)`, `z ∈ 𝔻`;
(iv) there exists `β > 0` such that, for all arcs `A ⊆ I ⊆ 𝕋`, `Λ(A) ≤ β Λ(I)` implies `diam f(A) ≤ ½ diam f(I)`;
(iv') for every `ε > 0` there exists `δ > 0` such that `Λ(A) ≤ δ Λ(I)` implies `diam f(A) ≤ ε diam f(I)`.
The constants `M₃, M₄, α, β` depend only on each other, on `M₁` and on `c`; (5.2.5) is used only for (i) ⇒ (ii).
Modelling:
- The theorem is stated as the cycle (i) ⇒ (ii) ⇒ (iii) ⇒ (iv′) ⇒ (iv) ⇒ (i) of the proof, with uniform constants:
  each implication holds for all `f` with constants depending only on the constants of its hypothesis (and on `c`
  for (i) ⇒ (ii)). The equivalence of the five conditions follows.
- `G` is bounded and `f` has a continuous extension `F` to `𝔻̄`, a hypothesis here: (ii), (iv), (iv′) are conditions
  on the boundary values; (i) implies the extension by l. 4015 and Theorem 2.1 (`johnDomain_isLocConn`, `thm2_1`), and
  (iii) implies it (Hölder continuity); `f(B(z))`, `f(A)` are images under `F`.
- (iv′) ⇒ (iv) is the instance `ε = 1/2` (with `β = δ`) of the third conjunct.
- Arcs `A ⊆ I` are `arcT s₁ s₂ ⊆ arcT t₁ t₂` with `t₁ ≤ s₁ < s₂ ≤ t₂ ≤ t₁ + 2π`. -/
theorem thm5_2 {c : ℝ} (hc : 0 < c) :
    (∀ M₁ : ℝ, ∃ M₃ : ℝ, ∀ f F : ℂ → ℂ, IsConformalOnto f unitDisc (f '' unitDisc) →
      Bornology.IsBounded (f '' unitDisc) → ContinuousOn F (closedBall 0 1) → EqOn F f unitDisc →
      ENNReal.ofReal (c) * Metric.ediam (f '' unitDisc) ≤ ENNReal.ofReal (distToBoundary f 0) →
      IsJohnDomainWith (f '' unitDisc) M₁ →
      ∀ z ∈ unitDisc, Metric.ediam (F '' boxB z) ≤ ENNReal.ofReal (M₃ * distToBoundary f z)) ∧
    (∀ M₃ : ℝ, ∃ α M₄ : ℝ, 0 < α ∧ α ≤ 1 ∧ ∀ f F : ℂ → ℂ, IsConformalOnto f unitDisc (f '' unitDisc) →
      Bornology.IsBounded (f '' unitDisc) → ContinuousOn F (closedBall 0 1) → EqOn F f unitDisc →
      (∀ z ∈ unitDisc, Metric.ediam (F '' boxB z) ≤ ENNReal.ofReal (M₃ * distToBoundary f z)) →
      ∀ z ∈ unitDisc, ∀ ζ ∈ unitDisc ∩ boxB z,
        ‖deriv f ζ‖ ≤ M₄ * ‖deriv f z‖ * ((1 - ‖ζ‖) / (1 - ‖z‖)) ^ (α - 1)) ∧
    (∀ α M₄ : ℝ, 0 < α → α ≤ 1 → ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ f F : ℂ → ℂ,
      IsConformalOnto f unitDisc (f '' unitDisc) → Bornology.IsBounded (f '' unitDisc) →
      ContinuousOn F (closedBall 0 1) → EqOn F f unitDisc →
      (∀ z ∈ unitDisc, ∀ ζ ∈ unitDisc ∩ boxB z,
        ‖deriv f ζ‖ ≤ M₄ * ‖deriv f z‖ * ((1 - ‖ζ‖) / (1 - ‖z‖)) ^ (α - 1)) →
      ∀ t₁ s₁ s₂ t₂ : ℝ, t₁ ≤ s₁ → s₁ < s₂ → s₂ ≤ t₂ → t₂ ≤ t₁ + 2 * π → s₂ - s₁ ≤ δ * (t₂ - t₁) →
        Metric.ediam (F '' arcT s₁ s₂) ≤ ENNReal.ofReal ε * Metric.ediam (F '' arcT t₁ t₂)) ∧
    (∀ β : ℝ, 0 < β → ∃ M₁ : ℝ, ∀ f F : ℂ → ℂ, IsConformalOnto f unitDisc (f '' unitDisc) →
      Bornology.IsBounded (f '' unitDisc) → ContinuousOn F (closedBall 0 1) → EqOn F f unitDisc →
      (∀ t₁ s₁ s₂ t₂ : ℝ, t₁ ≤ s₁ → s₁ < s₂ → s₂ ≤ t₂ → t₂ ≤ t₁ + 2 * π → s₂ - s₁ ≤ β * (t₂ - t₁) →
        Metric.ediam (F '' arcT s₁ s₂) ≤ ENNReal.ofReal (1 / 2) * Metric.ediam (F '' arcT t₁ t₂)) →
      IsJohnDomainWith (f '' unitDisc) M₁) := by
  sorry

/-- **Corollary 5.3** (§5.2). Let `f` map `𝔻` conformally onto a John domain. If `z ∈ 𝔻`, then (5.2.12)
`|f(ζ₁) - f(ζ₂)| ≤ M₈ d_f(z) (|ζ₁ - ζ₂|/(1 - |z|))^α` for `ζ₁, ζ₂ ∈ B(z)`.
Modelling: `α > 0` is the exponent of Theorem 5.2 (iii) (here: some `α > 0`); `f` on `𝕋` is its continuous extension
`F`; `M₈` depends on `f`. -/
theorem cor5_3 {f F : ℂ → ℂ} (hf : IsConformalOnto f unitDisc (f '' unitDisc)) (hG : IsJohnDomain (f '' unitDisc))
    (hFc : ContinuousOn F (closedBall 0 1)) (hFf : EqOn F f unitDisc) :
    ∃ α M₈ : ℝ, 0 < α ∧ ∀ z ∈ unitDisc, ∀ ζ₁ ∈ boxB z, ∀ ζ₂ ∈ boxB z,
      ‖F ζ₁ - F ζ₂‖ ≤ M₈ * distToBoundary f z * (‖ζ₁ - ζ₂‖ / (1 - ‖z‖)) ^ α := by
  sorry

/-- **Theorem 5.4** (§5.2; Smith–Stegenga). If (5.2.13) `f(z) = Σ_{n≥0} a_n zⁿ` maps `𝔻` conformally onto a John
domain, then (5.2.14) `Σ_{n≥1} n^{1+δ} |a_n|² < ∞` for some `δ > 0`.
Modelling: `a_n = f^{(n)}(0)/n!` (`sCoeff`, §1.3). -/
theorem thm5_4 {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc (f '' unitDisc)) (hG : IsJohnDomain (f '' unitDisc)) :
    ∃ δ > (0 : ℝ), Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 + δ) * ‖sCoeff f (n + 1)‖ ^ 2) := by
  sorry

/-- **Theorem 5.5** (§5.2), part (i). Let `f` map `𝔻` conformally onto a John domain `G` and let `ζ ∈ 𝕋`. If
`f'(ζ) ≠ ∞` exists, then (5.2.16) `(f(z) - f(ζ))/(z - ζ) → f'(ζ)` as `z → ζ`, `z ∈ 𝔻̄`.
Modelling: `f` on `𝕋` is its continuous extension `F`; `f'(ζ)` is the angular derivative (4.3.1). -/
theorem thm5_5_i {f F : ℂ → ℂ} (hf : IsConformalOnto f unitDisc (f '' unitDisc))
    (hG : IsJohnDomain (f '' unitDisc)) (hFc : ContinuousOn F (closedBall 0 1)) (hFf : EqOn F f unitDisc)
    {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) {a : ℂ} (ha : HasAngularDerivative f ζ a) :
    Tendsto (fun z => (F z - F ζ) / (z - ζ)) (𝓝[closedBall 0 1 \ {ζ}] ζ) (𝓝 a) := by
  sorry

/-- **Theorem 5.5** (§5.2), part (ii). Let `f` map `𝔻` conformally onto a John domain `G` and let `ζ = e^{iϑ} ∈ 𝕋`.
If `f` is isogonal at `ζ`, then there is `γ` such that (5.2.17) `arg[(f(z) - f(ζ))/(z - ζ)] → γ` as `z → ζ`,
`z ∈ 𝔻̄`, and `∂G` has a tangent at `f(ζ)`.
Modelling: a limit of directions; the tangent is a corner of opening `π` (§3.4) of the extension `F`, viewed in
`Ĉ`. -/
theorem thm5_5_ii {f F : ℂ → ℂ} (hf : IsConformalOnto f unitDisc (f '' unitDisc))
    (hG : IsJohnDomain (f '' unitDisc)) (hFc : ContinuousOn F (closedBall 0 1)) (hFf : EqOn F f unitDisc)
    {ϑ : ℝ} (hiso : IsIsogonalAt f (exp (ϑ * I))) :
    (∃ γ : ℝ, Tendsto (fun z => (F z - F (exp (ϑ * I))) / (z - exp (ϑ * I)) /
        (‖(F z - F (exp (ϑ * I))) / (z - exp (ϑ * I))‖ : ℂ))
      (𝓝[closedBall 0 1 \ {exp (ϑ * I)}] (exp (ϑ * I))) (𝓝 (exp (γ * I)))) ∧
    ∃ β : ℝ, HasTangentAt (fun z => (F z : ExtPlane)) ϑ β := by
  sorry

end Pommerenke1992
