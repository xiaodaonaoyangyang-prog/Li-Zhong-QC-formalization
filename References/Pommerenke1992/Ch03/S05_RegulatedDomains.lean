import References.Pommerenke1992.Ch03.S04_TangentsAndCorners

/-!
# Pommerenke 1992, Ch. 3 §3.5 Regulated Domains

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §3.5; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 2500–2767.

* Definition (regulated function, (3.5.1)) — `IsRegulatedOn`
* Formula (3.5.2) (regulated functions are the uniform limits of step functions, quoted from Dieudonné; cited in the
  proof of Theorem 3.14) — `eq3_5_2`
* Unlabelled (§3.5, l. 2516: a regulated function has `β(t+) = β(t-)` except for countably many `t`; used at l. 2534)
  — `isRegulatedOn_countable_jumps`
* Definition (regulated domain; the forward tangent `β`, (3.5.4), cited at l. 2901; the jump conventions (3.5.5),
  (3.5.6), cited at l. 2750) — `IsForwardTangent`, `IsRegulatedForMod`, `IsRegulatedFor`, `IsRegulatedDomain`
* Proposition 3.12 — `prop3_12`
* Proposition 3.13 — `prop3_13`
* Theorem 3.14 — `thm3_14`
* Theorem 3.15 — `thm3_15`
* Formula (3.5.14) (and `β(t + 2π) = β(t) + 2π`; cited at l. 2829) — `eq3_5_14`
* Definition (bounded boundary rotation, (3.5.17)) — `IsBoundedBoundaryRotation`
* Definition (the Riemann–Stieltjes integral `∫ φ dβ` of Corollary 3.16) — `HasRSIntegral`
* Corollary 3.16 — `cor3_16`
* Formula (3.5.19) (the decomposition of a function of bounded variation; cited in the proof of Corollary 3.17) —
  `eq3_5_19`
* Corollary 3.17 (the generalized Schwarz–Christoffel formula) — `cor3_17`

Not items (DESIGN §3): the examples (piecewise smooth curves, (3.4.16), Fig. 3.7); the independence of the definitions
from the parametrization (l. 2553, 2702, not cited); the converse of Theorem 3.15 "mentioned without proof" (l. 2660,
not cited); `σ_k = 1 - α_k`, resp. `1 + α_k` (l. 2750, immediate from (3.5.5), (3.5.6)).

**Standing assumption** (l. 2518): as in §3.4 (`IsBoundarySetting`); the conformal parametrization (3.5.3) of
`C = ∂G` is `w(t) = F(e^{it})`, which may pass through `∞`.

**Conventions.** As in §3.4. The forward tangent `β` is a real function on `ℝ`. The limit (3.5.4) determines each
value `β(t)` only modulo `2π` (`IsRegulatedForMod`); the book's `β` is the lift normalized by the jump conventions
(3.5.5) and (3.5.6), `β(t+) - β(t-) = π(1 - α)` at a corner of opening `πα` at a finite point and `π(1 + α)` at `∞`
(the openings being those of §3.4, `HasCornerAt`, `HasCornerAtInf`), and by `β(t) = β(t+)` (Proposition 3.13), which
is `IsRegulatedFor`. Every point of `C` is a corner, a cusp or a point with a tangent (l. 2534), so the jump
conventions fix all jumps; the remaining freedom, an additive constant `2πk`, changes no statement. The Stieltjes
integral is the Riemann–Stieltjes integral of a continuous integrand against a function of bounded variation
(`HasRSIntegral`; Mathlib's Stieltjes measures need monotone integrators).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsJordanCurve IsConformalOnto)

/-- **Definition (3.5.1)** (§3.5). `β` is a regulated function on `[a, b]`: the one-sided limits
`β(t-) = lim_{τ → t-} β(τ)` and `β(t+) = lim_{τ → t+} β(τ)` exist for `a ≤ t ≤ b` (the ones inside `[a, b]`). -/
def IsRegulatedOn (β : ℝ → ℝ) (a b : ℝ) : Prop :=
  (∀ t ∈ Ico a b, ∃ l, Tendsto β (𝓝[>] t) (𝓝 l)) ∧ ∀ t ∈ Ioc a b, ∃ l, Tendsto β (𝓝[<] t) (𝓝 l)

/-- **Formula (3.5.2)** (§3.5, quoted from Dieudonné; cited in the proof of Theorem 3.14). `β` is regulated on
`[a, b]` if and only if it can be uniformly approximated by step functions: for every `ε > 0` there are
`a = t₀ < t₁ < ⋯ < tₙ = b` and constants `γ₁, …, γₙ` with (3.5.2) `|β(t) - γ_ν| < ε` for `t_{ν-1} < t < t_ν`. -/
theorem eq3_5_2 {β : ℝ → ℝ} {a b : ℝ} (hab : a < b) :
    IsRegulatedOn β a b ↔
      ∀ ε > (0 : ℝ), ∃ (n : ℕ) (t : Fin (n + 1) → ℝ) (γ : Fin n → ℝ), StrictMono t ∧ t 0 = a ∧
        t (Fin.last n) = b ∧ ∀ ν : Fin n, ∀ s ∈ Ioo (t ν.castSucc) (t ν.succ), |β s - γ ν| < ε := by
  sorry

/-- **Unlabelled claim** (§3.5, l. 2516; used at l. 2534). A regulated function has `β(t+) = β(t-)` except possibly
for countably many `t`. -/
theorem isRegulatedOn_countable_jumps {β : ℝ → ℝ} {a b : ℝ} (hβ : IsRegulatedOn β a b) :
    {t ∈ Ioo a b | ∃ l₁ l₂ : ℝ, Tendsto β (𝓝[>] t) (𝓝 l₁) ∧ Tendsto β (𝓝[<] t) (𝓝 l₂) ∧ l₁ ≠ l₂}.Countable := by
  sorry

/-- **Definition (3.5.4)** (§3.5). `β(t)` is the direction angle of the forward (half-)tangent of the conformal
parametrization `w(t) = F(e^{it})` at `w(t)`: `β(t) = lim_{τ → t+} arg[w(τ) - w(t)]` if `w(t) ≠ ∞`, and
`β(t) = lim_{τ → t+} arg w(τ) + π` if `w(t) = ∞`.
Modelling: limits of directions (the file header); near `t` the values `w(τ)`, `τ > t`, are finite and `≠ w(t)`. -/
def IsForwardTangent (F : ℂ → ExtPlane) (β : ℝ → ℝ) : Prop :=
  ∀ t : ℝ,
    (∀ u : ℂ, F (exp (t * I)) = u → ∀ᶠ τ : ℝ in 𝓝[>] t, ∃ v : ℂ, F (exp (τ * I)) = v ∧ v ≠ u) ∧
    (∀ u : ℂ, F (exp (t * I)) = u →
      Tendsto (fun τ : ℝ => (extVal (F (exp (τ * I))) - u) / (‖extVal (F (exp (τ * I))) - u‖ : ℂ)) (𝓝[>] t)
        (𝓝 (exp (β t * I)))) ∧
    (F (exp (t * I)) = extInf →
      (∀ᶠ τ : ℝ in 𝓝[>] t, ∃ v : ℂ, F (exp (τ * I)) = v ∧ v ≠ 0) ∧
      Tendsto (fun τ : ℝ => extVal (F (exp (τ * I))) / (‖extVal (F (exp (τ * I)))‖ : ℂ)) (𝓝[>] t)
        (𝓝 (-exp (β t * I))))

/-- **Definition** (§3.5, (3.5.4)–(3.5.6)), up to the choice of the values modulo `2π` (helper). Each point of
`C = ∂G` is attained only finitely often by `F` on `𝕋`, and the forward tangent `β(t)` exists for all `t` and
defines a regulated function, with the jumps of (3.5.5), (3.5.6): `β(t+) - β(t-) = π(1 - α)` at a corner of opening
`πα` at `w(t) ≠ ∞`, and `= π(1 + α)` (`πα` the sector angle) at `w(t) = ∞`.
Modelling: "regulated" on every compact interval. The limit (3.5.4) is a limit of directions, so it determines each
value `β(t)` only modulo `2π`: `Function.update β t₀ (β t₀ + 2π)` satisfies this predicate whenever `β` does. The
opening `πα` of the corner at `w(t)` is that of (3.4.1) (`HasCornerAt`, resp. `HasCornerAtInf` for `w(t) = ∞`, read
through a continuous branch of the argument), which determines `α ∈ [0, 2]` itself and not only `α` modulo `2` (at a
cusp the jump `±π` is only fixed this way). -/
def IsRegulatedForMod (F : ℂ → ExtPlane) (β : ℝ → ℝ) : Prop :=
  (∀ p : ExtPlane, {ζ ∈ sphere (0 : ℂ) 1 | F ζ = p}.Finite) ∧ (∀ a b, IsRegulatedOn β a b) ∧
    IsForwardTangent F β ∧
    ∀ t l₁ l₂ : ℝ, Tendsto β (𝓝[>] t) (𝓝 l₁) → Tendsto β (𝓝[<] t) (𝓝 l₂) →
      (∀ α β₀ : ℝ, HasCornerAt F t α β₀ → l₁ - l₂ = π * (1 - α)) ∧
      (∀ α β₀ : ℝ, HasCornerAtInf F t α β₀ → l₁ - l₂ = π * (1 + α))

/-- **Definition** (§3.5, (3.5.4)–(3.5.6)). The domain `G` is regulated, with forward tangent `β`, for the conformal
map `f` with boundary extension `F` (`IsRegulatedForMod`), and `β` is the book's lift: normalized by the jump
conventions (3.5.5), (3.5.6) and by `β(t) = β(t+)` for all `t` ("it follows from Proposition 3.13 that
`β(t+) = β(t)`", l. 2534).
Modelling: `β(t) = β(t+)` fixes the value at each jump, which (3.5.4) leaves free modulo `2π`; the statements do not
depend on the remaining additive constant `2πk`. -/
def IsRegulatedFor (F : ℂ → ExtPlane) (β : ℝ → ℝ) : Prop :=
  IsRegulatedForMod F β ∧ ∀ t : ℝ, Tendsto β (𝓝[>] t) (𝓝 (β t))

/-- **Definition** (§3.5). `G ⊆ ℂ` is a regulated domain: a simply connected domain with locally connected boundary
(the standing assumption) whose conformal parametrization has a regulated forward tangent (`IsRegulatedFor`). -/
def IsRegulatedDomain (G : Set ℂ) : Prop :=
  ∃ (f : ℂ → ℂ) (F : ℂ → ExtPlane) (β : ℝ → ℝ), IsBoundarySetting f G F ∧ IsRegulatedFor F β

/-- **Proposition 3.12** (§3.5). Let `G` be regulated. If `0 < ε < π` and (3.5.7) `|β(t) - γ| < ε`, `w(t) ≠ ∞` for
`t ∈ I`, where `I` is an interval on `ℝ`, then (3.5.8) `|arg[w(τ) - w(t)] - γ| < ε` for `τ, t ∈ I`, `t < τ`.
Modelling: the conclusion says that `w(τ) - w(t) ≠ 0` has an argument within `ε` of `γ`. -/
theorem prop3_12 {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {β : ℝ → ℝ}
    (hβ : IsRegulatedFor F β) {ε γ : ℝ} (hε0 : 0 < ε) (hεπ : ε < π) {J : Set ℝ} (hJ : J.OrdConnected)
    (h7 : ∀ t ∈ J, |β t - γ| < ε ∧ ∃ u : ℂ, F (exp (t * I)) = u) :
    ∀ t ∈ J, ∀ τ ∈ J, t < τ → ∃ φ : ℝ, |φ - γ| < ε ∧
      extVal (F (exp (τ * I))) - extVal (F (exp (t * I))) ≠ 0 ∧
      extVal (F (exp (τ * I))) - extVal (F (exp (t * I))) =
        (‖extVal (F (exp (τ * I))) - extVal (F (exp (t * I)))‖ : ℂ) * exp (φ * I) := by
  sorry

/-- **Proposition 3.13** (§3.5). Let `G` be regulated. Then `β(t+) = β(t)` for all `t`, and if `w(t) ≠ ∞` then
(3.5.9) `β(t-) = lim_{τ → t-} arg[w(t) - w(τ)]`.
Modelling: for any `β` with the limits (3.5.4) (`IsRegulatedForMod`, values modulo `2π`), in the form
`β(t+) ≡ β(t)` modulo `2π`; the book's normalized lift (`IsRegulatedFor`) is the one with `β(t+) = β(t)`. -/
theorem prop3_13 {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {β : ℝ → ℝ}
    (hβ : IsRegulatedForMod F β) :
    ∀ t : ℝ, (∃ k : ℤ, Tendsto β (𝓝[>] t) (𝓝 (β t + 2 * π * k))) ∧
      ∀ u : ℂ, F (exp (t * I)) = u → ∃ l : ℝ, Tendsto β (𝓝[<] t) (𝓝 l) ∧
        Tendsto (fun τ : ℝ => (u - extVal (F (exp (τ * I)))) / (‖u - extVal (F (exp (τ * I)))‖ : ℂ)) (𝓝[<] t)
          (𝓝 (exp (l * I))) := by
  sorry

/-- **Theorem 3.14** (§3.5). The domain `G ⊆ ℂ` is regulated if and only if, for every `ε > 0`, there are finitely
many points `0 = t₀ < t₁ < ⋯ < tₙ = 2π` such that (3.5.10) `w(t) ≠ ∞`, `|arg[w(τ) - w(t)] - γ_ν| < ε`
(`t_{ν-1} < t < τ < t_ν`) for `ν = 1, …, n`, with real constants `γ_ν`.
Modelling: "regulated" for the given conformal map (`IsRegulatedFor F β` for some `β`); the argument condition as in
`prop3_12`. -/
theorem thm3_14 {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) :
    (∃ β : ℝ → ℝ, IsRegulatedFor F β) ↔
      ∀ ε > (0 : ℝ), ∃ (n : ℕ) (t : Fin (n + 1) → ℝ) (γ : Fin n → ℝ), StrictMono t ∧ t 0 = 0 ∧
        t (Fin.last n) = 2 * π ∧ ∀ ν : Fin n, ∀ s ∈ Ioo (t ν.castSucc) (t ν.succ),
          (∃ u : ℂ, F (exp (s * I)) = u) ∧ ∀ τ ∈ Ioo s (t ν.succ), ∃ φ : ℝ, |φ - γ ν| < ε ∧
            extVal (F (exp (τ * I))) - extVal (F (exp (s * I))) ≠ 0 ∧
            extVal (F (exp (τ * I))) - extVal (F (exp (s * I))) =
              (‖extVal (F (exp (τ * I))) - extVal (F (exp (s * I)))‖ : ℂ) * exp (φ * I) := by
  sorry

/-- **Theorem 3.15** (§3.5). Let `f` map `𝔻` conformally onto a regulated domain. Then, for `z ∈ 𝔻`,
(3.5.12) `log f'(z) = log|f'(0)| + (i/2π) ∫₀^{2π} (e^{it} + z)/(e^{it} - z) (β(t) - t - π/2) dt`, where `β(t)` is the
direction angle of the forward tangent at `f(e^{it})`, and furthermore (3.5.13)
`arg f'(z) + ((β(t+) - β(t-))/π)(arg(z - e^{it}) - t - π/2) → β(t) - t - π/2` as `z → e^{it}`, `z ∈ 𝔻`, for each `t`.
Modelling: `log f'` is the holomorphic logarithm `L` of `f'` given by (3.5.12); `arg f' = Im L`; `arg(z - e^{it})` is
the branch (3.4.2); `β(t+) = β(t)` (Proposition 3.13) and `β(t-)` is the left limit `l`. -/
theorem thm3_15 {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {β : ℝ → ℝ}
    (hβ : IsRegulatedFor F β) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L unitDisc ∧ (∀ z ∈ unitDisc, exp (L z) = deriv f z) ∧
      (∀ z ∈ unitDisc, L z = (Real.log ‖deriv f 0‖ : ℂ) + I / (2 * π) *
        ∫ t in (0 : ℝ)..2 * π, (exp (t * I) + z) / (exp (t * I) - z) * ((β t - t - π / 2 : ℝ) : ℂ)) ∧
      ∀ t l : ℝ, Tendsto β (𝓝[<] t) (𝓝 l) →
        Tendsto (fun z => (L z).im + (β t - l) / π * ((logAt t z).im - t - π / 2))
          (𝓝[unitDisc] (exp (t * I))) (𝓝 (β t - t - π / 2)) := by
  sorry

/-- **Formula (3.5.14)** (§3.5, following Theorem 3.15; cited at l. 2829). Under the hypotheses of Theorem 3.15,
`β(t + 2π) = β(t) + 2π`, and `arg f'(re^{it}) → (β(t+) + β(t-))/2 - t - π/2` as `r → 1-`.
Modelling: `arg f' = Im L` for the logarithm `L` of (3.5.12). -/
theorem eq3_5_14 {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {β : ℝ → ℝ}
    (hβ : IsRegulatedFor F β) {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L unitDisc)
    (hLf : ∀ z ∈ unitDisc, exp (L z) = deriv f z)
    (h12 : ∀ z ∈ unitDisc, L z = (Real.log ‖deriv f 0‖ : ℂ) + I / (2 * π) *
      ∫ t in (0 : ℝ)..2 * π, (exp (t * I) + z) / (exp (t * I) - z) * ((β t - t - π / 2 : ℝ) : ℂ)) :
    (∀ t, β (t + 2 * π) = β t + 2 * π) ∧
      ∀ t l : ℝ, Tendsto β (𝓝[<] t) (𝓝 l) →
        Tendsto (fun r : ℝ => (L (r * exp (t * I))).im) (𝓝[<] 1) (𝓝 ((β t + l) / 2 - t - π / 2)) := by
  sorry

/-- **Definition (3.5.17)** (§3.5; Paatero). The regulated domain `G` is of bounded boundary rotation: `β` has
bounded variation, `∫₀^{2π} |dβ(t)| < ∞`. -/
def IsBoundedBoundaryRotation (G : Set ℂ) : Prop :=
  ∃ (f : ℂ → ℂ) (F : ℂ → ExtPlane) (β : ℝ → ℝ), IsBoundarySetting f G F ∧ IsRegulatedFor F β ∧
    BoundedVariationOn β (Icc 0 (2 * π))

/-- The Riemann–Stieltjes integral `∫_a^b φ(t) dβ(t) = J` (helper, for Corollary 3.16, Theorem 3.18 and (3.6.1)):
the sums `Σ φ(ξ_k)(β(t_k) - β(t_{k-1}))` over tagged partitions `a = t₀ ≤ ⋯ ≤ tₙ = b`, `ξ_k ∈ [t_{k-1}, t_k]`,
converge to `J` as the mesh tends to `0`. -/
def HasRSIntegral (φ : ℝ → ℂ) (β : ℝ → ℝ) (a b : ℝ) (J : ℂ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (n : ℕ) (t : Fin (n + 1) → ℝ) (ξ : Fin n → ℝ), Monotone t → t 0 = a →
    t (Fin.last n) = b → (∀ k : Fin n, t k.succ - t k.castSucc < δ) →
    (∀ k : Fin n, ξ k ∈ Icc (t k.castSucc) (t k.succ)) →
    ‖∑ k : Fin n, φ (ξ k) * ((β (t k.succ) - β (t k.castSucc) : ℝ) : ℂ) - J‖ < ε

/-- **Corollary 3.16** (§3.5). If `f` maps `𝔻` conformally onto a domain `G` of bounded boundary rotation, then
(3.5.18) `log f'(z) = log f'(0) - (1/π) ∫₀^{2π} log(1 - e^{-it} z) dβ(t)` (`z ∈ 𝔻`), a Stieltjes integral, with the
branch `|arg(1 - e^{-it} z)| < π/2`.
Modelling: for any holomorphic logarithm `L` of `f'` (the difference `L(z) - L(0)` does not depend on the branch);
the branch of `log(1 - e^{-it} z)` is the principal one. -/
theorem cor3_16 {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {β : ℝ → ℝ}
    (hβ : IsRegulatedFor F β) (hbv : BoundedVariationOn β (Icc 0 (2 * π))) {L : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L unitDisc) (hLf : ∀ z ∈ unitDisc, exp (L z) = deriv f z) :
    ∀ z ∈ unitDisc, HasRSIntegral (fun t : ℝ => log (1 - exp (-(t * I)) * z)) β 0 (2 * π) (π * (L 0 - L z)) := by
  sorry

/-- **Formula (3.5.19)** (§3.5; cited in the proof of Corollary 3.17). Every function of bounded variation can be
written as `β = β_jump + β_sing + β_abs`, where `β_jump` is constant except for countably many jumps, `β_sing` is
continuous with `β_sing' = 0` almost everywhere, and `β_abs` is absolutely continuous.
Modelling: on a compact interval `[a, b]`; `β_jump` is a saltus function
`β_jump(t) = c + Σ_{s ∈ S, s < t} p(s) + Σ_{s ∈ S, s ≤ t} q(s)` over a countable set `S` with
`Σ_{s ∈ S} (|p(s)| + |q(s)|) < ∞`. -/
theorem eq3_5_19 {β : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hbv : BoundedVariationOn β (Icc a b)) :
    ∃ βj βs βa : ℝ → ℝ, (∀ t ∈ Icc a b, β t = βj t + βs t + βa t) ∧
      (∃ (S : Set ℝ) (p q : ℝ → ℝ) (c : ℝ), S.Countable ∧ S ⊆ Icc a b ∧
        Summable (fun s : S => |p s| + |q s|) ∧
        ∀ t ∈ Icc a b, βj t = c + ∑' s : S, ((if (s : ℝ) < t then p s else 0) + (if (s : ℝ) ≤ t then q s else 0))) ∧
      ContinuousOn βs (Icc a b) ∧ (∀ᵐ t, t ∈ Icc a b → HasDerivAt βs 0 t) ∧
      AbsolutelyContinuousOnInterval βa a b := by
  sorry

/-- **Corollary 3.17** (§3.5; the generalized Schwarz–Christoffel formula). If `β` is absolutely continuous except for
the jumps `πσ_k` at `t_k` (`k = 1, …, n`), then (3.5.20)
`f'(z) = f'(0) ∏_{k=1}^n (1 - e^{-it_k} z)^{-σ_k} exp(-(1/π) ∫₀^{2π} log(1 - e^{-it} z) β'(t) dt)`.
Modelling: under the hypotheses of Theorem 3.15; `β - Σ_k πσ_k 1_{[t_k, ∞)}` is absolutely continuous on `[0, 2π]`,
with `t_k ∈ (0, 2π]` (the jumps are right-continuous, `β(t+) = β(t)`); `β'` is `deriv β`, which exists almost
everywhere; the powers and logarithms are principal (`Re(1 - e^{-it} z) > 0`). -/
theorem cor3_17 {f : ℂ → ℂ} {G : Set ℂ} {F : ℂ → ExtPlane} (hS : IsBoundarySetting f G F) {β : ℝ → ℝ}
    (hβ : IsRegulatedFor F β) {n : ℕ} {t σ : Fin n → ℝ} (ht : ∀ k, t k ∈ Ioc 0 (2 * π))
    (hac : AbsolutelyContinuousOnInterval
      (fun s : ℝ => β s - ∑ k, π * σ k * (Ici (t k)).indicator (fun _ => (1 : ℝ)) s) 0 (2 * π)) :
    ∀ z ∈ unitDisc, deriv f z = deriv f 0 * (∏ k, (1 - exp (-(t k * I)) * z) ^ (-(σ k : ℂ))) *
      exp (-(1 / π) * ∫ s in (0 : ℝ)..2 * π, log (1 - exp (-(s * I)) * z) * ((deriv β s : ℝ) : ℂ)) := by
  sorry

end Pommerenke1992
