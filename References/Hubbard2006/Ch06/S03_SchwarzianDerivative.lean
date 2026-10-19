import References.Common.HyperbolicSurface
import References.Hubbard2006.Ch05.S04_QuadraticDifferentials

/-!
# Hubbard 2006, Chapter 6 §6.3: The Schwarzian derivative (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 2007–2316.

**Conventions.** Maps between open sets of `ℂ` are written in the standard coordinate, and the quadratic differential
`S{f, g} = s(z) dz²` is recorded by its coefficient `s`. In Definition 6.3.2 the symbol `D³(f − A ∘ g)(z)` is the cubic
Taylor coefficient (so that `6 D³ = ` the third derivative), which is what gives the classical value (6.3.6) in
Proposition 6.3.3: `S{f, g}(z) = (f − A ∘ g)'''(z) / f'(z)`, `A` the Möbius transformation with the same value,
first and
second derivative as `f` at `z` (`IsBestMobius`, chosen by `Classical.epsilon`, unique when `f'(z) g'(z) ≠ 0`). The
classical Schwarzian derivative of the project is `LiZhongQC.schwarzian` (meromorphic functions), `schwarzianHol`
(holomorphic germs). `ρ_U` denotes the hyperbolic density (curvature `−1`) of a round disc: `2 r / (r² − |z − c|²)` on
`D(c, r)` and `1 / Im z` on `ℍ`; `‖q‖_∞ = sup |q| / ρ²`.

* Def. 6.3.2 (the Schwarzian derivative `S{f, g}` through the best Möbius approximation) — `IsBestMobius`, `schwarzDiff`
* Prop. 6.3.3 (computing the Schwarzian derivative: `S{f, z} = f'''/f' − (3/2)(f''/f')²`) — `prop6_3_3`
* Prop. 6.3.4 (1) (`S{f, g} = −S{g, f}`) — `prop6_3_4_a`
* Prop. 6.3.4 (2) (`S{f, g} = 0` if and only if `f = α ∘ g`) — `prop6_3_4_b`
* Prop. 6.3.4 (3) (`S{f, g} = S{α ∘ f, g} = S{f, α ∘ g}`) — `prop6_3_4_c`
* Prop. 6.3.7 (global solution of the Schwarzian equation `S{f, z} = q` on a simply connected open set) —
  `prop6_3_7`
* Thm 6.3.9 (Nehari's theorem for a round disc and for a half plane: `‖S{f, z}‖_∞ ≤ 3/2` for injective analytic
  `f`) — `thm6_3_9_a`, `thm6_3_9_b`
* Thm 6.3.10 (Ahlfors–Weill: `S{f^{μ_q}|_{ℍ*}, z} = q` for `‖q‖_∞ < 1/2`, with `μ_q = −2 y² q(z̄)`) — `ahlforsWeillCoeff`,
  `thm6_3_10`
* Examples 6.3.1, 6.3.6, 6.3.8, Exercise 6.3.5, 6.3.11, Lemma 6.3.12 (the diffeomorphism property in the proof of
  Thm 6.3.10) — omitted: example / exercise / proof step
-/

open Set Metric Filter
open scoped Real

namespace Hubbard2006

open LiZhongQC

/-- **`A` is a best Möbius approximation of `f` along `g` at `z`** (Definition 6.3.2, H2:2047): `A` is a Möbius
transformation such that `A ∘ g` has the same value, first and second derivative at `z` as `f`. -/
def IsBestMobius (f g : ℂ → ℂ) (z : ℂ) (A : ℂ → ℂ) : Prop :=
  IsMobiusOn A univ ∧ A (g z) = f z ∧ deriv (A ∘ g) z = deriv f z ∧
    deriv (deriv (A ∘ g)) z = deriv (deriv f) z

/-- **The Schwarzian derivative `S{f, g}`** (Definition 6.3.2, H2:2047, equation (6.3.5)) of two maps with non-vanishing
derivative at `z`: the coefficient of `dz²` in `(Df)⁻¹ ∘ D³(f − A ∘ g)`, `A` the best Möbius approximation of `f` along
`g` at `z` (see the module docstring for the normalization of `D³`). -/
noncomputable def schwarzDiff (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (deriv f z)⁻¹ * iteratedDeriv 3 (fun w => f w - Classical.epsilon (IsBestMobius f g z) (g w)) z

/-- **Proposition 6.3.3** (H2:2055). If `f` is analytic near `z` with `f'(z) ≠ 0` and `g(z) = z`, then
`S{f, z} = f'''/f' − (3/2)(f''/f')²`, i.e. the classical Schwarzian derivative `LiZhongQC.schwarzianHol`. -/
theorem prop6_3_3 {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hf' : deriv f z ≠ 0) :
    schwarzDiff f id z = schwarzianHol f z := by
  sorry

/-- **Proposition 6.3.4 (1)** (Properties of the Schwarzian derivative, H2:2093). `S{f, g} = −S{g, f}` for analytic
maps with non-vanishing derivative at `z`. -/
theorem prop6_3_4_a {f g : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z) (hf' : deriv f z ≠ 0)
    (hg' : deriv g z ≠ 0) : schwarzDiff f g z = -schwarzDiff g f z := by
  sorry

/-- **Proposition 6.3.4 (2)** (H2:2093). On a connected open set `U`, for analytic `f`, `g` with non-vanishing
derivatives, `S{f, g} = 0` on `U` if and only if `f = α ∘ g` on `U` for a Möbius transformation `α`. -/
theorem prop6_3_4_b {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U) {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (hf' : ∀ z ∈ U, deriv f z ≠ 0) (hg' : ∀ z ∈ U, deriv g z ≠ 0) :
    (∀ z ∈ U, schwarzDiff f g z = 0) ↔ ∃ α : ℂ → ℂ, IsMobiusOn α univ ∧ EqOn f (α ∘ g) U := by
  sorry

/-- **Proposition 6.3.4 (3)** (H2:2093). For a Möbius transformation `α`, `S{f, g} = S{α ∘ f, g} = S{f, α ∘ g}`
(at points where `α ∘ f`, `α ∘ g` are analytic with non-vanishing derivative). -/
theorem prop6_3_4_c {f g α : ℂ → ℂ} {z : ℂ} (hα : IsMobiusOn α univ) (hf : AnalyticAt ℂ f z)
    (hg : AnalyticAt ℂ g z) (hf' : deriv f z ≠ 0) (hg' : deriv g z ≠ 0) (hαf : AnalyticAt ℂ (α ∘ f) z)
    (hαg : AnalyticAt ℂ (α ∘ g) z) (hαf' : deriv (α ∘ f) z ≠ 0) (hαg' : deriv (α ∘ g) z ≠ 0) :
    schwarzDiff f g z = schwarzDiff (α ∘ f) g z ∧ schwarzDiff f g z = schwarzDiff f (α ∘ g) z := by
  sorry

/-- **Proposition 6.3.7 (Global solution for the Schwarzian differential equation)** (H2:2123). Let `U ⊂ ℂ` be a simply
connected open set, `q` a holomorphic quadratic differential on `U`, `z₀ ∈ U` and `a₀, a₁, a₂ ∈ ℂ` with `a₁ ≠ 0`.
There is a unique (up to a discrete set of poles, where the value is not meaningful) solution `f` of `S{f, z} = q` that
is meromorphic in `U` and satisfies `f(z₀) = a₀`, `f'(z₀) = a₁`, `f''(z₀) = a₂`. -/
theorem prop6_3_7 {U : Set ℂ} (hU : IsOpen U) (hUs : IsSimplyConnected U) {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) {a₀ a₁ a₂ : ℂ} (ha₁ : a₁ ≠ 0) :
    ∃ f : ℂ → ℂ, (MeromorphicOn f U ∧ (∀ z ∈ U, schwarzian f z = q z) ∧ f z₀ = a₀ ∧ deriv f z₀ = a₁ ∧
        deriv (deriv f) z₀ = a₂) ∧
      ∀ g : ℂ → ℂ, MeromorphicOn g U → (∀ z ∈ U, schwarzian g z = q z) → g z₀ = a₀ → deriv g z₀ = a₁ →
        deriv (deriv g) z₀ = a₂ → f =ᶠ[codiscreteWithin U] g := by
  sorry

/-- **Theorem 6.3.9 (Nehari), round disc** (H2:2165). Let `U = D(c, r)` be a round disc with hyperbolic density
`ρ_U = 2 r / (r² − |z − c|²)` and `f : U → ℂ` an injective analytic map. Then `‖S{f, z}‖_∞ ≤ 3/2`, i.e.
`|S{f, z}| / ρ_U(z)² ≤ 3/2` on `U`. -/
theorem thm6_3_9_a {c : ℂ} {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c r))
    (hinj : InjOn f (ball c r)) {z : ℂ} (hz : z ∈ ball c r) :
    ‖schwarzian f z‖ / (2 * r / (r ^ 2 - ‖z - c‖ ^ 2)) ^ 2 ≤ 3 / 2 := by
  sorry

/-- **Theorem 6.3.9 (Nehari), half plane** (H2:2165). For `f : ℍ → ℂ` injective analytic, with `ρ_ℍ = 1 / Im z`,
`|S{f, z}| (Im z)² ≤ 3/2`. -/
theorem thm6_3_9_b {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalf) (hinj : InjOn f upperHalf) {z : ℂ}
    (hz : z ∈ upperHalf) : ‖schwarzian f z‖ * z.im ^ 2 ≤ 3 / 2 := by
  sorry

/-- **The Beltrami coefficient `μ_q` of the Ahlfors–Weill construction** (equation (6.3.24), H2:2203): for a quadratic
differential `q` on `ℍ*`, `μ_q(z) = −2 y² q(z̄)` for `z ∈ ℍ` and `0` on `ℍ*`. *Correction to the book:* (6.3.24) prints
`+2 y² q(z̄)`; with the extension (6.3.25) of the book (`w''+ (q/2) w = 0`) one finds `∂̄f/∂f = (z − z̄)² q(z̄)/2 = −2 y² q(z̄)`,
and with `+2 y² q(z̄)` one would get `S{f, z} = −q`. The sign `−` is that of `LiZhongQC.lemma33_3`. -/
noncomputable def ahlforsWeillCoeff (q : ℂ → ℂ) (z : ℂ) : ℂ :=
  if 0 < z.im then -2 * (z.im : ℂ) ^ 2 * q ((starRingEnd ℂ) z) else 0

/-- **Theorem 6.3.10 (Ahlfors–Weill)** (H2:2211). Let `q ∈ Q^∞(ℍ*)` (holomorphic on the lower half plane) with
`‖q‖_∞ < 1/2`. Then `‖μ_q‖_∞ < 1`, and the normalized solution `f^{μ_q}` (`f(0) = 0`, `f(1) = 1`, `f(∞) = ∞`,
`LiZhongQC.IsNormalizedSolution`) is injective analytic on `ℍ*` with Schwarzian derivative
`S{f^{μ_q}|_{ℍ*}, z} = q(z)`. (Near miss: `LiZhongQC.lemma33_3`, the `Γ`-automorphic case, stated through the Bers
map.) -/
theorem thm6_3_10 {q : ℂ → ℂ} (hq : DifferentiableOn ℂ q lowerHalf)
    (hsup : qdSupNorm lowerHalf q < ENNReal.ofReal (1 / 2))
    {f : ℂ → ℂ} (hf : IsNormalizedSolution f (ahlforsWeillCoeff q)) :
    DifferentiableOn ℂ f lowerHalf ∧ InjOn f lowerHalf ∧ ∀ z ∈ lowerHalf, schwarzian f z = q z := by
  sorry

end Hubbard2006
