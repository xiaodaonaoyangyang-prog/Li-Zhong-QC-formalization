import References.Common.RiemannSurface
import References.Common.RiemannSurfaceHarmonic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Farkas–Kra, Chapter IV §1: More on harmonic functions (a quick review)

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. IV §1 (`full.md` FK1:7265–7452).

Conventions: a Riemann surface `M` has the binders `[TopologicalSpace M] [T2Space M] [ConnectedSpace M]`
`[ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]`. Harmonic functions on an open subset of a Riemann surface are the shared
`References.IsHarmonicRS U u` (mean-value property in the charts of the maximal atlas; on smooth functions it is
`Forster1981.IsHarmonicOn`). Harmonic functions on subsets of `ℂ` are written with Mathlib's
`InnerProductSpace.HarmonicOnNhd`. A *domain* is an open connected set. `δD` is `frontier D` and `Cl D` is `closure D`.

* IV.1.1 (Dirichlet problem, solution) — `IsDirichletSolution`
* IV.1.2 (Poisson kernel and its properties) — omitted: U−, the Poisson kernel formulas (1.2.1)–(1.2.6) are used only inside the proof of IV.1.3
* Theorem IV.1.3 — `thm4_1_3`
* Corollary IV.1.3 — `cor4_1_3`
* Harnack's inequality IV.1.4 — `thm4_1_4`
* Proposition IV.1.5 — `prop4_1_5`
* Harnack's principle IV.1.6 — `thm4_1_6`
* Theorem IV.1.7 — `thm4_1_7`
* Corollary IV.1.7, part 1 — `cor4_1_7_a`
* Corollary IV.1.7, part 2 — `cor4_1_7_b`
-/

open scoped Manifold ContDiff Topology Real
open Set Filter Metric

noncomputable section

namespace FarkasKra1992

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **Solution of the Dirichlet problem** (Ch. IV §1.1). Let `D` be a region on a Riemann surface `M` with boundary
`δD` and `f` a continuous function on `δD`. A *solution* is a continuous function `F` on `D ∪ δD = Cl D` such that
(i) `F | D` is harmonic and (ii) `F | δD = f`. Modelling: `f` is a function on `M` of which only the values on `δD`
count; `D` is open. -/
def IsDirichletSolution (D : Set M) (f F : M → ℝ) : Prop :=
  ContinuousOn F (closure D) ∧ References.IsHarmonicRS D F ∧ ∀ P ∈ frontier D, F P = f P

/-- **Theorem IV.1.3** (Ch. IV §1.3). The Dirichlet problem for the disc has a unique solution: given a continuous
function `f` on `{|z| = r}` there exists a continuous function `F` on `{|z| ≤ r}`, harmonic in `{|z| < r}`, with
`F = f` on `{|z| = r}`, and `F` is unique. -/
theorem thm4_1_3 {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ} (hf : ContinuousOn f (sphere 0 r)) :
    (∃ F : ℂ → ℝ, ContinuousOn F (closedBall 0 r) ∧ InnerProductSpace.HarmonicOnNhd F (ball 0 r) ∧
      EqOn F f (sphere 0 r)) ∧
    ∀ F₁ F₂ : ℂ → ℝ, ContinuousOn F₁ (closedBall 0 r) → InnerProductSpace.HarmonicOnNhd F₁ (ball 0 r) →
      EqOn F₁ f (sphere 0 r) → ContinuousOn F₂ (closedBall 0 r) →
      InnerProductSpace.HarmonicOnNhd F₂ (ball 0 r) → EqOn F₂ f (sphere 0 r) → EqOn F₁ F₂ (closedBall 0 r) := by
  sorry

/-- **Corollary IV.1.3** (Ch. IV §1.3). If `f` is a continuous function on a domain `D ⊂ ℂ`, and `f` satisfies the
mean-value property in `D` (`f(c)` is the circle average over every circle with closed disc in `D`), then `f` is
harmonic in `D`. -/
theorem cor4_1_3 {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {f : ℂ → ℝ} (hf : ContinuousOn f D)
    (hmv : ∀ (c : ℂ) (r : ℝ), 0 < r → closedBall c r ⊆ D → Real.circleAverage f c r = f c) :
    InnerProductSpace.HarmonicOnNhd f D := by
  sorry

/-- **Harnack's inequality** (Ch. IV §1.4). Let `D` be a domain in `ℂ` and `D₁ ⊂⊂ D` (a relatively compact
subdomain). There is a constant `c = c(D₁, D)`, depending only on `D₁` and `D` (not on `u`), such that every positive
harmonic function `u` on `D` satisfies `1/c ≤ u(z₁)/u(z₂) ≤ c` for all `z₁, z₂ ∈ D₁`. -/
theorem thm4_1_4 {D D₁ : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) (hD₁ : IsOpen D₁) (hD₁c : IsConnected D₁)
    (hcpt : IsCompact (closure D₁)) (hsub : closure D₁ ⊆ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u D → (∀ z ∈ D, 0 < u z) →
      ∀ z₁ ∈ D₁, ∀ z₂ ∈ D₁, 1 / c ≤ u z₁ / u z₂ ∧ u z₁ / u z₂ ≤ c := by
  sorry

/-- **Proposition IV.1.5** (Ch. IV §1.5). If `{u_n}` is a sequence of harmonic functions on a Riemann surface `M`
converging to `u` uniformly on compact subsets of `M`, then `u` is also harmonic. -/
theorem prop4_1_5 {u : ℕ → M → ℝ} {v : M → ℝ} (hu : ∀ n, References.IsHarmonicRS univ (u n))
    (hconv : TendstoLocallyUniformly u v atTop) : References.IsHarmonicRS univ v := by
  sorry

/-- **Harnack's principle** (Ch. IV §1.6). Consider a sequence of real valued harmonic functions `u_n`, each defined on
a domain `D_n` of the Riemann surface `M`. Assume that each `P₀ ∈ M` has a neighbourhood `U` such that `U ⊂ D_n` for all
but finitely many `n`, and `u_n(P) ≤ u_{n+1}(P)` for `P ∈ U`, `n` large. Then either (i) `lim u_n = +∞` uniformly on
compact subsets of `M`, or (ii) `lim u_n = u` uniformly on compact subsets of `M`, with `u` a harmonic function.
Modelling: `u_n` is a function on `M` of which only the values on `D_n` count (locally, `U ⊂ D_n` for large `n`). -/
theorem thm4_1_6 {D : ℕ → Set M} {u : ℕ → M → ℝ} (hD : ∀ n, IsOpen (D n) ∧ IsConnected (D n))
    (hu : ∀ n, References.IsHarmonicRS (D n) (u n))
    (hloc : ∀ P : M, ∃ U ∈ 𝓝 P, (∀ᶠ n in atTop, U ⊆ D n) ∧ ∀ᶠ n in atTop, ∀ x ∈ U, u n x ≤ u (n + 1) x) :
    (∀ K : Set M, IsCompact K → ∀ B : ℝ, ∀ᶠ n in atTop, ∀ x ∈ K, B < u n x) ∨
      ∃ v : M → ℝ, TendstoLocallyUniformly u v atTop ∧ References.IsHarmonicRS univ v := by
  sorry

/-- **Theorem IV.1.7** (Ch. IV §1.7). Let `u` be a harmonic function on `{0 < |z| < 1}`. Then there exist constants
`α, β` such that for `0 < r < 1`, `∫₀^{2π} u(re^{iθ}) dθ = α log r + β`. -/
theorem thm4_1_7 {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1 \ {0})) :
    ∃ α β : ℝ, ∀ r : ℝ, 0 < r → r < 1 →
      ∫ θ in (0 : ℝ)..2 * π, u (r * Complex.exp (θ * Complex.I)) = α * Real.log r + β := by
  sorry

/-- **Corollary IV.1.7, part 1** (Ch. IV §1.7, Corollary 1). If `u` is harmonic and bounded in `{0 < |z| < 1}`, then
`α = 0`: the circle integral `∫₀^{2π} u(re^{iθ}) dθ` is independent of `r`. -/
theorem cor4_1_7_a {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1 \ {0}))
    (hb : ∃ B : ℝ, ∀ z ∈ ball (0 : ℂ) 1 \ {0}, |u z| ≤ B) :
    ∃ β : ℝ, ∀ r : ℝ, 0 < r → r < 1 → ∫ θ in (0 : ℝ)..2 * π, u (r * Complex.exp (θ * Complex.I)) = β := by
  sorry

/-- **Corollary IV.1.7, part 2** (Ch. IV §1.7, Corollary 2). If `u` is harmonic and bounded in `{0 < |z| < 1}`, then
`u` can be extended as a harmonic function to `{|z| < 1}`. -/
theorem cor4_1_7_b {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u (ball 0 1 \ {0}))
    (hb : ∃ B : ℝ, ∀ z ∈ ball (0 : ℂ) 1 \ {0}, |u z| ≤ B) :
    ∃ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (ball 0 1) ∧ EqOn v u (ball 0 1 \ {0}) := by
  sorry

end FarkasKra1992
