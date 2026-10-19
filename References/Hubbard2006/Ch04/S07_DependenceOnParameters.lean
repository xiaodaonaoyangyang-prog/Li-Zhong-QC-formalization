import References.Common.HyperbolicSurface
import References.Hubbard2006.Ch04.S02_SobolevSpaces

/-!
# Hubbard 2006, Chapter 4 §4.7: Dependence on parameters (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 4372–4515.

**Conventions.** Beltrami coefficients are functions `μ : ℂ → ℂ`, bounded by `k < 1` almost everywhere. A solution of
the
Beltrami equation `∂f/∂z̄ = μ ∂f/∂z` is a homeomorphism `f : ℂ → ℂ` with distributional partials in `L²_loc`
(`Hubbard2006.IsH1With`, Chapter 4 §4.2) satisfying the equation almost everywhere.

* Notation 4.7.1 (the solution `w^μ` normalized by `w^μ(z) = z + O(1/|z|)` at `∞`; `μ` of compact support) — `IsWMu`
* Prop. 4.7.2 (`L¹` convergence of Beltrami coefficients bounded by `k < 1` gives uniform convergence of the
  normalized solutions) — `prop4_7_2`
* Def. 4.7.3 (the space `QC(U, V)` of quasiconformal maps with the topology of uniform convergence on compact sets, and
  its subsets `QC_K(U, V)`) — `QCSet`, `QCSetK`
* Thm 4.7.4 (`μ ↦ w^μ` is analytic on the unit ball of `L^∞` of functions supported in a compact set) —
  `ballSupp`, `thm4_7_4`
* Notation 4.7.5 (the solution `f^μ` normalized by `f^μ(0) = 0`, `f^μ(1) = 1`, `f^μ(∞) = ∞`) — exists:
  `LiZhongQC.IsNormalizedSolution`
* Prop. 4.7.6 (`μ ↦ f^μ` is analytic on the unit ball of `L^∞(ℂ)`) — `ballLinf`, `prop4_7_6`
* Equations 4.7.2–4.7.13 (Fourier transform and the operator `ℒ` in the proof of Thm 4.7.4) — omitted: proof step
-/

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace Hubbard2006

open LiZhongQC

/-- **The normalized solution `w^μ`** (Notation 4.7.1, H1:4390): `w` is a homeomorphism of `ℂ`, has distributional
partials `(g, h)` locally in `L²` that solve the Beltrami equation `∂w/∂z̄ = μ ∂w/∂z` almost everywhere, and
`w(z) = z + O(1/|z|)` at infinity. *Reading:* Hubbard assumes `μ` has compact support; the predicate is stated
for any `μ`, and the statements below assume compact support. This normalization differs from the one of
`LiZhongQC.IsNormalizedSolution` (fixing `0`, `1`, `∞`). -/
def IsWMu (w μ : ℂ → ℂ) : Prop :=
  IsHomeomorphOnto w univ univ ∧
    (∃ g h : ℂ → ℂ, IsH1With w g h univ ∧ ∀ᵐ z, genDzbar g h z = μ z * genDz g h z) ∧
    ∃ C R : ℝ, ∀ z : ℂ, R < ‖z‖ → ‖w z - z‖ ≤ C / ‖z‖

/-- **Proposition 4.7.2** (H1:4396). Let `U ⊂ ℂ` be compact and `μₙ`, `μ` Beltrami coefficients supported in `U` with
`‖μₙ‖_∞ ≤ k < 1` and `‖μₙ − μ‖_{L¹} → 0`. Then the normalized solutions `w^{μₙ}` converge to `w^μ` uniformly on `ℂ`. -/
theorem prop4_7_2 {U : Set ℂ} (hU : IsCompact U) {μ : ℕ → ℂ → ℂ} {ν : ℂ → ℂ} {k : ℝ} (hk : k < 1)
    (hbound : ∀ n, ∀ᵐ z, ‖μ n z‖ ≤ k) (hsupp : ∀ n, ∀ᵐ z, z ∉ U → μ n z = 0) (hνsupp : ∀ᵐ z, z ∉ U → ν z = 0)
    (hconv : Tendsto (fun n => eLpNorm (fun z => μ n z - ν z) 1 volume) atTop (𝓝 0))
    {w : ℕ → ℂ → ℂ} {wν : ℂ → ℂ} (hw : ∀ n, IsWMu (w n) (μ n)) (hwν : IsWMu wν ν) :
    TendstoUniformly w wν atTop := by
  sorry

/-- **The space `QC(U, V)`** (Definition 4.7.3, H1:4410): the quasiconformal maps from `U` onto `V`, as a subset of
the space `C(U, ℂ)` of continuous maps with the compact-open topology (= uniform convergence on compact sets). -/
def QCSet (U V : Set ℂ) : Set C(↥U, ℂ) :=
  {F | ∃ f : ℂ → ℂ, IsQuasiconformal f U ∧ f '' U = V ∧ ∀ z : U, F z = f z}

/-- **The subset `QC_K(U, V)`** of `K`-quasiconformal maps (Definition 4.7.3). -/
def QCSetK (U V : Set ℂ) (K : ℝ) : Set C(↥U, ℂ) :=
  {F | ∃ f : ℂ → ℂ, IsKQC f U K ∧ f '' U = V ∧ ∀ z : U, F z = f z}

/-- **The unit ball of Beltrami coefficients supported in `U`** (Theorem 4.7.4, H1:4412): the elements `μ` of
`L^∞(ℂ)` with `‖μ‖ < 1` that vanish almost everywhere outside `U`. -/
def ballSupp (U : Set ℂ) : Set (Lp ℂ ∞ (volume : Measure ℂ)) :=
  {μ | ‖μ‖ < 1 ∧ ∀ᵐ z, z ∉ U → μ z = 0}

/-- **Theorem 4.7.4** (H1:4412). Let `U ⊂ ℂ` be compact. The map `μ ↦ w^μ` from `B_U(ℂ)` (`ballSupp U`, with the
norm topology of `L^∞`) to `QC(ℂ, ℂ)` is analytic: it is continuous, and for each `z ∈ ℂ` the map `μ ↦ w^μ(z)` is
analytic (the restriction to `B_U` of a function analytic within `B_U`). Here `W` is the assignment `μ ↦ w^μ`, which
exists and is unique by Theorem 4.6.1. -/
theorem thm4_7_4 {U : Set ℂ} (hU : IsCompact U) (W : ballSupp U → C(ℂ, ℂ))
    (hW : ∀ μ : ballSupp U, IsWMu (W μ) (μ.1 : ℂ → ℂ)) :
    Continuous W ∧ ∀ z : ℂ, ∃ F : Lp ℂ ∞ (volume : Measure ℂ) → ℂ,
      AnalyticOn ℂ F (ballSupp U) ∧ ∀ μ : ballSupp U, F μ.1 = W μ z := by
  sorry

/-- **The open unit ball of `L^∞(ℂ)`** (Proposition 4.7.6): the Beltrami coefficients `μ` with `‖μ‖_∞ < 1`. -/
def ballLinf : Set (Lp ℂ ∞ (volume : Measure ℂ)) := {μ | ‖μ‖ < 1}

/-- **Proposition 4.7.6** (H1:4504). The map `μ ↦ f^μ` from the unit ball of `L^∞(ℂ)` to `QC(ℂ, ℂ)` is analytic: it
is continuous, and for each `z ∈ ℂ` the map `μ ↦ f^μ(z)` is analytic on the (open) ball. Here `W` is the assignment
`μ ↦ f^μ` of normalized solutions (`LiZhongQC.IsNormalizedSolution`, which exist and are unique by Theorem 4.6.1; the
installed `LiZhongQC.thm13_8_ahlfors_bers_holomorphic` is the holomorphic dependence on a finite-dimensional
parameter, a near miss). -/
theorem prop4_7_6 (W : ballLinf → C(ℂ, ℂ)) (hW : ∀ μ : ballLinf, IsNormalizedSolution (W μ) (μ.1 : ℂ → ℂ)) :
    Continuous W ∧ ∀ z : ℂ, ∃ F : Lp ℂ ∞ (volume : Measure ℂ) → ℂ,
      AnalyticOnNhd ℂ F ballLinf ∧ ∀ μ : ballLinf, F μ.1 = W μ z := by
  sorry

end Hubbard2006
