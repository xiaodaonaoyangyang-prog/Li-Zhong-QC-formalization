import References.GardinerLakic2000.Ch14.S10_ExtremalityInAT

/-!
# Gardiner–Lakic 2000, Ch. 14 §14.11 Teichmüller's metric on `AT`

Source `teichmuller.txt`, lines 11114–11228.

* Definition (`d` on `AT`, l. 11117–11127) — exists: `GardinerLakic2000.asymDist` (defined in §14.10)
* Theorem 10 ((14.33), [EGL98a], l. 11131) — `thm14_10`
* Definition (`F(μ, ν)`, l. 11183) — `asymInfNorm`
* Definition (piecewise smooth paths of Beltrami coefficients, `L(γ)`, `d̃`, l. 11178–11182) —
  `IsPiecewiseC1BeltramiPath`
* Theorem 11 ([EGL98a], l. 11176) — `thm14_11`

Not items (DESIGN §3): the exercises (l. 11203–11227).

**Modelling (calibration D0.10).** Theorem 10: `d([0], [t μ]) = |t| β(μ) + o(t)` with `o(t)` depending only on `‖μ‖∞`
is stated as `∀ M ε ∃ δ` over the `μ` with `‖μ‖∞ ≤ M` [reading]. `F(μ, ν)` is the book's first formula, read as the
upper Dini quotient `limsup_{t → 0+} d([μ], [μ + tν])/t`; its value as a supremum over degenerating sequences
(l. 11184) is not stated. A piecewise `C¹` path is a path `γ` in `M(R)` over `[0, 1]` with a subdivision on whose
closed pieces `γ` is differentiable in `L∞` (one-sided at the ends) with a continuous derivative `Dᵢ`; the given `γ′`
equals `Dᵢ` inside the pieces. `L(γ) = ∫₀¹ F(γ(t), γ′(t)) dt`, and `d̃(p, q)` is the infimum of `L(γ)` over the paths
from `p` to `q`; Theorem 11 is `d = d̃`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsFuchsian IsUniformization)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

open Classical in
/-- **Definition** (`F(μ, ν)`, §14.11, l. 11183; D0.10). `F(μ, ν) = limsup_{t → 0+} d([μ], [μ + tν])/t`. -/
def asymInfNorm (p : UpperHalfPlane → R) (μ ν : R → ℂ → ℂ) : ℝ≥0∞ :=
  limsup (fun t : ℝ => if h : μ ∈ beltramiBall R ∧ (fun x z => μ x z + t * ν x z) ∈ beltramiBall R then
      ENNReal.ofReal (asymDist p (Quot.mk (asymRel p) ⟨μ, h.1⟩) (Quot.mk (asymRel p) ⟨_, h.2⟩) / t)
    else 0) (𝓝[>] 0)

/-- **Definition** (§14.11, l. 11178; D0.10). `γ` is a piecewise `C¹` path in `M(R)` over `[0, 1]` with derivative
`γ′` (in `L∞`) inside the pieces of a subdivision. -/
def IsPiecewiseC1BeltramiPath (γ γ' : ℝ → R → ℂ → ℂ) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ beltramiBall R) ∧
    ∃ (m : ℕ) (τ : Fin (m + 1) → ℝ) (D : Fin m → ℝ → R → ℂ → ℂ), τ 0 = 0 ∧ τ (Fin.last m) = 1 ∧ StrictMono τ ∧
      ∀ i : Fin m, (∀ t ∈ Ioo (τ i.castSucc) (τ i.succ), γ' t = D i t) ∧
        ∀ t ∈ Icc (τ i.castSucc) (τ i.succ), D i t ∈ beltramiSpace R ∧
          Tendsto (fun s => beltramiNormRS fun x z => (γ s x z - γ t x z) / (s - t) - D i t x z)
            (𝓝[Icc (τ i.castSucc) (τ i.succ) \ {t}] t) (𝓝 0) ∧
          Tendsto (fun s => beltramiNormRS fun x z => D i s x z - D i t x z)
            (𝓝[Icc (τ i.castSucc) (τ i.succ)] t) (𝓝 0)

variable [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R]

/-- **Theorem 10** ((14.33), §14.11, l. 11131; [EGL98a]). The infinitesimal form of `d` on `AT` at the identity is the
`β`-norm: `d([0], [t μ]) = |t| β(μ) + o(t)`, the `o(t)` depending only on `‖μ‖∞`. -/
theorem thm14_10 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (h0 : (0 : R → ℂ → ℂ) ∈ beltramiBall R) (M : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ μ ∈ beltramiSpace R, beltramiNormRS μ ≤ ENNReal.ofReal M → ∀ t : ℝ, |t| < δ →
      ∀ h : (fun x z => (t : ℂ) * μ x z) ∈ beltramiBall R,
        |asymDist p (Quot.mk (asymRel p) ⟨0, h0⟩) (Quot.mk (asymRel p) ⟨_, h⟩) - |t| * betaOf μ| ≤ ε * |t| := by
  sorry

/-- **Theorem 11** (§14.11, l. 11176; [EGL98a]). The Teichmüller metric `d` on `AT` is the integral of its
infinitesimal form: `d(p, q) = inf L(γ)` over the piecewise `C¹` paths of Beltrami coefficients from `p` to `q`. -/
theorem thm14_11 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (P Q : AsymTeichSpace R p) :
    asymDist p P Q = sInf {L | ∃ γ γ' : ℝ → R → ℂ → ℂ, IsPiecewiseC1BeltramiPath γ γ' ∧
      ∃ (h₀ : γ 0 ∈ beltramiBall R) (h₁ : γ 1 ∈ beltramiBall R), Quot.mk (asymRel p) ⟨γ 0, h₀⟩ = P ∧
        Quot.mk (asymRel p) ⟨γ 1, h₁⟩ = Q ∧ L = ∫ t in (0 : ℝ)..1, (asymInfNorm p (γ t) (γ' t)).toReal} := by
  sorry

end GardinerLakic2000
