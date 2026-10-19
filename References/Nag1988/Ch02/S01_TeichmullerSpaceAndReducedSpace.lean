import References.Nag1988.Ch05.S02_UniversalFamily
import References.Lehto1987.Ch05.S03_TeichmullerSpaceAndLiftedMappings
import References.GardinerLakic2000.Ch02.S09_FundamentalDomains

/-!
# Nag, Chapter 2 §2.1: Teichmüller space and reduced Teichmüller space

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 2 §2.1 (`full.md`
N1:3143–3415, folder `The Complex Analytic Theory … 10dae1e9`; cited `N1:<line>`). New items only: the items of §2.1 that
the project already states are passed with `exists:`; §2.2.4 identifies the reduced space with the space of the
homomorphisms `E_μ`, which is the model used here.

**Model (group version).** As in Chapter 5 (N-D1): `X = ℍ/Γ`, `Γ` a Fuchsian group in `SL(2, ℝ)`, `M(X)` is the unit ball
`LiZhongQC.BeltramiGamma Γ`, and `T(X)` is `LiZhongQC.TeichGamma Γ` (the quotient by `w^μ|ℝ = w^ν|ℝ`, i.e. Teichmüller
equivalence; Nag Theorem 2.2.6 identifies it with the surface version). A marked surface `(X, f, X₁)` is represented by the
Beltrami coefficient `μ` of a lift of `f`; `w^μ` is `LiZhongQC.fMuSym μ` (the normalized solution of the symmetric extension of
`μ`). **Reduced and Riemann equivalence** (N1:3166, 3187; Nag 2.2.4, 2.5.7): the homomorphism
`E_μ : Γ → Möb(ℝ)`, `E_μ(γ) = w^μ γ (w^μ)⁻¹`, is `IsDeformedBy μ γ A`; `μ ∼_# ν` iff `E_ν = α E_μ α⁻¹` for one real Möbius
map `α` (weak Teichmüller equivalence is the free homotopy of the identification to the identity: it fixes the isomorphism
`π₁(X) → π₁(X₁)` up to conjugation; `α` is the conformal map `σ` of the book, and is not `1` in general because `w^μ` is
normalized at `0, 1, ∞`, which need not lie in `Λ(Γ)` for a group of the second kind), and `μ ∼_R ν` iff the groups `E_μ(Γ)`,
`E_ν(Γ)` are conjugate in `Möb(ℝ)`. [CORRECTION of the first reading `E_μ = E_ν`, which is `∼_#` only for groups normalized
with `0, 1, ∞ ∈ Λ(Γ)` and made `prop2_4_1_reduced` false for a group of the second kind.] This agrees with the
surface definitions (a biholomorphism `σ : X₁ → X₂` is a conjugation of the uniformizing groups). The distance `τ̂` on `M(X)`
is `betaDist` (`½ log K` of the pair, `K = (1 + k)/(1 - k)`, `k = ‖(μ - ν)/(1 - ν̄μ)‖_∞`).

**Normalization conversions.** Nag works on `U` (upper half-plane) with `μ` on `U` and `0` on `L`, `w^μ` normalized by `0, 1, ∞`;
`LiZhongQC.BeltramiGamma` and `fMuSym` are the same objects (dilatation on `ℍ`, reflection to the lower half-plane).

* Definition (marked Riemann surfaces `M̂(X)`, Teichmüller equivalence `∼`, `T(X)`; N1:3150–3165) — exists:
  `LiZhongQC.TeichGamma`, `LiZhongQC.teichSetoidGamma`
* Definition (weak equivalence `∼_#`, `T^#(X)`, Riemann equivalence `∼_R`, `R(X)`; N1:3166–3199) — `IsDeformedBy`,
  `reducedSetoidGamma`, `ReducedTeichGamma`, `riemannRel`, `RiemannSpaceGamma`
* Unlabelled (the natural projections `T(X) → T^#(X) → R(X)`, N1:3191–3199) — `para2_1_1_projections`
* Unlabelled (for `∂(X) = ∅`, i.e. `Γ` of the first kind, `T(X) = T^#(X)`; N1:3181) — `para2_1_1_firstKind`
* Definition (the function `τ̂` on `M̂(X)` and the metric on `M(X)`; N1:3201–3222) — `betaDist` (the Teichmüller distance
  teichDistanceGamma of the project is the quotient pseudometric of `betaDist`)
* Lemma 2.1.3 (the projection `M̂(X) → T(X)` factors through `M(X)`; N1:3201) — omitted: definitional in the group model (`M(X)`
  is BeltramiGamma, `T(X)` its quotient; the equivalence of TeichGamma with the marked-surface version is
  teichGamma_equiv_teichSpace of the project)
* Lemma 2.1.4 (`M(X)` is the unit ball of `L^∞_{(-1,1)}(X)` with `τ̂` the Teichmüller distance; N1:3217) — omitted: definitional in the
  group model, as for Lemma 2.1.3
* Definition (quotient pseudometric `d_Φ`; N1:3240) — `quotientDist` (the exercise that `d_Φ` is a pseudometric with the
  quotient topology is omitted: exercise)
* Lemma 2.1.6 (completeness of the quotient pseudometric; N1:3252) — `lemma2_1_6` [CORRECTION: the book's general claim
  is false for an arbitrary surjection; the hypothesis that every point is equally close to every fibre is added]
* Proposition 2.1.7 (`(T(X), τ)` is a complete connected metric space) — exists: `Lehto1987.thm5_3_2` (complete),
  `Lehto1987.thm5_2_2` (path connected)
* Proposition 2.1.7 for `(T^#(X), τ^#)` — `prop2_1_7_sharp` (metric and complete; the connectedness of T^#(X) is an omitted
  part: it follows as for T(X) since Φ^# is a continuous surjection from the connected ball M(X), and no topology on
  ReducedTeichGamma is modelled; the distinction of points is Nag 2.2.5, stated in the same item)
* Examples 2.1.8–2.1.10 (examples, annulus, trivial cases) — omitted: examples (2.1.9: an orientation-preserving homeomorphism
  of the sphere is homotopic to the identity; a topological fact, not Teichmüller theory)

**Near misses.** `LiZhongQC.UniversalTeichmuller.dist` (the universal space `T(1)` only), `GardinerLakic2000.teichDist`
(distance on `T(Γ)` itself, not the reduced space).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff MatrixGroups

noncomputable section

namespace Nag1988

open LiZhongQC (BeltramiGamma TeichGamma teichSetoidGamma fMuSym h36p_m IsFuchsian)

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- **Quotient pseudometric** (§2.1.5; N1:3240). For `Φ : M → T` and a function `d` on `M`,
`d_Φ(t₁, t₂) = inf {d(m₁, m₂) : Φ m₁ = t₁, Φ m₂ = t₂}`. -/
def quotientDist {M T : Type*} (d : M → M → ℝ) (Φ : M → T) (s t : T) : ℝ :=
  sInf {r | ∃ m₁ m₂, Φ m₁ = s ∧ Φ m₂ = t ∧ r = d m₁ m₂}

/-- **The distance `τ̂`** on `M(X) = BeltramiGamma Γ` (§2.1.2; N1:3201): `½ log K(g ∘ f⁻¹)`, with
`K = (1 + k)/(1 - k)` and `k = ‖(μ - ν)/(1 - ν̄μ)‖_∞` (`LiZhongQC.UniversalTeichmuller.dilatationDiffNorm`). -/
def betaDist (μ ν : BeltramiGamma Γ) : ℝ :=
  (1 / 2) * Real.log ((1 + LiZhongQC.UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1) /
    (1 - LiZhongQC.UniversalTeichmuller.dilatationDiffNorm μ.1.1 ν.1.1))

/-- **The homomorphism `E_μ`** (N1:3820, §2.5.5): `A = E_μ(γ) = w^μ γ (w^μ)⁻¹`, i.e. `w^μ(γ x) = A (w^μ x)` for the real points
`x` with `γ x` finite. (`A` is determined by `μ` and `γ`: three points fix a Möbius map.) -/
def IsDeformedBy (μ : BeltramiGamma Γ) (γ A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Prop :=
  ∀ x : ℝ, (γ 1 0 : ℂ) * x + γ 1 1 ≠ 0 → fMuSym μ.1.1 (h36p_m γ x) = h36p_m A (fMuSym μ.1.1 x)

/-- **Weak Teichmüller equivalence** `∼_#` (§2.1.1(b); N1:3166): `E_ν = α E_μ α⁻¹` for one `α ∈ Möb(ℝ)`, the same for every `γ`
(the conformal map `σ : X₁ → X₂` lifted to `ℍ`; free homotopy to the identity means `γ ↦ E(γ)` is respected up to `α`). -/
def reducedSetoidGamma (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Setoid (BeltramiGamma Γ) where
  r μ ν := ∃ α : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ γ ∈ Γ, ∀ A, IsDeformedBy μ γ A ↔ IsDeformedBy ν γ (α * A * α⁻¹)
  iseqv :=
    ⟨fun _ => ⟨1, fun γ _ A => by simp⟩,
      fun {μ ν} ⟨α, h⟩ => ⟨α⁻¹, fun γ hγ B => by
        have := h γ hγ (α⁻¹ * B * α)
        simp only [mul_assoc, mul_inv_cancel, mul_one, inv_inv] at this ⊢
        simpa [mul_assoc] using this.symm⟩,
      fun {μ ν ρ} ⟨α, h₁⟩ ⟨β, h₂⟩ => ⟨β * α, fun γ hγ A => by
        refine (h₁ γ hγ A).trans ((h₂ γ hγ (α * A * α⁻¹)).trans ?_)
        simp [mul_assoc]⟩⟩

/-- **The reduced Teichmüller space** `T^#(X) = M̂(X)/∼_#` (§2.1.1(b)), as the quotient of `M(X)` by `reducedSetoidGamma`. -/
def ReducedTeichGamma (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  Quotient (reducedSetoidGamma Γ)

/-- **Riemann equivalence** `∼_R` (§2.1.1(c); N1:3187): the groups `E_μ(Γ)` and `E_ν(Γ)` are conjugate in `Möb(ℝ)`. -/
def riemannRel (μ ν : BeltramiGamma Γ) : Prop :=
  ∃ α : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
    (∃ γ ∈ Γ, IsDeformedBy μ γ A) ↔ ∃ γ ∈ Γ, IsDeformedBy ν γ (α * A * α⁻¹)

/-- **The Riemann moduli space** `R(X) = M̂(X)/∼_R` (§2.1.1(c)), the quotient of `M(X)` by `riemannRel` (equivalence relation
generated; `riemannRel` is itself an equivalence relation: conjugation by `α`, `α⁻¹`, and products). -/
def RiemannSpaceGamma (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  Quot (riemannRel (Γ := Γ))

/-- **The Teichmüller distance `τ^#`** on `T^#(X)` (§2.1.7; N1:3282): the quotient pseudometric of `τ̂` through `Φ^#`. -/
def reducedDist (s t : ReducedTeichGamma Γ) : ℝ :=
  quotientDist betaDist (Quotient.mk (reducedSetoidGamma Γ)) s t

/-- **Unlabelled** (§2.1.1; N1:3191–3199). The natural projections `T(X) → T^#(X) → R(X)` exist: Teichmüller equivalence
implies weak Teichmüller equivalence (`α = 1`), which implies Riemann equivalence. -/
theorem para2_1_1_projections :
    (∀ μ ν : BeltramiGamma Γ, (teichSetoidGamma Γ).r μ ν → (reducedSetoidGamma Γ).r μ ν) ∧
      ∀ μ ν : BeltramiGamma Γ, (reducedSetoidGamma Γ).r μ ν → riemannRel μ ν := by
  sorry

/-- **Unlabelled** (§2.1.1; N1:3181). If `∂(X)` is empty, i.e. `Γ` is of the first kind, then Teichmüller equivalence
coincides with weak Teichmüller equivalence and `T(X) = T^#(X)`. -/
theorem para2_1_1_firstKind (hΓ : IsFuchsian Γ) (h1 : GardinerLakic2000.IsFirstKind Γ) (μ ν : BeltramiGamma Γ) :
    (teichSetoidGamma Γ).r μ ν ↔ (reducedSetoidGamma Γ).r μ ν := by
  sorry

/-- **Lemma 2.1.6** (§2.1.6; N1:3252) [CORRECTION]. Let `(M, d)` be a complete metric space and `Φ : M → T` a surjection such that
every point of `M` is as close to a fibre of `Φ` as the fibre of the point is (`hiso`: `d(m, Φ⁻¹{t}) = d_Φ(Φ m, t)`; this holds when
the fibres are the orbits of a group of isometries of `M`, which is the situation of the book: the pull-back by `Q₀` preserves
`τ̂`). Then every Cauchy sequence for the quotient pseudometric `d_Φ` converges to some point of `T`, in the sense
`d_Φ(x_n, t) → 0`. (So if `d_Φ` is a metric, it is complete.) *Correction:* without `hiso` the statement is false (a closed discrete
`M = ⋃ F_n ⊂ ℝ`, `T = ℕ`, `Φ = n` on `F_n`, with points `c_{nm} ∈ F_n` and `c_{nm} + 1/n ∈ F_m` far apart from each other, gives a
`d_Φ`-Cauchy sequence `n` with `d_Φ(n, t) → 1/t ≠ 0`); the book's proof uses `hiso` tacitly. -/
theorem lemma2_1_6 {M T : Type*} [MetricSpace M] [CompleteSpace M] (Φ : M → T) (hΦ : Function.Surjective Φ)
    (hiso : ∀ (m : M) (t : T), Metric.infDist m (Φ ⁻¹' {t}) = quotientDist dist Φ (Φ m) t) (x : ℕ → T)
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, quotientDist dist Φ (x m) (x n) < ε) :
    ∃ t : T, Tendsto (fun n => quotientDist dist Φ (x n) t) atTop (𝓝 0) := by
  sorry

/-- **Proposition 2.1.7, reduced part** (N1:3282; the distinction of points is Nag 2.2.5). `τ^#` is a metric on `T^#(X)` and
`(T^#(X), τ^#)` is complete: `τ^#(s, t) = 0` implies `s = t`, and every `τ^#`-Cauchy sequence converges. -/
theorem prop2_1_7_sharp (hΓ : IsFuchsian Γ) :
    (∀ s t : ReducedTeichGamma Γ, reducedDist s t = 0 → s = t) ∧
      ∀ x : ℕ → ReducedTeichGamma Γ, (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, reducedDist (x m) (x n) < ε) →
        ∃ t : ReducedTeichGamma Γ, Tendsto (fun n => reducedDist (x n) t) atTop (𝓝 0) := by
  sorry

end Nag1988
