import References.GardinerLakic2000.Ch03.S08_RationalQuadraticDifferentials

/-!
# Gardiner–Lakic 2000, Ch. 3 §3.9 The equivalence theorem

Source `teichmuller.txt`, lines 3037–3170 (Chapter 3, §3.9).

* Definition (the Teichmüller norm of a vector field on `Λ`, through the map `I` of §3.5, l. 2629, 3040) —
  `teichNormVF`
* Theorem 11 (the equivalence theorem [EGL97], l. 3040; cited in §3.10, Ch. 16, 17) — `thm3_11`
* Corollary 2 (l. 3102) — `cor3_11_2`
* Corollary 3 (l. 3128) — `cor3_11_3`

Not items: the proof for `Λ = ℂ̄` ((3.40)–(3.43), l. 3048–3098; "Combining (3.36) and (3.42)" at l. 3094 reads (3.26)
[misprint; so also GL8:2985]); the Remark on the atomic decomposition (l. 3139). Modelling: a vector field `V` on
`Λ` belongs to `Z_cr(Λ)` when `‖V‖_cr < ∞`; its Teichmüller norm is `inf ‖μ‖∞` over the `μ` with `V = V_μ + p` on `Λ`
(`V_μ` of (3.18), `p` a quadratic polynomial: the identification `I` of `L∞(ℂ)/N` with vector fields modulo quadratic
polynomials). "`V(φ_Q)`" in Corollary 2 is the pairing `∬ μ φ_Q` for any such `μ` (it does not depend on the choice).
The constants of Corollaries 2 and 3 are "the constant of the equivalence theorem"; each statement asserts its own
universal constant. In Corollary 3 the four-pole differentials of the quadruples containing `∞` are `phiQInf`, and
`φ_i` is determined up to a unimodular factor (l. 3118), which is written as the factor `c_i`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane phiArea normalizedCauchyTOn IsBeltramiCoeff)

/-- **Definition** (§3.9, l. 3040; the map `I` of §3.5, l. 2629). The infinitesimal Teichmüller norm of a vector field
`V` on `Λ`: `‖V‖_T = inf ‖μ‖∞` over the bounded `μ` with `V = V_μ + p` on `Λ`, `p` a quadratic polynomial. -/
def teichNormVF (Λ : Set ExtPlane) (V : ℂ → ℂ) : ℝ≥0∞ :=
  ⨅ (μ : ℂ → ℂ) (_ : (∃ k : ℝ, IsBeltramiCoeff μ univ k) ∧ ∃ a b c : ℂ, ∀ z : ℂ, (z : ExtPlane) ∈ Λ →
      V z = normalizedCauchyTOn univ μ z + (a * z ^ 2 + b * z + c)), eLpNorm μ ⊤ volume

/-- **Theorem 11** (the equivalence theorem, [EGL97], §3.9, l. 3040). There is a constant `C` such that for every
closed `Λ ⊆ ℂ̄` and every `V ∈ Z_cr(Λ)`, `‖V‖_cr ≤ ‖V‖_T ≤ C ‖V‖_cr`. -/
theorem thm3_11 :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (Λ : Set ExtPlane) (V : ℂ → ℂ), IsClosed Λ → V ∈ zCrSet Λ →
      crNorm Λ V ≤ teichNormVF Λ V ∧ teichNormVF Λ V ≤ C * crNorm Λ V := by
  sorry

/-- **Corollary 2** (§3.9, l. 3102). For `V` with bounded cross-ratio norm on `Λ`, represented by `μ`,
`‖V‖_T ≤ C sup_Q |V(φ_Q)|` over the quadruples `Q ⊆ Λ`; `C` does not depend on `Λ`. -/
theorem cor3_11_2 :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (Λ : Set ExtPlane) (V μ : ℂ → ℂ), IsClosed Λ → V ∈ zCrSet Λ →
      (∃ k : ℝ, IsBeltramiCoeff μ univ k) →
      (∃ a b c : ℂ, ∀ z : ℂ, (z : ExtPlane) ∈ Λ → V z = normalizedCauchyTOn univ μ z + (a * z ^ 2 + b * z + c)) →
        teichNormVF Λ V ≤ C * ⨆ (Q : Fin 4 → ℂ) (_ : Function.Injective Q ∧ ∀ i, (Q i : ExtPlane) ∈ Λ),
          (‖∫ z, μ z * phiQ Q z‖₊ : ℝ≥0∞) := by
  sorry

/-- **Corollary 3** (§3.9, l. 3128). Every `φ ∈ Rat(Λ)` is a finite combination `φ = Σ aᵢ φᵢ`, `aᵢ ≥ 0`, of
differentials `φᵢ` of norm 1 with four poles at points of a quadruple `Qᵢ` among the poles of `φ` (and `∞`), with
`Σ aᵢ ≤ C ‖φ‖`; `C` depends neither on `Λ` nor on `φ`. -/
theorem cor3_11_3 :
    ∃ C : ℝ, ∀ (Λ : Set ExtPlane) (φ : ℂ → ℂ), IsClosed Λ → φ ∈ ratSpace Λ →
      ∃ (n m : ℕ) (Q : Fin n → Fin 4 → ℂ) (P : Fin m → Fin 3 → ℂ) (a : Fin n → ℝ) (b : Fin m → ℝ)
        (c : Fin n → ℂ) (d : Fin m → ℂ),
        (∀ i, 0 ≤ a i ∧ ‖c i‖ = 1 ∧ Function.Injective (Q i) ∧ ∀ j, ¬ AnalyticAt ℂ φ (Q i j)) ∧
        (∀ i, 0 ≤ b i ∧ ‖d i‖ = 1 ∧ Function.Injective (P i) ∧ (∀ j, ¬ AnalyticAt ℂ φ (P i j)) ∧
          (OnePoint.infty : ExtPlane) ∈ Λ) ∧
        (φ =ᵐ[volume] fun z => ∑ i, (a i : ℂ) * c i * phiQ (Q i) z + ∑ i, (b i : ℂ) * d i * phiQInf (P i) z) ∧
        ∑ i, a i + ∑ i, b i ≤ C * (phiArea φ univ).toReal := by
  sorry

end GardinerLakic2000
