import LiZhongQC.Ch07.S26_TeichmullerUniqueness
import LiZhongQC.Ch07.S25_QuadraticDifferentials
import LiZhongQC.Lemmas.UniformizedUniqueness

/-!
# Imayoshi–Taniguchi, Chapter 5 §5.3: Proof of Teichmüller's uniqueness theorem

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 5 §5.3 (`full.md` IT1:4778–5177,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions: `R = S₀`, `S = S₁` are closed Riemann surfaces, a holomorphic quadratic differential `φ dz²` is a family of
coefficients `q x` in the preferred charts (`LiZhongQC.IsHolQuadDiff`, weight `(2, 0)`), a Beltrami coefficient `μ_f` of a
quasiconformal map `f` in the chart at `x` is `LiZhongQC.complexDilatation (localMapExpr f x)`; the Beltrami coefficient of
`k φ̄/|φ|` is `k conj (q x z) / ‖q x z‖` in the chart at `x`. A *formal Teichmüller mapping* for `(k, φ)` (IT1:4542) is a
quasiconformal map with this Beltrami coefficient; `LiZhongQC.IsTeichmullerMap f q q' k` bundles such an `f` with a terminal
differential `q'` satisfying (i) and (ii) of Proposition 5.19, which is what the Proposition produces and makes unique.

* Proposition 5.16 (a `φ̃`-geodesic between two points is unique, IT1:4854) — exists: `LiZhongQC.thm25_3_unique_geodesic`
* Corollary to Proposition 5.16 (a `φ̃`-segment is the unique geodesic, IT1:4884) — exists:
  `LiZhongQC.thm25_3_unique_geodesic`, `LiZhongQC.thm25_1_geodesics`
* Lemma 5.17 (Teichmüller's lemma `|h(L)|_φ ≥ |L|_φ - M`, IT1:4894) — exists: `LiZhongQC.lemma26_1`
* Proposition 5.18 (the affine stretch is the unique extremal rectangle map, IT1:4936) — exists:
  `LiZhongQC.grotzsch_generalized`, `LiZhongQC.thm6_2_grotzsch_eq_iff`
* Definition (formal Teichmüller mapping for `(k, φ)`, IT1:4542) — `IsFormalTeichmuller`
* Proposition 5.19 (existence and uniqueness of the terminal differential, IT1:4992) — `prop5_19`
* Lemma 5.20 (the main inequality (5.6), IT1:5105) — exists: `LiZhongQC.lemma26_2`
-/

open Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (IsHolQuadDiff IsTeichmullerMap IsQCRS complexDilatation localMapExpr)

variable {S₀ S₁ : Type} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
  [CompactSpace S₀] [TopologicalSpace S₁] [ChartedSpace ℂ S₁] [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁]
  [CompactSpace S₁]

/-- **Formal Teichmüller mapping** (Ch. 5 §5.2.2). For `0 < k < 1` and a non-zero holomorphic quadratic differential `φ`
(`q`) on `R = S₀`, a quasiconformal map `f : R → S` is a formal Teichmüller mapping for `(k, φ)` if its Beltrami coefficient is
`k φ̄/|φ|`: in the chart at every `x`, `μ_f(z) = k conj (q x z) / ‖q x z‖` for almost every `z` in the domain of the local
expression (at the zeros of `φ` the right side is a null set). -/
def IsFormalTeichmuller (f : S₀ ≃ₜ S₁) (q : S₀ → ℂ → ℂ) (k : ℝ) : Prop :=
  IsQCRS f ∧ IsHolQuadDiff q ∧ q ≠ 0 ∧ 0 < k ∧ k < 1 ∧
    ∀ x : S₀, ∀ᵐ z ∂(MeasureTheory.volume.restrict (LiZhongQC.localMapDomain f x)),
      complexDilatation (localMapExpr f x) z = (k : ℂ) * (starRingEnd ℂ) (q x z) / (‖q x z‖ : ℂ)

/-- **Proposition 5.19** (Ch. 5 §5.3.2). Let `f : R → S` be a formal Teichmüller mapping for `(k, φ)`. Then there exists a unique
holomorphic quadratic differential `ψ` (`q'`) on `S` such that (i) a zero of `φ` of order `m` is mapped to a zero of `ψ` of the
same order, and (ii) around every point `p` that is not a zero of `φ` there are a `φ`-coordinate `ζ` at `p` and a `ψ`-coordinate
`ω` at `f(p)` with `ω ∘ f = (ζ + k ζ̄)/(1 - k)`: this is `IsTeichmullerMap f q q' k`. -/
theorem prop5_19 {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {k : ℝ} (hf : IsFormalTeichmuller f q k) :
    ∃! q' : S₁ → ℂ → ℂ, IsTeichmullerMap f q q' k := by
  sorry

end ImayoshiTaniguchi1992
