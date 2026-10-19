import References.GardinerLakic2000.Ch14.S08_BoundaryDilatationInequalities

/-!
# Gardiner–Lakic 2000, Ch. 14 §14.9 Contraction

Source `teichmuller.txt`, lines 10777–11060.

* Definition (k, h, h*, β(μ), l. 10778) — `hStarOf`, `betaOf` (k, h inline where used)
* Definition (the quantities A, B, C, D, l. 10792–10797) — `effA`, `effB`, `effC`, `effD`
* Theorem 7 (inequalities for boundary dilatation, [EGL98a], l. 10800) — `thm14_7`
* Corollary 4 (l. 11053) — `cor14_7_4`

Not items (DESIGN §3): "infinitesimally / globally efficient" (l. 10780, informal; measured by `D` and `A`) and (14.28)
(l. 10783, announced; it is Corollary 4).

**Modelling.** For `μ ∈ M(R)`: `H* = H*(μ)` is B's `boundaryDilatationStarK μ`, `H = H[μ]` is B's
`boundaryDilatationH` of the class, `h* = (H* − 1)/(H* + 1)`, and `β(μ)` is Part A's `betaSeminorm` of the functional
`φ ↦ ∬ φ μ`; all are taken as real numbers. The suprema over degenerating sequences (Part A's `IsDegeneratingSeq`) are
in `ℝ≥0∞`; the integrals are read as in (II′) (`surfaceIntegral` weighting by `|φₙ|`), and `∬ Re (μ φₙ/(1 − |μ|²))` is
the real part of Part A's `pairingRS`. Theorem 7 needs degenerating sequences to exist (`A(R)` infinite dimensional;
otherwise the suprema are `0` and `B ≤ 2A` fails) [reading]. The proof's `B ≤ 8D/(1 − h*)²` is the printed
`½B ≤ 4D/(1 − h*)²`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsFuchsian IsUniformization surfaceIntegral)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition** (§14.9, l. 10778). `h* = (H* − 1)/(H* + 1)` for `H* = H*(μ)`. -/
def hStarOf (μ : R → ℂ → ℂ) : ℝ :=
  ((boundaryDilatationStarK μ).toReal - 1) / ((boundaryDilatationStarK μ).toReal + 1)

/-- **Definition** (§14.9, l. 10778). `β(μ)`: the `β`-norm of the functional represented by `μ`. -/
def betaOf (μ : R → ℂ → ℂ) : ℝ := (betaSeminorm fun φ => pairingRS φ μ).toReal

/-- **Definition** (§14.9, l. 10793). `A = H* − H`. -/
def effA (p : UpperHalfPlane → R) (μ : beltramiBall R) : ℝ :=
  (boundaryDilatationStarK μ.1).toReal - (boundaryDilatationH p (Quot.mk (teichRel p) μ)).toReal

/-- **Definition** (§14.9, l. 10794). `B = H* − sup_{φₙ} limsup_n ∬_R |φₙ| |1 + μ φₙ/|φₙ||² / (1 − |μ|²)`. -/
def effB (μ : R → ℂ → ℂ) : ℝ :=
  (boundaryDilatationStarK μ).toReal - (⨆ (φ : ℕ → R → ℂ → ℂ) (_ : IsDegeneratingSeq φ),
    limsup (fun n => surfaceIntegral (φ n) fun x z =>
      ENNReal.ofReal (‖1 + μ x z * (φ n x z / ‖φ n x z‖)‖ ^ 2 / (1 - ‖μ x z‖ ^ 2))) atTop).toReal

/-- **Definition** (§14.9, l. 10795). `C = h*/(1 − h*²) − sup_{φₙ} limsup_n |∬_R Re (μ φₙ/(1 − |μ|²))|`. -/
def effC (μ : R → ℂ → ℂ) : ℝ :=
  hStarOf μ / (1 - hStarOf μ ^ 2) - (⨆ (φ : ℕ → R → ℂ → ℂ) (_ : IsDegeneratingSeq φ),
    limsup (fun n => ENNReal.ofReal |(pairingRS (φ n) fun x z => μ x z / (1 - (‖μ x z‖ : ℂ) ^ 2)).re|)
      atTop).toReal

/-- **Definition** (§14.9, l. 10796). `D = h* − β`. -/
def effD (μ : R → ℂ → ℂ) : ℝ := hStarOf μ - betaOf μ

variable [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R]

/-- **Theorem 7** (inequalities for boundary dilatation, §14.9, l. 10800; [EGL98a]).
`B ≤ A (H* + 1)/H* ≤ 2A`, `A ≤ H H* B` and `D ≤ C ≤ ½ B ≤ 4D/(1 − h*)²`. -/
theorem thm14_7 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (hdeg : ∃ φ : ℕ → R → ℂ → ℂ, IsDegeneratingSeq φ) (μ : beltramiBall R) :
    effB μ.1 ≤ effA p μ * (((boundaryDilatationStarK μ.1).toReal + 1) / (boundaryDilatationStarK μ.1).toReal) ∧
      effA p μ * (((boundaryDilatationStarK μ.1).toReal + 1) / (boundaryDilatationStarK μ.1).toReal) ≤
        2 * effA p μ ∧
      effA p μ ≤ (boundaryDilatationH p (Quot.mk (teichRel p) μ)).toReal *
        (boundaryDilatationStarK μ.1).toReal * effB μ.1 ∧
      effD μ.1 ≤ effC μ.1 ∧ effC μ.1 ≤ effB μ.1 / 2 ∧ effB μ.1 / 2 ≤ 4 * effD μ.1 / (1 - hStarOf μ.1) ^ 2 := by
  sorry

/-- **Corollary 4** (§14.9, l. 11053). If `8 H*(f) H(f) / (1 − h*(f))² ≤ M`, then
`h* − β ≤ H* − H ≤ M (h* − β)`. -/
theorem cor14_7_4 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (hdeg : ∃ φ : ℕ → R → ℂ → ℂ, IsDegeneratingSeq φ) (μ : beltramiBall R) {M : ℝ}
    (hM : 8 * (boundaryDilatationStarK μ.1).toReal * (boundaryDilatationH p (Quot.mk (teichRel p) μ)).toReal /
      (1 - hStarOf μ.1) ^ 2 ≤ M) :
    effD μ.1 ≤ effA p μ ∧ effA p μ ≤ M * effD μ.1 := by
  sorry

end GardinerLakic2000
