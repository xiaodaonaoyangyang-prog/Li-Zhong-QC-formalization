import References.GardinerLakic2000.Ch14.S07_ManifoldStructure

/-!
# Gardiner–Lakic 2000, Ch. 14 §14.8 Inequalities for boundary dilatation

Source `teichmuller.txt`, lines 10737–10776.

* Definition (`H*(f)`, `H(f)`, l. 10738) — exists: `GardinerLakic2000.boundaryDilatationStarK`
  `GardinerLakic2000.boundaryDilatationH`
* Definition (`[[f]]`, the class in `AT`, l. 10738) — exists: `GardinerLakic2000.AsymTeichSpace`
* Unlabelled (`f_E ∈ [[f]]`; `H` depends only on `[[f]]`, l. 10740–10742; used in Theorem 7, l. 10805) —
  `para14_8_H_asym_invariant`
* Formula (I′) (l. 10767; cited in Theorem 10) — `ineq14_Ip`
* Formula (II′) (l. 10774; cited in Theorem 7) — `ineq14_IIp`

Not items (DESIGN §3): (I) and (II) (l. 10750–10758, recalled: B's `thm4_9_i`, `thm4_9_ii`); "`K(f_E) = K(f|R ∖ E)`"
(l. 10742, immediate from the definition of `f_E`).

**Modelling.** `f_E` is given by its Beltrami coefficient `μ_E`, equal to `0` on `E` and to `μ` off `E` (read in
charts). `H[f]` is B's `boundaryDilatationH` of the Teichmüller class, which by this paragraph depends only on the
`AT`-class. The integrands of (I′), (II′) are garbled [OCR] and are read as in B's `thm4_9_i`, `thm4_9_ii`:
`|φ| |1 ∓ μ φ/|φ||² / (1 − |μ|²)`. Degenerating sequences are Part A's `IsDegeneratingSeq` (norm `1`). In (II′) the
book's index `n ≥ 1` is `n + 1`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsFuchsian IsUniformization quadDiffNorm surfaceIntegral)

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

open Classical in
/-- **Unlabelled** (§14.8, l. 10740–10742). For a compact `E ⊆ R`, the coefficient `μ_E` (`0` on `E`, `μ` off `E`)
lies in `M(R)` and represents the same point of `AT` as `μ`; and `H` depends only on the class in `AT`. -/
theorem para14_8_H_asym_invariant {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) :
    (∀ (μ : beltramiBall R) (E : Set R), IsCompact E →
      ∃ hE : (fun x z => if (chartAt ℂ x).symm z ∈ E then 0 else μ.1 x z) ∈ beltramiBall R,
        asymRel p μ ⟨_, hE⟩) ∧
    ∀ μ ν : beltramiBall R, asymRel p μ ν →
      boundaryDilatationH p (Quot.mk (teichRel p) μ) = boundaryDilatationH p (Quot.mk (teichRel p) ν) := by
  sorry

/-- **Formula (I′)** (§14.8, l. 10767). `1/H[f] ≤ inf_{φₙ} liminf_n ∬_R |φₙ| |1 − μ φₙ/|φₙ||² / (1 − |μ|²)` over the
degenerating sequences. -/
theorem ineq14_Ip {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (μ : beltramiBall R) :
    (boundaryDilatationH p (Quot.mk (teichRel p) μ))⁻¹ ≤
      ⨅ (φ : ℕ → R → ℂ → ℂ) (_ : IsDegeneratingSeq φ), liminf (fun n => surfaceIntegral (φ n) fun x z =>
        ENNReal.ofReal (‖1 - μ.1 x z * (φ n x z / ‖φ n x z‖)‖ ^ 2 / (1 - ‖μ.1 x z‖ ^ 2))) atTop := by
  sorry

open Classical in
/-- **Formula (II′)** (§14.8, l. 10771–10774). For compact sets `Eₙ` increasing to `R` (the union of their interiors
is `R`) there are `φₙ ∈ A(R)` of norm `1` with
`H[f] ≤ 1/n + ∬_{R∖Eₙ} |φₙ| |1 + μ φₙ/|φₙ||² / (1 − |μ|²) + ∬_{Eₙ} |φₙ|`. -/
theorem ineq14_IIp {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (hA : ∃ φ ∈ integrableHolQDSet R, quadDiffNorm φ = 1) (μ : beltramiBall R)
    {E : ℕ → Set R} (hEc : ∀ n, IsCompact (E n)) (hEm : Monotone E) (hEu : (⋃ n, interior (E n)) = univ) :
    ∃ φ : ℕ → R → ℂ → ℂ, (∀ n, φ n ∈ integrableHolQDSet R ∧ quadDiffNorm (φ n) = 1) ∧
      ∀ n : ℕ, boundaryDilatationH p (Quot.mk (teichRel p) μ) ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) +
        surfaceIntegral (φ n) fun x z => if (chartAt ℂ x).symm z ∈ E n then 1 else
          ENNReal.ofReal (‖1 + μ.1 x z * (φ n x z / ‖φ n x z‖)‖ ^ 2 / (1 - ‖μ.1 x z‖ ^ 2)) := by
  sorry

end GardinerLakic2000
