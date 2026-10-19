import References.GardinerLakic2000.Ch04.S08_InfinitesimalFrameMapping

/-!
# Gardiner–Lakic 2000, Ch. 4 §4.9 The fundamental inequalities

Source `teichmuller.txt`, lines 4297–4386 (and the chapter introduction, (4.2), (4.3), l. 3663–3675).

* Lemma 4 (l. 4330; cited Ch. 8, l. 6588) — `lemma4_4`
* Theorem 9 (the fundamental inequalities I = (4.2) = (4.26) and II = (4.3), l. 4342; cited l. 5964, 7338, 10746,
  12884) — `thm4_9_i`, `thm4_9_ii`

Not items (DESIGN §3): `μ₁ ∘ f₀ = −μ₀ p̄/p` (l. 4301, U−; content `LiZhongQC.eq13_5_7_inverse`), the elementary
inequality with the constant 7 (l. 4370), steps of the proofs. Near miss: `LiZhongQC.eq35_6` (inequality I on the disc).

**Conventions.** As §4.6. `K₀` is Part A's `minimalDilatation p P` of the class `P` of `f`; the supremum in II is over
`φ ∈ A(R)` with `‖φ‖ = 1`. In Lemma 4 the exhaustion `Cₙ` is by compact sets.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsFuchsian IsUniformization quadDiffNorm surfaceIntegral)

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

open scoped Classical in
/-- **[CORRECTION]** (AUDIT4 G7) `0 < ‖μ₀‖∞` is added: for `μ₀ = 0` (the base point, `k₀ = 0`) no `μₙ = 0` is a frame mapping (`ess sup < k₀ = 0`
is impossible), so the first conjunct fails.
**Lemma 4** (§4.9, l. 4330). Let `μ₀` be extremal in its class, `0 < ε < 1`, `Cₙ` an increasing sequence of
compact sets exhausting `R`, and `μₙ = μ₀` on `Cₙ`, `μₙ = (1 − ε)μ₀` off `Cₙ`. Then for large `n`, `μₙ` is (the
coefficient of) a frame mapping for its class, and the extremal dilatation `Kₙ` of the class of `μₙ` tends to
`K₀`. -/
theorem lemma4_4 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (μ₀ : beltramiBall R) (hμ₀ : IsExtremalRS p μ₀) (hμ₀0 : 0 < beltramiNormRS μ₀.1) {ε : ℝ} (hε₀ : 0 < ε)
    (hε₁ : ε < 1) {C : ℕ → Set R} (hC : ∀ n, IsCompact (C n)) (hmono : Monotone C) (hexh : ⋃ n, C n = univ)
    (μ : ℕ → beltramiBall R)
    (hμ : ∀ n x z, (μ n).1 x z = if (chartAt ℂ x).symm z ∈ C n then μ₀.1 x z else (1 - ε) * μ₀.1 x z) :
    (∀ᶠ n in atTop, IsFrameMapping p (Quot.mk (teichRel p) (μ n)) (μ n)) ∧
      Tendsto (fun n => minimalDilatation p (Quot.mk (teichRel p) (μ n))) atTop
        (𝓝 (minimalDilatation p (Quot.mk (teichRel p) μ₀))) := by
  sorry

/-- **Theorem 9 I** (the first fundamental inequality (4.26), §4.9, l. 4342). If `f : R → R₁` is quasiconformal with
Beltrami coefficient `μ` and `K₀` is the dilatation of an extremal map in the class of `f`, then
`1/K₀ ≤ ∬_R |1 − μφ/|φ||²/(1 − |μ|²) |φ| dx dy` for all `φ ∈ A(R)` with `‖φ‖ = 1`. -/
theorem thm4_9_i {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (μ : beltramiBall R) {φ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R)
    (hφ1 : quadDiffNorm φ = 1) :
    (minimalDilatation p (Quot.mk (teichRel p) μ))⁻¹ ≤ surfaceIntegral φ fun x z =>
      ENNReal.ofReal (‖1 - μ.1 x z * (φ x z / ‖φ x z‖)‖ ^ 2 / (1 - ‖μ.1 x z‖ ^ 2)) := by
  sorry

/-- **Theorem 9 II** (the second fundamental inequality, §4.9, l. 4352). In the same situation,
`K₀ ≤ sup ∬_R |1 + μφ/|φ||²/(1 − |μ|²) |φ| dx dy`, the supremum over `φ ∈ A(R)` with `‖φ‖ = 1`.
Modelling: `A(R) ≠ 0` (for `A(R) = 0` the supremum is empty; the book's surfaces have `A(R) ≠ 0`, cf. l. 3686). -/
theorem thm4_9_ii {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) (hA : ∃ φ ∈ integrableHolQDSet R, quadDiffNorm φ = 1) (μ : beltramiBall R) :
    minimalDilatation p (Quot.mk (teichRel p) μ) ≤
      ⨆ (φ : R → ℂ → ℂ) (_ : φ ∈ integrableHolQDSet R ∧ quadDiffNorm φ = 1), surfaceIntegral φ fun x z =>
        ENNReal.ofReal (‖1 + μ.1 x z * (φ x z / ‖φ x z‖)‖ ^ 2 / (1 - ‖μ.1 x z‖ ^ 2)) := by
  sorry

end GardinerLakic2000
