import References.GardinerLakic2000.Ch09.S01_InfinitesimalMainInequality

/-!
# Gardiner–Lakic 2000, Ch. 9 §9.2 Constant absolute value

Source `teichmuller.txt`, lines 7297–7462 (Chapter 9, §9.2).

* Definition (`δ(φ) = k‖φ‖ − Re ∫_R μφ`, Reich's notation, l. 7306) — `reichDelta`
* Definition (constant absolute value `|μ| = k` a.e., l. 7298) — `HasConstModulus`
* Definition (integrals over a subset `E ⊆ R`, l. 7312–7436) — `setIntegralQD`, `restrictBeltrami`, `IsNonnullSetRS`
* Formula (9.3) (Reich's infinitesimal delta inequality, l. 7302; cited in Lemma 1) — `eq9_3`
* Lemma 1 (l. 7308) — `lemma9_1`
* Formula (9.6) (the delta inequality, l. 7376; the constant-modulus case of Theorem 5, not separate) — exists:
  `GardinerLakic2000.thm9_5` (§9.4)
* Lemma 2 (l. 7381) — `lemma9_2`
* Theorem 2 (TFAE (a)–(f), with (9.9), (9.10), l. 7411; cited as "Theorem 1" at l. 7470) — `thm9_2`

Not items: (9.4), (9.5), (9.7), (9.8) (proof steps); the Hamilton–Krushkal–Reich–Strebel criterion (l. 7403, U−; it
is batch B's `cor4_10_2`). Modelling: surface level (C0.1). A "measurable subset `E` of `R` with nonzero measure" is
a set whose chart images are measurable, one of them of positive measure (`IsNonnullSetRS`); `∬_E |φ|` is
`setIntegralQD φ E` and `∬_E μφ` is `pairingRS φ (restrictBeltrami μ E)`. The constant `C` of (9.3) depends only on
`k` (`∀ k ∃ C`). In (e), (f) the coefficient `μχ_E + μ/(1 + r) χ_{R−E}` is any element of `M(R)` equal to it in charts.
The book cites this theorem as "Theorem 1" (l. 7470) and "Theorem 7.1" (Exercise 1) [misprint].
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

open scoped Classical

namespace GardinerLakic2000

universe u

open LiZhongQC (surfaceIntegral quadDiffNorm)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition** (Reich's `δ(φ)`, §9.2, l. 7306). `δ(φ) = k‖φ‖ − Re ∫_R μφ`. -/
def reichDelta (k : ℝ) (μ φ : R → ℂ → ℂ) : ℝ := k * (quadDiffNorm φ).toReal - (pairingRS φ μ).re

/-- **Definition** (§9.2, l. 7298). `μ` has constant absolute value `k`: `|μ| = k` almost everywhere. -/
def HasConstModulus (μ : R → ℂ → ℂ) (k : ℝ) : Prop :=
  ∀ x : R, ∀ᵐ z ∂(volume.restrict (chartAt ℂ x).target), ‖μ x z‖ = k

/-- Helper (§9.2). `∬_E |φ|` for a subset `E ⊆ R`. -/
def setIntegralQD (φ : R → ℂ → ℂ) (E : Set R) : ℝ≥0∞ :=
  surfaceIntegral φ (fun x z => if (chartAt ℂ x).symm z ∈ E then 1 else 0)

/-- Helper (§9.2). `μ χ_E`: the Beltrami differential `μ` on `E`, `0` off `E`. -/
def restrictBeltrami (μ : R → ℂ → ℂ) (E : Set R) : R → ℂ → ℂ :=
  fun x z => if (chartAt ℂ x).symm z ∈ E then μ x z else 0

/-- Helper (§9.2). `E` is a measurable subset of `R` of nonzero measure (read in the charts). -/
def IsNonnullSetRS (E : Set R) : Prop :=
  (∀ x : R, MeasurableSet (chartAt ℂ x '' (E ∩ (chartAt ℂ x).source))) ∧
    ∃ x : R, 0 < volume (chartAt ℂ x '' (E ∩ (chartAt ℂ x).source))

/-- **Formula (9.3)** (Reich's infinitesimal delta inequality, §9.2, l. 7302). If `|μ| = k` a.e. and `ν` is
infinitesimally equivalent to `μ` with `‖ν‖∞ ≤ k`, then `∫ |μ − ν|²|φ| ≤ C(k) (k‖φ‖ − Re ∫ μφ)` for all `φ ∈ A(R)`. -/
theorem eq9_3 (k : ℝ) (hk0 : 0 < k) (hk : k < 1) :
    ∃ C : ℝ, ∀ (R : Type u) [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
      [IsManifold 𝓘(ℂ) ω R] (μ ν : R → ℂ → ℂ), μ ∈ beltramiBall R → HasConstModulus μ k →
      ν ∈ beltramiSpace R → beltramiNormRS ν ≤ ENNReal.ofReal k → IsInfEquiv μ ν →
        ∀ φ ∈ integrableHolQDSet R,
          (surfaceIntegral φ (fun x z => ENNReal.ofReal (‖μ x z - ν x z‖ ^ 2))).toReal ≤ C * reichDelta k μ φ := by
  sorry

/-- **Lemma 1** (§9.2, l. 7308). If `μ` has constant absolute value and is uniquely extremal in its class in `T`, it
is uniquely extremal in its class in `Z`. -/
theorem lemma9_1 [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {p : UpperHalfPlane → R}
    (hp : ∃ Γ, LiZhongQC.IsFuchsian Γ ∧ LiZhongQC.IsUniformization Γ p) {μ : beltramiBall R} {k : ℝ}
    (hk : HasConstModulus μ.1 k) (hμ : IsUniquelyExtremalRS p μ) : IsInfUniquelyExtremal μ.1 := by
  sorry

/-- **Lemma 2** (§9.2, l. 7381). If `μ` has constant absolute value and is uniquely extremal in its class in `Z`, it
is uniquely extremal in its class in `T`. -/
theorem lemma9_2 [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {p : UpperHalfPlane → R}
    (hp : ∃ Γ, LiZhongQC.IsFuchsian Γ ∧ LiZhongQC.IsUniformization Γ p) {μ : beltramiBall R} {k : ℝ}
    (hk : HasConstModulus μ.1 k) (hμ : IsInfUniquelyExtremal μ.1) : IsUniquelyExtremalRS p μ := by
  sorry

/-- **Theorem 2** (§9.2, l. 7411). For `μ ∈ M(R)` with constant absolute value `k = ‖μ‖∞` the following are
equivalent: (a) `μ` is uniquely extremal in `T`; (b) uniquely extremal in `Z`; (c) for every measurable `E` of nonzero
measure there are unit vectors `φₙ ∈ A` with `(k − Re ∫ μφₙ)/∫_E |φₙ| → 0`; (d) for every such `E` there are unit
vectors with (9.9) `Re ∫_E μφₙ / ∫_E |φₙ| → k` and (9.10) `(k ∫_{R−E} |φₙ| − Re ∫_{R−E} μφₙ)/∫_E |φₙ| → 0`; (e) `μ` is
extremal in `T` and `[μχ_E + μ/(1+r) χ_{R−E}]` is a Strebel point for every compact `E` of nonzero measure and
`r > 0`; (f) `μ` is extremal in `Z` and these classes are infinitesimal Strebel points (`b < ‖·‖`).
[CORRECTION] (AUDIT5_GL P1) "Constant absolute value" means `|μ| = k > 0`; the hypothesis `hk0 : 0 < ‖μ‖∞` is added.
For `μ = 0`, (a) and (b) hold but (f) would need `b(0) < ‖0‖ = 0`. -/
theorem thm9_2 [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {p : UpperHalfPlane → R}
    (hp : ∃ Γ, LiZhongQC.IsFuchsian Γ ∧ LiZhongQC.IsUniformization Γ p) {μ : beltramiBall R}
    (hk : HasConstModulus μ.1 (beltramiNormRS μ.1).toReal) (hk0 : 0 < (beltramiNormRS μ.1).toReal) :
    List.TFAE [IsUniquelyExtremalRS p μ, IsInfUniquelyExtremal μ.1,
      ∀ E : Set R, IsNonnullSetRS E → ∃ φ : ℕ → R → ℂ → ℂ,
        (∀ n, φ n ∈ integrableHolQDSet R ∧ quadDiffNorm (φ n) = 1) ∧
        Tendsto (fun n => ((beltramiNormRS μ.1).toReal - (pairingRS (φ n) μ.1).re) / (setIntegralQD (φ n) E).toReal)
          atTop (𝓝 0),
      ∀ E : Set R, IsNonnullSetRS E → ∃ φ : ℕ → R → ℂ → ℂ,
        (∀ n, φ n ∈ integrableHolQDSet R ∧ quadDiffNorm (φ n) = 1) ∧
        Tendsto (fun n => (pairingRS (φ n) (restrictBeltrami μ.1 E)).re / (setIntegralQD (φ n) E).toReal) atTop
          (𝓝 (beltramiNormRS μ.1).toReal) ∧
        Tendsto (fun n => ((beltramiNormRS μ.1).toReal * (setIntegralQD (φ n) Eᶜ).toReal -
          (pairingRS (φ n) (restrictBeltrami μ.1 Eᶜ)).re) / (setIntegralQD (φ n) E).toReal) atTop (𝓝 0),
      IsExtremalRS p μ ∧ ∀ E : Set R, IsCompact E → IsNonnullSetRS E → ∀ r > (0 : ℝ), ∀ α : beltramiBall R,
        (∀ x : R, EqOn (α.1 x) (fun z => if (chartAt ℂ x).symm z ∈ E then μ.1 x z else μ.1 x z / (1 + r))
          (chartAt ℂ x).target) → IsStrebelPoint p (Quot.mk (teichRel p) α),
      IsInfExtremal μ.1 ∧ ∀ E : Set R, IsCompact E → IsNonnullSetRS E → ∀ r > (0 : ℝ), ∀ α : beltramiBall R,
        (∀ x : R, EqOn (α.1 x) (fun z => if (chartAt ℂ x).symm z ∈ E then μ.1 x z else μ.1 x z / (1 + r))
          (chartAt ℂ x).target) →
        infBoundaryDilatation (fun φ => pairingRS φ α.1) < ENNReal.ofReal (zNorm (fun φ => pairingRS φ α.1))] := by
  sorry

end GardinerLakic2000
