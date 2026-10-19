import References.GardinerLakic2000.Ch08.S09_FiniteGenus

/-!
# Gardiner–Lakic 2000, Ch. 9 §9.1 Infinitesimal main inequality (with the chapter introduction)

Source `teichmuller.txt`, lines 7236–7296 (Chapter 9, introduction and §9.1); (9.2) from the second OCR, GL1:40.

* Definition (uniquely extremal in its Teichmüller class, l. 7238; used throughout Ch. 9, 14, 15) —
  `IsUniquelyExtremalRS`
* Definition (Teichmüller Beltrami coefficient `k|φ|/φ`, l. 7238) — exists: `GardinerLakic2000.IsTeichmullerForm`
  (batch B, §4.6)
* Definition (infinitesimally equivalent; extremal and uniquely extremal in the infinitesimal class, l. 7257–7263) —
  `IsInfEquiv`, `IsInfExtremal`, `IsInfUniquelyExtremal`
* Theorem 1 (the infinitesimal main inequality (9.2), l. 7289) — `thm9_1`

Not items: the three cases (i)–(iii) and the strip and chimney examples (l. 7240–7255, examples, not cited); the
Hahn–Banach reformulation of infinitesimal unique extremality (l. 7263, U−); "extremal in `T` iff extremal in `Z`"
(l. 7265, U−; it is batch B's `cor4_10_2`); (9.1) (l. 7283, the derivation of (9.2)). Modelling (leader calibration
C0.1, C0.4): surface level; `IsUniquelyExtremalRS` is the surface counterpart of batch B's Fuchsian
`GardinerLakic2000.IsUniquelyExtremal` (the bridge is `para5_2_teichGamma_equiv`); coefficients agree "almost
everywhere" chart by chart. Integrals `∫_R u |φ|` are `LiZhongQC.surfaceIntegral φ u`. (9.2) is garbled in
`teichmuller.txt` (l. 7293) and is stated as printed in GL1:40.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (surfaceIntegral)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition** (§9 introduction, l. 7238). `μ` is uniquely extremal in its Teichmüller class: every other `ν` in
the class has `‖ν‖∞ > ‖μ‖∞` (a `ν` of the class with `‖ν‖∞ ≤ ‖μ‖∞` equals `μ` almost everywhere). -/
def IsUniquelyExtremalRS (p : UpperHalfPlane → R) (μ : beltramiBall R) : Prop :=
  IsExtremalRS p μ ∧ ∀ ν : beltramiBall R, Quot.mk (teichRel p) ν = Quot.mk (teichRel p) μ →
    beltramiNormRS ν.1 ≤ beltramiNormRS μ.1 → ∀ x : R, ν.1 x =ᵐ[volume.restrict (chartAt ℂ x).target] μ.1 x

/-- **Definition** (§9 introduction, l. 7257–7263). `μ` and `ν` are infinitesimally equivalent:
`∫_R φμ = ∫_R φν` for every `φ ∈ A(R)`. -/
def IsInfEquiv (μ ν : R → ℂ → ℂ) : Prop := ∀ φ ∈ integrableHolQDSet R, pairingRS φ μ = pairingRS φ ν

/-- **Definition** (§9 introduction, l. 7263). `μ` is extremal in its infinitesimal class: `‖μ‖∞ ≤ ‖ν‖∞` for every
`ν` infinitesimally equivalent to `μ`. -/
def IsInfExtremal (μ : R → ℂ → ℂ) : Prop :=
  μ ∈ beltramiSpace R ∧ ∀ ν ∈ beltramiSpace R, IsInfEquiv μ ν → beltramiNormRS μ ≤ beltramiNormRS ν

/-- **Definition** (§9 introduction, l. 7263). `μ` is uniquely extremal in its infinitesimal class: `‖μ‖∞ < ‖ν‖∞`
for every other `ν` infinitesimally equivalent to `μ`. -/
def IsInfUniquelyExtremal (μ : R → ℂ → ℂ) : Prop :=
  IsInfExtremal μ ∧ ∀ ν ∈ beltramiSpace R, IsInfEquiv μ ν → beltramiNormRS ν ≤ beltramiNormRS μ →
    ∀ x : R, ν x =ᵐ[volume.restrict (chartAt ℂ x).target] μ x

/-- **Theorem 1** (the infinitesimal main inequality (9.2), §9.1, l. 7289; GL1:40). If `μ` and `ν` (`‖μ‖∞, ‖ν‖∞ < 1`)
induce the same functional on `A(R)`, then for `φ ∈ A(R)`
`∫ |φ|(1 − |μ|²) ≤ ∫ |φ| |1 − μφ/|φ||² |1 + ν (φ/|φ|) (1 − μ̄φ̄/|φ|)/(1 − μφ/|φ|)|² / (1 − |ν|²)`. -/
theorem thm9_1 [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {μ ν : R → ℂ → ℂ} (hμ : μ ∈ beltramiBall R)
    (hν : ν ∈ beltramiBall R) (heq : IsInfEquiv μ ν) {φ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R) :
    surfaceIntegral φ (fun x z => ENNReal.ofReal (1 - ‖μ x z‖ ^ 2)) ≤
      surfaceIntegral φ (fun x z => ENNReal.ofReal (‖1 - μ x z * (φ x z / ‖φ x z‖)‖ ^ 2 *
        ‖1 + ν x z * (φ x z / ‖φ x z‖) * ((1 - conj (μ x z) * (conj (φ x z) / ‖φ x z‖)) /
          (1 - μ x z * (φ x z / ‖φ x z‖)))‖ ^ 2 / (1 - ‖ν x z‖ ^ 2))) := by
  sorry

end GardinerLakic2000
