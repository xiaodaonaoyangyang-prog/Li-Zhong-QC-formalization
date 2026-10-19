import References.GardinerLakic2000.Ch12.S06_HeightsMapping

/-!
# Gardiner–Lakic 2000, Ch. 12 §12.7 Variation of the Dirichlet norm

Source `teichmuller.txt`, lines 9272–9469.

* Theorem 5 (the first variation of `log M_μ(|dv|)`, l. 9273; restated as (13.2), cited l. 9734) — `thm12_5`
* Definition (allowable curves for `φ`, types 1–3, l. 9281–9286) — `IsAllowableCurve`
* Lemma 4 ((12.9), l. 9287) — `lemma12_4`
* Lemma 5 (l. 9330) — `lemma12_5`

Not items (DESIGN §3): the Remark after Lemma 5 (continuity of `M_μ`, l. 9364, U−), (12.10)–(12.15) (proof).

**Modelling.** Theorem 5: "differentiable on `T`, with the displayed expansion" is stated as the expansion at the base
point (`∀ ε ∃ δ`, `o(‖μ‖∞)`), for every quasiconformal `f` with coefficient `μ` [reading]. Allowable curves: simple
loops made of one closed vertical piece (type 1), a vertical and a horizontal piece (type 2), or four alternating
pieces (type 3); vertical for `φ` is horizontal for `−φ`. The book's "departs … from the opposite side" is not
imposed (the class is then larger, so Lemma 4's hypothesis is stronger) [reading]. "For almost every allowable curve"
is "for every allowable curve whose base point lies off a null set", as in batch B's `thm4_1`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (Loop quadDiffNorm surfaceIntegral IsQCRS IsHorizontalArcRS IsDiffFamilyAE phiLengthPath)

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

/-- **Theorem 5** (§12.7, l. 9273). Let `Ṙ` be of finite analytic type and `|dv|` a measured foliation, and let `φ` be
the unique element of `A(Ṙ)` whose foliation is measure equivalent to `|dv|`. Then
`log M_μ(|dv|) = log M(|dv|) + 2 Re (1/‖φ‖) ∬ μφ + o(‖μ‖∞)`. -/
theorem thm12_5 {g n : ℕ} (hR : IsFiniteAnalyticType R g n) (F : LiZhongQC.FiniteTypeStructure R g n 0)
    {ι : Type*} {U : ι → Set R} {v : ι → R → ℝ} {Sing : Set F.X.carrier} {k : F.X.carrier → ℤ}
    (hv : IsMeasuredFoliation F U v Sing k) {φ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R) (hφ0 : φ ≠ 0)
    (hφv : ∀ β : Loop R, IsEssentialLoop β → qdHeight φ β = folHeight U v β) :
    ∀ ε > 0, ∃ δ > 0, ∀ (Y : RSBundle.{u}) (f : R ≃ₜ Y.carrier) (μ : beltramiBall R), IsQCRS f →
      HasBeltramiCoeff f μ.1 → beltramiNormRS μ.1 < ENNReal.ofReal δ →
      |Real.log (dirichletMmu f U v).toReal - Real.log (dirichletM U v).toReal -
          2 * (pairingRS φ μ.1).re / (quadDiffNorm φ).toReal| ≤ ε * (beltramiNormRS μ.1).toReal := by
  sorry

/-- **Definition** (allowable curve, §12.7, l. 9281–9286). A simple closed curve `β` is allowable for `φ` if it is
(1) a regular closed vertical trajectory, (2) a vertical and a horizontal regular segment, or (3) four alternating
vertical and horizontal regular segments (see the module docstring). -/
def IsAllowableCurve (φ : R → ℂ → ℂ) (β : Loop R) : Prop :=
  IsSimpleLoop β ∧ ∃ (m : ℕ) (τ : Fin (m + 1) → ℝ), (m = 1 ∨ m = 2 ∨ m = 4) ∧ τ 0 = 0 ∧ τ (Fin.last m) = 1 ∧
    StrictMono τ ∧ ∀ i : Fin m,
      IsHorizontalArcRS (if (i : ℕ) % 2 = 0 then (fun x z => -φ x z) else φ)
        (β.2.truncate (τ i.castSucc) (τ i.succ))

/-- **Lemma 4** ((12.9), §12.7, l. 9287). Let `φ ∈ A(Ṙ)` (`Ṙ` compact up to finitely many punctures) and `ψ` a locally
`L¹` quadratic differential with `∫_γ |Im(√φ dz)| ≤ ∫_γ |√ψ dz|` for almost every allowable curve `γ` for `φ`. Then
`‖φ‖ ≤ ∬ |√φ √ψ| ≤ ∬ |ψ|`. -/
theorem lemma12_4 {g n : ℕ} (hR : IsFiniteAnalyticType R g n) {φ : R → ℂ → ℂ} (hφ : φ ∈ integrableHolQDSet R)
    {ψ : R → ℂ → ℂ} (hψ : IsDiffFamilyAE 2 0 ψ) (hψi : ∀ x : R, LocallyIntegrableOn (ψ x) (chartAt ℂ x).target)
    {N : Set R} (hN : IsNullSetRS N)
    (hcomp : ∀ β : Loop R, IsAllowableCurve φ β → β.1 ∉ N → imLengthLoop φ β ≤ phiLengthPath ψ β.2) :
    quadDiffNorm φ ≤ surfaceIntegral φ (fun x z => ENNReal.ofReal (Real.sqrt (‖ψ x z‖ / ‖φ x z‖))) ∧
      surfaceIntegral φ (fun x z => ENNReal.ofReal (Real.sqrt (‖ψ x z‖ / ‖φ x z‖))) ≤ quadDiffNorm ψ := by
  sorry

/-- **Lemma 5** (§12.7, l. 9330). With `K = (1 + ‖μ‖∞)/(1 − ‖μ‖∞)`, `K⁻¹ M_μ(|dv|) ≤ M(|dv|) ≤ K M_μ(|dv|)`. -/
theorem lemma12_5 {g n : ℕ} (hR : IsFiniteAnalyticType R g n) (F : LiZhongQC.FiniteTypeStructure R g n 0)
    {ι : Type*} {U : ι → Set R} {v : ι → R → ℝ} {Sing : Set F.X.carrier} {k : F.X.carrier → ℤ}
    (hv : IsMeasuredFoliation F U v Sing k) {Y : RSBundle.{u}} (f : R ≃ₜ Y.carrier) (hf : IsQCRS f)
    (μ : beltramiBall R) (hμ : HasBeltramiCoeff f μ.1) :
    let K := ENNReal.ofReal ((1 + (beltramiNormRS μ.1).toReal) / (1 - (beltramiNormRS μ.1).toReal))
    K⁻¹ * dirichletMmu f U v ≤ dirichletM U v ∧ dirichletM U v ≤ K * dirichletMmu f U v := by
  sorry

end GardinerLakic2000
