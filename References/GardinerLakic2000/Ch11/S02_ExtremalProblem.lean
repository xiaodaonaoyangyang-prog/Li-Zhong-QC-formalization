import References.GardinerLakic2000.Ch11.S01_AdmissibleSystems

/-!
# Gardiner–Lakic 2000, Ch. 11 §11.2 An extremal problem

Source `teichmuller.txt`, lines 8378–8410 (Chapter 11, §11.2); properties (a)–(e) from the chapter introduction,
lines 8322–8327.

* Definition 2 (system of annuli compatible with an admissible system, l. 8379) — `IsCompatibleAnnuli`
* Definition (modulus `(log R)/2π` of an annulus, l. 8389) — `annulusModulusRS`
* Formula (11.4) (`P{A_i} = Σ b_i²/m_i`, l. 8385) — `annuliFunctional`
* Formula (11.5) (`c = inf P{A_i}`, l. 8401) — `annuliInf`
* Properties (a)–(e) of the differential attached to `{α_j}` and heights `b_j` (introduction, l. 8322–8327; used in
  Theorems 3, 4) — `HasJSProperties`
* Theorem 1 (l. 8406) — `thm11_1`

Not items: (11.1) (the finiteness condition of the introduction, restated as (11.10) in Theorem 3); "there always is a
compatible system of annuli" (l. 8393, a remark); the bound `m_i ≤ π/ℓ(α_i)` (l. 8395, a step of the proof of
Theorem 1). Modelling: the core curve of `A_i = e({1 < |z| < r})` is the image of a circle `|z| = ρ`, `1 < ρ < r`;
the modulus is read through any such `e` (it does not depend on `e`); near miss `LiZhongQC.dcModulus` (plane domains,
`log(r₂/r₁)` without the factor `1/2π`). In (d) the height `b_j` of `A_j` in the metric `|φ|^{1/2}` is read through
`b_j² = m_j · ∬_{A_j} |φ|` (a flat cylinder of circumference `a_j` and height `b_j` has `m_j = b_j/a_j` and area
`a_j b_j`); (a) and (b) are read as: the ring domains `A_j` of `φ` fill `R` up to a null set (`IsJSDecomp`); (c): every
closed trajectory in `A_j` is freely homotopic to `α_j`; the differential is compared in the charts.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (Loop FreelyHomotopic quadDiffNorm)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition 2** (§11.2, l. 8379). The open annuli `A_i ⊆ R` are compatible with the admissible system `{α_i}`:
a core curve of `A_i` is homotopic to `α_i` and no two of the `A_i` overlap. -/
def IsCompatibleAnnuli {ι : Type*} (α : ι → Loop R) (A : ι → Set R) : Prop :=
  (∀ i, ∃ (r : ℝ) (e : ℂ → R), IsAnnulusMap (A i) r e ∧ ∃ ρ : ℝ, 1 < ρ ∧ ρ < r ∧ ∃ β : Loop R,
    (∀ t : unitInterval, β.2 t = e (ρ * exp (2 * π * I * (t : ℝ)))) ∧ FreelyHomotopic β (α i)) ∧
    Pairwise (fun i j => Disjoint (A i) (A j))

/-- **Definition** (§11.2, l. 8389). The modulus `(log r)/2π` of an annulus `A ⊆ R` conformal to
`{1 < |z| < r}`. -/
def annulusModulusRS (A : Set R) : ℝ :=
  sSup {m | ∃ (r : ℝ) (e : ℂ → R), IsAnnulusMap A r e ∧ m = Real.log r / (2 * π)}

/-- **Formula (11.4)** (§11.2, l. 8385). `P{A_i} = Σ_i b_i² / m_i`. -/
def annuliFunctional {ι : Type*} (b : ι → ℝ) (A : ι → Set R) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (b i ^ 2 / annulusModulusRS (A i))

/-- **Formula (11.5)** (§11.2, l. 8401). `c = inf P{A_i}` over the systems of annuli compatible with `{α_i}`. -/
def annuliInf {ι : Type*} (α : ι → Loop R) (b : ι → ℝ) : ℝ≥0∞ :=
  ⨅ (A : ι → Set R) (_ : IsCompatibleAnnuli α A), annuliFunctional b A

/-- **Properties (a)–(e)** (§11 introduction, l. 8322–8327). `φ ∈ A(R)`, the annuli `A_j` are the ring domains of `φ`
and fill `R` up to a null set ((a), (b)), every closed trajectory in `A_j` is homotopic to `α_j` (c), `A_j` has height
`b_j` in the metric `|φ|^{1/2}` (d), and `‖φ‖ = Σ_j ∬_{A_j} |φ| < ∞` (e).
[CORRECTION/modelling] (AUDITR3_GL45 R3-1) In (c) "homotopic" is unoriented: `IsHorizClosedTraj` is invariant under reversing
the loop, so the oriented clause `FreelyHomotopic β (α j)` could not hold for every trajectory `β` (and its reverse) in `A j`; (c)
reads `β ≃ α j` or `β ≃ (α j)⁻¹`. -/
def HasJSProperties {ι : Type*} (φ : R → ℂ → ℂ) (α : ι → Loop R) (b : ι → ℝ) (A : ι → Set R) : Prop :=
  IsJSDecomp φ A ∧
    (∀ j, ∀ β : Loop R, IsHorizClosedTraj φ β → range β.2 ⊆ A j →
      FreelyHomotopic β (α j) ∨ FreelyHomotopic β ⟨(α j).1, (α j).2.symm⟩) ∧
    (∀ j, b j ^ 2 = annulusModulusRS (A j) * (setIntegralQD φ (A j)).toReal) ∧
    quadDiffNorm φ = ∑' j, setIntegralQD φ (A j) ∧ quadDiffNorm φ < ⊤

/-- **Theorem 1** (§11.2, l. 8406). Let `b_i > 0` be constants for an admissible system `{α_i}` on `R`, and assume some
system of annuli compatible with `{α_i}` has `P{A_i} < ∞`. Then a compatible system attains the infimum (11.5). -/
theorem thm11_1 [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] {ι : Type*} [Countable ι] {α : ι → Loop R}
    (hα : IsAdmissibleSystem α) {b : ι → ℝ} (hb : ∀ i, 0 < b i)
    (hfin : ∃ A : ι → Set R, IsCompatibleAnnuli α A ∧ annuliFunctional b A < ⊤) :
    ∃ A : ι → Set R, IsCompatibleAnnuli α A ∧ annuliFunctional b A = annuliInf α b := by
  sorry

end GardinerLakic2000
