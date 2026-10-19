import References.GardinerLakic2000.Ch11.S03_WeylLemma

/-!
# Gardiner–Lakic 2000, Ch. 11 §11.4 Prescribing heights

Source `teichmuller.txt`, lines 8457–8586 (Chapter 11, §11.4).

* Theorem 3 (l. 8460) — `thm11_3`

Not items: (11.10) is the hypothesis of Theorem 3; (11.11)–(11.20) (proof: the variation `z + εh(z)` and the first
variation of the moduli). Modelling: the system `A′_j` of the hypothesis is read as a system of annuli compatible with
`{α_j}` (the proof takes the infimum of (11.10) over the compatible systems, i.e. (11.5)); "the annuli swept out by
the closed trajectories of `φ` are the annuli realizing the minimum" is: some compatible system attains the minimum,
and for every compatible system `A` attaining it there is `φ` with properties (a)–(e) whose ring domains are the
`A_j` (`HasJSProperties`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (Loop)

/-- **Theorem 3** (§11.4, l. 8460). Let `{α_j}` be an admissible system on `R`, `A′_j` compatible non-overlapping
annuli with moduli `m′_j`, and `b_j > 0` with `Σ_j b_j²/m′_j < ∞` (11.10). Then there is a holomorphic quadratic
differential `φ` with properties (a)–(e), and its ring domains are the annuli realizing the minimum.
[CORRECTION] (AUDITR2_GL614 R2-2) `[Nonempty ι]` is added: for the empty system `IsJSDecomp` would need the whole surface to
be a null set, so the statement is false. -/
theorem thm11_3 {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] {ι : Type*} [Countable ι] [Nonempty ι] {α : ι → Loop R} (hα : IsAdmissibleSystem α) {b : ι → ℝ}
    (hb : ∀ j, 0 < b j) {A' : ι → Set R} (hA' : IsCompatibleAnnuli α A') (hfin : annuliFunctional b A' < ⊤) :
    (∃ A : ι → Set R, IsCompatibleAnnuli α A ∧ annuliFunctional b A = annuliInf α b) ∧
      ∀ A : ι → Set R, IsCompatibleAnnuli α A → annuliFunctional b A = annuliInf α b →
        ∃ φ : R → ℂ → ℂ, HasJSProperties φ α b A := by
  sorry

end GardinerLakic2000
