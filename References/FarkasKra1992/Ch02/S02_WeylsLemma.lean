import References.FarkasKra1992.Ch02.S01_HilbertSpaceReview
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Farkas–Kra, Chapter II §2: Weyl's lemma

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. II §2 (`full.md` FK1:1393–1663).

Conventions: `D` is the unit disc `ball 0 1 ⊂ ℂ`; "harmonic" is Mathlib's `InnerProductSpace.HarmonicOnNhd`; the Laplacian is
`Laplacian.laplacian`; test functions `η` are real `C^∞` functions with compact support in `D`. As in the Remark
after the theorem, "`φ` is harmonic" means "equal almost everywhere to a harmonic function".

* Theorem II.2.1 (Weyl's lemma) — `thm2_2_1`
* II.2.2 (the Cauchy integral formula for a region bounded by finitely many `C¹` Jordan curves) — deferred: regions with piecewise differentiable boundary; the disc case is exists: `LiZhongQC.eq11_11_pompeiu`
* II.2.3 (the proof of Weyl's lemma, conclusion) — omitted: proof

Omitted (U−): the Exercises (the holomorphic form of Weyl's lemma, the one-dimensional analogue).
-/

open scoped Manifold ContDiff Topology
open Set Filter MeasureTheory Metric

noncomputable section

namespace FarkasKra1992

/-- **Weyl's lemma** (Ch. II §2.1, Theorem II.2.1). Let `φ` be a measurable square integrable function on the unit disc `D`.
The function `φ` is harmonic (a.e. equal to a harmonic function) if and only if `∬_D φ Δη = 0` for every `C^∞` function
`η` on `D` with compact support. -/
theorem thm2_2_1 {φ : ℂ → ℂ} (hm : AEStronglyMeasurable φ (volume.restrict (ball 0 1)))
    (h2 : MemLp φ 2 (volume.restrict (ball 0 1))) :
    (∃ h : ℂ → ℂ, InnerProductSpace.HarmonicOnNhd h (ball 0 1) ∧ φ =ᵐ[volume.restrict (ball 0 1)] h) ↔
      ∀ η : ℂ → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η → tsupport η ⊆ ball 0 1 →
        ∫ z in ball (0 : ℂ) 1, φ z * (Laplacian.laplacian η z : ℝ) = 0 := by
  sorry

end FarkasKra1992
