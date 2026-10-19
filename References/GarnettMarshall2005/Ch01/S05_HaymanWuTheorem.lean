import References.GarnettMarshall2005.Ch01.S04_DistortionHyperbolicMetric

/-!
# Garnett–Marshall, Chapter I §5: The Hayman–Wu theorem

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. I §5 (pp. 23–25;
`full.md` P1:1180–1275).

Conventions as in §4 (planar domains, `LiZhongQC.IsConformalOnto`, simply connected domains as
`LehtoVirtanen1973.IsSimplyConnectedDomain` of the image in `ℂ*`). The length of a plane set is its one-dimensional
Hausdorff measure `μH[1]` (arc length on rectifiable curves, with values in `[0, ∞]`), not the book's `Λ₁` of
Appendix D, which is half of it. A line of `ℂ` is `line[ℝ, a, b]`, the real affine span of two distinct points.

* Definition (the length of a subset of the plane, (5.1), §5) — exists: `MeasureTheory.Measure.hausdorffMeasure`
  (the one-dimensional Hausdorff measure of the plane, which is arc length on rectifiable curves and on countable
  unions of arcs; the book's Λ₁ of Appendix D is half of it)
* Theorem 5.1 (Hayman–Wu, §5) — `thm1_5_1`
* Definition (the pseudohyperbolic metrics `δ_𝔻(z₁, z₂) = |(z₁ − z₂)/(1 − z̄₁z₂)|` and `δ_Ω`, §5, P1:1192–1202) —
  omitted: introduced for the proof of Theorem 5.1 only ("for the proof it will be convenient"); the later notation
  δ_Ω of Ch. V §3 is the reduced extremal distance, a different notion

Not stated (inventory U−): the history of the constant in (5.1) (P1:1190); (5.2) and (5.3), steps of the proof of
Theorem 5.1; the remark that the conclusion of Theorem 5.1 is stronger than (5.1) because it does not depend on `φ`
(P1:1266, Exercise 20); the preview (5.4) of Ch. VII (`∫_{L∩Ω} |(φ⁻¹)'(w)|^p |dw| < C_p` for some `1 < p < 2`,
P1:1268–1274), whose statement lives in Ch. VII, and the remark that the largest such `p` is unknown (an open
problem).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (toExt unitDisc IsConformalOnto)
open LehtoVirtanen1973 (IsSimplyConnectedDomain)

/-- **Theorem 5.1** (Hayman–Wu; Ch. I §5; cited throughout the book; the mention in Ch. III, P1:5661, is in an
exercise). Let `φ` be a
conformal mapping from `𝔻` to a simply connected domain `Ω` and let `L` be any line. Then (5.1)
`length(φ⁻¹(L ∩ Ω)) ≤ 4π`.
Modelling: `φ` maps `𝔻` onto the plane domain `Ω`; `L = line[ℝ, a, b]` with `a ≠ b` is an arbitrary line of `ℂ`;
`φ⁻¹(L ∩ Ω)` is the preimage in `𝔻`, and its length is the one-dimensional Hausdorff measure `μH[1]`, compared with
`4π` in `[0, ∞]`. The constant `4π` was checked against the equation image. -/
theorem thm1_5_1 {Ω : Set ℂ} (hΩ : IsSimplyConnectedDomain (toExt Ω)) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ unitDisc Ω) {a b : ℂ} (hab : a ≠ b) :
    μH[1] (unitDisc ∩ φ ⁻¹' ((line[ℝ, a, b] : Set ℂ) ∩ Ω)) ≤ ENNReal.ofReal (4 * π) := by
  sorry

end GarnettMarshall2005
