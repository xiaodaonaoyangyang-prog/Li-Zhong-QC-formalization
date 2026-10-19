import References.GardinerLakic2000.Ch17.S03_BoundaryDilatation

/-!
# Gardiner–Lakic 2000, Ch. 17 §17.4 Infinitesimally substantial points

Source `teichmuller.txt`, lines 12915–12976 (Chapter 17, §17.4).

* Theorem 3 (l. 12920) — `thm17_3`

Not items: the proof (the infinitesimal Sullivan–Thurston extension of the Appendix to Chapter 3). Modelling: as §17.1;
`Λ = ℂ ∖ Ω` contains at least three points (with `∞`: at least two finite points); "`max`" is an attained supremum over
the boundary `∂Ω` in `ℂ̂`: the frontier of `Ω` in `ℂ` and, for unbounded `Ω`, the point `∞`, where `b_∞(v)` is written
out with the neighbourhoods `{|z| > R}` of `∞` [CORRECTION, AUDIT5_GL1518 G15-4: with finite `p` only, Theorem 3 fails
when `∞` is the only point attaining `b(v)`, e.g. `Ω = ℍ` and the field `v(x) = 0` (`x ≤ 0`), `x` (`x ≥ 1`), smooth in
between, which is not in `Z₀` because of its corner at `∞`].
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (toExt)

/-- **Theorem 3** (§17.4, l. 12920). `b(v) = max_{p ∈ ∂Ω} b_p(v)` for all `v ∈ Z(Ω)`. -/
theorem thm17_3 {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsConnected Ω) (h3 : 2 ≤ Ωᶜ.encard) {V : (ℂ → ℂ) → ℂ}
    (hV : V ∈ zSpaceOpen (toExt Ω)) :
    ((∃ p ∈ frontier Ω, bp Ω p V = bPlane Ω V) ∨
        (¬ Bornology.IsBounded Ω ∧
          (⨅ (μ : ℂ → ℂ) (_ : RepresentsPlane Ω μ V) (R : ℝ), eLpNorm μ ⊤ (volume.restrict (Ω ∩ {z | R < ‖z‖}))) = bPlane Ω V)) ∧
      ∀ q ∈ frontier Ω, bp Ω q V ≤ bPlane Ω V := by
  sorry

end GardinerLakic2000
