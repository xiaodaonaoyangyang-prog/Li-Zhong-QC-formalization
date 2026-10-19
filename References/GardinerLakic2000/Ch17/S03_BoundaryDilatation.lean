import References.GardinerLakic2000.Ch17.S02_UnitDiscCase

/-!
# Gardiner–Lakic 2000, Ch. 17 §17.3 Boundary dilatation

Source `teichmuller.txt`, lines 12871–12914 (Chapter 17, §17.3).

* Formulas (17.6), (17.7) (the fundamental inequalities of Reich–Strebel, l. 12877–12882) — exists:
  `GardinerLakic2000.thm4_9_i` `GardinerLakic2000.thm4_9_ii` (batch B, Theorem 4.9)
* Definition (`g(τ)`, `G(τ)`, l. 12893–12900) — `gPlane`
* Theorem 2 (l. 12905) — `thm17_2`

Not items: `k₀(τ) = sup Re ∬ μ φ` for extremal `μ` (l. 12887, batch B's Chapter 4, U−); the remark on the local
approach (l. 12913). Modelling: as §17.1; `g` is defined for any coefficient (the book uses asymptotically extremal
representatives), and Theorem 2's "`G(τ)` is well defined" is the independence of the value from the asymptotically
extremal representative; `G = H` is `g = h`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (toExt)

/-- **Definition** (`g(τ)`, §17.3, l. 12897). `g = sup limsup Re ∬ μ φₙ` over degenerating sequences, for an
asymptotically extremal representative `μ` (`G = (1 + g)/(1 − g)`).
[CORRECTION] (AUDIT5_GL1518 G15-3) `⊔ 0`: the book's supremum is `0` over an empty family (no degenerating sequences,
e.g. `Ω = ℂ ∖ {0, 1}`); the `EReal` supremum would be `⊥`. Otherwise the value is unchanged, since the supremum is
`≥ 0` (rotate `φₙ`). -/
def gPlane (Ω : Set ℂ) (μ : ℂ → ℂ) : EReal :=
  (⨆ (φ : ℕ → ℂ → ℂ) (_ : IsDegeneratingSeqOpen (toExt Ω) φ),
    limsup (fun n => ((∫ z, μ z * φ n z).re : EReal)) atTop) ⊔ 0

/-- **Theorem 2** (§17.3, l. 12905). `G(τ)` is well defined and `G(τ) = H(τ)`: for asymptotically extremal
representatives `μ, ν` of the same class, `g` takes the same value, equal to `h(τ)`. -/
theorem thm17_2 {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsConnected Ω) (h2 : 2 ≤ (frontier Ω).encard) {μ ν : ℂ → ℂ}
    (hμ : IsAsymExtremalPlane Ω μ) (hν : IsAsymExtremalPlane Ω ν) (hμν : teichRelPlane Ω μ ν) :
    gPlane Ω μ = gPlane Ω ν ∧ gPlane Ω μ = ((hPlane Ω μ).toReal : EReal) := by
  sorry

end GardinerLakic2000
