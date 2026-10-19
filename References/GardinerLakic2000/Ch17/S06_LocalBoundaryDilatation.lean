import References.GardinerLakic2000.Ch17.S05_LocalBoundarySeminorms

/-!
# Gardiner–Lakic 2000, Ch. 17 §17.6 Local boundary dilatation

Source `teichmuller.txt`, lines 13026–13083 (Chapter 17, §17.6).

* Definition (`g_p(τ)`, `G_p`, l. 13028–13039) — `IsGpValue`
* Theorem 5 (l. 13043) — `thm17_5`
* Lemma 1 (l. 13051) — `lemma17_1`

Not items: the proofs; "`h(τ) = sup_p g_p(τ)`" (l. 13082, it is Corollary 17.1 with Theorem 5). Modelling: `g_p` is a
limit over a choice of representatives `μ_k` with `h*_p(μ_k) < h_p(τ) + 1/k`; to keep choices out of the definition,
`IsGpValue Ω p μ g` says that this limit is `g` for every such choice (Theorem 5's "`g_p` exists" is that some, hence
the, value exists). The printed "`se ∫`" (l. 13030) is `Re ∫` [OCR]. `H*_p = (1 + h*_p)/(1 − h*_p)`,
`H_p = (1 + h_p)/(1 − h_p)` are written out.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

/-- **Definition** (`g_p(τ)`, §17.6, l. 13028). For every choice of representatives `μ_k` of the class of `μ` with
`h*_p(μ_k) < h_p(τ) + 1/k`, `sup_{φₙ → p} limsup Re ∬ μ_k φₙ` tends to `g` as `k → ∞`.
[CORRECTION] (AUDIT5_GL1518 G15-3) The supremum is taken `⊔ 0`: no sequence degenerates toward an isolated point of
`Ωᶜ` (nor any at all when `A(Ω)` is finite dimensional), and the book's supremum is then `0`, not `⊥`. -/
def IsGpValue (Ω : Set ℂ) (p : ℂ) (μ : ℂ → ℂ) (g : EReal) : Prop :=
  ∀ μk : ℕ → ℂ → ℂ, (∀ k, μk k ∈ beltramiPlane Ω ∧ teichRelPlane Ω μ (μk k) ∧
      hpStar Ω p (μk k) < hp Ω p μ + 1 / ((k : ℝ≥0∞) + 1)) →
    Tendsto (fun k => (⨆ (φ : ℕ → ℂ → ℂ) (_ : IsDegTowardSeq Ω p φ),
      limsup (fun n => ((∫ z, μk k z * φ n z).re : EReal)) atTop) ⊔ 0) atTop (𝓝 g)

/-- **Theorem 5** (§17.6, l. 13043). `g_p(τ)` exists for every `τ ∈ T(Ω)` and `g_p(τ) = h_p(τ)`. -/
theorem thm17_5 {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsConnected Ω) (h3 : 2 ≤ Ωᶜ.encard) {μ : ℂ → ℂ}
    (hμ : μ ∈ beltramiPlane Ω) {p : ℂ} (hp' : p ∈ frontier Ω) : IsGpValue Ω p μ ((hp Ω p μ).toReal : EReal) := by
  sorry

/-- **Lemma 1** (§17.6, l. 13051). `b*_p(μ) − β_p(v) ≤ H*_p(μ) − H_p(τ)` for `v` the functional of `μ`. -/
theorem lemma17_1 {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsConnected Ω) (h3 : 2 ≤ Ωᶜ.encard) {μ : ℂ → ℂ}
    (hμ : μ ∈ beltramiPlane Ω) {p : ℂ} (hp' : p ∈ frontier Ω) :
    (hpStar Ω p μ).toReal - (betaP Ω p fun φ => ∫ z, μ z * φ z).toReal ≤
      (1 + (hpStar Ω p μ).toReal) / (1 - (hpStar Ω p μ).toReal) -
        (1 + (hp Ω p μ).toReal) / (1 - (hp Ω p μ).toReal) := by
  sorry

end GardinerLakic2000
