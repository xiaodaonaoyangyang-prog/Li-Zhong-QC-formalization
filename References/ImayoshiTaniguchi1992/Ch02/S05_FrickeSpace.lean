import References.ImayoshiTaniguchi1992.Ch02.S04_FuchsianGroups

/-!
# Imayoshi–Taniguchi, Chapter 2 §2.5: Fricke space (W2 batch I2)

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 2 §2.5 (`full.md` IT1:1400–1521,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions as in `Ch02/S04_FuchsianGroups` and `Ch03/S02_FenchelNielsen`: the canonical system of generators `{α_j, β_j}_{j=1}^g` of the
normalized Fuchsian model `Γ` of a marked closed surface of genus `g ≥ 2` is `LiZhongQC.StandardGenerators Γ g`: the pairs `(α_j, β_j)`,
`j ≤ g − 1`, are `G.first j`, and `α_g = G.γg`, `β_g = G.δg`, with the normalization `β_g(z) = λ z` (`λ > 1`), `α_g(1) = 1`.
A Fuchsian model of a closed surface is a Fuchsian group acting freely and cocompactly.

* Normalization conditions, Proposition 2.23 (the canonical system of the normalized model is determined by `[R, Σ]`) — exists:
  `LiZhongQC.exists_inducedGenerators`
* Lemma 2.24 (`bc ≠ 0` for the generators other than `β_g`) — `lem2_24`
* Theorem 2.25 (the Fricke coordinates are injective on `T_g`) — exists: `LiZhongQC.thm27_fricke_bijection`
-/

open Complex Set Metric Filter Topology
open scoped MatrixGroups

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (IsFuchsian ActsFreely IsCocompact StandardGenerators IsUniformization HasGenus)

/-- **Lemma 2.24** (Ch. 2 §2.5, IT1:1432). Let `{α_j, β_j}_{j=1}^g` be the canonical system of generators of the normalized Fuchsian model
`Γ` for a point `[R, Σ]` in `T_g`. If an element `γ(z) = (az + b)/(cz + d)` of `{α_j, β_j}` does not coincide with `β_g`, then `bc ≠ 0`.
**Correction** (IT-fix3, AUDITR2_IT R2-IT-03): the genus of the uniformized surface `S = ℍ/Γ` must be `g`; otherwise a padded inner pair
`(1, 1)` (`g = 3` on a genus-2 group, `first = ![(α₂, β₂), (1, 1)]`, `γg = α₁`, `δg = β₁`) satisfies every field of `StandardGenerators`
and `bc = 0`. The second conjunct is the field `G.alternate`. -/
theorem lem2_24 {Γ : Subgroup SL(2, ℝ)} {g : ℕ} (hg : 1 < g) {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S]
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) (hS : HasGenus S g) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hc : IsCocompact Γ) (G : StandardGenerators Γ g) :
    (∀ j, (G.first j).1 0 1 * (G.first j).1 1 0 ≠ 0 ∧ (G.first j).2 0 1 * (G.first j).2 1 0 ≠ 0) ∧ G.γg 0 1 * G.γg 1 0 ≠ 0 := by
  sorry

end ImayoshiTaniguchi1992
