import References.Katok1992.Ch03.S05_StructureOfDirichletRegion

/-!
# Katok 1992, Ch. 3 §3.6 Connection with Riemann surfaces and homogeneous spaces

S. Katok, *Fuchsian Groups* (1992), Chapter 3, §3.6; source `full.md` of `Fuchsian groups (Katok, Svetlana)
…-3766f6b7…`, lines 1705–1749.

* Unlabelled (the quotient `Γ\ℍ` of a finite-area Fuchsian group is an oriented surface with marked points, the
  homogeneous space `Γ\PSL(2, ℝ)`, `Γ\ℍ` is not a torus; l. 1707–1730) — omitted: topology of the quotient (no model of
  the orbifold structure); the signature of the quotient is `Katok1992.HasSignature` (Ch. 4 §4.3)
* Exercises 3.14, 3.15 (`SF` is a fundamental region in `Sℍ`) — omitted: exercises
* Theorem 3.6.1 (a compact set `K ⊂ Sℍ` with `Sℍ = Γ·K` makes `S F` compact; l. 1719) — `thm3_6_1`
* Corollary 3.6.2 (cocompactness from a compact `K1 ⊂ SL(2, ℝ)` with `SL(2, ℝ) = G1·K1`; l. 1748) — `cor3_6_2`

**Conventions.** The unit tangent bundle is `Katok1992.unitTangentBundle ⊆ ℍ × ℂ` (§2.1) with the action
`Katok1992.tangentMap`; `S F` is the set of unit tangent vectors with base point in `F`, for the Dirichlet region `F`
centred at a point `z₀` not fixed by a non-identity element of `Γ`. The quotient `Γ\ℍ` is the orbit space
`MulAction.orbitRel.Quotient Γ ℍ` with the quotient topology; `G1` is a subgroup of `SL(2, ℝ)` containing `−1` and
`Γ` its image in `PSL(2, ℝ)`.
-/

open Set
open scoped UpperHalfPlane MatrixGroups

noncomputable section

namespace Katok1992

/-- **Theorem 3.6.1** (§3.6; l. 1719). Suppose there exists a compact subset `K ⊂ Sℍ` such that every `(z, ζ) ∈ Sℍ` can be
written as `T(k, κ)` with `T ∈ Γ`, `(k, κ) ∈ K`. Then `S F = {(z, ζ) ∈ Sℍ | z ∈ F}` is compact, where `F = D_{z₀}(Γ)` is
a Dirichlet region for `Γ`. -/
theorem thm3_6_1 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {K : Set (ℍ × ℂ)} (hK : IsCompact K)
    (hKS : K ⊆ unitTangentBundle) (hcov : ∀ q ∈ unitTangentBundle, ∃ T ∈ Γ, ∃ k ∈ K, q = tangentMap T k) {z₀ : ℍ}
    (hz₀ : ∀ T ∈ Γ, T ≠ 1 → T • z₀ ≠ z₀) :
    IsCompact {q ∈ unitTangentBundle | q.1 ∈ dirichletRegion Γ z₀} := by
  sorry

/-- **Corollary 3.6.2** (§3.6; l. 1748). Suppose `G1` is a subgroup of `SL(2, ℝ)` containing `−1` with image `Γ` in
`PSL(2, ℝ)`. If there exists a compact subset `K1 ⊂ SL(2, ℝ)` such that `SL(2, ℝ) = G1 · K1`, then
`Γ\ℍ` is compact. (The book assumes `Γ` Fuchsian; the statement holds without this hypothesis, as `Γ\ℍ` is the
image of the compact set `K1 · i`.) -/
theorem cor3_6_2 {G1 : Subgroup SL(2, ℝ)} (h1 : (-1 : SL(2, ℝ)) ∈ G1)
    {K1 : Set SL(2, ℝ)} (hK : IsCompact K1)
    (hcov : ∀ g : SL(2, ℝ), ∃ γ ∈ G1, ∃ k ∈ K1, g = γ * k) :
    CompactSpace (MulAction.orbitRel.Quotient (G1.map (QuotientGroup.mk' (Subgroup.center SL(2, ℝ)))) ℍ) := by
  sorry

end Katok1992
