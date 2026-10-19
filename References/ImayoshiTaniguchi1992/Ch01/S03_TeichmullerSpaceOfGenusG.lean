import References.ImayoshiTaniguchi1992.Ch01.S02_TeichmullerSpaceOfGenusOne

/-!
# Imayoshi–Taniguchi, Chapter 1 §1.3: Teichmüller space of genus `g`

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 1 §1.3 (`full.md` IT1:453–500,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions as in `Ch01/S02_TeichmullerSpaceOfGenusOne`: `T_g` is the set of marked closed surfaces `(S, Σ)` modulo
`MarkedEquiv`, `T(R)` the set of classes `[S, f]` of pairs of a closed surface and an orientation-preserving (quasiconformal)
homeomorphism `f : R → S` with `(S₁, f₁) ~ (S₂, f₂)` iff `f₂ ∘ f₁⁻¹` is homotopic to a biholomorphic map, i.e. `f₁ ≫ h ≃ f₂` for
a biholomorphic `h` (this is `LiZhongQC.MarkedRS.Equiv`, `LiZhongQC.TeichSpace`). The map `Φ_Σ : T(R) → T_g`, `[S, f] ↦ [S, f_*(Σ)]`,
is stated as a bijection by its two halves: well defined and injective (`thm1_4_a`), surjective (`thm1_4_b`).

* Definition (marked Riemann surface, `T_g`, `T(R)`, `Φ_Σ`, IT1:456) — exists: `LiZhongQC.TeichSpace`,
  `LiZhongQC.MarkedRS.Equiv`
* Theorem 1.4 (`Φ_Σ : T(R) → T_g` is bijective; well defined and injective, IT1:470) — `thm1_4_a`
* Theorem 1.4 (surjectivity, IT1:470) — `thm1_4_b`
-/

open Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (IsQCRS IsBiholomorphic HasGenus)

variable {R S S' : Type} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R]
  [CompactSpace R] [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
  [CompactSpace S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S'] [ChartedSpace ℂ S'] [IsManifold 𝓘(ℂ) ω S']
  [CompactSpace S']

/-- **Theorem 1.4, well definedness and injectivity** (Ch. 1 §1.3). Let `R` be a closed surface of genus `g ≥ 2`, `Σ` a canonical
system of generators of `π₁(R, p)`, and `f : R → S`, `g : R → S'` orientation-preserving (quasiconformal) homeomorphisms onto
closed surfaces. Then `[S, f] = [S', g]` in `T(R)` (that is, `g ∘ f⁻¹` is homotopic to a biholomorphic map) if and only if
`[S, f_*(Σ)] = [S', g_*(Σ)]` in `T_g`. -/
theorem thm1_4_a {n : ℕ} (hn : 2 ≤ n) (hR : HasGenus R n) (hS : HasGenus S n) (hS' : HasGenus S' n) {p : R}
    {a b : Fin n → FundamentalGroup R p} (hcan : IsCanonicalSystem n a b) (f : R ≃ₜ S) (g : R ≃ₜ S') (hf : IsQCRS f)
    (hg : IsQCRS g) :
    (∃ h : S ≃ₜ S', IsBiholomorphic h ∧
        ContinuousMap.Homotopic ((f.trans h : R ≃ₜ S') : C(R, S')) (g : C(R, S'))) ↔
      MarkedEquiv n (fun j => FundamentalGroup.map (f : C(R, S)) p (a j)) (fun j => FundamentalGroup.map (f : C(R, S)) p (b j))
        (fun j => FundamentalGroup.map (g : C(R, S')) p (a j)) (fun j => FundamentalGroup.map (g : C(R, S')) p (b j)) := by
  sorry

/-- **Theorem 1.4, surjectivity** (Ch. 1 §1.3). Let `R` be a closed surface of genus `g ≥ 2` with a canonical system `Σ` of
generators of `π₁(R, p)`. For every closed surface `S` of genus `g` and every canonical system `Σ'` of generators of `π₁(S, p')`
there is an orientation-preserving (quasiconformal) homeomorphism `f : R → S` such that `Σ'` is equivalent to `f_*(Σ)`, that is,
`T_C ∘ f_*` carries `Σ` to `Σ'` for a curve `C` from `f(p)` to `p'`. -/
theorem thm1_4_b {n : ℕ} (hn : 2 ≤ n) (hR : HasGenus R n) (hS : HasGenus S n) {p : R} {a b : Fin n → FundamentalGroup R p}
    (hcan : IsCanonicalSystem n a b) {p' : S} {a' b' : Fin n → FundamentalGroup S p'} (hcan2 : IsCanonicalSystem n a' b') :
    ∃ f : R ≃ₜ S, IsQCRS f ∧ ∃ C : Path (f p) p', ∀ j : Fin n,
      FundamentalGroup.fundamentalGroupMulEquivOfPath C (FundamentalGroup.map (f : C(R, S)) p (a j)) = a' j ∧
        FundamentalGroup.fundamentalGroupMulEquivOfPath C (FundamentalGroup.map (f : C(R, S)) p (b j)) = b' j := by
  sorry

end ImayoshiTaniguchi1992
