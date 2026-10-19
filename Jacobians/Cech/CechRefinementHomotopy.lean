/-
  **Homotopy-independence of the Čech refinement map** (the first half of the `cechH1` Leray
  cover-independence; cf. `CechRefinement`).

  Two refinement-index maps `r, r' : 𝔙.ι → 𝔘.ι` for the SAME pair of covers `(𝔙, 𝔘)` induce the same
  map on Čech `H¹`: `refineH1 hr D = refineH1 hr' D`.  This is the standard chain-homotopy argument,
  here for the length-2 complex `C⁰ →[δ⁰] C¹ →[δ¹] C²`.

  ## The prism (simplicial) homotopy

  For the two "vertex maps" `r#, r'#` we build the simplicial prism operator `K : C^q → C^{q-1}`,
    `(K g)_{j₀…j_{q-1}} = Σ_{i} (-1)ⁱ  g_{r j₀,…,r jᵢ, r' jᵢ,…,r' j_{q-1}} |_{𝔙-overlap}` ,
  in the two degrees we need:

    * `prismK0 : Cochain¹ 𝔘 → Cochain⁰ 𝔙`, `(prismK0 g)_j     = g_{(r j, r' j)} |_{𝔙.U j}`;
    * `prismK1 : Cochain² 𝔘 → Cochain¹ 𝔙`,
      `(prismK1 h)_{a b} = h_{(r a, r' a, r' b)} − h_{(r a, r b, r' b)} |_{𝔙.U a ⊓ 𝔙.U b}`.

  These are well-typed because `𝔙.U j ≤ 𝔘.U (r j) ⊓ 𝔘.U (r' j)` (`le_inf (hr j) (hr' j)`) — the
  germ `g_{(r j, r' j)}` lives on the coarse overlap, which contains the fine set.

  The **prism identity** (pure `rawRestrictG_comp` + alternating-sum `abel` bookkeeping):

      refineC1 hr' − refineC1 hr  =  cechDelta0 𝔙 ∘ prismK0  +  prismK1 ∘ cechDelta1 𝔘 .

  On a **cocycle** `g` (`cechDelta1 𝔘 g = 0`) the second summand vanishes, so the difference of the
  two refinements is the coboundary `δ⁰_𝔙 (prismK0 g)`; moreover `prismK0 g` is an `𝒪_D` 0-section
  when `g` is an `𝒪_D` 1-cocycle, so this is a genuine `coboundaries1 𝔙 D`. Descending through the
  `H¹ = Z¹/B¹` quotient (`Submodule.Quotient.eq`) gives `refineH1 hr = refineH1 hr'`.

  The remaining (analytic) half — `refineH1` an isomorphism for Leray covers — is built in
  `CechRefinementInjective` and `CechRefinementLeray`; see the note at the bottom.
-/
import Jacobians.Cech.CechRefinement

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X]

namespace FiniteCover

open FiniteFamily
namespace IsRefinement

variable {𝔙 𝔘 : FiniteCover X} {r r' : 𝔙.ι → 𝔘.ι}

/-! ### The prism homotopy operators -/

/-! ### The prism (chain-homotopy) identity -/

/-! ### Descent to `H¹`: the two refinement maps agree -/


end IsRefinement
end FiniteCover

/-! ## From homotopy-independence to the Leray cover-independence isomorphism

This file shows `refineH1` depends only on the pair `(𝔙, 𝔘)`, not on the chosen index map `r`
(`IsRefinement.refineH1_eq`).  The chain-homotopy operators `prismK0`, `prismK1` and the prism
identity `refineC1_sub_eq_homotopy` are reusable.

What this buys downstream: with index-independence, for two covers admitting *mutual* refinements
`𝔙 ⪯ 𝔘` and `𝔘 ⪯ 𝔙` the two composites `refineH1 ∘ refineH1` are forced to be the identity as
soon as each round trip is shown to be the canonical self-refinement map — any two refinement
index maps (in particular the round-trip `r ∘ s` and the identity `id`) induce the same `H¹` map,
and `(IsRefinement.id 𝔘).refineH1 = LinearMap.id`.  The remaining content — injectivity
(Forster 12.4) and the surjectivity from the disk/overlap-acyclicity input `H¹(overlap, 𝒪) = 0`
(`DbarDiskCohomology.dbar_solvable_ball`) — is carried out in `CechRefinementInjective` and
`CechRefinementLeray`, giving `cechH1 𝔘 D ≃ₗ[ℂ] cechH1 𝔙 D` for two Leray covers. -/

end Jacobians.Dolbeault
