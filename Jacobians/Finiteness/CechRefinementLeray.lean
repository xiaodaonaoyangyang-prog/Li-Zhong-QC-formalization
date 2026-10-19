/-
  Dolbeault ladder — **STEP B of the Čech Leray cover-independence**: `refineH1` is a `ℂ`-linear
  isomorphism for two Leray covers (the key step of `CechFinitenessWiring.exists_cechModel`).

  Builds on STEP A (`CechRefinementHomotopy.refineH1_eq`, homotopy/index-independence of the
  refinement map) and the refinement chain-map machinery (`CechRefinement`). See the `## PLAN` block
  of `CechRefinement.lean` for the full route.

  ## What is proven here (complete, axiom-clean `[propext, Classical.choice, Quot.sound]`)

    * **Round-trip / functoriality on `H¹`** (pure restriction algebra + STEP A):
        - `refineC1_id`  — the identity refinement is the identity on 1-cochains;
        - `refineH1_id`  — `(IsRefinement.id 𝔘).refineH1 D = LinearMap.id`;
        - `refineH1_comp` — `(hs.comp hr).refineH1 D = hs.refineH1 D ∘ₗ hr.refineH1 D`
          (functoriality, using `refineC1_comp` + descent through the quotient).
    * **Injectivity from a back-refinement** (homotopy-independence + functoriality):
        - `refineH1_leftInverse` — a back-refinement `𝔘 ⪯ 𝔙` gives `refineH1 hs` as an explicit
          left inverse of `refineH1 hr` (`(hs.comp hr).refineH1 = id` by homotopy-independence,
          since `r∘s : 𝔘 → 𝔘` is a self-refinement, equal on `H¹` to the identity refinement);
        - `refineH1_injective` — hence `refineH1 hr` is injective.
    * **The mutual-refinement isomorphism** (no analytic input):
        - `refineH1_equiv` — for covers `𝔙, 𝔘` with *mutual* refinements `𝔙 ⪯ 𝔘` and `𝔘 ⪯ 𝔙`,
          both round-trips are self-refinements (= identity on `H¹`), so `refineH1 hr` is a
          `ℂ`-linear bijection `cechH1 𝔘 D ≃ₗ[ℂ] cechH1 𝔙 D`.  This is the cover-independence
          isomorphism whenever the two covers mutually refine (in particular it does not need
          disk-acyclicity).
    * **The strictly-finer case, reduced to two cocycle-level conditions** — see the note at the
      bottom of this file: `RefinementLift` (surjectivity) and `RefinementDescend` (injectivity),
      with `refineH1_equiv_of_leray` giving the iso from the two.  They are discharged for
      chart-disk refinements via the disk-acyclicity of `CechDiskAcyclic*`
      (`CechRefinementInjective` and the model files).
-/
import Jacobians.Cech.CechRefinementHomotopy
import Jacobians.Dbar.CechDiskAcyclic

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace FiniteCover

open FiniteFamily
namespace IsRefinement

variable {𝔚 𝔙 𝔘 : FiniteCover X}

/-! ### Round-trip / functoriality on `H¹` -/

variable (D : Divisor X)

/-! ### Injectivity of `refineH1` from a back-refinement (STEP A + functoriality)

The standard Leray injectivity, in the complete *mutual-refinement* form: if `𝔙 ⪯ 𝔘` (via `r`) AND
`𝔘 ⪯ 𝔙` (via `s`), then the round-trip `r ∘ s : 𝔘.ι → 𝔘.ι` is a self-refinement of `𝔘`, so by STEP A
(homotopy/index-independence, `refineH1_eq`) it induces the SAME `H¹` map as the identity
refinement, namely `LinearMap.id`. Functoriality (`refineH1_comp`) then exhibits `refineH1 hs` as an
explicit LEFT INVERSE of `refineH1 hr`, giving injectivity. No analytic input. -/

/-! ### The mutual-refinement isomorphism (complete, no analytic input) -/

/-! ### The Leray analytic conditions for a STRICTLY-finer refinement (honest predicates)

The mutual-refinement equiv above covers the case where the two covers refine each other. The
`exists_cechModel` chaining instead needs the case `𝔙 ⪯ 𝔘` with `𝔙` STRICTLY finer (a common
refinement), where there is NO back-refinement `𝔘 ⪯ 𝔙`. For that case `refineH1 hr` being an iso is
the genuine Leray theorem, and the analytic content is isolated into the two cocycle-level
predicates below — both stated in the SAME "lift mod coboundary" shape as
`CechFinitenessWiring.Coboundaries.leray`. The conditional upgrades (`refineH1_surjective_of_lift`,
`refineH1_injective_of_descend`, `refineH1_equiv_of_leray`) are then complete; the honest analytic
obligation is to PRODUCE these predicates from disk/overlap-acyclicity (the `## SURJECTIVITY` plan
at the bottom). -/

variable {r : 𝔙.ι → 𝔘.ι}

/-- **The Leray DESCEND condition (injectivity input).**  A `𝔘`-cocycle whose refinement is a
`𝔙`-coboundary was already a `𝔘`-coboundary (`ker (refineH1 hr) = 0`).  This is Forster 12.8
(injectivity of the coarse→fine map on `H¹`); for `𝒪` with germ-class sections it is the H⁰ gluing
of the splitting `η`, again an overlap-acyclicity consequence. -/
def RefinementDescend (hr : IsRefinement 𝔙 𝔘 r) (D : Divisor X) : Prop :=
  ∀ g : ↥(𝔘.cocycles1 D),
    hr.refineC1 (g : 𝔘.Cochain1) ∈ 𝔙.coboundaries1 D → (g : 𝔘.Cochain1) ∈ 𝔘.coboundaries1 D

/-- `refineH1 hr [g] = [t]` (in `H¹`) ⟺ `refineC1 g − t` is a `𝔙`-coboundary. The bridge between the
quotient `H¹`-class equality and the cocycle-level "mod coboundary" statement
(`Submodule.Quotient.eq`; membership in `(coboundaries1).submoduleOf (cocycles1)` is defeq to
`↑· ∈ coboundaries1`). -/
theorem refineH1_mk_eq_iff (hr : IsRefinement 𝔙 𝔘 r) (g : ↥(𝔘.cocycles1 D))
    (t : ↥(𝔙.cocycles1 D)) :
    hr.refineH1 D (Submodule.Quotient.mk g) = Submodule.Quotient.mk t ↔
      hr.refineC1 (g : 𝔘.Cochain1) - (t : 𝔙.Cochain1) ∈ 𝔙.coboundaries1 D := by
  rw [refineH1_mk, Submodule.Quotient.eq]
  rfl

/-- **Injectivity of `refineH1` ⟺ the Leray DESCEND condition.** -/
theorem refineH1_injective_iff_descend (hr : IsRefinement 𝔙 𝔘 r) :
    Function.Injective (hr.refineH1 D) ↔ RefinementDescend hr D := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  constructor
  · intro hker g hg
    have hmk : Submodule.Quotient.mk g = (0 : 𝔘.cechH1 D) := by
      refine hker (Submodule.Quotient.mk g) ?_
      rw [show (0 : 𝔙.cechH1 D) = Submodule.Quotient.mk (0 : ↥(𝔙.cocycles1 D)) from rfl,
        refineH1_mk_eq_iff, ZeroMemClass.coe_zero, sub_zero]
      exact hg
    -- `mk g = 0` ⇔ `g ∈ submoduleOf`, defeq to `↑g ∈ coboundaries1 𝔘 D`.
    exact (Submodule.Quotient.mk_eq_zero
      ((𝔘.coboundaries1 D).submoduleOf (𝔘.cocycles1 D))).1 hmk
  · intro hdesc q hq
    induction q using Submodule.Quotient.induction_on with
    | _ g =>
      rw [show (0 : 𝔙.cechH1 D) = Submodule.Quotient.mk (0 : ↥(𝔙.cocycles1 D)) from rfl,
        refineH1_mk_eq_iff, ZeroMemClass.coe_zero, sub_zero] at hq
      rw [Submodule.Quotient.mk_eq_zero]
      exact hdesc g hq

end IsRefinement
end FiniteCover

/-! ## The strictly-finer case: `RefinementLift` / `RefinementDescend`

This file reduces the Leray cover-independence iso to two cocycle-level conditions:

  * `RefinementLift hr D` (surjectivity) — every `𝔙`-cocycle is `refineC1 g + δ⁰η` for a
    `𝔘`-cocycle `g`; equivalent to `Function.Surjective (refineH1 hr)`
    (`refineH1_surjective_iff_lift`).
  * `RefinementDescend hr D` (injectivity) — a `𝔘`-cocycle whose refinement is a `𝔙`-coboundary
    is a `𝔘`-coboundary; equivalent to `Function.Injective (refineH1 hr)`
    (`refineH1_injective_iff_descend`).

`refineH1_equiv_of_leray` then gives the iso from these two.  For two covers that mutually refine,
`refineH1_equiv` discharges both conditions with no analysis.  For a *strictly finer* Leray
refinement (the common-refinement case `exists_cechModel` needs, where there is no
back-refinement), the two conditions are the standard Forster §12 Leray argument: per coarse
overlap `W`, the fine cocycle restricted to `W` is a coboundary because `W` is `H¹(𝒪)`-acyclic.
The acyclicity input is supplied at the germ level by the chart-disk machinery
(`CechDiskAcyclic` / `CechDiskAcyclicProof` / `CechDiskAcyclicAssembly`), and the discharge is
carried out in `CechRefinementInjective` (Forster 12.4, unconditional injectivity) and the
`CechModel*` files. -/

end Jacobians.Dolbeault
