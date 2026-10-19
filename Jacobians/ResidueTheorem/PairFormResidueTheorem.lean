/-
  THE PAIR-FORM RESIDUE: definition and ω₀-factorization bridge (Miranda Ch. VI pp. 186–188).

  A meromorphic 1-form on the compact Riemann surface `X` is represented as a PAIR `(g₀, h)` of
  meromorphic functions meaning `h·dg₀` (no new form type).  Its residue at `a` is computed in the
  canonical chart: `pairFormResidue g₀ h a = Res_{chart a}((h∘chart⁻¹)·(g₀∘chart⁻¹)′)`.

  This file provides:
  * `pairFormResidue` — the pair-form residue at a point;
  * `pairFormResidue_eq_zero_of_analyticAt` — `Res(holo) = 0` for pair-forms;
  * `pairFormResidue_eq_formFnResidue` — the LOCAL IDENTITY: for any `ω₀ ≠ 0` and
    `q := dg₀/ω₀` (`derivQuotientFn`, `Jacobians/ResidueTheorem/OmegaFactorization.lean`), at EVERY
    point `pairFormResidue g₀ h a = formFnResidue ω₀ ((h·q).toFun) a` — germ equality off the
    centre (chart-coherence of `q` + isolated zeros of `coeffAt ω₀ a`) + `resAt_congr`.

  The residue THEOREM `∑ pairFormResidue = 0` itself lives in
  `Jacobians/ResidueTheorem/ResidueTheoremStokes.lean`
  (`StokesResidue.residueSum_pairForm_eq_zero_unconditional`), proven by the self-contained
  planar-Stokes ledger.  Everything here is complete and depends on no unproved lemma.
-/
import Jacobians.ResidueTheorem.OmegaFactorization

open scoped Manifold ContDiff Topology
open Filter


namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **The residue of the meromorphic pair-form `h·dg₀` at `a`**, computed in the canonical chart:
the `resAt` of `(h ∘ chart⁻¹)·(g₀ ∘ chart⁻¹)′` at the chart image of `a` (Miranda Ch. VI p. 186:
residues of `f·dg` are chart-independent, so the canonical chart pins the value). -/
noncomputable def pairFormResidue (g₀ h : MeromorphicFunction X) (a : X) : ℂ :=
  resAt (fun z => h.toFun ((chartAt (H := ℂ) a).symm z)
    * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) a).symm w)) z) ((chartAt (H := ℂ) a) a)

/-- **`Res(holo) = 0` for pair-forms**: if the pair integrand is analytic at the chart centre
(no pole of `h·dg₀` at `a`), the residue vanishes. -/
theorem pairFormResidue_eq_zero_of_analyticAt (g₀ h : MeromorphicFunction X) (a : X)
    (ha : AnalyticAt ℂ (fun z => h.toFun ((chartAt (H := ℂ) a).symm z)
      * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) a).symm w)) z) ((chartAt (H := ℂ) a) a)) :
    pairFormResidue g₀ h a = 0 :=
  resAt_eq_zero_of_analyticAt ha

/-- **The local identity `Res_a(h·dg₀) = Res_a((h·q)·ω₀)`** for `q = dg₀/ω₀` — at EVERY point `a`
(no exceptional set!): near the chart centre (off it), `q`'s pullback is the single-chart quotient
(`derivQuotient_eventuallyEq_chart`) and `coeffAt ω₀ a ≠ 0` (isolated zeros, `ω₀ ≠ 0`), so the
`coeffAt` factor cancels and the two `resAt` integrands agree as germs (`resAt_congr`). -/
theorem pairFormResidue_eq_formFnResidue [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0)
    (g₀ h : MeromorphicFunction X) (a : X) :
    pairFormResidue g₀ h a = formFnResidue ω₀ ((h * derivQuotientFn ω₀ g₀).toFun) a := by
  refine resAt_congr ?_
  have hcoh := derivQuotient_eventuallyEq_chart ω₀ g₀ a
  have hne := coeffAt_eventually_ne_zero ω₀ hω₀ a
  filter_upwards [hcoh, hne] with z hq hC
  simp only [MeromorphicFunction.mul_toFun, Pi.mul_apply, derivQuotientFn_toFun]
  rw [hq]
  set H := h.toFun ((chartAt (H := ℂ) a).symm z) with hH
  set D := deriv (fun w => g₀.toFun ((chartAt (H := ℂ) a).symm w)) z with hD
  set C := coeffAt ω₀ a z with hCdef
  -- `H·D = C·(H·(D/C))` with `C ≠ 0`
  rw [mul_left_comm C H (D / C), mul_div_cancel₀ D hC]

end Jacobians.Dolbeault
