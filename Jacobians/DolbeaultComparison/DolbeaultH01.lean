/-
  The intrinsic `∂̄` as a linear map — the first layer of the Dolbeault `H^{0,1}` comparison.

  `RealForms.dbar : A⁰ → A¹` is a bare function; `A⁰ = SmoothCFunctions` and
  `A¹ = SmoothCOneForms` already carry `AddCommGroup` + `Module ℝ`.  This file proves `dbar`
  additive (via `mfderiv_add`) and ℝ-homogeneous (via `const_smul_mfderiv`) and packages it as
  the ℝ-linear map `dbarL : A⁰ →ₗ[ℝ] A¹`, whose range is the coboundary space of `H^{0,1}`.

  The space `DolbeaultH01` itself and the comparison with Čech `H¹(X, 𝒪)` are built in
  `DolbeaultComparison` / `DolbeaultComparisonEquiv`.
-/
import Jacobians.Dbar.RealForms

open scoped Manifold ContDiff

-- The `SmoothCOneForms` hom-bundle `TopologicalSpace`/`DFunLike` instances synthesize only under
-- the permissive transparency option `RealForms` itself uses (the ℂ-ℝ-module diamond); without it
-- the section `ext`/`coe_injective` lemmas fail to find `TopologicalSpace (TotalSpace …)`.
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- `∂̄` is additive (`differential` is additive via `mfderiv_add`; `proj01` is linear). -/
theorem dbar_add (u v : SmoothCFunctions X) : dbar (u + v) = dbar u + dbar v := by
  refine ContMDiffSection.ext fun x => ?_
  have hu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x := (u.contMDiff x).mdifferentiableAt (by simp)
  have hv : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑v) x := (v.contMDiff x).mdifferentiableAt (by simp)
  simp only [ContMDiffSection.coe_add, Pi.add_apply]
  show proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(u + v)) x)
      = proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x) + proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑v) x)
  rw [show (⇑(u + v) : X → ℂ) = ⇑u + ⇑v from rfl, mfderiv_add hu hv, map_add]

/-- `∂̄` is ℝ-homogeneous (`const_smul_mfderiv`; `proj01` is linear). -/
theorem dbar_smul (c : ℝ) (u : SmoothCFunctions X) : dbar (c • u) = c • dbar u := by
  refine ContMDiffSection.ext fun x => ?_
  have hu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x := (u.contMDiff x).mdifferentiableAt (by simp)
  simp only [ContMDiffSection.coe_smul, Pi.smul_apply]
  show proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(c • u)) x)
      = c • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x)
  rw [show (⇑(c • u) : X → ℂ) = c • ⇑u from rfl, const_smul_mfderiv hu, map_smul]

/-- The intrinsic ∂̄ operator as an ℝ-linear map `A⁰ →ₗ[ℝ] A¹` (upgrade of the bare `dbar`), so that
`LinearMap.range dbarL` — the image needed to form `H^{0,1}` — is available. -/
noncomputable def dbarL : SmoothCFunctions X →ₗ[ℝ] SmoothCOneForms X where
  toFun := dbar
  map_add' := dbar_add
  map_smul' c u := dbar_smul c u

@[simp] theorem dbarL_apply (u : SmoothCFunctions X) : dbarL u = dbar u := rfl

end Jacobians.Dolbeault
