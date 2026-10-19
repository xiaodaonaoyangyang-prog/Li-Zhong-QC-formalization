/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.MappingDegree.ClopennessOfLocallyConstDischarge


/-! # Fibres of a non-constant analytic map are finite

`clopennessOfLocallyConst_holds` closed
`ClopennessOfLocallyConstHypothesis` unconditionally;
`fibres_finite_statement_holds_of_clopennessOfLocallyConst` reduced
`fibres_finite_statement` to that hypothesis. Composing the two gives the
first `Degree` statement with no remaining hypotheses. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-- **Every fibre of a non-constant analytic map between compact connected
complex 1-manifolds is finite** (`fibres_finite_statement`, with no
remaining hypotheses). Direct composition of
`fibres_finite_statement_holds_of_clopennessOfLocallyConst` with
`clopennessOfLocallyConst_holds`. -/
theorem fibres_finite
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f →
        ∀ y : Y, (f ⁻¹' {y}).Finite :=
  fibres_finite_statement_holds_of_clopennessOfLocallyConst
    clopennessOfLocallyConst_holds

end Degree
end ContMDiff
end Jacobians.Discharge
