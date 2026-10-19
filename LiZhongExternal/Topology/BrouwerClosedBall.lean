/-
Brouwer closed-ball adapter, 2026-10-14.
The imported fixed-point proof is MIT-licensed; see ../Harfe/LICENSE.harfe.
-/
import LiZhongExternal.Harfe.Brouwer

namespace LiZhongExternal.Topology

/-- Every continuous self-map of a finite-dimensional real closed unit ball has a fixed point. -/
theorem brouwer_closedBall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : Metric.closedBall (0 : E) 1 → Metric.closedBall (0 : E) 1)
    (hf : Continuous f) : ∃ x, f x = x := by
  exact Harfe.brouwer_fixed_point (Metric.closedBall (0 : E) 1)
    (convex_closedBall 0 1) (isCompact_closedBall 0 1)
    ⟨0, by simp⟩ ⟨f, hf⟩

end LiZhongExternal.Topology
