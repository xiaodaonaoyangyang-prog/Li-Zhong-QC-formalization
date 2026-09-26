import LiZhongQC.Ch02.S11_IntegralOperators
import LiZhongQC.Lemmas.HilbertInterpPair
import LiZhongQC.Lemmas.HilbertNormWiring

/-!
# §11.3 (continued): the norm `Λ_p` as a function of `p`

Theorem 11.2 (Riesz–Thorin: `ln Λ_p` convex in `1/p`), the continuity of `Λ_p` on `p > 1`, and
Theorem 11.3 Corollary 2 (`Λ_p → 1` as `p → 2`), relocated VERBATIM from `S11_IntegralOperators`
so that they can be proved from the interpolation leaves `Lemmas/HilbertInterp*` and
`Lemmas/HilbertNormWiring`, which import S11 and therefore cannot be used inside it. Statements
are unchanged. Each proof is the corresponding primed theorem of `HilbertNormWiring`; their only
remaining `sorryAx` source is `zygmund_calderon` (finiteness of `Λ_p` is the Calderón–Zygmund wall).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- **Theorem 11.2** (Riesz–Thorin): for `p > 1`, `ln Λ_p` is a convex function of `1/p`.
Proved by the three-lines interpolation of `Lemmas/HilbertInterpPair` (`hilbertH_boundedLp_interp_pair`);
modulo the Calderón–Zygmund wall only. -/
theorem thm11_2_riesz_thorin :
    ConvexOn ℝ (Ioo 0 1) (fun s : ℝ => Real.log (hilbertNorm (1 / s))) :=
  thm11_2_riesz_thorin'

/-- A consequence of Theorem 11.2: `Λ_p` is a continuous function of `p > 1`. -/
theorem hilbertNorm_continuousOn : ContinuousOn hilbertNorm (Ioi 1) :=
  hilbertNorm_continuousOn'

/-- **Theorem 11.3, Corollary 2**: `Λ_p → 1` as `p → 2`. -/
theorem thm11_3_cor2 : Tendsto hilbertNorm (𝓝 2) (𝓝 1) :=
  thm11_3_cor2'

end LiZhongQC
