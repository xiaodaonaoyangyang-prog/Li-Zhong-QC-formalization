import LiZhongQC.Ch04.S16_Quasicircles
import References.Common.ExtendedPlane

/-!
# Shared layer: quasidisks of the extended plane

Registry: `refs_lean\FOUNDATIONS.md`, DESIGN §2 shared layer. First users: Astala–Gehring 1990; Lehto 1987.

* Shared notion (quasidisk of `ℂ̄`: a Jordan domain bounded by a quasicircle) — `IsQuasidiskExt`
-/

open Set

namespace References

open LiZhongQC

/-- A quasidisk of `ℂ̄`: a Jordan domain of `ℂ̄` (`References.IsJordanDomainExt`) whose boundary is a quasicircle
(`LiZhongQC.IsQuasicircle`). The project's `LiZhongQC.IsKQuasidisc` is this notion for plane domains. -/
def IsQuasidiskExt (U : Set ExtPlane) : Prop :=
  IsJordanDomainExt U ∧ IsQuasicircle (frontier U)

end References
