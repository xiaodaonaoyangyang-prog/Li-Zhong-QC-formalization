import LiZhongQC.Basic

/-!
# Shared layer: basic notions for domains of the extended plane

Notions of the extended plane `ℂ̄ = LiZhongQC.ExtPlane` that several works use and that belong to no single work's
conventions (DESIGN §2, shared layer; registry `refs_lean\FOUNDATIONS.md`). The project's own notions
(`LiZhongQC.IsJordanDomain`, …) are for plane domains `D ⊆ ℂ` only.

* Shared notion (domain of `ℂ̄`: open and connected; Gehring 1978 §1, LV I.1) — `IsDomainExt`
* Shared notion (Jordan domain of `ℂ̄`; Gehring 1978 §1, LV I.1.4) — `IsJordanDomainExt`
* Shared notion (finite part `D ∩ ℂ` of a set `D ⊆ ℂ̄`; Gehring 1978 §1) — `finitePart`
-/

open Set

namespace References

open LiZhongQC

/-- A domain of `ℂ̄`: an open connected subset of the extended plane. -/
def IsDomainExt (G : Set ExtPlane) : Prop :=
  IsOpen G ∧ IsConnected G

/-- A Jordan domain of `ℂ̄`: a domain `U ⊆ ℂ̄` whose boundary is a Jordan curve. It is then a complementary component
of that curve. The project's `LiZhongQC.IsJordanDomain` is this notion for plane domains. -/
def IsJordanDomainExt (U : Set ExtPlane) : Prop :=
  IsDomainExt U ∧ IsJordanCurve (frontier U)

/-- The finite part `D ∩ ℂ` of a set `D ⊆ ℂ̄`, as a subset of `ℂ`. -/
def finitePart (D : Set ExtPlane) : Set ℂ :=
  ((↑) : ℂ → ExtPlane) ⁻¹' D

end References
