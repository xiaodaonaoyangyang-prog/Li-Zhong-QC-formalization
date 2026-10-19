import References.Pommerenke1992.Ch02.S03_CutPointsAndJordanDomains
import References.Pommerenke1992.Ch02.S05_LimitsAndClusterSets

/-!
# Pommerenke 1992, Ch. 2 §2.1 An Overview

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §2.1; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 970–1000.

* Continuity Theorem (§2.1) — `continuity_theorem`
* Carathéodory Theorem (§2.1) — `caratheodory_theorem`
* Prime End Theorem (§2.1) — `prime_end_theorem`

**Import order (an exception, approved by the leader 2026-09-28).** The overview states, for domains of `Ĉ`, three
named theorems whose notions are defined later in the chapter (local connectedness in §2.2, prime ends and
impressions in §2.4–2.5). This file therefore imports the files of §2.3 and §2.5; the import graph stays acyclic, as
no other file imports this one.

Not items (DESIGN §3): the notation (2.1.1) for the unrestricted limit (that of (1.2.12)); the informal description of
local connection (defined in §2.2); the preview of §2.6 (l. 1000).

**Conventions.** `f` maps `𝔻` conformally onto `G ⊆ Ĉ` (`LehtoVirtanen1973.IsConformalMap f (toExt 𝔻)`, `f(𝔻) = G`);
continuity at `𝕋` is in the spherical metric, that is in the topology of `Ĉ`; local connection is the spherical
form `IsLocConnSph` of (2.2.1).
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane toExt unitDisc IsJordanCurve)
open LehtoVirtanen1973 (IsConformalMap)

/-- **Continuity Theorem** (§2.1). The conformal map `f` of `𝔻` onto `G ⊆ Ĉ` has a continuous extension to `𝔻 ∪ 𝕋` if
and only if `∂G` is locally connected. (Theorem 2.1 is the case of bounded `G`.) -/
theorem continuity_theorem {G : Set ExtPlane} {f : ExtPlane → ExtPlane} (hf : IsConformalMap f (toExt unitDisc))
    (hfG : f '' toExt unitDisc = G) :
    (∃ F : ExtPlane → ExtPlane, EqOn F f (toExt unitDisc) ∧ ContinuousOn F (toExt (closedBall 0 1))) ↔
      IsLocConnSph (frontier G) := by
  sorry

/-- **Carathéodory Theorem** (§2.1). The conformal map `f` of `𝔻` onto `G ⊆ Ĉ` has a continuous and injective extension
to `𝔻 ∪ 𝕋` if and only if `∂G` is a Jordan curve. (Theorem 2.6 is the case of bounded `G`.) -/
theorem caratheodory_theorem {G : Set ExtPlane} {f : ExtPlane → ExtPlane} (hf : IsConformalMap f (toExt unitDisc))
    (hfG : f '' toExt unitDisc = G) :
    (∃ F : ExtPlane → ExtPlane, EqOn F f (toExt unitDisc) ∧ ContinuousOn F (toExt (closedBall 0 1)) ∧
      InjOn F (toExt (closedBall 0 1))) ↔ IsJordanCurve (frontier G) := by
  sorry

/-- **Prime End Theorem** (§2.1). The points `ζ` on `𝕋` correspond one-to-one to the prime ends of `G`, and the limit
`f(ζ)` exists if and only if the prime end has only one point.
Modelling: the correspondence is that of Theorem 2.15 (`IsPrimeEndCorrespondence`); `f(ζ)` is the unrestricted limit
(2.1.1); "the prime end has only one point" is: its impression is a single point. -/
theorem prime_end_theorem {G : Set ExtPlane} {f : ExtPlane → ExtPlane} (hf : IsConformalMap f (toExt unitDisc))
    (hfG : f '' toExt unitDisc = G) :
    ∃ fhat : ℂ → Set (ℕ → Set ExtPlane), IsPrimeEndCorrespondence G f fhat ∧
      ∀ ζ ∈ sphere (0 : ℂ) 1,
        (∃ a, HasUnrestrictedLimit (fun z : ℂ => f z) ζ a) ↔ ∃ a, impression G (fhat ζ) = {a} := by
  sorry

end Pommerenke1992
