import LiZhongQC.Ch05.S20_SchwarzDomains
import References.LehtoVirtanen1973.Ch01.S03_DefinitionQC

/-!
# Astala–Gehring 1990, §1 Introduction

K. Astala, F. W. Gehring, *Crickets, zippers, and the Bers universal Teichmüller space*, Proc. Amer. Math. Soc. 110
(1990), §1; source `full.md` of `Astala-CricketsZippersBers-1990.pdf-e9a341c8…`, lines 25–45.

* Definition (the Banach space `E` with the norm (1.1), §1) — `normU`, `spaceE`
* Definition (Schwarzian derivative `S_f`, §1) — exists: `LiZhongQC.schwarzian` (the same formula; at poles by
  inversion)
* Definition (the universal Teichmüller space `T ⊂ E`, §1) — `setT`
* Definition (the set `S ⊂ E` of Schwarzians of all conformal maps of `U`, §1) — `setS`
* Definition (the closure `T̄` in `E`, §1) — `closureE`

Not items (DESIGN §3): the facts quoted from the literature at l. 35, none of them cited later as a result (U−):
- `S` is closed;
- `int S = T` [G2] (the project's half-plane form is `LiZhongQC.thm21_4_gehring`);
- `T` is connected [EE];
- `S ∖ T̄ ≠ ∅` [G3] (not formalized: the project's statement was deleted by user decision, 2026-10-17);
- `S` has isolated points [T, As] (not formalized: the project's statement was deleted by user decision, 2026-10-17).

**Conventions.**
- The paper works in the unit disc `U` (`LiZhongQC.unitDisc`). The project's universal Teichmüller space lives in the
  lower half-plane, and the project has no disc-model Bers space, so `E`, `S`, `T` and `T̄` are defined here.
- Elements of `E` are functions on `ℂ` vanishing off `U` (`unitDisc.indicator`), as in the project's half-plane model.
- "Conformal mapping of `U`" means univalent meromorphic (`LiZhongQC.IsUnivMero`), with values in `ℂ̄` read through
  `LiZhongQC.meroToExt`.
- "Quasiconformal extension to `ℂ̄`" means a quasiconformal self-mapping `F` of `ℂ̄`
  (`LehtoVirtanen1973.IsQuasiconformalMap F univ`, the reference notion, FOUNDATIONS.md) which agrees with `f` in `U`.
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real

noncomputable section

namespace AstalaGehring1990

open LiZhongQC
open LehtoVirtanen1973 (IsQuasiconformalMap)

/-- **Definition (1.1)** (§1). The norm `‖φ‖_U = sup_{z ∈ U} |φ(z)| (1 - |z|²)²` on functions in the unit disc.
It is the norm (2.1), `Gehring1978.hypNorm`, for `D = U`, where `ρ_U = (1 - |z|²)⁻¹`; the paper writes it out. -/
def normU (φ : ℂ → ℂ) : ℝ≥0∞ :=
  ⨆ z ∈ unitDisc, ENNReal.ofReal (‖φ z‖ * (1 - ‖z‖ ^ 2) ^ 2)

/-- **Definition** (§1). The Banach space `E` of the functions `φ` analytic in the unit disc `U` with `‖φ‖_U < ∞`.
Modelling: a function of `E` is a function on `ℂ` which vanishes off `U`. -/
def spaceE : Set (ℂ → ℂ) :=
  {φ | DifferentiableOn ℂ φ unitDisc ∧ normU φ < ⊤ ∧ unitDisc.indicator φ = φ}

/-- **Definition** (§1). The universal Teichmüller space `T ⊂ E`: the Schwarzian derivatives `S_f` of the conformal
mappings `f` of `U` which have a quasiconformal extension to `ℂ̄`.
Modelling: `f` is univalent meromorphic in `U`; the extension is a quasiconformal self-mapping `F` of `ℂ̄`
(`LehtoVirtanen1973.IsQuasiconformalMap F univ`) with `F = f` in `U` (values through `LiZhongQC.meroToExt`); `S_f` is
restricted to `U` by `unitDisc.indicator`. -/
def setT : Set (ℂ → ℂ) :=
  {φ | ∃ f : ℂ → ℂ, IsUnivMero f unitDisc ∧
    (∃ F : ExtPlane → ExtPlane, IsQuasiconformalMap F univ ∧ ∀ z ∈ unitDisc, F z = meroToExt f z) ∧
    φ = unitDisc.indicator (schwarzian f)}

/-- **Definition** (§1). The set `S ⊂ E` of the Schwarzian derivatives `S_f` of all conformal mappings `f` of `U`.
Modelling: as in `setT`. -/
def setS : Set (ℂ → ℂ) :=
  {φ | ∃ f : ℂ → ℂ, IsUnivMero f unitDisc ∧ φ = unitDisc.indicator (schwarzian f)}

/-- **Definition** (§1). The closure `Ā` in `E` of a set `A ⊆ E` (for `A = T`: the closure `T̄` of the universal
Teichmüller space): the functions vanishing off `U` which are limits in the norm (1.1) of elements of `A`.
Modelling: a norm limit of analytic functions is analytic in `U` with finite norm, so this is the closure in the
Banach space `E`. -/
def closureE (A : Set (ℂ → ℂ)) : Set (ℂ → ℂ) :=
  {φ | unitDisc.indicator φ = φ ∧ ∀ ε > (0 : ℝ), ∃ ψ ∈ A, normU (φ - ψ) < ENNReal.ofReal ε}

end AstalaGehring1990
