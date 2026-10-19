import LiZhongQC.Ch05.S21_UniversalTeichmuller
import References.Common.ExtendedPlane

/-!
# Gehring 1978, §1 Introduction

F. W. Gehring, *Spirals and the universal Teichmüller space*, Acta Math. 141 (1978), §1; source `full.md` of
`Spirals and the universal Teichmüller space.pdf-602096dc…`, lines 11–89.

* Definition (simply connected domain of hyperbolic type in `ℂ̄`, §1, standing) — `IsHypSimplyConnectedExt`
* Definition (hyperbolic metric `ϱ_D`, §1) — `hypDensity`
* Definition (norm `‖φ‖_D`, §1) — `hypNorm`
* Definition (Schwarzian derivative `S_f`, (1), §1) — exists: `LiZhongQC.schwarzian` (the same formula at the finite
  points, extended to the poles by inversion; its value at infinity is never needed, as `Gehring1978.hypNorm` is a
  supremum over the finite points)
* Definition (conformal map in a domain of `ℂ̄` and its image; standing, §1) — `IsConformalExt`, `imageExt`
* Definition (Jordan domain in `ℂ̄`; standing, §1) — exists: `References.IsJordanDomainExt` (shared layer; the finite
  part of a set of the extended plane is `References.finitePart`)
* Definition (lower half-plane `L`, §1) — exists: `LiZhongQC.lowerHalf`
* Definition (`B₂ = B₂(L, 1)`, `‖φ‖ = sup 4y²|φ(z)|`, §1) — exists: `LiZhongQC.bersSpaceL` (the same space; its norm
  `LiZhongQC.bersNormL` is one quarter of Gehring's norm, which is `Gehring1978.hypNorm` of the lower half-plane)
* Definition (`S`: the `S_g`, `g` conformal in `L`, §1) — exists: `LiZhongQC.schwarzianUnivalentSet` (as functions on
  the plane vanishing off the lower half-plane, like T in the project; elements of B₂ are compared with S and T
  through their restriction to the lower half-plane)
* Definition (`T = T(1)`, the universal Teichmüller space: the `S_g`, `g` conformal in `L` with a quasiconformal
  extension to `ℂ̄`, §1) — exists: `LiZhongQC.bersMapU` (T is its range; a quasiconformal extension of g, normalized by
  a Möbius map, is the normalized solution of a Beltrami coefficient vanishing in L, with the same Schwarzian on L,
  the step `LiZhongQC.aw_extend` with `LiZhongQC.aw_nu`; conversely every normalized solution is conformal in L,
  `LiZhongQC.ut_conformal_lowerHalf`)
* Theorem 1 (`T` is the interior of `S`) — exists: `LiZhongQC.thm21_4_gehring` (the same statement, the interior taken
  in B₂; the project's norm is equivalent to Gehring's)
* Theorem 2 — `thm2`
* Corollary (a `φ ∈ S` not in the closure of `T`) — omitted: the project's statement `gehring_closure_ne` was
  deleted by user decision, 2026-10-17

Not items (DESIGN §3):
- the Question (Bers: is `S` the closure of `T`?, l. 47), an open problem answered by the Corollary;
- the bound `‖φ‖ ≤ 6` on `S` quoted from Nehari (l. 39, unlabelled and not cited later, U−; the project has it for
  holomorphic `g` as `LiZhongQC.bA_kraus_lowerHalf`, `3/2` in the quarter normalization);
- the proof of the Corollary (l. 55–67);
- the aside that `S_g` is rational (l. 75; not proved, not cited later, U−);
- the outline of the proof of Theorem 2 (l. 77–89; restated by Lemmas 1, 3, 5, 6, 8, 9).

The explicit domain `D = ℂ̄ - γ` of l. 69–75 and the spirals `α₁`, `α₂` are defined in `S3_ProofOfTheorem2`, where the
paper defines them formally. The explicit form of Theorem 2 is stated there as `thm2_explicit`.

**Conventions.** Domains are subsets of `ℂ̄ = LiZhongQC.ExtPlane`, and the paper's own `D` contains `∞`; the project's
`poincareDensity`, `schwarzianNorm` and `IsJordanDomain` are for plane domains only, hence the new definitions below
and the shared ones of `References.Common.ExtendedPlane` (`IsDomainExt`, `IsJordanDomainExt`, `finitePart`).
They use Gehring's normalization: `ϱ_D` has curvature `-4`, so `‖·‖_D` is four times the project's `schwarzianNorm`
and `bersNormL` for plane domains. No constant of a stated result depends on this factor.
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real

noncomputable section

namespace Gehring1978

open LiZhongQC References

/-- **Definition** (§1, standing). `D ⊆ ℂ̄` is a simply connected domain of hyperbolic type: a domain of `ℂ̄`
(`References.IsDomainExt`) which is simply connected, with at least two points of `ℂ̄` outside `D`.
Modelling: for a simply connected domain of `ℂ̄`, hyperbolic type (the unit disc as universal covering) means exactly
that the complement has at least two points. -/
def IsHypSimplyConnectedExt (D : Set ExtPlane) : Prop :=
  IsDomainExt D ∧ IsSimplyConnected D ∧ Dᶜ.Nontrivial

/-- `g` maps the domain `D ⊆ ℂ̄` conformally onto the unit disc: `g` is holomorphic at the finite points of `D`, and
`g`, extended to `∞` by continuity when `∞ ∈ D`, maps `D` bijectively onto the disc.
Modelling: at `∞ ∈ D` the extension is bounded, hence holomorphic in the chart `1/z` (removable singularity), and an
injective holomorphic map is conformal. -/
def IsConformalOntoDiscExt (g : ℂ → ℂ) (D : Set ExtPlane) : Prop :=
  DifferentiableOn ℂ g (finitePart D) ∧
    ∃ G : ExtPlane → ℂ, (∀ z : ℂ, (z : ExtPlane) ∈ D → G z = g z) ∧ ContinuousOn G D ∧ InjOn G D ∧
      G '' D = unitDisc

/-- **Definition** (§1). The hyperbolic (non-euclidean) density `ϱ_D(z) = (1 - |g(z)|²)⁻¹ |g'(z)|` of a simply
connected domain `D ⊆ ℂ̄` of hyperbolic type at a finite point `z ∈ D`, where `g` is any conformal map of `D` onto the
unit disc.
Modelling: the value does not depend on `g` (Schwarz–Pick), so it is written as the supremum of the set of values,
which is a single point; it is `0` (junk) only when `D` has no such map, which does not happen for the domains of the
paper. For a plane domain this is half the project's `LiZhongQC.poincareDensity`. -/
def hypDensity (D : Set ExtPlane) (z : ℂ) : ℝ :=
  sSup {r : ℝ | ∃ g : ℂ → ℂ, IsConformalOntoDiscExt g D ∧ r = ‖deriv g z‖ / (1 - ‖g z‖ ^ 2)}

/-- **Definition** (§1). The norm `‖φ‖_D = sup_{z ∈ D} |φ(z)| ϱ_D(z)⁻²` of a function `φ` in `D ⊆ ℂ̄`.
Modelling: the supremum runs over the finite points of `D`. If `∞ ∈ D`, the quantity `|φ| ϱ_D⁻²` at `∞` is computed in
the chart `1/z`; for `φ = S_f`, `f` conformal at `∞`, it is continuous there, so leaving out this one point does not
change the supremum. The paper (and this formalization) uses the norm only for `φ = S_f`. For a plane domain this is
four times the project's `LiZhongQC.hyperbolicSupNorm`. -/
def hypNorm (φ : ℂ → ℂ) (D : Set ExtPlane) : ℝ≥0∞ :=
  ⨆ z ∈ finitePart D, ENNReal.ofReal (‖φ z‖ / hypDensity D z ^ 2)

/-- **Definition** (§1, standing). `f` is conformal (univalent meromorphic) in the domain `D ⊆ ℂ̄`: univalent
meromorphic at the finite points of `D` (at most one simple pole) and, if `∞ ∈ D`, `f` has a limit `f(∞) ∈ ℂ̄` at `∞`
which it takes at no finite point of `D`.
Modelling: values in `ℂ̄` are read through `LiZhongQC.meroToExt` (`∞` at the pole). An injective meromorphic map near
`∞` has a removable singularity or a simple pole there, so the limit condition only records the value `f(∞)` and the
injectivity at `∞`. The limit is taken along `cocompact ℂ`; in every use `D` is open, hence a neighbourhood of `∞`
when `∞ ∈ D`, so only values of `f` in `D` matter.
*Caveat* (AUDITR2_AGGCommon R2-G1): the predicate is meaningful only for open `D` (a domain): for a non-open `D` the limit
at `∞` along `cocompact ℂ` also sees values of `f` outside `D`. `IsOpen D` is deliberately not part of the definition
because some statements apply it to an arbitrary `Set ExtPlane` (for instance the suprema over `f` in the definitions of
`discDistance`-type quantities, and `imageExt`-hypotheses with a free target `A'`), where adding it would change the value
of those definitions; every theorem in the program that uses it supplies a domain. -/
def IsConformalExt (f : ℂ → ℂ) (D : Set ExtPlane) : Prop :=
  IsUnivMero f (finitePart D) ∧
    (extInf ∈ D → ∃ p : ExtPlane, Tendsto (meroToExt f) (cocompact ℂ) (𝓝 p) ∧ p ∉ meroToExt f '' finitePart D)

/-- The image `f(D) ⊆ ℂ̄` of a domain `D ⊆ ℂ̄` under a map `f` conformal in `D`: the values `f(z) ∈ ℂ̄` at the finite
points of `D` (`∞` at the pole), together with the limit `f(∞)` when `∞ ∈ D`.
Modelling: `f(∞)` must be included; otherwise it would be an isolated boundary point of the image. As in
`IsConformalExt`, the limit along `cocompact ℂ` only sees `D` because `D` is open in every use. -/
def imageExt (f : ℂ → ℂ) (D : Set ExtPlane) : Set ExtPlane :=
  meroToExt f '' finitePart D ∪ {p | extInf ∈ D ∧ Tendsto (meroToExt f) (cocompact ℂ) (𝓝 p)}

/-- **Theorem 2** (§1). There exist a simply connected domain `D` of hyperbolic type and a constant `δ > 0` with the
following property: if `f` is conformal in `D` and `‖S_f‖_D ≤ δ`, then `f(D)` is not a Jordan domain.
Modelling: `D` ranges over the domains of `ℂ̄` (the paper's `D` contains `∞`), `f` over the univalent meromorphic maps
in `D` (`IsConformalExt`), `f(D)` is `imageExt f D` (including `f(∞)`), "Jordan domain" is the shared
`References.IsJordanDomainExt`, and `‖S_f‖_D` is Gehring's `hypNorm`. -/
theorem thm2 :
    ∃ D : Set ExtPlane, IsHypSimplyConnectedExt D ∧ ∃ δ > (0 : ℝ), ∀ f : ℂ → ℂ, IsConformalExt f D →
      hypNorm (schwarzian f) D ≤ ENNReal.ofReal δ → ¬ IsJordanDomainExt (imageExt f D) := by
  sorry

end Gehring1978
