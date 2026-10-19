import References.Common.HyperbolicSurface
import References.GardinerLakic2000.Ch05.S01_ConformallyNaturalExtension
import References.Hubbard2006.Ch04.S09_BoundaryValues

/-!
# Hubbard 2006, Chapter 5 §5.1: The Douady–Earle extension (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 180–556.

**Conventions.** Circle homeomorphisms are `Pommerenke1992.IsSensePreservingCircleHomeo` (sense preserving), the
Douady–Earle extension is `Pommerenke1992.douadyEarleExt`, with the quasisymmetry modulus `λ` of
`Pommerenke1992.IsQuasisymmetricWith` playing the role of Hubbard's `M` (the two notions of quasisymmetric circle maps
are equivalent, Exercise 5.1.1, and the constants depend only on each other). The Earle–Nag reflection estimate uses
the Poincaré density `LiZhongQC.poincareDensity` of the complementary component (curvature `−1`).

* Thm 5.1.2 (Douady–Earle extension theorem: a quasisymmetric circle map has a `K`-quasiconformal extension, `K`
  depending only on the modulus, naturally under `Aut 𝔻`) — exists: `Pommerenke1992.thm5_15`,
  `Pommerenke1992.thm5_15_ii`
* Prop. and Def. 5.1.3 (the conformal barycenter) — exists: `GardinerLakic2000.vectorFieldVm`,
  `GardinerLakic2000.conformalBarycenter`, `GardinerLakic2000.lemma5_1`
* Def. 5.1.5 (the Douady–Earle extension `Φ(f)(z) = B(f_* η_z)`) — exists: `Pommerenke1992.douadyEarleExt`
* Prop. 5.1.6 (extension to the closed disc, agreement on the circle, real analyticity, naturality) — exists:
  `Pommerenke1992.thm5_15`
* Prop. 5.1.7 (the extension of a homeomorphism of the circle is a diffeomorphism) — `prop5_1_7`
* Prop. 5.1.11 (the extension of a quasisymmetric homeomorphism is quasiconformal, with a constant `α(M)`) — exists:
  `Pommerenke1992.thm5_15_ii`, `GardinerLakic2000.thm5_2`
* Thm 5.1.13 (natural reflections in quasicircles: a quasireflection `ψ_D`, Möbius natural, with the Earle–Nag
  estimate (5.1.26)) — `thm5_1_13`
* Thm 5.1.12 (extension of quasisymmetric maps `S¹ → ℙ¹` to quasiconformal maps of `ℙ¹`, continuous and natural) —
  deferred: needs the Möbius-normalized modulus (5.1.24) of quasisymmetric maps `S¹ → ℙ¹` and the topology of
  uniform convergence on `ℙ¹`
* Lemmas 5.1.8, 5.1.10 (linear algebra and Fourier coefficients in the proof of 5.1.7, 5.1.11) — omitted: proof step
* Remark 5.1.4, Exercise 5.1.1, 5.1.9 — omitted: remark / exercise
-/

open Set Metric
open scoped Real

namespace Hubbard2006

open LiZhongQC

/-- **Proposition 5.1.7** (H2:300). If `f : S¹ → S¹` is a (sense preserving) homeomorphism, the Douady–Earle extension
`f̂` is a diffeomorphism of the open disc: it is real analytic with positive Jacobian (`jac > 0`), hence a real
analytic diffeomorphism of `𝔻` onto `𝔻` (it is a homeomorphism of the closed disc by `Pommerenke1992.thm5_15`). -/
theorem prop5_1_7 {f : ℂ → ℂ} (hf : Pommerenke1992.IsSensePreservingCircleHomeo f) :
    ∀ z ∈ unitDisc, 0 < jacobian (Pommerenke1992.douadyEarleExt f) z := by
  sorry

/-- **Theorem 5.1.13 (Natural reflections in quasicircles)** (H2:431). For `M ≥ 1` there are constants `K`, `C` and, for
every component `D` of the complement of an `M`-quasicircle `Γ ⊂ ℙ¹`, a `K`-quasireflection `ψ_D` in `Γ`
(`IsKQuasireflection`) such that (1) `ψ_{γ(D)} = γ ∘ ψ_D ∘ γ⁻¹` for every Möbius `γ`, and (2) for the curves through
`∞` and `z ∈ ℂ ∖ Γ` with `ψ_D z ≠ ∞`: `1/C ≤ |z − ψ_D(z)|² ρ_{D*}(ψ_D(z))² |∂̄ψ_D(z)| ≤ C`, where `ρ_{D*}` is the
Poincaré density of the other component `D*`. *Reading:* the family `ψ_D` is the function `D ↦ ψ_D` on subsets of `ℙ¹`;
(2) is stated for `∞ ∈ Γ` (the general case follows from (1)). -/
theorem thm5_1_13 {M : ℝ} (hM : 1 ≤ M) :
    ∃ (K C : ℝ) (Ψ : Set ExtPlane → ExtPlane → ExtPlane), 0 < C ∧
      (∀ Γ D D' : Set ExtPlane, IsKQuasicircle Γ M → AreComplementaryComponents Γ D D' →
        IsKQuasireflection Γ D D' (Ψ D) K) ∧
      (∀ Γ D D' : Set ExtPlane, IsKQuasicircle Γ M → AreComplementaryComponents Γ D D' →
        ∀ γ : ExtPlane → ExtPlane, IsMobius γ → Function.Bijective γ → ∀ p : ExtPlane,
          Ψ (γ '' D) (γ p) = γ (Ψ D p)) ∧
      (∀ Γ D D' : Set ExtPlane, IsKQuasicircle Γ M → AreComplementaryComponents Γ D D' → extInf ∈ Γ →
        ∀ z : ℂ, (z : ExtPlane) ∈ D → Ψ D z ≠ extInf →
          1 / C ≤ ‖z - extToC (Ψ D z)‖ ^ 2 * poincareDensity {w : ℂ | (w : ExtPlane) ∈ D'} (extToC (Ψ D z)) ^ 2 *
              ‖dzbar (fun w => extToC (Ψ D w)) z‖ ∧
            ‖z - extToC (Ψ D z)‖ ^ 2 * poincareDensity {w : ℂ | (w : ExtPlane) ∈ D'} (extToC (Ψ D z)) ^ 2 *
              ‖dzbar (fun w => extToC (Ψ D w)) z‖ ≤ C) := by
  sorry

end Hubbard2006
