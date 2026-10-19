import LiZhongQC.Ch06.S22_RiemannSurfaces
import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
import References.GardinerLakic2000.Ch08.S06_IsometryProperty
import References.GardinerLakic2000.Ch10.S01_MCGForCoveringGroup

/-!
# Imayoshi–Taniguchi, Chapter 6 §6.3: Teichmüller modular group and moduli sets

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 6 §6.3 (`full.md` IT1:5830–5987,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions as in `Ch06/S04_Royden`: `Γ` is the Fuchsian model of a closed Riemann surface of genus `g ≥ 2`
(`LiZhongQC.IsFuchsian`: a subgroup of `SL(2, ℝ)` acting properly discontinuously on `ℍ`), `ρ` is the Poincaré distance on `ℍ`
(curvature `-1`), which is Mathlib's `dist` on `UpperHalfPlane`.

* Definition (Teichmüller modular group `Mod(Γ)` and its action `[ω]_*`, §6.3.1, IT1:5804) — exists: `GardinerLakic2000.mcgGamma`,
  `GardinerLakic2000.IsRhoGamma`
* Theorem 6.14 (`[ω]_*` is an isometry of the Teichmüller distance, IT1:5830) — exists:
  `GardinerLakic2000.para2_4_geometric_isometry`
* Lemma 6.15 (finitely many `γ ∈ Γ` move a compact set by at most `M`, IT1:5836) — `lemma6_15`
* Proposition 6.16 (the lengths of closed geodesics form a discrete set, finitely many of each length, IT1:5840) — exists:
  `LiZhongQC.thm30_1_discrete`
* Corollary to Proposition 6.16 (`{tr² γ}` is discrete, IT1:5848) — exists: `LiZhongQC.lengthSpectrum_discrete`
* Proposition 6.17 (traces of finitely many words determine the normalized generators, IT1:5852) — exists:
  `LiZhongQC.eq30_1_generators_determined`
* Theorem 6.18 (`Mod(Γ)` acts properly discontinuously on `T(Γ)`, IT1:5932) — exists: `LiZhongQC.thm30_3`
* Theorem 6.19 (the moduli space `M_g` is a normal complex analytic space of dimension `3g - 3`, IT1:5982) — deferred: normal
  complex analytic spaces are not available (cf. Cartan's quotient theorem, which the proof quotes)
-/

open Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (IsFuchsian)

/-- **Lemma 6.15** (Ch. 6 §6.3.2). For every compact subset `K` of the upper half-plane `H` and every positive number `M`, there
exist at most finitely many `γ ∈ Γ` with `min_{z ∈ K} ρ(z, γ(z)) ≤ M`, where `ρ` is the Poincaré distance on `H`. -/
theorem lemma6_15 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {K : Set UpperHalfPlane}
    (hK : IsCompact K) {M : ℝ} (hM : 0 < M) : {γ : Γ | ∃ z ∈ K, dist z (γ • z) ≤ M}.Finite := by
  sorry

end ImayoshiTaniguchi1992
