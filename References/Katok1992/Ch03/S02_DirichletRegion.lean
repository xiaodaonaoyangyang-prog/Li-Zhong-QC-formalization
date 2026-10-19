import References.Katok1992.Ch03.S01_FundamentalRegion
import References.Common.HypConvex

/-!
# Katok 1992, Ch. 3 §3.2 The Dirichlet region

S. Katok, *Fuchsian Groups* (1992), Chapter 3, §3.2; source `full.md` of `Fuchsian groups (Katok, Svetlana)
…-3766f6b7…`, lines 1283–1373.

* Definition (the Dirichlet region `D_p(Γ)`, (3.2.1)–(3.2.3); l. 1283–1303) — `dirichletRegion`
* Definition (perpendicular bisector; l. 1309) — covered by `lemma3_2_1` (the bisector is the geodesic through the
  midpoint orthogonal to the segment)
* Definition (hyperbolic convexity; l. 1303) — exists: `References.HypConvex`
* Lemma 3.2.1 (the locus `ρ(z, z₁) = ρ(z, z₂)` is the perpendicular bisector; l. 1313) — `lemma3_2_1`
* Theorem 3.2.2 (`D_p(Γ)` is a connected, convex fundamental region; l. 1337) — `thm3_2_2`
* Example A (the Dirichlet region of the modular group centred at `ki`; l. 1343–1371) — `exampleA_dirichlet`

**Conventions.** `ρ` is Mathlib's `dist` on `ℍ` (curvature `−1`, Ch. 1 §1.1). `D_p(Γ)` is the set (3.2.1); the equivalent
form (3.2.2) and the description as an intersection of half-planes `H_p(T)` are consequences used in the proof and are
not separate items. Convexity is `References.HypConvex` (`Common/HypConvex`, a light file: `Common/HyperbolicSurface` imports
Gardiner–Lakic Ch. 11, downstream of the Chapter 10 items that cite Katok Ch. 3 and 4, so it is not imported here). The geodesic
facts use the installed `IsGeodesic`, `geodSegment`, `hypAngle`.

**Near miss.** `GardinerLakic2000.dirichletDomain` (formula (2.27)): the Dirichlet domain of a subgroup of `SL(2, ℝ)` as a
set of complex numbers, for a non-elliptic centre; the statement there is the definition only.
-/

open Set
open scoped UpperHalfPlane MatrixGroups Real

noncomputable section

namespace Katok1992

/-- **Definition** (§3.2; l. 1285–1295, (3.2.1)). The Dirichlet region for `Γ` centred at `p ∈ ℍ`:
`D_p(Γ) = {z ∈ ℍ | ρ(z, p) ≤ ρ(z, T(p)) for all T ∈ Γ}`. (The book assumes `p` is not fixed by any element of
`Γ − {Id}`; the definition makes sense for every `p`, the theorem carries the assumption.) -/
def dirichletRegion (Γ : Subgroup PSL(2, ℝ)) (p : ℍ) : Set ℍ :=
  {z | ∀ T : Γ, dist z p ≤ dist z ((T : PSL(2, ℝ)) • p)}

/-- **Lemma 3.2.1** (§3.2; l. 1313). For `z₁ ≠ z₂` the line `ρ(z, z₁) = ρ(z, z₂)` is the perpendicular bisector of the
geodesic segment `[z₁, z₂]`: it is a geodesic, it passes through the midpoint `w` of the segment, and it is orthogonal to
the segment there (the angle at `w` between the geodesic towards a point `u ≠ w` of the line and the geodesic towards
`z₁` is `π/2`). -/
theorem lemma3_2_1 {z₁ z₂ : ℍ} (h : z₁ ≠ z₂) :
    IsGeodesic {z : ℍ | dist z z₁ = dist z z₂} ∧
      ∃ w ∈ geodSegment z₁ z₂, dist z₁ w = dist w z₂ ∧ dist w z₁ = dist w z₂ ∧
        ∀ u ∈ {z : ℍ | dist z z₁ = dist z z₂}, u ≠ w → hypAngle w (toExtH u) (toExtH z₁) = π / 2 := by
  sorry

/-- **Theorem 3.2.2** (§3.2; l. 1337). If `p` is not fixed by any element of `Γ − {Id}`, then `D_p(Γ)` is a connected
fundamental region for `Γ` (and, as the intersection of the hyperbolic half-planes `H_p(T)`, hyperbolically convex). -/
theorem thm3_2_2 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {p : ℍ}
    (hp : ∀ T ∈ Γ, T ≠ 1 → T • p ≠ p) :
    IsFundamentalRegion Γ (dirichletRegion Γ p) ∧ IsConnected (dirichletRegion Γ p) ∧
      References.HypConvex (dirichletRegion Γ p) := by
  sorry

/-- **Example A** (§3.2; l. 1343–1371; cited at l. 1659, 1699, 1707). For the modular group `Γ = PSL(2, ℤ)` and
`p = ki` with `k > 1`: `p` is not fixed by any non-identity element of `Γ`, and the Dirichlet region centred at `p` is
`F = {z ∈ ℍ | |z| ≥ 1, |Re z| ≤ 1/2}`. -/
theorem exampleA_dirichlet {k : ℝ} (hk : 1 < k) {p : ℍ} (hp : (p : ℂ) = k * Complex.I) :
    (∀ T ∈ modularGroup, T ≠ 1 → T • p ≠ p) ∧
      dirichletRegion modularGroup p = {z : ℍ | 1 ≤ ‖(z : ℂ)‖ ∧ |(z : ℂ).re| ≤ 1 / 2} := by
  sorry

end Katok1992
