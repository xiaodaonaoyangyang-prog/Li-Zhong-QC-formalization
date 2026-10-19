import References.Katok1992.Ch03.S06_RiemannSurfacesHomogeneousSpaces

/-!
# Katok 1992, Ch. 4 §4.1 Geometrically finite Fuchsian groups

S. Katok, *Fuchsian Groups* (1992), Chapter 4, §4.1; source `full.md` of `Fuchsian groups (Katok, Svetlana)
…-3766f6b7…`, lines 1800–1908.

* Unlabelled (sides of `F`, the Euclidean closure of `F`, free sides; l. 1802–1803) — omitted: terminology (no polygon
  structure is modelled; see `Ch03/S05`)
* Definition (the area of the quotient `μ(Γ\ℍ)`; l. 1713, used from §4.1) — `quotientArea`
* Definition (geometrically finite; l. 1804) — `IsGeometricallyFinite`
* Theorem 4.1.1 (Siegel's theorem; l. 1806) — `thm4_1_1`

**Conventions.** The hyperbolic area of the quotient is that of a Dirichlet region (the book's definition at the start of
§3.6): `quotientArea Γ` is the infimum of `μ(D_p(Γ))` over the points `p` not fixed by an element of `Γ − {Id}`
(all these areas agree when finite, by Theorem 3.1.1; such points exist by Lemma 2.2.5, so the infimum is over a
non-empty set). *Finitely many sides* of a convex region `F ⊆ ℍ` means that the frontier of `F` in `ℍ` lies in a finite union
of geodesics: a side is a segment of a geodesic of the frontier (free sides on the real axis are not in `ℍ` and do not
count; the bound of the book is on the sides in `ℍ`). The book's "convex fundamental region" is
`IsFundamentalRegion Γ F ∧ References.HypConvex F`.

**Near misses.** None for `IsGeometricallyFinite`; Siegel's theorem is not stated elsewhere in the project.
-/

open Set MeasureTheory
open scoped UpperHalfPlane MatrixGroups ENNReal

noncomputable section

namespace Katok1992

/-- **Definition** (§3.6; l. 1713, §4.1). The hyperbolic area `μ(Γ\ℍ)` of the quotient: the area of a Dirichlet region
`D_p(Γ)` (Theorem 3.1.1 shows it does not depend on `p` when it is finite). -/
def quotientArea (Γ : Subgroup PSL(2, ℝ)) : ℝ≥0∞ :=
  ⨅ p : {p : ℍ // ∀ T ∈ Γ, T ≠ 1 → T • p ≠ p}, volume (dirichletRegion Γ p)

/-- **Definition** (§4.1; l. 1804). A Fuchsian group is *geometrically finite* if there exists a convex fundamental region
for `Γ` with finitely many sides (the frontier of `F` in `ℍ` lies in finitely many geodesics). -/
def IsGeometricallyFinite (Γ : Subgroup PSL(2, ℝ)) : Prop :=
  ∃ F : Set ℍ, IsFundamentalRegion Γ F ∧ References.HypConvex F ∧
    ∃ L : Finset (Set ℍ), (∀ l ∈ L, IsGeodesic l) ∧ frontier F ⊆ ⋃ l ∈ L, l

/-- **Theorem 4.1.1** (Siegel's theorem; §4.1; l. 1806). If `Γ` is such that `μ(Γ\ℍ) < ∞`, then `Γ` is geometrically
finite (in fact every Dirichlet region of `Γ` has finitely many sides). -/
theorem thm4_1_1 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (h : quotientArea Γ < ⊤) : IsGeometricallyFinite Γ := by
  sorry

end Katok1992
