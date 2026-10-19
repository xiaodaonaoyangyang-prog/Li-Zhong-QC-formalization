import References.Katok1992.Ch04.S01_GeometricallyFiniteGroups

/-!
# Katok 1992, Ch. 4 §4.6 Finitely generated Fuchsian groups

S. Katok, *Fuchsian Groups* (1992), Chapter 4, §4.6; source `full.md` of `Fuchsian groups (Katok, Svetlana)
…-3766f6b7…`, lines 2258–2334.

* Theorem 4.6.1 (a finitely generated Fuchsian group is geometrically finite; l. 2262) — `thm4_6_1`
* Remark (the converse is Theorem 3.5.4: a group with a finitely-sided fundamental region is finitely generated; l. 2260) —
  covered by Theorem 3.5.4 (the side-pairing elements generate `Γ`)

**Conventions.** Finitely generated is `Group.FG Γ` for the subgroup `Γ` of `PSL(2, ℝ)`.

**For the Gardiner–Lakic items of Chapter 10.** `GardinerLakic2000.thm10_3`, `thm10_3_classes`, `thm10_4`, `thm10_5` (for a finitely
generated Fuchsian subgroup of `SL(2, ℝ)`; `thm10_4`: of the first kind) use, in the book's proofs, the local finiteness of Dirichlet regions
(`Katok1992.thm3_5_1`), the generation by side pairings (`thm3_5_4`) and `thm4_6_1`; they are stated for subgroups of
`SL(2, ℝ)`, so the bridge is the image `Γ.map (QuotientGroup.mk' (Subgroup.center SL(2, ℝ)))` in `PSL(2, ℝ)`.
-/

open Set
open scoped UpperHalfPlane MatrixGroups

noncomputable section

namespace Katok1992

/-- **Theorem 4.6.1** (§4.6; l. 2262). If a Fuchsian group `Γ` is finitely generated, it is geometrically finite. -/
theorem thm4_6_1 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfg : Group.FG Γ) : IsGeometricallyFinite Γ := by
  sorry

end Katok1992
