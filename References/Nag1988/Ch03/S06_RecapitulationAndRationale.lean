import References.Nag1988.Ch03.S03_BersEmbeddingOfArbitraryTG
import References.GardinerLakic2000.Ch02.S09_FundamentalDomains

/-!
# Nag, Chapter 3 §3.6: Recapitulation and rationale for the Bers embedding

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 3 §3.6 (`full.md` N2:1533–1637; folder
`c10f6cd1`, cited `N2:<line>`). New: Proposition 3.6.3.

**Reading of "`T(G)` is finite dimensional"** (leader ruling): `B₂(L, G)` is a finite-dimensional complex vector space, i.e.
`Submodule.span ℂ (cuspFormsL Γ)` (`cuspFormsL Γ` is already a subspace) is `FiniteDimensional ℂ`; `T(G)` is an open subset of it
(Bers embedding), so the two dimensions agree. "Of the first kind" is `GardinerLakic2000.IsFirstKind` (`Γ ≤ SL(2, ℝ)`).

* Sections 3.6.1–3.6.2 (summary; intrinsicality, `Mod(G)` acts biholomorphically) — omitted: recapitulation
  (the content is `Lehto1987.thm5_5_6`, see Ch03/S02)
* Proposition 3.6.3 (`dim T(G) < ∞` iff `G` is finitely generated of the first kind; then `T(G) ≅ T(X)` and the dimension is
  `3g - 3 + n`; N2:1582) — `prop3_6_3`, `prop3_6_3_dim`
* Section 3.6.4 (`T_β(G)` is the component of `T_β(1) ∩ B₂(L, G)` containing `0`; N2:1610) — exists: `Lehto1987.thm5_4_1`
* Section 3.6.5 (Gehring: the closure of `T_β(1)` is a proper subset of `S`, and `T_β(1)` is the interior of `S`; N2:1622) —
  exists: `LiZhongQC.thm21_4_gehring`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff MatrixGroups

noncomputable section

namespace Nag1988

open LiZhongQC (IsFuchsian)
open GardinerLakic2000 (cuspFormsL IsFirstKind)

/-- **Proposition 3.6.3** (§3.6.3; N2:1582). For a Fuchsian group `Γ`, the space `B₂(L, Γ)` (hence the complex manifold `T(Γ)`) is
finite dimensional iff `Γ` is finitely generated and of the first kind. In that case, if `Γ` is torsion free of type `(g, n)`, the
dimension is `3g - 3 + n` (and `2g - 2 + n > 0`). -/
theorem prop3_6_3 {Γ : Subgroup SL2R} (hΓ : IsFuchsian Γ) :
    FiniteDimensional ℂ (Submodule.span ℂ (cuspFormsL Γ)) ↔ (Group.FG Γ ∧ IsFirstKind Γ) := by
  sorry

/-- **Proposition 3.6.3**, the dimension: for a torsion-free `Γ` of finite type `(g, n)` (no holes), `dim T(Γ) = 3g - 3 + n`. -/
theorem prop3_6_3_dim {Γ : Subgroup SL2R} {g n : ℕ} (hΓ : IsFuchsian Γ) (hT : IsOfType3 Γ g n 0) :
    0 < 2 * (g : ℤ) - 2 + n ∧ Module.finrank ℂ (Submodule.span ℂ (cuspFormsL Γ)) = 3 * g + n - 3 := by
  sorry

end Nag1988
