import References.Nag1988.Ch05.S02_UniversalFamily
import References.GardinerLakic2000.Ch10.S01_MCGForCoveringGroup

/-!
# Nag, Chapter 2 §2.3: Allowable bijections and the modular group

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 2 §2.3 (`full.md` N1:3676–3860; folder
`The Complex Analytic Theory … 10dae1e9`, cited `N1:<line>`). Only §2.3.10 is new; the other items are passed with `exists:`.

**Model.** `T(g, n)` is `LiZhongQC.TeichGamma Γ` for a Fuchsian group `Γ ≤ SL(2, ℝ)` with `Nag1988.IsOfType Γ g n` (the
uniformizing group of a surface of finite type `(g, n)`, no holes); the Teichmüller distance is
`LiZhongQC.teichDistanceGamma`. An *isometric bijection* `T(g, n) → T(g', n')` is an equivalence of the underlying types
preserving `teichDistanceGamma` (no topology or complex structure is put on `T`; Nag's parenthetical "biholomorphic" in the
statement of Theorem 2.3.10 is omitted for this reason, see below). The modular action: `h ∈ GardinerLakic2000.qcNormalizer Γ`
sends `[μ]` to `[ν]` when `w^ν = α ∘ w^μ ∘ h` on `ℝ` for a real Möbius map `α` (`GardinerLakic2000.IsRhoGamma`, for `h⁻¹`);
`h` is the identity in `Mod(Γ)` iff `h|ℝ` is an element of `Γ` (`GardinerLakic2000.mcgGamma`). The case `(1, 0)`, `(0, 0)`, `(0, 1)`,
`(0, 2)` is excluded by `2g - 2 + n > 0`.

* Lemma 2.3.4 (`Mod(X)` acts by isometries; N1:3718), Lemma 2.3.5 (orbits are conformal classes; `R = T/Mod`; N1:3728) —
  exists: `GardinerLakic2000.para2_4_geometric_isometry`, `LiZhongQC.modAction_bijective`,
  `LiZhongQC.eq28_1_moduli_eq_quotient`
* Theorem 2.3.10 (the only isometric bijections between distinct `T(g, n)`, `2g - 2 + n > 0`, are `T(2, 0) ≅ T(0, 6)`,
  `T(1, 2) ≅ T(0, 5)`, `T(1, 1) ≅ T(0, 4)`; N1:3797) — `thm2_3_10`
  (the parenthetical "and actually the only cases of biholomorphically equivalent Teichmüller spaces" is an omitted part: it
  would need a complex structure on T(g, n), which is not an instance on the installed TeichGamma; the book gives it as a
  remark after the theorem)
* Proposition (the modular group `Mod(g, n)` acts non-effectively on `T(g, n)` exactly for `(2, 0)`, `(1, 2)`, `(1, 1)`, `(0, 4)`,
  `(0, 3)`; N1:3805) — `prop2_3_10_noneffective`
* Examples 2.3.11–2.3.12 (annulus; modular actions on T(G), mod(G), Mod(G)) — omitted: 2.3.11 is a remark on bordered
  surfaces; 2.3.12 is definitions that are installed (mcgGamma, qcNormalizer of Gardiner–Lakic, modExtended of Nag Ch. 5)
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff MatrixGroups

noncomputable section

namespace Nag1988

open LiZhongQC (TeichGamma teichSetoidGamma teichDistanceGamma fMuSym h36p_m IsFuchsian ActsFreely BeltramiGamma)
open GardinerLakic2000 (qcNormalizer)

/-- The pairs of types `(g, n)`, `(g', n')` for which the Teichmüller spaces are isometric (Theorem 2.3.10): equal types, or one
of the three exceptional pairs `(2, 0), (0, 6)`, `(1, 2), (0, 5)`, `(1, 1), (0, 4)` (in either order). -/
def IsoTypes (g n g' n' : ℕ) : Prop :=
  (g = g' ∧ n = n') ∨ (g = 2 ∧ n = 0 ∧ g' = 0 ∧ n' = 6) ∨ (g = 0 ∧ n = 6 ∧ g' = 2 ∧ n' = 0) ∨
    (g = 1 ∧ n = 2 ∧ g' = 0 ∧ n' = 5) ∨ (g = 0 ∧ n = 5 ∧ g' = 1 ∧ n' = 2) ∨
    (g = 1 ∧ n = 1 ∧ g' = 0 ∧ n' = 4) ∨ (g = 0 ∧ n = 4 ∧ g' = 1 ∧ n' = 1)

/-- **Theorem 2.3.10** (§2.3.10; N1:3797). Let `X`, `X'` be Riemann surfaces of finite conformal type `(g, n)`, `(g', n')` with
`2g - 2 + n > 0`, `2g' - 2 + n' > 0`, uniformized by the Fuchsian groups `Γ`, `Γ'`. There is an isometric bijection
`T(g, n) → T(g', n')` iff the types agree or the pair is one of the three exceptional pairs `(2,0)–(0,6)`, `(1,2)–(0,5)`,
`(1,1)–(0,4)`. -/
theorem thm2_3_10 {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {g n g' n' : ℕ} (hΓ : IsFuchsian Γ)
    (hΓ' : IsFuchsian Γ') (hT : IsOfType Γ g n) (hT' : IsOfType Γ' g' n') (hχ : 0 < 2 * (g : ℤ) - 2 + n)
    (hχ' : 0 < 2 * (g' : ℤ) - 2 + n') :
    (∃ f : TeichGamma Γ ≃ TeichGamma Γ', ∀ p q, teichDistanceGamma (f p) (f q) = teichDistanceGamma p q) ↔
      IsoTypes g n g' n' := by
  sorry

/-- **Proposition** (§2.3.10; N1:3805). For a surface of finite conformal type `(g, n)` with `2g - 2 + n > 0`, uniformized by
`Γ`, the modular group acts non-effectively on `T(g, n)` iff `(g, n)` is one of `(2, 0)`, `(1, 2)`, `(1, 1)`, `(0, 4)`, `(0, 3)`.
Modelling: non-effective means that some `h ∈ QC(Γ)` which is not the identity in `Mod(Γ)` (the boundary map `h|ℝ`,
`GardinerLakic2000.qcBdry h` in `ℂ̂`, is not the restriction of an element of `Γ`) acts trivially: `ρ_h` is the identity
(`GardinerLakic2000.IsRhoGamma Γ Γ h id`: `w^ν ∘ h = α ∘ w^μ` on `ℝ̂`, `α` real Möbius, implies `[μ] = [ν]`). -/
theorem prop2_3_10_noneffective {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {g n : ℕ} (hΓ : IsFuchsian Γ)
    (hT : IsOfType Γ g n) (hχ : 0 < 2 * (g : ℤ) - 2 + n) :
    (∃ h ∈ qcNormalizer Γ,
        (¬ ∃ γ ∈ Γ, ∀ x : ℝ, GardinerLakic2000.qcBdry h ((x : ℂ) : LiZhongQC.ExtPlane) =
          LiZhongQC.mobiusSL (LiZhongQC.slRealToComplex γ) ((x : ℂ) : LiZhongQC.ExtPlane)) ∧
          GardinerLakic2000.IsRhoGamma Γ Γ h id) ↔
      ((g = 2 ∧ n = 0) ∨ (g = 1 ∧ n = 2) ∨ (g = 1 ∧ n = 1) ∨ (g = 0 ∧ n = 4) ∨ (g = 0 ∧ n = 3)) := by
  sorry

end Nag1988
