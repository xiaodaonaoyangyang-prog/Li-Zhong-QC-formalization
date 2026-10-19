import References.GardinerLakic2000.Ch07.S02_TeichmullerKobayashi
import References.GardinerLakic2000.Ch01.S06_HolomorphicMotions

/-!
# Gardiner–Lakic 2000, Ch. 7 §7.3 The lifting theorem

Source `teichmuller.txt`, lines 6284–6386.

* Definition (geometric isomorphism `ρ_h`, l. 6285) — exists: `GardinerLakic2000.IsGeometricIsomorphism`
  (Part A, §2.4)
* Theorem 2 (the lifting theorem [EKK94], l. 6332; cited l. 6551) — `thm7_2`

Not items (DESIGN §3): the proof of `d ≤ σ` for the universal Teichmüller space and the reduction (7.8)–(7.9)
(l. 6287–6330), which give (7.7) (`para7_2_kobayashi_eq_teich`); (7.11)–(7.15), steps of the proof.

**Conventions.** Holomorphic motions are Part A's `IsHolMotion` (of subsets of `ℂ`, parametrized by `Δ`, `∞` fixed);
`ℂ̄ ∖ ℍ` is the closed lower half-plane `{Im z ≤ 0}` (with `∞`). The group `Γ ≤ SL(2, ℝ)` preserves `ℍ` and `𝕃`.
"Torsion free" is used in the proof as "every `γ ≠ id` is fixed-point free on `ℍ`" (l. 6350), which is
`LiZhongQC.ActsFreely` [reading]. The Möbius transformations `γ̃_t` are `LiZhongQC.mobiusFn a b c d`, `ad − bc ≠ 0`;
the relation (7.10) is required where both sides are finite.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (mobiusFn lowerHalf)

/-- The relation (7.10) for a motion `h` on a set `S`: for every `γ ∈ Γ` and `t ∈ Δ` there is a Möbius
transformation `γ̃_t` with `h(t, γ(z)) = γ̃_t(h(t, z))` for `z ∈ S` (where both sides are finite). -/
def IsGammaEquivariantMotion (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (S : Set ℂ)
    (h : ℂ → ℂ → ℂ) : Prop :=
  ∀ γ ∈ Γ, ∀ t ∈ ball (0 : ℂ) 1, ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ ∀ z ∈ S,
    (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 → c * h t z + d ≠ 0 →
      h t (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = mobiusFn a b c d (h t z)

/-- **Theorem 2** (the lifting theorem, §7.3, l. 6332). Let `h(t, z)` be a holomorphic motion of `ℂ̄ ∖ ℍ` and `Γ` a
torsion-free group of Möbius transformations mapping `𝕃` onto itself, such that for each `γ ∈ Γ` and `t ∈ Δ` there is
a Möbius transformation `γ̃_t` with `h(t, γ(z)) = γ̃_t(h(t, z))` (7.10) for `z ∈ 𝕃`. Then `h` extends to a
holomorphic motion of `ℂ̄` for which (7.10) holds for all `γ ∈ Γ`, `t ∈ Δ` and `z ∈ ℂ̄`. -/
theorem thm7_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hfree : LiZhongQC.ActsFreely Γ)
    {h : ℂ → ℂ → ℂ} (hh : IsHolMotion {z : ℂ | z.im ≤ 0} h) (heq : IsGammaEquivariantMotion Γ lowerHalf h) :
    ∃ H : ℂ → ℂ → ℂ, IsHolMotion univ H ∧ (∀ t ∈ ball (0 : ℂ) 1, ∀ z : ℂ, z.im ≤ 0 → H t z = h t z) ∧
      IsGammaEquivariantMotion Γ univ H := by
  sorry

end GardinerLakic2000
