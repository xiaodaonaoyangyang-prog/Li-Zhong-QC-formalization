import References.Miyachi2008.S02_AsymptoticBersMap

/-!
# Miyachi 2008, §1.3 and §3: The necessary condition for an arbitrary Fuchsian group

H. Miyachi, *Image of asymptotic Bers map*, J. Math. Soc. Japan **60** (2008), 1255–1276; journal pages `p. n`.
Conventions: as in `S02_AsymptoticBersMap` (half-plane model: `D*` is `𝕃`, `Γ ≤ SL(2, ℝ)` Fuchsian).

* Definition (the quasiconformal extension property at ends with respect to `Γ`, p. 1257) — `IsRoundDisk`, `HasQCExtPropertyEnds`
* Proposition 1.1 (necessary condition for arbitrary `Γ`, p. 1258; proof in §3, p. 1262) — `prop1_1`

Reading: "a compact set `C(φ, L)` of `ℜ* = D*/Γ`" is a compact set `C ⊆ 𝕃` of the surface `𝕃/Γ` lifted to `𝕃`: every compact set of
the quotient is the image of a compact subset of `𝕃`, and its preimage is the `Γ`-orbit of that subset.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Miyachi2008

open LiZhongQC (lowerHalf toExt ExtPlane meroToExt IsFuchsian IsKQuasidisc)
open GardinerLakic2000 (cuspFormsL orbitMapsR)
open LehtoVirtanen1973 (IsKQuasiconformal)

/-- **Round disk** (p. 1257, "the image of a round disk"). A disk of `Ĉ`: the image of the unit disk under a Möbius transformation
(a disk, the complement of a closed disk, or a half-plane). -/
def IsRoundDisk (B : Set ExtPlane) : Prop :=
  ∃ M : ExtPlane → ExtPlane, LiZhongQC.IsMobius M ∧ B = M '' toExt (ball (0 : ℂ) 1)

/-- **Quasiconformal extension property at ends with respect to `Γ`** (p. 1257). An automorphic form `φ ∈ B(Γ)` has the property
when there is a constant `ε(φ) ≥ 1` such that for any `L > 1` there is a compact set `C(φ, L)` of `𝕃/Γ` (a compact `C ⊆ 𝕃` with
its `Γ`-orbit) such that for any `L`-quasidisk `D ⊆ 𝕃` avoiding the preimage of `C(φ, L)`, the restriction of the developing
mapping `f_φ` to `D` admits an `ε(φ)`-quasiconformal extension on `Ĉ`. Modelling: for every developing mapping `f` of `φ`. -/
def HasQCExtPropertyEnds (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (φ : ℂ → ℂ) : Prop :=
  φ ∈ cuspFormsL Γ ∧ ∃ ε : ℝ, 1 ≤ ε ∧ ∀ L : ℝ, 1 < L → ∃ C : Set ℂ, IsCompact C ∧ C ⊆ lowerHalf ∧
    ∀ f : ℂ → ℂ, IsDevelopingMap φ f → ∀ D : Set ℂ, D ⊆ lowerHalf → IsKQuasidisc D L →
      Disjoint D (⋃ g ∈ orbitMapsR Γ, g '' C) →
        ∃ E : ExtPlane → ExtPlane, IsKQuasiconformal E univ ε ∧ ∀ z ∈ D, E z = meroToExt f z

/-- **Proposition 1.1** (necessary condition for arbitrary `Γ`; p. 1258). Let `Γ` be a Fuchsian group. For `φ ∈ B(Γ)`, if the
equivalence class `[φ] ∈ B̂(Γ)` is contained in the image `𝒜𝒯_Γ` of `AT(D/Γ)` under the asymptotic Bers map, then `φ` has the
quasiconformal extension property at ends with respect to `Γ`. -/
theorem prop1_1 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {φ : ℂ → ℂ}
    (hφ : φ ∈ cuspFormsL Γ) (h : bHatMk Γ φ hφ ∈ asymBersImage Γ) : HasQCExtPropertyEnds Γ φ := by
  sorry

end Miyachi2008
