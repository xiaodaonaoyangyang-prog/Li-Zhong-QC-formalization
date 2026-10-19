import References.Miyachi2008.S07_FailureOfDensity

/-!
# Miyachi 2008, §8: Points in the closure of `𝒜𝒯₁`

H. Miyachi, *Image of asymptotic Bers map*, J. Math. Soc. Japan **60** (2008), 1255–1276; journal pages `p. n`.
Conventions: as in `S02_AsymptoticBersMap` (half-plane model: `D*` is `𝕃`, `Γ = 1` is `⊥`; `f` is a developing mapping of `φ`).
The Riemann surface `Σ_φ`, the image of `D*` under `f_φ` regarded as a surface spread over `Ĉ`, is represented by `D*` itself
(the biholomorphic map `f̂_φ : D* → Σ_φ` is the identity of `𝕃`, the projection `pr_φ` is `f_φ`): a `K`-quasiconformal mapping `g` on
`Σ_φ` is a `K`-quasiconformal mapping `g ∘ f̂_φ` on `𝕃`; a compact set of `Σ_φ` is a compact set of `𝕃`; a univalent disk `B` of `Σ_φ`
(a set on which `pr_φ` is injective with round-disk image) is an open `B ⊆ 𝕃` on which `f_φ` is injective with `f_φ(B)` a round disk;
`g ∘ (pr_φ|_B)⁻¹` on `pr_φ(B) = f_φ(B)` is `w = f_φ(z) ↦ g(z)`.

* Theorem 3 (characterization of the preimage of the closure, p. 1259; proof §8, pp. 1271–1274) — `thm3`
* Theorem 4 (the simpler characterization, p. 1274) — `thm4`

Omitted (U−): Lemma 8.1 (the quotient norm `‖[φ]‖^ ≤ 2 limsup (1 − |z|²)² |φ(z)|`, p. 1272), the necessity and sufficiency
computations (§8.1–§8.2).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Miyachi2008

open LiZhongQC (lowerHalf toExt ExtPlane meroToExt)
open GardinerLakic2000 (cuspFormsL)
open LehtoVirtanen1973 (IsKQuasiconformal)

/-- **Theorem 3** (characterization of the preimage of the closure; p. 1259). For `φ ∈ B(1)`, the class `[φ]` is in the closure
`cl(𝒜𝒯₁)` of `𝒜𝒯₁` in `B̂(1)` if and only if for any `K, L > 1` there are a `K`-quasiconformal mapping `g` on `Σ_φ` onto a quasidisk
and a compact set `C` in `Σ_φ` such that for any univalent disk `B` in `Σ_φ ∖ C`, `g ∘ (pr_φ|_B)⁻¹ : pr_φ(B) → Ĉ` admits an
`L`-quasiconformal extension on `Ĉ`. -/
theorem thm3 {φ : ℂ → ℂ} (hφ : φ ∈ cuspFormsL ⊥) {f : ℂ → ℂ} (hf : IsDevelopingMap φ f) :
    bHatMk ⊥ φ hφ ∈ hatClosure ⊥ (asymBersImage ⊥) ↔
      ∀ K L : ℝ, 1 < K → 1 < L → ∃ g : ExtPlane → ExtPlane, IsKQuasiconformal g (toExt lowerHalf) K ∧
        References.IsQuasidiskExt (g '' toExt lowerHalf) ∧ ∃ C : Set ℂ, IsCompact C ∧ C ⊆ lowerHalf ∧
          ∀ B : Set ℂ, IsOpen B → B ⊆ lowerHalf \ C → InjOn (meroToExt f) B → IsRoundDisk (meroToExt f '' B) →
            ∃ E : ExtPlane → ExtPlane, IsKQuasiconformal E univ L ∧ ∀ z ∈ B, E (meroToExt f z) = g z := by
  sorry

/-- **Theorem 4** (p. 1274). For `φ ∈ B(1)`, the class `[φ]` is in the closure `cl(𝒜𝒯₁)` of `𝒜𝒯₁` in `B̂(1)` if and only if for any
`K, L > 1`, there are a `K`-quasiconformal mapping `g` on `D*` onto a quasidisk `Ω` and a compact set `C` in `Ω` such that for any round
disk `B` in `Ω ∖ C`, the restriction `(f_φ ∘ g⁻¹)|_B` admits an `L`-quasiconformal extension on `Ĉ`. -/
theorem thm4 {φ : ℂ → ℂ} (hφ : φ ∈ cuspFormsL ⊥) {f : ℂ → ℂ} (hf : IsDevelopingMap φ f) :
    bHatMk ⊥ φ hφ ∈ hatClosure ⊥ (asymBersImage ⊥) ↔
      ∀ K L : ℝ, 1 < K → 1 < L → ∃ g : ExtPlane → ExtPlane, IsKQuasiconformal g (toExt lowerHalf) K ∧
        References.IsQuasidiskExt (g '' toExt lowerHalf) ∧ ∃ C : Set ExtPlane, IsCompact C ∧ C ⊆ g '' toExt lowerHalf ∧
          ∀ B : Set ExtPlane, IsRoundDisk B → B ⊆ g '' toExt lowerHalf \ C →
            ∃ E : ExtPlane → ExtPlane, IsKQuasiconformal E univ L ∧
              ∀ z : ℂ, z ∈ lowerHalf → (g z) ∈ B → E (g z) = meroToExt f z := by
  sorry

end Miyachi2008
