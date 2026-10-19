import References.GardinerLakic2000.Ch14.S03_EarleNagReflection

/-!
# Gardiner–Lakic 2000, Ch. 14 §14.4 Generalized Ahlfors–Weill sections

Source `teichmuller.txt`, lines 10316–10422.

* Definition (`L∞(Ω, Γ)`, l. 10325–10328) — `beltramiSpaceOmega`
* Definition (`B(Ω, Γ)`, l. 10331) — exists: `GardinerLakic2000.boundedCuspFormsC`
* Formula (14.17) (`s(φ)`, l. 10337) — `awSection`
* Definition (the map `𝒮`: the Schwarzian of the map with coefficient `μ` in `Ω*`, conformal in `Ω`, l. 10343–10345) —
  `bersMapOmega`
* Theorem 3 ([Ahl64], [EN86], l. 10359) — `thm14_3`

Not items (DESIGN §3): the automorphy of `𝒮(μ)` and the bound `12` (l. 10347–10357, recalled from Ch. 6), and
(14.18)–(14.22) (l. 10375–10414, the proof).

**Modelling.** The configuration is `IsQCConfiguration` (normalized by `∞ ∈ C`) with a quasi-Fuchsian group
`Γ ≤ SL(2, ℂ)` (`LiZhongQC.IsQuasiFuchsian Γ C`: `C` and its complementary domains are `Γ`-invariant), and `j` its
Earle–Nag reflection (its conformal naturality (14.16) is a consequence, l. 10214). `j_z`, `j_z̄` are
`LiZhongQC.dz`/`dzbar`. `𝒮(μ)` is the Schwarzian (`LiZhongQC.schwarzian`), on `Ω`, of the normalized solution
`LiZhongQC.normalizedSolution` of the Beltrami equation with coefficient `μ` on `Ω*` and `0` on `Ω`; it does not depend
on the Möbius normalization (l. 10347). `L∞(Ω, Γ)` consists of the essentially bounded `μ` on `Ω` with
`μ(γ(z)) conj (γ′(z)) = μ(z) γ′(z)` a.e., `γ′(z) = (cz + d)⁻²`. "`s(φ)` is a section of `𝒮`" includes that `s(φ)` lies
in the unit ball of `L∞(Ω*, Γ)`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (ExtPlane IsQuasiFuchsian schwarzian normalizedSolution dz dzbar)

/-- **Definition** (`L∞(Ω, Γ)`, §14.4, l. 10325–10328). Essentially bounded measurable `μ` on `Ω` with
`μ(γ(z)) conj (γ′(z)) = μ(z) γ′(z)` a.e. on `Ω` for `γ ∈ Γ`. -/
def beltramiSpaceOmega (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) (Ω : Set ℂ) : Set (ℂ → ℂ) :=
  {μ | AEStronglyMeasurable μ (volume.restrict Ω) ∧ eLpNorm μ ⊤ (volume.restrict Ω) < ⊤ ∧
    ∀ γ ∈ G, ∀ᵐ z ∂(volume.restrict Ω),
      μ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) * conj (((γ 1 0 * z + γ 1 1) ^ 2)⁻¹) =
        μ z * ((γ 1 0 * z + γ 1 1) ^ 2)⁻¹}

/-- **Formula (14.17)** (§14.4, l. 10337).
`s(φ)(z) = (z − j(z))² φ(j(z)) j_z̄(z) / (2 + φ(j(z)) (z − j(z))² j_z(z))`. -/
def awSection (j : ℂ → ℂ) (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z - j z) ^ 2 * φ (j z) * dzbar j z / (2 + φ (j z) * (z - j z) ^ 2 * dz j z)

/-- **Definition** (the map `𝒮`, §14.4, l. 10343–10345). `𝒮(μ)` is the Schwarzian derivative, on `Ω`, of a
quasiconformal self-map of `ℂ̄` with Beltrami coefficient `μ` in `Ω*` and `0` in `Ω` (extended by `0` off `Ω`). -/
def bersMapOmega (Ω Ωs : Set ℂ) (μ : ℂ → ℂ) : ℂ → ℂ :=
  Ω.indicator (schwarzian (normalizedSolution (Ωs.indicator μ)))

/-- **Theorem 3** (§14.4, l. 10359; [Ahl64], [EN86]). For a configuration `Ω, C, Ω*` with a `K`-quasiconformal
(Earle–Nag) reflection `j`, invariant under a quasi-Fuchsian group `Γ`, `s : B(Ω, Γ) → L∞(Ω*, Γ)` is a section of `𝒮`:
there is `ε = ε(K) > 0` such that `‖φ ρ⁻²‖∞ < ε` implies `𝒮 ∘ s(φ) = φ`. -/
theorem thm14_3 (K : ℝ) : ∃ ε : ℝ, 0 < ε ∧ ∀ (C : Set ExtPlane) (Ω Ωs : Set ℂ) (j : ℂ → ℂ)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)), IsQCConfiguration C Ω Ωs → IsQuasiFuchsian Γ C →
    IsEarleNagReflection C Ω Ωs j → IsReflectionGL C Ω Ωs j K → ∀ φ ∈ boundedCuspFormsC Γ Ω,
      cuspNorm Ω φ < ENNReal.ofReal ε →
      awSection j φ ∈ beltramiSpaceOmega Γ Ωs ∧ eLpNorm (awSection j φ) ⊤ (volume.restrict Ωs) < 1 ∧
        ∀ z ∈ Ω, bersMapOmega Ω Ωs (awSection j φ) z = φ z := by
  sorry

end GardinerLakic2000
