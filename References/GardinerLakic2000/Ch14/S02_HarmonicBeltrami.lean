import References.GardinerLakic2000.Ch14.S01_InfinitesimalTheory

/-!
# Gardiner–Lakic 2000, Ch. 14 §14.2 Harmonic Beltrami differentials

Source `teichmuller.txt`, lines 10042–10157.

* Definition (`B = B(Γ)`, harmonic Beltrami differentials, the decomposition, l. 10043–10058) — exists:
  `GardinerLakic2000.boundedCuspForms` `GardinerLakic2000.IsHarmonicBeltrami` `GardinerLakic2000.cor6_5_2_a`
* Definition (the group action as a set of maps; `b*(ν, G)` for a group `G` on a domain, l. 10060, 10466, 10577) —
  `orbitMapsR`, `orbitMapsC`, `bStarOmega`
* Definition (`B(Ω, G)` for a group of Möbius maps, l. 10331, 10582) — `boundedCuspFormsC`
* Definition (`B₀`: `ρ⁻² ψ̄` vanishes at infinity, l. 10060, 10587) — `boundedCuspForms0`
* Formula (14.5) (`Ψ_s`, l. 10096) — `poincareSeriesPsi`
* Lemma 2 (l. 10102) — `lemma14_2`

Not items (DESIGN §3): (14.3), (14.4) (`μ_ζ`, its bound, l. 10080, 10088) and (14.6), (14.7) (l. 10108, 10122):
steps of the proofs of Lemmas 1 and 2.

**Modelling (calibration D0.8).** A group of Möbius maps acting on a plane domain `Ω` is given by its set of maps
(`orbitMapsR` for `Γ ≤ SL(2, ℝ)`, `orbitMapsC` for `G ≤ SL(2, ℂ)`). A compact set `C` of `Ω/G` is the image of a
compact `K ⊆ Ω`, and `π⁻¹(C)` is the orbit `G(K)`; so `b*(ν, G) = inf_K ‖ν‖_{L∞(Ω ∖ G(K))}`. `B₀` is the subspace of
a space `B` of cusp forms with `b*(ρ⁻² ψ̄, G) = 0` (`ρ` the Poincaré density of Part A, `poincareDensityGL`), for
`ψ` continuous the book's "`|ρ⁻² ψ|` vanishes at infinity on `Ω/G`". The disc model of Lemma 2 is read on `Δ` through
the Cayley transform: `Γ ≤ SL(2, ℝ)` acts on `Δ` by `C ∘ γ ∘ C⁻¹` (A0.2), and `Ψ_s(ζ) = Σ_γ (1 − |γ(ζ)|²)^s`; its
convergence is summability over `Γ` (absolute, the terms being positive). The sum runs over the matrices, so a Möbius
map is counted twice when `−I ∈ Γ`; Lemma 2 is insensitive to this.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (IsFuchsian upperHalf unitDisc cayley cayleyInv)

/-- Helper (§14.2). The Möbius maps `z ↦ (az + b)/(cz + d)` of a subgroup of `SL(2, ℝ)`. -/
def orbitMapsR (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → ℂ) :=
  {g | ∃ γ ∈ Γ, g = fun z : ℂ => ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)}

/-- Helper (§14.4). The Möbius maps `z ↦ (az + b)/(cz + d)` of a subgroup of `SL(2, ℂ)`. -/
def orbitMapsC (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) : Set (ℂ → ℂ) :=
  {g | ∃ γ ∈ G, g = fun z => (γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)}

/-- **Definition** (`b*(ν, G)`, §14.2 l. 10060, §14.5 l. 10466, §14.7 l. 10577). The infimum, over compact `K ⊆ Ω`, of
the essential supremum of `|ν|` on `Ω` minus the orbit `G(K)`. -/
def bStarOmega (G : Set (ℂ → ℂ)) (Ω : Set ℂ) (ν : ℂ → ℂ) : ℝ≥0∞ :=
  ⨅ (K : Set ℂ) (_ : IsCompact K ∧ K ⊆ Ω), eLpNorm ν ⊤ (volume.restrict (Ω \ ⋃ g ∈ G, g '' K))

/-- **Definition** (`B(Ω, G)`, §14.4 l. 10331, §14.7 l. 10582). Holomorphic `φ` on `Ω` with `φ(γ(z)) γ′(z)² = φ(z)`
for `γ ∈ G` and `‖ρ⁻² φ‖∞ < ∞` (`G ≤ SL(2, ℂ)`, `γ′(z) = (cz + d)⁻²`). -/
def boundedCuspFormsC (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) (Ω : Set ℂ) : Set (ℂ → ℂ) :=
  {φ | DifferentiableOn ℂ φ Ω ∧ (∀ γ ∈ G, ∀ z ∈ Ω,
      φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / (γ 1 0 * z + γ 1 1) ^ 4 = φ z) ∧
    cuspNorm Ω φ < ⊤}

/-- **Definition** (`B₀`, §14.2 l. 10060, §14.7 l. 10587). The `ψ` of the space `B` of cusp forms on `Ω` (for the
group maps `G`) with `b*(ρ⁻² ψ̄, G) = 0`. -/
def boundedCuspForms0 (G : Set (ℂ → ℂ)) (Ω : Set ℂ) (B : Set (ℂ → ℂ)) : Set (ℂ → ℂ) :=
  {ψ | ψ ∈ B ∧ bStarOmega G Ω (fun z => (poincareDensityGL Ω z ^ (-2 : ℤ) : ℝ) * conj (ψ z)) = 0}

/-- **Formula (14.5)** (§14.2, l. 10096). `Ψ_s(ζ) = Σ_{γ ∈ Γ} (1 − |γ(ζ)|²)^s` on `Δ`, for `Γ` acting on `Δ` through the
Cayley transform. -/
def poincareSeriesPsi (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (s : ℝ) (ζ : ℂ) : ℝ :=
  ∑' γ : Γ, (1 - ‖cayley ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℂ) * cayleyInv ζ +
    ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 : ℂ)) / (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) *
      cayleyInv ζ + ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℂ)))‖ ^ 2) ^ s

/-- **Lemma 2** (§14.2, l. 10102; [EGL98b]). For every `s > 1` the series (14.5) converges absolutely, and the function
`F_s` it induces on `R = Δ/Γ` vanishes at infinity: for every `ε > 0` there is a compact `K ⊆ Δ` with `Ψ_s < ε` off the
orbit `Γ(K)`. -/
theorem lemma14_2 {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {s : ℝ} (hs : 1 < s) :
    (∀ ζ ∈ unitDisc, Summable fun γ : Γ =>
      (1 - ‖cayley ((((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 0 : ℂ) * cayleyInv ζ +
        ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 0 1 : ℂ)) / (((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 0 : ℂ) *
          cayleyInv ζ + ((γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) 1 1 : ℂ)))‖ ^ 2) ^ s) ∧
    ∀ ε > 0, ∃ K : Set ℂ, IsCompact K ∧ K ⊆ unitDisc ∧
      ∀ ζ ∈ unitDisc \ ⋃ g ∈ orbitMapsR Γ, (fun w => cayley (g (cayleyInv w))) '' K, poincareSeriesPsi Γ s ζ < ε := by
  sorry

end GardinerLakic2000
