import References.FarkasKra1992.Ch01.S01_DefinitionsAndExamples
import References.Lehto1987.Ch04.S02_TopologyOfCoveringSurfaces
import References.Forster1981.Ch01.S05_TheUniversalCoveringAndCoveringTransformations
import References.Forster1981.Ch02.S17_TheSerreDualityTheorem

/-!
# Farkas–Kra, Chapter I §2: Topology of Riemann surfaces

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. I §2 (`full.md` FK1:632–854).

Conventions: as in `Ch01/S01_DefinitionsAndExamples`. The first homology group is `H₁(M) = Abelianization(π₁(M))`
(Hurewicz; leader ruling, 2026-10-09); simplicial homology and triangulations are deferred (W-TOP: triangulation not
available). The genus is `LiZhongQC.HasGenus M g` (a compact surface whose fundamental group is the surface group of
genus `g`). The total branching number of a holomorphic map is `totalBranching f = Σ_P b_f(P)`, `b_f(P) = multiplicity − 1`.

* I.2.1–I.2.2 (curves, the fundamental group, homotopy) — exists: `FundamentalGroup`
* I.2.3 (simplicial homology, Betti numbers) — deferred: triangulation not available (W-TOP); `H₁` is the abelianization of the fundamental group
* I.2.4 (ramified covering manifolds, branch points) — exists: `Forster1981.IsHolomorphicCovering`
* I.2.4 (monodromy theorem) — exists: `LiZhongQC.thm22_1_monodromy`
* I.2.4 (the universal covering, `G ≅ π₁(M)`) — exists: `LiZhongQC.exists_universal_covering`, `Forster1981.thm5_6_b`, `Lehto1987.thm4_2_4`
* I.2.5 (normal forms, genus, presentation of `π₁`) — exists: `LiZhongQC.HasGenus`, `LiZhongQC.closed_surface_has_genus`
* I.2.5 (`H₁(M) ≅ ℤ^{2g}`, `β₁ = 2g`) — `para1_2_5`
* I.2.6 (Euler–Poincaré characteristic) — deferred: triangulation not available (W-TOP)
* Theorem I.2.7 (Riemann–Hurwitz relation) — exists: `Forster1981.thm17_14`
* Definition I.2.7 (total branching number) — `totalBranching`
* Corollary I.2.8, part 1 — `cor1_2_8_a`
* Corollary I.2.8, part 2 (a) — `cor1_2_8_b_a`
* Corollary I.2.8, part 2 (b) — `cor1_2_8_b_b`
* Corollary I.2.8, part 2 (c) — `cor1_2_8_b_c`
* Corollary I.2.8, part 3 (a) — `cor1_2_8_c`
* Corollary I.2.8, part 3 (b) — deferred: OCR unreadable (only "1 ≤ g = γ" survives in the text layer)
-/

open scoped Manifold ContDiff Topology References
open Set Filter

noncomputable section

namespace FarkasKra1992

open LiZhongQC (HasGenus)

/-- **The total branching number** (Ch. I §2.7). For a holomorphic map `f : M → N` of compact Riemann surfaces,
`B = Σ_{P ∈ M} b_f(P)`, with the branch number `b_f(P) = n − 1` at a point where `f` has multiplicity `n`
(`Forster1981.multiplicity`). Modelling: `finsum` in `ℕ∞`; the sum is finite for a non-constant `f` on a compact `M`. -/
def totalBranching {M N : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] (f : M → N) : ℕ∞ := ∑ᶠ P : M, (Forster1981.multiplicity f P - 1)

/-- **Unlabelled** (Ch. I §2.5, FK1:714). For a compact surface `M` of genus `g`, `H₁(M)` is the free abelian group on
the generators `[a_j], [b_j]`, `j = 1, …, g`: `H₁(M) ≅ ℤ^{2g}`, `β₁ = 2g`.
Modelling: `H₁` is the abelianization of `π₁(M)`; the isomorphism is of additive groups. -/
theorem para1_2_5 {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] {g : ℕ} (hM : HasGenus M g) (x : M) :
    Nonempty (Additive (Abelianization (FundamentalGroup M x)) ≃+ (Fin (2 * g) → ℤ)) := by
  sorry

section Hurwitz

variable {M N : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
  [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N]

/-- **Corollary I.2.8, part 1** (Ch. I §2.8, Corollary 1). Let `f : M → N` be a non-constant holomorphic mapping between
compact Riemann surfaces. The total branching number `B` is always even. -/
theorem cor1_2_8_a [CompactSpace M] [CompactSpace N] {f : M → N} {n : ℕ} (hf : Forster1981.IsHolomorphicCovering f n) :
    ∃ k : ℕ, totalBranching f = 2 * k := by
  sorry

/-- **Corollary I.2.8, part 2 (a)** (Ch. I §2.8, Corollary 2). Assume that `f : M → N` is unramified, of degree `n`, with
`M` of genus `g` and `N` of genus `γ`. If `g = 0` then `n = 1` and `γ = 0`. -/
theorem cor1_2_8_b_a {g γ n : ℕ} (hM : HasGenus M g) (hN : HasGenus N γ) {f : M → N}
    (hf : Forster1981.IsHolomorphicCovering f n) (hu : Forster1981.IsUnbranched f) (hg : g = 0) :
    n = 1 ∧ γ = 0 := by
  sorry

/-- **Corollary I.2.8, part 2 (b)** (Ch. I §2.8, Corollary 2). In the situation of part 2 (a): if `g = 1` then `γ = 1`
(`n` arbitrary). -/
theorem cor1_2_8_b_b {g γ n : ℕ} (hM : HasGenus M g) (hN : HasGenus N γ) {f : M → N}
    (hf : Forster1981.IsHolomorphicCovering f n) (hu : Forster1981.IsUnbranched f) (hg : g = 1) : γ = 1 := by
  sorry

/-- **Corollary I.2.8, part 2 (c)** (Ch. I §2.8, Corollary 2). In the situation of part 2 (a): if `g > 1`, then `g = γ`
for `n = 1`, and `g > γ > 1` for `n > 1` (and `n` divides `g − 1`). -/
theorem cor1_2_8_b_c {g γ n : ℕ} (hM : HasGenus M g) (hN : HasGenus N γ) {f : M → N}
    (hf : Forster1981.IsHolomorphicCovering f n) (hu : Forster1981.IsUnbranched f) (hg : 1 < g) :
    (n = 1 → g = γ) ∧ (1 < n → γ < g ∧ 1 < γ ∧ n ∣ g - 1) := by
  sorry

/-- **Corollary I.2.8, part 3 (a)** (Ch. I §2.8, Corollary 3). Let `f : M → N` be a non-constant holomorphic mapping
between compact Riemann surfaces of genera `g` and `γ`. If `g = 0`, then `γ = 0`. -/
theorem cor1_2_8_c {g γ n : ℕ} (hM : HasGenus M g) (hN : HasGenus N γ) {f : M → N}
    (hf : Forster1981.IsHolomorphicCovering f n) (hg : g = 0) : γ = 0 := by
  sorry

end Hurwitz

end FarkasKra1992
