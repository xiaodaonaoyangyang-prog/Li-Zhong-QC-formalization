import References.Katok1992.Ch02.S04_ElementaryGroups

/-!
# Katok 1992, Ch. 3 §3.1 Definition of a fundamental region

S. Katok, *Fuchsian Groups* (1992), Chapter 3 *Fundamental Regions*, §3.1; source `full.md` of
`Fuchsian groups (Katok, Svetlana) …-3766f6b7…`, lines 1193–1282.

* Definition (fundamental region, boundary, tessellation; l. 1197–1207) — `IsFundamentalRegion`
* Example B (a fundamental region for `z ↦ 2z`; l. 1209–1214) — omitted: example with figures
* Theorem 3.1.1 (the area of a fundamental region; l. 1217) — `thm3_1_1`
* Theorem 3.1.2 (fundamental region of a subgroup of finite index; l. 1253) — `thm3_1_2`

**Conventions.** The group is `Γ ≤ PSL(2, ℝ)` (`Katok1992.IsFuchsian`) acting on `ℍ` by `pslAction`; a fundamental region
for a general group `G` acting on a topological space `X` is `IsFundamentalRegion G F`: the book's *closed region*
`F = closure F̊` for a non-empty open set `F̊`, which it calls the interior of `F`, is read with `F̊ = interior F`
(so `∂F = F ∖ interior F = frontier F`, as `F` is closed), together with (i) `⋃ T F = X` and (ii) `F̊ ∩ T F̊ = ∅`
for `T ≠ Id`. The book's standing hypothesis (`G` acts properly discontinuously) is not part of the definition; the
theorems carry it as the Fuchsian hypothesis. *Connectedness is not assumed*: the book's *region* is connected, the definition
only asks `closure (interior F) = F`; statements that need connectedness or convexity (Lemma 4.5.3) carry it as a hypothesis. The hyperbolic area `μ` is `MeasureTheory.volume` on `ℍ` (Mathlib's
measure `dx dy / y²`, see Ch. 1 §1.4). The tessellation `{T F | T ∈ G}` is the family `fun T : G => T • F`.

**Near misses.** `LiZhongQC.IsFundamentalDomainH` (a measurable `F ⊆ ℍ` meeting every orbit exactly once up to null
sets), `Hubbard2006.IsFundamentalDomainTop` (a set meeting every orbit at most once whose closure meets every orbit),
`Lehto1987.IsFundamentalRegion`, `FarkasKra1992.IsFundamentalDomainFK` (for Kleinian groups): all of them are
different definitions from Katok's closed region with the interior condition; `GardinerLakic2000.dirichletDomain`
lives in `Set ℂ` for subgroups of `SL(2, ℝ)`.
-/

open Set MeasureTheory
open scoped UpperHalfPlane MatrixGroups Pointwise

noncomputable section

namespace Katok1992

/-- **Definition** (§3.1; l. 1197–1207). `F ⊆ X` is a *fundamental region* for the group `G` acting on `X` if `F` is a
closed region (the closure of its non-empty interior) such that (i) `⋃_{T ∈ G} T F = X` and (ii) `F̊ ∩ T F̊ = ∅` for all
`T ∈ G − {Id}`. Modelling: `F̊ = interior F` (see the module docstring). -/
def IsFundamentalRegion (G : Type*) {X : Type*} [Group G] [MulAction G X] [TopologicalSpace X] (F : Set X) : Prop :=
  IsClosed F ∧ (interior F).Nonempty ∧ closure (interior F) = F ∧ (⋃ T : G, T • F) = univ ∧
    ∀ T : G, T ≠ 1 → interior F ∩ T • interior F = ∅

/-- **Theorem 3.1.1** (§3.1; l. 1217–1250; cited in §3.1, §3.6, §4.3). Let `F₁` and `F₂` be two fundamental regions for a
Fuchsian group `Γ` with `μ(F₁) < ∞`. Suppose that the boundaries of `F₁` and `F₂` have zero hyperbolic area. Then
`μ(F₂) = μ(F₁)`. Modelling: `μ` is `volume` on `ℍ`. -/
theorem thm3_1_1 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {F₁ F₂ : Set ℍ} (h₁ : IsFundamentalRegion Γ F₁)
    (h₂ : IsFundamentalRegion Γ F₂) (hμ : volume F₁ < ⊤) (hb₁ : volume (frontier F₁) = 0)
    (hb₂ : volume (frontier F₂) = 0) : volume F₂ = volume F₁ := by
  sorry

/-- **Theorem 3.1.2** (§3.1; l. 1253–1281). Let `Γ` be a Fuchsian group and `Λ` a subgroup of index `n`, with the
decomposition `Γ = Λ T₁ ∪ ⋯ ∪ Λ T_n` into cosets (`T : Fin n → Γ` runs through a system of representatives of the right
cosets: every element of `Γ` is `S T_i` for exactly one `i` and one `S ∈ Λ`), and let `F` be a fundamental region for
`Γ`. Then (i) `F₁ = T₁ F ∪ ⋯ ∪ T_n F` is a fundamental region for `Λ`, and (ii) if `μ(F)` is finite and the hyperbolic
area of the boundary of `F` is zero, then `μ(F₁) = n μ(F)`. -/
theorem thm3_1_2 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {Λ : Subgroup PSL(2, ℝ)} (hΛ : Λ ≤ Γ) {n : ℕ}
    (T : Fin n → PSL(2, ℝ)) (hT : ∀ i, T i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : Fin n, ∃ S ∈ Λ, γ = S * T i) {F : Set ℍ} (hF : IsFundamentalRegion Γ F) :
    IsFundamentalRegion Λ (⋃ i, T i • F) ∧
      (volume F < ⊤ → volume (frontier F) = 0 → volume (⋃ i, T i • F) = n * volume F) := by
  sorry

end Katok1992
