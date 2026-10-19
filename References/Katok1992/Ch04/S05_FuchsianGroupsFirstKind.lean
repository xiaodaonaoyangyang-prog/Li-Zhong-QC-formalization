import References.Katok1992.Ch04.S01_GeometricallyFiniteGroups

/-!
# Katok 1992, Ch. 4 §4.5 Fuchsian groups of the first kind

S. Katok, *Fuchsian Groups* (1992), Chapter 4, §4.5; source `full.md` of `Fuchsian groups (Katok, Svetlana)
…-3766f6b7…`, lines 2233–2257.

* Definition (first kind; l. 2235, from §3.4) — exists: `Katok1992.IsFirstKind`
* Theorem 4.5.1 (a geometrically finite group of the first kind has a fundamental region of finite area; l. 2237) — `thm4_5_1`
* Theorem 4.5.2 (a fundamental region of finite area forces the first kind; l. 2246) — `thm4_5_2`
* Lemma 4.5.3 (the Euclidean diameters of the translates of a locally finite region tend to zero; l. 2250) — `lemma4_5_3`
  [CORRECTION: the region must be convex, as the Dirichlet region the book uses it for; the hypothesis `HypConvex F` is added]
* Remark (Siegel's theorem is another converse; l. 2257) — omitted: remark

**Conventions.** In Lemma 4.5.3 the group acts on the unit disc `𝔘`, and `g_n(F)` is read in the disc model (`discAct` of
the elements `g_n` of `Γ`, an enumeration of `Γ` by distinct elements). `Euclidean diameter` is the diameter in `ℂ` of the image of
the translate under Katok's Cayley map, `Metric.diam (cayleyK '' …)`. A fundamental region "of finite hyperbolic area" is one
with `volume F < ⊤` (the area of the boundary is not assumed zero: it is not needed for the finiteness).
-/

open Set Filter Topology MeasureTheory Metric
open scoped UpperHalfPlane MatrixGroups ENNReal Pointwise

noncomputable section

namespace Katok1992

/-- **Theorem 4.5.1** (§4.5; l. 2237). If `Γ` is a geometrically finite Fuchsian group of the first kind, then `Γ` has a
fundamental region of finite hyperbolic area. -/
theorem thm4_5_1 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (hg : IsGeometricallyFinite Γ) (h1 : IsFirstKind Γ) :
    ∃ F : Set ℍ, IsFundamentalRegion Γ F ∧ volume F < ⊤ := by
  sorry

/-- **Theorem 4.5.2** (§4.5; l. 2246). If a Fuchsian group `Γ` has a fundamental region of finite hyperbolic area, then `Γ`
is of the first kind. -/
theorem thm4_5_2 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {F : Set ℍ} (hF : IsFundamentalRegion Γ F)
    (hμ : volume F < ⊤) : IsFirstKind Γ := by
  sorry

/-- **Lemma 4.5.3** (§4.5; l. 2250). Let `Γ = {Id, g₁, g₂, …}` be a Fuchsian group (an enumeration `g : ℕ → Γ` of the
elements by distinct elements) acting on `𝔘`, and `F` a locally finite *convex* fundamental region for `Γ`. Then the Euclidean
diameter of `g_n(F)` in the disc model tends to `0` as `n → ∞`. *Correction:* without convexity the statement is false (a disconnected locally
finite fundamental region of `⟨z ↦ 2z⟩` obtained by redistributing the tiles `2^k P_j` along a bijection `ℕ → ℤ` has all `g_n(F)` of diameter `≈ 2`);
the book's proof (the segment `[z_k, w_k]` lies in `g_{n_k}(F)`) needs convexity and is only used for a Dirichlet region. -/
theorem lemma4_5_3 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {F : Set ℍ} (hF : IsLocallyFiniteRegion Γ F)
    (hconv : References.HypConvex F) (g : ℕ → Γ) (hg : Function.Injective g) :
    Tendsto (fun n => Metric.diam (cayleyK '' (((↑) : ℍ → ℂ) '' ((g n : PSL(2, ℝ)) • F)))) atTop (𝓝 0) := by
  sorry

end Katok1992
