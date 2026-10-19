import References.Forster1981.Ch02.S17_TheSerreDualityTheorem
import LiZhongQC.Ch06.S22_RiemannSurfaces

/-!
# Hubbard 2006, Appendix A10: The Riemann–Roch theorem for Riemann surfaces

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H3` lines 1172–1519.

**Conventions.** `X` is a compact Riemann surface (`[T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
[IsManifold 𝓘(ℂ) ω X] [CompactSpace X]`) and `g` its genus in Hubbard's sense, one half of `dim_ℝ H¹(X, ℝ)`, which is the
topological genus `LiZhongQC.HasGenus X g` (the fundamental group is the surface group of genus `g`). The cohomology groups
are those of Forster §12 (`Forster1981.H1`, `Forster1981.H0`) of the sheaves `𝒪` (`Forster1981.modO`) and `Ω`
(`Forster1981.modOmega`); in Forster's text the genus *is* `dim H¹(X, 𝒪)` (`Forster1981.genus`), so Prop. A10.1.1 is the
statement that this analytic dimension equals the topological genus, which Forster does not need and does not state. Real
vector spaces: `modConstR X` is the sheaf of locally constant real functions and `modOR X` the sheaf `𝒪` regarded as a sheaf
of `ℝ`-modules (both built by Forster's generic `localRepPresheaf`); the inclusion of the real constants is the sheaf
homomorphism induced by `a ↦ (fun x ↦ (a x : ℂ))` (`Forster1981.IsInducedBy`), and the induced map of the groups
`H¹` is `Forster1981.IsH1Induced`.

**The divisor form is Forster's.** Hubbard states Riemann–Roch for analytic line bundles with the Chern class
`c₁(L) ∈ H²(X, ℤ)` (A10.0.1, A10.2.1, A10.2.5, A10.2.6); the line-bundle phrasing is deferred (it needs `H²(X, ℤ)` and the
connecting map of `0 → ℤ → 𝒪 → 𝒪* → 0`, Def. A7.4.3). The divisor form is Forster's `Forster1981.thm16_9` (`dim H⁰(X,
𝒪_D) − dim H¹(X, 𝒪_D) = 1 − g + deg D`, with the analytic genus), a near miss for A10.0.1 together with
`LiZhongQC.thm22_4_riemann_roch` (the project's divisors and the topological genus). Near misses also: `Forster1981.thm16_5`
(`deg D < 0` implies `H⁰(X, 𝒪_D) = 0`) for Cor. A10.2.4; `Forster1981.thm17_9`, `Forster1981.thm17_11` (Serre duality)
for the duality in Thm A10.3.1.

* Theorem A10.0.1 (`χ(L) = c₁(L) + 1 − g`) — deferred: analytic line bundles and the first Chern class (decision D24); divisor form
  is Forster's Riemann–Roch
* Proposition A10.1.1 (`g = dim H¹(X, 𝒪_X)`) — `propA10_1_1`
* Theorem A10.1.2 (`dim H⁰(X, Ω_X) = g`) — `thmA10_1_2`
* Theorem A10.1.3 (`H¹(X, ℝ_X) → H¹(X, ℂ_X) → H¹(X, 𝒪_X)` is an isomorphism of real vector spaces) — `modConstR`, `modOR`,
  `thmA10_1_3`
* Proposition A10.2.1, Lemmas A10.2.2, A10.2.3, Theorem A10.2.5, Corollary A10.2.6 — deferred: line bundles and `c₁` (D24);
  A10.2.2, A10.2.3 are proof steps
* Corollary A10.2.4 (`c₁(L) < 0` implies no non-zero analytic section) — deferred: line-bundle phrasing; divisor form is
  Forster's `thm16_5`
* Theorem A10.3.1 (`H⁰(Ω)` and `H¹(𝒪)` are dual, both of dimension `g`) — covered by `propA10_1_1` and `thmA10_1_2` (dimensions);
  the duality is Forster's Serre duality (near miss)
* Proposition A10.3.2 (1) (`dim H⁰(X, Ω^{⊗2}) = 3g − 3` for `g ≥ 2`) — exists:
  `LiZhongQC.thm22_5_dim_quadratic_differentials`
* Proposition A10.3.2 (2) (`H¹(X, T_X)` is dual to `H⁰(X, Ω^{⊗2})`) — deferred: the sheaf `T_X` of holomorphic vector fields and
  Serre duality for it; it belongs with Chapter 6 (the tangent space of Teichmüller space)
-/

open scoped Manifold ContDiff
open LiZhongQC Forster1981 CategoryTheory

namespace Hubbard2006

/-- **The sheaf `ℝ_X`** of locally constant real functions, as a sheaf of `ℝ`-modules (generic `localRepPresheaf`, as
`Forster1981.modC`, `modZ`). -/
abbrev modConstR (X : Type) [TopologicalSpace X] : TopCat.Presheaf (ModuleCat.{0} ℝ) (TopCat.of X) :=
  localRepPresheaf ℝ (A := X → ℝ) IsLocConstAt VanishesAt

/-- **The sheaf `𝒪_X` as a sheaf of real vector spaces**: holomorphic functions, with the same representatives and the same
vanishing relation as `Forster1981.modO`, but over the coefficient ring `ℝ`. -/
noncomputable abbrev modOR (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : TopCat.Presheaf (ModuleCat.{0} ℝ) (TopCat.of X) :=
  localRepPresheaf ℝ (A := X → ℂ) IsHolFunAt VanishesAt

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [CompactSpace X]

/-- **Proposition A10.1.1** (Appendix A10, H3:1206). Let `X` be a compact Riemann surface of genus `g`. Then `H¹(X, 𝒪_X)` is
finite dimensional and `g = dim H¹(X, 𝒪_X)`. Here `g` is the topological genus (`HasGenus`, equal to `½ dim_ℝ H¹(X, ℝ)`);
Forster takes `dim H¹(X, 𝒪)` as the *definition* of the genus, so this identification is the new content. Near miss:
`Forster1981.rem17_10_b`. -/
theorem propA10_1_1 {g : ℕ} (hX : HasGenus X g) :
    Module.Finite ℂ (H1 (modO X) ⊤) ∧ Module.finrank ℂ (H1 (modO X) ⊤) = g := by
  sorry

/-- **Theorem A10.1.2** (Appendix A10, H3:1252). If `X` is a compact Riemann surface of genus `g`, then `H⁰(X, Ω_X)` is
finite dimensional and `dim H⁰(X, Ω_X) = g`. -/
theorem thmA10_1_2 {g : ℕ} (hX : HasGenus X g) :
    Module.Finite ℂ (H0 (modOmega X)) ∧ Module.finrank ℂ (H0 (modOmega X)) = g := by
  sorry

/-- **Theorem A10.1.3** (Appendix A10, H3:1254). The composition `H¹(X, ℝ_X) → H¹(X, ℂ_X) → H¹(X, 𝒪_X)` induced by the
inclusions of sheaves `ℝ_X ⊆ ℂ_X ⊆ 𝒪_X` is an isomorphism of real vector spaces. Modelling: the composite inclusion is the
sheaf homomorphism `α : ℝ_X → 𝒪_X` of real vector spaces induced by `a ↦ (fun x ↦ (a x : ℂ))`, and `α₁` is the induced map of
the Čech groups (`IsH1Induced`); the intermediate group `H¹(X, ℂ_X)` is not needed. (So `H¹(X, ℝ_X)` gets a complex structure.)
Near misses: Forster's Dolbeault and de Rham theorems `Forster1981.thm15_14_a`, `Forster1981.thm15_15`. -/
theorem thmA10_1_3 :
    ∃ α : modConstR X ⟶ modOR X, IsInducedBy α (fun (a : X → ℝ) x => (a x : ℂ)) ∧
      ∃ α₁ : H1 (modConstR X) ⊤ →ₗ[ℝ] H1 (modOR X) ⊤, IsH1Induced (modConstR X) (modOR X) α α₁ ∧ Function.Bijective α₁ := by
  sorry

end Hubbard2006
