import LiZhongQC.Ch06.S22_RiemannSurfaces
import References.Common.RiemannSphere

/-!
# Hubbard 2006, Chapter 1 §1.1: Two statements of the uniformization theorem

Source: J. H. Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 350–390 (OCR `full.md`, folder `…-d20b3cc3-…`).

**Conventions.** A Riemann surface is the bundle `[TopologicalSpace X] [T2Space X] [ConnectedSpace X]
[ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]` of `References/Common/RiemannSurface.lean` (no second countability; Radó's
theorem, Thm 1.3.3, then proves it). `ℙ¹` is `References.RiemannSphere` (scoped charts, `open scoped References`), `𝔻`
is
`LiZhongQC.unitDiscOpens`. `H¹(X, ℝ)` is modelled as `Hom(π₁(X, x), ℝ)` (the book recalls this identification at H1:364;
there is no singular cohomology in the project): `HasTrivialH1 X` says every homomorphism `π₁(X, x) → (ℝ, +)` is
trivial.

* Theorem 1.1.1 (uniformization: a simply connected Riemann surface is `ℙ¹`, `ℂ` or `𝔻`) — exists:
  `LiZhongQC.thm22_2_uniformization` (LZ: compact with the complement of a point isomorphic to the plane, or the plane,
  or the disc, and exactly one; equivalent to Hubbard's by the removable singularity theorem)
* Definition (`H¹(X, ℝ) = 0`, §1.1) — `HasTrivialH1`
* Theorem 1.1.2 (noncompact, `H¹ = 0` ⇒ `ℂ` or `𝔻`) — `thm1_1_2`
* Theorem 1.1.3 (compact, `H¹ = 0` ⇒ `ℙ¹`) — `thm1_1_3`
* Lemma 1.1.4 (compact, `H¹ = 0` ⇒ `H¹(X ∖ {x}) = 0`) — `lemma1_1_4`
* Lemma 1.1.5 (`𝔻 ∪ {∞}` has no Riemann surface structure extending that of `𝔻`) — `lemma1_1_5`
-/

open scoped Manifold ContDiff Topology References
open LiZhongQC

namespace Hubbard2006

/-- **`H¹(X, ℝ) = 0`** (Ch. 1 §1.1, used in Thm 1.1.2–1.1.3, Lemma 1.1.4, Prop. 1.4.1, 1.6.1). Modelling: `H¹(X, ℝ) =
Hom(π₁(X, x), ℝ)` (the book's own recollection, H1:364), so the condition is that every homomorphism from the
fundamental group at any base point to `(ℝ, +)` (written multiplicatively) is trivial. For a path connected space the
condition does not depend on the base point. -/
def HasTrivialH1 (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∀ f : FundamentalGroup X x →* Multiplicative ℝ, f = 1

/-- **Theorem 1.1.2** (Ch. 1 §1.1, H1:360). A connected noncompact Riemann surface `X` with `H¹(X, ℝ) = 0` is
isomorphic to `ℂ` or to `𝔻`. -/
theorem thm1_1_2 {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (hX : ¬ CompactSpace X) (h : HasTrivialH1 X) :
    RSConformallyEquivalent X ℂ ∨ RSConformallyEquivalent X unitDiscOpens := by
  sorry

/-- **Theorem 1.1.3** (Ch. 1 §1.1, H1:368). A connected compact Riemann surface `X` with `H¹(X, ℝ) = 0` is isomorphic to
`ℙ¹`. -/
theorem thm1_1_3 {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [CompactSpace X] (h : HasTrivialH1 X) :
    RSConformallyEquivalent X References.RiemannSphere := by
  sorry

/-- **Lemma 1.1.4** (Ch. 1 §1.1, H1:372). If `X` is a compact connected Riemann surface with `H¹(X, ℝ) = 0`, then
`H¹(X ∖ {x}, ℝ) = 0` for every `x ∈ X`. Modelling: `X ∖ {x}` is the open subsurface `{x}ᶜ`. -/
theorem lemma1_1_4 {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [CompactSpace X] (h : HasTrivialH1 X) (x : X) :
    HasTrivialH1 (⟨{x}ᶜ, isOpen_compl_singleton⟩ : TopologicalSpace.Opens X) := by
  sorry

/-- **Lemma 1.1.5** (Ch. 1 §1.1, H1:384). The one-point compactification `𝔻 ∪ {∞}` of the open unit disc carries no
Riemann surface structure for which the inclusion `𝔻 → 𝔻 ∪ {∞}` is holomorphic. Modelling: "coinciding with the standard
structure on `𝔻`" is "the inclusion is a holomorphic map"; the inclusion is an open embedding, and an injective
holomorphic map between Riemann surfaces is a biholomorphism onto its open image, so this is the same condition. -/
theorem lemma1_1_5 :
    ¬ ∃ c : ChartedSpace ℂ (OnePoint unitDiscOpens),
      letI := c
      IsManifold 𝓘(ℂ) ω (OnePoint unitDiscOpens) ∧
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : unitDiscOpens => (x : OnePoint unitDiscOpens)) := by
  sorry

end Hubbard2006
