import References.Hubbard2006.Ch01.S01_TwoStatements
import References.Forster1981.Ch01.S05_TheUniversalCoveringAndCoveringTransformations
import References.GardinerLakic2000.Ch02.S07_FuchsianGroups

/-!
# Hubbard 2006, Chapter 1 §1.8: A first classification of Riemann surfaces

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 748–915 (§1.7, `H1` 730–747, has only a proof-step
proposition, 1.7.1, which is not an item).

**Conventions.** Riemann surfaces as in `S01_TwoStatements`; `Aut X` is the group of biholomorphic self-maps
(`LiZhongQC.IsBiholomorphic`); "universal covering" is `Forster1981.IsUniversalCovering` together with holomorphy of the
covering map; `ℙ¹ = References.RiemannSphere`, `𝔻 = LiZhongQC.unitDiscOpens`.
*Hyperbolic* (Def. 1.8.9, "the universal covering space is isomorphic to `𝔻`") is modelled in the project's idiom with
`ℍ` (Cayley: `ℍ ≅ 𝔻`): `X = ℍ/Γ` for a torsion-free Fuchsian group, i.e. a holomorphic covering from the simply
connected `ℍ`, which is a universal covering. All later "universal covering `𝔻 → X`" statements of the program read
`(Γ, p)` with `IsUniformization Γ p`.

* Definition 1.8.1 (Möbius transformation) — exists: `LiZhongQC.IsMobius`
* Theorem 1.8.2 (1) (`Aut ℙ¹` = the Möbius transformations) — `thm1_8_2_a`
* Theorem 1.8.2 (2) (`Aut ℂ` = the maps `z ↦ az + b`, `a ≠ 0`) — `thm1_8_2_b`
* Theorem 1.8.2 (3) (`Aut 𝔻` = the maps `z ↦ (az + b)/(b̄z + ā)`, `|a|² > |b|²`) — `thm1_8_2_c`
* Proposition 1.7.1 (the maps `φ_n` form a normal family) — omitted: proof step of Thm 1.1.2
* Remark 1.8.5, Exercises 1.8.3, 1.8.4, 1.8.6, 1.8.7, 1.8.10, 1.8.11 — omitted: remark and exercises
* Theorem 1.8.8 (1) (`ℙ¹` is the universal cover only of itself) — `thm1_8_8_a`
* Theorem 1.8.8 (2) (`ℂ` is the universal cover of `ℂ`, of `ℂ ∖ {a}` and of the tori, and of nothing else) —
  `thm1_8_8_b`
* Theorem 1.8.8 (3) (all other surfaces have universal covering `𝔻`) — `thm1_8_8_c`
* Definition 1.8.9 (hyperbolic Riemann surface) — `IsHyperbolicRS`
* Definition 1.8.12 (finite type) — `IsFiniteTypeRS`
* Definition 1.8.13 (Fuchsian group) — exists: `LiZhongQC.IsFuchsian`
* Definition 1.8.13 (Kleinian group) — `IsKleinianGroup`
* Proposition 1.8.14 (the quotient `𝔻/Γ` by a torsion-free Fuchsian group has a unique Riemann surface structure making
  the
  projection a local isomorphism) — exists: `GardinerLakic2000.thm2_2_c`, `GardinerLakic2000.thm2_2_d`
-/

open scoped Manifold ContDiff Topology References
open LiZhongQC ComplexConjugate

namespace Hubbard2006

/-- **Theorem 1.8.2 (1)** (Ch. 1 §1.8, H1:760). `Aut ℙ¹` is the group of all Möbius transformations: a self-map of `ℙ¹`
is biholomorphic iff it is a fractional linear transformation. -/
theorem thm1_8_2_a (f : References.RiemannSphere → References.RiemannSphere) :
    IsBiholomorphic f ↔ IsMobius f := by
  sorry

/-- **Theorem 1.8.2 (2)** (Ch. 1 §1.8, H1:760). `Aut ℂ` is the group of the maps `z ↦ az + b` with `a ≠ 0`. -/
theorem thm1_8_2_b (f : ℂ → ℂ) : IsBiholomorphic f ↔ ∃ a b : ℂ, a ≠ 0 ∧ f = fun z => a * z + b := by
  sorry

/-- **Theorem 1.8.2 (3)** (Ch. 1 §1.8, H1:760). `Aut 𝔻` is the group of the maps `z ↦ (az + b)/(b̄ z + ā)` with
`|a|² > |b|²`. (On `𝔻` the denominator `b̄ z + ā` does not vanish since `|b z| < |a|`.) -/
theorem thm1_8_2_c (f : unitDiscOpens → unitDiscOpens) :
    IsBiholomorphic f ↔ ∃ a b : ℂ, ‖b‖ ^ 2 < ‖a‖ ^ 2 ∧
      ∀ z : unitDiscOpens, (f z : ℂ) = (a * (z : ℂ) + b) / (conj b * (z : ℂ) + conj a) := by
  sorry

/-- **Theorem 1.8.8 (1)** (universal covering spaces, Ch. 1 §1.8, H1:850). The Riemann sphere is the universal cover
only of itself: a Riemann surface `X` has a holomorphic universal covering by `ℙ¹` iff `X ≅ ℙ¹`. -/
theorem thm1_8_8_a {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    (∃ p : References.RiemannSphere → X, Forster1981.IsUniversalCovering p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) ↔
      RSConformallyEquivalent X References.RiemannSphere := by
  sorry

/-- **Theorem 1.8.8 (2)** (Ch. 1 §1.8, H1:850). The plane `ℂ` is the universal cover of itself, of the punctured plane
`ℂ ∖ {a}` and of all compact Riemann surfaces homeomorphic to a torus (compact of genus `1`), and of no other Riemann
surface: `X` has a holomorphic universal covering by `ℂ` iff `X ≅ ℂ`, or `X ≅ ℂ ∖ {0}`, or `X` is compact of genus `1`.
Modelling: `ℂ ∖ {a} ≅ ℂ ∖ {0}` by translation. -/
theorem thm1_8_8_b {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    (∃ p : ℂ → X, Forster1981.IsUniversalCovering p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) ↔
      RSConformallyEquivalent X ℂ ∨ RSConformallyEquivalent X puncturedPlaneOpens ∨
        (CompactSpace X ∧ HasGenus X 1) := by
  sorry

/-- **Theorem 1.8.8 (3)** (Ch. 1 §1.8, H1:850). All other Riemann surfaces have a universal covering space analytically
isomorphic to `𝔻`: if `X` has no holomorphic universal covering by `ℙ¹` nor by `ℂ`, it has one by `𝔻`. -/
theorem thm1_8_8_c {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (h₁ : ¬ ∃ p : References.RiemannSphere → X, Forster1981.IsUniversalCovering p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p)
    (h₂ : ¬ ∃ p : ℂ → X, Forster1981.IsUniversalCovering p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) :
    ∃ p : unitDiscOpens → X, Forster1981.IsUniversalCovering p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p := by
  sorry

/-- **Hyperbolic Riemann surface** (Def. 1.8.9, H1:858). A Riemann surface is hyperbolic if its universal covering space
is isomorphic to `𝔻`. Modelling (project idiom, with `ℍ ≅ 𝔻`): `X = ℍ/Γ` for a torsion-free Fuchsian group
`Γ ⊆ SL(2, ℝ)`
and a holomorphic covering `p : ℍ → X` whose fibres are the `Γ`-orbits (`LiZhongQC.IsUniformization`); `ℍ` is simply
connected, so `p` is a universal covering. -/
def IsHyperbolicRS (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → X),
    IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p

/-- **Finite type** (Def. 1.8.12, H1:884). A Riemann surface is of finite type if it is isomorphic to a compact Riemann
surface from which at most finitely many points have been removed. Modelling: `LiZhongQC.IsFiniteType X g n 0` (a closed
surface of genus `g`, `n` removed points and no removed discs), for some `g` and `n`. -/
def IsFiniteTypeRS (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∃ g n : ℕ, IsFiniteType X g n 0

/-- **Kleinian group** (Def. 1.8.13, H1:890). A discrete subgroup of `PSL₂ℂ`. Modelling: a subgroup `Γ ⊆ SL(2, ℂ)`
that is discrete in the subspace topology (the book's `PSL₂ℂ` is the quotient by `±1`; `SL₂ℂ → PSL₂ℂ` is a covering, so
the image is discrete iff `Γ` is). Near miss: `Lehto1987.IsKleinian` asks a non-empty set of discontinuity, which is
not the same condition. -/
def IsKleinianGroup (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) : Prop :=
  DiscreteTopology Γ

end Hubbard2006
