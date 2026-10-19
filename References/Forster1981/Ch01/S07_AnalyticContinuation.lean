import References.Forster1981.Ch01.S06_Sheaves

/-!
# Forster, Chapter 1 §7: Analytic continuation

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §7 (`full.md` F1:1811–1900).

Conventions: a germ `φ ∈ 𝒪_a` is a point of the space `|𝒪|` over `a` (`(sheafO X).presheaf.EtaleSpace`: a base point
together with an element of the stalk at it). The stalk `𝒪_y` of the sheaf of holomorphic functions, the germ of a
section and the pull-back `p^*` are expressed through representatives on open neighbourhoods; `p^*` is a relation
(`IsGermPullback`), a function by `para7_5`, and the book's `p_*` (its inverse) is avoided: 7.6(iii) is stated as
`ρ_b(f) = p^*φ`, equivalent since `p^*` is bijective.

* Definition 7.1 (analytic continuation of a germ along a curve, F1:1815) — `IsAnalyticContinuationAlong`
* Lemma 7.2 (F1:1831) — `lemma7_2`
* Monodromy theorem 7.3 (F1:1841) — `thm7_3`
* Corollary 7.4 (F1:1845) — `cor7_4`
* Paragraph 7.5 (the pull-back of germs `p^*`, F1:1851) — `IsGermOf`, `IsGermPullback`, `para7_5`
* Definition 7.6 (analytic continuation of a germ, maximal, F1:1861) — `IsAnalyticContinuation`,
  `IsMaximalAnalyticContinuation`
* Lemma 7.7 (F1:1877) — `lemma7_7`
* Theorem 7.8 (F1:1887) — `thm7_8`

Omitted (U−): uniqueness of continuations (F1:1839), the equivalent partition form of 7.1 (F1:1821), uniqueness of maximal
analytic continuations (F1:1875), the remark on meromorphic germs (F1:1893).
-/

open scoped Manifold ContDiff Topology unitInterval References
open Set Filter TopologicalSpace CategoryTheory

namespace Forster1981

open scoped Forster1981

section Germs

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Definition 7.1** (analytic continuation along a curve, Ch. 1 §7, F1:1815). The germ `ψ ∈ 𝒪_{u(1)}` is the *analytic
continuation* of the germ `φ ∈ 𝒪_{u(0)}` along the curve `u : [0, 1] → X` if there is a family of germs `φ_t ∈ 𝒪_{u(t)}`
with `φ_0 = φ`, `φ_1 = ψ`, which is locally given by sections: for every `t₀` there are a neighbourhood `U` of `u(t₀)`,
a holomorphic `f` on `U` and a neighbourhood of `t₀` on which `φ_t` is the germ of `f` at `u(t)`.
Modelling: germs are points of the étalé space `|𝒪|`, with their base points. -/
def IsAnalyticContinuationAlong (u : C(I, X)) (φ ψ : (sheafO X).presheaf.EtaleSpace) : Prop :=
  φ.base = u 0 ∧ ψ.base = u 1 ∧ ∃ φt : I → (sheafO X).presheaf.EtaleSpace,
    (∀ t, (φt t).base = u t) ∧ φt 0 = φ ∧ φt 1 = ψ ∧
      ∀ t₀ : I, ∃ (U : Opens (TopCat.of X)) (_ : u t₀ ∈ U) (f : (sheafO X).presheaf.obj (Opposite.op U)),
        ∀ᶠ t in 𝓝 t₀, ∃ h : (φt t).base ∈ U, (φt t).germ = (sheafO X).presheaf.germ U (φt t).base h f

/-- **The germ of a holomorphic function** (Ch. 1 §7, F1:1853 helper, after 6.5): the stalk element `ψ ∈ 𝒪_y` is the germ
`ρ_y(f)` of the function `f : X → ℂ` at `y` when `ψ` is the germ of a holomorphic section over a neighbourhood of `y`
which agrees with `f`. -/
def IsGermOf (f : X → ℂ) (y : X) (ψ : (sheafO X).presheaf.stalk y) : Prop :=
  ∃ (V : Opens (TopCat.of X)) (hV : y ∈ V) (g : (sheafO X).presheaf.obj (Opposite.op V)),
    (∀ v : V, g.1 v = f v) ∧ (sheafO X).presheaf.germ V y hV g = ψ

variable {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- **The pull-back of germs `p^*`** (7.5, Ch. 1 §7, F1:1853), as a relation: the germ `ψ ∈ 𝒪_{Y,y}` is the pull-back
`p^*φ` of the germ `φ ∈ 𝒪_{X,p(y)}` when, for a representative `g` of `φ` on a neighbourhood `U` of `p(y)`, `ψ` is the germ
at `y` of `g ∘ p` on a neighbourhood `V ⊆ p⁻¹(U)` of `y`. -/
def IsGermPullback (p : Y → X) (y : Y) (φ : (sheafO X).presheaf.EtaleSpace) (ψ : (sheafO Y).presheaf.stalk y) : Prop :=
  φ.base = p y ∧ ∃ (U : Opens (TopCat.of X)) (hU : φ.base ∈ U) (g : (sheafO X).presheaf.obj (Opposite.op U)),
    (sheafO X).presheaf.germ U φ.base hU g = φ.germ ∧
      ∃ (V : Opens (TopCat.of Y)) (hV : y ∈ V) (g' : (sheafO Y).presheaf.obj (Opposite.op V)),
        (∀ v : V, ∃ hv : p v ∈ U, g'.1 v = g.1 ⟨p v, hv⟩) ∧ (sheafO Y).presheaf.germ V y hV g' = ψ

/-- **Definition 7.6** (analytic continuation of a germ, Ch. 1 §7, F1:1861). Let `φ ∈ 𝒪_a`. A quadruple `(Y, p, f, b)` is an
*analytic continuation* of `φ` if (i) `Y` is a Riemann surface and `p : Y → X` an unbranched holomorphic map, (ii) `f ∈ 𝒪(Y)`,
(iii) `p(b) = a` and `ρ_b(f) = p^*φ`.
Modelling: `Y`, `p`, `f`, `b` are the arguments; "Y is a Riemann surface" is stated separately where needed
(`References.IsRiemannSurface`). -/
def IsAnalyticContinuation (p : Y → X) (f : Y → ℂ) (b : Y) (φ : (sheafO X).presheaf.EtaleSpace) : Prop :=
  IsUnbranched p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧
    ∃ ψ : (sheafO Y).presheaf.stalk b, IsGermPullback p b φ ψ ∧ IsGermOf f b ψ

/-- **Definition 7.6** (maximal analytic continuation, Ch. 1 §7, F1:1873). An analytic continuation `(Y, p, f, b)` of `φ`
is *maximal* if every analytic continuation `(Z, q, g, c)` of `φ` (`Z` a Riemann surface) is dominated by it: there is a
holomorphic `F : Z → Y` with `p ∘ F = q`, `g = f ∘ F` and `F(c) = b`. -/
def IsMaximalAnalyticContinuation (p : Y → X) (f : Y → ℂ) (b : Y) (φ : (sheafO X).presheaf.EtaleSpace) : Prop :=
  IsAnalyticContinuation p f b φ ∧
    ∀ (Z : Type) [TopologicalSpace Z] [ChartedSpace ℂ Z], References.IsRiemannSurface Z →
      ∀ (q : Z → X) (g : Z → ℂ) (c : Z), IsAnalyticContinuation q g c φ →
        ∃ F : Z → Y, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ (p ∘ F) = q ∧ g = f ∘ F ∧ F c = b

end Germs

section Statements

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Lemma 7.2** (Ch. 1 §7, F1:1831). The germ `ψ ∈ 𝒪_b` is the analytic continuation of the germ `φ ∈ 𝒪_a` along the
curve `u` iff there is a lifting `û : [0, 1] → |𝒪|` of `u` (to the étalé space of `𝒪`) with `û(0) = φ`, `û(1) = ψ`. -/
theorem lemma7_2 (u : C(I, X)) (φ ψ : (sheafO X).presheaf.EtaleSpace) :
    IsAnalyticContinuationAlong u φ ψ ↔
      ∃ û : C(I, (sheafO X).presheaf.EtaleSpace), (∀ t, (û t).base = u t) ∧ û 0 = φ ∧ û 1 = ψ := by
  sorry

/-- **Monodromy theorem 7.3** (Ch. 1 §7, F1:1841). Let `u_s` (`s ∈ [0, 1]`) be a homotopy of curves from `a` to `b`
(`(t, s) ↦ u_s(t)` continuous, `u_s(0) = a`, `u_s(1) = b`), and `φ ∈ 𝒪_a` a germ which can be continued analytically along
every `u_s`. Then the continuations of `φ` along `u₀` and `u₁` are the same germ. -/
theorem thm7_3 {a b : X} (u : I → C(I, X)) (hu : Continuous (fun p : I × I => u p.2 p.1)) (hu0 : ∀ s, u s 0 = a)
    (hu1 : ∀ s, u s 1 = b) {φ : (sheafO X).presheaf.EtaleSpace} (hφ : φ.base = a)
    (hcont : ∀ s, ∃ ψ, IsAnalyticContinuationAlong (u s) φ ψ) (ψ₀ ψ₁ : (sheafO X).presheaf.EtaleSpace)
    (h₀ : IsAnalyticContinuationAlong (u 0) φ ψ₀) (h₁ : IsAnalyticContinuationAlong (u 1) φ ψ₁) : ψ₀ = ψ₁ := by
  sorry

/-- **Corollary 7.4** (Ch. 1 §7, F1:1845). Let `X` be simply connected and `φ ∈ 𝒪_a` a germ which can be continued
analytically along every curve starting at `a`. Then there is a global holomorphic function `f ∈ 𝒪(X)` with germ `φ` at `a`. -/
theorem cor7_4 [SimplyConnectedSpace X] {φ : (sheafO X).presheaf.EtaleSpace}
    (hcont : ∀ u : C(I, X), u 0 = φ.base → ∃ ψ, IsAnalyticContinuationAlong u φ ψ) :
    ∃ f : (sheafO X).presheaf.obj (Opposite.op ⊤),
      (sheafO X).presheaf.germ ⊤ φ.base (mem_univ _) f = φ.germ := by
  sorry

/-- **7.5** (Ch. 1 §7, F1:1851–1859). For an unbranched holomorphic map `p : Y → X` and `y ∈ Y`, the pull-back
`p^* : 𝒪_{X,p(y)} → 𝒪_{Y,y}` (the relation `IsGermPullback`) is a bijection of the stalks.
[Forster-fix1] `Y` carries the Riemann-surface binders (AUDIT5_Forster N1). -/
theorem para7_5 {Y : Type} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] {p : Y → X} (hp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p)
    (hu : IsUnbranched p) (y : Y) :
    (∀ φ : (sheafO X).presheaf.EtaleSpace, φ.base = p y → ∃! ψ, IsGermPullback p y φ ψ) ∧
      ∀ ψ : (sheafO Y).presheaf.stalk y, ∃! φ : (sheafO X).presheaf.EtaleSpace, IsGermPullback p y φ ψ := by
  sorry

/-- **Lemma 7.7** (Ch. 1 §7, F1:1877). Let `(Y, p, f, b)` be an analytic continuation of the germ `φ` and `v` a curve in
`Y` starting at `b`. Then the germ `p_*(ρ_{v(1)}(f))` (the germ whose pull-back is the germ of `f` at the end point) is the
analytic continuation of `φ` along the curve `p ∘ v`. [Forster-fix1] `Y` carries the Riemann-surface binders
(AUDIT5_Forster N1). -/
theorem lemma7_7 {Y : Type} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] {p : Y → X} {f : Y → ℂ} {b : Y}
    {φ : (sheafO X).presheaf.EtaleSpace} (hc : IsAnalyticContinuation p f b φ) (v : C(I, Y)) (hv : v 0 = b) :
    ∃ ψ : (sheafO X).presheaf.EtaleSpace, ∃ ρ : (sheafO Y).presheaf.stalk (v 1),
      IsGermOf f (v 1) ρ ∧ IsGermPullback p (v 1) ψ ρ ∧
        IsAnalyticContinuationAlong ((⟨p, hc.2.1.continuous⟩ : C(Y, X)).comp v) φ ψ := by
  sorry

/-- **Theorem 7.8** (Ch. 1 §7, F1:1887). Every germ `φ ∈ 𝒪_a` has a maximal analytic continuation `(Y, p, f, b)`. -/
theorem thm7_8 (φ : (sheafO X).presheaf.EtaleSpace) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace ℂ Y), References.IsRiemannSurface Y ∧
      ∃ (p : Y → X) (f : Y → ℂ) (b : Y), IsMaximalAnalyticContinuation p f b φ := by
  sorry

end Statements

end Forster1981
