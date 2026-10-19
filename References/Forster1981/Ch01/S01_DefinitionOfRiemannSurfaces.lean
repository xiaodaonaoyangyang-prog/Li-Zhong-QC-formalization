import References.Common.RiemannSphere
import LiZhongQC.Ch06.S22_RiemannSurfaces

/-!
# Forster, Chapter 1 §1: The definition of Riemann surfaces

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, Springer 1981, §1 (`full.md` F1:268–596, folder
`Lectures on Riemann Surfaces … b77137c6`).

Conventions: a Riemann surface is the Mathlib bundle of `References/Common/RiemannSurface.lean`
(`[T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]`, Forster's Definition 1.4), written as instance
binders in every statement; surfaces are in universe `0`. "Chart" means a chart of the maximal atlas. Holomorphic functions
and maps are `MDifferentiableOn`/`MDifferentiable` for `𝓘(ℂ)`.

* Definition 1.1 (complex chart, holomorphically compatible, complex atlas, F1:274) — exists: `OpenPartialHomeomorph`,
  `contDiffGroupoid`, `ChartedSpace` (a chart is an `OpenPartialHomeomorph`; two charts are compatible when the
  transition map lies in the holomorphic groupoid, i.e. is biholomorphic)
* Definition 1.1 (analytically equivalent atlases, F1:287) — `AreAnalyticallyEquivalent`
* Definition 1.3 (complex structure, F1:295) — `complexStructureOf`
* Definition 1.4 (Riemann surface, F1:299) — exists: `References.IsRiemannSurface` (the bundle of binders)
* Example (the plane ℂ, §1.5(a), F1:307) — exists: `chartedSpaceSelf`
* Example (domains in a Riemann surface, §1.5(b), F1:310) — exists: `TopologicalSpace.Opens.instChartedSpace`
* Example (the Riemann sphere ℙ¹, §1.5(c), F1:313) — exists: `References.RiemannSphere`
* Example (tori ℂ/Γ, §1.5(d), F1:337) — `IsTorusProjection`, `IsTorusWith`
* Definition 1.6 (holomorphic function, F1:380) — exists: `MDifferentiableOn`
* Definition 1.6 (the algebra 𝒪(Y), F1:386) — `holoFun`
* Theorem 1.8 (Riemann's removable singularities theorem, F1:396) — `thm1_8`
* Definition 1.9 (holomorphic map, biholomorphic, isomorphic, F1:402) — exists: `MDifferentiable`,
  `LiZhongQC.IsBiholomorphic`, `LiZhongQC.RSConformallyEquivalent`
* Remark 1.10(b) (compositions of holomorphic maps are holomorphic, F1:416) — exists: `MDifferentiable.comp`
* Theorem 1.11 (identity theorem, F1:428) — `thm1_11`
* Definition 1.12 (meromorphic function, poles, F1:438) — `poles`, `IsMeromorphicOn`
* Remark 1.13(b) (𝓜(X) is a ℂ-algebra, F1:460) — `meroFun`
* Example 1.14 (polynomials are meromorphic on ℙ¹, F1:462) — `example1_14`
* Theorem 1.15 (meromorphic functions are holomorphic maps to ℙ¹, F1:472) — `thm1_15_a`, `thm1_15_b`
* Remark 1.16(a) (identity theorem for meromorphic functions, F1:488) — `rem1_16_a`
* Remark 1.16(b) (𝓜(X) is a field, F1:488) — `rem1_16_b`

Omitted (U−): Remarks 1.2(a), 1.2(b) (F1:289–293), the remark F1:305, Remarks 1.7(a)–(c) (F1:388), Remarks 1.10(a), (c)
(F1:414–426), Remark 1.13(a) (F1:452).
-/

open scoped Manifold ContDiff Topology References
open Set Filter

namespace Forster1981

/-- **Definition 1.1** (Ch. 1 §1, F1:287). Two complex atlases (charted-space structures `c₁`, `c₂` over `ℂ`) on the
same space `X` are *analytically equivalent* if every chart of the first is holomorphically compatible with every chart of
the second: the transition map lies in `contDiffGroupoid ω 𝓘(ℂ)` (both directions, being a groupoid member). -/
def AreAnalyticallyEquivalent {X : Type*} [TopologicalSpace X] (c₁ c₂ : ChartedSpace ℂ X) : Prop :=
  ∀ e ∈ c₁.atlas, ∀ e' ∈ c₂.atlas, e.symm ≫ₕ e' ∈ contDiffGroupoid ω 𝓘(ℂ)

/-- **Definition 1.3** (Ch. 1 §1, F1:295). The complex structure of an atlas `c`: the maximal atlas it generates, the set of
all charts holomorphically compatible with `c` (two atlases define the same complex structure iff they are analytically
equivalent, F1:297). -/
def complexStructureOf {X : Type*} [TopologicalSpace X] (c : ChartedSpace ℂ X) :
    Set (OpenPartialHomeomorph X ℂ) :=
  letI := c; (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X

/-- **Example 1.5(d)** (Ch. 1 §1, F1:337). A holomorphic map `π : ℂ → X` into a Riemann surface is *the projection of the
torus `ℂ/Γ`* for the lattice `Γ = ℤω₁ + ℤω₂` (`L : PeriodPair`) when it is a covering map whose fibres are exactly the
cosets of `Γ` (`π z = π w ↔ z - w ∈ Γ`); then `π` induces a biholomorphic bijection `ℂ/Γ ≅ X`. -/
def IsTorusProjection {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] (L : PeriodPair) (π : ℂ → X) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π ∧ IsCoveringMap π ∧ ∀ z w : ℂ, π z = π w ↔ z - w ∈ L.lattice

/-- **Example 1.5(d)** (Ch. 1 §1, F1:337). A Riemann surface `X` *is the torus `ℂ/Γ`* when `X` has a projection
`IsTorusProjection L π`.
Modelling: the quotient `ℂ ⧸ Γ` with its charts (the inverses of `π` on small discs) is described by this property of
`X` instead of being constructed (no `IsManifold` instance for the quotient is available); every statement about "the
torus `ℂ/Γ`" holds for every such `X`. Near misses, not reused: `Lehto1987.IsTorusCovering π L` (Ch. V §6: the same
conditions, plus surjectivity, for an arbitrary set `L ⊆ ℂ`, hence not tied to a lattice; it lives in another work) and
`LiZhongQC.IsTorusWithPeriod τ p` (periods normalized to `(1, τ)`). -/
def IsTorusWith (L : PeriodPair) (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∃ π : ℂ → X, IsTorusProjection L π

section Holomorphic

/-- The `ℂ`-algebra structure on germs of complex functions along a filter `l` (constants act by scalar multiplication of
the module structure of germs). Scoped to `Forster1981`. -/
scoped instance germAlgebra {α : Type*} (l : Filter α) : Algebra ℂ (l.Germ ℂ) :=
  Algebra.ofModule
    (fun r x y => by
      induction x using Filter.Germ.inductionOn with | _ f => ?_
      induction y using Filter.Germ.inductionOn with | _ g => ?_
      show (((r • f) * g : α → ℂ) : l.Germ ℂ) = ((r • (f * g) : α → ℂ) : l.Germ ℂ)
      congr 1
      funext x
      simp [mul_assoc])
    (fun r x y => by
      induction x using Filter.Germ.inductionOn with | _ f => ?_
      induction y using Filter.Germ.inductionOn with | _ g => ?_
      show ((f * (r • g) : α → ℂ) : l.Germ ℂ) = ((r • (f * g) : α → ℂ) : l.Germ ℂ)
      congr 1
      funext x
      simp [mul_left_comm])

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **The algebra `𝒪(Y)`** (Definition 1.6 and Remark 1.7(a), Ch. 1 §1, F1:380). For an open subset `Y` of a Riemann
surface (the open submanifold `↥Y`, with the induced charts), the ℂ-algebra of holomorphic functions `Y → ℂ`. -/
def holoFun (Y : TopologicalSpace.Opens X) : Subalgebra ℂ (↥Y → ℂ) where
  carrier := {f | MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f}
  mul_mem' := fun {_ _} hf hg => hf.mul hg
  add_mem' := fun {_ _} hf hg => hf.add hg
  algebraMap_mem' := fun _ => mdifferentiable_const

/-- **The poles** of a function `f : X → ℂ` on `Y ⊆ X` (Definition 1.12, Ch. 1 §1, F1:448): the points of `Y` at which
`|f(x)| → ∞`. -/
def poles (f : X → ℂ) (Y : Set X) : Set X :=
  {p | p ∈ Y ∧ Tendsto (fun x => ‖f x‖) (𝓝[≠] p) atTop}

/-- **Definition 1.12** (Ch. 1 §1, F1:438). `f` is a *meromorphic function on `Y`*: `Y` is open, the poles of `f` (the
points of `Y` at which `|f| → ∞`) form a set which is discrete and closed in `Y`, and `f` is holomorphic on `Y` minus the
poles.
Modelling: `f : X → ℂ` is a total function; its values at the poles are junk and never read (the book's `f` is defined
only on `Y′ = Y ∖ poles`). -/
def IsMeromorphicOn (f : X → ℂ) (Y : Set X) : Prop :=
  IsOpen Y ∧ IsDiscrete (poles f Y) ∧ (∀ q ∈ Y, q ∈ closure (poles f Y) → q ∈ poles f Y) ∧
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (Y \ poles f Y)

/-- **The ℂ-algebra `𝓜(X)` of meromorphic functions** (Remark 1.13(b), Ch. 1 §1, F1:460). The germs along the codiscrete
filter of functions `f : X → ℂ` which are meromorphic in every preferred chart, as a `ℂ`-subalgebra of the algebra of
germs.
Modelling: Forster's meromorphic function is defined off its poles only, and `f + g`, `fg` are extended over removable
singularities; passing to germs along the codiscrete filter forgets the values on discrete sets, so the sum and the product
of two such germs are again of this form. -/
def meroFun (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Subalgebra ℂ ((Filter.codiscrete X).Germ ℂ) where
  carrier := {g | ∃ f : X → ℂ, (f : (Filter.codiscrete X).Germ ℂ) = g ∧
    ∀ x : X, MeromorphicAt (f ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)}
  mul_mem' := by
    rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨f * g, rfl, fun x => (hf x).mul (hg x)⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨f + g, rfl, fun x => (hf x).add (hg x)⟩
  algebraMap_mem' := fun c => ⟨fun _ => c, by
    show (((fun _ => c : X → ℂ)) : (Filter.codiscrete X).Germ ℂ) = c • (((1 : X → ℂ)) : (Filter.codiscrete X).Germ ℂ)
    show _ = (((c • (1 : X → ℂ)) : X → ℂ) : (Filter.codiscrete X).Germ ℂ)
    congr 1
    funext x
    simp, fun x => MeromorphicAt.const c _⟩

end Holomorphic

section Statements

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Theorem 1.8** (Riemann's removable singularities theorem, Ch. 1 §1, F1:396). Let `U` be open in a Riemann surface,
`a ∈ U`, and `f` holomorphic on `U ∖ {a}` and bounded near `a`. Then `f` has a unique holomorphic extension to `U`.
Modelling: functions are total on `X`; the extension is unique as a function on `U`. -/
theorem thm1_8 {U : Set X} (hU : IsOpen U) {a : X} (ha : a ∈ U) {f : X → ℂ}
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (U \ {a}))
    (hb : ∃ V ∈ 𝓝 a, BddAbove ((fun x => ‖f x‖) '' (V \ {a}))) :
    ∃ g : X → ℂ, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) g U ∧ EqOn g f (U \ {a}) ∧
      ∀ g' : X → ℂ, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) g' U → EqOn g' f (U \ {a}) → EqOn g' g U := by
  sorry

/-- **Theorem 1.11** (Identity theorem, Ch. 1 §1, F1:428). Let `X`, `Y` be Riemann surfaces and `f₁, f₂ : X → Y`
holomorphic maps which coincide on a set `A ⊆ X` having a limit point `a` in `X`. Then `f₁ = f₂`.
Modelling: a limit point of `A` in `X` is a point `a ∈ closure (A ∖ {a})`. -/
theorem thm1_11 {f₁ f₂ : X → Y} (h₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₁) (h₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f₂)
    {A : Set X} {a : X} (ha : a ∈ closure (A \ {a})) (hA : EqOn f₁ f₂ A) : f₁ = f₂ := by
  sorry

/-- **Example 1.14** (Ch. 1 §1, F1:462). Let `F(z) = zⁿ + c₁zⁿ⁻¹ + … + cₙ`, `n ≥ 1`. Then `|F(z)| → ∞` as `z → ∞`, so
`F` is a meromorphic function on `ℙ¹` with a pole at `∞`.
Modelling: `F` is a monic polynomial of positive degree; the function on `ℙ¹` equals `F` on `ℂ` and `0` at `∞` (junk value,
never read as the value of a pole). -/
theorem example1_14 (F : Polynomial ℂ) (hF : F.Monic) (hn : 1 ≤ F.natDegree) :
    Tendsto (fun z : ℂ => ‖F.eval z‖) (cocompact ℂ) atTop ∧
      IsMeromorphicOn (fun x : References.RiemannSphere =>
        OnePoint.elim (x : OnePoint ℂ) 0 (fun z => F.eval z)) univ ∧
      References.RiemannSphere.infty ∈ poles (fun x : References.RiemannSphere =>
        OnePoint.elim (x : OnePoint ℂ) 0 (fun z => F.eval z)) univ := by
  sorry

open scoped Classical in
/-- **Theorem 1.15(a)** (Ch. 1 §1, F1:472). A meromorphic function `f` on a Riemann surface, extended by `f(p) := ∞` at the
poles, is a holomorphic map `X → ℙ¹`. -/
theorem thm1_15_a {f : X → ℂ} (hf : IsMeromorphicOn f univ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : X =>
      if x ∈ poles f univ then References.RiemannSphere.infty else References.RiemannSphere.ofComplex (f x)) := by
  sorry

/-- **Theorem 1.15(b)** (Ch. 1 §1, F1:472). A holomorphic map `f : X → ℙ¹` is either identically `∞`, or `f⁻¹(∞)` is a
discrete closed set and `f : X ∖ f⁻¹(∞) → ℂ` is a meromorphic function on `X`.
Modelling: the finite value is read through the chart at the finite points, `References.RiemannSphere.chart₀` (value `0`
at `∞`, junk never read as the value of a pole). -/
theorem thm1_15_b {g : X → References.RiemannSphere} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) :
    (∀ x, g x = References.RiemannSphere.infty) ∨
      (IsDiscrete (g ⁻¹' {References.RiemannSphere.infty}) ∧ IsClosed (g ⁻¹' {References.RiemannSphere.infty}) ∧
        IsMeromorphicOn (fun x => References.RiemannSphere.chart₀ (g x)) univ) := by
  sorry

/-- **Remark 1.16(a)** (identity theorem for meromorphic functions, Ch. 1 §1, F1:488). A meromorphic function `f ≢ 0` on a
Riemann surface has only isolated zeros: the zeros (off the poles) form a discrete closed set. -/
theorem rem1_16_a {f : X → ℂ} (hf : IsMeromorphicOn f univ) (h0 : ∃ x, x ∉ poles f univ ∧ f x ≠ 0) :
    IsDiscrete {x | x ∉ poles f univ ∧ f x = 0} ∧ IsClosed {x | x ∉ poles f univ ∧ f x = 0} := by
  sorry

/-- **Remark 1.16(b)** (Ch. 1 §1, F1:488). The ring `𝓜(X)` of meromorphic functions on a Riemann surface is a field. -/
theorem rem1_16_b : IsField (meroFun X) := by
  sorry

end Statements

end Forster1981
