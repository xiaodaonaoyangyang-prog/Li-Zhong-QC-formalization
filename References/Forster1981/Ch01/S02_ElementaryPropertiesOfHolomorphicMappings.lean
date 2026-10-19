import References.Forster1981.Ch01.S01_DefinitionOfRiemannSurfaces

/-!
# Forster, Chapter 1 §2: Elementary properties of holomorphic mappings

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §2 (`full.md` F1:597–732).

* Theorem 2.1 (local behavior of holomorphic mappings, F1:601) — `thm2_1`
* Remark 2.2 (the multiplicity, F1:621) — `multiplicity`, `rem2_2`
* Example 2.3 (polynomials as maps of ℙ¹, F1:623) — `example2_3`
* Corollary 2.4 (open mapping theorem, F1:625) — `cor2_4`
* Corollary 2.5 (injective holomorphic maps, F1:629) — `cor2_5`
* Corollary 2.6 (maximum principle, F1:633) — exists: `MDifferentiableOn.eqOn_of_isPreconnected_of_isMaxOn_norm` (with
  U the whole surface; its conclusion "f is constant if |f| attains its maximum" is the contrapositive)
* Theorem 2.7 (F1:649) — `thm2_7`
* Corollary 2.8 (F1:653) — exists: `MDifferentiable.exists_eq_const_of_compactSpace` (hypotheses weaker: only
  a C¹ manifold structure)
* Corollary 2.9 (meromorphic functions on ℙ¹ are rational, F1:657) — `cor2_9`
* Liouville's theorem 2.10 (F1:667) — exists: `Differentiable.apply_eq_apply_of_bounded`
* Fundamental theorem of algebra 2.11 (F1:671) — exists: `Complex.exists_root` (positive degree; a monic polynomial of
  degree at least 1 is a special case)
* Definition (doubly periodic functions, 2.12, F1:681) — `IsDoublyPeriodic`
* Paragraph 2.12 (functions on the torus, F1:681) — `para2_12`
* Theorem 2.13 (F1:689) — `thm2_13_a`, `thm2_13_b`
-/

open scoped Manifold ContDiff Topology References
open Set Filter

namespace Forster1981

open scoped Forster1981

section Local

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **The multiplicity** `v(f, a) = k` of a holomorphic map `f : X → Y` at `a` (Remark 2.2, F1:621, and 4.23, F1:1273):
the order at `a` of the local expression `f(a) ↦ ψ ∘ f ∘ φ⁻¹` of `f` in the preferred charts at `a` and `f a` (minus the
value at `a`), the exponent `k` of Theorem 2.1.
Modelling: the order is `analyticOrderAt` of the local expression; the junk value `⊤` for locally constant `f` is never
read, all statements assume `f` non-constant. -/
noncomputable def multiplicity (f : X → Y) (a : X) : ℕ∞ :=
  analyticOrderAt (fun z => chartAt ℂ (f a) (f ((chartAt ℂ a).symm z)) - chartAt ℂ (f a) (f a)) (chartAt ℂ a a)

/-- **Theorem 2.1** (Local behavior of holomorphic mappings, Ch. 1 §2, F1:601). Let `f : X → Y` be a non-constant
holomorphic map of Riemann surfaces, `a ∈ X`, `b = f(a)`. Then there are `k ≥ 1` and charts `φ : U → V` of `X`,
`ψ : U′ → V′` of `Y` with `a ∈ U`, `φ(a) = 0`, `b ∈ U′`, `ψ(b) = 0`, `f(U) ⊆ U′`, and `ψ ∘ f ∘ φ⁻¹ (z) = zᵏ` on `V`.
Modelling: charts are members of the maximal atlases. -/
theorem thm2_1 {f : X → Y} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hnc : ¬ ∃ c, ∀ x, f x = c) (a : X) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X, ∃ ψ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Y,
      a ∈ φ.source ∧ φ a = 0 ∧ f a ∈ ψ.source ∧ ψ (f a) = 0 ∧ (∀ x ∈ φ.source, f x ∈ ψ.source) ∧
        ∀ z ∈ φ.target, ψ (f (φ.symm z)) = z ^ k := by
  sorry

/-- **Remark 2.2** (The multiplicity, Ch. 1 §2, F1:621). For a non-constant holomorphic map `f : X → Y` and `a ∈ X`, the
multiplicity `k = multiplicity f a` (a natural number `≥ 1`) is characterized by: for every neighbourhood `U₀` of `a` there
are neighbourhoods `U ⊆ U₀` of `a` and `W` of `b = f(a)` such that every `y ∈ W ∖ {b}` has exactly `k` preimages in `U`. -/
theorem rem2_2 {f : X → Y} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hnc : ¬ ∃ c, ∀ x, f x = c) (a : X) :
    ∃ k : ℕ, 1 ≤ k ∧ multiplicity f a = k ∧ ∀ U₀ ∈ 𝓝 a, ∃ U ∈ 𝓝 a, ∃ W ∈ 𝓝 (f a), U ⊆ U₀ ∧
      ∀ y ∈ W \ {f a}, (f ⁻¹' {y} ∩ U).Finite ∧ (f ⁻¹' {y} ∩ U).ncard = k := by
  sorry

/-- **Example 2.3** (Ch. 1 §2, F1:623). A polynomial `f(z) = zᵏ + c₁zᵏ⁻¹ + … + c_k` of degree `k ≥ 1`, extended by
`f(∞) = ∞`, is a holomorphic map `ℙ¹ → ℙ¹` which takes the value `∞` at `∞` with multiplicity `k`. -/
theorem example2_3 (P : Polynomial ℂ) (hP : P.Monic) (hk : 1 ≤ P.natDegree) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : References.RiemannSphere =>
      OnePoint.elim (x : OnePoint ℂ) References.RiemannSphere.infty
        (fun z => References.RiemannSphere.ofComplex (P.eval z))) ∧
    multiplicity (fun x : References.RiemannSphere =>
      OnePoint.elim (x : OnePoint ℂ) References.RiemannSphere.infty
        (fun z => References.RiemannSphere.ofComplex (P.eval z))) References.RiemannSphere.infty = P.natDegree := by
  sorry

/-- **Corollary 2.4** (Open mapping theorem, Ch. 1 §2, F1:625). A non-constant holomorphic map of Riemann surfaces is
open. -/
theorem cor2_4 {f : X → Y} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hnc : ¬ ∃ c, ∀ x, f x = c) : IsOpenMap f := by
  sorry

/-- **Corollary 2.5** (Ch. 1 §2, F1:629). An injective holomorphic map `f : X → Y` is biholomorphic onto its image, which is
open in `Y`.
Modelling: the image is the open submanifold `⟨range f, _⟩ : Opens Y`; `f` corestricted to it is biholomorphic. -/
theorem cor2_5 {f : X → Y} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hi : Function.Injective f) :
    ∃ h : IsOpen (Set.range f),
      LiZhongQC.IsBiholomorphic
        (fun x => (⟨f x, Set.mem_range_self x⟩ : ↥(⟨Set.range f, h⟩ : TopologicalSpace.Opens Y))) := by
  sorry

/-- **Theorem 2.7** (Ch. 1 §2, F1:649). Let `X` be a compact Riemann surface and `f : X → Y` a non-constant holomorphic
map. Then `Y` is compact and `f` is surjective. -/
theorem thm2_7 [CompactSpace X] {f : X → Y} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hnc : ¬ ∃ c, ∀ x, f x = c) :
    CompactSpace Y ∧ Function.Surjective f := by
  sorry

/-- **Corollary 2.9** (Ch. 1 §2, F1:657). Every meromorphic function on the Riemann sphere is rational: a holomorphic map
`f : ℙ¹ → ℙ¹` which is not identically `∞` agrees on `ℂ` (off the zeros of the denominator) with a quotient of two
polynomials. -/
theorem cor2_9 {f : References.RiemannSphere → References.RiemannSphere}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hinfty : ¬ ∀ x, f x = References.RiemannSphere.infty) :
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ z : ℂ, Q.eval z ≠ 0 →
      f (References.RiemannSphere.ofComplex z) = References.RiemannSphere.ofComplex (P.eval z / Q.eval z) := by
  sorry

end Local

/-- **Doubly periodic functions** (2.12, Ch. 1 §2, F1:681). For a lattice `Γ = ℤω₁ + ℤω₂` (`L : PeriodPair`), a
holomorphic map `f : ℂ → ℙ¹` is *doubly periodic with respect to `Γ`* if `f(z) = f(z + w)` for all `z ∈ ℂ`, `w ∈ Γ`. -/
def IsDoublyPeriodic (f : ℂ → References.RiemannSphere) (L : PeriodPair) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ ∀ z : ℂ, ∀ w ∈ L.lattice, f (z + w) = f z

/-- **2.12 Doubly periodic functions** (Ch. 1 §2, F1:681–687). Let `π : ℂ → X` be the projection of a torus `X = ℂ/Γ`.
Then `F ↦ F ∘ π` is a bijection from the holomorphic maps `X → ℙ¹` onto the doubly periodic functions: every
doubly periodic `f` is `F ∘ π` for a unique holomorphic `F`, and conversely. -/
theorem para2_12 {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (L : PeriodPair) (π : ℂ → X) (hπ : IsTorusProjection L π) :
    (∀ F : X → References.RiemannSphere, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F → IsDoublyPeriodic (F ∘ π) L) ∧
      ∀ f : ℂ → References.RiemannSphere, IsDoublyPeriodic f L →
        ∃! F : X → References.RiemannSphere, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ F ∘ π = f := by
  sorry

/-- **Theorem 2.13(a)** (Ch. 1 §2, F1:689). Every doubly periodic holomorphic function `f : ℂ → ℂ` is constant. -/
theorem thm2_13_a (L : PeriodPair) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hper : ∀ z : ℂ, ∀ w ∈ L.lattice, f (z + w) = f z) : ∃ c, ∀ z, f z = c := by
  sorry

/-- **Theorem 2.13(b)** (Ch. 1 §2, F1:689). Every non-constant doubly periodic meromorphic function `f : ℂ → ℙ¹` attains
every value `c ∈ ℙ¹`. -/
theorem thm2_13_b (L : PeriodPair) {f : ℂ → References.RiemannSphere} (hf : IsDoublyPeriodic f L)
    (hnc : ¬ ∃ c, ∀ z, f z = c) : Function.Surjective f := by
  sorry

end Forster1981
