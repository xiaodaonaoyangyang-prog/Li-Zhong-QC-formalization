import References.Forster1981.Ch01.S03_HomotopyOfCurvesTheFundamentalGroup

/-!
# Forster, Chapter 1 §4: Branched and unbranched coverings

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §4 (`full.md` F1:1011–1374).

Conventions: a lifting of `f : Z → X` with respect to `p : Y → X` is a continuous `g : Z → Y` with `p ∘ g = f`; the fibre
of `p` over `x` is `p ⁻¹' {x}`. The multiplicity `v(f, x)` of 4.23 is `multiplicity f x` (§2). Reading (misprint, 4.23): the
sum over `x ∈ f⁻¹(c)`, not `p⁻¹(c)`.

* Definition 4.1 (fibre, discrete subset, F1:1015) — exists: `IsDiscrete`
* Definition 4.1 (discrete map, F1:1015) — `IsDiscreteMap`
* Theorem 4.2 (F1:1019) — `thm4_2`
* Definition 4.3 (branch point, unbranched, F1:1031) — `IsBranchPoint`, `IsUnbranched`
* Theorem 4.4 (F1:1033) — `thm4_4`
* Theorem 4.6 (complex structure on a local homeomorphism, F1:1049) — `thm4_6`
* Theorem 4.8 (uniqueness of lifting, F1:1061) — exists: `IsSeparatedMap.eq_of_comp_eq` (the hypotheses of the
  book, Hausdorff spaces and a local homeomorphism, imply the separatedness and local injectivity it requires)
* Theorem 4.9 (F1:1065) — `thm4_9`
* Consequence of 4.9 (fibre-preserving continuous maps are holomorphic, F1:1069) — `thm4_9_cons`
* Theorem 4.10 (lifting of homotopic curves, F1:1075) — `thm4_10`
* Definition 4.11 (covering map, F1:1135) — exists: `IsCoveringMap`
* Definition 4.13 (curve lifting property, F1:1175) — `HasCurveLiftingProperty`
* Theorem 4.14 (F1:1177) — exists: `IsCoveringMap.exists_path_lifts`
* Theorem 4.16 (number of sheets, F1:1209) — `numSheets`, `thm4_16`
* Theorem 4.17 (F1:1217) — exists: `IsCoveringMap.existsUnique_continuousMap_lifts`
* Remark after 4.17 (F1:1219) — `rem4_17`
* Theorem 4.19 (F1:1239) — `thm4_19`
* Paragraph 4.20 (proper mappings, F1:1249) — exists: `IsProperMap`, `LocallyCompactSpace`, `IsProperMap.isClosedMap`
* Lemma 4.21 (F1:1251) — `lemma4_21_a`, `lemma4_21_b`
* Theorem 4.22 (F1:1263) — `thm4_22`
* Paragraph 4.23 (proper holomorphic mappings, F1:1273) — `criticalValues`, `valenceCount`, `para4_23_a`, `para4_23_b`
* Theorem 4.24 (F1:1283) — `thm4_24`
* Definition (n-sheeted holomorphic covering map, remark after 4.24, F1:1287) — `IsHolomorphicCovering`
* Corollary 4.25 (F1:1289) — `cor4_25`
* Corollary 4.26 (F1:1293) — exists: `IsAlgClosed.card_roots_eq_natDegree`

Omitted (U−): the terminology "domain over X" and multi-valued functions (F1:1023–1029), Examples 4.5 (F1:1039–1047),
the lifting-of-curves paragraph (F1:1071), Examples 4.12 (F1:1145), Remark 4.15 (F1:1199), Example 4.18 (F1:1231).
-/

open scoped Manifold ContDiff Topology unitInterval References
open Set Filter

namespace Forster1981

open scoped Forster1981

/-- **Definition 4.1** (discrete map, Ch. 1 §4, F1:1017). A map `p : Y → X` is *discrete* if every fibre `p⁻¹(x)` is a
discrete subset of `Y`. -/
def IsDiscreteMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : Y → X) : Prop :=
  ∀ x, IsDiscrete (p ⁻¹' {x})

/-- **Definition 4.3** (branch point, Ch. 1 §4, F1:1031). A point `y` is a *branch point* (ramification point) of `p` if
there is no neighbourhood of `y` on which `p` is injective. -/
def IsBranchPoint {X Y : Type*} [TopologicalSpace Y] (p : Y → X) (y : Y) : Prop :=
  ¬ ∃ V ∈ 𝓝 y, InjOn p V

/-- **Definition 4.3** (unbranched, Ch. 1 §4, F1:1031). The map `p` is *unbranched* if it has no branch points. -/
def IsUnbranched {X Y : Type*} [TopologicalSpace Y] (p : Y → X) : Prop :=
  ∀ y, ¬ IsBranchPoint p y

/-- **Definition 4.13** (curve lifting property, Ch. 1 §4, F1:1175). The map `p : Y → X` has the *curve lifting property*
if every curve `u : I → X` has, for every `y₀` over its initial point, a lifting `û : I → Y` with `û(0) = y₀`. -/
def HasCurveLiftingProperty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : Y → X) : Prop :=
  ∀ (u : C(I, X)) (y₀ : Y), p y₀ = u 0 → ∃ û : C(I, Y), (p ∘ û) = u ∧ û 0 = y₀

/-- **The number of sheets** over `x` (Theorem 4.16, Ch. 1 §4, F1:1211): the cardinality of the fibre `p⁻¹(x)`. -/
def numSheets {X Y : Type*} (p : Y → X) (x : X) : Cardinal := Cardinal.mk ↥(p ⁻¹' {x})

/-- **The critical values** of a map `f` (4.23, Ch. 1 §4, F1:1273): the images of the branch points. -/
def criticalValues {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) : Set Y :=
  f '' {x | IsBranchPoint f x}

section Holomorphic

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Counting a value with multiplicities** (4.23, Ch. 1 §4, F1:1277). The number of times the holomorphic map `f` takes
the value `c`, counting multiplicities: `Σ_{x ∈ f⁻¹(c)} v(f, x)`.
Modelling: `finsum`, with junk value `0` for an infinite sum, excluded by properness in every statement. Reading
(misprint in the book): the sum is over `f⁻¹(c)`. -/
noncomputable def valenceCount (f : X → Y) (c : Y) : ℕ∞ := ∑ᶠ x ∈ f ⁻¹' {c}, multiplicity f x

/-- **Definition** (n-sheeted holomorphic covering map, remark after 4.24, Ch. 1 §4, F1:1287). A non-constant holomorphic
map `f : X → Y` which is proper and takes every value `n` times counting multiplicities. -/
def IsHolomorphicCovering (f : X → Y) (n : ℕ) : Prop :=
  IsProperMap f ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ (¬ ∃ c, ∀ x, f x = c) ∧ ∀ c, valenceCount f c = n

/-- **Theorem 4.2** (Ch. 1 §4, F1:1019). A non-constant holomorphic map of Riemann surfaces is open and discrete. -/
theorem thm4_2 {p : Y → X} (hp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hnc : ¬ ∃ c, ∀ y, p y = c) :
    IsOpenMap p ∧ IsDiscreteMap p := by
  sorry

/-- **Theorem 4.4** (Ch. 1 §4, F1:1033). A non-constant holomorphic map `p : Y → X` has no branch points iff it is a local
homeomorphism. -/
theorem thm4_4 {p : Y → X} (hp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hnc : ¬ ∃ c, ∀ y, p y = c) :
    IsUnbranched p ↔ IsLocalHomeomorph p := by
  sorry

/-- **Theorem 4.9** (Ch. 1 §4, F1:1065). Let `p : Y → X` be an unbranched holomorphic map and `f : Z → X` holomorphic.
Then every lifting `g : Z → Y` of `f` (continuous, `p ∘ g = f`) is holomorphic. -/
theorem thm4_9 {Z : Type} [TopologicalSpace Z] [T2Space Z] [ConnectedSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) ω Z] {p : Y → X} (hp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hu : IsUnbranched p) {f : Z → X}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {g : Z → Y} (hg : Continuous g) (hgf : p ∘ g = f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
  sorry

/-- **Consequence of Theorem 4.9** (Ch. 1 §4, F1:1069). A continuous fibre-preserving map `φ : Y → Z` between unbranched
holomorphic coverings `p : Y → X`, `q : Z → X` (`q ∘ φ = p`) is holomorphic. -/
theorem thm4_9_cons {Z : Type} [TopologicalSpace Z] [T2Space Z] [ConnectedSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) ω Z] {p : Y → X} {q : Z → X} (hp : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hpu : IsUnbranched p)
    (hq : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) q) (hqu : IsUnbranched q) {φ : Y → Z} (hφ : Continuous φ) (hqφ : q ∘ φ = p) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ := by
  sorry

end Holomorphic

/-- **Theorem 4.6** (Ch. 1 §4, F1:1049). Let `X` be a Riemann surface, `Y` a Hausdorff space and `p : Y → X` a local
homeomorphism. Then there is a unique complex structure on `Y` such that `p` is holomorphic.
Modelling: a complex structure is an atlas up to analytic equivalence (1.3): there is a complex atlas on `Y` (an
`IsManifold 𝓘(ℂ) ω` charted-space structure) for which `p` is holomorphic, and any two such atlases are analytically
equivalent. `Y` is not assumed connected here (the book's "complex structure" is that of a possibly disconnected space). -/
theorem thm4_6 {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {Y : Type} [TopologicalSpace Y] [T2Space Y] {p : Y → X} (hp : IsLocalHomeomorph p) :
    (∃ c : ChartedSpace ℂ Y, letI := c; IsManifold 𝓘(ℂ) ω Y ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) ∧
      ∀ c₁ c₂ : ChartedSpace ℂ Y,
        (letI := c₁; IsManifold 𝓘(ℂ) ω Y ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) →
        (letI := c₂; IsManifold 𝓘(ℂ) ω Y ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) →
        AreAnalyticallyEquivalent c₁ c₂ := by
  sorry

/-- **Theorem 4.10** (Lifting of homotopic curves, Ch. 1 §4, F1:1075). Let `X`, `Y` be Hausdorff spaces, `p : Y → X` a
local homeomorphism, `â ∈ Y`, and `A : I × I → X` continuous with `A(0, s) = a` and `A(1, s) = b` for all `s`. If every
curve `u_s = A(·, s)` has a lifting `û_s` with `û_s(0) = â`, then `û₀` and `û₁` have the same end point and are homotopic
(relative to the end points).
Modelling: the homotopy of `û₀`, `û₁` is a continuous `H : I × I → Y` with `H(·, 0) = û₀`, `H(·, 1) = û₁`,
`H(0, s) = â`, `H(1, s) = û₀(1)`. -/
theorem thm4_10 {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y] {p : Y → X}
    (hp : IsLocalHomeomorph p) {A : C(I × I, X)} {a b : X} (ha : ∀ s, A (0, s) = a) (hb : ∀ s, A (1, s) = b)
    {â : Y} (û : I → C(I, Y)) (hû : ∀ s, ∀ t, p (û s t) = A (t, s)) (hû0 : ∀ s, û s 0 = â) :
    û 0 1 = û 1 1 ∧ ∃ H : C(I × I, Y), (∀ t, H (t, 0) = û 0 t) ∧ (∀ t, H (t, 1) = û 1 t) ∧
      (∀ s, H (0, s) = â) ∧ ∀ s, H (1, s) = û 0 1 := by
  sorry

/-- **Theorem 4.16** (Ch. 1 §4, F1:1209). Let `X`, `Y` be Hausdorff, `X` pathwise connected, `p : Y → X` a covering map.
Then all fibres have the same cardinality (the number of sheets), and if `Y ≠ ∅`, `p` is surjective. -/
theorem thm4_16 {X Y : Type*} [TopologicalSpace X] [T2Space X] [PathConnectedSpace X] [TopologicalSpace Y]
    [T2Space Y] {p : Y → X} (hp : IsCoveringMap p) :
    (∀ x₀ x₁, numSheets p x₀ = numSheets p x₁) ∧ (Nonempty Y → Function.Surjective p) := by
  sorry

/-- **Remark after Theorem 4.17** (Ch. 1 §4, F1:1219). Theorem 4.17 holds for a local homeomorphism `p : Y → X` of
Hausdorff spaces which has the curve lifting property (instead of a covering map): if `Z` is simply connected, pathwise
connected and locally pathwise connected and `f : Z → X` is continuous with `f(z₀) = p(y₀)`, there is exactly one lifting
`f̂ : Z → Y` with `f̂(z₀) = y₀`. -/
theorem rem4_17 {X Y Z : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y] [TopologicalSpace Z]
    [SimplyConnectedSpace Z] [PathConnectedSpace Z] [LocallyPathConnectedSpace Z] {p : Y → X}
    (hp : IsLocalHomeomorph p) (hl : HasCurveLiftingProperty p) (f : C(Z, X)) (z₀ : Z) (y₀ : Y)
    (hz : f z₀ = p y₀) : ∃! g : C(Z, Y), (p ∘ g) = f ∧ g z₀ = y₀ := by
  sorry

/-- **Theorem 4.19** (Ch. 1 §4, F1:1239). Let `X` be a manifold (Hausdorff, locally Euclidean), `Y` Hausdorff and
`p : Y → X` a local homeomorphism with the curve lifting property. Then `p` is a covering map. -/
theorem thm4_19 {n : ℕ} {X Y : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [TopologicalSpace Y] [T2Space Y] {p : Y → X} (hp : IsLocalHomeomorph p) (hl : HasCurveLiftingProperty p) :
    IsCoveringMap p := by
  sorry

/-- **Lemma 4.21(a)** (Ch. 1 §4, F1:1251). Let `X`, `Y` be locally compact Hausdorff spaces and `p : Y → X` proper and
discrete. Then every fibre of `p` is finite. -/
theorem lemma4_21_a {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TopologicalSpace Y]
    [T2Space Y] [LocallyCompactSpace Y] {p : Y → X} (hp : IsProperMap p) (hd : IsDiscreteMap p) (x : X) :
    (p ⁻¹' {x}).Finite := by
  sorry

/-- **Lemma 4.21(b)** (Ch. 1 §4, F1:1251). With the hypotheses of 4.21(a): every neighbourhood `V` of a fibre `p⁻¹(x)`
contains `p⁻¹(U)` for a neighbourhood `U` of `x`. -/
theorem lemma4_21_b {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TopologicalSpace Y]
    [T2Space Y] [LocallyCompactSpace Y] {p : Y → X} (hp : IsProperMap p) (hd : IsDiscreteMap p) (x : X)
    {V : Set Y} (hV : V ∈ 𝓝ˢ (p ⁻¹' {x})) : ∃ U ∈ 𝓝 x, p ⁻¹' U ⊆ V := by
  sorry

/-- **Theorem 4.22** (Ch. 1 §4, F1:1263). A proper local homeomorphism `p : Y → X` of locally compact Hausdorff spaces is a
covering map. -/
theorem thm4_22 {X Y : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TopologicalSpace Y]
    [T2Space Y] [LocallyCompactSpace Y] {p : Y → X} (hp : IsProperMap p) (hl : IsLocalHomeomorph p) :
    IsCoveringMap p := by
  sorry

section Proper

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **4.23(a)** (Proper holomorphic mappings, Ch. 1 §4, F1:1273). For a proper non-constant holomorphic map `f : X → Y`
the set of branch points is closed and discrete in `X`, and so is the set of critical values in `Y`. -/
theorem para4_23_a {f : X → Y} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hp : IsProperMap f)
    (hnc : ¬ ∃ c, ∀ x, f x = c) :
    IsClosed {x | IsBranchPoint f x} ∧ IsDiscrete {x | IsBranchPoint f x} ∧ IsClosed (criticalValues f) ∧
      IsDiscrete (criticalValues f) := by
  sorry

/-- **4.23(b)** (Proper holomorphic mappings, Ch. 1 §4, F1:1273). For a proper non-constant holomorphic map `f : X → Y`,
with `Y' = Y ∖ B` (`B` the critical values) and `X' = f⁻¹(Y')`, the restriction `f : X' → Y'` is a proper (unbranched)
covering map with a finite number `n` of sheets. -/
theorem para4_23_b {f : X → Y} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hp : IsProperMap f)
    (hnc : ¬ ∃ c, ∀ x, f x = c) :
    ∃ n : ℕ, IsProperMap (Set.restrictPreimage (criticalValues f)ᶜ f) ∧
      IsCoveringMap (Set.restrictPreimage (criticalValues f)ᶜ f) ∧
      ∀ y : ↥(criticalValues f)ᶜ, (Set.restrictPreimage (criticalValues f)ᶜ f ⁻¹' {y}).Finite ∧
        Nat.card ↥(Set.restrictPreimage (criticalValues f)ᶜ f ⁻¹' {y}) = n := by
  sorry

/-- **Theorem 4.24** (Ch. 1 §4, F1:1283). A proper non-constant holomorphic map `f : X → Y` takes every value, counting
multiplicities, the same number `n` of times. -/
theorem thm4_24 {f : X → Y} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hp : IsProperMap f) (hnc : ¬ ∃ c, ∀ x, f x = c) :
    ∃ n : ℕ, ∀ c, valenceCount f c = n := by
  sorry

/-- **Corollary 4.25** (Ch. 1 §4, F1:1289). A non-constant meromorphic function `f : X → ℙ¹` on a compact Riemann surface
has as many zeros as poles, counted with multiplicities. -/
theorem cor4_25 [CompactSpace X] {f : X → References.RiemannSphere} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hnc : ¬ ∃ c, ∀ x, f x = c) :
    valenceCount f (References.RiemannSphere.ofComplex 0) = valenceCount f References.RiemannSphere.infty := by
  sorry

end Proper

end Forster1981
