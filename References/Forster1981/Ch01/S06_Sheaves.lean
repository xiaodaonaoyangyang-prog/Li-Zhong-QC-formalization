import References.Forster1981.Ch01.S05_TheUniversalCoveringAndCoveringTransformations

/-!
# Forster, Chapter 1 §6: Sheaves

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §6 (`full.md` F1:1651–1810).

Conventions: sheaves are Mathlib's `TopCat.Presheaf`/`TopCat.Presheaf.IsSheaf`; the concrete sheaves of functions are
`TopCat.subsheafToTypes` of local predicates on the space `TopCat.of X`, `X : Type` (universe `0`, as in all Forster
files). The value `φ(a)` of a germ is `TopCat.stalkToFiber`. A local predicate is built from pointwise conditions on the
function extended by a default value, which depend only on the germ (`pointwiseLocalPredicate`). Following 1.15, the
sheaf `𝓜` of meromorphic functions is the sheaf of holomorphic maps into `ℙ¹` which are nowhere locally `≡ ∞` (sections
with values read as germs, so there is no junk at the poles).

* Definition 6.1 (presheaf, F1:1655) — exists: `TopCat.Presheaf`
* Definition 6.3 (sheaf, axioms (I), (II), F1:1679) — exists: `TopCat.Presheaf.IsSheaf`
* Examples 6.4(b), (c), (e) (the sheaves 𝒪, 𝓜, 𝒪*, 𝓜*, and locally constant functions, F1:1699) — `pointwiseLocalPredicate`,
  `sheafO`, `sheafM`, `sheafOStar`, `sheafMStar`, `sheafLocConst`
* Paragraph 6.5 (stalk, germ, value of a germ, F1:1707) — exists: `TopCat.Presheaf.stalk`, `TopCat.Presheaf.germ`,
  `TopCat.stalkToFiber`
* Lemma 6.6 (F1:1737) — exists: `TopCat.Presheaf.section_ext`
* Paragraph 6.7 (the space `|𝓕|` associated to a presheaf, F1:1741) — exists: `TopCat.Presheaf.EtaleSpace`,
  `TopCat.Presheaf.EtaleSpace.base`
* Paragraph 6.7 (the basic open sets of `|𝓕|`, F1:1745) — `etaleBasicOpen`
* Theorem 6.8 (F1:1759) — `thm6_8`
* Definition 6.9 (presheaf satisfying the identity theorem, F1:1771) — `SatisfiesIdentityTheorem`
* Examples in 6.9 (𝒪 and 𝓜 satisfy the identity theorem, F1:1773) — `rem6_9_O`, `rem6_9_M`
* Theorem 6.10 (F1:1775) — `thm6_10`

Omitted (U−): Example 6.2 and 6.4(a) (the sheaf of continuous functions, F1:1677, 1697), Example 6.4(d) (F1:1705), remarks
of 6.1 and 6.3, the algebraic structure of stalks and `𝒪_a ≅ ℂ{z − a}` (F1:1707–1735).
-/

open scoped Manifold ContDiff Topology References
open Set Filter TopologicalSpace CategoryTheory

namespace Forster1981

open scoped Forster1981

open scoped Classical in
/-- **The local predicate of a pointwise condition** (helper for the sheaves of Example 6.4). A condition `Q x g` on a
function `g : X → T` at the point `x`, depending only on the germ of `g` at `x` (`hQ`), defines the local predicate on
sections `f : U → T` ("`Q x` holds at every `x ∈ U` for `f` extended by the default value `d` outside `U`").
The restriction and gluing axioms hold because `Q` depends on the germ only. -/
def pointwiseLocalPredicate {X : Type} [TopologicalSpace X] {T : Type} (d : T) (Q : X → (X → T) → Prop)
    (hQ : ∀ x g g', g =ᶠ[𝓝 x] g' → (Q x g ↔ Q x g')) :
    TopCat.LocalPredicate (fun _ : TopCat.of X => T) where
  pred {U} f := ∀ x : U, Q x.1 (fun y => if h : y ∈ U then f ⟨y, h⟩ else d)
  res := by
    intro Us Ub i f h x
    refine (hQ x.1 _ _ ?_).1 (h ⟨x.1, i.le x.2⟩)
    filter_upwards [Us.2.mem_nhds x.2] with y hy
    have hyU : y ∈ Us := hy
    have hyB : y ∈ Ub := i.le hyU
    show (if h : y ∈ Ub then f ⟨y, h⟩ else d) = (if h : y ∈ Us then f ⟨y, i.le h⟩ else d)
    simp only [hyB, hyU, dite_true]
  locality := by
    intro U f h x
    obtain ⟨V, hx, i, hV⟩ := h x
    refine (hQ x.1 _ _ ?_).1 (hV ⟨x.1, hx⟩)
    filter_upwards [V.2.mem_nhds hx] with y hy
    have hyV : y ∈ V := hy
    have hyU : y ∈ U := i.le hyV
    show (if h : y ∈ V then f ⟨y, i.le h⟩ else d) = (if h : y ∈ U then f ⟨y, h⟩ else d)
    simp only [hyV, hyU, dite_true]

section Sheaves

variable (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **The sheaf `𝒪` of holomorphic functions** (Example 6.4(b), Ch. 1 §6, F1:1699): sections over `U` are the
functions `U → ℂ` which are holomorphic at every point. -/
noncomputable def sheafO : TopCat.Sheaf (Type) (TopCat.of X) :=
  TopCat.subsheafToTypes (pointwiseLocalPredicate (X := X) (T := ℂ) 0
    (fun x g => MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g x)
    (fun _ _ _ h => ⟨fun hg => hg.congr_of_eventuallyEq h.symm, fun hg => hg.congr_of_eventuallyEq h⟩))

/-- **The sheaf `𝒪*` of nowhere-vanishing holomorphic functions** (Example 6.4(c), F1:1701), the units of `𝒪`. -/
noncomputable def sheafOStar : TopCat.Sheaf (Type) (TopCat.of X) :=
  TopCat.subsheafToTypes (pointwiseLocalPredicate (X := X) (T := ℂ) 1
    (fun x g => MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g x ∧ g x ≠ 0)
    (fun x g g' h => by
      rw [h.eq_of_nhds]
      exact ⟨fun hg => ⟨hg.1.congr_of_eventuallyEq h.symm, hg.2⟩, fun hg => ⟨hg.1.congr_of_eventuallyEq h, hg.2⟩⟩))

/-- **The sheaf `𝓜` of meromorphic functions** (Example 6.4(b), F1:1699), by Theorem 1.15: sections over `U` are the
holomorphic maps `U → ℙ¹` which are not identically `∞` near any point.
Modelling: a meromorphic function is a holomorphic map into the Riemann sphere (value `∞` at the poles). -/
noncomputable def sheafM : TopCat.Sheaf (Type) (TopCat.of X) :=
  TopCat.subsheafToTypes (pointwiseLocalPredicate (X := X) (T := References.RiemannSphere)
    References.RiemannSphere.infty
    (fun x g => MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g x ∧ ¬ ∀ᶠ y in 𝓝 x, g y = References.RiemannSphere.infty)
    (fun x g g' h => by
      constructor
      · rintro ⟨hg, hn⟩
        exact ⟨hg.congr_of_eventuallyEq h.symm, fun hc => hn (by filter_upwards [h, hc] with y h1 h2; rw [h1, h2])⟩
      · rintro ⟨hg, hn⟩
        exact ⟨hg.congr_of_eventuallyEq h, fun hc => hn (by filter_upwards [h, hc] with y h1 h2; rw [← h1, h2])⟩))

/-- **The sheaf `𝓜*` of meromorphic functions not identically zero** (Example 6.4(c), F1:1701): the holomorphic maps
`U → ℙ¹` which are nowhere locally `≡ ∞` and nowhere locally `≡ 0`. -/
noncomputable def sheafMStar : TopCat.Sheaf (Type) (TopCat.of X) :=
  TopCat.subsheafToTypes (pointwiseLocalPredicate (X := X) (T := References.RiemannSphere)
    (References.RiemannSphere.ofComplex 1)
    (fun x g => MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g x ∧ ¬ (∀ᶠ y in 𝓝 x, g y = References.RiemannSphere.infty) ∧
      ¬ ∀ᶠ y in 𝓝 x, g y = References.RiemannSphere.ofComplex 0)
    (fun x g g' h => by
      constructor
      · rintro ⟨hg, hn1, hn2⟩
        exact ⟨hg.congr_of_eventuallyEq h.symm, fun hc => hn1 (by filter_upwards [h, hc] with y h1 h2; rw [h1, h2]),
          fun hc => hn2 (by filter_upwards [h, hc] with y h1 h2; rw [h1, h2])⟩
      · rintro ⟨hg, hn1, hn2⟩
        exact ⟨hg.congr_of_eventuallyEq h, fun hc => hn1 (by filter_upwards [h, hc] with y h1 h2; rw [← h1, h2]),
          fun hc => hn2 (by filter_upwards [h, hc] with y h1 h2; rw [← h1, h2])⟩))

end Sheaves

/-- **The sheaf of locally constant functions** with values in an abelian group `G` (Example 6.4(e), Ch. 1 §6, F1:1705). -/
noncomputable def sheafLocConst (X : Type) [TopologicalSpace X] (G : Type) [AddCommGroup G] :
    TopCat.Sheaf (Type) (TopCat.of X) :=
  TopCat.subsheafToTypes (pointwiseLocalPredicate (X := X) (T := G) 0 (fun x g => ∀ᶠ y in 𝓝 x, g y = g x)
    (fun x g g' h => by
      constructor
      · intro hg
        filter_upwards [h, hg] with y h1 h2
        rw [← h1, h2, h.eq_of_nhds]
      · intro hg
        filter_upwards [h, hg] with y h1 h2
        rw [h1, h2, ← h.eq_of_nhds]))

/-- **The basic open sets `[U, f]`** of the space `|𝓕|` associated to a presheaf (6.7, Ch. 1 §6, F1:1756): the germs at
the points of `U` of a section `f ∈ 𝓕(U)`. -/
def etaleBasicOpen {X : TopCat} (F : TopCat.Presheaf (Type) X) (U : Opens X) (f : F.obj (Opposite.op U)) :
    Set F.EtaleSpace :=
  {g | ∃ h : g.base ∈ U, g.germ = F.germ U g.base h f}

/-- **Definition 6.9** (Ch. 1 §6, F1:1771). A presheaf `𝓕` on `X` *satisfies the Identity Theorem* if for every domain
(connected open set) `Y ⊆ X` and sections `f, g ∈ 𝓕(Y)` whose germs agree at one point, `f = g`. -/
def SatisfiesIdentityTheorem {X : TopCat} (F : TopCat.Presheaf (Type) X) : Prop :=
  ∀ (Y : Opens X), IsConnected (Y : Set X) → ∀ f g : F.obj (Opposite.op Y),
    (∃ y : Y, F.germ Y y.1 y.2 f = F.germ Y y.1 y.2 g) → f = g

/-- **Theorem 6.8** (Ch. 1 §6, F1:1759). For a presheaf `𝓕` on `X`, the sets `[U, f]` form a basis of a topology on
`|𝓕|`, and the projection `p : |𝓕| → X` is a local homeomorphism. -/
theorem thm6_8 {X : TopCat} (F : TopCat.Presheaf (Type) X) :
    IsTopologicalBasis {S | ∃ (U : Opens X) (f : F.obj (Opposite.op U)), S = etaleBasicOpen F U f} ∧
      IsLocalHomeomorph (TopCat.Presheaf.EtaleSpace.base (F := F)) := by
  sorry

section Identity

variable (X : Type) [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Example in 6.9** (Ch. 1 §6, F1:1773). The sheaf `𝒪` of holomorphic functions satisfies the Identity Theorem. -/
theorem rem6_9_O : SatisfiesIdentityTheorem (sheafO X).presheaf := by
  sorry

/-- **Example in 6.9** (Ch. 1 §6, F1:1773). The sheaf `𝓜` of meromorphic functions satisfies the Identity Theorem. -/
theorem rem6_9_M : SatisfiesIdentityTheorem (sheafM X).presheaf := by
  sorry

end Identity

/-- **Theorem 6.10** (Ch. 1 §6, F1:1775). Let `X` be a locally connected Hausdorff space and `𝓕` a presheaf on `X`
satisfying the Identity Theorem. Then the space `|𝓕|` is Hausdorff. -/
theorem thm6_10 {X : Type} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    (F : TopCat.Presheaf (Type) (TopCat.of X)) (hF : SatisfiesIdentityTheorem F) : T2Space F.EtaleSpace := by
  sorry

end Forster1981
