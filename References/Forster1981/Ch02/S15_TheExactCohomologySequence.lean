import References.Forster1981.Ch02.S14_AFinitenessTheorem

/-!
# Forster, Chapter 2 §15: The exact cohomology sequence

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §15 (`full.md` F1:5197–5587).

Conventions (rulings B0.3, B0.5): sheaf homomorphisms are morphisms of presheaves of modules (`F ⟶ G`); a homomorphism
"induced by" a map `Φ` of representatives is the relation `IsInducedBy α Φ`; the maps `α¹` on `H¹`, the connecting
homomorphism `δ*` and the isomorphisms of Dolbeault and de Rham are relations / existence statements ("for every map with
the property …"). Exactness of sheaves is stalkwise (`TopCat.Presheaf.stalkFunctor`); the book's "well defined / unique"
sentences are the `∃!` statements `para15_10`, `para15_11`. The sheaves `𝒪*, Ω, 𝓩` are built with the generic
`localRepPresheaf`; `𝒪*` is a sheaf of `ℤ`-modules (the additive group of invertible functions).

* Definition 15.1 (sheaf homomorphisms, F1:5201) — exists: `CategoryTheory.NatTrans`
* Paragraph 15.2 (the sheaf homomorphisms `d`, `d′`, `d″`, inclusions, `ex`, F1:5217) — `cechMap`, `IsInducedBy`,
  `modOStar`, `modOZ`, `Form1.IsHolAt`, `Form1.IsClosedAt`, `modOmega`, `modClosedForms`
* Examples 15.3 (kernels, F1:5239) — `holFormsOn`, `example15_3_a`, `example15_3_b`, `example15_3_c`
* Paragraph 15.5 (exactness, F1:5279) — `IsSheafMono`, `IsSheafEpi`, `IsExactSeq`, `IsShortExactSeq`
* Lemma 15.6 (F1:5305) — exists: `TopCat.Presheaf.app_injective_of_stalkFunctor_map_injective`
* Remark 15.7 (F1:5309) — `rem15_7_a`, `rem15_7_b`
* Lemma 15.8 (F1:5311) — `lemma15_8`
* Examples 15.9 (the five short exact sequences, F1:5327) — `example15_9_a`, `example15_9_b`, `example15_9_c`,
  `example15_9_d`, `example15_9_e`
* Paragraph 15.10 (the induced map `α¹`, F1:5387) — `IsH1Induced`, `para15_10`
* Paragraph 15.11 (the connecting homomorphism `δ*`, F1:5413) — `IsConnectingHom`, `para15_11`
* Theorem 15.12 (the exact cohomology sequence, F1:5451) — `thm15_12`
* Theorem 15.13 (F1:5498) — `thm15_13`, `thm15_13_explicit`
* Theorem 15.14 (Dolbeault, F1:5524) — `dBarImage`, `dImage`, `thm15_14_a`, `thm15_14_b`
* Theorem 15.15 (de Rham, F1:5534) — `closedFormsOn`, `exactForms`, `deRham1`, `thm15_15`

Omitted (U−): existence claims of 15.2, the image presheaf of 15.4, "the kernel is a sheaf" (15.3), the two `Rh¹ = 0`
claims and the remark of 15.15.
-/

open scoped Manifold ContDiff Topology References
open Set Filter TopologicalSpace CategoryTheory Opposite

namespace Forster1981

section Defs

variable {R : Type} [CommRing R] {X : Type} [TopologicalSpace X]

/-- **The cochain map induced by a sheaf homomorphism** (15.10, Ch. 2 §15, F1:5387): `α_𝔘 : C¹(𝔘, F) → C¹(𝔘, G)`,
componentwise. -/
def cechMap {F G : TopCat.Presheaf (ModuleCat.{0} R) (TopCat.of X)} (α : F ⟶ G) {ι : Type} (U : ι → Opens X) :
    CechC1 F U →ₗ[R] CechC1 G U :=
  LinearMap.pi fun i => LinearMap.pi fun j => (α.app (op (U i ⊓ U j))).hom ∘ₗ (LinearMap.proj j ∘ₗ LinearMap.proj i)

/-- **Homomorphisms induced by a map of representatives** (15.2, Ch. 2 §15, F1:5217): the sheaf homomorphism `α` between
sheaves of local representatives sends the class of `a` over `U` to the class of `Φ a`. -/
def IsInducedBy {A B : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] {pA nA : A → X → Prop}
    {pB nB : B → X → Prop} (α : localRepPresheaf R pA nA ⟶ localRepPresheaf R pB nB) (Φ : A → B) : Prop :=
  ∀ (U : (Opens X)ᵒᵖ) (a : A) (ha : a ∈ repSpan (R := R) pA (U.unop : Set X)),
    ∃ hb : Φ a ∈ repSpan (R := R) pB (U.unop : Set X),
      α.app U (Submodule.Quotient.mk ⟨a, ha⟩) = Submodule.Quotient.mk ⟨Φ a, hb⟩

variable (F G H : TopCat.Presheaf (ModuleCat.{0} R) (TopCat.of X))

/-- **Monomorphisms of sheaves** (15.5, Ch. 2 §15, F1:5279): injective on every stalk. -/
def IsSheafMono (α : F ⟶ G) : Prop :=
  ∀ x : X, Function.Injective ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} R) x).map α).hom

/-- **Epimorphisms of sheaves** (15.5, Ch. 2 §15, F1:5279): surjective on every stalk. -/
def IsSheafEpi (α : F ⟶ G) : Prop :=
  ∀ x : X, Function.Surjective ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} R) x).map α).hom

/-- **Exactness at the middle** (15.5, Ch. 2 §15, F1:5279): `Ker β_x = Im α_x` on every stalk. -/
def IsExactSeq (α : F ⟶ G) (β : G ⟶ H) : Prop :=
  ∀ x : X, LinearMap.ker ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} R) x).map β).hom =
    LinearMap.range ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} R) x).map α).hom

/-- **Short exact sequences** `0 → F → G → H → 0` (15.5, Ch. 2 §15, F1:5279). -/
def IsShortExactSeq (α : F ⟶ G) (β : G ⟶ H) : Prop :=
  IsSheafMono F G α ∧ IsExactSeq F G H α β ∧ IsSheafEpi G H β

/-- **The map `α¹` on `H¹`** (15.10, Ch. 2 §15, F1:5387): `α₁ [c] = [α_𝔘 c]` for every covering `𝔘` of `X` and cocycle `c`. -/
def IsH1Induced (α : F ⟶ G) (α₁ : H1 F ⊤ →ₗ[R] H1 G ⊤) : Prop :=
  ∀ (𝔘 : CechCover X ⊤) (ξ : ↥(cechZ1 F 𝔘.U)),
    ∃ h : cechMap α 𝔘.U ξ ∈ cechZ1 G 𝔘.U, α₁ (cechClass F 𝔘 ξ) = cechClass G 𝔘 ⟨cechMap α 𝔘.U ξ, h⟩

/-- **The connecting homomorphism `δ*`** (15.11, Ch. 2 §15, F1:5413): for `h ∈ H⁰(X, H)` and a covering `𝔘` of `X` with
`g_i ∈ G(U_i)` mapping to `h|U_i`, the cochain `δg` comes from a cocycle `ξ ∈ Z¹(𝔘, F)` (`α_𝔘 ξ = δg`), and
`δ* h = [ξ]`. -/
def IsConnectingHom (α : F ⟶ G) (β : G ⟶ H) (δ : H0 H →ₗ[R] H1 F ⊤) : Prop :=
  ∀ (h : H0 H) (𝔘 : CechCover X ⊤) (g : CechC0 G 𝔘.U),
    (∀ i, (β.app (op (𝔘.U i))) (g i) = cechRes H (le_top : 𝔘.U i ≤ ⊤) h) →
      ∃ ξ : ↥(cechZ1 F 𝔘.U), cechMap α 𝔘.U ξ = cechD0 G 𝔘.U g ∧ δ h = cechClass F 𝔘 ξ

end Defs

section Sheaves

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Holomorphic coefficient at a point: the coefficient of `dz` is complex differentiable at the point in every chart. -/
def Form1.IsHolAt (w : Form1 X) (x : X) : Prop :=
  ∀ y z, z ∈ (chartAt ℂ y).target → (chartAt ℂ y).symm z = x → DifferentiableAt ℂ (w.1 y) z

/-- Closed near a point: smooth with `dω = 0` on a neighbourhood. -/
def Form1.IsClosedAt (w : Form1 X) (x : X) : Prop :=
  ∃ Y ∈ 𝓝 x, w.IsSmoothOn Y ∧ Form2.VanishOn w.d Y

/-- The global space `Ω(Y)` of holomorphic 1-forms (representatives). -/
def holFormsOn (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (Y : Set X) : Submodule ℂ (Form1 X) :=
  repSpan (fun (w : Form1 X) x => w.IsFormOn {x} ∧ w.IsType10On {x} ∧ w.IsHolAt x) Y

/-- The global space `𝓩(Y)` of closed 1-forms (representatives). -/
def closedFormsOn (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (Y : Set X) : Submodule ℂ (Form1 X) :=
  repSpan (fun (w : Form1 X) x => w.IsFormOn {x} ∧ w.IsClosedAt x) Y

/-- **The sheaf `Ω`** of holomorphic 1-forms (15.2, Ch. 2 §15, F1:5217). -/
abbrev modOmega (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  localRepPresheaf ℂ (A := Form1 X) (fun w x => w.IsFormOn {x} ∧ w.IsType10On {x} ∧ w.IsHolAt x)
    (fun w x => w.VanishOn {x})

/-- **The sheaf `𝓩`** of closed differentiable 1-forms (15.2, Ch. 2 §15, F1:5217). -/
abbrev modClosedForms (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] :
    TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  localRepPresheaf ℂ (A := Form1 X) (fun w x => w.IsFormOn {x} ∧ w.IsClosedAt x) (fun w x => w.VanishOn {x})

/-- **The sheaf `𝒪*`** of nowhere vanishing holomorphic functions, as a sheaf of `ℤ`-modules (the additive group of
functions to `ℂˣ`; the neutral element is the constant `1`). -/
abbrev modOStar (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : TopCat.Presheaf (ModuleCat.{0} ℤ) (TopCat.of X) :=
  localRepPresheaf ℤ (A := Additive (X → ℂˣ))
    (fun a x => MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun y => ((Additive.toMul a y : ℂˣ) : ℂ)) x)
    (fun a x => Additive.toMul a x = 1)

/-- **The sheaf `𝒪` as a sheaf of `ℤ`-modules** (restriction of scalars). -/
noncomputable abbrev modOZ (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : TopCat.Presheaf (ModuleCat.{0} ℤ) (TopCat.of X) :=
  modO X ⋙ ModuleCat.restrictScalars (Int.castRingHom ℂ)

/-- The image `d″𝓔(X)` in the space of 1-forms. -/
noncomputable def dBarImage (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Submodule ℂ (Form1 X) :=
  Submodule.span ℂ (dFormBar '' (smoothFunOn X ⊤ : Set (X → ℂ)))

/-- The image `dℰ^{1,0}(X)` in the space of 2-forms. -/
noncomputable def dImage (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Submodule ℂ (Form2 X) :=
  Submodule.span ℂ (Form1.d '' (smoothForms10On X ⊤ : Set (Form1 X)))

/-- The space `dℰ(X)` of exact 1-forms. -/
noncomputable def exactForms (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Submodule ℂ (Form1 X) :=
  Submodule.span ℂ (dForm '' (smoothFunOn X ⊤ : Set (X → ℂ)))

/-- **The de Rham group** `Rh¹(X) = 𝓩(X)/dℰ(X)` (15.15, Ch. 2 §15, F1:5534). -/
abbrev deRham1 (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Type :=
  ↥(closedFormsOn X ⊤) ⧸ (exactForms X).comap (closedFormsOn X ⊤).subtype

end Sheaves

section Statements

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Example 15.3(a)** (Ch. 2 §15, F1:5239). `𝒪 = Ker d″`: a differentiable function on `Y` is holomorphic iff `d″f = 0`. -/
theorem example15_3_a (Y : Set X) {f : X → ℂ} (hf : f ∈ smoothFunOn X Y) :
    f ∈ holOn X Y ↔ (dFormBar f).VanishOn Y := by
  sorry

/-- **Example 15.3(b)** (Ch. 2 §15, F1:5239). `Ω = Ker d` on `ℰ^{1,0}`: a differentiable `(1, 0)`-form on `Y` is holomorphic
iff `dω = 0`. -/
theorem example15_3_b (Y : Set X) {w : Form1 X} (hw : w ∈ smoothForms10On X Y) :
    w ∈ holFormsOn X Y ↔ Form2.VanishOn w.d Y := by
  sorry

/-- **Example 15.3(c)** (Ch. 2 §15, F1:5239). `ℤ = Ker ex`: a holomorphic function `f` on `Y` satisfies `e^{2πif} = 1`
iff it is a locally constant integer valued function. -/
theorem example15_3_c (Y : Set X) {f : X → ℂ} (hf : f ∈ holOn X Y) :
    (∀ x ∈ Y, Complex.exp (2 * Real.pi * Complex.I * f x) = 1) ↔
      ∃ g : X → ℤ, (∀ x ∈ Y, IsLocConstAt g x) ∧ ∀ x ∈ Y, f x = g x := by
  sorry

/-- **Remark 15.7(a)** (Ch. 2 §15, F1:5309). `ex : 𝒪 → 𝒪*`, `f ↦ e^{2πif}`, is an epimorphism: every nowhere vanishing
function holomorphic at `x` has a holomorphic logarithm near `x`. Modelling: "holomorphic at `x`" is the germ notion
(differentiable on a neighbourhood of `x`), not differentiability at the single point `x`. -/
theorem rem15_7_a (x : X) {u : X → ℂˣ}
    (hu : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun y => ((u y : ℂˣ) : ℂ)) y) :
    ∃ f : X → ℂ, (∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) ∧
      ∀ᶠ y in 𝓝 x, Complex.exp (2 * Real.pi * Complex.I * f y) = (u y : ℂ) := by
  sorry

/-- **Remark 15.7(b)** (Ch. 2 §15, F1:5309). On `X = ℂ*`, `ex : 𝒪(X) → 𝒪*(X)` is not surjective: the identity has no
holomorphic logarithm. -/
theorem rem15_7_b : ¬ ∃ f : ℂ → ℂ, DifferentiableOn ℂ f {0}ᶜ ∧ ∀ z ∈ ({0}ᶜ : Set ℂ), Complex.exp (2 * Real.pi * Complex.I * f z) = z := by
  sorry

variable {R : Type} [CommRing R]

/-- **Lemma 15.8** (Ch. 2 §15, F1:5311). If `0 → F → G → H → 0` is a short exact sequence of sheaves, then for every open
`Y` the sequence `0 → F(Y) → G(Y) → H(Y)` is exact. -/
theorem lemma15_8 {F G H : TopCat.Presheaf (ModuleCat.{0} R) (TopCat.of X)} (hF : F.IsSheaf) (hG : G.IsSheaf)
    (hH : H.IsSheaf) {α : F ⟶ G} {β : G ⟶ H} (h : IsShortExactSeq F G H α β) (Y : Opens X) :
    Function.Injective (α.app (op Y)).hom ∧
      LinearMap.ker (β.app (op Y)).hom = LinearMap.range (α.app (op Y)).hom := by
  sorry

/-- **Example 15.9(a)** (Ch. 2 §15, F1:5327). `0 → 𝒪 → ℰ → ℰ^{0,1} → 0` with `f ↦ f`, `f ↦ d″f`. -/
theorem example15_9_a : ∃ (α : modO X ⟶ modE X) (β : modE X ⟶ modE01 X),
    IsInducedBy α (id : (X → ℂ) → (X → ℂ)) ∧ IsInducedBy β dFormBar ∧ IsShortExactSeq _ _ _ α β := by
  sorry

/-- **Example 15.9(b)** (Ch. 2 §15, F1:5327). `0 → ℂ → ℰ → 𝓩 → 0` with `f ↦ f`, `f ↦ df`. -/
theorem example15_9_b : ∃ (α : modC X ⟶ modE X) (β : modE X ⟶ modClosedForms X),
    IsInducedBy α (id : (X → ℂ) → (X → ℂ)) ∧ IsInducedBy β dForm ∧ IsShortExactSeq _ _ _ α β := by
  sorry

/-- **Example 15.9(c)** (Ch. 2 §15, F1:5327). `0 → ℂ → 𝒪 → Ω → 0` with `f ↦ f`, `f ↦ df`. -/
theorem example15_9_c : ∃ (α : modC X ⟶ modO X) (β : modO X ⟶ modOmega X),
    IsInducedBy α (id : (X → ℂ) → (X → ℂ)) ∧ IsInducedBy β dFormHol ∧ IsShortExactSeq _ _ _ α β := by
  sorry

/-- **Example 15.9(d)** (Ch. 2 §15, F1:5327). `0 → Ω → ℰ^{1,0} → ℰ^(2) → 0` with `ω ↦ ω`, `ω ↦ dω`. -/
theorem example15_9_d : ∃ (α : modOmega X ⟶ modE10 X) (β : modE10 X ⟶ modE2 X),
    IsInducedBy α (id : Form1 X → Form1 X) ∧ IsInducedBy β Form1.d ∧ IsShortExactSeq _ _ _ α β := by
  sorry

/-- **Example 15.9(e)** (Ch. 2 §15, F1:5327). `0 → ℤ → 𝒪 → 𝒪* → 0` with `n ↦ n`, `f ↦ e^{2πif}`.
Modelling: `ℤ`-modules; `𝒪` through restriction of scalars. -/
theorem example15_9_e : ∃ (α : modZ X ⟶ modOZ X) (β : modOZ X ⟶ modOStar X), IsShortExactSeq _ _ _ α β ∧
    (∀ (Y : Opens X) (n : X → ℤ) (hn : n ∈ repSpan (R := ℤ) IsLocConstAt (Y : Set X)),
      ∃ hn' : (fun x => (n x : ℂ)) ∈ repSpan (R := ℂ) IsHolFunAt (Y : Set X),
        (α.app (op Y) (Submodule.Quotient.mk ⟨n, hn⟩) : ↥((modO X).obj (op Y))) =
          Submodule.Quotient.mk ⟨fun x => (n x : ℂ), hn'⟩) ∧
    (∀ (Y : Opens X) (f : X → ℂ) (hf : f ∈ repSpan (R := ℂ) IsHolFunAt (Y : Set X)),
      ∃ hf' : (Additive.ofMul fun x => (Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * f x))
          (Complex.exp_ne_zero _))) ∈ repSpan (R := ℤ) (fun (a : Additive (X → ℂˣ)) x =>
            MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun y => ((Additive.toMul a y : ℂˣ) : ℂ)) x) (Y : Set X),
        β.app (op Y) (Submodule.Quotient.mk ⟨f, hf⟩) = Submodule.Quotient.mk ⟨_, hf'⟩) := by
  sorry

/-- **Paragraph 15.10** (Ch. 2 §15, F1:5387). A sheaf homomorphism `α : F → G` induces a unique homomorphism
`α¹ : H¹(X, F) → H¹(X, G)` with `α¹ [c] = [α_𝔘 c]`. -/
theorem para15_10 {F G : TopCat.Presheaf (ModuleCat.{0} R) (TopCat.of X)} (hF : F.IsSheaf) (hG : G.IsSheaf) (α : F ⟶ G) :
    ∃! α₁ : H1 F ⊤ →ₗ[R] H1 G ⊤, IsH1Induced F G α α₁ := by
  sorry

/-- **Paragraph 15.11** (Ch. 2 §15, F1:5413). For a short exact sequence of sheaves `0 → F → G → H → 0` there is a unique
connecting homomorphism `δ* : H⁰(X, H) → H¹(X, F)` with the property of 15.11. -/
theorem para15_11 {F G H : TopCat.Presheaf (ModuleCat.{0} R) (TopCat.of X)} (hF : F.IsSheaf) (hG : G.IsSheaf)
    (hH : H.IsSheaf) {α : F ⟶ G} {β : G ⟶ H} (h : IsShortExactSeq F G H α β) :
    ∃! δ : H0 H →ₗ[R] H1 F ⊤, IsConnectingHom F G H α β δ := by
  sorry

/-- **Theorem 15.12** (the exact cohomology sequence, Ch. 2 §15, F1:5451). For a short exact sequence of sheaves
`0 → F → G → H → 0` and the maps `α¹`, `β¹`, `δ*` of 15.10, 15.11, the sequence
`0 → F(X) → G(X) → H(X) → H¹(X, F) → H¹(X, G) → H¹(X, H)` is exact. -/
theorem thm15_12 {F G H : TopCat.Presheaf (ModuleCat.{0} R) (TopCat.of X)} (hF : F.IsSheaf) (hG : G.IsSheaf)
    (hH : H.IsSheaf) {α : F ⟶ G} {β : G ⟶ H} (h : IsShortExactSeq F G H α β) {α₁ : H1 F ⊤ →ₗ[R] H1 G ⊤}
    {β₁ : H1 G ⊤ →ₗ[R] H1 H ⊤} {δ : H0 H →ₗ[R] H1 F ⊤} (hα : IsH1Induced F G α α₁)
    (hβ : IsH1Induced G H β β₁) (hδ : IsConnectingHom F G H α β δ) :
    Function.Injective (α.app (op ⊤)).hom ∧
      LinearMap.ker (β.app (op ⊤)).hom = LinearMap.range (α.app (op ⊤)).hom ∧
      LinearMap.ker δ = LinearMap.range (β.app (op ⊤)).hom ∧
      LinearMap.ker α₁ = LinearMap.range δ ∧ LinearMap.ker β₁ = LinearMap.range α₁ := by
  sorry

/-- **Theorem 15.13** (Ch. 2 §15, F1:5498). Let `0 → F → G → H → 0` be a short exact sequence of sheaves with
`H¹(X, G) = 0`. Then `H¹(X, F) ≅ H⁰(X, H)/β(H⁰(X, G))`. -/
theorem thm15_13 {F G H : TopCat.Presheaf (ModuleCat.{0} R) (TopCat.of X)} (hF : F.IsSheaf) (hG : G.IsSheaf)
    (hH : H.IsSheaf) {α : F ⟶ G} {β : G ⟶ H} (h : IsShortExactSeq F G H α β) (h1 : Subsingleton (H1 G ⊤)) :
    Nonempty (H1 F ⊤ ≃ₗ[R] (H0 H ⧸ LinearMap.range (β.app (op ⊤)).hom)) := by
  sorry

/-- **Theorem 15.13, explicit form** (Ch. 2 §15, F1:5498). Under the assumptions of 15.13 the isomorphism is induced by the
connecting homomorphism: for every `δ*` there is a linear equivalence `Φ` with `Φ ∘ mk = δ*`. -/
theorem thm15_13_explicit {F G H : TopCat.Presheaf (ModuleCat.{0} R) (TopCat.of X)} (hF : F.IsSheaf) (hG : G.IsSheaf)
    (hH : H.IsSheaf) {α : F ⟶ G} {β : G ⟶ H} (h : IsShortExactSeq F G H α β) (h1 : Subsingleton (H1 G ⊤))
    {δ : H0 H →ₗ[R] H1 F ⊤} (hδ : IsConnectingHom F G H α β δ) :
    ∃ Φ : (H0 H ⧸ LinearMap.range (β.app (op ⊤)).hom) ≃ₗ[R] H1 F ⊤, ∀ c : H0 H, Φ (Submodule.Quotient.mk c) = δ c := by
  sorry

/-- **Theorem 15.14(a)** (Dolbeault's isomorphism, Ch. 2 §15, F1:5524). `H¹(X, 𝒪) ≅ ℰ^{0,1}(X)/d″𝓔(X)`. -/
theorem thm15_14_a :
    Nonempty (H1 (modO X) ⊤ ≃ₗ[ℂ] (↥(smoothForms01On X ⊤) ⧸ (dBarImage X).comap (smoothForms01On X ⊤).subtype)) := by
  sorry

/-- **Theorem 15.14(b)** (Ch. 2 §15, F1:5524). `H¹(X, Ω) ≅ ℰ^(2)(X)/dℰ^{1,0}(X)`. -/
theorem thm15_14_b :
    Nonempty (H1 (modOmega X) ⊤ ≃ₗ[ℂ] (↥(smoothForms2On X ⊤) ⧸ (dImage X).comap (smoothForms2On X ⊤).subtype)) := by
  sorry

/-- **Theorem 15.15** (de Rham's isomorphism, Ch. 2 §15, F1:5534). `H¹(X, ℂ) ≅ Rh¹(X) = 𝓩(X)/dℰ(X)`. -/
theorem thm15_15 : Nonempty (H1 (modC X) ⊤ ≃ₗ[ℂ] deRham1 X) := by
  sorry

end Statements

end Forster1981
