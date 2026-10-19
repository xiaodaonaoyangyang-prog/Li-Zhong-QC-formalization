import References.Forster1981.Ch01.S11_LinearDifferentialEquations

/-!
# Forster, Chapter 2 §12: Cohomology groups

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §12 (`full.md` F1:3991–4390).

Conventions (Part B, rulings B0.1, B0.2, B0.14): a sheaf of `R`-modules on `X` is a presheaf
`F : TopCat.Presheaf (ModuleCat.{0} R) (TopCat.of X)` (with `F.IsSheaf` in the general statements). The Čech cochain groups
`CechC0/1/2 F U` are Pi-modules over an arbitrary family `U : ι → Opens X` (the family need not cover: §14 uses
non-covering families). `H¹(Y, F)` is the inductive limit of the groups `H¹(𝔘, F)` over the coverings `𝔘` of `Y`,
presented as the quotient of the direct sum of the cocycle groups `Z¹(𝔘)` by the relations `ξ ~ t ξ` (refinement) and
`ξ ~ 0` (coboundaries) (12.3–12.5). The concrete sheaves of modules `ℰ, ℰ^(1), ℰ^{1,0}, ℰ^{0,1}, ℰ^(2), ℂ, ℤ` are built
by the generic `localRepPresheaf`: sections over `U` are the representatives `a` of an ambient module with a pointwise
property `p a x` for all `x ∈ U`, modulo those with a pointwise property `n a x` on `U`. Forms are the coefficient pairs of
Part A; the local transformation law on a set is `Form1.IsFormOn`.

* Paragraph 12.1 (cochains, `δ`, `Z¹`, `B¹`, F1:3995) — `CechC0`, `CechC1`, `CechC2`, `cechRes`, `cechD0`, `cechD1`,
  `cechZ1`, `cechB1`
* Paragraph 12.2 (`H¹(𝔘, F)`, refinement `t`, F1:4065) — `H1Cov`, `IsRefinementMap`, `cechRefine`
* Lemma 12.3 (F1:4095) — `lemma12_3`
* Lemma 12.4 (F1:4123) — `lemma12_4`
* Paragraph 12.5 (`H¹(X, F)`, `[c]`, F1:4153) — `CechCover`, `H1`, `cechClass`, `para12_5_a`, `para12_5_b`
* Theorem 12.6 (F1:4175) — `repSpan`, `localRepPresheaf`, `IsSmoothFunAt`, `modE`, `thm12_6`
* Remark 12.6 (F1:4203) — `Form1.IsFormOn`, `Form1.IsType10On`, `Form1.IsType01On`, `Form1.VanishOn`, `Form2.IsFormOn`,
  `Form2.VanishOn`, `modE1`, `modE10`, `modE01`, `modE2`, `rem12_6_a`, `rem12_6_b`, `rem12_6_c`, `rem12_6_d`
* Theorem 12.7 (F1:4205) — `IsLocConstAt`, `modC`, `modZ`, `thm12_7_a`, `thm12_7_b`
* Paragraph 12.8 (Leray coverings, F1:4263) — `IsLerayCovering`, `thm12_8`
* Paragraph 12.10 (`H⁰(X, F)`, F1:4323) — `H0`
* Global spaces of representatives (the book's `𝓔(X)`, `ℰ^{0,1}(X)`, …, §15) — `smoothFunOn`, `locConstOn`,
  `smoothForms1On`, `smoothForms10On`, `smoothForms01On`, `smoothForms2On`

Omitted (U−): `f_ii = 0` and "the coboundary is a cocycle" (12.1), Example 12.9, the isomorphism `H⁰(𝔘) ≅ F(X)`
(12.10).
-/

open scoped Manifold ContDiff Topology References
open Set Filter CategoryTheory Opposite TopologicalSpace

namespace Forster1981

section Cech

variable {R : Type} [CommRing R] {X : Type} [TopologicalSpace X] (F : TopCat.Presheaf (ModuleCat.{0} R) (TopCat.of X))
  {ι : Type} (U : ι → Opens X)

/-- **The restriction** `F(V) → F(W)` for `W ≤ V` as a linear map. -/
def cechRes {V W : Opens X} (h : W ≤ V) : F.obj (op V) →ₗ[R] F.obj (op W) := (F.map (homOfLE h).op).hom

/-- **0-cochains** (12.1, Ch. 2 §12, F1:3995): `(f_i)` with `f_i ∈ F(U_i)`. -/
abbrev CechC0 : Type := (i : ι) → F.obj (op (U i))

/-- **1-cochains** (12.1, Ch. 2 §12, F1:3995): `(f_ij)` with `f_ij ∈ F(U_i ∩ U_j)`. -/
abbrev CechC1 : Type := (i j : ι) → F.obj (op (U i ⊓ U j))

/-- **2-cochains** (12.1, Ch. 2 §12, F1:3995): `(f_ijk)` with `f_ijk ∈ F(U_i ∩ U_j ∩ U_k)`. -/
abbrev CechC2 : Type := (i j k : ι) → F.obj (op (U i ⊓ U j ⊓ U k))

/-- **The coboundary** `δ : C⁰ → C¹` (12.1, Ch. 2 §12, F1:3995): `(δf)_ij = f_j − f_i` on `U_i ∩ U_j`. -/
def cechD0 : CechC0 F U →ₗ[R] CechC1 F U :=
  LinearMap.pi fun i => LinearMap.pi fun j =>
    cechRes F (inf_le_right : U i ⊓ U j ≤ U j) ∘ₗ LinearMap.proj j -
      cechRes F (inf_le_left : U i ⊓ U j ≤ U i) ∘ₗ LinearMap.proj i

/-- **The coboundary** `δ : C¹ → C²` (12.1, Ch. 2 §12, F1:3995): `(δf)_ijk = f_jk − f_ik + f_ij` on `U_i ∩ U_j ∩ U_k`. -/
def cechD1 : CechC1 F U →ₗ[R] CechC2 F U :=
  LinearMap.pi fun i => LinearMap.pi fun j => LinearMap.pi fun k =>
    cechRes F (le_inf (inf_le_left.trans inf_le_right) inf_le_right : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k) ∘ₗ
        (LinearMap.proj k ∘ₗ LinearMap.proj j) -
      cechRes F (le_inf (inf_le_left.trans inf_le_left) inf_le_right : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k) ∘ₗ
        (LinearMap.proj k ∘ₗ LinearMap.proj i) +
      cechRes F (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) :
        U i ⊓ U j ⊓ U k ≤ U i ⊓ U j) ∘ₗ ((LinearMap.proj j) ∘ₗ LinearMap.proj i)

/-- **Cocycles** `Z¹(𝔘, F) = ker δ` (12.1, Ch. 2 §12, F1:3995). -/
def cechZ1 : Submodule R (CechC1 F U) := LinearMap.ker (cechD1 F U)

/-- **Coboundaries** `B¹(𝔘, F) = δ C⁰` (12.1, Ch. 2 §12, F1:3995). -/
def cechB1 : Submodule R (CechC1 F U) := LinearMap.range (cechD0 F U)

/-- **The group `H¹(𝔘, F) = Z¹/B¹`** (12.2, Ch. 2 §12, F1:4065). -/
abbrev H1Cov : Type := ↥(cechZ1 F U) ⧸ (cechB1 F U).comap (cechZ1 F U).subtype

variable {κ : Type} (V : κ → Opens X)

/-- **Refinement** (12.2, Ch. 2 §12, F1:4065): `𝔙 = (V_k)` is finer than `𝔘 = (U_i)` through `τ : κ → ι` when
`V_k ⊆ U_{τ(k)}`. -/
def IsRefinementMap (τ : κ → ι) : Prop := ∀ k, V k ≤ U (τ k)

/-- **The refinement map** `t : C¹(𝔘) → C¹(𝔙)` (12.2, Ch. 2 §12, F1:4065): `(tξ)_kl = ξ_{τ(k)τ(l)}` restricted to
`V_k ∩ V_l`. -/
def cechRefine (τ : κ → ι) (hτ : IsRefinementMap U V τ) : CechC1 F U →ₗ[R] CechC1 F V :=
  LinearMap.pi fun k => LinearMap.pi fun l =>
    cechRes F (inf_le_inf (hτ k) (hτ l)) ∘ₗ (LinearMap.proj (τ l) ∘ₗ LinearMap.proj (τ k))

/-- **Coverings of `Y`** (12.5, Ch. 2 §12, F1:4153): a family of open sets with union `Y`. -/
structure CechCover (X : Type) [TopologicalSpace X] (Y : Opens X) where
  ι : Type
  U : ι → Opens X
  cover : iSup U = Y

/-- **The direct sum of the 1-cochain groups** over the coverings of `Y` (auxiliary for `H1`). -/
abbrev CechSum (Y : Opens X) := DirectSum (CechCover X Y) fun 𝔘 => CechC1 F 𝔘.U

open scoped Classical in
/-- **The direct sum `⨁ Z¹(𝔘)` of the cocycle groups**, as the submodule of `⨁ C¹(𝔘)` spanned by the summands `lof ξ`,
`ξ ∈ Z¹(𝔘)` (auxiliary for `H1`; a direct sum over the subtypes `Z¹(𝔘)` does not synthesize a quotient instance). -/
def cechZSum (Y : Opens X) : Submodule R (CechSum F Y) :=
  Submodule.span R {z | ∃ (𝔘 : CechCover X Y) (ξ : CechC1 F 𝔘.U), ξ ∈ cechZ1 F 𝔘.U ∧
    z = DirectSum.lof R (CechCover X Y) (fun 𝔘 => CechC1 F 𝔘.U) 𝔘 ξ}

open scoped Classical in
/-- **The relations of the inductive limit** (12.2, 12.5): `lof ξ − lof (tξ)` for a refinement map `t`, and `lof ξ` for
the coboundaries `ξ ∈ B¹(𝔘)`. -/
def cechRel (Y : Opens X) : Submodule R (CechSum F Y) :=
  Submodule.span R ({z | ∃ (𝔘 𝔙 : CechCover X Y) (τ : 𝔙.ι → 𝔘.ι) (hτ : IsRefinementMap 𝔘.U 𝔙.U τ)
        (ξ : CechC1 F 𝔘.U), ξ ∈ cechZ1 F 𝔘.U ∧
          z = DirectSum.lof R (CechCover X Y) (fun 𝔘 => CechC1 F 𝔘.U) 𝔘 ξ -
            DirectSum.lof R (CechCover X Y) (fun 𝔘 => CechC1 F 𝔘.U) 𝔙 (cechRefine F 𝔘.U 𝔙.U τ hτ ξ)} ∪
      {z | ∃ (𝔘 : CechCover X Y) (ξ : CechC1 F 𝔘.U), ξ ∈ cechB1 F 𝔘.U ∧
        z = DirectSum.lof R (CechCover X Y) (fun 𝔘 => CechC1 F 𝔘.U) 𝔘 ξ})

/-- **The cohomology group `H¹(Y, F)`** (12.5, Ch. 2 §12, F1:4153): the inductive limit of the groups `H¹(𝔘, F)` over the
coverings of `Y`, presented as the quotient of `⨁ Z¹(𝔘)` by the relations `lof ξ − lof (tξ)` for a refinement map `t`
and `lof ξ` for the coboundaries `ξ ∈ B¹(𝔘)` (`cechRel`). Since the relations lie in `⨁ Z¹`, this quotient is realised as the image of `⨁ Z¹` in
`⨁ C¹ ⧸ cechRel` (a quotient of the submodule `⨁ Z¹` itself does not synthesize its instances). -/
abbrev H1 (Y : Opens X) : Type 1 := ↥(Submodule.map (cechRel F Y).mkQ (cechZSum F Y))

open scoped Classical in
/-- **The class `[c]`** of a cocycle (12.5, Ch. 2 §12, F1:4153). -/
noncomputable def cechClass {Y : Opens X} (𝔘 : CechCover X Y) : ↥(cechZ1 F 𝔘.U) →ₗ[R] H1 F Y :=
  LinearMap.codRestrict (Submodule.map (cechRel F Y).mkQ (cechZSum F Y))
    ((cechRel F Y).mkQ ∘ₗ DirectSum.lof R (CechCover X Y) (fun 𝔘 => CechC1 F 𝔘.U) 𝔘 ∘ₗ (cechZ1 F 𝔘.U).subtype)
    (fun ξ => Submodule.mem_map_of_mem (Submodule.subset_span ⟨𝔘, ξ, ξ.2, rfl⟩))

/-- **`H⁰(X, F)`** (12.10, Ch. 2 §12, F1:4323): the sections over `X`. -/
abbrev H0 : Type := F.obj (op ⊤)

/-- **Leray coverings** (12.8, Ch. 2 §12, F1:4263): `H¹(U_i, F) = 0` for every `i`. -/
def IsLerayCovering : Prop := ∀ i, Subsingleton (H1 F (U i))

end Cech

section Sheaves

/-- **Global representatives with a pointwise property** (the book's global spaces `𝓔(X)`, … ): the span of the
representatives `a` of the ambient module `A` with `p a x` for every `x ∈ Y`. -/
def repSpan {R : Type} [CommRing R] {X : Type} {A : Type} [AddCommGroup A] [Module R A] (p : A → X → Prop)
    (Y : Set X) : Submodule R A :=
  Submodule.span R {a | ∀ x ∈ Y, p a x}

theorem repSpan_mono {R : Type} [CommRing R] {X : Type} {A : Type} [AddCommGroup A] [Module R A] (p : A → X → Prop)
    {Y Z : Set X} (h : Z ⊆ Y) : repSpan (R := R) p Y ≤ repSpan p Z :=
  Submodule.span_mono fun _ ha x hx => ha x (h hx)

/-- **The generic presheaf of local representatives** (B0.2, option A): the sections over `U` are the representatives `a`
of the ambient module `A` with the pointwise property `p a x` for all `x ∈ U`, modulo those with the pointwise property
`n a x` for all `x ∈ U`; restriction is induced by the inclusion. -/
def localRepPresheaf (R : Type) [CommRing R] {X : Type} [TopologicalSpace X] {A : Type} [AddCommGroup A]
    [Module R A] (p n : A → X → Prop) : TopCat.Presheaf (ModuleCat.{0} R) (TopCat.of X) where
  obj U := ModuleCat.of R (↥(repSpan (R := R) p (U.unop : Set X)) ⧸
    (repSpan (R := R) n (U.unop : Set X)).comap (repSpan (R := R) p (U.unop : Set X)).subtype)
  map {U V} f := ModuleCat.ofHom (Submodule.mapQ _ _
    (Submodule.inclusion (repSpan_mono p (show (V.unop : Set X) ⊆ U.unop from leOfHom f.unop)))
    (fun a ha => repSpan_mono n (show (V.unop : Set X) ⊆ U.unop from leOfHom f.unop) ha))
  map_id U := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_))
    rfl
  map_comp f g := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun a => ?_))
    rfl

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- Differentiable (`C^∞`, real sense) at a point. -/
def IsSmoothFunAt (a : X → ℂ) (x : X) : Prop := ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ a x

/-- Locally constant at a point. -/
def IsLocConstAt {T : Type} (a : X → T) (x : X) : Prop := ∀ᶠ y in 𝓝 x, a y = a x

/-- Vanishing at a point. -/
def VanishesAt {T : Type} [Zero T] (a : X → T) (x : X) : Prop := a x = 0

/-- **The sheaf `ℰ`** as a sheaf of ℂ-modules (9.2, 12.6, Ch. 2 §12, F1:4175): smooth functions. -/
abbrev modE (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  localRepPresheaf ℂ (A := X → ℂ) IsSmoothFunAt VanishesAt

/-- **The sheaf `ℂ`** of locally constant complex functions. -/
abbrev modC (X : Type) [TopologicalSpace X] : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  localRepPresheaf ℂ (A := X → ℂ) IsLocConstAt VanishesAt

/-- **The sheaf `ℤ`** of locally constant integer functions, as a sheaf of `ℤ`-modules. -/
abbrev modZ (X : Type) [TopologicalSpace X] : TopCat.Presheaf (ModuleCat.{0} ℤ) (TopCat.of X) :=
  localRepPresheaf ℤ (A := X → ℤ) IsLocConstAt VanishesAt

/-- The global space `𝓔(Y)` of smooth functions (representatives). -/
def smoothFunOn (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (Y : Set X) : Submodule ℂ (X → ℂ) :=
  repSpan IsSmoothFunAt Y

/-- The global space of locally constant functions with values in `R` (representatives). -/
def locConstOn (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] (Y : Set X) : Submodule R (X → R) :=
  repSpan IsLocConstAt Y

/-- **The local transformation law of `(m, n)` differentials on a set** (junk off the chart targets is zero): the law of
`LiZhongQC.IsDiffFamily` at the points of `Y`. -/
def IsDiffFamilyOn (m n : ℤ) (q : X → ℂ → ℂ) (Y : Set X) : Prop :=
  (∀ x z, z ∉ (chartAt ℂ x).target → q x z = 0) ∧
    ∀ x y : X, ∀ z ∈ (chartAt ℂ y).target, (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source →
      (chartAt ℂ y).symm z ∈ Y →
      q y z = q x (LiZhongQC.chartTransition x y z) * deriv (LiZhongQC.chartTransition x y) z ^ m *
        starRingEnd ℂ (deriv (LiZhongQC.chartTransition x y) z) ^ n

/-- A 1-form on `Y`: the transformation laws of `dz` and `dz̄` at the points of `Y` (`IsForm` is the case `Y = univ`). -/
def Form1.IsFormOn (w : Form1 X) (Y : Set X) : Prop := IsDiffFamilyOn 1 0 w.1 Y ∧ IsDiffFamilyOn 0 1 w.2 Y

/-- A 2-form on `Y`: the transformation law of `dz ∧ dz̄` at the points of `Y`. -/
def Form2.IsFormOn (c : Form2 X) (Y : Set X) : Prop := IsDiffFamilyOn 1 1 c Y

/-- A 1-form of type `(1, 0)` on `Y`. -/
def Form1.IsType10On (w : Form1 X) (Y : Set X) : Prop :=
  ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ Y → w.2 x z = 0

/-- A 1-form of type `(0, 1)` on `Y`. -/
def Form1.IsType01On (w : Form1 X) (Y : Set X) : Prop :=
  ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ Y → w.1 x z = 0

/-- A 1-form vanishing on `Y`. -/
def Form1.VanishOn (w : Form1 X) (Y : Set X) : Prop :=
  ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ Y → w.1 x z = 0 ∧ w.2 x z = 0

/-- A 2-form vanishing on `Y`. -/
def Form2.VanishOn (c : Form2 X) (Y : Set X) : Prop :=
  ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ Y → c x z = 0

/-- The global space `ℰ^(1)(Y)` of differentiable 1-forms (representatives). -/
def smoothForms1On (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (Y : Set X) : Submodule ℂ (Form1 X) :=
  repSpan (fun (w : Form1 X) x => w.IsFormOn {x} ∧ w.IsSmoothOn {x}) Y

/-- The global space `ℰ^{1,0}(Y)` of differentiable 1-forms of type `(1, 0)` (representatives). -/
def smoothForms10On (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (Y : Set X) : Submodule ℂ (Form1 X) :=
  repSpan (fun (w : Form1 X) x => w.IsFormOn {x} ∧ w.IsSmoothOn {x} ∧ w.IsType10On {x}) Y

/-- The global space `ℰ^{0,1}(Y)` of differentiable 1-forms of type `(0, 1)` (representatives). -/
def smoothForms01On (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (Y : Set X) : Submodule ℂ (Form1 X) :=
  repSpan (fun (w : Form1 X) x => w.IsFormOn {x} ∧ w.IsSmoothOn {x} ∧ w.IsType01On {x}) Y

/-- The global space `ℰ^(2)(Y)` of differentiable 2-forms (representatives). -/
def smoothForms2On (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (Y : Set X) : Submodule ℂ (Form2 X) :=
  repSpan (fun (c : Form2 X) x => c.IsFormOn {x} ∧ c.IsSmoothOn {x}) Y

/-- **The sheaf `ℰ^(1)`** of differentiable 1-forms. -/
abbrev modE1 (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  localRepPresheaf ℂ (A := Form1 X) (fun w x => w.IsFormOn {x} ∧ w.IsSmoothOn {x}) (fun w x => w.VanishOn {x})

/-- **The sheaf `ℰ^{1,0}`** of differentiable 1-forms of type `(1, 0)`. -/
abbrev modE10 (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  localRepPresheaf ℂ (A := Form1 X) (fun w x => w.IsFormOn {x} ∧ w.IsSmoothOn {x} ∧ w.IsType10On {x})
    (fun w x => w.VanishOn {x})

/-- **The sheaf `ℰ^{0,1}`** of differentiable 1-forms of type `(0, 1)`. -/
abbrev modE01 (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  localRepPresheaf ℂ (A := Form1 X) (fun w x => w.IsFormOn {x} ∧ w.IsSmoothOn {x} ∧ w.IsType01On {x})
    (fun w x => w.VanishOn {x})

/-- **The sheaf `ℰ^(2)`** of differentiable 2-forms. -/
abbrev modE2 (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  localRepPresheaf ℂ (A := Form2 X) (fun c x => c.IsFormOn {x} ∧ c.IsSmoothOn {x}) (fun c x => c.VanishOn {x})

end Sheaves

section Statements

variable {R : Type} [CommRing R] {X : Type} [TopologicalSpace X] (F : TopCat.Presheaf (ModuleCat.{0} R) (TopCat.of X))

/-- **Lemma 12.3** (Ch. 2 §12, F1:4095). The refinement map `t` takes cocycles to cocycles and coboundaries to
coboundaries, and two refinement maps give cohomologous images of a cocycle. -/
theorem lemma12_3 {ι κ : Type} (U : ι → Opens X) (V : κ → Opens X) (τ τ' : κ → ι) (hτ : IsRefinementMap U V τ)
    (hτ' : IsRefinementMap U V τ') :
    (∀ ξ ∈ cechZ1 F U, cechRefine F U V τ hτ ξ ∈ cechZ1 F V) ∧
      (∀ ξ ∈ cechB1 F U, cechRefine F U V τ hτ ξ ∈ cechB1 F V) ∧
      ∀ ξ ∈ cechZ1 F U, cechRefine F U V τ hτ ξ - cechRefine F U V τ' hτ' ξ ∈ cechB1 F V := by
  sorry

/-- **Lemma 12.4** (Ch. 2 §12, F1:4123). Let `F` be a sheaf, and `𝔙` a refinement of `𝔘`, both coverings of `Y`. Then `t`
induces an injective map `H¹(𝔘, F) → H¹(𝔙, F)`: a cocycle whose refinement is a coboundary is a coboundary. -/
theorem lemma12_4 (hF : F.IsSheaf) {Y : Opens X} (𝔘 𝔙 : CechCover X Y) (τ : 𝔙.ι → 𝔘.ι)
    (hτ : IsRefinementMap 𝔘.U 𝔙.U τ) (ξ : CechC1 F 𝔘.U) (hξ : ξ ∈ cechZ1 F 𝔘.U)
    (h : cechRefine F 𝔘.U 𝔙.U τ hτ ξ ∈ cechB1 F 𝔙.U) : ξ ∈ cechB1 F 𝔘.U := by
  sorry

/-- **Paragraph 12.5(a)** (Ch. 2 §12, F1:4153). For a sheaf `F`, the class of a cocycle vanishes if and only if the cocycle
is a coboundary: `[c] = 0 ↔ c ∈ B¹(𝔘, F)`. -/
theorem para12_5_a (hF : F.IsSheaf) {Y : Opens X} (𝔘 : CechCover X Y) (ξ : ↥(cechZ1 F 𝔘.U)) :
    cechClass F 𝔘 ξ = 0 ↔ (ξ : CechC1 F 𝔘.U) ∈ cechB1 F 𝔘.U := by
  sorry

/-- **Paragraph 12.5(b)** (Ch. 2 §12, F1:4153). For a sheaf `F`, `H¹(X, F) = 0` if and only if `H¹(𝔘, F) = 0` for every
covering `𝔘` of `X`. -/
theorem para12_5_b (hF : F.IsSheaf) :
    Subsingleton (H1 F ⊤) ↔ ∀ 𝔘 : CechCover X ⊤, ∀ ξ ∈ cechZ1 F 𝔘.U, ξ ∈ cechB1 F 𝔘.U := by
  sorry

/-- **Paragraph 12.8** (Leray's theorem, Ch. 2 §12, F1:4263). Let `F` be a sheaf and `𝔘` a Leray covering of `X`. Then
every element of `H¹(X, F)` is of the form `[c]` for a cocycle `c ∈ Z¹(𝔘, F)`, and `[c] = [c′]` if and only if
`c − c′ ∈ B¹(𝔘, F)`; so `H¹(X, F) ≅ H¹(𝔘, F)` canonically. -/
theorem thm12_8 (hF : F.IsSheaf) (𝔘 : CechCover X ⊤) (hL : IsLerayCovering F 𝔘.U) :
    Function.Surjective (cechClass F 𝔘) ∧
      ∀ ξ ξ' : ↥(cechZ1 F 𝔘.U), cechClass F 𝔘 ξ = cechClass F 𝔘 ξ' ↔
        ((ξ : CechC1 F 𝔘.U) - ξ') ∈ cechB1 F 𝔘.U := by
  sorry

variable [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Theorem 12.6** (Ch. 2 §12, F1:4175). On a Riemann surface `X`, `H¹(X, ℰ) = 0`. -/
theorem thm12_6 : Subsingleton (H1 (modE X) ⊤) := by
  sorry

/-- **Remark 12.6(a)** (Ch. 2 §12, F1:4203). `H¹(X, ℰ^(1)) = 0`. -/
theorem rem12_6_a : Subsingleton (H1 (modE1 X) ⊤) := by
  sorry

/-- **Remark 12.6(b)** (Ch. 2 §12, F1:4203). `H¹(X, ℰ^{1,0}) = 0`. -/
theorem rem12_6_b : Subsingleton (H1 (modE10 X) ⊤) := by
  sorry

/-- **Remark 12.6(c)** (Ch. 2 §12, F1:4203). `H¹(X, ℰ^{0,1}) = 0`. -/
theorem rem12_6_c : Subsingleton (H1 (modE01 X) ⊤) := by
  sorry

/-- **Remark 12.6(d)** (Ch. 2 §12, F1:4203). `H¹(X, ℰ^(2)) = 0`. -/
theorem rem12_6_d : Subsingleton (H1 (modE2 X) ⊤) := by
  sorry

/-- **Theorem 12.7(a)** (Ch. 2 §12, F1:4205). For a simply connected Riemann surface, `H¹(X, ℂ) = 0`. -/
theorem thm12_7_a [SimplyConnectedSpace X] : Subsingleton (H1 (modC X) ⊤) := by
  sorry

/-- **Theorem 12.7(b)** (Ch. 2 §12, F1:4205). For a simply connected Riemann surface, `H¹(X, ℤ) = 0`. -/
theorem thm12_7_b [SimplyConnectedSpace X] : Subsingleton (H1 (modZ X) ⊤) := by
  sorry

end Statements

end Forster1981
