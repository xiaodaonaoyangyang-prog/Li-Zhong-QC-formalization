import References.Forster1981.Ch01.S08_AlgebraicFunctions

/-!
# Forster, Chapter 1 §9: Differential forms

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §9 (`full.md` F1:2333–2750).

Conventions: "differentiable" is `C^∞` in the real sense (`ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞`, read in the preferred charts);
`∂/∂z`, `∂/∂z̄` are `LiZhongQC.dz`, `LiZhongQC.dzbar` (Forster's normalization `½(∂/∂x ∓ i ∂/∂y)`). Forms use the
coefficient model of `LiZhongQC.IsDiffFamily`: a 1-form is a pair `(c10, c01)` of families `X → ℂ → ℂ` (the coefficients
of `dz` and `dz̄` in the preferred chart at each point, extended by `0` off the chart target), a 2-form a family (the
coefficient of `dz ∧ dz̄`). They are ℂ-modules (products of function spaces); that a pair is a well defined form, i.e. satisfies
the transformation law of `IsDiffFamily`, is the predicate `Form1.IsForm`/`Form2.IsForm`, assumed in the statements
(junk values of the operations outside this domain are never read). The cotangent spaces and the differentials `d_a f`
are the faithful constructions of 9.2–9.5, 9.11. Forms on an open set `Y` are read through the set argument of the
predicates; the sheaves of forms (`ℰ^(1)`, `ℰ^{1,0}`, `ℰ^{0,1}`, `Ω`, `𝓜^(1)`, `ℰ^(2)`) are module-valued presheaves
built in Part B by the generic `localRepPresheaf` from these ambient spaces of forms.

* Definition (smooth functions 𝓔(U), `∂/∂z`, `∂/∂z̄`, §9.1, F1:2337) — exists: `ContDiffOn`, `LiZhongQC.dz`,
  `LiZhongQC.dzbar`
* Paragraph 9.2 (the sheaf ℰ, the ideals 𝔪_a, 𝔪_a², F1:2345) — `sheafE`, `maxIdealGerms`, `secondOrderGerms`
* Definition 9.3 (the cotangent space and the differential `d_a f`, F1:2365) — `cotangentSpace`, `diffAt`
* Theorem 9.4 (F1:2379) — `thm9_4_a`, `thm9_4_b`
* Paragraph 9.5 (cotangent vectors of type (1,0), (0,1), F1:2421) — `cotangent10`, `cotangent01`, `para9_5`
* Definition 9.6 (1-forms, types (1,0), (0,1), F1:2455) — `Form1`, `Form1.IsForm`, `Form1.IsType10`, `Form1.IsType01`
* Examples 9.7 (`df`, `d′f`, `d″f`, `fω`, F1:2463) — `dForm`, `dFormHol`, `dFormBar`, `Form1.smulFun`
* Definition 9.8 (differentiable and holomorphic 1-forms, F1:2483) — `Form1.IsSmoothOn`, `Form1.IsHolomorphicOn`
* Paragraph 9.9 (the residue, F1:2497) — `HasResidueAt`, `HasResidue`, `Form1.orderAt`
* Lemma 9.9 (the residue is independent of the chart, F1:2513) — `lemma9_9`
* Paragraph 9.10 (meromorphic 1-forms, abelian differentials, F1:2561) — `Form1.IsMeromorphicOn`, `IsAbelianDiff1`,
  `IsAbelianDiff2`, `IsAbelianDiff3`
* Paragraph 9.11 (the exterior product, F1:2571) — `cotangentSpace2`, `para9_11`
* Definition 9.12 (2-forms, `ω₁ ∧ ω₂`, F1:2587) — `Form2`, `Form2.IsForm`, `Form2.IsSmoothOn`, `Form1.wedge`,
  `Form2.smulFun`, `Form1.EqOn`, `Form2.EqOn`
* Paragraph 9.13 (exterior differentiation `d`, `d′`, `d″`, F1:2609) — `Form1.d`, `Form1.dHol`, `Form1.dBar`
* Paragraph 9.14 (elementary properties, harmonic functions, F1:2649) — `para9_14_i`, `para9_14_ii`, `para9_14_iii`,
  `para9_14_iv`, `IsHarmonicOn`
* Definition 9.15 (closed and exact 1-forms, F1:2675) — `Form1.IsClosed`, `Form1.IsExact`
* Theorem 9.16 (F1:2679) — `thm9_16_a`, `thm9_16_b`
* Paragraph 9.17 (the pull-back of differential forms, F1:2695) — `localDeriv`, `Form1.pullback`, `Form2.pullback`, `para9_17`

Omitted (U−): the sheaves of forms (module-valued, Part B), uniqueness of `f̃` and chart independence in 9.2, the remark
after 9.7, the independence of the representation `Σ f_k dg_k` in 9.13, the consequence after 9.16 (F1:2693), the
consequence after 9.17.
-/

open scoped Manifold ContDiff Topology
open Set Filter

namespace Forster1981

open scoped Forster1981

section Smooth

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **The sheaf `ℰ` of differentiable functions** (9.2, Ch. 1 §9, F1:2347): sections over `U` are the functions `U → ℂ`
which are `C^∞` (in the real sense) at every point. -/
noncomputable def sheafE : TopCat.Sheaf (Type) (TopCat.of X) :=
  TopCat.subsheafToTypes (pointwiseLocalPredicate (X := X) (T := ℂ) 0
    (fun x g => ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ g x)
    (fun _ _ _ h => ⟨fun hg => hg.congr_of_eventuallyEq h.symm, fun hg => hg.congr_of_eventuallyEq h⟩))

/-- **The ideal `𝔪_a`** (9.2, Ch. 1 §9, F1:2357): the germs at `a` of differentiable functions which vanish at `a`
(as a ℂ-span of such germs; the set of germs is already a ℂ-space). -/
def maxIdealGerms (a : X) : Submodule ℂ ((𝓝 a).Germ ℂ) :=
  Submodule.span ℂ {g | ∃ f : X → ℂ, (f : (𝓝 a).Germ ℂ) = g ∧ ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f a ∧ f a = 0}

/-- **The space `𝔪_a²`** (9.2, Ch. 1 §9, F1:2357): the germs of differentiable functions which vanish to second order at
`a`: value `0` at `a` and (real) derivative `0` at `a` of the local expression in the preferred chart. -/
def secondOrderGerms (a : X) : Submodule ℂ ((𝓝 a).Germ ℂ) :=
  Submodule.span ℂ {g | ∃ f : X → ℂ, (f : (𝓝 a).Germ ℂ) = g ∧ ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f a ∧ f a = 0 ∧
    HasFDerivAt (f ∘ (chartAt ℂ a).symm) (0 : ℂ →L[ℝ] ℂ) (chartAt ℂ a a)}

/-- **The cotangent space** `T_a^(1) = 𝔪_a / 𝔪_a²` (Definition 9.3, Ch. 1 §9, F1:2365). -/
abbrev cotangentSpace (a : X) : Type :=
  ↥(maxIdealGerms a) ⧸ (secondOrderGerms a).comap (maxIdealGerms a).subtype

/-- **The differential** `d_a f ∈ T_a^(1)` of a function `f` differentiable at `a` (Definition 9.3, Ch. 1 §9, F1:2365): the
class of the germ of `f − f(a)`. -/
def diffAt (f : X → ℂ) {a : X} (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f a) : cotangentSpace a :=
  Submodule.Quotient.mk ⟨((fun y => f y - f a : X → ℂ) : (𝓝 a).Germ ℂ),
    Submodule.subset_span ⟨fun y => f y - f a, rfl, hf.sub contMDiffAt_const, sub_self _⟩⟩

/-- **The subspace `T_a^{1,0}`** of cotangent vectors of type `(1, 0)` (9.5, Ch. 1 §9, F1:2421): spanned by the differentials
`d_a f` of functions `f` holomorphic at `a` (equivalently, by `d_a z` for a local coordinate `z`). -/
def cotangent10 (a : X) : Submodule ℂ (cotangentSpace a) :=
  Submodule.span ℂ {v | ∃ (f : X → ℂ) (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f a),
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f a ∧ v = diffAt f hf}

/-- **The subspace `T_a^{0,1}`** of cotangent vectors of type `(0, 1)` (9.5, Ch. 1 §9, F1:2421): spanned by the
differentials `d_a f` of functions `f` antiholomorphic at `a` (equivalently, by `d_a z̄`). -/
def cotangent01 (a : X) : Submodule ℂ (cotangentSpace a) :=
  Submodule.span ℂ {v | ∃ (f : X → ℂ) (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f a),
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun y => starRingEnd ℂ (f y)) a ∧ v = diffAt f hf}

/-- **The space `T_a^(2) = Λ² T_a^(1)`** (9.11, Ch. 1 §9, F1:2579). -/
abbrev cotangentSpace2 (a : X) : Type := ↥(ExteriorAlgebra.exteriorPower ℂ 2 (cotangentSpace a))

end Smooth

section Forms

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **1-forms** (Definition 9.6, Ch. 1 §9, F1:2455): the pair `(c10, c01)` of coefficient families of `dz` and `dz̄` in the
preferred chart at every point (the model of `LiZhongQC.IsDiffFamily`). Whether the pair is a well defined form is
`Form1.IsForm`. -/
abbrev Form1 (X : Type) : Type := (X → ℂ → ℂ) × (X → ℂ → ℂ)

/-- **2-forms** (Definition 9.12, Ch. 1 §9, F1:2587): the coefficient family of `dz ∧ dz̄` in the preferred chart at every
point. -/
abbrev Form2 (X : Type) : Type := X → ℂ → ℂ

/-- A pair of families is a well defined 1-form: the transformation laws of `dz` (type `(1, 0)`) and `dz̄` (type `(0, 1)`)
hold. -/
def Form1.IsForm (w : Form1 X) : Prop :=
  LiZhongQC.IsDiffFamily 1 0 w.1 ∧ LiZhongQC.IsDiffFamily 0 1 w.2

/-- **Type `(1, 0)`** (Definition 9.6, Ch. 1 §9, F1:2455): no `dz̄` part. -/
def Form1.IsType10 (w : Form1 X) : Prop := w.2 = 0

/-- **Type `(0, 1)`** (Definition 9.6, Ch. 1 §9, F1:2455): no `dz` part. -/
def Form1.IsType01 (w : Form1 X) : Prop := w.1 = 0

/-- A family of coefficients is a well defined 2-form: the transformation law of `dz ∧ dz̄`. -/
def Form2.IsForm (c : Form2 X) : Prop := LiZhongQC.IsDiffFamily 1 1 c

/-- **The differential `df`** (Examples 9.7, Ch. 1 §9, F1:2463): `df = f_z dz + f_z̄ dz̄` in the preferred chart at each
point (coefficients extended by `0` off the chart target). -/
noncomputable def dForm (f : X → ℂ) : Form1 X :=
  (fun x => (chartAt ℂ x).target.indicator (LiZhongQC.dz (f ∘ (chartAt ℂ x).symm)),
   fun x => (chartAt ℂ x).target.indicator (LiZhongQC.dzbar (f ∘ (chartAt ℂ x).symm)))

/-- **The form `d′f`** (Examples 9.7, Ch. 1 §9, F1:2463): `d′f = f_z dz`. -/
noncomputable def dFormHol (f : X → ℂ) : Form1 X := ((dForm f).1, 0)

/-- **The form `d″f`** (Examples 9.7, Ch. 1 §9, F1:2463): `d″f = f_z̄ dz̄`. -/
noncomputable def dFormBar (f : X → ℂ) : Form1 X := (0, (dForm f).2)

/-- **The form `fω`** (Examples 9.7, Ch. 1 §9, F1:2463). -/
noncomputable def Form1.smulFun (g : X → ℂ) (w : Form1 X) : Form1 X :=
  (fun x z => g ((chartAt ℂ x).symm z) * w.1 x z, fun x z => g ((chartAt ℂ x).symm z) * w.2 x z)

/-- **Differentiable 1-forms on `Y`** (Definition 9.8, Ch. 1 §9, F1:2483): the coefficients are `C^∞` (in the real sense)
at every point of the chart image of `Y`. -/
def Form1.IsSmoothOn (w : Form1 X) (Y : Set X) : Prop :=
  ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ Y →
    ContDiffAt ℝ ∞ (w.1 x) z ∧ ContDiffAt ℝ ∞ (w.2 x) z

/-- **Holomorphic 1-forms on `Y`** (Definition 9.8, Ch. 1 §9, F1:2483): of type `(1, 0)` with holomorphic coefficient. -/
def Form1.IsHolomorphicOn (w : Form1 X) (Y : Set X) : Prop :=
  w.IsType10 ∧ ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ Y → DifferentiableAt ℂ (w.1 x) z

/-- **The residue `r` of `w` at `a`, read in the chart at `x`** (9.9, Ch. 1 §9, F1:2497): the integral of the coefficient
of `dz` over small circles around `a` in the chart at `x`, divided by `2πi`, is `r`. -/
def HasResidueAt (w : Form1 X) (x a : X) (r : ℂ) : Prop :=
  ∃ ε > 0, ∀ ρ ∈ Ioo 0 ε,
    (2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(chartAt ℂ x a, ρ), w.1 x z) = r

/-- **The residue `r` of `w` at `a`** (9.9, Ch. 1 §9, F1:2497), in the preferred chart at `a`. -/
def HasResidue (w : Form1 X) (a : X) (r : ℂ) : Prop := HasResidueAt w a a r

/-- **The order of `w` at `a`** (9.9, Ch. 1 §9, F1:2497): the order of the coefficient of `dz` in the preferred chart at
`a` (`> 0`: zero, `< 0`: pole, `0` with nonvanishing coefficient: regular; `⊤`: vanishing near `a`). -/
noncomputable def Form1.orderAt (w : Form1 X) (a : X) : WithTop ℤ := meromorphicOrderAt (w.1 a) (chartAt ℂ a a)

/-- **Meromorphic 1-forms on `Y`** (Paragraph 9.10, Ch. 1 §9, F1:2561): of type `(1, 0)` with meromorphic coefficient. -/
def Form1.IsMeromorphicOn (w : Form1 X) (Y : Set X) : Prop :=
  w.IsType10 ∧ ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ Y → MeromorphicAt (w.1 x) z

/-- **Abelian differentials of the first kind** (Paragraph 9.10, Ch. 1 §9, F1:2565): the holomorphic 1-forms on `X`. -/
def IsAbelianDiff1 (w : Form1 X) : Prop := w.IsForm ∧ w.IsHolomorphicOn univ

/-- **Abelian differentials of the second kind** (Paragraph 9.10, Ch. 1 §9, F1:2565): meromorphic 1-forms on `X` all of
whose residues vanish. -/
def IsAbelianDiff2 (w : Form1 X) : Prop :=
  w.IsForm ∧ w.IsMeromorphicOn univ ∧ ∀ a r, HasResidue w a r → r = 0

/-- **Abelian differentials of the third kind** (Paragraph 9.10, Ch. 1 §9, F1:2565): the meromorphic 1-forms on `X`. -/
def IsAbelianDiff3 (w : Form1 X) : Prop := w.IsForm ∧ w.IsMeromorphicOn univ

/-- **Differentiable 2-forms on `Y`** (Definition 9.12, Ch. 1 §9, F1:2587). -/
def Form2.IsSmoothOn (c : Form2 X) (Y : Set X) : Prop :=
  ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ Y → ContDiffAt ℝ ∞ (c x) z

/-- **The form `fc`** for a 2-form `c` (Definition 9.12, Ch. 1 §9, F1:2587). -/
noncomputable def Form2.smulFun (g : X → ℂ) (c : Form2 X) : Form2 X := fun x z => g ((chartAt ℂ x).symm z) * c x z

/-- **The exterior product** `w₁ ∧ w₂` of 1-forms (Definition 9.12, Ch. 1 §9, F1:2587):
`(a₁ dz + b₁ dz̄) ∧ (a₂ dz + b₂ dz̄) = (a₁ b₂ − b₁ a₂) dz ∧ dz̄`. -/
noncomputable def Form1.wedge (w₁ w₂ : Form1 X) : Form2 X := fun x z => w₁.1 x z * w₂.2 x z - w₁.2 x z * w₂.1 x z

/-- **Equality of 1-forms on `Y`** (read in the preferred charts, junk off the charts ignored). -/
def Form1.EqOn (w₁ w₂ : Form1 X) (Y : Set X) : Prop :=
  ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ Y → w₁.1 x z = w₂.1 x z ∧ w₁.2 x z = w₂.2 x z

/-- **Equality of 2-forms on `Y`** (read in the preferred charts, junk off the charts ignored). -/
def Form2.EqOn (c₁ c₂ : Form2 X) (Y : Set X) : Prop :=
  ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ Y → c₁ x z = c₂ x z

/-- **The exterior derivative `dω`** of a 1-form (Paragraph 9.13, Ch. 1 §9, F1:2609): for `ω = a dz + b dz̄`,
`dω = da ∧ dz + db ∧ dz̄ = (b_z − a_z̄) dz ∧ dz̄`. -/
noncomputable def Form1.d (w : Form1 X) : Form2 X :=
  fun x => (chartAt ℂ x).target.indicator (fun z => LiZhongQC.dz (w.2 x) z - LiZhongQC.dzbar (w.1 x) z)

/-- **The operator `d′`** (Paragraph 9.13, Ch. 1 §9, F1:2609): `d′ω = d′a ∧ dz + d′b ∧ dz̄ = b_z dz ∧ dz̄`. -/
noncomputable def Form1.dHol (w : Form1 X) : Form2 X :=
  fun x => (chartAt ℂ x).target.indicator (LiZhongQC.dz (w.2 x))

/-- **The operator `d″`** (Paragraph 9.13, Ch. 1 §9, F1:2609): `d″ω = d″a ∧ dz + d″b ∧ dz̄ = −a_z̄ dz ∧ dz̄`. -/
noncomputable def Form1.dBar (w : Form1 X) : Form2 X :=
  fun x => (chartAt ℂ x).target.indicator (fun z => - LiZhongQC.dzbar (w.1 x) z)

/-- **Harmonic functions on `Y`** (Paragraph 9.14, Ch. 1 §9, F1:2667): differentiable `f` with `d′d″f = 0`. -/
def IsHarmonicOn (f : X → ℂ) (Y : Set X) : Prop :=
  (∀ x ∈ Y, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f x) ∧ Form2.EqOn (Form1.dHol (dFormBar f)) 0 Y

/-- **Closed 1-forms on `Y`** (Definition 9.15, Ch. 1 §9, F1:2675): differentiable with `dω = 0`. -/
def Form1.IsClosed (w : Form1 X) (Y : Set X) : Prop := w.IsSmoothOn Y ∧ Form2.EqOn w.d 0 Y

/-- **Exact 1-forms on `Y`** (Definition 9.15, Ch. 1 §9, F1:2675): `ω = df` for a differentiable `f`. -/
def Form1.IsExact (w : Form1 X) (Y : Set X) : Prop :=
  ∃ f : X → ℂ, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f Y ∧ Form1.EqOn w (dForm f) Y

section Pullback

variable {Z : Type} [TopologicalSpace Z] [ChartedSpace ℂ Z]

/-- The derivative at `z` of the local expression of `F` from the preferred chart at `x` to the preferred chart at the
image point (the holomorphic derivative `F′`). -/
noncomputable def localDeriv (F : X → Z) (x : X) (z : ℂ) : ℂ :=
  deriv (fun u => chartAt ℂ (F ((chartAt ℂ x).symm z)) (F ((chartAt ℂ x).symm u))) z

/-- **The pull-back of a 1-form** under a holomorphic map `F` (Paragraph 9.17, Ch. 1 §9, F1:2695):
`F^*(a dz + b dz̄) = (a ∘ F) F′ dz + (b ∘ F) conj(F′) dz̄`. -/
noncomputable def Form1.pullback (F : X → Z) (w : Form1 Z) : Form1 X :=
  (fun x => (chartAt ℂ x).target.indicator (fun z =>
    w.1 (F ((chartAt ℂ x).symm z)) (chartAt ℂ (F ((chartAt ℂ x).symm z)) (F ((chartAt ℂ x).symm z))) *
      localDeriv F x z),
   fun x => (chartAt ℂ x).target.indicator (fun z =>
    w.2 (F ((chartAt ℂ x).symm z)) (chartAt ℂ (F ((chartAt ℂ x).symm z)) (F ((chartAt ℂ x).symm z))) *
      starRingEnd ℂ (localDeriv F x z)))

/-- **The pull-back of a 2-form** under a holomorphic map `F` (Paragraph 9.17, Ch. 1 §9, F1:2695):
`F^*(c dz ∧ dz̄) = (c ∘ F) |F′|² dz ∧ dz̄`. -/
noncomputable def Form2.pullback (F : X → Z) (c : Form2 Z) : Form2 X :=
  fun x => (chartAt ℂ x).target.indicator (fun z =>
    c (F ((chartAt ℂ x).symm z)) (chartAt ℂ (F ((chartAt ℂ x).symm z)) (F ((chartAt ℂ x).symm z))) *
      (localDeriv F x z * starRingEnd ℂ (localDeriv F x z)))

end Pullback

end Forms

section Statements

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Theorem 9.4(a)** (Ch. 1 §9, F1:2379). In a coordinate neighbourhood `(U, z = x + iy)` of `a`, `d_a x, d_a y` is a
basis of `T_a^(1)` and `d_a f = f_x(a) d_a x + f_y(a) d_a y`.
Modelling: chart `e` of the maximal atlas, `x = Re e`, `y = Im e` (differentiability of the coordinates is a hypothesis
automatically satisfied), `f_x(a)`, `f_y(a)` the real derivatives of `f ∘ e⁻¹` at `e a` in the directions `1`, `i`. -/
theorem thm9_4_a {e : OpenPartialHomeomorph X ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) {a : X}
    (ha : a ∈ e.source)
    (hx : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun p => ((e p).re : ℂ)) a)
    (hy : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun p => ((e p).im : ℂ)) a) :
    LinearIndependent ℂ ![diffAt _ hx, diffAt _ hy] ∧
      Submodule.span ℂ (Set.range ![diffAt _ hx, diffAt _ hy]) = ⊤ ∧
      ∀ (f : X → ℂ) (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f a),
        diffAt f hf = fderiv ℝ (f ∘ e.symm) (e a) 1 • diffAt _ hx +
          fderiv ℝ (f ∘ e.symm) (e a) Complex.I • diffAt _ hy := by
  sorry

/-- **Theorem 9.4(b)** (Ch. 1 §9, F1:2379). `d_a z, d_a z̄` is a basis of `T_a^(1)` and
`d_a f = f_z(a) d_a z + f_z̄(a) d_a z̄`.
Modelling: as 9.4(a), with `z = e`, `z̄ = conj ∘ e` and `f_z`, `f_z̄` given by `LiZhongQC.dz`, `LiZhongQC.dzbar`. -/
theorem thm9_4_b {e : OpenPartialHomeomorph X ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X) {a : X}
    (ha : a ∈ e.source)
    (hz : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun p => e p) a)
    (hzb : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun p => starRingEnd ℂ (e p)) a) :
    LinearIndependent ℂ ![diffAt _ hz, diffAt _ hzb] ∧
      Submodule.span ℂ (Set.range ![diffAt _ hz, diffAt _ hzb]) = ⊤ ∧
      ∀ (f : X → ℂ) (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f a),
        diffAt f hf = LiZhongQC.dz (f ∘ e.symm) (e a) • diffAt _ hz +
          LiZhongQC.dzbar (f ∘ e.symm) (e a) • diffAt _ hzb := by
  sorry

/-- **Paragraph 9.5** (Ch. 1 §9, F1:2421). `T_a^(1) = T_a^{1,0} ⊕ T_a^{0,1}` with both summands one dimensional
(`d_a f = d′_a f + d″_a f`).
Modelling: the decomposition `d′_a f + d″_a f` is the unique decomposition along the complementary pair
`cotangent10`, `cotangent01`; `diffAt′`, `diffAt″` are not introduced. -/
theorem para9_5 (a : X) :
    IsCompl (cotangent10 a) (cotangent01 a) ∧ Module.finrank ℂ (cotangent10 a) = 1 ∧
      Module.finrank ℂ (cotangent01 a) = 1 := by
  sorry

/-- **Lemma 9.9** (Ch. 1 §9, F1:2513). The residue of a 1-form `w` which is holomorphic on a punctured neighbourhood of
`a` does not depend on the chart: for every `x` whose chart contains `a`, `r` is the residue in the chart at `x` iff it
is the residue in the preferred chart at `a`. -/
theorem lemma9_9 {w : Form1 X} (hw : w.IsForm) {a x : X} (ha : a ∈ (chartAt ℂ x).source)
    (hhol : ∃ U ∈ 𝓝 a, w.IsHolomorphicOn (U \ {a})) (r : ℂ) :
    HasResidueAt w x a r ↔ HasResidue w a r := by
  sorry

/-- **Paragraph 9.11** (Ch. 1 §9, F1:2571). `T_a^(2) = Λ² T_a^(1)` is one dimensional with basis `d_a x ∧ d_a y`, and
`d_a z ∧ d_a z̄ = −2i d_a x ∧ d_a y` for the preferred chart `z = x + iy` at `a`.
Modelling: wedge products in the exterior algebra of `T_a^(1)`; the differentiability of the coordinates is a
hypothesis automatically satisfied. -/
theorem para9_11 (a : X)
    (hz : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun p => chartAt ℂ a p) a)
    (hzb : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun p => starRingEnd ℂ (chartAt ℂ a p)) a)
    (hx : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun p => (((chartAt ℂ a p).re : ℝ) : ℂ)) a)
    (hy : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun p => (((chartAt ℂ a p).im : ℝ) : ℂ)) a) :
    Module.finrank ℂ (cotangentSpace2 a) = 1 ∧
      ExteriorAlgebra.ι ℂ (diffAt _ hx) * ExteriorAlgebra.ι ℂ (diffAt _ hy) ≠ 0 ∧
      ExteriorAlgebra.ι ℂ (diffAt _ hz) * ExteriorAlgebra.ι ℂ (diffAt _ hzb) =
        (-2 * Complex.I) • (ExteriorAlgebra.ι ℂ (diffAt _ hx) * ExteriorAlgebra.ι ℂ (diffAt _ hy)) := by
  sorry

/-- **Paragraph 9.14(i)** (Ch. 1 §9, F1:2649). For a differentiable `f` on an open `Y`: `ddf = d′d′f = d″d″f = 0`.
Modelling: `d(df)` is `Form1.d (dForm f)`; equality of 2-forms on `Y` (`Form2.EqOn`). -/
theorem para9_14_i {Y : Set X} (hY : IsOpen Y) {f : X → ℂ} (hf : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f Y) :
    Form2.EqOn (Form1.d (dForm f)) 0 Y ∧ Form2.EqOn (Form1.dHol (dFormHol f)) 0 Y ∧
      Form2.EqOn (Form1.dBar (dFormBar f)) 0 Y := by
  sorry

/-- **Paragraph 9.14(ii)** (Ch. 1 §9, F1:2649). For a differentiable 1-form `ω` on an open `Y`: `dω = d′ω + d″ω`. -/
theorem para9_14_ii {Y : Set X} (hY : IsOpen Y) {w : Form1 X} (hw : w.IsSmoothOn Y) :
    Form2.EqOn (Form1.d w) (Form1.dHol w + Form1.dBar w) Y := by
  sorry

/-- **Paragraph 9.14(iii)** (Ch. 1 §9, F1:2649). `d(fω) = df ∧ ω + f dω`, and similarly for `d′` and `d″`
(`d′(fω) = d′f ∧ ω + f d′ω`, `d″(fω) = d″f ∧ ω + f d″ω`). -/
theorem para9_14_iii {Y : Set X} (hY : IsOpen Y) {f : X → ℂ} (hf : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f Y)
    {w : Form1 X} (hw : w.IsSmoothOn Y) :
    Form2.EqOn (Form1.d (w.smulFun f)) (Form1.wedge (dForm f) w + Form2.smulFun f (Form1.d w)) Y ∧
      Form2.EqOn (Form1.dHol (w.smulFun f)) (Form1.wedge (dFormHol f) w + Form2.smulFun f (Form1.dHol w)) Y ∧
      Form2.EqOn (Form1.dBar (w.smulFun f)) (Form1.wedge (dFormBar f) w + Form2.smulFun f (Form1.dBar w)) Y := by
  sorry

/-- **Paragraph 9.14(iv)** (Ch. 1 §9, F1:2649). `d′d″f = −d″d′f`, and in a chart `z = x + iy`,
`d′d″f = f_{zz̄} dz ∧ dz̄ = (1/2i)(f_xx + f_yy) dx ∧ dy`, i.e. `f_{zz̄} = ¼(f_xx + f_yy)` (`dz ∧ dz̄ = −2i dx ∧ dy`).
Modelling: the second formula is stated for the coefficient of `dz ∧ dz̄` in the preferred chart at `x`. -/
theorem para9_14_iv {Y : Set X} (hY : IsOpen Y) {f : X → ℂ} (hf : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f Y) :
    Form2.EqOn (Form1.dHol (dFormBar f)) (-(Form1.dBar (dFormHol f))) Y ∧
      ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ Y →
        Form1.dHol (dFormBar f) x z =
          (fderiv ℝ (fun u => fderiv ℝ (f ∘ (chartAt ℂ x).symm) u 1) z 1 +
            fderiv ℝ (fun u => fderiv ℝ (f ∘ (chartAt ℂ x).symm) u Complex.I) z Complex.I) / 4 := by
  sorry

/-- **Theorem 9.16(a)** (Ch. 1 §9, F1:2679). Every holomorphic 1-form on an open `Y` is closed. -/
theorem thm9_16_a {Y : Set X} (hY : IsOpen Y) {w : Form1 X} (hw : w.IsForm) (hh : w.IsHolomorphicOn Y) :
    w.IsClosed Y := by
  sorry

/-- **Theorem 9.16(b)** (Ch. 1 §9, F1:2679). Every closed form `ω ∈ ℰ^{1,0}(Y)` on an open `Y` is holomorphic. -/
theorem thm9_16_b {Y : Set X} (hY : IsOpen Y) {w : Form1 X} (hw : w.IsForm) (h10 : w.IsType10)
    (hc : w.IsClosed Y) : w.IsHolomorphicOn Y := by
  sorry

/-- **Paragraph 9.17** (Ch. 1 §9, F1:2695). For a holomorphic map `F : X → Z` of Riemann surfaces, a differentiable
function `f` and a differentiable 1-form `ω` on `Z`: `F^*(df) = d(F^*f)` and `F^*(dω) = d(F^*ω)`, and the same for
`d′`, `d″` (`F^*f = f ∘ F`).
Modelling: equality on `X` of the forms read in the preferred charts.
[CORRECTION, Forster-fix1] `ω` is a 1-form (`hwf : w.IsForm`): `Form1.pullback` reads `ω` at chart centres, so for a
non-form family of coefficients `d(F^*ω) ≠ F^*(dω)` (`F = id` on `ℂ`, `ω = conj y dz` read at `y`: `−1` vs `0`;
AUDIT5_Forster G3). -/
theorem para9_17 {Z : Type} [TopologicalSpace Z] [T2Space Z] [ConnectedSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) ω Z] {F : X → Z} (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) {f : Z → ℂ}
    (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f) {w : Form1 Z} (hwf : w.IsForm) (hw : w.IsSmoothOn univ) :
    Form1.EqOn (Form1.pullback F (dForm f)) (dForm (f ∘ F)) univ ∧
      Form1.EqOn (Form1.pullback F (dFormHol f)) (dFormHol (f ∘ F)) univ ∧
      Form1.EqOn (Form1.pullback F (dFormBar f)) (dFormBar (f ∘ F)) univ ∧
      Form2.EqOn (Form1.d (Form1.pullback F w)) (Form2.pullback F (Form1.d w)) univ ∧
      Form2.EqOn (Form1.dHol (Form1.pullback F w)) (Form2.pullback F (Form1.dHol w)) univ ∧
      Form2.EqOn (Form1.dBar (Form1.pullback F w)) (Form2.pullback F (Form1.dBar w)) univ := by
  sorry

end Statements

end Forster1981
