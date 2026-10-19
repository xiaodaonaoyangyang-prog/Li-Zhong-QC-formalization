import References.Forster1981.Ch02.S16_TheRiemannRochTheorem

/-!
# Forster, Chapter 2 §17: The Serre duality theorem

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §17 (`full.md` F1:5850–6579).

Conventions (rulings B0.3, B0.7): the linear form `Res : H¹(X, Ω) → ℂ` is the relation `IsResH1 Res` (the book's
definition through the Dolbeault isomorphism of 15.14, unravelled as in the proof of 17.3: a cocycle `ξ` of `Ω` becomes
`δσ` in `ℰ^{1,0}` and `Res [ξ] = (1/2πi) ∬ τ` for the global 2-form `τ` with `τ|U_i = dσ_i`); the Serre pairing `ι_D` is
the relation `IsSerreDuality Res D ι`; products of forms by classes are the relation `IsFormTimesClass`. The sheaves
`𝓜` and `𝓜^(1)` of meromorphic functions and 1-forms and `Ω_D` are built with `localRepPresheaf`; `ℙ^N` is Mathlib's
`Projectivization ℂ (Fin n → ℂ)` (`n = N + 1`), whose charts `φ_j` are given by `rep` and "holomorphic into `ℙ^N`" is
chartwise, as in the book (`ℙ^N` carries no topology here, so openness of `F⁻¹ U_j` is part of the definition). The branching
order is `b(f, x) = v(f, x) − 1`; Riemann–Hurwitz is stated in `ℚ`. "Globally generated" is Forster's equivalent `ord` form.
Reading: in 17.7 the hypothesis `ω ∈ H⁰(X, Ω_{−D})` is `ω ∈ H⁰(X, Ω_{−D′})` [misprint].

* Paragraph 17.1 (the linear form `Res`, F1:5854) — `IsResH1`, `para17_1`
* Paragraph 17.2 (Mittag–Leffler distributions of forms, F1:5868) — `modM1`, `IsMLDistribution1`, `IsMLClass1`,
  `HasMLResidue1`
* Theorem 17.3 (F1:5886) — `thm17_3`
* Paragraph 17.4 (the sheaves `Ω_D`, F1:5954) — `modOmegaD`, `para17_4`, `lemma17_4`
* Paragraph 17.5 (the dual pairing, F1:5976) — `IsFormTimesClass`, `IsSerreDuality`, `para17_5`
* Theorem 17.6 (F1:6002) — `thm17_6`
* Lemma 17.7 (F1:6038) — `lemma17_7`
* Lemma 17.8 (F1:6102) — `lemma17_8`
* Theorem 17.9 (Serre duality, F1:6124) — `thm17_9`
* Remark 17.10 (F1:6172) — `rem17_10_a`, `rem17_10_b`
* Theorem 17.11 (F1:6194) — `thm17_11`, `thm17_11_cons`
* Theorem 17.12 (F1:6210) — `thm17_12`
* Corollary 17.13 (F1:6230) — `cor17_13`
* Paragraph 17.14 (the Riemann–Hurwitz formula, F1:6234) — `branchingOrder`, `totalBranchingOrder`, `thm17_14`
* Paragraph 17.15 (hyperelliptic surfaces, F1:6292) — `IsHyperelliptic`
* Theorem 17.16 (F1:6314) — `thm17_16`
* Corollary 17.17 (F1:6322) — `modM`, `cor17_17`
* Paragraph 17.18 (globally generated sheaves, F1:6340) — `IsGloballyGenerated`
* Theorem 17.19 (F1:6352) — `thm17_19`
* Paragraph 17.20 (maps into `ℙ^N`, F1:6374) — `projChartDomain`, `projChart`, `IsHolomorphicToProj`, `IsImmersionToProj`,
  `IsEmbeddingToProj`
* Paragraph 17.21 (F1:6414) — `IsProjMapOf`, `para17_21`
* Theorem 17.22 (F1:6440) — `thm17_22`

Omitted (U−): side claims of 17.2, the diagrams of 17.7 and 17.8, the Riemann–Roch reformulation of 17.10, finiteness in
17.14, the formulas and the example `√P` of 17.15, the remark of 17.17, the topology claims of 17.20, the `ℙ³` remark of 17.22.
-/

open scoped Manifold ContDiff Topology References ENNReal
open Set Filter TopologicalSpace CategoryTheory Opposite

namespace Forster1981

section Defs

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **The sheaf `𝓜`** of meromorphic functions (17.17, Ch. 2 §17, F1:6322): representatives modulo functions vanishing off a
discrete set. -/
abbrev modM (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  localRepPresheaf ℂ (A := X → ℂ) (fun a x => MeromorphicAt (LiZhongQC.localExpr a x) (chartAt ℂ x x))
    (fun a x => ∀ᶠ y in 𝓝[≠] x, a y = 0)

/-- **The sheaf `𝓜^(1)`** of meromorphic 1-forms (17.2, Ch. 2 §17, F1:5868). -/
abbrev modM1 (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  localRepPresheaf ℂ (A := Form1 X)
    (fun w x => w.IsFormOn {x} ∧ w.IsType10On {x} ∧
      ∀ y z, z ∈ (chartAt ℂ y).target → (chartAt ℂ y).symm z = x → MeromorphicAt (w.1 y) z)
    (fun w x => ∀ᶠ y in 𝓝[≠] x, w.VanishOn {y})

/-- **The sheaf `Ω_D`** (17.4, Ch. 2 §17, F1:5954): meromorphic 1-forms `ω` with `ord_x ω ≥ −D(x)`. -/
abbrev modOmegaD (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] (D : Function.locallyFinsupp X ℤ) :
    TopCat.Presheaf (ModuleCat.{0} ℂ) (TopCat.of X) :=
  localRepPresheaf ℂ (A := Form1 X)
    (fun w x => w.IsFormOn {x} ∧ w.IsType10On {x} ∧
      (∀ y z, z ∈ (chartAt ℂ y).target → (chartAt ℂ y).symm z = x → MeromorphicAt (w.1 y) z) ∧
      ((-(D x) : ℤ) : WithTop ℤ) ≤ w.orderAt x)
    (fun w x => ∀ᶠ y in 𝓝[≠] x, w.VanishOn {y})

/-- **A Mittag–Leffler distribution of forms** (17.2, Ch. 2 §17, F1:5868): a 0-cochain `μ = (ω_i)` of `𝓜^(1)` whose
coboundary `δμ` comes from a cocycle of `Ω` (the differences `ω_j − ω_i` are holomorphic); `ι` is the inclusion
`Ω → 𝓜^(1)`. -/
def IsMLDistribution1 (ι : modOmega X ⟶ modM1 X) (𝔘 : CechCover X ⊤) (μ : CechC0 (modM1 X) 𝔘.U) : Prop :=
  ∃ ξ : ↥(cechZ1 (modOmega X) 𝔘.U), cechMap ι 𝔘.U ξ = cechD0 (modM1 X) 𝔘.U μ

/-- **The class `[δμ] ∈ H¹(X, Ω)`** of a Mittag–Leffler distribution (17.2, Ch. 2 §17, F1:5868). -/
def IsMLClass1 (ι : modOmega X ⟶ modM1 X) (𝔘 : CechCover X ⊤) (μ : CechC0 (modM1 X) 𝔘.U)
    (c : H1 (modOmega X) ⊤) : Prop :=
  ∃ ξ : ↥(cechZ1 (modOmega X) 𝔘.U), cechMap ι 𝔘.U ξ = cechD0 (modM1 X) 𝔘.U μ ∧ c = cechClass (modOmega X) 𝔘 ξ

/-- **The residue `Res_a(μ)`** of a Mittag–Leffler distribution at `a` (17.2, Ch. 2 §17, F1:5868): `Res_a(ω_i)` for an
index `i` with `a ∈ U_i`. -/
def HasMLResidue1 (𝔘 : CechCover X ⊤) (μ : CechC0 (modM1 X) 𝔘.U) (a : X) (r : ℂ) : Prop :=
  ∃ i, a ∈ 𝔘.U i ∧ ∀ (w : Form1 X) (hw : w ∈ repSpan (R := ℂ) (fun (w : Form1 X) x => w.IsFormOn {x} ∧ w.IsType10On {x} ∧
      ∀ y z, z ∈ (chartAt ℂ y).target → (chartAt ℂ y).symm z = x → MeromorphicAt (w.1 y) z) (𝔘.U i : Set X)),
    (Submodule.Quotient.mk ⟨w, hw⟩ : ↥((modM1 X).obj (op (𝔘.U i)))) = μ i → HasResidue w a r

/-- **The linear form `Res : H¹(X, Ω) → ℂ`** (17.1, Ch. 2 §17, F1:5854): for the exact sequence
`0 → Ω → ℰ^{1,0} → ℰ^(2) → 0` (any `α`, `β` induced by `ω ↦ ω`, `ω ↦ dω`), a cocycle `ξ` of `Ω` that becomes `δσ` in
`ℰ^{1,0}` and a global 2-form `τ` with `τ|U_i = dσ_i`: `Res [ξ] = (1/2πi) ∬_X τ`. -/
def IsResH1 (Res : H1 (modOmega X) ⊤ →ₗ[ℂ] ℂ) : Prop :=
  ∀ (α : modOmega X ⟶ modE10 X) (β : modE10 X ⟶ modE2 X), IsInducedBy α (id : Form1 X → Form1 X) →
    IsInducedBy β Form1.d → IsShortExactSeq _ _ _ α β →
    ∀ (𝔘 : CechCover X ⊤) (ξ : ↥(cechZ1 (modOmega X) 𝔘.U)) (σ : CechC0 (modE10 X) 𝔘.U) (τ : Form2 X)
      (hτ : τ ∈ smoothForms2On X ⊤),
      cechMap α 𝔘.U ξ = cechD0 (modE10 X) 𝔘.U σ →
      (∀ i, β.app (op (𝔘.U i)) (σ i) =
        cechRes (modE2 X) (le_top : 𝔘.U i ≤ ⊤) (Submodule.Quotient.mk ⟨τ, hτ⟩ : ↥((modE2 X).obj (op ⊤)))) →
      ∃ v, HasIntegral2 τ v ∧ Res (cechClass (modOmega X) 𝔘 ξ) = (2 * Real.pi * Complex.I)⁻¹ * v

/-- **The product of a form by a class** (17.5, Ch. 2 §17, F1:5976): the product `Ω_{−D} × 𝒪_D → Ω`,
`(ω, f) ↦ ωf`, induces `H⁰(X, Ω_{−D}) × H¹(X, 𝒪_D) → H¹(X, Ω)`: `η = ω ξ` when `ξ = [c]`, `η = [c′]` for cocycles with
`c′_ij = ω f_ij` on the representatives.
Modelling: the product `w · a` of representatives is read up to null modification: `c′_ij` is the class of a
holomorphic representative `h` that agrees with `w · a` on a punctured neighbourhood of every point of `U_i ∩ U_j`.
[CORRECTION, Forster-fix1] Representatives of `𝒪_D` and `Ω_{−D}` are taken modulo forms vanishing on punctured
neighbourhoods, so their values at single points are arbitrary; requiring `w · a` itself to be a holomorphic
representative for all representatives made the relation unsatisfiable and `IsSerreDuality` vacuous (AUDIT5_Forster
G1). -/
def IsFormTimesClass (D : Function.locallyFinsupp X ℤ) (s : H0 (modOmegaD X (-D))) (ξ : H1 (modOD X D) ⊤)
    (η : H1 (modOmega X) ⊤) : Prop :=
  ∃ (𝔘 : CechCover X ⊤) (c : ↥(cechZ1 (modOD X D) 𝔘.U)) (c' : ↥(cechZ1 (modOmega X) 𝔘.U)),
    ξ = cechClass (modOD X D) 𝔘 c ∧ η = cechClass (modOmega X) 𝔘 c' ∧
    ∀ (i j : 𝔘.ι) (a : X → ℂ) (w : Form1 X)
      (ha : a ∈ repSpan (R := ℂ) (fun (a : X → ℂ) x => MeromorphicAt (LiZhongQC.localExpr a x) (chartAt ℂ x x) ∧
        ((-(D x) : ℤ) : WithTop ℤ) ≤ LiZhongQC.ordRS a x) ((𝔘.U i ⊓ 𝔘.U j : Opens X) : Set X))
      (hw : w ∈ repSpan (R := ℂ) (fun (w : Form1 X) x => w.IsFormOn {x} ∧ w.IsType10On {x} ∧
        (∀ y z, z ∈ (chartAt ℂ y).target → (chartAt ℂ y).symm z = x → MeromorphicAt (w.1 y) z) ∧
        ((-((-D) x) : ℤ) : WithTop ℤ) ≤ w.orderAt x) ((𝔘.U i ⊓ 𝔘.U j : Opens X) : Set X)),
      (Submodule.Quotient.mk ⟨a, ha⟩ : ↥((modOD X D).obj (op (𝔘.U i ⊓ 𝔘.U j)))) = (c : CechC1 (modOD X D) 𝔘.U) i j →
      (Submodule.Quotient.mk ⟨w, hw⟩ : ↥((modOmegaD X (-D)).obj (op (𝔘.U i ⊓ 𝔘.U j)))) =
        cechRes (modOmegaD X (-D)) (inf_le_left.trans le_top : 𝔘.U i ⊓ 𝔘.U j ≤ ⊤) s →
      ∃ (h : Form1 X) (hb : h ∈ repSpan (R := ℂ) (fun (w : Form1 X) x => w.IsFormOn {x} ∧ w.IsType10On {x} ∧ w.IsHolAt x)
          ((𝔘.U i ⊓ 𝔘.U j : Opens X) : Set X)),
        (∀ x ∈ ((𝔘.U i ⊓ 𝔘.U j : Opens X) : Set X), ∀ᶠ y in 𝓝[≠] x, (h - w.smulFun a).VanishOn {y}) ∧
        (c' : CechC1 (modOmega X) 𝔘.U) i j = Submodule.Quotient.mk ⟨h, hb⟩

/-- **The Serre pairing** `ι_D : H⁰(X, Ω_{−D}) → H¹(X, 𝒪_D)*` (17.5, Ch. 2 §17, F1:5976): `ι_D ω (ξ) = Res (ωξ)`. -/
def IsSerreDuality (Res : H1 (modOmega X) ⊤ →ₗ[ℂ] ℂ) (D : Function.locallyFinsupp X ℤ)
    (ι : H0 (modOmegaD X (-D)) →ₗ[ℂ] Module.Dual ℂ (H1 (modOD X D) ⊤)) : Prop :=
  ∀ (s : H0 (modOmegaD X (-D))) (ξ : H1 (modOD X D) ⊤) (η : H1 (modOmega X) ⊤),
    IsFormTimesClass D s ξ η → ι s ξ = Res η

/-- **The branching order** `b(f, x) = v(f, x) − 1` (17.14, Ch. 2 §17, F1:6234). -/
noncomputable def branchingOrder {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y] (f : X → Y) (x : X) : ℕ :=
  (multiplicity f x).toNat - 1

/-- **The total branching order** `b(f) = Σ b(f, x)` (17.14, Ch. 2 §17, F1:6234); finite on a compact surface. -/
noncomputable def totalBranchingOrder {Y : Type} [TopologicalSpace Y] [ChartedSpace ℂ Y] (f : X → Y) : ℕ :=
  ∑ᶠ x, branchingOrder f x

/-- **The chart domains of `ℙ^N`** (17.20, Ch. 2 §17, F1:6374): `U_j = {z_j ≠ 0}`. -/
def projChartDomain {n : ℕ} (j : Fin n) : Set (Projectivization ℂ (Fin n → ℂ)) := {p | p.rep j ≠ 0}

/-- **The charts of `ℙ^N`** (17.20, Ch. 2 §17, F1:6374): `φ_j(p)_ν = z_ν/z_j`. -/
noncomputable def projChart {n : ℕ} (j : Fin n) (p : Projectivization ℂ (Fin n → ℂ)) (ν : Fin n) : ℂ :=
  p.rep ν / p.rep j

/-- **Holomorphic maps into `ℙ^N`** (17.20, Ch. 2 §17, F1:6374): `F⁻¹ U_j` is open and the coordinates `φ_j ∘ F` are
holomorphic on it. -/
def IsHolomorphicToProj {n : ℕ} (F : X → Projectivization ℂ (Fin n → ℂ)) : Prop :=
  ∀ j : Fin n, IsOpen (F ⁻¹' projChartDomain j) ∧
    ∀ ν : Fin n, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (fun x => projChart j (F x) ν) (F ⁻¹' projChartDomain j)

/-- **Immersions into `ℙ^N`** (17.20, Ch. 2 §17, F1:6374): holomorphic, and at every point some coordinate `F_jν` has
nonzero differential. -/
def IsImmersionToProj {n : ℕ} (F : X → Projectivization ℂ (Fin n → ℂ)) : Prop :=
  IsHolomorphicToProj F ∧ ∀ x, ∃ j ν : Fin n, x ∈ F ⁻¹' projChartDomain j ∧ ν ≠ j ∧
    LiZhongQC.dz ((fun y => projChart j (F y) ν) ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) ≠ 0

/-- **Embeddings into `ℙ^N`** (17.20, Ch. 2 §17, F1:6374): injective immersions. -/
def IsEmbeddingToProj {n : ℕ} (F : X → Projectivization ℂ (Fin n → ℂ)) : Prop :=
  IsImmersionToProj F ∧ Function.Injective F

/-- **The map `(f₀ : ⋯ : f_N)`** (17.21, Ch. 2 §17, F1:6414): at `x`, with `k = min_j ord_x f_j` and `f_j = z^k g_j`,
`F(x) = (g₀(x) : ⋯ : g_N(x))`. -/
def IsProjMapOf {n : ℕ} (f : Fin n → X → ℂ) (F : X → Projectivization ℂ (Fin n → ℂ)) : Prop :=
  ∀ x, ∃ (k : ℤ) (v : Fin n → ℂ) (hv : v ≠ 0), (∀ j, (k : WithTop ℤ) ≤ LiZhongQC.ordRS (f j) x) ∧
    (∃ j, LiZhongQC.ordRS (f j) x = k) ∧ F x = Projectivization.mk ℂ v hv ∧
    ∀ j, Tendsto (fun z => LiZhongQC.localExpr (f j) x z / (z - chartAt ℂ x x) ^ k) (𝓝[≠] (chartAt ℂ x x))
      (𝓝 (v j))

/-- **Globally generated** (17.18, Ch. 2 §17, F1:6340): for every `x` some `f ∈ H⁰(X, 𝒪_D)` has `ord_x f = −D(x)`. -/
def IsGloballyGenerated (D : Function.locallyFinsupp X ℤ) : Prop :=
  ∀ x, ∃ f : X → ℂ, f ∈ repSpan (R := ℂ) (fun (a : X → ℂ) y => MeromorphicAt (LiZhongQC.localExpr a y) (chartAt ℂ y y) ∧
    ((-(D y) : ℤ) : WithTop ℤ) ≤ LiZhongQC.ordRS a y) (Set.univ : Set X) ∧ LiZhongQC.ordRS f x = ((-(D x) : ℤ) : WithTop ℤ)

end Defs

section Statements

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Paragraph 17.1** (Ch. 2 §17, F1:5854). On a compact Riemann surface there is exactly one linear form
`Res : H¹(X, Ω) → ℂ` with the property of 17.1 (the book's definition is independent of the representative by 10.20). -/
theorem para17_1 [CompactSpace X] : ∃! Res : H1 (modOmega X) ⊤ →ₗ[ℂ] ℂ, IsResH1 Res := by
  sorry

/-- **Theorem 17.3** (Ch. 2 §17, F1:5886). On a compact Riemann surface, for a Mittag–Leffler distribution `μ`:
`Res(μ) = Res([δμ])`, where `Res(μ) = Σ_a Res_a(μ)`. -/
theorem thm17_3 [CompactSpace X] {Res : H1 (modOmega X) ⊤ →ₗ[ℂ] ℂ} (hRes : IsResH1 Res)
    {ι : modOmega X ⟶ modM1 X} (hι : IsInducedBy ι (id : Form1 X → Form1 X)) {𝔘 : CechCover X ⊤}
    {μ : CechC0 (modM1 X) 𝔘.U} (hμ : IsMLDistribution1 ι 𝔘 μ) {c : H1 (modOmega X) ⊤} (hc : IsMLClass1 ι 𝔘 μ c)
    {r : X → ℂ} (hr : ∀ a, HasMLResidue1 𝔘 μ a (r a)) : (∑ᶠ a, r a) = Res c := by
  sorry

/-- **Paragraph 17.4** (Ch. 2 §17, F1:5954). Let `ω` be a non-trivial meromorphic 1-form with divisor `K`. Multiplication
by `ω` is an isomorphism of sheaves `𝒪_{D+K} ≅ Ω_D`, `f ↦ fω`. -/
theorem para17_4 [CompactSpace X] {w : Form1 X} {K : Function.locallyFinsupp X ℤ} (hw : IsDivisorOfForm w K)
    (D : Function.locallyFinsupp X ℤ) :
    ∃ e : modOD X (D + K) ≅ modOmegaD X D, IsInducedBy e.hom (fun (a : X → ℂ) => w.smulFun a) := by
  sorry

/-- **Lemma in 17.4** (Ch. 2 §17, F1:5954). There is a constant `k₀ ∈ ℤ` with `dim H⁰(X, Ω_D) ≥ deg D + k₀` for every
divisor `D`. -/
theorem lemma17_4 [CompactSpace X] :
    ∃ k₀ : ℤ, ∀ D : Function.locallyFinsupp X ℤ, (Module.finrank ℂ (H0 (modOmegaD X D)) : ℤ) ≥ divDeg D + k₀ := by
  sorry

/-- **Paragraph 17.5** (Ch. 2 §17, F1:5976). On a compact Riemann surface, for every divisor `D` the pairing
`⟨ω, ξ⟩ = Res(ωξ)` induces a (unique) linear map `ι_D : H⁰(X, Ω_{−D}) → H¹(X, 𝒪_D)*`. -/
theorem para17_5 [CompactSpace X] {Res : H1 (modOmega X) ⊤ →ₗ[ℂ] ℂ} (hRes : IsResH1 Res)
    (D : Function.locallyFinsupp X ℤ) :
    ∃! ι : H0 (modOmegaD X (-D)) →ₗ[ℂ] Module.Dual ℂ (H1 (modOD X D) ⊤), IsSerreDuality Res D ι := by
  sorry

/-- **Theorem 17.6** (Ch. 2 §17, F1:6002). The map `ι_D` is injective. -/
theorem thm17_6 [CompactSpace X] {Res : H1 (modOmega X) ⊤ →ₗ[ℂ] ℂ} (hRes : IsResH1 Res)
    {D : Function.locallyFinsupp X ℤ} {ι : H0 (modOmegaD X (-D)) →ₗ[ℂ] Module.Dual ℂ (H1 (modOD X D) ⊤)}
    (hι : IsSerreDuality Res D ι) : Function.Injective ι := by
  sorry

/-- **Lemma 17.7** (Ch. 2 §17, F1:6038). Let `D′ ≤ D` be divisors on a compact Riemann surface, `λ ∈ H¹(X, 𝒪_D)*` and
`ω ∈ H⁰(X, Ω_{−D′})` with `i^D_{D′}(λ) = ι_{D′}(ω)`, where `i^D_{D′}` is the dual of `H¹(X, 𝒪_{D′}) → H¹(X, 𝒪_D)`. Then
`ω` lies in `H⁰(X, Ω_{−D})` and `λ = ι_D(ω)`.
Reading: the printed hypothesis `ω ∈ H⁰(X, Ω_{−D})` is `ω ∈ H⁰(X, Ω_{−D′})` [misprint]. -/
theorem lemma17_7 [CompactSpace X] {Res : H1 (modOmega X) ⊤ →ₗ[ℂ] ℂ} (hRes : IsResH1 Res)
    {D D' : Function.locallyFinsupp X ℤ} (h : D' ≤ D)
    {ιD : H0 (modOmegaD X (-D)) →ₗ[ℂ] Module.Dual ℂ (H1 (modOD X D) ⊤)} (hD : IsSerreDuality Res D ιD)
    {ιD' : H0 (modOmegaD X (-D')) →ₗ[ℂ] Module.Dual ℂ (H1 (modOD X D') ⊤)} (hD' : IsSerreDuality Res D' ιD')
    {incl : modOD X D' ⟶ modOD X D} (hincl : IsInducedBy incl (id : (X → ℂ) → (X → ℂ)))
    {π₁ : H1 (modOD X D') ⊤ →ₗ[ℂ] H1 (modOD X D) ⊤} (hπ : IsH1Induced _ _ incl π₁)
    {j : modOmegaD X (-D) ⟶ modOmegaD X (-D')} (hj : IsInducedBy j (id : Form1 X → Form1 X))
    (lam : Module.Dual ℂ (H1 (modOD X D) ⊤)) (s : H0 (modOmegaD X (-D')))
    (hs : π₁.dualMap lam = ιD' s) :
    ∃ s₀ : H0 (modOmegaD X (-D)), (j.app (op ⊤)) s₀ = s ∧ lam = ιD s₀ := by
  sorry

/-- **Lemma 17.8** (Ch. 2 §17, F1:6102). Let `ψ ∈ H⁰(X, 𝒪_B)` be non-zero. Then multiplication by `ψ`,
`H¹(X, 𝒪_D)* → H¹(X, 𝒪_{D−B})*`, is injective. -/
theorem lemma17_8 [CompactSpace X] {D B A : Function.locallyFinsupp X ℤ} {ψ : X → ℂ} (hψ : IsDivisorOf ψ A)
    (hA : -B ≤ A) {mulψ : modOD X (D - B) ⟶ modOD X D}
    (hmul : IsInducedBy mulψ (fun (a : X → ℂ) x => ψ x * a x))
    {m₁ : H1 (modOD X (D - B)) ⊤ →ₗ[ℂ] H1 (modOD X D) ⊤} (hm : IsH1Induced _ _ mulψ m₁) :
    Function.Injective m₁.dualMap := by
  sorry

/-- **Theorem 17.9** (Serre duality, Ch. 2 §17, F1:6124). For every divisor `D` on a compact Riemann surface, `ι_D` is an
isomorphism. -/
theorem thm17_9 [CompactSpace X] {Res : H1 (modOmega X) ⊤ →ₗ[ℂ] ℂ} (hRes : IsResH1 Res)
    {D : Function.locallyFinsupp X ℤ} {ι : H0 (modOmegaD X (-D)) →ₗ[ℂ] Module.Dual ℂ (H1 (modOD X D) ⊤)}
    (hι : IsSerreDuality Res D ι) : Function.Bijective ι := by
  sorry

/-- **Remark 17.10(a)** (Ch. 2 §17, F1:6172). `dim H¹(X, 𝒪_D) = dim H⁰(X, Ω_{−D})`. -/
theorem rem17_10_a [CompactSpace X] (D : Function.locallyFinsupp X ℤ) :
    Module.finrank ℂ (H1 (modOD X D) ⊤) = Module.finrank ℂ (H0 (modOmegaD X (-D))) := by
  sorry

/-- **Remark 17.10(b)** (Ch. 2 §17, F1:6172). The genus equals the dimension of the space of holomorphic 1-forms:
`g = dim Ω(X)`.
Near miss: `Lehto1987.para4_5_3` (`dim` of the holomorphic differentials is the topological genus `p`, for `HasGenus S p`). -/
theorem rem17_10_b [CompactSpace X] : genus X = Module.finrank ℂ (H0 (modOmega X)) := by
  sorry

/-- **Theorem 17.11** (Ch. 2 §17, F1:6194). For a divisor `D` on a compact Riemann surface, `H⁰(X, 𝒪_{−D}) ≅ H¹(X, Ω_D)*`. -/
theorem thm17_11 [CompactSpace X] (D : Function.locallyFinsupp X ℤ) :
    Nonempty (H0 (modOD X (-D)) ≃ₗ[ℂ] Module.Dual ℂ (H1 (modOmegaD X D) ⊤)) := by
  sorry

/-- **Consequence of 17.11** (Ch. 2 §17, F1:6194). `dim H¹(X, Ω) = 1`, and `Res : H¹(X, Ω) → ℂ` is an isomorphism. -/
theorem thm17_11_cons [CompactSpace X] :
    Module.finrank ℂ (H1 (modOmega X) ⊤) = 1 ∧
      ∀ Res : H1 (modOmega X) ⊤ →ₗ[ℂ] ℂ, IsResH1 Res → Function.Bijective Res := by
  sorry

/-- **Theorem 17.12** (Ch. 2 §17, F1:6210). The divisor of a non-vanishing meromorphic 1-form on a compact Riemann surface
of genus `g` has degree `2g − 2`.
Near miss: `LiZhongQC.deg_canonical` (`deg K = 2g − 2` for the project's `Divisor` and the topological genus `HasGenus`; here `g` is `dim H¹(X, 𝒪)` and `K` is a `Function.locallyFinsupp` divisor). -/
theorem thm17_12 [CompactSpace X] {w : Form1 X} {K : Function.locallyFinsupp X ℤ} (hw : IsDivisorOfForm w K) :
    divDeg K = 2 * (genus X : ℤ) - 2 := by
  sorry

/-- **Corollary 17.13** (Ch. 2 §17, F1:6230). For any lattice `Γ ⊆ ℂ` the torus `ℂ/Γ` has genus one.
Near miss: `Lehto1987.para4_5_2_a` (a torus has topological genus 1, for `HasGenus S 1`). -/
theorem cor17_13 (L : PeriodPair) (hX : IsTorusWith L X) : genus X = 1 := by
  sorry

/-- **Theorem 17.14** (the Riemann–Hurwitz formula, Ch. 2 §17, F1:6234). Let `f : X → Y` be an `n`-sheeted holomorphic
covering map between compact Riemann surfaces with total branching order `b`, and let `g`, `g′` be the genera of `X`, `Y`.
Then `g = b/2 + n (g′ − 1) + 1` (in `ℚ`). -/
theorem thm17_14 [CompactSpace X] {Y : Type} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y] [CompactSpace Y] {n : ℕ} {f : X → Y} (hf : IsHolomorphicCovering f n) :
    (genus X : ℚ) = (totalBranchingOrder f : ℚ) / 2 + n * ((genus Y : ℚ) - 1) + 1 := by
  sorry

/-- **Hyperelliptic surfaces** (17.15, Ch. 2 §17, F1:6292): a compact Riemann surface of genus `> 1` which admits a double
covering of `ℙ¹`. -/
def IsHyperelliptic (X : Type) [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  1 < genus X ∧ ∃ π : X → References.RiemannSphere, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π ∧ IsHolomorphicCovering π 2

/-- **Theorem 17.16** (Ch. 2 §17, F1:6314). On a compact Riemann surface of genus `g`, `H¹(X, 𝒪_D) = 0` whenever
`deg D > 2g − 2`. -/
theorem thm17_16 [CompactSpace X] {D : Function.locallyFinsupp X ℤ} (hD : 2 * (genus X : ℤ) - 2 < divDeg D) :
    Subsingleton (H1 (modOD X D) ⊤) := by
  sorry

/-- **Corollary 17.17** (Ch. 2 §17, F1:6322). On a compact Riemann surface, `H¹(X, 𝓜) = 0`. -/
theorem cor17_17 [CompactSpace X] : Subsingleton (H1 (modM X) ⊤) := by
  sorry

/-- **Theorem 17.19** (Ch. 2 §17, F1:6352). On a compact Riemann surface of genus `g`, for a divisor `D` with `deg D ≥ 2g`
the sheaf `𝒪_D` is globally generated. -/
theorem thm17_19 [CompactSpace X] {D : Function.locallyFinsupp X ℤ} (hD : 2 * (genus X : ℤ) ≤ divDeg D) :
    IsGloballyGenerated D := by
  sorry

/-- **Paragraph 17.21** (Ch. 2 §17, F1:6414). For meromorphic functions `f₀, …, f_N`, none identically zero, the map
`(f₀ : ⋯ : f_N)` is well defined (unique) and holomorphic. -/
theorem para17_21 {n : ℕ} {f : Fin n → X → ℂ} (hf : ∀ j, LiZhongQC.IsMeromorphicRS (f j))
    (hz : ∀ j, ¬ ∀ᶠ x in Filter.codiscrete X, f j x = 0) :
    ∃! F : X → Projectivization ℂ (Fin n → ℂ), IsProjMapOf f F ∧ IsHolomorphicToProj F := by
  sorry

/-- **Theorem 17.22** (Ch. 2 §17, F1:6440). On a compact Riemann surface `X` of genus `g` let `D` be a divisor of degree
`≥ 2g + 1` and `f₀, …, f_N` a basis of `H⁰(X, 𝒪_D)`. Then `F = (f₀ : ⋯ : f_N) : X → ℙ^N` is an embedding. -/
theorem thm17_22 [CompactSpace X] {D : Function.locallyFinsupp X ℤ} (hD : 2 * (genus X : ℤ) + 1 ≤ divDeg D) {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (H0 (modOD X D))) (f : Fin n → X → ℂ)
    (hf : ∀ j, ∃ hfj : f j ∈ repSpan (R := ℂ) (fun (a : X → ℂ) y => MeromorphicAt (LiZhongQC.localExpr a y) (chartAt ℂ y y) ∧
        ((-(D y) : ℤ) : WithTop ℤ) ≤ LiZhongQC.ordRS a y) (Set.univ : Set X),
      (Submodule.Quotient.mk ⟨f j, hfj⟩ : ↥((modOD X D).obj (op ⊤))) = b j)
    {F : X → Projectivization ℂ (Fin n → ℂ)} (hF : IsProjMapOf f F) : IsEmbeddingToProj F := by
  sorry

end Statements

end Forster1981
