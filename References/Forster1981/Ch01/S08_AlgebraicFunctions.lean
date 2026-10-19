import References.Forster1981.Ch01.S07_AnalyticContinuation

/-!
# Forster, Chapter 1 §8: Algebraic functions

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §8 (`full.md` F1:1901–2332).

Conventions: `𝓜(X)` is the ℂ-algebra `meroFun X` of germs along the codiscrete filter (§1.13(b)); a statement about the
field `𝓜(X)` is a statement about this commutative ring (`rem1_16_b`: it is a field); "Galois" for an extension `L : K` is
`Nat.card (L ≃ₐ[K] L) = Module.finrank K L` (equivalent for finite field extensions). The pull-back
`π^* : 𝓜(X) → 𝓜(Y)` is the ring homomorphism `meroPullback` into the ring of all germs on `Y` (that it lands in
`meroFun Y` is part of the statements, `∃ hmem, …`). An `n`-sheeted branched holomorphic covering is
`IsHolomorphicCovering π n` (§4).

* Paragraph 8.1 (elementary symmetric functions, F1:1905) — `IsElemSymmOn`, `IsElemSymmFunctions`, `para8_1`
* Theorem 8.2 (F1:1919) — `thm8_2_a`, `thm8_2_b`
* Remark after 8.2 (the proof does not use connectedness of `Y`, F1:1943) — `rem8_2`
* Paragraph after 8.2 (`π^* : 𝓜(X) → 𝓜(Y)` is a monomorphism of fields, F1:1945) — `meroPullback`, `meroPullbackHom`,
  `meroPullback_injective`
* Theorem 8.3 (F1:1953) — `thm8_3_a`, `thm8_3_b`, `thm8_3_c`
* Theorem 8.4 (F1:1981) — `thm8_4`
* Theorem 8.5 (F1:2017) — `thm8_5_a`, `thm8_5_b`
* Definition 8.6 (Galois branched covering, F1:2025) — `IsGaloisBranchedCovering`
* Lemma 8.7 (F1:2027) — `lemma8_7`
* Corollary 8.8 (F1:2071) — `cor8_8`
* Theorem 8.9 (the algebraic function defined by `P`, F1:2089) — `IsAlgebraicFunctionOf`, `thm8_9_a`, `thm8_9_b`
* Example 8.10 (the square root, F1:2141) — `example8_10_a`, `example8_10_b`
* Paragraph 8.11 (F1:2183) — `para8_11`
* Theorem 8.12 (F1:2197) — `thm8_12_a`, `thm8_12_b`, `thm8_12_c`
* Paragraph 8.13 (the field `ℂ{{z}}`, F1:2217) — `convLaurent`
* Theorem 8.14 (Puiseux, F1:2263) — `thm8_14`

Omitted (U−): the remarks after 8.3 (F1:1975), the derivation of 8.14 and its remarks (F1:2225–2261, 2263 ff.), the
identification `ℂ{{z}} ≅ 𝓜₀` (F1:2223).
-/

open scoped Manifold ContDiff Topology References
open Set Filter

namespace Forster1981

open scoped Forster1981

section Surfaces

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type} [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **8.1** (Ch. 1 §8, F1:1905). `c : Fin n → X → ℂ` are *elementary symmetric functions of `f` over `X ∖ A`* with
respect to `π : Y → X`: over every `x ∉ A` there are an open neighbourhood `U` of `x` and `n` holomorphic sections
`τ_ν : U → Y` of `π` with disjoint images covering `π⁻¹(U)`, and on `U`
`c_ν = (−1)^ν s_ν(f ∘ τ₁, …, f ∘ τ_n)`, `s_ν` the `ν`-th elementary symmetric polynomial (indices `ν = 0, …, n − 1` stand for
`1, …, n`).
Modelling: the formula is asserted where none of the `τ_μ(x)` is a pole of `f` (the values of `f` at poles are junk). -/
def IsElemSymmOn (π : Y → X) {n : ℕ} (f : Y → ℂ) (c : Fin n → X → ℂ) (A : Set X) : Prop :=
  ∀ x, x ∉ A → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ τ : Fin n → X → Y,
    (∀ ν, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (τ ν) U) ∧ (∀ ν, ∀ y ∈ U, π (τ ν y) = y) ∧
    (∀ y ∈ U, Function.Injective fun ν => τ ν y) ∧ (∀ z, π z ∈ U → ∃ ν, τ ν (π z) = z) ∧
    ∀ ν : Fin n, ∀ y ∈ U, (∀ μ, τ μ y ∉ poles f univ) →
      c ν y = (-1) ^ ((ν : ℕ) + 1) * Multiset.esymm (Multiset.map (fun μ => f (τ μ y)) Finset.univ.val) ((ν : ℕ) + 1)

/-- **8.1** (Ch. 1 §8, F1:1905). For an `n`-sheeted unbranched holomorphic covering and `f ∈ 𝓜(Y)`, the functions
`c₁, …, c_n` (elementary symmetric functions over the complement of the critical values) are meromorphic on `X`. -/
def IsElemSymmFunctions (π : Y → X) {n : ℕ} (f : Y → ℂ) (c : Fin n → X → ℂ) : Prop :=
  IsElemSymmOn π f c (criticalValues π) ∧ ∀ ν, IsMeromorphicOn (c ν) univ

/-- **The pull-back `π^* : 𝓜(X) → 𝓜(Y)`** (after 8.2, Ch. 1 §8, F1:1945): `F ↦ F ∘ π` on germs, as a ring homomorphism into
the ring of all germs along the codiscrete filter of `Y`. It requires that `π` maps codiscrete sets to codiscrete sets
(`hπ`, a consequence of Theorem 4.2 that is not assumed by the definition). That the image lies in `meroFun Y` is stated in
the theorems that use it. -/
noncomputable def meroPullback (π : Y → X) (hπ : Tendsto π (Filter.codiscrete Y) (Filter.codiscrete X)) :
    meroFun X →+* (Filter.codiscrete Y).Germ ℂ where
  toFun F := F.1.compTendsto π hπ
  map_one' := by
    show ((1 : (Filter.codiscrete X).Germ ℂ)).compTendsto π hπ = 1
    exact Filter.Germ.const_compTendsto 1 hπ
  map_mul' F G := by
    show (F.1 * G.1).compTendsto π hπ = F.1.compTendsto π hπ * G.1.compTendsto π hπ
    induction F.1 using Filter.Germ.inductionOn with | _ f => ?_
    induction G.1 using Filter.Germ.inductionOn with | _ g => ?_
    rfl
  map_zero' := by
    show ((0 : (Filter.codiscrete X).Germ ℂ)).compTendsto π hπ = 0
    exact Filter.Germ.const_compTendsto 0 hπ
  map_add' F G := by
    show (F.1 + G.1).compTendsto π hπ = F.1.compTendsto π hπ + G.1.compTendsto π hπ
    induction F.1 using Filter.Germ.inductionOn with | _ f => ?_
    induction G.1 using Filter.Germ.inductionOn with | _ g => ?_
    rfl

/-- **The pull-back as a homomorphism into `𝓜(Y)`** (after 8.2, Ch. 1 §8, F1:1945): `meroPullback` corestricted to
`meroFun Y`, given that its image lies there (`hmem`, a consequence of the holomorphy of `π` that is not assumed by the
definition). -/
noncomputable def meroPullbackHom (π : Y → X) (hπ : Tendsto π (Filter.codiscrete Y) (Filter.codiscrete X))
    (hmem : ∀ F : meroFun X, meroPullback π hπ F ∈ meroFun Y) : meroFun X →+* meroFun Y :=
  (meroPullback π hπ).codRestrict (meroFun Y) hmem

/-- **Definition 8.6** (Galois branched covering, Ch. 1 §8, F1:2025). A branched holomorphic covering `π : Y → X` is
*Galois* if the unbranched covering `Y ∖ π⁻¹(B) → X ∖ B` (`B` the critical values) is Galois. -/
def IsGaloisBranchedCovering (π : Y → X) : Prop :=
  IsGaloisCovering (Set.restrictPreimage (criticalValues π)ᶜ π)

/-- **The algebraic function defined by `P`** (Theorem 8.9, Ch. 1 §8, F1:2089). For `P ∈ 𝓜(X)[T]` monic, `(Y, π, F)` is
the algebraic function defined by `P` when `π : Y → X` is an `n`-sheeted branched holomorphic covering, `n = deg P`, and
`F ∈ 𝓜(Y)` satisfies `(π^*P)(F) = 0` (in the germs on `Y`). -/
def IsAlgebraicFunctionOf (P : Polynomial (meroFun X)) (π : Y → X)
    (hπ : Tendsto π (Filter.codiscrete Y) (Filter.codiscrete X)) (F : meroFun Y) : Prop :=
  IsHolomorphicCovering π P.natDegree ∧ (P.map (meroPullback π hπ)).eval F.1 = 0

variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ConnectedSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

/-- **8.1** (Ch. 1 §8, F1:1905). For an `n`-sheeted branched holomorphic covering `π : Y → X` and a meromorphic function
`f` on `Y`, the elementary symmetric functions `c₁, …, c_n` of `f` over the complement of the critical values exist and are
meromorphic on `X`. -/
theorem para8_1 {n : ℕ} {π : Y → X} (hπ : IsHolomorphicCovering π n) {f : Y → ℂ} (hf : IsMeromorphicOn f univ) :
    ∃ c : Fin n → X → ℂ, IsElemSymmFunctions π f c := by
  sorry

/-- **Theorem 8.2(a)** (Ch. 1 §8, F1:1919). Let `π : Y → X` be an `n`-sheeted branched holomorphic covering, `A ⊆ X` closed
and discrete containing the critical values of `π`, and `f` holomorphic on `Y ∖ π⁻¹(A)` with elementary symmetric functions
`c_ν` over `X ∖ A`. Then `f` extends holomorphically to `Y` iff all `c_ν` extend holomorphically to `X`. -/
theorem thm8_2_a {n : ℕ} {π : Y → X} (hπ : IsHolomorphicCovering π n) {A : Set X} (hA : IsClosed A)
    (hAd : IsDiscrete A) (hcrit : criticalValues π ⊆ A) {f : Y → ℂ} (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (π ⁻¹' Aᶜ))
    {c : Fin n → X → ℂ} (hc : IsElemSymmOn π f c A) :
    (∃ g : Y → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ EqOn g f (π ⁻¹' Aᶜ)) ↔
      ∀ ν, ∃ c' : X → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) c' ∧ EqOn c' (c ν) Aᶜ := by
  sorry

/-- **Theorem 8.2(b)** (Ch. 1 §8, F1:1919). The meromorphic version of 8.2: with `f` meromorphic on `Y ∖ π⁻¹(A)` and `c_ν`
meromorphic on `X ∖ A`, `f` extends meromorphically to `Y` iff all `c_ν` extend meromorphically to `X`.
[CORRECTION, Forster-fix1] The book's hypothesis "`c_ν` meromorphic on `X ∖ A`" is now `hcm`: `IsElemSymmOn` does not
constrain `c_ν` over points where `f` has a pole, so without it a junk value of `c_ν` at a point where the genuine `c_ν` is
holomorphic makes the right side false (AUDIT5_Forster G2). -/
theorem thm8_2_b {n : ℕ} {π : Y → X} (hπ : IsHolomorphicCovering π n) {A : Set X} (hA : IsClosed A)
    (hAd : IsDiscrete A) (hcrit : criticalValues π ⊆ A) {f : Y → ℂ} (hf : IsMeromorphicOn f (π ⁻¹' Aᶜ))
    {c : Fin n → X → ℂ} (hc : IsElemSymmOn π f c A) (hcm : ∀ ν, IsMeromorphicOn (c ν) Aᶜ) :
    (∃ g : Y → ℂ, IsMeromorphicOn g univ ∧ EqOn g f (π ⁻¹' Aᶜ)) ↔
      ∀ ν, ∃ c' : X → ℂ, IsMeromorphicOn c' univ ∧ EqOn c' (c ν) Aᶜ := by
  sorry

/-- **Remark after Theorem 8.2** (Ch. 1 §8, F1:1943). The proof of 8.2 does not use the connectedness of `Y`: the theorem
(holomorphic and meromorphic case) holds for a Hausdorff complex 1-manifold `Y` with finitely many components and a
proper holomorphic map `π : Y → X` which is `n`-sheeted off the critical values.
Modelling: the `n` sheets are the fibres of cardinality `n` over `X ∖ B`; the elementary symmetric functions are those
of `IsElemSymmOn`. [CORRECTION, Forster-fix1] In the meromorphic half the `c_ν` are meromorphic on `X ∖ A`, as in
`thm8_2_b` (AUDIT5_Forster G2). -/
theorem rem8_2 {Y' : Type} [TopologicalSpace Y'] [T2Space Y'] [ChartedSpace ℂ Y'] [IsManifold 𝓘(ℂ) ω Y']
    [Finite (ConnectedComponents Y')] {n : ℕ} {π : Y' → X} (hπh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π) (hπp : IsProperMap π)
    (hsheets : ∀ x, x ∉ criticalValues π → (π ⁻¹' {x}).Finite ∧ (π ⁻¹' {x}).ncard = n) {A : Set X} (hA : IsClosed A)
    (hAd : IsDiscrete A) (hcrit : criticalValues π ⊆ A) {f : Y' → ℂ}
    {c : Fin n → X → ℂ} (hc : IsElemSymmOn π f c A) :
    (MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (π ⁻¹' Aᶜ) →
        ((∃ g : Y' → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ EqOn g f (π ⁻¹' Aᶜ)) ↔
          ∀ ν, ∃ c' : X → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) c' ∧ EqOn c' (c ν) Aᶜ)) ∧
      (IsMeromorphicOn f (π ⁻¹' Aᶜ) → (∀ ν, IsMeromorphicOn (c ν) Aᶜ) →
        ((∃ g : Y' → ℂ, IsMeromorphicOn g univ ∧ EqOn g f (π ⁻¹' Aᶜ)) ↔
          ∀ ν, ∃ c' : X → ℂ, IsMeromorphicOn c' univ ∧ EqOn c' (c ν) Aᶜ)) := by
  sorry

/-- **`π^*` is a monomorphism of fields** (after 8.2, Ch. 1 §8, F1:1945). For a non-constant holomorphic `π : Y → X`,
`π` maps codiscrete sets to codiscrete sets, the pull-back is injective, and it takes values in `𝓜(Y)`. -/
theorem meroPullback_injective {π : Y → X} (hπ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π) (hnc : ¬ ∃ c, ∀ y, π y = c) :
    ∃ h : Tendsto π (Filter.codiscrete Y) (Filter.codiscrete X),
      Function.Injective (meroPullback π h) ∧ ∀ F : meroFun X, meroPullback π h F ∈ meroFun Y := by
  sorry

/-- **Theorem 8.3(a)** (Ch. 1 §8, F1:1953). Let `π : Y → X` be an `n`-sheeted branched holomorphic covering and `f ∈ 𝓜(Y)`
with elementary symmetric functions `c₁, …, c_n`. Then `fⁿ + (π^*c₁) fⁿ⁻¹ + … + π^*c_n = 0` in `𝓜(Y)`: the identity holds on
`Y` off a discrete set. -/
theorem thm8_3_a {n : ℕ} {π : Y → X} (hπ : IsHolomorphicCovering π n) {f : Y → ℂ} (hf : IsMeromorphicOn f univ)
    {c : Fin n → X → ℂ} (hc : IsElemSymmFunctions π f c) :
    ∀ᶠ y in Filter.codiscrete Y, f y ^ n + ∑ ν : Fin n, c ν (π y) * f y ^ (n - 1 - (ν : ℕ)) = 0 := by
  sorry

/-- **Theorem 8.3(b)** (Ch. 1 §8, F1:1953). For an `n`-sheeted branched holomorphic covering `π : Y → X`, the map
`π^* : 𝓜(X) → 𝓜(Y)` is an algebraic field extension of degree at most `n`. Modelling: finiteness is stated explicitly (`Module.Finite`), since
`finrank` is `0` for an infinite-dimensional extension and `≤ n` alone would then hold vacuously. -/
theorem thm8_3_b {n : ℕ} {π : Y → X} (hπ : IsHolomorphicCovering π n)
    (h : Tendsto π (Filter.codiscrete Y) (Filter.codiscrete X)) :
    ∃ hmem : ∀ F : meroFun X, meroPullback π h F ∈ meroFun Y,
      letI := (meroPullbackHom π h hmem).toAlgebra
      Algebra.IsAlgebraic (meroFun X) (meroFun Y) ∧ Module.Finite (meroFun X) (meroFun Y) ∧
        Module.finrank (meroFun X) (meroFun Y) ≤ n := by
  sorry

/-- **Theorem 8.3(c)** (Ch. 1 §8, F1:1953). If some `f ∈ 𝓜(Y)` takes `n` distinct (finite) values on some fibre
`π⁻¹(x)` of the `n`-sheeted covering `π`, the extension `𝓜(Y) : π^*𝓜(X)` has degree exactly `n`. -/
theorem thm8_3_c {n : ℕ} {π : Y → X} (hπ : IsHolomorphicCovering π n)
    (h : Tendsto π (Filter.codiscrete Y) (Filter.codiscrete X)) {f : Y → ℂ} (hf : IsMeromorphicOn f univ) {x : X}
    (hx : (π ⁻¹' {x}).ncard = n) (hinj : InjOn f (π ⁻¹' {x})) (hpol : ∀ y ∈ π ⁻¹' {x}, y ∉ poles f univ) :
    ∃ hmem : ∀ F : meroFun X, meroPullback π h F ∈ meroFun Y,
      letI := (meroPullbackHom π h hmem).toAlgebra
      Module.finrank (meroFun X) (meroFun Y) = n := by
  sorry

/-- **Theorem 8.4** (Ch. 1 §8, F1:1981). Let `A ⊆ X` be closed and discrete and `π′ : Y′ → X ∖ A` a proper unbranched
holomorphic covering map of a Riemann surface `Y′`. Then there are a Riemann surface `Y`, a proper holomorphic map
`π : Y → X` and a fibre-preserving biholomorphic map `φ : Y ∖ π⁻¹(A) → Y′`.
Modelling: `Y ∖ π⁻¹(A)` is the open submanifold of `Y`; the openness of `π⁻¹(Aᶜ)` is part of the conclusion. -/
theorem thm8_4 {A : Set X} (hA : IsClosed A) (hAd : IsDiscrete A) {Y' : Type} [TopologicalSpace Y'] [T2Space Y']
    [ConnectedSpace Y'] [ChartedSpace ℂ Y'] [IsManifold 𝓘(ℂ) ω Y']
    {π' : Y' → ↥(⟨Aᶜ, hA.isOpen_compl⟩ : TopologicalSpace.Opens X)} (hp : IsProperMap π')
    (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π') (hu : IsUnbranched π') :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : ChartedSpace ℂ Y), References.IsRiemannSurface Y ∧
      ∃ π : Y → X, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π ∧ IsProperMap π ∧ ∃ h : IsOpen (π ⁻¹' Aᶜ),
        ∃ φ : ↥(⟨π ⁻¹' Aᶜ, h⟩ : TopologicalSpace.Opens Y) → Y', LiZhongQC.IsBiholomorphic φ ∧
          ∀ y, ((π' (φ y) : ↥(⟨Aᶜ, hA.isOpen_compl⟩ : TopologicalSpace.Opens X)) : X) = π y := by
  sorry

/-- **Theorem 8.5(a)** (Ch. 1 §8, F1:2017). Let `π : Y → X`, `τ : Z → X` be proper non-constant holomorphic maps and
`A ⊆ X` closed and discrete. Every fibre-preserving biholomorphic map `σ′ : Y ∖ π⁻¹(A) → Z ∖ τ⁻¹(A)` extends to a
fibre-preserving biholomorphic map `σ : Y → Z`. -/
theorem thm8_5_a {π : Y → X} {τ : Z → X} (hπh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π) (hπp : IsProperMap π)
    (hπn : ¬ ∃ c, ∀ y, π y = c) (hτh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) τ) (hτp : IsProperMap τ)
    (hτn : ¬ ∃ c, ∀ z, τ z = c) {A : Set X} (hA : IsClosed A) (hAd : IsDiscrete A)
    (σ' : ↥(⟨π ⁻¹' Aᶜ, hA.isOpen_compl.preimage hπh.continuous⟩ : TopologicalSpace.Opens Y) →
      ↥(⟨τ ⁻¹' Aᶜ, hA.isOpen_compl.preimage hτh.continuous⟩ : TopologicalSpace.Opens Z))
    (hσ' : LiZhongQC.IsBiholomorphic σ') (hfib : ∀ y, τ (σ' y : Z) = π (y : Y)) :
    ∃ σ : Y → Z, LiZhongQC.IsBiholomorphic σ ∧ (τ ∘ σ) = π ∧ ∀ y, (σ' y : Z) = σ (y : Y) := by
  sorry

/-- **Theorem 8.5(b)** (Ch. 1 §8, F1:2017). Let `π : Y → X` be a proper non-constant holomorphic map and `A ⊆ X` closed and
discrete. Every covering transformation `σ′` of the restricted covering `Y ∖ π⁻¹(A) → X ∖ A` extends to a covering
transformation `σ ∈ Deck(Y/X)`. -/
theorem thm8_5_b {π : Y → X} (hπh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π) (hπp : IsProperMap π)
    (hπn : ¬ ∃ c, ∀ y, π y = c) {A : Set X} (hA : IsClosed A) (hAd : IsDiscrete A)
    (σ' : ↥(⟨π ⁻¹' Aᶜ, hA.isOpen_compl.preimage hπh.continuous⟩ : TopologicalSpace.Opens Y) ≃ₜ
      ↥(⟨π ⁻¹' Aᶜ, hA.isOpen_compl.preimage hπh.continuous⟩ : TopologicalSpace.Opens Y))
    (hσ' : σ' ∈ deck (fun y : ↥(⟨π ⁻¹' Aᶜ, hA.isOpen_compl.preimage hπh.continuous⟩ : TopologicalSpace.Opens Y) =>
      π (y : Y))) : ∃ σ ∈ deck π, ∀ y, (σ' y : Y) = σ (y : Y) := by
  sorry

/-- **8.11** (Ch. 1 §8, F1:2183). Let `π : Y → X` be a branched holomorphic covering. Each covering transformation
`σ ∈ Deck(Y/X)` is biholomorphic and acts on the meromorphic functions on `Y` by `f ↦ f ∘ σ⁻¹`; this action fixes the
functions `π^*g`, and it is a homomorphism `Deck(Y/X) → Aut(𝓜(Y) / π^*𝓜(X))`.
Modelling: the action `σf = f ∘ σ⁻¹` takes meromorphic functions to meromorphic functions, and fixes `g ∘ π`
(`π ∘ σ = π`). -/
theorem para8_11 {n : ℕ} {π : Y → X} (hπ : IsHolomorphicCovering π n) :
    ∀ σ ∈ deck π, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) σ ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) σ.symm ∧
      (∀ f : Y → ℂ, (∀ y : Y, MeromorphicAt (f ∘ (chartAt ℂ y).symm) (chartAt ℂ y y)) →
        ∀ y : Y, MeromorphicAt ((f ∘ σ.symm) ∘ (chartAt ℂ y).symm) (chartAt ℂ y y)) ∧
      ∀ g : X → ℂ, (g ∘ π) ∘ σ.symm = g ∘ π := by
  sorry

/-- **Corollary 8.8** (Ch. 1 §8, F1:2071). Let `c₁, …, c_n` be holomorphic on an open neighbourhood `U` of `x` such that
the polynomial `Tⁿ + c₁(x)Tⁿ⁻¹ + … + c_n(x)` has `n` distinct zeros `w_ν`. Then, near `x`, the polynomial
`Tⁿ + c₁Tⁿ⁻¹ + … + c_n ∈ 𝒪_x[T]` factors as `∏ (T − φ_ν)` with holomorphic `φ_ν`, `φ_ν(x) = w_ν`.
Modelling: germs at `x` are represented by functions on an open neighbourhood. -/
theorem cor8_8 {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) {n : ℕ} {c : Fin n → X → ℂ}
    (hc : ∀ ν, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (c ν) U) {w : Fin n → ℂ} (hw : Function.Injective w)
    (hroots : Polynomial.X ^ n + ∑ ν : Fin n, Polynomial.C (c ν x) * Polynomial.X ^ (n - 1 - (ν : ℕ)) =
      ∏ ν : Fin n, (Polynomial.X - Polynomial.C (w ν))) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ φ : Fin n → X → ℂ, (∀ ν, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (φ ν) V) ∧
      (∀ ν, φ ν x = w ν) ∧ ∀ y ∈ V, Polynomial.X ^ n + ∑ ν : Fin n, Polynomial.C (c ν y) *
        Polynomial.X ^ (n - 1 - (ν : ℕ)) = ∏ ν : Fin n, (Polynomial.X - Polynomial.C (φ ν y)) := by
  sorry

/-- **Theorem 8.9(a)** (Ch. 1 §8, F1:2089). Let `P(T) = Tⁿ + c₁Tⁿ⁻¹ + … + c_n ∈ 𝓜(X)[T]` be a monic irreducible polynomial.
Then there are a Riemann surface `Y`, an `n`-sheeted branched holomorphic covering `π : Y → X` and `F ∈ 𝓜(Y)` with
`(π^*P)(F) = 0`. -/
theorem thm8_9_a (P : Polynomial (meroFun X)) (hm : P.Monic) (hi : Irreducible P) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : T2Space Y) (_ : ConnectedSpace Y) (_ : ChartedSpace ℂ Y)
      (_ : IsManifold 𝓘(ℂ) ω Y) (π : Y → X) (hπ : Tendsto π (Filter.codiscrete Y) (Filter.codiscrete X))
      (F : meroFun Y), IsAlgebraicFunctionOf P π hπ F := by
  sorry

/-- **Theorem 8.9(b)** (Ch. 1 §8, F1:2089). The algebraic function defined by `P` (monic and irreducible, as in 8.9(a);
the hypotheses are repeated here, the printed statement being a continuation of (a): without them the uniqueness is false,
e.g. `P = T(T − 1)` with `F = 0`, `G = 1`) is unique: for two triples `(Y, π, F)`,
`(Z, τ, G)` defined by `P` there is exactly one fibre-preserving biholomorphic map `σ : Z → Y` with `G = σ^*F`. -/
theorem thm8_9_b (P : Polynomial (meroFun X)) (hm : P.Monic) (hi : Irreducible P) {π : Y → X} {hπ : Tendsto π (Filter.codiscrete Y) (Filter.codiscrete X)}
    {F : meroFun Y} (hF : IsAlgebraicFunctionOf P π hπ F) {τ : Z → X}
    {hτ : Tendsto τ (Filter.codiscrete Z) (Filter.codiscrete X)} {G : meroFun Z} (hG : IsAlgebraicFunctionOf P τ hτ G) :
    ∃! σ : Z → Y, LiZhongQC.IsBiholomorphic σ ∧ (π ∘ σ) = τ ∧
      ∃ hσ : Tendsto σ (Filter.codiscrete Z) (Filter.codiscrete Y), G.1 = F.1.compTendsto σ hσ := by
  sorry

/-- **Example 8.10(a)** (the square root, Ch. 1 §8, F1:2141). Let `f(z) = (z − a₁)⋯(z − a_n)` with distinct `a_j`. Then
`T² − f` is irreducible over `𝓜(ℙ¹)`, i.e. `f` is not the square of a meromorphic function on `ℙ¹`; and for every
algebraic function `(Y, π, F)` defined by it (`F² = f ∘ π`, `π` a 2-sheeted covering) there is exactly one point of `Y`
over each `a_j`.
Modelling: irreducibility of `T² − f` is stated as "`f` is not a square in `𝓜(ℙ¹)`" (equivalent for a quadratic); the
algebraic function is described by `F² = f ∘ π` (equality of germs on `Y`). -/
theorem example8_10_a {n : ℕ} (hn : 1 ≤ n) {a : Fin n → ℂ} (ha : Function.Injective a) :
    (¬ ∃ g : References.RiemannSphere → ℂ,
        (∀ x : References.RiemannSphere, MeromorphicAt (g ∘ (chartAt ℂ x).symm) (chartAt ℂ x x)) ∧
        ∀ᶠ x in Filter.codiscrete References.RiemannSphere,
          g x ^ 2 = OnePoint.elim (x : OnePoint ℂ) 0 (fun z => ∏ j, (z - a j))) ∧
    ∀ (Y : Type) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
      (π : Y → References.RiemannSphere) (F : Y → ℂ), IsHolomorphicCovering π 2 →
      (∀ y : Y, MeromorphicAt (F ∘ (chartAt ℂ y).symm) (chartAt ℂ y y)) →
      (∀ᶠ y in Filter.codiscrete Y, F y ^ 2 = OnePoint.elim ((π y : References.RiemannSphere) : OnePoint ℂ) 0
        (fun z => ∏ j, (z - a j))) →
      ∀ j, (π ⁻¹' {References.RiemannSphere.ofComplex (a j)}).ncard = 1 := by
  sorry

/-- **Example 8.10(b)** (Ch. 1 §8, F1:2141). In the situation of 8.10(a), the fibre of `π` over `∞` consists of one point if
`n` is odd and of two points if `n` is even. -/
theorem example8_10_b {n : ℕ} (hn : 1 ≤ n) {a : Fin n → ℂ} (ha : Function.Injective a)
    (Y : Type) [TopologicalSpace Y] [T2Space Y] [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (π : Y → References.RiemannSphere) (F : Y → ℂ) (hπ : IsHolomorphicCovering π 2)
    (hF : ∀ y : Y, MeromorphicAt (F ∘ (chartAt ℂ y).symm) (chartAt ℂ y y))
    (hFf : ∀ᶠ y in Filter.codiscrete Y, F y ^ 2 = OnePoint.elim ((π y : References.RiemannSphere) : OnePoint ℂ) 0
        (fun z => ∏ j, (z - a j))) :
    (π ⁻¹' {References.RiemannSphere.infty}).ncard = if Odd n then 1 else 2 := by
  sorry

/-- **Theorem 8.12(a)** (Ch. 1 §8, F1:2197). Let `K = 𝓜(X)`, `P ∈ K[T]` monic irreducible of degree `n`, `(Y, π, F)` the
algebraic function defined by `P` and `L = 𝓜(Y) ⊇ K` (via `π^*`). Then `L : K` has degree `n` and `L ≅ K[T]/(P(T))`. -/
theorem thm8_12_a {P : Polynomial (meroFun X)} (hm : P.Monic) (hi : Irreducible P) {π : Y → X}
    {hπ : Tendsto π (Filter.codiscrete Y) (Filter.codiscrete X)} {F : meroFun Y}
    (hF : IsAlgebraicFunctionOf P π hπ F) :
    ∃ hmem : ∀ G : meroFun X, meroPullback π hπ G ∈ meroFun Y,
      letI := (meroPullbackHom π hπ hmem).toAlgebra
      Module.finrank (meroFun X) (meroFun Y) = P.natDegree ∧ Nonempty (AdjoinRoot P ≃ₐ[meroFun X] meroFun Y) := by
  sorry

/-- **Theorem 8.12(b)** (Ch. 1 §8, F1:2197). In the situation of 8.12(a), `σ ↦ (f ↦ f ∘ σ⁻¹)` is an isomorphism of the
group of covering transformations `Deck(Y/X)` onto the Galois group `Aut(L/K)`. -/
theorem thm8_12_b {P : Polynomial (meroFun X)} (hm : P.Monic) (hi : Irreducible P) {π : Y → X}
    {hπ : Tendsto π (Filter.codiscrete Y) (Filter.codiscrete X)} {F : meroFun Y}
    (hF : IsAlgebraicFunctionOf P π hπ F) :
    ∃ hmem : ∀ G : meroFun X, meroPullback π hπ G ∈ meroFun Y,
      letI := (meroPullbackHom π hπ hmem).toAlgebra
      Nonempty (deck π ≃* (meroFun Y ≃ₐ[meroFun X] meroFun Y)) := by
  sorry

/-- **Theorem 8.12(c)** (Ch. 1 §8, F1:2197). In the situation of 8.12(a), the covering `π : Y → X` is Galois iff the
extension `L : K` is Galois.
Modelling: `L : K` Galois is `Nat.card (L ≃ₐ[K] L) = Module.finrank K L` (equivalent for finite extensions of fields). -/
theorem thm8_12_c {P : Polynomial (meroFun X)} (hm : P.Monic) (hi : Irreducible P) {π : Y → X}
    {hπ : Tendsto π (Filter.codiscrete Y) (Filter.codiscrete X)} {F : meroFun Y}
    (hF : IsAlgebraicFunctionOf P π hπ F) :
    ∃ hmem : ∀ G : meroFun X, meroPullback π hπ G ∈ meroFun Y,
      letI := (meroPullbackHom π hπ hmem).toAlgebra
      (IsGaloisBranchedCovering π ↔
        Nat.card (meroFun Y ≃ₐ[meroFun X] meroFun Y) = Module.finrank (meroFun X) (meroFun Y)) := by
  sorry

end Surfaces

/-- **Lemma 8.7** (Ch. 1 §8, F1:2027). Let `c₁, …, c_n` be holomorphic on the disc `D(R)` and let `w₀` be a simple zero of
`Tⁿ + c₁(0)Tⁿ⁻¹ + … + c_n(0)`. Then there are `0 < r ≤ R` and a holomorphic `φ` on `D(r)` with `φ(0) = w₀` and
`φⁿ + c₁φⁿ⁻¹ + … + c_n = 0` on `D(r)`.
Modelling: "simple zero" is a root at which the derivative of the polynomial does not vanish. -/
theorem lemma8_7 {n : ℕ} {R : ℝ} (hR : 0 < R) {c : Fin n → ℂ → ℂ}
    (hc : ∀ ν, DifferentiableOn ℂ (c ν) (Metric.ball 0 R)) {w₀ : ℂ}
    (hroot : (Polynomial.X ^ n + ∑ ν : Fin n, Polynomial.C (c ν 0) * Polynomial.X ^ (n - 1 - (ν : ℕ))).IsRoot w₀)
    (hsimple : (Polynomial.derivative (Polynomial.X ^ n + ∑ ν : Fin n, Polynomial.C (c ν 0) *
      Polynomial.X ^ (n - 1 - (ν : ℕ)))).eval w₀ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r ≤ R ∧ ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ φ 0 = w₀ ∧
      ∀ z ∈ Metric.ball (0 : ℂ) r, φ z ^ n + ∑ ν : Fin n, c ν z * φ z ^ (n - 1 - (ν : ℕ)) = 0 := by
  sorry

/-- **The field `ℂ{{z}}` of convergent Laurent series with finite principal part** (8.13, Ch. 1 §8, F1:2217): the germs at
`0` (along the punctured neighbourhood filter) of functions meromorphic at `0`.
Modelling: Forster identifies `ℂ{{z}}` with the stalk `𝓜₀` of meromorphic germs (F1:2223); here a subalgebra of the germs
of complex functions along `𝓝[≠] 0`. -/
def convLaurent : Subalgebra ℂ ((𝓝[≠] (0 : ℂ)).Germ ℂ) where
  carrier := {g | ∃ f : ℂ → ℂ, (f : (𝓝[≠] (0 : ℂ)).Germ ℂ) = g ∧ MeromorphicAt f 0}
  mul_mem' := by
    rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨f * g, rfl, hf.mul hg⟩
  add_mem' := by
    rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨f + g, rfl, hf.add hg⟩
  algebraMap_mem' := fun c => ⟨fun _ => c, by
    show (((fun _ => c : ℂ → ℂ)) : (𝓝[≠] (0 : ℂ)).Germ ℂ) = c • (((1 : ℂ → ℂ)) : (𝓝[≠] (0 : ℂ)).Germ ℂ)
    show _ = (((c • (1 : ℂ → ℂ)) : ℂ → ℂ) : (𝓝[≠] (0 : ℂ)).Germ ℂ)
    congr 1
    funext x
    simp, MeromorphicAt.const c _⟩

/-- **Theorem 8.14** (Puiseux, Ch. 1 §8, F1:2263). Let `F(z, w) = wⁿ + a₁(z)wⁿ⁻¹ + … + a_n(z)` be an irreducible
polynomial of degree `n` in `w` with coefficients `a_j ∈ ℂ{{z}}` (meromorphic at `0`). Then there is a Laurent series
`φ(ζ) = Σ_{ν ≥ k} c_ν ζ^ν ∈ ℂ{{ζ}}` (a function meromorphic at `0`) with `F(ζⁿ, φ(ζ)) = 0` near `0`.
Modelling: the coefficients are given by representatives `a j` meromorphic at `0`; irreducibility is that of the
polynomial over `ℂ{{z}}` (`convLaurent`); the identity `F(ζⁿ, φ(ζ)) = 0` holds on a punctured neighbourhood of `0`. -/
theorem thm8_14 {n : ℕ} (hn : 1 ≤ n) (a : Fin n → ℂ → ℂ) (ha : ∀ j, MeromorphicAt (a j) 0)
    (hirr : Irreducible (Polynomial.X ^ n + ∑ j : Fin n,
      Polynomial.C (⟨(a j : (𝓝[≠] (0 : ℂ)).Germ ℂ), a j, rfl, ha j⟩ : convLaurent) *
        Polynomial.X ^ (n - 1 - (j : ℕ)))) :
    ∃ φ : ℂ → ℂ, MeromorphicAt φ 0 ∧ ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      φ ζ ^ n + ∑ j : Fin n, a j (ζ ^ n) * φ ζ ^ (n - 1 - (j : ℕ)) = 0 := by
  sorry

end Forster1981
