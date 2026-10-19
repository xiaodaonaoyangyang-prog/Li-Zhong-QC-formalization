import References.Lehto1987.Ch02.S05_FunctionsUnivalentInADisc
import LiZhongQC.Ch10.S33_BersEmbedding

/-!
# Lehto, Chapter III §1: Models of the universal Teichmüller space

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. III §1 (`full.md`
P1:3576–3755).

Conventions of Chapter III, as modelled here (INVENTORY Part B, decisions B0.1–B0.3). The model is the project's
(Li Zhong §21, §33):
- A Beltrami coefficient `μ ∈ B` is `LiZhongQC.BeltramiH`, a coefficient on the plane with `‖μ‖∞ < 1` vanishing in
  the closed lower half-plane, i.e. a coefficient on `H`, extended by `0`.
- `f^μ` is the normalized quasiconformal self-map of `H` with complex dilatation `μ`. It is read through its
  reflection-symmetric extension to the plane, `LiZhongQC.fMuSym`, which fixes `0, 1, ∞` and is real on `ℝ`.
- `f_μ` is the quasiconformal map of the plane with dilatation `μ`, fixing `0, 1, ∞`: `LiZhongQC.normalizedSolution`.
  It is conformal in the lower half-plane `H′ = LiZhongQC.lowerHalf`.
- The universal Teichmüller space `T` is `LiZhongQC.UniversalTeichmuller`, the classes of `B` under
  `f_μ|ℝ = f_ν|ℝ`. By `LiZhongQC.lemma33_1` this is the book's relation `f^μ|ℝ = f^ν|ℝ`.
- The origin is `LiZhongQC.UniversalTeichmuller.origin`.

Quasiconformal maps of plane sets are the project's `LiZhongQC.IsQuasiconformal`; their homeomorphic extensions to
the closure in `ℂ̄` are `LiZhongQC.IsHomeoExtension`. The normalized quasisymmetric functions are those of I.5.2
(`IsNormalizedQuasisymmetric`).

* Definition (the family `F` of normalized quasiconformal self-maps of `H`, §1.1) — `IsNormalizedQCSelfMapH`
* Definition (the ball `B` of complex dilatations, §1.1) — exists: `LiZhongQC.BeltramiH` (the Beltrami coefficients
  with norm less than 1 vanishing off the upper half-plane, decision B0.2)
* Definition (equivalence in `F`, §1.1) — `AreEquivalentF`
* Definition (universal Teichmüller space `T`, §1.1) — exists: `LiZhongQC.UniversalTeichmuller` (the classes of
  coefficients whose normalized solutions agree on the real axis, which is the book's relation by
  `LiZhongQC.lemma33_1`, decision B0.1)
* Definition (the class `X` of normalized quasisymmetric functions, §1.1) — `qsX`
* Formula (1.1) (§1.1) — `eq3_1_1`
* Theorem 1.1 (§1.1) — `thm3_1_1`
* Definition (the group operation (1.2) of `T`, §1.2) — `IsTProduct`
* Definition (the origin of `T`, §1.2) — exists: `LiZhongQC.UniversalTeichmuller.origin`
* Unlabelled (§1.2, P1:3608, 3618): (1.2) is a well-defined group law on `T` — `para3_1_2_a`
* Unlabelled (§1.2, P1:3618): `X` is a group under composition and (1.1) is a group isomorphism — `para3_1_2_b`
* Definition (the universal modular group `M`, §1.2) — `IsUniversalModular`
* Unlabelled (§1.2, P1:3628): `ω_[g]` is well defined and the transformations form a group — omitted: immediate
  (U−), not cited
* Definition (right translations `M_t`, §1.2) — `IsRightTranslation`
* Unlabelled (§1.2, P1:3644): `M_t` is transitive — omitted: immediate (U−)
* Definition (`f^μ`, `f_μ`, §1.3) — exists: `LiZhongQC.fMuSym`, `LiZhongQC.normalizedSolution`
* Theorem 1.2 (§1.3) — exists: `LiZhongQC.lemma33_1`, `LiZhongQC.fMu_lower_model` (jointly, decision B0.13: the
  first identifies the book's relation with agreement of the normalized solutions on the real axis, the second
  identifies that with agreement in the lower half-plane)
* Definition (the family `F*` and its equivalence, §1.3) — `IsNormalizedQCConformalLower`
* Unlabelled (§1.3, P1:3660–3668): real-analytic representatives `f_μ` — omitted: immediate from Theorem 1.1 (U−)
* Definition (sewing problem, normalized pair of solutions, §1.4) — `IsSewingSolution`
* Lemma 1.1 (§1.4, Pfluger) — `lemma3_1_1`
* Unlabelled (§1.4, P1:3696): the solutions map onto quasidiscs — omitted: a remark (U−)
* Definition (normalized quasidisc, the class `Δ`, §1.5) — `IsNormalizedQuasidisc`
* Formula (1.3) (§1.5) — `eq3_1_3`
* Theorem 1.3 (§1.5, Gardiner) — `thm3_1_3`
* Definition (the distance `q` on `Δ`, §1.5) — `qDistDelta`
* Unlabelled (§1.5, P1:3752): `q` is a metric — omitted: "easy to check" (U−)
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt upperHalf lowerHalf BeltramiH UniversalTeichmuller teichSetoid fMuSym
  normalizedSolution IsHomeoExtension IsMobius schwarzian)
open References (IsQuasidiskExt)
open LehtoVirtanen1973 (IsHomeoOn IsSensePreservingOn)
open Gehring1978 (hypNorm)

/-! ## §1.1 Equivalent quasiconformal mappings -/

/-- **Definition** (the family `F`, Ch. III §1.1). The quasiconformal self-maps `f` of the upper half-plane `H`
whose homeomorphic extension to the closure of `H` in `ℂ̄` keeps the boundary points `0`, `1` and `∞` fixed. -/
def IsNormalizedQCSelfMapH (f : ℂ → ℂ) : Prop :=
  LiZhongQC.IsQuasiconformal f upperHalf ∧ f '' upperHalf = upperHalf ∧
    ∃ F : ExtPlane → ExtPlane, IsHomeoExtension f upperHalf upperHalf F ∧ F extInf = extInf ∧
      F ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧ F ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)

/-- **Definition** (equivalence in `F`, Ch. III §1.1). Two mappings of `F` are equivalent if they agree on the real
axis (their homeomorphic extensions to the closure of `H` do; the extensions are unique). -/
def AreEquivalentF (f g : ℂ → ℂ) : Prop :=
  ∃ F G : ExtPlane → ExtPlane, IsHomeoExtension f upperHalf upperHalf F ∧ IsHomeoExtension g upperHalf upperHalf G ∧
    ∀ x : ℝ, F ((x : ℂ) : ExtPlane) = G ((x : ℂ) : ExtPlane)

/-- **Definition** (the class `X`, Ch. III §1.1): the normalized quasisymmetric functions (I.5.2). -/
def qsX : Set (ℝ → ℝ) := {h | ∃ k : ℝ, IsNormalizedQuasisymmetric h k}

/-- **Formula (1.1)** (Ch. III §1.1). `[f] ↦ f|ℝ` is a well-defined bijective mapping of `T` onto `X`.
Modelling: in the project's model `[μ] ↦ f^μ|ℝ`: a map `Φ : T → (ℝ → ℝ)` whose value at `[μ]` is `f^μ` on the real
axis (so `f^μ` is real there and the map is well defined), bijective onto `X`. -/
theorem eq3_1_1 :
    ∃ Φ : UniversalTeichmuller → ℝ → ℝ, (∀ (μ : BeltramiH) (x : ℝ),
      ((Φ (Quotient.mk teichSetoid μ) x : ℝ) : ℂ) = fMuSym μ.1 x) ∧ BijOn Φ univ qsX := by
  sorry

/-- **Theorem 1.1** (Ch. III §1.1). Every point of the universal Teichmüller space can be represented by a real
analytic quasiconformal mapping `f ∈ F` or by a real analytic complex dilatation `μ ∈ B`.
Modelling: one representative `μ` does both: `μ` and `f^μ` are real analytic in `H`. -/
theorem thm3_1_1 (p : UniversalTeichmuller) :
    ∃ μ : BeltramiH, Quotient.mk teichSetoid μ = p ∧ AnalyticOnNhd ℝ μ.1 upperHalf ∧
      AnalyticOnNhd ℝ (fMuSym μ.1) upperHalf := by
  sorry

/-! ## §1.2 Group structures -/

/-- **Definition** (the group operation (1.2) of `T`, Ch. III §1.2). `[f] ∘ [g] = [f ∘ g]`: the class `r` is the
product of `p` and `q` when `f^λ = f^μ ∘ f^ν` on the real axis for representatives `μ, ν, λ` of `p, q, r`
(equivalence is agreement on the real axis). -/
def IsTProduct (p q r : UniversalTeichmuller) : Prop :=
  ∃ μ ν lam : BeltramiH, Quotient.mk teichSetoid μ = p ∧ Quotient.mk teichSetoid ν = q ∧
    Quotient.mk teichSetoid lam = r ∧ ∀ x : ℝ, fMuSym lam.1 x = fMuSym μ.1 (fMuSym ν.1 x)

/-- **Unlabelled** (Ch. III §1.2, P1:3608, 3618). `T` inherits the group structure of `F`: (1.2) defines a
single-valued group operation, with neutral element the origin. -/
theorem para3_1_2_a :
    ∃ mul : UniversalTeichmuller → UniversalTeichmuller → UniversalTeichmuller,
      (∀ p q, IsTProduct p q (mul p q)) ∧ (∀ p q r, IsTProduct p q r → r = mul p q) ∧
      (∀ p, mul UniversalTeichmuller.origin p = p ∧ mul p UniversalTeichmuller.origin = p) ∧
      (∀ p q s, mul (mul p q) s = mul p (mul q s)) ∧
      ∀ p, ∃ q, mul p q = UniversalTeichmuller.origin ∧ mul q p = UniversalTeichmuller.origin := by
  sorry

/-- **Unlabelled** (Ch. III §1.2, P1:3618). Normalized quasisymmetric functions form a group under composition, and
the mapping (1.1) is an isomorphism between the groups `T` and `X`.
Modelling: `X` is closed under composition and inversion; for the map `Φ` of (1.1) (`eq3_1_1`), `r` is the product of
`p` and `q` exactly when `Φ r = Φ p ∘ Φ q`. -/
theorem para3_1_2_b :
    (∀ h₁ ∈ qsX, ∀ h₂ ∈ qsX, h₁ ∘ h₂ ∈ qsX) ∧ (∀ h ∈ qsX, ∃ g ∈ qsX, g ∘ h = id ∧ h ∘ g = id) ∧
    ∀ Φ : UniversalTeichmuller → ℝ → ℝ, (∀ (μ : BeltramiH) (x : ℝ),
      ((Φ (Quotient.mk teichSetoid μ) x : ℝ) : ℂ) = fMuSym μ.1 x) →
      ∀ p q r, IsTProduct p q r ↔ Φ r = Φ p ∘ Φ q := by
  sorry

/-- **Definition** (the universal modular group `M`, Ch. III §1.2). `ω = ω_[g] : T → T`,
`ω([f]) = [h ∘ f ∘ g⁻¹]`, for a quasiconformal self-map `g` of `H` (not necessarily normalized) and the Möbius
self-map `h` of `H` which normalizes `h ∘ f ∘ g⁻¹`.
Modelling: `ω` is such a transformation for some `g`: `ω([μ]) = [λ]` exactly when, on the real axis (the boundary of
`H` in `ℂ̄`, through the homeomorphic extensions `G` of `g` and `f^μ`, `f^λ`), `f^λ = h ∘ f^μ ∘ G⁻¹` for a Möbius
transformation `h` (necessarily the normalizing one). -/
def IsUniversalModular (ω : UniversalTeichmuller → UniversalTeichmuller) : Prop :=
  ∃ (g : ℂ → ℂ) (G : ExtPlane → ExtPlane), LiZhongQC.IsQuasiconformal g upperHalf ∧ g '' upperHalf = upperHalf ∧
    IsHomeoExtension g upperHalf upperHalf G ∧ ∀ μ lam : BeltramiH,
      (ω (Quotient.mk teichSetoid μ) = Quotient.mk teichSetoid lam ↔ ∃ M : ExtPlane → ExtPlane, IsMobius M ∧
        ∀ x : ℝ, OnePoint.map (fMuSym lam.1) ((x : ℂ) : ExtPlane) =
          M (OnePoint.map (fMuSym μ.1) (Function.invFunOn G (closure (toExt upperHalf)) ((x : ℂ) : ExtPlane))))

/-- **Definition** (the right translations, the subgroup `M_t`, Ch. III §1.2): `ω_[g]([f]) = [f ∘ g⁻¹]` for `g ∈ F`.
Modelling: `g = f^ν`; `ω([μ]) = [λ]` exactly when `f^λ ∘ f^ν = f^μ` on the real axis. -/
def IsRightTranslation (ω : UniversalTeichmuller → UniversalTeichmuller) : Prop :=
  ∃ ν : BeltramiH, ∀ μ lam : BeltramiH,
    ω (Quotient.mk teichSetoid μ) = Quotient.mk teichSetoid lam ↔ ∀ x : ℝ, fMuSym lam.1 (fMuSym ν.1 x) = fMuSym μ.1 x

/-! ## §1.3 Normalized conformal mappings -/

/-- **Definition** (the family `F*`, Ch. III §1.3): the quasiconformal mappings of the plane which fix `0`, `1`, `∞`
and are conformal in the lower half-plane `H′`. (Two of them are equivalent if they agree in `H′`.) -/
def IsNormalizedQCConformalLower (f : ℂ → ℂ) : Prop :=
  LiZhongQC.IsQuasiconformal f univ ∧ f '' univ = univ ∧ f 0 = 0 ∧ f 1 = 1 ∧ DifferentiableOn ℂ f lowerHalf

/-! ## §1.4 Sewing problem -/

/-- **Definition** (normalized solution of the sewing problem, Ch. III §1.4). Let `h` be a strictly increasing
continuous function of the real axis onto itself. `f₁` and `f₂` map the upper and the lower half-plane conformally onto
complementary Jordan domains, `f₁⁻¹ ∘ f₂ = h` on the real axis, and the pair is normalized: `f₁` and `f₂` fix `0`, `1`
and `∞`. [correction: the normalization is on the boundary values `F₁`, `F₂`; reading `f₁ 0`, a value outside the domain, left the
uniqueness of Lemma 1.1 false (`2 f₁`, `2 f₂` is another solution)]
Modelling: the boundary values are those of the homeomorphic extensions `F₁`, `F₂` to the closures in `ℂ̄`;
`f₁⁻¹ ∘ f₂ = h` is written `F₂ = F₁ ∘ h` on `ℝ`. -/
def IsSewingSolution (h : ℝ → ℝ) (f₁ f₂ : ℂ → ℂ) : Prop :=
  LiZhongQC.IsConformalOnto f₁ upperHalf (f₁ '' upperHalf) ∧ LiZhongQC.IsConformalOnto f₂ lowerHalf (f₂ '' lowerHalf) ∧
    (∃ C : Set ExtPlane, LiZhongQC.AreComplementaryComponents C (toExt (f₁ '' upperHalf)) (toExt (f₂ '' lowerHalf))) ∧
    ∃ F₁ F₂ : ExtPlane → ExtPlane, IsHomeoExtension f₁ upperHalf (f₁ '' upperHalf) F₁ ∧
      IsHomeoExtension f₂ lowerHalf (f₂ '' lowerHalf) F₂ ∧
      (∀ x : ℝ, F₂ ((x : ℂ) : ExtPlane) = F₁ (((h x : ℝ) : ℂ) : ExtPlane)) ∧
      F₁ extInf = extInf ∧ F₂ extInf = extInf ∧
      F₁ ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧ F₁ ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧
      F₂ ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧ F₂ ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane)

/-- **Lemma 1.1** (Ch. III §1.4, Pfluger). Let `h` be a normalized quasisymmetric function. Then the sewing problem
has a unique normalized pair of solutions.
Modelling: uniqueness of `f₁` in `H` and of `f₂` in `H′`. -/
theorem lemma3_1_1 {h : ℝ → ℝ} (hh : h ∈ qsX) :
    ∃ f₁ f₂ : ℂ → ℂ, IsSewingSolution h f₁ f₂ ∧ ∀ g₁ g₂ : ℂ → ℂ, IsSewingSolution h g₁ g₂ →
      EqOn g₁ f₁ upperHalf ∧ EqOn g₂ f₂ lowerHalf := by
  sorry

/-! ## §1.5 Normalized quasidiscs -/

/-- **Definition** (normalized quasidisc, the class `Δ`, Ch. III §1.5). A quasidisc whose boundary passes through
`0`, `1`, `∞` and is so oriented that the direction from `0` to `1` to `∞` to `0` is negative with respect to the
domain.
Modelling: the orientation condition says that the quasidisc is the image of the lower half-plane `H′` (for which
`0 → 1 → ∞` is the negative direction) under a sense-preserving homeomorphism of `ℂ̄` fixing `0`, `1`, `∞`. -/
def IsNormalizedQuasidisc (A : Set ExtPlane) : Prop :=
  IsQuasidiskExt A ∧ ∃ F : ExtPlane → ExtPlane, IsSensePreservingOn F univ ∧ F '' univ = univ ∧
    F ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧ F ((1 : ℂ) : ExtPlane) = ((1 : ℂ) : ExtPlane) ∧
    F extInf = extInf ∧ F '' toExt lowerHalf = A

/-- **Formula (1.3)** (Ch. III §1.5). For `f ∈ F*`, `[f] ↦ f(H′)` is a bijective mapping of `T` onto `Δ`.
Modelling: in the project's model `[μ] ↦ f_μ(H′)` (`f_μ ∈ F*`), as a map `T → Set ℂ̄`, bijective onto `Δ`. -/
theorem eq3_1_3 :
    ∃ Ψ : UniversalTeichmuller → Set ExtPlane,
      (∀ μ : BeltramiH, Ψ (Quotient.mk teichSetoid μ) = toExt (normalizedSolution μ.1 '' lowerHalf)) ∧
      BijOn Ψ univ {A | IsNormalizedQuasidisc A} := by
  sorry

/-- **Theorem 1.3** (Ch. III §1.5, Gardiner). Two points `[f^μ]`, `[f^ν] ∈ T` are inverse elements of the group `T` if
and only if the quasidiscs `f_μ(H)` and `f_ν(H′)` are mirror images with respect to the real axis.
Modelling: inverse elements: the product (1.2) of the two points is the origin. -/
theorem thm3_1_3 (μ ν : BeltramiH) :
    IsTProduct (Quotient.mk teichSetoid μ) (Quotient.mk teichSetoid ν) UniversalTeichmuller.origin ↔
      normalizedSolution ν.1 '' lowerHalf = conj '' (normalizedSolution μ.1 '' upperHalf) := by
  sorry

/-- **Definition** (the distance `q` of normalized quasidiscs, Ch. III §1.5):
`q(f(H′), g(H′)) = ‖S_f − S_g‖_{H′}` for `f, g ∈ F*`.
Modelling: the infimum over the representing pairs (all give the same value, `f|H′` being determined by `f(H′)`);
`[0, ∞]`-valued, Lehto's norm (`Gehring1978.hypNorm`). -/
def qDistDelta (A B : Set ExtPlane) : ℝ≥0∞ :=
  ⨅ (f : ℂ → ℂ) (g : ℂ → ℂ) (_ : IsNormalizedQCConformalLower f ∧ IsNormalizedQCConformalLower g ∧
    toExt (f '' lowerHalf) = A ∧ toExt (g '' lowerHalf) = B),
    hypNorm (fun z => schwarzian f z - schwarzian g z) (toExt lowerHalf)

end Lehto1987
