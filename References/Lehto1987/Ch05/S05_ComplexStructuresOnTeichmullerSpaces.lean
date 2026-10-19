import References.Lehto1987.Ch05.S04_TeichmullerSpaceAndSchwarzianDerivatives

/-!
# Lehto, Chapter V §5: Complex structures on Teichmüller spaces

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. V §5 (`full.md`
P2:496–733).

Conventions (see §3–§4; decision B0.10).
- **Abstract Banach spaces.** Holomorphy of maps between complex Banach spaces is Mathlib's `DifferentiableOn ℂ`
  (Fréchet derivative), and the dual is `StrongDual ℂ F`.
- **Concrete spaces.** The concrete Banach spaces of the section are spaces of functions `ℂ → ℂ` with a norm given as
  a function (`L^∞(G)` with `eLpNorm · ⊤`, `Q(G)` with Lehto's `Gehring1978.hypNorm` on `𝕃`), which carry no normed
  instance. For them the book's definition of the derivative is written out (`IsHolomorphicFn`). A biholomorphic map
  is a holomorphic bijection with holomorphic inverse.
- **Charts.** The charts of `T_S` go into the different spaces `Q(G^μ)`; the book's atlas (5.6)–(5.8) is described
  relationally: a chart `h_μ` is a map `T_S → (ℂ → ℂ)` given on representatives (`IsBersChart`), with domain
  `V_μ = {p | ‖h_μ(p)‖ < 2}`.
- **Groups.** `G^μ` is given with the relations of `LiZhongQC.exists_deformation_group`
  (`f^μ ∘ g = g′ ∘ f^μ`, `IsDeformationGroup`).

- **Known gap** (audit AUDIT2_Lehto, left as documented). `IsFnBanachAtlas` does not require the chart images `h_i(V_i)` to be open
  in the model Banach space `Q(G^μ)` (the book's `B(0, 2) ∩ Q(G^μ)`), so `thm5_5_2` is weaker than "complex analytic structure".

* Definition (derivative and holomorphic maps of Banach spaces, §5.1) — exists: `DifferentiableOn`, `fderiv` (over ℂ)
* Definition (biholomorphic map, §5.1) — `IsBiholomorphicBanach`
* Definition (dual space, §5.1) — exists: `StrongDual`
* Definition (total set, §5.1) — `IsTotalSet`
* Lemma 5.1 (§5.1) — `lemma5_5_1` [corrected: (i) needs continuity, see the root Corrections]
* Definition (complex Banach manifold, complex analytic structure, §5.2) — `IsFnBanachAtlas`
* Unlabelled (§5.2, P2:536–546): history; the structure inherited from `ℂ^{3p−3}` is not natural — omitted: remarks
* Definition (the space `L^∞(G)`, the ball `B(G)`, §5.3) — `LinfG`; exists: `LiZhongQC.BeltramiGamma` (the ball)
* Definition (holomorphic maps between spaces of functions, §5.1 applied in §5.3) — `IsHolomorphicFn`
* Theorem 5.1 (§5.3) — `thm5_5_1`
* Formula (5.1) (§5.3) — `thm5_5_1` (the map Λ)
* Formula (5.2) (§5.3) — omitted: a step of the proof of Theorem 5.1
* Formula (5.3) (§5.4) — `alphaTilde` (its explicit form, §4.6)
* Unlabelled (§5.4, P2:589–592): `α̃_μ` maps `B(G)` biholomorphically onto `B(G^μ)` — `para5_5_4_a`
* Formula (5.4) (§5.4) — `thm5_5_1` (Λ_μ is the map of Theorem 5.1 for `G^μ`)
* Formula (5.5) (§5.4) — `sigmaSection`
* Unlabelled (§5.4, P2:604–610): `σ_μ` is a holomorphic section of `Λ_μ` in `B_μ(0, 2)` — `para5_5_4_b`
* Formula (5.6) (§5.4) — `IsBersChart` (the domains V_μ)
* Formula (5.7) (§5.4) — `IsBersChart` (the charts h_μ)
* Unlabelled (§5.4, P2:620–626): the `V_μ` cover `T_S` and `h_μ` is a homeomorphism of `T_S` onto `T(G^μ)` —
  `para5_5_4_c`
* Theorem 5.2 (§5.5) — `thm5_5_2`
* Formula (5.8) (§5.5) — `thm5_5_2` (the atlas)
* Theorem 5.3 (§5.5) — `thm5_5_3`
* Formula (5.9) (§5.5) — `thm5_5_3` (the local sections)
* Theorem 5.4 (§5.5) — `thm5_5_4`
* Theorem 5.5 (§5.6) — `thm5_5_5`
* Formula (5.10) (§5.6) — omitted: a step of the proof of Theorem 5.5
* Theorem 5.6 (§5.6) — `thm5_5_6`
* Unlabelled (§5.6, P2:730–732): the abstract space `T_p` and `ℂ^{3p−3}` — omitted: notation and remarks

Helpers (not book notions): `IsDeformationGroup` (the Fuchsian group `G^μ` of `μ`) and `bersDomainV` (the chart
domain `V_μ`).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace Lehto1987

universe u

open LiZhongQC (toExt upperHalf lowerHalf IsFuchsian ActsFreely BeltramiH BeltramiGamma TeichGamma teichSetoidGamma
  teichDistanceGamma fMuSym automorphicQD bersFunction bersMapGamma bersImage mobiusFn IsGammaCompatible)
open Gehring1978 (hypNorm)

/-! ## §5.1 Holomorphic functions in Banach spaces -/

/-- **Definition** (biholomorphic map, Ch. V §5.1): a holomorphic map of an open set `U` onto `f(U)` with a holomorphic
inverse. -/
def IsBiholomorphicBanach {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (f : E → F) (U : Set E) : Prop :=
  IsOpen U ∧ IsOpen (f '' U) ∧ DifferentiableOn ℂ f U ∧ InjOn f U ∧
    ∃ g : F → E, DifferentiableOn ℂ g (f '' U) ∧ ∀ x ∈ U, g (f x) = x

/-- **Definition** (total set of the dual, Ch. V §5.1): `A ⊂ F*` is total if `α(x) = 0` for every `α ∈ A` implies
`x = 0`. -/
def IsTotalSet {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] (A : Set (StrongDual ℂ F)) : Prop :=
  ∀ x : F, (∀ α ∈ A, α x = 0) → x = 0

/-- **Lemma 5.1** (Ch. V §5.1, Bourbaki). A function `f : U → F` is holomorphic if and only if (i) it is continuous and
for every `x ∈ U` and `e ∈ E` the function `w ↦ f(x + we)` is holomorphic near the origin; if and only if (ii) it is
continuous and there is a total subset `A` of `F*` such that `α ∘ f` is holomorphic for every `α ∈ A`.
[misstatement, root Corrections] As printed, (i) omits the continuity of `f`; without it (i) fails in infinite
dimension (a discontinuous linear functional satisfies it); Bourbaki's condition is for continuous `f`. -/
theorem lemma5_5_1 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace E] [CompleteSpace F] {U : Set E} (hU : IsOpen U) (f : E → F) :
    (DifferentiableOn ℂ f U ↔ ContinuousOn f U ∧ ∀ x ∈ U, ∀ e : E,
      ∃ r > (0 : ℝ), DifferentiableOn ℂ (fun w : ℂ => f (x + w • e)) (Metric.ball 0 r)) ∧
    (DifferentiableOn ℂ f U ↔ ContinuousOn f U ∧ ∃ A : Set (StrongDual ℂ F), IsTotalSet A ∧
      ∀ α ∈ A, DifferentiableOn ℂ (fun x => α (f x)) U) := by
  sorry

/-! ## §5.2 Banach manifolds -/

/-- **Definition** (holomorphic map between spaces of functions, Ch. V §5.1, for the spaces of §5.3–§5.6): `f` is
holomorphic in `U` for the norms `nE`, `nF` if at every `x ∈ U` it has a derivative: a complex linear map `L`, bounded
for the norms, with `nF(f(x + h) − f(x) − L h) = o(nE(h))`. -/
def IsHolomorphicFn (nE nF : (ℂ → ℂ) → ℝ≥0∞) (U : Set (ℂ → ℂ)) (f : (ℂ → ℂ) → ℂ → ℂ) : Prop :=
  ∀ x ∈ U, ∃ L : (ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ), (∃ C : ℝ, ∀ h, nF (L h) ≤ ENNReal.ofReal C * nE h) ∧
    ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ h, nE h < ENNReal.ofReal δ → x + h ∈ U →
      nF (f (x + h) - f x - L h) ≤ ENNReal.ofReal ε * nE h

/-- **Definition** (complex Banach manifold, complex analytic structure, Ch. V §5.2): a space `M` with an atlas of
charts `(V_i, h_i)` into Banach spaces (here spaces of functions with norms `n_i`) whose parameter transformations are
biholomorphic (decision B0.10).
Modelling: each `h_i` is injective on the open set `V_i` (open in the topology given by a metric `d` of `M`), the `V_i`
cover `M`, `h_i` is a homeomorphism onto its image (`ε–δ` for `d` and `n_i`), and every change of charts
`h_j ∘ h_i⁻¹` is holomorphic on `h_i(V_i ∩ V_j)`. -/
def IsFnBanachAtlas {M ι : Type*} (d : M → M → ℝ) (n : ι → (ℂ → ℂ) → ℝ≥0∞) (V : ι → Set M)
    (h : ι → M → ℂ → ℂ) : Prop :=
  (∀ x : M, ∃ i, x ∈ V i) ∧ (∀ i, InjOn (h i) (V i)) ∧
    (∀ i, ∀ x ∈ V i, ∃ r > (0 : ℝ), ∀ y, d x y < r → y ∈ V i) ∧
    (∀ i, ∀ x ∈ V i, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ y ∈ V i, d x y < δ → n i (h i y - h i x) < ENNReal.ofReal ε) ∧
    (∀ i, ∀ x ∈ V i, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ y ∈ V i, n i (h i y - h i x) < ENNReal.ofReal δ → d x y < ε) ∧
    ∀ i j, ∃ g : (ℂ → ℂ) → ℂ → ℂ, IsHolomorphicFn (n i) (n j) (h i '' (V i ∩ V j)) g ∧
      ∀ x ∈ V i ∩ V j, g (h i x) = h j x

/-! ## §5.3 A holomorphic mapping between Banach spaces -/

/-- **Definition** (the space `L^∞(G)`, Ch. V §5.3): the bounded measurable `(−1, 1)`-differentials for `G`, as
functions on `ℍ` extended by `0`; its open unit ball is `B(G)` (`LiZhongQC.BeltramiGamma`). -/
def LinfG (Γ : Subgroup SL(2, ℝ)) : Set (ℂ → ℂ) :=
  {μ | AEStronglyMeasurable μ volume ∧ eLpNorm μ ⊤ volume < ⊤ ∧ (∀ z : ℂ, z.im ≤ 0 → μ z = 0) ∧
    IsGammaCompatible Γ μ}

/-- **Theorem 5.1** (Ch. V §5.3). The function `μ ↦ Λ(μ) = S_{f_μ|H}` (5.1), which maps the open unit ball `B(G)` of
`L^∞(G)` into `Q(G)`, is holomorphic.
Modelling: mirrored (`𝕃`); `B(G)` as the set of coefficients of `LiZhongQC.BeltramiGamma Γ`; norms `‖·‖∞` and Lehto's
`hypNorm` on `𝕃` (near miss: `LiZhongQC.lemma36_2_bers_analytic`, pointwise in `z`). -/
theorem thm5_5_1 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) :
    IsHolomorphicFn (fun μ => eLpNorm μ ⊤ volume) (fun φ => hypNorm φ (toExt lowerHalf))
      {μ | ∃ m : BeltramiGamma Γ, m.1.1 = μ} bersFunction := by
  sorry

/-! ## §5.4 An atlas on the Teichmüller space -/

/-- Helper. `Γμ` is the Fuchsian group `G^μ = {f^μ ∘ g ∘ (f^μ)⁻¹ | g ∈ G}` of `μ` (relations as in
`LiZhongQC.exists_deformation_group`). -/
def IsDeformationGroup (Γ Γμ : Subgroup SL(2, ℝ)) (μ : ℂ → ℂ) : Prop :=
  (∀ γ ∈ Γ, ∃ γ' ∈ Γμ, ∀ z ∈ upperHalf,
      fMuSym μ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ z)) ∧
    ∀ γ' ∈ Γμ, ∃ γ ∈ Γ, ∀ z ∈ upperHalf,
      fMuSym μ (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ z)

/-- **Unlabelled** (Ch. V §5.4, P2:589–592). For `μ ∈ B(G)`, `α̃_μ` (5.3) maps `B(G)` bijectively and
biholomorphically onto `B(G^μ)`.
**Correction** (Lehto-fix1, audit AUDIT2_Lehto finding 2): elements of `B(G)` are classes of coefficients modulo almost
everywhere equality, so bijectivity and `g ∘ α̃_μ = id` hold almost everywhere, not as equalities of functions (the pointwise
`BijOn` fails: changing `ν` at one point where `1 − μ̄ ν = 0` or `dz f^μ = 0` does not change `α̃_μ ν` in Lean, `x/0 = 0`, and
the value `1/μ̄` is never attained). Statement: `α̃_μ` maps `B(G)` into `B(G^μ)` and onto it, injectively, all up to null sets,
is holomorphic, and has a holomorphic left inverse `g` with `g (α̃_μ m) = m` a.e. -/
theorem para5_5_4_a {Γ Γμ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (μ : BeltramiGamma Γ)
    (hΓμ : IsDeformationGroup Γ Γμ μ.1.1) :
    (∀ m : BeltramiGamma Γ, ∃ m' : BeltramiGamma Γμ, ∀ᵐ z : ℂ, m'.1.1 z = alphaTilde μ.1.1 m.1.1 z) ∧
      (∀ m' : BeltramiGamma Γμ, ∃ m : BeltramiGamma Γ, ∀ᵐ z : ℂ, m'.1.1 z = alphaTilde μ.1.1 m.1.1 z) ∧
      (∀ m₁ m₂ : BeltramiGamma Γ, (∀ᵐ z : ℂ, alphaTilde μ.1.1 m₁.1.1 z = alphaTilde μ.1.1 m₂.1.1 z) →
        ∀ᵐ z : ℂ, m₁.1.1 z = m₂.1.1 z) ∧
      IsHolomorphicFn (fun ν => eLpNorm ν ⊤ volume) (fun ν => eLpNorm ν ⊤ volume)
        {ν | ∃ m : BeltramiGamma Γ, m.1.1 = ν} (alphaTilde μ.1.1) ∧
      ∃ g : (ℂ → ℂ) → ℂ → ℂ, IsHolomorphicFn (fun ν => eLpNorm ν ⊤ volume) (fun ν => eLpNorm ν ⊤ volume)
        {ν | ∃ m : BeltramiGamma Γμ, m.1.1 = ν} g ∧
        ∀ m : BeltramiGamma Γ, ∀ᵐ z : ℂ, g (alphaTilde μ.1.1 m.1.1) z = m.1.1 z := by
  sorry

/-- **Definition** (the section `σ_μ`, (5.5), Ch. V §5.4): `σ_μ(φ)(z̄) = −2y²φ(z)`, `z ∈ H`.
Modelling: mirrored (decision B0.2): `σ(φ)(z) = −2y²φ(z̄)` for `z = x + iy ∈ ℍ`, `φ` on `𝕃`; `0` off `ℍ`. -/
def sigmaSection (φ : ℂ → ℂ) : ℂ → ℂ := upperHalf.indicator fun z => -2 * ((z.im : ℂ) ^ 2) * φ (conj z)

/-- **Unlabelled** (Ch. V §5.4, P2:604–610). In the ball `B_μ(0, 2)` of `Q(G^μ)`, `σ_μ` is a holomorphic section of
`Λ_μ`: `σ(φ) ∈ B(G^μ)` and `Λ_μ(σ(φ)) = φ`. -/
theorem para5_5_4_b {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) :
    (∀ φ ∈ automorphicQD Γ, hypNorm φ (toExt lowerHalf) < 2 →
      ∃ m : BeltramiGamma Γ, m.1.1 = sigmaSection φ ∧ bersFunction (sigmaSection φ) = φ) ∧
    IsHolomorphicFn (fun φ => hypNorm φ (toExt lowerHalf)) (fun ν => eLpNorm ν ⊤ volume)
      {φ | φ ∈ automorphicQD Γ ∧ hypNorm φ (toExt lowerHalf) < 2} sigmaSection := by
  sorry

/-- **Definition** (the charts `h_μ = λ_μ ∘ α_μ`, (5.7), Ch. V §5.4): `h_μ([ν]) = S_{f_{α̃_μ(ν)}|H}`, the Bers
imbedding of `T_{S^μ}` after `α_μ`.
Modelling: relational, on representatives: `h` takes the value `Λ(ν′)` at `[ν]` whenever `ν′ = α̃_μ(ν)` a.e. -/
def IsBersChart {Γ : Subgroup SL(2, ℝ)} (μ : BeltramiGamma Γ) (h : TeichGamma Γ → ℂ → ℂ) : Prop :=
  ∀ (ν : BeltramiGamma Γ) (ν' : BeltramiH), (∀ᵐ z : ℂ, ν'.1 z = alphaTilde μ.1.1 ν.1.1 z) →
    h (Quotient.mk (teichSetoidGamma Γ) ν) = bersFunction ν'.1

/-- Helper. The domain `V_μ` (5.6) of the chart `h_μ`: the preimage of `B_μ(0, 2)`. -/
def bersDomainV {Γ : Subgroup SL(2, ℝ)} (h : TeichGamma Γ → ℂ → ℂ) : Set (TeichGamma Γ) :=
  {p | hypNorm (h p) (toExt lowerHalf) < 2}

/-- **Unlabelled** (Ch. V §5.4, P2:620–626). The domains `V_μ`, `μ ∈ B(G)`, form an open covering of `T_S`, and
`h_μ` is a homeomorphism of `T_S` onto `T(G^μ)`. -/
theorem para5_5_4_c {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (h : BeltramiGamma Γ → TeichGamma Γ → ℂ → ℂ) (hh : ∀ μ, IsBersChart μ (h μ)) :
    (∀ p : TeichGamma Γ, ∃ μ, p ∈ bersDomainV (h μ)) ∧
      ∀ μ : BeltramiGamma Γ, ∀ Γμ : Subgroup SL(2, ℝ), IsDeformationGroup Γ Γμ μ.1.1 →
        BijOn (h μ) univ (bersImage Γμ) ∧
        (∀ p, ∀ ε > 0, ∃ δ > 0, ∀ q, teichDistanceGamma p q < δ →
          hypNorm (h μ p - h μ q) (toExt lowerHalf) < ENNReal.ofReal ε) ∧
        ∀ p, ∀ ε > 0, ∃ δ > 0, ∀ q, hypNorm (h μ p - h μ q) (toExt lowerHalf) < ENNReal.ofReal δ →
          teichDistanceGamma p q < ε := by
  sorry

/-! ## §5.5 Complex analytic structure -/

/-- **Theorem 5.2** (Ch. V §5.5). The atlas `{(V_μ, h_μ) | μ ∈ B(G)}` (5.8) defines a complex analytic structure on
the Teichmüller space `T_S`. The Bers imbedding of `T_S` into `Q(G)` is holomorphic with respect to this structure.
Modelling: `IsFnBanachAtlas` for `τ_S` and Lehto's norm; the Bers imbedding in the charts is `λ ∘ h_μ⁻¹`. -/
theorem thm5_5_2 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (h : BeltramiGamma Γ → TeichGamma Γ → ℂ → ℂ) (hh : ∀ μ, IsBersChart μ (h μ)) :
    IsFnBanachAtlas teichDistanceGamma (fun _ => fun φ => hypNorm φ (toExt lowerHalf)) (fun μ => bersDomainV (h μ)) h ∧
      ∀ μ : BeltramiGamma Γ, ∃ g : (ℂ → ℂ) → ℂ → ℂ,
        IsHolomorphicFn (fun φ => hypNorm φ (toExt lowerHalf)) (fun φ => hypNorm φ (toExt lowerHalf))
          (h μ '' bersDomainV (h μ)) g ∧ ∀ p ∈ bersDomainV (h μ), g (h μ p) = bersMapGamma Γ p := by
  sorry

/-- **Theorem 5.3** (Ch. V §5.5). The canonical projection `π : B(G) → T_S` is holomorphic, and it has local
holomorphic sections everywhere in `T_S` (5.9).
Modelling: in the charts: `h_μ ∘ π` is holomorphic on `π⁻¹(V_μ)`, and there is a holomorphic `ψ_μ` on `h_μ(V_μ)`
with values in `B(G)` and `π ∘ ψ_μ ∘ h_μ = id` on `V_μ`. -/
theorem thm5_5_3 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (h : BeltramiGamma Γ → TeichGamma Γ → ℂ → ℂ) (hh : ∀ μ, IsBersChart μ (h μ)) (μ : BeltramiGamma Γ) :
    (∃ g : (ℂ → ℂ) → ℂ → ℂ,
      IsHolomorphicFn (fun ν => eLpNorm ν ⊤ volume) (fun φ => hypNorm φ (toExt lowerHalf))
        {ν | ∃ m : BeltramiGamma Γ, m.1.1 = ν ∧ Quotient.mk (teichSetoidGamma Γ) m ∈ bersDomainV (h μ)} g ∧
      ∀ m : BeltramiGamma Γ, Quotient.mk (teichSetoidGamma Γ) m ∈ bersDomainV (h μ) →
        g m.1.1 = h μ (Quotient.mk (teichSetoidGamma Γ) m)) ∧
    ∃ ψ : (ℂ → ℂ) → ℂ → ℂ,
      IsHolomorphicFn (fun φ => hypNorm φ (toExt lowerHalf)) (fun ν => eLpNorm ν ⊤ volume)
        (h μ '' bersDomainV (h μ)) ψ ∧
      ∀ p ∈ bersDomainV (h μ), ∃ m : BeltramiGamma Γ, m.1.1 = ψ (h μ p) ∧ Quotient.mk (teichSetoidGamma Γ) m = p := by
  sorry

/-- **Theorem 5.4** (Ch. V §5.5). The Bers imbedding `λ : T_S → T(G)` is biholomorphic.
Modelling: in the charts, `λ ∘ h_μ⁻¹` has a holomorphic inverse on `λ(V_μ)`. -/
theorem thm5_5_4 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (h : BeltramiGamma Γ → TeichGamma Γ → ℂ → ℂ) (hh : ∀ μ, IsBersChart μ (h μ)) (μ : BeltramiGamma Γ) :
    ∃ g g' : (ℂ → ℂ) → ℂ → ℂ,
      IsHolomorphicFn (fun φ => hypNorm φ (toExt lowerHalf)) (fun φ => hypNorm φ (toExt lowerHalf))
        (h μ '' bersDomainV (h μ)) g ∧
      IsHolomorphicFn (fun φ => hypNorm φ (toExt lowerHalf)) (fun φ => hypNorm φ (toExt lowerHalf))
        (bersMapGamma Γ '' bersDomainV (h μ)) g' ∧
      ∀ p ∈ bersDomainV (h μ), g (h μ p) = bersMapGamma Γ p ∧ g' (bersMapGamma Γ p) = h μ p := by
  sorry

/-! ## §5.6 Complex structure under quasiconformal mappings -/

/-- **Theorem 5.5** (Ch. V §5.6). Quasiconformally equivalent Riemann surfaces have isometrically and biholomorphically
isomorphic Teichmüller spaces.
Modelling: for `S = H′/G` and `S′ = H′/G′` with `G′ = G^μ` (the lift `f^μ` of a quasiconformal map): the map
`α_μ : T_S → T_{S′}` is an isometric bijection which is holomorphic in the charts of both spaces. -/
theorem thm5_5_5 {Γ Γ' : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hΓ' : IsFuchsian Γ')
    (hfree' : ActsFreely Γ') (μ : BeltramiGamma Γ) (hΓμ : IsDeformationGroup Γ Γ' μ.1.1)
    (h : BeltramiGamma Γ → TeichGamma Γ → ℂ → ℂ) (hh : ∀ ν, IsBersChart ν (h ν))
    (h' : BeltramiGamma Γ' → TeichGamma Γ' → ℂ → ℂ) (hh' : ∀ ν, IsBersChart ν (h' ν)) :
    ∃ α : TeichGamma Γ → TeichGamma Γ', Function.Bijective α ∧
      (∀ p q, teichDistanceGamma (α p) (α q) = teichDistanceGamma p q) ∧
      (∀ (ν : BeltramiGamma Γ) (ν' : BeltramiGamma Γ'), (∀ᵐ z : ℂ, ν'.1.1 z = alphaTilde μ.1.1 ν.1.1 z) →
        α (Quotient.mk (teichSetoidGamma Γ) ν) = Quotient.mk (teichSetoidGamma Γ') ν') ∧
      ∀ ν₁ ν₂, ∃ g : (ℂ → ℂ) → ℂ → ℂ,
        IsHolomorphicFn (fun φ => hypNorm φ (toExt lowerHalf)) (fun φ => hypNorm φ (toExt lowerHalf))
          (h ν₁ '' (bersDomainV (h ν₁) ∩ α ⁻¹' bersDomainV (h' ν₂))) g ∧
        ∀ p ∈ bersDomainV (h ν₁) ∩ α ⁻¹' bersDomainV (h' ν₂), g (h ν₁ p) = h' ν₂ (α p) := by
  sorry

/-- **Theorem 5.6** (Ch. V §5.6). The elements of the modular group `Mod(S)` are biholomorphic automorphisms of the
Teichmüller space `T_S`.
Modelling: an element of `Mod(S)` in the lifted model is the map `α_μ` of a lift `f^μ` of a quasiconformal
self-mapping of `S` (`G^μ = G`); it is holomorphic in the charts, and so is its inverse `β` (Lehto-fix1: the
inverse chart expressions were not stated before). -/
theorem thm5_5_6 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (μ : BeltramiGamma Γ)
    (hΓμ : IsDeformationGroup Γ Γ μ.1.1) (h : BeltramiGamma Γ → TeichGamma Γ → ℂ → ℂ)
    (hh : ∀ ν, IsBersChart ν (h ν)) {α : TeichGamma Γ → TeichGamma Γ}
    (hα : ∀ (ν ν' : BeltramiGamma Γ), (∀ᵐ z : ℂ, ν'.1.1 z = alphaTilde μ.1.1 ν.1.1 z) →
      α (Quotient.mk (teichSetoidGamma Γ) ν) = Quotient.mk (teichSetoidGamma Γ) ν') :
    Function.Bijective α ∧ (∀ ν₁ ν₂, ∃ g : (ℂ → ℂ) → ℂ → ℂ,
      IsHolomorphicFn (fun φ => hypNorm φ (toExt lowerHalf)) (fun φ => hypNorm φ (toExt lowerHalf))
        (h ν₁ '' (bersDomainV (h ν₁) ∩ α ⁻¹' bersDomainV (h ν₂))) g ∧
      ∀ p ∈ bersDomainV (h ν₁) ∩ α ⁻¹' bersDomainV (h ν₂), g (h ν₁ p) = h ν₂ (α p)) ∧
    ∃ β : TeichGamma Γ → TeichGamma Γ, (∀ p, β (α p) = p) ∧ (∀ q, α (β q) = q) ∧ ∀ ν₁ ν₂, ∃ g : (ℂ → ℂ) → ℂ → ℂ,
      IsHolomorphicFn (fun φ => hypNorm φ (toExt lowerHalf)) (fun φ => hypNorm φ (toExt lowerHalf))
        (h ν₂ '' (bersDomainV (h ν₂) ∩ β ⁻¹' bersDomainV (h ν₁))) g ∧
      ∀ q ∈ bersDomainV (h ν₂) ∩ β ⁻¹' bersDomainV (h ν₁), g (h ν₂ q) = h ν₁ (β q) := by
  sorry

end Lehto1987
