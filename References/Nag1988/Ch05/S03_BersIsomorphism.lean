import References.Nag1988.Ch05.S02_UniversalFamily

/-!
# Nag, Chapter 5 §5.3: Puncture-forgetting fiber spaces and Bers' isomorphism theorem (§5.3.1–§5.3.4)

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 5 §5.3.1–§5.3.4 (`full.md`
N2:4932–5170, folder `The Complex Analytic Theory … c10f6cd1`). §5.3.5–§5.3.10 (Earle–Eells, `Diff₀`-bundles,
projective structures) need the `C^∞`/Hölder topology on diffeomorphism groups, which is not available; they are listed
below as deferred, one line each.

Conventions: as in §5.1–§5.2 (`T(G)` = Bers image, Banach-style predicates). Punctured surfaces are handled through
their Fuchsian groups: `X = ℍ/Γ` of type `(g, n)`, `X' = X − {x₁, …, x_k} = ℍ/Γ'` of type `(g, n + k)` (3.1); the
inclusion `X' ↪ X` lifts to a holomorphic map `ι : ℍ → ℍ` (`IsPunctureCovering`), and `M(X') = M(X)` becomes the
pull-back `μ' = ι^*μ` (`IsPuncturePullback`). `P : T(g,n+k) → T(g,n)`, `P[μ'] = [μ]` is the relation `IsPunctureMap`.

* Definition (puncture-forgetting map `P`, (3.1)–(3.3), §5.3.1, N2:4934) — `IsPunctureCovering`, `IsPuncturePullback`,
  `IsPunctureMap`, `mobAct`
* Proposition 5.3.1 (`P : T(g,n+k) → T(g,n)` is a holomorphic fiber space, N2:4972) — `prop5_3_1`
* Theorem 5.3.2 (Bers' isomorphism theorem, `F(g,n) ≅ T(g,n+1)` over `T(g,n)`, N2:5002) — `thm5_3_2`
* Corollary 5.3.2 (a) (`T(g,n+1)` is the universal covering of `V(g,n)'`, N2:5020) — `cor5_3_2_a`
* Corollary 5.3.2 (b) (the fibers of `P` are properly embedded holomorphic disks, N2:5022) — `cor5_3_2_b`
* Corollary 5.3.2 (c) (`mod(g,n)` embeds in `Mod(g,n+1)`, N2:5024) — deferred: needs the group structure of `mod(g,n)`
  and the identification of the forgotten puncture's cusp class under the uniformization
* Remark 1 of Theorem 5.3.2 (Bers, general torsion-free `G`, quoted, N2:5028) — `thm5_3_2_general`
* Remark 2 of Theorem 5.3.2 (Earle–Kra non-isomorphism, quoted, N2:5032) — deferred: the type `(g, n)` of a group with
  torsion and cusps is not defined in the work
* Proposition 5.2.4 (c) (independence of the signature, pullback `W(g,n)`, N2:4764) — deferred: needs the complex-analytic
  equivalence of the quotient `V(G)` (known only chart-wise) with a pullback fiber space and the identification
  `T(G) ≅ T(g,n)`
* Definition (bundle vocabulary after Husemoller, §5.3.3, N2:5042) — `IsPrincipalBundle`, `rightSubRel`, `assocSubRel`
* Proposition 5.3.4 (`X mod H ≅ ξ[G mod H]` for a principal `G` bundle and closed `H ≤ G`, N2:5120) — `prop5_3_4`
* Definition (`S^∞(X)`, `Diff⁺(X)`, `Diff₀(X)`, `Diff(X,k)`, §5.3.5, N2:5170) — deferred: needs the C^∞/Hölder
  topology on diffeomorphism groups
* Lemmas 1–3 of 5.3.5, formulas (3.19), (3.24), (3.25), Arens' remark, the contractibility remark — deferred: needs the
  `C^∞`/Hölder topology on diffeomorphism groups
* Theorem 5.3.5 (a), (b) (Earle–Eells), Corollary 5.3.5 — deferred: needs the C^∞/Hölder topology on diffeomorphism groups
* Lemma 5.3.6, Definition `D₀(G)`, Proposition 5.3.6, formula (3.35) — deferred: needs the C^∞/Hölder topology on
  diffeomorphism groups
* Proposition 5.3.7, fact (B), Corollary 5.3.7, §5.3.8 formulas (3.40)–(3.42), §5.3.9 — deferred: needs the C^∞/Hölder
  topology on diffeomorphism groups
* Definition (`Σ^∞(X)`, `P(g,0)`, `P_T V`) and the claims of §5.3.10 — deferred: projective structures are not installed
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Nag1988

open LiZhongQC (upperHalf lowerHalf BeltramiGamma bersFunctionGamma bersImage BersFiberSpace bersFiberRel
  BersQuotient normalizedSolution IsFuchsian ActsFreely mobiusFn)
open GardinerLakic2000 (cuspNorm cuspFormsL)

variable {Γ Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-! ## §5.3.1 The puncture-forgetting map -/

/-- The Möbius action of `γ ∈ SL(2, ℝ)` on `ℂ`, `z ↦ (a z + b)/(c z + d)`. -/
def mobAct (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) : ℂ := mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z

/-- **The lift `ι : ℍ → ℍ` of the inclusion `X' = ℍ/Γ' ↪ ℍ/Γ = X`** forgetting `k` punctures (§5.3.1, (3.1)): `ι` is
holomorphic with non-vanishing derivative, maps `ℍ` into `ℍ`, is equivariant (every element of `Γ'` acts through some
element of `Γ`), induces an injection of `Γ'`-orbits into `Γ`-orbits, and the `Γ`-orbits missed by `ι(ℍ)` are exactly the
`k` lifts of the forgotten points. Modelling: the covering data of the inclusion `X' ↪ X` through the uniformizations. -/
structure IsPunctureCovering (Γ' Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (ι : ℂ → ℂ) (k : ℕ) : Prop where
  holo : DifferentiableOn ℂ ι upperHalf
  maps : ι '' upperHalf ⊆ upperHalf
  deriv_ne : ∀ z ∈ upperHalf, deriv ι z ≠ 0
  equivariant : ∀ γ' ∈ Γ', ∃ γ ∈ Γ, ∀ z ∈ upperHalf, ι (mobAct γ' z) = mobAct γ (ι z)
  orbit_inj : ∀ z ∈ upperHalf, ∀ w ∈ upperHalf, (∃ γ ∈ Γ, ι z = mobAct γ (ι w)) → ∃ γ' ∈ Γ', z = mobAct γ' w
  missed : Cardinal.mk (Quot fun τ σ : {τ : UpperHalfPlane // ∀ z ∈ upperHalf, ∀ γ ∈ Γ, mobAct γ (ι z) ≠ (τ : ℂ)} =>
    ∃ γ ∈ Γ, γ • (τ : UpperHalfPlane) = σ) = k

/-- **`M(X') = M(X)`** (§5.3.1, (3.2)): `μ' ∈ M(Γ')` is the pull-back `ι^*μ` of `μ ∈ M(Γ)`, i.e.
`μ'(z) = μ(ι z) · conj(ι'(z))/ι'(z)` a.e. on `ℍ` (no junk: `ι' ≠ 0` on `ℍ` by `IsPunctureCovering.deriv_ne`). -/
def IsPuncturePullback (ι : ℂ → ℂ) (μ' : BeltramiGamma Γ') (μ : BeltramiGamma Γ) : Prop :=
  ∀ᵐ z ∂(volume.restrict upperHalf), μ'.1.1 z = μ.1.1 (ι z) * (conj (deriv ι z) / deriv ι z)

/-- **The puncture-forgetting map `P : T(g,n+k) → T(g,n)`**, `P([μ']) = [[μ]]` (§5.3.1, (3.2)): in Bers coordinates,
`P φ' = φ_μ` whenever `φ' = φ_{μ'}` and `μ' = ι^*μ`. -/
def IsPunctureMap (Γ' Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (ι : ℂ → ℂ) (P : (ℂ → ℂ) → (ℂ → ℂ)) : Prop :=
  ∀ φ' ∈ bersImage Γ', ∀ (μ' : BeltramiGamma Γ') (μ : BeltramiGamma Γ), bersFunctionGamma μ' = φ' →
    IsPuncturePullback ι μ' μ → P φ' = bersFunctionGamma μ

/-- **Proposition 5.3.1** (Ch. 5 §5.3.1). `P : T(g, n+k) → T(g, n)` is a well-defined holomorphic fiber space for each
`k ≥ 1`: every `μ' ∈ M(Γ')` is the pull-back of some `μ ∈ M(Γ)`, `P[μ'] = [μ]`, and `P` is a holomorphic split submersion
between open subsets of the Banach spaces `B(Γ')`, `B(Γ)`. Modelling: the statement on the derivative `d_{[μ]}P` being
induced by the identity on `L^∞` (3.5) and on the dual inclusion `A₂(X^μ) ↪ A₂(X'^μ)` (3.6) is not formalized
(the surjectivity of `dP` is part of `IsHolFiberSpace`). -/
theorem prop5_3_1 (hΓ : IsFuchsian Γ) (hΓ' : IsFuchsian Γ') (hfree : ActsFreely Γ) (hfree' : ActsFreely Γ')
    {g n k : ℕ} (hk : 1 ≤ k) (hty : IsOfType Γ g n) (hty' : IsOfType Γ' g (n + k)) {ι : ℂ → ℂ}
    (hι : IsPunctureCovering Γ' Γ ι k) :
    (∀ μ' : BeltramiGamma Γ', ∃ μ : BeltramiGamma Γ, IsPuncturePullback ι μ' μ) ∧
      ∃ P : (ℂ → ℂ) → (ℂ → ℂ), IsPunctureMap Γ' Γ ι P ∧
        IsBOpen (cuspNorm lowerHalf) (cuspFormsL Γ') (bersImage Γ') ∧ IsBOpen (cuspNorm lowerHalf) (cuspFormsL Γ) (bersImage Γ) ∧
        IsHolFiberSpace (cuspNorm lowerHalf) (cuspNorm lowerHalf) (bersImage Γ') (bersImage Γ) P := by
  sorry

/-- **Theorem 5.3.2 (Bers' isomorphism theorem)** (Ch. 5 §5.3.2). Let `G` be torsion free, `X = U/G` of type `(g, n)`,
`X' = X − {pt}` of type `(g, n+1)`. Then the Bers fiber space `F : F(g,n) → T(g,n)` and the puncture-forgetting fiber space
`P : T(g,n+1) → T(g,n)` are complex-analytically equivalent by the biholomorphism `α([μ']) = ([[μ]], w^μ(a))` (3.7), with
`a ∈ U` fixed over the forgotten puncture (not in the `Γ`-orbit of `ι(ℍ)`), so that `F ∘ α = P`. -/
theorem thm5_3_2 (hΓ : IsFuchsian Γ) (hΓ' : IsFuchsian Γ') (hfree : ActsFreely Γ) (hfree' : ActsFreely Γ')
    {g n : ℕ} (hty : IsOfType Γ g n) (hty' : IsOfType Γ' g (n + 1)) {ι : ℂ → ℂ} (hι : IsPunctureCovering Γ' Γ ι 1)
    {a : ℂ} (ha : a ∈ upperHalf) (hmiss : ∀ z ∈ upperHalf, ∀ γ ∈ Γ, mobAct γ (ι z) ≠ a)
    (P : (ℂ → ℂ) → (ℂ → ℂ)) (hP : IsPunctureMap Γ' Γ ι P) :
    ∃ α : (ℂ → ℂ) → (ℂ → ℂ) × ℂ,
      IsHolFiberEquiv (cuspNorm lowerHalf) pairNorm (cuspNorm lowerHalf) (cuspNorm lowerHalf) (bersImage Γ') (bersImage Γ)
        (BersFiberSpace Γ) (bersImage Γ) P Prod.fst α id ∧
      ∀ (μ' : BeltramiGamma Γ') (μ : BeltramiGamma Γ), IsPuncturePullback ι μ' μ →
        α (bersFunctionGamma μ') = (bersFunctionGamma μ, normalizedSolution μ.1.1 a) := by
  sorry

/-- **Theorem 5.3.2, Remark 1 (Bers, general case, quoted)** (Ch. 5 §5.3.2). For an arbitrary torsion-free Fuchsian group
`G` (no finiteness assumption), with `X = U/G` and `G'` uniformizing `X' = X − {pt}`, the Bers fiber space `F(G)` is
biholomorphic to `T(G')` by a map commuting with the projections to `T(G)`; the biholomorphism is again
`α([μ']) = ([[μ]], w^μ(a))`. -/
theorem thm5_3_2_general (hΓ : IsFuchsian Γ) (hΓ' : IsFuchsian Γ') (hfree : ActsFreely Γ) (hfree' : ActsFreely Γ')
    {ι : ℂ → ℂ} (hι : IsPunctureCovering Γ' Γ ι 1) {a : ℂ} (ha : a ∈ upperHalf)
    (hmiss : ∀ z ∈ upperHalf, ∀ γ ∈ Γ, mobAct γ (ι z) ≠ a) (P : (ℂ → ℂ) → (ℂ → ℂ)) (hP : IsPunctureMap Γ' Γ ι P) :
    ∃ α : (ℂ → ℂ) → (ℂ → ℂ) × ℂ,
      IsHolFiberEquiv (cuspNorm lowerHalf) pairNorm (cuspNorm lowerHalf) (cuspNorm lowerHalf) (bersImage Γ') (bersImage Γ)
        (BersFiberSpace Γ) (bersImage Γ) P Prod.fst α id ∧
      ∀ (μ' : BeltramiGamma Γ') (μ : BeltramiGamma Γ), IsPuncturePullback ι μ' μ →
        α (bersFunctionGamma μ') = (bersFunctionGamma μ, normalizedSolution μ.1.1 a) := by
  sorry

/-- **Corollary 5.3.2 (a)** (Ch. 5 §5.3.2). `T(g, n+1)` is the (holomorphic) universal covering space of `V(g,n)'`: for
a Bers isomorphism `α`, the composite `T(g,n+1) → F(g,n) → V(g,n)` is a covering map and `T(g,n+1)` is simply connected. -/
theorem cor5_3_2_a (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (α : (ℂ → ℂ) → (ℂ → ℂ) × ℂ)
    (hα : IsBBiholOn (cuspNorm lowerHalf) pairNorm (bersImage Γ') (BersFiberSpace Γ) α) :
    letI := bersImageTopology Γ'
    letI := bersQuotientTopology Γ
    ∃ pr : bersImage Γ' → BersQuotient Γ, IsCoveringMap pr ∧ SimplyConnectedSpace (bersImage Γ') ∧
      ∀ (φ' : bersImage Γ') (q : BersFiberSpace Γ), (q : (ℂ → ℂ) × ℂ) = α φ'.1 → pr φ' = Quot.mk (bersFiberRel Γ) q := by
  sorry

/-- **Corollary 5.3.2 (b)** (Ch. 5 §5.3.2). The fibers of `P` are properly embedded holomorphic disks in `T(g, n+1)`: each
fiber `P⁻¹(φ)` is the image of the unit disc under an injective holomorphic map which is a homeomorphism onto the fiber, and
the fiber is closed in `T(g,n+1)`. -/
theorem cor5_3_2_b (hΓ : IsFuchsian Γ) (hΓ' : IsFuchsian Γ') (hfree : ActsFreely Γ) (hfree' : ActsFreely Γ') {ι : ℂ → ℂ}
    (hι : IsPunctureCovering Γ' Γ ι 1) (P : (ℂ → ℂ) → (ℂ → ℂ)) (hP : IsPunctureMap Γ' Γ ι P) :
    ∀ φ ∈ bersImage Γ, ∃ f : ℂ → (ℂ → ℂ),
      IsBHolOn (fun t : ℂ => ENNReal.ofReal ‖t‖) (cuspNorm lowerHalf) (ball 0 1) f ∧
      IsBHomeoOn (fun t : ℂ => ENNReal.ofReal ‖t‖) (cuspNorm lowerHalf) (ball 0 1) {φ' ∈ bersImage Γ' | P φ' = φ} f ∧
      ∀ φ'' ∈ bersImage Γ', (∀ ε > (0 : ℝ), ∃ φ' ∈ bersImage Γ', P φ' = φ ∧ cuspNorm lowerHalf (φ'' - φ') < ENNReal.ofReal ε) →
        P φ'' = φ := by
  sorry

/-! ## §5.3.3, §5.3.4 Principal bundles and Proposition 5.3.4 -/

/-- **Principal `G` bundle** (§5.3.3, after Husemoller, N2:5042–5112). `p : X → B` is a continuous surjection from a
space with a free (continuous) right `G`-action whose fibers are exactly the `G`-orbits, locally trivial: over a
neighbourhood `U` of every point there is a homeomorphism `p⁻¹(U) ≅ U × G` over `U`, `G`-equivariant for right
translation in the second factor. Modelling: the right action is `MulAction Gᵐᵒᵖ X`; the translation function of the book
is continuous by local triviality. -/
def IsPrincipalBundle {X B : Type*} (G : Type*) [Group G] [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace B]
    [MulAction Gᵐᵒᵖ X] (p : X → B) : Prop :=
  Continuous p ∧ Function.Surjective p ∧ (∀ x y, p x = p y ↔ ∃ g : G, y = MulOpposite.op g • x) ∧
    (∀ (x : X) (g : G), MulOpposite.op g • x = x → g = 1) ∧
    ∀ b : B, ∃ U : Set B, IsOpen U ∧ b ∈ U ∧ ∃ φ : ↥(p ⁻¹' U) ≃ₜ (↥U × G),
      (∀ x, ((φ x).1 : B) = p x.1) ∧ ∀ (x y : ↥(p ⁻¹' U)) (g : G), y.1 = MulOpposite.op g • x.1 → (φ y).2 = (φ x).2 * g

/-- **The orbit relation of a subgroup `H` acting on the right** (§5.3.3): `x ~ y` iff `y = x h` for some `h ∈ H`. -/
def rightSubRel {X : Type*} {G : Type*} [Group G] [MulAction Gᵐᵒᵖ X] (H : Subgroup G) (x y : X) : Prop :=
  ∃ h ∈ H, y = MulOpposite.op h • x

/-- **The orbit relation of the associated bundle `ξ[G/H]`** (§5.3.3, (3.13)): on `X × G/H`, `(x, y) ~ (x g, g⁻¹ y)`. -/
def assocSubRel {X : Type*} {G : Type*} [Group G] [MulAction Gᵐᵒᵖ X] (H : Subgroup G) (u v : X × (G ⧸ H)) : Prop :=
  ∃ g : G, v = (MulOpposite.op g • u.1, g⁻¹ • u.2)

/-- **Proposition 5.3.4** (Ch. 5 §5.3.4). Let `ξ = (X, p, B)` be a principal `G` bundle and `H` a closed subgroup of `G`.
Then `h : X mod H → (X × (G mod H)) mod G`, `h(xH) = (x, 1H)G` (3.15) is a homeomorphism and a `B`-isomorphism of
`ξ mod H` onto the associated bundle `ξ[G mod H]`. -/
theorem prop5_3_4 {X B G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
    [TopologicalSpace B] [MulAction Gᵐᵒᵖ X] [ContinuousSMul Gᵐᵒᵖ X] (p : X → B) (hp : IsPrincipalBundle G p) (H : Subgroup G)
    (hH : IsClosed (H : Set G)) :
    ∃ e : Quot (rightSubRel (X := X) H) ≃ₜ Quot (assocSubRel (X := X) H),
      (∀ x : X, e (Quot.mk _ x) = Quot.mk _ (x, ((1 : G) : G ⧸ H))) ∧
        ∀ (x : X) (q : X × (G ⧸ H)), e (Quot.mk _ x) = Quot.mk _ q → p x = p q.1 := by
  sorry

end Nag1988
