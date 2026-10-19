import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
import References.GardinerLakic2000.Ch12.S04_IntersectionNumbers
import References.Lehto1987.Ch05.S08_UniquenessOfExtremalMappingsOfCompactSurfaces

/-!
# Imayoshi–Taniguchi, Chapter 6 §6.5: Classification of Teichmüller modular transformations

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 6 §6.5 (`full.md`
IT1:6160–6455, folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions: `R = S₀` is a closed Riemann surface of genus `g ≥ 2` (`R_*`), `T(R_*) = LiZhongQC.TeichSpace S₀`, a Teichmüller
modular transformation is `LiZhongQC.ModTransform` acting by the relation `LiZhongQC.ModAction` (`σ^*[S, f] = [S, f ∘ σ]`; this
is IT's `[σ]_*` up to the inverse, which does not matter for the classification). A complex structure `σ` on `R` is a marked
surface `m : LiZhongQC.MarkedRS S₀` (`R_σ = m.X`, with the marking), and `K_σ(f)` is the maximal dilatation of the conjugate
`m.marking ∘ f ∘ m.marking⁻¹` (`dilatationIn`). Homotopy of self-mappings is `ContinuousMap.Homotopic` (IT: homotopic ⇔ isotopic,
Epstein). Distance (IT-D3): IT's `d` is **twice** `LiZhongQC.teichDistance`; `a(χ)` below is taken for `teichDistance`, so IT's
`a(χ)` is `2 *` it (the four types only use `a = 0` or `a > 0` and attainment); the factor is written explicitly in
`IsStraightLineTeich`. Simple closed geodesics of a closed surface `S = ℍ/Γ` are `IsSimpleClosedGeodesic p C` for a
uniformization `p` (`GardinerLakic2000.IsSimpleLoop`, `GardinerLakic2000.IsClosedPoincareGeodesic`), their length is
`LiZhongQC.poincareLengthLoop p C`.

* Definition (translation-length classification of real Möbius maps, §6.5.1, IT1:6172) — omitted: recall of Chapter 2 notions
  (`LiZhongQC.translationLength`)
* Definition (`a(χ)`, `χ`-minimal point, §6.5.1, IT1:6188) — `modTranslationLength`, `IsChiMinimal`
* Definition (elliptic, parabolic, hyperbolic, pseudo-hyperbolic, §6.5.1, IT1:6202) — `IsEllipticMod`, `IsParabolicMod`,
  `IsHyperbolicMod`, `IsPseudoHyperbolicMod`
* Definition (`K_σ(f)`, `f`-minimal complex structure, absolutely extremal mapping, §6.5.1, IT1:6216) — `dilatationIn`,
  `IsFMinimal`, `IsAbsolutelyExtremal`, `HomeoHomotopic`
* Proposition 6.24 (IT1:6228) — `prop6_24`
* Theorem 6.25 (elliptic ⇔ periodic, IT1:6256) — `homeoPow`, `ModActionPow`, `IsPeriodicMod`, `thm6_25`
* Theorem 6.26 (IT1:6266) — `thm6_26`
* Definition (admissible system of curves, reduced, reducible, irreducible, §6.5.2, IT1:6268) — `IsAdmissibleCurveSystem`,
  `IsReducedBy`, `IsReducible`, `IsIrreducible`
* Theorem 6.27 (IT1:6276) — `thm6_27`
* Lemma 6.28 (Wolpert, IT1:6280) — exists: `LiZhongQC.lemma30_3_wolpert` (for every closed curve α, in particular a simple
  closed geodesic, l[f α] ≤ K[f] l[α], l the length of the shortest curve in the free homotopy class)
* Lemma 6.29 (short simple closed geodesics are disjoint, IT1:6292) — `IsSimpleClosedGeodesic`, `HasDisjointShortGeodesics`,
  `lemma6_29`
* Lemma 6.30 (IT1:6296) — `lemma6_30`
* Lemma 6.31 (Mumford compactness, IT1:6316) — `lemma6_31`
* Definition (straight line in `T(R_*)`, §6.5.3, IT1:6356) — `IsStraightLineTeich`
* Unlabelled (`T(R_*)` is a Busemann straight-line space, §6.5.3, IT1:6356) — `para6_5_3`
* Theorem 6.32 (IT1:6364) — `LeavesInvariant`, `thm6_32`
* Corollary to Theorem 6.32 (IT1:6390) — `thm6_32_cor`
* Theorem 6.33 (absolutely extremal mappings, IT1:6396) — `thm6_33`
* Unlabelled (Remark 2 of §6.5.3, IT1:6418) — `para6_5_3_rem2`
* Theorem 6.34 (IT1:6424) — `IsHomotopicToPeriodic`, `thm6_34`
* Corollary to Theorem 6.34 (IT1:6428) — `thm6_34_cor`
* Definition (completely reduced mapping, §6.5.4, IT1:6432) — omitted: used only in an explanatory paragraph
* Unlabelled (pseudo-Anosov ⇔ Teichmüller map with proportional differentials, (a), (b), §6.5.4, IT1:6448) — deferred:
  pseudo-Anosov diffeomorphisms are not defined in the work
* Theorem 6.35 (Nielsen–Thurston, IT1:6454) — deferred: pseudo-Anosov diffeomorphisms are not defined in the work
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (TeichSpace MarkedRS ModTransform ModAction teichDistance maxDilatationRS IsBiholomorphic IsQCRS Loop
  FreelyHomotopic poincareLengthLoop HasGenus IsUniformization IsFuchsian ActsFreely)
open GardinerLakic2000 (IsSimpleLoop IsClosedPoincareGeodesic)

section Defs

variable {S₀ : Type} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

/-- Two self-homeomorphisms are homotopic (as continuous self-maps). -/
def HomeoHomotopic (f g : S₀ ≃ₜ S₀) : Prop := ContinuousMap.Homotopic (f : C(S₀, S₀)) (g : C(S₀, S₀))

/-- **`a(χ) = inf_p d(p, χ(p))`** (Ch. 6 §6.5.1, Bers' extremal problem): the infimum of the Teichmüller distance
`teichDistance p (χ p)` over `T(R_*)`, `χ = σ^*` acting by the relation `ModAction`. (IT's `d` is twice `teichDistance`.) -/
def modTranslationLength (f : ModTransform S₀) : ℝ :=
  sInf {d | ∃ p q : TeichSpace S₀, ModAction f p q ∧ d = teichDistance p q}

/-- **`χ`-minimal point** (Ch. 6 §6.5.1): `p` realizes `a(χ) = d(p, χ(p))`. -/
def IsChiMinimal (f : ModTransform S₀) (p : TeichSpace S₀) : Prop :=
  ∃ q, ModAction f p q ∧ teichDistance p q = modTranslationLength f

/-- **Elliptic** modular transformation (Ch. 6 §6.5.1): `a(χ) = 0` and a `χ`-minimal point exists. -/
def IsEllipticMod (f : ModTransform S₀) : Prop := modTranslationLength f = 0 ∧ ∃ p, IsChiMinimal f p

/-- **Parabolic** modular transformation: `a(χ) = 0` and no `χ`-minimal point exists. -/
def IsParabolicMod (f : ModTransform S₀) : Prop := modTranslationLength f = 0 ∧ ¬∃ p, IsChiMinimal f p

/-- **Hyperbolic** modular transformation: `a(χ) > 0` and a `χ`-minimal point exists. (Named `IsHyperbolicMod` to avoid
`LiZhongQC.IsHyperbolic`, which is for group elements.) -/
def IsHyperbolicMod (f : ModTransform S₀) : Prop := 0 < modTranslationLength f ∧ ∃ p, IsChiMinimal f p

/-- **Pseudo-hyperbolic** modular transformation: `a(χ) > 0` and no `χ`-minimal point exists. -/
def IsPseudoHyperbolicMod (f : ModTransform S₀) : Prop := 0 < modTranslationLength f ∧ ¬∃ p, IsChiMinimal f p

/-- **`K_σ(f)`** (Ch. 6 §6.5.1): the maximal dilatation of the self-mapping `f` of `R`, considered as a self-mapping of the
Riemann surface `R_σ = m.X` (`σ` = the complex structure of the marked surface `m`); `⊤` if `f` is not quasiconformal. -/
def dilatationIn (m : MarkedRS S₀) (f : S₀ ≃ₜ S₀) : ℝ≥0∞ :=
  maxDilatationRS (m.marking.symm.trans (f.trans m.marking))

/-- **`f`-minimal complex structure** (Ch. 6 §6.5.1, Bers' extremal problem for complex structures): there is `f₀ ≃ f`
with `K_σ(f₀) ≤ K_{σ₁}(f₁)` for every complex structure `σ₁` and every `f₁ ≃ f`. -/
def IsFMinimal (m : MarkedRS S₀) (f : S₀ ≃ₜ S₀) : Prop :=
  ∃ f₀ : S₀ ≃ₜ S₀, HomeoHomotopic f₀ f ∧ ∀ (m₁ : MarkedRS S₀) (f₁ : S₀ ≃ₜ S₀), HomeoHomotopic f₁ f →
    dilatationIn m f₀ ≤ dilatationIn m₁ f₁

/-- **Absolutely extremal self-mapping** (Ch. 6 §6.5.1): `f : S → S` has `K(f) ≤ K_{σ₁}(f₁)` for every complex structure
`σ₁` on `S` (a marked surface) and every `f₁ ≃ f`. -/
def IsAbsolutelyExtremal (f : S₀ ≃ₜ S₀) : Prop :=
  ∀ (m₁ : MarkedRS S₀) (f₁ : S₀ ≃ₜ S₀), HomeoHomotopic f₁ f → maxDilatationRS f ≤ dilatationIn m₁ f₁

/-- The `k`-th iterate of a self-homeomorphism (`f⁰ = id`, `f^{k+1} = f ∘ f^k`). -/
def homeoPow (f : S₀ ≃ₜ S₀) : ℕ → (S₀ ≃ₜ S₀)
  | 0 => Homeomorph.refl S₀
  | k + 1 => (homeoPow f k).trans f

/-- The action of the `k`-th power `σ^k` of a modular transformation, `[S, m] ↦ [S, m ∘ σ^k]`, as a relation (as `ModAction`). -/
def ModActionPow (f : ModTransform S₀) (k : ℕ) (p q : TeichSpace S₀) : Prop :=
  ∃ (m : MarkedRS S₀) (hqc : IsQCRS ((homeoPow f.1 k).trans m.marking)), p = Quot.mk _ m ∧
    q = Quot.mk _ ⟨m.X, (homeoPow f.1 k).trans m.marking, hqc⟩

/-- A modular transformation is **periodic** (of finite order): some positive power acts as the identity on `T(R_*)`. -/
def IsPeriodicMod (f : ModTransform S₀) : Prop := ∃ k : ℕ, 0 < k ∧ ∀ p q, ModActionPow f k p q → q = p

/-- A self-mapping is **periodic**: some positive power is the identity. -/
def IsPeriodicMap (f : S₀ ≃ₜ S₀) : Prop := ∃ k : ℕ, 0 < k ∧ homeoPow f k = Homeomorph.refl S₀

/-- `f` is homotopic to a periodic self-mapping. -/
def IsHomotopicToPeriodic (f : S₀ ≃ₜ S₀) : Prop := ∃ f' : S₀ ≃ₜ S₀, HomeoHomotopic f' f ∧ IsPeriodicMap f'

/-- **Admissible system of curves** (Ch. 6 §6.5.2): a finite non-empty family of mutually disjoint simple closed curves, none
freely homotopic to a point or to any `C_k^{±1}`, `k ≠ j`. (Not `GardinerLakic2000.IsAdmissibleSystem`, which is the
Jenkins–Strebel notion.) -/
def IsAdmissibleCurveSystem {n : ℕ} (C : Fin n → Loop S₀) : Prop :=
  0 < n ∧ (∀ j, IsSimpleLoop (C j)) ∧ (∀ j k, j ≠ k → Disjoint (range (C j).2) (range (C k).2)) ∧
    (∀ j k, j ≠ k → ¬FreelyHomotopic (C j) (C k) ∧ ¬FreelyHomotopic (C j) ⟨(C k).1, (C k).2.symm⟩) ∧
    ∀ j (x : S₀), ¬FreelyHomotopic (C j) ⟨x, Path.refl x⟩

/-- `f` is **reduced** by the system `C`: the system is admissible and `f (C₁ ∪ ⋯ ∪ C_n) = C₁ ∪ ⋯ ∪ C_n`. -/
def IsReducedBy {n : ℕ} (f : S₀ ≃ₜ S₀) (C : Fin n → Loop S₀) : Prop :=
  IsAdmissibleCurveSystem C ∧ f '' (⋃ j, range (C j).2) = ⋃ j, range (C j).2

/-- `f` is **reducible** if it is homotopic to a reduced mapping, and **irreducible** if not. -/
def IsReducible (f : S₀ ≃ₜ S₀) : Prop :=
  ∃ f' : S₀ ≃ₜ S₀, HomeoHomotopic f' f ∧ ∃ (n : ℕ) (C : Fin n → Loop S₀), IsReducedBy f' C

/-- `f` is irreducible: not reducible. -/
def IsIrreducible (f : S₀ ≃ₜ S₀) : Prop := ¬IsReducible f

/-- **Straight line in `T(R_*)`** (Ch. 6 §6.5.3): an isometric image of `ℝ` for IT's distance `d = 2 * teichDistance`
(IT-D3: the factor is explicit). -/
def IsStraightLineTeich (L : ℝ → TeichSpace S₀) : Prop := ∀ x y : ℝ, 2 * teichDistance (L x) (L y) = |x - y|

/-- A set `A ⊆ T(R_*)` is **left invariant** by a modular transformation: `χ` maps `A` into `A` and onto `A`. -/
def LeavesInvariant (f : ModTransform S₀) (A : Set (TeichSpace S₀)) : Prop :=
  (∀ p ∈ A, ∀ q, ModAction f p q → q ∈ A) ∧ ∀ q ∈ A, ∃ p ∈ A, ModAction f p q

end Defs

/-- A **simple closed geodesic** of the closed surface `S = ℍ/Γ` (through the uniformization `p`): a simple closed curve
which is a closed Poincaré geodesic. -/
def IsSimpleClosedGeodesic {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] (p : UpperHalfPlane → S) (C : Loop S) : Prop :=
  IsSimpleLoop C ∧ IsClosedPoincareGeodesic p C

/-- **The property of Lemma 6.29 for the constant `δ₀`**: on every closed Riemann surface of genus `g`, any two simple closed
geodesics, not freely homotopic to each other or to the inverse, of hyperbolic length `< δ₀` are disjoint. -/
def HasDisjointShortGeodesics (g : ℕ) (δ₀ : ℝ) : Prop :=
  ∀ (S : Type) (_ : TopologicalSpace S) (_ : T2Space S) (_ : ConnectedSpace S) (_ : ChartedSpace ℂ S)
    (_ : IsManifold 𝓘(ℂ) ω S) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → S),
    IsFuchsian Γ → ActsFreely Γ → IsUniformization Γ p → HasGenus S g → ∀ C D : Loop S,
      IsSimpleClosedGeodesic p C → IsSimpleClosedGeodesic p D → ¬FreelyHomotopic C D →
        ¬FreelyHomotopic C ⟨D.1, D.2.symm⟩ → poincareLengthLoop p C < ENNReal.ofReal δ₀ →
          poincareLengthLoop p D < ENNReal.ofReal δ₀ → Disjoint (range C.2) (range D.2)

variable {S₀ : Type} [TopologicalSpace S₀] [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀] [ChartedSpace ℂ S₀]
  [IsManifold 𝓘(ℂ) ω S₀]

/-- **Proposition 6.24** (Ch. 6 §6.5.1). For a self-mapping `f` of `R`, a complex structure `σ` is `f`-minimal if and only if
the point `[σ] ∈ T(R_*)` is `[f]_*`-minimal. -/
theorem prop6_24 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (f : ModTransform S₀) (m : MarkedRS S₀) :
    IsFMinimal m f.1 ↔ IsChiMinimal f (Quot.mk _ m) := by
  sorry

/-- **Theorem 6.25** (Ch. 6 §6.5.2). A Teichmüller modular transformation `χ` is elliptic if and only if it is periodic. -/
theorem thm6_25 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (f : ModTransform S₀) :
    IsEllipticMod f ↔ IsPeriodicMod f := by
  sorry

/-- **Theorem 6.26** (Ch. 6 §6.5.2). For a self-mapping `f` of `R` there is an `f`-minimal complex structure if and only if
the Teichmüller modular transformation `[f]_*` is either elliptic or hyperbolic. -/
theorem thm6_26 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (f : ModTransform S₀) :
    (∃ m : MarkedRS S₀, IsFMinimal m f.1) ↔ IsEllipticMod f ∨ IsHyperbolicMod f := by
  sorry

/-- **Theorem 6.27** (Ch. 6 §6.5.2). If `f` is an irreducible self-mapping of `R`, then the Teichmüller modular transformation
`[f]_*` induced by `f` is either elliptic or hyperbolic. -/
theorem thm6_27 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (f : ModTransform S₀) (hirr : IsIrreducible f.1) :
    IsEllipticMod f ∨ IsHyperbolicMod f := by
  sorry

/-- **Lemma 6.29** (Ch. 6 §6.5.2, by the collar lemma). There is a constant `δ₀ > 0`, depending only on the genus `g`, such
that any two distinct simple closed geodesics on a closed Riemann surface of genus `g` are disjoint provided that their
hyperbolic lengths are less than `δ₀`. Modelling: distinct = not freely homotopic to each other or to the inverse; lengths
are `LiZhongQC.poincareLengthLoop` (the project's Poincaré density; only constants depend on the normalization).
Near miss: Hubbard 2006 Corollary 3.8.7 (Lane B, not yet installed), whose constant is universal. -/
theorem lemma6_29 {g : ℕ} (hg : 1 < g) : ∃ δ₀ : ℝ, 0 < δ₀ ∧ HasDisjointShortGeodesics g δ₀ := by
  sorry

/-- **Lemma 6.30** (Ch. 6 §6.5.2). Let `C` be a simple closed geodesic with hyperbolic length `ℓ` on a closed Riemann surface
`S` of genus `g ≥ 2`. Then every irreducible (quasiconformal) self-mapping `f` of `S` satisfies
`K(f) ≥ (δ₀/ℓ)^{1/(3g-3)}` (6.14), `δ₀` a constant with the property of Lemma 6.29. Modelling: `δ₀` is a parameter satisfying
`HasDisjointShortGeodesics` (the constant of Lemma 6.29 cannot be referred to as such). -/
theorem lemma6_30 {g : ℕ} (hg : 1 < g) {δ₀ : ℝ} (hδ : 0 < δ₀) (h629 : HasDisjointShortGeodesics g δ₀)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S₀} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) (hS : HasGenus S₀ g) {C : Loop S₀}
    (hC : IsSimpleClosedGeodesic p C) {ℓ : ℝ} (hℓ : 0 < ℓ) (hlen : poincareLengthLoop p C = ENNReal.ofReal ℓ)
    (f : S₀ ≃ₜ S₀) (hf : IsQCRS f) (hirr : IsIrreducible f) :
    ENNReal.ofReal ((δ₀ / ℓ) ^ ((1 : ℝ) / (3 * (g : ℝ) - 3))) ≤ maxDilatationRS f := by
  sorry

/-- **Lemma 6.31 (Mumford's compactness theorem)** (Ch. 6 §6.5.2). Let `(p_j)` be a sequence in `T(R_*)`. Suppose there is
`δ > 0` such that every simple closed geodesic on the surface of every `p_j` has hyperbolic length `> δ`. Then there are a
subsequence `(p_{j_n})` and Teichmüller modular transformations `χ_n` such that `(χ_n(p_{j_n}))` converges in `T(R_*)` (for the
Teichmüller distance). Near miss: Hubbard 2006 Theorem 7.3.1 (Lane B, not yet installed). -/
theorem lemma6_31 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (pseq : ℕ → TeichSpace S₀) {δ : ℝ} (hδ : 0 < δ)
    (hsys : ∀ j (m : MarkedRS S₀), Quot.mk _ m = pseq j →
      ∀ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (q : UpperHalfPlane → m.X.carrier), IsFuchsian Γ →
        ActsFreely Γ → IsUniformization Γ q → ∀ C : Loop m.X.carrier, IsSimpleClosedGeodesic q C →
          ENNReal.ofReal δ < poincareLengthLoop q C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (χ : ℕ → ModTransform S₀) (q : TeichSpace S₀), ∀ ε > (0 : ℝ), ∃ N : ℕ,
      ∀ n ≥ N, ∀ r, ModAction (χ n) (pseq (φ n)) r → teichDistance r q < ε := by
  sorry

/-- **Unlabelled claim** (Ch. 6 §6.5.3, IT1:6356). `T(R_*)` is a straight-line space in the sense of Busemann: any two
distinct points lie on a unique straight line `L` (an isometric image of `ℝ`), and `L` contains every `p` with
`d(p₁, p) + d(p, p₂) = d(p₁, p₂)`. -/
theorem para6_5_3 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {p₁ p₂ : TeichSpace S₀} (hne : p₁ ≠ p₂) :
    ∃ L : ℝ → TeichSpace S₀, IsStraightLineTeich L ∧ p₁ ∈ range L ∧ p₂ ∈ range L ∧
      (∀ L' : ℝ → TeichSpace S₀, IsStraightLineTeich L' → p₁ ∈ range L' → p₂ ∈ range L' → range L' = range L) ∧
      ∀ p, teichDistance p₁ p + teichDistance p p₂ = teichDistance p₁ p₂ → p ∈ range L := by
  sorry

/-- **Theorem 6.32** (Ch. 6 §6.5.3). If a Teichmüller modular transformation `χ` is of infinite order, then a point `p` is
`χ`-minimal if and only if `χ` leaves a straight line through `p` invariant. -/
theorem thm6_32 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (f : ModTransform S₀) (hinf : ¬IsPeriodicMod f)
    (p : TeichSpace S₀) :
    IsChiMinimal f p ↔ ∃ L : ℝ → TeichSpace S₀, IsStraightLineTeich L ∧ p ∈ range L ∧ LeavesInvariant f (range L) := by
  sorry

/-- **Corollary to Theorem 6.32** (Ch. 6 §6.5.3). For a non-periodic `[f] ∈ Mod(R_*)`, the Teichmüller modular
transformation `[f]_*` is hyperbolic if and only if it leaves some straight line invariant. -/
theorem thm6_32_cor {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (f : ModTransform S₀) (hinf : ¬IsPeriodicMod f) :
    IsHyperbolicMod f ↔ ∃ L : ℝ → TeichSpace S₀, IsStraightLineTeich L ∧ LeavesInvariant f (range L) := by
  sorry

/-- **Theorem 6.33** (Ch. 6 §6.5.3). Let `S` be a closed Riemann surface of genus `g ≥ 2`. A quasiconformal mapping
`f : S → S` is absolutely extremal if and only if it is either a conformal mapping or a Teichmüller mapping such that `f²` is
also a Teichmüller mapping with `K(f²) = K(f)²`. -/
theorem thm6_33 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (f : S₀ ≃ₜ S₀) (hf : IsQCRS f) :
    IsAbsolutelyExtremal f ↔ IsBiholomorphic f ∨ (Lehto1987.IsTeichmullerMapRS f ∧
      Lehto1987.IsTeichmullerMapRS (f.trans f) ∧ maxDilatationRS (f.trans f) = maxDilatationRS f ^ 2) := by
  sorry

/-- **Unlabelled Remark 2** (Ch. 6 §6.5.3, IT1:6418). For a non-conformal Teichmüller self-mapping `f` of `S`, the
condition that `f²` is also a Teichmüller mapping with `K(f²) = K(f)²` is equivalent to the initial and terminal
differentials of `f` coinciding up to a positive constant factor. -/
theorem para6_5_3_rem2 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (f : S₀ ≃ₜ S₀) (hT : Lehto1987.IsTeichmullerMapRS f)
    (hnc : ¬IsBiholomorphic f) :
    (Lehto1987.IsTeichmullerMapRS (f.trans f) ∧ maxDilatationRS (f.trans f) = maxDilatationRS f ^ 2) ↔
      ∃ (q q' : S₀ → ℂ → ℂ) (k : ℝ), LiZhongQC.IsTeichmullerMap f q q' k ∧ ∃ c : ℝ, 0 < c ∧
        q' = fun x z => (c : ℂ) * q x z := by
  sorry

/-- **Theorem 6.34** (Ch. 6 §6.5.4; proof omitted in the book). Let `f` be a reducible self-mapping of `R`. If `f` is not
homotopic to a periodic mapping, then `[f]_*` is either parabolic or pseudo-hyperbolic. -/
theorem thm6_34 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (f : ModTransform S₀) (hred : IsReducible f.1)
    (hnp : ¬IsHomotopicToPeriodic f.1) : IsParabolicMod f ∨ IsPseudoHyperbolicMod f := by
  sorry

/-- **Corollary to Theorem 6.34** (Ch. 6 §6.5.4). For a self-mapping `f` of `R`, an `f`-minimal complex structure exists if
and only if `f` is either homotopic to a periodic mapping or irreducible. -/
theorem thm6_34_cor {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (f : ModTransform S₀) :
    (∃ m : MarkedRS S₀, IsFMinimal m f.1) ↔ IsHomotopicToPeriodic f.1 ∨ IsIrreducible f.1 := by
  sorry

end ImayoshiTaniguchi1992
