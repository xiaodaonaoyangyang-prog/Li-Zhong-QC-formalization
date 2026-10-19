import References.GardinerLakic2000.Ch05.S01_ConformallyNaturalExtension

/-!
# Gardiner–Lakic 2000, Ch. 5 §5.2 Quasiconformal isotopies

Source `teichmuller.txt`, lines 5011–5103.

* Definition (ideal boundary, ideal closure, l. 5018) — exists: `LiZhongQC.ordinarySet` `LiZhongQC.fuchsianLimitSet`
  (the ideal boundary is the quotient of the ordinary set ℝ̂ ∖ Λ; maps of the ideal closure are read through their
  lifts to ℍ ∪ (ℝ̂ ∖ Λ), A0.4(iii))
* Definition (normalized lift, l. 5037) — exists: `LiZhongQC.IsNormalizedLift`
* Definition 2 (Teichmüller space, l. 5020) — exists: `GardinerLakic2000.TeichSpace` (the book restates Definition
  2.7, with the boundary made precise as announced at l. 1343)
* Definition 3 (Teichmüller equivalence, l. 5022) — exists: `GardinerLakic2000.IsTeichEquiv` (Definition 2.6)
* Definition 4 (circle equivalence, l. 5039) — `IsCircleEquiv`
* Definition 5 (isotopy equivalence, l. 5047) — `IsIsotopyEquiv`
* Theorem 3 (isotopy ⇔ Teichmüller ⇔ circle equivalence to the identity, l. 5056) — `thm5_3`
* Corollary 1 (l. 5091) — `cor5_3_1`
* Corollary 2 (l. 5093) — `cor5_3_2`
* Unlabelled (§5.2, l. 5770 and l. 6313; `T(R)` is `T(Γ)` isometrically, the identification used in Ch. 6–7) —
  `para5_2_teichGamma_equiv`
* Definition 6 (trivial Beltrami coefficients, l. 5095) — exists: `LiZhongQC.IsTrivialBeltrami` (the bridge: in the
  Fuchsian model Definition 6 is Corollary 2's w_μ|ℝ = id; IsTrivialBeltrami tests w^μ|ℝ = id; the two agree by
  `LiZhongQC.lemma33_1` with μ₂ = 0)
* Theorem 4 (the same equivalences for two maps `f`, `g`, l. 5099) — `thm5_4`

Not items (DESIGN §3): the argument that homotopic maps have lifts agreeing on the limit set (l. 5031–5037, U−; content
`LiZhongQC.lift_homotopy_agrees_on_limitSet`); the basepoint (Part A).
[misprint] l. 5089 and l. 5135 say "Theorem 1" for Theorem 3.

**Conventions.** `R` carries a uniformization `p : ℍ → R` by a Fuchsian group, as in Part A's `IsTeichEquiv`; maps
`R → R` are maps to the bundle `selfBundle R`. Near miss for Theorem 4: `LiZhongQC.thm36_1` ((ii) ⇔ (iii) for maps to
a common target, without the conformal map `c` and without isotopies).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (ExtPlane extRealLine IsQCRS IsKQCRS IsBiholomorphic IsFuchsian IsUniformization IsNormalizedLift)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition 4** (circle equivalence, §5.2, l. 5039). `f₀ : R → R₀` and `f₁ : R → R₁` are circle equivalent if
their normalized lifts `w₀`, `w₁` (lifts to `ℍ` whose boundary maps fix `0, 1, ∞`) agree on `ℝ̂`. Modelling: the
lifts are taken with respect to the uniformization `p` of `R` and some uniformizations of `R₀`, `R₁` (the normalized
lift does not depend on this choice). -/
def IsCircleEquiv (p : UpperHalfPlane → R) {Y₀ Y₁ : RSBundle.{u}} (f₀ : R ≃ₜ Y₀.carrier) (f₁ : R ≃ₜ Y₁.carrier) :
    Prop :=
  ∃ (p₀ : UpperHalfPlane → Y₀.carrier) (p₁ : UpperHalfPlane → Y₁.carrier) (F₀ F₁ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (G₀ G₁ : ExtPlane → ExtPlane), (∃ Γ₀, IsFuchsian Γ₀ ∧ IsUniformization Γ₀ p₀) ∧
    (∃ Γ₁, IsFuchsian Γ₁ ∧ IsUniformization Γ₁ p₁) ∧ IsNormalizedLift p p₀ f₀ F₀ G₀ ∧
    IsNormalizedLift p p₁ f₁ F₁ G₁ ∧ ∀ x ∈ extRealLine, G₀ x = G₁ x

/-- **Definition 5** (isotopy equivalence, §5.2, l. 5047). `f₀ : R → R₀` and `f₁ : R → R₁` are isotopically
equivalent (with constant `K′`) if there are a conformal map `c : R₀ → R₁` and an isotopy `g_t` of the ideal closure
of `R` with `g₀ = id`, `g₁ = f₁⁻¹ ∘ c ∘ f₀`, fixing the ideal boundary pointwise, every `g_t` being
`K′`-quasiconformal. Modelling: as Part A's `IsTeichEquiv` (the lifted isotopy fixes `ℝ̂`), with `K′`-q.c. stages;
the dependence "`K′` depending only on `K`" is the quantifier order of Theorem 3. -/
def IsIsotopyEquiv (p : UpperHalfPlane → R) (K' : ℝ) {Y₀ Y₁ : RSBundle.{u}} (f₀ : R ≃ₜ Y₀.carrier)
    (f₁ : R ≃ₜ Y₁.carrier) : Prop :=
  ∃ c : Y₀.carrier ≃ₜ Y₁.carrier, IsBiholomorphic (c : Y₀.carrier → Y₁.carrier) ∧
    ∃ (H : R → unitInterval → R) (Ht : UpperHalfPlane → unitInterval → UpperHalfPlane)
      (G : ExtPlane → unitInterval → ExtPlane),
      Continuous (fun x : R × unitInterval => H x.1 x.2) ∧ (∀ x, H x 0 = x) ∧ (∀ x, H x 1 = f₁.symm (c (f₀ x))) ∧
      (∀ t, ∃ e : R ≃ₜ R, (⇑e = fun x => H x t) ∧ IsKQCRS e K') ∧
      (∀ τ t, p (Ht τ t) = H (p τ) t) ∧ Continuous (fun x : ExtPlane × unitInterval => G x.1 x.2) ∧
      (∀ (τ : UpperHalfPlane) t, G ((τ : ℂ) : ExtPlane) t = ((Ht τ t : ℂ) : ExtPlane)) ∧
      ∀ x ∈ extRealLine, ∀ t, G x t = x

/-- **Theorem 3** (§5.2, l. 5056). Let `f : R → R` be quasiconformal. Then the following are equivalent:
(i) `f` is isotopically equivalent to the identity; (ii) `f` is Teichmüller equivalent to the identity; (iii) `f` is
circle equivalent to the identity. Modelling: `f` is `K`-quasiconformal and the isotopy in (i) is through
`K′`-quasiconformal maps with `K′` depending only on `K` (Definition 5): `∀ K ∃ K′`. -/
theorem thm5_3 (K : ℝ) : ∃ K' : ℝ, ∀ (R : Type u) [TopologicalSpace R] [T2Space R] [ConnectedSpace R]
    [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (p : UpperHalfPlane → R), IsFuchsian Γ → IsUniformization Γ p →
    ∀ f : R ≃ₜ R, IsKQCRS f K →
      List.TFAE [IsIsotopyEquiv p K' (Y₀ := selfBundle R) (Y₁ := selfBundle R) f (Homeomorph.refl R),
        IsTeichEquiv p (Y₀ := selfBundle R) (Y₁ := selfBundle R) f (Homeomorph.refl R),
        IsCircleEquiv p (Y₀ := selfBundle R) (Y₁ := selfBundle R) f (Homeomorph.refl R)] := by
  sorry

/-- **Corollary 1** (§5.2, l. 5091). A quasiconformal map `f` with domain `R` represents the basepoint of `T(R)` if
and only if there is a conformal map `c : f(R) → R` such that `c ∘ f` is isotopic to the identity through
quasiconformal maps with uniformly bounded distortion. Modelling: the class of `f` is that of its Beltrami
coefficient `μ` (`HasBeltramiCoeff f μ`), the basepoint that of `0`; "uniformly bounded" is `∃ K′`. -/
theorem cor5_3_1 [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) {Y : RSBundle.{u}} (f : R ≃ₜ Y.carrier) (hf : IsQCRS f) (μ : beltramiBall R)
    (hμ : HasBeltramiCoeff f μ.1) (h0 : (0 : R → ℂ → ℂ) ∈ beltramiBall R) :
    Quot.mk (teichRel p) μ = Quot.mk (teichRel p) ⟨0, h0⟩ ↔
      ∃ K' : ℝ, IsIsotopyEquiv p K' (Y₁ := selfBundle R) f (Homeomorph.refl R) := by
  sorry

/-- **Corollary 2** (§5.2, l. 5093). A quasiconformal map `f` with domain `R` represents the basepoint of `T(R)` if
and only if the normalized lift `w_f` of `f` extends continuously to the identity of `ℝ̂`. -/
theorem cor5_3_2 [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) {p : UpperHalfPlane → R}
    (hp : IsUniformization Γ p) {Y : RSBundle.{u}} (f : R ≃ₜ Y.carrier) (hf : IsQCRS f) (μ : beltramiBall R)
    (hμ : HasBeltramiCoeff f μ.1) (h0 : (0 : R → ℂ → ℂ) ∈ beltramiBall R) :
    Quot.mk (teichRel p) μ = Quot.mk (teichRel p) ⟨0, h0⟩ ↔
      ∃ (p₀ : UpperHalfPlane → Y.carrier) (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (G : ExtPlane → ExtPlane),
        (∃ Γ₀, IsFuchsian Γ₀ ∧ IsUniformization Γ₀ p₀) ∧ IsNormalizedLift p p₀ f F G ∧
          ∀ x ∈ extRealLine, G x = x := by
  sorry

/-- **Unlabelled** (§5.2 and §6.4, l. 5770 "We identify `M(R)` with `M(G)` and `T(R)` with `T(G)`", l. 6313
"`T(R)` is isometrically isomorphic to the space of equivalence classes of Beltrami coefficients on `ℍ`"). For
`R = ℍ/Γ` (`Γ` Fuchsian, fixed-point free) there is a bijection `T(R) ≅ T(Γ)` which carries the basepoint to the
origin and the Teichmüller metric `teichDist` to `LiZhongQC.teichDistanceGamma`. Modelling: the existence of such an
isometric bijection (the book's map lifts the Beltrami coefficients to `ℍ`, which Corollary 2 makes well defined). -/
theorem para5_2_teichGamma_equiv [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) (h0 : (0 : R → ℂ → ℂ) ∈ beltramiBall R) :
    ∃ e : TeichSpace R p ≃ LiZhongQC.TeichGamma Γ,
      e (Quot.mk (teichRel p) ⟨0, h0⟩) = LiZhongQC.TeichGamma.origin Γ ∧
        ∀ P Q, LiZhongQC.teichDistanceGamma (e P) (e Q) = teichDist p P Q := by
  sorry

/-- **Theorem 4** (§5.2, l. 5099). Let `f` and `g` be quasiconformal maps with domain `R`. Then the following are
equivalent: (i) `f` is isotopically equivalent to `g`; (ii) `f` is Teichmüller equivalent to `g`; (iii) `f` is
circle equivalent to `g`. Modelling: as Theorem 3, `f` and `g` `K`-quasiconformal, `∀ K ∃ K′`. -/
theorem thm5_4 (K : ℝ) : ∃ K' : ℝ, ∀ (R : Type u) [TopologicalSpace R] [T2Space R] [ConnectedSpace R]
    [ChartedSpace ℂ R] [IsManifold 𝓘(ℂ) ω R] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
    (p : UpperHalfPlane → R), IsFuchsian Γ → IsUniformization Γ p →
    ∀ (Y₀ Y₁ : RSBundle.{u}) (f : R ≃ₜ Y₀.carrier) (g : R ≃ₜ Y₁.carrier), IsKQCRS f K → IsKQCRS g K →
      List.TFAE [IsIsotopyEquiv p K' f g, IsTeichEquiv p f g, IsCircleEquiv p f g] := by
  sorry

end GardinerLakic2000
