import References.GardinerLakic2000.Ch09.S06_UniqueHolomorphicMotions

/-!
# Gardiner–Lakic 2000, Ch. 10 §10.1 MCG for the covering group (with the chapter introduction)

Source `teichmuller.txt`, lines 7903–7953 (Chapter 10, introduction and §10.1).

* Definition 1 (the Teichmüller mapping class group `MCG(R)`, l. 7933; recalled at l. 6591) — `mcgRS`
* Definition (`QC(Γ)`, the normalizer of `Γ` in the quasiconformal self-maps of ℍ, l. 7937) — exists:
  `GardinerLakic2000.qcNormalizer` (§8.1, where it is first used)
* Definition (the homomorphism `χ : QC(Γ) → QC(R)`, (10.1), l. 7941) — `IsInducedMap`
* Definition (`QC₀(Γ)`, the elements fixing `ℝ` pointwise, l. 7946) — `qcNormalizer0`
* Definition 2 (`MCG(Γ) = [QC(Γ)/QC₀(Γ)]/Γ`, l. 7948) — `mcgGamma`
* Theorem 1 (l. 7950) — `thm10_1`

Not items: the homomorphism `H : MCG(R) → aut(T(R))` and the remarks on injectivity and surjectivity (l. 7913–7922;
the content of `para8_0_geometric_hol`); "`ker χ = Γ`, `QC(Γ)/Γ ≅ QC(R)`" (l. 7945, inside Theorem 1). Modelling
(leader calibration C0.3): `MCG(R)` is the quotient (`Quot`) of the quasiconformal self-homeomorphisms of `R` by
homotopy modulo the ideal boundary (`LiZhongQC.HomotopicModBoundary`, the book's "Teichmüller equivalent to the
identity"); `MCG(Γ)` is the quotient of `QC(Γ)` by "the boundary values on `ℝ` agree up to an element of `Γ`", which
is `[QC(Γ)/QC₀(Γ)]/Γ`. Theorem 1 is stated as a bijection compatible with `χ` (no group instances).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsQCRS HomotopicModBoundary h36p_m IsFuchsian ActsFreely IsUniformization)

/-- **Definition 1** (§10.1, l. 7933). The Teichmüller mapping class group `MCG(R)`: quasiconformal
self-homeomorphisms of `R` modulo homotopy fixing the ideal boundary pointwise. -/
def mcgRS (R : Type u) [TopologicalSpace R] [ChartedSpace ℂ R] (p : UpperHalfPlane → R) : Type u :=
  Quot fun g₁ g₂ : {g : R ≃ₜ R // IsQCRS g} => HomotopicModBoundary p p (g₁.1 : R → R) (g₂.1 : R → R)

/-- **Definition** (`χ`, (10.1), §10.1, l. 7941). `g = χ(h)` is the self-map of `R = ℍ/Γ` induced by `h ∈ QC(Γ)`:
`g(π(z)) = π(h(z))`. -/
def IsInducedMap {R : Type u} [TopologicalSpace R] (p : UpperHalfPlane → R) (h : ℂ → ℂ) (g : R → R) : Prop :=
  ∀ τ : UpperHalfPlane, g (p τ) = p (UpperHalfPlane.ofComplex (h τ))

/-- **Definition** (`QC₀(Γ)`, §10.1, l. 7946). The elements of `QC(Γ)` fixing every real point (their boundary map
`qcBdry h` is the identity on `ℝ`, hence on `ℝ̂`). -/
def qcNormalizer0 (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → ℂ) :=
  {h | h ∈ qcNormalizer Γ ∧ ∀ x : ℝ, qcBdry h ((x : ℂ) : LiZhongQC.ExtPlane) = ((x : ℂ) : LiZhongQC.ExtPlane)}

/-- **Definition 2** (§10.1, l. 7948). `MCG(Γ) = [QC(Γ)/QC₀(Γ)]/Γ`: elements of `QC(Γ)` identified when their boundary
values on `ℝ` (the boundary maps `qcBdry`, in `ℂ̂`) differ by an element of `Γ`. -/
def mcgGamma (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type :=
  Quot fun h₁ h₂ : qcNormalizer Γ => ∃ γ ∈ Γ, ∀ x : ℝ,
    qcBdry h₂.1 ((x : ℂ) : LiZhongQC.ExtPlane) =
      LiZhongQC.mobiusSL (LiZhongQC.slRealToComplex γ) (qcBdry h₁.1 ((x : ℂ) : LiZhongQC.ExtPlane))

/-- **Theorem 1** (§10.1, l. 7950). The map `χ` induces an isomorphism of `MCG(Γ)` onto `MCG(R)`: a bijection sending
the class of `h` to the class of the induced self-map of `R`. -/
theorem thm10_1 {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
    [IsManifold 𝓘(ℂ) ω R] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) {p : UpperHalfPlane → R} (hp : IsUniformization Γ p) :
    ∃ Φ : mcgGamma Γ → mcgRS R p, Function.Bijective Φ ∧
      ∀ (h : qcNormalizer Γ) (g : {g : R ≃ₜ R // IsQCRS g}), IsInducedMap p h.1 (g.1 : R → R) →
        Φ (Quot.mk _ h) = Quot.mk _ g := by
  sorry

end GardinerLakic2000
