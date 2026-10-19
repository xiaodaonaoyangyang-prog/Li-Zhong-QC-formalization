import References.ImayoshiTaniguchi1992.Ch03.S02_FenchelNielsen
import LiZhongQC.Ch08.S29_TeichmullerMetric
import References.Lehto1987.Ch05.S09_TeichmullerSpacesOfCompactSurfaces

/-!
# Imayoshi–Taniguchi, Chapter 5 §5.2: Teichmüller mappings and Teichmüller's theorems

Source: Y. Imayoshi, M. Taniguchi, *An Introduction to Teichmüller Spaces*, Springer 1992, Ch. 5 §5.2 (`full.md` IT1:4474–4777,
folder `An Introduction to Teichmuller Spaces … ef13744b`).

Conventions as in `Ch05/S01_AnalyticConstruction`; `S₀` is a closed Riemann surface of genus `g ≥ 2` with a fixed
uniformization `p₀` and standard generators `G` (`LiZhongQC.StandardGenerators`), `F_g` is IT's Fricke space with the coordinates
`frickeCoordinatesIT` (`IsFrickeCoordsIT p₀ G m c`: `c` are the Fricke coordinates of the marked surface `m`, a relation, since the
coordinates depend on the class only; Lemma 5.6), the topology of `T(R)` is that of the Teichmüller distance `LiZhongQC.teichDistance`
and that of `F_g ⊆ ℝ^{6g-6}` the product (sup) metric of `FC g`.

* Definition (holomorphic quadratic differentials `A₂(R)`, IT1:4476) — exists: `LiZhongQC.IsHolQuadDiff`
* Definition (formal Teichmüller mapping, Teichmüller mapping, IT1:4542) — exists: `LiZhongQC.IsTeichmullerMap`
* Lemma 5.6 (`Φ_Σ` and `F_g ∘ Φ_Σ` are bijective, IT1:4594) — exists: `LiZhongQC.thm27_fricke_bijection`
* Lemma 5.7 (`T̃ : A₂(R)₁ → F_g` is continuous, IT1:4598) — exists: `LiZhongQC.lemma27_1_continuous_injective`
* Lemma 5.8 (`F_g ∘ Φ_Σ` is continuous, IT1:4666) — `lemma5_8`
* Theorem 5.9 (a Teichmüller mapping is extremal in its homotopy class, uniqueness, IT1:4672) — exists:
  `LiZhongQC.teichmullerMap_isExtremal`, `LiZhongQC.thm26_2_uniqueness`
* Corollary to Theorem 5.9 (`T` and `T̃` are injective, IT1:4682) — exists: `LiZhongQC.lemma27_1_injective`
* Lemma 5.10 (`T̃` has open image and is a homeomorphism onto it, IT1:4700) — exists: `LiZhongQC.deformationImage_isOpen`
* Lemma 5.11 (`T` is a homeomorphism onto its image, IT1:4704) — exists: `LiZhongQC.thm29_1`
* Lemma 5.12 (`T(R)` and `F_g` are connected, IT1:4730) — exists: `LiZhongQC.lemma27_2_connected`
* Lemma 5.13 (`T` and `T̃` are surjective, IT1:4736) — exists: `LiZhongQC.deformationImage_eq_frickeSpace`,
  `LiZhongQC.teichSpace_deformation_bijection`
* Theorem 5.14 (Teichmüller's existence theorem, IT1:4766) — exists: `LiZhongQC.thm27_2_existence`
* Theorem 5.15 (`T : A₂(R)₁ → T(R)` is a surjective homeomorphism, IT1:4770) — exists: `LiZhongQC.thm29_1`
* Corollary to Theorem 5.15 (`T(R)` and `F_g` are homeomorphic to `ℝ^{6g-6}`, IT1:4776) — exists: `LiZhongQC.thm29_1`
-/

open Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace ImayoshiTaniguchi1992

open LiZhongQC (MarkedRS StandardGenerators IsUniformization HasGenus TeichSpace teichDistance)

variable {S₀ : Type} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
  [CompactSpace S₀]

/-- **Lemma 5.8** (Ch. 5 §5.2.2). The map `F_g ∘ Φ_Σ : T(R) → F_g`, which sends the class of a marked surface to its Fricke
coordinates, is continuous: if `[m]` has the Fricke coordinates `c` (`IsFrickeCoordsIT`), then for every `ε > 0` there is `δ > 0`
such that every `[m']` within Teichmüller distance `δ` of `[m]` has Fricke coordinates `c'` with `dist c c' < ε`. -/
theorem lemma5_8 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) (G : StandardGenerators Γ₀ g) (m : MarkedRS S₀) (c : FC g)
    (hc : IsFrickeCoordsIT p₀ G m c) :
    ∀ ε > 0, ∃ δ > 0, ∀ (m' : MarkedRS S₀) (c' : FC g), teichDistance (Quot.mk _ m) (Quot.mk _ m') < δ →
      IsFrickeCoordsIT p₀ G m' c' → dist c c' < ε := by
  sorry

end ImayoshiTaniguchi1992
