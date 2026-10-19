import References.GardinerLakic2000.Ch12.S04_IntersectionNumbers

/-!
# Gardiner–Lakic 2000, Ch. 12 §12.5 Projectivizations

Source `teichmuller.txt`, lines 9187–9201.

* Theorem (Thurston, quoted with its MST-coordinates argument, l. 9190; used in the proof of Theorem 1, l. 9196): the
  image of `𝒮′` is dense in `𝒫𝓜𝓕` — `para12_5_thurston_density`

Not items (DESIGN §3): the projective spaces and the diagram of Figure 12.2 (l. 9188), the density of the image of `𝒮`
(l. 9192, "not essential"), the realization of projective classes (l. 9196, proof of Theorem 1), the density of
Jenkins–Strebel differentials (l. 9198, a remark; also omitted in part C).

**Modelling.** Density in `𝒫𝓜𝓕` for the product topology of heights: every measured foliation is the limit, up to
positive factors `cₙ`, of the intersection vectors of multicurves (an element of `𝒮′` counts each component, so no
integer weights are needed).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (Loop)

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

/-- **Theorem** (Thurston [FLP79], §12.5, l. 9190). On a surface of finite analytic type the projective classes of
elements of `𝒮′` are dense in `𝒫𝓜𝓕`: for every measured foliation `|dv|` there are multicurves `γⁿ` and `cₙ > 0`
with `cₙ Σⱼ i(γⁿⱼ, σ) → h_v[σ]` for every `σ ∈ 𝒮`. -/
theorem para12_5_thurston_density {g n : ℕ} (hR : IsFiniteAnalyticType R g n)
    (F : LiZhongQC.FiniteTypeStructure R g n 0) {ι : Type*} {U : ι → Set R} {v : ι → R → ℝ}
    {Sing : Set F.X.carrier} {k : F.X.carrier → ℤ} (hv : IsMeasuredFoliation F U v Sing k) :
    ∃ (m : ℕ → ℕ) (γ : ∀ l, Fin (m l) → Loop R) (c : ℕ → ℝ), (∀ l, IsMulticurve (γ l)) ∧ (∀ l, 0 < c l) ∧
      ∀ σ : Loop R, IsEssentialLoop σ → Tendsto (fun l => c l * ∑ j, ((intersectionNumber (γ l j) σ : ℝ≥0∞)).toReal)
        atTop (𝓝 (folHeight U v σ).toReal) := by
  sorry

end GardinerLakic2000
