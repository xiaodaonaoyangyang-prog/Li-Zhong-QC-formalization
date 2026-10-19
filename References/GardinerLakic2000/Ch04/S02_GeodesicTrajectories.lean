import References.GardinerLakic2000.Ch04.S01_HorizontalTrajectories

/-!
# Gardiner–Lakic 2000, Ch. 4 §4.2 Geodesic trajectories

Source `teichmuller.txt`, lines 3739–3818. The standing assumption of §4.1 (finite analytic type) is kept.

* Lemma 1 (horizontal arcs with injective lift are shortest in their homotopy class, l. 3742) — `lemma4_1`
* Lemma 2 (a self-map homotopic to the identity shortens horizontal segments by at most `M`, l. 3800) — `lemma4_2`

Near misses: `LiZhongQC.thm25_3_unique_geodesic` (the disc) and `LiZhongQC.lemma26_1` (closed surfaces: the same
statement as Lemma 2 without punctures).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace GardinerLakic2000

universe u

variable {R : Type u} [TopologicalSpace R] [T2Space R] [ConnectedSpace R] [ChartedSpace ℂ R]
  [IsManifold 𝓘(ℂ) ω R]

/-- **Lemma 1** (§4.2, l. 3742). Let `φ` be a holomorphic quadratic differential on `R` (of finite analytic type) and
`π : R̃ → R` its universal covering. Let `α` be an arc of a horizontal trajectory of `φ` whose lift `α̃` to `R̃` is
one-to-one, and `γ` an arc with the same end points, homotopic to `α` with fixed end points. Then
`ℓ_φ(α) ≤ ℓ_φ(γ)`. Modelling: the universal covering is any covering map from a simply connected space; the lift
is a path `α̃` with `π ∘ α̃ = α`. -/
theorem lemma4_1 {g n : ℕ} (hR : IsFiniteAnalyticType R g n) {φ : R → ℂ → ℂ} (hφ : LiZhongQC.IsHolQuadDiff φ)
    {E : Type u} [TopologicalSpace E] [SimplyConnectedSpace E] {cov : E → R} (hcov : IsCoveringMap cov)
    {a b : R} (α γ : Path a b) (hα : LiZhongQC.IsHorizontalArcRS φ α) {a' b' : E} (α' : Path a' b')
    (hlift : ∀ t, cov (α' t) = α t) (hinj : Function.Injective α') (hγ : γ.Homotopic α) :
    LiZhongQC.phiLengthPath φ α ≤ LiZhongQC.phiLengthPath φ γ := by
  sorry

/-- **Lemma 2** (§4.2, l. 3800). Let `R` be of finite analytic type, `φ` a holomorphic quadratic differential on `R`
with `‖φ‖ < ∞`, and `f` a quasiconformal self-map of `R` homotopic to the identity. Then there is a constant `M`
(depending on `φ` and `f`) such that `ℓ_φ(α) ≤ ℓ_φ(f(α)) + M` for every noncritical horizontal segment `α` of `φ`.
Modelling: for finite analytic type the covering group is of the first kind and "homotopic relative to the boundary"
is plain homotopy (B0.2); `ℓ_φ(f(α))` is the length of the image curve up to reparametrization
(`LiZhongQC.phiLengthPathInv`, as in `LiZhongQC.lemma26_1`). -/
theorem lemma4_2 {g n : ℕ} (hR : IsFiniteAnalyticType R g n) {φ : R → ℂ → ℂ} (hφ : LiZhongQC.IsHolQuadDiff φ)
    (hφn : LiZhongQC.quadDiffNorm φ < ⊤) (f : R ≃ₜ R) (hf : LiZhongQC.IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f : C(R, R)) (ContinuousMap.id R)) :
    ∃ M : ℝ, ∀ (a b : R) (α : Path a b), LiZhongQC.IsHorizontalArcRS φ α →
      LiZhongQC.phiLengthPath φ α ≤ LiZhongQC.phiLengthPathInv φ (α.map f.continuous) + ENNReal.ofReal M := by
  sorry

end GardinerLakic2000
