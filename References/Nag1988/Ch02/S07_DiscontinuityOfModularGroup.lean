import References.Nag1988.Ch05.S02_UniversalFamily
import LiZhongQC.Ch06.S23_QCOnSurfaces

/-!
# Nag, Chapter 2 §2.7: Discontinuity of the modular group action on finite-dimensional Teichmüller spaces

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 2 §2.7 (`full.md` N1:4427–4590; folder
`The Complex Analytic Theory … 10dae1e9`, cited `N1:<line>`). New: Proposition 2.7.1 (the discreteness of the quasiconformal
mapping class group, a purely topological fact); Theorems 2.7.3–2.7.4 are passed.

**Model.** `X` is a Riemann surface of finite conformal type `(g, k)` (`LiZhongQC.IsFiniteType X g k 0`), `Q(X)` the quasiconformal
self-homeomorphisms (`LiZhongQC.IsQCRS`). Convergence `φ_n → 1_X` uniformly on compact subsets is convergence in the
compact-open topology of `C(X, X)`; homotopy is `ContinuousMap.Homotopic`.

* Section 2.7.1 (reduction of the proper discontinuity to the base point; N1:4443) — omitted: argument
* Proposition (2.7.1: `φ_n ∈ Q(X)`, `φ_n → 1_X` uniformly on compacta implies `φ_n ≃ 1_X` for all large `n`; N1:4453) — `prop2_7_1`
* Remark 2.7.2 (compact surfaces; Mangler–Epstein) — omitted: remark (pointwise convergence on compact `X` is a special case of
  uniform convergence on compacta once the maps are quasiconformal; the second remark is a comment)
* Theorem 2.7.3 (`Mod(G)` acts properly discontinuously by isometries on `T(G)`, `G` finitely generated of the first kind; N1:4461)
  — exists: `LiZhongQC.thm30_3` (closed surfaces), `GardinerLakic2000.thm10_4` (the general case: Gardiner–Lakic Theorem 10.4,
  finitely generated of the first kind)
* Section 2.7.4 (Lemmas A, B: the normalizer is Fuchsian; `tr²` discrete; N1:4471) — exists: `LiZhongQC.lengthSpectrum_discrete`,
  `GardinerLakic2000.lemma10_3` (the normalizer of a non-cyclic Fuchsian group is Fuchsian), `GardinerLakic2000.thm10_5`
  (N(Γ)/Γ is finite)
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace Nag1988

open LiZhongQC (IsFiniteType IsQCRS)

/-- **Proposition** (§2.7.1; N1:4453). Let `X` be a Riemann surface of finite conformal type `(g, k)` with `2g - 2 + k > 0`. If
`φ_n ∈ Q(X)` converge to the identity uniformly on compact subsets of `X`, then `φ_n` is homotopic to `1_X` for all
sufficiently large `n`. -/
theorem prop2_7_1 {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {g k : ℕ} (hX : IsFiniteType X g k 0) (hχ : 0 < 2 * (g : ℤ) - 2 + k) (φ : ℕ → (X ≃ₜ X)) (hφ : ∀ n, IsQCRS (φ n))
    (hlim : Tendsto (fun n => (⟨φ n, (φ n).continuous⟩ : C(X, X))) atTop (𝓝 (ContinuousMap.id X))) :
    ∀ᶠ n in atTop, ContinuousMap.Homotopic (⟨φ n, (φ n).continuous⟩ : C(X, X)) (ContinuousMap.id X) := by
  sorry

end Nag1988
