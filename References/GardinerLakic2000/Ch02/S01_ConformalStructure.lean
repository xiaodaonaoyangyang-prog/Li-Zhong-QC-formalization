import References.GardinerLakic2000.Ch01.S07_HausdorffDimension

/-!
# Gardiner–Lakic 2000, Ch. 2 §2.1 Conformal structure

Source `teichmuller.txt`, lines 1105–1139 (Chapter 2, introduction and §2.1).

* Definition 1 (Riemann surface, l. 1118) — exists: `References.IsRiemannSurface` (the Mathlib charted-space
  convention of the shared layer and of LiZhongQC §22; in statements it is written as instance binders)
* Definition 2 (conformal map between Riemann surfaces, l. 1126) — exists: `MDifferentiable` (with the model
  𝓘(ℂ) on both sides)
* Definition 2 (`K`-quasiconformal map between Riemann surfaces, l. 1126) — exists: `LiZhongQC.IsKQCRS` (every local
  expression is K-quasiconformal; the book's pointwise analytic form is the same notion by Definitions 1.2 and 1.4)
* Definition 3 (conformally equivalent surfaces, l. 1136) — exists: `LiZhongQC.RSConformallyEquivalent`
* Definition 4 (the quasiconformal moduli space `𝓜(R)`, l. 1138; used in Ch. 10) — `RSBundle`, `qcModuliSpace`

Not items: the orientation claim (l. 1124) and the well-definedness of `K`-quasiconformality (l. 1128–1134), U−; the
chapter introduction (translation length as a `K`-invariant, l. 1109, not proved in the chapter and not cited).
Modelling: surfaces in existential positions and in quotients are bundled as `RSBundle` (carrier, topology, charts,
and the proposition `References.IsRiemannSurface`; no proof fields). The project's `LiZhongQC.ClosedRS` (closed
surfaces) and `LiZhongQC.FiniteTypeRS` (finite type) are special bundles and are not reused here.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (IsQCRS RSConformallyEquivalent)

/-- Helper (for Definitions 4, 6, 7 and §2.4). A Riemann surface as a bundle: a carrier type with its topology and
its atlas of charts to `ℂ`, which form a Riemann surface (`References.IsRiemannSurface`). -/
structure RSBundle : Type (u + 1) where
  /-- The underlying set of the surface. -/
  carrier : Type u
  /-- Its topology. -/
  [top : TopologicalSpace carrier]
  /-- Its atlas. -/
  [charted : ChartedSpace ℂ carrier]
  /-- Hausdorff, connected, complex analytic atlas. -/
  isRS : References.IsRiemannSurface carrier

attribute [instance] RSBundle.top RSBundle.charted

/-- **Definition 4** (§2.1, l. 1138). The quasiconformal moduli space `𝓜(R)`: the conformal equivalence classes of
Riemann surfaces quasiconformally equivalent to `R` (surfaces in the universe of `R`). -/
def qcModuliSpace (R : Type u) [TopologicalSpace R] [ChartedSpace ℂ R] : Type (u + 1) :=
  Quot fun (Y Z : {Y : RSBundle.{u} // ∃ f : R ≃ₜ Y.carrier, IsQCRS f}) =>
    RSConformallyEquivalent Y.1.carrier Z.1.carrier

end GardinerLakic2000
