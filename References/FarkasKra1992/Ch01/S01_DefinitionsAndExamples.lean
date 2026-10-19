import References.Forster1981.Ch01.S04_BranchedAndUnbranchedCoverings
import References.Common.RiemannSurface
import References.Common.RiemannSphere
import LiZhongQC.Ch06.S22_RiemannSurfaces

/-!
# Farkas–Kra, Chapter I §1: Definitions and examples

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. I §1 (`full.md` FK1:482–631).

Conventions: a Riemann surface is a charted space over `ℂ` with the binders `[TopologicalSpace M] [T2Space M]`
`[ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]` (`References.IsRiemannSurface` in existential positions);
the book's countable basis is not a binder (it is a consequence, IV.3.18 Corollary 3). `ℂ̂` is
`References.RiemannSphere`. Holomorphic maps are `MDifferentiable 𝓘(ℂ) 𝓘(ℂ)`; conformal maps are
`LiZhongQC.IsBiholomorphic`. The multiplicity of a holomorphic map at a point is `Forster1981.multiplicity` (the book's
ramification number `n`; the branch number is `b_f(P) = n − 1`), and the degree `m` of a non-constant holomorphic map
between compact surfaces is the `m` of `Forster1981.IsHolomorphicCovering f m`.

* Definition I.1.1 (Riemann surface) — exists: `References.IsRiemannSurface`
* I.1.2 (maximal atlases) — omitted: U−, the Zorn's lemma remark (the atlas is the maximal analytic atlas of the charted space)
* I.1.3 (examples: `ℂ`, domains on a surface, the Riemann sphere) — exists: `References.RiemannSphere`
* I.1.4 (coordinate discs, terminology) — omitted: U−
* Definition I.1.5 (holomorphic and conformal maps) — exists: `LiZhongQC.IsBiholomorphic`, `LiZhongQC.RSConformallyEquivalent`
* Theorem I.1.5 (a holomorphic map from a compact surface is constant or surjective) — exists: `Forster1981.thm2_7`
* I.1.5 (`ℋ(M) = ℂ` for compact `M`) — `para1_1_5`
* Definition I.1.6 (ramification number, branch number) — exists: `Forster1981.multiplicity`
* Proposition I.1.6 (the degree of a holomorphic map) — exists: `Forster1981.thm4_24`
* Definition I.1.6 (degree, `m`-sheeted) — exists: `Forster1981.IsHolomorphicCovering`
* I.1.7 (Riemann surfaces are smooth manifolds; every orientable surface carries a structure) — omitted: U−
-/

open scoped Manifold ContDiff Topology References
open Set Filter

noncomputable section

namespace FarkasKra1992

/-- **Unlabelled** (Ch. I §1.5, FK1:566–568, "In particular `ℋ(M) = ℂ`"). The holomorphic functions on a compact
Riemann surface are the constants: `ℋ(M) = ℂ`. -/
theorem para1_1_5 {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] [CompactSpace M] {f : M → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ∃ c : ℂ, ∀ x, f x = c := by
  sorry

end FarkasKra1992
