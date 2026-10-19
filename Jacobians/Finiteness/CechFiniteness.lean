/-
  `H¹(X, 𝒪_D)` finiteness (Forster 14.9) — the Montel compactness input.

  The cochain restriction between a cover and a relatively-compact shrinking is a compact
  operator (Montel), so by the Schwartz finiteness lemma
  (`SchwartzFiniteness.finiteDimensional_quotient_range_add_compact`, Forster 14.8) the Čech `H¹`
  is finite-dimensional.  This file proves the de-bundled compact-restriction lemma that the
  cochain layer is built on, reusing the plain-function disk lemmas of `Montel/Compactness.lean`.
-/
import Jacobians.Forms.Compactness
open Metric Topology BoundedContinuousFunction
open Jacobians.Montel

namespace Jacobians.Dolbeault.CechFiniteness

/-! ### The de-bundled compact-restriction lemma (Montel core for cochains)

A sup-`M`-bounded family of functions holomorphic on an open `U ⊆ ℂ`, restricted to a compact
convex `K ⋐ U`, is relatively compact in `K →ᵇ ℂ`. This is the plain-function analogue of the
bundle-level `isCompact_closure_image_inner_bcf`, without the `localRep`/cotangent bookkeeping.
It is the engine that makes the cochain restriction a compact operator. -/

/-! ### From this lemma to `DolbeaultLadder.finiteDimensional_cechH1`

The assembly built on this Montel core:

* `BddHol` — the sup-norm Banach space `BddHol U` of bounded holomorphic functions on an open
  `U ⊆ ℂ` (a closed subspace of the bounded continuous functions, complete), and the restriction
  CLM `BddHol U → (K →ᵇ ℂ)` for compact `K ⋐ U`, a compact operator via the lemma above
  (`isCompactOperator_iff_isCompact_closure_image_closedBall`).
* `ChartDiskFiniteness` / `ChartDiskLeray` — the cochain Banach spaces over the chart-disk cover
  and its shrinking; the cochain restriction `C^q(𝔘) → C^q(𝔙)` is a finite product of disk
  restrictions, hence compact, and the Leray two-cover map is surjective on `H¹`
  (`H¹(disk, 𝒪) = 0`); Schwartz then gives `H¹(𝔙, 𝒪)` finite-dimensional.
* `CechFinitenessAssembly` / `CechFinitenessDtwist` — the comparison with the germ-class `cechH1`
  of `CechComplex` (codiscrete junk does not change `H¹`) and the twist to general `D`.
-/

end Jacobians.Dolbeault.CechFiniteness
