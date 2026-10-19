import References.FarkasKra1992.Ch01.S04_IntegrationFormulae
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Farkas–Kra, Chapter II §1: Hilbert space theory — a quick review

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. II §1 (`full.md` FK1:1351–1392).

This section recalls the orthogonal projection theorem onto closed subspaces of a Hilbert space; it is in Mathlib.

* II.1.1 (orthogonal complement `F^⊥` of a subspace) — exists: `Submodule.orthogonal`
* Theorem II.1.2 (every `h = f + g` with `f ∈ F`, `g ∈ F^⊥`, uniquely; `f` minimizes `‖h − φ‖`) — exists: `Submodule.isCompl_orthogonal_of_hasOrthogonalProjection`, `Submodule.exists_norm_eq_iInf_of_complete_subspace`
* Theorem II.1.3 (the orthogonal projection `P`: `‖P‖ = 1`, `P² = P`, `ker P = F^⊥`) — exists: `Submodule.orthogonalProjectionOnto`, `Submodule.ker_orthogonalProjectionOnto`
-/

namespace FarkasKra1992

end FarkasKra1992
