import References.Nag1988.Ch05.S02_UniversalFamily

/-!
# Nag, Chapter 2 §2.8: Subgroups of the modular group and intermediate moduli spaces

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 2 §2.8 (`full.md` N1:4591–4805; folder
`The Complex Analytic Theory … 10dae1e9`, cited `N1:<line>`). New: Proposition 2.8.1 (orbit spaces of free properly discontinuous
actions on manifolds).

* Proposition (2.8.1: the quotient of a manifold by a properly discontinuous, fixed point free group of homeomorphisms is a
  manifold of the same dimension and the quotient map is a covering; for biholomorphic actions the quotient is a complex
  manifold and the quotient map is holomorphic; N1:4459) — `prop2_8_1_real`, `prop2_8_1_complex` (the uniqueness of the
  complex structure making the quotient map holomorphic is an omitted part: the charts are determined by the local
  biholomorphism q)
* Theorem (2.8.1: for `G` finitely generated of the first kind, the Riemann space `R(G)` is a finite-dimensional normal complex
  space of pure dimension `3g - 3 + n`; N1:4469) — omitted: needs the notion of a normal complex space (Cartan's quotient
  theorem), which is not in the project (the same obstruction as for Nag Ch. 5, item 2.12); the orbit-space description
  `R(G) = T(G)/Mod(G)` is `Nag1988.prop2_4_1_riemann` / `LiZhongQC.eq28_1_moduli_eq_quotient`
* Section 2.8.2 (`π₁(T/S) = S` for free `S`; Armstrong; N1:4473), Proposition 2.8.3 (Hurwitz–Serre; N1:4535), Section 2.8.4 (N1:4579)
  — omitted: the earlier leader ruling (algebraic topology of orbit spaces; Armstrong's theorem is not a Teichmüller statement)
* Theorem 2.8.5 (Torelli covers `U(0, n+3)`, `U(1, n+1)`; N1:4597) — omitted: earlier leader ruling
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff

noncomputable section

namespace Nag1988

/-- **Proposition** (§2.8.1; N1:4459), topological part. Let a group `S` act on a topological `n`-manifold `T` by homeomorphisms,
properly discontinuously and without fixed points (`s • x = x` only for `s = 1`). Then the orbit space is Hausdorff, locally
Euclidean of dimension `n` (it carries a charted structure over `ℝⁿ`), and the quotient map is a covering map. -/
theorem prop2_8_1_real {T S : Type*} [TopologicalSpace T] [T2Space T] [Group S] [MulAction S T] [ContinuousConstSMul S T]
    {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) T] [ProperlyDiscontinuousSMul S T]
    (hfree : ∀ (s : S) (x : T), s • x = x → s = 1) :
    T2Space (MulAction.orbitRel.Quotient S T) ∧
      Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin n)) (MulAction.orbitRel.Quotient S T)) ∧
        IsCoveringMap (Quotient.mk (MulAction.orbitRel S T)) := by
  sorry

/-- **Proposition** (§2.8.1; N1:4459), holomorphic part. If moreover `T` is a complex manifold of dimension `n` and `S` acts by
biholomorphic automorphisms, the orbit space (with its quotient topology) carries a complex structure for which `q` is holomorphic (a holomorphic
covering). -/
theorem prop2_8_1_complex {T S : Type*} [TopologicalSpace T] [T2Space T] [Group S] [MulAction S T] [ContinuousConstSMul S T]
    {n : ℕ} [ChartedSpace (EuclideanSpace ℂ (Fin n)) T] [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω T]
    [ProperlyDiscontinuousSMul S T] (hfree : ∀ (s : S) (x : T), s • x = x → s = 1)
    (hhol : ∀ s : S, MDifferentiable 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) (fun x : T => s • x)) :
    ∃ _ : ChartedSpace (EuclideanSpace ℂ (Fin n)) (MulAction.orbitRel.Quotient S T),
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ω (MulAction.orbitRel.Quotient S T) ∧
        MDifferentiable 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n))
          (Quotient.mk (MulAction.orbitRel S T) : T → MulAction.orbitRel.Quotient S T) := by
  sorry

end Nag1988
