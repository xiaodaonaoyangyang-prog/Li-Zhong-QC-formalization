import References.Forster1981.Ch01.S02_ElementaryPropertiesOfHolomorphicMappings

/-!
# Forster, Chapter 1 §3: Homotopy of curves, the fundamental group

Source: O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §3 (`full.md` F1:733–1010).

Conventions: a curve from `a` to `b` is a `Path a b`; homotopy of curves is `Path.Homotopic` (homotopy relative to the end
points, Forster's (i)–(iii)); `π₁(X, a)` is Mathlib's `FundamentalGroup X a`, whose multiplication `p * q = q.trans p`
is the opposite of Forster's `cl(u)·cl(v) = cl(u·v)` (the two groups are isomorphic by inversion; statements below are
insensitive to the order). Reading (misprint, F1:802–816): the inverse curve `u⁻` of a curve from `a` to `b` runs from
`b` to `a`.

* Definition (curve, arcwise connected, locally arcwise connected, §3 preliminaries, F1:737) — exists: `Path`,
  `PathConnectedSpace`, `LocallyPathConnectedSpace`
* Definition 3.1 (homotopic curves, F1:741) — exists: `Path.Homotopic`
* Theorem 3.2 (homotopy is an equivalence relation, F1:754) — exists: `Path.Homotopic.equivalence`
* Lemma 3.3 (reparametrization, F1:786) — exists: `Path.Homotopy.reparam`
* Definition 3.4 (product curve, inverse curve, F1:802) — exists: `Path.trans`, `Path.symm`
* Remark after 3.4 (compatibility of product and inverse with homotopy, F1:818) — exists: `Path.Homotopic.hcomp`,
  `Path.Homotopic.symm₂`
* Definition 3.5 (constant curve, F1:820) — exists: `Path.refl`
* Theorem 3.6 (F1:822) — exists: `Path.Homotopic.refl_trans`, `Path.Homotopic.trans_refl`, `Path.Homotopic.trans_symm`,
  `Path.Homotopic.trans_assoc`
* Definition 3.7 (closed curve, null-homotopic, F1:876) — exists: `Path.Homotopic`
* Theorem and definition 3.8 (the fundamental group, F1:878) — exists: `FundamentalGroup`
* Paragraph 3.9 (dependence on the base point, F1:888) — exists: `FundamentalGroup.fundamentalGroupMulEquivOfPath`
* Definition 3.10 (simply connected, F1:920) — exists: `SimplyConnectedSpace`
* Theorem 3.11 (F1:924) — exists: `SimplyConnectedSpace.paths_homotopic`
* Example 3.12(a) (star-shaped sets are simply connected, F1:930) — exists: `StarConvex.contractibleSpace`,
  `SimplyConnectedSpace.ofContractible`
* Example 3.12(b) (ℙ¹ is simply connected, F1:938) — `example3_12_b`
* Definition 3.13 (free homotopic closed curves, F1:956) — `AreFreeHomotopic`
* Remark after 3.13 (a free homotopy is a conjugation, F1:972) — `rem3_13`
* Theorem 3.14 (F1:977) — `thm3_14`
* Paragraph 3.15 (functorial behavior, F1:981) — exists: `FundamentalGroup.map`, `Path.Homotopic.map`

Omitted (U−): the claim "connected and locally arcwise connected implies arcwise connected" (F1:739, the convention),
the remark on deformations (F1:741), the remark on bracketings (F1:874), the dependence on the connecting curve and the
canonical isomorphism for abelian `π₁` (F1:888–918), `π₁ = 0` notation (F1:920), `(g ∘ f)_* = g_* ∘ f_*` (F1:981).
-/

open scoped Manifold ContDiff Topology unitInterval References
open Set Filter

namespace Forster1981

/-- **Definition 3.13** (free homotopic closed curves, Ch. 1 §3, F1:956). Two closed curves `u` at `x` and `v` at `y` are
*freely homotopic* if there is a continuous map `A : I × I → X` with `A(t, 0) = u(t)`, `A(t, 1) = v(t)` and
`A(0, s) = A(1, s)` for all `s` (every intermediate curve is closed). -/
def AreFreeHomotopic {X : Type*} [TopologicalSpace X] {x y : X} (u : Path x x) (v : Path y y) : Prop :=
  ∃ A : C(I × I, X), (∀ t, A (t, 0) = u t) ∧ (∀ t, A (t, 1) = v t) ∧ ∀ s, A (0, s) = A (1, s)

/-- **Example 3.12(b)** (Ch. 1 §3, F1:938). The Riemann sphere `ℙ¹` is simply connected. -/
theorem example3_12_b : SimplyConnectedSpace References.RiemannSphere := by
  sorry

/-- **Remark after Definition 3.13** (Ch. 1 §3, F1:972). If the closed curves `u` at `x` and `v` at `y` are freely
homotopic, there is a curve `w` from `x` to `y` such that `u` is homotopic (relative to the end points) to `w · v · w⁻`. -/
theorem rem3_13 {X : Type*} [TopologicalSpace X] {x y : X} {u : Path x x} {v : Path y y}
    (h : AreFreeHomotopic u v) : ∃ w : Path x y, Path.Homotopic u ((w.trans v).trans w.symm) := by
  sorry

/-- **Theorem 3.14** (Ch. 1 §3, F1:977). A pathwise connected space `X` is simply connected iff any two closed curves in
`X` are freely homotopic. -/
theorem thm3_14 {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] :
    SimplyConnectedSpace X ↔ ∀ (x y : X) (u : Path x x) (v : Path y y), AreFreeHomotopic u v := by
  sorry

end Forster1981
