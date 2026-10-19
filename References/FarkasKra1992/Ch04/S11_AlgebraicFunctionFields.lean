import References.FarkasKra1992.Ch04.S08_RiemannianMetrics
import References.Forster1981.Ch01.S08_AlgebraicFunctions
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Farkas–Kra, Chapter IV §11: Algebraic function fields in one variable

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. IV §11 (`full.md` FK2:2549–3201).

Conventions: as in `Ch04/S06_ExceptionalSurfaces`; `M` is a compact Riemann surface. A meromorphic function on `M` that is
not constant is a non-constant holomorphic map `M → ℂ̂` (`References.RiemannSphere`); its degree `n` is
`Forster1981.IsHolomorphicCovering f n`. An algebraic relation `P(z, w) ≡ 0`, `P ∈ ℂ[Z, W]` (variable `0` is `Z`, variable
`1` is `W`), is read at the points where `z` and `w` are finite (`finVal` is the finite value). The analytic
configurations (`ℳ*`, Puiseux series, IV.11.1–11.5) are deferred; IV.11.8 is stated through `Forster1981` (8.9).

* IV.11.1–IV.11.5 — deferred: the space `ℳ*` of Puiseux series with its topology and charts and the analytic configurations
  are not in `Forster1981` Part A (only `convLaurent` and analytic continuation of holomorphic germs)
* Proposition IV.11.6 — `finVal`, `IsAlgebraicRelation`, `prop4_11_6`
* Definition IV.11.6 (primitive pair) — `IsPrimitivePair`
* Proposition IV.11.7 — `prop4_11_7`
* Corollary IV.11.8 — `cor4_11_8`
* Proposition IV.11.9 — `prop4_11_9`
* Proposition IV.11.10 — `prop4_11_10`
* Definition IV.11.12 (discrete valuation of rank 1) — `IsDiscreteValuation1`
* Lemma IV.11.13 — exists: `AddValuation.map_add_eq_of_lt_left`

Deferred: IV.11.10 Corollary (`𝒦(M) ≅ ℂ(z)[w]/P(z, w)`: needs a field structure on `𝒦(M)`; `Forster1981.rem1_16_b` states that
it is a field but there is no instance). Waiting for `Forster1981` Part B (order of a meromorphic function): IV.11.14 Lemma,
IV.11.15 Theorem, IV.11.16 Theorem, IV.11.17 Corollaries. Omitted (U−): IV.11.11 (example), the Exercise, the Remark after
IV.11.17.
-/

open scoped Manifold ContDiff MatrixGroups Topology References Forster1981
open Set Filter

noncomputable section

namespace FarkasKra1992

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- The finite value of a point of `ℂ̂` (helper): `finVal ∞ = 0` (junk; only used where the point is finite). -/
def finVal (p : References.RiemannSphere) : ℂ := OnePoint.elim p 0 id

/-- **Algebraic relation** (Ch. IV §11.6, helper). `P(z, w) ≡ 0` for `P ∈ ℂ[Z, W]` and meromorphic functions `z`, `w`: the
polynomial vanishes at the values `(z(x), w(x))` at all points where both are finite (a meromorphic identity: the remaining
points are isolated). -/
def IsAlgebraicRelation (P : MvPolynomial (Fin 2) ℂ) (z w : M → References.RiemannSphere) : Prop :=
  ∀ x : M, z x ≠ References.RiemannSphere.infty → w x ≠ References.RiemannSphere.infty →
    MvPolynomial.eval ![finVal (z x), finVal (w x)] P = 0

/-- **Proposition IV.11.6** (Ch. IV §11.6). If `M` is compact and `w, z ∈ 𝒦(M) ∖ ℂ`, then there exists a polynomial
`P ≠ 0` such that `P(z, w) ≡ 0`. -/
theorem prop4_11_6 [CompactSpace M] {z w : M → References.RiemannSphere} (hz : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) z)
    (hw : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) w) (hz' : ¬ ∃ c, ∀ x, z x = c) (hw' : ¬ ∃ c, ∀ x, w x = c) :
    ∃ P : MvPolynomial (Fin 2) ℂ, P ≠ 0 ∧ IsAlgebraicRelation P z w := by
  sorry

/-- **Primitive pair** (Ch. IV §11.6, Definition). Two non-constant meromorphic functions `z, w ∈ 𝒦(M) ∖ ℂ` form a
*primitive pair* provided the canonical map `φ : M → ℳ*` of Theorem IV.11.5 is one-to-one.
Modelling: `φ` is one-to-one if and only if it has degree 1 onto the analytic configuration, if and only if the map
`x ↦ (z(x), w(x))` is injective outside a finite set (the singular points of the curve); this is the form used here. -/
def IsPrimitivePair (z w : M → References.RiemannSphere) : Prop :=
  ∃ S : Set M, S.Finite ∧ InjOn (fun x => (z x, w x)) Sᶜ

/-- **Proposition IV.11.7** (Ch. IV §11.7). If `M` is a compact Riemann surface and `z ∈ 𝒦(M) ∖ ℂ`, then there exists
`w ∈ 𝒦(M) ∖ ℂ` such that `z, w` form a primitive pair. -/
theorem prop4_11_7 [CompactSpace M] {z : M → References.RiemannSphere} (hz : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) z)
    (hz' : ¬ ∃ c, ∀ x, z x = c) :
    ∃ w : M → References.RiemannSphere, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) w ∧ (¬ ∃ c, ∀ x, w x = c) ∧
      IsPrimitivePair z w := by
  sorry

/-- **Corollary IV.11.8** (Ch. IV §11.8). If `M` is a compact Riemann surface and `z ∈ 𝒦(M) ∖ ℂ`, then there exists an
irreducible polynomial `P` in the two variables `z` and `w` such that `M` is conformally equivalent to the analytic
configuration corresponding to `P`, with `z` being the `proj` function.
Modelling (Forster's language, `Forster1981.IsAlgebraicFunctionOf`, Theorem 8.9): there are a monic irreducible polynomial
`P` over the field `𝓜(ℂ̂)` of degree `deg z` and `w ∈ 𝓜(M)` with `(M, z, w)` the algebraic function defined by `P`; by
`Forster1981.thm8_9_b` this algebraic function is unique up to isomorphism, so `M` is the Riemann surface of `P`. -/
theorem cor4_11_8 [CompactSpace M] {z : M → References.RiemannSphere} (hz : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) z)
    (hz' : ¬ ∃ c, ∀ x, z x = c) :
    ∃ (P : Polynomial (Forster1981.meroFun References.RiemannSphere))
      (hπ : Tendsto z (Filter.codiscrete M) (Filter.codiscrete References.RiemannSphere))
      (w : Forster1981.meroFun M), P.Monic ∧ Irreducible P ∧ Forster1981.IsAlgebraicFunctionOf P z hπ w := by
  sorry

/-- **Proposition IV.11.9** (Ch. IV §11.9). Let `M` be a compact Riemann surface and `z, w` a primitive pair. Assume
`n = deg z`, `m = deg w`. Let `P` be an irreducible polynomial satisfied by the pair `z, w`. Then `n = deg_w P` and
`m = deg_z P`. -/
theorem prop4_11_9 [CompactSpace M] {z w : M → References.RiemannSphere} {n m : ℕ}
    (hz : Forster1981.IsHolomorphicCovering z n) (hw : Forster1981.IsHolomorphicCovering w m)
    (hp : IsPrimitivePair z w) {P : MvPolynomial (Fin 2) ℂ} (hirr : Irreducible P) (hP : IsAlgebraicRelation P z w) :
    MvPolynomial.degreeOf 1 P = n ∧ MvPolynomial.degreeOf 0 P = m := by
  sorry

/-- **Proposition IV.11.10** (Ch. IV §11.10). Let `M` be a compact Riemann surface and `z, w` a primitive pair. Assume
`deg z = n`. Let `f ∈ 𝒦(M)`. Then there exist rational functions `a_j`, `j = 0, …, n − 1`, such that
`f = Σ_{j=0}^{n-1} a_j(z) w^j`.
Modelling: the identity holds at all points where `z`, `w`, `f` are finite and the rational functions are defined (all but
finitely many points; the identity of meromorphic functions then holds everywhere by continuity). -/
theorem prop4_11_10 [CompactSpace M] {z w f : M → References.RiemannSphere} {n : ℕ}
    (hz : Forster1981.IsHolomorphicCovering z n) (hp : IsPrimitivePair z w) (hw : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) w)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hf' : ¬ ∀ x, f x = References.RiemannSphere.infty) :
    ∃ a : Fin n → RatFunc ℂ, ∃ S : Set M, S.Finite ∧ ∀ x ∉ S,
      z x ≠ References.RiemannSphere.infty → w x ≠ References.RiemannSphere.infty →
      f x ≠ References.RiemannSphere.infty →
      finVal (f x) = ∑ j : Fin n, RatFunc.eval (RingHom.id ℂ) (finVal (z x)) (a j) * finVal (w x) ^ (j : ℕ) := by
  sorry

/-- **Discrete valuation of rank 1** (Ch. IV §11.12, Definition). Let `K` be a field. A *(discrete) valuation (of
rank 1)* `v` on `K` is a surjective homomorphism `v : K* → ℤ` such that `v(f + g) ≥ min {v(f), v(g)}`. Modelling: a Mathlib
`AddValuation K (WithTop ℤ)` (with `v(0) = +∞`, as in the Remark) which is surjective onto `ℤ`. -/
def IsDiscreteValuation1 {K : Type*} [Field K] (v : AddValuation K (WithTop ℤ)) : Prop :=
  ∀ n : ℤ, ∃ f : K, f ≠ 0 ∧ v f = (n : WithTop ℤ)

end FarkasKra1992
