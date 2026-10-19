import References.Forster1981.Ch01.S08_AlgebraicFunctions
import References.Forster1981.Ch02.S16_TheRiemannRochTheorem

/-!
# Farkas–Kra, Chapter IV §11 (continued): valuations of the function field and morphisms of compact surfaces

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. IV §11.14–11.17 (`full.md` FK2:2995–3200).

Sibling of `Ch04/S11_AlgebraicFunctionFields` (which holds IV.11.6–11.13). The field `𝒦(M)` of meromorphic functions of a
compact surface `M` is `Forster1981.meroFun M` (a `ℂ`-subalgebra of the germs along the codiscrete filter; that it is a field
is `Forster1981.rem1_16_b`, with no `Field` instance), so a valuation is an `AddValuation` of this ring into `ℤ ∪ {∞}`
that is finite on non-zero elements and takes every value of `ℤ` (FK IV.11.12: surjective onto `ℤ`). Orders and values of a
germ are read on a representative: `ordGerm x f = ord_x` and `evalGerm f x ∈ ℂ̂` is the value (`∞` at a pole). A `ℂ`-algebra
homomorphism `F : 𝒦(N) → 𝒦(M)` has the dual `F^* : M → N` characterized by `(F f)(x) = f(F^* x)` (`IsDualMap`).

* Lemma IV.11.14 (separation of `n + 1` points) — `lemma4_11_14`
* Theorem IV.11.15 (valuations of `𝒦(M)` are the orders `ord_x`) — `ordGerm`, `thm4_11_15`
* Theorem IV.11.16 (`ℂ`-algebra homomorphisms are induced by holomorphic maps) — `evalGerm`, `IsDualMap`, `thm4_11_16`
* Corollary IV.11.17 (a) (`id^* = id`) — `cor4_11_17_a`
* Corollary IV.11.17 (b) (`(F₂ F₁)^* = F₁^* F₂^*`) — `cor4_11_17_b`
* Corollary IV.11.17 (c) (an isomorphism induces a homeomorphism) — `cor4_11_17_c`
* Remark after Corollary IV.11.17 (open surfaces) — omitted: remark without a labelled claim
-/

open scoped Manifold ContDiff Topology References
open Set Filter

noncomputable section

namespace FarkasKra1992

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
variable {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N]

/-- **Lemma IV.11.14** (Ch. IV §11.14). Let `P_0, …, P_n` be `n + 1` distinct points on a compact Riemann surface `M`. Then
there exists `f ∈ 𝒦(M)` which separates these points (`f(P_j) ≠ f(P_k)`, `j ≠ k`) with `(df)(P_j) ≠ 0, ∞`: `f` is finite at each
`P_j` and `f - f(P_j)` has a simple zero at `P_j`. The value `f(P_j)` is the limit `limUnder (𝓝[≠] (P j)) f` (the value of the
function `f` at a removable point is not looked at).
[CORRECTION, FK-fix2] Separation is stated on these limits; the earlier form "`f y ≠ f (P k)` near `P j`" followed from the
simple-zero clause and did not separate (AUDIT5_FK F5). -/
theorem lemma4_11_14 [CompactSpace M] {n : ℕ} (P : Fin (n + 1) → M) (hP : Function.Injective P) :
    ∃ f : M → ℂ, LiZhongQC.IsMeromorphicRS f ∧ (∀ j, 0 ≤ LiZhongQC.ordRS f (P j)) ∧
      (∀ j k, j ≠ k → limUnder (𝓝[≠] (P j)) f ≠ limUnder (𝓝[≠] (P k)) f) ∧
      ∀ j, LiZhongQC.ordRS (fun y => f y - limUnder (𝓝[≠] (P j)) f) (P j) = (1 : ℤ) := by
  sorry

/-- **The order `ord_x f` of a meromorphic germ** `f ∈ 𝒦(M)` at `x` (`⊤` for `f = 0`), read on a representative function. -/
def ordGerm (x : M) (f : ↥(Forster1981.meroFun M)) : WithTop ℤ := LiZhongQC.ordRS f.2.choose x

/-- **The value `f(x) ∈ ℂ̂`** of a meromorphic germ at `x`: the limit of a representative at `x` if `f` has no pole at `x`, and
`∞` at a pole. (For the zero germ: `0`.) -/
def evalGerm (f : ↥(Forster1981.meroFun M)) (x : M) : References.RiemannSphere :=
  if 0 ≤ ordGerm x f then ((limUnder (𝓝[≠] x) f.2.choose : ℂ) : References.RiemannSphere) else References.RiemannSphere.infty

/-- **Theorem IV.11.15** (Ch. IV §11.15). Let `M` be a compact Riemann surface. Then `v` is a (discrete, rank 1) valuation on
`𝒦(M)` if and only if there exists a unique `x ∈ M` with `v(f) = ord_x f` for all `f ∈ 𝒦(M)`. (A valuation is an
`AddValuation` of `𝒦(M)` into `ℤ ∪ {∞}` which is finite on non-zero elements and surjective onto `ℤ`.) -/
theorem thm4_11_15 [CompactSpace M] (v : AddValuation ↥(Forster1981.meroFun M) (WithTop ℤ)) :
    ((∀ f, f ≠ 0 → v f ≠ ⊤) ∧ (∀ n : ℤ, ∃ f, v f = (n : WithTop ℤ))) ↔ ∃! x : M, ∀ f, v f = ordGerm x f := by
  sorry

/-- **The dual map** (11.16.3): `F^* : M → N` is holomorphic and `(F f)(x) = f(F^* x)` in `ℂ̂` for all `f ∈ 𝒦(N)`, `x ∈ M`. -/
def IsDualMap (F : ↥(Forster1981.meroFun N) →ₐ[ℂ] ↥(Forster1981.meroFun M)) (Fs : M → N) : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Fs ∧ ∀ f x, evalGerm (F f) x = evalGerm f (Fs x)

/-- **Theorem IV.11.16** (Ch. IV §11.16). Let `M` and `N` be compact Riemann surfaces and `F : 𝒦(N) → 𝒦(M)` a `ℂ`-algebra
homomorphism. Then there exists a unique holomorphic map `F^* : M → N` with `(F f)(x) = f(F^*(x))` for all
`f ∈ 𝒦(N)`, `x ∈ M`. -/
theorem thm4_11_16 [CompactSpace M] [CompactSpace N] (F : ↥(Forster1981.meroFun N) →ₐ[ℂ] ↥(Forster1981.meroFun M)) :
    ∃! Fs : M → N, IsDualMap F Fs := by
  sorry

/-- **Corollary IV.11.17 (a)** (Ch. IV §11.17). If `F : 𝒦(M) → 𝒦(M)` is the identity, then `F^* : M → M` is the identity. -/
theorem cor4_11_17_a [CompactSpace M] {Fs : M → M} (h : IsDualMap (AlgHom.id ℂ ↥(Forster1981.meroFun M)) Fs) : Fs = id := by
  sorry

/-- **Corollary IV.11.17 (b)** (Ch. IV §11.17). For `ℂ`-algebra homomorphisms `𝒦(M₁) → 𝒦(M₂) → 𝒦(M₃)` of compact
surfaces, `(F₂ ∘ F₁)^* = F₁^* ∘ F₂^*`. -/
theorem cor4_11_17_b {M₁ M₂ M₃ : Type} [TopologicalSpace M₁] [T2Space M₁] [ConnectedSpace M₁] [ChartedSpace ℂ M₁]
    [IsManifold 𝓘(ℂ) ω M₁] [CompactSpace M₁] [TopologicalSpace M₂] [T2Space M₂] [ConnectedSpace M₂] [ChartedSpace ℂ M₂]
    [IsManifold 𝓘(ℂ) ω M₂] [CompactSpace M₂] [TopologicalSpace M₃] [T2Space M₃] [ConnectedSpace M₃] [ChartedSpace ℂ M₃]
    [IsManifold 𝓘(ℂ) ω M₃] [CompactSpace M₃] (F₁ : ↥(Forster1981.meroFun M₁) →ₐ[ℂ] ↥(Forster1981.meroFun M₂))
    (F₂ : ↥(Forster1981.meroFun M₂) →ₐ[ℂ] ↥(Forster1981.meroFun M₃)) {F₁s : M₂ → M₁} {F₂s : M₃ → M₂}
    (h₁ : IsDualMap F₁ F₁s) (h₂ : IsDualMap F₂ F₂s) : IsDualMap (F₂.comp F₁) (F₁s ∘ F₂s) := by
  sorry

/-- **Corollary IV.11.17 (c)** (Ch. IV §11.17). If `F : 𝒦(N) → 𝒦(M)` is an isomorphism (surjective), then `F^*` is a
homeomorphism (indeed conformal). -/
theorem cor4_11_17_c [CompactSpace M] [CompactSpace N] (F : ↥(Forster1981.meroFun N) ≃ₐ[ℂ] ↥(Forster1981.meroFun M))
    {Fs : M → N} (h : IsDualMap (F : ↥(Forster1981.meroFun N) →ₐ[ℂ] ↥(Forster1981.meroFun M)) Fs) :
    ∃ e : M ≃ₜ N, (e : M → N) = Fs ∧ LiZhongQC.IsBiholomorphic (e : M → N) := by
  sorry

end FarkasKra1992
