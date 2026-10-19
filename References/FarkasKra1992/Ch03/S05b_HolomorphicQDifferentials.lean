import References.FarkasKra1992.Ch03.S05_ApplicationsOfRiemannRoch
import References.FarkasKra1992.Ch02.S05_MeromorphicFunctionsAndDifferentials
import References.FarkasKra1992.Ch05.S02_RepresentationsOnDifferentials

/-!
# Farkas–Kra, Chapter III §5 (continued): holomorphic `q`-differentials and `q`-Weierstrass points

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. III §5.1, §5.2, §5.9, §5.10 (`full.md` FK1:3596–3660,
3955–4002).

Sibling of `Ch03/S05_ApplicationsOfRiemannRoch` (which holds the gap theorems and the classical `q = 1` Weierstrass points).
A *holomorphic `q`-differential* is a family of coefficients `c x` in the preferred charts with the transformation law of
`LiZhongQC.IsDiffFamily q 0` that is holomorphic on every chart target (`IsHolQDiff`, `Ch02/S05`); the space `ℋ^q(M)` is
`holQDiffSpan M q` and `dimHolQ M q` its dimension (both defined in `Ch02/S05`, next to the meromorphic `q`-differentials
`IsMeroQDiff` and their order `ordQDiff`). The weight `qWeight q P` of `P` with respect to `ℋ^q(M)` is the weight `τ(P)` of Ch. III §5.8
(`weightWRT`) of the space of coefficient functions in the preferred chart at `P`, taken at the point `chartAt ℂ P P`;
`P` is a *`q`-Weierstrass point* iff this weight is positive. For `q = 1` it is the weight of `Forster1981.weierstrassWeight`
(Proposition III.5.9 of `Ch03/S05`). The canonical divisor of a non-zero abelian differential is `Forster1981.IsDivisorOfForm`;
`q • K` is the additive form of `Z^q`.

* Definition (holomorphic `q`-differentials `ℋ^q(M)`, III.5.1) — exists: `FarkasKra1992.IsHolQDiff`, `FarkasKra1992.holQDiffSpan`, `FarkasKra1992.dimHolQ`
* Paragraph III.5.1 ((5.1.5) `L(Z^{-q}) ≅ ℋ^q(M)`) — `para3_5_1_b`
* Proposition III.5.2 (dimension table of `ℋ^q(M)`) — `prop3_5_2`
* Definition (`q`-Weierstrass point, III.5.9) — exists: `FarkasKra1992.IsQWeierstrass`
* Definition (weight of a point with respect to the holomorphic q-differentials, III.5.9) — `qWeight`
* Proposition III.5.9 (general `q`) — `isQWeierstrass_iff_weight_pos`, `prop3_5_9`
* Proposition III.5.10 (general `q`: `Σ τ(P) = (g - 1) d (2q - 1 + d)`) — `prop3_5_10`
* Corollary to Proposition III.5.10 (`q`-Weierstrass points exist for every `q ≥ 1`) — `cor3_5_10`
-/

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

namespace FarkasKra1992

open Forster1981 (H0 modOD divDeg)

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **Paragraph III.5.1, (5.1.5)** (Ch. III §5.1). Let `ω ≠ 0` be an abelian differential on `M` with divisor `K = (ω)`. Then
`ω^q` induces an isomorphism `L(Z^{-q}) ≅ ℋ^q(M)` (`q ∈ ℤ`): a function `f` with `(f) ≥ -qK` goes to the holomorphic
`q`-differential `f ω^q`. In the sheaf model `L(Z^{-q}) = H⁰(M, 𝒪_{qK})`. -/
theorem para3_5_1_b (q : ℤ) {K : Function.locallyFinsupp M ℤ} {w : Forster1981.Form1 M}
    (hK : Forster1981.IsDivisorOfForm w K) :
    Nonempty (holQDiffSpan M q ≃ₗ[ℂ] H0 (modOD M (q • K))) := by
  sorry

/-- **Proposition III.5.2** (Ch. III §5.2). Let `M` be a compact Riemann surface of genus `g`. Then
`dim ℋ^q(M) = 1 - 2q` for `g = 0`, `q ≤ 0`; `0` for `g = 0`, `q > 0`; `1` for `g = 1`; and for `g > 1`:
`0` for `q < 0`, `1` for `q = 0`, `g` for `q = 1`, `(2q - 1)(g - 1)` for `q > 1`. -/
theorem prop3_5_2 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (q : ℤ) :
    (g = 0 → q ≤ 0 → (dimHolQ M q : ℤ) = 1 - 2 * q) ∧ (g = 0 → 0 < q → dimHolQ M q = 0) ∧
      (g = 1 → dimHolQ M q = 1) ∧ (1 < g → q < 0 → dimHolQ M q = 0) ∧ (1 < g → q = 0 → dimHolQ M q = 1) ∧
      (1 < g → q = 1 → dimHolQ M q = g) ∧ (1 < g → 1 < q → (dimHolQ M q : ℤ) = (2 * q - 1) * ((g : ℤ) - 1)) := by
  sorry

/-- **The weight `τ(P)` of `P` with respect to `ℋ^q(M)`** (Ch. III §5.9): the weight `weightWRT` (Ch. III §5.8) at the point
`chartAt ℂ P P` of the space of coefficient functions in the preferred chart at `P` of the holomorphic `q`-differentials. -/
def qWeight (q : ℤ) (P : M) : ℕ :=
  weightWRT (Submodule.map (LinearMap.proj P : (M → ℂ → ℂ) →ₗ[ℂ] (ℂ → ℂ)) (holQDiffSpan M q)) (chartAt ℂ P P)

/-- **Definition of `q`-Weierstrass point** (Ch. III §5.9): `P` is a `q`-Weierstrass point iff its weight with respect to `ℋ^q(M)`
is positive. The notion is `FarkasKra1992.IsQWeierstrass` (`Ch05/S02`, defined through the orders at `P`); this identifies it with
the weight `qWeight` (`q ∈ ℕ`). -/
theorem isQWeierstrass_iff_weight_pos [CompactSpace M] (q : ℕ) (P : M) : IsQWeierstrass M q P ↔ 0 < qWeight (q : ℤ) P := by
  sorry

/-- **Proposition III.5.9** (Ch. III §5.9, general `q`). Let `M` be a compact surface of genus `g ≥ 2`, `q ≥ 1`,
`d = dim ℋ^q(M)`. Then `P` is a `q`-Weierstrass point if and only if there is a holomorphic `q`-differential, not zero, with a
zero of order `≥ d` at `P`. (For `q = 1` this is `prop3_5_9_one`.) -/
theorem prop3_5_9 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (h2 : 2 ≤ g) {q : ℕ} (hq : 1 ≤ q) (P : M) :
    IsQWeierstrass M q P ↔
      ∃ c, IsHolQDiff (q : ℤ) c ∧ ordQDiff c P ≠ ⊤ ∧ ((dimHolQ M (q : ℤ) : ℤ) : WithTop ℤ) ≤ ordQDiff c P := by
  sorry

/-- **Proposition III.5.10** (Ch. III §5.10, general `q`). Let `M` be a compact surface of genus `g ≥ 2`, `q ≥ 1`,
`d = dim ℋ^q(M)`. Then there are finitely many `q`-Weierstrass points and `Σ_P τ(P) = (g - 1) d (2q - 1 + d)`. For `q = 1`
this is `Forster1981.thm18_8`. -/
theorem prop3_5_10 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (h2 : 2 ≤ g) {q : ℕ} (hq : 1 ≤ q) :
    (Function.support (qWeight (M := M) (q : ℤ))).Finite ∧
      ((∑ᶠ P : M, qWeight (q : ℤ) P : ℕ) : ℤ) =
        ((g : ℤ) - 1) * dimHolQ M (q : ℤ) * (2 * (q : ℤ) - 1 + dimHolQ M (q : ℤ)) := by
  sorry

/-- **Corollary to Proposition III.5.10** (Ch. III §5.10). If `g ≥ 2` and `q ≥ 1`, there exist `q`-Weierstrass points on `M`. -/
theorem cor3_5_10 [CompactSpace M] {g : ℕ} (hg : LiZhongQC.HasGenus M g) (h2 : 2 ≤ g) {q : ℕ} (hq : 1 ≤ q) :
    ∃ P : M, IsQWeierstrass M q P := by
  sorry

end FarkasKra1992
