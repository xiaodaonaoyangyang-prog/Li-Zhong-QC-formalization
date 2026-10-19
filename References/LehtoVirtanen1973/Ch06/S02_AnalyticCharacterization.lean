import References.LehtoVirtanen1973.Ch06.S00_Introduction

/-!
# Lehto–Virtanen, Chapter VI §2: Analytic characterization of a quasiconformal function

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. VI §2
(pp. 246–248; `full.md` second part P2:1723–1771). Chapter VI, and the text of the book, end at P2:1771; the
bibliography follows (its heading was lost in the OCR).

Conventions. "Since the results of Chapter III which find application here were stated only for domains of the finite
plane and finite-valued functions, we shall restrict ourselves to this case. In particular, this means that analytic
functions will have no poles" (P2:1727). As in Ch. V §4–§7, a domain `G` of the finite plane is `toExt D` for
`D : Set ℂ` with `IsDomainExt (toExt D)`, and a finite function in it is `OnePoint.map f` for `f : ℂ → ℂ`. For these
the generalized `L^p`-solutions of IV.5.3 (`IsGeneralizedLpSolution`) are the book's finite notion: `f` has
`L^p`-derivatives in `D` (III.6.1) and the equation holds almost everywhere in `D`. The derivatives `f_z`,
`f_{\bar z}` are built from the partial derivatives (IV.5.3). A measurable function `κ` in `G` is
`AEStronglyMeasurable κ (volume.restrict D)`; the bound `|κ(z)| ≤ (K − 1)/(K + 1)` is required at every point of `D`,
as printed, and is multiplied by `K + 1`. The conclusion "`f` is a `K`-quasiconformal function in `G`" is the
Definition of the Introduction for `OnePoint.map f` in `toExt D`; it is equivalent to the book's finite reading (`φ`
without poles on a finite domain `w(G)`), since `φ = f ∘ w⁻¹` is finite, and `w` may be followed by a Möbius
transformation which moves `w(G) ≠ ℂ̄` into the finite plane. The exponent `p(K)` is the extremal exponent of V.5.4
(`limitExponent`), and `p(K)`, `q(K)` are `ℝ≥0∞`-valued (H6); the exponents of `L^p`-derivatives are real, `p ≥ 1`.

* Unlabelled (§2.1, P2:1725): a `1`-quasiconformal function is an analytic function — omitted: immediate from the
  Definition of the Introduction (a 1-quasiconformal mapping is conformal, Theorem I.5.1, so f = φ ∘ w is analytic;
  conversely a non-constant analytic f is f composed with the identity), and it only introduces Theorem 2.1
* Theorem 2.1 (§2.1) — `thm6_2_1`
* Unlabelled (§2.1, P2:1731, after Theorem 2.1) — omitted: a remark (Theorem 2.1 compared with the Uniqueness theorem:
  without injectivity the local integrability of the derivatives is needed)
* Definition (the exponent `q(K)`, `1 − 1/p(K) = 1/q(K)`, §2.2) — `conjLimitExponent`
* Unlabelled (§2.2, P2:1733; recalled at P2:1753, 1769): `q(K)` increases monotonically from `1` to `2` as `K`
  increases from `1` to `∞`, so that `q(K) < 2` — omitted: immediate from the definition of q(K) and the facts of V.5.4
  stated in Chapter V (p(1) is infinite, p(K) is non-increasing, p(K) exceeds 2 for K greater than 1 and tends to 2 as
  K tends to infinity)
* Theorem 2.2 (§2.2) — `thm6_2_2`
* Formula (2.1) (§2.2) — omitted: the Beltrami equation displayed in the hypothesis of Theorem 2.2 and formalized
  there; not a result
* Remark (§2.2, P2:1753) — omitted: a remark; its claim (Theorem 2.2 for generalized L²-solutions, with a proof that
  avoids V.5) is the case q = 2 of Theorem 2.2, since q(K) is less than 2
* Unlabelled (§2.3, P2:1755–1763): Theorem 2.2 in the dilatation form (`L^q`-derivatives for a `q > q(K)` and
  `max_α |∂_α f(z)|² ≤ K J(z)` almost everywhere) — omitted: presented as an immediate reformulation ("we see
  immediately", by the dilatation condition (1.6) of IV.1.3), not cited later
* Unnumbered theorem (§2.3, P2:1765–1767, "This theorem", derived from Theorem 2.2) — `thm6_2_2_cor`
* Closing comments (§2.3, P2:1769–1771) — omitted: remarks (the theorem gives more information as K tends to 1; the
  precise value of p(K) is unknown; the integrability needed in Theorems 2.1 and 2.2 is an open question)
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt)
open References (IsDomainExt finitePart)

/-! ## §2.1 `L¹`-solutions of the Cauchy–Riemann equation -/

/-- **Theorem 2.1** (Ch. VI §2.1; "a special case of Lemma III.7.1"). Let `f` be a generalized `L¹`-solution of the
Cauchy–Riemann equation in a domain `G`. Then `f` is analytic in `G`.
Modelling: finite regime (module docstring): `G = toExt D`, `f` finite; the Cauchy–Riemann equation is the Beltrami
equation `f_{\bar z} = 0` (`κ = 0`); "analytic" is holomorphy in `D` (no poles, P2:1727). -/
theorem thm6_2_1 {D : Set ℂ} (hD : IsDomainExt (toExt D)) {f : ℂ → ℂ}
    (hf : IsGeneralizedLpSolution (OnePoint.map f) (fun _ => 0) (toExt D) 1) : DifferentiableOn ℂ f D := by
  sorry

/-! ## §2.2 `L^p`-solutions of Beltrami equations -/

/-- **Definition** (the exponent `q(K)`, Ch. VI §2.2, P2:1733). With the extremal exponent `p(K)` of V.5.4
(`limitExponent`), `q(K)` is defined by `1 − 1/p(K) = 1/q(K)`.
Modelling: Mathlib's conjugate exponent in `[0, ∞]`, `ENNReal.conjExponent p = 1 + (p − 1)⁻¹`, which satisfies
`p⁻¹ + q⁻¹ = 1` for `p ≥ 1` and gives `q = 1` for `p = ∞` (the book's `q(1) = 1`, P2:1769). Its truncation junk
(`q = ∞` for `p < 1`; at `p = 1`, `q = ∞` is the genuine conjugate) is never seen: `p(1) = ∞` and `p(K) > 2` for
`K > 1` (V.5.4), and every statement assumes `K ≥ 1`. -/
def conjLimitExponent (K : ℝ) : ℝ≥0∞ :=
  ENNReal.conjExponent (limitExponent K)

/-- **Theorem 2.2** (Ch. VI §2.2). In a domain `G` let `f` be a non-constant generalized `L^q`-solution of a Beltrami
equation `f_{\bar z} = κ f_z` (2.1), where `κ` is a measurable function in `G` with `|κ(z)| ≤ (K − 1)/(K + 1)` and
`q > q(K)`. Then `f` is a `K`-quasiconformal function in `G`.
Modelling: finite regime and coefficient as in the module docstring; [OCR] (2.1) is OCR'd as `f_z = κ f_z` (the
print, checked on the page image, is `f_{\bar z} = κ f_z`), and `κ` also as `\kappa`. `q` is real, `q > q(K) ≥ 1`.
Non-constant: `f` takes two different values in `D`. `1 ≤ K` is the book's standing `K ≥ 1` (harmonization H8): for
`-1 ≤ K < 1` the multiplied-out bound holds at no point, but for `K < -1` it reads `|κ| ≥ (K − 1)/(K + 1) > 1`, and
the statement would be false (`f(z) = z + 2z̄`, `κ ≡ 2`, `K = -3`, `q(-3) = 1` by the junk value `p(K) = ∞` for
`K < 1`, while no `(-3)`-quasiconformal mapping exists). -/
theorem thm6_2_2 {D : Set ℂ} (hD : IsDomainExt (toExt D)) {K : ℝ} (hK : 1 ≤ K) {κ : ℂ → ℂ}
    (hκm : AEStronglyMeasurable κ (volume.restrict D)) (hκ : ∀ z ∈ D, (K + 1) * ‖κ z‖ ≤ K - 1) {q : ℝ}
    (hq : conjLimitExponent K < ENNReal.ofReal q) {f : ℂ → ℂ} (hnc : ∃ a ∈ D, ∃ b ∈ D, f a ≠ f b)
    (hf : IsGeneralizedLpSolution (OnePoint.map f) κ (toExt D) q) :
    IsKQuasiconformalFunction (OnePoint.map f) (toExt D) K := by
  sorry

/-! ## §2.3 Other forms of the analytic characterization -/

/-- **Unnumbered theorem** (Ch. VI §2.3, P2:1765–1767, "This theorem"; derived from Theorem 2.2). If the function `f`
is a generalized `L^p`-solution of the Beltrami equation `f_{\bar z} = κ f_z`, with `|κ(z)| ≤ (K − 1)/(K + 1)`, for
some `p > q(K)`, then `f` is a generalized `L^p`-solution for every `p < p(K)`.
Modelling: [OCR] the equation is OCR'd as `f_{\bar z} = x f_z`. The book writes `p` for both exponents; the given one
is `p₀ > q(K)` here. Finite regime and coefficient as in Theorem 2.2 (`κ` measurable, as the coefficient of a
Beltrami equation, IV.5.3); the same `κ` for every `p`; `p` is real with `1 ≤ p` (III.6.1). A constant `f` is
allowed. `1 ≤ K` as in Theorem 2.2: for `-1 ≤ K < 1` the bound holds at no point, and for `K < -1` it reads
`|κ| ≥ (K − 1)/(K + 1) > 1`, `p(K) = ∞` is a junk value, and the claim fails (for `0 < α < 1` the conjugate of the
radial stretching `z |z|^{α - 1}` solves such an equation with `K = -1/α` and `|κ| = (1 + α)/(1 − α)`, and it has
`L^{p₀}`- but not `L^p`-derivatives near `0` for `1 < p₀ < 2/(1 − α) ≤ p`). -/
theorem thm6_2_2_cor {D : Set ℂ} (hD : IsDomainExt (toExt D)) {K : ℝ} (hK : 1 ≤ K) {κ : ℂ → ℂ}
    (hκm : AEStronglyMeasurable κ (volume.restrict D)) (hκ : ∀ z ∈ D, (K + 1) * ‖κ z‖ ≤ K - 1) {f : ℂ → ℂ}
    {p₀ : ℝ} (hp₀ : conjLimitExponent K < ENNReal.ofReal p₀)
    (hf : IsGeneralizedLpSolution (OnePoint.map f) κ (toExt D) p₀) :
    ∀ p : ℝ, 1 ≤ p → ENNReal.ofReal p < limitExponent K →
      IsGeneralizedLpSolution (OnePoint.map f) κ (toExt D) p := by
  sorry

end LehtoVirtanen1973
