import References.Nag1988.Ch02.S01_TeichmullerSpaceAndReducedSpace
import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity

/-!
# Nag, Chapter 2 §2.5: Fricke coordinates for Teichmüller spaces of finite type (§2.5.5–§2.5.7)

Source: S. Nag, *The Complex Analytic Theory of Teichmüller Spaces*, Wiley 1988, Ch. 2 §2.5.5–§2.5.7 (`full.md` N1:4089–4234,
folder `The Complex Analytic Theory … 10dae1e9`, cited `N1:<line>`). The closed case (§2.5.2–§2.5.4) is passed:
`LiZhongQC.frickeSpace`, `LiZhongQC.deformationImage_eq_frickeSpace` (the homeomorphism onto an open set; the real-analyticity
is not stated there).

**Model.** `Γ` is a torsion-free Fuchsian group in `SL(2, ℝ)` with `X = ℍ/Γ` of finite type `(g, n, m)` (`IsOfType3`; `m` ideal
boundary continua are the holes of `LiZhongQC.IsFiniteType`). A *Fricke system* `FrickeGenerators Γ g n m` is the presentation
of §2.5.5/§2.5.7: standard loops `A_i, B_i` (hyperbolic), `C_j` around the punctures (parabolic), `D_l` around the holes
(hyperbolic), the single relation (5.9)/(5.14), and the normalization: for `g > 0`, `B_g` has repelling fixed point `0` and
attracting fixed point `∞` and `A_g(1) = 1`; for `g = 0` (and `m = 0`), the parabolics `C_n, C_{n-1}, C_{n-2}` fix `0, 1, ∞`.
The Fricke coordinates of `[μ]` are read off the matrices `A'_i = E_μ(A_i)`, … (`IsDeformedBy`, automatically normalized
since `w^μ` fixes `0, 1, ∞`): the lift of a hyperbolic matrix is normalized by `a ≥ 0` (and `b > 0` if `a = 0`), of a parabolic one
by `a' + d' = 2`; the coordinates are `(a, b, c)` of the first `2g - 2` hyperbolic generators `A_1, B_1, …, A_{g-1}, B_{g-1}`,
`(a', c')` of the parabolic generators (the first `n - 3` of them when `g = 0`) and `(a'', b'', c'')` of the `D_l`; the space is
`FrickeSpace g n m` (a product of Euclidean spaces of dimension `6g - 6 + 2n + 3m`, resp. `2n - 6` for `g = 0`).
Real-analytic structure: `T(X)` carries no manifold instance (N-D1); the real analyticity of the inverse is read through the Bers
embedding (the value of the Bers function at each `z ∈ 𝕃` is a real analytic function on the Fricke image).

* Section 2.5.5 (Fricke coordinates on `T(X)` for `X` of finite conformal type `(g, n)`; the loops, the relation (5.9), the
  normalization, the tuples (5.10)–(5.11), N1:4089) — `FrickeGenerators`, `FrickeSpace`, `IsFrickeCoords`
* Theorem (section 2.5.5; `F : T(X) → ℝ^{6g-6+2n}` is a real analytic embedding onto an open domain; N1:4167) — `thm2_5_5`
* Example 2.5.6 (`T(0, 3)` is a point; N1:4195) — `ex2_5_6`
* Section 2.5.7 (Fricke coordinates on `T^#(X)`, `X` of finite topological type `(g, n, m)`, `m ≥ 1`; (5.13)–(5.16); N1:4213) —
  covered by `FrickeGenerators`, `FrickeSpace`, `IsFrickeCoords`
* Theorem (section 2.5.7; `F : T^#(X) → ℝ^{6g-6+2n+3m}` is a real analytic isomorphism onto an open domain; N1:4228) —
  `thm2_5_7` (for `g > 0`; the real-analytic structure of `T^#(X)` is not modelled, so only injectivity and the openness of the
  image are stated; the cases `g = 0`, `m ≥ 1` with the normalizations (5.15), (5.16) are an omitted part: they differ from
  the stated case only by the normalization of the generators)
* Section 2.5.8 (independence of the base point; the modular action on the Fricke image) — omitted: remark (5.17)–(5.18),
  no new statement beyond the allowable-bijection formalism

**Near misses.** `LiZhongQC.frickeCoordinates`, `ImayoshiTaniguchi1992.frickeCoordinatesIT` (closed surfaces only, `g ≥ 2`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate Manifold ContDiff MatrixGroups

noncomputable section

namespace Nag1988

open LiZhongQC (TeichGamma teichSetoidGamma fMuSym h36p_m IsFuchsian BeltramiGamma IsUniformization IsFiniteType
  IsHyperbolic IsParabolic bersMapGamma lowerHalf)

abbrev SL2R : Type := Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- `X = ℍ/Γ` is a Riemann surface of finite type `(g, n, m)`: `n` punctures and `m` holes (the ideal boundary continua of
a Fuchsian group of the second kind). -/
def IsOfType3 (Γ : Subgroup SL2R) (g n m : ℕ) : Prop :=
  ∃ (S : Type) (_ : TopologicalSpace S) (_ : ChartedSpace ℂ S) (p : UpperHalfPlane → S),
    IsUniformization Γ p ∧ IsFiniteType S g n m

/-- The Fricke space `ℝ^{N}` of §2.5.5/§2.5.7 as a product of Euclidean spaces: `(a, b, c)` for the first `2g - 2` hyperbolic
generators, `(a', c')` for the parabolic generators (the first `n - 3` when `g = 0`), `(a'', b'', c'')` for the `m` holes. -/
abbrev FrickeSpace (g n m : ℕ) : Type :=
  (Fin (2 * g - 2) → ℝ × ℝ × ℝ) × (Fin (if g = 0 then n - 3 else n) → ℝ × ℝ) × (Fin m → ℝ × ℝ × ℝ)

/-- **Fricke system** for the group of a surface of type `(g, n, m)` (§2.5.5, §2.5.7): generators `A_i, B_i, C_j, D_l` in `Γ`
generating `Γ`, with the single relation `∏ [A_i, B_i] · C_1 ⋯ C_n · D_1 ⋯ D_m = 1`, the `A_i, B_i, D_l` hyperbolic, the `C_j`
parabolic, and the normalization of §2.5.2/§2.5.5 (for `g > 0`: `B_g(z) = a²z` with `|a| > 1` and `A_g(1) = 1`; for `g = 0`:
`C_n`, `C_{n-1}`, `C_{n-2}` fix `0`, `1`, `∞`). -/
structure FrickeGenerators (Γ : Subgroup SL2R) (g n m : ℕ) where
  A : Fin g → SL2R
  B : Fin g → SL2R
  C : Fin n → SL2R
  D : Fin m → SL2R
  mem : (∀ i, A i ∈ Γ) ∧ (∀ i, B i ∈ Γ) ∧ (∀ j, C j ∈ Γ) ∧ ∀ l, D l ∈ Γ
  generate : Subgroup.closure (range A ∪ range B ∪ range C ∪ range D) = Γ
  relation : (List.ofFn fun i => A i * B i * (A i)⁻¹ * (B i)⁻¹).prod * (List.ofFn C).prod * (List.ofFn D).prod = 1
  hyp : (∀ i, IsHyperbolic (A i)) ∧ (∀ i, IsHyperbolic (B i)) ∧ ∀ l, IsHyperbolic (D l)
  par : ∀ j, IsParabolic (C j)
  norm_B : ∀ i : Fin g, i.val + 1 = g → B i 0 1 = 0 ∧ B i 1 0 = 0 ∧ 1 < |B i 0 0|
  norm_A : ∀ i : Fin g, i.val + 1 = g → A i 0 0 + A i 0 1 = A i 1 0 + A i 1 1
  norm_C : g = 0 → ∀ j : Fin n, (j.val + 1 = n → C j 0 1 = 0) ∧ (j.val + 2 = n → C j 0 0 + C j 0 1 = C j 1 0 + C j 1 1) ∧
    (j.val + 3 = n → C j 1 0 = 0)

/-- The lift `(a, b, c)` of a hyperbolic matrix with `a ≥ 0`, and `b > 0` if `a = 0` (§2.5.5). -/
def hypCoord (M : SL2R) : ℝ × ℝ × ℝ :=
  if 0 < M 0 0 ∨ (M 0 0 = 0 ∧ 0 < M 0 1) then (M 0 0, M 0 1, M 1 0) else (-M 0 0, -M 0 1, -M 1 0)

/-- The coordinates `(a', c')` of the lift of a parabolic matrix with `a' + d' = 2` (§2.5.5). -/
def parCoord (M : SL2R) : ℝ × ℝ :=
  if M 0 0 + M 1 1 = 2 then (M 0 0, M 1 0) else (-M 0 0, -M 1 0)

/-- The `k`-th hyperbolic generator in the order `A_1, B_1, A_2, B_2, …` (`1` outside the range). -/
def hypPick {g : ℕ} (A B : Fin g → SL2R) (k : ℕ) : SL2R :=
  if h : k / 2 < g then (if k % 2 = 0 then A ⟨k / 2, h⟩ else B ⟨k / 2, h⟩) else 1

/-- `c` are the **Fricke coordinates** of `μ` with respect to the system `G` (§2.5.5, §2.5.7): the coordinates of the matrices
`E_μ(A_i), E_μ(B_i), E_μ(C_j), E_μ(D_l)`. Normalization of the lifts: `A_i, B_i` as in the book (`hypCoord`: `a ≥ 0`, and `b > 0`
if `a = 0`), `C_j` with trace `2` (`parCoord`). For the hole generators `D_l` the book (N1:4220) takes the lift with positive trace
`a'' + d'' > 2`; here `hypCoord` (`a ≥ 0`) is used for them as well. This is another choice of sign of the lift, so the coordinates
differ from the book's by the sign of some triples only, and still determine `E_μ(D_l)` (`a'' ≠ 0`: `D_l(∞) = 0` would make
`D_l B_g D_l⁻¹` and `B_g` share exactly one fixed point, impossible in a discrete group). [AUDITR2_Nag R2N-5] -/
def IsFrickeCoords {Γ : Subgroup SL2R} {g n m : ℕ} (G : FrickeGenerators Γ g n m) (μ : BeltramiGamma Γ)
    (c : FrickeSpace g n m) : Prop :=
  ∃ (A' B' : Fin g → SL2R) (C' : Fin n → SL2R) (D' : Fin m → SL2R),
    (∀ i, IsDeformedBy μ (G.A i) (A' i) ∧ IsDeformedBy μ (G.B i) (B' i)) ∧ (∀ j, IsDeformedBy μ (G.C j) (C' j)) ∧
      (∀ l, IsDeformedBy μ (G.D l) (D' l)) ∧
      (∀ k : Fin (2 * g - 2), c.1 k = hypCoord (hypPick A' B' k)) ∧
      (∀ j : Fin (if g = 0 then n - 3 else n), c.2.1 j = parCoord (if h : j.val < n then C' ⟨j.val, h⟩ else 1)) ∧
      ∀ l, c.2.2 l = hypCoord (D' l)

/-- **Theorem** (§2.5.5; N1:4167). Let `X = ℍ/Γ` be of finite conformal type `(g, n)`, `2g - 2 + n > 0` and `n > 3` if `g = 0`, and
`G` a Fricke system. The Fricke coordinates define an injective function `F : T(X) → ℝ^{6g-6+2n}` (`[μ] = [ν]` iff the
coordinates agree); its image is an open domain, and the inverse is real analytic: for each `z` in the lower half-plane the
value at `z` of the Bers function of `F⁻¹(c)` is a real analytic function of `c` on the image. -/
theorem thm2_5_5 {Γ : Subgroup SL2R} {g n : ℕ} (hΓ : IsFuchsian Γ) (hT : IsOfType3 Γ g n 0) (hχ : 0 < 2 * (g : ℤ) - 2 + n)
    (h0 : g = 0 → 3 < n) (G : FrickeGenerators Γ g n 0) :
    (∀ μ : BeltramiGamma Γ, ∃ c, IsFrickeCoords G μ c) ∧
      (∀ (μ ν : BeltramiGamma Γ) (c c' : FrickeSpace g n 0), IsFrickeCoords G μ c → IsFrickeCoords G ν c' →
        ((teichSetoidGamma Γ).r μ ν ↔ c = c')) ∧
      IsOpen {c : FrickeSpace g n 0 | ∃ μ, IsFrickeCoords G μ c} ∧
      ∃ φ : FrickeSpace g n 0 → ℂ → ℂ, (∀ μ c, IsFrickeCoords G μ c → φ c = bersMapGamma Γ (Quotient.mk _ μ)) ∧
        ∀ z ∈ lowerHalf, AnalyticOnNhd ℝ (fun c => φ c z) {c : FrickeSpace g n 0 | ∃ μ, IsFrickeCoords G μ c} := by
  sorry

/-- **Example 2.5.6** (N1:4195). A Riemann surface of type `(0, 3)` has a trivial Teichmüller space: `T(0, 3)` is a single point. -/
theorem ex2_5_6 {Γ : Subgroup SL2R} (hΓ : IsFuchsian Γ) (hT : IsOfType3 Γ 0 3 0) : Subsingleton (TeichGamma Γ) := by
  sorry

/-- **Theorem** (§2.5.7; N1:4228). Let `X = ℍ/Γ` be of finite topological type `(g, n, m)`, `g > 0`, `m ≥ 1`, and `G` a Fricke
system. The Fricke coordinates define an injective function on the reduced Teichmüller space `T^#(X)` into `ℝ^{6g-6+2n+3m}`
(`[μ]_# = [ν]_#` iff the coordinates agree) whose image is an open domain. -/
theorem thm2_5_7 {Γ : Subgroup SL2R} {g n m : ℕ} (hΓ : IsFuchsian Γ) (hT : IsOfType3 Γ g n m) (hg : 0 < g) (hm : 1 ≤ m)
    (G : FrickeGenerators Γ g n m) :
    (∀ μ : BeltramiGamma Γ, ∃ c, IsFrickeCoords G μ c) ∧
      (∀ (μ ν : BeltramiGamma Γ) (c c' : FrickeSpace g n m), IsFrickeCoords G μ c → IsFrickeCoords G ν c' →
        ((reducedSetoidGamma Γ).r μ ν ↔ c = c')) ∧
      IsOpen {c : FrickeSpace g n m | ∃ μ, IsFrickeCoords G μ c} := by
  sorry

end Nag1988
