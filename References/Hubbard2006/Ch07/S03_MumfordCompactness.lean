import References.Common.HyperbolicSurface
import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller

/-!
# Hubbard 2006, Chapter 7 §7.3: The Mumford compactness theorem

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H2` lines 3849–3931.

**Conventions.** `Moduli(S)` is the set of Riemann surfaces homeomorphic to `S` (no marking), with the topology of the
quotient `T_S/MCG(S)` of the Teichmüller space by the modular group, which is the topology of the quotient Teichmüller
metric `d(X, Y) = inf ln K(f)` over quasiconformal maps `f : X → Y`. It is metrizable, so *compactness* is sequential
compactness, and `X_n → X` in `Moduli(S)` iff there are quasiconformal homeomorphisms `f_n : X_n → X` (no marking) with
`K(f_n) → 1` (`ModuliConverges`). `Moduli_c(S)` is the set of surfaces whose simple closed geodesics all have length
`≥ c` (`HasSystoleAtLeast`). For finite type the surfaces are `LiZhongQC.FiniteTypeRS g n 0` (cusps contribute no closed
geodesic).

**Normalization of lengths.** The hyperbolic metric is the Poincaré metric `|dz|/Im z` of curvature `−1`, the metric
of `LiZhongQC.poincareLengthLoop` and `LiZhongQC.freeHomotopyLength`. For `g ∈ SL(2, ℝ)` hyperbolic,
`LiZhongQC.translationLength g = 2 log λ` (`λ` the larger eigenvalue) is the distance `d(z, g z)` of a point of the axis
`axisH g`; so the simple closed geodesic `p '' axisH g` of `ℍ/Γ` (`g` primitive, which is forced by simplicity, see
`References.IsSimpleClosedGeodesicOf`) has length exactly `translationLength g`. The systole condition below is written
with this length.

**Near misses.** `ImayoshiTaniguchi1992.lemma6_31` is Mumford's compactness theorem in the form for a sequence in
`T(R_*)` and Teichmüller modular transformations (IT Ch. 6 §6.5), not for `Moduli_c(S)` with the convergence of
`ModuliConverges`.

* Definition (the length of every simple closed geodesic is `≥ c`) — `HasSystoleAtLeast`
* Definition (convergence in `Moduli(S)`) — `ModuliConverges`
* Theorem 7.3.1 (Mumford compactness theorem) — `thm7_3_1`
* Exercise 7.3.2 — omitted: exercise (its content is not cited)
* Remark after Theorem 7.3.1 (generality: complete manifolds modelled on `(H, G)`) — omitted: remark
* Theorem 7.3.3 (Mumford compactness for finite type) — `thm7_3_3`
* Exercise 7.3.4 — omitted: exercise (the proof of Theorem 7.3.3)
-/

open Filter Topology
open scoped ENNReal
open LiZhongQC References

namespace Hubbard2006

universe u

/-- **`X` has all its simple closed geodesics of length `≥ c`**: for some (equivalently, any) uniformization `(Γ, p)` of
`X` by a torsion-free Fuchsian group, every simple closed geodesic `p '' axisH g` (`g ∈ Γ` hyperbolic with
`IsSimpleClosedGeodesicOf Γ p (p '' axisH g)`) has `translationLength g ≥ c`, the length in the Poincaré metric
`|dz|/Im z` (see the module docstring). *Junk:* a surface without a uniformization (not hyperbolic) does not satisfy
the condition. It defines `Moduli_c(S)` (Ch. 7 §7.3). -/
def HasSystoleAtLeast (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] (c : ℝ) : Prop :=
  ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → X),
    IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p ∧
      ∀ g ∈ Γ, IsHyperbolic g → IsSimpleClosedGeodesicOf Γ p (p '' axisH g) → c ≤ translationLength g

/-- **Convergence in `Moduli(S)`**: the sequence `X_n` converges to `X` iff there are quasiconformal homeomorphisms
`f_n : X_n → X` (no marking) with maximal dilatation `K(f_n) → 1`, i.e. convergence for the quotient Teichmüller metric
(Def. 6.4.14). The surfaces are in a common universe. -/
def ModuliConverges (Xn : ℕ → Type u) [∀ n, TopologicalSpace (Xn n)] [∀ n, ChartedSpace ℂ (Xn n)] (X : Type u)
    [TopologicalSpace X] [ChartedSpace ℂ X] : Prop :=
  ∃ f : ∀ n, Xn n ≃ₜ X, (∀ n, IsQCRS (f n)) ∧ Tendsto (fun n => maxDilatationRS (f n)) atTop (𝓝 1)

/-- **Theorem 7.3.1** (Mumford compactness theorem, Ch. 7 §7.3, H2:3853). Let `g ≥ 2` and `c > 0`. The space
`Moduli_c(S)` of closed Riemann surfaces of genus `g` whose simple closed geodesics all have length `≥ c` is compact:
every sequence `(X_n)` of such surfaces has a subsequence converging in `Moduli` (`ModuliConverges`) to a closed Riemann
surface `X` of genus `g` that again has all its simple closed geodesics of length `≥ c`. -/
theorem thm7_3_1 {g : ℕ} (hg : 2 ≤ g) {c : ℝ} (hc : 0 < c) (Xn : ℕ → ClosedRS.{0})
    (hgen : ∀ n, HasGenus (Xn n).carrier g) (hsys : ∀ n, HasSystoleAtLeast (Xn n).carrier c) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (X : ClosedRS.{0}), HasGenus X.carrier g ∧ HasSystoleAtLeast X.carrier c ∧
      ModuliConverges (fun n => (Xn (φ n)).carrier) X.carrier := by
  sorry

/-- **Theorem 7.3.3** (Mumford compactness for finite type, Ch. 7 §7.3, H2:3928). Let `P` be `n ≥ 1` points of a closed
surface of genus `g` with `2g − 2 + n > 0` (so `S ∖ P` is hyperbolic of finite type `(g, n, 0)`). For every `c > 0` the
space `Moduli_c(S ∖ P)` is compact: every sequence of surfaces of type `(g, n, 0)` whose simple closed geodesics all
have length `≥ c` has a subsequence converging in `Moduli` to such a surface. -/
theorem thm7_3_3 {g n : ℕ} (hn : 1 ≤ n) (hgn : 0 < 2 * (g : ℤ) - 2 + n) {c : ℝ} (hc : 0 < c)
    (Xn : ℕ → FiniteTypeRS.{0} g n 0) (hsys : ∀ k, HasSystoleAtLeast (Xn k).carrier c) :
    ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (X : FiniteTypeRS.{0} g n 0), HasSystoleAtLeast X.carrier c ∧
      ModuliConverges (fun k => (Xn (φ k)).carrier) X.carrier := by
  sorry

end Hubbard2006
