import References.Hubbard2006.Ch03.S03_HyperbolicMetric
import References.Lehto1987.Ch05.S06_TeichmullerSpaceOfATorus

/-!
# Hubbard 2006, Chapter 3 §3.2: The classification of annuli

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 2031–2197.

**Conventions.** An *annulus* is a Riemann surface with fundamental group `ℤ` (`IsAnnulusRS`). The round annulus `A_M =
{1 < |z| < e^{2πM}}` (`References.roundAnnulus`) and the modulus `M` (`References.HasModulus A M`, `A ≅ A_M`, a
predicate, not a function) are the shared notions of `Common/HyperbolicSurface.lean`. `ℂ ∖ {0}` and `𝔻* = ℂ`-disc minus
the origin are `LiZhongQC.puncturedPlaneOpens` and `Hubbard2006.punctDiscOpens` (defined in `S03`, imported here).
Annuli of infinite modulus are the cases `ℂ ∖ {0}` and `𝔻*`; they have no number `M`. The torus `T = ℂ/(2πiℤ + ωℤ)` of
Thm 3.2.8 is `Lehto1987.IsTorusCovering pr L` for the lattice `L = 2πiℤ + ωℤ`, and "an annulus in the homology class of
`pγ₁ + qγ₂`" is modelled by: a generator of the fundamental group of the annulus lifts, through `pr`, to a path of `ℂ`
whose displacement is `±(2πi p + ω q)` (`IsAnnulusInClass`). The modulus of a quadrilateral (Exercise 3.2.10) and
Exercises 3.2.11–3.2.12 are not items.

* Proposition 3.2.1 (classification of annuli: `ℂ∖{0}`, `A_M` for exactly one `M`, or `𝔻*`; exactly one case) —
  `prop3_2_1`
* Definition (annulus; an annulus in the homology class of a vector, Thm 3.2.8) — `IsAnnulusRS`, `IsAnnulusInClass`
* Remark 3.2.2 (doubly / singly infinite annulus) — omitted: terminology
* Exercises 3.2.3, 3.2.4, 3.2.5, 3.2.10, 3.2.11, 3.2.12 — omitted: exercises
* Theorem 3.2.6 (a) (subadditivity of moduli of annuli) — `thm3_2_6_a`
* Theorem 3.2.6 (b) (the equality case, and annuli of infinite modulus) — deferred: needs the straight subcylinders of
  the cylinder model (Exercise 3.2.5), not an item
* Theorem 3.2.7 (Koebe's one-quarter theorem) — `thm3_2_7`
* Theorem 3.2.8 (moduli of annuli on a torus) — `thm3_2_8`
* Definition 3.2.9 (quadrilateral in a Riemann surface) — `IsQuadrilateral`
-/

open Set Metric
open scoped Manifold ContDiff Topology Real
open LiZhongQC References

namespace Hubbard2006

/-- **Annulus** (Prop. 3.2.1): a Riemann surface whose fundamental group is infinite cyclic. -/
def IsAnnulusRS (A : Type*) [TopologicalSpace A] : Prop :=
  ∃ x : A, Nonempty (FundamentalGroup A x ≃* Multiplicative ℤ)

/-- **Quadrilateral in a Riemann surface** (Def. 3.2.9, H1:2161): `Q ⊆ X` is homeomorphic to a closed disc (by `φ`), and
`I₁, I₂ ⊆ Q` are disjoint, non-empty, connected, closed subsets of the boundary `∂Q = φ⁻¹(S¹)` that are not single
points. Modelling: the boundary of the disc `Q` is the preimage of the unit circle under the homeomorphism (independent
of it by invariance of domain). -/
def IsQuadrilateral {X : Type*} [TopologicalSpace X] (Q I₁ I₂ : Set X) : Prop :=
  ∃ φ : Q ≃ₜ closedBall (0 : ℂ) 1,
    (∀ x : Q, (x : X) ∈ I₁ ∪ I₂ → ‖(φ x : ℂ)‖ = 1) ∧ I₁ ⊆ Q ∧ I₂ ⊆ Q ∧ Disjoint I₁ I₂ ∧
      I₁.Nonempty ∧ I₂.Nonempty ∧ IsConnected I₁ ∧ IsConnected I₂ ∧ IsClosed I₁ ∧ IsClosed I₂ ∧
      (∃ a ∈ I₁, ∃ b ∈ I₁, a ≠ b) ∧ ∃ a ∈ I₂, ∃ b ∈ I₂, a ≠ b

/-- **An annulus `A` in the homology class `v`** on the torus `T = ℂ/L` covered by `pr : ℂ → T` (Thm 3.2.8, "`A` in the
homology class of `pγ₁ + qγ₂`", `v = 2πi p + ω q`): a generator `σ` of `π₁(A, x)` lifts through `pr` to a path in `ℂ`
whose end point differs from its start point by `v` (or `−v`, the orientation of the generator being free). -/
def IsAnnulusInClass {T : Type*} [TopologicalSpace T] [ChartedSpace ℂ T] (pr : ℂ → T)
    (A : TopologicalSpace.Opens T) (v : ℂ) : Prop :=
  ∃ (x : A) (σ : Path x x),
    (∀ τ : FundamentalGroup A x, ∃ k : ℤ, τ = (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk σ)) ^ k) ∧
    ∃ c : C(unitInterval, ℂ), (∀ s, pr (c s) = ((σ s : A) : T)) ∧ (c 1 - c 0 = v ∨ c 1 - c 0 = -v)

variable {A : Type*} [TopologicalSpace A] [T2Space A] [ConnectedSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A]

/-- **Proposition 3.2.1** (classification of annuli, Ch. 3 §3.2, H1:2037). An annulus `A` is isomorphic to exactly one
of
(1) `ℂ ∖ {0}`; (2) `A_M = {1 < |z| < e^{2πM}}` for exactly one `M ∈ (0, ∞)` (the modulus `Mod A`); (3) `𝔻* ≅ A_∞ = {1 <
  |z|}`. "Exactly one" refers to both the three cases (pairwise non-isomorphic) and the number `M`. -/
theorem prop3_2_1 (hA : IsAnnulusRS A) :
    ((RSConformallyEquivalent A puncturedPlaneOpens ∧ ¬ (∃ M, HasModulus A M) ∧
        ¬ RSConformallyEquivalent A punctDiscOpens) ∨
      (¬ RSConformallyEquivalent A puncturedPlaneOpens ∧ (∃ M, HasModulus A M) ∧
        ¬ RSConformallyEquivalent A punctDiscOpens) ∨
      (¬ RSConformallyEquivalent A puncturedPlaneOpens ∧ ¬ (∃ M, HasModulus A M) ∧
        RSConformallyEquivalent A punctDiscOpens)) ∧
    ∀ M M' : ℝ, HasModulus A M → HasModulus A M' → M = M' := by
  sorry

/-- **Theorem 3.2.6 (a)** (subadditivity of moduli of annuli, Ch. 3 §3.2, H1:2091). Let `A` be an annulus of modulus `m`
and `(A_j)` a (finite or infinite, countable) family of disjoint open sub-annuli of finite moduli `m_j` such that the
inclusions `A_j ⊆ A` are homotopy equivalences. Then `∑ m_j ≤ m` (the series converges). -/
theorem thm3_2_6_a {ι : Type*} [Countable ι] {m : ℝ} (hm : HasModulus A m) (Aj : ι → TopologicalSpace.Opens A)
    (mj : ι → ℝ) (hmj : ∀ j, HasModulus (Aj j) (mj j))
    (hdisj : Pairwise (Function.onFun Disjoint fun j => (Aj j : Set A)))
    (hhe : ∀ j, ∃ e : ContinuousMap.HomotopyEquiv (Aj j) A, (e : Aj j → A) = Subtype.val) :
    Summable mj ∧ ∑' j, mj j ≤ m := by
  sorry

/-- **Theorem 3.2.7** (Koebe's one-quarter theorem, Ch. 3 §3.2, H1:2121). If `f : 𝔻 → ℂ` is injective and analytic with
`f(0) = 0` and `‖f′(0)‖ = 1`, then `f(𝔻)` contains the disc `D(0, 1/4)`. (Derivable from `Pommerenke1992.cor1_4` at `z =
0`: `¼ (1 − ‖z‖²) ‖f′(z)‖ ≤ dist(f z, ∂f(𝔻))`, the frontier of an open set being disjoint from it; stated here as a new
item in Hubbard's form.) -/
theorem thm3_2_7 (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (ball 0 1)) (hinj : InjOn f (ball 0 1)) (h0 : f 0 = 0)
    (h1 : ‖deriv f 0‖ = 1) : ball (0 : ℂ) (1 / 4) ⊆ f '' ball 0 1 := by
  sorry

/-- **Theorem 3.2.8** (moduli of annuli on a torus, Ch. 3 §3.2, H1:2147). Let `ω ∈ ℂ` with `Re ω > 0` and `T = ℂ/(2πiℤ +
ωℤ)` (`pr : ℂ → T` a torus covering with lattice `L = {2πi a + ω b}`). Let `(A_j)` be a (finite or infinite) family of
disjoint annuli in `T` of finite moduli `m_j`, all in the homology class of `pγ₁ + qγ₂` with `p, q` coprime integers.
Then `∑ m_j ≤ 2π Re ω / ‖2πi p + ω q‖²`. Modelling: finite moduli only (the infinite-modulus cases are the deferred ones
of Thm 3.2.6); the homology class is `IsAnnulusInClass`. -/
theorem thm3_2_8 {T : Type*} [TopologicalSpace T] [ChartedSpace ℂ T] {om : ℂ} (hom : 0 < om.re) (pr : ℂ → T)
    (hπ : Lehto1987.IsTorusCovering pr {z | ∃ a b : ℤ, z = 2 * π * Complex.I * a + om * b}) {p q : ℤ}
    (hpq : IsCoprime p q) {ι : Type*} [Countable ι] (Aj : ι → TopologicalSpace.Opens T) (mj : ι → ℝ)
    (hmj : ∀ j, HasModulus (Aj j) (mj j)) (hdisj : Pairwise (Function.onFun Disjoint fun j => (Aj j : Set T)))
    (hcl : ∀ j, IsAnnulusInClass pr (Aj j) (2 * π * Complex.I * p + om * q)) :
    Summable mj ∧ ∑' j, mj j ≤ 2 * π * om.re / ‖2 * π * Complex.I * p + om * q‖ ^ 2 := by
  sorry

end Hubbard2006
