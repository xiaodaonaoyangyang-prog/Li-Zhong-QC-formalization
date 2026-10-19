import References.Lehto1987.Ch04.S05_CompactRiemannSurfaces

/-!
# Lehto, Chapter IV §6: Trajectories of quadratic differentials

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. IV §6 (`full.md`
P1:5608–5780).

Conventions (see §1, §5). `φ` is a holomorphic quadratic differential on a Riemann surface `S`, not identically zero:
`q : S → ℂ → ℂ` with `LiZhongQC.IsHolQuadDiff q` and `q ≠ 0`, where `q x` is its representation in the preferred
chart at `x`. Quantities like `φ(z(t)) z′(t)²` are computed in the preferred chart at the point `γ(t)` (they do not
depend on the chart). Paths are maps `γ : ℝ → S` on an open interval `I` (named `J` in the code, where `I` is the
imaginary unit). A trajectory parametrized by its natural
parameter (its `φ`-arc length, Lehto's `f` on `I = G ∩ ℝ` of §6.4) is a *natural parametrization*
(`IsNaturalParametrization`).

* Definition (regular and critical points, §6.1) — exists: `LiZhongQC.IsRegularPoint`, `LiZhongQC.IsZeroOfOrder`
  (critical points are the points which are not regular)
* Unlabelled (§6.1, P1:5612): critical points are discrete, finitely many on a compact surface — omitted: U−
* Definition (natural parameter at a regular point, §6.1) — exists: `LiZhongQC.IsNaturalParameterAt` (normalized to
  vanish at the point; Lehto's natural parameters are the ±w + c)
* Unlabelled (§6.1, P1:5622–5628): natural parameters exist, and `φ ≡ 1` in them — exists:
  `LiZhongQC.eq25_2_natural_parameter` (in a chart)
* Unlabelled (§6.1, P1:5630): every natural parameter is `±w + const` — exists:
  `LiZhongQC.eq25_3_natural_parameter_unique` (for the normalized ones: the sign)
* Definition (natural parameter at a critical point, §6.1) — exists: `LiZhongQC.IsNaturalParameterAtZero`
* Formula (6.1) (§6.1) — exists: `LiZhongQC.eq25_5_natural_parameter_zero` (in a chart, zeros of order n ≥ 1)
* Definition (regular path, §6.2) — `IsRegularPath`
* Formula (6.2) (§6.2) — `IsStraightLine` (the defining condition)
* Definition (straight line, horizontal and vertical, §6.2) — `IsStraightLine` (with `θ = 0`, `θ = π`)
* Definition (maximal straight line, horizontal and vertical trajectory, §6.2) — `IsMaximalStraightLine`,
  `IsHorizontalTrajectory`, `IsVerticalTrajectory`
* Unlabelled (§6.2, P1:5684–5689): trajectories in natural parameters; the `n + 2` horizontal rays at a zero of order
  `n` — omitted: U−, not cited
* Definition (critical trajectory, §6.2) — `IsCriticalTrajectory`
* Unlabelled (§6.2, P1:5691): critical trajectories are countable, finitely many on a compact surface — omitted: not
  cited
* Unlabelled (§6.2, P1:5693): exactly one horizontal trajectory passes through each regular point — `para4_6_2`
* Definition (orientable quadratic differential, §6.3) — `IsOrientableQD`
* Unlabelled (§6.3, P1:5703–5717): a non-orientable `φ` lifts to a two-sheeted covering surface, branched over its
  zeros of odd order, where it is the square of an Abelian differential — `para4_6_3`
* Definition (maximal disc and its radius, §6.4) — `maximalDiscRadius`
* Unlabelled (§6.4, P1:5721–5729): the maximal disc is unique, the radius is continuous, chains of discs and the
  horizontal trajectory through `p₀` — omitted: a construction, U−
* Unlabelled (§6.5, P1:5733–5743): periodic trajectories, the maximal annulus, the torus case — omitted: a construction
  (the maximal rectangle) not formalized; its cited consequence, the euclidean metric on a torus, is para4_7_1 of §7
* Definition (trajectory ray, §6.6) — `trajectoryRay`
* Definition (limit set of a ray, §6.6) — `rayLimitSet`
* Unlabelled (§6.6, P1:5751): the limit set does not depend on the initial point — omitted: U−
* Definition (boundary ray, cross-cut, §6.6) — `IsBoundaryRay`, `IsCrossCut`
* Definition (critical ray, divergent ray, §6.6) — `IsCriticalRay`, `IsDivergentRay`
* Definition (recurrent ray, spiral, §6.6) — `IsRecurrentRay`, `IsSpiralTrajectory`
* Unlabelled (§6.6, P1:5751–5765): no boundary rays on a compact surface; a one-point limit set is a zero; a limit
  set with more than one point forces infinite length; a recurrent ray has `L = cl α` — `para4_6_6`
* Unlabelled (§6.6, P1:5773): divergent rays are recurrent on compact surfaces, with finitely many exceptions —
  omitted: quoted (Strebel)

Helper (not a book notion): `IsNaturalParametrization` (a path parametrized by a natural parameter, `φ(z) z′² = 1`).
-/

open Complex Set Filter Topology
open scoped ContDiff Manifold

noncomputable section

namespace Lehto1987

universe u

open LiZhongQC (IsHolQuadDiff IsRegularPoint IsZeroOfOrder IsDiffFamily)

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-! ## §6.2 Straight lines and trajectories -/

/-- **Definition** (regular path, Ch. IV §6.2): a continuously differentiable map `γ` of an open interval `I` into `S`
with non-zero derivative on `I`.
Modelling: in the preferred chart at `γ(t)`. -/
def IsRegularPath (γ : ℝ → S) (J : Set ℝ) : Prop :=
  IsOpen J ∧ J.OrdConnected ∧ J.Nonempty ∧ ContinuousOn γ J ∧
    ∀ t ∈ J, ContDiffAt ℝ 1 (fun s => chartAt ℂ (γ t) (γ s)) t ∧ deriv (fun s => chartAt ℂ (γ t) (γ s)) t ≠ 0

/-- **Definition** (straight line, (6.2), Ch. IV §6.2): a regular path along which `arg(φ(z(t)) z′(t)²) = θ` is
constant (it avoids the zeros of `φ`). Horizontal: `θ = 0`; vertical: `θ = π`. (Not `Pommerenke1992.IsStraightLine`,
a euclidean line.) -/
def IsStraightLine (q : S → ℂ → ℂ) (γ : ℝ → S) (J : Set ℝ) (θ : ℝ) : Prop :=
  IsRegularPath γ J ∧ ∀ t ∈ J, ∃ r : ℝ, 0 < r ∧
    q (γ t) (chartAt ℂ (γ t) (γ t)) * deriv (fun s => chartAt ℂ (γ t) (γ s)) t ^ 2 = r * exp (θ * I)

/-- **Definition** (maximal straight line, Ch. IV §6.2): a straight line which is not properly contained in any
regular curve on which (6.2) holds.
Modelling: containment of the images. -/
def IsMaximalStraightLine (q : S → ℂ → ℂ) (γ : ℝ → S) (J : Set ℝ) (θ : ℝ) : Prop :=
  IsStraightLine q γ J θ ∧ ∀ (γ' : ℝ → S) (J' : Set ℝ), IsStraightLine q γ' J' θ → γ '' J ⊆ γ' '' J' →
    γ' '' J' = γ '' J

/-- **Definition** (horizontal trajectory, Ch. IV §6.2): a maximal horizontal straight line (near miss:
`LiZhongQC.IsHorizontalArcRS`, arcs). -/
def IsHorizontalTrajectory (q : S → ℂ → ℂ) (γ : ℝ → S) (J : Set ℝ) : Prop := IsMaximalStraightLine q γ J 0

/-- **Definition** (vertical trajectory, Ch. IV §6.2): a maximal vertical straight line. -/
def IsVerticalTrajectory (q : S → ℂ → ℂ) (γ : ℝ → S) (J : Set ℝ) : Prop := IsMaximalStraightLine q γ J Real.pi

/-- **Definition** (critical trajectory, Ch. IV §6.2): a horizontal trajectory with an endpoint which is a zero of
`φ`. -/
def IsCriticalTrajectory (q : S → ℂ → ℂ) (γ : ℝ → S) (J : Set ℝ) : Prop :=
  IsHorizontalTrajectory q γ J ∧ ∃ p : S, ¬ IsRegularPoint q p ∧
    ((∃ a : ℝ, IsGLB J a ∧ Tendsto γ (𝓝[>] a) (𝓝 p)) ∨ (∃ b : ℝ, IsLUB J b ∧ Tendsto γ (𝓝[<] b) (𝓝 p)))

/-- **Unlabelled** (Ch. IV §6.2, P1:5693). Through every regular point of `S` passes exactly one horizontal
trajectory.
Modelling: existence, and uniqueness of the image. -/
theorem para4_6_2 [T2Space S] [SecondCountableTopology S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {p : S} (hp : IsRegularPoint q p) :
    (∃ (γ : ℝ → S) (J : Set ℝ), IsHorizontalTrajectory q γ J ∧ p ∈ γ '' J) ∧
      ∀ (γ γ' : ℝ → S) (J J' : Set ℝ), IsHorizontalTrajectory q γ J → IsHorizontalTrajectory q γ' J' →
        p ∈ γ '' J → p ∈ γ' '' J' → γ '' J = γ' '' J' := by
  sorry

/-! ## §6.3 Orientation of trajectories -/

/-- **Definition** (orientable quadratic differential, Ch. IV §6.3): the punctured surface
`S₀ = S ∖ {zeros of φ}` has an atlas of natural parameters `wᵢ` whose changes of variables are all of the form
`z + constant`.
Modelling: local parameters `w` on `S₀` in which `φ` is represented by `1`; the changes of variables have derivative
`1`. -/
def IsOrientableQD (q : S → ℂ → ℂ) : Prop :=
  ∃ A : Set (OpenPartialHomeomorph S ℂ), (∀ p : S, IsRegularPoint q p → ∃ w ∈ A, p ∈ w.source) ∧
    (∀ w ∈ A, ∀ x ∈ w.source, IsRegularPoint q x ∧
      q x (chartAt ℂ x x) = deriv (fun z => w ((chartAt ℂ x).symm z)) (chartAt ℂ x x) ^ 2) ∧
    ∀ w ∈ A, ∀ w' ∈ A, ∀ z ∈ (w.symm.trans w').source, deriv (fun y => w' (w.symm y)) z = 1

/-- **Unlabelled** (Ch. IV §6.3, P1:5703–5717). If `φ` is not orientable, `S` has a two-sheeted covering surface `S̃`,
branched over the zeros of `φ` of odd order, such that the lift of `φ` to `S̃` is the square of a holomorphic Abelian
differential (and hence orientable).
Modelling: `S̃` is a Riemann surface in the universe of `S` with an analytic projection `π`; `π` has one preimage over
the zeros of odd order and two elsewhere; the lift is in the sense of (3.4) (`IsDiffLift`). -/
theorem para4_6_3 [T2Space S] [SecondCountableTopology S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (hno : ¬ IsOrientableQD q) :
    ∃ (T : Type u) (_ : TopologicalSpace T) (_ : ChartedSpace ℂ T), References.IsRiemannSurface T ∧
      SecondCountableTopology T ∧ ∃ π : T → S, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π ∧ IsCoveringSurface π ∧
        (∀ x : S, ((∃ m : ℕ, Odd m ∧ IsZeroOfOrder q x m) → (π ⁻¹' {x}).ncard = 1) ∧
          (¬ (∃ m : ℕ, Odd m ∧ IsZeroOfOrder q x m) → (π ⁻¹' {x}).ncard = 2)) ∧
        ∃ α : T → ℂ → ℂ, IsDiffFamily 1 0 α ∧ (∀ y : T, DifferentiableOn ℂ (α y) (chartAt ℂ y).target) ∧
          IsDiffLift 2 0 π q (fun y z => α y z ^ 2) := by
  sorry

/-! ## §6.4 Trajectories in the large -/

/-- **Definition** (radius of the maximal disc, Ch. IV §6.4): the largest `r ≤ ∞` such that the analytic
continuation `f₀` of the local inverse of a natural parameter `Φ₀` at `p` (`Φ₀(p) = 0`) maps `D(0, r)` injectively
into `S`; the maximal disc is `f₀(D(0, r))`.
Modelling: the supremum of the `r` admitting an analytic injective `f` on `D(0, r)` with `f(0) = p` along which `φ`
pulls back to `dw²`; `[0, ∞]`-valued. -/
def maximalDiscRadius (q : S → ℂ → ℂ) (p : S) : ENNReal :=
  ⨆ (r : ENNReal) (f : ℂ → S) (_ : f 0 = p ∧ InjOn f (Metric.eball 0 r) ∧
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (Metric.eball 0 r) ∧ ∀ w ∈ Metric.eball (0 : ℂ) r,
      q (f w) (chartAt ℂ (f w) (f w)) * deriv (fun v => chartAt ℂ (f w) (f v)) w ^ 2 = 1), r

/-! ## §6.6 Non-periodic trajectories -/

/-- Helper. `γ` is parametrized on `I` by a natural parameter: `φ(z(t)) z′(t)² = 1`, i.e. by `φ`-arc length along a
horizontal line (Lehto's `f` on `I = G ∩ ℝ`). -/
def IsNaturalParametrization (q : S → ℂ → ℂ) (γ : ℝ → S) (J : Set ℝ) : Prop :=
  IsRegularPath γ J ∧ ∀ t ∈ J,
    q (γ t) (chartAt ℂ (γ t) (γ t)) * deriv (fun s => chartAt ℂ (γ t) (γ s)) t ^ 2 = 1

/-- **Definition** (trajectory ray, Ch. IV §6.6): for a trajectory `α = γ(I)` through `p₀ = γ(0)`, the ray
`α⁺ = γ([0, u_∞))`, `u_∞ = sup I` (the other ray `α⁻` is the ray of `t ↦ γ(−t)` on `−I`). -/
def trajectoryRay (γ : ℝ → S) (J : Set ℝ) : Set S := γ '' (J ∩ Ici 0)

/-- **Definition** (limit set of a ray, Ch. IV §6.6): the points `p` with `γ(uₙ) → p` for a sequence `uₙ ∈ I` tending
to `u_∞ = sup I`.
Modelling: `uₙ` eventually exceeds every point of `I`. -/
def rayLimitSet (γ : ℝ → S) (J : Set ℝ) : Set S :=
  {p | ∃ u : ℕ → ℝ, (∀ n, u n ∈ J) ∧ (∀ t ∈ J, ∀ᶠ n in atTop, t < u n) ∧ Tendsto (fun n => γ (u n)) atTop (𝓝 p)}

/-- **Definition** (boundary ray, Ch. IV §6.6): the limit set is empty (`α⁺` tends to the boundary of `S`). -/
def IsBoundaryRay (γ : ℝ → S) (J : Set ℝ) : Prop := rayLimitSet γ J = ∅

/-- **Definition** (cross-cut, Ch. IV §6.6): both rays `α⁺` and `α⁻` are boundary rays. (A trajectory notion; not
the crosscuts of domains `LiZhongQC.IsCrosscut`, `GardinerLakic2000.IsCrosscut`, `Pommerenke1992.IsCrosscut`.) -/
def IsCrossCut (γ : ℝ → S) (J : Set ℝ) : Prop :=
  IsBoundaryRay γ J ∧ IsBoundaryRay (fun t => γ (-t)) (Neg.neg ⁻¹' J)

/-- **Definition** (critical ray, Ch. IV §6.6): the limit set is a single point, a zero of `φ`. -/
def IsCriticalRay (q : S → ℂ → ℂ) (γ : ℝ → S) (J : Set ℝ) : Prop :=
  ∃ p : S, rayLimitSet γ J = {p} ∧ ¬ IsRegularPoint q p

/-- **Definition** (divergent ray, Ch. IV §6.6): the limit set contains more than one point. -/
def IsDivergentRay (γ : ℝ → S) (J : Set ℝ) : Prop := (rayLimitSet γ J).Nontrivial

/-- **Definition** (recurrent ray, Ch. IV §6.6): the initial point `p₀ = γ(0)` belongs to the limit set. -/
def IsRecurrentRay (γ : ℝ → S) (J : Set ℝ) : Prop := γ 0 ∈ rayLimitSet γ J

/-- **Definition** (spiral, Ch. IV §6.6): a trajectory both rays of which are recurrent; its limit set is a spiral
set. -/
def IsSpiralTrajectory (γ : ℝ → S) (J : Set ℝ) : Prop :=
  IsRecurrentRay γ J ∧ IsRecurrentRay (fun t => γ (-t)) (Neg.neg ⁻¹' J)

/-- **Unlabelled** (Ch. IV §6.6, P1:5751–5765). Let `α = γ(I)`, `0 ∈ I`, be a non-periodic horizontal trajectory in
its natural parametrization, and `L` the limit set of the ray `α⁺`. Then:
(a) on a compact surface `L` is not empty (there are no boundary rays);
(b) if `L` is a single point, it is a zero of `φ` (the ray is critical);
(c) if `L` contains more than one point, `α⁺` has infinite length;
(d) if `p₀ = γ(0) ∈ L` (the ray is recurrent), then `L = cl α`.
Modelling: non-periodic: `γ` injective on `I`; the length of `α⁺` is `sup I` (`φ`-arc length). -/
theorem para4_6_6 [T2Space S] [SecondCountableTopology S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {γ : ℝ → S} {J : Set ℝ} (hγ : IsHorizontalTrajectory q γ J)
    (hnat : IsNaturalParametrization q γ J) (hinj : InjOn γ J) (h0 : (0 : ℝ) ∈ J) :
    (CompactSpace S → (rayLimitSet γ J).Nonempty) ∧
      (∀ p : S, rayLimitSet γ J = {p} → ¬ IsRegularPoint q p) ∧
      ((rayLimitSet γ J).Nontrivial → ¬ BddAbove J) ∧
      (γ 0 ∈ rayLimitSet γ J → rayLimitSet γ J = closure (γ '' J)) := by
  sorry

end Lehto1987
