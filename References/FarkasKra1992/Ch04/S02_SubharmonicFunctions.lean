import References.FarkasKra1992.Ch04.S01_HarmonicFunctions
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Farkas–Kra, Chapter IV §2: Subharmonic functions and Perron's method

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. IV §2 (`full.md` FK1:7453–7848).

Conventions: as in `Ch04/S01_HarmonicFunctions`. Subharmonic, superharmonic functions and Perron families are the
shared `References.IsSubharmonicRS U u`, `IsSuperharmonicRS`, `IsPerronFamily` (mean-value definitions in the charts of the
maximal analytic atlas; FK's definition by the maximum principle (IV.2.1) is Proposition IV.2.1 below, the
characterization by the harmonization `u^{(K)}` is Proposition IV.2.2). A function "subharmonic on `M`" is
`IsSubharmonicRS univ u`. A *conformal disc* is a coordinate disc `e⁻¹(B(0, ρ))`, `ρ > 1`, of a chart `e` of the maximal
atlas whose closed disc lies in the chart image. The harmonization `u^{(K)}` (continuous on `M`, equal to `u` off `K`,
harmonic in `K`) is the predicate `IsHarmonicReplacement K u v`; its existence and uniqueness is the Dirichlet problem
for the disc (`thm4_1_3`).

* Definition IV.2.1 (subharmonic function; FK's definition) — exists: `References.IsSubharmonicRS`
* Proposition IV.2.1 — `prop4_2_1`
* Corollary IV.2.1 — `cor4_2_1`
* Definition IV.2.2 (conformal disc) — `IsConformalDisc`
* Definition IV.2.2 (harmonization `u^{(K)}`) — `IsHarmonicReplacement`
* Proposition IV.2.2 — `prop4_2_2`
* Corollary IV.2.2, part 1 — `cor4_2_2_a`
* Corollary IV.2.2, part 2 — `cor4_2_2_b`
* Proposition IV.2.3 — `prop4_2_3`
* Proposition IV.2.4 — `prop4_2_4`
* Proposition IV.2.5 — `prop4_2_5`
* Definition IV.2.6 (Perron family) — exists: `References.IsPerronFamily`
* Theorem IV.2.6 (Perron's principle) — `thm4_2_6`
* Definition IV.2.7 (barrier) — `IsBarrier`
* IV.2.7 (Remark: an analytic arc reaching `P` gives a barrier) — `para4_2_7`
* Definition IV.2.8 (regular point) — `IsRegularPoint`
* Definition IV.2.8 (proper solution) — `IsProperSolution`
* Theorem IV.2.8 — `thm4_2_8`

Omitted (U−): Remarks 1–2 after IV.2.6 (`u^{(K)}` and `max` are the usual `v`; finitely many `u_j`), the Remark after the
proof of Perron's principle (uniform convergence on compacts), the normalized barrier in IV.2.7 (a construction).
-/

open scoped Manifold ContDiff Topology Real
open Set Filter Metric

noncomputable section

namespace FarkasKra1992

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **Conformal disc** (Ch. IV §2.2). A *conformal disc* `K ⊂ M` is an open set whose closure lies in a single
coordinate patch (with local coordinate `z`) such that `z(Cl K)` is a closed disc in `ℂ` of radius `> 1` and centre `0`.
Modelling: `z` is a chart `e` of the maximal analytic atlas with `closedBall 0 ρ ⊆ e.target`, `ρ > 1`, and
`K = e⁻¹(ball 0 ρ)`. -/
def IsConformalDisc (K : Set M) : Prop :=
  ∃ e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas M, ∃ ρ : ℝ, 1 < ρ ∧ closedBall 0 ρ ⊆ e.target ∧
    K = e.symm '' ball 0 ρ

/-- **Harmonization** (Ch. IV §2.2). For `u ∈ C(M)` and a conformal disc `K`, `v = u^{(K)}` is the function with
`v ∈ C(M)`, `v | M ∖ K = u | M ∖ K` and `v` harmonic in `K` (exists and unique by the Dirichlet problem for the disc).
Modelling: a predicate on `v`. -/
def IsHarmonicReplacement (K : Set M) (u v : M → ℝ) : Prop :=
  Continuous v ∧ (∀ x, x ∉ K → v x = u x) ∧ References.IsHarmonicRS K v

/-- **Proposition IV.2.1** (Ch. IV §2.1). Let `u` be continuous on `M`. The following are equivalent: (a) `u` is
subharmonic (FK's definition: for every domain `D` and every harmonic `h` on `D` with `u ≤ h` on `D`, either `u ≡ h` on
`D` or `u < h` on `D`); (b) for every domain `D ⊂ M` and every harmonic function `h` on `D`, `u + h` has no maximum in
`D` unless `u + h` is constant on `D`; (c) `u` is subharmonic in the sense of `References.IsSubharmonicRS` (mean-value
property in the charts). (The book says "harmonic function `h` on `M`" in (b), a slip for `D`.) -/
theorem prop4_2_1 {u : M → ℝ} (hu : Continuous u) :
    List.TFAE [References.IsSubharmonicRS univ u,
      ∀ D : Set M, IsOpen D → IsConnected D → ∀ h : M → ℝ, References.IsHarmonicRS D h → (∀ x ∈ D, u x ≤ h x) →
        (∀ x ∈ D, u x = h x) ∨ (∀ x ∈ D, u x < h x),
      ∀ D : Set M, IsOpen D → IsConnected D → ∀ h : M → ℝ, References.IsHarmonicRS D h → ∀ H : ℝ,
        (∃ x ∈ D, u x + h x = H) → (∀ x ∈ D, u x + h x ≤ H) → ∀ x ∈ D, u x + h x = H] := by
  sorry

/-- **Corollary IV.2.1** (Ch. IV §2.1). Subharmonicity is a local property: a continuous function subharmonic in a
neighbourhood of every point is subharmonic. -/
theorem cor4_2_1 {u : M → ℝ} (hu : Continuous u)
    (h : ∀ P : M, ∃ U : Set M, IsOpen U ∧ P ∈ U ∧ References.IsSubharmonicRS U u) :
    References.IsSubharmonicRS univ u := by
  sorry

/-- **Proposition IV.2.2** (Ch. IV §2.2). Let `u ∈ C(M)`. The function `u` is subharmonic if and only if
`u ≤ u^{(K)}` for every conformal disc `K` on `M`. -/
theorem prop4_2_2 {u : M → ℝ} (hu : Continuous u) :
    References.IsSubharmonicRS univ u ↔
      ∀ K : Set M, IsConformalDisc K → ∀ v : M → ℝ, IsHarmonicReplacement K u v → ∀ x, u x ≤ v x := by
  sorry

/-- **Corollary IV.2.2, part 1** (Ch. IV §2.2, Corollary of the proof). Let `u ∈ C(M)`. Then `u` is subharmonic if and
only if `u(0) ≤ (1/2π) ∫₀^{2π} u(e^{iθ}) dθ` for every conformal disc: for every chart `e` of the maximal atlas and every
`ρ > 1` with `closedBall 0 ρ ⊆ e.target`, `u(e⁻¹ 0)` is at most the circle average of `u ∘ e⁻¹` over the unit circle. -/
theorem cor4_2_2_a {u : M → ℝ} (hu : Continuous u) :
    References.IsSubharmonicRS univ u ↔
      ∀ e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas M, ∀ ρ : ℝ, 1 < ρ → closedBall 0 ρ ⊆ e.target →
        u (e.symm 0) ≤ Real.circleAverage (fun w => u (e.symm w)) 0 1 := by
  sorry

/-- **Corollary IV.2.2, part 2** (Ch. IV §2.2, Corollary of Corollary). Let `D` be a domain on `M`. Assume that
`u ∈ C(Cl D)` is subharmonic and non-negative on `D` and identically zero on `δD`. Extend `u` to be zero on `M ∖ D`.
Then `u` is subharmonic on `M`. -/
theorem cor4_2_2_b {D : Set M} (hD : IsOpen D) (hDc : IsConnected D) {u : M → ℝ} (hu : ContinuousOn u (closure D))
    (hsub : References.IsSubharmonicRS D u) (hnn : ∀ x ∈ D, 0 ≤ u x) (hzero : ∀ x ∈ frontier D, u x = 0) :
    References.IsSubharmonicRS univ (indicator (closure D) u) := by
  sorry

/-- **Proposition IV.2.3** (Ch. IV §2.3). Let `u`, `v` be subharmonic functions on `M`, `c ∈ ℝ`, `c ≥ 0`, and `K` a
conformal disc on `M`. Then `cu`, `u + v`, `max {u, v}` and `u^{(K)}` are all subharmonic. -/
theorem prop4_2_3 {u v : M → ℝ} (hu : References.IsSubharmonicRS univ u) (hv : References.IsSubharmonicRS univ v)
    {c : ℝ} (hc : 0 ≤ c) {K : Set M} (hK : IsConformalDisc K) :
    References.IsSubharmonicRS univ (fun x => c * u x) ∧ References.IsSubharmonicRS univ (fun x => u x + v x) ∧
      References.IsSubharmonicRS univ (fun x => max (u x) (v x)) ∧
      ∀ w : M → ℝ, IsHarmonicReplacement K u w → References.IsSubharmonicRS univ w := by
  sorry

/-- **Proposition IV.2.4** (Ch. IV §2.4). Let `u ∈ C(M)`. Then `u` is harmonic if and only if `u` is subharmonic and
superharmonic. -/
theorem prop4_2_4 {u : M → ℝ} (hu : Continuous u) :
    References.IsHarmonicRS univ u ↔
      References.IsSubharmonicRS univ u ∧ References.IsSuperharmonicRS univ u := by
  sorry

/-- **Proposition IV.2.5** (Ch. IV §2.5). Let `u ∈ C²(M)`. Then `u` is subharmonic if and only if `Δu ≥ 0`.
Modelling: `u ∈ C²(M)` is `ContDiffOn ℝ 2` of `u ∘ e⁻¹` on the chart image for every chart `e` of the maximal atlas;
`Δu ≥ 0` is the condition in every chart (a well-defined concept, since the transition maps are analytic). -/
theorem prop4_2_5 {u : M → ℝ}
    (hC2 : ∀ e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas M, ContDiffOn ℝ 2 (fun w => u (e.symm w)) e.target) :
    References.IsSubharmonicRS univ u ↔
      ∀ e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas M, ∀ w ∈ e.target,
        0 ≤ Laplacian.laplacian (fun z => u (e.symm z)) w := by
  sorry

/-- **Perron's principle** (Ch. IV §2.6, Theorem). Let `𝓕` be a Perron family on `M` and define
`u(P) = sup_{v ∈ 𝓕} v(P)`. Then either `u ≡ +∞` or `u` is harmonic.
Modelling: `u ≡ +∞` is "for every `P` the set `{v(P) ; v ∈ 𝓕}` is unbounded above"; `u` harmonic is the existence of a
harmonic `h` on `M` with `h(P)` the least upper bound of `{v(P) ; v ∈ 𝓕}` for all `P`. -/
theorem thm4_2_6 {𝓕 : Set (M → ℝ)} (hF : References.IsPerronFamily 𝓕) :
    (∀ P : M, ¬ BddAbove ((fun v : M → ℝ => v P) '' 𝓕)) ∨
      ∃ h : M → ℝ, References.IsHarmonicRS univ h ∧ ∀ P : M, IsLUB ((fun v : M → ℝ => v P) '' 𝓕) (h P) := by
  sorry

/-- **Barrier** (Ch. IV §2.7). Let `D` be a region with boundary `δD` on `M` and `P ∈ δD`. A function `β` is a *barrier
at `P`* provided there is a neighbourhood `N` of `P` such that (2.7.1) `β ∈ C(Cl(D ∩ N))`, (2.7.2) `β` is superharmonic on
`Int(D ∩ N)`, (2.7.3) `β(P) = 0`, and (2.7.4) `β(Q) > 0` for `Q ≠ P`, `Q ∈ Cl(D ∩ N)`. -/
def IsBarrier (D : Set M) (P : M) (β : M → ℝ) : Prop :=
  ∃ N ∈ 𝓝 P, ContinuousOn β (closure (D ∩ N)) ∧ References.IsSuperharmonicRS (interior (D ∩ N)) β ∧ β P = 0 ∧
    ∀ Q ∈ closure (D ∩ N), Q ≠ P → 0 < β Q

/-- **Unlabelled** (Ch. IV §2.7, Remark). If `P ∈ δD` can be reached by an analytic arc (the image of a straight line
under a holomorphic mapping) with no points in common with `Cl D`, then there exists a barrier at `P`.
Modelling: the arc is `t ↦ φ(tw)`, `0 < t < ε`, for a map `φ : ℂ → M` holomorphic near `0` with `φ(0) = P` and non-zero
derivative in a chart (so the arc is regular); `D` is open. -/
theorem para4_2_7 {D : Set M} (hD : IsOpen D) {P : M} (hP : P ∈ frontier D) {φ : ℂ → M}
    (hφ : ∃ U ∈ 𝓝 (0 : ℂ), MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) φ U) (h0 : φ 0 = P)
    (hreg : ∃ e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas M, P ∈ e.source ∧ deriv (fun z => e (φ z)) 0 ≠ 0)
    (harc : ∃ (w : ℂ) (ε : ℝ), 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε → φ (t * w) ∉ closure D) :
    ∃ β : M → ℝ, IsBarrier D P β := by
  sorry

/-- **Regular point** (Ch. IV §2.8). Let `D ⊂ M`. A point `P ∈ δD` is called a *regular point* (for the Dirichlet problem)
if there exists a barrier at `P`. -/
def IsRegularPoint (D : Set M) (P : M) : Prop := P ∈ frontier D ∧ ∃ β : M → ℝ, IsBarrier D P β

/-- **Proper solution** (Ch. IV §2.8). A solution `u` to the Dirichlet problem for a bounded `f ∈ C(δD)` is *proper*
provided `inf {f(P) ; P ∈ δD} ≤ u(Q) ≤ sup {f(P) ; P ∈ δD}` for all `Q ∈ Cl D`.
Modelling: `δD` is non-empty and `f` bounded on it (otherwise the infimum and supremum are junk values). -/
def IsProperSolution (D : Set M) (f u : M → ℝ) : Prop :=
  IsDirichletSolution D f u ∧ ∀ Q ∈ closure D, sInf (f '' frontier D) ≤ u Q ∧ u Q ≤ sSup (f '' frontier D)

/-- **Theorem IV.2.8** (Ch. IV §2.8). The following are equivalent for an open set `D ⊂ M` with non-empty boundary:
(a) there exists a proper solution for every bounded `f ∈ C(δD)`; (b) every point of `δD` is regular. -/
theorem thm4_2_8 {D : Set M} (hD : IsOpen D) (hne : (frontier D).Nonempty) :
    (∀ f : M → ℝ, ContinuousOn f (frontier D) → (∃ B : ℝ, ∀ P ∈ frontier D, |f P| ≤ B) →
      ∃ u : M → ℝ, IsProperSolution D f u) ↔ ∀ P ∈ frontier D, IsRegularPoint D P := by
  sorry

end FarkasKra1992
