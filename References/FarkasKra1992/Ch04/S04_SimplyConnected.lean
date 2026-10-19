import References.FarkasKra1992.Ch04.S03_Classification
import References.Forster1981.Ch01.S05_TheUniversalCoveringAndCoveringTransformations
import LiZhongQC.Ch06.S22_RiemannSurfaces

/-!
# Farkas–Kra, Chapter IV §4: The uniformization theorem for simply connected surfaces

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. IV §4 (`full.md` FK2:413–856).

Conventions: as in `Ch04/S03_Classification`. The first homology group is `H₁(M) = Abelianization(π₁(M))` (Hurewicz;
leader ruling, 2026-10-09), so `H₁(M) = {0}` is `IsHomologicallyTrivial M`. Meromorphic functions on `M` are
`LiZhongQC.IsMeromorphicRS f` (meromorphic in every chart, `f : M → ℂ`), with order `LiZhongQC.ordRS`; "holomorphic at
`x`" is `AnalyticAt ℂ (localExpr f x) (chartAt ℂ x x)`. The model surfaces are `ℂ̂ = References.RiemannSphere`, `ℂ`, and
`Δ = Forster1981.unitDiscOpen`.

* Definition (homologically trivial surface, IV.4.1) — `IsHomologicallyTrivial`
* Theorem IV.4.1 — `thm4_4_1`
* Theorem IV.4.2 — deferred: the statement is about the analytic continuation of a germ of a meromorphic function
  along paths (the sheaf of meromorphic germs); Forster Part A has analytic continuation only for holomorphic germs (§7)
* Corollary IV.4.2, part 1 — `cor4_4_2_a`
* Corollary IV.4.2, part 2 — `cor4_4_2_b`
* Proposition IV.4.3 — `prop4_4_3`
* Theorem IV.4.4 — `thm4_4_4`
* Theorem IV.4.5, part 1 — `thm4_4_5_a`
* Theorem IV.4.5, part 2 — `thm4_4_5_b`
* Lemma IV.4.6 — `lemma4_4_6`
* Corollary IV.4.6 — `cor4_4_6`
* Lemma IV.4.7 — `lemma4_4_7`

Omitted (U−): the Remark after IV.4.2, Remarks 1–2 after IV.4.3, IV.4.8 (proof of IV.4.5, with the Assertion).
-/

open scoped Manifold ContDiff Topology References
open Set Filter

noncomputable section

namespace FarkasKra1992

open LiZhongQC (IsMeromorphicRS ordRS localExpr RSConformallyEquivalent)
open References (RiemannSphere)

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **Homologically trivial** (Ch. IV §4.1). A Riemann surface `M` is *homologically trivial* if `H₁(M) = {0}`.
Modelling: `H₁(M)` is the abelianization of the fundamental group (Hurewicz; Mathlib has no singular `H₁` for spaces);
this hypothesis is strictly weaker than `SimplyConnectedSpace` before the uniformization theorem is known. -/
def IsHomologicallyTrivial (M : Type) [TopologicalSpace M] : Prop :=
  ∀ x₀ : M, Subsingleton (Abelianization (FundamentalGroup M x₀))

/-- **Theorem IV.4.1** (Ch. IV §4.1). Let `M` be a homologically trivial Riemann surface. Then `M` is conformally
equivalent to one and only one of: (a) `ℂ ∪ {∞}`, (b) `ℂ`, (c) `Δ = {z ; |z| < 1}`. These correspond to the surface `M`
being (a) elliptic, (b) parabolic, (c) hyperbolic. -/
theorem thm4_4_1 (hM : IsHomologicallyTrivial M) :
    (RSConformallyEquivalent M RiemannSphere ∨ RSConformallyEquivalent M ℂ ∨
        RSConformallyEquivalent M ↥Forster1981.unitDiscOpen) ∧
      ¬ (RSConformallyEquivalent M RiemannSphere ∧ RSConformallyEquivalent M ℂ) ∧
      ¬ (RSConformallyEquivalent M RiemannSphere ∧ RSConformallyEquivalent M ↥Forster1981.unitDiscOpen) ∧
      ¬ (RSConformallyEquivalent M ℂ ∧ RSConformallyEquivalent M ↥Forster1981.unitDiscOpen) ∧
      (IsElliptic M ↔ RSConformallyEquivalent M RiemannSphere) ∧
      (IsParabolicSurface M ↔ RSConformallyEquivalent M ℂ) ∧
      (IsHyperbolicSurface M ↔ RSConformallyEquivalent M ↥Forster1981.unitDiscOpen) := by
  sorry

/-- **Corollary IV.4.2, part 1** (Ch. IV §4.2, Corollary, case log). Let `M` be a Riemann surface with `H₁(M) = {0}`. Let
`σ` be a discrete subset of `M`, and `u` a harmonic function on `M ∖ σ`. If `u` is locally the log modulus of a
meromorphic function on `M`, then `u` is globally so: there is a meromorphic function `F` on `M`, holomorphic on
`M ∖ σ`, with `u = log |F|` on `M ∖ σ`.
Modelling: `σ` is closed and discrete; "locally" means: every `P ∈ M` has a neighbourhood `N` and a function `f_P`
meromorphic on `N` (holomorphic on `N ∖ σ`) with `u = log |f_P|` on `N ∖ σ`. -/
theorem cor4_4_2_a (hM : IsHomologicallyTrivial M) {σ : Set M} (hσ : IsClosed σ ∧ DiscreteTopology σ) {u : M → ℝ}
    (hu : References.IsHarmonicRS σᶜ u)
    (hloc : ∀ P : M, ∃ N ∈ 𝓝 P, ∃ f : M → ℂ, (∀ x ∈ N, MeromorphicAt (localExpr f x) (chartAt ℂ x x)) ∧
      (∀ x ∈ N, x ∉ σ → AnalyticAt ℂ (localExpr f x) (chartAt ℂ x x)) ∧ ∀ x ∈ N, x ∉ σ → u x = Real.log ‖f x‖) :
    ∃ F : M → ℂ, IsMeromorphicRS F ∧ (∀ x, x ∉ σ → AnalyticAt ℂ (localExpr F x) (chartAt ℂ x x)) ∧
      ∀ x, x ∉ σ → u x = Real.log ‖F x‖ := by
  sorry

/-- **Corollary IV.4.2, part 2** (Ch. IV §4.2, Corollary, case real part). As part 1, with "real part" in place of "log
modulus": if `u` is locally the real part of a meromorphic function (holomorphic off `σ`) then `u = Re F` on `M ∖ σ` for a
meromorphic `F` on `M`, holomorphic on `M ∖ σ`. -/
theorem cor4_4_2_b (hM : IsHomologicallyTrivial M) {σ : Set M} (hσ : IsClosed σ ∧ DiscreteTopology σ) {u : M → ℝ}
    (hu : References.IsHarmonicRS σᶜ u)
    (hloc : ∀ P : M, ∃ N ∈ 𝓝 P, ∃ f : M → ℂ, (∀ x ∈ N, MeromorphicAt (localExpr f x) (chartAt ℂ x x)) ∧
      (∀ x ∈ N, x ∉ σ → AnalyticAt ℂ (localExpr f x) (chartAt ℂ x x)) ∧ ∀ x ∈ N, x ∉ σ → u x = (f x).re) :
    ∃ F : M → ℂ, IsMeromorphicRS F ∧ (∀ x, x ∉ σ → AnalyticAt ℂ (localExpr F x) (chartAt ℂ x x)) ∧
      ∀ x, x ∉ σ → u x = (F x).re := by
  sorry

/-- **Proposition IV.4.3** (Ch. IV §4.3). Let `D` be a domain in the extended plane `ℂ ∪ {∞} = S²` with `H₁(D) = {0}`.
Then `D` is hyperbolic unless `S² ∖ D` contains at most one point: if `S² ∖ D` has at least two points, `D` is
hyperbolic. -/
theorem prop4_4_3 {D : TopologicalSpace.Opens RiemannSphere} (hDc : IsConnected (D : Set RiemannSphere))
    (hD : IsHomologicallyTrivial D) (h2 : (Set.univ \ (D : Set RiemannSphere)).Nontrivial) :
    IsHyperbolicSurface D := by
  sorry

/-- **Theorem IV.4.4** (Ch. IV §4.4). If `M` is a hyperbolic Riemann surface with `H₁(M) = {0}`, then `M` is
conformally equivalent to the unit disc `Δ`. -/
theorem thm4_4_4 (hM : IsHomologicallyTrivial M) (hh : IsHyperbolicSurface M) :
    RSConformallyEquivalent M ↥Forster1981.unitDiscOpen := by
  sorry

/-- **Theorem IV.4.5, part 1** (Ch. IV §4.5). Let `M` be a Riemann surface with `H₁(M) = {0}`. If `M` is compact, then
`M` is conformally equivalent to the complex sphere `ℂ ∪ {∞}`. -/
theorem thm4_4_5_a (hM : IsHomologicallyTrivial M) (hc : CompactSpace M) :
    RSConformallyEquivalent M RiemannSphere := by
  sorry

/-- **Theorem IV.4.5, part 2** (Ch. IV §4.5). Let `M` be a Riemann surface with `H₁(M) = {0}`. If `M` is parabolic,
then `M` is conformally equivalent to the complex plane `ℂ`. -/
theorem thm4_4_5_b (hM : IsHomologicallyTrivial M) (hp : IsParabolicSurface M) : RSConformallyEquivalent M ℂ := by
  sorry

/-- **Lemma IV.4.6** (Ch. IV §4.6). Let `D` be a relatively compact domain on a Riemann surface `M` and `P₀ ∈ D`. Let `f`
be a meromorphic function on `Cl D` whose only singularity is a simple pole at `P₀`. Then there is a neighbourhood `N`
of `P₀` such that for any `Q₀ ∈ N`, `f(Q) ≠ f(Q₀)` for all `Q ∈ D ∖ {Q₀}`.
Modelling: for `Q₀ = P₀` (`f(P₀) = ∞`) this says that `f` takes no value `∞` elsewhere, so `Q₀ ∈ N ∖ {P₀}` and
`Q ≠ P₀`. -/
theorem lemma4_4_6 {D : Set M} (hD : IsOpen D) (hDc : IsConnected D) (hrel : IsCompact (closure D)) {P₀ : M}
    (hP₀ : P₀ ∈ D) {f : M → ℂ} (hmero : ∀ x ∈ closure D, MeromorphicAt (localExpr f x) (chartAt ℂ x x))
    (hhol : ∀ x ∈ closure D, x ≠ P₀ → AnalyticAt ℂ (localExpr f x) (chartAt ℂ x x))
    (hpole : ordRS f P₀ = ((-1 : ℤ) : WithTop ℤ)) :
    ∃ N ∈ 𝓝 P₀, ∀ Q₀ ∈ N, Q₀ ≠ P₀ → ∀ Q ∈ D, Q ≠ Q₀ → Q ≠ P₀ → f Q ≠ f Q₀ := by
  sorry

/-- **Corollary IV.4.6** (Ch. IV §4.6). Let `M` be a parabolic or compact Riemann surface and `P₀ ∈ M`. Assume that
`f ∈ 𝒦(M)` with `ord_{P₀} f = −1`, `f` is holomorphic on `M ∖ {P₀}` and `f` is bounded outside some relatively compact
neighbourhood of `P₀`. Then there exists a neighbourhood `N` of `P₀` such that for any `Q₀ ∈ N`,
`f(Q) ≠ f(Q₀)` for all `Q ∈ M ∖ {Q₀}`. (Modelling as in `lemma4_4_6`: `Q₀ ≠ P₀`, `Q ≠ P₀`.) -/
theorem cor4_4_6 (hM : IsParabolicSurface M ∨ CompactSpace M) {P₀ : M} {f : M → ℂ} (hf : IsMeromorphicRS f)
    (hhol : ∀ x, x ≠ P₀ → AnalyticAt ℂ (localExpr f x) (chartAt ℂ x x))
    (hpole : ordRS f P₀ = ((-1 : ℤ) : WithTop ℤ))
    (hb : ∃ N₁ ∈ 𝓝 P₀, IsCompact (closure N₁) ∧ ∃ B : ℝ, ∀ x ∉ N₁, ‖f x‖ ≤ B) :
    ∃ N ∈ 𝓝 P₀, ∀ Q₀ ∈ N, Q₀ ≠ P₀ → ∀ Q, Q ≠ Q₀ → Q ≠ P₀ → f Q ≠ f Q₀ := by
  sorry

/-- **Lemma IV.4.7** (Ch. IV §4.7). Let `M` be a parabolic or compact Riemann surface with `H₁(M) = {0}`. Let `P₀ ∈ M`.
There exists a function `f ∈ 𝒦(M)` with `ord_{P₀} f = −1` that is bounded outside every neighbourhood of `P₀`
(and holomorphic on `M ∖ {P₀}`). -/
theorem lemma4_4_7 (hM : IsParabolicSurface M ∨ CompactSpace M) (hH : IsHomologicallyTrivial M) (P₀ : M) :
    ∃ f : M → ℂ, IsMeromorphicRS f ∧ (∀ x, x ≠ P₀ → AnalyticAt ℂ (localExpr f x) (chartAt ℂ x x)) ∧
      ordRS f P₀ = ((-1 : ℤ) : WithTop ℤ) ∧ ∀ N ∈ 𝓝 P₀, ∃ B : ℝ, ∀ x ∉ N, ‖f x‖ ≤ B := by
  sorry

end FarkasKra1992
