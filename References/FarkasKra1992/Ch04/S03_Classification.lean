import References.FarkasKra1992.Ch04.S02_SubharmonicFunctions
import References.Common.RiemannSphere
import References.Hubbard2006.Ch01.S03_Rado

/-!
# Farkas–Kra, Chapter IV §3: A classification of Riemann surfaces

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. IV §3 (`full.md` FK1:7849–8228, FK2:1–412).

Conventions: as in `Ch04/S01_HarmonicFunctions` and `Ch04/S02_SubharmonicFunctions`. A *region* or *domain* is an open
(connected) set; `δD` is `frontier D`, `Cl D` is `closure D`. Green's functions are the shared
`References.IsGreenFunction P g` (minimal positive harmonic function on `M ∖ {P}` with logarithmic pole at `P`); the Green's
function `g(P, ·)` of a hyperbolic surface is any `g` with `IsGreenFunction P g` (unique by minimality), and the Green's
function of a domain `D` is `IsGreenFunction` on the Riemann surface `↥D`. The flux `∫ *du` over a circle `|z| = r` is
`circleFlux` (`*du = (∂u/∂r) r dθ` on the circle). Items whose text needs the machinery of Chapters I–III
(IV.3.18 Corollary 1, the Riemannian metric; Corollary 4, triangulation) are deferred; Corollary 3 (second countability,
Radó) is `Hubbard2006.thm1_3_3`.

* Lemma IV.3.1 — `IsAnalyticClosedCurve`, `HasAnalyticBoundary`, `lemma4_3_1`
* Definition IV.3.2 (elliptic) — `IsElliptic`
* Definition IV.3.2 (parabolic) — `IsParabolicSurface`
* Definition IV.3.2 (hyperbolic) — `IsHyperbolicSurface`
* Theorem IV.3.3 — `thm4_3_3`
* Corollary IV.3.3, part 1 — `cor4_3_3_a`
* Corollary IV.3.3, part 2 — `cor4_3_3_b`
* Theorem IV.3.4 — `IsHarmonicMeasureCandidate`, `thm4_3_4`
* Remark IV.3.4 (harmonic measure) — `IsHarmonicMeasure`
* IV.3.5 (the harmonic measure exists) — `para4_3_5`
* Corollary IV.3.5 — `cor4_3_5`
* Definition IV.3.6 (Green's function) — exists: `References.IsGreenFunction`
* Theorem IV.3.7 — `thm4_3_7`
* Remark IV.3.7 (Green's function at every point of a hyperbolic surface) — `para4_3_7`
* Lemma IV.3.8 — `lemma4_3_8`
* Lemma IV.3.9 — `lemma4_3_9`
* Theorem IV.3.10 — `thm4_3_10`
* Theorem IV.3.11 — `thm4_3_11`
* Lemma IV.3.12 — `lemma4_3_12`
* Lemma IV.3.13 — `lemma4_3_13`
* Lemma IV.3.14 — `lemma4_3_14`
* Lemma IV.3.15 — `circleFlux`, `lemma4_3_15`
* Theorem IV.3.17 — `thm4_3_17`
* Corollary IV.3.18, part 2 (metrizable) — `cor4_3_18_b`
* Corollary IV.3.18, part 3 (second countability, Radó) — exists: `Hubbard2006.thm1_3_3`

Omitted (U−): IV.3.2 Remark (hyperbolic ⇒ not compact), the Remark after IV.3.5, the Remark on the independence of (3.6.3)
from the parameter, the classical example, the Exercises, the Digression (3.10.1), IV.3.16 (proof of IV.3.11).
Deferred: IV.3.18 Corollary 1 (a `C^∞` Riemannian metric consistent with the conformal structure: no Riemannian metric
notion), Corollary 4 (triangulation: W-TOP). 
-/

open scoped Manifold ContDiff Topology Real References
open Set Filter Metric

noncomputable section

namespace FarkasKra1992

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **Closed analytic curve** (Ch. IV §3.1, helper). A closed analytic curve on `M`: the image of the unit circle
under a map holomorphic near the circle, injective on the circle, with non-zero derivative in the charts. -/
def IsAnalyticClosedCurve (C : Set M) : Prop :=
  ∃ (U : Set ℂ) (φ : ℂ → M), IsOpen U ∧ sphere (0 : ℂ) 1 ⊆ U ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) φ U ∧
    InjOn φ (sphere 0 1) ∧ (∀ z ∈ sphere (0 : ℂ) 1, ∀ e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas M,
      φ z ∈ e.source → deriv (fun w => e (φ w)) z ≠ 0) ∧ φ '' sphere 0 1 = C

/-- **Analytic boundary** (Ch. IV §3.1, helper). The boundary `δD` consists of finitely many closed analytic curves. -/
def HasAnalyticBoundary (D : Set M) : Prop :=
  ∃ F : Finset (Set M), (∀ C ∈ F, IsAnalyticClosedCurve C) ∧ frontier D = ⋃ C ∈ F, C

/-- **Lemma IV.3.1** (Ch. IV §3.1). Let `K` be a compact connected region on a Riemann surface `M`, with `K ≠ M`. There
exists a domain `D` on `M` with `K ⊂ D`, `Cl D` compact, and `δD` consisting of finitely many closed analytic curves. -/
theorem lemma4_3_1 {K : Set M} (hK : IsCompact K) (hKc : IsConnected K) (hKM : K ≠ univ) :
    ∃ D : Set M, IsOpen D ∧ IsConnected D ∧ K ⊆ D ∧ IsCompact (closure D) ∧ HasAnalyticBoundary D := by
  sorry

/-- **Elliptic** (Ch. IV §3.2). A Riemann surface `M` is *elliptic* if and only if `M` is compact. -/
def IsElliptic (M : Type) [TopologicalSpace M] : Prop := CompactSpace M

/-- **Parabolic** (Ch. IV §3.2). `M` is *parabolic* if and only if `M` is not compact and `M` does not carry a negative
non-constant subharmonic function. -/
def IsParabolicSurface (M : Type) [TopologicalSpace M] [ChartedSpace ℂ M] : Prop :=
  ¬ CompactSpace M ∧ ¬ ∃ u : M → ℝ, References.IsSubharmonicRS univ u ∧ (∀ x, u x < 0) ∧ ¬ ∃ c, ∀ x, u x = c

/-- **Hyperbolic** (Ch. IV §3.2). `M` is *hyperbolic* if and only if `M` does carry a negative non-constant
subharmonic function. -/
def IsHyperbolicSurface (M : Type) [TopologicalSpace M] [ChartedSpace ℂ M] : Prop :=
  ∃ u : M → ℝ, References.IsSubharmonicRS univ u ∧ (∀ x, u x < 0) ∧ ¬ ∃ c, ∀ x, u x = c

/-- **Theorem IV.3.3** (Ch. IV §3.3, strong maximum principle). Let `D` be an open set on a parabolic surface `M`. Let
`u ∈ C(Cl D)` be subharmonic in `D`, and assume there exist `m₁, m₂ ∈ ℝ` such that `u ≤ m₁` on `δD` and `u ≤ m₂` on
`Cl D`. Then `u ≤ m₁` on `Cl D`.
Modelling: `δD ≠ ∅`, i.e. `D ≠ M` (for a connected `M` and non-empty `D ≠ M` the frontier is non-empty, so this only
excludes `D = M`, where the hypothesis on `δD` is vacuous and `u ≡ 0`, `m₁ = −1` would be a counterexample). -/
theorem thm4_3_3 (hM : IsParabolicSurface M) {D : Set M} (hD : IsOpen D) (hne : (frontier D).Nonempty) {u : M → ℝ}
    (hu : ContinuousOn u (closure D)) (hsub : References.IsSubharmonicRS D u) {m₁ m₂ : ℝ}
    (h₁ : ∀ x ∈ frontier D, u x ≤ m₁) (h₂ : ∀ x ∈ closure D, u x ≤ m₂) : ∀ x ∈ closure D, u x ≤ m₁ := by
  sorry

/-- **Corollary IV.3.3, part 1** (Ch. IV §3.3, Corollary 1). Let `u` be a bounded real-valued harmonic function on an open
set `D` on a parabolic surface `M`, `u ∈ C(Cl D)`, with `m₀ = inf {u(P) ; P ∈ δD}` and `m₁ = sup {u(P) ; P ∈ δD}`. Then
`m₀ ≤ u ≤ m₁` on `Cl D`. Modelling: `δD ≠ ∅` (otherwise the infimum and supremum are junk values; for `D = M` the
conclusion fails for constants). -/
theorem cor4_3_3_a (hM : IsParabolicSurface M) {D : Set M} (hD : IsOpen D) (hne : (frontier D).Nonempty) {u : M → ℝ}
    (hu : ContinuousOn u (closure D)) (hh : References.IsHarmonicRS D u) (hb : ∃ B : ℝ, ∀ x ∈ closure D, |u x| ≤ B) :
    ∀ x ∈ closure D, sInf (u '' frontier D) ≤ u x ∧ u x ≤ sSup (u '' frontier D) := by
  sorry

/-- **Corollary IV.3.3, part 2** (Ch. IV §3.3, Corollary 2). On a parabolic Riemann surface the Dirichlet problem has at
most one bounded solution. Modelling: `δD ≠ ∅` (for `δD = ∅`, `D = M`, two constants are bounded solutions). -/
theorem cor4_3_3_b (hM : IsParabolicSurface M) {D : Set M} (hD : IsOpen D) (hne : (frontier D).Nonempty)
    {f u₁ u₂ : M → ℝ} (h₁ : IsDirichletSolution D f u₁) (h₂ : IsDirichletSolution D f u₂)
    (hb₁ : ∃ B : ℝ, ∀ x ∈ closure D, |u₁ x| ≤ B) (hb₂ : ∃ B : ℝ, ∀ x ∈ closure D, |u₂ x| ≤ B) :
    EqOn u₁ u₂ (closure D) := by
  sorry

/-- **The properties of the harmonic measure** (Ch. IV §3.4, helper). `ω ∈ C(Cl(M ∖ K))` such that (i) `ω` is harmonic on
`M ∖ K`, (ii) `ω = 1` on `δ(M ∖ K)`, (iii) `0 < ω < 1` on `M ∖ K`. -/
def IsHarmonicMeasureCandidate (K : Set M) (ω' : M → ℝ) : Prop :=
  ContinuousOn ω' (closure Kᶜ) ∧ References.IsHarmonicRS Kᶜ ω' ∧ (∀ x ∈ frontier Kᶜ, ω' x = 1) ∧
    ∀ x ∈ Kᶜ, 0 < ω' x ∧ ω' x < 1

/-- **Theorem IV.3.4** (Ch. IV §3.4). Let `M` be a hyperbolic Riemann surface and `K` a compact subset with `δ(M ∖ K)`
regular and `M ∖ K` connected. Then there exists `ω ∈ C(Cl(M ∖ K))` such that (i) `ω` is harmonic on `M ∖ K`, (ii) `ω = 1`
on `δ(M ∖ K)`, (iii) `0 < ω < 1` on `M ∖ K`. Modelling: `K ≠ ∅` (the proof takes a minimum over `K`). -/
theorem thm4_3_4 (hM : IsHyperbolicSurface M) {K : Set M} (hK : IsCompact K) (hne : K.Nonempty)
    (hreg : ∀ P ∈ frontier Kᶜ, IsRegularPoint Kᶜ P) (hconn : IsConnected Kᶜ) :
    ∃ ω' : M → ℝ, IsHarmonicMeasureCandidate K ω' := by
  sorry

/-- **Harmonic measure** (Ch. IV §3.4, Remark). The smallest `ω` as in Theorem IV.3.4 is the *harmonic measure* of `K`:
`ω` has properties (i)–(iii) and `ω ≤ ω̃` on `M ∖ K` for every `ω̃` with properties (i)–(iii). -/
def IsHarmonicMeasure (K : Set M) (ω' : M → ℝ) : Prop :=
  IsHarmonicMeasureCandidate K ω' ∧ ∀ ω'' : M → ℝ, IsHarmonicMeasureCandidate K ω'' → ∀ x ∈ Kᶜ, ω' x ≤ ω'' x

/-- **Unlabelled** (Ch. IV §3.5, "Important Addition", FK1:7951). Under the hypotheses of Theorem IV.3.4 the harmonic
measure of `K` exists: `ω₁ = sup {v ; v ∈ 𝓕₁}` (compact-support competitors) satisfies (i)–(iii) and `ω₁ ≤ ω̃` for every
`ω̃` with these properties. -/
theorem para4_3_5 (hM : IsHyperbolicSurface M) {K : Set M} (hK : IsCompact K) (hne : K.Nonempty)
    (hreg : ∀ P ∈ frontier Kᶜ, IsRegularPoint Kᶜ P) (hconn : IsConnected Kᶜ) :
    ∃ ω' : M → ℝ, IsHarmonicMeasure K ω' := by
  sorry

/-- **Corollary IV.3.5** (Ch. IV §3.5). Let `M` be a hyperbolic Riemann surface and `D` a domain in `M` with regular
boundary such that `M ∖ D` is compact (and non-empty). Then we have non-uniqueness of solutions for the Dirichlet problem
for `D`: there are a `f ∈ C(δD)` and two distinct bounded solutions. -/
theorem cor4_3_5 (hM : IsHyperbolicSurface M) {D : Set M} (hD : IsOpen D) (hDc : IsConnected D)
    (hreg : ∀ P ∈ frontier D, IsRegularPoint D P) (hcpt : IsCompact Dᶜ) (hne : Dᶜ.Nonempty) :
    ∃ f u₁ u₂ : M → ℝ, ContinuousOn f (frontier D) ∧ IsDirichletSolution D f u₁ ∧ IsDirichletSolution D f u₂ ∧
      (∃ B : ℝ, ∀ x ∈ closure D, |u₁ x| ≤ B) ∧ (∃ B : ℝ, ∀ x ∈ closure D, |u₂ x| ≤ B) ∧
      ∃ x ∈ closure D, u₁ x ≠ u₂ x := by
  sorry

/-- **Theorem IV.3.7** (Ch. IV §3.7). Let `M` be a Riemann surface. There exists a Green's function on `M` (with
singularity at some point `P ∈ M`) if and only if `M` is hyperbolic. -/
theorem thm4_3_7 : (∃ (P : M) (g : M → ℝ), References.IsGreenFunction P g) ↔ IsHyperbolicSurface M := by
  sorry

/-- **Unlabelled** (Ch. IV §3.7, Remark). On a hyperbolic surface there is a Green's function with singularity at every
point (existence at one point ⇒ hyperbolic ⇒ harmonic measures exist ⇒ Green's function at every point); `g(P, Q)` is the
value at `Q` of the Green's function with singularity at `P`. -/
theorem para4_3_7 (hM : IsHyperbolicSurface M) (P : M) : ∃ g : M → ℝ, References.IsGreenFunction P g := by
  sorry

/-- **Lemma IV.3.8** (Ch. IV §3.8). Let `M` be a hyperbolic Riemann surface. Let `D` be a domain on `M` with `Cl D`
compact and `δD` regular for the Dirichlet problem. Let `P ∈ D`, `g = g(P, ·)` the Green's function of `M`, and `u` the
harmonic function on `D`, continuous on `Cl D`, with `u(Q) = g(P, Q)` on `δD`. Then `g_D(P, Q) = g(P, Q) − u(Q)`,
`Q ∈ D`, defines the Green's function for `D` with singularity at `P` (on the Riemann surface `D`). -/
theorem lemma4_3_8 (hM : IsHyperbolicSurface M) {D : TopologicalSpace.Opens M} (hDc : IsConnected (D : Set M))
    (hcpt : IsCompact (closure (D : Set M))) (hreg : ∀ P ∈ frontier (D : Set M), IsRegularPoint (D : Set M) P)
    {P : M} (hP : P ∈ D) {g : M → ℝ} (hg : References.IsGreenFunction P g) {u : M → ℝ}
    (hu : ContinuousOn u (closure (D : Set M))) (huh : References.IsHarmonicRS (D : Set M) u)
    (hub : ∀ Q ∈ frontier (D : Set M), u Q = g Q) :
    References.IsGreenFunction (X := D) ⟨P, hP⟩ (fun Q : D => g Q - u Q) := by
  sorry

/-- **Lemma IV.3.9** (Ch. IV §3.9). In addition to the hypotheses of Lemma IV.3.8, assume that `δD` consists of closed
analytic curves, and `P, Q ∈ D`. Then `g_D(P, Q) = g_D(Q, P)`, for the Green's functions of the surface `D` with
singularities at `P` and at `Q` (`P ≠ Q`; the value at the singularity is not defined). -/
theorem lemma4_3_9 (hM : IsHyperbolicSurface M) {D : TopologicalSpace.Opens M} (hDc : IsConnected (D : Set M))
    (hcpt : IsCompact (closure (D : Set M))) (hreg : ∀ P ∈ frontier (D : Set M), IsRegularPoint (D : Set M) P)
    (han : HasAnalyticBoundary (D : Set M)) {P Q : D} (hPQ : P ≠ Q) {gP gQ : D → ℝ}
    (hgP : References.IsGreenFunction (X := D) P gP) (hgQ : References.IsGreenFunction (X := D) Q gQ) :
    gP Q = gQ P := by
  sorry

/-- **Theorem IV.3.10** (Ch. IV §3.10). If `M` is hyperbolic, then the Green's function is symmetric:
`g(P, Q) = g(Q, P)` for all `P ≠ Q` in `M`. -/
theorem thm4_3_10 (hM : IsHyperbolicSurface M) {P Q : M} (hPQ : P ≠ Q) {gP gQ : M → ℝ}
    (hgP : References.IsGreenFunction P gP) (hgQ : References.IsGreenFunction Q gQ) : gP Q = gQ P := by
  sorry

/-- **Theorem IV.3.11** (Ch. IV §3.11). Let `M` be a non-hyperbolic Riemann surface. Let `D` be a domain on `M` with
`P ∈ D`. Let `f` be a holomorphic function on `D ∖ {P}`. Then there exists a unique harmonic function `u` on `M ∖ {P}` such
that (3.11.1) `u − Re f` is harmonic in `D` and vanishes at `P`, and (3.11.2) `u` is bounded outside every neighbourhood
of `P`. Modelling: `u − Re f` harmonic in `D` and vanishing at `P` is the existence of a harmonic `h` on `D` with
`h(P) = 0` and `h = u − Re f` on `D ∖ {P}`; uniqueness is for the values on `M ∖ {P}` (the value `u(P)` is not part of
`u`). -/
theorem thm4_3_11 (hM : ¬ IsHyperbolicSurface M) {D : Set M} (hD : IsOpen D) (hDc : IsConnected D) {P : M} (hP : P ∈ D)
    {f : M → ℂ} (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f (D \ {P})) :
    ∃ u : M → ℝ, (References.IsHarmonicRS {P}ᶜ u ∧ (∃ h : M → ℝ, References.IsHarmonicRS D h ∧ h P = 0 ∧
        ∀ x ∈ D, x ≠ P → h x = u x - (f x).re) ∧ ∀ N ∈ 𝓝 P, ∃ B : ℝ, ∀ x ∈ Nᶜ, |u x| ≤ B) ∧
      ∀ u' : M → ℝ, (References.IsHarmonicRS {P}ᶜ u' ∧ (∃ h : M → ℝ, References.IsHarmonicRS D h ∧ h P = 0 ∧
        ∀ x ∈ D, x ≠ P → h x = u' x - (f x).re) ∧ ∀ N ∈ 𝓝 P, ∃ B : ℝ, ∀ x ∈ Nᶜ, |u' x| ≤ B) →
        ∀ x, x ≠ P → u' x = u x := by
  sorry

/-- **Lemma IV.3.12** (Ch. IV §3.12). Let `D ⊂ ℂ`, `u` harmonic in `D` and `|u| ≤ m`. Let `P ∈ D`. Then
`‖(grad u)_P‖ ≤ c m / |P − δD|` with `c` a universal constant, where `grad u = (u_x, u_y)` and its norm is
`max {|u_x|, |u_y|}`. Modelling: stated as `‖grad u (P)‖ · dist(P, ℂ ∖ D) ≤ c m` (`dist(P, ℂ ∖ D) = |P − δD|` for
`P ∈ D`; the product form has no division by `0` for `D = ℂ`). -/
theorem lemma4_3_12 :
    ∃ c : ℝ, ∀ (D : Set ℂ) (u : ℂ → ℝ) (m : ℝ) (P : ℂ), IsOpen D → InnerProductSpace.HarmonicOnNhd u D →
      (∀ z ∈ D, |u z| ≤ m) → P ∈ D →
      max |fderiv ℝ u P 1| |fderiv ℝ u P Complex.I| * Metric.infDist P Dᶜ ≤ c * m := by
  sorry

/-- **Lemma IV.3.13** (Ch. IV §3.13). Let `{u_j}` be a sequence of harmonic functions on a domain `D ⊂ ℂ`. If `{u_j}`
converges uniformly on compact subsets to a function `u`, then `u` is harmonic and `{u_{j,x}}` converges uniformly on
compact subsets to `u_x`. -/
theorem lemma4_3_13 {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {u : ℕ → ℂ → ℝ} {v : ℂ → ℝ}
    (hu : ∀ j, InnerProductSpace.HarmonicOnNhd (u j) D) (hconv : TendstoLocallyUniformlyOn u v atTop D) :
    InnerProductSpace.HarmonicOnNhd v D ∧
      TendstoLocallyUniformlyOn (fun j z => fderiv ℝ (u j) z 1) (fun z => fderiv ℝ v z 1) atTop D := by
  sorry

/-- **Lemma IV.3.14** (Ch. IV §3.14). Let `{u_j}` be a uniformly bounded sequence of harmonic functions on a Riemann
surface `M`. Then there exists a subsequence converging uniformly on compact subsets of `M`. -/
theorem lemma4_3_14 {u : ℕ → M → ℝ} (hu : ∀ j, References.IsHarmonicRS univ (u j))
    (hb : ∃ B : ℝ, ∀ j x, |u j x| ≤ B) :
    ∃ (φ : ℕ → ℕ) (v : M → ℝ), StrictMono φ ∧ TendstoLocallyUniformly (fun j => u (φ j)) v atTop := by
  sorry

/-- **The flux `∫ *du` over a circle** (Ch. IV §3.15, helper). For a function `g` of the plane, differentiable within
`S`, the integral of the conjugate differential `*dg` over the circle `|z| = r` (counterclockwise):
`∫₀^{2π} (∂g/∂r) r dθ`. -/
def circleFlux (g : ℂ → ℝ) (S : Set ℂ) (r : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * π, fderivWithin ℝ g S (r * Complex.exp (θ * Complex.I)) (r * Complex.exp (θ * Complex.I))

/-- **Lemma IV.3.15** (Ch. IV §3.15). Let `M` be a non-hyperbolic Riemann surface and `K` a conformal disc (in the
coordinate `z`, `K = {|z| < ρ}`). Let `u` be a bounded harmonic function on `M ∖ K`, `C¹` on `Cl(M ∖ K)`. Then
`∫_{δK} *du = 0`.
Modelling: `u` is harmonic on `M ∖ Cl K`; `C¹` up to `δK` is `ContDiffOn ℝ 1` of `u ∘ e⁻¹` on `{ρ ≤ |z| ≤ ρ'}` for some
`ρ' > ρ` inside the chart image; the flux is `circleFlux` within that closed annulus. -/
theorem lemma4_3_15 (hM : ¬ IsHyperbolicSurface M) {e : OpenPartialHomeomorph M ℂ}
    (he : e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas M) {ρ ρ' : ℝ} (hρ : 1 < ρ) (hρρ' : ρ < ρ')
    (hcl : closedBall (0 : ℂ) ρ' ⊆ e.target) {K : Set M} (hK : K = e.symm '' ball 0 ρ) {u : M → ℝ}
    (hh : References.IsHarmonicRS (closure K)ᶜ u) (hb : ∃ B : ℝ, ∀ x ∈ Kᶜ, |u x| ≤ B)
    (hC1 : ContDiffOn ℝ 1 (fun w => u (e.symm w)) (closedBall 0 ρ' \ ball 0 ρ)) :
    circleFlux (fun w => u (e.symm w)) (closedBall 0 ρ' \ ball 0 ρ) ρ = 0 := by
  sorry

/-- **Theorem IV.3.17** (Ch. IV §3.17). Every Riemann surface `M` carries non-constant meromorphic functions.
Modelling: a meromorphic function is a holomorphic map `M → ℂ̂`; non-constant. -/
theorem thm4_3_17 : ∃ f : M → References.RiemannSphere, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ ¬ ∃ c, ∀ x, f x = c := by
  sorry

/-- **Corollary IV.3.18, part 2** (Ch. IV §3.18, Corollary 2). Every Riemann surface is metrizable. -/
theorem cor4_3_18_b : TopologicalSpace.MetrizableSpace M := by
  sorry

end FarkasKra1992
