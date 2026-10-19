import References.FarkasKra1992.Ch02.S02_WeylsLemma
import References.FarkasKra1992.Ch04.S03_Classification
import References.Forster1981.Ch01.S10_TheIntegrationOfDifferentialForms

/-!
# Farkas–Kra, Chapter II §5: Meromorphic functions and differentials

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. II §5 (`full.md` FK1:2158–2293).

Conventions: as in `Ch01/S03_DifferentialForms` (coefficient model of forms, `Forster1981.Form1`). A *local coordinate
vanishing at `P`* is a chart `e` of the maximal analytic atlas with `P ∈ e.source` and `e P = 0`; the coefficient of a
1-form `ω` in the coordinate `e` at `P` is `coeffIn ω P e` (the preferred-chart coefficient transported by the chart change,
`f_e(u) = f_P(τ u) τ′(u)`, `τ = φ_P ∘ e⁻¹`). A meromorphic differential is `Forster1981.IsAbelianDiff3`
(type `(1, 0)`, meromorphic coefficient); `q`-differentials are the coefficient families of `LiZhongQC.IsDiffFamily q 0` with
meromorphic coefficients (`IsMeroQDiff`), their order is `ordQDiff`; the holomorphic ones are `IsHolQDiff` (holomorphic coefficients on the chart images); the residue is `Forster1981.HasResidue`, the order of
an abelian differential is `Forster1981.Form1.orderAt`.

* Definition II.5.1 (meromorphic differential) — exists: `Forster1981.IsAbelianDiff3`
* Theorem II.5.1, part (a) — `coeffIn`, `thm2_5_1_a`
* Theorem II.5.1, part (b) — `thm2_5_1_b`
* Definition II.5.2 (`q`-differential, order) — `IsMeroQDiff`, `ordQDiff`
* Definition II.5.2 (holomorphic `q`-differential, the space `ℋ^q(M)` and its dimension) — `IsHolQDiff`, `holQDiffSpan`, `dimHolQ`
* Definition II.5.2 (abelian differential, residue) — exists: `Forster1981.IsAbelianDiff3`, `Forster1981.HasResidue`, `Forster1981.Form1.orderAt`
* Theorem II.5.3 — `thm2_5_3`
* Corollary II.5.3 (non-constant meromorphic functions on every surface) — exists: `FarkasKra1992.thm4_3_17`
* Proposition II.5.4 (residue theorem) — exists: `Forster1981.thm10_21`
* II.5.5 (compact Riemann surfaces are triangulable) — deferred: triangulation not available (W-TOP)

Omitted (U−): II.5.4 Remark (the condition `Σ c_j = 0` is necessary on a compact surface; it is the converse content of
`Forster1981.thm10_21`), the Exercises.
-/

open scoped Manifold ContDiff Topology
open Set Filter Forster1981

noncomputable section

namespace FarkasKra1992

variable {X : Type} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The coefficient of a 1-form in a local coordinate** (Ch. II §5.1, helper). For a chart `e` with `P ∈ e.source`, the
coefficient of `dz` of `ω` in the coordinate `z = e` at the point `P`: `f_e(u) = f_P(τ(u)) τ′(u)`, `τ = φ_P ∘ e⁻¹`. -/
def coeffIn (w : Form1 X) (P : X) (e : OpenPartialHomeomorph X ℂ) (u : ℂ) : ℂ :=
  w.1 P ((chartAt ℂ P) (e.symm u)) * deriv (fun v => (chartAt ℂ P) (e.symm v)) u

/-- **Theorem II.5.1(a)** (Ch. II §5.1). Let `P ∈ M` and let `z` be a local coordinate on `M` vanishing at `P`. For every integer
`n ≥ 1`, there exists a meromorphic differential on `M` which is holomorphic on `M ∖ {P}` and with singularity `1/z^{n+1}` at
`P` (the difference with `1/z^{n+1}` is holomorphic near `P` in the coordinate `z`). -/
theorem thm2_5_1_a {P : X} {e : OpenPartialHomeomorph X ℂ} (he : e ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X)
    (hP : P ∈ e.source) (h0 : e P = 0) {n : ℕ} (hn : 1 ≤ n) :
    ∃ w : Form1 X, IsAbelianDiff3 w ∧ w.IsHolomorphicOn {P}ᶜ ∧
      ∃ V ∈ 𝓝 (0 : ℂ), ∃ h : ℂ → ℂ, DifferentiableOn ℂ h V ∧
        ∀ u ∈ V, u ≠ 0 → coeffIn w P e u = 1 / u ^ (n + 1) + h u := by
  sorry

/-- **Theorem II.5.1(b)** (Ch. II §5.1). Given two distinct points `P₁` and `P₂` on `M` and local coordinates `z_j` vanishing at
`P_j`, there exists a meromorphic differential `ω`, holomorphic on `M ∖ {P₁, P₂}`, with singularity `1/z₁` at `P₁` and
singularity `−1/z₂` at `P₂`. -/
theorem thm2_5_1_b {P₁ P₂ : X} (hP : P₁ ≠ P₂) {e₁ e₂ : OpenPartialHomeomorph X ℂ}
    (he₁ : e₁ ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X) (he₂ : e₂ ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas X)
    (h₁ : P₁ ∈ e₁.source) (h₂ : P₂ ∈ e₂.source) (h₁₀ : e₁ P₁ = 0) (h₂₀ : e₂ P₂ = 0) :
    ∃ w : Form1 X, IsAbelianDiff3 w ∧ w.IsHolomorphicOn ({P₁, P₂} : Set X)ᶜ ∧
      (∃ V ∈ 𝓝 (0 : ℂ), ∃ h : ℂ → ℂ, DifferentiableOn ℂ h V ∧
        ∀ u ∈ V, u ≠ 0 → coeffIn w P₁ e₁ u = 1 / u + h u) ∧
      ∃ V ∈ 𝓝 (0 : ℂ), ∃ h : ℂ → ℂ, DifferentiableOn ℂ h V ∧
        ∀ u ∈ V, u ≠ 0 → coeffIn w P₂ e₂ u = -1 / u + h u := by
  sorry

/-- **Meromorphic `q`-differential** (Ch. II §5.2). Let `q` be an integer. A *(meromorphic) `q`-differential* `ω` on `M` is an
assignment of a meromorphic function `f` to each local coordinate `z` so that `f(z) dz^q` is invariantly defined: a family of
coefficients `c x` with the transformation law of `LiZhongQC.IsDiffFamily q 0` and meromorphic at every point of the chart
image. For `q = 1` these are the abelian differentials.
**Warning:** this constrains the coefficient only at the centre of each chart (`MeromorphicAt` at `chartAt ℂ x x`), not on the chart
image; use it only for existence statements and orders, never for spans or dimensions (use `IsHolQDiff`, `holQDiffSpan`). -/
def IsMeroQDiff (q : ℤ) (c : X → ℂ → ℂ) : Prop :=
  LiZhongQC.IsDiffFamily q 0 c ∧ ∀ x, MeromorphicAt (c x) (chartAt ℂ x x)

/-- **Order of a `q`-differential at a point** (Ch. II §5.2). `ord_P ω = ord_0 f` for the coefficient `f` in a coordinate
vanishing at `P` (well defined; computed in the preferred chart at `P`). -/
noncomputable def ordQDiff (c : X → ℂ → ℂ) (P : X) : WithTop ℤ := meromorphicOrderAt (c P) (chartAt ℂ P P)

/-- **Holomorphic `q`-differential** (Ch. II §5.2, III.2). A `q`-differential (`LiZhongQC.IsDiffFamily q 0`: the coefficient `c x`
vanishes off the chart image and the transformation law holds) whose coefficient is holomorphic on the chart image
`(chartAt ℂ x).target` at every `x`. For `q = 1` these are the holomorphic abelian differentials. -/
def IsHolQDiff (q : ℤ) (c : X → ℂ → ℂ) : Prop :=
  LiZhongQC.IsDiffFamily q 0 c ∧ ∀ x, DifferentiableOn ℂ (c x) (chartAt ℂ x).target

/-- **The space `ℋ^q(M)` of holomorphic `q`-differentials** (Ch. III §2.5, III.5). Modelling: the span of the holomorphic
`q`-differentials in the vector space of coefficient families (the set itself is a subspace). -/
def holQDiffSpan (X : Type) [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (q : ℤ) : Submodule ℂ (X → ℂ → ℂ) := Submodule.span ℂ {c | IsHolQDiff q c}

/-- **The dimension `dim ℋ^q(M)`** (Ch. III §5). `Module.finrank` of `holQDiffSpan` (finite on a compact surface). -/
def dimHolQ (X : Type) [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (q : ℤ) : ℕ := Module.finrank ℂ (holQDiffSpan X q)

/-- **Theorem II.5.3** (Ch. II §5.3). Let `P₁, …, P_k` be `k > 1` distinct points on a Riemann surface `M`. Let `c₁, …, c_k` be
complex numbers with `Σ c_j = 0`. Then there exists a meromorphic abelian differential `ω` on `M`, holomorphic on
`M ∖ {P₁, …, P_k}`, with `ord_{P_j} ω = −1` and `res_{P_j} ω = c_j`.
Modelling: a simple pole with residue `0` is impossible, so `ord_{P_j} ω = −1` is asserted for the `c_j ≠ 0` (implicit in
the book); for `c_j = 0` the differential is holomorphic at `P_j` (`ord_{P_j} ω ≥ 0`) with residue `0`.
[CORRECTION, FK-fix2] The holomorphy at `P_j` for `c_j = 0` is now part of the statement (AUDIT5_FK F6). -/
theorem thm2_5_3 {k : ℕ} (hk : 1 < k) {P : Fin k → X} (hP : Function.Injective P) {c : Fin k → ℂ}
    (hc : ∑ j, c j = 0) :
    ∃ w : Form1 X, IsAbelianDiff3 w ∧ w.IsHolomorphicOn (Set.range P)ᶜ ∧
      ∀ j, (c j ≠ 0 → w.orderAt (P j) = ((-1 : ℤ) : WithTop ℤ)) ∧
        (c j = 0 → (0 : WithTop ℤ) ≤ w.orderAt (P j)) ∧ HasResidue w (P j) (c j) := by
  sorry

end FarkasKra1992
