import References.FarkasKra1992.Ch04.S07_TwoProblemsOnModuli
import LiZhongQC.Ch03.S14_PoincareMetric

/-!
# Farkas–Kra, Chapter IV §8: Riemannian metrics

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. IV §8 (`full.md` FK2:1291–1651).

Conventions: the metrics `λ(z)|dz|` of the three simply connected surfaces are given by their densities (IV.8.1). The
hyperbolic density of the unit disc, `2/(1 − |z|²)`, is the project's `LiZhongQC.poincareDensityDisc` (FK's normalization,
curvature `−1`; Gehring's `Gehring1978.hypDensity` is half of it), that of the upper half plane `1/Im z` is
`LiZhongQC.poincareDensity upperHalf`. The distance `d` (IV(8.4.2)), the infimum of lengths of rectifiable curves, is
`LiZhongQC.poincareDist unitDisc`, with the lengths of `LiZhongQC.LRCurve.rhoLength`. The non-Euclidean area is
`hyperbolicAreaDisc`.

* IV.8.1 (the metric of `ℂ ∪ {∞}`, `2/(1 + |z|²)`) — `sphericalDensityFK`
* IV.8.1 (the Euclidean metric of `ℂ`, density `1`) — omitted: U−, trivial
* IV.8.1 (the metric of `Δ`, density `2/(1 − |z|²)`, IV.8.4) — exists: `LiZhongQC.poincareDensityDisc`
* IV.8.4 (the metric of `U`, density `1/Im z`) — exists: `LiZhongQC.poincareDensity`
* IV.8.4 (the distance function on `Δ`, (8.4.2)) — exists: `LiZhongQC.poincareDist`
* Proposition IV.8.2 — `prop4_8_2`
* Proposition IV.8.4, part (a) — `prop4_8_4_a`
* Proposition IV.8.4, part (b) — `prop4_8_4_b`
* Proposition IV.8.4, part (c) — `prop4_8_4_c`
* Proposition IV.8.4, part (d) — `prop4_8_4_d`
* IV.8.5 (non-Euclidean area) — `hyperbolicAreaDisc`

Deferred: IV.8.5 Proposition (the area of a non-Euclidean triangle with angles `α, β, γ` is `π − (α + β + γ)`: hyperbolic
triangles and angles are not modelled), IV.8.6 Theorem (a complete Riemannian metric of constant curvature on every Riemann
surface: no Riemannian metric / curvature notion). Omitted (U−): the curvature computations `K = ±1, 0` and
`Area(ℂ ∪ {∞}) = 4π` in IV.8.2–8.4, the Exercise, the Remarks after IV.8.6.
-/

open scoped Manifold ContDiff MatrixGroups Topology References Real ComplexConjugate
open Set Filter

noncomputable section

namespace FarkasKra1992

open LiZhongQC (poincareDist poincareDensityDisc unitDisc IsPathIn LRCurve)

/-- **The spherical density** (Ch. IV §8.1, (8.1.1)). The metric of `ℂ ∪ {∞}` is `λ(z)|dz|`, `λ(z) = 2/(1 + |z|²)`
(the metric of the unit sphere `S²` under stereographic projection). -/
def sphericalDensityFK (z : ℂ) : ℝ := 2 / (1 + ‖z‖ ^ 2)

/-- **Proposition IV.8.2** (Ch. IV §8.2). An element `T ∈ Aut(ℂ ∪ {∞})` is an isometry in the metric
`(2/(1 + |z|²))|dz|` if and only if as a matrix `T = [[a, −c̄], [c, ā]]`, `|a|² + |c|² = 1`.
Modelling: `T ∈ SL(2, ℂ)`; `T` is an isometry when `λ(Tz)|T′(z)| = λ(z)` for all `z ∈ ℂ` with `Tz ≠ ∞`. -/
theorem prop4_8_2 (T : SL(2, ℂ)) :
    (∀ z : ℂ, T 1 0 * z + T 1 1 ≠ 0 →
      sphericalDensityFK ((T 0 0 * z + T 0 1) / (T 1 0 * z + T 1 1)) *
        ‖deriv (fun w : ℂ => (T 0 0 * w + T 0 1) / (T 1 0 * w + T 1 1)) z‖ = sphericalDensityFK z) ↔
      (T 1 1 = conj (T 0 0) ∧ T 0 1 = - conj (T 1 0) ∧ ‖T 0 0‖ ^ 2 + ‖T 1 0‖ ^ 2 = 1) := by
  sorry

/-- **Proposition IV.8.4(a)** (Ch. IV §8.4). The distance induced by the metric `2/(1 − |z|²)|dz|` on `Δ` is complete:
every Cauchy sequence of `Δ` converges to a point of `Δ`. -/
theorem prop4_8_4_a {z : ℕ → ℂ} (hz : ∀ n, z n ∈ unitDisc)
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m ≥ N, ∀ n ≥ N, poincareDist unitDisc (z m) (z n) < ENNReal.ofReal ε) :
    ∃ w ∈ unitDisc, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, poincareDist unitDisc (z n) w < ENNReal.ofReal ε := by
  sorry

/-- **Proposition IV.8.4(b)** (Ch. IV §8.4). The topology induced by this metric is equivalent to the usual topology on
`Δ`: a subset `U ⊆ Δ` is open if and only if it contains a metric ball about each of its points. -/
theorem prop4_8_4_b {U : Set ℂ} (hU : U ⊆ unitDisc) :
    IsOpen U ↔ ∀ z ∈ U, ∃ r : ℝ, 0 < r ∧ {w ∈ unitDisc | poincareDist unitDisc z w < ENNReal.ofReal r} ⊆ U := by
  sorry

/-- **Proposition IV.8.4(c)** (Ch. IV §8.4). The geodesics in the metric are the arcs of circles orthogonal to the unit
circle `{|z| = 1}` (diameters being circles through `∞`): every shortest rectifiable curve in `Δ` between two points lies
on a diameter or on a circle with centre `c` and radius `r` with `|c|² = 1 + r²`. -/
theorem prop4_8_4_c {a b : ℂ} (ha : a ∈ unitDisc) (hb : b ∈ unitDisc) {γ : LRCurve} (hγ : IsPathIn unitDisc a b γ)
    (hlen : γ.rhoLength (fun z => ENNReal.ofReal (poincareDensityDisc z)) = poincareDist unitDisc a b) :
    (∃ θ : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∃ s : ℝ, γ.toFun t = s * Complex.exp (θ * Complex.I)) ∨
      ∃ (c : ℂ) (r : ℝ), 0 < r ∧ ‖c‖ ^ 2 = 1 + r ^ 2 ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖γ.toFun t - c‖ = r := by
  sorry

/-- **Proposition IV.8.4(d)** (Ch. IV §8.4). Given any two points `a, b ∈ Δ`, `a ≠ b`, there is a unique geodesic between
them: a shortest rectifiable curve exists, and any two shortest curves have the same trace. -/
theorem prop4_8_4_d {a b : ℂ} (ha : a ∈ unitDisc) (hb : b ∈ unitDisc) (hab : a ≠ b) :
    (∃ γ : LRCurve, IsPathIn unitDisc a b γ ∧
      γ.rhoLength (fun z => ENNReal.ofReal (poincareDensityDisc z)) = poincareDist unitDisc a b) ∧
    ∀ γ γ' : LRCurve, IsPathIn unitDisc a b γ →
      γ.rhoLength (fun z => ENNReal.ofReal (poincareDensityDisc z)) = poincareDist unitDisc a b →
      IsPathIn unitDisc a b γ' →
      γ'.rhoLength (fun z => ENNReal.ofReal (poincareDensityDisc z)) = poincareDist unitDisc a b →
      γ.closedTrace = γ'.closedTrace := by
  sorry

/-- **Non-Euclidean area** (Ch. IV §8.5). If `D` is any Lebesgue-measurable subset of `Δ`, then
`Area D = ½ ∬_D λ(z)² |dz ∧ dz̄|` (`|dz ∧ dz̄| = 2 dx dy`) defines the non-Euclidean area of `D`, i.e.
`∬_D λ² dx dy` with `λ = 2/(1 − |z|²)`. -/
def hyperbolicAreaDisc (D : Set ℂ) : ENNReal := ∫⁻ z in D, ENNReal.ofReal (poincareDensityDisc z ^ 2)

end FarkasKra1992
