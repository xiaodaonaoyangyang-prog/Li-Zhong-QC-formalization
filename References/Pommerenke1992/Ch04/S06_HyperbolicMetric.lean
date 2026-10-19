import References.Pommerenke1992.Ch04.S05_LengthDistortion
import References.Gehring1978.S1_Introduction

/-!
# Pommerenke 1992, Ch. 4 §4.6 The Hyperbolic Metric

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §4.6; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 3830–3947.

* Definition (the hyperbolic metric `λ_G` of a simply connected domain `G ⊊ ℂ`, (4.6.1)) — `hypDistG`
* Unlabelled (§4.6, l. 3838: the definition does not depend on the choice of `f`, by (1.2.7)) — `hypDistG_eq`
* Definition (hyperbolic geodesic: the image of a non-euclidean segment, resp. line, §4.6) — `IsHypGeodesicSegment`,
  `IsHypGeodesicLine`
* Formula (4.6.2) (cited "(2)" in §4.6: `λ_G` is the minimal hyperbolic length of curves, attained for the hyperbolic
  geodesic) — `eq4_6_2`
* Proposition 4.22 (Jørgensen) — `prop4_22`
* Definition (the quasihyperbolic metric `λ*_G`, (4.6.4)) — `quasihypDist`
* Formula (4.6.5) (cited "(5)" in §4.6) — `eq4_6_5`
* Formula (4.6.6) (cited "(6)" in §4.6) — `eq4_6_6`
* Definition (Hölder domain, §4.6) — `IsHolderDomain`
* Formula (4.6.10) (quoted from Smith–Stegenga; cited "compare (4.6.10)" at l. 4241) — `eq4_6_10`

Not items (DESIGN §3): the remarks on multiply connected domains; (4.6.3) (a consequence of Theorem 4.20, not cited);
"for non-convex domains there is not always a shortest curve" (a remark); the Hardy–Littlewood characterization
(4.6.7) (quoted from Duren, not cited) and the characterization of Hölder domains (4.6.8), (4.6.9) derived from it
(BePo82; not cited; (4.6.9) is printed `O(1/dist(w, ∂G))`, while the derivation from (4.6.8) and (4.6.6) gives
`O(log 1/dist(w, ∂G))` [misprint?], image checked in the leader's audit); "the power series converges absolutely on
`𝕋`" (immediate from (4.6.10)); that the minimum in (4.6.4) is attained (not cited; `quasihypDist` is the infimum,
which is the same value); the monotonicity remarks on `λ_G` (l. 3840); "for general bounded domains (4.6.10) holds
only for `δ = 0`" (l. 3935, Pir62).

**Conventions.** `G ⊊ ℂ` is a simply connected domain and `f` a conformal map of `𝔻` onto `G`
(`LiZhongQC.IsConformalOnto f unitDisc G`). The hyperbolic density of `G` is `Gehring1978.hypDensity (toExt G)`, in the
same normalization as `λ` (curvature `-4`). Curve lengths for a density are the project's `LRCurve.rhoLength`, and the
distances are the project's `LiZhongQC.metricDist` (infimum over rectifiable curves), as for `hypDistD` in §1.2.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto IsPathIn metricDist LRCurve)

/-- **Definition (4.6.1)** (§4.6; the first display of §4.6, untagged in the OCR). The hyperbolic metric (Poincaré
metric) of `G`: `λ_G(w₁, w₂) = λ_𝔻(z₁, z₂)` for
`w_j = f(z_j)`, `z_j ∈ 𝔻`, where `f` maps `𝔻` onto `G`.
Modelling: the value does not depend on `f` (`hypDistG_eq`), so it is written as the supremum of the set of the values
for all `f` and all preimages, a single point (the pattern of `Gehring1978.hypDensity`; `0` outside the domain of
discourse). -/
def hypDistG (G : Set ℂ) (w₁ w₂ : ℂ) : ℝ :=
  sSup {r : ℝ | ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc G ∧
    ∃ z₁ ∈ unitDisc, ∃ z₂ ∈ unitDisc, f z₁ = w₁ ∧ f z₂ = w₂ ∧ r = hypDistD z₁ z₂}

/-- **Unlabelled claim** (§4.6, l. 3838; the definition rests on it). By (1.2.7) the definition of `λ_G` is independent
of the choice of the function `f` mapping `𝔻` onto `G`: `λ_G(f(z₁), f(z₂)) = λ(z₁, z₂)` for every such `f`. -/
theorem hypDistG_eq {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc)
    (h₂ : z₂ ∈ unitDisc) : hypDistG G (f z₁) (f z₂) = hypDistD z₁ z₂ := by
  sorry

/-- **Definition** (§4.6). `S` is the hyperbolic geodesic of `G` from `w₁` to `w₂`: the image of the non-euclidean
segment from `z₁` to `z₂` under a conformal map `f` of `𝔻` onto `G` with `f(z_j) = w_j`. -/
def IsHypGeodesicSegment (G S : Set ℂ) (w₁ w₂ : ℂ) : Prop :=
  ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc G ∧ ∃ z₁ ∈ unitDisc, ∃ z₂ ∈ unitDisc, f z₁ = w₁ ∧ f z₂ = w₂ ∧
    S = f '' nonEuclideanSegment z₁ z₂

/-- **Definition** (§4.6, Proposition 4.22). `S` is a (complete) hyperbolic geodesic of `G`: the image of a
non-euclidean line of `𝔻`; after composing `f` with a conformal self-map of `𝔻`, the image of the diameter
`(-1, 1)`. -/
def IsHypGeodesicLine (G S : Set ℂ) : Prop :=
  ∃ f : ℂ → ℂ, IsConformalOnto f unitDisc G ∧ S = f '' {z | z ∈ unitDisc ∧ z.im = 0}

/-- **Formula (4.6.2)** (§4.6; cited "(2)" in §4.6). It follows from (1.2.5) that
`λ_G(w₁, w₂) = min_C λ_G(C)`, `λ_G(C) = ∫_{f⁻¹(C)} |dz|/(1 - |z|²)`, where the minimum is taken over all curves `C`
in `G` from `w₁` to `w₂`; it is attained for the hyperbolic geodesic from `w₁` to `w₂`.
Modelling: `λ_G(C) = ∫_C ϱ_G(w)|dw|` with the hyperbolic density `ϱ_G = Gehring1978.hypDensity (toExt G)` (the
image of `|dz|/(1 - |z|²)`); the minimum is the infimum `LiZhongQC.metricDist`, attained on a curve whose trace is
the geodesic. -/
theorem eq4_6_2 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {z₁ z₂ : ℂ} (h₁ : z₁ ∈ unitDisc)
    (h₂ : z₂ ∈ unitDisc) :
    ENNReal.ofReal (hypDistG G (f z₁) (f z₂)) =
        metricDist G (fun w => ENNReal.ofReal (Gehring1978.hypDensity (toExt G) w)) (f z₁) (f z₂) ∧
      ∃ γ : LRCurve, IsPathIn G (f z₁) (f z₂) γ ∧ γ.closedTrace = f '' nonEuclideanSegment z₁ z₂ ∧
        γ.rhoLength (fun w => ENNReal.ofReal (Gehring1978.hypDensity (toExt G) w)) =
          ENNReal.ofReal (hypDistG G (f z₁) (f z₂)) := by
  sorry

/-- **Proposition 4.22** (§4.6; Jørgensen). Let `D ⊆ G` be a disk and `S` a hyperbolic geodesic of `G`. If `∂D` is
tangential to `S`, then `D ∩ S = ∅`.
Modelling: `D = D(c, ρ)`; `S = f((-1, 1))` for a conformal map `f` of `𝔻` onto `G` (`IsHypGeodesicLine`); "`∂D` is
tangential to `S`" means that `∂D` and `S` meet at a point `w₀ = f(x₀)` where the tangent `f'(x₀)` of `S` is
orthogonal to the radius `w₀ - c`. -/
theorem prop4_22 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hD : ball c ρ ⊆ G) {x₀ : ℝ} (hx₀ : |x₀| < 1) (htouch : f x₀ ∈ sphere c ρ)
    (htan : (conj (deriv f x₀) * (f x₀ - c)).re = 0) :
    Disjoint (ball c ρ) (f '' {z | z ∈ unitDisc ∧ z.im = 0}) := by
  sorry

/-- **Definition (4.6.4)** (§4.6). The quasihyperbolic metric `λ*_G(w₁, w₂) = min_C ∫_C |dw|/dist(w, ∂G)`, the
minimum over all curves `C ⊆ G` from `w₁` to `w₂`.
Modelling: the infimum `LiZhongQC.metricDist` for the density `1/dist(w, ∂G)`, finite for `w₁, w₂ ∈ G`; the book's
minimum is attained, which is not part of the definition here. -/
def quasihypDist (G : Set ℂ) (w₁ w₂ : ℂ) : ℝ :=
  (metricDist G (fun w => ENNReal.ofReal (1 / infDist w (frontier G))) w₁ w₂).toReal

/-- **Formula (4.6.5)** (§4.6; cited "(5)" in §4.6). It follows from (4.5.2) that
`1/(1 - |z|²) ≤ |f'(z)|/dist(f(z), ∂G) ≤ 4/(1 - |z|²)` for `z ∈ 𝔻`. -/
theorem eq4_6_5 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {z : ℂ} (hz : z ∈ unitDisc) :
    1 / (1 - ‖z‖ ^ 2) ≤ ‖deriv f z‖ / infDist (f z) (frontier G) ∧
      ‖deriv f z‖ / infDist (f z) (frontier G) ≤ 4 / (1 - ‖z‖ ^ 2) := by
  sorry

/-- **Formula (4.6.6)** (§4.6; cited "(6)" in §4.6). `λ_G(w₁, w₂) ≤ λ*_G(w₁, w₂) ≤ 4 λ_G(w₁, w₂)` for `w₁, w₂ ∈ G`.
Modelling: `G ⊊ ℂ` simply connected, given as the image of a conformal map of `𝔻`. -/
theorem eq4_6_6 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsConformalOnto f unitDisc G) {w₁ w₂ : ℂ} (h₁ : w₁ ∈ G)
    (h₂ : w₂ ∈ G) : hypDistG G w₁ w₂ ≤ quasihypDist G w₁ w₂ ∧ quasihypDist G w₁ w₂ ≤ 4 * hypDistG G w₁ w₂ := by
  sorry

/-- **Definition** (§4.6; BePo82). `G = f(𝔻)` is a Hölder domain: `f` is Hölder continuous in `𝔻̄` for some exponent
`α` with `0 < α ≤ 1` ((3.3.9)).
Modelling: `f` has a continuous extension `F` to `𝔻̄` that is Hölder continuous there; this does not depend on `f`. -/
def IsHolderDomain (G : Set ℂ) : Prop :=
  ∃ f F : ℂ → ℂ, IsConformalOnto f unitDisc G ∧ ContinuousOn F (closedBall 0 1) ∧ EqOn F f unitDisc ∧
    ∃ (M α : ℝ≥0), 0 < α ∧ α ≤ 1 ∧ HolderOnWith M α F (closedBall 0 1)

/-- **Formula (4.6.10)** (§4.6, quoted from Smith–Stegenga; cited "compare (4.6.10)" at l. 4241). If `G = f(𝔻)` is a
Hölder domain and `f(z) = Σ_{n≥0} a_n z^n`, then `Σ_{n≥1} n^{1+δ} |a_n|² < ∞` for some `δ > 0`.
Modelling: `a_n = f^{(n)}(0)/n!` (`sCoeff`, §1.3). -/
theorem eq4_6_10 {f : ℂ → ℂ} {G : Set ℂ} (hG : IsHolderDomain G) (hf : IsConformalOnto f unitDisc G) :
    ∃ δ > (0 : ℝ), Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 + δ) * ‖sCoeff f (n + 1)‖ ^ 2) := by
  sorry

end Pommerenke1992
