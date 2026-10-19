import References.Common.HyperbolicSurface
import References.GardinerLakic2000.Ch02.S05_ConstantCurvature

/-!
# Hubbard 2006, Chapter 2 §2.1: The hyperbolic metric of the plane (new items)

Source: Hubbard, *Teichmüller Theory*, Vol. 1, `H1` lines 916–1150.

**Conventions.** The unit disc is `LiZhongQC.unitDisc` with the density `ρ_𝔻(z) = 2 / (1 − |z|²)`, i.e.
`LiZhongQC.poincareDensityDisc` (curvature `−1`; Hubbard's normalization). The upper half plane has `ρ_ℍ = 1 / Im z`.
Automorphisms of `ℍ` are the elements of `SL(2, ℝ)` acting by Möbius maps (`g` and `−g` are the same automorphism).

* Prop. 2.1.2 (automorphisms of `𝔻` are the Blaschke maps; the metric is invariant) — exists:
  `LiZhongQC.poincareDensityDisc_rotBlaschke`, `LiZhongQC.exists_rotation_blaschke_of_isConformalOnto_unitDisc`
* Prop. 2.1.6 (1) (Schwarz–Pick: analytic self-maps of `𝔻` are weakly contracting) — exists:
  `LiZhongQC.schwarz_pick_unitDisc`
* Prop. 2.1.6 (2) (a self-map of `𝔻` that is an isometry at one point is an automorphism) — `prop2_1_6_b`
* Prop. 2.1.7 (geodesics of `ℍ`: the arc between two points) — `hypArc`, `prop2_1_7_a`, `prop2_1_7_b`
* Prop. 2.1.12 (`𝔻` has constant curvature `−1`) — `prop2_1_12`
* Prop. 2.1.14 (1) (elliptic automorphisms are conjugate to rotations) — `prop2_1_14_a`
* Prop. 2.1.14 (2) (parabolic automorphisms: normal forms `z ↦ z ± 1`, and these are not conjugate) —
  `prop2_1_14_b`, `prop2_1_14_b'`
* Prop. 2.1.14 (3) (hyperbolic automorphisms are conjugate to a dilation; the minimal displacement is realized) —
  `prop2_1_14_c`
* Exercises 2.1.3–2.1.5, 2.1.9–2.1.11, 2.1.13, 2.1.15 — omitted: exercise
-/

open Set Metric
open scoped Real

namespace Hubbard2006

open LiZhongQC References

/-- **Hyperbolic arc of `ℍ` between `a` and `b`** (Prop. 2.1.7, H1:1037): the arc of the vertical line or of the
semicircle centred on `ℝ` through `a` and `b`, between them. If `Re a = Re b` it is the vertical segment;
otherwise it is
the part of the circle `|z − c| = |a − c|` (centred at the real `c` with `|a − c| = |b − c|`) with real part between
`Re a` and `Re b`. -/
def hypArc (a b : ℂ) : Set ℂ :=
  {z | 0 < z.im ∧
    ((a.re = b.re ∧ z.re = a.re ∧ z.im ∈ uIcc a.im b.im) ∨
      ∃ c : ℝ, ‖a - c‖ = ‖b - c‖ ∧ ‖z - c‖ = ‖a - c‖ ∧ z.re ∈ uIcc a.re b.re)}

/-- **Proposition 2.1.6 (2)** (Schwarz–Pick theorem, H1:1021). If an analytic self-map `f` of the unit disc is an
isometry at a single point `z` (`ρ_𝔻(f z) |f′(z)| = ρ_𝔻(z)`), it is an automorphism: a bijection of `𝔻` with analytic
inverse. -/
theorem prop2_1_6_b {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hmaps : MapsTo f unitDisc unitDisc)
    {z : ℂ} (hz : z ∈ unitDisc) (hiso : poincareDensityDisc (f z) * ‖deriv f z‖ = poincareDensityDisc z) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g unitDisc ∧ MapsTo g unitDisc unitDisc ∧
      LeftInvOn g f unitDisc ∧ RightInvOn g f unitDisc := by
  sorry

/-- **Proposition 2.1.7 (a)** (Geodesics in `ℍ`, H1:1037). For two points `a`, `b` of the upper half plane with
`Re a ≠ Re b` there is exactly one centre `c ∈ ℝ` with `|a − c| = |b − c|`: a unique semicircle perpendicular to `ℝ`
passes through `a` and `b`. (If `Re a = Re b` the vertical line plays this role.) -/
theorem prop2_1_7_a {a b : ℂ} (ha : a ∈ upperHalf) (hb : b ∈ upperHalf) (hre : a.re ≠ b.re) :
    ∃! c : ℝ, ‖a - c‖ = ‖b - c‖ := by
  sorry

/-- **Proposition 2.1.7 (b)** (Geodesics in `ℍ`, H1:1037). A shortest curve from `a` to `b` in `ℍ` for the metric
`|dz| / Im z` traces exactly the hyperbolic arc `hypArc a b`: every rectifiable curve `γ ⊂ ℍ` from `a` to `b` whose
`ρ_ℍ`-length equals the distance (the infimum of lengths, `LiZhongQC.metricDist`) has image `hypArc a b`. Existence of
such a curve is `LiZhongQC.upperHalf_geodesic`. -/
theorem prop2_1_7_b {a b : ℂ} (ha : a ∈ upperHalf) (hb : b ∈ upperHalf) (γ : LRCurve)
    (hγ : IsPathIn upperHalf a b γ)
    (hlen : γ.rhoLength (fun z => ENNReal.ofReal (1 / z.im)) =
      metricDist upperHalf (fun z => ENNReal.ofReal (1 / z.im)) a b) :
    γ.toFun '' Icc 0 1 = hypArc a b := by
  sorry

/-- **Proposition 2.1.12** (H1:1092). With the hyperbolic metric `ρ_𝔻 = 2 / (1 − |z|²)` the unit disc has constant
curvature `−1` (curvature `κ(ρ) = −ρ⁻² Δ log ρ` of `GardinerLakic2000.gaussCurvature`; GL's `prop2_2_b` is the
normalization `1 / (1 − |z|²)` with curvature `−4`). -/
theorem prop2_1_12 {z : ℂ} (hz : z ∈ unitDisc) :
    GardinerLakic2000.gaussCurvature poincareDensityDisc z = -1 := by
  sorry

/-- **Proposition 2.1.14 (1)** (Normal forms for automorphisms, H1:1126). An elliptic automorphism `g` of `ℍ`
(`|tr g| < 2`) is conjugate to a rotation about `i`:
`h g h⁻¹ = [[cos θ, sin θ], [−sin θ, cos θ]]` for some `h ∈ SL(2, ℝ)`
and `θ ∈ ℝ` (the rotation of `𝔻` by the angle `2θ` after the Cayley map; replacing `θ` by `θ + π` gives `−g`). -/
theorem prop2_1_14_a {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg : |slTrace g| < 2) :
    ∃ (h : Matrix.SpecialLinearGroup (Fin 2) ℝ) (θ : ℝ),
      ((h * g * h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
  sorry

/-- **Proposition 2.1.14 (2)** (H1:1126). A parabolic automorphism is conjugate in `ℍ` to `z ↦ z + 1` or to `z ↦ z − 1`
(up to the sign `±` of the matrix, which acts in the same way). -/
theorem prop2_1_14_b {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg : IsParabolic g) :
    ∃ (h : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧
      (((h * g * h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, ε; 0, 1] ∨
        ((h * g * h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = -!![1, ε; 0, 1]) := by
  sorry

/-- **Proposition 2.1.14 (2), second half** (H1:1126). The maps `z ↦ z + 1` and `z ↦ z − 1` are not conjugate in the
automorphism group of `ℍ`: no `h ∈ SL(2, ℝ)` conjugates `[[1, 1], [0, 1]]` to `±[[1, −1], [0, 1]]`. -/
theorem prop2_1_14_b' (h : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ((h : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 0, 1] * ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) ≠ !![1, -1; 0, 1]) ∧
    ((h : Matrix (Fin 2) (Fin 2) ℝ) * !![1, 1; 0, 1] * ((h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) ≠ -!![1, -1; 0, 1]) := by
  sorry

/-- **Proposition 2.1.14 (3)** (H1:1126). A hyperbolic automorphism `g` of `ℍ` is conjugate to the dilation
`z ↦ e^t z`, `t = ` its translation length (the translation `z ↦ z + D(α)` of the band model), and the minimal
displacement `inf_z d(z, g z)` is realized (`axisH g` is nonempty). -/
theorem prop2_1_14_c {g : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg : IsHyperbolic g) :
    (∃ (h : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ), 0 < t ∧ translationLength g = t ∧
      (((h * g * h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          !![Real.exp (t / 2), 0; 0, Real.exp (-t / 2)] ∨
        ((h * g * h⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          -!![Real.exp (t / 2), 0; 0, Real.exp (-t / 2)])) ∧
    (axisH g).Nonempty := by
  sorry

end Hubbard2006
