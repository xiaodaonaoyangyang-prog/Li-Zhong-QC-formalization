import LiZhongQC.Lemmas.GeodesicZeroCorner
import LiZhongQC.Lemmas.GeodesicRegularCorners
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- The degree of an actual natural zero chart is the meromorphic order
of the original coefficient, because the chart has a simple zero and its
derivative and the constant multiplier are analytic units. -/
theorem s25ep_natural_chart_order {φ ζ : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} {m : ℕ}
    (hr : 0 < r) (hζ0 : ζ z₀ = 0)
    (hchart : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2) :
    meromorphicOrderAt φ z₀ = (m : ℤ) := by
  have hz := hchart z₀ (mem_closedBall_self hr.le)
  have horder := hz.1.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hζ0 hz.2.1
  let U : ℂ → ℂ := fun z => (((m : ℂ) + 2) / 2) ^ 2 * deriv ζ z ^ 2
  have hU : AnalyticAt ℂ U z₀ := analyticAt_const.mul (hz.1.deriv.pow 2)
  have hm2 : (m : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
  have hU0 : U z₀ ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 (div_ne_zero hm2 (by norm_num))) (pow_ne_zero 2 hz.2.1)
  have he : φ =ᶠ[𝓝 z₀] U * (ζ ^ m) := by
    filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz'
    change φ z = U z * ζ z ^ m
    rw [(hchart z (ball_subset_closedBall hz')).2.2]
    dsimp only [U]
    ring
  rw [meromorphicOrderAt_congr (he.filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_mul_of_ne_zero hU hU0, meromorphicOrderAt_pow hz.1.meromorphicAt,
    hz.1.meromorphicOrderAt_eq, horder]
  simp

/-- Positive speeds and the common conformal derivative cancel in the
physical corner angle. The left tangent is incoming and the right outgoing. -/
theorem s25ep_physical_corner_angle {u v D df dg : ℂ} {k l : ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0) (hD : D ≠ 0) (hk : 0 < k) (hl : 0 < l)
    (hf : df = -((k : ℂ) * (u / D))) (hg : dg = (l : ℂ) * (v / D)) :
    |arg (-df / dg)| = |arg (v / u)| := by
  have he : -df / dg = ((k / l : ℝ) : ℂ) * (u / v) := by
    rw [hf, hg]
    push_cast
    field_simp [hD, hv, Complex.ofReal_ne_zero.2 hl.ne']
    <;> ring
  rw [he, Complex.arg_real_mul _ (div_pos hk hl)]
  have hi : u / v = (v / u)⁻¹ := by rw [inv_div]
  rw [hi, Complex.abs_arg_inv]

/-- A true natural zero chart supplies both the order and the physical
one-sided angle inequalities required for a blunt corner. The natural
direction bound can be the output of ZeroCorner for the actual segment. -/
theorem s25ep_physical_zero_corner {φ ζ : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} {m : ℕ}
    (hr : 0 < r) (hζ0 : ζ z₀ = 0)
    (hchart : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    {u v df dg : ℂ} {k l : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) (hk : 0 < k) (hl : 0 < l)
    (hf : df = -((k : ℂ) * (u / deriv ζ z₀)))
    (hg : dg = (l : ℂ) * (v / deriv ζ z₀))
    (hangle : 2 * Real.pi / ((m : ℝ) + 2) ≤ |arg (v / u)|) :
    meromorphicOrderAt φ z₀ = (m : ℤ) ∧
      2 * Real.pi / ((m : ℝ) + 2) ≤ |arg (-df / dg)| ∧
      2 * Real.pi / ((m : ℝ) + 2) ≤ 2 * Real.pi - |arg (-df / dg)| ∧
      arg (-df / dg) ≠ 0 := by
  have he := s25ep_physical_corner_angle hu hv (hchart z₀ (mem_closedBall_self hr.le)).2.1 hk hl hf hg
  have hb := s25za_both_angles m hangle
  refine ⟨s25ep_natural_chart_order hr hζ0 hchart, ?_, ?_, ?_⟩
  · rw [he]; exact hb.1
  · rw [he]; exact hb.2
  · intro hz
    have hp : 0 < 2 * Real.pi / ((m : ℝ) + 2) := by positivity
    have ha : 2 * Real.pi / ((m : ℝ) + 2) ≤ |arg (-df / dg)| := by rwa [he]
    rw [hz, abs_zero] at ha
    exact (not_le_of_gt hp) ha

/-- An actual minimizing segment through the zero supplies the angle bound
for physical one-sided derivatives of any regular representatives following
its two oriented radial chart arms. The scalar time changes need only be
monotone. This conclusion uses the exact derivWithin terms of chain sides. -/
theorem s25ep_actual_zero_corner {φ ζ : ℂ → ℂ} {z₀ : ℂ} {r R : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hr : 0 < r) (hζ0 : ζ z₀ = 0)
    (hchart : ∀ z ∈ closedBall z₀ r, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    {D W : Set ℂ} (hW : IsOpen W) (hWD : W ⊆ D) (hWr : W ⊆ closedBall z₀ r)
    (hζ : IsConformalOnto ζ W (ball (0 : ℂ) R))
    (γ : LRCurve) {K : ℝ≥0} {s t₀ t : ℝ} (hs : s ≤ t₀) (ht : t₀ ≤ t)
    (hK : LipschitzOnWith K γ.toFun (Icc s t)) (hmap : MapsTo γ.toFun (Icc s t) W)
    (hzero : γ.toFun t₀ = z₀)
    {u v : ℂ} {ρ τ : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) (hρ : 0 < ρ) (hτ : 0 < τ)
    (hleft : ζ (γ.toFun s) = (ρ : ℂ) * u) (hright : ζ (γ.toFun t) = (τ : ℂ) * v)
    (hmin : phiSegmentLength φ γ s t = metricDist D (phiDensity φ) (γ.toFun s) (γ.toFun t))
    {f g : ℝ → ℂ} {α β : ℝ → ℝ} {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hfb : f b = z₀) (hgc : g c = z₀)
    (hfd : DifferentiableWithinAt ℝ f (Icc a b) b)
    (hgd : DifferentiableWithinAt ℝ g (Icc c d) c)
    (hfn : derivWithin f (Icc a b) b ≠ 0) (hgn : derivWithin g (Icc c d) c ≠ 0)
    (hα : MonotoneOn α (Icc a b)) (hβ : MonotoneOn β (Icc c d))
    {qf qg : ℂ}
    (hfline : ∀ x ∈ Icc a b, ζ (f x) = qf + (α x : ℂ) * (-u))
    (hgline : ∀ x ∈ Icc c d, ζ (g x) = qg + (β x : ℂ) * v) :
    meromorphicOrderAt φ z₀ = (m : ℤ) ∧
      2 * Real.pi / ((m : ℝ) + 2) ≤
        |arg (-derivWithin f (Icc a b) b / derivWithin g (Icc c d) c)| ∧
      2 * Real.pi / ((m : ℝ) + 2) ≤ 2 * Real.pi -
        |arg (-derivWithin f (Icc a b) b / derivWithin g (Icc c d) c)| ∧
      arg (-derivWithin f (Icc a b) b / derivWithin g (Icc c d) c) ≠ 0 := by
  have hz := hchart z₀ (mem_closedBall_self hr.le)
  have hnat := s25za_radial_corner m hm hW hWD hζ
    (fun z hz' => (hchart z (hWr hz')).2.2) γ hs ht hK hmap
    (by rw [hzero]; exact hζ0) hu hv hρ hτ hleft hright hmin
  obtain ⟨k, hk, hef⟩ := s25gb_ordered_chart_tangent hab
    (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
    hfd.hasDerivWithinAt hfn (neg_ne_zero.2 hu)
    (by simpa only [hfb] using hz.1.differentiableAt)
    (by simpa only [hfb] using hz.2.1) hα hfline
  obtain ⟨l, hl, heg⟩ := s25gb_ordered_chart_tangent hcd
    (show c ∈ Icc c d from ⟨le_rfl, hcd.le⟩)
    hgd.hasDerivWithinAt hgn hv
    (by simpa only [hgc] using hz.1.differentiableAt)
    (by simpa only [hgc] using hz.2.1) hβ hgline
  rw [hfb] at hef
  rw [hgc] at heg
  have hdf : derivWithin f (Icc a b) b = -((k : ℂ) * (u / deriv ζ z₀)) := by
    have he : derivWithin f (Icc a b) b = ((k : ℂ) * (-u)) / deriv ζ z₀ :=
      (eq_div_iff hz.2.1).2 (by simpa only [mul_comm] using hef)
    simpa only [mul_neg, neg_div, mul_div_assoc] using he
  have hdg : derivWithin g (Icc c d) c = (l : ℂ) * (v / deriv ζ z₀) := by
    have he : derivWithin g (Icc c d) c = ((l : ℂ) * v) / deriv ζ z₀ :=
      (eq_div_iff hz.2.1).2 (by simpa only [mul_comm] using heg)
    simpa only [mul_div_assoc] using he
  exact s25ep_physical_zero_corner hr hζ0 hchart hu hv hk hl hdf hdg hnat.1

end LiZhongQC

