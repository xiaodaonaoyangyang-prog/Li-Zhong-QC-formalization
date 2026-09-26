import LiZhongQC.Basic
import LiZhongQC.RiemannMapping

/-!
# Domains with connected complement have holomorphic logarithms and square roots

The bridge needed by Theorem 2.1 (`thm2_1_canonical_form`): the book applies the Riemann mapping
theorem to `B ∪ E`, where `E` is one complementary component of a doubly connected `B`, using that
a domain whose complement in `ℂ̄` is connected is simply connected.  The Riemann mapping theorem
of `LiZhongQC.RiemannMapping` takes the analytic form of that hypothesis,
`RMT.HasHolomorphicSqrt U`, and this file proves it from connectedness of `(toExt U)ᶜ`
(`hasHolomorphicSqrt_of_isConnected_compl`).

Route, with closed polygons as the curves:
1. `segIntegral`, `polyIntegral`: integrals along segments and closed polygons.
2. `polyWinding`: the winding number of a closed polygon; it is an integer
   (`exists_int_polyWinding`), locally constant off the trace, and `0` far away.
3. `polyWinding_eq_zero_of_isConnected_compl`: if `(toExt U)ᶜ` is connected and the polygon lies in
   `U`, it winds `0` times around every point outside `U` (such a point is joined to `∞` inside
   the complement).
4. `polyIntegral_eq_zero_of_polyWinding_eq_zero`: Cauchy's theorem for closed polygons with winding
   number `0` around every point outside `U` (Dixon's proof).
5. Primitives from vanishing polygon integrals, then logarithms, then square roots.

This file alone does not prove Theorem 2.1: its case of two nondegenerate complementary components
still needs the construction of the annulus map.
-/

open Complex Set Metric Filter Topology
open scoped Real

noncomputable section

namespace LiZhongQC

/-! ### Integrals along segments and closed polygons -/

/-- The integral of `f` along the oriented segment from `p` to `q`,
`∫₀¹ f(p + t (q - p)) (q - p) dt`. -/
def segIntegral (f : ℂ → ℂ) (p q : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, f (p + (t : ℂ) * (q - p)) * (q - p)

/-- The oriented edges `(v₀, v₁), …, (vₙ₋₁, vₙ), (vₙ, v₀)` of the closed polygon with vertex
list `v`. -/
def polyEdges (v : List ℂ) : List (ℂ × ℂ) := v.zip (v.rotate 1)

/-- The integral of `f` along the closed polygon with vertex list `v`. -/
def polyIntegral (f : ℂ → ℂ) (v : List ℂ) : ℂ :=
  ((polyEdges v).map fun e => segIntegral f e.1 e.2).sum

/-- The trace (image) of the closed polygon with vertex list `v`. -/
def polyTrace (v : List ℂ) : Set ℂ := ⋃ e ∈ polyEdges v, segment ℝ e.1 e.2

/-- The winding number of the closed polygon `v` around `a`, `(1/2πi) ∮ dz/(z - a)`. -/
def polyWinding (v : List ℂ) (a : ℂ) : ℂ :=
  polyIntegral (fun z => (z - a)⁻¹) v / (2 * π * I)

/-! ### Basic facts about polygon integrals -/

/-- The trace of a closed polygon is compact: a finite union of segments. -/
theorem isCompact_polyTrace (v : List ℂ) : IsCompact (polyTrace v) := by
  unfold polyTrace
  refine (List.finite_toSet (polyEdges v)).isCompact_biUnion fun e _ => ?_
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

/-- The complement of the trace of a closed polygon is open. -/
theorem isOpen_compl_polyTrace (v : List ℂ) : IsOpen (polyTrace v)ᶜ :=
  (isCompact_polyTrace v).isClosed.isOpen_compl

/-- A point off the trace is off every edge. -/
theorem notMem_segment_of_notMem_polyTrace {v : List ℂ} {a : ℂ} (ha : a ∉ polyTrace v)
    {e : ℂ × ℂ} (he : e ∈ polyEdges v) : a ∉ segment ℝ e.1 e.2 :=
  fun h => ha (Set.mem_iUnion₂.mpr ⟨e, he, h⟩)

/-- The norm of a list sum is at most the sum of the norms. -/
theorem norm_list_sum_le : ∀ l : List ℂ, ‖l.sum‖ ≤ (l.map fun z => ‖z‖).sum
  | [] => by simp
  | x :: l => by
    simp only [List.sum_cons, List.map_cons]
    have h1 := norm_list_sum_le l
    have h2 := norm_add_le x l.sum
    linarith

/-- Two integers whose casts are at distance `< 1` are equal. -/
theorem int_eq_of_norm_cast_sub_lt_one {m n : ℤ} (h : ‖(m : ℂ) - n‖ < 1) : m = n := by
  have h1 : ‖((m - n : ℤ) : ℂ)‖ < 1 := by push_cast; exact h
  rw [Complex.norm_intCast, ← Int.cast_abs, ← Int.cast_one (R := ℝ), Int.cast_lt] at h1
  exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp h1)

/-- The product of the ratios `(y - a)/(x - a)` along a zip of two lists of equal length
telescopes into a quotient of two products. -/
theorem prod_zip_div (a : ℂ) :
    ∀ (v w : List ℂ), v.length = w.length →
      ((v.zip w).map fun e => (e.2 - a) / (e.1 - a)).prod
        = (w.map fun z => z - a).prod / (v.map fun z => z - a).prod
  | [], [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: v, y :: w, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.prod_cons, List.length_cons] at h ⊢
    rw [prod_zip_div a v w (by omega), div_mul_div_comm]

/-- Along a segment missing `a`, the ratio `(q - a)/(p - a)` lies in the slit plane. -/
theorem div_mem_slitPlane_of_notMem_segment {a p q : ℂ} (ha : a ∉ segment ℝ p q) :
    (q - a) / (p - a) ∈ slitPlane := by
  have hpa : p - a ≠ 0 := by
    intro h
    apply ha
    rw [sub_eq_zero] at h
    rw [← h]
    exact left_mem_segment ℝ p q
  rw [mem_slitPlane_iff_not_le_zero]
  intro hle
  set ρ : ℂ := (q - a) / (p - a) with hρ
  obtain ⟨hre, him⟩ := Complex.le_def.mp hle
  rw [Complex.zero_re] at hre
  rw [Complex.zero_im] at him
  set r : ℝ := ρ.re with hr
  have hρr : ρ = (r : ℂ) := Complex.ext rfl (by rw [Complex.ofReal_im]; exact him)
  have hr1 : 0 < 1 - r := by linarith
  have h1r : (1 : ℂ) - (r : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr hr1.ne'
  apply ha
  rw [segment_eq_image']
  refine ⟨1 / (1 - r), ⟨by positivity, ?_⟩, ?_⟩
  · rw [div_le_one hr1]; linarith
  · have hq : q - a = ρ * (p - a) := by rw [hρ, div_mul_cancel₀ _ hpa]
    have hq' : q = a + (r : ℂ) * (p - a) := by rw [← hρr]; linear_combination hq
    show p + (1 / (1 - r)) • (q - p) = a
    rw [Complex.real_smul, hq']
    push_cast
    field_simp
    ring

/-- The segment from `1` to a point of the slit plane stays in the slit plane. -/
theorem one_sub_add_mul_mem_slitPlane {ρ : ℂ} (hρ : ρ ∈ slitPlane) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : (1 - (t : ℂ)) + t * ρ ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hρ ⊢
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.add_im, Complex.sub_im, Complex.one_im, Complex.mul_im, zero_mul,
    sub_zero, add_zero, zero_add]
  obtain ⟨ht0, ht1⟩ := ht
  rcases hρ with h | h
  · left
    rcases eq_or_lt_of_le ht1 with h1 | h1
    · rw [h1]; linarith
    · linarith [mul_nonneg ht0 h.le]
  · rcases eq_or_lt_of_le ht0 with h0 | h0
    · left; rw [← h0]; norm_num
    · right; exact mul_ne_zero h0.ne' h

-- Integral algebra of segments and polygons (session d0).

/-- The point `p + t (q - p)`, `t ∈ [0, 1]`, lies on the segment from `p` to `q`. -/
theorem mem_segment_of_mem_Icc {p q : ℂ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    p + (t : ℂ) * (q - p) ∈ segment ℝ p q := by
  rw [segment_eq_image']
  exact ⟨t, ht, by simp only [Complex.real_smul]⟩

/-- A segment integral only sees the values on the segment. -/
theorem segIntegral_congr {f g : ℂ → ℂ} {p q : ℂ} (h : EqOn f g (segment ℝ p q)) :
    segIntegral f p q = segIntegral g p q := by
  unfold segIntegral
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  simp only [h (mem_segment_of_mem_Icc ht)]

/-- A polygon integral only sees the values on the trace. -/
theorem polyIntegral_congr {f g : ℂ → ℂ} {v : List ℂ} (h : EqOn f g (polyTrace v)) :
    polyIntegral f v = polyIntegral g v := by
  unfold polyIntegral
  congr 1
  refine List.map_congr_left fun e he => ?_
  exact segIntegral_congr fun z hz => h (mem_iUnion₂.2 ⟨e, he, hz⟩)

/-- The integrand of a segment integral of a function continuous on the segment is
interval-integrable. -/
theorem segIntegral_intervalIntegrable {f : ℂ → ℂ} {p q : ℂ}
    (hf : ContinuousOn f (segment ℝ p q)) :
    IntervalIntegrable (fun t : ℝ => f (p + (t : ℂ) * (q - p)) * (q - p)) MeasureTheory.volume 0 1 := by
  have hcont : ContinuousOn (fun t : ℝ => f (p + (t : ℂ) * (q - p)) * (q - p)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.mul ?_ continuousOn_const
    refine hf.comp ?_ fun t ht => mem_segment_of_mem_Icc ht
    fun_prop
  exact ContinuousOn.intervalIntegrable (μ := MeasureTheory.volume) hcont

theorem segIntegral_sub {f g : ℂ → ℂ} {p q : ℂ} (hf : ContinuousOn f (segment ℝ p q))
    (hg : ContinuousOn g (segment ℝ p q)) :
    segIntegral (fun z => f z - g z) p q = segIntegral f p q - segIntegral g p q := by
  unfold segIntegral
  rw [← intervalIntegral.integral_sub (segIntegral_intervalIntegrable hf)
    (segIntegral_intervalIntegrable hg)]
  congr 1
  funext t
  ring

theorem segIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (p q : ℂ) :
    segIntegral (fun z => c * f z) p q = c * segIntegral f p q := by
  unfold segIntegral
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext t
  ring

/-- Every edge of the polygon lies in its trace. -/
theorem segment_subset_polyTrace {v : List ℂ} {e : ℂ × ℂ} (he : e ∈ polyEdges v) :
    segment ℝ e.1 e.2 ⊆ polyTrace v :=
  fun _ hz => mem_iUnion₂.2 ⟨e, he, hz⟩

theorem polyIntegral_sub {f g : ℂ → ℂ} {v : List ℂ} (hf : ContinuousOn f (polyTrace v))
    (hg : ContinuousOn g (polyTrace v)) :
    polyIntegral (fun z => f z - g z) v = polyIntegral f v - polyIntegral g v := by
  unfold polyIntegral
  have key : ∀ l : List (ℂ × ℂ), (∀ e ∈ l, segment ℝ e.1 e.2 ⊆ polyTrace v) →
      (l.map fun e => segIntegral (fun z => f z - g z) e.1 e.2).sum
        = (l.map fun e => segIntegral f e.1 e.2).sum
          - (l.map fun e => segIntegral g e.1 e.2).sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons e l ih =>
      intro hl
      have hsub : segment ℝ e.1 e.2 ⊆ polyTrace v := hl e (by simp)
      simp only [List.map_cons, List.sum_cons]
      rw [ih (fun e' he' => hl e' (by simp [he'])),
        segIntegral_sub (hf.mono hsub) (hg.mono hsub)]
      ring
  exact key _ fun e he => segment_subset_polyTrace he

theorem polyIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (v : List ℂ) :
    polyIntegral (fun z => c * f z) v = c * polyIntegral f v := by
  unfold polyIntegral
  simp only [segIntegral_const_mul]
  rw [List.sum_map_mul_left]

/-- The standard estimate `‖∫_[p,q] f‖ ≤ C ‖q - p‖`. -/
theorem norm_segIntegral_le {f : ℂ → ℂ} {p q : ℂ} {C : ℝ}
    (h : ∀ z ∈ segment ℝ p q, ‖f z‖ ≤ C) : ‖segIntegral f p q‖ ≤ C * ‖q - p‖ := by
  unfold segIntegral
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun t : ℝ => f (p + (t : ℂ) * (q - p)) * (q - p)) (C := C * ‖q - p‖) ?_
  · simpa using this
  · intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (h _ (mem_segment_of_mem_Icc (Ioc_subset_Icc_self ht)))
      (norm_nonneg _)

/-- The standard estimate `‖∮ f‖ ≤ C · length` for a closed polygon. -/
theorem norm_polyIntegral_le {f : ℂ → ℂ} {v : List ℂ} {C : ℝ}
    (h : ∀ z ∈ polyTrace v, ‖f z‖ ≤ C) :
    ‖polyIntegral f v‖ ≤ C * ((polyEdges v).map fun e => ‖e.2 - e.1‖).sum := by
  unfold polyIntegral
  have key : ∀ l : List (ℂ × ℂ), (∀ e ∈ l, segment ℝ e.1 e.2 ⊆ polyTrace v) →
      ‖(l.map fun e => segIntegral f e.1 e.2).sum‖ ≤ C * (l.map fun e => ‖e.2 - e.1‖).sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons e l ih =>
      intro hl
      have hsub : segment ℝ e.1 e.2 ⊆ polyTrace v := hl e (by simp)
      simp only [List.map_cons, List.sum_cons]
      calc ‖segIntegral f e.1 e.2 + (l.map fun e => segIntegral f e.1 e.2).sum‖
          ≤ ‖segIntegral f e.1 e.2‖ + ‖(l.map fun e => segIntegral f e.1 e.2).sum‖ :=
            norm_add_le _ _
        _ ≤ C * ‖e.2 - e.1‖ + C * (l.map fun e => ‖e.2 - e.1‖).sum :=
            add_le_add (norm_segIntegral_le fun z hz => h z (hsub hz))
              (ih fun e' he' => hl e' (by simp [he']))
        _ = C * (‖e.2 - e.1‖ + (l.map fun e => ‖e.2 - e.1‖).sum) := by ring
  exact key _ fun e he => segment_subset_polyTrace he


-- The difference quotient `dslope`.

/-- `dslope` is symmetric in its two points. -/
theorem dslope_comm (f : ℂ → ℂ) (a b : ℂ) : dslope f a b = dslope f b a := by
  rcases eq_or_ne b a with rfl | h
  · rfl
  · rw [dslope_of_ne f h, dslope_of_ne f h.symm, slope_comm]

/-- For `F` holomorphic on an open set `U`, the difference quotient `(w, z) ↦ dslope F w z` is
jointly continuous on `U × U`.  Off the diagonal it is the quotient `(F z - F w)/(z - w)`; at a
diagonal point `(c, c)` the mean value inequality for `F - F'(c)·id` on a small ball gives
`‖dslope F w z - F'(c)‖ ≤ sup_ball ‖F' - F'(c)‖`, which is small by continuity of `F'`. -/
theorem continuousOn_dslope_prod {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) :
    ContinuousOn (fun p : ℂ × ℂ => dslope F p.1 p.2) (U ×ˢ U) := by
  refine fun p hp => ContinuousAt.continuousWithinAt ?_
  obtain ⟨ha, hb⟩ := mem_prod.1 hp
  rcases eq_or_ne p.1 p.2 with heq | hne
  · -- diagonal point `(c, c)`, `c = p.1 = p.2`
    have hFc : ContinuousAt (deriv F) p.1 :=
      (hF.deriv hU).continuousOn.continuousAt (hU.mem_nhds ha)
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ₁, hδ₁, hδ₁U⟩ := Metric.isOpen_iff.1 hU p.1 ha
    obtain ⟨δ₂, hδ₂, hδ₂F⟩ := Metric.continuousAt_iff.1 hFc (ε / 2) (by positivity)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun q hq => ?_⟩
    -- both coordinates of `q` lie in the ball of radius `min δ₁ δ₂` about `c`
    have hq1 : dist q.1 p.1 < min δ₁ δ₂ :=
      lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_left _ _) hq
    have hq2 : dist q.2 p.1 < min δ₁ δ₂ := by
      have := lt_of_le_of_lt (by rw [Prod.dist_eq]; exact le_max_right _ _ : dist q.2 p.2 ≤ dist q p) hq
      rwa [← heq] at this
    have hball : ball p.1 (min δ₁ δ₂) ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hδ₁U
    have hder : ∀ z ∈ ball p.1 (min δ₁ δ₂), ‖deriv F z - deriv F p.1‖ < ε / 2 := fun z hz => by
      have := hδ₂F (lt_of_lt_of_le (mem_ball.1 hz) (min_le_right _ _))
      rwa [dist_eq_norm] at this
    rw [dist_eq_norm, show dslope F p.1 p.2 = deriv F p.1 by rw [← heq, dslope_same]]
    rcases eq_or_ne q.2 q.1 with hqq | hqq
    · rw [hqq, dslope_same]
      exact lt_of_lt_of_le (hder q.1 (mem_ball.2 hq1)) (by linarith)
    · -- mean value inequality for `G = F - F'(c) · id` on the convex ball
      have hG : ∀ z ∈ ball p.1 (min δ₁ δ₂),
          HasDerivAt (fun z => F z - z * deriv F p.1) (deriv F z - deriv F p.1) z := fun z hz =>
        (hF.differentiableAt (hU.mem_nhds (hball hz))).hasDerivAt.sub
          (hasDerivAt_mul_const (deriv F p.1))
      have hmv := (convex_ball p.1 (min δ₁ δ₂)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hG z hz).differentiableAt)
        (fun z hz => by rw [(hG z hz).deriv]; exact (hder z hz).le)
        (mem_ball.2 hq1) (mem_ball.2 hq2)
      -- `hmv : ‖(F q.2 - F'(c) q.2) - (F q.1 - F'(c) q.1)‖ ≤ ε/2 * ‖q.2 - q.1‖`
      have hne' : q.2 - q.1 ≠ 0 := sub_ne_zero.2 hqq
      have hpos : 0 < ‖q.2 - q.1‖ := norm_pos_iff.2 hne'
      rw [dslope_of_ne F hqq, slope_def_field]
      have hrew : (F q.2 - F q.1) / (q.2 - q.1) - deriv F p.1
          = ((F q.2 - q.2 * deriv F p.1) - (F q.1 - q.1 * deriv F p.1)) / (q.2 - q.1) := by
        field_simp
        ring
      rw [hrew, norm_div, div_lt_iff₀ hpos]
      calc ‖(F q.2 - q.2 * deriv F p.1) - (F q.1 - q.1 * deriv F p.1)‖
          ≤ ε / 2 * ‖q.2 - q.1‖ := hmv
        _ < ε * ‖q.2 - q.1‖ := by nlinarith
  · -- off the diagonal, `dslope` is the quotient of continuous functions
    have hev : (fun q : ℂ × ℂ => (F q.2 - F q.1) / (q.2 - q.1)) =ᶠ[𝓝 p]
        fun q : ℂ × ℂ => dslope F q.1 q.2 := by
      have hc : Continuous fun q : ℂ × ℂ => q.1 - q.2 := by fun_prop
      have h0 : (fun q : ℂ × ℂ => q.1 - q.2) p ≠ 0 := sub_ne_zero.2 hne
      filter_upwards [hc.continuousAt.eventually_ne h0] with q hq
      rw [dslope_of_ne F (sub_ne_zero.1 hq).symm, slope_def_field]
    refine ContinuousAt.congr ?_ hev
    have hFa : ContinuousAt F p.1 := hF.continuousOn.continuousAt (hU.mem_nhds ha)
    have hFb : ContinuousAt F p.2 := hF.continuousOn.continuousAt (hU.mem_nhds hb)
    exact ((hFb.comp continuousAt_snd).sub (hFa.comp continuousAt_fst)).div
      (continuousAt_snd.sub continuousAt_fst) (sub_ne_zero.2 hne.symm)


-- Holomorphy of parameter integrals along polygons.

/-- A segment is compact. -/
theorem isCompact_segment_ℂ (p q : ℂ) : IsCompact (segment ℝ p q) := by
  rw [segment_eq_image']
  exact isCompact_Icc.image (by fun_prop)

/-- **Holomorphy of a parameter integral along a segment.**  If `K w z` is jointly continuous on
`W ×ˢ [p, q]` and holomorphic in `w ∈ W` (open) for every `z ∈ [p, q]`, then
`w ↦ ∫_[p,q] K w z dz` is holomorphic on `W`.

Proof: on a ball `B = ball w₀ r` with `closedBall w₀ (2r) ⊆ W`, the Cauchy estimate bounds
`‖∂_w K w z‖` by `M/r` uniformly in `z ∈ [p, q]` and `w ∈ B`, where `M` bounds `‖K‖` on the compact
`closedBall w₀ (2r) ×ˢ [p, q]`; differentiation under the integral sign
(`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`) then applies.  Measurability
of `t ↦ ∂_w K w₀ (γ t)` is obtained as an a.e. limit of difference quotients. -/
theorem differentiableOn_segIntegral_param {K : ℂ → ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    {p q : ℂ} (hK : ContinuousOn (fun x : ℂ × ℂ => K x.1 x.2) (W ×ˢ segment ℝ p q))
    (hKd : ∀ z ∈ segment ℝ p q, DifferentiableOn ℂ (fun w => K w z) W) :
    DifferentiableOn ℂ (fun w => segIntegral (K w) p q) W := by
  intro w₀ hw₀
  obtain ⟨R, hR, hRW⟩ := Metric.isOpen_iff.1 hW w₀ hw₀
  have hr : (0 : ℝ) < R / 4 := by positivity
  have h2r : closedBall w₀ (2 * (R / 4)) ⊆ W :=
    (closedBall_subset_ball (by linarith)).trans hRW
  have hballW : ball w₀ (R / 4) ⊆ W :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans h2r
  -- a bound for `‖K‖` on the compact set `closedBall w₀ (2r) ×ˢ [p, q]`
  obtain ⟨M, hM⟩ := ((isCompact_closedBall w₀ (2 * (R / 4))).prod (isCompact_segment_ℂ p q))
    |>.exists_bound_of_continuousOn (hK.mono (prod_mono h2r subset_rfl))
  -- Cauchy estimate for the `w`-derivative on the smaller ball
  have hderiv_bound : ∀ z ∈ segment ℝ p q, ∀ w ∈ ball w₀ (R / 4),
      ‖deriv (fun w => K w z) w‖ ≤ M / (R / 4) := by
    intro z hz w hw
    have hsub : closedBall w (R / 4) ⊆ closedBall w₀ (2 * (R / 4)) :=
      closedBall_subset_closedBall' (by linarith [mem_ball.1 hw])
    have hd : DiffContOnCl ℂ (fun w => K w z) (ball w (R / 4)) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball w hr.ne']
      exact (hKd z hz).mono (hsub.trans h2r)
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd fun ζ hζ => ?_
    exact hM (ζ, z) ⟨hsub (sphere_subset_closedBall hζ), hz⟩
  -- the parametrised segment
  have hγ : ∀ t ∈ Icc (0 : ℝ) 1, p + (t : ℂ) * (q - p) ∈ segment ℝ p q :=
    fun t ht => mem_segment_of_mem_Icc ht
  -- continuity in `t` of the integrand, for each `w ∈ W`
  have hcont : ∀ w ∈ W, ContinuousOn (fun t : ℝ => K w (p + (t : ℂ) * (q - p)) * (q - p))
      (Icc (0 : ℝ) 1) := by
    intro w hw
    refine ContinuousOn.mul ?_ continuousOn_const
    exact hK.comp (f := fun t : ℝ => ((w, p + (t : ℂ) * (q - p)) : ℂ × ℂ)) (by fun_prop)
      fun t ht => ⟨hw, hγ t ht⟩
  have hIoc : uIoc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
  -- the derivative of the integrand in `w`, for `w ∈ ball w₀ r` and `t ∈ [0, 1]`
  have hdiff : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ ball w₀ (R / 4),
      HasDerivAt (fun w => K w (p + (t : ℂ) * (q - p)) * (q - p))
        (deriv (fun w => K w (p + (t : ℂ) * (q - p))) w * (q - p)) w := fun t ht w hw =>
    (((hKd _ (hγ t ht)).differentiableAt (hW.mem_nhds (hballW hw))).hasDerivAt).mul_const _
  -- measurability of `t ↦ ∂_w K w₀ (γ t)`: an a.e. limit of difference quotients
  have hmeas' : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => deriv (fun w => K w (p + (t : ℂ) * (q - p))) w₀ * (q - p))
      (MeasureTheory.volume.restrict (uIoc (0 : ℝ) 1)) := by
    have hh : ∀ n : ℕ, w₀ + (((R / 8) / ((n : ℝ) + 1) : ℝ) : ℂ) ∈ ball w₀ (R / 4) := by
      intro n
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      calc R / 8 / ((n : ℝ) + 1) ≤ R / 8 / 1 := by gcongr
        _ < R / 4 := by linarith
    have hne : ∀ n : ℕ, (((R / 8) / ((n : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := fun n =>
      Complex.ofReal_ne_zero.2 (by positivity)
    refine AEMeasurable.aestronglyMeasurable
      (aemeasurable_of_tendsto_metrizable_ae'
        (f := fun n (t : ℝ) => slope (fun w => K w (p + (t : ℂ) * (q - p)) * (q - p)) w₀
          (w₀ + (((R / 8) / ((n : ℝ) + 1) : ℝ) : ℂ))) (fun n => ?_) ?_)
    · -- each difference quotient is continuous in `t`
      refine (ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc).aemeasurable
      refine ContinuousOn.mono ?_ hIoc
      simp only [slope_def_field]
      refine ContinuousOn.div (ContinuousOn.sub (hcont _ (hballW (hh n))) (hcont _ hw₀))
        continuousOn_const fun t _ => ?_
      rw [add_sub_cancel_left]
      exact hne n
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
      have h1 := hdiff t (hIoc ht) w₀ (mem_ball_self hr)
      rw [hasDerivAt_iff_tendsto_slope] at h1
      refine h1.comp ?_
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h0 : Tendsto (fun n : ℕ => (((R / 8) / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 0) := by
          have hreal : Tendsto (fun n : ℕ => (R / 8) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
            tendsto_const_nhds.div_atTop
              (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          have h0' := (Complex.continuous_ofReal.tendsto 0).comp hreal
          rw [Complex.ofReal_zero] at h0'
          exact h0'
        simpa using tendsto_const_nhds.add h0
      · simp only [mem_compl_iff, mem_singleton_iff]
        intro h
        exact hne n (by linear_combination h)
  -- differentiate under the integral sign
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := 0) (b := 1)
    (F := fun w (t : ℝ) => K w (p + (t : ℂ) * (q - p)) * (q - p))
    (F' := fun w (t : ℝ) => deriv (fun w => K w (p + (t : ℂ) * (q - p))) w * (q - p))
    (x₀ := w₀) (s := ball w₀ (R / 4)) (bound := fun _ => M / (R / 4) * ‖q - p‖)
    (ball_mem_nhds w₀ hr) ?_ ?_ hmeas' ?_ ?_ ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · filter_upwards [hW.mem_nhds hw₀] with w hw
    exact ((hcont w hw).mono hIoc).aestronglyMeasurable measurableSet_uIoc
  · have h : ContinuousOn (fun t : ℝ => K w₀ (p + (t : ℂ) * (q - p)) * (q - p)) (uIcc 0 1) := by
      rw [uIcc_of_le zero_le_one]
      exact hcont w₀ hw₀
    exact h.intervalIntegrable
  · filter_upwards with t
    intro ht w hw
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hderiv_bound _ (hγ t (hIoc ht)) w hw) (norm_nonneg _)
  · exact intervalIntegrable_const
  · filter_upwards with t
    intro ht w hw
    exact hdiff t (hIoc ht) w hw

/-- **Holomorphy of a parameter integral along a closed polygon.** -/
theorem differentiableOn_polyIntegral_param {K : ℂ → ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    {v : List ℂ} (hK : ContinuousOn (fun x : ℂ × ℂ => K x.1 x.2) (W ×ˢ polyTrace v))
    (hKd : ∀ z ∈ polyTrace v, DifferentiableOn ℂ (fun w => K w z) W) :
    DifferentiableOn ℂ (fun w => polyIntegral (K w) v) W := by
  unfold polyIntegral
  have key : ∀ l : List (ℂ × ℂ), (∀ e ∈ l, segment ℝ e.1 e.2 ⊆ polyTrace v) →
      DifferentiableOn ℂ (fun w => (l.map fun e => segIntegral (K w) e.1 e.2).sum) W := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons e l ih =>
      intro hl
      have hsub : segment ℝ e.1 e.2 ⊆ polyTrace v := hl e (by simp)
      simp only [List.map_cons, List.sum_cons]
      exact (differentiableOn_segIntegral_param hW (hK.mono (prod_mono subset_rfl hsub))
        fun z hz => hKd z (hsub hz)).add (ih fun e' he' => hl e' (by simp [he']))
  exact key _ fun e he => segment_subset_polyTrace he

/-! ### Winding numbers -/

/-- Along a segment missing `a`, `∫ dz/(z - a)` is the principal logarithm of the ratio
`(q - a)/(p - a)` (which then lies off the closed negative real axis). -/
theorem segIntegral_inv_sub_eq_log {a p q : ℂ} (ha : a ∉ segment ℝ p q) :
    segIntegral (fun z => (z - a)⁻¹) p q = log ((q - a) / (p - a)) := by
  have hpa : p - a ≠ 0 := by
    intro h
    apply ha
    rw [sub_eq_zero] at h
    rw [← h]
    exact left_mem_segment ℝ p q
  set ρ : ℂ := (q - a) / (p - a) with hρ
  have hρs : ρ ∈ slitPlane := div_mem_slitPlane_of_notMem_segment ha
  have hpath : ∀ t ∈ Icc (0 : ℝ) 1, (1 - (t : ℂ)) + t * ρ ∈ slitPlane :=
    fun t ht => one_sub_add_mul_mem_slitPlane hρs ht
  have hpath0 : ∀ t ∈ Icc (0 : ℝ) 1, (1 - (t : ℂ)) + t * ρ ≠ 0 :=
    fun t ht => slitPlane_ne_zero (hpath t ht)
  -- the integrand along the normalized path `(1 - t) + t ρ`
  have hint : EqOn (fun t : ℝ => (p + (t : ℂ) * (q - p) - a)⁻¹ * (q - p))
      (fun t : ℝ => (ρ - 1) / ((1 - (t : ℂ)) + t * ρ)) (uIcc 0 1) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have h1 := hpath0 t ht
    have hkey : p + (t : ℂ) * (q - p) - a = (p - a) * ((1 - (t : ℂ)) + t * ρ) := by
      rw [hρ]
      field_simp
      ring
    show (p + (t : ℂ) * (q - p) - a)⁻¹ * (q - p) = (ρ - 1) / ((1 - (t : ℂ)) + t * ρ)
    rw [hkey, hρ]
    field_simp
    ring
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => log ((1 - (t : ℂ)) + t * ρ))
        ((ρ - 1) / ((1 - (t : ℂ)) + t * ρ)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hd : HasDerivAt (fun t : ℝ => (1 - (t : ℂ)) + t * ρ) (ρ - 1) t := by
      have h0' : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
      have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) ((1 : ℝ) : ℂ) t := h0'.ofReal_comp
      have h1 := (h0.const_sub 1).add (h0.mul_const ρ)
      convert h1 using 1
      push_cast
      ring
    exact hd.clog_real (hpath t ht)
  have hcont : ContinuousOn (fun t : ℝ => (ρ - 1) / ((1 - (t : ℂ)) + t * ρ)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ContinuousOn.div continuousOn_const (by fun_prop) fun t ht => hpath0 t ht
  rw [segIntegral]
  rw [intervalIntegral.integral_congr hint,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  simp

/-- Off the trace, the polygon integral of `1/(z - a)` is the sum of the edge logarithms. -/
theorem polyIntegral_inv_sub_eq_sum_log {v : List ℂ} {a : ℂ} (ha : a ∉ polyTrace v) :
    polyIntegral (fun z => (z - a)⁻¹) v
      = ((polyEdges v).map fun e => log ((e.2 - a) / (e.1 - a))).sum := by
  unfold polyIntegral
  congr 1
  exact List.map_congr_left fun e he =>
    segIntegral_inv_sub_eq_log (notMem_segment_of_notMem_polyTrace ha he)

/-- The winding number of a closed polygon around a point off its trace is an integer. -/
theorem exists_int_polyWinding {v : List ℂ} {a : ℂ} (ha : a ∉ polyTrace v) :
    ∃ n : ℤ, polyWinding v a = n := by
  have hne : ∀ e ∈ polyEdges v, e.1 - a ≠ 0 ∧ e.2 - a ≠ 0 := by
    intro e he
    have h := notMem_segment_of_notMem_polyTrace ha he
    constructor
    · intro h0
      apply h
      rw [sub_eq_zero] at h0
      rw [← h0]
      exact left_mem_segment ℝ _ _
    · intro h0
      apply h
      rw [sub_eq_zero] at h0
      rw [← h0]
      exact right_mem_segment ℝ _ _
  -- `exp` of the polygon integral is the telescoping product of the edge ratios
  have hexp : exp (polyIntegral (fun z => (z - a)⁻¹) v) = 1 := by
    rw [polyIntegral_inv_sub_eq_sum_log ha, Complex.exp_list_sum, List.map_map]
    have hmap : (polyEdges v).map (exp ∘ fun e => log ((e.2 - a) / (e.1 - a)))
        = (polyEdges v).map fun e => (e.2 - a) / (e.1 - a) := by
      refine List.map_congr_left fun e he => ?_
      exact Complex.exp_log (div_ne_zero (hne e he).2 (hne e he).1)
    rw [hmap, polyEdges, prod_zip_div a v (v.rotate 1) (List.length_rotate v 1).symm,
      List.map_rotate, (List.rotate_perm _ 1).prod_eq]
    refine div_self (List.prod_ne_zero ?_)
    intro h0
    rw [List.mem_map] at h0
    obtain ⟨x, hx, hx0⟩ := h0
    have hx' : x ∈ (polyEdges v).map Prod.fst := by
      rw [polyEdges, List.map_fst_zip (by rw [List.length_rotate])]
      exact hx
    rw [List.mem_map] at hx'
    obtain ⟨e, he, rfl⟩ := hx'
    exact (hne e he).1 hx0
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
  exact ⟨n, by rw [polyWinding, hn, mul_div_assoc, div_self Complex.two_pi_I_ne_zero, mul_one]⟩

/-- The winding number is continuous in the point, off the trace. -/
theorem continuousAt_polyWinding {v : List ℂ} {a : ℂ} (ha : a ∉ polyTrace v) :
    ContinuousAt (polyWinding v) a := by
  have hev : ∀ᶠ b in 𝓝 a, b ∉ polyTrace v := (isOpen_compl_polyTrace v).mem_nhds ha
  have heq : (fun b => ((polyEdges v).map fun e => log ((e.2 - b) / (e.1 - b))).sum / (2 * π * I))
      =ᶠ[𝓝 a] polyWinding v := by
    filter_upwards [hev] with b hb
    rw [polyWinding, polyIntegral_inv_sub_eq_sum_log hb]
  refine ContinuousAt.congr ?_ heq
  refine ContinuousAt.div_const ?_ _
  have hterm : ∀ e ∈ polyEdges v, ContinuousAt (fun b => log ((e.2 - b) / (e.1 - b))) a := by
    intro e he
    have hseg := notMem_segment_of_notMem_polyTrace ha he
    have hpa : e.1 - a ≠ 0 := by
      intro h0
      apply hseg
      rw [sub_eq_zero] at h0
      rw [← h0]
      exact left_mem_segment ℝ _ _
    have hρ := div_mem_slitPlane_of_notMem_segment hseg
    have h1 : ContinuousAt (fun b : ℂ => e.2 - b) a := continuousAt_const.sub continuousAt_id
    have h2 : ContinuousAt (fun b : ℂ => e.1 - b) a := continuousAt_const.sub continuousAt_id
    have hratio : ContinuousAt (fun b : ℂ => (e.2 - b) / (e.1 - b)) a := h1.div h2 hpa
    exact hratio.clog hρ
  exact tendsto_list_sum (polyEdges v) hterm

/-- The winding number is locally constant off the trace. -/
theorem eventually_polyWinding_eq {v : List ℂ} {a : ℂ} (ha : a ∉ polyTrace v) :
    ∀ᶠ b in 𝓝 a, polyWinding v b = polyWinding v a := by
  have hev : ∀ᶠ b in 𝓝 a, b ∉ polyTrace v := (isOpen_compl_polyTrace v).mem_nhds ha
  have hclose : ∀ᶠ b in 𝓝 a, dist (polyWinding v b) (polyWinding v a) < 1 :=
    Metric.tendsto_nhds.mp (continuousAt_polyWinding ha) 1 one_pos
  obtain ⟨n, hn⟩ := exists_int_polyWinding ha
  filter_upwards [hev, hclose] with b hb hlt
  obtain ⟨m, hm⟩ := exists_int_polyWinding hb
  rw [hm, hn, dist_eq_norm] at hlt
  rw [hm, hn, int_eq_of_norm_cast_sub_lt_one hlt]

/-- The winding number vanishes around points far from the polygon. -/
theorem exists_polyWinding_eq_zero_of_norm_gt (v : List ℂ) :
    ∃ R : ℝ, ∀ a : ℂ, R < ‖a‖ → polyWinding v a = 0 := by
  obtain ⟨M, hM⟩ := (isCompact_polyTrace v).isBounded.subset_closedBall 0
  have hM' : ∀ z ∈ polyTrace v, ‖z‖ ≤ M := fun z hz => mem_closedBall_zero_iff.mp (hM hz)
  set L : ℝ := ((polyEdges v).map fun e => ‖e.2 - e.1‖).sum with hL
  have hL0 : 0 ≤ L := List.sum_nonneg fun x hx => by
    rw [List.mem_map] at hx
    obtain ⟨e, -, rfl⟩ := hx
    exact norm_nonneg _
  have hpos : 0 < L + 1 := by linarith
  refine ⟨M + L + 1, fun a ha => ?_⟩
  have hnot : a ∉ polyTrace v := fun h => by linarith [hM' a h]
  obtain ⟨n, hn⟩ := exists_int_polyWinding hnot
  -- each edge integral is at most `‖q - p‖ / (L + 1)`
  have hterm : ∀ e ∈ polyEdges v,
      ‖segIntegral (fun z => (z - a)⁻¹) e.1 e.2‖ ≤ ‖e.2 - e.1‖ * (1 / (L + 1)) := by
    intro e he
    rw [segIntegral]
    have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
        ‖(fun z => (z - a)⁻¹) (e.1 + (t : ℂ) * (e.2 - e.1)) * (e.2 - e.1)‖
          ≤ 1 / (L + 1) * ‖e.2 - e.1‖ := by
      intro t ht
      rw [uIoc_of_le zero_le_one] at ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
      have hmem : e.1 + (t : ℂ) * (e.2 - e.1) ∈ polyTrace v := by
        refine Set.mem_iUnion₂.mpr ⟨e, he, ?_⟩
        rw [segment_eq_image']
        refine ⟨t, ht', ?_⟩
        show e.1 + t • (e.2 - e.1) = e.1 + (t : ℂ) * (e.2 - e.1)
        rw [Complex.real_smul]
      have hz : ‖e.1 + (t : ℂ) * (e.2 - e.1)‖ ≤ M := hM' _ hmem
      have hdist : L + 1 ≤ ‖e.1 + (t : ℂ) * (e.2 - e.1) - a‖ := by
        have h1 := norm_sub_norm_le a (e.1 + (t : ℂ) * (e.2 - e.1))
        rw [norm_sub_rev] at h1
        linarith
      show ‖(e.1 + (t : ℂ) * (e.2 - e.1) - a)⁻¹ * (e.2 - e.1)‖ ≤ 1 / (L + 1) * ‖e.2 - e.1‖
      rw [norm_mul, norm_inv]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [one_div]
      exact inv_anti₀ hpos hdist
    calc ‖∫ t in (0 : ℝ)..1, (fun z => (z - a)⁻¹) (e.1 + (t : ℂ) * (e.2 - e.1)) * (e.2 - e.1)‖
        ≤ 1 / (L + 1) * ‖e.2 - e.1‖ * |1 - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = ‖e.2 - e.1‖ * (1 / (L + 1)) := by rw [sub_zero, abs_one, mul_one, mul_comm]
  have hbound : ‖polyIntegral (fun z => (z - a)⁻¹) v‖ ≤ L / (L + 1) := by
    rw [polyIntegral]
    calc ‖((polyEdges v).map fun e => segIntegral (fun z => (z - a)⁻¹) e.1 e.2).sum‖
        ≤ (((polyEdges v).map fun e => segIntegral (fun z => (z - a)⁻¹) e.1 e.2).map
            fun z => ‖z‖).sum := norm_list_sum_le _
      _ = ((polyEdges v).map fun e => ‖segIntegral (fun z => (z - a)⁻¹) e.1 e.2‖).sum := by
          rw [List.map_map]; rfl
      _ ≤ ((polyEdges v).map fun e => ‖e.2 - e.1‖ * (1 / (L + 1))).sum := List.sum_le_sum hterm
      _ = L / (L + 1) := by rw [List.sum_map_mul_right, ← hL, mul_one_div]
  have hlt1 : L / (L + 1) < 1 := by
    rw [div_lt_one hpos]
    linarith
  have hint : polyIntegral (fun z => (z - a)⁻¹) v = n * (2 * π * I) := by
    rw [polyWinding] at hn
    rw [← hn, div_mul_cancel₀ _ Complex.two_pi_I_ne_zero]
  have h2pi : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, RCLike.norm_two]
  rw [hint, norm_mul, Complex.norm_intCast, h2pi] at hbound
  have hlt : |(n : ℝ)| * (2 * π) < 1 := lt_of_le_of_lt hbound hlt1
  have habs : |(n : ℝ)| < 1 := by
    by_contra hcon
    push Not at hcon
    have := mul_le_mul_of_nonneg_right hcon (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith [Real.pi_gt_three]
  have hn0 : n = 0 := by
    rw [← Int.cast_abs, ← Int.cast_one (R := ℝ), Int.cast_lt] at habs
    exact Int.abs_lt_one_iff.mp habs
  rw [polyWinding, hint, hn0]
  simp

/-- If `ℂ̄ ∖ U` is connected, a closed polygon in `U` winds `0` times around every point
outside `U`. -/
theorem polyWinding_eq_zero_of_isConnected_compl {U : Set ℂ} (hc : IsConnected (toExt U)ᶜ)
    {v : List ℂ} (hv : polyTrace v ⊆ U) {a : ℂ} (ha : a ∉ U) : polyWinding v a = 0 := by
  obtain ⟨R, hR⟩ := exists_polyWinding_eq_zero_of_norm_gt v
  -- the winding number extended by `0` at `∞`
  set W : ExtPlane → ℂ := fun z => OnePoint.elim z 0 (polyWinding v) with hW
  -- the open set `Ω = ℂ̄ ∖ trace` on which `W` is locally constant
  set Ω : Set ExtPlane := (toExt (polyTrace v))ᶜ with hΩ
  have hΩo : IsOpen Ω := by
    rw [hΩ, isOpen_compl_iff, toExt, OnePoint.isClosed_image_coe]
    exact ⟨(isCompact_polyTrace v).isClosed, isCompact_polyTrace v⟩
  have hloc : ∀ z ∈ Ω, ∀ᶠ y in 𝓝 z, W y = W z := by
    intro z hz
    induction z using OnePoint.rec with
    | infty =>
      rw [OnePoint.hasBasis_nhds_infty.eventually_iff]
      refine ⟨closedBall 0 R, ⟨isClosed_closedBall, isCompact_closedBall _ _⟩, ?_⟩
      intro y hy
      rcases hy with ⟨b, hb, rfl⟩ | hy
      · simp only [hW, OnePoint.elim_some, OnePoint.elim_infty]
        exact hR b (by simpa [not_le] using hb)
      · rw [mem_singleton_iff] at hy
        rw [hy]
    | coe b =>
      have hb : b ∉ polyTrace v := fun h => hz ⟨b, h, rfl⟩
      rw [OnePoint.nhds_coe_eq, Filter.eventually_map]
      filter_upwards [eventually_polyWinding_eq hb] with y hy
      simpa only [hW, OnePoint.elim_some] using hy
  -- `{W = 0}` and `{W ≠ 0}` are open in `Ω`, disjoint, and cover the connected complement
  have hu : IsOpen {z | z ∈ Ω ∧ W z = 0} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    filter_upwards [hΩo.mem_nhds hz.1, hloc z hz.1] with y hy hWy
    exact ⟨hy, hWy.trans hz.2⟩
  have hv' : IsOpen {z | z ∈ Ω ∧ W z ≠ 0} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    filter_upwards [hΩo.mem_nhds hz.1, hloc z hz.1] with y hy hWy
    exact ⟨hy, by rw [hWy]; exact hz.2⟩
  have hsub : (toExt U)ᶜ ⊆ Ω := by
    intro z hz hzt
    apply hz
    obtain ⟨b, hb, rfl⟩ := hzt
    exact ⟨b, hv hb, rfl⟩
  have hinf : extInf ∈ (toExt U)ᶜ := by
    intro h
    obtain ⟨b, -, hb⟩ := h
    exact OnePoint.coe_ne_infty b hb
  have hWinf : W extInf = 0 := by simp [hW]
  have hcover : (toExt U)ᶜ ⊆ {z | z ∈ Ω ∧ W z = 0} ∪ {z | z ∈ Ω ∧ W z ≠ 0} := by
    intro z hz
    by_cases h0 : W z = 0
    · exact Or.inl ⟨hsub hz, h0⟩
    · exact Or.inr ⟨hsub hz, h0⟩
  have hdisj : Disjoint {z | z ∈ Ω ∧ W z = 0} {z | z ∈ Ω ∧ W z ≠ 0} := by
    rw [Set.disjoint_left]
    intro z h1 h2
    exact h2.2 h1.2
  have hne : ((toExt U)ᶜ ∩ {z | z ∈ Ω ∧ W z = 0}).Nonempty := ⟨extInf, hinf, hsub hinf, hWinf⟩
  have hall := hc.isPreconnected.subset_left_of_subset_union hu hv' hdisj hcover hne
  have haU : (a : ExtPlane) ∈ (toExt U)ᶜ := by
    intro h
    obtain ⟨b, hb, hba⟩ := h
    rw [OnePoint.coe_eq_coe] at hba
    rw [hba] at hb
    exact ha hb
  have h0 := (hall haU).2
  simpa [hW] using h0

/-! ### Open polygonal paths

Proof machinery for `exists_primitive_of_polyIntegral_eq_zero`: open polygonal paths with an
explicit first vertex, their integrals, endpoints and traces, and how they assemble into closed
polygons. -/

/-- The integral of `h` along the open polygonal path with vertices `a, b₁, …, bₙ`
(first vertex `a`, then the list).  Proof machinery for `exists_primitive_of_polyIntegral_eq_zero`. -/
def pathIntFrom (h : ℂ → ℂ) : ℂ → List ℂ → ℂ
  | _, [] => 0
  | a, b :: l => segIntegral h a b + pathIntFrom h b l

/-- The last vertex of the path `a, b₁, …, bₙ`.  Proof machinery for
`exists_primitive_of_polyIntegral_eq_zero`. -/
def lastOf : ℂ → List ℂ → ℂ
  | a, [] => a
  | _, b :: l => lastOf b l

/-- All segments of the path `a, b₁, …, bₙ` lie in `U`.  Proof machinery for
`exists_primitive_of_polyIntegral_eq_zero`. -/
def SegsIn (U : Set ℂ) : ℂ → List ℂ → Prop
  | _, [] => True
  | a, b :: l => segment ℝ a b ⊆ U ∧ SegsIn U b l

theorem pathIntFrom_append (h : ℂ → ℂ) (a : ℂ) (l₁ l₂ : List ℂ) :
    pathIntFrom h a (l₁ ++ l₂) = pathIntFrom h a l₁ + pathIntFrom h (lastOf a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil => simp [pathIntFrom, lastOf]
  | cons b l ih => simp [pathIntFrom, lastOf, ih, add_assoc]

theorem lastOf_append (a : ℂ) (l₁ l₂ : List ℂ) :
    lastOf a (l₁ ++ l₂) = lastOf (lastOf a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil => simp [lastOf]
  | cons b l ih => simp [lastOf, ih]

theorem segsIn_append {U : Set ℂ} {a : ℂ} {l₁ l₂ : List ℂ} :
    SegsIn U a (l₁ ++ l₂) ↔ SegsIn U a l₁ ∧ SegsIn U (lastOf a l₁) l₂ := by
  induction l₁ generalizing a with
  | nil => simp [SegsIn, lastOf]
  | cons b l ih => simp [SegsIn, lastOf, ih, and_assoc]

/-- The closed polygon `a :: l` is the open path `a, l` followed by the closing edge. -/
theorem polyIntegral_cons (h : ℂ → ℂ) (a : ℂ) (l : List ℂ) :
    polyIntegral h (a :: l) = pathIntFrom h a l + segIntegral h (lastOf a l) a := by
  have key : ∀ (c a : ℂ) (l : List ℂ),
      (((a :: l).zip (l ++ [c])).map fun e => segIntegral h e.1 e.2).sum
        = pathIntFrom h a l + segIntegral h (lastOf a l) c := by
    intro c a l
    induction l generalizing a with
    | nil => simp [pathIntFrom, lastOf]
    | cons b l ih => simp [pathIntFrom, lastOf, ih, add_assoc]
  unfold polyIntegral polyEdges
  rw [show (a :: l).rotate 1 = l ++ [a] by
    rw [show (1 : ℕ) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]]
  exact key a a l

/-- The trace of `a :: l` lies in `U` when all segments of the path and the closing edge do. -/
theorem polyTrace_cons_subset {U : Set ℂ} {a : ℂ} {l : List ℂ} (hl : SegsIn U a l)
    (hclose : segment ℝ (lastOf a l) a ⊆ U) : polyTrace (a :: l) ⊆ U := by
  have key : ∀ (c a : ℂ) (l : List ℂ), SegsIn U a l → segment ℝ (lastOf a l) c ⊆ U →
      ∀ e ∈ (a :: l).zip (l ++ [c]), segment ℝ e.1 e.2 ⊆ U := by
    intro c a l
    induction l generalizing a with
    | nil =>
      intro _ hc e he
      simp only [List.nil_append, List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at he
      subst he
      exact hc
    | cons b l ih =>
      intro hs hc e he
      simp only [List.cons_append, List.zip_cons_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact hs.1
      · exact ih b hs.2 hc e he
  intro z hz
  unfold polyTrace polyEdges at hz
  rw [show (a :: l).rotate 1 = l ++ [a] by
    rw [show (1 : ℕ) = 0 + 1 from rfl, List.rotate_cons_succ, List.rotate_zero]] at hz
  obtain ⟨e, he, hze⟩ := mem_iUnion₂.1 hz
  exact key a a l hl hclose e he hze

theorem segIntegral_self (h : ℂ → ℂ) (p : ℂ) : segIntegral h p p = 0 := by
  simp [segIntegral]

theorem segIntegral_const (c : ℂ) (p q : ℂ) : segIntegral (fun _ => c) p q = c * (q - p) := by
  simp [segIntegral]

/-- Reversing a segment negates the integral (`t ↦ 1 - t`). -/
theorem segIntegral_symm (h : ℂ → ℂ) (p q : ℂ) : segIntegral h q p = - segIntegral h p q := by
  unfold segIntegral
  have e : ∀ t : ℝ, h (q + (t : ℂ) * (p - q)) * (p - q)
      = (fun s : ℝ => -(h (p + (s : ℂ) * (q - p)) * (q - p))) (1 - t) := by
    intro t
    have hpt : q + (t : ℂ) * (p - q) = p + ((1 - t : ℝ) : ℂ) * (q - p) := by
      push_cast
      ring
    simp only [hpt]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => -(h (p + (s : ℂ) * (q - p)) * (q - p)))
    (1 : ℝ), sub_self, sub_zero, intervalIntegral.integral_neg]

theorem lastOf_reverse (a : ℂ) (l : List ℂ) :
    lastOf (lastOf a l) ((a :: l).reverse.tail) = a := by
  induction l generalizing a with
  | nil => simp [lastOf]
  | cons b l ih =>
    have e : (a :: b :: l).reverse.tail = (b :: l).reverse.tail ++ [a] := by
      rw [List.reverse_cons, List.tail_append_of_ne_nil (by simp)]
    simp only [lastOf, e, lastOf_append]

/-- The integral along the reversed path is the negative. -/
theorem pathIntFrom_reverse (h : ℂ → ℂ) (a : ℂ) (l : List ℂ) :
    pathIntFrom h (lastOf a l) ((a :: l).reverse.tail) = - pathIntFrom h a l := by
  induction l generalizing a with
  | nil => simp [pathIntFrom, lastOf]
  | cons b l ih =>
    have e : (a :: b :: l).reverse.tail = (b :: l).reverse.tail ++ [a] := by
      rw [List.reverse_cons, List.tail_append_of_ne_nil (by simp)]
    simp only [lastOf, e, pathIntFrom_append, ih, lastOf_reverse, pathIntFrom, segIntegral_symm h a b]
    ring

theorem segsIn_reverse {U : Set ℂ} {a : ℂ} {l : List ℂ} (hl : SegsIn U a l) :
    SegsIn U (lastOf a l) ((a :: l).reverse.tail) := by
  induction l generalizing a with
  | nil => simp [SegsIn]
  | cons b l ih =>
    have e : (a :: b :: l).reverse.tail = (b :: l).reverse.tail ++ [a] := by
      rw [List.reverse_cons, List.tail_append_of_ne_nil (by simp)]
    obtain ⟨hab, hbl⟩ := hl
    simp only [lastOf, e, segsIn_append, lastOf_reverse, SegsIn, and_true]
    refine ⟨ih hbl, ?_⟩
    rw [segment_symm]
    exact hab

/-! ### Cauchy's theorem and primitives -/

/-- **Dixon's key step.**  For `F` holomorphic on an open `U` and a closed polygon in `U` winding
`0` times around every point outside `U`, `∮ dslope F w z dz = 0` for every `w ∈ U`.

Proof: `g w := ∮ dslope F w z dz` is holomorphic on `U`, and `h w := ∮ F z / (z - w) dz` is
holomorphic off the trace; on `U ∩ V₀`, `V₀ := {w ∉ trace | winding w = 0}` (open), `g = h`
because `dslope F w z = F z/(z - w) - F w · (z - w)⁻¹` and `∮ (z - w)⁻¹ dz = 2πi · winding = 0`.
Since `U ∪ V₀ = ℂ`, the glued function `Φ` is entire; it is bounded (in fact `Φ w = h w` for
`‖w‖` large, with `‖h w‖ ≤ M · length/(‖w‖ - R)`), so it is constant by Liouville, and the
constant is `0` because the bound tends to `0`. -/
theorem polyIntegral_dslope_eq_zero {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) {v : List ℂ} (hv : polyTrace v ⊆ U)
    (hw : ∀ a ∉ U, polyWinding v a = 0) {w : ℂ} (hwU : w ∈ U) :
    polyIntegral (dslope F w) v = 0 := by
  classical
  -- `g` is holomorphic on `U`
  have hgd : DifferentiableOn ℂ (fun a => polyIntegral (dslope F a) v) U := by
    refine differentiableOn_polyIntegral_param hU ?_ ?_
    · exact (continuousOn_dslope_prod hU hF).mono (prod_mono subset_rfl hv)
    · intro z hz
      have : (fun a => dslope F a z) = dslope F z := by
        funext a
        exact dslope_comm F a z
      rw [this]
      exact (Complex.differentiableOn_dslope (hU.mem_nhds (hv hz))).2 hF
  -- `h` is holomorphic off the trace
  have hhd : DifferentiableOn ℂ (fun a => polyIntegral (fun z => F z / (z - a)) v)
      (polyTrace v)ᶜ := by
    refine differentiableOn_polyIntegral_param (isOpen_compl_polyTrace v) ?_ ?_
    · refine ContinuousOn.div ?_ ?_ ?_
      · exact (hF.continuousOn.comp continuousOn_snd fun x hx => hv hx.2)
      · exact continuousOn_snd.sub continuousOn_fst
      · rintro ⟨a, z⟩ ⟨ha, hz⟩ h0
        exact ha ((sub_eq_zero.1 h0) ▸ hz)
    · intro z hz
      refine (differentiableOn_const _).div ((differentiableOn_const _).sub differentiableOn_id)
        fun a ha => ?_
      exact sub_ne_zero.2 fun h => ha (h ▸ hz)
  -- `V₀` is open
  have hV₀open : IsOpen {a : ℂ | a ∉ polyTrace v ∧ polyWinding v a = 0} := by
    rw [isOpen_iff_mem_nhds]
    rintro a ⟨ha, hwa⟩
    filter_upwards [(isOpen_compl_polyTrace v).mem_nhds ha, eventually_polyWinding_eq ha]
      with b hb hb'
    exact ⟨hb, hb'.trans hwa⟩
  -- `g = h` on `U ∩ V₀`
  have h2πI : (2 * π * I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) I_ne_zero
  have hgh : ∀ a ∈ U, a ∉ polyTrace v → polyWinding v a = 0 →
      polyIntegral (dslope F a) v = polyIntegral (fun z => F z / (z - a)) v := by
    intro a haU ha hwa
    have h1 : polyIntegral (dslope F a) v
        = polyIntegral (fun z => F z / (z - a) - F a * (z - a)⁻¹) v := by
      refine polyIntegral_congr fun z hz => ?_
      have hza : z ≠ a := fun h => ha (h ▸ hz)
      rw [dslope_of_ne F hza, slope_def_field]
      simp only [div_eq_mul_inv, sub_mul]
    have hc1 : ContinuousOn (fun z => F z / (z - a)) (polyTrace v) := by
      refine (hF.continuousOn.mono hv).div (continuousOn_id.sub continuousOn_const) fun z hz => ?_
      exact sub_ne_zero.2 fun h => ha (h ▸ hz)
    have hc2 : ContinuousOn (fun z => F a * (z - a)⁻¹) (polyTrace v) := by
      refine continuousOn_const.mul ((continuousOn_id.sub continuousOn_const).inv₀ fun z hz => ?_)
      exact sub_ne_zero.2 fun h => ha ((show z = a from h) ▸ hz)
    have hwind : polyIntegral (fun z => (z - a)⁻¹) v = 0 := by
      have := hwa
      unfold polyWinding at this
      rwa [div_eq_zero_iff, or_iff_left h2πI] at this
    rw [h1, polyIntegral_sub hc1 hc2, polyIntegral_const_mul, hwind, mul_zero, sub_zero]
  -- the glued function
  set Φ : ℂ → ℂ := fun a =>
    if a ∈ U then polyIntegral (dslope F a) v else polyIntegral (fun z => F z / (z - a)) v
    with hΦdef
  have hΦh : ∀ a, a ∉ polyTrace v → polyWinding v a = 0 →
      Φ a = polyIntegral (fun z => F z / (z - a)) v := by
    intro a ha hwa
    by_cases haU : a ∈ U
    · rw [hΦdef]
      simp only [if_pos haU]
      exact hgh a haU ha hwa
    · rw [hΦdef]
      simp only [if_neg haU]
  have hΦ : Differentiable ℂ Φ := by
    intro a
    by_cases haU : a ∈ U
    · have hev : Φ =ᶠ[𝓝 a] fun b => polyIntegral (dslope F b) v := by
        filter_upwards [hU.mem_nhds haU] with b hb
        rw [hΦdef]
        simp only [if_pos hb]
      exact hev.differentiableAt_iff.2 (hgd.differentiableAt (hU.mem_nhds haU))
    · have haV : a ∈ {b : ℂ | b ∉ polyTrace v ∧ polyWinding v b = 0} :=
        ⟨fun h => haU (hv h), hw a haU⟩
      have hev : Φ =ᶠ[𝓝 a] fun b => polyIntegral (fun z => F z / (z - b)) v := by
        filter_upwards [hV₀open.mem_nhds haV] with b hb
        exact hΦh b hb.1 hb.2
      exact hev.differentiableAt_iff.2
        (hhd.differentiableAt ((isOpen_compl_polyTrace v).mem_nhds haV.1))
  -- the decay estimate far away
  obtain ⟨MF, hMF⟩ :=
    (isCompact_polyTrace v).exists_bound_of_continuousOn (hF.continuousOn.mono hv)
  obtain ⟨R₀, hR₀⟩ := exists_polyWinding_eq_zero_of_norm_gt v
  obtain ⟨R₁, hR₁⟩ := (isCompact_polyTrace v).isBounded.exists_norm_le
  have hL0 : (0 : ℝ) ≤ ((polyEdges v).map fun e => ‖e.2 - e.1‖).sum := by
    refine List.sum_nonneg fun x hx => ?_
    simp only [List.mem_map] at hx
    obtain ⟨e, -, rfl⟩ := hx
    exact norm_nonneg _
  have hMF' : ∀ z ∈ polyTrace v, ‖F z‖ ≤ max MF 0 := fun z hz =>
    (hMF z hz).trans (le_max_left _ _)
  have hdecay : ∀ a : ℂ, max R₀ R₁ < ‖a‖ →
      ‖Φ a‖ ≤ max MF 0 / (‖a‖ - R₁) * ((polyEdges v).map fun e => ‖e.2 - e.1‖).sum := by
    intro a ha
    have ha0 : R₀ < ‖a‖ := lt_of_le_of_lt (le_max_left _ _) ha
    have ha1 : R₁ < ‖a‖ := lt_of_le_of_lt (le_max_right _ _) ha
    have hatr : a ∉ polyTrace v := fun h => absurd ha1 (not_lt.2 (hR₁ a h))
    rw [hΦh a hatr (hR₀ a ha0)]
    refine norm_polyIntegral_le fun z hz => ?_
    have hza : ‖a‖ - R₁ ≤ ‖z - a‖ := by
      calc ‖a‖ - R₁ ≤ ‖a‖ - ‖z‖ := by linarith [hR₁ z hz]
        _ ≤ ‖a - z‖ := norm_sub_norm_le _ _
        _ = ‖z - a‖ := norm_sub_rev _ _
    have hpos : 0 < ‖a‖ - R₁ := by linarith
    rw [norm_div]
    calc ‖F z‖ / ‖z - a‖ ≤ max MF 0 / ‖z - a‖ :=
          div_le_div_of_nonneg_right (hMF' z hz) (norm_nonneg _)
      _ ≤ max MF 0 / (‖a‖ - R₁) := div_le_div_of_nonneg_left (le_max_right _ _) hpos hza
  -- `Φ` is bounded, hence constant
  have hbdd : Bornology.IsBounded (range Φ) := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) (max R₀ R₁ + 1)).exists_bound_of_continuousOn
      hΦ.continuous.continuousOn
    rw [isBounded_iff_forall_norm_le]
    refine ⟨max B (max MF 0 * ((polyEdges v).map fun e => ‖e.2 - e.1‖).sum), ?_⟩
    rintro _ ⟨a, rfl⟩
    by_cases ha : ‖a‖ ≤ max R₀ R₁ + 1
    · exact (hB a (mem_closedBall_zero_iff.2 ha)).trans (le_max_left _ _)
    · rw [not_le] at ha
      refine (hdecay a (by linarith)).trans (le_trans ?_ (le_max_right _ _))
      have h1 : (1 : ℝ) ≤ ‖a‖ - R₁ := by linarith [le_max_right R₀ R₁]
      have : max MF 0 / (‖a‖ - R₁) ≤ max MF 0 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [le_max_right MF 0]
      exact mul_le_mul_of_nonneg_right this hL0
  have hconst : ∀ a, Φ a = Φ w := fun a => hΦ.apply_eq_apply_of_bounded hbdd a w
  -- the constant is `0`: compare with far-away points
  have hΦw : Φ w = 0 := by
    rw [← norm_le_zero_iff]
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hML : (0 : ℝ) ≤ max MF 0 * ((polyEdges v).map fun e => ‖e.2 - e.1‖).sum :=
      mul_nonneg (le_max_right _ _) hL0
    -- the far-away point `T` on the real axis
    set T : ℝ := max R₀ R₁ + 1 + max MF 0 * ((polyEdges v).map fun e => ‖e.2 - e.1‖).sum / ε
      with hT
    have hTn : T ≤ ‖(T : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_abs_self T
    have hTbig : max R₀ R₁ < ‖(T : ℂ)‖ := by
      have := div_nonneg hML hε.le
      linarith
    have hD : max MF 0 * ((polyEdges v).map fun e => ‖e.2 - e.1‖).sum / ε + 1 ≤ ‖(T : ℂ)‖ - R₁ := by
      linarith [le_max_right R₀ R₁]
    have hDpos : 0 < ‖(T : ℂ)‖ - R₁ := by
      have := div_nonneg hML hε.le
      linarith
    calc ‖Φ w‖ = ‖Φ (T : ℂ)‖ := by rw [hconst (T : ℂ)]
      _ ≤ max MF 0 / (‖(T : ℂ)‖ - R₁) * ((polyEdges v).map fun e => ‖e.2 - e.1‖).sum :=
          hdecay _ hTbig
      _ < 0 + ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ hDpos, zero_add]
          have hkey : ε * (max MF 0 * ((polyEdges v).map fun e => ‖e.2 - e.1‖).sum / ε)
              = max MF 0 * ((polyEdges v).map fun e => ‖e.2 - e.1‖).sum := by
            field_simp
          nlinarith [hD, hkey, hε]
  -- conclude
  have : Φ w = polyIntegral (dslope F w) v := by
    rw [hΦdef]
    simp only [if_pos hwU]
  rw [← this, hΦw]

/-- **Cauchy's theorem for closed polygons** (homology form): if a closed polygon in the open set
`U` winds `0` times around every point outside `U`, the integral of a holomorphic function along
it vanishes. -/
theorem polyIntegral_eq_zero_of_polyWinding_eq_zero {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {v : List ℂ} (hv : polyTrace v ⊆ U)
    (hw : ∀ a ∉ U, polyWinding v a = 0) : polyIntegral f v = 0 := by
  rcases v with _ | ⟨p₀, v'⟩
  · simp [polyIntegral, polyEdges]
  -- a vertex of the polygon lies in `U`
  obtain ⟨e, he⟩ : ∃ e, e ∈ polyEdges (p₀ :: v') :=
    List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos (by simp [polyEdges]))
  have hw₀ : e.1 ∈ U := hv (segment_subset_polyTrace he (left_mem_segment ℝ e.1 e.2))
  -- `F z := (z - w₀) f z`, so that `dslope F w₀ = f` on `U`
  have hFd : DifferentiableOn ℂ (fun z => (z - e.1) * f z) U :=
    (differentiableOn_id.sub_const _).mul hf
  have key := polyIntegral_dslope_eq_zero hU hFd hv hw hw₀
  have hds : EqOn (dslope (fun z => (z - e.1) * f z) e.1) f (polyTrace (p₀ :: v')) := by
    intro z hz
    rcases eq_or_ne z e.1 with hze | hne
    · rw [hze, dslope_same]
      have hd : HasDerivAt (fun z => (z - e.1) * f z) (1 * f e.1 + (e.1 - e.1) * deriv f e.1) e.1 :=
        ((hasDerivAt_id' e.1).sub_const e.1).mul (hf.differentiableAt (hU.mem_nhds hw₀)).hasDerivAt
      rw [hd.deriv]
      simp
    · rw [dslope_of_ne _ hne, slope_def_field]
      have hne' : z - e.1 ≠ 0 := sub_ne_zero.2 hne
      rw [sub_self, zero_mul, sub_zero, mul_div_cancel_left₀ _ hne']
  rw [← polyIntegral_congr hds]
  exact key

/-- A holomorphic function whose integrals along all closed polygons in a domain vanish has a
primitive there. -/
theorem exists_primitive_of_polyIntegral_eq_zero {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsConnected U) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h U)
    (hzero : ∀ v : List ℂ, polyTrace v ⊆ U → polyIntegral h v = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧ ∀ z ∈ U, deriv F z = h z := by
  obtain ⟨z₀, hz₀⟩ := hUc.nonempty
  -- every point of `U` is reached from `z₀` by a polygonal path in `U`
  have hreach : ∀ z ∈ U, ∃ l : List ℂ, SegsIn U z₀ l ∧ lastOf z₀ l = z := by
    have hSopen : IsOpen {z | z ∈ U ∧ ∃ l : List ℂ, SegsIn U z₀ l ∧ lastOf z₀ l = z} := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzU, l, hl, hlz⟩
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hzU
      filter_upwards [ball_mem_nhds z hr] with w hw
      refine ⟨hball hw, l ++ [w], ?_, ?_⟩
      · rw [segsIn_append]
        refine ⟨hl, ?_⟩
        simp only [SegsIn, and_true, hlz]
        exact ((convex_ball z r).segment_subset (mem_ball_self hr) hw).trans hball
      · rw [lastOf_append, hlz]
        rfl
    have hVopen : IsOpen (U \ {z | z ∈ U ∧ ∃ l : List ℂ, SegsIn U z₀ l ∧ lastOf z₀ l = z}) := by
      rw [isOpen_iff_mem_nhds]
      rintro z ⟨hzU, hzS⟩
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hzU
      filter_upwards [ball_mem_nhds z hr] with w hw
      refine ⟨hball hw, fun hwS => hzS ⟨hzU, ?_⟩⟩
      obtain ⟨-, l, hl, hlw⟩ := hwS
      refine ⟨l ++ [z], ?_, ?_⟩
      · rw [segsIn_append]
        refine ⟨hl, ?_⟩
        simp only [SegsIn, and_true, hlw]
        exact ((convex_ball z r).segment_subset hw (mem_ball_self hr)).trans hball
      · rw [lastOf_append, hlw]
        rfl
    have hsub : U ⊆ {z | z ∈ U ∧ ∃ l : List ℂ, SegsIn U z₀ l ∧ lastOf z₀ l = z} := by
      refine hUc.isPreconnected.subset_left_of_subset_union hSopen hVopen ?_ ?_ ?_
      · exact Set.disjoint_left.2 fun z hz hz' => hz'.2 hz
      · intro z hz
        by_cases hzS : z ∈ {z | z ∈ U ∧ ∃ l : List ℂ, SegsIn U z₀ l ∧ lastOf z₀ l = z}
        · exact Or.inl hzS
        · exact Or.inr ⟨hz, hzS⟩
      · exact ⟨z₀, hz₀, hz₀, [], trivial, rfl⟩
    intro z hz
    exact (hsub hz).2
  choose! path hpath using hreach
  -- the local formula `F w - F z = ∫_[z,w] h` and the derivative
  have hderiv : ∀ z ∈ U, HasDerivAt (fun z => pathIntFrom h z₀ (path z)) (h z) z := by
    intro z hz
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hz
    have hloc : ∀ w ∈ ball z r,
        pathIntFrom h z₀ (path w) - pathIntFrom h z₀ (path z) = segIntegral h z w := by
      intro w hw
      obtain ⟨hlz, hz'⟩ := hpath z hz
      obtain ⟨hlw, hw'⟩ := hpath w (hball hw)
      have hseg : segment ℝ z w ⊆ U :=
        ((convex_ball z r).segment_subset (mem_ball_self hr) hw).trans hball
      have hrev := pathIntFrom_reverse h z₀ (path w)
      rw [hw'] at hrev
      have hlast := lastOf_reverse z₀ (path w)
      rw [hw'] at hlast
      have hrevseg := segsIn_reverse hlw
      rw [hw'] at hrevseg
      have hpoly := hzero (z₀ :: (path z ++ [w] ++ (z₀ :: path w).reverse.tail)) ?_
      · rw [polyIntegral_cons] at hpoly
        simp only [pathIntFrom_append, lastOf_append, hz', lastOf, pathIntFrom, add_zero] at hpoly
        rw [hrev, hlast, segIntegral_self] at hpoly
        linear_combination -hpoly
      · refine polyTrace_cons_subset ?_ ?_
        · simp only [segsIn_append, lastOf_append, hz', lastOf, SegsIn, and_true]
          exact ⟨⟨hlz, hseg⟩, hrevseg⟩
        · simp only [lastOf_append, hz', lastOf, hlast, segment_same]
          exact singleton_subset_iff.2 hz₀
    rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδh⟩ :=
      Metric.continuousAt_iff.1 (hh.continuousOn.continuousAt (hU.mem_nhds hz)) ε hε
    filter_upwards [ball_mem_nhds z (lt_min hr hδ)] with w hw
    have hwr : w ∈ ball z r := ball_subset_ball (min_le_left _ _) hw
    have hwδ : dist w z < δ := lt_of_lt_of_le (mem_ball.1 hw) (min_le_right _ _)
    simp only [smul_eq_mul]
    rw [hloc w hwr]
    have hsegU : segment ℝ z w ⊆ U :=
      ((convex_ball z r).segment_subset (mem_ball_self hr) hwr).trans hball
    have e : segIntegral h z w - (w - z) * h z = segIntegral (fun ζ => h ζ - h z) z w := by
      rw [segIntegral_sub (hh.continuousOn.mono hsegU) continuousOn_const, segIntegral_const]
      ring
    rw [e]
    refine (norm_segIntegral_le fun ζ hζ => ?_).trans (le_of_eq rfl)
    have hζ : dist ζ z < δ :=
      mem_ball.1 ((convex_ball z δ).segment_subset (mem_ball_self hδ) (mem_ball.2 hwδ) hζ)
    have := hδh hζ
    rw [dist_eq_norm] at this
    exact this.le
  exact ⟨fun z => pathIntFrom h z₀ (path z),
    fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt,
    fun z hz => (hderiv z hz).deriv⟩

/-- **Holomorphic logarithms** on a domain whose complement in `ℂ̄` is connected. -/
theorem exists_log_of_isConnected_compl {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    (hc : IsConnected (toExt U)ᶜ) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (hne : ∀ z ∈ U, g z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧ ∀ z ∈ U, exp (L z) = g z := by
  -- the logarithmic derivative `g'/g` has a primitive `L₀` on `U`
  have hhd : DifferentiableOn ℂ (fun z => deriv g z / g z) U := (hg.deriv hU).div hg hne
  have hzero : ∀ v : List ℂ, polyTrace v ⊆ U → polyIntegral (fun z => deriv g z / g z) v = 0 :=
    fun v hv => polyIntegral_eq_zero_of_polyWinding_eq_zero hU hhd hv
      fun a ha => polyWinding_eq_zero_of_isConnected_compl hc hv ha
  obtain ⟨L₀, hL₀, hL₀'⟩ := exists_primitive_of_polyIntegral_eq_zero hU hUc hhd hzero
  -- `g · exp (-L₀)` has zero derivative, hence is constant on the domain `U`
  have hφ : ∀ z ∈ U, HasDerivAt (fun z => g z * exp (-L₀ z)) 0 z := by
    intro z hz
    have hgz := (hg.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    have hLz := (hL₀.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    have hexp : HasDerivAt (fun z => exp (-L₀ z)) (exp (-L₀ z) * -deriv L₀ z) z := hLz.neg.cexp
    have hmul := hgz.mul hexp
    convert hmul using 1
    rw [hL₀' z hz]
    field_simp [hne z hz]
    ring
  obtain ⟨z₀, hz₀⟩ := hUc.nonempty
  have hconst : ∀ z ∈ U, g z * exp (-L₀ z) = g z₀ * exp (-L₀ z₀) := fun z hz =>
    hU.is_const_of_deriv_eq_zero hUc.isPreconnected
      (fun z hz => (hφ z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hφ z hz).deriv) hz hz₀
  have hc0 : g z₀ * exp (-L₀ z₀) ≠ 0 := mul_ne_zero (hne z₀ hz₀) (exp_ne_zero _)
  refine ⟨fun z => L₀ z + log (g z₀ * exp (-L₀ z₀)), hL₀.add_const _, fun z hz => ?_⟩
  rw [exp_add, exp_log hc0, ← hconst z hz, mul_comm (g z), ← mul_assoc, ← exp_add, add_neg_cancel,
    exp_zero, one_mul]

/-- **The bridge**: a domain whose complement in `ℂ̄` is connected satisfies hypothesis (H) of the
Riemann mapping theorem. -/
theorem hasHolomorphicSqrt_of_isConnected_compl {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsConnected U) (hc : IsConnected (toExt U)ᶜ) : RMT.HasHolomorphicSqrt U := by
  intro g hg hne
  obtain ⟨L, hL, hLg⟩ := exists_log_of_isConnected_compl hU hUc hc hg hne
  refine ⟨fun z => exp (L z / 2), (hL.div_const 2).cexp, fun z hz => ?_⟩
  have h2 : exp (L z / 2) ^ 2 = exp (L z) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h2, hLg z hz]

end LiZhongQC
