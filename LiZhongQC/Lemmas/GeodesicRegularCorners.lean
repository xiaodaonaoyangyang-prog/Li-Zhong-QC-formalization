import LiZhongQC.Lemmas.FiniteGeodesicChain
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real
noncomputable section
namespace LiZhongQC

/-- A nonzero one-sided tangent on an ordered coordinate line has a strictly
positive scalar speed. The time change need only be monotone: differentiability
of that scalar coordinate follows from the smooth spatial curve. -/
theorem s25gb_ordered_chart_tangent {σ : ℝ → ℂ} {ζ : ℂ → ℂ} {θ : ℝ → ℝ}
    {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) {d u w : ℂ}
    (hσ : HasDerivWithinAt σ d (Icc a b) x) (hd : d ≠ 0) (hu : u ≠ 0)
    (hζ : DifferentiableAt ℂ ζ (σ x)) (hζd : deriv ζ (σ x) ≠ 0)
    (hθ : MonotoneOn θ (Icc a b))
    (hline : ∀ t ∈ Icc a b, ζ (σ t) = w + (θ t : ℂ) * u) :
    ∃ r : ℝ, 0 < r ∧ deriv ζ (σ x) * d = (r : ℂ) * u := by
  let r : ℝ := (d * deriv ζ (σ x) / u).re
  have hc : HasDerivWithinAt (fun t => ζ (σ t)) (d * deriv ζ (σ x)) (Icc a b) x := by
    simpa only [Function.comp_def, smul_eq_mul] using
      hζ.hasDerivAt.scomp_hasDerivWithinAt x hσ
  have hr : HasDerivWithinAt (fun t => ((ζ (σ t) - w) / u).re) r (Icc a b) x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt x ((hc.sub_const w).div_const u)
  have heθ : ∀ t ∈ Icc a b, θ t = ((ζ (σ t) - w) / u).re := by
    intro t ht
    rw [hline t ht]
    simp [hu]
  have hθd : HasDerivWithinAt θ r (Icc a b) x := hr.congr_of_mem heθ hx
  have hr0 : 0 ≤ r := by
    rw [← hθd.derivWithin (uniqueDiffOn_Icc hab x hx)]
    exact hθ.derivWithin_nonneg
  have hlineD : HasDerivWithinAt (fun t => w + (θ t : ℂ) * u) ((r : ℂ) * u) (Icc a b) x :=
    (hθd.ofReal_comp.mul_const u).const_add w
  have hsame : HasDerivWithinAt (fun t => ζ (σ t)) ((r : ℂ) * u) (Icc a b) x :=
    hlineD.congr_of_mem hline hx
  have he : d * deriv ζ (σ x) = (r : ℂ) * u :=
    (hc.derivWithin (uniqueDiffOn_Icc hab x hx)).symm.trans
      (hsame.derivWithin (uniqueDiffOn_Icc hab x hx))
  have hrne : r ≠ 0 := by
    intro hrz
    rw [hrz, Complex.ofReal_zero, zero_mul] at he
    exact mul_ne_zero hd hζd he
  have hrpos : 0 < r := by
    rcases eq_or_lt_of_le hr0 with hrz | hrpos
    · exact False.elim (hrne hrz.symm)
    · exact hrpos
  exact ⟨r, hrpos, by simpa [mul_comm] using he⟩

/-- Regular geodesic charts orient every smooth representative of an ordered
subinterval in the same direction. This includes one-sided endpoint derivatives
at artificial subdivision vertices. The representative's time map may be
nondifferentiable. -/
theorem s25gb_regular_tangent_window {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) {γ : LRCurve}
    (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (hz : φ (γ.toFun t₀) ≠ 0) :
    ∃ δ > 0, ∃ (ζ : ℂ → ℂ) (u : ℂ), u ≠ 0 ∧
      ∀ (σ : ℝ → ℂ) (p : ℝ → ℝ),
        ContDiffOn ℝ 1 σ (Icc 0 1) → MonotoneOn p (Icc (0 : ℝ) 1) →
        (∀ t ∈ Icc (0 : ℝ) 1, p t ∈ Icc (0 : ℝ) 1 ∧ t₀ - δ < p t ∧ p t < t₀ + δ) →
        (∀ t ∈ Icc (0 : ℝ) 1, σ t = γ.toFun (p t)) →
        ∀ x ∈ Icc (0 : ℝ) 1, derivWithin σ (Icc 0 1) x ≠ 0 →
          deriv ζ (σ x) ≠ 0 ∧
          ∃ r : ℝ, 0 < r ∧ deriv ζ (σ x) * derivWithin σ (Icc 0 1) x = (r : ℂ) * u := by
  obtain ⟨δ, hδ, ζ, ψ, W, u, hu, hW, hWD, han, hinj, hopen, hψ, hwin, hrel⟩ :=
    s25g_local isOpen_ball hφ hγ hp ht₀ hz
  have hu0 : u ≠ 0 := by
    intro he
    rw [he, norm_zero] at hu
    exact zero_ne_one hu
  refine ⟨δ, hδ, ζ, u, hu0, ?_⟩
  intro σ p hσ hpm hpi heq x hx hd
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hσW : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈ W := by
    intro t ht
    rw [heq t ht]
    exact hwin _ (hpi t ht).1 (hpi t ht).2.1 (hpi t ht).2.2
  have hdζ := (han _ (hσW x hx)).2.2
  refine ⟨hdζ, ?_⟩
  let θ : ℝ → ℝ := fun t => ((ζ (σ t) - ζ (σ 0)) / u).re
  have hsegment : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s ≤ t →
      ζ (σ t) - ζ (σ s) = u * ((phiSegmentLength φ γ (p s) (p t)).toReal : ℂ) := by
    intro s hs t ht hst
    rw [heq s hs, heq t ht]
    exact hrel _ (hpi s hs).1 _ (hpi t ht).1 (hpi s hs).2.1
      (hpm hs ht hst) (hpi t ht).2.2
  have hline : ∀ t ∈ Icc (0 : ℝ) 1,
      ζ (σ t) = ζ (σ 0) + (θ t : ℂ) * u := by
    intro t ht
    have he := hsegment 0 h0 t ht ht.1
    have hθt : θ t = (phiSegmentLength φ γ (p 0) (p t)).toReal := by
      dsimp [θ]
      rw [he]
      simp [hu0]
    rw [hθt]
    linear_combination he
  have hθm : MonotoneOn θ (Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    have he := hsegment s hs t ht hst
    have hθdiff : θ t - θ s = ((ζ (σ t) - ζ (σ s)) / u).re := by
      dsimp [θ]
      rw [← Complex.sub_re, ← sub_div]
      congr 2
      ring
    rw [he] at hθdiff
    have hr : θ t - θ s = (phiSegmentLength φ γ (p s) (p t)).toReal := by
      simpa [hu0] using hθdiff
    have := ENNReal.toReal_nonneg (a := phiSegmentLength φ γ (p s) (p t))
    linarith
  exact s25gb_ordered_chart_tangent zero_lt_one hx
    (fx_p2_hasDerivWithinAt_of_contDiffOn hσ x hx) hd hu0
    (han _ (hσW x hx)).1.differentiableAt hdζ hθm hline

/-- Two positive tangents in one regular natural coordinate make a straight
angle at their join. The shared conformal derivative cancels exactly. -/
theorem s25gb_regular_tangent_ratio {lam u d₁ d₂ : ℂ} {r₁ r₂ : ℝ}
    (hlam : lam ≠ 0) (hu : u ≠ 0) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h₁ : lam * d₁ = (r₁ : ℂ) * u) (h₂ : lam * d₂ = (r₂ : ℂ) * u) :
    arg (-d₁ / d₂) = Real.pi := by
  have hr₂c : (r₂ : ℂ) ≠ 0 := by exact_mod_cast hr₂.ne'
  have hd₂ : d₂ ≠ 0 := by
    intro he
    rw [he, mul_zero] at h₂
    exact mul_ne_zero hr₂c hu h₂.symm
  have he : -d₁ / d₂ = ((-r₁ / r₂ : ℝ) : ℂ) := by
    have he₁ : d₁ = (r₁ : ℂ) * u / lam :=
      (eq_div_iff hlam).2 (by simpa only [mul_comm] using h₁)
    have he₂ : d₂ = (r₂ : ℂ) * u / lam :=
      (eq_div_iff hlam).2 (by simpa only [mul_comm] using h₂)
    rw [he₁, he₂]
    push_cast
    field_simp <;> ring
  rw [he]
  exact Complex.arg_ofReal_of_neg (div_neg_of_neg_of_pos (neg_neg_of_pos hr₁) hr₂)

/-- A regular artificial vertex is blunt as soon as its two increasing side
representatives lie in the same regular tangent window. -/
theorem s25gb_regular_join_blunt {φ : ℂ → ℂ} {n : ℕ} [NeZero n]
    {side : Fin n → ℝ → ℂ} (j : Fin n)
    (hord : meromorphicOrderAt φ (side j 0) = (0 : ℤ))
    {lam u : ℂ} {r₁ r₂ : ℝ} (hlam : lam ≠ 0) (hu : u ≠ 0)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h₁ : lam * derivWithin (side (j - 1)) (Icc 0 1) 1 = (r₁ : ℂ) * u)
    (h₂ : lam * derivWithin (side j) (Icc 0 1) 0 = (r₂ : ℂ) * u) :
    fx_IsBlunt φ side j ∧
      arg (-derivWithin (side (j - 1)) (Icc 0 1) 1 / derivWithin (side j) (Icc 0 1) 0) ≠ 0 := by
  have harg := s25gb_regular_tangent_ratio hlam hu hr₁ hr₂ h₁ h₂
  refine ⟨s25gb_blunt_of_angle j 0 hord ?_ ?_, ?_⟩
  · rw [harg, abs_of_pos Real.pi_pos]
    norm_num
  · rw [harg, abs_of_pos Real.pi_pos]
    norm_num
    linarith
  · rw [harg]
    exact Real.pi_ne_zero

/-- Two radial outgoing arms with equal unit direction meet before either
endpoint. Hence disjoint extracted interiors force different directions. -/
theorem s25gb_radial_directions_ne {ψ : ℂ → ℂ} {u v : ℂ} {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B)
    (hdisj : ∀ s ∈ Ioo (0 : ℝ) A, ∀ t ∈ Ioo (0 : ℝ) B,
      ψ ((s : ℂ) * u) ≠ ψ ((t : ℂ) * v)) : u ≠ v := by
  intro he
  let r : ℝ := min A B / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrA : r < A := by dsimp [r]; linarith [min_le_left A B]
  have hrB : r < B := by dsimp [r]; linarith [min_le_right A B]
  exact hdisj r ⟨hr, hrA⟩ r ⟨hr, hrB⟩ (by rw [he])

/-- Unit directions with a zero quotient argument coincide. -/
theorem s25gb_unit_direction_of_arg {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (harg : arg (u / v) = 0) : u = v := by
  have hv0 : v ≠ 0 := by intro he; simpa [he] using hv
  have hnorm : ‖u / v‖ = 1 := by rw [norm_div, hu, hv, div_self one_ne_zero]
  have he : u / v = 1 := by
    have h := Complex.norm_mul_exp_arg_mul_I (u / v)
    simpa only [hnorm, harg, Complex.ofReal_one, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, mul_one] using h.symm
  exact (div_eq_one_iff_eq hv0).1 he

/-- The local no-cusp obstruction at a zero: disjoint radial arms cannot
have zero angle. This uses geometric radial identities, not an assumed angle. -/
theorem s25gb_radial_no_cusp {ψ : ℂ → ℂ} {u v : ℂ} {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hdisj : ∀ s ∈ Ioo (0 : ℝ) A, ∀ t ∈ Ioo (0 : ℝ) B,
      ψ ((s : ℂ) * u) ≠ ψ ((t : ℂ) * v)) : arg (u / v) ≠ 0 := by
  intro he
  exact s25gb_radial_directions_ne hA hB hdisj (s25gb_unit_direction_of_arg hu hv he)

/-- Nonzero conformal factors and positive parametrization speeds preserve
the outgoing angle. Thus the radial no-cusp conclusion is a statement about
the actual one-sided physical tangents, not only coordinate directions. -/
theorem s25gb_radial_tangent_no_cusp {ψ : ℂ → ℂ} {u v lam d₁ d₂ : ℂ}
    {A B r₁ r₂ : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hlam : lam ≠ 0)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hd₁ : d₁ = (r₁ : ℂ) * lam * u) (hd₂ : d₂ = (r₂ : ℂ) * lam * v)
    (hdisj : ∀ s ∈ Ioo (0 : ℝ) A, ∀ t ∈ Ioo (0 : ℝ) B,
      ψ ((s : ℂ) * u) ≠ ψ ((t : ℂ) * v)) : arg (d₁ / d₂) ≠ 0 := by
  have hv0 : v ≠ 0 := by intro he; simpa [he] using hv
  have hr₂c : (r₂ : ℂ) ≠ 0 := by exact_mod_cast hr₂.ne'
  have he : d₁ / d₂ = ((r₁ / r₂ : ℝ) : ℂ) * (u / v) := by
    rw [hd₁, hd₂]
    push_cast
    field_simp <;> ring
  rw [he, Complex.arg_real_mul _ (div_pos hr₁ hr₂)]
  exact s25gb_radial_no_cusp hA hB hu hv hdisj

end LiZhongQC

