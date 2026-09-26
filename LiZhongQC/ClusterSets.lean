import LiZhongQC.Lemmas.Caratheodory

/-!
# The Schwarz reflection principle, the Hahn–Mazurkiewicz theorem and cluster sets

Three tools behind Carathéodory's theorem (`LiZhongQC.Lemmas.Caratheodory`, from `LZ3.txt`):
* §1 the Schwarz reflection principle (segment, harmonic and circular-arc versions), and the
  consequence used in Step 4 of Theorem C2 (`eqOn_const_of_eqOn_const_on_arc`);
* §2 the Hahn–Mazurkiewicz theorem and the form used in Theorem C1;
* §3 cluster sets (full, radial, along a curve, angular, boundary), continuity criteria, Lindelöf's
  theorem, the Iversen–Gross theorem, and Carathéodory's prime-end theorem in cluster-set form.

## Adaptation to this project

This file was a standalone skeleton (namespace `RMT`, its own `disc`, closures in `ℂ`).  It now
uses the project's conventions: namespace `LiZhongQC`; the disc is `unitDisc`; the cluster set is
`clusterSet f unitDisc ζ` from `Lemmas/Caratheodory.lean` (the skeleton's filter form is
`clusterSet_unitDisc_eq_mapClusterPt`); prime ends, impressions and principal points are those of
that file; `Complex.abs` is `‖·‖`, `QuotientMap` is `Topology.IsQuotientMap`, harmonicity is
Mathlib's `InnerProductSpace.HarmonicOnNhd`.

Statements corrected because they were false as written (counterexample in brackets):
* `schwarz_reflection_harmonic`: the odd extension is `0` on the real axis (the skeleton kept the
  arbitrary values of `v` there: `v = 0` off the axis, `v = 1` on it).
* `IsCircleSymmetricNbhd` now requires `U ∩ ∂Δ = A` (`U` could meet the circle outside `A`, where
  `f` need not extend: `sin (i (z + ζ₁)/(z - ζ₁))`, `ζ₁ ∉ A`); this also makes `A` relatively open.
* `schwarz_reflection_arc_abs_one` (now `schwarz_reflection_arc_norm_one`) gives the extension on some
  neighbourhood of `A` only (the reflection `1/(f(1/z*))*` has poles at reflected zeros of `f`:
  a Blaschke factor with its zero in `U`).
* `frontier_locallyConnected_iff_isCurve` assumes `Ω` is a conformal image of the disc (the annulus
  `1 < |z| < 2` has locally connected but disconnected boundary).
* `clusterSet_subsingleton_iff_continuous_extension` assumes `f` continuous on `Δ` and `ζ ∈ ∂Δ`
  (otherwise `f` can be discontinuous away from `ζ`, and for `ζ` outside the closed disc the
  cluster set is empty while the extension exists).
* `lindelof` takes a curve `γ` ending at `ζ` with `f ∘ γ → a` (the skeleton allowed any set with
  `ζ` in its closure: `exp (i log (1 - z))` is `1` at `tₙ` with `log (1 - tₙ) ∈ 2πℤ` but has no
  angular limit at `1`).
* `iversen_gross` assumes `ζ ∈ ∂Δ` (at an interior point the boundary cluster set is empty).
-/

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ## §1. The Schwarz reflection principle -/

section SchwarzReflection

/-- Reflection of a set in the real axis: `S* = { z* : z ∈ S }`. -/
def conjSet (S : Set ℂ) : Set ℂ := conj '' S

/-- `Ω` is open and symmetric about the real axis. -/
structure IsRealSymmetric (Ω : Set ℂ) : Prop where
  isOpen : IsOpen Ω
  conj_eq : conjSet Ω = Ω

/-- `Ω⁺ = Ω ∩ {Im z > 0}`. -/
def upperPart (Ω : Set ℂ) : Set ℂ := {z ∈ Ω | 0 < z.im}

/-- `Ω⁻ = Ω ∩ {Im z < 0}`. -/
def lowerPart (Ω : Set ℂ) : Set ℂ := {z ∈ Ω | z.im < 0}

/-- `σ = Ω ∩ ℝ`. -/
def realPart (Ω : Set ℂ) : Set ℂ := {z ∈ Ω | z.im = 0}

theorem upper_union_real_union_lower (Ω : Set ℂ) :
    upperPart Ω ∪ realPart Ω ∪ lowerPart Ω = Ω := by
  ext z
  simp only [upperPart, realPart, lowerPart, mem_union, mem_setOf_eq]
  constructor
  · rintro ((h | h) | h) <;> exact h.1
  · intro hz
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact Or.inr ⟨hz, h⟩
    · exact Or.inl (Or.inr ⟨hz, h⟩)
    · exact Or.inl (Or.inl ⟨hz, h⟩)

/-- The reflected extension `F z = f z` on `Ω⁺ ∪ σ`, `F z = (f z*)*` on `Ω⁻`. -/
def reflectExtend (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => if 0 ≤ z.im then f z else conj (f (conj z))

theorem reflectExtend_eq_of_im_nonneg (f : ℂ → ℂ) {z : ℂ} (hz : 0 ≤ z.im) :
    reflectExtend f z = f z := by
  show (if 0 ≤ z.im then f z else conj (f (conj z))) = f z
  exact if_pos hz

theorem reflectExtend_eq_of_im_neg (f : ℂ → ℂ) {z : ℂ} (hz : z.im < 0) :
    reflectExtend f z = conj (f (conj z)) := by
  show (if 0 ≤ z.im then f z else conj (f (conj z))) = conj (f (conj z))
  exact if_neg (not_le.2 hz)

/-! ### Cauchy's theorem for a rectangle cut by the real axis -/

theorem mem_uIcc_of_mem_Ioo_min_max {a b x : ℝ} (h : x ∈ Ioo (min a b) (max a b)) :
    x ∈ uIcc a b := by
  rw [← Icc_min_max]
  exact Ioo_subset_Icc_self h

/-- **Cauchy's theorem for a rectangle, for a function holomorphic off the real axis.**  If `F` is
continuous on the closed rectangle and complex differentiable at every point of the open rectangle
off the real axis, its boundary integral vanishes.  (Proof machinery for Schwarz reflection: cut
the rectangle along the axis and apply Cauchy's theorem to the two pieces.) -/
theorem integral_boundary_rect_eq_zero_of_differentiableAt_off_real_axis (F : ℂ → ℂ) (z w : ℂ)
    (Hc : ContinuousOn F (uIcc z.re w.re ×ℂ uIcc z.im w.im))
    (Hd : ∀ p ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im),
      p.im ≠ 0 → DifferentiableAt ℂ F p) :
    (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, F (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, F (re z + y * I)) = 0 := by
  by_cases h0 : (0 : ℝ) ∈ Ioo (min z.im w.im) (max z.im w.im)
  · -- cut the rectangle along the real axis
    have h0' : (0 : ℝ) ∈ uIcc z.im w.im := mem_uIcc_of_mem_Ioo_min_max h0
    -- the vertical sides are integrable on subintervals
    have hvert : ∀ a : ℝ, a ∈ uIcc z.re w.re → ∀ b c : ℝ, b ∈ uIcc z.im w.im →
        c ∈ uIcc z.im w.im → IntervalIntegrable (fun y : ℝ => F (a + y * I)) MeasureTheory.volume b c := by
      intro a ha b c hb hc
      refine ContinuousOn.intervalIntegrable ?_
      refine Hc.comp (by fun_prop : Continuous fun y : ℝ => (a : ℂ) + y * I).continuousOn ?_
      intro y hy
      refine mem_reProdIm.2 ⟨?_, ?_⟩
      · simpa using ha
      · simpa using uIcc_subset_uIcc hb hc hy
    -- the piece below the axis: corners `z` and `(w.re, 0)`
    have h1 : (∫ x : ℝ in z.re..w.re, F (x + z.im * I)) -
        (∫ x : ℝ in z.re..w.re, F (x + (0 : ℝ) * I)) +
        I • (∫ y : ℝ in z.im..(0 : ℝ), F (re w + y * I)) -
        I • (∫ y : ℝ in z.im..(0 : ℝ), F (re z + y * I)) = 0 := by
      refine Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F z
        ⟨w.re, 0⟩ ?_ ?_
      · show ContinuousOn F (uIcc z.re w.re ×ℂ uIcc z.im 0)
        refine Hc.mono ?_
        intro p hp
        obtain ⟨hp1, hp2⟩ := mem_reProdIm.1 hp
        exact mem_reProdIm.2 ⟨hp1, uIcc_subset_uIcc left_mem_uIcc h0' hp2⟩
      · show DifferentiableOn ℂ F
          (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im 0) (max z.im 0))
        intro p hp
        obtain ⟨hp1, hp2⟩ := mem_reProdIm.1 hp
        refine (Hd p (mem_reProdIm.2 ⟨hp1, Ioo_subset_Ioo (le_min (min_le_left _ _) h0.1.le)
          (max_le (le_max_left _ _) h0.2.le) hp2⟩) ?_).differentiableWithinAt
        intro hp0
        rw [hp0] at hp2
        rcases min_lt_iff.1 hp2.1 with h | h <;> rcases lt_max_iff.1 hp2.2 with h' | h' <;>
          linarith
    -- the piece above the axis: corners `(z.re, 0)` and `w`
    have h2 : (∫ x : ℝ in z.re..w.re, F (x + (0 : ℝ) * I)) -
        (∫ x : ℝ in z.re..w.re, F (x + w.im * I)) +
        I • (∫ y : ℝ in (0 : ℝ)..w.im, F (re w + y * I)) -
        I • (∫ y : ℝ in (0 : ℝ)..w.im, F (re z + y * I)) = 0 := by
      refine Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F
        ⟨z.re, 0⟩ w ?_ ?_
      · show ContinuousOn F (uIcc z.re w.re ×ℂ uIcc 0 w.im)
        refine Hc.mono ?_
        intro p hp
        obtain ⟨hp1, hp2⟩ := mem_reProdIm.1 hp
        exact mem_reProdIm.2 ⟨hp1, uIcc_subset_uIcc h0' right_mem_uIcc hp2⟩
      · show DifferentiableOn ℂ F
          (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min 0 w.im) (max 0 w.im))
        intro p hp
        obtain ⟨hp1, hp2⟩ := mem_reProdIm.1 hp
        refine (Hd p (mem_reProdIm.2 ⟨hp1, Ioo_subset_Ioo (le_min h0.1.le (min_le_right _ _))
          (max_le h0.2.le (le_max_right _ _)) hp2⟩) ?_).differentiableWithinAt
        intro hp0
        rw [hp0] at hp2
        rcases min_lt_iff.1 hp2.1 with h | h <;> rcases lt_max_iff.1 hp2.2 with h' | h' <;>
          linarith
    -- join the vertical sides and add the two pieces
    have hv1 : (∫ y : ℝ in z.im..(0 : ℝ), F (re w + y * I)) +
        (∫ y : ℝ in (0 : ℝ)..w.im, F (re w + y * I)) =
          ∫ y : ℝ in z.im..w.im, F (re w + y * I) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hvert w.re right_mem_uIcc _ _ left_mem_uIcc h0')
        (hvert w.re right_mem_uIcc _ _ h0' right_mem_uIcc)
    have hv2 : (∫ y : ℝ in z.im..(0 : ℝ), F (re z + y * I)) +
        (∫ y : ℝ in (0 : ℝ)..w.im, F (re z + y * I)) =
          ∫ y : ℝ in z.im..w.im, F (re z + y * I) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hvert z.re left_mem_uIcc _ _ left_mem_uIcc h0')
        (hvert z.re left_mem_uIcc _ _ h0' right_mem_uIcc)
    rw [← hv1, ← hv2]
    simp only [smul_eq_mul] at h1 h2 ⊢
    linear_combination h1 + h2
  · -- the open rectangle misses the axis: one application of Cauchy's theorem
    refine Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn F z w Hc ?_
    intro p hp
    refine (Hd p hp fun hp0 => h0 ?_).differentiableWithinAt
    rw [← hp0]
    exact (mem_reProdIm.1 hp).2

/-- **Schwarz reflection, real-segment version.**  `f` holomorphic on `Ω⁺`, continuous on
`Ω⁺ ∪ σ` and real on `σ` ⟹ `reflectExtend f` is holomorphic on `Ω`. -/
theorem schwarz_reflection_segment {Ω : Set ℂ} (hΩ : IsRealSymmetric Ω) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (upperPart Ω))
    (hcont : ContinuousOn f (upperPart Ω ∪ realPart Ω))
    (hreal : ∀ z ∈ realPart Ω, (f z).im = 0) :
    DifferentiableOn ℂ (reflectExtend f) Ω := by
  -- symmetry of `Ω` and openness of the half-planes
  have hconj : ∀ z ∈ Ω, conj z ∈ Ω := fun z hz => by
    have h : conj z ∈ conjSet Ω := mem_image_of_mem conj hz
    rwa [hΩ.conj_eq] at h
  have hUo : IsOpen (upperPart Ω) := hΩ.isOpen.inter (isOpen_lt continuous_const continuous_im)
  have hLo : IsOpen {z : ℂ | z.im < 0} := isOpen_lt continuous_im continuous_const
  have hPo : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im
  -- the two descriptions of the extension on the closed half-planes
  have hFup : ∀ z : ℂ, 0 ≤ z.im → reflectExtend f z = f z := fun z hz =>
    reflectExtend_eq_of_im_nonneg f hz
  have hFlow : ∀ z ∈ Ω, z.im ≤ 0 → reflectExtend f z = conj (f (conj z)) := by
    intro z hz hz0
    rcases hz0.lt_or_eq with h | h
    · exact reflectExtend_eq_of_im_neg f h
    · rw [hFup z h.ge, Complex.conj_eq_iff_im.2 h, Complex.conj_eq_iff_im.2 (hreal z ⟨hz, h⟩)]
  -- complex differentiability off the real axis
  have hdiffA : ∀ z ∈ Ω, z.im ≠ 0 → DifferentiableAt ℂ (reflectExtend f) z := by
    intro z hz hz0
    rcases lt_or_gt_of_ne hz0 with h | h
    · have hcz : conj z ∈ upperPart Ω := ⟨hconj z hz, by rw [Complex.conj_im]; linarith⟩
      have hd : DifferentiableAt ℂ (conj ∘ f ∘ conj) z :=
        differentiableAt_conj_conj_iff.2 (hf.differentiableAt (hUo.mem_nhds hcz))
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [hLo.mem_nhds (show z ∈ {z : ℂ | z.im < 0} from h)] with y hy
      exact reflectExtend_eq_of_im_neg f hy
    · have hzU : z ∈ upperPart Ω := ⟨hz, h⟩
      refine (hf.differentiableAt (hUo.mem_nhds hzU)).congr_of_eventuallyEq ?_
      filter_upwards [hPo.mem_nhds (show z ∈ {z : ℂ | 0 < z.im} from h)] with y hy
      exact reflectExtend_eq_of_im_nonneg f (le_of_lt hy)
  -- continuity on `Ω`
  have hcontF : ContinuousOn (reflectExtend f) Ω := by
    intro z hz
    rcases lt_trichotomy z.im 0 with h | h | h
    · -- below the axis: `reflectExtend f = conj ∘ f ∘ conj` near `z`
      have hcz : conj z ∈ upperPart Ω := ⟨hconj z hz, by rw [Complex.conj_im]; linarith⟩
      have h1 : ContinuousAt f (conj z) :=
        hcont.continuousAt (mem_of_superset (hUo.mem_nhds hcz) subset_union_left)
      have hc : ContinuousAt (conj ∘ f ∘ conj) z :=
        continuous_conj.continuousAt.comp (h1.comp continuous_conj.continuousAt)
      refine (hc.congr_of_eventuallyEq ?_).continuousWithinAt
      filter_upwards [hLo.mem_nhds (show z ∈ {z : ℂ | z.im < 0} from h)] with y hy
      exact reflectExtend_eq_of_im_neg f hy
    · -- on the axis: glue the two closed half-planes
      have hzr : z ∈ realPart Ω := ⟨hz, h⟩
      refine (ContinuousWithinAt.union (s := Ω ∩ {y : ℂ | 0 ≤ y.im})
        (t := Ω ∩ {y : ℂ | y.im ≤ 0}) ?_ ?_).mono fun y hy => ?_
      · -- the closed upper half, where `reflectExtend f = f`
        have h1 : ContinuousWithinAt f (Ω ∩ {y : ℂ | 0 ≤ y.im}) z := by
          refine (hcont z (mem_union_right _ hzr)).mono ?_
          rintro y ⟨hy, hy0⟩
          have hy0' : 0 ≤ y.im := hy0
          rcases lt_or_eq_of_le hy0' with h' | h'
          · exact Or.inl ⟨hy, h'⟩
          · exact Or.inr ⟨hy, h'.symm⟩
        exact h1.congr (fun y hy => hFup y hy.2) (hFup z h.ge)
      · -- the closed lower half, where `reflectExtend f = conj ∘ f ∘ conj`
        have hmaps : MapsTo conj (Ω ∩ {y : ℂ | y.im ≤ 0}) (upperPart Ω ∪ realPart Ω) := by
          rintro y ⟨hy, hy0⟩
          have hy0' : y.im ≤ 0 := hy0
          have h0 : 0 ≤ (conj y).im := by rw [Complex.conj_im]; linarith
          rcases lt_or_eq_of_le h0 with h' | h'
          · exact Or.inl ⟨hconj y hy, h'⟩
          · exact Or.inr ⟨hconj y hy, h'.symm⟩
        have hcz : conj z ∈ upperPart Ω ∪ realPart Ω := hmaps ⟨hz, h.le⟩
        have h1 : ContinuousWithinAt (conj ∘ f ∘ conj) (Ω ∩ {y : ℂ | y.im ≤ 0}) z :=
          continuous_conj.continuousAt.comp_continuousWithinAt
            ((hcont (conj z) hcz).comp continuous_conj.continuousWithinAt hmaps)
        exact h1.congr (fun y hy => hFlow y hy.1 hy.2) (hFlow z hz h.le)
      · rcases le_total 0 y.im with h' | h'
        · exact Or.inl ⟨hy, h'⟩
        · exact Or.inr ⟨hy, h'⟩
    · -- above the axis: `reflectExtend f = f` near `z`
      have hzU : z ∈ upperPart Ω := ⟨hz, h⟩
      have h1 : ContinuousAt f z :=
        hcont.continuousAt (mem_of_superset (hUo.mem_nhds hzU) subset_union_left)
      refine (h1.congr_of_eventuallyEq ?_).continuousWithinAt
      filter_upwards [hPo.mem_nhds (show z ∈ {z : ℂ | 0 < z.im} from h)] with y hy
      exact reflectExtend_eq_of_im_nonneg f (le_of_lt hy)
  -- Morera: the rectangle integrals vanish
  have hcons : IsConservativeOn (reflectExtend f) Ω := by
    intro z w hzw
    have hrect : uIcc z.re w.re ×ℂ uIcc z.im w.im ⊆ Ω := hzw
    rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
    refine integral_boundary_rect_eq_zero_of_differentiableAt_off_real_axis (reflectExtend f) z w
      (hcontF.mono hrect) ?_
    intro p hp hp0
    obtain ⟨hp1, hp2⟩ := mem_reProdIm.1 hp
    exact hdiffA p (hrect (mem_reProdIm.2 ⟨mem_uIcc_of_mem_Ioo_min_max hp1,
      mem_uIcc_of_mem_Ioo_min_max hp2⟩)) hp0
  exact (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hΩ.isOpen).1 ⟨hcons, hcontF⟩

/-- Odd reflection of a real function across the real axis, `0` on the axis. -/
def reflectExtendOdd (v : ℂ → ℝ) : ℂ → ℝ :=
  fun z => if 0 < z.im then v z else if z.im = 0 then 0 else -v (conj z)

/-! ### The maximum principle for harmonic functions -/

/-- A real harmonic function is locally constant at a local maximum (the maximum modulus principle
applied to `exp ∘ F`, where `F` is a local holomorphic function with real part `u`). -/
theorem eventually_eq_of_harmonicAt_of_isLocalMax {u : ℂ → ℝ} {c : ℂ}
    (hu : ∀ᶠ z in 𝓝 c, InnerProductSpace.HarmonicAt u z) (hc : IsLocalMax u c) :
    ∀ᶠ y in 𝓝 c, u y = u c := by
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.mem_nhds_iff.1 (hu : {z | InnerProductSpace.HarmonicAt u z} ∈ 𝓝 c)
  obtain ⟨F, hF, hFu⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
    (fun y hy => hball hy)
  have hnorm : ∀ z ∈ ball c ρ, ‖Complex.exp (F z)‖ = Real.exp (u z) := by
    intro z hz
    rw [Complex.norm_exp]
    exact congrArg Real.exp (hFu hz)
  have hd : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ (fun z => Complex.exp (F z)) z := by
    filter_upwards [ball_mem_nhds c hρ] with z hz
    exact (hF z hz).differentiableAt.cexp
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (F z)) c := by
    have hc' : ∀ᶠ z in 𝓝 c, u z ≤ u c := hc
    show ∀ᶠ z in 𝓝 c, (norm ∘ fun z => Complex.exp (F z)) z ≤
      (norm ∘ fun z => Complex.exp (F z)) c
    filter_upwards [ball_mem_nhds c hρ, hc'] with z hz hzc
    show ‖Complex.exp (F z)‖ ≤ ‖Complex.exp (F c)‖
    rw [hnorm z hz, hnorm c (mem_ball_self hρ)]
    exact Real.exp_le_exp.2 hzc
  filter_upwards [Complex.norm_eventually_eq_of_isLocalMax hd hmax, ball_mem_nhds c hρ]
    with y hy hyb
  rw [hnorm y hyb, hnorm c (mem_ball_self hρ)] at hy
  exact Real.exp_eq_exp.1 hy

/-- **Maximum principle.**  A harmonic function on a bounded connected open set which tends to `0`
at every boundary point is nonpositive. -/
theorem le_zero_of_harmonicOnNhd_of_tendsto_frontier {U : Set ℂ} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : IsPreconnected U) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hbd : ∀ ζ ∈ frontier U, Tendsto u (𝓝[U] ζ) (𝓝 0)) :
    ∀ z ∈ U, u z ≤ 0 := by
  classical
  -- the extension of `u` by `0` to the closure
  set ũ : ℂ → ℝ := fun z => if z ∈ U then u z else 0 with hũ
  have hũU : ∀ z ∈ U, ũ z = u z := fun z hz => by simp [hũ, hz]
  have hũF : ∀ z ∈ frontier U, ũ z = 0 := by
    intro z hz
    rw [hUo.frontier_eq] at hz
    simp [hũ, hz.2]
  have hcont : ContinuousOn ũ (closure U) := by
    intro z hz
    by_cases hzU : z ∈ U
    · have h1 : ContinuousAt u z := (HarmonicAt.analyticAt (hu z hzU)).continuousAt
      have h2 : ũ =ᶠ[𝓝 z] u := by
        filter_upwards [hUo.mem_nhds hzU] with y hy
        exact hũU y hy
      exact (h1.congr_of_eventuallyEq h2).continuousWithinAt
    · have hzF : z ∈ frontier U := by
        rw [hUo.frontier_eq]
        exact ⟨hz, hzU⟩
      have hsplit : closure U ⊆ U ∪ (closure U \ U) := fun y hy => by
        by_cases h : y ∈ U
        · exact Or.inl h
        · exact Or.inr ⟨hy, h⟩
      show Tendsto ũ (𝓝[closure U] z) (𝓝 (ũ z))
      rw [hũF z hzF]
      refine Tendsto.mono_left ?_ (nhdsWithin_mono _ hsplit)
      rw [nhdsWithin_union]
      refine Tendsto.sup ?_ ?_
      · exact (hbd z hzF).congr' (eventually_nhdsWithin_of_forall fun y hy => (hũU y hy).symm)
      · refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
        simp [hũ, hy.2]
  rcases U.eq_empty_or_nonempty with hU | hUne
  · intro z hz
    rw [hU] at hz
    exact absurd hz (notMem_empty z)
  have hcpt : IsCompact (closure U) := hUb.isCompact_closure
  obtain ⟨c, hcU, hcmax⟩ := hcpt.exists_isMaxOn hUne.closure hcont
  have hcmax' : ∀ y ∈ closure U, ũ y ≤ ũ c := isMaxOn_iff.1 hcmax
  by_contra hcon
  simp only [not_forall, not_le] at hcon
  obtain ⟨z₀, hz₀, hz₀pos⟩ := hcon
  have hM : 0 < ũ c := by
    have := hcmax' z₀ (subset_closure hz₀)
    rw [hũU z₀ hz₀] at this
    exact lt_of_lt_of_le hz₀pos this
  -- the maximum is attained at an interior point
  have hcU' : c ∈ U := by
    by_contra h
    have hcF : c ∈ frontier U := by
      rw [hUo.frontier_eq]
      exact ⟨hcU, h⟩
    rw [hũF c hcF] at hM
    exact lt_irrefl _ hM
  -- the set where the maximum is attained is open
  have hSo : IsOpen {z ∈ U | u z = ũ c} := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hloc : IsLocalMax u z := by
      show ∀ᶠ y in 𝓝 z, u y ≤ u z
      filter_upwards [hUo.mem_nhds hz.1] with y hy
      rw [hz.2, ← hũU y hy]
      exact hcmax' y (subset_closure hy)
    have hev := eventually_eq_of_harmonicAt_of_isLocalMax
      (Filter.eventually_of_mem (hUo.mem_nhds hz.1) fun y hy => hu y hy) hloc
    filter_upwards [hev, hUo.mem_nhds hz.1] with y hy hyU
    exact ⟨hyU, by rw [hy, hz.2]⟩
  -- its complement in `U` is open too
  have hSc : IsOpen (U \ {z ∈ U | u z = ũ c}) := by
    have heq : U \ {z ∈ U | u z = ũ c} = U ∩ u ⁻¹' (Iio (ũ c)) := by
      ext z
      simp only [mem_diff, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_Iio, not_and]
      constructor
      · rintro ⟨hz, h⟩
        refine ⟨hz, lt_of_le_of_ne ?_ (h hz)⟩
        rw [← hũU z hz]
        exact hcmax' z (subset_closure hz)
      · rintro ⟨hz, h⟩
        exact ⟨hz, fun _ h' => (ne_of_lt h) h'⟩
    rw [heq]
    exact (InnerProductSpace.HarmonicOnNhd.continuousOn hu).isOpen_inter_preimage hUo isOpen_Iio
  -- hence `u ≡ ũ c` on the connected set `U`
  have hall : U ⊆ {z ∈ U | u z = ũ c} := by
    refine IsPreconnected.subset_left_of_subset_union hSo hSc disjoint_sdiff_right ?_
      ⟨c, hcU', hcU', (hũU c hcU').symm⟩ hUc
    intro z hz
    by_cases h : z ∈ {z ∈ U | u z = ũ c}
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩
  -- but `u → 0` at a boundary point, which exists since `U` is bounded and nonempty
  have hfr : (frontier U).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty, isClopen_iff] at h
    rcases h with h | h
    · exact hUne.ne_empty h
    · rw [h] at hUb
      exact NormedSpace.unbounded_univ ℝ ℂ hUb
  obtain ⟨ζ, hζ⟩ := hfr
  have h1 : Tendsto u (𝓝[U] ζ) (𝓝 0) := hbd ζ hζ
  have h2 : Tendsto u (𝓝[U] ζ) (𝓝 (ũ c)) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => ((hall hy).2).symm)
  haveI : NeBot (𝓝[U] ζ) := mem_closure_iff_nhdsWithin_neBot.1 (frontier_subset_closure hζ)
  have h3 := tendsto_nhds_unique h1 h2
  rw [← h3] at hM
  exact lt_irrefl _ hM

/-- **Uniqueness for the Dirichlet problem.**  A harmonic function on a bounded connected open set
which tends to `0` at every boundary point vanishes. -/
theorem eqOn_zero_of_harmonicOnNhd_of_tendsto_frontier {U : Set ℂ} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : IsPreconnected U) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u U)
    (hbd : ∀ ζ ∈ frontier U, Tendsto u (𝓝[U] ζ) (𝓝 0)) :
    ∀ z ∈ U, u z = 0 := by
  intro z hz
  have h1 := le_zero_of_harmonicOnNhd_of_tendsto_frontier hUo hUb hUc hu hbd z hz
  have h2 := le_zero_of_harmonicOnNhd_of_tendsto_frontier hUo hUb hUc hu.neg
    (fun ζ hζ => by
      have h := (hbd ζ hζ).neg
      rw [neg_zero] at h
      exact h) z hz
  simp only [Pi.neg_apply, neg_nonpos] at h2
  exact le_antisymm h1 h2

/-! ### Two small tools: reflection of harmonic functions and of circle integrals -/

/-- If `v` is harmonic near `conj z`, then `v ∘ conj` is harmonic at `z`. -/
theorem harmonicAt_comp_conj {v : ℂ → ℝ} {z : ℂ}
    (hv : ∀ᶠ y in 𝓝 (conj z), InnerProductSpace.HarmonicAt v y) :
    InnerProductSpace.HarmonicAt (fun y => v (conj y)) z := by
  obtain ⟨ρ, hρ, hball⟩ :=
    Metric.mem_nhds_iff.1 (hv : {y | InnerProductSpace.HarmonicAt v y} ∈ 𝓝 (conj z))
  obtain ⟨F, hF, hFv⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq
    (fun y hy => hball hy)
  have hmem : ∀ y ∈ ball z ρ, conj y ∈ ball (conj z) ρ := by
    intro y hy
    rw [mem_ball, dist_eq_norm, ← map_sub, Complex.norm_conj, ← dist_eq_norm]
    exact hy
  have hG : DifferentiableOn ℂ (conj ∘ F ∘ conj) (ball z ρ) := fun y hy =>
    (differentiableAt_conj_conj_iff.2 (hF _ (hmem y hy)).differentiableAt).differentiableWithinAt
  have hGa : AnalyticAt ℂ (conj ∘ F ∘ conj) z := hG.analyticAt (ball_mem_nhds z hρ)
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2 hGa.harmonicAt_re
  filter_upwards [ball_mem_nhds z hρ] with y hy
  show v (conj y) = ((conj ∘ F ∘ conj) y).re
  rw [Function.comp_apply, Function.comp_apply, Complex.conj_re]
  exact (hFv (hmem y hy)).symm

/-- The substitution `θ ↦ -θ` in the integral of a `2π`-periodic function over a period. -/
theorem intervalIntegral_neg_arg_eq_of_periodic {g : ℝ → ℝ}
    (hper : Function.Periodic g (2 * Real.pi)) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, g (-θ) = ∫ θ in (0 : ℝ)..2 * Real.pi, g θ := by
  rw [intervalIntegral.integral_comp_neg g, neg_zero]
  have h := hper.intervalIntegral_add_eq (-(2 * Real.pi)) 0
  rwa [neg_add_cancel, zero_add] at h

/-! ### The Poisson integral of continuous boundary data -/

theorem sub_ne_zero_of_mem_sphere_of_mem_ball {x z w : ℂ} {r : ℝ} (hz : z ∈ sphere x r)
    (hw : w ∈ ball x r) : z - w ≠ 0 := by
  rw [sub_ne_zero]
  rintro rfl
  rw [mem_sphere_iff_norm] at hz
  rw [mem_ball_iff_norm, hz] at hw
  exact lt_irrefl _ hw

/-- The Poisson kernel is nonnegative on the circle. -/
theorem poissonKernel_nonneg_of_mem_sphere {x z w : ℂ} {r : ℝ} (hz : z ∈ sphere x r)
    (hw : w ∈ ball x r) : 0 ≤ poissonKernel x w z := by
  rw [poissonKernel_def]
  refine div_nonneg (sub_nonneg.2 ?_) (sq_nonneg _)
  rw [mem_sphere_iff_norm] at hz
  rw [mem_ball_iff_norm] at hw
  rw [hz]
  exact pow_le_pow_left₀ (norm_nonneg _) hw.le 2

/-- The Poisson kernel is continuous on the circle when `w` lies inside. -/
theorem continuousOn_poissonKernel_sphere {x w : ℂ} {r : ℝ} (hw : w ∈ ball x r) :
    ContinuousOn (fun z => poissonKernel x w z) (sphere x r) := by
  have hne : ∀ z ∈ sphere x r, ‖(z - x) - (w - x)‖ ^ 2 ≠ 0 := by
    intro z hz
    refine pow_ne_zero 2 (norm_ne_zero_iff.2 ?_)
    rw [sub_sub_sub_cancel_right]
    exact sub_ne_zero_of_mem_sphere_of_mem_ball hz hw
  simp only [poissonKernel_def]
  exact ContinuousOn.div (by fun_prop) (by fun_prop) hne

theorem circleIntegrable_poissonKernel_mul {x w : ℂ} {r : ℝ} (hr : 0 ≤ r) (hw : w ∈ ball x r)
    {V : ℂ → ℝ} (hV : ContinuousOn V (sphere x r)) :
    CircleIntegrable (fun z => poissonKernel x w z * V z) x r :=
  ((continuousOn_poissonKernel_sphere hw).mul hV).circleIntegrable hr

/-- **The Poisson integral is harmonic.**  For continuous boundary data `V` on the circle
`∂B(x, r)`, the Poisson integral `w ↦ ⨍ P(x, w, z) V(z)` is harmonic on `B(x, r)`.  (It is the
real part of the Herglotz integral, which is a Cauchy integral up to constants.) -/
theorem harmonicOnNhd_poissonIntegral {x : ℂ} {r : ℝ} (hr : 0 < r) {V : ℂ → ℝ}
    (hV : ContinuousOn V (sphere x r)) :
    InnerProductSpace.HarmonicOnNhd
      (fun w => Real.circleAverage (fun z => poissonKernel x w z * V z) x r) (ball x r) := by
  -- the complexified data and its Cauchy integral
  set Vc : ℂ → ℂ := fun z => (V z : ℂ) with hVc
  have hVcc : ContinuousOn Vc (sphere x r) := continuous_ofReal.comp_continuousOn hV
  have hVci : CircleIntegrable Vc x r := hVcc.circleIntegrable hr.le
  set A : ℂ → ℂ := fun w => (2 * Real.pi * I)⁻¹ • ∮ z in C(x, r), (z - w)⁻¹ • Vc z with hA
  have hAan : ∀ w ∈ ball x r, AnalyticAt ℂ A w := by
    intro w hw
    have hR : (0 : NNReal) < r.toNNReal := Real.toNNReal_pos.2 hr
    have hVci' : CircleIntegrable Vc x (r.toNNReal : ℝ) := by
      rwa [Real.coe_toNNReal r hr.le]
    have h := hasFPowerSeriesOn_cauchy_integral hVci' hR
    rw [Real.coe_toNNReal r hr.le] at h
    refine h.analyticAt_of_mem ?_
    rw [Metric.eball_coe, Real.coe_toNNReal r hr.le]
    exact hw
  -- the Herglotz kernel in terms of the Cauchy kernel
  have hker : ∀ w ∈ ball x r, ∀ z ∈ sphere x r,
      herglotzRieszKernel x w z = 2 * ((z - x) * (z - w)⁻¹) - 1 := by
    intro w hw z hz
    have hzw : z - w ≠ 0 := sub_ne_zero_of_mem_sphere_of_mem_ball hz hw
    rw [herglotzRieszKernel_def, sub_sub_sub_cancel_right]
    field_simp
    ring
  have hcont1 : ∀ w ∈ ball x r,
      ContinuousOn (fun z => (z - x) * (z - w)⁻¹ * Vc z) (sphere x r) := by
    intro w hw
    exact ((continuousOn_id.sub continuousOn_const).mul
      ((continuousOn_id.sub continuousOn_const).inv₀
        fun z hz => sub_ne_zero_of_mem_sphere_of_mem_ball hz hw)).mul hVcc
  have hHeq : ∀ w ∈ ball x r,
      Real.circleAverage (fun z => herglotzRieszKernel x w z * Vc z) x r
        = 2 * A w - Real.circleAverage Vc x r := by
    intro w hw
    have h1 : Real.circleAverage (fun z => herglotzRieszKernel x w z * Vc z) x r
        = Real.circleAverage (fun z => (2 : ℂ) • ((z - x) * (z - w)⁻¹ * Vc z) - Vc z) x r := by
      refine Real.circleAverage_congr_sphere fun z hz => ?_
      rw [abs_of_pos hr] at hz
      rw [hker w hw z hz, smul_eq_mul]
      ring
    rw [h1, Real.circleAverage_fun_sub
      (f₁ := fun z => (2 : ℂ) • ((z - x) * (z - w)⁻¹ * Vc z))
      (((hcont1 w hw).const_smul (2 : ℂ)).circleIntegrable hr.le) hVci,
      Real.circleAverage_fun_smul, smul_eq_mul]
    congr 2
    rw [Real.circleAverage_eq_circleIntegral hr.ne']
    simp only [hA]
    congr 1
    refine circleIntegral.integral_congr hr.le fun z hz => ?_
    have hzx : z - x ≠ 0 := by
      rw [sub_ne_zero]
      rintro rfl
      rw [mem_sphere_iff_norm, sub_self, norm_zero] at hz
      exact hr.ne hz
    simp only [smul_eq_mul]
    field_simp
  -- the Poisson integral is the real part of the Herglotz integral
  have hre : ∀ w ∈ ball x r,
      Real.circleAverage (fun z => poissonKernel x w z * V z) x r
        = (Real.circleAverage (fun z => herglotzRieszKernel x w z * Vc z) x r).re := by
    intro w hw
    have hkc : ContinuousOn (fun z => herglotzRieszKernel x w z) (sphere x r) := by
      have : (fun z => herglotzRieszKernel x w z)
          = fun z => ((z - x) + (w - x)) / ((z - x) - (w - x)) :=
        funext (herglotzRieszKernel_def x w)
      rw [this]
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_
      rw [sub_sub_sub_cancel_right]
      exact sub_ne_zero_of_mem_sphere_of_mem_ball hz hw
    have hint : CircleIntegrable (fun z => herglotzRieszKernel x w z * Vc z) x r :=
      (hkc.mul hVcc).circleIntegrable hr.le
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.circleAverage_comp_comm reCLM hint]
    refine Real.circleAverage_congr_sphere fun z _ => ?_
    simp only [Function.comp_apply, Complex.reCLM_apply, hVc, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    rw [congrFun poissonKernel_eq_re_herglotzRieszKernel z, Function.comp_apply]
  intro w₀ hw₀
  have hev : (fun w => Real.circleAverage (fun z => poissonKernel x w z * V z) x r)
      =ᶠ[𝓝 w₀] fun w => (2 * A w - Real.circleAverage Vc x r).re := by
    filter_upwards [isOpen_ball.mem_nhds hw₀] with w hw
    rw [hre w hw, hHeq w hw]
  refine (InnerProductSpace.harmonicAt_congr_nhds hev).2 ?_
  exact AnalyticAt.harmonicAt_re ((analyticAt_const.mul (hAan w₀ hw₀)).sub analyticAt_const)

/-! ### Boundary values of the Poisson integral, via harmonic barriers -/

/-- On the circle, the affine barrier `r² - Re((z - x) conj (ζ - x))` equals `‖z - ζ‖² / 2`. -/
theorem barrier_eq_of_mem_sphere {x z ζ : ℂ} {r : ℝ} (hz : z ∈ sphere x r)
    (hζ : ζ ∈ sphere x r) :
    r ^ 2 - ((z - x) * conj (ζ - x)).re = ‖z - ζ‖ ^ 2 / 2 := by
  rw [mem_sphere_iff_norm] at hz hζ
  have h := Complex.normSq_sub (z - x) (ζ - x)
  rw [sub_sub_sub_cancel_right, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq, hz, hζ] at h
  linarith

/-- The affine barrier is bounded by `r ‖ζ - w‖`. -/
theorem barrier_le_of_mem_sphere {x w ζ : ℂ} {r : ℝ} (hζ : ζ ∈ sphere x r) :
    r ^ 2 - ((w - x) * conj (ζ - x)).re ≤ r * ‖ζ - w‖ := by
  rw [mem_sphere_iff_norm] at hζ
  have h1 : ((ζ - x) * conj (ζ - x)).re = r ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ, Complex.ofReal_re]
  have h2 : r ^ 2 - ((w - x) * conj (ζ - x)).re = ((ζ - w) * conj (ζ - x)).re := by
    rw [← h1, ← Complex.sub_re, ← sub_mul, sub_sub_sub_cancel_right]
  rw [h2]
  calc ((ζ - w) * conj (ζ - x)).re ≤ ‖(ζ - w) * conj (ζ - x)‖ := Complex.re_le_norm _
    _ = r * ‖ζ - w‖ := by rw [norm_mul, Complex.norm_conj, hζ, mul_comm]

/-- **Upper barrier for the Poisson integral.**  For continuous boundary data `V`, a boundary point
`ζ` and `ε > 0`, the Poisson integral is bounded by `V ζ + ε + C ‖ζ - w‖`.  (Compare with the
harmonic barrier `V ζ + ε + K (r² - Re((w - x) conj (ζ - x)))`, which dominates `V` on the circle
and is reproduced by the Poisson formula.) -/
theorem poissonIntegral_le_of_continuousOn {x : ℂ} {r : ℝ} (hr : 0 < r) {V : ℂ → ℝ}
    (hV : ContinuousOn V (sphere x r)) {ζ : ℂ} (hζ : ζ ∈ sphere x r) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ ball x r,
      Real.circleAverage (fun z => poissonKernel x w z * V z) x r ≤ V ζ + ε + C * ‖ζ - w‖ := by
  -- a bound for `V` and a modulus of continuity at `ζ`
  obtain ⟨M, hM⟩ := (isCompact_sphere x r).exists_bound_of_continuousOn hV
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM ζ hζ)
  obtain ⟨δ, hδ, hδV⟩ := Metric.continuousWithinAt_iff.1 (hV ζ hζ) ε hε
  have hδ0 : δ ≠ 0 := hδ.ne'
  -- the barrier
  set K : ℝ := 4 * M / δ ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  set b : ℂ → ℝ := fun w => r ^ 2 - ((w - x) * conj (ζ - x)).re with hb
  set h : ℂ → ℝ := fun w => V ζ + ε + K * b w with hh
  have hcont : Continuous h := by
    rw [hh, hb]
    fun_prop
  -- the barrier is harmonic and continuous
  have hharm : InnerProductSpace.HarmonicContOnCl h (ball x r) := by
    refine ⟨fun w _ => ?_, hcont.continuousOn⟩
    have hG : AnalyticAt ℂ (fun w : ℂ => ((V ζ + ε : ℝ) : ℂ) + (K : ℂ) *
        (((r ^ 2 : ℝ) : ℂ) - (w - x) * conj (ζ - x))) w := by fun_prop
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2 hG.harmonicAt_re
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [hh, hb, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  -- the barrier dominates `V` on the circle
  have hVh : ∀ z ∈ sphere x r, V z ≤ h z := by
    intro z hz
    have hbz : b z = ‖z - ζ‖ ^ 2 / 2 := barrier_eq_of_mem_sphere hz hζ
    have hbz0 : 0 ≤ b z := by rw [hbz]; positivity
    simp only [hh]
    by_cases hzζ : dist z ζ < δ
    · have h1 := hδV hz hzζ
      rw [Real.dist_eq, abs_sub_lt_iff] at h1
      have h2 : 0 ≤ K * b z := mul_nonneg hK0 hbz0
      linarith [h1.1]
    · have hzζ' : δ ≤ dist z ζ := not_lt.1 hzζ
      have hb2 : δ ^ 2 / 2 ≤ b z := by
        rw [hbz]
        have : δ ^ 2 ≤ ‖z - ζ‖ ^ 2 := by
          rw [← dist_eq_norm]
          exact pow_le_pow_left₀ hδ.le hzζ' 2
        linarith
      have hKb : 2 * M ≤ K * b z := by
        calc 2 * M = K * (δ ^ 2 / 2) := by
              rw [hK]
              field_simp
              ring
          _ ≤ K * b z := mul_le_mul_of_nonneg_left hb2 hK0
      have h1 : V z ≤ M := by
        have := hM z hz
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans this
      have h2 : -M ≤ V ζ := by
        have := hM ζ hζ
        rw [Real.norm_eq_abs] at this
        exact (abs_le.1 this).1
      linarith
  refine ⟨K * r, mul_nonneg hK0 hr.le, fun w hw => ?_⟩
  have hint1 := circleIntegrable_poissonKernel_mul hr.le hw hV
  have hint2 : CircleIntegrable (fun z => poissonKernel x w z * h z) x r :=
    circleIntegrable_poissonKernel_mul hr.le hw hcont.continuousOn
  calc Real.circleAverage (fun z => poissonKernel x w z * V z) x r
      ≤ Real.circleAverage (fun z => poissonKernel x w z * h z) x r := by
        refine Real.circleAverage_mono hint1 hint2 fun z hz => ?_
        rw [abs_of_pos hr] at hz
        exact mul_le_mul_of_nonneg_left (hVh z hz) (poissonKernel_nonneg_of_mem_sphere hz hw)
    _ = h w := hharm.circleAverage_poissonKernel_smul hw
    _ ≤ V ζ + ε + K * r * ‖ζ - w‖ := by
        simp only [hh, hb]
        have h1 := mul_le_mul_of_nonneg_left (barrier_le_of_mem_sphere (w := w) hζ) hK0
        rw [mul_assoc]
        linarith

/-- **Boundary values of the Poisson integral.**  The Poisson integral of continuous boundary data
tends to the data at each boundary point. -/
theorem tendsto_poissonIntegral_nhdsWithin {x : ℂ} {r : ℝ} (hr : 0 < r) {V : ℂ → ℝ}
    (hV : ContinuousOn V (sphere x r)) {ζ : ℂ} (hζ : ζ ∈ sphere x r) :
    Tendsto (fun w => Real.circleAverage (fun z => poissonKernel x w z * V z) x r)
      (𝓝[ball x r] ζ) (𝓝 (V ζ)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨C₁, hC₁, h₁⟩ := poissonIntegral_le_of_continuousOn hr hV hζ (half_pos hε)
  obtain ⟨C₂, hC₂, h₂⟩ := poissonIntegral_le_of_continuousOn hr hV.neg hζ (half_pos hε)
  refine ⟨ε / 2 / (C₁ + C₂ + 1), by positivity, fun w hw hwζ => ?_⟩
  have hneg : Real.circleAverage (fun z => poissonKernel x w z * -V z) x r
      = -Real.circleAverage (fun z => poissonKernel x w z * V z) x r := by
    have := Real.circleAverage_fun_smul (a := (-1 : ℝ))
      (f := fun z => poissonKernel x w z * V z) (c := x) (R := r)
    rw [neg_one_smul] at this
    rw [← this]
    congr 1
    funext z
    simp only [smul_eq_mul]
    ring
  have hn : 0 ≤ ‖ζ - w‖ := norm_nonneg _
  have hd : ‖ζ - w‖ < ε / 2 / (C₁ + C₂ + 1) := by
    rw [norm_sub_rev, ← dist_eq_norm]
    exact hwζ
  have hd' : (C₁ + C₂ + 1) * ‖ζ - w‖ < ε / 2 := by
    rw [mul_comm, ← lt_div_iff₀ (by positivity)]
    exact hd
  have hd₁ : C₁ * ‖ζ - w‖ ≤ (C₁ + C₂ + 1) * ‖ζ - w‖ :=
    mul_le_mul_of_nonneg_right (by linarith) hn
  have hd₂ : C₂ * ‖ζ - w‖ ≤ (C₁ + C₂ + 1) * ‖ζ - w‖ :=
    mul_le_mul_of_nonneg_right (by linarith) hn
  have e₁ := h₁ w hw
  have e₂ := h₂ w hw
  simp only [Pi.neg_apply] at e₂
  rw [hneg] at e₂
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-! ### Symmetry of the Poisson integral under conjugation -/

theorem poissonKernel_conj_conj {x w z : ℂ} (hx : x.im = 0) :
    poissonKernel x (conj w) (conj z) = poissonKernel x w z := by
  have hxc : conj x = x := Complex.conj_eq_iff_im.2 hx
  simp only [poissonKernel_def]
  rw [show conj z - x = conj (z - x) by rw [map_sub, hxc],
    show conj w - x = conj (w - x) by rw [map_sub, hxc], ← map_sub, Complex.norm_conj,
    Complex.norm_conj, Complex.norm_conj]

theorem circleMap_neg_eq_conj {x : ℂ} (hx : x.im = 0) (r θ : ℝ) :
    circleMap x r (-θ) = conj (circleMap x r θ) := by
  have hxc : conj x = x := Complex.conj_eq_iff_im.2 hx
  simp only [circleMap, map_add, map_mul, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I, hxc]
  push_cast
  ring_nf

/-- **Odd symmetry of the Poisson integral.**  If the centre is real and the data is odd under
conjugation, so is the Poisson integral. -/
theorem poissonIntegral_conj_eq_neg {x : ℂ} (hx : x.im = 0) {r : ℝ} {V : ℂ → ℝ}
    (hV : ∀ z, V (conj z) = -V z) (w : ℂ) :
    Real.circleAverage (fun z => poissonKernel x (conj w) z * V z) x r
      = -Real.circleAverage (fun z => poissonKernel x w z * V z) x r := by
  simp only [Real.circleAverage_def]
  rw [← smul_neg]
  congr 1
  set g : ℝ → ℝ := fun θ => poissonKernel x w (circleMap x r θ) * V (circleMap x r θ) with hg
  have hper : Function.Periodic g (2 * Real.pi) := by
    intro θ
    simp only [hg, periodic_circleMap x r θ]
  have hpt : ∀ θ : ℝ, poissonKernel x (conj w) (circleMap x r θ) * V (circleMap x r θ)
      = -g (-θ) := by
    intro θ
    have h := circleMap_neg_eq_conj hx r (-θ)
    rw [neg_neg] at h
    simp only [hg]
    rw [h, poissonKernel_conj_conj hx, hV]
    ring
  rw [← intervalIntegral_neg_arg_eq_of_periodic hper, ← intervalIntegral.integral_neg]
  exact intervalIntegral.integral_congr fun θ _ => hpt θ

/-! ### The odd reflection: symmetry and continuity -/

theorem reflectExtendOdd_conj (v : ℂ → ℝ) (z : ℂ) :
    reflectExtendOdd v (conj z) = -reflectExtendOdd v z := by
  simp only [reflectExtendOdd, Complex.conj_im, Complex.conj_conj]
  rcases lt_trichotomy z.im 0 with h | h | h
  · simp [h, h.ne, not_lt.2 h.le]
  · simp [h]
  · simp [h, h.ne', not_lt.2 h.le]

theorem reflectExtendOdd_of_pos (v : ℂ → ℝ) {z : ℂ} (hz : 0 < z.im) :
    reflectExtendOdd v z = v z := by
  simp [reflectExtendOdd, hz]

theorem reflectExtendOdd_of_eq_zero (v : ℂ → ℝ) {z : ℂ} (hz : z.im = 0) :
    reflectExtendOdd v z = 0 := by
  simp [reflectExtendOdd, hz]

theorem reflectExtendOdd_of_neg (v : ℂ → ℝ) {z : ℂ} (hz : z.im < 0) :
    reflectExtendOdd v z = -v (conj z) := by
  simp [reflectExtendOdd, not_lt.2 hz.le, hz.ne]

/-- The odd reflection of a harmonic function with zero boundary values is continuous. -/
theorem continuousOn_reflectExtendOdd {Ω : Set ℂ} (hΩ : IsRealSymmetric Ω) {v : ℂ → ℝ}
    (hv : InnerProductSpace.HarmonicOnNhd v (upperPart Ω))
    (hbdry : ∀ x ∈ realPart Ω, Tendsto v (𝓝[upperPart Ω] x) (𝓝 0)) :
    ContinuousOn (reflectExtendOdd v) Ω := by
  have hconj : ∀ z ∈ Ω, conj z ∈ Ω := fun z hz => by
    have h : conj z ∈ conjSet Ω := mem_image_of_mem conj hz
    rwa [hΩ.conj_eq] at h
  have hUo : IsOpen (upperPart Ω) := hΩ.isOpen.inter (isOpen_lt continuous_const continuous_im)
  have hPo : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im
  have hLo : IsOpen {z : ℂ | z.im < 0} := isOpen_lt continuous_im continuous_const
  have hvcont : ∀ z ∈ upperPart Ω, ContinuousAt v z := fun z hz =>
    (HarmonicAt.analyticAt (hv z hz)).continuousAt
  intro z hz
  rcases lt_trichotomy z.im 0 with h | h | h
  · -- below the axis
    have hcz : conj z ∈ upperPart Ω := ⟨hconj z hz, by rw [Complex.conj_im]; linarith⟩
    have hc : ContinuousAt (fun y => -v (conj y)) z :=
      ((hvcont _ hcz).comp continuous_conj.continuousAt).neg
    refine (hc.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [hLo.mem_nhds (show z ∈ {z : ℂ | z.im < 0} from h)] with y hy
    exact reflectExtendOdd_of_neg v hy
  · -- on the axis: glue the three pieces
    have hzr : z ∈ realPart Ω := ⟨hz, h⟩
    have hzc : conj z = z := Complex.conj_eq_iff_im.2 h
    rw [← upper_union_real_union_lower Ω]
    show Tendsto (reflectExtendOdd v) (𝓝[upperPart Ω ∪ realPart Ω ∪ lowerPart Ω] z)
      (𝓝 (reflectExtendOdd v z))
    rw [reflectExtendOdd_of_eq_zero v h, nhdsWithin_union, nhdsWithin_union]
    refine Tendsto.sup (Tendsto.sup ?_ ?_) ?_
    · refine (hbdry z hzr).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
      exact (reflectExtendOdd_of_pos v hy.2).symm
    · refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
      exact (reflectExtendOdd_of_eq_zero v hy.2).symm
    · have hmaps : MapsTo conj (lowerPart Ω) (upperPart Ω) := fun y hy =>
        ⟨hconj y hy.1, by rw [Complex.conj_im]; linarith [hy.2]⟩
      have h1 : Tendsto conj (𝓝[lowerPart Ω] z) (𝓝[upperPart Ω] z) := by
        have := (continuous_conj.continuousWithinAt (s := lowerPart Ω) (x := z)).tendsto_nhdsWithin
          hmaps
        rwa [hzc] at this
      have h2 : Tendsto (fun y => -v (conj y)) (𝓝[lowerPart Ω] z) (𝓝 0) := by
        have := ((hbdry z hzr).comp h1).neg
        rwa [neg_zero] at this
      refine h2.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
      exact (reflectExtendOdd_of_neg v hy.2).symm
  · -- above the axis
    have hzU : z ∈ upperPart Ω := ⟨hz, h⟩
    refine ((hvcont z hzU).congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [hPo.mem_nhds (show z ∈ {z : ℂ | 0 < z.im} from h)] with y hy
    exact reflectExtendOdd_of_pos v hy

/-- **Schwarz reflection, harmonic version.**  `v` harmonic on `Ω⁺` with `v → 0` at `σ` extends by
odd reflection to a harmonic function on `Ω`. -/
theorem schwarz_reflection_harmonic {Ω : Set ℂ} (hΩ : IsRealSymmetric Ω) {v : ℂ → ℝ}
    (hv : InnerProductSpace.HarmonicOnNhd v (upperPart Ω))
    (hbdry : ∀ x ∈ realPart Ω, Tendsto v (𝓝[upperPart Ω] x) (𝓝 0)) :
    InnerProductSpace.HarmonicOnNhd (reflectExtendOdd v) Ω := by
  have hconj : ∀ z ∈ Ω, conj z ∈ Ω := fun z hz => by
    have h : conj z ∈ conjSet Ω := mem_image_of_mem conj hz
    rwa [hΩ.conj_eq] at h
  have hUo : IsOpen (upperPart Ω) := hΩ.isOpen.inter (isOpen_lt continuous_const continuous_im)
  have hPo : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im
  have hLo : IsOpen {z : ℂ | z.im < 0} := isOpen_lt continuous_im continuous_const
  have hVcont : ContinuousOn (reflectExtendOdd v) Ω := continuousOn_reflectExtendOdd hΩ hv hbdry
  intro x hx
  rcases lt_trichotomy x.im 0 with h | h | h
  · -- below the axis: `V = -v ∘ conj` near `x`
    have hcx : conj x ∈ upperPart Ω := ⟨hconj x hx, by rw [Complex.conj_im]; linarith⟩
    have h1 : InnerProductSpace.HarmonicAt (fun y => v (conj y)) x :=
      harmonicAt_comp_conj (Filter.eventually_of_mem (hUo.mem_nhds hcx) fun y hy => hv y hy)
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2 h1.neg
    filter_upwards [hLo.mem_nhds (show x ∈ {z : ℂ | z.im < 0} from h)] with y hy
    exact reflectExtendOdd_of_neg v hy
  · -- on the axis: compare with the Poisson integral of `V` on a small disc
    have hxr : x ∈ realPart Ω := ⟨hx, h⟩
    have hxc : conj x = x := Complex.conj_eq_iff_im.2 h
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ.isOpen x hx
    set r : ℝ := ε / 2 with hr_def
    have hr : 0 < r := by positivity
    have hcb : closedBall x r ⊆ Ω :=
      (closedBall_subset_ball (by rw [hr_def]; linarith)).trans hball
    have hV : ContinuousOn (reflectExtendOdd v) (sphere x r) :=
      hVcont.mono (sphere_subset_closedBall.trans hcb)
    -- the Poisson integral of `V` and its properties
    set P : ℂ → ℝ := fun w =>
      Real.circleAverage (fun z => poissonKernel x w z * reflectExtendOdd v z) x r with hP
    have hPh : InnerProductSpace.HarmonicOnNhd P (ball x r) :=
      harmonicOnNhd_poissonIntegral hr hV
    have hPb : ∀ ζ ∈ sphere x r, Tendsto P (𝓝[ball x r] ζ) (𝓝 (reflectExtendOdd v ζ)) :=
      fun ζ hζ => tendsto_poissonIntegral_nhdsWithin hr hV hζ
    have hPodd : ∀ w, P (conj w) = -P w := fun w =>
      poissonIntegral_conj_eq_neg h (reflectExtendOdd_conj v) w
    have hP0 : ∀ w : ℂ, w.im = 0 → P w = 0 := by
      intro w hw
      have := hPodd w
      rw [Complex.conj_eq_iff_im.2 hw] at this
      linarith
    -- the upper half-disc
    set D : Set ℂ := ball x r ∩ {y : ℂ | 0 < y.im} with hD
    have hDo : IsOpen D := isOpen_ball.inter hPo
    have hDb : Bornology.IsBounded D := isBounded_ball.subset inter_subset_left
    have hDc : IsPreconnected D :=
      ((convex_ball x r).inter (convex_halfSpace_im_gt 0)).isPreconnected
    have hDU : D ⊆ upperPart Ω := fun y hy => ⟨hcb (ball_subset_closedBall hy.1), hy.2⟩
    have hDcl : closure D ⊆ closedBall x r ∩ {y : ℂ | 0 ≤ y.im} := by
      refine (closure_inter_subset_inter_closure _ _).trans (inter_subset_inter ?_ ?_)
      · exact closure_ball_subset_closedBall
      · exact (IsClosed.closure_subset_iff (isClosed_le continuous_const continuous_im)).2
          fun y hy => show (0 : ℝ) ≤ y.im from le_of_lt hy
    -- `P - v` is harmonic on `D` and tends to `0` at its boundary
    have hu : InnerProductSpace.HarmonicOnNhd (P - v) D :=
      fun y hy => (hPh y hy.1).sub (hv y (hDU hy))
    have hbd : ∀ ζ ∈ frontier D, Tendsto (P - v) (𝓝[D] ζ) (𝓝 0) := by
      intro ζ hζ
      have hζcl : ζ ∈ closure D := frontier_subset_closure hζ
      have hζD : ζ ∉ D := by
        rw [hDo.frontier_eq] at hζ
        exact hζ.2
      obtain ⟨hζb, hζim'⟩ := hDcl hζcl
      have hζim : 0 ≤ ζ.im := hζim'
      have hζΩ : ζ ∈ Ω := hcb hζb
      have hPζ : Tendsto P (𝓝[D] ζ) (𝓝 (reflectExtendOdd v ζ)) := by
        rcases eq_or_lt_of_le (mem_closedBall.1 hζb) with hζs | hζs
        · exact (hPb ζ hζs).mono_left (nhdsWithin_mono _ inter_subset_left)
        · have hζb' : ζ ∈ ball x r := hζs
          have hζ0 : ζ.im = 0 := by
            by_contra hne
            exact hζD ⟨hζb', lt_of_le_of_ne hζim (Ne.symm hne)⟩
          have hPc : Tendsto P (𝓝[D] ζ) (𝓝 (P ζ)) :=
            (HarmonicAt.analyticAt (hPh ζ hζb')).continuousAt.continuousWithinAt
          rw [hP0 ζ hζ0] at hPc
          rw [reflectExtendOdd_of_eq_zero v hζ0]
          exact hPc
      have hvζ : Tendsto v (𝓝[D] ζ) (𝓝 (reflectExtendOdd v ζ)) := by
        rcases eq_or_lt_of_le hζim with hζ0 | hζ0
        · rw [reflectExtendOdd_of_eq_zero v hζ0.symm]
          exact (hbdry ζ ⟨hζΩ, hζ0.symm⟩).mono_left (nhdsWithin_mono _ hDU)
        · rw [reflectExtendOdd_of_pos v hζ0]
          exact (HarmonicAt.analyticAt (hv ζ ⟨hζΩ, hζ0⟩)).continuousAt.continuousWithinAt
      have := hPζ.sub hvζ
      rw [sub_self] at this
      exact this
    have hzero := eqOn_zero_of_harmonicOnNhd_of_tendsto_frontier hDo hDb hDc hu hbd
    -- hence `P = V` on the whole disc
    have hPV : ∀ y ∈ ball x r, P y = reflectExtendOdd v y := by
      intro y hy
      rcases lt_trichotomy y.im 0 with hy0 | hy0 | hy0
      · have hcy : conj y ∈ D := by
          refine ⟨?_, show 0 < (conj y).im by rw [Complex.conj_im]; linarith⟩
          rw [mem_ball, dist_eq_norm, ← hxc, ← map_sub, Complex.norm_conj, ← dist_eq_norm]
          exact hy
        have h1 := hzero (conj y) hcy
        rw [Pi.sub_apply, sub_eq_zero] at h1
        calc P y = P (conj (conj y)) := by rw [Complex.conj_conj]
          _ = -P (conj y) := hPodd (conj y)
          _ = -v (conj y) := by rw [h1]
          _ = -reflectExtendOdd v (conj y) := by rw [reflectExtendOdd_of_pos v hcy.2]
          _ = reflectExtendOdd v y := by rw [reflectExtendOdd_conj, neg_neg]
      · rw [hP0 y hy0, reflectExtendOdd_of_eq_zero v hy0]
      · have h1 := hzero y ⟨hy, hy0⟩
        rw [Pi.sub_apply, sub_eq_zero] at h1
        rw [h1, reflectExtendOdd_of_pos v hy0]
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2 (hPh x (mem_ball_self hr))
    filter_upwards [ball_mem_nhds x hr] with y hy
    exact (hPV y hy).symm
  · -- above the axis
    have hxU : x ∈ upperPart Ω := ⟨hx, h⟩
    refine (InnerProductSpace.harmonicAt_congr_nhds ?_).2 (hv x hxU)
    filter_upwards [hPo.mem_nhds (show x ∈ {z : ℂ | 0 < z.im} from h)] with y hy
    exact reflectExtendOdd_of_pos v hy

/-- A holomorphic function with real values on a preconnected open set is constant (open mapping
theorem). -/
theorem eqOn_const_of_im_eq_zero {s : Set ℂ} (hs : IsOpen s) (hsc : IsPreconnected s)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h s) (him : ∀ z ∈ s, (h z).im = 0) :
    ∃ c : ℂ, c.im = 0 ∧ ∀ z ∈ s, h z = c := by
  rcases s.eq_empty_or_nonempty with hse | ⟨z₀, hz₀⟩
  · exact ⟨0, Complex.zero_im, fun z hz => by rw [hse] at hz; simp at hz⟩
  rcases (hh.analyticOnNhd hs).is_constant_or_isOpen hsc with ⟨w, hw⟩ | hopen
  · refine ⟨w, ?_, hw⟩
    rw [← hw z₀ hz₀]
    exact him z₀ hz₀
  · exfalso
    have hio : IsOpen (h '' s) := hopen s Subset.rfl hs
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hio (h z₀) (Set.mem_image_of_mem h hz₀)
    have hmem : h z₀ + ((ε / 2 : ℝ) : ℂ) * I ∈ ball (h z₀) ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    obtain ⟨z, hz, hzeq⟩ := hball hmem
    have h1 : (h z).im = (h z₀ + ((ε / 2 : ℝ) : ℂ) * I).im := congrArg Complex.im hzeq
    have h2 : (h z₀ + ((ε / 2 : ℝ) : ℂ) * I).im = ε / 2 := by
      simp [him z₀ hz₀]
    rw [him z hz, h2] at h1
    linarith

/-- Points of the real part of an open set are limits of points of its upper part. -/
theorem realPart_mem_closure_upperPart {Ω : Set ℂ} (hΩ : IsOpen Ω) {y : ℂ} (hy : y ∈ realPart Ω) :
    y ∈ closure (upperPart Ω) := by
  have hy' : y ∈ Ω ∧ y.im = 0 := hy
  set s : ℕ → ℂ := fun n => y + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I with hs
  have hlim : Tendsto s atTop (𝓝 y) := by
    have h1 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop
        (𝓝 (((0 : ℝ) : ℂ) * I)) :=
      ((Complex.continuous_ofReal.tendsto _).comp tendsto_one_div_add_atTop_nhds_zero_nat).mul_const I
    have h2 := h1.const_add y
    have h3 : y + ((0 : ℝ) : ℂ) * I = y := by simp
    rw [h3] at h2
    exact h2
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [hlim.eventually (hΩ.mem_nhds hy'.1)] with n hn
  have hpos : 0 < (y + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I).im := by
    simp only [Complex.add_im, hy'.2, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
    positivity
  have hmem : s n ∈ Ω ∧ 0 < (s n).im := ⟨hn, hpos⟩
  exact hmem

/-- Continuity on `σ` is not needed: it suffices that `Im f → 0` at `σ`. -/
theorem schwarz_reflection_segment_of_im_tendsto_zero {Ω : Set ℂ} (hΩ : IsRealSymmetric Ω)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (upperPart Ω))
    (him : ∀ x ∈ realPart Ω, Tendsto (fun z => (f z).im) (𝓝[upperPart Ω] x) (𝓝 0)) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧ EqOn F f (upperPart Ω) := by
  have hUo : IsOpen (upperPart Ω) :=
    hΩ.isOpen.inter (isOpen_lt continuous_const Complex.continuous_im)
  -- the harmonic function `v = Im f` on `Ω⁺` and its odd reflection `V`, harmonic on `Ω`
  set v : ℂ → ℝ := fun z => (f z).im with hv
  have hvh : InnerProductSpace.HarmonicOnNhd v (upperPart Ω) := by
    intro z hz
    exact ((hf.analyticOnNhd hUo) z hz).harmonicAt_im
  have hV := schwarz_reflection_harmonic hΩ hvh him
  set V : ℂ → ℝ := reflectExtendOdd v with hVdef
  have hVup : ∀ z : ℂ, 0 < z.im → V z = v z := fun z hz => if_pos hz
  have hVreal : ∀ z : ℂ, z.im = 0 → V z = 0 := by
    intro z hz
    show (if 0 < z.im then v z else if z.im = 0 then 0 else -v (conj z)) = 0
    rw [if_neg (by rw [hz]; exact lt_irrefl 0), if_pos hz]
  -- near each real point, a holomorphic `K` on a ball with `K = f` on the upper part and
  -- real values on the real diameter
  have hloc : ∀ x ∈ realPart Ω, ∃ (r : ℝ) (K : ℂ → ℂ), 0 < r ∧ ball x r ⊆ Ω ∧
      AnalyticOnNhd ℂ K (ball x r) ∧ (∀ z ∈ ball x r, 0 < z.im → K z = f z) ∧
      ∀ z ∈ ball x r, z.im = 0 → (K z).im = 0 := by
    intro x hx
    have hx' : x ∈ Ω ∧ x.im = 0 := hx
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ.isOpen x hx'.1
    obtain ⟨H, hHan, hHre⟩ :=
      InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (hV.mono hrΩ)
    have hK₀im : ∀ z ∈ ball x r, (I * H z).im = V z := fun z hz => by
      rw [Complex.I_mul_im]
      exact hHre hz
    have hK₀an : AnalyticOnNhd ℂ (fun z => I * H z) (ball x r) := analyticOnNhd_const.mul hHan
    -- on the upper half-ball, `I * H - f` is holomorphic with zero imaginary part, hence constant
    set B : Set ℂ := ball x r ∩ {z : ℂ | 0 < z.im} with hB
    have hBo : IsOpen B := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
    have hBc : IsPreconnected B :=
      ((convex_ball x r).inter (convex_halfSpace_im_gt 0)).isPreconnected
    have hBsub : B ⊆ upperPart Ω := fun z hz => ⟨hrΩ hz.1, hz.2⟩
    have hdiff : DifferentiableOn ℂ (fun z => I * H z - f z) B :=
      (hK₀an.differentiableOn.mono Set.inter_subset_left).sub (hf.mono hBsub)
    have himB : ∀ z ∈ B, (I * H z - f z).im = 0 := by
      intro z hz
      rw [Complex.sub_im, hK₀im z hz.1, hVup z hz.2]
      show (f z).im - (f z).im = 0
      exact sub_self _
    obtain ⟨c, hcim, hc⟩ := eqOn_const_of_im_eq_zero hBo hBc hdiff himB
    refine ⟨r, fun z => I * H z - c, hr, hrΩ, hK₀an.sub analyticOnNhd_const, ?_, ?_⟩
    · intro z hz hzim
      have h1 : I * H z - f z = c := hc z ⟨hz, hzim⟩
      linear_combination h1
    · intro z hz hzim
      rw [Complex.sub_im, hK₀im z hz, hVreal z hzim, hcim, sub_zero]
  choose! r K hrK using hloc
  -- `f'`: `f` on `Ω⁺`, the limit from `Ω⁺` on `σ`
  set f' : ℂ → ℂ := fun z => if 0 < z.im then f z else limUnder (𝓝[upperPart Ω] z) f with hf'
  have hf'up : ∀ z ∈ upperPart Ω, f' z = f z := fun z hz => if_pos (show 0 < z.im from hz.2)
  -- near a real point `x`, `f' = K x` on `Ω⁺ ∪ σ`
  have hf'loc : ∀ x ∈ realPart Ω, ∀ y ∈ ball x (r x) ∩ (upperPart Ω ∪ realPart Ω),
      f' y = K x y := by
    intro x hx y hy
    obtain ⟨hyb, hy⟩ := hy
    rcases hy with hyu | hyr
    · rw [hf'up y hyu, (hrK x hx).2.2.2.1 y hyb hyu.2]
    · have hyr' : y ∈ Ω ∧ y.im = 0 := hyr
      have hyim : ¬ 0 < y.im := by
        rw [hyr'.2]
        exact lt_irrefl 0
      show (if 0 < y.im then f y else limUnder (𝓝[upperPart Ω] y) f) = K x y
      rw [if_neg hyim]
      haveI : (𝓝[upperPart Ω] y).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp (realPart_mem_closure_upperPart hΩ.isOpen hyr)
      have hKc : ContinuousAt (K x) y := ((hrK x hx).2.2.1 y hyb).continuousAt
      have hlim : Tendsto f (𝓝[upperPart Ω] y) (𝓝 (K x y)) := by
        refine hKc.continuousWithinAt.tendsto.congr' ?_
        show ∀ᶠ z in 𝓝[upperPart Ω] y, K x z = f z
        rw [eventually_nhdsWithin_iff]
        filter_upwards [isOpen_ball.mem_nhds hyb] with z hz hzu
        exact (hrK x hx).2.2.2.1 z hz hzu.2
      exact hlim.limUnder_eq
  have hf'diff : DifferentiableOn ℂ f' (upperPart Ω) := hf.congr hf'up
  have hf'cont : ContinuousOn f' (upperPart Ω ∪ realPart Ω) := by
    intro z hz
    rcases hz with hzu | hzr
    · have hmem : upperPart Ω ∈ 𝓝 z := hUo.mem_nhds hzu
      have hfc : ContinuousAt f z := (hf.differentiableAt hmem).continuousAt
      refine (hfc.congr ?_).continuousWithinAt
      filter_upwards [hmem] with w hw
      exact (hf'up w hw).symm
    · have hrz := (hrK z hzr).1
      have hKc : ContinuousAt (K z) z := ((hrK z hzr).2.2.1 z (mem_ball_self hrz)).continuousAt
      refine hKc.continuousWithinAt.congr_of_eventuallyEq ?_
        (hf'loc z hzr z ⟨mem_ball_self hrz, Or.inr hzr⟩)
      show ∀ᶠ w in 𝓝[upperPart Ω ∪ realPart Ω] z, f' w = K z w
      rw [eventually_nhdsWithin_iff]
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hrz)] with w hw hws
      exact hf'loc z hzr w ⟨hw, hws⟩
  have hf'real : ∀ x ∈ realPart Ω, (f' x).im = 0 := by
    intro x hx
    rw [hf'loc x hx x ⟨mem_ball_self (hrK x hx).1, Or.inr hx⟩]
    exact (hrK x hx).2.2.2.2 x (mem_ball_self (hrK x hx).1) (show x.im = 0 from hx.2)
  have hF := schwarz_reflection_segment hΩ hf'diff hf'cont hf'real
  refine ⟨reflectExtend f', hF, ?_⟩
  intro z hz
  rw [reflectExtend_eq_of_im_nonneg f' (le_of_lt (show 0 < z.im from hz.2)), hf'up z hz]

/-- Reflection in the unit circle: `z ↦ 1 / z*`. -/
def circleReflect (z : ℂ) : ℂ := 1 / conj z

/-- `U` is an open neighbourhood of the arc `A ⊆ ∂Δ`, invariant under `circleReflect`, meeting the
unit circle exactly in `A`. -/
structure IsCircleSymmetricNbhd (U A : Set ℂ) : Prop where
  isOpen : IsOpen U
  inter_sphere : U ∩ sphere (0 : ℂ) 1 = A
  invariant : ∀ z ∈ U, circleReflect z ∈ U

/-! ### Basic facts: reflection in the circle and the chart to the upper half-plane -/

theorem norm_circleReflect (z : ℂ) : ‖circleReflect z‖ = ‖z‖⁻¹ := by
  rw [circleReflect, norm_div, norm_one, Complex.norm_conj, one_div]

/-- Reflection in the unit circle fixes the circle. -/
theorem circleReflect_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : circleReflect z = z := by
  have h : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    simp
  rw [circleReflect, one_div, eq_inv_of_mul_eq_one_right h, inv_inv]

theorem circleReflect_circleReflect {z : ℂ} (_hz : z ≠ 0) :
    circleReflect (circleReflect z) = z := by
  rw [circleReflect, circleReflect, map_div₀, map_one, conj_conj, one_div, one_div, inv_inv]

theorem continuousAt_circleReflect {z : ℂ} (hz : z ≠ 0) : ContinuousAt circleReflect z := by
  have hc : conj z ≠ 0 := fun h => hz (by rw [← conj_conj z, h, map_zero])
  show ContinuousAt (fun w => 1 / conj w) z
  exact continuousAt_const.div Complex.continuous_conj.continuousAt hc

theorem isRealSymmetric_ball (r : ℝ) : IsRealSymmetric (ball (0 : ℂ) r) := by
  refine ⟨isOpen_ball, ?_⟩
  show conj '' ball (0 : ℂ) r = ball 0 r
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_ball_zero_iff] at hz ⊢
    rwa [Complex.norm_conj]
  · intro hw
    refine ⟨conj w, ?_, conj_conj w⟩
    rw [mem_ball_zero_iff] at hw ⊢
    rwa [Complex.norm_conj]

theorem add_I_ne_zero_of_norm_lt_one {u : ℂ} (hu : ‖u‖ < 1) : I + u ≠ 0 := by
  intro h
  have : u = -I := by linear_combination h
  rw [this, norm_neg, Complex.norm_I] at hu
  exact lt_irrefl _ hu

theorem sub_I_ne_zero_of_norm_lt_one {u : ℂ} (hu : ‖u‖ < 1) : I - u ≠ 0 := by
  intro h
  have : u = I := by linear_combination -h
  rw [this, Complex.norm_I] at hu
  exact lt_irrefl _ hu

/-- The Möbius chart `z ↦ i (ζ - z)/(ζ + z)`: it sends `ζ ↦ 0`, the disc to the upper half-plane
and the circle near `ζ` to the real axis. -/
def arcChart (ζ z : ℂ) : ℂ := I * (ζ - z) / (ζ + z)

/-- The inverse chart `u ↦ ζ (i - u)/(i + u)`. -/
def arcChartInv (ζ u : ℂ) : ℂ := ζ * (I - u) / (I + u)

theorem arcChart_self (ζ : ℂ) : arcChart ζ ζ = 0 := by
  simp [arcChart]

theorem arcChartInv_zero (ζ : ℂ) : arcChartInv ζ 0 = ζ := by
  simp [arcChartInv]

theorem arcChartInv_arcChart {ζ z : ℂ} (hζ : ζ ≠ 0) (hz : ζ + z ≠ 0) :
    arcChartInv ζ (arcChart ζ z) = z := by
  have hden : I + I * (ζ - z) / (ζ + z) ≠ 0 := by
    have h : I + I * (ζ - z) / (ζ + z) = 2 * I * ζ / (ζ + z) := by
      field_simp
      ring
    rw [h]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hζ) hz
  unfold arcChartInv arcChart
  rw [div_eq_iff hden]
  field_simp
  ring

theorem differentiableAt_arcChart {ζ z : ℂ} (hz : ζ + z ≠ 0) :
    DifferentiableAt ℂ (arcChart ζ) z := by
  unfold arcChart
  fun_prop (disch := assumption)

theorem differentiableAt_arcChartInv {ζ u : ℂ} (_hu : I + u ≠ 0) :
    DifferentiableAt ℂ (arcChartInv ζ) u := by
  unfold arcChartInv
  fun_prop (disch := assumption)

theorem continuousAt_arcChartInv {ζ u : ℂ} (hu : I + u ≠ 0) :
    ContinuousAt (arcChartInv ζ) u :=
  (differentiableAt_arcChartInv hu).continuousAt

theorem normSq_I_add_sub_normSq_I_sub (u : ℂ) : normSq (I + u) - normSq (I - u) = 4 * u.im := by
  simp only [normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.I_re, Complex.I_im]
  ring

theorem norm_arcChartInv_lt_one_iff {ζ u : ℂ} (hζ : ‖ζ‖ = 1) (hu : I + u ≠ 0) :
    ‖arcChartInv ζ u‖ < 1 ↔ 0 < u.im := by
  have hpos : 0 < ‖I + u‖ := norm_pos_iff.mpr hu
  rw [arcChartInv, mul_div_assoc, norm_mul, hζ, one_mul, norm_div, div_lt_one hpos,
    ← pow_lt_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  have h := normSq_I_add_sub_normSq_I_sub u
  constructor <;> intro h' <;> linarith

theorem norm_arcChartInv_le_one_iff {ζ u : ℂ} (hζ : ‖ζ‖ = 1) (hu : I + u ≠ 0) :
    ‖arcChartInv ζ u‖ ≤ 1 ↔ 0 ≤ u.im := by
  have hpos : 0 < ‖I + u‖ := norm_pos_iff.mpr hu
  rw [arcChartInv, mul_div_assoc, norm_mul, hζ, one_mul, norm_div, div_le_one hpos,
    ← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  have h := normSq_I_add_sub_normSq_I_sub u
  constructor <;> intro h' <;> linarith

theorem norm_arcChartInv_eq_one_iff {ζ u : ℂ} (hζ : ‖ζ‖ = 1) (hu : I + u ≠ 0) :
    ‖arcChartInv ζ u‖ = 1 ↔ u.im = 0 := by
  constructor
  · intro h
    have h1 : 0 ≤ u.im := (norm_arcChartInv_le_one_iff hζ hu).mp h.le
    have h2 : ¬ 0 < u.im := by
      rw [← norm_arcChartInv_lt_one_iff hζ hu, h]
      exact lt_irrefl _
    linarith [not_lt.mp h2]
  · intro h
    apply le_antisymm ((norm_arcChartInv_le_one_iff hζ hu).mpr h.symm.le)
    by_contra hlt
    push Not at hlt
    have := (norm_arcChartInv_lt_one_iff hζ hu).mp hlt
    linarith

/-- The inverse chart intertwines conjugation with reflection in the circle. -/
theorem arcChartInv_conj {ζ u : ℂ} (hζ : ‖ζ‖ = 1) (_hu : I + u ≠ 0) (hu' : I + conj u ≠ 0)
    (hu'' : I - conj u ≠ 0) :
    arcChartInv ζ (conj u) = circleReflect (arcChartInv ζ u) := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  have hζc : conj ζ = ζ⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]
    simp
  have h1 : -I + conj u ≠ 0 := by
    intro h
    apply hu''
    linear_combination -h
  have h2 : -I - conj u ≠ 0 := by
    intro h
    apply hu'
    linear_combination -h
  unfold circleReflect arcChartInv
  rw [map_div₀, map_mul, map_sub, map_add, conj_I, hζc]
  field_simp
  ring

/-- **Schwarz reflection at a point of the arc.**  With `F z = f z` on the closed disc and
`F z = (f (1/z*))*` outside, `F` is differentiable at every point `ζ ∈ A`: the segment version,
applied to `f ∘ arcChartInv ζ` on a small ball, is transported back by `arcChart ζ`. -/
theorem differentiableAt_circleReflectExtend_of_mem_arc {U A : Set ℂ}
    (hUA : IsCircleSymmetricNbhd U A) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U ∩ unitDisc))
    (hcont : ContinuousOn f ((U ∩ unitDisc) ∪ A)) (hreal : ∀ z ∈ A, (f z).im = 0)
    {ζ : ℂ} (hζU : ζ ∈ U) (hζ : ‖ζ‖ = 1) :
    DifferentiableAt ℂ (fun z => if ‖z‖ ≤ 1 then f z else conj (f (circleReflect z))) ζ := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  -- a radius `ρ ≤ 1/2` with `arcChartInv ζ '' ball 0 ρ ⊆ U`
  have hS0 : ContinuousAt (arcChartInv ζ) 0 := continuousAt_arcChartInv (by simp)
  have hUnhds : U ∈ 𝓝 (arcChartInv ζ 0) := by
    rw [arcChartInv_zero]
    exact hUA.isOpen.mem_nhds hζU
  obtain ⟨ρ₀, hρ₀, hρ₀U⟩ := Metric.mem_nhds_iff.mp (hS0.preimage_mem_nhds hUnhds)
  set ρ : ℝ := min ρ₀ (1 / 2) with hρ
  have hρpos : 0 < ρ := lt_min hρ₀ (by norm_num)
  have hρle : ρ ≤ 1 / 2 := min_le_right _ _
  have hSU : ∀ u ∈ ball (0 : ℂ) ρ, arcChartInv ζ u ∈ U := fun u hu =>
    hρ₀U (ball_subset_ball (min_le_left _ _) hu)
  have hsmall : ∀ u ∈ ball (0 : ℂ) ρ, ‖u‖ < 1 := fun u hu => by
    have := mem_ball_zero_iff.mp hu
    linarith
  have hIu : ∀ u ∈ ball (0 : ℂ) ρ, I + u ≠ 0 := fun u hu =>
    add_I_ne_zero_of_norm_lt_one (hsmall u hu)
  have hIu' : ∀ u ∈ ball (0 : ℂ) ρ, I + conj u ≠ 0 := fun u hu =>
    add_I_ne_zero_of_norm_lt_one (by rw [Complex.norm_conj]; exact hsmall u hu)
  have hIu'' : ∀ u ∈ ball (0 : ℂ) ρ, I - conj u ≠ 0 := fun u hu =>
    sub_I_ne_zero_of_norm_lt_one (by rw [Complex.norm_conj]; exact hsmall u hu)
  have hSdisc : ∀ u ∈ ball (0 : ℂ) ρ, 0 < u.im → arcChartInv ζ u ∈ U ∩ unitDisc := fun u hu him =>
    ⟨hSU u hu, mem_ball_zero_iff.mpr ((norm_arcChartInv_lt_one_iff hζ (hIu u hu)).mpr him)⟩
  have hSarc : ∀ u ∈ ball (0 : ℂ) ρ, u.im = 0 → arcChartInv ζ u ∈ A := fun u hu him => by
    rw [← hUA.inter_sphere]
    exact ⟨hSU u hu, mem_sphere_zero_iff_norm.mpr ((norm_arcChartInv_eq_one_iff hζ (hIu u hu)).mpr him)⟩
  -- the segment reflection for `G := f ∘ arcChartInv ζ` on the ball
  set G : ℂ → ℂ := fun u => f (arcChartInv ζ u) with hG
  have hGdiff : DifferentiableOn ℂ G (upperPart (ball 0 ρ)) := by
    intro u hu
    have hu' : u ∈ ball (0 : ℂ) ρ ∧ 0 < u.im := hu
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (hf.differentiableAt ((hUA.isOpen.inter isOpen_ball).mem_nhds (hSdisc u hu'.1 hu'.2))).comp
      u (differentiableAt_arcChartInv (hIu u hu'.1))
  have hGcont : ContinuousOn G (upperPart (ball 0 ρ) ∪ realPart (ball 0 ρ)) := by
    refine hcont.comp (f := arcChartInv ζ) ?_ ?_
    · intro u hu
      have hu' : u ∈ ball (0 : ℂ) ρ := by
        rcases hu with h | h
        · exact (show u ∈ ball (0 : ℂ) ρ ∧ 0 < u.im from h).1
        · exact (show u ∈ ball (0 : ℂ) ρ ∧ u.im = 0 from h).1
      exact (continuousAt_arcChartInv (hIu u hu')).continuousWithinAt
    · intro u hu
      rcases hu with h | h
      · have h' : u ∈ ball (0 : ℂ) ρ ∧ 0 < u.im := h
        exact Or.inl (hSdisc u h'.1 h'.2)
      · have h' : u ∈ ball (0 : ℂ) ρ ∧ u.im = 0 := h
        exact Or.inr (hSarc u h'.1 h'.2)
  have hGreal : ∀ u ∈ realPart (ball 0 ρ), (G u).im = 0 := by
    intro u hu
    have h' : u ∈ ball (0 : ℂ) ρ ∧ u.im = 0 := hu
    exact hreal _ (hSarc u h'.1 h'.2)
  have hRG := schwarz_reflection_segment (isRealSymmetric_ball ρ) hGdiff hGcont hGreal
  -- `F = reflectExtend G ∘ arcChart ζ` on the open set `W ∋ ζ`
  have hzζ : ∀ z ∈ ball ζ 1, ζ + z ≠ 0 := by
    intro z hz h
    rw [mem_ball, dist_eq_norm] at hz
    have hzeq : z = -ζ := by linear_combination h
    rw [hzeq] at hz
    have h2 : -ζ - ζ = -(2 * ζ) := by ring
    rw [h2, norm_neg, norm_mul, RCLike.norm_two, hζ] at hz
    linarith
  have hTζ : DifferentiableAt ℂ (arcChart ζ) ζ :=
    differentiableAt_arcChart (hzζ ζ (mem_ball_self one_pos))
  have hW : IsOpen (ball ζ 1 ∩ arcChart ζ ⁻¹' ball 0 ρ) := by
    refine ContinuousOn.isOpen_inter_preimage ?_ isOpen_ball isOpen_ball
    intro z hz
    exact (differentiableAt_arcChart (hzζ z hz)).continuousAt.continuousWithinAt
  have hζW : ζ ∈ ball ζ 1 ∩ arcChart ζ ⁻¹' ball 0 ρ := by
    refine ⟨mem_ball_self one_pos, ?_⟩
    show arcChart ζ ζ ∈ ball 0 ρ
    rw [arcChart_self]
    exact mem_ball_self hρpos
  have hcomp : DifferentiableAt ℂ (reflectExtend G ∘ arcChart ζ) ζ := by
    refine DifferentiableAt.comp ζ ?_ hTζ
    rw [arcChart_self]
    exact hRG.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hρpos))
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hW.mem_nhds hζW] with z hz
  obtain ⟨hz1, hzT⟩ := hz
  have hzT' : arcChart ζ z ∈ ball (0 : ℂ) ρ := hzT
  have hST : arcChartInv ζ (arcChart ζ z) = z := arcChartInv_arcChart hζ0 (hzζ z hz1)
  show (if ‖z‖ ≤ 1 then f z else conj (f (circleReflect z))) = reflectExtend G (arcChart ζ z)
  by_cases him : 0 ≤ (arcChart ζ z).im
  · rw [reflectExtend_eq_of_im_nonneg G him]
    have hle : ‖z‖ ≤ 1 := by
      rw [← hST]
      exact (norm_arcChartInv_le_one_iff hζ (hIu _ hzT')).mpr him
    rw [if_pos hle]
    show f z = f (arcChartInv ζ (arcChart ζ z))
    rw [hST]
  · push Not at him
    rw [reflectExtend_eq_of_im_neg G him]
    have hgt : 1 < ‖z‖ := by
      have h : ¬ ‖arcChartInv ζ (arcChart ζ z)‖ ≤ 1 := by
        rw [norm_arcChartInv_le_one_iff hζ (hIu _ hzT')]
        exact not_le.2 him
      rw [hST] at h
      exact not_le.1 h
    rw [if_neg (not_le.2 hgt)]
    show conj (f (circleReflect z)) = conj (f (arcChartInv ζ (conj (arcChart ζ z))))
    rw [arcChartInv_conj hζ (hIu _ hzT') (hIu' _ hzT') (hIu'' _ hzT'), hST]

/-! ### Basic facts: the symmetric neighbourhood of a small arc, and the chart in the values -/

theorem I_add_arcChart_ne_zero {a w : ℂ} (ha : a ≠ 0) (hw : a + w ≠ 0) :
    I + arcChart a w ≠ 0 := by
  have h : I + arcChart a w = 2 * I * a / (a + w) := by
    unfold arcChart
    field_simp
    ring
  rw [h]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) ha) hw

theorem I_sub_arcChart_ne_zero {a w : ℂ} (hw : a + w ≠ 0) (hw0 : w ≠ 0) :
    I - arcChart a w ≠ 0 := by
  have h : I - arcChart a w = 2 * I * w / (a + w) := by
    unfold arcChart
    field_simp
    ring
  rw [h]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hw0) hw

/-- For `ζ₀` on the circle and `0 < ρ < 1`, `ball ζ₀ ρ ∩ circleReflect ⁻¹' ball ζ₀ ρ` is a symmetric
neighbourhood of the arc `sphere 0 1 ∩ ball ζ₀ ρ`. -/
theorem isCircleSymmetricNbhd_ball_inter {ζ₀ : ℂ} (hζ₀ : ‖ζ₀‖ = 1) {ρ : ℝ} (_hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    IsCircleSymmetricNbhd (ball ζ₀ ρ ∩ circleReflect ⁻¹' ball ζ₀ ρ) (sphere 0 1 ∩ ball ζ₀ ρ) := by
  have hball0 : ∀ z ∈ ball ζ₀ ρ, z ≠ 0 := by
    intro z hz h0
    rw [h0, mem_ball, dist_zero_left, hζ₀] at hz
    linarith
  refine ⟨?_, ?_, ?_⟩
  · refine ContinuousOn.isOpen_inter_preimage ?_ isOpen_ball isOpen_ball
    intro z hz
    exact (continuousAt_circleReflect (hball0 z hz)).continuousWithinAt
  · ext z
    constructor
    · rintro ⟨⟨hz1, _⟩, hz2⟩
      exact ⟨hz2, hz1⟩
    · rintro ⟨hz1, hz2⟩
      refine ⟨⟨hz2, ?_⟩, hz1⟩
      show circleReflect z ∈ ball ζ₀ ρ
      rw [circleReflect_of_norm_eq_one (mem_sphere_zero_iff_norm.mp hz1)]
      exact hz2
  · rintro z ⟨hz1, hz2⟩
    refine ⟨hz2, ?_⟩
    show circleReflect (circleReflect z) ∈ ball ζ₀ ρ
    rw [circleReflect_circleReflect (hball0 z hz1)]
    exact hz1

/-- **Unimodular arc reflection at a point of the arc.**  With `F z = f z` on the closed disc and
`F z = 1/(f (1/z*))*` outside, `F` is differentiable at every point `ζ₀ ∈ A`: the chart
`arcChart (f ζ₀)` in the values turns `f` into a function with real boundary values near `ζ₀`,
to which `differentiableAt_circleReflectExtend_of_mem_arc` applies. -/
theorem differentiableAt_circleReflectExtend_norm_one_of_mem_arc {U A : Set ℂ}
    (hUA : IsCircleSymmetricNbhd U A) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U ∩ unitDisc))
    (hcont : ContinuousOn f ((U ∩ unitDisc) ∪ A)) (hnorm : ∀ z ∈ A, ‖f z‖ = 1)
    {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ A) :
    DifferentiableAt ℂ
      (fun z => if ‖z‖ ≤ 1 then f z else circleReflect (f (circleReflect z))) ζ₀ := by
  have hζ₀' : ζ₀ ∈ U ∩ sphere (0 : ℂ) 1 := by
    rw [hUA.inter_sphere]
    exact hζ₀
  have hζ₀U : ζ₀ ∈ U := hζ₀'.1
  have hζ₀n : ‖ζ₀‖ = 1 := mem_sphere_zero_iff_norm.mp hζ₀'.2
  set a : ℂ := f ζ₀ with ha
  have han : ‖a‖ = 1 := hnorm ζ₀ hζ₀
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at han
    exact zero_ne_one han
  -- a radius `ρ < 1` with `ball ζ₀ ρ ⊆ U` and `‖f z - a‖ < 1` on `ball ζ₀ ρ ∩ ((U ∩ Δ) ∪ A)`
  have hcζ : ContinuousWithinAt f ((U ∩ unitDisc) ∪ A) ζ₀ := hcont ζ₀ (Or.inr hζ₀)
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.mp hcζ 1 one_pos
  obtain ⟨δ', hδ', hδ'U⟩ := Metric.isOpen_iff.mp hUA.isOpen ζ₀ hζ₀U
  set ρ : ℝ := min (min δ δ') (1 / 2) with hρ
  have hρ0 : 0 < ρ := lt_min (lt_min hδ hδ') (by norm_num)
  have hρ1 : ρ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hρδ : ρ ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hρδ' : ρ ≤ δ' := (min_le_left _ _).trans (min_le_right _ _)
  have hballU : ball ζ₀ ρ ⊆ U := (ball_subset_ball hρδ').trans hδ'U
  have hnear : ∀ z ∈ ball ζ₀ ρ, z ∈ (U ∩ unitDisc) ∪ A → ‖f z - a‖ < 1 := by
    intro z hz hzs
    have h := hδf hzs ((mem_ball.mp hz).trans_le hρδ)
    rwa [dist_eq_norm] at h
  have hU'A' := isCircleSymmetricNbhd_ball_inter hζ₀n hρ0 hρ1
  set U' : Set ℂ := ball ζ₀ ρ ∩ circleReflect ⁻¹' ball ζ₀ ρ with hU'
  set A' : Set ℂ := sphere 0 1 ∩ ball ζ₀ ρ with hA'
  have hU'U : U' ⊆ U := fun z hz => hballU hz.1
  have hA'A : A' ⊆ A := by
    intro z hz
    rw [← hUA.inter_sphere]
    exact ⟨hballU hz.2, hz.1⟩
  have hsub : (U' ∩ unitDisc) ∪ A' ⊆ (U ∩ unitDisc) ∪ A :=
    Set.union_subset_union (Set.inter_subset_inter_left _ hU'U) hA'A
  have hball : ∀ z ∈ (U' ∩ unitDisc) ∪ A', z ∈ ball ζ₀ ρ := by
    intro z hz
    rcases hz with h | h
    · exact h.1.1
    · exact h.2
  -- on `(U' ∩ Δ) ∪ A'` the values of `f` avoid `0` and `-a`
  have hgood : ∀ z ∈ (U' ∩ unitDisc) ∪ A', f z ≠ 0 ∧ a + f z ≠ 0 := by
    intro z hz
    have h1 := hnear z (hball z hz) (hsub hz)
    constructor
    · intro h0
      rw [h0, zero_sub, norm_neg, han] at h1
      exact lt_irrefl _ h1
    · intro h0
      have h2 : f z - a = -(2 * a) := by linear_combination h0
      rw [h2, norm_neg, norm_mul, RCLike.norm_two, han] at h1
      linarith
  -- `g := arcChart a ∘ f` has real boundary values on `A'`
  set g : ℂ → ℂ := fun z => arcChart a (f z) with hg
  have hgd : DifferentiableOn ℂ g (U' ∩ unitDisc) := by
    intro z hz
    have hz' : z ∈ U ∩ unitDisc := ⟨hU'U hz.1, hz.2⟩
    exact ((differentiableAt_arcChart (hgood z (Or.inl hz)).2).comp z
      (hf.differentiableAt ((hUA.isOpen.inter isOpen_ball).mem_nhds hz'))).differentiableWithinAt
  have hgc : ContinuousOn g ((U' ∩ unitDisc) ∪ A') := by
    intro z hz
    exact (differentiableAt_arcChart (hgood z hz).2).continuousAt.comp_continuousWithinAt
      ((hcont z (hsub hz)).mono hsub)
  have hgreal : ∀ z ∈ A', (g z).im = 0 := by
    intro z hz
    have hz' : ‖f z‖ = 1 := hnorm z (hA'A hz)
    have hw := hgood z (Or.inr hz)
    have hI : I + arcChart a (f z) ≠ 0 := I_add_arcChart_ne_zero ha0 hw.2
    have h1 : ‖arcChartInv a (arcChart a (f z))‖ = 1 := by
      rw [arcChartInv_arcChart ha0 hw.2, hz']
    exact (norm_arcChartInv_eq_one_iff han hI).mp h1
  have hζ₀U' : ζ₀ ∈ U' := by
    refine ⟨mem_ball_self hρ0, ?_⟩
    show circleReflect ζ₀ ∈ ball ζ₀ ρ
    rw [circleReflect_of_norm_eq_one hζ₀n]
    exact mem_ball_self hρ0
  have hG := differentiableAt_circleReflectExtend_of_mem_arc hU'A' hgd hgc hgreal hζ₀U' hζ₀n
  set G : ℂ → ℂ := fun z => if ‖z‖ ≤ 1 then g z else conj (g (circleReflect z)) with hGdef
  have hGζ₀ : G ζ₀ = 0 := by
    show (if ‖ζ₀‖ ≤ 1 then g ζ₀ else conj (g (circleReflect ζ₀))) = 0
    rw [if_pos hζ₀n.le]
    show arcChart a (f ζ₀) = 0
    rw [← ha, arcChart_self]
  have hcomp : DifferentiableAt ℂ (arcChartInv a ∘ G) ζ₀ := by
    refine DifferentiableAt.comp ζ₀ ?_ hG
    rw [hGζ₀]
    exact differentiableAt_arcChartInv (by simp)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hU'A'.isOpen.mem_nhds hζ₀U'] with z hz
  show (if ‖z‖ ≤ 1 then f z else circleReflect (f (circleReflect z))) = arcChartInv a (G z)
  by_cases hle : ‖z‖ ≤ 1
  · rw [if_pos hle]
    show f z = arcChartInv a (if ‖z‖ ≤ 1 then g z else conj (g (circleReflect z)))
    rw [if_pos hle]
    show f z = arcChartInv a (arcChart a (f z))
    have hzs : z ∈ (U' ∩ unitDisc) ∪ A' := by
      rcases lt_or_eq_of_le hle with h | h
      · exact Or.inl ⟨hz, mem_ball_zero_iff.mpr h⟩
      · exact Or.inr ⟨mem_sphere_zero_iff_norm.mpr h, hz.1⟩
    rw [arcChartInv_arcChart ha0 (hgood z hzs).2]
  · rw [if_neg hle]
    show circleReflect (f (circleReflect z))
      = arcChartInv a (if ‖z‖ ≤ 1 then g z else conj (g (circleReflect z)))
    rw [if_neg hle]
    have hgt : 1 < ‖z‖ := not_le.mp hle
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hgt
      linarith
    have hzr : circleReflect z ∈ U' ∩ unitDisc := by
      refine ⟨⟨hz.2, ?_⟩, ?_⟩
      · show circleReflect (circleReflect z) ∈ ball ζ₀ ρ
        rw [circleReflect_circleReflect hz0]
        exact hz.1
      · show circleReflect z ∈ ball 0 1
        rw [mem_ball_zero_iff, norm_circleReflect]
        exact inv_lt_one_of_one_lt₀ hgt
    have hw := hgood _ (Or.inl hzr)
    have hI := I_add_arcChart_ne_zero ha0 hw.2
    have hI' := I_sub_arcChart_ne_zero hw.2 hw.1
    have hc1 : I + conj (arcChart a (f (circleReflect z))) ≠ 0 := by
      intro h
      apply hI'
      have h' := congrArg conj h
      rw [map_add, conj_I, conj_conj, map_zero] at h'
      linear_combination -h'
    have hc2 : I - conj (arcChart a (f (circleReflect z))) ≠ 0 := by
      intro h
      apply hI
      have h' := congrArg conj h
      rw [map_sub, conj_I, conj_conj, map_zero] at h'
      linear_combination -h'
    show circleReflect (f (circleReflect z))
      = arcChartInv a (conj (arcChart a (f (circleReflect z))))
    rw [arcChartInv_conj han hI hc1 hc2, arcChartInv_arcChart ha0 hw.2]

/-- **Arc version, unimodular boundary values.**  If `|f| = 1` on `A`, then `f` extends
holomorphically across `A` (by `1 / (f (circleReflect z))*` outside the disc) on some neighbourhood
of `A`. -/
theorem schwarz_reflection_arc_norm_one {U A : Set ℂ} (hUA : IsCircleSymmetricNbhd U A)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U ∩ unitDisc))
    (hcont : ContinuousOn f ((U ∩ unitDisc) ∪ A)) (hnorm : ∀ z ∈ A, ‖f z‖ = 1) :
    ∃ V : Set ℂ, IsOpen V ∧ A ⊆ V ∧ V ⊆ U ∧
      ∃ F : ℂ → ℂ, DifferentiableOn ℂ F V ∧ EqOn F f (V ∩ unitDisc) := by
  have hAn : ∀ ζ ∈ A, ‖ζ‖ = 1 := by
    intro ζ hζ
    rw [← hUA.inter_sphere] at hζ
    exact mem_sphere_zero_iff_norm.mp hζ.2
  have hAU : ∀ ζ ∈ A, ζ ∈ U := by
    intro ζ hζ
    rw [← hUA.inter_sphere] at hζ
    exact hζ.1
  -- for each `ζ ∈ A` a radius on which `f` does not vanish inside the disc
  have hloc : ∀ ζ ∈ A, ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ball ζ ρ ⊆ U ∧
      ∀ z ∈ ball ζ ρ ∩ (U ∩ unitDisc), f z ≠ 0 := by
    intro ζ hζ
    have hcζ : ContinuousWithinAt f ((U ∩ unitDisc) ∪ A) ζ := hcont ζ (Or.inr hζ)
    obtain ⟨δ, hδ, hδf⟩ := Metric.continuousWithinAt_iff.mp hcζ 1 one_pos
    obtain ⟨δ', hδ', hδ'U⟩ := Metric.isOpen_iff.mp hUA.isOpen ζ (hAU ζ hζ)
    refine ⟨min (min δ δ') (1 / 2), lt_min (lt_min hδ hδ') (by norm_num),
      (min_le_right _ _).trans_lt (by norm_num),
      (ball_subset_ball ((min_le_left _ _).trans (min_le_right _ _))).trans hδ'U, ?_⟩
    rintro z ⟨hz, hzU⟩ h0
    have h := hδf (Or.inl hzU)
      ((mem_ball.mp hz).trans_le ((min_le_left _ _).trans (min_le_left _ _)))
    rw [dist_eq_norm, h0, zero_sub, norm_neg, hnorm ζ hζ] at h
    exact lt_irrefl _ h
  choose! ρ hρ using hloc
  -- the neighbourhood `V` of `A`
  set V : Set ℂ := ⋃ ζ ∈ A, (ball ζ (ρ ζ) ∩ circleReflect ⁻¹' ball ζ (ρ ζ)) with hV
  have hVo : IsOpen V := isOpen_biUnion fun ζ hζ =>
    (isCircleSymmetricNbhd_ball_inter (hAn ζ hζ) (hρ ζ hζ).1 (hρ ζ hζ).2.1).isOpen
  have hAV : A ⊆ V := by
    intro ζ hζ
    refine Set.mem_biUnion hζ ⟨mem_ball_self (hρ ζ hζ).1, ?_⟩
    show circleReflect ζ ∈ ball ζ (ρ ζ)
    rw [circleReflect_of_norm_eq_one (hAn ζ hζ)]
    exact mem_ball_self (hρ ζ hζ).1
  have hVU : V ⊆ U := Set.iUnion₂_subset fun ζ hζ z hz => (hρ ζ hζ).2.2.1 hz.1
  refine ⟨V, hVo, hAV, hVU,
    fun z => if ‖z‖ ≤ 1 then f z else circleReflect (f (circleReflect z)), ?_, ?_⟩
  · intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    obtain ⟨ζ, hζ, hzζ⟩ := Set.mem_iUnion₂.mp hz
    rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
    · -- interior points: `F = f` near `z`
      have hmem : U ∩ unitDisc ∈ 𝓝 z :=
        (hUA.isOpen.inter isOpen_ball).mem_nhds ⟨hVU hz, mem_ball_zero_iff.mpr hlt⟩
      refine (hf.differentiableAt hmem).congr_of_eventuallyEq ?_
      filter_upwards [hmem] with w hw
      exact if_pos (mem_ball_zero_iff.mp hw.2).le
    · -- points of the arc
      have hzA : z ∈ A := by
        rw [← hUA.inter_sphere]
        exact ⟨hVU hz, mem_sphere_zero_iff_norm.mpr heq⟩
      exact differentiableAt_circleReflectExtend_norm_one_of_mem_arc hUA hf hcont hnorm hzA
    · -- exterior points: `f (circleReflect z) ≠ 0`, and `F = 1/(f ∘ circleReflect)*` near `z`
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [norm_zero] at hgt
        linarith
      have hcr : circleReflect z ∈ ball ζ (ρ ζ) ∩ (U ∩ unitDisc) := by
        refine ⟨hzζ.2, (hρ ζ hζ).2.2.1 hzζ.2, mem_ball_zero_iff.mpr ?_⟩
        rw [norm_circleReflect]
        exact inv_lt_one_of_one_lt₀ hgt
      have hfne : f (circleReflect z) ≠ 0 := (hρ ζ hζ).2.2.2 _ hcr
      have hfd : DifferentiableAt ℂ f (conj (1 / z)) := by
        rw [map_div₀, map_one]
        exact hf.differentiableAt ((hUA.isOpen.inter isOpen_ball).mem_nhds hcr.2)
      have hcc := hfd.conj_conj
      rw [conj_conj] at hcc
      have hinv : DifferentiableAt ℂ (fun w : ℂ => 1 / w) z :=
        (differentiableAt_const (1 : ℂ)).div differentiableAt_id hz0
      have hd1 : DifferentiableAt ℂ ((conj ∘ f ∘ conj) ∘ fun w : ℂ => 1 / w) z := hcc.comp z hinv
      have hne' : ((conj ∘ f ∘ conj) ∘ fun w : ℂ => 1 / w) z ≠ 0 := by
        show conj (f (conj (1 / z))) ≠ 0
        rw [map_div₀, map_one]
        intro h
        apply hfne
        have h' := congrArg conj h
        rwa [conj_conj, map_zero] at h'
      have hinv2 : DifferentiableAt ℂ (fun v : ℂ => 1 / v)
          (((conj ∘ f ∘ conj) ∘ fun w : ℂ => 1 / w) z) :=
        (differentiableAt_const (1 : ℂ)).div differentiableAt_id hne'
      have hd : DifferentiableAt ℂ
          ((fun v : ℂ => 1 / v) ∘ ((conj ∘ f ∘ conj) ∘ fun w : ℂ => 1 / w)) z :=
        hinv2.comp z hd1
      have hopen : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hgt] with w hw
      show (if ‖w‖ ≤ 1 then f w else circleReflect (f (circleReflect w)))
        = 1 / conj (f (conj (1 / w)))
      rw [if_neg (not_le.2 hw), circleReflect, circleReflect, map_div₀, map_one]
  · intro z hz
    exact if_pos (mem_ball_zero_iff.mp hz.2).le

/-- **Arc version, real boundary values.**  The extension is `(f (circleReflect z))*` outside the
disc. -/
theorem schwarz_reflection_arc_real {U A : Set ℂ} (hUA : IsCircleSymmetricNbhd U A) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U ∩ unitDisc)) (hcont : ContinuousOn f ((U ∩ unitDisc) ∪ A))
    (hreal : ∀ z ∈ A, (f z).im = 0) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧ EqOn F f (U ∩ unitDisc) := by
  refine ⟨fun z => if ‖z‖ ≤ 1 then f z else conj (f (circleReflect z)), ?_, ?_⟩
  · intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    rcases lt_trichotomy ‖z‖ 1 with hlt | heq | hgt
    · -- interior points: `F = f` near `z`
      have hmem : U ∩ unitDisc ∈ 𝓝 z :=
        (hUA.isOpen.inter isOpen_ball).mem_nhds ⟨hz, mem_ball_zero_iff.mpr hlt⟩
      refine (hf.differentiableAt hmem).congr_of_eventuallyEq ?_
      filter_upwards [hmem] with w hw
      exact if_pos (mem_ball_zero_iff.mp hw.2).le
    · -- points of the arc
      exact differentiableAt_circleReflectExtend_of_mem_arc hUA hf hcont hreal hz heq
    · -- exterior points: `F = (f ∘ circleReflect)*` near `z`
      have hz0 : z ≠ 0 := by
        rintro rfl
        rw [norm_zero] at hgt
        linarith
      have hcr : circleReflect z ∈ U ∩ unitDisc := by
        refine ⟨hUA.invariant z hz, mem_ball_zero_iff.mpr ?_⟩
        rw [norm_circleReflect]
        exact inv_lt_one_of_one_lt₀ hgt
      have hfd : DifferentiableAt ℂ f (conj (1 / z)) := by
        rw [map_div₀, map_one]
        exact hf.differentiableAt ((hUA.isOpen.inter isOpen_ball).mem_nhds hcr)
      have hcc := hfd.conj_conj
      rw [conj_conj] at hcc
      have hinv : DifferentiableAt ℂ (fun w : ℂ => 1 / w) z :=
        (differentiableAt_const (1 : ℂ)).div differentiableAt_id hz0
      have hd : DifferentiableAt ℂ ((conj ∘ f ∘ conj) ∘ fun w : ℂ => 1 / w) z := hcc.comp z hinv
      have hopen : IsOpen {w : ℂ | 1 < ‖w‖} := isOpen_lt continuous_const continuous_norm
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [hopen.mem_nhds hgt] with w hw
      show (if ‖w‖ ≤ 1 then f w else conj (f (circleReflect w))) = conj (f (conj (1 / w)))
      rw [if_neg (not_le.2 hw), circleReflect, map_div₀, map_one]
  · intro z hz
    exact if_pos (mem_ball_zero_iff.mp hz.2).le

/-- A nontrivial preconnected subset of the unit circle contains a nondegenerate arc: some
`sphere 0 1 ∩ ball ζ₀ ρ` with `ζ₀ ∈ A` and `0 < ρ < 1`. -/
theorem exists_arc_subset_of_nontrivial {A : Set ℂ} (hA : A ⊆ sphere (0 : ℂ) 1)
    (hAne : A.Nontrivial) (hAconn : IsPreconnected A) :
    ∃ ζ₀ ∈ A, ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ sphere (0 : ℂ) 1 ∩ ball ζ₀ ρ ⊆ A := by
  obtain ⟨a, ha, b, hb, hab⟩ := hAne
  by_cases hfull : sphere (0 : ℂ) 1 ⊆ A
  · exact ⟨a, ha, 1 / 2, by norm_num, by norm_num, fun z hz => hfull hz.1⟩
  obtain ⟨p, hp, hpA⟩ := Set.not_subset.mp hfull
  have hpn : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp hp
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hpn
  -- the angle coordinate `ψ z = arg (-z / p)`, continuous on the circle minus `p`
  set ψ : ℂ → ℝ := fun z => arg (-z / p) with hψ
  have hψdef : ∀ z, ψ z = arg (-z / p) := fun z => rfl
  have hrec : ∀ z, ‖z‖ = 1 → z = -p * exp ((ψ z : ℂ) * I) := by
    intro z hz
    have h := Complex.norm_mul_exp_arg_mul_I (-z / p)
    rw [norm_div, norm_neg, hz, hpn, div_one, Complex.ofReal_one, one_mul] at h
    rw [hψdef, h, neg_div, mul_neg, neg_mul, neg_neg, mul_div_assoc', mul_comm, mul_div_assoc,
      div_self hp0, mul_one]
  have hslit : ∀ z, ‖z‖ = 1 → z ≠ p → -z / p ∈ slitPlane := by
    intro z hz hzp
    rw [mem_slitPlane_iff_not_le_zero]
    intro hle
    obtain ⟨hre, him⟩ := Complex.le_def.mp hle
    rw [Complex.zero_re] at hre
    rw [Complex.zero_im] at him
    have hn : ‖-z / p‖ = 1 := by rw [norm_div, norm_neg, hz, hpn, div_one]
    have h1 : normSq (-z / p) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hn]
      norm_num
    rw [normSq_apply, him, mul_zero, add_zero] at h1
    have hre' : (-z / p).re = -1 := by
      have h2 : ((-z / p).re + 1) * ((-z / p).re - 1) = 0 := by
        linear_combination h1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · linarith
      · linarith
    apply hzp
    have h4 : -z / p = -1 := Complex.ext (by rw [hre']; norm_num) (by rw [him]; norm_num)
    rw [div_eq_iff hp0] at h4
    linear_combination -h4
  have hψcont : ∀ z, ‖z‖ = 1 → z ≠ p → ContinuousAt ψ z := by
    intro z hz hzp
    have h1 : ContinuousAt (fun z : ℂ => -z / p) z := by fun_prop
    exact ContinuousAt.comp (f := fun z : ℂ => -z / p) (Complex.continuousAt_arg (hslit z hz hzp)) h1
  have hψinj : ∀ z, ‖z‖ = 1 → ∀ z', ‖z'‖ = 1 → ψ z = ψ z' → z = z' := by
    intro z hz z' hz' h
    rw [hrec z hz, hrec z' hz', h]
  have hApre : ∀ z ∈ A, ‖z‖ = 1 ∧ z ≠ p := fun z hz =>
    ⟨mem_sphere_zero_iff_norm.mp (hA hz), fun h => hpA (h ▸ hz)⟩
  -- the image `ψ '' A` is an interval containing two distinct points
  have himg : IsPreconnected (ψ '' A) :=
    hAconn.image ψ fun z hz => (hψcont z (hApre z hz).1 (hApre z hz).2).continuousWithinAt
  have hord := isPreconnected_iff_ordConnected.mp himg
  have hab' : ψ a ≠ ψ b := fun h => hab (hψinj a (hApre a ha).1 b (hApre b hb).1 h)
  obtain ⟨θ₁, θ₂, hθ, hθ₁, hθ₂⟩ : ∃ θ₁ θ₂ : ℝ, θ₁ < θ₂ ∧ θ₁ ∈ ψ '' A ∧ θ₂ ∈ ψ '' A := by
    rcases lt_or_gt_of_ne hab' with h | h
    · exact ⟨ψ a, ψ b, h, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    · exact ⟨ψ b, ψ a, h, ⟨b, hb, rfl⟩, ⟨a, ha, rfl⟩⟩
  set θ₀ : ℝ := (θ₁ + θ₂) / 2 with hθ₀
  have hθ₀mem : θ₀ ∈ ψ '' A := hord.out hθ₁ hθ₂ ⟨by linarith, by linarith⟩
  obtain ⟨ζ₀, hζ₀A, hζ₀θ⟩ := hθ₀mem
  -- continuity of `ψ` at `ζ₀` gives the radius
  have hζ₀n := (hApre ζ₀ hζ₀A).1
  obtain ⟨δ, hδ, hδψ⟩ := Metric.continuousAt_iff.mp
    (hψcont ζ₀ hζ₀n (hApre ζ₀ hζ₀A).2) ((θ₂ - θ₁) / 2) (by linarith)
  refine ⟨ζ₀, hζ₀A, min δ (1 / 2), lt_min hδ (by norm_num), ?_, ?_⟩
  · exact (min_le_right _ _).trans_lt (by norm_num)
  · rintro z ⟨hz, hzb⟩
    have hzn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have hzδ : dist z ζ₀ < δ := (mem_ball.mp hzb).trans_le (min_le_left _ _)
    have h := hδψ hzδ
    rw [Real.dist_eq, hζ₀θ] at h
    have hmem : ψ z ∈ ψ '' A := by
      refine hord.out hθ₁ hθ₂ ?_
      rw [abs_lt] at h
      constructor <;> linarith [h.1, h.2]
    obtain ⟨z', hz'A, hz'ψ⟩ := hmem
    rw [hψinj z hzn z' (hApre z' hz'A).1 hz'ψ.symm]
    exact hz'A

/-- If `f` is holomorphic on `Δ`, continuous up to a nondegenerate boundary arc `A` and equal to `w`
on `A`, then `f ≡ w` (Step 4 of Theorem C2). -/
theorem eqOn_const_of_eqOn_const_on_arc {A : Set ℂ} (hA : A ⊆ sphere (0 : ℂ) 1)
    (hAne : A.Nontrivial) (hAconn : IsPreconnected A) {f : ℂ → ℂ} {w : ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) (hcont : ContinuousOn f (unitDisc ∪ A))
    (hconst : ∀ ζ ∈ A, f ζ = w) : EqOn f (fun _ => w) unitDisc := by
  -- Step 1: a nondegenerate arc `A' ⊆ A`
  obtain ⟨ζ₀, hζ₀A, ρ, hρ0, hρ1, harc⟩ := exists_arc_subset_of_nontrivial hA hAne hAconn
  have hζ₀ : ‖ζ₀‖ = 1 := mem_sphere_zero_iff_norm.mp (hA hζ₀A)
  have hζ₀0 : ζ₀ ≠ 0 := by
    rintro rfl
    simp at hζ₀
  -- Step 2: the symmetric neighbourhood `U` of `A'`
  set U : Set ℂ := ball ζ₀ ρ ∩ circleReflect ⁻¹' ball ζ₀ ρ with hU
  set A' : Set ℂ := sphere 0 1 ∩ ball ζ₀ ρ with hA'
  have hA'A : A' ⊆ A := harc
  have hball0 : ∀ z ∈ ball ζ₀ ρ, z ≠ 0 := by
    intro z hz h0
    rw [h0, mem_ball, dist_zero_left, hζ₀] at hz
    linarith
  have hUA : IsCircleSymmetricNbhd U A' := by
    refine ⟨?_, ?_, ?_⟩
    · refine ContinuousOn.isOpen_inter_preimage ?_ isOpen_ball isOpen_ball
      intro z hz
      exact (continuousAt_circleReflect (hball0 z hz)).continuousWithinAt
    · ext z
      constructor
      · rintro ⟨⟨hz1, _⟩, hz2⟩
        exact ⟨hz2, hz1⟩
      · rintro ⟨hz1, hz2⟩
        refine ⟨⟨hz2, ?_⟩, hz1⟩
        show circleReflect z ∈ ball ζ₀ ρ
        rw [circleReflect_of_norm_eq_one (mem_sphere_zero_iff_norm.mp hz1)]
        exact hz2
    · rintro z ⟨hz1, hz2⟩
      refine ⟨hz2, ?_⟩
      show circleReflect (circleReflect z) ∈ ball ζ₀ ρ
      rw [circleReflect_circleReflect (hball0 z hz1)]
      exact hz1
  have hζ₀U : ζ₀ ∈ U := by
    refine ⟨mem_ball_self hρ0, ?_⟩
    show circleReflect ζ₀ ∈ ball ζ₀ ρ
    rw [circleReflect_of_norm_eq_one hζ₀]
    exact mem_ball_self hρ0
  -- Step 2': reflect `g := f - w` across `A'`
  set g : ℂ → ℂ := fun z => f z - w with hg
  have hgd' : DifferentiableOn ℂ g unitDisc := hf.sub_const w
  have hgd : DifferentiableOn ℂ g (U ∩ unitDisc) := hgd'.mono Set.inter_subset_right
  have hgc : ContinuousOn g ((U ∩ unitDisc) ∪ A') := by
    refine (hcont.mono ?_).sub continuousOn_const
    exact Set.union_subset_union Set.inter_subset_right hA'A
  have hgreal : ∀ z ∈ A', (g z).im = 0 := by
    intro z hz
    show (f z - w).im = 0
    rw [hconst z (hA'A hz), sub_self, Complex.zero_im]
  obtain ⟨F, hFd, hFg⟩ := schwarz_reflection_arc_real hUA hgd hgc hgreal
  -- Step 3: `F = 0` on `A'`, by continuity from `U ∩ unitDisc`
  have hFzero : ∀ ξ ∈ A', F ξ = 0 := by
    intro ξ hξ
    have hξ' : ξ ∈ U ∩ sphere (0 : ℂ) 1 := by
      rw [hUA.inter_sphere]
      exact hξ
    have hξn : ‖ξ‖ = 1 := mem_sphere_zero_iff_norm.mp hξ'.2
    have hξ0 : ξ ≠ 0 := by
      rintro rfl
      simp at hξn
    -- `ξ` is a limit of points `(1 - 1/(n+1)) ξ` of `U ∩ unitDisc`
    set y : ℕ → ℂ := fun n => ((1 - 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * ξ with hy
    have hylim : Tendsto y atTop (𝓝 ξ) := by
      have h1 : Tendsto (fun n : ℕ => ((1 - 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 ((1 - 0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp
          (tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat)
      have h2 := h1.mul_const ξ
      have h3 : ((1 - 0 : ℝ) : ℂ) * ξ = ξ := by simp
      rw [h3] at h2
      exact h2
    have hyU : ∀ᶠ n in atTop, y n ∈ U := by
      have h1 : ∀ᶠ n in atTop, y n ∈ ball ζ₀ ρ :=
        hylim.eventually (isOpen_ball.mem_nhds hξ'.1.1)
      have h2 : ∀ᶠ n in atTop, circleReflect (y n) ∈ ball ζ₀ ρ := by
        have hc : Tendsto (fun n => circleReflect (y n)) atTop (𝓝 (circleReflect ξ)) :=
          ((continuousAt_circleReflect hξ0).tendsto).comp hylim
        exact hc.eventually (isOpen_ball.mem_nhds hξ'.1.2)
      filter_upwards [h1, h2] with n hn1 hn2
      exact ⟨hn1, hn2⟩
    have hyD : ∀ n, y n ∈ unitDisc := by
      intro n
      show ((1 - 1 / ((n : ℝ) + 1) : ℝ) : ℂ) * ξ ∈ ball 0 1
      have hn0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      rw [mem_ball_zero_iff, norm_mul, hξn, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
      linarith
    have hcl : ξ ∈ closure (U ∩ unitDisc) :=
      mem_closure_of_tendsto hylim (hyU.mono fun n hn => ⟨hn, hyD n⟩)
    haveI : (𝓝[U ∩ unitDisc] ξ).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
    have hFcont : ContinuousWithinAt F (U ∩ unitDisc) ξ :=
      (hFd ξ hξ'.1).continuousWithinAt.mono Set.inter_subset_left
    have hgcont : ContinuousWithinAt g (U ∩ unitDisc) ξ :=
      (hgc ξ (Or.inr hξ)).mono Set.subset_union_left
    have h1 : Tendsto F (𝓝[U ∩ unitDisc] ξ) (𝓝 (F ξ)) := hFcont.tendsto
    have h2 : Tendsto F (𝓝[U ∩ unitDisc] ξ) (𝓝 (g ξ)) := by
      refine hgcont.tendsto.congr' ?_
      exact eventually_nhdsWithin_of_forall fun z hz => (hFg hz).symm
    rw [tendsto_nhds_unique h1 h2]
    show f ξ - w = 0
    rw [hconst ξ (hA'A hξ), sub_self]
  -- Step 4: `A'` accumulates at `ζ₀`, so `F ≡ 0` near `ζ₀` by the identity theorem
  have hfreq : ∃ᶠ z in 𝓝[≠] ζ₀, F z = 0 := by
    set zs : ℕ → ℂ := fun n => ζ₀ * exp (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) with hzs
    have hlim : Tendsto zs atTop (𝓝 ζ₀) := by
      have h1 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop (𝓝 (((0 : ℝ) : ℂ) * I)) :=
        ((Complex.continuous_ofReal.tendsto _).comp tendsto_one_div_add_atTop_nhds_zero_nat).mul_const I
      have h2 := (Complex.continuous_exp.tendsto _).comp h1
      have h3 := h2.const_mul ζ₀
      have h4 : ζ₀ * exp (((0 : ℝ) : ℂ) * I) = ζ₀ := by simp
      rw [h4] at h3
      exact h3
    have hne : ∀ n, zs n ≠ ζ₀ := by
      intro n h
      have h' : exp (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) = 1 := by
        have h1 : ζ₀ * exp (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) = ζ₀ * 1 := by
          rw [mul_one]
          exact h
        exact mul_left_cancel₀ hζ₀0 h1
      have h2 := congrArg Complex.im h'
      rw [Complex.exp_ofReal_mul_I_im, Complex.one_im] at h2
      have hpos : 0 < Real.sin (1 / ((n : ℝ) + 1)) := by
        refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
        have : 1 / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
        linarith [Real.pi_gt_three]
      linarith
    have hsph : ∀ n, zs n ∈ sphere (0 : ℂ) 1 := by
      intro n
      show ζ₀ * exp (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) ∈ sphere 0 1
      rw [mem_sphere_zero_iff_norm, norm_mul, hζ₀, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hev : ∀ᶠ n in atTop, F (zs n) = 0 := by
      filter_upwards [hlim.eventually (isOpen_ball.mem_nhds (mem_ball_self hρ0))] with n hn
      exact hFzero _ ⟨hsph n, hn⟩
    have hlim' : Tendsto zs atTop (𝓝[≠] ζ₀) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun n => hne n⟩
    exact hlim'.frequently hev.frequently
  have hFan : AnalyticOnNhd ℂ F U := hFd.analyticOnNhd hUA.isOpen
  obtain ⟨ρ', hρ', hρ'U⟩ := Metric.isOpen_iff.mp hUA.isOpen ζ₀ hζ₀U
  have hFzeroB : EqOn F 0 (ball ζ₀ ρ') :=
    (hFan.mono hρ'U).eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_ball ζ₀ ρ').isPreconnected (mem_ball_self hρ') hfreq
  -- Step 5: transfer to `g` at the interior point `z₁ = (1 - t) ζ₀` and conclude
  set t : ℝ := min (ρ' / 2) (1 / 2) with ht
  have ht0 : 0 < t := lt_min (by positivity) (by norm_num)
  have ht1 : t ≤ 1 / 2 := min_le_right _ _
  have htρ : t < ρ' := (min_le_left _ _).trans_lt (by linarith)
  set z₁ : ℂ := ((1 - t : ℝ) : ℂ) * ζ₀ with hz₁
  have hz₁D : z₁ ∈ unitDisc := by
    show ((1 - t : ℝ) : ℂ) * ζ₀ ∈ ball 0 1
    rw [mem_ball_zero_iff, norm_mul, hζ₀, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
    linarith
  have hz₁B : z₁ ∈ ball ζ₀ ρ' := by
    rw [mem_ball, dist_eq_norm]
    have h : ((1 - t : ℝ) : ℂ) * ζ₀ - ζ₀ = -((t : ℂ) * ζ₀) := by
      push_cast
      ring
    rw [h, norm_neg, norm_mul, hζ₀, mul_one, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    exact htρ
  have hgan : AnalyticOnNhd ℂ g unitDisc := hgd'.analyticOnNhd isOpen_ball
  have hev : g =ᶠ[𝓝 z₁] 0 := by
    filter_upwards [(isOpen_ball.inter isOpen_ball).mem_nhds (show z₁ ∈ ball ζ₀ ρ' ∩ unitDisc from ⟨hz₁B, hz₁D⟩)]
      with z hz
    rw [← hFg ⟨hρ'U hz.1, hz.2⟩]
    exact hFzeroB hz.1
  have hgzero : EqOn g 0 unitDisc :=
    hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      hz₁D hev
  intro z hz
  exact sub_eq_zero.mp (hgzero hz)

end SchwarzReflection

/-! ## §2. The Hahn–Mazurkiewicz theorem -/

section HahnMazurkiewicz

/-- A Peano continuum: nonempty, compact, connected, locally connected, metrizable. -/
structure IsPeanoContinuum (X : Type*) [TopologicalSpace X] : Prop where
  nonempty : Nonempty X
  compactSpace : CompactSpace X
  connectedSpace : ConnectedSpace X
  locallyConnected : LocallyConnectedSpace X
  metrizable : TopologicalSpace.MetrizableSpace X

/-- **Hahn–Mazurkiewicz.**  A Hausdorff space is a continuous image of `[0, 1]` iff it is a Peano
continuum.

Not proved (kept as `sorry`): not in Mathlib (Cantor-set surjection and a decomposition argument). -/
theorem hahn_mazurkiewicz (X : Type*) [TopologicalSpace X] [T2Space X] :
    (∃ γ : ℝ → X, ContinuousOn γ (Icc 0 1) ∧ γ '' Icc 0 1 = univ) ↔ IsPeanoContinuum X := by
  sorry

/-- Hahn–Mazurkiewicz for a nonempty subset of `ℂ`. -/
theorem hahn_mazurkiewicz_subset {K : Set ℂ} (hne : K.Nonempty) :
    (∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) ∧ γ '' Icc 0 1 = K) ↔
      (IsCompact K ∧ IsPreconnected K ∧ LocallyConnectedSpace ↥K) := by
  constructor
  · rintro ⟨γ, hγc, hγK⟩
    -- reparametrize into the subtype `↥K` via the projection onto `[0, 1]`
    have hmem : ∀ t : ℝ, γ (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) ∈ K := fun t => by
      rw [← hγK]
      exact Set.mem_image_of_mem γ (Set.projIcc (0 : ℝ) 1 zero_le_one t).2
    set γ' : ℝ → ↥K := fun t => ⟨γ (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ), hmem t⟩ with hγ'
    have hγ'c : Continuous γ' := by
      refine Continuous.subtype_mk ?_ _
      exact hγc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
        fun t => (Set.projIcc (0 : ℝ) 1 zero_le_one t).2
    have hγ'img : γ' '' Icc 0 1 = univ := by
      apply Set.eq_univ_of_forall
      rintro ⟨x, hx⟩
      rw [← hγK] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      refine ⟨t, ht, ?_⟩
      apply Subtype.ext
      show γ (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) = γ t
      rw [Set.projIcc_of_mem _ ht]
    have hP := (hahn_mazurkiewicz ↥K).mp ⟨γ', hγ'c.continuousOn, hγ'img⟩
    refine ⟨isCompact_iff_compactSpace.mpr hP.compactSpace, ?_, hP.locallyConnected⟩
    haveI := hP.connectedSpace
    exact isPreconnected_iff_preconnectedSpace.mpr inferInstance
  · rintro ⟨hc, hp, hlc⟩
    haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hc
    haveI : ConnectedSpace ↥K := isConnected_iff_connectedSpace.mp ⟨hne, hp⟩
    have hP : IsPeanoContinuum ↥K := ⟨hne.to_subtype, inferInstance, inferInstance, hlc, inferInstance⟩
    obtain ⟨γ', hγ'c, hγ'img⟩ := (hahn_mazurkiewicz ↥K).mpr hP
    refine ⟨fun t => (γ' t : ℂ), continuous_subtype_val.comp_continuousOn hγ'c, ?_⟩
    rw [show (fun t => (γ' t : ℂ)) = Subtype.val ∘ γ' from rfl, Set.image_comp, hγ'img,
      Subtype.coe_image_univ]

/-- Continuous images of `[0, 1]` and of the unit circle are the same subsets of `ℂ`. -/
theorem image_interval_iff_image_circle {K : Set ℂ} :
    (∃ γ : ℝ → ℂ, ContinuousOn γ (Icc 0 1) ∧ γ '' Icc 0 1 = K) ↔
      (∃ γ : ℂ → ℂ, ContinuousOn γ (sphere 0 1) ∧ γ '' sphere 0 1 = K) := by
  constructor
  · rintro ⟨γ, hγc, hγK⟩
    -- project the circle onto `[0, 1]` by `z ↦ (1 + Re z) / 2`
    set p : ℂ → ℝ := fun z => (1 + z.re) / 2 with hp
    have hpdef : ∀ z, p z = (1 + z.re) / 2 := fun z => rfl
    have hpc : Continuous p := by
      rw [hp]
      fun_prop
    have hmaps : MapsTo p (sphere 0 1) (Icc 0 1) := by
      intro z hz
      rw [mem_sphere_zero_iff_norm] at hz
      have h := Complex.abs_re_le_norm z
      rw [hz, abs_le] at h
      rw [hpdef]
      constructor <;> linarith [h.1, h.2]
    have himg : p '' sphere 0 1 = Icc 0 1 := by
      apply Subset.antisymm hmaps.image_subset
      intro t ht
      set x : ℝ := 2 * t - 1 with hx
      have hx1 : x ^ 2 ≤ 1 := by
        rw [hx]
        nlinarith [ht.1, ht.2]
      have hsq : x ^ 2 + (1 - x ^ 2) = 1 := by ring
      refine ⟨(x : ℂ) + (Real.sqrt (1 - x ^ 2) : ℂ) * I, ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, Complex.norm_add_mul_I, Real.sq_sqrt (by linarith), hsq,
          Real.sqrt_one]
      · rw [hpdef]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        rw [hx]
        ring
    refine ⟨γ ∘ p, hγc.comp hpc.continuousOn hmaps, ?_⟩
    rw [Set.image_comp, himg, hγK]
  · rintro ⟨Γ, hΓc, hΓK⟩
    -- parametrize the circle by `t ↦ e^{2πit}`
    set c : ℝ → ℂ := fun t => circleMap 0 1 (2 * Real.pi * t) with hc
    have hcdef : ∀ t, c t = circleMap 0 1 (2 * Real.pi * t) := fun t => rfl
    have hcc : Continuous c := by
      rw [hc]
      exact (continuous_circleMap 0 1).comp (by fun_prop)
    have hmaps : MapsTo c (Icc 0 1) (sphere 0 1) := fun t _ =>
      circleMap_mem_sphere 0 zero_le_one _
    have himg : c '' Icc 0 1 = sphere 0 1 := by
      apply Subset.antisymm hmaps.image_subset
      intro z hz
      have hz' : z ∈ circleMap 0 1 '' Ioc 0 (2 * Real.pi) := by
        rw [image_circleMap_Ioc, abs_one]
        exact hz
      obtain ⟨θ, hθ, rfl⟩ := hz'
      have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      refine ⟨θ / (2 * Real.pi), ⟨div_nonneg hθ.1.le Real.two_pi_pos.le, ?_⟩, ?_⟩
      · rw [div_le_one Real.two_pi_pos]
        exact hθ.2
      · rw [hcdef]
        congr 1
        field_simp
    refine ⟨Γ ∘ c, hΓc.comp hcc.continuousOn hmaps, ?_⟩
    rw [Set.image_comp, himg, hΓK]

/-- Quotient maps preserve local connectedness. -/
theorem locallyConnectedSpace_of_isQuotientMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [LocallyConnectedSpace X] {q : X → Y} (hq : IsQuotientMap q) :
    LocallyConnectedSpace Y := by
  rw [locallyConnectedSpace_iff_connectedComponentIn_open]
  intro F hF y hy
  rw [← hq.isOpen_preimage, isOpen_iff_forall_mem_open]
  intro x hx
  have hqx : q x ∈ F := connectedComponentIn_subset _ _ hx
  refine ⟨connectedComponentIn (q ⁻¹' F) x, ?_, (hF.preimage hq.continuous).connectedComponentIn,
    mem_connectedComponentIn hqx⟩
  -- the image of the component of `x` lies in the component of `q x`, which is that of `y`
  have himg : q '' connectedComponentIn (q ⁻¹' F) x ⊆ connectedComponentIn F (q x) := by
    refine IsPreconnected.subset_connectedComponentIn ?_ ⟨x, mem_connectedComponentIn hqx, rfl⟩ ?_
    · exact isPreconnected_connectedComponentIn.image _ hq.continuous.continuousOn
    · rintro _ ⟨x', hx', rfl⟩
      exact connectedComponentIn_subset (q ⁻¹' F) x hx'
  rw [← connectedComponentIn_eq hx] at himg
  intro x' hx'
  exact himg ⟨x', hx', rfl⟩

/-! ### Basic facts: nested continua and the boundary of a conformal disc image -/

/-- The intersection of a decreasing sequence of compact preconnected subsets of a Hausdorff space
is preconnected. -/
theorem isPreconnected_iInter_of_antitone_isCompact {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : ℕ → Set X} (hd : ∀ n, K (n + 1) ⊆ K n) (hc : ∀ n, IsCompact (K n))
    (hp : ∀ n, IsPreconnected (K n)) : IsPreconnected (⋂ n, K n) := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hsuv hdisj
  set S : Set X := ⋂ n, K n with hS
  have hSc : IsCompact S :=
    (hc 0).of_isClosed_subset (isClosed_iInter fun n => (hc n).isClosed) (Set.iInter_subset _ 0)
  have hAc : IsCompact (S ∩ u) := hSc.inter_right hu
  have hBc : IsCompact (S ∩ v) := hSc.inter_right hv
  have hAB : Disjoint (S ∩ u) (S ∩ v) := by
    rw [Set.disjoint_left]
    intro x hxu hxv
    have h : x ∈ S ∩ (u ∩ v) := ⟨hxu.1, hxu.2, hxv.2⟩
    rw [hdisj] at h
    exact h
  by_cases hA : (S ∩ u).Nonempty
  · by_cases hB : (S ∩ v).Nonempty
    · exfalso
      obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact hAc hBc hAB
      -- no `Kₙ` lies in `U ∪ V`, so the sets `Kₙ \ (U ∪ V)` form a decreasing sequence of
      -- nonempty compact sets
      have hT : ∀ n, (K n \ (U ∪ V)).Nonempty := by
        intro n
        by_contra hcon
        rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hcon
        rcases (hp n).subset_or_subset hU hV hUV hcon with h | h
        · obtain ⟨x, hx⟩ := hB
          exact Set.disjoint_left.mp hUV (h (Set.iInter_subset _ n hx.1)) (hBV hx)
        · obtain ⟨x, hx⟩ := hA
          exact Set.disjoint_left.mp hUV (hAU hx) (h (Set.iInter_subset _ n hx.1))
      obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
        (fun n => K n \ (U ∪ V)) (fun n => Set.diff_subset_diff_left (hd n)) hT
        ((hc 0).diff (hU.union hV)) (fun n => (hc n).isClosed.sdiff (hU.union hV))
      rw [Set.mem_iInter] at hx
      have hxS : x ∈ S := Set.mem_iInter.mpr fun n => (hx n).1
      have hxUV : x ∉ U ∪ V := (hx 0).2
      rcases hsuv hxS with hxu | hxv
      · exact hxUV (Or.inl (hAU ⟨hxS, hxu⟩))
      · exact hxUV (Or.inr (hBV ⟨hxS, hxv⟩))
    · left
      intro x hx
      rcases hsuv hx with h | h
      · exact h
      · exact absurd ⟨x, hx, h⟩ hB
  · right
    intro x hx
    rcases hsuv hx with h | h
    · exact absurd ⟨x, hx, h⟩ hA
    · exact h

/-- An open annulus `{r₁ < |z| < r₂}` (with `0 ≤ r₁`) is preconnected: it is the image of
`Ioo r₁ r₂ × ℝ` under polar coordinates. -/
theorem isPreconnected_annulusOpen {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) :
    IsPreconnected {z : ℂ | r₁ < ‖z‖ ∧ ‖z‖ < r₂} := by
  have hmap : (fun p : ℝ × ℝ => (p.1 : ℂ) * exp ((p.2 : ℂ) * I)) '' (Ioo r₁ r₂ ×ˢ univ)
      = {z : ℂ | r₁ < ‖z‖ ∧ ‖z‖ < r₂} := by
    apply Subset.antisymm
    · rintro _ ⟨⟨ρ, θ⟩, ⟨hρ, -⟩, rfl⟩
      show r₁ < ‖(ρ : ℂ) * exp ((θ : ℂ) * I)‖ ∧ ‖(ρ : ℂ) * exp ((θ : ℂ) * I)‖ < r₂
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (h₁.trans hρ.1.le)]
      exact hρ
    · intro z hz
      exact ⟨(‖z‖, arg z), ⟨hz, mem_univ _⟩, Complex.norm_mul_exp_arg_mul_I z⟩
  rw [← hmap]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _
    (Continuous.continuousOn (by fun_prop))

/-- The boundary of a conformal image of the disc is preconnected: it is the intersection of the
decreasing compact preconnected sets `closure f({rₙ < |z| < 1})`, `rₙ ↑ 1`. -/
theorem isPreconnected_frontier_of_isConformalOnto {Ω : Set ℂ} (hbdd : Bornology.IsBounded Ω)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) : IsPreconnected (frontier Ω) := by
  have hΔ : IsOpen unitDisc := isOpen_ball
  have hΩo : IsOpen Ω := hf.isOpen hΔ
  have hfc : ContinuousOn f unitDisc := hf.1.continuousOn
  -- the radii `rₙ = 1 - 1/(n+2)`
  set r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hr
  have hrdef : ∀ n, r n = 1 - 1 / ((n : ℝ) + 2) := fun n => rfl
  have hr0 : ∀ n, 0 ≤ r n := fun n => by
    rw [hrdef]
    have : 1 / ((n : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith
  have hr1 : ∀ n, r n < 1 := fun n => by
    rw [hrdef]
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hrmono : ∀ n, r n ≤ r (n + 1) := fun n => by
    rw [hrdef, hrdef]
    push_cast
    have : 1 / ((n : ℝ) + 1 + 2) ≤ 1 / ((n : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hrlim : ∀ s : ℝ, s < 1 → ∃ n, s < r n := by
    intro s hs
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hs)
    refine ⟨n, ?_⟩
    rw [hrdef]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  -- the annuli `Aₙ` and the compact sets `Kₙ`
  set A : ℕ → Set ℂ := fun n => {z : ℂ | r n < ‖z‖ ∧ ‖z‖ < 1} with hA
  have hAdef : ∀ n, A n = {z : ℂ | r n < ‖z‖ ∧ ‖z‖ < 1} := fun n => rfl
  set K : ℕ → Set ℂ := fun n => closure (f '' A n) with hK
  have hKdef : ∀ n, K n = closure (f '' A n) := fun n => rfl
  have hAsub : ∀ n, A n ⊆ unitDisc := fun n z hz => mem_ball_zero_iff.mpr hz.2
  have hKsub : ∀ n, K n ⊆ closure Ω := fun n => by
    rw [hKdef]
    refine closure_mono ?_
    rw [← hf.2.2]
    exact Set.image_mono (hAsub n)
  have hKd : ∀ n, K (n + 1) ⊆ K n := fun n => by
    rw [hKdef, hKdef]
    exact closure_mono (Set.image_mono fun z hz => ⟨lt_of_le_of_lt (hrmono n) hz.1, hz.2⟩)
  have hKc : ∀ n, IsCompact (K n) := fun n => by
    rw [hKdef]
    exact isCompact_of_isClosed_isBounded isClosed_closure (hbdd.closure.subset (hKsub n))
  have hKp : ∀ n, IsPreconnected (K n) := fun n => by
    rw [hKdef]
    exact ((isPreconnected_annulusOpen (hr0 n)).image f (hfc.mono (hAsub n))).closure
  -- `frontier Ω = ⋂ Kₙ`
  have hfr : frontier Ω = ⋂ n, K n := by
    rw [hΩo.frontier_eq]
    apply Subset.antisymm
    · rintro w ⟨hwc, hwΩ⟩
      rw [Set.mem_iInter]
      intro n
      -- `Ω = f(Aₙ) ∪ f(closedBall 0 rₙ)`, and the second set is compact and inside `Ω`
      have hsplit : unitDisc = A n ∪ closedBall 0 (r n) := by
        ext z
        constructor
        · intro hz
          by_cases h : r n < ‖z‖
          · exact Or.inl ⟨h, mem_ball_zero_iff.mp hz⟩
          · exact Or.inr (mem_closedBall_zero_iff.mpr (not_lt.mp h))
        · rintro (h | h)
          · exact mem_ball_zero_iff.mpr h.2
          · exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp h) (hr1 n))
      have hcb : closedBall (0 : ℂ) (r n) ⊆ unitDisc := fun z hz =>
        mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hz) (hr1 n))
      have hcpt2 : IsCompact (f '' closedBall 0 (r n)) :=
        (isCompact_closedBall 0 (r n)).image_of_continuousOn (hfc.mono hcb)
      have h1 : closure Ω = closure (f '' A n) ∪ f '' closedBall 0 (r n) := by
        rw [← hf.2.2, hsplit, Set.image_union, closure_union, hcpt2.isClosed.closure_eq]
      rw [h1] at hwc
      rcases hwc with h | h
      · rw [hKdef]
        exact h
      · exfalso
        apply hwΩ
        rw [← hf.2.2]
        exact Set.image_mono hcb h
    · intro w hw
      rw [Set.mem_iInter] at hw
      refine ⟨(hKsub 0) (hw 0), ?_⟩
      intro hwΩ
      rw [← hf.2.2] at hwΩ
      obtain ⟨z₀, hz₀, rfl⟩ := hwΩ
      have hz₀n : ‖z₀‖ < 1 := mem_ball_zero_iff.mp hz₀
      -- `f(ball 0 rₙ)` is a neighbourhood of `f z₀` disjoint from `f(Aₙ)` once `‖z₀‖ < rₙ`
      obtain ⟨n, hn⟩ := hrlim ‖z₀‖ hz₀n
      have hnhds : f '' ball 0 (r n) ∈ 𝓝 (f z₀) :=
        hf.image_mem_nhds hΔ hz₀ (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hn))
      have hdisj : Disjoint (f '' ball 0 (r n)) (f '' A n) := by
        rw [Set.disjoint_left]
        rintro _ ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, heq⟩
        have hz₁n : ‖z₁‖ < r n := mem_ball_zero_iff.mp hz₁
        have h21 : z₂ = z₁ :=
          hf.2.1 (hAsub n hz₂) (mem_ball_zero_iff.mpr (lt_trans hz₁n (hr1 n))) heq
        rw [h21] at hz₂
        exact lt_irrefl _ (lt_trans hz₂.1 hz₁n)
      have hcl : f z₀ ∈ closure (f '' A n) := by
        rw [← hKdef]
        exact hw n
      rw [mem_closure_iff_nhds] at hcl
      obtain ⟨y, hy1, hy2⟩ := hcl _ hnhds
      exact Set.disjoint_left.mp hdisj hy1 hy2
  rw [hfr]
  exact isPreconnected_iInter_of_antitone_isCompact hKd hKc hKp

/-- The form used in Theorem C1: the boundary of a bounded simply connected domain (a conformal
image of the disc) is locally connected iff it is a curve. -/
theorem frontier_locallyConnected_iff_isCurve {Ω : Set ℂ} (hbdd : Bornology.IsBounded Ω)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    LocallyConnectedSpace ↥(frontier Ω) ↔
      ∃ γ : ℂ → ℂ, ContinuousOn γ (sphere 0 1) ∧ γ '' sphere 0 1 = frontier Ω := by
  -- the boundary is nonempty, compact and preconnected
  have hne : (frontier Ω).Nonempty := by
    rw [nonempty_frontier_iff]
    refine ⟨?_, ?_⟩
    · rw [← hf.2.2]
      exact ⟨f 0, 0, mem_ball_self one_pos, rfl⟩
    · intro huniv
      obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hbdd
      have h := hR (huniv ▸ mem_univ ((|R| + 1 : ℝ) : ℂ))
      rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
      linarith [le_abs_self R]
  have hcpt : IsCompact (frontier Ω) :=
    isCompact_of_isClosed_isBounded isClosed_frontier (hbdd.closure.subset frontier_subset_closure)
  have hpre : IsPreconnected (frontier Ω) := isPreconnected_frontier_of_isConformalOnto hbdd hf
  rw [← image_interval_iff_image_circle, hahn_mazurkiewicz_subset hne]
  constructor
  · intro hlc
    exact ⟨hcpt, hpre, hlc⟩
  · exact fun h => h.2.2

end HahnMazurkiewicz

/-! ## §3. Cluster sets

The cluster set is `clusterSet f unitDisc ζ = ⋂_{r > 0} closure f(Δ ∩ B(ζ, r))` from
`Lemmas/Caratheodory.lean`; closures are taken in `ℂ`, which loses nothing for bounded `f`. -/

section ClusterSets

/-- The cluster set is the set of cluster points of `f` along `𝓝[Δ] ζ`. -/
theorem clusterSet_unitDisc_eq_mapClusterPt (f : ℂ → ℂ) (ζ : ℂ) :
    clusterSet f unitDisc ζ = {w | MapClusterPt w (𝓝[unitDisc] ζ) f} := by
  ext w
  rw [mem_setOf_eq, MapClusterPt,
    ((Metric.nhdsWithin_basis_ball (x := ζ) (s := unitDisc)).map f).clusterPt_iff_forall_mem_closure]
  simp only [clusterSet, mem_iInter, gt_iff_lt]
  constructor
  · intro h ε hε
    rw [inter_comm]
    exact h ε hε
  · intro h r hr
    rw [inter_comm]
    exact h r hr

/-- The sequential description of the cluster set. -/
theorem mem_clusterSet_unitDisc_iff {f : ℂ → ℂ} {ζ w : ℂ} :
    w ∈ clusterSet f unitDisc ζ ↔
      ∃ z : ℕ → ℂ, (∀ n, z n ∈ unitDisc) ∧ Tendsto z atTop (𝓝 ζ) ∧
        Tendsto (fun n => f (z n)) atTop (𝓝 w) := by
  constructor
  · intro hw
    simp only [clusterSet, mem_iInter, gt_iff_lt] at hw
    have hpick : ∀ n : ℕ, ∃ z ∈ unitDisc ∩ ball ζ (1 / ((n : ℝ) + 1)),
        dist w (f z) < 1 / ((n : ℝ) + 1) := by
      intro n
      have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨y, ⟨z, hz, rfl⟩, hy⟩ := Metric.mem_closure_iff.1 (hw _ hn) _ hn
      exact ⟨z, hz, hy⟩
    choose z hz hdist using hpick
    have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine ⟨z, fun n => (hz n).1, ?_, ?_⟩
    · rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun n => dist_nonneg) (fun n => (mem_ball.1 (hz n).2).le) hlim
    · rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hlim
      rw [dist_comm]
      exact (hdist n).le
  · rintro ⟨z, hzD, hzζ, hfz⟩
    simp only [clusterSet, mem_iInter, gt_iff_lt]
    intro r hr
    refine mem_closure_of_tendsto hfz ?_
    filter_upwards [hzζ (ball_mem_nhds ζ hr)] with n hn
    exact ⟨z n, ⟨hzD n, hn⟩, rfl⟩

/-- For a bounded continuous `f` the cluster set at a boundary point is nonempty, compact and
connected. -/
theorem clusterSet_isCompact_isConnected {f : ℂ → ℂ} {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (hf : ContinuousOn f unitDisc) (hbdd : ∃ M, ∀ z ∈ unitDisc, ‖f z‖ ≤ M) :
    (clusterSet f unitDisc ζ).Nonempty ∧ IsCompact (clusterSet f unitDisc ζ) ∧
      IsConnected (clusterSet f unitDisc ζ) := by
  obtain ⟨M, hM⟩ := hbdd
  rw [mem_sphere_zero_iff_norm] at hζ
  -- the decreasing sequence `Kₙ = closure f(Δ ∩ B(ζ, 1/(n+1)))` has the cluster set as intersection
  set K : ℕ → Set ℂ := fun n => closure (f '' (unitDisc ∩ ball ζ (1 / ((n : ℝ) + 1)))) with hK
  have hKdef : ∀ n, K n = closure (f '' (unitDisc ∩ ball ζ (1 / ((n : ℝ) + 1)))) := fun n => rfl
  have hKeq : clusterSet f unitDisc ζ = ⋂ n, K n := by
    unfold clusterSet
    apply Subset.antisymm
    · rw [Set.subset_iInter_iff]
      intro n
      rw [hKdef]
      exact Set.iInter₂_subset (1 / ((n : ℝ) + 1)) (by positivity)
    · rw [Set.subset_iInter₂_iff]
      intro r hr
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hr
      refine (Set.iInter_subset _ n).trans ?_
      rw [hKdef]
      exact closure_mono (Set.image_mono (Set.inter_subset_inter Subset.rfl (ball_subset_ball hn.le)))
  -- `Δ ∩ B(ζ, r)` is nonempty for every `r > 0`: it contains `(1 - s) ζ` for small `s > 0`
  have hne : ∀ r > (0 : ℝ), (unitDisc ∩ ball ζ r).Nonempty := by
    intro r hr
    set s : ℝ := min r 1 / 2 with hs
    have hs0 : 0 < s := by
      rw [hs]
      exact half_pos (lt_min hr one_pos)
    have hs1 : s < 1 := by
      have := min_le_right r 1
      linarith
    have hsr : s < r := by
      have := min_le_left r 1
      linarith
    refine ⟨((1 - s : ℝ) : ℂ) * ζ, ?_, ?_⟩
    · show ((1 - s : ℝ) : ℂ) * ζ ∈ ball 0 1
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hζ,
        mul_one]
      linarith
    · rw [mem_ball_iff_norm]
      have h : ((1 - s : ℝ) : ℂ) * ζ - ζ = -((s : ℂ) * ζ) := by
        push_cast
        ring
      rw [h, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le, hζ, mul_one]
      exact hsr
  have hKne : ∀ n, (K n).Nonempty := fun n => by
    rw [hKdef]
    exact ((hne _ (by positivity)).image f).closure
  have hKbdd : ∀ n, K n ⊆ closedBall 0 M := by
    intro n
    rw [hKdef]
    refine closure_minimal ?_ isClosed_closedBall
    rintro _ ⟨z, hz, rfl⟩
    exact mem_closedBall_zero_iff.mpr (hM z hz.1)
  have hKcl : ∀ n, IsClosed (K n) := fun n => by
    rw [hKdef]
    exact isClosed_closure
  have hKc : ∀ n, IsCompact (K n) := fun n =>
    isCompact_of_isClosed_isBounded (hKcl n) (isBounded_closedBall.subset (hKbdd n))
  have hKp : ∀ n, IsPreconnected (K n) := fun n => by
    rw [hKdef]
    exact (((convex_ball (0 : ℂ) 1).inter (convex_ball ζ _)).isPreconnected.image f
      (hf.mono Set.inter_subset_left)).closure
  have hKd : ∀ n, K (n + 1) ⊆ K n := by
    intro n
    rw [hKdef, hKdef]
    refine closure_mono (Set.image_mono (Set.inter_subset_inter Subset.rfl (ball_subset_ball ?_)))
    push_cast
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hint : (⋂ n, K n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hKd hKne (hKc 0) hKcl
  rw [hKeq]
  refine ⟨hint, ?_, hint, isPreconnected_iInter_of_antitone_isCompact hKd hKc hKp⟩
  exact (hKc 0).of_isClosed_subset (isClosed_iInter hKcl) (Set.iInter_subset _ 0)

/-- The radius to `ζ`, truncated below at `r`. -/
def radialSegment (ζ : ℂ) (r : ℝ) : Set ℂ := {z | ∃ t : ℝ, r < t ∧ t < 1 ∧ z = (t : ℂ) * ζ}

/-- **Radial cluster set** `C_ρ(f, ζ)`: limits along the radius to `ζ`. -/
def radialClusterSet (f : ℂ → ℂ) (ζ : ℂ) : Set ℂ :=
  ⋂ r ∈ Ioo (0 : ℝ) 1, closure (f '' radialSegment ζ r)

/-- **Cluster set along a set** `Γ` accumulating at `ζ` (a curve ending at `ζ`, in use). -/
def curveClusterSet (f : ℂ → ℂ) (ζ : ℂ) (Γ : Set ℂ) : Set ℂ :=
  ⋂ r ∈ Ioi (0 : ℝ), closure (f '' (Γ ∩ ball ζ r))

/-- The Stolz angle at `ζ` with aperture parameter `M > 1`. -/
def stolzAngle (ζ : ℂ) (M : ℝ) : Set ℂ := {z ∈ unitDisc | ‖z - ζ‖ < M * (1 - ‖z‖)}

/-- **Angular cluster set** `C_Δ(f, ζ)` for the Stolz angle of parameter `M`. -/
def angularClusterSet (f : ℂ → ℂ) (ζ : ℂ) (M : ℝ) : Set ℂ :=
  ⋂ r ∈ Ioi (0 : ℝ), closure (f '' (stolzAngle ζ M ∩ ball ζ r))

/-- **Boundary cluster set** `C_B(f, ζ)`. -/
def boundaryClusterSet (f : ℂ → ℂ) (ζ : ℂ) : Set ℂ :=
  ⋂ r ∈ Ioi (0 : ℝ),
    closure (⋃ ξ ∈ (sphere (0 : ℂ) 1 ∩ ball ζ r) \ {ζ}, clusterSet f unitDisc ξ)

/-! ### A one-point cluster set forces a limit -/

/-- If `f` is continuous on `Δ` and its cluster set at `ζ` is the single point `w`, then
`f z → w` as `z → ζ` in `Δ`.  (Proof machinery: the intermediate value theorem on the connected
sets `Δ ∩ B(ζ, r)` produces points with `|f z - w| = ε/2`, a limit of which would be a second
cluster point.) -/
theorem tendsto_nhdsWithin_unitDisc_of_clusterSet_eq_singleton {f : ℂ → ℂ} {ζ w : ℂ}
    (hf : ContinuousOn f unitDisc) (h : clusterSet f unitDisc ζ = {w}) :
    Tendsto f (𝓝[unitDisc] ζ) (𝓝 w) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  by_contra hcon
  have hbad : ∀ δ > (0 : ℝ), ∃ x ∈ unitDisc, dist x ζ < δ ∧ ε ≤ dist (f x) w := by
    intro δ hδ
    by_contra hno
    apply hcon
    refine ⟨δ, hδ, fun {x} hx hxδ => ?_⟩
    by_contra hge
    exact hno ⟨x, hx, hxδ, not_lt.1 hge⟩
  have hmem : ∀ n : ℕ, w ∈ closure (f '' (unitDisc ∩ ball ζ (1 / ((n : ℝ) + 1)))) := by
    intro n
    have hw : w ∈ clusterSet f unitDisc ζ := by
      rw [h]
      exact mem_singleton w
    simp only [clusterSet, mem_iInter, gt_iff_lt] at hw
    exact hw _ (by positivity)
  have hpick : ∀ n : ℕ, ∃ c ∈ unitDisc ∩ ball ζ (1 / ((n : ℝ) + 1)), dist (f c) w = ε / 2 := by
    intro n
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨b, hbD, hbζ, hb⟩ := hbad _ hn
    obtain ⟨y, ⟨a, ha, rfl⟩, hay⟩ := Metric.mem_closure_iff.1 (hmem n) (ε / 2) (by positivity)
    have hconn : IsPreconnected (unitDisc ∩ ball ζ (1 / ((n : ℝ) + 1))) :=
      ((convex_ball (0 : ℂ) 1).inter (convex_ball ζ _)).isPreconnected
    have hcont : ContinuousOn (fun z => dist (f z) w) (unitDisc ∩ ball ζ (1 / ((n : ℝ) + 1))) :=
      (continuous_id.dist continuous_const).comp_continuousOn (hf.mono inter_subset_left)
    have hIcc : ε / 2 ∈ Icc (dist (f a) w) (dist (f b) w) := by
      constructor
      · rw [dist_comm]
        exact hay.le
      · linarith
    obtain ⟨c, hc, hc'⟩ := hconn.intermediate_value ha ⟨hbD, mem_ball.2 hbζ⟩ hcont hIcc
    exact ⟨c, hc, hc'⟩
  choose c hc hfc using hpick
  -- the values `f (c n)` lie on a compact sphere: extract a convergent subsequence
  obtain ⟨v, hv, φ, hφ, hlim⟩ := (isCompact_sphere w (ε / 2)).tendsto_subseq
    (x := fun n => f (c n)) (fun n => mem_sphere.2 (hfc n))
  have hcζ : Tendsto c atTop (𝓝 ζ) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (mem_ball.1 (hc n).2).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hvmem : v ∈ clusterSet f unitDisc ζ :=
    mem_clusterSet_unitDisc_iff.2 ⟨c ∘ φ, fun n => (hc (φ n)).1, hcζ.comp hφ.tendsto_atTop, hlim⟩
  rw [h, mem_singleton_iff] at hvmem
  rw [hvmem, mem_sphere, dist_self] at hv
  linarith

/-- A continuous `f` on `Δ` extends continuously to `Δ ∪ {ζ}`, `ζ ∈ ∂Δ`, iff its cluster set at `ζ`
is a single point. -/
theorem clusterSet_subsingleton_iff_continuous_extension {f : ℂ → ℂ} {ζ : ℂ}
    (hζ : ζ ∈ sphere (0 : ℂ) 1) (hf : ContinuousOn f unitDisc) :
    (∃ w, clusterSet f unitDisc ζ = {w}) ↔
      ∃ g : ℂ → ℂ, ContinuousOn g (unitDisc ∪ {ζ}) ∧ EqOn g f unitDisc := by
  have hζD : ζ ∉ unitDisc := by
    rw [mem_sphere_zero_iff_norm] at hζ
    simp only [unitDisc, mem_ball_zero_iff, hζ, lt_self_iff_false, not_false_eq_true]
  have hDo : IsOpen unitDisc := isOpen_ball
  constructor
  · rintro ⟨w, hw⟩
    have hlim := tendsto_nhdsWithin_unitDisc_of_clusterSet_eq_singleton hf hw
    classical
    refine ⟨Function.update f ζ w, ?_,
      fun z hz => Function.update_of_ne (ne_of_mem_of_not_mem hz hζD) _ _⟩
    intro z hz
    rcases hz with hz | hz
    · have hev : Function.update f ζ w =ᶠ[𝓝 z] f := by
        filter_upwards [hDo.mem_nhds hz] with x hx
        exact Function.update_of_ne (ne_of_mem_of_not_mem hx hζD) _ _
      exact ((hf.continuousAt (hDo.mem_nhds hz)).congr hev.symm).continuousWithinAt
    · rw [mem_singleton_iff] at hz
      subst hz
      rw [continuousWithinAt_update_same]
      have hdiff : (unitDisc ∪ {z}) \ {z} = unitDisc := by
        rw [union_diff_right, diff_singleton_eq_self hζD]
      rw [hdiff]
      exact hlim
  · rintro ⟨g, hg, hgf⟩
    refine ⟨g ζ, ?_⟩
    have hζcl : ζ ∈ closure unitDisc := by
      rw [show unitDisc = ball (0 : ℂ) 1 from rfl, closure_ball (0 : ℂ) one_ne_zero]
      exact sphere_subset_closedBall hζ
    haveI : NeBot (𝓝[unitDisc] ζ) := mem_closure_iff_nhdsWithin_neBot.1 hζcl
    have hlim : Tendsto f (𝓝[unitDisc] ζ) (𝓝 (g ζ)) := by
      have h1 : Tendsto g (𝓝[unitDisc] ζ) (𝓝 (g ζ)) :=
        (hg ζ (mem_union_right _ (mem_singleton ζ))).mono_left (nhdsWithin_mono _ subset_union_left)
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact hgf hx
    rw [clusterSet_unitDisc_eq_mapClusterPt]
    ext v
    simp only [mem_setOf_eq, mem_singleton_iff]
    constructor
    · intro hv
      exact eq_of_nhds_neBot (ClusterPt.mono hv hlim)
    · rintro rfl
      exact hlim.mapClusterPt

/-- A holomorphic `f` on `Δ` extends continuously to the closed disc iff every cluster set at a
boundary point is a single point. -/
theorem continuous_extension_iff_forall_clusterSet_subsingleton {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f unitDisc) :
    (∃ g : ℂ → ℂ, ContinuousOn g (closure unitDisc) ∧ EqOn g f unitDisc) ↔
      ∀ ξ ∈ sphere (0 : ℂ) 1, ∃ w, clusterSet f unitDisc ξ = {w} := by
  have hcl : closure unitDisc = closedBall (0 : ℂ) 1 := closure_ball (0 : ℂ) one_ne_zero
  constructor
  · rintro ⟨g, hg, hgf⟩ ξ hξ
    refine (clusterSet_subsingleton_iff_continuous_extension hξ hf.continuousOn).2
      ⟨g, hg.mono ?_, hgf⟩
    rw [hcl]
    exact union_subset ball_subset_closedBall
      (singleton_subset_iff.2 (sphere_subset_closedBall hξ))
  · intro hall
    have hlim : ∀ x ∈ closure unitDisc, ∃ y, Tendsto f (𝓝[unitDisc] x) (𝓝 y) := by
      intro x hx
      rw [hcl, ← ball_union_sphere] at hx
      rcases hx with hx | hx
      · exact ⟨f x, hf.continuousOn x hx⟩
      · obtain ⟨w, hw⟩ := hall x hx
        exact ⟨w, tendsto_nhdsWithin_unitDisc_of_clusterSet_eq_singleton hf.continuousOn hw⟩
    refine ⟨extendFrom unitDisc f, continuousOn_extendFrom subset_rfl hlim, fun z hz => ?_⟩
    exact extendFrom_eq (subset_closure hz) (hf.continuousOn z hz)

/-- **Lindelöf's theorem.**  A bounded holomorphic `f` on `Δ` with limit `a` along a curve ending at
`ζ ∈ ∂Δ` has angular limit `a` at `ζ`.

Not proved (kept as `sorry`): needs the two-constants theorem / harmonic measure estimates. -/
theorem lindelof {f : ℂ → ℂ} {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (hf : DifferentiableOn ℂ f unitDisc) (hbdd : ∃ M, ∀ z ∈ unitDisc, ‖f z‖ ≤ M)
    {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Ico 0 1)) (hγ : MapsTo γ (Ico 0 1) unitDisc)
    (hγζ : Tendsto γ (𝓝[<] 1) (𝓝 ζ)) {a : ℂ} (hlim : Tendsto (f ∘ γ) (𝓝[<] 1) (𝓝 a)) :
    ∀ M : ℝ, 1 < M → angularClusterSet f ζ M = {a} := by
  sorry

/-! ### Lindelöf's maximum principle with one exceptional boundary point -/

/-- Membership in the slit plane is stable under division by a positive real number. -/
theorem div_ofReal_mem_slitPlane {z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ slitPlane) :
    z / (r : ℂ) ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rw [div_ofReal_re, div_ofReal_im]
  rcases hz with h | h
  · exact Or.inl (div_pos h hr)
  · exact Or.inr (div_ne_zero h hr.ne')

/-- **Lindelöf's maximum principle with one exceptional boundary point.**  Let `U ⊆ ℂ` be open,
bounded and preconnected, contained in a half-plane-like region `{z | c * (z - p) ∈ slitPlane}`
with `p ∈ ∂U`.  If `h` is holomorphic and bounded on `U` and `limsup ‖h‖ ≤ M` at every boundary
point of `U` other than `p`, then `‖h‖ ≤ M` on `U`.

Route: for `η > 0` the function `h_η z = h z · (c (z - p) / R)^η` is holomorphic on `U`, tends to
`0` at `p` and has `limsup ‖h_η‖ ≤ M` at the other boundary points; if its supremum `S` over `U`
exceeded `M`, a maximizing sequence would converge either to an interior point (then `h_η` is
constant by the maximum principle, contradicting the vanishing at `p`) or to a boundary point
(contradicting the limsup bounds).  Then let `η → 0`. -/
theorem norm_le_of_frontier_limsup_le_of_bounded {U : Set ℂ} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUc : IsPreconnected U) {p c : ℂ} (hp : p ∈ frontier U)
    (hslit : ∀ z ∈ U, c * (z - p) ∈ slitPlane) {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h U)
    {K : ℝ} (hK : ∀ z ∈ U, ‖h z‖ ≤ K) {M : ℝ} (hM : 0 ≤ M)
    (hbd : ∀ q ∈ frontier U, q ≠ p → ∀ ε > 0, ∀ᶠ z in 𝓝[U] q, ‖h z‖ ≤ M + ε) :
    ∀ z ∈ U, ‖h z‖ ≤ M := by
  obtain ⟨D, hD⟩ := hUb.subset_closedBall p
  set R : ℝ := ‖c‖ * max D 0 + 1 with hR
  have hR0 : 0 < R := by positivity
  have hφlt : ∀ z ∈ U, ‖c * (z - p)‖ < R := by
    intro z hz
    have h1 : ‖z - p‖ ≤ D := by
      have := hD hz
      rwa [mem_closedBall, dist_eq_norm] at this
    calc ‖c * (z - p)‖ = ‖c‖ * ‖z - p‖ := norm_mul _ _
      _ ≤ ‖c‖ * max D 0 := by gcongr; exact h1.trans (le_max_left _ _)
      _ < R := by rw [hR]; linarith
  set φ : ℂ → ℂ := fun z => c * (z - p) / (R : ℂ) with hφ
  have hφslit : ∀ z ∈ U, φ z ∈ slitPlane := fun z hz =>
    div_ofReal_mem_slitPlane hR0 (hslit z hz)
  have hφne : ∀ z ∈ U, φ z ≠ 0 := fun z hz => slitPlane_ne_zero (hφslit z hz)
  have hφle : ∀ z ∈ U, ‖φ z‖ ≤ 1 := by
    intro z hz
    simp only [hφ, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    exact (div_le_one hR0).2 (hφlt z hz).le
  have hφcont : Continuous φ := by
    simp only [hφ]
    fun_prop
  have hφp : φ p = 0 := by simp [hφ]
  have hφdiff : ∀ z, DifferentiableAt ℂ φ z := fun z => by
    simp only [hφ]
    fun_prop
  -- the key estimate for the auxiliary functions `h_η`
  have key : ∀ η : ℝ, 0 < η → ∀ z ∈ U, ‖h z‖ * ‖φ z‖ ^ η ≤ M := by
    intro η hη
    set haux : ℂ → ℂ := fun z => h z * φ z ^ (η : ℂ) with hhaux
    have hnorm : ∀ z ∈ U, ‖haux z‖ = ‖h z‖ * ‖φ z‖ ^ η := by
      intro z hz
      simp only [hhaux, norm_mul]
      rw [Complex.norm_cpow_of_ne_zero (hφne z hz), Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, Real.exp_zero, div_one]
    have hdiff : DifferentiableOn ℂ haux U := by
      refine hh.mul fun z hz => ?_
      exact ((hφdiff z).cpow_const (hφslit z hz)).differentiableWithinAt
    have hbound : ∀ z ∈ U, ‖haux z‖ ≤ max K 0 * ‖φ z‖ ^ η := by
      intro z hz
      rw [hnorm z hz]
      gcongr
      exact (hK z hz).trans (le_max_left _ _)
    have hle1 : ∀ z ∈ U, ‖haux z‖ ≤ ‖h z‖ := by
      intro z hz
      rw [hnorm z hz]
      calc ‖h z‖ * ‖φ z‖ ^ η ≤ ‖h z‖ * 1 := by
            gcongr
            exact Real.rpow_le_one (norm_nonneg _) (hφle z hz) hη.le
        _ = ‖h z‖ := mul_one _
    -- the continuous majorant `max K 0 * ‖φ z‖ ^ η` vanishes at `p`
    have hmaj : Continuous fun z => max K 0 * ‖φ z‖ ^ η := by
      refine continuous_const.mul ?_
      refine continuous_iff_continuousAt.2 fun z => ?_
      exact (Real.continuousAt_rpow_const _ _ (Or.inr hη.le)).comp hφcont.norm.continuousAt
    have hmajp : max K 0 * ‖φ p‖ ^ η = 0 := by
      rw [hφp, norm_zero, Real.zero_rpow hη.ne', mul_zero]
    by_contra hcon
    push Not at hcon
    obtain ⟨z₀, hz₀, hz₀M⟩ := hcon
    set S := sSup ((fun z => ‖haux z‖) '' U) with hS
    have hne : ((fun z => ‖haux z‖) '' U).Nonempty := ⟨_, mem_image_of_mem _ hz₀⟩
    have hbdd : BddAbove ((fun z => ‖haux z‖) '' U) :=
      ⟨max K 0, by
        rintro _ ⟨z, hz, rfl⟩
        exact (hle1 z hz).trans ((hK z hz).trans (le_max_left _ _))⟩
    have hSle : ∀ z ∈ U, ‖haux z‖ ≤ S := fun z hz => le_csSup hbdd (mem_image_of_mem _ hz)
    have hSM : M < S := by
      refine lt_of_lt_of_le ?_ (hSle z₀ hz₀)
      rw [hnorm z₀ hz₀]
      exact hz₀M
    obtain ⟨u, -, hu, humem⟩ := exists_seq_tendsto_sSup hne hbdd
    choose zs hzs hzsu using humem
    obtain ⟨q, hq, ψ, hψ, hlim⟩ :=
      hUb.isCompact_closure.tendsto_subseq (fun n => subset_closure (hzs n))
    have hlimS : Tendsto (fun n => ‖haux (zs (ψ n))‖) atTop (𝓝 S) := by
      have : (fun n => ‖haux (zs (ψ n))‖) = u ∘ ψ := funext fun n => hzsu (ψ n)
      rw [this]
      exact hu.comp hψ.tendsto_atTop
    by_cases hqU : q ∈ U
    · -- an interior maximum: `hη` is constant, but it is small near `p`
      have hcont : ContinuousAt haux q :=
        (hdiff.differentiableAt (hUo.mem_nhds hqU)).continuousAt
      have hval : ‖haux q‖ = S := by
        have h' : Tendsto (fun n => ‖haux (zs (ψ n))‖) atTop (𝓝 ‖haux q‖) :=
          hcont.norm.tendsto.comp hlim
        exact tendsto_nhds_unique h' hlimS
      have hmax : IsMaxOn (norm ∘ haux) U q := fun z hz => by
        show ‖haux z‖ ≤ ‖haux q‖
        rw [hval]
        exact hSle z hz
      have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hUo hdiff hqU hmax
      have hsmall : ∀ᶠ z in 𝓝 p, max K 0 * ‖φ z‖ ^ η < S := by
        have h1 : max K 0 * ‖φ p‖ ^ η < S := by
          rw [hmajp]
          exact hM.trans_lt hSM
        have h2 : ∀ᶠ y in 𝓝 (max K 0 * ‖φ p‖ ^ η), y < S := Iio_mem_nhds h1
        exact Filter.Tendsto.eventually hmaj.continuousAt h2
      obtain ⟨z, hzsm, hzU⟩ := mem_closure_iff_nhds.1 (frontier_subset_closure hp) _ hsmall
      have h1 : ‖haux z‖ = S := by
        rw [hconst hzU, Function.const_apply, hval]
      have h2 : ‖haux z‖ ≤ max K 0 * ‖φ z‖ ^ η := hbound z hzU
      have h3 : max K 0 * ‖φ z‖ ^ η < S := hzsm
      linarith
    · have hqfr : q ∈ frontier U := by
        rw [hUo.frontier_eq]
        exact ⟨hq, hqU⟩
      by_cases hqp : q = p
      · -- the subsequence converges to `p`, where `hη → 0`
        subst hqp
        have h0 : Tendsto (fun n => max K 0 * ‖φ (zs (ψ n))‖ ^ η) atTop (𝓝 0) := by
          have := (hmaj.tendsto q).comp hlim
          rwa [hmajp] at this
        have : S ≤ 0 :=
          le_of_tendsto_of_tendsto' hlimS h0 fun n => hbound _ (hzs _)
        linarith
      · -- the limsup bound at `q`
        have hev := hbd q hqfr hqp ((S - M) / 2) (by linarith)
        have hlim' : Tendsto (fun n => zs (ψ n)) atTop (𝓝[U] q) :=
          tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hzs (ψ n)⟩
        have : S ≤ M + (S - M) / 2 :=
          le_of_tendsto hlimS ((hlim'.eventually hev).mono fun n hn =>
            (hle1 _ (hzs _)).trans hn)
        linarith
  -- let `η → 0`
  intro z hz
  have hφpos : 0 < ‖φ z‖ := norm_pos_iff.2 (hφne z hz)
  have hlim : Tendsto (fun η : ℝ => ‖h z‖ * ‖φ z‖ ^ η) (𝓝[>] 0) (𝓝 ‖h z‖) := by
    have h1 : Tendsto (fun η : ℝ => ‖h z‖ * ‖φ z‖ ^ η) (𝓝 0)
        (𝓝 (‖h z‖ * ‖φ z‖ ^ (0 : ℝ))) :=
      (continuousAt_const.mul (Real.continuousAt_const_rpow hφpos.ne')).tendsto
    rw [Real.rpow_zero, mul_one] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim (eventually_nhdsWithin_of_forall fun η hη => key η hη z hz)

/-! ### Cluster-set estimates and the affine barrier -/

/-- If `w ∉ C(f, ξ)`, then `f` stays at positive distance from `w` near `ξ`. -/
theorem exists_forall_le_norm_sub_of_notMem_clusterSet {f : ℂ → ℂ} {ξ w : ℂ}
    (hw : w ∉ clusterSet f unitDisc ξ) :
    ∃ r > 0, ∃ η > 0, ∀ z ∈ unitDisc ∩ ball ξ r, η ≤ ‖f z - w‖ := by
  simp only [clusterSet, mem_iInter] at hw
  push Not at hw
  obtain ⟨r, hr, hw⟩ := hw
  rw [Metric.mem_closure_iff] at hw
  push Not at hw
  obtain ⟨η, hη, hw⟩ := hw
  refine ⟨r, hr, η, hη, fun z hz => ?_⟩
  have := hw (f z) (mem_image_of_mem f hz)
  rwa [dist_comm, dist_eq_norm] at this

/-- If the ball `B(w, 2ε)` misses `C(f, ξ)`, then `‖f z - w‖ ≥ ε` near `ξ`. -/
theorem exists_forall_le_norm_sub_of_clusterSet_disjoint {f : ℂ → ℂ} {ξ w : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hdisj : ∀ v ∈ clusterSet f unitDisc ξ, 2 * ε ≤ ‖v - w‖) :
    ∃ r > 0, ∀ z ∈ unitDisc ∩ ball ξ r, ε ≤ ‖f z - w‖ := by
  by_contra hcon
  push Not at hcon
  choose! zs hzs hzsw using hcon
  set z : ℕ → ℂ := fun n => zs (1 / ((n : ℝ) + 1)) with hz
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hzD : ∀ n, z n ∈ unitDisc := fun n => (hzs _ (hpos n)).1
  have hzξ : Tendsto z atTop (𝓝 ξ) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
    refine ⟨N, fun n hn => ?_⟩
    have h1 : dist (z n) ξ < 1 / ((n : ℝ) + 1) := mem_ball.1 (hzs _ (hpos n)).2
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
    linarith
  have hfz : ∀ n, f (z n) ∈ closedBall w ε := fun n => by
    rw [mem_closedBall, dist_eq_norm]
    exact (hzsw _ (hpos n)).le
  obtain ⟨v, hv, ψ, hψ, hlim⟩ := (isCompact_closedBall w ε).tendsto_subseq hfz
  have hvC : v ∈ clusterSet f unitDisc ξ :=
    mem_clusterSet_unitDisc_iff.2 ⟨z ∘ ψ, fun n => hzD _, hzξ.comp hψ.tendsto_atTop, hlim⟩
  have := hdisj v hvC
  rw [mem_closedBall, dist_eq_norm] at hv
  linarith

/-- For `‖ζ‖ = 1` and `z` in the unit disc, `Re (conj ζ · (z − ζ)) < −‖z − ζ‖² / 2`: the barrier
`1 − conj ζ · z` has real part `> δ²/2` on the arc `{‖z − ζ‖ = δ} ∩ Δ`. -/
theorem re_conj_mul_sub_lt_of_norm_lt_one {ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hz : ‖z‖ < 1) :
    (conj ζ * (z - ζ)).re < -(‖z - ζ‖ ^ 2) / 2 := by
  have h1 : normSq z = normSq ζ + normSq (z - ζ) + 2 * (ζ * conj (z - ζ)).re := by
    rw [← normSq_add]
    congr 1
    ring
  have h2 : (ζ * conj (z - ζ)).re = (conj ζ * (z - ζ)).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq, normSq_eq_norm_sq, hζ, h2, one_pow] at h1
  have h3 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
  linarith

/-- **Iversen–Gross.**  For `f` holomorphic on `Δ` and `ζ ∈ ∂Δ`, `∂C(f, ζ) ⊆ C_B(f, ζ)`.

Not proved (kept as `sorry`): a cluster-set argument with the maximum principle. -/
theorem iversen_gross {f : ℂ → ℂ} {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1)
    (hf : DifferentiableOn ℂ f unitDisc) :
    frontier (clusterSet f unitDisc ζ) ⊆ boundaryClusterSet f ζ := by
  intro w hw
  have hζ' : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.1 hζ
  by_contra hwB
  -- Step 1: `w ∉ C_B` gives `r₀, ε₀` with `B(w, ε₀) ∩ C(f, ξ) = ∅` for `ξ ∈ ∂Δ ∩ B(ζ, r₀) ∖ {ζ}`
  simp only [boundaryClusterSet, mem_iInter, mem_Ioi] at hwB
  push Not at hwB
  obtain ⟨r₀, hr₀, hwB⟩ := hwB
  rw [Metric.mem_closure_iff] at hwB
  push Not at hwB
  obtain ⟨ε₀, hε₀, hwB⟩ := hwB
  have hfar : ∀ ξ : ℂ, ‖ξ‖ = 1 → ‖ξ - ζ‖ < r₀ → ξ ≠ ζ →
      ∃ r > 0, ∀ z ∈ unitDisc ∩ ball ξ r, ε₀ / 2 ≤ ‖f z - w‖ := by
    intro ξ hξ hξζ hξne
    refine exists_forall_le_norm_sub_of_clusterSet_disjoint (by positivity) fun v hv => ?_
    have hmem : v ∈ ⋃ ξ ∈ (sphere (0 : ℂ) 1 ∩ ball ζ r₀) \ {ζ}, clusterSet f unitDisc ξ := by
      rw [mem_iUnion₂]
      exact ⟨ξ, ⟨⟨mem_sphere_zero_iff_norm.2 hξ, mem_ball.2 (by rwa [dist_eq_norm])⟩, hξne⟩, hv⟩
    have := hwB v hmem
    rw [dist_comm, dist_eq_norm] at this
    linarith
  -- Step 2: `w ∈ C(f, ζ)`, and there is `w' ∉ C(f, ζ)` with `‖w' - w‖ < ε₀ / 4`
  have hclosed : IsClosed (clusterSet f unitDisc ζ) :=
    isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_closure
  have hwC : w ∈ clusterSet f unitDisc ζ := by
    rw [← hclosed.closure_eq]
    exact frontier_subset_closure hw
  obtain ⟨w', hw'C, hw'near⟩ : ∃ w', w' ∉ clusterSet f unitDisc ζ ∧ ‖w' - w‖ < ε₀ / 4 := by
    have h : w ∈ closure (clusterSet f unitDisc ζ)ᶜ := by
      rw [frontier_eq_closure_inter_closure] at hw
      exact hw.2
    rw [Metric.mem_closure_iff] at h
    obtain ⟨w', hw', hd⟩ := h (ε₀ / 4) (by positivity)
    exact ⟨w', hw', by rwa [dist_comm, dist_eq_norm] at hd⟩
  obtain ⟨r₁, hr₁, η, hη, hfar'⟩ := exists_forall_le_norm_sub_of_notMem_clusterSet hw'C
  obtain ⟨zs, hzs, hzsζ, hfzs⟩ := mem_clusterSet_unitDisc_iff.1 hwC
  have hww' : w ≠ w' := fun h => hw'C (h ▸ hwC)
  -- Step 3: the lens `N`, the function `g = 1/(f - w')` and the constants
  set δ : ℝ := min r₀ r₁ / 2 with hδ
  have hδ0 : 0 < δ := by
    rw [hδ]
    exact half_pos (lt_min hr₀ hr₁)
  have hδr₀ : δ < r₀ := by
    rw [hδ]
    linarith [min_le_left r₀ r₁]
  have hδr₁ : δ < r₁ := by
    rw [hδ]
    linarith [min_le_right r₀ r₁]
  set N : Set ℂ := unitDisc ∩ ball ζ δ with hN
  have hNo : IsOpen N := isOpen_ball.inter isOpen_ball
  have hNb : Bornology.IsBounded N := isBounded_ball.subset inter_subset_left
  have hNc : IsPreconnected N := ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  have hNsub : ∀ z ∈ N, z ∈ unitDisc ∩ ball ζ r₁ := fun z hz =>
    ⟨hz.1, mem_ball.2 (lt_trans (mem_ball.1 hz.2) hδr₁)⟩
  have hfw' : ∀ z ∈ N, f z - w' ≠ 0 := fun z hz => by
    intro h
    have := hfar' z (hNsub z hz)
    rw [h, norm_zero] at this
    linarith
  set g : ℂ → ℂ := fun z => (f z - w')⁻¹ with hg
  have hgd : DifferentiableOn ℂ g N := by
    have : DifferentiableOn ℂ (fun z => f z - w') N :=
      (hf.mono inter_subset_left).sub_const w'
    exact this.inv hfw'
  set K : ℝ := 1 / η with hK
  have hK0 : 0 < K := by positivity
  have hgK : ∀ z ∈ N, ‖g z‖ ≤ K := fun z hz => by
    simp only [hg, norm_inv]
    rw [hK, one_div]
    exact inv_anti₀ hη (hfar' z (hNsub z hz))
  set M : ℝ := 1 / (ε₀ / 2 - ‖w' - w‖) with hM
  have hMden : 0 < ε₀ / 2 - ‖w' - w‖ := by linarith
  have hM0 : 0 < M := by positivity
  -- the affine barrier `U z = (2/δ²)(1 - conj ζ * z)`
  set U : ℂ → ℂ := fun z => ((2 / δ ^ 2 : ℝ) : ℂ) * (1 - conj ζ * z) with hU
  have hUre : ∀ z, (U z).re = 2 / δ ^ 2 * (1 - (conj ζ * z).re) := fun z => by
    simp only [hU, re_ofReal_mul, sub_re, one_re]
  have hUnn : ∀ z ∈ unitDisc, 0 ≤ (U z).re := fun z hz => by
    rw [hUre]
    have h1 : (conj ζ * z).re ≤ ‖conj ζ * z‖ := re_le_norm _
    have h2 : ‖conj ζ * z‖ < 1 := by
      rw [norm_mul, Complex.norm_conj, hζ', one_mul]
      exact mem_ball_zero_iff.1 hz
    have h3 : 0 ≤ 2 / δ ^ 2 := by positivity
    nlinarith
  have hUarc : ∀ z, ‖z‖ < 1 → ‖z - ζ‖ = δ → 1 < (U z).re := fun z hz hzδ => by
    rw [hUre]
    have h1 := re_conj_mul_sub_lt_of_norm_lt_one hζ' hz
    rw [hzδ] at h1
    have h2 : (conj ζ * z).re = (conj ζ * (z - ζ)).re + 1 := by
      have : conj ζ * z = conj ζ * (z - ζ) + conj ζ * ζ := by ring
      rw [this, add_re, conj_mul', hζ']
      norm_num
    rw [h2]
    have h4 : 2 / δ ^ 2 * (-(δ ^ 2) / 2) = -1 := by
      field_simp
    have h5 : 2 / δ ^ 2 * (1 - ((conj ζ * (z - ζ)).re + 1)) =
        -(2 / δ ^ 2 * (conj ζ * (z - ζ)).re) := by ring
    rw [h5]
    have h6 : 2 / δ ^ 2 * (conj ζ * (z - ζ)).re < 2 / δ ^ 2 * (-(δ ^ 2) / 2) :=
      mul_lt_mul_of_pos_left h1 (by positivity)
    linarith
  have hUζ : U ζ = 0 := by
    simp only [hU]
    rw [conj_mul', hζ']
    norm_num
  have hUcont : Continuous U := by
    simp only [hU]
    fun_prop
  have hUd : Differentiable ℂ U := by
    simp only [hU]
    fun_prop
  -- the constant `λ` and the function `h = g · exp (-λ U)`
  set K' : ℝ := max K M with hK'
  have hK'pos : 0 < K' := lt_of_lt_of_le hK0 (le_max_left _ _)
  set lam : ℝ := Real.log (K' / M) with hlam
  have hK'M : 1 ≤ K' / M := by
    rw [le_div_iff₀ hM0, one_mul]
    exact le_max_right _ _
  have hlam0 : 0 ≤ lam := Real.log_nonneg hK'M
  have hexp : Real.exp (-lam) = M / K' := by
    rw [Real.exp_neg, hlam, Real.exp_log (by positivity), inv_div]
  set h : ℂ → ℂ := fun z => g z * exp (-(lam : ℂ) * U z) with hh
  have hhnorm : ∀ z, ‖h z‖ = ‖g z‖ * Real.exp (-(lam * (U z).re)) := fun z => by
    simp only [hh, norm_mul, Complex.norm_exp, neg_mul, neg_re, re_ofReal_mul]
  have hhd : DifferentiableOn ℂ h N := by
    have h1 : DifferentiableOn ℂ (fun z => -(lam : ℂ) * U z) N :=
      (hUd.const_mul _).differentiableOn
    exact hgd.mul h1.cexp
  have hhle : ∀ z ∈ N, ‖h z‖ ≤ ‖g z‖ := fun z hz => by
    rw [hhnorm]
    calc ‖g z‖ * Real.exp (-(lam * (U z).re)) ≤ ‖g z‖ * 1 := by
          gcongr
          rw [Real.exp_le_one_iff]
          have := hUnn z hz.1
          nlinarith
      _ = ‖g z‖ := mul_one _
  have hhK : ∀ z ∈ N, ‖h z‖ ≤ K := fun z hz => (hhle z hz).trans (hgK z hz)
  -- Step 4: `ζ ∈ ∂N`, the slit-plane condition, and the boundary bounds
  have hzsN : ∀ᶠ n in atTop, zs n ∈ N := by
    have : ∀ᶠ n in atTop, zs n ∈ ball ζ δ := hzsζ (ball_mem_nhds ζ hδ0)
    exact this.mono fun n hn => ⟨hzs n, hn⟩
  have hζfr : ζ ∈ frontier N := by
    rw [hNo.frontier_eq]
    refine ⟨mem_closure_of_tendsto hzsζ hzsN, fun hζN => ?_⟩
    have := mem_ball_zero_iff.1 hζN.1
    linarith
  have hslit : ∀ z ∈ N, -conj ζ * (z - ζ) ∈ slitPlane := fun z hz => by
    rw [mem_slitPlane_iff]
    left
    have hζζ : conj ζ * ζ = 1 := by
      rw [conj_mul', hζ']
      norm_num
    have : -conj ζ * (z - ζ) = 1 - conj ζ * z := by linear_combination hζζ
    rw [this, sub_re, one_re]
    have h1 : (conj ζ * z).re ≤ ‖conj ζ * z‖ := re_le_norm _
    have h2 : ‖conj ζ * z‖ < 1 := by
      rw [norm_mul, Complex.norm_conj, hζ', one_mul]
      exact mem_ball_zero_iff.1 hz.1
    linarith
  have hbd : ∀ q ∈ frontier N, q ≠ ζ → ∀ ε > 0, ∀ᶠ z in 𝓝[N] q, ‖h z‖ ≤ M + ε := by
    intro q hq hqζ ε hε
    have hqcl : q ∈ closure N := frontier_subset_closure hq
    have hqN : q ∉ N := by
      rw [hNo.frontier_eq] at hq
      exact hq.2
    have hq1 : ‖q‖ ≤ 1 := by
      have h1 : closure N ⊆ closure unitDisc := closure_mono inter_subset_left
      have h2 : closure unitDisc = closedBall (0 : ℂ) 1 := closure_ball 0 one_ne_zero
      rw [h2] at h1
      exact mem_closedBall_zero_iff.1 (h1 hqcl)
    have hqδ : ‖q - ζ‖ ≤ δ := by
      have h1 : closure N ⊆ closure (ball ζ δ) := closure_mono inter_subset_right
      rw [closure_ball _ hδ0.ne'] at h1
      have := h1 hqcl
      rwa [mem_closedBall, dist_eq_norm] at this
    suffices hsuff : ∀ᶠ z in 𝓝[N] q, ‖h z‖ ≤ M from hsuff.mono fun z hz => by linarith
    by_cases hq1' : ‖q‖ = 1
    · -- `q` on the circle: the boundary-cluster-set estimate
      obtain ⟨r, hr, hfr⟩ := hfar q hq1' (lt_of_le_of_lt hqδ hδr₀) hqζ
      have hmem : ball q r ∈ 𝓝[N] q := mem_nhdsWithin_of_mem_nhds (ball_mem_nhds q hr)
      filter_upwards [hmem, self_mem_nhdsWithin] with z hz hzN
      refine (hhle z hzN).trans ?_
      have h1 : ε₀ / 2 ≤ ‖f z - w‖ := hfr z ⟨hzN.1, hz⟩
      have h2 : ‖f z - w‖ ≤ ‖f z - w'‖ + ‖w' - w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h3 : ε₀ / 2 - ‖w' - w‖ ≤ ‖f z - w'‖ := by linarith
      simp only [hg, norm_inv]
      rw [hM, one_div]
      exact inv_anti₀ hMden h3
    · -- `q` on the inner arc: the barrier estimate
      have hq1'' : ‖q‖ < 1 := lt_of_le_of_ne hq1 hq1'
      have hqδ' : ‖q - ζ‖ = δ := by
        by_contra hne
        exact hqN ⟨mem_ball_zero_iff.2 hq1'',
          mem_ball.2 (by rw [dist_eq_norm]; exact lt_of_le_of_ne hqδ hne)⟩
      have hUq : 1 < (U q).re := hUarc q hq1'' hqδ'
      have hev : ∀ᶠ z in 𝓝 q, 1 < (U z).re := by
        have h1 : ∀ᶠ y in 𝓝 ((U q).re), 1 < y := Ioi_mem_nhds hUq
        exact Filter.Tendsto.eventually (Complex.continuous_re.comp hUcont).continuousAt h1
      filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzN
      have hz' : 1 < (U z).re := hz
      rw [hhnorm]
      calc ‖g z‖ * Real.exp (-(lam * (U z).re)) ≤ K * Real.exp (-lam) := by
            gcongr
            · exact hgK z hzN
            · nlinarith
        _ = K * (M / K') := by rw [hexp]
        _ ≤ K' * (M / K') := by
            gcongr
            exact le_max_left _ _
        _ = M := mul_div_cancel₀ _ hK'pos.ne'
  -- Step 5: the maximum principle, and the limit along `zs`
  have hhM : ∀ z ∈ N, ‖h z‖ ≤ M :=
    norm_le_of_frontier_limsup_le_of_bounded hNo hNb hNc hζfr hslit hhd hhK hM0.le hbd
  have hgle : ∀ᶠ n in atTop, ‖g (zs n)‖ ≤ M * Real.exp (lam * (U (zs n)).re) := by
    filter_upwards [hzsN] with n hn
    have h1 := hhM _ hn
    rw [hhnorm] at h1
    have hexppos : 0 < Real.exp (-(lam * (U (zs n)).re)) := Real.exp_pos _
    rw [← le_div_iff₀ hexppos] at h1
    calc ‖g (zs n)‖ ≤ M / Real.exp (-(lam * (U (zs n)).re)) := h1
      _ = M * Real.exp (lam * (U (zs n)).re) := by rw [Real.exp_neg, div_inv_eq_mul]
  have hlimR : Tendsto (fun n => M * Real.exp (lam * (U (zs n)).re)) atTop (𝓝 M) := by
    have h1 : Tendsto (fun n => (U (zs n)).re) atTop (𝓝 (U ζ).re) :=
      ((Complex.continuous_re.comp hUcont).tendsto ζ).comp hzsζ
    rw [hUζ, zero_re] at h1
    have h2 : Tendsto (fun n => lam * (U (zs n)).re) atTop (𝓝 (lam * 0)) := h1.const_mul lam
    rw [mul_zero] at h2
    have h3 : Tendsto (fun n => Real.exp (lam * (U (zs n)).re)) atTop (𝓝 (Real.exp 0)) :=
      (Real.continuous_exp.tendsto 0).comp h2
    rw [Real.exp_zero] at h3
    have h4 := h3.const_mul M
    rwa [mul_one] at h4
  have hlimL : Tendsto (fun n => ‖g (zs n)‖) atTop (𝓝 ‖(w - w')⁻¹‖) := by
    have h1 : Tendsto (fun n => f (zs n) - w') atTop (𝓝 (w - w')) := hfzs.sub_const w'
    exact (h1.inv₀ (sub_ne_zero.2 hww')).norm
  have hfinal : ‖(w - w')⁻¹‖ ≤ M := le_of_tendsto_of_tendsto hlimL hlimR hgle
  rw [norm_inv, hM, ← one_div] at hfinal
  have hpos : 0 < ‖w - w'‖ := norm_pos_iff.2 (sub_ne_zero.2 hww')
  have h2 := (one_div_le_one_div hpos hMden).1 hfinal
  have h3 : ‖w - w'‖ = ‖w' - w‖ := norm_sub_rev _ _
  linarith

/-- **Carathéodory's prime-end theorem, cluster-set form.**  The prime end at `ζ` has impression
equal to the cluster set and principal points equal to the radial cluster set of `f` at `ζ`.

Not proved (kept as `sorry`): the full prime-end theory (see `caratheodory_primeEnd`). -/
theorem caratheodory_primeEnd_principal {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω) {f : ℂ → ℂ}
    (hf : IsConformalOnto f unitDisc Ω) :
    ∃ P : Circle → PrimeEnd Ω, Function.Bijective P ∧ ∀ ζ : Circle,
      (∀ c : {C : ℕ → Set ℂ // IsNullChain Ω C}, Quot.mk _ c = P ζ →
        chainImpression Ω c.1 = clusterSet f unitDisc ζ) ∧
      {w | IsPrincipalPoint Ω (P ζ) w} = radialClusterSet f ζ := by
  sorry

/-- **Carathéodory–Torhorst, cluster-set form.**  For a conformal map `f` of the disc onto a bounded
domain, `∂Ω` is locally connected iff every cluster set at a boundary point is a single point.

Not proved (kept as `sorry`): Carathéodory–Torhorst. -/
theorem locallyConnected_iff_clusterSet_subsingleton {Ω : Set ℂ} (hΩ : Bornology.IsBounded Ω)
    {f : ℂ → ℂ} (hf : IsConformalOnto f unitDisc Ω) :
    LocallyConnectedSpace ↥(frontier Ω) ↔
      ∀ ξ ∈ sphere (0 : ℂ) 1, ∃ w, clusterSet f unitDisc ξ = {w} := by
  have h01 := (caratheodory_continuous_iff hΩ hf).out 1 2
  rw [← h01, ← continuous_extension_iff_forall_clusterSet_subsingleton hf.1]
  have hcl : closure unitDisc = closedBall (0 : ℂ) 1 := closure_ball 0 one_ne_zero
  constructor
  · rintro ⟨F, hFf, hFc, -⟩
    refine ⟨F, ?_, fun z hz => hFf z hz⟩
    rw [hcl]
    exact hFc
  · rintro ⟨g, hgc, hgf⟩
    have hgc' : ContinuousOn g (closedBall 0 1) := by
      rw [← hcl]
      exact hgc
    refine ⟨g, fun z hz => hgf hz, hgc', ?_⟩
    have himg : g '' unitDisc = Ω := by
      rw [hgf.image_eq]
      exact hf.2.2
    apply Subset.antisymm
    · have h1 : g '' closure unitDisc ⊆ closure (g '' unitDisc) := hgc.image_closure
      rw [hcl, himg] at h1
      exact h1
    · refine closure_minimal ?_ ((isCompact_closedBall (0 : ℂ) 1).image_of_continuousOn hgc').isClosed
      rw [← himg]
      exact Set.image_mono ball_subset_closedBall

end ClusterSets

end LiZhongQC
