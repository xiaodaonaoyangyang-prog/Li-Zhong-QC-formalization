import LiZhongQC.Ch03.S15_Distortion

/-!
# §16 拟圆周与拟共形反射 — Quasicircles and quasiconformal reflections

* Definition 16.1 (`K`-quasicircles and `K`-quasidiscs)   — `IsKQuasicircle`, `IsKQuasidisc`
* Theorem 16.1 (the three point condition (16.1))         — `thm16_1_three_point`
* examples: a curve with a cusp is not a quasicircle; ellipses; quasicircles of Hausdorff
  dimension close to `2` (stated and proved in `Lemmas/KochQuasicircle.lean`, user decision 2026-09-27)
* Definition 16.2 (quasiconformal reflection)            — `IsQCReflection`
* Theorem 16.2 (quasicircles ⇔ existence of a q.c. reflection) — `thm16_2`
* Theorem 16.3 (conformal welding)                       — `thm16_3_welding`

## Conventions

A `K`-q.c. map of `ℂ̄` is, after composition with a Möbius transformation, a `K`-q.c.
homeomorphism of `ℂ` onto itself (fixing `∞`).  So a `K`-quasicircle is the image of the unit
circle under such a map followed by a Möbius transformation.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- The real axis `ℝ` as a subset of `ℂ`. -/
def realLine : Set ℂ := {z : ℂ | z.im = 0}

/-- The extended real line `ℝ ∪ {∞} ⊆ ℂ̄`. -/
def extRealLine : Set ExtPlane := toExt realLine ∪ {extInf}

/-- **Definition 16.1** (`K` 拟圆周).  `C ⊆ ℂ̄` is a `K`-quasicircle: the image of the unit circle
under a `K`-q.c. map of `ℂ̄`, i.e. under a `K`-q.c. homeomorphism of `ℂ` followed by a Möbius
transformation. -/
def IsKQuasicircle (C : Set ExtPlane) (K : ℝ) : Prop :=
  ∃ f : ℂ → ℂ, IsKQC f univ K ∧ f '' univ = univ ∧
    ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ C = M '' (OnePoint.map f '' toExt (sphere 0 1))

/-- A quasicircle (for some `K`). -/
def IsQuasicircle (C : Set ExtPlane) : Prop := ∃ K : ℝ, IsKQuasicircle C K

/-- A `K`-quasidisc (`K` 拟圆): a Jordan domain bounded by a `K`-quasicircle. -/
def IsKQuasidisc (D : Set ℂ) (K : ℝ) : Prop :=
  IsJordanDomain D ∧ IsKQuasicircle (frontier (toExt D)) K

/-! ### Batch-4 interface (coordinator 553e2d): the Cayley map and removable points -/

/-- The Cayley-type map `ζ ↦ i(1 + ζ)/(1 - ζ)` sends the unit circle minus `1` onto the real axis. -/
theorem b4_cayley_image : (fun ζ : ℂ => I * (1 + ζ) / (1 - ζ)) '' (sphere 0 1 \ {1}) = realLine := by
  ext w
  constructor
  · rintro ⟨ζ, ⟨hζ1, -⟩, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hζ1
    have hsq : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hζ1, one_pow]
    have hnum : (I * (1 + ζ)).im * (1 - ζ).re - (I * (1 + ζ)).re * (1 - ζ).im = 0 := by
      simp only [mul_im, mul_re, I_re, I_im, add_re, add_im, one_re, one_im, sub_re, sub_im]
      linear_combination -hsq
    show (I * (1 + ζ) / (1 - ζ)).im = 0
    rw [div_im, ← sub_div, hnum, zero_div]
  · intro hw
    have hw' : w.im = 0 := hw
    have hne : w + I ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp [hw'] at this
    refine ⟨(w - I) / (w + I), ⟨?_, ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hne)]
      have h1 : w - I = conj (w + I) := by
        apply Complex.ext <;> simp [hw']
      rw [h1, Complex.norm_conj]
    · intro h
      rw [mem_singleton_iff, div_eq_one_iff_eq hne] at h
      have := congrArg Complex.im h
      simp only [sub_im, add_im, I_im] at this
      linarith
    · have h1 : 1 + (w - I) / (w + I) = 2 * w / (w + I) := by
        field_simp
        ring
      have h2 : 1 - (w - I) / (w + I) = 2 * I / (w + I) := by
        field_simp
        ring
      show I * (1 + (w - I) / (w + I)) / (1 - (w - I) / (w + I)) = w
      rw [h1, h2]
      field_simp [I_ne_zero]

/-- A point is removable: a homeomorphism of the plane onto itself that is `K`-q.c. off one point is `K`-q.c.
(`s13x_removable` with `L = {p}`). -/
theorem b4_isKQC_univ_of_punctured {F : ℂ → ℂ} {K : ℝ} {p : ℂ} (hF : IsHomeomorphOnto F univ univ)
    (hK : IsKQC F {p}ᶜ K) : IsKQC F univ K := by
  have hFu : IsHomeomorphOnto F univ (F '' univ) := by
    rw [hF.2.2.1]
    exact hF
  refine s13x_removable (L := {p}) isOpen_univ hK.2.1 hFu (measure_singleton p)
    (Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall fun y => ?_)
    fun z hz => ⟨{p}ᶜ, isOpen_compl_singleton, hz.2, subset_univ _, hK⟩
  · refine (countable_singleton p.im).mono fun y hy => ?_
    rw [mem_ofPred_eq, mem_singleton_iff] at hy
    rw [mem_singleton_iff, ← hy]
    simp
  · refine (countable_singleton p.re).mono fun x hx => ?_
    rw [mem_ofPred_eq, mem_singleton_iff] at hx
    rw [mem_singleton_iff, ← hx]
    simp

/-- The Cayley-type map `ζ ↦ -i + 2i/(1 - ζ)` (equal to `ζ ↦ i(1 + ζ)/(1 - ζ)` off `1`) is
`1`-q.c. off `1`. -/
theorem b4_qc_cay_isKQC : IsKQC (fun ζ : ℂ => -I + 2 * I * (1 - ζ)⁻¹) {1}ᶜ 1 := by
  refine isKQC_one_of_conformal (D' := (fun ζ : ℂ => -I + 2 * I * (1 - ζ)⁻¹) '' {1}ᶜ)
    isOpen_compl_singleton ⟨fun ζ hζ => ?_, fun a _ b _ hab => ?_, rfl⟩
  · have h1 : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm (mem_compl_singleton_iff.mp hζ))
    exact ((differentiableAt_const _).add ((differentiableAt_const _).mul
      (((differentiableAt_const _).sub differentiableAt_id).inv h1))).differentiableWithinAt
  · have h2I : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
    exact sub_right_injective (inv_injective (mul_left_cancel₀ h2I (add_left_cancel hab)))

/-- The map `w ↦ 1/(w - q)` is `1`-q.c. off `q`. -/
theorem b4_qc_invShift_isKQC (q : ℂ) : IsKQC (fun w : ℂ => (w - q)⁻¹) {q}ᶜ 1 := by
  refine isKQC_one_of_conformal (D' := (fun w : ℂ => (w - q)⁻¹) '' {q}ᶜ)
    isOpen_compl_singleton ⟨fun w hw => ?_, fun a _ b _ hab => ?_, rfl⟩
  · have h1 : w - q ≠ 0 := sub_ne_zero.mpr (mem_compl_singleton_iff.mp hw)
    exact ((differentiableAt_id.sub (differentiableAt_const q)).inv h1).differentiableWithinAt
  · exact sub_left_injective (inv_injective hab)

/-- The conjugate `ζ ↦ 1/(f(-i + 2i/(1 - ζ)) - f(-i))` of a `K`-q.c. map `f` of the plane is
`K`-q.c. off `1`. -/
theorem b4_qc_conj_isKQC {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) :
    IsKQC (fun ζ : ℂ => (f (-I + 2 * I * (1 - ζ)⁻¹) - f (-I))⁻¹) {1}ᶜ K := by
  have h1 := thm7_1_comp b4_qc_cay_isKQC hf (subset_univ _)
  have hsub : (f ∘ fun ζ : ℂ => -I + 2 * I * (1 - ζ)⁻¹) '' {1}ᶜ ⊆ {f (-I)}ᶜ := by
    rintro _ ⟨ζ, hζ, rfl⟩ h
    have heq := hf.2.2.1.2.1 (mem_univ _) (mem_univ _) (mem_singleton_iff.mp h)
    rw [add_eq_left, mul_eq_zero, inv_eq_zero, sub_eq_zero] at heq
    rcases heq with h0 | h0
    · exact mul_ne_zero two_ne_zero I_ne_zero h0
    · exact hζ h0.symm
  have h2 := thm7_1_comp h1 (b4_qc_invShift_isKQC (f (-I))) hsub
  rw [one_mul, mul_one] at h2
  exact h2

/-- The conjugate `ζ ↦ 1/(f(-i + 2i/(1 - ζ)) - f(-i))` of a `K`-q.c. map `f` of the plane onto
itself is a homeomorphism of the plane onto itself: it is `ζ ↦ 1/e(1/(1 - ζ))` for the plane
homeomorphism `e(u) = f(-i + 2iu) - f(-i)` fixing `0`. -/
theorem b4_qc_conj_isHomeomorphOnto {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K)
    (hs : f '' univ = univ) :
    IsHomeomorphOnto (fun ζ : ℂ => (f (-I + 2 * I * (1 - ζ)⁻¹) - f (-I))⁻¹) univ univ := by
  obtain ⟨e, rfl⟩ := t1_homeomorph hf hs
  have h2I : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  set e₁ : ℂ ≃ₜ ℂ := ((Homeomorph.mulLeft₀ (2 * I) h2I).trans (Homeomorph.addLeft (-I))).trans
    (e.trans (Homeomorph.subRight (e (-I)))) with he₁
  have h0 : e₁ 0 = 0 := by simp [he₁]
  obtain ⟨E, hE⟩ := nxI1_exists_homeo e₁ h0
  have hG : ⇑((Homeomorph.subLeft (1 : ℂ)).trans E) =
      fun ζ : ℂ => (e (-I + 2 * I * (1 - ζ)⁻¹) - e (-I))⁻¹ := by
    funext ζ
    simp [hE, nxInvConj, he₁]
  rw [← hG]
  exact nxI1_isHomeomorphOnto_of_homeomorph _

/-- The image identity: with `g(ζ) = 1/(f(-i + 2i/(1 - ζ)) - f(-i))` and `N(w) = f(-i) + 1/w`,
`N(g(S¹)) = f(ℝ) ∪ {∞}`. -/
theorem b4_qc_image {f : ℂ → ℂ} (hf : Function.Injective f) :
    mobiusExt (f (-I)) 1 1 0 ''
        (OnePoint.map (fun ζ : ℂ => (f (-I + 2 * I * (1 - ζ)⁻¹) - f (-I))⁻¹) ''
          toExt (sphere 0 1)) =
      toExt (f '' realLine) ∪ {extInf} := by
  set g : ℂ → ℂ := fun ζ : ℂ => (f (-I + 2 * I * (1 - ζ)⁻¹) - f (-I))⁻¹ with hg
  have hmap : OnePoint.map g '' toExt (sphere 0 1) = toExt (g '' sphere 0 1) := by
    unfold toExt
    rw [← image_comp, ← image_comp]
    exact image_congr fun x _ => by simp
  have h1 : (1 : ℂ) ∈ sphere (0 : ℂ) 1 := by simp
  have hS : sphere (0 : ℂ) 1 = insert 1 (sphere 0 1 \ {1}) := by
    rw [insert_sdiff_singleton, insert_eq_of_mem h1]
  have hg1 : g 1 = 0 := by simp [hg]
  have hM0 : mobiusExt (f (-I)) 1 1 0 ((0 : ℂ) : ExtPlane) = extInf :=
    mobiusExt_coe_of_eq_zero (by simp)
  have hpt : ∀ ζ ∈ sphere (0 : ℂ) 1 \ {1}, mobiusExt (f (-I)) 1 1 0 ((g ζ : ℂ) : ExtPlane) =
      ((f (I * (1 + ζ) / (1 - ζ)) : ℂ) : ExtPlane) := by
    rintro ζ ⟨-, hζ⟩
    have hζ1 : (1 : ℂ) - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ)
    have hC : -I + 2 * I * (1 - ζ)⁻¹ = I * (1 + ζ) / (1 - ζ) := by
      field_simp
      ring
    have hw : f (I * (1 + ζ) / (1 - ζ)) - f (-I) ≠ 0 := by
      intro h
      have h' := hf (sub_eq_zero.mp h)
      rw [div_eq_iff hζ1] at h'
      have h2 : (2 : ℂ) * I = 0 := by linear_combination h'
      exact mul_ne_zero two_ne_zero I_ne_zero h2
    have hgζ : g ζ = (f (I * (1 + ζ) / (1 - ζ)) - f (-I))⁻¹ := by simp only [hg, hC]
    rw [hgζ, mobiusExt_coe (by simpa using hw)]
    congr 1
    simp only [mobiusFn]
    field_simp
    ring
  rw [hmap, hS]
  unfold toExt
  rw [image_insert_eq, image_insert_eq, image_insert_eq, hg1, hM0, union_singleton]
  congr 1
  rw [← b4_cayley_image, image_image, image_image, image_image, image_image]
  exact image_congr hpt

/-- The image of the extended real line under a `K`-q.c. map of the plane is a
`K`-quasicircle through `∞`. -/
theorem isKQuasicircle_image_realLine {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K)
    (hs : f '' univ = univ) : IsKQuasicircle (toExt (f '' realLine) ∪ {extInf}) K := by
  have hhom := b4_qc_conj_isHomeomorphOnto hf hs
  refine ⟨fun ζ : ℂ => (f (-I + 2 * I * (1 - ζ)⁻¹) - f (-I))⁻¹,
    b4_isKQC_univ_of_punctured hhom (b4_qc_conj_isKQC hf), hhom.2.2.1,
    mobiusExt (f (-I)) 1 1 0, ⟨f (-I), 1, 1, 0, by simp, rfl⟩, ?_⟩
  exact (b4_qc_image fun a b hab => hf.2.2.1.2.1 (mem_univ a) (mem_univ b) hab).symm

/-- Teichmüller's circle distortion between two points of one circle: if `‖y - x₀‖ = ‖w - x₀‖ = r > 0`
for a `K`-q.c. map `f` of the plane onto itself, then `‖f y - f x₀‖ ≤ λ(K) ‖f w - f x₀‖`
(`thm15_4_circle_distortion`). -/
theorem tp_a_circle {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ)
    {x₀ y w : ℂ} {r : ℝ} (hr : 0 < r) (hy : ‖y - x₀‖ = r) (hw : ‖w - x₀‖ = r) :
    ‖f y - f x₀‖ ≤ lambdaInv K * ‖f w - f x₀‖ := by
  have hfc : Continuous f := continuousOn_univ.1 hf.2.2.1.1
  set g : ℝ → ℝ := fun θ => ‖f (x₀ + r * exp (θ * I)) - f x₀‖ with hg
  have hgc : Continuous g := by
    simp only [hg]
    fun_prop
  have hper : Function.Periodic g (2 * π) := by
    intro θ
    simp only [hg]
    have h := exp_mul_I_periodic (θ : ℂ)
    simp only at h
    push_cast
    rw [h]
  have hcpt : IsCompact (range g) := hper.compact_of_continuous (by positivity) hgc
  have hlam : 0 ≤ lambdaInv K := zero_le_one.trans (td_one_le_lambdaInv hf.2.1)
  have hpt : ∀ v : ℂ, ‖v - x₀‖ = r → g (arg (v - x₀)) = ‖f v - f x₀‖ := by
    intro v hv
    have hv' : x₀ + (r : ℂ) * exp ((arg (v - x₀) : ℂ) * I) = v := by
      rw [← hv, Complex.norm_mul_exp_arg_mul_I]
      ring
    simp only [hg, hv']
  calc ‖f y - f x₀‖ = g (arg (y - x₀)) := (hpt y hy).symm
    _ ≤ sSup (range g) := le_csSup hcpt.bddAbove ⟨_, rfl⟩
    _ ≤ lambdaInv K * sInf (range g) := thm15_4_circle_distortion hf hs x₀ hr
    _ ≤ lambdaInv K * g (arg (w - x₀)) :=
        mul_le_mul_of_nonneg_left (csInf_le hcpt.bddBelow ⟨_, rfl⟩) hlam
    _ = lambdaInv K * ‖f w - f x₀‖ := by rw [hpt w hw]

/-- First exit from an open set along a segment: if `U` is open, `a ∈ U` and `b ∉ U`, the segment
`t ↦ a + t (b - a)` leaves `U` for the first time at some `s ∈ (0, 1]`, at a point of
`closure U \ U`. -/
theorem tp_a_exit {U : Set ℂ} (hU : IsOpen U) {a b : ℂ} (ha : a ∈ U) (hb : b ∉ U) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ a + s * (b - a) ∈ closure U \ U ∧
      ∀ t : ℝ, 0 ≤ t → t < s → a + t * (b - a) ∈ U := by
  have hγc : Continuous fun t : ℝ => a + (t : ℂ) * (b - a) := by fun_prop
  set S : Set ℝ := Icc 0 1 ∩ (fun t : ℝ => a + (t : ℂ) * (b - a)) ⁻¹' Uᶜ
  have hSc : IsClosed S := isClosed_Icc.inter (hU.isClosed_compl.preimage hγc)
  have h1S : (1 : ℝ) ∈ S := ⟨⟨zero_le_one, le_rfl⟩, by simpa using hb⟩
  have hSb : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  have hsS : sInf S ∈ S := hSc.csInf_mem ⟨1, h1S⟩ hSb
  have hs1 : sInf S ≤ 1 := csInf_le hSb h1S
  have hsU : a + ((sInf S : ℝ) : ℂ) * (b - a) ∉ U := hsS.2
  have hbefore : ∀ t : ℝ, 0 ≤ t → t < sInf S → a + t * (b - a) ∈ U := by
    intro t ht0 hts
    by_contra hcon
    have htS : t ∈ S := ⟨⟨ht0, (hts.trans_le hs1).le⟩, hcon⟩
    exact absurd (csInf_le hSb htS) (not_le.2 hts)
  have hs0 : 0 < sInf S := by
    refine lt_of_le_of_ne hsS.1.1 fun h => hsU ?_
    rw [← h]
    simpa using ha
  refine ⟨sInf S, hs0, hs1, ⟨?_, hsU⟩, hbefore⟩
  have hlim : Tendsto (fun t : ℝ => a + (t : ℂ) * (b - a)) (𝓝[<] (sInf S))
      (𝓝 (a + ((sInf S : ℝ) : ℂ) * (b - a))) :=
    (hγc.tendsto _).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hs0] with t ht
  exact hbefore t ht.1.le ht.2

/-- One side of the three-point estimate: if `‖y - c‖ = r > 0` and `b ∉ f(B(c, r))`, the segment
from `f(c)` to `b` stays in `f(B(c, r))` up to a parameter `s ∈ (0, 1]` with
`‖f y - f c‖ ≤ λ(K) s ‖b - f c‖` (first exit point on `f(∂B(c, r))` + `tp_a_circle`). -/
theorem tp_a_side {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ)
    {c y b : ℂ} {r : ℝ} (hr : 0 < r) (hy : ‖y - c‖ = r) (hb : b ∉ f '' ball c r) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ‖f y - f c‖ ≤ lambdaInv K * (s * ‖b - f c‖) ∧
      ∀ t : ℝ, 0 ≤ t → t < s → f c + t * (b - f c) ∈ f '' ball c r := by
  have hfc : Continuous f := continuousOn_univ.1 hf.2.2.1.1
  have hU : IsOpen (f '' ball c r) :=
    isOpen_image_of_isKQC (ac_t_isKQC_restrict hf isOpen_ball (subset_univ _))
  obtain ⟨s, hs0, hs1, ⟨hcl, hnot⟩, hbefore⟩ :=
    tp_a_exit hU (mem_image_of_mem f (mem_ball_self hr)) hb
  refine ⟨s, hs0, hs1, ?_, hbefore⟩
  have hclosed : IsClosed (f '' closedBall c r) := ((isCompact_closedBall c r).image hfc).isClosed
  obtain ⟨w, hw, hwp⟩ := closure_minimal (image_mono ball_subset_closedBall) hclosed hcl
  have hwr : ‖w - c‖ = r := by
    rw [← dist_eq_norm]
    exact le_antisymm (mem_closedBall.1 hw)
      (not_lt.1 fun h => hnot ⟨w, mem_ball.2 h, hwp⟩)
  have hnorm : ‖f w - f c‖ = s * ‖b - f c‖ := by
    rw [hwp, add_sub_cancel_left, norm_mul, Complex.norm_of_nonneg hs0.le]
  rw [← hnorm]
  exact tp_a_circle hf hs hr hy hwr

/-- **Theorem 16.1**: if `C = f(ℝ) ∪ {∞}` for a `K`-q.c. map `f` of the plane, then for any three
points `z₁ = f(x₁), z₂ = f(x₂), z₃ = f(x₃)`, `x₁ < x₂ < x₃`, of `C`,
`|z₁ - z₂| + |z₂ - z₃| ≤ λ(K) |z₁ - z₃|` (16.1). -/
theorem thm16_1_three_point {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ)
    {x₁ x₂ x₃ : ℝ} (h₁₂ : x₁ < x₂) (h₂₃ : x₂ < x₃) :
    ‖f x₁ - f x₂‖ + ‖f x₂ - f x₃‖ ≤ lambdaInv K * ‖f x₁ - f x₃‖ := by
  have hinj : Function.Injective f := fun a b hab => hf.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
  have hlam : 0 ≤ lambdaInv K := zero_le_one.trans (td_one_le_lambdaInv hf.2.1)
  have hd12 : ‖(x₂ : ℂ) - x₁‖ = x₂ - x₁ := by
    rw [← ofReal_sub, Complex.norm_of_nonneg (by linarith)]
  have hd23 : ‖(x₂ : ℂ) - x₃‖ = x₃ - x₂ := by
    rw [← ofReal_sub, Complex.norm_real, Real.norm_of_nonpos (by linarith), neg_sub]
  have hd13 : ‖(x₃ : ℂ) - x₁‖ = (x₂ - x₁) + (x₃ - x₂) := by
    rw [← ofReal_sub, Complex.norm_of_nonneg (by linarith)]
    ring
  -- the discs `B(x₁, x₂ - x₁)` and `B(x₃, x₃ - x₂)` are disjoint
  have hdisj : ∀ z, z ∈ ball (x₁ : ℂ) (x₂ - x₁) → z ∈ ball (x₃ : ℂ) (x₃ - x₂) → False := by
    intro z h1 h2
    rw [mem_ball, dist_eq_norm] at h1 h2
    have h3 := norm_sub_le_norm_sub_add_norm_sub (x₃ : ℂ) z x₁
    rw [norm_sub_rev (x₃ : ℂ) z, hd13] at h3
    linarith
  have hb1 : f x₃ ∉ f '' ball (x₁ : ℂ) (x₂ - x₁) := by
    rintro ⟨y, hy, hyx⟩
    rw [hinj hyx] at hy
    exact hdisj _ hy (mem_ball_self (by linarith))
  have hb2 : f x₁ ∉ f '' ball (x₃ : ℂ) (x₃ - x₂) := by
    rintro ⟨y, hy, hyx⟩
    rw [hinj hyx] at hy
    exact hdisj _ (mem_ball_self (by linarith)) hy
  obtain ⟨s₁, hs₁0, hs₁1, hle₁, hU₁⟩ := tp_a_side hf hs (by linarith) hd12 hb1
  obtain ⟨s₂, hs₂0, hs₂1, hle₂, hU₂⟩ := tp_a_side hf hs (by linarith) hd23 hb2
  -- the two first exits do not overlap: `s₁ + s₂ ≤ 1`
  have hsum : s₁ + s₂ ≤ 1 := by
    by_contra hcon
    obtain ⟨y₁, hy₁, hfy₁⟩ := hU₁ ((s₁ + 1 - s₂) / 2) (by linarith) (by linarith)
    obtain ⟨y₂, hy₂, hfy₂⟩ := hU₂ (1 - (s₁ + 1 - s₂) / 2) (by linarith) (by linarith)
    have heq : f y₁ = f y₂ := by
      rw [hfy₁, hfy₂]
      push_cast
      ring
    rw [hinj heq] at hy₁
    exact hdisj _ hy₁ hy₂
  rw [norm_sub_rev (f x₃) (f x₁)] at hle₁
  rw [norm_sub_rev (f x₁) (f x₂)]
  calc ‖f x₂ - f x₁‖ + ‖f x₂ - f x₃‖
      ≤ lambdaInv K * (s₁ * ‖f x₁ - f x₃‖) + lambdaInv K * (s₂ * ‖f x₁ - f x₃‖) :=
        add_le_add hle₁ hle₂
    _ = lambdaInv K * ((s₁ + s₂) * ‖f x₁ - f x₃‖) := by ring
    _ ≤ lambdaInv K * (1 * ‖f x₁ - f x₃‖) := by gcongr
    _ = lambdaInv K * ‖f x₁ - f x₃‖ := by rw [one_mul]

/-! ### Three-point track interface (coordinator 553e2d) -/

/-- `T z = ζ₀ - 2iζ₀/(z + i)` is `1`-q.c. off `-i`. -/
theorem tp_b1_T_isKQC {ζ₀ : ℂ} (hζ₀ : ζ₀ ≠ 0) :
    IsKQC (fun z : ℂ => ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹) {-I}ᶜ 1 := by
  refine isKQC_one_of_conformal (D' := (fun z : ℂ => ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹) '' {-I}ᶜ)
    isOpen_compl_singleton ⟨fun z hz => ?_, fun a _ b _ hab => ?_, rfl⟩
  · have h1 : z + I ≠ 0 := by
      intro h
      exact hz (mem_singleton_iff.mpr (eq_neg_of_add_eq_zero_left h))
    have hd : DifferentiableAt ℂ (fun z : ℂ => z + I) z :=
      differentiableAt_id.add (differentiableAt_const I)
    exact ((differentiableAt_const _).sub ((differentiableAt_const _).mul
      (hd.inv h1))).differentiableWithinAt
  · have h2I : (2 : ℂ) * I * ζ₀ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hζ₀
    exact add_left_injective I (inv_injective (mul_left_cancel₀ h2I (sub_right_injective hab)))

/-- The Möbius map `w ↦ α + β/(w - q)` (`β ≠ 0`) is `1`-q.c. off `q`. -/
theorem tp_b1_M_isKQC (q α : ℂ) {β : ℂ} (hβ : β ≠ 0) :
    IsKQC (fun w : ℂ => α + β * (w - q)⁻¹) {q}ᶜ 1 := by
  refine isKQC_one_of_conformal (D' := (fun w : ℂ => α + β * (w - q)⁻¹) '' {q}ᶜ)
    isOpen_compl_singleton ⟨fun w hw => ?_, fun a _ b _ hab => ?_, rfl⟩
  · have h1 : w - q ≠ 0 := sub_ne_zero.mpr (mem_compl_singleton_iff.mp hw)
    exact ((differentiableAt_const _).add ((differentiableAt_const _).mul
      ((differentiableAt_id.sub (differentiableAt_const q)).inv h1))).differentiableWithinAt
  · exact sub_left_injective (inv_injective (mul_left_cancel₀ hβ (add_left_cancel hab)))

/-- The conjugate `z ↦ α + β/(f(ζ₀ - 2iζ₀/(z + i)) - f(ζ₀))` of a `K`-q.c. map `f` of the plane is
`K`-q.c. off `-i`. -/
theorem tp_b1_conj_isKQC {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) {ζ₀ : ℂ} (α : ℂ) {β : ℂ}
    (hζ₀ : ζ₀ ≠ 0) (hβ : β ≠ 0) :
    IsKQC (fun z : ℂ => α + β * (f (ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹) - f ζ₀)⁻¹) {-I}ᶜ K := by
  have h1 := thm7_1_comp (tp_b1_T_isKQC hζ₀) hf (subset_univ _)
  have hsub : (f ∘ fun z : ℂ => ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹) '' {-I}ᶜ ⊆ {f ζ₀}ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ h
    have heq := hf.2.2.1.2.1 (mem_univ _) (mem_univ _) (mem_singleton_iff.mp h)
    rw [sub_eq_self, mul_eq_zero, inv_eq_zero] at heq
    rcases heq with h0 | h0
    · exact mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hζ₀ h0
    · exact hz (mem_singleton_iff.mpr (eq_neg_of_add_eq_zero_left h0))
  have h2 := thm7_1_comp h1 (tp_b1_M_isKQC (f ζ₀) α hβ) hsub
  rw [one_mul, mul_one] at h2
  exact h2

/-- The conjugate `z ↦ α + β/(f(ζ₀ - 2iζ₀/(z + i)) - f(ζ₀))` (`ζ₀, β ≠ 0`) of a `K`-q.c. map `f` of
the plane onto itself is a homeomorphism of the plane onto itself: it is
`z ↦ α + β/e(1/(z + i))` for the plane homeomorphism `e(u) = f(ζ₀ - 2iζ₀u) - f(ζ₀)` fixing `0`. -/
theorem tp_b1_conj_isHomeomorphOnto {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K)
    (hs : f '' univ = univ) {ζ₀ : ℂ} (α : ℂ) {β : ℂ} (hζ₀ : ζ₀ ≠ 0) (hβ : β ≠ 0) :
    IsHomeomorphOnto (fun z : ℂ => α + β * (f (ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹) - f ζ₀)⁻¹)
      univ univ := by
  obtain ⟨e, rfl⟩ := t1_homeomorph hf hs
  have h2I : (2 : ℂ) * I * ζ₀ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) hζ₀
  set e₁ : ℂ ≃ₜ ℂ := ((Homeomorph.mulLeft₀ (2 * I * ζ₀) h2I).trans (Homeomorph.subLeft ζ₀)).trans
    (e.trans (Homeomorph.subRight (e ζ₀))) with he₁
  have h0 : e₁ 0 = 0 := by simp [he₁]
  obtain ⟨E, hE⟩ := nxI1_exists_homeo e₁ h0
  have hG : ⇑(((Homeomorph.addRight I).trans E).trans
      ((Homeomorph.mulLeft₀ β hβ).trans (Homeomorph.addLeft α))) =
      fun z : ℂ => α + β * (e (ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹) - e ζ₀)⁻¹ := by
    funext z
    simp [hE, nxInvConj, he₁]
  rw [← hG]
  exact nxI1_isHomeomorphOnto_of_homeomorph _

/-- `T(z) = ζ₀ - 2iζ₀/(z + i)` undoes the Cayley map up to the rotation by `ζ₀`:
`T(i(1 + u)/(1 - u)) = ζ₀ u` for `u ≠ 1`. -/
theorem tp_b1_T_cayley (ζ₀ : ℂ) {u : ℂ} (hu : u ≠ 1) :
    ζ₀ - 2 * I * ζ₀ * (I * (1 + u) / (1 - u) + I)⁻¹ = ζ₀ * u := by
  have hu1 : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have hx : I * (1 + u) / (1 - u) + I = 2 * I / (1 - u) := by
    field_simp
    ring
  rw [hx, inv_div]
  field_simp
  ring

/-- `T(z) = ζ₀ - 2iζ₀/(z + i)` (`|ζ₀| = 1`) maps the real axis onto the unit circle minus `ζ₀`. -/
theorem tp_b1_T_image {ζ₀ : ℂ} (hζ₀ : ‖ζ₀‖ = 1) :
    (fun z : ℂ => ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹) '' realLine = sphere 0 1 \ {ζ₀} := by
  have hζ₀0 : ζ₀ ≠ 0 := ne_zero_of_norm_ne_zero (by rw [hζ₀]; exact one_ne_zero)
  rw [← b4_cayley_image, image_image]
  ext ζ
  constructor
  · rintro ⟨u, ⟨hu1, hu⟩, rfl⟩
    show ζ₀ - 2 * I * ζ₀ * (I * (1 + u) / (1 - u) + I)⁻¹ ∈ _
    rw [tp_b1_T_cayley ζ₀ hu]
    refine ⟨?_, fun h => hu ((mul_eq_left₀ hζ₀0).mp (mem_singleton_iff.mp h))⟩
    rw [mem_sphere_zero_iff_norm, norm_mul, hζ₀, one_mul]
    exact mem_sphere_zero_iff_norm.mp hu1
  · rintro ⟨hζ1, hζ⟩
    have hu : ζ / ζ₀ ≠ 1 := fun h => hζ (mem_singleton_iff.mpr ((div_eq_one_iff_eq hζ₀0).mp h))
    refine ⟨ζ / ζ₀, ⟨?_, hu⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_div, hζ₀, div_one]
      exact mem_sphere_zero_iff_norm.mp hζ1
    · show ζ₀ - 2 * I * ζ₀ * (I * (1 + ζ / ζ₀) / (1 - ζ / ζ₀) + I)⁻¹ = ζ
      rw [tp_b1_T_cayley ζ₀ hu, mul_div_cancel₀ ζ hζ₀0]

/-- Off its pole `q` (`c q + d = 0`, `c ≠ 0`), `mobiusExt a b c d` is
`w ↦ a/c + ((bc - ad)/c²)/(w - q)`. -/
theorem tp_b1_mobius_eq {a b c d q w : ℂ} (hc : c ≠ 0) (hq : c * q + d = 0) (hw : w ≠ q) :
    mobiusExt a b c d (w : ExtPlane) =
      ((a / c + (b * c - a * d) / c ^ 2 * (w - q)⁻¹ : ℂ) : ExtPlane) := by
  have hwq : w - q ≠ 0 := sub_ne_zero.mpr hw
  have hden : c * w + d = c * (w - q) := by linear_combination hq
  rw [mobiusExt_coe (by rw [hden]; exact mul_ne_zero hc hwq)]
  congr 1
  rw [mobiusFn, hden]
  have hd : d = -(c * q) := by linear_combination hq
  rw [hd]
  field_simp
  ring

/-- The image identity: with `g(z) = a/c + ((bc - ad)/c²)/(f(ζ₀ - 2iζ₀/(z + i)) - f(ζ₀))`, where
`|ζ₀| = 1` and `f(ζ₀)` is the pole of `M = mobiusExt a b c d`, `M(f(S¹)) = g(ℝ) ∪ {∞}`. -/
theorem tp_b1_image {f : ℂ → ℂ} (hf : Function.Injective f) {a b c d ζ₀ : ℂ} (hζ₀ : ‖ζ₀‖ = 1)
    (hc : c ≠ 0) (hq : c * f ζ₀ + d = 0) :
    mobiusExt a b c d '' (OnePoint.map f '' toExt (sphere 0 1)) =
      toExt ((fun z : ℂ => a / c + (b * c - a * d) / c ^ 2 *
        (f (ζ₀ - 2 * I * ζ₀ * (z + I)⁻¹) - f ζ₀)⁻¹) '' realLine) ∪ {extInf} := by
  have hmem : ζ₀ ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr hζ₀
  have hS : sphere (0 : ℂ) 1 = insert ζ₀ (sphere 0 1 \ {ζ₀}) := by
    rw [insert_sdiff_singleton, insert_eq_of_mem hmem]
  have hM0 : mobiusExt a b c d ((f ζ₀ : ℂ) : ExtPlane) = extInf := mobiusExt_coe_of_eq_zero hq
  unfold toExt
  rw [hS, image_insert_eq, image_insert_eq, image_insert_eq, OnePoint.map_some, hM0,
    union_singleton, ← tp_b1_T_image hζ₀]
  congr 1
  rw [image_image, image_image, image_image, image_image]
  refine image_congr fun x hx => ?_
  have hT : ζ₀ - 2 * I * ζ₀ * (x + I)⁻¹ ∈ sphere (0 : ℂ) 1 \ {ζ₀} := by
    rw [← tp_b1_T_image hζ₀]
    exact mem_image_of_mem _ hx
  rw [OnePoint.map_some]
  exact tp_b1_mobius_eq hc hq fun h => hT.2 (mem_singleton_iff.mpr (hf h))

/-- **B1.** A `K`-quasicircle through `∞` is `g(ℝ) ∪ {∞}` for a `K`-q.c. map `g` of the plane onto itself (the
converse of `isKQuasicircle_image_realLine`): `g = M ∘ f ∘ T`, where `T(z) = ζ₀ (z - i)/(z + i)` maps `ℝ ∪ {∞}` onto
the unit circle with `T(∞) = ζ₀`, `M(f(ζ₀)) = ∞`; `g` is `K`-q.c. off `-i` and the point is removable
(`b4_isKQC_univ_of_punctured`). -/
theorem tp_quasicircle_through_inf {C : Set ExtPlane} {K : ℝ} (hC : IsKQuasicircle C K) (hinf : extInf ∈ C) :
    ∃ g : ℂ → ℂ, IsKQC g univ K ∧ g '' univ = univ ∧ C = toExt (g '' realLine) ∪ {extInf} := by
  obtain ⟨f, hf, hs, M, ⟨a, b, c, d, hdet, rfl⟩, rfl⟩ := hC
  obtain ⟨_, ⟨_, ⟨ζ₀, hζ₀, rfl⟩, rfl⟩, hM⟩ := hinf
  have hq : c * f ζ₀ + d = 0 := by
    by_contra h
    rw [OnePoint.map_some, mobiusExt_coe h] at hM
    exact OnePoint.coe_ne_infty _ hM
  have hc : c ≠ 0 := by
    rintro rfl
    exact hdet (by linear_combination a * hq)
  have hζ₀1 : ‖ζ₀‖ = 1 := mem_sphere_zero_iff_norm.mp hζ₀
  have hζ₀0 : ζ₀ ≠ 0 := ne_zero_of_norm_ne_zero (by rw [hζ₀1]; exact one_ne_zero)
  have hβ : (b * c - a * d) / c ^ 2 ≠ 0 :=
    div_ne_zero (fun h => hdet (by linear_combination -h)) (pow_ne_zero 2 hc)
  have hhom := tp_b1_conj_isHomeomorphOnto hf hs (a / c) hζ₀0 hβ
  exact ⟨_, b4_isKQC_univ_of_punctured hhom (tp_b1_conj_isKQC hf (a / c) hζ₀0 hβ), hhom.2.2.1,
    tp_b1_image (fun x y hxy => hf.2.2.1.2.1 (mem_univ x) (mem_univ y) hxy) hζ₀1 hc hq⟩

/-- Removing `∞`: `toExt A ∪ {∞} = toExt B ∪ {∞}` forces `A = B`. -/
theorem tp_b2_eq_of_toExt_union {A B : Set ℂ} (h : toExt A ∪ {extInf} = toExt B ∪ {extInf}) :
    A = B := by
  have key : ∀ (s : Set ℂ) (z : ℂ), (z : ExtPlane) ∈ toExt s ∪ {extInf} ↔ z ∈ s := by
    intro s z
    constructor
    · rintro (⟨w, hw, hwz⟩ | hz)
      · exact OnePoint.coe_injective hwz ▸ hw
      · exact (OnePoint.coe_ne_infty z (mem_singleton_iff.mp hz)).elim
    · intro hz
      exact Or.inl ⟨z, hz, rfl⟩
  ext z
  rw [← key A z, ← key B z, h]

/-- The cusp minus its tip lies in the union of the disjoint open sets `y < x²/2` (containing
the open ray) and `y > x²/2` (containing the open arc of `y = x²`). -/
theorem tp_b2_mem_cover {z : ℂ}
    (hz : z ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} ∪ {z : ℂ | 0 ≤ z.re ∧ z.im = z.re ^ 2}) (h0 : z ≠ 0) :
    z ∈ {z : ℂ | z.im < z.re ^ 2 / 2} ∪ {z : ℂ | z.re ^ 2 / 2 < z.im} := by
  have hre : z.re ≠ 0 := by
    intro hre
    rcases hz with ⟨him, -⟩ | ⟨-, him⟩
    · exact h0 (Complex.ext hre him)
    · exact h0 (Complex.ext hre (by rw [him, hre, Complex.zero_im]; ring))
  have hsq : 0 < z.re ^ 2 := by positivity
  rcases hz with ⟨him, -⟩ | ⟨-, him⟩
  · left
    show z.im < z.re ^ 2 / 2
    rw [him]
    positivity
  · right
    show z.re ^ 2 / 2 < z.im
    rw [him]
    linarith

/-- A preconnected set covered by `{y < x²/2} ∪ {y > x²/2}` cannot meet both sets. -/
theorem tp_b2_not_both {T : Set ℂ} (hT : IsPreconnected T)
    (hcov : T ⊆ {z : ℂ | z.im < z.re ^ 2 / 2} ∪ {z : ℂ | z.re ^ 2 / 2 < z.im}) {a b : ℂ}
    (ha : a ∈ T) (hb : b ∈ T) (haU : a.im < a.re ^ 2 / 2) (hbV : b.re ^ 2 / 2 < b.im) : False := by
  obtain ⟨z, -, hzU, hzV⟩ := hT _ _ (isOpen_lt continuous_im ((continuous_re.pow 2).div_const 2))
    (isOpen_lt ((continuous_re.pow 2).div_const 2) continuous_im) hcov ⟨a, ha, haU⟩ ⟨b, hb, hbV⟩
  exact lt_asymm (show z.im < z.re ^ 2 / 2 from hzU) hzV

/-- (16.1) fails at the cusp: for `c ≥ 0` and `x = 1/(c + 1)`,
`c |x - (x + i x²)| < |x| + |x + i x²|`. -/
theorem tp_b2_numeric {c x : ℝ} (hc : 0 ≤ c) (hx : x = 1 / (c + 1)) :
    c * ‖(x : ℂ) - ((x : ℂ) + ((x ^ 2 : ℝ) : ℂ) * I)‖ <
      ‖(x : ℂ)‖ + ‖(x : ℂ) + ((x ^ 2 : ℝ) : ℂ) * I‖ := by
  have hxpos : 0 < x := by
    rw [hx]
    positivity
  have hcx : c * x < 1 := by
    rw [hx, mul_one_div, div_lt_one (by linarith)]
    linarith
  have h1 : (x : ℂ) - ((x : ℂ) + ((x ^ 2 : ℝ) : ℂ) * I) = -(((x ^ 2 : ℝ) : ℂ) * I) := by ring
  rw [h1, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_of_nonneg (sq_nonneg x),
    Complex.norm_of_nonneg hxpos.le]
  have h2 := norm_nonneg ((x : ℂ) + ((x ^ 2 : ℝ) : ℂ) * I)
  nlinarith

/-- The core of the cusp example (book §16.1): the curve `S` formed by the ray `[0, ∞)` and the
arc `y = x²` (`x ≥ 0`) is not `g(ℝ)` for a `K`-q.c. map `g` of the plane onto itself.  The two
open arcs of `S ∖ {0}` lie in the disjoint open sets `y < x²/2` and `y > x²/2`, so the preimages
of `x` and `x + i x²` lie on opposite sides of `g⁻¹(0)`; then (16.1) at `(x, 0, x + i x²)` with
`x = 1/(λ(K) + 1)` fails. -/
theorem tp_b2_not_image {g : ℂ → ℂ} {K : ℝ} (hg : IsKQC g univ K) (hgs : g '' univ = univ)
    (hS : {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} ∪ {z : ℂ | 0 ≤ z.re ∧ z.im = z.re ^ 2} = g '' realLine) :
    False := by
  have hgc : Continuous g := continuousOn_univ.1 hg.2.2.1.1
  have hinj : Function.Injective g := fun a b h => hg.2.2.1.2.1 (mem_univ a) (mem_univ b) h
  -- the points of `S` are the `g t`, `t` real
  have hmem : ∀ z : ℂ, z ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re} ∪ {z : ℂ | 0 ≤ z.re ∧ z.im = z.re ^ 2} →
      ∃ t : ℝ, g t = z := by
    intro z hz
    rw [hS] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    refine ⟨w.re, congrArg g (Complex.ext (by simp) ?_)⟩
    simpa using hw.symm
  obtain ⟨x₀, hx₀⟩ := hmem 0 (Or.inl ⟨by simp, by simp⟩)
  -- off `x₀`, `g t` lies in `{y < x²/2} ∪ {y > x²/2}`
  have hcov : ∀ t : ℝ, t ≠ x₀ →
      g t ∈ {z : ℂ | z.im < z.re ^ 2 / 2} ∪ {z : ℂ | z.re ^ 2 / 2 < z.im} := by
    intro t ht
    refine tp_b2_mem_cover ?_ fun h0 => ht (Complex.ofReal_injective (hinj (h0.trans hx₀.symm)))
    rw [hS]
    exact ⟨t, by simp [realLine], rfl⟩
  -- the test points `x` and `x + i x²`, `x = 1/(λ(K) + 1)`
  have hlam : 0 ≤ lambdaInv K := zero_le_one.trans (td_one_le_lambdaInv hg.2.1)
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 / (lambdaInv K + 1) := ⟨_, rfl⟩
  have hnum := tp_b2_numeric hlam hx
  have hxpos : 0 < x := by
    rw [hx]
    positivity
  have hre : ((x : ℂ) + ((x ^ 2 : ℝ) : ℂ) * I).re = x := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
      add_zero]
  have him : ((x : ℂ) + ((x ^ 2 : ℝ) : ℂ) * I).im = x ^ 2 := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one,
      zero_add]
  obtain ⟨t₁, ht₁⟩ :=
    hmem (x : ℂ) (Or.inl ⟨Complex.ofReal_im x, (Complex.ofReal_re x).symm ▸ hxpos.le⟩)
  obtain ⟨t₃, ht₃⟩ :=
    hmem ((x : ℂ) + ((x ^ 2 : ℝ) : ℂ) * I) (Or.inr ⟨hre ▸ hxpos.le, by rw [hre, him]⟩)
  have hU₁ : (g t₁).im < (g t₁).re ^ 2 / 2 := by
    rw [ht₁, Complex.ofReal_im, Complex.ofReal_re]
    positivity
  have hV₃ : (g t₃).re ^ 2 / 2 < (g t₃).im := by
    rw [ht₃, hre, him]
    linarith [pow_pos hxpos 2]
  have hne₁ : t₁ ≠ x₀ := fun h => by
    rw [h, hx₀] at ht₁
    exact hxpos.ne' (Complex.ofReal_eq_zero.mp ht₁.symm)
  have hne₃ : t₃ ≠ x₀ := fun h => by
    rw [h, hx₀] at ht₃
    have h0 := congrArg Complex.re ht₃
    rw [hre, Complex.zero_re] at h0
    exact hxpos.ne h0
  -- `t₁` and `t₃` are not on the same side of `x₀`
  have hconn : ∀ J : Set ℝ, IsPreconnected J → (∀ t ∈ J, t ≠ x₀) → t₁ ∈ J → t₃ ∈ J → False := by
    intro J hJ hJx h1 h3
    exact tp_b2_not_both (a := g t₁) (b := g t₃)
      (hJ.image (fun t : ℝ => g t) (hgc.comp continuous_ofReal).continuousOn)
      (by rintro _ ⟨t, ht, rfl⟩; exact hcov t (hJx t ht)) ⟨t₁, h1, rfl⟩ ⟨t₃, h3, rfl⟩ hU₁ hV₃
  rcases lt_or_gt_of_ne hne₁ with h1 | h1 <;> rcases lt_or_gt_of_ne hne₃ with h3 | h3
  · exact hconn (Iio x₀) isPreconnected_Iio (fun t ht => ht.ne) h1 h3
  · have h := thm16_1_three_point hg hgs h1 h3
    rw [ht₁, hx₀, ht₃, sub_zero, zero_sub, norm_neg] at h
    linarith
  · have h := thm16_1_three_point hg hgs h3 h1
    rw [ht₁, hx₀, ht₃, sub_zero, zero_sub, norm_neg, norm_sub_rev] at h
    linarith
  · exact hconn (Ioi x₀) isPreconnected_Ioi (fun t ht => ht.ne') h1 h3

/-- §16.1: the Jordan curve formed by the positive real axis and the arc `y = x²` (`x ≥ 0`) is
not a quasicircle. -/
theorem cusp_not_quasicircle :
    ¬ IsQuasicircle (toExt ({z : ℂ | z.im = 0 ∧ 0 ≤ z.re} ∪ {z : ℂ | 0 ≤ z.re ∧ z.im = z.re ^ 2}) ∪
      {extInf}) := by
  rintro ⟨K, hC⟩
  obtain ⟨g, hg, hgs, hCg⟩ := tp_quasicircle_through_inf hC (Or.inr rfl)
  exact tp_b2_not_image hg hgs (tp_b2_eq_of_toExt_union hCg)

/-- §16.1: an ellipse `x²/a² + y²/b² = 1`, `a ≥ b > 0`, is an `a/b`-quasicircle (the image of the
unit circle under the affine map `z ↦ ((a+b)/2) z + ((a-b)/2) z̄`, which sends `e^{iθ}` to
`a cos θ + i b sin θ` with constant `|μ| = (a-b)/(a+b)`, hence `K = a/b`). -/
theorem ellipse_isKQuasicircle {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    IsKQuasicircle (toExt {z : ℂ | z.re ^ 2 / a ^ 2 + z.im ^ 2 / b ^ 2 = 1}) (a / b) := by
  have ha : 0 < a := hb.trans_le hab
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  set A : ℂ := (((a + b) / 2 : ℝ) : ℂ) with hA_def
  set B : ℂ := (((a - b) / 2 : ℝ) : ℂ) with hB_def
  set f : ℂ → ℂ := fun z => A * z + B * conj z + 0 with hf_def
  -- norms of the affine coefficients
  have hAnorm : ‖A‖ = (a + b) / 2 := by
    rw [hA_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hBnorm : ‖B‖ = (a - b) / 2 := by
    rw [hB_def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hlt : ‖B‖ < ‖A‖ := by rw [hAnorm, hBnorm]; linarith
  have hK : (‖A‖ + ‖B‖) / (‖A‖ - ‖B‖) = a / b := by
    have h1 : (a + b) / 2 + (a - b) / 2 = a := by ring
    have h2 : (a + b) / 2 - (a - b) / 2 = b := by ring
    rw [hAnorm, hBnorm, h1, h2]
  -- `f` is `a/b`-quasiconformal on the whole plane
  have hqc : IsKQC f univ (a / b) := by
    have h0 := isKQC_of_isC1Quasiconformal
      (affine_isC1Quasiconformal (A := A) (B := B) (C := 0) hlt).1
    rw [hK] at h0
    rw [hf_def]
    exact h0
  -- coordinate formulas: `f(z)` has real part `a·Re z` and imaginary part `b·Im z`
  have hfre : ∀ z : ℂ, (f z).re = a * z.re := fun z => by
    simp only [hf_def, hA_def, hB_def, add_zero, Complex.add_re, Complex.re_ofReal_mul,
      Complex.conj_re]
    ring
  have hfim : ∀ z : ℂ, (f z).im = b * z.im := fun z => by
    simp only [hf_def, hA_def, hB_def, add_zero, Complex.add_im, Complex.im_ofReal_mul,
      Complex.conj_im]
    ring
  -- `f` maps the point `Re w / a + i Im w / b` back to `w`
  have hpre : ∀ w : ℂ, f (((w.re / a : ℝ) : ℂ) + ((w.im / b : ℝ) : ℂ) * I) = w := by
    intro w
    have hz0re : (((w.re / a : ℝ) : ℂ) + ((w.im / b : ℝ) : ℂ) * I).re = w.re / a := by simp
    have hz0im : (((w.re / a : ℝ) : ℂ) + ((w.im / b : ℝ) : ℂ) * I).im = w.im / b := by simp
    apply Complex.ext
    · rw [hfre, hz0re]; field_simp
    · rw [hfim, hz0im]; field_simp
  -- hence `f` is surjective
  have hsurj : f '' univ = univ := by
    rw [eq_univ_iff_forall]
    exact fun w => ⟨_, mem_univ _, hpre w⟩
  -- the image of the unit circle is exactly the ellipse
  have himg : f '' sphere 0 1 = {z : ℂ | z.re ^ 2 / a ^ 2 + z.im ^ 2 / b ^ 2 = 1} := by
    ext w
    simp only [mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hz
      have hz2 : z.re ^ 2 + z.im ^ 2 = 1 := by
        have h := Complex.sq_norm z
        rw [Complex.normSq_apply, hz, one_pow] at h
        rw [pow_two, pow_two]; linarith
      rw [hfre, hfim]
      have hcalc : (a * z.re) ^ 2 / a ^ 2 + (b * z.im) ^ 2 / b ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        field_simp
      rw [hcalc, hz2]
    · intro hw
      refine ⟨((w.re / a : ℝ) : ℂ) + ((w.im / b : ℝ) : ℂ) * I, ?_, hpre w⟩
      rw [mem_sphere_zero_iff_norm]
      have hn := norm_nonneg (((w.re / a : ℝ) : ℂ) + ((w.im / b : ℝ) : ℂ) * I)
      have hsq : ‖((w.re / a : ℝ) : ℂ) + ((w.im / b : ℝ) : ℂ) * I‖ ^ 2 = 1 := by
        rw [Complex.sq_norm, Complex.normSq_add_mul_I, div_pow, div_pow]
        exact hw
      rw [← Real.sqrt_sq hn, hsq, Real.sqrt_one]
  -- assemble: the ellipse is the image of the unit circle, with the identity Möbius map
  refine ⟨f, hqc, hsurj, mobiusExt 1 0 0 1, ⟨1, 0, 0, 1, by norm_num, rfl⟩, ?_⟩
  -- `mobiusExt 1 0 0 1` is the identity on finite points
  have hMcoe : ∀ z : ℂ, mobiusExt 1 0 0 1 (↑z) = ↑z := fun z => by
    rw [mobiusExt_coe (by simp : (0 : ℂ) * z + 1 ≠ 0)]
    simp [mobiusFn]
  -- `OnePoint.map f` pushes the coerced circle to the coerced image
  have hmap : OnePoint.map f '' toExt (sphere 0 1) = toExt (f '' sphere 0 1) := by
    unfold toExt
    rw [← image_comp, ← image_comp]
    exact image_congr fun x _ => by simp
  have hMob : mobiusExt 1 0 0 1 '' toExt (f '' sphere 0 1) = toExt (f '' sphere 0 1) := by
    unfold toExt
    rw [← image_comp]
    exact image_congr fun x _ => hMcoe x
  rw [hmap, hMob, himg]

/-- The point of `ℂ` represented by a point of `ℂ̄` (`∞ ↦ 0`, a junk value). -/
def extToC (p : ExtPlane) : ℂ := OnePoint.elim p 0 id

/-- **Definition 16.2** (拟共形反射).  Let the Jordan curve `C` split `ℂ̄` into `A₁` and `A₂`.  A
quasiconformal reflection in `C` is a homeomorphism `F` of `A₁ ∪ C` onto `A₂ ∪ C` which is
anti-quasiconformal on `A₁` (i.e. `z ↦ conj F(z)` is quasiconformal) and fixes every point of
`C`. -/
def IsQCReflection (C A₁ A₂ : Set ExtPlane) (F : ExtPlane → ExtPlane) : Prop :=
  ContinuousOn F (A₁ ∪ C) ∧ InjOn F (A₁ ∪ C) ∧ F '' A₁ = A₂ ∧ (∀ p ∈ C, F p = p) ∧
    ∃ K : ℝ, IsKQC (fun z : ℂ => conj (extToC (F z)))
      {z : ℂ | (z : ExtPlane) ∈ A₁ ∧ F z ≠ extInf} K

/-- `A₁` and `A₂` are the two complementary components of the Jordan curve `C` in `ℂ̄`. -/
def AreComplementaryComponents (C A₁ A₂ : Set ExtPlane) : Prop :=
  IsJordanCurve C ∧ ∃ p₁ ∈ Cᶜ, ∃ p₂ ∈ Cᶜ, A₁ = connectedComponentIn Cᶜ p₁ ∧
    A₂ = connectedComponentIn Cᶜ p₂ ∧ A₁ ≠ A₂

/-- A point of `ℂ̄` is `∞`, real, in `ℍ` or in `𝕃`. -/
theorem wd_b_cases (p : ExtPlane) :
    p = extInf ∨ (∃ x : ℝ, p = (((x : ℝ) : ℂ) : ExtPlane)) ∨ (∃ z ∈ upperHalf, p = (z : ExtPlane)) ∨
      ∃ z ∈ lowerHalf, p = (z : ExtPlane) := by
  induction p using OnePoint.rec with
  | infty => exact Or.inl rfl
  | coe z =>
    rcases lt_trichotomy z.im 0 with hlt | heq | hgt
    · exact Or.inr (Or.inr (Or.inr ⟨z, hlt, rfl⟩))
    · refine Or.inr (Or.inl ⟨z.re, ?_⟩)
      congr 1
      exact Complex.ext (by simp) (by simp [heq])
    · exact Or.inr (Or.inr (Or.inl ⟨z, hgt, rfl⟩))

/-- `∞` lies in the closure of `ℍ` in `ℂ̄`. -/
theorem wd_b_infty_mem_closure_upper : extInf ∈ closure (toExt upperHalf) :=
  frontier_subset_closure infty_mem_frontier_upperHalf

/-- A real point lies in the closure of `ℍ` in `ℂ̄`. -/
theorem wd_b_real_mem_closure_upper (x : ℝ) : (((x : ℝ) : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) :=
  frontier_subset_closure (ofReal_mem_frontier_upperHalf x)

/-- A real point lies in the closure of `𝕃` in `ℂ̄`. -/
theorem wd_b_real_mem_closure_lower (x : ℝ) : (((x : ℝ) : ℂ) : ExtPlane) ∈ closure (toExt lowerHalf) := by
  have h1 : (x : ℂ) ∈ closure lowerHalf := by
    rw [show lowerHalf = {z : ℂ | z.im < 0} from rfl, Complex.closure_setOfPred_im_lt]
    show (x : ℂ).im ≤ 0
    rw [Complex.ofReal_im]
  exact image_closure_subset_closure_image OnePoint.continuous_coe ⟨_, h1, rfl⟩

/-- The closure of `ℍ` in `ℂ̄` misses `𝕃`. -/
theorem wd_b_closure_upper_disjoint : Disjoint (closure (toExt upperHalf)) (toExt lowerHalf) := by
  refine Disjoint.closure_left ?_ (OnePoint.isOpen_image_coe.2 (isOpen_lt continuous_im continuous_const))
  rw [Set.disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
  rw [OnePoint.coe_injective hwz] at hw
  exact lt_asymm (show (0 : ℝ) < z.im from hz) hw

/-- The closure of `𝕃` in `ℂ̄` misses `ℍ`. -/
theorem wd_b_closure_lower_disjoint : Disjoint (closure (toExt lowerHalf)) (toExt upperHalf) := by
  refine Disjoint.closure_left ?_ (OnePoint.isOpen_image_coe.2 isOpen_upperHalf)
  rw [Set.disjoint_left]
  rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
  rw [OnePoint.coe_injective hwz] at hw
  exact lt_asymm (show z.im < 0 from hz) hw

/-- A point in the closures of both `ℍ` and `𝕃` is `∞` or real. -/
theorem wd_b_closure_inter {p : ExtPlane} (h₁ : p ∈ closure (toExt upperHalf))
    (h₂ : p ∈ closure (toExt lowerHalf)) : p = extInf ∨ ∃ x : ℝ, p = (((x : ℝ) : ℂ) : ExtPlane) := by
  rcases wd_b_cases p with h | h | ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact (disjoint_left.1 wd_b_closure_lower_disjoint h₂ ⟨z, hz, rfl⟩).elim
  · exact (disjoint_left.1 wd_b_closure_upper_disjoint h₁ ⟨z, hz, rfl⟩).elim

/-- A point of the closure of `ℍ` in `ℂ̄` is `∞`, real or in `ℍ`. -/
theorem wd_b_closure_upper_cases {p : ExtPlane} (hp : p ∈ closure (toExt upperHalf)) :
    p = extInf ∨ (∃ x : ℝ, p = (((x : ℝ) : ℂ) : ExtPlane)) ∨ ∃ z ∈ upperHalf, p = (z : ExtPlane) := by
  rcases wd_b_cases p with h | h | h | ⟨z, hz, rfl⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact (disjoint_left.1 wd_b_closure_upper_disjoint hp ⟨z, hz, rfl⟩).elim

/-- A point of `ℂ̄` off the closure of `ℍ` is a point of `𝕃`. -/
theorem wd_b_not_mem_closure_upper {p : ExtPlane} (hp : p ∉ closure (toExt upperHalf)) :
    ∃ z ∈ lowerHalf, p = (z : ExtPlane) := by
  rcases wd_b_cases p with rfl | ⟨x, rfl⟩ | ⟨z, hz, rfl⟩ | h
  · exact absurd wd_b_infty_mem_closure_upper hp
  · exact absurd (wd_b_real_mem_closure_upper x) hp
  · exact (hp (subset_closure ⟨z, hz, rfl⟩)).elim
  · exact h

/-- The inverse of a map continuous and injective on a closed subset `S` of `ℂ̄`, with image `T`: it is continuous on
`T`, maps `T` into `S`, and is a right inverse on `T` and a left inverse on `S`. -/
theorem wd_b_inv {F : ExtPlane → ExtPlane} {S T : Set ExtPlane} (hS : IsClosed S) (hFc : ContinuousOn F S)
    (hFi : InjOn F S) (hFS : F '' S = T) :
    ContinuousOn (Function.invFunOn F S) T ∧ MapsTo (Function.invFunOn F S) T S ∧
      (∀ q ∈ T, F (Function.invFunOn F S q) = q) ∧ ∀ p ∈ S, Function.invFunOn F S (F p) = p := by
  subst hFS
  exact ⟨continuousOn_invFunOn_of_isClosed hS hFc hFi, fun q hq => Function.invFunOn_mem hq,
    fun q hq => Function.invFunOn_eq hq, fun p hp => hFi.leftInvOn_invFunOn hp⟩

/-- On `V`, the inverse of a homeomorphic extension `F` of `f : U → V` is the inverse of `f`. -/
theorem wd_b_invFunOn_coe {f : ℂ → ℂ} {U V : Set ℂ} {F : ExtPlane → ExtPlane} (hF : IsHomeoExtension f U V F)
    (hfUV : f '' U = V) {v : ℂ} (hv : v ∈ V) :
    Function.invFunOn F (closure (toExt U)) (v : ExtPlane) = ((Function.invFunOn f U v : ℂ) : ExtPlane) ∧
      Function.invFunOn f U v ∈ U := by
  have hv' : v ∈ f '' U := hfUV.symm ▸ hv
  have hu : Function.invFunOn f U v ∈ U := Function.invFunOn_mem hv'
  have h1 : F ((Function.invFunOn f U v : ℂ) : ExtPlane) = (v : ExtPlane) := by
    rw [hF.1 _ hu, Function.invFunOn_eq hv']
  refine ⟨?_, hu⟩
  rw [← h1]
  exact hF.2.2.1.leftInvOn_invFunOn (subset_closure ⟨_, hu, rfl⟩)

/-- Pasting across `ℝ ∪ {∞}`: a map of `ℂ̄` agreeing on `ℍ̄` with a map continuous there and on `𝕃̄` with a map
continuous there is continuous. -/
theorem wd_b_paste {F F₁ F₂ : ExtPlane → ExtPlane} (h₁ : ContinuousOn F₁ (closure (toExt upperHalf)))
    (h₂ : ContinuousOn F₂ (closure (toExt lowerHalf))) (hF₁ : EqOn F F₁ (closure (toExt upperHalf)))
    (hF₂ : EqOn F F₂ (closure (toExt lowerHalf))) : Continuous F := by
  have hU : closure (toExt upperHalf) ∪ closure (toExt lowerHalf) = univ := by
    refine eq_univ_of_forall fun p => ?_
    rcases wd_b_cases p with rfl | ⟨x, rfl⟩ | ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · exact Or.inl wd_b_infty_mem_closure_upper
    · exact Or.inl (wd_b_real_mem_closure_upper x)
    · exact Or.inl (subset_closure ⟨z, hz, rfl⟩)
    · exact Or.inr (subset_closure ⟨z, hz, rfl⟩)
  rw [← continuousOn_univ, ← hU]
  exact (h₁.congr hF₁).union_of_isClosed (h₂.congr hF₂) isClosed_closure isClosed_closure

/-- A continuous injection of `ℂ̄` into itself fixing `∞` restricts to a homeomorphism of `ℂ` onto `ℂ`
(`lemma12_1`). -/
theorem wd_b_plane_homeo {F : ExtPlane → ExtPlane} (hF : Continuous F) (hFi : Function.Injective F)
    (hFinf : F extInf = extInf) :
    (∀ z : ℂ, ((extToC (F z) : ℂ) : ExtPlane) = F z) ∧
      IsHomeomorphOnto (fun z : ℂ => extToC (F z)) univ univ := by
  have hcoe : ∀ z : ℂ, ((extToC (F z) : ℂ) : ExtPlane) = F z := by
    intro z
    have hne : F z ≠ extInf := fun h => OnePoint.coe_ne_infty z (hFi (h.trans hFinf.symm))
    obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.1 hne
    rw [← hw]
    rfl
  refine ⟨hcoe, ?_⟩
  have hcomp : ((↑) : ℂ → ExtPlane) ∘ (fun z : ℂ => extToC (F z)) = F ∘ ((↑) : ℂ → ExtPlane) := funext hcoe
  have hc : Continuous (fun z : ℂ => extToC (F z)) := by
    rw [OnePoint.isOpenEmbedding_coe.isEmbedding.continuous_iff, hcomp]
    exact hF.comp OnePoint.continuous_coe
  have hi : Function.Injective (fun z : ℂ => extToC (F z)) := by
    intro a b hab
    have h := congrArg ((↑) : ℂ → ExtPlane) hab
    simp only [hcoe] at h
    exact OnePoint.coe_injective (hFi h)
  have ht : Tendsto (fun z : ℂ => extToC (F z)) (cocompact ℂ) (cocompact ℂ) := by
    rw [← coclosedCompact_eq_cocompact, ← OnePoint.comap_coe_nhds_infty, tendsto_comap_iff, hcomp]
    have h1 : Tendsto F (𝓝 extInf) (𝓝 extInf) := by
      have h2 := hF.tendsto extInf
      rwa [hFinf] at h2
    exact h1.comp tendsto_comap
  obtain ⟨e, he⟩ := lemma12_1 hc ht fun _ => ⟨univ, univ_mem, hi.injOn⟩
  rw [← he]
  exact nxI1_isHomeomorphOnto_of_homeomorph e

/-- A finite point lies in `toExt s` iff it lies in `s`. -/
theorem wd_n_coe_mem_toExt {s : Set ℂ} {z : ℂ} : (z : ExtPlane) ∈ toExt s ↔ z ∈ s :=
  OnePoint.coe_injective.mem_set_image

/-- `∞` does not lie in `toExt s`. -/
theorem wd_n_infty_notMem_toExt {s : Set ℂ} : extInf ∉ toExt s := by
  rintro ⟨z, -, hz⟩
  exact OnePoint.coe_ne_infty z hz

/-- For a bijection `g` of the plane, the complement of `g(ℝ) ∪ {∞}` in `ℂ̄` is `g(ℍ) ∪ g(𝕃)`. -/
theorem wd_n_compl_eq {g : ℂ → ℂ} (hg : Function.Bijective g) :
    (toExt (g '' realLine) ∪ {extInf})ᶜ = toExt (g '' upperHalf) ∪ toExt (g '' lowerHalf) := by
  ext p
  induction p using OnePoint.rec with
  | infty =>
    refine iff_of_false (fun h => h (Or.inr rfl)) ?_
    rintro (h | h) <;> exact wd_n_infty_notMem_toExt h
  | coe z =>
    obtain ⟨w, rfl⟩ := hg.2 z
    simp only [mem_compl_iff, mem_union, mem_singleton_iff, wd_n_coe_mem_toExt,
      hg.1.mem_set_image, OnePoint.coe_ne_infty, or_false]
    show ¬ w.im = 0 ↔ 0 < w.im ∨ w.im < 0
    rw [← ne_eq, ne_comm, ne_iff_lt_or_gt, or_comm]

/-- A set `S = U ∪ V` with `U`, `V` disjoint and open and `U` preconnected: the component of `S` through a point of `U`
is `U`. -/
theorem wd_n_component_eq {S U V : Set ExtPlane} (hS : S = U ∪ V) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hUc : IsPreconnected U) {p : ExtPlane} (hp : p ∈ U) : connectedComponentIn S p = U := by
  have hpS : p ∈ S := hS ▸ Or.inl hp
  refine Subset.antisymm ?_ (hUc.subset_connectedComponentIn hp (hS ▸ subset_union_left))
  exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hU hV hUV
    ((connectedComponentIn_subset S p).trans hS.subset) ⟨p, mem_connectedComponentIn hpS, hp⟩

/-- The two complementary components of `e(ℝ) ∪ {∞}` for a homeomorphism `e` of the plane: every component of the
complement is `e(ℍ)` or `e(𝕃)` (these are open, disjoint and connected, and cover the complement). -/
theorem wd_n_components (e : ℂ ≃ₜ ℂ) {p : ExtPlane} (hp : p ∈ (toExt (e '' realLine) ∪ {extInf})ᶜ) :
    connectedComponentIn (toExt (e '' realLine) ∪ {extInf})ᶜ p = toExt (e '' upperHalf) ∨
      connectedComponentIn (toExt (e '' realLine) ∪ {extInf})ᶜ p = toExt (e '' lowerHalf) := by
  have hS := wd_n_compl_eq e.bijective
  have hoU : IsOpen (toExt (e '' upperHalf)) := OnePoint.isOpen_image_coe.2 (e.isOpenMap _ isOpen_upperHalf)
  have hoL : IsOpen (toExt (e '' lowerHalf)) :=
    OnePoint.isOpen_image_coe.2 (e.isOpenMap _ (isOpen_lt continuous_im continuous_const))
  have hdisj : Disjoint (toExt (e '' upperHalf)) (toExt (e '' lowerHalf)) := by
    refine (disjoint_image_iff OnePoint.coe_injective).2 ((disjoint_image_iff e.injective).2 ?_)
    refine disjoint_left.2 fun z (hz : 0 < z.im) (hz' : z.im < 0) => ?_
    linarith
  have hcU : IsPreconnected (toExt (e '' upperHalf)) :=
    (isConnected_upperHalf.isPreconnected.image _ e.continuous.continuousOn).image _
      OnePoint.continuous_coe.continuousOn
  have hcL : IsPreconnected (toExt (e '' lowerHalf)) :=
    ((((convex_Iio (0 : ℝ)).linear_preimage Complex.imLm).isPreconnected).image _
      e.continuous.continuousOn).image _ OnePoint.continuous_coe.continuousOn
  rw [hS] at hp
  rcases hp with hp | hp
  · exact Or.inl (wd_n_component_eq hS hoU hoL hdisj hcU hp)
  · exact Or.inr (wd_n_component_eq (hS.trans (union_comm _ _)) hoL hoU hdisj.symm hcL hp)

/-- The image of a set under `z ↦ -z`, from a membership criterion. -/
theorem wd_n_neg_image {S T : Set ℂ} (h : ∀ z : ℂ, -z ∈ T ↔ z ∈ S) : (fun z : ℂ => -z) '' S = T := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (h z).2 hz
  · intro hw
    exact ⟨-w, (h (-w)).1 (by rwa [neg_neg]), neg_neg w⟩

/-- **N** (normal form of a quasicircle through `∞`, (⇒)): `C = g₀(ℝ) ∪ {∞}` for a `K`-q.c. map `g₀` of the plane
onto itself with `A₁ = g₀(ℍ)`, `A₂ = g₀(𝕃)` (`tp_quasicircle_through_inf`; `ℂ̄ ∖ C` has exactly the components
`g₀(ℍ)`, `g₀(𝕃)`; replace `g₀` by `g₀(-z)` if they are swapped). -/
theorem wd_normal_form {C : Set ExtPlane} {A₁ A₂ : Set ℂ} (hinf : extInf ∈ C)
    (hC : AreComplementaryComponents C (toExt A₁) (toExt A₂)) (hq : IsQuasicircle C) :
    ∃ (g₀ : ℂ → ℂ) (K : ℝ), IsKQC g₀ univ K ∧ g₀ '' univ = univ ∧ C = toExt (g₀ '' realLine) ∪ {extInf} ∧
      A₁ = g₀ '' upperHalf ∧ A₂ = g₀ '' lowerHalf := by
  obtain ⟨K, hK⟩ := hq
  obtain ⟨g, hg, hgs, rfl⟩ := tp_quasicircle_through_inf hK hinf
  obtain ⟨e, rfl⟩ := t1_homeomorph hg hgs
  obtain ⟨-, p₁, hp₁, p₂, hp₂, h₁, h₂, hne⟩ := hC
  have hinj : Function.Injective toExt := image_injective.2 OnePoint.coe_injective
  rcases wd_n_components e hp₁ with hc₁ | hc₁ <;> rcases wd_n_components e hp₂ with hc₂ | hc₂
  · exact absurd (h₁.trans (hc₁.trans (hc₂.symm.trans h₂.symm))) hne
  · exact ⟨e, K, hg, hgs, rfl, hinj (h₁.trans hc₁), hinj (h₂.trans hc₂)⟩
  · -- the components are swapped: precompose with `z ↦ -z`
    have hneg : IsKQC (fun z : ℂ => -z) univ 1 :=
      isKQC_one_of_conformal (D' := (fun z : ℂ => -z) '' univ) isOpen_univ
        ⟨differentiable_id.neg.differentiableOn, fun a _ b _ h => neg_injective h, rfl⟩
    have hK' := thm7_1_comp hneg hg (subset_univ _)
    rw [one_mul] at hK'
    have himg : ∀ S : Set ℂ, (fun z : ℂ => e (-z)) '' S = e '' ((fun z : ℂ => -z) '' S) :=
      fun S => (image_image e (fun z : ℂ => -z) S).symm
    have hR : (fun z : ℂ => -z) '' realLine = realLine :=
      wd_n_neg_image fun z => by
        show (-z).im = 0 ↔ z.im = 0
        rw [neg_im, neg_eq_zero]
    have hU : (fun z : ℂ => -z) '' upperHalf = lowerHalf :=
      wd_n_neg_image fun z => by
        show (-z).im < 0 ↔ 0 < z.im
        rw [neg_im, neg_lt_zero]
    have hL : (fun z : ℂ => -z) '' lowerHalf = upperHalf :=
      wd_n_neg_image fun z => by
        show 0 < (-z).im ↔ z.im < 0
        rw [neg_im, neg_pos]
    have huniv : (fun z : ℂ => -z) '' univ = univ := image_univ_of_surjective neg_surjective
    refine ⟨fun z => e (-z), K, hK', ?_, ?_, ?_, ?_⟩
    · rw [himg, huniv, hgs]
    · rw [himg, hR]
    · rw [himg, hU]
      exact hinj (h₁.trans hc₁)
    · rw [himg, hL]
      exact hinj (h₂.trans hc₂)
  · exact absurd (h₁.trans (hc₁.trans (hc₂.symm.trans h₂.symm))) hne

/-- Gluing across `ℝ` (a local copy of the S21 lemma `ut2_ruh_glue`, which lies downstream): a map of the plane which is
a homeomorphism onto its image and is `K`-q.c. on `ℍ` and on `𝕃` is `K`-q.c. on `ℂ` (`s13x_removable` with `L = ℝ`). -/
theorem wd_glue {f : ℂ → ℂ} {K : ℝ} (hK : 1 ≤ K) (hf : IsHomeomorphOnto f univ (f '' univ))
    (hU : IsKQC f upperHalf K) (hL : IsKQC f lowerHalf K) : IsKQC f univ K := by
  refine s13x_removable (L := {z : ℂ | z.im = 0}) isOpen_univ hK hf gzE_volume_im_eq_zero ?_ ?_ ?_
  · -- a vertical line meets the real axis in one point
    refine Eventually.of_forall fun x => (countable_singleton (0 : ℝ)).mono fun y hy => ?_
    simpa using hy
  · -- a horizontal line off the real axis misses it
    have h0 : ∀ᵐ y : ℝ, y ∉ ({0} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.1 (measure_singleton 0)
    filter_upwards [h0] with y hy
    refine countable_empty.mono fun x hx => ?_
    exact absurd (by simpa using hx) hy
  · -- off the real axis, a point lies in `ℍ` or in `𝕃`
    rintro w ⟨-, hw⟩
    have hw' : w.im ≠ 0 := hw
    rcases lt_or_gt_of_ne hw' with hlt | hgt
    · exact ⟨lowerHalf, hL.1, hlt, subset_univ _, hL⟩
    · exact ⟨upperHalf, hU.1, hgt, subset_univ _, hU⟩

/-! ### Theorem 16.2 (s21u prover Q16): helpers -/

/-- Composition of fractional linear transformations of `ℂ̄` is given by the matrix product (the inner one
invertible); a local copy of the S24 lemma `k24_mobiusExt_comp`, which lies downstream. -/
theorem s16p_mobiusExt_comp {a b c d a' b' c' d' : ℂ} (h' : a' * d' - b' * c' ≠ 0) (p : ExtPlane) :
    mobiusExt a b c d (mobiusExt a' b' c' d' p) =
      mobiusExt (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') p := by
  induction p using OnePoint.rec with
  | infty =>
    by_cases hc' : c' = 0
    · have ha' : a' ≠ 0 := by
        rintro rfl
        apply h'
        simp [hc']
      rw [mobiusExt_infty_of_eq hc']
      by_cases hc : c = 0
      · rw [mobiusExt_infty_of_eq hc, mobiusExt_infty_of_eq (by simp [hc, hc'])]
      · have hne : c * a' + d * c' ≠ 0 := by
          rw [hc', mul_zero, add_zero]
          exact mul_ne_zero hc ha'
        rw [mobiusExt_infty_of_ne hc, mobiusExt_infty_of_ne hne]
        congr 1
        rw [div_eq_div_iff hc hne, hc']
        ring
    · rw [mobiusExt_infty_of_ne hc']
      have e : c * a' + d * c' = (c * (a' / c') + d) * c' := by
        field_simp
      by_cases hden : c * (a' / c') + d = 0
      · rw [mobiusExt_coe_of_eq_zero hden, mobiusExt_infty_of_eq (by rw [e, hden, zero_mul])]
      · have hne : c * a' + d * c' ≠ 0 := by
          rw [e]
          exact mul_ne_zero hden hc'
        rw [mobiusExt_coe hden, mobiusExt_infty_of_ne hne]
        congr 1
        rw [mobiusFn, div_eq_div_iff hden hne]
        field_simp
  | coe z =>
    by_cases hz : c' * z + d' = 0
    · have hnum : a' * z + b' ≠ 0 := by
        intro hab
        apply h'
        linear_combination a' * hz - c' * hab
      rw [mobiusExt_coe_of_eq_zero hz]
      have hden : (c * a' + d * c') * z + (c * b' + d * d') = c * (a' * z + b') := by
        linear_combination d * hz
      by_cases hc : c = 0
      · rw [mobiusExt_infty_of_eq hc, mobiusExt_coe_of_eq_zero (by rw [hden, hc, zero_mul])]
      · have hne : (c * a' + d * c') * z + (c * b' + d * d') ≠ 0 := by
          rw [hden]
          exact mul_ne_zero hc hnum
        rw [mobiusExt_infty_of_ne hc, mobiusExt_coe hne]
        congr 1
        rw [mobiusFn, div_eq_div_iff hc hne]
        linear_combination (a * d - b * c) * hz
    · rw [mobiusExt_coe hz]
      have hmd := mobiusFn_mul_den (a := a') (b := b') hz
      have key : (c * a' + d * c') * z + (c * b' + d * d') =
          (c * mobiusFn a' b' c' d' z + d) * (c' * z + d') := by
        linear_combination (-c) * hmd
      have keyN : (a * a' + b * c') * z + (a * b' + b * d') =
          (a * mobiusFn a' b' c' d' z + b) * (c' * z + d') := by
        linear_combination (-a) * hmd
      by_cases hw : c * mobiusFn a' b' c' d' z + d = 0
      · rw [mobiusExt_coe_of_eq_zero hw, mobiusExt_coe_of_eq_zero (by rw [key, hw, zero_mul])]
      · rw [mobiusExt_coe hw, mobiusExt_coe (by rw [key]; exact mul_ne_zero hw hz)]
        congr 1
        show (a * mobiusFn a' b' c' d' z + b) / (c * mobiusFn a' b' c' d' z + d) =
          ((a * a' + b * c') * z + (a * b' + b * d')) / ((c * a' + d * c') * z + (c * b' + d * d'))
        rw [key, keyN, mul_div_mul_right _ _ hz]

/-- The image of a quasicircle under a fractional linear transformation is a quasicircle. -/
theorem s16p_isQuasicircle_mobius_image {C : Set ExtPlane} (hC : IsQuasicircle C) {a b c d : ℂ}
    (h : a * d - b * c ≠ 0) : IsQuasicircle (mobiusExt a b c d '' C) := by
  obtain ⟨K, f, hf, hs, M, ⟨α, β, κ, δ, hdet, rfl⟩, rfl⟩ := hC
  refine ⟨K, f, hf, hs, mobiusExt (a * α + b * κ) (a * β + b * δ) (c * α + d * κ) (c * β + d * δ),
    ⟨_, _, _, _, ?_, rfl⟩, ?_⟩
  · have hmul : (a * α + b * κ) * (c * β + d * δ) - (a * β + b * δ) * (c * α + d * κ) =
        (a * d - b * c) * (α * δ - β * κ) := by ring
    rw [hmul]
    exact mul_ne_zero h hdet
  · rw [image_image]
    exact image_congr fun w _ => s16p_mobiusExt_comp hdet w

/-- A homeomorphism of `ℂ̄` carries the complementary components of a Jordan curve to those of its image. -/
theorem s16p_areComplementaryComponents_image {C A₁ A₂ : Set ExtPlane}
    (hC : AreComplementaryComponents C A₁ A₂) (e : ExtPlane ≃ₜ ExtPlane) :
    AreComplementaryComponents (e '' C) (e '' A₁) (e '' A₂) := by
  obtain ⟨hJ, p₁, hp₁, p₂, hp₂, h₁, h₂, hne⟩ := hC
  have hcompl : e '' Cᶜ = (e '' C)ᶜ := e.toEquiv.image_compl C
  refine ⟨uq_isJordanCurve_image e hJ, e p₁, ?_, e p₂, ?_, ?_, ?_, ?_⟩
  · rw [← hcompl]
    exact mem_image_of_mem e hp₁
  · rw [← hcompl]
    exact mem_image_of_mem e hp₂
  · rw [h₁, gsep_z_connectedComponentIn_image_homeomorph e hp₁, hcompl]
  · rw [h₂, gsep_z_connectedComponentIn_image_homeomorph e hp₂, hcompl]
  · intro h
    exact hne (image_injective.2 e.injective h)

/-- Elementary facts on the complementary components `A₁, A₂` of a Jordan curve `C`: `C` is closed, `A₁, A₂` are
open, connected, disjoint from each other and from `C`. -/
theorem s16p_basic {C A₁ A₂ : Set ExtPlane} (hC : AreComplementaryComponents C A₁ A₂) :
    IsClosed C ∧ IsOpen A₁ ∧ IsOpen A₂ ∧ IsConnected A₁ ∧ Disjoint A₁ C ∧ Disjoint A₂ C ∧
      Disjoint A₁ A₂ := by
  obtain ⟨hJ, p₁, hp₁, p₂, hp₂, h₁, h₂, hne⟩ := hC
  have hCc : IsClosed C := by
    obtain ⟨γ, hγc, -, hγr⟩ := hJ
    rw [← hγr]
    exact (isCompact_range hγc).isClosed
  have hCo : IsOpen Cᶜ := hCc.isOpen_compl
  refine ⟨hCc, h₁ ▸ hCo.connectedComponentIn, h₂ ▸ hCo.connectedComponentIn, ?_, ?_, ?_, ?_⟩
  · rw [h₁]
    exact isConnected_connectedComponentIn_iff.2 hp₁
  · rw [h₁]
    exact disjoint_compl_left.mono_left (connectedComponentIn_subset _ _)
  · rw [h₂]
    exact disjoint_compl_left.mono_left (connectedComponentIn_subset _ _)
  · rw [Set.disjoint_left]
    intro q hq₁ hq₂
    rw [h₁] at hq₁
    rw [h₂] at hq₂
    exact hne (by rw [h₁, h₂, connectedComponentIn_eq hq₁, connectedComponentIn_eq hq₂])

/-- Finitely many points are removable: a continuous injective map of an open set which is `K`-q.c. off a finite
set is `K`-q.c. (`s13x_removable`). -/
theorem s16p_isKQC_of_finite {g : ℂ → ℂ} {Ω L : Set ℂ} {K : ℝ} (hΩ : IsOpen Ω) (hK : 1 ≤ K)
    (hgc : ContinuousOn g Ω) (hgi : InjOn g Ω) (hL : L.Finite) (hg : IsKQC g (Ω \ L) K) : IsKQC g Ω K := by
  refine s13x_removable (L := L) hΩ hK (qcl_f_isHomeomorphOnto_of_injOn hΩ hgc hgi) (hL.measure_zero _)
    (Eventually.of_forall fun x => ?_) (Eventually.of_forall fun y => ?_)
    fun z hz => ⟨Ω \ L, hΩ.sdiff hL.isClosed, hz, sdiff_subset, hg⟩
  · refine (hL.preimage fun y₁ _ y₂ _ h => ?_).countable
    have h' := congrArg Complex.im h
    simpa using h'
  · refine (hL.preimage fun x₁ _ x₂ _ h => ?_).countable
    have h' := congrArg Complex.re h
    simpa using h'

/-- `ℂ̄ → ℂ` (`∞ ↦ 0`) is continuous at every finite point. -/
theorem s16p_continuousAt_extToC (z : ℂ) : ContinuousAt extToC (z : ExtPlane) := by
  show Tendsto extToC (𝓝 (z : ExtPlane)) (𝓝 (extToC z))
  rw [← OnePoint.isOpenEmbedding_coe.map_nhds_eq, tendsto_map'_iff]
  exact tendsto_id


/-- The frontier of a complementary component `A₁` of a Jordan curve `C ∋ ∞` is `C`: move a point `b` of the other
component `A₂` to `∞` by `w ↦ 1/(w - b)`.  The image curve lies in `ℂ`, and by the Jordan curve theorem the image of
`A₁` is its bounded complementary piece (the unbounded piece has `∞ ∈ e(A₂)` in its closure), whose frontier is the
image curve. -/
theorem s16p_frontier_eq {C A₁ A₂ : Set ExtPlane} (hC : AreComplementaryComponents C A₁ A₂)
    (hinf : extInf ∈ C) : frontier A₁ = C := by
  obtain ⟨-, -, hA₂o, -, -, -, hA₁₂⟩ := s16p_basic hC
  obtain ⟨hJ, p₁, hp₁, p₂, hp₂, h₁, h₂, -⟩ := hC
  have hp₂A : p₂ ∈ A₂ := h₂ ▸ mem_connectedComponentIn hp₂
  have hp₁A : p₁ ∈ A₁ := h₁ ▸ mem_connectedComponentIn hp₁
  obtain ⟨b, rfl⟩ : ∃ b : ℂ, p₂ = b :=
    (uq_j_eq_infty_or_coe p₂).resolve_left (by rintro rfl; exact hp₂ hinf)
  set e := mobiusHomeomorph 0 1 1 (-b) (uq_j_inv_det b) with he
  have heb : e (b : ExtPlane) = extInf := uq_j_mobiusInv_apply_self b
  have hinfC : extInf ∉ e '' C := by
    rintro ⟨c, hc, hce⟩
    rw [← heb] at hce
    rw [e.injective hce] at hc
    exact hp₂ hc
  set C₀ : Set ℂ := ((↑) : ℂ → ExtPlane) ⁻¹' (e '' C) with hC₀
  have hC₀e : toExt C₀ = e '' C := uq_j_toExt_preimage_coe hinfC
  have hJ₀ : IsJordanCurve (toExt C₀) := by
    rw [hC₀e]
    exact uq_isJordanCurve_image e hJ
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hAC, hBC, huniv, hAb, hBb⟩ := jordan_curve_theorem_complex_bounded hJ₀
  obtain ⟨hfA, -⟩ := frontier_pieces_eq_of_jordan_curve_theorem_complex hJ₀ hA hB hAc hBc hAB hAC hBC huniv
  have hcompl : e '' Cᶜ = (e '' C)ᶜ := e.toEquiv.image_compl C
  have hU₁ : e '' A₁ = connectedComponentIn (e '' C)ᶜ (e p₁) := by
    rw [h₁, gsep_z_connectedComponentIn_image_homeomorph e hp₁, hcompl]
  have hinfU₂ : extInf ∈ e '' A₂ := ⟨b, hp₂A, heb⟩
  have hU₂o : IsOpen (e '' A₂) := e.isOpenMap _ hA₂o
  have hU₁₂ : Disjoint (e '' A₁) (e '' A₂) := (disjoint_image_iff e.injective).2 hA₁₂
  have hU₁C : e '' A₁ ⊆ (e '' C)ᶜ := by
    rw [hU₁]
    exact connectedComponentIn_subset _ _
  have hsub : e '' A₁ ⊆ toExt A ∪ toExt B := by
    intro w hw
    induction w using OnePoint.rec with
    | infty => exact absurd hinfU₂ (disjoint_left.1 hU₁₂ hw)
    | coe z =>
      have hz : z ∉ C₀ := fun h => hU₁C hw h
      have hz' : z ∈ A ∪ B ∪ C₀ := huniv ▸ mem_univ z
      rcases hz' with (h | h) | h
      · exact Or.inl ⟨z, h, rfl⟩
      · exact Or.inr ⟨z, h, rfl⟩
      · exact absurd h hz
  have hAo' : IsOpen (toExt A) := OnePoint.isOpen_image_coe.2 hA
  have hBo' : IsOpen (toExt B) := OnePoint.isOpen_image_coe.2 hB
  have hABd : Disjoint (toExt A) (toExt B) := (disjoint_image_iff OnePoint.coe_injective).2 hAB
  have hpre : IsPreconnected (e '' A₁) := by
    rw [hU₁]
    exact isPreconnected_connectedComponentIn
  have hmem : e p₁ ∈ e '' A₁ := mem_image_of_mem e hp₁A
  have hSC : ∀ S : Set ℂ, Disjoint S C₀ → toExt S ⊆ (e '' C)ᶜ := by
    rintro S hS _ ⟨z, hz, rfl⟩ h
    rw [← hC₀e] at h
    exact disjoint_left.1 hS hz (coe_mem_toExt_iff.1 h)
  have key : ∀ S : Set ℂ, IsConnected S → Disjoint S C₀ → e '' A₁ ⊆ toExt S → e '' A₁ = toExt S := by
    intro S hS hSd hsubS
    refine Subset.antisymm hsubS ?_
    rw [hU₁]
    exact (hS.isPreconnected.image _ OnePoint.continuous_coe.continuousOn).subset_connectedComponentIn
      (hsubS hmem) (hSC S hSd)
  rcases hpre.subset_or_subset hAo' hBo' hABd hsub with hsA | hsB
  · have heq := key A hAc hAC hsA
    have hfr : frontier (e '' A₁) = e '' C := by
      rw [heq, frontier_toExt_of_isBounded' hAb hA, hfA, hC₀e]
    rw [← e.image_frontier] at hfr
    exact image_injective.2 e.injective hfr
  · exfalso
    have heq := key B hBc hBC hsB
    have hcl : extInf ∈ closure (e '' A₁) := heq ▸ extInf_mem_closure_toExt_of_not_isBounded hBb
    exact disjoint_left.1 (hU₁₂.closure_left hU₂o) hcl hinfU₂

/-- A Jordan domain with `∞` on its boundary has a conformal map onto `ℍ` whose homeomorphic extension fixes `∞`
(`uq_exists_uniformizer`, normalized by a real Möbius map); a local copy of the S20 lemma `s20l_uniformizer_inf`,
which lies downstream. -/
theorem s16p_uniformizer_inf {Ω : Set ℂ} (hΩ : IsJordanDomain Ω) (hinf : extInf ∈ frontier (toExt Ω)) :
    ∃ φ : ℂ → ℂ, IsConformalOnto φ Ω upperHalf ∧
      ∃ Φ : ExtPlane → ExtPlane, IsHomeoExtension φ Ω upperHalf Φ ∧ Φ extInf = extInf := by
  obtain ⟨ψ, hψ, Ψ, hΨ⟩ := uq_exists_uniformizer hΩ
  have hHo : IsOpen (toExt upperHalf) := OnePoint.isOpen_image_coe.2 isOpen_upperHalf
  have hmemcl : extInf ∈ closure (toExt Ω) := frontier_subset_closure hinf
  have hΨfr : Ψ extInf ∈ frontier (toExt upperHalf) := by
    refine ⟨hΨ.2.2.2 ▸ mem_image_of_mem Ψ hmemcl, ?_⟩
    rw [hHo.interior_eq]
    rintro ⟨w, hw, hwe⟩
    have hw' : w ∈ ψ '' Ω := hψ.2.2.symm ▸ hw
    obtain ⟨z, hz, rfl⟩ := hw'
    have hzcl : ((z : ℂ) : ExtPlane) ∈ closure (toExt Ω) := subset_closure ⟨z, hz, rfl⟩
    have h1 : Ψ (z : ExtPlane) = Ψ extInf := by rw [hΨ.1 z hz, hwe]
    have h2 := hΨ.2.2.1 hzcl hmemcl h1
    exact OnePoint.coe_ne_infty z h2
  rcases uq_k_frontier_cases hΨfr with ⟨x₀, hx₀⟩ | hx₀
  · have hdet : (0 : ℝ) < 0 * (-x₀) - (-1) * 1 := by norm_num
    obtain ⟨hMc, hMe⟩ := uq_k_mobius_auto hdet
    refine ⟨mobiusFn ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((-x₀ : ℝ) : ℂ) ∘ ψ,
      hMc.comp hψ, _, hMe.comp hΨ hψ.mapsTo, ?_⟩
    show mobiusExt _ _ _ _ (Ψ extInf) = extInf
    rw [hx₀]
    exact mobiusExt_coe_of_eq_zero (by push_cast; ring)
  · exact ⟨ψ, hψ, Ψ, hΨ, hx₀⟩

/-- **(⇐) of Theorem 16.2 for a curve through `∞`** (the book's gluing across `ℝ`): with `φ : A₁ → ℍ` conformal,
extended by `Φ` with `Φ(∞) = ∞`, the map `E = Φ⁻¹` on `ℍ̄`, `E = F ∘ Φ⁻¹ ∘ conj` on `𝕃̄` is a homeomorphism of `ℂ̄`
fixing `∞` (they agree on `ℝ ∪ {∞}`, where `Φ⁻¹` lands on `C` and `F` is the identity), conformal on `ℍ` and
`K`-q.c. on `𝕃`; so it is `K`-q.c. (`wd_glue`) and `C = E(ℝ) ∪ {∞}` is a quasicircle. -/
theorem s16p_bwd_inf {C A₁ A₂ : Set ExtPlane} (hC : AreComplementaryComponents C A₁ A₂) (hinf : extInf ∈ C)
    {F : ExtPlane → ExtPlane} (hF : IsQCReflection C A₁ A₂ F) : IsQuasicircle C := by
  classical
  obtain ⟨-, hA₁o, -, hA₁c, hA₁C, hA₂C, hA₁₂⟩ := s16p_basic hC
  have hfr : frontier A₁ = C := s16p_frontier_eq hC hinf
  obtain ⟨hFc, hFi, hFA, hFC, K, hK⟩ := hF
  have hA₁inf : extInf ∉ A₁ := fun h => disjoint_left.1 hA₁C h hinf
  set Ω : Set ℂ := ((↑) : ℂ → ExtPlane) ⁻¹' A₁ with hΩdef
  have hΩA : toExt Ω = A₁ := uq_j_toExt_preimage_coe hA₁inf
  have hΩo : IsOpen Ω := hA₁o.preimage OnePoint.continuous_coe
  have hΩc : IsConnected Ω := by
    have h := hA₁c
    rw [← hΩA] at h
    exact ⟨h.nonempty.of_image, OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image.1 h.isPreconnected⟩
  have hΩJ : IsJordanDomain Ω := ⟨hΩo, hΩc, by rw [hΩA, hfr]; exact hC.1⟩
  obtain ⟨φ, hφ, Φ, hΦ, hΦinf⟩ := s16p_uniformizer_inf hΩJ (by rw [hΩA, hfr]; exact hinf)
  have hclA : closure (toExt Ω) = A₁ ∪ C := by
    rw [hΩA, ← hfr, closure_eq_self_union_frontier]
  obtain ⟨hΦic, hΦim, hΦr, hΦl⟩ := wd_b_inv isClosed_closure hΦ.2.1 hΦ.2.2.1 hΦ.2.2.2
  have hΦiU : ∀ v ∈ upperHalf, Function.invFunOn Φ (closure (toExt Ω)) (v : ExtPlane) =
      ((Function.invFunOn φ Ω v : ℂ) : ExtPlane) ∧ Function.invFunOn φ Ω v ∈ Ω :=
    fun v hv => wd_b_invFunOn_coe hΦ hφ.2.2 hv
  set Φi := Function.invFunOn Φ (closure (toExt Ω)) with hΦidef
  set φi := Function.invFunOn φ Ω with hφidef
  -- boundary points of `ℍ` go to `C`
  have hbd : ∀ p ∈ closure (toExt upperHalf), p ∉ toExt upperHalf → Φi p ∈ C := by
    intro p hp hpU
    have h1 := hΦim hp
    rw [hclA] at h1
    rcases h1 with h1 | h1
    · exfalso
      rw [← hΩA] at h1
      obtain ⟨u, hu, hue⟩ := h1
      apply hpU
      rw [← hΦr p hp, ← hue, hΦ.1 u hu]
      exact ⟨φ u, hφ.mapsTo hu, rfl⟩
    · exact h1
  have hΦiinf : Φi extInf = extInf := by
    have h0 := hΦl extInf (by rw [hclA]; exact Or.inr hinf)
    rwa [hΦinf] at h0
  -- conjugation on `ℂ̄`
  set cj : ExtPlane ≃ₜ ExtPlane := (Complex.conjLIE.toHomeomorph).onePointCongr with hcj
  have hcjz : ∀ z : ℂ, cj (z : ExtPlane) = ((conj z : ℂ) : ExtPlane) := fun z => rfl
  have hcjinf : cj extInf = extInf := rfl
  have hconjU : ∀ z ∈ lowerHalf, conj z ∈ upperHalf := fun z hz => by
    show 0 < (conj z).im
    rw [conj_im]
    exact neg_pos.2 hz
  have hcjL : MapsTo cj (closure (toExt lowerHalf)) (closure (toExt upperHalf)) := by
    refine MapsTo.closure ?_ cj.continuous
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨conj z, hconjU z hz, (hcjz z).symm⟩
  have hnotU : ∀ x : ℝ, (((x : ℝ) : ℂ) : ExtPlane) ∉ toExt upperHalf := by
    rintro x ⟨w, hw, hwe⟩
    have hw' : 0 < w.im := hw
    rw [OnePoint.coe_injective hwe, ofReal_im] at hw'
    exact lt_irrefl 0 hw'
  -- the glued map
  obtain ⟨E, hE⟩ : ∃ E : ExtPlane → ExtPlane,
      ∀ p, E p = if p ∈ closure (toExt upperHalf) then Φi p else F (Φi (cj p)) := ⟨_, fun p => rfl⟩
  have hEU : EqOn E Φi (closure (toExt upperHalf)) := fun p hp => by rw [hE, ite_eq_left hp]
  have hEL : EqOn E (F ∘ Φi ∘ cj) (closure (toExt lowerHalf)) := fun p hp => by
    by_cases hpU : p ∈ closure (toExt upperHalf)
    · rw [hE, ite_eq_left hpU]
      rcases wd_b_closure_inter hpU hp with rfl | ⟨y, rfl⟩
      · show Φi extInf = F (Φi (cj extInf))
        rw [hcjinf, hΦiinf, hFC _ hinf]
      · show Φi _ = F (Φi (cj _))
        rw [hcjz, conj_ofReal]
        exact (hFC _ (hbd _ hpU (hnotU y))).symm
    · rw [hE, ite_eq_right hpU]
      rfl
  have hLmaps : MapsTo (Φi ∘ cj) (closure (toExt lowerHalf)) (A₁ ∪ C) := fun p hp => by
    have h1 := hΦim (hcjL hp)
    rwa [hclA] at h1
  have hEc : Continuous E :=
    wd_b_paste hΦic (hFc.comp (hΦic.comp cj.continuous.continuousOn hcjL) hLmaps) hEU hEL
  have hA₂' : ∀ z ∈ lowerHalf, E z ∈ A₂ := by
    intro z hz
    have hzU : (z : ExtPlane) ∉ closure (toExt upperHalf) := fun h' =>
      disjoint_left.1 wd_b_closure_upper_disjoint h' ⟨z, hz, rfl⟩
    rw [hE, ite_eq_right hzU, hcjz, (hΦiU _ (hconjU z hz)).1, ← hFA]
    exact mem_image_of_mem F (by rw [← hΩA]; exact ⟨_, (hΦiU _ (hconjU z hz)).2, rfl⟩)
  have hEinj : Function.Injective E := by
    have hsep : ∀ p q, p ∈ closure (toExt upperHalf) → q ∉ closure (toExt upperHalf) → E p ≠ E q := by
      intro p q hp hq hpq
      obtain ⟨z, hz, rfl⟩ := wd_b_not_mem_closure_upper hq
      have h1 : E p ∈ A₁ ∪ C := by
        rw [hEU hp, ← hclA]
        exact hΦim hp
      rw [hpq] at h1
      rcases h1 with h1 | h1
      · exact disjoint_left.1 hA₁₂ h1 (hA₂' z hz)
      · exact disjoint_left.1 hA₂C (hA₂' z hz) h1
    intro p q hpq
    by_cases hp : p ∈ closure (toExt upperHalf) <;> by_cases hq : q ∈ closure (toExt upperHalf)
    · rw [hEU hp, hEU hq] at hpq
      rw [← hΦr p hp, ← hΦr q hq, hpq]
    · exact (hsep p q hp hq hpq).elim
    · exact (hsep q p hq hp hpq.symm).elim
    · obtain ⟨z, hz, rfl⟩ := wd_b_not_mem_closure_upper hp
      obtain ⟨w, hw, rfl⟩ := wd_b_not_mem_closure_upper hq
      have hzL : ((z : ℂ) : ExtPlane) ∈ closure (toExt lowerHalf) := subset_closure ⟨z, hz, rfl⟩
      have hwL : ((w : ℂ) : ExtPlane) ∈ closure (toExt lowerHalf) := subset_closure ⟨w, hw, rfl⟩
      rw [hEL hzL, hEL hwL] at hpq
      have h1 := hFi (hLmaps hzL) (hLmaps hwL) hpq
      have h2 : cj (z : ExtPlane) = cj (w : ExtPlane) := by
        rw [← hΦr _ (hcjL hzL), ← hΦr _ (hcjL hwL)]
        exact congrArg Φ h1
      exact cj.injective h2
  have hEinf : E extInf = extInf := by
    rw [hEU wd_b_infty_mem_closure_upper, hΦiinf]
  -- the plane map
  obtain ⟨hHcoe, hHhom⟩ := wd_b_plane_homeo hEc hEinj hEinf
  set H : ℂ → ℂ := fun z => extToC (E z) with hHdef
  have hφiU : IsKQC φi upperHalf 1 := isKQC_one_of_conformal isOpen_upperHalf (hφ.symm hΩo)
  have hHU : IsKQC H upperHalf 1 := by
    refine ad_isKQC_congr hφiU fun z hz => OnePoint.coe_injective ?_
    show ((extToC (E z) : ℂ) : ExtPlane) = ((φi z : ℂ) : ExtPlane)
    rw [hHcoe z, hEU (subset_closure ⟨z, hz, rfl⟩)]
    exact (hΦiU z hz).1
  -- `conj ∘ F` is `K`-q.c. on `Ω`
  have hdom : {z : ℂ | (z : ExtPlane) ∈ A₁ ∧ F z ≠ extInf} = Ω := by
    ext z
    refine ⟨fun h => h.1, fun h => ⟨h, fun h' => ?_⟩⟩
    have h2 : F z ∈ A₂ := hFA ▸ mem_image_of_mem F h
    rw [h'] at h2
    exact disjoint_left.1 hA₂C h2 hinf
  rw [hdom] at hK
  have hGφ := thm7_1_comp hφiU hK (by rw [(hφ.symm hΩo).2.2])
  have hconj := abR_x_isKQC_conj hGφ
  have hpre : (starRingEnd ℂ) ⁻¹' upperHalf = lowerHalf := by
    ext z
    show 0 < (conj z).im ↔ z.im < 0
    rw [conj_im, neg_pos]
  rw [hpre] at hconj
  have hHL : IsKQC H lowerHalf (1 * K) := by
    refine ad_isKQC_congr hconj fun z hz => ?_
    have hzU : (z : ExtPlane) ∉ closure (toExt upperHalf) := fun h' =>
      disjoint_left.1 wd_b_closure_upper_disjoint h' ⟨z, hz, rfl⟩
    simp only [Function.comp_apply, conj_conj]
    show extToC (E z) = extToC (F (φi (conj z)))
    rw [hE, ite_eq_right hzU, hcjz, (hΦiU _ (hconjU z hz)).1]
  have hK1 : 1 ≤ 1 * K := hGφ.2.1
  have hH' : IsHomeomorphOnto H univ (H '' univ) := by
    rw [hHhom.2.2.1]
    exact hHhom
  have hHK : IsKQC H univ (1 * K) := wd_glue hK1 hH' (hHU.mono hK1) hHL
  -- `C = H(ℝ) ∪ {∞}`
  have hreal : ∀ x : ℝ, ((H x : ℂ) : ExtPlane) = Φi (((x : ℝ) : ℂ) : ExtPlane) := fun x => by
    rw [hHcoe, hEU (wd_b_real_mem_closure_upper x)]
  have hCH : C = toExt (H '' realLine) ∪ {extInf} := by
    apply Subset.antisymm
    · intro p hp
      induction p using OnePoint.rec with
      | infty => exact Or.inr rfl
      | coe z =>
        left
        have hzcl : (z : ExtPlane) ∈ closure (toExt Ω) := by
          rw [hclA]
          exact Or.inr hp
        have hΦz : Φ z ∈ closure (toExt upperHalf) := hΦ.2.2.2 ▸ mem_image_of_mem Φ hzcl
        rcases wd_b_closure_upper_cases hΦz with h0 | ⟨x, hx⟩ | ⟨w, hw, hwe⟩
        · exfalso
          have h1 := hΦ.2.2.1 hzcl (by rw [hclA]; exact Or.inr hinf) (h0.trans hΦinf.symm)
          exact OnePoint.coe_ne_infty z h1
        · refine ⟨H x, ⟨(x : ℂ), ofReal_im x, rfl⟩, ?_⟩
          rw [hreal, ← hx, hΦl _ hzcl]
        · exfalso
          have h1 := hΦl _ hzcl
          rw [hwe, (hΦiU w hw).1] at h1
          have h2 : (z : ExtPlane) ∈ A₁ := by
            rw [← h1, ← hΩA]
            exact ⟨_, (hΦiU w hw).2, rfl⟩
          exact disjoint_left.1 hA₁C h2 hp
    · rintro p (⟨_, ⟨z, hz, rfl⟩, rfl⟩ | hp)
      · have hz' : ((z.re : ℝ) : ℂ) = z :=
          Complex.ext (by simp) (by simp [show z.im = 0 from hz])
        rw [← hz', hreal]
        exact hbd _ (wd_b_real_mem_closure_upper _) (hnotU _)
      · rw [mem_singleton_iff] at hp
        rw [hp]
        exact hinf
  rw [hCH]
  exact ⟨1 * K, isKQuasicircle_image_realLine hHK hHhom.2.2.1⟩

/-- The anti-q.c. core of the reflection in `g₀(ℝ) ∪ {∞}`: `z ↦ conj (g₀ (conj (g₀⁻¹ z)))` is `K²`-q.c. on the
plane. -/
theorem s16p_refl_core {g₀ : ℂ → ℂ} {K : ℝ} (hg : IsKQC g₀ univ K) (e : ℂ ≃ₜ ℂ) (he : ⇑e = g₀) :
    IsKQC (fun z => conj (g₀ (conj (e.symm z)))) univ (K * K) := by
  have hs : g₀ '' univ = univ := by
    rw [← he, image_univ_of_surjective e.surjective]
  have h1 := thm7_2_inv hg
  rw [hs] at h1
  have heq : EqOn (⇑e.symm) (Function.invFunOn g₀ univ) univ := by
    intro z _
    have hex : ∃ a ∈ (univ : Set ℂ), g₀ a = z := ⟨e.symm z, mem_univ _, by rw [← he]; simp⟩
    have h := Function.invFunOn_eq hex
    apply e.injective
    rw [e.apply_symm_apply, he, h]
  have h1' : IsKQC (⇑e.symm) univ K := ad_isKQC_congr h1 heq
  have h2 := abR_x_isKQC_conj hg
  rw [preimage_univ] at h2
  have h3 := thm7_1_comp h1' h2 (subset_univ _)
  exact h3

/-- **(⇒) of Theorem 16.2 for a quasicircle through `∞`**: with `C = g₀(ℝ) ∪ {∞}`, `A₁ = g₀(ℍ)`, `A₂ = g₀(𝕃)`
(`wd_normal_form`), the reflection is `ĝ₀ ∘ conj ∘ ĝ₀⁻¹`. -/
theorem s16p_fwd_inf {C : Set ExtPlane} {A₁ A₂ : Set ℂ} (hinf : extInf ∈ C)
    (hC : AreComplementaryComponents C (toExt A₁) (toExt A₂)) (hq : IsQuasicircle C) :
    ∃ F : ExtPlane → ExtPlane, IsQCReflection C (toExt A₁) (toExt A₂) F := by
  obtain ⟨g₀, K, hg₀, hg₀s, hCeq, hA₁, hA₂⟩ := wd_normal_form hinf hC hq
  obtain ⟨e, he⟩ := t1_homeomorph hg₀ hg₀s
  set R : ℂ ≃ₜ ℂ := (e.symm.trans Complex.conjLIE.toHomeomorph).trans e with hRdef
  have hR : ∀ z, R z = e (conj (e.symm z)) := fun z => by simp [R]
  have hRe : ∀ z, R (e z) = e (conj z) := fun z => by rw [hR, e.symm_apply_apply]
  have hA₁o : IsOpen A₁ := by
    rw [hA₁, ← he]
    exact e.isOpenMap _ isOpen_upperHalf
  refine ⟨R.onePointCongr, R.onePointCongr.continuous.continuousOn,
    R.onePointCongr.injective.injOn, ?_, ?_, K * K, ?_⟩
  · rw [s13x_de_image_toExt]
    congr 1
    rw [hA₁, hA₂, ← he]
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨conj z, ?_, (hRe z).symm⟩
      show (conj z).im < 0
      have hz' : 0 < z.im := hz
      rw [conj_im]
      linarith
    · rintro ⟨z, hz, rfl⟩
      refine ⟨e (conj z), ⟨conj z, ?_, rfl⟩, ?_⟩
      · show 0 < (conj z).im
        have hz' : z.im < 0 := hz
        rw [conj_im]
        linarith
      · rw [hRe, conj_conj]
  · intro p hp
    rw [hCeq] at hp
    rcases hp with ⟨_, ⟨x, hx, rfl⟩, rfl⟩ | hp
    · have hx' : x.im = 0 := hx
      have hcx : conj x = x := Complex.conj_eq_iff_im.2 hx'
      show OnePoint.map R ((g₀ x : ℂ) : ExtPlane) = ((g₀ x : ℂ) : ExtPlane)
      rw [OnePoint.map_some, ← he, hRe, hcx]
    · rw [mem_singleton_iff] at hp
      subst hp
      rfl
  · have hdom : {z : ℂ | (z : ExtPlane) ∈ toExt A₁ ∧ R.onePointCongr (z : ExtPlane) ≠ extInf} = A₁ := by
      ext z
      simp only [mem_ofPred_eq, coe_mem_toExt_iff]
      constructor
      · exact fun h => h.1
      · intro h
        exact ⟨h, by simp⟩
    rw [hdom]
    have hcore := nx_isKQC_restrict (s16p_refl_core hg₀ e he) hA₁o (subset_univ _)
    refine ad_isKQC_congr hcore fun z _ => ?_
    show conj (extToC (OnePoint.map R (z : ExtPlane))) = conj (g₀ (conj (e.symm z)))
    rw [OnePoint.map_some, hR, he]
    rfl

/-- **Theorem 16.2 for a Jordan curve through `∞`.** -/
theorem s16p_main_inf {C A₁ A₂ : Set ExtPlane} (hC : AreComplementaryComponents C A₁ A₂) (hinf : extInf ∈ C) :
    IsQuasicircle C ↔ ∃ F : ExtPlane → ExtPlane, IsQCReflection C A₁ A₂ F := by
  refine ⟨fun hq => ?_, fun ⟨F, hF⟩ => s16p_bwd_inf hC hinf hF⟩
  obtain ⟨-, -, -, -, hA₁C, hA₂C, -⟩ := s16p_basic hC
  have h₁ : toExt (((↑) : ℂ → ExtPlane) ⁻¹' A₁) = A₁ :=
    uq_j_toExt_preimage_coe fun h => disjoint_left.1 hA₁C h hinf
  have h₂ : toExt (((↑) : ℂ → ExtPlane) ⁻¹' A₂) = A₂ :=
    uq_j_toExt_preimage_coe fun h => disjoint_left.1 hA₂C h hinf
  have h := s16p_fwd_inf (A₁ := ((↑) : ℂ → ExtPlane) ⁻¹' A₁) (A₂ := ((↑) : ℂ → ExtPlane) ⁻¹' A₂) hinf
    (by rw [h₁, h₂]; exact hC) hq
  rwa [h₁, h₂] at h

/-- **Möbius transport of a q.c. reflection.**  Let `e` be the fractional linear map `z ↦ α + β/(z - q)` of `ℂ̄`
(`β ≠ 0`).  A q.c. reflection `F` in `C` gives the q.c. reflection `e ∘ F ∘ e⁻¹` in `e(C)`: off the (at most two)
points where `e⁻¹` or `F ∘ e⁻¹` takes the value `∞`, `conj ∘ (e ∘ F ∘ e⁻¹)` is the composition of
`w ↦ q + β/(w - α)`, `conj ∘ F` and `u ↦ ᾱ + β̄/(u - q̄)`, and finitely many points are removable. -/
theorem s16p_refl_transport {C A₁ A₂ : Set ExtPlane} (hC : AreComplementaryComponents C A₁ A₂)
    {F : ExtPlane → ExtPlane} (hF : IsQCReflection C A₁ A₂ F) (e : ExtPlane ≃ₜ ExtPlane) {α β q : ℂ}
    (hβ : β ≠ 0) (heq : e (q : ExtPlane) = extInf)
    (hez : ∀ z : ℂ, z ≠ q → e z = ((α + β * (z - q)⁻¹ : ℂ) : ExtPlane)) :
    IsQCReflection (e '' C) (e '' A₁) (e '' A₂) (e ∘ F ∘ e.symm) := by
  classical
  obtain ⟨-, hA₁o, -, -, -, -, -⟩ := s16p_basic hC
  obtain ⟨hFc, hFi, hFA, hFC, K, hK⟩ := hF
  have hsw : ∀ w : ℂ, w ≠ α → e.symm (w : ExtPlane) = ((q + β * (w - α)⁻¹ : ℂ) : ExtPlane) := by
    intro w hw
    have hwα : w - α ≠ 0 := sub_ne_zero.2 hw
    have hne : q + β * (w - α)⁻¹ ≠ q := by
      intro h
      have h0 : β * (w - α)⁻¹ = 0 := by linear_combination h
      exact mul_ne_zero hβ (inv_ne_zero hwα) h0
    rw [e.symm_apply_eq, hez _ hne]
    congr 1
    rw [add_sub_cancel_left, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ hβ, one_mul, add_sub_cancel]
  have hss : ∀ s : Set ExtPlane, e.symm '' (e '' s) = s := fun s => by
    rw [image_image]
    simp
  have hmaps : MapsTo e.symm (e '' A₁ ∪ e '' C) (A₁ ∪ C) := by
    rw [← image_union]
    rintro _ ⟨p, hp, rfl⟩
    rwa [e.symm_apply_apply]
  have hF'c : ContinuousOn (e ∘ F ∘ e.symm) (e '' A₁ ∪ e '' C) :=
    e.continuous.comp_continuousOn (hFc.comp e.symm.continuous.continuousOn hmaps)
  have hF'i : InjOn (e ∘ F ∘ e.symm) (e '' A₁ ∪ e '' C) :=
    e.injective.comp_injOn (hFi.comp e.symm.injective.injOn hmaps)
  refine ⟨hF'c, hF'i, ?_, ?_, 1 * K * 1, ?_⟩
  · rw [image_comp, image_comp, hss, hFA]
  · rintro _ ⟨c, hc, rfl⟩
    show e (F (e.symm (e c))) = e c
    rw [e.symm_apply_apply, hFC c hc]
  -- the q.c. part
  set F' := e ∘ F ∘ e.symm with hF'def
  set D' : Set ℂ := {w : ℂ | (w : ExtPlane) ∈ e '' A₁ ∧ F' w ≠ extInf} with hD'def
  set L : Set ℂ := {α} ∪ {w : ℂ | (w : ExtPlane) ∈ e '' A₁ ∧ F (e.symm w) = extInf} with hLdef
  have hD'o : IsOpen D' :=
    ((hF'c.mono subset_union_left).isOpen_inter_preimage (e.isOpenMap _ hA₁o)
      (isOpen_compl_singleton (x := extInf))).preimage OnePoint.continuous_coe
  have hLf : L.Finite := by
    refine (finite_singleton α).union (Set.Subsingleton.finite ?_)
    rintro w₁ ⟨hw₁, hF₁⟩ w₂ ⟨hw₂, hF₂⟩
    exact OnePoint.coe_injective
      (e.symm.injective (hFi (hmaps (Or.inl hw₁)) (hmaps (Or.inl hw₂)) (hF₁.trans hF₂.symm)))
  have hfin : ∀ w ∈ D', ((extToC (F' w) : ℂ) : ExtPlane) = F' w := by
    intro w hw
    obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.1 hw.2
    rw [← hu]
    rfl
  have hgc : ContinuousOn (fun w : ℂ => conj (extToC (F' w))) D' := by
    intro w hw
    have h1 : ContinuousWithinAt (fun w : ℂ => F' w) D' w :=
      ((hF'c.mono subset_union_left) _ hw.1).comp OnePoint.continuous_coe.continuousWithinAt
        fun v hv => by exact hv.1
    have h2 : ContinuousAt extToC (F' w) := by
      rw [← hfin w hw]
      exact s16p_continuousAt_extToC _
    have h3 : ContinuousWithinAt (fun v : ℂ => extToC (F' v)) D' w :=
      ContinuousAt.comp_continuousWithinAt (f := fun v : ℂ => F' v) h2 h1
    exact Complex.continuous_conj.continuousAt.comp_continuousWithinAt h3
  have hgi : InjOn (fun w : ℂ => conj (extToC (F' w))) D' := by
    intro w₁ hw₁ w₂ hw₂ h
    have h1 : extToC (F' w₁) = extToC (F' w₂) := by
      have h' := congrArg conj h
      simpa using h'
    have h2 : F' w₁ = F' w₂ := by rw [← hfin w₁ hw₁, ← hfin w₂ hw₂, h1]
    exact OnePoint.coe_injective (hF'i (Or.inl hw₁.1) (Or.inl hw₂.1) h2)
  have hK1 : 1 ≤ 1 * K * 1 := by
    rw [one_mul, mul_one]
    exact hK.2.1
  refine s16p_isKQC_of_finite hD'o hK1 hgc hgi hLf ?_
  have hDL : IsOpen (D' \ L) := hD'o.sdiff hLf.isClosed
  have hmem : ∀ w ∈ D' \ L, w ≠ α ∧ e.symm (w : ExtPlane) = ((q + β * (w - α)⁻¹ : ℂ) : ExtPlane) ∧
      ((q + β * (w - α)⁻¹ : ℂ) : ExtPlane) ∈ A₁ ∧ F ((q + β * (w - α)⁻¹ : ℂ) : ExtPlane) ≠ extInf := by
    rintro w ⟨hwD, hwL⟩
    have hwα : w ≠ α := fun h => hwL (Or.inl h)
    have hs := hsw w hwα
    refine ⟨hwα, hs, ?_, ?_⟩
    · obtain ⟨p, hp, hpw⟩ := hwD.1
      rw [← hs, ← hpw, e.symm_apply_apply]
      exact hp
    · intro h
      exact hwL (Or.inr ⟨hwD.1, by rw [hs]; exact h⟩)
  have k1 : IsKQC (fun w : ℂ => q + β * (w - α)⁻¹) (D' \ L) 1 :=
    ac_t_isKQC_restrict (tp_b1_M_isKQC α q hβ) hDL fun w hw => (hmem w hw).1
  have k2 := thm7_1_comp k1 hK (by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨(hmem w hw).2.2.1, (hmem w hw).2.2.2⟩)
  have hβ' : conj β ≠ 0 := (map_ne_zero _).2 hβ
  have k3 := thm7_1_comp k2 (tp_b1_M_isKQC (conj q) (conj α) hβ') (by
    rintro _ ⟨w, hw, rfl⟩ h
    obtain ⟨-, hs, -, hFne⟩ := hmem w hw
    obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.1 hFne
    have h1 : conj (extToC (F ((q + β * (w - α)⁻¹ : ℂ) : ExtPlane))) = conj q := h
    rw [← hu] at h1
    have h2 : extToC (u : ExtPlane) = q := by simpa using congrArg conj h1
    have huq : u = q := h2
    apply hw.1.2
    show e (F (e.symm w)) = extInf
    rw [hs, ← hu, huq, heq])
  refine ad_isKQC_congr k3 fun w hw => ?_
  obtain ⟨-, hs, -, hFne⟩ := hmem w hw
  obtain ⟨u, hu⟩ := OnePoint.ne_infty_iff_exists.1 hFne
  have huq : u ≠ q := by
    rintro rfl
    apply hw.1.2
    show e (F (e.symm w)) = extInf
    rw [hs, ← hu, heq]
  show conj (extToC (e (F (e.symm w)))) =
    conj α + conj β * (conj (extToC (F ((q + β * (w - α)⁻¹ : ℂ) : ExtPlane))) - conj q)⁻¹
  rw [hs, ← hu, hez u huq]
  show conj (α + β * (u - q)⁻¹) = conj α + conj β * (conj u - conj q)⁻¹
  simp only [map_add, map_mul, map_inv₀, map_sub]

/-- **Theorem 16.2**, proved: for a curve through `∞` directly (`s16p_main_inf`); otherwise move a point `a ∈ C` to
`∞` by `e(z) = 1/(z - a)`, which carries quasicircles, complementary components and q.c. reflections both ways
(`s16p_isQuasicircle_mobius_image`, `s16p_areComplementaryComponents_image`, `s16p_refl_transport` for `e` and for
`e⁻¹(w) = a + 1/w`). -/
theorem s16p_thm16_2 {C A₁ A₂ : Set ExtPlane} (hC : AreComplementaryComponents C A₁ A₂) :
    IsQuasicircle C ↔ ∃ F : ExtPlane → ExtPlane, IsQCReflection C A₁ A₂ F := by
  by_cases hinf : extInf ∈ C
  · exact s16p_main_inf hC hinf
  obtain ⟨p, hp⟩ : C.Nonempty := by
    obtain ⟨γ, -, -, hγ⟩ := hC.1
    rw [← hγ]
    exact range_nonempty γ
  obtain ⟨a, rfl⟩ : ∃ a : ℂ, p = a :=
    (uq_j_eq_infty_or_coe p).resolve_left (by rintro rfl; exact hinf hp)
  set e := mobiusHomeomorph 0 1 1 (-a) (uq_j_inv_det a) with he
  have hC' := s16p_areComplementaryComponents_image hC e
  have hea : e (a : ExtPlane) = extInf := uq_j_mobiusInv_apply_self a
  have hmain := s16p_main_inf hC' ⟨a, hp, hea⟩
  have heinf : e extInf = ((0 : ℂ) : ExtPlane) := by
    rw [he, mobiusHomeomorph_apply, mobiusExt_infty_of_ne one_ne_zero, zero_div]
  have hez : ∀ z : ℂ, z ≠ a → e z = ((0 + 1 * (z - a)⁻¹ : ℂ) : ExtPlane) := by
    intro z hz
    rw [uq_j_mobiusInv_coe hz]
    congr 1
    simp [mobiusFn, sub_eq_add_neg]
  have hs0 : e.symm ((0 : ℂ) : ExtPlane) = extInf := by
    rw [e.symm_apply_eq, heinf]
  have hsz : ∀ z : ℂ, z ≠ 0 → e.symm z = ((a + 1 * (z - 0)⁻¹ : ℂ) : ExtPlane) := by
    intro z hz
    have hne : a + 1 * (z - 0)⁻¹ ≠ a := by
      intro h
      have h0 : 1 * (z - 0)⁻¹ = 0 := by linear_combination h
      rw [sub_zero, one_mul] at h0
      exact inv_ne_zero hz h0
    rw [e.symm_apply_eq, hez _ hne]
    congr 1
    simp
  have hss : ∀ s : Set ExtPlane, e.symm '' (e '' s) = s := fun s => by
    rw [image_image]
    simp
  constructor
  · intro hq
    obtain ⟨F', hF'⟩ := hmain.1 (s16p_isQuasicircle_mobius_image hq (uq_j_inv_det a))
    have h := s16p_refl_transport hC' hF' e.symm one_ne_zero hs0 hsz
    rw [hss C, hss A₁, hss A₂] at h
    exact ⟨_, h⟩
  · rintro ⟨F, hF⟩
    have hq' := hmain.2 ⟨_, s16p_refl_transport hC hF e one_ne_zero hea hez⟩
    have h := s16p_isQuasicircle_mobius_image hq' (a := -a) (b := -1) (c := -1) (d := 0) (by norm_num)
    have heq : mobiusExt (-a) (-1) (-1) 0 '' (e '' C) = C := hss C
    rwa [heq] at h

/-- **Theorem 16.2**: a Jordan curve `C` is a quasicircle iff there is a quasiconformal reflection
in `C`. -/
theorem thm16_2 {C A₁ A₂ : Set ExtPlane} (hC : AreComplementaryComponents C A₁ A₂) :
    IsQuasicircle C ↔ ∃ F : ExtPlane → ExtPlane, IsQCReflection C A₁ A₂ F := by
  exact s16p_thm16_2 hC

/-! ### Welding track interface (coordinator 553e2d): Theorem 16.3 -/

/-- There is no continuous injective map of the circle into `ℝ`: for `F = f ∘ Circle.exp` the midpoint value
`(F 0 + F π) / 2` is taken on `[0, π]` and on `[π, 2π]` (intermediate value theorem, `F (2π) = F 0`), at points
which `Circle.exp` identifies although it is injective on `[0, 2π)`. -/
theorem wd_j_not_injective_circle_real {f : Circle → ℝ} (hf : Continuous f) : ¬ Function.Injective f := by
  intro hinj
  set F : ℝ → ℝ := fun t => f (Circle.exp t) with hF
  have hFc : Continuous F := hf.comp Circle.exp.continuous
  have hpi := Real.pi_pos
  have hinjOn : InjOn Circle.exp (Ico 0 (2 * π)) := Circle.exp_injOn_Ico (by linarith)
  have h0pi : F 0 ≠ F π := fun h =>
    hpi.ne (hinjOn ⟨le_refl 0, by linarith⟩ ⟨hpi.le, by linarith⟩ (hinj h))
  have h2pi : F (2 * π) = F 0 := by
    rw [hF]
    simp only [Circle.exp_two_pi, Circle.exp_zero]
  set v := (F 0 + F π) / 2 with hv
  have hv0 : v ≠ F 0 := fun h => h0pi (by linarith)
  have hvpi : v ≠ F π := fun h => h0pi (by linarith)
  have hv1 : v ∈ uIcc (F 0) (F π) := by
    rw [mem_uIcc]
    rcases le_total (F 0) (F π) with h | h
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  have hv2 : v ∈ uIcc (F π) (F (2 * π)) := by
    rw [h2pi, uIcc_comm]
    exact hv1
  obtain ⟨s, hs, hFs⟩ := intermediate_value_uIcc hFc.continuousOn hv1
  obtain ⟨t, ht, hFt⟩ := intermediate_value_uIcc hFc.continuousOn hv2
  rw [uIcc_of_le hpi.le] at hs
  rw [uIcc_of_le (by linarith)] at ht
  have ht2 : t ≠ 2 * π := by
    rintro rfl
    exact hv0 (hFt.symm.trans h2pi)
  have hst : s = t := hinjOn ⟨hs.1, by linarith [hs.2]⟩ ⟨by linarith [ht.1], lt_of_le_of_ne ht.2 ht2⟩
    (hinj (hFs.trans hFt.symm))
  have hsπ : s = π := by linarith [hs.2, ht.1]
  exact hvpi (hsπ ▸ hFs.symm)

/-- A continuous injective self-map `σ` of the circle is surjective: if it missed `θ₀`, then `u ↦ arg (-(σ u / θ₀))`
would be a continuous (`arg` is continuous off the slit, which `-(w / θ₀)` meets only for `w = θ₀`) injective map of
the circle into `ℝ`. -/
theorem wd_j_surjective_of_injective {σ : Circle → Circle} (hσc : Continuous σ) (hσi : Function.Injective σ) :
    Function.Surjective σ := by
  intro θ₀
  by_contra hθ
  push Not at hθ
  have hslit : ∀ w : Circle, w ≠ θ₀ → ((-(w / θ₀) : Circle) : ℂ) ∈ slitPlane := by
    intro w hw
    rw [mem_slitPlane_iff_arg]
    refine ⟨fun h => hw ?_, Circle.coe_ne_zero _⟩
    have h1 : -(w / θ₀) = (-1 : Circle) := Circle.injective_arg (by
      show arg _ = arg _
      rw [h, Circle.coe_neg, Circle.coe_one, Complex.arg_neg_one])
    rwa [neg_inj, div_eq_one] at h1
  refine wd_j_not_injective_circle_real (f := fun u => arg ((-(σ u / θ₀) : Circle) : ℂ)) ?_ ?_
  · have hc : Continuous fun u => ((-(σ u / θ₀) : Circle) : ℂ) :=
      continuous_subtype_val.comp ((hσc.div' continuous_const).neg)
    refine continuous_iff_continuousAt.2 fun u => ?_
    exact ContinuousAt.comp (f := fun u => ((-(σ u / θ₀) : Circle) : ℂ))
      (Complex.continuousAt_arg (hslit _ (hθ u))) hc.continuousAt
  · intro u v huv
    apply hσi
    have h1 := Circle.injective_arg huv
    rwa [neg_inj, div_left_inj] at h1

/-- In a Hausdorff space, of two continuous injective images of the circle neither contains the other properly: a
continuous injection of the compact circle is an embedding, so the inclusion pulls back to a continuous injective
self-map of the circle, which is surjective (`wd_j_surjective_of_injective`). -/
theorem wd_j_range_eq {X : Type*} [TopologicalSpace X] [T2Space X] {γ₁ γ₂ : Circle → X}
    (h₁c : Continuous γ₁) (h₁i : Function.Injective γ₁) (h₂c : Continuous γ₂) (h₂i : Function.Injective γ₂)
    (hsub : range γ₁ ⊆ range γ₂) : range γ₁ = range γ₂ := by
  have hemb : IsEmbedding γ₂ := (h₂c.isClosedEmbedding h₂i).isEmbedding
  choose σ hσ using fun u => (hsub (mem_range_self u) : ∃ θ, γ₂ θ = γ₁ u)
  have hσc : Continuous σ := by
    rw [hemb.continuous_iff]
    have h1 : γ₂ ∘ σ = γ₁ := funext hσ
    rw [h1]
    exact h₁c
  have hσi : Function.Injective σ := fun u v h => h₁i (by rw [← hσ u, ← hσ v, h])
  refine subset_antisymm hsub ?_
  rintro _ ⟨θ, rfl⟩
  obtain ⟨u, rfl⟩ := wd_j_surjective_of_injective hσc hσi θ
  exact ⟨u, (hσ u).symm⟩

/-- **J** (a Jordan curve contains no other Jordan curve): if `J₁ ⊆ J₂` are Jordan curves of `ℂ̄` then `J₁ = J₂`
(otherwise `J₁` embeds in `J₂ ∖ {p} ≅ ℝ`, but a circle does not embed in `ℝ`). -/
theorem wd_jordan_subcurve {J₁ J₂ : Set ExtPlane} (h₁ : IsJordanCurve J₁) (h₂ : IsJordanCurve J₂)
    (hsub : J₁ ⊆ J₂) : J₁ = J₂ := by
  obtain ⟨γ₁, hγ₁c, hγ₁i, rfl⟩ := h₁
  obtain ⟨γ₂, hγ₂c, hγ₂i, rfl⟩ := h₂
  exact wd_j_range_eq hγ₁c hγ₁i hγ₂c hγ₂i hsub

/-- The frontier of a component of the complement of a closed set `K ⊆ ℂ̄` lies in `K` (the components of the open
set `ℂ̄ ∖ K` are open, `ℂ̄` being locally connected); the `ℂ̄` analogue of `iod_frontier_connectedComponentIn_subset`. -/
theorem wd_f_frontier_component_subset {K : Set ExtPlane} (hK : IsClosed K) (a : ExtPlane) :
    frontier (connectedComponentIn Kᶜ a) ⊆ K := by
  have hKo : IsOpen Kᶜ := hK.isOpen_compl
  intro z hz
  by_contra hzK
  have hzV : z ∈ connectedComponentIn Kᶜ z := mem_connectedComponentIn hzK
  rw [hKo.connectedComponentIn.frontier_eq] at hz
  obtain ⟨y, hyV, hyW⟩ := mem_closure_iff_nhds.mp hz.1 _ (hKo.connectedComponentIn.mem_nhds hzV)
  rw [connectedComponentIn_eq hyV, ← connectedComponentIn_eq hyW] at hzV
  exact hz.2 hzV

/-- The image of a Jordan curve `J` under a map which is continuous and injective on a set containing `J` is a
Jordan curve. -/
theorem wd_f_isJordanCurve_image {G : ExtPlane → ExtPlane} {S J : Set ExtPlane} (hG : ContinuousOn G S)
    (hGi : InjOn G S) (hJ : IsJordanCurve J) (hJS : J ⊆ S) : IsJordanCurve (G '' J) := by
  obtain ⟨γ, hγc, hγi, hγr⟩ := hJ
  have hmaps : ∀ t, γ t ∈ S := fun t => hJS (hγr ▸ mem_range_self t)
  refine ⟨G ∘ γ, hG.comp_continuous hγc hmaps, fun s t hst => hγi (hGi (hmaps s) (hmaps t) hst), ?_⟩
  rw [range_comp, hγr]

/-- `∂𝕃` is a Jordan curve of `ℂ̄`: it is the image of `∂ℍ` under the homeomorphism of `ℂ̄` induced by `z ↦ -z`. -/
theorem wd_f_isJordanCurve_frontier_lowerHalf : IsJordanCurve (frontier (toExt lowerHalf)) := by
  have himg : (Homeomorph.neg ℂ) '' upperHalf = lowerHalf := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : 0 < w.im := hw
      show (-w).im < 0
      rw [neg_im]
      linarith
    · intro hz
      have hz' : z.im < 0 := hz
      refine ⟨-z, ?_, neg_neg z⟩
      show 0 < (-z).im
      rw [neg_im]
      linarith
  have h := uq_isJordanCurve_image (Homeomorph.neg ℂ).onePointCongr isJordanCurve_frontier_upperHalf
  rwa [(Homeomorph.neg ℂ).onePointCongr.image_frontier, s13x_de_image_toExt, himg] at h

/-- **F** (the boundary of a complementary component): a component `A` of `ℂ̄ ∖ C` (`C` a Jordan curve) mapped
conformally onto a half-plane `V`, with a homeomorphic extension `Φ` to the closures, has `∂A = C`: `∂A ⊆ C` since
components of the open set `ℂ̄ ∖ C` are open, `∂A = Φ⁻¹(∂V)` is a Jordan curve, and then J. -/
theorem wd_frontier_eq {C : Set ExtPlane} {A V : Set ℂ} {φ : ℂ → ℂ} {Φ : ExtPlane → ExtPlane}
    (hC : IsJordanCurve C) (hA : ∃ p ∈ Cᶜ, toExt A = connectedComponentIn Cᶜ p)
    (hV : V = upperHalf ∨ V = lowerHalf) (hφ : IsConformalOnto φ A V) (hΦ : IsHomeoExtension φ A V Φ) :
    frontier (toExt A) = C := by
  obtain ⟨p, -, hAp⟩ := hA
  have hCc : IsClosed C := by
    obtain ⟨γ, hγc, -, hγr⟩ := hC
    rw [← hγr]
    exact (isCompact_range hγc).isClosed
  have hAo : IsOpen A := by
    refine OnePoint.isOpen_image_coe.1 ?_
    change IsOpen (toExt A)
    rw [hAp]
    exact hCc.isOpen_compl.connectedComponentIn
  have hVo : IsOpen V := by
    rcases hV with rfl | rfl
    · exact isOpen_upperHalf
    · exact isOpen_lt continuous_im continuous_const
  have hVJ : IsJordanCurve (frontier (toExt V)) := by
    rcases hV with rfl | rfl
    · exact isJordanCurve_frontier_upperHalf
    · exact wd_f_isJordanCurve_frontier_lowerHalf
  have hinv := isHomeoExtension_invFunOn hφ hΦ
  have hfr := hinv.image_frontier hVo hAo (hφ.symm hAo).2.2
  have hJ : IsJordanCurve (frontier (toExt A)) := by
    rw [← hfr]
    exact wd_f_isJordanCurve_image hinv.2.1 hinv.2.2.1 hVJ frontier_subset_closure
  refine wd_jordan_subcurve hJ hC ?_
  rw [hAp]
  exact wd_f_frontier_component_subset hCc p

/-- **B** (the welded homeomorphism, (⇐) of Theorem 16.3): if `g` is a `K`-q.c. self-map of `ℍ` with boundary values
`h`, then `H := φ⁻¹ ∘ g⁻¹` on `ℍ̄`, `H := ψ⁻¹` on `𝕃̄` (they agree on `ℝ`: `Φ⁻¹(G⁻¹ y) = Ψ⁻¹ y` by `hh` and F) is a
homeomorphism of `ℂ` onto `ℂ`, `K`-q.c. on `ℍ`, conformal on `𝕃`, with `C = H(ℝ) ∪ {∞}`. -/
theorem wd_backward {C : Set ExtPlane} {A₁ A₂ : Set ℂ} (hinf : extInf ∈ C)
    (hC : AreComplementaryComponents C (toExt A₁) (toExt A₂)) {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    (hφ : IsConformalOnto φ A₁ upperHalf) (hψ : IsConformalOnto ψ A₂ lowerHalf)
    (hΦ : IsHomeoExtension φ A₁ upperHalf Φ) (hΨ : IsHomeoExtension ψ A₂ lowerHalf Ψ)
    (hΦinf : Φ extInf = extInf) (hΨinf : Ψ extInf = extInf) {h : ℝ → ℝ}
    (hh : ∀ z : ℂ, (z : ExtPlane) ∈ C →
      ∃ x : ℝ, Φ z = ((x : ℂ) : ExtPlane) ∧ Ψ z = (((h x : ℝ) : ℂ) : ExtPlane))
    {g : ℂ → ℂ} {G : ExtPlane → ExtPlane} {K : ℝ} (hg : IsKQC g upperHalf K) (hgs : g '' upperHalf = upperHalf)
    (hG : IsHomeoExtension g upperHalf upperHalf G)
    (hGh : ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = (((h x : ℝ) : ℂ) : ExtPlane)) :
    ∃ H : ℂ → ℂ, IsHomeomorphOnto H univ univ ∧ IsKQC H upperHalf K ∧ IsKQC H lowerHalf 1 ∧
      C = toExt (H '' realLine) ∪ {extInf} := by
  classical
  obtain ⟨hJ, p₁, hp₁, p₂, hp₂, hA₁eq, hA₂eq, hne⟩ := hC
  -- the two components are open and disjoint
  have hCo : IsOpen Cᶜ := by
    obtain ⟨γ, hγc, -, hγr⟩ := hJ
    rw [← hγr]
    exact (isCompact_range hγc).isClosed.isOpen_compl
  have hA₁o : IsOpen (toExt A₁) := by
    rw [hA₁eq]
    exact hCo.connectedComponentIn
  have hA₂o : IsOpen (toExt A₂) := by
    rw [hA₂eq]
    exact hCo.connectedComponentIn
  have hdisj : Disjoint (toExt A₁) (toExt A₂) := by
    rw [Set.disjoint_left]
    intro q hq₁ hq₂
    rw [hA₁eq] at hq₁
    rw [hA₂eq] at hq₂
    exact hne (by rw [hA₁eq, hA₂eq, connectedComponentIn_eq hq₁, connectedComponentIn_eq hq₂])
  -- `C` is the frontier of both components (F)
  have hfr₁ : frontier (toExt A₁) = C := wd_frontier_eq hJ ⟨p₁, hp₁, hA₁eq⟩ (Or.inl rfl) hφ hΦ
  have hfr₂ : frontier (toExt A₂) = C := wd_frontier_eq hJ ⟨p₂, hp₂, hA₂eq⟩ (Or.inr rfl) hψ hΨ
  have hCS₁ : C ⊆ closure (toExt A₁) := by
    rw [← hfr₁]
    exact frontier_subset_closure
  have hCS₂ : C ⊆ closure (toExt A₂) := by
    rw [← hfr₂]
    exact frontier_subset_closure
  -- the inverses of `Φ`, `Ψ`, `G` on the closures
  obtain ⟨hΦic, hΦim, hΦr, hΦl⟩ := wd_b_inv isClosed_closure hΦ.2.1 hΦ.2.2.1 hΦ.2.2.2
  obtain ⟨hΨic, hΨim, hΨr, hΨl⟩ := wd_b_inv isClosed_closure hΨ.2.1 hΨ.2.2.1 hΨ.2.2.2
  obtain ⟨hGic, hGim, hGr, hGl⟩ := wd_b_inv isClosed_closure hG.2.1 hG.2.2.1 hG.2.2.2
  have hGiU : ∀ z ∈ upperHalf, Function.invFunOn G (closure (toExt upperHalf)) (z : ExtPlane) =
      ((Function.invFunOn g upperHalf z : ℂ) : ExtPlane) ∧ Function.invFunOn g upperHalf z ∈ upperHalf :=
    fun z hz => wd_b_invFunOn_coe hG hgs hz
  have hΦiU : ∀ v ∈ upperHalf, Function.invFunOn Φ (closure (toExt A₁)) (v : ExtPlane) =
      ((Function.invFunOn φ A₁ v : ℂ) : ExtPlane) :=
    fun v hv => (wd_b_invFunOn_coe hΦ hφ.2.2 hv).1
  have hΨiL : ∀ z ∈ lowerHalf, Function.invFunOn Ψ (closure (toExt A₂)) (z : ExtPlane) =
      ((Function.invFunOn ψ A₂ z : ℂ) : ExtPlane) ∧ Function.invFunOn ψ A₂ z ∈ A₂ :=
    fun z hz => wd_b_invFunOn_coe hΨ hψ.2.2 hz
  set Φi := Function.invFunOn Φ (closure (toExt A₁))
  set Ψi := Function.invFunOn Ψ (closure (toExt A₂))
  set Gi := Function.invFunOn G (closure (toExt upperHalf))
  -- boundary identification: `Φ⁻¹(G⁻¹ y) = Ψ⁻¹ y ∈ C` for real `y`
  have hkey : ∀ y : ℝ, Φi (Gi (((y : ℝ) : ℂ) : ExtPlane)) = Ψi (((y : ℝ) : ℂ) : ExtPlane) ∧
      Ψi (((y : ℝ) : ℂ) : ExtPlane) ∈ C := by
    intro y
    have hyL := wd_b_real_mem_closure_lower y
    have hΨz : Ψ (Ψi (((y : ℝ) : ℂ) : ExtPlane)) = (((y : ℝ) : ℂ) : ExtPlane) := hΨr _ hyL
    have hzC : Ψi (((y : ℝ) : ℂ) : ExtPlane) ∈ C := by
      rw [← hfr₂, hA₂o.frontier_eq]
      refine ⟨hΨim hyL, ?_⟩
      rintro ⟨u, hu, hue⟩
      rw [← hue, hΨ.1 u hu] at hΨz
      have h1 : (ψ u).im < 0 := by
        have h2 : ψ u ∈ lowerHalf := by
          rw [← hψ.2.2]
          exact mem_image_of_mem ψ hu
        exact h2
      rw [OnePoint.coe_injective hΨz, Complex.ofReal_im] at h1
      exact lt_irrefl 0 h1
    have hzne : Ψi (((y : ℝ) : ℂ) : ExtPlane) ≠ extInf := by
      intro h0
      rw [h0, hΨinf] at hΨz
      exact OnePoint.coe_ne_infty _ hΨz.symm
    obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.1 hzne
    rw [← hw] at hzC hΨz ⊢
    obtain ⟨x, hx₁, hx₂⟩ := hh w hzC
    have hxy : (((h x : ℝ) : ℂ) : ExtPlane) = (((y : ℝ) : ℂ) : ExtPlane) := by
      rw [← hx₂, hΨz]
    have hGy : Gi (((y : ℝ) : ℂ) : ExtPlane) = (((x : ℝ) : ℂ) : ExtPlane) := by
      rw [← hxy, ← hGh x]
      exact hGl _ (wd_b_real_mem_closure_upper x)
    refine ⟨?_, hzC⟩
    rw [hGy, ← hx₁]
    exact hΦl _ (hCS₁ hzC)
  -- the three inverses fix `∞`
  have hGiinf : Gi extInf = extInf := by
    have hGeq := hGr _ wd_b_infty_mem_closure_upper
    rcases wd_b_closure_upper_cases (hGim wd_b_infty_mem_closure_upper) with h0 | ⟨x, hx⟩ | ⟨z, hz, hzeq⟩
    · exact h0
    · rw [hx, hGh x] at hGeq
      exact (OnePoint.coe_ne_infty _ hGeq).elim
    · rw [hzeq, hG.1 z hz] at hGeq
      exact (OnePoint.coe_ne_infty _ hGeq).elim
  have hΦiinf : Φi extInf = extInf := by
    have h0 := hΦl _ (hCS₁ hinf)
    rwa [hΦinf] at h0
  have hΨiinf : Ψi extInf = extInf := by
    have h0 := hΨl _ (hCS₂ hinf)
    rwa [hΨinf] at h0
  -- the welded map of `ℂ̄`: `Φ⁻¹ ∘ G⁻¹` on `ℍ̄`, `Ψ⁻¹` on `𝕃̄`
  obtain ⟨E, hE⟩ : ∃ E : ExtPlane → ExtPlane,
      ∀ p, E p = if p ∈ closure (toExt upperHalf) then Φi (Gi p) else Ψi p := ⟨_, fun p => rfl⟩
  have hEU : EqOn E (Φi ∘ Gi) (closure (toExt upperHalf)) := fun p hp => by
    rw [hE, ite_eq_left hp, Function.comp_apply]
  have hEL : EqOn E Ψi (closure (toExt lowerHalf)) := fun p hp => by
    by_cases hpU : p ∈ closure (toExt upperHalf)
    · rw [hE, ite_eq_left hpU]
      rcases wd_b_closure_inter hpU hp with rfl | ⟨y, rfl⟩
      · rw [hGiinf, hΦiinf, hΨiinf]
      · exact (hkey y).1
    · rw [hE, ite_eq_right hpU]
  have hEc : Continuous E := wd_b_paste (hΦic.comp hGic hGim) hΨic hEU hEL
  have hEinj : Function.Injective E := by
    -- a point of `ℍ̄` and a point off `ℍ̄` have different images
    have hsep : ∀ p q, p ∈ closure (toExt upperHalf) → q ∉ closure (toExt upperHalf) → E p ≠ E q := by
      intro p q hp hq hpq
      obtain ⟨z, hz, rfl⟩ := wd_b_not_mem_closure_upper hq
      rw [hEU hp, hE, ite_eq_right hq, (hΨiL z hz).1] at hpq
      have h1 : (Φi ∘ Gi) p ∈ closure (toExt A₁) := hΦim (hGim hp)
      rw [hpq] at h1
      exact disjoint_left.1 (hdisj.closure_left hA₂o) h1 ⟨_, (hΨiL z hz).2, rfl⟩
    intro p q hpq
    by_cases hp : p ∈ closure (toExt upperHalf) <;> by_cases hq : q ∈ closure (toExt upperHalf)
    · rw [hEU hp, hEU hq] at hpq
      have h1 : Gi p = Gi q := by
        rw [← hΦr _ (hGim hp), ← hΦr _ (hGim hq)]
        exact congrArg Φ hpq
      calc p = G (Gi p) := (hGr p hp).symm
        _ = G (Gi q) := by rw [h1]
        _ = q := hGr q hq
    · exact (hsep p q hp hq hpq).elim
    · exact (hsep q p hq hp hpq.symm).elim
    · obtain ⟨z, hz, rfl⟩ := wd_b_not_mem_closure_upper hp
      obtain ⟨w, hw, rfl⟩ := wd_b_not_mem_closure_upper hq
      rw [hE, ite_eq_right hp, hE, ite_eq_right hq] at hpq
      calc (z : ExtPlane) = Ψ (Ψi z) := (hΨr _ (subset_closure ⟨z, hz, rfl⟩)).symm
        _ = Ψ (Ψi w) := by rw [hpq]
        _ = w := hΨr _ (subset_closure ⟨w, hw, rfl⟩)
  have hEinf : E extInf = extInf := by
    rw [hEU wd_b_infty_mem_closure_upper, Function.comp_apply, hGiinf, hΦiinf]
  -- the plane map
  obtain ⟨hHcoe, hHhom⟩ := wd_b_plane_homeo hEc hEinj hEinf
  have hA₁o' : IsOpen A₁ := OnePoint.isOpen_image_coe.1 hA₁o
  have hA₂o' : IsOpen A₂ := OnePoint.isOpen_image_coe.1 hA₂o
  have hLo : IsOpen lowerHalf := isOpen_lt continuous_im continuous_const
  refine ⟨fun z : ℂ => extToC (E z), hHhom, ?_, ?_, ?_⟩
  · -- on `ℍ`, `H = φ⁻¹ ∘ g⁻¹` is `K`-q.c.
    have hgi : IsKQC (Function.invFunOn g upperHalf) upperHalf K := by
      have h0 := thm7_2_inv hg
      rwa [hgs] at h0
    have hsub : Function.invFunOn g upperHalf '' upperHalf ⊆ upperHalf := by
      rintro _ ⟨z, hz, rfl⟩
      exact (hGiU z hz).2
    have hcomp := thm7_1_comp hgi (isKQC_one_of_conformal isOpen_upperHalf (hφ.symm hA₁o')) hsub
    rw [mul_one] at hcomp
    refine ad_isKQC_congr hcomp fun z hz => OnePoint.coe_injective ?_
    show ((extToC (E z) : ℂ) : ExtPlane) =
      ((Function.invFunOn φ A₁ (Function.invFunOn g upperHalf z) : ℂ) : ExtPlane)
    rw [hHcoe z, hEU (subset_closure ⟨z, hz, rfl⟩), Function.comp_apply, (hGiU z hz).1,
      hΦiU _ (hGiU z hz).2]
  · -- on `𝕃`, `H = ψ⁻¹` is conformal
    refine ad_isKQC_congr (isKQC_one_of_conformal hLo (hψ.symm hA₂o')) fun z hz => OnePoint.coe_injective ?_
    have hzU : (z : ExtPlane) ∉ closure (toExt upperHalf) := fun h' =>
      disjoint_left.1 wd_b_closure_upper_disjoint h' ⟨z, hz, rfl⟩
    show ((extToC (E z) : ℂ) : ExtPlane) = ((Function.invFunOn ψ A₂ z : ℂ) : ExtPlane)
    rw [hHcoe z, hE, ite_eq_right hzU]
    exact (hΨiL z hz).1
  · -- `C = H(ℝ) ∪ {∞}`
    have hreal : ∀ y : ℝ, E (((y : ℝ) : ℂ) : ExtPlane) = Ψi (((y : ℝ) : ℂ) : ExtPlane) := fun y => by
      rw [hEU (wd_b_real_mem_closure_upper y), Function.comp_apply]
      exact (hkey y).1
    apply Subset.antisymm
    · intro p hp
      by_cases hpinf : p = extInf
      · exact Or.inr hpinf
      obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.1 hpinf
      obtain ⟨x, -, hx₂⟩ := hh w hp
      refine Or.inl ⟨extToC (E (((h x : ℝ) : ℂ) : ExtPlane)), ⟨((h x : ℝ) : ℂ), Complex.ofReal_im _, rfl⟩, ?_⟩
      rw [hHcoe, hreal, ← hx₂, hΨl _ (hCS₂ hp)]
    · rintro p (⟨_, ⟨z, hz, rfl⟩, rfl⟩ | hp)
      · have hz' : ((z.re : ℝ) : ℂ) = z :=
          Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im]; exact (show z.im = 0 from hz).symm)
        show ((extToC (E z) : ℂ) : ExtPlane) ∈ C
        rw [hHcoe z, ← hz', hreal]
        exact (hkey z.re).2
      · rw [mem_singleton_iff] at hp
        rw [hp]
        exact hinf

/-- Complex conjugation, as a homeomorphism of `ℂ`, maps `ℍ` onto `𝕃`. -/
theorem wd_w_conj_image_upperHalf : Complex.conjLIE.toHomeomorph '' upperHalf = lowerHalf := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    show (conj z).im < 0
    rw [conj_im]
    exact neg_neg_of_pos hz
  · intro hw
    refine ⟨conj w, ?_, conj_conj w⟩
    show 0 < (conj w).im
    rw [conj_im]
    exact neg_pos.mpr hw

/-- Complex conjugation, as a homeomorphism of `ℂ`, maps `𝕃` onto `ℍ`. -/
theorem wd_w_conj_image_lowerHalf : Complex.conjLIE.toHomeomorph '' lowerHalf = upperHalf := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    show 0 < (conj z).im
    rw [conj_im]
    exact neg_pos.mpr hz
  · intro hw
    refine ⟨conj w, ?_, conj_conj w⟩
    show (conj w).im < 0
    rw [conj_im]
    exact neg_neg_of_pos hw

/-- A homeomorphic extension `F` of a self-map `f` of `ℍ` with `F ∞ = ∞` maps the real axis onto itself: every real
point is the `F`-image of a real point (the preimage lies in `ℍ̄ = ℍ ∪ ℝ ∪ {∞}`, but not in `ℍ` and not at `∞`). -/
theorem wd_w_real_preimage {f : ℂ → ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f upperHalf upperHalf F) (hf : MapsTo f upperHalf upperHalf)
    (hinf : F extInf = extInf) (y : ℝ) : ∃ x : ℝ, F ((x : ℂ) : ExtPlane) = ((y : ℂ) : ExtPlane) := by
  have hy : ((y : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) :=
    frontier_subset_closure (ofReal_mem_frontier_upperHalf y)
  rw [← hF.2.2.2] at hy
  obtain ⟨p, hp, hpy⟩ := hy
  induction p using OnePoint.rec with
  | infty =>
    rw [hinf] at hpy
    exact absurd hpy.symm (OnePoint.coe_ne_infty _)
  | coe w =>
    have hw : w ∈ closure upperHalf := by
      rw [OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image]
      exact hp
    have hsub : upperHalf ⊆ {z : ℂ | 0 ≤ z.im} := fun z (hz : 0 < z.im) => hz.le
    have hw0 : 0 ≤ w.im := closure_minimal hsub (isClosed_le continuous_const continuous_im) hw
    have hw1 : ¬ 0 < w.im := by
      intro hpos
      rw [hF.1 w hpos] at hpy
      have h2 : 0 < (f w).im := hf hpos
      rw [OnePoint.coe_injective hpy, ofReal_im] at h2
      exact lt_irrefl _ h2
    have hwr : ((w.re : ℝ) : ℂ) = w := Complex.ext (by simp) (by simp [le_antisymm (not_lt.mp hw1) hw0])
    exact ⟨w.re, by rw [hwr]; exact hpy⟩

/-- **W** (the welding homeomorphism, (⇒) of Theorem 16.3): with `T₁ = φ ∘ g₀ : ℍ → ℍ` (boundary `a`),
`T₂ = ψ ∘ g₀ : 𝕃 → 𝕃` (boundary `h ∘ a` by `hh`) and `T = conj ∘ T₂ ∘ conj`, the map `g = T ∘ T₁⁻¹` is a q.c. self-map
of `ℍ` whose homeomorphic extension `G` (composed from `Φ ∘ ĝ₀`, `Ψ ∘ ĝ₀` and `conj`) fixes `∞` and has boundary values
`h`. -/
theorem wd_forward_core {A₁ A₂ : Set ℂ} {g₀ : ℂ → ℂ} {K : ℝ} (hg₀ : IsKQC g₀ univ K) (hg₀s : g₀ '' univ = univ)
    (hA₁ : A₁ = g₀ '' upperHalf) (hA₂ : A₂ = g₀ '' lowerHalf) {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    (hφ : IsConformalOnto φ A₁ upperHalf) (hψ : IsConformalOnto ψ A₂ lowerHalf)
    (hΦ : IsHomeoExtension φ A₁ upperHalf Φ) (hΨ : IsHomeoExtension ψ A₂ lowerHalf Ψ)
    (hΦinf : Φ extInf = extInf) (hΨinf : Ψ extInf = extInf) {h : ℝ → ℝ}
    (hh : ∀ x : ℝ, ∃ y : ℝ, Φ ((g₀ x : ℂ) : ExtPlane) = ((y : ℂ) : ExtPlane) ∧
      Ψ ((g₀ x : ℂ) : ExtPlane) = (((h y : ℝ) : ℂ) : ExtPlane)) :
    ∃ (g : ℂ → ℂ) (G : ExtPlane → ExtPlane) (K' : ℝ), IsKQC g upperHalf K' ∧ g '' upperHalf = upperHalf ∧
      IsHomeoExtension g upperHalf upperHalf G ∧ G extInf = extInf ∧
      ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = (((h x : ℝ) : ℂ) : ExtPlane) := by
  obtain ⟨e, rfl⟩ := t1_homeomorph hg₀ hg₀s
  subst hA₁ hA₂
  have hLo : IsOpen lowerHalf := isOpen_lt continuous_im continuous_const
  -- `T₁ = φ ∘ g₀ : ℍ → ℍ`
  have hT₁ : IsKQC (φ ∘ ⇑e) upperHalf (K * 1) :=
    thm7_1_comp (ac_t_isKQC_restrict hg₀ isOpen_upperHalf (subset_univ _))
      (isKQC_one_of_conformal (e.isOpenMap _ isOpen_upperHalf) hφ) Subset.rfl
  have hT₁s : (φ ∘ ⇑e) '' upperHalf = upperHalf := by rw [image_comp, hφ.2.2]
  have hT₁m : MapsTo (φ ∘ ⇑e) upperHalf upperHalf := fun z hz => hT₁s ▸ mem_image_of_mem _ hz
  have hT₁e : IsHomeoExtension (φ ∘ ⇑e) upperHalf upperHalf (Φ ∘ e.onePointCongr) :=
    hΦ.comp (s13x_de_isHomeoExtension_homeomorph e upperHalf) (mapsTo_image _ _)
  -- `T₂ = ψ ∘ g₀ : 𝕃 → 𝕃`
  have hT₂ : IsKQC (ψ ∘ ⇑e) lowerHalf (K * 1) :=
    thm7_1_comp (ac_t_isKQC_restrict hg₀ hLo (subset_univ _))
      (isKQC_one_of_conformal (e.isOpenMap _ hLo) hψ) Subset.rfl
  have hT₂s : (ψ ∘ ⇑e) '' lowerHalf = lowerHalf := by rw [image_comp, hψ.2.2]
  have hT₂m : MapsTo (ψ ∘ ⇑e) lowerHalf lowerHalf := fun z hz => hT₂s ▸ mem_image_of_mem _ hz
  have hT₂e : IsHomeoExtension (ψ ∘ ⇑e) lowerHalf lowerHalf (Ψ ∘ e.onePointCongr) :=
    hΨ.comp (s13x_de_isHomeoExtension_homeomorph e lowerHalf) (mapsTo_image _ _)
  -- `T = conj ∘ T₂ ∘ conj : ℍ → ℍ`
  set c : ℂ ≃ₜ ℂ := Complex.conjLIE.toHomeomorph
  have hcU : IsHomeoExtension c upperHalf lowerHalf c.onePointCongr := by
    have h1 := s13x_de_isHomeoExtension_homeomorph c upperHalf
    rwa [wd_w_conj_image_upperHalf] at h1
  have hcL : IsHomeoExtension c lowerHalf upperHalf c.onePointCongr := by
    have h1 := s13x_de_isHomeoExtension_homeomorph c lowerHalf
    rwa [wd_w_conj_image_lowerHalf] at h1
  have hcm : MapsTo c upperHalf lowerHalf := fun z hz =>
    wd_w_conj_image_upperHalf ▸ mem_image_of_mem _ hz
  have hTe : IsHomeoExtension (c ∘ ((ψ ∘ ⇑e) ∘ c)) upperHalf upperHalf
      (c.onePointCongr ∘ ((Ψ ∘ e.onePointCongr) ∘ c.onePointCongr)) :=
    hcL.comp (hT₂e.comp hcU hcm) (hT₂m.comp hcm)
  have hT : IsKQC (c ∘ ((ψ ∘ ⇑e) ∘ c)) upperHalf (K * 1) := by
    have h1 := abR_x_isKQC_conj hT₂
    have hpre : (starRingEnd ℂ) ⁻¹' lowerHalf = upperHalf := by
      ext z
      show (conj z).im < 0 ↔ 0 < z.im
      rw [conj_im, neg_lt_zero]
    rw [hpre] at h1
    exact h1
  have hTs : (c ∘ ((ψ ∘ ⇑e) ∘ c)) '' upperHalf = upperHalf := by
    rw [image_comp, image_comp, wd_w_conj_image_upperHalf, hT₂s, wd_w_conj_image_lowerHalf]
  -- `g = T ∘ T₁⁻¹`
  have hT₁hom : IsHomeomorphOnto (φ ∘ ⇑e) upperHalf upperHalf := by
    have h1 := hT₁.2.2.1
    rwa [hT₁s] at h1
  have hinv : IsKQC (Function.invFunOn (φ ∘ ⇑e) upperHalf) upperHalf (K * 1) := by
    have h1 := thm7_2_inv hT₁
    rwa [hT₁s] at h1
  have hinvm : MapsTo (Function.invFunOn (φ ∘ ⇑e) upperHalf) upperHalf upperHalf := by
    intro w hw
    rw [← hT₁s] at hw
    exact Function.invFunOn_mem hw
  have hinvs : Function.invFunOn (φ ∘ ⇑e) upperHalf '' upperHalf = upperHalf :=
    Subset.antisymm hinvm.image_subset fun z hz =>
      ⟨(φ ∘ ⇑e) z, hT₁m hz, hT₁hom.2.1.leftInvOn_invFunOn hz⟩
  have hinve := uq_isHomeoExtension_invFunOn isOpen_upperHalf isOpen_upperHalf hT₁hom hT₁e
  have hT₁inj := hT₁e.2.2.1
  refine ⟨(c ∘ ((ψ ∘ ⇑e) ∘ c)) ∘ Function.invFunOn (φ ∘ ⇑e) upperHalf,
    (c.onePointCongr ∘ ((Ψ ∘ e.onePointCongr) ∘ c.onePointCongr)) ∘
      Function.invFunOn (Φ ∘ e.onePointCongr) (closure (toExt upperHalf)), (K * 1) * (K * 1),
    thm7_1_comp hinv hT hinvm.image_subset, by rw [image_comp, hinvs, hTs], hTe.comp hinve hinvm, ?_, ?_⟩
  · -- `G ∞ = ∞`
    have hinfmem : extInf ∈ closure (toExt upperHalf) :=
      frontier_subset_closure infty_mem_frontier_upperHalf
    have h1 : Function.invFunOn (Φ ∘ e.onePointCongr) (closure (toExt upperHalf)) extInf = extInf := by
      have h2 := hT₁inj.leftInvOn_invFunOn hinfmem
      have h3 : (Φ ∘ e.onePointCongr) extInf = extInf := hΦinf
      rwa [h3] at h2
    show c.onePointCongr (Ψ (e.onePointCongr (c.onePointCongr
      (Function.invFunOn (Φ ∘ e.onePointCongr) (closure (toExt upperHalf)) extInf)))) = extInf
    rw [h1]
    show c.onePointCongr (Ψ extInf) = extInf
    rw [hΨinf]
    rfl
  · -- boundary values
    intro y
    obtain ⟨x, hx⟩ := wd_w_real_preimage hT₁e hT₁m hΦinf y
    obtain ⟨y', hy'1, hy'2⟩ := hh x
    have hyy : y' = y := by
      have h1 : Φ ((e x : ℂ) : ExtPlane) = ((y : ℂ) : ExtPlane) := hx
      rw [hy'1] at h1
      exact Complex.ofReal_injective (OnePoint.coe_injective h1)
    subst hyy
    have hxmem : ((x : ℂ) : ExtPlane) ∈ closure (toExt upperHalf) :=
      frontier_subset_closure (ofReal_mem_frontier_upperHalf x)
    have h1 : Function.invFunOn (Φ ∘ e.onePointCongr) (closure (toExt upperHalf))
        ((y' : ℂ) : ExtPlane) = ((x : ℂ) : ExtPlane) := by
      rw [← hx]
      exact hT₁inj.leftInvOn_invFunOn hxmem
    show c.onePointCongr (Ψ (e.onePointCongr (c.onePointCongr
      (Function.invFunOn (Φ ∘ e.onePointCongr) (closure (toExt upperHalf)) ((y' : ℂ) : ExtPlane))))) = _
    rw [h1]
    have hcx : c.onePointCongr ((x : ℂ) : ExtPlane) = ((x : ℂ) : ExtPlane) := by
      show (((conj (x : ℂ)) : ℂ) : ExtPlane) = _
      rw [conj_ofReal]
    rw [hcx]
    show c.onePointCongr (Ψ ((e x : ℂ) : ExtPlane)) = _
    rw [hy'2]
    show (((conj ((h y' : ℝ) : ℂ)) : ℂ) : ExtPlane) = _
    rw [conj_ofReal]

/-- (⇒) of Theorem 16.3 with `G ∞ = ∞` (used also for the quasisymmetric corollary in §17): N, then W. -/
theorem wd_forward {C : Set ExtPlane} {A₁ A₂ : Set ℂ} (hinf : extInf ∈ C)
    (hC : AreComplementaryComponents C (toExt A₁) (toExt A₂)) {φ ψ : ℂ → ℂ} {Φ Ψ : ExtPlane → ExtPlane}
    (hφ : IsConformalOnto φ A₁ upperHalf) (hψ : IsConformalOnto ψ A₂ lowerHalf)
    (hΦ : IsHomeoExtension φ A₁ upperHalf Φ) (hΨ : IsHomeoExtension ψ A₂ lowerHalf Ψ)
    (hΦinf : Φ extInf = extInf) (hΨinf : Ψ extInf = extInf) {h : ℝ → ℝ}
    (hh : ∀ z : ℂ, (z : ExtPlane) ∈ C →
      ∃ x : ℝ, Φ z = ((x : ℂ) : ExtPlane) ∧ Ψ z = (((h x : ℝ) : ℂ) : ExtPlane))
    (hq : IsQuasicircle C) :
    ∃ (g : ℂ → ℂ) (G : ExtPlane → ExtPlane) (K : ℝ), IsKQC g upperHalf K ∧ g '' upperHalf = upperHalf ∧
      IsHomeoExtension g upperHalf upperHalf G ∧ G extInf = extInf ∧
      ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = (((h x : ℝ) : ℂ) : ExtPlane) := by
  obtain ⟨g₀, K, hg₀, hg₀s, hCeq, hA₁, hA₂⟩ := wd_normal_form hinf hC hq
  refine wd_forward_core hg₀ hg₀s hA₁ hA₂ hφ hψ hΦ hΨ hΦinf hΨinf fun x => hh (g₀ x) ?_
  rw [hCeq]
  exact Or.inl ⟨g₀ x, ⟨x, Complex.ofReal_im x, rfl⟩, rfl⟩

/-- **Theorem 16.3** (共形映射的粘合, conformal welding).  Let `C` be a Jordan curve through `∞`
with complementary components `A₁, A₂ ⊆ ℂ`, `φ : A₁ → ℍ` and `ψ : A₂ → 𝕃` conformal maps
extending to homeomorphisms `Φ, Ψ` of the closures with `Φ(∞) = Ψ(∞) = ∞`, and let
`h = ψ ∘ φ⁻¹ : ℝ → ℝ` be the induced homeomorphism of the real axis.  Then `C` is a
quasicircle iff `h` is the boundary value of a quasiconformal self-map of `ℍ`. -/
theorem thm16_3_welding {C : Set ExtPlane} {A₁ A₂ : Set ℂ} (hinf : extInf ∈ C)
    (hC : AreComplementaryComponents C (toExt A₁) (toExt A₂)) {φ ψ : ℂ → ℂ}
    {Φ Ψ : ExtPlane → ExtPlane} (hφ : IsConformalOnto φ A₁ upperHalf)
    (hψ : IsConformalOnto ψ A₂ lowerHalf) (hΦ : IsHomeoExtension φ A₁ upperHalf Φ)
    (hΨ : IsHomeoExtension ψ A₂ lowerHalf Ψ) (hΦinf : Φ extInf = extInf) (hΨinf : Ψ extInf = extInf)
    {h : ℝ → ℝ} (hh : ∀ z : ℂ, (z : ExtPlane) ∈ C →
      ∃ x : ℝ, Φ z = ((x : ℂ) : ExtPlane) ∧ Ψ z = (((h x : ℝ) : ℂ) : ExtPlane)) :
    IsQuasicircle C ↔ ∃ (g : ℂ → ℂ) (G : ExtPlane → ExtPlane) (K : ℝ), IsKQC g upperHalf K ∧
      g '' upperHalf = upperHalf ∧ IsHomeoExtension g upperHalf upperHalf G ∧
      ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = (((h x : ℝ) : ℂ) : ExtPlane) := by
  constructor
  · intro hq
    obtain ⟨g, G, K, hg, hgs, hG, -, hGx⟩ := wd_forward hinf hC hφ hψ hΦ hΨ hΦinf hΨinf hh hq
    exact ⟨g, G, K, hg, hgs, hG, hGx⟩
  · rintro ⟨g, G, K, hg, hgs, hG, hGx⟩
    obtain ⟨H, hH, hHU, hHL, hCH⟩ := wd_backward hinf hC hφ hψ hΦ hΨ hΦinf hΨinf hh hg hgs hG hGx
    have hK1 : 1 ≤ K := hg.2.1
    have hH' : IsHomeomorphOnto H univ (H '' univ) := by
      rw [hH.2.2.1]
      exact hH
    have hHK : IsKQC H univ K := wd_glue hK1 hH' hHU (hHL.mono hK1)
    rw [hCH]
    exact ⟨K, isKQuasicircle_image_realLine hHK hH.2.2.1⟩

end LiZhongQC
