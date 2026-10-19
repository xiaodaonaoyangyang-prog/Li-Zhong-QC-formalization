import LiZhongQC.Lemmas.StdGenAlg
import LiZhongQC.Lemmas.StdGenLink1
import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
import LiZhongQC.Lemmas.CaratheodoryJordan

/-!
# Standard generators of a closed surface group (R83): the linking lemma
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section
namespace LiZhongQC

universe u



/-- The Cayley transform `ℍ → 𝔻`. -/
theorem s83sg_cay_norm_lt (z : UpperHalfPlane) : ‖((z : ℂ) - I) / ((z : ℂ) + I)‖ < 1 := by
  have hz : 0 < (z : ℂ).im := z.im_pos
  have h2 : (z : ℂ) + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith [z.im_pos]
  rw [norm_div, div_lt_one (norm_pos_iff.2 h2)]
  apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im]
  nlinarith

theorem s83sg_cay_ne (z : UpperHalfPlane) : (z : ℂ) + I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith [z.im_pos]

theorem s83sg_cay_inj {z w : UpperHalfPlane}
    (h : ((z : ℂ) - I) / ((z : ℂ) + I) = ((w : ℂ) - I) / ((w : ℂ) + I)) : z = w := by
  rw [div_eq_div_iff (s83sg_cay_ne z) (s83sg_cay_ne w)] at h
  apply UpperHalfPlane.ext
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-Complex.I / 2) * h + ((z : ℂ) - w) * hI

theorem s83sg_cay_cont : Continuous fun z : UpperHalfPlane => ((z : ℂ) - I) / ((z : ℂ) + I) :=
  (UpperHalfPlane.continuous_coe.sub continuous_const).div
    (UpperHalfPlane.continuous_coe.add continuous_const) s83sg_cay_ne




/-- Exponentials of angles in a half circle. -/
theorem s83sg_exp_arc_inj {ε u v : ℝ} (hε : ε = 1 ∨ ε = -1) (hu : u ∈ Ico (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1)
    (h : Complex.exp (Complex.I * ((ε * Real.pi * u : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((ε * Real.pi * v : ℝ) : ℂ))) : u = v := by
  rw [Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨n, hn⟩ := h
  have h2 : ((ε * Real.pi * u : ℝ) : ℂ) = ((ε * Real.pi * v : ℝ) : ℂ) + n * (2 * Real.pi) := by
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    apply mul_left_cancel₀ hI
    linear_combination hn
  have h3 : ε * Real.pi * u = ε * Real.pi * v + n * (2 * Real.pi) := by exact_mod_cast h2
  have hpi := Real.pi_pos
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have h4 : ε * (u - v) = 2 * n := by
    have : Real.pi * (ε * (u - v) - 2 * n) = 0 := by linear_combination h3
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hpi.ne'
    · linarith
  have h5 : ((2 : ℝ) * n) ^ 2 = (u - v) ^ 2 := by
    rw [← h4]
    rcases hε with rfl | rfl <;> ring
  have h6 : (u - v) ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2, hv.1, hv.2]
  have h7 : (n : ℝ) < 1 ∧ -1 < (n : ℝ) := by
    constructor <;> nlinarith
  have h8 : n = 0 := by
    have h9 : n < 1 := by exact_mod_cast h7.1
    have h10 : -1 < n := by exact_mod_cast h7.2
    omega
  have hne0 : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have h11 : ε * (u - v) = 0 := by rw [h4, h8]; simp
  have := (mul_eq_zero.1 h11).resolve_left hne0
  linarith




/-- The loop `L̄_a ∪ (half circle)` is a Jordan curve (the Cayley picture of a line from `0` to `∞` in `ℍ`
closed up by a half of the real line). -/
theorem s83sg_loop (a : ℝ → UpperHalfPlane) (ha : Continuous a) (hai : Function.Injective a)
    (hap : Tendsto (fun t => ((a t : ℂ) - I) / ((a t : ℂ) + I)) atTop (𝓝 1))
    (ham : Tendsto (fun t => ((a t : ℂ) - I) / ((a t : ℂ) + I)) atBot (𝓝 (-1)))
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    ∃ J : Set ℂ, IsJordanCurve (toExt J) ∧
      (∀ s, ((a s : ℂ) - I) / ((a s : ℂ) + I) ∈ J) ∧
      (∀ z ∈ J, ‖z‖ < 1 → ∃ s, z = ((a s : ℂ) - I) / ((a s : ℂ) + I)) ∧
      (∀ z ∈ J, ‖z‖ = 1 → 0 ≤ ε * z.im) ∧ (∀ z ∈ J, ‖z‖ ≤ 1) := by
  set G : ℝ → ℂ := fun s => ((a s : ℂ) - I) / ((a s : ℂ) + I) with hGdef
  have hG : Continuous G := s83sg_cay_cont.comp ha
  set φ : ℝ → ℝ := fun t => Real.tan (2 * Real.pi * t - Real.pi / 2) with hφdef
  set f₀ : ℝ → ℂ := fun t => G (φ t) with hf₀def
  have hpi := Real.pi_pos
  have hmaps : ∀ t ∈ Ioo (0 : ℝ) (1 / 2), 2 * Real.pi * t - Real.pi / 2 ∈
      Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  have hφc : ContinuousOn φ (Ioo 0 (1 / 2)) := by
    have h1 : ContinuousOn (fun t : ℝ => 2 * Real.pi * t - Real.pi / 2) (Ioo 0 (1 / 2)) := by fun_prop
    exact Real.continuousOn_tan_Ioo.comp h1 hmaps
  have hf₀c : ContinuousOn f₀ (Ioo 0 (1 / 2)) := hG.comp_continuousOn hφc
  have hlim0 : Tendsto f₀ (𝓝[>] 0) (𝓝 (-1)) := by
    have h1 : Tendsto (fun t : ℝ => 2 * Real.pi * t - Real.pi / 2) (𝓝[>] 0) (𝓝[>] (-(Real.pi / 2))) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ => 2 * Real.pi * t - Real.pi / 2) (𝓝 0) (𝓝 (2 * Real.pi * 0 - Real.pi / 2)) :=
          (by fun_prop : Continuous fun t : ℝ => 2 * Real.pi * t - Real.pi / 2).tendsto 0
        simp only [mul_zero, zero_sub] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        show -(Real.pi / 2) < 2 * Real.pi * t - Real.pi / 2
        have : (0 : ℝ) < t := ht
        nlinarith
    exact ham.comp (Real.tendsto_tan_neg_pi_div_two.comp h1)
  have hlim1 : Tendsto f₀ (𝓝[<] (1 / 2)) (𝓝 1) := by
    have h1 : Tendsto (fun t : ℝ => 2 * Real.pi * t - Real.pi / 2) (𝓝[<] (1 / 2)) (𝓝[<] (Real.pi / 2)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ => 2 * Real.pi * t - Real.pi / 2) (𝓝 (1 / 2))
            (𝓝 (2 * Real.pi * (1 / 2) - Real.pi / 2)) :=
          (by fun_prop : Continuous fun t : ℝ => 2 * Real.pi * t - Real.pi / 2).tendsto _
        have e : 2 * Real.pi * (1 / 2) - Real.pi / 2 = Real.pi / 2 := by ring
        rw [e] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        show 2 * Real.pi * t - Real.pi / 2 < Real.pi / 2
        have : t < 1 / 2 := ht
        nlinarith
    exact hap.comp (Real.tendsto_tan_pi_div_two.comp h1)
  have hext : ContinuousOn (extendFrom (Ioo 0 (1 / 2)) f₀) (Icc 0 (1 / 2)) :=
    continuousOn_Icc_extendFrom_Ioo hf₀c hlim0 hlim1
  have e0 : extendFrom (Ioo (0 : ℝ) (1 / 2)) f₀ 0 = -1 :=
    extendFrom_eq (by rw [closure_Ioo (by norm_num)]; simp)
      (hlim0.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self))
  have e1 : extendFrom (Ioo (0 : ℝ) (1 / 2)) f₀ (1 / 2) = 1 :=
    extendFrom_eq (by rw [closure_Ioo (by norm_num)]; simp)
      (hlim1.mono_left (nhdsWithin_mono _ Ioo_subset_Iio_self))
  have em : ∀ t ∈ Ioo (0 : ℝ) (1 / 2), extendFrom (Ioo 0 (1 / 2)) f₀ t = f₀ t := by
    intro t ht
    exact extendFrom_eq (subset_closure ht) ((hf₀c.continuousAt (Ioo_mem_nhds ht.1 ht.2)).tendsto.mono_left
      nhdsWithin_le_nhds)
  set F : ℝ → ℂ := fun t => if t ≤ 1 / 2 then extendFrom (Ioo 0 (1 / 2)) f₀ t
    else Complex.exp (Complex.I * ((ε * Real.pi * (2 * t - 1) : ℝ) : ℂ)) with hFdef
  have hFA : ∀ t, t ≤ 1 / 2 → F t = extendFrom (Ioo 0 (1 / 2)) f₀ t := fun t ht => by
    simp only [hFdef]
    rw [if_pos ht]
  have hFB : ∀ t, 1 / 2 ≤ t →
      F t = Complex.exp (Complex.I * ((ε * Real.pi * (2 * t - 1) : ℝ) : ℂ)) := by
    intro t ht
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, hFA _ le_rfl, e1]
      simp
    · simp only [hFdef]
      rw [if_neg (not_le.2 h)]
  have hFcont : ContinuousOn F (Icc 0 1) := by
    have hA : ContinuousOn F (Icc 0 (1 / 2)) := hext.congr fun t ht => hFA t ht.2
    have hB : ContinuousOn F (Icc (1 / 2) 1) := by
      have : Continuous fun t : ℝ => Complex.exp (Complex.I * ((ε * Real.pi * (2 * t - 1) : ℝ) : ℂ)) := by
        fun_prop
      exact this.continuousOn.congr fun t ht => hFB t ht.1
    have := hA.union_of_isClosed hB isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at this
  have hFmid : ∀ t ∈ Ioo (0 : ℝ) (1 / 2), F t = G (φ t) := fun t ht => by
    rw [hFA t ht.2.le, em t ht]
  have hF0 : F 0 = -1 := by
    rw [hFA 0 (by norm_num), e0]
  have hnorm_mid : ∀ t ∈ Ioo (0 : ℝ) (1 / 2), ‖F t‖ < 1 := fun t ht => by
    rw [hFmid t ht]
    exact s83sg_cay_norm_lt _
  have hnorm_arc : ∀ t, 1 / 2 ≤ t → ‖F t‖ = 1 := fun t ht => by
    rw [hFB t ht]
    exact Complex.norm_exp_I_mul_ofReal _
  have hexp1 : Complex.exp (Complex.I * ((ε * Real.pi * 1 : ℝ) : ℂ)) = -1 := by
    rcases hε with rfl | rfl
    · rw [show Complex.I * (((1 : ℝ) * Real.pi * 1 : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I by push_cast; ring]
      exact Complex.exp_pi_mul_I
    · rw [show Complex.I * ((((-1 : ℝ)) * Real.pi * 1 : ℝ) : ℂ) = -((Real.pi : ℂ) * Complex.I) by
        push_cast; ring, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
  have hF01 : F 0 = F 1 := by
    rw [hF0, hFB 1 (by norm_num)]
    rw [show (2 * (1 : ℝ) - 1) = 1 by norm_num, hexp1]
  have hz : ∀ r ∈ Ico (0 : ℝ) 1, r = 0 ∨ r ∈ Ioo (0 : ℝ) (1 / 2) ∨ (1 / 2 ≤ r ∧ r < 1) := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with h | h
    · left; exact h.symm
    · rcases lt_or_ge r (1 / 2) with h2 | h2
      · right; left; exact ⟨h, h2⟩
      · right; right; exact ⟨h2, hr.2⟩
  have hz' : ∀ r ∈ Icc (0 : ℝ) 1, r = 0 ∨ r ∈ Ioo (0 : ℝ) (1 / 2) ∨ 1 / 2 ≤ r := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with h | h
    · left; exact h.symm
    · rcases lt_or_ge r (1 / 2) with h2 | h2
      · right; left; exact ⟨h, h2⟩
      · right; right; exact h2
  have harc : ∀ r : ℝ, 1 / 2 ≤ r → r < 1 → (2 * r - 1) ∈ Ico (0 : ℝ) 1 := fun r h1 h2 =>
    ⟨by linarith, by linarith⟩
  have hFinj : InjOn F (Ico 0 1) := by
    intro s hs t ht hst
    rcases hz s hs with rfl | hs1 | hs1 <;> rcases hz t ht with rfl | ht1 | ht1
    · rfl
    · exfalso
      have := hnorm_mid t ht1
      rw [← hst, hF0] at this
      simp at this
    · exfalso
      have h := hst
      rw [hF0, hFB t ht1.1] at h
      have h' : Complex.exp (Complex.I * ((ε * Real.pi * (2 * t - 1) : ℝ) : ℂ)) =
          Complex.exp (Complex.I * ((ε * Real.pi * 1 : ℝ) : ℂ)) := by rw [hexp1]; exact h.symm
      have := s83sg_exp_arc_inj hε (harc t ht1.1 ht1.2) ⟨zero_le_one, le_rfl⟩ h'
      linarith [ht1.2]
    · exfalso
      have := hnorm_mid s hs1
      rw [hst, hF0] at this
      simp at this
    · have h1 : G (φ s) = G (φ t) := by rw [← hFmid s hs1, ← hFmid t ht1]; exact hst
      have h2 := hai (UpperHalfPlane.ext_iff.1 (s83sg_cay_inj h1) |> fun h => UpperHalfPlane.ext h)
      have hm1 := hmaps s hs1
      have hm2 := hmaps t ht1
      have h3 := Real.strictMonoOn_tan.injOn hm1 hm2 h2
      nlinarith [Real.pi_pos]
    · exfalso
      have h1 := hnorm_mid s hs1
      rw [hst, hnorm_arc t ht1.1] at h1
      exact lt_irrefl _ h1
    · exfalso
      have h := hst
      rw [hF0, hFB s hs1.1] at h
      have h' : Complex.exp (Complex.I * ((ε * Real.pi * (2 * s - 1) : ℝ) : ℂ)) =
          Complex.exp (Complex.I * ((ε * Real.pi * 1 : ℝ) : ℂ)) := by rw [hexp1]; exact h
      have := s83sg_exp_arc_inj hε (harc s hs1.1 hs1.2) ⟨zero_le_one, le_rfl⟩ h'
      linarith [hs1.2]
    · exfalso
      have h1 := hnorm_mid t ht1
      rw [← hst, hnorm_arc s hs1.1] at h1
      exact lt_irrefl _ h1
    · rw [hFB s hs1.1, hFB t ht1.1] at hst
      have := s83sg_exp_arc_inj hε (harc s hs1.1 hs1.2)
        ⟨(harc t ht1.1 ht1.2).1, (harc t ht1.1 ht1.2).2.le⟩ hst
      linarith
  have hJ := isJordanCurve_of_loop hFcont hFinj hF01
  refine ⟨F '' Icc 0 1, hJ, ?_, ?_, ?_, ?_⟩
  · intro s
    have hs := Real.arctan_mem_Ioo s
    set t : ℝ := (Real.arctan s + Real.pi / 2) / (2 * Real.pi) with ht
    have ht0 : 0 < t := by rw [ht]; apply div_pos <;> linarith [hs.1]
    have ht1 : t < 1 / 2 := by
      rw [ht, div_lt_iff₀ (by positivity)]
      linarith [hs.2]
    refine ⟨t, ⟨ht0.le, by linarith⟩, ?_⟩
    rw [hFmid t ⟨ht0, ht1⟩]
    have : φ t = s := by
      show Real.tan (2 * Real.pi * t - Real.pi / 2) = s
      have : 2 * Real.pi * t - Real.pi / 2 = Real.arctan s := by
        rw [ht]
        field_simp
        ring
      rw [this, Real.tan_arctan]
    rw [this]
  · rintro _ ⟨t, ht, rfl⟩ hlt
    rcases hz' t ht with h | h | h
    · exfalso
      rw [h, hF0] at hlt
      simp at hlt
    · exact ⟨φ t, hFmid t h⟩
    · exfalso
      rw [hnorm_arc t h] at hlt
      exact lt_irrefl _ hlt
  · rintro _ ⟨t, ht, rfl⟩ hn
    rcases hz' t ht with h | h | h
    · rw [h, hF0]
      simp
    · exfalso
      have := hnorm_mid t h
      rw [hn] at this
      exact lt_irrefl _ this
    · rw [hFB t h, mul_comm Complex.I, Complex.exp_ofReal_mul_I_im]
      have hu : 0 ≤ 2 * t - 1 ∧ 2 * t - 1 ≤ 1 := ⟨by linarith, by linarith [ht.2]⟩
      have hs : 0 ≤ Real.sin (Real.pi * (2 * t - 1)) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      rcases hε with rfl | rfl
      · simpa using hs
      · have : Real.sin (-1 * Real.pi * (2 * t - 1)) = - Real.sin (Real.pi * (2 * t - 1)) := by
          rw [← Real.sin_neg]; congr 1; ring
        rw [this]; linarith
  · rintro _ ⟨t, ht, rfl⟩
    rcases hz' t ht with h | h | h
    · rw [h, hF0]; simp
    · exact (hnorm_mid t h).le
    · exact (hnorm_arc t h).le




/-- The Cayley transform maps open subsets of `ℍ` to open subsets of `ℂ`. -/
theorem s83sg_cay_open {U : Set UpperHalfPlane} (hU : IsOpen U) :
    IsOpen ((fun z : UpperHalfPlane => ((z : ℂ) - I) / ((z : ℂ) + I)) '' U) := by
  set h : ℂ → ℂ := fun w => I * (1 + w) / (1 - w) with hh
  have hne : ∀ w ∈ ball (0 : ℂ) 1, 1 - w ≠ 0 := by
    intro w hw h0
    have : w = 1 := by linear_combination -h0
    rw [this] at hw
    simp at hw
  have hcont : ContinuousOn h (ball 0 1) := by
    refine ContinuousOn.div (by fun_prop) (by fun_prop) hne
  have hopen : IsOpen ((fun z : UpperHalfPlane => (z : ℂ)) '' U) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hU
  have heq : (fun z : UpperHalfPlane => ((z : ℂ) - I) / ((z : ℂ) + I)) '' U =
      ball (0 : ℂ) 1 ∩ h ⁻¹' ((fun z : UpperHalfPlane => (z : ℂ)) '' U) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, z, hz, ?_⟩
      · rw [mem_ball, dist_zero_right]
        exact s83sg_cay_norm_lt z
      · have h2 := s83sg_cay_ne z
        have hw1 : 1 - ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I) ≠ 0 := by
          intro h0
          rw [sub_eq_zero, eq_div_iff h2] at h0
          have : (2 : ℂ) * Complex.I = 0 := by linear_combination h0
          simp at this
        show (z : ℂ) = Complex.I * (1 + ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I)) /
          (1 - ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I))
        rw [eq_div_iff hw1]
        field_simp
        ring
    · rintro ⟨hw, z, hz, hzw⟩
      refine ⟨z, hz, ?_⟩
      have h1 := hne w hw
      have h2 := s83sg_cay_ne z
      have hzw' : (z : ℂ) = Complex.I * (1 + w) / (1 - w) := hzw
      rw [eq_div_iff h1] at hzw'
      show ((z : ℂ) - Complex.I) / ((z : ℂ) + Complex.I) = w
      rw [div_eq_iff h2]
      linear_combination hzw'
  rw [heq]
  exact hcont.isOpen_inter_preimage isOpen_ball hopen




/-- The Cayley transform at a real point: modulus `1` and imaginary part `-2x/(x²+1)`. -/
theorem s83sg_cay_real (x : ℝ) :
    ‖((x : ℂ) - I) / ((x : ℂ) + I)‖ = 1 ∧
      (((x : ℂ) - I) / ((x : ℂ) + I)).im = -2 * x / (x ^ 2 + 1) := by
  have h : (x : ℂ) + I ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
  have hx : (x : ℂ) - I = ((x : ℂ) + I) * (((x : ℂ) - I) / ((x : ℂ) + I)) := by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [norm_div]
    have h1 : ‖(x : ℂ) - I‖ = ‖(x : ℂ) + I‖ := by
      have e1 : ‖(x : ℂ) - I‖ ^ 2 = x ^ 2 + 1 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
      have e2 : ‖(x : ℂ) + I‖ ^ 2 = x ^ 2 + 1 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
      have := e1.trans e2.symm
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
    rw [h1]
    exact div_self (norm_ne_zero_iff.2 h)
  · have h2 : ((x : ℂ) - I) / ((x : ℂ) + I) =
        (((x : ℂ) - I) * ((x : ℂ) - I)) / (((x : ℂ) + I) * ((x : ℂ) - I)) := by
      rw [mul_div_mul_right _ _ (sub_ne_zero.2 (fun h0 => by
        have := congrArg Complex.im h0; simp at this))]
    rw [h2]
    have h3 : ((x : ℂ) + I) * ((x : ℂ) - I) = ((x ^ 2 + 1 : ℝ) : ℂ) := by
      push_cast
      linear_combination (-1 : ℂ) * Complex.I_sq
    rw [h3]
    have h4 : (0 : ℝ) < x ^ 2 + 1 := by positivity
    rw [show ((x : ℂ) - I) * ((x : ℂ) - I) = (((x ^ 2 - 1 : ℝ)) : ℂ) + ((-(2 * x) : ℝ) : ℂ) * I by
      push_cast
      linear_combination Complex.I_sq]
    rw [Complex.div_ofReal_im]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im]
    ring




theorem s83sg_mc_coe {z : ℂ} (h : z + I ≠ 0) :
    mobiusExt 1 (-I) 1 I ((z : ℂ) : ExtPlane) = (((z - I) / (z + I) : ℂ) : ExtPlane) := by
  rw [mobiusExt_coe (by simpa using h)]
  congr 1
  simp [mobiusFn, sub_eq_add_neg]

theorem s83sg_mc_infty : mobiusExt 1 (-I) 1 I extInf = ((1 : ℂ) : ExtPlane) := by
  rw [mobiusExt_infty_of_ne one_ne_zero]
  simp

theorem s83sg_mc_cont : Continuous (mobiusExt 1 (-I) 1 I) :=
  continuous_mobiusExt (by simp)

/-- Cayley images of a sequence of points of `ℍ` converging to `p` in `ℂ̄`. -/
theorem s83sg_tendsto_cay {ι : Type*} {l : Filter ι} {f : ι → UpperHalfPlane} {p : ExtPlane}
    (h : Tendsto (fun t => ((f t : ℂ) : ExtPlane)) l (𝓝 p)) :
    Tendsto (fun t => ((((f t : ℂ) - I) / ((f t : ℂ) + I) : ℂ) : ExtPlane)) l
      (𝓝 (mobiusExt 1 (-I) 1 I p)) := by
  have := (s83sg_mc_cont.tendsto p).comp h
  refine this.congr fun t => ?_
  exact s83sg_mc_coe (s83sg_cay_ne (f t))

/-- Converting convergence in `ℂ̄` of finite points to convergence in `ℂ`. -/
theorem s83sg_tendsto_of_coe {ι : Type*} {l : Filter ι} {f : ι → ℂ} {w : ℂ}
    (h : Tendsto (fun t => ((f t : ℂ) : ExtPlane)) l (𝓝 ((w : ℂ) : ExtPlane))) :
    Tendsto f l (𝓝 w) :=
  (OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff).2 h




/-- **Core of the linking lemma** (after the normalization `a : 0 → ∞`): see `s83sg_link_sep`. -/
theorem s83sg_core {a b : ℝ → UpperHalfPlane} (ha : Continuous a) (hb : Continuous b)
    (hai : Function.Injective a)
    (hap : Tendsto (fun t => ((a t : ℂ) : ExtPlane)) atTop (𝓝 extInf))
    (ham : Tendsto (fun t => ((a t : ℂ) : ExtPlane)) atBot (𝓝 ((0 : ℂ) : ExtPlane)))
    {ηp ηm : ExtPlane} (hbp : Tendsto (fun t => ((b t : ℂ) : ExtPlane)) atTop (𝓝 ηp))
    (hbm : Tendsto (fun t => ((b t : ℂ) : ExtPlane)) atBot (𝓝 ηm))
    (hmeet : ∀ s t, a s = b t → s = 0 ∧ t = 0) (h0 : a 0 = b 0)
    (hcross : ∃ N Wp Wm : Set UpperHalfPlane, IsOpen N ∧ a 0 ∈ N ∧ IsOpen Wp ∧ IsOpen Wm ∧
      IsConnected Wp ∧ IsConnected Wm ∧ Disjoint Wp Wm ∧ N \ range a = Wp ∪ Wm ∧
      (∃ ε > 0, ∀ s, 0 < s → s < ε → b s ∈ Wp) ∧ (∃ ε > 0, ∀ s, -ε < s → s < 0 → b s ∈ Wm)) :
    ∀ C : Set ExtPlane, C ⊆ extRealLine → IsConnected C → ηp ∈ C → ηm ∈ C →
      extInf ∈ C ∨ ((0 : ℂ) : ExtPlane) ∈ C := by
  intro C hCsub hCconn hηpC hηmC
  -- `h0` is implied by the crossing data and not needed (the statement stays true without it)
  have _h0 := h0
  by_contra hno
  push Not at hno
  obtain ⟨hnoI, hno0⟩ := hno
  set g : UpperHalfPlane → ℂ := fun z => ((z : ℂ) - I) / ((z : ℂ) + I) with hg
  set gr : ℝ → ℂ := fun x => ((x : ℂ) - I) / ((x : ℂ) + I) with hgr
  have hrne : ∀ x : ℝ, (x : ℂ) + I ≠ 0 := by
    intro x h0
    have := congrArg Complex.im h0
    simp at this
  have hgrc : Continuous gr :=
    Continuous.div (by fun_prop) (by fun_prop) hrne
  have hgc : Continuous g := s83sg_cay_cont
  -- Step A: limits of `g ∘ a`
  have hGp : Tendsto (fun t => g (a t)) atTop (𝓝 1) := by
    have := s83sg_tendsto_cay hap
    rw [s83sg_mc_infty] at this
    exact s83sg_tendsto_of_coe this
  have hGm : Tendsto (fun t => g (a t)) atBot (𝓝 (-1)) := by
    have := s83sg_tendsto_cay ham
    have e : mobiusExt 1 (-I) 1 I ((0 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) := by
      rw [s83sg_mc_coe (by simp)]
      congr 1
      simp
    rw [e] at this
    exact s83sg_tendsto_of_coe this
  -- Step B: the sign of `C`
  have hemb : Topology.IsEmbedding (fun x : ℝ => ((x : ℂ) : ExtPlane)) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.comp Complex.isometry_ofReal.isEmbedding
  set C₀ : Set ℝ := (fun x : ℝ => ((x : ℂ) : ExtPlane)) ⁻¹' C with hC₀
  have hCimg : C = (fun x : ℝ => ((x : ℂ) : ExtPlane)) '' C₀ := by
    ext p
    constructor
    · intro hp
      rcases hCsub hp with ⟨z, hz, rfl⟩ | hinf
      · refine ⟨z.re, ?_, ?_⟩
        · show (((z.re : ℝ) : ℂ) : ExtPlane) ∈ C
          have : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simpa using hz.symm)
          rw [this]
          exact hp
        · have : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simpa using hz.symm)
          show (((z.re : ℝ) : ℂ) : ExtPlane) = (z : ExtPlane)
          rw [this]
      · rw [mem_singleton_iff.1 hinf] at hp
        exact absurd hp hnoI
    · rintro ⟨x, hx, rfl⟩
      exact hx
  have hC₀pre : IsPreconnected C₀ := by
    have := hCconn.isPreconnected
    rw [hCimg] at this
    exact hemb.isPreconnected_image.1 this
  have hC₀sub : C₀ ⊆ Iio 0 ∪ Ioi 0 := by
    intro x hx
    rcases lt_trichotomy x 0 with h | h | h
    · exact Or.inl h
    · exfalso
      apply hno0
      have : (((x : ℝ) : ℂ) : ExtPlane) ∈ C := hx
      rwa [h, Complex.ofReal_zero] at this
    · exact Or.inr h
  obtain ⟨ε, hε, hsign⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ x ∈ C₀, ε * (gr x).im < 0 := by
    have hdj : Disjoint (Iio (0 : ℝ)) (Ioi (0 : ℝ)) :=
      Set.disjoint_left.2 fun x hx hx' => lt_asymm (show x < 0 from hx) (show 0 < x from hx')
    rcases IsPreconnected.subset_or_subset (isOpen_Iio : IsOpen (Iio (0 : ℝ))) isOpen_Ioi hdj hC₀sub
      hC₀pre with h | h
    · refine ⟨-1, Or.inr rfl, fun x hx => ?_⟩
      have hx' : x < 0 := h hx
      rw [(s83sg_cay_real x).2]
      have : 0 < x ^ 2 + 1 := by positivity
      have h2 : (-1 : ℝ) * (-2 * x / (x ^ 2 + 1)) = 2 * x / (x ^ 2 + 1) := by ring
      rw [h2]
      exact div_neg_of_neg_of_pos (by linarith) this
    · refine ⟨1, Or.inl rfl, fun x hx => ?_⟩
      have hx' : 0 < x := h hx
      rw [(s83sg_cay_real x).2]
      have : 0 < x ^ 2 + 1 := by positivity
      rw [one_mul]
      exact div_neg_of_neg_of_pos (by linarith) this
  -- Step C: the Jordan curve
  obtain ⟨J, hJ, hJa, hJlt, hJcirc, hJle⟩ := s83sg_loop a ha hai hGp hGm hε
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hAB, hAJ, hBJ, huniv, -, -⟩ := jordan_curve_theorem_complex_bounded hJ
  obtain ⟨hfA, hfB⟩ := frontier_pieces_eq_of_jordan_curve_theorem_complex hJ hAo hBo hAc hBc hAB hAJ hBJ huniv
  have hcomp : ∀ w, w ∉ J → w ∈ A ∨ w ∈ B := by
    intro w hw
    have : w ∈ A ∪ B ∪ J := by rw [huniv]; trivial
    rcases this with (h | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hw
  -- Step D: the crossing data
  obtain ⟨N, Wp, Wm, hNo, hx0N, hWpo, hWmo, hWpc, hWmc, hWdisj, hNeq, ⟨εp, hεp, hbWp⟩,
    ⟨εm, hεm, hbWm⟩⟩ := hcross
  have hnotJ : ∀ z : UpperHalfPlane, z ∉ range a → g z ∉ J := by
    intro z hz hzJ
    obtain ⟨s, hs⟩ := hJlt _ hzJ (s83sg_cay_norm_lt z)
    exact hz ⟨s, (s83sg_cay_inj hs).symm⟩
  have hrangeJ : ∀ n : UpperHalfPlane, n ∈ range a → g n ∈ J := by
    rintro n ⟨s, rfl⟩
    exact hJa s
  have hN'o : IsOpen (g '' N) := s83sg_cay_open hNo
  have hx0 : g (a 0) ∈ J := hJa 0
  have hWp'J : ∀ w ∈ g '' Wp, w ∉ J := by
    rintro _ ⟨z, hz, rfl⟩
    have : z ∈ N \ range a := by rw [hNeq]; exact Or.inl hz
    exact hnotJ z this.2
  have hWm'J : ∀ w ∈ g '' Wm, w ∉ J := by
    rintro _ ⟨z, hz, rfl⟩
    have : z ∈ N \ range a := by rw [hNeq]; exact Or.inr hz
    exact hnotJ z this.2
  have hWp'c : IsPreconnected (g '' Wp) := hWpc.isPreconnected.image g hgc.continuousOn
  have hWm'c : IsPreconnected (g '' Wm) := hWmc.isPreconnected.image g hgc.continuousOn
  have hsub_or : ∀ S : Set ℂ, IsPreconnected S → (∀ w ∈ S, w ∉ J) → S ⊆ A ∨ S ⊆ B := by
    intro S hS hSJ
    exact hS.subset_or_subset hAo hBo hAB fun w hw => by
      rcases hcomp w (hSJ w hw) with h | h
      · exact Or.inl h
      · exact Or.inr h
  have hN'sub : ∀ w ∈ g '' N, w ∈ J ∨ w ∈ g '' Wp ∨ w ∈ g '' Wm := by
    rintro _ ⟨n, hn, rfl⟩
    by_cases hr : n ∈ range a
    · exact Or.inl (hrangeJ n hr)
    · have : n ∈ N \ range a := ⟨hn, hr⟩
      rw [hNeq] at this
      rcases this with h | h
      · exact Or.inr (Or.inl ⟨n, h, rfl⟩)
      · exact Or.inr (Or.inr ⟨n, h, rfl⟩)
  have hfrontA : g (a 0) ∈ closure A := by
    have : g (a 0) ∈ frontier A := by rw [hfA]; exact hx0
    exact frontier_subset_closure this
  have hfrontB : g (a 0) ∈ closure B := by
    have : g (a 0) ∈ frontier B := by rw [hfB]; exact hx0
    exact frontier_subset_closure this
  have key1 : ∀ X Y : Set ℂ, Disjoint X Y → Disjoint Y J → g (a 0) ∈ closure Y →
      g '' Wp ⊆ X → g '' Wm ⊆ X → False := by
    intro X Y hXY hYJ hcl h1 h2
    obtain ⟨w, hwN, hwY⟩ := mem_closure_iff.1 hcl (g '' N) hN'o ⟨a 0, hx0N, rfl⟩
    rcases hN'sub w hwN with h | h | h
    · exact (Set.disjoint_left.1 hYJ) hwY h
    · exact Set.disjoint_left.1 hXY (h1 h) hwY
    · exact Set.disjoint_left.1 hXY (h2 h) hwY
  obtain ⟨X, Y, hXo, hYo, hXY, hXJ, hYJ, hu, hpX, hmY⟩ : ∃ X Y : Set ℂ, IsOpen X ∧ IsOpen Y ∧
      Disjoint X Y ∧ Disjoint X J ∧ Disjoint Y J ∧ (∀ w, w ∉ J → w ∈ X ∨ w ∈ Y) ∧
      g '' Wp ⊆ X ∧ g '' Wm ⊆ Y := by
    rcases hsub_or _ hWp'c hWp'J with hpA | hpB <;> rcases hsub_or _ hWm'c hWm'J with hmA | hmB
    · exact (key1 A B hAB hBJ hfrontB hpA hmA).elim
    · exact ⟨A, B, hAo, hBo, hAB, hAJ, hBJ, hcomp, hpA, hmB⟩
    · exact ⟨B, A, hBo, hAo, hAB.symm, hBJ, hAJ, fun w hw => (hcomp w hw).symm, hpB, hmA⟩
    · exact (key1 B A hAB.symm hAJ hfrontA hpB hmB).elim
  have hsub_or' : ∀ S : Set ℂ, IsPreconnected S → (∀ w ∈ S, w ∉ J) → S ⊆ X ∨ S ⊆ Y := by
    intro S hS hSJ
    exact hS.subset_or_subset hXo hYo hXY fun w hw => hu w (hSJ w hw)
  -- Step E: the rays of `b`
  have hbJ : ∀ s : ℝ, s ≠ 0 → g (b s) ∉ J := by
    intro s hs
    refine hnotJ (b s) ?_
    rintro ⟨r, hr⟩
    exact hs (hmeet r s hr).2
  have hgbc : Continuous fun s => g (b s) := hgc.comp hb
  have hRp : (fun s => g (b s)) '' Ioi (0 : ℝ) ⊆ X := by
    rcases hsub_or' _ (isPreconnected_Ioi.image _ hgbc.continuousOn)
      (by rintro _ ⟨s, hs, rfl⟩; exact hbJ s (ne_of_gt hs)) with h | h
    · exact h
    · exfalso
      have h1 : g (b (εp / 2)) ∈ g '' Wp := ⟨b (εp / 2), hbWp _ (by linarith) (by linarith), rfl⟩
      have h2 : g (b (εp / 2)) ∈ (fun s => g (b s)) '' Ioi (0 : ℝ) := ⟨εp / 2, by simpa using hεp, rfl⟩
      exact Set.disjoint_left.1 hXY (hpX h1) (h h2)
  have hRm : (fun s => g (b s)) '' Iio (0 : ℝ) ⊆ Y := by
    rcases hsub_or' _ (isPreconnected_Iio.image _ hgbc.continuousOn)
      (by rintro _ ⟨s, hs, rfl⟩; exact hbJ s (ne_of_lt hs)) with h | h
    · exfalso
      have h1 : g (b (-(εm / 2))) ∈ g '' Wm :=
        ⟨b (-(εm / 2)), hbWm _ (by linarith) (by linarith), rfl⟩
      have h2 : g (b (-(εm / 2))) ∈ (fun s => g (b s)) '' Iio (0 : ℝ) :=
        ⟨-(εm / 2), by simp only [mem_Iio]; linarith, rfl⟩
      exact Set.disjoint_left.1 hXY (h h2) (hmY h1)
    · exact h
  -- Step F: the endpoints
  obtain ⟨xp, hxpC, hxp⟩ : ∃ x ∈ C₀, ((x : ℂ) : ExtPlane) = ηp := by
    have := hηpC
    rw [hCimg] at this
    exact this
  obtain ⟨xm, hxmC, hxm⟩ : ∃ x ∈ C₀, ((x : ℂ) : ExtPlane) = ηm := by
    have := hηmC
    rw [hCimg] at this
    exact this
  have hlimp : Tendsto (fun t => g (b t)) atTop (𝓝 (gr xp)) := by
    have := s83sg_tendsto_cay hbp
    rw [← hxp, s83sg_mc_coe (hrne xp)] at this
    exact s83sg_tendsto_of_coe this
  have hlimm : Tendsto (fun t => g (b t)) atBot (𝓝 (gr xm)) := by
    have := s83sg_tendsto_cay hbm
    rw [← hxm, s83sg_mc_coe (hrne xm)] at this
    exact s83sg_tendsto_of_coe this
  have hclp : gr xp ∈ closure ((fun s => g (b s)) '' Ioi (0 : ℝ)) :=
    mem_closure_of_tendsto hlimp (eventually_atTop.2 ⟨1, fun t ht => ⟨t, by simp only [mem_Ioi]; linarith, rfl⟩⟩)
  have hclm : gr xm ∈ closure ((fun s => g (b s)) '' Iio (0 : ℝ)) :=
    mem_closure_of_tendsto hlimm (eventually_atBot.2 ⟨-1, fun t ht => ⟨t, by simp only [mem_Iio]; linarith, rfl⟩⟩)
  have hnotJgr : ∀ x ∈ C₀, gr x ∉ J := by
    intro x hx hJx
    have h1 := hJcirc _ hJx (s83sg_cay_real x).1
    have h2 := hsign x hx
    linarith
  have hwpX : gr xp ∈ X := by
    rcases hu _ (hnotJgr xp hxpC) with h | h
    · exact h
    · exfalso
      obtain ⟨w, hwY, hwR⟩ := mem_closure_iff.1 hclp Y hYo h
      exact Set.disjoint_left.1 hXY (hRp hwR) hwY
  have hwmY : gr xm ∈ Y := by
    rcases hu _ (hnotJgr xm hxmC) with h | h
    · exfalso
      obtain ⟨w, hwX, hwR⟩ := mem_closure_iff.1 hclm X hXo h
      exact Set.disjoint_left.1 hXY hwX (hRm hwR)
    · exact h
  -- Step G: `C` is connected and misses `J`
  have hC'c : IsPreconnected (gr '' C₀) := hC₀pre.image gr hgrc.continuousOn
  rcases hsub_or' _ hC'c (by rintro _ ⟨x, hx, rfl⟩; exact hnotJgr x hx) with h | h
  · exact Set.disjoint_left.1 hXY (h ⟨xm, hxmC, rfl⟩) hwmY
  · exact Set.disjoint_left.1 hXY hwpX (h ⟨xp, hxpC, rfl⟩)




/-- **[L4 + JCT]** Linking of two equivariant lines that meet exactly once and cross there: the endpoints at
infinity interleave. -/
theorem s83sg_link_sep {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : IsHyperbolic γ) (hδ : IsHyperbolic δ)
    (hdisj : ∀ x ∈ ({attractingFixedPoint γ, repellingFixedPoint γ} : Set ExtPlane),
      x ∉ ({attractingFixedPoint δ, repellingFixedPoint δ} : Set ExtPlane))
    {a b : ℝ → UpperHalfPlane} (ha : Continuous a) (hb : Continuous b)
    (hai : Function.Injective a) (hbi : Function.Injective b)
    (haγ : ∀ t, a (t + 1) = γ • a t) (hbδ : ∀ t, b (t + 1) = δ • b t)
    (h0 : a 0 = b 0) (hmeet : ∀ s t, a s = b t → s = 0 ∧ t = 0)
    (hcross : ∃ N Wp Wm : Set UpperHalfPlane, IsOpen N ∧ a 0 ∈ N ∧ IsOpen Wp ∧ IsOpen Wm ∧
      IsConnected Wp ∧ IsConnected Wm ∧ Disjoint Wp Wm ∧ N \ range a = Wp ∪ Wm ∧
      (∃ ε > 0, ∀ s, 0 < s → s < ε → b s ∈ Wp) ∧ (∃ ε > 0, ∀ s, -ε < s → s < 0 → b s ∈ Wm)) :
    ∀ C : Set ExtPlane, C ⊆ extRealLine → IsConnected C → attractingFixedPoint δ ∈ C →
      repellingFixedPoint δ ∈ C → attractingFixedPoint γ ∈ C ∨ repellingFixedPoint γ ∈ C := by
  intro C hCsub hCconn hηpC hηmC
  -- `hdisj` and `hbi` are not needed: `η± ∈ C` already excludes the fixed points of `γ` when the conclusion
  -- fails, and `b` is only used through its limits and the one crossing (the statement stays true without them)
  have _hdisj := hdisj
  have _hbi := hbi
  have hγ' : 2 < |γ 0 0 + γ 1 1| := hγ
  have hγ4 : 4 < (γ 0 0 + γ 1 1) ^ 2 := by
    nlinarith [sq_abs (γ 0 0 + γ 1 1), abs_nonneg (γ 0 0 + γ 1 1)]
  obtain ⟨A, h01, h10, hl⟩ := s83sg_diagonalize γ hγ4
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ₁ = A * γ * A⁻¹ := ⟨_, rfl⟩
  obtain ⟨δ₁, hδ₁⟩ : ∃ δ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ, δ₁ = A * δ * A⁻¹ := ⟨_, rfl⟩
  rw [← hγ₁] at h01 h10 hl
  have hγ₁h : IsHyperbolic γ₁ := by
    show 2 < |γ₁ 0 0 + γ₁ 1 1|
    rw [hγ₁, s83sg_trace_conj]
    exact hγ'
  have hδ₁h : IsHyperbolic δ₁ := by
    show 2 < |δ₁ 0 0 + δ₁ 1 1|
    rw [hδ₁, s83sg_trace_conj]
    exact hδ
  -- the homeomorphism `z ↦ A • z` of `ℍ`
  let Tm : UpperHalfPlane ≃ₜ UpperHalfPlane :=
    { toFun := fun z => A • z
      invFun := fun z => A⁻¹ • z
      left_inv := fun z => inv_smul_smul A z
      right_inv := fun z => smul_inv_smul A z
      continuous_toFun := (s27t_mdifferentiable_smul A).continuous
      continuous_invFun := (s27t_mdifferentiable_smul A⁻¹).continuous }
  have hTm : ∀ z, Tm z = A • z := fun z => rfl
  set a' : ℝ → UpperHalfPlane := fun t => A • a t with ha'def
  set b' : ℝ → UpperHalfPlane := fun t => A • b t with hb'def
  have ha' : Continuous a' := Tm.continuous.comp ha
  have hb' : Continuous b' := Tm.continuous.comp hb
  have hper_a : ∀ t, a' (t + 1) = γ₁ • a' t := by
    intro t
    show A • a (t + 1) = γ₁ • (A • a t)
    rw [haγ, ← mul_smul, ← mul_smul, hγ₁]
    congr 1
    group
  have hper_b : ∀ t, b' (t + 1) = δ₁ • b' t := by
    intro t
    show A • b (t + 1) = δ₁ • (A • b t)
    rw [hbδ, ← mul_smul, ← mul_smul, hδ₁]
    congr 1
    group
  obtain ⟨hap, ham⟩ := s83sg_line_ends hγ₁h ha' hper_a
  obtain ⟨hbp, hbm⟩ := s83sg_line_ends hδ₁h hb' hper_b
  have hc1 : γ₁ 1 0 = 0 := h10
  have hA1 : 1 < |γ₁ 0 0| := by
    have : 1 < γ₁ 0 0 ^ 2 := hl
    exact one_lt_sq_iff_one_lt_abs _ |>.1 this
  obtain ⟨hf1, -⟩ := hnf_fixed_of_eq_zero hc1
  have hattr : attractingFixedPoint γ₁ = extInf := (hf1 hA1).1
  have hrep : repellingFixedPoint γ₁ = ((0 : ℂ) : ExtPlane) := by
    rw [(hf1 hA1).2, h01]
    simp
  rw [hattr] at hap
  rw [hrep] at ham
  -- the real Möbius map
  set M : ExtPlane → ExtPlane := mobiusSL (slRealToComplex A) with hM
  have hMhomeo : ⇑(k24_mobiusSLHomeo (slRealToComplex A)) = M := rfl
  have hMcont : Continuous M := (k24_mobiusSLHomeo (slRealToComplex A)).continuous
  have hMinj : Function.Injective M := (k24_mobiusSLHomeo (slRealToComplex A)).injective
  have hMpt : ∀ τ : UpperHalfPlane, M ((τ : ℂ) : ExtPlane) = ((A • τ : UpperHalfPlane) : ℂ) :=
    fun τ => h36t_mobiusSL_coe A τ
  have hMline : ∀ (f : ℝ → UpperHalfPlane) (l : Filter ℝ) (p : ExtPlane),
      Tendsto (fun t => ((f t : ℂ) : ExtPlane)) l (𝓝 p) →
      Tendsto (fun t => (((A • f t : UpperHalfPlane) : ℂ) : ExtPlane)) l (𝓝 (M p)) := by
    intro f l p h
    exact ((hMcont.tendsto p).comp h).congr fun t => hMpt (f t)
  obtain ⟨hapγ, hamγ⟩ := s83sg_line_ends hγ ha haγ
  obtain ⟨hapδ, hamδ⟩ := s83sg_line_ends hδ hb hbδ
  have e1 : M (attractingFixedPoint γ) = extInf := tendsto_nhds_unique (hMline a atTop _ hapγ) hap
  have e2 : M (repellingFixedPoint γ) = ((0 : ℂ) : ExtPlane) :=
    tendsto_nhds_unique (hMline a atBot _ hamγ) ham
  have e3 : M (attractingFixedPoint δ) = attractingFixedPoint δ₁ :=
    tendsto_nhds_unique (hMline b atTop _ hapδ) hbp
  have e4 : M (repellingFixedPoint δ) = repellingFixedPoint δ₁ :=
    tendsto_nhds_unique (hMline b atBot _ hamδ) hbm
  -- transport of the crossing data
  obtain ⟨N, Wp, Wm, hNo, hx0N, hWpo, hWmo, hWpc, hWmc, hWdisj, hNeq, ⟨εp, hεp, hbWp⟩,
    ⟨εm, hεm, hbWm⟩⟩ := hcross
  have hrange : range a' = Tm '' range a := by
    rw [← Set.range_comp]
    rfl
  have hcross' : ∃ N Wp Wm : Set UpperHalfPlane, IsOpen N ∧ a' 0 ∈ N ∧ IsOpen Wp ∧ IsOpen Wm ∧
      IsConnected Wp ∧ IsConnected Wm ∧ Disjoint Wp Wm ∧ N \ range a' = Wp ∪ Wm ∧
      (∃ ε > 0, ∀ s, 0 < s → s < ε → b' s ∈ Wp) ∧ (∃ ε > 0, ∀ s, -ε < s → s < 0 → b' s ∈ Wm) := by
    refine ⟨Tm '' N, Tm '' Wp, Tm '' Wm, Tm.isOpenMap _ hNo, ⟨a 0, hx0N, rfl⟩, Tm.isOpenMap _ hWpo,
      Tm.isOpenMap _ hWmo, hWpc.image _ Tm.continuous.continuousOn,
      hWmc.image _ Tm.continuous.continuousOn, ?_, ?_, ⟨εp, hεp, fun s hs hs' => ⟨b s, hbWp s hs hs', rfl⟩⟩,
      ⟨εm, hεm, fun s hs hs' => ⟨b s, hbWm s hs hs', rfl⟩⟩⟩
    · exact (Set.disjoint_image_iff Tm.injective).2 hWdisj
    · rw [hrange, ← Set.image_diff Tm.injective, hNeq, Set.image_union]
  have hmeet' : ∀ s t, a' s = b' t → s = 0 ∧ t = 0 := fun s t h =>
    hmeet s t (Tm.injective h)
  have hη : ∀ x ∈ ({attractingFixedPoint δ₁, repellingFixedPoint δ₁} : Set ExtPlane), x ∈ extRealLine := by
    intro x hx
    rcases s83sg_fixpt_cases hδ₁h hx with rfl | ⟨r, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl ⟨(r : ℂ), by simp [realLine], rfl⟩
  have hcore := s83sg_core ha' hb' (Tm.injective.comp hai) hap ham hbp hbm hmeet'
    (show A • a 0 = A • b 0 by rw [h0]) hcross'
  have hsub : M '' C ⊆ extRealLine := by
    rintro _ ⟨c, hc, rfl⟩
    have h := k24_real_image_extRealLine A
    rw [← h]
    exact ⟨c, hCsub hc, rfl⟩
  rcases hcore (M '' C) hsub (hCconn.image M hMcont.continuousOn) ⟨_, hηpC, e3⟩ ⟨_, hηmC, e4⟩ with h | h
  · obtain ⟨c, hc, hce⟩ := h
    left
    have : c = attractingFixedPoint γ := hMinj (hce.trans e1.symm)
    rw [← this]
    exact hc
  · obtain ⟨c, hc, hce⟩ := h
    right
    have : c = repellingFixedPoint γ := hMinj (hce.trans e2.symm)
    rw [← this]
    exact hc


end LiZhongQC
