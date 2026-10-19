import LiZhongQC.Lemmas.SchottkyReflectionCoordinates
import LiZhongQC.Lemmas.QDReflectionHolInverse
import LiZhongQC.Lemmas.SchottkyCollarHole
import LiZhongQC.Lemmas.CaratheodoryJordan
import LiZhongQC.Lemmas.FiniteTypeComponentTrapping
import LiZhongQC.ClusterSets
import LiZhongQC.RiemannMapping
import Mathlib.Analysis.Complex.OpenMapping

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Manifold ContDiff
noncomputable section
namespace LiZhongQC
universe u

theorem s31qc_isRealSymmetric_ball (x ρ : ℝ) : IsRealSymmetric (ball (x : ℂ) ρ) := by
  refine ⟨isOpen_ball, ?_⟩
  show conj '' ball (x : ℂ) ρ = ball (x : ℂ) ρ
  have hd : ∀ z : ℂ, dist (conj z) (x : ℂ) = dist z (x : ℂ) := by
    intro z
    have := Complex.dist_conj_conj z (x : ℂ)
    rwa [Complex.conj_ofReal] at this
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_ball] at hz ⊢
    rwa [hd]
  · intro hw
    refine ⟨conj w, ?_, Complex.conj_conj w⟩
    rw [mem_ball] at hw ⊢
    rwa [hd]

/-- **Local Schwarz reflection for unimodular boundary values.**  A holomorphic map of a half-disc centred on the real
axis into the unit disc with `|f| → 1` at every real point extends analytically across a smaller disc, and the
extension has modulus `< 1`, `= 1`, `> 1` exactly above, on, below the real axis. -/
theorem s31qc_unimodular_extension {f : ℂ → ℂ} {x ρ : ℝ} (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (ball (x : ℂ) ρ ∩ {z | 0 < z.im}))
    (hlt : ∀ z ∈ ball (x : ℂ) ρ ∩ {z | 0 < z.im}, ‖f z‖ < 1)
    (hlim : ∀ y : ℝ, |y - x| < ρ →
      Tendsto (fun z => ‖f z‖) (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ)) (𝓝 1)) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball (x : ℂ) ρ') ∧
      EqOn F f (ball (x : ℂ) ρ' ∩ {z | 0 < z.im}) ∧
      (∀ z ∈ ball (x : ℂ) ρ', (‖F z‖ < 1 ↔ 0 < z.im)) ∧
      (∀ z ∈ ball (x : ℂ) ρ', (‖F z‖ = 1 ↔ z.im = 0)) := by
  classical
  have h1 := hlim x (by simpa using hρ)
  have hev : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ), 1 / 2 < ‖f z‖ :=
    h1.eventually (lt_mem_nhds (by norm_num))
  obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  set ρ' : ℝ := min ε ρ with hρ'
  have hρ'pos : 0 < ρ' := lt_min hε hρ
  have hρ'ε : ρ' ≤ ε := min_le_left _ _
  have hρ'ρ : ρ' ≤ ρ := min_le_right _ _
  have hball : ball (x : ℂ) ρ' ⊆ ball (x : ℂ) ρ := ball_subset_ball hρ'ρ
  set U : Set ℂ := ball (x : ℂ) ρ' ∩ {z | 0 < z.im} with hU
  have hUo : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hUconv : Convex ℝ U := (convex_ball _ _).inter (convex_halfSpace_im_gt 0)
  have hUne : U.Nonempty := by
    refine ⟨(x : ℂ) + ((ρ' / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    · show 0 < ((x : ℂ) + ((ρ' / 2 : ℝ) : ℂ) * Complex.I).im
      simpa using hρ'pos
  have hUc : IsConnected U := hUconv.isConnected hUne
  haveI : ContractibleSpace U := hUconv.contractibleSpace hUne
  have hfU : DifferentiableOn ℂ f U := hf.mono (inter_subset_inter_left _ hball)
  have hne : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz h0
    have : 1 / 2 < ‖f z‖ := hεsub (lt_of_lt_of_le (mem_ball.1 hz.1) hρ'ε) hz.2
    rw [h0, norm_zero] at this
    linarith
  obtain ⟨h, hhd, hhe⟩ := RMT.exists_holomorphic_log_of_simplyConnected hUo hUc hfU hne
  have hre : ∀ z ∈ U, (h z).re = Real.log ‖f z‖ := by
    intro z hz
    have := congrArg norm (hhe z hz)
    rw [Complex.norm_exp] at this
    rw [← this, Real.log_exp]
  set g : ℂ → ℂ := fun z => Complex.I * h z with hg
  have hgd : DifferentiableOn ℂ g U := (differentiableOn_const _).mul hhd
  have hgim : ∀ z ∈ U, (g z).im = Real.log ‖f z‖ := by
    intro z hz
    rw [hg]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
    exact hre z hz
  have hsymm := s31qc_isRealSymmetric_ball x ρ'
  obtain ⟨G, hGd, hGeq⟩ := schwarz_reflection_segment_of_im_tendsto_zero hsymm
    (f := g) (show DifferentiableOn ℂ g (upperPart (ball (x : ℂ) ρ')) from hgd) (by
      intro y hy
      have hyim : y.im = 0 := hy.2
      have hy' : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using hyim)
      have hyb : |y.re - x| < ρ' := by
        have := hy.1
        rw [mem_ball, hy', Complex.dist_eq] at this
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
        exact this
      have hl := hlim y.re (lt_of_lt_of_le hyb hρ'ρ)
      rw [← hy'] at hl
      have hl2 : Tendsto (fun z => Real.log ‖f z‖) (𝓝[upperPart (ball (x : ℂ) ρ')] y) (𝓝 0) := by
        have hsub : 𝓝[upperPart (ball (x : ℂ) ρ')] y ≤ 𝓝[{z : ℂ | 0 < z.im}] y :=
          nhdsWithin_mono _ (fun z hz => hz.2)
        have := (hl.mono_left hsub).log one_ne_zero
        simpa using this
      refine hl2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hgim z hz).symm)
  set F : ℂ → ℂ := fun z => Complex.exp (-(Complex.I * G z)) with hF
  have hFd : DifferentiableOn ℂ F (ball (x : ℂ) ρ') :=
    (differentiableOn_const _ |>.mul hGd |>.neg).cexp
  have hFeq : EqOn F f U := by
    intro z hz
    have hGz : G z = g z := hGeq hz
    simp only [hF, hGz, hg]
    have : -(Complex.I * (Complex.I * h z)) = h z := by
      rw [← mul_assoc, Complex.I_mul_I]; ring
    rw [this, hhe z hz]
  refine ⟨ρ', hρ'pos, hρ'ρ, F, hFd, hFeq, ?_⟩
  -- unimodular on the real axis
  have hreal : ∀ y : ℂ, y ∈ ball (x : ℂ) ρ' → y.im = 0 → ‖F y‖ = 1 := by
    intro y hy hyim
    have hy' : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using hyim)
    have hyb : |y.re - x| < ρ' := by
      have := hy
      rw [mem_ball, hy', Complex.dist_eq] at this
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
      exact this
    have hl := hlim y.re (lt_of_lt_of_le hyb hρ'ρ)
    rw [← hy'] at hl
    have hFc : ContinuousAt F y := (hFd.differentiableAt (isOpen_ball.mem_nhds hy)).continuousAt
    have hl2 : Tendsto (fun z => ‖F z‖) (𝓝[{z : ℂ | 0 < z.im}] y) (𝓝 ‖F y‖) :=
      ((hFc.norm).tendsto).mono_left nhdsWithin_le_nhds
    have hl3 : Tendsto (fun z => ‖F z‖) (𝓝[{z : ℂ | 0 < z.im}] y) (𝓝 1) := by
      refine hl.congr' ?_
      have hmem : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] y, z ∈ ball (x : ℂ) ρ' :=
        eventually_nhdsWithin_of_eventually_nhds (isOpen_ball.mem_nhds hy)
      filter_upwards [hmem, self_mem_nhdsWithin] with z hz1 hz2
      exact (congrArg norm (hFeq ⟨hz1, hz2⟩)).symm
    haveI : (𝓝[{z : ℂ | 0 < z.im}] y).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, Complex.closure_setOf_lt_im]
      exact hyim.symm.le
    exact tendsto_nhds_unique hl2 hl3
  -- the symmetry `F z * conj (F (conj z)) = 1`
  have hconjball : ∀ z ∈ ball (x : ℂ) ρ', conj z ∈ ball (x : ℂ) ρ' := by
    intro z hz
    have : conj z ∈ conj '' ball (x : ℂ) ρ' := ⟨z, hz, rfl⟩
    rwa [show conj '' ball (x : ℂ) ρ' = ball (x : ℂ) ρ' from hsymm.conj_eq] at this
  set Φ : ℂ → ℂ := fun z => F z * conj (F (conj z)) with hΦ
  have hΦd : DifferentiableOn ℂ Φ (ball (x : ℂ) ρ') := by
    intro z hz
    have h1 : DifferentiableAt ℂ F z := hFd.differentiableAt (isOpen_ball.mem_nhds hz)
    have h2 : DifferentiableAt ℂ F (conj z) :=
      hFd.differentiableAt (isOpen_ball.mem_nhds (hconjball z hz))
    have h3 : DifferentiableAt ℂ (fun w => conj (F (conj w))) z := by
      simpa [Function.comp_def] using h2.conj_conj
    exact (h1.mul h3).differentiableWithinAt
  have hΦreal : ∀ z ∈ ball (x : ℂ) ρ', z.im = 0 → Φ z = 1 := by
    intro z hz hzim
    have hzc : conj z = z := Complex.conj_eq_iff_im.2 hzim
    simp only [hΦ, hzc]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hreal z hz hzim]
    simp
  have hΦone : EqOn Φ (fun _ => 1) (ball (x : ℂ) ρ') := by
    have hxm : (x : ℂ) ∈ ball (x : ℂ) ρ' := mem_ball_self hρ'pos
    refine (hΦd.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_frequently_eq
      (analyticOnNhd_const) (convex_ball _ _).isPreconnected hxm ?_
    have hT : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto x).mono_left nhdsWithin_le_nhds)
        (by filter_upwards [self_mem_nhdsWithin] with t ht
            simpa using ht)
    refine hT.frequently ?_
    have hev2 : ∀ᶠ t : ℝ in 𝓝[≠] x, (t : ℂ) ∈ ball (x : ℂ) ρ' :=
      eventually_nhdsWithin_of_eventually_nhds
        (Complex.continuous_ofReal.continuousAt.eventually (isOpen_ball.mem_nhds hxm))
    exact (hev2.mono fun t ht => hΦreal (t : ℂ) ht (by simp)).frequently
  have hlower : ∀ z ∈ ball (x : ℂ) ρ', z.im < 0 → 1 < ‖F z‖ := by
    intro z hz hzim
    have h1 : F z * conj (F (conj z)) = 1 := hΦone hz
    have hzc : conj z ∈ ball (x : ℂ) ρ' ∩ {w | 0 < w.im} :=
      ⟨hconjball z hz, by simpa using hzim⟩
    have h2 : ‖F (conj z)‖ < 1 := by
      rw [hFeq hzc]; exact hlt _ ⟨hball hzc.1, hzc.2⟩
    have h3 : ‖F z‖ * ‖F (conj z)‖ = 1 := by
      have := congrArg norm h1
      rwa [norm_mul, Complex.norm_conj, norm_one] at this
    have h4 : 0 < ‖F (conj z)‖ := by
      rcases (norm_nonneg (F (conj z))).lt_or_eq with h | h
      · exact h
      · rw [← h] at h3; simp at h3
    by_contra hcon
    rw [not_lt] at hcon
    nlinarith [norm_nonneg (F z)]
  refine ⟨fun z hz => ⟨fun hlt1 => ?_, fun hpos => ?_⟩, fun z hz => ⟨fun h1 => ?_, fun hz0 => hreal z hz hz0⟩⟩
  · by_contra hnp
    rw [not_lt] at hnp
    rcases hnp.lt_or_eq with h | h
    · linarith [hlower z hz h]
    · exact absurd (hreal z hz h) (ne_of_lt hlt1)
  · rw [hFeq ⟨hz, hpos⟩]
    exact hlt z ⟨hball hz, hpos⟩
  · by_contra hne0
    rcases lt_or_gt_of_ne hne0 with h | h
    · linarith [hlower z hz h]
    · rw [hFeq ⟨hz, h⟩] at h1
      linarith [hlt z ⟨hball hz, h⟩]

theorem s31qc_nebot_upper {z : ℂ} (hz : z.im = 0) : (𝓝[{w : ℂ | 0 < w.im}] z).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Complex.closure_setOf_lt_im]
  exact hz.symm.le

/-- Gluing the local reflections: a holomorphic injective map of a half disc into the unit disc with `|f| → 1` at
every real point extends continuously and injectively to the closed half disc, with the expected modulus pattern and
relatively open image. -/
theorem s31qc_halfdisc_extension {f₁ : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f₁ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hinj : InjOn f₁ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hlt : ∀ z ∈ {z : ℂ | ‖z‖ < r ∧ 0 < z.im}, ‖f₁ z‖ < 1)
    (hlim : ∀ y : ℝ, |y| < r →
      Tendsto (fun z => ‖f₁ z‖) (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ)) (𝓝 1)) :
    ∃ L : ℂ → ℂ, ContinuousOn L {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} ∧
      EqOn L f₁ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} ∧
      InjOn L {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} ∧
      (∀ z ∈ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im}, (‖L z‖ < 1 ↔ 0 < z.im)) ∧
      (∀ z ∈ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im}, (‖L z‖ = 1 ↔ z.im = 0)) ∧
      ∀ z ∈ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im}, ∃ N : Set ℂ, IsOpen N ∧ L z ∈ N ∧
        N ∩ closedBall 0 1 ⊆ L '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} := by
  classical
  set H : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 < z.im} with hH
  set Hb : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} with hHb
  have hHo : IsOpen H := (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hnorm_le : ∀ (t : ℝ) (z : ℂ), ‖z‖ ≤ ‖z - t‖ + |t| := by
    intro t z
    have h1 : ‖z‖ ≤ ‖z - t‖ + ‖(t : ℂ)‖ := by
      calc ‖z‖ = ‖(z - t) + t‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    rwa [Complex.norm_real, Real.norm_eq_abs] at h1
  -- local reflections at each real point
  have hloc : ∀ t : ℝ, ∃ ρ' : ℝ, ∃ F : ℂ → ℂ, |t| < r → (0 < ρ' ∧ ρ' ≤ r - |t| ∧
      DifferentiableOn ℂ F (ball (t : ℂ) ρ') ∧ EqOn F f₁ (ball (t : ℂ) ρ' ∩ {z | 0 < z.im}) ∧
      (∀ z ∈ ball (t : ℂ) ρ', (‖F z‖ < 1 ↔ 0 < z.im)) ∧
      (∀ z ∈ ball (t : ℂ) ρ', (‖F z‖ = 1 ↔ z.im = 0))) := by
    intro t
    by_cases ht : |t| < r
    · have hsub : ball (t : ℂ) (r - |t|) ⊆ ball (0 : ℂ) r := by
        intro z hz
        rw [mem_ball, Complex.dist_eq] at hz
        rw [mem_ball_zero_iff]
        linarith [hnorm_le t z]
      obtain ⟨ρ', hρ'0, hρ'le, F, hF⟩ := s31qc_unimodular_extension (f := f₁) (x := t) (ρ := r - |t|)
        (by linarith)
        (hd.mono fun z hz => ⟨mem_ball_zero_iff.1 (hsub hz.1), hz.2⟩)
        (fun z hz => hlt z ⟨mem_ball_zero_iff.1 (hsub hz.1), hz.2⟩)
        (fun y hy => hlim y (by
          have : |y| ≤ |y - t| + |t| := by
            calc |y| = |(y - t) + t| := by ring_nf
              _ ≤ _ := abs_add_le _ _
          linarith))
      exact ⟨ρ', F, fun _ => ⟨hρ'0, hρ'le, hF⟩⟩
    · exact ⟨1, fun _ => 0, fun h => absurd h ht⟩
  choose ρ' F hF using hloc
  have hsubr : ∀ t : ℝ, |t| < r → ball (t : ℂ) (ρ' t) ⊆ ball (0 : ℂ) r := by
    intro t ht z hz
    have hle := (hF t ht).2.1
    rw [mem_ball, Complex.dist_eq] at hz
    rw [mem_ball_zero_iff]
    linarith [hnorm_le t z]
  -- values agree on the real axis
  have hagree : ∀ t s : ℝ, |t| < r → |s| < r → ∀ z : ℂ, z ∈ ball (t : ℂ) (ρ' t) →
      z ∈ ball (s : ℂ) (ρ' s) → z.im = 0 → F t z = F s z := by
    intro t s ht hs z hzt hzs hzim
    haveI := s31qc_nebot_upper hzim
    have hlimit : ∀ u : ℝ, |u| < r → z ∈ ball (u : ℂ) (ρ' u) →
        Tendsto f₁ (𝓝[{w : ℂ | 0 < w.im}] z) (𝓝 (F u z)) := by
      intro u hu hzu
      have hFc : ContinuousAt (F u) z :=
        ((hF u hu).2.2.1.differentiableAt (isOpen_ball.mem_nhds hzu)).continuousAt
      refine (hFc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      have hmem : ∀ᶠ w in 𝓝[{w : ℂ | 0 < w.im}] z, w ∈ ball (u : ℂ) (ρ' u) :=
        eventually_nhdsWithin_of_eventually_nhds (isOpen_ball.mem_nhds hzu)
      filter_upwards [hmem, self_mem_nhdsWithin] with w hw1 hw2
      exact (hF u hu).2.2.2.1 ⟨hw1, hw2⟩
    exact tendsto_nhds_unique (hlimit t ht hzt) (hlimit s hs hzs)
  set L : ℂ → ℂ := fun z => if 0 < z.im then f₁ z else F z.re z with hL
  have hLH : EqOn L f₁ H := fun z hz => by simp only [hL, if_pos hz.2]
  have hrealpt : ∀ z : ℂ, z.im = 0 → z = ((z.re : ℝ) : ℂ) := fun z hz =>
    Complex.ext (by simp) (by simpa using hz)
  have hrealr : ∀ z : ℂ, ‖z‖ < r → |z.re| < r := fun z hz =>
    (Complex.abs_re_le_norm z).trans_lt hz
  have hcenter : ∀ z : ℂ, z.im = 0 → ‖z‖ < r → z ∈ ball ((z.re : ℝ) : ℂ) (ρ' z.re) := by
    intro z hzim hzr
    rw [← hrealpt z hzim]
    exact mem_ball_self (hF z.re (hrealr z hzr)).1
  -- near a real point `t`, `L = F t` on the closed half disc
  have hLF : ∀ t : ℝ, |t| < r → EqOn L (F t) (ball (t : ℂ) (ρ' t) ∩ Hb) := by
    intro t ht z hz
    by_cases hz0 : 0 < z.im
    · simp only [hL, if_pos hz0]
      exact ((hF t ht).2.2.2.1 ⟨hz.1, hz0⟩).symm
    · have hzim : z.im = 0 := le_antisymm (not_lt.1 hz0) hz.2.2
      simp only [hL, if_neg hz0]
      have hzn : ‖z‖ < r := hz.2.1
      exact (hagree z.re t (hrealr z hzn) ht z (hcenter z hzim hzn) hz.1 hzim)
  -- continuity
  have hcont : ContinuousOn L Hb := by
    intro z hz
    by_cases hz0 : 0 < z.im
    · have hzH : z ∈ H := ⟨hz.1, hz0⟩
      have : ContinuousAt L z := by
        refine ContinuousAt.congr (hd.continuousOn.continuousAt (hHo.mem_nhds hzH)) ?_
        filter_upwards [hHo.mem_nhds hzH] with w hw
        exact (hLH hw).symm
      exact this.continuousWithinAt
    · have hzim : z.im = 0 := le_antisymm (not_lt.1 hz0) hz.2
      have hzr := hrealr z hz.1
      have hzc := hcenter z hzim hz.1
      have hFc : ContinuousAt (F z.re) z :=
        ((hF z.re hzr).2.2.1.differentiableAt (isOpen_ball.mem_nhds hzc)).continuousAt
      refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
      · have hmem : ∀ᶠ w in 𝓝[Hb] z, w ∈ ball ((z.re : ℝ) : ℂ) (ρ' z.re) :=
          eventually_nhdsWithin_of_eventually_nhds (isOpen_ball.mem_nhds hzc)
        filter_upwards [hmem, self_mem_nhdsWithin] with w hw1 hw2
        exact hLF z.re hzr ⟨hw1, hw2⟩
      · exact hLF z.re hzr ⟨hzc, hz⟩
  -- modulus pattern
  have hmod : ∀ z ∈ Hb, (‖L z‖ < 1 ↔ 0 < z.im) ∧ (‖L z‖ = 1 ↔ z.im = 0) := by
    intro z hz
    by_cases hz0 : 0 < z.im
    · have hzH : z ∈ H := ⟨hz.1, hz0⟩
      rw [hLH hzH]
      have h1 := hlt z hzH
      exact ⟨⟨fun _ => hz0, fun _ => h1⟩, ⟨fun h => absurd h (ne_of_lt h1), fun h => absurd h hz0.ne'⟩⟩
    · have hzim : z.im = 0 := le_antisymm (not_lt.1 hz0) hz.2
      have hzr := hrealr z hz.1
      have hzc := hcenter z hzim hz.1
      have hLz : L z = F z.re z := by simp only [hL, if_neg hz0]
      rw [hLz]
      have h2 : ‖F z.re z‖ = 1 := ((hF z.re hzr).2.2.2.2.2 z hzc).2 hzim
      exact ⟨⟨fun h => absurd h (by rw [h2]; exact lt_irrefl _), fun h => absurd h hz0⟩,
        ⟨fun _ => hzim, fun _ => h2⟩⟩
  -- the open image near a real point
  have hopen : ∀ t : ℝ, |t| < r → ∀ δ : ℝ, 0 < δ → δ ≤ ρ' t →
      IsOpen (F t '' ball (t : ℂ) δ) ∧ F t t ∈ F t '' ball (t : ℂ) δ := by
    intro t ht δ hδ hδle
    have hF0 := hF t ht
    have hana : AnalyticOnNhd ℂ (F t) (ball (t : ℂ) (ρ' t)) := hF0.2.2.1.analyticOnNhd isOpen_ball
    have hnc : ¬ ∃ w, ∀ z ∈ ball (t : ℂ) (ρ' t), F t z = w := by
      rintro ⟨w, hw⟩
      have hm : (t : ℂ) ∈ ball (t : ℂ) (ρ' t) := mem_ball_self hF0.1
      have h0 : ‖F t t‖ = 1 := (hF0.2.2.2.2.2 t hm).2 (by simp)
      have hup : (t : ℂ) + ((ρ' t / 2 : ℝ) : ℂ) * Complex.I ∈ ball (t : ℂ) (ρ' t) := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hF0.1])]
        linarith [hF0.1]
      have h1 := (hF0.2.2.2.2.1 _ hup).2 (by simpa using hF0.1)
      have h2 := hw _ hup
      have h3 := hw _ hm
      rw [h3] at h0
      rw [h2] at h1
      linarith
    rcases hana.is_constant_or_isOpen (convex_ball _ _).isPreconnected with hc | hop
    · exact absurd hc hnc
    · exact ⟨hop _ (ball_subset_ball hδle) isOpen_ball, ⟨t, mem_ball_self hδ, rfl⟩⟩
  have hLreal : ∀ z : ℂ, z.im = 0 → ‖z‖ < r → L z = F z.re z := by
    intro z hzim hzn
    have hz0 : ¬ 0 < z.im := by rw [hzim]; exact lt_irrefl _
    simp only [hL, if_neg hz0]
  refine ⟨L, hcont, hLH, ?_, fun z hz => (hmod z hz).1, fun z hz => (hmod z hz).2, ?_⟩
  · -- injectivity
    intro a ha b hb hab
    by_cases ha0 : 0 < a.im
    · by_cases hb0 : 0 < b.im
      · rw [hLH ⟨ha.1, ha0⟩, hLH ⟨hb.1, hb0⟩] at hab
        exact hinj ⟨ha.1, ha0⟩ ⟨hb.1, hb0⟩ hab
      · have h1 := (hmod a ha).1.2 ha0
        have h2 := (hmod b hb).2.2 (le_antisymm (not_lt.1 hb0) hb.2)
        rw [hab] at h1
        linarith
    · by_cases hb0 : 0 < b.im
      · have h1 := (hmod b hb).1.2 hb0
        have h2 := (hmod a ha).2.2 (le_antisymm (not_lt.1 ha0) ha.2)
        rw [← hab] at h1
        linarith
      · -- two real points
        have haim : a.im = 0 := le_antisymm (not_lt.1 ha0) ha.2
        have hbim : b.im = 0 := le_antisymm (not_lt.1 hb0) hb.2
        by_contra hne
        have har := hrealr a ha.1
        have hbr := hrealr b hb.1
        have hne' : a.re ≠ b.re := by
          intro h
          exact hne (by rw [hrealpt a haim, hrealpt b hbim, h])
        have hpos : 0 < |a.re - b.re| := abs_pos.2 (sub_ne_zero.2 hne')
        set δ : ℝ := min (min (ρ' a.re) (ρ' b.re)) (|a.re - b.re| / 2) with hδ
        have hδpos : 0 < δ := lt_min (lt_min (hF a.re har).1 (hF b.re hbr).1) (by linarith)
        have hδa : δ ≤ ρ' a.re := (min_le_left _ _).trans (min_le_left _ _)
        have hδb : δ ≤ ρ' b.re := (min_le_left _ _).trans (min_le_right _ _)
        have hδab : δ ≤ |a.re - b.re| / 2 := min_le_right _ _
        obtain ⟨hoa, hma⟩ := hopen a.re har δ hδpos hδa
        obtain ⟨hob, hmb⟩ := hopen b.re hbr δ hδpos hδb
        have hLa : L a = F a.re a.re := by
          rw [hLreal a haim ha.1]
          rw [← hrealpt a haim]
        have hLb : L b = F b.re b.re := by
          rw [hLreal b hbim hb.1]
          rw [← hrealpt b hbim]
        set w : ℂ := L a with hw
        have hwn : ‖w‖ = 1 := ((hmod a ha).2).2 haim
        have hwb : w = F b.re b.re := hab.trans hLb
        have hwa : w = F a.re a.re := hLa
        have hNa : w ∈ F a.re '' ball ((a.re : ℝ) : ℂ) δ := by rw [hwa]; exact hma
        have hNb : w ∈ F b.re '' ball ((b.re : ℝ) : ℂ) δ := by rw [hwb]; exact hmb
        have hNo := hoa.inter hob
        obtain ⟨η, hη, hηsub⟩ := Metric.isOpen_iff.1 hNo w ⟨hNa, hNb⟩
        set ε : ℝ := min (η / 2) (1 / 2) with hε
        have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
        have hεη : ε < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hε1 : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
        set u : ℂ := ((1 - ε : ℝ) : ℂ) * w with hu
        have hdu : dist u w < η := by
          have : u - w = ((-ε : ℝ) : ℂ) * w := by rw [hu]; push_cast; ring
          rw [dist_eq_norm, this, norm_mul, hwn, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_neg, abs_of_pos hε0]
          exact hεη
        have hun : ‖u‖ < 1 := by
          rw [hu, norm_mul, hwn, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
          linarith
        obtain ⟨⟨c₁, hc₁, hc₁u⟩, ⟨c₂, hc₂, hc₂u⟩⟩ := hηsub (mem_ball.2 hdu)
        have hc₁' : c₁ ∈ ball ((a.re : ℝ) : ℂ) (ρ' a.re) := ball_subset_ball hδa hc₁
        have hc₂' : c₂ ∈ ball ((b.re : ℝ) : ℂ) (ρ' b.re) := ball_subset_ball hδb hc₂
        have hc₁up : 0 < c₁.im := ((hF a.re har).2.2.2.2.1 c₁ hc₁').1 (by rw [hc₁u]; exact hun)
        have hc₂up : 0 < c₂.im := ((hF b.re hbr).2.2.2.2.1 c₂ hc₂').1 (by rw [hc₂u]; exact hun)
        have hH₁ : c₁ ∈ H := ⟨mem_ball_zero_iff.1 (hsubr a.re har hc₁'), hc₁up⟩
        have hH₂ : c₂ ∈ H := ⟨mem_ball_zero_iff.1 (hsubr b.re hbr hc₂'), hc₂up⟩
        have e1 : F a.re c₁ = f₁ c₁ := (hF a.re har).2.2.2.1 ⟨hc₁', hc₁up⟩
        have e2 : F b.re c₂ = f₁ c₂ := (hF b.re hbr).2.2.2.1 ⟨hc₂', hc₂up⟩
        have hc12 : c₁ = c₂ := hinj hH₁ hH₂ (by rw [← e1, ← e2, hc₁u, hc₂u])
        have d1 : dist c₁ ((a.re : ℝ) : ℂ) < δ := mem_ball.1 hc₁
        have d2 : dist c₁ ((b.re : ℝ) : ℂ) < δ := by rw [hc12]; exact mem_ball.1 hc₂
        have hdd : dist ((a.re : ℝ) : ℂ) ((b.re : ℝ) : ℂ) < 2 * δ := by
          calc dist ((a.re : ℝ) : ℂ) ((b.re : ℝ) : ℂ)
              ≤ dist ((a.re : ℝ) : ℂ) c₁ + dist c₁ ((b.re : ℝ) : ℂ) := dist_triangle _ _ _
            _ = dist c₁ ((a.re : ℝ) : ℂ) + dist c₁ ((b.re : ℝ) : ℂ) := by rw [dist_comm ((a.re : ℝ) : ℂ) c₁]
            _ < δ + δ := add_lt_add d1 d2
            _ = 2 * δ := by ring
        rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hdd
        linarith
  · intro z0 hz0
    by_cases hz0up : 0 < z0.im
    · -- an interior point: open mapping for the injective holomorphic `f₁`
      have hzH : z0 ∈ H := ⟨hz0.1, hz0up⟩
      obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hHo z0 hzH
      have hana : AnalyticOnNhd ℂ f₁ (ball z0 ρ) :=
        (hd.mono hρsub).analyticOnNhd isOpen_ball
      have hnc : ¬ ∃ w, ∀ z ∈ ball z0 ρ, f₁ z = w := by
        rintro ⟨w, hw⟩
        have hm : z0 + ((ρ / 2 : ℝ) : ℂ) ∈ ball z0 ρ := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith)]
          linarith
        have h1 := hinj (hρsub (mem_ball_self hρ)) (hρsub hm) ((hw _ (mem_ball_self hρ)).trans (hw _ hm).symm)
        have : ((ρ / 2 : ℝ) : ℂ) = 0 := by
          have := congrArg (fun c => c - z0) h1.symm
          simpa using this
        have : ρ / 2 = 0 := by exact_mod_cast this
        linarith
      rcases hana.is_constant_or_isOpen (convex_ball _ _).isPreconnected with hc | hop
      · exact absurd hc hnc
      · refine ⟨f₁ '' ball z0 ρ, hop _ subset_rfl isOpen_ball, ⟨z0, mem_ball_self hρ, (hLH hzH).symm⟩, ?_⟩
        rintro w ⟨⟨c, hc, rfl⟩, -⟩
        exact ⟨c, ⟨(hρsub hc).1, (hρsub hc).2.le⟩, hLH (hρsub hc)⟩
    · have hz0im : z0.im = 0 := le_antisymm (not_lt.1 hz0up) hz0.2
      have hy : |z0.re| < r := hrealr z0 hz0.1
      obtain ⟨hoy, hmy⟩ := hopen z0.re hy (ρ' z0.re) (hF z0.re hy).1 le_rfl
      have hm : z0 ∈ ball ((z0.re : ℝ) : ℂ) (ρ' z0.re) := hcenter z0 hz0im hz0.1
      refine ⟨F z0.re '' ball ((z0.re : ℝ) : ℂ) (ρ' z0.re), hoy, ?_, ?_⟩
      · rw [hLreal z0 hz0im hz0.1]
        exact ⟨z0, hm, rfl⟩
      · rintro w ⟨⟨c, hc, rfl⟩, hw⟩
        have hF0 := hF z0.re hy
        have hle : ‖F z0.re c‖ ≤ 1 := by simpa using hw
        have hc0 : 0 ≤ c.im := by
          rcases hle.lt_or_eq with h | h
          · exact ((hF0.2.2.2.2.1 c hc).1 h).le
          · exact ((hF0.2.2.2.2.2 c hc).1 h).ge
        have hcn : ‖c‖ < r := mem_ball_zero_iff.1 (hsubr z0.re hy hc)
        exact ⟨c, ⟨hcn, hc0⟩, hLF z0.re hy ⟨hc, ⟨hcn, hc0⟩⟩⟩

/-- A homeomorphism of the closed exterior onto the closed disc: if `g` tends to a closed subset `C` of the
boundary set, the modulus of `e (g a)` tends to `1`. -/
theorem s31qc_norm_tendsto_one {α : Type*} {l : Filter α} {K C : Set ExtPlane} [DecidablePred (· ∈ K)]
    (e : ↥K ≃ₜ closedBall (0 : ℂ) 1) {g : α → ExtPlane}
    (hg : Tendsto g l (𝓝ˢ C)) (hgK : ∀ᶠ a in l, g a ∈ K) (hCK : C ⊆ K)
    (hCe : ∀ (p : ExtPlane) (hp : p ∈ K), p ∈ C → ‖(e ⟨p, hp⟩).val‖ = 1) :
    Tendsto (fun a => if h : g a ∈ K then ‖(e ⟨g a, h⟩).val‖ else 1) l (𝓝 1) := by
  classical
  refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' => ?_⟩
  · -- lower bound
    set W : Set ↥K := {p | a' < ‖(e p).val‖} with hW
    have hWo : IsOpen W :=
      isOpen_lt continuous_const (continuous_norm.comp (continuous_subtype_val.comp e.continuous))
    obtain ⟨O, hOo, hOW⟩ := isOpen_induced_iff.1 hWo
    have hCO : C ⊆ O := by
      intro p hp
      have : (⟨p, hCK hp⟩ : ↥K) ∈ W := by
        show a' < ‖(e ⟨p, hCK hp⟩).val‖
        rw [hCe p (hCK hp) hp]; exact ha'
      rw [← hOW] at this
      exact this
    have hev : ∀ᶠ a in l, g a ∈ O := hg (hOo.mem_nhdsSet.2 hCO)
    filter_upwards [hev, hgK] with a ha1 ha2
    rw [dif_pos ha2]
    have : (⟨g a, ha2⟩ : ↥K) ∈ Subtype.val ⁻¹' O := ha1
    rw [hOW] at this
    exact this
  · refine Eventually.of_forall fun a => ?_
    by_cases h : g a ∈ K
    · rw [dif_pos h]
      have := (e ⟨g a, h⟩).property
      rw [mem_closedBall_zero_iff] at this
      exact lt_of_le_of_lt this ha'
    · rw [dif_neg h]; exact ha'

/-- Boundary behaviour of the collar map: a holomorphic injective map of a half disc into the exterior of a bounded
Jordan domain, accumulating only on its boundary at the real segment, extends to a homeomorphism of the closed half
disc onto a relatively open subset of the closed exterior, the segment going to the boundary curve. -/
theorem s31qc_collar_boundary {Jd : Set ℂ} (hJd : IsJordanDomain Jd) (hb : Bornology.IsBounded Jd)
    {r : ℝ} (hr : 0 < r) {κ₀ : ℂ → ℂ}
    (hd : DifferentiableOn ℂ κ₀ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hinj : InjOn κ₀ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hmaps : MapsTo κ₀ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (closure Jd)ᶜ)
    (hbdry : ∀ y : ℝ, |y| < r → Tendsto (fun z => ((κ₀ z : ℂ) : ExtPlane))
      (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ)) (𝓝ˢ (frontier (toExt Jd)))) :
    ∃ κ : ℂ → ℂ, ContinuousOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} ∧
      EqOn κ κ₀ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} ∧ InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} ∧
      MapsTo κ {z : ℂ | ‖z‖ < r ∧ z.im = 0} (frontier Jd) ∧
      ∃ V : Set ℂ, IsOpen V ∧ κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} = V ∩ Jdᶜ := by
  classical
  obtain ⟨f, e, hfd, hfi, hef, hei, heb⟩ := s78ra_exterior_closed_coordinate hJd hb
  set H : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 < z.im} with hH
  set Hb : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} with hHb
  have hJo : IsOpen Jd := hJd.1
  have hclos : closure (toExt Jd) = toExt (closure Jd) := closure_toExt_of_isBounded' hb
  have hfront : frontier (toExt Jd) = toExt (frontier Jd) := frontier_toExt_of_isBounded' hb hJo
  have hcoe_mem : ∀ (w : ℂ) (S : Set ℂ), ((w : ℂ) : ExtPlane) ∈ toExt S ↔ w ∈ S := fun w S =>
    ⟨fun ⟨c, hc, hcw⟩ => by rw [← OnePoint.coe_injective hcw]; exact hc, fun h => ⟨w, h, rfl⟩⟩
  have hnotcl : ∀ w : ℂ, w ∈ (closure Jd)ᶜ → ((w : ℂ) : ExtPlane) ∈ ((toExt Jd)ᶜ) := by
    intro w hw h
    exact hw (subset_closure ((hcoe_mem w Jd).1 h))
  have hnotcl' : ∀ w : ℂ, w ∈ (closure Jd)ᶜ → ((w : ℂ) : ExtPlane) ∈ (closure (toExt Jd))ᶜ := by
    intro w hw h
    rw [hclos] at h
    exact hw ((hcoe_mem w _).1 h)
  -- the composite `f ∘ κ₀`
  set f₁ : ℂ → ℂ := fun z => f (κ₀ z) with hf₁
  have hf₁d : DifferentiableOn ℂ f₁ H := hfd.comp hd hmaps
  have hf₁i : InjOn f₁ H := hfi.comp hinj hmaps
  have hval : ∀ z (hz : z ∈ H), f₁ z = (e ⟨((κ₀ z : ℂ) : ExtPlane), hnotcl _ (hmaps hz)⟩).val := by
    intro z hz
    exact (hef (κ₀ z) (hmaps hz) (hnotcl _ (hmaps hz))).symm
  have hf₁lt : ∀ z ∈ H, ‖f₁ z‖ < 1 := by
    intro z hz
    rw [hval z hz]
    exact (hei ⟨((κ₀ z : ℂ) : ExtPlane), hnotcl _ (hmaps hz)⟩).2 (hnotcl' _ (hmaps hz))
  have hopenK : IsOpen (toExt Jd) := isOpen_toExt_iff.2 hJo
  have hCK : frontier (toExt Jd) ⊆ ((toExt Jd)ᶜ) := fun p hp => by
    rw [hopenK.frontier_eq] at hp
    exact hp.2
  have hCe : ∀ (p : ExtPlane) (hp : p ∈ ((toExt Jd)ᶜ)), p ∈ frontier (toExt Jd) → ‖(e ⟨p, hp⟩).val‖ = 1 :=
    fun p hp hpC => (heb ⟨p, hp⟩).2 hpC
  have hlim : ∀ y : ℝ, |y| < r →
      Tendsto (fun z => ‖f₁ z‖) (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ)) (𝓝 1) := by
    intro y hy
    have hyn : ‖(y : ℂ)‖ < r := by simpa [Complex.norm_real] using hy
    have hH' : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (y : ℂ), z ∈ H := by
      have : ∀ᶠ z in 𝓝 (y : ℂ), ‖z‖ < r :=
        (isOpen_lt continuous_norm continuous_const).mem_nhds hyn
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds this, self_mem_nhdsWithin] with z h1 h2
      exact ⟨h1, h2⟩
    have hgK : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (y : ℂ), ((κ₀ z : ℂ) : ExtPlane) ∈ ((toExt Jd)ᶜ) :=
      hH'.mono fun z hz => hnotcl _ (hmaps hz)
    have := s31qc_norm_tendsto_one e (hbdry y hy) hgK hCK hCe
    refine this.congr' ?_
    filter_upwards [hH'] with z hz
    rw [dif_pos (hnotcl _ (hmaps hz)), hval z hz]
  obtain ⟨L, hLc, hLeq, hLi, hLlt, hLone, hLopen⟩ :=
    s31qc_halfdisc_extension hr hf₁d hf₁i hf₁lt hlim
  have hLle : ∀ z ∈ Hb, ‖L z‖ ≤ 1 := by
    intro z hz
    by_cases h : 0 < z.im
    · exact ((hLlt z hz).2 h).le
    · exact ((hLone z hz).2 (le_antisymm (not_lt.1 h) hz.2)).le
  set g : ↥Hb → closedBall (0 : ℂ) 1 :=
    fun z => ⟨L z, mem_closedBall_zero_iff.2 (hLle z z.2)⟩ with hg
  have hgc : Continuous g := Continuous.subtype_mk hLc.restrict _
  set Eb : ↥Hb → ↥((toExt Jd)ᶜ) := fun z => e.symm (g z) with hEb
  have hEbc : Continuous Eb := e.symm.continuous.comp hgc
  have hge : ∀ z : ↥Hb, e (Eb z) = g z := fun z => e.apply_symm_apply _
  have hupper : ∀ z : ↥Hb, 0 < (z : ℂ).im → (Eb z).val = ((κ₀ z : ℂ) : ExtPlane) := by
    intro z hz
    have hzH : (z : ℂ) ∈ H := ⟨z.2.1, hz⟩
    have : Eb z = ⟨((κ₀ z : ℂ) : ExtPlane), hnotcl _ (hmaps hzH)⟩ := by
      apply e.injective
      rw [hge]
      apply Subtype.ext
      show L z = _
      rw [hLeq hzH, hval _ hzH]
    rw [this]
  have hrealpt : ∀ z : ↥Hb, (z : ℂ).im = 0 → (Eb z).val ∈ toExt (frontier Jd) := by
    intro z hz
    rw [← hfront]
    apply (heb (Eb z)).1
    rw [hge]
    exact (hLone z z.2).2 hz
  have hex : ∀ z : ↥Hb, ∃ c : ℂ, ((c : ℂ) : ExtPlane) = (Eb z).val := by
    intro z
    by_cases h : 0 < (z : ℂ).im
    · exact ⟨κ₀ z, (hupper z h).symm⟩
    · obtain ⟨c, hc, hcz⟩ := hrealpt z (le_antisymm (not_lt.1 h) z.2.2)
      exact ⟨c, hcz⟩
  choose κ' hκ' using hex
  set κ : ℂ → ℂ := fun z => if h : z ∈ Hb then κ' ⟨z, h⟩ else 0 with hκ
  have hκz : ∀ z : ↥Hb, κ z = κ' z := fun z => by simp only [hκ, dif_pos z.2]
  have hκe : ∀ z : ↥Hb, ((κ z : ℂ) : ExtPlane) = (Eb z).val := fun z => by rw [hκz]; exact hκ' z
  have hKz : ∀ z : ↥Hb, κ z ∉ Jd := by
    intro z h
    have : (Eb z).val ∈ toExt Jd := by rw [← hκe z]; exact (hcoe_mem _ _).2 h
    exact (Eb z).property this
  have hloc : ∀ z : ↥Hb, ∃ U : Set ℂ, IsOpen U ∧ κ z ∈ U ∧ U ∩ Jdᶜ ⊆ κ '' Hb := by
    intro z
    obtain ⟨N, hNo, hzN, hNsub⟩ := hLopen z z.2
    set O₀ : Set ↥((toExt Jd)ᶜ) := {p | (e p).val ∈ N} with hO₀
    have hO₀o : IsOpen O₀ := hNo.preimage (continuous_subtype_val.comp e.continuous)
    obtain ⟨O, hOo, hOO⟩ := isOpen_induced_iff.1 hO₀o
    refine ⟨(fun c : ℂ => (c : ExtPlane)) ⁻¹' O, hOo.preimage OnePoint.continuous_coe, ?_, ?_⟩
    · show ((κ z : ℂ) : ExtPlane) ∈ O
      have : Eb z ∈ Subtype.val ⁻¹' O := by
        rw [hOO]
        show (e (Eb z)).val ∈ N
        rw [hge]
        exact hzN
      rw [hκe]
      exact this
    · rintro c ⟨hcU, hcJ⟩
      have hcK : ((c : ℂ) : ExtPlane) ∈ ((toExt Jd)ᶜ) := fun h => hcJ ((hcoe_mem c _).1 h)
      have h1 : (⟨(c : ExtPlane), hcK⟩ : ↥((toExt Jd)ᶜ)) ∈ Subtype.val ⁻¹' O := hcU
      rw [hOO] at h1
      have h2 : (e ⟨(c : ExtPlane), hcK⟩).val ∈ N := h1
      have h3 : (e ⟨(c : ExtPlane), hcK⟩).val ∈ N ∩ closedBall 0 1 := ⟨h2, (e _).property⟩
      obtain ⟨w, hw, hLw⟩ := hNsub h3
      refine ⟨w, hw, ?_⟩
      have hEw : Eb ⟨w, hw⟩ = ⟨(c : ExtPlane), hcK⟩ := by
        apply e.injective
        rw [hge]
        apply Subtype.ext
        exact hLw
      apply OnePoint.coe_injective
      rw [hκz ⟨w, hw⟩] at *
      have := hκe ⟨w, hw⟩
      rw [hκz] at this
      rw [this, hEw]
  choose Uz hUo hUz hUsub using hloc
  refine ⟨κ, ?_, ?_, ?_, ?_, ⟨⋃ z : ↥Hb, Uz z, isOpen_iUnion hUo, ?_⟩⟩
  · rw [continuousOn_iff_continuous_restrict]
    have : Continuous (fun z : ↥Hb => ((κ z : ℂ) : ExtPlane)) := by
      have h := continuous_subtype_val.comp hEbc
      convert h using 1
      funext z
      exact hκe z
    exact OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff.2 this
  · intro z hz
    have hzb : z ∈ Hb := ⟨hz.1, hz.2.le⟩
    apply OnePoint.coe_injective
    rw [hκe ⟨z, hzb⟩]
    exact hupper ⟨z, hzb⟩ hz.2
  · intro a ha b hb hab
    have h1 := hκe ⟨a, ha⟩
    have h2 := hκe ⟨b, hb⟩
    have hE : Eb ⟨a, ha⟩ = Eb ⟨b, hb⟩ := Subtype.ext (by rw [← h1, ← h2]; exact congrArg _ hab)
    have hgab : g ⟨a, ha⟩ = g ⟨b, hb⟩ := by
      have := congrArg e hE
      rwa [hge, hge] at this
    exact hLi ha hb (congrArg Subtype.val hgab)
  · intro z hz
    have hzb : z ∈ Hb := ⟨hz.1, hz.2.ge⟩
    have := hrealpt ⟨z, hzb⟩ hz.2
    rw [← hκe ⟨z, hzb⟩] at this
    exact (hcoe_mem _ _).1 this
  · ext c
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨mem_iUnion.2 ⟨⟨z, hz⟩, hUz ⟨z, hz⟩⟩, hKz ⟨z, hz⟩⟩
    · rintro ⟨hcV, hcJ⟩
      obtain ⟨z, hcz⟩ := mem_iUnion.1 hcV
      exact hUsub z ⟨hcz, hcJ⟩


/-- Local holomorphic chart at a fixed point of an anticonformal involution, in which the involution is complex
conjugation; the chart is defined on a ball and sits inside a prescribed neighbourhood. -/
theorem s31qc_fixed_chart_local {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {J : X ≃ₜ X} (hJ : IsAnticonformalInvolution J) {p₀ : X} (hp₀ : J p₀ = p₀)
    {U : Set X} (hU : U ∈ 𝓝 p₀) :
    ∃ (wc : OpenPartialHomeomorph X ℂ) (r : ℝ), 0 < r ∧ p₀ ∈ wc.source ∧ wc p₀ = 0 ∧
      wc.target = ball 0 r ∧ wc.source ⊆ U ∧
      (∀ p ∈ wc.source, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc p) ∧
      (∀ z ∈ wc.target, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc.symm z) ∧
      (∀ p ∈ wc.source, J p ∈ wc.source ∧ wc (J p) = conj (wc p)) := by
  obtain ⟨e, he1, he2, hea, hesa, hident⟩ := s78ra_given_involution_fixed_coordinate J hJ p₀ hp₀
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ p₀ with hc
  set z₀ : ℂ := c p₀ with hz₀
  have hps : p₀ ∈ c.source := mem_chart_source ℂ p₀
  have hz₀t : z₀ ∈ c.target := c.map_source hps
  have hcs : c.symm z₀ = p₀ := c.left_inv hps
  have hle : localMapExpr J p₀ = fun w => c (J (c.symm w)) := by
    funext w
    simp only [localMapExpr, hp₀]
    rfl
  -- continuity of `J ∘ c.symm` and of `localMapExpr` at `z₀`
  have hJc : ContinuousAt (fun w => J (c.symm w)) z₀ :=
    J.continuous.continuousAt.comp (c.continuousAt_symm hz₀t)
  have hJc0 : J (c.symm z₀) = p₀ := by rw [hcs, hp₀]
  have hcJ : ContinuousAt c (J (c.symm z₀)) := by
    rw [hJc0]; exact c.continuousAt hps
  have hlc : ContinuousAt (localMapExpr J p₀) z₀ := by
    rw [hle]
    exact ContinuousAt.comp (g := c) (f := fun w => J (c.symm w)) hcJ hJc
  have hlz : localMapExpr J p₀ z₀ = z₀ := by
    rw [hle]
    show c (J (c.symm z₀)) = z₀
    rw [hJc0]
  -- eventual properties at `z₀`
  have hP1 : ∀ᶠ w in 𝓝 z₀, w ∈ c.target := c.open_target.mem_nhds hz₀t
  have hP2 : ∀ᶠ w in 𝓝 z₀, w ∈ e.source := e.open_source.mem_nhds he1
  have hP3 : ∀ᶠ w in 𝓝 z₀, AnalyticAt ℂ e w := hea.eventually_analyticAt
  have hP4 : ∀ᶠ w in 𝓝 z₀, e (localMapExpr J p₀ w) = conj (e w) := hident
  have hP5 : ∀ᶠ w in 𝓝 z₀, localMapExpr J p₀ w ∈ e.source := by
    refine hlc.eventually (e.open_source.mem_nhds ?_)
    rw [hlz]; exact he1
  have hP6 : ∀ᶠ w in 𝓝 z₀, c.symm w ∈ U := by
    refine (c.continuousAt_symm hz₀t).eventually ?_
    rw [hcs]; exact hU
  have hP7 : ∀ᶠ w in 𝓝 z₀, J (c.symm w) ∈ c.source := by
    refine hJc.eventually (c.open_source.mem_nhds ?_)
    show J (c.symm z₀) ∈ c.source
    rw [hJc0]; exact hps
  set Q : ℂ → Prop := fun w => w ∈ c.target ∧ w ∈ e.source ∧ AnalyticAt ℂ e w ∧
      e (localMapExpr J p₀ w) = conj (e w) ∧ localMapExpr J p₀ w ∈ e.source ∧ c.symm w ∈ U ∧
      J (c.symm w) ∈ c.source with hQ
  have hN : ∀ᶠ w in 𝓝 z₀, Q w :=
    hP1.and (hP2.and (hP3.and (hP4.and (hP5.and (hP6.and hP7)))))
  have he0 : e.symm 0 = z₀ := by
    rw [← he2]; exact e.left_inv he1
  have hT : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ e.target ∧ AnalyticAt ℂ e.symm z ∧ Q (e.symm z) := by
    have h0 : (0 : ℂ) ∈ e.target := by rw [← he2]; exact e.map_source he1
    have h0' : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ e.target := e.open_target.mem_nhds h0
    refine h0'.and (hesa.eventually_analyticAt.and ?_)
    have hcont : ContinuousAt e.symm 0 := e.continuousAt_symm h0
    refine hcont.eventually (p := Q) ?_
    rw [he0]; exact hN
  obtain ⟨r, hr, hrT⟩ := Metric.eventually_nhds_iff_ball.1 hT
  set φ : OpenPartialHomeomorph X ℂ := (c.trans e).trans (OpenPartialHomeomorph.ofSet (ball (0 : ℂ) r) isOpen_ball)
    with hφ
  have hφapp : ∀ p, φ p = e (c p) := fun p => rfl
  have hφsymm : ∀ z, φ.symm z = c.symm (e.symm z) := fun z => rfl
  have hφs : φ.source = {p | p ∈ c.source ∧ c p ∈ e.source ∧ e (c p) ∈ ball (0 : ℂ) r} := by
    ext p
    simp only [hφ, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.ofSet_source,
      OpenPartialHomeomorph.trans_apply, mem_inter_iff, mem_preimage, mem_setOf_eq]
    tauto
  have hφt : φ.target = ball (0 : ℂ) r := by
    ext z
    simp only [hφ, OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.ofSet_target,
      mem_inter_iff, mem_preimage]
    constructor
    · intro h; exact h.1
    · intro hz
      obtain ⟨hzT, -, hz2⟩ := hrT z hz
      refine ⟨hz, ?_⟩
      simp only [OpenPartialHomeomorph.ofSet_symm, OpenPartialHomeomorph.refl_apply, id_eq,
        OpenPartialHomeomorph.trans_target, mem_inter_iff, mem_preimage]
      exact ⟨hzT, hz2.1⟩
  refine ⟨φ, r, hr, ?_, ?_, hφt, ?_, ?_, ?_, ?_⟩
  · rw [hφs]
    refine ⟨hps, he1, ?_⟩
    show e z₀ ∈ ball (0 : ℂ) r
    rw [he2]; exact mem_ball_self hr
  · rw [hφapp]; exact he2
  · intro p hp
    rw [hφs] at hp
    have : φ.symm (φ p) = p := φ.left_inv (by rw [hφs]; exact hp)
    rw [← this, hφsymm]
    exact (hrT _ hp.2.2).2.2.2.2.2.2.2.1
  · intro p hp
    rw [hφs] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    have hcp : c.symm (c p) = p := c.left_inv h1
    have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c p :=
      ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := p₀)).mdifferentiableOn (by simp) p h1).mdifferentiableAt
        (c.open_source.mem_nhds h1)
    have hz : (c p) = e.symm (e (c p)) := (e.left_inv h2).symm
    have hae : AnalyticAt ℂ e (c p) := by
      have := (hrT _ h3).2.2.2.2.1
      rwa [← hz] at this
    exact (hae.differentiableAt.mdifferentiableAt).comp p hmd
  · intro z hz
    rw [hφt] at hz
    obtain ⟨hzT, hzA, hz2⟩ := hrT z hz
    have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c.symm (e.symm z) :=
      ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := p₀)).mdifferentiableOn (by simp) _
        hz2.1).mdifferentiableAt (c.open_target.mem_nhds hz2.1)
    exact hmd.comp z (hzA.differentiableAt.mdifferentiableAt)
  · intro p hp
    rw [hφs] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    obtain ⟨hzT, -, hz2⟩ := hrT _ h3
    have hw : e.symm (e (c p)) = c p := e.left_inv h2
    rw [hw] at hz2
    obtain ⟨-, -, -, h4, h5, -, h7⟩ := hz2
    have hcp : c.symm (c p) = p := c.left_inv h1
    rw [hcp] at h7
    have hloc : localMapExpr J p₀ (c p) = c (J p) := by
      rw [hle]; simp only [hcp]
    rw [hloc] at h4 h5
    have hcn : ‖conj (e (c p))‖ < r := by
      rw [Complex.norm_conj]; exact mem_ball_zero_iff.1 h3
    refine ⟨?_, ?_⟩
    · rw [hφs]
      exact ⟨h7, h5, by rw [h4]; exact mem_ball_zero_iff.2 hcn⟩
    · rw [hφapp, hφapp]; exact h4

/-- Negating a chart of the fixed-point coordinate type gives another one, with the same domain and target. -/
theorem s31qc_chart_neg {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {J : X ≃ₜ X} {p₀ : X} {U : Set X} {wc : OpenPartialHomeomorph X ℂ} {r : ℝ}
    (h1 : p₀ ∈ wc.source) (h2 : wc p₀ = 0) (h3 : wc.target = ball 0 r) (h4 : wc.source ⊆ U)
    (h5 : ∀ p ∈ wc.source, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc p)
    (h6 : ∀ z ∈ wc.target, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc.symm z)
    (h7 : ∀ p ∈ wc.source, J p ∈ wc.source ∧ wc (J p) = conj (wc p)) :
    ∃ wc' : OpenPartialHomeomorph X ℂ, wc'.source = wc.source ∧ p₀ ∈ wc'.source ∧ wc' p₀ = 0 ∧
      wc'.target = ball 0 r ∧ wc'.source ⊆ U ∧
      (∀ p ∈ wc'.source, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc' p) ∧
      (∀ z ∈ wc'.target, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc'.symm z) ∧
      (∀ p ∈ wc'.source, J p ∈ wc'.source ∧ wc' (J p) = conj (wc' p)) ∧
      (∀ p ∈ wc'.source, wc' p = - wc p) := by
  set N : OpenPartialHomeomorph ℂ ℂ := (Homeomorph.neg ℂ).toOpenPartialHomeomorph with hN
  set w : OpenPartialHomeomorph X ℂ := wc.trans N with hw
  have hwapp : ∀ p, w p = - wc p := fun p => rfl
  have hwsymm : ∀ z, w.symm z = wc.symm (-z) := fun z => rfl
  have hws : w.source = wc.source := by
    simp only [hw, OpenPartialHomeomorph.trans_source, hN, Homeomorph.toOpenPartialHomeomorph_source,
      preimage_univ, inter_univ]
  have hwt : w.target = ball 0 r := by
    ext z
    show (z ∈ N.target ∧ N.symm z ∈ wc.target) ↔ z ∈ ball (0 : ℂ) r
    have hNz : N.symm z = -z := rfl
    rw [hNz, h3, mem_ball_zero_iff, mem_ball_zero_iff, norm_neg]
    exact ⟨fun h => h.2, fun h => ⟨show z ∈ univ from trivial, h⟩⟩
  refine ⟨w, hws, ?_, ?_, hwt, ?_, ?_, ?_, ?_, fun p _ => hwapp p⟩
  · rw [hws]; exact h1
  · rw [hwapp, h2, neg_zero]
  · rw [hws]; exact h4
  · intro p hp
    rw [hws] at hp
    have : ⇑w = fun p => -(wc p) := funext hwapp
    rw [this]
    exact (h5 p hp).neg
  · intro z hz
    rw [hwt] at hz
    have : ⇑w.symm = fun z => wc.symm (-z) := funext hwsymm
    rw [this]
    have hz' : -z ∈ wc.target := by
      rw [h3, mem_ball_zero_iff, norm_neg]; exact mem_ball_zero_iff.1 hz
    exact (h6 (-z) hz').comp z (differentiableAt_id.neg.mdifferentiableAt)
  · intro p hp
    rw [hws] at hp
    obtain ⟨hJ1, hJ2⟩ := h7 p hp
    refine ⟨by rw [hws]; exact hJ1, ?_⟩
    rw [hwapp, hwapp, hJ2, map_neg]

theorem s31qc_sides_dichotomy {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    {F : FiniteTypeStructure S g n m} {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {wc : OpenPartialHomeomorph Xd.carrier ℂ} {r : ℝ} (h3 : wc.target = ball 0 r)
    (h4 : wc.source ⊆ (↑Pd : Set Xd.carrier)ᶜ)
    (h7 : ∀ p ∈ wc.source, J p ∈ wc.source ∧ wc (J p) = conj (wc p)) :
    (∀ p ∈ wc.source, 0 < (wc p).im → p ∈ range ιd) ∨
      (∀ p ∈ wc.source, (wc p).im < 0 → p ∈ range ιd) := by
  have hfix : ∀ p ∈ wc.source, J p = p → (wc p).im = 0 := by
    intro p hp hJp
    have := (h7 p hp).2
    rw [hJp] at this
    exact Complex.conj_eq_iff_im.1 this.symm
  set A : Set Xd.carrier := wc.symm '' ((ball (0 : ℂ) r) ∩ {z | 0 < z.im}) with hA
  have hApre : IsPreconnected A := by
    refine IsPreconnected.image ?_ _ (wc.continuousOn_symm.mono ?_)
    · exact ((convex_ball (0 : ℂ) r).inter (convex_halfSpace_im_gt 0)).isPreconnected
    · rw [h3]; exact inter_subset_left
  have hAsrc : ∀ z ∈ ball (0 : ℂ) r, wc.symm z ∈ wc.source := fun z hz =>
    wc.map_target (by rw [h3]; exact hz)
  have hcov : A ⊆ range ιd ∪ range (J ∘ ιd) := by
    rintro p ⟨z, ⟨hz1, hz2⟩, rfl⟩
    have hps := hAsrc z hz1
    have hcz : wc (wc.symm z) = z := wc.right_inv (by rw [h3]; exact hz1)
    have hc : wc.symm z ∈ range ιd ∪ range (J ∘ ιd) ∪ {x | J x = x} ∪ ↑Pd := by
      rw [hd.cover]; exact mem_univ _
    rcases hc with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have := hfix _ hps h
      rw [hcz] at this
      exact absurd this (ne_of_gt hz2)
    · exact absurd h (h4 hps)
  have ho1 : IsOpen (range ιd) := hd.embedding.isOpen_range
  have ho2 : IsOpen (range (J ∘ ιd)) := (J.isOpenEmbedding.comp hd.embedding).isOpen_range
  rcases hApre.subset_or_subset ho1 ho2 hd.disjoint hcov with h | h
  · left
    intro p hp him
    exact h ⟨wc p, ⟨by rw [← h3]; exact wc.map_source hp, him⟩, wc.left_inv hp⟩
  · right
    intro p hp him
    obtain ⟨hJ1, hJ2⟩ := h7 p hp
    have hJA : J p ∈ A := ⟨wc (J p), ⟨by rw [← h3]; exact wc.map_source hJ1, by
      rw [hJ2]; simpa using him⟩, wc.left_inv hJ1⟩
    obtain ⟨s, hs⟩ := h hJA
    exact ⟨s, J.injective (by simpa using hs)⟩

theorem s31qc_sides_iff {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    {F : FiniteTypeStructure S g n m} {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {wc : OpenPartialHomeomorph Xd.carrier ℂ}
    (h7 : ∀ p ∈ wc.source, J p ∈ wc.source ∧ wc (J p) = conj (wc p))
    (hup : ∀ p ∈ wc.source, 0 < (wc p).im → p ∈ range ιd) :
    (∀ p ∈ wc.source, (0 < (wc p).im ↔ p ∈ range ιd)) ∧
      (∀ p ∈ wc.source, ((wc p).im = 0 ↔ J p = p)) := by
  have hfix : ∀ p ∈ wc.source, ((wc p).im = 0 ↔ J p = p) := by
    intro p hp
    obtain ⟨hJ1, hJ2⟩ := h7 p hp
    constructor
    · intro him
      have : wc (J p) = wc p := by rw [hJ2]; exact Complex.conj_eq_iff_im.2 him
      exact wc.injOn hJ1 hp this
    · intro hJp
      have := hJ2
      rw [hJp] at this
      exact Complex.conj_eq_iff_im.1 this.symm
  refine ⟨fun p hp => ⟨hup p hp, fun hr => ?_⟩, hfix⟩
  by_contra hnot
  rw [not_lt] at hnot
  rcases hnot.lt_or_eq with hlt | heq
  · obtain ⟨hJ1, hJ2⟩ := h7 p hp
    have hJm : J p ∈ range ιd := hup _ hJ1 (by rw [hJ2]; simpa using hlt)
    obtain ⟨s, hs⟩ := hr
    exact Set.disjoint_left.1 hd.disjoint hJm ⟨s, by rw [Function.comp_apply, hs]⟩
  · have hJp := (hfix p hp).1 heq
    have hmem : p ∈ {x | J x = x} := hJp
    rw [hd.fixed_curves] at hmem
    rw [hd.embedding.isOpen_range.frontier_eq] at hmem
    exact hmem.1.2 hr

theorem s31qc_fixed_chart {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    {F : FiniteTypeStructure S g n m} {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {p₀ : Xd.carrier} (hp₀ : J p₀ = p₀) :
    ∃ (wc : OpenPartialHomeomorph Xd.carrier ℂ) (r : ℝ),
      0 < r ∧ p₀ ∈ wc.source ∧ wc p₀ = 0 ∧ wc.target = ball 0 r ∧
      (∀ p ∈ wc.source, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc p) ∧
      (∀ z ∈ wc.target, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc.symm z) ∧
      (∀ p ∈ wc.source, J p ∈ wc.source ∧ wc (J p) = conj (wc p)) ∧
      (∀ p ∈ wc.source, (0 < (wc p).im ↔ p ∈ range ιd)) ∧
      (∀ p ∈ wc.source, ((wc p).im = 0 ↔ J p = p)) := by
  have hmem : p₀ ∈ {x | J x = x} := hp₀
  rw [hd.fixed_curves] at hmem
  have hU : (↑Pd : Set Xd.carrier)ᶜ ∈ 𝓝 p₀ :=
    Pd.finite_toSet.isClosed.isOpen_compl.mem_nhds hmem.2
  obtain ⟨wc, r, hr, h1, h2, h3, h4, h5, h6, h7⟩ :=
    s31qc_fixed_chart_local hd.involution hp₀ hU
  rcases s31qc_sides_dichotomy hd h3 h4 h7 with hup | hup
  · obtain ⟨hi1, hi2⟩ := s31qc_sides_iff hd h7 hup
    exact ⟨wc, r, hr, h1, h2, h3, h5, h6, h7, hi1, hi2⟩
  · obtain ⟨wc', k0, k1, k2, k3, k4, k5, k6, k7, k8⟩ :=
      s31qc_chart_neg (J := J) h1 h2 h3 h4 h5 h6 h7
    have hup' : ∀ p ∈ wc'.source, 0 < (wc' p).im → p ∈ range ιd := by
      intro p hp him
      rw [k0] at hp
      rw [k8 p (by rw [k0]; exact hp)] at him
      exact hup p hp (by simpa using him)
    obtain ⟨hi1, hi2⟩ := s31qc_sides_iff hd k7 hup'
    exact ⟨wc', r, hr, k1, k2, k3, k5, k6, k7, hi1, hi2⟩

/-- A map continuous near a closed-in-the-open-set `C` carries convergence to `C` to convergence to any set
containing the image of `C`. -/
theorem s31qc_nhdsSet_tendsto_image {α X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {l : Filter α} {q : α → X} {C T : Set X} (hT : IsOpen T) (hCT : C ⊆ T) {f : X → Y}
    (hf : ContinuousOn f T) {B : Set Y} (hCB : f '' C ⊆ B) (hq : Tendsto q l (𝓝ˢ C)) :
    Tendsto (fun a => f (q a)) l (𝓝ˢ B) := by
  intro W hW
  obtain ⟨O, hOo, hBO, hOW⟩ := mem_nhdsSet_iff_exists.1 hW
  have hO' : IsOpen (T ∩ f ⁻¹' O) := hf.isOpen_inter_preimage hT hOo
  have hC : C ⊆ T ∩ f ⁻¹' O := fun p hp => ⟨hCT hp, hBO (hCB ⟨p, hp, rfl⟩)⟩
  have h : ∀ᶠ a in l, q a ∈ T ∩ f ⁻¹' O := hq (hO'.mem_nhdsSet.2 hC)
  rw [Filter.mem_map]
  filter_upwards [h] with a ha
  exact hOW ha.2

/-- The chart of a closed disc carries the frontier of the disc into the frontier of the chart domain. -/
theorem s31qc_chart_frontier_image {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {x : X}
    {D : Set X} {Jd : Set ℂ} (hDc : IsClosed D) (hDs : D ⊆ (chartAt ℂ x).source) (hJo : IsOpen Jd)
    (hDe : chartAt ℂ x '' D = closure Jd) : chartAt ℂ x '' frontier D ⊆ frontier Jd := by
  rintro _ ⟨p, hp, rfl⟩
  have hpD : p ∈ D := hDc.frontier_subset hp
  have hcp : chartAt ℂ x p ∈ closure Jd := by rw [← hDe]; exact ⟨p, hpD, rfl⟩
  rw [hJo.frontier_eq]
  refine ⟨hcp, fun hJ => hp.2 ?_⟩
  have hNo : IsOpen ((chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Jd) :=
    (chartAt ℂ x).isOpen_inter_preimage hJo
  have hND : (chartAt ℂ x).source ∩ (chartAt ℂ x) ⁻¹' Jd ⊆ D := by
    rintro q ⟨hq1, hq2⟩
    have : chartAt ℂ x q ∈ closure Jd := subset_closure hq2
    rw [← hDe] at this
    obtain ⟨q', hq', hqq⟩ := this
    have := (chartAt ℂ x).injOn (hDs hq') hq1 hqq
    rw [← this]; exact hq'
  exact interior_maximal hND hNo ⟨hDs hpD, hJ⟩

theorem s31qc_collar_witness {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {ιd : S → Xd.carrier}
    {wc : OpenPartialHomeomorph Xd.carrier ℂ} {r : ℝ} (hr : 0 < r) (hwt : wc.target = ball 0 r)
    (s : ℂ → S) (hs0 : ∀ z ∈ ball (0 : ℂ) r, 0 < z.im → ιd (s z) = wc.symm z)
    (hsd : ∀ z ∈ ball (0 : ℂ) r, 0 < z.im → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) s z)
    (j : Fin m)
    (hj : ∀ y : ℝ, |y| < r → Tendsto (fun z => F.ι (s z)) (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ))
      (𝓝ˢ (frontier (F.D j))))
    (x : F.X.carrier) (Jd : Set ℂ) (hDs : F.D j ⊆ (chartAt ℂ x).source)
    (hJd : IsJordanDomain Jd) (hb : Bornology.IsBounded Jd)
    (hDc : chartAt ℂ x '' F.D j = closure Jd) :
    ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ∃ κ : ℂ → ℂ,
      DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r' ∧ 0 < z.im} ∧
      ContinuousOn κ {z : ℂ | ‖z‖ < r' ∧ 0 ≤ z.im} ∧
      InjOn κ {z : ℂ | ‖z‖ < r' ∧ 0 ≤ z.im} ∧
      MapsTo κ {z : ℂ | ‖z‖ < r' ∧ 0 < z.im} (closure Jd)ᶜ ∧
      MapsTo κ {z : ℂ | ‖z‖ < r' ∧ z.im = 0} (frontier Jd) ∧
      (∃ V : Set ℂ, IsOpen V ∧ κ '' {z : ℂ | ‖z‖ < r' ∧ 0 ≤ z.im} = V ∩ Jdᶜ) ∧
      ∀ z : ℂ, ‖z‖ < r' → 0 < z.im →
        ∃ s' : S, ιd s' = wc.symm z ∧ F.ι s' ∈ (chartAt ℂ x).source ∧
          κ z = chartAt ℂ x (F.ι s') := by
  set c : OpenPartialHomeomorph F.X.carrier ℂ := chartAt ℂ x with hc
  have hDclosed : IsClosed (F.D j) := (s31eg_disc_compact (F.disc j)).isClosed
  have hfrD : frontier (F.D j) ⊆ c.source := hDclosed.frontier_subset.trans hDs
  have h0 : Tendsto (fun z => F.ι (s z)) (𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ)) (𝓝ˢ (frontier (F.D j))) := by
    simpa using hj 0 (by simpa using hr)
  have hev : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ), F.ι (s z) ∈ c.source :=
    h0.eventually (c.open_source.mem_nhdsSet.2 hfrD)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set r' : ℝ := min ε r with hr'
  have hr'pos : 0 < r' := lt_min hε hr
  have hr'ε : r' ≤ ε := min_le_left _ _
  have hr'r : r' ≤ r := min_le_right _ _
  set H : Set ℂ := {z : ℂ | ‖z‖ < r' ∧ 0 < z.im} with hH
  have hmem : ∀ z ∈ H, z ∈ ball (0 : ℂ) r ∧ 0 < z.im ∧ F.ι (s z) ∈ c.source := by
    rintro z ⟨hz1, hz2⟩
    refine ⟨mem_ball_zero_iff.2 (lt_of_lt_of_le hz1 hr'r), hz2, hεsub ⟨?_, hz2⟩⟩
    rw [mem_ball_zero_iff]
    exact lt_of_lt_of_le hz1 hr'ε
  set κ₀ : ℂ → ℂ := fun z => c (F.ι (s z)) with hκ₀
  have hd : DifferentiableOn ℂ κ₀ H := by
    intro z hz
    obtain ⟨hzb, him, hsrc⟩ := hmem z hz
    have hchart : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c (F.ι (s z)) :=
      ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := x)).mdifferentiableOn (by simp) _
        hsrc).mdifferentiableAt (c.open_source.mem_nhds hsrc)
    have hmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (c ∘ (F.ι ∘ s)) z :=
      hchart.comp z ((F.holomorphic (s z)).comp z (hsd z hzb him))
    exact (mdifferentiableAt_iff_differentiableAt.1 hmd).differentiableWithinAt
  have hinj : InjOn κ₀ H := by
    intro z₁ hz₁ z₂ hz₂ h12
    obtain ⟨hb1, hi1, hs1⟩ := hmem z₁ hz₁
    obtain ⟨hb2, hi2, hs2⟩ := hmem z₂ hz₂
    have h1 : F.ι (s z₁) = F.ι (s z₂) := c.injOn hs1 hs2 h12
    have h2 : s z₁ = s z₂ := F.embedding.injective h1
    have h3 : wc.symm z₁ = wc.symm z₂ := by
      rw [← hs0 z₁ hb1 hi1, ← hs0 z₂ hb2 hi2, h2]
    exact wc.symm.injOn (by rw [OpenPartialHomeomorph.symm_source, hwt]; exact hb1)
      (by rw [OpenPartialHomeomorph.symm_source, hwt]; exact hb2) h3
  have hmaps : MapsTo κ₀ H (closure Jd)ᶜ := by
    intro z hz hcl
    obtain ⟨-, -, hsrc⟩ := hmem z hz
    rw [← hDc] at hcl
    obtain ⟨q, hq, hqe⟩ := hcl
    have hqq : q = F.ι (s z) := c.injOn (hDs hq) hsrc hqe
    have hr0 : F.ι (s z) ∈ range F.ι := mem_range_self _
    rw [F.range_ι] at hr0
    exact hr0 (Or.inr (mem_iUnion.2 ⟨j, hqq ▸ hq⟩))
  have hcont : ContinuousOn (fun p => ((c p : ℂ) : ExtPlane)) c.source :=
    OnePoint.continuous_coe.comp_continuousOn c.continuousOn
  have hCB : (fun p => ((c p : ℂ) : ExtPlane)) '' frontier (F.D j) ⊆ frontier (toExt Jd) := by
    rintro _ ⟨p, hp, rfl⟩
    have := s31qc_chart_frontier_image hDclosed hDs hJd.1 hDc ⟨p, hp, rfl⟩
    rw [frontier_toExt_of_isBounded' hb hJd.1]
    exact ⟨c p, this, rfl⟩
  have hbdry : ∀ y : ℝ, |y| < r' → Tendsto (fun z => ((κ₀ z : ℂ) : ExtPlane))
      (𝓝[{z : ℂ | 0 < z.im}] (y : ℂ)) (𝓝ˢ (frontier (toExt Jd))) := fun y hy =>
    s31qc_nhdsSet_tendsto_image c.open_source hfrD hcont hCB (hj y (lt_of_lt_of_le hy hr'r))
  obtain ⟨κ, hκc, hκeq, hκinj, hκmaps, V, hV, hVimg⟩ :=
    s31qc_collar_boundary hJd hb hr'pos hd hinj hmaps hbdry
  refine ⟨r', hr'pos, hr'r, κ, hd.congr (fun z hz => hκeq hz), hκc, hκinj,
    fun z hz => by rw [hκeq hz]; exact hmaps hz, hκmaps, ⟨V, hV, hVimg⟩, ?_⟩
  intro z hz1 him
  obtain ⟨hzb, -, hsrc⟩ := hmem z ⟨hz1, him⟩
  exact ⟨s z, hs0 z hzb him, hsrc, hκeq ⟨hz1, him⟩⟩


section Double
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}

/-- (B) Collar coordinates at a fixed point `p₀` of the given involution.  `ω` is a holomorphic chart of
`Xd` on a disc `ball 0 r` (so `ω p₀ = 0`) in which `J` is complex conjugation and the upper half is
exactly the part of `ιd(S)`.  The pulled-back original coordinate `κ` (a chart of `F.X` at the hole `j`)
extends to the closed half disc as in (A), and its values on the open half are the actual chart images of
`F.ι` along `ιd⁻¹`.  The hole is an arbitrary `IsClosedDiscIn`-witness `(x, Jd)` of `F.D j`; the radius `r'` of the
collar half disc may depend on the witness (its chart source can be thin). -/
theorem s31qi_collar_from_hd [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {p₀ : Xd.carrier} (hp₀ : J p₀ = p₀) :
    ∃ (j : Fin m) (wc : OpenPartialHomeomorph Xd.carrier ℂ) (r : ℝ),
      0 < r ∧ p₀ ∈ wc.source ∧ wc p₀ = 0 ∧ wc.target = ball 0 r ∧
      (∀ p ∈ wc.source, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc p) ∧
      (∀ z ∈ wc.target, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc.symm z) ∧
      (∀ p ∈ wc.source, J p ∈ wc.source ∧ wc (J p) = conj (wc p)) ∧
      (∀ p ∈ wc.source, (0 < (wc p).im ↔ p ∈ range ιd)) ∧
      (∀ p ∈ wc.source, ((wc p).im = 0 ↔ J p = p)) ∧
      ∀ (x : F.X.carrier) (Jd : Set ℂ), F.D j ⊆ (chartAt ℂ x).source →
        IsJordanDomain Jd → Bornology.IsBounded Jd → chartAt ℂ x '' F.D j = closure Jd →
        closure Jd ⊆ (chartAt ℂ x).target →
        ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ∃ κ : ℂ → ℂ,
          DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r' ∧ 0 < z.im} ∧
          ContinuousOn κ {z : ℂ | ‖z‖ < r' ∧ 0 ≤ z.im} ∧
          InjOn κ {z : ℂ | ‖z‖ < r' ∧ 0 ≤ z.im} ∧
          MapsTo κ {z : ℂ | ‖z‖ < r' ∧ 0 < z.im} (closure Jd)ᶜ ∧
          MapsTo κ {z : ℂ | ‖z‖ < r' ∧ z.im = 0} (frontier Jd) ∧
          (∃ V : Set ℂ, IsOpen V ∧ κ '' {z : ℂ | ‖z‖ < r' ∧ 0 ≤ z.im} = V ∩ Jdᶜ) ∧
          ∀ z : ℂ, ‖z‖ < r' → 0 < z.im →
            ∃ s : S, ιd s = wc.symm z ∧ F.ι s ∈ (chartAt ℂ x).source ∧ κ z = chartAt ℂ x (F.ι s) := by
  obtain ⟨wc, r, hr, h1, h2, h3, h5, h6, h7, hi1, hi2⟩ := s31qc_fixed_chart hd hp₀
  have hinj : Function.Injective ιd := hd.embedding.injective
  haveI : Nonempty S := inferInstance
  set s : ℂ → S := fun z => Function.invFun ιd (wc.symm z) with hs
  have hzt : ∀ z ∈ ball (0 : ℂ) r, z ∈ wc.target := fun z hz => by rw [h3]; exact hz
  have hsrc : ∀ z ∈ ball (0 : ℂ) r, wc.symm z ∈ wc.source := fun z hz => wc.map_target (hzt z hz)
  have hwz : ∀ z ∈ ball (0 : ℂ) r, wc (wc.symm z) = z := fun z hz => wc.right_inv (hzt z hz)
  have hup : ∀ z ∈ ball (0 : ℂ) r, 0 < z.im → wc.symm z ∈ range ιd := fun z hz him =>
    (hi1 _ (hsrc z hz)).1 (by rw [hwz z hz]; exact him)
  have hreal : ∀ z ∈ ball (0 : ℂ) r, z.im = 0 → J (wc.symm z) = wc.symm z := fun z hz him =>
    (hi2 _ (hsrc z hz)).1 (by rw [hwz z hz]; exact him)
  have hs0 : ∀ z ∈ ball (0 : ℂ) r, 0 < z.im → ιd (s z) = wc.symm z := fun z hz him =>
    Function.invFun_eq (hup z hz him)
  have hsd : ∀ z ∈ ball (0 : ℂ) r, 0 < z.im → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) s z := fun z hz him =>
    ((s31inv_invFun_mdifferentiableOn hinj hd.holomorphic).mdifferentiableAt
      (hd.embedding.isOpen_range.mem_nhds (hup z hz him))).comp z (h6 z (hzt z hz))
  have hγ : ContinuousOn wc.symm (ball (0 : ℂ) r) := by
    rw [← h3]; exact wc.continuousOn_symm
  obtain ⟨j, hj⟩ := s31qc_hole_of_collar_curve F hm hd hr hγ hup hreal s hs0
  refine ⟨j, wc, r, hr, h1, h2, h3, h5, h6, h7, hi1, hi2, ?_⟩
  intro x Jd hDs hJd hb hDc _hcl
  exact s31qc_collar_witness F hr h3 s hs0 hsd j hj x Jd hDs hJd hb hDc

end Double

end LiZhongQC
