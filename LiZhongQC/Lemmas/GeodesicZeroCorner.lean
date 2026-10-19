import LiZhongQC.Ch07.S25_QuadraticDifferentials

/-!
Zero-corner obstruction for actual locally minimizing phi-curves.
The radial potential gives a lower bound for the original curve, including a
curve with arbitrary parametrization. A strict-sector connector contradicts
local minimality. No simple bigon or prior angle lower bound is assumed.

Archive source candidate: Root alone compiles and chooses final placement.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace LiZhongQC

/-- A point in the slit plane gives a strictly shorter chord than the route via zero. -/
theorem s25za_slit_chord {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ‖z - 1‖ < ‖z‖ + 1 := by
  have hle : ‖z - 1‖ ≤ ‖z‖ + 1 := by simpa using norm_sub_le z (1 : ℂ)
  apply lt_of_le_of_ne hle
  intro heq
  have hzsq : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hsubsq : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    ring
  have hre : z.re = -‖z‖ := by nlinarith [congrArg (fun x : ℝ => x ^ 2) heq]
  have him : z.im = 0 := by
    rw [hre] at hzsq
    nlinarith [sq_nonneg z.im]
  rcases Complex.mem_slitPlane_iff.1 hz with h | h
  · nlinarith [norm_nonneg z]
  · exact h him

/-- The principal angular strict-sector condition implies the analytic connector condition. -/
theorem s25za_sector_of_arg {c : ℝ} (hc : 1 < c) {z : ℂ} (hz : z ≠ 0)
    (harg : |Complex.arg z| < Real.pi / c) :
    Real.cos (Real.pi / c) * ‖z‖ < z.re := by
  have hc0 : 0 < c := by linarith
  have hpi : Real.pi / c ≤ Real.pi := by
    rw [div_le_iff₀ hc0]
    nlinarith [Real.pi_pos]
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg (Complex.arg z)) hpi harg
  rw [Real.cos_abs] at hcos
  have h := mul_lt_mul_of_pos_right hcos (norm_pos_iff.2 hz)
  simpa only [mul_comm, Complex.norm_mul_cos_arg] using h

/-- Strictly inside the sector, the existing connector is strictly shorter than
the sum of the two endpoint radial lengths, not merely no longer. -/
theorem s25za_strict_connector (m : ℕ) (hm : 1 ≤ m) {r : ℝ} {a b : ℂ}
    (ha : a ∈ ball (0 : ℂ) r) (hb : b ∈ ball (0 : ℂ) r)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (harg : |Complex.arg (b / a)| < 2 * Real.pi / ((m : ℝ) + 2)) :
    ∃ σ : LRCurve, IsPathIn (ball (0 : ℂ) r) a b σ ∧
      phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) σ <
        ENNReal.ofReal (‖a‖ ^ (((m : ℝ) + 2) / 2) + ‖b‖ ^ (((m : ℝ) + 2) / 2)) := by
  let c : ℝ := ((m : ℝ) + 2) / 2
  have hc : 1 < c := by
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    dsimp only [c]
    linarith
  have hc0 : 0 < c := by linarith
  have hac : 0 < ‖a‖ ^ c := Real.rpow_pos_of_pos (norm_pos_iff.2 ha0) c
  have he : Real.pi / c = 2 * Real.pi / ((m : ℝ) + 2) := by
    dsimp only [c]
    field_simp [show (m : ℝ) + 2 ≠ 0 by positivity]
    <;> ring
  have harg' : |Complex.arg (b / a)| < Real.pi / c := by rwa [he]
  have hsec := s25za_sector_of_arg hc (div_ne_zero hb0 ha0) harg'
  obtain ⟨σ, hσ, hlen⟩ := s25e_sector_curve m hm ha hb ha0 hsec
  have hslit := (s25e_cpow_cpow_inv hc (div_ne_zero hb0 ha0) harg').1
  have hshort := mul_lt_mul_of_pos_left (s25za_slit_chord hslit) hac
  have hnorm : ‖a‖ ^ c * (‖(b / a) ^ (c : ℂ)‖ + 1) = ‖a‖ ^ c + ‖b‖ ^ c := by
    rw [Complex.norm_cpow_real, norm_div,
      Real.div_rpow (norm_nonneg b) (norm_nonneg a)]
    field_simp [hac.ne']
    <;> ring
  rw [hnorm] at hshort
  refine ⟨σ, hσ, ?_⟩
  rw [hlen]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity :
    0 < ‖a‖ ^ c + ‖b‖ ^ c)).2 hshort

/-- Exact density transport in an m-th order zero natural coordinate. -/
theorem s25za_density (m : ℕ) {φ ζ : ℂ → ℂ} {W : Set ℂ}
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    {z : ℂ} (hz : z ∈ W) :
    phiDensity φ z =
      phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) (ζ z) *
        ‖deriv ζ z‖ₑ := by
  have hn : ‖φ z‖ = ‖(((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m‖ * ‖deriv ζ z‖ ^ 2 := by
    rw [hq z hz, norm_mul, norm_pow]
  change ENNReal.ofReal (Real.sqrt ‖φ z‖) = _
  rw [hn, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _),
    ENNReal.ofReal_mul (Real.sqrt_nonneg _), ofReal_norm]
  rfl

/-- Transport the entire segment integral, including nondifferentiable parameter
values: the conformal chain rule handles the derivative's zero convention. -/
theorem s25za_segment_transport (m : ℕ) {φ ζ : ℂ → ℂ} {W V : Set ℂ}
    (hW : IsOpen W) (hζ : IsConformalOnto ζ W V)
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (γ : LRCurve) {s t : ℝ} (hmap : MapsTo γ.toFun (Icc s t) W) :
    phiSegmentLength φ γ s t =
      ∫⁻ u in Ioo s t,
        phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) (ζ (γ.toFun u)) *
          ‖deriv (ζ ∘ γ.toFun) u‖ₑ := by
  change (∫⁻ u in Ioo s t, phiDensity φ (γ.toFun u) * ‖deriv γ.toFun u‖ₑ) = _
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro u hu
  have hev : ∀ᶠ v in 𝓝 u, γ.toFun v ∈ W := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
    exact hmap (Ioo_subset_Icc_self hv)
  dsimp only
  rw [hζ.deriv_comp hW hev, s25za_density m hq (hmap (Ioo_subset_Icc_self hu)), enorm_mul]
  exact mul_assoc _ _ _

/-- A natural-coordinate potential bounds the length of the original curve.
The only parametrization hypothesis is Lipschitz continuity on this interval. -/
theorem s25za_potential_segment (m : ℕ) {φ ζ : ℂ → ℂ} {W V : Set ℂ}
    (hW : IsOpen W) (hζ : IsConformalOnto ζ W V)
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    {G : ℂ → ℝ}
    (hG : ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      |G y - G x| ≤ ((((m : ℝ) + 2) / 2) * ‖x‖ ^ ((((m : ℝ) + 2) / 2) - 1) + ε) * ‖y - x‖)
    (γ : LRCurve) {K : ℝ≥0} {s t : ℝ} (hst : s ≤ t)
    (hK : LipschitzOnWith K γ.toFun (Icc s t)) (hmap : MapsTo γ.toFun (Icc s t) W) :
    ENNReal.ofReal (G (ζ (γ.toFun t)) - G (ζ (γ.toFun s))) ≤ phiSegmentLength φ γ s t := by
  obtain ⟨K', hK'⟩ := s25e_comp_lipschitz hW hζ.1 hK hmap
  have h := s25e_potential_model m hG hst hK'
  rw [s25za_segment_transport m hW hζ hq γ hmap]
  exact h

/-- Every curve that passes through the zero pays both radial costs. No equality
case, straightness, radial parametrization, or prior angle bound is assumed. -/
theorem s25za_through_zero_lower (m : ℕ) {φ ζ : ℂ → ℂ} {W V : Set ℂ}
    (hW : IsOpen W) (hζ : IsConformalOnto ζ W V)
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (γ : LRCurve) {K : ℝ≥0} {s t₀ t : ℝ} (hs : s ≤ t₀) (ht : t₀ ≤ t)
    (hK : LipschitzOnWith K γ.toFun (Icc s t)) (hmap : MapsTo γ.toFun (Icc s t) W)
    (hzero : ζ (γ.toFun t₀) = 0) :
    ENNReal.ofReal (‖ζ (γ.toFun s)‖ ^ (((m : ℝ) + 2) / 2) +
      ‖ζ (γ.toFun t)‖ ^ (((m : ℝ) + 2) / 2)) ≤ phiSegmentLength φ γ s t := by
  let c : ℝ := ((m : ℝ) + 2) / 2
  have hc0 : 0 < c := by dsimp only [c]; positivity
  have hsubL : Icc s t₀ ⊆ Icc s t := Icc_subset_Icc le_rfl ht
  have hsubR : Icc t₀ t ⊆ Icc s t := Icc_subset_Icc hs le_rfl
  have hneg : ∀ x : ℂ, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ y : ℂ, ‖y - x‖ < δ →
      |(-‖y‖ ^ c) - (-‖x‖ ^ c)| ≤ (c * ‖x‖ ^ (c - 1) + ε) * ‖y - x‖ := by
    intro x ε hε
    obtain ⟨δ, hδ, hd⟩ := s25e_radial_hG m x ε hε
    refine ⟨δ, hδ, fun y hy => ?_⟩
    simpa only [neg_sub_neg, abs_sub_comm] using hd y hy
  have hL := s25za_potential_segment m hW hζ hq
    (G := fun w => -‖w‖ ^ c) hneg γ hs (hK.mono hsubL) (hmap.mono hsubL (Subset.refl _))
  have hR := s25za_potential_segment m hW hζ hq
    (s25e_radial_hG m) γ ht (hK.mono hsubR) (hmap.mono hsubR (Subset.refl _))
  have hzpow : ‖ζ (γ.toFun t₀)‖ ^ c = 0 := by
    rw [hzero, norm_zero, Real.zero_rpow hc0.ne']
  change ENNReal.ofReal (-‖ζ (γ.toFun t₀)‖ ^ c - (-‖ζ (γ.toFun s)‖ ^ c)) ≤ _ at hL
  change ENNReal.ofReal (‖ζ (γ.toFun t)‖ ^ c - ‖ζ (γ.toFun t₀)‖ ^ c) ≤ _ at hR
  rw [hzpow, neg_zero, zero_sub, neg_neg] at hL
  rw [hzpow, sub_zero] at hR
  rw [s25g_segLen_add φ γ hs ht, ENNReal.ofReal_add (by positivity) (by positivity)]
  exact add_le_add hL hR

/-- Distances can only decrease when more comparison curves are admitted. -/
theorem s25za_dist_mono {W D : Set ℂ} (hWD : W ⊆ D) (ρ : ℂ → ℝ≥0∞) (a b : ℂ) :
    metricDist D ρ a b ≤ metricDist W ρ a b := by
  unfold metricDist
  apply le_iInf₂
  intro γ hγ
  exact iInf₂_le γ ⟨hγ.1, hγ.2.1, hγ.2.2.1, hγ.2.2.2.trans hWD⟩

/-- A conformal natural-coordinate chart transports its intrinsic comparison distance. -/
theorem s25za_chart_distance (m : ℕ) {φ ζ : ℂ → ℂ} {W V : Set ℂ}
    (hW : IsOpen W) (hV : IsOpen V) (hζ : IsConformalOnto ζ W V)
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    {a b : ℂ} (ha : a ∈ W) (hb : b ∈ W) :
    metricDist W (phiDensity φ) a b =
      metricDist V (phiDensity (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m)) (ζ a) (ζ b) := by
  let ψ := Function.invFunOn ζ W
  have hψ : IsConformalOnto ψ V W := hζ.symm hW
  apply metricDist_eq_of_isConformalOnto hW hV hζ hψ.1 hψ.mapsTo
  · intro w hw
    apply Function.invFunOn_eq
    change w ∈ ζ '' W
    rwa [hζ.2.2]
  · intro z hz
    exact hζ.2.1.leftInvOn_invFunOn hz
  · intro z hz
    exact s25za_density m hq hz
  · exact ha
  · exact hb

/-- A minimizing original phi-segment through a zero cannot have endpoint rays
separated by a strict cone sector. This compares actual original length with
an actual connector; the original segment need not be radial. -/
theorem s25za_minimizing_angle (m : ℕ) (hm : 1 ≤ m)
    {φ ζ : ℂ → ℂ} {D W : Set ℂ} {r : ℝ}
    (hW : IsOpen W) (hWD : W ⊆ D) (hζ : IsConformalOnto ζ W (ball (0 : ℂ) r))
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (γ : LRCurve) {K : ℝ≥0} {s t₀ t : ℝ} (hs : s ≤ t₀) (ht : t₀ ≤ t)
    (hK : LipschitzOnWith K γ.toFun (Icc s t)) (hmap : MapsTo γ.toFun (Icc s t) W)
    (hzero : ζ (γ.toFun t₀) = 0)
    (hs0 : ζ (γ.toFun s) ≠ 0) (ht0 : ζ (γ.toFun t) ≠ 0)
    (hmin : phiSegmentLength φ γ s t = metricDist D (phiDensity φ) (γ.toFun s) (γ.toFun t)) :
    2 * Real.pi / ((m : ℝ) + 2) ≤ |Complex.arg (ζ (γ.toFun t) / ζ (γ.toFun s))| := by
  by_contra hangle
  have hst := hs.trans ht
  have hsW := hmap ⟨le_rfl, hst⟩
  have htW := hmap ⟨hst, le_rfl⟩
  obtain ⟨σ, hσ, hshort⟩ := s25za_strict_connector m hm
    (hζ.mapsTo hsW) (hζ.mapsTo htW) hs0 ht0 (not_le.1 hangle)
  have hlower := s25za_through_zero_lower m hW hζ hq γ hs ht hK hmap hzero
  have hupper : phiSegmentLength φ γ s t ≤
      phiLength (fun w : ℂ => (((m : ℂ) + 2) / 2) ^ 2 * w ^ m) σ := by
    rw [hmin]
    apply (s25za_dist_mono hWD (phiDensity φ) (γ.toFun s) (γ.toFun t)).trans
    rw [s25za_chart_distance m hW isOpen_ball hζ hq hsW htW]
    exact iInf₂_le σ hσ
  exact (not_lt_of_ge hlower) (hupper.trans_lt hshort)

/-- Both complementary angles satisfy the bound. The principal absolute angle
is the smaller angle; its complement is no smaller than pi. -/
theorem s25za_both_angles (m : ℕ) {z : ℂ}
    (h : 2 * Real.pi / ((m : ℝ) + 2) ≤ |Complex.arg z|) :
    2 * Real.pi / ((m : ℝ) + 2) ≤ |Complex.arg z| ∧
      2 * Real.pi / ((m : ℝ) + 2) ≤ 2 * Real.pi - |Complex.arg z| := by
  refine ⟨h, ?_⟩
  have hα : 2 * Real.pi / ((m : ℝ) + 2) ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity : 0 < (m : ℝ) + 2)]
    nlinarith [Real.pi_pos, (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]
  linarith [Complex.abs_arg_le_pi z]

/-- Actual local minimality supplies the endpoint-angle inequality throughout
a sufficiently small two-sided window inside a specified natural chart. -/
theorem s25za_geodesic_window (m : ℕ) (hm : 1 ≤ m)
    {φ ζ : ℂ → ℂ} {D W : Set ℂ} {r : ℝ}
    (hW : IsOpen W) (hWD : W ⊆ D) (hζ : IsConformalOnto ζ W (ball (0 : ℂ) r))
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ D γ)
    {a t₀ b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (ha₀ : a < t₀) (h₀b : t₀ < b)
    (hmap : MapsTo γ.toFun (Icc a b) W) (hzero : ζ (γ.toFun t₀) = 0) :
    ∃ ε > 0, ∀ s ∈ Ioo (t₀ - ε) t₀, ∀ t ∈ Ioo t₀ (t₀ + ε),
      ζ (γ.toFun s) ≠ 0 → ζ (γ.toFun t) ≠ 0 →
        2 * Real.pi / ((m : ℝ) + 2) ≤ |Complex.arg (ζ (γ.toFun t) / ζ (γ.toFun s))| ∧
        2 * Real.pi / ((m : ℝ) + 2) ≤ 2 * Real.pi - |Complex.arg (ζ (γ.toFun t) / ζ (γ.toFun s))| := by
  obtain ⟨K, hK⟩ := hγ.1
  obtain ⟨δ, hδ, hlocal⟩ := hγ.2.2 t₀ ⟨by linarith, by linarith⟩
  let ε := min δ (min (t₀ - a) (b - t₀))
  have hε : 0 < ε := lt_min hδ (lt_min (sub_pos.2 ha₀) (sub_pos.2 h₀b))
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεa : ε ≤ t₀ - a := (min_le_right _ _).trans (min_le_left _ _)
  have hεb : ε ≤ b - t₀ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, hε, ?_⟩
  intro s hs t ht hs0 ht0
  have has : a ≤ s := by linarith [hs.1]
  have htb : t ≤ b := by linarith [ht.2]
  have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨ha.trans has, by linarith [hs.2]⟩
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], htb.trans hb⟩
  have hst : s < t := hs.2.trans ht.1
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
  apply s25za_both_angles m
  exact s25za_minimizing_angle m hm hW hWD hζ hq γ hs.2.le ht.1.le
    (hK.mono (Icc_subset_Icc hsI.1 htI.2)) (hmap.mono hsub (Subset.refl _)) hzero hs0 ht0
    (hlocal s hsI t htI (by linarith [hs.1]) hst (by linarith [ht.2]))

/-- Positive radial rescalings preserve the principal angular separation. -/
theorem s25za_radial_arg {u v : ℂ} {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) :
    Complex.arg (((σ : ℂ) * v) / ((ρ : ℂ) * u)) = Complex.arg (v / u) := by
  have he : ((σ : ℂ) * v) / ((ρ : ℂ) * u) = ((σ / ρ : ℝ) : ℂ) * (v / u) := by
    push_cast
    exact (div_mul_div_comm (σ : ℂ) (ρ : ℂ) v u).symm
  rw [he]
  exact Complex.arg_real_mul (v / u) (div_pos hσ hρ)

/-- In particular, two actual radial arms of a locally minimizing segment have
both corner angles at least 2*pi/(m+2). The radial identities are geometric
hypotheses to be supplied by regular-piece classification, not length assumptions. -/
theorem s25za_radial_corner (m : ℕ) (hm : 1 ≤ m)
    {φ ζ : ℂ → ℂ} {D W : Set ℂ} {r : ℝ}
    (hW : IsOpen W) (hWD : W ⊆ D) (hζ : IsConformalOnto ζ W (ball (0 : ℂ) r))
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    (γ : LRCurve) {K : ℝ≥0} {s t₀ t : ℝ} (hs : s ≤ t₀) (ht : t₀ ≤ t)
    (hK : LipschitzOnWith K γ.toFun (Icc s t)) (hmap : MapsTo γ.toFun (Icc s t) W)
    (hzero : ζ (γ.toFun t₀) = 0)
    {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (hleft : ζ (γ.toFun s) = (ρ : ℂ) * u) (hright : ζ (γ.toFun t) = (σ : ℂ) * v)
    (hmin : phiSegmentLength φ γ s t = metricDist D (phiDensity φ) (γ.toFun s) (γ.toFun t)) :
    2 * Real.pi / ((m : ℝ) + 2) ≤ |Complex.arg (v / u)| ∧
      2 * Real.pi / ((m : ℝ) + 2) ≤ 2 * Real.pi - |Complex.arg (v / u)| := by
  have hs0 : ζ (γ.toFun s) ≠ 0 := by
    rw [hleft]
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 hρ.ne') hu
  have ht0 : ζ (γ.toFun t) ≠ 0 := by
    rw [hright]
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 hσ.ne') hv
  have h := s25za_minimizing_angle m hm hW hWD hζ hq γ hs ht hK hmap hzero hs0 ht0 hmin
  rw [hleft, hright, s25za_radial_arg hρ hσ] at h
  exact s25za_both_angles m h

/-- Angular bounds pass to any actual limiting angle of shrinking endpoint
pairs. This uses closed inequalities and does not assume the desired bound. -/
theorem s25za_angle_limit (m : ℕ) {θ : ℕ → ℝ} {θ₀ : ℝ}
    (hθ : Tendsto θ atTop (𝓝 θ₀))
    (hbound : ∀ᶠ n in atTop, 2 * Real.pi / ((m : ℝ) + 2) ≤ θ n ∧
      2 * Real.pi / ((m : ℝ) + 2) ≤ 2 * Real.pi - θ n) :
    2 * Real.pi / ((m : ℝ) + 2) ≤ θ₀ ∧
      2 * Real.pi / ((m : ℝ) + 2) ≤ 2 * Real.pi - θ₀ := by
  constructor
  · exact ge_of_tendsto hθ (hbound.mono fun n hn => hn.1)
  · exact ge_of_tendsto (tendsto_const_nhds.sub hθ) (hbound.mono fun n hn => hn.2)

/-- Absolute argument has an arccos expression, including on the negative real
axis. This avoids introducing an artificial branch-cut assumption on the angle. -/
theorem s25za_abs_arg_arccos {z : ℂ} (hz : z ≠ 0) :
    |Complex.arg z| = Real.arccos (z.re / ‖z‖) := by
  rw [← Complex.cos_arg hz, ← Real.cos_abs,
    Real.arccos_cos (abs_nonneg (Complex.arg z)) (Complex.abs_arg_le_pi z)]

/-- Nonzero limiting endpoint ratios have convergent smaller angles, even when
the limiting ratio lies on the branch cut of the signed principal argument. -/
theorem s25za_abs_arg_tendsto {q : ℕ → ℂ} {q₀ : ℂ}
    (hq : Tendsto q atTop (𝓝 q₀)) (hq₀ : q₀ ≠ 0) :
    Tendsto (fun n => |Complex.arg (q n)|) atTop (𝓝 |Complex.arg q₀|) := by
  have hre := (Complex.continuous_re.tendsto q₀).comp hq
  have hnorm := (continuous_norm.tendsto q₀).comp hq
  have hquot := hre.div hnorm (norm_ne_zero_iff.2 hq₀)
  have hangle := (Real.continuous_arccos.tendsto (q₀.re / ‖q₀‖)).comp hquot
  rw [← s25za_abs_arg_arccos hq₀] at hangle
  apply hangle.congr'
  have hne : ∀ᶠ n in atTop, q n ≠ 0 :=
    hq.eventually (isOpen_compl_singleton.mem_nhds hq₀)
  filter_upwards [hne] with n hn
  exact (s25za_abs_arg_arccos hn).symm

/-- A genuine shrinking-endpoint consumer of the local geodesic theorem. The
limit premise is convergence of endpoint ratios, not a prior angular bound.
In particular, it applies after regular pieces supply two limiting radial arms. -/
theorem s25za_limiting_corner (m : ℕ) (hm : 1 ≤ m)
    {φ ζ : ℂ → ℂ} {D W : Set ℂ} {r : ℝ}
    (hW : IsOpen W) (hWD : W ⊆ D) (hζ : IsConformalOnto ζ W (ball (0 : ℂ) r))
    (hq : ∀ z ∈ W, φ z = (((m : ℂ) + 2) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ D γ)
    {a t₀ b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (ha₀ : a < t₀) (h₀b : t₀ < b)
    (hmap : MapsTo γ.toFun (Icc a b) W) (hzero : ζ (γ.toFun t₀) = 0)
    {s t : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 t₀)) (ht : Tendsto t atTop (𝓝 t₀))
    (hside : ∀ᶠ n in atTop, s n < t₀ ∧ t₀ < t n ∧
      ζ (γ.toFun (s n)) ≠ 0 ∧ ζ (γ.toFun (t n)) ≠ 0)
    {q₀ : ℂ} (hq₀ : q₀ ≠ 0)
    (hratio : Tendsto (fun n => ζ (γ.toFun (t n)) / ζ (γ.toFun (s n))) atTop (𝓝 q₀)) :
    2 * Real.pi / ((m : ℝ) + 2) ≤ |Complex.arg q₀| ∧
      2 * Real.pi / ((m : ℝ) + 2) ≤ 2 * Real.pi - |Complex.arg q₀| := by
  obtain ⟨ε, hε, hwindow⟩ := s25za_geodesic_window m hm hW hWD hζ hq hγ
    ha hb ha₀ h₀b hmap hzero
  have hsnear : ∀ᶠ n in atTop, t₀ - ε < s n :=
    (tendsto_order.1 hs).1 (t₀ - ε) (by linarith)
  have htnear : ∀ᶠ n in atTop, t n < t₀ + ε :=
    (tendsto_order.1 ht).2 (t₀ + ε) (by linarith)
  apply s25za_angle_limit m (s25za_abs_arg_tendsto hratio hq₀)
  filter_upwards [hsnear, htnear, hside] with n hsn htn hn
  exact hwindow (s n) ⟨hsn, hn.1⟩ (t n) ⟨hn.2.1, htn⟩ hn.2.2.1 hn.2.2.2

end LiZhongQC

