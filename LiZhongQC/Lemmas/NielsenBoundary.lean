import DouadyEarle.Extension
import LiZhongQC.Ch06.S23_QCOnSurfaces
import LiZhongQC.Lemmas.RingCharacterization
import LiZhongQC.Lemmas.Winding
import LiZhongQC.Lemmas.LocalWinding

/-!
# The Nielsen boundary map of a lift (`s24q_nb_`, for §24.2)

The lift to `ℍ` of a homeomorphism between compact surfaces uniformized by Fuchsian groups is a quasi-isometry
of the hyperbolic plane (`s24q_nb_qi`, parts A); a quasi-isometry maps geodesics near geodesics (`s24q_nb_morse`,
part B), hence extends to the boundary circle (parts C: `s24q_nb_cauchy`, `s24q_nb_limit`); the boundary map is a
homeomorphism intertwining the deck groups (part D: `s24q_nb_extension`).  Orientation enters through the local winding
number `+1` of the lift (`s24q_nb_lift_localWinding`), which gives an increasing lift of the boundary map
(`s24q_nb_increasing`).  The three results together give `s24q_boundary`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u v

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S₁ : Type v} [TopologicalSpace S₁] [ChartedSpace ℂ S₁]

/-- The hyperbolic distance of two points on a common vertical line. -/
theorem s24q_nb_dist_vertical (y y' : ℝ) (hy : 0 < y) (hy' : 0 < y') :
    dist (UpperHalfPlane.mk ⟨0, y⟩ hy) (UpperHalfPlane.mk ⟨0, y'⟩ hy') = |Real.log y - Real.log y'| := by
  have h := UpperHalfPlane.dist_of_re_eq (z := UpperHalfPlane.mk ⟨0, y⟩ hy) (w := UpperHalfPlane.mk ⟨0, y'⟩ hy') rfl
  rw [h, Real.dist_eq]
  rfl

/-- The real part of `(z - a)/(b - z)` vanishes when `z` lies on the circle with diameter `[a, b]`. -/
theorem s24q_nb_re_div_zero (a b u v : ℝ) (h : (u - a) * (b - u) = v ^ 2) :
    (((u : ℂ) + v * I - a) / (b - ((u : ℂ) + v * I))).re = 0 := by
  rw [Complex.div_re]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im, mul_zero, zero_mul, sub_zero, add_zero,
    mul_one, zero_sub, zero_add]
  have h0 : (u - a) * (b - u) + v * (-v) = 0 := by nlinarith
  have h1 : ∀ N : ℝ, (u - a) * (b - u) / N + v * (-v) / N = 0 := fun N => by
    rw [← add_div, h0, zero_div]
  exact h1 _

/-- Two points of `ℍ` are moved to the imaginary axis by one element of `SL(2, ℝ)`. -/
theorem s24q_nb_exists_vertical (z w : UpperHalfPlane) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, ((g • z : UpperHalfPlane) : ℂ).re = 0 ∧
      ((g • w : UpperHalfPlane) : ℂ).re = 0 := by
  by_cases hre : (z : ℂ).re = (w : ℂ).re
  · obtain ⟨g, h00, h01, h10, h11⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        g 0 0 = 1 ∧ g 0 1 = -(z : ℂ).re ∧ g 1 0 = 0 ∧ g 1 1 = 1 :=
      ⟨⟨!![1, -(z : ℂ).re; 0, 1], by simp [Matrix.det_fin_two]⟩, rfl, rfl, rfl, rfl⟩
    refine ⟨g, ?_, ?_⟩
    · rw [h36t_coe_smul, h00, h01, h10, h11]
      simp
    · rw [h36t_coe_smul, h00, h01, h10, h11]
      have h2 : w.re = z.re := hre.symm
      simp [h2]
  · have hy : 0 < (z : ℂ).im := z.im_pos
    have hy' : 0 < (w : ℂ).im := w.im_pos
    obtain ⟨x, hx⟩ : ∃ x, x = (z : ℂ).re := ⟨_, rfl⟩
    obtain ⟨y, hyd⟩ : ∃ y, y = (z : ℂ).im := ⟨_, rfl⟩
    obtain ⟨x', hx'⟩ : ∃ x', x' = (w : ℂ).re := ⟨_, rfl⟩
    obtain ⟨y', hyd'⟩ : ∃ y', y' = (w : ℂ).im := ⟨_, rfl⟩
    rw [← hx, ← hx'] at hre
    rw [← hyd] at hy
    rw [← hyd'] at hy'
    have hxx : x - x' ≠ 0 := sub_ne_zero.2 hre
    obtain ⟨c, hc⟩ : ∃ c : ℝ, 2 * c * (x - x') = x ^ 2 + y ^ 2 - x' ^ 2 - y' ^ 2 :=
      ⟨(x ^ 2 + y ^ 2 - x' ^ 2 - y' ^ 2) / (2 * (x - x')), by field_simp⟩
    have hr2 : 0 < (x - c) ^ 2 + y ^ 2 := by positivity
    obtain ⟨r, hr, hrsq⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = (x - c) ^ 2 + y ^ 2 :=
      ⟨Real.sqrt ((x - c) ^ 2 + y ^ 2), Real.sqrt_pos.2 hr2, Real.sq_sqrt hr2.le⟩
    obtain ⟨s, hs, hssq⟩ : ∃ s : ℝ, 0 < s ∧ s ^ 2 = 2 * r :=
      ⟨Real.sqrt (2 * r), Real.sqrt_pos.2 (by positivity), Real.sq_sqrt (by positivity)⟩
    obtain ⟨g, h00, h01, h10, h11⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        g 0 0 = 1 / s ∧ g 0 1 = -(c - r) / s ∧ g 1 0 = -1 / s ∧ g 1 1 = (c + r) / s :=
      ⟨⟨!![1 / s, -(c - r) / s; -1 / s, (c + r) / s], by
        simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
        field_simp
        nlinarith⟩, rfl, rfl, rfl, rfl⟩
    have key : ∀ t : ℂ, (((1 / s : ℝ) : ℂ) * t + ((-(c - r) / s : ℝ) : ℂ)) /
        (((-1 / s : ℝ) : ℂ) * t + (((c + r) / s : ℝ) : ℂ)) = (t - ((c - r : ℝ) : ℂ)) / (((c + r : ℝ) : ℂ) - t) := by
      intro t
      have hs' : ((1 / s : ℝ) : ℂ) ≠ 0 := by
        have : (1 / s : ℝ) ≠ 0 := by positivity
        exact_mod_cast this
      have e1 : ((1 / s : ℝ) : ℂ) * t + ((-(c - r) / s : ℝ) : ℂ) = ((1 / s : ℝ) : ℂ) * (t - ((c - r : ℝ) : ℂ)) := by
        push_cast
        ring
      have e2 : ((-1 / s : ℝ) : ℂ) * t + (((c + r) / s : ℝ) : ℂ) = ((1 / s : ℝ) : ℂ) * (((c + r : ℝ) : ℂ) - t) := by
        push_cast
        ring
      rw [e1, e2, mul_div_mul_left _ _ hs']
    have hre0 : ∀ (τ : UpperHalfPlane) (u v : ℝ), (τ : ℂ).re = u → (τ : ℂ).im = v →
        (u - (c - r)) * ((c + r) - u) = v ^ 2 → ((g • τ : UpperHalfPlane) : ℂ).re = 0 := by
      intro τ u v hu hv huv
      rw [h36t_coe_smul, h00, h01, h10, h11, key]
      have : (τ : ℂ) = (u : ℂ) + v * I := by
        rw [← hu, ← hv]
        exact (Complex.re_add_im _).symm
      rw [this]
      exact s24q_nb_re_div_zero (c - r) (c + r) u v huv
    refine ⟨g, hre0 z x y hx.symm hyd.symm ?_, hre0 w x' y' hx'.symm hyd'.symm ?_⟩
    · nlinarith
    · nlinarith

/-- A chain of `n` steps of length `≤ 1` along the geodesic from `z` to `w`, when `d(z, w) ≤ n`. -/
theorem s24q_nb_chain (z w : UpperHalfPlane) (n : ℕ) (hn : 0 < n) (hd : dist z w ≤ n) :
    ∃ u : ℕ → UpperHalfPlane, u 0 = z ∧ u n = w ∧ ∀ i, dist (u i) (u (i + 1)) ≤ 1 := by
  obtain ⟨g, hz, hw⟩ := s24q_nb_exists_vertical z w
  have hz' : (g • z) = UpperHalfPlane.mk ⟨0, (g • z).im⟩ (g • z).im_pos := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · simpa using hz
    · rfl
  have hw' : (g • w) = UpperHalfPlane.mk ⟨0, (g • w).im⟩ (g • w).im_pos := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · simpa using hw
    · rfl
  obtain ⟨y, hy, hyz⟩ : ∃ y : ℝ, ∃ hy : 0 < y, g • z = UpperHalfPlane.mk ⟨0, y⟩ hy := ⟨_, (g • z).im_pos, hz'⟩
  obtain ⟨y', hy', hyw⟩ : ∃ y' : ℝ, ∃ hy' : 0 < y', g • w = UpperHalfPlane.mk ⟨0, y'⟩ hy' := ⟨_, (g • w).im_pos, hw'⟩
  let p : ℝ → UpperHalfPlane := fun s =>
    UpperHalfPlane.mk ⟨0, Real.exp ((1 - s) * Real.log y + s * Real.log y')⟩ (Real.exp_pos _)
  have hp0 : p 0 = g • z := by
    rw [hyz]
    apply UpperHalfPlane.ext
    apply Complex.ext
    · rfl
    · show Real.exp ((1 - 0) * Real.log y + 0 * Real.log y') = y
      simp [Real.exp_log hy]
  have hp1 : p 1 = g • w := by
    rw [hyw]
    apply UpperHalfPlane.ext
    apply Complex.ext
    · rfl
    · show Real.exp ((1 - 1) * Real.log y + 1 * Real.log y') = y'
      simp [Real.exp_log hy']
  have hpd : ∀ s t : ℝ, dist (p s) (p t) = |s - t| * |Real.log y - Real.log y'| := by
    intro s t
    have h := s24q_nb_dist_vertical (Real.exp ((1 - s) * Real.log y + s * Real.log y'))
      (Real.exp ((1 - t) * Real.log y + t * Real.log y')) (Real.exp_pos _) (Real.exp_pos _)
    show dist (UpperHalfPlane.mk _ _) (UpperHalfPlane.mk _ _) = _
    rw [h, Real.log_exp, Real.log_exp, ← abs_mul, ← abs_neg]
    congr 1
    ring
  have hD : dist z w = |Real.log y - Real.log y'| := by
    rw [← dist_smul g z w, hyz, hyw, s24q_nb_dist_vertical]
  let σ : ℕ → ℝ := fun i => (min (i : ℝ) n) / n
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨fun i => g⁻¹ • p (σ i), ?_, ?_, fun i => ?_⟩
  · have : σ 0 = 0 := by simp [σ]
    simp only [this, hp0, inv_smul_smul]
  · have : σ n = 1 := by simp [σ, hnr.ne']
    simp only [this, hp1, inv_smul_smul]
  · rw [dist_smul, hpd]
    have h1 : |σ i - σ (i + 1)| ≤ 1 / n := by
      have e : σ i - σ (i + 1) = (min (i : ℝ) n - min ((i + 1 : ℕ) : ℝ) n) / n := by simp [σ, sub_div]
      rw [e, abs_div, abs_of_pos hnr, div_le_div_iff_of_pos_right hnr]
      push_cast
      rw [abs_le]
      constructor
      · rcases le_total (i : ℝ) n with h | h
        · rcases le_total ((i : ℝ) + 1) n with h' | h'
          · rw [min_eq_left h, min_eq_left h']; linarith
          · rw [min_eq_left h, min_eq_right h']; linarith
        · have h' : (n : ℝ) ≤ i + 1 := by linarith
          rw [min_eq_right h, min_eq_right h']; linarith
      · rcases le_total (i : ℝ) n with h | h
        · rcases le_total ((i : ℝ) + 1) n with h' | h'
          · rw [min_eq_left h, min_eq_left h']; linarith
          · rw [min_eq_left h, min_eq_right h']; linarith
        · have h' : (n : ℝ) ≤ i + 1 := by linarith
          rw [min_eq_right h, min_eq_right h']; linarith
    calc |σ i - σ (i + 1)| * |Real.log y - Real.log y'| ≤ (1 / n) * |Real.log y - Real.log y'| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = dist z w / n := by rw [hD]; ring
      _ ≤ 1 := by rw [div_le_one hnr]; exact hd

/-- Coarse Lipschitz bound at unit scale: a map conjugating a cocompact group to a group of isometries moves points at
distance `≤ 1` by a bounded amount. -/
theorem s24q_nb_coarse_unit {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (F : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hK₀ : ∃ K : Set UpperHalfPlane, IsCompact K ∧ ∀ z, ∃ γ ∈ Γ₀, γ • z ∈ K)
    (hdeck : ∀ γ ∈ Γ₀, ∃ δ ∈ Γ₁, ∀ τ, F (γ • τ) = δ • F τ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z w : UpperHalfPlane, dist z w ≤ 1 → dist (F z) (F w) ≤ B := by
  obtain ⟨K, hKc, hK⟩ := hK₀
  have hKc' : IsCompact (Metric.cthickening 1 K) := hKc.cthickening
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 (hKc'.image F.continuous).isBounded
  refine ⟨max C 0, le_max_right _ _, fun z w hzw => ?_⟩
  obtain ⟨γ, hγ, hγK⟩ := hK z
  obtain ⟨δ, -, hδ⟩ := hdeck γ hγ
  have h1 : γ • w ∈ Metric.cthickening 1 K := by
    refine Metric.mem_cthickening_of_dist_le (γ • w) (γ • z) 1 K hγK ?_
    rw [dist_smul, UpperHalfPlane.dist_comm]
    exact hzw
  have h2 : γ • z ∈ Metric.cthickening 1 K := Metric.self_subset_cthickening _ hγK
  have h3 : dist (F (γ • z)) (F (γ • w)) ≤ C := hC (mem_image_of_mem F h2) (mem_image_of_mem F h1)
  rw [hδ, hδ, dist_smul] at h3
  exact h3.trans (le_max_left _ _)

/-- A coarsely Lipschitz bound at unit scale gives the linear bound, by the chain along geodesics. -/
theorem s24q_nb_coarse_lip (F : UpperHalfPlane → UpperHalfPlane) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ z w : UpperHalfPlane, dist z w ≤ 1 → dist (F z) (F w) ≤ B) (z w : UpperHalfPlane) :
    dist (F z) (F w) ≤ B * dist z w + B := by
  set n : ℕ := max 1 ⌈dist z w⌉₊ with hn
  have hn0 : 0 < n := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hdn : dist z w ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have hnd : (n : ℝ) ≤ dist z w + 1 := by
    rcases max_choice 1 ⌈dist z w⌉₊ with h | h
    · rw [hn, h]
      simp
    · rw [hn, h]
      exact (Nat.ceil_lt_add_one dist_nonneg).le
  obtain ⟨u, hu0, hun, hstep⟩ := s24q_nb_chain z w n hn0 hdn
  have hsum : dist (F (u 0)) (F (u n)) ≤ ∑ i ∈ Finset.range n, dist (F (u i)) (F (u (i + 1))) :=
    dist_le_range_sum_dist (fun i => F (u i)) n
  have hle : ∑ i ∈ Finset.range n, dist (F (u i)) (F (u (i + 1))) ≤ ∑ _i ∈ Finset.range n, B :=
    Finset.sum_le_sum fun i _ => hB _ _ (hstep i)
  rw [hu0, hun] at hsum
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
  calc dist (F z) (F w) ≤ n * B := hsum.trans hle
    _ ≤ (dist z w + 1) * B := mul_le_mul_of_nonneg_right hnd hB0
    _ = B * dist z w + B := by ring

/-- **A.** The lift `F` of a homeomorphism between compact surfaces uniformized by Fuchsian groups is a
quasi-isometry of the hyperbolic plane: `F` conjugates the cocompact groups `Γ₀`, `Γ₁` (cocompactness: a compact set
meets every orbit), so `F` is coarsely Lipschitz on unit scale (the closed `1`-neighbourhood of the compact set has
compact `F`-image) and coarsely Lipschitz in the other direction by the same argument for `F⁻¹`. -/
theorem s24q_nb_qi {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (F : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hK₀ : ∃ K : Set UpperHalfPlane, IsCompact K ∧ ∀ z, ∃ γ ∈ Γ₀, γ • z ∈ K)
    (hK₁ : ∃ K : Set UpperHalfPlane, IsCompact K ∧ ∀ z, ∃ δ ∈ Γ₁, δ • z ∈ K)
    (hdeck : ∀ γ ∈ Γ₀, ∃ δ ∈ Γ₁, ∀ τ, F (γ • τ) = δ • F τ)
    (hdeck' : ∀ δ ∈ Γ₁, ∃ γ ∈ Γ₀, ∀ τ, F (γ • τ) = δ • F τ) :
    ∃ L c : ℝ, 1 ≤ L ∧ 0 ≤ c ∧ ∀ z w : UpperHalfPlane,
      dist z w / L - c ≤ dist (F z) (F w) ∧ dist (F z) (F w) ≤ L * dist z w + c := by
  obtain ⟨B₁, hB₁0, hB₁⟩ := s24q_nb_coarse_unit F hK₀ hdeck
  have hdeck'' : ∀ δ ∈ Γ₁, ∃ γ ∈ Γ₀, ∀ τ, F.symm (δ • τ) = γ • F.symm τ := by
    intro δ hδ
    obtain ⟨γ, hγ, h⟩ := hdeck' δ hδ
    refine ⟨γ, hγ, fun τ => ?_⟩
    have := h (F.symm τ)
    rw [F.apply_symm_apply] at this
    rw [← this, F.symm_apply_apply]
  obtain ⟨B₂, hB₂0, hB₂⟩ := s24q_nb_coarse_unit F.symm hK₁ hdeck''
  set L : ℝ := max (max B₁ B₂) 1 with hL
  have hL1 : 1 ≤ L := le_max_right _ _
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
  have hB₁L : B₁ ≤ L := (le_max_left _ _).trans (le_max_left _ _)
  have hB₂L : B₂ ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨L, L, hL1, hL0.le, fun z w => ⟨?_, ?_⟩⟩
  · have h := s24q_nb_coarse_lip F.symm hB₂0 hB₂ (F z) (F w)
    rw [F.symm_apply_apply, F.symm_apply_apply] at h
    rw [sub_le_iff_le_add, div_le_iff₀ hL0]
    have h1 : dist z w ≤ L * dist (F z) (F w) + L := by
      calc dist z w ≤ B₂ * dist (F z) (F w) + B₂ := h
        _ ≤ L * dist (F z) (F w) + L :=
          add_le_add (mul_le_mul_of_nonneg_right hB₂L dist_nonneg) hB₂L
    nlinarith
  · have h := s24q_nb_coarse_lip F hB₁0 hB₁ z w
    calc dist (F z) (F w) ≤ B₁ * dist z w + B₁ := h
      _ ≤ L * dist z w + L := add_le_add (mul_le_mul_of_nonneg_right hB₁L dist_nonneg) hB₁L

/-- **Fermi coordinates around the imaginary axis.** `T p = log |p|` (the position of the projection on the axis) and
`D p = arsinh (Re p / Im p)` (the signed distance to the axis) satisfy the hyperbolic law of cosines in these
coordinates. -/
theorem s24q_nb_coords : ∃ T D : UpperHalfPlane → ℝ,
    (∀ p q : UpperHalfPlane, Real.cosh (dist p q) =
      Real.cosh (D p) * Real.cosh (D q) * Real.cosh (T p - T q) - Real.sinh (D p) * Real.sinh (D q)) ∧
    (∀ p : UpperHalfPlane, D p = 0 ↔ (p : ℂ).re = 0) ∧
    (∀ (y : ℝ) (hy : 0 < y), T (UpperHalfPlane.mk ⟨0, y⟩ hy) = Real.log y) := by
  refine ⟨fun p => Real.log ‖(p : ℂ)‖, fun p => Real.arsinh ((p : ℂ).re / (p : ℂ).im), ?_, ?_, ?_⟩
  · intro p q
    have hy : 0 < (p : ℂ).im := p.im_pos
    have hy' : 0 < (q : ℂ).im := q.im_pos
    obtain ⟨x, hx⟩ : ∃ x, x = (p : ℂ).re := ⟨_, rfl⟩
    obtain ⟨y, hyy⟩ : ∃ y, y = (p : ℂ).im := ⟨_, rfl⟩
    obtain ⟨x', hx'⟩ : ∃ x', x' = (q : ℂ).re := ⟨_, rfl⟩
    obtain ⟨y', hyy'⟩ : ∃ y', y' = (q : ℂ).im := ⟨_, rfl⟩
    rw [← hyy] at hy
    rw [← hyy'] at hy'
    have hρ : ‖(p : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, ← hx, ← hyy]; ring
    have hρ' : ‖(q : ℂ)‖ ^ 2 = x' ^ 2 + y' ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, ← hx', ← hyy']; ring
    have hρpos : 0 < ‖(p : ℂ)‖ := norm_pos_iff.2 p.ne_zero
    have hρpos' : 0 < ‖(q : ℂ)‖ := norm_pos_iff.2 q.ne_zero
    have hd2 : dist (p : ℂ) (q : ℂ) ^ 2 = (x - x') ^ 2 + (y - y') ^ 2 := by
      rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, ← hx, ← hx', ← hyy, ← hyy']
      ring
    have e1y : p.im = y := hyy.symm
    have e2y : q.im = y' := hyy'.symm
    rw [UpperHalfPlane.cosh_dist, e1y, e2y, hd2]
    show _ = Real.cosh (Real.arsinh ((p : ℂ).re / (p : ℂ).im)) * Real.cosh (Real.arsinh ((q : ℂ).re / (q : ℂ).im)) *
      Real.cosh (Real.log ‖(p : ℂ)‖ - Real.log ‖(q : ℂ)‖) -
      Real.sinh (Real.arsinh ((p : ℂ).re / (p : ℂ).im)) * Real.sinh (Real.arsinh ((q : ℂ).re / (q : ℂ).im))
    rw [← hx, ← hyy, ← hx', ← hyy', Real.cosh_arsinh, Real.cosh_arsinh, Real.sinh_arsinh, Real.sinh_arsinh]
    have e1 : Real.sqrt (1 + (x / y) ^ 2) = ‖(p : ℂ)‖ / y := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
      field_simp
      nlinarith [hρ]
    have e2 : Real.sqrt (1 + (x' / y') ^ 2) = ‖(q : ℂ)‖ / y' := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
      field_simp
      nlinarith [hρ']
    have e3 : Real.cosh (Real.log ‖(p : ℂ)‖ - Real.log ‖(q : ℂ)‖) =
        (‖(p : ℂ)‖ / ‖(q : ℂ)‖ + ‖(q : ℂ)‖ / ‖(p : ℂ)‖) / 2 := by
      rw [Real.cosh_eq, Real.exp_sub, Real.exp_neg, Real.exp_sub, Real.exp_log hρpos, Real.exp_log hρpos']
      field_simp
    rw [e1, e2, e3]
    field_simp
    nlinarith [hρ, hρ']
  · intro p
    have hy : 0 < (p : ℂ).im := p.im_pos
    show Real.arsinh ((p : ℂ).re / (p : ℂ).im) = 0 ↔ _
    rw [Real.arsinh_eq_zero_iff, div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd h hy.ne'
    · intro h
      exact Or.inl h
  · intro y hy
    show Real.log ‖((UpperHalfPlane.mk ⟨0, y⟩ hy : UpperHalfPlane) : ℂ)‖ = Real.log y
    congr 1
    show ‖(⟨0, y⟩ : ℂ)‖ = y
    rw [Complex.norm_def, Complex.normSq_apply]
    simp
    rw [Real.sqrt_mul_self hy.le]

/-- Discrete intermediate value theorem, increasing case. -/
theorem s24q_nb_ivt (f : ℕ → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) (n : ℕ)
    (hstep : ∀ i < n, |f i - f (i + 1)| ≤ lam) {t : ℝ} (h0 : f 0 ≤ t) (hn : t ≤ f n) :
    ∃ i ≤ n, |f i - t| ≤ lam := by
  induction n with
  | zero =>
    refine ⟨0, le_refl _, ?_⟩
    have : f 0 = t := le_antisymm h0 hn
    rw [this, sub_self, abs_zero]
    exact hlam
  | succ n ih =>
    by_cases h : t ≤ f n
    · obtain ⟨i, hi, hi'⟩ := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi)) h
      exact ⟨i, hi.trans (Nat.le_succ n), hi'⟩
    · push Not at h
      refine ⟨n, Nat.le_succ n, ?_⟩
      have h1 := hstep n (Nat.lt_succ_self n)
      rw [abs_le] at h1 ⊢
      constructor <;> linarith [h1.1, h1.2]

/-- Discrete intermediate value theorem, both orders. -/
theorem s24q_nb_ivt' (f : ℕ → ℝ) (lam : ℝ) (hlam : 0 ≤ lam) (n : ℕ)
    (hstep : ∀ i < n, |f i - f (i + 1)| ≤ lam) {t : ℝ}
    (h : (f 0 ≤ t ∧ t ≤ f n) ∨ (f n ≤ t ∧ t ≤ f 0)) : ∃ i ≤ n, |f i - t| ≤ lam := by
  rcases h with ⟨h0, hn⟩ | ⟨hn, h0⟩
  · exact s24q_nb_ivt f lam hlam n hstep h0 hn
  · obtain ⟨i, hi, hi'⟩ := s24q_nb_ivt (fun i => -f i) lam hlam n
      (fun i hi => by
        have := hstep i hi
        rw [show -f i - -f (i + 1) = -(f i - f (i + 1)) by ring, abs_neg]
        exact this)
      (t := -t) (neg_le_neg h0) (neg_le_neg hn)
    refine ⟨i, hi, ?_⟩
    rw [show -f i - -t = -(f i - t) by ring, abs_neg] at hi'
    exact hi'

/-- Overshoot bound: a coarsely continuous sequence on `ℝ` that is coarsely injective at scale `A`, `B`
stays within `Q` of the interval spanned by its end points (lower side). -/
theorem s24q_nb_overshoot_low {n : ℕ} (t : ℕ → ℝ) {lam A B E : ℝ} (hlam : 0 ≤ lam)
    (hstep : ∀ i < n, |t i - t (i + 1)| ≤ lam)
    (hlow : ∀ i ≤ n, ∀ k ≤ n, |(i : ℝ) - k| ≤ A * |t i - t k| + B)
    (hup : ∀ i ≤ n, ∀ k ≤ n, |t i - t k| ≤ E * |(i : ℝ) - k| + E) (hE : 0 ≤ E) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ i ≤ n, min (t 0) (t n) - (E * (A * lam + B) + E) ≤ t i := by
  intro i hi
  by_contra hcon
  push Not at hcon
  set Q := E * (A * lam + B) + E with hQ
  have hQ0 : 0 ≤ Q := by
    have := mul_nonneg hE (add_nonneg (mul_nonneg hA hlam) hB)
    linarith
  rcases le_total (t 0) (t n) with h | h
  · rw [min_eq_left h] at hcon
    -- the sequence passes from `t i < t 0` to `t n ≥ t 0` after index `i`
    obtain ⟨i', hi', hi''⟩ := s24q_nb_ivt' (fun s => t (i + s)) lam hlam (n - i)
      (fun s hs => by
        have := hstep (i + s) (by omega)
        simpa [Nat.add_assoc] using this)
      (t := t 0) (Or.inl ⟨by simp only [Nat.add_zero]; linarith, by simpa [Nat.add_sub_cancel' hi] using h⟩)
    have hii : i + i' ≤ n := by omega
    have h1 := hlow (i + i') hii 0 (Nat.zero_le _)
    simp only [Nat.cast_zero, sub_zero, Nat.abs_cast] at h1
    have h2 : |t (i + i') - t 0| ≤ lam := hi''
    have h3 : (i : ℝ) ≤ A * lam + B := by
      have : ((i + i' : ℕ) : ℝ) ≤ A * lam + B := by
        calc ((i + i' : ℕ) : ℝ) ≤ A * |t (i + i') - t 0| + B := by simpa using h1
          _ ≤ A * lam + B := by gcongr
      have hle : (i : ℝ) ≤ ((i + i' : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right i i'
      linarith
    have h4 := hup i hi 0 (Nat.zero_le _)
    simp only [Nat.cast_zero, sub_zero, Nat.abs_cast] at h4
    have h5 : |t i - t 0| ≤ Q := by
      calc |t i - t 0| ≤ E * i + E := h4
        _ ≤ E * (A * lam + B) + E := by gcongr
    rw [abs_le] at h5
    linarith [h5.1]
  · rw [min_eq_right h] at hcon
    -- the sequence passes from `t 0 ≥ t n` down to `t i < t n` before index `i`
    obtain ⟨s, hs, hs'⟩ := s24q_nb_ivt' (fun s => t s) lam hlam i
      (fun s hs => hstep s (by omega)) (t := t n) (Or.inr ⟨by linarith, h⟩)
    have h1 := hlow s (by omega) n le_rfl
    have h2 : |t s - t n| ≤ lam := hs'
    have h3 : ((n : ℝ) - s) ≤ A * lam + B := by
      have : |(s : ℝ) - n| ≤ A * lam + B := by
        calc |(s : ℝ) - n| ≤ A * |t s - t n| + B := h1
          _ ≤ A * lam + B := by gcongr
      have hsn : (s : ℝ) ≤ n := by exact_mod_cast (show s ≤ n by omega)
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hsn)] at this
      exact this
    have h4 := hup i hi n le_rfl
    have hsi : (s : ℝ) ≤ i := by exact_mod_cast hs
    have h6 : (n : ℝ) - i ≤ A * lam + B := by linarith
    have h7 : |(i : ℝ) - n| = n - i := by
      rw [abs_sub_comm, abs_of_nonneg]
      exact sub_nonneg.2 (by exact_mod_cast hi)
    have h5 : |t i - t n| ≤ Q := by
      calc |t i - t n| ≤ E * |(i : ℝ) - n| + E := h4
        _ = E * (n - i) + E := by rw [h7]
        _ ≤ E * (A * lam + B) + E := by gcongr
    rw [abs_le] at h5
    linarith [h5.1]

theorem s24q_nb_overshoot {n : ℕ} (t : ℕ → ℝ) {lam A B E : ℝ} (hlam : 0 ≤ lam)
    (hstep : ∀ i < n, |t i - t (i + 1)| ≤ lam)
    (hlow : ∀ i ≤ n, ∀ k ≤ n, |(i : ℝ) - k| ≤ A * |t i - t k| + B)
    (hup : ∀ i ≤ n, ∀ k ≤ n, |t i - t k| ≤ E * |(i : ℝ) - k| + E) (hE : 0 ≤ E) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ i ≤ n, min (t 0) (t n) - (E * (A * lam + B) + E) ≤ t i ∧
      t i ≤ max (t 0) (t n) + (E * (A * lam + B) + E) := by
  intro i hi
  refine ⟨s24q_nb_overshoot_low t hlam hstep hlow hup hE hA hB i hi, ?_⟩
  have e : ∀ a b : ℝ, |(-a) - (-b)| = |a - b| := fun a b => by
    rw [show -a - -b = -(a - b) by ring, abs_neg]
  have := s24q_nb_overshoot_low (n := n) (fun s => - t s) hlam
    (fun i hi => by rw [e]; exact hstep i hi)
    (fun i hi k hk => by rw [e]; exact hlow i hi k hk)
    (fun i hi k hk => by rw [e]; exact hup i hi k hk) hE hA hB i hi
  have h2 : min (-t 0) (-t n) = -max (t 0) (t n) := min_neg_neg _ _
  simp only [h2] at this
  linarith

/-- `cosh x - 1 = 2 sinh (x/2)²`. -/
theorem s24q_nb_cosh_sub_one_eq (x : ℝ) : Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
  have h := Real.cosh_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  nlinarith [Real.cosh_sq (x / 2)]

/-- `1 + x²/2 ≤ cosh x`. -/
theorem s24q_nb_one_add_sq_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h1 := s24q_nb_cosh_sub_one_eq x
  have h2 : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := by
    rcases le_total 0 (x / 2) with h | h
    · have := Real.self_le_sinh_iff.2 h
      exact pow_le_pow_left₀ h this 2
    · have h' : 0 ≤ -(x / 2) := by linarith
      have := Real.self_le_sinh_iff.2 h'
      rw [Real.sinh_neg] at this
      have h3 : x / 2 ≥ Real.sinh (x / 2) := by linarith
      nlinarith [Real.sinh_nonpos_iff.2 h]
  nlinarith

/-- `cosh x - 1 ≤ x² e^x / 2` for `x ≥ 0`. -/
theorem s24q_nb_cosh_sub_one_le (x : ℝ) (hx : 0 ≤ x) : Real.cosh x - 1 ≤ x ^ 2 * Real.exp x / 2 := by
  have h1 := s24q_nb_cosh_sub_one_eq x
  have h2 : Real.sinh (x / 2) ≤ x / 2 * Real.exp (x / 2) := by
    have hx2 : 0 ≤ x / 2 := by positivity
    set y := x / 2 with hy
    have e1 : 1 - y ≤ Real.exp (-y) := by linarith [Real.add_one_le_exp (-y)]
    have e2 : Real.exp y - 1 ≤ y * Real.exp y := by
      have := mul_le_mul_of_nonneg_right e1 (Real.exp_pos y).le
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
      nlinarith
    rw [Real.sinh_eq]
    have e3 : Real.exp (-y) ≥ 1 - y := e1
    nlinarith [Real.exp_pos y, Real.exp_pos (-y), Real.exp_neg y, mul_nonneg hx2 (Real.exp_pos y).le]
  have h3 : 0 ≤ Real.sinh (x / 2) := Real.sinh_nonneg_iff.2 (by positivity)
  rw [h1]
  have h4 : Real.sinh (x / 2) ^ 2 ≤ (x / 2 * Real.exp (x / 2)) ^ 2 := by gcongr
  have h5 : (x / 2 * Real.exp (x / 2)) ^ 2 = x ^ 2 / 4 * Real.exp x := by
    rw [mul_pow, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (x / 2) = x := by push_cast; ring
    rw [this]
    ring
  nlinarith

/-- Exponential beats a quadratic: if `exp (μ m / 2) ≤ A + B m²` with `m ≥ 1`, then `m` is bounded. -/
theorem s24q_nb_exp_poly {μ A B : ℝ} (hμ : 0 < μ) (hA : 0 ≤ A) (hB : 0 ≤ B) {m : ℝ} (hm : 1 ≤ m)
    (h : Real.exp (μ * m / 2) ≤ A + B * m ^ 2) : m ≤ 48 * (A + B) / μ ^ 3 := by
  have h1 := Real.pow_div_factorial_le_exp (μ * m / 2) (by positivity) 3
  have h2 : (μ * m / 2) ^ 3 / (Nat.factorial 3 : ℝ) = μ ^ 3 * m ^ 3 / 48 := by
    norm_num [Nat.factorial]
    ring
  rw [h2] at h1
  have hm2 : 1 ≤ m ^ 2 := by nlinarith
  have h3 : μ ^ 3 * m ^ 3 / 48 ≤ (A + B) * m ^ 2 := by
    calc μ ^ 3 * m ^ 3 / 48 ≤ A + B * m ^ 2 := h1.trans h
      _ ≤ A * m ^ 2 + B * m ^ 2 := by nlinarith
      _ = (A + B) * m ^ 2 := by ring
  rw [le_div_iff₀ (by positivity)]
  have hm0 : 0 < m ^ 2 := by positivity
  nlinarith

/-- Splitting of the law of cosines: `cosh d = cosh (ΔD) + cosh D cosh D' (cosh ΔT - 1)`. -/
theorem s24q_nb_cosh_split {T D : UpperHalfPlane → ℝ}
    (hstar : ∀ p q : UpperHalfPlane, Real.cosh (dist p q) =
      Real.cosh (D p) * Real.cosh (D q) * Real.cosh (T p - T q) - Real.sinh (D p) * Real.sinh (D q))
    (p q : UpperHalfPlane) :
    Real.cosh (dist p q) = Real.cosh (D p - D q) +
      Real.cosh (D p) * Real.cosh (D q) * (Real.cosh (T p - T q) - 1) := by
  rw [hstar p q, Real.cosh_sub (D p) (D q)]
  ring

theorem s24q_nb_dD_le {T D : UpperHalfPlane → ℝ}
    (hstar : ∀ p q : UpperHalfPlane, Real.cosh (dist p q) =
      Real.cosh (D p) * Real.cosh (D q) * Real.cosh (T p - T q) - Real.sinh (D p) * Real.sinh (D q))
    (p q : UpperHalfPlane) : |D p - D q| ≤ dist p q := by
  have h := s24q_nb_cosh_split hstar p q
  have h1 : Real.cosh (D p - D q) ≤ Real.cosh (dist p q) := by
    rw [h]
    have : 0 ≤ Real.cosh (D p) * Real.cosh (D q) * (Real.cosh (T p - T q) - 1) :=
      mul_nonneg (mul_nonneg (Real.cosh_pos _).le (Real.cosh_pos _).le) (by linarith [Real.one_le_cosh (T p - T q)])
    linarith
  have := Real.cosh_le_cosh.1 h1
  rwa [abs_of_nonneg dist_nonneg] at this

theorem s24q_nb_dT_le {T D : UpperHalfPlane → ℝ}
    (hstar : ∀ p q : UpperHalfPlane, Real.cosh (dist p q) =
      Real.cosh (D p) * Real.cosh (D q) * Real.cosh (T p - T q) - Real.sinh (D p) * Real.sinh (D q))
    (p q : UpperHalfPlane) : |T p - T q| ≤ dist p q := by
  have h := s24q_nb_cosh_split hstar p q
  have hc1 : 1 ≤ Real.cosh (D p) * Real.cosh (D q) := by
    nlinarith [Real.one_le_cosh (D p), Real.one_le_cosh (D q)]
  have hct := Real.one_le_cosh (T p - T q)
  have hsub := Real.one_le_cosh (D p - D q)
  have h1 : Real.cosh (T p - T q) ≤ Real.cosh (dist p q) := by
    rw [h]
    nlinarith [mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 hct)]
  have := Real.cosh_le_cosh.1 h1
  rwa [abs_of_nonneg dist_nonneg] at this

/-- The distance to a point `q` of the axis is at most `|D p| + |ΔT|`. -/
theorem s24q_nb_dist_le_axis {T D : UpperHalfPlane → ℝ}
    (hstar : ∀ p q : UpperHalfPlane, Real.cosh (dist p q) =
      Real.cosh (D p) * Real.cosh (D q) * Real.cosh (T p - T q) - Real.sinh (D p) * Real.sinh (D q))
    (p q : UpperHalfPlane) (hq : D q = 0) : dist p q ≤ |D p| + |T p - T q| := by
  have h := hstar p q
  rw [hq, Real.cosh_zero, Real.sinh_zero] at h
  have h1 : Real.cosh (dist p q) ≤ Real.cosh (|D p| + |T p - T q|) := by
    rw [h, Real.cosh_add, mul_one, mul_zero, sub_zero, ← Real.cosh_abs (D p), ← Real.cosh_abs (T p - T q)]
    nlinarith [Real.sinh_nonneg_iff.2 (abs_nonneg (D p)), Real.sinh_nonneg_iff.2 (abs_nonneg (T p - T q))]
  have := Real.cosh_le_cosh.1 h1
  rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))] at this

/-- **Contraction of the projection** away from the axis: two points of depth `≥ r` at distance `≤ λ` have projections
within `C / cosh r`, `C = √(2 (cosh λ - 1))`. -/
theorem s24q_nb_contract {T D : UpperHalfPlane → ℝ}
    (hstar : ∀ p q : UpperHalfPlane, Real.cosh (dist p q) =
      Real.cosh (D p) * Real.cosh (D q) * Real.cosh (T p - T q) - Real.sinh (D p) * Real.sinh (D q))
    (p q : UpperHalfPlane) {lam r : ℝ} (hr : 0 ≤ r) (hd : dist p q ≤ lam) (hp : r ≤ |D p|) (hq : r ≤ |D q|) :
    |T p - T q| ≤ Real.sqrt (2 * (Real.cosh lam - 1)) / Real.cosh r := by
  have h := s24q_nb_cosh_split hstar p q
  have hcr : 0 < Real.cosh r := Real.cosh_pos r
  have hcp : Real.cosh r ≤ Real.cosh (D p) := by
    rw [← Real.cosh_abs (D p)]; exact Real.cosh_le_cosh.2 (by rw [abs_of_nonneg hr, abs_abs]; assumption)
  have hcq : Real.cosh r ≤ Real.cosh (D q) := by
    rw [← Real.cosh_abs (D q)]; exact Real.cosh_le_cosh.2 (by rw [abs_of_nonneg hr, abs_abs]; assumption)
  have hdl : Real.cosh (dist p q) ≤ Real.cosh lam :=
    Real.cosh_le_cosh.2 (by rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg (dist_nonneg.trans hd)])
  have hsub := Real.one_le_cosh (D p - D q)
  have hct : 0 ≤ Real.cosh (T p - T q) - 1 := by linarith [Real.one_le_cosh (T p - T q)]
  have h1 : Real.cosh r * Real.cosh r * (Real.cosh (T p - T q) - 1) ≤ Real.cosh lam - 1 := by
    have : Real.cosh r * Real.cosh r ≤ Real.cosh (D p) * Real.cosh (D q) :=
      mul_le_mul hcp hcq hcr.le (hcr.le.trans hcp)
    nlinarith [mul_le_mul_of_nonneg_right this hct]
  have h2 : (T p - T q) ^ 2 / 2 ≤ Real.cosh (T p - T q) - 1 := by
    have := s24q_nb_one_add_sq_le_cosh (T p - T q)
    linarith
  have h3 : (T p - T q) ^ 2 * (Real.cosh r) ^ 2 ≤ 2 * (Real.cosh lam - 1) := by
    nlinarith [mul_le_mul_of_nonneg_left h2 (mul_self_nonneg (Real.cosh r))]
  have h4 : |T p - T q| * Real.cosh r ≤ Real.sqrt (2 * (Real.cosh lam - 1)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_abs (T p - T q)]
  rw [le_div_iff₀ hcr]
  exact h4

/-- `e^x ≤ 2 cosh x`. -/
theorem s24q_nb_exp_le_two_cosh (x : ℝ) : Real.exp x ≤ 2 * Real.cosh x := by
  rw [Real.cosh_eq]
  have := Real.exp_pos (-x)
  linarith

/-- `cosh (a + b) ≤ e^b cosh a` for `b ≥ 0`. -/
theorem s24q_nb_cosh_add_le (a b : ℝ) (hb : 0 ≤ b) : Real.cosh (a + b) ≤ Real.exp b * Real.cosh a := by
  rw [Real.cosh_add]
  have h1 : Real.sinh a ≤ Real.cosh a := by
    rw [Real.sinh_eq, Real.cosh_eq]
    have := Real.exp_pos (-a)
    linarith
  have h2 : Real.cosh b + Real.sinh b = Real.exp b := by
    rw [Real.cosh_eq, Real.sinh_eq]; ring
  have h3 : 0 ≤ Real.sinh b := Real.sinh_nonneg_iff.2 hb
  nlinarith [Real.cosh_pos a, h3]

/-- **The excursion estimate.** A chain of `m` steps of size `≤ λ` which stays at depth `≥ r'` from the axis and whose end
points are at depth `≤ r' + λ` on the same side is at most `m₁` steps long, provided `r'` is large, because the
projection to the axis moves at most `C / cosh r'` per step while the end points are `μ m - c` apart. -/
theorem s24q_nb_excursion {T D : UpperHalfPlane → ℝ}
    (hstar : ∀ p q : UpperHalfPlane, Real.cosh (dist p q) =
      Real.cosh (D p) * Real.cosh (D q) * Real.cosh (T p - T q) - Real.sinh (D p) * Real.sinh (D q))
    {lam μ c : ℝ} (hlam : 0 < lam) (hμ : 0 < μ) (hc : 0 ≤ c) (x : ℕ → UpperHalfPlane) {j k : ℕ} (hjk : j < k)
    {r' : ℝ} (hr' : Real.log (4 * Real.sqrt (2 * (Real.cosh lam - 1)) / μ) ≤ r') (hr'0 : 0 ≤ r')
    (hstep : ∀ i, j ≤ i → i < k → dist (x i) (x (i + 1)) ≤ lam)
    (hdepth : ∀ i, j ≤ i → i ≤ k → r' ≤ |D (x i)|)
    (hendj : |D (x j)| ≤ r' + lam) (hendk : |D (x k)| ≤ r' + lam)
    (hsame : |D (x j) - D (x k)| ≤ lam)
    (hlow : μ * ((k : ℝ) - j) - c ≤ dist (x j) (x k)) :
    ((k : ℝ) - j) ≤ 48 * (2 * Real.exp c * Real.cosh lam +
      Real.exp (c + 2 * lam) * Real.sqrt (2 * (Real.cosh lam - 1)) ^ 2) / μ ^ 3 := by
  set C := Real.sqrt (2 * (Real.cosh lam - 1)) with hC
  have hcoshlam : 1 < Real.cosh lam := by
    have := Real.one_lt_cosh.2 hlam.ne'
    exact this
  have hCpos : 0 < C := Real.sqrt_pos.2 (by linarith)
  set m : ℝ := (k : ℝ) - j with hm
  have hm1 : 1 ≤ m := by
    have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
    linarith
  -- (1) the projection moves little
  have hT : |T (x j) - T (x k)| ≤ m * (C / Real.cosh r') := by
    have h1 : dist (T (x j)) (T (x k)) ≤ ∑ i ∈ Finset.Ico j k, dist (T (x i)) (T (x (i + 1))) :=
      dist_le_Ico_sum_dist (fun i => T (x i)) hjk.le
    have h2 : ∀ i ∈ Finset.Ico j k, dist (T (x i)) (T (x (i + 1))) ≤ C / Real.cosh r' := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      rw [Real.dist_eq]
      exact s24q_nb_contract hstar (x i) (x (i + 1)) hr'0 (hstep i hi.1 hi.2) (hdepth i hi.1 hi.2.le)
        (hdepth (i + 1) (by omega) (by omega))
    have h3 := h1.trans (Finset.sum_le_sum h2)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h3
    rw [Real.dist_eq] at h3
    have : ((k - j : ℕ) : ℝ) = m := by
      rw [hm, Nat.cast_sub hjk.le]
    rwa [this] at h3
  set τ := m * (C / Real.cosh r') with hτ
  have hτ0 : 0 ≤ τ := by positivity
  -- (2) the law of cosines
  have hcos := s24q_nb_cosh_split hstar (x j) (x k)
  have hcj : Real.cosh (D (x j)) ≤ Real.cosh (r' + lam) := by
    rw [← Real.cosh_abs (D (x j))]
    exact Real.cosh_le_cosh.2 (by rw [abs_abs, abs_of_nonneg (show 0 ≤ r' + lam by linarith)]; assumption)
  have hck : Real.cosh (D (x k)) ≤ Real.cosh (r' + lam) := by
    rw [← Real.cosh_abs (D (x k))]
    exact Real.cosh_le_cosh.2 (by rw [abs_abs, abs_of_nonneg (show 0 ≤ r' + lam by linarith)]; assumption)
  have hcd : Real.cosh (D (x j) - D (x k)) ≤ Real.cosh lam :=
    Real.cosh_le_cosh.2 (by rwa [abs_of_nonneg hlam.le])
  have hcT : Real.cosh (T (x j) - T (x k)) ≤ Real.cosh τ :=
    Real.cosh_le_cosh.2 (by rwa [abs_of_nonneg hτ0])
  have hcT1 : 0 ≤ Real.cosh (T (x j) - T (x k)) - 1 := by linarith [Real.one_le_cosh (T (x j) - T (x k))]
  have hprod : Real.cosh (D (x j)) * Real.cosh (D (x k)) ≤ Real.cosh (r' + lam) ^ 2 := by
    rw [sq]
    exact mul_le_mul hcj hck (Real.cosh_pos _).le (Real.cosh_pos _).le
  have hcosh_d : Real.cosh (dist (x j) (x k)) ≤ Real.cosh lam + Real.cosh (r' + lam) ^ 2 * (Real.cosh τ - 1) := by
    rw [hcos]
    have := mul_le_mul hprod (sub_le_sub_right hcT 1) hcT1 (sq_nonneg _)
    linarith
  -- (3) comparison of cosh at depth r' + lam and r'
  have hshift : Real.cosh (r' + lam) ≤ Real.exp lam * Real.cosh r' := s24q_nb_cosh_add_le r' lam hlam.le
  have hcr' : 0 < Real.cosh r' := Real.cosh_pos r'
  -- (4) `cosh τ - 1 ≤ τ² e^τ / 2`
  have hct := s24q_nb_cosh_sub_one_le τ hτ0
  have hstuff : Real.cosh (r' + lam) ^ 2 * (Real.cosh τ - 1) ≤
      Real.exp (2 * lam) * (m ^ 2 * C ^ 2) * Real.exp τ / 2 := by
    have h1 : Real.cosh (r' + lam) ^ 2 ≤ Real.exp (2 * lam) * Real.cosh r' ^ 2 := by
      have := pow_le_pow_left₀ (Real.cosh_pos _).le hshift 2
      rwa [mul_pow, ← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * lam = 2 * lam by norm_num] at this
    have h2 : τ ^ 2 * Real.cosh r' ^ 2 = m ^ 2 * C ^ 2 := by
      rw [hτ]
      field_simp
    calc Real.cosh (r' + lam) ^ 2 * (Real.cosh τ - 1)
        ≤ (Real.exp (2 * lam) * Real.cosh r' ^ 2) * (τ ^ 2 * Real.exp τ / 2) :=
          mul_le_mul h1 hct (by linarith [Real.one_le_cosh τ]) (by positivity)
      _ = Real.exp (2 * lam) * (τ ^ 2 * Real.cosh r' ^ 2) * Real.exp τ / 2 := by ring
      _ = Real.exp (2 * lam) * (m ^ 2 * C ^ 2) * Real.exp τ / 2 := by rw [h2]
  -- (5) `τ ≤ μ m / 2`
  have hτle : τ ≤ μ * m / 2 := by
    have h1 : Real.exp r' ≤ 2 * Real.cosh r' := s24q_nb_exp_le_two_cosh r'
    have h2 : Real.exp (-r') ≤ μ / (4 * C) := by
      have : -r' ≤ -Real.log (4 * C / μ) := by linarith
      calc Real.exp (-r') ≤ Real.exp (-Real.log (4 * C / μ)) := Real.exp_le_exp.2 this
        _ = μ / (4 * C) := by
          rw [Real.exp_neg, Real.exp_log (by positivity)]
          field_simp
    have h3 : C / Real.cosh r' ≤ μ / 2 := by
      rw [div_le_iff₀ hcr']
      have : (1 : ℝ) = Real.exp r' * Real.exp (-r') := by rw [← Real.exp_add]; simp
      have h4 : C ≤ μ / 2 * Real.cosh r' := by
        have h5 : Real.exp r' * Real.exp (-r') = 1 := this.symm
        have h6 : C = C * (Real.exp r' * Real.exp (-r')) := by rw [h5, mul_one]
        have h7 : C * (Real.exp r' * Real.exp (-r')) ≤ C * ((2 * Real.cosh r') * (μ / (4 * C))) := by
          gcongr
        have h8 : C * ((2 * Real.cosh r') * (μ / (4 * C))) = μ / 2 * Real.cosh r' := by
          field_simp
          ring
        linarith
      exact h4
    calc τ = m * (C / Real.cosh r') := rfl
      _ ≤ m * (μ / 2) := by gcongr
      _ = μ * m / 2 := by ring
  -- (6), (7): exponential versus quadratic
  have hd1 : Real.exp (μ * m - c) ≤ Real.exp (dist (x j) (x k)) := Real.exp_le_exp.2 (by linarith)
  have hd2 : Real.exp (dist (x j) (x k)) ≤ 2 * Real.cosh (dist (x j) (x k)) := s24q_nb_exp_le_two_cosh _
  have hd3 : Real.exp (μ * m - c) ≤ 2 * Real.cosh lam + Real.exp (2 * lam) * C ^ 2 * m ^ 2 * Real.exp (μ * m / 2) := by
    have h1 : Real.exp τ ≤ Real.exp (μ * m / 2) := Real.exp_le_exp.2 hτle
    have h2 : Real.exp (2 * lam) * (m ^ 2 * C ^ 2) * Real.exp τ / 2 ≤
        Real.exp (2 * lam) * (m ^ 2 * C ^ 2) * Real.exp (μ * m / 2) / 2 := by gcongr
    linarith [hd1, hd2, hcosh_d, hstuff, h2]
  have hd4 : Real.exp (μ * m / 2) ≤ 2 * Real.exp c * Real.cosh lam +
      Real.exp (c + 2 * lam) * C ^ 2 * m ^ 2 := by
    -- from  e^{y} e^{y} e^{-c} ≤ 2 cosh λ + K m² e^{y}  deduce  e^y ≤ e^c (2 cosh λ + K m²)
    set y := μ * m / 2 with hy
    set K := Real.exp (2 * lam) * C ^ 2 * m ^ 2 with hK
    have h5 : Real.exp y * (Real.exp y * Real.exp (-c)) ≤ 2 * Real.cosh lam + K * Real.exp y := by
      have e1' : Real.exp y * (Real.exp y * Real.exp (-c)) = Real.exp (μ * m - c) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hy]; ring
      rw [e1']
      linarith [hd3]
    have h7 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    have hKnn : 0 ≤ K := by positivity
    have h6 : Real.exp y * Real.exp (-c) ≤ 2 * Real.cosh lam * Real.exp (-y) + K := by
      have e2' : Real.exp y * Real.exp (-c) = (Real.exp y * (Real.exp y * Real.exp (-c))) * Real.exp (-y) := by
        calc Real.exp y * Real.exp (-c) = (Real.exp y * Real.exp (-y)) * (Real.exp y * Real.exp (-c)) := by
              rw [h7, one_mul]
          _ = _ := by ring
      rw [e2']
      calc (Real.exp y * (Real.exp y * Real.exp (-c))) * Real.exp (-y)
          ≤ (2 * Real.cosh lam + K * Real.exp y) * Real.exp (-y) :=
            mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
        _ = 2 * Real.cosh lam * Real.exp (-y) + K * (Real.exp y * Real.exp (-y)) := by ring
        _ = 2 * Real.cosh lam * Real.exp (-y) + K := by rw [h7, mul_one]
    have h8 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by rw [hy]; nlinarith)
    have h9 : Real.exp y * Real.exp (-c) ≤ 2 * Real.cosh lam + K := by
      have : 2 * Real.cosh lam * Real.exp (-y) ≤ 2 * Real.cosh lam := by
        have := mul_le_mul_of_nonneg_left h8 (by linarith : (0 : ℝ) ≤ 2 * Real.cosh lam)
        linarith
      linarith
    have h10 := mul_le_mul_of_nonneg_right h9 (Real.exp_pos c).le
    have hec1 : Real.exp (-c) * Real.exp c = 1 := by rw [← Real.exp_add]; simp
    have h11 : Real.exp y * Real.exp (-c) * Real.exp c = Real.exp y := by
      rw [mul_assoc, hec1, mul_one]
    rw [h11] at h10
    have h12 : Real.exp (c + 2 * lam) = Real.exp c * Real.exp (2 * lam) := Real.exp_add _ _
    rw [h12]
    show Real.exp y ≤ _
    calc Real.exp y ≤ (2 * Real.cosh lam + K) * Real.exp c := h10
      _ = 2 * Real.exp c * Real.cosh lam + Real.exp c * Real.exp (2 * lam) * C ^ 2 * m ^ 2 := by
        rw [hK]; ring
  exact s24q_nb_exp_poly hμ (by positivity) (by positivity) hm1 hd4

/-- A real sequence with steps `≤ λ` that stays `> λ` away from `0` keeps its sign. -/
theorem s24q_nb_sign_chain (f : ℕ → ℝ) {lam : ℝ} (hlam : 0 ≤ lam) {j k : ℕ} (hjk : j ≤ k)
    (hstep : ∀ i, j ≤ i → i < k → |f i - f (i + 1)| ≤ lam) (hbig : ∀ i, j ≤ i → i ≤ k → lam < |f i|) :
    0 < f j * f k := by
  induction k, hjk using Nat.le_induction with
  | base =>
    have h := hbig j le_rfl le_rfl
    have : f j ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      linarith
    exact mul_self_pos.2 this
  | succ k hk ih =>
    have ih' := ih (fun i hi hik => hstep i hi (Nat.lt_succ_of_lt hik)) (fun i hi hik => hbig i hi (by omega))
    have h1 := hstep k hk (Nat.lt_succ_self k)
    have h2 := hbig k hk (by omega)
    have h3 : 0 < f k * f (k + 1) := by
      rcases lt_or_gt_of_ne (show f k ≠ 0 by
        intro h0; rw [h0, abs_zero] at h2; linarith) with hneg | hpos
      · have : f k - f (k + 1) ≥ -lam := by rw [abs_le] at h1; linarith [h1.1]
        have h4 : f (k + 1) < 0 := by
          rw [abs_of_neg hneg] at h2
          rw [abs_le] at h1
          linarith [h1.1, h1.2]
        nlinarith
      · have h4 : 0 < f (k + 1) := by
          rw [abs_of_pos hpos] at h2
          rw [abs_le] at h1
          linarith [h1.1, h1.2]
        positivity
    have h5 : 0 < f k * f k := mul_self_pos.2 (by
      intro h0; rw [h0, abs_zero] at h2; linarith)
    have : 0 < f j * f k * (f k * f (k + 1)) := mul_pos ih' h3
    have h6 : f j * f k * (f k * f (k + 1)) = (f j * f (k + 1)) * (f k * f k) := by ring
    rw [h6] at this
    exact (mul_pos_iff_of_pos_right h5).1 this

/-- **Depth bound (Claim 1 of Morse).** A coarse `(μ, U, c)`-quasi-geodesic chain with steps `≤ λ` whose end points lie
on the axis stays within a fixed distance `M₁` of the axis. -/
theorem s24q_nb_depth {T D : UpperHalfPlane → ℝ}
    (hstar : ∀ p q : UpperHalfPlane, Real.cosh (dist p q) =
      Real.cosh (D p) * Real.cosh (D q) * Real.cosh (T p - T q) - Real.sinh (D p) * Real.sinh (D q))
    {lam μ c U : ℝ} (hlam : 0 < lam) (hμ : 0 < μ) (hc : 0 ≤ c) (hU : 0 < U) :
    ∃ M₁ : ℝ, 0 ≤ M₁ ∧ ∀ (n : ℕ) (x : ℕ → UpperHalfPlane),
      (∀ i < n, dist (x i) (x (i + 1)) ≤ lam) →
      (∀ i ≤ n, ∀ k ≤ n, μ * |(i : ℝ) - k| - c ≤ dist (x i) (x k)) →
      (∀ i ≤ n, ∀ k ≤ n, dist (x i) (x k) ≤ U * |(i : ℝ) - k| + c) →
      D (x 0) = 0 → D (x n) = 0 → ∀ i ≤ n, |D (x i)| ≤ M₁ := by
  classical
  set C := Real.sqrt (2 * (Real.cosh lam - 1)) with hC
  set m₁ : ℝ := 48 * (2 * Real.exp c * Real.cosh lam + Real.exp (c + 2 * lam) * C ^ 2) / μ ^ 3 with hm₁
  have hm₁0 : 0 ≤ m₁ := by positivity
  set K' : ℝ := c + U * (m₁ + 1) with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hK'pos : 0 < K' := by
    have := mul_pos hU (by linarith : 0 < m₁ + 1)
    linarith
  set r0 : ℝ := max 0 (Real.log (4 * C / μ)) with hr0
  refine ⟨K' + 2 * lam + 1 + r0, by positivity, ?_⟩
  intro n x hstep hlow hup hD0 hDn
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, hi₀, hi₀'⟩ := hcon
  obtain ⟨istar, histar, hmax⟩ := Finset.exists_max_image (Finset.range (n + 1)) (fun i => |D (x i)|)
    ⟨0, by simp⟩
  have histar_le : istar ≤ n := by
    have := Finset.mem_range.1 histar; omega
  set M := |D (x istar)| with hM
  have hMbig : K' + 2 * lam + 1 + r0 < M := by
    refine lt_of_lt_of_le hi₀' (hmax i₀ (Finset.mem_range.2 (by omega)))
  have hMall : ∀ i ≤ n, |D (x i)| ≤ M := fun i hi => hmax i (Finset.mem_range.2 (by omega))
  have hr0' : 0 ≤ r0 := le_max_left _ _
  set r := M - K' with hr
  have hrbig : 2 * lam + 1 + r0 < r := by linarith
  have hr0pos : 0 < r := by linarith
  -- end indices
  have hist0 : istar ≠ 0 := by
    intro h; rw [hM, h, hD0, abs_zero] at hMbig; linarith
  have histn : istar ≠ n := by
    intro h; rw [hM, h, hDn, abs_zero] at hMbig; linarith
  have hist_lt : istar < n := lt_of_le_of_ne histar_le histn
  -- j: last index below `istar` with `|D| ≤ r`
  set P : ℕ → Prop := fun i => |D (x i)| ≤ r with hP
  have hP0 : P 0 := by
    show |D (x 0)| ≤ r
    rw [hD0, abs_zero]; linarith
  set j := Nat.findGreatest P (istar - 1) with hj
  have hPj : P j := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  have hjle : j ≤ istar - 1 := Nat.findGreatest_le _
  have hjlt : j < istar := by omega
  have hjmax : ∀ i, j < i → i ≤ istar - 1 → ¬ P i := fun i hi hi' =>
    Nat.findGreatest_is_greatest (P := P) hi hi'
  have hPn : P n := by
    show |D (x n)| ≤ r
    rw [hDn, abs_zero]; linarith
  have hex : ∃ k, istar < k ∧ k ≤ n ∧ P k := ⟨n, hist_lt, le_rfl, hPn⟩
  set k := Nat.find hex with hk
  have hkspec := Nat.find_spec hex
  have hkgt : istar < k := hkspec.1
  have hkle : k ≤ n := hkspec.2.1
  have hPk : P k := hkspec.2.2
  have hkmin : ∀ i, istar < i → i < k → ¬ P i := fun i hi hik hPi =>
    Nat.find_min hex hik ⟨hi, by omega, hPi⟩
  -- all indices strictly between j and k are deep
  have hdeep : ∀ i, j < i → i < k → r < |D (x i)| := by
    intro i hji hik
    by_cases h1 : i ≤ istar - 1
    · exact lt_of_not_ge (hjmax i hji h1)
    · by_cases h2 : i = istar
      · rw [h2]; show r < M; linarith
      · have : istar < i := by omega
        exact lt_of_not_ge (hkmin i this hik)
  have hDd : ∀ p q : UpperHalfPlane, |D p - D q| ≤ dist p q := fun p q => s24q_nb_dD_le hstar p q
  have hdist_step : ∀ i, i < n → |D (x i) - D (x (i + 1))| ≤ lam := fun i hi =>
    (hDd _ _).trans (hstep i hi)
  -- depth at the ends
  have hdj : r - lam ≤ |D (x j)| := by
    have h1 := hdeep (j + 1) (by omega) (by omega)
    have h2 := hdist_step j (by omega)
    have h3 : |D (x (j + 1))| ≤ |D (x j)| + |D (x j) - D (x (j + 1))| := by
      calc |D (x (j + 1))| = |D (x j) - (D (x j) - D (x (j + 1)))| := by ring_nf
        _ ≤ |D (x j)| + |D (x j) - D (x (j + 1))| := by
          simpa using abs_sub (D (x j)) (D (x j) - D (x (j + 1)))
    linarith
  have hdk : r - lam ≤ |D (x k)| := by
    have h1 := hdeep (k - 1) (by omega) (by omega)
    have h2 := hdist_step (k - 1) (by omega)
    have hk1 : k - 1 + 1 = k := by omega
    rw [hk1] at h2
    have h3 : |D (x (k - 1))| ≤ |D (x k)| + |D (x (k - 1)) - D (x k)| := by
      calc |D (x (k - 1))| = |D (x k) + (D (x (k - 1)) - D (x k))| := by ring_nf
        _ ≤ |D (x k)| + |D (x (k - 1)) - D (x k)| := abs_add_le _ _
    linarith
  have hdepth : ∀ i, j ≤ i → i ≤ k → r - lam ≤ |D (x i)| := by
    intro i hji hik
    rcases eq_or_lt_of_le hji with h | h
    · rw [← h]; exact hdj
    · rcases eq_or_lt_of_le hik with h' | h'
      · rw [h']; exact hdk
      · exact ((sub_le_self r hlam.le).trans (hdeep i h h').le)
  -- sign
  have hsign : 0 < D (x j) * D (x k) := by
    refine s24q_nb_sign_chain (fun i => D (x i)) hlam.le (by omega) (fun i hji hik => ?_) (fun i hji hik => ?_)
    · exact hdist_step i (by omega)
    · have := hdepth i hji hik
      linarith
  have hsame : |D (x j) - D (x k)| ≤ lam := by
    have hj1 : |D (x j)| ≤ r := hPj
    have hk1 : |D (x k)| ≤ r := hPk
    rcases lt_or_gt_of_ne (show D (x j) ≠ 0 from by
      intro h0; rw [h0, zero_mul] at hsign; exact lt_irrefl _ hsign) with hneg | hpos
    · have hk0 : D (x k) < 0 := by
        by_contra hh; push Not at hh; nlinarith
      rw [abs_of_neg hneg] at hj1 hdj
      rw [abs_of_neg hk0] at hk1 hdk
      rw [abs_le]; constructor <;> linarith
    · have hk0 : 0 < D (x k) := by
        by_contra hh; push Not at hh; nlinarith
      rw [abs_of_pos hpos] at hj1 hdj
      rw [abs_of_pos hk0] at hk1 hdk
      rw [abs_le]; constructor <;> linarith
  have hexc := s24q_nb_excursion hstar hlam hμ hc x (show j < k by omega)
    (r' := r - lam) (by
      have : Real.log (4 * C / μ) ≤ r0 := le_max_right _ _
      linarith) (by linarith)
    (fun i hji hik => hstep i (by omega)) hdepth (by rw [sub_add_cancel]; exact hPj)
    (by rw [sub_add_cancel]; exact hPk) hsame
    (by
      have := hlow j (by omega) k hkle
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast (show j ≤ k by omega)))] at this
      exact this)
  -- the climb forces a long chain
  have hclimb : K' ≤ dist (x istar) (x j) := by
    have h1 : M - |D (x j)| ≤ |D (x istar) - D (x j)| := by
      have := abs_sub_abs_le_abs_sub (D (x istar)) (D (x j))
      linarith
    have h2 : M - r ≤ M - |D (x j)| := by linarith [hPj]
    have h3 := hDd (x istar) (x j)
    have : M - r = K' := by rw [hr]; ring
    linarith
  have hupj := hup istar histar_le j (by omega)
  rw [abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hjlt.le))] at hupj
  have hij : (m₁ + 1) ≤ (istar : ℝ) - j := by
    have h1 : K' ≤ U * ((istar : ℝ) - j) + c := hclimb.trans hupj
    have h2 : U * (m₁ + 1) ≤ U * ((istar : ℝ) - j) := by
      rw [hK'] at h1; linarith
    exact le_of_mul_le_mul_left h2 hU
  have hkj : ((istar : ℝ) - j) ≤ (k : ℝ) - j := by
    have : (istar : ℝ) ≤ k := by exact_mod_cast hkgt.le
    linarith
  linarith

/-- The axis point with `T = t`. -/
theorem s24q_nb_axis_pt {T D : UpperHalfPlane → ℝ}
    (hD0 : ∀ p : UpperHalfPlane, D p = 0 ↔ (p : ℂ).re = 0)
    (hT : ∀ (y : ℝ) (hy : 0 < y), T (UpperHalfPlane.mk ⟨0, y⟩ hy) = Real.log y) (t : ℝ) :
    ∃ p : UpperHalfPlane, D p = 0 ∧ T p = t := by
  refine ⟨UpperHalfPlane.mk ⟨0, Real.exp t⟩ (Real.exp_pos t), (hD0 _).2 rfl, ?_⟩
  rw [hT, Real.log_exp]

/-- Distance between two axis points. -/
theorem s24q_nb_dist_axis {T D : UpperHalfPlane → ℝ}
    (hstar : ∀ p q : UpperHalfPlane, Real.cosh (dist p q) =
      Real.cosh (D p) * Real.cosh (D q) * Real.cosh (T p - T q) - Real.sinh (D p) * Real.sinh (D q))
    (p q : UpperHalfPlane) (hp : D p = 0) (hq : D q = 0) : dist p q = |T p - T q| := by
  have h := hstar p q
  rw [hp, hq, Real.cosh_zero, Real.sinh_zero] at h
  simp only [one_mul, mul_zero, sub_zero] at h
  have h1 := Real.cosh_le_cosh.1 h.le
  have h2 := Real.cosh_le_cosh.1 h.ge
  rw [abs_of_nonneg dist_nonneg] at h1 h2
  exact le_antisymm h1 h2

/-- `dist p q ≤ |D p| + |D q| + |T p - T q|`. -/
theorem s24q_nb_dist_le_three {T D : UpperHalfPlane → ℝ}
    (hstar : ∀ p q : UpperHalfPlane, Real.cosh (dist p q) =
      Real.cosh (D p) * Real.cosh (D q) * Real.cosh (T p - T q) - Real.sinh (D p) * Real.sinh (D q))
    (hD0 : ∀ p : UpperHalfPlane, D p = 0 ↔ (p : ℂ).re = 0)
    (hT : ∀ (y : ℝ) (hy : 0 < y), T (UpperHalfPlane.mk ⟨0, y⟩ hy) = Real.log y) (p q : UpperHalfPlane) :
    dist p q ≤ |D p| + |D q| + |T p - T q| := by
  obtain ⟨a, ha0, haT⟩ := s24q_nb_axis_pt hD0 hT (T p)
  obtain ⟨b, hb0, hbT⟩ := s24q_nb_axis_pt hD0 hT (T q)
  have h1 : dist p a ≤ |D p| + |T p - T a| := s24q_nb_dist_le_axis hstar p a ha0
  have h2 : dist q b ≤ |D q| + |T q - T b| := s24q_nb_dist_le_axis hstar q b hb0
  have h3 := s24q_nb_dist_axis hstar a b ha0 hb0
  rw [haT, hbT] at h3
  rw [haT] at h1
  rw [hbT] at h2
  simp only [sub_self, abs_zero, add_zero] at h1 h2
  calc dist p q ≤ dist p a + dist a b + dist b q := dist_triangle4 _ _ _ _
    _ ≤ |D p| + |T p - T q| + |D q| := by rw [dist_comm b q]; linarith
    _ = |D p| + |D q| + |T p - T q| := by ring

/-- A point of the geodesic segment between two axis points lies on the axis, between them. -/
theorem s24q_nb_seg_imp {T D : UpperHalfPlane → ℝ}
    (hstar : ∀ p q : UpperHalfPlane, Real.cosh (dist p q) =
      Real.cosh (D p) * Real.cosh (D q) * Real.cosh (T p - T q) - Real.sinh (D p) * Real.sinh (D q))
    (p q u : UpperHalfPlane) (hp : D p = 0) (hq : D q = 0) (h : dist p u + dist u q = dist p q) :
    D u = 0 ∧ min (T p) (T q) ≤ T u ∧ T u ≤ max (T p) (T q) := by
  have hpq := s24q_nb_dist_axis hstar p q hp hq
  have h1 := s24q_nb_dT_le hstar p u
  have h2 := s24q_nb_dT_le hstar u q
  have h3 : |T p - T q| ≤ |T p - T u| + |T u - T q| := by
    calc |T p - T q| = |(T p - T u) + (T u - T q)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have e1 : dist p u = |T p - T u| := by linarith
  have e2 : dist u q = |T u - T q| := by linarith
  have hsum : |T p - T u| + |T u - T q| = |T p - T q| := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h4 := hstar p u
    rw [hp, Real.cosh_zero, Real.sinh_zero, e1, Real.cosh_abs] at h4
    simp only [one_mul, zero_mul, sub_zero] at h4
    have hpos := Real.cosh_pos (T p - T u)
    have h6 : Real.cosh (D u) = 1 := by
      have : Real.cosh (D u) * Real.cosh (T p - T u) = 1 * Real.cosh (T p - T u) := by linarith
      exact mul_right_cancel₀ hpos.ne' this
    have h7 := s24q_nb_one_add_sq_le_cosh (D u)
    have h8 : D u ^ 2 ≤ 0 := by linarith
    exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h8 (sq_nonneg _))
  · rw [min_le_iff]
    by_contra hc
    push Not at hc
    rcases abs_cases (T p - T u) with ⟨a1, _⟩ | ⟨a1, _⟩ <;> rcases abs_cases (T u - T q) with ⟨a2, _⟩ | ⟨a2, _⟩ <;>
      rcases abs_cases (T p - T q) with ⟨a3, _⟩ | ⟨a3, _⟩ <;> linarith [hc.1, hc.2]
  · rw [le_max_iff]
    by_contra hc
    push Not at hc
    rcases abs_cases (T p - T u) with ⟨a1, _⟩ | ⟨a1, _⟩ <;> rcases abs_cases (T u - T q) with ⟨a2, _⟩ | ⟨a2, _⟩ <;>
      rcases abs_cases (T p - T q) with ⟨a3, _⟩ | ⟨a3, _⟩ <;> linarith [hc.1, hc.2]

/-- Converse: axis points between `p` and `q` lie on the geodesic segment. -/
theorem s24q_nb_seg_of {T D : UpperHalfPlane → ℝ}
    (hstar : ∀ p q : UpperHalfPlane, Real.cosh (dist p q) =
      Real.cosh (D p) * Real.cosh (D q) * Real.cosh (T p - T q) - Real.sinh (D p) * Real.sinh (D q))
    (p q u : UpperHalfPlane) (hp : D p = 0) (hq : D q = 0) (hu : D u = 0)
    (h1 : min (T p) (T q) ≤ T u) (h2 : T u ≤ max (T p) (T q)) : dist p u + dist u q = dist p q := by
  rw [s24q_nb_dist_axis hstar p u hp hu, s24q_nb_dist_axis hstar u q hu hq, s24q_nb_dist_axis hstar p q hp hq]
  rw [min_le_iff] at h1
  rw [le_max_iff] at h2
  rcases abs_cases (T p - T u) with ⟨a1, _⟩ | ⟨a1, _⟩ <;> rcases abs_cases (T u - T q) with ⟨a2, _⟩ | ⟨a2, _⟩ <;>
    rcases abs_cases (T p - T q) with ⟨a3, _⟩ | ⟨a3, _⟩ <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    linarith

/-- An equally spaced chain along the geodesic segment `[z, w]`, covering the segment up to `d(z, w) / n`. -/
theorem s24q_nb_chain2 (z w : UpperHalfPlane) (n : ℕ) (hn : 0 < n) :
    ∃ u : ℕ → UpperHalfPlane, u 0 = z ∧ u n = w ∧
      (∀ i ≤ n, ∀ k ≤ n, dist (u i) (u k) = |(i : ℝ) - k| * (dist z w / n)) ∧
      (∀ x : UpperHalfPlane, dist z x + dist x w = dist z w → ∃ i ≤ n, dist x (u i) ≤ dist z w / n) := by
  obtain ⟨T, D, hstar, hD0, hT⟩ := s24q_nb_coords
  obtain ⟨g, hz, hw⟩ := s24q_nb_exists_vertical z w
  have hz' : (g • z) = UpperHalfPlane.mk ⟨0, (g • z).im⟩ (g • z).im_pos := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · simpa using hz
    · rfl
  have hw' : (g • w) = UpperHalfPlane.mk ⟨0, (g • w).im⟩ (g • w).im_pos := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · simpa using hw
    · rfl
  obtain ⟨y, hy, hyz⟩ : ∃ y : ℝ, ∃ hy : 0 < y, g • z = UpperHalfPlane.mk ⟨0, y⟩ hy := ⟨_, (g • z).im_pos, hz'⟩
  obtain ⟨y', hy', hyw⟩ : ∃ y' : ℝ, ∃ hy' : 0 < y', g • w = UpperHalfPlane.mk ⟨0, y'⟩ hy' := ⟨_, (g • w).im_pos, hw'⟩
  let p : ℝ → UpperHalfPlane := fun s =>
    UpperHalfPlane.mk ⟨0, Real.exp ((1 - s) * Real.log y + s * Real.log y')⟩ (Real.exp_pos _)
  have hp0 : p 0 = g • z := by
    rw [hyz]
    apply UpperHalfPlane.ext
    apply Complex.ext
    · rfl
    · show Real.exp ((1 - 0) * Real.log y + 0 * Real.log y') = y
      simp [Real.exp_log hy]
  have hp1 : p 1 = g • w := by
    rw [hyw]
    apply UpperHalfPlane.ext
    apply Complex.ext
    · rfl
    · show Real.exp ((1 - 1) * Real.log y + 1 * Real.log y') = y'
      simp [Real.exp_log hy']
  have hpD : ∀ s, D (p s) = 0 := fun s => (hD0 _).2 rfl
  have hpT : ∀ s, T (p s) = (1 - s) * Real.log y + s * Real.log y' := fun s => by
    show T (UpperHalfPlane.mk ⟨0, Real.exp ((1 - s) * Real.log y + s * Real.log y')⟩ _) = _
    rw [hT, Real.log_exp]
  have hpd : ∀ s t : ℝ, dist (p s) (p t) = |s - t| * |Real.log y - Real.log y'| := by
    intro s t
    rw [s24q_nb_dist_axis hstar _ _ (hpD s) (hpD t), hpT, hpT, ← abs_mul, ← abs_neg]
    congr 1
    ring
  have hzT : T (g • z) = Real.log y := by rw [hyz, hT]
  have hwT : T (g • w) = Real.log y' := by rw [hyw, hT]
  have hzD : D (g • z) = 0 := (hD0 _).2 hz
  have hwD : D (g • w) = 0 := (hD0 _).2 hw
  have hD : dist z w = |Real.log y - Real.log y'| := by
    rw [← dist_smul g z w, s24q_nb_dist_axis hstar _ _ hzD hwD, hzT, hwT]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨fun i => g⁻¹ • p ((i : ℝ) / n), ?_, ?_, ?_, ?_⟩
  · simp only [Nat.cast_zero, zero_div, hp0, inv_smul_smul]
  · simp only [div_self hnr.ne', hp1, inv_smul_smul]
  · intro i hi k hk
    rw [dist_smul, hpd, hD, ← sub_div, abs_div, abs_of_pos hnr]
    ring
  · intro x hx
    have hx' : dist (g • z) (g • x) + dist (g • x) (g • w) = dist (g • z) (g • w) := by
      rw [dist_smul, dist_smul, dist_smul]; exact hx
    obtain ⟨hxD, hx1, hx2⟩ := s24q_nb_seg_imp hstar _ _ _ hzD hwD hx'
    rw [hzT, hwT] at hx1 hx2
    set t := T (g • x) with ht
    by_cases hab : Real.log y = Real.log y'
    · refine ⟨0, Nat.zero_le _, ?_⟩
      have h1 : t = Real.log y := by
        rw [← hab, min_self] at hx1
        rw [← hab, max_self] at hx2
        exact le_antisymm hx2 hx1
      have : dist x (g⁻¹ • p ((0 : ℕ) / n)) = 0 := by
        simp only [Nat.cast_zero, zero_div, hp0, inv_smul_smul]
        rw [← dist_smul g x z, s24q_nb_dist_axis hstar _ _ hxD hzD, hzT, ← ht, h1, sub_self, abs_zero]
      rw [this]
      positivity
    · set s : ℝ := (t - Real.log y) / (Real.log y' - Real.log y) with hs
      have hba : Real.log y' - Real.log y ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
      have hs01 : 0 ≤ s ∧ s ≤ 1 := by
        rcases le_total (Real.log y) (Real.log y') with h | h
        · rw [min_eq_left h] at hx1
          rw [max_eq_right h] at hx2
          have hpos : 0 < Real.log y' - Real.log y := sub_pos.2 (lt_of_le_of_ne h hab)
          constructor
          · exact div_nonneg (by linarith) hpos.le
          · rw [hs, div_le_one hpos]; linarith
        · rw [min_eq_right h] at hx1
          rw [max_eq_left h] at hx2
          have hneg : Real.log y' - Real.log y < 0 := sub_neg.2 (lt_of_le_of_ne h (Ne.symm hab))
          constructor
          · exact div_nonneg_of_nonpos (by linarith) hneg.le
          · rw [hs, div_le_one_of_neg hneg]; linarith
      set i : ℕ := ⌊s * n⌋₊ with hi
      have hsn : 0 ≤ s * n := mul_nonneg hs01.1 hnr.le
      have hi1 : (i : ℝ) ≤ s * n := Nat.floor_le hsn
      have hi2 : s * n < i + 1 := Nat.lt_floor_add_one _
      have hin : i ≤ n := by
        have : (i : ℝ) ≤ n := hi1.trans (by nlinarith [hs01.2])
        exact_mod_cast this
      refine ⟨i, hin, ?_⟩
      show dist x (g⁻¹ • p ((i : ℝ) / n)) ≤ _
      rw [← dist_smul g x (g⁻¹ • p ((i : ℝ) / n)), smul_inv_smul,
        s24q_nb_dist_axis hstar _ _ hxD (hpD _), hpT, hD]
      have e1 : t - ((1 - (i : ℝ) / n) * Real.log y + (i : ℝ) / n * Real.log y') =
          (s - (i : ℝ) / n) * (Real.log y' - Real.log y) := by
        rw [hs]
        field_simp
        ring
      rw [e1, abs_mul, abs_sub_comm (Real.log y') (Real.log y)]
      have h3 : |s - (i : ℝ) / n| ≤ 1 / n := by
        rw [abs_le]
        constructor
        · have : (i : ℝ) / n ≤ s := by rw [div_le_iff₀ hnr]; linarith
          have h0 : 0 ≤ 1 / (n : ℝ) := by positivity
          linarith
        · have : s < ((i : ℝ) + 1) / n := by rw [lt_div_iff₀ hnr]; linarith
          have : s - (i : ℝ) / n < 1 / n := by
            have e : ((i : ℝ) + 1) / n = (i : ℝ) / n + 1 / n := by ring
            linarith
          linarith
      calc |s - (i : ℝ) / n| * |Real.log y - Real.log y'| ≤ (1 / n) * |Real.log y - Real.log y'| :=
            mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
        _ = |Real.log y - Real.log y'| / n := by ring

/-- **Morse, normalized.** The case where the segment `[G z, G w]` lies on the imaginary axis. -/
theorem s24q_nb_morse_core (L c : ℝ) (hL : 1 ≤ L) (hc : 0 ≤ c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ G : UpperHalfPlane → UpperHalfPlane,
      (∀ z w : UpperHalfPlane, dist z w / L - c ≤ dist (G z) (G w) ∧ dist (G z) (G w) ≤ L * dist z w + c) →
      ∀ z w : UpperHalfPlane, (G z : ℂ).re = 0 → (G w : ℂ).re = 0 →
        (∀ u : UpperHalfPlane, dist z u + dist u w = dist z w →
          ∃ u' : UpperHalfPlane, dist (G z) u' + dist u' (G w) = dist (G z) (G w) ∧ dist (G u) u' ≤ M) ∧
        (∀ v : UpperHalfPlane, dist (G z) v + dist v (G w) = dist (G z) (G w) →
          ∃ u : UpperHalfPlane, dist z u + dist u w = dist z w ∧ dist (G u) v ≤ M) := by
  obtain ⟨T, D, hstar, hD0, hT⟩ := s24q_nb_coords
  have hL0 : 0 < L := by linarith
  have hlam : 0 < L + c := by linarith
  have hμ : 0 < 1 / (2 * L) := by positivity
  obtain ⟨M₁, hM₁0, hdepth⟩ := s24q_nb_depth hstar (lam := L + c) (μ := 1 / (2 * L)) (c := c) (U := L)
    hlam hμ hc hL0
  set E : ℝ := L + c with hE
  set Q : ℝ := E * (2 * L * (L + c) + 2 * L * (2 * M₁ + c)) + E with hQ
  have hE0 : 0 ≤ E := hlam.le
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨L + c + M₁ + Q + (L + c) + 1, by positivity, fun G hG z w hz hw => ?_⟩
  have hDa : D (G z) = 0 := (hD0 _).2 hz
  have hDb : D (G w) = 0 := (hD0 _).2 hw
  by_cases hd : dist z w < 1
  · constructor
    · intro u hu
      refine ⟨G z, by simp, ?_⟩
      have h1 : dist z u ≤ dist z w := by
        have := dist_nonneg (x := u) (y := w); linarith
      have h2 := (hG z u).2
      have h3 : L * dist z u ≤ L * 1 := mul_le_mul_of_nonneg_left (by linarith) hL0.le
      rw [dist_comm]
      linarith [hM₁0, hQ0]
    · intro v hv
      refine ⟨z, by simp, ?_⟩
      have h1 : dist (G z) v ≤ dist (G z) (G w) := by
        have := dist_nonneg (x := v) (y := G w); linarith
      have h2 := (hG z w).2
      have h3 : L * dist z w ≤ L * 1 := mul_le_mul_of_nonneg_left (by linarith) hL0.le
      linarith [hM₁0, hQ0]
  · push Not at hd
    set d := dist z w with hdd
    set n : ℕ := ⌈d⌉₊ with hn
    have hn0 : 0 < n := Nat.ceil_pos.2 (by linarith)
    have hnr : (0 : ℝ) < n := by exact_mod_cast hn0
    have hnd : d ≤ n := Nat.le_ceil d
    have hnd2 : (n : ℝ) < d + 1 := Nat.ceil_lt_add_one (by linarith)
    set h : ℝ := d / n with hh
    have hh1 : h ≤ 1 := by rw [hh, div_le_one hnr]; exact hnd
    have hh2 : 1 / 2 ≤ h := by
      rw [hh, le_div_iff₀ hnr]; linarith
    obtain ⟨σ, hσ0, hσn, hσd, hσc⟩ := s24q_nb_chain2 z w n hn0
    set x : ℕ → UpperHalfPlane := fun i => G (σ i) with hx
    have hx0 : x 0 = G z := by simp only [hx, hσ0]
    have hxn : x n = G w := by simp only [hx, hσn]
    have hup : ∀ i ≤ n, ∀ k ≤ n, dist (x i) (x k) ≤ L * |(i : ℝ) - k| + c := by
      intro i hi k hk
      have h1 := (hG (σ i) (σ k)).2
      rw [hσd i hi k hk] at h1
      have h2 : |(i : ℝ) - k| * h ≤ |(i : ℝ) - k| := by
        nlinarith [abs_nonneg ((i : ℝ) - k)]
      calc dist (x i) (x k) ≤ L * (|(i : ℝ) - k| * h) + c := h1
        _ ≤ L * |(i : ℝ) - k| + c := by gcongr
    have hlow : ∀ i ≤ n, ∀ k ≤ n, 1 / (2 * L) * |(i : ℝ) - k| - c ≤ dist (x i) (x k) := by
      intro i hi k hk
      have h1 := (hG (σ i) (σ k)).1
      rw [hσd i hi k hk] at h1
      have h2 : 1 / (2 * L) * |(i : ℝ) - k| ≤ |(i : ℝ) - k| * (d / n) / L := by
        calc 1 / (2 * L) * |(i : ℝ) - k| = (|(i : ℝ) - k| * (1 / 2)) / L := by field_simp
          _ ≤ (|(i : ℝ) - k| * (d / n)) / L := by
            apply div_le_div_of_nonneg_right _ hL0.le
            exact mul_le_mul_of_nonneg_left hh2 (abs_nonneg _)
      linarith
    have hstep : ∀ i < n, dist (x i) (x (i + 1)) ≤ L + c := by
      intro i hi
      have := hup i hi.le (i + 1) (by omega)
      have e : |(i : ℝ) - ((i + 1 : ℕ) : ℝ)| = 1 := by
        push_cast
        rw [show (i : ℝ) - (i + 1) = -1 by ring, abs_neg, abs_one]
      rw [e] at this
      linarith
    have hdep := hdepth n x hstep hlow hup (by rw [hx0]; exact hDa) (by rw [hxn]; exact hDb)
    set t : ℕ → ℝ := fun i => T (x i) with ht
    have ht0 : t 0 = T (G z) := by simp only [ht, hx0]
    have htn : t n = T (G w) := by simp only [ht, hxn]
    have hstep_t : ∀ i < n, |t i - t (i + 1)| ≤ L + c := fun i hi =>
      (s24q_nb_dT_le hstar (x i) (x (i + 1))).trans (hstep i hi)
    have hlow_t : ∀ i ≤ n, ∀ k ≤ n, |(i : ℝ) - k| ≤ 2 * L * |t i - t k| + 2 * L * (2 * M₁ + c) := by
      intro i hi k hk
      have h1 := hlow i hi k hk
      have h2 := s24q_nb_dist_le_three hstar hD0 hT (x i) (x k)
      have h3 := hdep i hi
      have h4 := hdep k hk
      have h5 : 1 / (2 * L) * |(i : ℝ) - k| ≤ 2 * M₁ + |t i - t k| + c := by
        have : |D (x i)| + |D (x k)| + |T (x i) - T (x k)| ≤ 2 * M₁ + |t i - t k| := by
          simp only [ht]; linarith
        linarith
      have h6 : |(i : ℝ) - k| ≤ 2 * L * (2 * M₁ + |t i - t k| + c) := by
        have := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2 * L)
        have e : 2 * L * (1 / (2 * L) * |(i : ℝ) - k|) = |(i : ℝ) - k| := by field_simp
        linarith
      nlinarith
    have hup_t : ∀ i ≤ n, ∀ k ≤ n, |t i - t k| ≤ E * |(i : ℝ) - k| + E := by
      intro i hi k hk
      have h1 := s24q_nb_dT_le hstar (x i) (x k)
      have h2 := hup i hi k hk
      have h3 : L * |(i : ℝ) - k| + c ≤ E * |(i : ℝ) - k| + E := by
        rw [hE]; nlinarith [abs_nonneg ((i : ℝ) - k)]
      show |T (x i) - T (x k)| ≤ _
      linarith
    have hover := s24q_nb_overshoot t hlam.le hstep_t hlow_t hup_t hE0 (by positivity) (by positivity)
    have hQ' : E * (2 * L * (L + c) + 2 * L * (2 * M₁ + c)) + E = Q := hQ.symm
    constructor
    · -- direction 1
      intro u hu
      obtain ⟨i, hi, hui⟩ := hσc u hu
      have hui1 : dist u (σ i) ≤ 1 := hui.trans hh1
      have hGu : dist (G u) (x i) ≤ L + c := by
        have := (hG u (σ i)).2
        simp only [hx]
        nlinarith
      obtain ⟨hlo, hhi⟩ := hover i hi
      rw [ht0, htn] at hlo hhi
      set lo := min (T (G z)) (T (G w)) with hlo_def
      set hi' := max (T (G z)) (T (G w)) with hhi_def
      have hlohi : lo ≤ hi' := (min_le_left _ _).trans (le_max_left _ _)
      set t' : ℝ := max lo (min (t i) hi') with ht'
      obtain ⟨u', hu'D, hu'T⟩ := s24q_nb_axis_pt hD0 hT t'
      have hseg := s24q_nb_seg_of hstar (G z) (G w) u' hDa hDb hu'D (by rw [hu'T]; exact le_max_left _ _)
        (by rw [hu'T]; exact max_le hlohi (min_le_right _ _))
      have hclamp : |t i - t'| ≤ Q := by
        rw [abs_le]
        rcases le_total (t i) lo with h1 | h1
        · have : min (t i) hi' = t i := min_eq_left (h1.trans hlohi)
          rw [ht', this, max_eq_left h1]
          constructor <;> linarith
        · rcases le_total (t i) hi' with h2 | h2
          · rw [ht', min_eq_left h2, max_eq_right h1]
            constructor <;> linarith
          · rw [ht', min_eq_right h2, max_eq_right hlohi]
            constructor <;> linarith
      have hxu : dist (x i) u' ≤ M₁ + Q := by
        have := s24q_nb_dist_le_axis hstar (x i) u' hu'D
        rw [hu'T] at this
        have h2 := hdep i hi
        simp only [ht] at hclamp
        linarith
      refine ⟨u', hseg, ?_⟩
      calc dist (G u) u' ≤ dist (G u) (x i) + dist (x i) u' := dist_triangle _ _ _
        _ ≤ (L + c) + (M₁ + Q) := add_le_add hGu hxu
        _ ≤ L + c + M₁ + Q + (L + c) + 1 := by linarith
    · -- direction 2
      intro v hv
      obtain ⟨hvD, hv1, hv2⟩ := s24q_nb_seg_imp hstar (G z) (G w) v hDa hDb hv
      obtain ⟨i, hi, hiv⟩ := s24q_nb_ivt' t (L + c) hlam.le n hstep_t (t := T v) (by
        rw [ht0, htn]
        rcases le_total (T (G z)) (T (G w)) with h | h
        · left
          rw [min_eq_left h] at hv1
          rw [max_eq_right h] at hv2
          exact ⟨hv1, hv2⟩
        · right
          rw [min_eq_right h] at hv1
          rw [max_eq_left h] at hv2
          exact ⟨hv1, hv2⟩)
      refine ⟨σ i, ?_, ?_⟩
      · have h1 := hσd 0 (Nat.zero_le _) i hi
        have h2 := hσd i hi n le_rfl
        rw [hσ0] at h1
        rw [hσn] at h2
        rw [h1, h2]
        simp only [Nat.cast_zero, zero_sub, abs_neg]
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ i),
          abs_of_nonpos (by have : (i : ℝ) ≤ n := by exact_mod_cast hi
                            linarith : (i : ℝ) - n ≤ 0)]
        show (i : ℝ) * (d / n) + -((i : ℝ) - n) * (d / n) = d
        field_simp
        ring
      · have := s24q_nb_dist_le_axis hstar (x i) v hvD
        have h2 := hdep i hi
        show dist (x i) v ≤ _
        simp only [ht] at hiv
        linarith

/-- **B (Morse).** A `(L, c)`-quasi-isometric map `G : ℍ → ℍ` maps a geodesic segment `[z, w]` (the metric segment
`{u | d(z,u) + d(u,w) = d(z,w)}`) within a Hausdorff distance `M = M(L, c)` of the geodesic segment `[G z, G w]`:
every point of the one is within `M` of the `G`-image (resp. a point) of the other. -/
theorem s24q_nb_morse (L c : ℝ) (hL : 1 ≤ L) (hc : 0 ≤ c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ G : UpperHalfPlane → UpperHalfPlane,
      (∀ z w : UpperHalfPlane, dist z w / L - c ≤ dist (G z) (G w) ∧ dist (G z) (G w) ≤ L * dist z w + c) →
      ∀ z w : UpperHalfPlane,
        (∀ u : UpperHalfPlane, dist z u + dist u w = dist z w →
          ∃ u' : UpperHalfPlane, dist (G z) u' + dist u' (G w) = dist (G z) (G w) ∧ dist (G u) u' ≤ M) ∧
        (∀ v : UpperHalfPlane, dist (G z) v + dist v (G w) = dist (G z) (G w) →
          ∃ u : UpperHalfPlane, dist z u + dist u w = dist z w ∧ dist (G u) v ≤ M) := by
  obtain ⟨M, hM0, hcore⟩ := s24q_nb_morse_core L c hL hc
  refine ⟨M, hM0, fun G hG z w => ?_⟩
  obtain ⟨g, hgz, hgw⟩ := s24q_nb_exists_vertical (G z) (G w)
  have hG' : ∀ z w : UpperHalfPlane, dist z w / L - c ≤ dist ((fun p => g • G p) z) ((fun p => g • G p) w) ∧
      dist ((fun p => g • G p) z) ((fun p => g • G p) w) ≤ L * dist z w + c := by
    intro z w
    simp only [dist_smul]
    exact hG z w
  obtain ⟨h1, h2⟩ := hcore (fun p => g • G p) hG' z w hgz hgw
  have e1 : ∀ a b : UpperHalfPlane, dist a (g⁻¹ • b) = dist (g • a) b := by
    intro a b; rw [← dist_smul g a (g⁻¹ • b), smul_inv_smul]
  have e2 : ∀ a b : UpperHalfPlane, dist (g⁻¹ • a) b = dist a (g • b) := by
    intro a b; rw [← dist_smul g (g⁻¹ • a) b, smul_inv_smul]
  constructor
  · intro u hu
    obtain ⟨u', hs, hd⟩ := h1 u hu
    refine ⟨g⁻¹ • u', ?_, ?_⟩
    · rw [e1, e2, ← dist_smul g (G z) (G w)]
      exact hs
    · rw [e1]
      exact hd
  · intro v hv
    have hv' : dist ((fun p => g • G p) z) (g • v) + dist (g • v) ((fun p => g • G p) w) =
        dist ((fun p => g • G p) z) ((fun p => g • G p) w) := by
      simp only [dist_smul]
      exact hv
    obtain ⟨u, hs, hd⟩ := h2 (g • v) hv'
    refine ⟨u, hs, ?_⟩
    simp only [dist_smul] at hd
    exact hd

/-! ### The disc model of the hyperbolic metric -/

theorem s24q_nb_add_I_ne (z : UpperHalfPlane) : (z : ℂ) + I ≠ 0 := by
  intro h0
  have := congrArg Complex.im h0
  simp at this
  have := z.im_pos
  linarith

theorem s24q_nb_norm_add_I (z : UpperHalfPlane) : 0 < ‖(z : ℂ) + I‖ ^ 2 := by
  have h := s24q_nb_add_I_ne z
  positivity

theorem s24q_nb_sq_norm_pm (z : UpperHalfPlane) :
    ‖(z : ℂ) + I‖ ^ 2 = z.re ^ 2 + (z.im + 1) ^ 2 ∧ ‖(z : ℂ) - I‖ ^ 2 = z.re ^ 2 + (z.im - 1) ^ 2 := by
  constructor <;> (rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring)

theorem s24q_nb_cayley_norm_sq (z : UpperHalfPlane) :
    ‖cayley (z : ℂ)‖ ^ 2 = ‖(z : ℂ) - I‖ ^ 2 / ‖(z : ℂ) + I‖ ^ 2 := by
  unfold cayley; rw [norm_div, div_pow]

/-- `1 - |cayley z|² = 4 Im z / |z + i|²`. -/
theorem s24q_nb_one_sub_norm_sq (z : UpperHalfPlane) :
    1 - ‖cayley (z : ℂ)‖ ^ 2 = 4 * z.im / ‖(z : ℂ) + I‖ ^ 2 := by
  have hN := s24q_nb_norm_add_I z
  obtain ⟨h1, h2⟩ := s24q_nb_sq_norm_pm z
  rw [s24q_nb_cayley_norm_sq]
  have e : ‖(z : ℂ) + I‖ ^ 2 - ‖(z : ℂ) - I‖ ^ 2 = 4 * z.im := by rw [h1, h2]; ring
  generalize ‖(z : ℂ) + I‖ ^ 2 = N at *
  generalize ‖(z : ℂ) - I‖ ^ 2 = M at *
  field_simp
  linarith

/-- `|cayley z - cayley z'|² = 4 |z - z'|² / (|z + i|² |z' + i|²)`. -/
theorem s24q_nb_cayley_sub_sq (z z' : UpperHalfPlane) :
    ‖cayley (z : ℂ) - cayley (z' : ℂ)‖ ^ 2 =
      4 * ‖(z : ℂ) - z'‖ ^ 2 / (‖(z : ℂ) + I‖ ^ 2 * ‖(z' : ℂ) + I‖ ^ 2) := by
  have h := s24q_nb_add_I_ne z
  have h' := s24q_nb_add_I_ne z'
  have e : cayley (z : ℂ) - cayley (z' : ℂ) =
      2 * I * ((z : ℂ) - z') / (((z : ℂ) + I) * ((z' : ℂ) + I)) := by
    unfold cayley
    field_simp
    ring
  have n1 : ‖2 * I * ((z : ℂ) - z')‖ ^ 2 = 4 * ‖(z : ℂ) - z'‖ ^ 2 := by
    rw [norm_mul, norm_mul, mul_pow, mul_pow]
    simp
    norm_num
  have n2 : ‖((z : ℂ) + I) * ((z' : ℂ) + I)‖ ^ 2 = ‖(z : ℂ) + I‖ ^ 2 * ‖(z' : ℂ) + I‖ ^ 2 := by
    rw [norm_mul, mul_pow]
  rw [e, norm_div, div_pow, n1, n2]

/-- The law of cosines in the disc model. -/
theorem s24q_nb_cosh_dist_disc (z z' : UpperHalfPlane) :
    Real.cosh (dist z z') = 1 + 2 * ‖cayley (z : ℂ) - cayley (z' : ℂ)‖ ^ 2 /
      ((1 - ‖cayley (z : ℂ)‖ ^ 2) * (1 - ‖cayley (z' : ℂ)‖ ^ 2)) := by
  rw [UpperHalfPlane.cosh_dist, s24q_nb_cayley_sub_sq, s24q_nb_one_sub_norm_sq, s24q_nb_one_sub_norm_sq]
  have hN := s24q_nb_norm_add_I z
  have hN' := s24q_nb_norm_add_I z'
  have hy := z.im_pos
  have hy' := z'.im_pos
  have e : dist (z : ℂ) (z' : ℂ) = ‖(z : ℂ) - z'‖ := Complex.dist_eq _ _
  rw [e]
  generalize ‖(z : ℂ) + I‖ ^ 2 = N at *
  generalize ‖(z' : ℂ) + I‖ ^ 2 = N' at *
  generalize ‖(z : ℂ) - z'‖ = A
  field_simp
  ring

/-- `cosh (dist z i) = (1 + |cayley z|²) / (1 - |cayley z|²)`. -/
theorem s24q_nb_cosh_dist_I (z : UpperHalfPlane) :
    Real.cosh (dist z UpperHalfPlane.I) = (1 + ‖cayley (z : ℂ)‖ ^ 2) / (1 - ‖cayley (z : ℂ)‖ ^ 2) := by
  rw [UpperHalfPlane.cosh_dist, s24q_nb_one_sub_norm_sq, s24q_nb_cayley_norm_sq]
  have hN := s24q_nb_norm_add_I z
  have hy := z.im_pos
  obtain ⟨h1, h2⟩ := s24q_nb_sq_norm_pm z
  have e : dist (z : ℂ) ((UpperHalfPlane.I : UpperHalfPlane) : ℂ) = ‖(z : ℂ) - I‖ := by
    rw [Complex.dist_eq]; rfl
  have eI : (UpperHalfPlane.I : UpperHalfPlane).im = 1 := UpperHalfPlane.I_im
  rw [e, eI]
  have e2 : ‖(z : ℂ) + I‖ ^ 2 - ‖(z : ℂ) - I‖ ^ 2 = 4 * z.im := by rw [h1, h2]; ring
  generalize ‖(z : ℂ) + I‖ ^ 2 = N at *
  generalize ‖(z : ℂ) - I‖ ^ 2 = M at *
  have hNne : N ≠ 0 := hN.ne'
  have hsub : N - M ≠ 0 := by rw [e2]; positivity
  field_simp
  nlinarith [e2]

theorem s24q_nb_exp_abs_le_cosh (s : ℝ) : Real.exp |s| / 2 ≤ Real.cosh s := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have := Real.exp_pos (-|s|)
  linarith

theorem s24q_nb_cosh_le_exp_abs (s : ℝ) : Real.cosh s ≤ Real.exp |s| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h : Real.exp (-|s|) ≤ Real.exp |s| := Real.exp_le_exp.2 (by linarith [abs_nonneg s])
  linarith

theorem s24q_nb_exp_ge_cosh {d : ℝ} (hd : 0 ≤ d) : Real.cosh d ≤ Real.exp d := by
  have := s24q_nb_cosh_le_exp_abs d
  rwa [abs_of_nonneg hd] at this

theorem s24q_nb_clamp_identity (a b q : ℝ) :
    |q - a| + |q - b| = (max a b - min a b) + 2 * |q - max (min a b) (min q (max a b))| := by
  simp only [abs_eq_max_neg, min_def, max_def]
  split_ifs <;> linarith

/-- Distance from a point `q` to an axis point. -/
theorem s24q_nb_axis_dist_bounds {T D : UpperHalfPlane → ℝ}
    (hstar : ∀ p q : UpperHalfPlane, Real.cosh (dist p q) =
      Real.cosh (D p) * Real.cosh (D q) * Real.cosh (T p - T q) - Real.sinh (D p) * Real.sinh (D q))
    (q x : UpperHalfPlane) (hx : D x = 0) :
    Real.log (Real.cosh (D q)) + |T q - T x| - Real.log 2 ≤ dist q x ∧
      dist q x ≤ Real.log (2 * Real.cosh (D q)) + |T q - T x| := by
  have h := hstar q x
  rw [hx, Real.cosh_zero, Real.sinh_zero] at h
  simp only [mul_one, mul_zero, sub_zero] at h
  have hc := Real.cosh_pos (D q)
  have hs1 := s24q_nb_exp_abs_le_cosh (T q - T x)
  have hs2 := s24q_nb_cosh_le_exp_abs (T q - T x)
  have hd := dist_nonneg (x := q) (y := x)
  constructor
  · have h1 : Real.cosh (D q) * (Real.exp |T q - T x| / 2) ≤ Real.exp (dist q x) := by
      calc Real.cosh (D q) * (Real.exp |T q - T x| / 2) ≤ Real.cosh (D q) * Real.cosh (T q - T x) :=
            mul_le_mul_of_nonneg_left hs1 hc.le
        _ = Real.cosh (dist q x) := h.symm
        _ ≤ Real.exp (dist q x) := s24q_nb_exp_ge_cosh hd
    have hpos : 0 < Real.cosh (D q) * (Real.exp |T q - T x| / 2) := by positivity
    have := Real.log_le_log hpos h1
    rw [Real.log_exp, Real.log_mul hc.ne' (by positivity), Real.log_div (Real.exp_pos _).ne' (by norm_num),
      Real.log_exp] at this
    linarith
  · have h1 : Real.exp (dist q x) ≤ 2 * Real.cosh (D q) * Real.exp |T q - T x| := by
      have h2 : Real.exp (dist q x) ≤ 2 * Real.cosh (dist q x) := by
        rw [Real.cosh_eq]
        have := Real.exp_pos (-dist q x)
        linarith
      calc Real.exp (dist q x) ≤ 2 * Real.cosh (dist q x) := h2
        _ = 2 * (Real.cosh (D q) * Real.cosh (T q - T x)) := by rw [h]
        _ ≤ 2 * (Real.cosh (D q) * Real.exp |T q - T x|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs2 hc.le) (by norm_num)
        _ = 2 * Real.cosh (D q) * Real.exp |T q - T x| := by ring
    have hpos : 0 < Real.exp (dist q x) := Real.exp_pos _
    have := Real.log_le_log hpos h1
    rw [Real.log_exp, Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at this
    exact this

/-- **Thinness of triangles** (core): for `a, b` on the axis and any `q`, some point `u` of `[a, b]` is within
`P(q; a, b) + 2` of `q`, where `P` is the Gromov product. -/
theorem s24q_nb_gromov_core {T D : UpperHalfPlane → ℝ}
    (hstar : ∀ p q : UpperHalfPlane, Real.cosh (dist p q) =
      Real.cosh (D p) * Real.cosh (D q) * Real.cosh (T p - T q) - Real.sinh (D p) * Real.sinh (D q))
    (hD0 : ∀ p : UpperHalfPlane, D p = 0 ↔ (p : ℂ).re = 0)
    (hT : ∀ (y : ℝ) (hy : 0 < y), T (UpperHalfPlane.mk ⟨0, y⟩ hy) = Real.log y)
    (a b q : UpperHalfPlane) (ha : D a = 0) (hb : D b = 0) :
    ∃ u : UpperHalfPlane, dist a u + dist u b = dist a b ∧
      dist q u ≤ (dist q a + dist q b - dist a b) / 2 + 2 := by
  set lo := min (T a) (T b) with hlo
  set hi := max (T a) (T b) with hhi
  have hlohi : lo ≤ hi := (min_le_left _ _).trans (le_max_left _ _)
  set t : ℝ := max lo (min (T q) hi) with ht
  obtain ⟨u, hu0, huT⟩ := s24q_nb_axis_pt hD0 hT t
  have hseg := s24q_nb_seg_of hstar a b u ha hb hu0 (by rw [huT]; exact le_max_left _ _)
    (by rw [huT]; exact max_le hlohi (min_le_right _ _))
  refine ⟨u, hseg, ?_⟩
  have hab := s24q_nb_dist_axis hstar a b ha hb
  have hab' : dist a b = hi - lo := by
    rw [hab]
    rcases le_total (T a) (T b) with h | h
    · rw [hlo, hhi, min_eq_left h, max_eq_right h, abs_of_nonpos (by linarith)]; ring
    · rw [hlo, hhi, min_eq_right h, max_eq_left h, abs_of_nonneg (by linarith)]
  obtain ⟨la, ua⟩ := s24q_nb_axis_dist_bounds hstar q a ha
  obtain ⟨lb, ub⟩ := s24q_nb_axis_dist_bounds hstar q b hb
  obtain ⟨lu, uu⟩ := s24q_nb_axis_dist_bounds hstar q u hu0
  rw [huT] at lu uu
  have hsum : |T q - T a| + |T q - T b| = (hi - lo) + 2 * |T q - t| :=
    s24q_nb_clamp_identity (T a) (T b) (T q)
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hl2 : Real.log (2 * Real.cosh (D q)) = Real.log 2 + Real.log (Real.cosh (D q)) :=
    Real.log_mul (by norm_num) (Real.cosh_pos _).ne'
  have hL0 : 0 ≤ Real.log (Real.cosh (D q)) := Real.log_nonneg (Real.one_le_cosh _)
  rw [hl2] at uu
  have : (dist q a + dist q b - dist a b) / 2 ≥ Real.log (Real.cosh (D q)) + |T q - t| - Real.log 2 := by
    rw [hab']
    linarith [hsum]
  linarith

/-- **Thin triangles.** For any `a, b, q` some point `u` of the geodesic segment `[a, b]` is within the Gromov product
plus `2` of `q`. -/
theorem s24q_nb_gromov_seg (a b q : UpperHalfPlane) :
    ∃ u : UpperHalfPlane, dist a u + dist u b = dist a b ∧
      dist q u ≤ (dist q a + dist q b - dist a b) / 2 + 2 := by
  obtain ⟨T, D, hstar, hD0, hT⟩ := s24q_nb_coords
  obtain ⟨g, hga, hgb⟩ := s24q_nb_exists_vertical a b
  obtain ⟨u, hs, hd⟩ := s24q_nb_gromov_core hstar hD0 hT (g • a) (g • b) (g • q) ((hD0 _).2 hga) ((hD0 _).2 hgb)
  refine ⟨g⁻¹ • u, ?_, ?_⟩
  · have e1 : ∀ x y : UpperHalfPlane, dist x (g⁻¹ • y) = dist (g • x) y := by
      intro x y; rw [← dist_smul g x (g⁻¹ • y), smul_inv_smul]
    have e2 : ∀ x y : UpperHalfPlane, dist (g⁻¹ • x) y = dist x (g • y) := by
      intro x y; rw [← dist_smul g (g⁻¹ • x) y, smul_inv_smul]
    rw [e1, e2, ← dist_smul g a b]
    exact hs
  · rw [← dist_smul g q (g⁻¹ • u), smul_inv_smul]
    simp only [dist_smul] at hd
    exact hd

/-- The Gromov product lower-bounds the distance from the base point to the segment. -/
theorem s24q_nb_gromov_le (a b p u : UpperHalfPlane) (h : dist a u + dist u b = dist a b) :
    (dist p a + dist p b - dist a b) / 2 ≤ dist p u := by
  have h1 := dist_triangle p u a
  have h2 := dist_triangle p u b
  rw [dist_comm u a] at h1
  linarith

/-- `1 - |cayley z|² > 0`. -/
theorem s24q_nb_s_pos (z : UpperHalfPlane) : 0 < 1 - ‖cayley (z : ℂ)‖ ^ 2 := by
  rw [s24q_nb_one_sub_norm_sq]
  have := s24q_nb_norm_add_I z
  have := z.im_pos
  positivity

theorem s24q_nb_s_le (z : UpperHalfPlane) :
    1 - ‖cayley (z : ℂ)‖ ^ 2 ≤ 4 * Real.exp (-dist z UpperHalfPlane.I) := by
  have hs := s24q_nb_s_pos z
  have hc := s24q_nb_cosh_dist_I z
  set s := 1 - ‖cayley (z : ℂ)‖ ^ 2 with hsdef
  have h1 : 1 + ‖cayley (z : ℂ)‖ ^ 2 ≤ 2 := by
    have : ‖cayley (z : ℂ)‖ ^ 2 ≤ 1 := by linarith
    linarith
  have h2 : Real.exp (dist z UpperHalfPlane.I) / 2 ≤ Real.cosh (dist z UpperHalfPlane.I) := by
    have := s24q_nb_exp_abs_le_cosh (dist z UpperHalfPlane.I)
    rwa [abs_of_nonneg dist_nonneg] at this
  rw [hc, le_div_iff₀ hs] at h2
  -- exp(ρ)/2 * s ≤ 1 + |w|² ≤ 2
  have h3 : Real.exp (dist z UpperHalfPlane.I) * s ≤ 4 := by nlinarith
  rw [Real.exp_neg]
  have hpos := Real.exp_pos (dist z UpperHalfPlane.I)
  rw [← div_eq_mul_inv, le_div_iff₀ hpos]
  linarith

theorem s24q_nb_one_div_s_le (z : UpperHalfPlane) :
    1 / (1 - ‖cayley (z : ℂ)‖ ^ 2) ≤ Real.exp (dist z UpperHalfPlane.I) := by
  have hs := s24q_nb_s_pos z
  have hc := s24q_nb_cosh_dist_I z
  have h1 : 1 / (1 - ‖cayley (z : ℂ)‖ ^ 2) ≤ Real.cosh (dist z UpperHalfPlane.I) := by
    rw [hc]
    apply div_le_div_of_nonneg_right _ hs.le
    nlinarith [sq_nonneg ‖cayley (z : ℂ)‖]
  exact h1.trans (s24q_nb_exp_ge_cosh dist_nonneg)

/-- **Disc distance versus Gromov product** (upper bound): `|cayley a - cayley b| ≤ 3 e^{-P}`. -/
theorem s24q_nb_cayley_le (a b : UpperHalfPlane) :
    ‖cayley (a : ℂ) - cayley (b : ℂ)‖ ≤
      3 * Real.exp (-((dist a UpperHalfPlane.I + dist b UpperHalfPlane.I - dist a b) / 2)) := by
  have hcd := s24q_nb_cosh_dist_disc a b
  have hsa := s24q_nb_s_pos a
  have hsb := s24q_nb_s_pos b
  have ha := s24q_nb_s_le a
  have hb := s24q_nb_s_le b
  set sa := 1 - ‖cayley (a : ℂ)‖ ^ 2
  set sb := 1 - ‖cayley (b : ℂ)‖ ^ 2
  set Δ := ‖cayley (a : ℂ) - cayley (b : ℂ)‖ with hΔ
  have h1 : Δ ^ 2 = (Real.cosh (dist a b) - 1) * (sa * sb) / 2 := by
    rw [hcd]
    field_simp
    ring
  have h2 : Real.cosh (dist a b) - 1 ≤ Real.exp (dist a b) := by
    have := s24q_nb_exp_ge_cosh (dist_nonneg (x := a) (y := b))
    linarith
  have h3 : sa * sb ≤ 16 * Real.exp (-dist a UpperHalfPlane.I) * Real.exp (-dist b UpperHalfPlane.I) := by
    have := mul_le_mul ha hb hsb.le (by positivity)
    nlinarith
  have hcosh1 : 0 ≤ Real.cosh (dist a b) - 1 := by linarith [Real.one_le_cosh (dist a b)]
  have h4 : Δ ^ 2 ≤ 8 * Real.exp (dist a b - dist a UpperHalfPlane.I - dist b UpperHalfPlane.I) := by
    rw [h1]
    have h5 : (Real.cosh (dist a b) - 1) * (sa * sb) ≤
        Real.exp (dist a b) * (16 * Real.exp (-dist a UpperHalfPlane.I) * Real.exp (-dist b UpperHalfPlane.I)) :=
      mul_le_mul h2 h3 (by positivity) (Real.exp_pos _).le
    have e : Real.exp (dist a b) * (16 * Real.exp (-dist a UpperHalfPlane.I) * Real.exp (-dist b UpperHalfPlane.I)) =
        16 * Real.exp (dist a b - dist a UpperHalfPlane.I - dist b UpperHalfPlane.I) := by
      rw [show dist a b - dist a UpperHalfPlane.I - dist b UpperHalfPlane.I =
        dist a b + (-dist a UpperHalfPlane.I) + (-dist b UpperHalfPlane.I) by ring, Real.exp_add, Real.exp_add]
      ring
    rw [e] at h5
    linarith
  have h6 : Real.exp (dist a b - dist a UpperHalfPlane.I - dist b UpperHalfPlane.I) =
      Real.exp (-((dist a UpperHalfPlane.I + dist b UpperHalfPlane.I - dist a b) / 2)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h6] at h4
  have h7 : Δ ^ 2 ≤ (3 * Real.exp (-((dist a UpperHalfPlane.I + dist b UpperHalfPlane.I - dist a b) / 2))) ^ 2 := by
    rw [mul_pow]
    nlinarith [sq_nonneg (Real.exp (-((dist a UpperHalfPlane.I + dist b UpperHalfPlane.I - dist a b) / 2)))]
  exact abs_le_of_sq_le_sq' h7 (by positivity) |>.2 |> fun h => by
    simpa using h

/-- **C1.** Conversely, the two endpoints of a geodesic segment far from `i` are close in the disc model. -/
theorem s24q_nb_escape (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ a b : UpperHalfPlane,
      (∀ u : UpperHalfPlane, dist a u + dist u b = dist a b → R ≤ dist u UpperHalfPlane.I) →
        ‖cayley (a : ℂ) - cayley (b : ℂ)‖ < ε := by
  refine ⟨3 + Real.log (3 / ε), fun a b h => ?_⟩
  obtain ⟨u, hu, hd⟩ := s24q_nb_gromov_seg a b UpperHalfPlane.I
  have h1 := h u hu
  rw [dist_comm] at hd
  set P := (dist UpperHalfPlane.I a + dist UpperHalfPlane.I b - dist a b) / 2 with hP
  have hP' : P = (dist a UpperHalfPlane.I + dist b UpperHalfPlane.I - dist a b) / 2 := by
    rw [hP, dist_comm UpperHalfPlane.I a, dist_comm UpperHalfPlane.I b]
  have h2 : 1 + Real.log (3 / ε) ≤ P := by linarith
  have h3 := s24q_nb_cayley_le a b
  rw [← hP'] at h3
  have h4 : Real.exp (-P) ≤ Real.exp (-(1 + Real.log (3 / ε))) := Real.exp_le_exp.2 (by linarith)
  have h5 : Real.exp (-(1 + Real.log (3 / ε))) = Real.exp (-1) * (ε / 3) := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (3 / ε)), Real.exp_log (by positivity)]
    field_simp
  have h6 : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]; norm_num
  have h7 : 3 * Real.exp (-P) < ε := by
    calc 3 * Real.exp (-P) ≤ 3 * (Real.exp (-1) * (ε / 3)) := by rw [← h5]; gcongr
      _ = Real.exp (-1) * ε := by ring
      _ < 1 * ε := by gcongr
      _ = ε := one_mul ε
  exact lt_of_le_of_lt h3 h7

/-- **C0.** Two points of `ℍ` close (in the disc model `cayley`) to a boundary point `ζ` are joined by a geodesic
segment far from `i`, uniformly in `ζ`. -/
theorem s24q_nb_near (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ζ : Circle) (z w : UpperHalfPlane), ‖cayley (z : ℂ) - (ζ : ℂ)‖ < δ →
      ‖cayley (w : ℂ) - (ζ : ℂ)‖ < δ → ∀ u : UpperHalfPlane, dist z u + dist u w = dist z w →
        R ≤ dist u UpperHalfPlane.I := by
  refine ⟨Real.exp (-R) / 5, by positivity, fun ζ z w hz hw u hu => ?_⟩
  set δ := Real.exp (-R) / 5 with hδ
  have hδ0 : 0 < δ := by positivity
  have hζ : ‖(ζ : ℂ)‖ = 1 := Circle.norm_coe ζ
  -- smallness of `s`
  have hs_small : ∀ x : UpperHalfPlane, ‖cayley (x : ℂ) - (ζ : ℂ)‖ < δ → 1 - ‖cayley (x : ℂ)‖ ^ 2 < 2 * δ := by
    intro x hx
    have h1 : 1 - ‖cayley (x : ℂ)‖ ≤ ‖cayley (x : ℂ) - (ζ : ℂ)‖ := by
      have := norm_sub_norm_le (ζ : ℂ) (cayley (x : ℂ))
      rw [norm_sub_rev] at this
      linarith
    have hpos := s24q_nb_s_pos x
    have hn0 : 0 ≤ ‖cayley (x : ℂ)‖ := norm_nonneg _
    have hn1 : ‖cayley (x : ℂ)‖ < 1 := by
      by_contra hcon; push Not at hcon
      nlinarith
    nlinarith
  have hzs := hs_small z hz
  have hws := hs_small w hw
  have hΔ : ‖cayley (z : ℂ) - cayley (w : ℂ)‖ < 2 * δ := by
    have := norm_sub_le_norm_sub_add_norm_sub (cayley (z : ℂ)) (ζ : ℂ) (cayley (w : ℂ))
    rw [norm_sub_rev (ζ : ℂ)] at this
    linarith
  have hsz := s24q_nb_s_pos z
  have hsw := hs_small w hw
  have hswpos := s24q_nb_s_pos w
  have hcd := s24q_nb_cosh_dist_disc z w
  have hez := s24q_nb_one_div_s_le z
  have hew := s24q_nb_one_div_s_le w
  set sz := 1 - ‖cayley (z : ℂ)‖ ^ 2
  set sw := 1 - ‖cayley (w : ℂ)‖ ^ 2
  set Δ := ‖cayley (z : ℂ) - cayley (w : ℂ)‖
  have hQ : 0 < sz * sw := mul_pos hsz hswpos
  have hQ4 : sz * sw < 4 * δ ^ 2 := by nlinarith
  have hΔ2 : Δ ^ 2 < 4 * δ ^ 2 := by
    have : 0 ≤ Δ := norm_nonneg _
    nlinarith
  have hd : Real.exp (dist z w) ≤ 2 + 4 * Δ ^ 2 / (sz * sw) := by
    have h1 : Real.exp (dist z w) ≤ 2 * Real.cosh (dist z w) := by
      rw [Real.cosh_eq]
      have := Real.exp_pos (-dist z w)
      linarith
    rw [hcd] at h1
    have e : 2 * (1 + 2 * Δ ^ 2 / (sz * sw)) = 2 + 4 * Δ ^ 2 / (sz * sw) := by
      field_simp
      ring
    linarith
  have hexp : 1 / (sz * sw) ≤ Real.exp (dist z UpperHalfPlane.I) * Real.exp (dist w UpperHalfPlane.I) := by
    have := mul_le_mul hez hew (by positivity) (Real.exp_pos _).le
    rw [one_div, one_div, ← mul_inv] at this
    rwa [one_div]
  -- `e^{2P} ≥ 1/(24 δ²)`
  have hP : Real.exp (dist z UpperHalfPlane.I + dist w UpperHalfPlane.I - dist z w) ≥ 1 / (24 * δ ^ 2) := by
    rw [Real.exp_sub, Real.exp_add]
    have hd0 : 0 < Real.exp (dist z w) := Real.exp_pos _
    have hden : 0 < 2 + 4 * Δ ^ 2 / (sz * sw) := by positivity
    have h1 : (1 / (sz * sw)) / (2 + 4 * Δ ^ 2 / (sz * sw)) ≤
        Real.exp (dist z UpperHalfPlane.I) * Real.exp (dist w UpperHalfPlane.I) / Real.exp (dist z w) := by
      apply div_le_div₀ (by positivity) hexp hd0 hd
    have h2 : (1 / (sz * sw)) / (2 + 4 * Δ ^ 2 / (sz * sw)) = 1 / (2 * (sz * sw) + 4 * Δ ^ 2) := by
      field_simp
    have h3 : 1 / (24 * δ ^ 2) ≤ 1 / (2 * (sz * sw) + 4 * Δ ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    rw [h2] at h1
    exact h3.trans h1
  -- convert to `P > R`
  have hRP : R < (dist z UpperHalfPlane.I + dist w UpperHalfPlane.I - dist z w) / 2 := by
    have h1 : 1 / (24 * δ ^ 2) = Real.exp (2 * R) * (25 / 24) := by
      have : Real.exp (-R) ^ 2 = Real.exp (-(2 * R)) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [hδ, div_pow, this, Real.exp_neg]
      field_simp
      norm_num
    have h2 : Real.exp (2 * R) < Real.exp (dist z UpperHalfPlane.I + dist w UpperHalfPlane.I - dist z w) := by
      calc Real.exp (2 * R) < Real.exp (2 * R) * (25 / 24) := by
            have := Real.exp_pos (2 * R); nlinarith
        _ = 1 / (24 * δ ^ 2) := h1.symm
        _ ≤ _ := hP
    have := Real.exp_lt_exp.1 h2
    linarith
  have hgr := s24q_nb_gromov_le z w UpperHalfPlane.I u hu
  rw [dist_comm UpperHalfPlane.I z, dist_comm UpperHalfPlane.I w, dist_comm UpperHalfPlane.I u] at hgr
  linarith

/-- `1 - |cayley x| ≤ 4 e^{-ρ}`. -/
theorem s24q_nb_one_sub_norm_le (x : UpperHalfPlane) :
    1 - ‖cayley (x : ℂ)‖ ≤ 4 * Real.exp (-dist x UpperHalfPlane.I) := by
  have h := s24q_nb_s_le x
  have hpos := s24q_nb_s_pos x
  have hn0 : 0 ≤ ‖cayley (x : ℂ)‖ := norm_nonneg _
  have hn1 : ‖cayley (x : ℂ)‖ < 1 := by
    by_contra hcon; push Not at hcon
    nlinarith
  nlinarith

/-- A point of `ℍ` near the boundary is far from `i`. -/
theorem s24q_nb_far_of_norm {δ : ℝ} (hδ : 0 < δ) (x : UpperHalfPlane) (hx : 1 - δ < ‖cayley (x : ℂ)‖) :
    Real.log (1 / (2 * δ)) < dist x UpperHalfPlane.I := by
  have hpos := s24q_nb_s_pos x
  have hn0 : 0 ≤ ‖cayley (x : ℂ)‖ := norm_nonneg _
  have hn1 : ‖cayley (x : ℂ)‖ < 1 := by
    by_contra hcon; push Not at hcon
    nlinarith
  have h1 : 1 - ‖cayley (x : ℂ)‖ ^ 2 < 2 * δ := by nlinarith
  have h2 := s24q_nb_one_div_s_le x
  have h3 : 1 / (2 * δ) < 1 / (1 - ‖cayley (x : ℂ)‖ ^ 2) := by
    apply one_div_lt_one_div_of_lt hpos h1
  have h4 : 1 / (2 * δ) < Real.exp (dist x UpperHalfPlane.I) := h3.trans_le h2
  have := Real.log_lt_log (by positivity) h4
  rwa [Real.log_exp] at this

/-- **C2.** A quasi-isometric map `G : ℍ → ℍ` is uniformly Cauchy at the boundary: points near a common boundary
point go to points near each other, and boundary neighbourhoods go to boundary neighbourhoods. -/
theorem s24q_nb_cauchy (L c : ℝ) (hL : 1 ≤ L) (hc : 0 ≤ c) (G : UpperHalfPlane → UpperHalfPlane)
    (hqi : ∀ z w : UpperHalfPlane,
      dist z w / L - c ≤ dist (G z) (G w) ∧ dist (G z) (G w) ≤ L * dist z w + c) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ (ζ : Circle) (z w : UpperHalfPlane), ‖cayley (z : ℂ) - (ζ : ℂ)‖ < δ →
      ‖cayley (w : ℂ) - (ζ : ℂ)‖ < δ → ‖cayley (G z : ℂ) - cayley (G w : ℂ)‖ < ε) ∧
      ∀ z : UpperHalfPlane, 1 - δ < ‖cayley (z : ℂ)‖ → 1 - ε < ‖cayley (G z : ℂ)‖ := by
  have hL0 : 0 < L := by linarith
  obtain ⟨M, hM0, hmorse⟩ := s24q_nb_morse L c hL hc
  obtain ⟨R₁, hR₁⟩ := s24q_nb_escape ε hε
  set K := dist (G UpperHalfPlane.I) UpperHalfPlane.I with hK
  set R₂ := L * (R₁ + c + M + K) with hR₂
  obtain ⟨δ₁, hδ₁, hnear⟩ := s24q_nb_near R₂
  set δ₂ := Real.exp (-(L * (Real.log (4 / ε) + 1 + c + K))) / 2 with hδ₂
  have hδ₂0 : 0 < δ₂ := by positivity
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂0, fun ζ z w hz hw => ?_, fun z hz => ?_⟩
  · have hz' : ‖cayley (z : ℂ) - (ζ : ℂ)‖ < δ₁ := lt_of_lt_of_le hz (min_le_left _ _)
    have hw' : ‖cayley (w : ℂ) - (ζ : ℂ)‖ < δ₁ := lt_of_lt_of_le hw (min_le_left _ _)
    have hseg : ∀ u' : UpperHalfPlane, dist (G z) u' + dist u' (G w) = dist (G z) (G w) →
        R₁ ≤ dist u' UpperHalfPlane.I := by
      intro u' hu'
      obtain ⟨u, hu, hdu⟩ := ((hmorse G hqi z w).2) u' hu'
      have h1 := hnear ζ z w hz' hw' u hu
      have h2 := (hqi u UpperHalfPlane.I).1
      have h3 : R₁ + M + K ≤ dist (G u) (G UpperHalfPlane.I) := by
        have : R₂ / L - c = R₁ + M + K := by
          rw [hR₂]; field_simp; ring
        have h4 : R₂ / L ≤ dist u UpperHalfPlane.I / L := div_le_div_of_nonneg_right h1 hL0.le
        linarith
      have h5 := dist_triangle (G u) u' (G UpperHalfPlane.I)
      have h6 := dist_triangle u' UpperHalfPlane.I (G UpperHalfPlane.I)
      rw [dist_comm UpperHalfPlane.I (G UpperHalfPlane.I)] at h6
      have h7 : dist u' (G UpperHalfPlane.I) ≤ dist u' UpperHalfPlane.I + K := by
        rw [hK, dist_comm (G UpperHalfPlane.I) UpperHalfPlane.I]
        exact dist_triangle _ _ _
      linarith
    exact hR₁ (G z) (G w) hseg
  · have hz' : 1 - δ₂ < ‖cayley (z : ℂ)‖ := lt_of_le_of_lt (by linarith [min_le_right δ₁ δ₂]) hz
    have h1 := s24q_nb_far_of_norm hδ₂0 z hz'
    set A := L * (Real.log (4 / ε) + 1 + c + K) with hA
    have hδA : 1 / (2 * δ₂) = Real.exp A := by
      rw [hδ₂]
      have : Real.exp (-A) ≠ 0 := (Real.exp_pos _).ne'
      rw [Real.exp_neg]
      field_simp
    rw [hδA, Real.log_exp] at h1
    have h2 := (hqi z UpperHalfPlane.I).1
    have h3 : dist (G z) (G UpperHalfPlane.I) ≤ dist (G z) UpperHalfPlane.I + K := by
      rw [hK, dist_comm (G UpperHalfPlane.I) UpperHalfPlane.I]
      exact dist_triangle _ _ _
    have h4 : Real.log (4 / ε) + 1 < dist (G z) UpperHalfPlane.I := by
      have : A / L = Real.log (4 / ε) + 1 + c + K := by
        rw [hA]; field_simp
      have h5 : A / L < dist z UpperHalfPlane.I / L := div_lt_div_of_pos_right h1 hL0
      linarith
    have h5 := s24q_nb_one_sub_norm_le (G z)
    have h6 : Real.exp (-dist (G z) UpperHalfPlane.I) < Real.exp (-(Real.log (4 / ε) + 1)) :=
      Real.exp_lt_exp.2 (by linarith)
    have h7 : Real.exp (-(Real.log (4 / ε) + 1)) = Real.exp (-1) * (ε / 4) := by
      rw [neg_add, Real.exp_add, Real.exp_neg (Real.log (4 / ε)), Real.exp_log (by positivity)]
      field_simp
    have h8 : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    have h9 : 4 * Real.exp (-dist (G z) UpperHalfPlane.I) < ε := by
      calc 4 * Real.exp (-dist (G z) UpperHalfPlane.I) < 4 * (Real.exp (-1) * (ε / 4)) := by
            rw [← h7]; linarith
        _ = Real.exp (-1) * ε := by ring
        _ < 1 * ε := by gcongr
        _ = ε := one_mul ε
    linarith

/-- Points of the open unit disc are the Cayley images of points of `ℍ`, and `liftToC F` is `F` there. -/
theorem s24q_nb_disc_pt (F : UpperHalfPlane → UpperHalfPlane) {z : ℂ} (hz : ‖z‖ < 1) :
    ∃ x : UpperHalfPlane, cayley (x : ℂ) = z ∧ cayley (liftToC F (cayleyInv z)) = cayley ((F x : UpperHalfPlane) : ℂ) := by
  have him : 0 < (cayleyInv z).im := cayleyInv_mem_upperHalf hz
  refine ⟨UpperHalfPlane.ofComplex (cayleyInv z), ?_, ?_⟩
  · rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
    exact cayley_cayleyInv hz
  · rw [h23l_liftToC_eq F (show cayleyInv z ∈ upperHalf from him)]

/-- **C3.** The boundary limit of a quasi-isometric homeomorphism of `ℍ`: `cayley ∘ F ∘ cayley⁻¹` has a limit
`φ ζ` on the circle at every boundary point, and `φ` is continuous. -/
theorem s24q_nb_limit (F : UpperHalfPlane ≃ₜ UpperHalfPlane) (L c : ℝ) (hL : 1 ≤ L) (hc : 0 ≤ c)
    (hqi : ∀ z w : UpperHalfPlane,
      dist z w / L - c ≤ dist (F z) (F w) ∧ dist (F z) (F w) ≤ L * dist z w + c) :
    ∃ φ : Circle → Circle, Continuous φ ∧ ∀ ζ : Circle,
      Tendsto (fun z => cayley (liftToC F (cayleyInv z))) (𝓝[ball 0 1] (ζ : ℂ)) (𝓝 (φ ζ : ℂ)) := by
  set f : ℂ → ℂ := fun z => cayley (liftToC F (cayleyInv z)) with hf
  have hFqi : ∀ ε > 0, ∃ δ : ℝ, 0 < δ ∧ (∀ (ζ : Circle) (z w : UpperHalfPlane), ‖cayley (z : ℂ) - (ζ : ℂ)‖ < δ →
      ‖cayley (w : ℂ) - (ζ : ℂ)‖ < δ → ‖cayley (F z : ℂ) - cayley (F w : ℂ)‖ < ε) ∧
      ∀ z : UpperHalfPlane, 1 - δ < ‖cayley (z : ℂ)‖ → 1 - ε < ‖cayley (F z : ℂ)‖ :=
    fun ε hε => s24q_nb_cauchy L c hL hc F hqi ε hε
  have hne : ∀ ζ : Circle, (𝓝[ball (0 : ℂ) 1] (ζ : ℂ)).NeBot := by
    intro ζ
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_ball (0 : ℂ) one_ne_zero]
    simp
  -- the filter image is Cauchy
  have hcauchy : ∀ ζ : Circle, Cauchy (map f (𝓝[ball (0 : ℂ) 1] (ζ : ℂ))) := by
    intro ζ
    haveI := hne ζ
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨δ, hδ, hclose, -⟩ := hFqi ε hε
    have hU : ball (ζ : ℂ) δ ∩ ball (0 : ℂ) 1 ∈ 𝓝[ball (0 : ℂ) 1] (ζ : ℂ) :=
      inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hδ)) self_mem_nhdsWithin
    refine ⟨f '' (ball (ζ : ℂ) δ ∩ ball (0 : ℂ) 1), image_mem_map hU, ?_⟩
    rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩ _ ⟨w, ⟨hw1, hw2⟩, rfl⟩
    rw [mem_ball_zero_iff] at hz2 hw2
    obtain ⟨x, hx, hfx⟩ := s24q_nb_disc_pt F hz2
    obtain ⟨y, hy, hfy⟩ := s24q_nb_disc_pt F hw2
    have h1 : ‖cayley (x : ℂ) - (ζ : ℂ)‖ < δ := by
      rw [hx]; rwa [mem_ball, dist_eq_norm] at hz1
    have h2 : ‖cayley (y : ℂ) - (ζ : ℂ)‖ < δ := by
      rw [hy]; rwa [mem_ball, dist_eq_norm] at hw1
    have := hclose ζ x y h1 h2
    rw [dist_eq_norm]
    show ‖cayley (liftToC F (cayleyInv z)) - cayley (liftToC F (cayleyInv w))‖ < ε
    rw [hfx, hfy]
    exact this
  -- the limit exists and lies on the circle
  have hlim : ∀ ζ : Circle, ∃ y : Circle, Tendsto f (𝓝[ball (0 : ℂ) 1] (ζ : ℂ)) (𝓝 (y : ℂ)) := by
    intro ζ
    haveI := hne ζ
    obtain ⟨y, hy⟩ := CompleteSpace.complete (hcauchy ζ)
    have hy' : Tendsto f (𝓝[ball (0 : ℂ) 1] (ζ : ℂ)) (𝓝 y) := hy
    have hle : ‖y‖ ≤ 1 := by
      have hn : Tendsto (fun z => ‖f z‖) (𝓝[ball (0 : ℂ) 1] (ζ : ℂ)) (𝓝 ‖y‖) := hy'.norm
      refine le_of_tendsto hn ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [mem_ball_zero_iff] at hz
      obtain ⟨x, hx, hfx⟩ := s24q_nb_disc_pt F hz
      show ‖cayley (liftToC F (cayleyInv z))‖ ≤ 1
      rw [hfx]
      have h : ‖cayley ((F x : UpperHalfPlane) : ℂ)‖ < 1 := by
        have := cayley_mem_unitDisc (F x).im_pos
        simpa [unitDisc] using this
      exact h.le
    have hge : 1 ≤ ‖y‖ := by
      refine le_of_forall_sub_le fun ε hε => ?_
      obtain ⟨δ, hδ, -, hnorm⟩ := hFqi ε hε
      have hn : Tendsto (fun z => ‖f z‖) (𝓝[ball (0 : ℂ) 1] (ζ : ℂ)) (𝓝 ‖y‖) := hy'.norm
      have : 1 - ε ≤ ‖y‖ := by
        refine ge_of_tendsto hn ?_
        have hU : ball (ζ : ℂ) δ ∩ ball (0 : ℂ) 1 ∈ 𝓝[ball (0 : ℂ) 1] (ζ : ℂ) :=
          inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hδ)) self_mem_nhdsWithin
        filter_upwards [hU] with z hz
        obtain ⟨hz1, hz2⟩ := hz
        rw [mem_ball_zero_iff] at hz2
        obtain ⟨x, hx, hfx⟩ := s24q_nb_disc_pt F hz2
        have hzn : 1 - δ < ‖cayley (x : ℂ)‖ := by
          rw [hx]
          have : ‖(ζ : ℂ)‖ - ‖z‖ ≤ ‖(ζ : ℂ) - z‖ := norm_sub_norm_le _ _
          rw [mem_ball, dist_eq_norm, norm_sub_rev] at hz1
          rw [Circle.norm_coe] at this
          linarith
        have := hnorm x hzn
        show 1 - ε ≤ ‖cayley (liftToC F (cayleyInv z))‖
        rw [hfx]
        exact this.le
      linarith
    exact ⟨⟨y, mem_sphere_zero_iff_norm.2 (le_antisymm hle hge)⟩, hy'⟩
  choose φ hφ using hlim
  refine ⟨φ, ?_, hφ⟩
  rw [Metric.continuous_iff]
  intro ζ ε hε
  obtain ⟨δ, hδ, hclose, -⟩ := hFqi (ε / 3) (by positivity)
  refine ⟨δ / 2, by positivity, fun ζ' hζ' => ?_⟩
  have hζ'd : ‖(ζ' : ℂ) - ζ‖ < δ / 2 := by
    have : dist (ζ' : ℂ) (ζ : ℂ) < δ / 2 := hζ'
    rwa [dist_eq_norm] at this
  haveI := hne ζ
  haveI := hne ζ'
  have e1 : ∀ᶠ z in 𝓝[ball (0 : ℂ) 1] (ζ' : ℂ), dist (f z) (φ ζ' : ℂ) < ε / 3 :=
    (hφ ζ').eventually (ball_mem_nhds _ (by positivity))
  have e1' : ∀ᶠ z in 𝓝[ball (0 : ℂ) 1] (ζ' : ℂ), ‖z - (ζ' : ℂ)‖ < δ / 2 :=
    mem_nhdsWithin_of_mem_nhds (by
      have := ball_mem_nhds (ζ' : ℂ) (show 0 < δ / 2 by positivity)
      filter_upwards [this] with z hz
      rwa [mem_ball, dist_eq_norm] at hz)
  have e1'' : ∀ᶠ z in 𝓝[ball (0 : ℂ) 1] (ζ' : ℂ), z ∈ ball (0 : ℂ) 1 := self_mem_nhdsWithin
  obtain ⟨z, hz1, hz2, hz3⟩ := (e1.and (e1'.and e1'')).exists
  have f1 : ∀ᶠ w in 𝓝[ball (0 : ℂ) 1] (ζ : ℂ), dist (f w) (φ ζ : ℂ) < ε / 3 :=
    (hφ ζ).eventually (ball_mem_nhds _ (by positivity))
  have f1' : ∀ᶠ w in 𝓝[ball (0 : ℂ) 1] (ζ : ℂ), ‖w - (ζ : ℂ)‖ < δ / 2 :=
    mem_nhdsWithin_of_mem_nhds (by
      have := ball_mem_nhds (ζ : ℂ) (show 0 < δ / 2 by positivity)
      filter_upwards [this] with w hw
      rwa [mem_ball, dist_eq_norm] at hw)
  have f1'' : ∀ᶠ w in 𝓝[ball (0 : ℂ) 1] (ζ : ℂ), w ∈ ball (0 : ℂ) 1 := self_mem_nhdsWithin
  obtain ⟨w, hw1, hw2, hw3⟩ := (f1.and (f1'.and f1'')).exists
  rw [mem_ball_zero_iff] at hz3 hw3
  obtain ⟨x, hx, hfx⟩ := s24q_nb_disc_pt F hz3
  obtain ⟨y, hy, hfy⟩ := s24q_nb_disc_pt F hw3
  have hxz : ‖cayley (x : ℂ) - (ζ : ℂ)‖ < δ := by
    rw [hx]
    calc ‖z - (ζ : ℂ)‖ = ‖(z - (ζ' : ℂ)) + ((ζ' : ℂ) - ζ)‖ := by ring_nf
      _ ≤ ‖z - (ζ' : ℂ)‖ + ‖(ζ' : ℂ) - ζ‖ := norm_add_le _ _
      _ < δ := by linarith
  have hyw : ‖cayley (y : ℂ) - (ζ : ℂ)‖ < δ := by rw [hy]; linarith
  have hfine := hclose ζ x y hxz hyw
  have hfz : f z = cayley ((F x : UpperHalfPlane) : ℂ) := hfx
  have hfw : f w = cayley ((F y : UpperHalfPlane) : ℂ) := hfy
  show dist (φ ζ' : ℂ) (φ ζ : ℂ) < ε
  rw [dist_eq_norm] at hz1 hw1 ⊢
  have : ‖f z - f w‖ < ε / 3 := by rw [hfz, hfw]; exact hfine
  calc ‖(φ ζ' : ℂ) - (φ ζ : ℂ)‖ = ‖((φ ζ' : ℂ) - f z) + (f z - f w) + (f w - (φ ζ : ℂ))‖ := by ring_nf
    _ ≤ ‖(φ ζ' : ℂ) - f z‖ + ‖f z - f w‖ + ‖f w - (φ ζ : ℂ)‖ := norm_add₃_le
    _ < ε := by
      rw [norm_sub_rev (φ ζ' : ℂ) (f z)]
      linarith

/-- **D0.** The Cayley transform conjugates the action of `γ ∈ SL(2, ℝ)` on `ℍ` to the disc automorphism with the
coefficients of the statement of `s24q_nb_extension`. -/
theorem s24q_nb_cayley_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    cayley ((γ • τ : UpperHalfPlane) : ℂ) =
      ((((γ 0 0 + γ 1 1 : ℝ) : ℂ) + ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I) * cayley (τ : ℂ) +
          (((γ 0 0 - γ 1 1 : ℝ) : ℂ) - ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I)) /
        ((((γ 0 0 - γ 1 1 : ℝ) : ℂ) + ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I) * cayley (τ : ℂ) +
          (((γ 0 0 + γ 1 1 : ℝ) : ℂ) - ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I)) := by
  have hcz := h36t_den_ne γ τ
  have hzI := s24q_nb_add_I_ne τ
  have hγI := s24q_nb_add_I_ne (γ • τ)
  rw [h36t_coe_smul] at hγI ⊢
  push_cast
  generalize (τ : ℂ) = z at *
  generalize ((γ 0 0 : ℝ) : ℂ) = a at *
  generalize ((γ 0 1 : ℝ) : ℂ) = b at *
  generalize ((γ 1 0 : ℝ) : ℂ) = c at *
  generalize ((γ 1 1 : ℝ) : ℂ) = d at *
  have hu : (a * z + b) + I * (c * z + d) ≠ 0 := by
    intro h0
    apply hγI
    rw [div_add' _ _ _ hcz, h0, zero_div]
  have hden : ((a - d) + (b + c) * I) * ((z - I) / (z + I)) + ((a + d) - (b - c) * I) =
      2 * ((a * z + b) + I * (c * z + d)) / (z + I) := by
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  have hnum : ((a + d) + (b - c) * I) * ((z - I) / (z + I)) + ((a - d) - (b + c) * I) =
      2 * ((a * z + b) - I * (c * z + d)) / (z + I) := by
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  unfold cayley
  rw [hden, hnum]
  have e1' : (a * z + b) / (c * z + d) - I = ((a * z + b) - I * (c * z + d)) / (c * z + d) := by
    rw [sub_eq_add_neg, div_add' _ _ _ hcz]
    congr 1
    ring
  have e1'' : (a * z + b) / (c * z + d) + I = ((a * z + b) + I * (c * z + d)) / (c * z + d) :=
    div_add' _ _ _ hcz
  rw [e1', e1'', div_div_div_cancel_right₀ hcz]
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  field_simp

theorem s24q_nb_f_cayley (F : UpperHalfPlane → UpperHalfPlane) (y : UpperHalfPlane) :
    cayley (liftToC F (cayleyInv (cayley (y : ℂ)))) = cayley ((F y : UpperHalfPlane) : ℂ) := by
  rw [cayleyInv_cayley y.im_pos, h23l_liftToC_eq F (show (y : ℂ) ∈ upperHalf from y.im_pos),
    UpperHalfPlane.ofComplex_apply]

theorem s24q_nb_cayley_lt (y : UpperHalfPlane) : ‖cayley (y : ℂ)‖ < 1 := by
  have := cayley_mem_unitDisc y.im_pos
  simpa [unitDisc] using this

/-- The disc automorphism of `γ` has no pole on the closed unit disc. -/
theorem s24q_nb_disc_den_ne (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    (((γ 0 0 - γ 1 1 : ℝ) : ℂ) + ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I) * ζ +
      (((γ 0 0 + γ 1 1 : ℝ) : ℂ) - ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I) ≠ 0 := by
  intro h
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h1 := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h1
  set C : ℂ := ((γ 0 0 - γ 1 1 : ℝ) : ℂ) + ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I with hC
  set D : ℂ := ((γ 0 0 + γ 1 1 : ℝ) : ℂ) - ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I with hD
  have h1 : C * ζ = -D := by linear_combination h
  have h2 : ‖C‖ = ‖D‖ := by
    have := congrArg norm h1
    rw [norm_mul, hζ, mul_one, norm_neg] at this
    exact this
  have h3 : ‖C‖ ^ 2 = ‖D‖ ^ 2 := by rw [h2]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply] at h3
  simp only [hC, hD, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.add_im, Complex.sub_im, Complex.mul_im] at h3
  nlinarith [h3, hdet]

theorem s24q_nb_neBot (ζ : Circle) : (𝓝[ball (0 : ℂ) 1] (ζ : ℂ)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, closure_ball (0 : ℂ) one_ne_zero]
  simp

/-- Every point of the open unit disc is `cayley x`, `x ∈ ℍ`. -/
theorem s24q_nb_disc_pt' {z : ℂ} (hz : ‖z‖ < 1) : ∃ x : UpperHalfPlane, cayley (x : ℂ) = z := by
  have him : 0 < (cayleyInv z).im := cayleyInv_mem_upperHalf hz
  refine ⟨UpperHalfPlane.ofComplex (cayleyInv z), ?_⟩
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  exact cayley_cayleyInv hz

/-- The boundary maps of `F` and `F⁻¹` are mutually inverse. -/
theorem s24q_nb_inverse_limit (F : UpperHalfPlane ≃ₜ UpperHalfPlane) {φ ψ : Circle → Circle}
    (hφ : ∀ ζ : Circle,
      Tendsto (fun z => cayley (liftToC F (cayleyInv z))) (𝓝[ball (0 : ℂ) 1] (ζ : ℂ)) (𝓝 (φ ζ : ℂ)))
    (hψ : ∀ ζ : Circle,
      Tendsto (fun z => cayley (liftToC F.symm (cayleyInv z))) (𝓝[ball (0 : ℂ) 1] (ζ : ℂ)) (𝓝 (ψ ζ : ℂ))) :
    ∀ ζ : Circle, ψ (φ ζ) = ζ := by
  intro ζ
  haveI := s24q_nb_neBot ζ
  have h1 : Tendsto (fun z => cayley (liftToC F (cayleyInv z))) (𝓝[ball (0 : ℂ) 1] (ζ : ℂ))
      (𝓝[ball (0 : ℂ) 1] (φ ζ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hφ ζ, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [mem_ball_zero_iff] at hz
    obtain ⟨x, hx⟩ := s24q_nb_disc_pt' hz
    rw [← hx, s24q_nb_f_cayley, mem_ball_zero_iff]
    exact s24q_nb_cayley_lt _
  have h2 := (hψ (φ ζ)).comp h1
  have h3 : ∀ᶠ z in 𝓝[ball (0 : ℂ) 1] (ζ : ℂ),
      (fun z => cayley (liftToC F.symm (cayleyInv z))) (cayley (liftToC F (cayleyInv z))) = z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [mem_ball_zero_iff] at hz
    obtain ⟨x, hx⟩ := s24q_nb_disc_pt' hz
    show cayley (liftToC F.symm (cayleyInv (cayley (liftToC F (cayleyInv z))))) = z
    rw [← hx, s24q_nb_f_cayley, s24q_nb_f_cayley]
    simp [hx]
  have h4 : Tendsto (fun z : ℂ => z) (𝓝[ball (0 : ℂ) 1] (ζ : ℂ)) (𝓝 (ζ : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h5 : Tendsto ((fun z => cayley (liftToC F.symm (cayleyInv z))) ∘
      (fun z => cayley (liftToC F (cayleyInv z)))) (𝓝[ball (0 : ℂ) 1] (ζ : ℂ)) (𝓝 (ζ : ℂ)) :=
    h4.congr' (h3.mono fun z hz => hz.symm)
  exact Circle.ext (tendsto_nhds_unique h2 h5)

/-- The boundary map intertwines the Cayley conjugates of `γ` and `δ` when `F ∘ γ = δ ∘ F`. -/
theorem s24q_nb_equivariant (F : UpperHalfPlane ≃ₜ UpperHalfPlane) {φ : Circle → Circle}
    (hφ : ∀ ζ : Circle,
      Tendsto (fun z => cayley (liftToC F (cayleyInv z))) (𝓝[ball (0 : ℂ) 1] (ζ : ℂ)) (𝓝 (φ ζ : ℂ)))
    (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hFγ : ∀ τ, F (γ • τ) = δ • F τ) (ζ ζ' : Circle)
    (hζ' : (ζ' : ℂ) = ((((γ 0 0 + γ 1 1 : ℝ) : ℂ) + ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I) * ζ +
              (((γ 0 0 - γ 1 1 : ℝ) : ℂ) - ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I)) /
            ((((γ 0 0 - γ 1 1 : ℝ) : ℂ) + ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I) * ζ +
              (((γ 0 0 + γ 1 1 : ℝ) : ℂ) - ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I))) :
    (φ ζ' : ℂ) = ((((δ 0 0 + δ 1 1 : ℝ) : ℂ) + ((δ 0 1 - δ 1 0 : ℝ) : ℂ) * I) * (φ ζ) +
              (((δ 0 0 - δ 1 1 : ℝ) : ℂ) - ((δ 0 1 + δ 1 0 : ℝ) : ℂ) * I)) /
            ((((δ 0 0 - δ 1 1 : ℝ) : ℂ) + ((δ 0 1 + δ 1 0 : ℝ) : ℂ) * I) * (φ ζ) +
              (((δ 0 0 + δ 1 1 : ℝ) : ℂ) - ((δ 0 1 - δ 1 0 : ℝ) : ℂ) * I)) := by
  haveI := s24q_nb_neBot ζ
  set Cg : ℂ → ℂ := fun w =>
    ((((γ 0 0 + γ 1 1 : ℝ) : ℂ) + ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I) * w +
          (((γ 0 0 - γ 1 1 : ℝ) : ℂ) - ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I)) /
        ((((γ 0 0 - γ 1 1 : ℝ) : ℂ) + ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I) * w +
          (((γ 0 0 + γ 1 1 : ℝ) : ℂ) - ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I)) with hCg
  set Cd : ℂ → ℂ := fun w =>
    ((((δ 0 0 + δ 1 1 : ℝ) : ℂ) + ((δ 0 1 - δ 1 0 : ℝ) : ℂ) * I) * w +
          (((δ 0 0 - δ 1 1 : ℝ) : ℂ) - ((δ 0 1 + δ 1 0 : ℝ) : ℂ) * I)) /
        ((((δ 0 0 - δ 1 1 : ℝ) : ℂ) + ((δ 0 1 + δ 1 0 : ℝ) : ℂ) * I) * w +
          (((δ 0 0 + δ 1 1 : ℝ) : ℂ) - ((δ 0 1 - δ 1 0 : ℝ) : ℂ) * I)) with hCd
  have hcontg : ContinuousAt Cg (ζ : ℂ) := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    exact s24q_nb_disc_den_ne γ (Circle.norm_coe ζ)
  have hcontd : ContinuousAt Cd (φ ζ : ℂ) := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    exact s24q_nb_disc_den_ne δ (Circle.norm_coe (φ ζ))
  have hCgx : ∀ x : UpperHalfPlane, Cg (cayley (x : ℂ)) = cayley ((γ • x : UpperHalfPlane) : ℂ) := fun x =>
    (s24q_nb_cayley_smul γ x).symm
  have hCdx : ∀ x : UpperHalfPlane, Cd (cayley (x : ℂ)) = cayley ((δ • x : UpperHalfPlane) : ℂ) := fun x =>
    (s24q_nb_cayley_smul δ x).symm
  have hT : Tendsto Cg (𝓝[ball (0 : ℂ) 1] (ζ : ℂ)) (𝓝[ball (0 : ℂ) 1] (ζ' : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := hcontg.tendsto
      rw [show Cg (ζ : ℂ) = (ζ' : ℂ) from hζ'.symm] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      rw [mem_ball_zero_iff] at hw
      obtain ⟨x, hx⟩ := s24q_nb_disc_pt' hw
      rw [← hx, hCgx, mem_ball_zero_iff]
      exact s24q_nb_cayley_lt _
  have h1 := (hφ ζ').comp hT
  have h2 := hcontd.tendsto.comp (hφ ζ)
  have h3 : ∀ᶠ w in 𝓝[ball (0 : ℂ) 1] (ζ : ℂ),
      (fun z => cayley (liftToC F (cayleyInv z))) (Cg w) =
        Cd ((fun z => cayley (liftToC F (cayleyInv z))) w) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [mem_ball_zero_iff] at hw
    obtain ⟨x, hx⟩ := s24q_nb_disc_pt' hw
    show cayley (liftToC F (cayleyInv (Cg w))) = Cd (cayley (liftToC F (cayleyInv w)))
    rw [← hx, hCgx, s24q_nb_f_cayley, s24q_nb_f_cayley, hFγ, hCdx]
  exact tendsto_nhds_unique h1 (h2.congr' (h3.mono fun w hw => hw.symm))

theorem s24q_nb_lift_symm {p₀ : UpperHalfPlane → S₀} {p₁ : UpperHalfPlane → S₁} {f : S₀ ≃ₜ S₁}
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₀ p₁ f F) : IsLift p₁ p₀ f.symm F.symm := by
  intro τ
  apply f.injective
  rw [Homeomorph.apply_symm_apply, ← hF, Homeomorph.apply_symm_apply]

/-- **Nielsen extension (W2a).** The lift `F` of a homeomorphism between compact surfaces uniformized by Fuchsian groups
extends continuously to the boundary: read in the disc by the Cayley map, `C ∘ F ∘ C⁻¹` has a boundary map
`φ : S¹ → S¹`, which is a homeomorphism and intertwines the Cayley conjugates of `γ` and `δ` whenever
`F ∘ γ = δ ∘ F` (orientation is not needed here).  (Assembled from parts A–D.) -/
theorem s24q_nb_extension [T2Space S₀] [ConnectedSpace S₀] [CompactSpace S₀]
    [T2Space S₁] [ConnectedSpace S₁] [CompactSpace S₁]
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} {p₁ : UpperHalfPlane → S₁}
    (hΓ₀ : IsFuchsian Γ₀) (hfree₀ : ActsFreely Γ₀) (hp₀ : IsUniformization Γ₀ p₀)
    (hΓ₁ : IsFuchsian Γ₁) (hfree₁ : ActsFreely Γ₁) (hp₁ : IsUniformization Γ₁ p₁)
    {f : S₀ ≃ₜ S₁} {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₀ p₁ f F) :
    ∃ φ : Circle → Circle, Function.Bijective φ ∧ Continuous φ ∧
      (∀ ζ : Circle, Tendsto (fun z => cayley (liftToC F (cayleyInv z))) (𝓝[ball 0 1] (ζ : ℂ)) (𝓝 (φ ζ : ℂ))) ∧
      ∀ γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ ∈ Γ₀ → (∀ τ, F (γ • τ) = δ • F τ) →
        ∀ ζ ζ' : Circle,
          (ζ' : ℂ) = ((((γ 0 0 + γ 1 1 : ℝ) : ℂ) + ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I) * ζ +
              (((γ 0 0 - γ 1 1 : ℝ) : ℂ) - ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I)) /
            ((((γ 0 0 - γ 1 1 : ℝ) : ℂ) + ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I) * ζ +
              (((γ 0 0 + γ 1 1 : ℝ) : ℂ) - ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I)) →
          (φ ζ' : ℂ) = ((((δ 0 0 + δ 1 1 : ℝ) : ℂ) + ((δ 0 1 - δ 1 0 : ℝ) : ℂ) * I) * (φ ζ) +
              (((δ 0 0 - δ 1 1 : ℝ) : ℂ) - ((δ 0 1 + δ 1 0 : ℝ) : ℂ) * I)) /
            ((((δ 0 0 - δ 1 1 : ℝ) : ℂ) + ((δ 0 1 + δ 1 0 : ℝ) : ℂ) * I) * (φ ζ) +
              (((δ 0 0 + δ 1 1 : ℝ) : ℂ) - ((δ 0 1 - δ 1 0 : ℝ) : ℂ) * I)) := by
  have hF' := s24q_nb_lift_symm hF
  obtain ⟨K₀, hK₀c, hK₀⟩ := utm_exists_compact_translate hp₀
  obtain ⟨K₁, hK₁c, hK₁⟩ := utm_exists_compact_translate hp₁
  have hd : ∀ γ ∈ Γ₀, ∃ δ ∈ Γ₁, ∀ τ, F (γ • τ) = δ • F τ := fun γ hγ => h23l_deck hp₀ hp₁ hF hγ
  have hd' : ∀ δ ∈ Γ₁, ∃ γ ∈ Γ₀, ∀ τ, F (γ • τ) = δ • F τ := by
    intro δ hδ
    obtain ⟨γ, hγ, h⟩ := h23l_deck hp₁ hp₀ hF' hδ
    refine ⟨γ, hγ, fun τ => ?_⟩
    have := h (F τ)
    rw [Homeomorph.symm_apply_apply] at this
    rw [← this, Homeomorph.apply_symm_apply]
  have hd'' : ∀ γ ∈ Γ₀, ∃ δ ∈ Γ₁, ∀ τ, F.symm (δ • τ) = γ • F.symm τ := by
    intro γ hγ
    obtain ⟨δ, hδ, h⟩ := hd γ hγ
    refine ⟨δ, hδ, fun τ => ?_⟩
    have := h (F.symm τ)
    rw [Homeomorph.apply_symm_apply] at this
    rw [← this, Homeomorph.symm_apply_apply]
  obtain ⟨L, c, hL, hc, hqi⟩ := s24q_nb_qi F ⟨K₀, hK₀c, hK₀⟩ ⟨K₁, hK₁c, hK₁⟩ hd hd'
  obtain ⟨L', c', hL', hc', hqi'⟩ := s24q_nb_qi F.symm ⟨K₁, hK₁c, hK₁⟩ ⟨K₀, hK₀c, hK₀⟩
    (fun δ hδ => by
      obtain ⟨γ, hγ, h⟩ := hd' δ hδ
      exact ⟨γ, hγ, fun τ => by
        have := h (F.symm τ)
        rw [Homeomorph.apply_symm_apply] at this
        rw [← this]; simp⟩)
    (fun γ hγ => by
      obtain ⟨δ, hδ, h⟩ := hd γ hγ
      exact ⟨δ, hδ, fun τ => by
        have := h (F.symm τ)
        rw [Homeomorph.apply_symm_apply] at this
        rw [← this]; simp⟩)
  obtain ⟨φ, hφc, hφ⟩ := s24q_nb_limit F L c hL hc hqi
  obtain ⟨ψ, hψc, hψ⟩ := s24q_nb_limit F.symm L' c' hL' hc' hqi'
  have h1 := s24q_nb_inverse_limit F hφ hψ
  have h2 : ∀ ζ : Circle, φ (ψ ζ) = ζ := s24q_nb_inverse_limit F.symm hψ (by simpa using hφ)
  refine ⟨φ, ⟨?_, fun ζ => ⟨ψ ζ, h2 ζ⟩⟩, hφc, hφ, ?_⟩
  · intro a b hab
    rw [← h1 a, ← h1 b, hab]
  · intro γ δ _ hFγ ζ ζ' h
    exact s24q_nb_equivariant F hφ γ δ hFγ ζ ζ' h

/-- The local expression of a continuous map is continuous on its domain. -/
theorem s24q_nb_localMapExpr_continuousOn {f : S₀ → S₁} (hf : Continuous f) (x : S₀) :
    ContinuousOn (localMapExpr f x) (localMapDomain f x) := by
  have h1 : ContinuousOn (fun u => f ((chartAt ℂ x).symm u)) (localMapDomain f x) :=
    hf.comp_continuousOn ((chartAt ℂ x).continuousOn_symm.mono inter_subset_left)
  exact (chartAt ℂ (f x)).continuousOn.comp h1 fun u hu => hu.2

/-- **Orientation bridge (local, replaces `s24q_nb_lift_sensePreserving`).** The lift `F` of an orientation preserving
homeomorphism (all chart expressions sense preserving) has local winding number `+1` at every point of `ℍ`. -/
theorem s24q_nb_lift_localWinding [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} {p₁ : UpperHalfPlane → S₁}
    (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁) {f : S₀ ≃ₜ S₁}
    (hf : ∀ x : S₀, IsSensePreserving (localMapExpr f x) (localMapDomain f x))
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₀ p₁ f F) (τ : UpperHalfPlane) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        Complex.exp (Lg t) = liftToC F ((τ : ℂ) + ρ * Complex.exp (2 * π * Complex.I * t)) - liftToC F (τ : ℂ)) →
        Lg 1 - Lg 0 = 2 * π * Complex.I := by
  obtain ⟨U₀, hU₀o, hτU₀, hU₀H, hU₀s, hψ₀⟩ :=
    h23l_chart_proj (τ := τ) hp₀.1 hp₀.2.1 (p₀ τ) (mem_chart_source ℂ _)
  obtain ⟨U₁, hU₁o, hτU₁, -, -, hψ₁⟩ :=
    h23l_chart_proj (τ := F τ) hp₁.1 hp₁.2.1 (p₁ (F τ)) (mem_chart_source ℂ _)
  have hFx : p₁ (F τ) = f (p₀ τ) := hF τ
  have hkey : ∀ z ∈ U₀, chartAt ℂ (p₁ (F τ)) (p₁ (UpperHalfPlane.ofComplex (liftToC F z))) =
      localMapExpr f (p₀ τ) (chartAt ℂ (p₀ τ) (p₀ (UpperHalfPlane.ofComplex z))) := by
    intro z hz
    rw [h23l_liftToC_eq F (hU₀H hz), UpperHalfPlane.ofComplex_apply, hFx, hF (UpperHalfPlane.ofComplex z)]
    unfold localMapExpr
    rw [(chartAt ℂ (p₀ τ)).left_inv (hU₀s z hz)]
  set V : Set ℂ := (U₀ ∩ liftToC F ⁻¹' U₁) ∩
    (fun z => chartAt ℂ (p₀ τ) (p₀ (UpperHalfPlane.ofComplex z))) ⁻¹' localMapDomain f (p₀ τ) with hVdef
  have hV : IsOpen V :=
    (hψ₀.2.2.1.1.mono inter_subset_left).isOpen_inter_preimage
      (((h23l_liftToC_continuousOn F.continuous).mono hU₀H).isOpen_inter_preimage hU₀o hU₁o)
      (s23_localMapDomain_isOpen f.continuous _)
  have hτV : (τ : ℂ) ∈ V := by
    refine ⟨⟨hτU₀, ?_⟩, ?_⟩
    · show liftToC F (τ : ℂ) ∈ U₁
      rw [h23l_liftToC_coe]
      exact hτU₁
    · have e : UpperHalfPlane.ofComplex (τ : ℂ) = τ := UpperHalfPlane.ofComplex_apply τ
      simp only [mem_preimage, e]
      exact (s23_h_center f _).1
  have hc₀ := thm7_3_one_qc_conformal hψ₀
  have hc₁ := thm7_3_one_qc_conformal hψ₁
  have hFc : ContinuousAt (liftToC F) (τ : ℂ) :=
    (h23l_liftToC_continuousOn F.continuous).continuousAt (isOpen_upperHalf.mem_nhds τ.coe_im_pos)
  refine s24q_lw_winding_conj (U := V) (V := U₁) (D := localMapDomain f (p₀ τ))
    (ψ₀ := fun z => chartAt ℂ (p₀ τ) (p₀ (UpperHalfPlane.ofComplex z)))
    (ψ₁ := fun z => chartAt ℂ (p₁ (F τ)) (p₁ (UpperHalfPlane.ofComplex z)))
    (h := localMapExpr f (p₀ τ)) hV hτV hψ₁.1 (s23_localMapDomain_isOpen f.continuous _)
    (hc₀.1.mono (fun z hz => hz.1.1)) (hc₀.2.1.mono (fun z hz => hz.1.1))
    hc₁.1 hc₁.2.1 hFc ?_ (fun z hz => hz.2) ?_
    (s24q_nb_localMapExpr_continuousOn f.continuous _)
    (s23_c1_injOn_localMapExpr f.injective _) (hf _)
  · show liftToC F (τ : ℂ) ∈ U₁
    rw [h23l_liftToC_coe]
    exact hτU₁
  · intro z hz _
    exact hkey z hz.1.1

/-- Post-composition with a holomorphic injective map preserves the local winding number `+1`. -/
theorem s24q_nb_winding_postcomp {G M : ℂ → ℂ} {z₀ : ℂ} {U V : Set ℂ} (hU : IsOpen U) (hz₀ : z₀ ∈ U)
    (hGc : ContinuousOn G U) (hV : IsOpen V) (hGz : G z₀ ∈ V) (hMd : DifferentiableOn ℂ M V)
    (hMi : InjOn M V)
    (hw : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (Lg t) = G (z₀ + ρ * Complex.exp (2 * π * I * t)) - G z₀) →
        Lg 1 - Lg 0 = 2 * π * I) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (Lg t) = M (G (z₀ + ρ * Complex.exp (2 * π * I * t))) - M (G z₀)) →
        Lg 1 - Lg 0 = 2 * π * I := by
  obtain ⟨ρ₁, hρ₁, hw⟩ := hw
  set w₀ := G z₀ with hw₀
  set s : ℂ → ℂ := dslope M w₀ with hs
  have hκ : deriv M w₀ ≠ 0 := deriv_ne_zero_of_injOn hV hMd hMi hGz
  set κ := deriv M w₀ with hκdef
  have hVn : V ∈ 𝓝 w₀ := hV.mem_nhds hGz
  have hs_cont : ContinuousOn s V :=
    (continuousOn_dslope hVn).2 ⟨hMd.continuousOn, hMd.differentiableAt hVn⟩
  have hs_w₀ : s w₀ = κ := dslope_same M w₀
  have hsc : ContinuousAt s w₀ := hs_cont.continuousAt hVn
  have hκpos : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  obtain ⟨r, hr, hB⟩ : ∃ r > 0, ball w₀ r ⊆ V ∧ ∀ w ∈ ball w₀ r, ‖s w - κ‖ < ‖κ‖ := by
    have h1 : {w | ‖s w - κ‖ < ‖κ‖} ∈ 𝓝 w₀ := by
      have := hsc.tendsto
      rw [hs_w₀] at this
      have h := Filter.mem_map.1 (this (Metric.isOpen_ball.mem_nhds (mem_ball_self hκpos)))
      filter_upwards [h] with w hw
      simpa [dist_eq_norm] using hw
    obtain ⟨r, hr, hr'⟩ := Metric.mem_nhds_iff.1 (inter_mem hVn h1)
    exact ⟨r, hr, fun w hw => (hr' hw).1, fun w hw => (hr' hw).2⟩
  obtain ⟨δ, hδ, hδU, hδG⟩ : ∃ δ > 0, ball z₀ δ ⊆ U ∧ ∀ z ∈ ball z₀ δ, G z ∈ ball w₀ r := by
    have hGat : ContinuousAt G z₀ := hGc.continuousAt (hU.mem_nhds hz₀)
    have h1 : G ⁻¹' ball w₀ r ∈ 𝓝 z₀ := hGat.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (mem_ball_self hr))
    obtain ⟨δ, hδ, hδ'⟩ := Metric.mem_nhds_iff.1 (inter_mem (hU.mem_nhds hz₀) h1)
    exact ⟨δ, hδ, fun z hz => (hδ' hz).1, fun z hz => (hδ' hz).2⟩
  refine ⟨min ρ₁ δ, lt_min hρ₁ hδ, fun ρ hρ hρlt Lg hLgc hLge => ?_⟩
  set c : ℝ → ℂ := fun t => z₀ + ρ * Complex.exp (2 * π * I * t) with hc
  have hc_cont : Continuous c := by simp only [hc]; fun_prop
  have hc_mem : ∀ t, c t ∈ ball z₀ δ := fun t => by
    rw [mem_ball_iff_norm]
    simp only [hc, add_sub_cancel_left, norm_mul, Complex.norm_real]
    have : ‖Complex.exp (2 * π * I * (t : ℂ))‖ = 1 := by
      have e : (2 * π * I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
      rw [e]; exact Complex.norm_exp_ofReal_mul_I _
    rw [this, mul_one, Real.norm_of_nonneg hρ.le]
    exact lt_of_lt_of_le hρlt (min_le_right _ _)
  have hGcc : ContinuousOn (fun t => G (c t)) (Icc 0 1) :=
    hGc.comp hc_cont.continuousOn (fun t _ => hδU (hc_mem t))
  have hscc : ContinuousOn (fun t => s (G (c t))) (Icc 0 1) :=
    hs_cont.comp hGcc (fun t _ => hB.1 (hδG _ (hc_mem t)))
  have hslit : ∀ t, s (G (c t)) / κ ∈ slitPlane := fun t => by
    have h1 := hB.2 _ (hδG _ (hc_mem t))
    have h2 : ‖s (G (c t)) / κ - 1‖ < 1 := by
      have : s (G (c t)) / κ - 1 = (s (G (c t)) - κ) / κ := by field_simp
      rw [this, norm_div, div_lt_one hκpos]
      exact h1
    refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
    have h3 := Complex.abs_re_le_norm (s (G (c t)) / κ - 1)
    have h4 : (s (G (c t)) / κ - 1).re = (s (G (c t)) / κ).re - 1 := by simp
    rw [h4] at h3
    have := (abs_le.1 h3).1
    linarith
  set ℓ : ℝ → ℂ := fun t => Complex.log (s (G (c t)) / κ) with hℓ
  have hℓcont : ContinuousOn ℓ (Icc 0 1) :=
    (hscc.div_const κ).clog (fun t _ => hslit t)
  have hexpℓ : ∀ t, Complex.exp (ℓ t) = s (G (c t)) / κ := fun t =>
    Complex.exp_log (Complex.slitPlane_ne_zero (hslit t))
  have hsne : ∀ t, s (G (c t)) ≠ 0 := fun t h => by
    have := hexpℓ t
    rw [h, zero_div] at this
    exact Complex.exp_ne_zero _ this
  have hMs : ∀ t, M (G (c t)) - M w₀ = (G (c t) - w₀) * s (G (c t)) := fun t => by
    have := sub_smul_dslope M w₀ (G (c t))
    simpa [hs] using this.symm
  have hL₀ : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (Lg t - ℓ t - Complex.log κ) = G (c t) - G z₀ := by
    intro t ht
    rw [Complex.exp_sub, Complex.exp_sub, hLge t ht, hexpℓ, Complex.exp_log hκ]
    have := hsne t
    have h5 : M (G (z₀ + ρ * Complex.exp (2 * π * I * t))) - M (G z₀) = (G (c t) - w₀) * s (G (c t)) :=
      hMs t
    rw [h5]
    field_simp
    rfl
  have hL₀c : ContinuousOn (fun t => Lg t - ℓ t - Complex.log κ) (Icc 0 1) :=
    (hLgc.sub hℓcont).sub continuousOn_const
  have h2π := hw ρ hρ (lt_of_lt_of_le hρlt (min_le_left _ _)) _ hL₀c hL₀
  have hc10 : c 1 = c 0 := by
    simp only [hc]
    have : Complex.exp (2 * π * I * ((1 : ℝ) : ℂ)) = Complex.exp (2 * π * I * ((0 : ℝ) : ℂ)) := by
      simp [Complex.exp_two_pi_mul_I]
    rw [this]
  have hℓ10 : ℓ 1 = ℓ 0 := by simp only [hℓ, hc10]
  rw [hℓ10] at h2π
  linear_combination h2π

/-- `cayley (cayleyInv w) = w` for every `w ≠ 1`. -/
theorem s24q_nb_cayley_cayleyInv_ne {w : ℂ} (hw : w ≠ 1) : cayley (cayleyInv w) = w := by
  have hden : (1 : ℂ) - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
  have h1 : cayleyInv w - I = I * (2 * w) / (1 - w) := by
    rw [cayleyInv]; field_simp; ring
  have h2 : cayleyInv w + I = I * 2 / (1 - w) := by
    rw [cayleyInv]; field_simp; ring
  have h2ne : cayleyInv w + I ≠ 0 := by
    rw [h2]
    exact div_ne_zero (mul_ne_zero I_ne_zero two_ne_zero) hden
  rw [cayley, div_eq_iff h2ne, h1, h2]
  field_simp

/-- `cayleyInv` is injective off `1`. -/
theorem s24q_nb_cayleyInv_inj {w w' : ℂ} (hw : w ≠ 1) (hw' : w' ≠ 1) (h : cayleyInv w = cayleyInv w') :
    w = w' := by
  rw [← s24q_nb_cayley_cayleyInv_ne hw, ← s24q_nb_cayley_cayleyInv_ne hw', h]

/-- `cayleyInv` is real on the unit circle. -/
theorem s24q_nb_cayleyInv_im {w : ℂ} (hw : ‖w‖ = 1) : (cayleyInv w).im = 0 := by
  have hn : normSq w = 1 := by rw [← Complex.sq_norm, hw]; norm_num
  rw [cayleyInv, Complex.div_im, ← sub_div]
  have : (I * (1 + w)).im * (1 - w).re - (I * (1 + w)).re * (1 - w).im = 1 - normSq w := by
    simp [Complex.normSq_apply]; ring
  rw [this, hn]
  simp

/-- On the arc `(0, 2π)` the Cayley coordinate of `e^{iθ}` is `tan ((θ - π) / 2)`. -/
theorem s24q_nb_cayleyInv_exp {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * π) :
    cayleyInv (Complex.exp (θ * I)) = ((Real.tan ((θ - π) / 2) : ℝ) : ℂ) := by
  have hπ := Real.pi_pos
  set a := θ / 2 with ha
  have hθ : (θ : ℂ) = (a : ℂ) + (a : ℂ) := by rw [ha]; push_cast; ring
  have hs : 0 < Real.sin a :=
    Real.sin_pos_of_pos_of_lt_pi (by rw [ha]; linarith) (by rw [ha]; linarith)
  have htan : Real.tan ((θ - π) / 2) = -Real.cos a / Real.sin a := by
    have : (θ - π) / 2 = a - π / 2 := by rw [ha]; ring
    rw [this, Real.tan_eq_sin_div_cos, Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two]
  have hcs : ((Real.cos a : ℝ) : ℂ) ^ 2 + ((Real.sin a : ℝ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq a
  have hexp : Complex.exp (θ * I) = (((Real.cos a : ℝ) : ℂ) + ((Real.sin a : ℝ) : ℂ) * I) ^ 2 := by
    have e1 : Complex.exp ((a : ℂ) * I) = ((Real.cos a : ℝ) : ℂ) + ((Real.sin a : ℝ) : ℂ) * I := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [hθ, add_mul, Complex.exp_add, e1, sq]
  set c : ℂ := ((Real.cos a : ℝ) : ℂ) with hc
  set s : ℂ := ((Real.sin a : ℝ) : ℂ) with hsdef
  have hs0 : s ≠ 0 := by rw [hsdef]; exact_mod_cast hs.ne'
  have hz1 : (c + s * I) * (c - s * I) = 1 := by
    linear_combination hcs + (-(s ^ 2)) * Complex.I_sq
  have hz0 : c + s * I ≠ 0 := fun h => by
    rw [h, zero_mul] at hz1
    exact zero_ne_one hz1
  have h1pw : 1 + (c + s * I) ^ 2 = (c + s * I) * (2 * c) := by
    linear_combination (-1 : ℂ) * hcs + s ^ 2 * Complex.I_sq
  have h1mw : 1 - (c + s * I) ^ 2 = (c + s * I) * (-2 * s * I) := by
    linear_combination (-1 : ℂ) * hcs + s ^ 2 * Complex.I_sq
  rw [cayleyInv, hexp, h1pw, h1mw, htan, Complex.ofReal_div, Complex.ofReal_neg, ← hc, ← hsdef]
  have hz0' : c + I * s ≠ 0 := by rwa [mul_comm]
  field_simp

/-- A point `≠ 1` of the unit circle is `e^{iθ}` with `θ ∈ (0, 2π)`. -/
theorem s24q_nb_theta_exists {ζ : ℂ} (hζ : ‖ζ‖ = 1) (hζ1 : ζ ≠ 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 2 * π ∧ ζ = Complex.exp (θ * I) := by
  have hπ := Real.pi_pos
  have hexp : ζ = Complex.exp (Complex.arg ζ * I) := by
    have := Complex.norm_mul_exp_arg_mul_I ζ
    rw [hζ, Complex.ofReal_one, one_mul] at this
    exact this.symm
  rcases lt_trichotomy (Complex.arg ζ) 0 with hlt | heq | hgt
  · refine ⟨Complex.arg ζ + 2 * π, by linarith [Complex.neg_pi_lt_arg ζ], by linarith, ?_⟩
    have e : ((Complex.arg ζ + 2 * π : ℝ) : ℂ) * I = (Complex.arg ζ : ℂ) * I + 2 * π * I := by
      push_cast; ring
    rw [e, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    exact hexp
  · exact absurd (by rw [hexp, heq]; simp) hζ1
  · exact ⟨Complex.arg ζ, hgt, by linarith [Complex.arg_le_pi ζ], hexp⟩

/-- The Cayley coordinate is strictly increasing in the angle on `(0, 2π)`. -/
theorem s24q_nb_tan_lt {θ θ' : ℝ} (h0 : 0 < θ) (h : θ < θ') (h1 : θ' < 2 * π) :
    Real.tan ((θ - π) / 2) < Real.tan ((θ' - π) / 2) := by
  have hπ := Real.pi_pos
  exact Real.strictMonoOn_tan (by constructor <;> linarith) (by constructor <;> linarith) (by linarith)

/-- Every real number is the Cayley coordinate of some `e^{iθ}`, `θ ∈ (0, 2π)`. -/
theorem s24q_nb_theta_of_real (y : ℝ) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 2 * π ∧ Real.tan ((θ - π) / 2) = y := by
  have hπ := Real.pi_pos
  refine ⟨π + 2 * Real.arctan y, ?_, ?_, ?_⟩
  · linarith [Real.neg_pi_div_two_lt_arctan y]
  · linarith [Real.arctan_lt_pi_div_two y]
  · have : (π + 2 * Real.arctan y - π) / 2 = Real.arctan y := by ring
    rw [this, Real.tan_arctan]

theorem s24q_nb_int_le (a b : ℤ) (x y : ℝ) (hx0 : 0 < x) (hx1 : x < 2 * π) (hy0 : 0 < y) (hy1 : y < 2 * π)
    (h : x + a * (2 * π) < y + b * (2 * π)) : a ≤ b := by
  by_contra hc
  push_neg at hc
  have h1 : (b : ℝ) + 1 ≤ a := by exact_mod_cast hc
  nlinarith [mul_nonneg (sub_nonneg.2 h1) Real.pi_pos.le, Real.pi_pos]

/-- The angles of four points in positive cyclic order (given by increasing real arguments inside a window of length
`2π`) are cyclically increasing. -/
theorem s24q_nb_pattern {t θ : Fin 4 → ℝ} {n : Fin 4 → ℤ} (ht : StrictMono t) (ht4 : t 3 < t 0 + 2 * π)
    (hθ0 : ∀ i, 0 < θ i) (hθ1 : ∀ i, θ i < 2 * π) (hn : ∀ i, t i = θ i + n i * (2 * π)) :
    CyclicStrictMono (fun i => Real.tan ((θ i - π) / 2)) := by
  have hπ := Real.pi_pos
  have t01 : t 0 < t 1 := ht (by decide)
  have t12 : t 1 < t 2 := ht (by decide)
  have t23 : t 2 < t 3 := ht (by decide)
  have a01 : n 0 ≤ n 1 := s24q_nb_int_le _ _ _ _ (hθ0 0) (hθ1 0) (hθ0 1) (hθ1 1) (by rw [← hn 0, ← hn 1]; exact t01)
  have a12 : n 1 ≤ n 2 := s24q_nb_int_le _ _ _ _ (hθ0 1) (hθ1 1) (hθ0 2) (hθ1 2) (by rw [← hn 1, ← hn 2]; exact t12)
  have a23 : n 2 ≤ n 3 := s24q_nb_int_le _ _ _ _ (hθ0 2) (hθ1 2) (hθ0 3) (hθ1 3) (by rw [← hn 2, ← hn 3]; exact t23)
  have a30 : n 3 ≤ n 0 + 1 := s24q_nb_int_le (n 3) (n 0 + 1) (θ 3) (θ 0) (hθ0 3) (hθ1 3) (hθ0 0) (hθ1 0) (by
    have := hn 3; have := hn 0; push_cast; linarith)
  have hcase : (n 1 = n 0 ∧ n 2 = n 0 ∧ n 3 = n 0) ∨ (n 1 = n 0 ∧ n 2 = n 0 ∧ n 3 = n 0 + 1) ∨
      (n 1 = n 0 ∧ n 2 = n 0 + 1 ∧ n 3 = n 0 + 1) ∨ (n 1 = n 0 + 1 ∧ n 2 = n 0 + 1 ∧ n 3 = n 0 + 1) := by omega
  have hn0 := hn 0
  have hn1 := hn 1
  have hn2 := hn 2
  have hn3 := hn 3
  rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have e1 : (n 1 : ℝ) = n 0 := by exact_mod_cast h1
    have e2 : (n 2 : ℝ) = n 0 := by exact_mod_cast h2
    have e3 : (n 3 : ℝ) = n 0 := by exact_mod_cast h3
    rw [e1] at hn1; rw [e2] at hn2; rw [e3] at hn3
    have c1 : θ 0 < θ 1 := by linarith
    have c2 : θ 1 < θ 2 := by linarith
    have c3 : θ 2 < θ 3 := by linarith
    exact cyclicStrictMono_of_chain 0 (s24q_nb_tan_lt (hθ0 _) c1 (hθ1 _))
      (s24q_nb_tan_lt (hθ0 _) c2 (hθ1 _)) (s24q_nb_tan_lt (hθ0 _) c3 (hθ1 _))
  · have e1 : (n 1 : ℝ) = n 0 := by exact_mod_cast h1
    have e2 : (n 2 : ℝ) = n 0 := by exact_mod_cast h2
    have e3 : (n 3 : ℝ) = n 0 + 1 := by exact_mod_cast h3
    rw [e1] at hn1; rw [e2] at hn2; rw [e3] at hn3
    have c1 : θ 3 < θ 0 := by linarith
    have c2 : θ 0 < θ 1 := by linarith
    have c3 : θ 1 < θ 2 := by linarith
    exact cyclicStrictMono_of_chain 3 (s24q_nb_tan_lt (hθ0 _) c1 (hθ1 _))
      (s24q_nb_tan_lt (hθ0 _) c2 (hθ1 _)) (s24q_nb_tan_lt (hθ0 _) c3 (hθ1 _))
  · have e1 : (n 1 : ℝ) = n 0 := by exact_mod_cast h1
    have e2 : (n 2 : ℝ) = n 0 + 1 := by exact_mod_cast h2
    have e3 : (n 3 : ℝ) = n 0 + 1 := by exact_mod_cast h3
    rw [e1] at hn1; rw [e2] at hn2; rw [e3] at hn3
    have c1 : θ 2 < θ 3 := by linarith
    have c2 : θ 3 < θ 0 := by linarith
    have c3 : θ 0 < θ 1 := by linarith
    exact cyclicStrictMono_of_chain 2 (s24q_nb_tan_lt (hθ0 _) c1 (hθ1 _))
      (s24q_nb_tan_lt (hθ0 _) c2 (hθ1 _)) (s24q_nb_tan_lt (hθ0 _) c3 (hθ1 _))
  · have e1 : (n 1 : ℝ) = n 0 + 1 := by exact_mod_cast h1
    have e2 : (n 2 : ℝ) = n 0 + 1 := by exact_mod_cast h2
    have e3 : (n 3 : ℝ) = n 0 + 1 := by exact_mod_cast h3
    rw [e1] at hn1; rw [e2] at hn2; rw [e3] at hn3
    have c1 : θ 1 < θ 2 := by linarith
    have c2 : θ 2 < θ 3 := by linarith
    have c3 : θ 3 < θ 0 := by linarith
    exact cyclicStrictMono_of_chain 1 (s24q_nb_tan_lt (hθ0 _) c1 (hθ1 _))
      (s24q_nb_tan_lt (hθ0 _) c2 (hθ1 _)) (s24q_nb_tan_lt (hθ0 _) c3 (hθ1 _))

/-- Four points `≠ 1` of the unit circle in positive cyclic order have cyclically ordered real Cayley coordinates. -/
theorem s24q_nb_x_cyc {ζ : Fin 4 → ℂ} {t : Fin 4 → ℝ} (ht : StrictMono t) (ht4 : t 3 < t 0 + 2 * π)
    (hζ : ∀ i, ζ i = Complex.exp (t i * I)) (hζ1 : ∀ i, ζ i ≠ 1) :
    ∃ x : Fin 4 → ℝ, CyclicStrictMono x ∧ ∀ i, cayleyInv (ζ i) = (x i : ℂ) := by
  have hnorm : ∀ i, ‖ζ i‖ = 1 := fun i => by rw [hζ i]; exact Complex.norm_exp_ofReal_mul_I _
  choose θ hθ0 hθ1 hθe using fun i => s24q_nb_theta_exists (hnorm i) (hζ1 i)
  have hn : ∀ i, ∃ n : ℤ, t i = θ i + n * (2 * π) := fun i => by
    refine CircleLift.sub_eq_int_mul_two_pi ?_
    rw [← hζ i, hθe i]
  choose n hn using hn
  refine ⟨fun i => Real.tan ((θ i - π) / 2), s24q_nb_pattern ht ht4 hθ0 hθ1 hn, fun i => ?_⟩
  rw [hθe i]
  exact s24q_nb_cayleyInv_exp (hθ0 i) (hθ1 i)

theorem s24q_nb_exp_ne_one {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * π) : Complex.exp (θ * I) ≠ 1 := by
  intro h
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h
  have : (θ : ℂ) = (m : ℂ) * (2 * π) := by
    have h2 : (θ : ℂ) * I = ((m : ℂ) * (2 * π)) * I := by rw [hm]; ring
    exact mul_right_cancel₀ Complex.I_ne_zero h2
  have h3 : θ = (m : ℝ) * (2 * π) := by exact_mod_cast this
  have hπ := Real.pi_pos
  have h4 : (0 : ℝ) < m := by
    by_contra hc
    push_neg at hc
    nlinarith
  have h5 : (m : ℝ) < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith
  have h6 : (0 : ℤ) < m := by exact_mod_cast h4
  have h7 : m < 1 := by exact_mod_cast h5
  omega

theorem s24q_nb_strictMono4 {f : Fin 4 → ℝ} (h0 : f 0 < f 1) (h1 : f 1 < f 2) (h2 : f 2 < f 3) :
    StrictMono f := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem s24q_nb_exp_shift (a : ℝ) (m : ℤ) :
    Complex.exp (((a + m * (2 * π) : ℝ) : ℂ) * I) = Complex.exp ((a : ℂ) * I) := by
  have : (((a + m * (2 * π) : ℝ) : ℂ) * I) = (a : ℂ) * I + m * (2 * π * I) := by push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- A cyclically increasing quadruple in `(0, 2π)` is, after shifting by multiples of `2π`, increasing in a window of
length `2π`. -/
theorem s24q_nb_unrotate {θ : Fin 4 → ℝ} (h0 : ∀ i, 0 < θ i) (h1 : ∀ i, θ i < 2 * π) {k : Fin 4}
    (hk : StrictMono fun i => θ (i + k)) :
    ∃ s : Fin 4 → ℝ, StrictMono s ∧ s 3 < s 0 + 2 * π ∧ ∀ i, ∃ m : ℤ, s i = θ i + m * (2 * π) := by
  have hπ := Real.pi_pos
  have c01 : θ (0 + k) < θ (1 + k) := hk (by decide)
  have c12 : θ (1 + k) < θ (2 + k) := hk (by decide)
  have c23 : θ (2 + k) < θ (3 + k) := hk (by decide)
  fin_cases k
  · simp only [Fin.zero_eta, add_zero] at c01 c12 c23
    refine ⟨θ, s24q_nb_strictMono4 c01 c12 c23, by linarith [h0 0, h1 3], fun i => ⟨0, by simp⟩⟩
  · have a1 : θ 1 < θ 2 := c01
    have a2 : θ 2 < θ 3 := c12
    have a3 : θ 3 < θ 0 := c23
    refine ⟨fun i => θ i + (![-1, 0, 0, 0] i : ℤ) * (2 * π), ?_, ?_, fun i => ⟨_, rfl⟩⟩
    · refine s24q_nb_strictMono4 ?_ ?_ ?_
      · show θ 0 + ((-1 : ℤ) : ℝ) * (2 * π) < θ 1 + ((0 : ℤ) : ℝ) * (2 * π)
        push_cast; linarith [h0 1, h1 0]
      · show θ 1 + ((0 : ℤ) : ℝ) * (2 * π) < θ 2 + ((0 : ℤ) : ℝ) * (2 * π)
        push_cast; linarith
      · show θ 2 + ((0 : ℤ) : ℝ) * (2 * π) < θ 3 + ((0 : ℤ) : ℝ) * (2 * π)
        push_cast; linarith
    · show θ 3 + ((0 : ℤ) : ℝ) * (2 * π) < θ 0 + ((-1 : ℤ) : ℝ) * (2 * π) + 2 * π
      push_cast; linarith
  · have a1 : θ 2 < θ 3 := c01
    have a2 : θ 3 < θ 0 := c12
    have a3 : θ 0 < θ 1 := c23
    refine ⟨fun i => θ i + (![-1, -1, 0, 0] i : ℤ) * (2 * π), ?_, ?_, fun i => ⟨_, rfl⟩⟩
    · refine s24q_nb_strictMono4 ?_ ?_ ?_
      · show θ 0 + ((-1 : ℤ) : ℝ) * (2 * π) < θ 1 + ((-1 : ℤ) : ℝ) * (2 * π)
        push_cast; linarith
      · show θ 1 + ((-1 : ℤ) : ℝ) * (2 * π) < θ 2 + ((0 : ℤ) : ℝ) * (2 * π)
        push_cast; linarith [h0 2, h1 1]
      · show θ 2 + ((0 : ℤ) : ℝ) * (2 * π) < θ 3 + ((0 : ℤ) : ℝ) * (2 * π)
        push_cast; linarith
    · show θ 3 + ((0 : ℤ) : ℝ) * (2 * π) < θ 0 + ((-1 : ℤ) : ℝ) * (2 * π) + 2 * π
      push_cast; linarith
  · have a1 : θ 3 < θ 0 := c01
    have a2 : θ 0 < θ 1 := c12
    have a3 : θ 1 < θ 2 := c23
    refine ⟨fun i => θ i + (![-1, -1, -1, 0] i : ℤ) * (2 * π), ?_, ?_, fun i => ⟨_, rfl⟩⟩
    · refine s24q_nb_strictMono4 ?_ ?_ ?_
      · show θ 0 + ((-1 : ℤ) : ℝ) * (2 * π) < θ 1 + ((-1 : ℤ) : ℝ) * (2 * π)
        push_cast; linarith
      · show θ 1 + ((-1 : ℤ) : ℝ) * (2 * π) < θ 2 + ((-1 : ℤ) : ℝ) * (2 * π)
        push_cast; linarith
      · show θ 2 + ((-1 : ℤ) : ℝ) * (2 * π) < θ 3 + ((0 : ℤ) : ℝ) * (2 * π)
        push_cast; linarith [h0 3, h1 2]
    · show θ 3 + ((0 : ℤ) : ℝ) * (2 * π) < θ 0 + ((-1 : ℤ) : ℝ) * (2 * π) + 2 * π
      push_cast; linarith

/-- Cyclically ordered real numbers give four points of the circle in positive cyclic order. -/
theorem s24q_nb_y_unrotate {w : Fin 4 → ℂ} {y : Fin 4 → ℝ} (hy : CyclicStrictMono y)
    (hw : ∀ i, cayleyInv (w i) = (y i : ℂ)) (hw1 : ∀ i, w i ≠ 1) :
    ∃ s : Fin 4 → ℝ, StrictMono s ∧ s 3 < s 0 + 2 * π ∧ ∀ i, w i = Complex.exp (s i * I) := by
  have hπ := Real.pi_pos
  choose θ hθ0 hθ1 hθy using fun i => s24q_nb_theta_of_real (y i)
  have hwθ : ∀ i, w i = Complex.exp (θ i * I) := fun i => by
    refine s24q_nb_cayleyInv_inj (hw1 i) (s24q_nb_exp_ne_one (hθ0 i) (hθ1 i)) ?_
    rw [hw i, s24q_nb_cayleyInv_exp (hθ0 i) (hθ1 i), hθy i]
  have hlt : ∀ i j, y i < y j → θ i < θ j := fun i j hij => by
    by_contra hc
    push_neg at hc
    rcases hc.lt_or_eq with hc | hc
    · have := s24q_nb_tan_lt (hθ0 j) hc (hθ1 i)
      rw [hθy, hθy] at this
      linarith
    · have e : y i = y j := by rw [← hθy i, ← hθy j, hc]
      exact absurd e hij.ne
  obtain ⟨k, hk⟩ := hy
  have hθk : StrictMono fun i => θ (i + k) := fun i j hij => hlt _ _ (hk hij)
  obtain ⟨s, hs, hs3, hsm⟩ := s24q_nb_unrotate hθ0 hθ1 hθk
  refine ⟨s, hs, hs3, fun i => ?_⟩
  obtain ⟨m, hm⟩ := hsm i
  rw [hm, s24q_nb_exp_shift, hwθ i]

theorem s24q_nb_range_circle : range ((↑) : Circle → ℂ) = sphere (0 : ℂ) 1 := by
  ext z
  constructor
  · rintro ⟨ζ, rfl⟩
    rw [mem_sphere_zero_iff_norm]
    exact Circle.norm_coe ζ
  · intro hz
    rw [mem_sphere_zero_iff_norm] at hz
    refine ⟨Circle.exp (Complex.arg z), ?_⟩
    rw [Circle.coe_exp]
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hz, Complex.ofReal_one, one_mul] at this
    exact this

theorem s24q_nb_circ_of_norm {z : ℂ} (hz : ‖z‖ = 1) : ∃ ζ : Circle, (ζ : ℂ) = z := by
  have : z ∈ range ((↑) : Circle → ℂ) := by
    rw [s24q_nb_range_circle, mem_sphere_zero_iff_norm]; exact hz
  exact this

theorem s24q_nb_closedBall_eq : closedBall (0 : ℂ) 1 = ball 0 1 ∪ range ((↑) : Circle → ℂ) := by
  rw [s24q_nb_range_circle]
  ext z
  simp only [mem_closedBall_zero_iff, mem_union, mem_ball_zero_iff, mem_sphere_zero_iff_norm]
  constructor
  · intro h; exact h.lt_or_eq.imp id id
  · rintro (h | h)
    · exact h.le
    · exact h.le

/-- The disc map of a lift with boundary map `φ`, rotated by `u`. -/
theorem s24q_nb_disc_map (F : UpperHalfPlane ≃ₜ UpperHalfPlane) {φ : Circle → Circle}
    (hφ : Function.Bijective φ) (hφc : Continuous φ)
    (hlim : ∀ ζ : Circle,
      Tendsto (fun z => cayley (liftToC F (cayleyInv z))) (𝓝[ball (0 : ℂ) 1] (ζ : ℂ)) (𝓝 (φ ζ : ℂ)))
    {u : ℂ} (hu : ‖u‖ = 1) :
    ∃ Ψ : ℂ → ℂ, (∀ z : ℂ, ‖z‖ < 1 → Ψ z = u * cayley (liftToC F (cayleyInv z))) ∧
      (∀ ζ : Circle, Ψ ζ = u * (φ ζ : ℂ)) ∧ ContinuousOn Ψ (closedBall 0 1) ∧
      InjOn Ψ (closedBall 0 1) ∧ Ψ '' closedBall 0 1 = closedBall 0 1 ∧ (∀ z : ℂ, ‖z‖ < 1 → ‖Ψ z‖ < 1) ∧
      (∀ ζ : Circle, ‖Ψ ζ‖ = 1) := by
  classical
  have hu0 : u ≠ 0 := norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)
  set I' : ℂ → ℂ := fun z => cayley (liftToC F (cayleyInv z)) with hI'
  have hIx : ∀ x : UpperHalfPlane, I' (cayley x) = cayley (F x) := s24q_nb_f_cayley F
  have hIlt : ∀ z : ℂ, ‖z‖ < 1 → ‖I' z‖ < 1 := by
    intro z hz
    obtain ⟨x, rfl⟩ := s24q_nb_disc_pt' hz
    rw [hIx]
    exact s24q_nb_cayley_lt _
  have hIinj : ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 → I' z = I' w → z = w := by
    intro z w hz hw h
    obtain ⟨x, rfl⟩ := s24q_nb_disc_pt' hz
    obtain ⟨y, rfl⟩ := s24q_nb_disc_pt' hw
    rw [hIx, hIx] at h
    have h1 : (F x : ℂ) = (F y : ℂ) := by
      have := congrArg cayleyInv h
      rwa [cayleyInv_cayley (F x).im_pos, cayleyInv_cayley (F y).im_pos] at this
    have h2 : x = y := F.injective (UpperHalfPlane.ext h1)
    rw [h2]
  have hIsurj : ∀ w : ℂ, ‖w‖ < 1 → ∃ z : ℂ, ‖z‖ < 1 ∧ I' z = w := by
    intro w hw
    obtain ⟨x, rfl⟩ := s24q_nb_disc_pt' hw
    refine ⟨cayley ((F.symm x : UpperHalfPlane) : ℂ), s24q_nb_cayley_lt _, ?_⟩
    rw [hIx, F.apply_symm_apply]
  set Ψ : ℂ → ℂ := fun z =>
    if ‖z‖ < 1 then u * I' z else u * ((φ (Circle.exp (Complex.arg z)) : Circle) : ℂ) with hΨ
  have hΨint : ∀ z : ℂ, ‖z‖ < 1 → Ψ z = u * I' z := fun z hz => by simp [hΨ, hz]
  have hexp_arg : ∀ ζ : Circle, Circle.exp (Complex.arg (ζ : ℂ)) = ζ := fun ζ => by
    apply Circle.ext
    rw [Circle.coe_exp]
    have := Complex.norm_mul_exp_arg_mul_I (ζ : ℂ)
    rw [Circle.norm_coe, Complex.ofReal_one, one_mul] at this
    exact this
  have hΨcirc : ∀ ζ : Circle, Ψ ζ = u * (φ ζ : ℂ) := by
    intro ζ
    have : ¬ ‖(ζ : ℂ)‖ < 1 := by simp
    simp only [hΨ, this, ite_false, hexp_arg]
  have hΨnorm : ∀ ζ : Circle, ‖Ψ ζ‖ = 1 := fun ζ => by
    rw [hΨcirc, norm_mul, hu, Circle.norm_coe, one_mul]
  have hΨlt : ∀ z : ℂ, ‖z‖ < 1 → ‖Ψ z‖ < 1 := fun z hz => by
    rw [hΨint z hz, norm_mul, hu, one_mul]
    exact hIlt z hz
  refine ⟨Ψ, hΨint, hΨcirc, ?_, ?_, ?_, hΨlt, hΨnorm⟩
  · -- continuity
    intro z hz
    rw [s24q_nb_closedBall_eq] at hz
    rcases hz with hz | ⟨ζ, hζ0⟩
    · have hz' : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
      have hIc : ContinuousAt I' z := by
        have h1 : ContinuousAt cayleyInv z := by
          unfold cayleyInv
          exact ContinuousAt.div (by fun_prop) (by fun_prop) (cayleyInv_den_ne_zero hz')
        have hup : cayleyInv z ∈ upperHalf := cayleyInv_mem_upperHalf hz'
        have h2 : ContinuousAt (liftToC F) (cayleyInv z) :=
          (h23l_liftToC_continuousOn F.continuous).continuousAt (isOpen_upperHalf.mem_nhds hup)
        have hpos : 0 < (liftToC F (cayleyInv z)).im := by
          rw [h23l_liftToC_eq F hup]
          exact (F _).im_pos
        have h3 : ContinuousAt cayley (liftToC F (cayleyInv z)) := by
          unfold cayley
          exact ContinuousAt.div (by fun_prop) (by fun_prop) (cayley_den_ne_zero hpos)
        exact ContinuousAt.comp (g := cayley) (f := fun z => liftToC F (cayleyInv z)) h3 (h2.comp h1)
      have : ContinuousAt (fun w => u * I' w) z := continuousAt_const.mul hIc
      refine (this.congr ?_).continuousWithinAt
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact (hΨint w (mem_ball_zero_iff.1 hw)).symm
    · -- boundary point
      have hζ1 : (ζ : ℂ) = z := hζ0
      subst hζ1
      have hemb : Topology.IsInducing ((↑) : Circle → ℂ) := Topology.IsInducing.subtypeVal
      have hwithin : ContinuousWithinAt Ψ (range ((↑) : Circle → ℂ)) (ζ : ℂ) := by
        have h1 : Continuous fun ζ' : Circle => Ψ ζ' := by
          have : (fun ζ' : Circle => Ψ ζ') = fun ζ' => u * (φ ζ' : ℂ) := funext hΨcirc
          rw [this]
          exact continuous_const.mul (continuous_subtype_val.comp hφc)
        unfold ContinuousWithinAt
        rw [← hemb.map_nhds_eq, tendsto_map'_iff]
        exact h1.tendsto ζ
      have hball : ContinuousWithinAt Ψ (ball 0 1) (ζ : ℂ) := by
        unfold ContinuousWithinAt
        rw [hΨcirc ζ]
        refine ((hlim ζ).const_mul u).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact (hΨint w (mem_ball_zero_iff.1 hw)).symm
      rw [s24q_nb_closedBall_eq]
      exact hball.union hwithin
  · -- injectivity
    intro z hz w hw h
    rw [s24q_nb_closedBall_eq] at hz hw
    rcases hz with hz | ⟨ζ, hζ0⟩ <;> rcases hw with hw | ⟨ζ', hζ0'⟩
    · have hz' := mem_ball_zero_iff.1 hz
      have hw' := mem_ball_zero_iff.1 hw
      rw [hΨint z hz', hΨint w hw'] at h
      exact hIinj z w hz' hw' (mul_left_cancel₀ hu0 h)
    · have hz' := mem_ball_zero_iff.1 hz
      have hζ1 : (ζ' : ℂ) = w := hζ0'
      subst hζ1
      have h1 := hΨlt z hz'
      have h2 := hΨnorm ζ'
      rw [h] at h1
      linarith
    · have hw' := mem_ball_zero_iff.1 hw
      have hζ1 : (ζ : ℂ) = z := hζ0
      subst hζ1
      have h1 := hΨlt w hw'
      have h2 := hΨnorm ζ
      rw [← h] at h1
      linarith
    · have hζ1 : (ζ : ℂ) = z := hζ0
      have hζ1' : (ζ' : ℂ) = w := hζ0'
      subst hζ1 hζ1'
      have h' : u * (φ ζ : ℂ) = u * (φ ζ' : ℂ) := (hΨcirc ζ).symm.trans (h.trans (hΨcirc ζ'))
      have h1 : φ ζ = φ ζ' := Circle.ext (mul_left_cancel₀ hu0 h')
      rw [hφ.1 h1]
  · -- surjectivity
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [s24q_nb_closedBall_eq] at hz
      rcases hz with hz | ⟨ζ, hζ0⟩
      · exact mem_closedBall_zero_iff.2 (hΨlt z (mem_ball_zero_iff.1 hz)).le
      · have hζ1 : (ζ : ℂ) = z := hζ0
        subst hζ1
        exact mem_closedBall_zero_iff.2 (hΨnorm ζ).le
    · intro hw
      rw [mem_closedBall_zero_iff] at hw
      rcases hw.lt_or_eq with hw | hw
      · have hn : ‖u⁻¹ * w‖ < 1 := by rw [norm_mul, norm_inv, hu, inv_one, one_mul]; exact hw
        obtain ⟨z, hz, hzw⟩ := hIsurj _ hn
        refine ⟨z, mem_closedBall_zero_iff.2 hz.le, ?_⟩
        rw [hΨint z hz, hzw, mul_inv_cancel_left₀ hu0]
      · have hn : ‖u⁻¹ * w‖ = 1 := by rw [norm_mul, norm_inv, hu, inv_one, one_mul]; exact hw
        obtain ⟨ζ', hζ'⟩ := s24q_nb_circ_of_norm hn
        obtain ⟨ζ, hζ⟩ := hφ.2 ζ'
        refine ⟨ζ, ?_, ?_⟩
        · rw [mem_closedBall_zero_iff]; simp
        · rw [hΨcirc, hζ, hζ', mul_inv_cancel_left₀ hu0]

theorem s24q_nb_T_coe {w : ℂ} (hw : w ≠ 1) :
    mobiusExt I I (-1) 1 (w : ExtPlane) = ((cayleyInv w : ℂ) : ExtPlane) := by
  have hden : (-1 : ℂ) * w + 1 ≠ 0 := by
    intro h; apply hw; linear_combination -h
  rw [mobiusExt_coe hden]
  congr 1
  rw [mobiusFn, cayleyInv]
  congr 1 <;> ring

theorem s24q_nb_S_coe {z : ℂ} (hz : z + I ≠ 0) :
    mobiusExt 1 (-I) 1 I (z : ExtPlane) = ((cayley z : ℂ) : ExtPlane) := by
  have hden : (1 : ℂ) * z + I ≠ 0 := by rwa [one_mul]
  rw [mobiusExt_coe hden]
  congr 1
  rw [mobiusFn, cayley]
  congr 1 <;> ring

/-- The extension of `g = cayleyInv ∘ Ψ ∘ cayley` to the closed half-plane in `ℂ̄`. -/
theorem s24q_nb_ext_map (F : UpperHalfPlane ≃ₜ UpperHalfPlane) {φ : Circle → Circle}
    (hφ : Function.Bijective φ) (hφc : Continuous φ)
    (hlim : ∀ ζ : Circle,
      Tendsto (fun z => cayley (liftToC F (cayleyInv z))) (𝓝[ball (0 : ℂ) 1] (ζ : ℂ)) (𝓝 (φ ζ : ℂ)))
    {u : ℂ} (hu : ‖u‖ = 1) (hu1 : u * (φ 1 : ℂ) = 1) :
    ∃ (g : ℂ → ℂ) (G : ExtPlane → ExtPlane), IsHomeoExtension g upperHalf upperHalf G ∧
      g '' upperHalf = upperHalf ∧ G extInf = extInf ∧
      (∀ z ∈ upperHalf, g z = cayleyInv (u * cayley (liftToC F z))) ∧
      (∀ (x : ℝ) (ζ : Circle), cayley (x : ℂ) = ζ → u * (φ ζ : ℂ) ≠ 1 →
        G ((x : ℂ) : ExtPlane) = ((cayleyInv (u * (φ ζ : ℂ)) : ℂ) : ExtPlane)) := by
  classical
  obtain ⟨Ψ, h1, h2, h3, h4, h5, h6, h7⟩ := s24q_nb_disc_map F hφ hφc hlim hu
  set T : ExtPlane → ExtPlane := mobiusExt I I (-1) 1 with hT
  set S : ExtPlane → ExtPlane := mobiusExt 1 (-I) 1 I with hS
  have hTc : Continuous T := continuous_mobiusExt scExt_cayley_det
  have hSc : Continuous S := continuous_mobiusExt scExt_cayley_inv_det
  have hTS : ∀ p, T (S p) = p := fun p => scExt_cayley_apply_inv p
  have hST : ∀ q, S (T q) = q := fun q => by
    have := mobiusExt_inv_apply scExt_cayley_det q
    simpa using this
  set Ψt : ExtPlane → ExtPlane := fun q => OnePoint.elim q extInf (fun z => ((Ψ z : ℂ) : ExtPlane)) with hΨt
  have hΨtc : ∀ z : ℂ, Ψt (z : ExtPlane) = ((Ψ z : ℂ) : ExtPlane) := fun z => rfl
  set G : ExtPlane → ExtPlane := fun p => T (Ψt (S p)) with hG
  set g : ℂ → ℂ := fun z => cayleyInv (Ψ (cayley z)) with hg
  -- the closure of ℍ in ℂ̄
  have hcl : closure (toExt upperHalf) = T '' toExt (closedBall (0 : ℂ) 1) := by
    set Th := mobiusHomeomorph I I (-1) 1 scExt_cayley_det with hTh
    have hThT : ∀ w, Th w = T w := fun w => rfl
    have e1 : toExt upperHalf = Th '' toExt unitDisc := by
      rw [show (Th : ExtPlane → ExtPlane) = T from funext hThT]
      exact scExt_cayley_image_disc.symm
    rw [e1, ← Th.image_closure, unitDisc, scExt_closure_toExt_of_isBounded Metric.isBounded_ball,
      closure_ball (0 : ℂ) one_ne_zero]
    rfl
  have hmaps : ∀ p ∈ closure (toExt upperHalf), ∃ z ∈ closedBall (0 : ℂ) 1, S p = (z : ExtPlane) := by
    intro p hp
    rw [hcl] at hp
    obtain ⟨q, ⟨z, hz, rfl⟩, rfl⟩ := hp
    exact ⟨z, hz, hST _⟩
  have hSmem : ∀ p ∈ closure (toExt upperHalf), S p ∈ toExt (closedBall (0 : ℂ) 1) := by
    intro p hp
    obtain ⟨z, hz, hz'⟩ := hmaps p hp
    rw [hz']
    exact ⟨z, hz, rfl⟩
  refine ⟨g, G, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- agreement on ℍ
    intro z hz
    have hz' : 0 < z.im := hz
    have hS' : S (z : ExtPlane) = ((cayley z : ℂ) : ExtPlane) := s24q_nb_S_coe (cayley_den_ne_zero hz')
    have hlt : ‖Ψ (cayley z)‖ < 1 := h6 _ (mem_ball_zero_iff.1 (cayley_mem_unitDisc hz'))
    have hne : Ψ (cayley z) ≠ 1 := fun h => by rw [h, norm_one] at hlt; exact lt_irrefl _ hlt
    show T (Ψt (S (z : ExtPlane))) = _
    rw [hS', hΨtc]
    exact s24q_nb_T_coe hne
  · -- continuity
    have hΨtcont : ContinuousOn Ψt (toExt (closedBall (0 : ℂ) 1)) := by
      rintro _ ⟨z, hz, rfl⟩
      have hmap : 𝓝[toExt (closedBall (0 : ℂ) 1)] ((z : ℂ) : ExtPlane) =
          Filter.map ((↑) : ℂ → ExtPlane) (𝓝[closedBall (0 : ℂ) 1] z) :=
        (OnePoint.isOpenEmbedding_coe.isEmbedding.map_nhdsWithin_eq _ _).symm
      unfold ContinuousWithinAt
      rw [hmap, tendsto_map'_iff]
      have : (Ψt ∘ ((↑) : ℂ → ExtPlane)) = ((↑) : ℂ → ExtPlane) ∘ Ψ := funext hΨtc
      rw [this, hΨtc]
      exact (OnePoint.continuous_coe.tendsto _).comp (h3 z hz)
    exact hTc.comp_continuousOn (hΨtcont.comp hSc.continuousOn hSmem)
  · -- injectivity
    intro p hp p' hp' h
    obtain ⟨z, hz, hz'⟩ := hmaps p hp
    obtain ⟨z', hz'', hz'''⟩ := hmaps p' hp'
    have e : T (Ψt (S p)) = T (Ψt (S p')) := h
    rw [hz', hz''', hΨtc, hΨtc] at e
    have e2 : ((Ψ z : ℂ) : ExtPlane) = ((Ψ z' : ℂ) : ExtPlane) := by
      have := congrArg S e
      rwa [hST, hST] at this
    have e3 : z = z' := h4 hz hz'' (OnePoint.coe_injective e2)
    rw [← hTS p, ← hTS p', hz', hz''', e3]
  · -- image
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨z, hz, hz'⟩ := hmaps p hp
      show T (Ψt (S p)) ∈ _
      rw [hz', hΨtc, hcl]
      refine ⟨_, ⟨Ψ z, ?_, rfl⟩, rfl⟩
      exact h5.subset ⟨z, hz, rfl⟩
    · intro hq
      rw [hcl] at hq
      obtain ⟨r, ⟨w, hw, rfl⟩, rfl⟩ := hq
      rw [← h5] at hw
      obtain ⟨z, hz, rfl⟩ := hw
      refine ⟨T (z : ExtPlane), ?_, ?_⟩
      · rw [hcl]; exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      · show T (Ψt (S (T (z : ExtPlane)))) = _
        rw [hST, hΨtc]
  · -- g maps ℍ onto ℍ
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : 0 < z.im := hz
      have hlt : ‖Ψ (cayley z)‖ < 1 := h6 _ (mem_ball_zero_iff.1 (cayley_mem_unitDisc hz'))
      exact cayleyInv_mem_upperHalf hlt
    · intro hy
      have hy' : 0 < y.im := hy
      have hw : ‖cayley y‖ < 1 := mem_ball_zero_iff.1 (cayley_mem_unitDisc hy')
      have hmem : cayley y ∈ Ψ '' closedBall (0 : ℂ) 1 := by
        rw [h5]; exact mem_closedBall_zero_iff.2 hw.le
      obtain ⟨z', hz', hz'e⟩ := hmem
      have hzlt : ‖z'‖ < 1 := by
        rcases (mem_closedBall_zero_iff.1 hz').lt_or_eq with h | h
        · exact h
        · exfalso
          obtain ⟨ζ, hζ⟩ := s24q_nb_circ_of_norm h
          have hζ' : (ζ : ℂ) = z' := hζ
          subst hζ'
          have := h7 ζ
          rw [hz'e] at this
          linarith
      refine ⟨cayleyInv z', cayleyInv_mem_upperHalf hzlt, ?_⟩
      show cayleyInv (Ψ (cayley (cayleyInv z'))) = y
      rw [cayley_cayleyInv hzlt, hz'e, cayleyInv_cayley hy']
  · -- fixes ∞
    show T (Ψt (S extInf)) = extInf
    have : S extInf = ((1 : ℂ) : ExtPlane) := by
      rw [hS, mobiusExt_infty_of_ne one_ne_zero, div_one]
    rw [this, hΨtc]
    have h1' : Ψ 1 = 1 := by
      have := h2 1
      rw [Circle.coe_one] at this
      rw [this, hu1]
    rw [h1', hT]
    exact mobiusExt_coe_of_eq_zero (by norm_num)
  · -- formula for g
    intro z hz
    have hz' : 0 < z.im := hz
    show cayleyInv (Ψ (cayley z)) = _
    rw [h1 _ (mem_ball_zero_iff.1 (cayley_mem_unitDisc hz')), cayleyInv_cayley hz']
  · -- values on the real axis
    intro x ζ hx hne
    have hxI : (x : ℂ) + I ≠ 0 := fun h => by simpa using congrArg Complex.im h
    show T (Ψt (S ((x : ℂ) : ExtPlane))) = _
    have hS' : S ((x : ℂ) : ExtPlane) = ((cayley (x : ℂ) : ℂ) : ExtPlane) := s24q_nb_S_coe hxI
    rw [hS', hx, hΨtc, h2 ζ]
    exact s24q_nb_T_coe hne

theorem s24q_nb_rot_diff {u : ℂ} (hu : ‖u‖ = 1) :
    DifferentiableOn ℂ (fun w => cayleyInv (u * cayley w)) upperHalf := by
  intro w hw
  have hw' : 0 < w.im := hw
  apply DifferentiableAt.differentiableWithinAt
  have hc : DifferentiableAt ℂ cayley w := by
    unfold cayley
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) (cayley_den_ne_zero hw')
  have hlt : ‖u * cayley w‖ < 1 := by
    rw [norm_mul, hu, one_mul]
    exact mem_ball_zero_iff.1 (cayley_mem_unitDisc hw')
  have hci : DifferentiableAt ℂ cayleyInv (u * cayley w) := by
    unfold cayleyInv
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) (cayleyInv_den_ne_zero hlt)
  exact hci.comp w (hc.const_mul u)

theorem s24q_nb_rot_inj {u : ℂ} (hu : ‖u‖ = 1) :
    InjOn (fun w => cayleyInv (u * cayley w)) upperHalf := by
  have hu0 : u ≠ 0 := norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)
  intro w hw w' hw' h
  have hw1 : 0 < w.im := hw
  have hw1' : 0 < w'.im := hw'
  have hlt : ‖u * cayley w‖ < 1 := by
    rw [norm_mul, hu, one_mul]; exact mem_ball_zero_iff.1 (cayley_mem_unitDisc hw1)
  have hlt' : ‖u * cayley w'‖ < 1 := by
    rw [norm_mul, hu, one_mul]; exact mem_ball_zero_iff.1 (cayley_mem_unitDisc hw1')
  have h1 : u * cayley w = u * cayley w' := by
    have := congrArg cayley h
    simp only at this
    rwa [cayley_cayleyInv hlt, cayley_cayleyInv hlt'] at this
  have h2 := mul_left_cancel₀ hu0 h1
  have := congrArg cayleyInv h2
  rwa [cayleyInv_cayley hw1, cayleyInv_cayley hw1'] at this

theorem s24q_nb_rot_maps {u : ℂ} (hu : ‖u‖ = 1) {w : ℂ} (hw : w ∈ upperHalf) :
    cayleyInv (u * cayley w) ∈ upperHalf := by
  have hw1 : 0 < w.im := hw
  apply cayleyInv_mem_upperHalf
  rw [norm_mul, hu, one_mul]
  exact mem_ball_zero_iff.1 (cayley_mem_unitDisc hw1)

/-- The cyclic order of four boundary points `≠ 1` is preserved. -/
theorem s24q_nb_cyclic_avoid {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {τ₀ : UpperHalfPlane}
    (hw : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        Complex.exp (Lg t) =
          liftToC F ((τ₀ : ℂ) + ρ * Complex.exp (2 * π * Complex.I * t)) - liftToC F (τ₀ : ℂ)) →
        Lg 1 - Lg 0 = 2 * π * Complex.I)
    {φ : Circle → Circle} (hφ : Function.Bijective φ) (hφc : Continuous φ)
    (hlim : ∀ ζ : Circle,
      Tendsto (fun z => cayley (liftToC F (cayleyInv z))) (𝓝[ball 0 1] (ζ : ℂ)) (𝓝 (φ ζ : ℂ)))
    (ζ : Fin 4 → Circle) (t : Fin 4 → ℝ) (ht : StrictMono t) (ht4 : t 3 < t 0 + 2 * π)
    (hζ : ∀ i, (ζ i : ℂ) = Complex.exp (t i * I)) (hζ1 : ∀ i, (ζ i : ℂ) ≠ 1) :
    ∃ s : Fin 4 → ℝ, StrictMono s ∧ s 3 < s 0 + 2 * π ∧ ∀ i, (φ (ζ i) : ℂ) = Complex.exp (s i * I) := by
  have hπ := Real.pi_pos
  set u : ℂ := conj ((φ 1 : Circle) : ℂ) with hudef
  have hu : ‖u‖ = 1 := by rw [hudef, Complex.norm_conj, Circle.norm_coe]
  have hu0 : u ≠ 0 := norm_ne_zero_iff.1 (by rw [hu]; exact one_ne_zero)
  have hu1 : u * ((φ 1 : Circle) : ℂ) = 1 := by
    rw [hudef, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    simp
  obtain ⟨g, G, hG, hgs, hinf, hgform, hval⟩ := s24q_nb_ext_map F hφ hφc hlim hu hu1
  have hz₀ : (τ₀ : ℂ) ∈ upperHalf := τ₀.im_pos
  -- the local winding of `g`
  have hloc : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = g ((τ₀ : ℂ) + ρ * Complex.exp (2 * π * I * t)) - g (τ₀ : ℂ)) →
      L 1 - L 0 = 2 * π * I := by
    have hGz : liftToC F (τ₀ : ℂ) ∈ upperHalf := by
      rw [h23l_liftToC_coe]; exact (F τ₀).im_pos
    obtain ⟨ρ₁, hρ₁, hρ⟩ := s24q_nb_winding_postcomp (G := liftToC F)
      (M := fun w => cayleyInv (u * cayley w)) (U := upperHalf) isOpen_upperHalf hz₀
      (h23l_liftToC_continuousOn F.continuous) isOpen_upperHalf hGz (s24q_nb_rot_diff hu)
      (s24q_nb_rot_inj hu) hw
    refine ⟨min ρ₁ (τ₀ : ℂ).im, lt_min hρ₁ τ₀.im_pos, fun ρ hρ0 hρlt L hLc hLe => ?_⟩
    refine hρ ρ hρ0 (lt_of_lt_of_le hρlt (min_le_left _ _)) L hLc (fun t ht => ?_)
    have hρim : ρ < (τ₀ : ℂ).im := lt_of_lt_of_le hρlt (min_le_right _ _)
    have hmem : (τ₀ : ℂ) + ρ * Complex.exp (2 * π * I * t) ∈ upperHalf := by
      show 0 < ((τ₀ : ℂ) + ρ * Complex.exp (2 * π * I * t)).im
      have h1 : ‖(ρ : ℂ) * Complex.exp (2 * π * I * t)‖ = ρ := by
        have e : (2 * π * I * (t : ℂ)) = ((2 * π * t : ℝ) : ℂ) * I := by push_cast; ring
        rw [norm_mul, Complex.norm_real, e, Complex.norm_exp_ofReal_mul_I, mul_one,
          Real.norm_of_nonneg hρ0.le]
      have h2 := Complex.abs_im_le_norm ((ρ : ℂ) * Complex.exp (2 * π * I * t))
      rw [h1] at h2
      have h3 := (abs_le.1 h2).1
      rw [Complex.add_im]
      linarith
    have := hLe t ht
    rw [hgform _ hmem, hgform _ hz₀] at this
    exact this
  have hcyc := cyclicOrder_preserved_of_isHomeoExtension_of_fixes_infty hG hgs hinf hz₀ hloc
  -- real coordinates
  obtain ⟨x, hx, hxζ⟩ := s24q_nb_x_cyc (ζ := fun i => (ζ i : ℂ)) ht ht4 hζ hζ1
  have hζne : ∀ i, ζ i ≠ 1 := fun i h => hζ1 i (by rw [h]; rfl)
  have hcay : ∀ i, cayley ((x i : ℝ) : ℂ) = (ζ i : ℂ) := fun i => by
    rw [← hxζ i]; exact s24q_nb_cayley_cayleyInv_ne (hζ1 i)
  have hwne : ∀ i, u * ((φ (ζ i) : Circle) : ℂ) ≠ 1 := fun i h => by
    have : φ (ζ i) = φ 1 := by
      apply Circle.ext
      exact mul_left_cancel₀ hu0 (h.trans hu1.symm)
    exact hζne i (hφ.1 this)
  have hwnorm : ∀ i, ‖u * ((φ (ζ i) : Circle) : ℂ)‖ = 1 := fun i => by
    rw [norm_mul, hu, Circle.norm_coe, one_mul]
  set y : Fin 4 → ℝ := fun i => (cayleyInv (u * ((φ (ζ i) : Circle) : ℂ))).re with hy
  have hyc : ∀ i, cayleyInv (u * ((φ (ζ i) : Circle) : ℂ)) = (y i : ℂ) := fun i => by
    apply Complex.ext
    · simp [hy]
    · simp [hy, s24q_nb_cayleyInv_im (hwnorm i)]
  have hGy : ∀ i, G (((x i : ℝ) : ℂ) : ExtPlane) = (((y i : ℝ) : ℂ) : ExtPlane) := fun i => by
    rw [hval (x i) (ζ i) (hcay i) (hwne i), hyc i]
  have hycyc := hcyc x hx y hGy
  obtain ⟨s', hs', hs'3, hs'e⟩ := s24q_nb_y_unrotate (w := fun i => u * ((φ (ζ i) : Circle) : ℂ)) hycyc hyc hwne
  refine ⟨fun i => s' i - Complex.arg u, fun i j hij => by simpa using hs' hij, by
    simp only; linarith, fun i => ?_⟩
  have hue : u = Complex.exp (Complex.arg u * I) := by
    have := Complex.norm_mul_exp_arg_mul_I u
    rw [hu, Complex.ofReal_one, one_mul] at this
    exact this.symm
  have h1 := hs'e i
  have e : Complex.exp (((s' i - Complex.arg u : ℝ) : ℂ) * I) =
      Complex.exp ((s' i : ℂ) * I) / Complex.exp (Complex.arg u * I) := by
    rw [← Complex.exp_sub]; congr 1; push_cast; ring
  show _ = Complex.exp (((s' i - Complex.arg u : ℝ) : ℂ) * I)
  rw [e, ← h1, ← hue]
  field_simp

/-- Two angles in `(0, 2π)` with the same exponential coincide. -/
theorem s24q_nb_window_unique {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 2 * π) (hb0 : 0 < b) (hb1 : b < 2 * π)
    (h : Complex.exp (a * I) = Complex.exp (b * I)) : a = b := by
  obtain ⟨m, hm⟩ := CircleLift.sub_eq_int_mul_two_pi h
  have hπ := Real.pi_pos
  have h1 : (m : ℝ) < 1 := by
    by_contra hc; push_neg at hc; nlinarith
  have h2 : (-1 : ℝ) < m := by
    by_contra hc; push_neg at hc; nlinarith
  have h3 : m < 1 := by exact_mod_cast h1
  have h4 : -1 < m := by exact_mod_cast h2
  have : m = 0 := by omega
  rw [this] at hm
  simpa using hm

/-- Rotating the quadruple one step. -/
theorem s24q_nb_rot_H {ζ : Fin 4 → Circle} {t : Fin 4 → ℝ} (ht : StrictMono t) (ht4 : t 3 < t 0 + 2 * π)
    (hζ : ∀ i, (ζ i : ℂ) = Complex.exp (t i * I)) :
    ∃ t' : Fin 4 → ℝ, StrictMono t' ∧ t' 3 < t' 0 + 2 * π ∧ ∀ i, (ζ (i + 1) : ℂ) = Complex.exp (t' i * I) := by
  have hπ := Real.pi_pos
  have t01 : t 0 < t 1 := ht (by decide)
  have t12 : t 1 < t 2 := ht (by decide)
  have t23 : t 2 < t 3 := ht (by decide)
  refine ⟨![t 1, t 2, t 3, t 0 + 2 * π], s24q_nb_strictMono4 t12 t23 (by show t 3 < t 0 + 2 * π; exact ht4),
    by show t 0 + 2 * π < t 1 + 2 * π; linarith, fun i => ?_⟩
  fin_cases i
  · exact hζ 1
  · exact hζ 2
  · exact hζ 3
  · show (ζ 0 : ℂ) = Complex.exp (((t 0 + 2 * π : ℝ) : ℂ) * I)
    have e : (((t 0 + 2 * π : ℝ) : ℂ) * I) = (t 0 : ℂ) * I + (1 : ℤ) * (2 * π * I) := by push_cast; ring
    rw [hζ 0, e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem s24q_nb_rot_R {φ : Circle → Circle} {ζ : Fin 4 → Circle}
    (h : ∃ s : Fin 4 → ℝ, StrictMono s ∧ s 3 < s 0 + 2 * π ∧ ∀ i, (φ (ζ (i + 1)) : ℂ) = Complex.exp (s i * I)) :
    ∃ s : Fin 4 → ℝ, StrictMono s ∧ s 3 < s 0 + 2 * π ∧ ∀ i, (φ (ζ i) : ℂ) = Complex.exp (s i * I) := by
  obtain ⟨s, hs, hs3, hse⟩ := h
  have hπ := Real.pi_pos
  have s01 : s 0 < s 1 := hs (by decide)
  have s12 : s 1 < s 2 := hs (by decide)
  have s23 : s 2 < s 3 := hs (by decide)
  refine ⟨![s 3 - 2 * π, s 0, s 1, s 2], s24q_nb_strictMono4 (by show s 3 - 2 * π < s 0; linarith) s01 s12,
    by show s 2 < s 3 - 2 * π + 2 * π; linarith, fun i => ?_⟩
  fin_cases i
  · show (φ (ζ 0) : ℂ) = Complex.exp (((s 3 - 2 * π : ℝ) : ℂ) * I)
    have := hse 3
    have e : (((s 3 - 2 * π : ℝ) : ℂ) * I) = (s 3 : ℂ) * I + (-1 : ℤ) * (2 * π * I) := by push_cast; ring
    rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, ← this]
    rfl
  · exact hse 0
  · exact hse 1
  · exact hse 2

/-- The exponentials of the entries of a quadruple in a window of length `2π` are distinct. -/
theorem s24q_nb_zeta_inj {ζ : Fin 4 → Circle} {t : Fin 4 → ℝ} (ht : StrictMono t) (ht4 : t 3 < t 0 + 2 * π)
    (hζ : ∀ i, (ζ i : ℂ) = Complex.exp (t i * I)) {i j : Fin 4} (h : ζ i = ζ j) : i = j := by
  have hπ := Real.pi_pos
  have hmono : ∀ k : Fin 4, t 0 ≤ t k ∧ t k ≤ t 3 := fun k =>
    ⟨ht.monotone (by fin_cases k <;> decide), ht.monotone (by fin_cases k <;> decide)⟩
  have hexp : Complex.exp (t i * I) = Complex.exp (t j * I) := by rw [← hζ i, ← hζ j, h]
  obtain ⟨m, hm⟩ := CircleLift.sub_eq_int_mul_two_pi hexp
  have hi := hmono i
  have hj := hmono j
  have h1 : (m : ℝ) < 1 := by by_contra hc; push_neg at hc; nlinarith
  have h2 : (-1 : ℝ) < m := by by_contra hc; push_neg at hc; nlinarith
  have h3 : m < 1 := by exact_mod_cast h1
  have h4 : -1 < m := by exact_mod_cast h2
  have : m = 0 := by omega
  rw [this] at hm
  have : t i = t j := by simpa using hm
  exact ht.injective this

/-- If cyclic order is preserved for quadruples avoiding `1`, it is preserved when the last point is `1`
(limit of quadruples whose last point tends to `1` from below). -/
theorem s24q_nb_cyclic_last {φ : Circle → Circle} (hφ : Function.Bijective φ) (hφc : Continuous φ)
    (havoid : ∀ (ζ : Fin 4 → Circle) (t : Fin 4 → ℝ), StrictMono t → t 3 < t 0 + 2 * π →
      (∀ i, (ζ i : ℂ) = Complex.exp (t i * I)) → (∀ i, (ζ i : ℂ) ≠ 1) →
        ∃ s : Fin 4 → ℝ, StrictMono s ∧ s 3 < s 0 + 2 * π ∧ ∀ i, (φ (ζ i) : ℂ) = Complex.exp (s i * I))
    {ζ : Fin 4 → Circle} {t : Fin 4 → ℝ} (ht : StrictMono t) (ht4 : t 3 < t 0 + 2 * π)
    (hζ : ∀ i, (ζ i : ℂ) = Complex.exp (t i * I)) (h3 : (ζ 3 : ℂ) = 1) :
    ∃ s : Fin 4 → ℝ, StrictMono s ∧ s 3 < s 0 + 2 * π ∧ ∀ i, (φ (ζ i) : ℂ) = Complex.exp (s i * I) := by
  classical
  have hπ := Real.pi_pos
  have t01 : t 0 < t 1 := ht (by decide)
  have t12 : t 1 < t 2 := ht (by decide)
  have t23 : t 2 < t 3 := ht (by decide)
  have hne : ∀ i : Fin 4, i ≠ 3 → (ζ i : ℂ) ≠ 1 := fun i hi h =>
    hi (s24q_nb_zeta_inj ht ht4 hζ (Circle.ext (h.trans h3.symm)))
  have hE3 : Complex.exp (t 3 * I) = 1 := by rw [← hζ 3, h3]
  set ε : ℝ := min (t 3 - t 2) π with hε
  have hε0 : 0 < ε := lt_min (by linarith) hπ
  have hεt : ε ≤ t 3 - t 2 := min_le_left _ _
  have hεπ : ε ≤ π := min_le_right _ _
  set δ : ℕ → ℝ := fun n => ε / ((n : ℝ) + 2) with hδ
  have hδ0 : ∀ n, 0 < δ n := fun n => div_pos hε0 (by positivity)
  have hδε : ∀ n, δ n < ε := fun n =>
    div_lt_self hε0 (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  set tn : ℕ → Fin 4 → ℝ := fun n i => if i = 3 then t 3 - δ n else t i with htn
  set ζn : ℕ → Fin 4 → Circle := fun n i => if i = 3 then Circle.exp (t 3 - δ n) else ζ i with hζn
  have tn0 : ∀ n, tn n 0 = t 0 := fun n => by simp [htn]
  have tn1 : ∀ n, tn n 1 = t 1 := fun n => by simp [htn]
  have tn2 : ∀ n, tn n 2 = t 2 := fun n => by simp [htn]
  have tn3 : ∀ n, tn n 3 = t 3 - δ n := fun n => by simp [htn]
  have ζn3 : ∀ n, ζn n 3 = Circle.exp (t 3 - δ n) := fun n => by simp [hζn]
  have ζn_ne : ∀ n i, i ≠ 3 → ζn n i = ζ i := fun n i hi => by simp [hζn, hi]
  have hexpne : ∀ n, Complex.exp (((t 3 - δ n : ℝ) : ℂ) * I) ≠ 1 := fun n h => by
    have e : Complex.exp (((t 3 - δ n : ℝ) : ℂ) * I) * Complex.exp ((δ n : ℂ) * I) = 1 := by
      rw [← Complex.exp_add]
      have : ((t 3 - δ n : ℝ) : ℂ) * I + (δ n : ℂ) * I = (t 3 : ℂ) * I := by push_cast; ring
      rw [this, hE3]
    rw [h, one_mul] at e
    exact s24q_nb_exp_ne_one (hδ0 n) (by linarith [hδε n]) e
  have hyp : ∀ n, StrictMono (tn n) ∧ tn n 3 < tn n 0 + 2 * π ∧
      (∀ i, ((ζn n i : Circle) : ℂ) = Complex.exp (tn n i * I)) ∧ ∀ i, ((ζn n i : Circle) : ℂ) ≠ 1 := by
    intro n
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine s24q_nb_strictMono4 ?_ ?_ ?_
      · rw [tn0, tn1]; exact t01
      · rw [tn1, tn2]; exact t12
      · rw [tn2, tn3]; linarith [hδε n]
    · rw [tn3, tn0]; linarith [hδ0 n]
    · intro i
      by_cases hi : i = 3
      · subst hi; rw [ζn3, tn3, Circle.coe_exp]
      · rw [ζn_ne n i hi, hζ i]; congr 2; simp [htn, hi]
    · intro i
      by_cases hi : i = 3
      · subst hi; rw [ζn3, Circle.coe_exp]; exact hexpne n
      · rw [ζn_ne n i hi]; exact hne i hi
  choose s hs hs3 hse using fun n => havoid (ζn n) (tn n) (hyp n).1 (hyp n).2.1 (hyp n).2.2.1 (hyp n).2.2.2
  have hse' : ∀ n i, i ≠ 3 → (φ (ζ i) : ℂ) = Complex.exp (s n i * I) := fun n i hi => by
    rw [← ζn_ne n i hi]; exact hse n i
  have hφne : ∀ i, (φ (ζ i) : ℂ) ≠ 0 := fun i h => by
    have := Circle.norm_coe (φ (ζ i)); rw [h, norm_zero] at this; exact zero_ne_one this
  have hs01 : ∀ n, s n 0 < s n 1 := fun n => hs n (by decide)
  have hs12 : ∀ n, s n 1 < s n 2 := fun n => hs n (by decide)
  have hs23 : ∀ n, s n 2 < s n 3 := fun n => hs n (by decide)
  -- the differences are independent of `n`
  have hdiff : ∀ n m, ∀ i j : Fin 4, i ≠ 3 → j ≠ 3 → s n i < s n j → s n j < s n i + 2 * π →
      s m i < s m j → s m j < s m i + 2 * π → s n j - s n i = s m j - s m i := by
    intro n m i j hi hj h1 h2 h3' h4
    refine s24q_nb_window_unique (by linarith) (by linarith) (by linarith) (by linarith) ?_
    have e1 : Complex.exp (((s n j - s n i : ℝ) : ℂ) * I) = Complex.exp ((s n j : ℂ) * I) / Complex.exp ((s n i : ℂ) * I) := by
      rw [← Complex.exp_sub]; congr 1; push_cast; ring
    have e2 : Complex.exp (((s m j - s m i : ℝ) : ℂ) * I) = Complex.exp ((s m j : ℂ) * I) / Complex.exp ((s m i : ℂ) * I) := by
      rw [← Complex.exp_sub]; congr 1; push_cast; ring
    rw [e1, e2, ← hse' n i hi, ← hse' n j hj, ← hse' m i hi, ← hse' m j hj]
  have hd1 : ∀ n, s n 1 - s n 0 = s 0 1 - s 0 0 := fun n =>
    hdiff n 0 0 1 (by decide) (by decide) (hs01 n) (by linarith [hs3 n, hs23 n, hs12 n]) (hs01 0)
      (by linarith [hs3 0, hs23 0, hs12 0])
  have hd2 : ∀ n, s n 2 - s n 0 = s 0 2 - s 0 0 := fun n =>
    hdiff n 0 0 2 (by decide) (by decide) (by linarith [hs01 n, hs12 n]) (by linarith [hs3 n, hs23 n])
      (by linarith [hs01 0, hs12 0]) (by linarith [hs3 0, hs23 0])
  set δ1 := s 0 1 - s 0 0 with hδ1
  set δ2 := s 0 2 - s 0 0 with hδ2
  have hδ12 : δ1 < δ2 := by rw [hδ1, hδ2]; linarith [hs12 0]
  have hδ1pos : 0 < δ1 := by rw [hδ1]; linarith [hs01 0]
  set w : ℕ → ℝ := fun n => s n 3 - s n 0 with hw
  have hwlo : ∀ n, δ2 < w n := fun n => by
    show δ2 < s n 3 - s n 0
    rw [← hd2 n]; linarith [hs23 n]
  have hwhi : ∀ n, w n < 2 * π := fun n => by
    show s n 3 - s n 0 < 2 * π
    linarith [hs3 n]
  -- limit
  have hv : ∀ n, Complex.exp ((w n : ℂ) * I) = (φ (ζn n 3) : ℂ) / (φ (ζ 0) : ℂ) := fun n => by
    have e : Complex.exp ((w n : ℂ) * I) = Complex.exp ((s n 3 : ℂ) * I) / Complex.exp ((s n 0 : ℂ) * I) := by
      rw [← Complex.exp_sub]; congr 1; simp only [hw]; push_cast; ring
    rw [e, ← hse n 3, hse' n 0 (by decide)]
  have hlimζ : Tendsto (fun n => (φ (ζn n 3) : ℂ) / (φ (ζ 0) : ℂ)) atTop
      (𝓝 ((φ (ζ 3) : ℂ) / (φ (ζ 0) : ℂ))) := by
    have hc : Tendsto (fun n => ζn n 3) atTop (𝓝 (ζ 3)) := by
      have h1 : Tendsto (fun n => Circle.exp (t 3 - δ n)) atTop (𝓝 (Circle.exp (t 3 - 0))) :=
        ((Circle.exp.continuous.tendsto _).comp (tendsto_const_nhds.sub hδlim))
      have h2 : Circle.exp (t 3 - 0) = ζ 3 := by
        apply Circle.ext; rw [Circle.coe_exp, hζ 3, sub_zero]
      rw [h2] at h1
      exact h1.congr (fun n => (ζn3 n).symm)
    have hc2 : Tendsto (fun n => (φ (ζn n 3) : ℂ)) atTop (𝓝 (φ (ζ 3) : ℂ)) :=
      (continuous_subtype_val.tendsto _).comp ((hφc.tendsto _).comp hc)
    exact hc2.div_const _
  set K : Set ℂ := (fun x : ℝ => Complex.exp ((x : ℂ) * I)) '' Icc δ2 (2 * π) with hK
  have hKc : IsClosed K :=
    (isCompact_Icc.image (by fun_prop)).isClosed
  have hvK : (φ (ζ 3) : ℂ) / (φ (ζ 0) : ℂ) ∈ K := by
    refine hKc.mem_of_tendsto hlimζ (Eventually.of_forall fun n => ?_)
    exact ⟨w n, ⟨(hwlo n).le, (hwhi n).le⟩, hv n⟩
  obtain ⟨w₀, ⟨hw₀1, hw₀2⟩, hw₀e'⟩ := hvK
  have hw₀e : Complex.exp ((w₀ : ℂ) * I) = (φ (ζ 3) : ℂ) / (φ (ζ 0) : ℂ) := hw₀e'
  have hexp2 : Complex.exp ((δ2 : ℂ) * I) = (φ (ζ 2) : ℂ) / (φ (ζ 0) : ℂ) := by
    rw [hδ2]
    have e : Complex.exp (((s 0 2 - s 0 0 : ℝ) : ℂ) * I) = Complex.exp ((s 0 2 : ℂ) * I) / Complex.exp ((s 0 0 : ℂ) * I) := by
      rw [← Complex.exp_sub]; congr 1; push_cast; ring
    rw [e, ← hse' 0 2 (by decide), ← hse' 0 0 (by decide)]
  have hw₀ne2 : w₀ ≠ δ2 := fun h => by
    rw [h, hexp2] at hw₀e
    have : (φ (ζ 3) : ℂ) = φ (ζ 2) := by
      exact (div_left_inj' (hφne 0)).1 hw₀e.symm
    have h32 : ζ 3 = ζ 2 := hφ.1 (Circle.ext this)
    exact absurd (s24q_nb_zeta_inj ht ht4 hζ h32) (by decide)
  have hw₀ne1 : w₀ ≠ 2 * π := fun h => by
    rw [h] at hw₀e
    have h1 : Complex.exp (((2 * π : ℝ) : ℂ) * I) = 1 := by
      have : (((2 * π : ℝ) : ℂ) * I) = 2 * π * I := by push_cast; ring
      rw [this]; exact Complex.exp_two_pi_mul_I
    rw [h1] at hw₀e
    have : (φ (ζ 3) : ℂ) = φ (ζ 0) := by
      have := (div_eq_one_iff_eq (hφne 0)).1 hw₀e.symm
      exact this
    have h30 : ζ 3 = ζ 0 := hφ.1 (Circle.ext this)
    exact absurd (s24q_nb_zeta_inj ht ht4 hζ h30) (by decide)
  have hw₀lo : δ2 < w₀ := lt_of_le_of_ne hw₀1 (Ne.symm hw₀ne2)
  have hw₀hi : w₀ < 2 * π := lt_of_le_of_ne hw₀2 hw₀ne1
  refine ⟨![s 0 0, s 0 0 + δ1, s 0 0 + δ2, s 0 0 + w₀], s24q_nb_strictMono4 ?_ ?_ ?_, ?_, fun i => ?_⟩
  · show s 0 0 < s 0 0 + δ1; linarith
  · show s 0 0 + δ1 < s 0 0 + δ2; linarith
  · show s 0 0 + δ2 < s 0 0 + w₀; linarith
  · show s 0 0 + w₀ < s 0 0 + 2 * π; linarith
  · fin_cases i
    · exact hse' 0 0 (by decide)
    · show (φ (ζ 1) : ℂ) = Complex.exp (((s 0 0 + δ1 : ℝ) : ℂ) * I)
      rw [hδ1, show s 0 0 + (s 0 1 - s 0 0) = s 0 1 by ring]
      exact hse' 0 1 (by decide)
    · show (φ (ζ 2) : ℂ) = Complex.exp (((s 0 0 + δ2 : ℝ) : ℂ) * I)
      rw [hδ2, show s 0 0 + (s 0 2 - s 0 0) = s 0 2 by ring]
      exact hse' 0 2 (by decide)
    · show (φ (ζ 3) : ℂ) = Complex.exp (((s 0 0 + w₀ : ℝ) : ℂ) * I)
      have e : Complex.exp (((s 0 0 + w₀ : ℝ) : ℂ) * I) =
          Complex.exp ((s 0 0 : ℂ) * I) * Complex.exp ((w₀ : ℂ) * I) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [e, hw₀e, ← hse' 0 0 (by decide)]
      field_simp [hφne 0]

/-- **Boundary cyclic order.** If `F` has local winding `+1` at a point of `ℍ` and `φ` is its boundary map (a
bijective continuous self-map of the circle with `cayley ∘ F ∘ cayley⁻¹ → φ`), then `φ` preserves the positive
cyclic order of four boundary points. (Via the extension `G` of `F` to the closed half-plane, a real Möbius
normalization fixing `∞`, and `cyclicOrder_preserved_of_isHomeoExtension_of_fixes_infty`.) -/
theorem s24q_nb_cyclic {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {τ₀ : UpperHalfPlane}
    (hw : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        Complex.exp (Lg t) =
          liftToC F ((τ₀ : ℂ) + ρ * Complex.exp (2 * π * Complex.I * t)) - liftToC F (τ₀ : ℂ)) →
        Lg 1 - Lg 0 = 2 * π * Complex.I)
    {φ : Circle → Circle} (hφ : Function.Bijective φ) (hφc : Continuous φ)
    (hlim : ∀ ζ : Circle,
      Tendsto (fun z => cayley (liftToC F (cayleyInv z))) (𝓝[ball 0 1] (ζ : ℂ)) (𝓝 (φ ζ : ℂ)))
    (ζ : Fin 4 → Circle) (t : Fin 4 → ℝ) (ht : StrictMono t) (ht4 : t 3 < t 0 + 2 * π)
    (hζ : ∀ i, (ζ i : ℂ) = Complex.exp (t i * I)) :
    ∃ s : Fin 4 → ℝ, StrictMono s ∧ s 3 < s 0 + 2 * π ∧ ∀ i, (φ (ζ i) : ℂ) = Complex.exp (s i * I) := by
  have havoid : ∀ (ζ : Fin 4 → Circle) (t : Fin 4 → ℝ), StrictMono t → t 3 < t 0 + 2 * π →
      (∀ i, (ζ i : ℂ) = Complex.exp (t i * I)) → (∀ i, (ζ i : ℂ) ≠ 1) →
        ∃ s : Fin 4 → ℝ, StrictMono s ∧ s 3 < s 0 + 2 * π ∧ ∀ i, (φ (ζ i) : ℂ) = Complex.exp (s i * I) :=
    fun ζ t ht ht4 hζ hne => s24q_nb_cyclic_avoid hw hφ hφc hlim ζ t ht ht4 hζ hne
  have P3 : ∀ (ζ : Fin 4 → Circle) (t : Fin 4 → ℝ), StrictMono t → t 3 < t 0 + 2 * π →
      (∀ i, (ζ i : ℂ) = Complex.exp (t i * I)) → (ζ 3 : ℂ) = 1 →
        ∃ s : Fin 4 → ℝ, StrictMono s ∧ s 3 < s 0 + 2 * π ∧ ∀ i, (φ (ζ i) : ℂ) = Complex.exp (s i * I) :=
    fun ζ t ht ht4 hζ h => s24q_nb_cyclic_last hφ hφc havoid ht ht4 hζ h
  have P0 : ∀ (ζ : Fin 4 → Circle) (t : Fin 4 → ℝ), StrictMono t → t 3 < t 0 + 2 * π →
      (∀ i, (ζ i : ℂ) = Complex.exp (t i * I)) → (ζ 0 : ℂ) = 1 →
        ∃ s : Fin 4 → ℝ, StrictMono s ∧ s 3 < s 0 + 2 * π ∧ ∀ i, (φ (ζ i) : ℂ) = Complex.exp (s i * I) := by
    intro ζ t ht ht4 hζ h
    obtain ⟨t', ht', ht4', hζ'⟩ := s24q_nb_rot_H ht ht4 hζ
    refine s24q_nb_rot_R (P3 (fun i => ζ (i + 1)) t' ht' ht4' hζ' ?_)
    have e : (3 : Fin 4) + 1 = 0 := by decide
    show (ζ (3 + 1) : ℂ) = 1
    rw [e]; exact h
  have P1 : ∀ (ζ : Fin 4 → Circle) (t : Fin 4 → ℝ), StrictMono t → t 3 < t 0 + 2 * π →
      (∀ i, (ζ i : ℂ) = Complex.exp (t i * I)) → (ζ 1 : ℂ) = 1 →
        ∃ s : Fin 4 → ℝ, StrictMono s ∧ s 3 < s 0 + 2 * π ∧ ∀ i, (φ (ζ i) : ℂ) = Complex.exp (s i * I) := by
    intro ζ t ht ht4 hζ h
    obtain ⟨t', ht', ht4', hζ'⟩ := s24q_nb_rot_H ht ht4 hζ
    exact s24q_nb_rot_R (P0 (fun i => ζ (i + 1)) t' ht' ht4' hζ' h)
  have P2 : ∀ (ζ : Fin 4 → Circle) (t : Fin 4 → ℝ), StrictMono t → t 3 < t 0 + 2 * π →
      (∀ i, (ζ i : ℂ) = Complex.exp (t i * I)) → (ζ 2 : ℂ) = 1 →
        ∃ s : Fin 4 → ℝ, StrictMono s ∧ s 3 < s 0 + 2 * π ∧ ∀ i, (φ (ζ i) : ℂ) = Complex.exp (s i * I) := by
    intro ζ t ht ht4 hζ h
    obtain ⟨t', ht', ht4', hζ'⟩ := s24q_nb_rot_H ht ht4 hζ
    exact s24q_nb_rot_R (P1 (fun i => ζ (i + 1)) t' ht' ht4' hζ' h)
  by_cases hex : ∃ j, (ζ j : ℂ) = 1
  · obtain ⟨j, hj⟩ := hex
    fin_cases j
    · exact P0 ζ t ht ht4 hζ hj
    · exact P1 ζ t ht ht4 hζ hj
    · exact P2 ζ t ht ht4 hζ hj
    · exact P3 ζ t ht ht4 hζ hj
  · push_neg at hex
    exact havoid ζ t ht ht4 hζ hex

/-- Two consecutive differences of integers separated by a window of length `< 4π` are `1`. -/
theorem s24q_nb_int_step (u v : ℤ) (x : ℝ) (hx : x = ((u : ℝ) - v) * (2 * π)) (h0 : 0 < x)
    (h1 : x < 4 * π) : u - v = 1 := by
  have hπ := Real.pi_pos
  have hpos : (0 : ℝ) < (u : ℝ) - v := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc (by positivity : (0 : ℝ) ≤ 2 * π)]
  have hlt : (u : ℝ) - v < 2 := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ 2 * π)]
  have a : (0 : ℤ) < u - v := by exact_mod_cast hpos
  have b : u - v < 2 := by exact_mod_cast hlt
  omega

/-- **Increasing lift from cyclic order.** A continuous bijection of the circle preserving the positive cyclic order of
quadruples has an increasing lift to `ℝ`. -/
theorem s24q_nb_increasing_of_cyclic {φ : Circle → Circle} (hφ : Function.Bijective φ) (hφc : Continuous φ)
    (hcyc : ∀ (ζ : Fin 4 → Circle) (t : Fin 4 → ℝ), StrictMono t → t 3 < t 0 + 2 * π →
      (∀ i, (ζ i : ℂ) = Complex.exp (t i * I)) →
        ∃ s : Fin 4 → ℝ, StrictMono s ∧ s 3 < s 0 + 2 * π ∧ ∀ i, (φ (ζ i) : ℂ) = Complex.exp (s i * I)) :
    HasIncreasingLift φ := by
  obtain ⟨h, hmon, hcoe⟩ := CircleLift.exists_strictMono_lift φ hφ hφc
  rcases hmon with ⟨hm, hp⟩ | ⟨ha, hp⟩
  · exact ⟨h, hm, hp, hcoe⟩
  exfalso
  have hπ := Real.pi_pos
  set t : Fin 4 → ℝ := fun i => ((i : ℕ) : ℝ) * (π / 2) with htdef
  have ht : StrictMono t := fun i j hij => by
    simp only [htdef]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) (by positivity)
  have ht0 : t 0 = 0 := by simp [htdef]
  have ht1 : t 1 = π / 2 := by simp [htdef]
  have ht2 : t 2 = π := by simp [htdef]; ring
  have ht3 : t 3 = 3 * π / 2 := by simp [htdef]; ring
  have ht4 : t 3 < t 0 + 2 * π := by rw [ht3, ht0]; linarith
  obtain ⟨s, hs, hs3, hse⟩ := hcyc (fun i => Circle.exp (t i)) t ht ht4 (fun i => Circle.coe_exp _)
  have hn : ∀ i, ∃ n : ℤ, s i = h (t i) + n * (2 * π) := fun i => by
    refine CircleLift.sub_eq_int_mul_two_pi ?_
    rw [← hse i, hcoe (t i)]
  choose n hn using hn
  have s01 : s 0 < s 1 := hs (by decide)
  have s12 : s 1 < s 2 := hs (by decide)
  have s23 : s 2 < s 3 := hs (by decide)
  have h01 : h (t 1) < h (t 0) := ha (ht (by decide))
  have h12 : h (t 2) < h (t 1) := ha (ht (by decide))
  have h23 : h (t 3) < h (t 2) := ha (ht (by decide))
  have h30 : h (t 0) - 2 * π < h (t 3) := by
    have := ha ht4
    rw [hp] at this
    linarith
  have e1 := s24q_nb_int_step (n 1) (n 0) (s 1 - s 0 - (h (t 1) - h (t 0)))
    (by rw [hn 1, hn 0]; ring) (by linarith) (by linarith)
  have e2 := s24q_nb_int_step (n 2) (n 1) (s 2 - s 1 - (h (t 2) - h (t 1)))
    (by rw [hn 2, hn 1]; ring) (by linarith) (by linarith)
  have e3 := s24q_nb_int_step (n 3) (n 2) (s 3 - s 2 - (h (t 3) - h (t 2)))
    (by rw [hn 3, hn 2]; ring) (by linarith) (by linarith)
  have e4 : (n 3 : ℝ) - n 0 = 3 := by
    have : n 3 - n 0 = 3 := by omega
    exact_mod_cast this
  have : s 3 - s 0 - (h (t 3) - h (t 0)) = ((n 3 : ℝ) - n 0) * (2 * π) := by
    rw [hn 3, hn 0]; ring
  rw [e4] at this
  linarith

/-- **Orientation bridge (boundary, amended).** If `F` has local winding `+1` at every point of `ℍ`, its boundary
map has an increasing lift. -/
theorem s24q_nb_increasing {F : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hw : ∀ τ : UpperHalfPlane, ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ,
      ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        Complex.exp (Lg t) = liftToC F ((τ : ℂ) + ρ * Complex.exp (2 * π * Complex.I * t)) - liftToC F (τ : ℂ)) →
        Lg 1 - Lg 0 = 2 * π * Complex.I)
    {φ : Circle → Circle} (hφ : Function.Bijective φ) (hφc : Continuous φ)
    (hlim : ∀ ζ : Circle,
      Tendsto (fun z => cayley (liftToC F (cayleyInv z))) (𝓝[ball 0 1] (ζ : ℂ)) (𝓝 (φ ζ : ℂ))) :
    HasIncreasingLift φ := by
  exact s24q_nb_increasing_of_cyclic hφ hφc fun ζ t ht ht4 hζ =>
    s24q_nb_cyclic (hw UpperHalfPlane.I) hφ hφc hlim ζ t ht ht4 hζ

/-- **Nielsen boundary map.** The lift `F` of an orientation preserving homeomorphism between compact surfaces
uniformized by Fuchsian groups has a boundary map on the circle (Cayley) which is a homeomorphism with an increasing
lift and intertwines the Cayley conjugates of `γ` and `δ` whenever `F ∘ γ = δ ∘ F`. -/
theorem s24q_boundary [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] [CompactSpace S₁]
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀} {p₁ : UpperHalfPlane → S₁}
    (hΓ₀ : IsFuchsian Γ₀) (hfree₀ : ActsFreely Γ₀) (hp₀ : IsUniformization Γ₀ p₀)
    (hΓ₁ : IsFuchsian Γ₁) (hfree₁ : ActsFreely Γ₁) (hp₁ : IsUniformization Γ₁ p₁)
    {f : S₀ ≃ₜ S₁} (hf : ∀ x : S₀, IsSensePreserving (localMapExpr f x) (localMapDomain f x))
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₀ p₁ f F) :
    ∃ φ : Circle → Circle, Function.Bijective φ ∧ Continuous φ ∧ HasIncreasingLift φ ∧
      ∀ γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ ∈ Γ₀ → (∀ τ, F (γ • τ) = δ • F τ) →
        ∀ ζ ζ' : Circle,
          (ζ' : ℂ) = ((((γ 0 0 + γ 1 1 : ℝ) : ℂ) + ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I) * ζ +
              (((γ 0 0 - γ 1 1 : ℝ) : ℂ) - ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I)) /
            ((((γ 0 0 - γ 1 1 : ℝ) : ℂ) + ((γ 0 1 + γ 1 0 : ℝ) : ℂ) * I) * ζ +
              (((γ 0 0 + γ 1 1 : ℝ) : ℂ) - ((γ 0 1 - γ 1 0 : ℝ) : ℂ) * I)) →
          (φ ζ' : ℂ) = ((((δ 0 0 + δ 1 1 : ℝ) : ℂ) + ((δ 0 1 - δ 1 0 : ℝ) : ℂ) * I) * (φ ζ) +
              (((δ 0 0 - δ 1 1 : ℝ) : ℂ) - ((δ 0 1 + δ 1 0 : ℝ) : ℂ) * I)) /
            ((((δ 0 0 - δ 1 1 : ℝ) : ℂ) + ((δ 0 1 + δ 1 0 : ℝ) : ℂ) * I) * (φ ζ) +
              (((δ 0 0 + δ 1 1 : ℝ) : ℂ) - ((δ 0 1 - δ 1 0 : ℝ) : ℂ) * I)) := by
  obtain ⟨φ, hφ, hφc, hlim, heq⟩ := s24q_nb_extension hΓ₀ hfree₀ hp₀ hΓ₁ hfree₁ hp₁ hF
  exact ⟨φ, hφ, hφc, s24q_nb_increasing (fun τ => s24q_nb_lift_localWinding hp₀ hp₁ hf hF τ) hφ hφc hlim, heq⟩

end LiZhongQC
