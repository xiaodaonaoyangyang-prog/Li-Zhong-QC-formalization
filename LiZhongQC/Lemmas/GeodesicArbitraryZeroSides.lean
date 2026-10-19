import LiZhongQC.Lemmas.GeodesicActualZeroSides
import LiZhongQC.Lemmas.GeodesicRegularJoins
import LiZhongQC.Lemmas.GeodesicParameterContinuity
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- Independent positive changes of speed preserve the signed physical
corner angle, not just its absolute value. -/
theorem s25ep_corner_positive_rescale {df dg : ℂ} {e k : ℝ}
    (he : 0 < e) (hk : 0 < k) (hdg : dg ≠ 0) :
    arg (-((e : ℂ) * df) / ((k : ℂ) * dg)) = arg (-df / dg) := by
  have hrat : -((e : ℂ) * df) / ((k : ℂ) * dg) =
      ((e / k : ℝ) : ℂ) * (-df / dg) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.2 hk.ne', hdg]
    <;> ring
  rw [hrat, Complex.arg_real_mul _ (div_pos he hk)]

/-- Two arbitrary regular adjacent sides representing one original
geodesic at an interior zero form a blunt non-cuspidal corner. Their whole
traces need not lie in a zero-chart window. Time-map continuity is derived
from the actual strict-monotone bijections, not assumed. -/
theorem s25ep_arbitrary_zero_join {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hpause : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hz : φ (γ.toFun t₀) = 0)
    {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ} (j : Fin n)
    {p q : ℝ → ℝ} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 (side (j - 1)) (Icc 0 1)) (hg : ContDiffOn ℝ 1 (side j) (Icc 0 1))
    (hp : StrictMonoOn p (Icc (0 : ℝ) 1)) (hq : StrictMonoOn q (Icc (0 : ℝ) 1))
    (hpb : BijOn p (Icc (0 : ℝ) 1) (Icc a t₀)) (hqb : BijOn q (Icc (0 : ℝ) 1) (Icc t₀ b))
    (hp1 : p 1 = t₀) (hq0 : q 0 = t₀)
    (hfeq : ∀ x ∈ Icc (0 : ℝ) 1, side (j - 1) x = γ.toFun (p x))
    (hgeq : ∀ x ∈ Icc (0 : ℝ) 1, side j x = γ.toFun (q x))
    (hfn : derivWithin (side (j - 1)) (Icc 0 1) 1 ≠ 0)
    (hgn : derivWithin (side j) (Icc 0 1) 0 ≠ 0) :
    (∃ m : ℕ, 1 ≤ m ∧ meromorphicOrderAt φ (side j 0) = (m : ℤ)) ∧
      fx_IsBlunt φ side j ∧
      arg (-derivWithin (side (j - 1)) (Icc 0 1) 1 / derivWithin (side j) (Icc 0 1) 0) ≠ 0 := by
  have hpc := s25cv_par_continuous hp hpb
  have hqc := s25cv_par_continuous hq hqb
  obtain ⟨δ, hδ, m, hm, hord, hwindow⟩ := s25ep_actual_zero_blunt_window hφ hne hγ hpause ht₀ hz
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨e, he, he1, hem, hen⟩ := s25gb_parameter_shrink hpc h1 hδ
  obtain ⟨k, hk, hk1, hkm, hkn⟩ := s25gb_parameter_shrink hqc h0 hδ
  let A : ℝ → ℝ := fun x => (1 - e) * 1 + e * x
  let B : ℝ → ℝ := fun x => (1 - k) * 0 + k * x
  let P : ℝ → ℝ := fun x => p (A x)
  let Q : ℝ → ℝ := fun x => q (B x)
  let F : ℝ → ℂ := fun x => side (j - 1) (A x)
  let G : ℝ → ℂ := fun x => side j (B x)
  have hA1 : A 1 = 1 := by dsimp only [A]; ring
  have hB0 : B 0 = 0 := by dsimp only [B]; ring
  have hP1 : P 1 = t₀ := by change p (A 1) = t₀; rw [hA1, hp1]
  have hQ0 : Q 0 = t₀ := by change q (B 0) = t₀; rw [hB0, hq0]
  have hPm : StrictMonoOn P (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    apply hp (hem x hx) (hem y hy)
    linarith [mul_lt_mul_of_pos_left hxy he]
  have hQm : StrictMonoOn Q (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    apply hq (hkm x hx) (hkm y hy)
    linarith [mul_lt_mul_of_pos_left hxy hk]
  have hs : P 0 ∈ Ioo (t₀ - δ) t₀ := by
    have hn := hen 0 h0
    rw [hp1, abs_lt] at hn
    have hm' := hPm h0 h1 zero_lt_one
    rw [hP1] at hm'
    exact ⟨by change t₀ - δ < p (A 0); dsimp only [A]; linarith [hn.1], hm'⟩
  have ht : Q 1 ∈ Ioo t₀ (t₀ + δ) := by
    have hn := hkn 1 h1
    rw [hq0, abs_lt] at hn
    have hm' := hQm h0 h1 zero_lt_one
    rw [hQ0] at hm'
    exact ⟨hm', by change q (B 1) < t₀ + δ; dsimp only [B]; linarith [hn.2]⟩
  have hPi : MapsTo P (Icc (0 : ℝ) 1) (Icc (P 0) t₀) := by
    intro x hx
    exact ⟨hPm.monotoneOn h0 hx hx.1, by simpa only [hP1] using hPm.monotoneOn hx h1 hx.2⟩
  have hQi : MapsTo Q (Icc (0 : ℝ) 1) (Icc t₀ (Q 1)) := by
    intro x hx
    exact ⟨by simpa only [hQ0] using hQm.monotoneOn h0 hx hx.1, hQm.monotoneOn hx h1 hx.2⟩
  have hF : ContDiffOn ℝ 1 F (Icc 0 1) := fx_p2_contDiffOn_affine hf hem
  have hG : ContDiffOn ℝ 1 G (Icc 0 1) := fx_p2_contDiffOn_affine hg hkm
  have hFd : derivWithin F (Icc 0 1) 1 = (e : ℂ) * derivWithin (side (j - 1)) (Icc 0 1) 1 := by
    simpa only [show (1 - e) * 1 + e * 1 = 1 by ring] using
      fx_p2_derivWithin_affine (fx_p2_hasDerivWithinAt_of_contDiffOn hf) zero_lt_one hem h1
  have hGd : derivWithin G (Icc 0 1) 0 = (k : ℂ) * derivWithin (side j) (Icc 0 1) 0 := by
    simpa only [show (1 - k) * 0 + k * 0 = 0 by ring] using
      fx_p2_derivWithin_affine (fx_p2_hasDerivWithinAt_of_contDiffOn hg) zero_lt_one hkm h0
  have hFn : derivWithin F (Icc 0 1) 1 ≠ 0 := by
    rw [hFd]
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 he.ne') hfn
  have hGn : derivWithin G (Icc 0 1) 0 ≠ 0 := by
    rw [hGd]
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 hk.ne') hgn
  -- A temporary two-side family avoids aliasing when the original n is one.
  let T : Fin 2 → ℝ → ℂ := fun i => if i = 0 then F else G
  have hT0 : T 0 = F := by simp only [T, if_pos rfl]
  have hT1 : T 1 = G := by norm_num [T]
  have hprev : (1 : Fin 2) - 1 = 0 := rfl
  have hTeqF : ∀ x ∈ Icc (0 : ℝ) 1, T ((1 : Fin 2) - 1) x = γ.toFun (P x) := by
    intro x hx
    rw [hprev, hT0]
    exact hfeq _ (hem x hx)
  have hTeqG : ∀ x ∈ Icc (0 : ℝ) 1, T 1 x = γ.toFun (Q x) := by
    intro x hx
    rw [hT1]
    exact hgeq _ (hkm x hx)
  obtain ⟨hblunt, hnc⟩ := hwindow (P 0) hs (Q 1) ht 2 T 1 P Q
    (by simpa only [hprev, hT0] using hF) (by simpa only [hT1] using hG)
    hPm hQm hPi hQi hP1 hQ0 hTeqF hTeqG
    (by simpa only [hprev, hT0] using hFn) (by simpa only [hT1] using hGn)
  have harg : arg (-derivWithin (T ((1 : Fin 2) - 1)) (Icc 0 1) 1 /
      derivWithin (T 1) (Icc 0 1) 0) =
      arg (-derivWithin (side (j - 1)) (Icc 0 1) 1 / derivWithin (side j) (Icc 0 1) 0) := by
    rw [hprev, hT0, hT1, hFd, hGd]
    exact s25ep_corner_positive_rescale he hk hgn
  have hangle : fx_chainAngle T 1 = fx_chainAngle side j := by
    unfold fx_chainAngle
    rw [harg]
  have hstart : T 1 0 = side j 0 := by
    rw [hT1]
    change side j (B 0) = side j 0
    rw [hB0]
  have hjoin : side j 0 = γ.toFun t₀ := by rw [hgeq 0 h0, hq0]
  refine ⟨⟨m, hm, by rwa [hjoin]⟩, ?_, ?_⟩
  · obtain ⟨m', hm', hlo, hhi⟩ := hblunt
    exact ⟨m', by simpa only [hstart] using hm', by simpa only [hangle] using hlo,
      by simpa only [hangle] using hhi⟩
  · rwa [harg] at hnc

end LiZhongQC

