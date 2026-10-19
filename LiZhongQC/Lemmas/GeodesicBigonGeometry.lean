import LiZhongQC.Lemmas.GeodesicInteriorCorners
import LiZhongQC.Lemmas.GeodesicExceptionalJoins
import LiZhongQC.Lemmas.GeodesicBigonCompletion
import LiZhongQC.Lemmas.GeodesicActualPartition
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real
noncomputable section
namespace LiZhongQC

/-- The actual interior-corner producer applied to two consecutive Side
records. Its conclusion is independent of a surrounding cyclic index set. -/
theorem s25bg_side_pair_bounds {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {a t₀ b : ℝ} (ha : 0 ≤ a) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hb : b ≤ 1)
    (L : s25cv_Side φ γ.toFun a t₀) (R : s25cv_Side φ γ.toFun t₀ b) :
    ∃ k : ℕ, meromorphicOrderAt φ (R.side 0) = (k : ℤ) ∧
      2 * Real.pi / ((k : ℝ) + 2) ≤
        |arg (-derivWithin L.side (Icc 0 1) 1 / derivWithin R.side (Icc 0 1) 0)| ∧
      2 * Real.pi / ((k : ℝ) + 2) ≤ 2 * Real.pi -
        |arg (-derivWithin L.side (Icc 0 1) 1 / derivWithin R.side (Icc 0 1) 0)| := by
  let C : Fin 2 → ℝ → ℂ := ![L.side, R.side]
  have h := s25ic_actual_interior_corner hφ hne hγ hp (side := C) (j := 1)
    ha ht₀ hb L.smooth R.smooth L.mono R.mono L.bij R.bij L.last R.first L.trace R.trace
    (L.regular 1 ⟨zero_le_one, le_rfl⟩) (R.regular 0 ⟨le_rfl, zero_le_one⟩)
  simpa [C] using s25bg_blunt_absolute h.1

/-- Two finite-cover side records meeting at selected endpoints have no
cusp when their open traces are disjoint. Endpoint 0 uses the original side;
endpoint 1 uses its reversal. This matches all four bigon seam orientations. -/
theorem s25bg_side_endpoint_no_cusp {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ₁ γ₂ : LRCurve} (hγ₁ : IsPhiGeodesic φ unitDisc γ₁)
    (hγ₂ : IsPhiGeodesic φ unitDisc γ₂)
    (hp₁ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₁.toFun u ≠ γ₁.toFun s)
    (hp₂ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₂.toFun u ≠ γ₂.toFun s)
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hc : 0 ≤ c) (hd : d ≤ 1)
    (S : s25cv_Side φ γ₁.toFun a b) (T : s25cv_Side φ γ₂.toFun c d)
    {x y : ℝ} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1)
    (hpoint : S.side x = T.side y)
    (hdisj : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Ioo (0 : ℝ) 1, S.side s ≠ T.side t) :
    arg ((((1 - 2 * x : ℝ) : ℂ) * derivWithin S.side (Icc 0 1) x) /
      (((1 - 2 * y : ℝ) : ℂ) * derivWithin T.side (Icc 0 1) y)) ≠ 0 := by
  have hxI : x ∈ Icc (0 : ℝ) 1 := by rcases hx with rfl | rfl <;> constructor <;> norm_num
  have hyI : y ∈ Icc (0 : ℝ) 1 := by rcases hy with rfl | rfl <;> constructor <;> norm_num
  have hxne : (1 - 2 * x : ℝ) ≠ 0 := by rcases hx with rfl | rfl <;> norm_num
  have hyne : (1 - 2 * y : ℝ) ≠ 0 := by rcases hy with rfl | rfl <;> norm_num
  have hmaps : ∀ t ∈ Icc (0 : ℝ) 1, x + (1 - 2 * x) * t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    rcases hx with rfl | rfl <;> constructor <;> nlinarith [ht.1, ht.2]
  have hmapt : ∀ t ∈ Icc (0 : ℝ) 1, y + (1 - 2 * y) * t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    rcases hy with rfl | rfl <;> constructor <;> nlinarith [ht.1, ht.2]
  have hopenS : ∀ t ∈ Ioo (0 : ℝ) 1, x + (1 - 2 * x) * t ∈ Ioo (0 : ℝ) 1 := by
    intro t ht
    rcases hx with rfl | rfl <;> constructor <;> nlinarith [ht.1, ht.2]
  have hopenT : ∀ t ∈ Ioo (0 : ℝ) 1, y + (1 - 2 * y) * t ∈ Ioo (0 : ℝ) 1 := by
    intro t ht
    rcases hy with rfl | rfl <;> constructor <;> nlinarith [ht.1, ht.2]
  let F : ℝ → ℂ := fun t => S.side (x + (1 - 2 * x) * t)
  let G : ℝ → ℂ := fun t => T.side (y + (1 - 2 * y) * t)
  let pF : ℝ → ℝ := fun t => S.par (x + (1 - 2 * x) * t)
  let pG : ℝ → ℝ := fun t => T.par (y + (1 - 2 * y) * t)
  have hiS : MapsTo S.par (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ⟨ha.trans (S.bij.1 ht).1, (S.bij.1 ht).2.trans hb⟩
  have hiT : MapsTo T.par (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact ⟨hc.trans (T.bij.1 ht).1, (T.bij.1 ht).2.trans hd⟩
  have hmF : StrictMonoOn pF (Icc (0 : ℝ) 1) ∨ StrictAntiOn pF (Icc (0 : ℝ) 1) := by
    rcases hx with rfl | rfl
    · left
      simpa [pF] using S.mono
    · right
      intro s hs t ht hst
      exact S.mono (hmaps t ht) (hmaps s hs) (by linarith)
  have hmG : StrictMonoOn pG (Icc (0 : ℝ) 1) ∨ StrictAntiOn pG (Icc (0 : ℝ) 1) := by
    rcases hy with rfl | rfl
    · left
      simpa [pG] using T.mono
    · right
      intro s hs t ht hst
      exact T.mono (hmapt t ht) (hmapt s hs) (by linarith)
  have hFd : derivWithin F (Icc 0 1) 0 =
      ((1 - 2 * x : ℝ) : ℂ) * derivWithin S.side (Icc 0 1) x := by
    simpa only [mul_zero, add_zero] using fx_p2_derivWithin_affine
      (fx_p2_hasDerivWithinAt_of_contDiffOn S.smooth) zero_lt_one hmaps
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
  have hGd : derivWithin G (Icc 0 1) 0 =
      ((1 - 2 * y : ℝ) : ℂ) * derivWithin T.side (Icc 0 1) y := by
    simpa only [mul_zero, add_zero] using fx_p2_derivWithin_affine
      (fx_p2_hasDerivWithinAt_of_contDiffOn T.smooth) zero_lt_one hmapt
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl, zero_le_one⟩)
  have hpoint' : γ₁.toFun (S.par x) = γ₂.toFun (T.par y) :=
    (S.trace x hxI).symm.trans (hpoint.trans (T.trace y hyI))
  have hno := s25gb_actual_exceptional_join hφ hne hγ₁ hγ₂ hp₁ hp₂
    (hiS hxI) (hiT hyI) hpoint'
    (fx_p2_contDiffOn_affine S.smooth hmaps) (fx_p2_contDiffOn_affine T.smooth hmapt)
    ((s25cv_par_continuous S.mono S.bij).comp (by fun_prop) hmaps)
    ((s25cv_par_continuous T.mono T.bij).comp (by fun_prop) hmapt)
    hmF hmG (fun t ht => hiS (hmaps t ht)) (fun t ht => hiT (hmapt t ht))
    (by simp [pF]) (by simp [pG])
    (fun t ht => S.trace _ (hmaps t ht)) (fun t ht => T.trace _ (hmapt t ht))
    (show derivWithin F (Icc 0 1) 0 ≠ 0 by
      rw [hFd]; exact mul_ne_zero (Complex.ofReal_ne_zero.2 hxne) (S.regular x hxI))
    (show derivWithin G (Icc 0 1) 0 ≠ 0 by
      rw [hGd]; exact mul_ne_zero (Complex.ofReal_ne_zero.2 hyne) (T.regular y hyI))
    (fun s hs t ht => hdisj _ (hopenS s hs) _ (hopenT t ht))
  change arg (derivWithin F (Icc 0 1) 0 / derivWithin G (Icc 0 1) 0) ≠ 0 at hno
  rw [hFd, hGd] at hno
  exact hno

end LiZhongQC



