import Jacobians.ResidueTheorem.ResidueStokesCoverPoU
import Jacobians.PlanarStokes.PlanarCompactSupportStokes

open Complex Set Filter Topology MeasureTheory
open scoped Real Manifold ContDiff Classical
open Jacobians.Montel Jacobians.Dolbeault Jacobians.Dolbeault.StokesResidue

noncomputable section
namespace LiZhongQC

universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S] [CompactSpace S]
  [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]

/-- The chart coefficient of a form multiplied by the existing global finite
partition, extended by zero outside the chart target. The target guard is
essential because a partial chart inverse has arbitrary off-target values. -/
def s22cp_chartPiece (j : Fin ((chartCover : Finset S).card))
    (F : ℂ → ℝ) (z : ℂ) : ℝ :=
  if z ∈ (chartAt ℂ (coverCenter (X := S) j)).target then
    coverPoU (X := S) j ((chartAt ℂ (coverCenter (X := S) j)).symm z) * F z
  else 0

/-- The already constructed PoU has support in the actual chart source. -/
theorem s22cp_support_source (j : Fin ((chartCover : Finset S).card)) :
    tsupport (coverPoU (X := S) j) ⊆ (chartAt ℂ (coverCenter (X := S) j)).source :=
  (coverPoU_tsupport_subset j).trans
    (chartOpen_subset_chartAt_source (coverCenter j) (coverCenter_mem j))

/-- The relevant support image is compact in the plane. This derives compact
support from the compact surface and the existing finite PoU. -/
theorem s22cp_compact_support_image (j : Fin ((chartCover : Finset S).card)) :
    IsCompact ((chartAt ℂ (coverCenter (X := S) j)) ''
      tsupport (coverPoU (X := S) j)) :=
  isCompact_chartImage_of_subset_source (isCompact_tsupport_coverPoU j)
    (s22cp_support_source j)

theorem s22cp_chartPiece_germ (j : Fin ((chartCover : Finset S).card))
    (F : ℂ → ℝ) {z : ℂ}
    (hz : z ∈ (chartAt ℂ (coverCenter (X := S) j)).target) :
    s22cp_chartPiece j F =ᶠ[𝓝 z]
      (fun w => coverPoU (X := S) j
        ((chartAt ℂ (coverCenter (X := S) j)).symm w) * F w) := by
  filter_upwards [(chartAt ℂ (coverCenter (X := S) j)).open_target.mem_nhds hz]
    with w hw
  exact if_pos hw

/-- Off the compact support image the extended coefficient vanishes on a
whole neighborhood, including at the boundary of the chart target. -/
theorem s22cp_chartPiece_zero_germ (j : Fin ((chartCover : Finset S).card))
    (F : ℂ → ℝ) {z : ℂ}
    (hz : z ∉ (chartAt ℂ (coverCenter (X := S) j)) ''
      tsupport (coverPoU (X := S) j)) :
    s22cp_chartPiece j F =ᶠ[𝓝 z] fun _ => 0 := by
  let φ := chartAt ℂ (coverCenter (X := S) j)
  filter_upwards [(s22cp_compact_support_image j).isClosed.isOpen_compl.mem_nhds hz]
    with w hw
  change (if w ∈ φ.target then coverPoU (X := S) j (φ.symm w) * F w else 0) = 0
  by_cases ht : w ∈ φ.target
  · rw [if_pos ht]
    have hn : φ.symm w ∉ tsupport (coverPoU (X := S) j) := by
      intro h
      exact hw ⟨φ.symm w, h, φ.right_inv ht⟩
    rw [image_eq_zero_of_notMem_tsupport hn, zero_mul]
  · rw [if_neg ht]

theorem s22cp_chartPiece_compactSupport
    (j : Fin ((chartCover : Finset S).card)) (F : ℂ → ℝ) :
    HasCompactSupport (s22cp_chartPiece j F) := by
  refine HasCompactSupport.intro (s22cp_compact_support_image j) ?_
  intro z hz
  exact (s22cp_chartPiece_zero_germ j F hz).self_of_nhds

/-- Every global PoU weight is real-smooth when read in ANY chart, not just
its own support chart. This is the coordinate form used for cancellation. -/
theorem s22cp_weight_contDiffAt
    (j : Fin ((chartCover : Finset S).card)) (y : S) {z : ℂ}
    (hz : z ∈ (chartAt ℂ y).target) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => coverPoU (X := S) j ((chartAt ℂ y).symm w)) z := by
  have hs : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (chartAt ℂ y).symm z :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞))
      (x := y) z hz).contMDiffAt ((chartAt ℂ y).open_target.mem_nhds hz)
  exact contMDiffAt_iff_contDiffAt.mp
    ((contMDiff_coverPoU j).contMDiffAt.comp z hs)

/-- A C1 local coefficient becomes a global C1 compactly supported plane
coefficient after multiplying by the subordinate PoU and extending by zero. -/
theorem s22cp_chartPiece_contDiff
    (j : Fin ((chartCover : Finset S).card)) {F : ℂ → ℝ}
    (hF : ContDiffOn ℝ 1 F (chartAt ℂ (coverCenter (X := S) j)).target) :
    ContDiff ℝ 1 (s22cp_chartPiece j F) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ (chartAt ℂ (coverCenter (X := S) j)).target
  · have hm := ((s22cp_weight_contDiffAt j (coverCenter j) hz).of_le (by simp)).mul
      (hF.contDiffAt ((chartAt ℂ (coverCenter (X := S) j)).open_target.mem_nhds hz))
    exact hm.congr_of_eventuallyEq (s22cp_chartPiece_germ j F hz)
  · have hn : z ∉ (chartAt ℂ (coverCenter (X := S) j)) ''
        tsupport (coverPoU (X := S) j) := by
      rintro ⟨x, hx, rfl⟩
      exact hz ((chartAt ℂ (coverCenter (X := S) j)).map_source
        (s22cp_support_source j hx))
    exact contDiffAt_const.congr_of_eventuallyEq (s22cp_chartPiece_zero_germ j F hn)

/-- The C1 extension's directional derivative is the product derivative on
the chart target. Thus the planar Stokes derivative really differentiates
the surface weight and the local coefficient. -/
theorem s22cp_chartPiece_fderiv
    (j : Fin ((chartCover : Finset S).card)) {F : ℂ → ℝ} {z : ℂ}
    (hz : z ∈ (chartAt ℂ (coverCenter (X := S) j)).target)
    (hF : DifferentiableAt ℝ F z) (v : ℂ) :
    fderiv ℝ (s22cp_chartPiece j F) z v =
      coverPoU (X := S) j ((chartAt ℂ (coverCenter (X := S) j)).symm z) *
        fderiv ℝ F z v +
      F z * fderiv ℝ
        (fun w => coverPoU (X := S) j
          ((chartAt ℂ (coverCenter (X := S) j)).symm w)) z v := by
  rw [(s22cp_chartPiece_germ j F hz).fderiv_eq,
    fderiv_fun_mul
      ((s22cp_weight_contDiffAt j (coverCenter j) hz).differentiableAt (by simp)) hF]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]

/-- Outside the compact support image both the coefficient and its actual
Frechet derivative vanish. No differentiability hypothesis is needed there. -/
theorem s22cp_chartPiece_fderiv_zero
    (j : Fin ((chartCover : Finset S).card)) (F : ℂ → ℝ) {z : ℂ}
    (hz : z ∉ (chartAt ℂ (coverCenter (X := S) j)) ''
      tsupport (coverPoU (X := S) j)) :
    fderiv ℝ (s22cp_chartPiece j F) z = 0 := by
  rw [(s22cp_chartPiece_zero_germ j F hz).fderiv_eq]
  simp

/-- Real-valued directional derivatives of C1 compactly supported functions
are integrable. This rules out the undefined-integral junk branch. -/
theorem s22cp_real_directional_integrable {F : ℂ → ℝ}
    (hF : ContDiff ℝ 1 F) (hs : HasCompactSupport F) (v : ℂ) :
    Integrable (fun z => fderiv ℝ F z v) := by
  have hc : Continuous (fun z => fderiv ℝ F z v) :=
    (hF.continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const)
  have hcs : HasCompactSupport (fun z => fderiv ℝ F z v) :=
    (hs.fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : ℂ →L[ℝ] ℝ => L v) (by simp)
  exact hc.integrable_of_hasCompactSupport hcs

/-- Real compact-support Stokes, directional version, derived from Haar
integration by parts against 1. The complex-valued installed counterpart is
not assumed to cover real-valued forms by an implicit coercion. -/
theorem s22cp_real_directional_integral_zero {F : ℂ → ℝ}
    (hF : ContDiff ℝ 1 F) (hs : HasCompactSupport F) (v : ℂ) :
    (∫ z : ℂ, fderiv ℝ F z v) = 0 := by
  have h1 : Integrable
      (fun z : ℂ => fderiv ℝ (fun _ : ℂ => (1 : ℝ)) z v * F z) := by
    simp
  have h2 : Integrable (fun z : ℂ => (1 : ℝ) * fderiv ℝ F z v) := by
    simpa only [one_mul] using s22cp_real_directional_integrable hF hs v
  have h3 : Integrable (fun z : ℂ => (1 : ℝ) * F z) := by
    simpa only [one_mul] using hF.continuous.integrable_of_hasCompactSupport hs
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : ℂ => (1 : ℝ)) (g := F) (v := v) h1 h2 h3
    (fun z _ => differentiableAt_const (1 : ℝ))
    (fun z _ => (hF.differentiable one_ne_zero).differentiableAt)
  simpa using he

/-- Actual local Stokes for PoU-weighted form coefficients. Compact support,
C1 regularity and integrability all follow from the surface partition.
This is an unconditional zero-integral conclusion once P,Q are C1 locally. -/
theorem s22cp_chartPiece_stokes
    (j : Fin ((chartCover : Finset S).card)) {P Q : ℂ → ℝ}
    (hP : ContDiffOn ℝ 1 P (chartAt ℂ (coverCenter (X := S) j)).target)
    (hQ : ContDiffOn ℝ 1 Q (chartAt ℂ (coverCenter (X := S) j)).target) :
    (∫ z : ℂ, fderiv ℝ (s22cp_chartPiece j Q) z 1 -
      fderiv ℝ (s22cp_chartPiece j P) z I) = 0 := by
  have hp := s22cp_chartPiece_contDiff j hP
  have hq := s22cp_chartPiece_contDiff j hQ
  have hps := s22cp_chartPiece_compactSupport j P
  have hqs := s22cp_chartPiece_compactSupport j Q
  rw [integral_sub (s22cp_real_directional_integrable hq hqs 1)
    (s22cp_real_directional_integrable hp hps I),
    s22cp_real_directional_integral_zero hq hqs 1,
    s22cp_real_directional_integral_zero hp hps I, sub_self]

/-- In any common coordinate, the actual global partition has zero total
differential. The derivative is taken after reading every weight in that
same coordinate; derivatives in unrelated charts are not added. -/
theorem s22cp_weight_sum_fderiv (y : S) {z : ℂ}
    (hz : z ∈ (chartAt ℂ y).target) :
    (∑ j : Fin ((chartCover : Finset S).card),
      fderiv ℝ (fun w => coverPoU (X := S) j ((chartAt ℂ y).symm w)) z) = 0 := by
  have hd : ∀ j : Fin ((chartCover : Finset S).card),
      DifferentiableAt ℝ
        (fun w => coverPoU (X := S) j ((chartAt ℂ y).symm w)) z :=
    fun j => (s22cp_weight_contDiffAt j y hz).differentiableAt (by simp)
  rw [← fderiv_fun_sum (fun j _ => hd j)]
  have he : (fun w : ℂ => ∑ j : Fin ((chartCover : Finset S).card),
      coverPoU (X := S) j ((chartAt ℂ y).symm w)) = fun _ => (1 : ℝ) := by
    funext w
    exact sum_coverPoU_eq_one _
  rw [he]
  simp

/-- The cross terms d(rho_j) wedge alpha cancel for every real one-form
coefficient pair in a common chart. This uses the constructed partition. -/
theorem s22cp_weight_cross_terms_zero (y : S) {z : ℂ}
    (hz : z ∈ (chartAt ℂ y).target) (P Q : ℝ) :
    (∑ j : Fin ((chartCover : Finset S).card),
      (fderiv ℝ (fun w => coverPoU (X := S) j ((chartAt ℂ y).symm w)) z 1 * Q -
       fderiv ℝ (fun w => coverPoU (X := S) j ((chartAt ℂ y).symm w)) z I * P)) = 0 := by
  have h1 := congrArg (fun L : ℂ →L[ℝ] ℝ => L 1) (s22cp_weight_sum_fderiv y hz)
  have hi := congrArg (fun L : ℂ →L[ℝ] ℝ => L I) (s22cp_weight_sum_fderiv y hz)
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.zero_apply] at h1 hi
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, h1, hi]
  ring

/-- The finite sum of weighted local curls is the original curl. Together
with chartPiece_stokes and change of variables this supplies the finite
partition algebra in a global Stokes proof. -/
theorem s22cp_weighted_curl_sum (y : S) {z : ℂ}
    (hz : z ∈ (chartAt ℂ y).target) {P Q : ℂ → ℝ}
    (hP : DifferentiableAt ℝ P z) (hQ : DifferentiableAt ℝ Q z) :
    (∑ j : Fin ((chartCover : Finset S).card),
      (fderiv ℝ (fun w => coverPoU (X := S) j ((chartAt ℂ y).symm w) * Q w) z 1 -
       fderiv ℝ (fun w => coverPoU (X := S) j ((chartAt ℂ y).symm w) * P w) z I)) =
      fderiv ℝ Q z 1 - fderiv ℝ P z I := by
  have hd : ∀ j : Fin ((chartCover : Finset S).card),
      DifferentiableAt ℝ
        (fun w => coverPoU (X := S) j ((chartAt ℂ y).symm w)) z :=
    fun j => (s22cp_weight_contDiffAt j y hz).differentiableAt (by simp)
  calc
    _ = ∑ j : Fin ((chartCover : Finset S).card),
        (coverPoU (X := S) j ((chartAt ℂ y).symm z) *
          (fderiv ℝ Q z 1 - fderiv ℝ P z I) +
        (fderiv ℝ (fun w => coverPoU (X := S) j ((chartAt ℂ y).symm w)) z 1 * Q z -
         fderiv ℝ (fun w => coverPoU (X := S) j ((chartAt ℂ y).symm w)) z I * P z)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [fderiv_fun_mul (hd j) hQ, fderiv_fun_mul (hd j) hP]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    _ = fderiv ℝ Q z 1 - fderiv ℝ P z I := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul,
        sum_coverPoU_eq_one, s22cp_weight_cross_terms_zero y hz (P z) (Q z),
        one_mul, add_zero]

end LiZhongQC
