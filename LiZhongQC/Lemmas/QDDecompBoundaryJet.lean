import LiZhongQC.Lemmas.QDDecompJetLimit
import LiZhongQC.Lemmas.QDDecompJetLower
/-!
# S6a: the boundary jet of the collar map (round78)

`s31qd_boundary_jet` (frozen statement of the QD double-decomposition skeleton): `κ'` has a limit at each point of the
segment (`s31qj_deriv_limit`, module `QDDecompJetLimit`), and the limit is nonzero by the lower bound
`s31qj_deriv_lower` (module `QDDecompJetLower`).
-/

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- (S6a) Local first-jet Kellogg–Warschawski at the seam, in the setting of `s31qi_reflect_across_arc`
(without the coefficient `Qc`): the derivative of the collar map `κ` has a nonzero limit at every point of
the real segment, from the open upper half disc. -/
theorem s31qd_boundary_jet
    {Jd : Set ℂ} (hJd : IsJordanDomain Jd) (hbd : Bornology.IsBounded Jd)
    {c : ℝ → ℂ} (hc : ContDiff ℝ ∞ c) (hc' : ∀ t, deriv c t ≠ 0) (hper : ∀ t, c (t + 1) = c t)
    (hinj : InjOn c (Ico 0 1)) (hcf : c '' Ico 0 1 = frontier Jd)
    {r : ℝ} (hr : 0 < r) {κ : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hcont : ContinuousOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hκinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hup : MapsTo κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (closure Jd)ᶜ)
    (hreal : MapsTo κ {z : ℂ | ‖z‖ < r ∧ z.im = 0} (frontier Jd))
    (hlocal : ∃ V : Set ℂ, IsOpen V ∧ κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} = V ∩ Jdᶜ) :
    ∀ x : ℝ, |x| < r → ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (deriv κ) (𝓝[{z : ℂ | ‖z‖ < r ∧ 0 < z.im}] (x : ℂ)) (𝓝 L) := by
  intro x hx
  obtain ⟨L, hL⟩ := s31qj_deriv_limit hJd hc hc' hper hinj hcf hhol hcont hκinj hup hreal hlocal hx
  obtain ⟨m, δ, hm, hδ, hlow⟩ := s31qj_deriv_lower hJd hbd hc hc' hper hinj hcf hr hhol hcont hκinj hup hreal hlocal hx
  refine ⟨L, fun hL0 => ?_, hL⟩
  -- `m ≤ ‖κ'‖` near `x`, so `m ≤ ‖L‖ = 0`
  have hev : ∀ᶠ w in 𝓝[{z : ℂ | ‖z‖ < r ∧ 0 < z.im}] (x : ℂ), m ≤ ‖deriv κ w‖ := by
    have h1 : ball (x : ℂ) δ ∈ 𝓝 (x : ℂ) := ball_mem_nhds _ hδ
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1] with w hw hwb
    rw [mem_ball, dist_eq_norm] at hwb
    exact hlow w hwb hw.1 hw.2
  have hne : (𝓝[{z : ℂ | ‖z‖ < r ∧ 0 < z.im}] (x : ℂ)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.1 (Metric.mem_closure_iff.2 fun ε hε => ?_)
    set s : ℝ := min ε (r - |x|) / 2 with hs
    have hrx : 0 < r - |x| := by linarith
    have hs0 : 0 < s := by positivity
    refine ⟨(x : ℂ) + s * I, ⟨?_, by simpa using hs0⟩, ?_⟩
    · calc ‖(x : ℂ) + s * I‖ ≤ ‖(x : ℂ)‖ + ‖(s : ℂ) * I‖ := norm_add_le _ _
        _ = |x| + s := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hs0]
        _ < r := by have := min_le_right ε (r - |x|); linarith
    · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs0]
      have := min_le_left ε (r - |x|); linarith
  have := ge_of_tendsto hL.norm hev
  rw [hL0, norm_zero] at this
  linarith

end LiZhongQC
