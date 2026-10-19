import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.QDTransportZero
import LiZhongQC.Lemmas.QDSeamFill
import LiZhongQC.Lemmas.SchottkyCollarFromDouble
import LiZhongQC.Lemmas.QDBoundaryInverseContinuity
open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- (E3) Boundary limit of a function `g` whose pull-back `g (κ w) * κ'(w)^2` is a continuous function `P` of `w`
near `t`: along `κ(upper half disc)` at `κ t`, `g` tends to `P t / L^2`. -/
theorem s31qe_boundary_limit
    {Jd : Set ℂ} (hJd : IsJordanDomain Jd) (hbd : Bornology.IsBounded Jd)
    {r : ℝ} (hr : 0 < r) {κ : ℂ → ℂ}
    (hhol : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im})
    (hcont : ContinuousOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hκinj : InjOn κ {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im})
    (hup : MapsTo κ {z : ℂ | ‖z‖ < r ∧ 0 < z.im} (closure Jd)ᶜ)
    (hreal : MapsTo κ {z : ℂ | ‖z‖ < r ∧ z.im = 0} (frontier Jd))
    (hlocal : ∃ V : Set ℂ, IsOpen V ∧ κ '' {z : ℂ | ‖z‖ < r ∧ 0 ≤ z.im} = V ∩ Jdᶜ)
    {t : ℝ} (ht : |t| < r) {L : ℂ} (hL0 : L ≠ 0)
    (hL : Tendsto (deriv κ) (𝓝[{z : ℂ | ‖z‖ < r ∧ 0 < z.im}] (t : ℂ)) (𝓝 L))
    {g P : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hPc : ContinuousAt P t)
    (hg : ∀ w : ℂ, ‖w‖ < r → 0 < w.im → ‖w - t‖ < ρ → g (κ w) * deriv κ w ^ 2 = P w) :
    Tendsto g (𝓝[κ '' {z : ℂ | ‖z‖ < r ∧ 0 < z.im}] (κ t)) (𝓝 (P t / L ^ 2)) := by
  classical
  set B : Set ℂ := {z : ℂ | ‖z‖ < r ∧ 0 < z.im} with hB
  let ψ : ℂ → ℂ := Function.invFunOn κ B
  have hψmem : ∀ y ∈ κ '' B, ψ y ∈ B ∧ κ (ψ y) = y := fun y hy =>
    ⟨Function.invFunOn_mem hy, Function.invFunOn_eq hy⟩
  have hψB : Tendsto ψ (𝓝[κ '' B] (κ t)) (𝓝[B] (t : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hE2⟩ := s31qe_inverse_continuity hJd hbd hr hhol hcont hκinj hup hreal hlocal
        ht ε hε
      have hmem : κ '' B ∩ ball (κ (t : ℂ)) δ ∈ 𝓝[κ '' B] (κ (t : ℂ)) :=
        inter_mem_nhdsWithin _ (ball_mem_nhds _ hδ)
      filter_upwards [hmem] with y hy
      obtain ⟨hb1, hb2⟩ := hψmem y hy.1
      rw [dist_eq_norm]
      apply hE2 (ψ y) hb1.1 hb1.2.le
      rw [hb2]
      have h2 := hy.2
      rwa [mem_ball, dist_eq_norm] at h2
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hψmem y hy).1
  have hev1 : ∀ᶠ w : ℂ in 𝓝[B] (t : ℂ), deriv κ w ≠ 0 := hL.eventually_ne hL0
  have hev2 : ∀ᶠ w : ℂ in 𝓝[B] (t : ℂ), ‖w - (t : ℂ)‖ < ρ :=
    eventually_nhdsWithin_of_eventually_nhds (by
      have := ball_mem_nhds (t : ℂ) hρ
      filter_upwards [this] with w hw
      rwa [mem_ball, dist_eq_norm] at hw)
  have hev3 : ∀ᶠ w : ℂ in 𝓝[B] (t : ℂ), w ∈ B := self_mem_nhdsWithin
  have hev : ∀ᶠ y in 𝓝[κ '' B] (κ (t : ℂ)),
      deriv κ (ψ y) ≠ 0 ∧ ‖ψ y - t‖ < ρ ∧ ψ y ∈ B ∧ y ∈ κ '' B := by
    have h1 := hψB.eventually (hev1.and (hev2.and hev3))
    filter_upwards [h1, self_mem_nhdsWithin] with y hy hyB
    exact ⟨hy.1, hy.2.1, hy.2.2, hyB⟩
  have hlim : Tendsto (fun y => P (ψ y) / deriv κ (ψ y) ^ 2) (𝓝[κ '' B] (κ (t : ℂ)))
      (𝓝 (P t / L ^ 2)) := by
    have hψt : Tendsto ψ (𝓝[κ '' B] (κ (t : ℂ))) (𝓝 (t : ℂ)) := hψB.mono_right nhdsWithin_le_nhds
    have hP := hPc.tendsto.comp hψt
    have hD := (hL.comp hψB).pow 2
    exact hP.div hD (pow_ne_zero 2 hL0)
  refine hlim.congr' ?_
  filter_upwards [hev] with y ⟨hd0, hρy, hyB, hyK⟩
  obtain ⟨hb1, hb2⟩ := hψmem y hyK
  have h := hg (ψ y) hb1.1 hb1.2 hρy
  rw [hb2] at h
  rw [← h]
  field_simp [hd0]

end LiZhongQC
