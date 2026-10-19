import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.QDTransportZero
import LiZhongQC.Lemmas.QDSeamFill
import LiZhongQC.Lemmas.SchottkyCollarFromDouble

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- (Rel) The pull-back relation in the collar.  `κ` is a collar map linked to the half disc coordinate `wc`
(`hlink`: `κ w = chart_x (F.ι s)` where `ιd s = wc⁻¹ w`).  The transported coefficient `q0` of `Q` along
`E ∘ ιd ∘ F.ι⁻¹` on the open surface, evaluated at `κ w` and multiplied by `κ'(w)²`, equals the pull-back of `Q`
to the coordinate `wc`, read in any fixed chart `a` of the target containing `E (wc⁻¹ w')` for `w'` near `w`.
(Proof: `s31qr_transport_local` gives `q0 x z = Q a (chart_a (G (symm z))) * deriv (v ↦ chart_a (G (symm v))) z ^ 2`
with `G (F.ι s) = E (ιd s)`; the functions `v ↦ chart_a (G (symm_x v)) ∘ κ` and `w' ↦ chart_a (E (wc⁻¹ w'))` agree near
`w` (hlink), so the chain rule gives `deriv φ w = deriv g (κ w) * deriv κ w`.) -/
theorem s31qe_pullback_rel {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [Nonempty S]
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {Y : ClosedRS.{u}} (E : Xd.carrier ≃ₜ Y.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Y.carrier))
    {Q : Y.carrier → ℂ → ℂ} (hQ : IsDiffFamily 2 0 Q)
    {wc : OpenPartialHomeomorph Xd.carrier ℂ} {r : ℝ} (hwt : wc.target = ball 0 r)
    (hmds : ∀ z ∈ wc.target, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) wc.symm z)
    {x : F.X.carrier} {r' : ℝ} (hr' : r' ≤ r) {κ : ℂ → ℂ}
    (hκd : DifferentiableOn ℂ κ {z : ℂ | ‖z‖ < r' ∧ 0 < z.im})
    (hlink : ∀ z : ℂ, ‖z‖ < r' → 0 < z.im → ∃ s : S, ιd s = wc.symm z ∧
      F.ι s ∈ (chartAt ℂ x).source ∧ κ z = chartAt ℂ x (F.ι s))
    (a : Y.carrier) {ρ : ℝ} (ha : ∀ w : ℂ, ‖w‖ < ρ → E (wc.symm w) ∈ (chartAt ℂ a).source)
    {w : ℂ} (hw : ‖w‖ < r') (hwi : 0 < w.im) (hwρ : ‖w‖ < ρ) :
    s31qr_transportOn (range F.ι)
        (fun y : F.X.carrier => E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y)))
        (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x (κ w) * deriv κ w ^ 2 =
      Q a (chartAt ℂ a (E (wc.symm w))) *
        deriv (fun v : ℂ => chartAt ℂ a (E (wc.symm v))) w ^ 2 := by
  classical
  set H : F.X.carrier → Y.carrier := fun y => E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y))
    with hH
  have hBo := s31qk_isOpen_upper r'
  -- pointwise facts from the link
  have key : ∀ z : ℂ, ‖z‖ < r' → 0 < z.im →
      (chartAt ℂ x).symm (κ z) ∈ range F.ι ∧ κ z ∈ (chartAt ℂ x).target ∧
        H ((chartAt ℂ x).symm (κ z)) = E (wc.symm z) := by
    intro z hz hzi
    obtain ⟨s, hs1, hs2, hs3⟩ := hlink z hz hzi
    have hsymm : (chartAt ℂ x).symm (κ z) = F.ι s := by rw [hs3]; exact (chartAt ℂ x).left_inv hs2
    refine ⟨by rw [hsymm]; exact mem_range_self s, by rw [hs3]; exact (chartAt ℂ x).map_source hs2, ?_⟩
    rw [hsymm, hH]
    show E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm (F.ι s))) = _
    rw [F.embedding.toOpenPartialHomeomorph_left_inv F.ι, hs1]
  obtain ⟨hr1, hr2, hr3⟩ := key w hw hwi
  have hHm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) H ((chartAt ℂ x).symm (κ w)) := by
    have hinv := s31qr_open_embedding_inverse F.embedding F.holomorphic hr1
    exact (hE.1 _).comp _ ((hd.holomorphic _).comp _ hinv)
  have haw : H ((chartAt ℂ x).symm (κ w)) ∈ (chartAt ℂ a).source := by rw [hr3]; exact ha w hwρ
  have hloc := s31qr_transport_local (U := range F.ι) (H := H) hQ x a hr2 hr1 haw hHm
  set g : ℂ → ℂ := fun v => chartAt ℂ a (H ((chartAt ℂ x).symm v)) with hg
  have hgd : DifferentiableAt ℂ g (κ w) := s31qr_coordinate_differentiable x a hr2 haw hHm
  have hκw : DifferentiableAt ℂ κ w := hκd.differentiableAt (hBo.mem_nhds ⟨hw, hwi⟩)
  have hev : (fun v : ℂ => chartAt ℂ a (E (wc.symm v))) =ᶠ[𝓝 w] g ∘ κ := by
    filter_upwards [hBo.mem_nhds ⟨hw, hwi⟩] with z hz
    obtain ⟨-, -, h3⟩ := key z hz.1 hz.2
    show _ = chartAt ℂ a (H ((chartAt ℂ x).symm (κ z)))
    rw [h3]
  have hchain : deriv (fun v : ℂ => chartAt ℂ a (E (wc.symm v))) w = deriv g (κ w) * deriv κ w := by
    rw [hev.deriv_eq]
    exact deriv_comp w hgd hκw
  rw [hloc, hchain, hr3]
  ring

end LiZhongQC
