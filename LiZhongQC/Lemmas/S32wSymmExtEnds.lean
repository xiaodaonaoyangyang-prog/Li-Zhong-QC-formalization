import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Ch08.S28_Moduli
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Lemmas.SchottkyCollarFromDouble
import LiZhongQC.Lemmas.FiniteTypeComponentTrapping
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.S32wAnnulusEnd
import LiZhongQC.Lemmas.S32wSeamCoordinate
import LiZhongQC.Lemmas.S32wReflectRectangle
import LiZhongQC.Lemmas.LV81PunctureRemovable
import LiZhongQC.Lemmas.SchottkyHalfRetraction

/-!
# §32.2 (W1.3, banked part): ends and the topological symmetric extension

Banked part of `S32wSymmetricExtension` (stubs a, b, c of the W1.3 interface, proved; leader suggestion R82):
* `s32w_se_double_dictionary`: the ends of `ιd(S)` in a Schottky double correspond to the ends of `ι(S)` in `F.X`
  (seam points to hole circles, punctures to punctures), with limits in both directions;
* `s32w_se_qc_end_limits`: a quasiconformal map has limits at the ends of `ι(S₀)`, hole circles going to hole circles
  and punctures to punctures;
* `s32w_se_exists`: a quasiconformal map has a symmetric extension to the doubles (a homeomorphism);
* the shared helper `s32w_se_coord_isKQC` (a `K`-q.c. map is `K`-q.c. in any holomorphic coordinates).
Helpers carry the prefix `s32w_se_`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **A quasiconformal map in holomorphic coordinates.**  Let `ι₀ : S₀ → X₀`, `ι₁ : S → X₁` be holomorphic open
embeddings and `α`, `β` coordinates of `X₀`, `X₁` that are biholomorphic at the points of `ι₀(S₀)`, `ι₁(S)`.  If
`s : G → S₀` lifts `α⁻¹` (`ι₀ ∘ s = α⁻¹` on the open set `G ⊆ α.target`) and `ι₁ ∘ f ∘ s` stays in the source of
`β`, then `β ∘ ι₁ ∘ f ∘ s` is `K`-q.c. on `G` for a `K`-q.c. `f` (locally it is a local expression of `f` between
holomorphic coordinate changes, `s26w_isKQC_local_comp`; `s13x_removable` with `L = ∅` globalizes). -/
theorem s32w_se_coord_isKQC {X₀ X₁ : Type*} [TopologicalSpace X₀] [ChartedSpace ℂ X₀] [IsManifold 𝓘(ℂ) ω X₀]
    [TopologicalSpace X₁] [ChartedSpace ℂ X₁] [IsManifold 𝓘(ℂ) ω X₁] {ι₀ : S₀ → X₀} {ι₁ : S → X₁}
    (h₀ : Topology.IsOpenEmbedding ι₀) (h₀m : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι₀)
    (h₁ : Topology.IsOpenEmbedding ι₁) (h₁m : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι₁)
    {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K) (α : OpenPartialHomeomorph X₀ ℂ) (β : OpenPartialHomeomorph X₁ ℂ)
    (hα : ∀ y : S₀, ι₀ y ∈ α.source →
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) α (ι₀ y) ∧ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) α.symm (α (ι₀ y)))
    (hβ : ∀ y : S, ι₁ y ∈ β.source →
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) β (ι₁ y) ∧ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) β.symm (β (ι₁ y)))
    {G : Set ℂ} (hG : IsOpen G) (hGt : G ⊆ α.target) {s : ℂ → S₀} (hs : ∀ z ∈ G, ι₀ (s z) = α.symm z)
    (hmaps : ∀ z ∈ G, ι₁ (f (s z)) ∈ β.source) :
    IsKQC (fun z => β (ι₁ (f (s z)))) G K := by
  classical
  haveI : Nonempty S₀ := ⟨f.symm (Classical.arbitrary S)⟩
  haveI : Nonempty S := ⟨Classical.arbitrary S⟩
  set e₀ := h₀.toOpenPartialHomeomorph ι₀ with he₀
  set e₁ := h₁.toOpenPartialHomeomorph ι₁ with he₁
  have hl₀ : ∀ y : S₀, e₀.symm (ι₀ y) = y := fun y => h₀.toOpenPartialHomeomorph_left_inv ι₀
  have hl₁ : ∀ y : S, e₁.symm (ι₁ y) = y := fun y => h₁.toOpenPartialHomeomorph_left_inv ι₁
  have hsr : ∀ z ∈ G, α.symm z ∈ range ι₀ := fun z hz => ⟨s z, hs z hz⟩
  have hse : ∀ z ∈ G, s z = e₀.symm (α.symm z) := fun z hz => by rw [← hs z hz, hl₀]
  -- continuity and the inverse
  have hsc : ContinuousOn s G := by
    intro z hz
    have h1 : ContinuousAt (fun w => e₀.symm (α.symm w)) z := by
      have h2 : α.symm z ∈ e₀.target := by
        rw [h₀.toOpenPartialHomeomorph_target]; exact hsr z hz
      exact (e₀.continuousAt_symm h2).comp (α.continuousAt_symm (hGt hz))
    exact (h1.congr (by filter_upwards [hG.mem_nhds hz] with w hw; exact (hse w hw).symm)).continuousWithinAt
  set h : ℂ → ℂ := fun z => β (ι₁ (f (s z))) with hh
  have hhc : ContinuousOn h G := by
    intro z hz
    have h1 : ContinuousAt (fun w => ι₁ (f w)) (s z) := (h₁.continuous.comp f.continuous).continuousAt
    have h2 : ContinuousWithinAt (fun w => ι₁ (f (s w))) G z := h1.comp_continuousWithinAt (hsc z hz)
    exact (β.continuousAt (hmaps z hz)).comp_continuousWithinAt (f := fun w => ι₁ (f (s w))) h2
  have hsinj : InjOn s G := by
    intro z hz w hw hzw
    have := congrArg ι₀ hzw
    rw [hs z hz, hs w hw] at this
    exact α.symm.injOn (hGt hz) (hGt hw) this
  have hhinj : InjOn h G := by
    intro z hz w hw hzw
    have h1 := β.injOn (hmaps z hz) (hmaps w hw) hzw
    exact hsinj hz hw (f.injective (h₁.injective h1))
  set ginv : ℂ → ℂ := fun w => α (ι₀ (f.symm (e₁.symm (β.symm w)))) with hginv
  have hginv_h : ∀ z ∈ G, ginv (h z) = z := by
    intro z hz
    show α (ι₀ (f.symm (e₁.symm (β.symm (β (ι₁ (f (s z)))))))) = z
    rw [β.left_inv (hmaps z hz), hl₁, f.symm_apply_apply, hs z hz, α.right_inv (hGt hz)]
  have hinvc : ContinuousOn (Function.invFunOn h G) (h '' G) := by
    have heq : EqOn ginv (Function.invFunOn h G) (h '' G) := by
      rintro _ ⟨z, hz, rfl⟩
      rw [hginv_h z hz, hhinj.leftInvOn_invFunOn hz]
    refine ContinuousOn.congr ?_ heq.symm
    rintro _ ⟨z, hz, rfl⟩
    have hb : h z ∈ β.target := β.map_source (hmaps z hz)
    have h1 : β.symm (h z) = ι₁ (f (s z)) := β.left_inv (hmaps z hz)
    have h2 : ContinuousAt e₁.symm (β.symm (h z)) := by
      refine e₁.continuousAt_symm ?_
      rw [h₁.toOpenPartialHomeomorph_target, h1]; exact mem_range_self _
    have h3 : ContinuousAt (fun y => α (ι₀ y)) (f.symm (e₁.symm (β.symm (h z)))) := by
      rw [h1, hl₁, f.symm_apply_apply]
      refine (α.continuousAt ?_).comp h₀.continuous.continuousAt
      rw [hs z hz]; exact α.map_target (hGt hz)
    have h4 : ContinuousAt (fun w => f.symm (e₁.symm (β.symm w))) (h z) :=
      ContinuousAt.comp (f := fun w => e₁.symm (β.symm w)) f.symm.continuous.continuousAt
        (h2.comp (β.continuousAt_symm hb))
    exact (ContinuousAt.comp (f := fun w => f.symm (e₁.symm (β.symm w))) h3 h4).continuousWithinAt
  have hhom : IsHomeomorphOnto h G (h '' G) := ⟨hhc, hhinj, rfl, hinvc⟩
  have hK1 : 1 ≤ K := hf.1
  refine s13x_removable (L := ∅) hG hK1 hhom measure_empty (by simp) (by simp) ?_
  intro z hz
  have hzG : z ∈ G := hz.1
  set x : S₀ := s z with hx
  -- the coordinate changes `τ = φ_x ∘ s` and `σ = β ∘ ι₁ ∘ φ_{f x}⁻¹`
  set τ : ℂ → ℂ := fun w => chartAt ℂ x (s w) with hτ
  set σ : ℂ → ℂ := fun v => β (ι₁ ((chartAt ℂ (f x)).symm v)) with hσ
  set U₁ : Set ℂ := G ∩ s ⁻¹' (chartAt ℂ x).source with hU₁
  have hU₁o : IsOpen U₁ := hsc.isOpen_inter_preimage hG (chartAt ℂ x).open_source
  have hzU₁ : z ∈ U₁ := ⟨hzG, mem_chart_source ℂ x⟩
  have hτd : DifferentiableOn ℂ τ U₁ := by
    intro w hw
    have hwG : w ∈ G := hw.1
    have hm1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) α.symm w := by
      have := (hα (s w) (by rw [hs w hwG]; exact α.map_target (hGt hwG))).2
      rwa [hs w hwG, α.right_inv (hGt hwG)] at this
    have hm2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e₀.symm (α.symm w) :=
      s31qr_open_embedding_inverse h₀ h₀m (hsr w hwG)
    have hm3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x) (e₀.symm (α.symm w)) := by
      rw [← hse w hwG]; exact mdifferentiableAt_atlas (chart_mem_atlas ℂ x) hw.2
    have hm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun v => chartAt ℂ x (e₀.symm (α.symm v))) w :=
      hm3.comp w (hm2.comp w hm1)
    have hd : DifferentiableAt ℂ (fun v => chartAt ℂ x (e₀.symm (α.symm v))) w :=
      mdifferentiableAt_iff_differentiableAt.1 hm
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hG.mem_nhds hwG] with v hv
    show chartAt ℂ x (s v) = chartAt ℂ x (e₀.symm (α.symm v))
    rw [hse v hv]
  have hτi : InjOn τ U₁ := by
    intro w hw v hv hwv
    exact hsinj hw.1 hv.1 ((chartAt ℂ x).injOn hw.2 hv.2 hwv)
  have hτa : AnalyticAt ℂ τ z := hτd.analyticAt (hU₁o.mem_nhds hzU₁)
  have hτ' : deriv τ z ≠ 0 := deriv_ne_zero_of_injOn hU₁o hτd hτi hzU₁
  set c₁ := chartAt ℂ (f x) with hc₁
  set U₂ : Set ℂ := c₁.target ∩ c₁.symm ⁻¹' (ι₁ ⁻¹' β.source) with hU₂
  have hU₂o : IsOpen U₂ := c₁.isOpen_inter_preimage_symm (β.open_source.preimage h₁.continuous)
  have hfx : f x ∈ c₁.source := mem_chart_source ℂ (f x)
  have hv₀ : c₁ (f x) ∈ U₂ := ⟨c₁.map_source hfx, by
    show ι₁ (c₁.symm (c₁ (f x))) ∈ β.source
    rw [c₁.left_inv hfx]; exact hmaps z hzG⟩
  have hσd : DifferentiableOn ℂ σ U₂ := by
    intro v hv
    have hm1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c₁.symm v := mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ (f x)) hv.1
    have hm2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ι₁ (c₁.symm v) := h₁m _
    have hm3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) β (ι₁ (c₁.symm v)) := (hβ _ hv.2).1
    exact (mdifferentiableAt_iff_differentiableAt.1 (hm3.comp v (hm2.comp v hm1))).differentiableWithinAt
  have hσi : InjOn σ U₂ := by
    intro v hv w hw hvw
    exact c₁.symm.injOn hv.1 hw.1 (h₁.injective (β.injOn hv.2 hw.2 hvw))
  have hτz : τ z = chartAt ℂ x x := rfl
  have hFτ : localMapExpr f x (τ z) = c₁ (f x) := by
    show chartAt ℂ (f x) (f ((chartAt ℂ x).symm (chartAt ℂ x x))) = c₁ (f x)
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]
  have hσa : AnalyticAt ℂ σ (localMapExpr f x (τ z)) := by
    rw [hFτ]; exact hσd.analyticAt (hU₂o.mem_nhds hv₀)
  have hσ' : deriv σ (localMapExpr f x (τ z)) ≠ 0 := by
    rw [hFτ]; exact deriv_ne_zero_of_injOn hU₂o hσd hσi hv₀
  have hτV : τ z ∈ localMapDomain f x := by
    refine ⟨(chartAt ℂ x).map_source (mem_chart_source ℂ x), ?_⟩
    show f ((chartAt ℂ x).symm (chartAt ℂ x x)) ∈ (chartAt ℂ (f x)).source
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x)]; exact hfx
  have hev : ∀ᶠ w in 𝓝 z, h w = σ (localMapExpr f x (τ w)) := by
    have hfs : ContinuousAt (fun w => f (s w)) z :=
      f.continuous.continuousAt.comp ((hsc z hzG).continuousAt (hG.mem_nhds hzG))
    have h2 : ∀ᶠ w in 𝓝 z, f (s w) ∈ c₁.source := hfs.preimage_mem_nhds (c₁.open_source.mem_nhds hfx)
    filter_upwards [hU₁o.mem_nhds hzU₁, h2] with w hw hw2
    show β (ι₁ (f (s w))) = β (ι₁ (c₁.symm (chartAt ℂ (f x) (f ((chartAt ℂ x).symm (chartAt ℂ x (s w)))))))
    rw [(chartAt ℂ x).left_inv hw.2, ← hc₁, c₁.left_inv hw2]
  obtain ⟨U, hUo, hzU, hUG, hUK⟩ := s26w_isKQC_local_comp (hf.2 x) hτV hτa hτ' hσa hσ' hev (hG.mem_nhds hzG)
  exact ⟨U, hUo, hzU, hUG, hUK⟩

/-- Hole coordinates (`s82td_hole_coordinates`): a point of the source of `W j` lies in `ι(S)` iff `‖W j y‖ > 1`. -/
theorem s32w_se_hole_range {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    {W : Fin m → OpenPartialHomeomorph F.X.carrier ℂ} {r : Fin m → ℝ}
    (hW : ∀ j, 1 < r j ∧ (W j).target = ball (0 : ℂ) (r j) ∧ F.D j ⊆ (W j).source ∧
        (∀ y ∈ (W j).source, y ∈ F.D j ↔ ‖W j y‖ ≤ 1) ∧
        (∀ y ∈ (W j).source, y ∉ (↑F.P : Set F.X.carrier)) ∧
        (∀ y ∈ (W j).source, y ∉ F.D j → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j) y) ∧
        (∀ w ∈ (W j).target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j).symm w))
    (hdis : Pairwise fun i j => Disjoint (W i).source (W j).source) (j : Fin m) {y : F.X.carrier}
    (hy : y ∈ (W j).source) : y ∈ range F.ι ↔ 1 < ‖W j y‖ := by
  rw [F.range_ι]
  constructor
  · intro h
    by_contra h'
    exact h (Or.inr (mem_iUnion.2 ⟨j, ((hW j).2.2.2.1 y hy).2 (not_lt.1 h')⟩))
  · intro h hc
    rcases hc with hp | hd
    · exact (hW j).2.2.2.2.1 y hy hp
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hd
      by_cases hij : i = j
      · subst hij
        have := ((hW i).2.2.2.1 y hy).1 hi
        linarith
      · exact disjoint_left.1 (hdis hij) ((hW i).2.2.1 hi) hy

/-- The frontier of `ι(S)` in `F.X`: the punctures, and the points with `‖W j‖ = 1` of the hole coordinates. -/
theorem s32w_se_hole_frontier {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    {W : Fin m → OpenPartialHomeomorph F.X.carrier ℂ} {r : Fin m → ℝ}
    (hW : ∀ j, 1 < r j ∧ (W j).target = ball (0 : ℂ) (r j) ∧ F.D j ⊆ (W j).source ∧
        (∀ y ∈ (W j).source, y ∈ F.D j ↔ ‖W j y‖ ≤ 1) ∧
        (∀ y ∈ (W j).source, y ∉ (↑F.P : Set F.X.carrier)) ∧
        (∀ y ∈ (W j).source, y ∉ F.D j → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j) y) ∧
        (∀ w ∈ (W j).target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j).symm w))
    (hdis : Pairwise fun i j => Disjoint (W i).source (W j).source) {c : F.X.carrier}
    (hcP : c ∉ (↑F.P : Set F.X.carrier)) :
    c ∈ frontier (range F.ι) ↔ ∃ j, c ∈ (W j).source ∧ ‖W j c‖ = 1 := by
  have hro : IsOpen (range F.ι) := F.embedding.isOpen_range
  rw [hro.frontier_eq]
  constructor
  · rintro ⟨hcl, hcr⟩
    have hc' : c ∈ (↑F.P ∪ ⋃ j, F.D j) := by
      rw [F.range_ι] at hcr; exact not_not.1 hcr
    rcases hc' with hp | hd
    · exact (hcP hp).elim
    obtain ⟨j, hj⟩ := mem_iUnion.1 hd
    have hcs : c ∈ (W j).source := (hW j).2.2.1 hj
    have hle : ‖W j c‖ ≤ 1 := ((hW j).2.2.2.1 c hcs).1 hj
    refine ⟨j, hcs, le_antisymm hle (not_lt.1 fun hlt => ?_)⟩
    have hO : IsOpen ((W j).source ∩ W j ⁻¹' ball 0 1) := (W j).isOpen_inter_preimage isOpen_ball
    obtain ⟨y, hyO, hyr⟩ := mem_closure_iff.1 hcl _ hO ⟨hcs, mem_ball_zero_iff.2 hlt⟩
    have := (s32w_se_hole_range F hW hdis j hyO.1).1 hyr
    have := mem_ball_zero_iff.1 hyO.2
    linarith
  · rintro ⟨j, hcs, hc1⟩
    refine ⟨?_, fun hr => by have := (s32w_se_hole_range F hW hdis j hcs).1 hr; linarith⟩
    set w₀ := W j c with hw₀
    have hw₀t : w₀ ∈ (W j).target := (W j).map_source hcs
    have hlim : Tendsto (fun t : ℝ => (W j).symm ((t : ℂ) * w₀)) (𝓝[>] (1 : ℝ)) (𝓝 c) := by
      have h1 : Tendsto (fun t : ℝ => (t : ℂ) * w₀) (𝓝[>] (1 : ℝ)) (𝓝 w₀) := by
        have : Tendsto (fun t : ℝ => (t : ℂ) * w₀) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) * w₀)) :=
          ((Complex.continuous_ofReal.tendsto 1).mul tendsto_const_nhds)
        simpa using this.mono_left nhdsWithin_le_nhds
      have h2 := ((W j).continuousAt_symm hw₀t).tendsto.comp h1
      rwa [(W j).left_inv hcs] at h2
    refine mem_closure_of_tendsto hlim ?_
    have h1 : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), (t : ℂ) * w₀ ∈ (W j).target := by
      have : Tendsto (fun t : ℝ => (t : ℂ) * w₀) (𝓝 (1 : ℝ)) (𝓝 w₀) := by
        simpa using ((Complex.continuous_ofReal.tendsto 1).mul (tendsto_const_nhds (x := w₀)))
      exact nhdsWithin_le_nhds (this.eventually ((W j).open_target.mem_nhds hw₀t))
    filter_upwards [h1, self_mem_nhdsWithin] with t ht ht1
    have hts : (W j).symm ((t : ℂ) * w₀) ∈ (W j).source := (W j).map_target ht
    refine (s32w_se_hole_range F hW hdis j hts).2 ?_
    rw [(W j).right_inv ht, norm_mul, Complex.norm_real, hc1, mul_one,
      Real.norm_of_nonneg (by linarith [show (1 : ℝ) < t from ht1])]
    exact ht1

/-- An annulus is preconnected (the image of a vertical strip under `exp`). -/
theorem s32w_se_annulus_preconnected {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : IsPreconnected (annulus a b) := by
  have heq : annulus a b = Complex.exp '' {z : ℂ | Real.log a < z.re ∧ z.re < Real.log b} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at h1; linarith
      refine ⟨Complex.log w, ⟨?_, ?_⟩, Complex.exp_log hw0⟩
      · rw [Complex.log_re]; exact Real.log_lt_log ha h1
      · rw [Complex.log_re]; exact Real.log_lt_log (by linarith) h2
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Complex.norm_exp]
        calc a = Real.exp (Real.log a) := (Real.exp_log ha).symm
          _ < Real.exp z.re := Real.exp_lt_exp.2 h1
      · rw [Complex.norm_exp]
        calc Real.exp z.re < Real.exp (Real.log b) := Real.exp_lt_exp.2 h2
          _ = b := Real.exp_log hb
  rw [heq]
  have hconv : Convex ℝ {z : ℂ | Real.log a < z.re ∧ z.re < Real.log b} :=
    ((convex_Ioi (Real.log a)).linear_preimage Complex.reLm).inter
      ((convex_Iio (Real.log b)).linear_preimage Complex.reLm)
  exact hconv.isPreconnected.image _ Complex.continuous_exp.continuousOn

/-- **Trapping of a hole end** (`s31eg_component_trapping` with the radius `‖W j‖` of the hole coordinate, cut off
at `ρ`, as the end parameter): under a homeomorphism `f`, the collar `1 < ‖W j‖ < 1 + δ` of a hole of `F₀` is mapped,
uniformly for small `δ`, into any neighbourhood of one deleted component of `F₁`. -/
theorem s32w_se_hole_trap {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    (f : S₀ ≃ₜ S) {W : Fin m → OpenPartialHomeomorph F₀.X.carrier ℂ} {r : Fin m → ℝ}
    (hW : ∀ j, 1 < r j ∧ (W j).target = ball (0 : ℂ) (r j) ∧ F₀.D j ⊆ (W j).source ∧
        (∀ y ∈ (W j).source, y ∈ F₀.D j ↔ ‖W j y‖ ≤ 1) ∧
        (∀ y ∈ (W j).source, y ∉ (↑F₀.P : Set F₀.X.carrier)) ∧
        (∀ y ∈ (W j).source, y ∉ F₀.D j → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j) y) ∧
        (∀ w ∈ (W j).target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j).symm w))
    (hdis : Pairwise fun i j => Disjoint (W i).source (W j).source) (j : Fin m) :
    ∃ k : ↥F₁.P ⊕ Fin m, ∀ V : Set F₁.X.carrier, IsOpen V → s31eg_component F₁ k ⊆ V →
      ∃ δ > 0, ∀ a : S₀, F₀.ι a ∈ (W j).source → ‖W j (F₀.ι a)‖ < 1 + δ → F₁.ι (f a) ∈ V := by
  classical
  obtain ⟨hr, ht, -, -, -, -, -⟩ := hW j
  set ρ : ℝ := (1 + r j) / 2 with hρ
  have hρ1 : 1 < ρ := by rw [hρ]; linarith
  have hρr : ρ < r j := by rw [hρ]; linarith
  set w := W j with hw
  -- the cut-off radius
  set i : S₀ → ℝ := fun a => if F₀.ι a ∈ w.source then min ρ ‖w (F₀.ι a)‖ else ρ with hi
  set C : Set F₀.X.carrier := w.symm '' closedBall 0 ρ with hC
  have hCc : IsClosed C := by
    refine (IsCompact.image_of_continuousOn (isCompact_closedBall 0 ρ) (w.continuousOn_symm.mono ?_)).isClosed
    intro z hz
    rw [ht, mem_ball_zero_iff]
    exact lt_of_le_of_lt (mem_closedBall_zero_iff.1 hz) hρr
  have hCmem : ∀ y ∈ w.source, ‖w y‖ ≤ ρ → y ∈ C := fun y hy hyρ =>
    ⟨w y, mem_closedBall_zero_iff.2 hyρ, w.left_inv hy⟩
  have hic : Continuous i := by
    rw [continuous_iff_continuousAt]
    intro a
    by_cases ha : F₀.ι a ∈ w.source
    · have h1 : ContinuousAt (fun b => min ρ ‖w (F₀.ι b)‖) a :=
        continuousAt_const.min (continuous_norm.continuousAt.comp
          ((w.continuousAt ha).comp F₀.embedding.continuous.continuousAt))
      refine h1.congr ?_
      filter_upwards [F₀.embedding.continuous.continuousAt.preimage_mem_nhds (w.open_source.mem_nhds ha)]
        with b hb
      show min ρ ‖w (F₀.ι b)‖ = if F₀.ι b ∈ w.source then min ρ ‖w (F₀.ι b)‖ else ρ
      rw [if_pos (show F₀.ι b ∈ w.source from hb)]
    · have haC : F₀.ι a ∉ C := by
        rintro ⟨z, hzC, hz⟩
        apply ha
        rw [← hz]
        refine w.map_target ?_
        rw [ht, mem_ball_zero_iff]
        exact lt_of_le_of_lt (mem_closedBall_zero_iff.1 hzC) hρr
      refine (continuousAt_const (y := ρ)).congr ?_
      filter_upwards [F₀.embedding.continuous.continuousAt.preimage_mem_nhds (hCc.isOpen_compl.mem_nhds haC)]
        with b hb
      show ρ = if F₀.ι b ∈ w.source then min ρ ‖w (F₀.ι b)‖ else ρ
      split_ifs with hbs
      · refine (min_eq_left ?_).symm
        by_contra hlt
        exact hb (hCmem _ hbs (not_le.1 hlt).le)
      · rfl
  have hrange : ∀ y ∈ w.source, 1 < ‖w y‖ → ∃ a : S₀, F₀.ι a = y := fun y hy h1 =>
    (s32w_se_hole_range F₀ hW hdis j hy).2 h1
  have hi1 : ∀ a, 1 < i a := by
    intro a
    show 1 < if F₀.ι a ∈ w.source then min ρ ‖w (F₀.ι a)‖ else ρ
    split_ifs with ha
    · exact lt_min hρ1 ((s32w_se_hole_range F₀ hW hdis j ha).1 (mem_range_self a))
    · exact hρ1
  -- small values of `i` are the collar points
  have hismall : ∀ a, i a < ρ → F₀.ι a ∈ w.source ∧ i a = ‖w (F₀.ι a)‖ := by
    intro a ha
    by_cases has : F₀.ι a ∈ w.source
    · refine ⟨has, ?_⟩
      have : i a = min ρ ‖w (F₀.ι a)‖ := if_pos has
      rw [this] at ha ⊢
      exact min_eq_right (le_of_lt (lt_of_not_ge fun h => by rw [min_eq_left h] at ha; exact lt_irrefl _ ha))
    · have : i a = ρ := if_neg has
      rw [this] at ha; exact (lt_irrefl _ ha).elim
  have hval : ∀ v : ℂ, 1 < ‖v‖ → ‖v‖ < ρ → ∃ a : S₀, F₀.ι a = w.symm v ∧ i a = ‖v‖ := by
    intro v hv1 hvρ
    have hvt : v ∈ w.target := by rw [ht, mem_ball_zero_iff]; linarith
    obtain ⟨a, ha⟩ := hrange _ (w.map_target hvt) (by rw [w.right_inv hvt]; exact hv1)
    refine ⟨a, ha, ?_⟩
    have has : F₀.ι a ∈ w.source := by rw [ha]; exact w.map_target hvt
    have : i a = min ρ ‖w (F₀.ι a)‖ := if_pos has
    rw [this, ha, w.right_inv hvt, min_eq_right hvρ.le]
  have hx : (1 : ℝ) ∉ range i := by
    rintro ⟨a, ha⟩
    have := hi1 a
    linarith
  have hnb : NeBot (comap i (𝓝 (1 : ℝ))) := by
    refine comap_neBot_iff.2 fun t ht' => ?_
    obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 ht'
    set τ : ℝ := min (ε / 2) ((ρ - 1) / 2) with hτ
    have hτ0 : 0 < τ := lt_min (half_pos hε) (by linarith)
    have hτε : τ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    have hτρ : τ < ρ - 1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hn : ‖((1 + τ : ℝ) : ℂ)‖ = 1 + τ := by rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    obtain ⟨a, -, hia⟩ := hval ((1 + τ : ℝ) : ℂ) (by rw [hn]; linarith) (by rw [hn]; linarith)
    refine ⟨a, hεt ?_⟩
    rw [hia, hn, Metric.mem_ball, Real.dist_eq, show 1 + τ - 1 = τ by ring, abs_of_pos hτ0]
    exact hτε
  have hconn : ∀ U ∈ 𝓝 (1 : ℝ), ∃ V ∈ 𝓝 (1 : ℝ), V ⊆ U ∧ IsPreconnected (i ⁻¹' V) := by
    intro U hU
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
    set ε' : ℝ := min ε (ρ - 1) with hε'
    have hε'0 : 0 < ε' := lt_min hε (by linarith)
    refine ⟨ball 1 ε', ball_mem_nhds _ hε'0, (ball_subset_ball (min_le_left _ _)).trans hεU, ?_⟩
    apply F₀.embedding.isInducing.isPreconnected_image.1
    have heq : F₀.ι '' (i ⁻¹' ball 1 ε') = w.symm '' annulus 1 (1 + ε') := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        have ha' : |i a - 1| < ε' := by rw [← Real.dist_eq]; exact ha
        have hiρ : i a < ρ := by have := min_le_right ε (ρ - 1); linarith [(abs_lt.1 ha').2]
        obtain ⟨has, hia⟩ := hismall a hiρ
        refine ⟨w (F₀.ι a), ⟨?_, ?_⟩, w.left_inv has⟩
        · rw [← hia]; exact hi1 a
        · rw [← hia]; linarith [(abs_lt.1 ha').2]
      · rintro ⟨v, ⟨hv1, hv2⟩, rfl⟩
        have hvρ : ‖v‖ < ρ := by have := min_le_right ε (ρ - 1); linarith
        obtain ⟨a, ha, hia⟩ := hval v hv1 hvρ
        refine ⟨a, ?_, ha⟩
        show i a ∈ ball 1 ε'
        rw [hia, Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith
    rw [heq]
    refine (s32w_se_annulus_preconnected one_pos (by linarith)).image _ (w.continuousOn_symm.mono ?_)
    intro v hv
    rw [ht, mem_ball_zero_iff]
    have := min_le_right ε (ρ - 1)
    linarith [hv.2]
  have hjj : Topology.IsOpenEmbedding (fun a : S₀ => F₁.ι (f a)) :=
    F₁.embedding.comp f.isOpenEmbedding
  have hcov : (range fun a : S₀ => F₁.ι (f a))ᶜ = ⋃ k, s31eg_component F₁ k := by
    rw [show (fun a : S₀ => F₁.ι (f a)) = F₁.ι ∘ f from rfl, f.surjective.range_comp]
    exact s31eg_components_cover F₁
  obtain ⟨k, hk⟩ := s31eg_component_trapping i (fun a : S₀ => F₁.ι (f a)) hic hjj (s31eg_component F₁)
    (s31eg_components_compact F₁) (s31eg_components_disjoint F₁) hcov hx hconn
  refine ⟨k, fun V hV hkV => ?_⟩
  obtain ⟨U, hU, hUV⟩ := hk V hV hkV
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.1 hU
  refine ⟨min δ (ρ - 1), lt_min hδ (by linarith), fun a has haδ => hUV a (hδU ?_)⟩
  have hlt : ‖w (F₀.ι a)‖ < ρ := by have := min_le_right δ (ρ - 1); linarith
  have hia : i a = ‖w (F₀.ι a)‖ := by
    have : i a = min ρ ‖w (F₀.ι a)‖ := if_pos has
    rw [this, min_eq_right hlt.le]
  rw [Metric.mem_ball, Real.dist_eq, hia, abs_lt]
  have h1 := (s32w_se_hole_range F₀ hW hdis j has).1 (mem_range_self a)
  have := min_le_left δ (ρ - 1)
  constructor <;> linarith

/-- **Trapping of a puncture end** under a homeomorphism (`s31eg_component_trapping`, as `s31eg_puncture_component`
with `F₁.ι ∘ f` in place of `G.ι`). -/
theorem s32w_se_puncture_trap {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    (f : S₀ ≃ₜ S) {c : F₀.X.carrier} (hc : c ∈ F₀.P) :
    ∃ k : ↥F₁.P ⊕ Fin m, ∀ V : Set F₁.X.carrier, IsOpen V → s31eg_component F₁ k ⊆ V →
      ∃ U ∈ 𝓝 c, ∀ a : S₀, F₀.ι a ∈ U → F₁.ι (f a) ∈ V := by
  letI := s31eg_puncture_neBot F₀ hc
  have hcr : c ∉ range F₀.ι := by
    rw [F₀.range_ι]
    exact fun h => h (Or.inl hc)
  have hcov : (range fun a : S₀ => F₁.ι (f a))ᶜ = ⋃ k, s31eg_component F₁ k := by
    rw [show (fun a : S₀ => F₁.ι (f a)) = F₁.ι ∘ f from rfl, f.surjective.range_comp]
    exact s31eg_components_cover F₁
  exact s31eg_component_trapping F₀.ι (fun a : S₀ => F₁.ι (f a)) F₀.embedding.continuous
    (F₁.embedding.comp f.isOpenEmbedding) (s31eg_component F₁) (s31eg_components_compact F₁)
    (s31eg_components_disjoint F₁) hcov hcr (s31eg_puncture_connected_traces F₀ hc)

/-- **A puncture end is not mapped into a hole collar** by a `K`-q.c. map: otherwise `f` in a chart at the puncture
and the hole coordinate `W₁ j'` is a bounded `K`-q.c. map of a punctured disc into `1 < ‖w‖`, with limit values of
norm `1`; by `lv81_puncture_removable` it extends to a `K`-q.c. map of the disc, whose open image contains a point of
norm `< 1`.  (General source: a holomorphic open embedding `ι₀ : S₀ → X₀` whose range is a punctured
neighbourhood of `c`.) -/
theorem s32w_se_punct_not_hole_gen {X₀ : Type*} [TopologicalSpace X₀] [T2Space X₀] [ChartedSpace ℂ X₀]
    [IsManifold 𝓘(ℂ) ω X₀] {ι₀ : S₀ → X₀} (h₀ : Topology.IsOpenEmbedding ι₀)
    (h₀m : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι₀) {g n m : ℕ}
    (F₁ : FiniteTypeStructure S g n m) {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K)
    {W : Fin m → OpenPartialHomeomorph F₁.X.carrier ℂ} {r : Fin m → ℝ}
    (hW : ∀ j, 1 < r j ∧ (W j).target = ball (0 : ℂ) (r j) ∧ F₁.D j ⊆ (W j).source ∧
        (∀ y ∈ (W j).source, y ∈ F₁.D j ↔ ‖W j y‖ ≤ 1) ∧
        (∀ y ∈ (W j).source, y ∉ (↑F₁.P : Set F₁.X.carrier)) ∧
        (∀ y ∈ (W j).source, y ∉ F₁.D j → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j) y) ∧
        (∀ w ∈ (W j).target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j).symm w))
    (hdis : Pairwise fun i j => Disjoint (W i).source (W j).source) {c : X₀}
    (hpunct : ∀ᶠ y in 𝓝[≠] c, y ∈ range ι₀) (j' : Fin m)
    (htrap : ∀ V : Set F₁.X.carrier, IsOpen V → F₁.D j' ⊆ V → ∃ U ∈ 𝓝 c, ∀ a : S₀, ι₀ a ∈ U → F₁.ι (f a) ∈ V) :
    False := by
  classical
  obtain ⟨-, ht, hDs, hDn, -, hWd, hWs⟩ := hW j'
  set β := W j' with hβdef
  set φ := chartAt ℂ c with hφ
  have hcφ : c ∈ φ.source := mem_chart_source ℂ c
  set z₀ := φ c with hz₀
  have hz₀t : z₀ ∈ φ.target := φ.map_source hcφ
  obtain ⟨u, hu, hur⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hpunct
  have hsymm_nhds : ∀ U ∈ 𝓝 c, φ.symm ⁻¹' U ∈ 𝓝 z₀ := fun U hU =>
    (φ.continuousAt_symm hz₀t).preimage_mem_nhds (by rw [φ.left_inv hcφ]; exact hU)
  obtain ⟨U₁, hU₁, hU₁V⟩ := htrap β.source β.open_source hDs
  have hN : φ.symm ⁻¹' (U₁ ∩ u) ∩ φ.target ∈ 𝓝 z₀ :=
    inter_mem (hsymm_nhds _ (inter_mem hU₁ hu)) (φ.open_target.mem_nhds hz₀t)
  obtain ⟨ρ, hρ, hρN⟩ := Metric.mem_nhds_iff.1 hN
  set G : Set ℂ := ball z₀ ρ \ {z₀} with hG
  have hGo : IsOpen G := isOpen_ball.sdiff isClosed_singleton
  have hGt : G ⊆ φ.target := fun z hz => (hρN hz.1).2
  have hGr : ∀ z ∈ G, φ.symm z ∈ range ι₀ := by
    intro z hz
    refine hur ⟨(hρN hz.1).1.2, fun hzc => ?_⟩
    have := φ.right_inv (hGt hz)
    rw [show φ.symm z = c from hzc] at this
    exact hz.2 (mem_singleton_iff.2 this.symm)
  set s : ℂ → S₀ := fun z => Function.invFun ι₀ (φ.symm z) with hsdef
  have hs : ∀ z ∈ G, ι₀ (s z) = φ.symm z := fun z hz => Function.invFun_eq (hGr z hz)
  have hmaps : ∀ z ∈ G, F₁.ι (f (s z)) ∈ β.source := fun z hz =>
    hU₁V _ (by rw [hs z hz]; exact (hρN hz.1).1.1)
  have hα : ∀ y : S₀, ι₀ y ∈ φ.source →
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ (ι₀ y) ∧ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) φ.symm (φ (ι₀ y)) := fun y hy =>
    ⟨mdifferentiableAt_atlas (chart_mem_atlas ℂ c) hy,
      mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ c) (φ.map_source hy)⟩
  have hβ : ∀ y : S, F₁.ι y ∈ β.source →
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) β (F₁.ι y) ∧ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) β.symm (β (F₁.ι y)) := by
    intro y hy
    have h1 := (s32w_se_hole_range F₁ hW hdis j' hy).1 (mem_range_self y)
    refine ⟨hWd _ hy fun hD => ?_, hWs _ (β.map_source hy) h1⟩
    have := (hDn _ hy).1 hD
    linarith
  set h : ℂ → ℂ := fun z => β (F₁.ι (f (s z))) with hh
  have hK : IsKQC h G K :=
    s32w_se_coord_isKQC h₀ h₀m F₁.embedding F₁.holomorphic hf φ β hα hβ hGo hGt hs hmaps
  have hbdd : Bornology.IsBounded (h '' (ball z₀ ρ \ {z₀})) := by
    refine (Metric.isBounded_ball (x := (0 : ℂ)) (r := r j')).subset ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [← ht]
    exact β.map_source (hmaps z hz)
  have hz₀G : z₀ ∉ G := fun h' => h'.2 rfl
  obtain ⟨w₀, hlim, -, hupd⟩ := lv81_puncture_removable hK hρ subset_rfl hz₀G hbdd
  have h1 : ∀ z ∈ G, 1 < ‖h z‖ := fun z hz =>
    (s32w_se_hole_range F₁ hW hdis j' (hmaps z hz)).1 (mem_range_self _)
  have hGev : ∀ᶠ z in 𝓝[≠] z₀, z ∈ G := by
    filter_upwards [inter_mem_nhdsWithin {z₀}ᶜ (ball_mem_nhds z₀ hρ)] with z hz
    exact ⟨hz.2, hz.1⟩
  have hge : 1 ≤ ‖w₀‖ :=
    ge_of_tendsto hlim.norm (by filter_upwards [hGev] with z hz; exact (h1 z hz).le)
  have hle : ‖w₀‖ ≤ 1 := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    have hVo : IsOpen (β.source ∩ β ⁻¹' ball 0 (1 + ε / 2)) := β.isOpen_inter_preimage isOpen_ball
    have hDV : F₁.D j' ⊆ β.source ∩ β ⁻¹' ball 0 (1 + ε / 2) := fun y hy =>
      ⟨hDs hy, mem_ball_zero_iff.2 (by have := (hDn y (hDs hy)).1 hy; linarith)⟩
    obtain ⟨U₂, hU₂, hU₂V⟩ := htrap _ hVo hDV
    have hev2 : ∀ᶠ z in 𝓝[≠] z₀, ‖h z‖ ≤ 1 + ε / 2 := by
      filter_upwards [hGev, nhdsWithin_le_nhds (hsymm_nhds U₂ hU₂)] with z hz hz2
      have := hU₂V (s z) (by rw [hs z hz]; exact hz2)
      exact (mem_ball_zero_iff.1 this.2).le
    have := le_of_tendsto hlim.norm hev2
    linarith
  have hw1 : ‖w₀‖ = 1 := le_antisymm hle hge
  have hins : insert z₀ G = ball z₀ ρ := by
    rw [hG, insert_diff_singleton, insert_eq_of_mem (mem_ball_self hρ)]
  have hopen := isOpen_image_of_isKQC hupd
  have hw₀mem : w₀ ∈ Function.update h z₀ w₀ '' insert z₀ G :=
    ⟨z₀, mem_insert _ _, Function.update_self _ _ _⟩
  obtain ⟨η, hη, hηsub⟩ := Metric.isOpen_iff.1 hopen w₀ hw₀mem
  set t : ℝ := min (η / 2) (1 / 2) with htdef
  have ht0 : 0 < t := lt_min (half_pos hη) (by norm_num)
  have htη : t < η := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hη)
  have ht1 : t ≤ 1 / 2 := min_le_right _ _
  set w₁ : ℂ := ((1 - t : ℝ) : ℂ) * w₀ with hw₁
  have hn1 : ‖w₁‖ = 1 - t := by
    rw [hw₁, norm_mul, Complex.norm_real, hw1, mul_one, Real.norm_of_nonneg (by linarith)]
  have hd : dist w₁ w₀ < η := by
    rw [dist_eq_norm, show w₁ - w₀ = -((t : ℂ) * w₀) by rw [hw₁]; push_cast; ring, norm_neg, norm_mul,
      Complex.norm_real, hw1, mul_one, Real.norm_of_nonneg ht0.le]
    exact htη
  obtain ⟨z, hz, hzw⟩ := hηsub (mem_ball.2 hd)
  by_cases hzz : z = z₀
  · rw [hzz, Function.update_self] at hzw
    have := congrArg norm hzw
    rw [hn1, hw1] at this
    linarith
  · rw [Function.update_of_ne hzz] at hzw
    have hzG : z ∈ G := by
      rcases hz with h' | h'
      · exact (hzz h').elim
      · exact h'
    have := h1 z hzG
    rw [hzw, hn1] at this
    linarith

/-- **A puncture end is not mapped into a hole collar** by a `K`-q.c. map (`s32w_se_punct_not_hole_gen` for
`ι₀ = F₀.ι`: a small punctured neighbourhood of a puncture lies in `ι(S₀)`). -/
theorem s32w_se_puncture_not_hole {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m) {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K)
    {W : Fin m → OpenPartialHomeomorph F₁.X.carrier ℂ} {r : Fin m → ℝ}
    (hW : ∀ j, 1 < r j ∧ (W j).target = ball (0 : ℂ) (r j) ∧ F₁.D j ⊆ (W j).source ∧
        (∀ y ∈ (W j).source, y ∈ F₁.D j ↔ ‖W j y‖ ≤ 1) ∧
        (∀ y ∈ (W j).source, y ∉ (↑F₁.P : Set F₁.X.carrier)) ∧
        (∀ y ∈ (W j).source, y ∉ F₁.D j → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j) y) ∧
        (∀ w ∈ (W j).target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j).symm w))
    (hdis : Pairwise fun i j => Disjoint (W i).source (W j).source) {c : F₀.X.carrier} (hc : c ∈ F₀.P)
    (j' : Fin m)
    (htrap : ∀ V : Set F₁.X.carrier, IsOpen V → F₁.D j' ⊆ V → ∃ U ∈ 𝓝 c, ∀ a : S₀, F₀.ι a ∈ U → F₁.ι (f a) ∈ V) :
    False := by
  set Bad : Set F₀.X.carrier := ((↑F₀.P : Set F₀.X.carrier) \ {c}) ∪ ⋃ i, F₀.D i with hBad
  have hBadc : IsClosed Bad :=
    ((F₀.P.finite_toSet.subset sdiff_subset).isClosed).union
      (isCompact_iUnion fun i => s31eg_disc_compact (F₀.disc i)).isClosed
  have hcBad : c ∉ Bad := by
    rintro (⟨-, h⟩ | h)
    · exact h rfl
    · obtain ⟨i, hi⟩ := mem_iUnion.1 h
      exact disjoint_left.1 (F₀.disjoint_P i) hi hc
  have hpunct : ∀ᶠ y in 𝓝[≠] c, y ∈ range F₀.ι := by
    filter_upwards [inter_mem_nhdsWithin {c}ᶜ (hBadc.isOpen_compl.mem_nhds hcBad)] with y hy
    rw [F₀.range_ι]
    rintro (hp | hd)
    · exact hy.2 (Or.inl ⟨hp, hy.1⟩)
    · exact hy.2 (Or.inr hd)
  exact s32w_se_punct_not_hole_gen F₀.embedding F₀.holomorphic F₁ hf hW hdis hpunct j' htrap

/-- The punctures lie in the frontier of `ι(S)`. -/
theorem s32w_se_puncture_frontier {g n m : ℕ} (F : FiniteTypeStructure S g n m) {p : F.X.carrier}
    (hp : p ∈ F.P) : p ∈ frontier (range F.ι) := by
  rw [F.embedding.isOpen_range.frontier_eq]
  refine ⟨mem_closure_iff_nhds.2 fun t ht => ?_, fun h => by rw [F.range_ι] at h; exact h (Or.inl hp)⟩
  obtain ⟨a, ha⟩ := comap_neBot_iff.1 (s31eg_puncture_neBot F hp) t ht
  exact ⟨F.ι a, ha, mem_range_self a⟩

/-- **Punctures go to punctures** under a `K`-q.c. map, with a limit. -/
theorem s32w_se_puncture_limit {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K) {c : F₀.X.carrier} (hc : c ∈ F₀.P) :
    ∃ p' ∈ F₁.P, Tendsto (fun a => F₁.ι (f a)) (comap F₀.ι (𝓝 c)) (𝓝 p') := by
  obtain ⟨W, r, hW, hdis⟩ := s82td_hole_coordinates F₁
  obtain ⟨k, hk⟩ := s32w_se_puncture_trap F₀ F₁ f hc
  cases k with
  | inl p =>
    refine ⟨p.1, p.2, ?_⟩
    rw [_root_.tendsto_nhds]
    intro V hV hpV
    obtain ⟨U, hU, hUV⟩ := hk V hV (singleton_subset_iff.2 hpV)
    exact mem_comap.2 ⟨U, hU, fun a ha => hUV a ha⟩
  | inr j' => exact (s32w_se_puncture_not_hole F₀ F₁ hf hW hdis hc j' fun V hV hDV => hk V hV hDV).elim

/-- A point with `‖W j c‖ = 1` is approached by `ι(S)`: the filter `comap ι (𝓝 c)` is nontrivial. -/
theorem s32w_se_hole_neBot {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    {W : Fin m → OpenPartialHomeomorph F.X.carrier ℂ} {r : Fin m → ℝ}
    (hW : ∀ j, 1 < r j ∧ (W j).target = ball (0 : ℂ) (r j) ∧ F.D j ⊆ (W j).source ∧
        (∀ y ∈ (W j).source, y ∈ F.D j ↔ ‖W j y‖ ≤ 1) ∧
        (∀ y ∈ (W j).source, y ∉ (↑F.P : Set F.X.carrier)) ∧
        (∀ y ∈ (W j).source, y ∉ F.D j → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j) y) ∧
        (∀ w ∈ (W j).target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j).symm w))
    (hdis : Pairwise fun i j => Disjoint (W i).source (W j).source) {j : Fin m} {c : F.X.carrier}
    (hcs : c ∈ (W j).source) (hc1 : ‖W j c‖ = 1) : NeBot (comap F.ι (𝓝 c)) := by
  have hfr := (s32w_se_hole_frontier F hW hdis ((hW j).2.2.2.2.1 c hcs)).2 ⟨j, hcs, hc1⟩
  have hcl : c ∈ closure (range F.ι) := frontier_subset_closure hfr
  refine comap_neBot_iff.2 fun t ht => ?_
  obtain ⟨y, hyt, a, rfl⟩ := mem_closure_iff_nhds.1 hcl t ht
  exact ⟨a, hyt⟩

/-- **A hole end is not mapped to a puncture** by a `K`-q.c. map (else the inverse would map the puncture end to
the hole, against `s32w_se_puncture_limit`). -/
theorem s32w_se_hole_not_puncture {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m) {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K)
    {W : Fin m → OpenPartialHomeomorph F₀.X.carrier ℂ} {r : Fin m → ℝ}
    (hW : ∀ j, 1 < r j ∧ (W j).target = ball (0 : ℂ) (r j) ∧ F₀.D j ⊆ (W j).source ∧
        (∀ y ∈ (W j).source, y ∈ F₀.D j ↔ ‖W j y‖ ≤ 1) ∧
        (∀ y ∈ (W j).source, y ∉ (↑F₀.P : Set F₀.X.carrier)) ∧
        (∀ y ∈ (W j).source, y ∉ F₀.D j → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j) y) ∧
        (∀ w ∈ (W j).target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j).symm w))
    (hdis : Pairwise fun i j => Disjoint (W i).source (W j).source) (j : Fin m) (p' : ↥F₁.P)
    (htrap : ∀ V : Set F₁.X.carrier, IsOpen V → {p'.1} ⊆ V →
      ∃ δ > 0, ∀ a : S₀, F₀.ι a ∈ (W j).source → ‖W j (F₀.ι a)‖ < 1 + δ → F₁.ι (f a) ∈ V) : False := by
  obtain ⟨hr, ht, -, -, hPs, -, -⟩ := hW j
  have h1t : (1 : ℂ) ∈ (W j).target := by rw [ht, mem_ball_zero_iff, norm_one]; exact hr
  set c₀ := (W j).symm 1 with hc₀
  have hc₀s : c₀ ∈ (W j).source := (W j).map_target h1t
  have hc₀1 : ‖W j c₀‖ = 1 := by rw [hc₀, (W j).right_inv h1t, norm_one]
  have := s32w_se_hole_neBot F₀ hW hdis hc₀s hc₀1
  have hcoll : ∀ δ > 0, ∀ᶠ a in comap F₀.ι (𝓝 c₀), F₀.ι a ∈ (W j).source ∧ ‖W j (F₀.ι a)‖ < 1 + δ := by
    intro δ hδ
    have hO : IsOpen ((W j).source ∩ W j ⁻¹' ball 0 (1 + δ)) := (W j).isOpen_inter_preimage isOpen_ball
    have hm : c₀ ∈ (W j).source ∩ W j ⁻¹' ball 0 (1 + δ) :=
      ⟨hc₀s, mem_ball_zero_iff.2 (by rw [hc₀1]; linarith)⟩
    exact mem_comap.2 ⟨_, hO.mem_nhds hm, fun a ha => ⟨ha.1, mem_ball_zero_iff.1 ha.2⟩⟩
  have hf1 : Tendsto (fun a => F₁.ι (f a)) (comap F₀.ι (𝓝 c₀)) (𝓝 p'.1) := by
    rw [_root_.tendsto_nhds]
    intro V hV hpV
    obtain ⟨δ, hδ, hδV⟩ := htrap V hV (singleton_subset_iff.2 hpV)
    filter_upwards [hcoll δ hδ] with a ha
    exact hδV a ha.1 ha.2
  have hf2 : Tendsto f (comap F₀.ι (𝓝 c₀)) (comap F₁.ι (𝓝 p'.1)) := tendsto_comap_iff.2 hf1
  obtain ⟨p'', hp'', hlim⟩ := s32w_se_puncture_limit F₁ F₀ (s29_m_isKQCRS_symm hf) p'.2
  have h2 : Tendsto F₀.ι (comap F₀.ι (𝓝 c₀)) (𝓝 p'') := by
    have := hlim.comp hf2
    simpa [Function.comp_def] using this
  have h3 : Tendsto F₀.ι (comap F₀.ι (𝓝 c₀)) (𝓝 c₀) := tendsto_comap
  have heq : c₀ = p'' := tendsto_nhds_unique h3 h2
  exact hPs c₀ hc₀s (heq ▸ hp'')

/-- **Holes go to holes** under a `K`-q.c. map: the collar of the hole `j` is trapped by a hole `j'`. -/
theorem s32w_se_hole_target {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m) {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K)
    {W : Fin m → OpenPartialHomeomorph F₀.X.carrier ℂ} {r : Fin m → ℝ}
    (hW : ∀ j, 1 < r j ∧ (W j).target = ball (0 : ℂ) (r j) ∧ F₀.D j ⊆ (W j).source ∧
        (∀ y ∈ (W j).source, y ∈ F₀.D j ↔ ‖W j y‖ ≤ 1) ∧
        (∀ y ∈ (W j).source, y ∉ (↑F₀.P : Set F₀.X.carrier)) ∧
        (∀ y ∈ (W j).source, y ∉ F₀.D j → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j) y) ∧
        (∀ w ∈ (W j).target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W j).symm w))
    (hdis : Pairwise fun i j => Disjoint (W i).source (W j).source) (j : Fin m) :
    ∃ j' : Fin m, ∀ V : Set F₁.X.carrier, IsOpen V → F₁.D j' ⊆ V →
      ∃ δ > 0, ∀ a : S₀, F₀.ι a ∈ (W j).source → ‖W j (F₀.ι a)‖ < 1 + δ → F₁.ι (f a) ∈ V := by
  obtain ⟨k, hk⟩ := s32w_se_hole_trap F₀ F₁ f hW hdis j
  cases k with
  | inl p => exact (s32w_se_hole_not_puncture F₀ F₁ hf hW hdis j p fun V hV hpV => hk V hV hpV).elim
  | inr j' => exact ⟨j', fun V hV hDV => hk V hV hDV⟩

/-- **The hole correspondence is inverse**: if `f` traps the hole `j` of `F₀` by the hole `j'` of `F₁` and `f⁻¹`
traps `j'` by `j''`, then `j'' = j` (the collar of `j` would otherwise come back into the disjoint coordinate
neighbourhood of `j''`). -/
theorem s32w_se_hole_pair {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m) {f : S₀ ≃ₜ S}
    {W₀ : Fin m → OpenPartialHomeomorph F₀.X.carrier ℂ} {r₀ : Fin m → ℝ}
    (hW₀ : ∀ j, 1 < r₀ j ∧ (W₀ j).target = ball (0 : ℂ) (r₀ j) ∧ F₀.D j ⊆ (W₀ j).source ∧
        (∀ y ∈ (W₀ j).source, y ∈ F₀.D j ↔ ‖W₀ j y‖ ≤ 1) ∧
        (∀ y ∈ (W₀ j).source, y ∉ (↑F₀.P : Set F₀.X.carrier)) ∧
        (∀ y ∈ (W₀ j).source, y ∉ F₀.D j → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W₀ j) y) ∧
        (∀ w ∈ (W₀ j).target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W₀ j).symm w))
    (hdis₀ : Pairwise fun i j => Disjoint (W₀ i).source (W₀ j).source)
    {W₁ : Fin m → OpenPartialHomeomorph F₁.X.carrier ℂ} {r₁ : Fin m → ℝ}
    (hW₁ : ∀ j, 1 < r₁ j ∧ (W₁ j).target = ball (0 : ℂ) (r₁ j) ∧ F₁.D j ⊆ (W₁ j).source ∧
        (∀ y ∈ (W₁ j).source, y ∈ F₁.D j ↔ ‖W₁ j y‖ ≤ 1) ∧
        (∀ y ∈ (W₁ j).source, y ∉ (↑F₁.P : Set F₁.X.carrier)) ∧
        (∀ y ∈ (W₁ j).source, y ∉ F₁.D j → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W₁ j) y) ∧
        (∀ w ∈ (W₁ j).target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W₁ j).symm w))
    {j j' j'' : Fin m}
    (h01 : ∀ V : Set F₁.X.carrier, IsOpen V → F₁.D j' ⊆ V →
      ∃ δ > 0, ∀ a : S₀, F₀.ι a ∈ (W₀ j).source → ‖W₀ j (F₀.ι a)‖ < 1 + δ → F₁.ι (f a) ∈ V)
    (h10 : ∀ V : Set F₀.X.carrier, IsOpen V → F₀.D j'' ⊆ V →
      ∃ δ > 0, ∀ b : S, F₁.ι b ∈ (W₁ j').source → ‖W₁ j' (F₁.ι b)‖ < 1 + δ → F₀.ι (f.symm b) ∈ V) :
    j'' = j := by
  by_contra hne
  obtain ⟨hr, ht, -, -, -, -, -⟩ := hW₀ j
  have h1t : (1 : ℂ) ∈ (W₀ j).target := by rw [ht, mem_ball_zero_iff, norm_one]; exact hr
  set c₀ := (W₀ j).symm 1 with hc₀
  have hc₀s : c₀ ∈ (W₀ j).source := (W₀ j).map_target h1t
  have hc₀1 : ‖W₀ j c₀‖ = 1 := by rw [hc₀, (W₀ j).right_inv h1t, norm_one]
  have := s32w_se_hole_neBot F₀ hW₀ hdis₀ hc₀s hc₀1
  have hcoll : ∀ δ > 0, ∀ᶠ a in comap F₀.ι (𝓝 c₀), F₀.ι a ∈ (W₀ j).source ∧ ‖W₀ j (F₀.ι a)‖ < 1 + δ := by
    intro δ hδ
    have hO : IsOpen ((W₀ j).source ∩ W₀ j ⁻¹' ball 0 (1 + δ)) := (W₀ j).isOpen_inter_preimage isOpen_ball
    have hm : c₀ ∈ (W₀ j).source ∩ W₀ j ⁻¹' ball 0 (1 + δ) :=
      ⟨hc₀s, mem_ball_zero_iff.2 (by rw [hc₀1]; linarith)⟩
    exact mem_comap.2 ⟨_, hO.mem_nhds hm, fun a ha => ⟨ha.1, mem_ball_zero_iff.1 ha.2⟩⟩
  obtain ⟨δ'', hδ'', hδ''V⟩ := h10 (W₀ j'').source (W₀ j'').open_source (hW₀ j'').2.2.1
  obtain ⟨-, -, hDs₁, hDn₁, -, -, -⟩ := hW₁ j'
  have hVo : IsOpen ((W₁ j').source ∩ W₁ j' ⁻¹' ball 0 (1 + δ'')) := (W₁ j').isOpen_inter_preimage isOpen_ball
  have hDV : F₁.D j' ⊆ (W₁ j').source ∩ W₁ j' ⁻¹' ball 0 (1 + δ'') := fun y hy =>
    ⟨hDs₁ hy, mem_ball_zero_iff.2 (by have := (hDn₁ y (hDs₁ hy)).1 hy; linarith)⟩
  obtain ⟨δ', hδ', hδ'V⟩ := h01 _ hVo hDV
  have hev : ∀ᶠ a in comap F₀.ι (𝓝 c₀), False := by
    filter_upwards [hcoll δ' hδ'] with a ha
    have h1 := hδ'V a ha.1 ha.2
    have h2 := hδ''V (f a) h1.1 (mem_ball_zero_iff.1 h1.2)
    rw [f.symm_apply_apply] at h2
    exact disjoint_left.1 (hdis₀ hne) h2 ha.1
  obtain ⟨_, hx⟩ := hev.exists
  exact hx

/-- **Boundary values at a hole.**  If `f` traps the hole `j` of `F₀` by the hole `j'` of `F₁` and `f⁻¹` traps `j'`
by `j`, then in the hole coordinates `f` is a `K`-q.c. map of a collar `A(1, R)` into `A(1, r₁ j')` satisfying the
end conditions of `s32w_qc_annulus_end_extends`; its continuous extension to the circle gives the limit of `f` at
every point `‖W₀ j c‖ = 1`, a point `‖W₁ j' c'‖ = 1`. -/
theorem s32w_se_hole_limit {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m) {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K)
    {W₀ : Fin m → OpenPartialHomeomorph F₀.X.carrier ℂ} {r₀ : Fin m → ℝ}
    (hW₀ : ∀ j, 1 < r₀ j ∧ (W₀ j).target = ball (0 : ℂ) (r₀ j) ∧ F₀.D j ⊆ (W₀ j).source ∧
        (∀ y ∈ (W₀ j).source, y ∈ F₀.D j ↔ ‖W₀ j y‖ ≤ 1) ∧
        (∀ y ∈ (W₀ j).source, y ∉ (↑F₀.P : Set F₀.X.carrier)) ∧
        (∀ y ∈ (W₀ j).source, y ∉ F₀.D j → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W₀ j) y) ∧
        (∀ w ∈ (W₀ j).target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W₀ j).symm w))
    (hdis₀ : Pairwise fun i j => Disjoint (W₀ i).source (W₀ j).source)
    {W₁ : Fin m → OpenPartialHomeomorph F₁.X.carrier ℂ} {r₁ : Fin m → ℝ}
    (hW₁ : ∀ j, 1 < r₁ j ∧ (W₁ j).target = ball (0 : ℂ) (r₁ j) ∧ F₁.D j ⊆ (W₁ j).source ∧
        (∀ y ∈ (W₁ j).source, y ∈ F₁.D j ↔ ‖W₁ j y‖ ≤ 1) ∧
        (∀ y ∈ (W₁ j).source, y ∉ (↑F₁.P : Set F₁.X.carrier)) ∧
        (∀ y ∈ (W₁ j).source, y ∉ F₁.D j → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W₁ j) y) ∧
        (∀ w ∈ (W₁ j).target, 1 < ‖w‖ → MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (W₁ j).symm w))
    (hdis₁ : Pairwise fun i j => Disjoint (W₁ i).source (W₁ j).source)
    {j j' : Fin m}
    (h01 : ∀ V : Set F₁.X.carrier, IsOpen V → F₁.D j' ⊆ V →
      ∃ δ > 0, ∀ a : S₀, F₀.ι a ∈ (W₀ j).source → ‖W₀ j (F₀.ι a)‖ < 1 + δ → F₁.ι (f a) ∈ V)
    (h10 : ∀ V : Set F₀.X.carrier, IsOpen V → F₀.D j ⊆ V →
      ∃ δ > 0, ∀ b : S, F₁.ι b ∈ (W₁ j').source → ‖W₁ j' (F₁.ι b)‖ < 1 + δ → F₀.ι (f.symm b) ∈ V)
    {c : F₀.X.carrier} (hcs : c ∈ (W₀ j).source) (hc1 : ‖W₀ j c‖ = 1) :
    ∃ c' ∈ (W₁ j').source, ‖W₁ j' c'‖ = 1 ∧ Tendsto (fun a => F₁.ι (f a)) (comap F₀.ι (𝓝 c)) (𝓝 c') := by
  classical
  obtain ⟨hr₀, ht₀, hDs₀, hDn₀, -, hWd₀, hWs₀⟩ := hW₀ j
  obtain ⟨hr₁, ht₁, hDs₁, hDn₁, -, hWd₁, hWs₁⟩ := hW₁ j'
  set α := W₀ j with hα
  set β := W₁ j' with hβ
  have hrange₀ : ∀ y ∈ α.source, (y ∈ range F₀.ι ↔ 1 < ‖α y‖) := fun y hy =>
    s32w_se_hole_range F₀ hW₀ hdis₀ j hy
  have hrange₁ : ∀ y ∈ β.source, (y ∈ range F₁.ι ↔ 1 < ‖β y‖) := fun y hy =>
    s32w_se_hole_range F₁ hW₁ hdis₁ j' hy
  -- the collar `A(1, R)` lands in the source of `β`
  obtain ⟨δ₁, hδ₁, hδ₁m⟩ := h01 β.source β.open_source hDs₁
  set R : ℝ := min (1 + δ₁) (r₀ j) with hR
  have hR1 : 1 < R := lt_min (by linarith) hr₀
  have hAt : ∀ z ∈ annulus 1 R, z ∈ α.target := fun z hz => by
    rw [ht₀, mem_ball_zero_iff]; exact lt_of_lt_of_le hz.2 (min_le_right _ _)
  have hAr : ∀ z ∈ annulus 1 R, α.symm z ∈ range F₀.ι := fun z hz =>
    (hrange₀ _ (α.map_target (hAt z hz))).2 (by rw [α.right_inv (hAt z hz)]; exact hz.1)
  set s : ℂ → S₀ := fun z => Function.invFun F₀.ι (α.symm z) with hsdef
  have hs : ∀ z ∈ annulus 1 R, F₀.ι (s z) = α.symm z := fun z hz => Function.invFun_eq (hAr z hz)
  have hsα : ∀ z ∈ annulus 1 R, α (F₀.ι (s z)) = z := fun z hz => by rw [hs z hz, α.right_inv (hAt z hz)]
  have hss : ∀ z ∈ annulus 1 R, F₀.ι (s z) ∈ α.source := fun z hz => by
    rw [hs z hz]; exact α.map_target (hAt z hz)
  have hmaps : ∀ z ∈ annulus 1 R, F₁.ι (f (s z)) ∈ β.source := fun z hz =>
    hδ₁m (s z) (hss z hz) (by rw [hsα z hz]; exact lt_of_lt_of_le hz.2 (min_le_left _ _))
  have hAo : IsOpen (annulus (1 : ℝ) R) :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hαh : ∀ y : S₀, F₀.ι y ∈ α.source →
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) α (F₀.ι y) ∧ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) α.symm (α (F₀.ι y)) := by
    intro y hy
    have h1 := (hrange₀ _ hy).1 (mem_range_self y)
    refine ⟨hWd₀ _ hy fun hD => ?_, hWs₀ _ (α.map_source hy) h1⟩
    have := (hDn₀ _ hy).1 hD
    linarith
  have hβh : ∀ y : S, F₁.ι y ∈ β.source →
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) β (F₁.ι y) ∧ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) β.symm (β (F₁.ι y)) := by
    intro y hy
    have h1 := (hrange₁ _ hy).1 (mem_range_self y)
    refine ⟨hWd₁ _ hy fun hD => ?_, hWs₁ _ (β.map_source hy) h1⟩
    have := (hDn₁ _ hy).1 hD
    linarith
  set h : ℂ → ℂ := fun z => β (F₁.ι (f (s z))) with hh
  have hK : IsKQC h (annulus 1 R) K :=
    s32w_se_coord_isKQC F₀.embedding F₀.holomorphic F₁.embedding F₁.holomorphic hf α β hαh hβh hAo hAt hs
      hmaps
  have hmapA : MapsTo h (annulus 1 R) (annulus 1 (r₁ j')) := by
    intro z hz
    refine ⟨(hrange₁ _ (hmaps z hz)).1 (mem_range_self _), ?_⟩
    have := β.map_source (hmaps z hz)
    rw [ht₁, mem_ball_zero_iff] at this
    exact this
  have hend : ∀ ε > 0, ∃ δ > 0, ∀ z ∈ annulus 1 R, ‖z‖ < 1 + δ → ‖h z‖ < 1 + ε := by
    intro ε hε
    have hVo : IsOpen (β.source ∩ β ⁻¹' ball 0 (1 + ε)) := β.isOpen_inter_preimage isOpen_ball
    have hDV : F₁.D j' ⊆ β.source ∩ β ⁻¹' ball 0 (1 + ε) := fun y hy =>
      ⟨hDs₁ hy, mem_ball_zero_iff.2 (by have := (hDn₁ y (hDs₁ hy)).1 hy; linarith)⟩
    obtain ⟨δ, hδ, hδV⟩ := h01 _ hVo hDV
    refine ⟨δ, hδ, fun z hz hzδ => ?_⟩
    have := hδV (s z) (hss z hz) (by rw [hsα z hz]; exact hzδ)
    exact mem_ball_zero_iff.1 this.2
  have hend' : ∀ δ > 0, ∃ ε > 0, ∀ w ∈ annulus 1 (r₁ j'), ‖w‖ < 1 + ε →
      ∃ z ∈ annulus 1 R, ‖z‖ < 1 + δ ∧ h z = w := by
    intro δ hδ
    set δ' : ℝ := min δ ((R - 1) / 2) with hδ'
    have hδ'0 : 0 < δ' := lt_min hδ (by linarith)
    have hVo : IsOpen (α.source ∩ α ⁻¹' ball 0 (1 + δ')) := α.isOpen_inter_preimage isOpen_ball
    have hDV : F₀.D j ⊆ α.source ∩ α ⁻¹' ball 0 (1 + δ') := fun y hy =>
      ⟨hDs₀ hy, mem_ball_zero_iff.2 (by have := (hDn₀ y (hDs₀ hy)).1 hy; linarith)⟩
    obtain ⟨ε, hε, hεV⟩ := h10 _ hVo hDV
    refine ⟨ε, hε, fun w hw hwε => ?_⟩
    have hwt : w ∈ β.target := by rw [ht₁, mem_ball_zero_iff]; exact hw.2
    obtain ⟨b, hb⟩ := (hrange₁ _ (β.map_target hwt)).2 (by rw [β.right_inv hwt]; exact hw.1)
    have hbs : F₁.ι b ∈ β.source := by rw [hb]; exact β.map_target hwt
    have hbw : β (F₁.ι b) = w := by rw [hb, β.right_inv hwt]
    have h1 := hεV b hbs (by rw [hbw]; exact hwε)
    set z := α (F₀.ι (f.symm b)) with hz
    have hz1 : 1 < ‖z‖ := (hrange₀ _ h1.1).1 (mem_range_self _)
    have hzδ : ‖z‖ < 1 + δ' := mem_ball_zero_iff.1 h1.2
    have hzR : z ∈ annulus 1 R := ⟨hz1, by have := min_le_right δ ((R - 1) / 2); linarith⟩
    refine ⟨z, hzR, by have := min_le_left δ ((R - 1) / 2); linarith, ?_⟩
    have hsz : s z = f.symm b := by
      apply F₀.embedding.injective
      rw [hs z hzR, hz, α.left_inv h1.1]
    show β (F₁.ι (f (s z))) = w
    rw [hsz, f.apply_symm_apply, hbw]
  obtain ⟨Fh, hFeq, hFc, hFS, -⟩ := s32w_qc_annulus_end_extends hR1 hr₁ hK hmapA hend hend'
  set ξ := α c with hξ
  have hξS : ξ ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.2 hc1
  have hw₀S : Fh ξ ∈ sphere (0 : ℂ) 1 := hFS ▸ mem_image_of_mem Fh hξS
  have hw₀1 : ‖Fh ξ‖ = 1 := mem_sphere_zero_iff_norm.1 hw₀S
  have hw₀t : Fh ξ ∈ β.target := by rw [ht₁, mem_ball_zero_iff, hw₀1]; exact hr₁
  refine ⟨β.symm (Fh ξ), β.map_target hw₀t, by rw [β.right_inv hw₀t, hw₀1], ?_⟩
  -- the limit along `comap ι (𝓝 c)`
  have hO : IsOpen (α.source ∩ α ⁻¹' ball 0 R) := α.isOpen_inter_preimage isOpen_ball
  have hcO : c ∈ α.source ∩ α ⁻¹' ball 0 R := ⟨hcs, mem_ball_zero_iff.2 (by rw [hc1]; exact hR1)⟩
  have hev : ∀ᶠ a in comap F₀.ι (𝓝 c), α (F₀.ι a) ∈ annulus 1 R ∧ F₀.ι a ∈ α.source := by
    refine mem_comap.2 ⟨_, hO.mem_nhds hcO, fun a ha => ⟨⟨(hrange₀ _ ha.1).1 (mem_range_self a), ?_⟩, ha.1⟩⟩
    exact mem_ball_zero_iff.1 ha.2
  have hz : Tendsto (fun a => α (F₀.ι a)) (comap F₀.ι (𝓝 c)) (𝓝[annulus 1 R ∪ sphere 0 1] ξ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨((α.continuousAt hcs).tendsto).comp tendsto_comap, ?_⟩
    filter_upwards [hev] with a ha
    exact Or.inl ha.1
  have hFt : Tendsto (fun a => Fh (α (F₀.ι a))) (comap F₀.ι (𝓝 c)) (𝓝 (Fh ξ)) :=
    (hFc ξ (Or.inr hξS)).tendsto.comp hz
  have hβt := ((β.continuousAt_symm hw₀t).tendsto).comp hFt
  refine hβt.congr' ?_
  filter_upwards [hev] with a ha
  have hsa : s (α (F₀.ι a)) = a := by
    apply F₀.embedding.injective
    rw [hs _ ha.1, α.left_inv ha.2]
  show β.symm (Fh (α (F₀.ι a))) = F₁.ι (f a)
  rw [hFeq ha.1]
  show β.symm (β (F₁.ι (f (s (α (F₀.ι a)))))) = F₁.ι (f a)
  rw [hsa, β.left_inv (by have := hmaps _ ha.1; rwa [hsa] at this)]

/-- The frontier of `ιd(S)` in the double consists of seam points and punctures. -/
theorem s32w_se_double_frontier {g n m : ℕ} (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd) {p : Xd.carrier} (hp : p ∈ frontier (range ιd)) :
    J p = p ∨ p ∈ (↑Pd : Set Xd.carrier) := by
  rw [hd.embedding.isOpen_range.frontier_eq] at hp
  obtain ⟨hcl, hnr⟩ := hp
  have hMo : IsOpen (range (J ∘ ιd)) := (J.isOpenMap.comp hd.embedding.isOpenMap).isOpen_range
  have hnm : p ∉ range (J ∘ ιd) := by
    intro h
    obtain ⟨y, hyM, a, rfl⟩ := mem_closure_iff.1 hcl _ hMo h
    exact disjoint_left.1 hd.disjoint (mem_range_self a) hyM
  have hcov : p ∈ range ιd ∪ range (J ∘ ιd) ∪ {x | J x = x} ∪ ↑Pd := hd.cover ▸ mem_univ p
  rcases hcov with ((h | h) | h) | h
  · exact (hnr h).elim
  · exact (hnm h).elim
  · exact Or.inl h
  · exact Or.inr h

/-- **Punctures of the double, forward**: at a puncture `p ∈ Pd` in the frontier of `ιd(S)`, `F.ι x` converges to
a puncture of `F` as `ιd x → p` (the endpoint map `s31pp_endpoints_exhaust`; the mirror endpoints are excluded since
their punctured neighbourhoods lie in the mirror half, `s31pp_endpoint_half`). -/
theorem s32w_se_double_puncture_fwd {g n m : ℕ} (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd) {p : Xd.carrier} (hpP : p ∈ (↑Pd : Set Xd.carrier))
    (hpf : p ∈ frontier (range ιd)) :
    ∃ c ∈ F.P, Tendsto F.ι (comap ιd (𝓝 p)) (𝓝 c) := by
  classical
  haveI : Nonempty S := inferInstance
  obtain ⟨e, -, het, -, -, hPd⟩ := s31pp_endpoints_exhaust F hd
  rw [hd.embedding.isOpen_range.frontier_eq] at hpf
  obtain ⟨hcl, hnr⟩ := hpf
  have hp' : p ∈ Pd := hpP
  rw [hPd] at hp'
  rcases Finset.mem_union.1 hp' with h | h
  · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h
    have hc : c.1 ∈ F.P := Finset.mem_coe.1 c.2
    obtain ⟨-, hlim⟩ := s31pp_endpoint_half F hd hc (het c)
    refine ⟨c.1, hc, ?_⟩
    have h1 : Tendsto ιd (comap ιd (𝓝 (e c))) (𝓝[≠] (e c)) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_comap, Eventually.of_forall fun a ha => hnr ⟨a, ha⟩⟩
    exact (hlim.comp h1).congr fun a => s31qr_halfReturn_image F hd a
  · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h
    exfalso
    have hc : c.1 ∈ F.P := Finset.mem_coe.1 c.2
    obtain ⟨hpunct, -⟩ := s31pp_endpoint_half F hd hc (het c)
    have hJJ : ∀ y, J (J y) = y := hd.involution.1
    have hJt : Tendsto J (𝓝[≠] (J (e c))) (𝓝[≠] (e c)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := (J.continuous.tendsto (J (e c))).mono_left (nhdsWithin_le_nhds (s := {J (e c)}ᶜ))
        rwa [hJJ] at this
      · filter_upwards [self_mem_nhdsWithin] with y hy hJy
        apply hy
        show y = J (e c)
        rw [← hJy, hJJ]
    have hev : ∀ᶠ y in 𝓝[≠] (J (e c)), J y ∈ range ιd := hJt.eventually hpunct
    have hfr : ∃ᶠ y in 𝓝[≠] (J (e c)), y ∈ range ιd := by
      rw [frequently_nhdsWithin_iff]
      refine (mem_closure_iff_frequently.1 hcl).mono fun y hy => ⟨hy, fun hyp => hnr ?_⟩
      rw [← mem_singleton_iff.1 hyp]; exact hy
    obtain ⟨y, hJy, hy⟩ := (hev.and_frequently hfr).exists
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, hb⟩ := hJy
    refine disjoint_left.1 hd.disjoint (mem_range_self a) ⟨b, ?_⟩
    show J (ιd b) = ιd a
    rw [hb, hJJ]

/-- **Punctures of `F`, backward**: as `F.ι x` tends to a puncture `c`, `ιd x` converges to a puncture of the double
in the frontier of `ιd(S)` (`s31pp_endpoints_exhaust`). -/
theorem s32w_se_double_puncture_bwd {g n m : ℕ} (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd) {c : F.X.carrier} (hc : c ∈ F.P) :
    ∃ p ∈ (↑Pd : Set Xd.carrier), p ∈ frontier (range ιd) ∧ Tendsto ιd (comap F.ι (𝓝 c)) (𝓝 p) := by
  classical
  haveI : Nonempty S := inferInstance
  obtain ⟨e, he, het, -, -, -⟩ := s31pp_endpoints_exhaust F hd
  set c' : (↑F.P : Set F.X.carrier) := ⟨c, Finset.mem_coe.2 hc⟩
  refine ⟨e c', Finset.mem_coe.2 (he c'), ?_, het c'⟩
  rw [hd.embedding.isOpen_range.frontier_eq]
  haveI := s31eg_puncture_neBot F hc
  exact ⟨mem_closure_of_tendsto (het c') (Eventually.of_forall fun a => mem_range_self a),
    (s31pp_endpoint_off_halves F hd hc (het c')).1⟩

/-- **Seam points, both directions.**  At a fixed point `p` of `J`, the collar map `κ` of `s31qi_collar_from_hd`
(chart of `F.X` along `ιd⁻¹`, continuous and injective on the closed half disc) gives the limit `c` of `F.ι` as
`ιd x → p`, a point of a hole circle.  Conversely, written in the hole coordinate `W j` and doubled across the unit
circle (`w ↦ 1 / w̄`), `κ` is a continuous injective map of a disc, hence open (invariance of domain); so points of
`ι(S)` near `c` come from points of the half disc near `0`, and `ιd x → p` as `F.ι x → c`. -/
theorem s32w_se_double_seam {g n m : ℕ} (hm : m ≠ 0) (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd) {p : Xd.carrier} (hp : J p = p) :
    ∃ c, c ∈ frontier (range F.ι) ∧ c ∉ (↑F.P : Set F.X.carrier) ∧
      Tendsto F.ι (comap ιd (𝓝 p)) (𝓝 c) ∧ Tendsto ιd (comap F.ι (𝓝 c)) (𝓝 p) := by
  classical
  obtain ⟨j, wc, r, hr, hpw, hw0, hwt, -, -, -, hup, -, hcol⟩ := s31qi_collar_from_hd F hm hd hp
  obtain ⟨x, hDs, Jd, hJd, hb, hJt, hDc, -⟩ := F.disc j
  obtain ⟨r', hr', -, κ, -, hκc, hκi, -, hκre, -, hκs⟩ := hcol x Jd hDs hJd hb hDc hJt
  set φ := chartAt ℂ x with hφ
  obtain ⟨W, rW, hW, hdis⟩ := s82td_hole_coordinates F
  obtain ⟨-, -, hDsW, hDnW, hPsW, -, -⟩ := hW j
  set H : Set ℂ := {z : ℂ | ‖z‖ < r' ∧ 0 ≤ z.im} with hH
  have h0H : (0 : ℂ) ∈ H := ⟨by simpa using hr', le_refl _⟩
  have hro : IsOpen (range F.ι) := F.embedding.isOpen_range
  -- values of `κ`
  have hκt : ∀ z ∈ H, κ z ∈ φ.target := by
    intro z hz
    rcases hz.2.lt_or_eq with hlt | heq
    · obtain ⟨s', -, hs'2, hs'3⟩ := hκs z hz.1 hlt
      rw [hs'3]; exact φ.map_source hs'2
    · exact hJt (frontier_subset_closure (hκre ⟨hz.1, heq.symm⟩))
  have hκD : ∀ z ∈ H, z.im = 0 → φ.symm (κ z) ∈ F.D j := by
    intro z hz hz0
    have h1 : κ z ∈ φ '' F.D j := by rw [hDc]; exact frontier_subset_closure (hκre ⟨hz.1, hz0⟩)
    obtain ⟨d, hd', hde⟩ := h1
    rw [← hde, φ.left_inv (hDs hd')]
    exact hd'
  have hκup : ∀ z, ‖z‖ < r' → 0 < z.im → ∃ s' : S, ιd s' = wc.symm z ∧ φ.symm (κ z) = F.ι s' := by
    intro z hz him
    obtain ⟨s', hs'1, hs'2, hs'3⟩ := hκs z hz him
    exact ⟨s', hs'1, by rw [hs'3, φ.left_inv hs'2]⟩
  set c := φ.symm (κ 0) with hc
  have hcD : c ∈ F.D j := hκD 0 h0H rfl
  have hcW : c ∈ (W j).source := hDsW hcD
  -- forward limit
  have hOp : wc.source ∩ wc ⁻¹' ball 0 r' ∈ 𝓝 p :=
    (wc.isOpen_inter_preimage isOpen_ball).mem_nhds ⟨hpw, by show wc p ∈ ball 0 r'; rw [hw0]; exact mem_ball_self hr'⟩
  have hfwd : Tendsto F.ι (comap ιd (𝓝 p)) (𝓝 c) := by
    have hev : ∀ᶠ a in comap ιd (𝓝 p), ιd a ∈ wc.source ∧ wc (ιd a) ∈ ball 0 r' :=
      mem_comap.2 ⟨_, hOp, fun a ha => ha⟩
    have h1 : Tendsto (fun a => wc (ιd a)) (comap ιd (𝓝 p)) (𝓝[H] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := ((wc.continuousAt hpw).tendsto).comp (tendsto_comap (f := ιd) (x := 𝓝 p))
        rwa [hw0] at this
      · filter_upwards [hev] with a ha
        exact ⟨mem_ball_zero_iff.1 ha.2, ((hup _ ha.1).2 (mem_range_self a)).le⟩
    have h3 : Tendsto (fun a => φ.symm (κ (wc (ιd a)))) (comap ιd (𝓝 p)) (𝓝 c) :=
      ((φ.continuousAt_symm (hκt 0 h0H)).tendsto).comp (((hκc 0 h0H).tendsto).comp h1)
    refine h3.congr' ?_
    filter_upwards [hev] with a ha
    obtain ⟨s', hs'1, hs'2⟩ := hκup _ (mem_ball_zero_iff.1 ha.2) ((hup _ ha.1).2 (mem_range_self a))
    have : s' = a := hd.embedding.injective (by rw [hs'1, wc.left_inv ha.1])
    rw [hs'2, this]
  -- `c` is a hole point
  have hpcl : p ∈ closure (range ιd) := by
    have : p ∈ {y | J y = y} := hp
    rw [hd.fixed_curves] at this
    exact frontier_subset_closure this.1
  have hnb : NeBot (comap ιd (𝓝 p)) := by
    refine comap_neBot_iff.2 fun t ht => ?_
    obtain ⟨y, hyt, a, rfl⟩ := mem_closure_iff_nhds.1 hpcl t ht
    exact ⟨a, hyt⟩
  have hcfr : c ∈ frontier (range F.ι) := by
    rw [hro.frontier_eq]
    refine ⟨mem_closure_of_tendsto hfwd (Eventually.of_forall fun a => mem_range_self a), fun hcr => ?_⟩
    rw [F.range_ι] at hcr
    exact hcr (Or.inr (mem_iUnion.2 ⟨j, hcD⟩))
  have hcP : c ∉ (↑F.P : Set F.X.carrier) := hPsW c hcW
  have hW1 : ∀ y ∈ F.D j, y ∈ frontier (range F.ι) → ‖W j y‖ = 1 := by
    intro y hyD hyf
    obtain ⟨j₂, hy₂, hy1⟩ := (s32w_se_hole_frontier F hW hdis (fun hyP => disjoint_left.1 (F.disjoint_P j) hyD hyP)).1 hyf
    by_cases hjj : j₂ = j
    · rw [← hjj]; exact hy1
    · exact (disjoint_left.1 (hdis hjj) hy₂ (hDsW hyD)).elim
  refine ⟨c, hcfr, hcP, hfwd, ?_⟩
  -- the hole coordinate along `κ`
  set κt : ℂ → ℂ := fun z => W j (φ.symm (κ z)) with hκtdef
  have hcont0 : ContinuousWithinAt (fun z => φ.symm (κ z)) H 0 :=
    (φ.continuousAt_symm (hκt 0 h0H)).comp_continuousWithinAt (hκc 0 h0H)
  obtain ⟨ε₀, hε₀, hε₀s⟩ := Metric.mem_nhdsWithin_iff.1
    (hcont0.preimage_mem_nhdsWithin ((W j).open_source.mem_nhds hcW))
  set ρ : ℝ := min ε₀ r' with hρ
  have hρ0 : 0 < ρ := lt_min hε₀ hr'
  set Hρ : Set ℂ := {z : ℂ | ‖z‖ < ρ ∧ 0 ≤ z.im} with hHρ
  have hHρH : Hρ ⊆ H := fun z hz => ⟨lt_of_lt_of_le hz.1 (min_le_right _ _), hz.2⟩
  have hsrc : ∀ z ∈ Hρ, φ.symm (κ z) ∈ (W j).source := fun z hz =>
    hε₀s ⟨mem_ball_zero_iff.2 (lt_of_lt_of_le hz.1 (min_le_left _ _)), hHρH hz⟩
  have hκtc : ContinuousOn κt Hρ := by
    intro z hz
    exact ((W j).continuousAt (hsrc z hz)).comp_continuousWithinAt (f := fun z => φ.symm (κ z))
      (((φ.continuousAt_symm (hκt z (hHρH hz))).comp_continuousWithinAt (hκc z (hHρH hz))).mono hHρH)
  have hup1 : ∀ z ∈ Hρ, 0 < z.im → 1 < ‖κt z‖ := by
    intro z hz him
    obtain ⟨s', -, hs'2⟩ := hκup z (hHρH hz).1 him
    have h1 := hsrc z hz
    show 1 < ‖W j (φ.symm (κ z))‖
    rw [hs'2] at h1 ⊢
    exact (s32w_se_hole_range F hW hdis j h1).1 (mem_range_self s')
  have hre1 : ∀ z ∈ Hρ, z.im = 0 → ‖κt z‖ = 1 := by
    intro z hz hz0
    have hle : ‖κt z‖ ≤ 1 := ((hDnW _ (hsrc z hz)).1 (hκD z (hHρH hz) hz0))
    refine le_antisymm hle ?_
    have ht : Tendsto (fun τ : ℝ => z + (τ : ℂ) * I) (𝓝[>] (0 : ℝ)) (𝓝[Hρ] z) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun τ : ℝ => z + (τ : ℂ) * I) (𝓝 (0 : ℝ)) (𝓝 (z + ((0 : ℝ) : ℂ) * I)) :=
          tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto 0).mul tendsto_const_nhds)
        simpa using this.mono_left nhdsWithin_le_nhds
      · have hzρ : ‖z‖ < ρ := hz.1
        have hlt : ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ), τ < ρ - ‖z‖ :=
          nhdsWithin_le_nhds (gt_mem_nhds (by linarith))
        filter_upwards [hlt, self_mem_nhdsWithin] with τ hτ hτ0
        have hτ0' : (0 : ℝ) < τ := hτ0
        refine ⟨?_, by simp [hz0, hτ0'.le]⟩
        calc ‖z + (τ : ℂ) * I‖ ≤ ‖z‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
          _ = ‖z‖ + τ := by rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
              Real.norm_of_nonneg hτ0'.le]
          _ < ρ := by linarith
    have hlim : Tendsto (fun τ : ℝ => ‖κt (z + (τ : ℂ) * I)‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖κt z‖) :=
      ((hκtc z hz).tendsto.comp ht).norm
    refine ge_of_tendsto hlim ?_
    filter_upwards [ht.eventually self_mem_nhdsWithin, self_mem_nhdsWithin] with τ hτ hτ0
    refine (hup1 _ hτ ?_).le
    have hτ0' : (0 : ℝ) < τ := hτ0
    simpa [hz0] using hτ0'
  have hκtne : ∀ z ∈ Hρ, κt z ≠ 0 := by
    intro z hz h0
    rcases hz.2.lt_or_eq with hlt | heq
    · have := hup1 z hz hlt; rw [h0, norm_zero] at this; linarith
    · have := hre1 z hz heq.symm; rw [h0, norm_zero] at this; linarith
  -- the doubled map
  set κh : ℂ → ℂ := fun z => if 0 ≤ z.im then κt z else (conj (κt (conj z)))⁻¹ with hκh
  have hconjH : ∀ z ∈ ball (0 : ℂ) ρ, z.im ≤ 0 → conj z ∈ Hρ := fun z hz hz0 =>
    ⟨by rw [Complex.norm_conj]; exact mem_ball_zero_iff.1 hz, by rw [Complex.conj_im]; linarith⟩
  have hκhc : ContinuousOn κh (ball 0 ρ) := by
    refine ContinuousOn.if ?_ ?_ ?_
    · rintro z ⟨hz, hzf⟩
      rw [Complex.frontier_setOfPred_le_im] at hzf
      have hz0 : z.im = 0 := hzf
      have hzc : conj z = z := Complex.conj_eq_iff_im.2 hz0
      have hzH : z ∈ Hρ := ⟨mem_ball_zero_iff.1 hz, hz0.symm.le⟩
      show κt z = (conj (κt (conj z)))⁻¹
      rw [hzc, s82td_conj_eq_inv (hre1 z hzH hz0), inv_inv]
    · refine hκtc.mono ?_
      rintro z ⟨hz, hzc⟩
      have : 0 ≤ z.im := by
        have hcl : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
        rw [hcl.closure_eq] at hzc; exact hzc
      exact ⟨mem_ball_zero_iff.1 hz, this⟩
    · have hsub : ball (0 : ℂ) ρ ∩ closure {z : ℂ | ¬0 ≤ z.im} ⊆ ball 0 ρ ∩ {z : ℂ | z.im ≤ 0} := by
        rintro z ⟨hz, hzc⟩
        refine ⟨hz, ?_⟩
        have hcl : IsClosed {z : ℂ | z.im ≤ 0} := isClosed_le Complex.continuous_im continuous_const
        exact closure_minimal (fun w hw => le_of_lt (not_le.1 hw)) hcl hzc
      refine ContinuousOn.mono ?_ hsub
      intro z hz
      have hzH := hconjH z hz.1 hz.2
      have h1 : ContinuousWithinAt (fun w => κt (conj w)) (ball 0 ρ ∩ {z : ℂ | z.im ≤ 0}) z :=
        (hκtc (conj z) hzH).comp Complex.continuous_conj.continuousWithinAt
          (fun w hw => hconjH w hw.1 hw.2)
      have h2 : ContinuousWithinAt (fun w => conj (κt (conj w))) (ball 0 ρ ∩ {z : ℂ | z.im ≤ 0}) z :=
        Complex.continuous_conj.continuousAt.comp_continuousWithinAt h1
      exact h2.inv₀ (by rw [map_ne_zero]; exact hκtne _ hzH)
  -- norms of the doubled map
  have hnorm : ∀ z ∈ ball (0 : ℂ) ρ, (0 < z.im → 1 < ‖κh z‖) ∧ (z.im = 0 → ‖κh z‖ = 1) ∧
      (z.im < 0 → ‖κh z‖ < 1) := by
    intro z hz
    have hzρ := mem_ball_zero_iff.1 hz
    refine ⟨fun him => ?_, fun him => ?_, fun him => ?_⟩
    · show 1 < ‖if 0 ≤ z.im then κt z else (conj (κt (conj z)))⁻¹‖
      rw [if_pos him.le]; exact hup1 z ⟨hzρ, him.le⟩ him
    · show ‖if 0 ≤ z.im then κt z else (conj (κt (conj z)))⁻¹‖ = 1
      rw [if_pos him.symm.le]; exact hre1 z ⟨hzρ, him.symm.le⟩ him
    · show ‖if 0 ≤ z.im then κt z else (conj (κt (conj z)))⁻¹‖ < 1
      rw [if_neg (not_le.2 him), norm_inv, Complex.norm_conj]
      have := hup1 (conj z) (hconjH z hz him.le) (by rw [Complex.conj_im]; linarith)
      exact inv_lt_one_of_one_lt₀ this
  have hκtinj : InjOn κt Hρ := by
    intro z₁ h₁ z₂ h₂ he
    have e1 := (W j).injOn (hsrc z₁ h₁) (hsrc z₂ h₂) he
    have e2 := φ.symm.injOn (hκt z₁ (hHρH h₁)) (hκt z₂ (hHρH h₂)) e1
    exact hκi (hHρH h₁) (hHρH h₂) e2
  have hκhinj : InjOn κh (ball 0 ρ) := by
    intro z₁ h₁ z₂ h₂ he
    have n1 := hnorm z₁ h₁
    have n2 := hnorm z₂ h₂
    rcases le_or_gt 0 z₁.im with i1 | i1 <;> rcases le_or_gt 0 z₂.im with i2 | i2
    · have he' : κt z₁ = κt z₂ := by
        have := he; simp only [hκh, if_pos i1, if_pos i2] at this; exact this
      exact hκtinj ⟨mem_ball_zero_iff.1 h₁, i1⟩ ⟨mem_ball_zero_iff.1 h₂, i2⟩ he'
    · exfalso
      have a2 := n2.2.2 i2
      rcases i1.lt_or_eq with i1' | i1'
      · have := n1.1 i1'; rw [he] at this; linarith
      · have := n1.2.1 i1'.symm; rw [he] at this; linarith
    · exfalso
      have a1 := n1.2.2 i1
      rcases i2.lt_or_eq with i2' | i2'
      · have := n2.1 i2'; rw [← he] at this; linarith
      · have := n2.2.1 i2'.symm; rw [← he] at this; linarith
    · have he' : (conj (κt (conj z₁)))⁻¹ = (conj (κt (conj z₂)))⁻¹ := by
        have := he; simp only [hκh, if_neg (not_le.2 i1), if_neg (not_le.2 i2)] at this; exact this
      rw [inv_inj, (RingHom.injective _).eq_iff] at he'
      have := hκtinj (hconjH z₁ h₁ i1.le) (hconjH z₂ h₂ i2.le) he'
      simpa using congrArg conj this
  have hopen : ∀ ε, 0 < ε → ε ≤ ρ → IsOpen (κh '' ball 0 ε) := fun ε _ hερ =>
    isOpen_image_of_continuousOn_injOn isOpen_ball (hκhc.mono (ball_subset_ball hερ))
      (hκhinj.mono (ball_subset_ball hερ))
  have hκh0 : κh 0 = W j c := by
    show (if 0 ≤ (0 : ℂ).im then κt 0 else (conj (κt (conj 0)))⁻¹) = W j c
    rw [if_pos (show (0 : ℝ) ≤ (0 : ℂ).im by simp)]
  -- the backward limit
  rw [_root_.tendsto_nhds]
  intro O hO hpO
  have hwp : wc.symm 0 = p := by rw [← hw0, wc.left_inv hpw]
  have h0t : (0 : ℂ) ∈ wc.target := by rw [hwt]; exact mem_ball_self hr
  obtain ⟨ε, hε, hεO⟩ := Metric.mem_nhds_iff.1
    ((wc.continuousAt_symm h0t).preimage_mem_nhds (by rw [hwp]; exact hO.mem_nhds hpO))
  set ε' : ℝ := min ε ρ with hε'
  have hε'0 : 0 < ε' := lt_min hε hρ0
  have hN := hopen ε' hε'0 (min_le_right _ _)
  have hQ : (W j).source ∩ W j ⁻¹' (κh '' ball 0 ε') ∈ 𝓝 c :=
    ((W j).isOpen_inter_preimage hN).mem_nhds ⟨hcW, ⟨0, mem_ball_self hε'0, hκh0⟩⟩
  refine mem_comap.2 ⟨_, hQ, fun a ha => ?_⟩
  obtain ⟨has, z, hz, hza⟩ := ha
  have hzρ : z ∈ ball (0 : ℂ) ρ := ball_subset_ball (min_le_right _ _) hz
  have h1 : 1 < ‖W j (F.ι a)‖ := (s32w_se_hole_range F hW hdis j has).1 (mem_range_self a)
  have him : 0 < z.im := by
    rcases lt_trichotomy 0 z.im with h | h | h
    · exact h
    · have := (hnorm z hzρ).2.1 h.symm; rw [hza] at this; linarith
    · have := (hnorm z hzρ).2.2 h; rw [hza] at this; linarith
  have hzr' : ‖z‖ < r' := lt_of_lt_of_le (mem_ball_zero_iff.1 hzρ) (min_le_right _ _)
  have hzH : z ∈ Hρ := ⟨mem_ball_zero_iff.1 hzρ, him.le⟩
  have hκz : κh z = κt z := by
    show (if 0 ≤ z.im then κt z else (conj (κt (conj z)))⁻¹) = κt z
    rw [if_pos him.le]
  rw [hκz] at hza
  have he : φ.symm (κ z) = F.ι a := (W j).injOn (hsrc z hzH) has hza
  obtain ⟨s', hs'1, hs'2⟩ := hκup z hzr' him
  have : s' = a := F.embedding.injective (by rw [← hs'2, he])
  rw [← this]
  show ιd s' ∈ O
  rw [hs'1]
  exact hεO (ball_subset_ball (min_le_left _ _) hz)

/-- A cluster point `p` of `u` along `L` makes `L ⊓ comap u (𝓝 p)` nontrivial. -/
theorem s32w_se_inf_comap_neBot {α β : Type*} [TopologicalSpace β] {L : Filter α} {u : α → β} {p : β}
    (h : MapClusterPt p L u) : NeBot (L ⊓ comap u (𝓝 p)) := by
  refine Filter.inf_neBot_iff.2 fun s hs t ht => ?_
  obtain ⟨t', ht', htt'⟩ := mem_comap.1 ht
  obtain ⟨a, has, hat⟩ := ((mapClusterPt_iff_frequently.1 h t' ht').and_eventually hs).exists
  exact ⟨a, hat, htt' has⟩

/-- **Hole circles, backward**: for a point `c` of a hole circle of `F`, `ιd x` converges to a seam point as
`F.ι x → c` (a cluster point of `ιd` lies on the frontier of `ιd(S)`; a puncture is excluded by
`s32w_se_double_puncture_fwd`, and at a seam point `s32w_se_double_seam` identifies the limit). -/
theorem s32w_se_double_hole_bwd {g n m : ℕ} (hm : m ≠ 0) (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd) {c : F.X.carrier} (hcf : c ∈ frontier (range F.ι))
    (hcP : c ∉ (↑F.P : Set F.X.carrier)) :
    ∃ p, J p = p ∧ Tendsto ιd (comap F.ι (𝓝 c)) (𝓝 p) := by
  rw [F.embedding.isOpen_range.frontier_eq] at hcf
  obtain ⟨hcl, hcr⟩ := hcf
  have hnb : NeBot (comap F.ι (𝓝 c)) := by
    refine comap_neBot_iff.2 fun t ht => ?_
    obtain ⟨y, hyt, a, rfl⟩ := mem_closure_iff_nhds.1 hcl t ht
    exact ⟨a, hyt⟩
  obtain ⟨p, hp⟩ := exists_clusterPt_of_compactSpace (map ιd (comap F.ι (𝓝 c)))
  have hmc : MapClusterPt p (comap F.ι (𝓝 c)) ιd := hp
  have hpr : p ∉ range ιd := s31eg_cluster_missing F.ι ιd F.embedding.continuous hd.embedding hcr hp
  have hpcl : p ∈ closure (range ιd) := by
    refine mem_closure_iff_nhds.2 fun t ht => ?_
    obtain ⟨a, ha⟩ := (mapClusterPt_iff_frequently.1 hmc t ht).exists
    exact ⟨ιd a, ha, mem_range_self a⟩
  have hpf : p ∈ frontier (range ιd) := by
    rw [hd.embedding.isOpen_range.frontier_eq]; exact ⟨hpcl, hpr⟩
  haveI hG := s32w_se_inf_comap_neBot hmc
  have hL : Tendsto F.ι (comap F.ι (𝓝 c) ⊓ comap ιd (𝓝 p)) (𝓝 c) := tendsto_comap.mono_left inf_le_left
  rcases s32w_se_double_frontier F hd hpf with hJ | hPd
  · obtain ⟨c', -, -, hfwd, hbwd⟩ := s32w_se_double_seam hm F hd hJ
    have hcc : c = c' := tendsto_nhds_unique hL (hfwd.mono_left inf_le_right)
    exact ⟨p, hJ, hcc ▸ hbwd⟩
  · obtain ⟨c', hc'P, hlim⟩ := s32w_se_double_puncture_fwd F hd hPd hpf
    have hcc : c = c' := tendsto_nhds_unique hL (hlim.mono_left inf_le_right)
    exact (hcP (hcc ▸ Finset.mem_coe.2 hc'P)).elim

/-- **[stub a] End dictionary of a Schottky double.**  Every point `p` of the frontier of `ιd(S)` in the double (a seam
point or a puncture) is the limit point of an end of `ι(S)` in `F.X`: there is `c` in the frontier of `ι(S)` with
`F.ι x → c` as `ιd x → p`, and conversely every `c` has such a `p` with `ιd x → p` as `F.ι x → c`; seam points
(`J p = p`) correspond to the hole circles (`c ∉ F.P`), the punctures of the double to the punctures. -/
theorem s32w_se_double_dictionary {g n m : ℕ} (hm : m ≠ 0) (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd) :
    (∀ p ∈ frontier (range ιd), ∃ c ∈ frontier (range F.ι),
      Tendsto F.ι (comap ιd (𝓝 p)) (𝓝 c) ∧ (J p = p ↔ c ∉ (↑F.P : Set F.X.carrier))) ∧
    (∀ c ∈ frontier (range F.ι), ∃ p ∈ frontier (range ιd),
      Tendsto ιd (comap F.ι (𝓝 c)) (𝓝 p) ∧ (J p = p ↔ c ∉ (↑F.P : Set F.X.carrier))) := by
  have hPdJ : ∀ p ∈ (↑Pd : Set Xd.carrier), J p ≠ p := by
    intro p hp hJ
    have : p ∈ {x | J x = x} := hJ
    rw [hd.fixed_curves] at this
    exact this.2 hp
  have hJfr : ∀ p, J p = p → p ∈ frontier (range ιd) := by
    intro p hJ
    have : p ∈ {x | J x = x} := hJ
    rw [hd.fixed_curves] at this
    exact this.1
  constructor
  · intro p hpf
    rcases s32w_se_double_frontier F hd hpf with hJ | hPd
    · obtain ⟨c, hcf, hcP, hfwd, -⟩ := s32w_se_double_seam hm F hd hJ
      exact ⟨c, hcf, hfwd, iff_of_true hJ hcP⟩
    · obtain ⟨c, hcP, hlim⟩ := s32w_se_double_puncture_fwd F hd hPd hpf
      exact ⟨c, s32w_se_puncture_frontier F hcP, hlim,
        iff_of_false (hPdJ p hPd) fun h => h (Finset.mem_coe.2 hcP)⟩
  · intro c hcf
    by_cases hcP : c ∈ (↑F.P : Set F.X.carrier)
    · obtain ⟨p, hpPd, hpf, hlim⟩ := s32w_se_double_puncture_bwd F hd (Finset.mem_coe.1 hcP)
      exact ⟨p, hpf, hlim, iff_of_false (hPdJ p hpPd) fun h => h hcP⟩
    · obtain ⟨p, hJ, hlim⟩ := s32w_se_double_hole_bwd hm F hd hcf hcP
      exact ⟨p, hJfr p hJ, hlim, iff_of_true hJ hcP⟩

/-- **[stub b] Ends under a quasiconformal map.**  A quasiconformal `f : S₀ → S` has a limit at every end of `ι(S₀)`
in `F₀.X`: for `c` in the frontier of `F₀.ι(S₀)` there is `c'` in the frontier of `F₁.ι(S)` with `F₁.ι (f x) → c'`
as `F₀.ι x → c`, and punctures go to punctures, hole circles to hole circles. -/
theorem s32w_se_qc_end_limits {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∀ c ∈ frontier (range F₀.ι), ∃ c' ∈ frontier (range F₁.ι),
      Tendsto (fun x => F₁.ι (f x)) (comap F₀.ι (𝓝 c)) (𝓝 c') ∧
        (c ∈ (↑F₀.P : Set F₀.X.carrier) ↔ c' ∈ (↑F₁.P : Set F₁.X.carrier)) := by
  intro c hc
  obtain ⟨K, hK⟩ := hf
  obtain ⟨W₀, r₀, hW₀, hdis₀⟩ := s82td_hole_coordinates F₀
  obtain ⟨W₁, r₁, hW₁, hdis₁⟩ := s82td_hole_coordinates F₁
  by_cases hcP : c ∈ (↑F₀.P : Set F₀.X.carrier)
  · obtain ⟨p', hp', hlim⟩ := s32w_se_puncture_limit F₀ F₁ hK hcP
    exact ⟨p', s32w_se_puncture_frontier F₁ hp', hlim, iff_of_true hcP hp'⟩
  · obtain ⟨j, hcs, hc1⟩ := (s32w_se_hole_frontier F₀ hW₀ hdis₀ hcP).1 hc
    obtain ⟨j', h01⟩ := s32w_se_hole_target F₀ F₁ hK hW₀ hdis₀ j
    obtain ⟨j'', h10⟩ := s32w_se_hole_target F₁ F₀ (s29_m_isKQCRS_symm hK) hW₁ hdis₁ j'
    have hjj : j'' = j := s32w_se_hole_pair F₀ F₁ hW₀ hdis₀ hW₁ h01 h10
    subst hjj
    obtain ⟨c', hc's, hc'1, hlim⟩ := s32w_se_hole_limit F₀ F₁ hK hW₀ hdis₀ hW₁ hdis₁ h01 h10 hcs hc1
    have hc'P : c' ∉ (↑F₁.P : Set F₁.X.carrier) := (hW₁ j').2.2.2.2.1 c' hc's
    exact ⟨c', (s32w_se_hole_frontier F₁ hW₁ hdis₁ hc'P).2 ⟨j', hc's, hc'1⟩, hlim, iff_of_false hcP hc'P⟩

/-- The mirror image of a puncture endpoint is not in the closure of `ιd(S)`: the punctured neighbourhoods of the
endpoint lie in `ιd(S)` (`s31pp_endpoint_half`), so those of its mirror lie in the mirror half. -/
theorem s32w_se_mirror_endpoint {g n m : ℕ} (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd) {c : F.X.carrier} (hc : c ∈ F.P) {q : Xd.carrier}
    (hq : Tendsto ιd (comap F.ι (𝓝 c)) (𝓝 q)) : J q ∉ closure (range ιd) := by
  haveI : Nonempty S := inferInstance
  intro hcl
  obtain ⟨hpunct, -⟩ := s31pp_endpoint_half F hd hc hq
  have hJJ : ∀ y, J (J y) = y := hd.involution.1
  have hnr : J q ∉ range ιd := by
    rintro ⟨a, ha⟩
    have hoff := (s31pp_endpoint_off_halves F hd hc hq).2
    exact hoff ⟨a, by show J (ιd a) = q; rw [ha, hJJ]⟩
  have hJt : Tendsto J (𝓝[≠] (J q)) (𝓝[≠] q) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := (J.continuous.tendsto (J q)).mono_left (nhdsWithin_le_nhds (s := {J q}ᶜ))
      rwa [hJJ] at this
    · filter_upwards [self_mem_nhdsWithin] with y hy hJy
      apply hy
      show y = J q
      rw [← hJy, hJJ]
  have hev : ∀ᶠ y in 𝓝[≠] (J q), J y ∈ range ιd := hJt.eventually hpunct
  have hfr : ∃ᶠ y in 𝓝[≠] (J q), y ∈ range ιd := by
    rw [frequently_nhdsWithin_iff]
    refine (mem_closure_iff_frequently.1 hcl).mono fun y hy => ⟨hy, fun hyp => hnr ?_⟩
    rw [← mem_singleton_iff.1 hyp]; exact hy
  obtain ⟨y, hJy, hy⟩ := (hev.and_frequently hfr).exists
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨b, hb⟩ := hJy
  refine disjoint_left.1 hd.disjoint (mem_range_self a) ⟨b, ?_⟩
  show J (ιd b) = ιd a
  rw [hb, hJJ]

/-- The two closed halves `closure ιd(S)` and its mirror cover the double and meet only on the seam. -/
theorem s32w_se_double_halves {g n m : ℕ} (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd) :
    (∀ y, y ∈ closure (range ιd) ∨ J y ∈ closure (range ιd)) ∧
      ∀ y, y ∈ closure (range ιd) → J y ∈ closure (range ιd) → J y = y := by
  classical
  haveI : Nonempty S := inferInstance
  have hJJ : ∀ y, J (J y) = y := hd.involution.1
  obtain ⟨e, -, het, -, -, hPd⟩ := s31pp_endpoints_exhaust F hd
  have hecl : ∀ c, e c ∈ closure (range ιd) := by
    intro c
    haveI := s31eg_puncture_neBot F (Finset.mem_coe.1 c.2)
    exact mem_closure_of_tendsto (het c) (Eventually.of_forall fun a => mem_range_self a)
  have hMo : IsOpen (range (J ∘ ιd)) := (J.isOpenMap.comp hd.embedding.isOpenMap).isOpen_range
  have hMcl : ∀ y ∈ range (J ∘ ιd), y ∉ closure (range ιd) := by
    intro y hy hcl
    obtain ⟨z, hzM, a, rfl⟩ := mem_closure_iff.1 hcl _ hMo hy
    exact disjoint_left.1 hd.disjoint (mem_range_self a) hzM
  refine ⟨fun y => ?_, fun y hy hJy => ?_⟩
  · have hcov : y ∈ range ιd ∪ range (J ∘ ιd) ∪ {x | J x = x} ∪ ↑Pd := hd.cover ▸ mem_univ y
    rcases hcov with ((h | h) | h) | h
    · exact Or.inl (subset_closure h)
    · obtain ⟨a, rfl⟩ := h
      right
      show J (J (ιd a)) ∈ closure (range ιd)
      rw [hJJ]; exact subset_closure (mem_range_self a)
    · left
      have : y ∈ {x | J x = x} := h
      rw [hd.fixed_curves] at this
      exact frontier_subset_closure this.1
    · have h' : y ∈ Pd := h
      rw [hPd] at h'
      rcases Finset.mem_union.1 h' with h1 | h1
      · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h1
        exact Or.inl (hecl c)
      · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h1
        right
        show J (J (e c)) ∈ closure (range ιd)
        rw [hJJ]; exact hecl c
  · have hyr : y ∉ range ιd := by
      rintro ⟨a, rfl⟩
      exact hMcl (J (ιd a)) ⟨a, rfl⟩ hJy
    have hJyr : J y ∉ range ιd := by
      rintro ⟨a, ha⟩
      exact hMcl y ⟨a, by show J (ιd a) = y; rw [ha, hJJ]⟩ hy
    have hfr : y ∈ frontier (range ιd) := by
      rw [hd.embedding.isOpen_range.frontier_eq]; exact ⟨hy, hyr⟩
    rcases s32w_se_double_frontier F hd hfr with hJ | hP
    · exact hJ
    · exfalso
      have h' : y ∈ Pd := hP
      rw [hPd] at h'
      rcases Finset.mem_union.1 h' with h1 | h1
      · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h1
        exact s32w_se_mirror_endpoint F hd (Finset.mem_coe.1 c.2) (het c) hJy
      · obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 h1
        exact s32w_se_mirror_endpoint F hd (Finset.mem_coe.1 c.2) (het c) hy

/-- **Extension by limits** of `ιd₁ ∘ f ∘ ιd₀⁻¹` to the closed half `closure ιd₀(S₀)` (stubs a, b): continuous, with
the frontier of `ιd₀(S₀)` going to the frontier of `ιd₁(S)`, seam points to seam points. -/
theorem s32w_se_half_ext {g n m : ℕ} (hm : m ≠ 0) (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∃ G : Xd₀.carrier → Xd₁.carrier, (∀ a, G (ιd₀ a) = ιd₁ (f a)) ∧ ContinuousOn G (closure (range ιd₀)) ∧
      ∀ p ∈ frontier (range ιd₀), G p ∈ frontier (range ιd₁) ∧ (J₀ p = p ↔ J₁ (G p) = G p) := by
  classical
  haveI : Nonempty S₀ := inferInstance
  set φ₀ : Xd₀.carrier → Xd₁.carrier := fun y => ιd₁ (f (Function.invFun ιd₀ y)) with hφ₀
  have hφ : ∀ a, φ₀ (ιd₀ a) = ιd₁ (f a) := fun a => by
    simp only [hφ₀, Function.leftInverse_invFun hd₀.embedding.injective a]
  have hnw : ∀ p, 𝓝[range ιd₀] p = map ιd₀ (comap ιd₀ (𝓝 p)) := fun p => (map_comap (𝓝 p) ιd₀).symm
  have htend : ∀ {p : Xd₀.carrier} {q : Xd₁.carrier},
      Tendsto (fun a => ιd₁ (f a)) (comap ιd₀ (𝓝 p)) (𝓝 q) → Tendsto φ₀ (𝓝[range ιd₀] p) (𝓝 q) := by
    intro p q h
    rw [hnw, tendsto_map'_iff]
    exact h.congr fun a => (hφ a).symm
  have hdict₀ := s32w_se_double_dictionary hm F₀ hd₀
  have hdict₁ := s32w_se_double_dictionary hm F₁ hd₁
  have hends := s32w_se_qc_end_limits F₀ F₁ f hf
  -- limits at the frontier
  have hfr : ∀ p ∈ frontier (range ιd₀), ∃ q ∈ frontier (range ιd₁),
      Tendsto (fun a => ιd₁ (f a)) (comap ιd₀ (𝓝 p)) (𝓝 q) ∧ (J₀ p = p ↔ J₁ q = q) := by
    intro p hp
    obtain ⟨c, hc, hl1, hf1⟩ := hdict₀.1 p hp
    obtain ⟨c', hc', hl2, hf2⟩ := hends c hc
    obtain ⟨q, hq, hl3, hf3⟩ := hdict₁.2 c' hc'
    refine ⟨q, hq, ?_, hf1.trans ((not_congr hf2).trans hf3.symm)⟩
    have h1 : Tendsto (fun a => a) (comap ιd₀ (𝓝 p)) (comap F₀.ι (𝓝 c)) := tendsto_comap_iff.2 hl1
    have h2 : Tendsto f (comap F₀.ι (𝓝 c)) (comap F₁.ι (𝓝 c')) := tendsto_comap_iff.2 hl2
    exact hl3.comp (h2.comp h1)
  have hin : ∀ a, Tendsto (fun a => ιd₁ (f a)) (comap ιd₀ (𝓝 (ιd₀ a))) (𝓝 (ιd₁ (f a))) := by
    intro a
    rw [← hd₀.embedding.isInducing.nhds_eq_comap]
    exact (hd₁.embedding.continuous.comp f.continuous).tendsto a
  have hall : ∀ x ∈ closure (range ιd₀), ∃ y, Tendsto φ₀ (𝓝[range ιd₀] x) (𝓝 y) := by
    intro x hx
    by_cases hxr : x ∈ range ιd₀
    · obtain ⟨a, rfl⟩ := hxr
      exact ⟨_, htend (hin a)⟩
    · have hxf : x ∈ frontier (range ιd₀) := by
        rw [hd₀.embedding.isOpen_range.frontier_eq]; exact ⟨hx, hxr⟩
      obtain ⟨q, -, hq, -⟩ := hfr x hxf
      exact ⟨q, htend hq⟩
  refine ⟨extendFrom (range ιd₀) φ₀, fun a => ?_, continuousOn_extendFrom subset_rfl hall, fun p hp => ?_⟩
  · exact extendFrom_eq (subset_closure (mem_range_self a)) (htend (hin a))
  · obtain ⟨q, hq, hql, hJ⟩ := hfr p hp
    rw [extendFrom_eq (frontier_subset_closure hp) (htend hql)]
    exact ⟨hq, hJ⟩

/-- **[stub c] Existence of the symmetric extension** (topological part): `f^d` is `ιd₁ ∘ f ∘ ιd₀⁻¹` on `ιd₀(S₀)`,
its limits (stubs a, b) on the frontier, and `J₁ ∘ f^d ∘ J₀` on the mirror half. -/
theorem s32w_se_exists {g n m : ℕ} (hm : m ≠ 0) (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∃ fd : Xd₀.carrier ≃ₜ Xd₁.carrier, IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd := by
  classical
  obtain ⟨G, hGι, hGc, hGfr⟩ := s32w_se_half_ext hm F₀ F₁ hd₀ hd₁ f hf
  obtain ⟨G', hG'ι, hG'c, hG'fr⟩ := s32w_se_half_ext hm F₁ F₀ hd₁ hd₀ f.symm (s28q_isQCRS_symm hf)
  obtain ⟨hcov₀, hov₀⟩ := s32w_se_double_halves F₀ hd₀
  obtain ⟨hcov₁, hov₁⟩ := s32w_se_double_halves F₁ hd₁
  have hJJ₀ : ∀ y, J₀ (J₀ y) = y := hd₀.involution.1
  have hJJ₁ : ∀ y, J₁ (J₁ y) = y := hd₁.involution.1
  set C₀ := closure (range ιd₀) with hC₀
  set C₁ := closure (range ιd₁) with hC₁
  have hfix₀ : ∀ y, J₀ y = y → y ∈ frontier (range ιd₀) := by
    intro y hy
    have : y ∈ {x | J₀ x = x} := hy
    rw [hd₀.fixed_curves] at this
    exact this.1
  have hfix₁ : ∀ y, J₁ y = y → y ∈ frontier (range ιd₁) := by
    intro y hy
    have : y ∈ {x | J₁ x = x} := hy
    rw [hd₁.fixed_curves] at this
    exact this.1
  have hGC : ∀ y ∈ C₀, G y ∈ C₁ := by
    intro y hy
    by_cases hyr : y ∈ range ιd₀
    · obtain ⟨a, rfl⟩ := hyr
      rw [hGι]; exact subset_closure (mem_range_self _)
    · have hyf : y ∈ frontier (range ιd₀) := by
        rw [hd₀.embedding.isOpen_range.frontier_eq]; exact ⟨hy, hyr⟩
      exact frontier_subset_closure (hGfr y hyf).1
  have hG'C : ∀ y ∈ C₁, G' y ∈ C₀ := by
    intro y hy
    by_cases hyr : y ∈ range ιd₁
    · obtain ⟨a, rfl⟩ := hyr
      rw [hG'ι]; exact subset_closure (mem_range_self _)
    · have hyf : y ∈ frontier (range ιd₁) := by
        rw [hd₁.embedding.isOpen_range.frontier_eq]; exact ⟨hy, hyr⟩
      exact frontier_subset_closure (hG'fr y hyf).1
  have hG'G : ∀ y ∈ C₀, G' (G y) = y := by
    have h : EqOn (fun y => G' (G y)) id C₀ := by
      refine Set.EqOn.of_subset_closure (s := range ιd₀) ?_ (hG'c.comp hGc hGC) continuousOn_id subset_closure
        subset_rfl
      rintro _ ⟨a, rfl⟩
      simp only [id, hGι, hG'ι, f.symm_apply_apply]
    exact fun y hy => h hy
  have hGG' : ∀ y ∈ C₁, G (G' y) = y := by
    have h : EqOn (fun y => G (G' y)) id C₁ := by
      refine Set.EqOn.of_subset_closure (s := range ιd₁) ?_ (hGc.comp hG'c hG'C) continuousOn_id subset_closure
        subset_rfl
      rintro _ ⟨a, rfl⟩
      simp only [id, hGι, hG'ι, f.apply_symm_apply]
    exact fun y hy => h hy
  have hGJ : ∀ y ∈ C₀, J₀ y ∈ C₀ → J₁ (G y) = G y := fun y hy hJy =>
    ((hGfr y (hfix₀ y (hov₀ y hy hJy))).2).1 (hov₀ y hy hJy)
  have hG'J : ∀ y ∈ C₁, J₁ y ∈ C₁ → J₀ (G' y) = G' y := fun y hy hJy =>
    ((hG'fr y (hfix₁ y (hov₁ y hy hJy))).2).1 (hov₁ y hy hJy)
  -- the glued maps
  set fd : Xd₀.carrier → Xd₁.carrier := fun y => if y ∈ C₀ then G y else J₁ (G (J₀ y)) with hfd
  set fd' : Xd₁.carrier → Xd₀.carrier := fun y => if y ∈ C₁ then G' y else J₀ (G' (J₁ y)) with hfd'
  have hfd1 : ∀ y ∈ C₀, fd y = G y := fun y hy => if_pos hy
  have hfd2 : ∀ y, J₀ y ∈ C₀ → fd y = J₁ (G (J₀ y)) := by
    intro y hJy
    by_cases hy : y ∈ C₀
    · rw [hfd1 y hy, hov₀ y hy hJy]
      exact (hGJ y hy hJy).symm
    · exact if_neg hy
  have hfd'1 : ∀ y ∈ C₁, fd' y = G' y := fun y hy => if_pos hy
  have hfd'2 : ∀ y, J₁ y ∈ C₁ → fd' y = J₀ (G' (J₁ y)) := by
    intro y hJy
    by_cases hy : y ∈ C₁
    · rw [hfd'1 y hy, hov₁ y hy hJy]
      exact (hG'J y hy hJy).symm
    · exact if_neg hy
  have hfdc : Continuous fd := by
    rw [← continuousOn_univ]
    have hU : C₀ ∪ J₀ ⁻¹' C₀ = univ := eq_univ_of_forall fun y => (hcov₀ y).elim Or.inl Or.inr
    rw [← hU]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_closure (isClosed_closure.preimage J₀.continuous)
    · exact hGc.congr fun y hy => hfd1 y hy
    · have : ContinuousOn (fun y => J₁ (G (J₀ y))) (J₀ ⁻¹' C₀) :=
        J₁.continuous.comp_continuousOn (hGc.comp J₀.continuous.continuousOn fun y hy => hy)
      exact this.congr fun y hy => hfd2 y hy
  have hfd'c : Continuous fd' := by
    rw [← continuousOn_univ]
    have hU : C₁ ∪ J₁ ⁻¹' C₁ = univ := eq_univ_of_forall fun y => (hcov₁ y).elim Or.inl Or.inr
    rw [← hU]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_closure (isClosed_closure.preimage J₁.continuous)
    · exact hG'c.congr fun y hy => hfd'1 y hy
    · have : ContinuousOn (fun y => J₀ (G' (J₁ y))) (J₁ ⁻¹' C₁) :=
        J₀.continuous.comp_continuousOn (hG'c.comp J₁.continuous.continuousOn fun y hy => hy)
      exact this.congr fun y hy => hfd'2 y hy
  have hleft : ∀ y, fd' (fd y) = y := by
    intro y
    rcases hcov₀ y with hy | hJy
    · rw [hfd1 y hy, hfd'1 _ (hGC y hy), hG'G y hy]
    · rw [hfd2 y hJy, hfd'2 _ (by rw [hJJ₁]; exact hGC _ hJy), hJJ₁, hG'G _ hJy, hJJ₀]
  have hright : ∀ y, fd (fd' y) = y := by
    intro y
    rcases hcov₁ y with hy | hJy
    · rw [hfd'1 y hy, hfd1 _ (hG'C y hy), hGG' y hy]
    · rw [hfd'2 y hJy, hfd2 _ (by rw [hJJ₀]; exact hG'C _ hJy), hJJ₀, hGG' _ hJy, hJJ₁]
  let fdh : Xd₀.carrier ≃ₜ Xd₁.carrier := ⟨⟨fd, fd', hleft, hright⟩, hfdc, hfd'c⟩
  have h1 : ∀ x, fdh (ιd₀ x) = ιd₁ (f x) := by
    intro x
    show fd (ιd₀ x) = ιd₁ (f x)
    rw [hfd1 _ (subset_closure (mem_range_self x)), hGι]
  have h2 : ∀ y, fdh (J₀ y) = J₁ (fdh y) := by
    intro y
    show fd (J₀ y) = J₁ (fd y)
    rcases hcov₀ y with hy | hJy
    · rw [hfd2 (J₀ y) (by rw [hJJ₀]; exact hy), hJJ₀, hfd1 y hy]
    · rw [hfd1 _ hJy, hfd2 y hJy, hJJ₁]
  exact ⟨fdh, (⟨h1, h2⟩ : (∀ x, fdh (ιd₀ x) = ιd₁ (f x)) ∧ ∀ y, fdh (J₀ y) = J₁ (fdh y))⟩

end LiZhongQC
