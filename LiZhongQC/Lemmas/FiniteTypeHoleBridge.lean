import LiZhongQC.Ch09.S31_FiniteType

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- A bounded univalent punctured-disc map has a holomorphic extension. Its
extension remains an open map on the disc: constancy is excluded by injectivity
on the infinite punctured disc. -/
theorem s31he_bounded_puncture_extension {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hd : DifferentiableOn ℂ f (ball c r \ {c}))
    (hi : InjOn f (ball c r \ {c}))
    (hb : BddAbove (norm ∘ f '' (ball c r \ {c}))) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c r) ∧
      EqOn g f (ball c r \ {c}) ∧ Tendsto f (𝓝[≠] c) (𝓝 (g c)) ∧
      ∀ V ⊆ ball c r, IsOpen V → IsOpen (g '' V) := by
  classical
  let g := Function.update f c (limUnder (𝓝[≠] c) f)
  have hg : DifferentiableOn ℂ g (ball c r) :=
    Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds c hr) hd hb
  have heq : EqOn g f (ball c r \ {c}) := by
    intro z hz
    exact Function.update_of_ne hz.2 _ _
  have ht : Tendsto f (𝓝[≠] c) (𝓝 (g c)) := by
    have h := continuousAt_update_same.1 (hg.continuousOn.continuousAt (ball_mem_nhds c hr))
    simpa only [g, Function.update_self] using h
  refine ⟨g, hg, heq, ht, ?_⟩
  rcases (hg.analyticOnNhd isOpen_ball).is_constant_or_isOpen isPreconnected_ball with hconst | hop
  · obtain ⟨v, hv⟩ := hconst
    obtain ⟨a, ha, b, hbb, hab⟩ :=
      ((infinite_of_mem_nhds c (ball_mem_nhds c hr)).sdiff (finite_singleton c)).nontrivial
    have he : f a = f b := by
      rw [← heq ha, ← heq hbb, hv a ha.1, hv b hbb.1]
    exact (hab (hi ha hbb he)).elim
  · exact hop

/-- A bounded univalent punctured-disc map avoiding an open planar domain
cannot end on its closure. Removability constructs the endpoint; openness of
the extension excludes boundary contact. No endpoint is assumed. -/
theorem s31he_puncture_limit_avoids_closure {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hd : DifferentiableOn ℂ f (ball c r \ {c}))
    (hi : InjOn f (ball c r \ {c}))
    (hb : BddAbove (norm ∘ f '' (ball c r \ {c})))
    {J : Set ℂ} (hJ : IsOpen J) (havoid : ∀ z ∈ ball c r \ {c}, f z ∉ J) :
    ∃ L : ℂ, Tendsto f (𝓝[≠] c) (𝓝 L) ∧ L ∉ closure J := by
  obtain ⟨g, _, heq, ht, hop⟩ := s31he_bounded_puncture_extension hr hd hi hb
  have hpunct : ball c r \ {c} ∈ 𝓝[≠] c :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds c hr)) self_mem_nhdsWithin
  have hc : g c ∉ J := hJ.isClosed_compl.mem_of_tendsto ht
    (mem_of_superset hpunct havoid)
  have himage : g '' ball c r ⊆ Jᶜ := by
    rintro y ⟨z, hz, rfl⟩
    by_cases hzc : z = c
    · change g z ∉ J
      simpa only [hzc] using hc
    · rw [heq ⟨hz, hzc⟩]
      exact havoid z ⟨hz, hzc⟩
  refine ⟨g c, ht, ?_⟩
  intro hcl
  have hnhds : g '' ball c r ∈ 𝓝 (g c) :=
    (hop _ subset_rfl isOpen_ball).mem_nhds ⟨c, mem_ball_self hr, rfl⟩
  obtain ⟨y, hy, hyJ⟩ := (mem_closure_iff_nhds.1 hcl) _ hnhds
  exact himage hy hyJ

/-- Local surface-chart form of the puncture-versus-hole obstruction. A
univalent holomorphic punctured-disc map trapped in a compact part of a chart
and avoiding the deleted closed Jordan disc has a genuine endpoint outside
that disc. The compact trapping hypothesis is local, not an end matching or
global compactification hypothesis. -/
theorem s31he_chart_endpoint_avoids_disc {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) {D : Set X} {J K : Set ℂ}
    (hDs : D ⊆ e.source) (hDJ : e '' D = closure J) (hJ : IsOpen J)
    (hK : IsCompact K) (hKt : K ⊆ e.target)
    {F : ℂ → X} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hsource : ∀ z ∈ ball c r \ {c}, F z ∈ e.source)
    (htrap : ∀ z ∈ ball c r \ {c}, e (F z) ∈ K)
    (hd : DifferentiableOn ℂ (e ∘ F) (ball c r \ {c}))
    (hi : InjOn (e ∘ F) (ball c r \ {c}))
    (havoid : ∀ z ∈ ball c r \ {c}, F z ∉ D) :
    ∃ p : X, p ∈ e.source ∧ p ∉ D ∧ Tendsto F (𝓝[≠] c) (𝓝 p) := by
  have hb : BddAbove (norm ∘ (e ∘ F) '' (ball c r \ {c})) := by
    obtain ⟨C, hC⟩ := hK.bddAbove_image continuous_norm.continuousOn
    refine ⟨C, ?_⟩
    rintro t ⟨z, hz, rfl⟩
    exact hC ⟨e (F z), htrap z hz, rfl⟩
  have havoidJ : ∀ z ∈ ball c r \ {c}, (e ∘ F) z ∉ J := by
    intro z hz hzJ
    have hzcl : e (F z) ∈ closure J := subset_closure hzJ
    rw [← hDJ] at hzcl
    obtain ⟨p, hp, heq⟩ := hzcl
    have hpF : p = F z := e.injOn (hDs hp) (hsource z hz) heq
    exact havoid z hz (hpF ▸ hp)
  obtain ⟨L, ht, hL⟩ := s31he_puncture_limit_avoids_closure hr hd hi hb hJ havoidJ
  have hpunct : ball c r \ {c} ∈ 𝓝[≠] c :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds c hr)) self_mem_nhdsWithin
  have hLK : L ∈ K := hK.isClosed.mem_of_tendsto ht (mem_of_superset hpunct htrap)
  have hLt : L ∈ e.target := hKt hLK
  refine ⟨e.symm L, e.map_target hLt, ?_, ?_⟩
  · intro hpD
    apply hL
    rw [← hDJ]
    exact ⟨e.symm L, hpD, e.right_inv hLt⟩
  · have hcomp := (e.continuousAt_symm hLt).tendsto.comp ht
    apply hcomp.congr'
    filter_upwards [hpunct] with z hz
    exact e.left_inv (hsource z hz)

end LiZhongQC

