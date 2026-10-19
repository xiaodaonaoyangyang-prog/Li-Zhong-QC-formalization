import LiZhongQC.Lemmas.SchottkyReflectionCoordinates
import LiZhongQC.Lemmas.FiniteTypePunctureEndpoint
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- An analytic map taking a real value at the centre cannot avoid the real
axis throughout a punctured neighbourhood. Local constancy and local openness
are both excluded by the actual punctured values. -/
theorem s31qr_analytic_cannot_touch_real {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hc : (f c).im = 0)
    (havoid : ∀ᶠ z in 𝓝[≠] c, (f z).im ≠ 0) : False := by
  rcases hf.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
  · obtain ⟨z, hz, he⟩ := (havoid.and (hconst.filter_mono nhdsWithin_le_nhds)).exists
    exact hz (by rw [he]; exact hc)
  · have hv : ∀ᶠ z in 𝓝 c, (f z).im ≠ 0 ∨ f z = f c := by
      filter_upwards [eventually_nhdsWithin_iff.1 havoid] with z hz
      by_cases he : z = c
      · exact Or.inr (congrArg f he)
      · exact Or.inl (hz he)
    have ht : {w : ℂ | w.im ≠ 0 ∨ w = f c} ∈ 𝓝 (f c) := hopen hv
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 ht
    have hw : f c + (ε / 2 : ℝ) ∈ ball (f c) ε := by
      change dist (f c + (ε / 2 : ℝ)) (f c) < ε
      rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    rcases hb hw with him | heq
    · exact him (by simp only [Complex.add_im, Complex.ofReal_im, hc, add_zero])
    · have hh := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.ofReal_re] at hh
      linarith

/-- A holomorphic map on a punctured neighbourhood whose values avoid the real
axis cannot have a finite real limit there. The removable value is constructed
by update, not assumed to be part of the original map. -/
theorem s31qr_punctured_real_limit_impossible {f : ℂ → ℂ} {c a : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (ht : Tendsto f (𝓝[≠] c) (𝓝 a)) (ha : a.im = 0)
    (havoid : ∀ᶠ z in 𝓝[≠] c, (f z).im ≠ 0) : False := by
  classical
  let g := Function.update f c a
  have hgC : ContinuousAt g c := continuousAt_update_same.2 ht
  have hgD : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ g z := by
    filter_upwards [hd, self_mem_nhdsWithin] with z hz hne
    apply hz.congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hne] with w hw
    exact Function.update_of_ne hw a f
  have hgA := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgD hgC
  have hgR : (g c).im = 0 := by simpa only [g, Function.update_self] using ha
  have hgAvoid : ∀ᶠ z in 𝓝[≠] c, (g z).im ≠ 0 := by
    filter_upwards [havoid, self_mem_nhdsWithin] with z hz hne
    simpa only [g, Function.update_of_ne hne] using hz
  exact s31qr_analytic_cannot_touch_real hgA hgR hgAvoid

/-- An actual holomorphic punctured map into the positive half of an arbitrary
given double cannot tend to a fixed point. The reflection coordinate is
constructed by the already passed given-involution coordinate theorem. -/
theorem s31qr_punctured_half_limit_not_fixed
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd)
    {γ : ℂ → Xd.carrier} {c : ℂ} {q : Xd.carrier}
    (hγ : ∀ᶠ z in 𝓝[≠] c, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) γ z)
    (ht : Tendsto γ (𝓝[≠] c) (𝓝 q))
    (hhalf : ∀ᶠ z in 𝓝[≠] c, γ z ∈ range ιd) : J q ≠ q := by
  intro hfix
  obtain ⟨e, heS, he0, heA, _heInv, href⟩ :=
    s78ra_given_involution_fixed_coordinate J hd.involution q hfix
  let b := chartAt ℂ q
  have hbs : q ∈ b.source := mem_chart_source ℂ q
  have hbt : b q ∈ b.target := b.map_source hbs
  have hleft : b.symm (b q) = q := b.left_inv hbs
  have hcoord : Tendsto (fun z => b (γ z)) (𝓝[≠] c) (𝓝 (b q)) :=
    (b.continuousAt hbs).tendsto.comp ht
  have hsource : ∀ᶠ z in 𝓝[≠] c, γ z ∈ b.source :=
    ht.eventually (b.open_source.mem_nhds hbs)
  have hLc : ContinuousAt (localMapExpr J q) (b q) := by
    have h1 : ContinuousAt (fun w => J (b.symm w)) (b q) :=
      J.continuous.continuousAt.comp (b.continuousAt_symm hbt)
    have h2 : ContinuousAt (chartAt ℂ (J q)) (J (b.symm (b q))) := by
      rw [hleft]
      exact (chartAt ℂ (J q)).continuousAt (mem_chart_source ℂ (J q))
    exact ContinuousAt.comp (g := chartAt ℂ (J q)) (f := fun w => J (b.symm w)) (x := b q) h2 h1
  have hL0 : localMapExpr J q (b q) = b q := by
    simpa only [hfix] using (s23_h_center J q).2
  have hLes : ∀ᶠ w in 𝓝 (b q), localMapExpr J q w ∈ e.source := by
    apply hLc.preimage_mem_nhds
    rw [hL0]
    exact e.open_source.mem_nhds heS
  have hdom : ∀ᶠ w in 𝓝 (b q), w ∈ localMapDomain J q :=
    (s23_localMapDomain_isOpen J.continuous q).mem_nhds (s23_h_center J q).1
  let f : ℂ → ℂ := fun z => e (b (γ z))
  have hfT : Tendsto f (𝓝[≠] c) (𝓝 (0 : ℂ)) := by
    have hh := heA.continuousAt.tendsto.comp hcoord
    rwa [he0] at hh
  have hfD : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z := by
    filter_upwards [hγ, hsource, hcoord.eventually heA.eventually_analyticAt] with z hz hs he
    have hbc : DifferentiableAt ℂ (fun w => b (γ w)) z :=
      mdifferentiableAt_iff_differentiableAt.1
        ((mdifferentiableAt_atlas (chart_mem_atlas ℂ q) hs).comp z hz)
    exact he.differentiableAt.comp z hbc
  have hfAvoid : ∀ᶠ z in 𝓝[≠] c, (f z).im ≠ 0 := by
    filter_upwards [hhalf, hsource, hcoord.eventually href,
      hcoord.eventually (e.open_source.mem_nhds heS),
      hcoord.eventually hLes, hcoord.eventually hdom] with z hz hs he hes hles hds
    intro him
    have hconj : conj (e (b (γ z))) = e (b (γ z)) :=
      Complex.conj_eq_iff_im.2 him
    have hLeq : localMapExpr J q (b (γ z)) = b (γ z) :=
      e.injOn hles hes (he.trans hconj)
    have hJsrc : J (γ z) ∈ b.source := by
      have hh := hds.2
      change J (b.symm (b (γ z))) ∈ (chartAt ℂ (J q)).source at hh
      rwa [hfix, b.left_inv hs] at hh
    have hJcoord : b (J (γ z)) = b (γ z) := by
      change (chartAt ℂ (J q)) (J (b.symm (b (γ z)))) = b (γ z) at hLeq
      rwa [hfix, b.left_inv hs] at hLeq
    have hJfix : J (γ z) = γ z := b.injOn hJsrc hs hJcoord
    have hmirror : γ z ∈ range (J ∘ ιd) := by
      obtain ⟨a, ha⟩ := hz
      refine ⟨a, ?_⟩
      change J (ιd a) = γ z
      rw [ha, hJfix]
    exact Set.disjoint_left.1 hd.disjoint hz hmirror
  exact s31qr_punctured_real_limit_impossible hfD hfT (by simp) hfAvoid

/-- Every actual limit of an original puncture in an arbitrary given double
is disjoint from the fixed-point seam. The punctured parametrization and its
holomorphy are built from the original finite-type data. -/
theorem s31qr_original_puncture_limit_not_fixed
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [Nonempty S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd)
    {p : F.X.carrier} (hp : p ∈ F.P) {q : Xd.carrier}
    (ht : Tendsto ιd (comap F.ι (𝓝 p)) (𝓝 q)) : J q ≠ q := by
  obtain ⟨r, hr, hrt, _hrU, hrr⟩ := s31eg_puncture_chart F hp univ univ_mem
  let b := chartAt ℂ p
  let A : Set S := F.ι ⁻¹' b.source
  let φ : S → ℂ := b ∘ F.ι
  let ψ : ℂ → S := Function.invFunOn φ A
  have hAo : IsOpen A := b.open_source.preimage F.embedding.continuous
  have hφi : InjOn φ A := by
    intro a ha c hc he
    exact F.embedding.injective (b.injOn ha hc he)
  have hφd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) φ A := by
    intro a ha
    exact ((mdifferentiableAt_atlas (chart_mem_atlas ℂ p) ha).comp a
      (F.holomorphic a)).mdifferentiableWithinAt
  have himg : ∀ z ∈ ball (b p) r \ {b p}, z ∈ φ '' A := by
    intro z hz
    obtain ⟨a, ha⟩ := hrr z hz
    refine ⟨a, ?_, ?_⟩
    · change F.ι a ∈ b.source
      rw [ha]
      exact b.map_target (hrt hz.1)
    · change b (F.ι a) = z
      rw [ha, b.right_inv (hrt hz.1)]
  have hmodel : ∀ z ∈ ball (b p) r \ {b p}, F.ι (ψ z) = b.symm z := by
    intro z hz
    have hzimg := himg z hz
    have hψA : ψ z ∈ A := Function.invFunOn_mem hzimg
    apply b.injOn hψA (b.map_target (hrt hz.1))
    exact (Function.invFunOn_eq hzimg).trans (b.right_inv (hrt hz.1)).symm
  have hψd : ∀ z ∈ ball (b p) r \ {b p}, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ z :=
    fun z hz => s31eg_coordinate_inverse hAo hφi hφd (himg z hz)
  have hnear : ∀ᶠ z in 𝓝[≠] (b p), z ∈ ball (b p) r \ {b p} := by
    filter_upwards [nhdsWithin_le_nhds (s := {b p}ᶜ) (ball_mem_nhds (b p) hr),
      self_mem_nhdsWithin] with z hz hne
    exact ⟨hz, hne⟩
  have hback : Tendsto (fun z => F.ι (ψ z)) (𝓝[≠] (b p)) (𝓝 p) := by
    have hbT : Tendsto b.symm (𝓝[≠] (b p)) (𝓝 p) := by
      have h := (b.continuousAt_symm (b.map_source (mem_chart_source ℂ p))).tendsto
      rw [b.left_inv (mem_chart_source ℂ p)] at h
      exact h.mono_left nhdsWithin_le_nhds
    apply hbT.congr'
    filter_upwards [hnear] with z hz
    exact (hmodel z hz).symm
  have hψT : Tendsto ψ (𝓝[≠] (b p)) (comap F.ι (𝓝 p)) := tendsto_comap_iff.2 hback
  refine s31qr_punctured_half_limit_not_fixed F hd (γ := ιd ∘ ψ)
    (c := b p) (q := q) ?_ (ht.comp hψT) ?_
  · filter_upwards [hnear] with z hz
    exact (hd.holomorphic (ψ z)).comp z (hψd z hz)
  · exact Eventually.of_forall fun z => ⟨ψ z, rfl⟩

/-- Any existing original puncture limit is a member of Pd, not either open
half or the seam. Existence of such limits is the next, separate end problem. -/
theorem s31qr_original_puncture_limit_mem_Pd
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [Nonempty S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd)
    {p : F.X.carrier} (hp : p ∈ F.P) {q : Xd.carrier}
    (ht : Tendsto ιd (comap F.ι (𝓝 p)) (𝓝 q)) : q ∈ Pd := by
  letI := s31eg_puncture_neBot F hp
  have hpout : p ∉ range F.ι := by
    rw [F.range_ι]
    exact fun h => h (Or.inl hp)
  have hqpos : q ∉ range ιd :=
    s31eg_cluster_missing F.ι ιd F.embedding.continuous hd.embedding hpout ht.mapClusterPt
  have hqmirror : q ∉ range (J ∘ ιd) := by
    intro hqm
    have hMo : IsOpen (range (J ∘ ιd)) :=
      (J.isOpenMap.comp hd.embedding.isOpenMap).isOpen_range
    obtain ⟨a, ha⟩ := (ht.eventually (hMo.mem_nhds hqm)).exists
    exact Set.disjoint_left.1 hd.disjoint (mem_range_self a) ha
  have hqfix := s31qr_original_puncture_limit_not_fixed F hd hp ht
  have hcov : q ∈ range ιd ∪ range (J ∘ ιd) ∪ {x | J x = x} ∪ (↑Pd : Set Xd.carrier) := by
    rw [hd.cover]
    trivial
  rcases hcov with ((h | h) | h) | h
  · exact False.elim (hqpos h)
  · exact False.elim (hqmirror h)
  · exact False.elim (hqfix h)
  · exact h

end LiZhongQC
