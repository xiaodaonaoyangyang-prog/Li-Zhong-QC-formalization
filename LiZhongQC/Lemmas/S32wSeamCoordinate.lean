import LiZhongQC.Ch09.S31_FiniteType
import LiZhongQC.Lemmas.SchottkyReflectionCoordinates

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

universe u

/-- A seam coordinate of an anticonformal involution at a fixed point, avoiding a closed set `Q`. -/
theorem s32w_seam_coordinate_aux {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (J : X ≃ₜ X) (hJ : IsAnticonformalInvolution J) {p : X} (hp : J p = p) (Q : Set X)
    (hQ : IsClosed Q) (hpQ : p ∉ Q) :
    ∃ (κ : OpenPartialHomeomorph ℂ X) (r : ℝ), 0 < r ∧ ball (0 : ℂ) r ⊆ κ.source ∧ κ 0 = p ∧
      (∀ z ∈ ball (0 : ℂ) r, conj z ∈ ball (0 : ℂ) r ∧ κ (conj z) = J (κ z)) ∧
      (∀ z ∈ ball (0 : ℂ) r, κ z ∉ Q) ∧
      DifferentiableOn ℂ (fun z => chartAt ℂ p (κ z)) (ball (0 : ℂ) r) ∧
      (∀ z ∈ ball (0 : ℂ) r, deriv (fun z => chartAt ℂ p (κ z)) z ≠ 0) := by
  obtain ⟨e, hpe, he0, hea, hesa, hev⟩ := s78ra_given_involution_fixed_coordinate J hJ p hp
  let c := chartAt ℂ p
  have hps : p ∈ c.source := mem_chart_source ℂ p
  have hpt : c p ∈ c.target := c.mapsTo hps
  have h0t : (0 : ℂ) ∈ e.target := by
    have := e.map_source hpe
    rwa [he0] at this
  have hsymm0 : e.symm 0 = c p := by
    have := e.left_inv hpe
    rwa [he0] at this
  have hcont : ContinuousAt e.symm 0 := e.continuousAt_symm h0t
  have htend : Tendsto e.symm (𝓝 0) (𝓝 (c p)) := hsymm0 ▸ hcont.tendsto
  let κ : OpenPartialHomeomorph ℂ X := e.symm.trans c.symm
  have hκapp : ∀ z, κ z = c.symm (e.symm z) := fun z => rfl
  have hκsrc : ∀ z, z ∈ κ.source ↔ z ∈ e.target ∧ e.symm z ∈ c.target := fun z => Iff.rfl
  have hκ0s : (0 : ℂ) ∈ κ.source := (hκsrc 0).2 ⟨h0t, by rw [hsymm0]; exact hpt⟩
  have hκ0 : κ 0 = p := by rw [hκapp, hsymm0, c.left_inv hps]
  -- domain and continuity facts for the local expression of `J`
  have hmem : c p ∈ localMapDomain J p := by
    change c p ∈ c.target ∧ J (c.symm (c p)) ∈ (chartAt ℂ (J p)).source
    simp only [c.left_inv hps, hp]
    exact ⟨hpt, hps⟩
  have hLv : localMapExpr J p (c p) = c p := by
    change (chartAt ℂ (J p)) (J (c.symm (c p))) = c p
    simp only [c.left_inv hps, hp]
    rfl
  have hLc : ContinuousAt (localMapExpr J p) (c p) := by
    have h1 : ContinuousAt c.symm (c p) := c.continuousAt_symm hpt
    have h2 : ContinuousAt J (c.symm (c p)) := J.continuous.continuousAt
    have h3 : ContinuousAt (chartAt ℂ (J p)) (J (c.symm (c p))) := by
      refine (chartAt ℂ (J p)).continuousAt ?_
      rw [c.left_inv hps, hp]
      exact mem_chart_source ℂ p
    exact ContinuousAt.comp (f := fun z => J (c.symm z)) h3 (h2.comp h1)
  have hLt : Tendsto (localMapExpr J p) (𝓝 (c p)) (𝓝 (c p)) := by
    have := hLc.tendsto
    rwa [hLv] at this
  -- derivative of `e.symm` at `0` is nonzero
  have hder0 : deriv e.symm 0 ≠ 0 := by
    have h1 : HasDerivAt e (deriv e (c p)) (c p) := hea.differentiableAt.hasDerivAt
    have hesa' : AnalyticAt ℂ e.symm (e (c p)) := by rw [he0]; exact hesa
    have h2 : HasDerivAt e.symm (deriv e.symm (e (c p))) (e (c p)) :=
      hesa'.differentiableAt.hasDerivAt
    have h3 := h2.comp (c p) h1
    have h4 : HasDerivAt (e.symm ∘ e) 1 (c p) :=
      (hasDerivAt_id (c p)).congr_of_eventuallyEq (e.eventually_left_inverse hpe)
    have h5 := h3.unique h4
    have h6 : deriv e.symm (e (c p)) ≠ 0 := left_ne_zero_of_mul_eq_one h5
    rwa [he0] at h6
  have hcd : ContinuousAt (deriv e.symm) 0 := hesa.deriv.continuousAt
  -- the eventual facts
  have E1 : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ e.target := e.open_target.mem_nhds h0t
  have E2 : ∀ᶠ z in 𝓝 (0 : ℂ), e.symm z ∈ c.target := htend.eventually (c.open_target.mem_nhds hpt)
  have E3 : ∀ᶠ z in 𝓝 (0 : ℂ), e (localMapExpr J p (e.symm z)) = conj (e (e.symm z)) :=
    htend.eventually hev
  have E4 : ∀ᶠ z in 𝓝 (0 : ℂ), localMapExpr J p (e.symm z) ∈ e.source :=
    (hLt.comp htend).eventually (e.open_source.mem_nhds hpe)
  have E5 : ∀ᶠ z in 𝓝 (0 : ℂ), e.symm z ∈ localMapDomain J p :=
    htend.eventually ((s23_localMapDomain_isOpen J.continuous p).mem_nhds hmem)
  have E6 : ∀ᶠ z in 𝓝 (0 : ℂ), κ z ∉ Q := by
    have hκc : ContinuousAt κ 0 := κ.continuousAt hκ0s
    have : Qᶜ ∈ 𝓝 (κ 0) := by
      rw [hκ0]
      exact hQ.isOpen_compl.mem_nhds hpQ
    exact hκc.preimage_mem_nhds this
  have E7 : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ e.symm z := hesa.eventually_analyticAt
  have E8 : ∀ᶠ z in 𝓝 (0 : ℂ), deriv e.symm z ≠ 0 := hcd.eventually_ne hder0
  have hall := E1.and (E2.and (E3.and (E4.and (E5.and (E6.and (E7.and E8))))))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hall
  have hchart : ∀ z ∈ ball (0 : ℂ) r, chartAt ℂ p (κ z) = e.symm z := by
    intro z hz
    obtain ⟨-, h2, -⟩ := hball z hz
    show c (c.symm (e.symm z)) = e.symm z
    exact c.right_inv h2
  refine ⟨κ, r, hr, fun z hz => ?_, hκ0, fun z hz => ⟨?_, ?_⟩, fun z hz => (hball z hz).2.2.2.2.2.1, ?_, ?_⟩
  · obtain ⟨h1, h2, -⟩ := hball z hz
    exact (hκsrc z).2 ⟨h1, h2⟩
  · rw [mem_ball_zero_iff] at hz ⊢
    rwa [Complex.norm_conj]
  · obtain ⟨h1, h2, h3, h4, h5, -⟩ := hball z hz
    -- `w = e.symm z`
    set w := e.symm z with hw
    have hez : e w = z := e.right_inv h1
    have hLw : e (localMapExpr J p w) = conj z := by rw [h3, hez]
    have hLeq : e.symm (conj z) = localMapExpr J p w := by
      have := e.left_inv h4
      rw [hLw] at this
      exact this
    show c.symm (e.symm (conj z)) = J (c.symm w)
    rw [hLeq]
    have hdom : w ∈ localMapDomain J p := h5
    change w ∈ c.target ∧ J (c.symm w) ∈ (chartAt ℂ (J p)).source at hdom
    rw [hp] at hdom
    have hL : localMapExpr J p w = c (J (c.symm w)) := by
      show chartAt ℂ (J p) (J (c.symm w)) = chartAt ℂ p (J (c.symm w))
      rw [hp]
    rw [hL]
    exact c.left_inv hdom.2
  · have hdiffon : DifferentiableOn ℂ e.symm (ball (0 : ℂ) r) := fun z hz =>
      (hball z hz).2.2.2.2.2.2.1.differentiableAt.differentiableWithinAt
    exact hdiffon.congr fun z hz => hchart z hz
  · intro z hz
    have hev' : (fun z => chartAt ℂ p (κ z)) =ᶠ[𝓝 z] e.symm :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) hchart
    rw [hev'.deriv_eq]
    exact (hball z hz).2.2.2.2.2.2.2

theorem s32w_seam_halves {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    {F : FiniteTypeStructure S g n m} {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {κ : OpenPartialHomeomorph ℂ Xd.carrier} {r : ℝ} (hr : 0 < r)
    (hsrc : ball (0 : ℂ) r ⊆ κ.source)
    (heq : ∀ z ∈ ball (0 : ℂ) r, conj z ∈ ball (0 : ℂ) r ∧ κ (conj z) = J (κ z))
    (hQ : ∀ z ∈ ball (0 : ℂ) r, κ z ∉ (↑Pd : Set Xd.carrier)) :
    (∀ z ∈ ball (0 : ℂ) r, 0 < z.im → κ z ∈ range ιd) ∨
      (∀ z ∈ ball (0 : ℂ) r, 0 < z.im → κ z ∈ range (J ∘ ιd)) := by
  have hconv : Convex ℝ (ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im}) :=
    (convex_ball 0 r).inter (convex_halfSpace_im_gt 0)
  have hpre := hconv.isPreconnected
  have hsub : ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im} ⊆ κ.source := fun z hz => hsrc hz.1
  have himg : IsPreconnected (κ '' (ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im})) :=
    hpre.image κ (κ.continuousOn.mono hsub)
  have hA1 : IsOpen (range ιd) := hd.embedding.isOpen_range
  have hA2 : IsOpen (range (J ∘ ιd)) := (J.isOpenEmbedding.comp hd.embedding).isOpen_range
  have hcover : κ '' (ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im}) ⊆ range ιd ∪ range (J ∘ ιd) := by
    rintro _ ⟨z, ⟨hzb, hzi⟩, rfl⟩
    have hz0 : z ∈ ball (0 : ℂ) r := hzb
    have hzim : 0 < z.im := hzi
    have hall : κ z ∈ (univ : Set Xd.carrier) := mem_univ _
    rw [← hd.cover] at hall
    rcases hall with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hJ : J (κ z) = κ z := h
      obtain ⟨hcb, hκc⟩ := heq z hz0
      rw [← hκc] at hJ
      have := κ.injOn (hsrc hcb) (hsrc hz0) hJ
      have him := congrArg Complex.im this
      rw [Complex.conj_im] at him
      linarith
    · exact absurd h (hQ z hz0)
  rcases hpre.image κ (κ.continuousOn.mono hsub) |>.subset_or_subset hA1 hA2 hd.disjoint hcover with h | h
  · left
    intro z hz hzi
    exact h ⟨z, ⟨hz, hzi⟩, rfl⟩
  · right
    intro z hz hzi
    exact h ⟨z, ⟨hz, hzi⟩, rfl⟩

theorem s32w_seam_coordinate {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {p : Xd.carrier} (hp : J p = p) :
    ∃ (κ : OpenPartialHomeomorph ℂ Xd.carrier) (r : ℝ), 0 < r ∧ ball (0 : ℂ) r ⊆ κ.source ∧
      κ 0 = p ∧
      (∀ z ∈ ball (0 : ℂ) r, conj z ∈ ball (0 : ℂ) r ∧ κ (conj z) = J (κ z)) ∧
      (∀ z ∈ ball (0 : ℂ) r, 0 < z.im → κ z ∈ range ιd) ∧
      (∀ z ∈ ball (0 : ℂ) r, z.im < 0 → κ z ∈ range (J ∘ ιd)) ∧
      (∀ z ∈ ball (0 : ℂ) r, z.im = 0 → J (κ z) = κ z) ∧
      DifferentiableOn ℂ (fun z => chartAt ℂ p (κ z)) (ball (0 : ℂ) r) ∧
      (∀ z ∈ ball (0 : ℂ) r, deriv (fun z => chartAt ℂ p (κ z)) z ≠ 0) := by
  have hpP : p ∉ (↑Pd : Set Xd.carrier) := by
    have : p ∈ {x | J x = x} := hp
    rw [hd.fixed_curves] at this
    exact this.2
  obtain ⟨κ, r, hr, hsrc, hκ0, heq, hQ, hdiff, hder⟩ :=
    s32w_seam_coordinate_aux J hd.involution hp (↑Pd) Pd.finite_toSet.isClosed hpP
  have hconjim : ∀ z : ℂ, (conj z).im = -z.im := fun z => Complex.conj_im z
  have hfix : ∀ z ∈ ball (0 : ℂ) r, z.im = 0 → J (κ z) = κ z := by
    intro z hz hzi
    have hc : conj z = z := Complex.conj_eq_iff_im.2 hzi
    have := (heq z hz).2
    rw [hc] at this
    exact this.symm
  have hneg : ∀ z ∈ ball (0 : ℂ) r, -z ∈ ball (0 : ℂ) r := fun z hz => by
    simpa [mem_ball_zero_iff] using hz
  rcases s32w_seam_halves hd hr hsrc heq hQ with h | h
  · refine ⟨κ, r, hr, hsrc, hκ0, heq, h, ?_, hfix, hdiff, hder⟩
    intro z hz hzi
    have hcz := (heq z hz).1
    have hu : 0 < (conj z).im := by rw [hconjim]; linarith
    obtain ⟨s, hs⟩ := h (conj z) hcz hu
    refine ⟨s, ?_⟩
    have h2 := (heq (conj z) hcz).2
    rw [Complex.conj_conj] at h2
    rw [h2, ← hs]
    rfl
  · let N : OpenPartialHomeomorph ℂ ℂ := (Homeomorph.neg ℂ).toOpenPartialHomeomorph
    let κ' : OpenPartialHomeomorph ℂ Xd.carrier := N.trans κ
    have hκ'app : ∀ z, κ' z = κ (-z) := fun z => rfl
    have hsrc' : ball (0 : ℂ) r ⊆ κ'.source := by
      intro z hz
      simp only [κ', OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage]
      exact ⟨by simp [N], hsrc (hneg z hz)⟩
    have heq' : ∀ z ∈ ball (0 : ℂ) r, conj z ∈ ball (0 : ℂ) r ∧ κ' (conj z) = J (κ' z) := by
      intro z hz
      refine ⟨(heq z hz).1, ?_⟩
      rw [hκ'app, hκ'app, ← map_neg]
      exact (heq (-z) (hneg z hz)).2
    have hup' : ∀ z ∈ ball (0 : ℂ) r, 0 < z.im → κ' z ∈ range ιd := by
      intro z hz hzi
      have hnz := hneg z hz
      have hcnz := (heq (-z) hnz).1
      have hu : 0 < (conj (-z)).im := by rw [hconjim, Complex.neg_im]; linarith
      obtain ⟨s, hs⟩ := h (conj (-z)) hcnz hu
      refine ⟨s, ?_⟩
      have h2 := (heq (conj (-z)) hcnz).2
      rw [Complex.conj_conj] at h2
      rw [hκ'app, h2, ← hs]
      exact (hd.involution.1 (ιd s)).symm
    have hlow' : ∀ z ∈ ball (0 : ℂ) r, z.im < 0 → κ' z ∈ range (J ∘ ιd) := by
      intro z hz hzi
      have hu : 0 < (-z).im := by rw [Complex.neg_im]; linarith
      exact h (-z) (hneg z hz) hu
    refine ⟨κ', r, hr, hsrc', ?_, heq', hup', hlow', ?_, ?_, ?_⟩
    · rw [hκ'app, neg_zero]
      exact hκ0
    · intro z hz hzi
      have hc : conj z = z := Complex.conj_eq_iff_im.2 hzi
      have := (heq' z hz).2
      rw [hc] at this
      exact this.symm
    · have := hdiff.comp (differentiable_neg.differentiableOn (s := ball (0 : ℂ) r))
        (fun z hz => hneg z hz)
      exact this
    · intro z hz
      have e1 : (fun z => chartAt ℂ p (κ' z)) =
          fun z => (fun w => chartAt ℂ p (κ w)) (-z) := rfl
      have e2 : deriv (fun z => chartAt ℂ p (κ' z)) z =
          -deriv (fun w => chartAt ℂ p (κ w)) (-z) :=
        deriv_comp_neg (fun w => chartAt ℂ p (κ w)) z
      rw [e2]
      exact neg_ne_zero.2 (hder _ (hneg z hz))

end LiZhongQC
