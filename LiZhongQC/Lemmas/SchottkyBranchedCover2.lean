import LiZhongQC.Lemmas.SchottkyNonOrientableCover
import Mathlib.Topology.Subpath


/-!
# Double covers attached to index-two subgroups of `π₁`

For a Riemann surface `S` and a subgroup `K ≤ π₁(S, x₀)` of index two, the quotient
`Y = PathCover x₀ / K` is a Riemann surface with a holomorphic two-sheeted covering `q : Y → S`
and a free holomorphic deck involution `τ`; lifts of loops whose class (conjugated to the base
point) is not in `K` are not closed (`s82bc_index_two_cover`).
-/

open Set Topology Filter
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC
universe u

open RiemannDynamics
/-- The projection of the path cover reads as the identity in the canonical charts. -/
theorem s82bc_pathCover_chart_proj {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] (x₀ : S) (pc : PathCover x₀) :
    ∀ qc ∈ (chartAt ℂ pc).source, pathCoverProj x₀ qc ∈ (chartAt ℂ (pathCoverProj x₀ pc)).source ∧
      chartAt ℂ (pathCoverProj x₀ pc) (pathCoverProj x₀ qc) = chartAt ℂ pc qc := by
  obtain ⟨-, hproj, -⟩ :=
    Classical.choose_spec (exists_pathCover_openPartialHomeomorph x₀ pc)
  intro qc hq
  have hq' : qc ∈ (Classical.choose (exists_pathCover_openPartialHomeomorph x₀ pc) ≫ₕ
      chartAt ℂ (pathCoverProj x₀ pc)).source := hq
  rw [OpenPartialHomeomorph.trans_source] at hq'
  obtain ⟨h1, h2⟩ := hq'
  refine ⟨?_, ?_⟩
  · rw [← hproj qc h1]
    exact h2
  · rw [← hproj qc h1]
    rfl

section Quotient

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
  [IsManifold 𝓘(ℂ) ω S] {x₀ : S} {K : Subgroup (FundamentalGroup S x₀)}
  [MulAction K (PathCover x₀)]

/-- **The quotient is a Riemann surface**: charts are local inverses of the quotient covering
followed by charts of the path cover; the transition maps agree locally with transitions through
an analytic deck transformation. -/
theorem s82bc_quotient_manifold
    (hsmul : ∀ (g : K) (pc : PathCover x₀),
      g • pc = pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc) :
    ∃ _ : ChartedSpace ℂ (Quotient (MulAction.orbitRel K (PathCover x₀))),
      IsManifold 𝓘(ℂ) ω (Quotient (MulAction.orbitRel K (PathCover x₀))) ∧
      ∀ (q : Quotient (MulAction.orbitRel K (PathCover x₀)) → S)
        (_ : ∀ e, q (Quotient.mk _ e) = pathCoverProj x₀ e)
        (y y' : Quotient (MulAction.orbitRel K (PathCover x₀))),
        y' ∈ (chartAt ℂ y).source → q y' ∈ (chartAt ℂ (q y)).source ∧
          chartAt ℂ (q y) (q y') = chartAt ℂ y y' := by
  classical
  have hq := (s78no_isQuotientCoveringMap hsmul).isLocalHomeomorph
  choose ψ hψmem hψeq using fun y : Quotient (MulAction.orbitRel K (PathCover x₀)) =>
    hq (Quotient.out y)
  set ch : Quotient (MulAction.orbitRel K (PathCover x₀)) → OpenPartialHomeomorph
      (Quotient (MulAction.orbitRel K (PathCover x₀))) ℂ := fun y =>
    (ψ y).symm.trans (chartAt ℂ (Quotient.out y)) with hch
  have hψout : ∀ y, ψ y (Quotient.out y) = y := by
    intro y; rw [← hψeq y]; exact Quotient.out_eq y
  have hmem : ∀ y, y ∈ (ch y).source := by
    intro y
    simp only [hch, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage]
    have h1 := (ψ y).map_source (hψmem y)
    have h2 := (ψ y).left_inv (hψmem y)
    rw [hψout y] at h1 h2
    refine ⟨h1, ?_⟩
    rw [h2]; exact mem_chart_source ℂ _
  let cs : ChartedSpace ℂ (Quotient (MulAction.orbitRel K (PathCover x₀))) :=
    { atlas := range ch
      chartAt := ch
      mem_chart_source := hmem
      chart_mem_atlas := fun y => ⟨y, rfl⟩ }
  have hchart : ∀ (q : Quotient (MulAction.orbitRel K (PathCover x₀)) → S)
      (_ : ∀ e, q (Quotient.mk _ e) = pathCoverProj x₀ e)
      (y y' : Quotient (MulAction.orbitRel K (PathCover x₀))),
      y' ∈ (cs.chartAt y).source → q y' ∈ (chartAt ℂ (q y)).source ∧
        chartAt ℂ (q y) (q y') = cs.chartAt y y' := by
    intro q hq y y' hy'
    have hy'' : y' ∈ (ch y).source := hy'
    simp only [hch, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage] at hy''
    obtain ⟨hy1, hy2⟩ := hy''
    have hqy : q y = pathCoverProj x₀ (Quotient.out y) := by
      rw [← hq, Quotient.out_eq]
    have hy3 : y' = Quotient.mk _ ((ψ y).symm y') := by
      rw [congrFun (hψeq y) _, (ψ y).right_inv hy1]
    have hqy' : q y' = pathCoverProj x₀ ((ψ y).symm y') := by
      have : q y' = q (Quotient.mk _ ((ψ y).symm y')) := congrArg q hy3
      rw [this, hq]
    obtain ⟨hm, he⟩ := s82bc_pathCover_chart_proj x₀ (Quotient.out y) ((ψ y).symm y') hy2
    rw [hqy, hqy']
    exact ⟨hm, he⟩
  refine ⟨cs, isManifold_of_contDiffOn _ _ _ ?_, hchart⟩
  rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, preimage_id, range_id, inter_univ]
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  set e := Quotient.out y with he
  set e' := Quotient.out y' with he'
  -- unpack the source condition
  simp only [hch, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.coe_trans, Function.comp_apply,
    OpenPartialHomeomorph.trans_target] at hz
  obtain ⟨⟨hz1, hz2⟩, hz3, hz4⟩ := hz
  set a := (chartAt ℂ e).symm z with ha
  set b := (ψ y').symm (ψ y a) with hb
  have hbsrc : b ∈ (ψ y').source := (ψ y').map_target hz3
  have hqab : Quotient.mk (MulAction.orbitRel K (PathCover x₀)) b =
      Quotient.mk (MulAction.orbitRel K (PathCover x₀)) a := by
    rw [congrFun (hψeq y') b, congrFun (hψeq y) a, hb, (ψ y').right_inv hz3]
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact hqab)
  replace hg : g • a = b := hg
  obtain ⟨gd, hgd⟩ := s78no_continuous_smul hsmul g
  -- local agreement with the deck transition
  have hev : (fun w => chartAt ℂ e' ((ψ y').symm (ψ y ((chartAt ℂ e).symm w)))) =ᶠ[𝓝 z]
      (fun w => chartAt ℂ e' (gd ((chartAt ℂ e).symm w))) := by
    have hc : ContinuousAt (fun w => gd ((chartAt ℂ e).symm w)) z :=
      gd.continuous.continuousAt.comp ((chartAt ℂ e).continuousAt_symm hz1)
    have h1 : ∀ᶠ w in 𝓝 z, (chartAt ℂ e).symm w ∈ (ψ y).source :=
      ((chartAt ℂ e).continuousAt_symm hz1).preimage_mem_nhds
        ((ψ y).open_source.mem_nhds hz2)
    have h2 : ∀ᶠ w in 𝓝 z, gd ((chartAt ℂ e).symm w) ∈ (ψ y').source := by
      apply hc.preimage_mem_nhds
      rw [hgd, hg]; exact (ψ y').open_source.mem_nhds hbsrc
    filter_upwards [h1, h2] with w hw1 hw2
    congr 1
    have hqq : ψ y ((chartAt ℂ e).symm w) = ψ y' (gd ((chartAt ℂ e).symm w)) := by
      rw [← congrFun (hψeq y) _, ← congrFun (hψeq y') _, hgd]
      exact (Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g, rfl⟩)).symm
    rw [hqq, (ψ y').left_inv hw2]
  apply ContDiffAt.congr_of_eventuallyEq _ hev
  have hsmooth : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω gd a := gd.contMDiff.contMDiffAt
  have ha_src : a ∈ (chartAt ℂ e).source := (chartAt ℂ e).map_target hz1
  have hb_src : gd a ∈ (chartAt ℂ e').source := by rw [hgd, hg]; exact hz4
  rw [contMDiffAt_iff_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω) e)
    (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ)) (n := ω) e') ha_src hb_src] at hsmooth
  have h := hsmooth.2
  simp only [OpenPartialHomeomorph.extend, PartialEquiv.coe_trans,
    PartialEquiv.coe_trans_symm, ModelWithCorners.toPartialEquiv_coe,
    ModelWithCorners.toPartialEquiv_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, range_id, Function.comp_id, Function.id_comp,
    OpenPartialHomeomorph.coe_coe, OpenPartialHomeomorph.coe_coe_symm] at h
  rw [ha, (chartAt ℂ e).right_inv hz1] at h
  exact h.contDiffAt univ_mem

end Quotient

/-- A local homeomorphism whose fibres are the orbits `{y, τ y}` of a free continuous involution
on a Hausdorff space is a covering map. -/
theorem s82bc_covering_of_involution {Y S : Type*} [TopologicalSpace Y] [T2Space Y]
    [TopologicalSpace S] (q : Y → S) (τ : Y → Y) (hqlh : IsLocalHomeomorph q)
    (hqs : Function.Surjective q) (hτ : Continuous τ) (hτ2 : ∀ y, τ (τ y) = y)
    (hqτ : ∀ y, q (τ y) = q y) (hfree : ∀ y, τ y ≠ y)
    (hfib : ∀ y y', q y = q y' → y' = y ∨ y' = τ y) : IsCoveringMap q := by
  classical
  intro s
  obtain ⟨y₀, rfl⟩ := hqs s
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage (I := Bool) ?_
  obtain ⟨W₀, W₁, hW₀, hW₁, h0, h1, hdisj⟩ := t2_separation (hfree y₀).symm
  obtain ⟨φ, hy₀φ, hφ⟩ := hqlh y₀
  let U : Set Y := φ.source ∩ W₀ ∩ τ ⁻¹' W₁
  have hUo : IsOpen U := (φ.open_source.inter hW₀).inter (hW₁.preimage hτ)
  have hy₀U : y₀ ∈ U := ⟨⟨hy₀φ, h0⟩, h1⟩
  have hqopen : IsOpenMap q := hqlh.isOpenMap
  have hqc : Continuous q := hqlh.continuous
  have hτU : IsOpen (τ ⁻¹' U) := hUo.preimage hτ
  have himg : q '' (τ ⁻¹' U) = q '' U := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨τ y, hy, hqτ y⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨τ y, by simpa [hτ2] using hy, by rw [hqτ]⟩
  let Uf : Bool → Set Y := fun b => if b then U else τ ⁻¹' U
  have hUf : ∀ b, IsOpen (Uf b) := by
    intro b; cases b
    · exact hτU
    · exact hUo
  have himgf : ∀ b, q '' (Uf b) = q '' U := by
    intro b; cases b
    · exact himg
    · rfl
  have hVo : IsOpen (q '' U) := hqopen _ hUo
  haveI : Nonempty (S → Y) := ⟨fun _ => y₀⟩
  let tt := IsOpen.trivializationDiscrete (f := q) (ι := Bool) Uf (q '' U) hVo
    (by
      intro b W hW
      constructor
      · intro h; exact (h.preimage hqc).inter (hUf b)
      · intro h
        have : W = q '' (q ⁻¹' W ∩ Uf b) := by
          ext z
          constructor
          · intro hz
            have : z ∈ q '' Uf b := by rw [himgf]; exact hW hz
            obtain ⟨y, hy, rfl⟩ := this
            exact ⟨y, ⟨hz, hy⟩, rfl⟩
          · rintro ⟨y, hy, rfl⟩; exact hy.1
        rw [this]; exact hqopen _ h)
    (by
      intro b
      cases b
      · intro y hy y' hy' hyy
        have h1 : τ y = τ y' := by
          apply φ.injOn hy.1.1 hy'.1.1
          rw [← hφ, hqτ, hqτ]; exact hyy
        calc y = τ (τ y) := (hτ2 y).symm
          _ = τ (τ y') := by rw [h1]
          _ = y' := hτ2 y'
      · intro y hy y' hy' hyy
        apply φ.injOn hy.1.1 hy'.1.1
        rw [← hφ]; exact hyy)
    (by
      intro b
      rw [Set.SurjOn, himgf b])
    (by
      intro b b' hbb'
      cases b <;> cases b' <;> simp at hbb'
      · rw [Function.onFun, Set.disjoint_left]
        intro y hy hy'
        have a1 : τ y ∈ W₁ := hy'.2
        have a2 : τ y ∈ W₀ := hy.1.2
        exact Set.disjoint_left.mp hdisj a2 a1
      · rw [Function.onFun, Set.disjoint_left]
        intro y hy hy'
        have a1 : τ y ∈ W₁ := hy.2
        have a2 : τ y ∈ W₀ := hy'.1.2
        exact Set.disjoint_left.mp hdisj a2 a1)
    (by
      intro y hy
      obtain ⟨u, hu, huy⟩ := hy
      rcases hfib u y huy with h | h
      · exact Set.mem_iUnion.mpr ⟨true, by simpa [Uf, h] using hu⟩
      · refine Set.mem_iUnion.mpr ⟨false, ?_⟩
        show y ∈ τ ⁻¹' U
        show τ y ∈ U
        rw [h, hτ2]; exact hu)
  exact IsEvenlyCovered.of_trivialization (t := tt) ⟨y₀, hy₀U, rfl⟩

/-- **Endpoint of a lift to the path cover.**  A lift of a path `f` to the path cover starting at
`⟨f 0, κ⟩` ends at `⟨f 1, κ · [f]⟩`. -/
theorem s82bc_lift_endpoint {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (x₀ : S)
    (f : C(unitInterval, S)) (κ : Path.Homotopic.Quotient x₀ (f 0))
    (Γ : C(unitInterval, PathCover x₀)) (h0 : Γ 0 = ⟨f 0, κ⟩)
    (hΓ : ∀ u, pathCoverProj x₀ (Γ u) = f u) :
    Γ 1 = ⟨f 1, κ.trans (Path.Homotopic.Quotient.mk (⟨f, rfl, rfl⟩ : Path (f 0) (f 1)))⟩ := by
  classical
  let P : Path (f 0) (f 1) := ⟨f, rfl, rfl⟩
  let F : unitInterval → PathCover x₀ :=
    fun u => ⟨f u, κ.trans (Path.Homotopic.Quotient.mk (P.subpath 0 u))⟩
  have hFc : Continuous F := by
    refine continuous_generateFrom_iff.mpr ?_
    rintro _ ⟨pc, U, hU, hpcU, rfl⟩
    rw [isOpen_iff_mem_nhds]
    intro t₀ ht₀
    obtain ⟨η₀, hη₀, hcls₀⟩ := ht₀
    have hW : IsOpen (f ⁻¹' U) := hU.preimage f.continuous
    have ht₀W : t₀ ∈ f ⁻¹' U := by
      have := hη₀ 1
      rw [η₀.target] at this
      exact this
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hW t₀ ht₀W
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t₀ hδ) ?_
    intro t ht
    have hseg : ∀ s ∈ Set.uIcc t₀ t, s ∈ Metric.ball t₀ δ := by
      intro s hs
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
      rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at ht
      rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_lt] at ht ⊢
        constructor <;> linarith [ht.1, ht.2, (show (t₀ : ℝ) ≤ s from h1), (show (s : ℝ) ≤ t from h2)]
      · rw [abs_lt] at ht ⊢
        constructor <;> linarith [ht.1, ht.2, (show (t : ℝ) ≤ s from h1), (show (s : ℝ) ≤ t₀ from h2)]
    refine ⟨η₀.trans (P.subpath t₀ t), ?_, ?_⟩
    · intro s
      have hr : range (η₀.trans (P.subpath t₀ t)) ⊆ U := by
        rw [Path.trans_range]
        refine union_subset ?_ ?_
        · rintro z ⟨s', rfl⟩
          exact hη₀ s'
        · rw [Path.range_subpath]
          rintro _ ⟨x, hx, rfl⟩
          exact hball (hseg x hx)
      exact hr ⟨s, rfl⟩
    · have hcls₀' : κ.trans (Path.Homotopic.Quotient.mk (P.subpath 0 t₀)) =
          pc.cls.trans (Path.Homotopic.Quotient.mk η₀) := hcls₀
      have hsub := Path.Homotopic.mk_subpath_trans_mk_subpath P 0 t₀ t
      show κ.trans (Path.Homotopic.Quotient.mk (P.subpath 0 t)) =
        pc.cls.trans (Path.Homotopic.Quotient.mk (η₀.trans (P.subpath t₀ t)))
      rw [← hsub, ← Path.Homotopic.Quotient.trans_assoc, hcls₀',
        Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.mk_trans]
  have hF0 : F 0 = ⟨f 0, κ⟩ := by
    show (⟨f 0, κ.trans (Path.Homotopic.Quotient.mk (P.subpath 0 0))⟩ : PathCover x₀) = _
    rw [Path.subpath_self]
    exact congrArg (PathCover.mk (f 0)) (Path.Homotopic.Quotient.trans_refl κ)
  have heq : (Γ : unitInterval → PathCover x₀) = F :=
    (pathCoverProj_isCoveringMap x₀).eq_of_comp_eq Γ.continuous hFc
      (funext fun u => by simp only [Function.comp_apply]; rw [hΓ]; rfl) 0 (h0.trans hF0.symm)
  have h1 := congrFun heq 1
  rw [h1]
  show (⟨f 1, κ.trans (Path.Homotopic.Quotient.mk (P.subpath 0 1))⟩ : PathCover x₀) = _
  rw [Path.subpath_zero_one]
  rfl

section IndexTwo

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
  [IsManifold 𝓘(ℂ) ω S] {x₀ : S} {K : Subgroup (FundamentalGroup S x₀)}
  [MulAction K (PathCover x₀)]
  (hsmul : ∀ (g : K) (pc : PathCover x₀),
      g • pc = pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc)

include hsmul in
/-- The projection descends to the quotient. -/
theorem s82bc_qmap :
    ∃ q : Quotient (MulAction.orbitRel K (PathCover x₀)) → S,
      ∀ e, q (Quotient.mk _ e) = pathCoverProj x₀ e := by
  refine ⟨Quotient.lift (pathCoverProj x₀) (fun a b hab => ?_), fun e => rfl⟩
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp hab
  replace hg : g • b = a := hg
  rw [← hg]
  exact s78no_proj_smul hsmul g b

include hsmul in
/-- A deck transformation by a class `γ` descends to the quotient when `K` is normal. -/
theorem s82bc_tau (hKn : K.Normal) (γ : FundamentalGroup S x₀) :
    ∃ τ : Quotient (MulAction.orbitRel K (PathCover x₀)) →
        Quotient (MulAction.orbitRel K (PathCover x₀)),
      ∀ e, τ (Quotient.mk _ e) = Quotient.mk _ (pathCoverDeck x₀ γ e) := by
  refine ⟨Quotient.lift (fun e => Quotient.mk _ (pathCoverDeck x₀ γ e)) (fun a b hab => ?_),
    fun e => rfl⟩
  obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp hab
  replace hg : g • b = a := hg
  have hk : γ⁻¹ * (g : FundamentalGroup S x₀) * γ ∈ K := by
    have := hKn.conj_mem (g : FundamentalGroup S x₀) g.2 γ⁻¹
    simpa using this
  apply Quotient.sound
  refine MulAction.orbitRel_apply.mpr ⟨⟨γ⁻¹ * (g : FundamentalGroup S x₀) * γ, hk⟩, ?_⟩
  show (⟨γ⁻¹ * (g : FundamentalGroup S x₀) * γ, hk⟩ : K) • pathCoverDeck x₀ γ b =
    pathCoverDeck x₀ γ a
  rw [hsmul, ← hg, hsmul]
  show pathCoverDeck x₀ ((γ⁻¹ * (g : FundamentalGroup S x₀) * γ)⁻¹ : FundamentalGroup S x₀)
      (pathCoverDeck x₀ γ b) =
    pathCoverDeck x₀ γ (pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) b)
  rw [s78no_deck_deck, s78no_deck_deck]
  congr 1
  group

end IndexTwo

section IndexTwoProps

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
  [IsManifold 𝓘(ℂ) ω S] {x₀ : S} {K : Subgroup (FundamentalGroup S x₀)}
  [MulAction K (PathCover x₀)]
  (hsmul : ∀ (g : K) (pc : PathCover x₀),
      g • pc = pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc)
  (γ : FundamentalGroup S x₀)
  (τ : Quotient (MulAction.orbitRel K (PathCover x₀)) →
        Quotient (MulAction.orbitRel K (PathCover x₀)))
  (hτ : ∀ e, τ (Quotient.mk _ e) = Quotient.mk _ (pathCoverDeck x₀ γ e))

include hsmul hτ in
theorem s82bc_tau_continuous : Continuous τ := by
  have hqm := (s78no_isQuotientCoveringMap hsmul).toIsQuotientMap
  rw [hqm.continuous_iff]
  have hd : Continuous (pathCoverDeck x₀ γ) := by
    obtain ⟨d, hd⟩ := exists_pathCoverDeck_diffeomorph x₀ γ
    rw [show pathCoverDeck x₀ γ = d from funext fun pc => (hd pc).symm]
    exact d.continuous
  have : τ ∘ Quotient.mk (MulAction.orbitRel K (PathCover x₀)) =
      Quotient.mk (MulAction.orbitRel K (PathCover x₀)) ∘ pathCoverDeck x₀ γ := funext hτ
  rw [this]
  exact continuous_quotient_mk'.comp hd

include hsmul hτ in
theorem s82bc_tau_involutive (hγ2 : γ * γ ∈ K) (y : Quotient (MulAction.orbitRel K (PathCover x₀))) :
    τ (τ y) = y := by
  obtain ⟨e, rfl⟩ := Quotient.exists_rep y
  rw [hτ, hτ]
  apply Quotient.sound
  refine MulAction.orbitRel_apply.mpr ⟨⟨(γ * γ)⁻¹, K.inv_mem hγ2⟩, ?_⟩
  show (⟨(γ * γ)⁻¹, K.inv_mem hγ2⟩ : K) • e = pathCoverDeck x₀ γ (pathCoverDeck x₀ γ e)
  rw [hsmul, s78no_deck_deck]
  simp

include hsmul hτ in
theorem s82bc_tau_free (hγK : γ ∉ K) (y : Quotient (MulAction.orbitRel K (PathCover x₀))) :
    τ y ≠ y := by
  obtain ⟨e, rfl⟩ := Quotient.exists_rep y
  rw [hτ]
  intro h
  obtain ⟨k, hk⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
  replace hk : k • e = pathCoverDeck x₀ γ e := hk
  rw [hsmul] at hk
  have h1 := congrArg (pathCoverDeck x₀ (k : FundamentalGroup S x₀)) hk
  rw [s78no_deck_deck, s78no_deck_deck] at h1
  rw [inv_mul_cancel] at h1
  have h1' : pathCoverDeck x₀ ((1 : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) e =
      pathCoverDeck x₀ (γ * (k : FundamentalGroup S x₀) : FundamentalGroup S x₀) e := by
    rw [inv_one]; exact h1
  rw [s78no_deck_one] at h1'
  have h1 := h1'
  have h2 : γ * (k : FundamentalGroup S x₀) = 1 := s78no_deck_free x₀ _ e h1.symm
  apply hγK
  have : γ = ((k : FundamentalGroup S x₀))⁻¹ := eq_inv_of_mul_eq_one_left h2
  rw [this]
  exact K.inv_mem k.2

include hsmul hτ in
theorem s82bc_tau_fibre (hKn : K.Normal) (hγK : γ ∉ K)
    (hγ3 : ∀ δ : FundamentalGroup S x₀, δ ∉ K → γ⁻¹ * δ ∈ K)
    (q : Quotient (MulAction.orbitRel K (PathCover x₀)) → S)
    (hq : ∀ e, q (Quotient.mk _ e) = pathCoverProj x₀ e)
    (y y' : Quotient (MulAction.orbitRel K (PathCover x₀))) (h : q y = q y') :
    y' = y ∨ y' = τ y := by
  obtain ⟨e, rfl⟩ := Quotient.exists_rep y
  obtain ⟨e', rfl⟩ := Quotient.exists_rep y'
  rw [hq, hq] at h
  obtain ⟨δ0, hδ⟩ := pathCoverDeck_transitive x₀ e e' h
  let δ : FundamentalGroup S x₀ := δ0
  by_cases hδK : δ ∈ K
  · left
    apply Quotient.sound
    refine MulAction.orbitRel_apply.mpr ⟨⟨δ⁻¹, K.inv_mem hδK⟩, ?_⟩
    show (⟨δ⁻¹, K.inv_mem hδK⟩ : K) • e = e'
    rw [hsmul, ← hδ]
    simp
    rfl
  · right
    rw [hτ]
    apply Quotient.sound
    have hk := hγ3 δ hδK
    refine MulAction.orbitRel_apply.mpr ⟨⟨(γ⁻¹ * δ)⁻¹, K.inv_mem hk⟩, ?_⟩
    show (⟨(γ⁻¹ * δ)⁻¹, K.inv_mem hk⟩ : K) • pathCoverDeck x₀ γ e = e'
    rw [hsmul, ← hδ, inv_inv, s78no_deck_deck]
    have hh : γ * (γ⁻¹ * δ) = δ := by group
    exact congrArg (fun c : FundamentalGroup S x₀ => pathCoverDeck x₀ c e) hh

end IndexTwoProps

theorem s82bc_lift_endpoint' {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (x₀ : S)
    {s t : S} (sg : Path s t) (κ : Path.Homotopic.Quotient x₀ s)
    (Γ : C(unitInterval, PathCover x₀)) (h0 : Γ 0 = ⟨s, κ⟩)
    (hΓ : ∀ u, pathCoverProj x₀ (Γ u) = sg u) :
    Γ 1 = ⟨t, κ.trans (Path.Homotopic.Quotient.mk sg)⟩ := by
  obtain ⟨⟨f, hf⟩, hs, ht⟩ := sg
  subst hs ht
  exact s82bc_lift_endpoint x₀ ⟨f, hf⟩ κ Γ h0 hΓ

theorem s82bc_cancel_l {S : Type u} [TopologicalSpace S] {x y w : S}
    (a : Path.Homotopic.Quotient x y) (b : Path.Homotopic.Quotient y w) :
    a.symm.trans (a.trans b) = b := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

theorem s82bc_cancel_r {S : Type u} [TopologicalSpace S] {x y w : S}
    (a : Path.Homotopic.Quotient x y) (b : Path.Homotopic.Quotient x w) :
    a.trans (a.symm.trans b) = b := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

section Mono

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
  [IsManifold 𝓘(ℂ) ω S] {x₀ : S} {K : Subgroup (FundamentalGroup S x₀)}
  [MulAction K (PathCover x₀)]
  (hsmul : ∀ (g : K) (pc : PathCover x₀),
      g • pc = pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc)

include hsmul in
/-- **Monodromy of the double cover.**  A lift of the loop `β` at `z` is closed only if the loop
`a β a⁻¹` lies in `K`. -/
theorem s82bc_mono (hKn : K.Normal)
    (q : Quotient (MulAction.orbitRel K (PathCover x₀)) → S)
    (hq : ∀ e, q (Quotient.mk _ e) = pathCoverProj x₀ e) (hcov : IsCoveringMap q)
    {z : S} (a : Path x₀ z) (β : Path z z)
    (hβ : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans β).trans a.symm)) ∉ K)
    (Γ : C(unitInterval, Quotient (MulAction.orbitRel K (PathCover x₀))))
    (hΓ : ∀ t, q (Γ t) = β t) : Γ 1 ≠ Γ 0 := by
  intro h
  obtain ⟨e₀, he₀⟩ := Quotient.exists_rep (Γ 0)
  have hpt : e₀.pt = z := by
    have h1 := hΓ 0
    rw [← he₀, hq] at h1
    exact h1.trans β.source
  obtain ⟨pt, c⟩ := e₀
  have hpt' : pt = z := hpt
  subst hpt'
  have hcovP := pathCoverProj_isCoveringMap x₀
  let Γ' := hcovP.liftPath (β : C(unitInterval, S)) ⟨pt, c⟩ β.source
  have hΓ'0 : Γ' 0 = ⟨pt, c⟩ := hcovP.liftPath_zero _ _ _
  have hΓ'p : ∀ u, pathCoverProj x₀ (Γ' u) = β u := fun u =>
    congrFun (hcovP.liftPath_lifts (β : C(unitInterval, S)) ⟨pt, c⟩ β.source) u
  have h1 := s82bc_lift_endpoint' x₀ β c Γ' hΓ'0 hΓ'p
  have hmk : Continuous (fun u => (Quotient.mk (MulAction.orbitRel K (PathCover x₀)) (Γ' u))) :=
    continuous_quotient_mk'.comp Γ'.continuous
  have hΓeq : (fun u => (Quotient.mk (MulAction.orbitRel K (PathCover x₀)) (Γ' u))) = Γ :=
    hcov.eq_of_comp_eq hmk Γ.continuous
      (funext fun u => by
        simp only [Function.comp_apply]
        rw [hq, hΓ u]; exact hΓ'p u) 0 (by
        show Quotient.mk (MulAction.orbitRel K (PathCover x₀)) (Γ' 0) = Γ 0
        rw [hΓ'0]; exact he₀)
  have hΓ1 : Γ 1 = Quotient.mk _ (⟨pt, c.trans (Path.Homotopic.Quotient.mk β)⟩ : PathCover x₀) := by
    rw [← congrFun hΓeq 1]
    show Quotient.mk (MulAction.orbitRel K (PathCover x₀)) (Γ' 1) = _
    rw [h1]
  rw [hΓ1, ← he₀] at h
  obtain ⟨k, hk⟩ := MulAction.orbitRel_apply.mp (Quotient.exact h)
  replace hk : k • (⟨pt, c⟩ : PathCover x₀) = ⟨pt, c.trans (Path.Homotopic.Quotient.mk β)⟩ := hk
  rw [hsmul] at hk
  simp only [pathCoverDeck, PathCover.mk.injEq, heq_eq_eq, true_and] at hk
  have hLc : (c.trans (Path.Homotopic.Quotient.mk β)).trans c.symm =
      ((k : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) := by
    rw [← hk, Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.trans_refl]
  have hLa : Path.Homotopic.Quotient.mk ((a.trans β).trans a.symm) =
      (((Path.Homotopic.Quotient.mk a).trans c.symm).trans
        ((c.trans (Path.Homotopic.Quotient.mk β)).trans c.symm)).trans
        (c.trans (Path.Homotopic.Quotient.mk a).symm) := by
    rw [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm]
    simp only [Path.Homotopic.Quotient.trans_assoc, s82bc_cancel_l, s82bc_cancel_r]
  let e : FundamentalGroup S x₀ := (Path.Homotopic.Quotient.mk a).trans c.symm
  let e' : FundamentalGroup S x₀ := c.trans (Path.Homotopic.Quotient.mk a).symm
  have hee' : e * e' = 1 := by
    show e'.trans e = Path.Homotopic.Quotient.refl x₀
    show (c.trans (Path.Homotopic.Quotient.mk a).symm).trans
      ((Path.Homotopic.Quotient.mk a).trans c.symm) = _
    simp only [Path.Homotopic.Quotient.trans_assoc, s82bc_cancel_l, s82bc_cancel_r,
      Path.Homotopic.Quotient.trans_symm]
  have hinv : e⁻¹ = e' := inv_eq_of_mul_eq_one_right hee'
  have hmem := hKn.conj_mem ((k : FundamentalGroup S x₀)⁻¹) (K.inv_mem k.2) e⁻¹
  apply hβ
  have heq : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk ((a.trans β).trans a.symm)) =
      e⁻¹ * (k : FundamentalGroup S x₀)⁻¹ * e⁻¹⁻¹ := by
    rw [inv_inv, hinv]
    show Path.Homotopic.Quotient.mk ((a.trans β).trans a.symm) = _
    rw [hLa, hLc]
    exact Path.Homotopic.Quotient.trans_assoc e (((k : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀)) e'
  rw [heq]
  exact hmem

end Mono

/-- In a group with an index-two subgroup, two elements outside the subgroup differ by an element
of the subgroup. -/
theorem s82bc_two_cosets {G : Type*} [Group G] (K : Subgroup G) (hK : K.index = 2) {x y : G}
    (hx : x ∉ K) (hy : y ∉ K) : x⁻¹ * y ∈ K := by
  have hcard : Nat.card (G ⧸ K) = 2 := hK
  obtain ⟨u, v, huv, hset⟩ := Nat.card_eq_two_iff.mp hcard
  have hmem : ∀ w : G ⧸ K, w = u ∨ w = v := by
    intro w
    have : w ∈ ({u, v} : Set (G ⧸ K)) := by rw [hset]; exact Set.mem_univ w
    simpa using this
  have h1x : (QuotientGroup.mk 1 : G ⧸ K) ≠ QuotientGroup.mk x := by
    intro h
    apply hx
    have := QuotientGroup.eq.mp h
    simpa using this
  have h1y : (QuotientGroup.mk 1 : G ⧸ K) ≠ QuotientGroup.mk y := by
    intro h
    apply hy
    have := QuotientGroup.eq.mp h
    simpa using this
  have hxy : (QuotientGroup.mk x : G ⧸ K) = QuotientGroup.mk y := by
    rcases hmem (QuotientGroup.mk 1) with h | h <;> rcases hmem (QuotientGroup.mk x) with h' | h' <;>
      rcases hmem (QuotientGroup.mk y) with h'' | h'' <;> simp_all
  exact QuotientGroup.eq.mp hxy

section Final

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
  [IsManifold 𝓘(ℂ) ω S] [ConnectedSpace S]

/-- **The double cover attached to an index-two subgroup of `π₁`.** -/
theorem s82bc_index_two_cover (x₀ : S) (K : Subgroup (FundamentalGroup S x₀)) (hK : K.index = 2) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace ℂ Y) (q : Y → S) (τ : Y → Y),
      T2Space Y ∧ IsManifold 𝓘(ℂ) ω Y ∧ PathConnectedSpace Y ∧ IsCoveringMap q ∧
      (∀ y y', y' ∈ (chartAt ℂ y).source → q y' ∈ (chartAt ℂ (q y)).source ∧
        chartAt ℂ (q y) (q y') = chartAt ℂ y y') ∧
      (∀ s, (q ⁻¹' {s}).ncard = 2) ∧ Continuous τ ∧ (∀ y, τ (τ y) = y) ∧ (∀ y, q (τ y) = q y) ∧
      (∀ y, τ y ≠ y) ∧
      (∀ (z : S) (a : Path x₀ z) (β : Path z z),
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans β).trans a.symm)) ∉ K →
        ∀ Γ : C(unitInterval, Y), (∀ t, q (Γ t) = β t) → Γ 1 ≠ Γ 0) := by
  classical
  have hKn : K.Normal := Subgroup.normal_of_index_eq_two hK
  letI : MulAction K (PathCover x₀) :=
    { smul := fun g pc =>
        pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc
      one_smul := fun pc => by
        change pathCoverDeck x₀ (((1 : K) : FundamentalGroup S x₀)⁻¹ :
          FundamentalGroup S x₀) pc = pc
        rw [OneMemClass.coe_one]; exact s78no_deck_one x₀ pc
      mul_smul := fun g h pc => by
        change pathCoverDeck x₀ (((g * h : K) : FundamentalGroup S x₀)⁻¹ :
          FundamentalGroup S x₀) pc = _
        rw [Subgroup.coe_mul]; exact s78no_deck_inv_mul x₀ g h pc }
  have hsmul : ∀ (g : K) (pc : PathCover x₀),
      g • pc = pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc :=
    fun _ _ => rfl
  obtain ⟨cs, hman, hchart⟩ := s82bc_quotient_manifold hsmul
  obtain ⟨q, hq⟩ := s82bc_qmap hsmul
  obtain ⟨γ, hγK⟩ : ∃ γ : FundamentalGroup S x₀, γ ∉ K := by
    by_contra h
    push Not at h
    have : K = ⊤ := Subgroup.eq_top_iff' K |>.mpr h
    rw [this, Subgroup.index_top] at hK
    omega
  have hγ3 : ∀ δ : FundamentalGroup S x₀, δ ∉ K → γ⁻¹ * δ ∈ K :=
    fun δ hδ => s82bc_two_cosets K hK hγK hδ
  have hγ2 : γ * γ ∈ K := by
    have := s82bc_two_cosets K hK (x := γ⁻¹) (y := γ) (fun h => hγK (by simpa using K.inv_mem h)) hγK
    simpa using this
  obtain ⟨τ, hτ⟩ := s82bc_tau hsmul hKn γ
  have hcont := s82bc_tau_continuous hsmul γ τ hτ
  have hinv := s82bc_tau_involutive hsmul γ τ hτ hγ2
  have hfree := s82bc_tau_free hsmul γ τ hτ hγK
  have hfib := s82bc_tau_fibre hsmul γ τ hτ hKn hγK hγ3 q hq
  have hqτ : ∀ y, q (τ y) = q y := by
    intro y
    obtain ⟨e, rfl⟩ := Quotient.exists_rep y
    rw [hτ, hq, hq]; rfl
  have hsurjmk : Function.Surjective (Quotient.mk (MulAction.orbitRel K (PathCover x₀))) :=
    fun y => Quotient.exists_rep y
  haveI : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace ℂ S
  haveI : PathConnectedSpace S := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  have hqs : Function.Surjective q := by
    intro s
    exact ⟨Quotient.mk _ (⟨s, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ s)⟩ :
      PathCover x₀), by rw [hq]; rfl⟩
  have hT2 : T2Space (Quotient (MulAction.orbitRel K (PathCover x₀))) := s78no_quotient_t2 hsmul
  have hlh : IsLocalHomeomorph q := by
    have hmk := (s78no_isQuotientCoveringMap hsmul).isLocalHomeomorph
    have hcomp : IsLocalHomeomorph (q ∘ Quotient.mk (MulAction.orbitRel K (PathCover x₀))) := by
      have : q ∘ Quotient.mk (MulAction.orbitRel K (PathCover x₀)) = pathCoverProj x₀ :=
        funext hq
      rw [this]
      exact (pathCoverProj_isCoveringMap x₀).isLocalHomeomorph
    have := IsLocalHomeomorphOn.of_comp_right (s := (Set.univ : Set (PathCover x₀)))
      hcomp.isLocalHomeomorphOn hmk.isLocalHomeomorphOn
    have himg : Quotient.mk (MulAction.orbitRel K (PathCover x₀)) '' (Set.univ : Set (PathCover x₀)) =
        Set.univ := by
      rw [Set.image_univ]; exact hsurjmk.range_eq
    rw [himg] at this
    exact isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr this
  have hcov : IsCoveringMap q :=
    s82bc_covering_of_involution q τ hlh hqs hcont hinv hqτ hfree hfib
  haveI : PathConnectedSpace (PathCover x₀) := pathConnectedSpace_pathCover x₀
  have hpc : PathConnectedSpace (Quotient (MulAction.orbitRel K (PathCover x₀))) :=
    hsurjmk.pathConnectedSpace continuous_quotient_mk'
  refine ⟨_, inferInstance, cs, q, τ, hT2, hman, hpc, hcov, hchart q hq, ?_, hcont, hinv, hqτ,
    hfree, ?_⟩
  · intro s
    obtain ⟨y₀, rfl⟩ := hqs s
    have : q ⁻¹' {q y₀} = {y₀, τ y₀} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_insert_iff]
      constructor
      · intro h; exact hfib y₀ y h.symm |>.imp id id
      · rintro (rfl | rfl)
        · rfl
        · exact (hqτ y₀)
    rw [this]
    exact Set.ncard_pair (hfree y₀).symm
  · intro z a β hβ Γ hΓ
    exact s82bc_mono hsmul hKn q hq hcov a β hβ Γ hΓ

end Final

end LiZhongQC
