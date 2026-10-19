import RiemannDynamics.Uniformization.Perron.PathCover
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

/-!
# Finite-index covers of a closed Riemann surface

For a closed Riemann surface `S` and a finite-index subgroup `K ≤ π₁(S, x₀)`, the quotient
`X_K = PathCover x₀ / K` of the universal path cover by `K` (acting through deck transformations)
is a closed Riemann surface with `π₁(X_K) ≅ Kᵐᵒᵖ` (`s78no_finiteIndex_cover`).

* `s78no_isQuotientCoveringMap`: `PathCover x₀ → X_K` is a quotient covering map (free action,
  local injectivity of the projection); `π₁` then comes from Mathlib's
  `IsQuotientCoveringMap.fundamentalGroupEquiv` (the path cover is simply connected).
* `s78no_quotient_t2`: Hausdorff, by unique path lifting.
* `s78no_quotient_compact`: compact, by finitely many compact local lifts and coset representatives.
* `s78no_quotient_manifold`: charts are local inverses of the quotient map followed by charts of the
  path cover; transitions agree locally with analytic deck transformations.
-/

open Set Topology Filter
open scoped Manifold ContDiff

noncomputable section
namespace LiZhongQC
universe u

open RiemannDynamics

section Action

variable {S : Type u} [TopologicalSpace S] (x₀ : S)

/-- Deck transformations by inverses compose like a left action. -/
theorem s78no_deck_inv_mul (g h : FundamentalGroup S x₀) (pc : PathCover x₀) :
    pathCoverDeck x₀ ((g * h)⁻¹ : FundamentalGroup S x₀) pc =
      pathCoverDeck x₀ (g⁻¹ : FundamentalGroup S x₀) (pathCoverDeck x₀ (h⁻¹ : FundamentalGroup S x₀) pc) := by
  obtain ⟨pt, cls⟩ := pc
  simp only [pathCoverDeck, PathCover.mk.injEq, heq_eq_eq, true_and]
  rw [mul_inv_rev, FundamentalGroup.mul_def]
  exact Path.Homotopic.Quotient.trans_assoc (g⁻¹ : FundamentalGroup S x₀)
    (h⁻¹ : FundamentalGroup S x₀) cls

/-- The deck transformation of the trivial loop is the identity. -/
theorem s78no_deck_one (pc : PathCover x₀) :
    pathCoverDeck x₀ ((1 : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc = pc := by
  obtain ⟨pt, cls⟩ := pc
  simp only [pathCoverDeck, FundamentalGroup.one_def]
  congr 1
  exact Path.Homotopic.Quotient.refl_trans cls

/-- Deck transformations act freely. -/
theorem s78no_deck_free (γ : FundamentalGroup S x₀) (pc : PathCover x₀)
    (h : pathCoverDeck x₀ γ pc = pc) : γ = 1 := by
  obtain ⟨pt, cls⟩ := pc
  simp only [pathCoverDeck, PathCover.mk.injEq, heq_eq_eq, true_and] at h
  have h2 := congrArg (fun c => Path.Homotopic.Quotient.trans c cls.symm) h
  simp only [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl] at h2
  exact h2

/-- Deck transformations compose (with the group law of `π₁`). -/
theorem s78no_deck_deck (a b : FundamentalGroup S x₀) (pc : PathCover x₀) :
    pathCoverDeck x₀ a (pathCoverDeck x₀ b pc) = pathCoverDeck x₀ (b * a) pc := by
  obtain ⟨pt, cls⟩ := pc
  simp only [pathCoverDeck, PathCover.mk.injEq, heq_eq_eq, true_and]
  rw [FundamentalGroup.mul_def]
  exact (Path.Homotopic.Quotient.trans_assoc a b cls).symm

end Action

section Quotient

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
  [IsManifold 𝓘(ℂ) ω S] {x₀ : S} {K : Subgroup (FundamentalGroup S x₀)}
  [MulAction K (PathCover x₀)]

/-- The action preserves the projection. -/
theorem s78no_proj_smul
    (hsmul : ∀ (g : K) (pc : PathCover x₀),
      g • pc = pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc)
    (g : K) (pc : PathCover x₀) : pathCoverProj x₀ (g • pc) = pathCoverProj x₀ pc := by
  rw [hsmul]; rfl

/-- The action is free. -/
theorem s78no_smul_free
    (hsmul : ∀ (g : K) (pc : PathCover x₀),
      g • pc = pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc)
    (g : K) (pc : PathCover x₀) (h : g • pc = pc) : g = 1 := by
  rw [hsmul] at h
  have h1 := s78no_deck_free x₀ _ pc h
  rw [inv_eq_one] at h1
  exact Subtype.ext h1

/-- Each group element acts by an analytic diffeomorphism, in particular continuously. -/
theorem s78no_continuous_smul
    (hsmul : ∀ (g : K) (pc : PathCover x₀),
      g • pc = pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc)
    (g : K) : ∃ e : PathCover x₀ ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯ PathCover x₀, ∀ pc, e pc = g • pc := by
  obtain ⟨e, he⟩ := exists_pathCoverDeck_diffeomorph x₀
    ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀)
  exact ⟨e, fun pc => by rw [he, hsmul]⟩

/-- **The quotient of the path cover by `K` is a quotient covering map.** -/
theorem s78no_isQuotientCoveringMap
    (hsmul : ∀ (g : K) (pc : PathCover x₀),
      g • pc = pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc) :
    IsQuotientCoveringMap (Quotient.mk (MulAction.orbitRel K (PathCover x₀))) K where
  toIsQuotientMap := isQuotientMap_quotient_mk'
  toContinuousConstSMul := ⟨fun g => by
    obtain ⟨e, he⟩ := s78no_continuous_smul hsmul g
    have : (fun pc => g • pc) = e := funext fun pc => (he pc).symm
    rw [this]; exact e.continuous⟩
  apply_eq_iff_mem_orbit := by
    intro e₁ e₂
    rw [Quotient.eq]
    exact MulAction.orbitRel_apply
  disjoint e := by
    obtain ⟨φ, heφ, hφ⟩ := (pathCoverProj_isCoveringMap x₀).isLocalHomeomorph e
    refine ⟨φ.source, φ.open_source.mem_nhds heφ, fun g hg => ?_⟩
    obtain ⟨q, ⟨u, hu, rfl⟩, hq⟩ := hg
    have hproj : φ (g • u) = φ u := by
      rw [← hφ]; exact s78no_proj_smul hsmul g u
    exact s78no_smul_free hsmul g u (φ.injOn hq hu hproj)

/-- The fundamental group of the quotient is `Kᵐᵒᵖ` (the path cover is simply connected). -/
theorem s78no_quotient_pi1 [ConnectedSpace S]
    (hsmul : ∀ (g : K) (pc : PathCover x₀),
      g • pc = pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc) :
    ∃ x : Quotient (MulAction.orbitRel K (PathCover x₀)),
      Nonempty (FundamentalGroup (Quotient (MulAction.orbitRel K (PathCover x₀))) x ≃* Kᵐᵒᵖ) := by
  haveI := simplyConnectedSpace_pathCover x₀
  refine ⟨Quotient.mk _ (pathCoverBase x₀), ⟨?_⟩⟩
  exact (s78no_isQuotientCoveringMap hsmul).fundamentalGroupEquiv ⟨pathCoverBase x₀, rfl⟩

/-- The quotient is connected. -/
theorem s78no_quotient_connected [ConnectedSpace S] :
    ConnectedSpace (Quotient (MulAction.orbitRel K (PathCover x₀))) := by
  haveI := pathConnectedSpace_pathCover x₀
  infer_instance

/-- **The quotient is Hausdorff**: points over distinct base points are separated through the
base; two points over the same base point are separated by the images of local sheets, using
uniqueness of path lifting for the covering `PathCover x₀ → S`. -/
theorem s78no_quotient_t2
    (hsmul : ∀ (g : K) (pc : PathCover x₀),
      g • pc = pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc) :
    T2Space (Quotient (MulAction.orbitRel K (PathCover x₀))) := by
  haveI : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace ℂ S
  have hq := s78no_isQuotientCoveringMap hsmul
  have hcov := pathCoverProj_isCoveringMap x₀
  have hopen : IsOpenMap (Quotient.mk (MulAction.orbitRel K (PathCover x₀))) :=
    hq.isLocalHomeomorph.isOpenMap
  refine ⟨fun y y' hne => ?_⟩
  obtain ⟨e, rfl⟩ := Quotient.exists_rep y
  obtain ⟨e', rfl⟩ := Quotient.exists_rep y'
  have horb : ∀ g : K, g • e ≠ e' := by
    intro g hg
    apply hne
    exact Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g, hg⟩) |>.symm
  by_cases hs : pathCoverProj x₀ e = pathCoverProj x₀ e'
  · -- same base point
    obtain ⟨φ, heφ, hφ⟩ := hcov.isLocalHomeomorph e
    obtain ⟨φ', heφ', hφ'⟩ := hcov.isLocalHomeomorph e'
    set s := pathCoverProj x₀ e with hsdef
    have hsφ : s ∈ φ.target := by rw [hsdef, hφ]; exact φ.map_source heφ
    have hsφ' : s ∈ φ'.target := by rw [hs, hφ']; exact φ'.map_source heφ'
    have hN : φ.target ∩ φ'.target ∈ 𝓝 s :=
      inter_mem (φ.open_target.mem_nhds hsφ) (φ'.open_target.mem_nhds hsφ')
    obtain ⟨W, ⟨hWs, hWpc⟩, hWN⟩ := (path_connected_basis s).mem_iff.mp hN
    set A := φ.source ∩ φ ⁻¹' interior W with hA
    set A' := φ'.source ∩ φ' ⁻¹' interior W with hA'
    have hAo : IsOpen A := φ.isOpen_inter_preimage isOpen_interior
    have hA'o : IsOpen A' := φ'.isOpen_inter_preimage isOpen_interior
    have heA : e ∈ A := ⟨heφ, by rw [mem_preimage, ← hφ]; exact mem_interior_iff_mem_nhds.mpr hWs⟩
    have he'A' : e' ∈ A' :=
      ⟨heφ', by rw [mem_preimage, ← hφ', ← hs]; exact mem_interior_iff_mem_nhds.mpr hWs⟩
    refine ⟨_ '' A, _ '' A', hopen A hAo, hopen A' hA'o, ⟨e, heA, rfl⟩, ⟨e', he'A', rfl⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨a', ha', haa'⟩
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact haa')
    replace hg : g • a = a' := hg
    -- `a' = g • a`; both lie over `w := p a ∈ W`
    set w := pathCoverProj x₀ a with hw
    have hwW : w ∈ W := interior_subset (by rw [hw, hφ]; exact ha.2)
    have hφa : φ.symm w = a := by rw [hw, hφ]; exact φ.left_inv ha.1
    have hpa' : pathCoverProj x₀ a' = w := by rw [← hg, s78no_proj_smul hsmul]
    have hφa' : φ'.symm w = a' := by rw [← hpa', hφ']; exact φ'.left_inv ha'.1
    obtain ⟨β, hβ⟩ := hWpc.joinedIn s (mem_of_mem_nhds hWs) w hwW
    obtain ⟨gc, hgc⟩ := s78no_continuous_smul hsmul g
    have hc1 : Continuous fun t => g • φ.symm (β t) := by
      have : Continuous fun t => φ.symm (β t) :=
        φ.continuousOn_symm.comp_continuous β.continuous fun t => (hWN (hβ t)).1
      simp_rw [← hgc]; exact gc.continuous.comp this
    have hc2 : Continuous fun t => φ'.symm (β t) :=
      φ'.continuousOn_symm.comp_continuous β.continuous fun t => (hWN (hβ t)).2
    have hcomp : pathCoverProj x₀ ∘ (fun t => g • φ.symm (β t)) =
        pathCoverProj x₀ ∘ (fun t => φ'.symm (β t)) := by
      funext t
      simp only [Function.comp_apply, s78no_proj_smul hsmul]
      conv_lhs => rw [hφ, φ.right_inv (hWN (hβ t)).1]
      conv_rhs => rw [hφ', φ'.right_inv (hWN (hβ t)).2]
    have heq := hcov.eq_of_comp_eq hc1 hc2 hcomp 1 (by
      simp only [Path.target]; rw [hφa, hφa', hg])
    have h0 := congrFun heq 0
    simp only [Path.source] at h0
    have hφs : φ.symm s = e := by rw [hsdef, hφ]; exact φ.left_inv heφ
    have hφ's : φ'.symm s = e' := by rw [hs, hφ']; exact φ'.left_inv heφ'
    rw [hφs, hφ's] at h0
    exact horb g h0
  · -- distinct base points
    obtain ⟨u, v, hu, hv, hsu, hsv, huv⟩ := t2_separation hs
    refine ⟨_ '' (pathCoverProj x₀ ⁻¹' u), _ '' (pathCoverProj x₀ ⁻¹' v),
      hopen _ (hu.preimage hcov.continuous), hopen _ (hv.preimage hcov.continuous),
      ⟨e, hsu, rfl⟩, ⟨e', hsv, rfl⟩, ?_⟩
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact hab)
    replace hg : g • a = b := hg
    have : pathCoverProj x₀ b = pathCoverProj x₀ a := by rw [← hg, s78no_proj_smul hsmul]
    exact Set.disjoint_left.mp huv ha (by rw [← this]; exact hb)

/-- **The quotient by a finite-index subgroup is compact**: finitely many compact local lifts
cover `S`, and finitely many coset representatives move them onto every `K`-orbit. -/
theorem s78no_quotient_compact [CompactSpace S] [ConnectedSpace S] [K.FiniteIndex]
    (hsmul : ∀ (g : K) (pc : PathCover x₀),
      g • pc = pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc) :
    CompactSpace (Quotient (MulAction.orbitRel K (PathCover x₀))) := by
  classical
  haveI : LocallyCompactSpace S := ChartedSpace.locallyCompactSpace ℂ S
  haveI : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace ℂ S
  haveI : PathConnectedSpace S := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  have hcov := pathCoverProj_isCoveringMap x₀
  have hlift : ∀ s : S, ∃ e : PathCover x₀, pathCoverProj x₀ e = s := fun s =>
    ⟨⟨s, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ s)⟩, rfl⟩
  have hloc : ∀ s : S, ∃ C : Set S, IsCompact C ∧ s ∈ interior C ∧
      ∃ F : Set (PathCover x₀), IsCompact F ∧ C ⊆ pathCoverProj x₀ '' F := by
    intro s
    obtain ⟨e, he⟩ := hlift s
    obtain ⟨φ, heφ, hφ⟩ := hcov.isLocalHomeomorph e
    have hsφ : s ∈ φ.target := by rw [← he, hφ]; exact φ.map_source heφ
    obtain ⟨C, hC, hsC, hCt⟩ := exists_compact_subset φ.open_target hsφ
    refine ⟨C, hC, hsC, φ.symm '' C, hC.image_of_continuousOn (φ.continuousOn_symm.mono hCt), ?_⟩
    intro z hz
    exact ⟨φ.symm z, ⟨z, hz, rfl⟩, by rw [hφ]; exact φ.right_inv (hCt hz)⟩
  choose C hC hsC F hF hCF using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun s => interior (C s))
    (fun _ => isOpen_interior) (fun s _ => mem_iUnion.mpr ⟨s, hsC s⟩)
  set F0 := ⋃ s ∈ t, F s with hF0def
  have hF0 : IsCompact F0 := t.isCompact_biUnion (fun s _ => hF s)
  have hF0cov : ∀ z : S, ∃ f ∈ F0, pathCoverProj x₀ f = z := by
    intro z
    obtain ⟨s, hs, hz⟩ := mem_iUnion₂.mp (ht (mem_univ z))
    obtain ⟨f, hf, hfz⟩ := hCF s (interior_subset hz)
    exact ⟨f, mem_biUnion hs hf, hfz⟩
  have hdeckc : ∀ γ : FundamentalGroup S x₀, Continuous (pathCoverDeck x₀ γ) := by
    intro γ
    obtain ⟨d, hd⟩ := exists_pathCoverDeck_diffeomorph x₀ γ
    rw [show pathCoverDeck x₀ γ = d from funext fun pc => (hd pc).symm]
    exact d.continuous
  have hcover : (univ : Set (Quotient (MulAction.orbitRel K (PathCover x₀)))) ⊆
      ⋃ q : FundamentalGroup S x₀ ⧸ K,
        Quotient.mk _ '' (pathCoverDeck x₀ (Quotient.out q) '' F0) := by
    intro y _
    obtain ⟨e, rfl⟩ := Quotient.exists_rep y
    obtain ⟨f, hf, hfe⟩ := hF0cov (pathCoverProj x₀ e)
    obtain ⟨γ0, hγ⟩ := pathCoverDeck_transitive x₀ f e hfe
    set γ : FundamentalGroup S x₀ := γ0 with hγdef
    set q : FundamentalGroup S x₀ ⧸ K := (γ : FundamentalGroup S x₀ ⧸ K) with hqdef
    have hq : (Quotient.out q)⁻¹ * γ ∈ K := by
      apply QuotientGroup.eq.mp
      rw [QuotientGroup.out_eq']
    refine mem_iUnion.mpr ⟨q, ⟨_, ⟨f, hf, rfl⟩, ?_⟩⟩
    apply Quotient.sound
    change pathCoverDeck x₀ (Quotient.out q) f ∈ MulAction.orbit K e
    refine ⟨⟨(Quotient.out q)⁻¹ * γ, hq⟩, ?_⟩
    change (⟨(Quotient.out q)⁻¹ * γ, hq⟩ : K) • e = _
    rw [hsmul, ← hγ, s78no_deck_deck]
    congr 1
    simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left]
  exact ⟨(isCompact_iUnion fun q =>
    (hF0.image (hdeckc _)).image continuous_quotient_mk').of_isClosed_subset isClosed_univ hcover⟩

/-- **The quotient is a Riemann surface**: charts are local inverses of the quotient covering
followed by charts of the path cover; the transition maps agree locally with transitions through
an analytic deck transformation. -/
theorem s78no_quotient_manifold
    (hsmul : ∀ (g : K) (pc : PathCover x₀),
      g • pc = pathCoverDeck x₀ ((g : FundamentalGroup S x₀)⁻¹ : FundamentalGroup S x₀) pc) :
    ∃ _ : ChartedSpace ℂ (Quotient (MulAction.orbitRel K (PathCover x₀))),
      IsManifold 𝓘(ℂ) ω (Quotient (MulAction.orbitRel K (PathCover x₀))) := by
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
  refine ⟨cs, isManifold_of_contDiffOn _ _ _ ?_⟩
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

/-- **Finite-index covers of a closed Riemann surface.**  For every finite-index subgroup `K` of
`π₁(S, x₀)` there is a closed Riemann surface `X` with `π₁(X) ≅ Kᵐᵒᵖ`: the quotient of the
universal path cover by `K` acting through deck transformations. -/
theorem s78no_finiteIndex_cover (S : Type u) [TopologicalSpace S] [T2Space S] [CompactSpace S]
    [ConnectedSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] (x₀ : S)
    (K : Subgroup (FundamentalGroup S x₀)) [K.FiniteIndex] :
    ∃ (X : Type u) (_ : TopologicalSpace X) (_ : ChartedSpace ℂ X), T2Space X ∧
      CompactSpace X ∧ ConnectedSpace X ∧ IsManifold 𝓘(ℂ) ω X ∧
      ∃ x : X, Nonempty (FundamentalGroup X x ≃* Kᵐᵒᵖ) := by
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
  obtain ⟨cs, hman⟩ := s78no_quotient_manifold hsmul
  exact ⟨Quotient (MulAction.orbitRel K (PathCover x₀)), inferInstance, cs,
    s78no_quotient_t2 hsmul, s78no_quotient_compact hsmul, s78no_quotient_connected, hman,
    s78no_quotient_pi1 hsmul⟩

end LiZhongQC
