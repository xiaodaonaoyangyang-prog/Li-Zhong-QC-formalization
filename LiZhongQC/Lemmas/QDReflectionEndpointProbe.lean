import LiZhongQC.Lemmas.QDReflectionPunctureSeam
import Jacobians.CanonicalForms.SerreOmega0
import Jacobians.ProperDegree.ToSphereGeneral
import Jacobians.MappingDegree.FibresFiniteUnconditional

open Complex Set Metric Filter Topology
open Jacobians Jacobians.Dolbeault
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- Riemann--Roch supplies a nonconstant meromorphic function with no pole away
from a prescribed point. The prescribed point is supplied by the geometry. -/
theorem s31qr_prescribed_pole_function (X : ClosedRS.{u}) (P : X.carrier) :
    ∃ f : Jacobians.MeromorphicFunction X.carrier,
      f.orderAtPoint P < 0 ∧ (∀ x, x ≠ P → 0 ≤ f.orderAtPoint x) := by
  classical
  obtain ⟨𝔘, _hL, hR⟩ := exists_realizableLerayCover (X := X.carrier)
  let D : Divisor X.carrier := Finsupp.single P ((𝔘.h1Dim 0 : ℤ) + 1)
  have hDnn : ∀ x, 0 ≤ D x := by
    intro x
    simp only [D, Finsupp.single_apply]
    split <;> positivity
  let q1 : Jacobians.Dolbeault.lSysModule (X := X.carrier) D :=
    Submodule.Quotient.mk ⟨Jacobians.Dolbeault.constOneMero,
      Jacobians.Dolbeault.constOneMero_mem_linearSystem hDnn⟩
  have hq1 : q1 ≠ 0 := Jacobians.Dolbeault.constOneMero_class_ne_zero hDnn
  have hfr : 1 < Module.finrank ℂ (Jacobians.Dolbeault.lSysModule (X := X.carrier) D) := by
    have hh := Jacobians.Dolbeault.two_le_lDim_largeEffective hR P
    change 2 ≤ Module.finrank ℂ (Jacobians.Dolbeault.lSysModule (X := X.carrier) D) at hh
    omega
  obtain ⟨y, hy⟩ := exists_linearIndependent_pair_of_one_lt_finrank hfr hq1
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  let f : Jacobians.MeromorphicFunction X.carrier := g.val
  have hnc : ¬ Jacobians.Dolbeault.IsGermConstant f := by
    rintro ⟨c, hc⟩
    have he : (Submodule.Quotient.mk g :
        Jacobians.Dolbeault.lSysModule (X := X.carrier) D) = c • q1 := by
      change Submodule.Quotient.mk g =
        c • Submodule.Quotient.mk (⟨Jacobians.Dolbeault.constOneMero,
          Jacobians.Dolbeault.constOneMero_mem_linearSystem hDnn⟩ :
            Jacobians.linearSystem (X := X.carrier) D)
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      change ∀ x, (f - c • Jacobians.Dolbeault.constOneMero).orderW x = ⊤
      intro x
      rw [Jacobians.MeromorphicFunction.orderW_eq_top_iff]
      filter_upwards [hc x] with z hz
      change f.toFun z - c * 1 = 0
      rw [hz]
      ring
    have hrel : c • q1 + (-1 : ℂ) • (Submodule.Quotient.mk g :
        Jacobians.Dolbeault.lSysModule (X := X.carrier) D) = 0 := by
      rw [he]
      module
    exact one_ne_zero (neg_eq_zero.mp ((LinearIndependent.pair_iff.mp hy c (-1) hrel).2))
  have hoff : ∀ x, x ≠ P → 0 ≤ f.orderAtPoint x := by
    intro x hx
    have hDx : D x = 0 := by
      simp only [D, Finsupp.single_apply, if_neg (Ne.symm hx)]
    have ho := g.property x
    change (-(D x) : WithTop ℤ) ≤ f.orderW x at ho
    rw [hDx] at ho
    change 0 ≤ (f.orderW x).untop₀
    apply Jacobians.untop₀_nonneg_iff.2
    simpa using ho
  have hpole : f.orderAtPoint P < 0 := by
    by_contra hn
    have hall : ∀ x, 0 ≤ f.orderAtPoint x := by
      intro x
      by_cases hx : x = P
      · simpa only [hx] using le_of_not_gt hn
      · exact hoff x hx
    have hmem : f ∈ Jacobians.linearSystem (X := X.carrier) 0 := by
      intro x
      change (0 : WithTop ℤ) ≤ f.orderW x
      exact Jacobians.untop₀_nonneg_iff.1 (hall x)
    exact hnc (Jacobians.germ_eq_const_of_mem_linearSystem_zero f hmem)
  exact ⟨f, hpole, hoff⟩

/-- The normal, junk-free representative is holomorphic at every nonpole. -/
theorem s31qr_holoRepr_mdiffAt (X : ClosedRS.{u})
    (f : Jacobians.MeromorphicFunction X.carrier) {x : X.carrier}
    (hx : 0 ≤ f.orderAtPoint x) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f.holoRepr x := by
  have ha := f.analyticAt_holoRepr_chartPullback_of_orderNonneg hx
  refine (mdifferentiableWithinAt_univ ..).mp ?_
  apply DifferentiableWithinAt.mdifferentiableWithinAt_of_comp_extChartAt_symm
  have hd : DifferentiableWithinAt ℂ (f.holoRepr ∘ (chartAt ℂ x).symm)
      univ (chartAt ℂ x x) := ha.differentiableWithinAt
  have hept : (extChartAt 𝓘(ℂ) x) x = chartAt ℂ x x := by simp only [mfld_simps]
  have hesymm : ⇑(extChartAt 𝓘(ℂ) x).symm = ⇑(chartAt ℂ x).symm := by
    funext z
    simp only [mfld_simps]
  rw [hept, hesymm]
  apply hd.mono
  simp only [Set.preimage_univ, mfld_simps]
  exact Set.Subset.rfl

/-- A finite set containing all target cluster points, together with actual
connected source traces, gives an actual unique endpoint. The finite set will
be a fiber of the bounded meromorphic probe, not an assumed Pd correspondence. -/
theorem s31qr_endpoint_of_finite_cluster_locus
    {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    (i : A → X) (j : A → Y) (hj : Continuous j) (x : X)
    [NeBot (comap i (𝓝 x))] (K : Set Y) (hK : K.Finite)
    (hcluster : ∀ y, ClusterPt y (map j (comap i (𝓝 x))) → y ∈ K)
    (hconn : ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsPreconnected (i ⁻¹' V)) :
    ∃! y : Y, Tendsto j (comap i (𝓝 x)) (𝓝 y) := by
  classical
  have hunique : ∀ y z, ClusterPt y (map j (comap i (𝓝 x))) →
      ClusterPt z (map j (comap i (𝓝 x))) → y = z := by
    intro y z hy hz
    have hyK := hcluster y hy
    have hzK := hcluster z hz
    by_contra hyz
    have hdis : Disjoint ({y} : Set Y) (K \ {y}) := by simp
    obtain ⟨U, V, hU, hV, hyU, hrestV, hUV⟩ :=
      SeparatedNhds.of_finite (finite_singleton y) (hK.subset sdiff_subset) hdis
    have hcover : K ⊆ U ∪ V := by
      intro w hw
      by_cases hwy : w = y
      · subst w
        exact Or.inl (hyU (mem_singleton y))
      · exact Or.inr (hrestV ⟨hw, hwy⟩)
    have hnear : U ∪ V ∈ map j (comap i (𝓝 x)) :=
      (isCompact_univ.le_nhdsSet_of_clusterPt univ_mem
        (fun y _ hy => hcluster y hy)) ((hU.union hV).mem_nhdsSet.2 hcover)
    obtain ⟨W, hW, hWi⟩ := mem_comap.1 (mem_map.1 hnear)
    obtain ⟨B, hB, hBW, hBc⟩ := hconn W hW
    have hC : IsPreconnected (j '' (i ⁻¹' B)) := hBc.image j hj.continuousOn
    have hCs : j '' (i ⁻¹' B) ⊆ U ∪ V := by
      rintro w ⟨a, ha, rfl⟩
      exact hWi (hBW ha)
    have hCe : (j '' (i ⁻¹' B)) ∩ (U ∩ V) = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      rintro w ⟨_, hwU, hwV⟩
      exact disjoint_left.1 hUV hwU hwV
    have hCm : j '' (i ⁻¹' B) ∈ map j (comap i (𝓝 x)) :=
      image_mem_map (preimage_mem_comap hB)
    rcases (isPreconnected_iff_subset_of_disjoint.1 hC) U V hU hV hCs hCe with hCU | hCV
    · obtain ⟨w, hwV, hwC⟩ := (clusterPt_iff_nonempty.1 hz)
        (hV.mem_nhds (hrestV ⟨hzK, Ne.symm hyz⟩)) hCm
      exact disjoint_left.1 hUV (hCU hwC) hwV
    · obtain ⟨w, hwU, hwC⟩ := (clusterPt_iff_nonempty.1 hy)
        (hU.mem_nhds (hyU (mem_singleton y))) hCm
      exact disjoint_left.1 hUV hwU (hCV hwC)
  obtain ⟨y, hy⟩ := exists_clusterPt_of_compactSpace (map j (comap i (𝓝 x)))
  have ht : Tendsto j (comap i (𝓝 x)) (𝓝 y) :=
    tendsto_nhds_of_unique_mapClusterPt (fun z hz => hunique z y hz hy)
  exact ⟨y, ht, fun z hz => tendsto_nhds_unique hz ht⟩

/-- The mirror supplies an actual point outside the closure of the positive
half. The prescribed-pole function is consequently holomorphic and bounded
on that whole compact closure, including its seam and missing endpoints. -/
theorem s31qr_bounded_probe_on_half
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [Nonempty S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd) :
    ∃ (f : Jacobians.MeromorphicFunction Xd.carrier) (M : ℝ),
      (∃ b, f.orderAtPoint b < 0) ∧
      (∀ x ∈ closure (range ιd), 0 ≤ f.orderAtPoint x) ∧
      (∀ x ∈ closure (range ιd), ‖f.holoRepr x‖ ≤ M) := by
  classical
  let a : S := Classical.choice (inferInstance : Nonempty S)
  let b := J (ιd a)
  have hbM : b ∈ range (J ∘ ιd) := ⟨a, rfl⟩
  have hMo : IsOpen (range (J ∘ ιd)) :=
    (J.isOpenMap.comp hd.embedding.isOpenMap).isOpen_range
  have hbOut : b ∉ closure (range ιd) := by
    intro hb
    obtain ⟨y, hyM, hyP⟩ := mem_closure_iff_nhds.1 hb _ (hMo.mem_nhds hbM)
    exact Set.disjoint_left.1 hd.disjoint hyP hyM
  obtain ⟨f, hfb, hfoff⟩ := s31qr_prescribed_pole_function Xd b
  have hnonpole : ∀ x ∈ closure (range ιd), 0 ≤ f.orderAtPoint x := by
    intro x hx
    apply hfoff x
    intro he
    exact hbOut (he ▸ hx)
  have hfc : ContinuousOn f.holoRepr (closure (range ιd)) :=
    fun x hx => (s31qr_holoRepr_mdiffAt Xd f (hnonpole x hx)).continuousAt.continuousWithinAt
  have hnorm : ContinuousOn (fun x => ‖f.holoRepr x‖) (closure (range ιd)) :=
    continuous_norm.comp_continuousOn hfc
  obtain ⟨M, hM⟩ := (isClosed_closure : IsClosed (closure (range ιd))).isCompact.bddAbove_image hnorm
  exact ⟨f, M, ⟨b, hfb⟩, hnonpole, fun x hx => hM ⟨x, hx, rfl⟩⟩

/-- Every bounded holomorphic scalar function on the actual original surface
has a finite limit at an original puncture, even in the presence of holes.
The actual punctured parameter and inverse are constructed from F. -/
theorem s31qr_bounded_scalar_puncture_limit
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [Nonempty S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {p : F.X.carrier} (hp : p ∈ F.P)
    {h : S → ℂ} (hh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h)
    (M : ℝ) (hM : ∀ a, ‖h a‖ ≤ M) :
    ∃ c : ℂ, Tendsto h (comap F.ι (𝓝 p)) (𝓝 c) := by
  classical
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
  have hψd : ∀ z ∈ ball (b p) r \ {b p}, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ z :=
    fun z hz => s31eg_coordinate_inverse hAo hφi hφd (himg z hz)
  let k : ℂ → ℂ := h ∘ ψ
  have hkd : DifferentiableOn ℂ k (ball (b p) r \ {b p}) := by
    intro z hz
    exact (mdifferentiableAt_iff_differentiableAt.1
      ((hh (ψ z)).comp z (hψd z hz))).differentiableWithinAt
  have hkb : BddAbove (norm ∘ k '' (ball (b p) r \ {b p})) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨z, _hz, rfl⟩
    exact hM (ψ z)
  have hrem := Complex.differentiableOn_update_limUnder_of_bddAbove
    (ball_mem_nhds (b p) hr) hkd hkb
  have hkT : Tendsto k (𝓝[≠] (b p)) (𝓝 (limUnder (𝓝[≠] (b p)) k)) :=
    continuousAt_update_same.1
      ((hrem.differentiableAt (ball_mem_nhds (b p) hr)).continuousAt)
  have hφT : Tendsto φ (comap F.ι (𝓝 p)) (𝓝[≠] (b p)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨(b.continuousAt (mem_chart_source ℂ p)).tendsto.comp
      (show Tendsto F.ι (comap F.ι (𝓝 p)) (𝓝 p) from map_comap_le), ?_⟩
    have hAm : A ∈ comap F.ι (𝓝 p) :=
      preimage_mem_comap (b.open_source.mem_nhds (mem_chart_source ℂ p))
    filter_upwards [hAm] with a ha
    change φ a ≠ b p
    intro he
    have hep : F.ι a = p := b.injOn ha (mem_chart_source ℂ p) he
    have hpR : p ∈ range F.ι := ⟨a, hep⟩
    rw [F.range_ι] at hpR
    exact hpR (Or.inl hp)
  refine ⟨limUnder (𝓝[≠] (b p)) k, ?_⟩
  apply (hkT.comp hφT).congr'
  have hAm : A ∈ comap F.ι (𝓝 p) :=
    preimage_mem_comap (b.open_source.mem_nhds (mem_chart_source ℂ p))
  filter_upwards [hAm] with a ha
  change h (ψ (φ a)) = h a
  exact congrArg h (hφi.leftInvOn_invFunOn ha)

/-- Actual endpoint existence and Pd membership for every original puncture of
an arbitrary given double. A prescribed pole in the mirror produces a bounded
scalar probe; its finite sphere fiber contains all surface cluster points.
Connected actual puncture traces force a unique surface limit. -/
theorem s31qr_original_puncture_endpoint
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [Nonempty S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
    (hd : IsSchottkyDouble F Xd J ιd Pd)
    {p : F.X.carrier} (hp : p ∈ F.P) :
    ∃! q : Xd.carrier, q ∈ Pd ∧ Tendsto ιd (comap F.ι (𝓝 p)) (𝓝 q) := by
  letI := s31eg_puncture_neBot F hp
  obtain ⟨f, M, hfpole, hfreg, hfbound⟩ := s31qr_bounded_probe_on_half F hd
  have hscalar : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f.holoRepr ∘ ιd) :=
    fun s => (s31qr_holoRepr_mdiffAt Xd f
      (hfreg _ (subset_closure (mem_range_self s)))).comp s (hd.holomorphic s)
  have hb : ∀ s : S, ‖(f.holoRepr ∘ ιd) s‖ ≤ M :=
    fun s => hfbound _ (subset_closure (mem_range_self s))
  obtain ⟨c, hc⟩ := s31qr_bounded_scalar_puncture_limit F hp hscalar M hb
  have hfcont := f.continuous_toRiemannSphere
  have hfnc := f.toRiemannSphere_not_isConstant_of_exists_pole hfpole
  letI : ChartedSpace ℂ Jacobians.RiemannSphere := Jacobians.RiemannSphere.instChartedSpaceComplex
  have hfin : (f.toRiemannSphere ⁻¹' {((c : ℂ) : Jacobians.RiemannSphere)}).Finite :=
    Jacobians.Discharge.ContMDiff.Degree.fibres_finite f.toRiemannSphere
      f.contMDiff_toRiemannSphere hfnc _
  have hSphere : Tendsto (f.toRiemannSphere ∘ ιd) (comap F.ι (𝓝 p))
      (𝓝 ((c : ℂ) : Jacobians.RiemannSphere)) := by
    have hcoe : Continuous (fun z : ℂ => (z : Jacobians.RiemannSphere)) := OnePoint.continuous_coe
    apply (hcoe.continuousAt.tendsto.comp hc).congr'
    exact Eventually.of_forall fun s =>
      (f.toRiemannSphere_of_nonneg (hfreg _ (subset_closure (mem_range_self s)))).symm
  have hcluster : ∀ q, ClusterPt q (map ιd (comap F.ι (𝓝 p))) →
      q ∈ f.toRiemannSphere ⁻¹' {((c : ℂ) : Jacobians.RiemannSphere)} := by
    intro q hq
    have hh : ClusterPt (f.toRiemannSphere q)
        (map (f.toRiemannSphere ∘ ιd) (comap F.ι (𝓝 p))) :=
      (show MapClusterPt q (comap F.ι (𝓝 p)) ιd from hq).tendsto_comp hfcont.continuousAt
    exact eq_of_nhds_neBot (hh.mono hSphere)
  obtain ⟨q, hqT, _hqUnique⟩ := s31qr_endpoint_of_finite_cluster_locus
    F.ι ιd hd.embedding.continuous p _ hfin hcluster (s31eg_puncture_connected_traces F hp)
  refine ⟨q, ⟨s31qr_original_puncture_limit_mem_Pd F hd hp hqT, hqT⟩, ?_⟩
  intro q' hq'
  exact tendsto_nhds_unique hq'.2 hqT

end LiZhongQC
