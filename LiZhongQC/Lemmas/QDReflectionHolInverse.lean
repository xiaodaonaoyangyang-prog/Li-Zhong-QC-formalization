import LiZhongQC.Lemmas.QDReflectionTwoHalves
import LiZhongQC.Lemmas.Conformal

open Complex Set Metric Filter Topology
open scoped ContDiff Manifold
noncomputable section
namespace LiZhongQC

section HolInverse
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
  [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N] {f : M → N}

/-- An injective holomorphic map between Riemann surfaces is open: in charts it is an injective
analytic function, hence non-constant, hence open. -/
theorem s31inv_isOpenMap (hinj : Function.Injective f)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) : IsOpenMap f := by
  rw [isOpenMap_iff_nhds_le]
  intro p
  set χ := chartAt ℂ p with hχ
  set ψ := chartAt ℂ (f p) with hψ
  have hfc : Continuous f := hf.continuous
  have hp : p ∈ χ.source := mem_chart_source ℂ p
  have hfp : f p ∈ ψ.source := mem_chart_source ℂ (f p)
  let g : ℂ → ℂ := fun z => ψ (f (χ.symm z))
  let W : Set ℂ := χ.target ∩ χ.symm ⁻¹' (f ⁻¹' ψ.source)
  have hWo : IsOpen W := χ.isOpen_inter_preimage_symm (ψ.open_source.preimage hfc)
  have hpW : χ p ∈ W := ⟨χ.map_source hp, by
    show f (χ.symm (χ p)) ∈ ψ.source
    rw [χ.left_inv hp]; exact hfp⟩
  have hgd : ∀ z ∈ W, DifferentiableAt ℂ g z := by
    intro z hz
    have hq : χ.symm z ∈ χ.source := χ.map_target hz.1
    have h := ((s23_mdifferentiableAt_iff (x := p) (y := f p) hq hz.2).1 (hf _)).2
    rwa [χ.right_inv hz.1] at h
  have hginj : InjOn g W := by
    intro z₁ h₁ z₂ h₂ he
    have e1 : f (χ.symm z₁) = f (χ.symm z₂) := ψ.injOn h₁.2 h₂.2 he
    have e2 : χ.symm z₁ = χ.symm z₂ := hinj e1
    calc z₁ = χ (χ.symm z₁) := (χ.right_inv h₁.1).symm
      _ = χ (χ.symm z₂) := by rw [e2]
      _ = z₂ := χ.right_inv h₂.1
  have hgdOn : DifferentiableOn ℂ g W := fun z hz => (hgd z hz).differentiableWithinAt
  have hga : AnalyticAt ℂ g (χ p) := hgdOn.analyticAt (hWo.mem_nhds hpW)
  have hopen : 𝓝 (g (χ p)) ≤ map g (𝓝 (χ p)) := by
    rcases hga.eventually_constant_or_nhds_le_map_nhds with hc | hopen
    · exfalso
      obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ := ((hc.and (hWo.mem_nhds hpW)).filter_mono
        (nhdsWithin_le_nhds (s := {χ p}ᶜ))).and self_mem_nhdsWithin |>.exists
      exact hz3 (hginj hz2 hpW hz1)
    · exact hopen
  have hev : f =ᶠ[𝓝 p] fun q => ψ.symm (g (χ q)) := by
    filter_upwards [χ.open_source.mem_nhds hp,
      hfc.continuousAt.preimage_mem_nhds (ψ.open_source.mem_nhds hfp)] with q hq1 hq2
    change f q = ψ.symm (ψ (f (χ.symm (χ q))))
    rw [χ.left_inv hq1, ψ.left_inv hq2]
  rw [Filter.map_congr hev]
  have e1 : map χ (𝓝 p) = 𝓝 (χ p) := χ.map_nhds_eq hp
  have e2 : map (fun q => ψ.symm (g (χ q))) (𝓝 p) = map ψ.symm (map g (𝓝 (χ p))) := by
    rw [← e1, Filter.map_map, Filter.map_map]
    rfl
  rw [e2]
  have e3 : map ψ.symm (𝓝 (ψ (f p))) = 𝓝 (f p) := by
    have := ψ.symm.map_nhds_eq (x := ψ (f p)) (ψ.map_source hfp)
    rwa [ψ.left_inv hfp] at this
  have hgp : g (χ p) = ψ (f p) := by
    change ψ (f (χ.symm (χ p))) = ψ (f p)
    rw [χ.left_inv hp]
  rw [← e3]
  exact Filter.map_mono (by rw [← hgp]; exact hopen)

/-- An injective holomorphic map between Riemann surfaces is an open embedding. -/
theorem s31inv_isOpenEmbedding (hinj : Function.Injective f)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) : Topology.IsOpenEmbedding f :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hf.continuous hinj
    (s31inv_isOpenMap hinj hf)

/-- The inverse of the open embedding is holomorphic on the range. -/
theorem s31inv_symm_mdifferentiableOn [Nonempty M] (hinj : Function.Injective f)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      ((s31inv_isOpenEmbedding hinj hf).toOpenPartialHomeomorph f).symm (range f) :=
  fun _ hy => (s31qr_open_embedding_inverse (s31inv_isOpenEmbedding hinj hf) hf
    hy).mdifferentiableWithinAt

/-- `Function.invFun f` is holomorphic on the range of an injective holomorphic map. -/
theorem s31inv_invFun_mdifferentiableOn [Nonempty M] (hinj : Function.Injective f)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (Function.invFun f) (range f) := by
  have hemb := s31inv_isOpenEmbedding hinj hf
  intro y hy
  refine MDifferentiableAt.mdifferentiableWithinAt ?_
  refine (s31qr_open_embedding_inverse hemb hf hy).congr_of_eventuallyEq ?_
  filter_upwards [hemb.isOpenMap.isOpen_range.mem_nhds hy] with y' hy'
  obtain ⟨x, rfl⟩ := hy'
  rw [Function.leftInverse_invFun hinj x, hemb.toOpenPartialHomeomorph_left_inv f]

end HolInverse

end LiZhongQC
