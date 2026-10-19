import Mathlib
import LiZhongQC.Lemmas.HurwitzLocalLinearization
import LiZhongQC.Lemmas.HurwitzSurfaceIdentity
/-! Actual finite analytic surface stabilizers: invariant coordinate action and cyclicity.
The two imported archive modules are Root's already compiled, unchanged proof blocks. -/

open Set Filter
open scoped Manifold Topology ContDiff

namespace LiZhongQC

/-- The actual point stabilizer in a group of surface homeomorphisms. -/
def h84a_pointStabilizer {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) (p : X) : Subgroup G where
  carrier := {g | ρ g p = p}
  one_mem' := by
    change ρ 1 p = p
    rw [map_one, Homeomorph.one_apply]
  mul_mem' := by
    intro g h hg hh
    change ρ (g * h) p = p
    rw [map_mul, Homeomorph.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    change ρ (g⁻¹) p = p
    calc
      ρ (g⁻¹) p = ρ (g⁻¹) (ρ g p) := congrArg (ρ (g⁻¹)) hg.symm
      _ = (ρ (g⁻¹) * ρ g) p := (Homeomorph.mul_apply _ _ _).symm
      _ = p := by rw [← map_mul, inv_mul_cancel, map_one, Homeomorph.one_apply]

/-- Finite intersection of all translates of a chart source, followed by its
fixed-point connected component, produces one common invariant connected chart neighborhood. -/
theorem h84a_exists_invariant_chart_neighborhood
    {G X : Type*} [Group G] [Finite G] [TopologicalSpace X] [ChartedSpace ℂ X]
    (ρ : G →* (X ≃ₜ X)) (p : X) (hfix : ∀ g, ρ g p = p) :
    ∃ V : Set X, IsOpen V ∧ p ∈ V ∧ IsPreconnected V ∧
      V ⊆ (chartAt ℂ p).source ∧ ∀ g, MapsTo (ρ g) V V := by
  classical
  letI := Fintype.ofFinite G
  letI : LocallyConnectedSpace X := ChartedSpace.locallyConnectedSpace (H := ℂ) (M := X)
  let c := chartAt ℂ p
  let W : Set X := ⋂ g : G, (ρ g) ⁻¹' c.source
  have hWopen : IsOpen W :=
    isOpen_iInter_of_finite (fun g => c.open_source.preimage (ρ g).continuous)
  have hpW : p ∈ W := by
    refine mem_iInter.mpr ?_
    intro g
    change ρ g p ∈ c.source
    rw [hfix g]
    exact mem_chart_source ℂ p
  have hWsub : W ⊆ c.source := by
    intro y hy
    have h := (mem_iInter.mp hy) (1 : G)
    change ρ 1 y ∈ c.source at h
    simpa only [map_one, Homeomorph.one_apply] using h
  have hWinv : ∀ g, MapsTo (ρ g) W W := by
    intro g y hy
    refine mem_iInter.mpr ?_
    intro h
    change ρ h (ρ g y) ∈ c.source
    have h' := (mem_iInter.mp hy) (h * g)
    change ρ (h * g) y ∈ c.source at h'
    simpa only [map_mul, Homeomorph.mul_apply] using h'
  let V := connectedComponentIn W p
  have hVopen : IsOpen V := hWopen.connectedComponentIn
  have hpV : p ∈ V := mem_connectedComponentIn hpW
  have hVpc : IsPreconnected V := isPreconnected_connectedComponentIn
  have hVsubW : V ⊆ W := connectedComponentIn_subset W p
  have hVinv : ∀ g, MapsTo (ρ g) V V := by
    intro g y hy
    have hImagepc : IsPreconnected ((ρ g) '' V) :=
      hVpc.image (ρ g) (ρ g).continuous.continuousOn
    have hpImage : p ∈ (ρ g) '' V := ⟨p, hpV, hfix g⟩
    have hImageW : (ρ g) '' V ⊆ W := by
      rintro _ ⟨z, hz, rfl⟩
      exact hWinv g (hVsubW hz)
    have hImageV : (ρ g) '' V ⊆ V :=
      hImagepc.subset_connectedComponentIn hpImage hImageW
    exact hImageV ⟨y, hy, rfl⟩
  exact ⟨V, hVopen, hpV, hVpc, hVsubW.trans hWsub, hVinv⟩

/-- Restriction of a genuine invariant action to its invariant neighborhood. -/
def h84a_restrictedAction {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) (V : Set X) (hInv : ∀ g, MapsTo (ρ g) V V) :
    G →* Equiv.Perm V where
  toFun g :=
    { toFun := fun x => ⟨ρ g x, hInv g x.property⟩
      invFun := fun x => ⟨ρ (g⁻¹) x, hInv (g⁻¹) x.property⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change ρ (g⁻¹) (ρ g x) = x
        rw [← Homeomorph.mul_apply, ← map_mul, inv_mul_cancel, map_one, Homeomorph.one_apply]
      right_inv := by
        intro x
        apply Subtype.ext
        change ρ g (ρ (g⁻¹) x) = x
        rw [← Homeomorph.mul_apply, ← map_mul, mul_inv_cancel, map_one, Homeomorph.one_apply] }
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change ρ 1 x = x
    rw [map_one, Homeomorph.one_apply]
  map_mul' g h := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change ρ (g * h) x = ρ g (ρ h x)
    rw [map_mul, Homeomorph.mul_apply]

/-- The actual chart equivalence from V to its image, with source guards. -/
noncomputable def h84a_chartEquiv {X : Type*} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X ℂ) (V : Set X) (hV : V ⊆ c.source) :
    V ≃ (c '' V) where
  toFun x := ⟨c x, ⟨x, x.property, rfl⟩⟩
  invFun z := ⟨c.symm z, by
    rcases z.property with ⟨x, hx, hxz⟩
    rw [← hxz, c.left_inv (hV hx)]
    exact hx⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact c.left_inv (hV x.property)
  right_inv := by
    intro z
    apply Subtype.ext
    have hz : (z : ℂ) ∈ c.target := by
      rcases z.property with ⟨x, hx, hxz⟩
      rw [← hxz]
      exact c.mapsTo (hV hx)
    exact c.right_inv hz

/-- Coordinate conjugation followed by the canonical identity extension outside
the invariant coordinate domain. This constructs a permutation, not an assumed local action. -/
noncomputable def h84a_planarAction {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) (c : OpenPartialHomeomorph X ℂ)
    (V : Set X) (hV : V ⊆ c.source) (hInv : ∀ g, MapsTo (ρ g) V V) :
    G →* Equiv.Perm ℂ := by
  classical
  exact (Equiv.Perm.ofSubtype (p := fun z => z ∈ c '' V)).comp
    (((h84a_chartEquiv c V hV).permCongrHom.toMonoidHom).comp
      (h84a_restrictedAction ρ V hInv))

/-- On the coordinate domain the constructed action is exactly chart conjugation. -/
theorem h84a_planarAction_apply {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) (c : OpenPartialHomeomorph X ℂ)
    (V : Set X) (hV : V ⊆ c.source) (hInv : ∀ g, MapsTo (ρ g) V V)
    (g : G) {z : ℂ} (hz : z ∈ c '' V) :
    h84a_planarAction ρ c V hV hInv g z = c (ρ g (c.symm z)) := by
  classical
  change (Equiv.Perm.ofSubtype
    (((h84a_chartEquiv c V hV).permCongrHom.toMonoidHom).comp
      (h84a_restrictedAction ρ V hInv) g)) z = _
  rw [Equiv.Perm.ofSubtype_apply_of_mem _ hz]
  rfl

/-- The extension is genuinely identity outside the coordinate domain. -/
theorem h84a_planarAction_apply_outside {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) (c : OpenPartialHomeomorph X ℂ)
    (V : Set X) (hV : V ⊆ c.source) (hInv : ∀ g, MapsTo (ρ g) V V)
    (g : G) {z : ℂ} (hz : z ∉ c '' V) :
    h84a_planarAction ρ c V hV hInv g z = z := by
  classical
  change (Equiv.Perm.ofSubtype
    (((h84a_chartEquiv c V hV).permCongrHom.toMonoidHom).comp
      (h84a_restrictedAction ρ V hInv) g)) z = z
  exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hz

/-- The coordinate domain is invariant under every constructed permutation. -/
theorem h84a_planarAction_mapsTo {G X : Type*} [Group G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) (c : OpenPartialHomeomorph X ℂ)
    (V : Set X) (hV : V ⊆ c.source) (hInv : ∀ g, MapsTo (ρ g) V V)
    (g : G) : MapsTo (h84a_planarAction ρ c V hV hInv g) (c '' V) (c '' V) := by
  intro z hz
  have hxV : c.symm z ∈ V :=
    ((h84a_chartEquiv c V hV).symm ⟨z, hz⟩).property
  rw [h84a_planarAction_apply ρ c V hV hInv g hz]
  exact ⟨ρ g (c.symm z), hInv g hxV, rfl⟩

/-- Analyticity of the coordinate action follows from the genuine analytic surface
maps and chart atlas compatibility. The identity extension is only used outside U. -/
theorem h84a_planarAction_analytic
    {G X : Type*} [Group G] [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (ρ : G →* (X ≃ₜ X)) (p : X) (V : Set X) (hOpen : IsOpen V)
    (hV : V ⊆ (chartAt ℂ p).source) (hInv : ∀ g, MapsTo (ρ g) V V)
    (hHol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρ g)) :
    ∀ g, AnalyticOnNhd ℂ (h84a_planarAction ρ (chartAt ℂ p) V hV hInv g)
      ((chartAt ℂ p) '' V) := by
  let c := chartAt ℂ p
  have hUopen : IsOpen (c '' V) := c.isOpen_image_of_subset_source hOpen hV
  intro g z hz
  have hxV : c.symm z ∈ V :=
    ((h84a_chartEquiv c V hV).symm ⟨z, hz⟩).property
  have hzTarget : z ∈ c.target := by
    rcases hz with ⟨x, hx, hxz⟩
    rw [← hxz]
    exact c.mapsTo (hV hx)
  have hSymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω c.symm z :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := p)).contMDiffAt
      (c.open_target.mem_nhds hzTarget)
  have hMap : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (ρ g) (c.symm z) := hHol g (c.symm z)
  have hChart : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω c (ρ g (c.symm z)) :=
    (contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := p)).contMDiffAt
      (c.open_source.mem_nhds (hV (hInv g hxV)))
  have hCoord : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (c ∘ (ρ g) ∘ c.symm) z :=
    hChart.comp z (hMap.comp z hSymm)
  have hA : AnalyticAt ℂ (c ∘ (ρ g) ∘ c.symm) z := by
    have h :=
      Jacobians.Discharge.ContMDiff.Degree.contMDiffAt_omega_analyticAt_chart_pullback hCoord
    change AnalyticAt ℂ (c ∘ (ρ g) ∘ c.symm) z at h
    exact h
  have hnear :
      h84a_planarAction ρ c V hV hInv g =ᶠ[𝓝 z] (c ∘ (ρ g) ∘ c.symm) :=
    Filter.eventually_of_mem (hUopen.mem_nhds hz)
      (fun w hw => h84a_planarAction_apply ρ c V hV hInv g hw)
  exact hA.congr hnear.symm

/-- Faithfulness on the coordinate domain is proved using the surface identity
principle and ordinary injectivity of the original surface action. It is not a premise. -/
theorem h84a_planarAction_faithful
    {G X : Type*} [Group G] [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [ConnectedSpace X]
    (ρ : G →* (X ≃ₜ X)) (hρ : Function.Injective ρ) (p : X)
    (V : Set X) (hOpen : IsOpen V) (hpV : p ∈ V)
    (hV : V ⊆ (chartAt ℂ p).source) (hInv : ∀ g, MapsTo (ρ g) V V)
    (hHol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρ g)) :
    ∀ g, EqOn (h84a_planarAction ρ (chartAt ℂ p) V hV hInv g) id
      ((chartAt ℂ p) '' V) → g = 1 := by
  let c := chartAt ℂ p
  intro g hg
  have hVequal : ∀ y ∈ V, ρ g y = y := by
    intro y hy
    have heq := hg (show c y ∈ c '' V from ⟨y, hy, rfl⟩)
    change h84a_planarAction ρ c V hV hInv g (c y) = c y at heq
    rw [h84a_planarAction_apply ρ c V hV hInv g ⟨y, hy, rfl⟩,
      c.left_inv (hV hy)] at heq
    exact c.injOn (hV (hInv g hy)) (hV hy) heq
  have hseed : (ρ g : X → X) =ᶠ[𝓝 p] id :=
    Filter.eventually_of_mem (hOpen.mem_nhds hpV) hVequal
  have hGlobal : (ρ g : X → X) = id :=
    h84s_contMDiff_eq_of_germ (hHol g) contMDiff_id hseed
  apply hρ
  apply Homeomorph.ext
  intro y
  change ρ g y = ρ 1 y
  rw [map_one, Homeomorph.one_apply]
  exact congrFun hGlobal y

/-- Explicit existence of a common invariant connected coordinate domain and a
faithful analytic permutation action, constructed from genuine surface automorphisms.
No local faithfulness, derivative faithfulness, or cyclicity is assumed. -/
theorem h84a_exists_faithful_planar_action
    {G X : Type*} [Group G] [Finite G] [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (ρ : G →* (X ≃ₜ X)) (hρ : Function.Injective ρ) (p : X)
    (hFix : ∀ g, ρ g p = p)
    (hHol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρ g)) :
    ∃ (V : Set X) (U : Set ℂ) (τ : G →* Equiv.Perm ℂ),
      IsOpen V ∧ p ∈ V ∧ IsPreconnected V ∧
      V ⊆ (chartAt ℂ p).source ∧
      (∀ g, MapsTo (ρ g) V V) ∧ U = (chartAt ℂ p) '' V ∧
      IsOpen U ∧ IsPreconnected U ∧ (chartAt ℂ p) p ∈ U ∧
      (∀ g, MapsTo (τ g) U U) ∧
      (∀ g, τ g ((chartAt ℂ p) p) = (chartAt ℂ p) p) ∧
      (∀ g, AnalyticOnNhd ℂ (τ g) U) ∧
      (∀ g, EqOn (τ g) id U → g = 1) := by
  obtain ⟨V, hOpen, hpV, hPc, hV, hInv⟩ :=
    h84a_exists_invariant_chart_neighborhood ρ p hFix
  let c := chartAt ℂ p
  let U := c '' V
  let τ := h84a_planarAction ρ c V hV hInv
  have hUopen : IsOpen U := c.isOpen_image_of_subset_source hOpen hV
  have hUpc : IsPreconnected U := hPc.image c (c.continuousOn_toFun.mono hV)
  have hpU : c p ∈ U := ⟨p, hpV, rfl⟩
  have hFixU : ∀ g, τ g (c p) = c p := by
    intro g
    rw [h84a_planarAction_apply ρ c V hV hInv g hpU, c.left_inv (hV hpV), hFix g]
  refine ⟨V, U, τ, hOpen, hpV, hPc, hV, hInv, rfl, hUopen, hUpc, hpU,
    ?_, hFixU, ?_, ?_⟩
  · exact fun g => h84a_planarAction_mapsTo ρ c V hV hInv g
  · exact h84a_planarAction_analytic ρ p V hOpen hV hInv hHol
  · exact h84a_planarAction_faithful ρ hρ p V hOpen hpV hV hInv hHol

/-- A finite faithful group of genuine analytic surface automorphisms fixing one
point is cyclic, by the constructed planar action and the already proved derivative character. -/
theorem h84a_fixedPoint_group_isCyclic
    {G X : Type*} [Group G] [Finite G] [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (ρ : G →* (X ≃ₜ X)) (hρ : Function.Injective ρ) (p : X)
    (hFix : ∀ g, ρ g p = p)
    (hHol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρ g)) :
    IsCyclic G := by
  obtain ⟨V, U, τ, _hOpen, _hpV, _hPc, _hV, _hInv, _hUeq,
    _hUopen, hUpc, hpU, _hUinv, hFixU, hAnalytic, hFaith⟩ :=
    h84a_exists_faithful_planar_action ρ hρ p hFix hHol
  exact h84l_finite_analytic_stabilizer_isCyclic τ hpU hUpc hAnalytic hFixU hFaith

/-- The point stabilizer of a true finite biholomorphic surface automorphism group is cyclic.
Global action injectivity is ordinary effectiveness; all local faithfulness is proved above. -/
theorem h84a_pointStabilizer_isCyclic
    {G X : Type*} [Group G] [Finite G] [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (ρ : G →* (X ≃ₜ X)) (hρ : Function.Injective ρ) (p : X)
    (hHol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρ g)) :
    IsCyclic (h84a_pointStabilizer ρ p) := by
  let K := h84a_pointStabilizer ρ p
  let ρK : K →* (X ≃ₜ X) := ρ.comp K.subtype
  have hρK : Function.Injective ρK := by
    intro g h heq
    apply Subtype.ext
    exact hρ heq
  have hFixK : ∀ g : K, ρK g p = p := by
    intro g
    exact g.property
  have hHolK : ∀ g : K, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρK g) :=
    fun g => hHol (g : G)
  exact h84a_fixedPoint_group_isCyclic ρK hρK p hFixK hHolK

end LiZhongQC

