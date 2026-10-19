import Mathlib
import LiZhongQC.Lemmas.HurwitzStabilizerAction
/-! Weighted finite averaging coordinates for the actual analytic stabilizer action.
The imported action, germ-rigidity and surface-identity modules remain unchanged. -/

open Set Filter
open scoped BigOperators Topology Manifold ContDiff

namespace LiZhongQC

/-- The normalized weighted orbit sum. The weights are inverse tangent multipliers,
and subtracting p centers the coordinate at the common fixed point. -/
noncomputable def h84b_averageCoordinate {G : Type*} [Group G] [Fintype G]
    (τ : G →* Equiv.Perm ℂ) (χ : G →* ℂˣ) (p : ℂ) : ℂ → ℂ :=
  fun z => (Fintype.card G : ℂ)⁻¹ *
    ∑ g : G, ((χ g : ℂ)⁻¹ * (τ g z - p))

/-- The explicit averaged coordinate sends the common fixed point to zero. -/
theorem h84b_averageCoordinate_fixed {G : Type*} [Group G] [Fintype G]
    (τ : G →* Equiv.Perm ℂ) (χ : G →* ℂˣ) (p : ℂ)
    (hfix : ∀ g, τ g p = p) :
    h84b_averageCoordinate τ χ p p = 0 := by
  classical
  change (Fintype.card G : ℂ)⁻¹ *
    (∑ g : G, ((χ g : ℂ)⁻¹ * (τ g p - p))) = 0
  simp only [hfix, sub_self, mul_zero, Finset.sum_const_zero]

/-- Analyticity is inherited term by term from the actual finite action. -/
theorem h84b_averageCoordinate_analytic {G : Type*} [Group G] [Fintype G]
    (τ : G →* Equiv.Perm ℂ) (χ : G →* ℂˣ) (p : ℂ) {U : Set ℂ}
    (hhol : ∀ g, AnalyticOnNhd ℂ (τ g) U) :
    AnalyticOnNhd ℂ (h84b_averageCoordinate τ χ p) U := by
  classical
  intro z hz
  change AnalyticAt ℂ
    (fun w => (Fintype.card G : ℂ)⁻¹ *
      ∑ g : G, ((χ g : ℂ)⁻¹ * (τ g w - p))) z
  apply analyticAt_const.mul
  apply Finset.analyticAt_fun_sum
  intro g _hg
  exact analyticAt_const.mul ((hhol g z hz).sub analyticAt_const)

/-- Each weighted derivative is one, so dividing the sum by the nonzero group
cardinality gives strict derivative one. No local injectivity is assumed. -/
theorem h84b_averageCoordinate_hasStrictDerivAt
    {G : Type*} [Group G] [Fintype G]
    (τ : G →* Equiv.Perm ℂ) (χ : G →* ℂˣ) {p : ℂ} {U : Set ℂ}
    (hp : p ∈ U) (hhol : ∀ g, AnalyticOnNhd ℂ (τ g) U)
    (hχ : ∀ g, (χ g : ℂ) = deriv (τ g) p) :
    HasStrictDerivAt (h84b_averageCoordinate τ χ p) 1 p := by
  classical
  have hterm : ∀ g : G,
      HasStrictDerivAt (fun z => (χ g : ℂ)⁻¹ * (τ g z - p)) 1 p := by
    intro g
    have hg := ((hhol g p hp).hasStrictDerivAt.sub
      (hasStrictDerivAt_const p p)).const_mul (χ g : ℂ)⁻¹
    simpa only [Pi.sub_apply, sub_zero, ← hχ g, inv_mul_cancel₀ (χ g).ne_zero] using hg
  have hsum := HasStrictDerivAt.fun_sum
    (u := Finset.univ) (A := fun g z => (χ g : ℂ)⁻¹ * (τ g z - p))
    (A' := fun _ : G => (1 : ℂ)) (fun g _hg => hterm g)
  have hcard : (Fintype.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  change HasStrictDerivAt
    (fun z => (Fintype.card G : ℂ)⁻¹ *
      ∑ g : G, ((χ g : ℂ)⁻¹ * (τ g z - p))) 1 p
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, inv_mul_cancel₀ hcard] using hsum.const_mul (Fintype.card G : ℂ)⁻¹

/-- Right multiplication reindexes the finite sum. The character multiplication
law gives simultaneous equivariance for every group element. -/
theorem h84b_averageCoordinate_equivariant
    {G : Type*} [Group G] [Fintype G]
    (τ : G →* Equiv.Perm ℂ) (χ : G →* ℂˣ) (p : ℂ) (h : G) (z : ℂ) :
    h84b_averageCoordinate τ χ p (τ h z) =
      (χ h : ℂ) * h84b_averageCoordinate τ χ p z := by
  classical
  have hterm : ∀ g : G,
      (χ g : ℂ)⁻¹ * (τ g (τ h z) - p) =
        (χ h : ℂ) * ((χ (g * h) : ℂ)⁻¹ * (τ (g * h) z - p)) := by
    intro g
    have hτ : τ (g * h) z = τ g (τ h z) := by
      rw [map_mul, Equiv.Perm.coe_mul]
      rfl
    have hχ : (χ (g * h) : ℂ) = (χ g : ℂ) * (χ h : ℂ) := by
      rw [map_mul, Units.val_mul]
    rw [hτ, hχ, mul_inv_rev]
    calc
      (χ g : ℂ)⁻¹ * (τ g (τ h z) - p) =
          ((χ h : ℂ) * (χ h : ℂ)⁻¹) *
            ((χ g : ℂ)⁻¹ * (τ g (τ h z) - p)) := by
        rw [mul_inv_cancel₀ (χ h).ne_zero, one_mul]
      _ = (χ h : ℂ) *
          ((χ h : ℂ)⁻¹ * (χ g : ℂ)⁻¹ * (τ g (τ h z) - p)) := by ring
  have hsum :
      (∑ g : G, ((χ g : ℂ)⁻¹ * (τ g (τ h z) - p))) =
        (χ h : ℂ) * ∑ g : G, ((χ g : ℂ)⁻¹ * (τ g z - p)) := by
    calc
      (∑ g : G, ((χ g : ℂ)⁻¹ * (τ g (τ h z) - p))) =
          ∑ g : G, ((χ h : ℂ) *
            ((χ (g * h) : ℂ)⁻¹ * (τ (g * h) z - p))) := by
        apply Finset.sum_congr rfl
        intro g _hg
        exact hterm g
      _ = (χ h : ℂ) *
          ∑ g : G, ((χ (g * h) : ℂ)⁻¹ * (τ (g * h) z - p)) := by
        rw [Finset.mul_sum]
      _ = (χ h : ℂ) * ∑ g : G, ((χ g : ℂ)⁻¹ * (τ g z - p)) := by
        congr 1
        exact Equiv.sum_comp (Equiv.mulRight h)
          (fun g : G => (χ g : ℂ)⁻¹ * (τ g z - p))
  change (Fintype.card G : ℂ)⁻¹ *
      (∑ g : G, ((χ g : ℂ)⁻¹ * (τ g (τ h z) - p))) =
    (χ h : ℂ) * ((Fintype.card G : ℂ)⁻¹ *
      ∑ g : G, ((χ g : ℂ)⁻¹ * (τ g z - p)))
  rw [hsum]
  ring

/-- Shrink any open neighborhood inside the analytic action domain to a common
invariant open neighborhood. Only continuity at points of U is needed. -/
theorem h84b_exists_invariant_open_subset
    {G : Type*} [Group G] [Finite G]
    (τ : G →* Equiv.Perm ℂ) {U S : Set ℂ} {p : ℂ}
    (hU : IsOpen U) (hp : p ∈ U) (hS : IsOpen S) (hpS : p ∈ S)
    (hhol : ∀ g, AnalyticOnNhd ℂ (τ g) U)
    (hfix : ∀ g, τ g p = p) (hInv : ∀ g, MapsTo (τ g) U U) :
    ∃ W : Set ℂ, IsOpen W ∧ p ∈ W ∧ W ⊆ U ∧ W ⊆ S ∧
      ∀ g, MapsTo (τ g) W W := by
  let W : Set ℂ := ⋂ g : G, U ∩ (τ g) ⁻¹' S
  have hWopen : IsOpen W := by
    apply isOpen_iInter_of_finite
    intro g
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    exact Filter.inter_mem (hU.mem_nhds hz.1)
      ((hhol g z hz.1).continuousAt.preimage_mem_nhds (hS.mem_nhds hz.2))
  have hpW : p ∈ W := by
    apply mem_iInter.mpr
    intro g
    exact ⟨hp, by change τ g p ∈ S; rw [hfix g]; exact hpS⟩
  have hWU : W ⊆ U := by
    intro z hz
    exact ((mem_iInter.mp hz) (1 : G)).1
  have hWS : W ⊆ S := by
    intro z hz
    have h := ((mem_iInter.mp hz) (1 : G)).2
    change τ 1 z ∈ S at h
    simpa only [map_one, Equiv.Perm.coe_one, id_eq] using h
  have hWInv : ∀ g, MapsTo (τ g) W W := by
    intro g z hz
    apply mem_iInter.mpr
    intro h
    have hgh := ((mem_iInter.mp hz) (h * g)).2
    change τ (h * g) z ∈ S at hgh
    refine ⟨hInv g (hWU hz), ?_⟩
    change τ h (τ g z) ∈ S
    simpa only [map_mul, Equiv.Perm.coe_mul, Function.comp_apply] using hgh
  exact ⟨W, hWopen, hpW, hWU, hWS, hWInv⟩

/-- The explicit average is a genuine local coordinate. The inverse function theorem
constructs its local inverse, and finite intersection makes its source invariant.
The resulting coordinate linearizes every element on the same source. -/
theorem h84b_averageCoordinate_local_linearization
    {G : Type*} [Group G] [Fintype G]
    (τ : G →* Equiv.Perm ℂ) (χ : G →* ℂˣ) {U : Set ℂ} {p : ℂ}
    (hU : IsOpen U) (hp : p ∈ U)
    (hhol : ∀ g, AnalyticOnNhd ℂ (τ g) U) (hfix : ∀ g, τ g p = p)
    (hInv : ∀ g, MapsTo (τ g) U U)
    (hχ : ∀ g, (χ g : ℂ) = deriv (τ g) p) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (e : ℂ → ℂ) = h84b_averageCoordinate τ χ p ∧
      p ∈ e.source ∧ e.source ⊆ U ∧ e p = 0 ∧
      HasStrictDerivAt (e : ℂ → ℂ) 1 p ∧
      InjOn (h84b_averageCoordinate τ χ p) e.source ∧
      AnalyticOnNhd ℂ (e : ℂ → ℂ) e.source ∧ AnalyticAt ℂ e.symm 0 ∧
      (∀ g, MapsTo (τ g) e.source e.source) ∧
      (∀ g, MapsTo (fun w => (χ g : ℂ) * w) e.target e.target) ∧
      (∀ g w, w ∈ e.target → e (τ g (e.symm w)) = (χ g : ℂ) * w) := by
  let A := h84b_averageCoordinate τ χ p
  have hA := h84b_averageCoordinate_analytic τ χ p hhol
  have hAp : AnalyticAt ℂ A p := hA p hp
  have hD : HasStrictDerivAt A 1 p :=
    h84b_averageCoordinate_hasStrictDerivAt τ χ hp hhol hχ
  have hzero : A p = 0 := h84b_averageCoordinate_fixed τ χ p hfix
  have hne : deriv A p ≠ 0 := by
    rw [hD.hasDerivAt.deriv]
    exact one_ne_zero
  let hfd := hAp.hasStrictDerivAt.hasStrictFDerivAt_equiv hne
  let e₀ : OpenPartialHomeomorph ℂ ℂ := hfd.toOpenPartialHomeomorph A
  have hp₀ : p ∈ e₀.source := hfd.mem_toOpenPartialHomeomorph_source
  obtain ⟨W, hWopen, hpW, hWU, hWS, hWInv⟩ :=
    h84b_exists_invariant_open_subset τ hU hp e₀.open_source hp₀ hhol hfix hInv
  let e := e₀.restrOpen W hWopen
  have hcoe : (e : ℂ → ℂ) = A := rfl
  have hsource : e.source = W := by
    change e₀.source ∩ W = W
    exact inter_eq_right.mpr hWS
  have hInvA : AnalyticAt ℂ e.symm 0 := by
    have h := hAp.analyticAt_localInverse hne
    change AnalyticAt ℂ e.symm (A p) at h
    rw [hzero] at h
    exact h
  have hSourceInv : ∀ g, MapsTo (τ g) e.source e.source := by
    rw [hsource]
    exact hWInv
  have hEq : ∀ g w, w ∈ e.target →
      e (τ g (e.symm w)) = (χ g : ℂ) * w := by
    intro g w hw
    calc
      e (τ g (e.symm w)) = (χ g : ℂ) * e (e.symm w) := by
        change A (τ g (e.symm w)) = (χ g : ℂ) * A (e.symm w)
        exact h84b_averageCoordinate_equivariant τ χ p g (e.symm w)
      _ = (χ g : ℂ) * w := by rw [e.right_inv hw]
  have hTargetInv : ∀ g, MapsTo (fun w => (χ g : ℂ) * w) e.target e.target := by
    intro g w hw
    dsimp only
    rw [← hEq g w hw]
    exact e.mapsTo (hSourceInv g (e.symm.mapsTo hw))
  refine ⟨e, hcoe, ?_, ?_, ?_, ?_, ?_, ?_, hInvA, hSourceInv, hTargetInv, hEq⟩
  · rw [hsource]
    exact hpW
  · rw [hsource]
    exact hWU
  · change A p = 0
    exact hzero
  · change HasStrictDerivAt A 1 p
    exact hD
  · change InjOn (e : ℂ → ℂ) e.source
    exact e.injOn
  · change AnalyticOnNhd ℂ A e.source
    exact hA.mono (by rw [hsource]; exact hWU)

/-- Apply the explicit average to the true surface stabilizer chart action.
The tangent character is constructed from derivatives and proved injective by the
already compiled germ-rigidity and surface-identity modules. No linearizing chart,
local faithfulness, tangent faithfulness, or cyclicity is supplied as a premise. -/
theorem h84b_surface_exists_linearized_action
    {G X : Type*} [Group G] [Finite G] [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (ρ : G →* (X ≃ₜ X)) (hρ : Function.Injective ρ) (p : X)
    (hFix : ∀ g, ρ g p = p)
    (hHol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρ g)) :
    ∃ (V : Set X) (U : Set ℂ) (τ : G →* Equiv.Perm ℂ) (χ : G →* ℂˣ)
      (e : OpenPartialHomeomorph ℂ ℂ),
      IsOpen V ∧ p ∈ V ∧ V ⊆ (chartAt ℂ p).source ∧
      (∀ g, MapsTo (ρ g) V V) ∧ U = (chartAt ℂ p) '' V ∧
      IsOpen U ∧ IsPreconnected U ∧ (chartAt ℂ p) p ∈ U ∧
      (∀ g y, y ∈ V → τ g ((chartAt ℂ p) y) = (chartAt ℂ p) (ρ g y)) ∧
      (∀ g, (χ g : ℂ) = deriv (τ g) ((chartAt ℂ p) p)) ∧
      Function.Injective χ ∧
      (chartAt ℂ p) p ∈ e.source ∧ e.source ⊆ U ∧ e ((chartAt ℂ p) p) = 0 ∧
      HasStrictDerivAt (e : ℂ → ℂ) 1 ((chartAt ℂ p) p) ∧
      AnalyticOnNhd ℂ (e : ℂ → ℂ) e.source ∧ AnalyticAt ℂ e.symm 0 ∧
      (∀ g, MapsTo (τ g) e.source e.source) ∧
      (∀ g, MapsTo (fun w => (χ g : ℂ) * w) e.target e.target) ∧
      (∀ g w, w ∈ e.target → e (τ g (e.symm w)) = (χ g : ℂ) * w) := by
  classical
  letI := Fintype.ofFinite G
  obtain ⟨V, hVopen, hpV, hVpc, hV, hVInv⟩ :=
    h84a_exists_invariant_chart_neighborhood ρ p hFix
  let c := chartAt ℂ p
  let U := c '' V
  let τ := h84a_planarAction ρ c V hV hVInv
  have hUopen : IsOpen U := c.isOpen_image_of_subset_source hVopen hV
  have hUpc : IsPreconnected U := hVpc.image c (c.continuousOn_toFun.mono hV)
  have hpU : c p ∈ U := ⟨p, hpV, rfl⟩
  have hτhol : ∀ g, AnalyticOnNhd ℂ (τ g) U :=
    h84a_planarAction_analytic ρ p V hVopen hV hVInv hHol
  have hτInv : ∀ g, MapsTo (τ g) U U :=
    fun g => h84a_planarAction_mapsTo ρ c V hV hVInv g
  have hτfix : ∀ g, τ g (c p) = c p := by
    intro g
    rw [h84a_planarAction_apply ρ c V hV hVInv g hpU, c.left_inv (hV hpV), hFix g]
  have hτfaith : ∀ g, EqOn (τ g) id U → g = 1 :=
    h84a_planarAction_faithful ρ hρ p V hVopen hpV hV hVInv hHol
  let χ := (h84l_derivativeCharacter τ hpU hτhol hτfix).toHomUnits
  have hχ : ∀ g, (χ g : ℂ) = deriv (τ g) (c p) := by
    intro g
    change ((h84l_derivativeCharacter τ hpU hτhol hτfix).toHomUnits g : ℂ) = _
    rw [MonoidHom.coe_toHomUnits]
    rfl
  have hχinj : Function.Injective χ :=
    h84l_derivativeCharacter_units_injective τ hpU hUpc hτhol hτfix hτfaith
  obtain ⟨e, _hAverage, hpe, hSub, he0, hDe, _hInj, hAe, hAi, hSe, hTe, hEq⟩ :=
    h84b_averageCoordinate_local_linearization τ χ hUopen hpU hτhol hτfix hτInv hχ
  refine ⟨V, U, τ, χ, e, hVopen, hpV, hV, hVInv, rfl, hUopen, hUpc, hpU,
    ?_, hχ, hχinj, hpe, hSub, he0, hDe, hAe, hAi, hSe, hTe, hEq⟩
  intro g y hy
  have hcy : c y ∈ U := ⟨y, hy, rfl⟩
  rw [h84a_planarAction_apply ρ c V hV hVInv g hcy, c.left_inv (hV hy)]

end LiZhongQC


