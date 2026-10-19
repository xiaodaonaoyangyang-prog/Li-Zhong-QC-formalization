import LiZhongQC.Lemmas.HurwitzSurfacePowerChart

/-! Mechanical round77 bundle: power descent, chart compatibility, complex quotient. -/

section HurwitzPowerDescentBlock

/-! Analytic descent through the power map, including its central branch point. -/

open Set Filter Topology
open scoped Topology Manifold ContDiff

namespace LiZhongQC

/-- Analyticity descends along z ↦ z^n away from zero. No branch of a complex
root is postulated: the inverse-function theorem supplies the local inverse. -/
theorem h84g_analytic_descends_power_nonzero (n : ℕ) (hn : n ≠ 0)
    (F : ℂ → ℂ) (w : ℂ) (hw : w ≠ 0)
    (hF : AnalyticAt ℂ (F ∘ (fun z : ℂ => z ^ n)) w) :
    AnalyticAt ℂ F (w ^ n) := by
  have hP : AnalyticAt ℂ (fun z : ℂ => z ^ n) w := analyticAt_id.pow n
  have hd : deriv (fun z : ℂ => z ^ n) w ≠ 0 := by
    rw [deriv_pow_field]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hn) (pow_ne_zero _ hw)
  exact (analyticAt_comp_iff_of_deriv_ne_zero hP hd).mp hF

/-- A continuous function on an open subset of the power disk is analytic when
its pullback to the source disk is analytic. The only exceptional point, zero,
is removed by the continuous removable-singularity theorem. -/
theorem h84g_analytic_descends_power (n : ℕ) (hn : n ≠ 0)
    (r : ℝ) (hr : 0 < r) (O : Set ℂ) (hO : IsOpen O)
    (hOD : O ⊆ Metric.ball 0 (r ^ n))
    (F : ℂ → ℂ) (hFc : ContinuousOn F O)
    (hF : ∀ w ∈ Metric.ball (0 : ℂ) r, w ^ n ∈ O →
      AnalyticAt ℂ (F ∘ (fun z : ℂ => z ^ n)) w) : AnalyticOnNhd ℂ F O := by
  have hAway : ∀ z ∈ O, z ≠ 0 → AnalyticAt ℂ F z := by
    intro z hz hz0
    letI : NeZero n := ⟨hn⟩
    obtain ⟨w, hw⟩ := (Complex.isOpenQuotientMap_pow n).surjective z
    change w ^ n = z at hw
    have hw0 : w ≠ 0 := by
      intro he
      apply hz0
      rw [← hw, he, zero_pow hn]
    have hnorm : ‖w‖ ^ n < r ^ n := by
      rw [← norm_pow, hw]
      simpa only [Metric.mem_ball, dist_zero_right] using hOD hz
    have hwD : w ∈ Metric.ball (0 : ℂ) r := by
      change dist w 0 < r
      rw [dist_zero_right]
      exact lt_of_pow_lt_pow_left₀ n hr.le hnorm
    rw [← hw]
    exact h84g_analytic_descends_power_nonzero n hn F w hw0 (hF w hwD (by rwa [hw]))
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hz)] with w hw0 hwO
      exact (hAway w hwO hw0).differentiableAt
    · exact (hFc 0 hz).continuousAt (hO.mem_nhds hz)
  · exact hAway z hz hz0

end LiZhongQC
end HurwitzPowerDescentBlock

section HurwitzChartCompatibilityBlock

/-! Analytic compatibility of genuine quotient power charts. -/

open Set Filter Topology
open scoped Topology Manifold ContDiff

namespace LiZhongQC

/-- The overlap of two actual quotient power charts is analytic. A lift to the
second source disk differs from the first by an actual global group element.
Analytic descent handles the central branch point without assuming regularity there. -/
theorem h84g_power_charts_compatible
    {G X : Type*} [Group G] [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X]
    (ρ : G →* (X ≃ₜ X))
    (hHol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρ g))
    (u₁ u₂ : OpenPartialHomeomorph X ℂ)
    (v₁ v₂ : OpenPartialHomeomorph (h84g_OrbitSpace ρ) ℂ)
    (n₁ n₂ : ℕ) (hn₂ : n₂ ≠ 0) (r₂ : ℝ) (hr₂ : 0 < r₂)
    (hu₂T : u₂.target = Metric.ball 0 r₂)
    (hv₂T : v₂.target = Metric.ball 0 (r₂ ^ n₂))
    (hu₁H : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u₁ u₁.source)
    (hui₂H : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u₂.symm u₂.target)
    (hv₁S : v₁.source = h84g_orbitMap ρ '' u₁.source)
    (hv₂S : v₂.source = h84g_orbitMap ρ '' u₂.source)
    (hP₁ : ∀ x ∈ u₁.source, v₁ (h84g_orbitMap ρ x) = (u₁ x) ^ n₁)
    (hP₂ : ∀ x ∈ u₂.source, v₂ (h84g_orbitMap ρ x) = (u₂ x) ^ n₂) :
    AnalyticOnNhd ℂ (v₁ ∘ v₂.symm) (v₂.symm.trans v₁).source := by
  let O := (v₂.symm.trans v₁).source
  have hOD : O ⊆ Metric.ball 0 (r₂ ^ n₂) := by
    intro z hz
    exact hv₂T ▸ hz.1
  have hFc : ContinuousOn (v₁ ∘ v₂.symm) O :=
    (v₂.symm.trans v₁).continuousOn
  apply h84g_analytic_descends_power n₂ hn₂ r₂ hr₂ O
    (v₂.symm.trans v₁).open_source hOD (v₁ ∘ v₂.symm) hFc
  intro w hwD hwO
  have hwT : w ∈ u₂.target := by rwa [hu₂T]
  let x := u₂.symm w
  have hxU : x ∈ u₂.source := u₂.symm.mapsTo hwT
  have hqxV : h84g_orbitMap ρ x ∈ v₂.source := by
    rw [hv₂S]
    exact ⟨x, hxU, rfl⟩
  have hpow : v₂ (h84g_orbitMap ρ x) = w ^ n₂ := by
    rw [hP₂ x hxU, u₂.right_inv hwT]
  have hLift : v₂.symm (w ^ n₂) = h84g_orbitMap ρ x := by
    rw [← hpow, v₂.left_inv hqxV]
  have hqxV₁ : h84g_orbitMap ρ x ∈ v₁.source := by
    rw [← hLift]
    exact hwO.2
  rw [hv₁S] at hqxV₁
  obtain ⟨y, hyU, hqy⟩ := hqxV₁
  obtain ⟨g, hg⟩ := (h84g_orbitMap_eq_iff ρ x y).mp hqy.symm
  have hgxU : ρ g x ∈ u₁.source := by rwa [hg]
  have hui₂ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω u₂.symm w :=
    hui₂H.contMDiffAt (u₂.open_target.mem_nhds hwT)
  have hgu : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω ((ρ g) ∘ u₂.symm) w :=
    (hHol g x).comp w hui₂
  have hu₁ : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω u₁ (ρ g x) :=
    hu₁H.contMDiffAt (u₁.open_source.mem_nhds hgxU)
  have hA : AnalyticAt ℂ (fun z => (u₁ (ρ g (u₂.symm z))) ^ n₁) w :=
    ((hu₁.comp w hgu).contDiffAt.analyticAt).pow n₁
  have hnearT : ∀ᶠ t in 𝓝 w, t ∈ u₂.target := u₂.open_target.mem_nhds hwT
  have hnearU : ∀ᶠ t in 𝓝 w, ρ g (u₂.symm t) ∈ u₁.source :=
    hgu.continuousAt (u₁.open_source.mem_nhds hgxU)
  have hnear : (v₁ ∘ v₂.symm) ∘ (fun z : ℂ => z ^ n₂) =ᶠ[𝓝 w]
      (fun z => (u₁ (ρ g (u₂.symm z))) ^ n₁) := by
    filter_upwards [hnearT, hnearU] with t htT htU
    have htX : u₂.symm t ∈ u₂.source := u₂.symm.mapsTo htT
    have htV : h84g_orbitMap ρ (u₂.symm t) ∈ v₂.source := by
      rw [hv₂S]
      exact ⟨u₂.symm t, htX, rfl⟩
    have htP : v₂ (h84g_orbitMap ρ (u₂.symm t)) = t ^ n₂ := by
      rw [hP₂ _ htX, u₂.right_inv htT]
    have htL : v₂.symm (t ^ n₂) = h84g_orbitMap ρ (u₂.symm t) := by
      rw [← htP, v₂.left_inv htV]
    have htG : h84g_orbitMap ρ (u₂.symm t) =
        h84g_orbitMap ρ (ρ g (u₂.symm t)) :=
      (h84g_orbitMap_eq_iff ρ _ _).mpr ⟨g, rfl⟩
    change v₁ (v₂.symm (t ^ n₂)) = _
    rw [htL, htG, hP₁ _ htU]
  exact hA.congr hnear.symm

end LiZhongQC
end HurwitzChartCompatibilityBlock

section HurwitzComplexQuotientBlock

/-! Assemble the actual finite-action orbit space into a complex analytic surface.
All chart and manifold data are constructed from the actual action. -/

open Set Filter Topology
open scoped Topology Manifold ContDiff

namespace LiZhongQC

/-- The actual quotient has a complex atlas, analytic projection, and analytic
power coordinates of degree equal to each actual stabilizer order. This is the
global geometric interface for fiber, ramification and divisor computations. -/
theorem h84g_exists_complex_quotient
    {G X : Type*} [Group G] [Finite G] [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (ρ : G →* (X ≃ₜ X)) (hρ : Function.Injective ρ)
    (hHol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρ g)) :
    ∃ c : ChartedSpace ℂ (h84g_OrbitSpace ρ),
      letI := c
      IsManifold 𝓘(ℂ) ω (h84g_OrbitSpace ρ) ∧
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (h84g_orbitMap ρ) ∧
      ∀ p : X, ∃ (r : ℝ) (u : OpenPartialHomeomorph X ℂ)
        (v : OpenPartialHomeomorph (h84g_OrbitSpace ρ) ℂ),
        0 < r ∧ p ∈ u.source ∧ u p = 0 ∧ u.target = Metric.ball 0 r ∧
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u u.source ∧
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u.symm u.target ∧
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω v v.source ∧
        ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω v.symm v.target ∧
        v.source = h84g_orbitMap ρ '' u.source ∧
        v.target = Metric.ball 0 (r ^ Nat.card (h84a_pointStabilizer ρ p)) ∧
        ∀ x ∈ u.source, v (h84g_orbitMap ρ x) =
          (u x) ^ Nat.card (h84a_pointStabilizer ρ p) := by
  classical
  choose r u v hr hpU hu0 huT huH huiH hvS hvT hP using
    (fun p : X => h84g_exists_surface_power_chart ρ hρ p hHol)
  let Q := h84g_OrbitSpace ρ
  have hqp : ∀ p : X, h84g_orbitMap ρ p ∈ (v p).source := by
    intro p
    rw [hvS p]
    exact ⟨p, hpU p, rfl⟩
  let c : ChartedSpace ℂ Q :=
    { atlas := range v
      chartAt := fun q => v q.out
      mem_chart_source := by
        intro q
        have h := hqp q.out
        change Quotient.mk (h84g_orbitSetoid ρ) q.out ∈ (v q.out).source at h
        rwa [Quotient.out_eq] at h
      chart_mem_atlas := fun q => ⟨q.out, rfl⟩ }
  letI := c
  have hM : IsManifold 𝓘(ℂ) ω Q := by
    apply isManifold_of_contDiffOn 𝓘(ℂ) ω Q
    intro e e' he he'
    change e ∈ range v at he
    change e' ∈ range v at he'
    obtain ⟨p, rfl⟩ := he
    obtain ⟨p', rfl⟩ := he'
    have hn : Nat.card (h84a_pointStabilizer ρ p) ≠ 0 := Nat.card_pos.ne'
    have hA := h84g_power_charts_compatible ρ hHol
      (u p') (u p) (v p') (v p)
      (Nat.card (h84a_pointStabilizer ρ p'))
      (Nat.card (h84a_pointStabilizer ρ p)) hn (r p) (hr p)
      (huT p) (hvT p) (huH p') (huiH p) (hvS p') (hvS p) (hP p') (hP p)
    have hCD := hA.contDiffOn_of_completeSpace (n := ω)
    change ContDiffOn ℂ ω ((v p).symm.trans (v p'))
      ((v p).symm.trans (v p')).source at hCD
    simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, preimage_id, range_id, inter_univ] using
      hCD
  letI : IsManifold 𝓘(ℂ) ω Q := hM
  have hvAtlas : ∀ p : X, v p ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω Q := by
    intro p
    apply IsManifold.subset_maximalAtlas
    exact ⟨p, rfl⟩
  have hπ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (h84g_orbitMap ρ) := by
    intro p
    let n := Nat.card (h84a_pointStabilizer ρ p)
    have hU : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (u p) p :=
      (huH p).contMDiffAt ((u p).open_source.mem_nhds (hpU p))
    have hPow : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
        (fun x : X => (u p x) ^ n) p :=
      ((contDiffAt_id.pow n).contMDiffAt).comp p hU
    have hpowT : (u p p) ^ n ∈ (v p).target := by
      rw [← hP p p (hpU p)]
      exact (v p).mapsTo (hqp p)
    have hVi : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (v p).symm ((u p p) ^ n) :=
      contMDiffAt_symm_of_mem_maximalAtlas (hvAtlas p) hpowT
    have hA := hVi.comp p hPow
    apply hA.congr_of_eventuallyEq
    filter_upwards [(u p).open_source.mem_nhds (hpU p)] with x hx
    have hqx : h84g_orbitMap ρ x ∈ (v p).source := by
      rw [hvS p]
      exact ⟨x, hx, rfl⟩
    change h84g_orbitMap ρ x = (v p).symm ((u p x) ^ n)
    rw [← hP p x hx, (v p).left_inv hqx]
  refine ⟨c, hM, hπ, ?_⟩
  intro p
  exact ⟨r p, u p, v p, hr p, hpU p, hu0 p, huT p, huH p, huiH p,
    contMDiffOn_of_mem_maximalAtlas (hvAtlas p),
    contMDiffOn_symm_of_mem_maximalAtlas (hvAtlas p), hvS p, hvT p, hP p⟩

end LiZhongQC
end HurwitzComplexQuotientBlock


