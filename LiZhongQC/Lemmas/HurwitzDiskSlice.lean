import LiZhongQC.Lemmas.HurwitzOrbitTopology
import LiZhongQC.Lemmas.HurwitzWeightedAverage

/-! Shrinking the genuine stabilizer linearization inside a separating slice. -/

open Set Filter Topology
open scoped Topology Manifold ContDiff

namespace LiZhongQC

/-- An actual rotation chart can be shrunk to a centered disk inside any prescribed
open neighborhood. Its equivariance survives restriction because rotations preserve disks. -/
theorem h84g_shrink_rotation_chart {H X : Type*}
    [Group H] [TopologicalSpace X]
    (ρ : H →* (X ≃ₜ X)) (χ : H →* ℂˣ)
    (hNorm : ∀ g, ‖(χ g : ℂ)‖ = 1)
    (a : OpenPartialHomeomorph X ℂ) (p : X)
    (hp : p ∈ a.source) (hzero : a p = 0)
    (hInv : ∀ g, MapsTo (ρ g) a.source a.source)
    (hLin : ∀ g x, x ∈ a.source → a (ρ g x) = (χ g : ℂ) * a x)
    (W : Set X) (hWo : IsOpen W) (hpW : p ∈ W) :
    ∃ (r : ℝ) (u : OpenPartialHomeomorph X ℂ), 0 < r ∧
      p ∈ u.source ∧ u p = 0 ∧ u.target = Metric.ball 0 r ∧
      u.source ⊆ W ∧ u.source ⊆ a.source ∧
      (u : X → ℂ) = a ∧ (u.symm : ℂ → X) = a.symm ∧
      (∀ g, MapsTo (ρ g) u.source u.source) ∧
      (∀ g x, x ∈ u.source → u (ρ g x) = (χ g : ℂ) * u x) := by
  have hO : IsOpen (a '' (a.source ∩ W)) :=
    a.isOpen_image_of_subset_source (a.open_source.inter hWo) inter_subset_left
  have h0O : (0 : ℂ) ∈ a '' (a.source ∩ W) := ⟨p, ⟨hp, hpW⟩, hzero⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO 0 h0O
  have hballT : Metric.ball (0 : ℂ) r ⊆ a.target := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hball hz
    exact a.mapsTo hx.1
  let u := (a.symm.restrOpen (Metric.ball 0 r) Metric.isOpen_ball).symm
  have hUS : ∀ x, x ∈ u.source ↔ x ∈ a.source ∧ a x ∈ Metric.ball 0 r :=
    fun _ => Iff.rfl
  have hUT : u.target = Metric.ball 0 r := by
    change a.target ∩ Metric.ball 0 r = Metric.ball 0 r
    exact inter_eq_right.mpr hballT
  have hsub : u.source ⊆ W := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hball ((hUS x).mp hx).2
    have hyx : y = x := a.injOn hy.1 ((hUS x).mp hx).1 he
    exact hyx ▸ hy.2
  refine ⟨r, u, hr, ?_, hzero, hUT, hsub,
    (fun x hx => ((hUS x).mp hx).1), rfl, rfl, ?_, ?_⟩
  · apply (hUS p).mpr
    refine ⟨hp, ?_⟩
    rw [hzero]
    exact Metric.mem_ball_self hr
  · intro g x hx
    obtain ⟨hxS, hxD⟩ := (hUS x).mp hx
    apply (hUS (ρ g x)).mpr
    refine ⟨hInv g hxS, ?_⟩
    rw [hLin g x hxS]
    simpa only [Metric.mem_ball, dist_zero_right, norm_mul, hNorm g, one_mul] using hxD
  · intro g x hx
    exact hLin g x ((hUS x).mp hx).1

/-- The two-stage surface chart is an actual linearizing chart for the stabilizer.
This records all domain guards, rather than extending chart identities outside their source. -/
theorem h84g_surface_linearizing_chart
    {H X : Type*} [Group H] [Finite H] [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (ρ : H →* (X ≃ₜ X)) (hρ : Function.Injective ρ) (p : X)
    (hFix : ∀ g, ρ g p = p)
    (hHol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρ g)) :
    ∃ (χ : H →* ℂˣ) (a : OpenPartialHomeomorph X ℂ),
      Function.Injective χ ∧ p ∈ a.source ∧ a p = 0 ∧
      (∀ g, MapsTo (ρ g) a.source a.source) ∧
      (∀ g x, x ∈ a.source → a (ρ g x) = (χ g : ℂ) * a x) ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω a a.source ∧
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω a.symm 0 := by
  obtain ⟨V, U, τ, χ, e, hVo, hpV, hV, hVI, hUeq, _hUo, _hUpc, _hpU,
    hChart, _hχDeriv, hχ, hpE, hEU, he0, _hDe, hAe, hAi, hInv, _hTarget, hLin⟩ :=
    h84b_surface_exists_linearized_action ρ hρ p hFix hHol
  let c := chartAt ℂ p
  let a := c.trans e
  have hSrc : ∀ x, x ∈ a.source ↔ x ∈ c.source ∧ c x ∈ e.source :=
    fun _ => Iff.rfl
  have hSubV : a.source ⊆ V := by
    intro x hx
    have hxU := hEU ((hSrc x).mp hx).2
    rw [hUeq] at hxU
    obtain ⟨y, hy, he⟩ := hxU
    have hyx : y = x := c.injOn (hV hy) ((hSrc x).mp hx).1 he
    exact hyx ▸ hy
  have hpA : p ∈ a.source := ⟨mem_chart_source ℂ p, hpE⟩
  have hAI : ∀ g, MapsTo (ρ g) a.source a.source := by
    intro g x hx
    have hxV := hSubV hx
    apply (hSrc (ρ g x)).mpr
    refine ⟨hV (hVI g hxV), ?_⟩
    rw [← hChart g x hxV]
    exact hInv g ((hSrc x).mp hx).2
  have hAL : ∀ g x, x ∈ a.source → a (ρ g x) = (χ g : ℂ) * a x := by
    intro g x hx
    have hcE := ((hSrc x).mp hx).2
    have h := hLin g (e (c x)) (e.mapsTo hcE)
    rw [e.left_inv hcE, hChart g x (hSubV hx)] at h
    exact h
  have hAH : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω a a.source := by
    intro x hx
    have hcH : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω c x :=
      (contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := p)).contMDiffAt
        (c.open_source.mem_nhds ((hSrc x).mp hx).1)
    have heH : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e (c x) :=
      (hAe (c x) ((hSrc x).mp hx).2).contDiffAt.contMDiffAt
    exact (heH.comp x hcH).contMDiffWithinAt
  have hInvH : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω a.symm 0 := by
    have heH : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω e.symm 0 :=
      hAi.contDiffAt.contMDiffAt
    have he0' : e.symm 0 = c p := by
      rw [← he0, e.left_inv hpE]
    have hcH : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω c.symm (e.symm 0) := by
      rw [he0']
      exact (contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := p)).contMDiffAt
        (c.open_target.mem_nhds (c.mapsTo (mem_chart_source ℂ p)))
    exact hcH.comp 0 heH
  exact ⟨χ, a, hχ, hpA, he0, hAI, hAL, hAH, hInvH⟩

end LiZhongQC

