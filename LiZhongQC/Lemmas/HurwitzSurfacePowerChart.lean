import LiZhongQC.Lemmas.HurwitzDiskSlice
import LiZhongQC.Lemmas.HurwitzQuotientChart
import LiZhongQC.Lemmas.HurwitzPowerModel

/-! Actual local power charts on the global orbit quotient. -/

open Set Filter Topology
open scoped Topology Manifold ContDiff

namespace LiZhongQC

/-- A disk coordinate for the actual stabilizer, contained in a separating slice.
Both directions of this source coordinate are analytic on their full open domains. -/
theorem h84g_exists_disk_slice
    {G X : Type*} [Group G] [Finite G] [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (ρ : G →* (X ≃ₜ X)) (hρ : Function.Injective ρ) (p : X)
    (hHol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρ g)) :
    ∃ (χ : h84a_pointStabilizer ρ p →* ℂˣ) (r : ℝ)
      (u : OpenPartialHomeomorph X ℂ),
      Function.Injective χ ∧ 0 < r ∧ p ∈ u.source ∧ u p = 0 ∧
      u.target = Metric.ball 0 r ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u u.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u.symm u.target ∧
      (∀ k : h84a_pointStabilizer ρ p, MapsTo (ρ (k : G)) u.source u.source) ∧
      (∀ k : h84a_pointStabilizer ρ p, ∀ x ∈ u.source,
        u (ρ (k : G) x) = (χ k : ℂ) * u x) ∧
      (∀ g : G, ∀ x ∈ u.source, ∀ y ∈ u.source,
        ρ g x = y → ρ g p = p) := by
  classical
  let K := h84a_pointStabilizer ρ p
  letI := Fintype.ofFinite K
  let ρK : K →* (X ≃ₜ X) := ρ.comp K.subtype
  have hρK : Function.Injective ρK := by
    intro k l he
    exact Subtype.ext (hρ he)
  obtain ⟨S, hSo, hpS, _hSI, hSep⟩ := h84g_exists_stabilizer_slice ρ p
  obtain ⟨χ, a, hχ, hpA, ha0, hAI, hAL, hAH, hAiH⟩ :=
    h84g_surface_linearizing_chart ρK hρK p (fun k => k.property)
      (fun k => hHol (k : G))
  obtain ⟨N, hN, hNH⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (by simp : (ω : WithTop ℕ∞) ≠ ∞)).mp hAiH
  obtain ⟨O, hON, hOo, h0O⟩ := mem_nhds_iff.mp hN
  let W : Set X := S ∩ (a.source ∩ a ⁻¹' O)
  have hWo : IsOpen W :=
    hSo.inter (a.continuousOn.isOpen_inter_preimage a.open_source hOo)
  have hpW : p ∈ W := ⟨hpS, hpA, by
    change a p ∈ O
    rw [ha0]
    exact h0O⟩
  obtain ⟨r, u, hr, hpU, hu0, huT, hUW, hUA, hu, hui, hUI, hUL⟩ :=
    h84g_shrink_rotation_chart ρK χ (fun k => h84q_character_norm χ k)
      a p hpA ha0 hAI hAL W hWo hpW
  have htO : u.target ⊆ O := by
    intro z hz
    have hw := hUW (u.symm.mapsTo hz)
    have he : u (u.symm z) = z := u.right_inv hz
    have hzO : a (u.symm z) ∈ O := hw.2.2
    rw [← hu, he] at hzO
    exact hzO
  refine ⟨χ, r, u, hχ, hr, hpU, hu0, huT, ?_, ?_, hUI, hUL, ?_⟩
  · simpa only [hu] using hAH.mono hUA
  · simpa only [hui] using hNH.mono (htO.trans hON)
  · intro g x hx y hy hxy
    exact hSep g x (hUW hx).1 y (hUW hy).1 hxy

/-- Descend an actual equivariant disk slice by the power map. The degree is the
order of the actual stabilizer, and the source is the actual orbit image. -/
theorem h84g_power_chart_of_disk_slice
    {G X : Type*} [Group G] [Finite G] [TopologicalSpace X]
    (ρ : G →* (X ≃ₜ X)) (p : X)
    (χ : h84a_pointStabilizer ρ p →* ℂˣ) (hχ : Function.Injective χ)
    (r : ℝ) (hr : 0 < r) (u : OpenPartialHomeomorph X ℂ)
    (hpU : p ∈ u.source) (huT : u.target = Metric.ball 0 r)
    (hUI : ∀ k : h84a_pointStabilizer ρ p, MapsTo (ρ (k : G)) u.source u.source)
    (hUL : ∀ k : h84a_pointStabilizer ρ p, ∀ x ∈ u.source,
      u (ρ (k : G) x) = (χ k : ℂ) * u x)
    (hSep : ∀ g : G, ∀ x ∈ u.source, ∀ y ∈ u.source,
      ρ g x = y → ρ g p = p) :
    ∃ v : OpenPartialHomeomorph (h84g_OrbitSpace ρ) ℂ,
      v.source = h84g_orbitMap ρ '' u.source ∧
      v.target = Metric.ball 0 (r ^ Nat.card (h84a_pointStabilizer ρ p)) ∧
      ∀ x ∈ u.source, v (h84g_orbitMap ρ x) =
        (u x) ^ Nat.card (h84a_pointStabilizer ρ p) := by
  classical
  let K := h84a_pointStabilizer ρ p
  letI := Fintype.ofFinite K
  let E : u.source ≃ₜ Metric.ball (0 : ℂ) r :=
    u.toHomeomorphSourceTarget.trans (Homeomorph.setCongr huT)
  let f := h84q_diskPower (Fintype.card K) Fintype.card_ne_zero r ∘ E
  have hf : IsOpenQuotientMap f :=
    (h84q_diskPower_isOpenQuotientMap (Fintype.card K) Fintype.card_ne_zero r hr).comp
      ⟨E.surjective, E.continuous, E.isOpenMap⟩
  have hker : ∀ x y : u.source,
      h84g_orbitMap ρ x = h84g_orbitMap ρ y ↔ f x = f y := by
    intro x y
    rw [h84g_slice_fiber_iff ρ p u.source hSep x.property y.property]
    have hpower : f x = f y ↔
        (u x) ^ Fintype.card K = (u y) ^ Fintype.card K := by
      exact Subtype.ext_iff
    rw [hpower, h84q_power_fiber_iff_orbit χ hχ]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← hk]
      exact hUL k x x.property
    · rintro ⟨k, hk⟩
      refine ⟨k, u.injOn (hUI k x.property) y.property ?_⟩
      exact (hUL k x x.property).trans hk.symm
  obtain ⟨v, hvS, hvT, hv⟩ := h84g_quotient_chart_of_local_model ρ
    u.source u.open_source ⟨p, hpU⟩ (Metric.ball 0 (r ^ Fintype.card K))
    Metric.isOpen_ball f hf hker
  refine ⟨v, hvS, ?_, ?_⟩
  · simpa only [Nat.card_eq_fintype_card] using hvT
  · intro x hx
    have he := hv ⟨x, hx⟩
    change v (h84g_orbitMap ρ x) = (u x) ^ Fintype.card K at he
    simpa only [Nat.card_eq_fintype_card] using he

/-- A genuine local power chart on the global orbit space, at every surface point.
The surface coordinate and its inverse are analytic. Analytic compatibility of the
quotient charts is a separate next step, not an assumption of this theorem. -/
theorem h84g_exists_surface_power_chart
    {G X : Type*} [Group G] [Finite G] [TopologicalSpace X] [ChartedSpace ℂ X]
    [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (ρ : G →* (X ≃ₜ X)) (hρ : Function.Injective ρ) (p : X)
    (hHol : ∀ g, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (ρ g)) :
    ∃ (r : ℝ) (u : OpenPartialHomeomorph X ℂ)
      (v : OpenPartialHomeomorph (h84g_OrbitSpace ρ) ℂ),
      0 < r ∧ p ∈ u.source ∧ u p = 0 ∧ u.target = Metric.ball 0 r ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u u.source ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω u.symm u.target ∧
      v.source = h84g_orbitMap ρ '' u.source ∧
      v.target = Metric.ball 0 (r ^ Nat.card (h84a_pointStabilizer ρ p)) ∧
      ∀ x ∈ u.source, v (h84g_orbitMap ρ x) =
        (u x) ^ Nat.card (h84a_pointStabilizer ρ p) := by
  obtain ⟨χ, r, u, hχ, hr, hpU, hu0, huT, huH, huiH, hUI, hUL, hSep⟩ :=
    h84g_exists_disk_slice ρ hρ p hHol
  obtain ⟨v, hvS, hvT, hv⟩ :=
    h84g_power_chart_of_disk_slice ρ p χ hχ r hr u hpU huT hUI hUL hSep
  exact ⟨r, u, v, hr, hpU, hu0, huT, huH, huiH, hvS, hvT, hv⟩

end LiZhongQC

