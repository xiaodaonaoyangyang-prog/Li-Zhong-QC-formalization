import LiZhongQC.Lemmas.FiniteTypeComponentTrapping
import LiZhongQC.Lemmas.FiniteTypeChartInverse
import LiZhongQC.Lemmas.FiniteTypeHoleBridge

open Complex Set Metric Filter Topology
open scoped Manifold ContDiff
noncomputable section
namespace LiZhongQC
universe u

/-- Arbitrarily small actual puncture coordinates, avoiding every other
deleted point and all deleted discs. -/
theorem s31eg_puncture_chart {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    {p : F.X.carrier} (hp : p ∈ F.P) (U : Set F.X.carrier) (hU : U ∈ 𝓝 p) :
    ∃ r : ℝ, 0 < r ∧ ball (chartAt ℂ p p) r ⊆ (chartAt ℂ p).target ∧
      (∀ z ∈ ball (chartAt ℂ p p) r, (chartAt ℂ p).symm z ∈ U) ∧
      ∀ z ∈ ball (chartAt ℂ p p) r \ {chartAt ℂ p p},
        (chartAt ℂ p).symm z ∈ range F.ι := by
  let e := chartAt ℂ p
  let H : Set F.X.carrier := ⋃ j, F.D j
  have hH : IsClosed H := (isCompact_iUnion (fun j => s31eg_disc_compact (F.disc j))).isClosed
  have hpH : p ∉ H := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.1 h
    exact disjoint_left.1 (F.disjoint_P j) hj hp
  let V : Set F.X.carrier := ((U ∩ Hᶜ) ∩ ((↑F.P : Set F.X.carrier) \ {p})ᶜ) ∩ e.source
  have hpV : V ∈ 𝓝 p :=
    Filter.inter_mem
      (Filter.inter_mem (Filter.inter_mem hU (hH.isOpen_compl.mem_nhds hpH))
        ((F.P.finite_toSet.subset sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)))
      (e.open_source.mem_nhds (mem_chart_source ℂ p))
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.1
    (e.image_mem_nhds (mem_chart_source ℂ p) hpV)
  have ht : ball (e p) r ⊆ e.target := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hb hz
    exact e.map_source hy.2
  have hv : ∀ z ∈ ball (e p) r, e.symm z ∈ V := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hb hz
    rwa [e.left_inv hy.2]
  refine ⟨r, hr, ht, fun z hz => (hv z hz).1.1.1, ?_⟩
  intro z hz
  rw [F.range_ι]
  rintro (hP | hD)
  · apply (hv z hz.1).1.2
    refine ⟨hP, ?_⟩
    intro he
    apply hz.2
    change z = e p
    rw [← e.right_inv (ht hz.1), mem_singleton_iff.1 he]
  · exact (hv z hz.1).1.1.2 hD

/-- Compact chart trapping around a whole deleted disc is constructed by
shrinking its open chart neighborhood. -/
theorem s31eg_disc_chart_neighborhood {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ChartedSpace ℂ X]
    {D : Set X} (hD : IsClosedDiscIn D) :
    ∃ (x : X) (J : Set ℂ) (W : Set X) (K : Set ℂ),
      D ⊆ (chartAt ℂ x).source ∧ chartAt ℂ x '' D = closure J ∧ IsJordanDomain J ∧
      IsOpen W ∧ D ⊆ W ∧ closure W ⊆ (chartAt ℂ x).source ∧
      IsCompact K ∧ K ⊆ (chartAt ℂ x).target ∧
      ∀ y ∈ W, chartAt ℂ x y ∈ K := by
  have hDc := s31eg_disc_compact hD
  obtain ⟨x, hDs, J, hJ, _hJb, _hJt, hDJ, _hc⟩ := hD
  obtain ⟨W, hWo, hDW, hWs⟩ := hDc.exists_isOpen_closure_subset
    ((chartAt ℂ x).open_source.mem_nhdsSet.2 hDs)
  refine ⟨x, J, W, chartAt ℂ x '' closure W, hDs, hDJ, hJ, hWo, hDW, hWs,
    isClosed_closure.isCompact.image_of_continuousOn
      ((chartAt ℂ x).continuousOn.mono hWs), ?_, ?_⟩
  · rintro z ⟨y, hy, rfl⟩
    exact (chartAt ℂ x).map_source (hWs hy)
  · intro y hy
    exact ⟨y, subset_closure hy, rfl⟩

/-- Singleton-component trapping is exactly convergence to that puncture. -/
theorem s31eg_singleton_trapping_tendsto {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (i : A → X) (j : A → Y) {p : X} {q : Y}
    (htrap : ∀ W : Set Y, IsOpen W → ({q} : Set Y) ⊆ W →
      ∃ U ∈ 𝓝 p, ∀ a, i a ∈ U → j a ∈ W) :
    Tendsto j (comap i (𝓝 p)) (𝓝 q) := by
  apply _root_.tendsto_nhds.mpr
  intro W hWo hqW
  obtain ⟨U, hU, hUW⟩ := htrap W hWo (singleton_subset_iff.2 hqW)
  exact mem_of_superset (preimage_mem_comap hU) (fun a ha => hUW a ha)

/-- A genuine limiting point must belong to the compact component approached
by all end neighborhoods. -/
theorem s31eg_limit_mem_component {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] [CompactSpace Y]
    (i : A → X) (j : A → Y) {p : X} {q : Y} [NeBot (comap i (𝓝 p))]
    {D : Set Y} (hD : IsCompact D)
    (htrap : ∀ W : Set Y, IsOpen W → D ⊆ W →
      ∃ U ∈ 𝓝 p, ∀ a, i a ∈ U → j a ∈ W)
    (ht : Tendsto j (comap i (𝓝 p)) (𝓝 q)) : q ∈ D := by
  by_contra hq
  obtain ⟨W, V, hW, hV, hDW, hqV, hWV⟩ := normal_separation
    hD.isClosed isClosed_singleton (disjoint_singleton_right.2 hq)
  obtain ⟨U, hU, hUW⟩ := htrap W hW hDW
  have hmemW : ∀ᶠ a in comap i (𝓝 p), j a ∈ W :=
    mem_of_superset (preimage_mem_comap hU) (fun a ha => hUW a ha)
  have hmemV : ∀ᶠ a in comap i (𝓝 p), j a ∈ V :=
    ht (hV.mem_nhds (hqV (mem_singleton q)))
  obtain ⟨a, haW, haV⟩ := (hmemW.and hmemV).exists
  exact disjoint_left.1 hWV haW haV

/-- A puncture cannot converge as an end to a deleted disc. Both the compact
coordinate trap and the holomorphic coordinate inverse are constructed from
the actual finite-type presentations. -/
theorem s31eg_puncture_not_hole {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [Nonempty S]
    {g n m g' n' m' : ℕ} (F : FiniteTypeStructure S g n m)
    (G : FiniteTypeStructure S g' n' m') {p : F.X.carrier} (hp : p ∈ F.P)
    (k : Fin m')
    (htrap : ∀ W : Set G.X.carrier, IsOpen W → G.D k ⊆ W →
      ∃ U ∈ 𝓝 p, ∀ a, F.ι a ∈ U → G.ι a ∈ W) : False := by
  letI := s31eg_puncture_neBot F hp
  obtain ⟨x, J, W, K, hDs, hDJ, hJ, hWo, hDW, hWs, hK, hKt, hWK⟩ :=
    s31eg_disc_chart_neighborhood (G.disc k)
  obtain ⟨U, hU, hUW⟩ := htrap W hWo hDW
  obtain ⟨r, hr, hrt, hrU, hrr⟩ := s31eg_puncture_chart F hp U hU
  let e := chartAt ℂ p
  let b := chartAt ℂ x
  let A : Set S := F.ι ⁻¹' e.source
  let φ : S → ℂ := e ∘ F.ι
  let ψ : ℂ → S := Function.invFunOn φ A
  have hAo : IsOpen A := e.open_source.preimage F.embedding.continuous
  have hφi : InjOn φ A := by
    intro a ha c hc he
    exact F.embedding.injective (e.injOn ha hc he)
  have hφd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) φ A := by
    intro a ha
    exact ((mdifferentiableAt_atlas (chart_mem_atlas ℂ p) ha).comp a
      (F.holomorphic a)).mdifferentiableWithinAt
  have himg : ∀ z ∈ ball (e p) r \ {e p}, z ∈ φ '' A := by
    intro z hz
    obtain ⟨a, ha⟩ := hrr z hz
    refine ⟨a, ?_, ?_⟩
    · change F.ι a ∈ e.source
      rw [ha]
      exact e.map_target (hrt hz.1)
    · change e (F.ι a) = z
      rw [ha, e.right_inv (hrt hz.1)]
  have hmodel : ∀ z ∈ ball (e p) r \ {e p}, F.ι (ψ z) = e.symm z := by
    intro z hz
    have hzimg := himg z hz
    have hψA : ψ z ∈ A := Function.invFunOn_mem hzimg
    change F.ι (ψ z) ∈ e.source at hψA
    apply e.injOn hψA (e.map_target (hrt hz.1))
    exact (Function.invFunOn_eq hzimg).trans (e.right_inv (hrt hz.1)).symm
  have hψd : ∀ z ∈ ball (e p) r \ {e p}, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ z :=
    fun z hz => s31eg_coordinate_inverse hAo hφi hφd (himg z hz)
  have hGW : ∀ z ∈ ball (e p) r \ {e p}, G.ι (ψ z) ∈ W := by
    intro z hz
    apply hUW
    rw [hmodel z hz]
    exact hrU z hz.1
  have hGs : ∀ z ∈ ball (e p) r \ {e p}, G.ι (ψ z) ∈ b.source :=
    fun z hz => hWs (subset_closure (hGW z hz))
  have hd : DifferentiableOn ℂ (b ∘ (G.ι ∘ ψ)) (ball (e p) r \ {e p}) := by
    intro z hz
    have hm := (mdifferentiableAt_atlas (chart_mem_atlas ℂ x) (hGs z hz)).comp z
      ((G.holomorphic (ψ z)).comp z (hψd z hz))
    exact (mdifferentiableAt_iff_differentiableAt.1 hm).differentiableWithinAt
  have hi : InjOn (b ∘ (G.ι ∘ ψ)) (ball (e p) r \ {e p}) := by
    intro z hz w hw he
    have hψeq : ψ z = ψ w := G.embedding.injective (b.injOn (hGs z hz) (hGs w hw) he)
    calc
      z = φ (ψ z) := (Function.invFunOn_eq (himg z hz)).symm
      _ = φ (ψ w) := congrArg φ hψeq
      _ = w := Function.invFunOn_eq (himg w hw)
  have havoid : ∀ z ∈ ball (e p) r \ {e p}, (G.ι ∘ ψ) z ∉ G.D k := by
    intro z _ hz
    have hg : G.ι (ψ z) ∈ range G.ι := ⟨ψ z, rfl⟩
    rw [G.range_ι] at hg
    exact hg (Or.inr (mem_iUnion.2 ⟨k, hz⟩))
  obtain ⟨q, _hqs, hqD, hlim⟩ := s31he_chart_endpoint_avoids_disc b hDs hDJ hJ.1
    hK hKt hr hGs (fun z hz => hWK _ (hGW z hz)) hd hi havoid
  have hFi : Tendsto F.ι (comap F.ι (𝓝 p)) (𝓝 p) := map_comap_le
  have hφt : Tendsto φ (comap F.ι (𝓝 p)) (𝓝[≠] (e p)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨(e.continuousAt (mem_chart_source ℂ p)).tendsto.comp hFi, ?_⟩
    have hAm : A ∈ comap F.ι (𝓝 p) :=
      preimage_mem_comap (e.open_source.mem_nhds (mem_chart_source ℂ p))
    filter_upwards [hAm] with a ha
    change φ a ≠ e p
    intro he
    have hep : F.ι a = p := e.injOn ha (mem_chart_source ℂ p) he
    have hpa : p ∈ range F.ι := ⟨a, hep⟩
    rw [F.range_ι] at hpa
    exact hpa (Or.inl hp)
  have hGt : Tendsto G.ι (comap F.ι (𝓝 p)) (𝓝 q) := by
    have ht := hlim.comp hφt
    apply ht.congr'
    have hAm : A ∈ comap F.ι (𝓝 p) :=
      preimage_mem_comap (e.open_source.mem_nhds (mem_chart_source ℂ p))
    filter_upwards [hAm] with a ha
    change G.ι (ψ (φ a)) = G.ι a
    exact congrArg G.ι (hφi.leftInvOn_invFunOn ha)
  exact hqD (s31eg_limit_mem_component F.ι G.ι (s31eg_disc_compact (G.disc k)) htrap hGt)

/-- Every actual puncture of one finite-type presentation has an actual
puncture limit in every other presentation of the same complex surface. -/
theorem s31eg_puncture_endpoint {S : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [Nonempty S]
    {g n m g' n' m' : ℕ} (F : FiniteTypeStructure S g n m)
    (G : FiniteTypeStructure S g' n' m') {p : F.X.carrier} (hp : p ∈ F.P) :
    ∃ q ∈ G.P, Tendsto G.ι (comap F.ι (𝓝 p)) (𝓝 q) := by
  obtain ⟨k, hk⟩ := s31eg_puncture_component F G hp
  cases k with
  | inl q =>
    exact ⟨q.1, q.2, s31eg_singleton_trapping_tendsto F.ι G.ι hk⟩
  | inr k => exact (s31eg_puncture_not_hole F G hp k hk).elim

end LiZhongQC

