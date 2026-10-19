import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.QDReflectionPunctureSeam

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u v

/-- The simple-pole normal form (with value `0` at the pole) of a differential family at a point
`p` read in a chart `p` transfers to any other chart `x` containing `p`. -/
theorem s31qd_pole_transfer {M : Type v} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] {q : M → ℂ → ℂ} (hq : IsDiffFamily 2 0 q) (x p : M)
    (hp : p ∈ (chartAt ℂ x).source) {c : ℂ} {r : ℂ → ℂ}
    (hz : q p (chartAt ℂ p p) = 0) (hr : AnalyticAt ℂ r (chartAt ℂ p p))
    (he : ∀ᶠ z in 𝓝[≠] (chartAt ℂ p p), q p z = c / (z - chartAt ℂ p p) + r z) :
    ∃ (c' : ℂ) (r' : ℂ → ℂ), AnalyticAt ℂ r' (chartAt ℂ x p) ∧
      ∀ᶠ z in 𝓝[≠] (chartAt ℂ x p), q x z = c' / (z - chartAt ℂ x p) + r' z := by
  classical
  let w := chartAt ℂ x p
  let φ : ℂ → ℂ := chartTransition p x
  have hw : w ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hp
  have hleft : (chartAt ℂ x).symm w = p := (chartAt ℂ x).left_inv hp
  have hφw : φ w = chartAt ℂ p p := by
    change chartAt ℂ p ((chartAt ℂ x).symm w) = _
    rw [hleft]
  let W : Set ℂ := (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ p).source
  have hWo : IsOpen W :=
    (chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ p).open_source
  have hwW : w ∈ W := ⟨hw, by rw [Set.mem_preimage, hleft]; exact mem_chart_source ℂ p⟩
  have hTd : DifferentiableOn ℂ φ W := by
    intro z hz'
    exact (s31qr_coordinate_differentiable (H := fun y : M => y) x p hz'.1 hz'.2
      (mdifferentiableAt_id)).differentiableWithinAt
  have hτ : AnalyticAt ℂ φ w := hTd.analyticOnNhd hWo w hwW
  have hd : deriv φ w ≠ 0 :=
    s31qr_coordinate_deriv_ne_zero (H := fun y : M => y) isOpen_univ
      (fun _ _ => mdifferentiableAt_id) Function.injective_id.injOn x p hw (mem_univ _) hwW.2
  have hz0 : q p (φ w) = 0 := by rw [hφw]; exact hz
  have hr' : AnalyticAt ℂ r (φ w) := by rw [hφw]; exact hr
  have he' : q p =ᶠ[𝓝[≠] (φ w)] (fun z => c / (z - φ w) + r z) := by
    rw [hφw]; exact he
  obtain ⟨_, c', r', hr'', hexp⟩ := s31qr_simple_pole_pullback hτ hd hz0 hr' he'
  refine ⟨c', r', hr'', ?_⟩
  have hloc : ∀ z ∈ W, q x z = q p (φ z) * deriv φ z ^ 2 := by
    intro z hz'
    have hh := hq.2 p x z hz'.1 hz'.2
    simpa only [zpow_zero, mul_one, zpow_two, pow_two] using hh
  filter_upwards [nhdsWithin_le_nhds (s := {w}ᶜ) (hWo.mem_nhds hwW), hexp] with z hz1 hz2
  rw [hloc z hz1]
  exact hz2

/-- The pull-back `q` of an admissible differential `Q` of `Fd` has a simple pole (in the chart of the
puncture) at every original puncture: the pull-back map extends non-ramified over the puncture. -/
theorem s31qd_pole_chart_p0 {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    [IsManifold 𝓘(ℂ) ω S] [Nonempty S]
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {gd nd : ℕ} (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)
    (E : Xd.carrier ≃ₜ Fd.X.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Fd.X.carrier))
    (hP : ∀ p : Xd.carrier, p ∈ Pd ↔ E p ∈ Fd.P)
    {Q : Fd.X.carrier → ℂ → ℂ} (hQ : IsAdmissibleQD Fd Q) {q : F.X.carrier → ℂ → ℂ}
    (hq : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range F.ι →
        q x z = s31qr_transportOn (range F.ι)
          (fun y : F.X.carrier => E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y)))
          (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x z)
    {p₀ : F.X.carrier} (hp : p₀ ∈ F.P) :
    ∃ (c : ℂ) (r : ℂ → ℂ), AnalyticAt ℂ r (chartAt ℂ p₀ p₀) ∧
      ∀ᶠ z in 𝓝[≠] (chartAt ℂ p₀ p₀), q p₀ z = c / (z - chartAt ℂ p₀ p₀) + r z := by
  classical
  obtain ⟨y₀, ⟨hy₀, ht⟩, -⟩ := s31qr_original_puncture_endpoint F hd hp
  set a : Fd.X.carrier := E y₀ with ha
  have haP : a ∈ Fd.P := (hP y₀).1 hy₀
  set b := chartAt ℂ p₀ with hb
  set ρ : F.X.carrier → S := fun y' => (F.embedding.toOpenPartialHomeomorph F.ι).symm y' with hρ
  let G : F.X.carrier → Fd.X.carrier := fun y' => E (ιd (ρ y'))
  have hρι : ∀ y' ∈ range F.ι, F.ι (ρ y') = y' := fun y' hy' =>
    F.embedding.toOpenPartialHomeomorph_right_inv F.ι hy'
  have ht' : Tendsto (fun s => E (ιd s)) (comap F.ι (𝓝 p₀)) (𝓝 a) :=
    (E.continuous.tendsto y₀).comp ht
  have hev : ∀ᶠ s in comap F.ι (𝓝 p₀), E (ιd s) ∈ (chartAt ℂ a).source :=
    ht'.eventually ((chartAt ℂ a).open_source.mem_nhds (mem_chart_source ℂ a))
  obtain ⟨U₁, hU₁, hsub⟩ := Filter.mem_comap.1 hev
  obtain ⟨r, hr, hrt, hrU, hrr⟩ := s31eg_puncture_chart F hp U₁ hU₁
  have hmem : ∀ u ∈ ball (b p₀) r \ {b p₀}, F.ι (ρ (b.symm u)) = b.symm u :=
    fun u hu => hρι _ (hrr u hu)
  have hsrc : ∀ u ∈ ball (b p₀) r \ {b p₀}, G (b.symm u) ∈ (chartAt ℂ a).source :=
    fun u hu => hsub (show F.ι (ρ (b.symm u)) ∈ U₁ by rw [hmem u hu]; exact hrU u hu.1)
  have hHd : ∀ u ∈ ball (b p₀) r \ {b p₀}, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) G (b.symm u) := by
    intro u hu
    exact (hE.1 _).comp _ ((hd.holomorphic _).comp _
      (s31qr_open_embedding_inverse F.embedding F.holomorphic (hrr u hu)))
  let f : ℂ → ℂ := fun u => chartAt ℂ a (G (b.symm u))
  have hdiff : DifferentiableOn ℂ f (ball (b p₀) r \ {b p₀}) := by
    intro u hu
    exact (s31qr_coordinate_differentiable (H := G) p₀ a (hrt hu.1) (hsrc u hu)
      (hHd u hu)).differentiableWithinAt
  have hinj : InjOn f (ball (b p₀) r \ {b p₀}) := by
    intro u₁ h₁ u₂ h₂ he
    have e1 := (chartAt ℂ a).injOn (hsrc u₁ h₁) (hsrc u₂ h₂) he
    have e2 := hd.embedding.injective (E.injective e1)
    have e3 : b.symm u₁ = b.symm u₂ := by rw [← hmem u₁ h₁, ← hmem u₂ h₂, e2]
    calc u₁ = b (b.symm u₁) := (b.right_inv (hrt h₁.1)).symm
      _ = b (b.symm u₂) := by rw [e3]
      _ = u₂ := b.right_inv (hrt h₂.1)
  have hnear : ∀ᶠ u in 𝓝[≠] (b p₀), u ∈ ball (b p₀) r \ {b p₀} := by
    filter_upwards [nhdsWithin_le_nhds (s := {b p₀}ᶜ) (ball_mem_nhds (b p₀) hr),
      self_mem_nhdsWithin] with z hz hne
    exact ⟨hz, hne⟩
  have hbT : Tendsto b.symm (𝓝[≠] (b p₀)) (𝓝 p₀) := by
    have h := (b.continuousAt_symm (b.map_source (mem_chart_source ℂ p₀))).tendsto
    rw [b.left_inv (mem_chart_source ℂ p₀)] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hback : Tendsto (fun u => F.ι (ρ (b.symm u))) (𝓝[≠] (b p₀)) (𝓝 p₀) := by
    apply hbT.congr'
    filter_upwards [hnear] with u hu
    exact (hmem u hu).symm
  have hψT : Tendsto (fun u => ρ (b.symm u)) (𝓝[≠] (b p₀)) (comap F.ι (𝓝 p₀)) :=
    tendsto_comap_iff.2 hback
  have hlim : Tendsto f (𝓝[≠] (b p₀)) (𝓝 (chartAt ℂ a a)) :=
    ((chartAt ℂ a).continuousAt (mem_chart_source ℂ a)).tendsto.comp (ht'.comp hψT)
  obtain ⟨τ, hτa, hτ0, hτd, hτeq⟩ := s31pp_extend_nonramified hr hdiff hinj hlim
  have hloc : ∀ u ∈ ball (b p₀) r \ {b p₀}, q p₀ u = Q a (τ u) * deriv τ u ^ 2 := by
    intro u hu
    have hz : u ∈ (chartAt ℂ p₀).target := hrt hu.1
    have hl := s31qr_transport_local (U := range F.ι) (H := G) hQ.1 p₀ a hz (hrr u hu)
      (hsrc u hu) (hHd u hu)
    have hev2 : f =ᶠ[𝓝 u] τ := by
      filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds hu] with w hw
      exact (hτeq w hw).symm
    rw [hq p₀ u hz (hrr u hu)]
    change s31qr_transportOn (range F.ι) G (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q p₀ u = _
    rw [hl, hev2.deriv_eq, show chartAt ℂ a (G (b.symm u)) = τ u from (hτeq u hu).symm]
  obtain ⟨hz0, c, r', hra, he⟩ := hQ.2.2.1 a a haP (mem_chart_source ℂ a)
  obtain ⟨_, c', r'', hr'', hexp⟩ := s31qr_simple_pole_pullback (f := Q a) (r := r') (τ := τ)
    (p := b p₀) (c := c) hτa hτd (by rw [hτ0]; exact hz0) (by rw [hτ0]; exact hra)
    (by rw [hτ0]; exact he)
  refine ⟨c', r'', hr'', ?_⟩
  filter_upwards [hnear, hexp] with u hu1 hu2
  rw [hloc u hu1]
  exact hu2

/-- (a) Simple poles of the pull-back at every original puncture, in every chart. -/
theorem s31qd_puncture_pole {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    [IsManifold 𝓘(ℂ) ω S] [Nonempty S]
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    {gd nd : ℕ} (Fd : FiniteTypeStructure (puncturedOpens Pd) gd nd 0)
    (E : Xd.carrier ≃ₜ Fd.X.carrier) (hE : IsBiholomorphic (E : Xd.carrier → Fd.X.carrier))
    (hP : ∀ p : Xd.carrier, p ∈ Pd ↔ E p ∈ Fd.P)
    {Q : Fd.X.carrier → ℂ → ℂ} (hQ : IsAdmissibleQD Fd Q) {q : F.X.carrier → ℂ → ℂ}
    (hqd : IsDiffFamily 2 0 q)
    (hq : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range F.ι →
        q x z = s31qr_transportOn (range F.ι)
          (fun y : F.X.carrier => E (ιd ((F.embedding.toOpenPartialHomeomorph F.ι).symm y)))
          (LinearMap.id : ℂ →ₗ[ℝ] ℂ) Q x z)
    (hq0 : ∀ (x : F.X.carrier), ∀ p ∈ F.P, p ∈ (chartAt ℂ x).source → q x (chartAt ℂ x p) = 0) :
    ∀ (x : F.X.carrier), ∀ p ∈ F.P, p ∈ (chartAt ℂ x).source →
      ∃ (c : ℂ) (r : ℂ → ℂ), AnalyticAt ℂ r (chartAt ℂ x p) ∧
        ∀ᶠ z in 𝓝[≠] (chartAt ℂ x p), q x z = c / (z - chartAt ℂ x p) + r z := by
  intro x p hp hs
  obtain ⟨c, r, hr, he⟩ := s31qd_pole_chart_p0 F hd Fd E hE hP hQ hq hp
  obtain ⟨c', r', hr', he'⟩ := s31qd_pole_transfer hqd x p hs
    (hq0 p p hp (mem_chart_source ℂ p)) hr he
  exact ⟨c', r', hr', he'⟩

end LiZhongQC
