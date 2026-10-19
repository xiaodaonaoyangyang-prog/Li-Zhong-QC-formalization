import LiZhongQC.Lemmas.QDReflectionAfterHalves
import LiZhongQC.Lemmas.QDReflectionPunctureSeam
import LiZhongQC.Lemmas.QDReflectionEndpointProbe
import LiZhongQC.Lemmas.Conformal
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

open Complex Set Metric Filter Topology
open scoped ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC
universe u

/-- A holomorphic map on a punctured disc, injective there and with a limit at the
puncture, extends (by the limit) to an injective analytic map of the whole disc. -/
theorem s31pp_update_injOn {f : ℂ → ℂ} {u₀ w : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball u₀ r \ {u₀}))
    (hinj : InjOn f (ball u₀ r \ {u₀}))
    (ht : Tendsto f (𝓝[≠] u₀) (𝓝 w)) :
    DifferentiableOn ℂ (Function.update f u₀ w) (ball u₀ r) ∧
      InjOn (Function.update f u₀ w) (ball u₀ r) := by
  classical
  set g : ℂ → ℂ := Function.update f u₀ w with hg
  have hgu : g u₀ = w := Function.update_self _ _ _
  have hgne : ∀ u, u ≠ u₀ → g u = f u := fun u hu => Function.update_of_ne hu _ _
  have hball : ball u₀ r ∈ 𝓝 u₀ := ball_mem_nhds u₀ hr
  have hopen : IsOpen (ball u₀ r \ {u₀}) := isOpen_ball.sdiff isClosed_singleton
  have hgd : DifferentiableOn ℂ g (ball u₀ r \ {u₀}) :=
    hd.congr (fun u hu => hgne u hu.2)
  have hgc : ContinuousAt g u₀ := by
    refine continuousAt_iff_punctured_nhds.2 ?_
    rw [hgu]
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (hgne u hu).symm
  have hga : AnalyticAt ℂ g u₀ := by
    refine analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ hgc
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hball] with z hz1 hz2
    exact (hgd.differentiableAt (hopen.mem_nhds ⟨hz2, hz1⟩))
  have hDiff : DifferentiableOn ℂ g (ball u₀ r) := by
    intro u hu
    by_cases h : u = u₀
    · subst h
      exact hga.differentiableAt.differentiableWithinAt
    · exact (hgd.differentiableAt (hopen.mem_nhds ⟨hu, h⟩)).differentiableWithinAt
  refine ⟨hDiff, ?_⟩
  -- the only possible failure of injectivity is a second preimage of `w`
  have hsecond : ∀ u₁ ∈ ball u₀ r, u₁ ≠ u₀ → f u₁ = w → False := by
    intro u₁ hu₁ hne hfu
    have hga₁ : AnalyticAt ℂ g u₁ := hgd.analyticAt (hopen.mem_nhds ⟨hu₁, hne⟩)
    have hgu₁ : g u₁ = w := by rw [hgne u₁ hne, hfu]
    -- g is open at u₀ and at u₁
    have hopen₀ : 𝓝 w ≤ map g (𝓝 u₀) := by
      rcases hga.eventually_constant_or_nhds_le_map_nhds with hconst | hmap
      · exfalso
        have hev : ∀ᶠ z in 𝓝[≠] u₀, g z = w ∧ z ∈ ball u₀ r ∧ z ≠ u₁ := by
          filter_upwards [nhdsWithin_le_nhds hconst, nhdsWithin_le_nhds hball,
            nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds
              (show u₀ ∈ ({u₁}ᶜ : Set ℂ) from Ne.symm hne))] with z h1 h2 h3
          exact ⟨by rw [h1, hgu], h2, h3⟩
        obtain ⟨z, ⟨hz1, hz2, hz3⟩, hz4⟩ := (hev.and self_mem_nhdsWithin).exists
        apply hz3
        apply hinj ⟨hz2, hz4⟩ ⟨hu₁, hne⟩
        rw [← hgne z hz4, hz1, hfu]
      · rwa [hgu] at hmap
    have hopen₁ : 𝓝 w ≤ map g (𝓝 u₁) := by
      rcases hga₁.eventually_constant_or_nhds_le_map_nhds with hconst | hmap
      · exfalso
        have hev : ∀ᶠ z in 𝓝[≠] u₁, g z = w ∧ z ∈ ball u₀ r ∧ z ≠ u₀ := by
          filter_upwards [nhdsWithin_le_nhds hconst,
            nhdsWithin_le_nhds (isOpen_ball.mem_nhds hu₁),
            nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds
              (show u₁ ∈ ({u₀}ᶜ : Set ℂ) from hne))]
            with z h1 h2 h3
          exact ⟨by rw [h1, hgu₁], h2, h3⟩
        obtain ⟨z, ⟨hz1, hz2, hz3⟩, hz4⟩ := (hev.and self_mem_nhdsWithin).exists
        apply hz4
        apply hinj ⟨hz2, hz3⟩ ⟨hu₁, hne⟩
        rw [← hgne z hz3, hz1, hfu]
      · rwa [hgu₁] at hmap
    obtain ⟨N₀, N₁, hN₀, hN₁, h0, h1, hdisj⟩ := t2_separation hne.symm
    have hA : g '' (N₀ ∩ ball u₀ r) ∈ 𝓝 w := hopen₀ (image_mem_map
      (inter_mem (hN₀.mem_nhds h0) hball))
    have hB : g '' (N₁ ∩ ball u₀ r) ∈ 𝓝 w := hopen₁ (image_mem_map
      (inter_mem (hN₁.mem_nhds h1) (isOpen_ball.mem_nhds hu₁)))
    have hAB : ∀ᶠ z in 𝓝[≠] w, z ∈ g '' (N₀ ∩ ball u₀ r) ∩ g '' (N₁ ∩ ball u₀ r) :=
      mem_nhdsWithin_of_mem_nhds (inter_mem hA hB)
    obtain ⟨z, ⟨⟨a, ⟨ha0, haB⟩, rfl⟩, ⟨b, ⟨hb1, hbB⟩, hbz⟩⟩, hzw⟩ :=
      (hAB.and self_mem_nhdsWithin).exists
    have hzw' : g a ≠ w := hzw
    have hane : a ≠ u₀ := fun h => hzw' (by rw [h, hgu])
    have hbne : b ≠ u₀ := fun h => hzw' (by rw [← hbz, h, hgu])
    have : a = b := hinj ⟨haB, hane⟩ ⟨hbB, hbne⟩
      (by rw [← hgne a hane, ← hgne b hbne]; exact hbz.symm)
    exact disjoint_left.1 hdisj ha0 (this ▸ hb1)
  intro a ha b hb hab
  by_cases hau : a = u₀
  · by_cases hbu : b = u₀
    · rw [hau, hbu]
    · exfalso
      refine hsecond b hb hbu ?_
      rw [← hgne b hbu, ← hab, hau, hgu]
  · by_cases hbu : b = u₀
    · exfalso
      refine hsecond a ha hau ?_
      rw [← hgne a hau, hab, hbu, hgu]
    · exact hinj ⟨ha, hau⟩ ⟨hb, hbu⟩ (by rw [← hgne a hau, ← hgne b hbu]; exact hab)

/-- An injective holomorphic map on a punctured disc with a limit `w` at the puncture
has an analytic, non-ramified inverse near `w`, which inverts it on a punctured
neighbourhood of `w`. -/
theorem s31pp_puncture_inverse {f : ℂ → ℂ} {u₀ w : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball u₀ r \ {u₀}))
    (hinj : InjOn f (ball u₀ r \ {u₀}))
    (ht : Tendsto f (𝓝[≠] u₀) (𝓝 w)) :
    ∃ τ : ℂ → ℂ, AnalyticAt ℂ τ w ∧ τ w = u₀ ∧ deriv τ w ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] w, τ z ∈ ball u₀ r \ {u₀} ∧ f (τ z) = z := by
  classical
  obtain ⟨hDiff, hInj⟩ := s31pp_update_injOn hr hd hinj ht
  set g : ℂ → ℂ := Function.update f u₀ w with hg
  have hgu : g u₀ = w := Function.update_self _ _ _
  have hgne : ∀ u, u ≠ u₀ → g u = f u := fun u hu => Function.update_of_ne hu _ _
  have hball : ball u₀ r ∈ 𝓝 u₀ := ball_mem_nhds u₀ hr
  have hga : AnalyticAt ℂ g u₀ := hDiff.analyticAt hball
  have hder : deriv g u₀ ≠ 0 := deriv_ne_zero_of_injOn isOpen_ball hDiff hInj (mem_ball_self hr)
  have hsd := hga.hasStrictDerivAt
  let τ : ℂ → ℂ := hsd.localInverse g (deriv g u₀) u₀ hder
  have hτu : τ w = u₀ := by
    have : τ (g u₀) = u₀ := HasStrictFDerivAt.localInverse_apply_image ..
    rwa [hgu] at this
  have hτa : AnalyticAt ℂ τ w := by
    have := hga.analyticAt_localInverse hder
    rwa [hgu] at this
  refine ⟨τ, hτa, hτu, ?_, ?_⟩
  · have h : HasStrictDerivAt τ (deriv g u₀)⁻¹ (g u₀) := hsd.to_localInverse hder
    rw [hgu] at h
    rw [h.hasDerivAt.deriv]
    exact inv_ne_zero hder
  · have hinv : ∀ᶠ z in 𝓝 w, g (τ z) = z := by
      have := hsd.eventually_right_inverse hder
      rwa [hgu] at this
    have hcont : ContinuousAt τ w := hτa.continuousAt
    have hnear : ∀ᶠ z in 𝓝 w, τ z ∈ ball u₀ r := by
      apply hcont.preimage_mem_nhds
      rw [hτu]; exact hball
    filter_upwards [nhdsWithin_le_nhds hinv, nhdsWithin_le_nhds hnear,
      self_mem_nhdsWithin] with z h1 h2 h3
    have hne : τ z ≠ u₀ := by
      intro h
      apply h3
      rw [← h1, h, hgu]
      exact mem_singleton w
    exact ⟨⟨h2, hne⟩, by rw [← hgne _ hne, h1]⟩

/-- Extension of an injective holomorphic map on a punctured disc with a limit:
the extension is analytic and non-ramified at the puncture. -/
theorem s31pp_extend_nonramified {f : ℂ → ℂ} {c w : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r \ {c}))
    (hinj : InjOn f (ball c r \ {c}))
    (ht : Tendsto f (𝓝[≠] c) (𝓝 w)) :
    ∃ τ : ℂ → ℂ, AnalyticAt ℂ τ c ∧ τ c = w ∧ deriv τ c ≠ 0 ∧
      ∀ u ∈ ball c r \ {c}, τ u = f u := by
  classical
  obtain ⟨hDiff, hInj⟩ := s31pp_update_injOn hr hd hinj ht
  refine ⟨Function.update f c w, hDiff.analyticAt (ball_mem_nhds c hr),
    Function.update_self _ _ _, ?_, fun u hu => Function.update_of_ne hu.2 _ _⟩
  exact deriv_ne_zero_of_injOn isOpen_ball hDiff hInj (mem_ball_self hr)

section Geometry
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [Nonempty S]
  [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}}
  {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier}
  (hd : IsSchottkyDouble F Xd J ιd Pd)

/-- Non-ramified puncture chart: an original puncture with an actual endpoint `y`
gives an analytic non-ramified coordinate `τ` near `chart a y`, inverting the
actual embedding on a punctured neighbourhood, which lies in the positive half. -/
theorem s31pp_endpoint_chart {p₀ : F.X.carrier} (hp : p₀ ∈ F.P) {y : Xd.carrier}
    (ht : Tendsto ιd (comap F.ι (𝓝 p₀)) (𝓝 y)) (a : Xd.carrier)
    (hya : y ∈ (chartAt ℂ a).source) :
    ∃ τ : ℂ → ℂ, AnalyticAt ℂ τ (chartAt ℂ a y) ∧ τ (chartAt ℂ a y) = chartAt ℂ p₀ p₀ ∧
      deriv τ (chartAt ℂ a y) ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] (chartAt ℂ a y),
        z ∈ (chartAt ℂ a).target ∧ (chartAt ℂ a).symm z ∈ range ιd ∧
        s31qr_halfReturn F hd ((chartAt ℂ a).symm z) ∈ (chartAt ℂ p₀).source ∧
        chartAt ℂ p₀ (s31qr_halfReturn F hd ((chartAt ℂ a).symm z)) = τ z := by
  classical
  set b := chartAt ℂ p₀ with hb
  set ρ : F.X.carrier → S := fun y' => (F.embedding.toOpenPartialHomeomorph F.ι).symm y' with hρ
  have hρι : ∀ y' ∈ range F.ι, F.ι (ρ y') = y' := fun y' hy' =>
    F.embedding.toOpenPartialHomeomorph_right_inv F.ι hy'
  have hev : ∀ᶠ s in comap F.ι (𝓝 p₀), ιd s ∈ (chartAt ℂ a).source :=
    ht.eventually ((chartAt ℂ a).open_source.mem_nhds hya)
  obtain ⟨U₁, hU₁, hsub⟩ := Filter.mem_comap.1 hev
  obtain ⟨r, hr, hrt, hrU, hrr⟩ := s31eg_puncture_chart F hp U₁ hU₁
  have hmem : ∀ u ∈ ball (b p₀) r \ {b p₀}, F.ι (ρ (b.symm u)) = b.symm u :=
    fun u hu => hρι _ (hrr u hu)
  have hsrc : ∀ u ∈ ball (b p₀) r \ {b p₀}, ιd (ρ (b.symm u)) ∈ (chartAt ℂ a).source :=
    fun u hu => hsub (show F.ι (ρ (b.symm u)) ∈ U₁ by rw [hmem u hu]; exact hrU u hu.1)
  let f : ℂ → ℂ := fun u => chartAt ℂ a (ιd (ρ (b.symm u)))
  have hdiff : DifferentiableOn ℂ f (ball (b p₀) r \ {b p₀}) := by
    intro u hu
    refine DifferentiableAt.differentiableWithinAt ?_
    have hH : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun y' => ιd (ρ y')) (b.symm u) :=
      (hd.holomorphic _).comp _ (s31qr_open_embedding_inverse F.embedding F.holomorphic (hrr u hu))
    exact s31qr_coordinate_differentiable (H := fun y' => ιd (ρ y')) p₀ a (hrt hu.1)
      (hsrc u hu) hH
  have hinj : InjOn f (ball (b p₀) r \ {b p₀}) := by
    intro u₁ h₁ u₂ h₂ he
    have e1 := (chartAt ℂ a).injOn (hsrc u₁ h₁) (hsrc u₂ h₂) he
    have e2 := hd.embedding.injective e1
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
  have hlim : Tendsto f (𝓝[≠] (b p₀)) (𝓝 (chartAt ℂ a y)) :=
    ((chartAt ℂ a).continuousAt hya).tendsto.comp (ht.comp hψT)
  obtain ⟨τ, hτa, hτ0, hτd, hτev⟩ := s31pp_puncture_inverse hr hdiff hinj hlim
  refine ⟨τ, hτa, hτ0, hτd, ?_⟩
  filter_upwards [hτev] with z ⟨hzt, hfz⟩
  have hs : ιd (ρ (b.symm (τ z))) ∈ (chartAt ℂ a).source := hsrc _ hzt
  have hfz' : chartAt ℂ a (ιd (ρ (b.symm (τ z)))) = z := hfz
  have hzs : (chartAt ℂ a).symm z = ιd (ρ (b.symm (τ z))) := by
    have := (chartAt ℂ a).left_inv hs
    rwa [hfz'] at this
  have hhr : s31qr_halfReturn F hd ((chartAt ℂ a).symm z) = b.symm (τ z) := by
    rw [hzs, s31qr_halfReturn_image F hd, hmem _ hzt]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (chartAt ℂ a).map_source hs
    rwa [hfz'] at this
  · rw [hzs]
    exact ⟨_, rfl⟩
  · rw [hhr]
    exact b.map_target (hrt hzt.1)
  · rw [hhr]
    exact b.right_inv (hrt hzt.1)

/-- The positive half of a reflected coefficient family has a normalized simple pole at
every actual endpoint of an original puncture. -/
theorem s31pp_positive_pole {p₀ : F.X.carrier} (hp : p₀ ∈ F.P) {q : F.X.carrier → ℂ → ℂ}
    (hq : IsAdmissibleQD F q) {Q : Xd.carrier → ℂ → ℂ}
    (hpos : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range ιd →
      Q x z = s31qr_positiveData F hd q x z)
    {y : Xd.carrier} (ht : Tendsto ιd (comap F.ι (𝓝 p₀)) (𝓝 y)) (a : Xd.carrier)
    (hya : y ∈ (chartAt ℂ a).source) :
    ∃ (c : ℂ) (r : ℂ → ℂ), AnalyticAt ℂ r (chartAt ℂ a y) ∧
      ∀ᶠ z in 𝓝[≠] (chartAt ℂ a y), Q a z = c / (z - chartAt ℂ a y) + r z := by
  obtain ⟨τ, hτa, hτ0, hτd, hτev⟩ := s31pp_endpoint_chart F hd hp ht a hya
  obtain ⟨hz0, c, r, hra, he⟩ := hq.2.2.1 p₀ p₀ hp (mem_chart_source ℂ p₀)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hτev
  have hloc : ∀ z ∈ ball (chartAt ℂ a y) ε ∩ {chartAt ℂ a y}ᶜ,
      Q a z = q p₀ (τ z) * deriv τ z ^ 2 := by
    intro z hz
    obtain ⟨hzt, hzr, hsrc, heq⟩ := hball hz
    have hH := s31qr_halfReturn_holomorphic F hd hzr
    have hl := s31qr_transport_local (U := range ιd) (H := s31qr_halfReturn F hd) hq.1 a p₀
      hzt hzr hsrc hH
    have hev : (fun w => chartAt ℂ p₀ (s31qr_halfReturn F hd ((chartAt ℂ a).symm w)))
        =ᶠ[𝓝 z] τ := by
      filter_upwards [(isOpen_ball.inter isOpen_compl_singleton).mem_nhds hz] with w hw
      exact (hball hw).2.2.2
    rw [hpos a z hzt hzr]
    change s31qr_transportOn (range ιd) (s31qr_halfReturn F hd)
      (LinearMap.id : ℂ →ₗ[ℝ] ℂ) q a z = _
    rw [hl, hev.deriv_eq, heq]
  obtain ⟨_, c', r', hr', hev'⟩ := s31qr_simple_pole_pullback (f := q p₀) (r := r) (τ := τ)
    (p := chartAt ℂ a y) (c := c) hτa hτd (by rw [hτ0]; exact hz0) (by rw [hτ0]; exact hra)
    (by rw [hτ0]; exact he)
  refine ⟨c', r', hr', ?_⟩
  have hmem : ball (chartAt ℂ a y) ε ∩ {chartAt ℂ a y}ᶜ ∈ 𝓝[≠] (chartAt ℂ a y) :=
    by rw [inter_comm]; exact inter_mem_nhdsWithin _ (ball_mem_nhds _ hε)
  filter_upwards [hev', hmem] with z h1 h2
  rw [hloc z h2]
  exact h1

/-- The conjugated return coordinate of the mirror half is holomorphic, in any fixed target
chart centred at a point whose chart contains the actual return value. -/
theorem s31pp_mirror_coord_diff (x : Xd.carrier) (a' : F.X.carrier) {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target) (hJp : J ((chartAt ℂ x).symm z) ∈ range ιd)
    (ha : s31qr_halfReturn F hd (J ((chartAt ℂ x).symm z)) ∈ (chartAt ℂ a').source) :
    DifferentiableAt ℂ (fun w => conj (chartAt ℂ a'
      (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) z := by
  classical
  have hH := s31qr_halfReturn_holomorphic F hd hJp
  set b := s31qr_halfReturn F hd (J ((chartAt ℂ x).symm z)) with hbdef
  have hbt : chartAt ℂ b b ∈ (chartAt ℂ b).target :=
    (chartAt ℂ b).map_source (mem_chart_source ℂ b)
  have hbi : (chartAt ℂ b).symm (chartAt ℂ b b) = b :=
    (chartAt ℂ b).left_inv (mem_chart_source ℂ b)
  have hg : DifferentiableAt ℂ (fun w => conj (chartAt ℂ b
      (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) z :=
    s31qr_return_after_involution J hd.involution (s31qr_halfReturn F hd) x hz hH
  have hτD := s23_transition_differentiableAt a' b hbt (by rw [hbi]; exact ha)
  have hc : ContinuousAt (fun w => s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))) z := by
    have hψ : ContinuousAt (chartAt ℂ x).symm z := (chartAt ℂ x).continuousAt_symm hz
    have hJc : ContinuousAt J ((chartAt ℂ x).symm z) := J.continuous.continuousAt
    have h2 : ContinuousAt (fun w => J ((chartAt ℂ x).symm w)) z := hJc.comp hψ
    exact ContinuousAt.comp (f := fun w => J ((chartAt ℂ x).symm w)) hH.continuousAt h2
  have he : (fun w => conj (chartAt ℂ a' (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) =ᶠ[𝓝 z]
      (conj ∘ chartTransition a' b ∘ conj) ∘
        (fun w => conj (chartAt ℂ b (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) := by
    filter_upwards [hc.preimage_mem_nhds ((chartAt ℂ b).open_source.mem_nhds
      (mem_chart_source ℂ b))] with w hw
    change conj (chartAt ℂ a' (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w)))) =
      conj (chartAt ℂ a' ((chartAt ℂ b).symm (conj (conj (chartAt ℂ b
        (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))))))
    rw [Complex.conj_conj, (chartAt ℂ b).left_inv hw]
  have hT : DifferentiableAt ℂ (conj ∘ chartTransition a' b ∘ conj) (conj (chartAt ℂ b b)) :=
    hτD.conj_conj
  exact (hT.comp z hg).congr_of_eventuallyEq he

/-- Conjugate transport formula on the mirror half, in any fixed target chart. -/
theorem s31pp_mirror_local {q : F.X.carrier → ℂ → ℂ} (hq : IsDiffFamily 2 0 q)
    (x : Xd.carrier) (a' : F.X.carrier) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hp : (chartAt ℂ x).symm z ∈ range (J ∘ ιd))
    (ha : s31qr_halfReturn F hd (J ((chartAt ℂ x).symm z)) ∈ (chartAt ℂ a').source) :
    s31qr_mirrorData F hd q x z =
      conj (q a' (chartAt ℂ a' (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm z))))) *
        deriv (fun w => conj (chartAt ℂ a'
          (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) z ^ 2 := by
  classical
  have hJp : J ((chartAt ℂ x).symm z) ∈ range ιd := (s31qr_mirror_membership F hd _).2 hp
  have hH := s31qr_halfReturn_holomorphic F hd hJp
  set b := s31qr_halfReturn F hd (J ((chartAt ℂ x).symm z)) with hbdef
  have hbt : chartAt ℂ b b ∈ (chartAt ℂ b).target :=
    (chartAt ℂ b).map_source (mem_chart_source ℂ b)
  have hbi : (chartAt ℂ b).symm (chartAt ℂ b b) = b :=
    (chartAt ℂ b).left_inv (mem_chart_source ℂ b)
  have hl : q b (chartAt ℂ b b) =
      q a' (chartAt ℂ a' b) * deriv (chartTransition a' b) (chartAt ℂ b b) ^ 2 := by
    have hh := hq.2 a' b (chartAt ℂ b b) hbt (by rw [hbi]; exact ha)
    have he : chartTransition a' b (chartAt ℂ b b) = chartAt ℂ a' b := by
      change chartAt ℂ a' ((chartAt ℂ b).symm (chartAt ℂ b b)) = _
      rw [hbi]
    simpa only [he, zpow_zero, mul_one, zpow_two, pow_two] using hh
  have hg : DifferentiableAt ℂ (fun w => conj (chartAt ℂ b
      (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) z :=
    s31qr_return_after_involution J hd.involution (s31qr_halfReturn F hd) x hz hH
  have hτD := s23_transition_differentiableAt a' b hbt (by rw [hbi]; exact ha)
  have hc : ContinuousAt (fun w => s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))) z := by
    have hψ : ContinuousAt (chartAt ℂ x).symm z := (chartAt ℂ x).continuousAt_symm hz
    have hJc : ContinuousAt J ((chartAt ℂ x).symm z) := J.continuous.continuousAt
    have h2 : ContinuousAt (fun w => J ((chartAt ℂ x).symm w)) z := hJc.comp hψ
    exact ContinuousAt.comp (f := fun w => J ((chartAt ℂ x).symm w)) hH.continuousAt h2
  have he : (fun w => conj (chartAt ℂ a' (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) =ᶠ[𝓝 z]
      (conj ∘ chartTransition a' b ∘ conj) ∘
        (fun w => conj (chartAt ℂ b (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) := by
    filter_upwards [hc.preimage_mem_nhds ((chartAt ℂ b).open_source.mem_nhds
      (mem_chart_source ℂ b))] with w hw
    change conj (chartAt ℂ a' (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w)))) =
      conj (chartAt ℂ a' ((chartAt ℂ b).symm (conj (conj (chartAt ℂ b
        (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))))))
    rw [Complex.conj_conj, (chartAt ℂ b).left_inv hw]
  have hd1 : deriv (fun w => conj (chartAt ℂ a'
      (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) z =
      conj (deriv (chartTransition a' b) (chartAt ℂ b b)) *
        deriv (fun w => conj (chartAt ℂ b
          (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) z := by
    rw [he.deriv_eq]
    have hT : DifferentiableAt ℂ (conj ∘ chartTransition a' b ∘ conj) (conj (chartAt ℂ b b)) :=
      hτD.conj_conj
    rw [deriv_comp z hT hg, deriv_conj_conj]
    simp [Function.comp_def, hbdef]
  have hC : ∀ t : ℂ, Complex.conjCLE.toLinearMap t = conj t := fun t => rfl
  change (if z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∈ range (J ∘ ιd) then
    Complex.conjCLE.toLinearMap (q b (chartAt ℂ b b)) *
      deriv (fun w => Complex.conjCLE.toLinearMap (chartAt ℂ b
        (s31qr_halfReturn F hd (J ((chartAt ℂ x).symm w))))) z ^ 2 else 0) = _
  rw [if_pos ⟨hz, hp⟩]
  simp only [hC]
  rw [hl, hd1]
  simp only [map_mul, map_pow]
  ring

/-- The mirror half of a reflected coefficient family has a normalized simple pole at the
mirror image of every actual endpoint of an original puncture. -/
theorem s31pp_mirror_pole {p₀ : F.X.carrier} (hp : p₀ ∈ F.P) {q : F.X.carrier → ℂ → ℂ}
    (hq : IsAdmissibleQD F q) {Q : Xd.carrier → ℂ → ℂ}
    (hmir : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range (J ∘ ιd) →
      Q x z = s31qr_mirrorData F hd q x z)
    {y : Xd.carrier} (ht : Tendsto ιd (comap F.ι (𝓝 p₀)) (𝓝 y)) (a : Xd.carrier)
    (hya : J y ∈ (chartAt ℂ a).source) :
    ∃ (c : ℂ) (r : ℂ → ℂ), AnalyticAt ℂ r (chartAt ℂ a (J y)) ∧
      ∀ᶠ z in 𝓝[≠] (chartAt ℂ a (J y)), Q a z = c / (z - chartAt ℂ a (J y)) + r z := by
  classical
  have hJJ : ∀ p, J (J p) = p := hd.involution.1
  set w₂ := chartAt ℂ a (J y) with hw₂
  set b := chartAt ℂ p₀ with hb
  have hyy : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  obtain ⟨τ₁, hτ₁a, hτ₁0, hτ₁d, hτ₁ev⟩ := s31pp_endpoint_chart F hd hp ht y hyy
  obtain ⟨hz0, c, r, hra, he⟩ := hq.2.2.1 p₀ p₀ hp (mem_chart_source ℂ p₀)
  -- (1) the positive-half description near `y`, in terms of points of `Xd`
  have hchart_t : Tendsto (chartAt ℂ y) (𝓝[≠] y) (𝓝[≠] (chartAt ℂ y y)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((chartAt ℂ y).continuousAt hyy).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [nhdsWithin_le_nhds ((chartAt ℂ y).open_source.mem_nhds hyy),
        self_mem_nhdsWithin] with x hx hne h
      exact hne ((chartAt ℂ y).injOn hx hyy h)
  have hEpos : ∀ᶠ x in 𝓝[≠] y, x ∈ range ιd ∧
      s31qr_halfReturn F hd x ∈ (chartAt ℂ p₀).source ∧
      chartAt ℂ p₀ (s31qr_halfReturn F hd x) = τ₁ (chartAt ℂ y x) := by
    filter_upwards [hchart_t.eventually hτ₁ev,
      nhdsWithin_le_nhds ((chartAt ℂ y).open_source.mem_nhds hyy)] with x hx hxs
    obtain ⟨_, hr, hs, he'⟩ := hx
    rw [(chartAt ℂ y).left_inv hxs] at hr hs he'
    exact ⟨hr, hs, he'⟩
  -- (2) transport to the mirror point `J y` in the chart `a`
  have hJt : Tendsto J (𝓝[≠] (J y)) (𝓝[≠] y) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h := (J.continuous.continuousAt (x := J y)).tendsto
      rw [hJJ] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx h
      apply hx
      have := congrArg J h
      rw [hJJ] at this
      exact this
  have hsymm_t : Tendsto (chartAt ℂ a).symm (𝓝[≠] w₂) (𝓝[≠] (J y)) := by
    have hw : w₂ ∈ (chartAt ℂ a).target := (chartAt ℂ a).map_source hya
    have hs : (chartAt ℂ a).symm w₂ = J y := (chartAt ℂ a).left_inv hya
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := ((chartAt ℂ a).continuousAt_symm hw).tendsto
      rw [hs] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [nhdsWithin_le_nhds ((chartAt ℂ a).open_target.mem_nhds hw),
        self_mem_nhdsWithin] with z hzt hne h
      apply hne
      have hzz : z = w₂ := by
        rw [← (chartAt ℂ a).right_inv hzt, h]
      exact hzz
  have hE2 : ∀ᶠ z in 𝓝[≠] w₂, z ∈ (chartAt ℂ a).target ∧
      J ((chartAt ℂ a).symm z) ∈ range ιd ∧
      s31qr_halfReturn F hd (J ((chartAt ℂ a).symm z)) ∈ (chartAt ℂ p₀).source ∧
      chartAt ℂ p₀ (s31qr_halfReturn F hd (J ((chartAt ℂ a).symm z))) =
        τ₁ (chartAt ℂ y (J ((chartAt ℂ a).symm z))) := by
    filter_upwards [(hJt.comp hsymm_t).eventually hEpos,
      nhdsWithin_le_nhds ((chartAt ℂ a).open_target.mem_nhds
        ((chartAt ℂ a).map_source hya))] with z h1 h2
    exact ⟨h2, h1⟩
  -- (3) the holomorphic coordinate `Φ` of the mirror half
  let Φ : ℂ → ℂ := fun z => conj (chartAt ℂ p₀ (s31qr_halfReturn F hd (J ((chartAt ℂ a).symm z))))
  have hw2t : w₂ ∈ (chartAt ℂ a).target := (chartAt ℂ a).map_source hya
  have hsw : (chartAt ℂ a).symm w₂ = J y := (chartAt ℂ a).left_inv hya
  have hcont : ContinuousAt (fun z => conj (τ₁ (chartAt ℂ y (J ((chartAt ℂ a).symm z))))) w₂ := by
    have h1 : ContinuousAt (fun z => J ((chartAt ℂ a).symm z)) w₂ :=
      J.continuous.continuousAt.comp ((chartAt ℂ a).continuousAt_symm hw2t)
    have h2 : ContinuousAt (chartAt ℂ y) (J ((chartAt ℂ a).symm w₂)) := by
      rw [hsw, hJJ]; exact (chartAt ℂ y).continuousAt hyy
    have h3 : ContinuousAt τ₁ (chartAt ℂ y (J ((chartAt ℂ a).symm w₂))) := by
      rw [hsw, hJJ]; exact hτ₁a.continuousAt
    have h23 : ContinuousAt (fun z => chartAt ℂ y (J ((chartAt ℂ a).symm z))) w₂ :=
      ContinuousAt.comp (f := fun z => J ((chartAt ℂ a).symm z)) h2 h1
    have h4 : ContinuousAt (fun z => τ₁ (chartAt ℂ y (J ((chartAt ℂ a).symm z)))) w₂ :=
      ContinuousAt.comp (f := fun z => chartAt ℂ y (J ((chartAt ℂ a).symm z))) h3 h23
    exact ContinuousAt.comp (f := fun z => τ₁ (chartAt ℂ y (J ((chartAt ℂ a).symm z))))
      Complex.continuous_conj.continuousAt h4
  have hval : conj (τ₁ (chartAt ℂ y (J ((chartAt ℂ a).symm w₂)))) = conj (chartAt ℂ p₀ p₀) := by
    rw [hsw, hJJ, hτ₁0]
  have hΦlim : Tendsto Φ (𝓝[≠] w₂) (𝓝 (conj (chartAt ℂ p₀ p₀))) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {w₂}ᶜ))
    rw [hval] at this
    refine this.congr' ?_
    filter_upwards [hE2] with z hz
    have h := hz.2.2.2
    show conj (τ₁ (chartAt ℂ y (J ((chartAt ℂ a).symm z)))) =
      conj (chartAt ℂ p₀ (s31qr_halfReturn F hd (J ((chartAt ℂ a).symm z))))
    rw [h]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hE2
  have hΦd : DifferentiableOn ℂ Φ (ball w₂ ε \ {w₂}) := by
    intro z hz
    obtain ⟨hzt, hzr, hsrc, _⟩ := hball ⟨hz.1, hz.2⟩
    exact (s31pp_mirror_coord_diff F hd a p₀ hzt hzr hsrc).differentiableWithinAt
  have hΦinj : InjOn Φ (ball w₂ ε \ {w₂}) := by
    intro z₁ h₁ z₂ h₂ hΦ
    obtain ⟨ht₁, hr₁, hs₁, _⟩ := hball ⟨h₁.1, h₁.2⟩
    obtain ⟨ht₂, hr₂, hs₂, _⟩ := hball ⟨h₂.1, h₂.2⟩
    have e1 : chartAt ℂ p₀ (s31qr_halfReturn F hd (J ((chartAt ℂ a).symm z₁))) =
        chartAt ℂ p₀ (s31qr_halfReturn F hd (J ((chartAt ℂ a).symm z₂))) := by
      have := congrArg conj hΦ
      simpa [Φ] using this
    have e2 := (chartAt ℂ p₀).injOn hs₁ hs₂ e1
    have e3 := s31qr_halfReturn_injOn F hd hr₁ hr₂ e2
    have e4 := J.injective e3
    calc z₁ = chartAt ℂ a ((chartAt ℂ a).symm z₁) := ((chartAt ℂ a).right_inv ht₁).symm
      _ = chartAt ℂ a ((chartAt ℂ a).symm z₂) := by rw [e4]
      _ = z₂ := (chartAt ℂ a).right_inv ht₂
  obtain ⟨τ₂, hτ₂a, hτ₂0, hτ₂d, hτ₂eq⟩ := s31pp_extend_nonramified hε hΦd hΦinj hΦlim
  -- (4) the local formula for `Q`
  have hloc : ∀ z ∈ ball w₂ ε \ {w₂},
      Q a z = conj (q p₀ (conj (τ₂ z))) * deriv τ₂ z ^ 2 := by
    intro z hz
    obtain ⟨hzt, hzr, hsrc, heq⟩ := hball ⟨hz.1, hz.2⟩
    have hmirz : (chartAt ℂ a).symm z ∈ range (J ∘ ιd) :=
      (s31qr_mirror_membership F hd _).1 hzr
    rw [hmir a z hzt hmirz, s31pp_mirror_local F hd hq.1 a p₀ hzt hmirz hsrc]
    have hev : Φ =ᶠ[𝓝 z] τ₂ := by
      filter_upwards [(isOpen_ball.sdiff isClosed_singleton).mem_nhds hz] with w hw
      exact (hτ₂eq w hw).symm
    have hΦz : Φ z = τ₂ z := (hτ₂eq z hz).symm
    have hcc : chartAt ℂ p₀ (s31qr_halfReturn F hd (J ((chartAt ℂ a).symm z))) =
        conj (τ₂ z) := by rw [← hΦz]; simp [Φ]
    rw [hcc]
    have hder : deriv (fun w => conj (chartAt ℂ p₀
        (s31qr_halfReturn F hd (J ((chartAt ℂ a).symm w))))) z = deriv τ₂ z := hev.deriv_eq
    rw [hder]
  -- (5) the conjugated pole expansion
  set u₀ := chartAt ℂ p₀ p₀ with hu₀
  have hconj_t : Tendsto conj (𝓝[≠] (conj u₀)) (𝓝[≠] u₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h := (Complex.continuous_conj.continuousAt (x := conj u₀)).tendsto
      rw [Complex.conj_conj] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu h
      apply hu
      have := congrArg conj h
      rw [Complex.conj_conj] at this
      exact this
  have hbar_exp : ∀ᶠ u in 𝓝[≠] (conj u₀),
      conj (q p₀ (conj u)) = conj c / (u - conj u₀) + conj (r (conj u)) := by
    filter_upwards [hconj_t.eventually he] with u hu
    rw [hu]
    simp [map_add, map_div₀, map_sub]
  have hbar_an : AnalyticAt ℂ (fun u => conj (r (conj u))) (conj u₀) := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    have hdr : ∀ᶠ v in 𝓝 u₀, DifferentiableAt ℂ r v := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt] at hra
      exact hra
    have hct : Tendsto conj (𝓝 (conj u₀)) (𝓝 u₀) := by
      have h := (Complex.continuous_conj.continuousAt (x := conj u₀)).tendsto
      rwa [Complex.conj_conj] at h
    filter_upwards [hct.eventually hdr] with u hu
    have := hu.conj_conj
    simpa [Function.comp_def] using this
  obtain ⟨_, c', r', hr', hev'⟩ := s31qr_simple_pole_pullback
    (f := fun u => conj (q p₀ (conj u))) (r := fun u => conj (r (conj u))) (τ := τ₂)
    (p := w₂) (c := conj c) hτ₂a hτ₂d
    (by rw [hτ₂0]; simp only [Complex.conj_conj, hz0, map_zero])
    (by rw [hτ₂0]; exact hbar_an)
    (by rw [hτ₂0]; exact hbar_exp)
  refine ⟨c', r', hr', ?_⟩
  have hmem : ball w₂ ε \ {w₂} ∈ 𝓝[≠] w₂ := by
    have : ball w₂ ε \ {w₂} = {w₂}ᶜ ∩ ball w₂ ε := by
      ext z; simp [and_comm]
    rw [this]
    exact inter_mem_nhdsWithin _ (ball_mem_nhds _ hε)
  filter_upwards [hev', hmem] with z h1 h2
  rw [hloc z h2]
  exact h1

/-- Punctured neighbourhoods of any point of a charted surface are nontrivial. -/
theorem s31pp_punctured_neBot {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] (y : M) :
    (𝓝[≠] y).NeBot := by
  have hyy : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have hw : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hyy
  have h : Tendsto (chartAt ℂ y).symm (𝓝[≠] (chartAt ℂ y y)) (𝓝[≠] y) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h0 := ((chartAt ℂ y).continuousAt_symm hw).tendsto
      rw [(chartAt ℂ y).left_inv hyy] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [nhdsWithin_le_nhds ((chartAt ℂ y).open_target.mem_nhds hw),
        self_mem_nhdsWithin] with z hzt hne h'
      apply hne
      have hzz : z = chartAt ℂ y y := by
        rw [← (chartAt ℂ y).right_inv hzt, h']
      exact hzz
  have hmap : (Filter.map (chartAt ℂ y).symm (𝓝[≠] (chartAt ℂ y y))).NeBot :=
    Filter.map_neBot
  exact hmap.mono h

/-- Near an endpoint of an original puncture, the positive half fills a punctured
neighbourhood and the return map converges to the puncture. -/
theorem s31pp_endpoint_half {p₀ : F.X.carrier} (hp : p₀ ∈ F.P) {y : Xd.carrier}
    (ht : Tendsto ιd (comap F.ι (𝓝 p₀)) (𝓝 y)) :
    (∀ᶠ x in 𝓝[≠] y, x ∈ range ιd) ∧
      Tendsto (s31qr_halfReturn F hd) (𝓝[≠] y) (𝓝 p₀) := by
  have hyy : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  obtain ⟨τ, hτa, hτ0, hτd, hτev⟩ := s31pp_endpoint_chart F hd hp ht y hyy
  have hchart_t : Tendsto (chartAt ℂ y) (𝓝[≠] y) (𝓝[≠] (chartAt ℂ y y)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((chartAt ℂ y).continuousAt hyy).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [nhdsWithin_le_nhds ((chartAt ℂ y).open_source.mem_nhds hyy),
        self_mem_nhdsWithin] with x hx hne h
      exact hne ((chartAt ℂ y).injOn hx hyy h)
  have hE : ∀ᶠ x in 𝓝[≠] y, x ∈ range ιd ∧
      s31qr_halfReturn F hd x ∈ (chartAt ℂ p₀).source ∧
      chartAt ℂ p₀ (s31qr_halfReturn F hd x) = τ (chartAt ℂ y x) := by
    filter_upwards [hchart_t.eventually hτev,
      nhdsWithin_le_nhds ((chartAt ℂ y).open_source.mem_nhds hyy)] with x hx hxs
    obtain ⟨_, hr, hs, he'⟩ := hx
    rw [(chartAt ℂ y).left_inv hxs] at hr hs he'
    exact ⟨hr, hs, he'⟩
  refine ⟨hE.mono fun x hx => hx.1, ?_⟩
  have h1 : Tendsto (chartAt ℂ y) (𝓝[≠] y) (𝓝 (chartAt ℂ y y)) :=
    hchart_t.mono_right nhdsWithin_le_nhds
  have h2 : Tendsto τ (𝓝 (chartAt ℂ y y)) (𝓝 (chartAt ℂ p₀ p₀)) := by
    have := hτa.continuousAt.tendsto
    rwa [hτ0] at this
  have h3 : Tendsto (chartAt ℂ p₀).symm (𝓝 (chartAt ℂ p₀ p₀)) (𝓝 p₀) := by
    have := ((chartAt ℂ p₀).continuousAt_symm
      ((chartAt ℂ p₀).map_source (mem_chart_source ℂ p₀))).tendsto
    rwa [(chartAt ℂ p₀).left_inv (mem_chart_source ℂ p₀)] at this
  have hlim : Tendsto (fun x => (chartAt ℂ p₀).symm (τ (chartAt ℂ y x))) (𝓝[≠] y) (𝓝 p₀) :=
    h3.comp (h2.comp h1)
  refine hlim.congr' ?_
  filter_upwards [hE] with x hx
  rw [← hx.2.2, (chartAt ℂ p₀).left_inv hx.2.1]

include hd in
/-- An actual endpoint of an original puncture lies in neither open half. -/
theorem s31pp_endpoint_off_halves {p₀ : F.X.carrier} (hp : p₀ ∈ F.P) {y : Xd.carrier}
    (ht : Tendsto ιd (comap F.ι (𝓝 p₀)) (𝓝 y)) :
    y ∉ range ιd ∧ y ∉ range (J ∘ ιd) := by
  letI := s31eg_puncture_neBot F hp
  have hpout : p₀ ∉ range F.ι := by
    rw [F.range_ι]
    exact fun h => h (Or.inl hp)
  refine ⟨s31eg_cluster_missing F.ι ιd F.embedding.continuous hd.embedding hpout
    ht.mapClusterPt, ?_⟩
  intro hqm
  have hMo : IsOpen (range (J ∘ ιd)) :=
    (J.isOpenMap.comp hd.embedding.isOpenMap).isOpen_range
  obtain ⟨a, ha⟩ := (ht.eventually (hMo.mem_nhds hqm)).exists
  exact Set.disjoint_left.1 hd.disjoint (mem_range_self a) ha

end Geometry

section Terminal
open Classical
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}

/-- Endpoints of the original punctures: injective, separated from the mirrors of the
others, and exhausting `Pd` together with their mirror images. -/
theorem s31pp_endpoints_exhaust [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd) :
    ∃ e : (↑F.P : Set F.X.carrier) → Xd.carrier,
      (∀ p, e p ∈ Pd) ∧ (∀ p : (↑F.P : Set F.X.carrier),
        Tendsto ιd (comap F.ι (𝓝 p.1)) (𝓝 (e p))) ∧
      Function.Injective e ∧ (∀ p r, e p ≠ J (e r)) ∧
      Pd = Finset.univ.image e ∪ Finset.univ.image (fun p => J (e p)) := by
  haveI : Nonempty S := inferInstance
  have hex : ∀ p : (↑F.P : Set F.X.carrier), ∃ y, y ∈ Pd ∧
      Tendsto ιd (comap F.ι (𝓝 p.1)) (𝓝 y) := fun p =>
    (s31qr_original_puncture_endpoint F hd (Finset.mem_coe.1 p.2)).exists
  choose e he_mem he_tend using hex
  have hJJ : ∀ p, J (J p) = p := hd.involution.1
  have hinj : Function.Injective e := by
    intro p r hpr
    have h1 := (s31pp_endpoint_half F hd (Finset.mem_coe.1 p.2) (he_tend p)).2
    have h2 := (s31pp_endpoint_half F hd (Finset.mem_coe.1 r.2) (he_tend r)).2
    rw [← hpr] at h2
    haveI := s31pp_punctured_neBot (e p)
    exact Subtype.ext (tendsto_nhds_unique h1 h2)
  have hsep : ∀ p r, e p ≠ J (e r) := by
    intro p r h
    have h1 := (s31pp_endpoint_half F hd (Finset.mem_coe.1 p.2) (he_tend p)).1
    have h2 := (s31pp_endpoint_half F hd (Finset.mem_coe.1 r.2) (he_tend r)).1
    have hJt : Tendsto J (𝓝[≠] (J (e r))) (𝓝[≠] (e r)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h' := (J.continuous.continuousAt (x := J (e r))).tendsto
        rw [hJJ] at h'
        exact h'.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx h''
        apply hx
        have := congrArg J h''
        rw [hJJ] at this
        exact this
    have h3 : ∀ᶠ x in 𝓝[≠] (J (e r)), x ∈ range (J ∘ ιd) := by
      filter_upwards [hJt.eventually h2] with x hx
      exact (s31qr_mirror_membership F hd x).1 hx
    rw [← h] at h3
    haveI := s31pp_punctured_neBot (e p)
    obtain ⟨x, hx1, hx2⟩ := (h1.and h3).exists
    exact Set.disjoint_left.1 hd.disjoint hx1 hx2
  refine ⟨e, he_mem, he_tend, hinj, hsep, ?_⟩
  exact s31qr_Pd_exhaustion F hd ⟨e, hinj⟩ he_mem hsep

/-- (D) Normalized simple poles of the extension at every point of `Pd`. -/
theorem s31qi_puncture_poles [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    (q : admissibleQDSpace F) (Q : Xd.carrier → ℂ → ℂ)
    (hpos : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range ιd →
      Q x z = s31qr_positiveData F hd (q : F.X.carrier → ℂ → ℂ) x z)
    (hmir : ∀ x z, z ∈ (chartAt ℂ x).target → (chartAt ℂ x).symm z ∈ range (J ∘ ιd) →
      Q x z = s31qr_mirrorData F hd (q : F.X.carrier → ℂ → ℂ) x z) :
    ∀ a : Xd.carrier, ∀ p ∈ Pd, p ∈ (chartAt ℂ a).source →
      ∃ (c : ℂ) (r : ℂ → ℂ), AnalyticAt ℂ r (chartAt ℂ a p) ∧
        ∀ᶠ z in 𝓝[≠] (chartAt ℂ a p), Q a z = c / (z - chartAt ℂ a p) + r z := by
  haveI : Nonempty S := inferInstance
  have hq : IsAdmissibleQD F (q : F.X.carrier → ℂ → ℂ) := q.2
  obtain ⟨e, he_mem, he_tend, hinj, hsep, hexh⟩ := s31pp_endpoints_exhaust F hd
  intro a p hp hps
  rw [hexh] at hp
  rcases Finset.mem_union.1 hp with h | h
  · obtain ⟨p₀, _, rfl⟩ := Finset.mem_image.1 h
    exact s31pp_positive_pole F hd (Finset.mem_coe.1 p₀.2) hq hpos (he_tend p₀) a hps
  · obtain ⟨p₀, _, rfl⟩ := Finset.mem_image.1 h
    exact s31pp_mirror_pole F hd (Finset.mem_coe.1 p₀.2) hq hmir (he_tend p₀) a hps

/-- The punctures `Pd` of a Schottky double lie in neither open half. -/
theorem s31qi_Pd_off_halves [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd) :
    ∀ p ∈ Pd, p ∉ range ιd ∧ p ∉ range (J ∘ ιd) := by
  haveI : Nonempty S := inferInstance
  obtain ⟨e, he_mem, he_tend, hinj, hsep, hexh⟩ := s31pp_endpoints_exhaust F hd
  have hJJ : ∀ p, J (J p) = p := hd.involution.1
  intro p hp
  rw [hexh] at hp
  rcases Finset.mem_union.1 hp with h | h
  · obtain ⟨p₀, _, rfl⟩ := Finset.mem_image.1 h
    exact s31pp_endpoint_off_halves F hd (Finset.mem_coe.1 p₀.2) (he_tend p₀)
  · obtain ⟨p₀, _, rfl⟩ := Finset.mem_image.1 h
    obtain ⟨h1, h2⟩ := s31pp_endpoint_off_halves F hd (Finset.mem_coe.1 p₀.2) (he_tend p₀)
    refine ⟨fun hm' => h2 ?_, fun hm' => h1 ?_⟩
    · exact (s31qr_mirror_membership F hd (e p₀)).1 hm'
    · have := (s31qr_mirror_membership F hd (J (e p₀))).2 hm'
      rwa [hJJ] at this

end Terminal

end LiZhongQC
