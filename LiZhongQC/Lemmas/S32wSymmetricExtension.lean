import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Ch08.S28_Moduli
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Lemmas.SchottkyCollarFromDouble
import LiZhongQC.Lemmas.FiniteTypeComponentTrapping
import LiZhongQC.Lemmas.QDReflectionPuncturePoles
import LiZhongQC.Lemmas.S32wAnnulusEnd
import LiZhongQC.Lemmas.S32wSeamCoordinate
import LiZhongQC.Lemmas.S32wReflectRectangle
import LiZhongQC.Lemmas.LV81PunctureRemovable
import LiZhongQC.Lemmas.S32wSymmExtEnds
import LiZhongQC.Lemmas.SchottkyHalfRetraction

/-!
# §32.2 (W1.3): the symmetric extension of a quasiconformal map to the Schottky doubles

`s32w_symmetric_extension`: for surfaces `S₀`, `S` of type `(g, n, m)`, `m ≠ 0`, with Schottky doubles
`(Xd₀, J₀, ιd₀, Pd₀)`, `(Xd₁, J₁, ιd₁, Pd₁)`, a quasiconformal `f : S₀ → S` has a symmetric extension
`f^d : Xd₀ → Xd₁` (`f^d ∘ ιd₀ = ιd₁ ∘ f`, `f^d ∘ J₀ = J₁ ∘ f^d`) which is quasiconformal with `K[f^d] = K[f]`:
clauses 1–3 of `symmetric_extension_properties` (the hypothesis `hex` is needed only for clause 4).

Pieces (prefix `s32w_se_`; (a)–(c) are proved in the banked module `S32wSymmExtEnds`):
* (a) `s32w_se_double_dictionary`: the ends of `ιd(S)` in the double correspond to the ends of `ι(S)` in `F.X`
  (seam points to hole circles, punctures to punctures), with limits in both directions
  (`s31qi_collar_from_hd`, hole coordinates `s82td_hole_coordinates`);
* (b) `s32w_se_qc_end_limits`: a quasiconformal `f` has limits at the ends of `ι(S₀)` in `F₀.X`, hole circles going
  to hole circles and punctures to punctures (component trapping `s31eg_component_trapping`, `lv81_puncture_removable`
  for the puncture/hole dichotomy, `s32w_qc_annulus_end_extends` in hole coordinates);
* (c) `s32w_se_exists`: the extension by limits on `closure (range ιd₀)`, reflected by `J`, is a homeomorphism (the
  same construction for `f.symm` is its inverse);
* (d) `s32w_se_isKQCRS`: a symmetric extension of a `K`-q.c. map is `K`-q.c. (off the seam and the punctures it is
  `f` in holomorphic coordinates, or its `J`-conjugate; the seam, a real segment in `s32w_seam_coordinate`, and the
  punctures are removable, `s13x_removable`; chart changes `s26w_isKQC_local_comp`);
* (e) `s32w_se_maxDil`: `K[f^d] = K[f]` (`≤` from (d); `≥` restricting to `ιd₀(S₀)`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- The chart transition `φ_y ∘ φ_x⁻¹` is holomorphic and injective on its (open) domain. -/
theorem s32w_se_transition {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] (x y : X) :
    IsOpen ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source) ∧
      DifferentiableOn ℂ (fun w => chartAt ℂ y ((chartAt ℂ x).symm w))
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source) ∧
      InjOn (fun w => chartAt ℂ y ((chartAt ℂ x).symm w))
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source) := by
  refine ⟨(chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ y).open_source, fun w hw => ?_, ?_⟩
  · have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ x).symm w :=
      mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x) hw.1
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ y) ((chartAt ℂ x).symm w) :=
      mdifferentiableAt_atlas (chart_mem_atlas ℂ y) hw.2
    exact (mdifferentiableAt_iff_differentiableAt.1 (h2.comp w h1)).differentiableWithinAt
  · intro w hw v hv he
    exact (chartAt ℂ x).symm.injOn hw.1 hv.1 ((chartAt ℂ y).injOn hw.2 hv.2 he)

/-- **Change of the base point of a local expression**: if the local expression of a homeomorphism `φ` at
`y = φ_x⁻¹ z` is `K`-q.c. near `φ_y(y)`, then the local expression at `x` is `K`-q.c. near `z`. -/
theorem s32w_se_chart_change {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] (φ : X ≃ₜ Y) {K : ℝ} (x : X) {z : ℂ}
    (hz : z ∈ localMapDomain φ x)
    (hloc : ∃ U : Set ℂ, IsOpen U ∧ chartAt ℂ ((chartAt ℂ x).symm z) ((chartAt ℂ x).symm z) ∈ U ∧
      IsKQC (localMapExpr φ ((chartAt ℂ x).symm z)) U K) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ localMapDomain φ x ∧ IsKQC (localMapExpr φ x) U K := by
  set y := (chartAt ℂ x).symm z with hy
  obtain ⟨U, hUo, hyU, hUK⟩ := hloc
  have hzt : z ∈ (chartAt ℂ x).target := hz.1
  have hys : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  obtain ⟨hO₁, hτd, hτi⟩ := s32w_se_transition x y
  have hz₁ : z ∈ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source := ⟨hzt, hys⟩
  set τ : ℂ → ℂ := fun w => chartAt ℂ y ((chartAt ℂ x).symm w) with hτ
  have hτa : AnalyticAt ℂ τ z := hτd.analyticAt (hO₁.mem_nhds hz₁)
  have hτ' : deriv τ z ≠ 0 := deriv_ne_zero_of_injOn hO₁ hτd hτi hz₁
  have hτz : τ z = chartAt ℂ y y := rfl
  have hφy : φ y ∈ (chartAt ℂ (φ x)).source := hz.2
  obtain ⟨hO₂, hσd, hσi⟩ := s32w_se_transition (φ y) (φ x)
  have hFτ : localMapExpr φ y (τ z) = chartAt ℂ (φ y) (φ y) := by
    show chartAt ℂ (φ y) (φ ((chartAt ℂ y).symm (chartAt ℂ y y))) = chartAt ℂ (φ y) (φ y)
    rw [(chartAt ℂ y).left_inv hys]
  have hv₂ : chartAt ℂ (φ y) (φ y) ∈ (chartAt ℂ (φ y)).target ∩ (chartAt ℂ (φ y)).symm ⁻¹' (chartAt ℂ (φ x)).source :=
    ⟨(chartAt ℂ (φ y)).map_source (mem_chart_source ℂ (φ y)), by
      show (chartAt ℂ (φ y)).symm (chartAt ℂ (φ y) (φ y)) ∈ (chartAt ℂ (φ x)).source
      rw [(chartAt ℂ (φ y)).left_inv (mem_chart_source ℂ (φ y))]; exact hφy⟩
  set σ : ℂ → ℂ := fun v => chartAt ℂ (φ x) ((chartAt ℂ (φ y)).symm v) with hσ
  have hσa : AnalyticAt ℂ σ (localMapExpr φ y (τ z)) := by
    rw [hFτ]; exact hσd.analyticAt (hO₂.mem_nhds hv₂)
  have hσ' : deriv σ (localMapExpr φ y (τ z)) ≠ 0 := by
    rw [hFτ]; exact deriv_ne_zero_of_injOn hO₂ hσd hσi hv₂
  have hDo : IsOpen (localMapDomain φ x) := s23_localMapDomain_isOpen φ.continuous x
  have hev : ∀ᶠ w in 𝓝 z, localMapExpr φ x w = σ (localMapExpr φ y (τ w)) := by
    have hc1 : ContinuousAt (chartAt ℂ x).symm z := (chartAt ℂ x).continuousAt_symm hzt
    have h1 : ∀ᶠ w in 𝓝 z, (chartAt ℂ x).symm w ∈ (chartAt ℂ y).source :=
      hc1.preimage_mem_nhds ((chartAt ℂ y).open_source.mem_nhds hys)
    have h2 : ∀ᶠ w in 𝓝 z, φ ((chartAt ℂ x).symm w) ∈ (chartAt ℂ (φ y)).source :=
      (φ.continuous.continuousAt.comp hc1).preimage_mem_nhds
        ((chartAt ℂ (φ y)).open_source.mem_nhds (mem_chart_source ℂ (φ y)))
    filter_upwards [h1, h2] with w hw1 hw2
    show chartAt ℂ (φ x) (φ ((chartAt ℂ x).symm w)) = chartAt ℂ (φ x) ((chartAt ℂ (φ y)).symm
      (chartAt ℂ (φ y) (φ ((chartAt ℂ y).symm (chartAt ℂ y ((chartAt ℂ x).symm w))))))
    rw [(chartAt ℂ y).left_inv hw1, (chartAt ℂ (φ y)).left_inv hw2]
  exact s26w_isKQC_local_comp hUK (hτz ▸ hyU) hτa hτ' hσa hσ' hev (hDo.mem_nhds hz)

/-- **Local-to-global for surfaces**: a homeomorphism whose local expressions are `K`-q.c. near the centre of each
preferred chart is `K`-q.c. (`s13x_removable` with `L = ∅`; the local expression is a homeomorphism onto its image by
invariance of domain). -/
theorem s32w_se_isKQCRS_of_local {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] (φ : X ≃ₜ Y) {K : ℝ} (hK : 1 ≤ K)
    (hloc : ∀ y : X, ∃ U : Set ℂ, IsOpen U ∧ chartAt ℂ y y ∈ U ∧ IsKQC (localMapExpr φ y) U K) :
    IsKQCRS φ K := by
  refine ⟨hK, fun x => ?_⟩
  have hDo : IsOpen (localMapDomain φ x) := s23_localMapDomain_isOpen φ.continuous x
  have hc : ContinuousOn (localMapExpr φ x) (localMapDomain φ x) := by
    intro z hz
    have h1 : ContinuousAt (fun z => φ ((chartAt ℂ x).symm z)) z :=
      φ.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz.1)
    exact (ContinuousAt.comp (g := chartAt ℂ (φ x)) (f := fun z => φ ((chartAt ℂ x).symm z))
      ((chartAt ℂ (φ x)).continuousAt hz.2) h1).continuousWithinAt
  have hhom := qcl_f_isHomeomorphOnto_of_injOn hDo hc (s23_c1_injOn_localMapExpr φ.injective x)
  refine s13x_removable (L := ∅) hDo hK hhom measure_empty (by simp) (by simp) fun z hz => ?_
  exact s32w_se_chart_change φ x hz.1 (hloc _)

/-- A symmetric extension of a `K`-q.c. map is `K`-q.c. near the points of `ιd₀(S₀)` (there its local expressions are
those of `f` in holomorphic coordinates, `s32w_se_coord_isKQC`). -/
theorem s32w_se_local_range {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K) {fd : Xd₀.carrier ≃ₜ Xd₁.carrier}
    (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd) (a : S₀) :
    ∃ U : Set ℂ, IsOpen U ∧ chartAt ℂ (ιd₀ a) (ιd₀ a) ∈ U ∧ IsKQC (localMapExpr fd (ιd₀ a)) U K := by
  classical
  haveI : Nonempty S₀ := inferInstance
  set y := ιd₀ a with hy
  set α := chartAt ℂ y with hα
  set β := chartAt ℂ (fd y) with hβ
  set G : Set ℂ := α.target ∩ α.symm ⁻¹' (range ιd₀ ∩ fd ⁻¹' β.source) with hG
  have hGo : IsOpen G :=
    α.isOpen_inter_preimage_symm (hd₀.embedding.isOpen_range.inter (β.open_source.preimage fd.continuous))
  have hys : y ∈ α.source := mem_chart_source ℂ y
  have hyG : α y ∈ G :=
    ⟨α.map_source hys, by
      show α.symm (α y) ∈ range ιd₀ ∩ fd ⁻¹' β.source
      rw [α.left_inv hys]; exact ⟨mem_range_self a, mem_chart_source ℂ (fd y)⟩⟩
  set s : ℂ → S₀ := fun z => Function.invFun ιd₀ (α.symm z) with hsdef
  have hs : ∀ z ∈ G, ιd₀ (s z) = α.symm z := fun z hz => Function.invFun_eq hz.2.1
  have hfds : ∀ z ∈ G, fd (α.symm z) = ιd₁ (f (s z)) := fun z hz => by rw [← hs z hz, hfd.1]
  have hmaps : ∀ z ∈ G, ιd₁ (f (s z)) ∈ β.source := fun z hz => by rw [← hfds z hz]; exact hz.2.2
  have hαh : ∀ y' : S₀, ιd₀ y' ∈ α.source →
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) α (ιd₀ y') ∧ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) α.symm (α (ιd₀ y')) := fun y' h =>
    ⟨mdifferentiableAt_atlas (chart_mem_atlas ℂ y) h, mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ y) (α.map_source h)⟩
  have hβh : ∀ y' : S, ιd₁ y' ∈ β.source →
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) β (ιd₁ y') ∧ MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) β.symm (β (ιd₁ y')) := fun y' h =>
    ⟨mdifferentiableAt_atlas (chart_mem_atlas ℂ (fd y)) h,
      mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ (fd y)) (β.map_source h)⟩
  have hK := s32w_se_coord_isKQC hd₀.embedding hd₀.holomorphic hd₁.embedding hd₁.holomorphic hf α β hαh hβh hGo
    (fun z hz => hz.1) hs hmaps
  refine ⟨G, hGo, hyG, ad_isKQC_congr hK fun z hz => ?_⟩
  show β (fd (α.symm z)) = β (ιd₁ (f (s z)))
  rw [hfds z hz]

/-- A symmetric extension of a `K`-q.c. map is `K`-q.c. near the points of the mirror half `J₀(ιd₀(S₀))`: there its
local expression is that at the mirror point between the antiholomorphic local expressions of `J₀`, `J₁`
(`abR_x_isKQC_conj`, `s26w_isKQC_local_comp`). -/
theorem s32w_se_local_mirror {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K) {fd : Xd₀.carrier ≃ₜ Xd₁.carrier}
    (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd) (a : S₀) :
    ∃ U : Set ℂ, IsOpen U ∧ chartAt ℂ (J₀ (ιd₀ a)) (J₀ (ιd₀ a)) ∈ U ∧
      IsKQC (localMapExpr fd (J₀ (ιd₀ a))) U K := by
  set y := J₀ (ιd₀ a) with hy
  set y' := ιd₀ a with hy'
  have hJJ₀ : ∀ v, J₀ (J₀ v) = v := hd₀.involution.1
  have hJy : J₀ y = y' := hJJ₀ _
  obtain ⟨U', hU'o, hyU', hU'K⟩ := s32w_se_local_range F₀ F₁ hd₀ hd₁ hf hfd a
  have hCK := abR_x_isKQC_conj hU'K
  -- `B = φ_{y'} ∘ J₀ ∘ φ_y⁻¹` (antiholomorphic), `τ = conj ∘ B`
  set B := localMapExpr J₀ y with hB
  have hBo : IsOpen (localMapDomain J₀ y) := s23_localMapDomain_isOpen J₀.continuous y
  have hys : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have hc0 : chartAt ℂ y y ∈ localMapDomain J₀ y :=
    ⟨(chartAt ℂ y).map_source hys, by
      show J₀ ((chartAt ℂ y).symm (chartAt ℂ y y)) ∈ (chartAt ℂ (J₀ y)).source
      rw [(chartAt ℂ y).left_inv hys]; exact mem_chart_source ℂ _⟩
  have hτd : DifferentiableOn ℂ (fun z => conj (B z)) (localMapDomain J₀ y) := hd₀.involution.2 y
  have hτi : InjOn (fun z => conj (B z)) (localMapDomain J₀ y) := by
    intro z hz w hw he
    have he' := congrArg conj he
    simp only [Complex.conj_conj] at he'
    exact s23_c1_injOn_localMapExpr J₀.injective y hz hw he'
  have hτa : AnalyticAt ℂ (fun z => conj (B z)) (chartAt ℂ y y) := hτd.analyticAt (hBo.mem_nhds hc0)
  have hτ' : deriv (fun z => conj (B z)) (chartAt ℂ y y) ≠ 0 := deriv_ne_zero_of_injOn hBo hτd hτi hc0
  have hB0 : B (chartAt ℂ y y) = chartAt ℂ y' y' := by
    show chartAt ℂ (J₀ y) (J₀ ((chartAt ℂ y).symm (chartAt ℂ y y))) = chartAt ℂ y' y'
    rw [(chartAt ℂ y).left_inv hys, hJy]
  have hτV : (fun z => conj (B z)) (chartAt ℂ y y) ∈ conj ⁻¹' U' := by
    show conj (conj (B (chartAt ℂ y y))) ∈ U'
    rw [Complex.conj_conj, hB0]; exact hyU'
  -- `A = φ_{fd y} ∘ J₁ ∘ φ_q⁻¹`, `q = fd y'`, and `σ = A ∘ conj`
  set q := fd y' with hq
  have hJq : J₁ q = fd y := by rw [hq, ← hfd.2]
  set A := localMapExpr J₁ q with hA
  have hAo : IsOpen (localMapDomain J₁ q) := s23_localMapDomain_isOpen J₁.continuous q
  have hqs : q ∈ (chartAt ℂ q).source := mem_chart_source ℂ q
  set v₀ := conj (chartAt ℂ q q) with hv₀
  have hv₀m : conj v₀ ∈ localMapDomain J₁ q := by
    rw [hv₀, Complex.conj_conj]
    refine ⟨(chartAt ℂ q).map_source hqs, ?_⟩
    show J₁ ((chartAt ℂ q).symm (chartAt ℂ q q)) ∈ (chartAt ℂ (J₁ q)).source
    rw [(chartAt ℂ q).left_inv hqs]; exact mem_chart_source ℂ _
  have hAd : DifferentiableOn ℂ (fun z => conj (A z)) (localMapDomain J₁ q) := hd₁.involution.2 q
  set N₂ := conj ⁻¹' localMapDomain J₁ q with hN₂
  have hN₂o : IsOpen N₂ := hAo.preimage Complex.continuous_conj
  have hσd : DifferentiableOn ℂ (fun v => A (conj v)) N₂ := by
    intro v hv
    have h1 : DifferentiableAt ℂ (fun z => conj (A z)) (conj v) :=
      (hAd _ hv).differentiableAt (hAo.mem_nhds hv)
    have h2 : DifferentiableAt ℂ (conj ∘ (fun z => conj (A z)) ∘ conj) v := by
      have := differentiableAt_conj_conj_iff.2 (by simpa using h1)
      simpa using this
    refine (h2.congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)).differentiableWithinAt
    simp
  have hσi : InjOn (fun v => A (conj v)) N₂ := by
    intro v hv w hw he
    have := s23_c1_injOn_localMapExpr J₁.injective q hv hw he
    simpa using congrArg conj this
  have hFτ : (fun w => conj (localMapExpr fd y' (conj w))) ((fun z => conj (B z)) (chartAt ℂ y y)) = v₀ := by
    show conj (localMapExpr fd y' (conj (conj (B (chartAt ℂ y y))))) = v₀
    rw [Complex.conj_conj, hB0]
    show conj (chartAt ℂ (fd y') (fd ((chartAt ℂ y').symm (chartAt ℂ y' y')))) = v₀
    rw [(chartAt ℂ y').left_inv (mem_chart_source ℂ y')]
  have hσa : AnalyticAt ℂ (fun v => A (conj v))
      ((fun w => conj (localMapExpr fd y' (conj w))) ((fun z => conj (B z)) (chartAt ℂ y y))) := by
    rw [hFτ]; exact hσd.analyticAt (hN₂o.mem_nhds hv₀m)
  have hσ' : deriv (fun v => A (conj v))
      ((fun w => conj (localMapExpr fd y' (conj w))) ((fun z => conj (B z)) (chartAt ℂ y y))) ≠ 0 := by
    rw [hFτ]; exact deriv_ne_zero_of_injOn hN₂o hσd hσi hv₀m
  have hev : ∀ᶠ w in 𝓝 (chartAt ℂ y y), localMapExpr fd y w =
      (fun v => A (conj v)) ((fun w => conj (localMapExpr fd y' (conj w))) ((fun z => conj (B z)) w)) := by
    have hc1 : ContinuousAt (chartAt ℂ y).symm (chartAt ℂ y y) :=
      (chartAt ℂ y).continuousAt_symm ((chartAt ℂ y).map_source hys)
    have hc1' : (chartAt ℂ y).symm (chartAt ℂ y y) = y := (chartAt ℂ y).left_inv hys
    have h1 : ∀ᶠ w in 𝓝 (chartAt ℂ y y), J₀ ((chartAt ℂ y).symm w) ∈ (chartAt ℂ y').source := by
      refine (J₀.continuous.continuousAt.comp hc1).preimage_mem_nhds ?_
      show (chartAt ℂ y').source ∈ 𝓝 (J₀ ((chartAt ℂ y).symm (chartAt ℂ y y)))
      rw [hc1', hJy]; exact (chartAt ℂ y').open_source.mem_nhds (mem_chart_source ℂ y')
    have h2 : ∀ᶠ w in 𝓝 (chartAt ℂ y y), fd (J₀ ((chartAt ℂ y).symm w)) ∈ (chartAt ℂ q).source := by
      refine (fd.continuous.continuousAt.comp (J₀.continuous.continuousAt.comp hc1)).preimage_mem_nhds ?_
      show (chartAt ℂ q).source ∈ 𝓝 (fd (J₀ ((chartAt ℂ y).symm (chartAt ℂ y y))))
      rw [hc1', hJy]; exact (chartAt ℂ q).open_source.mem_nhds hqs
    filter_upwards [h1, h2] with w hw1 hw2
    show chartAt ℂ (fd y) (fd ((chartAt ℂ y).symm w)) = chartAt ℂ (J₁ q) (J₁ ((chartAt ℂ q).symm
      (conj (conj (chartAt ℂ (fd y') (fd ((chartAt ℂ y').symm
        (conj (conj (chartAt ℂ (J₀ y) (J₀ ((chartAt ℂ y).symm w))))))))))))
    simp only [Complex.conj_conj]
    rw [hJy, (chartAt ℂ y').left_inv hw1, ← hq, (chartAt ℂ q).left_inv hw2, hJq, ← hfd.2, hJJ₀]
  obtain ⟨U, hUo, hzU, -, hUK⟩ := s26w_isKQC_local_comp (τ := fun z => conj (B z)) (σ := fun v => A (conj v))
    (F := fun w => conj (localMapExpr fd y' (conj w))) hCK hτV hτa hτ' hσa hσ' hev univ_mem
  exact ⟨U, hUo, hzU, hUK⟩

/-- Off the seam and the punctures (in either open half) a symmetric extension of a `K`-q.c. map is locally
`K`-q.c. -/
theorem s32w_se_local_regular {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K) {fd : Xd₀.carrier ≃ₜ Xd₁.carrier}
    (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd) {y : Xd₀.carrier}
    (hy : y ∈ range ιd₀ ∨ y ∈ range (J₀ ∘ ιd₀)) :
    ∃ U : Set ℂ, IsOpen U ∧ chartAt ℂ y y ∈ U ∧ IsKQC (localMapExpr fd y) U K := by
  rcases hy with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact s32w_se_local_range F₀ F₁ hd₀ hd₁ hf hfd a
  · exact s32w_se_local_mirror F₀ F₁ hd₀ hd₁ hf hfd a

/-- The local expression of a homeomorphism is continuous on its domain. -/
theorem s32w_se_localExpr_continuousOn {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] (φ : X ≃ₜ Y) (x : X) : ContinuousOn (localMapExpr φ x) (localMapDomain φ x) := by
  intro z hz
  have h1 : ContinuousAt (fun z => φ ((chartAt ℂ x).symm z)) z :=
    φ.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz.1)
  exact (ContinuousAt.comp (g := chartAt ℂ (φ x)) (f := fun z => φ ((chartAt ℂ x).symm z))
    ((chartAt ℂ (φ x)).continuousAt hz.2) h1).continuousWithinAt

/-- At a puncture of the double, a symmetric extension of a `K`-q.c. map is locally `K`-q.c.: it is so on a punctured
chart disc (`s32w_se_local_regular`), and the centre is removable (`s13x_removable`). -/
theorem s32w_se_local_puncture {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K) {fd : Xd₀.carrier ≃ₜ Xd₁.carrier}
    (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd) {p : Xd₀.carrier} (hp : p ∈ (↑Pd₀ : Set Xd₀.carrier)) :
    ∃ U : Set ℂ, IsOpen U ∧ chartAt ℂ p p ∈ U ∧ IsKQC (localMapExpr fd p) U K := by
  classical
  set φ := chartAt ℂ p with hφ
  have hps : p ∈ φ.source := mem_chart_source ℂ p
  set c₀ := φ p with hc₀
  have hDo : IsOpen (localMapDomain fd p) := s23_localMapDomain_isOpen fd.continuous p
  have hc₀D : c₀ ∈ localMapDomain fd p :=
    ⟨φ.map_source hps, by
      show fd (φ.symm (φ p)) ∈ (chartAt ℂ (fd p)).source
      rw [φ.left_inv hps]; exact mem_chart_source ℂ _⟩
  set Bad : Set Xd₀.carrier := {x | J₀ x = x} ∪ ((↑Pd₀ : Set Xd₀.carrier) \ {p}) with hBad
  have hBadc : IsClosed Bad :=
    (isClosed_eq J₀.continuous continuous_id).union (Pd₀.finite_toSet.subset sdiff_subset).isClosed
  have hpBad : p ∉ Bad := by
    rintro (h | ⟨-, h⟩)
    · have : p ∈ {x | J₀ x = x} := h
      rw [hd₀.fixed_curves] at this
      exact this.2 hp
    · exact h rfl
  set N : Set ℂ := localMapDomain fd p ∩ (φ.target ∩ φ.symm ⁻¹' Badᶜ) with hN
  have hNo : IsOpen N := hDo.inter (φ.isOpen_inter_preimage_symm hBadc.isOpen_compl)
  have hc₀N : c₀ ∈ N := ⟨hc₀D, φ.map_source hps, by show φ.symm (φ p) ∈ Badᶜ; rw [φ.left_inv hps]; exact hpBad⟩
  obtain ⟨ρ, hρ, hρN⟩ := Metric.isOpen_iff.1 hNo c₀ hc₀N
  have hK1 : 1 ≤ K := hf.1
  have hhom : IsHomeomorphOnto (localMapExpr fd p) (ball c₀ ρ) (localMapExpr fd p '' ball c₀ ρ) :=
    qcl_f_isHomeomorphOnto_of_injOn isOpen_ball
      ((s32w_se_localExpr_continuousOn fd p).mono fun z hz => (hρN hz).1)
      ((s23_c1_injOn_localMapExpr fd.injective p).mono fun z hz => (hρN hz).1)
  have hsub : ∀ x : ℝ, ({y : ℝ | (x : ℂ) + (y : ℂ) * I ∈ ({c₀} : Set ℂ)}).Countable := by
    intro x
    refine Set.Subsingleton.countable fun y₁ h₁ y₂ h₂ => ?_
    have e1 : (x : ℂ) + (y₁ : ℂ) * I = c₀ := h₁
    have e2 : (x : ℂ) + (y₂ : ℂ) * I = c₀ := h₂
    have := congrArg Complex.im (e1.trans e2.symm)
    simpa using this
  have hsub' : ∀ y : ℝ, ({x : ℝ | (x : ℂ) + (y : ℂ) * I ∈ ({c₀} : Set ℂ)}).Countable := by
    intro y
    refine Set.Subsingleton.countable fun x₁ h₁ x₂ h₂ => ?_
    have e1 : (x₁ : ℂ) + (y : ℂ) * I = c₀ := h₁
    have e2 : (x₂ : ℂ) + (y : ℂ) * I = c₀ := h₂
    have := congrArg Complex.re (e1.trans e2.symm)
    simpa using this
  refine ⟨ball c₀ ρ, isOpen_ball, mem_ball_self hρ, ?_⟩
  refine s13x_removable (L := {c₀}) isOpen_ball hK1 hhom (measure_singleton c₀)
    (Eventually.of_forall hsub) (Eventually.of_forall hsub') fun z hz => ?_
  obtain ⟨hzB, hzc⟩ := hz
  have hzN := hρN hzB
  set y' := φ.symm z with hy'
  have hy'p : y' ≠ p := by
    intro h
    apply hzc
    have := φ.right_inv hzN.2.1
    rw [← hy', h] at this
    exact mem_singleton_iff.2 this.symm
  have hy'B : y' ∉ Bad := hzN.2.2
  have hreg : y' ∈ range ιd₀ ∨ y' ∈ range (J₀ ∘ ιd₀) := by
    have hcov : y' ∈ range ιd₀ ∪ range (J₀ ∘ ιd₀) ∪ {x | J₀ x = x} ∪ ↑Pd₀ := hd₀.cover ▸ mem_univ y'
    rcases hcov with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hy'B (Or.inl h)).elim
    · exact (hy'B (Or.inr ⟨h, hy'p⟩)).elim
  obtain ⟨U, hUo, hzU, -, hUK⟩ := s32w_se_chart_change fd p hzN.1
    (s32w_se_local_regular F₀ F₁ hd₀ hd₁ hf hfd hreg)
  exact ⟨U ∩ ball c₀ ρ, hUo.inter isOpen_ball, ⟨hzU, hzB⟩, inter_subset_right,
    ac_t_isKQC_restrict hUK (hUo.inter isOpen_ball) inter_subset_left⟩

/-- At a seam point of the double, a symmetric extension of a `K`-q.c. map is locally `K`-q.c.: in the seam
coordinate `κ` (`s32w_seam_coordinate`) the map is `K`-q.c. off the real segment (`s32w_se_local_regular`), and the
segment is removable (`s13x_removable`); then pass back to the chart by the holomorphic local inverse of `φ_p ∘ κ`. -/
theorem s32w_se_local_seam {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K) {fd : Xd₀.carrier ≃ₜ Xd₁.carrier}
    (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd) {p : Xd₀.carrier} (hp : J₀ p = p) :
    ∃ U : Set ℂ, IsOpen U ∧ chartAt ℂ p p ∈ U ∧ IsKQC (localMapExpr fd p) U K := by
  classical
  obtain ⟨κ, r, hr, hκs, hκ0, -, hκup, hκlo, -, hκd, -⟩ := s32w_seam_coordinate F₀ hd₀ hp
  set φ := chartAt ℂ p with hφ
  set ψ := chartAt ℂ (fd p) with hψ
  have hps : p ∈ φ.source := mem_chart_source ℂ p
  have h0s : (0 : ℂ) ∈ κ.source := hκs (mem_ball_self hr)
  set O : Set Xd₀.carrier := φ.source ∩ fd ⁻¹' ψ.source with hO
  have hOo : IsOpen O := φ.open_source.inter (ψ.open_source.preimage fd.continuous)
  have hpO : p ∈ O := ⟨hps, mem_chart_source ℂ (fd p)⟩
  obtain ⟨r₂, hr₂, hr₂O⟩ := Metric.mem_nhds_iff.1
    ((κ.continuousAt h0s).preimage_mem_nhds (by rw [hκ0]; exact hOo.mem_nhds hpO))
  set r₁ : ℝ := min r r₂ with hr₁
  have hr₁0 : 0 < r₁ := lt_min hr hr₂
  set B₀ : Set ℂ := ball (0 : ℂ) r₁ with hB₀
  have hB₀r : B₀ ⊆ ball 0 r := ball_subset_ball (min_le_left _ _)
  have hB₀s : ∀ w ∈ B₀, w ∈ κ.source := fun w hw => hκs (hB₀r hw)
  have hB₀O : ∀ w ∈ B₀, κ w ∈ O := fun w hw => hr₂O (ball_subset_ball (min_le_right _ _) hw)
  have hK1 : 1 ≤ K := hf.1
  -- the map in the seam coordinate
  set M : ℂ → ℂ := fun w => ψ (fd (κ w)) with hM
  have hMc : ContinuousOn M B₀ := by
    intro w hw
    have h1 : ContinuousAt (fun w => fd (κ w)) w :=
      ContinuousAt.comp (f := κ) fd.continuous.continuousAt (κ.continuousAt (hB₀s w hw))
    exact (ContinuousAt.comp (f := fun w => fd (κ w)) (ψ.continuousAt (hB₀O w hw).2) h1).continuousWithinAt
  have hMi : InjOn M B₀ := by
    intro w hw v hv he
    exact κ.injOn (hB₀s w hw) (hB₀s v hv) (fd.injective (ψ.injOn (hB₀O w hw).2 (hB₀O v hv).2 he))
  have hMhom := qcl_f_isHomeomorphOnto_of_injOn isOpen_ball hMc hMi
  have hτ0d : DifferentiableOn ℂ (fun w => φ (κ w)) B₀ := hκd.mono hB₀r
  have hMK : IsKQC M B₀ K := by
    refine s13x_removable (L := {z : ℂ | z.im = 0}) isOpen_ball hK1 hMhom gzE_volume_im_eq_zero ?_ ?_ ?_
    · refine Eventually.of_forall fun x => (countable_singleton (0 : ℝ)).mono fun y hy => ?_
      simpa using hy
    · have h0 : ∀ᵐ y : ℝ, y ∉ ({0} : Set ℝ) := measure_eq_zero_iff_ae_notMem.1 (measure_singleton 0)
      filter_upwards [h0] with y hy
      refine countable_empty.mono fun x hx => ?_
      exact absurd (by simpa using hx) hy
    · rintro w ⟨hwB, hwim⟩
      have hwim' : w.im ≠ 0 := hwim
      set y' := κ w with hy'
      have hreg : y' ∈ range ιd₀ ∨ y' ∈ range (J₀ ∘ ιd₀) := by
        rcases lt_or_gt_of_ne hwim' with h | h
        · exact Or.inr (hκlo w (hB₀r hwB) h)
        · exact Or.inl (hκup w (hB₀r hwB) h)
      obtain ⟨U', hU'o, hyU', hU'K⟩ := s32w_se_local_regular F₀ F₁ hd₀ hd₁ hf hfd hreg
      set ch := chartAt ℂ y' with hch
      set Ow : Set ℂ := B₀ ∩ κ ⁻¹' ch.source with hOw
      have hOwo : IsOpen Ow :=
        (κ.continuousOn.mono fun v hv => hB₀s v hv).isOpen_inter_preimage isOpen_ball ch.open_source
      have hwOw : w ∈ Ow := ⟨hwB, mem_chart_source ℂ y'⟩
      obtain ⟨hTo, hTd, -⟩ := s32w_se_transition p y'
      have hτd : DifferentiableOn ℂ (fun v => ch (κ v)) Ow := by
        intro v hv
        have hvB := hv.1
        have hu : φ (κ v) ∈ φ.target ∩ φ.symm ⁻¹' ch.source :=
          ⟨φ.map_source (hB₀O v hvB).1, by
            show φ.symm (φ (κ v)) ∈ ch.source; rw [φ.left_inv (hB₀O v hvB).1]; exact hv.2⟩
        have h1 : DifferentiableAt ℂ (fun u => ch (φ.symm u)) (φ (κ v)) := (hTd _ hu).differentiableAt (hTo.mem_nhds hu)
        have h2 : DifferentiableAt ℂ (fun w => φ (κ w)) v := (hτ0d v hvB).differentiableAt (isOpen_ball.mem_nhds hvB)
        refine ((h1.comp v h2).congr_of_eventuallyEq ?_).differentiableWithinAt
        filter_upwards [isOpen_ball.mem_nhds hvB] with v' hv'
        show ch (κ v') = ch (φ.symm (φ (κ v')))
        rw [φ.left_inv (hB₀O v' hv').1]
      have hτi : InjOn (fun v => ch (κ v)) Ow := by
        intro v hv v' hv' he
        exact κ.injOn (hB₀s v hv.1) (hB₀s v' hv'.1) (ch.injOn hv.2 hv'.2 he)
      have hτa : AnalyticAt ℂ (fun v => ch (κ v)) w := hτd.analyticAt (hOwo.mem_nhds hwOw)
      have hτ' : deriv (fun v => ch (κ v)) w ≠ 0 := deriv_ne_zero_of_injOn hOwo hτd hτi hwOw
      have hτV : (fun v => ch (κ v)) w ∈ U' := hyU'
      obtain ⟨hSo, hSd, hSi⟩ := s32w_se_transition (fd y') (fd p)
      have hFτ : localMapExpr fd y' ((fun v => ch (κ v)) w) = chartAt ℂ (fd y') (fd y') := by
        show chartAt ℂ (fd y') (fd (ch.symm (ch (κ w)))) = chartAt ℂ (fd y') (fd y')
        rw [ch.left_inv (mem_chart_source ℂ y')]
      have hv₂ : chartAt ℂ (fd y') (fd y') ∈
          (chartAt ℂ (fd y')).target ∩ (chartAt ℂ (fd y')).symm ⁻¹' (chartAt ℂ (fd p)).source :=
        ⟨(chartAt ℂ (fd y')).map_source (mem_chart_source ℂ _), by
          show (chartAt ℂ (fd y')).symm (chartAt ℂ (fd y') (fd y')) ∈ (chartAt ℂ (fd p)).source
          rw [(chartAt ℂ (fd y')).left_inv (mem_chart_source ℂ _)]; exact (hB₀O w hwB).2⟩
      have hσa : AnalyticAt ℂ (fun u => chartAt ℂ (fd p) ((chartAt ℂ (fd y')).symm u))
          (localMapExpr fd y' ((fun v => ch (κ v)) w)) := by
        rw [hFτ]; exact hSd.analyticAt (hSo.mem_nhds hv₂)
      have hσ' : deriv (fun u => chartAt ℂ (fd p) ((chartAt ℂ (fd y')).symm u))
          (localMapExpr fd y' ((fun v => ch (κ v)) w)) ≠ 0 := by
        rw [hFτ]; exact deriv_ne_zero_of_injOn hSo hSd hSi hv₂
      have hev : ∀ᶠ v in 𝓝 w, M v = (fun u => chartAt ℂ (fd p) ((chartAt ℂ (fd y')).symm u))
          (localMapExpr fd y' ((fun v => ch (κ v)) v)) := by
        have hκw : ContinuousAt κ w := κ.continuousAt (hB₀s w hwB)
        have h1 : ∀ᶠ v in 𝓝 w, κ v ∈ ch.source := hκw.preimage_mem_nhds (ch.open_source.mem_nhds (mem_chart_source ℂ y'))
        have h2 : ∀ᶠ v in 𝓝 w, fd (κ v) ∈ (chartAt ℂ (fd y')).source :=
          (fd.continuous.continuousAt.comp hκw).preimage_mem_nhds
            ((chartAt ℂ (fd y')).open_source.mem_nhds (mem_chart_source ℂ _))
        filter_upwards [h1, h2] with v hv1 hv2
        show ψ (fd (κ v)) = chartAt ℂ (fd p) ((chartAt ℂ (fd y')).symm
          (chartAt ℂ (fd y') (fd (ch.symm (ch (κ v))))))
        rw [ch.left_inv hv1, (chartAt ℂ (fd y')).left_inv hv2]
      exact s26w_isKQC_local_comp hU'K hτV hτa hτ' hσa hσ' hev (isOpen_ball.mem_nhds hwB)
  -- back to the chart at `p`
  set τi : ℂ → ℂ := fun v => κ.symm (φ.symm v) with hτi
  set N' : Set ℂ := φ.target ∩ φ.symm ⁻¹' (κ.target ∩ κ.symm ⁻¹' B₀) with hN'
  have hN'o : IsOpen N' := φ.isOpen_inter_preimage_symm (κ.isOpen_inter_preimage_symm isOpen_ball)
  have hpt : p ∈ κ.target := by rw [← hκ0]; exact κ.map_source h0s
  have hκp : κ.symm p = 0 := by rw [← hκ0]; exact κ.left_inv h0s
  have hc₀N' : φ p ∈ N' := ⟨φ.map_source hps, by
    show φ.symm (φ p) ∈ κ.target ∩ κ.symm ⁻¹' B₀
    rw [φ.left_inv hps]; exact ⟨hpt, by show κ.symm p ∈ B₀; rw [hκp]; exact mem_ball_self hr₁0⟩⟩
  have hτiB : ∀ v ∈ N', τi v ∈ B₀ := fun v hv => hv.2.2
  have hτ0τi : ∀ v ∈ N', φ (κ (τi v)) = v := fun v hv => by
    show φ (κ (κ.symm (φ.symm v))) = v
    rw [κ.right_inv hv.2.1, φ.right_inv hv.1]
  have hτ0i : InjOn (fun w => φ (κ w)) B₀ := by
    intro w hw v hv he
    exact κ.injOn (hB₀s w hw) (hB₀s v hv) (φ.injOn (hB₀O w hw).1 (hB₀O v hv).1 he)
  have hτid : DifferentiableOn ℂ τi N' := by
    intro v hv
    have hev : ∀ᶠ v' in 𝓝 (φ (κ (τi v))), τi v' ∈ B₀ ∧ φ (κ (τi v')) = v' := by
      rw [hτ0τi v hv]
      filter_upwards [hN'o.mem_nhds hv] with v' hv'
      exact ⟨hτiB v' hv', hτ0τi v' hv'⟩
    have := s82td_inverse_differentiableAt isOpen_ball hτ0d hτ0i (hτiB v hv) hev
    rw [hτ0τi v hv] at this
    exact this.differentiableWithinAt
  have hτii : InjOn τi N' := by
    intro v hv v' hv' he
    rw [← hτ0τi v hv, ← hτ0τi v' hv', he]
  have hτia : AnalyticAt ℂ τi (φ p) := hτid.analyticAt (hN'o.mem_nhds hc₀N')
  have hτi' : deriv τi (φ p) ≠ 0 := deriv_ne_zero_of_injOn hN'o hτid hτii hc₀N'
  have hev : ∀ᶠ v in 𝓝 (φ p), localMapExpr fd p v = (fun u => u) (M (τi v)) := by
    filter_upwards [hN'o.mem_nhds hc₀N'] with v hv
    show ψ (fd (φ.symm v)) = ψ (fd (κ (κ.symm (φ.symm v))))
    rw [κ.right_inv hv.2.1]
  obtain ⟨U, hUo, hzU, -, hUK⟩ := s26w_isKQC_local_comp hMK (hτiB _ hc₀N') hτia hτi' analyticAt_id
    (by rw [deriv_id]; exact one_ne_zero) hev univ_mem
  exact ⟨U, hUo, hzU, hUK⟩

/-- **[stub d] A symmetric extension of a `K`-q.c. map is `K`-q.c.**  At points of `ιd₀(S₀)` the local expressions
of `f^d` are those of `f` up to holomorphic chart changes, on the mirror half their conjugates by `J`; the seam (a
real segment in seam coordinates) and the punctures are removable for `K`-q.c. homeomorphisms. -/
theorem s32w_se_isKQCRS {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {f : S₀ ≃ₜ S} {K : ℝ} (hf : IsKQCRS f K) {fd : Xd₀.carrier ≃ₜ Xd₁.carrier}
    (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd) : IsKQCRS fd K := by
  refine s32w_se_isKQCRS_of_local fd hf.1 fun y => ?_
  have hcov : y ∈ range ιd₀ ∪ range (J₀ ∘ ιd₀) ∪ {x | J₀ x = x} ∪ ↑Pd₀ := hd₀.cover ▸ mem_univ y
  rcases hcov with ((h | h) | h) | h
  · exact s32w_se_local_regular F₀ F₁ hd₀ hd₁ hf hfd (Or.inl h)
  · exact s32w_se_local_regular F₀ F₁ hd₀ hd₁ hf hfd (Or.inr h)
  · exact s32w_se_local_seam F₀ F₁ hd₀ hd₁ hf hfd h
  · exact s32w_se_local_puncture F₀ F₁ hd₀ hd₁ hf hfd h

/-- **Restriction back to the surface**: if a symmetric extension `f^d` of `f` is `K`-q.c., so is `f` (its local
expressions are those of `f^d` at `ιd₀(x)` between the holomorphic coordinate changes along `ιd₀`, `ιd₁⁻¹`). -/
theorem s32w_se_restrict_isKQCRS {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {f : S₀ ≃ₜ S} {fd : Xd₀.carrier ≃ₜ Xd₁.carrier} (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd) {K : ℝ}
    (hK : IsKQCRS fd K) : IsKQCRS f K := by
  haveI : Nonempty S := inferInstance
  refine s32w_se_isKQCRS_of_local f hK.1 fun x => ?_
  set e₁ := hd₁.embedding.toOpenPartialHomeomorph ιd₁ with he₁
  have hl₁ : ∀ b : S, e₁.symm (ιd₁ b) = b := fun b => hd₁.embedding.toOpenPartialHomeomorph_left_inv ιd₁
  set y := ιd₀ x with hy
  set cx := chartAt ℂ x with hcx
  set cy := chartAt ℂ y with hcy
  have hxs : x ∈ cx.source := mem_chart_source ℂ x
  have hys : y ∈ cy.source := mem_chart_source ℂ y
  -- `τ = φ_y ∘ ιd₀ ∘ φ_x⁻¹`
  set O₁ : Set ℂ := cx.target ∩ cx.symm ⁻¹' (ιd₀ ⁻¹' cy.source) with hO₁
  have hO₁o : IsOpen O₁ := cx.isOpen_inter_preimage_symm (cy.open_source.preimage hd₀.embedding.continuous)
  have hx₁ : cx x ∈ O₁ :=
    ⟨cx.map_source hxs, by show ιd₀ (cx.symm (cx x)) ∈ cy.source; rw [cx.left_inv hxs]; exact hys⟩
  have hτd : DifferentiableOn ℂ (fun w => cy (ιd₀ (cx.symm w))) O₁ := by
    intro w hw
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cx.symm w := mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ x) hw.1
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cy (ιd₀ (cx.symm w)) :=
      mdifferentiableAt_atlas (chart_mem_atlas ℂ y) hw.2
    exact (mdifferentiableAt_iff_differentiableAt.1
      (h2.comp w ((hd₀.holomorphic _).comp w h1))).differentiableWithinAt
  have hτi : InjOn (fun w => cy (ιd₀ (cx.symm w))) O₁ := by
    intro w hw v hv he
    exact cx.symm.injOn hw.1 hv.1 (hd₀.embedding.injective (cy.injOn hw.2 hv.2 he))
  have hτa : AnalyticAt ℂ (fun w => cy (ιd₀ (cx.symm w))) (cx x) := hτd.analyticAt (hO₁o.mem_nhds hx₁)
  have hτ' : deriv (fun w => cy (ιd₀ (cx.symm w))) (cx x) ≠ 0 := deriv_ne_zero_of_injOn hO₁o hτd hτi hx₁
  have hτz : (fun w => cy (ιd₀ (cx.symm w))) (cx x) = cy y := by
    show cy (ιd₀ (cx.symm (cx x))) = cy y; rw [cx.left_inv hxs]
  have hτV : (fun w => cy (ιd₀ (cx.symm w))) (cx x) ∈ localMapDomain fd y := by
    rw [hτz]
    refine ⟨cy.map_source hys, ?_⟩
    show fd (cy.symm (cy y)) ∈ (chartAt ℂ (fd y)).source
    rw [cy.left_inv hys]; exact mem_chart_source ℂ _
  -- `σ = φ_{f x} ∘ ιd₁⁻¹ ∘ φ_{fd y}⁻¹`
  set cq := chartAt ℂ (fd y) with hcq
  set cf := chartAt ℂ (f x) with hcf
  have hfdy : fd y = ιd₁ (f x) := hfd.1 x
  set O₂ : Set ℂ := cq.target ∩ cq.symm ⁻¹' (range ιd₁ ∩ e₁.symm ⁻¹' cf.source) with hO₂
  have hO₂o : IsOpen O₂ := by
    refine cq.isOpen_inter_preimage_symm ?_
    have : IsOpen (e₁.target ∩ e₁.symm ⁻¹' cf.source) := e₁.isOpen_inter_preimage_symm cf.open_source
    rwa [hd₁.embedding.toOpenPartialHomeomorph_target] at this
  have hqs : fd y ∈ cq.source := mem_chart_source ℂ _
  have hv₂ : cq (fd y) ∈ O₂ := ⟨cq.map_source hqs, by
    show cq.symm (cq (fd y)) ∈ range ιd₁ ∩ e₁.symm ⁻¹' cf.source
    rw [cq.left_inv hqs, hfdy]
    exact ⟨mem_range_self _, by show e₁.symm (ιd₁ (f x)) ∈ cf.source; rw [hl₁]; exact mem_chart_source ℂ _⟩⟩
  have hσd : DifferentiableOn ℂ (fun v => cf (e₁.symm (cq.symm v))) O₂ := by
    intro v hv
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cq.symm v := mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ _) hv.1
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e₁.symm (cq.symm v) :=
      s31qr_open_embedding_inverse hd₁.embedding hd₁.holomorphic hv.2.1
    have h3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) cf (e₁.symm (cq.symm v)) :=
      mdifferentiableAt_atlas (chart_mem_atlas ℂ _) hv.2.2
    exact (mdifferentiableAt_iff_differentiableAt.1 (h3.comp v (h2.comp v h1))).differentiableWithinAt
  have hσi : InjOn (fun v => cf (e₁.symm (cq.symm v))) O₂ := by
    intro v hv w hw he
    have h1 := cf.injOn hv.2.2 hw.2.2 he
    obtain ⟨b, hb⟩ := hv.2.1
    obtain ⟨b', hb'⟩ := hw.2.1
    rw [← hb, ← hb', hl₁, hl₁] at h1
    exact cq.symm.injOn hv.1 hw.1 (by rw [← hb, ← hb', h1])
  have hFτ : localMapExpr fd y ((fun w => cy (ιd₀ (cx.symm w))) (cx x)) = cq (fd y) := by
    rw [hτz]
    show cq (fd (cy.symm (cy y))) = cq (fd y)
    rw [cy.left_inv hys]
  have hσa : AnalyticAt ℂ (fun v => cf (e₁.symm (cq.symm v)))
      (localMapExpr fd y ((fun w => cy (ιd₀ (cx.symm w))) (cx x))) := by
    rw [hFτ]; exact hσd.analyticAt (hO₂o.mem_nhds hv₂)
  have hσ' : deriv (fun v => cf (e₁.symm (cq.symm v)))
      (localMapExpr fd y ((fun w => cy (ιd₀ (cx.symm w))) (cx x))) ≠ 0 := by
    rw [hFτ]; exact deriv_ne_zero_of_injOn hO₂o hσd hσi hv₂
  have hev : ∀ᶠ w in 𝓝 (cx x), localMapExpr f x w =
      (fun v => cf (e₁.symm (cq.symm v))) (localMapExpr fd y ((fun w => cy (ιd₀ (cx.symm w))) w)) := by
    have hc1 : ContinuousAt cx.symm (cx x) := cx.continuousAt_symm (cx.map_source hxs)
    have h1 : ∀ᶠ w in 𝓝 (cx x), ιd₀ (cx.symm w) ∈ cy.source := by
      refine (hd₀.embedding.continuous.continuousAt.comp hc1).preimage_mem_nhds ?_
      show cy.source ∈ 𝓝 (ιd₀ (cx.symm (cx x)))
      rw [cx.left_inv hxs]; exact cy.open_source.mem_nhds hys
    have h2 : ∀ᶠ w in 𝓝 (cx x), fd (ιd₀ (cx.symm w)) ∈ cq.source := by
      refine (fd.continuous.continuousAt.comp
        (hd₀.embedding.continuous.continuousAt.comp hc1)).preimage_mem_nhds ?_
      show cq.source ∈ 𝓝 (fd (ιd₀ (cx.symm (cx x))))
      rw [cx.left_inv hxs]; exact cq.open_source.mem_nhds hqs
    filter_upwards [h1, h2] with w hw1 hw2
    show cf (f (cx.symm w)) = cf (e₁.symm (cq.symm (cq (fd (cy.symm (cy (ιd₀ (cx.symm w))))))))
    rw [cy.left_inv hw1, cq.left_inv hw2, hfd.1, hl₁]
  obtain ⟨U, hUo, hzU, -, hUK⟩ := s26w_isKQC_local_comp (hK.2 y) hτV hτa hτ' hσa hσ' hev univ_mem
  exact ⟨U, hUo, hzU, hUK⟩

/-- **[stub e] The maximal dilatation of a symmetric extension**: `K[f^d] = K[f]` (`≤` by stub d with
`K = K[f]`; `≥` since the local expressions of `f` are those of `f^d` on `ιd₀(S₀)` up to holomorphic chart
changes). -/
theorem s32w_se_maxDil {g n m : ℕ} (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m)
    {Xd₀ Xd₁ : ClosedRS.{u}} {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier}
    {ιd₀ : S₀ → Xd₀.carrier} {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    {f : S₀ ≃ₜ S} (hf : IsQCRS f) {fd : Xd₀.carrier ≃ₜ Xd₁.carrier}
    (hfd : IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd) : maxDilatationRS fd = maxDilatationRS f := by
  haveI : Nonempty S₀ := inferInstance
  haveI : Nonempty Xd₀.carrier := ⟨ιd₀ (Classical.arbitrary S₀)⟩
  have hKf := s29_m_isKQCRS_maxDil hf
  have hKfd := s32w_se_isKQCRS F₀ F₁ hd₀ hd₁ hKf hfd
  have hfdQ : IsQCRS fd := ⟨_, hKfd⟩
  refine le_antisymm ?_ ?_
  · calc maxDilatationRS fd ≤ ENNReal.ofReal (maxDilatationRS f).toReal := maxDilatationRS_le hKfd
      _ = maxDilatationRS f := ENNReal.ofReal_toReal (s29_m_maxDilatationRS_ne_top hf)
  · have h := s32w_se_restrict_isKQCRS F₀ F₁ hd₀ hd₁ hfd (s29_m_isKQCRS_maxDil hfdQ)
    calc maxDilatationRS f ≤ ENNReal.ofReal (maxDilatationRS fd).toReal := maxDilatationRS_le h
      _ = maxDilatationRS fd := ENNReal.ofReal_toReal (s29_m_maxDilatationRS_ne_top hfdQ)

/-- **§32.2 (W1.3): symmetric extension.**  Clauses 1–3 of `symmetric_extension_properties`: a quasiconformal
`f : S₀ → S` has a quasiconformal symmetric extension `f^d` to the Schottky doubles with `K[f^d] = K[f]`.  (The
hypothesis `hm` is used by the seam/hole correspondence `s32w_se_double_dictionary`.) -/
theorem s32w_symmetric_extension {g n m : ℕ} (hm : m ≠ 0)
    (F₀ : FiniteTypeStructure S₀ g n m) (F₁ : FiniteTypeStructure S g n m) {Xd₀ Xd₁ : ClosedRS.{u}}
    {J₀ : Xd₀.carrier ≃ₜ Xd₀.carrier} {J₁ : Xd₁.carrier ≃ₜ Xd₁.carrier} {ιd₀ : S₀ → Xd₀.carrier}
    {ιd₁ : S → Xd₁.carrier} {Pd₀ : Finset Xd₀.carrier} {Pd₁ : Finset Xd₁.carrier}
    (hd₀ : IsSchottkyDouble F₀ Xd₀ J₀ ιd₀ Pd₀) (hd₁ : IsSchottkyDouble F₁ Xd₁ J₁ ιd₁ Pd₁)
    (f : S₀ ≃ₜ S) (hf : IsQCRS f) :
    ∃ fd : Xd₀.carrier ≃ₜ Xd₁.carrier, IsSymmetricExtension J₀ J₁ ιd₀ ιd₁ f fd ∧ IsQCRS fd ∧
      maxDilatationRS fd = maxDilatationRS f := by
  obtain ⟨fd, hfd⟩ := s32w_se_exists hm F₀ F₁ hd₀ hd₁ f hf
  exact ⟨fd, hfd, ⟨_, s32w_se_isKQCRS F₀ F₁ hd₀ hd₁ (s29_m_isKQCRS_maxDil hf) hfd⟩,
    s32w_se_maxDil F₀ F₁ hd₀ hd₁ hf hfd⟩

end LiZhongQC
