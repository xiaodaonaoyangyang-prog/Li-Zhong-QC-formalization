import LiZhongQC.Lemmas.BranchedLiftQC
import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller

open Complex Set Metric Filter Topology MeasureTheory
open scoped Manifold ContDiff Real

noncomputable section

namespace LiZhongQC

universe u

/-- **The terminal natural parameter at a zero (removable singularity).**  Let `ζ` be a natural parameter of
`φ = ((M+2)/2)² ζ^M ζ'² dz²` at `z₀`, let `L` be a homeomorphism near `z₀` with inverse `L⁻¹` near `L z₀`, and
suppose that near every point `z₁ ≠ z₀` the map `L` has the regular Teichmüller form `B ∘ L = S_k ∘ A`
(`A'² = φ`, `B'² = φ'`, `B'(L z₁) ≠ 0`).  Then `Z = S_{k,M} ∘ ζ ∘ L⁻¹` is analytic at `L z₀` with `Z' ≠ 0` and
`φ' = ((M+2)/2)² Z^M Z'²` off `L z₀`: near each point `Z^{M+2} = (B - c)²` (`s26d_b_local_affine`, `eq26_6`), so `Z`
is a constant multiple of an analytic root; `Z` is continuous at `L z₀`, hence analytic there, and injective. -/
theorem s82lc_zero_extend {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) {M : ℕ} {L Linv ζ φ φ' : ℂ → ℂ} {z₀ : ℂ}
    (hζ : AnalyticAt ℂ ζ z₀) (hζ0 : ζ z₀ = 0) (hζd : deriv ζ z₀ ≠ 0)
    (hφ : ∀ᶠ z in 𝓝 z₀, φ z = ((M + 2 : ℂ) / 2) ^ 2 * ζ z ^ M * deriv ζ z ^ 2)
    (hLc : ∀ᶠ z in 𝓝 z₀, ContinuousAt L z) (hLinvL : ∀ᶠ z in 𝓝 z₀, Linv (L z) = z)
    (hLinv : ∀ᶠ w in 𝓝 (L z₀), ContinuousAt Linv w ∧ L (Linv w) = w)
    (hloc : ∀ᶠ z₁ in 𝓝[≠] z₀, ∃ A B : ℂ → ℂ, AnalyticAt ℂ A z₁ ∧ (∀ᶠ z in 𝓝 z₁, deriv A z ^ 2 = φ z) ∧
      AnalyticAt ℂ B (L z₁) ∧ deriv B (L z₁) ≠ 0 ∧ (∀ᶠ w in 𝓝 (L z₁), deriv B w ^ 2 = φ' w) ∧
      ∀ᶠ z in 𝓝 z₁, B (L z) = teichStretch k (A z)) :
    ∃ Z : ℂ → ℂ, AnalyticAt ℂ Z (L z₀) ∧ Z (L z₀) = 0 ∧ deriv Z (L z₀) ≠ 0 ∧
      (∀ᶠ w in 𝓝[≠] (L z₀), φ' w = ((M + 2 : ℂ) / 2) ^ 2 * Z w ^ M * deriv Z w ^ 2) ∧
      ∀ᶠ z in 𝓝 z₀, Z (L z) = teichStretchZero k M (ζ z) := by
  set w₀ := L z₀ with hw₀
  set S := teichStretchZero k M with hS
  have hSc : Continuous S := (teichStretchZero_localHomeomorph hk₀ hk M).1
  have hS0 : S 0 = 0 := (teichStretchZero_localHomeomorph hk₀ hk M).2.1
  set Z : ℂ → ℂ := fun w => S (ζ (Linv w)) with hZ
  have hLi0 : Linv w₀ = z₀ := hLinvL.self_of_nhds
  have hLiw₀ : ContinuousAt Linv w₀ := hLinv.self_of_nhds.1
  have hLit : Tendsto Linv (𝓝 w₀) (𝓝 z₀) := by
    have := hLiw₀.tendsto
    rwa [hLi0] at this
  -- `Linv` maps the punctured neighbourhood of `w₀` into the punctured neighbourhood of `z₀`
  have hLit' : Tendsto Linv (𝓝[≠] w₀) (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hLit.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hLinv, self_mem_nhdsWithin] with w hw hw0
    intro h
    apply hw0
    show w = w₀
    rw [← hw.2, show Linv w = z₀ from h]
  obtain ⟨V, hVo, hz₀V, -, hVi⟩ := s26u_exists_open_injOn hζ hζd
  have hζdc : ∀ᶠ z in 𝓝 z₀, deriv ζ z ≠ 0 := hζ.deriv.continuousAt.eventually_ne hζd
  -- the good set around `z₀`
  have hgoodz : ∀ᶠ z in 𝓝 z₀, z ∈ V ∧ AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      (∀ᶠ z' in 𝓝 z, φ z' = ((M + 2 : ℂ) / 2) ^ 2 * ζ z' ^ M * deriv ζ z' ^ 2) ∧ ContinuousAt L z ∧
      (∀ᶠ z' in 𝓝 z, Linv (L z') = z') :=
    (show ∀ᶠ z in 𝓝 z₀, z ∈ V from hVo.mem_nhds hz₀V).and (hζ.eventually_analyticAt.and (hζdc.and (hφ.eventually_nhds.and
      (hLc.and hLinvL.eventually_nhds))))
  -- the regular points: analyticity of `Z` and the form of `φ'`
  have hreg : ∀ᶠ w in 𝓝[≠] w₀, AnalyticAt ℂ Z w ∧
      φ' w = ((M + 2 : ℂ) / 2) ^ 2 * Z w ^ M * deriv Z w ^ 2 := by
    filter_upwards [hLit'.eventually (hloc.and (nhdsWithin_le_nhds hgoodz)), self_mem_nhdsWithin,
      nhdsWithin_le_nhds hLinv.eventually_nhds] with w hw hw0 hwL
    obtain ⟨⟨A, B, hA, hAd, hB, hB', hBd, hBA⟩, hV1, hζ1, hζd1, hq1, hLc1, hLL1⟩ := hw
    set z₁ := Linv w with hz₁
    have hLz₁ : L z₁ = w := hwL.self_of_nhds.2
    have hz₁0 : z₁ ≠ z₀ := by
      intro h
      apply hw0
      show w = w₀
      rw [← hLz₁, h]
    have hζz₁ : ζ z₁ ≠ 0 := fun h => hz₁0 (hVi hV1 hz₀V (h.trans hζ0.symm))
    have hqz₁ : φ z₁ ≠ 0 := by
      rw [hq1.self_of_nhds]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (div_ne_zero (by exact_mod_cast (show M + 2 ≠ 0 by omega)) two_ne_zero)) (pow_ne_zero _ hζz₁))
        (pow_ne_zero _ hζd1)
    obtain ⟨W, hW, hW2, hWd⟩ := s26d_b_branch hζ1 hζz₁ hq1
    have hq'1 : φ' (L z₁) ≠ 0 := by
      rw [← hBd.self_of_nhds]
      exact pow_ne_zero 2 hB'
    obtain ⟨ε, c, hε, hrel⟩ := s26d_b_local_affine hA hAd hW hWd hqz₁ hB hBd hB hBd hq'1 hLc1 hBA
    have hεsq : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
    -- `Z^{M+2} = (B - c)²` near `w`
    have hLinvt : Tendsto Linv (𝓝 w) (𝓝 z₁) := hwL.self_of_nhds.1.tendsto
    have hpow : ∀ᶠ w' in 𝓝 w, Z w' ^ (M + 2) = (B w' - c) ^ 2 := by
      filter_upwards [hLinvt.eventually hrel, hLinvt.eventually (hζ1.continuousAt.eventually_ne hζz₁), hwL]
        with w' h1 h2 h3
      rw [h3.2] at h1
      show S (ζ (Linv w')) ^ (M + 2) = _
      rw [← eq26_6 k M h2 (hW2 _), h1]
      linear_combination (-(teichStretch k (W (Linv w'))) ^ 2) * hεsq
    have hZw : Z w ≠ 0 := teichStretchZero_ne_zero hk₀ hk M hζz₁
    have hH0 : (B w - c) ^ 2 ≠ 0 := by
      rw [← hpow.self_of_nhds]
      exact pow_ne_zero _ hZw
    have hBw : AnalyticAt ℂ B w := by rw [← hLz₁]; exact hB
    obtain ⟨R, hR, hR0, hRpow⟩ := exists_analyticAt_pow_eq ((hBw.sub analyticAt_const).pow 2) hH0
      (by omega : 0 < M + 2)
    -- `Z = ε' R` near `w`
    have hZc : ∀ᶠ w' in 𝓝 w, ContinuousAt Z w' := by
      filter_upwards [hwL, hLinvt.eventually hζ1.eventually_analyticAt] with w' h1 h2
      exact hSc.continuousAt.comp (h2.continuousAt.comp h1.1)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hZc.and (hpow.and (hRpow.and
      (hR.eventually_analyticAt.and (hR.continuousAt.eventually_ne hR0)))))
    obtain ⟨ε', -, hε'⟩ := s26d_b_eq_root_mul (convex_ball w δ).isPreconnected (by omega : 0 < M + 2)
      (G := Z) (H := R) (fun x hx => (hball hx).1.continuousWithinAt)
      (fun x hx => (hball hx).2.2.2.1.continuousAt.continuousWithinAt) (fun x hx => (hball hx).2.2.2.2)
      (fun x hx => by rw [(hball hx).2.1, (hball hx).2.2.1]; rfl)
    have hZev : Z =ᶠ[𝓝 w] fun x => ε' * R x :=
      Filter.eventually_of_mem (ball_mem_nhds w hδ) fun x hx => hε' x hx
    have hZa : AnalyticAt ℂ Z w := (analyticAt_const.mul hR).congr hZev.symm
    refine ⟨hZa, ?_⟩
    -- the form of `φ'` at `w`
    have hd1 : HasDerivAt (fun x => Z x ^ (M + 2)) (((M + 2 : ℕ) : ℂ) * Z w ^ (M + 2 - 1) * deriv Z w) w :=
      hZa.differentiableAt.hasDerivAt.pow (M + 2)
    have hd2 : HasDerivAt (fun x => (B x - c) ^ 2) (((2 : ℕ) : ℂ) * (B w - c) ^ (2 - 1) * deriv B w) w := by
      have h := (hBw.differentiableAt.hasDerivAt.sub_const c).pow 2
      exact h
    have hpow' : (fun x => Z x ^ (M + 2)) =ᶠ[𝓝 w] fun x => (B x - c) ^ 2 := hpow
    have hd3 := hd1.unique (hd2.congr_of_eventuallyEq hpow')
    have e1 : M + 2 - 1 = M + 1 := by omega
    rw [e1] at hd3
    norm_num at hd3
    have e4 : (((M : ℂ) + 2) * Z w ^ (M + 1) * deriv Z w) ^ 2 = (2 * (B w - c) * deriv B w) ^ 2 := by
      rw [hd3]
    have hp := hpow.self_of_nhds
    have hφ'w : φ' w = deriv B w ^ 2 := by rw [← hLz₁]; exact hBd.self_of_nhds.symm
    rw [hφ'w]
    refine mul_left_cancel₀ (pow_ne_zero (M + 2) hZw) ?_
    linear_combination deriv B w ^ 2 * hp - (1 / 4 : ℂ) * e4
  -- removable singularity at `w₀`
  have hZw₀c : ContinuousAt Z w₀ :=
    hSc.continuousAt.comp (ContinuousAt.comp_of_eq hζ.continuousAt hLiw₀ hLi0)
  have hZa : AnalyticAt ℂ Z w₀ := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    (hreg.mono fun w hw => hw.1.differentiableAt) hZw₀c
  have hZ0 : Z w₀ = 0 := by
    show S (ζ (Linv w₀)) = 0
    rw [hLi0, hζ0, hS0]
  -- `Z` is injective near `w₀`, so `Z'(w₀) ≠ 0`
  obtain ⟨U, hUsub, hUo, hw₀U⟩ := _root_.mem_nhds_iff.1 (hZa.eventually_analyticAt.and
    ((hLit.eventually (hVo.mem_nhds hz₀V)).and hLinv))
  have hinj : InjOn Z U := by
    intro a ha b hb hab
    have h1 : ζ (Linv a) = ζ (Linv b) := eq26_5_injective hk₀ hk M hab
    have h2 : Linv a = Linv b := hVi (hUsub ha).2.1 (hUsub hb).2.1 h1
    rw [← (hUsub ha).2.2.2, ← (hUsub hb).2.2.2, h2]
  have hZd : deriv Z w₀ ≠ 0 := deriv_ne_zero_of_injOn hUo
    (fun w hw => (hUsub hw).1.differentiableAt.differentiableWithinAt) hinj hw₀U
  refine ⟨Z, hZa, hZ0, hZd, hreg.mono fun w hw => hw.2, ?_⟩
  filter_upwards [hLinvL] with z hz
  show S (ζ (Linv (L z))) = S (ζ z)
  rw [hz]

/-- Off a finite set `B`, the inverse chart misses `B` on a punctured neighbourhood of every point. -/
theorem s82lc_punctured_off {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [T1Space Y] {B : Set Y}
    (hB : B.Finite) (y : Y) {z : ℂ} (hz : z ∈ (chartAt ℂ y).target) :
    ∀ᶠ w in 𝓝[≠] z, w ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm w ∉ B := by
  have hc : IsClosed (B \ {(chartAt ℂ y).symm z}) := (hB.subset sdiff_subset).isClosed
  have h1 : ∀ᶠ w in 𝓝 z, (chartAt ℂ y).symm w ∉ B \ {(chartAt ℂ y).symm z} :=
    ((chartAt ℂ y).continuousAt_symm hz).preimage_mem_nhds
      (hc.isOpen_compl.mem_nhds fun h => h.2 rfl)
  filter_upwards [nhdsWithin_le_nhds h1, nhdsWithin_le_nhds ((chartAt ℂ y).open_target.mem_nhds hz),
    self_mem_nhdsWithin] with w hw ht hwz
  refine ⟨ht, fun hwB => hw ⟨hwB, fun h => hwz ?_⟩⟩
  exact (chartAt ℂ y).symm.injOn ht hz h

/-- A function continuous at `z` is determined at `z` by its values on a punctured neighbourhood. -/
theorem s82lc_eq_of_punctured {f g : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z) (hg : ContinuousAt g z)
    (h : ∀ᶠ w in 𝓝[≠] z, f w = g w) : f z = g z :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun _ hw => hw.symm))

open Classical in
/-- **Removable points of a quadratic differential.**  A family `Q₀` which vanishes off the chart targets, obeys
the transformation law and is holomorphic at the points off a finite set `B`, and near each point of `B` (in its
own chart) agrees off the point with an analytic function, becomes a holomorphic quadratic differential after
filling in its limits at the points over `B`. -/
theorem s82lc_fill {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [T1Space Y] [IsManifold 𝓘(ℂ) ω Y]
    {Q₀ : Y → ℂ → ℂ} {B : Set Y} (hB : B.Finite)
    (h1 : ∀ y z, z ∉ (chartAt ℂ y).target → Q₀ y z = 0)
    (h2 : ∀ x y : Y, ∀ z ∈ (chartAt ℂ y).target, (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source →
      (chartAt ℂ y).symm z ∉ B → Q₀ y z = Q₀ x (chartTransition x y z) * deriv (chartTransition x y) z ^ 2)
    (h3 : ∀ y, ∀ z ∈ (chartAt ℂ y).target, (chartAt ℂ y).symm z ∉ B → DifferentiableAt ℂ (Q₀ y) z)
    (h4 : ∀ b ∈ B, ∃ G : ℂ → ℂ, AnalyticAt ℂ G (chartAt ℂ b b) ∧
      ∀ᶠ z in 𝓝[≠] (chartAt ℂ b b), Q₀ b z = G z) :
    IsHolQuadDiff (fun y z => if z ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm z ∈ B then
      limUnder (𝓝[≠] z) (Q₀ y) else Q₀ y z) := by
  set Q : Y → ℂ → ℂ := fun y z => if z ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm z ∈ B then
      limUnder (𝓝[≠] z) (Q₀ y) else Q₀ y z with hQ
  have hoff : ∀ y z, (chartAt ℂ y).symm z ∉ B → Q y z = Q₀ y z := fun y z h => by
    show (if _ then _ else _) = _
    rw [ite_eq_right fun h' => h h'.2]
  -- the transition near a point of the chart domain
  have htr : ∀ x y : Y, ∀ z ∈ (chartAt ℂ y).target, (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source →
      AnalyticAt ℂ (chartTransition x y) z ∧ deriv (chartTransition x y) z ≠ 0 ∧
        ∀ᶠ w in 𝓝 z, w ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm w ∈ (chartAt ℂ x).source := by
    intro x y z hz hzx
    have hNo : IsOpen ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) :=
      (chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source
    have hd : DifferentiableOn ℂ (chartTransition x y)
        ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) := fun w hw =>
      (s23_transition_differentiableAt x y hw.1 hw.2).differentiableWithinAt
    exact ⟨hd.analyticAt (hNo.mem_nhds ⟨hz, hzx⟩), (s23_transition x y hz hzx).2,
      hNo.mem_nhds ⟨hz, hzx⟩⟩
  -- near a point over `B`, `Q₀ y` agrees off the point with an analytic function
  have hA : ∀ y, ∀ z ∈ (chartAt ℂ y).target, (chartAt ℂ y).symm z ∈ B →
      ∃ G : ℂ → ℂ, AnalyticAt ℂ G z ∧ ∀ᶠ w in 𝓝[≠] z, Q₀ y w = G w := by
    intro y z hz hzB
    set b := (chartAt ℂ y).symm z with hb
    obtain ⟨G, hG, hGeq⟩ := h4 b hzB
    have hzb : (chartAt ℂ y).symm z ∈ (chartAt ℂ b).source := mem_chart_source ℂ b
    obtain ⟨hτa, -, hN⟩ := htr b y z hz hzb
    set τ := chartTransition b y with hτ
    have hτz : τ z = chartAt ℂ b b := rfl
    have hτt : Tendsto τ (𝓝[≠] z) (𝓝[≠] (chartAt ℂ b b)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · rw [← hτz]
        exact hτa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [nhdsWithin_le_nhds hN, self_mem_nhdsWithin] with w hw hwz
        intro h
        apply hwz
        have h' : chartAt ℂ b ((chartAt ℂ y).symm w) = chartAt ℂ b ((chartAt ℂ y).symm z) := h
        exact (chartAt ℂ y).symm.injOn hw.1 hz ((chartAt ℂ b).injOn hw.2 hzb h')
    refine ⟨fun w => G (τ w) * deriv τ w ^ 2, ?_, ?_⟩
    · exact (AnalyticAt.comp_of_eq hG hτa hτz).mul (hτa.deriv.pow 2)
    · filter_upwards [hτt.eventually hGeq, nhdsWithin_le_nhds hN, s82lc_punctured_off hB y hz]
        with w hw1 hw2 hw3
      rw [h2 b y w hw2.1 hw2.2 hw3.2, hw1]
  -- `Q y` is analytic on the chart target
  have hC : ∀ y, ∀ z ∈ (chartAt ℂ y).target, AnalyticAt ℂ (Q y) z := by
    intro y z hz
    by_cases hzB : (chartAt ℂ y).symm z ∈ B
    · obtain ⟨G, hG, hGeq⟩ := hA y z hz hzB
      have hlim : limUnder (𝓝[≠] z) (Q₀ y) = G z :=
        ((hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
          (hGeq.mono fun _ hw => hw.symm)).limUnder_eq
      refine hG.congr ?_
      have hpz : ∀ᶠ w in 𝓝[≠] z, G w = Q y w := by
        filter_upwards [hGeq, s82lc_punctured_off hB y hz] with w hw1 hw2
        rw [hoff y w hw2.2, hw1]
      rw [eventually_nhdsWithin_iff] at hpz
      filter_upwards [hpz] with w hw
      by_cases hwz : w = z
      · subst hwz
        show G w = if _ then _ else _
        rw [ite_eq_left ⟨hz, hzB⟩, hlim]
      · exact hw hwz
    · have hc : IsClosed B := hB.isClosed
      have hN : ∀ᶠ w in 𝓝 z, w ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm w ∉ B :=
        (show ∀ᶠ w in 𝓝 z, w ∈ (chartAt ℂ y).target from (chartAt ℂ y).open_target.mem_nhds hz).and
          (((chartAt ℂ y).continuousAt_symm hz).preimage_mem_nhds (hc.isOpen_compl.mem_nhds hzB))
      obtain ⟨U, hUsub, hUo, hzU⟩ := _root_.mem_nhds_iff.1 hN
      have hd : DifferentiableOn ℂ (Q₀ y) U := fun w hw =>
        (h3 y w (hUsub hw).1 (hUsub hw).2).differentiableWithinAt
      exact (hd.analyticAt (hUo.mem_nhds hzU)).congr
        (Filter.eventually_of_mem (hUo.mem_nhds hzU) fun w hw => (hoff y w (hUsub hw).2).symm)
  have key : IsDiffFamily 2 0 Q ∧ ∀ y : Y, DifferentiableOn ℂ (Q y) (chartAt ℂ y).target := by
    refine ⟨⟨fun y z hz => ?_, fun x y z hz hzx => ?_⟩, fun y z hz =>
      (hC y z hz).differentiableAt.differentiableWithinAt⟩
    · show (if _ then _ else _) = _
      rw [ite_eq_right fun h => hz h.1]
      exact h1 y z hz
    · rw [zpow_zero, mul_one, zpow_two, ← pow_two]
      obtain ⟨hτt, -, hτeq⟩ := s23_transition_mem hz hzx
      by_cases hzB : (chartAt ℂ y).symm z ∈ B
      · obtain ⟨hτa, -, hN⟩ := htr x y z hz hzx
        refine s82lc_eq_of_punctured (hC y z hz).continuousAt
          ((ContinuousAt.comp_of_eq (hC x _ hτt).continuousAt hτa.continuousAt rfl).mul
            (hτa.deriv.continuousAt.pow 2)) ?_
        filter_upwards [nhdsWithin_le_nhds hN, s82lc_punctured_off hB y hz] with w hw1 hw2
        obtain ⟨hwt, -, hweq⟩ := s23_transition_mem hw1.1 hw1.2
        show Q y w = Q x (chartTransition x y w) * deriv (chartTransition x y) w ^ 2
        rw [hoff y w hw2.2, h2 x y w hw1.1 hw1.2 hw2.2, hoff x _ (by rw [hweq]; exact hw2.2)]
      · rw [hoff y z hzB, h2 x y z hz hzx hzB, hoff x _ (by rw [hτeq]; exact hzB)]
  exact key

/-- The inverse of a holomorphic injection, composed with a holomorphic map, is holomorphic over the range. -/
theorem s82lc_invFun_mdifferentiableAt {M N Y : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] [TopologicalSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [Nonempty M] {f : M → N} (hinj : Function.Injective f)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {pr : Y → N} {y : Y} (hpr : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) pr y)
    (hy : pr y ∈ range f) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun t => Function.invFun f (pr t)) y := by
  have hoe := s31inv_isOpenEmbedding hinj hf
  set e := hoe.toOpenPartialHomeomorph f with he
  have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e.symm (pr y) :=
    (s31inv_symm_mdifferentiableOn hinj hf (pr y) hy).mdifferentiableAt (hoe.isOpen_range.mem_nhds hy)
  refine (h1.comp y hpr).congr_of_eventuallyEq ?_
  filter_upwards [hpr.continuousAt.preimage_mem_nhds (hoe.isOpen_range.mem_nhds hy)] with t ht
  obtain ⟨s, hs⟩ := ht
  show Function.invFun f (pr t) = e.symm (pr t)
  rw [← hs, Function.leftInverse_invFun hinj s]
  have hse : s ∈ e.source := by simp [he]
  have : e s = f s := by simp [he]
  rw [← this, e.left_inv hse]

section RawPullback

variable {Y M : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- The chart transfer `φ_x ∘ pm ∘ φ_y⁻¹` of a map holomorphic at `φ_y⁻¹ w` is holomorphic at `w`. -/
theorem s82lc_raw_T_diff (pm : Y → M) (y : Y) (x : M) {w : ℂ} (hw : w ∈ (chartAt ℂ y).target)
    (hpm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) pm ((chartAt ℂ y).symm w))
    (hwx : pm ((chartAt ℂ y).symm w) ∈ (chartAt ℂ x).source) :
    DifferentiableAt ℂ (fun v => chartAt ℂ x (pm ((chartAt ℂ y).symm v))) w := by
  have h := ((s23_mdifferentiableAt_iff (f := pm) (y := x) ((chartAt ℂ y).map_target hw) hwx).1 hpm).2
  rwa [(chartAt ℂ y).right_inv hw] at h

/-- **The pull-back in a fixed chart.**  The pull-back `pm^* Q` read in the chart at the image point equals its
reading `Q_x(T w) T'(w)²` in any chart `x` at the image point (`T = φ_x ∘ pm ∘ φ_y⁻¹`). -/
theorem s82lc_raw_local {Q : M → ℂ → ℂ} (hQ : IsDiffFamily 2 0 Q) (pm : Y → M) (y : Y) (x : M) {w : ℂ}
    (hw : w ∈ (chartAt ℂ y).target) (hpm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) pm ((chartAt ℂ y).symm w))
    (hwx : pm ((chartAt ℂ y).symm w) ∈ (chartAt ℂ x).source) :
    Q (pm ((chartAt ℂ y).symm w)) (chartAt ℂ (pm ((chartAt ℂ y).symm w)) (pm ((chartAt ℂ y).symm w))) *
        deriv (fun v => chartAt ℂ (pm ((chartAt ℂ y).symm w)) (pm ((chartAt ℂ y).symm v))) w ^ 2 =
      Q x (chartAt ℂ x (pm ((chartAt ℂ y).symm w))) *
        deriv (fun v => chartAt ℂ x (pm ((chartAt ℂ y).symm v))) w ^ 2 := by
  set s := pm ((chartAt ℂ y).symm w)
  have hst : chartAt ℂ s s ∈ (chartAt ℂ s).target := (chartAt ℂ s).map_source (mem_chart_source ℂ s)
  have hss : (chartAt ℂ s).symm (chartAt ℂ s s) = s := (chartAt ℂ s).left_inv (mem_chart_source ℂ s)
  have hlaw : Q s (chartAt ℂ s s) = Q x (chartTransition x s (chartAt ℂ s s)) *
      deriv (chartTransition x s) (chartAt ℂ s s) ^ 2 := by
    rw [hQ.2 x s _ hst (by rw [hss]; exact hwx)]
    norm_num
  have hT : chartTransition x s (chartAt ℂ s s) = chartAt ℂ x s := by
    show chartAt ℂ x ((chartAt ℂ s).symm (chartAt ℂ s s)) = chartAt ℂ x s
    rw [hss]
  rw [hT] at hlaw
  have hTd : DifferentiableAt ℂ (chartTransition x s) (chartAt ℂ s s) :=
    s23_transition_differentiableAt x s hst (by rw [hss]; exact hwx)
  have hgd : DifferentiableAt ℂ (fun v => chartAt ℂ s (pm ((chartAt ℂ y).symm v))) w :=
    s82lc_raw_T_diff pm y s hw hpm (mem_chart_source ℂ s)
  have hcont : ContinuousAt (fun v => pm ((chartAt ℂ y).symm v)) w :=
    ContinuousAt.comp (g := pm) hpm.continuousAt ((chartAt ℂ y).continuousAt_symm hw)
  have hev : (fun v => chartAt ℂ x (pm ((chartAt ℂ y).symm v))) =ᶠ[𝓝 w]
      chartTransition x s ∘ fun v => chartAt ℂ s (pm ((chartAt ℂ y).symm v)) := by
    filter_upwards [hcont.preimage_mem_nhds ((chartAt ℂ s).open_source.mem_nhds (mem_chart_source ℂ s))]
      with v hv
    show chartAt ℂ x (pm ((chartAt ℂ y).symm v)) =
      chartAt ℂ x ((chartAt ℂ s).symm (chartAt ℂ s (pm ((chartAt ℂ y).symm v))))
    rw [(chartAt ℂ s).left_inv hv]
  have hder : deriv (fun v => chartAt ℂ x (pm ((chartAt ℂ y).symm v))) w =
      deriv (chartTransition x s) (chartAt ℂ s s) *
        deriv (fun v => chartAt ℂ s (pm ((chartAt ℂ y).symm v))) w := by
    rw [hev.deriv_eq]
    exact (hTd.hasDerivAt.comp w hgd.hasDerivAt).deriv
  rw [hder, hlaw]
  ring

/-- **The transformation law of the pull-back.** -/
theorem s82lc_raw_law (Q : M → ℂ → ℂ) (pm : Y → M) (y y' : Y) {w : ℂ}
    (hw : w ∈ (chartAt ℂ y').target) (hwy : (chartAt ℂ y').symm w ∈ (chartAt ℂ y).source)
    (hpm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) pm ((chartAt ℂ y').symm w)) :
    Q (pm ((chartAt ℂ y').symm w)) (chartAt ℂ (pm ((chartAt ℂ y').symm w)) (pm ((chartAt ℂ y').symm w))) *
        deriv (fun v => chartAt ℂ (pm ((chartAt ℂ y').symm w)) (pm ((chartAt ℂ y').symm v))) w ^ 2 =
      Q (pm ((chartAt ℂ y).symm (chartTransition y y' w)))
          (chartAt ℂ (pm ((chartAt ℂ y).symm (chartTransition y y' w)))
            (pm ((chartAt ℂ y).symm (chartTransition y y' w)))) *
        deriv (fun v => chartAt ℂ (pm ((chartAt ℂ y).symm (chartTransition y y' w)))
          (pm ((chartAt ℂ y).symm v))) (chartTransition y y' w) ^ 2 *
        deriv (chartTransition y y') w ^ 2 := by
  obtain ⟨hτt, -, hτeq⟩ := s23_transition_mem hw hwy
  rw [hτeq]
  set s := pm ((chartAt ℂ y').symm w)
  have hpm' : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) pm ((chartAt ℂ y).symm (chartTransition y y' w)) := by
    rw [hτeq]; exact hpm
  have hsrc : pm ((chartAt ℂ y).symm (chartTransition y y' w)) ∈ (chartAt ℂ s).source := by
    rw [hτeq]
    exact mem_chart_source ℂ _
  have hτd := (s23_transition y y' hw hwy).1
  have hTd := s82lc_raw_T_diff pm y s hτt hpm' hsrc
  have hev : (fun v => chartAt ℂ s (pm ((chartAt ℂ y').symm v))) =ᶠ[𝓝 w]
      (fun v => chartAt ℂ s (pm ((chartAt ℂ y).symm v))) ∘ chartTransition y y' := by
    filter_upwards [((chartAt ℂ y').isOpen_inter_preimage_symm (chartAt ℂ y).open_source).mem_nhds
      ⟨hw, hwy⟩] with v hv
    show chartAt ℂ s (pm ((chartAt ℂ y').symm v)) =
      chartAt ℂ s (pm ((chartAt ℂ y).symm (chartAt ℂ y ((chartAt ℂ y').symm v))))
    rw [(chartAt ℂ y).left_inv hv.2]
  have hder : deriv (fun v => chartAt ℂ s (pm ((chartAt ℂ y').symm v))) w =
      deriv (fun v => chartAt ℂ s (pm ((chartAt ℂ y).symm v))) (chartTransition y y' w) *
        deriv (chartTransition y y') w := by
    rw [hev.deriv_eq]
    exact (hTd.hasDerivAt.comp w hτd.hasDerivAt).deriv
  rw [hder]
  ring

/-- **Holomorphy of the pull-back** of a holomorphic quadratic differential at a point where `pm` is holomorphic
nearby. -/
theorem s82lc_raw_diff {Q : M → ℂ → ℂ} (hQ : IsHolQuadDiff Q) (pm : Y → M) {O : Set Y} (hO : IsOpen O)
    (hpm : ∀ t ∈ O, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) pm t) (y : Y) {w : ℂ} (hw : w ∈ (chartAt ℂ y).target)
    (hwO : (chartAt ℂ y).symm w ∈ O) :
    DifferentiableAt ℂ (fun w => Q (pm ((chartAt ℂ y).symm w))
      (chartAt ℂ (pm ((chartAt ℂ y).symm w)) (pm ((chartAt ℂ y).symm w))) *
        deriv (fun v => chartAt ℂ (pm ((chartAt ℂ y).symm w)) (pm ((chartAt ℂ y).symm v))) w ^ 2) w := by
  have hQ' : IsDiffFamily 2 0 Q ∧ ∀ x : M, DifferentiableOn ℂ (Q x) (chartAt ℂ x).target := hQ
  set s := pm ((chartAt ℂ y).symm w)
  have hcont : ContinuousAt (fun v => pm ((chartAt ℂ y).symm v)) w :=
    ContinuousAt.comp (g := pm) (hpm _ hwO).continuousAt ((chartAt ℂ y).continuousAt_symm hw)
  set W := (chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' O ∩
    (fun v => pm ((chartAt ℂ y).symm v)) ⁻¹' (chartAt ℂ s).source with hW
  have hWn : W ∈ 𝓝 w := Filter.inter_mem
    (((chartAt ℂ y).isOpen_inter_preimage_symm hO).mem_nhds ⟨hw, hwO⟩)
    (hcont.preimage_mem_nhds ((chartAt ℂ s).open_source.mem_nhds (mem_chart_source ℂ s)))
  obtain ⟨U, hUW, hUo, hwU⟩ := _root_.mem_nhds_iff.1 hWn
  have hTd : DifferentiableOn ℂ (fun v => chartAt ℂ s (pm ((chartAt ℂ y).symm v))) U :=
    fun v hv => (s82lc_raw_T_diff pm y s (hUW hv).1.1 (hpm _ (hUW hv).1.2) (hUW hv).2).differentiableWithinAt
  have hdd := hTd.deriv hUo
  have h1 : DifferentiableAt ℂ (Q s) (chartAt ℂ s (pm ((chartAt ℂ y).symm w))) :=
    (hQ'.2 s).differentiableAt ((chartAt ℂ s).open_target.mem_nhds
      ((chartAt ℂ s).map_source (mem_chart_source ℂ s)))
  have hF : DifferentiableAt ℂ (fun v => Q s (chartAt ℂ s (pm ((chartAt ℂ y).symm v))) *
      deriv (fun v => chartAt ℂ s (pm ((chartAt ℂ y).symm v))) v ^ 2) w :=
    (h1.comp w ((hTd w hwU).differentiableAt (hUo.mem_nhds hwU))).mul
      ((hdd.differentiableAt (hUo.mem_nhds hwU)).pow 2)
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [hUo.mem_nhds hwU] with v hv
  exact s82lc_raw_local hQ'.1 pm y s (hUW hv).1.1 (hpm _ (hUW hv).1.2) (hUW hv).2

end RawPullback

/-- **The pull-back of an admissible differential through `ι⁻¹ ∘ pr`** is the pull-back of the differential on the
closed surface through `pr`: `(ι^* q̂)` pulled back by `ι⁻¹ ∘ pr` is `q̂_x(F w) F'(w)²`, `F = φ_x ∘ pr ∘ φ_y⁻¹`. -/
theorem s82lc_raw_pullback {S Y : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [Nonempty S] [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) {qh : F.X.carrier → ℂ → ℂ} (hqh : qh ∈ admissibleQDSpace F)
    {pr : Y → F.X.carrier} (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr) (y : Y) (x : F.X.carrier) {w : ℂ}
    (hw : w ∈ (chartAt ℂ y).target) (hwO : pr ((chartAt ℂ y).symm w) ∈ range F.ι)
    (hwx : pr ((chartAt ℂ y).symm w) ∈ (chartAt ℂ x).source) :
    pullbackQD F qh (Function.invFun F.ι (pr ((chartAt ℂ y).symm w)))
        (chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ y).symm w)))
          (Function.invFun F.ι (pr ((chartAt ℂ y).symm w)))) *
        deriv (fun v => chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ y).symm w)))
          (Function.invFun F.ι (pr ((chartAt ℂ y).symm v)))) w ^ 2 =
      qh x (chartAt ℂ x (pr ((chartAt ℂ y).symm w))) *
        deriv (fun v => chartAt ℂ x (pr ((chartAt ℂ y).symm v))) w ^ 2 := by
  set s := Function.invFun F.ι (pr ((chartAt ℂ y).symm w)) with hsdef
  have hs : F.ι s = pr ((chartAt ℂ y).symm w) := Function.invFun_eq hwO
  have hπ : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun t => Function.invFun F.ι (pr t)) ((chartAt ℂ y).symm w) :=
    s82lc_invFun_mdifferentiableAt F.embedding.injective F.holomorphic (hpr _) hwO
  have hTd : DifferentiableAt ℂ (fun v => chartAt ℂ s (Function.invFun F.ι (pr ((chartAt ℂ y).symm v)))) w :=
    s82lc_raw_T_diff (fun t => Function.invFun F.ι (pr t)) y s hw hπ (mem_chart_source ℂ s)
  have hst : chartAt ℂ s s ∈ (chartAt ℂ s).target := (chartAt ℂ s).map_source (mem_chart_source ℂ s)
  have hss : (chartAt ℂ s).symm (chartAt ℂ s s) = s := (chartAt ℂ s).left_inv (mem_chart_source ℂ s)
  have hsx : F.ι ((chartAt ℂ s).symm (chartAt ℂ s s)) ∈ (chartAt ℂ x).source := by
    rw [hss, hs]; exact hwx
  rw [s32p_pullbackQD_local F hqh s x hst hsx]
  have hUd := s32p_T_differentiableAt F x s hst hsx
  have hcont : ContinuousAt (fun v => pr ((chartAt ℂ y).symm v)) w :=
    hpr.continuous.continuousAt.comp ((chartAt ℂ y).continuousAt_symm hw)
  have hcont' : ContinuousAt (fun v => Function.invFun F.ι (pr ((chartAt ℂ y).symm v))) w :=
    ContinuousAt.comp (g := fun t => Function.invFun F.ι (pr t)) hπ.continuousAt
      ((chartAt ℂ y).continuousAt_symm hw)
  have hev : (fun v => chartAt ℂ x (pr ((chartAt ℂ y).symm v))) =ᶠ[𝓝 w]
      (fun v => chartAt ℂ x (F.ι ((chartAt ℂ s).symm v))) ∘
        fun v => chartAt ℂ s (Function.invFun F.ι (pr ((chartAt ℂ y).symm v))) := by
    filter_upwards [hcont.preimage_mem_nhds (F.embedding.isOpen_range.mem_nhds hwO),
      hcont'.preimage_mem_nhds ((chartAt ℂ s).open_source.mem_nhds (mem_chart_source ℂ s))] with v hv1 hv2
    show chartAt ℂ x (pr ((chartAt ℂ y).symm v)) = chartAt ℂ x (F.ι ((chartAt ℂ s).symm
      (chartAt ℂ s (Function.invFun F.ι (pr ((chartAt ℂ y).symm v))))))
    rw [(chartAt ℂ s).left_inv hv2, Function.invFun_eq hv1]
  have hTw : chartAt ℂ s (Function.invFun F.ι (pr ((chartAt ℂ y).symm w))) = chartAt ℂ s s := rfl
  have hder : deriv (fun v => chartAt ℂ x (pr ((chartAt ℂ y).symm v))) w =
      deriv (fun v => chartAt ℂ x (F.ι ((chartAt ℂ s).symm v))) (chartAt ℂ s s) *
        deriv (fun v => chartAt ℂ s (Function.invFun F.ι (pr ((chartAt ℂ y).symm v)))) w := by
    rw [hev.deriv_eq]
    exact (hUd.hasDerivAt.comp_of_eq w hTd.hasDerivAt hTw).deriv
  rw [hder, hss, hs]
  ring

/-- **(32.1) for the lifted initial differential.**  At a point `b` over a puncture `p`, in the chart at `b`, the
pull-back of an admissible `q̂` (`q̂ = c/(z - p) + r` near `p`) through `pr = p + ψ²` agrees off `b` with the analytic
function `4c ψ'² + 4ψ²ψ'² r(p + ψ²)`. -/
theorem s82lc_initial_removable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [Nonempty S] {g n : ℕ} (F : FiniteTypeStructure S g n 0) {qh : F.X.carrier → ℂ → ℂ}
    (hqh : qh ∈ admissibleQDSpace F) {Y : ClosedRS.{u}} {pr : Y.carrier → F.X.carrier}
    (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
      (∀ x ∉ F.P, (pr ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F.P, (pr ⁻¹' {x}).ncard = 1)
    (b : Y.carrier) (hb : pr b ∈ F.P) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G (chartAt ℂ b b) ∧ ∀ᶠ z in 𝓝[≠] (chartAt ℂ b b),
      pullbackQD F qh (Function.invFun F.ι (pr ((chartAt ℂ b).symm z)))
          (chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ b).symm z)))
            (Function.invFun F.ι (pr ((chartAt ℂ b).symm z)))) *
          deriv (fun v => chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ b).symm z)))
            (Function.invFun F.ι (pr ((chartAt ℂ b).symm v)))) z ^ 2 = G z := by
  have hrange : range F.ι = (↑F.P)ᶜ := by rw [F.range_ι]; simp
  set p := pr b with hp
  set cb := chartAt ℂ b b with hcb
  set c₀ := chartAt ℂ p p with hc₀
  obtain ⟨ψ, hψ, hψ0, hψ', hbr, -⟩ := s82lc_branch_index hpr b
  have hbb : (chartAt ℂ b).symm cb = b := (chartAt ℂ b).left_inv (mem_chart_source ℂ b)
  have heq : ∀ᶠ z in 𝓝 cb, chartAt ℂ p (pr ((chartAt ℂ b).symm z)) = c₀ + ψ z ^ 2 := by
    filter_upwards [hbr hb] with z hz
    rw [hz, hbb]
  obtain ⟨-, c, r, hr, hreq⟩ := hqh.2.2.1 p p hb (mem_chart_source ℂ p)
  obtain ⟨V, hVo, hcbV, -, hVi⟩ := s26u_exists_open_injOn hψ hψ'
  refine ⟨fun z => 4 * c * deriv ψ z ^ 2 + 4 * ψ z ^ 2 * deriv ψ z ^ 2 * r (c₀ + ψ z ^ 2), ?_, ?_⟩
  · have hra : AnalyticAt ℂ (fun z => r (c₀ + ψ z ^ 2)) cb :=
      AnalyticAt.comp_of_eq hr (analyticAt_const.add (hψ.pow 2)) (by show c₀ + ψ cb ^ 2 = c₀; rw [hψ0]; ring)
    exact (analyticAt_const.mul (hψ.deriv.pow 2)).add (((analyticAt_const.mul (hψ.pow 2)).mul
      (hψ.deriv.pow 2)).mul hra)
  · have hcbt : cb ∈ (chartAt ℂ b).target := (chartAt ℂ b).map_source (mem_chart_source ℂ b)
    have hcont : ContinuousAt (fun z => pr ((chartAt ℂ b).symm z)) cb :=
      hpr.1.continuous.continuousAt.comp ((chartAt ℂ b).continuousAt_symm hcbt)
    have hsrc : ∀ᶠ z in 𝓝 cb, pr ((chartAt ℂ b).symm z) ∈ (chartAt ℂ p).source := by
      refine hcont.preimage_mem_nhds ?_
      rw [show pr ((chartAt ℂ b).symm cb) = p by rw [hbb]]
      exact (chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)
    -- the parameter `u = c₀ + ψ²` tends to `c₀` off `c₀`
    have hut : Tendsto (fun z => c₀ + ψ z ^ 2) (𝓝[≠] cb) (𝓝[≠] c₀) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hc : ContinuousAt (fun z => c₀ + ψ z ^ 2) cb := continuousAt_const.add (hψ.continuousAt.pow 2)
        have h' : Tendsto (fun z => c₀ + ψ z ^ 2) (𝓝 cb) (𝓝 c₀) := by
          convert hc.tendsto using 2
          rw [hψ0]; ring
        exact h'.mono_left nhdsWithin_le_nhds
      · filter_upwards [nhdsWithin_le_nhds (hVo.mem_nhds hcbV), self_mem_nhdsWithin] with z hz hz0
        intro h
        have h2 : ψ z ^ 2 = 0 := by
          have h1 : c₀ + ψ z ^ 2 = c₀ := h
          linear_combination h1
        have : ψ z = ψ cb := by rw [hψ0]; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
        exact hz0 (hVi hz hcbV this)
    have hderF : ∀ᶠ z in 𝓝 cb, deriv (fun v => chartAt ℂ p (pr ((chartAt ℂ b).symm v))) z =
        2 * ψ z * deriv ψ z := by
      filter_upwards [heq.eventually_nhds, hψ.eventually_analyticAt] with z hz hza
      rw [Filter.EventuallyEq.deriv_eq hz]
      have h2 : HasDerivAt (fun x => c₀ + ψ x ^ 2) (((2 : ℕ) : ℂ) * ψ z ^ (2 - 1) * deriv ψ z) z :=
        (hza.differentiableAt.hasDerivAt.pow 2).const_add c₀
      rw [h2.deriv]
      norm_num
    filter_upwards [hut.eventually hreq, s82lc_punctured_off (s82lc_branch_finite hpr) b hcbt,
      nhdsWithin_le_nhds hsrc, nhdsWithin_le_nhds heq, nhdsWithin_le_nhds hderF,
      nhdsWithin_le_nhds (hVo.mem_nhds hcbV), self_mem_nhdsWithin] with z h1 h2 h3 h4 h5 h6 h7
    have hO : pr ((chartAt ℂ b).symm z) ∈ range F.ι := by
      rw [hrange]; exact h2.2
    rw [s82lc_raw_pullback F hqh hpr.1 b p h2.1 hO h3, h4, h5, h1]
    have hψz : ψ z ≠ 0 := fun h => h7 (hVi h6 hcbV (by rw [h, hψ0]))
    have e : c₀ + ψ z ^ 2 - c₀ = ψ z ^ 2 := by ring
    rw [e]
    field_simp
    ring

/-- **Transport of the regular form.**  If near `z₁` the coefficients `φ`, `φ'` are the pull-backs `q_s(T) T'²`,
`q'_{f s}(T₁) T₁'²` of a Teichmüller map `f` at a regular point `s`, through local coordinates `T`, `T₁` with
`T₁ ∘ L = (local expression of f at s) ∘ T`, then `L` has the regular form `B ∘ L = S_k ∘ A` with `A'² = φ`,
`B'² = φ'` (`A = ζ ∘ T`, `B = ζ' ∘ T₁` for the natural parameters `ζ`, `ζ'` of `f` at `s`). -/
theorem s82lc_regular_transport {S₀ S₁ : Type*} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
    [TopologicalSpace S₁] [ChartedSpace ℂ S₁] {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap f q q' k) (s : S₀) {T T₁ L φ φ' : ℂ → ℂ} {z₁ : ℂ}
    (hT : AnalyticAt ℂ T z₁) (hTz : T z₁ = chartAt ℂ s s) (hT₁ : AnalyticAt ℂ T₁ (L z₁))
    (hT₁d : deriv T₁ (L z₁) ≠ 0) (hT₁z : T₁ (L z₁) = chartAt ℂ (f s) (f s))
    (hrel : ∀ᶠ z in 𝓝 z₁, T₁ (L z) = localMapExpr f s (T z))
    (hφ : ∀ᶠ z in 𝓝 z₁, φ z = q s (T z) * deriv T z ^ 2)
    (hφ' : ∀ᶠ w in 𝓝 (L z₁), φ' w = q' (f s) (T₁ w) * deriv T₁ w ^ 2) (hreg : IsRegularPoint q s) :
    ∃ A B : ℂ → ℂ, AnalyticAt ℂ A z₁ ∧ (∀ᶠ z in 𝓝 z₁, deriv A z ^ 2 = φ z) ∧
      AnalyticAt ℂ B (L z₁) ∧ deriv B (L z₁) ≠ 0 ∧ (∀ᶠ w in 𝓝 (L z₁), deriv B w ^ 2 = φ' w) ∧
      ∀ᶠ z in 𝓝 z₁, B (L z) = teichStretch k (A z) := by
  obtain ⟨-, ζ, ζ', hζ, hζ', hr⟩ := hf.regular s hreg
  have hTt : Tendsto T (𝓝 z₁) (𝓝 (chartAt ℂ s s)) := by rw [← hTz]; exact hT.continuousAt.tendsto
  have hT₁t : Tendsto T₁ (𝓝 (L z₁)) (𝓝 (chartAt ℂ (f s) (f s))) := by
    rw [← hT₁z]; exact hT₁.continuousAt.tendsto
  refine ⟨ζ ∘ T, ζ' ∘ T₁, AnalyticAt.comp_of_eq hζ.1 hT hTz, ?_, AnalyticAt.comp_of_eq hζ'.1 hT₁ hT₁z, ?_, ?_,
    ?_⟩
  · filter_upwards [hT.eventually_analyticAt, hTt.eventually hζ.1.eventually_analyticAt,
      hTt.eventually hζ.2.2.2, hφ] with z h1 h2 h3 h4
    rw [deriv_comp z h2.differentiableAt h1.differentiableAt, mul_pow, h3, h4]
  · rw [deriv_comp _ (by rw [hT₁z]; exact hζ'.1.differentiableAt) hT₁.differentiableAt, hT₁z]
    exact mul_ne_zero hζ'.2.2.1 hT₁d
  · filter_upwards [hT₁.eventually_analyticAt, hT₁t.eventually hζ'.1.eventually_analyticAt,
      hT₁t.eventually hζ'.2.2.2, hφ'] with w h1 h2 h3 h4
    rw [deriv_comp w h2.differentiableAt h1.differentiableAt, mul_pow, h3, h4]
  · filter_upwards [hrel, hTt.eventually hr] with z h1 h2
    simp only [Function.comp_apply]
    rw [h1, h2]

/-- A coefficient of the natural form `((M+2)/2)² Z^M Z'²` (`Z(c) = 0`, `Z'(c) ≠ 0`) has a zero of order `M`. -/
theorem s82lc_order_of_form {φ Z : ℂ → ℂ} {c : ℂ} {M : ℕ} (hZ : AnalyticAt ℂ Z c) (hZ0 : Z c = 0)
    (hZd : deriv Z c ≠ 0) (hφ : ∀ᶠ w in 𝓝 c, φ w = ((M + 2 : ℂ) / 2) ^ 2 * Z w ^ M * deriv Z w ^ 2)
    (hφa : AnalyticAt ℂ φ c) : meromorphicOrderAt φ c = (M : ℤ) := by
  set h := dslope Z c with hh
  have hha : AnalyticAt ℂ h c := analyticAt_dslope hZ
  have hhc : h c = deriv Z c := by rw [hh, dslope_same]
  have hZeq : ∀ w, Z w = (w - c) * h w := by
    intro w
    rw [hh]
    have := sub_smul_dslope Z c w
    rw [hZ0, sub_zero, smul_eq_mul] at this
    exact this.symm
  have hc2 : ((M + 2 : ℂ) / 2) ≠ 0 := div_ne_zero (by exact_mod_cast (show M + 2 ≠ 0 by omega)) two_ne_zero
  rw [hφa.meromorphicOrderAt_eq]
  have : analyticOrderAt φ c = M := by
    refine hφa.analyticOrderAt_eq_natCast.2 ⟨fun w => ((M + 2 : ℂ) / 2) ^ 2 * h w ^ M * deriv Z w ^ 2,
      (analyticAt_const.mul (hha.pow M)).mul (hZ.deriv.pow 2), ?_, ?_⟩
    · show ((M + 2 : ℂ) / 2) ^ 2 * h c ^ M * deriv Z c ^ 2 ≠ 0
      rw [hhc]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc2) (pow_ne_zero _ hZd)) (pow_ne_zero _ hZd)
    · filter_upwards [hφ] with w hw
      rw [hw, hZeq w, smul_eq_mul, mul_pow]
      ring
  rw [this]
  simp

/-- `ι⁻¹ ∘ pr` is holomorphic at the points off the punctures. -/
theorem s82lc_pi_mdiff {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [Nonempty S]
    {g n : ℕ} (F : FiniteTypeStructure S g n 0) {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {pr : Y → F.X.carrier} (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr) {t : Y} (ht : pr t ∉ F.P) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun t => Function.invFun F.ι (pr t)) t := by
  have hrange : range F.ι = (↑F.P)ᶜ := by rw [F.range_ι]; simp
  exact s82lc_invFun_mdifferentiableAt F.embedding.injective F.holomorphic (hpr t) (by rw [hrange]; exact ht)

/-- **Analyticity of a chart transfer** `φ_x ∘ π ∘ φ_y⁻¹` at `w`, when `π` is holomorphic on an open set
containing `φ_y⁻¹ w`, together with the good neighbourhood. -/
theorem s82lc_T_analytic {Y M : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] (pm : Y → M) {O : Set Y} (hO : IsOpen O)
    (hpm : ∀ t ∈ O, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) pm t) (y : Y) (x : M) {w : ℂ}
    (hw : w ∈ (chartAt ℂ y).target) (hwO : (chartAt ℂ y).symm w ∈ O)
    (hwx : pm ((chartAt ℂ y).symm w) ∈ (chartAt ℂ x).source) :
    AnalyticAt ℂ (fun v => chartAt ℂ x (pm ((chartAt ℂ y).symm v))) w ∧
      ∀ᶠ v in 𝓝 w, v ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm v ∈ O ∧
        pm ((chartAt ℂ y).symm v) ∈ (chartAt ℂ x).source := by
  have hcont : ContinuousAt (fun v => pm ((chartAt ℂ y).symm v)) w :=
    ContinuousAt.comp (g := pm) (hpm _ hwO).continuousAt ((chartAt ℂ y).continuousAt_symm hw)
  have hev : ∀ᶠ v in 𝓝 w, v ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm v ∈ O ∧
      pm ((chartAt ℂ y).symm v) ∈ (chartAt ℂ x).source := by
    have h1 := ((chartAt ℂ y).isOpen_inter_preimage_symm hO).mem_nhds ⟨hw, hwO⟩
    have h2 := hcont.preimage_mem_nhds ((chartAt ℂ x).open_source.mem_nhds hwx)
    filter_upwards [h1, h2] with v hv1 hv2
    exact ⟨hv1.1, hv1.2, hv2⟩
  refine ⟨Complex.analyticAt_iff_eventually_differentiableAt.2 ?_, hev⟩
  filter_upwards [hev] with v hv
  exact s82lc_raw_T_diff pm y x hv.1 (hpm _ hv.2.1) hv.2.2

/-- The lift `Φ` commutes with `ι⁻¹ ∘ pr` off the punctures: `ι₁⁻¹(pr₁(Φ t)) = f(ι₀⁻¹(pr₀ t))`. -/
theorem s82lc_commute {S₀ S : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [Nonempty S₀]
    [TopologicalSpace S] [ChartedSpace ℂ S] [Nonempty S] {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) (F₁ : FiniteTypeStructure S g n 0)
    {Y₀ Y₁ : ClosedRS.{u}} {pr₀ : Y₀.carrier → F₀.X.carrier} {pr₁ : Y₁.carrier → F₁.X.carrier}
    {f : S₀ ≃ₜ S} {Φ : Y₀.carrier ≃ₜ Y₁.carrier} (hΦ : ∀ y s, pr₀ y = F₀.ι s → pr₁ (Φ y) = F₁.ι (f s))
    {t : Y₀.carrier} (ht : pr₀ t ∉ F₀.P) :
    pr₁ (Φ t) ∉ F₁.P ∧ Function.invFun F₁.ι (pr₁ (Φ t)) = f (Function.invFun F₀.ι (pr₀ t)) := by
  have hr0 : range F₀.ι = (↑F₀.P)ᶜ := by rw [F₀.range_ι]; simp
  have hr1 : range F₁.ι = (↑F₁.P)ᶜ := by rw [F₁.range_ι]; simp
  have h0 : pr₀ t ∈ range F₀.ι := by rw [hr0]; exact ht
  have h1 := hΦ t _ (Function.invFun_eq h0).symm
  refine ⟨?_, ?_⟩
  · have : pr₁ (Φ t) ∈ range F₁.ι := ⟨_, h1.symm⟩
    rw [hr1] at this
    exact this
  · rw [h1]
    exact Function.leftInverse_invFun F₁.embedding.injective _

/-- **Chart data of the lift at a point off the punctures.**  At `z₁` in the domain of `L = localMapExpr Φ a`
with `t = φ_a⁻¹ z₁` off the punctures and `s = ι₀⁻¹(pr₀ t)`, the transfers `T = φ_s ∘ ι₀⁻¹ ∘ pr₀ ∘ φ_a⁻¹` and
`T₁ = φ_{f s} ∘ ι₁⁻¹ ∘ pr₁ ∘ φ_{Φ a}⁻¹` are local coordinates with `T₁ ∘ L = (local expression of f at s) ∘ T`, and the
pull-backs of any quadratic differentials read `Q_s(T) T'²` and `Q'_{f s}(T₁) T₁'²` near `z₁`, `L z₁`. -/
theorem s82lc_chart_data {S₀ S : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [Nonempty S₀] [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [Nonempty S] {g n : ℕ}
    (F₀ : FiniteTypeStructure S₀ g n 0) (F₁ : FiniteTypeStructure S g n 0)
    {Y₀ Y₁ : ClosedRS.{u}} {pr₀ : Y₀.carrier → F₀.X.carrier} {pr₁ : Y₁.carrier → F₁.X.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀)
    (hpr₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₁ ∧ Function.Surjective pr₁ ∧
      (∀ x ∉ F₁.P, (pr₁ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₁.P, (pr₁ ⁻¹' {x}).ncard = 1)
    {f : S₀ ≃ₜ S} {Φ : Y₀.carrier ≃ₜ Y₁.carrier}
    (hΦ : ∀ y s, pr₀ y = F₀.ι s → pr₁ (Φ y) = F₁.ι (f s))
    (a : Y₀.carrier) {z₁ : ℂ} (hz₁ : z₁ ∈ localMapDomain Φ a) (ht : pr₀ ((chartAt ℂ a).symm z₁) ∉ F₀.P) :
    ∃ T T₁ : ℂ → ℂ, AnalyticAt ℂ T z₁ ∧
      T z₁ = chartAt ℂ (Function.invFun F₀.ι (pr₀ ((chartAt ℂ a).symm z₁)))
        (Function.invFun F₀.ι (pr₀ ((chartAt ℂ a).symm z₁))) ∧
      AnalyticAt ℂ T₁ (localMapExpr Φ a z₁) ∧ deriv T₁ (localMapExpr Φ a z₁) ≠ 0 ∧
      T₁ (localMapExpr Φ a z₁) = chartAt ℂ (f (Function.invFun F₀.ι (pr₀ ((chartAt ℂ a).symm z₁))))
        (f (Function.invFun F₀.ι (pr₀ ((chartAt ℂ a).symm z₁)))) ∧
      ContinuousAt (localMapExpr Φ a) z₁ ∧
      (∀ᶠ z in 𝓝 z₁, T₁ (localMapExpr Φ a z) =
        localMapExpr f (Function.invFun F₀.ι (pr₀ ((chartAt ℂ a).symm z₁))) (T z)) ∧
      (∀ Q : S₀ → ℂ → ℂ, IsDiffFamily 2 0 Q → ∀ᶠ z in 𝓝 z₁,
        Q (Function.invFun F₀.ι (pr₀ ((chartAt ℂ a).symm z)))
            (chartAt ℂ (Function.invFun F₀.ι (pr₀ ((chartAt ℂ a).symm z)))
              (Function.invFun F₀.ι (pr₀ ((chartAt ℂ a).symm z)))) *
          deriv (fun v => chartAt ℂ (Function.invFun F₀.ι (pr₀ ((chartAt ℂ a).symm z)))
            (Function.invFun F₀.ι (pr₀ ((chartAt ℂ a).symm v)))) z ^ 2 =
        Q (Function.invFun F₀.ι (pr₀ ((chartAt ℂ a).symm z₁))) (T z) * deriv T z ^ 2) ∧
      (∀ Q : S → ℂ → ℂ, IsDiffFamily 2 0 Q → ∀ᶠ w in 𝓝 (localMapExpr Φ a z₁),
        Q (Function.invFun F₁.ι (pr₁ ((chartAt ℂ (Φ a)).symm w)))
            (chartAt ℂ (Function.invFun F₁.ι (pr₁ ((chartAt ℂ (Φ a)).symm w)))
              (Function.invFun F₁.ι (pr₁ ((chartAt ℂ (Φ a)).symm w)))) *
          deriv (fun v => chartAt ℂ (Function.invFun F₁.ι (pr₁ ((chartAt ℂ (Φ a)).symm w)))
            (Function.invFun F₁.ι (pr₁ ((chartAt ℂ (Φ a)).symm v)))) w ^ 2 =
        Q (f (Function.invFun F₀.ι (pr₀ ((chartAt ℂ a).symm z₁)))) (T₁ w) * deriv T₁ w ^ 2) := by
  set t := (chartAt ℂ a).symm z₁ with htdef
  set s := Function.invFun F₀.ι (pr₀ t) with hsdef
  set π₀ : Y₀.carrier → S₀ := fun t => Function.invFun F₀.ι (pr₀ t) with hπ₀
  set π₁ : Y₁.carrier → S := fun t => Function.invFun F₁.ι (pr₁ t) with hπ₁
  set O₀ : Set Y₀.carrier := (pr₀ ⁻¹' ↑F₀.P)ᶜ with hO₀
  set O₁ : Set Y₁.carrier := (pr₁ ⁻¹' ↑F₁.P)ᶜ with hO₁
  have hO₀o : IsOpen O₀ := (F₀.P.finite_toSet.isClosed.preimage hpr₀.continuous).isOpen_compl
  have hO₁o : IsOpen O₁ := (F₁.P.finite_toSet.isClosed.preimage hpr₁.1.continuous).isOpen_compl
  have hπ₀d : ∀ t ∈ O₀, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) π₀ t := fun t ht => s82lc_pi_mdiff F₀ hpr₀ ht
  have hπ₁d : ∀ t ∈ O₁, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) π₁ t := fun t ht => s82lc_pi_mdiff F₁ hpr₁.1 ht
  set L := localMapExpr Φ a with hL
  have hz₁t : z₁ ∈ (chartAt ℂ a).target := hz₁.1
  have hΦt : Φ t ∈ (chartAt ℂ (Φ a)).source := hz₁.2
  have hLz₁ : L z₁ ∈ (chartAt ℂ (Φ a)).target := (chartAt ℂ (Φ a)).map_source hΦt
  have hLs : (chartAt ℂ (Φ a)).symm (L z₁) = Φ t := (chartAt ℂ (Φ a)).left_inv hΦt
  obtain ⟨hΦtP, hcomm⟩ := s82lc_commute F₀ F₁ hΦ ht
  have hπ₁t : π₁ (Φ t) = f s := hcomm
  -- the transfer `T`
  obtain ⟨hTa, hTev⟩ := s82lc_T_analytic π₀ hO₀o hπ₀d a s hz₁t ht (mem_chart_source ℂ s)
  -- the transfer `T₁`
  have hLO : (chartAt ℂ (Φ a)).symm (L z₁) ∈ O₁ := by rw [hLs]; exact hΦtP
  have hLsrc : π₁ ((chartAt ℂ (Φ a)).symm (L z₁)) ∈ (chartAt ℂ (f s)).source := by
    rw [hLs, hπ₁t]; exact mem_chart_source ℂ _
  obtain ⟨hT₁a, hT₁ev⟩ := s82lc_T_analytic π₁ hO₁o hπ₁d (Φ a) (f s) hLz₁ hLO hLsrc
  set T₁ : ℂ → ℂ := fun v => chartAt ℂ (f s) (π₁ ((chartAt ℂ (Φ a)).symm v)) with hT₁
  have hT₁z : T₁ (L z₁) = chartAt ℂ (f s) (f s) := by
    show chartAt ℂ (f s) (π₁ ((chartAt ℂ (Φ a)).symm (L z₁))) = _
    rw [hLs, hπ₁t]
  -- `T₁` is injective near `L z₁` (the cover is a local homeomorphism off the punctures)
  obtain ⟨e, hte, hepr, -⟩ := (s82lc_local_form hpr₁).2.1 (Φ t) hΦtP
  have hT₁d : deriv T₁ (L z₁) ≠ 0 := by
    have hc : ContinuousAt (chartAt ℂ (Φ a)).symm (L z₁) := (chartAt ℂ (Φ a)).continuousAt_symm hLz₁
    have he : ∀ᶠ v in 𝓝 (L z₁), (chartAt ℂ (Φ a)).symm v ∈ e.source :=
      hc.preimage_mem_nhds (by rw [hLs]; exact e.open_source.mem_nhds hte)
    obtain ⟨U, hUsub, hUo, hU⟩ := _root_.mem_nhds_iff.1 ((hT₁a.eventually_analyticAt.and hT₁ev).and he)
    refine deriv_ne_zero_of_injOn hUo (fun v hv => (hUsub hv).1.1.differentiableAt.differentiableWithinAt)
      ?_ hU
    intro v₁ hv₁ v₂ hv₂ heq
    have h1 := (hUsub hv₁).1.2
    have h2 := (hUsub hv₂).1.2
    have e1 : π₁ ((chartAt ℂ (Φ a)).symm v₁) = π₁ ((chartAt ℂ (Φ a)).symm v₂) :=
      (chartAt ℂ (f s)).injOn h1.2.2 h2.2.2 heq
    have hr1 : range F₁.ι = (↑F₁.P)ᶜ := by rw [F₁.range_ι]; simp
    have e2 : pr₁ ((chartAt ℂ (Φ a)).symm v₁) = pr₁ ((chartAt ℂ (Φ a)).symm v₂) := by
      have i1 : pr₁ ((chartAt ℂ (Φ a)).symm v₁) ∈ range F₁.ι := by rw [hr1]; exact h1.2.1
      have i2 : pr₁ ((chartAt ℂ (Φ a)).symm v₂) ∈ range F₁.ι := by rw [hr1]; exact h2.2.1
      rw [← Function.invFun_eq i1, ← Function.invFun_eq i2]
      exact congrArg F₁.ι e1
    have e3 : (chartAt ℂ (Φ a)).symm v₁ = (chartAt ℂ (Φ a)).symm v₂ := by
      have := e.injOn (hUsub hv₁).2 (hUsub hv₂).2
      rw [← hepr (hUsub hv₁).2, ← hepr (hUsub hv₂).2] at this
      exact this e2
    exact (chartAt ℂ (Φ a)).symm.injOn h1.1 h2.1 e3
  -- continuity of `L`
  have hLc : ContinuousAt L z₁ := by
    have h1 : ContinuousAt (fun z => Φ ((chartAt ℂ a).symm z)) z₁ :=
      Φ.continuous.continuousAt.comp ((chartAt ℂ a).continuousAt_symm hz₁t)
    exact ContinuousAt.comp (g := chartAt ℂ (Φ a)) (f := fun z => Φ ((chartAt ℂ a).symm z))
      ((chartAt ℂ (Φ a)).continuousAt hΦt) h1
  have hΩ : localMapDomain Φ a ∈ 𝓝 z₁ := (s23_localMapDomain_isOpen Φ.continuous a).mem_nhds hz₁
  refine ⟨fun v => chartAt ℂ s (π₀ ((chartAt ℂ a).symm v)), T₁, hTa, rfl, hT₁a, hT₁d, hT₁z, hLc, ?_, ?_, ?_⟩
  · filter_upwards [hΩ, hTev] with z hz hzT
    show chartAt ℂ (f s) (π₁ ((chartAt ℂ (Φ a)).symm (chartAt ℂ (Φ a) (Φ ((chartAt ℂ a).symm z))))) =
      chartAt ℂ (f s) (f ((chartAt ℂ s).symm (chartAt ℂ s (π₀ ((chartAt ℂ a).symm z)))))
    rw [(chartAt ℂ (Φ a)).left_inv hz.2, (chartAt ℂ s).left_inv hzT.2.2]
    exact congrArg (chartAt ℂ (f s)) (s82lc_commute F₀ F₁ hΦ hzT.2.1).2
  · intro Q hQ
    filter_upwards [hTev] with z hz
    exact s82lc_raw_local hQ π₀ a s hz.1 (hπ₀d _ hz.2.1) hz.2.2
  · intro Q hQ
    filter_upwards [hT₁ev] with w hw
    exact s82lc_raw_local hQ π₁ (Φ a) (f s) hw.1 (hπ₁d _ hw.2.1) hw.2.2

/-- **The terminal natural parameter at a point.**  `s82lc_zero_extend` for the local expression `L` of a
homeomorphism `Φ` at `p`, with inverse `φ_p ∘ Φ⁻¹ ∘ φ_{Φ p}⁻¹`. -/
theorem s82lc_point_Z {Y₀ Y₁ : Type*} [TopologicalSpace Y₀] [ChartedSpace ℂ Y₀] [TopologicalSpace Y₁]
    [ChartedSpace ℂ Y₁] (Φ : Y₀ ≃ₜ Y₁) {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1) {M : ℕ} {ζ φ φ' : ℂ → ℂ} (p : Y₀)
    (hζ : AnalyticAt ℂ ζ (chartAt ℂ p p)) (hζ0 : ζ (chartAt ℂ p p) = 0) (hζd : deriv ζ (chartAt ℂ p p) ≠ 0)
    (hφ : ∀ᶠ z in 𝓝 (chartAt ℂ p p), φ z = ((M + 2 : ℂ) / 2) ^ 2 * ζ z ^ M * deriv ζ z ^ 2)
    (hloc : ∀ᶠ z₁ in 𝓝[≠] (chartAt ℂ p p), ∃ A B : ℂ → ℂ, AnalyticAt ℂ A z₁ ∧
      (∀ᶠ z in 𝓝 z₁, deriv A z ^ 2 = φ z) ∧ AnalyticAt ℂ B (localMapExpr Φ p z₁) ∧
      deriv B (localMapExpr Φ p z₁) ≠ 0 ∧ (∀ᶠ w in 𝓝 (localMapExpr Φ p z₁), deriv B w ^ 2 = φ' w) ∧
      ∀ᶠ z in 𝓝 z₁, B (localMapExpr Φ p z) = teichStretch k (A z)) :
    ∃ Z : ℂ → ℂ, AnalyticAt ℂ Z (chartAt ℂ (Φ p) (Φ p)) ∧ Z (chartAt ℂ (Φ p) (Φ p)) = 0 ∧
      deriv Z (chartAt ℂ (Φ p) (Φ p)) ≠ 0 ∧
      (∀ᶠ w in 𝓝[≠] (chartAt ℂ (Φ p) (Φ p)), φ' w = ((M + 2 : ℂ) / 2) ^ 2 * Z w ^ M * deriv Z w ^ 2) ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ p p), Z (localMapExpr Φ p z) = teichStretchZero k M (ζ z) := by
  obtain ⟨hcD, hLc₀⟩ := s23_h_center Φ p
  set L := localMapExpr Φ p with hL
  set Linv : ℂ → ℂ := fun w => chartAt ℂ p (Φ.symm ((chartAt ℂ (Φ p)).symm w)) with hLinv
  have hΩ : localMapDomain Φ p ∈ 𝓝 (chartAt ℂ p p) :=
    (s23_localMapDomain_isOpen Φ.continuous p).mem_nhds hcD
  have hLc : ∀ᶠ z in 𝓝 (chartAt ℂ p p), ContinuousAt L z := by
    filter_upwards [hΩ] with z hz
    have h1 : ContinuousAt (fun z => Φ ((chartAt ℂ p).symm z)) z :=
      Φ.continuous.continuousAt.comp ((chartAt ℂ p).continuousAt_symm hz.1)
    exact ContinuousAt.comp (g := chartAt ℂ (Φ p)) (f := fun z => Φ ((chartAt ℂ p).symm z))
      ((chartAt ℂ (Φ p)).continuousAt hz.2) h1
  have hLinvL : ∀ᶠ z in 𝓝 (chartAt ℂ p p), Linv (L z) = z := by
    filter_upwards [hΩ] with z hz
    show chartAt ℂ p (Φ.symm ((chartAt ℂ (Φ p)).symm (chartAt ℂ (Φ p) (Φ ((chartAt ℂ p).symm z))))) = z
    rw [(chartAt ℂ (Φ p)).left_inv hz.2, Φ.symm_apply_apply, (chartAt ℂ p).right_inv hz.1]
  have hc't : chartAt ℂ (Φ p) (Φ p) ∈ (chartAt ℂ (Φ p)).target :=
    (chartAt ℂ (Φ p)).map_source (mem_chart_source ℂ _)
  have hWo : IsOpen ((chartAt ℂ (Φ p)).target ∩
      (chartAt ℂ (Φ p)).symm ⁻¹' (Φ.symm ⁻¹' (chartAt ℂ p).source)) :=
    (chartAt ℂ (Φ p)).isOpen_inter_preimage_symm (Φ.symm.continuous.isOpen_preimage _ (chartAt ℂ p).open_source)
  have hc'W : chartAt ℂ (Φ p) (Φ p) ∈ (chartAt ℂ (Φ p)).target ∩
      (chartAt ℂ (Φ p)).symm ⁻¹' (Φ.symm ⁻¹' (chartAt ℂ p).source) := by
    refine ⟨hc't, ?_⟩
    show Φ.symm ((chartAt ℂ (Φ p)).symm (chartAt ℂ (Φ p) (Φ p))) ∈ (chartAt ℂ p).source
    rw [(chartAt ℂ (Φ p)).left_inv (mem_chart_source ℂ _), Φ.symm_apply_apply]
    exact mem_chart_source ℂ p
  have hLinv' : ∀ᶠ w in 𝓝 (L (chartAt ℂ p p)), ContinuousAt Linv w ∧ L (Linv w) = w := by
    rw [hLc₀]
    filter_upwards [hWo.mem_nhds hc'W] with w hw
    refine ⟨?_, ?_⟩
    · have h1 : ContinuousAt (fun w => Φ.symm ((chartAt ℂ (Φ p)).symm w)) w :=
        Φ.symm.continuous.continuousAt.comp ((chartAt ℂ (Φ p)).continuousAt_symm hw.1)
      exact ContinuousAt.comp (g := chartAt ℂ p) (f := fun w => Φ.symm ((chartAt ℂ (Φ p)).symm w))
        ((chartAt ℂ p).continuousAt hw.2) h1
    · show chartAt ℂ (Φ p) (Φ ((chartAt ℂ p).symm (chartAt ℂ p (Φ.symm ((chartAt ℂ (Φ p)).symm w))))) = w
      rw [(chartAt ℂ p).left_inv hw.2, Φ.apply_symm_apply, (chartAt ℂ (Φ p)).right_inv hw.1]
  have h := s82lc_zero_extend hk₀ hk hζ hζ0 hζd hφ hLc hLinvL hLinv' hloc
  rw [hLc₀] at h
  exact h

/-- Off the punctures the transfer `φ_x ∘ ι⁻¹ ∘ pr ∘ φ_y⁻¹` has non-vanishing derivative (`pr` is a local
homeomorphism there). -/
theorem s82lc_T_deriv_ne {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [Nonempty S] {g n : ℕ} (F : FiniteTypeStructure S g n 0) {Y : ClosedRS.{u}} {pr : Y.carrier → F.X.carrier}
    (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
      (∀ x ∉ F.P, (pr ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F.P, (pr ⁻¹' {x}).ncard = 1)
    (y : Y.carrier) (x : S) {w : ℂ} (hw : w ∈ (chartAt ℂ y).target) (hwP : pr ((chartAt ℂ y).symm w) ∉ F.P)
    (hwx : Function.invFun F.ι (pr ((chartAt ℂ y).symm w)) ∈ (chartAt ℂ x).source) :
    deriv (fun v => chartAt ℂ x (Function.invFun F.ι (pr ((chartAt ℂ y).symm v)))) w ≠ 0 := by
  set π' : Y.carrier → S := fun t => Function.invFun F.ι (pr t) with hπ'
  have hOo : IsOpen (pr ⁻¹' ↑F.P)ᶜ := (F.P.finite_toSet.isClosed.preimage hpr.1.continuous).isOpen_compl
  obtain ⟨hTa, hTev⟩ := s82lc_T_analytic π' hOo (fun t ht => s82lc_pi_mdiff F hpr.1 ht) y x hw hwP hwx
  obtain ⟨e, hte, hepr, -⟩ := (s82lc_local_form hpr).2.1 _ hwP
  have he : ∀ᶠ v in 𝓝 w, (chartAt ℂ y).symm v ∈ e.source :=
    ((chartAt ℂ y).continuousAt_symm hw).preimage_mem_nhds (e.open_source.mem_nhds hte)
  obtain ⟨U, hUsub, hUo, hU⟩ := _root_.mem_nhds_iff.1 ((hTa.eventually_analyticAt.and hTev).and he)
  refine deriv_ne_zero_of_injOn hUo (fun v hv => (hUsub hv).1.1.differentiableAt.differentiableWithinAt)
    ?_ hU
  intro v₁ hv₁ v₂ hv₂ heq
  have h1 := (hUsub hv₁).1.2
  have h2 := (hUsub hv₂).1.2
  have e1 : π' ((chartAt ℂ y).symm v₁) = π' ((chartAt ℂ y).symm v₂) :=
    (chartAt ℂ x).injOn h1.2.2 h2.2.2 heq
  have hr : range F.ι = (↑F.P)ᶜ := by rw [F.range_ι]; simp
  have e2 : pr ((chartAt ℂ y).symm v₁) = pr ((chartAt ℂ y).symm v₂) := by
    have i1 : pr ((chartAt ℂ y).symm v₁) ∈ range F.ι := by rw [hr]; exact h1.2.1
    have i2 : pr ((chartAt ℂ y).symm v₂) ∈ range F.ι := by rw [hr]; exact h2.2.1
    rw [← Function.invFun_eq i1, ← Function.invFun_eq i2]
    exact congrArg F.ι e1
  have e3 : (chartAt ℂ y).symm v₁ = (chartAt ℂ y).symm v₂ := by
    have := e.injOn (hUsub hv₁).2 (hUsub hv₂).2
    rw [← hepr (hUsub hv₁).2, ← hepr (hUsub hv₂).2] at this
    exact this e2
  exact (chartAt ℂ y).symm.injOn h1.1 h2.1 e3

open Classical in
/-- **The pulled-back family before filling.**  `R_y(z)` is the pull-back of `Q` through `ι⁻¹ ∘ pr` at the points
off the punctures and `0` elsewhere; it vanishes off the chart targets and obeys the transformation law and is
holomorphic off the punctures. -/
theorem s82lc_raw_hyps {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [Nonempty S] {g n : ℕ} (F : FiniteTypeStructure S g n 0) {Y : ClosedRS.{u}} {pr : Y.carrier → F.X.carrier}
    (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr) {Q : S → ℂ → ℂ} (hQ : IsHolQuadDiff Q) {R : Y.carrier → ℂ → ℂ}
    (hR : ∀ y z, R y z = if z ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm z ∉ pr ⁻¹' ↑F.P then
      Q (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))
          (chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))
            (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))) *
        deriv (fun v => chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))
          (Function.invFun F.ι (pr ((chartAt ℂ y).symm v)))) z ^ 2 else 0) :
    (∀ y z, z ∉ (chartAt ℂ y).target → R y z = 0) ∧
      (∀ x y : Y.carrier, ∀ z ∈ (chartAt ℂ y).target, (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source →
        (chartAt ℂ y).symm z ∉ pr ⁻¹' ↑F.P →
          R y z = R x (chartTransition x y z) * deriv (chartTransition x y) z ^ 2) ∧
      ∀ y, ∀ z ∈ (chartAt ℂ y).target, (chartAt ℂ y).symm z ∉ pr ⁻¹' ↑F.P → DifferentiableAt ℂ (R y) z := by
  have hQ' : IsDiffFamily 2 0 Q ∧ ∀ x : S, DifferentiableOn ℂ (Q x) (chartAt ℂ x).target := hQ
  set π' : Y.carrier → S := fun t => Function.invFun F.ι (pr t) with hπ'
  have hOo : IsOpen (pr ⁻¹' ↑F.P)ᶜ := (F.P.finite_toSet.isClosed.preimage hpr.continuous).isOpen_compl
  have hπd : ∀ t ∈ (pr ⁻¹' ↑F.P)ᶜ, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) π' t := fun t ht => s82lc_pi_mdiff F hpr ht
  refine ⟨fun y z hz => ?_, fun x y z hz hzx hzB => ?_, fun y z hz hzB => ?_⟩
  · rw [hR, ite_eq_right fun h => hz h.1]
  · obtain ⟨hτt, -, hτeq⟩ := s23_transition_mem hz hzx
    rw [hR, hR, ite_eq_left ⟨hz, hzB⟩, ite_eq_left ⟨hτt, by rw [hτeq]; exact hzB⟩]
    exact s82lc_raw_law Q π' x y hz hzx (hπd _ hzB)
  · have hN : ∀ᶠ w in 𝓝 z, w ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm w ∉ pr ⁻¹' ↑F.P := by
      have := ((chartAt ℂ y).isOpen_inter_preimage_symm hOo).mem_nhds ⟨hz, hzB⟩
      filter_upwards [this] with w hw
      exact hw
    refine (s82lc_raw_diff hQ π' hOo hπd y hz hzB).congr_of_eventuallyEq ?_
    filter_upwards [hN] with w hw
    rw [hR, ite_eq_left hw]

/-- **The regular form near the punctured neighbourhood of a point** (input of `s82lc_point_Z`): for coefficients
`Q̃_p`, `φ'` which agree off the punctures with the pull-backs of the initial and terminal differentials of a
Teichmüller map `f`, near every point `z₁ ≠ φ_p(p)` with `Q̃_p(z₁) ≠ 0` the lift `Φ` has the regular form. -/
theorem s82lc_hloc {S₀ S : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [Nonempty S₀] [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [Nonempty S] {g n : ℕ}
    (F₀ : FiniteTypeStructure S₀ g n 0) (F₁ : FiniteTypeStructure S g n 0)
    {Y₀ Y₁ : ClosedRS.{u}} {pr₀ : Y₀.carrier → F₀.X.carrier} {pr₁ : Y₁.carrier → F₁.X.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ F₀.P, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₀.P, (pr₀ ⁻¹' {x}).ncard = 1)
    (hpr₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₁ ∧ Function.Surjective pr₁ ∧
      (∀ x ∉ F₁.P, (pr₁ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₁.P, (pr₁ ⁻¹' {x}).ncard = 1)
    {f : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ} (hT : IsTeichmullerMap f q q' k)
    {Φ : Y₀.carrier ≃ₜ Y₁.carrier} (hΦ : ∀ y s, pr₀ y = F₀.ι s → pr₁ (Φ y) = F₁.ι (f s))
    {Qt : Y₀.carrier → ℂ → ℂ} {φ' : ℂ → ℂ} (p : Y₀.carrier)
    (hQt : ∀ z ∈ (chartAt ℂ p).target, pr₀ ((chartAt ℂ p).symm z) ∉ F₀.P →
      Qt p z = q (Function.invFun F₀.ι (pr₀ ((chartAt ℂ p).symm z)))
          (chartAt ℂ (Function.invFun F₀.ι (pr₀ ((chartAt ℂ p).symm z)))
            (Function.invFun F₀.ι (pr₀ ((chartAt ℂ p).symm z)))) *
        deriv (fun v => chartAt ℂ (Function.invFun F₀.ι (pr₀ ((chartAt ℂ p).symm z)))
          (Function.invFun F₀.ι (pr₀ ((chartAt ℂ p).symm v)))) z ^ 2)
    (hφ' : ∀ w ∈ (chartAt ℂ (Φ p)).target, pr₁ ((chartAt ℂ (Φ p)).symm w) ∉ F₁.P →
      φ' w = q' (Function.invFun F₁.ι (pr₁ ((chartAt ℂ (Φ p)).symm w)))
          (chartAt ℂ (Function.invFun F₁.ι (pr₁ ((chartAt ℂ (Φ p)).symm w)))
            (Function.invFun F₁.ι (pr₁ ((chartAt ℂ (Φ p)).symm w)))) *
        deriv (fun v => chartAt ℂ (Function.invFun F₁.ι (pr₁ ((chartAt ℂ (Φ p)).symm w)))
          (Function.invFun F₁.ι (pr₁ ((chartAt ℂ (Φ p)).symm v)))) w ^ 2)
    (hreg : ∀ᶠ z in 𝓝[≠] (chartAt ℂ p p), Qt p z ≠ 0) :
    ∀ᶠ z₁ in 𝓝[≠] (chartAt ℂ p p), ∃ A B : ℂ → ℂ, AnalyticAt ℂ A z₁ ∧
      (∀ᶠ z in 𝓝 z₁, deriv A z ^ 2 = Qt p z) ∧ AnalyticAt ℂ B (localMapExpr Φ p z₁) ∧
      deriv B (localMapExpr Φ p z₁) ≠ 0 ∧ (∀ᶠ w in 𝓝 (localMapExpr Φ p z₁), deriv B w ^ 2 = φ' w) ∧
      ∀ᶠ z in 𝓝 z₁, B (localMapExpr Φ p z) = teichStretch k (A z) := by
  have hqi : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hT.initial
  have hqt : IsDiffFamily 2 0 q' ∧ ∀ x : S, DifferentiableOn ℂ (q' x) (chartAt ℂ x).target := hT.terminal
  have hcpt : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  obtain ⟨hcD, -⟩ := s23_h_center Φ p
  have hΩ : localMapDomain Φ p ∈ 𝓝 (chartAt ℂ p p) :=
    (s23_localMapDomain_isOpen Φ.continuous p).mem_nhds hcD
  have hO₀o : IsOpen (pr₀ ⁻¹' ↑F₀.P)ᶜ := (F₀.P.finite_toSet.isClosed.preimage hpr₀.1.continuous).isOpen_compl
  have hO₁o : IsOpen (pr₁ ⁻¹' ↑F₁.P)ᶜ := (F₁.P.finite_toSet.isClosed.preimage hpr₁.1.continuous).isOpen_compl
  filter_upwards [hreg, s82lc_punctured_off (s82lc_branch_finite hpr₀) p hcpt, nhdsWithin_le_nhds hΩ]
    with z₁ h1 h2 h3
  obtain ⟨T, T₁, hTa, hTz, hT₁a, hT₁d, hT₁z, hLc, hrel, hraw, hraw'⟩ :=
    s82lc_chart_data F₀ F₁ hpr₀.1 hpr₁ hΦ p h3 h2.2
  set s := Function.invFun F₀.ι (pr₀ ((chartAt ℂ p).symm z₁)) with hs
  -- the coefficients near `z₁` and `L z₁`
  have hN₀ : ∀ᶠ z in 𝓝 z₁, z ∈ (chartAt ℂ p).target ∧ (chartAt ℂ p).symm z ∉ pr₀ ⁻¹' ↑F₀.P :=
    ((chartAt ℂ p).isOpen_inter_preimage_symm hO₀o).mem_nhds h2
  have hφ : ∀ᶠ z in 𝓝 z₁, Qt p z = q s (T z) * deriv T z ^ 2 := by
    filter_upwards [hN₀, hraw q hqi.1] with z hz1 hz2
    rw [hQt z hz1.1 hz1.2, hz2]
  have hLt : localMapExpr Φ p z₁ ∈ (chartAt ℂ (Φ p)).target := (chartAt ℂ (Φ p)).map_source h3.2
  have hLs : (chartAt ℂ (Φ p)).symm (localMapExpr Φ p z₁) = Φ ((chartAt ℂ p).symm z₁) :=
    (chartAt ℂ (Φ p)).left_inv h3.2
  have hN₁ : ∀ᶠ w in 𝓝 (localMapExpr Φ p z₁), w ∈ (chartAt ℂ (Φ p)).target ∧
      (chartAt ℂ (Φ p)).symm w ∉ pr₁ ⁻¹' ↑F₁.P :=
    ((chartAt ℂ (Φ p)).isOpen_inter_preimage_symm hO₁o).mem_nhds
      ⟨hLt, show (chartAt ℂ (Φ p)).symm (localMapExpr Φ p z₁) ∉ pr₁ ⁻¹' ↑F₁.P by
        rw [hLs]; exact (s82lc_commute F₀ F₁ hΦ h2.2).1⟩
  have hφ'' : ∀ᶠ w in 𝓝 (localMapExpr Φ p z₁), φ' w = q' (f s) (T₁ w) * deriv T₁ w ^ 2 := by
    filter_upwards [hN₁, hraw' q' hqt.1] with w hw1 hw2
    rw [hφ' w hw1.1 hw1.2, hw2]
  have hregs : IsRegularPoint q s := by
    show q s (chartAt ℂ s s) ≠ 0
    intro h0
    apply h1
    rw [hφ.self_of_nhds, hTz, h0, zero_mul]
  exact s82lc_regular_transport hT s hTa hTz hT₁a hT₁d hT₁z hrel hφ hφ'' hregs

/-- **The pull-back in the chart at a fixed image point.**  A family agreeing off the punctures with the pull-back of
`Q` through `ι⁻¹ ∘ pr` reads, near `φ_y(y)` with `pr y = ι s`, `Q_s(T) T'²` with `T = φ_s ∘ ι⁻¹ ∘ pr ∘ φ_y⁻¹`. -/
theorem s82lc_fixed_chart {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [Nonempty S] {g n : ℕ} (F : FiniteTypeStructure S g n 0) {Y : ClosedRS.{u}} {pr : Y.carrier → F.X.carrier}
    (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr) {Q : S → ℂ → ℂ} (hQ : IsDiffFamily 2 0 Q) {Qt : Y.carrier → ℂ → ℂ}
    (hQt : ∀ y z, z ∈ (chartAt ℂ y).target → (chartAt ℂ y).symm z ∉ pr ⁻¹' ↑F.P →
      Qt y z = Q (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))
          (chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))
            (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))) *
        deriv (fun v => chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))
          (Function.invFun F.ι (pr ((chartAt ℂ y).symm v)))) z ^ 2)
    (y : Y.carrier) (s : S) (hy : pr y = F.ι s) :
    ∀ᶠ z in 𝓝 (chartAt ℂ y y), Qt y z = Q s (chartAt ℂ s (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))) *
      deriv (fun w => chartAt ℂ s (Function.invFun F.ι (pr ((chartAt ℂ y).symm w)))) z ^ 2 := by
  have hr : range F.ι = (↑F.P)ᶜ := by rw [F.range_ι]; simp
  have hyP : pr y ∉ F.P := by
    have : pr y ∈ range F.ι := ⟨s, hy.symm⟩
    rw [hr] at this
    exact this
  have hπy : Function.invFun F.ι (pr y) = s := by
    rw [hy]; exact Function.leftInverse_invFun F.embedding.injective s
  have hOo : IsOpen (pr ⁻¹' ↑F.P)ᶜ := (F.P.finite_toSet.isClosed.preimage hpr.continuous).isOpen_compl
  have hπd : ∀ t ∈ (pr ⁻¹' ↑F.P)ᶜ, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun t => Function.invFun F.ι (pr t)) t :=
    fun t ht => s82lc_pi_mdiff F hpr ht
  have hcyt : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
  have hyy : (chartAt ℂ y).symm (chartAt ℂ y y) = y := (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  obtain ⟨-, hev⟩ := s82lc_T_analytic (fun t => Function.invFun F.ι (pr t)) hOo hπd y s hcyt
    (show (chartAt ℂ y).symm (chartAt ℂ y y) ∉ pr ⁻¹' ↑F.P by rw [hyy]; exact hyP)
    (show Function.invFun F.ι (pr ((chartAt ℂ y).symm (chartAt ℂ y y))) ∈ (chartAt ℂ s).source by
      rw [hyy, hπy]; exact mem_chart_source ℂ s)
  filter_upwards [hev] with z hz
  rw [hQt y z hz.1 hz.2.1]
  exact s82lc_raw_local hQ (fun t => Function.invFun F.ι (pr t)) y s hz.1 (hπd _ hz.2.1) hz.2.2

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **W6** (the lift of a Teichmüller map): a homeomorphism `Φ` of two-sheeted covers branched exactly over the
punctures which covers an admissible Teichmüller map `f₀` is a Teichmüller map with the same `k`, for the lifted
initial differential (holomorphic over the punctures by (32.1)) and the lifted terminal differential (holomorphic
there by the removable singularity theorem for the natural parameter).  Off the points over the punctures, the
lifted differentials are the pull-backs `q̃ = pr₀^* q` and `q̃' = pr₁^* q'` read in charts (`T = φ_s ∘ ι⁻¹ ∘ pr ∘ φ_y⁻¹`,
`q̃_y = q_s ∘ T · T'²`). -/
theorem s82lc_lift_teich {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) (F₁ : FiniteTypeStructure S g n 0)
    {Y₀ Y₁ : ClosedRS.{u}} {pr₀ : Y₀.carrier → F₀.X.carrier} {pr₁ : Y₁.carrier → F₁.X.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ F₀.P, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₀.P, (pr₀ ⁻¹' {x}).ncard = 1)
    (hpr₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₁ ∧ Function.Surjective pr₁ ∧
      (∀ x ∉ F₁.P, (pr₁ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₁.P, (pr₁ ⁻¹' {x}).ncard = 1)
    {f₀ : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ} (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k)
    {Φ : Y₀.carrier ≃ₜ Y₁.carrier} (hΦ : ∀ y s, pr₀ y = F₀.ι s → pr₁ (Φ y) = F₁.ι (f₀ s)) :
    ∃ (qtil : Y₀.carrier → ℂ → ℂ) (qtil' : Y₁.carrier → ℂ → ℂ), IsTeichmullerMap Φ qtil qtil' k ∧
      (∀ (y : Y₀.carrier) (s : S₀), pr₀ y = F₀.ι s → ∀ᶠ z in 𝓝 (chartAt ℂ y y),
        qtil y z = q s (chartAt ℂ s (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm z)))) *
          deriv (fun w => chartAt ℂ s (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm w)))) z ^ 2) ∧
      ∀ (y : Y₁.carrier) (s : S), pr₁ y = F₁.ι s → ∀ᶠ z in 𝓝 (chartAt ℂ y y),
        qtil' y z = q' s (chartAt ℂ s (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm z)))) *
          deriv (fun w => chartAt ℂ s (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm w)))) z ^ 2 := by
  classical
  obtain ⟨qh, hqh, hqeq⟩ := Submodule.mem_map.1 hf₀.1
  have hqeq' : pullbackQD F₀ qh = q := hqeq
  subst hqeq'
  have hT := hf₀.2
  have hk₀ := hT.k_nonneg
  have hk := hT.k_lt_one
  have hqi : IsDiffFamily 2 0 (pullbackQD F₀ qh) ∧
      ∀ x : S₀, DifferentiableOn ℂ (pullbackQD F₀ qh x) (chartAt ℂ x).target := hT.initial
  have hqt : IsDiffFamily 2 0 q' ∧ ∀ x : S, DifferentiableOn ℂ (q' x) (chartAt ℂ x).target := hT.terminal
  have hB₀f : (pr₀ ⁻¹' ↑F₀.P).Finite := s82lc_branch_finite hpr₀
  have hB₁f : (pr₁ ⁻¹' ↑F₁.P).Finite := s82lc_branch_finite hpr₁
  -- the pulled-back families before filling
  set R₀ : Y₀.carrier → ℂ → ℂ := fun y z =>
    if z ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm z ∉ pr₀ ⁻¹' ↑F₀.P then
      pullbackQD F₀ qh (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm z)))
          (chartAt ℂ (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm z)))
            (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm z)))) *
        deriv (fun v => chartAt ℂ (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm z)))
          (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm v)))) z ^ 2 else 0 with hR₀
  set R₁ : Y₁.carrier → ℂ → ℂ := fun y z =>
    if z ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm z ∉ pr₁ ⁻¹' ↑F₁.P then
      q' (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm z)))
          (chartAt ℂ (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm z)))
            (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm z)))) *
        deriv (fun v => chartAt ℂ (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm z)))
          (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm v)))) z ^ 2 else 0 with hR₁
  obtain ⟨h1₀, h2₀, h3₀⟩ := s82lc_raw_hyps F₀ hpr₀.1 hT.initial (R := R₀) (fun y z => rfl)
  obtain ⟨h1₁, h2₁, h3₁⟩ := s82lc_raw_hyps F₁ hpr₁.1 hT.terminal (R := R₁) (fun y z => rfl)
  -- (32.1): the initial family is removable over the punctures
  have h4₀ : ∀ b ∈ pr₀ ⁻¹' ↑F₀.P, ∃ G : ℂ → ℂ, AnalyticAt ℂ G (chartAt ℂ b b) ∧
      ∀ᶠ z in 𝓝[≠] (chartAt ℂ b b), R₀ b z = G z := by
    intro b hb
    obtain ⟨G, hG, hGe⟩ := s82lc_initial_removable F₀ hqh hpr₀ b hb
    refine ⟨G, hG, ?_⟩
    filter_upwards [hGe, s82lc_punctured_off hB₀f b
      ((chartAt ℂ b).map_source (mem_chart_source ℂ b))] with z hz1 hz2
    show (if _ then _ else _) = _
    rw [ite_eq_left hz2]
    exact hz1
  set qtil : Y₀.carrier → ℂ → ℂ := fun y z =>
    if z ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm z ∈ pr₀ ⁻¹' ↑F₀.P then
      limUnder (𝓝[≠] z) (R₀ y) else R₀ y z with hqtil_def
  have hqtil : IsHolQuadDiff qtil := s82lc_fill hB₀f h1₀ h2₀ h3₀ h4₀
  have hqtil_eq : ∀ y z, z ∈ (chartAt ℂ y).target → (chartAt ℂ y).symm z ∉ pr₀ ⁻¹' ↑F₀.P →
      qtil y z = pullbackQD F₀ qh (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm z)))
          (chartAt ℂ (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm z)))
            (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm z)))) *
        deriv (fun v => chartAt ℂ (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm z)))
          (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm v)))) z ^ 2 := by
    intro y z hz hzB
    show (if _ then _ else _) = _
    rw [ite_eq_right fun h => hzB h.2]
    show (if _ then _ else _) = _
    rw [ite_eq_left ⟨hz, hzB⟩]
  have hR₁_eq : ∀ y z, z ∈ (chartAt ℂ y).target → (chartAt ℂ y).symm z ∉ pr₁ ⁻¹' ↑F₁.P →
      R₁ y z = q' (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm z)))
          (chartAt ℂ (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm z)))
            (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm z)))) *
        deriv (fun v => chartAt ℂ (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm z)))
          (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm v)))) z ^ 2 := by
    intro y z hz hzB
    show (if _ then _ else _) = _
    rw [ite_eq_left ⟨hz, hzB⟩]
  -- the lifted initial differential is not zero
  have hqtil_ne : qtil ≠ 0 := by
    obtain ⟨s₀, hs₀⟩ := (s26u_frequently_regular hT.initial hT.initial_ne (Classical.arbitrary S₀)).exists
    obtain ⟨y, hy⟩ := hpr₀.2.1 (F₀.ι s₀)
    have hcyt : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
    have hyy : (chartAt ℂ y).symm (chartAt ℂ y y) = y := (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    have hr : range F₀.ι = (↑F₀.P)ᶜ := by rw [F₀.range_ι]; simp
    have hyP : pr₀ y ∉ F₀.P := by
      have : pr₀ y ∈ range F₀.ι := ⟨s₀, hy.symm⟩
      rw [hr] at this
      exact this
    have hπy : Function.invFun F₀.ι (pr₀ y) = s₀ := by
      rw [hy]; exact Function.leftInverse_invFun F₀.embedding.injective s₀
    have hfix := (s82lc_fixed_chart F₀ hpr₀.1 hqi.1 hqtil_eq y s₀ hy).self_of_nhds
    have hD := s82lc_T_deriv_ne F₀ hpr₀ y s₀ hcyt (by rw [hyy]; exact hyP)
      (show Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm (chartAt ℂ y y))) ∈ (chartAt ℂ s₀).source by
        rw [hyy, hπy]; exact mem_chart_source ℂ s₀)
    intro h0
    have hz : qtil y (chartAt ℂ y y) = 0 := by rw [h0]; rfl
    rw [hfix, hyy, hπy] at hz
    exact mul_ne_zero hs₀ (pow_ne_zero 2 hD) hz
  -- the terminal family is removable over the punctures (the natural parameter `S_{k,M} ∘ ζ ∘ Φ⁻¹`)
  have h4₁ : ∀ b' ∈ pr₁ ⁻¹' ↑F₁.P, ∃ G : ℂ → ℂ, AnalyticAt ℂ G (chartAt ℂ b' b') ∧
      ∀ᶠ z in 𝓝[≠] (chartAt ℂ b' b'), R₁ b' z = G z := by
    intro b' _
    obtain ⟨p, rfl⟩ : ∃ p, Φ p = b' := ⟨Φ.symm b', Φ.apply_symm_apply b'⟩
    obtain ⟨M, ζ, Zd, hD⟩ := s26d_a_data_exists hqtil hqtil_ne p
    obtain ⟨hζa, hζ0, hζd, hζf⟩ := hD.natural
    have hreg : ∀ᶠ z in 𝓝[≠] (chartAt ℂ p p), qtil p z ≠ 0 := by
      filter_upwards [nhdsWithin_le_nhds (Zd.open_source.mem_nhds hD.center), self_mem_nhdsWithin]
        with z h1 h2
      exact hD.ne_zero z h1 h2
    have hl := s82lc_hloc F₀ F₁ hpr₀ hpr₁ hT hΦ (Qt := qtil) (φ' := R₁ (Φ p)) p
      (fun z hz hzP => hqtil_eq p z hz hzP) (fun w hw hwP => hR₁_eq (Φ p) w hw hwP) hreg
    obtain ⟨Z, hZa, -, -, hZf, -⟩ := s82lc_point_Z Φ hk₀ hk p hζa hζ0 hζd hζf hl
    exact ⟨fun w => ((M + 2 : ℂ) / 2) ^ 2 * Z w ^ M * deriv Z w ^ 2,
      (analyticAt_const.mul (hZa.pow M)).mul (hZa.deriv.pow 2), hZf⟩
  set qtil' : Y₁.carrier → ℂ → ℂ := fun y z =>
    if z ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm z ∈ pr₁ ⁻¹' ↑F₁.P then
      limUnder (𝓝[≠] z) (R₁ y) else R₁ y z with hqtil'_def
  have hqtil' : IsHolQuadDiff qtil' := s82lc_fill hB₁f h1₁ h2₁ h3₁ h4₁
  have hqtil'_eq : ∀ y z, z ∈ (chartAt ℂ y).target → (chartAt ℂ y).symm z ∉ pr₁ ⁻¹' ↑F₁.P →
      qtil' y z = q' (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm z)))
          (chartAt ℂ (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm z)))
            (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm z)))) *
        deriv (fun v => chartAt ℂ (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm z)))
          (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm v)))) z ^ 2 := by
    intro y z hz hzB
    show (if _ then _ else _) = _
    rw [ite_eq_right fun h => hzB h.2]
    exact hR₁_eq y z hz hzB
  -- the terminal natural parameter at every point
  have hpt : ∀ (p : Y₀.carrier) (M : ℕ) (ζ : ℂ → ℂ), IsNaturalParameterAtZero qtil p M ζ →
      ∃ Z : ℂ → ℂ, IsNaturalParameterAtZero qtil' (Φ p) M Z ∧
        ∀ᶠ z in 𝓝 (chartAt ℂ p p), Z (localMapExpr Φ p z) = teichStretchZero k M (ζ z) := by
    intro p M ζ hζ
    obtain ⟨hζa, hζ0, hζd, hζf⟩ := hζ
    have hc2 : ((M + 2 : ℂ) / 2) ≠ 0 :=
      div_ne_zero (by exact_mod_cast (show M + 2 ≠ 0 by omega)) two_ne_zero
    have hreg : ∀ᶠ z in 𝓝[≠] (chartAt ℂ p p), qtil p z ≠ 0 := by
      obtain ⟨V, hVo, hcV, -, hVi⟩ := s26u_exists_open_injOn hζa hζd
      filter_upwards [nhdsWithin_le_nhds hζf, nhdsWithin_le_nhds (hVo.mem_nhds hcV),
        nhdsWithin_le_nhds (hζa.deriv.continuousAt.eventually_ne hζd), self_mem_nhdsWithin]
        with z h1 h2 h3 h4
      rw [h1]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc2)
        (pow_ne_zero _ fun h => h4 (hVi h2 hcV (h.trans hζ0.symm)))) (pow_ne_zero _ h3)
    have hl := s82lc_hloc F₀ F₁ hpr₀ hpr₁ hT hΦ (Qt := qtil) (φ' := qtil' (Φ p)) p
      (fun z hz hzP => hqtil_eq p z hz hzP) (fun w hw hwP => hqtil'_eq (Φ p) w hw hwP) hreg
    obtain ⟨Z, hZa, hZ0, hZd, hZf, hrel⟩ := s82lc_point_Z Φ hk₀ hk p hζa hζ0 hζd hζf hl
    have hqt' : IsDiffFamily 2 0 qtil' ∧ ∀ x, DifferentiableOn ℂ (qtil' x) (chartAt ℂ x).target := hqtil'
    have hc't : chartAt ℂ (Φ p) (Φ p) ∈ (chartAt ℂ (Φ p)).target :=
      (chartAt ℂ (Φ p)).map_source (mem_chart_source ℂ _)
    have hqa : AnalyticAt ℂ (qtil' (Φ p)) (chartAt ℂ (Φ p) (Φ p)) :=
      (hqt'.2 (Φ p)).analyticAt ((chartAt ℂ (Φ p)).open_target.mem_nhds hc't)
    have hfa : AnalyticAt ℂ (fun w => ((M + 2 : ℂ) / 2) ^ 2 * Z w ^ M * deriv Z w ^ 2)
        (chartAt ℂ (Φ p) (Φ p)) := (analyticAt_const.mul (hZa.pow M)).mul (hZa.deriv.pow 2)
    have h0 := s82lc_eq_of_punctured hqa.continuousAt hfa.continuousAt hZf
    refine ⟨Z, ⟨hZa, hZ0, hZd, ?_⟩, hrel⟩
    rw [eventually_nhdsWithin_iff] at hZf
    filter_upwards [hZf] with w hw
    by_cases hwc : w = chartAt ℂ (Φ p) (Φ p)
    · rw [hwc]; exact h0
    · exact hw hwc
  refine ⟨qtil, qtil', ⟨(s82lc_lift_qc F₀ F₁ hpr₀ hpr₁ hT.qc hΦ).1, hqtil, hqtil_ne, hqtil', hk₀, hk,
    fun p hp => ?_, fun p n hn => ?_⟩, fun y s hy => s82lc_fixed_chart F₀ hpr₀.1 hqi.1 hqtil_eq y s hy,
    fun y s hy => s82lc_fixed_chart F₁ hpr₁.1 hqt.1 hqtil'_eq y s hy⟩
  · -- regular points
    obtain ⟨M, ζ, Zd, hD⟩ := s26d_a_data_exists hqtil hqtil_ne p
    have hM : M = 0 := hD.regular_iff.1 hp
    subst hM
    obtain ⟨Z, hZ, hrel⟩ := hpt p 0 ζ hD.natural
    obtain ⟨hζa, hζ0, hζd, hζf⟩ := hD.natural
    obtain ⟨hZa, hZ0, hZd, hZf⟩ := hZ
    refine ⟨?_, ζ, Z, ⟨hζa, hζ0, hζd, ?_⟩, ⟨hZa, hZ0, hZd, ?_⟩, ?_⟩
    · show qtil' (Φ p) (chartAt ℂ (Φ p) (Φ p)) ≠ 0
      rw [hZf.self_of_nhds]
      norm_num
      exact hZd
    · filter_upwards [hζf] with z hz
      rw [hz]; norm_num
    · filter_upwards [hZf] with z hz
      rw [hz]; norm_num
    · rw [← s26d_b_teichStretchZero_zero]
      exact hrel
  · -- zeros
    obtain ⟨M, ζ, Zd, hD⟩ := s26d_a_data_exists hqtil hqtil_ne p
    have hMn : M = n := by
      have h1 : meromorphicOrderAt (qtil p) (chartAt ℂ p p) = (M : ℤ) := hD.order
      have h2 : meromorphicOrderAt (qtil p) (chartAt ℂ p p) = (n : ℤ) := hn
      rw [h1] at h2
      exact_mod_cast WithTop.coe_injective h2
    subst hMn
    obtain ⟨Z, ⟨hZa, hZ0, hZd, hZf⟩, -⟩ := hpt p M ζ hD.natural
    have hqt' : IsDiffFamily 2 0 qtil' ∧ ∀ x, DifferentiableOn ℂ (qtil' x) (chartAt ℂ x).target := hqtil'
    have hc't : chartAt ℂ (Φ p) (Φ p) ∈ (chartAt ℂ (Φ p)).target :=
      (chartAt ℂ (Φ p)).map_source (mem_chart_source ℂ _)
    exact s82lc_order_of_form hZa hZ0 hZd hZf
      ((hqt'.2 (Φ p)).analyticAt ((chartAt ℂ (Φ p)).open_target.mem_nhds hc't))

end LiZhongQC
