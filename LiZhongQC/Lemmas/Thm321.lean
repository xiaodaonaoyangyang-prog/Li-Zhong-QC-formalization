import LiZhongQC.Lemmas.BranchedLiftBook
import LiZhongQC.Lemmas.SchottkyBranchedFinal

/-!
# Theorem 32.1 for surfaces of type `(g, n)` (`s82lc_`, §32.1)

The uniqueness theorem for admissible Teichmüller maps between surfaces of type `(g, n, 0)`:
* `n = 0`: the surface is closed and Theorem 26.2 applies (`s82lc_uniq_closed`);
* `n` even, not `(0, 4)`: lift to the two-sheeted cover branched over all punctures, of genus `2g + n/2 - 1 > 1`,
  and apply Theorem 26.2 there (`s82lc_uniq_even_of_cover`);
* `n` odd (not `(0, 3)`) and `(0, 4)`: lift to a two-sheeted cover branched over an even subset `B₀` of the
  punctures, keeping all points over the punctures as punctures (`s82lc_lift_punctured`), which is of even
  type `(h, 2n'')`, and apply the even case there (`s82lc_uniq_punctured_of_cover`);
* `(0, 3)`: there is no nonzero admissible differential (`s82lc_uniq_03`).

The existence of the branched covers (`exists_branched_double_cover`) enters as the hypothesis `hcov` of
`s82lc_thm32_1_of_cover`; the book theorem is `s82lc_thm32_1_of_cover` applied to it.
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

/-- **Theorem 32.1, `n = 0`**: `ι : S₀ → X` is a homeomorphism onto the closed surface, so `S₀` and `S` are closed of
genus `g > 1`, and Theorem 26.2 applies. -/
theorem s82lc_uniq_closed {g : ℕ} (hg : 1 < g) (F₀ : FiniteTypeStructure S₀ g 0 0)
    (F₁ : FiniteTypeStructure S g 0 0) {f₀ : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ}
    (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k) {f : S₀ ≃ₜ S} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    maxDilatationRS f₀ ≤ maxDilatationRS f ∧ (maxDilatationRS f = maxDilatationRS f₀ → ⇑f = ⇑f₀) := by
  have hT := hf₀.2
  have hK₀ := (teichmullerMap_beltrami hT).2
  have hsurj : ∀ (T : Type u) [TopologicalSpace T] [ChartedSpace ℂ T] {g' : ℕ} (G : FiniteTypeStructure T g' 0 0),
      HasGenus T g' := by
    intro T _ _ g' G
    have hr : range G.ι = univ := by rw [G.range_ι, Finset.card_eq_zero.1 G.card_P]; simp
    set e : T ≃ₜ G.X.carrier := G.embedding.isEmbedding.toHomeomorphOfSurjective
      (fun x => by rw [← mem_range, hr]; trivial) with he
    refine ⟨e.symm.compactSpace, fun x => ?_⟩
    obtain ⟨φ⟩ := G.genus.2 (e x)
    exact ⟨(fundamentalGroupMulEquivOfHomeomorph e rfl).trans φ⟩
  obtain ⟨h1, h2⟩ := thm26_2_uniqueness hg (hsurj S₀ F₀) (hsurj S F₁) hT hf hhom
  rw [hK₀]
  exact ⟨h1, h2⟩

/-- **Theorem 32.1, `n` even, given the cover**: with a two-sheeted cover of `F₀.X` branched exactly over the
punctures, of genus `h > 1`, lift (`s82lc_lift_teichmullerMap_double_cover`), apply Theorem 26.2 on the closed
covers and descend through the surjective projection. -/
theorem s82lc_uniq_even_of_cover {g r : ℕ} (F₀ : FiniteTypeStructure S₀ g (2 * r) 0)
    (F₁ : FiniteTypeStructure S g (2 * r) 0) {X₀' : ClosedRS.{u}} {pr₀ : X₀'.carrier → F₀.X.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ F₀.P, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₀.P, (pr₀ ⁻¹' {x}).ncard = 1)
    {h : ℕ} (hh : 1 < h) (hX₀' : HasGenus X₀'.carrier h)
    {f₀ : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ}
    (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k) {f : S₀ ≃ₜ S} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    maxDilatationRS f₀ ≤ maxDilatationRS f ∧ (maxDilatationRS f = maxDilatationRS f₀ → ⇑f = ⇑f₀) := by
  obtain ⟨X₁', pr₁, -, -, -, -, f₀', f', qtil, qtil', hc₀, hc, hT', hf', hK', hhom'⟩ :=
    s82lc_lift_teichmullerMap_double_cover F₀ F₁ hpr₀ hf₀ hf hhom
  have hX₁' := hasGenus_of_homeomorph hX₀' f₀'
  obtain ⟨h1, h2⟩ := thm26_2_uniqueness hh hX₀' hX₁' hT' hf' hhom'
  have hK₀ := (teichmullerMap_beltrami hf₀.2).2
  refine ⟨by rw [hK₀, ← hK']; exact h1, fun heq => ?_⟩
  have hfeq := h2 (by rw [hK', heq, hK₀])
  funext s
  obtain ⟨y, hy⟩ := hpr₀.2.1 (F₀.ι s)
  apply F₁.embedding.injective
  rw [← hc y s hy, ← hc₀ y s hy, hfeq]

/-- **Chart data of an unbranched lift.**  For holomorphic maps `π₀ : Y₀ → M₀`, `π₁ : Y₁ → M₁` with `π₁ ∘ Φ = f ∘ π₀`,
`π₁` having holomorphic local inverses, at `z₁` in the domain of `L = localMapExpr Φ a` with `s = π₀(φ_a⁻¹ z₁)`: the
transfers `T = φ_s ∘ π₀ ∘ φ_a⁻¹`, `T₁ = φ_{f s} ∘ π₁ ∘ φ_{Φ a}⁻¹` are local coordinates with
`T₁ ∘ L = (local expression of f at s) ∘ T`, and the pull-backs read `Q_s(T) T'²`, `Q'_{f s}(T₁) T₁'²`. -/
theorem s82lc_gchart_data {Y₀ Y₁ M₀ M₁ : Type*} [TopologicalSpace Y₀] [ChartedSpace ℂ Y₀] [IsManifold 𝓘(ℂ) ω Y₀]
    [TopologicalSpace Y₁] [ChartedSpace ℂ Y₁] [IsManifold 𝓘(ℂ) ω Y₁] [TopologicalSpace M₀] [ChartedSpace ℂ M₀]
    [IsManifold 𝓘(ℂ) ω M₀] [TopologicalSpace M₁] [ChartedSpace ℂ M₁] [IsManifold 𝓘(ℂ) ω M₁]
    {f : M₀ ≃ₜ M₁} {Φ : Y₀ ≃ₜ Y₁} {π₀ : Y₀ → M₀} {π₁ : Y₁ → M₁} (hπ₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₀)
    (hπ₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₁)
    (hπ₁loc : ∀ t, ∃ e : OpenPartialHomeomorph Y₁ M₁, t ∈ e.source ∧ Set.EqOn π₁ e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (hcomm : ∀ t, π₁ (Φ t) = f (π₀ t)) (a : Y₀) {z₁ : ℂ} (hz₁ : z₁ ∈ localMapDomain Φ a) :
    ∃ T T₁ : ℂ → ℂ, AnalyticAt ℂ T z₁ ∧ T z₁ = chartAt ℂ (π₀ ((chartAt ℂ a).symm z₁)) (π₀ ((chartAt ℂ a).symm z₁)) ∧
      AnalyticAt ℂ T₁ (localMapExpr Φ a z₁) ∧ deriv T₁ (localMapExpr Φ a z₁) ≠ 0 ∧
      T₁ (localMapExpr Φ a z₁) = chartAt ℂ (f (π₀ ((chartAt ℂ a).symm z₁))) (f (π₀ ((chartAt ℂ a).symm z₁))) ∧
      ContinuousAt (localMapExpr Φ a) z₁ ∧
      (∀ᶠ z in 𝓝 z₁, T₁ (localMapExpr Φ a z) = localMapExpr f (π₀ ((chartAt ℂ a).symm z₁)) (T z)) ∧
      (∀ Q : M₀ → ℂ → ℂ, IsDiffFamily 2 0 Q → ∀ᶠ z in 𝓝 z₁,
        Q (π₀ ((chartAt ℂ a).symm z)) (chartAt ℂ (π₀ ((chartAt ℂ a).symm z)) (π₀ ((chartAt ℂ a).symm z))) *
          deriv (fun v => chartAt ℂ (π₀ ((chartAt ℂ a).symm z)) (π₀ ((chartAt ℂ a).symm v))) z ^ 2 =
        Q (π₀ ((chartAt ℂ a).symm z₁)) (T z) * deriv T z ^ 2) ∧
      (∀ Q : M₁ → ℂ → ℂ, IsDiffFamily 2 0 Q → ∀ᶠ w in 𝓝 (localMapExpr Φ a z₁),
        Q (π₁ ((chartAt ℂ (Φ a)).symm w)) (chartAt ℂ (π₁ ((chartAt ℂ (Φ a)).symm w)) (π₁ ((chartAt ℂ (Φ a)).symm w))) *
          deriv (fun v => chartAt ℂ (π₁ ((chartAt ℂ (Φ a)).symm w)) (π₁ ((chartAt ℂ (Φ a)).symm v))) w ^ 2 =
        Q (f (π₀ ((chartAt ℂ a).symm z₁))) (T₁ w) * deriv T₁ w ^ 2) := by
  set t := (chartAt ℂ a).symm z₁ with htdef
  set s := π₀ t with hsdef
  set L := localMapExpr Φ a with hL
  have hπ₀d : ∀ t ∈ (univ : Set Y₀), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) π₀ t := fun t _ => hπ₀ t
  have hπ₁d : ∀ t ∈ (univ : Set Y₁), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) π₁ t := fun t _ => hπ₁ t
  have hz₁t : z₁ ∈ (chartAt ℂ a).target := hz₁.1
  have hΦt : Φ t ∈ (chartAt ℂ (Φ a)).source := hz₁.2
  have hLz₁ : L z₁ ∈ (chartAt ℂ (Φ a)).target := (chartAt ℂ (Φ a)).map_source hΦt
  have hLs : (chartAt ℂ (Φ a)).symm (L z₁) = Φ t := (chartAt ℂ (Φ a)).left_inv hΦt
  obtain ⟨hTa, hTev⟩ := s82lc_T_analytic π₀ isOpen_univ hπ₀d a s hz₁t (mem_univ _) (mem_chart_source ℂ s)
  have hLsrc : π₁ ((chartAt ℂ (Φ a)).symm (L z₁)) ∈ (chartAt ℂ (f s)).source := by
    rw [hLs, hcomm]; exact mem_chart_source ℂ _
  obtain ⟨hT₁a, hT₁ev⟩ := s82lc_T_analytic π₁ isOpen_univ hπ₁d (Φ a) (f s) hLz₁ (mem_univ _) hLsrc
  set T₁ : ℂ → ℂ := fun v => chartAt ℂ (f s) (π₁ ((chartAt ℂ (Φ a)).symm v)) with hT₁
  have hT₁z : T₁ (L z₁) = chartAt ℂ (f s) (f s) := by
    show chartAt ℂ (f s) (π₁ ((chartAt ℂ (Φ a)).symm (L z₁))) = _
    rw [hLs, hcomm]
  obtain ⟨e, hte, hepr, -⟩ := hπ₁loc (Φ t)
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
    have e3 : (chartAt ℂ (Φ a)).symm v₁ = (chartAt ℂ (Φ a)).symm v₂ := by
      have := e.injOn (hUsub hv₁).2 (hUsub hv₂).2
      rw [← hepr (hUsub hv₁).2, ← hepr (hUsub hv₂).2] at this
      exact this e1
    exact (chartAt ℂ (Φ a)).symm.injOn h1.1 h2.1 e3
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
    rw [(chartAt ℂ (Φ a)).left_inv hz.2, (chartAt ℂ s).left_inv hzT.2.2, hcomm]
  · intro Q hQ
    filter_upwards [hTev] with z hz
    exact s82lc_raw_local hQ π₀ a s hz.1 (hπ₀ _) hz.2.2
  · intro Q hQ
    filter_upwards [hT₁ev] with w hw
    exact s82lc_raw_local hQ π₁ (Φ a) (f s) hw.1 (hπ₁ _) hw.2.2

/-- **The regular form of an unbranched lift** near the punctured neighbourhood of a point (input of
`s82lc_point_Z`). -/
theorem s82lc_ghloc {Y₀ Y₁ M₀ M₁ : Type*} [TopologicalSpace Y₀] [ChartedSpace ℂ Y₀] [IsManifold 𝓘(ℂ) ω Y₀]
    [TopologicalSpace Y₁] [ChartedSpace ℂ Y₁] [IsManifold 𝓘(ℂ) ω Y₁] [TopologicalSpace M₀] [ChartedSpace ℂ M₀]
    [IsManifold 𝓘(ℂ) ω M₀] [TopologicalSpace M₁] [ChartedSpace ℂ M₁] [IsManifold 𝓘(ℂ) ω M₁]
    {f : M₀ ≃ₜ M₁} {q : M₀ → ℂ → ℂ} {q' : M₁ → ℂ → ℂ} {k : ℝ} (hT : IsTeichmullerMap f q q' k)
    {Φ : Y₀ ≃ₜ Y₁} {π₀ : Y₀ → M₀} {π₁ : Y₁ → M₁} (hπ₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₀)
    (hπ₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₁)
    (hπ₁loc : ∀ t, ∃ e : OpenPartialHomeomorph Y₁ M₁, t ∈ e.source ∧ Set.EqOn π₁ e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (hcomm : ∀ t, π₁ (Φ t) = f (π₀ t)) {Qt : Y₀ → ℂ → ℂ} {φ' : ℂ → ℂ} (p : Y₀)
    (hQt : ∀ z ∈ (chartAt ℂ p).target, Qt p z = q (π₀ ((chartAt ℂ p).symm z))
        (chartAt ℂ (π₀ ((chartAt ℂ p).symm z)) (π₀ ((chartAt ℂ p).symm z))) *
      deriv (fun v => chartAt ℂ (π₀ ((chartAt ℂ p).symm z)) (π₀ ((chartAt ℂ p).symm v))) z ^ 2)
    (hφ' : ∀ w ∈ (chartAt ℂ (Φ p)).target, φ' w = q' (π₁ ((chartAt ℂ (Φ p)).symm w))
        (chartAt ℂ (π₁ ((chartAt ℂ (Φ p)).symm w)) (π₁ ((chartAt ℂ (Φ p)).symm w))) *
      deriv (fun v => chartAt ℂ (π₁ ((chartAt ℂ (Φ p)).symm w)) (π₁ ((chartAt ℂ (Φ p)).symm v))) w ^ 2)
    (hreg : ∀ᶠ z in 𝓝[≠] (chartAt ℂ p p), Qt p z ≠ 0) :
    ∀ᶠ z₁ in 𝓝[≠] (chartAt ℂ p p), ∃ A B : ℂ → ℂ, AnalyticAt ℂ A z₁ ∧
      (∀ᶠ z in 𝓝 z₁, deriv A z ^ 2 = Qt p z) ∧ AnalyticAt ℂ B (localMapExpr Φ p z₁) ∧
      deriv B (localMapExpr Φ p z₁) ≠ 0 ∧ (∀ᶠ w in 𝓝 (localMapExpr Φ p z₁), deriv B w ^ 2 = φ' w) ∧
      ∀ᶠ z in 𝓝 z₁, B (localMapExpr Φ p z) = teichStretch k (A z) := by
  have hqi : IsDiffFamily 2 0 q ∧ ∀ x : M₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hT.initial
  have hqt : IsDiffFamily 2 0 q' ∧ ∀ x : M₁, DifferentiableOn ℂ (q' x) (chartAt ℂ x).target := hT.terminal
  obtain ⟨hcD, -⟩ := s23_h_center Φ p
  have hΩ : localMapDomain Φ p ∈ 𝓝 (chartAt ℂ p p) :=
    (s23_localMapDomain_isOpen Φ.continuous p).mem_nhds hcD
  filter_upwards [hreg, nhdsWithin_le_nhds hΩ] with z₁ h1 h3
  obtain ⟨T, T₁, hTa, hTz, hT₁a, hT₁d, hT₁z, hLc, hrel, hraw, hraw'⟩ :=
    s82lc_gchart_data hπ₀ hπ₁ hπ₁loc hcomm p h3
  set s := π₀ ((chartAt ℂ p).symm z₁) with hs
  have hφ : ∀ᶠ z in 𝓝 z₁, Qt p z = q s (T z) * deriv T z ^ 2 := by
    filter_upwards [(chartAt ℂ p).open_target.mem_nhds h3.1, hraw q hqi.1] with z hz1 hz2
    rw [hQt z hz1, hz2]
  have hLt : localMapExpr Φ p z₁ ∈ (chartAt ℂ (Φ p)).target := (chartAt ℂ (Φ p)).map_source h3.2
  have hφ'' : ∀ᶠ w in 𝓝 (localMapExpr Φ p z₁), φ' w = q' (f s) (T₁ w) * deriv T₁ w ^ 2 := by
    filter_upwards [(chartAt ℂ (Φ p)).open_target.mem_nhds hLt, hraw' q' hqt.1] with w hw1 hw2
    rw [hφ' w hw1, hw2]
  have hregs : IsRegularPoint q s := by
    show q s (chartAt ℂ s s) ≠ 0
    intro h0
    apply h1
    rw [hφ.self_of_nhds, hTz, h0, zero_mul]
  exact s82lc_regular_transport hT s hTa hTz hT₁a hT₁d hT₁z hrel hφ hφ'' hregs

/-- A transfer `φ_x ∘ π ∘ φ_y⁻¹` through a holomorphic map with a local inverse at `φ_y⁻¹ w` has non-vanishing
derivative at `w`. -/
theorem s82lc_gT_deriv_ne {Y M : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] {π' : Y → M}
    (hπ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π') {e : OpenPartialHomeomorph Y M} (heq : Set.EqOn π' e e.source)
    (y : Y) (x : M) {w : ℂ} (hw : w ∈ (chartAt ℂ y).target) (hwe : (chartAt ℂ y).symm w ∈ e.source)
    (hwx : π' ((chartAt ℂ y).symm w) ∈ (chartAt ℂ x).source) :
    deriv (fun v => chartAt ℂ x (π' ((chartAt ℂ y).symm v))) w ≠ 0 := by
  obtain ⟨hTa, hTev⟩ := s82lc_T_analytic π' isOpen_univ (fun t _ => hπ t) y x hw (mem_univ _) hwx
  have he : ∀ᶠ v in 𝓝 w, (chartAt ℂ y).symm v ∈ e.source :=
    ((chartAt ℂ y).continuousAt_symm hw).preimage_mem_nhds (e.open_source.mem_nhds hwe)
  obtain ⟨U, hUsub, hUo, hU⟩ := _root_.mem_nhds_iff.1 ((hTa.eventually_analyticAt.and hTev).and he)
  refine deriv_ne_zero_of_injOn hUo (fun v hv => (hUsub hv).1.1.differentiableAt.differentiableWithinAt)
    ?_ hU
  intro v₁ hv₁ v₂ hv₂ hv
  have h1 := (hUsub hv₁).1.2
  have h2 := (hUsub hv₂).1.2
  have e1 : π' ((chartAt ℂ y).symm v₁) = π' ((chartAt ℂ y).symm v₂) := (chartAt ℂ x).injOn h1.2.2 h2.2.2 hv
  have e3 : (chartAt ℂ y).symm v₁ = (chartAt ℂ y).symm v₂ := by
    have := e.injOn (hUsub hv₁).2 (hUsub hv₂).2
    rw [← heq (hUsub hv₁).2, ← heq (hUsub hv₂).2] at this
    exact this e1
  exact (chartAt ℂ y).symm.injOn h1.1 h2.1 e3

/-- The pull-back `π^* Q` through a holomorphic map, as the indicator of the chart targets, is a holomorphic quadratic
differential. -/
theorem s82lc_graw_hol {Y M : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] {π' : Y → M}
    (hπ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π') {Q : M → ℂ → ℂ} (hQ : IsHolQuadDiff Q) :
    IsHolQuadDiff (fun y => (chartAt ℂ y).target.indicator fun z => Q (π' ((chartAt ℂ y).symm z))
      (chartAt ℂ (π' ((chartAt ℂ y).symm z)) (π' ((chartAt ℂ y).symm z))) *
        deriv (fun v => chartAt ℂ (π' ((chartAt ℂ y).symm z)) (π' ((chartAt ℂ y).symm v))) z ^ 2) := by
  set R : Y → ℂ → ℂ := fun y => (chartAt ℂ y).target.indicator fun z => Q (π' ((chartAt ℂ y).symm z))
      (chartAt ℂ (π' ((chartAt ℂ y).symm z)) (π' ((chartAt ℂ y).symm z))) *
        deriv (fun v => chartAt ℂ (π' ((chartAt ℂ y).symm z)) (π' ((chartAt ℂ y).symm v))) z ^ 2 with hR
  have key : IsDiffFamily 2 0 R ∧ ∀ y : Y, DifferentiableOn ℂ (R y) (chartAt ℂ y).target := by
    refine ⟨⟨fun y z hz => indicator_of_notMem hz _, fun x y z hz hzx => ?_⟩, fun y z hz => ?_⟩
    · rw [zpow_zero, mul_one, zpow_two, ← pow_two]
      obtain ⟨hτt, -, -⟩ := s23_transition_mem hz hzx
      show (chartAt ℂ y).target.indicator _ z = (chartAt ℂ x).target.indicator _ (chartTransition x y z) * _
      rw [indicator_of_mem hz, indicator_of_mem hτt]
      exact s82lc_raw_law Q π' x y hz hzx (hπ _)
    · refine (s82lc_raw_diff hQ π' isOpen_univ (fun t _ => hπ t) y hz (mem_univ _)).congr_of_eventuallyEq
        ?_ |>.differentiableWithinAt
      filter_upwards [(chartAt ℂ y).open_target.mem_nhds hz] with w hw
      exact indicator_of_mem hw _
  exact key

/-- **The lift of a Teichmüller map to an unbranched cover.**  If `π₁ ∘ Φ = f ∘ π₀` for surjective holomorphic maps
with holomorphic local inverses and a quasiconformal homeomorphism `Φ`, then `Φ` is a Teichmüller map for the
pull-backs `π₀^* q`, `π₁^* q'` (with the same `k`). -/
theorem s82lc_teich_unbranched {Y₀ Y₁ M₀ M₁ : Type*} [TopologicalSpace Y₀] [ChartedSpace ℂ Y₀]
    [IsManifold 𝓘(ℂ) ω Y₀] [T2Space Y₀] [ConnectedSpace Y₀] [TopologicalSpace Y₁] [ChartedSpace ℂ Y₁]
    [IsManifold 𝓘(ℂ) ω Y₁] [T2Space Y₁] [ConnectedSpace Y₁] [TopologicalSpace M₀] [ChartedSpace ℂ M₀]
    [IsManifold 𝓘(ℂ) ω M₀] [T2Space M₀] [ConnectedSpace M₀] [TopologicalSpace M₁] [ChartedSpace ℂ M₁]
    [IsManifold 𝓘(ℂ) ω M₁]
    {f : M₀ ≃ₜ M₁} {q : M₀ → ℂ → ℂ} {q' : M₁ → ℂ → ℂ} {k : ℝ} (hT : IsTeichmullerMap f q q' k)
    {Φ : Y₀ ≃ₜ Y₁} (hΦ : IsQCRS Φ) {π₀ : Y₀ → M₀} {π₁ : Y₁ → M₁} (hπ₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₀)
    (hπ₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₁) (hπ₀s : Function.Surjective π₀)
    (hπ₀loc : ∀ t, ∃ e : OpenPartialHomeomorph Y₀ M₀, t ∈ e.source ∧ Set.EqOn π₀ e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (hπ₁loc : ∀ t, ∃ e : OpenPartialHomeomorph Y₁ M₁, t ∈ e.source ∧ Set.EqOn π₁ e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (hcomm : ∀ t, π₁ (Φ t) = f (π₀ t)) :
    IsTeichmullerMap Φ
      (fun y => (chartAt ℂ y).target.indicator fun z => q (π₀ ((chartAt ℂ y).symm z))
        (chartAt ℂ (π₀ ((chartAt ℂ y).symm z)) (π₀ ((chartAt ℂ y).symm z))) *
          deriv (fun v => chartAt ℂ (π₀ ((chartAt ℂ y).symm z)) (π₀ ((chartAt ℂ y).symm v))) z ^ 2)
      (fun y => (chartAt ℂ y).target.indicator fun z => q' (π₁ ((chartAt ℂ y).symm z))
        (chartAt ℂ (π₁ ((chartAt ℂ y).symm z)) (π₁ ((chartAt ℂ y).symm z))) *
          deriv (fun v => chartAt ℂ (π₁ ((chartAt ℂ y).symm z)) (π₁ ((chartAt ℂ y).symm v))) z ^ 2) k := by
  have hk₀ := hT.k_nonneg
  have hk := hT.k_lt_one
  have hqi : IsDiffFamily 2 0 q ∧ ∀ x : M₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hT.initial
  set R₀ : Y₀ → ℂ → ℂ := fun y => (chartAt ℂ y).target.indicator fun z => q (π₀ ((chartAt ℂ y).symm z))
      (chartAt ℂ (π₀ ((chartAt ℂ y).symm z)) (π₀ ((chartAt ℂ y).symm z))) *
        deriv (fun v => chartAt ℂ (π₀ ((chartAt ℂ y).symm z)) (π₀ ((chartAt ℂ y).symm v))) z ^ 2 with hR₀
  set R₁ : Y₁ → ℂ → ℂ := fun y => (chartAt ℂ y).target.indicator fun z => q' (π₁ ((chartAt ℂ y).symm z))
      (chartAt ℂ (π₁ ((chartAt ℂ y).symm z)) (π₁ ((chartAt ℂ y).symm z))) *
        deriv (fun v => chartAt ℂ (π₁ ((chartAt ℂ y).symm z)) (π₁ ((chartAt ℂ y).symm v))) z ^ 2 with hR₁
  have hR₀h : IsHolQuadDiff R₀ := s82lc_graw_hol hπ₀ hT.initial
  have hR₁h : IsHolQuadDiff R₁ := s82lc_graw_hol hπ₁ hT.terminal
  have hR₀e : ∀ y, ∀ z ∈ (chartAt ℂ y).target, R₀ y z = q (π₀ ((chartAt ℂ y).symm z))
      (chartAt ℂ (π₀ ((chartAt ℂ y).symm z)) (π₀ ((chartAt ℂ y).symm z))) *
        deriv (fun v => chartAt ℂ (π₀ ((chartAt ℂ y).symm z)) (π₀ ((chartAt ℂ y).symm v))) z ^ 2 :=
    fun y z hz => indicator_of_mem hz _
  have hR₁e : ∀ y, ∀ z ∈ (chartAt ℂ y).target, R₁ y z = q' (π₁ ((chartAt ℂ y).symm z))
      (chartAt ℂ (π₁ ((chartAt ℂ y).symm z)) (π₁ ((chartAt ℂ y).symm z))) *
        deriv (fun v => chartAt ℂ (π₁ ((chartAt ℂ y).symm z)) (π₁ ((chartAt ℂ y).symm v))) z ^ 2 :=
    fun y z hz => indicator_of_mem hz _
  -- the lifted initial differential is not zero
  have hR₀ne : R₀ ≠ 0 := by
    have : T1Space M₀ := inferInstance
    obtain ⟨s₀, hs₀⟩ :=
      (s26u_frequently_regular hT.initial hT.initial_ne (π₀ (Classical.arbitrary Y₀))).exists
    obtain ⟨y, hy⟩ := hπ₀s s₀
    have hcyt : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
    have hyy : (chartAt ℂ y).symm (chartAt ℂ y y) = y := (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
    obtain ⟨e, hye, hee, -⟩ := hπ₀loc y
    have hsrc : π₀ ((chartAt ℂ y).symm (chartAt ℂ y y)) ∈ (chartAt ℂ s₀).source := by
      rw [hyy, hy]; exact mem_chart_source ℂ s₀
    have hD := s82lc_gT_deriv_ne hπ₀ hee y s₀ hcyt (by rw [hyy]; exact hye) hsrc
    intro h0
    have hz : R₀ y (chartAt ℂ y y) = 0 := by rw [h0]; rfl
    rw [hR₀e y _ hcyt, s82lc_raw_local hqi.1 π₀ y s₀ hcyt (hπ₀ _) hsrc, hyy, hy] at hz
    exact mul_ne_zero hs₀ (pow_ne_zero 2 hD) hz
  -- the terminal natural parameter at every point
  have hpt : ∀ (p : Y₀) (M : ℕ) (ζ : ℂ → ℂ), IsNaturalParameterAtZero R₀ p M ζ →
      ∃ Z : ℂ → ℂ, IsNaturalParameterAtZero R₁ (Φ p) M Z ∧
        ∀ᶠ z in 𝓝 (chartAt ℂ p p), Z (localMapExpr Φ p z) = teichStretchZero k M (ζ z) := by
    intro p M ζ hζ
    obtain ⟨hζa, hζ0, hζd, hζf⟩ := hζ
    have hc2 : ((M + 2 : ℂ) / 2) ≠ 0 :=
      div_ne_zero (by exact_mod_cast (show M + 2 ≠ 0 by omega)) two_ne_zero
    have hreg : ∀ᶠ z in 𝓝[≠] (chartAt ℂ p p), R₀ p z ≠ 0 := by
      obtain ⟨V, hVo, hcV, -, hVi⟩ := s26u_exists_open_injOn hζa hζd
      filter_upwards [nhdsWithin_le_nhds hζf, nhdsWithin_le_nhds (hVo.mem_nhds hcV),
        nhdsWithin_le_nhds (hζa.deriv.continuousAt.eventually_ne hζd), self_mem_nhdsWithin]
        with z h1 h2 h3 h4
      rw [h1]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hc2)
        (pow_ne_zero _ fun h => h4 (hVi h2 hcV (h.trans hζ0.symm)))) (pow_ne_zero _ h3)
    have hl := s82lc_ghloc hT hπ₀ hπ₁ hπ₁loc hcomm (Qt := R₀) (φ' := R₁ (Φ p)) p (hR₀e p)
      (hR₁e (Φ p)) hreg
    obtain ⟨Z, hZa, hZ0, hZd, hZf, hrel⟩ := s82lc_point_Z Φ hk₀ hk p hζa hζ0 hζd hζf hl
    have hqt' : IsDiffFamily 2 0 R₁ ∧ ∀ x, DifferentiableOn ℂ (R₁ x) (chartAt ℂ x).target := hR₁h
    have hc't : chartAt ℂ (Φ p) (Φ p) ∈ (chartAt ℂ (Φ p)).target :=
      (chartAt ℂ (Φ p)).map_source (mem_chart_source ℂ _)
    have hqa : AnalyticAt ℂ (R₁ (Φ p)) (chartAt ℂ (Φ p) (Φ p)) :=
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
  refine ⟨hΦ, hR₀h, hR₀ne, hR₁h, hk₀, hk, fun p hp => ?_, fun p n hn => ?_⟩
  · obtain ⟨M, ζ, Zd, hD⟩ := s26d_a_data_exists hR₀h hR₀ne p
    have hM : M = 0 := hD.regular_iff.1 hp
    subst hM
    obtain ⟨Z, hZ, hrel⟩ := hpt p 0 ζ hD.natural
    obtain ⟨hζa, hζ0, hζd, hζf⟩ := hD.natural
    obtain ⟨hZa, hZ0, hZd, hZf⟩ := hZ
    refine ⟨?_, ζ, Z, ⟨hζa, hζ0, hζd, ?_⟩, ⟨hZa, hZ0, hZd, ?_⟩, ?_⟩
    · show R₁ (Φ p) (chartAt ℂ (Φ p) (Φ p)) ≠ 0
      rw [hZf.self_of_nhds]
      norm_num
      exact hZd
    · filter_upwards [hζf] with z hz
      rw [hz]; norm_num
    · filter_upwards [hZf] with z hz
      rw [hz]; norm_num
    · rw [← s26d_b_teichStretchZero_zero]
      exact hrel
  · obtain ⟨M, ζ, Zd, hD⟩ := s26d_a_data_exists hR₀h hR₀ne p
    have hMn : M = n := by
      have h1 : meromorphicOrderAt (R₀ p) (chartAt ℂ p p) = (M : ℤ) := hD.order
      have h2 : meromorphicOrderAt (R₀ p) (chartAt ℂ p p) = (n : ℤ) := hn
      rw [h1] at h2
      exact_mod_cast WithTop.coe_injective h2
    subst hMn
    obtain ⟨Z, ⟨hZa, hZ0, hZd, hZf⟩, -⟩ := hpt p M ζ hD.natural
    have hqt' : IsDiffFamily 2 0 R₁ ∧ ∀ x, DifferentiableOn ℂ (R₁ x) (chartAt ℂ x).target := hR₁h
    have hc't : chartAt ℂ (Φ p) (Φ p) ∈ (chartAt ℂ (Φ p)).target :=
      (chartAt ℂ (Φ p)).map_source (mem_chart_source ℂ _)
    exact s82lc_order_of_form hZa hZ0 hZd hZf
      ((hqt'.2 (Φ p)).analyticAt ((chartAt ℂ (Φ p)).open_target.mem_nhds hc't))

section GLiftQC

variable {Y₀ Y₁ M₀ M₁ : Type*} [TopologicalSpace Y₀] [ChartedSpace ℂ Y₀] [IsManifold 𝓘(ℂ) ω Y₀]
  [TopologicalSpace Y₁] [ChartedSpace ℂ Y₁] [IsManifold 𝓘(ℂ) ω Y₁] [TopologicalSpace M₀] [ChartedSpace ℂ M₀]
  [IsManifold 𝓘(ℂ) ω M₀] [TopologicalSpace M₁] [ChartedSpace ℂ M₁] [IsManifold 𝓘(ℂ) ω M₁]

/-- `K`-quasiconformality lifts to an unbranched lift `Φ` (`π₁ ∘ Φ = f ∘ π₀`, `π₀`, `π₁` with holomorphic local
inverses): near each point `Φ` is a conformal conjugate of `f`. -/
theorem s82lc_glift_isKQCRS {f : M₀ ≃ₜ M₁} {Φ : Y₀ ≃ₜ Y₁} {π₀ : Y₀ → M₀} {π₁ : Y₁ → M₁}
    (hπ₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₀)
    (hπ₀loc : ∀ t, ∃ e : OpenPartialHomeomorph Y₀ M₀, t ∈ e.source ∧ Set.EqOn π₀ e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (hπ₁loc : ∀ t, ∃ e : OpenPartialHomeomorph Y₁ M₁, t ∈ e.source ∧ Set.EqOn π₁ e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (hcomm : ∀ t, π₁ (Φ t) = f (π₀ t)) {K : ℝ} (hfK : IsKQCRS f K) : IsKQCRS Φ K := by
  refine ⟨hfK.1, fun y => ?_⟩
  refine s82lc_isKQC_of_local (L := ∅) (s23_localMapDomain_isOpen Φ.continuous y) hfK.1
    (s82lc_localMapExpr_continuousOn Φ.continuous y) (s23_c1_injOn_localMapExpr Φ.injective y)
    finite_empty fun z hz => ?_
  set m := (chartAt ℂ y).symm z
  obtain ⟨σ, hmσ, hσeq, -⟩ := hπ₀loc m
  obtain ⟨τ, hmτ, hτeq, hτd⟩ := hπ₁loc (Φ m)
  have hσd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ σ.source := fun x hx =>
    (hπ₀ x).mdifferentiableWithinAt.congr (fun w hw => (hσeq hw).symm) (hσeq hx).symm
  refine s82lc_conj_data Φ.continuous f.continuous (fun b => hfK.2 b) hσd hτd hmσ hmτ ?_ y hz.1 rfl
  intro x hx hxτ
  rw [← hτeq hxτ, ← hσeq hx, hcomm]

/-- `K`-quasiconformality descends from an unbranched lift `Φ` to `f` when `π₀` is surjective. -/
theorem s82lc_isKQCRS_of_glift {f : M₀ ≃ₜ M₁} {Φ : Y₀ ≃ₜ Y₁} {π₀ : Y₀ → M₀} {π₁ : Y₁ → M₁}
    (hπ₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₁) (hπ₀s : Function.Surjective π₀)
    (hπ₀loc : ∀ t, ∃ e : OpenPartialHomeomorph Y₀ M₀, t ∈ e.source ∧ Set.EqOn π₀ e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (hπ₁loc : ∀ t, ∃ e : OpenPartialHomeomorph Y₁ M₁, t ∈ e.source ∧ Set.EqOn π₁ e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (hcomm : ∀ t, π₁ (Φ t) = f (π₀ t)) {K : ℝ} (hΦK : IsKQCRS Φ K) : IsKQCRS f K := by
  refine ⟨hΦK.1, fun s₁ => ?_⟩
  refine s82lc_isKQC_of_local (L := ∅) (s23_localMapDomain_isOpen f.continuous s₁) hΦK.1
    (s82lc_localMapExpr_continuousOn f.continuous s₁) (s23_c1_injOn_localMapExpr f.injective s₁)
    finite_empty fun z hz => ?_
  set s := (chartAt ℂ s₁).symm z
  obtain ⟨t, ht⟩ := hπ₀s s
  obtain ⟨e₀, hte₀, heq₀, he₀'⟩ := hπ₀loc t
  obtain ⟨e₁, hte₁, heq₁, -⟩ := hπ₁loc (Φ t)
  have hσ₀o : IsOpen (e₀.symm.source ∩ e₀.symm ⁻¹' (Φ ⁻¹' e₁.source)) :=
    e₀.symm.isOpen_inter_preimage (e₁.open_source.preimage Φ.continuous)
  set σ := e₀.symm.restrOpen _ hσ₀o with hσ
  set τ := e₁.symm with hτ
  have he₀t : e₀ t = s := by rw [← heq₀ hte₀]; exact ht
  have hsσ : s ∈ σ.source := by
    refine ⟨by rw [← he₀t]; exact e₀.map_source hte₀, by rw [← he₀t]; exact e₀.map_source hte₀, ?_⟩
    show Φ (e₀.symm s) ∈ e₁.source
    rw [← he₀t, e₀.left_inv hte₀]; exact hte₁
  have hfsτ : f s ∈ τ.source := by
    show f s ∈ e₁.target
    rw [← ht, ← hcomm, heq₁ hte₁]; exact e₁.map_source hte₁
  have hσd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ σ.source := fun x hx => (he₀' x hx.1).mono fun w hw => hw.1
  have hτd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) τ.symm τ.target := fun u hu =>
    (hπ₁ u).mdifferentiableWithinAt.congr (fun w hw => (heq₁ hw).symm) (heq₁ hu).symm
  refine s82lc_conj_data f.continuous Φ.continuous (fun b => hΦK.2 b) hσd hτd hsσ hfsτ ?_ s₁ hz.1 rfl
  intro x hx _
  have hx1 : Φ (σ x) ∈ e₁.source := hx.2.2
  have hσx : σ x = e₀.symm x := rfl
  have hπσ : π₀ (σ x) = x := by
    rw [hσx, heq₀ (e₀.map_target hx.1)]
    exact e₀.right_inv hx.1
  have h2 : f x = e₁ (Φ (σ x)) := by rw [← heq₁ hx1, hcomm, hπσ]
  show e₁.symm (f x) = Φ (σ x)
  rw [h2, e₁.left_inv hx1]

/-- **The dilatation of an unbranched lift**: `Φ` is quasiconformal with `K[Φ] = K[f]`. -/
theorem s82lc_glift_qc {f : M₀ ≃ₜ M₁} (hf : IsQCRS f) {Φ : Y₀ ≃ₜ Y₁} {π₀ : Y₀ → M₀} {π₁ : Y₁ → M₁}
    (hπ₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₀) (hπ₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₁)
    (hπ₀s : Function.Surjective π₀)
    (hπ₀loc : ∀ t, ∃ e : OpenPartialHomeomorph Y₀ M₀, t ∈ e.source ∧ Set.EqOn π₀ e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (hπ₁loc : ∀ t, ∃ e : OpenPartialHomeomorph Y₁ M₁, t ∈ e.source ∧ Set.EqOn π₁ e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (hcomm : ∀ t, π₁ (Φ t) = f (π₀ t)) [Nonempty Y₀] [Nonempty M₀] :
    IsQCRS Φ ∧ maxDilatationRS Φ = maxDilatationRS f := by
  obtain ⟨K, hK⟩ := hf
  have hΦqc : IsQCRS Φ := ⟨K, s82lc_glift_isKQCRS hπ₀ hπ₀loc hπ₁loc hcomm hK⟩
  refine ⟨hΦqc, le_antisymm ?_ ?_⟩
  · have h1 : 1 ≤ maxDilatationRS f := s29_m_one_le_maxDilatationRS ⟨K, hK⟩
    have hfin : maxDilatationRS f ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (maxDilatationRS_le hK)
    have hK' : 1 ≤ (maxDilatationRS f).toReal := by
      have := ENNReal.toReal_mono hfin h1
      simpa using this
    have hfK := s82lc_isKQCRS_of_maxDil ⟨K, hK⟩ hK' (by rw [ENNReal.ofReal_toReal hfin])
    have := maxDilatationRS_le (s82lc_glift_isKQCRS hπ₀ hπ₀loc hπ₁loc hcomm hfK)
    rwa [ENNReal.ofReal_toReal hfin] at this
  · have h1 : 1 ≤ maxDilatationRS Φ := s29_m_one_le_maxDilatationRS hΦqc
    obtain ⟨KΦ, hKΦ⟩ := hΦqc
    have hfin : maxDilatationRS Φ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (maxDilatationRS_le hKΦ)
    have hK' : 1 ≤ (maxDilatationRS Φ).toReal := by
      have := ENNReal.toReal_mono hfin h1
      simpa using this
    have hΦK := s82lc_isKQCRS_of_maxDil ⟨KΦ, hKΦ⟩ hK' (by rw [ENNReal.ofReal_toReal hfin])
    have := maxDilatationRS_le (s82lc_isKQCRS_of_glift hπ₁ hπ₀s hπ₀loc hπ₁loc hcomm hΦK)
    rwa [ENNReal.ofReal_toReal hfin] at this

end GLiftQC

/-- **The lift on the punctured cover.**  Over `X ∖ P`, where `pr` is a covering map, a homeomorphism `h` of `X`
preserving `P` and homotopic to the identity off `P` (by `K`, avoiding `P`) lifts to a homeomorphism of
`pr⁻¹(X ∖ P)`, homotopic to the identity by the lifted homotopy (`s82lc_lift_homotopy`, inverse by path-lift
uniqueness, as in `s82lc_lift`). -/
theorem s82lc_lift_punct {Y X : ClosedRS.{u}} {P : Finset X.carrier} {pr : Y.carrier → X.carrier}
    (hprc : Continuous pr) (hcov : IsCoveringMapOn pr (↑P)ᶜ)
    (h : X.carrier ≃ₜ X.carrier) (hP : h '' ↑P = ↑P)
    (K : C(unitInterval × ((↑P)ᶜ : Set X.carrier), X.carrier)) (hK0 : ∀ x, K (0, x) = x)
    (hK1 : ∀ x, K (1, x) = h x) (hKP : ∀ t x, K (t, x) ∉ P) :
    ∃ F : (pr ⁻¹' (↑P)ᶜ : Set Y.carrier) ≃ₜ (pr ⁻¹' (↑P)ᶜ : Set Y.carrier), (∀ y, pr (F y) = h (pr y)) ∧
      ∃ L : C(unitInterval × (pr ⁻¹' (↑P)ᶜ : Set Y.carrier), (pr ⁻¹' (↑P)ᶜ : Set Y.carrier)),
        (∀ y, L (0, y) = y) ∧ ∀ y, L (1, y) = F y := by
  classical
  set Yc := (pr ⁻¹' (↑P : Set X.carrier)ᶜ : Set Y.carrier) with hYc
  have hinvc : ∀ x : X.carrier, x ∉ P → h.symm x ∉ P := fun x hx hx' => by
    have : h (h.symm x) ∈ h '' ↑P := mem_image_of_mem _ hx'
    rw [hP, h.apply_symm_apply] at this
    exact hx this
  set M₁ : C(unitInterval × Yc, X.carrier) :=
    ⟨fun ty => K (ty.1, ⟨pr ty.2, ty.2.2⟩), K.continuous.comp (continuous_fst.prodMk
      ((hprc.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _))⟩ with hM₁
  obtain ⟨H₁, hH₁, hH₁0⟩ := s82lc_lift_homotopy hcov M₁ (fun t y => hKP _ _) (ContinuousMap.id Yc)
    (fun y => hK0 _)
  set M₂ : C(unitInterval × Yc, X.carrier) :=
    ⟨fun ty => K (unitInterval.symm ty.1, ⟨h.symm (pr ty.2), hinvc _ ty.2.2⟩),
      K.continuous.comp ((unitInterval.continuous_symm.comp continuous_fst).prodMk
        ((h.symm.continuous.comp (hprc.comp (continuous_subtype_val.comp continuous_snd))).subtype_mk
          _))⟩ with hM₂
  obtain ⟨H₂, hH₂, hH₂0⟩ := s82lc_lift_homotopy hcov M₂ (fun t y => hKP _ _) (ContinuousMap.id Yc)
    (fun y => by
      show K (unitInterval.symm 0, _) = pr y
      rw [unitInterval.symm_zero, hK1, h.apply_symm_apply])
  set F₀ : Yc → Yc := fun y => H₁ (1, y) with hF₀
  set G₀ : Yc → Yc := fun y => H₂ (1, y) with hG₀
  have hF₀c : Continuous F₀ := H₁.continuous.comp (continuous_const.prodMk continuous_id)
  have hG₀c : Continuous G₀ := H₂.continuous.comp (continuous_const.prodMk continuous_id)
  have hF₀p : ∀ y, pr (F₀ y) = h (pr y) := fun y => by
    show pr (H₁ (1, y)) = _
    rw [hH₁]
    exact hK1 _
  have hG₀p : ∀ y, pr (G₀ y) = h.symm (pr y) := fun y => by
    show pr (H₂ (1, y)) = _
    rw [hH₂]
    show K (unitInterval.symm 1, _) = _
    rw [unitInterval.symm_one, hK0]
  have hGF : ∀ y, G₀ (F₀ y) = y := by
    intro y
    have := s82lc_path_lift_unique hcov (γ₁ := fun t => H₂ (t, F₀ y)) (γ₂ := fun t => H₁ (unitInterval.symm t, y))
      (H₂.continuous.comp (continuous_id.prodMk continuous_const))
      (H₁.continuous.comp (unitInterval.continuous_symm.prodMk continuous_const))
      (fun t => by
        rw [hH₂, hH₁]
        exact congrArg (fun x : ((↑P : Set X.carrier)ᶜ : Set X.carrier) => K (unitInterval.symm t, x))
          (Subtype.ext (show h.symm (pr (F₀ y)) = pr y by rw [hF₀p, h.symm_apply_apply])))
      (by
        show H₂ (0, F₀ y) = H₁ (unitInterval.symm 0, y)
        rw [hH₂0, unitInterval.symm_zero]
        rfl)
    simp only [unitInterval.symm_one] at this
    rw [hH₁0] at this
    exact this
  have hFG : ∀ w, F₀ (G₀ w) = w := by
    intro w
    have := s82lc_path_lift_unique hcov (γ₁ := fun t => H₁ (t, G₀ w)) (γ₂ := fun t => H₂ (unitInterval.symm t, w))
      (H₁.continuous.comp (continuous_id.prodMk continuous_const))
      (H₂.continuous.comp (unitInterval.continuous_symm.prodMk continuous_const))
      (fun t => by
        rw [hH₁, hH₂]
        show K (t, _) = K (unitInterval.symm (unitInterval.symm t), _)
        rw [unitInterval.symm_symm]
        exact congrArg (fun x : ((↑P : Set X.carrier)ᶜ : Set X.carrier) => K (t, x))
          (Subtype.ext (show pr (G₀ w) = h.symm (pr w) from hG₀p w)))
      (by
        show H₁ (0, G₀ w) = H₂ (unitInterval.symm 0, w)
        rw [hH₁0, unitInterval.symm_zero]
        rfl)
    simp only [unitInterval.symm_one] at this
    rw [hH₂0] at this
    exact this
  refine ⟨⟨⟨F₀, G₀, hGF, hFG⟩, hF₀c, hG₀c⟩, hF₀p, H₁, fun y => ?_, fun y => rfl⟩
  rw [hH₁0]; rfl

/-- The chart expression of a holomorphic map with finite nonempty fibres is not locally constant, in any chart at
the point. -/
theorem s82lc_not_locally_const' {Y X : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [T2Space Y] [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {pr : Y → X}
    (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr) (hfib : ∀ x, (pr ⁻¹' {x}).ncard ≠ 0) (x : Y) {y : Y}
    (hy : y ∈ (chartAt ℂ x).source) :
    ¬ ∀ᶠ z in 𝓝 (chartAt ℂ x y), chartAt ℂ (pr y) (pr ((chartAt ℂ x).symm z)) = chartAt ℂ (pr y) (pr y) := by
  intro hev
  set φ := chartAt ℂ x
  set v := chartAt ℂ (pr y)
  have hφy : φ y ∈ φ.target := φ.map_source hy
  have hcont : ContinuousAt (fun z => pr (φ.symm z)) (φ y) :=
    hpr.continuous.continuousAt.comp (φ.continuousAt_symm hφy)
  have hsrc : ∀ᶠ z in 𝓝 (φ y), z ∈ φ.target ∧ pr (φ.symm z) ∈ v.source := by
    refine (show ∀ᶠ z in 𝓝 (φ y), z ∈ φ.target from φ.open_target.mem_nhds hφy).and
      (hcont.preimage_mem_nhds ?_)
    rw [show pr (φ.symm (φ y)) = pr y by rw [φ.left_inv hy]]
    exact v.open_source.mem_nhds (mem_chart_source ℂ _)
  obtain ⟨O, hOsub, hOo, hcO⟩ := _root_.mem_nhds_iff.1 (hev.and hsrc)
  have hconst : φ.source ∩ φ ⁻¹' O ⊆ pr ⁻¹' {pr y} := by
    intro t ht
    have hz := hOsub ht.2
    have h1 : v (pr (φ.symm (φ t))) = v (pr y) := hz.1
    rw [φ.left_inv ht.1] at h1
    have h2 : pr t ∈ v.source := by
      have := hz.2.2
      rwa [φ.left_inv ht.1] at this
    exact v.injOn h2 (mem_chart_source ℂ _) h1
  have hinf : (φ.source ∩ φ ⁻¹' O).Infinite :=
    s82lc_open_infinite (φ.isOpen_inter_preimage hOo) ⟨hy, hcO⟩
  exact hfib (pr y) (Set.Infinite.ncard (hinf.mono hconst))

/-- **Pull-back of a simple pole.**  If `Q = c/(u - u₀) + r` off `u₀` and `F` is analytic, non-constant, with
`F(z₀) = u₀`, then `Q(F) F'²` is `c'/(z - z₀) + r'` off `z₀` with `r'` analytic (`c' = 0` when `F` is branched):
with `F = u₀ + ψ^e`, `Q(F) F'² = c e² ψ^{e-2} ψ'² + r(F) F'²`, and for `e = 1` the first term is `G/(z - z₀)`,
`G = c ψ'²/dslope ψ`. -/
theorem s82lc_pole_pullback {F Q r φ : ℂ → ℂ} {z₀ u₀ c : ℂ} (hF : AnalyticAt ℂ F z₀) (hF0 : F z₀ = u₀)
    (hnc : ¬ ∀ᶠ z in 𝓝 z₀, F z = F z₀) (hr : AnalyticAt ℂ r u₀)
    (hQ : ∀ᶠ u in 𝓝[≠] u₀, Q u = c / (u - u₀) + r u)
    (hφ : ∀ᶠ z in 𝓝[≠] z₀, φ z = Q (F z) * deriv F z ^ 2) :
    ∃ (c' : ℂ) (r' : ℂ → ℂ), AnalyticAt ℂ r' z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, φ z = c' / (z - z₀) + r' z := by
  obtain ⟨e, ψ, he, hψ, hψ0, hψ', hFe⟩ := s82lc_normal_form hF hnc
  rw [hF0] at hFe
  obtain ⟨V, hVo, hz₀V, -, hVi⟩ := s26u_exists_open_injOn hψ hψ'
  have hψne : ∀ᶠ z in 𝓝[≠] z₀, ψ z ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (hVo.mem_nhds hz₀V), self_mem_nhdsWithin] with z hz hz0 h
    exact hz0 (hVi hz hz₀V (h.trans hψ0.symm))
  have hFt : Tendsto F (𝓝[≠] z₀) (𝓝[≠] u₀) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · rw [← hF0]; exact hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [nhdsWithin_le_nhds hFe, hψne] with z h1 h2 h3
      have h3' : F z = u₀ := h3
      rw [h1] at h3'
      exact pow_ne_zero e h2 (by linear_combination h3')
  have hderF : ∀ᶠ z in 𝓝 z₀, deriv F z = (e : ℂ) * ψ z ^ (e - 1) * deriv ψ z := by
    filter_upwards [hFe.eventually_nhds, hψ.eventually_analyticAt] with z hz hza
    rw [Filter.EventuallyEq.deriv_eq hz]
    have h2 : HasDerivAt (fun x => u₀ + ψ x ^ e) (((e : ℕ) : ℂ) * ψ z ^ (e - 1) * deriv ψ z) z :=
      (hza.differentiableAt.hasDerivAt.pow e).const_add u₀
    exact h2.deriv
  have hFr : AnalyticAt ℂ (fun z => r (F z)) z₀ := AnalyticAt.comp_of_eq hr hF hF0
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rcases e' with _ | e''
  · -- `e = 1`: a simple pole with residue term `G(z₀)`
    set D := dslope ψ z₀ with hD
    have hDa : AnalyticAt ℂ D z₀ := analyticAt_dslope hψ
    have hD0 : D z₀ ≠ 0 := by rw [hD, dslope_same]; exact hψ'
    have hψD : ∀ z, ψ z = (z - z₀) * D z := by
      intro z
      have := sub_smul_dslope ψ z₀ z
      rw [hψ0, sub_zero, smul_eq_mul] at this
      exact this.symm
    set G : ℂ → ℂ := fun z => c * deriv ψ z ^ 2 / D z with hG
    have hGa : AnalyticAt ℂ G z₀ := (analyticAt_const.mul (hψ.deriv.pow 2)).div hDa hD0
    refine ⟨G z₀, fun z => dslope G z₀ z + r (F z) * deriv F z ^ 2,
      (analyticAt_dslope hGa).add (hFr.mul ((hF.deriv).pow 2)), ?_⟩
    filter_upwards [hφ, hFt.eventually hQ, nhdsWithin_le_nhds hFe, nhdsWithin_le_nhds hderF, hψne,
      self_mem_nhdsWithin] with z h1 h2 h3 h4 h5 h6
    have hz0 : z - z₀ ≠ 0 := sub_ne_zero.2 h6
    have hDz : D z ≠ 0 := fun h => h5 (by rw [hψD z, h, mul_zero])
    have hGz : G z = G z₀ + (z - z₀) * dslope G z₀ z := by
      have := sub_smul_dslope G z₀ z
      rw [smul_eq_mul] at this
      linear_combination -this
    have hdz : deriv F z = deriv ψ z := by rw [h4]; simp
    have hFz : F z - u₀ = ψ z := by rw [h3]; ring
    have key : c / ψ z * deriv ψ z ^ 2 = G z₀ / (z - z₀) + dslope G z₀ z := by
      calc c / ψ z * deriv ψ z ^ 2 = G z / (z - z₀) := by
            rw [hψD z]; simp only [hG]; field_simp
        _ = G z₀ / (z - z₀) + dslope G z₀ z := by rw [hGz]; field_simp
    rw [h1, h2, hFz, hdz, add_mul, key]
    ring
  · -- `e ≥ 2`: removable
    refine ⟨0, fun z => c * ((e'' + 2 : ℕ) : ℂ) ^ 2 * ψ z ^ e'' * deriv ψ z ^ 2 + r (F z) * deriv F z ^ 2,
      ((analyticAt_const.mul ((hψ.pow _))).mul (hψ.deriv.pow 2)).add (hFr.mul ((hF.deriv).pow 2)), ?_⟩
    filter_upwards [hφ, hFt.eventually hQ, nhdsWithin_le_nhds hFe, nhdsWithin_le_nhds hderF, hψne]
      with z h1 h2 h3 h4 h5
    have hdz : deriv F z = ((e'' + 2 : ℕ) : ℂ) * ψ z ^ (e'' + 1) * deriv ψ z := by
      rw [h4, show e'' + 1 + 1 - 1 = e'' + 1 by omega]
    have hFz : F z - u₀ = ψ z ^ (e'' + 2) := by rw [h3]; ring
    rw [h1, h2, hFz, hdz, zero_div, zero_add]
    field_simp
    ring

/-- **Pull-back through a composite.**  The pull-back of `Q` through `b ∘ a`, read in charts, is the pull-back
through `b` at the image point, times the square of the derivative of the transfer of `a`. -/
theorem s82lc_raw_comp {Y X M : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] {a : Y → X} {b : X → M} (ha : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a) (Q : M → ℂ → ℂ)
    (t : Y) {z : ℂ} (hz : z ∈ (chartAt ℂ t).target)
    (hb : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) b (a ((chartAt ℂ t).symm z))) :
    Q (b (a ((chartAt ℂ t).symm z))) (chartAt ℂ (b (a ((chartAt ℂ t).symm z))) (b (a ((chartAt ℂ t).symm z)))) *
        deriv (fun v => chartAt ℂ (b (a ((chartAt ℂ t).symm z))) (b (a ((chartAt ℂ t).symm v)))) z ^ 2 =
      Q (b (a ((chartAt ℂ t).symm z))) (chartAt ℂ (b (a ((chartAt ℂ t).symm z))) (b (a ((chartAt ℂ t).symm z)))) *
        deriv (fun v => chartAt ℂ (b (a ((chartAt ℂ t).symm z)))
          (b ((chartAt ℂ (a ((chartAt ℂ t).symm z))).symm v))) (chartAt ℂ (a ((chartAt ℂ t).symm z))
            (a ((chartAt ℂ t).symm z))) ^ 2 *
        deriv (fun v => chartAt ℂ (a ((chartAt ℂ t).symm z)) (a ((chartAt ℂ t).symm v))) z ^ 2 := by
  set x := a ((chartAt ℂ t).symm z) with hx
  set s := b x with hs
  have hxt : chartAt ℂ x x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  have hxx : (chartAt ℂ x).symm (chartAt ℂ x x) = x := (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have hAd : DifferentiableAt ℂ (fun v => chartAt ℂ s (b ((chartAt ℂ x).symm v))) (chartAt ℂ x x) :=
    s82lc_raw_T_diff b x s hxt (by rw [hxx]; exact hb) (by rw [hxx]; exact mem_chart_source ℂ s)
  have hBd : DifferentiableAt ℂ (fun v => chartAt ℂ x (a ((chartAt ℂ t).symm v))) z :=
    s82lc_raw_T_diff a t x hz (ha _) (mem_chart_source ℂ x)
  have hcont : ContinuousAt (fun v => a ((chartAt ℂ t).symm v)) z :=
    ha.continuous.continuousAt.comp ((chartAt ℂ t).continuousAt_symm hz)
  have hev : (fun v => chartAt ℂ s (b (a ((chartAt ℂ t).symm v)))) =ᶠ[𝓝 z]
      (fun v => chartAt ℂ s (b ((chartAt ℂ x).symm v))) ∘
        fun v => chartAt ℂ x (a ((chartAt ℂ t).symm v)) := by
    filter_upwards [hcont.preimage_mem_nhds ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))]
      with v hv
    show chartAt ℂ s (b (a ((chartAt ℂ t).symm v))) =
      chartAt ℂ s (b ((chartAt ℂ x).symm (chartAt ℂ x (a ((chartAt ℂ t).symm v)))))
    rw [(chartAt ℂ x).left_inv hv]
  rw [hev.deriv_eq, (hAd.hasDerivAt.comp_of_eq z hBd.hasDerivAt rfl).deriv]
  ring

/-- The inverse of the inclusion of an open subset is holomorphic on the subset. -/
theorem s82lc_opens_symm_mdiff {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] (U : TopologicalSpace.Opens Y)
    (hU : Nonempty U) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (U.openPartialHomeomorphSubtypeCoe hU).symm
      (U.openPartialHomeomorphSubtypeCoe hU).target := by
  set c := U.openPartialHomeomorphSubtypeCoe hU with hc
  intro y hy
  have hid : MDifferentiableWithinAt 𝓘(ℂ) 𝓘(ℂ) (Subtype.val ∘ c.symm) c.target y :=
    mdifferentiableWithinAt_id.congr (fun w hw => c.right_inv hw) (c.right_inv hy)
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (P := DifferentiableWithinAtProp 𝓘(ℂ) 𝓘(ℂ)) (U := U) c.symm c.target y).1 hid

section PuncturedCover

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
  [IsManifold 𝓘(ℂ) ω S] {g n : ℕ} (F : FiniteTypeStructure S g n 0) {B : Finset F.X.carrier}
  {Y : ClosedRS.{u}} {pr : Y.carrier → F.X.carrier}
  (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
    (∀ x ∉ B, (pr ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ B, (pr ⁻¹' {x}).ncard = 1)
  (U : TopologicalSpace.Opens Y.carrier) (hU : (U : Set Y.carrier) = pr ⁻¹' (↑F.P)ᶜ)

omit [T2Space S] in
include hpr hU in
/-- **The projection of the punctured cover**: `π = ι⁻¹ ∘ pr` is holomorphic, with holomorphic local inverses
(`pr` is unbranched off `F.P ⊇ B`). -/
theorem s82lc_punct_proj (hB : B ⊆ F.P) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun t : U => Function.invFun F.ι (pr t.1)) ∧
      ∀ t : U, ∃ e : OpenPartialHomeomorph U S, t ∈ e.source ∧
        Set.EqOn (fun t : U => Function.invFun F.ι (pr t.1)) e e.source ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target := by
  have hrange : range F.ι = (↑F.P)ᶜ := by rw [F.range_ι]; simp
  have hmem : ∀ t : U, pr t.1 ∉ F.P := fun t => by
    have := t.2
    rw [← SetLike.mem_coe, hU] at this
    exact this
  have hval : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : U → Y.carrier) :=
    (contMDiff_subtype_val (n := ω)).mdifferentiable (by simp)
  refine ⟨fun t => s82lc_invFun_mdifferentiableAt F.embedding.injective F.holomorphic
    ((hpr.1 _).comp t (hval t)) (by rw [hrange]; exact hmem t), fun t => ?_⟩
  have hU' : Nonempty U := ⟨t⟩
  set c := U.openPartialHomeomorphSubtypeCoe hU' with hc
  have htB : pr t.1 ∉ B := fun h => hmem t (hB h)
  obtain ⟨e₀, hte₀, heq₀, he₀'⟩ := (s82lc_local_form hpr).2.1 t.1 htB
  obtain ⟨hI, hI', hIt⟩ := s82lc_iota_oph F
  set I := F.embedding.toOpenPartialHomeomorph F.ι with hI
  have hIsymm : ∀ x ∈ range F.ι, Function.invFun F.ι x = I.symm x := by
    rintro x ⟨s, rfl⟩
    rw [Function.leftInverse_invFun F.embedding.injective s]
    have hse : s ∈ I.source := by simp [hI]
    have : I s = F.ι s := by simp [hI]
    rw [← this, I.left_inv hse]
  refine ⟨(c.trans e₀).trans I.symm, ?_, ?_, ?_⟩
  · refine ⟨⟨mem_univ _, hte₀⟩, ?_⟩
    show e₀ t.1 ∈ I.target
    rw [hIt, ← heq₀ hte₀]; exact hmem t
  · intro t' ht'
    have h1 : e₀ t'.1 = pr t'.1 := (heq₀ ht'.1.2).symm
    show Function.invFun F.ι (pr t'.1) = I.symm (e₀ t'.1)
    rw [h1, hIsymm _ (by rw [hrange]; exact hmem t')]
  · intro u hu
    have hu1 : I u ∈ e₀.target := hu.2.1
    have hu2 : e₀.symm (I u) ∈ (U : Set Y.carrier) := by
      have := hu.2.2
      simpa [hc] using this
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) I u := F.holomorphic u
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e₀.symm (I u) :=
      (he₀' _ hu1).mdifferentiableAt (e₀.open_target.mem_nhds hu1)
    have h3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c.symm (e₀.symm (I u)) :=
      (s82lc_opens_symm_mdiff U hU' _ (by rw [U.openPartialHomeomorphSubtypeCoe_target]; exact hu2)).mdifferentiableAt
        ((U.openPartialHomeomorphSubtypeCoe_target hU' ▸ U.isOpen).mem_nhds
          (by rw [U.openPartialHomeomorphSubtypeCoe_target]; exact hu2))
    exact (h3.comp u (h2.comp u h1)).mdifferentiableWithinAt

omit [T2Space S] [IsManifold 𝓘(ℂ) ω S] in
include hpr hU in
/-- The projection of the punctured cover is surjective, two-to-one and proper. -/
theorem s82lc_punct_proj_fibres (hB : B ⊆ F.P) :
    Function.Surjective (fun t : U => Function.invFun F.ι (pr t.1)) ∧
      (∀ s : S, ((fun t : U => Function.invFun F.ι (pr t.1)) ⁻¹' {s}).ncard = 2) ∧
      IsProperMap (fun t : U => Function.invFun F.ι (pr t.1)) := by
  have hrange : range F.ι = (↑F.P)ᶜ := by rw [F.range_ι]; simp
  have hιP : ∀ s, F.ι s ∉ F.P := fun s => by
    have : F.ι s ∈ range F.ι := ⟨s, rfl⟩
    rw [hrange] at this; exact this
  have hmemU : ∀ y : Y.carrier, pr y ∉ F.P → y ∈ U := fun y hy => by
    rw [← SetLike.mem_coe, hU]; exact hy
  have hmem : ∀ t : U, pr t.1 ∉ F.P := fun t => by
    have := t.2
    rw [← SetLike.mem_coe, hU] at this
    exact this
  have hfib : ∀ s : S, (fun t : U => Function.invFun F.ι (pr t.1)) ⁻¹' {s} =
      Subtype.val ⁻¹' (pr ⁻¹' {F.ι s}) := by
    intro s
    ext t
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      rw [← h]
      exact (Function.invFun_eq (show pr t.1 ∈ range F.ι by rw [hrange]; exact hmem t)).symm
    · intro h
      rw [h]
      exact Function.leftInverse_invFun F.embedding.injective s
  refine ⟨fun s => ?_, fun s => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := hpr.2.1 (F.ι s)
    refine ⟨⟨y, hmemU y (by rw [hy]; exact hιP s)⟩, ?_⟩
    show Function.invFun F.ι (pr y) = s
    rw [hy]; exact Function.leftInverse_invFun F.embedding.injective s
  · rw [hfib, Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
    · exact hpr.2.2.1 _ fun h => hιP s (hB h)
    · intro y hy
      exact ⟨⟨y, hmemU y (by rw [show pr y = F.ι s from hy]; exact hιP s)⟩, rfl⟩
  · -- `π = j ∘ (pr restricted to the preimage of X ∖ P)`, `j` the inverse of `ι`
    set ιh := F.embedding.isEmbedding.toHomeomorph with hιh
    have hinv : ∀ x : ((↑F.P)ᶜ : Set F.X.carrier), (x : F.X.carrier) ∈ range F.ι := fun x => by
      rw [hrange]; exact x.2
    set j : ((↑F.P)ᶜ : Set F.X.carrier) ≃ₜ range F.ι :=
      Homeomorph.setCongr (show ((↑F.P)ᶜ : Set F.X.carrier) = range F.ι from hrange.symm) with hj
    have hpp : IsProperMap pr := hpr.1.continuous.isProperMap
    have hres := hpp.restrictPreimage ((↑F.P)ᶜ : Set F.X.carrier)
    set k : U ≃ₜ (pr ⁻¹' ((↑F.P)ᶜ : Set F.X.carrier)) :=
      Homeomorph.setCongr (show (U : Set Y.carrier) = pr ⁻¹' ((↑F.P)ᶜ : Set F.X.carrier) from hU) with hk
    have hcomp : IsProperMap (ιh.symm ∘ j ∘ ((↑F.P)ᶜ : Set F.X.carrier).restrictPreimage pr ∘ k) :=
      ιh.symm.isProperMap.comp (j.isProperMap.comp (hres.comp k.isProperMap))
    convert hcomp using 1
    funext t
    have h1 : F.ι (ιh.symm (j (((↑F.P)ᶜ : Set F.X.carrier).restrictPreimage pr (k t)))) = pr t.1 := by
      have := ιh.apply_symm_apply (j (((↑F.P)ᶜ : Set F.X.carrier).restrictPreimage pr (k t)))
      exact congrArg Subtype.val this
    show Function.invFun F.ι (pr t.1) = ιh.symm (j (((↑F.P)ᶜ : Set F.X.carrier).restrictPreimage pr (k t)))
    rw [← h1, Function.leftInverse_invFun F.embedding.injective]

omit [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] in
include hpr hU in
/-- The punctured cover is connected. -/
theorem s82lc_punct_connected (hne : (U : Set Y.carrier).Nonempty) : ConnectedSpace U := by
  have hfin : (pr ⁻¹' (↑F.P : Set F.X.carrier)).Finite := by
    rw [← Set.biUnion_preimage_singleton]
    exact F.P.finite_toSet.biUnion fun x _ => Set.finite_of_ncard_ne_zero (by
      by_cases hx : x ∈ B
      · rw [hpr.2.2.2 x hx]; exact one_ne_zero
      · rw [hpr.2.2.1 x hx]; exact two_ne_zero)
  have hpc : IsPreconnected (U : Set Y.carrier) := by
    rw [hU, Set.preimage_compl]
    refine s82lc_isPreconnected_compl hfin.isClosed fun b hb => ⟨(pr ⁻¹' ↑F.P \ {b})ᶜ, ?_, ?_⟩
    · exact ((hfin.subset sdiff_subset).isClosed.isOpen_compl).mem_nhds fun h => h.2 rfl
    · rintro x ⟨hx1, hx2⟩
      by_contra hxb
      exact hx1 ⟨hx2, hxb⟩
  exact isConnected_iff_connectedSpace.1 ⟨hne, hpc⟩

end PuncturedCover

/-- The number of points over the punctures: `|B| + 2(|P| - |B|)`. -/
theorem s82lc_punct_card {Y X : Type*} [DecidableEq Y] {P B : Finset X} (hB : B ⊆ P) {pr : Y → X}
    (h2 : ∀ x ∉ B, (pr ⁻¹' {x}).ncard = 2) (h1 : ∀ x ∈ B, (pr ⁻¹' {x}).ncard = 1)
    (hfin : ∀ x, (pr ⁻¹' {x}).Finite) :
    (P.biUnion fun x => (hfin x).toFinset).card = B.card + 2 * (P.card - B.card) := by
  classical
  rw [Finset.card_biUnion]
  · have hc : ∀ x, (hfin x).toFinset.card = (pr ⁻¹' {x}).ncard := fun x =>
      (Set.ncard_eq_toFinset_card _ (hfin x)).symm
    simp only [hc]
    rw [← Finset.sum_sdiff hB, Finset.sum_congr rfl (fun x hx => h2 x (Finset.mem_sdiff.1 hx).2),
      Finset.sum_congr rfl (fun x hx => h1 x hx), Finset.sum_const, Finset.sum_const, smul_eq_mul,
      smul_eq_mul, Finset.card_sdiff_of_subset hB]
    ring
  · intro x _ y _ hxy
    rw [Function.onFun, Finset.disjoint_left]
    intro a ha hb
    simp only [Set.Finite.mem_toFinset, mem_preimage, mem_singleton_iff] at ha hb
    exact hxy (ha.symm.trans hb)

open Classical in
/-- **The lifted differential is admissible.**  On a two-sheeted cover `pr` branched over `B ⊆ F.P`, the pull-back
`Q̂ = (ι⁻¹ ∘ pr)^* (ι^* q̂)` of an admissible `q̂`, set to `0` over `F.P`, obeys the transformation law, is holomorphic
off `pr⁻¹ F.P`, and has at most a simple pole (normalized value `0`) at every point over `F.P`, in every chart: over
`B` the pole is removable, over `F.P ∖ B` it is simple (`s82lc_pole_pullback` with `F = φ ∘ pr ∘ φ⁻¹`). -/
theorem s82lc_lift_admissible {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g n : ℕ} (F : FiniteTypeStructure S g n 0) {qh : F.X.carrier → ℂ → ℂ}
    (hqh : qh ∈ admissibleQDSpace F) {B : Finset F.X.carrier} {Y : ClosedRS.{u}} {pr : Y.carrier → F.X.carrier}
    (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
      (∀ x ∉ B, (pr ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ B, (pr ⁻¹' {x}).ncard = 1) :
    IsDiffFamily 2 0 (fun y z => if z ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm z ∉ pr ⁻¹' ↑F.P then
      pullbackQD F qh (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))
          (chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))
            (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))) *
        deriv (fun v => chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))
          (Function.invFun F.ι (pr ((chartAt ℂ y).symm v)))) z ^ 2 else 0) ∧
    (∀ x : Y.carrier, DifferentiableOn ℂ (fun z => if z ∈ (chartAt ℂ x).target ∧
        (chartAt ℂ x).symm z ∉ pr ⁻¹' ↑F.P then
      pullbackQD F qh (Function.invFun F.ι (pr ((chartAt ℂ x).symm z)))
          (chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ x).symm z)))
            (Function.invFun F.ι (pr ((chartAt ℂ x).symm z)))) *
        deriv (fun v => chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ x).symm z)))
          (Function.invFun F.ι (pr ((chartAt ℂ x).symm v)))) z ^ 2 else 0)
        ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (pr ⁻¹' ↑F.P)ᶜ)) ∧
    ∀ (x : Y.carrier), ∀ p ∈ pr ⁻¹' (↑F.P : Set F.X.carrier), p ∈ (chartAt ℂ x).source →
      (fun z => if z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∉ pr ⁻¹' ↑F.P then
        pullbackQD F qh (Function.invFun F.ι (pr ((chartAt ℂ x).symm z)))
            (chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ x).symm z)))
              (Function.invFun F.ι (pr ((chartAt ℂ x).symm z)))) *
          deriv (fun v => chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ x).symm z)))
            (Function.invFun F.ι (pr ((chartAt ℂ x).symm v)))) z ^ 2 else 0) (chartAt ℂ x p) = 0 ∧
      ∃ c : ℂ, ∃ r : ℂ → ℂ, AnalyticAt ℂ r (chartAt ℂ x p) ∧ ∀ᶠ z in 𝓝[≠] (chartAt ℂ x p),
        (fun z => if z ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm z ∉ pr ⁻¹' ↑F.P then
          pullbackQD F qh (Function.invFun F.ι (pr ((chartAt ℂ x).symm z)))
              (chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ x).symm z)))
                (Function.invFun F.ι (pr ((chartAt ℂ x).symm z)))) *
            deriv (fun v => chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ x).symm z)))
              (Function.invFun F.ι (pr ((chartAt ℂ x).symm v)))) z ^ 2 else 0) z =
          c / (z - chartAt ℂ x p) + r z := by
  set R : Y.carrier → ℂ → ℂ := fun y z => if z ∈ (chartAt ℂ y).target ∧ (chartAt ℂ y).symm z ∉ pr ⁻¹' ↑F.P then
      pullbackQD F qh (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))
          (chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))
            (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))) *
        deriv (fun v => chartAt ℂ (Function.invFun F.ι (pr ((chartAt ℂ y).symm z)))
          (Function.invFun F.ι (pr ((chartAt ℂ y).symm v)))) z ^ 2 else 0 with hRdef
  have hrange : range F.ι = (↑F.P)ᶜ := by rw [F.range_ι]; simp
  have hBf : (pr ⁻¹' (↑F.P : Set F.X.carrier)).Finite := by
    rw [← Set.biUnion_preimage_singleton]
    exact F.P.finite_toSet.biUnion fun x _ => Set.finite_of_ncard_ne_zero (by
      by_cases hx : x ∈ B
      · rw [hpr.2.2.2 x hx]; exact one_ne_zero
      · rw [hpr.2.2.1 x hx]; exact two_ne_zero)
  have hfib0 : ∀ x, (pr ⁻¹' {x}).ncard ≠ 0 := fun x => by
    by_cases hx : x ∈ B
    · rw [hpr.2.2.2 x hx]; exact one_ne_zero
    · rw [hpr.2.2.1 x hx]; exact two_ne_zero
  obtain ⟨h1, h2, h3⟩ := s82lc_raw_hyps F hpr.1 (s32p_pullbackQD_isHolQuadDiff F hqh) (R := R)
    (fun y z => rfl)
  have hRB : ∀ y z, (chartAt ℂ y).symm z ∈ pr ⁻¹' ↑F.P → R y z = 0 := fun y z h => by
    show (if _ then _ else _) = _
    rw [ite_eq_right fun h' => h'.2 h]
  refine ⟨⟨h1, fun x y z hz hzx => ?_⟩, fun x z hz => (h3 x z hz.1 hz.2).differentiableWithinAt,
    fun x p hp hpx => ⟨hRB x _ (by rw [(chartAt ℂ x).left_inv hpx]; exact hp), ?_⟩⟩
  · rw [zpow_zero, mul_one, zpow_two, ← pow_two]
    by_cases hzB : (chartAt ℂ y).symm z ∈ pr ⁻¹' ↑F.P
    · obtain ⟨-, -, hτeq⟩ := s23_transition_mem hz hzx
      rw [hRB y z hzB, hRB x _ (by rw [hτeq]; exact hzB), zero_mul]
    · exact h2 x y z hz hzx hzB
  · -- the pole form at `p`, through `F = φ_{pr p} ∘ pr ∘ φ_x⁻¹`
    set z₀ := chartAt ℂ x p with hz₀
    set p' := pr p with hp'
    have hz₀t : z₀ ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hpx
    have hz₀s : (chartAt ℂ x).symm z₀ = p := (chartAt ℂ x).left_inv hpx
    obtain ⟨-, c, r, hr, hqr⟩ := hqh.2.2.1 p' p' hp (mem_chart_source ℂ p')
    obtain ⟨hFa, -⟩ := s82lc_T_analytic pr isOpen_univ (fun t _ => hpr.1 t) x p' hz₀t (mem_univ _)
      (by rw [hz₀s]; exact mem_chart_source ℂ p')
    have hcont : ContinuousAt (fun z => pr ((chartAt ℂ x).symm z)) z₀ :=
      hpr.1.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz₀t)
    have hsrc : ∀ᶠ z in 𝓝 z₀, pr ((chartAt ℂ x).symm z) ∈ (chartAt ℂ p').source := by
      refine hcont.preimage_mem_nhds ?_
      rw [show pr ((chartAt ℂ x).symm z₀) = p' by rw [hz₀s]]
      exact (chartAt ℂ p').open_source.mem_nhds (mem_chart_source ℂ p')
    have hF0 : chartAt ℂ p' (pr ((chartAt ℂ x).symm z₀)) = chartAt ℂ p' p' := by rw [hz₀s]
    have hnc : ¬ ∀ᶠ z in 𝓝 z₀, chartAt ℂ p' (pr ((chartAt ℂ x).symm z)) =
        chartAt ℂ p' (pr ((chartAt ℂ x).symm z₀)) := by
      rw [hF0]
      exact s82lc_not_locally_const' hpr.1 hfib0 x hpx
    refine s82lc_pole_pullback hFa hF0 hnc hr hqr ?_
    filter_upwards [s82lc_punctured_off hBf x hz₀t, nhdsWithin_le_nhds hsrc] with z hz hzs
    have hzO : pr ((chartAt ℂ x).symm z) ∈ range F.ι := by rw [hrange]; exact hz.2
    show (if _ then _ else _) = _
    rw [ite_eq_left hz]
    exact s82lc_raw_pullback F hqh hpr.1 x p' hz.1 hzO hzs

/-- The pull-back `π^* Q` (indicator of the chart targets) read in the chart at the fixed image point `π t`. -/
theorem s82lc_graw_fixed {Y M : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M] {π' : Y → M}
    (hπ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π') {Q : M → ℂ → ℂ} (hQ : IsDiffFamily 2 0 Q) (t : Y) :
    ∀ᶠ z in 𝓝 (chartAt ℂ t t), (chartAt ℂ t).target.indicator (fun z => Q (π' ((chartAt ℂ t).symm z))
        (chartAt ℂ (π' ((chartAt ℂ t).symm z)) (π' ((chartAt ℂ t).symm z))) *
          deriv (fun v => chartAt ℂ (π' ((chartAt ℂ t).symm z)) (π' ((chartAt ℂ t).symm v))) z ^ 2) z =
      Q (π' t) (chartAt ℂ (π' t) (π' ((chartAt ℂ t).symm z))) *
        deriv (fun w => chartAt ℂ (π' t) (π' ((chartAt ℂ t).symm w))) z ^ 2 := by
  have hct : chartAt ℂ t t ∈ (chartAt ℂ t).target := (chartAt ℂ t).map_source (mem_chart_source ℂ t)
  have htt : (chartAt ℂ t).symm (chartAt ℂ t t) = t := (chartAt ℂ t).left_inv (mem_chart_source ℂ t)
  obtain ⟨-, hev⟩ := s82lc_T_analytic π' isOpen_univ (fun t _ => hπ t) t (π' t) hct (mem_univ _)
    (by rw [htt]; exact mem_chart_source ℂ _)
  filter_upwards [hev] with z hz
  rw [indicator_of_mem hz.1]
  exact s82lc_raw_local hQ π' t (π' t) hz.1 (hπ _) hz.2.2

/-- **The lift to a partially branched cover, punctured over all punctures** (odd `n` and `(0, 4)`).  Let `pr₀`
be a two-sheeted cover of `F₀.X` branched exactly over `B₀ ⊆ F₀.P`, of genus `h`.  The punctured cover
`T₀ = X₀' ∖ pr₀⁻¹(F₀.P)` is of type `(h, 2n'')` (`|B₀| + 2n'' = 2n` points over the punctures), with the projection
`π₀ = ι₀⁻¹ ∘ pr₀ : T₀ → S₀` (a 2-to-1 local biholomorphism); the cover of the target is transported along `f₀`.
An admissible Teichmüller map `f₀` lifts to an admissible Teichmüller map `ft₀ : T₀ → T₁` with the pulled-back
differentials (holomorphic over the branch points by (32.1), at most simple poles over the other punctures), and a
quasiconformal `f ≃ f₀` lifts to `ft ≃ ft₀` (the lifted homotopy) with `K[ft] = K[f]`. -/
theorem s82lc_lift_punctured {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) (F₁ : FiniteTypeStructure S g n 0)
    {B₀ : Finset F₀.X.carrier} (hB₀ : B₀ ⊆ F₀.P) {X₀' : ClosedRS.{u}} {pr₀ : X₀'.carrier → F₀.X.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ B₀, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ B₀, (pr₀ ⁻¹' {x}).ncard = 1)
    {h : ℕ} (hX₀' : HasGenus X₀'.carrier h) {n'' : ℕ} (hB : B₀.card + 2 * n'' = 2 * n)
    (hh : 2 * h + 2 = 4 * g + B₀.card)
    {f₀ f : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ} (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k)
    (hf : IsQCRS f) (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    ∃ (T₀ T₁ : Type u) (_ : TopologicalSpace T₀) (_ : ChartedSpace ℂ T₀) (_ : T2Space T₀) (_ : ConnectedSpace T₀)
      (_ : IsManifold 𝓘(ℂ) ω T₀) (_ : TopologicalSpace T₁) (_ : ChartedSpace ℂ T₁) (_ : T2Space T₁)
      (_ : ConnectedSpace T₁) (_ : IsManifold 𝓘(ℂ) ω T₁)
      (G₀ : FiniteTypeStructure T₀ h (2 * n'') 0) (G₁ : FiniteTypeStructure T₁ h (2 * n'') 0)
      (π₀ : T₀ → S₀) (π₁ : T₁ → S) (ft₀ ft : T₀ ≃ₜ T₁) (qt : T₀ → ℂ → ℂ) (qt' : T₁ → ℂ → ℂ),
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₀ ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π₁ ∧ Function.Surjective π₀ ∧
      (∀ s : S₀, (π₀ ⁻¹' {s}).ncard = 2) ∧
      IsProperMap π₀ ∧
      (∀ t : T₀, ∃ e : OpenPartialHomeomorph T₀ S₀, t ∈ e.source ∧ Set.EqOn π₀ e e.source ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target) ∧
      (∀ t : T₁, ∃ e : OpenPartialHomeomorph T₁ S, t ∈ e.source ∧ Set.EqOn π₁ e e.source ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target) ∧
      (∀ t, π₁ (ft₀ t) = f₀ (π₀ t)) ∧ (∀ t, π₁ (ft t) = f (π₀ t)) ∧
      IsAdmissibleTeichmullerMap G₀ ft₀ qt qt' k ∧ IsQCRS ft ∧ maxDilatationRS ft = maxDilatationRS f ∧
      ContinuousMap.Homotopic (ft₀ : C(T₀, T₁)) (ft : C(T₀, T₁)) ∧
      (∀ t : T₀, ∀ᶠ z in 𝓝 (chartAt ℂ t t), qt t z = q (π₀ t) (chartAt ℂ (π₀ t) (π₀ ((chartAt ℂ t).symm z))) *
        deriv (fun w => chartAt ℂ (π₀ t) (π₀ ((chartAt ℂ t).symm w))) z ^ 2) ∧
      ∀ t : T₁, ∀ᶠ z in 𝓝 (chartAt ℂ t t), qt' t z = q' (π₁ t) (chartAt ℂ (π₁ t) (π₁ ((chartAt ℂ t).symm z))) *
        deriv (fun w => chartAt ℂ (π₁ t) (π₁ ((chartAt ℂ t).symm w))) z ^ 2 := by
  classical
  obtain ⟨qh, hqh, hqeq⟩ := Submodule.mem_map.1 hf₀.1
  have hqeq' : pullbackQD F₀ qh = q := hqeq
  subst hqeq'
  have hT := hf₀.2
  have hqi : IsDiffFamily 2 0 (pullbackQD F₀ qh) ∧
      ∀ x : S₀, DifferentiableOn ℂ (pullbackQD F₀ qh x) (chartAt ℂ x).target := hT.initial
  have hqt : IsDiffFamily 2 0 q' ∧ ∀ x : S, DifferentiableOn ℂ (q' x) (chartAt ℂ x).target := hT.terminal
  have hr0 : range F₀.ι = (↑F₀.P)ᶜ := by rw [F₀.range_ι]; simp
  have hr1 : range F₁.ι = (↑F₁.P)ᶜ := by rw [F₁.range_ι]; simp
  have hιP₀ : ∀ s, F₀.ι s ∉ F₀.P := fun s => by
    have : F₀.ι s ∈ range F₀.ι := ⟨s, rfl⟩
    rw [hr0] at this; exact this
  have hιP₁ : ∀ s, F₁.ι s ∉ F₁.P := fun s => by
    have : F₁.ι s ∈ range F₁.ι := ⟨s, rfl⟩
    rw [hr1] at this; exact this
  -- the extensions of `f₀`, `f` over the punctures and the transported cover of the target
  obtain ⟨fb₀, hfb₀, hfb₀P⟩ := s82lc_extend_homeomorph F₀ F₁ f₀
  obtain ⟨fb, hfb, hfbP⟩ := s82lc_extend_homeomorph F₀ F₁ f
  obtain ⟨X₁', e, pr₁, hd, he⟩ := s82lc_transport hpr₀ fb₀
  set B₁ : Finset F₁.X.carrier := B₀.image fb₀ with hB₁
  have hpr₁ := s82lc_transport_fibres (P₁ := B₁) hpr₀ fb₀ (by rw [hB₁, Finset.coe_image]) e hd he
  have hfbmem : ∀ x, fb₀ x ∈ F₁.P ↔ x ∈ F₀.P := fun x => by
    constructor
    · intro h
      have : fb₀ x ∈ fb₀ '' ↑F₀.P := by rw [hfb₀P]; exact h
      obtain ⟨y, hy, hyx⟩ := this
      rwa [fb₀.injective hyx] at hy
    · intro h
      have : fb₀ x ∈ fb₀ '' ↑F₀.P := mem_image_of_mem _ h
      rwa [hfb₀P] at this
  have hB₁P : B₁ ⊆ F₁.P := fun x hx => by
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hx
    exact (hfbmem b).2 (hB₀ hb)
  have hB₁c : B₁.card = B₀.card := Finset.card_image_of_injective _ fb₀.injective
  -- the punctured covers
  set U₀ : TopologicalSpace.Opens X₀'.carrier :=
    ⟨pr₀ ⁻¹' (↑F₀.P)ᶜ, F₀.P.finite_toSet.isClosed.isOpen_compl.preimage hpr₀.1.continuous⟩ with hU₀
  set U₁ : TopologicalSpace.Opens X₁'.carrier :=
    ⟨pr₁ ⁻¹' (↑F₁.P)ᶜ, F₁.P.finite_toSet.isClosed.isOpen_compl.preimage hpr₁.1.continuous⟩ with hU₁
  have hne₀ : (U₀ : Set X₀'.carrier).Nonempty := by
    obtain ⟨y, hy⟩ := hpr₀.2.1 (F₀.ι (Classical.arbitrary S₀))
    exact ⟨y, show pr₀ y ∉ F₀.P by rw [hy]; exact hιP₀ _⟩
  have hne₁ : (U₁ : Set X₁'.carrier).Nonempty := by
    obtain ⟨y, hy⟩ := hpr₁.2.1 (F₁.ι (Classical.arbitrary S))
    exact ⟨y, show pr₁ y ∉ F₁.P by rw [hy]; exact hιP₁ _⟩
  have hconn₀ : ConnectedSpace U₀ := s82lc_punct_connected F₀ hpr₀ U₀ rfl hne₀
  have hconn₁ : ConnectedSpace U₁ := s82lc_punct_connected F₁ hpr₁ U₁ rfl hne₁
  have : Nonempty U₀ := hne₀.to_subtype
  -- the puncture sets upstairs
  have hfin₀ : ∀ x, (pr₀ ⁻¹' {x}).Finite := fun x => Set.finite_of_ncard_ne_zero (by
    by_cases hx : x ∈ B₀
    · rw [hpr₀.2.2.2 x hx]; exact one_ne_zero
    · rw [hpr₀.2.2.1 x hx]; exact two_ne_zero)
  have hfin₁ : ∀ x, (pr₁ ⁻¹' {x}).Finite := fun x => Set.finite_of_ncard_ne_zero (by
    by_cases hx : x ∈ B₁
    · rw [hpr₁.2.2.2 x hx]; exact one_ne_zero
    · rw [hpr₁.2.2.1 x hx]; exact two_ne_zero)
  set PT₀ := F₀.P.biUnion fun x => (hfin₀ x).toFinset with hPT₀
  set PT₁ := F₁.P.biUnion fun x => (hfin₁ x).toFinset with hPT₁
  have hPT₀c : (↑PT₀ : Set X₀'.carrier) = pr₀ ⁻¹' ↑F₀.P := by
    ext y; simp [hPT₀]
  have hPT₁c : (↑PT₁ : Set X₁'.carrier) = pr₁ ⁻¹' ↑F₁.P := by
    ext y; simp [hPT₁]
  have hBn : B₀.card ≤ n := by
    have := Finset.card_le_card hB₀
    rwa [F₀.card_P] at this
  have hcard₀ : PT₀.card = 2 * n'' := by
    rw [hPT₀, s82lc_punct_card hB₀ hpr₀.2.2.1 hpr₀.2.2.2 hfin₀, F₀.card_P]; omega
  have hcard₁ : PT₁.card = 2 * n'' := by
    rw [hPT₁, s82lc_punct_card hB₁P hpr₁.2.2.1 hpr₁.2.2.2 hfin₁, F₁.card_P, hB₁c]; omega
  have hrangeU : ∀ {X : ClosedRS.{u}} (PT : Finset X.carrier) (U : TopologicalSpace.Opens X.carrier),
      (U : Set X.carrier) = (↑PT)ᶜ →
        range (Subtype.val : U → X.carrier) = (↑PT ∪ ⋃ j : Fin 0, (fun j : Fin 0 => j.elim0 : Fin 0 → Set X.carrier) j)ᶜ := by
    intro X PT U hU
    rw [Subtype.range_coe, hU]
    simp
  set G₀ : FiniteTypeStructure U₀ h (2 * n'') 0 :=
    { X := X₀', P := PT₀, D := fun j => j.elim0, ι := Subtype.val, genus := hX₀', card_P := hcard₀,
      disc := fun j => j.elim0, disjoint := fun i => i.elim0, disjoint_P := fun j => j.elim0,
      embedding := U₀.isOpen.isOpenEmbedding_subtypeVal,
      holomorphic := (contMDiff_subtype_val (n := ω)).mdifferentiable (by simp),
      range_ι := hrangeU PT₀ U₀ (by rw [hPT₀c]; rfl) } with hG₀
  set G₁ : FiniteTypeStructure U₁ h (2 * n'') 0 :=
    { X := X₁', P := PT₁, D := fun j => j.elim0, ι := Subtype.val, genus := hasGenus_of_homeomorph hX₀' e,
      card_P := hcard₁, disc := fun j => j.elim0, disjoint := fun i => i.elim0,
      disjoint_P := fun j => j.elim0, embedding := U₁.isOpen.isOpenEmbedding_subtypeVal,
      holomorphic := (contMDiff_subtype_val (n := ω)).mdifferentiable (by simp),
      range_ι := hrangeU PT₁ U₁ (by rw [hPT₁c]; rfl) } with hG₁
  -- the projections
  set π₀ : U₀ → S₀ := fun t => Function.invFun F₀.ι (pr₀ t.1) with hπ₀
  set π₁ : U₁ → S := fun t => Function.invFun F₁.ι (pr₁ t.1) with hπ₁
  obtain ⟨hπ₀d, hπ₀loc⟩ := s82lc_punct_proj F₀ hpr₀ U₀ rfl hB₀
  obtain ⟨hπ₁d, hπ₁loc⟩ := s82lc_punct_proj F₁ hpr₁ U₁ rfl hB₁P
  obtain ⟨hπ₀s, hπ₀fib, hπ₀prop⟩ := s82lc_punct_proj_fibres F₀ hpr₀ U₀ rfl hB₀
  -- the lift of `f₀`: the restriction of `e`
  have hUe : ∀ y : X₀'.carrier, y ∈ (U₀ : Set X₀'.carrier) ↔ e y ∈ (U₁ : Set X₁'.carrier) := fun y => by
    show pr₀ y ∉ F₀.P ↔ pr₁ (e y) ∉ F₁.P
    rw [he, hfbmem]
  set ft₀ : U₀ ≃ₜ U₁ := e.subtype hUe with hft₀
  have hc₀ : ∀ t, π₁ (ft₀ t) = f₀ (π₀ t) := by
    intro t
    have h1 : pr₀ t.1 = F₀.ι (π₀ t) :=
      (Function.invFun_eq (show pr₀ t.1 ∈ range F₀.ι by rw [hr0]; exact t.2)).symm
    show Function.invFun F₁.ι (pr₁ (e t.1)) = f₀ (π₀ t)
    rw [he, h1, hfb₀]
    exact Function.leftInverse_invFun F₁.embedding.injective _
  -- the lift of `f`: lift `h = fb₀⁻¹ ∘ fb` on the punctured cover, then compose with `ft₀`
  set hb : F₀.X.carrier ≃ₜ F₀.X.carrier := fb.trans fb₀.symm with hhb
  have hP : hb '' ↑F₀.P = ↑F₀.P := by
    show (fb₀.symm ∘ fb) '' ↑F₀.P = ↑F₀.P
    rw [Set.image_comp, hfbP, ← hfb₀P, Set.image_image]
    simp
  obtain ⟨H⟩ := hhom
  set ι₀h := F₀.embedding.isEmbedding.toHomeomorph with hι₀h
  have hinv : ∀ x : ((↑F₀.P)ᶜ : Set F₀.X.carrier), (x : F₀.X.carrier) ∈ range F₀.ι := fun x => by
    rw [hr0]; exact x.2
  set j : C(((↑F₀.P)ᶜ : Set F₀.X.carrier), S₀) :=
    ⟨fun x => ι₀h.symm ⟨x, hinv x⟩, ι₀h.symm.continuous.comp (continuous_subtype_val.subtype_mk _)⟩ with hj
  have hjι : ∀ x : ((↑F₀.P)ᶜ : Set F₀.X.carrier), F₀.ι (j x) = x := fun x => by
    have := ι₀h.apply_symm_apply ⟨x, hinv x⟩
    exact congrArg Subtype.val this
  set K : C(unitInterval × ((↑F₀.P)ᶜ : Set F₀.X.carrier), F₀.X.carrier) :=
    ⟨fun tx => fb₀.symm (F₁.ι (H (tx.1, j tx.2))),
      fb₀.symm.continuous.comp (F₁.embedding.continuous.comp
        (H.continuous.comp (continuous_fst.prodMk (j.continuous.comp continuous_snd))))⟩ with hK
  have hK0 : ∀ x, K (0, x) = x := fun x => by
    show fb₀.symm (F₁.ι (H (0, j x))) = x
    rw [H.apply_zero]
    show fb₀.symm (F₁.ι (f₀ (j x))) = x
    rw [← hfb₀, hjι, fb₀.symm_apply_apply]
  have hK1 : ∀ x, K (1, x) = hb x := fun x => by
    show fb₀.symm (F₁.ι (H (1, j x))) = fb₀.symm (fb x)
    rw [H.apply_one]
    show fb₀.symm (F₁.ι (f (j x))) = fb₀.symm (fb x)
    rw [← hfb, hjι]
  have hKP : ∀ t x, K (t, x) ∉ F₀.P := fun t x hx => by
    have h1 : F₁.ι (H (t, j x)) ∈ fb₀ '' ↑F₀.P := ⟨_, hx, fb₀.apply_symm_apply _⟩
    rw [hfb₀P] at h1
    exact hιP₁ _ h1
  have hcov : IsCoveringMapOn pr₀ (↑F₀.P)ᶜ := fun x hx =>
    (s82lc_local_form hpr₀).1 x fun hxB => hx (hB₀ hxB)
  obtain ⟨FT, hFT, L, hL0, hL1⟩ := s82lc_lift_punct hpr₀.1.continuous hcov hb hP K hK0 hK1 hKP
  set FT' : U₀ ≃ₜ U₀ := FT with hFT'
  set ft : U₀ ≃ₜ U₁ := FT'.trans ft₀ with hft
  have hc : ∀ t, π₁ (ft t) = f (π₀ t) := by
    intro t
    have h1 : pr₀ t.1 = F₀.ι (π₀ t) :=
      (Function.invFun_eq (show pr₀ t.1 ∈ range F₀.ι by rw [hr0]; exact t.2)).symm
    show Function.invFun F₁.ι (pr₁ (e (FT t).1)) = f (π₀ t)
    rw [he, hFT, h1, hhb, Homeomorph.trans_apply, fb₀.apply_symm_apply, hfb]
    exact Function.leftInverse_invFun F₁.embedding.injective _
  -- quasiconformality and the Teichmüller property of the lifts
  obtain ⟨hftqc, hftK⟩ := s82lc_glift_qc hf hπ₀d hπ₁d hπ₀s hπ₀loc hπ₁loc hc
  have hft₀qc := (s82lc_glift_qc hT.qc hπ₀d hπ₁d hπ₀s hπ₀loc hπ₁loc hc₀).1
  have hTeich := s82lc_teich_unbranched hT hft₀qc hπ₀d hπ₁d hπ₀s hπ₀loc hπ₁loc hc₀
  -- the lifted differential is admissible on `X₀'`
  obtain ⟨hlaw, hdiff, hpole⟩ := s82lc_lift_admissible F₀ hqh hpr₀
  set Qa : X₀'.carrier → ℂ → ℂ := fun y z => if z ∈ (chartAt ℂ y).target ∧
      (chartAt ℂ y).symm z ∉ pr₀ ⁻¹' ↑F₀.P then
      pullbackQD F₀ qh (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm z)))
          (chartAt ℂ (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm z)))
            (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm z)))) *
        deriv (fun v => chartAt ℂ (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm z)))
          (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm v)))) z ^ 2 else 0 with hQa
  have hrG : range G₀.ι = (pr₀ ⁻¹' ↑F₀.P)ᶜ := Subtype.range_coe
  have hadm : Qa ∈ admissibleQDSpace G₀ := by
    refine ⟨hlaw, fun x => ?_, fun x p hp hpx => ?_, fun x j => j.elim0, fun x j => j.elim0,
      fun x j => j.elim0⟩
    · rw [hrG]; exact hdiff x
    · have hp' : p ∈ pr₀ ⁻¹' (↑F₀.P : Set F₀.X.carrier) := by
        rw [← hPT₀c]; exact hp
      exact hpole x p hp' hpx
  -- the pull-back of `Qa` to `T₀` is the pull-back of `q` through `π₀`
  have hqt_eq : pullbackQD G₀ Qa = fun y => (chartAt ℂ y).target.indicator fun z =>
      pullbackQD F₀ qh (π₀ ((chartAt ℂ y).symm z))
        (chartAt ℂ (π₀ ((chartAt ℂ y).symm z)) (π₀ ((chartAt ℂ y).symm z))) *
          deriv (fun v => chartAt ℂ (π₀ ((chartAt ℂ y).symm z)) (π₀ ((chartAt ℂ y).symm v))) z ^ 2 := by
    funext t z
    by_cases hz : z ∈ (chartAt ℂ t).target
    · show (chartAt ℂ t).target.indicator _ z = (chartAt ℂ t).target.indicator _ z
      rw [indicator_of_mem hz, indicator_of_mem hz]
      set x : X₀'.carrier := ((chartAt ℂ t).symm z).1 with hx
      have hxP : pr₀ x ∉ F₀.P := ((chartAt ℂ t).symm z).2
      have hxt : chartAt ℂ x x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
      have hxx : (chartAt ℂ x).symm (chartAt ℂ x x) = x := (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
      have hQx : Qa x (chartAt ℂ x x) = pullbackQD F₀ qh (Function.invFun F₀.ι (pr₀ x))
          (chartAt ℂ (Function.invFun F₀.ι (pr₀ x)) (Function.invFun F₀.ι (pr₀ x))) *
            deriv (fun v => chartAt ℂ (Function.invFun F₀.ι (pr₀ x))
              (Function.invFun F₀.ι (pr₀ ((chartAt ℂ x).symm v)))) (chartAt ℂ x x) ^ 2 := by
        show (if _ then _ else _) = _
        rw [ite_eq_left ⟨hxt, by rw [hxx]; exact hxP⟩, hxx]
      show Qa x (chartAt ℂ x x) * _ = _
      rw [hQx]
      have hval : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Subtype.val : U₀ → X₀'.carrier) :=
        (contMDiff_subtype_val (n := ω)).mdifferentiable (by simp)
      have hbx : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun x => Function.invFun F₀.ι (pr₀ x)) x :=
        s82lc_invFun_mdifferentiableAt F₀.embedding.injective F₀.holomorphic (hpr₀.1 x)
          (by rw [hr0]; exact hxP)
      exact (s82lc_raw_comp (b := fun x => Function.invFun F₀.ι (pr₀ x)) hval (pullbackQD F₀ qh) t hz hbx).symm
    · show (chartAt ℂ t).target.indicator _ z = (chartAt ℂ t).target.indicator _ z
      rw [indicator_of_notMem hz, indicator_of_notMem hz]
  have hadmT : IsAdmissibleTeichmullerMap G₀ ft₀ (pullbackQD G₀ Qa)
      (fun y => (chartAt ℂ y).target.indicator fun z => q' (π₁ ((chartAt ℂ y).symm z))
        (chartAt ℂ (π₁ ((chartAt ℂ y).symm z)) (π₁ ((chartAt ℂ y).symm z))) *
          deriv (fun v => chartAt ℂ (π₁ ((chartAt ℂ y).symm z)) (π₁ ((chartAt ℂ y).symm v))) z ^ 2) k := by
    refine ⟨Submodule.mem_map.2 ⟨Qa, hadm, rfl⟩, ?_⟩
    rw [hqt_eq]
    exact hTeich
  -- the lifted homotopy
  have hhomt : ContinuousMap.Homotopic (ft₀ : C(U₀, U₁)) (ft : C(U₀, U₁)) := by
    refine ⟨⟨⟨fun p => ft₀ (L p), ft₀.continuous.comp L.continuous⟩, fun y => ?_, fun y => ?_⟩⟩
    · show ft₀ (L (0, y)) = ft₀ y
      rw [hL0]
    · show ft₀ (L (1, y)) = ft₀ (FT y)
      rw [hL1]
  refine ⟨U₀, U₁, inferInstance, inferInstance, inferInstance, hconn₀, inferInstance, inferInstance,
    inferInstance, inferInstance, hconn₁, inferInstance, G₀, G₁, π₀, π₁, ft₀, ft, pullbackQD G₀ Qa, _,
    hπ₀d, hπ₁d, hπ₀s, hπ₀fib, hπ₀prop, hπ₀loc, hπ₁loc, hc₀, hc, hadmT, hftqc, hftK, hhomt, ?_,
    fun t => s82lc_graw_fixed hπ₁d hqt.1 t⟩
  intro t
  rw [hqt_eq]
  exact s82lc_graw_fixed hπ₀d hqi.1 t

/-- **Theorem 32.1, odd `n` and `(0, 4)`, given the covers**: lift to the punctured partial cover of even type
`(h, 2n'')` (`s82lc_lift_punctured`), apply the even case there (with a cover of it branched over all its
punctures, of genus `2h + n'' - 1 > 1`), and descend through the surjective projection `π₀`. -/
theorem s82lc_uniq_punctured_of_cover
    (hcov : ∀ (X : ClosedRS.{u}) {g r : ℕ}, (g ≠ 0 ∨ r ≠ 0) → HasGenus X.carrier g → ∀ P : Finset X.carrier,
      P.card = 2 * r → ∃ (X' : ClosedRS.{u}) (pr : X'.carrier → X.carrier), HasGenus X'.carrier (2 * g + r - 1) ∧
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
        (∀ x ∉ P, (pr ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ P, (pr ⁻¹' {x}).ncard = 1)
    {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) (F₁ : FiniteTypeStructure S g n 0)
    {B₀ : Finset F₀.X.carrier} (hB₀ : B₀ ⊆ F₀.P) {X₀' : ClosedRS.{u}} {pr₀ : X₀'.carrier → F₀.X.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ B₀, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ B₀, (pr₀ ⁻¹' {x}).ncard = 1)
    {h : ℕ} (hX₀' : HasGenus X₀'.carrier h) {n'' : ℕ} (hB : B₀.card + 2 * n'' = 2 * n)
    (hh : 2 * h + 2 = 4 * g + B₀.card) (hn'' : 0 < n'') (hgood : 1 < 2 * h + n'' - 1)
    {f₀ : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ}
    (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k) {f : S₀ ≃ₜ S} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    maxDilatationRS f₀ ≤ maxDilatationRS f ∧ (maxDilatationRS f = maxDilatationRS f₀ → ⇑f = ⇑f₀) := by
  obtain ⟨T₀, T₁, _, _, _, _, _, _, _, _, _, _, G₀, G₁, π₀, π₁, ft₀, ft, qt, qt', -, -, hπ₀s, -, -, -, -, hc₀, hc,
    hTa, hft, hKft, hhomt, -, -⟩ := s82lc_lift_punctured F₀ F₁ hB₀ hpr₀ hX₀' hB hh hf₀ hf hhom
  obtain ⟨Y₀, ρ₀, hY₀, hρ₀⟩ := hcov G₀.X (g := h) (r := n'') (Or.inr hn''.ne') G₀.genus G₀.P G₀.card_P
  obtain ⟨h1, h2⟩ := s82lc_uniq_even_of_cover G₀ G₁ hρ₀ hgood hY₀ hTa hft hhomt
  have hK₀ := (teichmullerMap_beltrami hf₀.2).2
  have hKt₀ := (teichmullerMap_beltrami hTa.2).2
  refine ⟨by rw [hK₀, ← hKt₀, ← hKft]; exact h1, fun heq => ?_⟩
  have hfeq := h2 (by rw [hKft, heq, hK₀, hKt₀])
  funext s
  obtain ⟨t, rfl⟩ := hπ₀s s
  rw [← hc t, ← hc₀ t, hfeq]

/-- **Theorem 32.1, `(0, 3)`**: the admissible differentials of a thrice punctured sphere vanish
(`admissibleQD_complex_finrank`: real dimension `2(3·0 - 3 + 3) = 0`), so there is no admissible Teichmüller map. -/
theorem s82lc_uniq_03 (F₀ : FiniteTypeStructure S₀ 0 3 0) {f₀ : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ}
    {k : ℝ} (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k) : False := by
  classical
  have hrank := (admissibleQD_complex_finrank F₀ (by simp [IsExceptionalType])).2
  have : FiniteDimensional ℂ (Submodule.span ℂ (admissibleQDSpace F₀ : Set (F₀.X.carrier → ℂ → ℂ))) :=
    k31p_finite_admissible F₀
  obtain ⟨eR⟩ := k31p_real_equiv F₀
  have : FiniteDimensional ℝ (admissibleQDSpace F₀) := LinearEquiv.finiteDimensional eR
  have h0 : Module.finrank ℝ (admissibleQDSpace F₀) = 0 := by
    have : (Module.finrank ℝ (admissibleQDSpace F₀) : ℤ) = 0 := by rw [hrank]; norm_num
    exact_mod_cast this
  have hbot : admissibleQDSpace F₀ = ⊥ := Submodule.finrank_eq_zero.1 h0
  obtain ⟨qh, hqh, hqeq⟩ := Submodule.mem_map.1 hf₀.1
  rw [hbot, Submodule.mem_bot] at hqh
  apply hf₀.2.initial_ne
  rw [← hqeq, hqh, map_zero]

/-- **Theorem 32.1 from the existence of branched double covers** (`hcov`, the content of
`exists_branched_double_cover`): case analysis on `n`. -/
theorem s82lc_thm32_1_of_cover
    (hcov : ∀ (X : ClosedRS.{u}) {g r : ℕ}, (g ≠ 0 ∨ r ≠ 0) → HasGenus X.carrier g → ∀ P : Finset X.carrier,
      P.card = 2 * r → ∃ (X' : ClosedRS.{u}) (pr : X'.carrier → X.carrier), HasGenus X'.carrier (2 * g + r - 1) ∧
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
        (∀ x ∉ P, (pr ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ P, (pr ⁻¹' {x}).ncard = 1)
    {g n : ℕ} (hex : ¬ IsExceptionalType g n 0) (F₀ : FiniteTypeStructure S₀ g n 0)
    (F₁ : FiniteTypeStructure S g n 0) {f₀ : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ}
    (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k) {f : S₀ ≃ₜ S} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    maxDilatationRS f₀ ≤ maxDilatationRS f ∧ (maxDilatationRS f = maxDilatationRS f₀ → ⇑f = ⇑f₀) := by
  classical
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' n
  · -- `n = 2r`
    subst hr
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · -- closed: `g ≥ 2`
      have hg : 1 < g := by
        by_contra hg
        apply hex
        interval_cases g <;> simp [IsExceptionalType]
      exact s82lc_uniq_closed hg F₀ F₁ hf₀ hf hhom
    by_cases h04 : g = 0 ∧ r = 2
    · -- `(0, 4)`: branch over all four punctures, keep them as punctures: type `(1, 4)`
      obtain ⟨rfl, rfl⟩ := h04
      obtain ⟨X₀', pr₀, hX₀', hpr₀⟩ := hcov F₀.X (g := 0) (r := 2) (Or.inr (by norm_num)) F₀.genus F₀.P F₀.card_P
      exact s82lc_uniq_punctured_of_cover hcov F₀ F₁ (subset_refl _) hpr₀ hX₀' (n'' := 2)
        (by rw [F₀.card_P]) (by rw [F₀.card_P]) (by norm_num) (by norm_num) hf₀ hf hhom
    · -- even, not `(0, 4)`: the cover of genus `2g + r - 1 > 1`
      have hgr : g ≠ 0 ∨ r ≠ 0 := Or.inr hr0.ne'
      obtain ⟨X₀', pr₀, hX₀', hpr₀⟩ := hcov F₀.X hgr F₀.genus F₀.P F₀.card_P
      have hh : 1 < 2 * g + r - 1 := by
        by_contra hh
        apply hex
        have : g = 0 ∧ r ≤ 2 := by omega
        obtain ⟨rfl, hr2⟩ := this
        interval_cases r
        · simp [IsExceptionalType]
        · exact absurd ⟨rfl, rfl⟩ h04
      exact s82lc_uniq_even_of_cover F₀ F₁ hpr₀ hh hX₀' hf₀ hf hhom
  · -- `n = 2r + 1`
    subst hr
    by_cases h03 : g = 0 ∧ r = 1
    · obtain ⟨rfl, rfl⟩ := h03
      exact (s82lc_uniq_03 F₀ hf₀).elim
    -- branch over all punctures but one, `B₀ = P ∖ {p}` (`2r` points), keep all points over `P` as punctures
    have hPne : F₀.P.Nonempty := by
      rw [← Finset.card_pos, F₀.card_P]; omega
    obtain ⟨p, hp⟩ := hPne
    have hBc : (F₀.P.erase p).card = 2 * r := by
      rw [Finset.card_erase_of_mem hp, F₀.card_P]; omega
    have hgr : g ≠ 0 ∨ r ≠ 0 := by
      by_contra h
      push Not at h
      obtain ⟨rfl, rfl⟩ := h
      exact hex (by simp [IsExceptionalType])
    obtain ⟨X₀', pr₀, hX₀', hpr₀⟩ := hcov F₀.X hgr F₀.genus (F₀.P.erase p) hBc
    exact s82lc_uniq_punctured_of_cover hcov F₀ F₁ (Finset.erase_subset p F₀.P) hpr₀ hX₀' (n'' := r + 1)
      (by rw [hBc]; ring) (by rw [hBc]; omega) (by omega) (by omega) hf₀ hf hhom

/-- **Theorem 32.1** (32.1).  Let `S₀` be a non-exceptional surface of type `(g, n)` and
`f₀ : S₀ → S` a Teichmüller map with Beltrami differential `k ω̄/|ω|`, `ω` an admissible quadratic
differential, `k ∈ [0, 1)`.  Then `f₀` is the unique extremal map of its homotopy class: every
quasiconformal `f ≃ f₀` satisfies `K[f₀] ≤ K[f]`, with equality only for `f = f₀`.
(The cases `n` even, `n` odd, and `(0, 4)` are reduced to Theorem 26.2 by branched double
coverings.) -/
theorem s82lc_thm32_1_uniqueness_gn {g n : ℕ} (hex : ¬ IsExceptionalType g n 0) (F₀ : FiniteTypeStructure S₀ g n 0)
    (F₁ : FiniteTypeStructure S g n 0) {f₀ : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ}
    (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k) {f : S₀ ≃ₜ S} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    maxDilatationRS f₀ ≤ maxDilatationRS f ∧ (maxDilatationRS f = maxDilatationRS f₀ → ⇑f = ⇑f₀) := by
  exact s82lc_thm32_1_of_cover (fun X _ _ hgr hX P hP => by
      obtain ⟨X', pr, h1, h2, h3, h4, h5, -⟩ := s82bc_exists_branched_double_cover hgr hX P hP
      exact ⟨X', pr, h1, h2, h3, h4, h5⟩)
    hex F₀ F₁ hf₀ hf hhom

section RelocatedS32

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **Theorem 32.1** (32.1).  Let `S₀` be a non-exceptional surface of type `(g, n)` and
`f₀ : S₀ → S` a Teichmüller map with Beltrami differential `k ω̄/|ω|`, `ω` an admissible quadratic
differential, `k ∈ [0, 1)`.  Then `f₀` is the unique extremal map of its homotopy class: every
quasiconformal `f ≃ f₀` satisfies `K[f₀] ≤ K[f]`, with equality only for `f = f₀`.
(The cases `n` even, `n` odd, and `(0, 4)` are reduced to Theorem 26.2 by branched double
coverings.) -/
theorem thm32_1_uniqueness_gn {g n : ℕ} (hex : ¬ IsExceptionalType g n 0) (F₀ : FiniteTypeStructure S₀ g n 0)
    (F₁ : FiniteTypeStructure S g n 0) {f₀ : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ}
    (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k) {f : S₀ ≃ₜ S} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    maxDilatationRS f₀ ≤ maxDilatationRS f ∧ (maxDilatationRS f = maxDilatationRS f₀ → ⇑f = ⇑f₀) := by
  exact s82lc_thm32_1_uniqueness_gn hex F₀ F₁ hf₀ hf hhom

end RelocatedS32

end LiZhongQC
