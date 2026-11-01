import LiZhongQC.Lemmas.FiniteTypeComparisonEven
import LiZhongQC.Lemmas.Thm321

/-!
# Teichmüller's comparison inequality for odd `n` and type `(0, 4)` (`s82cmp_`, L32329)

Lift through a two-sheeted cover branched over an even subset of the punctures and punctured over all of them
(`s82lc_lift_punctured`), apply the even case `s82cmp_core_even` upstairs and descend the areas through the proper
two-to-one projection (`s82cmp_cover_integral_p`, a proper-cover version of `s82cmp_cover_integral`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]


/-- Two holomorphic sections of a two-sheeted cover over a small neighbourhood of a point off the branch
set (proper version of `s82cmp_sections`): `pr⁻¹ V = σ₁ V ⊔ σ₂ V`, `pr ∘ σₖ = id` on `V`. The data are the outputs of `s82lc_local_form` (local
holomorphic inverses). -/
theorem s82cmp_cover_sections {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [T2Space Y] {X : ClosedRS.{u}} {P : Finset X.carrier} {pr : Y → X.carrier}
    (hcont : Continuous pr)
    (hclosed : ∀ C : Set Y, IsClosed C → ∀ p ∉ P, p ∉ pr '' C → (pr '' C)ᶜ ∈ 𝓝 p) (hfib : ∀ x ∉ P, (pr ⁻¹' {x}).ncard = 2)
    (hloc : ∀ y, pr y ∉ P → ∃ e : OpenPartialHomeomorph Y X.carrier, y ∈ e.source ∧
      EqOn pr e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    {p : X.carrier} (hp : p ∉ P) {W : Set X.carrier} (hW : W ∈ 𝓝 p)
    (T : Y → Set Y) (hT : ∀ y, T y ∈ 𝓝 y) :
    ∃ (V : Set X.carrier) (σ₁ σ₂ : OpenPartialHomeomorph X.carrier Y) (y₁ y₂ : Y),
      σ₁ p = y₁ ∧ σ₂ p = y₂ ∧ σ₁ '' V ⊆ T y₁ ∧ σ₂ '' V ⊆ T y₂ ∧
      IsOpen V ∧ p ∈ V ∧ V ⊆ W ∧ V ⊆ σ₁.source ∧ V ⊆ σ₂.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ₁ V ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ₂ V ∧
      (∀ v ∈ V, pr (σ₁ v) = v) ∧ (∀ v ∈ V, pr (σ₂ v) = v) ∧
      Disjoint (σ₁ '' V) (σ₂ '' V) ∧ pr ⁻¹' V = σ₁ '' V ∪ σ₂ '' V ∧
      IsOpen (σ₁ '' V) ∧ IsOpen (σ₂ '' V) := by
  classical
  obtain ⟨y₁, y₂, hne, hfibre⟩ := Set.ncard_eq_two.1 (hfib p hp)
  have hy₁ : pr y₁ = p := by
    have : y₁ ∈ pr ⁻¹' {p} := by rw [hfibre]; simp
    exact this
  have hy₂ : pr y₂ = p := by
    have : y₂ ∈ pr ⁻¹' {p} := by rw [hfibre]; simp
    exact this
  obtain ⟨e₁, he₁s, he₁eq, he₁d⟩ := hloc y₁ (by rw [hy₁]; exact hp)
  obtain ⟨e₂, he₂s, he₂eq, he₂d⟩ := hloc y₂ (by rw [hy₂]; exact hp)
  -- disjoint open neighbourhoods of the two fibre points inside the sources
  obtain ⟨B₁, B₂, hB₁, hB₂, hy₁B, hy₂B, hdis⟩ := t2_separation hne
  set A₁ := B₁ ∩ e₁.source ∩ interior (T y₁) with hA₁
  set A₂ := B₂ ∩ e₂.source ∩ interior (T y₂) with hA₂
  have hA₁o : IsOpen A₁ := (hB₁.inter e₁.open_source).inter isOpen_interior
  have hA₂o : IsOpen A₂ := (hB₂.inter e₂.open_source).inter isOpen_interior
  have hA₁s : A₁ ⊆ e₁.source := fun y hy => hy.1.2
  have hA₂s : A₂ ⊆ e₂.source := fun y hy => hy.1.2
  have hy₁A : y₁ ∈ A₁ := ⟨⟨hy₁B, he₁s⟩, mem_interior_iff_mem_nhds.2 (hT y₁)⟩
  have hy₂A : y₂ ∈ A₂ := ⟨⟨hy₂B, he₂s⟩, mem_interior_iff_mem_nhds.2 (hT y₂)⟩
  have hAdis : Disjoint A₁ A₂ := hdis.mono (fun y hy => hy.1.1) (fun y hy => hy.1.1)
  -- the image of the closed set of points not in `A₁ ∪ A₂` avoids a neighbourhood of `p`
  have hpC : p ∉ pr '' (A₁ ∪ A₂)ᶜ := by
    rintro ⟨y, hy, hyp⟩
    have : y ∈ pr ⁻¹' {p} := hyp
    rw [hfibre] at this
    rcases this with rfl | rfl
    · exact hy (Or.inl hy₁A)
    · exact hy (Or.inr hy₂A)
  set V : Set X.carrier := e₁ '' A₁ ∩ e₂ '' A₂ ∩ interior (pr '' (A₁ ∪ A₂)ᶜ)ᶜ ∩ interior W with hV
  have hVo : IsOpen V :=
    (((e₁.isOpen_image_of_subset_source hA₁o hA₁s).inter
      (e₂.isOpen_image_of_subset_source hA₂o hA₂s)).inter isOpen_interior).inter isOpen_interior
  have hpV : p ∈ V := by
    refine ⟨⟨⟨?_, ?_⟩, mem_interior_iff_mem_nhds.2
      (hclosed _ (hA₁o.union hA₂o).isClosed_compl p hp hpC)⟩, mem_interior_iff_mem_nhds.2 hW⟩
    · exact ⟨y₁, hy₁A, by rw [← he₁eq he₁s, hy₁]⟩
    · exact ⟨y₂, hy₂A, by rw [← he₂eq he₂s, hy₂]⟩
  have hV1 : V ⊆ e₁ '' A₁ := fun v hv => hv.1.1.1
  have hV2 : V ⊆ e₂ '' A₂ := fun v hv => hv.1.1.2
  have hVC : ∀ v ∈ V, v ∉ pr '' (A₁ ∪ A₂)ᶜ := fun v hv => interior_subset hv.1.2
  have hVW : V ⊆ W := fun v hv => interior_subset hv.2
  have hs1 : ∀ v ∈ V, e₁.symm v ∈ A₁ := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hV1 hv
    rw [e₁.left_inv (hA₁s ha)]
    exact ha
  have hs2 : ∀ v ∈ V, e₂.symm v ∈ A₂ := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hV2 hv
    rw [e₂.left_inv (hA₂s ha)]
    exact ha
  have ht1 : ∀ v ∈ V, v ∈ e₁.target := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hV1 hv
    exact e₁.map_source (hA₁s ha)
  have ht2 : ∀ v ∈ V, v ∈ e₂.target := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := hV2 hv
    exact e₂.map_source (hA₂s ha)
  have hpr1 : ∀ v ∈ V, pr (e₁.symm v) = v := by
    intro v hv
    rw [he₁eq (e₁.map_target (ht1 v hv)), e₁.right_inv (ht1 v hv)]
  have hpr2 : ∀ v ∈ V, pr (e₂.symm v) = v := by
    intro v hv
    rw [he₂eq (e₂.map_target (ht2 v hv)), e₂.right_inv (ht2 v hv)]
  have himg1 : e₁.symm '' V = A₁ ∩ pr ⁻¹' V := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hs1 v hv, by simpa [hpr1 v hv] using hv⟩
    · rintro ⟨hyA, hyV⟩
      refine ⟨pr y, hyV, ?_⟩
      rw [he₁eq (hA₁s hyA), e₁.left_inv (hA₁s hyA)]
  have himg2 : e₂.symm '' V = A₂ ∩ pr ⁻¹' V := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨hs2 v hv, by simpa [hpr2 v hv] using hv⟩
    · rintro ⟨hyA, hyV⟩
      refine ⟨pr y, hyV, ?_⟩
      rw [he₂eq (hA₂s hyA), e₂.left_inv (hA₂s hyA)]
  have hσ1p : e₁.symm p = y₁ := by
    have h : e₁ y₁ = p := (he₁eq he₁s).symm.trans hy₁
    rw [← h]; exact e₁.left_inv he₁s
  have hσ2p : e₂.symm p = y₂ := by
    have h : e₂ y₂ = p := (he₂eq he₂s).symm.trans hy₂
    rw [← h]; exact e₂.left_inv he₂s
  refine ⟨V, e₁.symm, e₂.symm, y₁, y₂, hσ1p, hσ2p, ?_, ?_, hVo, hpV, hVW, ?_, ?_, he₁d.mono ?_, he₂d.mono ?_, hpr1, hpr2, ?_, ?_, ?_, ?_⟩
  · rw [himg1]; exact fun y hy => interior_subset hy.1.2
  · rw [himg2]; exact fun y hy => interior_subset hy.1.2
  · intro v hv; rw [OpenPartialHomeomorph.symm_source]; exact ht1 v hv
  · intro v hv; rw [OpenPartialHomeomorph.symm_source]; exact ht2 v hv
  · exact ht1
  · exact ht2
  · rw [himg1, himg2]
    exact hAdis.mono inter_subset_left inter_subset_left
  · ext y
    constructor
    · intro hyV
      have hyA : y ∈ A₁ ∪ A₂ := by
        by_contra hy
        exact hVC _ hyV ⟨y, hy, rfl⟩
      rcases hyA with hyA | hyA
      · left; rw [himg1]; exact ⟨hyA, hyV⟩
      · right; rw [himg2]; exact ⟨hyA, hyV⟩
    · rintro (h | h)
      · rw [himg1] at h; exact h.2
      · rw [himg2] at h; exact h.2
  · rw [himg1]; exact hA₁o.inter (hVo.preimage hcont)
  · rw [himg2]; exact hA₂o.inter (hVo.preimage hcont)



section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

omit [T2Space S₀] in
/-- **Sheet relation.**  On a sheet `σ` of a two-sheeted cover over `V`, with `ι⁻¹ V` inside a chart of `S₀` and
`σ V` inside a chart of `Y`, the lifted differential is the pull-back of `r` through `σ ∘ ι`, in any pair of charts
`x ∋ a`, `ŷ ∋ σ(ι a)`. -/
theorem s82cmp_cover_sheet_relation {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [T2Space Y]
    {pr : Y → F₀.X.carrier} (hcont : Continuous pr)
    {r : S₀ → ℂ → ℂ} {qh : Y → ℂ → ℂ} (hr : IsHolQuadDiff r) (hq : IsHolQuadDiff qh)
    (hrel : ∀ (y : Y) (s : S₀), pr y = F₀.ι s → ∀ᶠ z in 𝓝 (chartAt ℂ y y),
      qh y z = r s (chartAt ℂ s (Function.invFun F₀.ι (pr ((chartAt ℂ y).symm z)))) *
        deriv (fun w => chartAt ℂ s (Function.invFun F₀.ι (pr ((chartAt ℂ y).symm w)))) z ^ 2)
    {V : Set F₀.X.carrier} (hVo : IsOpen V) (hVr : V ⊆ Set.range F₀.ι)
    {σ : OpenPartialHomeomorph F₀.X.carrier Y} (hVσ : V ⊆ σ.source)
    (hσd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ V) (hσpr : ∀ v ∈ V, pr (σ v) = v)
    (hσo : IsOpen (σ '' V))
    {a : S₀} (haV : F₀.ι a ∈ V) {x : S₀} {ŷ : Y} (hax : a ∈ (chartAt ℂ x).source)
    (hŷ : σ (F₀.ι a) ∈ (chartAt ℂ ŷ).source) :
    r x (chartAt ℂ x a) = qh ŷ (chartAt ℂ ŷ (σ (F₀.ι a))) *
      deriv (fun w => chartAt ℂ ŷ (σ (F₀.ι ((chartAt ℂ x).symm w)))) (chartAt ℂ x a) ^ 2 := by
  classical
  have : Nonempty S₀ := ⟨a⟩
  have hemb := F₀.embedding
  set Φ : S₀ → Y := fun b => σ (F₀.ι b) with hΦ
  set G : Y → S₀ := fun y => Function.invFun F₀.ι (pr y) with hG
  set U' : Set S₀ := F₀.ι ⁻¹' V ∩ (chartAt ℂ a).source with hU'
  have hU'o : IsOpen U' := (hVo.preimage hemb.continuous).inter (chartAt ℂ a).open_source
  have haU' : a ∈ U' := ⟨haV, mem_chart_source ℂ a⟩
  have hΦd : ∀ b ∈ U', MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) Φ b := by
    intro b hb
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F₀.ι b := F₀.holomorphic b
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) σ (F₀.ι b) :=
      (hσd (F₀.ι b) hb.1).mdifferentiableAt (hVo.mem_nhds hb.1)
    exact h2.comp b h1
  have hinj : InjOn Φ U' := by
    intro b₁ hb₁ b₂ hb₂ h
    exact hemb.isEmbedding.injective (σ.injOn (hVσ hb₁.1) (hVσ hb₂.1) h)
  have hGΦ : ∀ b ∈ U', G (Φ b) = b := by
    intro b hb
    simp only [hG, hΦ]
    rw [hσpr _ hb.1]
    exact Function.leftInverse_invFun hemb.isEmbedding.injective b
  have hy0 : Φ a ∈ σ '' V := ⟨F₀.ι a, haV, rfl⟩
  have hGc : ContinuousAt G (Φ a) := by
    have h1 : pr (Φ a) = F₀.ι a := hσpr _ haV
    have h2 : ContinuousAt (Function.invFun F₀.ι) (pr (Φ a)) := by
      rw [h1]; exact s82cmp_invFun_continuousAt hemb ⟨a, rfl⟩
    exact h2.comp hcont.continuousAt
  have hΦG : ∀ᶠ y in 𝓝 (Φ a), Φ (G y) = y ∧ G y ∈ U' := by
    have h1 : ∀ᶠ y in 𝓝 (Φ a), G y ∈ (chartAt ℂ a).source := by
      refine hGc.eventually ?_
      have : G (Φ a) = a := hGΦ a haU'
      rw [this]
      exact (chartAt ℂ a).open_source.mem_nhds (mem_chart_source ℂ a)
    filter_upwards [hσo.mem_nhds hy0, h1] with y hy hys
    obtain ⟨v, hv, rfl⟩ := hy
    have hpv : pr (σ v) = v := hσpr v hv
    obtain ⟨c, hc⟩ := hVr hv
    have hGv : G (σ v) = c := by
      simp only [hG]
      rw [hpv, ← hc]
      exact Function.leftInverse_invFun hemb.isEmbedding.injective c
    refine ⟨?_, ?_, hys⟩
    · simp only [hΦ, hGv, hc]
    · show F₀.ι (G (σ v)) ∈ V
      rw [hGv, hc]; exact hv
  have hrel0 : qh (Φ a) (chartAt ℂ (Φ a) (Φ a)) =
      r a (chartAt ℂ a (G ((chartAt ℂ (Φ a)).symm (chartAt ℂ (Φ a) (Φ a))))) *
        deriv (fun v => chartAt ℂ a (G ((chartAt ℂ (Φ a)).symm v))) (chartAt ℂ (Φ a) (Φ a)) ^ 2 := by
    have h := (hrel (Φ a) a (hσpr _ haV)).self_of_nhds
    exact h
  exact s82cmp_pullback_pointwise hr hq hU'o haU' (fun b hb => hb.2) hΦd hinj hGΦ hΦG hGc hrel0 hax hŷ

end

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

omit [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] in
/-- Per-point sheet data of a two-sheeted cover: a neighbourhood `V` of `ι s` in the range of `ι`, two sections
`sh false`, `sh true` over `V` with images inside chart sources, covering `pr⁻¹ V`. -/
theorem s82cmp_cover_sheet_data {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [T2Space Y]
    {pr : Y → F₀.X.carrier} (hcont : Continuous pr)
    (hclosed : ∀ C : Set Y, IsClosed C → ∀ p ∉ F₀.P, p ∉ pr '' C → (pr '' C)ᶜ ∈ 𝓝 p)
    (hfib : ∀ x ∉ F₀.P, (pr ⁻¹' {x}).ncard = 2)
    (hloc : ∀ y, pr y ∉ F₀.P → ∃ e : OpenPartialHomeomorph Y F₀.X.carrier, y ∈ e.source ∧
      EqOn pr e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target) (s : S₀) :
    ∃ (V : Set F₀.X.carrier) (sh : Bool → OpenPartialHomeomorph F₀.X.carrier Y)
      (ŷ : Bool → Y),
      IsOpen V ∧ F₀.ι s ∈ V ∧ V ⊆ Set.range F₀.ι ∧ (∀ k, V ⊆ (sh k).source) ∧
      (∀ k, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (sh k) V) ∧ (∀ k, ∀ v ∈ V, pr (sh k v) = v) ∧
      (∀ k, IsOpen (sh k '' V)) ∧ (∀ k, sh k (F₀.ι s) = ŷ k) ∧
      (∀ k, sh k '' V ⊆ (chartAt ℂ (ŷ k)).source) ∧
      Disjoint (sh false '' V) (sh true '' V) ∧ pr ⁻¹' V = sh false '' V ∪ sh true '' V := by
  have hP0 : F₀.P = F₀.P := rfl
  have hrange : Set.range F₀.ι = (↑F₀.P : Set F₀.X.carrier)ᶜ := by
    rw [F₀.range_ι]; simp
  have hp : F₀.ι s ∉ F₀.P := by
    have : F₀.ι s ∈ Set.range F₀.ι := ⟨s, rfl⟩
    rw [hrange] at this
    exact this
  have hW : Set.range F₀.ι ∈ 𝓝 (F₀.ι s) := F₀.embedding.isOpen_range.mem_nhds ⟨s, rfl⟩
  obtain ⟨V, σ₁, σ₂, y₁, y₂, h1, h2, hT1, hT2, hVo, hpV, hVW, hV1, hV2, hd1, hd2, hp1, hp2, hdis, hpre,
    hio1, hio2⟩ := s82cmp_cover_sections hcont hclosed hfib hloc hp hW (fun y => (chartAt ℂ y).source)
      (fun y => (chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y))
  refine ⟨V, fun k => cond k σ₂ σ₁, fun k => cond k y₂ y₁, hVo, hpV, hVW, ?_, ?_, ?_, ?_, ?_, ?_, hdis, hpre⟩
  · intro k; cases k
    · exact hV1
    · exact hV2
  · intro k; cases k
    · exact hd1
    · exact hd2
  · intro k; cases k
    · exact hp1
    · exact hp2
  · intro k; cases k
    · exact hio1
    · exact hio2
  · intro k; cases k
    · exact h1
    · exact h2
  · intro k; cases k
    · exact hT1
    · exact hT2

end

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

omit [T2Space S₀] [ConnectedSpace S₀] in
/-- The chart expression `T = φ_ŷ ∘ σ ∘ ι ∘ φ_x⁻¹` of a sheet: it maps `φ_x(A)` onto `φ_ŷ(σ ι A)`, is holomorphic
and injective there. -/
theorem s82cmp_cover_sheet_T {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [T2Space Y]
    {V : Set F₀.X.carrier} (hVo : IsOpen V)
    {σ : OpenPartialHomeomorph F₀.X.carrier Y} (hVσ : V ⊆ σ.source)
    (hσd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ V) {x : S₀} {ŷ : Y}
    (hŷ : σ '' V ⊆ (chartAt ℂ ŷ).source)
    {A : Set S₀} (hA : A ⊆ F₀.ι ⁻¹' V) (hAx : A ⊆ (chartAt ℂ x).source) :
    (fun w => chartAt ℂ ŷ (σ (F₀.ι ((chartAt ℂ x).symm w)))) '' (chartAt ℂ x '' A) =
        chartAt ℂ ŷ '' (σ '' (F₀.ι '' A)) ∧
      (∀ w ∈ chartAt ℂ x '' A,
        DifferentiableAt ℂ (fun w => chartAt ℂ ŷ (σ (F₀.ι ((chartAt ℂ x).symm w)))) w) ∧
      InjOn (fun w => chartAt ℂ ŷ (σ (F₀.ι ((chartAt ℂ x).symm w)))) (chartAt ℂ x '' A) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨σ (F₀.ι a), ⟨F₀.ι a, ⟨a, ha, rfl⟩, rfl⟩, ?_⟩
      simp only [(chartAt ℂ x).left_inv (hAx ha)]
    · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, rfl⟩
      refine ⟨chartAt ℂ x a, ⟨a, ha, rfl⟩, ?_⟩
      simp only [(chartAt ℂ x).left_inv (hAx ha)]
  · rintro w ⟨a, ha, rfl⟩
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F₀.ι a := F₀.holomorphic a
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) σ (F₀.ι a) :=
      (hσd (F₀.ι a) (hA ha)).mdifferentiableAt (hVo.mem_nhds (hA ha))
    have h3 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun b => σ (F₀.ι b)) a := h2.comp a h1
    exact ((s23_mdifferentiableAt_iff (hAx ha) (hŷ ⟨F₀.ι a, hA ha, rfl⟩)).1 h3).2
  · rintro w₁ ⟨a₁, ha₁, rfl⟩ w₂ ⟨a₂, ha₂, rfl⟩ h
    simp only [(chartAt ℂ x).left_inv (hAx ha₁), (chartAt ℂ x).left_inv (hAx ha₂)] at h
    have h1 := (chartAt ℂ ŷ).injOn (hŷ ⟨F₀.ι a₁, hA ha₁, rfl⟩) (hŷ ⟨F₀.ι a₂, hA ha₂, rfl⟩) h
    have h2 := σ.injOn (hVσ (hA ha₁)) (hVσ (hA ha₂)) h1
    rw [F₀.embedding.isEmbedding.injective h2]

omit [T2Space S₀] [ConnectedSpace S₀] in
/-- Measurability of the chart image of a sheet piece (Lusin–Souslin). -/
theorem s82cmp_cover_sheet_measurable {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [T2Space Y]
    {V : Set F₀.X.carrier} (hVo : IsOpen V)
    {σ : OpenPartialHomeomorph F₀.X.carrier Y} (hVσ : V ⊆ σ.source)
    (hσd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ V) {x : S₀} {ŷ : Y}
    (hŷ : σ '' V ⊆ (chartAt ℂ ŷ).source)
    {A : Set S₀} (hA : A ⊆ F₀.ι ⁻¹' V) (hAx : A ⊆ (chartAt ℂ x).source)
    (hAm : MeasurableSet (chartAt ℂ x '' A)) :
    MeasurableSet (chartAt ℂ ŷ '' (σ '' (F₀.ι '' A))) := by
  obtain ⟨himg, hd, hinj⟩ := s82cmp_cover_sheet_T F₀ hVo hVσ hσd hŷ hA hAx
  rw [← himg]
  exact hAm.image_of_continuousOn_injOn
    (continuousOn_of_forall_continuousAt fun w hw => (hd w hw).continuousAt) hinj

omit [T2Space S₀] in
/-- **Integral over one sheet.**  The area integral of the lifted differential over the image of a piece `A`
of `S₀` along a sheet equals the integral of `r` over `A`. -/
theorem s82cmp_cover_sheet_integral {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [T2Space Y]
    {pr : Y → F₀.X.carrier} (hcont : Continuous pr)
    {r : S₀ → ℂ → ℂ} {qh : Y → ℂ → ℂ} (hr : IsHolQuadDiff r) (hq : IsHolQuadDiff qh)
    (hrel : ∀ (y : Y) (s : S₀), pr y = F₀.ι s → ∀ᶠ z in 𝓝 (chartAt ℂ y y),
      qh y z = r s (chartAt ℂ s (Function.invFun F₀.ι (pr ((chartAt ℂ y).symm z)))) *
        deriv (fun w => chartAt ℂ s (Function.invFun F₀.ι (pr ((chartAt ℂ y).symm w)))) z ^ 2)
    (U : S₀ → ℝ≥0∞) (Uh : Y → ℝ≥0∞) (hU : ∀ y s, pr y = F₀.ι s → Uh y = U s)
    {V : Set F₀.X.carrier} (hVo : IsOpen V) (hVr : V ⊆ Set.range F₀.ι)
    {σ : OpenPartialHomeomorph F₀.X.carrier Y} (hVσ : V ⊆ σ.source)
    (hσd : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) σ V) (hσpr : ∀ v ∈ V, pr (σ v) = v)
    (hσo : IsOpen (σ '' V)) {x : S₀} {ŷ : Y} (hŷ : σ '' V ⊆ (chartAt ℂ ŷ).source)
    {A : Set S₀} (hA : A ⊆ F₀.ι ⁻¹' V) (hAx : A ⊆ (chartAt ℂ x).source)
    (hAm : MeasurableSet (chartAt ℂ x '' A)) :
    ∫⁻ z in chartAt ℂ ŷ '' (σ '' (F₀.ι '' A)), Uh ((chartAt ℂ ŷ).symm z) * ENNReal.ofReal ‖qh ŷ z‖ =
      ∫⁻ w in chartAt ℂ x '' A, U ((chartAt ℂ x).symm w) * ENNReal.ofReal ‖r x w‖ := by
  classical
  obtain ⟨himg, hd, hinj⟩ := s82cmp_cover_sheet_T F₀ hVo hVσ hσd hŷ hA hAx
  have hrel' : ∀ w ∈ chartAt ℂ x '' A, r x w = qh ŷ (chartAt ℂ ŷ (σ (F₀.ι ((chartAt ℂ x).symm w)))) *
      deriv (fun w => chartAt ℂ ŷ (σ (F₀.ι ((chartAt ℂ x).symm w)))) w ^ 2 := by
    rintro w ⟨a, ha, rfl⟩
    have h := s82cmp_cover_sheet_relation F₀ hcont hr hq hrel hVo hVr hVσ hσd hσpr hσo (hA ha) (hAx ha)
      (hŷ ⟨F₀.ι a, hA ha, rfl⟩)
    simp only [(chartAt ℂ x).left_inv (hAx ha)]
    exact h
  rw [← himg]
  have key := s82cmp_lintegral_pullback (F := fun z => Uh ((chartAt ℂ ŷ).symm z)) hAm hd hinj hrel'
  rw [key]
  refine setLIntegral_congr_fun hAm fun w hw => ?_
  obtain ⟨a, ha, rfl⟩ := hw
  have hp : pr (σ (F₀.ι a)) = F₀.ι a := hσpr _ (hA ha)
  simp only [(chartAt ℂ x).left_inv (hAx ha)]
  rw [(chartAt ℂ ŷ).left_inv (hŷ ⟨F₀.ι a, hA ha, rfl⟩), hU _ _ hp]

end

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

omit [T2Space S₀] in
/-- **Change of variables for a two-sheeted cover, proper version** (`s82cmp_cover_integral` for a cover `Y` that
need not be compact: the images of closed sets avoid neighbourhoods of the points off `P`, and the fibres over `P`
are finite).  If the differential `qh` on the cover
`Y` is the chart-wise pull-back of the differential `r` on `S₀ = X ∖ P` (`hrel`), and `Uh` is the pull-back of the
point function `U`, then the area integrals satisfy `∫_Y Uh dA_qh = 2 ∫_{S₀} U dA_r`. -/
theorem s82cmp_cover_integral_p {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [T2Space Y]
    {pr : Y → F₀.X.carrier} (hcont : Continuous pr)
    (hclosed : ∀ C : Set Y, IsClosed C → ∀ p ∉ F₀.P, p ∉ pr '' C → (pr '' C)ᶜ ∈ 𝓝 p)
    (hfib : ∀ x ∉ F₀.P, (pr ⁻¹' {x}).ncard = 2) (hfibP : ∀ x ∈ F₀.P, (pr ⁻¹' {x}).Finite)
    (hloc : ∀ y, pr y ∉ F₀.P → ∃ e : OpenPartialHomeomorph Y F₀.X.carrier, y ∈ e.source ∧
      EqOn pr e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    {r : S₀ → ℂ → ℂ} {qh : Y → ℂ → ℂ} (hr : IsHolQuadDiff r) (hq : IsHolQuadDiff qh)
    (hrel : ∀ (y : Y) (s : S₀), pr y = F₀.ι s → ∀ᶠ z in 𝓝 (chartAt ℂ y y),
      qh y z = r s (chartAt ℂ s (Function.invFun F₀.ι (pr ((chartAt ℂ y).symm z)))) *
        deriv (fun w => chartAt ℂ s (Function.invFun F₀.ι (pr ((chartAt ℂ y).symm w)))) z ^ 2)
    (U : S₀ → ℝ≥0∞) (Uh : Y → ℝ≥0∞) (hU : ∀ y s, pr y = F₀.ι s → Uh y = U s) :
    surfaceIntegral qh (fun y z => Uh ((chartAt ℂ y).symm z)) =
      2 * surfaceIntegral r (fun x z => U ((chartAt ℂ x).symm z)) := by
  classical
  have : Nonempty S₀ := ConnectedSpace.toNonempty
  have : SecondCountableTopology F₀.X.carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ℂ F₀.X.carrier
  have : SecondCountableTopology S₀ := F₀.embedding.isEmbedding.secondCountableTopology
  have hrange : Set.range F₀.ι = (↑F₀.P : Set F₀.X.carrier)ᶜ := by
    rw [F₀.range_ι]; simp
  choose V sh ŷ hVo hpV hVr hVs hsd hspr hso hshy hshs hdis hpre using
    s82cmp_cover_sheet_data F₀ hcont hclosed hfib hloc
  obtain ⟨x, P, hP, hPV⟩ := s82cmp_exists_chartPartition
    (fun s => F₀.ι ⁻¹' V s ∩ (chartAt ℂ s).source)
    (fun s => ((hVo s).preimage F₀.embedding.continuous).inter (chartAt ℂ s).open_source)
    (fun s => ⟨hpV s, mem_chart_source ℂ s⟩) (fun s => inter_subset_right)
  have hS := s26v_surfaceIntegral_eq_tsum hr U hP
  -- the pieces of `S₀`
  have hPι : ∀ i, P i ⊆ F₀.ι ⁻¹' V (x i) := fun i => (hPV i).trans inter_subset_left
  have hPx : ∀ i, P i ⊆ (chartAt ℂ (x i)).source := fun i => (hP.1 i).1
  have hPm : ∀ i, MeasurableSet (chartAt ℂ (x i) '' P i) := fun i => (hP.1 i).2
  -- the exceptional fibre
  set B : Set Y := pr ⁻¹' (↑F₀.P : Set F₀.X.carrier) with hB
  have hBfin : B.Finite := by
    have : B = ⋃ p ∈ F₀.P, pr ⁻¹' {p} := by
      ext y; simp [hB]
    rw [this]
    exact F₀.P.finite_toSet.biUnion fun p hp =>
      hfibP p hp
  have : Finite B := hBfin.to_subtype
  -- the index type of the lifted partition
  obtain ⟨hden⟩ := nonempty_denumerable ((ℕ × Bool) ⊕ ↥B)
  have := hden
  let e : ((ℕ × Bool) ⊕ ↥B) ≃ ℕ := Denumerable.eqv _
  let xh : ((ℕ × Bool) ⊕ ↥B) → Y :=
    Sum.elim (fun ik => sh (x ik.1) ik.2 (F₀.ι (x ik.1))) (fun b => (b : Y))
  let Ph : ((ℕ × Bool) ⊕ ↥B) → Set Y :=
    Sum.elim (fun ik => sh (x ik.1) ik.2 '' (F₀.ι '' P ik.1)) (fun b => {(b : Y)})
  have hPhV : ∀ i k, sh (x i) k '' (F₀.ι '' P i) ⊆ sh (x i) k '' V (x i) := fun i k =>
    image_mono (by rintro _ ⟨a, ha, rfl⟩; exact hPι i ha)
  have hPh_sub : ∀ j, Ph j ⊆ (chartAt ℂ (xh j)).source := by
    rintro (⟨i, k⟩ | b)
    · show sh (x i) k '' (F₀.ι '' P i) ⊆ (chartAt ℂ (sh (x i) k (F₀.ι (x i)))).source
      rw [hshy (x i) k]
      exact (hPhV i k).trans (hshs (x i) k)
    · show {(b : Y)} ⊆ (chartAt ℂ (b : Y)).source
      simp
  have hPh_meas : ∀ j, MeasurableSet (chartAt ℂ (xh j) '' Ph j) := by
    rintro (⟨i, k⟩ | b)
    · show MeasurableSet (chartAt ℂ (sh (x i) k (F₀.ι (x i))) ''
        (sh (x i) k '' (F₀.ι '' P i)))
      rw [hshy (x i) k]
      exact s82cmp_cover_sheet_measurable F₀ (hVo (x i)) (hVs (x i) k) (hsd (x i) k) (hshs (x i) k)
        (hPι i) (hPx i) (hPm i)
    · show MeasurableSet (chartAt ℂ (b : Y) '' {(b : Y)})
      rw [Set.image_singleton]
      exact measurableSet_singleton _
  have hpr_Ph : ∀ i k, ∀ y ∈ sh (x i) k '' (F₀.ι '' P i), ∃ a ∈ P i, pr y = F₀.ι a ∧
      y = sh (x i) k (F₀.ι a) := by
    rintro i k _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, hspr (x i) k _ (hPι i ha), rfl⟩
  have hPh_disj : Pairwise (fun j j' => Disjoint (Ph j) (Ph j')) := by
    rintro (⟨i, k⟩ | b) (⟨i', k'⟩ | b') hne
    · -- two sheet pieces
      rw [Set.disjoint_left]
      intro y hy hy'
      obtain ⟨a, ha, hpa, hya⟩ := hpr_Ph i k y hy
      obtain ⟨a', ha', hpa', hya'⟩ := hpr_Ph i' k' y hy'
      by_cases hii : i = i'
      · subst hii
        have hkk : k ≠ k' := fun h => hne (by rw [h])
        have hV1 := hPhV i k hy
        have hV2 := hPhV i k' hy'
        cases k <;> cases k'
        · exact hkk rfl
        · exact (Set.disjoint_left.1 (hdis (x i))) hV1 hV2
        · exact (Set.disjoint_left.1 (hdis (x i))) hV2 hV1
        · exact hkk rfl
      · have : F₀.ι a = F₀.ι a' := hpa.symm.trans hpa'
        have haa : a = a' := F₀.embedding.isEmbedding.injective this
        exact (Set.disjoint_left.1 (hP.2.1 hii)) ha (haa ▸ ha')
    · rw [Set.disjoint_left]
      intro y hy hy'
      obtain ⟨a, ha, hpa, hya⟩ := hpr_Ph i k y hy
      have hyb : y = (b' : Y) := hy'
      have hb : pr (b' : Y) ∈ (↑F₀.P : Set F₀.X.carrier) := b'.2
      rw [← hyb, hpa] at hb
      have : F₀.ι a ∈ Set.range F₀.ι := ⟨a, rfl⟩
      rw [hrange] at this
      exact this hb
    · rw [Set.disjoint_left]
      intro y hy hy'
      obtain ⟨a, ha, hpa, hya⟩ := hpr_Ph i' k' y hy'
      have hyb : y = (b : Y) := hy
      have hb : pr (b : Y) ∈ (↑F₀.P : Set F₀.X.carrier) := b.2
      rw [← hyb, hpa] at hb
      have : F₀.ι a ∈ Set.range F₀.ι := ⟨a, rfl⟩
      rw [hrange] at this
      exact this hb
    · rw [Set.disjoint_left]
      intro y hy hy'
      have h1 : y = (b : Y) := hy
      have h2 : y = (b' : Y) := hy'
      exact hne (congrArg Sum.inr (Subtype.ext (h1.symm.trans h2)))
  have hPh_cover : (⋃ j, Ph j) = Set.univ := by
    rw [eq_univ_iff_forall]
    intro y
    by_cases hy : pr y ∈ (↑F₀.P : Set F₀.X.carrier)
    · exact mem_iUnion.2 ⟨Sum.inr ⟨y, hy⟩, rfl⟩
    · have hyr : pr y ∈ Set.range F₀.ι := by rw [hrange]; exact hy
      obtain ⟨s, hs⟩ := hyr
      obtain ⟨i, hi⟩ := mem_iUnion.1 (hP.2.2.symm ▸ mem_univ s : s ∈ ⋃ i, P i)
      have hsV : pr y ∈ V (x i) := by rw [← hs]; exact hPι i hi
      have hy2 : y ∈ pr ⁻¹' V (x i) := hsV
      rw [hpre (x i)] at hy2
      rcases hy2 with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
      · refine mem_iUnion.2 ⟨Sum.inl (i, false), ?_⟩
        have hpv : pr (sh (x i) false v) = v := hspr (x i) false v hv
        have : v = F₀.ι s := hpv.symm.trans hs.symm
        subst this
        exact ⟨F₀.ι s, ⟨s, hi, rfl⟩, rfl⟩
      · refine mem_iUnion.2 ⟨Sum.inl (i, true), ?_⟩
        have hpv : pr (sh (x i) true v) = v := hspr (x i) true v hv
        have : v = F₀.ι s := hpv.symm.trans hs.symm
        subst this
        exact ⟨F₀.ι s, ⟨s, hi, rfl⟩, rfl⟩
  have hPart : IsChartPartition Y (fun n => xh (e.symm n)) (fun n => Ph (e.symm n)) := by
    refine ⟨fun n => ⟨hPh_sub _, hPh_meas _⟩, fun n m hnm => hPh_disj ?_, ?_⟩
    · intro h; exact hnm (e.symm.injective h)
    · rw [← hPh_cover]
      ext y
      simp only [mem_iUnion]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨e.symm n, hn⟩
      · rintro ⟨j, hj⟩
        exact ⟨e j, by simpa using hj⟩
  rw [hS, s26v_surfaceIntegral_eq_tsum hq Uh hPart]
  -- evaluate the cover sum
  set G : ((ℕ × Bool) ⊕ ↥B) → ℝ≥0∞ := fun j =>
    ∫⁻ z in chartAt ℂ (xh j) '' Ph j, Uh ((chartAt ℂ (xh j)).symm z) *
      ENNReal.ofReal ‖qh (xh j) z‖ with hG
  have hre : ∑' n, G (e.symm n) = ∑' j, G j := e.symm.tsum_eq G
  have hGn : (∑' n, ∫⁻ z in chartAt ℂ (xh (e.symm n)) '' Ph (e.symm n),
      Uh ((chartAt ℂ (xh (e.symm n))).symm z) * ENNReal.ofReal ‖qh (xh (e.symm n)) z‖) =
      ∑' n, G (e.symm n) := rfl
  rw [hGn, hre]
  have hsplit : ∑' j, G j = ∑' ik : ℕ × Bool, G (Sum.inl ik) + ∑' b : ↥B, G (Sum.inr b) :=
    (ENNReal.summable.hasSum (f := fun ik => G (Sum.inl ik))).sum
      (ENNReal.summable.hasSum (f := fun b : ↥B => G (Sum.inr b))) |>.tsum_eq
  have hzero : ∑' b : ↥B, G (Sum.inr b) = 0 := by
    refine ENNReal.tsum_eq_zero.2 fun b => ?_
    show ∫⁻ z in chartAt ℂ (b : Y) '' {(b : Y)}, _ = 0
    rw [Set.image_singleton]
    exact setLIntegral_measure_zero _ _ (measure_singleton _)
  have hsheet : ∀ i k, G (Sum.inl (i, k)) =
      ∫⁻ w in chartAt ℂ (x i) '' P i, U ((chartAt ℂ (x i)).symm w) * ENNReal.ofReal ‖r (x i) w‖ := by
    intro i k
    show ∫⁻ z in chartAt ℂ (sh (x i) k (F₀.ι (x i))) '' (sh (x i) k '' (F₀.ι '' P i)),
      Uh ((chartAt ℂ (sh (x i) k (F₀.ι (x i)))).symm z) *
        ENNReal.ofReal ‖qh (sh (x i) k (F₀.ι (x i))) z‖ = _
    rw [hshy (x i) k]
    exact s82cmp_cover_sheet_integral F₀ hcont hr hq hrel U Uh hU (hVo (x i)) (hVr (x i)) (hVs (x i) k)
      (hsd (x i) k) (hspr (x i) k) (hso (x i) k) (hshs (x i) k) (hPι i) (hPx i) (hPm i)
  rw [hsplit, hzero, add_zero]
  have hprod : ∑' ik : ℕ × Bool, G (Sum.inl ik) = ∑' i, ∑' k : Bool, G (Sum.inl (i, k)) :=
    ENNReal.tsum_prod (f := fun i k => G (Sum.inl (i, k)))
  rw [hprod]
  have h2 : ∀ i, ∑' k : Bool, G (Sum.inl (i, k)) = 2 * ∫⁻ w in chartAt ℂ (x i) '' P i,
      U ((chartAt ℂ (x i)).symm w) * ENNReal.ofReal ‖r (x i) w‖ := by
    intro i
    rw [tsum_fintype, Fintype.sum_bool, hsheet, hsheet, two_mul]
  simp_rw [h2]
  rw [ENNReal.tsum_mul_left]

end

/-- Composing holomorphic local inverses of `π : T → S` with an open holomorphic embedding `ι : S → X` gives holomorphic
local inverses of `ι ∘ π`. -/
theorem s82cmp_cover_loc_comp {T S X : Type*} [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ) ω T]
    [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] [Nonempty S] [TopologicalSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {ι : S → X} (hι : Topology.IsOpenEmbedding ι)
    (hιd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι) {π' : T → S}
    (hπloc : ∀ t, ∃ e : OpenPartialHomeomorph T S, t ∈ e.source ∧ Set.EqOn π' e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target) :
    ∀ t, ∃ e : OpenPartialHomeomorph T X, t ∈ e.source ∧ Set.EqOn (fun t => ι (π' t)) e e.source ∧
      MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target := by
  intro t
  obtain ⟨e₀, hte₀, heq₀, hd₀⟩ := hπloc t
  set I := hι.toOpenPartialHomeomorph ι with hI
  have hIs : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) I.symm (range ι) :=
    s31inv_symm_mdifferentiableOn hι.injective hιd
  refine ⟨e₀.trans I, ⟨hte₀, by simp [hI]⟩, fun t' ht' => ?_, fun u hu => ?_⟩
  · show ι (π' t') = I (e₀ t')
    rw [heq₀ ht'.1]; rfl
  · have hu1 : u ∈ I.target := hu.1
    have hu2 : I.symm u ∈ e₀.target := hu.2
    have hIt : I.target = range ι := hι.toOpenPartialHomeomorph_target
    have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) I.symm u :=
      (hIs u (by rw [← hIt]; exact hu1)).mdifferentiableAt (hι.isOpen_range.mem_nhds (by rw [← hIt]; exact hu1))
    have h2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) e₀.symm (I.symm u) :=
      (hd₀ _ hu2).mdifferentiableAt (e₀.open_target.mem_nhds hu2)
    exact (h2.comp u h1).mdifferentiableWithinAt

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- **The comparison inequality through a punctured partial cover** (odd `n` and `(0, 4)`): lift `h` and `a` to the
punctured cover `T₀ → S₀` of even type `(h', 2n'')` (`s82lc_lift_punctured`), apply `s82cmp_core_even` there to
`qt/2`, and descend the areas through the two-to-one projection `π₀` (`s82cmp_cover_integral_p`,
`s82cmp_D_lift`); `K[ft₀] = K[h]` since both are Teichmüller maps with the same `k`. -/
theorem s82cmp_core_punct {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) (Y : FiniteTypeRS.{u} g n 0)
    (a : S₀ ≃ₜ Y.carrier) (ha : IsQCRS a) {h : S₀ ≃ₜ Y.carrier} {r : S₀ → ℂ → ℂ}
    {r' : Y.carrier → ℂ → ℂ} {k : ℝ} (hh : IsAdmissibleTeichmullerMap F₀ h r r' k)
    (hhom : ContinuousMap.Homotopic (h : C(S₀, Y.carrier)) (a : C(S₀, Y.carrier)))
    {B₀ : Finset F₀.X.carrier} (hB₀ : B₀ ⊆ F₀.P) {X₀' : ClosedRS.{u}} {pr₀ : X₀'.carrier → F₀.X.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ B₀, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ B₀, (pr₀ ⁻¹' {x}).ncard = 1)
    {h' : ℕ} (hX₀' : HasGenus X₀'.carrier h') {n'' : ℕ} (hB : B₀.card + 2 * n'' = 2 * n)
    (hh' : 2 * h' + 2 = 4 * g + B₀.card) (hn'' : 0 < n'') (hgood : 3 ≤ 2 * h' + n'') :
    quadDiffNorm r < ⊤ ∧ (quadDiffNorm r = 1 → maxDilatationRS h ≤ surfaceIntegral r
      (fun x z => ENNReal.ofReal (dilatationQuotient (localMapExprAt a x z) z))) := by
  classical
  have : Nonempty S₀ := ConnectedSpace.toNonempty
  have : Nonempty Y.carrier := ConnectedSpace.toNonempty
  obtain ⟨T₀, T₁, _, _, _, _, _, _, _, _, _, _, G₀, G₁, π₀, π₁, ft₀, ft, qt, qt', hπ₀d, hπ₁d, hπ₀s, hπ₀fib,
    hπ₀prop, hπ₀loc, hπ₁loc, hc₀, hc, hTa, hftqc, hftK, hhomt, hpb₀, -⟩ :=
    s82lc_lift_punctured F₀ Y.structure' hB₀ hpr₀ hX₀' hB hh' hh ha hhom
  have : Nonempty T₀ := ⟨Classical.choose (hπ₀s (Classical.arbitrary S₀))⟩
  set Y₁ : FiniteTypeRS.{u} h' (2 * n'') 0 := { carrier := T₁, structure' := G₁ } with hY₁
  have : Nonempty Y₁.carrier := ConnectedSpace.toNonempty
  -- the projections to the closed surfaces
  set p₀ : T₀ → F₀.X.carrier := fun t => F₀.ι (π₀ t) with hp₀
  set p₁ : T₁ → Y.structure'.X.carrier := fun t => Y.structure'.ι (π₁ t) with hp₁
  have hp₀c : Continuous p₀ := F₀.embedding.continuous.comp hπ₀d.continuous
  have hp₁c : Continuous p₁ := Y.structure'.embedding.continuous.comp hπ₁d.continuous
  have hr0 : range F₀.ι = (↑F₀.P)ᶜ := by rw [F₀.range_ι]; simp
  have hιP₀ : ∀ s, F₀.ι s ∉ F₀.P := fun s => by
    have : F₀.ι s ∈ range F₀.ι := ⟨s, rfl⟩
    rw [hr0] at this; exact this
  have hloc0 := s82cmp_cover_loc_comp F₀.embedding F₀.holomorphic hπ₀loc
  have hloc1 := s82cmp_cover_loc_comp Y.structure'.embedding Y.structure'.holomorphic hπ₁loc
  have hfib : ∀ x ∉ F₀.P, (p₀ ⁻¹' {x}).ncard = 2 := by
    intro x hx
    obtain ⟨s, rfl⟩ : x ∈ range F₀.ι := by rw [hr0]; exact hx
    have : p₀ ⁻¹' {F₀.ι s} = π₀ ⁻¹' {s} := by
      ext t; simp only [mem_preimage, mem_singleton_iff, hp₀]
      exact F₀.embedding.injective.eq_iff
    rw [this, hπ₀fib]
  have hfibP : ∀ x ∈ F₀.P, (p₀ ⁻¹' {x}).Finite := by
    intro x hx
    refine Set.Finite.subset Set.finite_empty fun t ht => ?_
    simp only [mem_preimage, mem_singleton_iff] at ht
    exact (hιP₀ _ (ht ▸ hx)).elim
  have hclosed : ∀ C : Set T₀, IsClosed C → ∀ p ∉ F₀.P, p ∉ p₀ '' C → (p₀ '' C)ᶜ ∈ 𝓝 p := by
    intro C hC p hp hpC
    obtain ⟨s, rfl⟩ : p ∈ range F₀.ι := by rw [hr0]; exact hp
    have hsC : s ∉ π₀ '' C := fun h => hpC (by
      obtain ⟨t, ht, hts⟩ := h
      exact ⟨t, ht, by rw [hp₀]; simp only; rw [hts]⟩)
    have h1 : (π₀ '' C)ᶜ ∈ 𝓝 s := (hπ₀prop.isClosedMap C hC).isOpen_compl.mem_nhds hsC
    have h2 : F₀.ι '' (π₀ '' C)ᶜ ∈ 𝓝 (F₀.ι s) := F₀.embedding.isOpenMap.image_mem_nhds h1
    refine Filter.mem_of_superset h2 ?_
    rintro _ ⟨s', hs', rfl⟩ ⟨t, ht, hts⟩
    exact hs' ⟨t, ht, F₀.embedding.injective hts⟩
  have hloc0' : ∀ y, p₀ y ∉ F₀.P → ∃ e : OpenPartialHomeomorph T₀ F₀.X.carrier, y ∈ e.source ∧
      EqOn p₀ e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target := fun y _ => hloc0 y
  have hinvι : ∀ s, Function.invFun F₀.ι (F₀.ι s) = s :=
    Function.leftInverse_invFun F₀.embedding.injective
  have hrel : ∀ (y : T₀) (s : S₀), p₀ y = F₀.ι s → ∀ᶠ z in 𝓝 (chartAt ℂ y y),
      qt y z = r s (chartAt ℂ s (Function.invFun F₀.ι (p₀ ((chartAt ℂ y).symm z)))) *
        deriv (fun w => chartAt ℂ s (Function.invFun F₀.ι (p₀ ((chartAt ℂ y).symm w)))) z ^ 2 := by
    intro y s hys
    have hy : π₀ y = s := F₀.embedding.injective hys
    subst hy
    simp only [hp₀, hinvι]
    exact hpb₀ y
  have hr : IsHolQuadDiff r := hh.2.initial
  have hq : IsHolQuadDiff qt := hTa.2.initial
  -- the dilatation densities agree along the projection
  have hU : ∀ y s, p₀ y = F₀.ι s →
      ENNReal.ofReal (dilatationQuotient (localMapExpr ft y) (chartAt ℂ y y)) =
        ENNReal.ofReal (dilatationQuotient (localMapExpr a s) (chartAt ℂ s s)) := by
    intro y s hs
    rw [s82cmp_D_lift F₀.embedding F₀.holomorphic Y.structure'.embedding Y.structure'.holomorphic
      hp₀c hp₁c (fun y _ => hloc0 y) (fun y _ => hloc1 y) ft.continuous (fun y s hys => by
        have hy : π₀ y = s := F₀.embedding.injective hys
        show Y.structure'.ι (π₁ (ft y)) = Y.structure'.ι (a s)
        rw [hc, hy]) hs]
  have hnorm : quadDiffNorm qt = 2 * quadDiffNorm r :=
    s82cmp_cover_integral_p F₀ hp₀c hclosed hfib hfibP hloc0' hr hq hrel (fun _ => 1) (fun _ => 1)
      (fun _ _ _ => rfl)
  have hDil := s82cmp_cover_integral_p F₀ hp₀c hclosed hfib hfibP hloc0' hr hq hrel
    (fun s => ENNReal.ofReal (dilatationQuotient (localMapExpr a s) (chartAt ℂ s s)))
    (fun y => ENNReal.ofReal (dilatationQuotient (localMapExpr ft y) (chartAt ℂ y y))) hU
  have hcore := s82cmp_core_even hn'' hgood G₀ Y₁ ft hftqc hTa hhomt
  have hr_fin : quadDiffNorm r < ⊤ := by
    have hfin := hcore.1
    rw [hnorm] at hfin
    exact lt_of_le_of_lt (by
      calc quadDiffNorm r = 1 * quadDiffNorm r := (one_mul _).symm
        _ ≤ 2 * quadDiffNorm r := by gcongr; norm_num) hfin
  refine ⟨hr_fin, fun hn1 => ?_⟩
  have hqn : quadDiffNorm qt = 2 := by rw [hnorm, hn1, mul_one]
  have hc2 : (0 : ℝ) < 1 / 2 := by norm_num
  have hT2 : IsAdmissibleTeichmullerMap G₀ ft₀ (((1 / 2 : ℝ) : ℂ) • qt) (((1 / 2 : ℝ) : ℂ) • qt') k := by
    refine ⟨?_, s29_e12_teichMap_smul hTa.2 hc2⟩
    have e : (((1 / 2 : ℝ) : ℂ) • qt) = ((1 / 2 : ℝ) • qt) := by
      funext x z; simp [Complex.real_smul]
    rw [e]
    exact (admissibleQDInterior G₀).smul_mem _ hTa.1
  have hnorm2 : quadDiffNorm (((1 / 2 : ℝ) : ℂ) • qt) = 1 := by
    rw [s82cmp_quadDiffNorm_smul qt hc2, hqn, one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  have key := (s82cmp_core_even hn'' hgood G₀ Y₁ ft hftqc hT2 hhomt).2 hnorm2
  rw [s82cmp_surfaceIntegral_smul qt _ hc2, s82cmp_surfaceIntegral_Dil ft qt, hDil] at key
  rw [s82cmp_surfaceIntegral_Dil a r]
  have hmax : maxDilatationRS h = ENNReal.ofReal ((1 + k) / (1 - k)) := (teichmullerMap_beltrami hh.2).2
  have hmax' : maxDilatationRS ft₀ = ENNReal.ofReal ((1 + k) / (1 - k)) := (teichmullerMap_beltrami hTa.2).2
  rw [hmax, ← hmax']
  refine key.trans (le_of_eq ?_)
  rw [← mul_assoc, one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- **The comparison inequality for the four-punctured sphere** (case `(0, 4, 0)` of L32329): through the cover
branched over the four punctures, punctured over them, of type `(1, 4)` (`s82cmp_core_punct`). -/
theorem s82cmp_core_g0n4 (F₀ : FiniteTypeStructure S₀ 0 4 0) (Y : FiniteTypeRS.{u} 0 4 0)
    (a : S₀ ≃ₜ Y.carrier) (ha : IsQCRS a) {h : S₀ ≃ₜ Y.carrier} {r : S₀ → ℂ → ℂ}
    {r' : Y.carrier → ℂ → ℂ} {k : ℝ} (hh : IsAdmissibleTeichmullerMap F₀ h r r' k)
    (hhom : ContinuousMap.Homotopic (h : C(S₀, Y.carrier)) (a : C(S₀, Y.carrier))) :
    quadDiffNorm r < ⊤ ∧ (quadDiffNorm r = 1 → maxDilatationRS h ≤ surfaceIntegral r
      (fun x z => ENNReal.ofReal (dilatationQuotient (localMapExprAt a x z) z))) := by
  obtain ⟨X₀', pr₀, hX₀', hd, hs, h2, h1, -⟩ := s82bc_exists_branched_double_cover (X := F₀.X.carrier)
    (g := 0) (n := 2) (Or.inr two_ne_zero) F₀.genus F₀.P (by rw [F₀.card_P])
  exact s82cmp_core_punct F₀ Y a ha hh hhom (subset_refl _) ⟨hd, hs, h2, h1⟩ hX₀' (n'' := 2)
    (by rw [F₀.card_P]) (by rw [F₀.card_P]) (by norm_num) (by norm_num)

/-- **The comparison inequality for an odd number of punctures** (`m = 0`, L32329): through the cover branched over
all punctures but one, punctured over all of them, of even type `(2g + n' - 1, 2n' + 2)` (`s82cmp_core_punct`);
the thrice punctured sphere has no admissible Teichmüller map (`s82lc_uniq_03`). -/
theorem s82cmp_core_odd {g n' : ℕ} (hex : ¬ IsExceptionalType g (2 * n' + 1) 0)
    (F₀ : FiniteTypeStructure S₀ g (2 * n' + 1) 0) (Y : FiniteTypeRS.{u} g (2 * n' + 1) 0)
    (a : S₀ ≃ₜ Y.carrier) (ha : IsQCRS a) {h : S₀ ≃ₜ Y.carrier} {r : S₀ → ℂ → ℂ}
    {r' : Y.carrier → ℂ → ℂ} {k : ℝ} (hh : IsAdmissibleTeichmullerMap F₀ h r r' k)
    (hhom : ContinuousMap.Homotopic (h : C(S₀, Y.carrier)) (a : C(S₀, Y.carrier))) :
    quadDiffNorm r < ⊤ ∧ (quadDiffNorm r = 1 → maxDilatationRS h ≤ surfaceIntegral r
      (fun x z => ENNReal.ofReal (dilatationQuotient (localMapExprAt a x z) z))) := by
  classical
  by_cases h03 : g = 0 ∧ n' = 1
  · obtain ⟨rfl, rfl⟩ := h03
    exact (s82lc_uniq_03 F₀ hh).elim
  have hPne : F₀.P.Nonempty := by
    rw [← Finset.card_pos, F₀.card_P]; omega
  obtain ⟨p, hp⟩ := hPne
  have hBc : (F₀.P.erase p).card = 2 * n' := by
    rw [Finset.card_erase_of_mem hp, F₀.card_P]; omega
  have hgn : g ≠ 0 ∨ n' ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact hex (by simp [IsExceptionalType])
  obtain ⟨X₀', pr₀, hX₀', hd, hs, h2, h1, -⟩ := s82bc_exists_branched_double_cover (X := F₀.X.carrier)
    hgn F₀.genus (F₀.P.erase p) hBc
  exact s82cmp_core_punct F₀ Y a ha hh hhom (Finset.erase_subset p F₀.P) ⟨hd, hs, h2, h1⟩ hX₀'
    (n'' := n' + 1) (by rw [hBc]; ring) (by rw [hBc]; omega) (by omega) (by omega)

end


end LiZhongQC
