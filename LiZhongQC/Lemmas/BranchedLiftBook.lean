import LiZhongQC.Lemmas.BranchedLiftTeich

/-!
# Lifting maps to two-sheeted branched covers (`s82lc_`, for §32.1)

Generic pieces of `lift_teichmullerMap_double_cover` (S32): a holomorphic map `pr : Y → X` of closed Riemann
surfaces with fibres of two points off a finite set `P` and one point over `P` is

* a covering map over `X ∖ P`, a local biholomorphism off `pr⁻¹ P`, and `w ↦ w²` in charts over `P`
  (`s82lc_local_form`);

homeomorphisms of finite type surfaces without holes extend over the punctures (`s82lc_extend_homeomorph`); the
complex structure of `Y` can be transported along any homeomorphism of the base (`s82lc_transport`); a homeomorphism
of the base that is homotopic to the identity off `P` lifts (`s82lc_lift`), its lift is quasiconformal with the same
maximal dilatation as the map it covers (`s82lc_lift_qc`), and homotopy off a finite set implies homotopy on a
closed surface carrying a nonzero holomorphic quadratic differential (`s82lc_homotopic_of_punctured`).  These
pieces live in `BranchedLiftCore`, `BranchedLiftQC` and `BranchedLiftTeich` (with the lift of a Teichmüller map,
`s82lc_lift_teich`); this file assembles the book lemma `lift_teichmullerMap_double_cover`.
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

/-- The fibres of `fb ∘ pr ∘ e⁻¹` are the images under `e` of the fibres of `pr` over `fb⁻¹`. -/
theorem s82lc_transport_fibres {Y X₀ X₁ : ClosedRS.{u}} {P₀ : Finset X₀.carrier} {P₁ : Finset X₁.carrier}
    {pr₀ : Y.carrier → X₀.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ P₀, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ P₀, (pr₀ ⁻¹' {x}).ncard = 1)
    (fb : X₀.carrier ≃ₜ X₁.carrier) (hfbP : fb '' ↑P₀ = ↑P₁) {Y₁ : ClosedRS.{u}} (e : Y.carrier ≃ₜ Y₁.carrier)
    {pr₁ : Y₁.carrier → X₁.carrier} (hd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₁) (he : ∀ y, pr₁ (e y) = fb (pr₀ y)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₁ ∧ Function.Surjective pr₁ ∧
      (∀ x ∉ P₁, (pr₁ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ P₁, (pr₁ ⁻¹' {x}).ncard = 1 := by
  have hfib : ∀ x, pr₁ ⁻¹' {x} = e '' (pr₀ ⁻¹' {fb.symm x}) := by
    intro x
    ext z
    constructor
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      show pr₀ (e.symm z) = fb.symm x
      have h1 := he (e.symm z)
      rw [e.apply_symm_apply] at h1
      rw [← (show pr₁ z = x from hz), h1, fb.symm_apply_apply]
    · rintro ⟨y, hy, rfl⟩
      show pr₁ (e y) = x
      rw [he, show pr₀ y = fb.symm x from hy, fb.apply_symm_apply]
  have hmem : ∀ x, x ∈ P₁ ↔ fb.symm x ∈ P₀ := by
    intro x
    constructor
    · intro hx
      have : x ∈ fb '' ↑P₀ := by rw [hfbP]; exact hx
      obtain ⟨p, hp, rfl⟩ := this
      rw [fb.symm_apply_apply]
      exact hp
    · intro hx
      have : fb (fb.symm x) ∈ fb '' ↑P₀ := mem_image_of_mem _ hx
      rw [hfbP, fb.apply_symm_apply] at this
      exact this
  refine ⟨hd, fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := hpr₀.2.1 (fb.symm x)
    exact ⟨e y, by rw [he, hy, fb.apply_symm_apply]⟩
  · rw [hfib, Set.ncard_image_of_injective _ e.injective]
    exact hpr₀.2.2.1 _ (fun h => hx ((hmem x).2 h))
  · rw [hfib, Set.ncard_image_of_injective _ e.injective]
    exact hpr₀.2.2.2 _ ((hmem x).1 hx)

/-- `lift_teichmullerMap_double_cover` with the lifted differentials identified: `q̃ = pr₀^* q` and `q̃' = pr₁^* q'` in
charts at the points over `ι(S₀)`, resp. `ι(S)` (for the area comparison of §32.3). -/
theorem s82lc_lift_teichmullerMap_double_cover_ext {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g (2 * n) 0)
    (F₁ : FiniteTypeStructure S g (2 * n) 0) {X₀' : ClosedRS.{u}} {pr₀ : X₀'.carrier → F₀.X.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ F₀.P, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₀.P, (pr₀ ⁻¹' {x}).ncard = 1)
    {f₀ f : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ} (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k)
    (hf : IsQCRS f) (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    ∃ (X₁' : ClosedRS.{u}) (pr₁ : X₁'.carrier → F₁.X.carrier), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₁ ∧
      Function.Surjective pr₁ ∧ (∀ x ∉ F₁.P, (pr₁ ⁻¹' {x}).ncard = 2) ∧
      (∀ x ∈ F₁.P, (pr₁ ⁻¹' {x}).ncard = 1) ∧
      ∃ (f₀' f' : X₀'.carrier ≃ₜ X₁'.carrier) (qtil : X₀'.carrier → ℂ → ℂ) (qtil' : X₁'.carrier → ℂ → ℂ),
        (∀ y s, pr₀ y = F₀.ι s → pr₁ (f₀' y) = F₁.ι (f₀ s)) ∧
        (∀ y s, pr₀ y = F₀.ι s → pr₁ (f' y) = F₁.ι (f s)) ∧
        IsTeichmullerMap f₀' qtil qtil' k ∧ IsQCRS f' ∧ maxDilatationRS f' = maxDilatationRS f ∧
        ContinuousMap.Homotopic (f₀' : C(X₀'.carrier, X₁'.carrier)) (f' : C(X₀'.carrier, X₁'.carrier)) ∧
        (∀ (y : X₀'.carrier) (s : S₀), pr₀ y = F₀.ι s → ∀ᶠ z in 𝓝 (chartAt ℂ y y),
          qtil y z = q s (chartAt ℂ s (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm z)))) *
            deriv (fun w => chartAt ℂ s (Function.invFun F₀.ι (pr₀ ((chartAt ℂ y).symm w)))) z ^ 2) ∧
        ∀ (y : X₁'.carrier) (s : S), pr₁ y = F₁.ι s → ∀ᶠ z in 𝓝 (chartAt ℂ y y),
          qtil' y z = q' s (chartAt ℂ s (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm z)))) *
            deriv (fun w => chartAt ℂ s (Function.invFun F₁.ι (pr₁ ((chartAt ℂ y).symm w)))) z ^ 2 := by
  -- fill the punctures (W2) and transport the cover along the extension of `f₀` (W3)
  obtain ⟨fb₀, hfb₀, hfb₀P⟩ := s82lc_extend_homeomorph F₀ F₁ f₀
  obtain ⟨fb, hfb, hfbP⟩ := s82lc_extend_homeomorph F₀ F₁ f
  obtain ⟨Y₁, e, pr₁, hd, he⟩ := s82lc_transport hpr₀ fb₀
  have hpr₁ := s82lc_transport_fibres hpr₀ fb₀ hfb₀P e hd he
  -- the base homeomorphism `h = fb₀⁻¹ ∘ fb` is homotopic to the identity off the punctures
  set h : F₀.X.carrier ≃ₜ F₀.X.carrier := fb.trans fb₀.symm with hh
  have hP : h '' ↑F₀.P = ↑F₀.P := by
    show (fb₀.symm ∘ fb) '' ↑F₀.P = ↑F₀.P
    rw [Set.image_comp, hfbP, ← hfb₀P, Set.image_image]
    simp
  -- the punctured surfaces are the complements of the punctures
  have hrange₀ : range F₀.ι = (↑F₀.P : Set F₀.X.carrier)ᶜ := by
    rw [F₀.range_ι]; simp
  have hrange₁ : range F₁.ι = (↑F₁.P : Set F₁.X.carrier)ᶜ := by
    rw [F₁.range_ι]; simp
  obtain ⟨H⟩ := hhom
  set ι₀h := F₀.embedding.isEmbedding.toHomeomorph with hι₀h
  have hinv : ∀ x : ((↑F₀.P)ᶜ : Set F₀.X.carrier), (x : F₀.X.carrier) ∈ range F₀.ι := fun x => by
    rw [hrange₀]; exact x.2
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
  have hK1 : ∀ x, K (1, x) = h x := fun x => by
    show fb₀.symm (F₁.ι (H (1, j x))) = fb₀.symm (fb x)
    rw [H.apply_one]
    show fb₀.symm (F₁.ι (f (j x))) = fb₀.symm (fb x)
    rw [← hfb, hjι]
  have hKP : ∀ t x, K (t, x) ∉ F₀.P := fun t x hx => by
    have h1 : F₁.ι (H (t, j x)) ∈ fb₀ '' ↑F₀.P := ⟨_, hx, fb₀.apply_symm_apply _⟩
    rw [hfb₀P] at h1
    have h2 : F₁.ι (H (t, j x)) ∈ range F₁.ι := ⟨_, rfl⟩
    rw [hrange₁] at h2
    exact h2 h1
  -- lift `h` (W4); the lift of `f` is `e ∘ F`
  obtain ⟨F, hF, L, hL0, hL1⟩ := s82lc_lift hpr₀ h hP K hK0 hK1 hKP
  have hΦ₀ : ∀ y s, pr₀ y = F₀.ι s → pr₁ (e y) = F₁.ι (f₀ s) := fun y s hy => by
    rw [he, hy, hfb₀]
  have hΦ : ∀ y s, pr₀ y = F₀.ι s → pr₁ ((F.trans e) y) = F₁.ι (f s) := fun y s hy => by
    show pr₁ (e (F y)) = _
    rw [he, hF, hy, hh, Homeomorph.trans_apply, hfb, fb₀.apply_symm_apply]
  obtain ⟨qtil, qtil', hT, hq₀, hq₁⟩ := s82lc_lift_teich F₀ F₁ hpr₀ hpr₁ hf₀ hΦ₀
  obtain ⟨hQC, hK⟩ := s82lc_lift_qc F₀ F₁ hpr₀ hpr₁ hf hΦ
  -- homotopy on the closed cover (W7), with `B = pr₀⁻¹ P` finite
  have hB : (pr₀ ⁻¹' (↑F₀.P : Set F₀.X.carrier)).Finite := by
    rw [← Set.biUnion_preimage_singleton]
    exact F₀.P.finite_toSet.biUnion fun x hx =>
      Set.finite_of_ncard_ne_zero (by rw [hpr₀.2.2.2 x hx]; exact one_ne_zero)
  have hhomF := s82lc_homotopic_of_punctured ⟨qtil, hT.initial, hT.initial_ne⟩ hB F L hL0 hL1
  refine ⟨Y₁, pr₁, hpr₁.1, hpr₁.2.1, hpr₁.2.2.1, hpr₁.2.2.2, e, F.trans e, qtil, qtil', hΦ₀, hΦ, hT, hQC, hK, ?_,
    hq₀, hq₁⟩
  have := (ContinuousMap.Homotopic.refl (e : C(X₀'.carrier, Y₁.carrier))).comp hhomF
  convert this using 1 <;> exact ContinuousMap.ext fun _ => rfl

/-- `lift_teichmullerMap_double_cover` (S32), compiled under a helper name (book statement byte-identical). -/
theorem s82lc_lift_teichmullerMap_double_cover {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g (2 * n) 0)
    (F₁ : FiniteTypeStructure S g (2 * n) 0) {X₀' : ClosedRS.{u}} {pr₀ : X₀'.carrier → F₀.X.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ F₀.P, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₀.P, (pr₀ ⁻¹' {x}).ncard = 1)
    {f₀ f : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ} (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k)
    (hf : IsQCRS f) (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    ∃ (X₁' : ClosedRS.{u}) (pr₁ : X₁'.carrier → F₁.X.carrier), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₁ ∧
      Function.Surjective pr₁ ∧ (∀ x ∉ F₁.P, (pr₁ ⁻¹' {x}).ncard = 2) ∧
      (∀ x ∈ F₁.P, (pr₁ ⁻¹' {x}).ncard = 1) ∧
      ∃ (f₀' f' : X₀'.carrier ≃ₜ X₁'.carrier) (qtil : X₀'.carrier → ℂ → ℂ) (qtil' : X₁'.carrier → ℂ → ℂ),
        (∀ y s, pr₀ y = F₀.ι s → pr₁ (f₀' y) = F₁.ι (f₀ s)) ∧
        (∀ y s, pr₀ y = F₀.ι s → pr₁ (f' y) = F₁.ι (f s)) ∧
        IsTeichmullerMap f₀' qtil qtil' k ∧ IsQCRS f' ∧ maxDilatationRS f' = maxDilatationRS f ∧
        ContinuousMap.Homotopic (f₀' : C(X₀'.carrier, X₁'.carrier)) (f' : C(X₀'.carrier, X₁'.carrier)) := by
  obtain ⟨X₁', pr₁, h1, h2, h3, h4, f₀', f', qtil, qtil', h5, h6, h7, h8, h9, h10, -⟩ :=
    s82lc_lift_teichmullerMap_double_cover_ext F₀ F₁ hpr₀ hf₀ hf hhom
  exact ⟨X₁', pr₁, h1, h2, h3, h4, f₀', f', qtil, qtil', h5, h6, h7, h8, h9, h10⟩

section RelocatedS32

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- §32.1: the Teichmüller map `f₀` and any `f ≃ f₀` lift to the branched double covers; the lift of
`f₀` is again a Teichmüller map, with the holomorphic lifted differential, and the lift of `f` can be
chosen homotopic to the lift of `f₀` (by lifting the track of a point under the homotopy).

**Correction (2026-09-27).**  The covers were not tied to `F₀`, `F₁` (constant maps passed the old
`ncard ≤ 2` condition, refuted in Lean, s31t), so now `pr₀` is a double cover branched exactly over `F₀.P`,
the cover `pr₁` of `F₁.X` is produced, and the lifts cover `f₀` and `f`. -/
theorem lift_teichmullerMap_double_cover {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g (2 * n) 0)
    (F₁ : FiniteTypeStructure S g (2 * n) 0) {X₀' : ClosedRS.{u}} {pr₀ : X₀'.carrier → F₀.X.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ F₀.P, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₀.P, (pr₀ ⁻¹' {x}).ncard = 1)
    {f₀ f : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ} (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k)
    (hf : IsQCRS f) (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    ∃ (X₁' : ClosedRS.{u}) (pr₁ : X₁'.carrier → F₁.X.carrier), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₁ ∧
      Function.Surjective pr₁ ∧ (∀ x ∉ F₁.P, (pr₁ ⁻¹' {x}).ncard = 2) ∧
      (∀ x ∈ F₁.P, (pr₁ ⁻¹' {x}).ncard = 1) ∧
      ∃ (f₀' f' : X₀'.carrier ≃ₜ X₁'.carrier) (qtil : X₀'.carrier → ℂ → ℂ) (qtil' : X₁'.carrier → ℂ → ℂ),
        (∀ y s, pr₀ y = F₀.ι s → pr₁ (f₀' y) = F₁.ι (f₀ s)) ∧
        (∀ y s, pr₀ y = F₀.ι s → pr₁ (f' y) = F₁.ι (f s)) ∧
        IsTeichmullerMap f₀' qtil qtil' k ∧ IsQCRS f' ∧ maxDilatationRS f' = maxDilatationRS f ∧
        ContinuousMap.Homotopic (f₀' : C(X₀'.carrier, X₁'.carrier)) (f' : C(X₀'.carrier, X₁'.carrier)) := by
  exact s82lc_lift_teichmullerMap_double_cover F₀ F₁ hpr₀ hf₀ hf hhom

end RelocatedS32

end LiZhongQC
