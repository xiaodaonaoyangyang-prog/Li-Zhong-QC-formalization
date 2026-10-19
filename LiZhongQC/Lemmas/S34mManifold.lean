import LiZhongQC.Ch10.S34_BersFiberSpace
import LiZhongQC.Lemmas.S34mCore

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

/-! R83 S34 (精英下属5): banked `s34m_` manifold layer for `bersQuotient_manifold` / `thm34_1_bers`
(box charts, atlas, `s34m_family`). -/

noncomputable section

namespace LiZhongQC

universe u

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- A point of `F(G₀)` has its first coordinate in `Q(G₀, 𝕃)`. -/
theorem s34m_fst_mem (hΓ : IsFuchsian Γ) (y : BersFiberSpace Γ) : y.1.1 ∈ automorphicQD Γ := by
  obtain ⟨μ, τ, h⟩ := s34m_fiber_rep y
  rw [congrArg Prod.fst h]
  exact (bersFunctionGamma_mem hΓ μ).1

/-- `φ_μ ∈ T_{G₀}`. -/
theorem s34m_mem_bersImage (hΓ : IsFuchsian Γ) (μ : BeltramiGamma Γ) : bersFunctionGamma μ ∈ bersImage Γ :=
  ⟨Quotient.mk _ μ, ((bersMapGamma_mem hΓ (Quotient.mk _ μ)).2.2 μ rfl).symm⟩

/-- The action map `γ : F(G₀) → F(G₀)` is continuous (`s34m_action_analytic`). -/
theorem s34m_act_cont (hΓ : IsFuchsian Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ Γ) :
    ∃ T : BersFiberSpace Γ → BersFiberSpace Γ, Continuous T ∧ ∀ y, (T y).1 = bersFiberSpaceAction Γ γ y.1 := by
  have hrep : ∀ y : BersFiberSpace Γ, ∃ μ : BeltramiGamma Γ, y.1.1 = bersFunctionGamma μ := by
    intro y
    obtain ⟨μ, τ, h⟩ := s34m_fiber_rep y
    exact ⟨μ, congrArg Prod.fst h⟩
  have hmem := s34m_fst_mem hΓ
  have hact : ∀ y : BersFiberSpace Γ, bersFiberSpaceAction Γ γ y.1 ∈ BersFiberSpace Γ := by
    intro y
    obtain ⟨μ, hμ⟩ := hrep y
    show y.1.1 ∈ bersImage Γ ∧ bersFiberAction Γ γ y.1.1 y.1.2 ∈ bersDisc Γ y.1.1
    refine ⟨y.2.1, ?_⟩
    have h2 : y.1.2 ∈ bersDisc Γ y.1.1 := y.2.2
    rw [hμ] at h2 ⊢
    rw [← (bersFiberAction_wellDefined hΓ μ hγ).2.2]
    exact mem_image_of_mem _ h2
  obtain ⟨A, hA, hAv⟩ := s34m_action_analytic hΓ e hfin hγ
  have hE : Continuous fun y : BersFiberSpace Γ => e ⟨y.1.1, hmem y⟩ :=
    e.continuous.comp (continuous_subtype_val.fst.subtype_mk hmem)
  have hS : ∀ y : BersFiberSpace Γ, (e ⟨y.1.1, hmem y⟩, y.1.2) ∈ {p : (Fin m → ℂ) × ℂ | ∃ μ : BeltramiGamma Γ,
      e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ = p.1 ∧ p.2 ∈ bersDisc Γ (bersFunctionGamma μ)} := by
    intro y
    obtain ⟨μ, hμ⟩ := hrep y
    have h2 : y.1.2 ∈ bersDisc Γ y.1.1 := y.2.2
    rw [hμ] at h2
    exact ⟨μ, congrArg e (Subtype.ext hμ.symm), h2⟩
  have hval : ∀ y : BersFiberSpace Γ, A (e ⟨y.1.1, hmem y⟩, y.1.2) = bersFiberAction Γ γ y.1.1 y.1.2 := by
    intro y
    obtain ⟨μ, hμ⟩ := hrep y
    have h2 : y.1.2 ∈ bersDisc Γ y.1.1 := y.2.2
    have he : (⟨y.1.1, hmem y⟩ : automorphicQD Γ) = ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ :=
      Subtype.ext hμ
    rw [hμ] at h2
    rw [he, hAv μ _ h2, hμ]
  have h2c : Continuous fun y : BersFiberSpace Γ => bersFiberAction Γ γ y.1.1 y.1.2 :=
    (hA.continuousOn.comp_continuous (hE.prodMk continuous_subtype_val.snd) hS).congr hval
  exact ⟨fun y => ⟨bersFiberSpaceAction Γ γ y.1, hact y⟩,
    (continuous_subtype_val.fst.prodMk h2c).subtype_mk _, fun y => rfl⟩

/-- **The box chart** about `x₀ ∈ F(G₀)`: an open partial homeomorphism of `V(G₀)` onto a box of `ℂ^{m+1}`
whose source is `[N]` for an open `N ∋ x₀`, reading `[φ_μ, z] ↦ (e(φ_μ), z)` on `N`, with inverse
`w ↦ [e⁻¹(init w), w_last]` (`s34m_local_box`, `s34m_mk_isOpenMap`). -/
theorem s34m_chart (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) [τ : TopologicalSpace (BersQuotient Γ)]
    (hτ : τ = TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance) (x₀ : BersFiberSpace Γ) :
    ∃ (c : OpenPartialHomeomorph (BersQuotient Γ) (Fin (m + 1) → ℂ)) (N : Set (BersFiberSpace Γ)),
      IsOpen N ∧ x₀ ∈ N ∧ Quot.mk (bersFiberRel Γ) '' N = c.source ∧
      (∀ x ∈ N, ∀ μ : BeltramiGamma Γ, x.1.1 = bersFunctionGamma μ →
        c (Quot.mk (bersFiberRel Γ) x) =
          Fin.snoc (α := fun _ => ℂ) (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩) x.1.2) ∧
      ∀ w ∈ c.target, ∃ h : (((e.symm (Fin.init w) : automorphicQD Γ) : ℂ → ℂ), w (Fin.last m)) ∈ BersFiberSpace Γ,
        (⟨_, h⟩ : BersFiberSpace Γ) ∈ N ∧ c.symm w = Quot.mk (bersFiberRel Γ) ⟨_, h⟩ := by
  classical
  subst hτ
  let _ : TopologicalSpace (BersQuotient Γ) := TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance
  have hmem := s34m_fst_mem hΓ
  obtain ⟨μ₀, τ₀, hx₀⟩ := s34m_fiber_rep x₀
  have hz₀ : x₀.1.2 ∈ bersDisc Γ (bersFunctionGamma μ₀) := by
    have h := x₀.2.2
    rwa [congrArg Prod.fst hx₀] at h
  obtain ⟨r, hr, ρ, hρ, hball, hdisc, hinj⟩ := s34m_local_box hΓ hfree e hfin μ₀ hz₀
  set t₀ := e ⟨bersFunctionGamma μ₀, (bersFunctionGamma_mem hΓ μ₀).1⟩ with ht₀
  set z₀ := x₀.1.2 with hz₀def
  let E : BersFiberSpace Γ → Fin m → ℂ := fun y => e ⟨y.1.1, hmem y⟩
  have hEc : Continuous E := e.continuous.comp (continuous_subtype_val.fst.subtype_mk hmem)
  have hEμ : ∀ y : BersFiberSpace Γ, ∀ μ : BeltramiGamma Γ, y.1.1 = bersFunctionGamma μ →
      E y = e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ := fun y μ h => congrArg e (Subtype.ext h)
  have hrep : ∀ y : BersFiberSpace Γ, ∃ μ : BeltramiGamma Γ, y.1.1 = bersFunctionGamma μ := by
    intro y
    obtain ⟨μ, τ, h⟩ := s34m_fiber_rep y
    exact ⟨μ, congrArg Prod.fst h⟩
  let N : Set (BersFiberSpace Γ) := {y | ‖E y - t₀‖ < r ∧ ‖y.1.2 - z₀‖ < ρ}
  have hNo : IsOpen N :=
    (isOpen_lt (hEc.sub continuous_const).norm continuous_const).inter
      (isOpen_lt (continuous_subtype_val.snd.sub continuous_const).norm continuous_const)
  have hx₀N : x₀ ∈ N := by
    refine ⟨?_, ?_⟩
    swap
    · show ‖x₀.1.2 - z₀‖ < ρ
      rw [hz₀def, sub_self, norm_zero]
      exact hρ
    rw [hEμ x₀ μ₀ (congrArg Prod.fst hx₀), sub_self, norm_zero]
    exact hr
  let B : Set (Fin (m + 1) → ℂ) := {w | ‖Fin.init w - t₀‖ < r ∧ ‖w (Fin.last m) - z₀‖ < ρ}
  have hinit : Continuous fun w : Fin (m + 1) → ℂ => Fin.init w := continuous_pi fun j => continuous_apply _
  have hBo : IsOpen B :=
    (isOpen_lt (hinit.sub continuous_const).norm continuous_const).inter
      (isOpen_lt ((continuous_apply _).sub continuous_const).norm continuous_const)
  -- injectivity of `[·]` on `N`
  have hNinj : ∀ x ∈ N, ∀ y ∈ N, Quot.mk (bersFiberRel Γ) x = Quot.mk (bersFiberRel Γ) y → x = y := by
    intro x hx y hy hxy
    obtain ⟨μ, hμ⟩ := hrep x
    obtain ⟨ν, hν⟩ := hrep y
    refine hinj x y ⟨μ, hμ, ?_⟩ hx.2 ⟨ν, hν, ?_⟩ hy.2 hxy
    · rw [← hEμ x μ hμ]
      exact hx.1
    · rw [← hEμ y ν hν]
      exact hy.1
  -- the inverse point
  have hP : ∀ w ∈ B, (((e.symm (Fin.init w) : automorphicQD Γ) : ℂ → ℂ), w (Fin.last m)) ∈ BersFiberSpace Γ := by
    intro w hw
    have hb : Fin.init w ∈ ball t₀ r := by
      rw [mem_ball, dist_eq_norm]
      exact hw.1
    obtain ⟨μ, hμ⟩ := hball hb
    have hμ' : e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ = Fin.init w := hμ
    have hs : ((e.symm (Fin.init w) : automorphicQD Γ) : ℂ → ℂ) = bersFunctionGamma μ := by
      rw [← hμ', ContinuousLinearEquiv.symm_apply_apply]
    show _ ∈ bersImage Γ ∧ _ ∈ bersDisc Γ _
    rw [hs]
    refine ⟨s34m_mem_bersImage hΓ μ, hdisc μ ?_ ?_⟩
    · show ‖e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ - t₀‖ < r
      rw [hμ']
      exact hw.1
    · rw [mem_ball, dist_eq_norm]
      exact hw.2
  have hEP : ∀ w (hw : w ∈ B), E ⟨_, hP w hw⟩ = Fin.init w := by
    intro w hw
    show e ⟨((e.symm (Fin.init w) : automorphicQD Γ) : ℂ → ℂ), _⟩ = Fin.init w
    rw [Subtype.coe_eta, ContinuousLinearEquiv.apply_symm_apply]
  have hPN : ∀ w (hw : w ∈ B), (⟨_, hP w hw⟩ : BersFiberSpace Γ) ∈ N := by
    intro w hw
    refine ⟨?_, hw.2⟩
    rw [hEP w hw]
    exact hw.1
  let f : BersQuotient Γ → Fin (m + 1) → ℂ := fun v =>
    if h : ∃ y ∈ N, Quot.mk (bersFiberRel Γ) y = v then Fin.snoc (α := fun _ => ℂ) (E h.choose) h.choose.1.2
    else 0
  let g : (Fin (m + 1) → ℂ) → BersQuotient Γ := fun w =>
    if h : (((e.symm (Fin.init w) : automorphicQD Γ) : ℂ → ℂ), w (Fin.last m)) ∈ BersFiberSpace Γ then
      Quot.mk (bersFiberRel Γ) ⟨_, h⟩
    else Quot.mk (bersFiberRel Γ) x₀
  have hf : ∀ y ∈ N, f (Quot.mk (bersFiberRel Γ) y) = Fin.snoc (α := fun _ => ℂ) (E y) y.1.2 := by
    intro y hy
    have h : ∃ y' ∈ N, Quot.mk (bersFiberRel Γ) y' = Quot.mk (bersFiberRel Γ) y := ⟨y, hy, rfl⟩
    show (if h : ∃ y' ∈ N, Quot.mk (bersFiberRel Γ) y' = Quot.mk (bersFiberRel Γ) y then
      Fin.snoc (α := fun _ => ℂ) (E h.choose) h.choose.1.2 else 0) = _
    split_ifs
    rw [hNinj _ h.choose_spec.1 y hy h.choose_spec.2]
  have hg : ∀ w (hw : w ∈ B), g w = Quot.mk (bersFiberRel Γ) ⟨_, hP w hw⟩ := by
    intro w hw
    show (if h : (((e.symm (Fin.init w) : automorphicQD Γ) : ℂ → ℂ), w (Fin.last m)) ∈ BersFiberSpace Γ then
      Quot.mk (bersFiberRel Γ) ⟨_, h⟩ else Quot.mk (bersFiberRel Γ) x₀) = _
    split_ifs with h'
    · rfl
    · exact absurd (hP w hw) h'
  have hsrc : IsOpen (Quot.mk (bersFiberRel Γ) '' N) := s34m_mk_isOpenMap hΓ e hfin N hNo
  have hsnoc : Continuous fun y : BersFiberSpace Γ => Fin.snoc (α := fun _ => ℂ) (E y) y.1.2 :=
    hEc.finSnoc continuous_subtype_val.snd
  refine ⟨{
      toFun := f
      invFun := g
      source := (Quot.mk (bersFiberRel Γ) '' N)
      target := B
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := hsrc
      open_target := hBo
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_ }, N, hNo, hx₀N, rfl, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [hf y hy]
    show ‖Fin.init (Fin.snoc (α := fun _ => ℂ) (E y) y.1.2) - t₀‖ < r ∧
      ‖Fin.snoc (α := fun _ => ℂ) (E y) y.1.2 (Fin.last m) - z₀‖ < ρ
    rw [Fin.init_snoc, Fin.snoc_last]
    exact hy
  · intro w hw
    rw [hg w hw]
    exact mem_image_of_mem _ (hPN w hw)
  · rintro _ ⟨y, hy, rfl⟩
    rw [hf y hy]
    have hw : Fin.snoc (α := fun _ => ℂ) (E y) y.1.2 ∈ B := by
      show ‖Fin.init (Fin.snoc (α := fun _ => ℂ) (E y) y.1.2) - t₀‖ < r ∧
        ‖Fin.snoc (α := fun _ => ℂ) (E y) y.1.2 (Fin.last m) - z₀‖ < ρ
      rw [Fin.init_snoc, Fin.snoc_last]
      exact hy
    rw [hg _ hw]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · show ((e.symm (Fin.init (Fin.snoc (α := fun _ => ℂ) (E y) y.1.2)) : automorphicQD Γ) : ℂ → ℂ) = y.1.1
      rw [Fin.init_snoc, ContinuousLinearEquiv.symm_apply_apply]
    · show Fin.snoc (α := fun _ => ℂ) (E y) y.1.2 (Fin.last m) = y.1.2
      rw [Fin.snoc_last]
  · intro w hw
    rw [hg w hw, hf _ (hPN w hw), hEP w hw]
    exact Fin.snoc_init_self w
  · refine (continuousOn_open_iff hsrc).2 fun V hV => ?_
    have heq : Quot.mk (bersFiberRel Γ) '' N ∩ f ⁻¹' V =
        Quot.mk (bersFiberRel Γ) '' (N ∩ (fun y : BersFiberSpace Γ => Fin.snoc (α := fun _ => ℂ) (E y) y.1.2) ⁻¹' V) := by
      ext v
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hv⟩
        refine ⟨y, ⟨hy, ?_⟩, rfl⟩
        rw [mem_preimage, ← hf y hy]
        exact hv
      · rintro ⟨y, ⟨hy, hv⟩, rfl⟩
        refine ⟨⟨y, hy, rfl⟩, ?_⟩
        show f (Quot.mk (bersFiberRel Γ) y) ∈ V
        rw [hf y hy]
        exact hv
    have ho := s34m_mk_isOpenMap hΓ e hfin _ (hNo.inter (hV.preimage hsnoc))
    exact (congrArg (fun s => IsOpen s) heq).mpr ho
  · refine continuousOn_iff_continuous_domRestrict.2 ?_
    have hc : Continuous fun w : B => Quot.mk (bersFiberRel Γ) (⟨_, hP w.1 w.2⟩ : BersFiberSpace Γ) := by
      refine continuous_coinduced_rng.comp (Continuous.subtype_mk ?_ _)
      exact (continuous_subtype_val.comp (e.symm.continuous.comp (hinit.comp continuous_subtype_val))).prodMk
        ((continuous_apply _).comp continuous_subtype_val)
    exact hc.congr fun w => (hg w.1 w.2).symm
  · intro x hx μ hμ
    show f _ = _
    rw [hf x hx, hEμ x μ hμ]
  · intro w hw
    exact ⟨hP w hw, hPN w hw, hg w hw⟩

/-- `w ↦ (init w, γ_{φ(init w)}(w_last))` is analytic where defined (`s34m_action_analytic`). -/
theorem s34m_snoc_analyticAt {m : ℕ} {A : (Fin m → ℂ) × ℂ → ℂ} {w₀ : Fin (m + 1) → ℂ}
    (hA : AnalyticAt ℂ A (Fin.init w₀, w₀ (Fin.last m))) :
    AnalyticAt ℂ (fun w : Fin (m + 1) → ℂ => Fin.snoc (α := fun _ => ℂ) (Fin.init w) (A (Fin.init w, w (Fin.last m))))
      w₀ := by
  let Li : (Fin (m + 1) → ℂ) →L[ℂ] (Fin m → ℂ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (m + 1) => ℂ) j.castSucc
  let Ll : (Fin (m + 1) → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (m + 1) => ℂ) (Fin.last m)
  have ha : AnalyticAt ℂ (fun w : Fin (m + 1) → ℂ => A (Fin.init w, w (Fin.last m))) w₀ :=
    AnalyticAt.comp (g := A) (f := fun w : Fin (m + 1) → ℂ => (Li w, Ll w)) hA
      ((Li.analyticAt w₀).prod (Ll.analyticAt w₀))
  refine AnalyticAt.pi (f := fun i (w : Fin (m + 1) → ℂ) => Fin.snoc (α := fun _ => ℂ) (Fin.init w) (A (Fin.init w, w (Fin.last m))) i)
    fun i => ?_
  induction i using Fin.lastCases with
  | last =>
    simp only [Fin.snoc_last]
    exact ha
  | cast j =>
    simp only [Fin.snoc_castSucc]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (m + 1) => ℂ) j.castSucc).analyticAt w₀

/-- **Transition maps are analytic**: for box charts `c₁, c₂` (`s34m_chart`), `c₂ ∘ c₁⁻¹` is, near each point, of
the form `w ↦ (init w, γ_{φ}(w_last))` for a fixed `γ ∈ G₀` (`s34m_mk_eq_iff`, `s34m_act_cont`). -/
theorem s34m_transition (hΓ : IsFuchsian Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) [TopologicalSpace (BersQuotient Γ)]
    (c₁ c₂ : OpenPartialHomeomorph (BersQuotient Γ) (Fin (m + 1) → ℂ)) (N₁ N₂ : Set (BersFiberSpace Γ))
    (hN₂ : IsOpen N₂) (hs₂ : Quot.mk (bersFiberRel Γ) '' N₂ = c₂.source)
    (hc₂ : ∀ x ∈ N₂, ∀ μ : BeltramiGamma Γ, x.1.1 = bersFunctionGamma μ →
        c₂ (Quot.mk (bersFiberRel Γ) x) =
          Fin.snoc (α := fun _ => ℂ) (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩) x.1.2)
    (hc₁ : ∀ w ∈ c₁.target, ∃ h : (((e.symm (Fin.init w) : automorphicQD Γ) : ℂ → ℂ), w (Fin.last m)) ∈ BersFiberSpace Γ,
        (⟨_, h⟩ : BersFiberSpace Γ) ∈ N₁ ∧ c₁.symm w = Quot.mk (bersFiberRel Γ) ⟨_, h⟩) :
    ContDiffOn ℂ ω (c₂ ∘ c₁.symm) (c₁.target ∩ c₁.symm ⁻¹' c₂.source) := by
  classical
  have hrep : ∀ y : BersFiberSpace Γ, ∃ μ : BeltramiGamma Γ, y.1.1 = bersFunctionGamma μ := by
    intro y
    obtain ⟨μ, τ, h⟩ := s34m_fiber_rep y
    exact ⟨μ, congrArg Prod.fst h⟩
  rintro w₀ ⟨hw₀t, hw₀s⟩
  obtain ⟨h₀, -, he₀⟩ := hc₁ w₀ hw₀t
  have hm : Quot.mk (bersFiberRel Γ) (⟨_, h₀⟩ : BersFiberSpace Γ) ∈ Quot.mk (bersFiberRel Γ) '' N₂ := by
    rw [hs₂, ← he₀]
    exact hw₀s
  obtain ⟨x', hx'N, hx'⟩ := hm
  obtain ⟨γ, hγ, hγx⟩ := (s34m_mk_eq_iff hΓ _ _).1 hx'.symm
  obtain ⟨T, hTc, hT⟩ := s34m_act_cont hΓ e hfin hγ
  obtain ⟨A, hA, hAv⟩ := s34m_action_analytic hΓ e hfin hγ
  let Q : (Fin (m + 1) → ℂ) → (ℂ → ℂ) × ℂ := fun w => (((e.symm (Fin.init w) : automorphicQD Γ) : ℂ → ℂ), w (Fin.last m))
  have hQc : Continuous Q :=
    (continuous_subtype_val.comp (e.symm.continuous.comp (continuous_pi fun j => continuous_apply _))).prodMk
      (continuous_apply _)
  let Φ : (Fin (m + 1) → ℂ) → BersFiberSpace Γ := fun w =>
    if h : w ∈ c₁.target then T ⟨Q w, (hc₁ w h).choose⟩ else x'
  have hΦ : ∀ w (h : w ∈ c₁.target), Φ w = T ⟨Q w, (hc₁ w h).choose⟩ := by
    intro w h
    show (if h : w ∈ c₁.target then T ⟨Q w, (hc₁ w h).choose⟩ else x') = _
    split_ifs
    rfl
  have hΦc : ContinuousOn Φ c₁.target := by
    refine continuousOn_iff_continuous_domRestrict.2 ?_
    have hc : Continuous fun w : c₁.target => T ⟨Q w.1, (hc₁ w.1 w.2).choose⟩ :=
      hTc.comp (Continuous.subtype_mk (hQc.comp continuous_subtype_val) _)
    exact hc.congr fun w => (hΦ w.1 w.2).symm
  have hUo : IsOpen (c₁.target ∩ Φ ⁻¹' N₂) := hΦc.isOpen_inter_preimage c₁.open_target hN₂
  have hw₀U : w₀ ∈ c₁.target ∩ Φ ⁻¹' N₂ := by
    refine ⟨hw₀t, ?_⟩
    rw [mem_preimage, hΦ w₀ hw₀t]
    convert hx'N using 1
    exact Subtype.ext ((hT _).trans hγx)
  -- the local formula
  have hloc : ∀ w ∈ c₁.target ∩ Φ ⁻¹' N₂, (c₂ ∘ c₁.symm) w =
      Fin.snoc (α := fun _ => ℂ) (Fin.init w) (A (Fin.init w, w (Fin.last m))) := by
    rintro w ⟨hwt, hwN⟩
    obtain ⟨hw, -, hew⟩ := hc₁ w hwt
    rw [mem_preimage, hΦ w hwt] at hwN
    set y : BersFiberSpace Γ := T ⟨Q w, (hc₁ w hwt).choose⟩ with hy
    have hqy : Quot.mk (bersFiberRel Γ) (⟨Q w, hw⟩ : BersFiberSpace Γ) = Quot.mk (bersFiberRel Γ) y :=
      Quot.sound ⟨γ, hγ, (hT _).symm⟩
    obtain ⟨μ, hμ⟩ := hrep ⟨Q w, hw⟩
    have hμ' : ((e.symm (Fin.init w) : automorphicQD Γ) : ℂ → ℂ) = bersFunctionGamma μ := hμ
    have hy1 : y.1.1 = bersFunctionGamma μ := by
      rw [hy, hT]
      exact hμ'
    have hey : e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ = Fin.init w := by
      have : (⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ : automorphicQD Γ) = e.symm (Fin.init w) :=
        Subtype.ext hμ'.symm
      rw [this, ContinuousLinearEquiv.apply_symm_apply]
    have hdw : w (Fin.last m) ∈ bersDisc Γ (bersFunctionGamma μ) := by
      have h2 := hw.2
      rw [hμ'] at h2
      exact h2
    have hy2 : y.1.2 = A (Fin.init w, w (Fin.last m)) := by
      rw [hy, hT]
      show bersFiberAction Γ γ ((e.symm (Fin.init w) : automorphicQD Γ) : ℂ → ℂ) (w (Fin.last m)) = _
      rw [hμ', ← hAv μ _ hdw, hey]
    show c₂ (c₁.symm w) = _
    rw [hew, hqy, hc₂ y hwN μ hy1, hey, hy2]
  -- analyticity at `w₀`
  have hmemA : (Fin.init w₀, w₀ (Fin.last m)) ∈ {p : (Fin m → ℂ) × ℂ | ∃ μ : BeltramiGamma Γ,
      e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ = p.1 ∧ p.2 ∈ bersDisc Γ (bersFunctionGamma μ)} := by
    obtain ⟨μ, hμ⟩ := hrep ⟨Q w₀, h₀⟩
    have hμ' : ((e.symm (Fin.init w₀) : automorphicQD Γ) : ℂ → ℂ) = bersFunctionGamma μ := hμ
    refine ⟨μ, ?_, ?_⟩
    · have : (⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩ : automorphicQD Γ) = e.symm (Fin.init w₀) :=
        Subtype.ext hμ'.symm
      rw [this, ContinuousLinearEquiv.apply_symm_apply]
    · have h2 := h₀.2
      rw [hμ'] at h2
      exact h2
  have hG := (s34m_snoc_analyticAt (hA _ hmemA)).contDiffAt (n := ω)
  have hev : (c₂ ∘ c₁.symm) =ᶠ[𝓝 w₀]
      fun w => Fin.snoc (α := fun _ => ℂ) (Fin.init w) (A (Fin.init w, w (Fin.last m))) :=
    Filter.eventually_of_mem (hUo.mem_nhds hw₀U) hloc
  exact (hG.congr_of_eventuallyEq hev).contDiffWithinAt

/-- **The atlas** of box charts on `V(G₀)` (one chart `s34m_chart` per point of `F(G₀)`, `chartAt v` the chart of a
representative): a `C^ω` structure (`s34m_transition`) whose charts read `[φ_μ, z] ↦ (e(φ_μ), z)`. -/
theorem s34m_atlas (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {m : ℕ} (e : automorphicQD Γ ≃L[ℂ] (Fin m → ℂ))
    (hfin : ∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) [τ : TopologicalSpace (BersQuotient Γ)]
    (hτ : τ = TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance) :
    ∃ _ : ChartedSpace (Fin (m + 1) → ℂ) (BersQuotient Γ),
      IsManifold 𝓘(ℂ, Fin (m + 1) → ℂ) ω (BersQuotient Γ) ∧
      (∀ x₀ : BersFiberSpace Γ, ∃ c ∈ atlas (Fin (m + 1) → ℂ) (BersQuotient Γ),
        ∃ N : Set (BersFiberSpace Γ), IsOpen N ∧ x₀ ∈ N ∧ Quot.mk (bersFiberRel Γ) '' N = c.source ∧
          ∀ x ∈ N, ∀ μ : BeltramiGamma Γ, x.1.1 = bersFunctionGamma μ →
            c (Quot.mk (bersFiberRel Γ) x) =
              Fin.snoc (α := fun _ => ℂ) (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩) x.1.2) ∧
      ∀ v : BersQuotient Γ, ∃ N : Set (BersFiberSpace Γ), IsOpen N ∧
        Quot.mk (bersFiberRel Γ) '' N = (chartAt (Fin (m + 1) → ℂ) v).source ∧
          ∀ x ∈ N, ∀ μ : BeltramiGamma Γ, x.1.1 = bersFunctionGamma μ →
            chartAt (Fin (m + 1) → ℂ) v (Quot.mk (bersFiberRel Γ) x) =
              Fin.snoc (α := fun _ => ℂ) (e ⟨bersFunctionGamma μ, (bersFunctionGamma_mem hΓ μ).1⟩) x.1.2 := by
  classical
  choose c N hNo hx₀N hsrc hc hinv using fun x₀ => s34m_chart hΓ hfree e hfin hτ x₀
  let cs : ChartedSpace (Fin (m + 1) → ℂ) (BersQuotient Γ) :=
    { atlas := range c
      chartAt := fun v => c (Quot.out v)
      mem_chart_source := fun v => by
        have h : v ∈ Quot.mk (bersFiberRel Γ) '' N (Quot.out v) := ⟨Quot.out v, hx₀N _, Quot.out_eq v⟩
        exact (Set.ext_iff.1 (hsrc (Quot.out v)) v).1 h
      chart_mem_atlas := fun v => mem_range_self _ }
  refine ⟨cs, ?_, fun x₀ => ⟨c x₀, mem_range_self _, N x₀, hNo x₀, hx₀N x₀, hsrc x₀, hc x₀⟩,
    fun v => ⟨N (Quot.out v), hNo _, hsrc _, hc _⟩⟩
  refine isManifold_of_contDiffOn _ _ _ ?_
  rintro _ _ ⟨x₁, rfl⟩ ⟨x₂, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id, Set.preimage_id,
    Set.inter_univ, Function.id_comp, Function.comp_id, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.coe_trans]
  exact s34m_transition hΓ e hfin (c x₁) (c x₂) (N x₁) (N x₂) (hNo x₂) (hsrc x₂) (hc x₂) (hinv x₁)

/-- **Linear coordinates** on `T_{G₀}` (`thm33_dimension`): a linear coordinate system `e` of `Q(G₀, 𝕃)`, the
finiteness of `‖·‖_𝕃` on it, and the injectivity and openness of `t ↦ e(Ψ(t))`. -/
theorem s34m_coords {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) (hΓ : IsFuchsian Γ)
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ∃ e : automorphicQD Γ ≃L[ℂ] (Fin (3 * g - 3) → ℂ), (∀ φ : automorphicQD Γ, bersNormL (φ : ℂ → ℂ) < ⊤) ∧
      Function.Injective (fun t : TeichGamma Γ => e ⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩) ∧
      IsOpen (range fun t : TeichGamma Γ => e ⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩) := by
  classical
  have : CompactSpace S := hS.1
  have : FiniteDimensional ℂ (holQuadDiffSubmodule S) := k22q_finite_quadratic (S := S)
  obtain ⟨r, -, -⟩ := s33dim_reflected_equiv hp
  have : FiniteDimensional ℝ (automorphicQD Γ) := r.finiteDimensional
  have : FiniteDimensional ℂ (automorphicQD Γ) :=
    Module.Finite.of_restrictScalars_finite ℝ ℂ (automorphicQD Γ)
  have hdim : Module.finrank ℂ (automorphicQD Γ) = 3 * g - 3 := by
    have hrank := r.finrank_eq
    simp only [finrank_real_of_complex] at hrank
    rw [thm22_5_dim_quadratic_differentials hg hS] at hrank
    omega
  have hn : 0 < 3 * g - 3 := by omega
  have hdimcoords : Module.finrank ℂ (automorphicQD Γ) =
      Module.finrank ℂ (Fin (3 * g - 3) → ℂ) := by
    simpa only [Module.finrank_fin_fun] using hdim
  obtain ⟨e⟩ := FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq hdimcoords
  have hfin := s33dim_weighted_finite hp
  obtain ⟨a, b, ha, hb, hcompare⟩ := s33dim_coordinate_comparison hn e hfin
  refine ⟨e, hfin, ?_, s33dim_coords_open hΓ e hb (fun φ => (hcompare φ).2)⟩
  intro t u htu
  apply bersMapGamma_injective hΓ
  have heq : (⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩ : automorphicQD Γ) =
      (⟨bersMapGamma Γ u, (bersMapGamma_mem hΓ u).1⟩ : automorphicQD Γ) := e.injective htu
  exact congrArg (fun φ : automorphicQD Γ => (φ : ℂ → ℂ)) heq

/-- A map into an open subset of `ℂⁿ` which reads `w ↦ init w` in every chart `chartAt v` is differentiable with
surjective derivative. -/
theorem s34m_init_chart {n : ℕ} {V : Type*} [TopologicalSpace V] [ChartedSpace (Fin (n + 1) → ℂ) V]
    {U : TopologicalSpace.Opens (Fin n → ℂ)} (f : V → U)
    (hf : ∀ v, ∀ v' ∈ (chartAt (Fin (n + 1) → ℂ) v).source,
      (f v' : Fin n → ℂ) = Fin.init (chartAt (Fin (n + 1) → ℂ) v v')) (v : V) :
    MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin n → ℂ) f v ∧
      Function.Surjective (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin n → ℂ) f v) := by
  set c := chartAt (Fin (n + 1) → ℂ) v with hc
  let Li : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) j.castSucc
  have hLi : ∀ w, Li w = Fin.init w := fun w => rfl
  have hp : extChartAt 𝓘(ℂ, Fin (n + 1) → ℂ) v v = c v := rfl
  have hw : writtenInExtChartAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin n → ℂ) v f
      =ᶠ[𝓝 (extChartAt 𝓘(ℂ, Fin (n + 1) → ℂ) v v)] Li := by
    rw [hp]
    filter_upwards [c.open_target.mem_nhds (c.map_source (mem_chart_source _ v))] with w hw
    show ((f (c.symm w) : U) : Fin n → ℂ) = Li w
    rw [hf v _ (c.map_target hw), c.right_inv hw, hLi]
  have hcont : ContinuousAt f v := by
    rw [Topology.IsInducing.subtypeVal.continuousAt_iff]
    have hev : (fun v' => Li (c v')) =ᶠ[𝓝 v] fun v' => (f v' : Fin n → ℂ) :=
      Filter.eventually_of_mem (c.open_source.mem_nhds (mem_chart_source _ v)) fun v' hv' => (hf v v' hv').symm
    exact (Li.continuous.continuousAt.comp (c.continuousAt (mem_chart_source _ v))).congr hev
  have hmd : MDifferentiableAt 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin n → ℂ) f v :=
    (mdifferentiableAt_iff f v).2 ⟨hcont, (Li.differentiableAt.congr_of_eventuallyEq hw).differentiableWithinAt⟩
  refine ⟨hmd, fun u => ⟨Fin.snoc (α := fun _ => ℂ) u 0, ?_⟩⟩
  have hr : range (𝓘(ℂ, Fin (n + 1) → ℂ) : (Fin (n + 1) → ℂ) → (Fin (n + 1) → ℂ)) = univ := by
    rw [modelWithCornersSelf_coe, range_id]
  rw [hmd.mfderiv, hr, fderivWithin_univ, hw.fderiv_eq, Li.fderiv]
  show Li (Fin.snoc (α := fun _ => ℂ) u 0) = u
  rw [hLi]
  exact Fin.init_snoc _ _

/-- **The Bers fibre space as a holomorphic family** (data shared by `bersQuotient_manifold` and `thm34_1_bers`):
coordinates, the quotient topology, the box-chart atlas (`s34m_atlas`), the chart clause, and the projection
`pr`, holomorphic, surjective, with surjective derivative (it reads `(t, z) ↦ t` in every chart). -/
theorem s34m_family {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ∃ (coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ) (_ : Function.Injective coords) (hopen : IsOpen (range coords))
      (τ : TopologicalSpace (BersQuotient Γ))
      (_ : τ = TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance)
      (_ : ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ)),
      IsManifold 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) ω (BersQuotient Γ) ∧
      (∀ x₀ : BersFiberSpace Γ, ∃ e ∈ atlas (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ),
        ∃ N : Set (BersFiberSpace Γ), IsOpen N ∧ x₀ ∈ N ∧
          (Quot.mk (bersFiberRel Γ) '' N : Set (BersQuotient Γ)) = e.source ∧
          ∀ x ∈ N, ∀ q : TeichGamma Γ, x.1.1 = bersMapGamma Γ q →
            e (Quot.mk (bersFiberRel Γ) x) = Fin.snoc (α := fun _ => ℂ) (coords q) x.1.2) ∧
      ∃ pr : BersQuotient Γ → (⟨range coords, hopen⟩ : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ)),
        MDifferentiable 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) 𝓘(ℂ, Fin (3 * g - 3) → ℂ) pr ∧
        (∀ (q : TeichGamma Γ) (v : BersQuotient Γ), bersProjection Γ v = bersMapGamma Γ q →
          (pr v : Fin (3 * g - 3) → ℂ) = coords q) ∧
        Function.Surjective pr ∧
        ∀ v, Function.Surjective (mfderiv 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) 𝓘(ℂ, Fin (3 * g - 3) → ℂ) pr v) := by
  classical
  obtain ⟨e, hfin, hinj, hopen⟩ := s34m_coords hg hS hΓ hp
  set coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ := fun t => e ⟨bersMapGamma Γ t, (bersMapGamma_mem hΓ t).1⟩
    with hcoords
  let τ : TopologicalSpace (BersQuotient Γ) := TopologicalSpace.coinduced (Quot.mk (bersFiberRel Γ)) inferInstance
  obtain ⟨cs, hM, hchart, hchartAt⟩ := s34m_atlas hΓ hfree e hfin (τ := τ) rfl
  have hproj : ∀ v : BersQuotient Γ, ∃ q, bersProjection Γ v = bersMapGamma Γ q := by
    intro v
    induction v using Quot.ind with
    | mk x =>
      obtain ⟨q, hq⟩ := x.2.1
      exact ⟨q, hq.symm⟩
  let pr : BersQuotient Γ → (⟨range coords, hopen⟩ : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ)) :=
    fun v => ⟨coords (hproj v).choose, mem_range_self _⟩
  have hpr : ∀ (q : TeichGamma Γ) (v : BersQuotient Γ), bersProjection Γ v = bersMapGamma Γ q →
      (pr v : Fin (3 * g - 3) → ℂ) = coords q := by
    intro q v h
    show coords (hproj v).choose = coords q
    rw [bersMapGamma_injective hΓ ((hproj v).choose_spec.symm.trans h)]
  have hval : ∀ v, ∀ v' ∈ (chartAt (Fin (3 * g - 3 + 1) → ℂ) v).source,
      (pr v' : Fin (3 * g - 3) → ℂ) = Fin.init (chartAt (Fin (3 * g - 3 + 1) → ℂ) v v') := by
    intro v v' hv'
    obtain ⟨N, -, hN, hf⟩ := hchartAt v
    have h' : v' ∈ Quot.mk (bersFiberRel Γ) '' N := (Set.ext_iff.1 hN v').2 hv'
    obtain ⟨x, hx, rfl⟩ := h'
    obtain ⟨q, hq⟩ := x.2.1
    rw [hf x hx q.out hq.symm, Fin.init_snoc, hpr q (Quot.mk (bersFiberRel Γ) x) hq.symm]
    rfl
  have hH := fun v => s34m_init_chart pr hval v
  refine ⟨coords, hinj, hopen, τ, rfl, cs, hM, ?_, pr, fun v => (hH v).1, hpr, ?_, fun v => (hH v).2⟩
  · intro x₀
    obtain ⟨c, hc, N, hN, hx₀, hs, hf⟩ := hchart x₀
    exact ⟨c, hc, N, hN, hx₀, hs, fun x hx q hq => hf x hx q.out hq⟩
  · rintro ⟨_, q, rfl⟩
    have hI : Complex.I ∈ upperHalf := by
      show 0 < Complex.I.im
      rw [Complex.I_im]
      exact one_pos
    let x : BersFiberSpace Γ := ⟨(bersMapGamma Γ q, normalizedSolution (Quotient.out q).1.1 Complex.I),
      ⟨q, rfl⟩, ⟨Quotient.out q, rfl, ⟨Complex.I, hI, rfl⟩⟩⟩
    exact ⟨Quot.mk (bersFiberRel Γ) x, Subtype.ext (hpr q _ rfl)⟩

end LiZhongQC
