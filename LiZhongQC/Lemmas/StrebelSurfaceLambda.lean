import LiZhongQC.Lemmas.BranchedLiftBook
import LiZhongQC.Lemmas.FiniteTypeCover
import LiZhongQC.Lemmas.SchottkyBranchedFinal
import LiZhongQC.Lemmas.S32wThm324
import LiZhongQC.Lemmas.SchottkyDirectD3a
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Lemmas.HyperbolicSurfaceArea
import LiZhongQC.Lemmas.Thm321
import LiZhongQC.Lemmas.FiniteTypeComparisonOdd

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- **The lift of a self-map `h ≃ id` of a finite-type surface through a branched double cover**, with the
cover itself as source and target: `F` covers `h`, is q.c., homotopic to the identity, and the lifted
differential `q̃ = pr^* q` is holomorphic and non-zero. -/
theorem str_lift_self {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g (2 * n) 0) {X' : ClosedRS.{u}}
    {pr : X'.carrier → F₀.X.carrier}
    (hpr : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
      (∀ x ∉ F₀.P, (pr ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₀.P, (pr ⁻¹' {x}).ncard = 1)
    {q : S₀ → ℂ → ℂ} (hq : q ∈ admissibleQDInterior F₀) (hqH : IsHolQuadDiff q) (hq0 : q ≠ 0)
    {h : S₀ ≃ₜ S₀} (hh : IsQCRS h)
    (hhom : ContinuousMap.Homotopic (h : C(S₀, S₀)) (ContinuousMap.id S₀)) :
    ∃ (F : X'.carrier ≃ₜ X'.carrier) (qtil : X'.carrier → ℂ → ℂ),
      (∀ y s, pr y = F₀.ι s → pr (F y) = F₀.ι (h s)) ∧ IsQCRS F ∧ IsHolQuadDiff qtil ∧ qtil ≠ 0 ∧
      ContinuousMap.Homotopic (ContinuousMap.id X'.carrier) (F : C(X'.carrier, X'.carrier)) ∧
      (∀ (y : X'.carrier) (s : S₀), pr y = F₀.ι s → ∀ᶠ z in 𝓝 (chartAt ℂ y y),
        qtil y z = q s (chartAt ℂ s (Function.invFun F₀.ι (pr ((chartAt ℂ y).symm z)))) *
          deriv (fun w => chartAt ℂ s (Function.invFun F₀.ι (pr ((chartAt ℂ y).symm w)))) z ^ 2) := by
  classical
  have hf₀ : IsAdmissibleTeichmullerMap F₀ (Homeomorph.refl S₀) q q 0 :=
    ⟨hq, s32w_t324_refl_teich hqH hq0⟩
  obtain ⟨fb, hfb, hfbP⟩ := s82lc_extend_homeomorph F₀ F₀ h
  have hrange₀ : range F₀.ι = (↑F₀.P : Set F₀.X.carrier)ᶜ := by
    rw [F₀.range_ι]; simp
  obtain ⟨H⟩ := hhom.symm
  set ι₀h := F₀.embedding.isEmbedding.toHomeomorph with hι₀h
  have hinv : ∀ x : ((↑F₀.P)ᶜ : Set F₀.X.carrier), (x : F₀.X.carrier) ∈ range F₀.ι := fun x => by
    rw [hrange₀]; exact x.2
  set j : C(((↑F₀.P)ᶜ : Set F₀.X.carrier), S₀) :=
    ⟨fun x => ι₀h.symm ⟨x, hinv x⟩, ι₀h.symm.continuous.comp (continuous_subtype_val.subtype_mk _)⟩ with hj
  have hjι : ∀ x : ((↑F₀.P)ᶜ : Set F₀.X.carrier), F₀.ι (j x) = x := fun x => by
    have := ι₀h.apply_symm_apply ⟨x, hinv x⟩
    exact congrArg Subtype.val this
  set K : C(unitInterval × ((↑F₀.P)ᶜ : Set F₀.X.carrier), F₀.X.carrier) :=
    ⟨fun tx => F₀.ι (H (tx.1, j tx.2)),
      F₀.embedding.continuous.comp
        (H.continuous.comp (continuous_fst.prodMk (j.continuous.comp continuous_snd)))⟩ with hK
  have hK0 : ∀ x, K (0, x) = x := fun x => by
    show F₀.ι (H (0, j x)) = x
    rw [H.apply_zero]
    exact hjι x
  have hK1 : ∀ x, K (1, x) = fb x := fun x => by
    show F₀.ι (H (1, j x)) = fb x
    rw [H.apply_one]
    show F₀.ι (h (j x)) = fb x
    rw [← hfb, hjι]
  have hKP : ∀ t x, K (t, x) ∉ F₀.P := fun t x hx => by
    have h2 : F₀.ι (H (t, j x)) ∈ range F₀.ι := ⟨_, rfl⟩
    rw [hrange₀] at h2
    exact h2 hx
  obtain ⟨F, hF, L, hL0, hL1⟩ := s82lc_lift hpr fb hfbP K hK0 hK1 hKP
  have hΦ : ∀ y s, pr y = F₀.ι s → pr (F y) = F₀.ι (h s) := fun y s hy => by
    rw [hF, hy, hfb]
  obtain ⟨qtil, qtil', hT, hq₀, -⟩ := s82lc_lift_teich F₀ F₀ hpr hpr hf₀
    (Φ := Homeomorph.refl X'.carrier) (fun y s hy => by simpa using hy)
  obtain ⟨hQC, -⟩ := s82lc_lift_qc F₀ F₀ hpr hpr hh hΦ
  have hB : (pr ⁻¹' (↑F₀.P : Set F₀.X.carrier)).Finite := by
    rw [← Set.biUnion_preimage_singleton]
    exact F₀.P.finite_toSet.biUnion fun x hx =>
      Set.finite_of_ncard_ne_zero (by rw [hpr.2.2.2 x hx]; exact one_ne_zero)
  have hhomF := s82lc_homotopic_of_punctured ⟨qtil, hT.initial, hT.initial_ne⟩ hB F L hL0 hL1
  exact ⟨F, qtil, hΦ, hQC, hT.initial, hT.initial_ne, hhomF, hq₀⟩


/-- **Conjugation invariance of the stretching function.**  If `Ls ∘ B = A ∘ Lc` near `c` with `B`, `A`
holomorphic and locally biholomorphic, and the densities `Φ`, `Φ'` are the pullbacks of `Qs`, `Qt` by `B`, `A`,
then `λ` of `Lc` at `c` equals `λ` of `Ls` at `B c`. -/
theorem str_lambda_conj {Ls Lc B A B' A' Qs Qt Φ Φ' : ℂ → ℂ} {c z0 : ℂ}
    (hBd : DifferentiableAt ℂ B c) (hB'd : DifferentiableAt ℂ B' z0) (hBc : B c = z0)
    (hBB' : ∀ᶠ w in 𝓝 c, B' (B w) = w) (hB'B : ∀ᶠ u in 𝓝 z0, B (B' u) = u)
    (hAd : DifferentiableAt ℂ A (Lc c)) (hA'd : DifferentiableAt ℂ A' (A (Lc c)))
    (hAA' : ∀ᶠ w in 𝓝 (Lc c), A' (A w) = w) (hLc : ContinuousAt Lc c)
    (hev : (Ls ∘ B) =ᶠ[𝓝 c] (A ∘ Lc)) (hAL : A (Lc c) = Ls z0)
    (hB0 : deriv B c ≠ 0) (hA0 : deriv A (Lc c) ≠ 0)
    (hΦ : Φ c = Qs z0 * deriv B c ^ 2) (hΦ' : Φ' (Lc c) = Qt (Ls z0) * deriv A (Lc c) ^ 2) :
    lambdaStretchPlane Φ Φ' Lc c = lambdaStretchPlane Qs Qt Ls z0 := by
  set a : ℂ := deriv B c with ha
  set b : ℂ := deriv A (Lc c) with hb
  obtain ⟨hdzR, hdzbarR⟩ := s23_wirtinger_comp_right (g := Ls) (T := B) (S := B') hBd
    (by rw [hBc]; exact hB'd) hBB' (by rw [hBc]; exact hB'B)
  obtain ⟨hdzL, hdzbarL⟩ := s23_wirtinger_comp_left (g := Lc) (h := A) (k := A') hLc hAd hA'd hAA'
  rw [hBc] at hdzR hdzbarR
  have e1 : dz Ls z0 * a = b * dz Lc c := by
    have h1 : dz (Ls ∘ B) c = dz (A ∘ Lc) c := by simp only [dz, hev.fderiv_eq]
    rw [hdzR, hdzL] at h1
    exact h1
  have e2 : dzbar Ls z0 * conj a = b * dzbar Lc c := by
    have h1 : dzbar (Ls ∘ B) c = dzbar (A ∘ Lc) c := by simp only [dzbar, hev.fderiv_eq]
    rw [hdzbarR, hdzbarL] at h1
    exact h1
  unfold lambdaStretchPlane
  have halg := s26v_b_lambdaPlane_alg (dz Ls z0) (dzbar Ls z0) (Qs z0) a hB0
    (Real.sqrt ‖Qt (Ls z0)‖)
  rw [← hΦ] at halg
  rw [← halg, e1, e2]
  have hfac : b * dz Lc c + b * dzbar Lc c * (Φ c / ((‖Φ c‖ : ℝ) : ℂ)) =
      b * (dz Lc c + dzbar Lc c * (Φ c / ((‖Φ c‖ : ℝ) : ℂ))) := by ring
  rw [hfac, norm_mul]
  have hsq : Real.sqrt ‖Φ' (Lc c)‖ = Real.sqrt ‖Qt (Ls z0)‖ * ‖b‖ := by
    rw [hΦ', norm_mul, norm_pow, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [hsq]
  ring


/-- **The stretching function is unchanged by lifting through a cover.**  Same setting as `s82cmp_D_lift`,
with the differentials related by `hrel₀`, `hrel₁`. -/
theorem str_lambda_lift {S₀' S₁' X₀ X₁ Y₀ Y₁ : Type*} [TopologicalSpace S₀'] [ChartedSpace ℂ S₀']
    [IsManifold 𝓘(ℂ) ω S₀'] [Nonempty S₀'] [TopologicalSpace S₁'] [ChartedSpace ℂ S₁']
    [IsManifold 𝓘(ℂ) ω S₁'] [Nonempty S₁'] [TopologicalSpace X₀] [ChartedSpace ℂ X₀]
    [IsManifold 𝓘(ℂ) ω X₀] [TopologicalSpace X₁] [ChartedSpace ℂ X₁] [IsManifold 𝓘(ℂ) ω X₁]
    [TopologicalSpace Y₀] [ChartedSpace ℂ Y₀] [IsManifold 𝓘(ℂ) ω Y₀] [TopologicalSpace Y₁]
    [ChartedSpace ℂ Y₁] [IsManifold 𝓘(ℂ) ω Y₁]
    {ι₀ : S₀' → X₀} (hι₀ : Topology.IsOpenEmbedding ι₀) (hι₀d : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι₀)
    {ι₁ : S₁' → X₁} (hι₁ : Topology.IsOpenEmbedding ι₁) (hι₁d : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι₁)
    {pr₀ : Y₀ → X₀} (hpr₀ : Continuous pr₀) {pr₁ : Y₁ → X₁} (hpr₁ : Continuous pr₁)
    (hloc₀ : ∀ y, pr₀ y ∈ Set.range ι₀ → ∃ e : OpenPartialHomeomorph Y₀ X₀, y ∈ e.source ∧
      EqOn pr₀ e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    (hloc₁ : ∀ y, pr₁ y ∈ Set.range ι₁ → ∃ e : OpenPartialHomeomorph Y₁ X₁, y ∈ e.source ∧
      EqOn pr₁ e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target)
    {a : S₀' → S₁'} {f' : Y₀ → Y₁} (hf' : Continuous f')
    (hrelf : ∀ y s, pr₀ y = ι₀ s → pr₁ (f' y) = ι₁ (a s)) {q : S₀' → ℂ → ℂ} {q' : S₁' → ℂ → ℂ} {qt : Y₀ → ℂ → ℂ} {qt' : Y₁ → ℂ → ℂ}
    (hrel₀ : ∀ (y : Y₀) (s : S₀'), pr₀ y = ι₀ s → ∀ᶠ z in 𝓝 (chartAt ℂ y y),
      qt y z = q s (chartAt ℂ s (Function.invFun ι₀ (pr₀ ((chartAt ℂ y).symm z)))) *
        deriv (fun w => chartAt ℂ s (Function.invFun ι₀ (pr₀ ((chartAt ℂ y).symm w)))) z ^ 2)
    (hrel₁ : ∀ (y : Y₁) (s : S₁'), pr₁ y = ι₁ s → ∀ᶠ z in 𝓝 (chartAt ℂ y y),
      qt' y z = q' s (chartAt ℂ s (Function.invFun ι₁ (pr₁ ((chartAt ℂ y).symm z)))) *
        deriv (fun w => chartAt ℂ s (Function.invFun ι₁ (pr₁ ((chartAt ℂ y).symm w)))) z ^ 2)
    {y : Y₀} {s : S₀'} (hs : pr₀ y = ι₀ s) :
    lambdaStretch qt qt' f' y (chartAt ℂ y y) = lambdaStretch q q' a s (chartAt ℂ s s) := by
  classical
  have hs₁ : pr₁ (f' y) = ι₁ (a s) := hrelf y s hs
  obtain ⟨e₀, he₀s, he₀eq, he₀d⟩ := hloc₀ y ⟨s, hs.symm⟩
  obtain ⟨e₁, he₁s, he₁eq, he₁d⟩ := hloc₁ (f' y) ⟨a s, hs₁.symm⟩
  obtain ⟨hBd, hB'd, hBc, hBB', hB'B⟩ := s82cmp_chart_pair hι₀ hι₀d hpr₀ hs e₀ he₀s he₀eq he₀d
  obtain ⟨hAd, hA'd, hAc, hAA', hA'A⟩ := s82cmp_chart_pair hι₁ hι₁d hpr₁ hs₁ e₁ he₁s he₁eq he₁d
  set c := chartAt ℂ y y with hc
  set cs := chartAt ℂ s s with hcs
  set c₁ := chartAt ℂ (f' y) (f' y) with hc₁
  set B : ℂ → ℂ := fun z => chartAt ℂ s (Function.invFun ι₀ (pr₀ ((chartAt ℂ y).symm z))) with hB
  set B' : ℂ → ℂ := fun u => chartAt ℂ y (e₀.symm (ι₀ ((chartAt ℂ s).symm u))) with hB'
  set A : ℂ → ℂ := fun w => chartAt ℂ (a s) (Function.invFun ι₁ (pr₁ ((chartAt ℂ (f' y)).symm w)))
    with hA
  set A' : ℂ → ℂ := fun u => chartAt ℂ (f' y) (e₁.symm (ι₁ ((chartAt ℂ (a s)).symm u))) with hA'
  set L' : ℂ → ℂ := localMapExpr f' y with hL'
  set L : ℂ → ℂ := localMapExpr a s with hL
  have hy_src : y ∈ (chartAt ℂ y).source := mem_chart_source ℂ y
  have hct : c ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hy_src
  have hsymm_c : (chartAt ℂ y).symm c = y := (chartAt ℂ y).left_inv hy_src
  have hs_src : s ∈ (chartAt ℂ s).source := mem_chart_source ℂ s
  have hL'c : L' c = c₁ := by
    simp only [hL', localMapExpr, hsymm_c]
    rfl
  have hBcs : B c = cs := hBc
  -- `L' = φ_{f' y} ∘ f' ∘ φ_y⁻¹` is continuous at `c`
  have hL'cont : ContinuousAt L' c := by
    have h1 : ContinuousAt (chartAt ℂ y).symm c := (chartAt ℂ y).continuousAt_symm hct
    have h2 : ContinuousAt f' ((chartAt ℂ y).symm c) := hf'.continuousAt
    have h3 : ContinuousAt (chartAt ℂ (f' y)) (f' ((chartAt ℂ y).symm c)) := by
      rw [hsymm_c]; exact (chartAt ℂ (f' y)).continuousAt (mem_chart_source ℂ (f' y))
    exact h3.comp_of_eq (h2.comp h1) rfl
  -- eventual facts near `c`
  have hsymm_cont : ContinuousAt (chartAt ℂ y).symm c := (chartAt ℂ y).continuousAt_symm hct
  have ha : ∀ᶠ z in 𝓝 c, z ∈ (chartAt ℂ y).target := (chartAt ℂ y).open_target.mem_nhds hct
  have hr : ∀ᶠ z in 𝓝 c, pr₀ ((chartAt ℂ y).symm z) ∈ Set.range ι₀ := by
    have hcomp : ContinuousAt (fun z => pr₀ ((chartAt ℂ y).symm z)) c :=
      hpr₀.continuousAt.comp_of_eq hsymm_cont hsymm_c
    refine hcomp.eventually_mem ?_
    show Set.range ι₀ ∈ 𝓝 (pr₀ ((chartAt ℂ y).symm c))
    rw [hsymm_c, hs]
    exact hι₀.isOpen_range.mem_nhds ⟨s, rfl⟩
  have hd : ∀ᶠ z in 𝓝 c, Function.invFun ι₀ (pr₀ ((chartAt ℂ y).symm z)) ∈ (chartAt ℂ s).source := by
    have hGcont : ContinuousAt (fun y' => Function.invFun ι₀ (pr₀ y')) y := by
      have h2 : ContinuousAt (Function.invFun ι₀) (pr₀ y) := by
        rw [hs]; exact s82cmp_invFun_continuousAt hι₀ ⟨s, rfl⟩
      exact h2.comp hpr₀.continuousAt
    have hG' : ContinuousAt (fun z => Function.invFun ι₀ (pr₀ ((chartAt ℂ y).symm z))) c :=
      hGcont.comp_of_eq hsymm_cont hsymm_c
    refine hG'.eventually_mem ?_
    show (chartAt ℂ s).source ∈ 𝓝 (Function.invFun ι₀ (pr₀ ((chartAt ℂ y).symm c)))
    rw [hsymm_c, hs, Function.leftInverse_invFun hι₀.isEmbedding.injective s]
    exact (chartAt ℂ s).open_source.mem_nhds hs_src
  have hf : ∀ᶠ z in 𝓝 c, f' ((chartAt ℂ y).symm z) ∈ (chartAt ℂ (f' y)).source := by
    have hcomp : ContinuousAt (fun z => f' ((chartAt ℂ y).symm z)) c :=
      hf'.continuousAt.comp_of_eq hsymm_cont hsymm_c
    refine hcomp.eventually_mem ?_
    show (chartAt ℂ (f' y)).source ∈ 𝓝 (f' ((chartAt ℂ y).symm c))
    rw [hsymm_c]
    exact (chartAt ℂ (f' y)).open_source.mem_nhds (mem_chart_source ℂ (f' y))
  have hev : (L ∘ B) =ᶠ[𝓝 c] (A ∘ L') := by
    filter_upwards [ha, hr, hd, hf] with z hz hr' hGs hfs
    simp only [Function.comp, hL, hL', hA, hB, localMapExpr]
    set y' := (chartAt ℂ y).symm z with hy'
    set s' := Function.invFun ι₀ (pr₀ y') with hs'
    have h1 : ι₀ s' = pr₀ y' := Function.invFun_eq hr'
    have h2 : pr₁ (f' y') = ι₁ (a s') := hrelf y' s' h1.symm
    rw [(chartAt ℂ s).left_inv hGs, (chartAt ℂ (f' y)).left_inv hfs, h2]
    rw [Function.leftInverse_invFun hι₁.isEmbedding.injective (a s')]
  -- the complex dilatations agree
  have hBne : deriv B c ≠ 0 := s23_deriv_ne_zero (k := B') hBd (by rw [hBcs]; exact hB'd) hBB'
  have hc₁A : A c₁ = chartAt ℂ (a s) (a s) := by simpa [hA, hc₁] using hAc
  have hAne : deriv A c₁ ≠ 0 := s23_deriv_ne_zero (k := A') hAd (by rw [hc₁A]; exact hA'd) hAA'
  have hLeq : L cs = chartAt ℂ (a s) (a s) := by
    have hsy : (chartAt ℂ s).symm cs = s := by rw [hcs]; exact (chartAt ℂ s).left_inv hs_src
    simp only [hL, localMapExpr, hsy]
  have hΦ : qt y c = q s cs * deriv B c ^ 2 := by
    have h1 := (hrel₀ y s hs).self_of_nhds
    change qt y c = q s (B c) * deriv B c ^ 2 at h1
    rwa [hBcs] at h1
  have hΦ' : qt' (f' y) c₁ = q' (a s) (L cs) * deriv A c₁ ^ 2 := by
    have h1 := (hrel₁ (f' y) (a s) hs₁).self_of_nhds
    change qt' (f' y) c₁ = q' (a s) (A c₁) * deriv A c₁ ^ 2 at h1
    rwa [hc₁A, ← hLeq] at h1
  have hAL : A (L' c) = L cs := by rw [hL'c, hc₁A, hLeq]
  have hLd1 : lambdaStretch qt qt' f' y c =
      lambdaStretchPlane (qt y) (qt' (f' y)) L' c := by
    have he : localMapExprAt f' y c = L' := by
      funext w; simp only [localMapExprAt, hL', localMapExpr, hsymm_c]
    simp only [lambdaStretch, he, hsymm_c]
  have hLd2 : lambdaStretch q q' a s cs =
      lambdaStretchPlane (q s) (q' (a s)) L cs := by
    have hsy : (chartAt ℂ s).symm cs = s := by rw [hcs]; exact (chartAt ℂ s).left_inv hs_src
    have he : localMapExprAt a s cs = L := by
      funext w; simp only [localMapExprAt, hL, localMapExpr, hsy]
    simp only [lambdaStretch, he, hsy]
  rw [hLd1, hLd2]
  refine str_lambda_conj (Ls := L) (Lc := L') (B := B) (A := A) (B' := B') (A' := A')
    (Qs := q s) (Qt := q' (a s)) (Φ := qt y) (Φ' := qt' (f' y)) hBd hB'd hBcs hBB' hB'B
    (by rw [hL'c]; exact hAd) (by rw [hAL, hLeq]; exact hA'd) (by rw [hL'c]; exact hAA') hL'cont hev hAL hBne
    (by rw [hL'c]; exact hAne) hΦ (by rw [hL'c]; exact hΦ')



/-- The surface integral of `λ_f` in the chart-by-chart form equals the point-function form. -/
theorem str_surfaceIntegral_lam {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) (f : S ≃ₜ S) :
    surfaceIntegral q (fun x z => ENNReal.ofReal (lambdaStretch q q f x z)) =
      surfaceIntegral q (fun x z => s26v_lam q f ((chartAt ℂ x).symm z)) := by
  refine (s26v_surfaceIntegral_congr_off q ∅ (fun x => by simp) fun x p hp _ => ?_).symm
  show s26v_lam q f ((chartAt ℂ x).symm (chartAt ℂ x p)) =
    ENNReal.ofReal (lambdaStretch q q f x (chartAt ℂ x p))
  rw [(chartAt ℂ x).left_inv hp, s26v_lambdaStretch_chart hq f x hp]
  rfl

/-- **The Reich–Strebel inequality `‖q‖ ≤ ∬ λ_{h,q} dA_q` for surfaces of type `(g, 2n', 0)`** (`(g, n') ≠ (0, 2)`
etc.): lift through the branched double cover and apply `lemma26_2` upstairs. -/
theorem str_lambda_even {g n' : ℕ} (hn : 0 < n') (hĝ : 3 ≤ 2 * g + n')
    (F₀ : FiniteTypeStructure S₀ g (2 * n') 0) {q : S₀ → ℂ → ℂ} (hq : q ∈ admissibleQDInterior F₀)
    (hqH : IsHolQuadDiff q) (hq0 : q ≠ 0) {h : S₀ ≃ₜ S₀} (hh : IsQCRS h)
    (hhom : ContinuousMap.Homotopic (h : C(S₀, S₀)) (ContinuousMap.id S₀)) :
    quadDiffNorm q ≤ surfaceIntegral q (fun x z => ENNReal.ofReal (lambdaStretch q q h x z)) := by
  classical
  have : Nonempty S₀ := ConnectedSpace.toNonempty
  obtain ⟨X', pr, hgen, hdiff, hsurj, hfib, hfibP, -⟩ := s82bc_exists_branched_double_cover
    (X := F₀.X.carrier) (g := g) (n := n') (Or.inr hn.ne') F₀.genus F₀.P F₀.card_P
  have hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr ∧ Function.Surjective pr ∧
      (∀ x ∉ F₀.P, (pr ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ F₀.P, (pr ⁻¹' {x}).ncard = 1 :=
    ⟨hdiff, hsurj, hfib, hfibP⟩
  obtain ⟨F, qtil, hΦ, hQC, hqt, hqt0, hhomF, hrel⟩ := str_lift_self F₀ hpr₀ hq hqH hq0 hh hhom
  obtain ⟨-, hloc0, -⟩ := s82lc_local_form hpr₀
  have hrange0 : Set.range F₀.ι = (↑F₀.P : Set F₀.X.carrier)ᶜ := by rw [F₀.range_ι]; simp
  have hloc0' : ∀ y, pr y ∈ Set.range F₀.ι → ∃ e : OpenPartialHomeomorph X'.carrier F₀.X.carrier,
      y ∈ e.source ∧ EqOn pr e e.source ∧ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) e.symm e.target :=
    fun y hy => hloc0 y (by rwa [hrange0] at hy)
  have hgenus : 1 < 2 * g + n' - 1 := by omega
  have key := lemma26_2 (S₀ := X'.carrier) hgenus hgen F hQC hhomF.symm hqt hqt0
  have hnorm : quadDiffNorm qtil = 2 * quadDiffNorm q :=
    s82cmp_cover_integral F₀ hdiff.continuous hfib hfibP hloc0 hqH hqt hrel (fun _ => 1) (fun _ => 1)
      (fun _ _ _ => rfl)
  have hU : ∀ y s, pr y = F₀.ι s → s26v_lam qtil F y = s26v_lam q h s := by
    intro y s hs
    exact congrArg ENNReal.ofReal (str_lambda_lift F₀.embedding F₀.holomorphic F₀.embedding
      F₀.holomorphic hdiff.continuous hdiff.continuous hloc0' hloc0' F.continuous hΦ hrel hrel hs)
  have hcov := s82cmp_cover_integral F₀ hdiff.continuous hfib hfibP hloc0 hqH hqt hrel
    (s26v_lam q h) (s26v_lam qtil F) hU
  rw [str_surfaceIntegral_lam hqt F, hcov, hnorm] at key
  rw [str_surfaceIntegral_lam hqH h]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 key

/-- **The Reich–Strebel inequality through a punctured partial cover** (odd `n` and `(0, 4)`): lift `h` to the
two-sheeted cover `T₀ → S₀` of even type `(h', 2n'')` (`s82lc_lift_punctured`, with `f₀ = id`), compose with the
inverse of the lifted identity, apply `str_lambda_even` upstairs and descend through `π₀`. -/
theorem str_lambda_punct {g n : ℕ} (F₀ : FiniteTypeStructure S₀ g n 0) {q : S₀ → ℂ → ℂ}
    (hq : q ∈ admissibleQDInterior F₀) (hqH : IsHolQuadDiff q) (hq0 : q ≠ 0) {h : S₀ ≃ₜ S₀} (hh : IsQCRS h)
    (hhom : ContinuousMap.Homotopic (h : C(S₀, S₀)) (ContinuousMap.id S₀))
    {B₀ : Finset F₀.X.carrier} (hB₀ : B₀ ⊆ F₀.P) {X₀' : ClosedRS.{u}} {pr₀ : X₀'.carrier → F₀.X.carrier}
    (hpr₀ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) pr₀ ∧ Function.Surjective pr₀ ∧
      (∀ x ∉ B₀, (pr₀ ⁻¹' {x}).ncard = 2) ∧ ∀ x ∈ B₀, (pr₀ ⁻¹' {x}).ncard = 1)
    {h' : ℕ} (hX₀' : HasGenus X₀'.carrier h') {n'' : ℕ} (hB : B₀.card + 2 * n'' = 2 * n)
    (hh' : 2 * h' + 2 = 4 * g + B₀.card) (hn'' : 0 < n'') (hgood : 3 ≤ 2 * h' + n'') :
    quadDiffNorm q ≤ surfaceIntegral q (fun x z => ENNReal.ofReal (lambdaStretch q q h x z)) := by
  classical
  have : Nonempty S₀ := ConnectedSpace.toNonempty
  have hf₀ : IsAdmissibleTeichmullerMap F₀ (Homeomorph.refl S₀) q q 0 :=
    ⟨hq, s32w_t324_refl_teich hqH hq0⟩
  obtain ⟨T₀, T₁, _, _, _, _, _, _, _, _, _, _, G₀, G₁, π₀, π₁, ft₀, ft, qt, qt', hπ₀d, hπ₁d, hπ₀s, hπ₀fib,
    hπ₀prop, hπ₀loc, hπ₁loc, hc₀, hc, hTa, hftqc, hftK, hhomt, hpb₀, -⟩ :=
    s82lc_lift_punctured F₀ F₀ hB₀ hpr₀ hX₀' hB hh' hf₀ hh hhom.symm
  have : Nonempty T₀ := ⟨Classical.choose (hπ₀s (Classical.arbitrary S₀))⟩
  -- the lifted self-map
  set F : T₀ ≃ₜ T₀ := ft.trans ft₀.symm with hF
  have hFcov : ∀ t, π₀ (F t) = h (π₀ t) := fun t => by
    have e := hc₀ (ft₀.symm (ft t))
    rw [ft₀.apply_symm_apply, hc t] at e
    exact e.symm
  have hFqc : IsQCRS F := s28q_isQCRS_trans hftqc (s28q_isQCRS_symm hTa.2.qc)
  have hhomF : ContinuousMap.Homotopic (F : C(T₀, T₀)) (ContinuousMap.id T₀) := by
    have h1 : ((ft₀.symm : C(T₁, T₀)).comp (ft₀ : C(T₀, T₁))).Homotopic
        ((ft₀.symm : C(T₁, T₀)).comp (ft : C(T₀, T₁))) := by
      obtain ⟨H⟩ := hhomt
      exact ⟨{ toFun := fun p => ft₀.symm (H p)
               continuous_toFun := ft₀.symm.continuous.comp H.continuous
               map_zero_left := fun x => by simp
               map_one_left := fun x => by simp }⟩
    have e1 : (ft₀.symm : C(T₁, T₀)).comp (ft₀ : C(T₀, T₁)) = ContinuousMap.id T₀ := by
      ext t; simp
    have e2 : (ft₀.symm : C(T₁, T₀)).comp (ft : C(T₀, T₁)) = (F : C(T₀, T₀)) := by
      ext t; simp [hF]
    rw [e1, e2] at h1
    exact h1.symm
  have hup := str_lambda_even hn'' hgood G₀ hTa.1 hTa.2.initial hTa.2.initial_ne hFqc hhomF
  -- the projections to the closed surface
  set p₀ : T₀ → F₀.X.carrier := fun t => F₀.ι (π₀ t) with hp₀
  have hp₀c : Continuous p₀ := F₀.embedding.continuous.comp hπ₀d.continuous
  have hr0 : range F₀.ι = (↑F₀.P)ᶜ := by rw [F₀.range_ι]; simp
  have hιP₀ : ∀ s, F₀.ι s ∉ F₀.P := fun s => by
    have : F₀.ι s ∈ range F₀.ι := ⟨s, rfl⟩
    rw [hr0] at this; exact this
  have hloc0 := s82cmp_cover_loc_comp F₀.embedding F₀.holomorphic hπ₀loc
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
      qt y z = q s (chartAt ℂ s (Function.invFun F₀.ι (p₀ ((chartAt ℂ y).symm z)))) *
        deriv (fun w => chartAt ℂ s (Function.invFun F₀.ι (p₀ ((chartAt ℂ y).symm w)))) z ^ 2 := by
    intro y s hys
    have hy : π₀ y = s := F₀.embedding.injective hys
    subst hy
    simp only [hp₀, hinvι]
    exact hpb₀ y
  have hq' : IsHolQuadDiff qt := hTa.2.initial
  have hrelf : ∀ (y : T₀) (s : S₀), p₀ y = F₀.ι s → p₀ (F y) = F₀.ι (h s) := by
    intro y s hys
    have hy : π₀ y = s := F₀.embedding.injective hys
    show F₀.ι (π₀ (F y)) = F₀.ι (h s)
    rw [hFcov, hy]
  have hU : ∀ y s, p₀ y = F₀.ι s → s26v_lam qt F y = s26v_lam q h s := by
    intro y s hs
    exact congrArg ENNReal.ofReal (str_lambda_lift F₀.embedding F₀.holomorphic F₀.embedding
      F₀.holomorphic hp₀c hp₀c (fun y _ => hloc0 y) (fun y _ => hloc0 y) F.continuous hrelf hrel hrel hs)
  have hnorm : quadDiffNorm qt = 2 * quadDiffNorm q :=
    s82cmp_cover_integral_p F₀ hp₀c hclosed hfib hfibP hloc0' hqH hq' hrel (fun _ => 1) (fun _ => 1)
      (fun _ _ _ => rfl)
  have hcov := s82cmp_cover_integral_p F₀ hp₀c hclosed hfib hfibP hloc0' hqH hq' hrel
    (s26v_lam q h) (s26v_lam qt F) hU
  rw [str_surfaceIntegral_lam hq' F, hcov, hnorm] at hup
  rw [str_surfaceIntegral_lam hqH h]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 hup


/-- **The Reich–Strebel inequality `‖q‖ ≤ ∬ λ_{h,q} dA_q` on every non-exceptional finite-type surface `(g, n, 0)`**
for `h ≃ id` quasiconformal and `q` a non-zero admissible differential: closed case `lemma26_2`, even type through
the branched cover (`str_lambda_even`), odd type and `(0, 4)` through the punctured cover (`str_lambda_punct`). -/
theorem str_surface_lambda {g n : ℕ} (hex : ¬ IsExceptionalType g n 0)
    (F₀ : FiniteTypeStructure S₀ g n 0) {q : S₀ → ℂ → ℂ} (hq : q ∈ admissibleQDInterior F₀)
    (hqH : IsHolQuadDiff q) (hq0 : q ≠ 0) {h : S₀ ≃ₜ S₀} (hh : IsQCRS h)
    (hhom : ContinuousMap.Homotopic (h : C(S₀, S₀)) (ContinuousMap.id S₀)) :
    quadDiffNorm q ≤ surfaceIntegral q (fun x z => ENNReal.ofReal (lambdaStretch q q h x z)) := by
  classical
  obtain ⟨k', rfl | rfl⟩ := Nat.even_or_odd' n
  · rcases Nat.eq_zero_or_pos k' with rfl | hk'
    · -- closed case
      obtain ⟨hcS, ⟨eS⟩⟩ := s82cmp_type_zero F₀
      haveI : CompactSpace S₀ := hcS
      have hg : 1 < g := by
        by_contra hg'
        have : g = 0 ∨ g = 1 := by omega
        rcases this with rfl | rfl <;> exact hex (by simp [IsExceptionalType])
      let XS : ClosedRS.{u} := ⟨S₀⟩
      have hSg : HasGenus S₀ g :=
        hasGenus_of_homeomorph (X := XS) F₀.genus (eS : F₀.X.carrier ≃ₜ XS.carrier)
      exact lemma26_2 hg hSg h hh hhom hqH hq0
    · by_cases hg0 : g = 0
      · subst hg0
        rcases Nat.lt_or_ge k' 3 with hlt | hge
        · have : k' = 1 ∨ k' = 2 := by omega
          rcases this with rfl | rfl
          · exact (hex (by simp [IsExceptionalType])).elim
          · obtain ⟨X₀', pr₀, hX₀', hd, hs, h2, h1, -⟩ := s82bc_exists_branched_double_cover
              (X := F₀.X.carrier) (g := 0) (n := 2) (Or.inr two_ne_zero) F₀.genus F₀.P (by rw [F₀.card_P])
            exact str_lambda_punct F₀ hq hqH hq0 hh hhom (subset_refl _) ⟨hd, hs, h2, h1⟩ hX₀'
              (n'' := 2) (by rw [F₀.card_P]) (by rw [F₀.card_P]) (by norm_num) (by norm_num)
        · exact str_lambda_even hk' (by omega) F₀ hq hqH hq0 hh hhom
      · exact str_lambda_even hk' (by omega) F₀ hq hqH hq0 hh hhom
  · by_cases h03 : g = 0 ∧ k' = 1
    · obtain ⟨rfl, rfl⟩ := h03
      exact (s82lc_uniq_03 F₀ ⟨hq, s32w_t324_refl_teich hqH hq0⟩).elim
    have hPne : F₀.P.Nonempty := by
      rw [← Finset.card_pos, F₀.card_P]; omega
    obtain ⟨p, hp⟩ := hPne
    have hBc : (F₀.P.erase p).card = 2 * k' := by
      rw [Finset.card_erase_of_mem hp, F₀.card_P]; omega
    have hgn : g ≠ 0 ∨ k' ≠ 0 := by
      by_contra hc
      push Not at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact hex (by simp [IsExceptionalType])
    obtain ⟨X₀', pr₀, hX₀', hd, hs, h2, h1, -⟩ := s82bc_exists_branched_double_cover (X := F₀.X.carrier)
      hgn F₀.genus (F₀.P.erase p) hBc
    exact str_lambda_punct F₀ hq hqH hq0 hh hhom (Finset.erase_subset p F₀.P) ⟨hd, hs, h2, h1⟩ hX₀'
      (n'' := k' + 1) (by rw [hBc]; ring) (by rw [hBc]; omega) (by omega) (by omega)

end LiZhongQC
