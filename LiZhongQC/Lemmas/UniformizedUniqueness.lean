import LiZhongQC.Lemmas.FluxRoute

/-!
# Uniqueness companions for surfaces given as `ℍ/Γ` (`utm_`), and generic q.c.-surface helpers

A verbatim relocation (delivery R, coordinator 553e2d, leader decision 2026-09-26), names unchanged, so that S27 can
use Teichmüller's uniqueness theorem for `ℍ/Γ` surfaces.  Nothing here depends on S27 or later.
* From `Lemmas/UniformizedTeichmuller` (see its module docstring, installments 1-4 and 6), Parts 1-4: the companions
  `thm23_1_cor_of_uniformization`, `conformal_unique_extremal_of_uniformization`, `lemma26_1_of_uniformization`,
  `lemma26_2_of_uniformization`, `thm26_2_uniqueness_of_uniformization`, `eq26_15_16_of_uniformization`,
  `teichmullerMap_isExtremal_of_uniformization` and their `utm_` helpers (the lift `utm_liftQD`, the `utm_d_`
  machinery, ...); and from its Part 5 the Teichmüller coefficient `utm_x_tcoeff`, S3 at a point
  (`utm_x1_liftQD_zeros_countable`, `utm_x1_lift_pointwise`), [S7a] (`utm_x_teichmullerMap_symm`), [S7b]
  (`utm_x_eq_smul_of_trans`) and the inverse trick `utm_x_dil_le_of_equiv`.
* From S26 (moved with their statements; bodies proved through `s22hg_exists_fuchsian_uniformization`): `lemma26_1`, `lemma26_2`, `thm26_2_uniqueness`, `eq26_15_16`, `conformal_unique_extremal`, `teichmullerMap_isExtremal`.
* From S28: `fundamentalGroupMulEquivOfHomeomorph`, `hasGenus_of_homeomorph`.
* From S29: the generic q.c.-surface helpers `s29_m_isKQC_of_maxDilatation_le` … `s29_m_maxDil_conj_biholo`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section

namespace LiZhongQC

universe u v

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S₁ : Type v} [TopologicalSpace S₁] [ChartedSpace ℂ S₁]

/-! ## Part 0. Generic helpers (moved from S28 and S29) -/

/-- A homeomorphism `f : X ≃ₜ Y` with `f x = y` induces an isomorphism of fundamental groups
`π₁(X, x) ≃* π₁(Y, y)`: Mathlib's `FundamentalGroup.mapOfEq` for `f` and for `f⁻¹`, which are
mutually inverse because `f⁻¹ ∘ f = id` and `f ∘ f⁻¹ = id` pointwise (`Path.ext`). -/
def fundamentalGroupMulEquivOfHomeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ Y) {x : X} {y : Y} (h : f x = y) : FundamentalGroup X x ≃* FundamentalGroup Y y where
  toFun := FundamentalGroup.mapOfEq (f : C(X, Y)) h
  invFun := FundamentalGroup.mapOfEq (f.symm : C(Y, X)) (by rw [← h]; exact f.symm_apply_apply x)
  left_inv := by
    rintro ⟨γ⟩
    show FundamentalGroup.mapOfEq (f.symm : C(Y, X)) _
      (FundamentalGroup.mapOfEq (f : C(X, Y)) h
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
    refine congrArg (fun p : Path x x => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) ?_
    refine Path.ext (funext fun t => ?_)
    simp [Path.cast_coe, Path.map_coe]
  right_inv := by
    rintro ⟨γ⟩
    show FundamentalGroup.mapOfEq (f : C(X, Y)) h
      (FundamentalGroup.mapOfEq (f.symm : C(Y, X)) _
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
    refine congrArg (fun p : Path y y => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) ?_
    refine Path.ext (funext fun t => ?_)
    simp [Path.cast_coe, Path.map_coe]
  map_mul' a b := map_mul (FundamentalGroup.mapOfEq (f : C(X, Y)) h) a b

/-- A homeomorphic image of a surface of genus `g` has genus `g`: compactness is part of
`ClosedRS`, and `π₁(X, x) ≅ π₁(S₀, f⁻¹(x)) ≅ surfaceGroup g` by transport of the fundamental
group along the homeomorphism (`fundamentalGroupMulEquivOfHomeomorph`). -/
theorem hasGenus_of_homeomorph {g : ℕ} (hS : HasGenus S₀ g) {X : ClosedRS.{u}} (f : S₀ ≃ₜ X.carrier) :
    HasGenus X.carrier g := by
  -- the complex structure of `S₀` plays no role (the instance is kept for uniformity of the
  -- statements in this file); compactness is part of `ClosedRS`, and the fundamental groups are
  -- transported along `f`
  have _inst : ChartedSpace ℂ S₀ := inferInstance
  refine ⟨inferInstance, fun x => ?_⟩
  obtain ⟨e⟩ := hS.2 (f.symm x)
  exact ⟨(fundamentalGroupMulEquivOfHomeomorph f (f.apply_symm_apply x)).symm.trans e⟩

/-- Theorem 10.1 in the plane: a `K`-q.c. map `f` of `D` whose maximal dilatation satisfies `K[f] ≤ K'`, with
`1 ≤ K'`, is `K'`-q.c. -/
theorem s29_m_isKQC_of_maxDilatation_le {f : ℂ → ℂ} {D : Set ℂ} {K K' : ℝ} (hf : IsKQC f D K)
    (hK' : 1 ≤ K') (hle : maxDilatation f D ≤ ENNReal.ofReal K') : IsKQC f D K' := by
  have hD : IsOpen D := hf.1
  have hhom : IsHomeomorphOnto f D (f '' D) := hf.2.2.1
  refine (thm10_1_isKQC_iff hD hK' hhom).2 ⟨thm9_1_isACL hf, ?_⟩
  have hae := ae_le_essSup (μ := volume.restrict D)
    (f := fun z => ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) / (‖dz f z‖ - ‖dzbar f z‖)))
  filter_upwards [hae, thm9_6_cor2_jacobian_pos hf] with z h1 hJ
  have h2 : ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) / (‖dz f z‖ - ‖dzbar f z‖)) ≤ ENNReal.ofReal K' :=
    h1.trans hle
  have h3 := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h2
  unfold jacobian at hJ
  have ha : 0 ≤ ‖dz f z‖ := norm_nonneg _
  have hb : 0 ≤ ‖dzbar f z‖ := norm_nonneg _
  have hlt : ‖dzbar f z‖ < ‖dz f z‖ := by nlinarith
  rw [div_le_iff₀ (sub_pos.2 hlt)] at h3
  linarith

/-- `1 ≤ K[f]` for a q.c. map `f` of a nonempty surface: every local expression has positive Jacobian almost
everywhere (Theorem 9.6). -/
theorem s29_m_one_le_maxDilatationRS {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [Nonempty A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} (hf : IsQCRS f) :
    1 ≤ maxDilatationRS f := by
  obtain ⟨K, -, hK⟩ := hf
  obtain ⟨x⟩ := (inferInstance : Nonempty A)
  refine le_trans ?_ (le_iSup (fun x => maxDilatation (localMapExpr f x) (localMapDomain f x)) x)
  have hΩ := s23_localMapDomain_isOpen f.continuous x
  have hne : (localMapDomain f x).Nonempty := ⟨_, (s23_h_center f x).1⟩
  have hμ : volume.restrict (localMapDomain f x) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact hΩ.measure_ne_zero volume hne
  rw [maxDilatation, ← essSup_const (1 : ℝ≥0∞) hμ]
  refine essSup_mono_ae ?_
  filter_upwards [thm9_6_cor2_jacobian_pos (hK x)] with z hJ
  unfold jacobian at hJ
  set a := ‖dz (localMapExpr f x) z‖
  set b := ‖dzbar (localMapExpr f x) z‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hlt : b < a := by nlinarith
  show (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((a + b) / (a - b))
  rw [ENNReal.one_le_ofReal, one_le_div (sub_pos.2 hlt)]
  linarith

/-- `K[f] ≠ ∞` for a q.c. map `f` of surfaces. -/
theorem s29_m_maxDilatationRS_ne_top {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} (hf : IsQCRS f) :
    maxDilatationRS f ≠ ⊤ := by
  obtain ⟨K, hK⟩ := hf
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (maxDilatationRS_le hK)

/-- `1 ≤ K[f]` in `ℝ`, for a q.c. map `f` of a nonempty surface. -/
theorem s29_m_one_le_toReal {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [Nonempty A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} (hf : IsQCRS f) :
    1 ≤ (maxDilatationRS f).toReal := by
  have := ENNReal.toReal_mono (s29_m_maxDilatationRS_ne_top hf) (s29_m_one_le_maxDilatationRS hf)
  simpa using this

/-- A q.c. map `f` of surfaces with `K[f] ≤ K'`, `1 ≤ K'`, is `K'`-q.c. (Theorem 10.1 in every chart). -/
theorem s29_m_isKQCRS_of_le {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} (hf : IsQCRS f) {K' : ℝ}
    (hK' : 1 ≤ K') (hle : maxDilatationRS f ≤ ENNReal.ofReal K') : IsKQCRS f K' := by
  obtain ⟨K, -, hK⟩ := hf
  refine ⟨hK', fun x => s29_m_isKQC_of_maxDilatation_le (hK x) hK' ?_⟩
  exact (le_iSup (fun x => maxDilatation (localMapExpr f x) (localMapDomain f x)) x).trans hle

/-- A q.c. map `f` of a nonempty surface is `K[f]`-q.c. -/
theorem s29_m_isKQCRS_maxDil {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [Nonempty A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} (hf : IsQCRS f) :
    IsKQCRS f (maxDilatationRS f).toReal :=
  s29_m_isKQCRS_of_le hf (s29_m_one_le_toReal hf)
    (by rw [ENNReal.ofReal_toReal (s29_m_maxDilatationRS_ne_top hf)])

/-- The inverse of a `K`-q.c. map of surfaces is `K`-q.c.: in charts it is the inverse of the local expression
(`thm7_2_inv`). -/
theorem s29_m_isKQCRS_symm {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} {K : ℝ} (hf : IsKQCRS f K) :
    IsKQCRS f.symm K := by
  refine ⟨hf.1, fun y => ?_⟩
  set x := f.symm y
  have hfx : f x = y := f.apply_symm_apply y
  set L := localMapExpr f x with hLdef
  set D := localMapDomain f x with hDdef
  have hL : IsKQC L D K := hf.2 x
  have hinj : InjOn L D := hL.2.2.1.2.1
  have hLz : ∀ z ∈ D, L z = chartAt ℂ y (f ((chartAt ℂ x).symm z)) := by
    intro z _
    simp only [hLdef, localMapExpr, hfx]
  have hDz : ∀ z ∈ D, z ∈ (chartAt ℂ x).target ∧ f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ y).source := by
    intro z hz
    have hz' := hz
    simp only [hDdef, localMapDomain, mem_inter_iff, mem_preimage] at hz'
    rw [hfx] at hz'
    exact hz'
  have hback : ∀ z ∈ D, localMapExpr f.symm y (L z) = z := by
    intro z hz
    obtain ⟨h1, h2⟩ := hDz z hz
    rw [hLz z hz]
    simp only [localMapExpr]
    rw [(chartAt ℂ y).left_inv h2, f.symm_apply_apply, (chartAt ℂ x).right_inv h1]
  have himg : L '' D = localMapDomain f.symm y := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨h1, h2⟩ := hDz z hz
      rw [hLz z hz]
      refine ⟨(chartAt ℂ y).map_source h2, ?_⟩
      show f.symm ((chartAt ℂ y).symm (chartAt ℂ y (f ((chartAt ℂ x).symm z)))) ∈
        (chartAt ℂ (f.symm y)).source
      rw [(chartAt ℂ y).left_inv h2, f.symm_apply_apply]
      exact (chartAt ℂ x).map_target h1
    · rintro ⟨hw1, hw2⟩
      have hw2' : f.symm ((chartAt ℂ y).symm w) ∈ (chartAt ℂ x).source := hw2
      have hzD : chartAt ℂ x (f.symm ((chartAt ℂ y).symm w)) ∈ D := by
        simp only [hDdef, localMapDomain, mem_inter_iff, mem_preimage, hfx]
        refine ⟨(chartAt ℂ x).map_source hw2', ?_⟩
        rw [(chartAt ℂ x).left_inv hw2', f.apply_symm_apply]
        exact (chartAt ℂ y).map_target hw1
      refine ⟨chartAt ℂ x (f.symm ((chartAt ℂ y).symm w)), hzD, ?_⟩
      rw [hLz _ hzD, (chartAt ℂ x).left_inv hw2', f.apply_symm_apply, (chartAt ℂ y).right_inv hw1]
  have hinv := thm7_2_inv hL
  rw [himg] at hinv
  refine ad_isKQC_congr hinv fun w hw => ?_
  rw [← himg] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  rw [hback z hz, hinj.leftInvOn_invFunOn hz]

/-- The inverse of a q.c. map `f` of a nonempty surface is q.c., with `K[f⁻¹] ≤ K[f]`. -/
theorem s29_m_maxDil_symm_le {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [Nonempty A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} (hf : IsQCRS f) :
    IsQCRS f.symm ∧ maxDilatationRS f.symm ≤ maxDilatationRS f := by
  have h := s29_m_isKQCRS_symm (s29_m_isKQCRS_maxDil hf)
  refine ⟨⟨_, h⟩, ?_⟩
  have := maxDilatationRS_le h
  rwa [ENNReal.ofReal_toReal (s29_m_maxDilatationRS_ne_top hf)] at this

/-- `0 ≤ ½ ln K[f]` for a q.c. map `f` of a nonempty surface. -/
theorem s29_m_half_log_nonneg {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [Nonempty A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} (hf : IsQCRS f) :
    0 ≤ (1 / 2 : ℝ) * Real.log (maxDilatationRS f).toReal := by
  have := Real.log_nonneg (s29_m_one_le_toReal hf)
  positivity

/-- `½ ln K` is monotone: `K[g'] ≤ K[g]` gives `½ ln K[g'] ≤ ½ ln K[g]`, for q.c. maps `g'` (of a nonempty
surface) and `g`. -/
theorem s29_m_half_log_mono {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [Nonempty A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {C : Type*} [TopologicalSpace C] [ChartedSpace ℂ C]
    {D : Type*} [TopologicalSpace D] [ChartedSpace ℂ D] {g' : A ≃ₜ B} (hg' : IsQCRS g') {g : C ≃ₜ D}
    (hg : IsQCRS g) (hle : maxDilatationRS g' ≤ maxDilatationRS g) :
    (1 / 2 : ℝ) * Real.log (maxDilatationRS g').toReal ≤
      (1 / 2 : ℝ) * Real.log (maxDilatationRS g).toReal := by
  have h1 := s29_m_one_le_toReal hg'
  have h2 : (maxDilatationRS g').toReal ≤ (maxDilatationRS g).toReal :=
    ENNReal.toReal_mono (s29_m_maxDilatationRS_ne_top hg) hle
  have := Real.log_le_log (by linarith) h2
  linarith

/-- Conformal invariance of `K` ((23.4)): for a q.c. `g` and biholomorphic `c₁`, `c₂`, the map `c₂ ∘ g ∘ c₁` is
q.c. with `K[c₂ ∘ g ∘ c₁] ≤ K[g]`. -/
theorem s29_m_maxDil_conj_biholo {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]
    {C : Type*} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ) ω C]
    {D : Type*} [TopologicalSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ) ω D]
    {g : B ≃ₜ C} (hg : IsQCRS g) {c₁ : A ≃ₜ B} (hc₁ : IsBiholomorphic c₁) {c₂ : C ≃ₜ D}
    (hc₂ : IsBiholomorphic c₂) :
    IsQCRS (c₁.trans (g.trans c₂)) ∧ maxDilatationRS (c₁.trans (g.trans c₂)) ≤ maxDilatationRS g := by
  obtain ⟨K, hK⟩ := hg
  have h1 : IsKQCRS c₁ 1 := (isKQCRS_one_iff c₁).2 hc₁
  have h2 : IsKQCRS c₂ 1 := (isKQCRS_one_iff c₂).2 hc₂
  have hc₁le : maxDilatationRS c₁ ≤ 1 := by simpa using maxDilatationRS_le h1
  have hc₂le : maxDilatationRS c₂ ≤ 1 := by simpa using maxDilatationRS_le h2
  obtain ⟨hgc, hgcle⟩ := eq23_4 hK h2
  obtain ⟨hall, hallle⟩ := eq23_4 h1 hgc
  refine ⟨⟨_, hall⟩, ?_⟩
  calc maxDilatationRS (c₁.trans (g.trans c₂)) = maxDilatationRS ((g.trans c₂) ∘ c₁) := rfl
    _ ≤ maxDilatationRS (g.trans c₂) * maxDilatationRS c₁ := hallle
    _ ≤ maxDilatationRS (g.trans c₂) * 1 := by gcongr
    _ = maxDilatationRS (c₂ ∘ g) := by rw [mul_one]; rfl
    _ ≤ maxDilatationRS c₂ * maxDilatationRS g := hgcle
    _ ≤ 1 * maxDilatationRS g := by gcongr
    _ = maxDilatationRS g := one_mul _

/-! ## Part 1. Route U1 (proved): `thm23_1_cor` and `conformal_unique_extremal` under a uniformization

The lift `F` of a biholomorphic `φ ≃ id` is Möbius (`utm_eq_smul_of_isKQC_one`); normalized by
`thm23_1_homotopy_iff` it commutes with `Γ₀`; its displacement is then `Γ₀`-invariant, hence bounded on the
compact quotient (`utm_exists_compact_translate`), so it is `±1` (`utm_sl2_eq_of_bounded_displacement`). -/

section U1

open UpperHalfPlane

/-- `-1` acts trivially on `ℍ`. -/
theorem utm_neg_one_smul (z : ℍ) : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z = z := by
  ext1
  rw [h36t_coe_smul]
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply,
    Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), neg_zero]
  push_cast
  have : ((-1 : ℂ) * z + 0) / (0 * z + -1) = (z : ℂ) := by
    rw [zero_mul, zero_add, add_zero, div_neg, div_one, neg_mul, one_mul, neg_neg]
  exact this

/-- **`thm23_1_cor` under a Fuchsian uniformization of a compact surface**, with the Stage 2 inputs as
explicit hypotheses: a lift `F` of `φ` (`exists_lift`), the relation `F γ F⁻¹ = γ₁ γ γ₁⁻¹` from
`thm23_1_homotopy_iff` (with the lift `id` of `id`), and the Möbius form `F = m ·` of the lift of a
biholomorphic map (`lift_isKQC_automorphic` with `K = 1`, `thm7_3`, and the classification of the
conformal automorphisms of `ℍ`). -/
theorem utm_cor_uniformized {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S} (hp : IsUniformization Γ p)
    (φ : S → S) (F : ℍ ≃ₜ ℍ) (hF : IsLift p p φ F)
    (γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hγ₁ : γ₁ ∈ Γ)
    (hrel : ∀ γ ∈ Γ, ∀ τ : ℍ, F (γ • F.symm τ) = γ₁ • (γ • (γ₁⁻¹ • τ)))
    (m : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hFm : ∀ τ, F τ = m • τ) : φ = id := by
  have hFs : ∀ τ, F.symm τ = m⁻¹ • τ := by
    intro τ
    apply F.injective
    rw [F.apply_symm_apply, hFm, smul_inv_smul]
  -- `M = γ₁⁻¹ m` commutes with `Γ`
  set M := γ₁⁻¹ * m with hMdef
  have hM : ∀ γ ∈ Γ, ∀ z : ℍ, M • γ • z = γ • M • z := by
    intro γ hγ z
    have h := hrel γ hγ (m • z)
    rw [hFs, inv_smul_smul, hFm] at h
    -- `m γ z = γ₁ γ γ₁⁻¹ m z`
    rw [hMdef, mul_smul, mul_smul, h, ← mul_smul γ₁⁻¹ γ₁, inv_mul_cancel, one_smul]
  have hM1 := utm_commute_eq_one hp M hM
  -- hence `F = γ₁ ·`
  have hFγ : ∀ τ, F τ = γ₁ • τ := by
    intro τ
    have hm : m = γ₁ * M := by rw [hMdef, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [hFm, hm, mul_smul]
    rcases hM1 with h | h
    · rw [h, one_smul]
    · rw [h, utm_neg_one_smul]
  obtain ⟨-, -, hsurj, hfib⟩ := hp
  funext s
  obtain ⟨τ, rfl⟩ := hsurj s
  rw [← hF τ, hFγ τ, id]
  exact ((hfib τ (γ₁ • τ)).2 ⟨γ₁, hγ₁, rfl⟩).symm

end U1

/-- A quasiconformal map of Riemann surfaces with `K[h] = 1` is `1`-quasiconformal (Theorem 10.1 in every chart).
(Scout U's `h35_isKQCRS_one_of_maxDil`.) -/
theorem utm_isKQCRS_one_of_maxDil {h : S₀ ≃ₜ S₁} (hh : IsQCRS h) (h1 : maxDilatationRS h = 1) :
    IsKQCRS h 1 := by
  obtain ⟨K, -, hK⟩ := hh
  refine ⟨le_rfl, fun x => ?_⟩
  have hx : IsKQC (localMapExpr h x) (localMapDomain h x) K := hK x
  have hle : maxDilatation (localMapExpr h x) (localMapDomain h x) ≤ 1 :=
    h1 ▸ le_iSup (fun x => maxDilatation (localMapExpr h x) (localMapDomain h x)) x
  refine (thm10_1_isKQC_iff hx.1 le_rfl hx.2.2.1).2 ⟨thm9_1_isACL hx, ?_⟩
  filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict (localMapDomain h x))
      (fun z => ENNReal.ofReal ((‖dz (localMapExpr h x) z‖ + ‖dzbar (localMapExpr h x) z‖) /
        (‖dz (localMapExpr h x) z‖ - ‖dzbar (localMapExpr h x) z‖))),
    thm9_6_cor2_jacobian_pos hx] with z hz hJ
  have hz1 := ENNReal.ofReal_le_one.1 (hz.trans hle)
  unfold jacobian at hJ
  have hlt : ‖dzbar (localMapExpr h x) z‖ < ‖dz (localMapExpr h x) z‖ := by
    nlinarith [norm_nonneg (dz (localMapExpr h x) z), norm_nonneg (dzbar (localMapExpr h x) z)]
  rw [div_le_one (sub_pos.2 hlt)] at hz1
  linarith

/-- **Companion of `thm23_1_cor`** (Theorem 23.1, Corollary) for a surface given as `ℍ/Γ₀`: a conformal
automorphism homotopic to the identity is the identity.

*Derivation note:* the book statement `thm23_1_cor` follows from this companion plus `thm22_3_classification`
(which supplies a Fuchsian uniformization of a closed surface of genus `g > 1`). -/
theorem thm23_1_cor_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ} (hg : 1 < g)
    (hS : HasGenus S₀ g) (φ : S₀ ≃ₜ S₀) (hφ : IsBiholomorphic φ)
    (hhom : ContinuousMap.Homotopic (φ : C(S₀, S₀)) (ContinuousMap.id S₀))
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) : ⇑φ = id := by
  have _ := hg
  have : CompactSpace S₀ := hS.1
  obtain ⟨τ₁, hτ₁⟩ := hp₀.2.2.1 (φ (p₀ UpperHalfPlane.I))
  obtain ⟨F, hF, -⟩ := exists_lift hp₀ hp₀ φ UpperHalfPlane.I τ₁ hτ₁
  have hK : IsKQCRS φ 1 := (isKQCRS_one_iff φ).2 hφ
  obtain ⟨m, hm⟩ := utm_eq_smul_of_isKQC_one F (lift_isKQC_automorphic hp₀ hp₀ hK hF).1
  have hG : IsLift p₀ p₀ (Homeomorph.refl S₀) (Homeomorph.refl UpperHalfPlane) := fun τ => rfl
  have hhom' : ContinuousMap.Homotopic (φ : C(S₀, S₀)) ((Homeomorph.refl S₀ : S₀ ≃ₜ S₀) : C(S₀, S₀)) :=
    hhom
  obtain ⟨γ₁, hγ₁, hrel⟩ := (thm23_1_homotopy_iff hp₀ hp₀ φ (Homeomorph.refl S₀) hF hG).1 hhom'
  exact utm_cor_uniformized hp₀ φ F hF γ₁ hγ₁ (fun γ hγ τ => hrel γ hγ τ) m hm

/-- **Companion of `conformal_unique_extremal`**: a quasiconformal `h` with `K[h] = 1` homotopic to a conformal
`c` equals `c`, when `S₀` is given as `ℍ/Γ₀` (`c⁻¹ ∘ h` is biholomorphic and homotopic to the identity).

*Derivation note:* the book statement `conformal_unique_extremal` follows from this companion plus
`thm22_3_classification` (a Fuchsian uniformization of `S₀`). -/
theorem conformal_unique_extremal_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {c h : S₀ ≃ₜ S₁} (hc : IsBiholomorphic c)
    (hh : IsQCRS h) (hhom : ContinuousMap.Homotopic (c : C(S₀, S₁)) (h : C(S₀, S₁)))
    (h1 : maxDilatationRS h = 1)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) : ⇑h = ⇑c := by
  have _ := h₁
  have hb : IsBiholomorphic h := (isKQCRS_one_iff h).1 (utm_isKQCRS_one_of_maxDil hh h1)
  have hφb : IsBiholomorphic (h.trans c.symm) := by
    have := IsBiholomorphic.comp (IsBiholomorphic.homeomorph_symm hc) hb
    exact this
  have hφh : ContinuousMap.Homotopic ((h.trans c.symm : S₀ ≃ₜ S₀) : C(S₀, S₀)) (ContinuousMap.id S₀) := by
    have h2 := ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl (c.symm : C(S₁, S₀))) hhom.symm
    have e1 : (c.symm : C(S₁, S₀)).comp (h : C(S₀, S₁)) = ((h.trans c.symm : S₀ ≃ₜ S₀) : C(S₀, S₀)) := rfl
    have e2 : (c.symm : C(S₁, S₀)).comp (c : C(S₀, S₁)) = ContinuousMap.id S₀ := by
      ext x
      simp
    rw [e1, e2] at h2
    exact h2
  have hid := thm23_1_cor_of_uniformization hg h₀ (h.trans c.symm) hφb hφh hp₀
  funext x
  have hx : c.symm (h x) = x := by
    have := congrFun hid x
    simpa [Homeomorph.trans_apply] using this
  calc h x = c (c.symm (h x)) := (c.apply_symm_apply _).symm
    _ = c x := by rw [hx]

/-- §26.4 (the conformal case, `k = 0`): a conformal map is the unique extremal map in its
homotopy class; a quasiconformal map homotopic to a conformal map `c` with `K[h] = 1` equals `c`. -/
theorem conformal_unique_extremal [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {c h : S₀ ≃ₜ S₁} (hc : IsBiholomorphic c)
    (hh : IsQCRS h) (hhom : ContinuousMap.Homotopic (c : C(S₀, S₁)) (h : C(S₀, S₁)))
    (h1 : maxDilatationRS h = 1) : ⇑h = ⇑c := by
  obtain ⟨Γ₀, _p, _hΓ, _hfree, hp₀⟩ :=
    s22hg_exists_fuchsian_uniformization (S := S₀) hg h₀
  exact conformal_unique_extremal_of_uniformization hg h₀ h₁ hc hh hhom h1 hp₀


/-! ## Part 2. Lemma 26.1 on `ℍ/Γ₀`: lifted arcs are shortest (route A-lifted)

`h26b`'s transport of `fx_arc_shortest` to `ℍ` (proved), scout A's `Γ`-commuting lift (proved), the lifted
differential `utm_liftQD` and the stubs [P0]–[P6]. -/

section ArcShortest

/-- The derivative of the Cayley map `z ↦ (z - i)/(z + i)`. -/
theorem utm_hasDerivAt_cayley {z : ℂ} (hz : z + I ≠ 0) :
    HasDerivAt cayley (2 * I / (z + I) ^ 2) z := by
  have h := ((hasDerivAt_id z).sub_const I).div ((hasDerivAt_id z).add_const I) hz
  have e : cayley = fun y => (id y - I) / (id y + I) := by
    funext y
    simp [cayley]
  rw [e]
  refine h.congr_deriv ?_
  simp only [id]
  ring

/-- The derivative of the inverse Cayley map `w ↦ i (1 + w)/(1 - w)`. -/
theorem utm_hasDerivAt_cayleyInv {w : ℂ} (hw : (1 : ℂ) - w ≠ 0) :
    HasDerivAt cayleyInv (2 * I / (1 - w) ^ 2) w := by
  have h := (((hasDerivAt_id w).const_add 1).const_mul I).div ((hasDerivAt_id w).const_sub 1) hw
  have e : cayleyInv = fun w => I * (1 + id w) / (1 - id w) := by
    funext w
    simp [cayleyInv]
  rw [e]
  refine h.congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- `(T⁻¹)'(T z) · T'(z) = 1` for the Cayley map `T`. -/
theorem utm_cay_mul {z : ℂ} (hz : z + I ≠ 0) :
    2 * I / (1 - cayley z) ^ 2 * (2 * I / (z + I) ^ 2) = 1 := by
  have e : (1 : ℂ) - cayley z = 2 * I / (z + I) := by
    unfold cayley
    field_simp
    ring
  rw [e]
  field_simp

/-- The pulled-back differential on the disc: `φ(w) = ψ(T⁻¹ w) ((T⁻¹)'(w))²`. -/
def utm_pull (ψ : ℂ → ℂ) (w : ℂ) : ℂ := ψ (cayleyInv w) * (2 * I / (1 - w) ^ 2) ^ 2

/-- `utm_pull ψ` at a Cayley point: `utm_pull ψ (cayley z) = ψ z · (2i / (1 - cayley z)²)²` for `z ∈ ℍ`. -/
theorem utm_pull_cayley (ψ : ℂ → ℂ) {z : ℂ} (hz : 0 < z.im) :
    utm_pull ψ (cayley z) = ψ z * (2 * I / (1 - cayley z) ^ 2) ^ 2 := by
  rw [utm_pull, cayleyInv_cayley hz]

/-- Density transport: `|φ(T z)|^{1/2} |T'(z) v| = |ψ(z)|^{1/2} |v|`. -/
theorem utm_density (ψ : ℂ → ℂ) {z : ℂ} (hz : 0 < z.im) (v : ℂ) :
    phiDensity (utm_pull ψ) (cayley z) * ‖2 * I / (z + I) ^ 2 * v‖ₑ = phiDensity ψ z * ‖v‖ₑ := by
  rw [fx_p5_density_mul, fx_p5_density_mul, utm_pull_cayley ψ hz]
  congr 1
  have hden := cayley_den_ne_zero hz
  have hA := utm_cay_mul hden
  set A : ℂ := 2 * I / (1 - cayley z) ^ 2
  set B : ℂ := 2 * I / (z + I) ^ 2
  have hAB : ‖A‖ * ‖B‖ = 1 := by rw [← norm_mul, hA, norm_one]
  rw [norm_mul, norm_mul, norm_pow, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  calc Real.sqrt ‖ψ z‖ * ‖A‖ * (‖B‖ * ‖v‖) = Real.sqrt ‖ψ z‖ * (‖A‖ * ‖B‖) * ‖v‖ := by ring
    _ = Real.sqrt ‖ψ z‖ * ‖v‖ := by rw [hAB, mul_one]

/-- The Cayley image of an open curve in `ℍ` is locally Lipschitz. -/
theorem utm_cayley_locallyLipschitzOn (β : LRCurve) (hβ : β.trace ⊆ upperHalf) :
    LocallyLipschitzOn (Ioo 0 1) (cayley ∘ β.toFun) := by
  intro τ hτ
  obtain ⟨K, t, ht, hK⟩ := β.locallyLipschitzOn hτ
  have hβτ : 0 < (β.toFun τ).im := hβ ⟨τ, hτ, rfl⟩
  have hden := cayley_den_ne_zero hβτ
  have hcd : ContDiffAt ℂ 1 cayley (β.toFun τ) := by
    unfold cayley
    exact (contDiffAt_id.sub contDiffAt_const).div (contDiffAt_id.add contDiffAt_const) hden
  obtain ⟨K', u, hu, hK'⟩ := hcd.exists_lipschitzOnWith
  have hcont : ContinuousWithinAt β.toFun (Ioo 0 1) τ := β.locallyLipschitzOn.continuousOn τ hτ
  refine ⟨K' * K, t ∩ β.toFun ⁻¹' u, inter_mem ht (hcont.preimage_mem_nhdsWithin hu), ?_⟩
  exact hK'.comp (hK.mono inter_subset_left) ((mapsTo_preimage _ u).mono_left inter_subset_right)

/-- Where `c` takes values in `ℍ` near `t`, `deriv (T ∘ c) t = T'(c t) · deriv c t` (both sides `0` when `c`
is not differentiable at `t`). -/
theorem utm_deriv_comp {c : ℝ → ℂ} {t : ℝ} (hev : ∀ᶠ s in 𝓝 t, 0 < (c s).im) :
    deriv (cayley ∘ c) t = 2 * I / (c t + I) ^ 2 * deriv c t := by
  have hct : 0 < (c t).im := hev.self_of_nhds
  have hden := cayley_den_ne_zero hct
  by_cases hd : DifferentiableAt ℝ c t
  · exact ((utm_hasDerivAt_cayley hden).comp t hd.hasDerivAt).deriv
  · rw [deriv_zero_of_not_differentiableAt hd, mul_zero]
    refine deriv_zero_of_not_differentiableAt fun hd' => hd ?_
    -- `c = T⁻¹ ∘ (T ∘ c)` near `t`
    have hw : ‖(cayley ∘ c) t‖ < 1 := mem_ball_zero_iff.1 (cayley_mem_unitDisc hct)
    have hw1 : (1 : ℂ) - (cayley ∘ c) t ≠ 0 := cayleyInv_den_ne_zero hw
    have hinv : HasDerivAt (cayleyInv ∘ (cayley ∘ c))
        (2 * I / (1 - (cayley ∘ c) t) ^ 2 * deriv (cayley ∘ c) t) t :=
      (utm_hasDerivAt_cayleyInv hw1).comp t hd'.hasDerivAt
    have heq : cayleyInv ∘ (cayley ∘ c) =ᶠ[𝓝 t] c := by
      filter_upwards [hev] with s hs
      exact cayleyInv_cayley hs
    exact (hinv.congr_of_eventuallyEq heq.symm).differentiableAt

/-- **Horizontal arcs are shortest in `ℍ`.**  For `ψ` holomorphic on `ℍ`, `ψ ≢ 0`, a horizontal arc
`c|[a, b]` of `ψ` in `ℍ` is no longer than any locally Lipschitz curve `β` in `ℍ` joining its end points
(`fx_arc_shortest` through the Cayley map; `ψ` need not be integrable). -/
theorem utm_arc_shortest_upperHalf {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ upperHalf)
    (hne : ∃ z ∈ upperHalf, ψ z ≠ 0) {c : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hc : IsHorizontalArc ψ c a b) (hcc : ContinuousOn c (Icc a b)) (hcH : c '' Icc a b ⊆ upperHalf)
    (β : LRCurve) (hβ : β.trace ⊆ upperHalf) (hβa : Tendsto β.toFun (𝓝[>] 0) (𝓝 (c a)))
    (hβb : Tendsto β.toFun (𝓝[<] 1) (𝓝 (c b))) :
    ∫⁻ t in Ioo a b, phiDensity ψ (c t) * ‖deriv c t‖ₑ ≤ phiLength ψ β := by
  have hcI : ∀ t ∈ Icc a b, 0 < (c t).im := fun t ht => hcH ⟨t, ht, rfl⟩
  have hβI : ∀ τ ∈ Ioo (0 : ℝ) 1, 0 < (β.toFun τ).im := fun τ hτ => hβ ⟨τ, hτ, rfl⟩
  -- the pulled-back differential is holomorphic on `Δ` and `≢ 0`
  have hφ : DifferentiableOn ℂ (utm_pull ψ) unitDisc := by
    intro w hw
    have hw' : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    have h1 : (1 : ℂ) - w ≠ 0 := cayleyInv_den_ne_zero hw'
    have hS : DifferentiableAt ℂ cayleyInv w := (utm_hasDerivAt_cayleyInv h1).differentiableAt
    have hψS : DifferentiableAt ℂ ψ (cayleyInv w) :=
      (hψ _ (cayleyInv_mem_upperHalf hw')).differentiableAt
        (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds (cayleyInv_mem_upperHalf hw'))
    refine DifferentiableAt.differentiableWithinAt ?_
    have hsub : DifferentiableAt ℂ (fun w : ℂ => (1 - w) ^ 2) w :=
      ((differentiableAt_const _).sub differentiableAt_id).pow 2
    have hq : DifferentiableAt ℂ (fun w : ℂ => 2 * I / (1 - w) ^ 2) w :=
      (differentiableAt_const _).div hsub (pow_ne_zero 2 h1)
    exact (hψS.comp w hS).mul (hq.pow 2)
  have hφne : ∃ w ∈ unitDisc, utm_pull ψ w ≠ 0 := by
    obtain ⟨z₀, hz₀, hψ₀⟩ := hne
    refine ⟨cayley z₀, cayley_mem_unitDisc hz₀, ?_⟩
    rw [utm_pull_cayley ψ hz₀]
    have hA := utm_cay_mul (cayley_den_ne_zero hz₀)
    have hA0 : (2 * I / (1 - cayley z₀) ^ 2) ≠ 0 := left_ne_zero_of_mul_eq_one hA
    exact mul_ne_zero hψ₀ (pow_ne_zero 2 hA0)
  -- the transported arc
  have hc' : IsHorizontalArc (utm_pull ψ) (cayley ∘ c) a b := by
    intro t ht
    obtain ⟨hd, hd0, hψ0, him, hre⟩ := hc t ht
    have hct := hcI t (Ioo_subset_Icc_self ht)
    have hden := cayley_den_ne_zero hct
    have hD := (utm_hasDerivAt_cayley hden).comp t hd.hasDerivAt
    have hA := utm_cay_mul hden
    have hB0 : (2 * I / (c t + I) ^ 2) ≠ 0 := right_ne_zero_of_mul_eq_one hA
    have hA0 : (2 * I / (1 - cayley (c t)) ^ 2) ≠ 0 := left_ne_zero_of_mul_eq_one hA
    have hkey : utm_pull ψ ((cayley ∘ c) t) * deriv (cayley ∘ c) t ^ 2 = ψ (c t) * deriv c t ^ 2 := by
      rw [hD.deriv, Function.comp_apply, utm_pull_cayley ψ hct]
      calc ψ (c t) * (2 * I / (1 - cayley (c t)) ^ 2) ^ 2 * (2 * I / (c t + I) ^ 2 * deriv c t) ^ 2
          = ψ (c t) * (2 * I / (1 - cayley (c t)) ^ 2 * (2 * I / (c t + I) ^ 2)) ^ 2 * deriv c t ^ 2 := by
            ring
        _ = ψ (c t) * deriv c t ^ 2 := by rw [hA]; ring
    refine ⟨hD.differentiableAt, ?_, ?_, ?_, ?_⟩
    · rw [hD.deriv]
      exact mul_ne_zero hB0 hd0
    · rw [Function.comp_apply, utm_pull_cayley ψ hct]
      exact mul_ne_zero hψ0 (pow_ne_zero 2 hA0)
    · rw [hkey]; exact him
    · rw [hkey]; exact hre
  have hcc' : ContinuousOn (cayley ∘ c) (Icc a b) := by
    refine ContinuousOn.comp (t := upperHalf) ?_ hcc fun t ht => hcI t ht
    intro z hz
    exact ((utm_hasDerivAt_cayley (cayley_den_ne_zero hz)).continuousAt).continuousWithinAt
  have hcD' : (cayley ∘ c) '' Icc a b ⊆ unitDisc := by
    rintro _ ⟨t, ht, rfl⟩
    exact cayley_mem_unitDisc (hcI t ht)
  -- the transported curve
  set β' : LRCurve := ⟨cayley ∘ β.toFun, utm_cayley_locallyLipschitzOn β hβ⟩ with hβ'
  have hβD' : β'.trace ⊆ unitDisc := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact cayley_mem_unitDisc (hβI τ hτ)
  have hcontT : ∀ z : ℂ, 0 < z.im → ContinuousAt cayley z := fun z hz =>
    (utm_hasDerivAt_cayley (cayley_den_ne_zero hz)).continuousAt
  have hβa' : Tendsto β'.toFun (𝓝[>] 0) (𝓝 ((cayley ∘ c) a)) :=
    (hcontT _ (hcI a (left_mem_Icc.2 hab.le))).tendsto.comp hβa
  have hβb' : Tendsto β'.toFun (𝓝[<] 1) (𝓝 ((cayley ∘ c) b)) :=
    (hcontT _ (hcI b (right_mem_Icc.2 hab.le))).tendsto.comp hβb
  have key := fx_arc_shortest hφ hφne hab hc' hcc' hcD' β' hβD' hβa' hβb'
  -- transport both sides back
  have hL : ∫⁻ t in Ioo a b, phiDensity (utm_pull ψ) ((cayley ∘ c) t) * ‖deriv (cayley ∘ c) t‖ₑ =
      ∫⁻ t in Ioo a b, phiDensity ψ (c t) * ‖deriv c t‖ₑ := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have hev : ∀ᶠ s in 𝓝 t, 0 < (c s).im := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hcI s (Ioo_subset_Icc_self hs)
    rw [utm_deriv_comp hev, Function.comp_apply]
    exact utm_density ψ (hcI t (Ioo_subset_Icc_self ht)) _
  have hR : phiLength (utm_pull ψ) β' = phiLength ψ β := by
    simp only [phiLength, LRCurve.rhoLength]
    refine setLIntegral_congr_fun measurableSet_Ioo fun τ hτ => ?_
    have hev : ∀ᶠ s in 𝓝 τ, 0 < (β.toFun s).im := by
      filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with s hs
      exact hβI s hs
    show phiDensity (utm_pull ψ) ((cayley ∘ β.toFun) τ) * ‖deriv (cayley ∘ β.toFun) τ‖ₑ =
      phiDensity ψ (β.toFun τ) * ‖deriv β.toFun τ‖ₑ
    rw [utm_deriv_comp hev, Function.comp_apply]
    exact utm_density ψ (hβI τ hτ) _
  rw [← hL, ← hR]
  exact key

end ArcShortest

/-- The lift of a self-map homotopic to the identity, obtained by lifting the homotopy from `id`, commutes with the
covering group (Mathlib's `IsCoveringMap.liftHomotopy`; scout A's `h26a_commuting_lift`). -/
theorem utm_commuting_lift {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → S}
    (hp : IsUniformization Γ p) (f : S ≃ₜ S)
    (hhom : ContinuousMap.Homotopic (f : C(S, S)) (ContinuousMap.id S)) :
    ∃ F : C(UpperHalfPlane, UpperHalfPlane), (∀ τ, p (F τ) = f (p τ)) ∧
      ∀ γ ∈ Γ, ∀ τ, F (γ • τ) = γ • F τ := by
  obtain ⟨H⟩ := hhom.symm
  have cov : IsCoveringMap p := hp.1
  let H' : C(unitInterval × UpperHalfPlane, S) :=
    ⟨fun x => H (x.1, p x.2), H.continuous.comp (continuous_fst.prodMk (cov.continuous.comp continuous_snd))⟩
  have H0 : ∀ τ, H' (0, τ) = p (ContinuousMap.id UpperHalfPlane τ) := fun τ => by
    simp [H']
  set L := cov.liftHomotopy H' (ContinuousMap.id UpperHalfPlane) H0 with hL
  have hlifts : ∀ t τ, p (L (t, τ)) = H (t, p τ) := fun t τ =>
    congr_fun (cov.liftHomotopy_lifts H' (ContinuousMap.id UpperHalfPlane) H0) (t, τ)
  have hzero : ∀ τ, L (0, τ) = τ := fun τ => cov.liftHomotopy_zero H' (ContinuousMap.id UpperHalfPlane) H0 τ
  refine ⟨⟨fun τ => L (1, τ), L.continuous.comp (continuous_const.prodMk continuous_id)⟩, fun τ => ?_,
    fun γ hγ τ => ?_⟩
  · show p (L (1, τ)) = f (p τ)
    rw [hlifts]
    simp
  · show L (1, γ • τ) = γ • L (1, τ)
    have hpγ : ∀ w, p (γ • w) = p w := fun w => ((hp.2.2.2 w (γ • w)).2 ⟨γ, hγ, rfl⟩).symm
    have h := cov.eq_of_comp_eq (A := unitInterval) (g₁ := fun t => L (t, γ • τ))
      (g₂ := fun t => γ • L (t, τ)) (L.continuous.comp (continuous_id.prodMk continuous_const))
      ((continuous_const_smul γ).comp (L.continuous.comp (continuous_id.prodMk continuous_const)))
      (by
        funext t
        simp only [Function.comp_apply, hpγ, hlifts])
      0 (by simp only [hzero])
    exact congr_fun h 1

/-- The uniformization `p₀ : ℍ → S₀` as a map `ℂ → S₀` (junk value `p₀ I` off `ℍ`). -/
def utm_pext (p₀ : UpperHalfPlane → S₀) (z : ℂ) : S₀ :=
  if hz : 0 < z.im then p₀ ⟨z, hz⟩ else p₀ UpperHalfPlane.I

/-- **The lift `ψ` of `q` to `ℍ`**: `ψ(z) = q_x(φ_x(p₀ z)) · ((φ_x ∘ p₀)'(z))²` in the chart at `x = p₀ z`
(junk off `ℍ`).  By the transformation law of `q`, any chart whose source contains `p₀ z` gives the same value
near `z` ([P0] `utm_liftQD_local`). -/
def utm_liftQD (q : S₀ → ℂ → ℂ) (p₀ : UpperHalfPlane → S₀) (z : ℂ) : ℂ :=
  q (utm_pext p₀ z) (chartAt ℂ (utm_pext p₀ z) (utm_pext p₀ z)) *
    deriv (fun w => chartAt ℂ (utm_pext p₀ z) (utm_pext p₀ w)) z ^ 2

/-- On `ℍ`, `utm_pext p₀` is `p₀ ∘ ofComplex`. -/
theorem utm_a_pext_eq {X : Type*} (p₀ : UpperHalfPlane → X) {z : ℂ} (hz : 0 < z.im) :
    utm_pext p₀ z = p₀ (UpperHalfPlane.ofComplex z) := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  simp only [utm_pext, hz, ↓reduceDIte]

/-- `utm_pext p₀` is continuous at every point of `ℍ` (it is `p₀ ∘ ofComplex` near such a point). -/
theorem utm_a_continuousAt {X : Type*} [TopologicalSpace X] {p₀ : UpperHalfPlane → X} (hp : Continuous p₀)
    {z : ℂ} (hz : 0 < z.im) : ContinuousAt (utm_pext p₀) z := by
  have hev : (fun w => p₀ (UpperHalfPlane.ofComplex w)) =ᶠ[𝓝 z] utm_pext p₀ := by
    filter_upwards [isOpen_upperHalf.mem_nhds hz] with w hw
    exact (utm_a_pext_eq p₀ hw).symm
  exact (hp.continuousAt.comp (UpperHalfPlane.mdifferentiableAt_ofComplex hz).continuousAt).congr hev

/-- The chart expression `v ↦ φ_x(p̂ v)` is holomorphic at every point of `ℍ` that `p̂` maps into the source of
the chart at `x` (`MDifferentiable` of `p₀` and of the chart). -/
theorem utm_a_differentiableAt [IsManifold 𝓘(ℂ) ω S₀] {p₀ : UpperHalfPlane → S₀}
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p₀) (x : S₀) {w : ℂ} (hw : 0 < w.im)
    (hx : utm_pext p₀ w ∈ (chartAt ℂ x).source) :
    DifferentiableAt ℂ (fun v => chartAt ℂ x (utm_pext p₀ v)) w := by
  have hx' : p₀ (UpperHalfPlane.ofComplex w) ∈ (chartAt ℂ x).source := by
    rwa [← utm_a_pext_eq p₀ hw]
  have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun z => chartAt ℂ x (p₀ (UpperHalfPlane.ofComplex z))) w :=
    (mdifferentiableAt_atlas (chart_mem_atlas ℂ x) hx').comp w
      ((hhol _).comp w (UpperHalfPlane.mdifferentiableAt_ofComplex hw))
  refine (mdifferentiableAt_iff_differentiableAt.1 h1).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_upperHalf.mem_nhds hw] with v hv
  rw [utm_a_pext_eq p₀ hv]

/-- [P0, stub] **Local form of the lifted differential.**  Near `τ ∈ ℍ`, for any chart `x` whose source contains
`p₀ τ`, the map `h = φ_x ∘ p̂` is holomorphic and injective with `h' ≠ 0`, and `ψ = (q_x ∘ h) · h'²`.

*Truth:* `p₀` is a holomorphic covering, hence a local biholomorphism, so `h` is injective and holomorphic near
`τ` with `h' ≠ 0`; the identity is the transformation law of `q` (`IsDiffFamily 2 0`) between the charts at
`p₀ w` and `x`, with the chain rule `h' = T' · (φ_{p₀ w} ∘ p̂)'` for the holomorphic transition `T`. -/
theorem utm_liftQD_local [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (τ : UpperHalfPlane) (x : S₀) (hx : p₀ τ ∈ (chartAt ℂ x).source) :
    ∃ U : Set ℂ, IsOpen U ∧ (τ : ℂ) ∈ U ∧ U ⊆ upperHalf ∧
      InjOn (fun w => chartAt ℂ x (utm_pext p₀ w)) U ∧
      ∀ w ∈ U, utm_pext p₀ w ∈ (chartAt ℂ x).source ∧
        HasDerivAt (fun v => chartAt ℂ x (utm_pext p₀ v))
          (deriv (fun v => chartAt ℂ x (utm_pext p₀ v)) w) w ∧
        deriv (fun v => chartAt ℂ x (utm_pext p₀ v)) w ≠ 0 ∧
        utm_liftQD q p₀ w =
          q x (chartAt ℂ x (utm_pext p₀ w)) * deriv (fun v => chartAt ℂ x (utm_pext p₀ v)) w ^ 2 := by
  obtain ⟨hcov, hhol, -, -⟩ := hp₀
  obtain ⟨e, hτe, hpe⟩ := hcov.isLocalHomeomorph τ
  set W : Set UpperHalfPlane := e.source ∩ p₀ ⁻¹' (chartAt ℂ x).source with hWdef
  have hWo : IsOpen W := e.open_source.inter (hcov.continuous.isOpen_preimage _ (chartAt ℂ x).open_source)
  set U : Set ℂ := upperHalf ∩ UpperHalfPlane.ofComplex ⁻¹' W with hUdef
  have hsrc : UpperHalfPlane.ofComplex.source = upperHalf := by
    ext z
    simp [UpperHalfPlane.ofComplex, upperHalf]
  have hUo : IsOpen U := by
    have h := UpperHalfPlane.ofComplex.isOpen_inter_preimage hWo
    rwa [hsrc] at h
  have hτU : (τ : ℂ) ∈ U := by
    refine ⟨τ.coe_im_pos, ?_⟩
    show UpperHalfPlane.ofComplex (τ : ℂ) ∈ W
    rw [UpperHalfPlane.ofComplex_apply]
    exact ⟨hτe, hx⟩
  have hUs : ∀ w ∈ U, utm_pext p₀ w ∈ (chartAt ℂ x).source := fun w hw => by
    rw [utm_a_pext_eq p₀ hw.1]
    exact hw.2.2
  have hd : ∀ w ∈ U, DifferentiableAt ℂ (fun v => chartAt ℂ x (utm_pext p₀ v)) w := fun w hw =>
    utm_a_differentiableAt hhol x hw.1 (hUs w hw)
  have hinj : InjOn (fun w => chartAt ℂ x (utm_pext p₀ w)) U := by
    intro z hz w hw hzw
    have h1 : utm_pext p₀ z = utm_pext p₀ w := (chartAt ℂ x).injOn (hUs z hz) (hUs w hw) hzw
    rw [utm_a_pext_eq p₀ hz.1, utm_a_pext_eq p₀ hw.1, hpe] at h1
    have h2 := e.injOn hz.2.1 hw.2.1 h1
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz.1, UpperHalfPlane.ofComplex_apply_of_im_pos hw.1] at h2
    exact congrArg UpperHalfPlane.coe h2
  refine ⟨U, hUo, hτU, inter_subset_left, hinj, fun w hw => ⟨hUs w hw, (hd w hw).hasDerivAt,
    deriv_ne_zero_of_injOn hUo (fun v hv => (hd v hv).differentiableWithinAt) hinj hw, ?_⟩⟩
  -- the transformation law between the chart at `y = p̂ w` and the chart at `x`
  set y := utm_pext p₀ w with hy
  have hyx : y ∈ (chartAt ℂ x).source := hUs w hw
  have hyt : chartAt ℂ y y ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source (mem_chart_source ℂ y)
  have hys : (chartAt ℂ y).symm (chartAt ℂ y y) = y := (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hlaw := s26u_law hq y x hyt (by rw [hys]; exact hyx)
  have hT : chartTransition x y (chartAt ℂ y y) = chartAt ℂ x y := by
    show chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y y)) = chartAt ℂ x y
    rw [hys]
  rw [hT] at hlaw
  have hTd : DifferentiableAt ℂ (chartTransition x y) (chartAt ℂ y y) :=
    s23_transition_differentiableAt x y hyt (by rw [hys]; exact hyx)
  have hgd : DifferentiableAt ℂ (fun v => chartAt ℂ y (utm_pext p₀ v)) w :=
    utm_a_differentiableAt hhol y hw.1 (mem_chart_source ℂ y)
  have hev : (fun v => chartAt ℂ x (utm_pext p₀ v)) =ᶠ[𝓝 w]
      chartTransition x y ∘ fun v => chartAt ℂ y (utm_pext p₀ v) := by
    filter_upwards [(utm_a_continuousAt hcov.continuous hw.1).preimage_mem_nhds
      ((chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y))] with v hv
    show chartAt ℂ x (utm_pext p₀ v) = chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y (utm_pext p₀ v)))
    rw [(chartAt ℂ y).left_inv hv]
  have hder : deriv (fun v => chartAt ℂ x (utm_pext p₀ v)) w =
      deriv (chartTransition x y) (chartAt ℂ y y) * deriv (fun v => chartAt ℂ y (utm_pext p₀ v)) w := by
    rw [hev.deriv_eq]
    exact (hTd.hasDerivAt.comp w hgd.hasDerivAt).deriv
  rw [hder]
  show q y (chartAt ℂ y y) * deriv (fun v => chartAt ℂ y (utm_pext p₀ v)) w ^ 2 = _
  rw [hlaw]
  ring

/-- [P1, proved from P0] The lifted differential is holomorphic on `ℍ`. -/
theorem utm_liftQD_differentiableOn [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) : DifferentiableOn ℂ (utm_liftQD q p₀) upperHalf := by
  intro z hz
  set τ : UpperHalfPlane := ⟨z, hz⟩ with hτ
  obtain ⟨U, hUo, hτU, -, -, hU⟩ := utm_liftQD_local hq hp₀ τ (p₀ τ) (mem_chart_source ℂ (p₀ τ))
  set x := p₀ τ with hx
  set h : ℂ → ℂ := fun v => chartAt ℂ x (utm_pext p₀ v) with hh
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  have hhd : DifferentiableOn ℂ h U := fun w hw => (hU w hw).2.1.differentiableAt.differentiableWithinAt
  have hdd : DifferentiableOn ℂ (deriv h) U := hhd.deriv hUo
  have hloc : DifferentiableOn ℂ (fun w => q x (h w) * deriv h w ^ 2) U := by
    intro w hw
    have hmem : h w ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source (hU w hw).1
    have h1 : DifferentiableAt ℂ (q x) (h w) :=
      (hq'.2 x).differentiableAt ((chartAt ℂ x).open_target.mem_nhds hmem)
    exact ((h1.comp w (hU w hw).2.1.differentiableAt).mul
      ((hdd.differentiableAt (hUo.mem_nhds hw)).pow 2)).differentiableWithinAt
  have heq : utm_liftQD q p₀ =ᶠ[𝓝 z] fun w => q x (h w) * deriv h w ^ 2 :=
    Filter.eventuallyEq_of_mem (hUo.mem_nhds hτU) fun w hw => (hU w hw).2.2.2
  exact ((hloc.differentiableAt (hUo.mem_nhds hτU)).congr_of_eventuallyEq heq).differentiableWithinAt

/-- [P2, proved from P0] The lifted differential of `q ≠ 0` is not identically zero on `ℍ` (lift a regular
point). -/
theorem utm_liftQD_ne [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) : ∃ z ∈ upperHalf, utm_liftQD q p₀ z ≠ 0 := by
  obtain ⟨p⟩ : Nonempty S₀ := ConnectedSpace.toNonempty
  obtain ⟨p', hp'⟩ := (s26u_frequently_regular hq hne p).exists
  obtain ⟨τ, hτ⟩ := hp₀.2.2.1 p'
  have hsrc : p₀ τ ∈ (chartAt ℂ p').source := by
    rw [hτ]
    exact mem_chart_source ℂ p'
  obtain ⟨U, -, hτU, -, -, hU⟩ := utm_liftQD_local hq hp₀ τ p' hsrc
  refine ⟨τ, τ.coe_im_pos, ?_⟩
  obtain ⟨-, -, hd0, heq⟩ := hU τ hτU
  rw [heq]
  have hpt : utm_pext p₀ (τ : ℂ) = p' := by
    simp only [utm_pext, τ.coe_im_pos, ↓reduceDIte]
    exact hτ
  refine mul_ne_zero ?_ (pow_ne_zero 2 hd0)
  rw [hpt]
  exact hp'

/-- The lift `γ'` of a path `γ`, read on `ℝ`, is mapped by `p̂` back onto `γ`: `p̂ (γ' t) = γ t` for every `t`. -/
theorem utm_a_pext_lift {X : Type*} [TopologicalSpace X] {p₀ : UpperHalfPlane → X} {a b : X} (γ : Path a b)
    (γ' : C(unitInterval, UpperHalfPlane)) (hγ' : ∀ t, p₀ (γ' t) = γ t) (t : ℝ) :
    utm_pext p₀ (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ) = γ.extend t := by
  have h := (γ' (Set.projIcc 0 1 zero_le_one t)).coe_im_pos
  simp only [utm_pext, h, ↓reduceDIte]
  exact hγ' _

/-- A lift `γ'`, read on `ℝ`, is continuous. -/
theorem utm_a_lift_continuous (γ' : C(unitInterval, UpperHalfPlane)) :
    Continuous fun t : ℝ => (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ) :=
  UpperHalfPlane.continuous_coe.comp (γ'.continuous.comp continuous_projIcc)

/-- **Local inverse.**  A holomorphic map with `h' ≠ 0` at `z₀` has a left inverse near `z₀` which is strictly
differentiable at `h z₀`. -/
theorem utm_a_local_inverse {h : ℂ → ℂ} {z₀ : ℂ} {U : Set ℂ} (hU : IsOpen U) (hz₀ : z₀ ∈ U)
    (hh : DifferentiableOn ℂ h U) (hh' : deriv h z₀ ≠ 0) :
    ∃ L : ℂ → ℂ, HasStrictDerivAt L (deriv h z₀)⁻¹ (h z₀) ∧ ∀ᶠ z in 𝓝 z₀, L (h z) = z := by
  have hs : HasStrictDerivAt h (deriv h z₀) z₀ := (hh.analyticAt (hU.mem_nhds hz₀)).hasStrictDerivAt
  exact ⟨_, hs.to_localInverse hh', hs.eventually_left_inverse hh'⟩

/-- If `h` is a local biholomorphism at `c t` and `h ∘ c` is differentiable at `t`, so is `c`. -/
theorem utm_a_hasDerivAt_of_comp {h : ℂ → ℂ} {c : ℝ → ℂ} {t : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hcU : c t ∈ U) (hh : DifferentiableOn ℂ h U) (hh' : deriv h (c t) ≠ 0) (hc : ContinuousAt c t)
    {A' : ℂ} (hA : HasDerivAt (h ∘ c) A' t) : HasDerivAt c ((deriv h (c t))⁻¹ * A') t := by
  obtain ⟨L, hL, hleft⟩ := utm_a_local_inverse hU hcU hh hh'
  have hev : c =ᶠ[𝓝 t] L ∘ (h ∘ c) := by
    filter_upwards [Filter.Tendsto.eventually hc hleft] with s hs
    exact hs.symm
  exact (hL.hasDerivAt.comp t hA).congr_of_eventuallyEq hev

/-- **The lift in a chart.**  Let `γ'` lift the path `γ` and let `γ(u)` lie in the chart at `x`.  With
`h = φ_x ∘ p̂` and `d = h'(γ' u) ≠ 0`: `ψ(γ' u) = q_x(φ_x γ(u)) d²`, the chart expression `φ_x ∘ γ = h ∘ γ'` is
differentiable at `u` iff `γ'` is, and `(φ_x ∘ γ)'(u) = d · γ''(u)` (both sides `0` when not differentiable). -/
theorem utm_a_lift_local [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {a b : S₀} (γ : Path a b)
    (γ' : C(unitInterval, UpperHalfPlane)) (hγ' : ∀ t, p₀ (γ' t) = γ t) (x : S₀) {u : ℝ}
    (hu : γ.extend u ∈ (chartAt ℂ x).source) :
    ∃ d : ℂ, d ≠ 0 ∧
      utm_liftQD q p₀ (γ' (Set.projIcc 0 1 zero_le_one u) : ℂ) = q x (chartAt ℂ x (γ.extend u)) * d ^ 2 ∧
      (DifferentiableAt ℝ (fun v => chartAt ℂ x (γ.extend v)) u ↔
        DifferentiableAt ℝ (fun v => (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ)) u) ∧
      deriv (fun v => chartAt ℂ x (γ.extend v)) u =
        d * deriv (fun v => (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ)) u := by
  have hA : (fun v => chartAt ℂ x (γ.extend v)) =
      (fun v => chartAt ℂ x (utm_pext p₀ v)) ∘ fun v => (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ) := by
    funext v
    simp only [Function.comp_apply, utm_a_pext_lift γ γ' hγ' v]
  have hτ : p₀ (γ' (Set.projIcc 0 1 zero_le_one u)) ∈ (chartAt ℂ x).source := by
    rw [hγ']
    exact hu
  obtain ⟨U, hUo, hcU, -, -, hU⟩ := utm_liftQD_local hq hp₀ (γ' (Set.projIcc 0 1 zero_le_one u)) x hτ
  obtain ⟨-, hhd, hd0, hψ⟩ := hU _ hcU
  have hdiffU : DifferentiableOn ℂ (fun v => chartAt ℂ x (utm_pext p₀ v)) U := fun w hw =>
    (hU w hw).2.1.differentiableAt.differentiableWithinAt
  have hcc := utm_a_lift_continuous γ'
  have hback : DifferentiableAt ℝ ((fun v => chartAt ℂ x (utm_pext p₀ v)) ∘
      fun v => (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ)) u →
      DifferentiableAt ℝ (fun v => (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ)) u := fun hAd =>
    (utm_a_hasDerivAt_of_comp hUo hcU hdiffU hd0 hcc.continuousAt hAd.hasDerivAt).differentiableAt
  refine ⟨_, hd0, ?_, ⟨fun hAd => hback (hA ▸ hAd), fun hcd => ?_⟩, ?_⟩
  · rw [hψ, utm_a_pext_lift γ γ' hγ' u]
  · rw [hA]
    exact (hhd.comp u hcd.hasDerivAt).differentiableAt
  · by_cases hcd : DifferentiableAt ℝ (fun v => (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ)) u
    · rw [hA]
      exact (hhd.comp u hcd.hasDerivAt).deriv
    · rw [hA, deriv_zero_of_not_differentiableAt hcd, mul_zero]
      exact deriv_zero_of_not_differentiableAt fun hAd => hcd (hback hAd)

/-- [P3, stub] **Horizontal arcs lift to horizontal arcs.**  A lift `α'` to `ℍ` of a horizontal trajectory arc `α`
of `q` (`p₀ ∘ α' = α`) is, read on `[0, 1]` in `ℂ`, a horizontal arc of the lifted differential.

*Truth:* at `t ∈ (0, 1)`, in the chart `x` of `IsHorizontalArcRS` and the local form [P0] at `α' t`,
`φ_x ∘ α = h ∘ α'` with `h` locally biholomorphic, so `α' = h⁻¹ ∘ (φ_x ∘ α)` is differentiable with
`α'' ≠ 0`, and `ψ(α') α''² = q_x(φ_x α) ((φ_x ∘ α)')²` is real and positive. -/
theorem utm_horizontal_lift [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {a b : S₀} (α : Path a b) (hα : IsHorizontalArcRS q α)
    (α' : C(unitInterval, UpperHalfPlane)) (hα' : ∀ t, p₀ (α' t) = α t) :
    IsHorizontalArc (utm_liftQD q p₀) (fun t : ℝ => (α' (Set.projIcc 0 1 zero_le_one t) : ℂ)) 0 1 := by
  intro t ht
  obtain ⟨δ, hδ, x, hsub, hh⟩ := hα t (Ioo_subset_Icc_self ht)
  have ht' : t ∈ Ioo (max 0 (t - δ)) (min 1 (t + δ)) :=
    ⟨max_lt ht.1 (by linarith), lt_min ht.2 (by linarith)⟩
  obtain ⟨hAd, hA0, hq0, him, hre⟩ := hh t ht'
  have hsrc : α.extend t ∈ (chartAt ℂ x).source := hsub ⟨t, ⟨by linarith, by linarith⟩, rfl⟩
  obtain ⟨d, hd0, hψ, hiff, hder⟩ := utm_a_lift_local hq hp₀ α α' hα' x hsrc
  have key : utm_liftQD q p₀ (α' (Set.projIcc 0 1 zero_le_one t) : ℂ) *
      deriv (fun v => (α' (Set.projIcc 0 1 zero_le_one v) : ℂ)) t ^ 2 =
      q x (chartAt ℂ x (α.extend t)) * deriv (fun v => chartAt ℂ x (α.extend v)) t ^ 2 := by
    rw [hψ, hder]
    ring
  refine ⟨hiff.1 hAd, fun h0 => hA0 ?_, ?_, ?_, ?_⟩
  · rw [hder, h0, mul_zero]
  · rw [hψ]
    exact mul_ne_zero hq0 (pow_ne_zero 2 hd0)
  · rw [key]
    exact him
  · rw [key]
    exact hre

/-- On a piece `[s₁, s₂]` of an admissible partition (in the chart at `x`, where `φ_x ∘ γ` is Lipschitz), the lift
`γ'` is locally Lipschitz: near each point it is `L ∘ (φ_x ∘ γ)` for a local inverse `L` of `φ_x ∘ p̂`, which is
Lipschitz near the image point (strict differentiability). -/
theorem utm_a_lift_locallyLipschitzOn [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {a b : S₀} (γ : Path a b)
    (γ' : C(unitInterval, UpperHalfPlane)) (hγ' : ∀ t, p₀ (γ' t) = γ t) (x : S₀) {s₁ s₂ : ℝ}
    (hsrc : γ.extend '' Icc s₁ s₂ ⊆ (chartAt ℂ x).source) {K : ℝ≥0}
    (hK : LipschitzOnWith K (fun v : ℝ => chartAt ℂ x (γ.extend v)) (Icc s₁ s₂)) :
    LocallyLipschitzOn (Icc s₁ s₂) (fun v : ℝ => (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ)) := by
  intro s hs
  have hτ : p₀ (γ' (Set.projIcc 0 1 zero_le_one s)) ∈ (chartAt ℂ x).source := by
    rw [hγ']
    exact hsrc ⟨s, hs, rfl⟩
  obtain ⟨U, hUo, hcU, -, -, hU⟩ := utm_liftQD_local hq hp₀ _ x hτ
  obtain ⟨-, -, hd0, -⟩ := hU _ hcU
  have hdiffU : DifferentiableOn ℂ (fun v => chartAt ℂ x (utm_pext p₀ v)) U := fun w hw =>
    (hU w hw).2.1.differentiableAt.differentiableWithinAt
  obtain ⟨L, hL, hleft⟩ := utm_a_local_inverse hUo hcU hdiffU hd0
  obtain ⟨KL, N, hN, hLN⟩ := hL.hasStrictFDerivAt.exists_lipschitzOnWith
  have hAc : ∀ v : ℝ, chartAt ℂ x (γ.extend v) =
      chartAt ℂ x (utm_pext p₀ (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ)) := fun v => by
    rw [utm_a_pext_lift γ γ' hγ' v]
  have hN' : N ∈ 𝓝 (chartAt ℂ x (γ.extend s)) := by
    rw [hAc s]
    exact hN
  set T : Set ℝ := {v | v ∈ Icc s₁ s₂ ∧ L (chartAt ℂ x (γ.extend v)) = (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ) ∧
    chartAt ℂ x (γ.extend v) ∈ N} with hT
  refine ⟨KL * K, T, ?_, ?_⟩
  · have h2 : ∀ᶠ v in 𝓝 s, L (chartAt ℂ x (γ.extend v)) = (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ) := by
      filter_upwards [Filter.Tendsto.eventually (utm_a_lift_continuous γ').continuousAt hleft] with v hv
      rw [hAc v]
      exact hv
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h2,
      Filter.Tendsto.eventually_mem (hK.continuousOn s hs) hN'] with v h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · have hcomp := hLN.comp (hK.mono fun v (hv : v ∈ T) => hv.1) fun v (hv : v ∈ T) => hv.2.2
    intro v hv w hw
    show edist (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ) (γ' (Set.projIcc 0 1 zero_le_one w) : ℂ) ≤ _
    rw [← hv.2.1, ← hw.2.1]
    exact hcomp hv hw

/-- A map `ℝ → ℂ` which is `K`-Lipschitz on `[a, b]` and on `[b, d]` is `K`-Lipschitz on `[a, d]`. -/
theorem utm_a_lipschitzOnWith_Icc_union {f : ℝ → ℂ} {K : ℝ≥0} {a b d : ℝ}
    (h₁ : LipschitzOnWith K f (Icc a b)) (h₂ : LipschitzOnWith K f (Icc b d)) :
    LipschitzOnWith K f (Icc a d) := by
  rw [lipschitzOnWith_iff_dist_le_mul] at h₁ h₂ ⊢
  have key : ∀ s ∈ Icc a d, ∀ t ∈ Icc a d, s ≤ t → dist (f s) (f t) ≤ K * dist s t := by
    intro s hs t ht hst
    rcases le_total t b with htb | hbt
    · exact h₁ s ⟨hs.1, hst.trans htb⟩ t ⟨hs.1.trans hst, htb⟩
    · rcases le_total b s with hbs | hsb
      · exact h₂ s ⟨hbs, hst.trans ht.2⟩ t ⟨hbs.trans hst, ht.2⟩
      · have hb1 : b ∈ Icc a b := ⟨hs.1.trans hsb, le_rfl⟩
        have hb2 : b ∈ Icc b d := ⟨le_rfl, hbt.trans ht.2⟩
        have e : dist s t = dist s b + dist b t := by
          simp only [Real.dist_eq]
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          ring
        calc dist (f s) (f t) ≤ dist (f s) (f b) + dist (f b) (f t) := dist_triangle _ _ _
          _ ≤ K * dist s b + K * dist b t :=
              add_le_add (h₁ s ⟨hs.1, hsb⟩ b hb1) (h₂ b hb2 t ⟨hbt, ht.2⟩)
          _ = K * dist s t := by rw [e, mul_add]
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact key s hs t ht hst
  · rw [dist_comm (f s), dist_comm s]
    exact key t ht s hs hts

/-- For a monotone subdivision `τ`, the integral over `(τ 0, τ n)` is the sum of the integrals over the pieces
`(τ i, τ (i + 1))` (they are disjoint; the reverse inequality is `s26n_lintegral_le_sum`). -/
theorem utm_a_lintegral_sum_eq (G : ℝ → ℝ≥0∞) (n : ℕ) (τ : Fin (n + 1) → ℝ) (hτ : Monotone τ) :
    ∑ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ), G u = ∫⁻ u in Ioo (τ 0) (τ (Fin.last n)), G u := by
  refine le_antisymm ?_ (s26n_lintegral_le_sum G n τ hτ)
  have hdisj : Pairwise fun i j : Fin n =>
      Disjoint (Ioo (τ i.castSucc) (τ i.succ)) (Ioo (τ j.castSucc) (τ j.succ)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · have hle : τ i.succ ≤ τ j.castSucc := hτ (Fin.succ_le_castSucc_iff.2 h)
      exact Set.disjoint_left.2 fun u hu hu' => lt_irrefl _ ((hu.2.trans_le hle).trans hu'.1)
    · have hle : τ j.succ ≤ τ i.castSucc := hτ (Fin.succ_le_castSucc_iff.2 h)
      exact Set.disjoint_left.2 fun u hu hu' => lt_irrefl _ ((hu'.2.trans_le hle).trans hu.1)
  calc ∑ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ), G u
      = ∫⁻ u in ⋃ i : Fin n, Ioo (τ i.castSucc) (τ i.succ), G u := by
        rw [lintegral_iUnion (fun i => measurableSet_Ioo) hdisj, tsum_fintype]
    _ ≤ ∫⁻ u in Ioo (τ 0) (τ (Fin.last n)), G u :=
        lintegral_mono_set (iUnion_subset fun i => Ioo_subset_Ioo (hτ (Fin.zero_le _)) (hτ (Fin.le_last _)))

/-- The `q`-density times the speed of `φ_x ∘ γ` equals the `ψ`-density times the speed of the lift `γ'` at every
time `u` with `γ u` in the chart at `x` (`utm_a_lift_local`). -/
theorem utm_a_density_speed [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {a b : S₀} (γ : Path a b)
    (γ' : C(unitInterval, UpperHalfPlane)) (hγ' : ∀ t, p₀ (γ' t) = γ t) (x : S₀) {u : ℝ}
    (hu : γ.extend u ∈ (chartAt ℂ x).source) :
    phiDensity (q x) (chartAt ℂ x (γ.extend u)) * ‖deriv (fun v : ℝ => chartAt ℂ x (γ.extend v)) u‖ₑ =
      phiDensity (utm_liftQD q p₀) (γ' (Set.projIcc 0 1 zero_le_one u) : ℂ) *
        ‖deriv (fun s : ℝ => (γ' (Set.projIcc 0 1 zero_le_one s) : ℂ)) u‖ₑ := by
  obtain ⟨d, -, hψ, -, hder⟩ := utm_a_lift_local hq hp₀ γ γ' hγ' x hu
  rw [fx_p5_density_mul, fx_p5_density_mul, hψ, hder]
  congr 1
  rw [norm_mul, norm_mul, norm_pow, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  ring

/-- [P4, stub] **Length transfer to the lift.**  If a path `γ` on `S₀` has finite `q`-length (some admissible
partition with Lipschitz chart pieces exists), its lift `γ'` to `ℍ` is Lipschitz on `[0, 1]` and its `ψ`-length is
`phiLengthPath q γ`.

*Truth:* on each piece of an admissible partition, `φ_x ∘ γ = h ∘ γ'` with `h` a local biholomorphism ([P0] at
every point of the piece, compactness), so `γ'` is Lipschitz there and
`|q_x(φ_x γ)|^{1/2} |(φ_x ∘ γ)'| = |ψ(γ')|^{1/2} |γ''|` a.e. (both derivatives exist or not together).  Every
admissible partition therefore gives the same sum, the `ψ`-length of `γ'`; the infimum is over a nonempty set. -/
theorem utm_length_lift [IsManifold 𝓘(ℂ) ω S₀] {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {a b : S₀} (γ : Path a b)
    (γ' : C(unitInterval, UpperHalfPlane)) (hγ' : ∀ t, p₀ (γ' t) = γ t) (hfin : phiLengthPath q γ < ⊤) :
    (∃ K : ℝ≥0, LipschitzOnWith K (fun t : ℝ => (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ)) (Icc 0 1)) ∧
      ∫⁻ t in Ioo (0 : ℝ) 1, phiDensity (utm_liftQD q p₀) (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ) *
        ‖deriv (fun s : ℝ => (γ' (Set.projIcc 0 1 zero_le_one s) : ℂ)) t‖ₑ = phiLengthPath q γ := by
  -- every admissible partition gives the `ψ`-length of the lift
  have hsum : ∀ (n : ℕ) (τ : Fin (n + 1) → ℝ) (x : Fin n → S₀), τ 0 = 0 → τ (Fin.last n) = 1 → Monotone τ →
      (∀ i : Fin n, γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source) →
      ∑ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ),
        phiDensity (q (x i)) (chartAt ℂ (x i) (γ.extend u)) *
          ‖deriv (fun v : ℝ => chartAt ℂ (x i) (γ.extend v)) u‖ₑ =
      ∫⁻ t in Ioo (0 : ℝ) 1, phiDensity (utm_liftQD q p₀) (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ) *
        ‖deriv (fun s : ℝ => (γ' (Set.projIcc 0 1 zero_le_one s) : ℂ)) t‖ₑ := by
    intro n τ x h0 h1 hmono hsrc
    have hE := utm_a_lintegral_sum_eq (fun t => phiDensity (utm_liftQD q p₀)
      (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ) *
        ‖deriv (fun s : ℝ => (γ' (Set.projIcc 0 1 zero_le_one s) : ℂ)) t‖ₑ) n τ hmono
    rw [h0, h1] at hE
    refine Eq.trans ?_ hE
    refine Finset.sum_congr rfl fun i _ => setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    exact utm_a_density_speed hq hp₀ γ γ' hγ' (x i) (hsrc i ⟨u, Ioo_subset_Icc_self hu, rfl⟩)
  -- an admissible partition exists
  obtain ⟨n, τ, x, h0, h1, hmono, hpc⟩ : ∃ (n : ℕ) (τ : Fin (n + 1) → ℝ) (x : Fin n → S₀),
      τ 0 = 0 ∧ τ (Fin.last n) = 1 ∧ Monotone τ ∧
      ∀ i : Fin n, γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source ∧
        ∃ K : ℝ≥0, LipschitzOnWith K (fun v : ℝ => chartAt ℂ (x i) (γ.extend v))
          (Icc (τ i.castSucc) (τ i.succ)) := by
    by_contra hne
    apply (lt_top_iff_ne_top.1 hfin)
    unfold phiLengthPath phiLengthOn
    simp only [iInf_eq_top]
    intro n τ x hP
    exact absurd ⟨n, τ, x, hP⟩ hne
  refine ⟨?_, ?_⟩
  · have hloc : ∀ i : Fin n, ∃ K : ℝ≥0, LipschitzOnWith K
        (fun t : ℝ => (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ)) (Icc (τ i.castSucc) (τ i.succ)) := fun i => by
      obtain ⟨hs, K, hK⟩ := hpc i
      exact (utm_a_lift_locallyLipschitzOn hq hp₀ γ γ' hγ' (x i) hs hK).exists_lipschitzOnWith_of_compact
        isCompact_Icc
    choose K hK using hloc
    have hpiece : ∀ i : Fin n, LipschitzOnWith (Finset.univ.sup K)
        (fun t : ℝ => (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ)) (Icc (τ i.castSucc) (τ i.succ)) := fun i =>
      (hK i).weaken (Finset.le_sup (Finset.mem_univ i))
    have hall : ∀ j : Fin (n + 1), LipschitzOnWith (Finset.univ.sup K)
        (fun t : ℝ => (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ)) (Icc (τ 0) (τ j)) := by
      intro j
      induction j using Fin.induction with
      | zero =>
        intro s hs t ht
        have hst : s = t := le_antisymm (hs.2.trans ht.1) (ht.2.trans hs.1)
        rw [hst, edist_self]
        exact zero_le
      | succ i ih => exact utm_a_lipschitzOnWith_Icc_union ih (hpiece i)
    refine ⟨Finset.univ.sup K, ?_⟩
    have h := hall (Fin.last n)
    rwa [h0, h1] at h
  · unfold phiLengthPath phiLengthOn
    refine le_antisymm (le_iInf fun n' => le_iInf fun τ' => le_iInf fun x' => le_iInf fun hP => ?_) ?_
    · exact (hsum n' τ' x' hP.1 hP.2.1 hP.2.2.1 fun i => (hP.2.2.2 i).1).ge
    · exact iInf_le_of_le n (iInf_le_of_le τ (iInf_le_of_le x (iInf_le_of_le ⟨h0, h1, hmono, hpc⟩
        (hsum n τ x h0 h1 hmono fun i => (hpc i).1).le)))

/-- The Möbius map `z ↦ (a z + b) / (c z + d)` of `g ∈ SL(2, ℝ)` on `ℂ`. -/
def utm_b_mob (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) : ℂ :=
  ((g 0 0 : ℂ) * z + g 0 1) / ((g 1 0 : ℂ) * z + g 1 1)

/-- On `ℍ`, `utm_b_mob g` is the action of `g`. -/
theorem utm_b_mob_coe (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    utm_b_mob g τ = ((g • τ : UpperHalfPlane) : ℂ) :=
  (h36t_coe_smul g τ).symm

/-- On `ℍ`, `utm_b_mob g` is the action of `g` (a point given by its coordinate). -/
theorem utm_b_mob_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : 0 < z.im) :
    utm_b_mob g z = ((g • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) :=
  (h36t_coe_smul g ⟨z, hz⟩).symm

/-- `utm_b_mob g` maps `ℍ` into `ℍ`. -/
theorem utm_b_mob_im_pos (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : 0 < z.im) :
    0 < (utm_b_mob g z).im := by
  rw [utm_b_mob_smul g hz]
  exact UpperHalfPlane.coe_im_pos _

/-- The derivative of a unimodular Möbius map: `((a z + b) / (c z + d))' = 1 / (c z + d)²`. -/
theorem utm_b_hasDerivAt_mob (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ}
    (hz : (g 1 0 : ℂ) * z + g 1 1 ≠ 0) :
    HasDerivAt (utm_b_mob g) (1 / ((g 1 0 : ℂ) * z + g 1 1) ^ 2) z := by
  have hdet : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have h := (((hasDerivAt_id' z).const_mul (g 0 0 : ℂ)).add_const (g 0 1 : ℂ)).div
    (((hasDerivAt_id' z).const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ)) hz
  refine h.congr_deriv ?_
  congr 1
  linear_combination hdet

/-- The uniformization is `Γ₀`-invariant on `ℍ` in the coordinate `z`: `p̂(g z) = p̂(z)` for `g ∈ Γ₀`. -/
theorem utm_b_pext_mob {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ₀) {z : ℂ}
    (hz : 0 < z.im) : utm_pext p₀ (utm_b_mob γ z) = utm_pext p₀ z := by
  have hz' := utm_b_mob_im_pos γ hz
  simp only [utm_pext, hz, hz', ↓reduceDIte]
  have e : (⟨utm_b_mob γ z, hz'⟩ : UpperHalfPlane) = γ • (⟨z, hz⟩ : UpperHalfPlane) :=
    UpperHalfPlane.ext (utm_b_mob_smul γ hz)
  rw [e]
  exact ((hp₀.2.2.2 ⟨z, hz⟩ (γ • ⟨z, hz⟩)).2 ⟨γ, hγ, rfl⟩).symm

/-- **The lifted differential is `Γ₀`-automorphic**: `ψ(γ z) γ'(z)² = ψ(z)` for `γ ∈ Γ₀`, `z ∈ ℍ`, where
`γ'(z) = 1 / (c z + d)²` (the charts at `p̂(γ z) = p̂(z)` coincide, and `h ∘ γ = h` near `z` for
`h = φ_x ∘ p̂`; where `h` is not differentiable, both sides vanish). -/
theorem utm_b_liftQD_automorphic (q : S₀ → ℂ → ℂ) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ Γ₀) {z : ℂ} (hz : 0 < z.im) :
    utm_liftQD q p₀ (utm_b_mob γ z) * (1 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) ^ 2 = utm_liftQD q p₀ z := by
  have hpz := utm_b_pext_mob hp₀ hγ hz
  set x := utm_pext p₀ z with hx
  set h : ℂ → ℂ := fun w => chartAt ℂ x (utm_pext p₀ w) with hh
  have hinv : ∀ g ∈ Γ₀, ∀ w : ℂ, 0 < w.im → h (utm_b_mob g w) = h w := fun g hg w hw => by
    simp only [hh, utm_b_pext_mob hp₀ hg hw]
  have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := h36t_den_ne γ ⟨z, hz⟩
  have hm := utm_b_hasDerivAt_mob γ hden
  have hmz := utm_b_mob_im_pos γ hz
  have hkey : deriv h z = deriv h (utm_b_mob γ z) * (1 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) := by
    have heq : h ∘ utm_b_mob γ =ᶠ[𝓝 z] h := by
      filter_upwards [isOpen_upperHalf.mem_nhds hz] with w hw
      exact hinv γ hγ w hw
    by_cases hd : DifferentiableAt ℂ h (utm_b_mob γ z)
    · rw [← heq.deriv_eq]
      exact (hd.hasDerivAt.comp z hm).deriv
    · rw [deriv_zero_of_not_differentiableAt hd, zero_mul]
      refine deriv_zero_of_not_differentiableAt fun hdz => hd ?_
      have heq' : h ∘ utm_b_mob γ⁻¹ =ᶠ[𝓝 (utm_b_mob γ z)] h := by
        filter_upwards [isOpen_upperHalf.mem_nhds hmz] with w hw
        exact hinv γ⁻¹ (Γ₀.inv_mem hγ) w hw
      have hback : utm_b_mob γ⁻¹ (utm_b_mob γ z) = z := by
        rw [utm_b_mob_smul γ hz, utm_b_mob_coe, inv_smul_smul]
      have hden' : (γ⁻¹ 1 0 : ℂ) * utm_b_mob γ z + γ⁻¹ 1 1 ≠ 0 := h36t_den_ne γ⁻¹ ⟨_, hmz⟩
      have hd2 : DifferentiableAt ℂ (h ∘ utm_b_mob γ⁻¹) (utm_b_mob γ z) := by
        refine DifferentiableAt.comp _ ?_ (utm_b_hasDerivAt_mob γ⁻¹ hden').differentiableAt
        rw [hback]
        exact hdz
      exact hd2.congr_of_eventuallyEq heq'.symm
  have e1 : utm_liftQD q p₀ (utm_b_mob γ z) = q x (chartAt ℂ x x) * deriv h (utm_b_mob γ z) ^ 2 := by
    rw [utm_liftQD, hpz]
  have e2 : utm_liftQD q p₀ z = q x (chartAt ℂ x x) * deriv h z ^ 2 := rfl
  rw [e1, e2, hkey]
  ring

/-- `ψ(c • q) = c ψ(q)`: the lift of quadratic differentials is homogeneous. -/
theorem utm_x_liftQD_smul (q : S₀ → ℂ → ℂ) (p₀ : UpperHalfPlane → S₀) (c : ℂ) (z : ℂ) :
    utm_liftQD (c • q) p₀ z = c * utm_liftQD q p₀ z := by
  simp only [utm_liftQD, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- `ψ(q₁ + q₂) = ψ(q₁) + ψ(q₂)`: the lift of quadratic differentials is additive. -/
theorem utm_x_liftQD_add (q₁ q₂ : S₀ → ℂ → ℂ) (p₀ : UpperHalfPlane → S₀) (z : ℂ) :
    utm_liftQD (q₁ + q₂) p₀ z = utm_liftQD q₁ p₀ z + utm_liftQD q₂ p₀ z := by
  simp only [utm_liftQD, Pi.add_apply, add_mul]

/-- The lift `q ↦ 𝟙_ℍ ψ(q)`, `ψ = utm_liftQD q p₀`, as a `ℂ`-linear map on `Q(S₀)`. -/
def utm_x_liftL (p₀ : UpperHalfPlane → S₀) : holQuadDiffSubmodule S₀ →ₗ[ℂ] (ℂ → ℂ) where
  toFun q := upperHalf.indicator (utm_liftQD q p₀)
  map_add' q₁ q₂ := by
    funext z
    simp only [Submodule.coe_add, Pi.add_apply]
    by_cases hz : z ∈ upperHalf
    · simp only [indicator_of_mem hz, utm_x_liftQD_add]
    · simp only [indicator_of_notMem hz, add_zero]
  map_smul' c q := by
    funext z
    have hc : ((c • q : holQuadDiffSubmodule S₀) : S₀ → ℂ → ℂ) = c • (q : S₀ → ℂ → ℂ) := rfl
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hz : z ∈ upperHalf
    · rw [indicator_of_mem hz, indicator_of_mem hz, hc, utm_x_liftQD_smul]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz, mul_zero]

/-- **The chain rule under `Γ₀` in any chart**: with `h = φ_x ∘ p̂`, `h'(z) = h'(γ z) γ'(z)` for `γ ∈ Γ₀`, `z ∈ ℍ`
(`h ∘ γ = h` on `ℍ`; where `h` is not differentiable both sides vanish; as in `utm_b_liftQD_automorphic`). -/
theorem utm_x2_deriv_mob {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (x : S₀) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ₀) {z : ℂ}
    (hz : 0 < z.im) :
    deriv (fun w => chartAt ℂ x (utm_pext p₀ w)) z =
      deriv (fun w => chartAt ℂ x (utm_pext p₀ w)) (utm_b_mob γ z) * (1 / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2) := by
  set h : ℂ → ℂ := fun w => chartAt ℂ x (utm_pext p₀ w) with hh
  have hinv : ∀ g ∈ Γ₀, ∀ w : ℂ, 0 < w.im → h (utm_b_mob g w) = h w := fun g hg w hw => by
    simp only [hh, utm_b_pext_mob hp₀ hg hw]
  have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := h36t_den_ne γ ⟨z, hz⟩
  have hm := utm_b_hasDerivAt_mob γ hden
  have hmz := utm_b_mob_im_pos γ hz
  have heq : h ∘ utm_b_mob γ =ᶠ[𝓝 z] h := by
    filter_upwards [isOpen_upperHalf.mem_nhds hz] with w hw
    exact hinv γ hγ w hw
  by_cases hd : DifferentiableAt ℂ h (utm_b_mob γ z)
  · rw [← heq.deriv_eq]
    exact (hd.hasDerivAt.comp z hm).deriv
  · rw [deriv_zero_of_not_differentiableAt hd, zero_mul]
    refine deriv_zero_of_not_differentiableAt fun hdz => hd ?_
    have heq' : h ∘ utm_b_mob γ⁻¹ =ᶠ[𝓝 (utm_b_mob γ z)] h := by
      filter_upwards [isOpen_upperHalf.mem_nhds hmz] with w hw
      exact hinv γ⁻¹ (Γ₀.inv_mem hγ) w hw
    have hback : utm_b_mob γ⁻¹ (utm_b_mob γ z) = z := by
      rw [utm_b_mob_smul γ hz, utm_b_mob_coe, inv_smul_smul]
    have hden' : (γ⁻¹ 1 0 : ℂ) * utm_b_mob γ z + γ⁻¹ 1 1 ≠ 0 := h36t_den_ne γ⁻¹ ⟨_, hmz⟩
    have hd2 : DifferentiableAt ℂ (h ∘ utm_b_mob γ⁻¹) (utm_b_mob γ z) := by
      refine DifferentiableAt.comp _ ?_ (utm_b_hasDerivAt_mob γ⁻¹ hden').differentiableAt
      rw [hback]
      exact hdz
    exact hd2.congr_of_eventuallyEq heq'.symm

/-- For a weight-`4` automorphic `φ`, the quotient `φ / h'²` (`h = φ_x ∘ p̂`) is `Γ₀`-invariant on `ℍ`. -/
theorem utm_x2_quot_inv {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (x : S₀) {φ : ℂ → ℂ}
    (hφΓ : ∀ γ ∈ Γ₀, ∀ z ∈ upperHalf,
      φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ₀) {z : ℂ} (hz : 0 < z.im) :
    φ (utm_b_mob γ z) / deriv (fun w => chartAt ℂ x (utm_pext p₀ w)) (utm_b_mob γ z) ^ 2 =
      φ z / deriv (fun w => chartAt ℂ x (utm_pext p₀ w)) z ^ 2 := by
  have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := h36t_den_ne γ ⟨z, hz⟩
  have hφ' : φ (utm_b_mob γ z) = φ z * ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 := by
    have h := hφΓ γ hγ z hz
    rw [div_eq_iff (pow_ne_zero 4 hden)] at h
    exact h
  rw [utm_x2_deriv_mob hp₀ x hγ hz, hφ']
  by_cases ha : deriv (fun w => chartAt ℂ x (utm_pext p₀ w)) (utm_b_mob γ z) = 0
  · rw [ha]
    simp
  · field_simp

/-- **The descended differential** of `φ`: `q_x(w) = φ(τ) / ((φ_x ∘ p̂)'(τ))²` with `τ = sec (φ_x⁻¹ w)` on the chart
target at `x`, `0` elsewhere (`sec` a section of `p₀`). -/
def utm_x2_desc (p₀ : UpperHalfPlane → S₀) (sec : S₀ → UpperHalfPlane) (φ : ℂ → ℂ) : S₀ → ℂ → ℂ :=
  fun x => (chartAt ℂ x).target.indicator fun w =>
    φ (sec ((chartAt ℂ x).symm w) : ℂ) /
      deriv (fun v => chartAt ℂ x (utm_pext p₀ v)) (sec ((chartAt ℂ x).symm w) : ℂ) ^ 2

/-- **The descended differential at a lifted point**: if `p₀ τ` lies in the chart source at `x`, then
`q_x(φ_x(p₀ τ)) = φ(τ) / h'(τ)²`, `h = φ_x ∘ p̂` (independent of the section, by `utm_x2_quot_inv`). -/
theorem utm_x2_desc_apply {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {sec : S₀ → UpperHalfPlane} (hsec : ∀ s, p₀ (sec s) = s) {φ : ℂ → ℂ}
    (hφΓ : ∀ γ ∈ Γ₀, ∀ z ∈ upperHalf,
      φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z)
    (x : S₀) (τ : UpperHalfPlane) (hτ : p₀ τ ∈ (chartAt ℂ x).source) :
    utm_x2_desc p₀ sec φ x (chartAt ℂ x (p₀ τ)) =
      φ τ / deriv (fun v => chartAt ℂ x (utm_pext p₀ v)) τ ^ 2 := by
  have ht : chartAt ℂ x (p₀ τ) ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hτ
  have hs : (chartAt ℂ x).symm (chartAt ℂ x (p₀ τ)) = p₀ τ := (chartAt ℂ x).left_inv hτ
  simp only [utm_x2_desc]
  rw [indicator_of_mem ht, hs]
  obtain ⟨γ, hγ, hγτ⟩ := (hp₀.2.2.2 τ (sec (p₀ τ))).1 (hsec (p₀ τ)).symm
  have hc : ((sec (p₀ τ) : UpperHalfPlane) : ℂ) = utm_b_mob γ τ := by rw [← hγτ, utm_b_mob_coe]
  rw [hc]
  exact utm_x2_quot_inv hp₀ x hφΓ hγ τ.coe_im_pos

/-- [S4, stub] **Descent of automorphic forms.**  A holomorphic function `φ` on `ℍ` which is `Γ₀`-automorphic of
weight `4` (`φ(γ z) γ'(z)² = φ(z)`, in the form of `integrableAutomorphicQD`) is the lift `utm_liftQD q p₀` of a
holomorphic quadratic differential `q` on `S₀`.

*Truth:* for `z` in the chart target at `x` choose `τ ∈ ℍ` with `p₀ τ = φ_x⁻¹ z` and put
`qₓ(z) = φ(τ) / ((φ_x ∘ p̂)'(τ))²` (`0` off the chart target).  Another choice is `γ τ`, `γ ∈ Γ₀` (fibres = orbits),
and automorphy plus the chain rule `(φ_x ∘ p̂)'(τ) = (φ_x ∘ p̂)'(γ τ) γ'(τ)` give the same value (the converse of
`utm_b_liftQD_automorphic`).  Near `z`, `qₓ = (φ ∘ s) (s')²` for the local inverse `s` of `φ_x ∘ p̂`, so `qₓ` is
holomorphic, and the transformation law between charts is the chain rule.  At `x = p₀ τ` the definition gives back
`utm_liftQD q p₀ τ = φ(τ)`.

*Route/reuse:* `utm_liftQD_local` (this file l.460), `utm_b_liftQD_automorphic` (l.903), `utm_b_mob` (l.856),
`utm_a_local_inverse` (l.591); S26 `s26u_law` (l.1779); S22 `IsDiffFamily` (l.235), `holQuadDiffSubmodule` (l.262).
*Estimate:* 0.6–1k.

*Walls:* none: the correspondence between `Q(S₀)` and weight-`4` forms on the given `ℍ/Γ₀`, with no dimension count
(no W-RR) and no other surface involved (no W-UC, W-QC, W-TOP, W-IoD). -/
theorem utm_x_descent [IsManifold 𝓘(ℂ) ω S₀]
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ upperHalf)
    (hφΓ : ∀ γ ∈ Γ₀, ∀ z ∈ upperHalf,
      φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) / ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z) :
    ∃ q : S₀ → ℂ → ℂ, IsHolQuadDiff q ∧ ∀ τ ∈ upperHalf, utm_liftQD q p₀ τ = φ τ := by
  set sec : S₀ → UpperHalfPlane := Function.surjInv hp₀.2.2.1 with hsecdef
  have hsec : ∀ s, p₀ (sec s) = s := Function.surjInv_eq hp₀.2.2.1
  have hq0 : IsHolQuadDiff (0 : S₀ → ℂ → ℂ) := (holQuadDiffSubmodule S₀).zero_mem
  -- the chart expression `h = φ_x ∘ p̂` is a local biholomorphism near every lifted point of the chart source
  have hloc : ∀ (x : S₀) (τ : UpperHalfPlane), p₀ τ ∈ (chartAt ℂ x).source →
      ∃ U : Set ℂ, IsOpen U ∧ (τ : ℂ) ∈ U ∧ ∀ w ∈ U,
        HasDerivAt (fun v => chartAt ℂ x (utm_pext p₀ v)) (deriv (fun v => chartAt ℂ x (utm_pext p₀ v)) w) w ∧
          deriv (fun v => chartAt ℂ x (utm_pext p₀ v)) w ≠ 0 := by
    intro x τ hτ
    obtain ⟨U, hUo, hτU, -, -, hU⟩ := utm_liftQD_local hq0 hp₀ τ x hτ
    exact ⟨U, hUo, hτU, fun w hw => ⟨(hU w hw).2.1, (hU w hw).2.2.1⟩⟩
  have hpt : ∀ τ : UpperHalfPlane, utm_pext p₀ (τ : ℂ) = p₀ τ := fun τ => by
    rw [utm_a_pext_eq p₀ τ.coe_im_pos, UpperHalfPlane.ofComplex_apply]
  -- the transformation law
  have hD : IsDiffFamily 2 0 (utm_x2_desc p₀ sec φ) := by
    refine ⟨fun x w hw => ?_, fun x y w hw hwx => ?_⟩
    · simp only [utm_x2_desc]
      rw [indicator_of_notMem hw]
    · obtain ⟨τ, hpτ⟩ := hp₀.2.2.1 ((chartAt ℂ y).symm w)
      have hsy : (chartAt ℂ y).symm w ∈ (chartAt ℂ y).source := (chartAt ℂ y).map_target hw
      have hwy : chartAt ℂ y (p₀ τ) = w := by
        rw [hpτ]
        exact (chartAt ℂ y).right_inv hw
      have hTw : chartTransition x y w = chartAt ℂ x (p₀ τ) := by
        unfold chartTransition
        rw [hpτ]
      have hKy := utm_x2_desc_apply hp₀ hsec hφΓ y τ (by rw [hpτ]; exact hsy)
      have hKx := utm_x2_desc_apply hp₀ hsec hφΓ x τ (by rw [hpτ]; exact hwx)
      rw [hwy] at hKy
      rw [hTw, hKx, hKy]
      obtain ⟨hTd, -⟩ := s23_transition x y hw hwx
      have hyd : DifferentiableAt ℂ (fun v => chartAt ℂ y (utm_pext p₀ v)) τ :=
        utm_a_differentiableAt hp₀.2.1 y τ.coe_im_pos (by rw [hpt, hpτ]; exact hsy)
      have hev : (fun v => chartAt ℂ x (utm_pext p₀ v)) =ᶠ[𝓝 (τ : ℂ)]
          chartTransition x y ∘ fun v => chartAt ℂ y (utm_pext p₀ v) := by
        filter_upwards [(utm_a_continuousAt hp₀.1.continuous τ.coe_im_pos).preimage_mem_nhds
          ((chartAt ℂ y).open_source.mem_nhds (by rw [hpt, hpτ]; exact hsy))] with v hv
        show chartAt ℂ x (utm_pext p₀ v) = chartAt ℂ x ((chartAt ℂ y).symm (chartAt ℂ y (utm_pext p₀ v)))
        rw [(chartAt ℂ y).left_inv hv]
      have hyτ : (fun v => chartAt ℂ y (utm_pext p₀ v)) τ = w := by
        show chartAt ℂ y (utm_pext p₀ τ) = w
        rw [hpt]
        exact hwy
      have hder : deriv (fun v => chartAt ℂ x (utm_pext p₀ v)) τ =
          deriv (chartTransition x y) w * deriv (fun v => chartAt ℂ y (utm_pext p₀ v)) τ := by
        rw [hev.deriv_eq]
        rw [← hyτ] at hTd ⊢
        exact (hTd.hasDerivAt.comp (τ : ℂ) hyd.hasDerivAt).deriv
      rw [hder]
      obtain ⟨U, -, hτU, hU⟩ := hloc y τ (by rw [hpτ]; exact hsy)
      obtain ⟨-, hne⟩ := hU τ hτU
      obtain ⟨-, hTne⟩ := s23_transition x y hw hwx
      norm_num
      field_simp
  -- holomorphy on the chart targets
  have hH : ∀ x : S₀, DifferentiableOn ℂ (utm_x2_desc p₀ sec φ x) (chartAt ℂ x).target := by
    intro x w hw
    obtain ⟨τ, hpτ⟩ := hp₀.2.2.1 ((chartAt ℂ x).symm w)
    have hsx : (chartAt ℂ x).symm w ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hw
    obtain ⟨E, hτE, hpE⟩ := hp₀.1.isLocalHomeomorph τ
    have hsE : (chartAt ℂ x).symm w ∈ E.target := by
      rw [← hpτ, hpE]
      exact E.map_source hτE
    obtain ⟨L, hLdef⟩ : ∃ L : ℂ → ℂ, L = fun w' => (E.symm ((chartAt ℂ x).symm w') : ℂ) := ⟨_, rfl⟩
    have hLw : L w = τ := by
      rw [hLdef]
      show ((E.symm ((chartAt ℂ x).symm w) : UpperHalfPlane) : ℂ) = τ
      rw [← hpτ, hpE, E.left_inv hτE]
    have hLc : ContinuousAt L w := by
      rw [hLdef]
      exact UpperHalfPlane.continuous_coe.continuousAt.comp
        ((E.continuousAt_symm hsE).comp ((chartAt ℂ x).continuousAt_symm hw))
    have hev0 : ∀ᶠ w' in 𝓝 w, w' ∈ (chartAt ℂ x).target := (chartAt ℂ x).open_target.mem_nhds hw
    have hev0' : ∀ᶠ w' in 𝓝 w, (chartAt ℂ x).symm w' ∈ E.target :=
      ((chartAt ℂ x).continuousAt_symm hw).preimage_mem_nhds (E.open_target.mem_nhds hsE)
    have hev1 : ∀ᶠ w' in 𝓝 w, w' ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm w' ∈ E.target := hev0.and hev0'
    have hev2 : ∀ᶠ w' in 𝓝 w, (fun v => chartAt ℂ x (utm_pext p₀ v)) (L w') = w' ∧
        utm_x2_desc p₀ sec φ x w' = φ (L w') / deriv (fun v => chartAt ℂ x (utm_pext p₀ v)) (L w') ^ 2 := by
      filter_upwards [hev1] with w' hw'
      obtain ⟨hw't, hw'E⟩ := hw'
      have hpσ : p₀ (E.symm ((chartAt ℂ x).symm w')) = (chartAt ℂ x).symm w' := by
        rw [hpE]
        exact E.right_inv hw'E
      have hσx : p₀ (E.symm ((chartAt ℂ x).symm w')) ∈ (chartAt ℂ x).source := by
        rw [hpσ]
        exact (chartAt ℂ x).map_target hw't
      have hcσ : chartAt ℂ x (p₀ (E.symm ((chartAt ℂ x).symm w'))) = w' := by
        rw [hpσ]
        exact (chartAt ℂ x).right_inv hw't
      rw [hLdef]
      refine ⟨?_, ?_⟩
      · show chartAt ℂ x (utm_pext p₀ ((E.symm ((chartAt ℂ x).symm w') : UpperHalfPlane) : ℂ)) = w'
        rw [hpt]
        exact hcσ
      · have h := utm_x2_desc_apply hp₀ hsec hφΓ x _ hσx
        rw [hcσ] at h
        exact h
    obtain ⟨U, hUo, hτU, hU⟩ := hloc x τ (by rw [hpτ]; exact hsx)
    have hLd : HasDerivAt L (deriv (fun v => chartAt ℂ x (utm_pext p₀ v)) τ)⁻¹ w := by
      refine HasDerivAt.of_local_left_inverse (f := fun v => chartAt ℂ x (utm_pext p₀ v)) hLc ?_ (hU τ hτU).2
        (hev2.mono fun _ h => h.1)
      rw [hLw]
      exact (hU τ hτU).1
    have hφd : DifferentiableAt ℂ φ (L w) := by
      rw [hLw]
      exact hφ.differentiableAt (isOpen_upperHalf.mem_nhds τ.coe_im_pos)
    have hdd : DifferentiableAt ℂ (deriv (fun v => chartAt ℂ x (utm_pext p₀ v))) (L w) := by
      rw [hLw]
      have hdiffU : DifferentiableOn ℂ (fun v => chartAt ℂ x (utm_pext p₀ v)) U := fun v hv =>
        (hU v hv).1.differentiableAt.differentiableWithinAt
      exact (hdiffU.deriv hUo).differentiableAt (hUo.mem_nhds hτU)
    have hne : deriv (fun v => chartAt ℂ x (utm_pext p₀ v)) (L w) ^ 2 ≠ 0 := by
      rw [hLw]
      exact pow_ne_zero 2 (hU τ hτU).2
    have hdiff : DifferentiableAt ℂ
        (fun w' => φ (L w') / deriv (fun v => chartAt ℂ x (utm_pext p₀ v)) (L w') ^ 2) w :=
      (hφd.comp w hLd.differentiableAt).div ((hdd.comp w hLd.differentiableAt).pow 2) hne
    exact (hdiff.congr_of_eventuallyEq (hev2.mono fun _ h => h.2)).differentiableWithinAt
  have hq : IsHolQuadDiff (utm_x2_desc p₀ sec φ) :=
    (⟨hD, hH⟩ : IsDiffFamily 2 0 (utm_x2_desc p₀ sec φ) ∧
      ∀ x : S₀, DifferentiableOn ℂ (utm_x2_desc p₀ sec φ x) (chartAt ℂ x).target)
  refine ⟨utm_x2_desc p₀ sec φ, hq, fun τ hτ => ?_⟩
  -- the lift at `τ`
  have hτ' : 0 < τ.im := hτ
  obtain ⟨τ', hτ'def⟩ : ∃ τ' : UpperHalfPlane, (τ' : ℂ) = τ := ⟨⟨τ, hτ'⟩, rfl⟩
  have hx : utm_pext p₀ τ = p₀ τ' := by rw [← hτ'def, hpt]
  obtain ⟨U, -, hτU, hU⟩ := hloc (p₀ τ') τ' (mem_chart_source ℂ _)
  have hK := utm_x2_desc_apply hp₀ hsec hφΓ (p₀ τ') τ' (mem_chart_source ℂ _)
  unfold utm_liftQD
  rw [hx, hK, ← hτ'def]
  exact div_mul_cancel₀ _ (pow_ne_zero 2 (hU (τ' : ℂ) hτU).2)

/-- `|ψ(z)| (Im z)²` is `Γ₀`-invariant for the lift `ψ = utm_liftQD q p₀` (`ψ(γz) γ'(z)² = ψ(z)` and
`Im(γ z) = Im z / |cz+d|²`). -/
theorem utm_x2_norm_mul_im_sq (q : S₀ → ℂ → ℂ) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ Γ₀) {z : ℂ} (hz : 0 < z.im) :
    ‖utm_liftQD q p₀ (utm_b_mob γ z)‖ * (utm_b_mob γ z).im ^ 2 = ‖utm_liftQD q p₀ z‖ * z.im ^ 2 := by
  have h := utm_b_liftQD_automorphic q hp₀ hγ hz
  have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := h36t_den_ne γ ⟨z, hz⟩
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h1 := γ.det_coe
    rw [Matrix.det_fin_two] at h1
    exact h1
  have him : (utm_b_mob γ z).im = z.im / Complex.normSq ((γ 1 0 : ℂ) * z + γ 1 1) := utm_im_mobius hdet z
  rw [← h, norm_mul, him, norm_pow, norm_div, norm_one, norm_pow, Complex.normSq_eq_norm_sq]
  have hD : ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ≠ 0 := norm_ne_zero_iff.2 hden
  field_simp

/-- `utm_b_mob g` is holomorphic on `ℍ`. -/
theorem utm_b_mob_differentiableOn (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    DifferentiableOn ℂ (utm_b_mob g) upperHalf := fun z hz =>
  (utm_b_hasDerivAt_mob g (h36t_den_ne g ⟨z, hz⟩)).differentiableAt.differentiableWithinAt

/-- [P5, stub] **Bounded displacement of a `Γ₀`-commuting lift.**  If `F` commutes with `Γ₀` and `S₀` is compact,
every `τ` is joined to `F τ` by a curve in `ℍ`, Lipschitz on `[0, 1]`, of `ψ`-length at most `M`.

*Truth:* a compact `K` meets every `Γ₀`-orbit (`utm_exists_compact_translate`); for `γ τ ∈ K`, the straight segment
from `γ τ` to `F (γ τ) = γ (F τ)` lies in the compact convex hull of `K ∪ F K ⊆ ℍ`, where `|ψ|` is bounded, and its
image under `γ⁻¹` joins `τ` to `F τ` with the same `ψ`-length, because `ψ` is `Γ₀`-automorphic
(`ψ(γ z) γ'(z)² = ψ(z)`, from `p₀ ∘ γ = p₀` and the definition). -/
theorem utm_displacement [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀] {q : S₀ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (F : C(UpperHalfPlane, UpperHalfPlane))
    (hFΓ : ∀ γ ∈ Γ₀, ∀ τ, F (γ • τ) = γ • F τ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ : UpperHalfPlane, ∃ c : ℝ → ℂ, c 0 = τ ∧ c 1 = F τ ∧
      c '' Icc 0 1 ⊆ upperHalf ∧ (∃ K : ℝ≥0, LipschitzOnWith K c (Icc 0 1)) ∧
      ∫⁻ t in Ioo (0 : ℝ) 1, phiDensity (utm_liftQD q p₀) (c t) * ‖deriv c t‖ₑ ≤ ENNReal.ofReal M := by
  obtain ⟨K, hKc, hKorb⟩ := utm_exists_compact_translate hp₀
  have hψc : ContinuousOn (utm_liftQD q p₀) upperHalf := (utm_liftQD_differentiableOn hq hp₀).continuousOn
  -- the compact set `T` swept by the segments `[w, F w]`, `w ∈ K`
  set seg : UpperHalfPlane × ℝ → ℂ := fun p => (p.1 : ℂ) + p.2 • ((F p.1 : ℂ) - p.1) with hseg
  have hsegc : Continuous seg := by
    have h1 : Continuous fun p : UpperHalfPlane × ℝ => ((p.1 : UpperHalfPlane) : ℂ) :=
      UpperHalfPlane.continuous_coe.comp continuous_fst
    have h2 : Continuous fun p : UpperHalfPlane × ℝ => ((F p.1 : UpperHalfPlane) : ℂ) :=
      UpperHalfPlane.continuous_coe.comp (F.continuous.comp continuous_fst)
    exact h1.add (continuous_snd.smul (h2.sub h1))
  set T := seg '' (K ×ˢ Icc 0 1) with hT
  have hTc : IsCompact T := (hKc.prod isCompact_Icc).image hsegc
  have hTH : T ⊆ upperHalf := by
    rintro _ ⟨⟨w, t⟩, ⟨-, ht'⟩, rfl⟩
    have ht : t ∈ Icc (0 : ℝ) 1 := ht'
    show 0 < (seg (w, t)).im
    have h1 := w.coe_im_pos
    have h2 := (F w).coe_im_pos
    simp only [hseg, Complex.add_im, Complex.smul_im, Complex.sub_im, smul_eq_mul]
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]
      linarith
    · nlinarith [mul_pos (sub_pos.2 h) h1, mul_nonneg ht.1 h2.le]
  obtain ⟨B, hB⟩ := hTc.exists_bound_of_continuousOn (hψc.mono hTH)
  have hdc : ContinuousOn (fun w : UpperHalfPlane => ((F w : UpperHalfPlane) : ℂ) - w) K :=
    ((UpperHalfPlane.continuous_coe.comp F.continuous).sub UpperHalfPlane.continuous_coe).continuousOn
  obtain ⟨D, hD⟩ := hKc.exists_bound_of_continuousOn hdc
  refine ⟨Real.sqrt B * max D 0, mul_nonneg (Real.sqrt_nonneg _) (le_max_right _ _), fun τ => ?_⟩
  -- translate `τ` into `K`, take the segment `[w, F w]`, and map it back by `γ⁻¹`
  obtain ⟨γ, hγ, hγK⟩ := hKorb τ
  set w : UpperHalfPlane := γ • τ with hw
  set v : ℂ := ((F w : UpperHalfPlane) : ℂ) - w with hv
  set s : ℝ → ℂ := fun t => (w : ℂ) + t • v with hs
  have hsT : ∀ t ∈ Icc (0 : ℝ) 1, s t ∈ T := fun t ht => ⟨(w, t), ⟨hγK, ht⟩, rfl⟩
  have hsH : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (s t).im := fun t ht => hTH (hsT t ht)
  have hsd : ∀ t : ℝ, HasDerivAt s v t := fun t => by
    have h := ((hasDerivAt_id t).smul_const v).const_add (w : ℂ)
    rw [one_smul] at h
    exact h
  refine ⟨fun t => utm_b_mob γ⁻¹ (s t), ?_, ?_, ?_, ?_, ?_⟩
  · -- `c 0 = τ`
    show utm_b_mob γ⁻¹ ((w : ℂ) + (0 : ℝ) • v) = τ
    rw [zero_smul, add_zero, utm_b_mob_coe, hw, inv_smul_smul]
  · -- `c 1 = F τ`
    show utm_b_mob γ⁻¹ ((w : ℂ) + (1 : ℝ) • v) = F τ
    rw [one_smul, hv, add_sub_cancel, utm_b_mob_coe, hw, hFΓ γ hγ τ, inv_smul_smul]
  · -- the curve lies in `ℍ`
    rintro _ ⟨t, ht, rfl⟩
    exact utm_b_mob_im_pos γ⁻¹ (hsH t ht)
  · -- Lipschitz on `[0, 1]` (`C¹` on the compact convex `[0, 1]`)
    have hcd : ContDiffOn ℝ 1 (fun t => utm_b_mob γ⁻¹ (s t)) (Icc 0 1) := by
      intro t ht
      have hm : ContDiffAt ℂ 1 (utm_b_mob γ⁻¹) (s t) :=
        ((utm_b_mob_differentiableOn γ⁻¹).contDiffOn isOpen_upperHalf).contDiffAt
          (isOpen_upperHalf.mem_nhds (hsH t ht))
      have hsc : ContDiffAt ℝ 1 s t := (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffAt
      exact ((hm.restrict_scalars ℝ).comp t hsc).contDiffWithinAt
    obtain ⟨K', hK'⟩ := hcd.exists_lipschitzOnWith one_ne_zero (convex_Icc 0 1) isCompact_Icc
    exact ⟨K', hK'⟩
  · -- the `ψ`-length: `γ⁻¹` preserves the density, so it is the length of the segment
    have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, phiDensity (utm_liftQD q p₀) (utm_b_mob γ⁻¹ (s t)) *
        ‖deriv (fun t => utm_b_mob γ⁻¹ (s t)) t‖ₑ ≤ ENNReal.ofReal (Real.sqrt B * max D 0) := by
      intro t ht
      have htI : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
      have hden : (γ⁻¹ 1 0 : ℂ) * s t + γ⁻¹ 1 1 ≠ 0 := h36t_den_ne γ⁻¹ ⟨s t, hsH t htI⟩
      set m' : ℂ := 1 / ((γ⁻¹ 1 0 : ℂ) * s t + γ⁻¹ 1 1) ^ 2 with hm'
      have hcd : HasDerivAt (fun t => utm_b_mob γ⁻¹ (s t)) (m' * v) t :=
        (utm_b_hasDerivAt_mob γ⁻¹ hden).comp t (hsd t)
      have haut := utm_b_liftQD_automorphic q hp₀ (Γ₀.inv_mem hγ) (hsH t htI)
      have hn : ‖utm_liftQD q p₀ (s t)‖ = ‖utm_liftQD q p₀ (utm_b_mob γ⁻¹ (s t))‖ * ‖m'‖ ^ 2 := by
        rw [← haut, norm_mul, norm_pow]
      have hsq : Real.sqrt ‖utm_liftQD q p₀ (s t)‖ =
          Real.sqrt ‖utm_liftQD q p₀ (utm_b_mob γ⁻¹ (s t))‖ * ‖m'‖ := by
        rw [hn, Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      rw [hcd.deriv, fx_p5_density_mul]
      apply ENNReal.ofReal_le_ofReal
      calc Real.sqrt ‖utm_liftQD q p₀ (utm_b_mob γ⁻¹ (s t))‖ * ‖m' * v‖
          = Real.sqrt ‖utm_liftQD q p₀ (s t)‖ * ‖v‖ := by
            rw [hsq, norm_mul]
            ring
        _ ≤ Real.sqrt B * max D 0 :=
            mul_le_mul (Real.sqrt_le_sqrt (hB _ (hsT t htI))) (le_max_of_le_left (hD w hγK))
              (norm_nonneg _) (Real.sqrt_nonneg _)
    calc ∫⁻ t in Ioo (0 : ℝ) 1, phiDensity (utm_liftQD q p₀) (utm_b_mob γ⁻¹ (s t)) *
          ‖deriv (fun t => utm_b_mob γ⁻¹ (s t)) t‖ₑ
        ≤ ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt B * max D 0) :=
          setLIntegral_mono' measurableSet_Ioo hpt
      _ = ENNReal.ofReal (Real.sqrt B * max D 0) := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]

/-- Lipschitz bounds on two adjacent closed intervals `[a, b]`, `[b, c]` glue to `[a, c]`. -/
theorem utm_b_lipschitzOnWith_Icc_union {f : ℝ → ℂ} {K : ℝ≥0} {a b c : ℝ}
    (h1 : LipschitzOnWith K f (Icc a b)) (h2 : LipschitzOnWith K f (Icc b c)) :
    LipschitzOnWith K f (Icc a c) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rcases le_total x b with hxb | hxb <;> rcases le_total y b with hyb | hyb
  · exact h1.dist_le_mul x ⟨hx.1, hxb⟩ y ⟨hy.1, hyb⟩
  · have hb1 : b ∈ Icc a b := ⟨hx.1.trans hxb, le_rfl⟩
    have hb2 : b ∈ Icc b c := ⟨le_rfl, hyb.trans hy.2⟩
    calc dist (f x) (f y) ≤ dist (f x) (f b) + dist (f b) (f y) := dist_triangle _ _ _
      _ ≤ K * dist x b + K * dist b y :=
          add_le_add (h1.dist_le_mul x ⟨hx.1, hxb⟩ b hb1) (h2.dist_le_mul b hb2 y ⟨hyb, hy.2⟩)
      _ = K * dist x y := by
          simp only [Real.dist_eq]
          rw [abs_of_nonpos (by linarith : x - b ≤ 0), abs_of_nonpos (by linarith : b - y ≤ 0),
            abs_of_nonpos (by linarith : x - y ≤ 0)]
          ring
  · have hb1 : b ∈ Icc a b := ⟨hy.1.trans hyb, le_rfl⟩
    have hb2 : b ∈ Icc b c := ⟨le_rfl, hxb.trans hx.2⟩
    calc dist (f x) (f y) ≤ dist (f x) (f b) + dist (f b) (f y) := dist_triangle _ _ _
      _ ≤ K * dist x b + K * dist b y :=
          add_le_add (h2.dist_le_mul x ⟨hxb, hx.2⟩ b hb2) (h1.dist_le_mul b hb1 y ⟨hy.1, hyb⟩)
      _ = K * dist x y := by
          simp only [Real.dist_eq]
          rw [abs_of_nonneg (by linarith : 0 ≤ x - b), abs_of_nonneg (by linarith : 0 ≤ b - y),
            abs_of_nonneg (by linarith : 0 ≤ x - y)]
          ring
  · exact h2.dist_le_mul x ⟨hxb, hx.2⟩ y ⟨hyb, hy.2⟩

/-- An affine reparametrization `β = c ∘ (m · + k)` on `[l, r]` of a curve Lipschitz on `[0, 1]` is Lipschitz. -/
theorem utm_b_lipschitz_affine {c β : ℝ → ℂ} {K C : ℝ≥0} (hc : LipschitzOnWith K c (Icc 0 1))
    {l r m k : ℝ} (hC : (K : ℝ) * |m| ≤ C) (hmaps : ∀ t ∈ Icc l r, m * t + k ∈ Icc (0 : ℝ) 1)
    (heq : ∀ t ∈ Icc l r, β t = c (m * t + k)) : LipschitzOnWith C β (Icc l r) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [heq x hx, heq y hy]
  calc dist (c (m * x + k)) (c (m * y + k)) ≤ K * dist (m * x + k) (m * y + k) :=
        hc.dist_le_mul _ (hmaps x hx) _ (hmaps y hy)
    _ = K * |m| * dist x y := by
        rw [Real.dist_eq, Real.dist_eq, show m * x + k - (m * y + k) = m * (x - y) by ring, abs_mul]
        ring
    _ ≤ C * dist x y := mul_le_mul_of_nonneg_right hC dist_nonneg

/-- The `ψ`-length of an affine reparametrization `β = c ∘ (m · + k)` over `(l, r)`, where `m · + k` maps
`(l, r)` onto `(0, 1)`, is the `ψ`-length of `c` over `(0, 1)`. -/
theorem utm_b_piece (ψ : ℂ → ℂ) {β c : ℝ → ℂ} {l r m k : ℝ} (hm : m ≠ 0)
    (himg : (fun t => m * t + k) '' Ioo l r = Ioo 0 1) (heq : ∀ t ∈ Ioo l r, β t = c (m * t + k)) :
    ∫⁻ t in Ioo l r, phiDensity ψ (β t) * ‖deriv β t‖ₑ =
      ∫⁻ s in Ioo (0 : ℝ) 1, phiDensity ψ (c s) * ‖deriv c s‖ₑ := by
  have hd : ∀ t, HasDerivAt (fun t => m * t + k) m t := fun t => by
    simpa using ((hasDerivAt_id' t).const_mul m).add_const k
  have hinj : InjOn (fun t => m * t + k) (Ioo l r) := fun x _ y _ hxy => by
    have h : m * x = m * y := by simpa using hxy
    exact mul_left_cancel₀ hm h
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (fun t _ => (hd t).hasDerivWithinAt) hinj]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have hev : β =ᶠ[𝓝 t] fun t => c (m * t + k) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact heq s hs
  have hder : deriv (fun t => c (m * t + k)) t = m • deriv c (m * t + k) := by
    rw [deriv_comp_mul_left m (fun y => c (y + k)) t, deriv_comp_add_const]
  rw [hev.deriv_eq, hder, heq t ht, enorm_smul, Real.enorm_eq_ofReal_abs]
  ring

/-- [P6, stub] **Concatenation.**  Three curves, Lipschitz on `[0, 1]`, with `c₁ 1 = c₂ 0` and `c₂ 1 = c₃ 1`, give an
open curve `β` (traversing `c₁`, then `c₂`, then `c₃` backwards) from `c₁ 0` to `c₃ 0` whose `ψ`-length is at most
the sum of the three.

*Truth:* `β = c₁(3t)`, `c₂(3t − 1)`, `c₃(3 − 3t)` on the thirds is Lipschitz on `[0, 1]`, hence an `LRCurve`; affine
substitution on each third (the two junctions are null) gives the lengths. -/
theorem utm_concat (ψ : ℂ → ℂ) {c₁ c₂ c₃ : ℝ → ℂ} (h₁ : ∃ K : ℝ≥0, LipschitzOnWith K c₁ (Icc 0 1))
    (h₂ : ∃ K : ℝ≥0, LipschitzOnWith K c₂ (Icc 0 1)) (h₃ : ∃ K : ℝ≥0, LipschitzOnWith K c₃ (Icc 0 1))
    {U : Set ℂ} (hU₁ : c₁ '' Icc 0 1 ⊆ U) (hU₂ : c₂ '' Icc 0 1 ⊆ U) (hU₃ : c₃ '' Icc 0 1 ⊆ U)
    (h12 : c₁ 1 = c₂ 0) (h23 : c₂ 1 = c₃ 1) :
    ∃ β : LRCurve, β.trace ⊆ U ∧ Tendsto β.toFun (𝓝[>] 0) (𝓝 (c₁ 0)) ∧
      Tendsto β.toFun (𝓝[<] 1) (𝓝 (c₃ 0)) ∧
      phiLength ψ β ≤ (∫⁻ t in Ioo (0 : ℝ) 1, phiDensity ψ (c₁ t) * ‖deriv c₁ t‖ₑ) +
        (∫⁻ t in Ioo (0 : ℝ) 1, phiDensity ψ (c₂ t) * ‖deriv c₂ t‖ₑ) +
        ∫⁻ t in Ioo (0 : ℝ) 1, phiDensity ψ (c₃ t) * ‖deriv c₃ t‖ₑ := by
  obtain ⟨K₁, hK₁⟩ := h₁
  obtain ⟨K₂, hK₂⟩ := h₂
  obtain ⟨K₃, hK₃⟩ := h₃
  set β₀ : ℝ → ℂ := fun t => if t ≤ 1 / 3 then c₁ (3 * t) else if t ≤ 2 / 3 then c₂ (3 * t - 1)
    else c₃ (3 - 3 * t) with hβ₀
  -- the three pieces
  have e1 : ∀ t ∈ Icc (0 : ℝ) (1 / 3), β₀ t = c₁ (3 * t + 0) := by
    intro t ht
    simp only [hβ₀, ht.2, add_zero, ↓reduceIte]
  have e2 : ∀ t ∈ Icc (1 / 3 : ℝ) (2 / 3), β₀ t = c₂ (3 * t + -1) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]
      have e : β₀ (1 / 3) = c₁ 1 := by
        simp only [hβ₀, le_refl, ↓reduceIte]
        norm_num
      rw [e, h12]
      norm_num
    · have hn : ¬ t ≤ 1 / 3 := not_le.2 h
      simp only [hβ₀, hn, ht.2, ↓reduceIte]
      ring_nf
  have e3 : ∀ t ∈ Icc (2 / 3 : ℝ) 1, β₀ t = c₃ (-3 * t + 3) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h]
      have e : β₀ (2 / 3) = c₂ 1 := by
        simp only [hβ₀]
        norm_num
      rw [e, h23]
      norm_num
    · have hn : ¬ t ≤ 2 / 3 := not_le.2 h
      have hn' : ¬ t ≤ 1 / 3 := fun h' => hn (h'.trans (by norm_num))
      simp only [hβ₀, hn, hn', ↓reduceIte]
      ring_nf
  -- Lipschitz on `[0, 1]`
  set C : ℝ≥0 := (K₁ + K₂ + K₃) * 3 with hC
  have hC3 : ∀ m : ℝ, |m| = 3 → (K₁ : ℝ) * |m| ≤ C ∧ (K₂ : ℝ) * |m| ≤ C ∧ (K₃ : ℝ) * |m| ≤ C := by
    intro m hm
    rw [hm, hC]
    push_cast
    have := K₁.2
    have := K₂.2
    have := K₃.2
    refine ⟨?_, ?_, ?_⟩ <;> nlinarith
  have h3 : |(3 : ℝ)| = 3 := abs_of_pos (by norm_num)
  have h3' : |(-3 : ℝ)| = 3 := by norm_num
  have L1 : LipschitzOnWith C β₀ (Icc 0 (1 / 3)) :=
    utm_b_lipschitz_affine hK₁ (hC3 3 h3).1 (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩) e1
  have L2 : LipschitzOnWith C β₀ (Icc (1 / 3) (2 / 3)) :=
    utm_b_lipschitz_affine hK₂ (hC3 3 h3).2.1 (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩) e2
  have L3 : LipschitzOnWith C β₀ (Icc (2 / 3) 1) :=
    utm_b_lipschitz_affine hK₃ (hC3 (-3) h3').2.2 (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩) e3
  have L : LipschitzOnWith C β₀ (Icc 0 1) :=
    utm_b_lipschitzOnWith_Icc_union (utm_b_lipschitzOnWith_Icc_union L1 L2) L3
  refine ⟨⟨β₀, fun t _ => ⟨C, Ioo 0 1, self_mem_nhdsWithin, L.mono Ioo_subset_Icc_self⟩⟩, ?_, ?_, ?_, ?_⟩
  · -- the trace
    rintro _ ⟨t, ht, rfl⟩
    show β₀ t ∈ U
    by_cases h1 : t ≤ 1 / 3
    · rw [e1 t ⟨ht.1.le, h1⟩]
      exact hU₁ ⟨_, ⟨by linarith [ht.1], by linarith⟩, rfl⟩
    · by_cases h2 : t ≤ 2 / 3
      · rw [e2 t ⟨(not_le.1 h1).le, h2⟩]
        exact hU₂ ⟨_, ⟨by linarith [not_le.1 h1], by linarith⟩, rfl⟩
      · rw [e3 t ⟨(not_le.1 h2).le, ht.2.le⟩]
        exact hU₃ ⟨_, ⟨by linarith [ht.2], by linarith [not_le.1 h2]⟩, rfl⟩
  · -- the left end point
    have h0 : β₀ 0 = c₁ 0 := by
      rw [e1 0 ⟨le_rfl, by norm_num⟩]
      norm_num
    rw [← h0]
    exact Filter.Tendsto.mono_left (L.continuousOn.continuousWithinAt ⟨le_rfl, zero_le_one⟩)
      (nhdsWithin_le_of_mem (Icc_mem_nhdsGT zero_lt_one))
  · -- the right end point
    have h1 : β₀ 1 = c₃ 0 := by
      rw [e3 1 ⟨by norm_num, le_rfl⟩]
      norm_num
    rw [← h1]
    exact Filter.Tendsto.mono_left (L.continuousOn.continuousWithinAt ⟨zero_le_one, le_rfl⟩)
      (nhdsWithin_le_of_mem (Icc_mem_nhdsLT zero_lt_one))
  · -- the length
    set g : ℝ → ℝ≥0∞ := fun t => phiDensity ψ (β₀ t) * ‖deriv β₀ t‖ₑ with hg
    have hsub : Ioo (0 : ℝ) 1 ⊆ ((Ioo 0 (1 / 3) ∪ Ioo (1 / 3) (2 / 3)) ∪ Ioo (2 / 3) 1) ∪ {1 / 3, 2 / 3} := by
      intro t ht
      rcases lt_trichotomy t (1 / 3) with h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨ht.1, h⟩))
      · exact Or.inr (Or.inl h)
      · rcases lt_trichotomy t (2 / 3) with h' | h' | h'
        · exact Or.inl (Or.inl (Or.inr ⟨h, h'⟩))
        · exact Or.inr (Or.inr h')
        · exact Or.inl (Or.inr ⟨h', ht.2⟩)
    have hnull : volume ({1 / 3, 2 / 3} : Set ℝ) = 0 :=
      Set.Finite.measure_zero (Set.toFinite _) volume
    have p1 : ∫⁻ t in Ioo (0 : ℝ) (1 / 3), g t = ∫⁻ s in Ioo (0 : ℝ) 1, phiDensity ψ (c₁ s) * ‖deriv c₁ s‖ₑ := by
      refine utm_b_piece ψ (m := 3) (k := 0) (by norm_num) ?_ fun t ht => e1 t (Ioo_subset_Icc_self ht)
      ext y
      constructor
      · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨y / 3, ⟨by linarith, by linarith⟩, by ring⟩
    have p2 : ∫⁻ t in Ioo (1 / 3 : ℝ) (2 / 3), g t =
        ∫⁻ s in Ioo (0 : ℝ) 1, phiDensity ψ (c₂ s) * ‖deriv c₂ s‖ₑ := by
      refine utm_b_piece ψ (m := 3) (k := -1) (by norm_num) ?_ fun t ht => e2 t (Ioo_subset_Icc_self ht)
      ext y
      constructor
      · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(y + 1) / 3, ⟨by linarith, by linarith⟩, by ring⟩
    have p3 : ∫⁻ t in Ioo (2 / 3 : ℝ) 1, g t =
        ∫⁻ s in Ioo (0 : ℝ) 1, phiDensity ψ (c₃ s) * ‖deriv c₃ s‖ₑ := by
      refine utm_b_piece ψ (m := -3) (k := 3) (by norm_num) ?_ fun t ht => e3 t (Ioo_subset_Icc_self ht)
      ext y
      constructor
      · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
        exact ⟨by linarith, by linarith⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(3 - y) / 3, ⟨by linarith, by linarith⟩, by ring⟩
    calc phiLength ψ ⟨β₀, _⟩ = ∫⁻ t in Ioo (0 : ℝ) 1, g t := rfl
      _ ≤ ∫⁻ t in ((Ioo 0 (1 / 3) ∪ Ioo (1 / 3) (2 / 3)) ∪ Ioo (2 / 3) 1) ∪ {1 / 3, 2 / 3}, g t :=
          lintegral_mono_set hsub
      _ ≤ (∫⁻ t in (Ioo 0 (1 / 3) ∪ Ioo (1 / 3) (2 / 3)) ∪ Ioo (2 / 3) 1, g t) +
          ∫⁻ t in ({1 / 3, 2 / 3} : Set ℝ), g t := lintegral_union_le _ _ _
      _ = ∫⁻ t in (Ioo 0 (1 / 3) ∪ Ioo (1 / 3) (2 / 3)) ∪ Ioo (2 / 3) 1, g t := by
          rw [setLIntegral_measure_zero _ _ hnull, add_zero]
      _ ≤ (∫⁻ t in Ioo (0 : ℝ) (1 / 3), g t) + (∫⁻ t in Ioo (1 / 3 : ℝ) (2 / 3), g t) +
          ∫⁻ t in Ioo (2 / 3 : ℝ) 1, g t :=
          (lintegral_union_le _ _ _).trans (add_le_add_left (lintegral_union_le _ _ _) _)
      _ = _ := by rw [p1, p2, p3]

/-- **Companion of `lemma26_1`** (FIX-1 statement) for `S₀ = ℍ/Γ₀`: a homeomorphism homotopic to the identity
shortens horizontal arcs by at most `2M` (the image measured by its true length `phiLengthPathInv`).

Route: lift `α` to `α'` ([P3], [P4]); for every reparametrization `σ` of `f ∘ α` of finite length, its lift is
`F ∘ α' ∘ σ` for the `Γ₀`-commuting lift `F` of `f` ([P4]); join the end points by displacement curves ([P5]),
concatenate ([P6]) and compare with the lifted horizontal arc, which is shortest in `ℍ`
(`utm_arc_shortest_upperHalf`).

*Derivation note:* the book statement `lemma26_1` follows from this companion plus `thm22_3_classification`
for surfaces with hyperbolic universal covering (genus `> 1`); genus `0` and `1` need the `ℂ̂`/`ℂ` analogues
(`lemma26_1` now carries the hypothesis `g > 1`, 2026-10-12, user decision). -/
theorem lemma26_1_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    (f : S₀ ≃ₜ S₀) (hhom : ContinuousMap.Homotopic (f : C(S₀, S₀)) (ContinuousMap.id S₀))
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ (a b : S₀) (α : Path a b), IsHorizontalArcRS q α → phiLengthPath q α < ⊤ →
      phiLengthPath q α ≤ phiLengthPathInv q (α.map f.continuous) + ENNReal.ofReal (2 * M) := by
  obtain ⟨F, hFlift, hFΓ⟩ := utm_commuting_lift hp₀ f hhom
  obtain ⟨M₀, hM₀, hdisp⟩ := utm_displacement hq hp₀ F hFΓ
  have hψ := utm_liftQD_differentiableOn hq hp₀
  have hψne := utm_liftQD_ne hq hne hp₀
  refine ⟨M₀ + 1, by linarith, fun a b α hα hfin => ?_⟩
  -- lift `α`
  obtain ⟨τ₀, hτ₀⟩ := hp₀.2.2.1 a
  have hα0 : (α : C(unitInterval, S₀)) 0 = p₀ τ₀ := by
    rw [hτ₀]
    exact α.source
  set α' := hp₀.1.liftPath (α : C(unitInterval, S₀)) τ₀ hα0 with hα'def
  have hα'lift : ∀ t, p₀ (α' t) = α t := fun t => congrFun (hp₀.1.liftPath_lifts _ τ₀ hα0) t
  have hc := utm_horizontal_lift hq hp₀ α hα α' hα'lift
  obtain ⟨⟨Kc, hKc⟩, hlenα⟩ := utm_length_lift hq hp₀ α α' hα'lift hfin
  set c : ℝ → ℂ := fun t => (α' (Set.projIcc 0 1 zero_le_one t) : ℂ) with hcdef
  have hcc : ContinuousOn c (Icc 0 1) := hKc.continuousOn
  have hcH : c '' Icc 0 1 ⊆ upperHalf := by
    rintro _ ⟨t, -, rfl⟩
    exact (α' _).coe_im_pos
  have hc0 : c 0 = (α' 0 : ℂ) := by
    simp only [hcdef, Set.projIcc_left]
    rfl
  have hc1 : c 1 = (α' 1 : ℂ) := by
    simp only [hcdef, Set.projIcc_right]
    rfl
  -- every reparametrization of `f ∘ α`
  unfold phiLengthPathInv
  simp only [ENNReal.iInf_add]
  refine le_iInf fun σ => le_iInf fun hσ => le_iInf fun h0 => le_iInf fun h1 => le_iInf fun _ => ?_
  set γ := (α.map f.continuous).reparam σ hσ h0 h1 with hγdef
  by_cases hγfin : phiLengthPath q γ = ⊤
  · rw [hγfin, top_add]
    exact le_top
  set γ' : C(unitInterval, UpperHalfPlane) := F.comp (α'.comp ⟨σ, hσ⟩) with hγ'def
  have hγ'lift : ∀ t, p₀ (γ' t) = γ t := by
    intro t
    show p₀ (F (α' (σ t))) = f (α (σ t))
    rw [hFlift, hα'lift]
  obtain ⟨hK₂, hlenγ⟩ := utm_length_lift hq hp₀ γ γ' hγ'lift (lt_top_iff_ne_top.2 hγfin)
  set c₂ : ℝ → ℂ := fun t => (γ' (Set.projIcc 0 1 zero_le_one t) : ℂ) with hc₂def
  have hlenγ' : ∫⁻ t in Ioo (0 : ℝ) 1, phiDensity (utm_liftQD q p₀) (c₂ t) * ‖deriv c₂ t‖ₑ =
      phiLengthPath q γ := hlenγ
  obtain ⟨c₁, hc₁0, hc₁1, hc₁H, hc₁L, hc₁len⟩ := hdisp (α' 0)
  obtain ⟨c₃, hc₃0, hc₃1, hc₃H, hc₃L, hc₃len⟩ := hdisp (α' 1)
  have hc₂H : c₂ '' Icc 0 1 ⊆ upperHalf := by
    rintro _ ⟨t, -, rfl⟩
    exact (γ' _).coe_im_pos
  have h12 : c₁ 1 = c₂ 0 := by
    rw [hc₁1]
    simp only [hc₂def, hγ'def, Set.projIcc_left]
    show ((F (α' 0) : UpperHalfPlane) : ℂ) = ((F (α' (σ 0)) : UpperHalfPlane) : ℂ)
    rw [h0]
  have h23 : c₂ 1 = c₃ 1 := by
    rw [hc₃1]
    simp only [hc₂def, hγ'def, Set.projIcc_right]
    show ((F (α' (σ 1)) : UpperHalfPlane) : ℂ) = ((F (α' 1) : UpperHalfPlane) : ℂ)
    rw [h1]
  obtain ⟨β, hβH, hβa, hβb, hβlen⟩ :=
    utm_concat (utm_liftQD q p₀) hc₁L hK₂ hc₃L hc₁H hc₂H hc₃H h12 h23
  have hβa' : Tendsto β.toFun (𝓝[>] 0) (𝓝 (c 0)) := by
    rw [hc0, ← hc₁0]
    exact hβa
  have hβb' : Tendsto β.toFun (𝓝[<] 1) (𝓝 (c 1)) := by
    rw [hc1, ← hc₃0]
    exact hβb
  have hkey := utm_arc_shortest_upperHalf hψ hψne zero_lt_one hc hcc hcH β hβH hβa' hβb'
  calc phiLengthPath q α
      = ∫⁻ t in Ioo (0 : ℝ) 1, phiDensity (utm_liftQD q p₀) (c t) * ‖deriv c t‖ₑ := hlenα.symm
    _ ≤ phiLength (utm_liftQD q p₀) β := hkey
    _ ≤ _ := hβlen
    _ ≤ ENNReal.ofReal M₀ + phiLengthPath q γ + ENNReal.ofReal M₀ := by
        rw [hlenγ']
        exact add_le_add (add_le_add hc₁len le_rfl) hc₃len
    _ ≤ phiLengthPath q γ + ENNReal.ofReal (2 * (M₀ + 1)) := by
        rw [add_comm (ENNReal.ofReal M₀) (phiLengthPath q γ), add_assoc, ← ENNReal.ofReal_add hM₀ hM₀]
        gcongr
        linarith

/-- **Lemma 26.1** (26.8).  Let `S₀` be a closed Riemann surface, `f : S₀ → S₀` a homeomorphism
homotopic to the identity, `q ∈ Q(S₀)` not identically zero.  Then there is `M > 0` such that every
horizontal trajectory arc `α` of finite `q`-length satisfies `l_q(f(α)) ≥ l_q(α) - 2M`.

**Correction.**  The hypothesis `phiLengthPath q α < ⊤` was missing, and the statement was **false**:
`phiLengthPath` counts only Lipschitz chart pieces, so it depends on the parametrization; an arc
parametrized like `p + L√t` has length `⊤`, while a quasiconformal `f` homotopic to the identity (a
radial squaring) straightens it, so `l_q(f(α)) < ⊤` and `⊤ ≤ l_q(f(α)) + 2M` fails.

**Correction (2026-09-26).**  The image `f(α)` is measured by the true length `phiLengthPathInv` (the infimum
over reparametrizations) instead of `phiLengthPath`: a quasiconformal image is generally not Lipschitz
parametrized, so `phiLengthPath q (f ∘ α) = ⊤` on exactly the arcs of the averaging argument, and the
statement said nothing there.  The new statement is stronger (`phiLengthPathInv ≤ phiLengthPath`).

**Correction (2026-10-12, user decision).** The hypothesis g > 1 is added: Lemma 26.1 serves Theorem 26.2, which assumes genus g > 1 (book l.432). The proof goes through a hyperbolic uniformization, which a torus lacks. -/
theorem lemma26_1 [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (f : S₀ ≃ₜ S₀) (hhom : ContinuousMap.Homotopic (f : C(S₀, S₀)) (ContinuousMap.id S₀))
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (a b : S₀) (α : Path a b), IsHorizontalArcRS q α → phiLengthPath q α < ⊤ →
      phiLengthPath q α ≤ phiLengthPathInv q (α.map f.continuous) + ENNReal.ofReal (2 * M) := by
  obtain ⟨Γ₀, _p, _hΓ, _hfree, hp₀⟩ :=
    s22hg_exists_fuchsian_uniformization (S := S₀) hg hS
  exact lemma26_1_of_uniformization f hhom hq hne hp₀


/-! ## Part 3. Lemma 26.2 on `ℍ/Γ₀`: Lemma 26.1 + averaging (scout A's reduction) -/

/-- Monotonicity of `surfaceIntegral` off a set `E` that is null in every chart (scout A). -/
theorem utm_surfaceIntegral_mono_off {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    (q : S → ℂ → ℂ) {u w : S → ℂ → ℝ≥0∞} (E : Set S)
    (hE : ∀ x : S, volume (chartAt ℂ x '' (E ∩ (chartAt ℂ x).source)) = 0)
    (huw : ∀ x : S, ∀ p ∈ (chartAt ℂ x).source, p ∉ E → u x (chartAt ℂ x p) ≤ w x (chartAt ℂ x p)) :
    surfaceIntegral q u ≤ surfaceIntegral q w := by
  unfold surfaceIntegral
  refine iInf_mono fun x => iInf_mono fun P => iInf_mono fun hP => ENNReal.tsum_le_tsum fun i => ?_
  refine lintegral_mono_ae ?_
  have h1 : ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)), z ∈ chartAt ℂ (x i) '' P i :=
    ae_restrict_mem (hP.1 i).2
  have h2 : ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)),
      z ∉ chartAt ℂ (x i) '' (E ∩ (chartAt ℂ (x i)).source) :=
    ae_restrict_of_ae (compl_mem_ae_iff.2 (hE (x i)))
  filter_upwards [h1, h2] with z hz1 hz2
  obtain ⟨p, hpP, rfl⟩ := hz1
  have hps : p ∈ (chartAt ℂ (x i)).source := (hP.1 i).1 hpP
  have hpE : p ∉ E := fun h => hz2 ⟨p, ⟨h, hps⟩, rfl⟩
  exact mul_le_mul_left (huw (x i) p hps hpE) _

/-- **Lemma 26.2 from Lemma 26.1 (FIX-1) and the averaging** (scout A's `h26a_lemma26_2_core`): off the null set
`E`, `2L ≤ l(f(α_p)) + 2M`, so `(2L - 2M) ‖q‖ ≤ ∬ l(f(α_p)) dA_q = 2L ∬ λ_f dA_q` for every `L > M`; let
`L → ∞`. -/
theorem utm_lemma26_2_core [CompactSpace S₀] [Nonempty S₀] {f : S₀ ≃ₜ S₀} {q : S₀ → ℂ → ℂ}
    (hq : IsHolQuadDiff q) {M : ℝ} (hM : 0 < M)
    (hα : ∀ (a b : S₀) (α : Path a b), IsHorizontalArcRS q α → phiLengthPath q α < ⊤ →
      phiLengthPath q α ≤ phiLengthPathInv q (α.map f.continuous) + ENNReal.ofReal (2 * M))
    (hav : ∀ L : ℝ, 0 < L → ∃ (E : Set S₀) (α : S₀ → Σ a b : S₀, Path a b),
      (∀ x : S₀, volume (chartAt ℂ x '' (E ∩ (chartAt ℂ x).source)) = 0) ∧
      (∀ p, p ∉ E → IsHorizontalArcRS q (α p).2.2 ∧ p ∈ range (α p).2.2 ∧
        phiLengthPath q (α p).2.2 = ENNReal.ofReal (2 * L)) ∧
      surfaceIntegral q (fun x z => phiLengthPathInv q ((α ((chartAt ℂ x).symm z)).2.2.map f.continuous)) =
        ENNReal.ofReal (2 * L) * surfaceIntegral q (fun x z => ENNReal.ofReal (lambdaStretch q q f x z))) :
    quadDiffNorm q ≤ surfaceIntegral q fun x z => ENNReal.ofReal (lambdaStretch q q f x z) := by
  have hNt : quadDiffNorm q < ⊤ := s26_quadDiffNorm_lt_top hq
  -- the key inequality for every `L > M`
  have key : ∀ L : ℝ, M < L → ENNReal.ofReal (2 * L - 2 * M) * quadDiffNorm q ≤
      ENNReal.ofReal (2 * L) * surfaceIntegral q (fun x z => ENNReal.ofReal (lambdaStretch q q f x z)) := by
    intro L hL
    obtain ⟨E, α, hE, hαE, hid⟩ := hav L (lt_trans hM hL)
    have hpt : ∀ x : S₀, ∀ p ∈ (chartAt ℂ x).source, p ∉ E → ENNReal.ofReal (2 * L - 2 * M) ≤
        phiLengthPathInv q ((α ((chartAt ℂ x).symm (chartAt ℂ x p))).2.2.map f.continuous) := by
      intro x p hp hpE
      rw [(chartAt ℂ x).left_inv hp]
      obtain ⟨hh, -, hlen⟩ := hαE p hpE
      have h1 := hα _ _ (α p).2.2 hh (by rw [hlen]; exact ENNReal.ofReal_lt_top)
      rw [hlen] at h1
      rw [ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ 2 * M)]
      exact tsub_le_iff_right.2 h1
    have hmono := utm_surfaceIntegral_mono_off q (u := fun _ _ => ENNReal.ofReal (2 * L - 2 * M))
      (w := fun x z => phiLengthPathInv q ((α ((chartAt ℂ x).symm z)).2.2.map f.continuous)) E hE hpt
    rw [hid, s26w_surfaceIntegral_const q (by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; linarith)
      ENNReal.ofReal_ne_top] at hmono
    exact hmono
  -- let `L → ∞`
  by_contra hlt
  rw [not_le] at hlt
  have hIt := hlt.trans hNt
  have hNa := (ENNReal.ofReal_toReal hNt.ne).symm
  have hIb := (ENNReal.ofReal_toReal hIt.ne).symm
  have hb0 : 0 ≤ (surfaceIntegral q fun x z => ENNReal.ofReal (lambdaStretch q q f x z)).toReal :=
    ENNReal.toReal_nonneg
  have hab := (ENNReal.toReal_lt_toReal hIt.ne hNt.ne).2 hlt
  generalize (surfaceIntegral q fun x z => ENNReal.ofReal (lambdaStretch q q f x z)).toReal = b at hIb hb0 hab
  generalize (quadDiffNorm q).toReal = a at hNa hab
  have hab' : 0 < a - b := sub_pos.2 hab
  have ha0 : 0 < a := lt_of_le_of_lt hb0 hab
  have hMa : 0 ≤ M * a / (a - b) := div_nonneg (mul_nonneg hM.le ha0.le) hab'.le
  have hL : M < M * a / (a - b) + M + 1 := by linarith
  have h := key _ hL
  rw [hNa, hIb, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by linarith),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  have h2 : (M * a / (a - b) + M + 1) * (a - b) ≤ M * a := by nlinarith
  have e : M * a / (a - b) * (a - b) = M * a := div_mul_cancel₀ _ hab'.ne'
  nlinarith

/-- **Companion of `lemma26_2`** (26.10) for `S₀ = ℍ/Γ₀`: `∬ dA_q ≤ ∬ λ_f dA_q` for a quasiconformal `f ≃ id`.

*Derivation note:* the book statement `lemma26_2` follows from this companion plus `thm22_3_classification`
(a Fuchsian uniformization of the closed surface `S₀` of genus `g > 1`). -/
theorem lemma26_2_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ} (hg : 1 < g)
    (hS : HasGenus S₀ g) (f : S₀ ≃ₜ S₀) (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f : C(S₀, S₀)) (ContinuousMap.id S₀))
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0)
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) :
    quadDiffNorm q ≤ surfaceIntegral q fun x z => ENNReal.ofReal (lambdaStretch q q f x z) := by
  have : CompactSpace S₀ := hS.1
  have : Nonempty S₀ := ConnectedSpace.toNonempty
  obtain ⟨M, hM, hα⟩ := lemma26_1_of_uniformization f hhom hq hne hp₀
  exact utm_lemma26_2_core hq hM hα fun L hL => lemma26_2_averaging hg hS f hf hq hne hL

/-- **Lemma 26.2** (26.10).  Let `S₀` be a closed Riemann surface of genus `g > 1`, `f` a
quasiconformal self-map of `S₀` homotopic to the identity, and `q ≢ 0` a holomorphic quadratic
differential.  Then `∬_{S₀} dA_q ≤ ∬_{S₀} λ_f(p) dA_q`. -/
theorem lemma26_2 [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ} (hg : 1 < g)
    (hS : HasGenus S₀ g) (f : S₀ ≃ₜ S₀) (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f : C(S₀, S₀)) (ContinuousMap.id S₀))
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) :
    quadDiffNorm q ≤ surfaceIntegral q fun x z => ENNReal.ofReal (lambdaStretch q q f x z) := by
  obtain ⟨Γ₀, _p, _hΓ, _hfree, hp₀⟩ :=
    s22hg_exists_fuchsian_uniformization (S := S₀) hg hS
  exact lemma26_2_of_uniformization hg hS f hf hhom hq hne hp₀


/-! ## Part 4. Theorem 26.2, (26.15)–(26.16) and the extremality of Teichmüller maps, for `S₁ = ℍ/Γ₁`

The main inequality is used on the **target** `S₁` (with `q'` and `f* = f ∘ f₀⁻¹`), and the equality case ends
with `thm23_1_cor_of_uniformization` on `S₁`; so only `S₁` carries uniformization data. -/

/-- [P7, stub] **The inverse of a `K`-quasiconformal map of Riemann surfaces is `K`-quasiconformal.**

*Truth:* near each point of its domain, the local expression of `f⁻¹` at `y` is the inverse of a local expression
of `f` composed with conformal chart transitions (`thm7_2_inv`, `s23_c1_transition_isKQC`), and it is injective on
its open domain, so it is `K`-q.c. there (`s23_lg`). -/
theorem utm_isKQCRS_symm [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ ≃ₜ S₁} {K : ℝ}
    (hf : IsKQCRS f K) : IsKQCRS f.symm K := by
  exact s29_m_isKQCRS_symm hf

/-- **Weighted assembly over two chart partitions** (the `≤` form of `s26w_partition_sum_eq`, with a weight `v`
on the target): if on every chart piece `A` (with `F(A)` in a chart) the `v`-weighted `q'`-area of `F(A)` is at most
the `u`-weighted `q`-area of `A`, then so are the partition sums (refine by `A_{ij} = P_i ∩ F⁻¹ Q_j`). -/
theorem utm_d_partition_sum_le {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {Y : Type*}
    [TopologicalSpace Y] [ChartedSpace ℂ Y] (F : X ≃ₜ Y) (q : X → ℂ → ℂ) (q' : Y → ℂ → ℂ)
    (u : X → ℂ → ℝ≥0∞) (v : Y → ℂ → ℝ≥0∞)
    (hloc : ∀ (x : X) (y : Y) (A : Set X), A ⊆ (chartAt ℂ x).source → F '' A ⊆ (chartAt ℂ y).source →
      MeasurableSet (chartAt ℂ x '' A) → MeasurableSet (chartAt ℂ y '' (F '' A)) →
      ∫⁻ w in chartAt ℂ y '' (F '' A), v y w * ENNReal.ofReal ‖q' y w‖ ≤
        ∫⁻ z in chartAt ℂ x '' A, u x z * ENNReal.ofReal ‖q x z‖)
    {x : ℕ → X} {P : ℕ → Set X} (hP : IsChartPartition X x P) {y : ℕ → Y} {Q : ℕ → Set Y}
    (hQ : IsChartPartition Y y Q) :
    ∑' j, ∫⁻ w in chartAt ℂ (y j) '' Q j, v (y j) w * ENNReal.ofReal ‖q' (y j) w‖ ≤
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, u (x i) z * ENNReal.ofReal ‖q (x i) z‖ := by
  obtain ⟨hPsm, hPd, hPc⟩ := hP
  obtain ⟨hQsm, hQd, hQc⟩ := hQ
  set A : ℕ → ℕ → Set X := fun i j => P i ∩ F ⁻¹' Q j with hAdef
  have hFA : ∀ i j, F '' A i j = Q j ∩ F.symm ⁻¹' P i := by
    intro i j
    rw [hAdef]
    dsimp only
    rw [image_inter_preimage, F.image_eq_preimage_symm, inter_comm]
  have hAs : ∀ i j, A i j ⊆ (chartAt ℂ (x i)).source := fun i j => inter_subset_left.trans (hPsm i).1
  have hFAs : ∀ i j, F '' A i j ⊆ (chartAt ℂ (y j)).source := fun i j => by
    rw [hFA]; exact inter_subset_left.trans (hQsm j).1
  have hAm : ∀ i j, MeasurableSet (chartAt ℂ (x i) '' A i j) := fun i j =>
    s26w_measurableSet_chart_piece F.continuous (x i) (y j) (hPsm i).1 (hQsm j).1 (hPsm i).2 (hQsm j).2
  have hFAm : ∀ i j, MeasurableSet (chartAt ℂ (y j) '' (F '' A i j)) := fun i j => by
    rw [hFA]
    exact s26w_measurableSet_chart_piece F.symm.continuous (y j) (x i) (hQsm j).1 (hPsm i).1
      (hQsm j).2 (hPsm i).2
  have hsrc : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i, u (x i) z * ENNReal.ofReal ‖q (x i) z‖ =
      ∑' j, ∫⁻ z in chartAt ℂ (x i) '' A i j, u (x i) z * ENNReal.ofReal ‖q (x i) z‖ := by
    intro i
    have hU : chartAt ℂ (x i) '' P i = ⋃ j, chartAt ℂ (x i) '' A i j := by
      rw [← image_iUnion]
      congr 1
      rw [hAdef]
      dsimp only
      rw [← inter_iUnion, ← preimage_iUnion, hQc, preimage_univ, inter_univ]
    rw [hU, lintegral_iUnion (hAm i)]
    intro j j' hjj'
    exact s26w_disjoint_image (chartAt ℂ (x i)).injOn (hAs i j) (hAs i j')
      (Disjoint.mono inter_subset_right inter_subset_right ((hQd hjj').preimage F))
  have htgt : ∀ j, ∫⁻ w in chartAt ℂ (y j) '' Q j, v (y j) w * ENNReal.ofReal ‖q' (y j) w‖ =
      ∑' i, ∫⁻ w in chartAt ℂ (y j) '' (F '' A i j), v (y j) w * ENNReal.ofReal ‖q' (y j) w‖ := by
    intro j
    have hU : chartAt ℂ (y j) '' Q j = ⋃ i, chartAt ℂ (y j) '' (F '' A i j) := by
      rw [← image_iUnion]
      congr 1
      simp only [hFA]
      rw [← inter_iUnion, ← preimage_iUnion, hPc, preimage_univ, inter_univ]
    rw [hU, lintegral_iUnion (hFAm · j)]
    intro i i' hii'
    exact s26w_disjoint_image (chartAt ℂ (y j)).injOn (hFAs i j) (hFAs i' j)
      (by
        rw [hFA, hFA]
        exact Disjoint.mono inter_subset_right inter_subset_right ((hPd hii').preimage F.symm))
  simp only [htgt, hsrc]
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun i => ENNReal.tsum_le_tsum fun j => ?_
  exact hloc (x i) (y j) (A i j) (hAs i j) (hFAs i j) (hAm i j) (hFAm i j)

/-- The weighted surface integral on the target is at most any partition sum on the source, under the local
hypothesis of `utm_d_partition_sum_le` (a chart partition of the compact target exists). -/
theorem utm_d_surfaceIntegral_le {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {Y : Type*}
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [CompactSpace Y] [Nonempty Y] (F : X ≃ₜ Y) (q : X → ℂ → ℂ)
    (q' : Y → ℂ → ℂ) (u : X → ℂ → ℝ≥0∞) (v : Y → ℂ → ℝ≥0∞)
    (hloc : ∀ (x : X) (y : Y) (A : Set X), A ⊆ (chartAt ℂ x).source → F '' A ⊆ (chartAt ℂ y).source →
      MeasurableSet (chartAt ℂ x '' A) → MeasurableSet (chartAt ℂ y '' (F '' A)) →
      ∫⁻ w in chartAt ℂ y '' (F '' A), v y w * ENNReal.ofReal ‖q' y w‖ ≤
        ∫⁻ z in chartAt ℂ x '' A, u x z * ENNReal.ofReal ‖q x z‖)
    {x : ℕ → X} {P : ℕ → Set X} (hP : IsChartPartition X x P) :
    surfaceIntegral q' v ≤ ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, u (x i) z * ENNReal.ofReal ‖q (x i) z‖ := by
  obtain ⟨y, Q, hQ⟩ := s26_exists_chartPartition' (S := Y)
  unfold surfaceIntegral
  exact iInf_le_of_le y (iInf_le_of_le Q (iInf_le_of_le hQ (utm_d_partition_sum_le F q q' u v hloc hP hQ)))

/-- **Every partition sum computes the norm of the target differential**, under the hypothesis of
`s26w_partition_sum_eq`: `∑ᵢ ∬_{φᵢ(Pᵢ)} u |q| = ‖q'‖` for every chart partition `P` of the source. -/
theorem utm_d_sum_eq_norm {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {Y : Type*}
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [CompactSpace Y] [Nonempty Y] (F : X ≃ₜ Y) (q : X → ℂ → ℂ)
    (q' : Y → ℂ → ℂ) (u : X → ℂ → ℝ≥0∞)
    (hloc : ∀ (x : X) (y : Y) (A : Set X), A ⊆ (chartAt ℂ x).source → F '' A ⊆ (chartAt ℂ y).source →
      MeasurableSet (chartAt ℂ x '' A) → MeasurableSet (chartAt ℂ y '' (F '' A)) →
      ∫⁻ w in chartAt ℂ y '' (F '' A), ENNReal.ofReal ‖q' y w‖ =
        ∫⁻ z in chartAt ℂ x '' A, u x z * ENNReal.ofReal ‖q x z‖)
    {x : ℕ → X} {P : ℕ → Set X} (hP : IsChartPartition X x P) :
    ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, u (x i) z * ENNReal.ofReal ‖q (x i) z‖ = quadDiffNorm q' := by
  obtain ⟨y₀, Q₀, hQ₀⟩ := s26_exists_chartPartition' (S := Y)
  unfold quadDiffNorm surfaceIntegral
  refine le_antisymm (le_iInf fun y => le_iInf fun Q => le_iInf fun hQ => ?_) ?_
  · exact (s26w_partition_sum_eq F q q' u hloc hP hQ).ge
  · exact iInf_le_of_le y₀ (iInf_le_of_le Q₀ (iInf_le_of_le hQ₀
      (s26w_partition_sum_eq F q q' u hloc hP hQ₀).le))

/-- **The first derivatives of a Teichmüller map in a chart pair.**  At a point `z` of the chart at `x` where
`q_x(z) ≠ 0`, with image in the chart at `y`, the expression `g = φ_y ∘ f₀ ∘ φ_x⁻¹` is real differentiable, and with
`a² = q_x(z)`, `b² = q'_y(g z)` (`a, b ≠ 0`, the derivatives of the natural parameters composed with the chart
transitions): `∂g(z) = b⁻¹ a/(1 - k)`, `∂̄g(z) = b⁻¹ k ā/(1 - k)` (the proof of `s26w_teich_jacobian`). -/
theorem utm_d_teich_deriv [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]
    {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k)
    (x : S₀) (y : S₁) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hzy : f₀ ((chartAt ℂ x).symm z) ∈ (chartAt ℂ y).source) (hq0 : q x z ≠ 0) :
    DifferentiableAt ℝ (fun w => chartAt ℂ y (f₀ ((chartAt ℂ x).symm w))) z ∧
      ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ q x z = a ^ 2 ∧ q' y (chartAt ℂ y (f₀ ((chartAt ℂ x).symm z))) = b ^ 2 ∧
        dz (fun w => chartAt ℂ y (f₀ ((chartAt ℂ x).symm w))) z = b⁻¹ * (1 / (1 - k) * a) ∧
        dzbar (fun w => chartAt ℂ y (f₀ ((chartAt ℂ x).symm w))) z = b⁻¹ * (k / (1 - k) * conj a) := by
  set g : ℂ → ℂ := fun w => chartAt ℂ y (f₀ ((chartAt ℂ x).symm w)) with hg
  set p := (chartAt ℂ x).symm z with hp
  have hreg : IsRegularPoint q p := (s26u_isRegularPoint_iff hf₀.initial x hz).2 hq0
  obtain ⟨-, ζ, ζ', hζ, hζ', hrel⟩ := hf₀.regular p hreg
  set τ := chartTransition p x with hτ
  obtain ⟨hτd, -⟩ := s23_transition p x hz (mem_chart_source ℂ p)
  have hτz : τ z = chartAt ℂ p p := rfl
  have hζd : DifferentiableAt ℂ ζ (τ z) := by rw [hτz]; exact hζ.1.differentiableAt
  set A := ζ ∘ τ with hA
  have hAd : DifferentiableAt ℂ A z := hζd.comp z hτd
  have hqA : q x z = deriv A z ^ 2 := by
    rw [s26u_law hf₀.initial x p hz (mem_chart_source ℂ p), hA, deriv_comp z hζd hτd, mul_pow]
    congr 1
    rw [hτz]
    exact hζ.2.2.2.self_of_nhds.symm
  set b := g z with hb
  have hbt : b ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hzy
  have hbs : (chartAt ℂ y).symm b = f₀ p := (chartAt ℂ y).left_inv hzy
  have hbs' : (chartAt ℂ y).symm b ∈ (chartAt ℂ (f₀ p)).source := by
    rw [hbs]; exact mem_chart_source ℂ (f₀ p)
  set σ := chartTransition (f₀ p) y with hσ
  have hσd' : deriv σ b ≠ 0 := (s23_transition (f₀ p) y hbt hbs').2
  have hσb : σ b = chartAt ℂ (f₀ p) (f₀ p) := by simp only [hσ, chartTransition, hbs]
  have hσan : AnalyticAt ℂ σ b :=
    DifferentiableOn.analyticAt (fun w hw => (s23_transition (f₀ p) y hw.1 hw.2).1.differentiableWithinAt)
      (((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ (f₀ p)).open_source).mem_nhds ⟨hbt, hbs'⟩)
  have hζ'an : AnalyticAt ℂ ζ' (σ b) := by rw [hσb]; exact hζ'.1
  set B := ζ' ∘ σ with hB
  have hBan : AnalyticAt ℂ B b := hζ'an.comp hσan
  have hB' : deriv B b ≠ 0 := by
    rw [hB, deriv_comp b hζ'an.differentiableAt hσan.differentiableAt, hσb]
    exact mul_ne_zero hζ'.2.2.1 hσd'
  have hqB : q' y b = deriv B b ^ 2 := by
    rw [s26u_law hf₀.terminal y (f₀ p) hbt hbs', hB, deriv_comp b hζ'an.differentiableAt
      hσan.differentiableAt, mul_pow]
    congr 1
    change q' (f₀ p) (σ b) = _
    rw [hσb]
    exact hζ'.2.2.2.self_of_nhds.symm
  have hBs : HasStrictDerivAt B (deriv B b) b := hBan.hasStrictDerivAt
  set Binv := hBs.localInverse B (deriv B b) b hB' with hBinv_def
  have hBinv : HasStrictDerivAt Binv (deriv B b)⁻¹ (B b) := hBs.to_localInverse hB'
  have hleft : ∀ᶠ v in 𝓝 b, Binv (B v) = v := hBs.eventually_left_inverse hB'
  have hgc : ContinuousAt g z := by
    have h1 : ContinuousAt (fun w => f₀ ((chartAt ℂ x).symm w)) z :=
      f₀.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)
    exact ContinuousAt.comp (g := chartAt ℂ y) (f := fun w => f₀ ((chartAt ℂ x).symm w))
      ((chartAt ℂ y).continuousAt hzy) h1
  have hτc : Tendsto τ (𝓝 z) (𝓝 (chartAt ℂ p p)) := by
    rw [← hτz]; exact hτd.continuousAt.tendsto
  have hN1 : {w | w ∈ (chartAt ℂ x).target ∧ (chartAt ℂ x).symm w ∈ (chartAt ℂ p).source} ∈ 𝓝 z :=
    ((chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ p).open_source).mem_nhds
      ⟨hz, mem_chart_source ℂ p⟩
  have hN2 : ∀ᶠ w in 𝓝 z, f₀ ((chartAt ℂ x).symm w) ∈ (chartAt ℂ y).source :=
    (f₀.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)).preimage_mem_nhds
      ((chartAt ℂ y).open_source.mem_nhds hzy)
  have hBg : ∀ᶠ w in 𝓝 z, B (g w) = teichStretch k (A w) := by
    filter_upwards [hτc.eventually hrel, hN1, hN2] with w h1 h2 h3
    simp only [hB, hA, Function.comp_apply]
    rw [← h1]
    congr 1
    simp only [hσ, hg, hτ, chartTransition, localMapExpr]
    rw [(chartAt ℂ y).left_inv h3, (chartAt ℂ p).left_inv h2.2]
  have hgeq : g =ᶠ[𝓝 z] Binv ∘ (teichStretch k ∘ A) := by
    filter_upwards [hBg, hgc.eventually hleft] with w h1 h2
    simp only [Function.comp_apply]
    rw [← h1, h2]
  obtain ⟨hSd, hSdz, hSdzbar⟩ := s26w_dz_teichStretch k (A z)
  have hFd : DifferentiableAt ℝ (teichStretch k ∘ A) z := hSd.comp z (hAd.restrictScalars ℝ)
  have hFz : (teichStretch k ∘ A) z = B b := (hBg.self_of_nhds).symm
  have hBinvd : DifferentiableAt ℂ Binv ((teichStretch k ∘ A) z) := by
    rw [hFz]; exact hBinv.hasDerivAt.differentiableAt
  have hdBinv : deriv Binv ((teichStretch k ∘ A) z) = (deriv B b)⁻¹ := by
    rw [hFz]; exact hBinv.hasDerivAt.deriv
  obtain ⟨hSA1, hSA2⟩ := eq6_4 hAd hSd
  obtain ⟨hall1, hall2⟩ := eq6_5 hFd hBinvd
  have hgd : DifferentiableAt ℝ g z :=
    ((hBinvd.restrictScalars ℝ).comp z hFd).congr_of_eventuallyEq hgeq
  have hdz : dz g z = (deriv B b)⁻¹ * (1 / (1 - k) * deriv A z) := by
    unfold dz
    rw [hgeq.fderiv_eq]
    rw [← dz, hall1, hdBinv, hSA1, hSdz]
  have hdzbar : dzbar g z = (deriv B b)⁻¹ * (k / (1 - k) * conj (deriv A z)) := by
    unfold dzbar
    rw [hgeq.fderiv_eq]
    rw [← dzbar, hall2, hdBinv, hSA2, hSdzbar]
  have hA0 : deriv A z ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hqA
    exact hq0 hqA
  exact ⟨hgd, deriv A z, deriv B b, hA0, hB', hqA, hqB, hdz, hdzbar⟩
/-- **The stretching function through a Teichmüller map** (the book's `λ_{f*}(f₀ p) = λ_f(p)/K₀`, one inequality): at a
point `z` of the chart at `x` where `q_x(z) ≠ 0`, with `f₀(φ_x⁻¹ z)` in the chart at `y` and `w = φ_y(f₀(φ_x⁻¹ z))`,
`K₀ λ_{q',q',f∘f₀⁻¹}(y, w) ≤ λ_{q,q',f}(x, z)`.  The expression of `f ∘ f₀⁻¹` composed with `g = φ_y ∘ f₀ ∘ φ_x⁻¹` is
the expression of `f`; if the former is differentiable at `w`, the chain rule with `∂g = b⁻¹ a/(1-k)`,
`∂̄g = b⁻¹ k ā/(1-k)` (`utm_d_teich_deriv`) gives equality, and otherwise the left side is `0`. -/
theorem utm_d_lambda_transfer [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]
    {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k)
    (f : S₀ ≃ₜ S₁) (x : S₀) (y : S₁) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target)
    (hzy : f₀ ((chartAt ℂ x).symm z) ∈ (chartAt ℂ y).source) (hq0 : q x z ≠ 0) :
    (1 + k) / (1 - k) * lambdaStretch q' q' (f₀.symm.trans f) y (chartAt ℂ y (f₀ ((chartAt ℂ x).symm z))) ≤
      lambdaStretch q q' f x z := by
  obtain ⟨hgd, a, b, ha0, hb0, hqa, hqb, hdz, hdzbar⟩ := utm_d_teich_deriv hf₀ x y hz hzy hq0
  set g : ℂ → ℂ := fun w => chartAt ℂ y (f₀ ((chartAt ℂ x).symm w)) with hg
  set p := (chartAt ℂ x).symm z with hp
  set w₀ := g z with hw₀
  have hw₀s : (chartAt ℂ y).symm w₀ = f₀ p := (chartAt ℂ y).left_inv hzy
  have hfs : (f₀.symm.trans f) ((chartAt ℂ y).symm w₀) = f p := by
    rw [hw₀s, Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
  set Gs : ℂ → ℂ := fun v => chartAt ℂ (f p) (f (f₀.symm ((chartAt ℂ y).symm v))) with hGs
  set G : ℂ → ℂ := fun v => chartAt ℂ (f p) (f ((chartAt ℂ x).symm v)) with hG
  have hLs : lambdaStretch q' q' (f₀.symm.trans f) y w₀ = lambdaStretchPlane (q' y) (q' (f p)) Gs w₀ := by
    unfold lambdaStretch localMapExprAt
    rw [hfs]
    rfl
  have hL : lambdaStretch q q' f x z = lambdaStretchPlane (q x) (q' (f p)) G z := rfl
  have hN2 : ∀ᶠ v in 𝓝 z, f₀ ((chartAt ℂ x).symm v) ∈ (chartAt ℂ y).source :=
    (f₀.continuous.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz)).preimage_mem_nhds
      ((chartAt ℂ y).open_source.mem_nhds hzy)
  have hGeq : G =ᶠ[𝓝 z] Gs ∘ g := by
    filter_upwards [hN2] with v hv
    simp only [hG, hGs, hg, Function.comp_apply, (chartAt ℂ y).left_inv hv, Homeomorph.symm_apply_apply]
  have hnn : 0 ≤ lambdaStretchPlane (q x) (q' (f p)) G z := by
    unfold lambdaStretchPlane
    positivity
  rw [hLs, hL]
  by_cases hd : DifferentiableAt ℝ Gs w₀
  · have hGz : G z = Gs w₀ := hGeq.self_of_nhds
    obtain ⟨e1, e2⟩ := eq6_3 hgd
    have hdzG : dz G z = dz Gs w₀ * dz g z + dzbar Gs w₀ * conj (dzbar g z) := by
      rw [show dz G z = dz (Gs ∘ g) z by unfold dz; rw [hGeq.fderiv_eq], eq6_2_dz_comp hgd hd, ← e2]
    have hdzbarG : dzbar G z = dz Gs w₀ * dzbar g z + dzbar Gs w₀ * conj (dz g z) := by
      rw [show dzbar G z = dzbar (Gs ∘ g) z by unfold dzbar; rw [hGeq.fderiv_eq], eq6_2_dzbar_comp hgd hd,
        ← e1]
    set α := dz Gs w₀ with hα
    set β := dzbar Gs w₀ with hβ
    set A : ℂ := (‖a‖ : ℂ) with hA
    set B : ℂ := (‖b‖ : ℂ) with hB
    have hA0 : A ≠ 0 := by rw [hA]; exact_mod_cast norm_ne_zero_iff.2 ha0
    have hB0 : B ≠ 0 := by rw [hB]; exact_mod_cast norm_ne_zero_iff.2 hb0
    have hca : conj a = A ^ 2 / a := by
      rw [eq_div_iff ha0, hA, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    have hcb : conj b = B ^ 2 / b := by
      rw [eq_div_iff hb0, hB, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    have hna : ((‖a ^ 2‖ : ℝ) : ℂ) = A ^ 2 := by rw [hA, norm_pow]; push_cast; ring
    have hnb : ((‖b ^ 2‖ : ℝ) : ℂ) = B ^ 2 := by rw [hB, norm_pow]; push_cast; ring
    have h1k : (1 : ℂ) - k ≠ 0 := by
      have : (1 - k : ℝ) ≠ 0 := by linarith [hf₀.k_lt_one]
      exact_mod_cast this
    have hkey : dz G z + dzbar G z * (q x z / ((‖q x z‖ : ℝ) : ℂ)) =
        (((1 + k) / (1 - k) : ℝ) : ℂ) * (a / b) * (α + β * (q' y w₀ / ((‖q' y w₀‖ : ℝ) : ℂ))) := by
      rw [hdzG, hdzbarG, hdz, hdzbar, hqa, hqb, hna, hnb]
      simp only [map_mul, map_div₀, map_inv₀, map_one, map_sub, Complex.conj_ofReal]
      rw [Complex.conj_conj, hca, hcb]
      push_cast
      field_simp
      ring
    have hK0 : 0 ≤ (1 + k) / (1 - k) := div_nonneg (by linarith [hf₀.k_nonneg]) (by linarith [hf₀.k_lt_one])
    have hsa : Real.sqrt ‖q x z‖ = ‖a‖ := by rw [hqa, norm_pow, Real.sqrt_sq (norm_nonneg _)]
    have hsb : Real.sqrt ‖q' y w₀‖ = ‖b‖ := by rw [hqb, norm_pow, Real.sqrt_sq (norm_nonneg _)]
    have ha' : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha0
    have hb' : ‖b‖ ≠ 0 := norm_ne_zero_iff.2 hb0
    refine le_of_eq ?_
    unfold lambdaStretchPlane
    rw [hGz, hkey, hsa, hsb, norm_mul, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hK0,
      ← hα, ← hβ]
    field_simp
  · have h0 : fderiv ℝ Gs w₀ = 0 := fderiv_zero_of_not_differentiableAt hd
    have hdz0 : dz Gs w₀ = 0 := by simp [dz, h0]
    have hdzbar0 : dzbar Gs w₀ = 0 := by simp [dzbar, h0]
    have hz0 : lambdaStretchPlane (q' y) (q' (f p)) Gs w₀ = 0 := by
      unfold lambdaStretchPlane
      rw [hdz0, hdzbar0]
      simp
    rw [hz0, mul_zero]
    exact hnn
/-- **A Teichmüller map multiplies `q`-areas by `K₀`, weighted form** (`s26w_teich_piece` with a weight `h` on the
target): for a piece `A` in the chart at `x` with `f₀(A)` in the chart at `y` and `g = φ_y ∘ f₀ ∘ φ_x⁻¹`,
`∬_{φ_y(f₀ A)} h |q'_y| = ∬_{φ_x(A)} h(g) K₀ |q_x|` (change of variables off the countable zero set of `q_x`). -/
theorem utm_d_teich_piece_w [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]
    {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k)
    (x : S₀) (y : S₁) (A : Set S₀) (hA : A ⊆ (chartAt ℂ x).source) (hFA : f₀ '' A ⊆ (chartAt ℂ y).source)
    (hAm : MeasurableSet (chartAt ℂ x '' A)) (h : ℂ → ℝ≥0∞) :
    ∫⁻ w in chartAt ℂ y '' (f₀ '' A), h w * ENNReal.ofReal ‖q' y w‖ =
      ∫⁻ z in chartAt ℂ x '' A, h (chartAt ℂ y (f₀ ((chartAt ℂ x).symm z))) *
        (ENNReal.ofReal ((1 + k) / (1 - k)) * ENNReal.ofReal ‖q x z‖) := by
  set φ := chartAt ℂ x with hφ
  set ψ := chartAt ℂ y with hψ
  set g : ℂ → ℂ := fun w => ψ (f₀ (φ.symm w)) with hg
  set s := φ '' A with hs
  set Z := {z | z ∈ φ.target ∧ q x z = 0} with hZ
  have hZc : Z.Countable := s26u_zeros_countable hf₀.initial hf₀.initial_ne x
  have hZ0 : volume Z = 0 := hZc.measure_zero _
  set s' := s \ Z with hs'
  have hs'm : MeasurableSet s' := hAm.diff hZc.measurableSet
  have himg : ψ '' (f₀ '' A) = g '' s := by
    rw [hs, image_image, image_image]
    refine image_congr fun a ha => ?_
    simp only [hg, φ.left_inv (hA ha)]
  have hpt : ∀ z ∈ s', z ∈ φ.target ∧ f₀ (φ.symm z) ∈ ψ.source ∧ q x z ≠ 0 := by
    rintro z ⟨⟨a, ha, rfl⟩, hzZ⟩
    have hl : φ.symm (φ a) = a := φ.left_inv (hA ha)
    refine ⟨φ.map_source (hA ha), by rw [hl]; exact hFA ⟨a, ha, rfl⟩, fun h0 => hzZ ⟨φ.map_source (hA ha), h0⟩⟩
  have hjac := fun z (hz : z ∈ s') =>
    s26w_teich_jacobian hf₀ x y (hpt z hz).1 (hpt z hz).2.1 (hpt z hz).2.2
  have hinj : InjOn g s := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h
    have h' : ψ (f₀ a) = ψ (f₀ b) := by
      simp only [hg, φ.left_inv (hA ha), φ.left_inv (hA hb)] at h
      exact h
    have h'' := f₀.injective (ψ.injOn (hFA ⟨a, ha, rfl⟩) (hFA ⟨b, hb, rfl⟩) h')
    rw [h'']
  have hs's : s' ⊆ s := sdiff_subset
  have hsrc_ae : s' =ᵐ[volume] s := sdiff_ae_eq_self.2 (measure_mono_null inter_subset_right hZ0)
  have htgt_ae : g '' s' =ᵐ[volume] g '' s := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [sdiff_eq_empty.2 (image_mono hs's), measure_empty]
    · refine measure_mono_null (t := g '' (s ∩ Z)) ?_ ((hZc.mono inter_subset_right).image g |>.measure_zero _)
      rintro _ ⟨⟨z, hz, rfl⟩, hz'⟩
      refine ⟨z, ⟨hz, ?_⟩, rfl⟩
      by_contra hzZ
      exact hz' ⟨z, ⟨hz, hzZ⟩, rfl⟩
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs'm
    (fun z hz => (hjac z hz).1.hasFDerivAt.hasFDerivWithinAt) (hinj.mono hs's)
    (fun w => h w * ENNReal.ofReal ‖q' y w‖)
  rw [himg, ← setLIntegral_congr htgt_ae, hcv, ← setLIntegral_congr hsrc_ae]
  refine setLIntegral_congr_fun hs'm fun z hz => ?_
  obtain ⟨hd, hJ0, hJ⟩ := hjac z hz
  have e : (fderiv ℝ g z).det = jacobian g z := det_fderiv_eq_jacobian hd
  have hK : 0 ≤ (1 + k) / (1 - k) := by
    have := hf₀.k_nonneg
    have := hf₀.k_lt_one
    exact div_nonneg (by linarith) (by linarith)
  have e2 : ENNReal.ofReal (jacobian g z) * ENNReal.ofReal ‖q' y (g z)‖ =
      ENNReal.ofReal ((1 + k) / (1 - k)) * ENNReal.ofReal ‖q x z‖ := by
    rw [← ENNReal.ofReal_mul hJ0, ← ENNReal.ofReal_mul hK]
    exact congrArg ENNReal.ofReal hJ
  rw [e, abs_of_nonneg hJ0, ← e2]
  ring

/-- `λ ≥ 0`. -/
theorem utm_d_lambdaStretch_nonneg (q : S₀ → ℂ → ℂ) (q' : S₁ → ℂ → ℂ) (f : S₀ → S₁) (x : S₀) (z : ℂ) :
    0 ≤ lambdaStretch q q' f x z := by
  unfold lambdaStretch lambdaStretchPlane
  positivity

/-- **The λ-integral through a Teichmüller map, piecewise**: for a piece `A` in the chart at `x` with `f₀(A)` in the
chart at `y`, `∬_{φ_y(f₀ A)} λ_{f∘f₀⁻¹} |q'_y| ≤ ∬_{φ_x(A)} λ_f |q_x|` (`utm_d_teich_piece_w` and
`utm_d_lambda_transfer` off the zeros of `q_x`). -/
theorem utm_d_lambda_piece [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]
    {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k)
    (f : S₀ ≃ₜ S₁) (x : S₀) (y : S₁) (A : Set S₀) (hA : A ⊆ (chartAt ℂ x).source)
    (hFA : f₀ '' A ⊆ (chartAt ℂ y).source) (hAm : MeasurableSet (chartAt ℂ x '' A)) :
    ∫⁻ w in chartAt ℂ y '' (f₀ '' A),
        ENNReal.ofReal (lambdaStretch q' q' (f₀.symm.trans f) y w) * ENNReal.ofReal ‖q' y w‖ ≤
      ∫⁻ z in chartAt ℂ x '' A, ENNReal.ofReal (lambdaStretch q q' f x z) * ENNReal.ofReal ‖q x z‖ := by
  rw [utm_d_teich_piece_w hf₀ x y A hA hFA hAm
    (fun w => ENNReal.ofReal (lambdaStretch q' q' (f₀.symm.trans f) y w))]
  refine lintegral_mono_ae ?_
  have hZ0 : volume {z | z ∈ (chartAt ℂ x).target ∧ q x z = 0} = 0 :=
    (s26u_zeros_countable hf₀.initial hf₀.initial_ne x).measure_zero _
  filter_upwards [ae_restrict_mem hAm, ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hZ0)] with z hzA hzZ
  obtain ⟨a, ha, rfl⟩ := hzA
  have hzt : chartAt ℂ x a ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source (hA ha)
  have hzy : f₀ ((chartAt ℂ x).symm (chartAt ℂ x a)) ∈ (chartAt ℂ y).source := by
    rw [(chartAt ℂ x).left_inv (hA ha)]
    exact hFA ⟨a, ha, rfl⟩
  have hq0 : q x (chartAt ℂ x a) ≠ 0 := fun h0 => hzZ ⟨hzt, h0⟩
  have h := utm_d_lambda_transfer hf₀ f x y hzt hzy hq0
  have hK : 0 ≤ (1 + k) / (1 - k) := by
    have := hf₀.k_nonneg
    have := hf₀.k_lt_one
    exact div_nonneg (by linarith) (by linarith)
  calc ENNReal.ofReal (lambdaStretch q' q' (f₀.symm.trans f) y
          (chartAt ℂ y (f₀ ((chartAt ℂ x).symm (chartAt ℂ x a))))) *
        (ENNReal.ofReal ((1 + k) / (1 - k)) * ENNReal.ofReal ‖q x (chartAt ℂ x a)‖)
      = ENNReal.ofReal ((1 + k) / (1 - k) * lambdaStretch q' q' (f₀.symm.trans f) y
          (chartAt ℂ y (f₀ ((chartAt ℂ x).symm (chartAt ℂ x a))))) * ENNReal.ofReal ‖q x (chartAt ℂ x a)‖ := by
        rw [ENNReal.ofReal_mul hK]
        ring
    _ ≤ ENNReal.ofReal (lambdaStretch q q' f x (chartAt ℂ x a)) * ENNReal.ofReal ‖q x (chartAt ℂ x a)‖ :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal h) le_rfl

/-- A quasiconformal map with `K[h] ≤ K`, `K ≥ 1`, is `K`-quasiconformal (Theorem 10.1 in every chart; the case
`K = 1` is `utm_isKQCRS_one_of_maxDil`). -/
theorem utm_d_isKQCRS_of_maxDil {h : S₀ ≃ₜ S₁} (hh : IsQCRS h) {K : ℝ} (hK : 1 ≤ K)
    (hle : maxDilatationRS h ≤ ENNReal.ofReal K) : IsKQCRS h K := by
  obtain ⟨K₁, -, hK₁⟩ := hh
  refine ⟨hK, fun x => ?_⟩
  have hx : IsKQC (localMapExpr h x) (localMapDomain h x) K₁ := hK₁ x
  have hle' : maxDilatation (localMapExpr h x) (localMapDomain h x) ≤ ENNReal.ofReal K :=
    (le_iSup (fun x => maxDilatation (localMapExpr h x) (localMapDomain h x)) x).trans hle
  refine (thm10_1_isKQC_iff hx.1 hK hx.2.2.1).2 ⟨thm9_1_isACL hx, ?_⟩
  filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict (localMapDomain h x))
      (fun z => ENNReal.ofReal ((‖dz (localMapExpr h x) z‖ + ‖dzbar (localMapExpr h x) z‖) /
        (‖dz (localMapExpr h x) z‖ - ‖dzbar (localMapExpr h x) z‖))),
    thm9_6_cor2_jacobian_pos hx] with z hz hJ
  have hzK := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 (hz.trans hle')
  unfold jacobian at hJ
  have hlt : ‖dzbar (localMapExpr h x) z‖ < ‖dz (localMapExpr h x) z‖ := by
    nlinarith [norm_nonneg (dz (localMapExpr h x) z), norm_nonneg (dzbar (localMapExpr h x) z)]
  rwa [div_le_iff₀ (sub_pos.2 hlt)] at hzK

/-- `K[h] ≥ 1` for a quasiconformal map of a nonempty surface: the dilatation quotient is `≥ 1` wherever the Jacobian
is positive, i.e. a.e. on the nonempty open domain of any local expression. -/
theorem utm_d_one_le_maxDil [Nonempty S₀] {h : S₀ ≃ₜ S₁} (hh : IsQCRS h) : 1 ≤ maxDilatationRS h := by
  obtain ⟨K₁, -, hK₁⟩ := hh
  obtain ⟨x⟩ : Nonempty S₀ := inferInstance
  have hx := hK₁ x
  have hΩ := s23_localMapDomain_isOpen h.continuous x
  have hne : (localMapDomain h x).Nonempty := ⟨_, (s23_h_center h x).1⟩
  have hμ : volume.restrict (localMapDomain h x) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact hΩ.measure_ne_zero volume hne
  refine le_trans ?_ (le_iSup (fun x => maxDilatation (localMapExpr h x) (localMapDomain h x)) x)
  unfold maxDilatation
  rw [← essSup_const (1 : ℝ≥0∞) hμ]
  refine essSup_mono_ae ?_
  filter_upwards [thm9_6_cor2_jacobian_pos hx] with z hJ
  unfold jacobian at hJ
  have hlt : ‖dzbar (localMapExpr h x) z‖ < ‖dz (localMapExpr h x) z‖ := by
    nlinarith [norm_nonneg (dz (localMapExpr h x) z), norm_nonneg (dzbar (localMapExpr h x) z)]
  show (1 : ℝ≥0∞) ≤ _
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ (sub_pos.2 hlt)]
  linarith [norm_nonneg (dzbar (localMapExpr h x) z)]

/-- **The expression read at the image point vs. the preferred one.**  For `z` in the domain of `g = localMapExpr f x`,
`G = localMapExprAt f x z` agrees near `z` with `σ ∘ g` for the holomorphic transition `σ = φ_{f p} ∘ φ_{f x}⁻¹`
(`p = φ_x⁻¹ z`), so `∂G = c ∂g`, `∂̄G = c ∂̄g` at `z` with `c = σ'(g z) ≠ 0`, and `G` is differentiable at `z` when `g`
is. -/
theorem utm_d_exprAt [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ → S₁} (hf : Continuous f) (x : S₀) {z : ℂ}
    (hz : z ∈ localMapDomain f x) :
    ∃ c : ℂ, c ≠ 0 ∧ dz (localMapExprAt f x z) z = c * dz (localMapExpr f x) z ∧
      dzbar (localMapExprAt f x z) z = c * dzbar (localMapExpr f x) z ∧
      (DifferentiableAt ℝ (localMapExpr f x) z → DifferentiableAt ℝ (localMapExprAt f x z) z) := by
  set p := (chartAt ℂ x).symm z with hp
  have hfp : f p ∈ (chartAt ℂ (f x)).source := hz.2
  set g := localMapExpr f x with hg
  set b := g z with hb
  have hbt : b ∈ (chartAt ℂ (f x)).target := (chartAt ℂ (f x)).map_source hfp
  have hbs0 : (chartAt ℂ (f x)).symm b = f p := (chartAt ℂ (f x)).left_inv hfp
  have hbs : (chartAt ℂ (f x)).symm b ∈ (chartAt ℂ (f p)).source := by
    rw [hbs0]; exact mem_chart_source ℂ (f p)
  set σ := chartTransition (f p) (f x) with hσ
  obtain ⟨hσd, hσ0⟩ := s23_transition (f p) (f x) hbt hbs
  obtain ⟨hm1, hm2, -⟩ := s23_transition_mem hbt hbs
  have hk : DifferentiableAt ℂ (chartTransition (f x) (f p)) (σ b) :=
    s23_transition_differentiableAt (f x) (f p) hm1 hm2
  have hkh := s23_transition_inv (f p) (f x) hbt hbs
  have hgc : ContinuousAt g z := by
    have h1 : ContinuousAt (fun w => f ((chartAt ℂ x).symm w)) z :=
      hf.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hz.1)
    exact ContinuousAt.comp (g := chartAt ℂ (f x)) (f := fun w => f ((chartAt ℂ x).symm w))
      ((chartAt ℂ (f x)).continuousAt hfp) h1
  have hGeq : localMapExprAt f x z =ᶠ[𝓝 z] σ ∘ g := by
    filter_upwards [(s23_localMapDomain_isOpen hf x).mem_nhds hz] with w hw
    have hw2 : f ((chartAt ℂ x).symm w) ∈ (chartAt ℂ (f x)).source := hw.2
    simp only [localMapExprAt, hσ, hg, Function.comp_apply, chartTransition, localMapExpr,
      (chartAt ℂ (f x)).left_inv hw2]
    rfl
  obtain ⟨hW1, hW2⟩ := s23_wirtinger_comp_left hgc hσd hk hkh
  refine ⟨deriv σ b, hσ0, ?_, ?_, fun hd => ?_⟩
  · rw [← hW1]; unfold dz; rw [hGeq.fderiv_eq]
  · rw [← hW2]; unfold dzbar; rw [hGeq.fderiv_eq]
  · exact ((hσd.restrictScalars ℝ).comp z hd).congr_of_eventuallyEq hGeq

/-- **The pointwise estimate of the chain** at a point `z` of the domain of `g = localMapExpr f x` where `q_x(z) ≠ 0`
and `g` is differentiable with `|∂̄g| < |∂g|` and dilatation quotient at most `K`: `J_f ≥ 0`, `D_f ≤ K` and
`λ_f² ≤ K J_f` (`eq26_13`, the quotient being the same for `g` and for the expression at the image point,
`utm_d_exprAt`; where `q'` vanishes at the image, `λ_f = 0`). -/
theorem utm_d_pointwise [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {K : ℝ}
    (x : S₀) {z : ℂ} (hz : z ∈ localMapDomain f x) (hq0 : q x z ≠ 0)
    (hd : DifferentiableAt ℝ (localMapExpr f x) z)
    (hlt : ‖dzbar (localMapExpr f x) z‖ < ‖dz (localMapExpr f x) z‖)
    (hK : ‖dz (localMapExpr f x) z‖ + ‖dzbar (localMapExpr f x) z‖ ≤
      K * (‖dz (localMapExpr f x) z‖ - ‖dzbar (localMapExpr f x) z‖)) :
    0 ≤ jacobianQD q q' f x z ∧ dilatationQuotient (localMapExprAt f x z) z ≤ K ∧
      lambdaStretch q q' f x z ^ 2 ≤ K * jacobianQD q q' f x z := by
  obtain ⟨c, hc0, hdzc, hdzbarc, hdiff⟩ := utm_d_exprAt f.continuous x hz
  set G := localMapExprAt f x z with hG
  set g := localMapExpr f x with hg
  have hc : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have ha : 0 < ‖dz g z‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have hltG : ‖dzbar G z‖ < ‖dz G z‖ := by
    rw [hdzc, hdzbarc, norm_mul, norm_mul]
    exact mul_lt_mul_of_pos_left hlt hc
  have hJG : 0 ≤ jacobian G z := by
    unfold jacobian
    nlinarith [norm_nonneg (dzbar G z)]
  have hJ : 0 ≤ jacobianQD q q' f x z := by
    unfold jacobianQD
    rw [← hG]
    positivity
  have hD : dilatationQuotient G z ≤ K := by
    unfold dilatationQuotient complexDilatation
    rw [norm_div, hdzc, hdzbarc, norm_mul, norm_mul, mul_div_mul_left _ _ hc.ne']
    have e1 : 1 + ‖dzbar g z‖ / ‖dz g z‖ = (‖dz g z‖ + ‖dzbar g z‖) / ‖dz g z‖ := by field_simp
    have e2 : 1 - ‖dzbar g z‖ / ‖dz g z‖ = (‖dz g z‖ - ‖dzbar g z‖) / ‖dz g z‖ := by field_simp
    rw [e1, e2, div_div_div_cancel_right₀ ha.ne', div_le_iff₀ (sub_pos.2 hlt)]
    exact hK
  have hK0 : 0 ≤ K := by
    have h1 : 0 < ‖dz g z‖ - ‖dzbar g z‖ := sub_pos.2 hlt
    by_contra hneg
    have hneg' := not_le.1 hneg
    nlinarith [norm_nonneg (dzbar g z)]
  refine ⟨hJ, hD, ?_⟩
  by_cases hq'0 : q' (f ((chartAt ℂ x).symm z)) (localMapExprAt f x z z) = 0
  · have hl : lambdaStretch q q' f x z = 0 := by
      unfold lambdaStretch lambdaStretchPlane
      rw [hq'0]
      simp
    rw [hl]
    simpa using mul_nonneg hK0 hJ
  · obtain ⟨h1, -⟩ := eq26_13 (q := q) (q' := q') (f := f) x (hdiff hd) hltG hq0 hq'0
    exact h1.trans (mul_le_mul_of_nonneg_right hD hJ)

/-- **(26.11)–(26.12): the λ-integral on the target is at most the λ-integral on the source**, for any chart
partition of `S₀`: `∬_{S₁} λ_{f∘f₀⁻¹} dA_{q'} ≤ ∑ᵢ ∬_{φᵢ(Pᵢ)} λ_f |q|` (`utm_d_lambda_piece`, assembled by
`utm_d_surfaceIntegral_le`). -/
theorem utm_d_transfer [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]
    [CompactSpace S₁] [Nonempty S₁] {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ}
    (hf₀ : IsTeichmullerMap f₀ q q' k) (f : S₀ ≃ₜ S₁) {x : ℕ → S₀} {P : ℕ → Set S₀}
    (hP : IsChartPartition S₀ x P) :
    surfaceIntegral q' (fun y w => ENNReal.ofReal (lambdaStretch q' q' (f₀.symm.trans f) y w)) ≤
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ENNReal.ofReal (lambdaStretch q q' f (x i) z) * ENNReal.ofReal ‖q (x i) z‖ :=
  utm_d_surfaceIntegral_le f₀ q q' _ _
    (fun x y A hA hFA hAm _ => utm_d_lambda_piece hf₀ f x y A hA hFA hAm) hP

/-- **A chart partition subordinate to a map, with a prescribed first piece.**  On a compact surface, for a continuous
`F`, there is a chart partition with `Pᵢ ⊆ U_{xᵢ} ∩ F⁻¹ U_{F xᵢ}` whose first piece is `U_{x₀} ∩ F⁻¹ U_{F x₀}` for a
given `x₀` (a partition from `s26_exists_chartPartition`, shifted, with that piece removed). -/
theorem utm_d_good_partition [CompactSpace S₀] [Nonempty S₀] (F : S₀ → S₁) (hF : Continuous F) (x₀ : S₀) :
    ∃ (x : ℕ → S₀) (P : ℕ → Set S₀), IsChartPartition S₀ x P ∧
      (∀ i, P i ⊆ (chartAt ℂ (x i)).source ∩ F ⁻¹' (chartAt ℂ (F (x i))).source) ∧ x 0 = x₀ ∧
      P 0 = (chartAt ℂ x₀).source ∩ F ⁻¹' (chartAt ℂ (F x₀)).source := by
  set V : S₀ → Set S₀ := fun p => (chartAt ℂ p).source ∩ F ⁻¹' (chartAt ℂ (F p)).source with hV
  have hVo : ∀ p, IsOpen (V p) := fun p =>
    (chartAt ℂ p).open_source.inter (hF.isOpen_preimage _ (chartAt ℂ (F p)).open_source)
  obtain ⟨x, P, -, ⟨hPsm, hPd, hPc⟩, hPV, -⟩ := s26_exists_chartPartition V hVo
    (fun p => ⟨mem_chart_source ℂ p, mem_chart_source ℂ (F p)⟩) (fun p => inter_subset_left)
  refine ⟨fun i => match i with | 0 => x₀ | j + 1 => x j,
    fun i => match i with | 0 => V x₀ | j + 1 => P j \ V x₀, ⟨fun i => ?_, fun i j hij => ?_, ?_⟩,
    fun i => ?_, rfl, rfl⟩
  · rcases i with _ | j
    · exact ⟨inter_subset_left,
        ((chartAt ℂ x₀).isOpen_image_of_subset_source (hVo x₀) inter_subset_left).measurableSet⟩
    · refine ⟨sdiff_subset.trans (hPsm j).1, ?_⟩
      have heq : chartAt ℂ (x j) '' (P j \ V x₀) = chartAt ℂ (x j) '' P j \
          ((chartAt ℂ (x j)).target ∩ (chartAt ℂ (x j)).symm ⁻¹' V x₀) := by
        ext w
        constructor
        · rintro ⟨a, ⟨haP, haV⟩, rfl⟩
          refine ⟨⟨a, haP, rfl⟩, fun h => haV ?_⟩
          have h2 := h.2
          rwa [mem_preimage, (chartAt ℂ (x j)).left_inv ((hPsm j).1 haP)] at h2
        · rintro ⟨⟨a, haP, rfl⟩, h⟩
          refine ⟨a, ⟨haP, fun haV => h ⟨(chartAt ℂ (x j)).map_source ((hPsm j).1 haP), ?_⟩⟩, rfl⟩
          rw [mem_preimage, (chartAt ℂ (x j)).left_inv ((hPsm j).1 haP)]
          exact haV
      show MeasurableSet (chartAt ℂ (x j) '' (P j \ V x₀))
      rw [heq]
      exact (hPsm j).2.diff ((chartAt ℂ (x j)).isOpen_inter_preimage_symm (hVo x₀)).measurableSet
  · rcases i with _ | i <;> rcases j with _ | j
    · exact absurd rfl hij
    · exact disjoint_sdiff_right
    · exact disjoint_sdiff_left
    · exact (hPd fun h => hij (congrArg Nat.succ h)).mono sdiff_subset sdiff_subset
  · refine eq_univ_of_forall fun p => ?_
    by_cases hp : p ∈ V x₀
    · exact mem_iUnion.2 ⟨0, hp⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.1 (hPc.symm ▸ mem_univ p : p ∈ ⋃ i, P i)
      exact mem_iUnion.2 ⟨j + 1, hj, hp⟩
  · rcases i with _ | j
    · exact subset_rfl
    · exact sdiff_subset.trans (hPV j)

/-- **The a.e. good points of a piece.**  For a `K`-q.c. `f` and a measurable `E` inside the domain of
`g = localMapExpr f x`, a.e. `z ∈ E` has `q_x(z) ≠ 0` (the zeros are countable) and `g` differentiable at `z` with
`|∂̄g| < |∂g|` and `|∂g| + |∂̄g| ≤ K (|∂g| - |∂̄g|)` (Theorems 9.3, 9.4 and 9.6). -/
theorem utm_d_ae_good [T2Space S₀] [ConnectedSpace S₀] {f : S₀ ≃ₜ S₁} {K : ℝ} (hf : IsKQCRS f K)
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (x : S₀) {E : Set ℂ} (hEm : MeasurableSet E)
    (hE : E ⊆ localMapDomain f x) :
    ∀ᵐ z ∂(volume.restrict E), z ∈ E ∧ q x z ≠ 0 ∧ DifferentiableAt ℝ (localMapExpr f x) z ∧
      ‖dzbar (localMapExpr f x) z‖ < ‖dz (localMapExpr f x) z‖ ∧
      ‖dz (localMapExpr f x) z‖ + ‖dzbar (localMapExpr f x) z‖ ≤
        K * (‖dz (localMapExpr f x) z‖ - ‖dzbar (localMapExpr f x) z‖) := by
  have hZ0 : volume {z | z ∈ (chartAt ℂ x).target ∧ q x z = 0} = 0 :=
    (s26u_zeros_countable hq hne x).measure_zero _
  filter_upwards [ae_restrict_mem hEm, ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hZ0),
    ae_restrict_of_ae_restrict_of_subset hE (thm9_3_differentiable_ae (hf.2 x)),
    ae_restrict_of_ae_restrict_of_subset hE (thm9_6_cor2_jacobian_pos (hf.2 x)),
    ae_restrict_of_ae_restrict_of_subset hE (thm9_4_dilatation_ae (hf.2 x))] with z hzE hzZ hd hJ hK
  refine ⟨hzE, fun h0 => hzZ ⟨(hE hzE).1, h0⟩, hd, ?_, hK⟩
  unfold jacobian at hJ
  nlinarith [norm_nonneg (dz (localMapExpr f x) z), norm_nonneg (dzbar (localMapExpr f x) z)]

/-- The real inequality of the chain (`2λ ≤ λ²/K₀ + K₀`): `λ² ≤ K J` and `K₀ > 0` give `2λ ≤ (K/K₀) J + K₀`. -/
theorem utm_d_real_ineq {l J K K₀ : ℝ} (hK₀ : 0 < K₀) (hl : l ^ 2 ≤ K * J) : 2 * l ≤ K / K₀ * J + K₀ := by
  have e : K / K₀ * J + K₀ = (K * J + K₀ ^ 2) / K₀ := by field_simp
  rw [e, le_div_iff₀ hK₀]
  nlinarith [sq_nonneg (l - K₀)]

/-- **The pieces of a subordinate partition.**  If `Pᵢ ⊆ U_{xᵢ} ∩ f⁻¹ U_{f xᵢ}`, the chart image `φ_{xᵢ}(Pᵢ)` lies in
the domain of `localMapExpr f xᵢ`. -/
theorem utm_d_piece_sub (f : S₀ → S₁) {x : S₀} {P : Set S₀}
    (hPV : P ⊆ (chartAt ℂ x).source ∩ f ⁻¹' (chartAt ℂ (f x)).source) :
    chartAt ℂ x '' P ⊆ localMapDomain f x := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨(chartAt ℂ x).map_source (hPV ha).1, ?_⟩
  show f ((chartAt ℂ x).symm (chartAt ℂ x a)) ∈ (chartAt ℂ (f x)).source
  rw [(chartAt ℂ x).left_inv (hPV ha).1]
  exact (hPV ha).2

/-- **The chain (26.11)–(26.14) on one piece**: for a `K`-q.c. `f` and a measurable `E` inside the domain of
`localMapExpr f x`, `2 ∬_E λ_f |q| ≤ (K/K₀) ∬_E J_f |q| + ∬_E K₀ |q|` (`utm_d_pointwise`, `utm_d_real_ineq` at the
a.e. good points; `|q_x|` is continuous on the chart target, hence measurable). -/
theorem utm_d_chain_piece [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ ≃ₜ S₁} {K : ℝ}
    (hf : IsKQCRS f K) {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {K₀ : ℝ}
    (hK₀ : 0 < K₀) (x : S₀) {E : Set ℂ} (hEm : MeasurableSet E) (hE : E ⊆ localMapDomain f x) :
    2 * ∫⁻ z in E, ENNReal.ofReal (lambdaStretch q q' f x z) * ENNReal.ofReal ‖q x z‖ ≤
      ENNReal.ofReal (K / K₀) * (∫⁻ z in E, ENNReal.ofReal (jacobianQD q q' f x z) * ENNReal.ofReal ‖q x z‖) +
        ∫⁻ z in E, ENNReal.ofReal K₀ * ENNReal.ofReal ‖q x z‖ := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  have hmeas : AEMeasurable (fun z => ENNReal.ofReal K₀ * ENNReal.ofReal ‖q x z‖) (volume.restrict E) := by
    have hc : ContinuousOn (q x) E := (hq'.2 x).continuousOn.mono fun z hz => (hE hz).1
    exact (ENNReal.measurable_ofReal.comp_aemeasurable (hc.aemeasurable hEm).norm).const_mul _
  rw [← lintegral_const_mul' 2 _ (by norm_num),
    ← lintegral_const_mul' (ENNReal.ofReal (K / K₀)) _ ENNReal.ofReal_ne_top, ← lintegral_add_right' _ hmeas]
  refine lintegral_mono_ae ?_
  filter_upwards [utm_d_ae_good hf hq hne x hEm hE] with z hz
  obtain ⟨hzE, hq0, hd, hlt, hKz⟩ := hz
  obtain ⟨hJ, -, hlJ⟩ := utm_d_pointwise (q := q) (q' := q') x (hE hzE) hq0 hd hlt hKz
  have hl := utm_d_lambdaStretch_nonneg q q' f x z
  have hr := utm_d_real_ineq hK₀ hlJ
  have hKK : 0 ≤ K / K₀ := div_nonneg (by linarith [hf.1]) hK₀.le
  have hQ := norm_nonneg (q x z)
  calc 2 * (ENNReal.ofReal (lambdaStretch q q' f x z) * ENNReal.ofReal ‖q x z‖)
      = ENNReal.ofReal (2 * (lambdaStretch q q' f x z * ‖q x z‖)) := by
        rw [← ENNReal.ofReal_mul hl, two_mul, two_mul, ENNReal.ofReal_add (mul_nonneg hl hQ) (mul_nonneg hl hQ)]
    _ ≤ ENNReal.ofReal (K / K₀ * (jacobianQD q q' f x z * ‖q x z‖) + K₀ * ‖q x z‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc 2 * (lambdaStretch q q' f x z * ‖q x z‖) = (2 * lambdaStretch q q' f x z) * ‖q x z‖ := by ring
          _ ≤ (K / K₀ * jacobianQD q q' f x z + K₀) * ‖q x z‖ := mul_le_mul_of_nonneg_right hr hQ
          _ = _ := by ring
    _ = ENNReal.ofReal (K / K₀) * (ENNReal.ofReal (jacobianQD q q' f x z) * ENNReal.ofReal ‖q x z‖) +
          ENNReal.ofReal K₀ * ENNReal.ofReal ‖q x z‖ := by
        rw [ENNReal.ofReal_add (mul_nonneg hKK (mul_nonneg hJ hQ)) (mul_nonneg hK₀.le hQ),
          ENNReal.ofReal_mul hKK, ENNReal.ofReal_mul hJ, ENNReal.ofReal_mul hK₀.le]

/-- **The chain (26.11)–(26.14) summed over a subordinate partition**: for a `K`-q.c. `f` satisfying the main
inequality `hL2`, and a chart partition `P` of `S₀` with `f(Pᵢ)` in the chart at `f(xᵢ)`, the three sums
`L = ∑ᵢ ∬ λ_f |q|`, `C = ∑ᵢ ∬ J_f |q|` and `B = ∑ᵢ ∬ K₀ |q|` satisfy `‖q'‖ ≤ L`, `C = B = ‖q'‖` and
`2 L ≤ (K/K₀) C + B` (`utm_d_transfer`, `s26w_qc_piece`, `s26w_teich_piece`, `utm_d_chain_piece`). -/
theorem utm_d_chain [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] [CompactSpace S₁]
    {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k)
    {f : S₀ ≃ₜ S₁} {K : ℝ} (hf : IsKQCRS f K)
    (hL2 : quadDiffNorm q' ≤
      surfaceIntegral q' fun x z => ENNReal.ofReal (lambdaStretch q' q' (f₀.symm.trans f) x z))
    {x : ℕ → S₀} {P : ℕ → Set S₀} (hP : IsChartPartition S₀ x P)
    (hPV : ∀ i, P i ⊆ (chartAt ℂ (x i)).source ∩ f ⁻¹' (chartAt ℂ (f (x i))).source) :
    quadDiffNorm q' ≤ ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ENNReal.ofReal (lambdaStretch q q' f (x i) z) * ENNReal.ofReal ‖q (x i) z‖ ∧
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ENNReal.ofReal (jacobianQD q q' f (x i) z) * ENNReal.ofReal ‖q (x i) z‖ = quadDiffNorm q' ∧
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ENNReal.ofReal ((1 + k) / (1 - k)) * ENNReal.ofReal ‖q (x i) z‖ = quadDiffNorm q' ∧
      ∀ i, 2 * ∫⁻ z in chartAt ℂ (x i) '' P i,
          ENNReal.ofReal (lambdaStretch q q' f (x i) z) * ENNReal.ofReal ‖q (x i) z‖ ≤
        ENNReal.ofReal (K / ((1 + k) / (1 - k))) * (∫⁻ z in chartAt ℂ (x i) '' P i,
          ENNReal.ofReal (jacobianQD q q' f (x i) z) * ENNReal.ofReal ‖q (x i) z‖) +
        ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ((1 + k) / (1 - k)) * ENNReal.ofReal ‖q (x i) z‖ := by
  have : Nonempty S₁ := ConnectedSpace.toNonempty
  have hK₀ : 0 < (1 + k) / (1 - k) := div_pos (by linarith [hf₀.k_nonneg]) (by linarith [hf₀.k_lt_one])
  refine ⟨hL2.trans (utm_d_transfer hf₀ f hP), ?_, ?_, fun i => ?_⟩
  · exact utm_d_sum_eq_norm f q q' (fun x z => ENNReal.ofReal (jacobianQD q q' f x z))
      (fun x y A hA hFA hAm _ => s26w_qc_piece hf₀.initial hf₀.initial_ne hf₀.terminal ⟨K, hf⟩ x y A hA hFA hAm)
      hP
  · exact utm_d_sum_eq_norm f₀ q q' (fun _ _ => ENNReal.ofReal ((1 + k) / (1 - k)))
      (fun x y A hA hFA hAm _ => s26w_teich_piece hf₀ x y A hA hFA hAm) hP
  · exact utm_d_chain_piece hf hf₀.initial hf₀.initial_ne hK₀ (x i) (hP.1 i).2 (utm_d_piece_sub f (hPV i))

/-- **(26.11)–(26.14): `K₀ ≤ K` for every `K` with `f` `K`-quasiconformal**, under the main inequality `hL2` on the
target.  On a subordinate chart partition (`utm_d_good_partition`), `utm_d_chain` gives
`2 ‖q'‖ ≤ 2 L ≤ (K/K₀) ‖q'‖ + ‖q'‖`, and `0 < ‖q'‖ < ∞` (`‖q'‖ = K₀ ‖q‖`, `q ≠ 0`). -/
theorem utm_d_ineq_core [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] [CompactSpace S₁]
    {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k)
    {f : S₀ ≃ₜ S₁} {K : ℝ} (hf : IsKQCRS f K)
    (hL2 : quadDiffNorm q' ≤
      surfaceIntegral q' fun x z => ENNReal.ofReal (lambdaStretch q' q' (f₀.symm.trans f) x z)) :
    (1 + k) / (1 - k) ≤ K := by
  have : Nonempty S₀ := ConnectedSpace.toNonempty
  have : Nonempty S₁ := ConnectedSpace.toNonempty
  have hK₀ : 0 < (1 + k) / (1 - k) := div_pos (by linarith [hf₀.k_nonneg]) (by linarith [hf₀.k_lt_one])
  obtain ⟨p₀⟩ : Nonempty S₀ := inferInstance
  obtain ⟨x, P, hP, hPV, -, -⟩ := utm_d_good_partition f f.continuous p₀
  obtain ⟨hL, hC, hB, hpiece⟩ := utm_d_chain hf₀ hf hL2 hP hPV
  set N := quadDiffNorm q' with hN
  have hNt : N ≠ ⊤ := (s26_quadDiffNorm_lt_top hf₀.terminal).ne
  have hN0 : N ≠ 0 := by
    rw [hN, s26w_quadDiffNorm_teich hf₀]
    exact mul_ne_zero (ENNReal.ofReal_pos.2 hK₀).ne' (s26_quadDiffNorm_pos hf₀.initial hf₀.initial_ne)
  have h2 : N + N ≤ ENNReal.ofReal (K / ((1 + k) / (1 - k))) * N + N := by
    rw [← two_mul]
    calc 2 * N ≤ 2 * ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
          ENNReal.ofReal (lambdaStretch q q' f (x i) z) * ENNReal.ofReal ‖q (x i) z‖ := mul_le_mul' le_rfl hL
      _ = ∑' i, 2 * ∫⁻ z in chartAt ℂ (x i) '' P i,
          ENNReal.ofReal (lambdaStretch q q' f (x i) z) * ENNReal.ofReal ‖q (x i) z‖ :=
          ENNReal.tsum_mul_left.symm
      _ ≤ _ := ENNReal.tsum_le_tsum hpiece
      _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, hC, hB]
  have h3 : 1 * N ≤ ENNReal.ofReal (K / ((1 + k) / (1 - k))) * N := by
    rw [one_mul]
    exact ENNReal.le_of_add_le_add_right hNt h2
  have h4 := ENNReal.one_le_ofReal.1 ((ENNReal.mul_le_mul_iff_left hN0 hNt).1 h3)
  rwa [one_le_div hK₀] at h4

/-- [P9, stub] **(26.11)–(26.14): the inequality of Theorem 26.2 from the main inequality on the target.**
If Lemma 26.2 holds on `S₁` for `q'` and `f* = f ∘ f₀⁻¹` (hypothesis `hL2`), then `K₀ ≤ K[f]`.

*Truth* (the book's computation; no homotopy is needed once `hL2` is given): at regular points
`λ_{f*}(f₀ p) = λ_{q,q',f}(p) / K₀` (natural parameters of `f₀`), and `f₀` multiplies `q`-areas by `K₀`, so
`‖q'‖ ≤ ∬_{S₁} λ_{f*} dA_{q'} = ∬_{S₀} λ_{q,q',f} dA_q ≤ (∬ λ² dA_q)^{1/2} ‖q‖^{1/2}
≤ (∬ D_f J_f dA_q)^{1/2} ‖q‖^{1/2} ≤ (K[f] ‖q'‖)^{1/2} (‖q'‖ / K₀)^{1/2}` (Cauchy–Schwarz, `eq26_13`,
`D_f ≤ K[f]` a.e., `eq26_14`); with `0 < ‖q'‖ < ∞` this is `K₀ ≤ K[f]`. -/
theorem utm_thm26_2_ineq [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ}
    {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k) {f : S₀ ≃ₜ S₁} (hf : IsQCRS f)
    (hL2 : quadDiffNorm q' ≤
      surfaceIntegral q' fun x z => ENNReal.ofReal (lambdaStretch q' q' (f₀.symm.trans f) x z)) :
    ENNReal.ofReal ((1 + k) / (1 - k)) ≤ maxDilatationRS f := by
  have _ := hg
  have : CompactSpace S₀ := h₀.1
  have : CompactSpace S₁ := h₁.1
  have : Nonempty S₀ := ConnectedSpace.toNonempty
  obtain ⟨K₁, hK₁⟩ := hf
  have hfin : maxDilatationRS f ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (maxDilatationRS_le hK₁)
  have h1 : 1 ≤ (maxDilatationRS f).toReal := by
    have h := ENNReal.toReal_mono hfin (utm_d_one_le_maxDil (h := f) ⟨K₁, hK₁⟩)
    rwa [ENNReal.toReal_one] at h
  have hK : IsKQCRS f (maxDilatationRS f).toReal :=
    utm_d_isKQCRS_of_maxDil ⟨K₁, hK₁⟩ h1 (ENNReal.ofReal_toReal hfin).ge
  exact (ENNReal.ofReal_le_ofReal (utm_d_ineq_core hf₀ hK hL2)).trans_eq (ENNReal.ofReal_toReal hfin)

/-- Termwise equality from equal finite sums: if `aᵢ ≤ bᵢ` for all `i`, `∑ b ≤ ∑ a` and `∑ a < ∞`, then `aᵢ = bᵢ`
(`ENNReal.tsum_lt_tsum`). -/
theorem utm_d_tsum_eq_of_le {a b : ℕ → ℝ≥0∞} (hab : ∀ i, a i ≤ b i) (hba : ∑' i, b i ≤ ∑' i, a i)
    (ha : ∑' i, a i ≠ ⊤) (i : ℕ) : a i = b i := by
  refine le_antisymm (hab i) (not_lt.1 fun hlt => ?_)
  exact (ENNReal.tsum_lt_tsum ha hab hlt).not_ge hba

/-- **The pointwise equality case of the chain** (`K = K₀`).  At a point as in `utm_d_pointwise` with
`K = K₀ = (1+k)/(1-k)`, if moreover `2 λ_f = J_f + K₀`, then `μ_g(z) = k q̄_x/|q_x|` for `g = localMapExpr f x`:
`λ_f² ≤ K₀ J_f` forces `λ_f = J_f = K₀`, so `λ_f² = D_f J_f` and `D_f = K₀`; the equality clause of `eq26_13` makes
`μ q_x/|q_x|` a non-negative real `r`, and `D_f = K₀` gives `|μ| = k = r`. -/
theorem utm_d_pointwise_eq [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ}
    (hk₀ : 0 ≤ k) (hk : k < 1) (x : S₀) {z : ℂ} (hz : z ∈ localMapDomain f x) (hq0 : q x z ≠ 0)
    (hd : DifferentiableAt ℝ (localMapExpr f x) z)
    (hlt : ‖dzbar (localMapExpr f x) z‖ < ‖dz (localMapExpr f x) z‖)
    (hK : ‖dz (localMapExpr f x) z‖ + ‖dzbar (localMapExpr f x) z‖ ≤
      (1 + k) / (1 - k) * (‖dz (localMapExpr f x) z‖ - ‖dzbar (localMapExpr f x) z‖))
    (h2 : 2 * lambdaStretch q q' f x z = jacobianQD q q' f x z + (1 + k) / (1 - k)) :
    complexDilatation (localMapExpr f x) z = teichmullerBeltrami k q x z := by
  have h1k : 0 < 1 - k := by linarith
  have hK₀ : 0 < (1 + k) / (1 - k) := div_pos (by linarith) h1k
  obtain ⟨hJ, hD, hlJ⟩ := utm_d_pointwise (q := q) (q' := q') x hz hq0 hd hlt hK
  have hl : lambdaStretch q q' f x z = (1 + k) / (1 - k) := by
    nlinarith [sq_nonneg (lambdaStretch q q' f x z - (1 + k) / (1 - k))]
  have hJ' : jacobianQD q q' f x z = (1 + k) / (1 - k) := by linarith
  obtain ⟨c, hc0, hdzc, hdzbarc, hdiff⟩ := utm_d_exprAt f.continuous x hz
  have hc : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have hltG : ‖dzbar (localMapExprAt f x z) z‖ < ‖dz (localMapExprAt f x z) z‖ := by
    rw [hdzc, hdzbarc, norm_mul, norm_mul]
    exact mul_lt_mul_of_pos_left hlt hc
  have hq'0 : q' (f ((chartAt ℂ x).symm z)) (localMapExprAt f x z z) ≠ 0 := by
    intro h0
    have hl0 : lambdaStretch q q' f x z = 0 := by
      unfold lambdaStretch lambdaStretchPlane
      rw [h0]
      simp
    linarith
  obtain ⟨h1, hiff⟩ := eq26_13 (q := q) (q' := q') (f := f) x (hdiff hd) hltG hq0 hq'0
  set D := dilatationQuotient (localMapExprAt f x z) z with hDdef
  have hDge : (1 + k) / (1 - k) ≤ D := by
    rw [hl, hJ'] at h1
    nlinarith
  have hDeq : D = (1 + k) / (1 - k) := le_antisymm hD hDge
  obtain ⟨r, hr0, hr⟩ := hiff.1 (by rw [hDeq, hl, hJ']; ring)
  -- the dilatation of the expression at the image point
  set G := localMapExprAt f x z with hG
  set μ := complexDilatation G z with hμ
  have hdz0 : dz G z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hltG
    exact (not_lt.2 (norm_nonneg _)) hltG
  have hm1 : ‖μ‖ < 1 := by
    rw [hμ, complexDilatation, norm_div, div_lt_one (norm_pos_iff.2 hdz0)]
    exact hltG
  have hmk : ‖μ‖ = k := by
    have h3 : (1 + ‖μ‖) / (1 - ‖μ‖) = (1 + k) / (1 - k) := hDeq
    rw [div_eq_div_iff (by linarith) h1k.ne'] at h3
    linarith
  set u : ℂ := q x z / ((‖q x z‖ : ℝ) : ℂ) with hu
  have hQ : (‖q x z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hq0
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.2 hq0)]
  have hμu : μ * u = r := by
    rw [hμ, complexDilatation, div_mul_eq_mul_div, hr, mul_div_assoc, div_self hdz0, mul_one]
  have hrk : r = k := by
    have h4 := congrArg norm hμu
    rw [norm_mul, hun, mul_one, hmk, Complex.norm_real, Real.norm_of_nonneg hr0] at h4
    exact h4.symm
  have hμG : μ = teichmullerBeltrami k q x z := by
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hun
      exact zero_ne_one hun
    have hμ' : μ = (k : ℂ) / u := by rw [eq_div_iff hu0, hμu, hrk]
    rw [hμ', teichmullerBeltrami, hu]
    have hqq : q x z * conj (q x z) = ((‖q x z‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    field_simp
    rw [mul_assoc, hqq]
  rw [← hμG, hμ, complexDilatation, complexDilatation, hdzc, hdzbarc, mul_div_mul_left _ _ hc0]

/-- The first piece of a subordinate chart partition is the whole domain of the local expression:
`φ_x(U_x ∩ f⁻¹ U_{f x}) = dom (localMapExpr f x)`. -/
theorem utm_d_image_eq_domain (f : S₀ → S₁) (x : S₀) :
    chartAt ℂ x '' ((chartAt ℂ x).source ∩ f ⁻¹' (chartAt ℂ (f x)).source) = localMapDomain f x := by
  rw [(chartAt ℂ x).image_source_inter_eq']
  rfl

/-- **(26.15): the complex dilatation of an extremal competitor.**  If `f` is `K₀`-q.c. and satisfies the main
inequality `hL2`, then in every chart `x`, `μ_f = k q̄_x/|q_x|` a.e. on the domain of `localMapExpr f x`.  On a
subordinate chart partition whose first piece is that domain (`utm_d_good_partition`), the chain `utm_d_chain` closes
(`2‖q'‖ ≤ 2L ≤ C + B = 2‖q'‖`), so every piece is an equality (`utm_d_tsum_eq_of_le`); on the first piece
`2 λ_f |q| ≤ (J_f + K₀) |q|` with equal finite integrals, and `J_f |q_x| = J_g |q'_{f x} ∘ g|` is measurable there
(`s26w_jacobianQD_mul`), so `2 λ_f = J_f + K₀` a.e. (`ae_eq_of_ae_le_of_lintegral_le`) and `utm_d_pointwise_eq`
applies. -/
theorem utm_d_mu_eq [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] [CompactSpace S₁]
    {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k)
    {f : S₀ ≃ₜ S₁} (hf : IsKQCRS f ((1 + k) / (1 - k)))
    (hL2 : quadDiffNorm q' ≤
      surfaceIntegral q' fun x z => ENNReal.ofReal (lambdaStretch q' q' (f₀.symm.trans f) x z)) (x : S₀) :
    ∀ᵐ z ∂(volume.restrict (localMapDomain f x)),
      complexDilatation (localMapExpr f x) z = teichmullerBeltrami k q x z := by
  have : Nonempty S₀ := ConnectedSpace.toNonempty
  have : Nonempty S₁ := ConnectedSpace.toNonempty
  have hk₀ := hf₀.k_nonneg
  have hk := hf₀.k_lt_one
  have hK₀ : 0 < (1 + k) / (1 - k) := div_pos (by linarith) (by linarith)
  obtain ⟨xs, P, hP, hPV, hx0, hP0⟩ := utm_d_good_partition f f.continuous x
  obtain ⟨hL, hC, hB, hpiece⟩ := utm_d_chain hf₀ hf hL2 hP hPV
  have hNt : quadDiffNorm q' ≠ ⊤ := (s26_quadDiffNorm_lt_top hf₀.terminal).ne
  have hone : ENNReal.ofReal ((1 + k) / (1 - k) / ((1 + k) / (1 - k))) = 1 := by
    rw [div_self hK₀.ne', ENNReal.ofReal_one]
  -- the two sides of the chain, piece by piece
  set a : ℕ → ℝ≥0∞ := fun i => 2 * ∫⁻ z in chartAt ℂ (xs i) '' P i,
    ENNReal.ofReal (lambdaStretch q q' f (xs i) z) * ENNReal.ofReal ‖q (xs i) z‖ with ha
  set b : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal ((1 + k) / (1 - k) / ((1 + k) / (1 - k))) *
    (∫⁻ z in chartAt ℂ (xs i) '' P i, ENNReal.ofReal (jacobianQD q q' f (xs i) z) * ENNReal.ofReal ‖q (xs i) z‖) +
    ∫⁻ z in chartAt ℂ (xs i) '' P i, ENNReal.ofReal ((1 + k) / (1 - k)) * ENNReal.ofReal ‖q (xs i) z‖ with hb
  have hsb : ∑' i, b i = quadDiffNorm q' + quadDiffNorm q' := by
    rw [hb, ENNReal.tsum_add, ENNReal.tsum_mul_left, hC, hB, hone, one_mul]
  have hsa : quadDiffNorm q' + quadDiffNorm q' ≤ ∑' i, a i := by
    rw [← two_mul, ha, ENNReal.tsum_mul_left]
    exact mul_le_mul' le_rfl hL
  have hfin : ∑' i, a i ≠ ⊤ :=
    ne_top_of_le_ne_top (hsb ▸ ENNReal.add_ne_top.2 ⟨hNt, hNt⟩) (ENNReal.tsum_le_tsum hpiece)
  have heq0 := utm_d_tsum_eq_of_le hpiece (hsb.trans_le hsa) hfin 0
  have ha0 : a 0 ≠ ⊤ := ne_top_of_le_ne_top hfin (ENNReal.le_tsum 0)
  simp only [ha, hx0, hP0, utm_d_image_eq_domain, hone, one_mul] at heq0 ha0
  -- the first piece is the domain `Ω` of `g = localMapExpr f x`
  set Ω := localMapDomain f x with hΩ
  have hΩo : IsOpen Ω := s23_localMapDomain_isOpen f.continuous x
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : S₀, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hf₀.initial
  have hq'' : IsDiffFamily 2 0 q' ∧ ∀ y : S₁, DifferentiableOn ℂ (q' y) (chartAt ℂ y).target := hf₀.terminal
  have hmeasK : AEMeasurable (fun z => ENNReal.ofReal ((1 + k) / (1 - k)) * ENNReal.ofReal ‖q x z‖)
      (volume.restrict Ω) := by
    have hc : ContinuousOn (q x) Ω := (hq'.2 x).continuousOn.mono fun z hz => hz.1
    exact (ENNReal.measurable_ofReal.comp_aemeasurable (hc.aemeasurable hΩo.measurableSet).norm).const_mul _
  set g := localMapExpr f x with hg
  have hmeasJ : AEMeasurable (fun z => ENNReal.ofReal (jacobianQD q q' f x z) * ENNReal.ofReal ‖q x z‖)
      (volume.restrict Ω) := by
    have hJm : Measurable (jacobian g) :=
      ((measurable_dz g).norm.pow_const 2).sub ((measurable_dzbar g).norm.pow_const 2)
    have hc : ContinuousOn (fun z => q' (f x) (g z)) Ω :=
      (hq''.2 (f x)).continuousOn.comp (hf.2 x).2.2.1.1 fun z hz => (chartAt ℂ (f x)).map_source hz.2
    have h1 : AEMeasurable (fun z => ENNReal.ofReal (jacobian g z * ‖q' (f x) (g z)‖)) (volume.restrict Ω) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        (hJm.aemeasurable.mul (hc.aemeasurable hΩo.measurableSet).norm)
    have hZ0 : volume {z | z ∈ (chartAt ℂ x).target ∧ q x z = 0} = 0 :=
      (s26u_zeros_countable hf₀.initial hf₀.initial_ne x).measure_zero _
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem hΩo.measurableSet,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hZ0)] with z hz hzZ
    have hq0 : q x z ≠ 0 := fun h0 => hzZ ⟨hz.1, h0⟩
    rw [← ENNReal.ofReal_mul' (norm_nonneg _), s26w_jacobianQD_mul hf₀.terminal f.continuous x (f x) hz.1 hz.2 hq0]
    rfl
  -- the pointwise inequality `F ≤ G` and the equality of the integrals
  set F : ℂ → ℝ≥0∞ := fun z => 2 * (ENNReal.ofReal (lambdaStretch q q' f x z) * ENNReal.ofReal ‖q x z‖)
    with hFdef
  set G : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (jacobianQD q q' f x z) * ENNReal.ofReal ‖q x z‖ +
    ENNReal.ofReal ((1 + k) / (1 - k)) * ENNReal.ofReal ‖q x z‖ with hGdef
  have hgood := utm_d_ae_good hf hf₀.initial hf₀.initial_ne x hΩo.measurableSet subset_rfl
  have hFG : ∀ᵐ z ∂(volume.restrict Ω), F z ≤ G z := by
    filter_upwards [hgood] with z hz
    obtain ⟨hzΩ, hq0, hd, hlt, hKz⟩ := hz
    obtain ⟨hJ, -, hlJ⟩ := utm_d_pointwise (q := q) (q' := q') x hzΩ hq0 hd hlt hKz
    have hl := utm_d_lambdaStretch_nonneg q q' f x z
    have hr := utm_d_real_ineq hK₀ hlJ
    rw [div_self hK₀.ne', one_mul] at hr
    have hQ := norm_nonneg (q x z)
    show 2 * (ENNReal.ofReal (lambdaStretch q q' f x z) * ENNReal.ofReal ‖q x z‖) ≤
      ENNReal.ofReal (jacobianQD q q' f x z) * ENNReal.ofReal ‖q x z‖ +
        ENNReal.ofReal ((1 + k) / (1 - k)) * ENNReal.ofReal ‖q x z‖
    rw [← ENNReal.ofReal_mul hl, two_mul, ← ENNReal.ofReal_add (mul_nonneg hl hQ) (mul_nonneg hl hQ),
      ← ENNReal.ofReal_mul hJ, ← ENNReal.ofReal_mul hK₀.le,
      ← ENNReal.ofReal_add (mul_nonneg hJ hQ) (mul_nonneg hK₀.le hQ)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith
  have hIF : ∫⁻ z in Ω, F z = 2 * ∫⁻ z in Ω,
      ENNReal.ofReal (lambdaStretch q q' f x z) * ENNReal.ofReal ‖q x z‖ :=
    lintegral_const_mul' 2 _ (by norm_num)
  have hIG : ∫⁻ z in Ω, G z = (∫⁻ z in Ω, ENNReal.ofReal (jacobianQD q q' f x z) * ENNReal.ofReal ‖q x z‖) +
      ∫⁻ z in Ω, ENNReal.ofReal ((1 + k) / (1 - k)) * ENNReal.ofReal ‖q x z‖ :=
    lintegral_add_right' _ hmeasK
  have hae := ae_eq_of_ae_le_of_lintegral_le hFG (by rw [hIF]; exact ha0) (hmeasJ.add hmeasK)
    (by rw [hIF, hIG, heq0])
  -- the pointwise equality case
  filter_upwards [hae, hgood] with z hFGz hz
  obtain ⟨hzΩ, hq0, hd, hlt, hKz⟩ := hz
  obtain ⟨hJ, -, -⟩ := utm_d_pointwise (q := q) (q' := q') x hzΩ hq0 hd hlt hKz
  have hl := utm_d_lambdaStretch_nonneg q q' f x z
  have hQ : 0 < ‖q x z‖ := norm_pos_iff.2 hq0
  have h3 : ENNReal.ofReal (2 * (lambdaStretch q q' f x z * ‖q x z‖)) =
      ENNReal.ofReal ((jacobianQD q q' f x z + (1 + k) / (1 - k)) * ‖q x z‖) := by
    have h4 : F z = G z := hFGz
    simp only [hFdef, hGdef] at h4
    rw [← ENNReal.ofReal_mul hl, two_mul, ← ENNReal.ofReal_add (mul_nonneg hl hQ.le) (mul_nonneg hl hQ.le),
      ← ENNReal.ofReal_mul hJ, ← ENNReal.ofReal_mul hK₀.le,
      ← ENNReal.ofReal_add (mul_nonneg hJ hQ.le) (mul_nonneg hK₀.le hQ.le)] at h4
    rw [two_mul, h4]
    ring_nf
  rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at h3
  have h5 : (2 * lambdaStretch q q' f x z) * ‖q x z‖ =
      (jacobianQD q q' f x z + (1 + k) / (1 - k)) * ‖q x z‖ := by
    rw [← h3]
    ring
  exact utm_d_pointwise_eq hk₀ hk x hzΩ hq0 hd hlt hKz (mul_right_cancel₀ hQ.ne' h5)

/-- A `K`-q.c. map whose complex dilatation is a.e. a given `μ` on `D` is a generalized solution of the Beltrami
equation for `μ` (Theorem 10.2, `thm10_2_genHomeoSolution_of_isKQC`, with `μ_g` replaced a.e.). -/
theorem utm_d_genHomeo {g μ : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hg : IsKQC g D K)
    (hgμ : ∀ᵐ z ∂(volume.restrict D), complexDilatation g z = μ z) : IsGenHomeoSolution g μ D 2 := by
  obtain ⟨-, hhom, gx, gy, hgp, hae⟩ := thm10_2_genHomeoSolution_of_isKQC hg
  refine ⟨hhom, gx, gy, hgp, ?_⟩
  filter_upwards [hae, hgμ] with z h1 h2
  rw [h1, h2]

/-- **(26.16): `f ∘ f₀⁻¹` is biholomorphic** when `μ_f = k q̄/|q|` a.e. in every chart.  Near every point its local
expression is `T₃ ∘ L_f ∘ L_{f₀⁻¹} ∘ T₁` (`s23_c_decomp`), and on `D = dom L_f ∩ dom L_{f₀}` one has `L_f = φ ∘ L_{f₀}`
with `φ` conformal (`same_dilatation_conformal`: both are generalized solutions of the Beltrami equation for
`k q̄/|q|`, `teichmullerMap_beltrami`); so the expression is `T₃ ∘ φ ∘ T₁`, holomorphic and injective, hence `1`-q.c.
near every point, `1`-q.c. on its domain (`s23_lg`), and `isKQCRS_one_iff`. -/
theorem utm_d_biholomorphic [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]
    {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k)
    {f : S₀ ≃ₜ S₁} (hf : IsQCRS f)
    (hμ : ∀ x : S₀, ∀ᵐ z ∂(volume.restrict (localMapDomain f x)),
      complexDilatation (localMapExpr f x) z = teichmullerBeltrami k q x z) :
    IsBiholomorphic (f₀.symm.trans f) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨K', hK'⟩ := hf₀.qc
  have hμ₀ := (teichmullerMap_beltrami hf₀).1
  have hBel := teichmullerBeltrami_isBeltramiDifferential hf₀.initial hf₀.k_nonneg hf₀.k_lt_one
  set F := f₀.symm.trans f with hF
  refine (isKQCRS_one_iff F).1 ⟨le_rfl, fun y => ?_⟩
  refine s23_lg (s23_localMapDomain_isOpen F.continuous y) le_rfl (s23_c1_injOn_localMapExpr F.injective y)
    fun w₀ hw₀ => ?_
  obtain ⟨U, hUo, hw₀U, hUD, hU⟩ := s23_c_decomp f₀.symm f y hw₀
  set p₀ := (chartAt ℂ y).symm w₀ with hp₀
  set x₀ := f₀.symm p₀ with hx₀
  have hfx₀ : f₀ x₀ = p₀ := f₀.apply_symm_apply p₀
  -- the plane step on `D`
  set D := localMapDomain f x₀ ∩ localMapDomain f₀ x₀ with hD
  have hDo : IsOpen D :=
    (s23_localMapDomain_isOpen f.continuous x₀).inter (s23_localMapDomain_isOpen f₀.continuous x₀)
  have hL₂ : IsKQC (localMapExpr f x₀) D K := ac_t_isKQC_restrict (hK.2 x₀) hDo inter_subset_left
  have hL₀ : IsKQC (localMapExpr f₀ x₀) D K' := ac_t_isKQC_restrict (hK'.2 x₀) hDo inter_subset_right
  have hBD : IsBeltramiCoeff (teichmullerBeltrami k q x₀) D k := by
    have hsub : D ⊆ (chartAt ℂ x₀).target := fun z hz => hz.1.1
    exact ⟨(hBel.2 x₀).1.mono_set hsub, ae_restrict_of_ae_restrict_of_subset hsub (hBel.2 x₀).2⟩
  obtain ⟨φ, hφ, hφeq⟩ := same_dilatation_conformal hDo hf₀.k_lt_one hBD
    (utm_d_genHomeo hL₀ (ae_restrict_of_ae_restrict_of_subset inter_subset_right (hμ₀ x₀)))
    (utm_d_genHomeo hL₂ (ae_restrict_of_ae_restrict_of_subset inter_subset_left (hμ x₀)))
  have hV : IsOpen (localMapExpr f₀ x₀ '' D) := isOpen_image_of_isKQC hL₀
  -- the neighbourhood `W` of `w₀`
  set W := U ∩ ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ p₀).source) with hW
  have hWo : IsOpen W := hUo.inter ((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ p₀).open_source)
  have hWD : W ⊆ localMapDomain F y := inter_subset_left.trans hUD
  -- on `W` the expression is `T₃ ∘ φ ∘ T₁`
  have hform : ∀ w ∈ W, localMapExpr F y w =
      (chartTransition (f (f₀.symm y)) (f x₀) ∘ φ ∘ chartTransition p₀ y) w ∧
      DifferentiableAt ℂ (chartTransition (f (f₀.symm y)) (f x₀) ∘ φ ∘ chartTransition p₀ y) w := by
    intro w hw
    obtain ⟨hwU, hwt, hws⟩ := hw
    obtain ⟨h1, h2, h3, h4, h5⟩ := hU w hwU
    set u := chartTransition p₀ y w with hu
    set v := localMapExpr f₀.symm p₀ u with hv
    have h1s : f₀.symm ((chartAt ℂ p₀).symm u) ∈ (chartAt ℂ x₀).source := h1.2
    have hvs : (chartAt ℂ x₀).symm v = f₀.symm ((chartAt ℂ p₀).symm u) := (chartAt ℂ x₀).left_inv h1s
    have hv0 : v ∈ localMapDomain f₀ x₀ := by
      refine ⟨(chartAt ℂ x₀).map_source h1s, ?_⟩
      show f₀ ((chartAt ℂ x₀).symm v) ∈ (chartAt ℂ (f₀ x₀)).source
      rw [hvs, hfx₀, Homeomorph.apply_symm_apply]
      exact (chartAt ℂ p₀).map_target h1.1
    have hvD : v ∈ D := ⟨h2, hv0⟩
    have hL₀v : localMapExpr f₀ x₀ v = u := by
      show chartAt ℂ (f₀ x₀) (f₀ ((chartAt ℂ x₀).symm v)) = u
      rw [hvs, hfx₀, Homeomorph.apply_symm_apply]
      exact (chartAt ℂ p₀).right_inv h1.1
    have hφv : φ u = localMapExpr f x₀ v := by rw [hφeq v hvD, hL₀v]
    refine ⟨by rw [h5, Function.comp_apply, Function.comp_apply, hφv], ?_⟩
    have hT₁ := (s23_transition p₀ y hwt hws).1
    have hφd : DifferentiableAt ℂ φ u :=
      (hφ.1 u ⟨v, hvD, hL₀v⟩).differentiableAt (hV.mem_nhds ⟨v, hvD, hL₀v⟩)
    have hT₃ : DifferentiableAt ℂ (chartTransition (f (f₀.symm y)) (f x₀)) (φ u) := by
      rw [hφv]
      exact (s23_transition (f (f₀.symm y)) (f x₀) h3 h4).1
    exact hT₃.comp w (hφd.comp w hT₁)
  refine ⟨W, hWo, ⟨hw₀U, hw₀.1, mem_chart_source ℂ p₀⟩, hWD,
    isKQC_one_of_conformal hWo ⟨fun w hw => ?_, (s23_c1_injOn_localMapExpr F.injective y).mono hWD, rfl⟩⟩
  refine ((hform w hw).2.congr_of_eventuallyEq ?_).differentiableWithinAt
  exact Filter.eventuallyEq_of_mem (hWo.mem_nhds hw) fun w' hw' => (hform w' hw').1

/-- [P10, stub] **(26.15)–(26.16): the equality analysis.**  Under `hL2` (as in [P9]) and `K[f] = K₀`, the complex
dilatation of `f` is `k q̄/|q|` a.e. in every chart, and `f ∘ f₀⁻¹` is biholomorphic.

*Truth:* every inequality in the chain of [P9] is an equality: `λ² = D_f J_f` a.e. (the iff clause of `eq26_13`:
`∂̄f · q/|q|` is a non-negative multiple of `∂f`) and `D_f = K₀` a.e., so `μ_f = k q̄/|q| = μ_{f₀}` a.e.; then
`f ∘ f₀⁻¹` has complex dilatation `0` a.e., is `1`-q.c., hence biholomorphic (`isKQCRS_one_iff`).  For `k = 0`,
`K[f] = 1` makes `f` conformal directly. -/
theorem utm_eq26_15_16_core [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ}
    {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k) {f : S₀ ≃ₜ S₁} (hf : IsQCRS f)
    (hL2 : quadDiffNorm q' ≤
      surfaceIntegral q' fun x z => ENNReal.ofReal (lambdaStretch q' q' (f₀.symm.trans f) x z))
    (heq : maxDilatationRS f = ENNReal.ofReal ((1 + k) / (1 - k))) :
    (∀ x : S₀, ∀ᵐ z ∂(volume.restrict (localMapDomain f x)),
      complexDilatation (localMapExpr f x) z = teichmullerBeltrami k q x z) ∧
      IsBiholomorphic (f₀.symm.trans f) := by
  have _ := hg
  have : CompactSpace S₀ := h₀.1
  have : CompactSpace S₁ := h₁.1
  have hK : IsKQCRS f ((1 + k) / (1 - k)) :=
    utm_d_isKQCRS_of_maxDil hf (s26u_one_le_K hf₀.k_nonneg hf₀.k_lt_one) heq.le
  have hμ := fun x => utm_d_mu_eq hf₀ hK hL2 x
  exact ⟨hμ, utm_d_biholomorphic hf₀ hf hμ⟩

/-- `f ∘ f₀⁻¹` is homotopic to the identity when `f₀ ≃ f` (scout A). -/
theorem utm_homotopic_symm_trans {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]
    {f₀ f : X ≃ₜ Y} (hhom : ContinuousMap.Homotopic (f₀ : C(X, Y)) (f : C(X, Y))) :
    ContinuousMap.Homotopic ((f₀.symm.trans f : Y ≃ₜ Y) : C(Y, Y)) (ContinuousMap.id Y) := by
  have h2 := ContinuousMap.Homotopic.comp hhom (ContinuousMap.Homotopic.refl (f₀.symm : C(Y, X)))
  have e1 : (f₀ : C(X, Y)).comp (f₀.symm : C(Y, X)) = ContinuousMap.id Y := by
    ext y
    simp
  have e2 : (f : C(X, Y)).comp (f₀.symm : C(Y, X)) = ((f₀.symm.trans f : Y ≃ₜ Y) : C(Y, Y)) := rfl
  rw [e1, e2] at h2
  exact h2.symm

/-- The terminal differential of a Teichmüller map is not zero (a regular point of `q ≠ 0` goes to a regular point
of `q'`). -/
theorem utm_terminal_ne [ConnectedSpace S₀] [T1Space S₀] {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ}
    {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k) : q' ≠ 0 := by
  obtain ⟨p⟩ : Nonempty S₀ := ConnectedSpace.toNonempty
  obtain ⟨p', hp'⟩ := (s26u_frequently_regular hf₀.initial hf₀.initial_ne p).exists
  have hreg := (hf₀.regular p' hp').1
  intro h0
  rw [h0] at hreg
  exact hreg rfl

/-- Lemma 26.2 on the target `S₁ = ℍ/Γ₁`, for `q'` and `f* = f ∘ f₀⁻¹` (glue: [P7], `eq23_4`, the `lemma26_2`
companion). -/
theorem utm_lemma26_2_target [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g) (h₁ : HasGenus S₁ g)
    {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k)
    {f : S₀ ≃ₜ S₁} (hf : IsQCRS f) (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S₁)) (f : C(S₀, S₁)))
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → S₁}
    (hp₁ : IsUniformization Γ₁ p₁) :
    quadDiffNorm q' ≤
      surfaceIntegral q' fun x z => ENNReal.ofReal (lambdaStretch q' q' (f₀.symm.trans f) x z) := by
  obtain ⟨K₀, hK₀⟩ := hf₀.qc
  obtain ⟨K, hK⟩ := hf
  have hqc : IsQCRS (f₀.symm.trans f) := ⟨_, (eq23_4 (utm_isKQCRS_symm hK₀) hK).1⟩
  exact lemma26_2_of_uniformization hg h₁ (f₀.symm.trans f) hqc (utm_homotopic_symm_trans hhom)
    hf₀.terminal (utm_terminal_ne hf₀) hp₁

/-- **Companion of `thm26_2_uniqueness`** (Theorem 26.2, (26.7)) for `S₁ = ℍ/Γ₁`: a Teichmüller map is the unique
extremal map of its homotopy class.

*Derivation note:* the book statement `thm26_2_uniqueness` follows from this companion plus
`thm22_3_classification` (a Fuchsian uniformization of the closed surface `S₁` of genus `g > 1`). -/
theorem thm26_2_uniqueness_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ}
    {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k) {f : S₀ ≃ₜ S₁} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S₁)) (f : C(S₀, S₁)))
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → S₁}
    (hp₁ : IsUniformization Γ₁ p₁) :
    ENNReal.ofReal ((1 + k) / (1 - k)) ≤ maxDilatationRS f ∧
      (maxDilatationRS f = ENNReal.ofReal ((1 + k) / (1 - k)) → ⇑f = ⇑f₀) := by
  have hL2 := utm_lemma26_2_target hg h₁ hf₀ hf hhom hp₁
  refine ⟨utm_thm26_2_ineq hg h₀ h₁ hf₀ hf hL2, fun heq => ?_⟩
  obtain ⟨-, hb⟩ := utm_eq26_15_16_core hg h₀ h₁ hf₀ hf hL2 heq
  have hid := thm23_1_cor_of_uniformization hg h₁ (f₀.symm.trans f) hb (utm_homotopic_symm_trans hhom) hp₁
  funext x
  have := congrFun hid (f₀ x)
  simpa [Homeomorph.trans_apply] using this

/-- **Theorem 26.2 (Teichmüller 唯一性定理)** (26.7).  Let `S₀` and `S` be closed Riemann surfaces of
genus `g > 1` and `f₀ : S₀ → S` a Teichmüller map (dilatation `K[f₀] = (1+k)/(1-k)`).  Then `f₀` is
the unique extremal map of its homotopy class: every `f ∈ [f₀]` satisfies `K[f] ≥ K[f₀]`, with
equality only for `f = f₀`. -/
theorem thm26_2_uniqueness [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ}
    {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k) {f : S₀ ≃ₜ S₁} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S₁)) (f : C(S₀, S₁))) :
    ENNReal.ofReal ((1 + k) / (1 - k)) ≤ maxDilatationRS f ∧
      (maxDilatationRS f = ENNReal.ofReal ((1 + k) / (1 - k)) → ⇑f = ⇑f₀) := by
  obtain ⟨Γ₁, _p, _hΓ, _hfree, hp₁⟩ :=
    s22hg_exists_fuchsian_uniformization (S := S₁) hg h₁
  exact thm26_2_uniqueness_of_uniformization hg h₀ h₁ hf₀ hf hhom hp₁


/-- **Companion of `eq26_15_16`** ((26.15)–(26.16), the equality case of Theorem 26.2) for `S₁ = ℍ/Γ₁`.

*Derivation note:* the book statement `eq26_15_16` follows from this companion plus `thm22_3_classification`
(a Fuchsian uniformization of `S₁`). -/
theorem eq26_15_16_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ}
    {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k) {f : S₀ ≃ₜ S₁} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S₁)) (f : C(S₀, S₁)))
    (heq : maxDilatationRS f = ENNReal.ofReal ((1 + k) / (1 - k)))
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → S₁}
    (hp₁ : IsUniformization Γ₁ p₁) :
    (∀ x : S₀, ∀ᵐ z ∂(volume.restrict (localMapDomain f x)),
      complexDilatation (localMapExpr f x) z = teichmullerBeltrami k q x z) ∧
      IsBiholomorphic (f₀.symm.trans f) := by
  exact utm_eq26_15_16_core hg h₀ h₁ hf₀ hf (utm_lemma26_2_target hg h₁ hf₀ hf hhom hp₁) heq

/-- (26.15)–(26.16) (the equality case of Theorem 26.2): if `K[f] = K[f₀]`, then almost everywhere
`|∂_ξ f̃| = |∂_ζ f̃| + |∂_ζ̄ f̃|` and `K₀ = (1 + |∂_ζ̄ f̃/∂_ζ f̃|)/(1 - |∂_ζ̄ f̃/∂_ζ f̃|)`, so
`∂_ζ̄ f̃/∂_ζ f̃ = k₀ = (K₀-1)/(K₀+1)` is a non-negative real constant: `f` has the same complex
dilatation as `f₀`, `f ∘ f₀⁻¹` is conformal and homotopic to the identity, hence the identity
(Corollary of Theorem 23.1). -/
theorem eq26_15_16 [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {f₀ : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ}
    {k : ℝ} (hf₀ : IsTeichmullerMap f₀ q q' k) {f : S₀ ≃ₜ S₁} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S₁)) (f : C(S₀, S₁)))
    (heq : maxDilatationRS f = ENNReal.ofReal ((1 + k) / (1 - k))) :
    (∀ x : S₀, ∀ᵐ z ∂(volume.restrict (localMapDomain f x)),
      complexDilatation (localMapExpr f x) z = teichmullerBeltrami k q x z) ∧
      IsBiholomorphic (f₀.symm.trans f) := by
  obtain ⟨Γ₁, _p, _hΓ, _hfree, hp₁⟩ :=
    s22hg_exists_fuchsian_uniformization (S := S₁) hg h₁
  exact eq26_15_16_of_uniformization hg h₀ h₁ hf₀ hf hhom heq hp₁


/-- **Companion of `teichmullerMap_isExtremal`** for `S₁ = ℍ/Γ₁`: a Teichmüller map is extremal, and the unique
extremal map, in its homotopy class.

*Derivation note:* the book statement `teichmullerMap_isExtremal` follows from this companion plus
`thm22_3_classification` (a Fuchsian uniformization of `S₁`). -/
theorem teichmullerMap_isExtremal_of_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ}
    {k : ℝ} (hf : IsTeichmullerMap f q q' k)
    {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → S₁}
    (hp₁ : IsUniformization Γ₁ p₁) :
    IsExtremalInHomotopyClass f ∧ ∀ h : S₀ ≃ₜ S₁, IsExtremalInHomotopyClass h →
      ContinuousMap.Homotopic (f : C(S₀, S₁)) (h : C(S₀, S₁)) → ⇑h = ⇑f := by
  have hmax : maxDilatationRS f = ENNReal.ofReal ((1 + k) / (1 - k)) := (teichmullerMap_beltrami hf).2
  have h262 : ∀ h : S₀ ≃ₜ S₁, IsQCRS h → ContinuousMap.Homotopic (f : C(S₀, S₁)) (h : C(S₀, S₁)) →
      ENNReal.ofReal ((1 + k) / (1 - k)) ≤ maxDilatationRS h ∧
        (maxDilatationRS h = ENNReal.ofReal ((1 + k) / (1 - k)) → ⇑h = ⇑f) :=
    fun h hh hfh => thm26_2_uniqueness_of_uniformization hg h₀ h₁ hf hh hfh hp₁
  refine ⟨⟨hf.qc, fun g' hg' hfg => hmax ▸ (h262 g' hg' hfg).1⟩, fun h hh hfh => ?_⟩
  have hle : maxDilatationRS h ≤ maxDilatationRS f := hh.2 f hf.qc hfh.symm
  exact (h262 h hh.1 hfh).2 (le_antisymm (hle.trans hmax.le) (h262 h hh.1 hfh).1)

/-- §26.4: a Teichmüller map is extremal in its homotopy class (and it is the unique extremal
map there). -/
theorem teichmullerMap_isExtremal [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ}
    {k : ℝ} (hf : IsTeichmullerMap f q q' k) :
    IsExtremalInHomotopyClass f ∧ ∀ h : S₀ ≃ₜ S₁, IsExtremalInHomotopyClass h →
      ContinuousMap.Homotopic (f : C(S₀, S₁)) (h : C(S₀, S₁)) → ⇑h = ⇑f := by
  obtain ⟨Γ₁, _p, _hΓ, _hfree, hp₁⟩ :=
    s22hg_exists_fuchsian_uniformization (S := S₁) hg h₁
  exact teichmullerMap_isExtremal_of_uniformization hg h₀ h₁ hf hp₁


/-- A uniformization `p : ℍ → S` followed by a biholomorphic homeomorphism `c : S ≃ₜ S'` is a uniformization of `S'`
with the same group. -/
theorem utm_isUniformization_comp {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {S' : Type*}
    [TopologicalSpace S'] [ChartedSpace ℂ S'] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) (c : S ≃ₜ S') (hc : IsBiholomorphic c) :
    IsUniformization Γ (c ∘ p) := by
  refine ⟨hp.1.homeomorph_comp c, hc.1.comp hp.2.1, c.surjective.comp hp.2.2.1, fun τ₁ τ₂ => ?_⟩
  rw [← hp.2.2.2 τ₁ τ₂]
  exact c.injective.eq_iff

/-! ## Part 5 pieces (moved from Part 5 of `Lemmas/UniformizedTeichmuller`): the Teichmüller coefficient, S3 at
a point, [S7a], [S7b] and the inverse trick -/

/-- The Teichmüller coefficient `k φ̄/|φ|` of a function `φ` on `ℍ` (`0` where `φ = 0`). -/
def utm_x_tcoeff (k : ℝ) (φ : ℂ → ℂ) : ℂ → ℂ := fun τ => (k : ℂ) * conj (φ τ) / (‖φ τ‖ : ℂ)

/-- The zeros in `ℍ` of the lift `ψ = utm_liftQD q p₀` of `q ≠ 0` form a countable set: `ψ` is holomorphic on the
connected `ℍ` and not identically zero there (`utm_liftQD_ne`), so its zeros are isolated. -/
theorem utm_x1_liftQD_zeros_countable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {q : S₀ → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) :
    {τ | τ ∈ upperHalf ∧ utm_liftQD q p₀ τ = 0}.Countable := by
  have han : AnalyticOnNhd ℂ (utm_liftQD q p₀) upperHalf :=
    (utm_liftQD_differentiableOn hq hp₀).analyticOnNhd isOpen_upperHalf
  obtain ⟨z₁, hz₁, hψ⟩ := utm_liftQD_ne hq hne hp₀
  have hpre : IsPreconnected upperHalf := (convex_halfSpace_im_gt 0).isPreconnected
  have hdisc : DiscreteTopology {τ | τ ∈ upperHalf ∧ utm_liftQD q p₀ τ = 0} := by
    refine discreteTopology_subtype_iff.2 fun z hz => ?_
    have hw : ∀ᶠ w in 𝓝[≠] z, utm_liftQD q p₀ w ≠ 0 := by
      rcases (han z hz.1).eventually_eq_zero_or_eventually_ne_zero with h | h
      · exact absurd (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hz.1 h hz₁) hψ
      · exact h
    rw [inf_principal_eq_bot]
    filter_upwards [hw] with w hw hwZ
    exact hw hwZ.2
  exact Set.countable_coe_iff.1 (TopologicalSpace.separableSpace_iff_countable.1 inferInstance)

/-- **S3 at a point.**  At `τ ∈ ℍ` with `ψ(τ) ≠ 0` (`ψ = utm_liftQD q p₀`), the dilatation of
`w ↦ φ_{f(p̂ τ)}(f(p̂ w))` at `τ` is `k ψ̄(τ)/|ψ(τ)|`: near `τ` the map is `L_f ∘ h`, `h = φ_x ∘ p̂` (`x = p̂ τ`) a
local biholomorphism, so the dilatation is `μ_{L_f}(h τ) conj h'(τ)/h'(τ)` (`s23_dilatation_comp_right`), with
`μ_{L_f}(h τ) = k q̄ₓ/|qₓ|` at `h τ = φ_x(x)` (`s26b_pointwise`) and `ψ(τ) = qₓ(h τ) h'(τ)²` (`utm_liftQD_local`). -/
theorem utm_x1_lift_pointwise [IsManifold 𝓘(ℂ) ω S₀] {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} (hp₀ : IsUniformization Γ₀ p₀) {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ}
    {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf : IsTeichmullerMap f q q' k) {τ : ℂ} (hτ : τ ∈ upperHalf)
    (hψ : utm_liftQD q p₀ τ ≠ 0) :
    utm_x_tcoeff k (utm_liftQD q p₀) τ =
      complexDilatation (fun w => chartAt ℂ (f (utm_pext p₀ τ)) (f (utm_pext p₀ w))) τ := by
  have hτ' : p₀ ⟨τ, hτ⟩ = utm_pext p₀ τ := by
    have h : (0 : ℝ) < τ.im := hτ
    simp only [utm_pext, h, ↓reduceDIte]
  obtain ⟨U, hUo, hτU, -, -, hU⟩ :=
    utm_liftQD_local hf.initial hp₀ ⟨τ, hτ⟩ (utm_pext p₀ τ) (by rw [hτ']; exact mem_chart_source ℂ _)
  obtain ⟨-, -, hd0, hψeq⟩ := hU τ hτU
  have hd : DifferentiableOn ℂ (fun v => chartAt ℂ (utm_pext p₀ τ) (utm_pext p₀ v)) U :=
    fun w hw => (hU w hw).2.1.differentiableAt.differentiableWithinAt
  have hs : HasStrictDerivAt (fun v => chartAt ℂ (utm_pext p₀ τ) (utm_pext p₀ v))
      (deriv (fun v => chartAt ℂ (utm_pext p₀ τ) (utm_pext p₀ v)) τ) τ :=
    (hd.analyticAt (hUo.mem_nhds hτU)).hasStrictDerivAt
  have hq0 : q (utm_pext p₀ τ) (chartAt ℂ (utm_pext p₀ τ) (utm_pext p₀ τ)) ≠ 0 := by
    intro h0
    apply hψ
    rw [hψeq, h0, zero_mul]
  -- near `τ` the map is `L_f ∘ h`
  have hev : (fun w => chartAt ℂ (f (utm_pext p₀ τ)) (f (utm_pext p₀ w))) =ᶠ[𝓝 τ]
      localMapExpr f (utm_pext p₀ τ) ∘ fun v => chartAt ℂ (utm_pext p₀ τ) (utm_pext p₀ v) := by
    filter_upwards [hUo.mem_nhds hτU] with w hw
    show chartAt ℂ (f (utm_pext p₀ τ)) (f (utm_pext p₀ w)) = chartAt ℂ (f (utm_pext p₀ τ))
      (f ((chartAt ℂ (utm_pext p₀ τ)).symm (chartAt ℂ (utm_pext p₀ τ) (utm_pext p₀ w))))
    rw [(chartAt ℂ (utm_pext p₀ τ)).left_inv (hU w hw).1]
  have h1 : complexDilatation (fun w => chartAt ℂ (f (utm_pext p₀ τ)) (f (utm_pext p₀ w))) τ =
      complexDilatation (localMapExpr f (utm_pext p₀ τ) ∘ fun v => chartAt ℂ (utm_pext p₀ τ) (utm_pext p₀ v)) τ := by
    simp only [complexDilatation, dz, dzbar, hev.fderiv_eq]
  rw [h1, s23_dilatation_comp_right hs.hasDerivAt.differentiableAt (hs.to_localInverse hd0).hasDerivAt.differentiableAt
    (hs.eventually_left_inverse hd0) (hs.eventually_right_inverse hd0),
    (s26b_pointwise hf (utm_pext p₀ τ) (s23_h_center f (utm_pext p₀ τ)).1 hq0).1]
  unfold utm_x_tcoeff teichmullerBeltrami
  rw [hψeq, teichmullerBeltrami_transform_aux, zpow_neg_one, zpow_one]
  ring

/-- The new parameter of a regular point, applied twice with a rotation: `S_k(i S_k(η)) = i K η`,
`K = (1+k)/(1-k)` (`S_k(a + ib) = K a + ib`). -/
theorem utm_x1_teichStretch_I {k : ℝ} (hk : k < 1) (η : ℂ) :
    teichStretch k (I * teichStretch k η) = I * (((1 + k) / (1 - k) : ℝ) : ℂ) * η := by
  have h1 : (1 - (k : ℂ)) ≠ 0 := by
    have : (1 - k : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  unfold teichStretch
  simp only [map_mul, map_div₀, map_add, map_sub, map_one, Complex.conj_I, Complex.conj_ofReal,
    Complex.conj_conj]
  push_cast
  field_simp
  ring_nf

/-- The order of a zero of a quadratic differential is unique. -/
theorem utm_x1_order_unique {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {q : S → ℂ → ℂ} {p : S}
    {m n : ℕ} (hm : IsZeroOfOrder q p m) (hn : IsZeroOfOrder q p n) : m = n := by
  unfold IsZeroOfOrder at hm hn
  rw [hm] at hn
  exact_mod_cast hn

/-- For a Teichmüller map `f`, the order of `q` at `f⁻¹ p` is the order of `q'` at `p`. -/
theorem utm_x1_zero_symm [T2Space S₀] [ConnectedSpace S₀] {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ}
    {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf : IsTeichmullerMap f q q' k) (p : S₁) (n : ℕ)
    (hn : IsZeroOfOrder q' p n) : IsZeroOfOrder q (f.symm p) n := by
  obtain ⟨m, _ζ, _Z, hD⟩ := s26d_a_data_exists hf.initial hf.initial_ne (f.symm p)
  have h1 := hf.zero _ m hD.order
  rw [f.apply_symm_apply] at h1
  rw [← utm_x1_order_unique h1 hn]
  exact hD.order

/-- The local expression of `f⁻¹` at `p` is continuous at `φ_p(p)`, tends to `φ_x(x)` there (`x = f⁻¹ p`), and is a
right inverse of the local expression of `f` at `x` near `φ_p(p)`. -/
theorem utm_x1_localMapExpr_symm (f : S₀ ≃ₜ S₁) (p : S₁) :
    Tendsto (localMapExpr f.symm p) (𝓝 (chartAt ℂ p p)) (𝓝 (chartAt ℂ (f.symm p) (f.symm p))) ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ p p), localMapExpr f (f.symm p) (localMapExpr f.symm p z) = z := by
  obtain ⟨hz, hcen⟩ := s23_h_center f.symm p
  have hgc : ContinuousAt (localMapExpr f.symm p) (chartAt ℂ p p) := by
    have h1 : ContinuousAt (fun z => f.symm ((chartAt ℂ p).symm z)) (chartAt ℂ p p) :=
      f.symm.continuous.continuousAt.comp ((chartAt ℂ p).continuousAt_symm hz.1)
    exact ContinuousAt.comp (g := chartAt ℂ (f.symm p)) (f := fun z => f.symm ((chartAt ℂ p).symm z))
      ((chartAt ℂ (f.symm p)).continuousAt hz.2) h1
  refine ⟨?_, ?_⟩
  · have h := hgc.tendsto
    rwa [hcen] at h
  · filter_upwards [(s23_localMapDomain_isOpen f.symm.continuous p).mem_nhds hz] with z hz'
    have h2 : f.symm ((chartAt ℂ p).symm z) ∈ (chartAt ℂ (f.symm p)).source := hz'.2
    show chartAt ℂ (f (f.symm p)) (f ((chartAt ℂ (f.symm p)).symm
      (chartAt ℂ (f.symm p) (f.symm ((chartAt ℂ p).symm z))))) = z
    rw [(chartAt ℂ (f.symm p)).left_inv h2, f.apply_symm_apply, f.apply_symm_apply,
      (chartAt ℂ p).right_inv hz'.1]

/-- [S7a, stub] **The inverse of a Teichmüller map is a Teichmüller map**, with the same `k`, initial differential
`-q'` and terminal differential `-K² q`, `K = (1+k)/(1-k)`.

*Truth:* in natural parameters `f` is `ζ ↦ ζ' = (ζ + k ζ̄)/(1-k)`, i.e. `ξ' = K ξ`, `η' = η`.  Put `ω = i ζ'` (a
natural parameter of `-q'` at `p' = f p`) and `ω' = i K ζ` (one of `-K² q` at `p`); then
`ω' = teichStretch k ω` pointwise (`Re ω' = -K η = K Re ω`, `Im ω' = K ξ = ξ' = Im ω`), and near `φ_{p'}(p')` the
local expression of `f⁻¹` at `p'` inverts that of `f` at `p`.  Regular points and zero orders correspond (`f` is
bijective, `q ≠ 0` has only isolated zeros of finite order on the connected `S₀`, `s26u_frequently_regular`), and
negation/scaling does not change orders.  `f⁻¹` is q.c. (`s29_m_isKQCRS_symm`).

*Route/reuse:* S26 `IsTeichmullerMap` (l.2440), `IsNaturalParameterAt` (l.929), `teichStretch` (l.447),
`s26u_frequently_regular` (l.1857), `s26u_isRegularPoint_iff` (l.1789); S29 `s29_m_isKQCRS_symm` (l.132); Mathlib
`meromorphicOrderAt` of `-f` and `c • f`.  *Estimate:* 0.3–0.5k.

*Walls:* none: a local computation with the given map, no homotopy, no uniformization (no W-UC, W-QC, W-TOP, W-RR,
W-IoD). -/
theorem utm_x_teichmullerMap_symm [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ}
    {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf : IsTeichmullerMap f q q' k) :
    IsTeichmullerMap f.symm (-q') (((-(((1 + k) / (1 - k)) ^ 2) : ℝ) : ℂ) • q) k := by
  have hk1 : 0 < 1 - k := by linarith [hf.k_lt_one]
  have hKpos : 0 < (1 + k) / (1 - k) := div_pos (by linarith [hf.k_nonneg]) hk1
  have hc0 : ((-(((1 + k) / (1 - k)) ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast neg_ne_zero.2 (pow_ne_zero 2 hKpos.ne')
  have hneg : -q' = (-1 : ℂ) • q' := (neg_one_smul ℂ q').symm
  have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
  have hq'ne : q' ≠ 0 := utm_terminal_ne hf
  obtain ⟨K₀, hK₀⟩ := hf.qc
  refine ⟨⟨K₀, s29_m_isKQCRS_symm hK₀⟩, (holQuadDiffSubmodule S₁).neg_mem hf.terminal, neg_ne_zero.2 hq'ne,
    (holQuadDiffSubmodule S₀).smul_mem _ hf.initial, hf.k_nonneg, hf.k_lt_one, fun p hp => ?_, fun p n hn => ?_⟩
  · have hp' : IsRegularPoint q' p := by
      rw [hneg] at hp
      exact (s26_isRegularPoint_smul hm1 p).1 hp
    -- `f⁻¹ p` is a regular point of `q`: its order is that of `q'` at `p`, which is `0`
    have hxr : IsRegularPoint q (f.symm p) := by
      obtain ⟨m', _ζ', _Z', hD'⟩ := s26d_a_data_exists hf.terminal hq'ne p
      obtain ⟨m, _ζ, _Z, hD⟩ := s26d_a_data_exists hf.initial hf.initial_ne (f.symm p)
      have h0 := utm_x1_zero_symm hf p m' hD'.order
      rw [hD.regular_iff, utm_x1_order_unique hD.order h0]
      exact hD'.regular_iff.1 hp'
    obtain ⟨-, ζ, ζ', hζ, hζ', hrel⟩ := hf.regular (f.symm p) hxr
    rw [f.apply_symm_apply] at hζ'
    obtain ⟨hTend, hcancel⟩ := utm_x1_localMapExpr_symm f p
    refine ⟨(s26_isRegularPoint_smul hc0 (f.symm p)).2 hxr, fun z => I * ζ' z,
      fun z => I * (((1 + k) / (1 - k) : ℝ) : ℂ) * ζ z, ?_, ?_, ?_⟩
    · obtain ⟨ha, h0, hd, hev⟩ := hζ'
      refine ⟨analyticAt_const.mul ha, by simp [h0], ?_, ?_⟩
      · rw [deriv_const_mul_field']
        exact mul_ne_zero I_ne_zero hd
      · filter_upwards [hev] with z hz
        rw [deriv_const_mul_field', mul_pow, hz, I_sq, Pi.neg_apply, Pi.neg_apply]
        ring
    · obtain ⟨ha, h0, hd, hev⟩ := hζ
      have hK0 : (((1 + k) / (1 - k) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hKpos.ne'
      refine ⟨analyticAt_const.mul ha, by simp [h0], ?_, ?_⟩
      · rw [deriv_const_mul_field']
        exact mul_ne_zero (mul_ne_zero I_ne_zero hK0) hd
      · filter_upwards [hev] with z hz
        rw [deriv_const_mul_field', mul_pow, hz, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, mul_pow, I_sq]
        push_cast
        ring
    · filter_upwards [hTend.eventually hrel, hcancel] with z h1 h2
      rw [h2] at h1
      show I * (((1 + k) / (1 - k) : ℝ) : ℂ) * ζ (localMapExpr f.symm p z) = teichStretch k (I * ζ' z)
      rw [h1, utm_x1_teichStretch_I hf.k_lt_one]
  · have hn' : IsZeroOfOrder q' p n := by
      rw [hneg] at hn
      exact (s26_isZeroOfOrder_smul hm1 p n).1 hn
    exact (s26_isZeroOfOrder_smul hc0 (f.symm p) n).2 (utm_x1_zero_symm hf p n hn')

/-- The local expression at `y` of a holomorphic homeomorphism `c` is holomorphic and injective on its (open) domain
(`s23_mdifferentiableAt_iff`). -/
theorem utm_x1_biholo_expr {S₂ : Type*} [TopologicalSpace S₂] [ChartedSpace ℂ S₂] [IsManifold 𝓘(ℂ) ω S₁]
    [IsManifold 𝓘(ℂ) ω S₂] {c : S₁ ≃ₜ S₂} (hc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) c) (y : S₁) :
    DifferentiableOn ℂ (localMapExpr c y) (localMapDomain c y) ∧ InjOn (localMapExpr c y) (localMapDomain c y) := by
  refine ⟨fun u hu => ?_, fun u hu v hv huv => ?_⟩
  · have hd := ((s23_mdifferentiableAt_iff (f := c) (y := c y) ((chartAt ℂ y).map_target hu.1) hu.2).1
      (hc ((chartAt ℂ y).symm u))).2
    rw [(chartAt ℂ y).right_inv hu.1] at hd
    exact hd.differentiableWithinAt
  · have hu2 : c ((chartAt ℂ y).symm u) ∈ (chartAt ℂ (c y)).source := hu.2
    have hv2 : c ((chartAt ℂ y).symm v) ∈ (chartAt ℂ (c y)).source := hv.2
    have h1 : (chartAt ℂ y).symm u = (chartAt ℂ y).symm v := c.injective ((chartAt ℂ (c y)).injOn hu2 hv2 huv)
    rw [← (chartAt ℂ y).right_inv hu.1, ← (chartAt ℂ y).right_inv hv.1, h1]

/-- The complex dilatation is unchanged by post-composition with a holomorphic homeomorphism `c`: at a point `w` of
the domains of the local expressions of `f` and `c ∘ f` at `x`, near `w` the latter is `T ∘ L_f` with
`T = localMapExpr c (f x)` holomorphic and injective (`s23_dilatation_comp_left`; a local inverse of `T` by
`utm_a_local_inverse`). -/
theorem utm_x1_dilatation_comp_biholo {S₂ : Type*} [TopologicalSpace S₂] [ChartedSpace ℂ S₂]
    [IsManifold 𝓘(ℂ) ω S₁] [IsManifold 𝓘(ℂ) ω S₂] {f : S₀ → S₁} (hf : Continuous f) {c : S₁ ≃ₜ S₂}
    (hc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) c) (x : S₀) {w : ℂ} (hw : w ∈ localMapDomain f x)
    (hw' : w ∈ localMapDomain (c ∘ f) x) :
    complexDilatation (localMapExpr (c ∘ f) x) w = complexDilatation (localMapExpr f x) w := by
  have hwf : f ((chartAt ℂ x).symm w) ∈ (chartAt ℂ (f x)).source := hw.2
  have huD : localMapExpr f x w ∈ localMapDomain c (f x) := by
    refine ⟨(chartAt ℂ (f x)).map_source hwf, ?_⟩
    show c ((chartAt ℂ (f x)).symm (chartAt ℂ (f x) (f ((chartAt ℂ x).symm w)))) ∈ (chartAt ℂ (c (f x))).source
    rw [(chartAt ℂ (f x)).left_inv hwf]
    exact hw'.2
  obtain ⟨hTd, hTi⟩ := utm_x1_biholo_expr hc (f x)
  have hDo : IsOpen (localMapDomain c (f x)) := s23_localMapDomain_isOpen c.continuous (f x)
  have hT0 : deriv (localMapExpr c (f x)) (localMapExpr f x w) ≠ 0 := deriv_ne_zero_of_injOn hDo hTd hTi huD
  obtain ⟨L, hL, hLT⟩ := utm_a_local_inverse hDo huD hTd hT0
  have hgc : ContinuousAt (localMapExpr f x) w := by
    have h1 : ContinuousAt (fun z => f ((chartAt ℂ x).symm z)) w :=
      hf.continuousAt.comp ((chartAt ℂ x).continuousAt_symm hw.1)
    exact ContinuousAt.comp (g := chartAt ℂ (f x)) (f := fun z => f ((chartAt ℂ x).symm z))
      ((chartAt ℂ (f x)).continuousAt hwf) h1
  have hev : localMapExpr (c ∘ f) x =ᶠ[𝓝 w] localMapExpr c (f x) ∘ localMapExpr f x := by
    filter_upwards [(s23_localMapDomain_isOpen hf x).mem_nhds hw] with v hv
    have hv2 : f ((chartAt ℂ x).symm v) ∈ (chartAt ℂ (f x)).source := hv.2
    show chartAt ℂ (c (f x)) (c (f ((chartAt ℂ x).symm v))) =
      chartAt ℂ (c (f x)) (c ((chartAt ℂ (f x)).symm (chartAt ℂ (f x) (f ((chartAt ℂ x).symm v)))))
    rw [(chartAt ℂ (f x)).left_inv hv2]
  have h1 : complexDilatation (localMapExpr (c ∘ f) x) w =
      complexDilatation (localMapExpr c (f x) ∘ localMapExpr f x) w := by
    simp only [complexDilatation, dz, dzbar, hev.fderiv_eq]
  rw [h1]
  exact s23_dilatation_comp_left hgc (hTd.differentiableAt (hDo.mem_nhds huD)) hL.hasDerivAt.differentiableAt hLT

/-- Equal Teichmüller coefficients `k ā/|a| = k b̄/|b|` (`k ≠ 0`, `a, b ≠ 0`) force `b/a` to be a positive real. -/
theorem utm_x1_ratio_pos {k : ℝ} (hk : k ≠ 0) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : (k : ℂ) * conj a / (‖a‖ : ℂ) = (k : ℂ) * conj b / (‖b‖ : ℂ)) :
    (b / a).im = 0 ∧ 0 < (b / a).re := by
  have hna : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 ha
  have hnb : (‖b‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hb
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  rw [div_eq_div_iff hna hnb] at h
  have h1 : conj a * (‖b‖ : ℂ) = conj b * (‖a‖ : ℂ) := mul_left_cancel₀ hk' (by linear_combination h)
  have h2 := congrArg conj h1
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2
  have h3 : b / a = ((‖b‖ / ‖a‖ : ℝ) : ℂ) := by
    push_cast
    rw [div_eq_div_iff ha hna]
    linear_combination -h2
  rw [h3, Complex.ofReal_im, Complex.ofReal_re]
  exact ⟨rfl, div_pos (norm_pos_iff.2 hb) (norm_pos_iff.2 ha)⟩

/-- **Plane step of S7b.**  If `g₁`, `g₂` are holomorphic on an open `V ∋ z₀` and, on a punctured neighbourhood of
`z₀`, `g₁ ≠ 0` and `g₂/g₁` is a positive real, then `g₂ = r g₁` near `z₀` for some `r > 0` (the open mapping theorem
at a point `w₁ ≠ z₀`, then the identity theorem on a disc around `z₀`). -/
theorem utm_x1_eq_smul_local {g₁ g₂ : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) {z₀ : ℂ} (hz₀ : z₀ ∈ V)
    (h₁ : DifferentiableOn ℂ g₁ V) (h₂ : DifferentiableOn ℂ g₂ V)
    (hpos : ∀ᶠ w in 𝓝[≠] z₀, g₁ w ≠ 0 ∧ (g₂ w / g₁ w).im = 0 ∧ 0 < (g₂ w / g₁ w).re) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ w in 𝓝 z₀, g₂ w = r * g₁ w := by
  have hgood : {w | w ∈ V ∧ (g₁ w ≠ 0 ∧ (g₂ w / g₁ w).im = 0 ∧ 0 < (g₂ w / g₁ w).re)} ∈ 𝓝[≠] z₀ :=
    Filter.inter_mem (nhdsWithin_le_nhds (hV.mem_nhds hz₀)) hpos
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hgood
  have hball : ball z₀ ε ⊆ V := by
    intro w hw
    by_cases hwz : w = z₀
    · rw [hwz]
      exact hz₀
    · exact (hsub ⟨hw, hwz⟩).1
  have hNo : IsOpen (ball z₀ ε ∩ {z₀}ᶜ) := isOpen_ball.inter isOpen_compl_singleton
  have hgN : ∀ w ∈ ball z₀ ε ∩ {z₀}ᶜ, g₁ w ≠ 0 ∧ (g₂ w / g₁ w).im = 0 ∧ 0 < (g₂ w / g₁ w).re :=
    fun w hw => (hsub hw).2
  have hw₁N : z₀ + ((ε / 2 : ℝ) : ℂ) ∈ ball z₀ ε ∩ {z₀}ᶜ := by
    refine ⟨?_, fun h => ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    · have h' : ((ε / 2 : ℝ) : ℂ) = 0 := by
        have h'' : z₀ + ((ε / 2 : ℝ) : ℂ) = z₀ := h
        linear_combination h''
      have : ε / 2 = 0 := by exact_mod_cast h'
      linarith
  set w₁ := z₀ + ((ε / 2 : ℝ) : ℂ) with hw₁
  have han₁ : AnalyticOnNhd ℂ g₁ (ball z₀ ε) := fun w hw => h₁.analyticAt (hV.mem_nhds (hball hw))
  have han₂ : AnalyticOnNhd ℂ g₂ (ball z₀ ε) := fun w hw => h₂.analyticAt (hV.mem_nhds (hball hw))
  have hh : AnalyticAt ℂ (fun w => g₂ w / g₁ w) w₁ :=
    (han₂ w₁ hw₁N.1).div (han₁ w₁ hw₁N.1) (hgN w₁ hw₁N).1
  have hreal : ∀ᶠ w in 𝓝 w₁, (g₂ w / g₁ w).im = 0 := by
    filter_upwards [hNo.mem_nhds hw₁N] with w hw using (hgN w hw).2.1
  rcases hh.eventually_constant_or_nhds_le_map_nhds with hc | hle
  · refine ⟨(g₂ w₁ / g₁ w₁).re, (hgN w₁ hw₁N).2.2, ?_⟩
    have hrc : g₂ w₁ / g₁ w₁ = (((g₂ w₁ / g₁ w₁).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [(hgN w₁ hw₁N).2.1])
    have hev : g₂ =ᶠ[𝓝 w₁] fun w => (((g₂ w₁ / g₁ w₁).re : ℝ) : ℂ) * g₁ w := by
      filter_upwards [hc, hNo.mem_nhds hw₁N] with w hw hwN
      have hg1 := (hgN w hwN).1
      have hw' : g₂ w / g₁ w = (((g₂ w₁ / g₁ w₁).re : ℝ) : ℂ) := hw.trans hrc
      rw [div_eq_iff hg1] at hw'
      exact hw'
    have heq := han₂.eqOn_of_preconnected_of_eventuallyEq (g := fun w => (((g₂ w₁ / g₁ w₁).re : ℝ) : ℂ) * g₁ w)
      (fun w hw => analyticAt_const.mul (han₁ w hw)) (convex_ball z₀ ε).isPreconnected hw₁N.1 hev
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with w hw using heq hw
  · exfalso
    have hmem : {v : ℂ | v.im = 0} ∈ map (fun w => g₂ w / g₁ w) (𝓝 w₁) := hreal
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 (hle hmem)
    have hv : g₂ w₁ / g₁ w₁ + ((δ / 2 : ℝ) : ℂ) * I ∈ ball (g₂ w₁ / g₁ w₁) δ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      linarith
    have him : (g₂ w₁ / g₁ w₁ + ((δ / 2 : ℝ) : ℂ) * I).im = 0 := hδsub hv
    rw [add_im, (hgN w₁ hw₁N).2.1, zero_add, mul_im, ofReal_re, ofReal_im, I_re, I_im] at him
    linarith

/-- [S7b, stub] **Teichmüller maps which differ by a conformal map have positively proportional initial
differentials** (for the same `k > 0`): if `f₂ = c ∘ f₁` with `c` biholomorphic, then `q₂ = r q₁`, `r > 0`.

*Truth:* the local expressions of `f₂` and `f₁` at `x` differ by the holomorphic post-composition
`φ ∘ c ∘ φ⁻¹`, so their dilatations agree (`s23_dilatation_comp_left`); by `teichmullerMap_beltrami` both are
`k q̄ᵢ/|qᵢ|` a.e. near `φ_x(x)`, and `k > 0` gives `q₁/|q₁| = q₂/|q₂|` a.e.  Off the isolated zeros of `q₁` the
holomorphic `q₂/q₁` then takes values in `(0, ∞)`, so it is locally constant (open mapping theorem); the transformation
law (`s26u_law`) shows the constants agree on overlapping charts, and `S₀` is connected.

*Route/reuse:* S26 `teichmullerMap_beltrami` (l.2699), `s26u_law` (l.1779), `s26u_frequently_regular` (l.1857); S23
`s23_dilatation_comp_left` (l.154), `utm_d_exprAt` (this file l.1908, the same comparison of expressions); Mathlib
`AnalyticAt.eventually_constant_or_nhds_le_map_nhds`.  *Estimate:* 0.3–0.5k.

*Walls:* none: a local computation plus connectedness of `S₀` (no W-UC, W-QC, W-TOP, W-RR, W-IoD). -/
theorem utm_x_eq_smul_of_trans [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {S₂ : Type*} [TopologicalSpace S₂]
    [ChartedSpace ℂ S₂] [T2Space S₂] [ConnectedSpace S₂] [IsManifold 𝓘(ℂ) ω S₂] {f₁ : S₀ ≃ₜ S₁}
    {f₂ : S₀ ≃ₜ S₂} {q₁ q₂ : S₀ → ℂ → ℂ} {q'₁ : S₁ → ℂ → ℂ} {q'₂ : S₂ → ℂ → ℂ} {k : ℝ} (hk : 0 < k)
    (hf₁ : IsTeichmullerMap f₁ q₁ q'₁ k) (hf₂ : IsTeichmullerMap f₂ q₂ q'₂ k) {c : S₁ ≃ₜ S₂}
    (hc : IsBiholomorphic c) (hfc : ⇑f₂ = ⇑(f₁.trans c)) : ∃ r : ℝ, 0 < r ∧ q₂ = (r : ℂ) • q₁ := by
  have hq₁ : IsDiffFamily 2 0 q₁ ∧ ∀ x : S₀, DifferentiableOn ℂ (q₁ x) (chartAt ℂ x).target := hf₁.initial
  have hq₂ : IsDiffFamily 2 0 q₂ ∧ ∀ x : S₀, DifferentiableOn ℂ (q₂ x) (chartAt ℂ x).target := hf₂.initial
  have hf₂c : (⇑f₂ : S₀ → S₂) = ⇑c ∘ ⇑f₁ := by
    rw [hfc]
    rfl
  -- the local step: `q₂ = r q₁` near every point, read in the preferred charts
  have hloc : ∀ p : S₀, ∃ r : ℝ, 0 < r ∧
      ∀ᶠ p' in 𝓝 p, q₂ p' (chartAt ℂ p' p') = r * q₁ p' (chartAt ℂ p' p') := by
    intro p
    have hz₀ : chartAt ℂ p p ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    have hl : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
    have hn₁ := s26u_eventually_ne_zero hf₁.initial p hz₀
      (by rw [hl]; exact s26u_frequently_regular hf₁.initial hf₁.initial_ne p)
    have hn₂ := s26u_eventually_ne_zero hf₂.initial p hz₀
      (by rw [hl]; exact s26u_frequently_regular hf₂.initial hf₂.initial_ne p)
    have hD₁ := (s23_localMapDomain_isOpen f₁.continuous p).mem_nhds (s23_h_center f₁ p).1
    have hD₂ := (s23_localMapDomain_isOpen f₂.continuous p).mem_nhds (s23_h_center f₂ p).1
    have hpos : ∀ᶠ w in 𝓝[≠] chartAt ℂ p p,
        q₁ p w ≠ 0 ∧ (q₂ p w / q₁ p w).im = 0 ∧ 0 < (q₂ p w / q₁ p w).re := by
      filter_upwards [hn₁, hn₂, nhdsWithin_le_nhds hD₁, nhdsWithin_le_nhds hD₂] with w h1 h2 hw1 hw2
      have e1 := (s26b_pointwise hf₁ p hw1 h1).1
      have e2 := (s26b_pointwise hf₂ p hw2 h2).1
      have hw2' : w ∈ localMapDomain (⇑c ∘ ⇑f₁) p := by
        rw [← hf₂c]
        exact hw2
      have e3 : complexDilatation (localMapExpr f₂ p) w = complexDilatation (localMapExpr f₁ p) w := by
        rw [hf₂c]
        exact utm_x1_dilatation_comp_biholo f₁.continuous hc.1 p hw1 hw2'
      rw [e3, e1] at e2
      exact ⟨h1, utm_x1_ratio_pos hk.ne' h1 h2 e2⟩
    obtain ⟨r, hr, hev⟩ := utm_x1_eq_smul_local (chartAt ℂ p).open_target hz₀ (hq₁.2 p) (hq₂.2 p) hpos
    refine ⟨r, hr, ?_⟩
    have hcont : Tendsto (chartAt ℂ p) (𝓝 p) (𝓝 (chartAt ℂ p p)) :=
      ((chartAt ℂ p).continuousAt (mem_chart_source ℂ p)).tendsto
    filter_upwards [hcont.eventually hev, (chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)]
      with p' h1 h2
    have hw : chartAt ℂ p' p' ∈ (chartAt ℂ p').target := (chartAt ℂ p').map_source (mem_chart_source ℂ p')
    have hl' : (chartAt ℂ p').symm (chartAt ℂ p' p') = p' := (chartAt ℂ p').left_inv (mem_chart_source ℂ p')
    have hws : (chartAt ℂ p').symm (chartAt ℂ p' p') ∈ (chartAt ℂ p).source := by
      rw [hl']
      exact h2
    have hT : chartTransition p p' (chartAt ℂ p' p') = chartAt ℂ p p' := by
      show chartAt ℂ p ((chartAt ℂ p').symm (chartAt ℂ p' p')) = _
      rw [hl']
    rw [s26u_law hf₂.initial p' p hw hws, s26u_law hf₁.initial p' p hw hws, hT, h1]
    ring
  -- the constant is locally unique (regular points of `q₁` accumulate everywhere)
  have huniq : ∀ (r s : ℝ) (p : S₀), (∀ᶠ p' in 𝓝 p, q₂ p' (chartAt ℂ p' p') = r * q₁ p' (chartAt ℂ p' p')) →
      (∀ᶠ p' in 𝓝 p, q₂ p' (chartAt ℂ p' p') = s * q₁ p' (chartAt ℂ p' p')) → r = s := by
    intro r s p hr hs
    obtain ⟨p', hreg, e1, e2⟩ :=
      ((s26u_frequently_regular hf₁.initial hf₁.initial_ne p).and_eventually (hr.and hs)).exists
    have h := mul_right_cancel₀ hreg (e1.symm.trans e2)
    exact_mod_cast h
  -- hence it is globally constant on the connected `S₀`
  obtain ⟨p₀⟩ : Nonempty S₀ := ConnectedSpace.toNonempty
  obtain ⟨r₀, hr₀, hp₀⟩ := hloc p₀
  set O : Set S₀ := {p | ∀ᶠ p' in 𝓝 p, q₂ p' (chartAt ℂ p' p') = r₀ * q₁ p' (chartAt ℂ p' p')} with hOdef
  have hOo : IsOpen O := isOpen_setOfPred_eventually_nhds
  have hOc : IsClosed O := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro p hp
    obtain ⟨s, -, hs⟩ := hloc p
    filter_upwards [eventually_eventually_nhds.2 hs] with p'' hp''
    intro hmem
    apply hp
    have hrs : r₀ = s := huniq r₀ s p'' hmem hp''
    show ∀ᶠ p' in 𝓝 p, q₂ p' (chartAt ℂ p' p') = r₀ * q₁ p' (chartAt ℂ p' p')
    rw [hrs]
    exact hs
  have hp₀O : p₀ ∈ O := hp₀
  have hOu : O = univ := by
    rcases isClopen_iff.1 ⟨hOc, hOo⟩ with h | h
    · rw [h] at hp₀O
      exact absurd hp₀O (notMem_empty p₀)
    · exact h
  refine ⟨r₀, hr₀, ?_⟩
  funext x z
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hz : z ∈ (chartAt ℂ x).target
  · have hpO : (chartAt ℂ x).symm z ∈ O := by
      rw [hOu]
      exact mem_univ _
    have e : q₂ ((chartAt ℂ x).symm z) (chartAt ℂ ((chartAt ℂ x).symm z) ((chartAt ℂ x).symm z)) =
        r₀ * q₁ ((chartAt ℂ x).symm z) (chartAt ℂ ((chartAt ℂ x).symm z) ((chartAt ℂ x).symm z)) :=
      hpO.self_of_nhds
    have hzp : (chartAt ℂ x).symm z ∈ (chartAt ℂ ((chartAt ℂ x).symm z)).source := mem_chart_source ℂ _
    rw [s26u_law hf₂.initial x _ hz hzp, s26u_law hf₁.initial x _ hz hzp]
    have hT : chartTransition ((chartAt ℂ x).symm z) x z =
        chartAt ℂ ((chartAt ℂ x).symm z) ((chartAt ℂ x).symm z) := rfl
    rw [hT, e]
    ring
  · rw [hq₂.1.1 x z hz, hq₁.1.1 x z hz, mul_zero]

/-- From `c ∘ e₁ ≃ e₂` get `c⁻¹ ∘ e₂ ≃ e₁` (compose the homotopy with `c⁻¹`). -/
theorem utm_x_homotopic_trans_symm {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {e₁ : X ≃ₜ Y} {e₂ : X ≃ₜ Z} {c : Y ≃ₜ Z}
    (hhom : ContinuousMap.Homotopic ((e₁.trans c : X ≃ₜ Z) : C(X, Z)) (e₂ : C(X, Z))) :
    ContinuousMap.Homotopic ((e₂.trans c.symm : X ≃ₜ Y) : C(X, Y)) (e₁ : C(X, Y)) := by
  have h2 := ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl (c.symm : C(Z, Y))) hhom
  have ea : (c.symm : C(Z, Y)).comp ((e₁.trans c : X ≃ₜ Z) : C(X, Z)) = (e₁ : C(X, Y)) := by
    ext x
    simp
  have eb : (c.symm : C(Z, Y)).comp (e₂ : C(X, Z)) = ((e₂.trans c.symm : X ≃ₜ Y) : C(X, Y)) := rfl
  rw [ea, eb] at h2
  exact h2.symm

/-- `(1+a)/(1-a) = (1+b)/(1-b)` (as `ENNReal.ofReal` inequalities both ways) forces `a = b` for `0 ≤ a, b < 1`. -/
theorem utm_x_eq_of_ofReal_le {a b : ℝ} (ha₀ : 0 ≤ a) (ha : a < 1) (hb₀ : 0 ≤ b) (hb : b < 1)
    (hab : ENNReal.ofReal ((1 + a) / (1 - a)) ≤ ENNReal.ofReal ((1 + b) / (1 - b)))
    (hba : ENNReal.ofReal ((1 + b) / (1 - b)) ≤ ENNReal.ofReal ((1 + a) / (1 - a))) : a = b := by
  have hA : 0 ≤ (1 + a) / (1 - a) := div_nonneg (by linarith) (by linarith)
  have hB : 0 ≤ (1 + b) / (1 - b) := div_nonneg (by linarith) (by linarith)
  rw [ENNReal.ofReal_le_ofReal_iff hB, div_le_div_iff₀ (by linarith) (by linarith)] at hab
  rw [ENNReal.ofReal_le_ofReal_iff hA, div_le_div_iff₀ (by linarith) (by linarith)] at hba
  nlinarith

/-- **The inverse trick** (the uniqueness step of (27.15), for the target `S₀ = ℍ/Γ₀`).  Let `eᵢ : S₀ → Xᵢ` be
Teichmüller maps with constants `kᵢ` and `c : X₁ → X₂` biholomorphic with `c ∘ e₁ ≃ e₂`.  Then `K(k₁) ≤ K(k₂)`, and for
`k₁ = k₂`, `e₂ = c ∘ e₁`: `e₁⁻¹ : X₁ → S₀` is a Teichmüller map ([S7a]) homotopic to `e₂⁻¹ ∘ c`, whose dilatation is at
most `K[e₂⁻¹] = K(k₂)` (`s29_m_maxDil_conj_biholo`, `teichmullerMap_beltrami`), so
`thm26_2_uniqueness_of_uniformization` on the uniformized target `S₀` applies. -/
theorem utm_x_dil_le_of_equiv [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {X₁ X₂ : ClosedRS.{u}} {e₁ : S₀ ≃ₜ X₁.carrier}
    {e₂ : S₀ ≃ₜ X₂.carrier} {q₁ q₂ : S₀ → ℂ → ℂ} {q'₁ : X₁.carrier → ℂ → ℂ} {q'₂ : X₂.carrier → ℂ → ℂ}
    {k₁ k₂ : ℝ} (hT₁ : IsTeichmullerMap e₁ q₁ q'₁ k₁) (hT₂ : IsTeichmullerMap e₂ q₂ q'₂ k₂)
    {c : X₁.carrier ≃ₜ X₂.carrier} (hc : IsBiholomorphic c)
    (hhom : ContinuousMap.Homotopic ((e₁.trans c : S₀ ≃ₜ X₂.carrier) : C(S₀, X₂.carrier))
      (e₂ : C(S₀, X₂.carrier)))
    {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) :
    ENNReal.ofReal ((1 + k₁) / (1 - k₁)) ≤ ENNReal.ofReal ((1 + k₂) / (1 - k₂)) ∧
      (k₁ = k₂ → ⇑e₂ = ⇑(e₁.trans c)) := by
  have hX₁ : HasGenus X₁.carrier g := hasGenus_of_homeomorph hS e₁
  have hi₁ := utm_x_teichmullerMap_symm hT₁
  have hi₂ := utm_x_teichmullerMap_symm hT₂
  obtain ⟨hqcf, hle⟩ := s29_m_maxDil_conj_biholo hi₂.qc hc (c₂ := Homeomorph.refl S₀) isBiholomorphic_id
  have hhom' : ContinuousMap.Homotopic ((e₁.symm : X₁.carrier ≃ₜ S₀) : C(X₁.carrier, S₀))
      ((c.trans (e₂.symm.trans (Homeomorph.refl S₀)) : X₁.carrier ≃ₜ S₀) : C(X₁.carrier, S₀)) := by
    have h1 := ContinuousMap.Homotopic.comp
      (ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl (e₂.symm : C(X₂.carrier, S₀))) hhom)
      (ContinuousMap.Homotopic.refl (e₁.symm : C(X₁.carrier, S₀)))
    have ea : ((e₂.symm : C(X₂.carrier, S₀)).comp ((e₁.trans c : S₀ ≃ₜ X₂.carrier) : C(S₀, X₂.carrier))).comp
        (e₁.symm : C(X₁.carrier, S₀)) =
        ((c.trans (e₂.symm.trans (Homeomorph.refl S₀)) : X₁.carrier ≃ₜ S₀) : C(X₁.carrier, S₀)) := by
      ext x
      simp
    have eb : ((e₂.symm : C(X₂.carrier, S₀)).comp (e₂ : C(S₀, X₂.carrier))).comp
        (e₁.symm : C(X₁.carrier, S₀)) = (e₁.symm : C(X₁.carrier, S₀)) := by
      ext x
      simp
    rw [ea, eb] at h1
    exact h1.symm
  obtain ⟨hineq, heq⟩ := thm26_2_uniqueness_of_uniformization hg hX₁ hS hi₁ hqcf hhom' hp₀
  have hmax₂ : maxDilatationRS e₂.symm = ENNReal.ofReal ((1 + k₂) / (1 - k₂)) := (teichmullerMap_beltrami hi₂).2
  refine ⟨hineq.trans (hle.trans hmax₂.le), fun hk => ?_⟩
  have h21 : ENNReal.ofReal ((1 + k₂) / (1 - k₂)) = ENNReal.ofReal ((1 + k₁) / (1 - k₁)) := by rw [hk]
  have hfun := heq (le_antisymm (hle.trans (hmax₂.trans h21).le) hineq)
  funext x
  have hx : e₂.symm (c (e₁ x)) = x := by simpa using congrFun hfun (e₁ x)
  have hx' := congrArg e₂ hx
  rw [Homeomorph.apply_symm_apply] at hx'
  rw [Homeomorph.trans_apply, hx']

end LiZhongQC
