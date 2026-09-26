import LiZhongQC.Ch06.S22_RiemannSurfaces
import LiZhongQC.Ch02.S13_Representation

/-!
# §23 Riemann 曲面上的拟共形映射 — Quasiconformal mappings of Riemann surfaces

* §23.1 `K`-quasiconformal maps between Riemann surfaces      — `IsKQCRS`
* the Beltrami differential of a q.c. map (23.1)               — `IsBeltramiDifferential`
* the maximal dilatation `K[f]` (23.3) and (23.4)
* §23.2 lifting q.c. maps to the universal covering; (23.5)
* Theorem 23.1 (homotopy classes and induced isomorphisms of covering groups)
* Corollary: a conformal self-map homotopic to the identity is the identity
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u v w

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S₁ : Type v} [TopologicalSpace S₁] [ChartedSpace ℂ S₁]
variable {S₂ : Type w} [TopologicalSpace S₂] [ChartedSpace ℂ S₂]

/-- The local expression `φ_{f(x)} ∘ f ∘ φ_x⁻¹` of `f : S₀ → S₁` in the preferred charts. -/
def localMapExpr (f : S₀ → S₁) (x : S₀) : ℂ → ℂ :=
  fun z => chartAt ℂ (f x) (f ((chartAt ℂ x).symm z))

/-- The (open) domain of the local expression of `f` at `x`. -/
def localMapDomain (f : S₀ → S₁) (x : S₀) : Set ℂ :=
  (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (f ⁻¹' (chartAt ℂ (f x)).source)

/-- **§23.1** (`K` 拟共形映射).  A homeomorphism `f : S₀ → S₁` is `K`-quasiconformal if all its local
expressions in charts are `K`-quasiconformal. -/
def IsKQCRS (f : S₀ ≃ₜ S₁) (K : ℝ) : Prop :=
  1 ≤ K ∧ ∀ x : S₀, IsKQC (localMapExpr f x) (localMapDomain f x) K

/-- `f` is quasiconformal (for some `K`). -/
def IsQCRS (f : S₀ ≃ₜ S₁) : Prop := ∃ K : ℝ, IsKQCRS f K

/-- `q` is a family of local coefficients satisfying the transformation law of `(m, n)`
differentials almost everywhere. -/
def IsDiffFamilyAE (m n : ℤ) (q : S₀ → ℂ → ℂ) : Prop :=
  ∀ x y : S₀, ∀ᵐ z ∂(volume.restrict ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source)),
    q y z = q x (chartTransition x y z) * deriv (chartTransition x y) z ^ m *
      conj (deriv (chartTransition x y) z) ^ n

/-- A Beltrami differential `μ dz̄/dz` on `S₀` with `‖μ‖_∞ ≤ k`: a `(-1, 1)` differential with
measurable coefficients bounded by `k`. -/
def IsBeltramiDifferential (μ : S₀ → ℂ → ℂ) (k : ℝ) : Prop :=
  IsDiffFamilyAE (-1) 1 μ ∧ ∀ x : S₀, IsBeltramiCoeff (μ x) (chartAt ℂ x).target k

/-! ### S23 basics track interface (coordinator 553e2d): charts, Wirtinger chain rules, (23.1), (23.3), (23.4) -/

/-- The chart transitions `φ_x ∘ φ_y⁻¹` and `φ_y ∘ φ_x⁻¹` are inverse to each other near a point of
`φ_y(U_x ∩ U_y)`. -/
theorem s23_transition_inv (x y : S₀) {z : ℂ} (hz : z ∈ (chartAt ℂ y).target)
    (hzx : (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source) :
    ∀ᶠ w in 𝓝 z, chartTransition y x (chartTransition x y w) = w := by
  filter_upwards [((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source).mem_nhds ⟨hz, hzx⟩]
    with w hw
  simp only [chartTransition]
  rw [(chartAt ℂ x).left_inv hw.2, (chartAt ℂ y).right_inv hw.1]

/-- A point of `φ_y(U_x ∩ U_y)` is sent by the transition `φ_x ∘ φ_y⁻¹` to a point of `φ_x(U_x ∩ U_y)`. -/
theorem s23_transition_mem {x y : S₀} {z : ℂ} (hz : z ∈ (chartAt ℂ y).target)
    (hzx : (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source) :
    chartTransition x y z ∈ (chartAt ℂ x).target ∧
      (chartAt ℂ x).symm (chartTransition x y z) ∈ (chartAt ℂ y).source ∧
      (chartAt ℂ x).symm (chartTransition x y z) = (chartAt ℂ y).symm z := by
  have h1 : (chartAt ℂ x).symm (chartTransition x y z) = (chartAt ℂ y).symm z := (chartAt ℂ x).left_inv hzx
  exact ⟨(chartAt ℂ x).map_source hzx, h1 ▸ (chartAt ℂ y).map_target hz, h1⟩

/-- In a holomorphic atlas the chart transition `φ_x ∘ φ_y⁻¹` is complex differentiable at the points of
`φ_y(U_x ∩ U_y)` (`contDiffWithinAt_ext_coord_change` with `n = ω`). -/
theorem s23_transition_differentiableAt [IsManifold 𝓘(ℂ) ω S₀] (x y : S₀) {z : ℂ}
    (hz : z ∈ (chartAt ℂ y).target) (hzx : (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source) :
    DifferentiableAt ℂ (chartTransition x y) z := by
  have hmem : z ∈ ((extChartAt 𝓘(ℂ) y).symm ≫ extChartAt 𝓘(ℂ) x).source := by
    simp only [mfld_simps]
    exact ⟨hz, hzx⟩
  have h := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) (n := ω) x y hmem
  rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
  have heq : (extChartAt 𝓘(ℂ) x ∘ (extChartAt 𝓘(ℂ) y).symm) = chartTransition x y := by
    funext v
    simp only [mfld_simps, chartTransition]
  rw [heq] at h
  exact h.differentiableAt (by simp)

/-- A holomorphic map with a holomorphic left inverse near a point has nonzero derivative there. -/
theorem s23_deriv_ne_zero {h k : ℂ → ℂ} {a : ℂ} (hh : DifferentiableAt ℂ h a)
    (hk : DifferentiableAt ℂ k (h a)) (hkh : ∀ᶠ w in 𝓝 a, k (h w) = w) : deriv h a ≠ 0 := by
  have hev : (k ∘ h) =ᶠ[𝓝 a] id := hkh
  have h1 : deriv (k ∘ h) a = 1 := by rw [hev.deriv_eq, deriv_id]
  rw [deriv_comp a hk hh] at h1
  intro h0
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

/-- In a holomorphic atlas the chart transition `φ_x ∘ φ_y⁻¹` is holomorphic with nonzero derivative at every point of
`φ_y(U_x ∩ U_y)` (its local inverse is the transition `φ_y ∘ φ_x⁻¹`). -/
theorem s23_transition [IsManifold 𝓘(ℂ) ω S₀] (x y : S₀) {z : ℂ} (hz : z ∈ (chartAt ℂ y).target)
    (hzx : (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source) :
    DifferentiableAt ℂ (chartTransition x y) z ∧ deriv (chartTransition x y) z ≠ 0 := by
  obtain ⟨hT1, hT2, -⟩ := s23_transition_mem hz hzx
  have h1 := s23_transition_differentiableAt x y hz hzx
  exact ⟨h1, s23_deriv_ne_zero h1 (s23_transition_differentiableAt y x hT1 hT2) (s23_transition_inv x y hz hzx)⟩

/-- **Wirtinger chain rule, holomorphic post-composition, at every point**: if `h` is holomorphic at `g z` with a
holomorphic left inverse `k` near `g z` and `g` is continuous at `z`, then `∂(h ∘ g) = h'(g z) ∂g` and
`∂̄(h ∘ g) = h'(g z) ∂̄g` at `z` (`eq6_5`; if `g` is not differentiable at `z`, neither is `h ∘ g = k⁻¹ ∘ …`, and both
sides vanish). -/
theorem s23_wirtinger_comp_left {g h k : ℂ → ℂ} {z : ℂ} (hg : ContinuousAt g z)
    (hh : DifferentiableAt ℂ h (g z)) (hk : DifferentiableAt ℂ k (h (g z)))
    (hkh : ∀ᶠ w in 𝓝 (g z), k (h w) = w) :
    dz (h ∘ g) z = deriv h (g z) * dz g z ∧ dzbar (h ∘ g) z = deriv h (g z) * dzbar g z := by
  by_cases hd : DifferentiableAt ℝ g z
  · exact eq6_5 hd hh
  · have hd' : ¬ DifferentiableAt ℝ (h ∘ g) z := by
      intro hhg
      apply hd
      have hev : g =ᶠ[𝓝 z] k ∘ (h ∘ g) := by
        filter_upwards [hg.tendsto.eventually hkh] with w hw
        exact hw.symm
      exact ((hk.restrictScalars ℝ).comp z hhg).congr_of_eventuallyEq hev
    simp [dz, dzbar, fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd']

/-- **Wirtinger chain rule, holomorphic pre-composition, at every point**: if `T` is holomorphic at `z` with a
holomorphic local inverse `S`, then `∂(g ∘ T) = ∂g(T z) T'(z)` and `∂̄(g ∘ T) = ∂̄g(T z) conj T'(z)` at `z` (`eq6_4`;
if `g` is not differentiable at `T z`, neither is `g ∘ T`, and both sides vanish). -/
theorem s23_wirtinger_comp_right {g T S : ℂ → ℂ} {z : ℂ} (hT : DifferentiableAt ℂ T z)
    (hS : DifferentiableAt ℂ S (T z)) (hST : ∀ᶠ w in 𝓝 z, S (T w) = w)
    (hTS : ∀ᶠ u in 𝓝 (T z), T (S u) = u) :
    dz (g ∘ T) z = dz g (T z) * deriv T z ∧ dzbar (g ∘ T) z = dzbar g (T z) * conj (deriv T z) := by
  by_cases hd : DifferentiableAt ℝ g (T z)
  · exact eq6_4 hT hd
  · have hd' : ¬ DifferentiableAt ℝ (g ∘ T) z := by
      intro hgT
      apply hd
      have hSTz : S (T z) = z := hST.self_of_nhds
      have h1 : DifferentiableAt ℝ ((g ∘ T) ∘ S) (T z) := by
        refine DifferentiableAt.comp (T z) ?_ (hS.restrictScalars ℝ)
        rw [hSTz]
        exact hgT
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards [hTS] with u hu
      simp only [Function.comp_apply, hu]
    simp [dz, dzbar, fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd']

/-- The complex dilatation is unchanged by a holomorphic post-composition (`s23_wirtinger_comp_left`). -/
theorem s23_dilatation_comp_left {g h k : ℂ → ℂ} {z : ℂ} (hg : ContinuousAt g z)
    (hh : DifferentiableAt ℂ h (g z)) (hk : DifferentiableAt ℂ k (h (g z)))
    (hkh : ∀ᶠ w in 𝓝 (g z), k (h w) = w) : complexDilatation (h ∘ g) z = complexDilatation g z := by
  obtain ⟨h1, h2⟩ := s23_wirtinger_comp_left hg hh hk hkh
  rw [complexDilatation, complexDilatation, h1, h2, mul_div_mul_left _ _ (s23_deriv_ne_zero hh hk hkh)]

/-- The complex dilatation under a holomorphic pre-composition: `μ_{g ∘ T}(z) = μ_g(T z) conj T'(z)/T'(z)`
(`s23_wirtinger_comp_right`). -/
theorem s23_dilatation_comp_right {g T S : ℂ → ℂ} {z : ℂ} (hT : DifferentiableAt ℂ T z)
    (hS : DifferentiableAt ℂ S (T z)) (hST : ∀ᶠ w in 𝓝 z, S (T w) = w)
    (hTS : ∀ᶠ u in 𝓝 (T z), T (S u) = u) :
    complexDilatation (g ∘ T) z = complexDilatation g (T z) * (conj (deriv T z) / deriv T z) := by
  obtain ⟨h1, h2⟩ := s23_wirtinger_comp_right (g := g) hT hS hST hTS
  have hT' : deriv T z ≠ 0 := s23_deriv_ne_zero hT hS hST
  rw [complexDilatation, complexDilatation, h1, h2]
  field_simp

/-- The quotient `(|∂g| + |∂̄g|)/(|∂g| - |∂̄g|)` (the integrand of `maxDilatation`) is unchanged by a holomorphic
post-composition. -/
theorem s23_quot_comp_left {g h k : ℂ → ℂ} {z : ℂ} (hg : ContinuousAt g z)
    (hh : DifferentiableAt ℂ h (g z)) (hk : DifferentiableAt ℂ k (h (g z)))
    (hkh : ∀ᶠ w in 𝓝 (g z), k (h w) = w) :
    (‖dz (h ∘ g) z‖ + ‖dzbar (h ∘ g) z‖) / (‖dz (h ∘ g) z‖ - ‖dzbar (h ∘ g) z‖) =
      (‖dz g z‖ + ‖dzbar g z‖) / (‖dz g z‖ - ‖dzbar g z‖) := by
  obtain ⟨h1, h2⟩ := s23_wirtinger_comp_left hg hh hk hkh
  have hn : ‖deriv h (g z)‖ ≠ 0 := norm_ne_zero_iff.2 (s23_deriv_ne_zero hh hk hkh)
  rw [h1, h2, norm_mul, norm_mul, ← mul_add, ← mul_sub, mul_div_mul_left _ _ hn]

/-- The quotient `(|∂g| + |∂̄g|)/(|∂g| - |∂̄g|)` under a holomorphic pre-composition: its value for `g ∘ T` at `z` is its
value for `g` at `T z`. -/
theorem s23_quot_comp_right {g T S : ℂ → ℂ} {z : ℂ} (hT : DifferentiableAt ℂ T z)
    (hS : DifferentiableAt ℂ S (T z)) (hST : ∀ᶠ w in 𝓝 z, S (T w) = w)
    (hTS : ∀ᶠ u in 𝓝 (T z), T (S u) = u) :
    (‖dz (g ∘ T) z‖ + ‖dzbar (g ∘ T) z‖) / (‖dz (g ∘ T) z‖ - ‖dzbar (g ∘ T) z‖) =
      (‖dz g (T z)‖ + ‖dzbar g (T z)‖) / (‖dz g (T z)‖ - ‖dzbar g (T z)‖) := by
  obtain ⟨h1, h2⟩ := s23_wirtinger_comp_right (g := g) hT hS hST hTS
  have hn : ‖deriv T z‖ ≠ 0 := norm_ne_zero_iff.2 (s23_deriv_ne_zero hT hS hST)
  rw [h1, h2, norm_mul, norm_mul, Complex.norm_conj, ← add_mul, ← sub_mul, mul_div_mul_right _ _ hn]

/-- For `p ∈ U_x` with `f p ∈ U_y`: `f` is holomorphic at `p` iff it is continuous there and
`φ_y ∘ f ∘ φ_x⁻¹` is complex differentiable at `φ_x p` (`mdifferentiableAt_iff_of_mem_source` for the trivial
model `𝓘(ℂ)`). -/
theorem s23_mdifferentiableAt_iff [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ → S₁} {x p : S₀}
    {y : S₁} (hp : p ∈ (chartAt ℂ x).source) (hfp : f p ∈ (chartAt ℂ y).source) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f p ↔
      ContinuousAt f p ∧ DifferentiableAt ℂ (fun z => chartAt ℂ y (f ((chartAt ℂ x).symm z))) (chartAt ℂ x p) := by
  rw [mdifferentiableAt_iff_of_mem_source hp hfp, ModelWithCorners.range_eq_univ, differentiableWithinAt_univ]
  simp only [mfld_simps]
  rfl

/-- **LG** (local-to-global; a local copy of the downstream `UniversalTeichmuller.ut2_lg`): a map injective on an
open set `Ω` which is `K`-q.c. near every point of `Ω` is `K`-q.c. on `Ω` (`s13x_removable` with `L = ∅`). -/
theorem s23_lg {g : ℂ → ℂ} {Ω : Set ℂ} {K : ℝ} (hΩ : IsOpen Ω) (hK : 1 ≤ K) (hinj : InjOn g Ω)
    (hloc : ∀ z ∈ Ω, ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ Ω ∧ IsKQC g U K) : IsKQC g Ω K := by
  have hcont : ContinuousOn g Ω := fun z hz => by
    obtain ⟨U, hUo, hzU, -, hgU⟩ := hloc z hz
    exact ((hgU.2.2.1.1 z hzU).continuousAt (hUo.mem_nhds hzU)).continuousWithinAt
  refine s13x_removable (L := ∅) hΩ hK (qcl_f_isHomeomorphOnto_of_injOn hΩ hcont hinj) measure_empty
    (Eventually.of_forall fun x => by simp) (Eventually.of_forall fun y => by simp) fun z hz => hloc z hz.1

/-- The domain of a local expression of a continuous map is open. -/
theorem s23_localMapDomain_isOpen {f : S₀ → S₁} (hf : Continuous f) (x : S₀) : IsOpen (localMapDomain f x) :=
  (chartAt ℂ x).isOpen_inter_preimage_symm (hf.isOpen_preimage _ (chartAt ℂ (f x)).open_source)

/-- **E1, pointwise** ((23.1) at one point of a chart overlap): for `z ∈ φ_y(U_x ∩ U_y)`, `p = φ_y⁻¹ z` and
`T = φ_x ∘ φ_y⁻¹`, the map `φ_{f p} ∘ f ∘ φ_y⁻¹` agrees near `z` with `(φ_{f p} ∘ f ∘ φ_x⁻¹) ∘ T` (`left_inv`), so its
dilatation at `z` is that of `φ_{f p} ∘ f ∘ φ_x⁻¹` at `T z` times `conj T'(z)/T'(z)` (`s23_dilatation_comp_right`, the
local inverse of `T` being `φ_y ∘ φ_x⁻¹`).  No condition on `f`. -/
theorem s23_e1_pointwise [IsManifold 𝓘(ℂ) ω S₀] (f : S₀ → S₁) (x y : S₀) {z : ℂ}
    (hz : z ∈ (chartAt ℂ y).target) (hzx : (chartAt ℂ y).symm z ∈ (chartAt ℂ x).source) :
    complexDilatation (fun w => chartAt ℂ (f ((chartAt ℂ y).symm z)) (f ((chartAt ℂ y).symm w))) z =
      complexDilatation (fun w => chartAt ℂ (f ((chartAt ℂ y).symm z)) (f ((chartAt ℂ x).symm w)))
        (chartTransition x y z) * (conj (deriv (chartTransition x y) z) / deriv (chartTransition x y) z) := by
  obtain ⟨hT1, hT2, -⟩ := s23_transition_mem hz hzx
  have hev : (fun w => chartAt ℂ (f ((chartAt ℂ y).symm z)) (f ((chartAt ℂ y).symm w))) =ᶠ[𝓝 z]
      (fun w => chartAt ℂ (f ((chartAt ℂ y).symm z)) (f ((chartAt ℂ x).symm w))) ∘ chartTransition x y := by
    filter_upwards [((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source).mem_nhds ⟨hz, hzx⟩]
      with w hw
    simp only [Function.comp_apply, chartTransition]
    rw [(chartAt ℂ x).left_inv hw.2]
  have h1 : complexDilatation (fun w => chartAt ℂ (f ((chartAt ℂ y).symm z)) (f ((chartAt ℂ y).symm w))) z =
      complexDilatation ((fun w => chartAt ℂ (f ((chartAt ℂ y).symm z)) (f ((chartAt ℂ x).symm w))) ∘
        chartTransition x y) z := by
    simp only [complexDilatation, dz, dzbar, hev.fderiv_eq]
  rw [h1]
  exact s23_dilatation_comp_right (s23_transition x y hz hzx).1 (s23_transition y x hT1 hT2).1
    (s23_transition_inv x y hz hzx) (s23_transition_inv y x hT1 hT2)

/-- **E1** ((23.1), the `(-1, 1)` law): for any map `f` and a holomorphic atlas on `S₀`, the family `μ_f` transforms as a
`(-1, 1)` differential at EVERY point of a chart overlap.  With `T = φ_x ∘ φ_y⁻¹` and `p = φ_y⁻¹ z`, the map whose
dilatation is `μ_f(y)(z)` agrees near `z` with (the map whose dilatation is `μ_f(x)(T z)`) `∘ T`, the target chart being
the one at `f p` in both; so `s23_dilatation_comp_right` gives `μ_f(y)(z) = μ_f(x)(T z) conj T'(z)/T'(z)`. -/
theorem s23_e_law [IsManifold 𝓘(ℂ) ω S₀] (f : S₀ → S₁) :
    IsDiffFamilyAE (-1) 1 (fun x => (chartAt ℂ x).target.indicator fun z =>
      complexDilatation (fun w => chartAt ℂ (f ((chartAt ℂ x).symm z)) (f ((chartAt ℂ x).symm w))) z) := by
  intro x y
  refine ae_restrict_of_forall_mem
    ((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source).measurableSet fun z hz => ?_
  obtain ⟨hT1, -, hT3⟩ := s23_transition_mem hz.1 hz.2
  simp only [Set.indicator_of_mem hz.1, Set.indicator_of_mem hT1, hT3, zpow_neg_one, zpow_one]
  rw [s23_e1_pointwise f x y hz.1 hz.2]
  ring

/-- **E2, local model**: near each point `z₀ = φ_x(p₀)` of the chart target, on the open set
`W = φ_x(U_x ∩ U_{p₀} ∩ f⁻¹ U_{f p₀})`, the coefficient `μ_f(x)` is the complex dilatation of the single map
`G = φ_{f p₀} ∘ f ∘ φ_x⁻¹`: at `z ∈ W` the map defining `μ_f(x)(z)` is `(φ_{f p} ∘ φ_{f p₀}⁻¹) ∘ G` near `z`
(`p = φ_x⁻¹ z`), a holomorphic post-composition (`s23_dilatation_comp_left`).  And
`G = (φ_{f p₀} ∘ f ∘ φ_{p₀}⁻¹) ∘ (φ_{p₀} ∘ φ_x⁻¹)` is `K`-q.c. on `W` (`thm7_1_comp`, the chart transition being
conformal on `W`). -/
theorem s23_e2_local [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ ≃ₜ S₁} {K : ℝ}
    (hf : IsKQCRS f K) (x : S₀) {z₀ : ℂ} (hz₀ : z₀ ∈ (chartAt ℂ x).target) :
    ∃ W : Set ℂ, IsOpen W ∧ z₀ ∈ W ∧ ∃ G : ℂ → ℂ, IsKQC G W K ∧ ∀ z ∈ W,
      (chartAt ℂ x).target.indicator (fun z =>
        complexDilatation (fun w => chartAt ℂ (f ((chartAt ℂ x).symm z)) (f ((chartAt ℂ x).symm w))) z) z =
        complexDilatation G z := by
  set p₀ := (chartAt ℂ x).symm z₀
  set y₀ := f p₀
  set W : Set ℂ := (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' ((chartAt ℂ p₀).source ∩
    f ⁻¹' (chartAt ℂ y₀).source)
  have hWo : IsOpen W := (chartAt ℂ x).isOpen_inter_preimage_symm
    ((chartAt ℂ p₀).open_source.inter (f.continuous.isOpen_preimage _ (chartAt ℂ y₀).open_source))
  set G : ℂ → ℂ := fun w => chartAt ℂ y₀ (f ((chartAt ℂ x).symm w))
  have hT₁ : IsKQC (chartTransition p₀ x) W 1 := by
    refine isKQC_one_of_conformal hWo
      ⟨fun w hw => (s23_transition p₀ x hw.1 hw.2.1).1.differentiableWithinAt, ?_, rfl⟩
    intro w₁ hw₁ w₂ hw₂ heq
    exact (chartAt ℂ x).symm.injOn hw₁.1 hw₂.1 ((chartAt ℂ p₀).injOn hw₁.2.1 hw₂.2.1 heq)
  have hsub : chartTransition p₀ x '' W ⊆ localMapDomain f p₀ := by
    rintro _ ⟨w, hw, rfl⟩
    have e1 : (chartAt ℂ p₀).symm (chartTransition p₀ x w) = (chartAt ℂ x).symm w :=
      (chartAt ℂ p₀).left_inv hw.2.1
    refine ⟨(chartAt ℂ p₀).map_source hw.2.1, ?_⟩
    rw [mem_preimage, e1]
    exact hw.2.2
  have hGK : IsKQC G W K := by
    have h := thm7_1_comp hT₁ (hf.2 p₀) hsub
    rw [one_mul] at h
    refine ad_isKQC_congr h fun w hw => ?_
    show chartAt ℂ (f p₀) (f ((chartAt ℂ x).symm w)) =
      chartAt ℂ (f p₀) (f ((chartAt ℂ p₀).symm (chartAt ℂ p₀ ((chartAt ℂ x).symm w))))
    rw [(chartAt ℂ p₀).left_inv hw.2.1]
  refine ⟨W, hWo, ⟨hz₀, mem_chart_source ℂ p₀, mem_chart_source ℂ y₀⟩, G, hGK, fun z hz => ?_⟩
  have hfp : f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ y₀).source := hz.2.2
  have hev : (fun w => chartAt ℂ (f ((chartAt ℂ x).symm z)) (f ((chartAt ℂ x).symm w))) =ᶠ[𝓝 z]
      chartTransition (f ((chartAt ℂ x).symm z)) y₀ ∘ G := by
    filter_upwards [hWo.mem_nhds hz] with w hw
    have hfw : f ((chartAt ℂ x).symm w) ∈ (chartAt ℂ y₀).source := hw.2.2
    show _ = chartAt ℂ (f ((chartAt ℂ x).symm z)) ((chartAt ℂ y₀).symm (chartAt ℂ y₀ (f ((chartAt ℂ x).symm w))))
    rw [(chartAt ℂ y₀).left_inv hfw]
  have hGz : G z ∈ (chartAt ℂ y₀).target := (chartAt ℂ y₀).map_source hfp
  have hGz' : (chartAt ℂ y₀).symm (G z) ∈ (chartAt ℂ (f ((chartAt ℂ x).symm z))).source := by
    show (chartAt ℂ y₀).symm (chartAt ℂ y₀ (f ((chartAt ℂ x).symm z))) ∈ _
    rw [(chartAt ℂ y₀).left_inv hfp]
    exact mem_chart_source ℂ _
  obtain ⟨hT1, hT2, -⟩ := s23_transition_mem hGz hGz'
  have hc : ContinuousAt G z := (hGK.2.2.1.1 z hz).continuousAt (hWo.mem_nhds hz)
  have h1 : complexDilatation (fun w => chartAt ℂ (f ((chartAt ℂ x).symm z)) (f ((chartAt ℂ x).symm w))) z =
      complexDilatation (chartTransition (f ((chartAt ℂ x).symm z)) y₀ ∘ G) z := by
    simp only [complexDilatation, dz, dzbar, hev.fderiv_eq (𝕜 := ℝ)]
  rw [indicator_of_mem hz.1, h1]
  exact s23_dilatation_comp_left hc (s23_transition _ y₀ hGz hGz').1 (s23_transition y₀ _ hT1 hT2).1
    (s23_transition_inv _ y₀ hGz hGz')
/-- **E2** ((23.1)–(23.2), the coefficients): for a `K`-q.c. `f`, near each point `z₀ = φ_x(p₀)` of the chart target,
`μ_f(x)` is the complex dilatation of the single map `G = φ_{f p₀} ∘ f ∘ φ_x⁻¹` (changing the target chart from `f p₀`
to `f(φ_x⁻¹ z)` is a holomorphic post-composition, `s23_dilatation_comp_left`), and
`G = (φ_{f p₀} ∘ f ∘ φ_{p₀}⁻¹) ∘ (φ_{p₀} ∘ φ_x⁻¹)` is `K`-q.c. near `z₀`; so `μ_f(x)` is measurable with
`|μ_f(x)| ≤ (K - 1)/(K + 1)` a.e. (`isKQC_maxDilatation_le`, a countable cover of the chart target). -/
theorem s23_e_coeff [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ ≃ₜ S₁} {K : ℝ} (hf : IsKQCRS f K)
    (x : S₀) :
    IsBeltramiCoeff ((chartAt ℂ x).target.indicator fun z =>
      complexDilatation (fun w => chartAt ℂ (f ((chartAt ℂ x).symm z)) (f ((chartAt ℂ x).symm w))) z)
      (chartAt ℂ x).target ((K - 1) / (K + 1)) := by
  refine ⟨?_, s13x_ae_of_local (L := ∅) measure_empty fun z hz => ?_⟩
  · choose! W hWo hzW G _hG hμ using fun z (hz : z ∈ (chartAt ℂ x).target) => s23_e2_local hf x hz
    obtain ⟨T, hTsub, hTc, hTeq⟩ :=
      TopologicalSpace.isOpen_biUnion_countable (chartAt ℂ x).target W fun z hz => hWo z hz
    have hcov : (chartAt ℂ x).target ⊆ ⋃ z ∈ T, W z := by
      intro w hw
      rw [hTeq]
      exact mem_biUnion hw (hzW w hw)
    refine AEStronglyMeasurable.mono_set hcov ?_
    have : Countable T := hTc.to_subtype
    rw [biUnion_eq_iUnion, aestronglyMeasurable_iUnion_iff]
    rintro ⟨z, hz⟩
    refine ((measurable_dzbar (G z)).div (measurable_dz (G z))).aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem (hWo z (hTsub hz)).measurableSet] with w hw
    exact (hμ z (hTsub hz) w hw).symm
  · obtain ⟨W, hWo, hzW, G, hG, hμ⟩ := s23_e2_local hf x hz.1
    refine ⟨W, hWo, hzW, ?_⟩
    filter_upwards [(isKQC_maxDilatation_le hG).2, ae_restrict_mem hWo.measurableSet] with w hw hwW
    rw [hμ w hwW]
    exact hw

/-- (23.1): the complex dilatations of the local expressions of a `K`-q.c. map form a Beltrami
differential with `‖μ‖_∞ ≤ (K-1)/(K+1)` (23.2); in particular `|μ|` is a well defined function
on `S₀`.

At `z` in the chart at `x` the dilatation is computed with the chart at the image point `f(p)`,
`p = φ_x⁻¹(z)`; for holomorphic atlases it does not depend on that choice.  (Corrected 2026-09-25: the
family used to be the dilatation of the preferred-chart expression `localMapExpr f x`, cut off where
`f` leaves the chart at `f(x)`, which breaks the `(-1, 1)` law on chart overlaps; the holomorphic
atlases are now assumed.) -/
theorem eq23_1_beltrami_differential [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ ≃ₜ S₁} {K : ℝ}
    (hf : IsKQCRS f K) :
    IsBeltramiDifferential
      (fun x => (chartAt ℂ x).target.indicator fun z =>
        complexDilatation (fun w => chartAt ℂ (f ((chartAt ℂ x).symm z)) (f ((chartAt ℂ x).symm w))) z)
      ((K - 1) / (K + 1)) := by
  exact ⟨s23_e_law f, fun x => s23_e_coeff hf x⟩

/-- (23.3): the maximal dilatation `K[f] = ess sup (1 + |μ|)/(1 - |μ|)` of a map of Riemann
surfaces. -/
def maxDilatationRS (f : S₀ → S₁) : ℝ≥0∞ :=
  ⨆ x : S₀, maxDilatation (localMapExpr f x) (localMapDomain f x)

/-- (23.3): `K[f] ≤ K` for a `K`-q.c. map. -/
theorem maxDilatationRS_le {f : S₀ ≃ₜ S₁} {K : ℝ} (hf : IsKQCRS f K) :
    maxDilatationRS f ≤ ENNReal.ofReal K := by
  exact iSup_le fun x => (isKQC_maxDilatation_le (hf.2 x)).1

/-- **C0** (local decomposition of a composite): for `z₀` in the domain of the local expression of `f ∘ g` at `x`,
with `p₀ = φ_x⁻¹ z₀` and `q₀ = g p₀`, there is an open `U ∋ z₀` inside that domain on which the expression is
`T₃ ∘ L_f ∘ L_g ∘ T₁`: `T₁ = φ_{p₀} ∘ φ_x⁻¹` maps `U` into the domain of `L_g` (the expression of `g` at `p₀`), `L_g`
maps `T₁(U)` into the domain of `L_f` (the expression of `f` at `q₀`), and the transition
`T₃ = φ_{f(g x)} ∘ φ_{f q₀}⁻¹` is defined at the points of `L_f(L_g(T₁(U)))`. -/
theorem s23_c_decomp (g : S₀ ≃ₜ S₁) (f : S₁ ≃ₜ S₂) (x : S₀) {z₀ : ℂ}
    (hz₀ : z₀ ∈ localMapDomain (g.trans f) x) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ U ⊆ localMapDomain (g.trans f) x ∧ ∀ w ∈ U,
      chartTransition ((chartAt ℂ x).symm z₀) x w ∈ localMapDomain g ((chartAt ℂ x).symm z₀) ∧
      localMapExpr g ((chartAt ℂ x).symm z₀) (chartTransition ((chartAt ℂ x).symm z₀) x w) ∈
        localMapDomain f (g ((chartAt ℂ x).symm z₀)) ∧
      localMapExpr f (g ((chartAt ℂ x).symm z₀))
          (localMapExpr g ((chartAt ℂ x).symm z₀) (chartTransition ((chartAt ℂ x).symm z₀) x w)) ∈
        (chartAt ℂ (f (g ((chartAt ℂ x).symm z₀)))).target ∧
      (chartAt ℂ (f (g ((chartAt ℂ x).symm z₀)))).symm (localMapExpr f (g ((chartAt ℂ x).symm z₀))
          (localMapExpr g ((chartAt ℂ x).symm z₀) (chartTransition ((chartAt ℂ x).symm z₀) x w))) ∈
        (chartAt ℂ (f (g x))).source ∧
      localMapExpr (g.trans f) x w = chartTransition (f (g x)) (f (g ((chartAt ℂ x).symm z₀)))
        (localMapExpr f (g ((chartAt ℂ x).symm z₀))
          (localMapExpr g ((chartAt ℂ x).symm z₀) (chartTransition ((chartAt ℂ x).symm z₀) x w))) := by
  set p₀ := (chartAt ℂ x).symm z₀ with hp₀
  set A : Set S₀ := (chartAt ℂ p₀).source ∩ g ⁻¹' ((chartAt ℂ (g p₀)).source ∩
    f ⁻¹' (chartAt ℂ (f (g p₀))).source) with hA
  have hAo : IsOpen A := (chartAt ℂ p₀).open_source.inter (g.continuous.isOpen_preimage _
    ((chartAt ℂ (g p₀)).open_source.inter (f.continuous.isOpen_preimage _ (chartAt ℂ (f (g p₀))).open_source)))
  refine ⟨localMapDomain (g.trans f) x ∩ ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' A),
    (s23_localMapDomain_isOpen (g.trans f).continuous x).inter
      ((chartAt ℂ x).isOpen_inter_preimage_symm hAo),
    ⟨hz₀, hz₀.1, mem_chart_source ℂ p₀, mem_chart_source ℂ (g p₀), mem_chart_source ℂ (f (g p₀))⟩,
    inter_subset_left, fun w hw => ?_⟩
  obtain ⟨⟨hwt, hwD⟩, -, hp, hgp, hfgp⟩ := hw
  set p := (chartAt ℂ x).symm w with hpdef
  have e1 : (chartAt ℂ p₀).symm (chartTransition p₀ x w) = p := (chartAt ℂ p₀).left_inv hp
  have e2 : (chartAt ℂ (g p₀)).symm (localMapExpr g p₀ (chartTransition p₀ x w)) = g p := by
    simp only [localMapExpr, e1]
    exact (chartAt ℂ (g p₀)).left_inv hgp
  have e3 : (chartAt ℂ (f (g p₀))).symm (localMapExpr f (g p₀) (localMapExpr g p₀ (chartTransition p₀ x w))) =
      f (g p) := by
    show (chartAt ℂ (f (g p₀))).symm (chartAt ℂ (f (g p₀))
      (f ((chartAt ℂ (g p₀)).symm (localMapExpr g p₀ (chartTransition p₀ x w))))) = f (g p)
    rw [e2]
    exact (chartAt ℂ (f (g p₀))).left_inv hfgp
  refine ⟨⟨(chartAt ℂ p₀).map_source hp, by rw [mem_preimage, e1]; exact hgp⟩,
    ⟨by
      show chartAt ℂ (g p₀) (g ((chartAt ℂ p₀).symm (chartTransition p₀ x w))) ∈ _
      rw [e1]
      exact (chartAt ℂ (g p₀)).map_source hgp, by rw [mem_preimage, e2]; exact hfgp⟩,
    ?_, ?_, ?_⟩
  · show chartAt ℂ (f (g p₀)) (f ((chartAt ℂ (g p₀)).symm (localMapExpr g p₀ (chartTransition p₀ x w)))) ∈ _
    rw [e2]
    exact (chartAt ℂ (f (g p₀))).map_source hfgp
  · rw [e3]
    exact hwD
  · show chartAt ℂ ((g.trans f) x) ((g.trans f) p) = chartAt ℂ (f (g x)) ((chartAt ℂ (f (g p₀))).symm
      (localMapExpr f (g p₀) (localMapExpr g p₀ (chartTransition p₀ x w))))
    rw [e3]
    rfl

/-- The chart transition `φ_x ∘ φ_y⁻¹` of a holomorphic atlas is `1`-q.c. on the open set `φ_y(U_x ∩ U_y)`: it is
holomorphic there (`s23_transition`) and injective (`φ_x` is injective on `U_x` and `φ_y⁻¹` on `φ_y(U_y)`), so it is
conformal (`isKQC_one_of_conformal`). -/
theorem s23_c1_transition_isKQC [IsManifold 𝓘(ℂ) ω S₀] (x y : S₀) :
    IsKQC (chartTransition x y) ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ x).source) 1 := by
  refine isKQC_one_of_conformal ((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ x).open_source)
    ⟨fun w hw => (s23_transition x y hw.1 hw.2).1.differentiableWithinAt, fun a ha b hb hab => ?_, rfl⟩
  have ha2 : (chartAt ℂ y).symm a ∈ (chartAt ℂ x).source := ha.2
  have hb2 : (chartAt ℂ y).symm b ∈ (chartAt ℂ x).source := hb.2
  have h1 : (chartAt ℂ y).symm a = (chartAt ℂ y).symm b := by
    rw [← (chartAt ℂ x).left_inv ha2, ← (chartAt ℂ x).left_inv hb2]
    exact congrArg (chartAt ℂ x).symm hab
  rw [← (chartAt ℂ y).right_inv ha.1, ← (chartAt ℂ y).right_inv hb.1, h1]

/-- The local expression `φ_{f x} ∘ f ∘ φ_x⁻¹` of an injective map `f` is injective on its domain
(`φ_{f x}` is injective on `U_{f x}` and `φ_x⁻¹` on `φ_x(U_x)`). -/
theorem s23_c1_injOn_localMapExpr {f : S₀ → S₁} (hf : Function.Injective f) (x : S₀) :
    InjOn (localMapExpr f x) (localMapDomain f x) := by
  intro a ha b hb hab
  have ha2 : f ((chartAt ℂ x).symm a) ∈ (chartAt ℂ (f x)).source := ha.2
  have hb2 : f ((chartAt ℂ x).symm b) ∈ (chartAt ℂ (f x)).source := hb.2
  have h1 : f ((chartAt ℂ x).symm a) = f ((chartAt ℂ x).symm b) := by
    rw [← (chartAt ℂ (f x)).left_inv ha2, ← (chartAt ℂ (f x)).left_inv hb2]
    exact congrArg (chartAt ℂ (f x)).symm hab
  rw [← (chartAt ℂ x).right_inv ha.1, ← (chartAt ℂ x).right_inv hb.1, hf h1]

/-- **C1** ((23.4), composition): near each point of its domain the local expression of `f ∘ g` at `x` is
`T₃ ∘ L_f ∘ L_g ∘ T₁` (`s23_c_decomp`), a `K₁ K₂`-q.c. map (`thm7_1_comp`; the transitions are conformal,
`s23_transition`), and it is injective on its open domain, so it is `K₁ K₂`-q.c. there (`s23_lg`). -/
theorem s23_c_qc [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₂] {g : S₀ ≃ₜ S₁} {f : S₁ ≃ₜ S₂} {K₁ K₂ : ℝ}
    (hg : IsKQCRS g K₁) (hf : IsKQCRS f K₂) : IsKQCRS (g.trans f) (K₁ * K₂) := by
  have hK : 1 ≤ K₁ * K₂ := one_le_mul_of_one_le_of_one_le hg.1 hf.1
  refine ⟨hK, fun x => s23_lg (s23_localMapDomain_isOpen (g.trans f).continuous x) hK
    (s23_c1_injOn_localMapExpr (g.trans f).injective x) fun z₀ hz₀ => ?_⟩
  obtain ⟨U, hUo, hz₀U, hUD, hU⟩ := s23_c_decomp g f x hz₀
  set p₀ := (chartAt ℂ x).symm z₀
  have hWo := (chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ p₀).open_source
  refine ⟨U ∩ ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ p₀).source), hUo.inter hWo,
    ⟨hz₀U, hz₀.1, mem_chart_source ℂ p₀⟩, inter_subset_left.trans hUD, ?_⟩
  have h1 := ac_t_isKQC_restrict (s23_c1_transition_isKQC p₀ x) (hUo.inter hWo) inter_subset_right
  have h2 := thm7_1_comp h1 (hg.2 p₀) (by rintro _ ⟨w, hw, rfl⟩; exact (hU w hw.1).1)
  have h3 := thm7_1_comp h2 (hf.2 (g p₀)) (by rintro _ ⟨w, hw, rfl⟩; exact (hU w hw.1).2.1)
  have h4 := thm7_1_comp h3 (s23_c1_transition_isKQC (f (g x)) (f (g p₀)))
    (by rintro _ ⟨w, hw, rfl⟩; exact ⟨(hU w hw.1).2.2.1, (hU w hw.1).2.2.2.1⟩)
  rw [one_mul, mul_one] at h4
  exact ad_isKQC_congr h4 fun w hw => (hU w hw.1).2.2.2.2

/-- **C2 helper** (germs): the quotient `(|∂F| + |∂̄F|)/(|∂F| - |∂̄F|)` at `w` only depends on the germ of `F` at
`w`. -/
theorem s23_c2_quot_congr {F G : ℂ → ℂ} {w : ℂ} (h : F =ᶠ[𝓝 w] G) :
    (‖dz F w‖ + ‖dzbar F w‖) / (‖dz F w‖ - ‖dzbar F w‖) =
      (‖dz G w‖ + ‖dzbar G w‖) / (‖dz G w‖ - ‖dzbar G w‖) := by
  simp only [dz, dzbar, h.fderiv_eq]

/-- **C2 helper** (the Jacobian is multiplicative): `J_{F ∘ G}(u) = J_F(G u) J_G(u)` at points of real
differentiability (`det_fderiv_eq_jacobian`, `LinearMap.det_comp`). -/
theorem s23_c2_jacobian_comp {F G : ℂ → ℂ} {u : ℂ} (hG : DifferentiableAt ℝ G u)
    (hF : DifferentiableAt ℝ F (G u)) : jacobian (F ∘ G) u = jacobian F (G u) * jacobian G u := by
  rw [← det_fderiv_eq_jacobian (hF.comp u hG), ← det_fderiv_eq_jacobian hF, ← det_fderiv_eq_jacobian hG,
    fderiv_comp u hF hG, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]

/-- **C2 helper** (the real inequality): if `0 ≤ A ≤ a c + b d`, `0 ≤ B ≤ a d + b c`, `0 ≤ b < a`, `0 ≤ d < c` and
`A² - B² = (a² - b²)(c² - d²)`, then `(A + B)/(A - B) ≤ (a + b)/(a - b) · (c + d)/(c - d)`: the two sides are
`(A + B)²/D` and `((a + b)(c + d))²/D` with `D = (a² - b²)(c² - d²) > 0`, and `A + B ≤ (a + b)(c + d)`. -/
theorem s23_c2_quot_ineq {A B a b c d : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hb0 : 0 ≤ b) (hd0 : 0 ≤ d)
    (hab : b < a) (hcd : d < c) (hA : A ≤ a * c + b * d) (hB : B ≤ a * d + b * c)
    (hJ : A ^ 2 - B ^ 2 = (a ^ 2 - b ^ 2) * (c ^ 2 - d ^ 2)) :
    (A + B) / (A - B) ≤ (a + b) / (a - b) * ((c + d) / (c - d)) := by
  have hab' : 0 < a - b := sub_pos.2 hab
  have hcd' : 0 < c - d := sub_pos.2 hcd
  have hapb : 0 < a + b := by linarith
  have hcpd : 0 < c + d := by linarith
  have hD : 0 < (a ^ 2 - b ^ 2) * (c ^ 2 - d ^ 2) := by
    have e : (a ^ 2 - b ^ 2) * (c ^ 2 - d ^ 2) = (a - b) * (a + b) * ((c - d) * (c + d)) := by ring
    rw [e]
    exact mul_pos (mul_pos hab' hapb) (mul_pos hcd' hcpd)
  have hD' : 0 < A ^ 2 - B ^ 2 := by
    rw [hJ]
    exact hD
  have hBA : B < A := by
    by_contra h
    push Not at h
    nlinarith [mul_le_mul h h hA0 hB0]
  have hS : A + B ≤ (a + b) * (c + d) := by
    have e : (a + b) * (c + d) = a * c + b * d + (a * d + b * c) := by ring
    rw [e]
    exact add_le_add hA hB
  have e1 : (A + B) / (A - B) = (A + B) ^ 2 / ((a ^ 2 - b ^ 2) * (c ^ 2 - d ^ 2)) := by
    rw [← hJ, div_eq_div_iff (sub_pos.2 hBA).ne' hD'.ne']
    ring
  have e2 : (a + b) / (a - b) * ((c + d) / (c - d)) =
      ((a + b) * (c + d)) ^ 2 / ((a ^ 2 - b ^ 2) * (c ^ 2 - d ^ 2)) := by
    rw [div_mul_div_comm, div_eq_div_iff (mul_pos hab' hcd').ne' hD.ne']
    ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by linarith) hS 2) hD.le

/-- **C2 helper** (pointwise submultiplicativity): if `G` is real differentiable at `u` and `F` at `G u`, both with
`|∂̄| < |∂|`, then `(|∂(F∘G)| + |∂̄(F∘G)|)/(|∂(F∘G)| - |∂̄(F∘G)|)` at `u` is at most the product of the quotients of `F`
at `G u` and of `G` at `u` (the chain rules (6.2), (6.3) bound `|∂(F∘G)|` and `|∂̄(F∘G)|`, and the Jacobian is
multiplicative). -/
theorem s23_c2_quot_comp_le {F G : ℂ → ℂ} {u : ℂ} (hG : DifferentiableAt ℝ G u)
    (hF : DifferentiableAt ℝ F (G u)) (hGj : ‖dzbar G u‖ < ‖dz G u‖) (hFj : ‖dzbar F (G u)‖ < ‖dz F (G u)‖) :
    (‖dz (F ∘ G) u‖ + ‖dzbar (F ∘ G) u‖) / (‖dz (F ∘ G) u‖ - ‖dzbar (F ∘ G) u‖) ≤
      (‖dz F (G u)‖ + ‖dzbar F (G u)‖) / (‖dz F (G u)‖ - ‖dzbar F (G u)‖) *
        ((‖dz G u‖ + ‖dzbar G u‖) / (‖dz G u‖ - ‖dzbar G u‖)) := by
  obtain ⟨h1, h2⟩ := eq6_3 hG
  have hA : ‖dz (F ∘ G) u‖ ≤ ‖dz F (G u)‖ * ‖dz G u‖ + ‖dzbar F (G u)‖ * ‖dzbar G u‖ := by
    rw [eq6_2_dz_comp hG hF, ← h2]
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_mul, norm_mul, Complex.norm_conj]
  have hB : ‖dzbar (F ∘ G) u‖ ≤ ‖dz F (G u)‖ * ‖dzbar G u‖ + ‖dzbar F (G u)‖ * ‖dz G u‖ := by
    rw [eq6_2_dzbar_comp hG hF, ← h1]
    refine (norm_add_le _ _).trans_eq ?_
    rw [norm_mul, norm_mul, Complex.norm_conj]
  have hJ := s23_c2_jacobian_comp hG hF
  simp only [jacobian] at hJ
  exact s23_c2_quot_ineq (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hFj hGj hA hB hJ

/-- **C2 helper** (pointwise, in `ℝ≥0∞`): at a point `u` where `G` and `F` (at `G u`) are real differentiable with
`|∂̄| < |∂|` and their quotients are bounded by `M₁` and `M₂`, the quotient of `F ∘ G` at `u` is at most `M₂ M₁`. -/
theorem s23_c2_ofReal_quot_comp_le {F G : ℂ → ℂ} {u : ℂ} {M₁ M₂ : ℝ≥0∞} (hG : DifferentiableAt ℝ G u)
    (hF : DifferentiableAt ℝ F (G u)) (hGj : ‖dzbar G u‖ < ‖dz G u‖) (hFj : ‖dzbar F (G u)‖ < ‖dz F (G u)‖)
    (hGM : ENNReal.ofReal ((‖dz G u‖ + ‖dzbar G u‖) / (‖dz G u‖ - ‖dzbar G u‖)) ≤ M₁)
    (hFM : ENNReal.ofReal ((‖dz F (G u)‖ + ‖dzbar F (G u)‖) / (‖dz F (G u)‖ - ‖dzbar F (G u)‖)) ≤ M₂) :
    ENNReal.ofReal ((‖dz (F ∘ G) u‖ + ‖dzbar (F ∘ G) u‖) / (‖dz (F ∘ G) u‖ - ‖dzbar (F ∘ G) u‖)) ≤
      M₂ * M₁ := by
  refine (ENNReal.ofReal_le_ofReal (s23_c2_quot_comp_le hG hF hGj hFj)).trans ?_
  rw [ENNReal.ofReal_mul (div_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (sub_pos.2 hFj).le)]
  exact mul_le_mul' hFM hGM

/-- **C2 helper** (a.e. on the domain of a q.c. map): a `K`-q.c. `φ` on `D` is real differentiable with
`|∂̄φ| < |∂φ|` a.e. on `D` (`thm9_3_differentiable_ae`, `thm9_6_cor2_jacobian_pos`), and its quotient is a.e. at most
its essential supremum `maxDilatation φ D`. -/
theorem s23_c2_ae_good {φ : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hφ : IsKQC φ D K) :
    ∀ᵐ u ∂(volume.restrict D), DifferentiableAt ℝ φ u ∧ ‖dzbar φ u‖ < ‖dz φ u‖ ∧
      ENNReal.ofReal ((‖dz φ u‖ + ‖dzbar φ u‖) / (‖dz φ u‖ - ‖dzbar φ u‖)) ≤ maxDilatation φ D := by
  filter_upwards [thm9_3_differentiable_ae hφ, thm9_6_cor2_jacobian_pos hφ,
    ENNReal.ae_le_essSup (μ := volume.restrict D)
      (fun z => ENNReal.ofReal ((‖dz φ z‖ + ‖dzbar φ z‖) / (‖dz φ z‖ - ‖dzbar φ z‖)))] with u h1 h2 h3
  refine ⟨h1, ?_, h3⟩
  unfold jacobian at h2
  nlinarith [norm_nonneg (dz φ u), norm_nonneg (dzbar φ u)]

/-- **C2 helper** (pulling an a.e. statement back through a q.c. map): if `φ` is `K`-q.c. on `U` with `φ(U) ⊆ D` and
`P` holds a.e. on `D`, then `P ∘ φ` holds a.e. on `U` (`abT_ae_image` for the inverse map, `thm7_2_inv`). -/
theorem s23_c2_ae_pullback {φ : ℂ → ℂ} {U D : Set ℂ} {K : ℝ} (hφ : IsKQC φ U K) (hsub : φ '' U ⊆ D)
    {P : ℂ → Prop} (h : ∀ᵐ u ∂(volume.restrict D), P u) : ∀ᵐ w ∂(volume.restrict U), P (φ w) := by
  have hleft : LeftInvOn (Function.invFunOn φ U) φ U := hφ.2.2.1.2.1.leftInvOn_invFunOn
  have h2 := abT_ae_image (thm7_2_inv hφ) (p := fun w => P (φ w)) (by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub h,
      ae_restrict_mem (isOpen_image_of_isKQC hφ).measurableSet] with u hu huD
    show P (φ (Function.invFunOn φ U u))
    rw [Function.invFunOn_eq huD]
    exact hu)
  rwa [hleft.image_image] at h2

/-- **C2 helper**: on an open subset `V` of `φ_x(U_x ∩ U_y)` the chart transition `φ_y ∘ φ_x⁻¹` is holomorphic and
injective (its left inverse is `φ_x ∘ φ_y⁻¹`), hence `1`-q.c. (`isKQC_one_of_conformal`). -/
theorem s23_c2_transition_isKQC [IsManifold 𝓘(ℂ) ω S₀] (x y : S₀) {V : Set ℂ} (hV : IsOpen V)
    (hVsub : V ⊆ (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ y).source) :
    IsKQC (chartTransition y x) V 1 := by
  have e : ∀ w ∈ V, chartTransition x y (chartTransition y x w) = w := fun w hw =>
    (s23_transition_inv y x (hVsub hw).1 (hVsub hw).2).self_of_nhds
  refine isKQC_one_of_conformal hV ⟨fun w hw => ?_, fun w₁ hw₁ w₂ hw₂ h => ?_, rfl⟩
  · exact (s23_transition y x (hVsub hw).1 (hVsub hw).2).1.differentiableWithinAt
  · rw [← e w₁ hw₁, ← e w₂ hw₂, h]

/-- **C2** ((23.4), `K[f ∘ g] ≤ K[f] K[g]`): with the decomposition `T₃ ∘ L_f ∘ L_g ∘ T₁` of `s23_c_decomp`, a.e. on the
domain of the expression of `f ∘ g` at `x` its quotient `(|∂| + |∂̄|)/(|∂| - |∂̄|)` equals that of `L_f ∘ L_g` at `T₁ w`
(`s23_quot_comp_left`/`_right`), which is at most the product of those of `L_f` and `L_g` at the corresponding points
(at points of differentiability with positive Jacobians); these are `≤ K[f]`, `≤ K[g]` a.e. (the essential suprema,
pulled back through the q.c. maps `T₁` and `L_g ∘ T₁`, which preserve null sets). -/
theorem s23_c_maxdil [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₂] {g : S₀ ≃ₜ S₁} {f : S₁ ≃ₜ S₂} {K₁ K₂ : ℝ}
    (hg : IsKQCRS g K₁) (hf : IsKQCRS f K₂) : maxDilatationRS (f ∘ g) ≤ maxDilatationRS f * maxDilatationRS g := by
  refine iSup_le fun x => essSup_le_of_ae_le _ ?_
  refine s13x_ae_of_local (L := ∅) measure_empty fun z₀ hz₀ => ?_
  obtain ⟨U, hUo, hz₀U, -, hU⟩ := s23_c_decomp g f x hz₀.1
  set p₀ := (chartAt ℂ x).symm z₀
  set V : Set ℂ := U ∩ ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (chartAt ℂ p₀).source)
  have hVo : IsOpen V := hUo.inter ((chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ p₀).open_source)
  refine ⟨V, hVo, ⟨hz₀U, hz₀.1.1, mem_chart_source ℂ p₀⟩, ?_⟩
  have hLg := hg.2 p₀
  have hLf := hf.2 (g p₀)
  have hT₁ := s23_c2_transition_isKQC x p₀ hVo inter_subset_right
  have hsub₁ : chartTransition p₀ x '' V ⊆ localMapDomain g p₀ := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hU w hw.1).1
  have hsub₂ : (localMapExpr g p₀ ∘ chartTransition p₀ x) '' V ⊆ localMapDomain f (g p₀) := by
    rintro _ ⟨w, hw, rfl⟩
    exact (hU w hw.1).2.1
  filter_upwards [s23_c2_ae_pullback hT₁ hsub₁ (s23_c2_ae_good hLg),
    s23_c2_ae_pullback (thm7_1_comp hT₁ hLg hsub₁) hsub₂ (s23_c2_ae_good hLf),
    ae_restrict_mem hVo.measurableSet] with w hwa hwb hwV
  obtain ⟨hGd, hGj, hGM⟩ := hwa
  obtain ⟨hFd, hFj, hFM⟩ := hwb
  obtain ⟨hwU, hwt, hws⟩ := hwV
  obtain ⟨hd1, hd2, hd3, hd4, -⟩ := hU w hwU
  have hcont : ContinuousAt ((localMapExpr f (g p₀) ∘ localMapExpr g p₀) ∘ chartTransition p₀ x) w :=
    ((hLf.2.2.1.1.continuousAt (hLf.1.mem_nhds hd2)).comp
      (hLg.2.2.1.1.continuousAt (hLg.1.mem_nhds hd1))).comp (s23_transition p₀ x hwt hws).1.continuousAt
  have hev : localMapExpr (⇑f ∘ ⇑g) x =ᶠ[𝓝 w] chartTransition (f (g x)) (f (g p₀)) ∘
      ((localMapExpr f (g p₀) ∘ localMapExpr g p₀) ∘ chartTransition p₀ x) :=
    Filter.eventuallyEq_of_mem (hVo.mem_nhds ⟨hwU, hwt, hws⟩) fun v hv => (hU v hv.1).2.2.2.2
  obtain ⟨hT3t, hT3s, -⟩ := s23_transition_mem hd3 hd4
  obtain ⟨hT1t, hT1s, -⟩ := s23_transition_mem hwt hws
  rw [s23_c2_quot_congr hev,
    s23_quot_comp_left hcont (s23_transition (f (g x)) (f (g p₀)) hd3 hd4).1
      (s23_transition (f (g p₀)) (f (g x)) hT3t hT3s).1 (s23_transition_inv (f (g x)) (f (g p₀)) hd3 hd4),
    s23_quot_comp_right (s23_transition p₀ x hwt hws).1 (s23_transition x p₀ hT1t hT1s).1
      (s23_transition_inv p₀ x hwt hws) (s23_transition_inv x p₀ hT1t hT1s)]
  exact s23_c2_ofReal_quot_comp_le hGd hFd hGj hFj
    (hGM.trans (le_iSup (fun y => maxDilatation (localMapExpr g y) (localMapDomain g y)) p₀))
    (hFM.trans (le_iSup (fun y => maxDilatation (localMapExpr f y) (localMapDomain f y)) (g p₀)))

/-- (23.4): `K[f ∘ g] ≤ K[f] K[g]`, and the composition of q.c. maps is q.c.  (Holomorphic atlases
assumed, corrected 2026-09-25: the local expressions of `f ∘ g` pass through non-preferred charts.) -/
theorem eq23_4 [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁] [IsManifold 𝓘(ℂ) ω S₂] {g : S₀ ≃ₜ S₁}
    {f : S₁ ≃ₜ S₂} {K₁ K₂ : ℝ} (hg : IsKQCRS g K₁) (hf : IsKQCRS f K₂) :
    IsKQCRS (g.trans f) (K₁ * K₂) ∧ maxDilatationRS (f ∘ g) ≤ maxDilatationRS f * maxDilatationRS g := by
  exact ⟨s23_c_qc hg hf, s23_c_maxdil hg hf⟩

/-- The centre `φ_p(p)` of the chart at `p` lies in the domain of the local expression of `f` at `p`, and the local
expression sends it to the centre `φ_{f p}(f p)` of the chart at `f p`. -/
theorem s23_h_center (f : S₀ → S₁) (p : S₀) :
    chartAt ℂ p p ∈ localMapDomain f p ∧ localMapExpr f p (chartAt ℂ p p) = chartAt ℂ (f p) (f p) := by
  have h1 : (chartAt ℂ p).symm (chartAt ℂ p p) = p := (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  refine ⟨⟨(chartAt ℂ p).map_source (mem_chart_source ℂ p), ?_⟩, ?_⟩
  · show f ((chartAt ℂ p).symm (chartAt ℂ p p)) ∈ (chartAt ℂ (f p)).source
    rw [h1]
    exact mem_chart_source ℂ (f p)
  · show chartAt ℂ (f p) (f ((chartAt ℂ p).symm (chartAt ℂ p p))) = chartAt ℂ (f p) (f p)
    rw [h1]

/-- A homeomorphism of Riemann surfaces whose local expression at `p` is `1`-q.c. is holomorphic at `p`: that
expression is conformal on its open domain (`thm7_3_one_qc_conformal`), which contains `φ_p(p)`
(`s23_mdifferentiableAt_iff`). -/
theorem s23_h_mdifferentiableAt [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ ≃ₜ S₁} {p : S₀}
    (hp : IsKQC (localMapExpr f p) (localMapDomain f p) 1) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f p := by
  have hmem := (s23_h_center f p).1
  exact (s23_mdifferentiableAt_iff (f := f) (mem_chart_source ℂ p) (mem_chart_source ℂ (f p))).2
    ⟨f.continuous.continuousAt,
      ((thm7_3_one_qc_conformal hp).1 _ hmem).differentiableAt (hp.1.mem_nhds hmem)⟩

/-- If the local expression `L` of a homeomorphism `f` at `p` is `1`-q.c., then `f⁻¹` is holomorphic at `f p`: on the
open image `L(D)` of the domain `D` of `L`, the local expression `φ_p ∘ f⁻¹ ∘ φ_{f p}⁻¹` of `f⁻¹` at `f p` is the
inverse of the conformal map `L` (`IsConformalOnto.symm`), and `φ_{f p}(f p) = L(φ_p(p)) ∈ L(D)`. -/
theorem s23_h_mdifferentiableAt_symm [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ ≃ₜ S₁} {p : S₀}
    (hp : IsKQC (localMapExpr f p) (localMapDomain f p) 1) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f.symm (f p) := by
  obtain ⟨hmem, hcen⟩ := s23_h_center f p
  have hc := thm7_3_one_qc_conformal hp
  have hV : IsOpen (localMapExpr f p '' localMapDomain f p) := isOpen_image_of_isKQC hp
  have hw₀ : chartAt ℂ (f p) (f p) ∈ localMapExpr f p '' localMapDomain f p := ⟨_, hmem, hcen⟩
  have heq : (fun z => chartAt ℂ p (f.symm ((chartAt ℂ (f p)).symm z))) =ᶠ[𝓝 (chartAt ℂ (f p) (f p))]
      Function.invFunOn (localMapExpr f p) (localMapDomain f p) := by
    filter_upwards [hV.mem_nhds hw₀] with w hw
    obtain ⟨u, hu, rfl⟩ := hw
    have hu2 : f ((chartAt ℂ p).symm u) ∈ (chartAt ℂ (f p)).source := hu.2
    rw [hc.2.1.leftInvOn_invFunOn hu]
    show chartAt ℂ p (f.symm ((chartAt ℂ (f p)).symm (chartAt ℂ (f p) (f ((chartAt ℂ p).symm u))))) = u
    rw [(chartAt ℂ (f p)).left_inv hu2, f.symm_apply_apply, (chartAt ℂ p).right_inv hu.1]
  have hfp : f.symm (f p) ∈ (chartAt ℂ p).source := by
    rw [f.symm_apply_apply]
    exact mem_chart_source ℂ p
  exact (s23_mdifferentiableAt_iff (f := f.symm) (mem_chart_source ℂ (f p)) hfp).2
    ⟨f.symm.continuous.continuousAt,
      (((hc.symm hp.1).1 _ hw₀).differentiableAt (hV.mem_nhds hw₀)).congr_of_eventuallyEq heq⟩

/-- The local expression of a holomorphic homeomorphism is conformal on its open domain (holomorphic by
`s23_mdifferentiableAt_iff`, injective as a composite of injective maps), hence `1`-q.c. (`isKQC_one_of_conformal`). -/
theorem s23_h_isKQC_one [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁] {f : S₀ ≃ₜ S₁}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (x : S₀) : IsKQC (localMapExpr f x) (localMapDomain f x) 1 := by
  refine isKQC_one_of_conformal (s23_localMapDomain_isOpen f.continuous x)
    ⟨fun u hu => ?_, fun u hu v hv huv => ?_, rfl⟩
  · have hd := ((s23_mdifferentiableAt_iff (f := f) (y := f x) ((chartAt ℂ x).map_target hu.1) hu.2).1
      (hf ((chartAt ℂ x).symm u))).2
    rw [(chartAt ℂ x).right_inv hu.1] at hd
    exact hd.differentiableWithinAt
  · have hu2 : f ((chartAt ℂ x).symm u) ∈ (chartAt ℂ (f x)).source := hu.2
    have hv2 : f ((chartAt ℂ x).symm v) ∈ (chartAt ℂ (f x)).source := hv.2
    have h1 : (chartAt ℂ x).symm u = (chartAt ℂ x).symm v := f.injective ((chartAt ℂ (f x)).injOn hu2 hv2 huv)
    rw [← (chartAt ℂ x).right_inv hu.1, ← (chartAt ℂ x).right_inv hv.1, h1]

/-- §23.1: a `1`-quasiconformal map of Riemann surfaces is a conformal (biholomorphic) map. -/
theorem isKQCRS_one_iff [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁] (f : S₀ ≃ₜ S₁) :
    IsKQCRS f 1 ↔ IsBiholomorphic f := by
  refine ⟨fun hf => ⟨fun p => s23_h_mdifferentiableAt (hf.2 p), f.symm, fun q => ?_, f.symm_apply_apply,
    f.apply_symm_apply⟩, fun hb => ⟨le_rfl, s23_h_isKQC_one hb.1⟩⟩
  have h := s23_h_mdifferentiableAt_symm (hf.2 (f.symm q))
  rwa [f.apply_symm_apply] at h

/-! ## §23.2 Lifting -/

/-- The map `ℍ → ℍ` viewed as a map `ℂ → ℂ` (junk value `0` off `ℍ`). -/
def liftToC (F : UpperHalfPlane → UpperHalfPlane) (z : ℂ) : ℂ :=
  if hz : 0 < z.im then (F ⟨z, hz⟩ : ℂ) else 0

/-- `F` is a lift of `f : S₀ → S₁` to the universal coverings `p₀ : ℍ → S₀`, `p₁ : ℍ → S₁`. -/
def IsLift (p₀ : UpperHalfPlane → S₀) (p₁ : UpperHalfPlane → S₁) (f : S₀ → S₁)
    (F : UpperHalfPlane ≃ₜ UpperHalfPlane) : Prop :=
  ∀ τ, p₁ (F τ) = f (p₀ τ)

/-! ### s36h Stage 2 (coordinator 553e2d): lifts to `ℍ`, the q.c. lift, the deck correspondence (`h23l_`) -/

/-- `liftToC F` agrees with `F` on `ℍ`. -/
theorem h23l_liftToC_coe (F : UpperHalfPlane → UpperHalfPlane) (τ : UpperHalfPlane) :
    liftToC F (τ : ℂ) = F τ := by
  unfold liftToC
  simp only [τ.coe_im_pos, ↓reduceDIte]

/-- On `ℍ`, `liftToC F` is `F ∘ ofComplex`. -/
theorem h23l_liftToC_eq (F : UpperHalfPlane → UpperHalfPlane) {z : ℂ} (hz : z ∈ upperHalf) :
    liftToC F z = F (UpperHalfPlane.ofComplex z) := by
  have hz' : 0 < z.im := hz
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz']
  unfold liftToC
  simp only [hz', ↓reduceDIte]

/-- `liftToC F` is continuous on `ℍ` for a continuous `F`. -/
theorem h23l_liftToC_continuousOn {F : UpperHalfPlane → UpperHalfPlane} (hF : Continuous F) :
    ContinuousOn (liftToC F) upperHalf := by
  intro z hz
  have hz' : 0 < z.im := hz
  have hev : (fun w => ((F (UpperHalfPlane.ofComplex w) : UpperHalfPlane) : ℂ)) =ᶠ[𝓝 z] liftToC F := by
    filter_upwards [isOpen_upperHalf.mem_nhds hz] with w hw
    exact (h23l_liftToC_eq F hw).symm
  have hc : ContinuousAt (fun w => ((F (UpperHalfPlane.ofComplex w) : UpperHalfPlane) : ℂ)) z :=
    UpperHalfPlane.continuous_coe.continuousAt.comp
      (hF.continuousAt.comp (UpperHalfPlane.mdifferentiableAt_ofComplex hz').continuousAt)
  exact (hc.congr hev).continuousWithinAt

/-- The lift of a homeomorphism of `ℍ`, viewed as a map of `ℂ`, is injective on `ℍ`. -/
theorem h23l_liftToC_injOn (F : UpperHalfPlane ≃ₜ UpperHalfPlane) : InjOn (liftToC F) upperHalf := by
  intro a ha b hb h
  rw [h23l_liftToC_eq F ha, h23l_liftToC_eq F hb] at h
  have h1 := F.injective (UpperHalfPlane.ext h)
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < a.im from ha),
    UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < b.im from hb)] at h1
  exact congrArg UpperHalfPlane.coe h1

/-- **L1** (the lifting criterion, Mathlib's `IsCoveringMap.existsUnique_continuousMap_lifts`: `ℍ` is simply
connected and locally path connected): a continuous map `g : ℍ → Y` lifts through a covering `p₁ : ℍ → Y`, with a
prescribed value `τ₁` over `g τ₀`. -/
theorem h23l_exists_continuous_lift {Y : Type*} [TopologicalSpace Y] {p₁ : UpperHalfPlane → Y}
    (hp₁ : IsCoveringMap p₁) {g : UpperHalfPlane → Y} (hg : Continuous g) {τ₀ τ₁ : UpperHalfPlane}
    (h : p₁ τ₁ = g τ₀) :
    ∃ F : UpperHalfPlane → UpperHalfPlane, Continuous F ∧ (∀ τ, p₁ (F τ) = g τ) ∧ F τ₀ = τ₁ := by
  obtain ⟨F, ⟨hF0, hFc⟩, -⟩ := hp₁.existsUnique_continuousMap_lifts ⟨g, hg⟩ τ₀ τ₁ h
  exact ⟨F, F.continuous, fun τ => congrFun hFc τ, hF0⟩

/-- **L2** [P1, stub] A continuous lift `F : ℍ → ℍ` of a homeomorphism `f : X → Y` through covering maps `p₀`, `p₁` is
a homeomorphism of `ℍ`: lift `f⁻¹ ∘ p₁` through `p₀` sending `F τ₀` to `τ₀` (`h23l_exists_continuous_lift`); both
composites of the two lifts are lifts of the identity with a fixed point, hence the identity
(`IsCoveringMap.eq_of_comp_eq`, `ℍ` connected). -/
theorem h23l_lift_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {p₀ : UpperHalfPlane → X}
    {p₁ : UpperHalfPlane → Y} (hp₀ : IsCoveringMap p₀) (hp₁ : IsCoveringMap p₁) (f : X ≃ₜ Y)
    {F : UpperHalfPlane → UpperHalfPlane} (hFc : Continuous F) (hF : ∀ τ, p₁ (F τ) = f (p₀ τ)) :
    ∃ F' : UpperHalfPlane ≃ₜ UpperHalfPlane, ⇑F' = F := by
  have hg : Continuous (fun τ => f.symm (p₁ τ)) := f.symm.continuous.comp hp₁.continuous
  have hbase : p₀ UpperHalfPlane.I = (fun τ => f.symm (p₁ τ)) (F UpperHalfPlane.I) := by
    simp only [hF, Homeomorph.symm_apply_apply]
  obtain ⟨G, hGc, hG, hG0⟩ := h23l_exists_continuous_lift hp₀ hg hbase
  have hGF : (fun τ => G (F τ)) = id := by
    refine hp₀.eq_of_comp_eq (hGc.comp hFc) continuous_id ?_ UpperHalfPlane.I hG0
    funext τ
    simp only [Function.comp_apply, id, hG, hF, Homeomorph.symm_apply_apply]
  have hFG : (fun τ => F (G τ)) = id := by
    refine hp₁.eq_of_comp_eq (hFc.comp hGc) continuous_id ?_ (F UpperHalfPlane.I) ?_
    · funext τ
      simp only [Function.comp_apply, id, hF, hG, Homeomorph.apply_symm_apply]
    · simp only [hG0, id]
  exact ⟨⟨⟨F, G, congrFun hGF, congrFun hFG⟩, hFc, hGc⟩, rfl⟩

/-- **Q1a** [P2, stub] In a holomorphic atlas, a holomorphic covering map `p₀ : ℍ → S₀` is conformal in the chart at
`p₀ τ` near `τ`: on some open `U ∋ τ` inside `ℍ`, `p₀` maps into the source of that chart and `z ↦ φ_{p₀ τ}(p₀ z)` is
`1`-q.c. (it is holomorphic, by `MDifferentiable` and the holomorphic compatibility of the charts, and injective near
`τ` because a covering map is a local homeomorphism).  False without `[IsManifold 𝓘(ℂ) ω S₀]` (scout A's radial
atlas). -/
theorem h23l_chart_proj [IsManifold 𝓘(ℂ) ω S₀] {p₀ : UpperHalfPlane → S₀} (hcov : IsCoveringMap p₀)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p₀) (τ : UpperHalfPlane) :
    ∃ U : Set ℂ, IsOpen U ∧ (τ : ℂ) ∈ U ∧ U ⊆ upperHalf ∧
      (∀ z ∈ U, p₀ (UpperHalfPlane.ofComplex z) ∈ (chartAt ℂ (p₀ τ)).source) ∧
      IsKQC (fun z => chartAt ℂ (p₀ τ) (p₀ (UpperHalfPlane.ofComplex z))) U 1 := by
  obtain ⟨e, hτe, hpe⟩ := hcov.isLocalHomeomorph τ
  set W : Set UpperHalfPlane := e.source ∩ p₀ ⁻¹' (chartAt ℂ (p₀ τ)).source
  have hWo : IsOpen W := e.open_source.inter
    (hcov.continuous.isOpen_preimage _ (chartAt ℂ (p₀ τ)).open_source)
  set U : Set ℂ := upperHalf ∩ UpperHalfPlane.ofComplex ⁻¹' W
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
    exact ⟨hτe, mem_chart_source ℂ (p₀ τ)⟩
  refine ⟨U, hUo, hτU, fun z hz => hz.1, fun z hz => hz.2.2, ?_⟩
  refine isKQC_one_of_conformal hUo ⟨fun z hz => ?_, fun z hz w hw hzw => ?_, rfl⟩
  · have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun z => chartAt ℂ (p₀ τ) (p₀ (UpperHalfPlane.ofComplex z))) z :=
      (mdifferentiableAt_atlas (chart_mem_atlas ℂ (p₀ τ)) hz.2.2).comp z
        ((hhol _).comp z (UpperHalfPlane.mdifferentiableAt_ofComplex hz.1))
    exact (mdifferentiableAt_iff_differentiableAt.1 h1).differentiableWithinAt
  · have h1 : p₀ (UpperHalfPlane.ofComplex z) = p₀ (UpperHalfPlane.ofComplex w) :=
      (chartAt ℂ (p₀ τ)).injOn hz.2.2 hw.2.2 hzw
    rw [hpe] at h1
    have h2 := e.injOn hz.2.1 hw.2.1 h1
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz.1, UpperHalfPlane.ofComplex_apply_of_im_pos hw.1] at h2
    exact congrArg UpperHalfPlane.coe h2

/-- `(g • τ : ℂ) = (a τ + b) / (c τ + d)` for `g ∈ SL(2, ℝ)`. -/
theorem h23l_b_coe_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    ((g • τ : UpperHalfPlane) : ℂ) = ((g 0 0 : ℂ) * τ + g 0 1) / ((g 1 0 : ℂ) * τ + g 1 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

/-- The determinant identity `a d - b c = 1` of `g ∈ SL(2, ℝ)`, over `ℂ`. -/
theorem h23l_b_det (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

/-- The denominator `c z + d` of `g ∈ SL(2, ℝ)` does not vanish on `ℍ`. -/
theorem h23l_b_den_ne (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : z ∈ upperHalf) :
    (g 1 0 : ℂ) * z + g 1 1 ≠ 0 := by
  have hz' : 0 < z.im := hz
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, zero_im, add_re, mul_re,
    sub_zero, zero_re] at him hre
  have hc : g 1 0 = 0 := by
    rcases mul_eq_zero.1 him with h1 | h1
    · exact h1
    · exact absurd h1 hz'.ne'
  rw [hc, zero_mul, zero_add] at hre
  have hdet := h23l_b_det g
  rw [hc, hre] at hdet
  simp at hdet

/-- Local facts on a Möbius map `T w = (a w + b)/(c w + d)` with `a d - b c = 1` near a point `z` with
`c z + d ≠ 0`: `T` is holomorphic at `z`, the Möbius map `S u = (d u - b)/(-c u + a)` is holomorphic at `T z`,
`S ∘ T = id` near `z`, `T ∘ S = id` near `T z`, and `T'(z) = 1/(c z + d)²`. -/
theorem h23l_b_mob {a b c d : ℂ} (hdet : a * d - b * c = 1) {z : ℂ} (hz : c * z + d ≠ 0) :
    DifferentiableAt ℂ (fun w => (a * w + b) / (c * w + d)) z ∧
      DifferentiableAt ℂ (fun u => (d * u - b) / (-c * u + a)) ((a * z + b) / (c * z + d)) ∧
      (∀ᶠ w in 𝓝 z, (d * ((a * w + b) / (c * w + d)) - b) / (-c * ((a * w + b) / (c * w + d)) + a) = w) ∧
      (∀ᶠ u in 𝓝 ((a * z + b) / (c * z + d)),
        (a * ((d * u - b) / (-c * u + a)) + b) / (c * ((d * u - b) / (-c * u + a)) + d) = u) ∧
      deriv (fun w => (a * w + b) / (c * w + d)) z = 1 / (c * z + d) ^ 2 := by
  have hden : ∀ w, c * w + d ≠ 0 → -c * ((a * w + b) / (c * w + d)) + a = 1 / (c * w + d) := by
    intro w hw
    field_simp
    linear_combination hdet
  have hnum : ∀ w, c * w + d ≠ 0 → d * ((a * w + b) / (c * w + d)) - b = w / (c * w + d) := by
    intro w hw
    rw [eq_div_iff hw, sub_mul, mul_assoc, div_mul_cancel₀ _ hw]
    linear_combination w * hdet
  have hden' : ∀ u, -c * u + a ≠ 0 → c * ((d * u - b) / (-c * u + a)) + d = 1 / (-c * u + a) := by
    intro u hu
    rw [eq_div_iff hu, add_mul, mul_assoc, div_mul_cancel₀ _ hu]
    linear_combination hdet
  have hnum' : ∀ u, -c * u + a ≠ 0 → a * ((d * u - b) / (-c * u + a)) + b = u / (-c * u + a) := by
    intro u hu
    rw [eq_div_iff hu, add_mul, mul_assoc, div_mul_cancel₀ _ hu]
    linear_combination u * hdet
  have hTz : -c * ((a * z + b) / (c * z + d)) + a ≠ 0 := by
    rw [hden z hz]
    exact one_div_ne_zero hz
  have hev1 : ∀ᶠ w in 𝓝 z, c * w + d ≠ 0 :=
    ((continuous_const.mul continuous_id).add continuous_const).continuousAt.eventually_ne hz
  have hev2 : ∀ᶠ u in 𝓝 ((a * z + b) / (c * z + d)), -c * u + a ≠ 0 :=
    ((continuous_const.mul continuous_id).add continuous_const).continuousAt.eventually_ne hTz
  have hT : HasDerivAt (fun w => (a * w + b) / (c * w + d)) (1 / (c * z + d) ^ 2) z := by
    have h := (((hasDerivAt_id' z).const_mul a).add_const b).div
      (((hasDerivAt_id' z).const_mul c).add_const d) hz
    convert h using 1
    field_simp
    linear_combination -hdet
  refine ⟨hT.differentiableAt, ?_, ?_, ?_, hT.deriv⟩
  · exact (((differentiableAt_id.const_mul d).sub_const b).div
      ((differentiableAt_id.const_mul (-c)).add_const a) hTz)
  · filter_upwards [hev1] with w hw
    rw [hden w hw, hnum w hw, div_div, mul_one_div_cancel hw, div_one]
  · filter_upwards [hev2] with u hu
    rw [hden' u hu, hnum' u hu, div_div, mul_one_div_cancel hu, div_one]

/-- **A** [P2, stub] (23.5), pointwise: if `F ∘ γ = δ ∘ F` on `ℍ` (`γ, δ ∈ SL(2, ℝ)`), then at every `z ∈ ℍ` the
dilatation `μ` of `liftToC F` satisfies `μ(z) = μ(γ z) (c z + d)²/conj((c z + d)²)`: near `z`,
`liftToC F ∘ γ = δ ∘ liftToC F`; the dilatation is unchanged by the holomorphic post-composition `δ`
(`s23_dilatation_comp_left`) and is multiplied by `conj γ'(z)/γ'(z) = (c z + d)²/conj((c z + d)²)` under the
pre-composition `γ` (`s23_dilatation_comp_right`). -/
theorem h23l_dilatation_conj {F : UpperHalfPlane ≃ₜ UpperHalfPlane} {γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγδ : ∀ τ, F (γ • τ) = δ • F τ) {z : ℂ} (hz : z ∈ upperHalf) :
    complexDilatation (liftToC F) z =
      complexDilatation (liftToC F) ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) *
        (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)) := by
  have hgz : liftToC F z ∈ upperHalf := by
    rw [h23l_liftToC_eq F hz]
    exact (F (UpperHalfPlane.ofComplex z)).coe_im_pos
  obtain ⟨hTd, hSd, hST, hTS, hTder⟩ := h23l_b_mob (h23l_b_det γ) (h23l_b_den_ne γ hz)
  obtain ⟨hDd, hKd, hKD, -, -⟩ := h23l_b_mob (h23l_b_det δ) (h23l_b_den_ne δ hgz)
  have hcont : ContinuousAt (liftToC F) z :=
    (h23l_liftToC_continuousOn F.continuous z hz).continuousAt (isOpen_upperHalf.mem_nhds hz)
  have hev : (liftToC F ∘ fun w => ((γ 0 0 : ℂ) * w + γ 0 1) / ((γ 1 0 : ℂ) * w + γ 1 1)) =ᶠ[𝓝 z]
      (fun w => ((δ 0 0 : ℂ) * w + δ 0 1) / ((δ 1 0 : ℂ) * w + δ 1 1)) ∘ liftToC F := by
    filter_upwards [isOpen_upperHalf.mem_nhds hz] with w hw
    have hw' : 0 < w.im := hw
    have e1 : ((γ • (⟨w, hw'⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) =
        ((γ 0 0 : ℂ) * w + γ 0 1) / ((γ 1 0 : ℂ) * w + γ 1 1) := h23l_b_coe_smul γ ⟨w, hw'⟩
    have e2 := h23l_b_coe_smul δ (F ⟨w, hw'⟩)
    simp only [Function.comp_apply]
    rw [← e1, h23l_liftToC_coe, hγδ, e2, h23l_liftToC_eq F hw, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
  have h1 := s23_dilatation_comp_left hcont hDd hKd hKD
  have h2 := s23_dilatation_comp_right (g := liftToC F) hTd hSd hST hTS
  have h3 : complexDilatation (liftToC F ∘ fun w => ((γ 0 0 : ℂ) * w + γ 0 1) / ((γ 1 0 : ℂ) * w + γ 1 1)) z =
      complexDilatation ((fun w => ((δ 0 0 : ℂ) * w + δ 0 1) / ((δ 1 0 : ℂ) * w + δ 1 1)) ∘ liftToC F) z := by
    rw [complexDilatation, complexDilatation, dz, dzbar, dz, dzbar, hev.fderiv_eq]
  rw [← h1, ← h3, h2, hTder]
  congr 1
  rw [map_div₀, map_one, div_div_div_cancel_left' _ _ one_ne_zero]

/-- **Q3** (deck correspondence; S36's `h36t_deck` for two universes): a lift `F` of `f` conjugates each `γ ∈ Γ₀` to
some `δ ∈ Γ₁`, `F ∘ γ = δ ∘ F` (uniqueness of lifts through the covering `p₁`). -/
theorem h23l_deck {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    {p₁ : UpperHalfPlane → S₁} (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁) {f : S₀ → S₁}
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₀ p₁ f F) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ Γ₀) : ∃ δ ∈ Γ₁, ∀ τ, F (γ • τ) = δ • F τ := by
  have hpγ : ∀ τ, p₀ (γ • τ) = p₀ τ := fun τ => ((hp₀.2.2.2 τ (γ • τ)).2 ⟨γ, hγ, rfl⟩).symm
  have h0 : p₁ (F UpperHalfPlane.I) = p₁ (F (γ • UpperHalfPlane.I)) := by rw [hF, hF, hpγ]
  obtain ⟨δ, hδ, hδe⟩ := (hp₁.2.2.2 _ _).1 h0
  refine ⟨δ, hδ, fun τ => ?_⟩
  have hcomp : p₁ ∘ (fun τ => F (γ • τ)) = p₁ ∘ (fun τ => δ • F τ) := by
    funext τ
    simp only [Function.comp_apply]
    rw [hF, hpγ, ← hF]
    exact (hp₁.2.2.2 _ _).2 ⟨δ, hδ, rfl⟩
  have h := hp₁.1.eq_of_comp_eq (F.continuous.comp (continuous_const_smul γ))
    ((continuous_const_smul δ).comp F.continuous) hcomp UpperHalfPlane.I hδe.symm
  exact congrFun h τ

/-- **Q1** (the first half of §23.2): the lift `F` of a `K`-q.c. map `f` is `K`-q.c. on `ℍ`.  Near `τ₀`, with
`ψ₀ = φ_{p₀ τ₀} ∘ p₀` and `ψ₁ = φ_{p₁(F τ₀)} ∘ p₁` conformal (`h23l_chart_proj`), `liftToC F = ψ₁⁻¹ ∘ L ∘ ψ₀` where
`L = localMapExpr f (p₀ τ₀)` is `K`-q.c.; so `liftToC F` is `K`-q.c. near `τ₀` (`thm7_1_comp`, `thm7_2_inv`), and on
`ℍ` by `s23_lg`. -/
theorem h23l_lift_isKQC [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} {p₁ : UpperHalfPlane → S₁} (hp₀ : IsUniformization Γ₀ p₀)
    (hp₁ : IsUniformization Γ₁ p₁) {f : S₀ ≃ₜ S₁} {K : ℝ} (hf : IsKQCRS f K)
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₀ p₁ f F) : IsKQC (liftToC F) upperHalf K := by
  refine s23_lg isOpen_upperHalf hf.1 (h23l_liftToC_injOn F) fun z₀ hz₀ => ?_
  have hz₀' : 0 < z₀.im := hz₀
  obtain ⟨U₀, hU₀o, hτU₀, hU₀H, hU₀s, hψ₀⟩ := h23l_chart_proj hp₀.1 hp₀.2.1 ⟨z₀, hz₀'⟩
  obtain ⟨U₁, hU₁o, hτU₁, -, -, hψ₁⟩ := h23l_chart_proj hp₁.1 hp₁.2.1 (F ⟨z₀, hz₀'⟩)
  have hFx : p₁ (F ⟨z₀, hz₀'⟩) = f (p₀ ⟨z₀, hz₀'⟩) := hF _
  -- the local identity `ψ₁ ∘ liftToC F = L ∘ ψ₀` on `U₀`
  have hkey : ∀ z ∈ U₀, chartAt ℂ (p₁ (F ⟨z₀, hz₀'⟩)) (p₁ (UpperHalfPlane.ofComplex (liftToC F z))) =
      localMapExpr f (p₀ ⟨z₀, hz₀'⟩) (chartAt ℂ (p₀ ⟨z₀, hz₀'⟩) (p₀ (UpperHalfPlane.ofComplex z))) := by
    intro z hz
    rw [h23l_liftToC_eq F (hU₀H hz), UpperHalfPlane.ofComplex_apply, hFx, hF (UpperHalfPlane.ofComplex z)]
    unfold localMapExpr
    rw [(chartAt ℂ (p₀ ⟨z₀, hz₀'⟩)).left_inv (hU₀s z hz)]
  set V : Set ℂ := (U₀ ∩ liftToC F ⁻¹' U₁) ∩
    (fun z => chartAt ℂ (p₀ ⟨z₀, hz₀'⟩) (p₀ (UpperHalfPlane.ofComplex z))) ⁻¹'
      localMapDomain f (p₀ ⟨z₀, hz₀'⟩) with hVdef
  have hV : IsOpen V :=
    (hψ₀.2.2.1.1.mono inter_subset_left).isOpen_inter_preimage
      (((h23l_liftToC_continuousOn F.continuous).mono hU₀H).isOpen_inter_preimage hU₀o hU₁o)
      (s23_localMapDomain_isOpen f.continuous _)
  have hz₀V : z₀ ∈ V := by
    refine ⟨⟨hτU₀, ?_⟩, ?_⟩
    · show liftToC F ((⟨z₀, hz₀'⟩ : UpperHalfPlane) : ℂ) ∈ U₁
      rw [h23l_liftToC_coe]
      exact hτU₁
    · have e : UpperHalfPlane.ofComplex z₀ = ⟨z₀, hz₀'⟩ := UpperHalfPlane.ofComplex_apply_of_im_pos hz₀'
      simp only [mem_preimage, e]
      exact (s23_h_center f _).1
  have h1 := ac_t_isKQC_restrict hψ₀ hV (fun z hz => hz.1.1)
  have h2 := thm7_1_comp h1 (hf.2 (p₀ ⟨z₀, hz₀'⟩)) (by rintro _ ⟨z, hz, rfl⟩; exact hz.2)
  have h3 := thm7_1_comp h2 (thm7_2_inv hψ₁) (by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨liftToC F z, hz.1.2, hkey z hz.1.1⟩)
  rw [one_mul, mul_one] at h3
  refine ⟨V, hV, hz₀V, fun z hz => hU₀H hz.1.1, ad_isKQC_congr h3 fun z hz => ?_⟩
  simp only [Function.comp_apply]
  rw [← hkey z hz.1.1]
  exact (hψ₁.2.2.1.2.1.leftInvOn_invFunOn hz.1.2).symm

/-- §23.2: a homeomorphism of Riemann surfaces uniformized by `ℍ` lifts to a homeomorphism of `ℍ`;
the lift can be chosen to send a given point over `x` to a given point over `f(x)`. -/
theorem exists_lift [T2Space S₀] [ConnectedSpace S₀] [T2Space S₁] [ConnectedSpace S₁]
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    {p₁ : UpperHalfPlane → S₁} (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁)
    (f : S₀ ≃ₜ S₁) (τ₀ τ₁ : UpperHalfPlane) (h : p₁ τ₁ = f (p₀ τ₀)) :
    ∃ F : UpperHalfPlane ≃ₜ UpperHalfPlane, IsLift p₀ p₁ f F ∧ F τ₀ = τ₁ := by
  obtain ⟨F, hFc, hF, hF0⟩ := h23l_exists_continuous_lift hp₁.1 (f.continuous.comp hp₀.1.continuous) h
  obtain ⟨F', hF'⟩ := h23l_lift_homeomorph hp₀.1 hp₁.1 f hFc hF
  exact ⟨F', fun τ => by rw [hF']; exact hF τ, by rw [hF']; exact hF0⟩

/-- §23.2: the lift of a `K`-q.c. map is `K`-q.c., and its complex dilatation `μ` satisfies the
automorphy relation (23.5) `μ(z) = μ(γz) conj(γ'(z))/γ'(z)` for all `γ ∈ Γ₀`.

**Correction.**  The hypotheses `[IsManifold 𝓘(ℂ) ω S₀]`, `[IsManifold 𝓘(ℂ) ω S₁]` were missing:
without holomorphically compatible charts (`[IsManifold 𝓘(ℂ) ω _]`) `IsQCRS`/`IsKQCRS` and
`IsUniformization` do not control the lift, and the statement was **false** (a copy of `ℍ` charted by the
radial stretches `w ↦ (w - x)|w - x|`, with a Lipschitz self-map having no homeomorphic extension, was a
counterexample). -/
theorem lift_isKQC_automorphic [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → S₀} {p₁ : UpperHalfPlane → S₁} (hp₀ : IsUniformization Γ₀ p₀)
    (hp₁ : IsUniformization Γ₁ p₁) {f : S₀ ≃ₜ S₁} {K : ℝ} (hf : IsKQCRS f K)
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₀ p₁ f F) :
    IsKQC (liftToC F) upperHalf K ∧
      ∀ γ ∈ Γ₀, ∀ᵐ z ∂(volume.restrict upperHalf),
        complexDilatation (liftToC F) z =
          complexDilatation (liftToC F) ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) *
            (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)) := by
  refine ⟨h23l_lift_isKQC hp₀ hp₁ hf hF, fun γ hγ => ?_⟩
  obtain ⟨δ, -, hδ⟩ := h23l_deck hp₀ hp₁ hF hγ
  exact ae_restrict_of_forall_mem isOpen_upperHalf.measurableSet fun z hz => h23l_dilatation_conj hδ hz

/-! ### s36h Stage 2 batch D (coordinator 553e2d): helpers moved upstream from S24 (`k24_`), S36 (`c36_d_`, `h36t_`) -/

/-- A real Möbius transformation of determinant `1` has its pole on the real axis: `c z + d ≠ 0` for `Im z ≠ 0`. -/
theorem k24_d_den_ne_zero {a b c d : ℝ} (h : a * d - b * c = 1) {z : ℂ} (hz : z.im ≠ 0) :
    (c : ℂ) * z + d ≠ 0 := by
  intro h0
  have him : c * z.im = 0 := by simpa using congrArg Complex.im h0
  have hc : c = 0 := (mul_eq_zero.1 him).resolve_right hz
  have hd : d = 0 := by simpa [hc] using congrArg Complex.re h0
  rw [hc, hd, mul_zero, mul_zero, sub_zero] at h
  exact zero_ne_one h

/-- The determinant of `γ ∈ SL(2, ℝ)` in coordinates. -/
theorem k24_det_realR (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rwa [Matrix.det_fin_two] at h

/-! ### s36c track (coordinator 553e2d), part D: the geodesic homotopy (Cayley coordinates) -/

/-! ## Real-variable helpers: `sinh y / y`, the radial factor, `tanh` of a difference -/

/-- The function `sinh y / y`, extended by `1` at `y = 0` (the `dslope` of `sinh` at `0`). -/
def c36_d_sinhc : ℝ → ℝ := dslope Real.sinh 0

/-- `sinh y / y` (extended by `1` at `0`) is continuous. -/
theorem c36_d_sinhc_continuous : Continuous c36_d_sinhc := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    exact continuousAt_dslope_same.2 (Real.differentiable_sinh 0)
  · exact (continuousAt_dslope_of_ne hy).2 Real.continuous_sinh.continuousAt

/-- `y · (sinh y / y) = sinh y`, including at `y = 0`. -/
theorem c36_d_mul_sinhc (y : ℝ) : y * c36_d_sinhc y = Real.sinh y := by
  have h := sub_smul_dslope Real.sinh 0 y
  simpa [c36_d_sinhc, Real.sinh_zero] using h

/-- `sinh y / y` (extended by `1` at `0`) never vanishes. -/
theorem c36_d_sinhc_ne_zero (y : ℝ) : c36_d_sinhc y ≠ 0 := by
  by_cases hy : y = 0
  · subst hy
    simp [c36_d_sinhc, dslope_same, Real.deriv_sinh]
  · intro h
    have := c36_d_mul_sinhc y
    rw [h, mul_zero] at this
    exact hy (Real.sinh_eq_zero.1 this.symm)

/-- The radial factor `λ(D, t) = tanh (t D) / tanh D`, written without a singularity at `D = 0`
(where it equals `t`). -/
def c36_d_lam (D t : ℝ) : ℝ :=
  t * (c36_d_sinhc (t * D) / c36_d_sinhc D) * (Real.cosh D / Real.cosh (t * D))

/-- The radial factor is jointly continuous in `(D, t)`. -/
theorem c36_d_lam_continuous : Continuous (fun x : ℝ × ℝ => c36_d_lam x.1 x.2) := by
  unfold c36_d_lam
  refine (continuous_snd.mul ?_).mul ?_
  · exact (c36_d_sinhc_continuous.comp (continuous_snd.mul continuous_fst)).div
      (c36_d_sinhc_continuous.comp continuous_fst) (fun x => c36_d_sinhc_ne_zero _)
  · exact (Real.continuous_cosh.comp continuous_fst).div
      (Real.continuous_cosh.comp (continuous_snd.mul continuous_fst))
      (fun x => (Real.cosh_pos _).ne')

/-- `λ(D, t) · tanh D = tanh (t D)`. -/
theorem c36_d_lam_mul_tanh (D t : ℝ) : c36_d_lam D t * Real.tanh D = Real.tanh (t * D) := by
  have h1 := c36_d_mul_sinhc (t * D)
  have h2 := c36_d_mul_sinhc D
  have h3 := c36_d_sinhc_ne_zero D
  have h5 := (Real.cosh_pos D).ne'
  have h6 := (Real.cosh_pos (t * D)).ne'
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, ← h1, ← h2]
  unfold c36_d_lam
  field_simp

/-- The subtraction formula for `tanh`. -/
theorem c36_d_tanh_sub (x y : ℝ) :
    Real.tanh (x - y) = (Real.tanh x - Real.tanh y) / (1 - Real.tanh x * Real.tanh y) := by
  have hx := (Real.cosh_pos x).ne'
  have hy := (Real.cosh_pos y).ne'
  have hxy : Real.cosh x * Real.cosh y - Real.sinh x * Real.sinh y ≠ 0 := by
    rw [← Real.cosh_sub]; exact (Real.cosh_pos _).ne'
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    Real.sinh_sub, Real.cosh_sub]
  field_simp

/-- `tanh` is nonnegative on `[0, ∞)`. -/
theorem c36_d_tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.2 hx) (Real.cosh_pos x).le

/-- `|tanh x| < 1`. -/
theorem c36_d_abs_tanh_lt_one (x : ℝ) : |Real.tanh x| < 1 :=
  abs_lt.2 ⟨Real.neg_one_lt_tanh x, Real.tanh_lt_one x⟩

/-! ## The Cayley coordinates centred at `p ∈ ℍ` -/

/-- A complex number of norm `< 1` is not `1`. -/
theorem c36_d_one_sub_ne {u : ℂ} (hu : ‖u‖ < 1) : (1 : ℂ) - u ≠ 0 := by
  intro h
  have : u = 1 := (sub_eq_zero.1 h).symm
  rw [this, norm_one] at hu
  exact lt_irrefl _ hu

/-- `q - p̄ ≠ 0` for `p, q ∈ ℍ`. -/
theorem c36_d_sub_conj_ne (p q : UpperHalfPlane) : (q : ℂ) - conj (p : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
  linarith [p.coe_im_pos, q.coe_im_pos]

/-- The disc coordinate `(q - p) / (q - p̄)` of `q` centred at `p`. -/
def c36_d_disc (p q : UpperHalfPlane) : ℂ := ((q : ℂ) - p) / ((q : ℂ) - conj (p : ℂ))

/-- The inverse Cayley map `u ↦ (p - p̄ u) / (1 - u)` from the unit disc back to `ℍ` (sending `0`
to `p`). -/
def c36_d_inv (p : UpperHalfPlane) (u : ℂ) : ℂ := ((p : ℂ) - conj (p : ℂ) * u) / (1 - u)

/-- `|(q - p)/(q - p̄)| = tanh (d(p, q) / 2)`. -/
theorem c36_d_norm_disc (p q : UpperHalfPlane) :
    ‖c36_d_disc p q‖ = Real.tanh (dist p q / 2) := by
  rw [UpperHalfPlane.tanh_half_dist, c36_d_disc, norm_div, Complex.dist_eq, Complex.dist_eq]
  congr 1
  · rw [← norm_neg]; congr 1; ring
  · rw [← Complex.norm_conj, ← norm_neg]; congr 1; simp [map_sub]

/-- The disc coordinate has norm `< 1`. -/
theorem c36_d_norm_disc_lt_one (p q : UpperHalfPlane) : ‖c36_d_disc p q‖ < 1 := by
  rw [c36_d_norm_disc]; exact Real.tanh_lt_one _

/-- The inverse Cayley map lands in `ℍ` on the unit disc. -/
theorem c36_d_inv_im (p : UpperHalfPlane) {u : ℂ} (hu : ‖u‖ < 1) : 0 < (c36_d_inv p u).im := by
  have h1 := c36_d_one_sub_ne hu
  have hN : 0 < Complex.normSq (1 - u) := Complex.normSq_pos.2 h1
  have hu2 : Complex.normSq u < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg u]
  have key : (c36_d_inv p u).im =
      (p : ℂ).im * (1 - Complex.normSq u) / Complex.normSq (1 - u) := by
    unfold c36_d_inv
    rw [Complex.div_im]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
    field_simp
    ring
  rw [key]
  have := p.coe_im_pos
  have : 0 < 1 - Complex.normSq u := by linarith
  positivity

/-- The inverse Cayley map sends `0` to `p`. -/
theorem c36_d_inv_zero (p : UpperHalfPlane) : c36_d_inv p 0 = p := by
  simp [c36_d_inv]

/-- The inverse Cayley map inverts the disc coordinate. -/
theorem c36_d_inv_disc (p q : UpperHalfPlane) : c36_d_inv p (c36_d_disc p q) = q := by
  have h1 := c36_d_one_sub_ne (c36_d_norm_disc_lt_one p q)
  have h2 := c36_d_sub_conj_ne p q
  unfold c36_d_inv
  rw [div_eq_iff h1]
  unfold c36_d_disc
  field_simp
  ring

/-- `p - p̄ ≠ 0`. -/
theorem c36_d_sub_conj_self_ne (p : UpperHalfPlane) : (p : ℂ) - conj (p : ℂ) ≠ 0 :=
  c36_d_sub_conj_ne p p

/-- The hyperbolic distance in Cayley coordinates centred at `p`:
`tanh (d(z, w) / 2) = |u - v| / |1 - v̄ u|`. -/
theorem c36_d_tanh_half_dist_inv (p : UpperHalfPlane) {u v : ℂ} (hu : ‖u‖ < 1) (hv : ‖v‖ < 1)
    {z w : UpperHalfPlane} (hz : (z : ℂ) = c36_d_inv p u) (hw : (w : ℂ) = c36_d_inv p v) :
    Real.tanh (dist z w / 2) = ‖u - v‖ / ‖1 - conj v * u‖ := by
  rw [UpperHalfPlane.tanh_half_dist, Complex.dist_eq, Complex.dist_eq, hz, hw]
  have h1u := c36_d_one_sub_ne hu
  have h1v := c36_d_one_sub_ne hv
  have hv' : ‖conj v‖ < 1 := by rwa [Complex.norm_conj]
  have h1v' := c36_d_one_sub_ne hv'
  have hvu : ‖conj v * u‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg u, norm_nonneg v]
  have h1vu := c36_d_one_sub_ne hvu
  have hpp := c36_d_sub_conj_self_ne p
  have e1 : c36_d_inv p u - c36_d_inv p v =
      ((p : ℂ) - conj (p : ℂ)) * (u - v) / ((1 - u) * (1 - v)) := by
    unfold c36_d_inv; field_simp; ring
  have e2 : c36_d_inv p u - conj (c36_d_inv p v) =
      ((p : ℂ) - conj (p : ℂ)) * (1 - conj v * u) / ((1 - u) * (1 - conj v)) := by
    unfold c36_d_inv
    simp only [map_div₀, map_sub, map_mul, map_one, Complex.conj_conj]
    field_simp
    ring
  have e3 : ‖1 - conj v‖ = ‖1 - v‖ := by
    rw [← Complex.norm_conj]; simp [map_sub]
  rw [e1, e2, norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, e3]
  have n1 : ‖(p : ℂ) - conj (p : ℂ)‖ ≠ 0 := norm_ne_zero_iff.2 hpp
  have n2 : ‖1 - u‖ ≠ 0 := norm_ne_zero_iff.2 h1u
  have n3 : ‖1 - v‖ ≠ 0 := norm_ne_zero_iff.2 h1v
  have n4 : ‖1 - conj v * u‖ ≠ 0 := norm_ne_zero_iff.2 h1vu
  field_simp

/-! ## The geodesic interpolation -/

/-- The disc point at fraction `t` along the radius towards `(q - p)/(q - p̄)`. -/
def c36_d_B (p q : UpperHalfPlane) (t : ℝ) : ℂ :=
  (c36_d_lam (dist p q / 2) t : ℂ) * c36_d_disc p q

/-- `|B(p, q, t)| = |tanh (t · d(p, q) / 2)|`. -/
theorem c36_d_norm_B (p q : UpperHalfPlane) (t : ℝ) :
    ‖c36_d_B p q t‖ = |Real.tanh (t * (dist p q / 2))| := by
  have hD : 0 ≤ Real.tanh (dist p q / 2) := c36_d_tanh_nonneg (by positivity)
  rw [c36_d_B, norm_mul, Complex.norm_real, c36_d_norm_disc, Real.norm_eq_abs,
    ← c36_d_lam_mul_tanh, abs_mul, abs_of_nonneg hD]

/-- `|B(p, q, t)| < 1`. -/
theorem c36_d_norm_B_lt_one (p q : UpperHalfPlane) (t : ℝ) : ‖c36_d_B p q t‖ < 1 := by
  rw [c36_d_norm_B]; exact c36_d_abs_tanh_lt_one _

/-- The point of the hyperbolic geodesic segment from `p` to `q` at fraction `t`. -/
def c36_d_geod (p q : UpperHalfPlane) (t : ℝ) : UpperHalfPlane :=
  UpperHalfPlane.mk (c36_d_inv p (c36_d_B p q t)) (c36_d_inv_im p (c36_d_norm_B_lt_one p q t))

/-- The geodesic interpolation is jointly continuous in `(p, q, t)`. -/
theorem c36_d_geod_continuous :
    Continuous (fun x : UpperHalfPlane × UpperHalfPlane × ℝ => c36_d_geod x.1 x.2.1 x.2.2) := by
  have hp : Continuous (fun x : UpperHalfPlane × UpperHalfPlane × ℝ => (x.1 : ℂ)) :=
    UpperHalfPlane.continuous_coe.comp continuous_fst
  have hq : Continuous (fun x : UpperHalfPlane × UpperHalfPlane × ℝ => (x.2.1 : ℂ)) :=
    UpperHalfPlane.continuous_coe.comp (continuous_fst.comp continuous_snd)
  have hdisc : Continuous (fun x : UpperHalfPlane × UpperHalfPlane × ℝ => c36_d_disc x.1 x.2.1) :=
    (hq.sub hp).div (hq.sub (Complex.continuous_conj.comp hp)) (fun x => c36_d_sub_conj_ne _ _)
  have hlam : Continuous (fun x : UpperHalfPlane × UpperHalfPlane × ℝ =>
      c36_d_lam (dist x.1 x.2.1 / 2) x.2.2) :=
    c36_d_lam_continuous.comp
      (((continuous_fst.dist (continuous_fst.comp continuous_snd)).div_const 2).prodMk
        (continuous_snd.comp continuous_snd))
  have hB : Continuous (fun x : UpperHalfPlane × UpperHalfPlane × ℝ => c36_d_B x.1 x.2.1 x.2.2) :=
    (Complex.continuous_ofReal.comp hlam).mul hdisc
  have hinv : Continuous (fun x : UpperHalfPlane × UpperHalfPlane × ℝ =>
      c36_d_inv x.1 (c36_d_B x.1 x.2.1 x.2.2)) :=
    (hp.sub ((Complex.continuous_conj.comp hp).mul hB)).div (continuous_const.sub hB)
      (fun x => c36_d_one_sub_ne (c36_d_norm_B_lt_one _ _ _))
  exact hinv.upperHalfPlaneMk _

/-- `d(p, γ(t)) = t · d(p, q)` for `t ≥ 0`. -/
theorem c36_d_dist_left (p q : UpperHalfPlane) {t : ℝ} (ht0 : 0 ≤ t) :
    dist p (c36_d_geod p q t) = t * dist p q := by
  have hB := c36_d_norm_B_lt_one p q t
  have h := c36_d_tanh_half_dist_inv p (u := 0) (v := c36_d_B p q t) (by simp) hB
    (z := p) (w := c36_d_geod p q t) (by rw [c36_d_inv_zero]) rfl
  have hnn : 0 ≤ t * (dist p q / 2) := mul_nonneg ht0 (by positivity)
  rw [zero_sub, norm_neg, mul_zero, sub_zero, norm_one, div_one, c36_d_norm_B,
    abs_of_nonneg (c36_d_tanh_nonneg hnn)] at h
  have := Real.tanh_injective h
  linarith

/-- `d(γ(t), q) = (1 - t) · d(p, q)` for `t ≤ 1`. -/
theorem c36_d_dist_right (p q : UpperHalfPlane) {t : ℝ} (ht1 : t ≤ 1) :
    dist (c36_d_geod p q t) q = (1 - t) * dist p q := by
  have hB := c36_d_norm_B_lt_one p q t
  have ha := c36_d_norm_disc_lt_one p q
  have h := c36_d_tanh_half_dist_inv p (u := c36_d_B p q t) (v := c36_d_disc p q) hB ha
    (z := c36_d_geod p q t) (w := q) rfl (c36_d_inv_disc p q).symm
  set D := dist p q / 2 with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hTD : 0 ≤ Real.tanh D := c36_d_tanh_nonneg hD0
  have hlam := c36_d_lam_mul_tanh D t
  have e1 : ‖c36_d_B p q t - c36_d_disc p q‖ = |Real.tanh (t * D) - Real.tanh D| := by
    have : c36_d_B p q t - c36_d_disc p q = ((c36_d_lam D t - 1 : ℝ) : ℂ) * c36_d_disc p q := by
      rw [c36_d_B]; push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, c36_d_norm_disc, ← hDdef,
      ← abs_of_nonneg hTD, ← abs_mul, abs_of_nonneg hTD, sub_mul, one_mul, hlam]
  have e2 : ‖1 - conj (c36_d_disc p q) * c36_d_B p q t‖ =
      |1 - Real.tanh (t * D) * Real.tanh D| := by
    have : 1 - conj (c36_d_disc p q) * c36_d_B p q t =
        ((1 - c36_d_lam D t * ‖c36_d_disc p q‖ ^ 2 : ℝ) : ℂ) := by
      rw [c36_d_B, ← hDdef]
      push_cast
      rw [← Complex.conj_mul']
      ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, c36_d_norm_disc, ← hDdef, sq, ← mul_assoc, hlam]
  rw [e1, e2, ← abs_div, ← c36_d_tanh_sub, show t * D - D = -(D - t * D) by ring, Real.tanh_neg,
    abs_neg, abs_of_nonneg (c36_d_tanh_nonneg (by nlinarith))] at h
  have := Real.tanh_injective h
  rw [hDdef] at this
  linarith

/-! ### Moved from S36 (§36.1, `h36t_` block): `SL(2, ℝ)`-equivariance of the Cayley coordinates and the geodesic -/

/-- `(g • τ : ℂ) = (a τ + b) / (c τ + d)` for `g ∈ SL(2, ℝ)`. -/
theorem h36t_coe_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    ((g • τ : UpperHalfPlane) : ℂ) = ((g 0 0 : ℂ) * τ + g 0 1) / ((g 1 0 : ℂ) * τ + g 1 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

/-- The denominator `c τ + d` of `g ∈ SL(2, ℝ)` does not vanish on `ℍ`. -/
theorem h36t_den_ne (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (τ : UpperHalfPlane) :
    (g 1 0 : ℂ) * τ + g 1 1 ≠ 0 :=
  k24_d_den_ne_zero (k24_det_realR g) τ.coe_im_pos.ne'

/-- The unimodular factor `(c p̄ + d) / (c p + d)` relating the disc coordinates at `p` and `g p`. -/
def h36t_omega (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p : UpperHalfPlane) : ℂ :=
  ((g 1 0 : ℂ) * conj (p : ℂ) + g 1 1) / ((g 1 0 : ℂ) * p + g 1 1)

/-- `conj (g • p) = (a p̄ + b) / (c p̄ + d)`. -/
theorem h36t_conj_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p : UpperHalfPlane) :
    conj ((g • p : UpperHalfPlane) : ℂ) =
      ((g 0 0 : ℂ) * conj (p : ℂ) + g 0 1) / ((g 1 0 : ℂ) * conj (p : ℂ) + g 1 1) := by
  rw [h36t_coe_smul]
  simp [map_div₀, Complex.conj_ofReal]

/-- The difference of two values of a unimodular Möbius map:
`(a z + b)/(c z + d) - (a w + b)/(c w + d) = (z - w) / ((c z + d)(c w + d))`. -/
theorem h36t_mob_sub {a b c d z w : ℂ} (hdet : a * d - b * c = 1) (hz : c * z + d ≠ 0)
    (hw : c * w + d ≠ 0) :
    (a * z + b) / (c * z + d) - (a * w + b) / (c * w + d) = (z - w) / ((c * z + d) * (c * w + d)) := by
  rw [div_sub_div _ _ hz hw]
  congr 1
  linear_combination (z - w) * hdet

/-- Disc coordinates are equivariant: `disc_{g p}(g q) = ω(g, p) · disc_p(q)`. -/
theorem h36t_disc_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p q : UpperHalfPlane) :
    c36_d_disc (g • p) (g • q) = h36t_omega g p * c36_d_disc p q := by
  have hdet : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by exact_mod_cast k24_det_realR g
  have hp := h36t_den_ne g p
  have hq := h36t_den_ne g q
  have hpc : (g 1 0 : ℂ) * conj (p : ℂ) + g 1 1 ≠ 0 :=
    k24_d_den_ne_zero (k24_det_realR g) (by rw [Complex.conj_im]; exact neg_ne_zero.2 p.coe_im_pos.ne')
  have h1 := c36_d_sub_conj_ne p q
  have hq' : (q : ℂ) * g 1 0 + g 1 1 ≠ 0 := by rwa [mul_comm]
  have hp' : (p : ℂ) * g 1 0 + g 1 1 ≠ 0 := by rwa [mul_comm]
  unfold c36_d_disc h36t_omega
  rw [h36t_conj_smul, h36t_coe_smul g p, h36t_coe_smul g q, h36t_mob_sub hdet hq hp,
    h36t_mob_sub hdet hq hpc]
  field_simp

/-- The inverse Cayley maps are equivariant: `g · inv_p(v) = inv_{g p}(ω(g, p) v)`. -/
theorem h36t_inv_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p : UpperHalfPlane) {v : ℂ} (hv : ‖v‖ < 1) :
    c36_d_inv (g • p) (h36t_omega g p * v) =
      ((g • UpperHalfPlane.mk (c36_d_inv p v) (c36_d_inv_im p hv) : UpperHalfPlane) : ℂ) := by
  have hdet : (g 0 0 : ℂ) * g 1 1 - g 0 1 * g 1 0 = 1 := by exact_mod_cast k24_det_realR g
  have hP := h36t_den_ne g p
  have hPc : (g 1 0 : ℂ) * conj (p : ℂ) + g 1 1 ≠ 0 :=
    k24_d_den_ne_zero (k24_det_realR g) (by rw [Complex.conj_im]; exact neg_ne_zero.2 p.coe_im_pos.ne')
  have hP' : (p : ℂ) * g 1 0 + g 1 1 ≠ 0 := by rwa [mul_comm]
  have hPc' : conj (p : ℂ) * g 1 0 + g 1 1 ≠ 0 := by rwa [mul_comm]
  have h1v := c36_d_one_sub_ne hv
  have hden := h36t_den_ne g (UpperHalfPlane.mk (c36_d_inv p v) (c36_d_inv_im p hv))
  rw [UpperHalfPlane.coe_mk] at hden
  have hK : (g 1 0 : ℂ) * p + g 1 1 - ((g 1 0 : ℂ) * conj (p : ℂ) + g 1 1) * v =
      (1 - v) * ((g 1 0 : ℂ) * c36_d_inv p v + g 1 1) := by
    unfold c36_d_inv
    field_simp
    ring
  have hK0 : (g 1 0 : ℂ) * p + g 1 1 - ((g 1 0 : ℂ) * conj (p : ℂ) + g 1 1) * v ≠ 0 := by
    rw [hK]; exact mul_ne_zero h1v hden
  have h1ω : 1 - h36t_omega g p * v ≠ 0 := by
    have e : 1 - h36t_omega g p * v =
        ((g 1 0 : ℂ) * p + g 1 1 - ((g 1 0 : ℂ) * conj (p : ℂ) + g 1 1) * v) / ((g 1 0 : ℂ) * p + g 1 1) := by
      unfold h36t_omega
      field_simp
    rw [e]; exact div_ne_zero hK0 hP
  rw [h36t_coe_smul, UpperHalfPlane.coe_mk]
  rw [show c36_d_inv (g • p) (h36t_omega g p * v) = (((g • p : UpperHalfPlane) : ℂ) -
    conj ((g • p : UpperHalfPlane) : ℂ) * (h36t_omega g p * v)) / (1 - h36t_omega g p * v) from rfl,
    div_eq_div_iff h1ω hden]
  unfold c36_d_inv h36t_omega
  rw [h36t_conj_smul, h36t_coe_smul]
  field_simp
  ring

/-- The geodesic interpolation is `SL(2, ℝ)`-equivariant: `γ_{g a, g b}(t) = g · γ_{a, b}(t)`. -/
theorem h36t_geod_smul (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a b : UpperHalfPlane) (t : ℝ) :
    c36_d_geod (g • a) (g • b) t = g • c36_d_geod a b t := by
  apply UpperHalfPlane.ext
  show c36_d_inv (g • a) (c36_d_B (g • a) (g • b) t) = ((g • c36_d_geod a b t : UpperHalfPlane) : ℂ)
  have hB : c36_d_B (g • a) (g • b) t = h36t_omega g a * c36_d_B a b t := by
    rw [c36_d_B, c36_d_B, dist_smul, h36t_disc_smul]
    ring
  rw [hB, h36t_inv_smul g a (c36_d_norm_B_lt_one a b t)]
  rfl

/-- The geodesic interpolation starts at `a`. -/
theorem h36t_geod_zero (a b : UpperHalfPlane) : c36_d_geod a b 0 = a := by
  refine (dist_eq_zero.1 ?_).symm
  rw [c36_d_dist_left a b le_rfl, zero_mul]

/-- The geodesic interpolation ends at `b`. -/
theorem h36t_geod_one (a b : UpperHalfPlane) : c36_d_geod a b 1 = b := by
  refine dist_eq_zero.1 ?_
  rw [c36_d_dist_right a b le_rfl, sub_self, zero_mul]

/-! ### s36h Stage 2 batch D (coordinator 553e2d): Theorem 23.1 (`h23l_`) -/

/-- Two continuous lifts through `p₁` of the same map differ by an element of `Γ₁` (the fibre clause of
`IsUniformization` at one point, then `IsCoveringMap.eq_of_comp_eq` on the connected `ℍ`). -/
theorem h23l_lifts_differ {Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → S₁}
    (hp₁ : IsUniformization Γ₁ p₁) {F₁ F₂ : UpperHalfPlane → UpperHalfPlane} (h₁ : Continuous F₁)
    (h₂ : Continuous F₂) (h : ∀ τ, p₁ (F₁ τ) = p₁ (F₂ τ)) : ∃ δ ∈ Γ₁, ∀ τ, F₁ τ = δ • F₂ τ := by
  obtain ⟨δ, hδ, hδe⟩ := (hp₁.2.2.2 (F₂ UpperHalfPlane.I) (F₁ UpperHalfPlane.I)).1 (h _).symm
  have hcomp : p₁ ∘ F₁ = p₁ ∘ (fun τ => δ • F₂ τ) := by
    funext τ
    simp only [Function.comp_apply]
    rw [h τ]
    exact (hp₁.2.2.2 _ _).2 ⟨δ, hδ, rfl⟩
  refine ⟨δ, hδ, fun τ => ?_⟩
  exact congrFun (hp₁.1.eq_of_comp_eq h₁ ((continuous_const_smul δ).comp h₂) hcomp UpperHalfPlane.I hδe.symm) τ

/-- **D1** [P1, stub] The deck element along a lifted homotopy does not depend on `t`: if `H̃ : [0, 1] × ℍ → ℍ` is
continuous and `p₁ (H̃ (t, τ)) = H (t, p₀ τ)`, then for `γ ∈ Γ₀` there is `δ ∈ Γ₁` with `H̃ (t, γ τ) = δ H̃ (t, τ)` for
all `t, τ` (both sides lift the same map through `p₁` on the connected `[0, 1] × ℍ` and agree at `(0, i)`:
`IsCoveringMap.eq_of_comp_eq`; `H` need not be continuous). -/
theorem h23l_homotopy_deck {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    {p₁ : UpperHalfPlane → S₁} (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁)
    {H : unitInterval × S₀ → S₁} {Ht : C(unitInterval × UpperHalfPlane, UpperHalfPlane)}
    (hHt : ∀ t τ, p₁ (Ht (t, τ)) = H (t, p₀ τ)) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ₀) :
    ∃ δ ∈ Γ₁, ∀ t τ, Ht (t, γ • τ) = δ • Ht (t, τ) := by
  have hpγ : ∀ τ, p₀ (γ • τ) = p₀ τ := fun τ => ((hp₀.2.2.2 τ (γ • τ)).2 ⟨γ, hγ, rfl⟩).symm
  have h0 : p₁ (Ht (0, UpperHalfPlane.I)) = p₁ (Ht (0, γ • UpperHalfPlane.I)) := by rw [hHt, hHt, hpγ]
  obtain ⟨δ, hδ, hδe⟩ := (hp₁.2.2.2 _ _).1 h0
  refine ⟨δ, hδ, fun t τ => ?_⟩
  have hcomp : p₁ ∘ (fun x : unitInterval × UpperHalfPlane => Ht (x.1, γ • x.2)) =
      p₁ ∘ (fun x : unitInterval × UpperHalfPlane => δ • Ht x) := by
    funext x
    simp only [Function.comp_apply]
    rw [hHt, hpγ, ← hHt]
    exact (hp₁.2.2.2 _ _).2 ⟨δ, hδ, rfl⟩
  have h := hp₁.1.eq_of_comp_eq
    (Ht.continuous.comp (continuous_fst.prodMk ((continuous_const_smul γ).comp continuous_snd)))
    ((continuous_const_smul δ).comp Ht.continuous) hcomp (0, UpperHalfPlane.I) hδe.symm
  exact congrFun h (t, τ)

/-- **D2** [P1, stub] Descent of an equivariant homotopy: a continuous `H̃ : ℍ × [0, 1] → ℍ` with
`H̃ (γ τ, t) = δ_γ H̃ (τ, t)` (some `δ_γ ∈ Γ₁` for each `γ ∈ Γ₀`) induces a continuous `H : [0, 1] × S₀ → S₁` with
`H (t, p₀ τ) = p₁ (H̃ (τ, t))`: well defined by the fibre clauses of `p₀` and `p₁`, continuous because `id × p₀` is an
open surjection, hence a quotient map (as in `h36_thm36_1_mpr`). -/
theorem h23l_homotopy_descend {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    {p₁ : UpperHalfPlane → S₁} (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁)
    {Ht : UpperHalfPlane → unitInterval → UpperHalfPlane}
    (hHt : Continuous (fun x : UpperHalfPlane × unitInterval => Ht x.1 x.2))
    (heq : ∀ γ ∈ Γ₀, ∃ δ ∈ Γ₁, ∀ τ t, Ht (γ • τ) t = δ • Ht τ t) :
    ∃ H : C(unitInterval × S₀, S₁), ∀ t τ, H (t, p₀ τ) = p₁ (Ht τ t) := by
  have hsurj : Function.Surjective p₀ := hp₀.2.2.1
  have hsec : ∀ x, p₀ (Function.surjInv hsurj x) = x := Function.surjInv_eq hsurj
  -- well defined: `p₁ ∘ H̃` is constant on the fibres of `p₀`
  have hwd : ∀ (τ : UpperHalfPlane) (t : unitInterval),
      p₁ (Ht (Function.surjInv hsurj (p₀ τ)) t) = p₁ (Ht τ t) := by
    intro τ t
    obtain ⟨γ, hγ, hγτ⟩ := (hp₀.2.2.2 τ (Function.surjInv hsurj (p₀ τ))).1 (hsec (p₀ τ)).symm
    obtain ⟨δ, hδ, hδe⟩ := heq γ hγ
    rw [← hγτ, hδe]
    exact ((hp₁.2.2.2 _ _).2 ⟨δ, hδ, rfl⟩).symm
  -- continuous: `id × p₀` is an open continuous surjection, hence a quotient map
  have hq : Topology.IsQuotientMap (Prod.map (id : unitInterval → unitInterval) p₀) :=
    (IsOpenMap.id.prodMap hp₀.1.isOpenMap).isQuotientMap (continuous_id.prodMap hp₀.1.continuous)
      (Function.surjective_id.prodMap hsurj)
  have hc : Continuous (fun x : unitInterval × S₀ => p₁ (Ht (Function.surjInv hsurj x.2) x.1)) := by
    refine hq.continuous_iff.2 ?_
    have e : (fun x : unitInterval × S₀ => p₁ (Ht (Function.surjInv hsurj x.2) x.1)) ∘ Prod.map id p₀ =
        fun x : unitInterval × UpperHalfPlane => p₁ (Ht x.2 x.1) := by
      funext x
      exact hwd x.2 x.1
    rw [e]
    exact hp₁.1.continuous.comp (hHt.comp continuous_swap)
  exact ⟨⟨_, hc⟩, fun t τ => hwd τ t⟩

/-- **Theorem 23.1**: let `f, g : S₀ → S₁` be homeomorphisms with lifts `F, G` to `ℍ`.  Then `f` and
`g` are homotopic iff there is `γ₁ ∈ Γ₁` with `χ_F = γ₁ χ_G γ₁⁻¹`, where
`χ_F(γ) = F ∘ γ ∘ F⁻¹` is the isomorphism `Γ₀ → Γ₁` induced by `F`. -/
theorem thm23_1_homotopy_iff [T2Space S₀] [ConnectedSpace S₀] [T2Space S₁] [ConnectedSpace S₁]
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    {p₁ : UpperHalfPlane → S₁} (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁)
    (f g : S₀ ≃ₜ S₁) {F G : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₀ p₁ f F)
    (hG : IsLift p₀ p₁ g G) :
    ContinuousMap.Homotopic (f : C(S₀, S₁)) (g : C(S₀, S₁)) ↔
      ∃ γ₁ ∈ Γ₁, ∀ γ ∈ Γ₀, ∀ τ : UpperHalfPlane,
        F (γ • F.symm τ) = γ₁ • G (γ • G.symm (γ₁⁻¹ • τ)) := by
  constructor
  · -- `⇒`: lift the homotopy `H ∘ (id × p₀)` from `F` (Mathlib's homotopy lifting); its end is `γ₁ ∘ G`
    rintro ⟨H⟩
    set H' : C(unitInterval × UpperHalfPlane, S₁) :=
      H.toContinuousMap.comp ((ContinuousMap.id unitInterval).prodMap ⟨p₀, hp₀.1.continuous⟩) with hH'
    have hH0 : ∀ τ, H' (0, τ) = p₁ (F τ) := fun τ => by
      show H (0, p₀ τ) = _
      rw [H.apply_zero]
      exact (hF τ).symm
    set Ht := hp₁.1.liftHomotopy H' ⟨F, F.continuous⟩ hH0 with hHt
    have hlift : ∀ t τ, p₁ (Ht (t, τ)) = H (t, p₀ τ) :=
      fun t τ => congrFun (hp₁.1.liftHomotopy_lifts H' ⟨F, F.continuous⟩ hH0) (t, τ)
    have hzero : ∀ τ, Ht (0, τ) = F τ := hp₁.1.liftHomotopy_zero H' ⟨F, F.continuous⟩ hH0
    obtain ⟨γ₁, hγ₁, hend'⟩ := h23l_lifts_differ hp₁ (F₁ := fun τ => Ht (1, τ))
      (Ht.continuous.comp (continuous_const.prodMk continuous_id)) G.continuous (fun τ => by
        show p₁ (Ht (1, τ)) = p₁ (G τ)
        rw [hlift, H.apply_one, hG]
        rfl)
    have hend : ∀ τ, Ht (1, τ) = γ₁ • G τ := hend'
    refine ⟨γ₁, hγ₁, fun γ hγ τ => ?_⟩
    obtain ⟨δ, -, hδ⟩ := h23l_homotopy_deck hp₀ hp₁ hlift hγ
    have h0 := hδ 0 (F.symm τ)
    rw [hzero, hzero, F.apply_symm_apply] at h0
    have h1 := hδ 1 (G.symm (γ₁⁻¹ • τ))
    rw [hend, hend, G.apply_symm_apply, smul_inv_smul] at h1
    rw [h0, h1]
  · -- `⇐`: the geodesic homotopy from `F` to `γ₁ ∘ G` is `Γ₀`-equivariant, hence descends
    rintro ⟨γ₁, hγ₁, hrel⟩
    have heq : ∀ γ ∈ Γ₀, ∃ δ ∈ Γ₁, ∀ τ (t : unitInterval),
        c36_d_geod (F (γ • τ)) (γ₁ • G (γ • τ)) t = δ • c36_d_geod (F τ) (γ₁ • G τ) t := by
      intro γ hγ
      obtain ⟨δ, hδ, hFδ⟩ := h23l_deck hp₀ hp₁ hF hγ
      refine ⟨δ, hδ, fun τ t => ?_⟩
      have hG' : γ₁ • G (γ • τ) = δ • (γ₁ • G τ) := by
        have h := hrel γ hγ (γ₁ • G τ)
        rw [inv_smul_smul, G.symm_apply_apply, hFδ, F.apply_symm_apply] at h
        exact h.symm
      rw [hFδ, hG', h36t_geod_smul]
    have hc : Continuous (fun x : UpperHalfPlane × unitInterval => c36_d_geod (F x.1) (γ₁ • G x.1) x.2) :=
      c36_d_geod_continuous.comp ((F.continuous.comp continuous_fst).prodMk
        (((continuous_const_smul γ₁).comp (G.continuous.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp continuous_snd)))
    obtain ⟨H, hH⟩ := h23l_homotopy_descend (Ht := fun τ (t : unitInterval) => c36_d_geod (F τ) (γ₁ • G τ) t)
      hp₀ hp₁ hc heq
    refine ⟨⟨H, fun x => ?_, fun x => ?_⟩⟩
    · obtain ⟨τ, rfl⟩ := hp₀.2.2.1 x
      show H (0, p₀ τ) = f (p₀ τ)
      rw [hH, Set.Icc.coe_zero, h36t_geod_zero, hF]
    · obtain ⟨τ, rfl⟩ := hp₀.2.2.1 x
      show H (1, p₀ τ) = g (p₀ τ)
      rw [hH, Set.Icc.coe_one, h36t_geod_one, ← hG]
      exact ((hp₁.2.2.2 (G τ) (γ₁ • G τ)).2 ⟨γ₁, hγ₁, rfl⟩).symm

/-- **Theorem 23.1, Corollary**: on a closed Riemann surface of genus `g > 1` (more generally when
the covering group is non-elementary), a conformal automorphism homotopic to the identity is the
identity. -/
theorem thm23_1_cor [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ} (hg : 1 < g)
    (hS : HasGenus S₀ g) (φ : S₀ ≃ₜ S₀) (hφ : IsBiholomorphic φ)
    (hhom : ContinuousMap.Homotopic (φ : C(S₀, S₀)) (ContinuousMap.id S₀)) : ⇑φ = id := by
  sorry

/-! ### Helpers moved up from `Lemmas/UniformizedTeichmuller` and S35 (s27t stage T, leader decision): the lift of a
biholomorphic map is Möbius, bounded displacement, the Cayley rotation lemmas -/

/-- The inverse Cayley transform `w ↦ i(1 + w)/(1 - w)` maps the unit disc conformally onto the upper half-plane. -/
theorem s35a_x_isConformalOnto_cayleyInv : IsConformalOnto cayleyInv unitDisc upperHalf := by
  refine ⟨?_, fun w₁ h₁ w₂ h₂ heq => ?_, ?_⟩
  · intro w hw
    have hden := cayleyInv_den_ne_zero (mem_ball_zero_iff.mp hw)
    refine DifferentiableAt.differentiableWithinAt ?_
    have hfun : cayleyInv = fun v : ℂ => I * (1 + v) / (1 - v) := rfl
    rw [hfun]
    exact (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => I * (1 + v)) w).div
      (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => 1 - v) w) hden
  · calc w₁ = cayley (cayleyInv w₁) := (cayley_cayleyInv (mem_ball_zero_iff.mp h₁)).symm
      _ = cayley (cayleyInv w₂) := by rw [heq]
      _ = w₂ := cayley_cayleyInv (mem_ball_zero_iff.mp h₂)
  · ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hw)
    · intro hz
      exact ⟨cayley z, cayley_mem_unitDisc hz, cayleyInv_cayley hz⟩

section UTMMoved

open scoped UpperHalfPlane

open UpperHalfPlane

/-- `Im((a z + b)/(c z + d)) = Im z / |c z + d|²` for real `a, b, c, d` with `a d - b c = 1`. -/
theorem utm_im_mobius {a b c d : ℝ} (hdet : a * d - b * c = 1) (z : ℂ) :
    (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).im = z.im / Complex.normSq ((c : ℂ) * z + d) := by
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Complex.ofReal_re, Complex.ofReal_im, add_zero]
  rw [div_sub_div_same]
  congr 1
  linear_combination z.im * hdet

/-- **A non-`±1` element of `SL(2, ℝ)` has unbounded displacement on `ℍ`.**  (From `cosh_dist'`:
`(Re w - Re z)² + (Im z)² + (Im w)² ≤ 2 cosh C · Im z · Im w` for `w = m z`; `c ≠ 0` fails for `z = iy`, `y` large;
`c = 0`, `a² ≠ 1` fails for `Im z = 1`, `Re z` large; `c = 0`, `a² = 1`, `b ≠ 0` fails for `Im z` small.) -/
theorem utm_sl2_eq_of_bounded_displacement (m : Matrix.SpecialLinearGroup (Fin 2) ℝ) {C : ℝ}
    (hC : ∀ z : ℍ, dist (m • z) z ≤ C) : m = 1 ∨ m = -1 := by
  have e1 : (m : Matrix (Fin 2) (Fin 2) ℝ) = !![m 0 0, m 0 1; m 1 0, m 1 1] := Matrix.eta_fin_two _
  obtain ⟨a, ha⟩ : ∃ a, m 0 0 = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, m 0 1 = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, m 1 0 = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, m 1 1 = d := ⟨_, rfl⟩
  rw [ha, hb, hc, hd] at e1
  have hdet : a * d - b * c = 1 := by
    have h := m.det_coe
    rw [e1, Matrix.det_fin_two_of] at h
    exact h
  set B := Real.cosh C with hB
  have hB1 : 1 ≤ B := Real.one_le_cosh C
  -- the key inequality at every point
  have key : ∀ z : ℍ, ((m • z).re - z.re) ^ 2 + (m • z).im ^ 2 + z.im ^ 2 ≤ 2 * B * (m • z).im * z.im := by
    intro z
    have h1 : Real.cosh (dist (m • z) z) ≤ B := by
      rw [hB, Real.cosh_le_cosh, abs_of_nonneg dist_nonneg]
      exact (hC z).trans (le_abs_self C)
    rw [cosh_dist'] at h1
    have hpos : 0 < 2 * (m • z).im * z.im := by have := (m • z).im_pos; have := z.im_pos; positivity
    rw [div_le_iff₀ hpos] at h1
    linarith
  -- the action in coordinates
  have hcoe : ∀ z : ℍ, ((m • z : ℍ) : ℂ) = ((a : ℂ) * z + b) / ((c : ℂ) * z + d) := fun z => by
    rw [h36t_coe_smul, ha, hb, hc, hd]
  have him : ∀ z : ℍ, (m • z).im = z.im / Complex.normSq ((c : ℂ) * z + d) := fun z => by
    rw [show (m • z).im = ((m • z : ℍ) : ℂ).im from rfl, hcoe z, utm_im_mobius hdet]
    rfl
  by_cases hc0 : c = 0
  · -- `c = 0`: `m z = a² z + a b`
    have had : a * d = 1 := by rw [hc0, mul_zero, sub_zero] at hdet; exact hdet
    have hd0 : d ≠ 0 := right_ne_zero_of_mul_eq_one had
    have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one had
    have hda : d⁻¹ = a := by
      field_simp
      linarith
    have hw : ∀ z : ℍ, ((m • z : ℍ) : ℂ) = ((a ^ 2 : ℝ) : ℂ) * z + ((a * b : ℝ) : ℂ) := by
      intro z
      rw [hcoe z, hc0]
      push_cast
      rw [zero_mul, zero_add, div_eq_mul_inv, ← Complex.ofReal_inv, hda]
      ring
    have hre : ∀ z : ℍ, (m • z).re = a ^ 2 * z.re + a * b := by
      intro z
      have h := congrArg Complex.re (hw z)
      rw [Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re] at h
      exact h
    have him' : ∀ z : ℍ, (m • z).im = a ^ 2 * z.im := by
      intro z
      have h := congrArg Complex.im (hw z)
      rw [Complex.add_im, Complex.im_ofReal_mul, Complex.ofReal_im, add_zero] at h
      exact h
    -- `((a² - 1) x + a b)² ≤ 2 B a² y²`
    have hineq : ∀ z : ℍ, ((a ^ 2 - 1) * z.re + a * b) ^ 2 ≤ 2 * B * a ^ 2 * z.im ^ 2 := by
      intro z
      have h := key z
      rw [hre z, him' z] at h
      nlinarith [sq_nonneg (a ^ 2 * z.im), sq_nonneg z.im]
    have ha2 : a ^ 2 = 1 := by
      by_contra hne
      have hne' : a ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hne
      set N : ℝ := 2 * B * a ^ 2 + 1 with hN
      set x : ℝ := (N - a * b) / (a ^ 2 - 1) with hx
      have h := hineq (UpperHalfPlane.mk ((x : ℂ) + Complex.I) (by simp))
      have hre' : (UpperHalfPlane.mk ((x : ℂ) + Complex.I) (by simp)).re = x := by
        show ((x : ℂ) + Complex.I).re = x
        simp
      have him'' : (UpperHalfPlane.mk ((x : ℂ) + Complex.I) (by simp)).im = 1 := by
        show ((x : ℂ) + Complex.I).im = 1
        simp
      rw [hre', him''] at h
      have hxe : (a ^ 2 - 1) * x + a * b = N := by
        rw [hx]
        field_simp
        ring
      rw [hxe] at h
      have hN1 : 1 ≤ N := by
        have : 0 ≤ 2 * B * a ^ 2 := by positivity
        linarith
      nlinarith
    have hab : a * b = 0 := by
      by_contra hne
      set y : ℝ := |a * b| / (2 * B + 1) with hy
      have hy0 : 0 < y := div_pos (abs_pos.2 hne) (by linarith)
      have h := hineq (UpperHalfPlane.mk ((y : ℂ) * Complex.I) (by simpa using hy0))
      have hre' : (UpperHalfPlane.mk ((y : ℂ) * Complex.I) (by simpa using hy0)).re = 0 := by
        show ((y : ℂ) * Complex.I).re = 0
        simp
      have him'' : (UpperHalfPlane.mk ((y : ℂ) * Complex.I) (by simpa using hy0)).im = y := by
        show ((y : ℂ) * Complex.I).im = y
        simp
      rw [hre', him'', ha2] at h
      simp only [mul_zero, zero_add, mul_one] at h
      -- `(ab)² ≤ 2 B y² = 2 B (ab)²/(2B+1)² < (ab)²`
      have habs : 0 < |a * b| := abs_pos.2 hne
      have h2B : 0 < 2 * B + 1 := by linarith
      have hyy : y * (2 * B + 1) = |a * b| := by rw [hy]; field_simp
      have hsq : (a * b) ^ 2 = |a * b| ^ 2 := (sq_abs _).symm
      rw [hsq, ← hyy] at h
      have : 0 < y ^ 2 := by positivity
      nlinarith
    have hb0 : b = 0 := by
      rcases mul_eq_zero.1 hab with h | h
      · exact absurd h ha0
      · exact h
    have hda' : d = a := by
      have h1 : a * a = 1 := by nlinarith
      have h2 : a * d = a * a := by rw [had, h1]
      exact mul_left_cancel₀ ha0 h2
    rcases mul_eq_zero.1 (show (a - 1) * (a + 1) = 0 by nlinarith) with h1 | h1
    · left
      have ha1 : a = 1 := by linarith
      apply Subtype.ext
      rw [e1, Matrix.SpecialLinearGroup.coe_one, hb0, hc0, hda', ha1]
      exact Matrix.one_fin_two.symm
    · right
      have ha1 : a = -1 := by linarith
      apply Subtype.ext
      rw [e1, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, hb0, hc0, hda', ha1,
        Matrix.one_fin_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  · -- `c ≠ 0`: at `z = i y`, `Im(m z) = y/(d² + c² y²)` while `y ≤ 2 B Im(m z)`
    exfalso
    set y : ℝ := (2 * B + 1) / |c| with hy
    have hy0 : 0 < y := div_pos (by linarith) (abs_pos.2 hc0)
    set z : ℍ := UpperHalfPlane.mk ((y : ℂ) * Complex.I) (by simpa using hy0) with hz
    have hzim : z.im = y := by
      show ((y : ℂ) * Complex.I).im = y
      simp
    have hD : Complex.normSq ((c : ℂ) * z + d) = d ^ 2 + c ^ 2 * y ^ 2 := by
      show Complex.normSq ((c : ℂ) * ((y : ℂ) * Complex.I) + d) = _
      rw [Complex.normSq_apply]
      simp
      ring
    have h := key z
    rw [him z, hD, hzim] at h
    have hDpos : 0 < d ^ 2 + c ^ 2 * y ^ 2 := by
      have : 0 < c ^ 2 := lt_of_le_of_ne (sq_nonneg c) (Ne.symm (pow_ne_zero 2 hc0))
      positivity
    have h1 : y * y ≤ 2 * B * (y / (d ^ 2 + c ^ 2 * y ^ 2)) * y := by
      nlinarith [sq_nonneg ((m • z).re - z.re), sq_nonneg (y / (d ^ 2 + c ^ 2 * y ^ 2))]
    have h2 : y ≤ 2 * B * (y / (d ^ 2 + c ^ 2 * y ^ 2)) := le_of_mul_le_mul_right h1 hy0
    have h3 : d ^ 2 + c ^ 2 * y ^ 2 ≤ 2 * B := by
      rw [mul_div_assoc', le_div_iff₀ hDpos] at h2
      nlinarith
    have hcy : c ^ 2 * y ^ 2 = (2 * B + 1) ^ 2 := by
      rw [hy, div_pow, sq_abs]
      have : c ^ 2 ≠ 0 := pow_ne_zero 2 hc0
      field_simp
    nlinarith [sq_nonneg d]

/-- **Compact quotient.**  If `p : ℍ → S` uniformizes a compact `S`, some compact `K ⊆ ℍ` meets every
`Γ`-orbit. -/
theorem utm_exists_compact_translate {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S} (hp : IsUniformization Γ p) :
    ∃ K : Set ℍ, IsCompact K ∧ ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ K := by
  obtain ⟨hcov, -, hsurj, hfib⟩ := hp
  have hopen : IsOpenMap p := hcov.isLocalHomeomorph.isOpenMap
  choose N hNc hNn using fun τ : ℍ => exists_compact_mem_nhds τ
  have hcover : (univ : Set S) ⊆ ⋃ τ : ℍ, p '' interior (N τ) := by
    intro s _
    obtain ⟨τ, rfl⟩ := hsurj s
    exact mem_iUnion.2 ⟨τ, τ, mem_interior_iff_mem_nhds.2 (hNn τ), rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun τ => p '' interior (N τ))
    (fun τ => hopen _ isOpen_interior) hcover
  refine ⟨⋃ τ ∈ t, N τ, t.isCompact_biUnion fun τ _ => hNc τ, fun z => ?_⟩
  obtain ⟨τ, hτ, k, hk, hkz⟩ : ∃ τ ∈ t, ∃ k ∈ interior (N τ), p k = p z := by
    have := ht (mem_univ (p z))
    simp only [mem_iUnion] at this
    obtain ⟨τ, hτ, k, hk, hkz⟩ := this
    exact ⟨τ, hτ, k, hk, hkz⟩
  obtain ⟨γ, hγ, hγz⟩ := (hfib z k).1 hkz.symm
  exact ⟨γ, hγ, mem_biUnion hτ (interior_subset (hγz ▸ hk))⟩

/-- **The commutant of a cocompact group.**  An element of `SL(2, ℝ)` commuting (on `ℍ`) with every element
of `Γ`, where `ℍ/Γ` is compact, is `±1`: its displacement is `Γ`-invariant, hence bounded. -/
theorem utm_commute_eq_one {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] [CompactSpace S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S} (hp : IsUniformization Γ p)
    (M : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hM : ∀ γ ∈ Γ, ∀ z : ℍ, M • γ • z = γ • M • z) :
    M = 1 ∨ M = -1 := by
  obtain ⟨K, hK, hKz⟩ := utm_exists_compact_translate hp
  have hcont : Continuous fun z : ℍ => dist (M • z) z := (continuous_const_smul M).dist continuous_id
  obtain ⟨C, hC⟩ := (hK.image hcont).isBounded.bddAbove
  refine utm_sl2_eq_of_bounded_displacement M (C := C) fun z => ?_
  obtain ⟨γ, hγ, hγz⟩ := hKz z
  have hinv : dist (M • γ • z) (γ • z) = dist (M • z) z := by
    rw [hM γ hγ z, dist_smul]
  rw [← hinv]
  exact hC ⟨γ • z, hγz, rfl⟩

/-- `p² + q² = 1` for `p = Re u`, `q = Im u`, `|u| = 1`. -/
theorem utm_re_sq_add_im_sq {u : ℂ} (hu : ‖u‖ = 1) : u.re ^ 2 + u.im ^ 2 = 1 := by
  have h : u.re * u.re + u.im * u.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hu, one_pow]
  nlinarith [h]

/-- The rotation `!![p, q; -q, p]` (`p² + q² = 1`) of `ℍ` about `i`. -/
def utm_rot (u : ℂ) (hu : ‖u‖ = 1) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![u.re, u.im; -u.im, u.re], by
    rw [Matrix.det_fin_two_of]
    have h := utm_re_sq_add_im_sq hu
    nlinarith [h]⟩

/-- The algebra behind `utm_cayley_rot`. -/
theorem utm_cayley_rot_alg {p q : ℝ} (hpq : p ^ 2 + q ^ 2 = 1) {τ : ℂ}
    (hden : -(q : ℂ) * τ + p ≠ 0) :
    cayley (((p : ℂ) * τ + q) / (-(q : ℂ) * τ + p)) = ((p : ℂ) + q * Complex.I) ^ 2 * cayley τ := by
  have hpq' : (p : ℂ) ^ 2 + (q : ℂ) ^ 2 = 1 := by exact_mod_cast hpq
  set N : ℂ := (p : ℂ) * τ + q
  set Dn : ℂ := -(q : ℂ) * τ + p
  have e1 : N - Complex.I * Dn = ((p : ℂ) + q * Complex.I) * (τ - Complex.I) := by
    simp only [N, Dn]
    linear_combination (q : ℂ) * Complex.I_sq
  have e2 : N + Complex.I * Dn = ((p : ℂ) - q * Complex.I) * (τ + Complex.I) := by
    simp only [N, Dn]
    linear_combination (q : ℂ) * Complex.I_sq
  have e3 : ((p : ℂ) + q * Complex.I) * ((p : ℂ) - q * Complex.I) = 1 := by
    linear_combination hpq' - (q : ℂ) ^ 2 * Complex.I_sq
  have hm : (p : ℂ) - q * Complex.I ≠ 0 := right_ne_zero_of_mul_eq_one e3
  have hc : cayley (N / Dn) = (N - Complex.I * Dn) / (N + Complex.I * Dn) := by
    unfold cayley
    rw [div_sub' hden, div_add' _ _ _ hden, div_div_div_cancel_right₀ hden]
    ring_nf
  rw [hc, e1, e2, mul_div_mul_comm]
  have e4 : ((p : ℂ) + q * Complex.I) / ((p : ℂ) - q * Complex.I) = ((p : ℂ) + q * Complex.I) ^ 2 := by
    rw [div_eq_iff hm]
    linear_combination (-((p : ℂ) + q * Complex.I)) * e3
  rw [e4]
  rfl

/-- The Cayley conjugate of the rotation `utm_rot u` is `w ↦ u² w`. -/
theorem utm_cayley_rot (u : ℂ) (hu : ‖u‖ = 1) (τ : ℍ) :
    cayley ((utm_rot u hu • τ : ℍ) : ℂ) = u ^ 2 * cayley τ := by
  have hcoe : ((utm_rot u hu • τ : ℍ) : ℂ) = ((u.re : ℂ) * τ + u.im) / (-(u.im : ℂ) * τ + u.re) := by
    rw [h36t_coe_smul]
    simp [utm_rot]
  have hden : -(u.im : ℂ) * τ + u.re ≠ 0 := by
    have := h36t_den_ne (utm_rot u hu) τ
    simpa [utm_rot] using this
  rw [hcoe, utm_cayley_rot_alg (utm_re_sq_add_im_sq hu) hden,
    Complex.re_add_im]

/-- **The lift of a conformal automorphism is Möbius.**  A self-homeomorphism `F` of `ℍ` whose lift
`liftToC F` is `1`-quasiconformal on `ℍ` is the action of some `m ∈ SL(2, ℝ)`. -/
theorem utm_eq_smul_of_isKQC_one (F : ℍ ≃ₜ ℍ) (hF : IsKQC (liftToC F) upperHalf 1) :
    ∃ m : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ τ, F τ = m • τ := by
  set G := liftToC F with hG
  have hGτ : ∀ τ : ℍ, G (τ : ℂ) = (F τ : ℂ) := by
    intro τ
    simp only [hG, liftToC, τ.coe_im_pos, ↓reduceDIte]
  have himg : G '' upperHalf = upperHalf := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h := hGτ ⟨z, hz⟩
      change G z = _ at h
      rw [h]
      exact (F ⟨z, hz⟩).coe_im_pos
    · intro hw
      obtain ⟨τ, hτ⟩ := F.surjective ⟨w, hw⟩
      refine ⟨τ, τ.coe_im_pos, ?_⟩
      rw [hGτ, hτ]
  have hconf : IsConformalOnto G upperHalf upperHalf := by
    have h := thm7_3_one_qc_conformal hF
    rwa [himg] at h
  -- move `F I` back to `I`
  obtain ⟨m₀, hm₀⟩ := MulAction.exists_smul_eq (Matrix.SpecialLinearGroup (Fin 2) ℝ) (F UpperHalfPlane.I)
    UpperHalfPlane.I
  have hdet : 0 < m₀ 0 0 * m₀ 1 1 - m₀ 0 1 * m₀ 1 0 := by
    have h := m₀.det_coe
    rw [Matrix.det_fin_two] at h
    rw [h]
    exact one_pos
  have hT := isConformalOnto_mobius_upperHalf hdet
  have hTτ : ∀ τ : ℍ, mobiusFn (m₀ 0 0) (m₀ 0 1) (m₀ 1 0) (m₀ 1 1) (τ : ℂ) = ((m₀ • τ : ℍ) : ℂ) := by
    intro τ
    rw [h36t_coe_smul]
    rfl
  -- the Cayley conjugate fixes `0`, hence is a rotation
  set g : ℂ → ℂ := cayley ∘ (mobiusFn (m₀ 0 0) (m₀ 0 1) (m₀ 1 0) (m₀ 1 1) ∘ G) ∘ cayleyInv with hgdef
  have hg : IsConformalOnto g unitDisc unitDisc :=
    isConformalOnto_cayley.comp ((hT.comp hconf).comp s35a_x_isConformalOnto_cayleyInv)
  have hI : cayleyInv 0 = ((UpperHalfPlane.I : ℍ) : ℂ) := by
    simp [cayleyInv, UpperHalfPlane.coe_I]
  have hg0 : g 0 = 0 := by
    simp only [hgdef, Function.comp]
    rw [hI, hGτ, hTτ, hm₀]
    simp [cayley, UpperHalfPlane.coe_I]
  obtain ⟨c', hc'1, hc'⟩ := exists_rotation_of_isConformalOnto_fix_zero hg hg0
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq c' (by norm_num : 0 < 2)
  have hu1 : ‖u‖ = 1 := by
    have h := congrArg norm hu
    rw [norm_pow, hc'1] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg u) two_ne_zero).1 h
  refine ⟨m₀⁻¹ * utm_rot u hu1, fun τ => ?_⟩
  have h1 : cayley ((m₀ • F τ : ℍ) : ℂ) = cayley ((utm_rot u hu1 • τ : ℍ) : ℂ) := by
    have h := hc' (cayley_mem_unitDisc τ.im_pos)
    simp only [hgdef, Function.comp] at h
    rw [cayleyInv_cayley τ.im_pos, hGτ, hTτ] at h
    rw [h, utm_cayley_rot, hu]
  have h2 : m₀ • F τ = utm_rot u hu1 • τ := by
    apply UpperHalfPlane.ext
    have h := congrArg cayleyInv h1
    rwa [cayleyInv_cayley (m₀ • F τ).im_pos, cayleyInv_cayley (utm_rot u hu1 • τ).im_pos] at h
  rw [mul_smul, ← h2, inv_smul_smul]

end UTMMoved

end LiZhongQC
