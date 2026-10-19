import LiZhongQC.Lemmas.UniformizedUniqueness

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold UpperHalfPlane

noncomputable section
namespace LiZhongQC

/-! Conformal transport of the literal S25 geodesic definition.
All curve comparisons below use the original parameter. No reparametrization,
non-pausing axiom, or uniqueness theorem is inserted. -/

/-- Trace containment on the closed interval also gives containment of the
open trace. This avoids imposing any condition on the extension off [0,1]. -/
theorem s25ct_trace_subset_of_closedTrace {γ : LRCurve} {D : Set ℂ}
    (hγ : γ.closedTrace ⊆ D) : γ.trace ⊆ D := by
  rintro z ⟨t, ht, rfl⟩
  exact hγ ⟨t, Ioo_subset_Icc_self ht, rfl⟩

theorem s25ct_closedTrace_mem {γ : LRCurve} {D : Set ℂ}
    (hγ : γ.closedTrace ⊆ D) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    γ.toFun t ∈ D :=
  hγ ⟨t, ht, rfl⟩

/-- Equality of curve functions on [0,1] gives the expected closed trace image. -/
theorem s25ct_closedTrace_image {γ β : LRCurve} {f : ℂ → ℂ}
    (he : EqOn β.toFun (f ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    β.closedTrace = f '' γ.closedTrace := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨γ.toFun t, ⟨t, ht, rfl⟩, (he ht).symm⟩
  · rintro ⟨w, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, he ht⟩

theorem s25ct_trace_image {γ β : LRCurve} {f : ℂ → ℂ}
    (he : EqOn β.toFun (f ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    β.trace = f '' γ.trace := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨γ.toFun t, ⟨t, ht, rfl⟩, (he (Ioo_subset_Icc_self ht)).symm⟩
  · rintro ⟨w, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, he (Ioo_subset_Icc_self ht)⟩

/-- Subarc traces retain their original parameter interval. -/
theorem s25ct_subarc_image {γ β : LRCurve} {f : ℂ → ℂ}
    (he : EqOn β.toFun (f ∘ γ.toFun) (Icc (0 : ℝ) 1))
    {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 1) :
    β.toFun '' Icc s t = f '' (γ.toFun '' Icc s t) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu01 : u ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hu.1, hu.2.trans ht⟩
    exact ⟨γ.toFun u, ⟨u, hu, rfl⟩, (he hu01).symm⟩
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    have hu01 : u ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hu.1, hu.2.trans ht⟩
    exact ⟨u, hu, he hu01⟩

theorem s25ct_initial_endpoint {γ β : LRCurve} {f : ℂ → ℂ}
    (he : EqOn β.toFun (f ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    β.toFun 0 = f (γ.toFun 0) :=
  he (by constructor <;> norm_num)

theorem s25ct_terminal_endpoint {γ β : LRCurve} {f : ℂ → ℂ}
    (he : EqOn β.toFun (f ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    β.toFun 1 = f (γ.toFun 1) :=
  he (by constructor <;> norm_num)

/-- A globally Lipschitz source curve has a globally Lipschitz holomorphic
image, obtained from the existing compact-trace path construction. -/
theorem s25ct_lipschitz_image {D D' : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f D) (hmaps : MapsTo f D D')
    {γ β : LRCurve} (hK : ∃ K : ℝ≥0, LipschitzOnWith K γ.toFun (Icc 0 1))
    (hγ : γ.closedTrace ⊆ D)
    (he : EqOn β.toFun (f ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    ∃ K : ℝ≥0, LipschitzOnWith K β.toFun (Icc 0 1) := by
  have hpath : IsPathIn D (γ.toFun 0) (γ.toFun 1) γ := ⟨hK, rfl, rfl, hγ⟩
  obtain ⟨β₀, hβ₀, hpath₀⟩ := exists_isPathIn_comp hD hf hmaps hpath
  obtain ⟨K, hK₀⟩ := hpath₀.1
  refine ⟨K, LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_⟩
  have hes : β.toFun s = β₀.toFun s := by rw [hβ₀]; exact he hs
  have het : β.toFun t = β₀.toFun t := by rw [hβ₀]; exact he ht
  rw [hes, het]
  exact hK₀.dist_le_mul s hs t ht

/-- The pointwise derivative transformation on every interior parameter.
The existing conformal derivative theorem handles nondifferentiable parameters
as well, so totalized derivatives cannot introduce a false length equality. -/
theorem s25ct_deriv_image {D D' : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℂ} (hf : IsConformalOnto f D D')
    {γ β : LRCurve} (hγ : γ.trace ⊆ D)
    (he : EqOn β.toFun (f ∘ γ.toFun) (Icc (0 : ℝ) 1))
    {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    deriv β.toFun u = deriv f (γ.toFun u) * deriv γ.toFun u := by
  have huv : ∀ᶠ v in 𝓝 u, v ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhds hu.1 hu.2
  have he' : β.toFun =ᶠ[𝓝 u] f ∘ γ.toFun :=
    huv.mono fun v hv => he (Ioo_subset_Icc_self hv)
  have hγv : ∀ᶠ v in 𝓝 u, γ.toFun v ∈ D :=
    huv.mono fun v hv => hγ ⟨v, hv, rfl⟩
  rw [he'.deriv_eq]
  exact hf.deriv_comp hD hγv

/-- Exact transport of each subarc length, not just the full curve length. -/
theorem s25ct_segmentLength_conformal {D D' : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℂ} (hf : IsConformalOnto f D D')
    {φ φ' : ℂ → ℂ}
    (hρ : ∀ z ∈ D, phiDensity φ z = phiDensity φ' (f z) * ‖deriv f z‖ₑ)
    {γ β : LRCurve} (hγ : γ.trace ⊆ D)
    (he : EqOn β.toFun (f ∘ γ.toFun) (Icc (0 : ℝ) 1))
    {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 1) :
    phiSegmentLength φ' β s t = phiSegmentLength φ γ s t := by
  change (∫⁻ u in Ioo s t, phiDensity φ' (β.toFun u) * ‖deriv β.toFun u‖ₑ) =
    ∫⁻ u in Ioo s t, phiDensity φ (γ.toFun u) * ‖deriv γ.toFun u‖ₑ
  refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have hu01 : u ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hs hu.1, lt_of_lt_of_le hu.2 ht⟩
  simp only [he (Ioo_subset_Icc_self hu01), Function.comp_apply,
    s25ct_deriv_image hD hf hγ he hu01,
    hρ _ (hγ ⟨u, hu01, rfl⟩), enorm_mul, mul_assoc]

/-- The original local-minimizing definition transports under a conformal
metric isometry. All endpoint-window quantifiers are preserved literally. -/
theorem s25ct_isPhiGeodesic_conformal {D D' : Set ℂ} (hD : IsOpen D) (hD' : IsOpen D')
    {f g : ℂ → ℂ} (hf : IsConformalOnto f D D') (hg : DifferentiableOn ℂ g D')
    (hgmaps : MapsTo g D' D) (hfg : ∀ w ∈ D', f (g w) = w)
    (hgf : ∀ z ∈ D, g (f z) = z)
    {φ φ' : ℂ → ℂ}
    (hρ : ∀ z ∈ D, phiDensity φ z = phiDensity φ' (f z) * ‖deriv f z‖ₑ)
    {γ β : LRCurve} (hγ : IsPhiGeodesic φ D γ)
    (he : EqOn β.toFun (f ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    IsPhiGeodesic φ' D' β := by
  refine ⟨s25ct_lipschitz_image hD hf.1 hf.mapsTo hγ.1 hγ.2.1 he, ?_, ?_⟩
  · rw [s25ct_closedTrace_image he]
    rintro z ⟨w, hw, rfl⟩
    exact hf.mapsTo (hγ.2.1 hw)
  · intro t₀ ht₀
    obtain ⟨δ, hδ, hshort⟩ := hγ.2.2 t₀ ht₀
    refine ⟨δ, hδ, ?_⟩
    intro s hs t ht hleft hst hright
    rw [s25ct_segmentLength_conformal hD hf hρ
      (s25ct_trace_subset_of_closedTrace hγ.2.1) he hs.1 ht.2,
      he hs, he ht, hshort s hs t ht hleft hst hright]
    exact metricDist_eq_of_isConformalOnto hD hD' hf hg hgmaps hfg hgf hρ
      (s25ct_closedTrace_mem hγ.2.1 hs) (s25ct_closedTrace_mem hγ.2.1 ht)

/-- Existence of the transported curve requires no new choice of parameter. -/
theorem s25ct_exists_geodesic_conformal {D D' : Set ℂ} (hD : IsOpen D) (hD' : IsOpen D')
    {f g : ℂ → ℂ} (hf : IsConformalOnto f D D') (hg : DifferentiableOn ℂ g D')
    (hgmaps : MapsTo g D' D) (hfg : ∀ w ∈ D', f (g w) = w)
    (hgf : ∀ z ∈ D, g (f z) = z)
    {φ φ' : ℂ → ℂ}
    (hρ : ∀ z ∈ D, phiDensity φ z = phiDensity φ' (f z) * ‖deriv f z‖ₑ)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ D γ) :
    ∃ β : LRCurve, β.toFun = f ∘ γ.toFun ∧ IsPhiGeodesic φ' D' β := by
  have hpath : IsPathIn D (γ.toFun 0) (γ.toFun 1) γ := ⟨hγ.1, rfl, rfl, hγ.2.1⟩
  obtain ⟨β, he, _⟩ := exists_isPathIn_comp hD hf.1 hf.mapsTo hpath
  refine ⟨β, he, s25ct_isPhiGeodesic_conformal hD hD' hf hg hgmaps hfg hgf hρ hγ ?_⟩
  intro u _
  exact congrFun he u

/-! Non-pausing: the exact quantified condition from Theorems 25.3 and 25.4. -/

/-- Injectivity of the coordinate map preserves every nonconstant subinterval. -/
theorem s25ct_nonpausing_image {D : Set ℂ} {f : ℂ → ℂ} (hf : InjOn f D)
    {γ β : LRCurve} (hγ : γ.closedTrace ⊆ D)
    (he : EqOn β.toFun (f ∘ γ.toFun) (Icc (0 : ℝ) 1))
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s) :
    ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, β.toFun u ≠ β.toFun s := by
  intro s t hs hst ht
  obtain ⟨u, hu, hne⟩ := hp s t hs hst ht
  have hu01 : u ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hu.1, hu.2.trans ht⟩
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hs, hst.le.trans ht⟩
  refine ⟨u, hu, ?_⟩
  intro h
  rw [he hu01, he hs01] at h
  exact hne (hf (s25ct_closedTrace_mem hγ hu01) (s25ct_closedTrace_mem hγ hs01) h)

/-- Reflection of non-pausing only uses that the image is a function of the
source curve. Injectivity is needed for the forward implication, not this one. -/
theorem s25ct_nonpausing_of_image {f : ℂ → ℂ} {γ β : LRCurve}
    (he : EqOn β.toFun (f ∘ γ.toFun) (Icc (0 : ℝ) 1))
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, β.toFun u ≠ β.toFun s) :
    ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s := by
  intro s t hs hst ht
  obtain ⟨u, hu, hne⟩ := hp s t hs hst ht
  have hu01 : u ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hu.1, hu.2.trans ht⟩
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨hs, hst.le.trans ht⟩
  refine ⟨u, hu, ?_⟩
  intro h
  apply hne
  rw [he hu01, he hs01]
  exact congrArg f h

theorem s25ct_nonpausing_iff {D : Set ℂ} {f : ℂ → ℂ} (hf : InjOn f D)
    {γ β : LRCurve} (hγ : γ.closedTrace ⊆ D)
    (he : EqOn β.toFun (f ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, β.toFun u ≠ β.toFun s) ↔
    (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s) :=
  ⟨s25ct_nonpausing_of_image he, s25ct_nonpausing_image hf hγ he⟩

/-- Injective coordinate changes reflect equality of closed traces, which is
the exact conclusion eventually needed from the disc uniqueness theorem. -/
theorem s25ct_closedTrace_eq_iff {D : Set ℂ} {f : ℂ → ℂ} (hf : InjOn f D)
    {γ₁ γ₂ β₁ β₂ : LRCurve} (h₁ : γ₁.closedTrace ⊆ D) (h₂ : γ₂.closedTrace ⊆ D)
    (he₁ : EqOn β₁.toFun (f ∘ γ₁.toFun) (Icc (0 : ℝ) 1))
    (he₂ : EqOn β₂.toFun (f ∘ γ₂.toFun) (Icc (0 : ℝ) 1)) :
    β₁.closedTrace = β₂.closedTrace ↔ γ₁.closedTrace = γ₂.closedTrace := by
  rw [s25ct_closedTrace_image he₁, s25ct_closedTrace_image he₂]
  constructor
  · intro he
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨w, hw, hwe⟩ := he ▸ (show f z ∈ f '' γ₁.closedTrace from ⟨z, hz, rfl⟩)
      exact (hf (h₂ hw) (h₁ hz) hwe) ▸ hw
    · intro z hz
      obtain ⟨w, hw, hwe⟩ := he.symm ▸ (show f z ∈ f '' γ₂.closedTrace from ⟨z, hz, rfl⟩)
      exact (hf (h₁ hw) (h₂ hz) hwe) ▸ hw
  · intro he
    rw [he]

theorem s25ct_endpoint_eq_iff {D : Set ℂ} {f : ℂ → ℂ} (hf : InjOn f D)
    {γ₁ γ₂ β₁ β₂ : LRCurve} (h₁ : γ₁.closedTrace ⊆ D) (h₂ : γ₂.closedTrace ⊆ D)
    (he₁ : EqOn β₁.toFun (f ∘ γ₁.toFun) (Icc (0 : ℝ) 1))
    (he₂ : EqOn β₂.toFun (f ∘ γ₂.toFun) (Icc (0 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    β₁.toFun t = β₂.toFun t ↔ γ₁.toFun t = γ₂.toFun t := by
  rw [he₁ ht, he₂ ht]
  exact ⟨hf (s25ct_closedTrace_mem h₁ ht) (s25ct_closedTrace_mem h₂ ht), congrArg f⟩

/-! Specialization to the fixed Cayley map and the literal utm_pull. -/

/-- Extract the holomorphic pullback fact already used internally by
utm_arc_shortest_upperHalf as a reusable public endpoint. -/
theorem s25ct_pull_holomorphic {ψ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ upperHalf) :
    DifferentiableOn ℂ (utm_pull ψ) unitDisc := by
  intro w hw
  have hw' : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
  have h1 : (1 : ℂ) - w ≠ 0 := cayleyInv_den_ne_zero hw'
  have hS : DifferentiableAt ℂ cayleyInv w :=
    (utm_hasDerivAt_cayleyInv h1).differentiableAt
  have hψS : DifferentiableAt ℂ ψ (cayleyInv w) :=
    (hψ _ (cayleyInv_mem_upperHalf hw')).differentiableAt
      (isOpen_upperHalf.mem_nhds (cayleyInv_mem_upperHalf hw'))
  have hsub : DifferentiableAt ℂ (fun v : ℂ => (1 - v) ^ 2) w :=
    ((differentiableAt_const _).sub differentiableAt_id).pow 2
  have hq : DifferentiableAt ℂ (fun v : ℂ => 2 * I / (1 - v) ^ 2) w :=
    (differentiableAt_const _).div hsub (pow_ne_zero 2 h1)
  exact ((hψS.comp w hS).mul (hq.pow 2)).differentiableWithinAt

theorem s25ct_pull_cayley_eq_zero_iff (ψ : ℂ → ℂ) {z : ℂ} (hz : z ∈ upperHalf) :
    utm_pull ψ (cayley z) = 0 ↔ ψ z = 0 := by
  have hA := utm_cay_mul (cayley_den_ne_zero hz)
  have hA0 : (2 * I / (1 - cayley z) ^ 2) ≠ 0 := left_ne_zero_of_mul_eq_one hA
  rw [utm_pull_cayley ψ hz]
  simp only [mul_eq_zero, pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0), hA0, or_false]

theorem s25ct_pull_eq_zero_iff (ψ : ℂ → ℂ) {w : ℂ} (hw : w ∈ unitDisc) :
    utm_pull ψ w = 0 ↔ ψ (cayleyInv w) = 0 := by
  have hH := cayleyInv_mem_upperHalf (mem_ball_zero_iff.1 hw)
  simpa only [cayley_cayleyInv (mem_ball_zero_iff.1 hw)] using
    s25ct_pull_cayley_eq_zero_iff ψ hH

theorem s25ct_pull_nonzero {ψ : ℂ → ℂ}
    (hne : ∃ z ∈ upperHalf, ψ z ≠ 0) :
    ∃ w ∈ unitDisc, utm_pull ψ w ≠ 0 := by
  obtain ⟨z, hz, hn⟩ := hne
  exact ⟨cayley z, cayley_mem_unitDisc hz,
    fun he => hn ((s25ct_pull_cayley_eq_zero_iff ψ hz).1 he)⟩

theorem s25ct_pull_nonzero_iff (ψ : ℂ → ℂ) :
    (∃ w ∈ unitDisc, utm_pull ψ w ≠ 0) ↔
      ∃ z ∈ upperHalf, ψ z ≠ 0 := by
  constructor
  · rintro ⟨w, hw, hn⟩
    refine ⟨cayleyInv w, cayleyInv_mem_upperHalf (mem_ball_zero_iff.1 hw), ?_⟩
    intro he
    exact hn ((s25ct_pull_eq_zero_iff ψ hw).2 he)
  · exact s25ct_pull_nonzero

/-- Scalar density relation in the orientation required by the existing
conformal metric-distance API. -/
theorem s25ct_density_cayley (ψ : ℂ → ℂ) {z : ℂ} (hz : z ∈ upperHalf) :
    phiDensity ψ z =
      phiDensity (utm_pull ψ) (cayley z) * ‖deriv cayley z‖ₑ := by
  rw [(utm_hasDerivAt_cayley (cayley_den_ne_zero hz)).deriv]
  simpa only [mul_one, enorm_one] using (utm_density ψ hz (1 : ℂ)).symm

/-- Inverse density relation, obtained without division in ENNReal. It remains
valid at zeros of the quadratic differential. -/
theorem s25ct_density_cayleyInv (ψ : ℂ → ℂ) {w : ℂ} (hw : w ∈ unitDisc) :
    phiDensity (utm_pull ψ) w =
      phiDensity ψ (cayleyInv w) * ‖deriv cayleyInv w‖ₑ := by
  have hw' := mem_ball_zero_iff.1 hw
  have hH := cayleyInv_mem_upperHalf hw'
  have hcc := cayley_cayleyInv hw'
  have hAB := utm_cay_mul (cayley_den_ne_zero hH)
  rw [hcc] at hAB
  have hBA : (2 * I / (cayleyInv w + I) ^ 2) *
      (2 * I / (1 - w) ^ 2) = 1 := (mul_comm _ _).trans hAB
  have hd := utm_density ψ hH (2 * I / (1 - w) ^ 2)
  rw [hcc, hBA, enorm_one, mul_one] at hd
  rw [(utm_hasDerivAt_cayleyInv (cayleyInv_den_ne_zero hw')).deriv]
  exact hd

/-- Equality of the actual infimum metric distances on ℍ and Δ. -/
theorem s25ct_metricDist_cayley (ψ : ℂ → ℂ) {a b : ℂ}
    (ha : a ∈ upperHalf) (hb : b ∈ upperHalf) :
    metricDist upperHalf (phiDensity ψ) a b =
      metricDist unitDisc (phiDensity (utm_pull ψ)) (cayley a) (cayley b) :=
  metricDist_eq_of_isConformalOnto isOpen_upperHalf isOpen_ball
    isConformalOnto_cayley s35a_x_isConformalOnto_cayleyInv.1
    s35a_x_isConformalOnto_cayleyInv.mapsTo
    (fun w hw => cayley_cayleyInv (mem_ball_zero_iff.1 hw))
    (fun z hz => cayleyInv_cayley hz)
    (fun z hz => s25ct_density_cayley ψ hz) ha hb

theorem s25ct_metricDist_cayleyInv (ψ : ℂ → ℂ) {a b : ℂ}
    (ha : a ∈ unitDisc) (hb : b ∈ unitDisc) :
    metricDist unitDisc (phiDensity (utm_pull ψ)) a b =
      metricDist upperHalf (phiDensity ψ) (cayleyInv a) (cayleyInv b) := by
  have h := s25ct_metricDist_cayley ψ
    (cayleyInv_mem_upperHalf (mem_ball_zero_iff.1 ha))
    (cayleyInv_mem_upperHalf (mem_ball_zero_iff.1 hb))
  simpa only [cayley_cayleyInv (mem_ball_zero_iff.1 ha),
    cayley_cayleyInv (mem_ball_zero_iff.1 hb)] using h.symm

theorem s25ct_segmentLength_cayley (ψ : ℂ → ℂ) {γ β : LRCurve}
    (hγ : γ.trace ⊆ upperHalf)
    (he : EqOn β.toFun (cayley ∘ γ.toFun) (Icc (0 : ℝ) 1))
    {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 1) :
    phiSegmentLength (utm_pull ψ) β s t = phiSegmentLength ψ γ s t :=
  s25ct_segmentLength_conformal isOpen_upperHalf isConformalOnto_cayley
    (fun z hz => s25ct_density_cayley ψ hz) hγ he hs ht

theorem s25ct_segmentLength_cayleyInv (ψ : ℂ → ℂ) {β γ : LRCurve}
    (hβ : β.trace ⊆ unitDisc)
    (he : EqOn γ.toFun (cayleyInv ∘ β.toFun) (Icc (0 : ℝ) 1))
    {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 1) :
    phiSegmentLength ψ γ s t = phiSegmentLength (utm_pull ψ) β s t :=
  s25ct_segmentLength_conformal isOpen_ball s35a_x_isConformalOnto_cayleyInv
    (fun w hw => s25ct_density_cayleyInv ψ hw) hβ he hs ht

theorem s25ct_phiLength_cayley (ψ : ℂ → ℂ) {γ β : LRCurve}
    (hγ : γ.trace ⊆ upperHalf)
    (he : EqOn β.toFun (cayley ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    phiLength (utm_pull ψ) β = phiLength ψ γ :=
  s25ct_segmentLength_cayley ψ hγ he (s := 0) (t := 1) le_rfl le_rfl

theorem s25ct_phiLength_cayleyInv (ψ : ℂ → ℂ) {β γ : LRCurve}
    (hβ : β.trace ⊆ unitDisc)
    (he : EqOn γ.toFun (cayleyInv ∘ β.toFun) (Icc (0 : ℝ) 1)) :
    phiLength ψ γ = phiLength (utm_pull ψ) β :=
  s25ct_segmentLength_cayleyInv ψ hβ he (s := 0) (t := 1) le_rfl le_rfl

/-- Forward transport of the literal local-shortest-curve predicate. -/
theorem s25ct_geodesic_cayley {ψ : ℂ → ℂ} {γ β : LRCurve}
    (hγ : IsPhiGeodesic ψ upperHalf γ)
    (he : EqOn β.toFun (cayley ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    IsPhiGeodesic (utm_pull ψ) unitDisc β :=
  s25ct_isPhiGeodesic_conformal isOpen_upperHalf isOpen_ball
    isConformalOnto_cayley s35a_x_isConformalOnto_cayleyInv.1
    s35a_x_isConformalOnto_cayleyInv.mapsTo
    (fun w hw => cayley_cayleyInv (mem_ball_zero_iff.1 hw))
    (fun z hz => cayleyInv_cayley hz)
    (fun z hz => s25ct_density_cayley ψ hz) hγ he

theorem s25ct_geodesic_cayleyInv {ψ : ℂ → ℂ} {β γ : LRCurve}
    (hβ : IsPhiGeodesic (utm_pull ψ) unitDisc β)
    (he : EqOn γ.toFun (cayleyInv ∘ β.toFun) (Icc (0 : ℝ) 1)) :
    IsPhiGeodesic ψ upperHalf γ :=
  s25ct_isPhiGeodesic_conformal isOpen_ball isOpen_upperHalf
    s35a_x_isConformalOnto_cayleyInv isConformalOnto_cayley.1
    isConformalOnto_cayley.mapsTo
    (fun z hz => cayleyInv_cayley hz)
    (fun w hw => cayley_cayleyInv (mem_ball_zero_iff.1 hw))
    (fun w hw => s25ct_density_cayleyInv ψ hw) hβ he

/-- The inverse equality holds on [0,1] even if the two total curve functions
have unrelated extensions outside the parameter interval. -/
theorem s25ct_inverse_curve_eqOn {γ β : LRCurve}
    (hγ : γ.closedTrace ⊆ upperHalf)
    (he : EqOn β.toFun (cayley ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    EqOn γ.toFun (cayleyInv ∘ β.toFun) (Icc (0 : ℝ) 1) := by
  intro t ht
  change γ.toFun t = cayleyInv (β.toFun t)
  rw [he ht]
  exact (cayleyInv_cayley (s25ct_closedTrace_mem hγ ht)).symm

theorem s25ct_forward_curve_eqOn {β γ : LRCurve}
    (hβ : β.closedTrace ⊆ unitDisc)
    (he : EqOn γ.toFun (cayleyInv ∘ β.toFun) (Icc (0 : ℝ) 1)) :
    EqOn β.toFun (cayley ∘ γ.toFun) (Icc (0 : ℝ) 1) := by
  intro t ht
  change β.toFun t = cayley (γ.toFun t)
  rw [he ht]
  exact (cayley_cayleyInv (mem_ball_zero_iff.1 (s25ct_closedTrace_mem hβ ht))).symm

theorem s25ct_geodesic_cayley_iff {ψ : ℂ → ℂ} {γ β : LRCurve}
    (hγ : γ.closedTrace ⊆ upperHalf)
    (he : EqOn β.toFun (cayley ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    IsPhiGeodesic (utm_pull ψ) unitDisc β ↔ IsPhiGeodesic ψ upperHalf γ :=
  ⟨fun hβ => s25ct_geodesic_cayleyInv hβ (s25ct_inverse_curve_eqOn hγ he),
    fun h => s25ct_geodesic_cayley h he⟩

/-- A directly usable curve-existence endpoint for the upper-half-plane
covering-lift worker. It constructs the Cayley parametrization itself. -/
theorem s25ct_exists_cayley_geodesic {ψ : ℂ → ℂ} {γ : LRCurve}
    (hγ : IsPhiGeodesic ψ upperHalf γ) :
    ∃ β : LRCurve, β.toFun = cayley ∘ γ.toFun ∧
      IsPhiGeodesic (utm_pull ψ) unitDisc β :=
  s25ct_exists_geodesic_conformal isOpen_upperHalf isOpen_ball
    isConformalOnto_cayley s35a_x_isConformalOnto_cayleyInv.1
    s35a_x_isConformalOnto_cayleyInv.mapsTo
    (fun w hw => cayley_cayleyInv (mem_ball_zero_iff.1 hw))
    (fun z hz => cayleyInv_cayley hz)
    (fun z hz => s25ct_density_cayley ψ hz) hγ

theorem s25ct_exists_cayleyInv_geodesic {ψ : ℂ → ℂ} {β : LRCurve}
    (hβ : IsPhiGeodesic (utm_pull ψ) unitDisc β) :
    ∃ γ : LRCurve, γ.toFun = cayleyInv ∘ β.toFun ∧
      IsPhiGeodesic ψ upperHalf γ :=
  s25ct_exists_geodesic_conformal isOpen_ball isOpen_upperHalf
    s35a_x_isConformalOnto_cayleyInv isConformalOnto_cayley.1
    isConformalOnto_cayley.mapsTo
    (fun z hz => cayleyInv_cayley hz)
    (fun w hw => cayley_cayleyInv (mem_ball_zero_iff.1 hw))
    (fun w hw => s25ct_density_cayleyInv ψ hw) hβ

/-! Cayley trace and non-pausing interfaces for the covering-lift consumer. -/

theorem s25ct_cayley_nonpausing_iff {γ β : LRCurve}
    (hγ : γ.closedTrace ⊆ upperHalf)
    (he : EqOn β.toFun (cayley ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, β.toFun u ≠ β.toFun s) ↔
    (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s) :=
  s25ct_nonpausing_iff isConformalOnto_cayley.2.1 hγ he

theorem s25ct_cayleyInv_nonpausing_iff {β γ : LRCurve}
    (hβ : β.closedTrace ⊆ unitDisc)
    (he : EqOn γ.toFun (cayleyInv ∘ β.toFun) (Icc (0 : ℝ) 1)) :
    (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s) ↔
    (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, β.toFun u ≠ β.toFun s) :=
  s25ct_nonpausing_iff s35a_x_isConformalOnto_cayleyInv.2.1 hβ he

theorem s25ct_cayley_closedTrace {γ β : LRCurve}
    (he : EqOn β.toFun (cayley ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    β.closedTrace = cayley '' γ.closedTrace :=
  s25ct_closedTrace_image he

theorem s25ct_cayley_inverse_closedTrace {γ β : LRCurve}
    (hγ : γ.closedTrace ⊆ upperHalf)
    (he : EqOn β.toFun (cayley ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    γ.closedTrace = cayleyInv '' β.closedTrace :=
  s25ct_closedTrace_image (s25ct_inverse_curve_eqOn hγ he)

theorem s25ct_cayley_inverse_trace {γ β : LRCurve}
    (hγ : γ.closedTrace ⊆ upperHalf)
    (he : EqOn β.toFun (cayley ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    γ.trace = cayleyInv '' β.trace :=
  s25ct_trace_image (s25ct_inverse_curve_eqOn hγ he)

theorem s25ct_cayley_closedTrace_eq_iff {γ₁ γ₂ β₁ β₂ : LRCurve}
    (h₁ : γ₁.closedTrace ⊆ upperHalf) (h₂ : γ₂.closedTrace ⊆ upperHalf)
    (he₁ : EqOn β₁.toFun (cayley ∘ γ₁.toFun) (Icc (0 : ℝ) 1))
    (he₂ : EqOn β₂.toFun (cayley ∘ γ₂.toFun) (Icc (0 : ℝ) 1)) :
    β₁.closedTrace = β₂.closedTrace ↔ γ₁.closedTrace = γ₂.closedTrace :=
  s25ct_closedTrace_eq_iff isConformalOnto_cayley.2.1 h₁ h₂ he₁ he₂

/-- Reflection of point equality includes both endpoints and every point on
the closed parameter interval. -/
theorem s25ct_cayley_point_eq_iff {γ₁ γ₂ β₁ β₂ : LRCurve}
    (h₁ : γ₁.closedTrace ⊆ upperHalf) (h₂ : γ₂.closedTrace ⊆ upperHalf)
    (he₁ : EqOn β₁.toFun (cayley ∘ γ₁.toFun) (Icc (0 : ℝ) 1))
    (he₂ : EqOn β₂.toFun (cayley ∘ γ₂.toFun) (Icc (0 : ℝ) 1))
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    β₁.toFun s = β₂.toFun t ↔ γ₁.toFun s = γ₂.toFun t := by
  rw [he₁ hs, he₂ ht]
  exact ⟨isConformalOnto_cayley.2.1
    (s25ct_closedTrace_mem h₁ hs) (s25ct_closedTrace_mem h₂ ht), congrArg cayley⟩

theorem s25ct_cayley_same_endpoints {γ₁ γ₂ β₁ β₂ : LRCurve}
    (he₁ : EqOn β₁.toFun (cayley ∘ γ₁.toFun) (Icc (0 : ℝ) 1))
    (he₂ : EqOn β₂.toFun (cayley ∘ γ₂.toFun) (Icc (0 : ℝ) 1))
    (h0 : γ₁.toFun 0 = γ₂.toFun 0) (h1 : γ₁.toFun 1 = γ₂.toFun 1) :
    β₁.toFun 0 = β₂.toFun 0 ∧ β₁.toFun 1 = β₂.toFun 1 := by
  constructor
  · rw [s25ct_initial_endpoint he₁, s25ct_initial_endpoint he₂, h0]
  · rw [s25ct_terminal_endpoint he₁, s25ct_terminal_endpoint he₂, h1]

/-- No parameter that hits a zero of the differential is lost by transport. -/
theorem s25ct_cayley_curve_zero_iff (ψ : ℂ → ℂ) {γ β : LRCurve}
    (hγ : γ.closedTrace ⊆ upperHalf)
    (he : EqOn β.toFun (cayley ∘ γ.toFun) (Icc (0 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    utm_pull ψ (β.toFun t) = 0 ↔ ψ (γ.toFun t) = 0 := by
  rw [he ht]
  exact s25ct_pull_cayley_eq_zero_iff ψ (s25ct_closedTrace_mem hγ ht)

theorem s25ct_cayley_zero_parameters (ψ : ℂ → ℂ) {γ β : LRCurve}
    (hγ : γ.closedTrace ⊆ upperHalf)
    (he : EqOn β.toFun (cayley ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    {t ∈ Icc (0 : ℝ) 1 | utm_pull ψ (β.toFun t) = 0} =
      {t ∈ Icc (0 : ℝ) 1 | ψ (γ.toFun t) = 0} := by
  ext t
  constructor
  · rintro ⟨ht, hz⟩
    exact ⟨ht, (s25ct_cayley_curve_zero_iff ψ hγ he ht).1 hz⟩
  · rintro ⟨ht, hz⟩
    exact ⟨ht, (s25ct_cayley_curve_zero_iff ψ hγ he ht).2 hz⟩

/-- Shortest-connection equality transports if it is known. This theorem
does not assert that an arbitrary local geodesic is globally shortest. -/
theorem s25ct_cayley_shortest_iff (ψ : ℂ → ℂ) {γ β : LRCurve}
    (hγ : γ.closedTrace ⊆ upperHalf)
    (he : EqOn β.toFun (cayley ∘ γ.toFun) (Icc (0 : ℝ) 1)) :
    (phiLength (utm_pull ψ) β =
      metricDist unitDisc (phiDensity (utm_pull ψ)) (β.toFun 0) (β.toFun 1)) ↔
    (phiLength ψ γ =
      metricDist upperHalf (phiDensity ψ) (γ.toFun 0) (γ.toFun 1)) := by
  rw [s25ct_phiLength_cayley ψ (s25ct_trace_subset_of_closedTrace hγ) he,
    s25ct_initial_endpoint he, s25ct_terminal_endpoint he,
    ← s25ct_metricDist_cayley ψ
      (s25ct_closedTrace_mem hγ (by constructor <;> norm_num))
      (s25ct_closedTrace_mem hγ (by constructor <;> norm_num))]

/-- Endpoint limits of a locally rectifiable curve also transport, when the
endpoint value lies in the open half-plane. -/
theorem s25ct_cayley_tendsto {α : Type*} {l : Filter α} {c : α → ℂ} {z : ℂ}
    (hz : z ∈ upperHalf) (hc : Tendsto c l (𝓝 z)) :
    Tendsto (cayley ∘ c) l (𝓝 (cayley z)) :=
  (utm_hasDerivAt_cayley (cayley_den_ne_zero hz)).continuousAt.tendsto.comp hc

theorem s25ct_cayleyInv_tendsto {α : Type*} {l : Filter α} {c : α → ℂ} {w : ℂ}
    (hw : w ∈ unitDisc) (hc : Tendsto c l (𝓝 w)) :
    Tendsto (cayleyInv ∘ c) l (𝓝 (cayleyInv w)) :=
  (utm_hasDerivAt_cayleyInv
    (cayleyInv_den_ne_zero (mem_ball_zero_iff.1 hw))).continuousAt.tendsto.comp hc

/-- The full input package for applying a future verified disc uniqueness
theorem. The non-pausing clause is the book's literal quantified condition. -/
theorem s25ct_transport_to_disc {ψ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ upperHalf) (hne : ∃ z ∈ upperHalf, ψ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic ψ upperHalf γ)
    (hp : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s) :
    ∃ β : LRCurve,
      β.toFun = cayley ∘ γ.toFun ∧
      DifferentiableOn ℂ (utm_pull ψ) unitDisc ∧
      (∃ w ∈ unitDisc, utm_pull ψ w ≠ 0) ∧
      IsPhiGeodesic (utm_pull ψ) unitDisc β ∧
      (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
        ∃ u ∈ Icc s t, β.toFun u ≠ β.toFun s) ∧
      β.toFun 0 = cayley (γ.toFun 0) ∧
      β.toFun 1 = cayley (γ.toFun 1) ∧
      β.closedTrace = cayley '' γ.closedTrace ∧
      γ.closedTrace = cayleyInv '' β.closedTrace ∧
      phiLength (utm_pull ψ) β = phiLength ψ γ := by
  obtain ⟨β, he, hβ⟩ := s25ct_exists_cayley_geodesic hγ
  have he' : EqOn β.toFun (cayley ∘ γ.toFun) (Icc (0 : ℝ) 1) :=
    fun t _ => congrFun he t
  exact ⟨β, he, s25ct_pull_holomorphic hψ, s25ct_pull_nonzero hne, hβ,
    (s25ct_cayley_nonpausing_iff hγ.2.1 he').2 hp,
    s25ct_initial_endpoint he', s25ct_terminal_endpoint he',
    s25ct_cayley_closedTrace he', s25ct_cayley_inverse_closedTrace hγ.2.1 he',
    s25ct_phiLength_cayley ψ (s25ct_trace_subset_of_closedTrace hγ.2.1) he'⟩

/-- Transport two geodesics simultaneously, preserving their common endpoints
and reflecting the desired trace equality. No uniqueness result is invoked. -/
theorem s25ct_transport_pair_to_disc {ψ : ℂ → ℂ}
    (hψ : DifferentiableOn ℂ ψ upperHalf) (hne : ∃ z ∈ upperHalf, ψ z ≠ 0)
    {γ₁ γ₂ : LRCurve} (h₁ : IsPhiGeodesic ψ upperHalf γ₁)
    (h₂ : IsPhiGeodesic ψ upperHalf γ₂)
    (hp₁ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₁.toFun u ≠ γ₁.toFun s)
    (hp₂ : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ₂.toFun u ≠ γ₂.toFun s)
    (h0 : γ₁.toFun 0 = γ₂.toFun 0) (h1 : γ₁.toFun 1 = γ₂.toFun 1) :
    ∃ β₁ β₂ : LRCurve,
      β₁.toFun = cayley ∘ γ₁.toFun ∧ β₂.toFun = cayley ∘ γ₂.toFun ∧
      DifferentiableOn ℂ (utm_pull ψ) unitDisc ∧
      (∃ w ∈ unitDisc, utm_pull ψ w ≠ 0) ∧
      IsPhiGeodesic (utm_pull ψ) unitDisc β₁ ∧
      IsPhiGeodesic (utm_pull ψ) unitDisc β₂ ∧
      (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
        ∃ u ∈ Icc s t, β₁.toFun u ≠ β₁.toFun s) ∧
      (∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
        ∃ u ∈ Icc s t, β₂.toFun u ≠ β₂.toFun s) ∧
      β₁.toFun 0 = β₂.toFun 0 ∧ β₁.toFun 1 = β₂.toFun 1 ∧
      (β₁.closedTrace = β₂.closedTrace ↔ γ₁.closedTrace = γ₂.closedTrace) := by
  obtain ⟨β₁, he₁, hβ₁⟩ := s25ct_exists_cayley_geodesic h₁
  obtain ⟨β₂, he₂, hβ₂⟩ := s25ct_exists_cayley_geodesic h₂
  have he₁' : EqOn β₁.toFun (cayley ∘ γ₁.toFun) (Icc (0 : ℝ) 1) :=
    fun t _ => congrFun he₁ t
  have he₂' : EqOn β₂.toFun (cayley ∘ γ₂.toFun) (Icc (0 : ℝ) 1) :=
    fun t _ => congrFun he₂ t
  obtain ⟨hβ0, hβ1⟩ := s25ct_cayley_same_endpoints he₁' he₂' h0 h1
  exact ⟨β₁, β₂, he₁, he₂, s25ct_pull_holomorphic hψ, s25ct_pull_nonzero hne,
    hβ₁, hβ₂, (s25ct_cayley_nonpausing_iff h₁.2.1 he₁').2 hp₁,
    (s25ct_cayley_nonpausing_iff h₂.2.1 he₂').2 hp₂, hβ0, hβ1,
    s25ct_cayley_closedTrace_eq_iff h₁.2.1 h₂.2.1 he₁' he₂'⟩

/-- A disc trace equality can be passed through any subsequent projection.
This is deliberately only a consequence of an equality already obtained by
the caller; it supplies no uniqueness premise or theorem. -/
theorem s25ct_projected_trace_of_disc_trace {X : Type*} (P : ℂ → X)
    {γ₁ γ₂ β₁ β₂ : LRCurve}
    (h₁ : γ₁.closedTrace ⊆ upperHalf) (h₂ : γ₂.closedTrace ⊆ upperHalf)
    (he₁ : EqOn β₁.toFun (cayley ∘ γ₁.toFun) (Icc (0 : ℝ) 1))
    (he₂ : EqOn β₂.toFun (cayley ∘ γ₂.toFun) (Icc (0 : ℝ) 1))
    (htr : β₁.closedTrace = β₂.closedTrace) :
    P '' γ₁.closedTrace = P '' γ₂.closedTrace := by
  rw [(s25ct_cayley_closedTrace_eq_iff h₁ h₂ he₁ he₂).1 htr]

end LiZhongQC

