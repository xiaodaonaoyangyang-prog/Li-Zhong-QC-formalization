import LiZhongQC.Ch07.S26_TeichmullerUniqueness

/-!
# The flux route to the Reich–Strebel inequality (35.5)

Upstream companion module of S35: it imports
`LiZhongQC.Ch07.S26_TeichmullerUniqueness` and nothing from S33–S35.  The analysis is stated with
`lambdaStretchPlane φ φ g` and `DifferentiableOn ℂ φ unitDisc ∧ phiArea φ unitDisc < ⊤` in place of the
S35 aliases `lambdaStretchDisc` / `integrableQD`; the final theorem `fx_eq35_5` is (35.5) in these terms,
and S35's `eq35_5_integrated` follows from it by unfolding the aliases.

The only global input is Teichmüller's lemma `thm25_2_polygon` (S25), used in exactly one place,
`fx_teich_symm` below.

## The route

1. `φ_r(z) = r² φ(r z)` reduces (35.5) to *tame* `φ` (holomorphic on a disc of radius `> 1`):
   `fx_eq35_5_limit`.
2. For tame `φ ≢ 0`, the critical vertical graph is a finite forest (`fx_IsVForest`,
   `fx_vforest_exists`); every non-forest configuration yields a closed chain of `φ`-straight arcs
   with at most two non-blunt corners, which Teichmüller's lemma excludes (`fx_chain_false`).
3. A horizontal leaf meets at most one edge at each zero (`fx_star`), and the forest has no
   cycles (`fx_nocycle`), so every leaf is avoided by some hanging cut system (`fx_cutChoice_avoid`).
4. On the complement of a cut system, `u = Re Φ` (`Φ'² = φ`) is continuous across the cuts and
   Lipschitz (`fx_cutCalib`).
5. The leaves avoiding the cuts form measurable saturated sets (`fx_sat_open`); together they cover
   `Δ` up to a null set (`fx_cover_of_forest`, `fx_cover`).
6. On each saturated set the flux of the horizontal field vanishes against `u ∘ g - u` (which tends
   to `0` at `∂Δ` by the Lipschitz bound), and the pointwise calibration
   `t25_pointwise_lipschitz_calibration` gives `∬_R |φ| ≤ ∬_R |φ| λ` (`fx_flux_engine`).
7. Summation (`fx_eq35_5_tame`) and the limit give `fx_eq35_5`.

## Main pieces

* **Analysis:** `fx_isGoodSelfMap_of_boundary`, `fx_flux_engine`, `fx_eq35_5_limit`.
* **Polygons and leaves:** `fx_chain_polygon`, `fx_htraj_unique`, `fx_htraj_injOn`,
  `fx_leaf_symm`, `fx_leaf_trans`, `fx_star`, `fx_nocycle`.
* **Vertical forest:** `fx_flowBox_exists`, `fx_plaque_leaf`, `fx_vforest_exists`.
* **Cut calibrations and covering:** `fx_sat_open`, `fx_cutCalib`, `fx_cutChoice_avoid`,
  `fx_cover_of_forest`.
* **Glue:** `fx_teich_symm`, `fx_chain_false`, `fx_cover`, `fx_eq35_5_tame`,
  `fx_eq35_5`, the lemmas of §0 and the change of variables `fx_lintegral_image_eq`.
* **The geodesic property** (not on the (35.5) path): `fx_arc_shortest` (the geodesic property, with S35's
  `rayLength` unfolded; S35 derives `lemma35_3`, `lemma35_2` from it).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ## §0 The pointwise calibration -/

/-- Algebra: `|conj s · (A + B s/conj s)| = |s| |A + B φ/|φ||` when `s² = φ`. -/
theorem t25_norm_conj_mul_eq {s φz A B : ℂ} (hs : s ^ 2 = φz) :
    ‖A * conj s + B * s‖ = Real.sqrt ‖φz‖ * ‖A + B * (φz / (‖φz‖ : ℂ))‖ := by
  by_cases h0 : s = 0
  · subst h0
    have : φz = 0 := by rw [← hs]; ring
    subst this; simp
  have hsn : 0 < ‖s‖ := norm_pos_iff.2 h0
  have hφ : ‖φz‖ = ‖s‖ ^ 2 := by rw [← hs, norm_pow]
  have hsq : Real.sqrt ‖φz‖ = ‖s‖ := by rw [hφ, Real.sqrt_sq (norm_nonneg s)]
  rw [hsq]
  have hc : conj s ≠ 0 := (map_ne_zero _).2 h0
  -- `φ/|φ| = s / conj s`
  have hratio : φz / (‖φz‖ : ℂ) = s / conj s := by
    rw [hφ, ← hs]
    have : ((‖s‖ ^ 2 : ℝ) : ℂ) = s * conj s := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [this]
    field_simp
  rw [hratio]
  have hkey : A * conj s + B * s = conj s * (A + B * (s / conj s)) := by
    field_simp
  rw [hkey, norm_mul, Complex.norm_conj]

/-- **Pointwise Lipschitz calibration.**  For any linear map `L` of norm `≤ |φ(g z)|^{1/2}` (the
differential at `g z` of a `φ`-1-Lipschitz calibration) and `s² = φ z`, the derivative of `u ∘ g`
in the horizontal direction `conj s` is bounded by `|φ z| λ_{g,φ}(z)`. -/
theorem t25_pointwise_lipschitz_calibration {φ g : ℂ → ℂ} {z : ℂ} {L : ℂ →L[ℝ] ℝ}
    (hL : ‖L‖ ≤ Real.sqrt ‖φ (g z)‖) {s : ℂ} (hs : s ^ 2 = φ z) :
    |L (fderiv ℝ g z (conj s))| ≤ ‖φ z‖ * lambdaStretchPlane φ φ g z := by
  have hexp : fderiv ℝ g z (conj s) = dz g z * conj s + dzbar g z * s := by
    rw [sp_c_fderiv_eq_dz_dzbar g z (conj s), Complex.conj_conj]
  rw [hexp]
  have h1 : |L (dz g z * conj s + dzbar g z * s)| ≤ ‖L‖ * ‖dz g z * conj s + dzbar g z * s‖ := by
    have := L.le_opNorm (dz g z * conj s + dzbar g z * s)
    rwa [Real.norm_eq_abs] at this
  refine h1.trans ?_
  rw [t25_norm_conj_mul_eq hs]
  unfold lambdaStretchPlane
  set X := ‖dz g z + dzbar g z * (φ z / (‖φ z‖ : ℂ))‖
  have hX : 0 ≤ X := norm_nonneg _
  by_cases hφ0 : φ z = 0
  · have hs0 : s = 0 := by
      have : s ^ 2 = 0 := by rw [hs, hφ0]
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    subst hs0
    simp [hφ0]
  have hpos : 0 < Real.sqrt ‖φ z‖ := Real.sqrt_pos.2 (norm_pos_iff.2 hφ0)
  have e : ‖φ z‖ * (Real.sqrt ‖φ (g z)‖ * X / Real.sqrt ‖φ z‖) =
      (‖φ z‖ / Real.sqrt ‖φ z‖) * (Real.sqrt ‖φ (g z)‖ * X) := by ring
  rw [e, Real.div_sqrt]
  calc ‖L‖ * (Real.sqrt ‖φ z‖ * X)
      ≤ Real.sqrt ‖φ (g z)‖ * (Real.sqrt ‖φ z‖ * X) :=
        mul_le_mul_of_nonneg_right hL (mul_nonneg hpos.le hX)
    _ = Real.sqrt ‖φ z‖ * (Real.sqrt ‖φ (g z)‖ * X) := by ring

/-- The companion identity: if `Φ' = s` at `z`, then the derivative of `Re Φ` in the direction
`conj s` is `|s|² = |φ z|` when `s² = φ z` (the calibration is tight along horizontal directions). -/
theorem t25_calibration_identity {Φ : ℂ → ℂ} {z s : ℂ} (hΦ : HasDerivAt Φ s z) {φz : ℂ}
    (hs : s ^ 2 = φz) :
    fderiv ℝ (fun w => (Φ w).re) z (conj s) = ‖φz‖ := by
  have hF : HasFDerivAt (fun w => (Φ w).re)
      (Complex.reCLM.comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) s).restrictScalars ℝ)) z :=
    Complex.reCLM.hasFDerivAt.comp z (hΦ.hasFDerivAt.restrictScalars ℝ)
  rw [hF.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul,
    Complex.reCLM_apply]
  rw [← hs, norm_pow, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rfl

/-- **Change of variables through a quasiconformal map**: `∫_{g(D)} G = ∫_D J_g · G ∘ g`
for any `G : ℂ → ℝ≥0∞` (lower integrals).  Used for the dominator of `fx_eq35_5_limit`. -/
theorem fx_lintegral_image_eq {g : ℂ → ℂ} {D : Set ℂ} {K : ℝ} (hg : IsKQC g D K)
    (G : ℂ → ℝ≥0∞) :
    ∫⁻ w in g '' D, G w = ∫⁻ z in D, ENNReal.ofReal (jacobian g z) * G (g z) := by
  have hD : MeasurableSet D := hg.1.measurableSet
  set A : Set ℂ := D ∩ {z | DifferentiableAt ℝ g z} with hAdef
  have hSm : MeasurableSet A := hD.inter (measurableSet_of_differentiableAt ℝ g)
  have hAD : A ⊆ D := inter_subset_left
  have hnull : volume (D \ A) = 0 := by
    have h := thm9_3_differentiable_ae hg
    rw [ae_restrict_iff' hD, ae_iff] at h
    exact measure_mono_null (fun z hz => fun h' => hz.2 ⟨hz.1, h' hz.1⟩) h
  have himg_null : volume (g '' (D \ A)) = 0 :=
    ac_n_volume_image_null_of_isKQC hg (fun z hz => hz.1) hnull
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hSm
    (fun z hz => hz.2.hasFDerivAt.hasFDerivWithinAt) (hg.2.2.1.2.1.mono hAD) G
  have hset1 : (g '' D : Set ℂ) =ᵐ[volume] (g '' A : Set ℂ) := by
    refine ae_eq_set.2 ⟨measure_mono_null ?_ himg_null, by
      rw [sdiff_eq_empty.2 (image_mono hAD), measure_empty]⟩
    rintro _ ⟨⟨z, hz, rfl⟩, hzA⟩
    exact ⟨z, ⟨hz, fun h => hzA ⟨z, h, rfl⟩⟩, rfl⟩
  have hset2 : (A : Set ℂ) =ᵐ[volume] (D : Set ℂ) :=
    ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 hAD, measure_empty], hnull⟩
  calc ∫⁻ w in g '' D, G w = ∫⁻ w in g '' A, G w := setLIntegral_congr hset1
    _ = ∫⁻ z in A, ENNReal.ofReal |(fderiv ℝ g z).det| * G (g z) := hcv
    _ = ∫⁻ z in A, ENNReal.ofReal (jacobian g z) * G (g z) := by
        refine setLIntegral_congr_fun hSm ?_
        intro z hz
        dsimp only
        have e : (fderiv ℝ g z).det = jacobian g z := det_fderiv_eq_jacobian hz.2
        rw [e, abs_of_nonneg (ac_j_jacobian_nonneg hg hz.1 hz.2)]
    _ = ∫⁻ z in D, ENNReal.ofReal (jacobian g z) * G (g z) := setLIntegral_congr hset2

/-! ## §1 Closed chains of `φ`-straight arcs; Teichmüller's lemma in symmetric form -/

/-- A **closed chain** of `n` `φ`-straight `C¹` arcs in `Δ` forming a simple closed curve: the data
of a `PhiPolygon` without the domain, the orientation and the angles.  `side j` runs from
`side j 0` to `side j 1 = side (j + 1) 0`; its one-sided derivatives at both ends are nonzero, and
consecutive sides do not form a cusp (`arg ≠ 0` of the corner ratio). -/
structure fx_IsChain (φ : ℂ → ℂ) {n : ℕ} [NeZero n] (side : Fin n → ℝ → ℂ) : Prop where
  /-- every side is a `φ`-straight arc on `(0, 1)` -/
  straight : ∀ j, IsPhiStraightArc φ (side j) 0 1
  /-- every side is `C¹` on `[0, 1]` -/
  smooth : ∀ j, ContDiffOn ℝ 1 (side j) (Icc 0 1)
  /-- the chain lies in `Δ` -/
  mem : ∀ j, side j '' Icc 0 1 ⊆ unitDisc
  /-- consecutive sides are joined -/
  next : ∀ j, side j 1 = side (j + 1) 0
  /-- the chain is a simple closed curve -/
  simple : ∀ i j : Fin n, ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1, side i s = side j t →
    i = j ∧ s = t
  /-- nonzero tangent at the start of each side -/
  tan0 : ∀ j, derivWithin (side j) (Icc 0 1) 0 ≠ 0
  /-- nonzero tangent at the end of each side -/
  tan1 : ∀ j, derivWithin (side j) (Icc 0 1) 1 ≠ 0
  /-- no cusp at the corners -/
  no_cusp : ∀ j,
    arg (-(derivWithin (side (j - 1)) (Icc 0 1) 1) / derivWithin (side j) (Icc 0 1) 0) ≠ 0

/-- The (counter-clockwise-listing) corner angle of a chain at the vertex `side j 0`: the
representative in `(0, 2π]` of `arg (-side'_{j-1}(1) / side'_j(0))` (the `PhiPolygon` angle when
the listing is positive). -/
def fx_chainAngle {n : ℕ} [NeZero n] (side : Fin n → ℝ → ℂ) (j : Fin n) : ℝ :=
  if 0 < arg (-(derivWithin (side (j - 1)) (Icc 0 1) 1) / derivWithin (side j) (Icc 0 1) 0) then
    arg (-(derivWithin (side (j - 1)) (Icc 0 1) 1) / derivWithin (side j) (Icc 0 1) 0)
  else arg (-(derivWithin (side (j - 1)) (Icc 0 1) 1) / derivWithin (side j) (Icc 0 1) 0) + 2 * π

/-- A **blunt** corner: at the vertex, where `φ` has a zero of order `m ≥ 0`, the angle lies in
`[2π/(m+2), 2π - 2π/(m+2)]`, so it qualifies for Teichmüller's lemma in neither orientation.
(Two distinct critical rays at a zero, and a smooth passage `θ = π` through a regular point, are
blunt.) -/
def fx_IsBlunt (φ : ℂ → ℂ) {n : ℕ} [NeZero n] (side : Fin n → ℝ → ℂ) (j : Fin n) : Prop :=
  ∃ m : ℕ, meromorphicOrderAt φ (side j 0) = (m : ℤ) ∧
    2 * π / ((m : ℝ) + 2) ≤ fx_chainAngle side j ∧
      fx_chainAngle side j ≤ 2 * π - 2 * π / ((m : ℝ) + 2)

/-- Affine reparametrisation `τ ↦ f (α + β τ)` of a function with derivatives within `S`: its
derivative within `Icc p q`. -/
theorem fx_p2_hasDerivWithinAt_affine {f : ℝ → ℂ} {S : Set ℝ} {f' : ℝ → ℂ}
    (hf : ∀ x ∈ S, HasDerivWithinAt f (f' x) S x) {α β p q : ℝ}
    (hmap : ∀ τ ∈ Icc p q, α + β * τ ∈ S) {τ : ℝ} (hτ : τ ∈ Icc p q) :
    HasDerivWithinAt (fun τ => f (α + β * τ)) ((β : ℂ) * f' (α + β * τ)) (Icc p q) τ := by
  have he : HasDerivWithinAt (fun τ : ℝ => α + β * τ) β (Icc p q) τ := by
    simpa using (((hasDerivAt_id τ).const_mul β).const_add α).hasDerivWithinAt
  have := (hf _ (hmap τ hτ)).scomp τ he (fun x hx => hmap x hx)
  simpa [Function.comp_def, Complex.real_smul] using this

/-- The derivative within `Icc p q` of an affine reparametrisation. -/
theorem fx_p2_derivWithin_affine {f : ℝ → ℂ} {S : Set ℝ} {f' : ℝ → ℂ}
    (hf : ∀ x ∈ S, HasDerivWithinAt f (f' x) S x) {α β p q : ℝ} (hpq : p < q)
    (hmap : ∀ τ ∈ Icc p q, α + β * τ ∈ S) {τ : ℝ} (hτ : τ ∈ Icc p q) :
    derivWithin (fun τ => f (α + β * τ)) (Icc p q) τ = (β : ℂ) * f' (α + β * τ) :=
  (fx_p2_hasDerivWithinAt_affine hf hmap hτ).derivWithin (uniqueDiffOn_Icc hpq τ hτ)

/-- An affine reparametrisation of a `C¹` function is `C¹`. -/
theorem fx_p2_contDiffOn_affine {f : ℝ → ℂ} {S : Set ℝ} (hf : ContDiffOn ℝ 1 f S) {α β p q : ℝ}
    (hmap : ∀ τ ∈ Icc p q, α + β * τ ∈ S) :
    ContDiffOn ℝ 1 (fun τ => f (α + β * τ)) (Icc p q) :=
  hf.comp (by fun_prop : ContDiff ℝ 1 (fun τ : ℝ => α + β * τ)).contDiffOn (fun x hx => hmap x hx)

/-- A `C¹` function on `Icc a b` has its `derivWithin` as derivative within `Icc a b`. -/
theorem fx_p2_hasDerivWithinAt_of_contDiffOn {f : ℝ → ℂ} {a b : ℝ}
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    ∀ x ∈ Icc a b, HasDerivWithinAt f (derivWithin f (Icc a b) x) (Icc a b) x :=
  fun x hx => ((hf.differentiableOn one_ne_zero) x hx).hasDerivWithinAt

/-- Unit-speed horizontal trajectory (a verbatim copy of the body of `fx_IsHTraj`, placed here so
that the helpers can precede it). -/
def fx_p2_htrajP (φ : ℂ → ℂ) (γ : ℝ → ℂ) (T : ℝ) : Prop :=
  0 < T ∧ ContDiffOn ℝ 1 γ (Icc 0 T) ∧ (∀ t ∈ Icc 0 T, γ t ∈ unitDisc ∧ φ (γ t) ≠ 0) ∧
    ∀ t ∈ Icc 0 T, φ (γ t) * derivWithin γ (Icc 0 T) t ^ 2 = 1

/-- The leaf (a verbatim copy of the body of `fx_leaf`). -/
def fx_p2_leafP (φ : ℂ → ℂ) (z : ℂ) : Set ℂ :=
  {w | (w = z ∧ z ∈ unitDisc ∧ φ z ≠ 0) ∨
    ∃ (γ : ℝ → ℂ) (T : ℝ), fx_p2_htrajP φ γ T ∧ γ 0 = z ∧ γ T = w}

/-- The derivative of an affine (`β = ±1`) reparametrisation of a trajectory. -/
theorem fx_p2_htrajP_derivWithin_affine {φ : ℂ → ℂ} {γ : ℝ → ℂ} {T : ℝ} (hγ : fx_p2_htrajP φ γ T)
    {α β L : ℝ} (hL : 0 < L) (hmap : ∀ τ ∈ Icc 0 L, α + β * τ ∈ Icc 0 T) {τ : ℝ}
    (hτ : τ ∈ Icc 0 L) :
    derivWithin (fun τ => γ (α + β * τ)) (Icc 0 L) τ =
      (β : ℂ) * derivWithin γ (Icc 0 T) (α + β * τ) :=
  fx_p2_derivWithin_affine (fx_p2_hasDerivWithinAt_of_contDiffOn hγ.2.1) hL hmap hτ

/-- An affine reparametrisation `τ ↦ γ (α ± τ)` of a trajectory is a trajectory. -/
theorem fx_p2_htrajP_affine {φ : ℂ → ℂ} {γ : ℝ → ℂ} {T : ℝ} (hγ : fx_p2_htrajP φ γ T) {α β L : ℝ}
    (hβ : β ^ 2 = 1) (hL : 0 < L) (hmap : ∀ τ ∈ Icc 0 L, α + β * τ ∈ Icc 0 T) :
    fx_p2_htrajP φ (fun τ => γ (α + β * τ)) L := by
  refine ⟨hL, fx_p2_contDiffOn_affine hγ.2.1 hmap, fun τ hτ => hγ.2.2.1 _ (hmap τ hτ), ?_⟩
  intro τ hτ
  rw [fx_p2_htrajP_derivWithin_affine hγ hL hmap hτ, mul_pow]
  have hβ' : ((β : ℂ)) ^ 2 = 1 := by exact_mod_cast hβ
  rw [hβ', one_mul]
  exact hγ.2.2.2 _ (hmap τ hτ)

/-- Leaves are symmetric. -/
theorem fx_p2_leafP_symm {φ : ℂ → ℂ} {z w : ℂ} (h : w ∈ fx_p2_leafP φ z) : z ∈ fx_p2_leafP φ w := by
  rcases h with ⟨rfl, hz, hz0⟩ | ⟨γ, T, hγ, h0, hT⟩
  · exact Or.inl ⟨rfl, hz, hz0⟩
  · refine Or.inr ⟨fun τ => γ (T + (-1) * τ), T, fx_p2_htrajP_affine hγ (by norm_num) hγ.1 ?_, ?_,
      ?_⟩
    · intro τ hτ
      exact ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    · simp [hT]
    · simp [h0]

/-- A local holomorphic branch of `φ^{-1/2}`, Lipschitz near a regular point. -/
theorem fx_p2_local_branch {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {p w₀ : ℂ}
    (hp : p ∈ unitDisc) (hw : φ p * w₀ ^ 2 = 1) :
    ∃ (h : ℂ → ℂ) (U : Set ℂ) (K : ℝ≥0), U ∈ 𝓝 p ∧ h p = w₀ ∧ LipschitzOnWith K h U ∧
      ∀ z ∈ U, φ z * h z ^ 2 = 1 := by
  have hp0 : φ p ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hw
    exact zero_ne_one hw
  have hφa : AnalyticAt ℂ φ p := hφ.analyticAt (isOpen_ball.mem_nhds hp)
  set h : ℂ → ℂ := fun z => w₀ * cexp (log (φ p / φ z) / 2) with hh
  have hha : AnalyticAt ℂ h p := by
    have h1 : AnalyticAt ℂ (fun z => φ p / φ z) p := analyticAt_const.div hφa hp0
    have h2 : AnalyticAt ℂ (fun z => log (φ p / φ z)) p := by
      have hsl : φ p / φ p ∈ slitPlane := by
        rw [div_self hp0]
        exact one_mem_slitPlane
      have h2' : AnalyticAt ℂ (log ∘ fun z => φ p / φ z) p := by
        apply AnalyticAt.comp _ h1
        exact analyticAt_clog hsl
      exact h2'
    have h3 : AnalyticAt ℂ (fun z => log (φ p / φ z) / 2) p := h2.div_const
    exact analyticAt_const.mul h3.cexp
  obtain ⟨K, t, ht, hK⟩ :=
    ((hha.contDiffAt (n := 1)).restrict_scalars ℝ).exists_lipschitzOnWith
  have hne : ∀ᶠ z in 𝓝 p, φ z ≠ 0 :=
    hφa.continuousAt.eventually_ne hp0
  refine ⟨h, t ∩ {z | φ z ≠ 0}, K, inter_mem ht hne, ?_, hK.mono inter_subset_left, ?_⟩
  · simp [hh, div_self hp0]
  · rintro z ⟨-, hz⟩
    have hz' : φ z ≠ 0 := hz
    simp only [hh, mul_pow]
    rw [← Complex.exp_nat_mul]
    have : ((2 : ℕ) : ℂ) * (log (φ p / φ z) / 2) = log (φ p / φ z) := by
      push_cast; ring
    rw [this, Complex.exp_log (div_ne_zero hp0 hz')]
    field_simp
    rw [← hw]
    ring

/-- Near a time `x`, a trajectory stays in a neighbourhood `U` of `γ x` and its velocity and
`h ∘ γ` stay within `‖w₀‖/2` of `w₀ = γ'(x) = h (γ x)`. -/
theorem fx_p2_htrajP_eventually {φ : ℂ → ℂ} {γ : ℝ → ℂ} {T : ℝ} (hγ : fx_p2_htrajP φ γ T) {x : ℝ}
    (hx0 : 0 ≤ x) (hxT : x < T) {h : ℂ → ℂ} {U : Set ℂ} (hU : U ∈ 𝓝 (γ x))
    (hhc : ContinuousAt h (γ x)) {w₀ : ℂ} (hw0 : w₀ ≠ 0)
    (hd : derivWithin γ (Icc 0 T) x = w₀) (hh : h (γ x) = w₀) :
    ∀ᶠ t in 𝓝[≥] x, γ t ∈ U ∧ ‖derivWithin γ (Icc 0 T) t - w₀‖ < ‖w₀‖ / 2 ∧
      ‖h (γ t) - w₀‖ < ‖w₀‖ / 2 := by
  have hxI : x ∈ Icc 0 T := ⟨hx0, hxT.le⟩
  have hmem : Icc 0 T ∈ 𝓝[≥] x := Icc_mem_nhdsGE_of_mem ⟨hx0, hxT⟩
  have hγc : ContinuousWithinAt γ (Icc 0 T) x := hγ.2.1.continuousOn.continuousWithinAt hxI
  have hdc : ContinuousWithinAt (derivWithin γ (Icc 0 T)) (Icc 0 T) x :=
    (hγ.2.1.continuousOn_derivWithin (uniqueDiffOn_Icc (hx0.trans_lt hxT))
      le_rfl).continuousWithinAt hxI
  have hγc' : Tendsto γ (𝓝[≥] x) (𝓝 (γ x)) := hγc.mono_of_mem_nhdsWithin hmem
  have hdc' : Tendsto (derivWithin γ (Icc 0 T)) (𝓝[≥] x) (𝓝 w₀) := by
    rw [← hd]; exact hdc.mono_of_mem_nhdsWithin hmem
  have hhc' : Tendsto (fun t => h (γ t)) (𝓝[≥] x) (𝓝 w₀) := by
    rw [← hh]; exact hhc.tendsto.comp hγc'
  have hw2 : 0 < ‖w₀‖ / 2 := by have := norm_pos_iff.2 hw0; positivity
  filter_upwards [hγc'.eventually hU, hdc'.eventually (Metric.ball_mem_nhds w₀ hw2),
    hhc'.eventually (Metric.ball_mem_nhds w₀ hw2)] with t h1 h2 h3
  exact ⟨h1, by rw [← dist_eq_norm]; exact h2, by rw [← dist_eq_norm]; exact h3⟩

/-- The sign argument: if `φ(γ)γ'² = 1 = φ(γ) h(γ)²` and both `γ'` and `h ∘ γ` are close to
`w₀ ≠ 0`, then `γ' = h ∘ γ`. -/
theorem fx_p2_sign_eq {a b c w₀ : ℂ} (hc : c ≠ 0) (ha : c * a ^ 2 = 1) (hb : c * b ^ 2 = 1)
    (h1 : ‖a - w₀‖ < ‖w₀‖ / 2) (h2 : ‖b - w₀‖ < ‖w₀‖ / 2) : a = b := by
  have hsq : a ^ 2 = b ^ 2 := mul_left_cancel₀ hc (ha.trans hb.symm)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact h
  · exfalso
    have e : (2 : ℂ) * w₀ = -(a - w₀) - (b - w₀) := by rw [h]; ring
    have : ‖(2 : ℂ) * w₀‖ ≤ ‖a - w₀‖ + ‖b - w₀‖ := by
      rw [e]
      calc ‖-(a - w₀) - (b - w₀)‖ ≤ ‖-(a - w₀)‖ + ‖b - w₀‖ := norm_sub_le _ _
        _ = ‖a - w₀‖ + ‖b - w₀‖ := by rw [norm_neg]
    rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at this
    linarith [norm_nonneg w₀]

/-- Local forward uniqueness of trajectories with equal position and velocity at `x`. -/
theorem fx_p2_htrajP_unique_local {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {γ₁ γ₂ : ℝ → ℂ}
    {T₁ T₂ : ℝ} (h₁ : fx_p2_htrajP φ γ₁ T₁) (h₂ : fx_p2_htrajP φ γ₂ T₂) {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x < T₁) (hx2 : x < T₂) (hxe : γ₁ x = γ₂ x)
    (hxd : derivWithin γ₁ (Icc 0 T₁) x = derivWithin γ₂ (Icc 0 T₂) x) :
    ∃ ε > 0, x + ε < T₁ ∧ x + ε < T₂ ∧ ∀ t ∈ Icc x (x + ε), γ₁ t = γ₂ t := by
  have hxI₁ : x ∈ Icc 0 T₁ := ⟨hx0, hx1.le⟩
  have hw : φ (γ₁ x) * derivWithin γ₁ (Icc 0 T₁) x ^ 2 = 1 := h₁.2.2.2 x hxI₁
  have hw0 : derivWithin γ₁ (Icc 0 T₁) x ≠ 0 := by
    rintro h0; rw [h0] at hw; simp at hw
  obtain ⟨h, U, K, hU, hp, hK, hUeq⟩ := fx_p2_local_branch hφ (h₁.2.2.1 x hxI₁).1 hw
  have hhc : ContinuousAt h (γ₁ x) := (hK.continuousOn).continuousAt hU
  have e₁ := fx_p2_htrajP_eventually h₁ hx0 hx1 hU hhc hw0 rfl hp
  have e₂ := fx_p2_htrajP_eventually h₂ hx0 hx2 (hxe ▸ hU) (hxe ▸ hhc) hw0 hxd.symm (hxe ▸ hp)
  obtain ⟨u, hxu, hu⟩ := mem_nhdsGE_iff_exists_Icc_subset.1 (e₁.and e₂)
  set ε := min (u - x) ((min T₁ T₂ - x) / 2) with hε
  have hm : x < min T₁ T₂ := lt_min hx1 hx2
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hε1 : ε ≤ u - x := min_le_left _ _
  have hε2 : ε ≤ (min T₁ T₂ - x) / 2 := min_le_right _ _
  have hT1 : x + ε < T₁ := by linarith [min_le_left T₁ T₂]
  have hT2 : x + ε < T₂ := by linarith [min_le_right T₁ T₂]
  refine ⟨ε, hε0, hT1, hT2, ?_⟩
  have hP : ∀ t ∈ Icc x (x + ε), _ := fun t ht => hu ⟨ht.1, by linarith [ht.2]⟩
  -- on `[x, x + ε]` both trajectories solve `γ' = h (γ)`
  have hsol : ∀ (γ : ℝ → ℂ) (T : ℝ), fx_p2_htrajP φ γ T → x + ε < T →
      (∀ t ∈ Icc x (x + ε), γ t ∈ U ∧ ‖derivWithin γ (Icc 0 T) t - derivWithin γ₁ (Icc 0 T₁) x‖ <
        ‖derivWithin γ₁ (Icc 0 T₁) x‖ / 2 ∧
        ‖h (γ t) - derivWithin γ₁ (Icc 0 T₁) x‖ < ‖derivWithin γ₁ (Icc 0 T₁) x‖ / 2) →
      ∀ t ∈ Ico x (x + ε), HasDerivWithinAt γ (h (γ t)) (Ici t) t := by
    intro γ T hγ hT hPγ t ht
    have htI : t ∈ Icc 0 T := ⟨hx0.trans ht.1, by linarith [ht.2]⟩
    obtain ⟨hU', hd', hh'⟩ := hPγ t (Ico_subset_Icc_self ht)
    have heq : derivWithin γ (Icc 0 T) t = h (γ t) :=
      fx_p2_sign_eq (hγ.2.2.1 t htI).2 (hγ.2.2.2 t htI) (hUeq _ hU') hd' hh'
    rw [← heq]
    exact (fx_p2_hasDerivWithinAt_of_contDiffOn hγ.2.1 t htI).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ⟨hx0.trans ht.1, by linarith [ht.2]⟩)
  have hs₁ := hsol γ₁ T₁ h₁ hT1 (fun t ht => (hP t ht).1)
  have hs₂ := hsol γ₂ T₂ h₂ hT2 (fun t ht => (hP t ht).2)
  have := ODE_solution_unique_of_mem_Icc_right (v := fun _ => h) (s := fun _ => U) (K := K)
    (fun _ _ => hK) (h₁.2.1.continuousOn.mono (Icc_subset_Icc hx0 hT1.le)) hs₁
    (fun t ht => (hP t (Ico_subset_Icc_self ht)).1.1)
    (h₂.2.1.continuousOn.mono (Icc_subset_Icc hx0 hT2.le)) hs₂
    (fun t ht => (hP t (Ico_subset_Icc_self ht)).2.1) hxe
  exact fun t ht => this ht

/-- **Uniqueness of trajectories** (helper form of `fx_htraj_unique`). -/
theorem fx_p2_htrajP_unique {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {γ₁ γ₂ : ℝ → ℂ}
    {T₁ T₂ : ℝ} (h₁ : fx_p2_htrajP φ γ₁ T₁) (h₂ : fx_p2_htrajP φ γ₂ T₂) (h0 : γ₁ 0 = γ₂ 0)
    (hd : derivWithin γ₁ (Icc 0 T₁) 0 = derivWithin γ₂ (Icc 0 T₂) 0) :
    ∀ t ∈ Icc 0 (min T₁ T₂), γ₁ t = γ₂ t := by
  set m := min T₁ T₂ with hm
  have hm1 : m ≤ T₁ := min_le_left _ _
  have hm2 : m ≤ T₂ := min_le_right _ _
  have hm0 : 0 < m := lt_min h₁.1 h₂.1
  set s : Set ℝ := {t | γ₁ t = γ₂ t ∧ derivWithin γ₁ (Icc 0 T₁) t = derivWithin γ₂ (Icc 0 T₂) t}
    with hs
  have hcl : IsClosed (s ∩ Icc 0 m) := by
    have hF : ContinuousOn (fun t => (γ₁ t - γ₂ t, derivWithin γ₁ (Icc 0 T₁) t -
        derivWithin γ₂ (Icc 0 T₂) t)) (Icc 0 m) := by
      have c1 := h₁.2.1.continuousOn.mono (Icc_subset_Icc_right hm1)
      have c2 := h₂.2.1.continuousOn.mono (Icc_subset_Icc_right hm2)
      have d1 := (h₁.2.1.continuousOn_derivWithin (uniqueDiffOn_Icc h₁.1) le_rfl).mono
        (Icc_subset_Icc_right hm1)
      have d2 := (h₂.2.1.continuousOn_derivWithin (uniqueDiffOn_Icc h₂.1) le_rfl).mono
        (Icc_subset_Icc_right hm2)
      exact (c1.sub c2).prodMk (d1.sub d2)
    have := hF.preimage_isClosed_of_isClosed isClosed_Icc
      (isClosed_singleton (x := ((0 : ℂ), (0 : ℂ))))
    convert this using 1
    ext t
    simp only [hs, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff, Prod.mk.injEq,
      sub_eq_zero]
    tauto
  have hsub := IsClosed.Icc_subset_of_forall_mem_nhdsWithin hcl ⟨h0, hd⟩ (by
    rintro x ⟨⟨hxe, hxd⟩, hx0, hxm⟩
    obtain ⟨ε, hε0, hT1, hT2, heq⟩ := fx_p2_htrajP_unique_local hφ h₁ h₂ hx0
      (lt_of_lt_of_le hxm hm1) (lt_of_lt_of_le hxm hm2) hxe hxd
    refine mem_of_superset (Ioo_mem_nhdsGT (show x < x + ε by linarith)) ?_
    intro t ht
    refine ⟨heq t ⟨ht.1.le, ht.2.le⟩, ?_⟩
    have ht0 : 0 < t := lt_of_le_of_lt hx0 ht.1
    have hn1 : Icc 0 T₁ ∈ 𝓝 t := Icc_mem_nhds ht0 (by linarith [ht.2])
    have hn2 : Icc 0 T₂ ∈ 𝓝 t := Icc_mem_nhds ht0 (by linarith [ht.2])
    rw [derivWithin_of_mem_nhds hn1, derivWithin_of_mem_nhds hn2]
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact heq r ⟨hr.1.le, hr.2.le⟩)
  exact fun t ht => (hsub ht).1

/-- Concatenation of two trajectories with matching end point and velocity. -/
theorem fx_p2_htrajP_concat {φ : ℂ → ℂ} {γ₁ γ₂ : ℝ → ℂ} {T₁ T₂ : ℝ} (h₁ : fx_p2_htrajP φ γ₁ T₁)
    (h₂ : fx_p2_htrajP φ γ₂ T₂) (he : γ₁ T₁ = γ₂ 0)
    (hd : derivWithin γ₁ (Icc 0 T₁) T₁ = derivWithin γ₂ (Icc 0 T₂) 0) :
    fx_p2_htrajP φ (fun t => if t ≤ T₁ then γ₁ t else γ₂ (t - T₁)) (T₁ + T₂) := by
  set γ : ℝ → ℂ := fun t => if t ≤ T₁ then γ₁ t else γ₂ (t - T₁) with hγ
  set D : ℝ → ℂ := fun t => if t ≤ T₁ then derivWithin γ₁ (Icc 0 T₁) t else
    derivWithin γ₂ (Icc 0 T₂) (t - T₁) with hD
  have hT₁ := h₁.1
  have hT₂ := h₂.1
  have hDR : ∀ t ∈ Icc T₁ (T₁ + T₂), D t = derivWithin γ₂ (Icc 0 T₂) (t - T₁) := by
    intro t ht
    by_cases h : t ≤ T₁
    · have : t = T₁ := le_antisymm h ht.1
      simp only [hD, ite_eq_left h]
      rw [this, sub_self, ← hd]
    · simp only [hD, ite_eq_right h]
  have hγR : ∀ t ∈ Icc T₁ (T₁ + T₂), γ t = γ₂ (t - T₁) := by
    intro t ht
    by_cases h : t ≤ T₁
    · have : t = T₁ := le_antisymm h ht.1
      simp only [hγ, ite_eq_left h]
      rw [this, sub_self, he]
    · simp only [hγ, ite_eq_right h]
  have hL : ∀ t ∈ Icc 0 T₁, HasDerivWithinAt γ (D t) (Icc 0 T₁) t := by
    intro t ht
    have := fx_p2_hasDerivWithinAt_of_contDiffOn h₁.2.1 t ht
    rw [show D t = derivWithin γ₁ (Icc 0 T₁) t from ite_eq_left ht.2]
    exact this.congr (fun x hx => ite_eq_left hx.2) (ite_eq_left ht.2)
  have hR : ∀ t ∈ Icc T₁ (T₁ + T₂), HasDerivWithinAt γ (D t) (Icc T₁ (T₁ + T₂)) t := by
    intro t ht
    have hmap : ∀ τ ∈ Icc T₁ (T₁ + T₂), (-T₁) + 1 * τ ∈ Icc 0 T₂ :=
      fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    have := fx_p2_hasDerivWithinAt_affine (fx_p2_hasDerivWithinAt_of_contDiffOn h₂.2.1) hmap ht
    simp only [one_mul, Complex.ofReal_one, neg_add_eq_sub] at this
    rw [hDR t ht]
    exact this.congr (fun x hx => hγR x hx) (hγR t ht)
  have hall : ∀ t ∈ Icc 0 (T₁ + T₂), HasDerivWithinAt γ (D t) (Icc 0 (T₁ + T₂)) t := by
    intro t ht
    rcases lt_trichotomy t T₁ with h | h | h
    · refine (hL t ⟨ht.1, h.le⟩).mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin.2 ⟨Iio T₁, isOpen_Iio, h, fun x hx => ⟨hx.2.1, le_of_lt hx.1⟩⟩
    · subst h
      have := (hL t ⟨ht.1, le_rfl⟩).union (hR t ⟨le_rfl, by linarith⟩)
      rwa [Icc_union_Icc_eq_Icc ht.1 (by linarith)] at this
    · refine (hR t ⟨h.le, ht.2⟩).mono_of_mem_nhdsWithin ?_
      exact mem_nhdsWithin.2 ⟨Ioi T₁, isOpen_Ioi, h, fun x hx => ⟨le_of_lt hx.1, hx.2.2⟩⟩
  have hT : 0 < T₁ + T₂ := by linarith
  have hder : ∀ t ∈ Icc 0 (T₁ + T₂), derivWithin γ (Icc 0 (T₁ + T₂)) t = D t :=
    fun t ht => (hall t ht).derivWithin (uniqueDiffOn_Icc hT t ht)
  have hDc : ContinuousOn D (Icc 0 (T₁ + T₂)) := by
    have c1 : ContinuousOn D (Icc 0 T₁) :=
      (h₁.2.1.continuousOn_derivWithin (uniqueDiffOn_Icc hT₁) le_rfl).congr
        (fun x hx => ite_eq_left hx.2)
    have c2 : ContinuousOn D (Icc T₁ (T₁ + T₂)) := by
      have hc := (h₂.2.1.continuousOn_derivWithin (uniqueDiffOn_Icc hT₂) le_rfl).comp
        (continuousOn_id.sub continuousOn_const)
        (fun x (hx : x ∈ Icc T₁ (T₁ + T₂)) => (⟨by linarith [hx.1], by linarith [hx.2]⟩ :
          x - T₁ ∈ Icc 0 T₂))
      exact hc.congr (fun x hx => hDR x hx)
    have := c1.union_of_isClosed c2 isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc hT₁.le (by linarith)] at this
  refine ⟨hT, ?_, ?_, ?_⟩
  · rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hT)]
    refine ⟨fun t ht => (hall t ht).differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact hDc.congr hder
  · intro t ht
    by_cases h : t ≤ T₁
    · simp only [hγ, ite_eq_left h]
      exact h₁.2.2.1 t ⟨ht.1, h⟩
    · simp only [hγ, ite_eq_right h]
      exact h₂.2.2.1 (t - T₁) ⟨by linarith, by linarith [ht.2]⟩
  · intro t ht
    rw [hder t ht]
    by_cases h : t ≤ T₁
    · simp only [hγ, hD, ite_eq_left h]
      exact h₁.2.2.2 t ⟨ht.1, h⟩
    · simp only [hγ, hD, ite_eq_right h]
      exact h₂.2.2.2 (t - T₁) ⟨by linarith, by linarith [ht.2]⟩

/-- Leaves are transitive (helper form of `fx_leaf_trans`). -/
theorem fx_p2_leafP_trans {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {z w v : ℂ}
    (hw : w ∈ fx_p2_leafP φ z) (hv : v ∈ fx_p2_leafP φ w) : v ∈ fx_p2_leafP φ z := by
  rcases hw with ⟨rfl, -, -⟩ | ⟨γ₁, T₁, h₁, h₁0, h₁T⟩
  · exact hv
  rcases hv with ⟨rfl, -, -⟩ | ⟨γ₂, T₂, h₂, h₂0, h₂T⟩
  · exact Or.inr ⟨γ₁, T₁, h₁, h₁0, h₁T⟩
  have hT1 : T₁ ∈ Icc 0 T₁ := ⟨h₁.1.le, le_rfl⟩
  have hz : (0 : ℝ) ∈ Icc 0 T₂ := ⟨le_rfl, h₂.1.le⟩
  have e1 := h₁.2.2.2 T₁ hT1
  have e2 := h₂.2.2.2 0 hz
  rw [h₁T] at e1
  rw [h₂0] at e2
  have hw0 : φ w ≠ 0 := by rw [← h₁T]; exact (h₁.2.2.1 T₁ hT1).2
  have hsq : derivWithin γ₁ (Icc 0 T₁) T₁ ^ 2 = derivWithin γ₂ (Icc 0 T₂) 0 ^ 2 :=
    mul_left_cancel₀ hw0 (e1.trans e2.symm)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hd | hd
  · -- same direction: concatenate
    refine Or.inr ⟨_, T₁ + T₂, fx_p2_htrajP_concat h₁ h₂ (h₁T.trans h₂0.symm) hd, ?_, ?_⟩
    · simp only [ite_eq_left h₁.1.le, h₁0]
    · simp only [ite_eq_right (show ¬ (T₁ + T₂ ≤ T₁) by linarith [h₂.1]), add_sub_cancel_left, h₂T]
  · -- opposite direction: the second arc retraces the first
    have hmapR : ∀ τ ∈ Icc 0 T₁, T₁ + (-1) * τ ∈ Icc 0 T₁ :=
      fun τ hτ => ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    have hρ := fx_p2_htrajP_affine h₁ (by norm_num) h₁.1 hmapR
    have hρ0 : derivWithin (fun τ => γ₁ (T₁ + (-1) * τ)) (Icc 0 T₁) 0 =
        derivWithin γ₂ (Icc 0 T₂) 0 := by
      rw [fx_p2_htrajP_derivWithin_affine h₁ h₁.1 hmapR ⟨le_rfl, h₁.1.le⟩]
      simp [hd]
    have huniq := fx_p2_htrajP_unique hφ hρ h₂ (by simp [h₁T, h₂0]) hρ0
    rcases lt_trichotomy T₂ T₁ with h | h | h
    · have hv' : γ₁ (T₁ - T₂) = v := by
        have := huniq T₂ ⟨h₂.1.le, le_min h.le le_rfl⟩
        rw [← h₂T, ← this]
        ring_nf
      refine Or.inr ⟨fun τ => γ₁ (0 + 1 * τ), T₁ - T₂,
        fx_p2_htrajP_affine h₁ (by norm_num) (by linarith) ?_, by simp [h₁0], by simp [hv']⟩
      intro τ hτ
      exact ⟨by linarith [hτ.1], by linarith [hτ.2, h₂.1]⟩
    · subst h
      have := huniq T₂ ⟨h₂.1.le, le_min le_rfl le_rfl⟩
      rw [show T₂ + -1 * T₂ = 0 by ring, h₁0, h₂T] at this
      exact Or.inl ⟨this.symm, by rw [← h₁0]; exact h₁.2.2.1 0 ⟨le_rfl, h₁.1.le⟩⟩
    · have hz' : γ₂ T₁ = z := by
        have := huniq T₁ ⟨h₁.1.le, le_min le_rfl h.le⟩
        rw [← this, ← h₁0]
        ring_nf
      refine Or.inr ⟨fun τ => γ₂ (T₁ + 1 * τ), T₂ - T₁,
        fx_p2_htrajP_affine h₂ (by norm_num) (by linarith) ?_, by simp [hz'], by simp [h₂T]⟩
      intro τ hτ
      exact ⟨by linarith [hτ.1, h₁.1], by linarith [hτ.2]⟩

/-! ### Basic facts on chains -/

/-- The sides of a chain have nonzero one-sided tangents everywhere on `[0, 1]`. -/
theorem fx_p2_chain_derivWithin_ne {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) (j : Fin n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    derivWithin (side j) (Icc 0 1) t ≠ 0 := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · rw [← h0]; exact hC.tan0 j
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · rw [h1]; exact hC.tan1 j
  obtain ⟨θ, hθ⟩ := hC.straight j
  rw [derivWithin_of_mem_nhds (Icc_mem_nhds h0 h1)]
  exact (hθ t ⟨h0, h1⟩).2.1

/-- At interior points, `deriv = derivWithin (Icc 0 1)`. -/
theorem fx_p2_deriv_eq_derivWithin {c : ℝ → ℂ} {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    deriv c t = derivWithin c (Icc 0 1) t :=
  (derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)).symm

/-- The loop parametrising a chain on `[0, n]`. -/
def fx_p2_chainLoop {n : ℕ} [NeZero n] (side : Fin n → ℝ → ℂ) (x : ℝ) : ℂ :=
  side (Fin.ofNat n ⌊x⌋₊) (x - ⌊x⌋₊)

/-- On `[k, k + 1]` the loop is the `k`-th side. -/
theorem fx_p2_chainLoop_eq {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) {k : ℕ} {x : ℝ} (hx : x ∈ Icc (k : ℝ) (k + 1)) :
    fx_p2_chainLoop side x = side (Fin.ofNat n k) (x - k) := by
  rcases eq_or_lt_of_le hx.2 with h | h
  · have hfl : ⌊x⌋₊ = k + 1 := by
      rw [h]; exact_mod_cast Nat.floor_natCast (k + 1)
    have hk : Fin.ofNat n (k + 1) = Fin.ofNat n k + 1 := by
      ext; simp [Fin.val_add]
    show side (Fin.ofNat n ⌊x⌋₊) (x - ⌊x⌋₊) = _
    rw [hfl, hk, h]
    push_cast
    rw [sub_self, show (k : ℝ) + 1 - k = 1 by ring, hC.next]
  · have hfl : ⌊x⌋₊ = k := by
      rw [Nat.floor_eq_iff (by linarith [hx.1, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)])]
      exact ⟨hx.1, h⟩
    simp only [fx_p2_chainLoop, hfl]

/-- Every point of `[0, n]` lies in a piece `[k, k + 1]` with `k < n`. -/
theorem fx_p2_exists_piece {n : ℕ} [NeZero n] {x : ℝ} (hx : x ∈ Icc (0 : ℝ) n) :
    ∃ k : ℕ, k < n ∧ x ∈ Icc (k : ℝ) (k + 1) := by
  have hn : 1 ≤ n := NeZero.one_le
  by_cases h : ⌊x⌋₊ < n
  · refine ⟨⌊x⌋₊, h, Nat.floor_le hx.1, (Nat.lt_floor_add_one x).le⟩
  · push Not at h
    have hxn : (n : ℝ) ≤ x := le_trans (by exact_mod_cast h) (Nat.floor_le hx.1)
    refine ⟨n - 1, by omega, ?_, ?_⟩
    · rw [Nat.cast_sub hn]; push_cast; linarith [hx.2]
    · rw [Nat.cast_sub hn]; push_cast; linarith [hx.2]

/-- The loop is continuous on `[0, n]`. -/
theorem fx_p2_chainLoop_continuousOn {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) : ContinuousOn (fx_p2_chainLoop side) (Icc (0 : ℝ) n) := by
  have hU : (⋃ k : Fin n, Icc ((k : ℕ) : ℝ) ((k : ℕ) + 1)) = Icc (0 : ℝ) n := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨le_trans (Nat.cast_nonneg _) hk.1, le_trans hk.2 ?_⟩
      have : (k : ℕ) + 1 ≤ n := k.isLt
      exact_mod_cast this
    · intro hx
      obtain ⟨k, hk, hxk⟩ := fx_p2_exists_piece hx
      exact ⟨⟨k, hk⟩, hxk⟩
  rw [← hU]
  refine LocallyFinite.continuousOn_iUnion (locallyFinite_of_finite _) (fun _ => isClosed_Icc) ?_
  intro k
  have hc : ContinuousOn (fun x : ℝ => side (Fin.ofNat n (k : ℕ)) (x - (k : ℕ)))
      (Icc ((k : ℕ) : ℝ) ((k : ℕ) + 1)) :=
    (hC.smooth _).continuousOn.comp (continuousOn_id.sub continuousOn_const)
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  exact hc.congr (fun x hx => fx_p2_chainLoop_eq hC hx)

/-- The loop is injective on `[0, n)`. -/
theorem fx_p2_chainLoop_injOn {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) : InjOn (fx_p2_chainLoop side) (Ico 0 n) := by
  intro x hx y hy hxy
  have hkx : ⌊x⌋₊ < n := (Nat.floor_lt hx.1).2 hx.2
  have hky : ⌊y⌋₊ < n := (Nat.floor_lt hy.1).2 hy.2
  have h1 : x - ⌊x⌋₊ ∈ Ico (0 : ℝ) 1 :=
    ⟨by linarith [Nat.floor_le hx.1], by linarith [Nat.lt_floor_add_one x]⟩
  have h2 : y - ⌊y⌋₊ ∈ Ico (0 : ℝ) 1 :=
    ⟨by linarith [Nat.floor_le hy.1], by linarith [Nat.lt_floor_add_one y]⟩
  obtain ⟨hk, hs⟩ := hC.simple _ _ _ h1 _ h2 hxy
  have hk' : ⌊x⌋₊ = ⌊y⌋₊ := by
    have := congrArg Fin.val hk
    simp only [Fin.val_ofNat] at this
    rwa [Nat.mod_eq_of_lt hkx, Nat.mod_eq_of_lt hky] at this
  rw [hk'] at hs
  linarith

/-- The image of the loop is the trace of the chain. -/
theorem fx_p2_chainLoop_image {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) : fx_p2_chainLoop side '' Icc 0 n = ⋃ j, side j '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨k, -, hxk⟩ := fx_p2_exists_piece hx
    rw [fx_p2_chainLoop_eq hC hxk]
    exact mem_iUnion.2 ⟨Fin.ofNat n k, x - k, ⟨by linarith [hxk.1], by linarith [hxk.2]⟩, rfl⟩
  · intro hz
    obtain ⟨j, t, ht, rfl⟩ := mem_iUnion.1 hz
    have hj : (j : ℕ) + 1 ≤ n := j.isLt
    have hj' : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hj
    refine ⟨(j : ℕ) + t, ⟨by linarith [ht.1, (Nat.cast_nonneg (j : ℕ) : (0 : ℝ) ≤ _)],
      by linarith [ht.2]⟩, ?_⟩
    rw [fx_p2_chainLoop_eq hC (k := (j : ℕ)) ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    simp

/-- A chain traces a Jordan curve. -/
theorem fx_p2_chain_jordan {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) : IsJordanCurve (toExt (⋃ j, side j '' Icc (0 : ℝ) 1)) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (NeZero.pos n)
  set F : ℝ → ℂ := fun t => fx_p2_chainLoop side (n * t) with hF
  have hcont : ContinuousOn F (Icc 0 1) :=
    (fx_p2_chainLoop_continuousOn hC).comp (continuousOn_const.mul continuousOn_id)
      (fun t ht => ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩)
  have hinj : InjOn F (Ico 0 1) := by
    intro s hs t ht hst
    have := fx_p2_chainLoop_injOn hC ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
      ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩ hst
    exact mul_left_cancel₀ hn.ne' this
  have h01 : F 0 = F 1 := by
    simp only [hF, mul_zero, mul_one]
    have e1 := fx_p2_chainLoop_eq hC (k := 0) (x := 0) ⟨by simp, by simp⟩
    have e2 := fx_p2_chainLoop_eq hC (k := n - 1) (x := n)
      ⟨by rw [Nat.cast_sub NeZero.one_le]; simp, by rw [Nat.cast_sub NeZero.one_le]; simp⟩
    rw [e1, e2, Nat.cast_sub NeZero.one_le]
    simp only [Nat.cast_one, sub_sub_cancel]
    rw [hC.next, Nat.cast_zero, sub_zero]
    congr 1
    ext
    simp only [Fin.val_add, Fin.val_ofNat, Fin.val_one']
    rw [← Nat.add_mod, Nat.sub_add_cancel NeZero.one_le, Nat.mod_self]
    simp
  have h := isJordanCurve_of_loop hcont hinj h01
  have himg : F '' Icc 0 1 = ⋃ j, side j '' Icc (0 : ℝ) 1 := by
    rw [show F = fx_p2_chainLoop side ∘ (fun t => (n : ℝ) * t) from rfl, image_comp,
      image_mul_left_Icc hn.le zero_le_one, mul_zero, mul_one]
    exact fx_p2_chainLoop_image hC
  rwa [himg] at h

/-- **The Jordan domain bounded by a chain** (vendored JCT via `JordanBridge` /
`CaratheodoryJordan`): its frontier is the trace, and its closure lies in `Δ`. -/
theorem fx_p2_chain_jct {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) :
    ∃ A B : Set ℂ, IsOpen A ∧ IsOpen B ∧ Disjoint A B ∧
      Disjoint A (⋃ j, side j '' Icc (0 : ℝ) 1) ∧ Disjoint B (⋃ j, side j '' Icc (0 : ℝ) 1) ∧
      A ∪ B ∪ (⋃ j, side j '' Icc (0 : ℝ) 1) = univ ∧
      frontier A = (⋃ j, side j '' Icc (0 : ℝ) 1) ∧ IsJordanDomain A ∧ closure A ⊆ unitDisc := by
  set C := ⋃ j, side j '' Icc (0 : ℝ) 1 with hCdef
  have hJ := fx_p2_chain_jordan hC
  obtain ⟨A, B, hAo, hBo, hAc, hBc, hAB, hAC, hBC, huniv, hAb, -⟩ :=
    jordan_curve_theorem_complex_bounded hJ
  obtain ⟨hfrA, -⟩ :=
    frontier_pieces_eq_of_jordan_curve_theorem_complex hJ hAo hBo hAc hBc hAB hAC hBC huniv
  have hCc : IsCompact C :=
    isCompact_iUnion fun j => isCompact_Icc.image_of_continuousOn (hC.smooth j).continuousOn
  have hCne : C.Nonempty := ⟨side 0 0, mem_iUnion.2 ⟨0, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩
  obtain ⟨z₀, hz₀, hmax⟩ := hCc.exists_isMaxOn hCne continuous_norm.continuousOn
  have hr1 : ‖z₀‖ < 1 := by
    obtain ⟨j, hj⟩ := mem_iUnion.1 hz₀
    have := hC.mem j hj
    simpa [unitDisc] using this
  have hCr : ∀ z ∈ C, ‖z‖ ≤ ‖z₀‖ := fun z hz => hmax hz
  set E := {z : ℂ | ‖z₀‖ < ‖z‖} with hEdef
  have hEne : E.Nonempty := ⟨((‖z₀‖ + 1 : ℝ) : ℂ), by
    simp only [hEdef, mem_ofPred_eq, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    linarith⟩
  have hEunb : ¬ Bornology.IsBounded E := by
    intro hEb
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hEb
    have hmem : ((max R ‖z₀‖ + 1 : ℝ) : ℂ) ∈ E := by
      simp only [hEdef, mem_ofPred_eq, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      linarith [le_max_right R ‖z₀‖]
    have := mem_closedBall_zero_iff.1 (hR hmem)
    simp only [Complex.norm_real, Real.norm_eq_abs] at this
    rw [abs_of_nonneg (by positivity)] at this
    linarith [le_max_left R ‖z₀‖]
  have hEC : Disjoint E C := by
    rw [Set.disjoint_left]
    intro z hzE hzC
    have := hCr z hzC
    simp only [hEdef, mem_ofPred_eq] at hzE
    linarith
  have hE : E ⊆ B := subset_unbounded_piece_of_isConnected_not_isBounded hAo hBo hAB hAC hBC huniv
    hAb ⟨hEne, isPreconnected_setOf_lt_norm (norm_nonneg _)⟩ hEunb hEC
  have hAr : A ⊆ closedBall 0 ‖z₀‖ := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    by_contra h
    push Not at h
    exact Set.disjoint_left.1 hAB hz (hE h)
  have hcl : closure A ⊆ unitDisc :=
    (closure_minimal hAr isClosed_closedBall).trans (closedBall_subset_ball hr1)
  refine ⟨A, B, hAo, hBo, hAB, hAC, hBC, huniv, hfrA, ⟨hAo, hAc, ?_⟩, hcl⟩
  rw [frontier_toExt_of_isBounded' hAb hAo, hfrA]
  exact hJ

/-- **Far part of a chain.**  If every parameter of the point `p` on the chain lies in the open
set `O k`, then parameters of chain points close to `p` lie in `O k` too. -/
theorem fx_p2_chain_far {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) (O : Fin n → Set ℝ) (hO : ∀ k, IsOpen (O k)) (p : ℂ)
    (hp : ∀ k, ∀ s ∈ Icc (0 : ℝ) 1, side k s = p → s ∈ O k) :
    ∃ ρ > 0, ∀ k, ∀ s ∈ Icc (0 : ℝ) 1, ‖side k s - p‖ < ρ → s ∈ O k := by
  set Far := ⋃ k, side k '' (Icc (0 : ℝ) 1 \ O k) with hFar
  have hc : IsCompact Far := isCompact_iUnion fun k =>
    (isCompact_Icc.diff (hO k)).image_of_continuousOn
      ((hC.smooth k).continuousOn.mono sdiff_subset)
  have hpF : p ∉ Far := by
    intro h
    obtain ⟨k, s, ⟨hs, hsO⟩, hks⟩ := mem_iUnion.1 h
    exact hsO (hp k s hs hks)
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hc.isClosed.isOpen_compl p hpF
  refine ⟨ρ, hρ, fun k s hs hks => ?_⟩
  by_contra hsO
  exact hball (mem_ball.2 (by rwa [dist_eq_norm])) (mem_iUnion.2 ⟨k, s, ⟨hs, hsO⟩, rfl⟩)

/-- `|x| + |y| ≤ 2 ‖x + y i‖`. -/
theorem fx_p2_abs_add_abs_le {z : ℂ} : |z.re| + |z.im| ≤ 2 * ‖z‖ := by
  linarith [Complex.abs_re_le_norm z, Complex.abs_im_le_norm z]

/-- **The tube lemma.**  Along a `C¹` arc whose tangent stays within `‖u‖/4` of `u ≠ 0`, the
points `c t + ε w` with `ε ≠ 0` real and `w` within `‖u‖/4` of the normal `i u` are off the arc. -/
theorem fx_p2_tube_ne {c c' : ℝ → ℂ} {a b : ℝ}
    (hc : ∀ x ∈ Icc a b, HasDerivWithinAt c (c' x) (Icc a b) x) {u : ℂ} (hu : u ≠ 0)
    (hcu : ∀ x ∈ Icc a b, ‖c' x - u‖ ≤ ‖u‖ / 4) {s t : ℝ} (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) {ε : ℝ} (hε : ε ≠ 0) {w : ℂ} (hw : ‖w - I * u‖ ≤ ‖u‖ / 4) :
    c s ≠ c t + ε * w := by
  intro heq
  set g : ℝ → ℂ := fun x => c x - (x : ℂ) * u with hg
  have hgd : ∀ x ∈ Icc a b, HasDerivWithinAt g (c' x - u) (Icc a b) x := by
    intro x hx
    have h1 : HasDerivWithinAt (fun x : ℝ => (x : ℂ) * u) u (Icc a b) x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const u).hasDerivWithinAt
    exact (hc x hx).sub h1
  have hmv := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hgd hcu ht hs
  -- g s - g t = ε w - (s - t) u
  have hgst : g s - g t = (ε : ℂ) * w - ((s - t : ℝ) : ℂ) * u := by
    simp only [hg]; rw [heq]; push_cast; ring
  rw [hgst, Real.norm_eq_abs] at hmv
  set z : ℂ := (ε : ℂ) * I - ((s - t : ℝ) : ℂ) with hz
  have hkey : z * u = ((ε : ℂ) * w - ((s - t : ℝ) : ℂ) * u) - (ε : ℂ) * (w - I * u) := by
    simp only [hz]; ring
  have h1 : ‖z‖ * ‖u‖ ≤ ‖u‖ / 4 * |s - t| + |ε| * (‖u‖ / 4) := by
    rw [← norm_mul, hkey]
    refine (norm_sub_le _ _).trans (add_le_add hmv ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hw (abs_nonneg _)
  have h2 : |s - t| + |ε| ≤ 2 * ‖z‖ := by
    have := fx_p2_abs_add_abs_le (z := z)
    have hre : z.re = -(s - t) := by simp [hz]
    have him : z.im = ε := by simp [hz]
    rw [hre, him, abs_neg] at this
    exact this
  have hu0 : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hε0 : 0 < |ε| := abs_pos.2 hε
  nlinarith [abs_nonneg (s - t)]

/-- Positivity of a side at `t`: the left normal points `side j t + ε i side'` lie in `A` for all
small `ε > 0` (the `PhiPolygon.positive` condition). -/
def fx_p2_PosAt {n : ℕ} (A : Set ℂ) (side : Fin n → ℝ → ℂ) (j : Fin n) (t : ℝ) : Prop :=
  ∀ᶠ ε : ℝ in 𝓝[>] 0, side j t + (ε : ℂ) * I * deriv (side j) t ∈ A

/-- A preconnected set off the trace lies in one of the two JCT pieces. -/
theorem fx_p2_sub_or_sub {A B C S : Set ℂ} (hAo : IsOpen A) (hBo : IsOpen B) (hAB : Disjoint A B)
    (huniv : A ∪ B ∪ C = univ) (hS : IsPreconnected S) (hSC : ∀ z ∈ S, z ∉ C) :
    S ⊆ A ∨ S ⊆ B := by
  refine hS.subset_or_subset hAo hBo hAB fun z hz => ?_
  have : z ∈ A ∪ B ∪ C := huniv ▸ mem_univ z
  rcases this with h | h
  · exact h
  · exact absurd h (hSC z hz)

/-- A chain point with an interior parameter has a unique parameter. -/
theorem fx_p2_chain_eq_interior {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) {k j : Fin n} {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Ioo (0 : ℝ) 1) (h : side k s = side j t) : k = j ∧ s = t := by
  rcases eq_or_lt_of_le hs.2 with h1 | h1
  · rw [h1, hC.next] at h
    have := hC.simple _ _ 0 ⟨le_rfl, zero_lt_one⟩ t ⟨ht.1.le, ht.2⟩ h
    exact absurd this.2.symm ht.1.ne'
  · exact hC.simple _ _ s ⟨hs.1, h1⟩ t ⟨ht.1.le, ht.2⟩ h

/-- The parameters of a chain point near a smooth point `side j t₀` are near `(j, t₀)`. -/
theorem fx_p2_chain_far_interior {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) (j : Fin n) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ ρ > 0, ∀ k, ∀ s ∈ Icc (0 : ℝ) 1, ‖side k s - side j t₀‖ < ρ →
      k = j ∧ s ∈ Ioo (t₀ - δ) (t₀ + δ) := by
  classical
  obtain ⟨ρ, hρ, h⟩ := fx_p2_chain_far hC (fun k => if k = j then Ioo (t₀ - δ) (t₀ + δ) else ∅)
    (fun k => by split_ifs <;> [exact isOpen_Ioo; exact isOpen_empty]) (side j t₀) (by
      intro k s hs hks
      obtain ⟨rfl, rfl⟩ := fx_p2_chain_eq_interior hC hs ht₀ hks
      simp only [ite_true]
      exact ⟨by linarith, by linarith⟩)
  refine ⟨ρ, hρ, fun k s hs hks => ?_⟩
  have := h k s hs hks
  by_cases hk : k = j
  · subst hk
    simp only [ite_true] at this
    exact ⟨rfl, this⟩
  · simp only [hk, ite_false] at this
    exact this.elim

/-- **Positivity is locally constant along a side** (the tube lemma). -/
theorem fx_p2_chain_pos_local {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) {A B : Set ℂ} (hAo : IsOpen A) (hBo : IsOpen B) (hAB : Disjoint A B)
    (huniv : A ∪ B ∪ (⋃ j, side j '' Icc (0 : ℝ) 1) = univ) (j : Fin n) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ δ > 0, ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), (fx_p2_PosAt A side j t ↔ fx_p2_PosAt A side j t₀) := by
  set d := derivWithin (side j) (Icc 0 1) with hd
  set u := d t₀ with hu
  have hu0 : u ≠ 0 := fx_p2_chain_derivWithin_ne hC j ⟨ht₀.1.le, ht₀.2.le⟩
  have hunorm : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hdc : ContinuousOn d (Icc 0 1) :=
    (hC.smooth j).continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
  have hdat : ContinuousAt d t₀ := hdc.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hsat : ContinuousAt (side j) t₀ :=
    (hC.smooth j).continuousOn.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.continuousAt_iff.1 hdat (‖u‖ / 4) (by positivity)
  set δ₁ := min δ₀ (min t₀ (1 - t₀)) / 2 with hδ₁
  have hδ₁0 : 0 < δ₁ := by
    have : 0 < min δ₀ (min t₀ (1 - t₀)) := lt_min hδ₀ (lt_min ht₀.1 (by linarith [ht₀.2]))
    positivity
  have hδ₁a : δ₁ < δ₀ := by
    have := min_le_left δ₀ (min t₀ (1 - t₀)); linarith
  have hδ₁b : δ₁ < t₀ := by
    have := min_le_right δ₀ (min t₀ (1 - t₀)); have := min_le_left t₀ (1 - t₀); linarith
  have hδ₁c : δ₁ < 1 - t₀ := by
    have := min_le_right δ₀ (min t₀ (1 - t₀)); have := min_le_right t₀ (1 - t₀); linarith
  have hIsub : Icc (t₀ - δ₁) (t₀ + δ₁) ⊆ Icc 0 1 :=
    Icc_subset_Icc (by linarith) (by linarith)
  obtain ⟨ρ, hρ, hfar⟩ := fx_p2_chain_far_interior hC j ht₀ hδ₁0
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.continuousAt_iff.1 hsat (ρ / 2) (by positivity)
  set δ := min δ₁ δ₂ with hδ
  have hδ0 : 0 < δ := lt_min hδ₁0 hδ₂
  set ε₁ := ρ / (4 * ‖u‖) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  -- the tube
  set T := (fun p : ℝ × ℝ => side j p.1 + (p.2 : ℂ) * I * d p.1) ''
    (Ioo (t₀ - δ) (t₀ + δ) ×ˢ Ioo 0 ε₁) with hT
  have hdist : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), |t - t₀| < δ₁ ∧ |t - t₀| < δ₂ := by
    intro t ht
    have h1 : |t - t₀| < δ := abs_sub_lt_iff.2 ⟨by linarith [ht.2], by linarith [ht.1]⟩
    exact ⟨lt_of_lt_of_le h1 (min_le_left _ _), lt_of_lt_of_le h1 (min_le_right _ _)⟩
  have hdclose : ∀ x ∈ Icc (t₀ - δ₁) (t₀ + δ₁), ‖d x - u‖ ≤ ‖u‖ / 4 := by
    intro x hx
    have : dist x t₀ < δ₀ := by
      rw [Real.dist_eq]
      exact lt_of_le_of_lt (abs_sub_le_iff.2 ⟨by linarith [hx.2], by linarith [hx.1]⟩) hδ₁a
    exact (le_of_lt (by simpa [dist_eq_norm] using hδ₀' this))
  have hTC : ∀ z ∈ T, z ∉ ⋃ k, side k '' Icc (0 : ℝ) 1 := by
    rintro _ ⟨⟨t, ε⟩, ⟨ht, hε⟩, rfl⟩ hz
    obtain ⟨k, s, hs, hks⟩ := mem_iUnion.1 hz
    obtain ⟨hdt1, hdt2⟩ := hdist t ht
    have htI : t ∈ Icc (t₀ - δ₁) (t₀ + δ₁) :=
      ⟨by linarith [(abs_sub_lt_iff.1 hdt1).2], by linarith [(abs_sub_lt_iff.1 hdt1).1]⟩
    have hdt : ‖d t‖ ≤ 5 / 4 * ‖u‖ := by
      have := hdclose t htI
      calc ‖d t‖ = ‖(d t - u) + u‖ := by ring_nf
        _ ≤ ‖d t - u‖ + ‖u‖ := norm_add_le _ _
        _ ≤ 5 / 4 * ‖u‖ := by linarith
    have hclose : ‖side k s - side j t₀‖ < ρ := by
      rw [hks]
      have h1 : ‖side j t - side j t₀‖ < ρ / 2 := by
        have := hδ₂' (show dist t t₀ < δ₂ by rw [Real.dist_eq]; exact hdt2)
        rwa [dist_eq_norm] at this
      have h2 : ‖(ε : ℂ) * I * d t‖ ≤ ε₁ * (5 / 4 * ‖u‖) := by
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hε.1]
        exact mul_le_mul hε.2.le hdt (norm_nonneg _) hε₁0.le
      have h3 : ε₁ * (5 / 4 * ‖u‖) = 5 / 16 * ρ := by
        rw [hε₁]; field_simp; ring
      calc ‖side j t + (ε : ℂ) * I * d t - side j t₀‖
          = ‖(side j t - side j t₀) + (ε : ℂ) * I * d t‖ := by ring_nf
        _ ≤ ‖side j t - side j t₀‖ + ‖(ε : ℂ) * I * d t‖ := norm_add_le _ _
        _ < ρ := by linarith
    obtain ⟨rfl, hsI⟩ := hfar k s hs hclose
    have hne := fx_p2_tube_ne (c := side k) (c' := d) (a := t₀ - δ₁) (b := t₀ + δ₁)
      (fun x hx => (fx_p2_hasDerivWithinAt_of_contDiffOn (hC.smooth k) x (hIsub hx)).mono hIsub)
      hu0 hdclose ⟨hsI.1.le, hsI.2.le⟩ htI hε.1.ne' (w := I * d t) (by
        rw [← mul_sub, norm_mul, Complex.norm_I, one_mul]; exact hdclose t htI)
    apply hne
    rw [hks]
    ring
  have hTconn : IsPreconnected T := by
    refine (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ ?_
    have hc1 : ContinuousOn (fun p : ℝ × ℝ => side j p.1) (Ioo (t₀ - δ) (t₀ + δ) ×ˢ Ioo 0 ε₁) :=
      (hC.smooth j).continuousOn.comp continuous_fst.continuousOn (fun p hp =>
        hIsub ⟨by linarith [hp.1.1, min_le_left δ₁ δ₂], by linarith [hp.1.2, min_le_left δ₁ δ₂]⟩)
    have hc2 : ContinuousOn (fun p : ℝ × ℝ => d p.1) (Ioo (t₀ - δ) (t₀ + δ) ×ˢ Ioo 0 ε₁) :=
      hdc.comp continuous_fst.continuousOn (fun p hp =>
        hIsub ⟨by linarith [hp.1.1, min_le_left δ₁ δ₂], by linarith [hp.1.2, min_le_left δ₁ δ₂]⟩)
    exact hc1.add (((Complex.continuous_ofReal.comp continuous_snd).continuousOn.mul
      continuousOn_const).mul hc2)
  have hmemT : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), ∀ ε ∈ Ioo 0 ε₁,
      side j t + (ε : ℂ) * I * deriv (side j) t ∈ T := by
    intro t ht ε hε
    have htI : t ∈ Ioo (0 : ℝ) 1 := by
      have := hdist t ht
      exact ⟨by linarith [(abs_sub_lt_iff.1 this.1).2], by linarith [(abs_sub_lt_iff.1 this.1).1]⟩
    rw [fx_p2_deriv_eq_derivWithin htI]
    exact ⟨(t, ε), ⟨ht, hε⟩, rfl⟩
  have hiff : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), (fx_p2_PosAt A side j t ↔ T ⊆ A) := by
    intro t ht
    rcases fx_p2_sub_or_sub hAo hBo hAB huniv hTconn hTC with hTA | hTB
    · refine ⟨fun _ => hTA, fun _ => ?_⟩
      filter_upwards [Ioo_mem_nhdsGT hε₁0] with ε hε
      exact hTA (hmemT t ht ε hε)
    · refine ⟨fun hpos => ?_, fun hTA => ?_⟩
      · exfalso
        obtain ⟨ε, hεA, hε⟩ := (hpos.and (Ioo_mem_nhdsGT hε₁0)).exists
        exact Set.disjoint_left.1 hAB hεA (hTB (hmemT t ht ε hε))
      · exfalso
        obtain ⟨ε, hε⟩ := (show ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 ε₁ from Ioo_mem_nhdsGT hε₁0).exists
        have hz := hmemT t₀ ⟨by linarith, by linarith⟩ ε hε
        exact Set.disjoint_left.1 hAB (hTA hz) (hTB hz)
  refine ⟨δ, hδ0, fun t ht => ?_⟩
  rw [hiff t ht, hiff t₀ ⟨by linarith, by linarith⟩]

/-- **Positivity is constant along each side.** -/
theorem fx_p2_chain_pos_side {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) {A B : Set ℂ} (hAo : IsOpen A) (hBo : IsOpen B) (hAB : Disjoint A B)
    (huniv : A ∪ B ∪ (⋃ j, side j '' Icc (0 : ℝ) 1) = univ) (j : Fin n) {t t' : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1) :
    fx_p2_PosAt A side j t ↔ fx_p2_PosAt A side j t' := by
  classical
  set f : ℝ → Bool := fun t => decide (fx_p2_PosAt A side j t) with hf
  have hfc : ContinuousOn f (Ioo 0 1) := by
    intro x hx
    obtain ⟨δ, hδ, hloc⟩ := fx_p2_chain_pos_local hC hAo hBo hAB huniv j hx
    have hca : ContinuousAt f x := by
      refine (continuousAt_const (y := f x)).congr ?_
      filter_upwards [Ioo_mem_nhds (show x - δ < x by linarith) (show x < x + δ by linarith)]
        with y hy
      simp only [hf, hloc y hy]
    exact hca.continuousWithinAt
  have := isPreconnected_Ioo.constant hfc ht ht'
  simpa [hf] using this

/-- `‖w/|w| - 1‖ ≤ 2 ‖w - 1‖`. -/
theorem fx_p2_unit_close {w : ℂ} (hw : w ≠ 0) : ‖w / (‖w‖ : ℂ) - 1‖ ≤ 2 * ‖w - 1‖ := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have e : w / (‖w‖ : ℂ) - 1 = (w / (‖w‖ : ℂ) - w) + (w - 1) := by ring
  have h1 : ‖w / (‖w‖ : ℂ) - w‖ = |1 - ‖w‖| := by
    have : w / (‖w‖ : ℂ) - w = w / (‖w‖ : ℂ) * ((1 - ‖w‖ : ℝ) : ℂ) := by
      have hn' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      push_cast
      rw [mul_sub, mul_one, div_mul_cancel₀ w hn']
    rw [this, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hn, div_self hn.ne', one_mul]
  have h2 : |1 - ‖w‖| ≤ ‖w - 1‖ := by
    have := abs_norm_sub_norm_le w 1
    rw [norm_one, abs_sub_comm] at this
    exact this
  rw [e]
  calc ‖(w / (‖w‖ : ℂ) - w) + (w - 1)‖ ≤ ‖w / (‖w‖ : ℂ) - w‖ + ‖w - 1‖ := norm_add_le _ _
    _ ≤ 2 * ‖w - 1‖ := by rw [h1]; linarith

/-- **Cone separation.**  If `x₁ (1 + e₁) = x₂ wo (1 + e₂)` with `x₁, x₂ > 0`, `|wo| = 1`, then
`|wo - 1| ≤ 2|e₁| + 2|e₂|`. -/
theorem fx_p2_cone2 {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) {wo e₁ e₂ : ℂ} (hwo : ‖wo‖ = 1)
    (h₁ : 1 + e₁ ≠ 0) (h₂ : 1 + e₂ ≠ 0)
    (h : (x₁ : ℂ) * (1 + e₁) = (x₂ : ℂ) * wo * (1 + e₂)) :
    ‖wo - 1‖ ≤ 2 * ‖e₁‖ + 2 * ‖e₂‖ := by
  set w₁ := 1 + e₁
  set w₂ := 1 + e₂
  have hn₁ : 0 < ‖w₁‖ := norm_pos_iff.2 h₁
  have hn₂ : 0 < ‖w₂‖ := norm_pos_iff.2 h₂
  have hnorm : x₁ * ‖w₁‖ = x₂ * ‖w₂‖ := by
    have := congrArg norm h
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx₁, abs_of_pos hx₂,
      hwo, mul_one] at this
    exact this
  have hunit : w₁ / (‖w₁‖ : ℂ) = wo * (w₂ / (‖w₂‖ : ℂ)) := by
    have hx₁' : (x₁ : ℂ) ≠ 0 := by exact_mod_cast hx₁.ne'
    have hn₁' : ((‖w₁‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn₁.ne'
    have hn₂' : ((‖w₂‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn₂.ne'
    have hnorm' : (x₁ : ℂ) * (‖w₁‖ : ℂ) = (x₂ : ℂ) * (‖w₂‖ : ℂ) := by exact_mod_cast hnorm
    have key0 : (x₁ : ℂ) * (w₁ * (‖w₂‖ : ℂ) - wo * w₂ * (‖w₁‖ : ℂ)) = 0 := by
      linear_combination (‖w₂‖ : ℂ) * h - wo * w₂ * hnorm'
    have key : w₁ * (‖w₂‖ : ℂ) - wo * w₂ * (‖w₁‖ : ℂ) = 0 :=
      (mul_eq_zero.1 key0).resolve_left hx₁'
    field_simp
    linear_combination key
  have e1 := fx_p2_unit_close h₁
  have e2 := fx_p2_unit_close h₂
  have : wo - 1 = wo * (1 - w₂ / (‖w₂‖ : ℂ)) + (w₁ / (‖w₁‖ : ℂ) - 1) := by
    rw [hunit]; ring
  rw [this]
  calc ‖wo * (1 - w₂ / (‖w₂‖ : ℂ)) + (w₁ / (‖w₁‖ : ℂ) - 1)‖
      ≤ ‖wo * (1 - w₂ / (‖w₂‖ : ℂ))‖ + ‖w₁ / (‖w₁‖ : ℂ) - 1‖ := norm_add_le _ _
    _ = ‖w₂ / (‖w₂‖ : ℂ) - 1‖ + ‖w₁ / (‖w₁‖ : ℂ) - 1‖ := by
        rw [norm_mul, hwo, one_mul, norm_sub_rev]
    _ ≤ 2 * ‖w₂ - 1‖ + 2 * ‖w₁ - 1‖ := add_le_add e2 e1
    _ = 2 * ‖e₁‖ + 2 * ‖e₂‖ := by simp only [w₁, w₂, add_sub_cancel_left]; ring

/-- `‖e^{iα} - 1‖² = 2 - 2 cos α`. -/
theorem fx_p2_norm_exp_sub_one_sq (α : ℝ) : ‖exp ((α : ℂ) * I) - 1‖ ^ 2 = 2 - 2 * Real.cos α := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : (exp ((α : ℂ) * I) - 1).re = Real.cos α - 1 := by
    rw [sub_re, Complex.exp_ofReal_mul_I_re, one_re]
  have him : (exp ((α : ℂ) * I) - 1).im = Real.sin α := by
    rw [sub_im, Complex.exp_ofReal_mul_I_im, one_im, sub_zero]
  rw [hre, him]
  nlinarith [Real.sin_sq_add_cos_sq α]

/-- `cos α ≤ cos a` for `|α| ∈ [a, 2π - a]`. -/
theorem fx_p2_cos_le {a α : ℝ} (ha : 0 ≤ a) (hα : a ≤ |α| ∧ |α| ≤ 2 * π - a) :
    Real.cos α ≤ Real.cos a := by
  rw [← Real.cos_abs α]
  rcases le_total |α| π with h | h
  · exact Real.cos_le_cos_of_nonneg_of_le_pi ha h hα.1
  · have : Real.cos |α| = Real.cos (2 * π - |α|) := by
      rw [Real.cos_two_pi_sub]
    rw [this]
    exact Real.cos_le_cos_of_nonneg_of_le_pi ha (by linarith) (by linarith [hα.2])

/-- Near the start of a `C¹` arc with `u = c'(0) ≠ 0`, the tangent stays within `η|u|` of `u` and
`c x = c 0 + x u + O(η|u| x)`. -/
theorem fx_p2_near0 {c : ℝ → ℂ} (hc : ContDiffOn ℝ 1 c (Icc 0 1)) {η : ℝ} (hη : 0 < η)
    (hu : derivWithin c (Icc 0 1) 0 ≠ 0) :
    ∃ t₁ > 0, t₁ ≤ 1 / 2 ∧ ∀ x ∈ Icc (0 : ℝ) t₁,
      ‖derivWithin c (Icc 0 1) x - derivWithin c (Icc 0 1) 0‖ ≤
        η * ‖derivWithin c (Icc 0 1) 0‖ ∧
      ‖c x - c 0 - (x : ℂ) * derivWithin c (Icc 0 1) 0‖ ≤ η * ‖derivWithin c (Icc 0 1) 0‖ * x := by
  set d := derivWithin c (Icc 0 1) with hd
  set u := d 0
  have hun : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hdc : ContinuousOn d (Icc 0 1) :=
    hc.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1
    (hdc 0 ⟨le_rfl, zero_le_one⟩) (η * ‖u‖) (by positivity)
  set t₁ := min (δ / 2) (1 / 2) with ht₁
  have ht₁0 : 0 < t₁ := lt_min (by positivity) (by norm_num)
  have ht₁a : t₁ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht₁b : t₁ ≤ 1 / 2 := min_le_right _ _
  have hsub : Icc (0 : ℝ) t₁ ⊆ Icc 0 1 := Icc_subset_Icc le_rfl (by linarith)
  have hbound : ∀ x ∈ Icc (0 : ℝ) t₁, ‖d x - u‖ ≤ η * ‖u‖ := by
    intro x hx
    have h := hδ' (hsub hx) (show dist x 0 < δ by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]; linarith [hx.2])
    rw [dist_eq_norm] at h
    exact h.le
  refine ⟨t₁, ht₁0, ht₁b, fun x hx => ⟨hbound x hx, ?_⟩⟩
  set g : ℝ → ℂ := fun y => c y - (y : ℂ) * u with hg
  have hgd : ∀ y ∈ Icc (0 : ℝ) t₁, HasDerivWithinAt g (d y - u) (Icc 0 t₁) y := by
    intro y hy
    have h1 : HasDerivWithinAt (fun y : ℝ => (y : ℂ) * u) u (Icc 0 t₁) y := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const u).hasDerivWithinAt
    exact ((fx_p2_hasDerivWithinAt_of_contDiffOn hc y (hsub hy)).mono hsub).sub h1
  have := (convex_Icc 0 t₁).norm_image_sub_le_of_norm_hasDerivWithin_le hgd hbound
    ⟨le_rfl, ht₁0.le⟩ hx
  simp only [hg, Complex.ofReal_zero, zero_mul, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg hx.1] at this
  convert this using 2
  ring

/-- Near the end of a `C¹` arc with `v = c'(1) ≠ 0`: the mirror of `fx_p2_near0`. -/
theorem fx_p2_near1 {c : ℝ → ℂ} (hc : ContDiffOn ℝ 1 c (Icc 0 1)) {η : ℝ} (hη : 0 < η)
    (hv : derivWithin c (Icc 0 1) 1 ≠ 0) :
    ∃ t₁ > 0, t₁ ≤ 1 / 2 ∧ ∀ x ∈ Icc (1 - t₁) 1,
      ‖derivWithin c (Icc 0 1) x - derivWithin c (Icc 0 1) 1‖ ≤
        η * ‖derivWithin c (Icc 0 1) 1‖ ∧
      ‖c x - c 1 + ((1 - x : ℝ) : ℂ) * derivWithin c (Icc 0 1) 1‖ ≤
        η * ‖derivWithin c (Icc 0 1) 1‖ * (1 - x) := by
  set d := derivWithin c (Icc 0 1) with hd
  set v := d 1
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hdc : ContinuousOn d (Icc 0 1) :=
    hc.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.1
    (hdc 1 ⟨zero_le_one, le_rfl⟩) (η * ‖v‖) (by positivity)
  set t₁ := min (δ / 2) (1 / 2) with ht₁
  have ht₁0 : 0 < t₁ := lt_min (by positivity) (by norm_num)
  have ht₁a : t₁ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht₁b : t₁ ≤ 1 / 2 := min_le_right _ _
  have hsub : Icc (1 - t₁) 1 ⊆ Icc 0 1 := Icc_subset_Icc (by linarith) le_rfl
  have hbound : ∀ x ∈ Icc (1 - t₁) 1, ‖d x - v‖ ≤ η * ‖v‖ := by
    intro x hx
    have h := hδ' (hsub hx) (show dist x 1 < δ by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hx.2])]; linarith [hx.1])
    rw [dist_eq_norm] at h
    exact h.le
  refine ⟨t₁, ht₁0, ht₁b, fun x hx => ⟨hbound x hx, ?_⟩⟩
  set g : ℝ → ℂ := fun y => c y - (y : ℂ) * v with hg
  have hgd : ∀ y ∈ Icc (1 - t₁) 1, HasDerivWithinAt g (d y - v) (Icc (1 - t₁) 1) y := by
    intro y hy
    have h1 : HasDerivWithinAt (fun y : ℝ => (y : ℂ) * v) v (Icc (1 - t₁) 1) y := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const v).hasDerivWithinAt
    exact ((fx_p2_hasDerivWithinAt_of_contDiffOn hc y (hsub hy)).mono hsub).sub h1
  have := (convex_Icc (1 - t₁) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hgd hbound hx
    ⟨by linarith, le_rfl⟩
  simp only [hg, Complex.ofReal_one, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ 1 - x by linarith [hx.2])] at this
  rw [← norm_neg]
  convert this using 2
  push_cast
  ring

/-- **Normal segments.**  If a segment `c + ε i w`, `0 < ε ≤ L`, misses the trace, then positivity
at `c` is equivalent to its end point lying in `A`. -/
theorem fx_p2_seg_iff {A B C : Set ℂ} (hAo : IsOpen A) (hBo : IsOpen B) (hAB : Disjoint A B)
    (huniv : A ∪ B ∪ C = univ) {c w : ℂ} {L : ℝ} (hL : 0 < L)
    (hoff : ∀ ε ∈ Ioc (0 : ℝ) L, c + (ε : ℂ) * I * w ∉ C) :
    (∀ᶠ ε : ℝ in 𝓝[>] 0, c + (ε : ℂ) * I * w ∈ A) ↔ c + (L : ℂ) * I * w ∈ A := by
  set S := (fun ε : ℝ => c + (ε : ℂ) * I * w) '' Ioc 0 L with hS
  have hSc : IsPreconnected S :=
    isPreconnected_Ioc.image _
      (by fun_prop : Continuous fun ε : ℝ => c + (ε : ℂ) * I * w).continuousOn
  have hSC : ∀ z ∈ S, z ∉ C := by
    rintro _ ⟨ε, hε, rfl⟩
    exact hoff ε hε
  have hLmem : c + (L : ℂ) * I * w ∈ S := ⟨L, ⟨hL, le_rfl⟩, rfl⟩
  rcases fx_p2_sub_or_sub hAo hBo hAB huniv hSc hSC with hSA | hSB
  · refine ⟨fun _ => hSA hLmem, fun _ => ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hL] with ε hε
    exact hSA ⟨ε, ⟨hε.1, hε.2.le⟩, rfl⟩
  · refine ⟨fun h => ?_, fun h => absurd (hSB hLmem) (Set.disjoint_left.1 hAB h)⟩
    exfalso
    obtain ⟨ε, hεA, hε⟩ := (h.and (Ioo_mem_nhdsGT hL)).exists
    exact Set.disjoint_left.1 hAB hεA (hSB ⟨ε, ⟨hε.1, hε.2.le⟩, rfl⟩)

/-- The representative in `(0, 2π)` of a nonzero principal argument. -/
theorem fx_p2_angle_facts {a : ℝ} (ha : a ∈ Ioc (-π) π) (ha0 : a ≠ 0) :
    0 < (if 0 < a then a else a + 2 * π) ∧ (if 0 < a then a else a + 2 * π) < 2 * π ∧
      exp (((if 0 < a then a else a + 2 * π : ℝ) : ℂ) * I) = exp ((a : ℂ) * I) ∧
      ∃ k : ℤ, (if 0 < a then a else a + 2 * π) = a + 2 * k * π := by
  have hpi := Real.pi_pos
  split_ifs with h
  · exact ⟨h, by linarith [ha.2], rfl, 0, by simp⟩
  · have h' : a < 0 := lt_of_le_of_ne (not_lt.1 h) ha0
    refine ⟨by linarith [ha.1], by linarith, ?_, 1, by simp⟩
    push_cast
    rw [add_mul, Complex.exp_add, show (2 : ℂ) * π * I = 2 * π * I from rfl,
      Complex.exp_two_pi_mul_I, mul_one]

/-- `1 + e ≠ 0` for `‖e‖ < 1`. -/
theorem fx_p2_one_add_ne {e : ℂ} (he : ‖e‖ < 1) : 1 + e ≠ 0 := by
  intro h
  have : e = -1 := by linear_combination h
  rw [this, norm_neg, norm_one] at he
  exact lt_irrefl _ he

/-- **The corner sector misses the trace** (cone estimates near the vertex `V`, in the
coordinate `z = V + u ζ`). -/
theorem fx_p2_corner_sector_off {C : Set ℂ} {V u wo : ℂ} {θ a η ρf : ℝ} (hu0 : u ≠ 0)
    (hwo : wo = exp ((θ : ℂ) * I)) (ha0 : 0 < a) (hθ2 : θ < 2 * π)
    (hη : 4 * η ^ 2 < 2 - 2 * Real.cos a) (hη1 : η ≤ 1 / 8)
    (hnear : ∀ z ∈ C, ‖z - V‖ < ρf → z = V ∨
      (∃ x : ℝ, 0 < x ∧ ∃ e : ℂ, ‖e‖ ≤ η ∧ z = V + u * ((x : ℂ) * (1 + e))) ∨
      (∃ x : ℝ, 0 < x ∧ ∃ e : ℂ, ‖e‖ ≤ η ∧ z = V + u * ((x : ℂ) * wo * (1 + e)))) :
    ∀ ρ ∈ Ioo 0 (ρf / ‖u‖), ∀ α ∈ Icc a (θ - a), V + u * ((ρ : ℂ) * exp ((α : ℂ) * I)) ∉ C := by
  intro ρ hρ α hα hz
  have hun : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hzV : ‖V + u * ((ρ : ℂ) * exp ((α : ℂ) * I)) - V‖ < ρf := by
    rw [add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ.1, Complex.norm_exp_ofReal_mul_I, mul_one]
    have := hρ.2
    rw [lt_div_iff₀ hun] at this
    linarith
  have hcancel : ∀ ζ₁ ζ₂ : ℂ, V + u * ζ₁ = V + u * ζ₂ → ζ₁ = ζ₂ :=
    fun ζ₁ ζ₂ h => mul_left_cancel₀ hu0 (add_left_cancel h)
  have hcos1 : Real.cos α ≤ Real.cos a :=
    fx_p2_cos_le ha0.le ⟨by rw [abs_of_pos (by linarith [hα.1])]; exact hα.1,
      by rw [abs_of_pos (by linarith [hα.1])]; linarith [hα.2]⟩
  have hcos2 : Real.cos (α - θ) ≤ Real.cos a :=
    fx_p2_cos_le ha0.le ⟨by rw [abs_of_neg (by linarith [hα.2])]; linarith [hα.2],
      by rw [abs_of_neg (by linarith [hα.2])]; linarith [hα.1]⟩
  have hsq : ∀ β : ℝ, Real.cos β ≤ Real.cos a → ¬ ‖exp ((β : ℂ) * I) - 1‖ ≤ 2 * η := by
    intro β hβ h
    have h0 : 0 ≤ ‖exp ((β : ℂ) * I) - 1‖ := norm_nonneg _
    have h2 : ‖exp ((β : ℂ) * I) - 1‖ ^ 2 ≤ (2 * η) ^ 2 := pow_le_pow_left₀ h0 h 2
    rw [fx_p2_norm_exp_sub_one_sq β] at h2
    nlinarith
  have he1 : ∀ e : ℂ, ‖e‖ ≤ η → 1 + e ≠ 0 := fun e he => fx_p2_one_add_ne (by linarith)
  rcases hnear _ hz hzV with h | ⟨x, hx, e, he, h⟩ | ⟨x, hx, e, he, h⟩
  · have : u * ((ρ : ℂ) * exp ((α : ℂ) * I)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · exact hu0 h
    rcases mul_eq_zero.1 h with h | h
    · exact hρ.1.ne' (by exact_mod_cast h)
    · exact Complex.exp_ne_zero _ h
  · have h' := (hcancel _ _ h).symm
    have hc := fx_p2_cone2 (e₂ := 0) hx hρ.1 (Complex.norm_exp_ofReal_mul_I α) (he1 e he) (by simp)
      (by rw [h']; ring)
    simp only [norm_zero, mul_zero, add_zero] at hc
    exact hsq α hcos1 (hc.trans (by linarith))
  · have h' := (hcancel _ _ h).symm
    have hwo0 : wo ≠ 0 := by rw [hwo]; exact Complex.exp_ne_zero _
    have hwoe : exp ((α : ℂ) * I) = wo * exp (((α - θ : ℝ) : ℂ) * I) := by
      rw [hwo, ← Complex.exp_add]; congr 1; push_cast; ring
    have h'' : (x : ℂ) * (1 + e) = (ρ : ℂ) * exp (((α - θ : ℝ) : ℂ) * I) * (1 + 0) := by
      apply mul_left_cancel₀ hwo0
      rw [show wo * ((x : ℂ) * (1 + e)) = (x : ℂ) * wo * (1 + e) by ring, h', hwoe]
      ring
    have hc := fx_p2_cone2 (e₂ := 0) hx hρ.1 (Complex.norm_exp_ofReal_mul_I (α - θ)) (he1 e he)
      (by simp) h''
    simp only [norm_zero, mul_zero, add_zero] at hc
    exact hsq (α - θ) hcos2 (hc.trans (by linarith))

/-- **A normal segment near the corner misses the trace**: its points `V + u y (1 + E)` are
off the own-side part `P` (tube lemma, as a hypothesis), off `V`, and off the other side's cone
around `wo`. -/
theorem fx_p2_corner_seg_off {C P : Set ℂ} {V u wo q E : ℂ} {η ρf y : ℝ} (hu0 : u ≠ 0)
    (hwon : ‖wo‖ = 1) (hη1 : η ≤ 1 / 8)
    (hnear : ∀ z ∈ C, ‖z - V‖ < ρf → z ∈ P ∨ z = V ∨
      (∃ x : ℝ, 0 < x ∧ ∃ e : ℂ, ‖e‖ ≤ η ∧ z = V + u * ((x : ℂ) * wo * (1 + e))))
    (hqP : q ∉ P) (hy : 0 < y) (hE : ‖E‖ ≤ 1 / 4) (hsep : 2 * ‖E‖ + 2 * η < ‖wo - 1‖)
    (hq : q = V + u * ((y : ℂ) * (1 + E))) (hqV : ‖q - V‖ < ρf) : q ∉ C := by
  intro hqC
  have hE1 : 1 + E ≠ 0 := fx_p2_one_add_ne (by linarith)
  rcases hnear q hqC hqV with h | h | ⟨x, hx, e, he, h⟩
  · exact hqP h
  · rw [hq] at h
    have : u * ((y : ℂ) * (1 + E)) = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h | h
    · exact hu0 h
    rcases mul_eq_zero.1 h with h | h
    · exact hy.ne' (by exact_mod_cast h)
    · exact hE1 h
  · rw [hq] at h
    have h' := mul_left_cancel₀ hu0 (add_left_cancel h)
    have hc := fx_p2_cone2 hy hx hwon hE1 (fx_p2_one_add_ne (by linarith)) h'
    linarith

/-- The end point `V + u y W` with `arg W ≈ β` lies in the corner sector. -/
theorem fx_p2_corner_end1 {V u W : ℂ} {β θ y ρ₀ : ℝ} (hβ0 : 0 < β) (hβθ : 2 * β ≤ θ)
    (hW : |arg W - β| < β / 2) (hy : 0 < y) (hyW : y * ‖W‖ < ρ₀) :
    V + u * ((y : ℂ) * W) ∈ (fun p : ℝ × ℝ => V + u * ((p.1 : ℂ) * exp ((p.2 : ℂ) * I))) ''
      (Ioo 0 ρ₀ ×ˢ Icc (β / 2) (θ - β / 2)) := by
  have hW0 : W ≠ 0 := by
    intro h
    rw [h, arg_zero, zero_sub, abs_neg, abs_of_pos hβ0] at hW
    linarith
  refine ⟨(y * ‖W‖, arg W), ⟨⟨by have := norm_pos_iff.2 hW0; positivity, hyW⟩,
    ⟨by linarith [(abs_sub_lt_iff.1 hW).2], by linarith [(abs_sub_lt_iff.1 hW).1]⟩⟩, ?_⟩
  simp only
  push_cast
  rw [mul_assoc, Complex.norm_mul_exp_arg_mul_I]

/-- The end point `V + u y wo W` with `arg W ≈ -β`, `wo = e^{iθ}`, lies in the corner sector. -/
theorem fx_p2_corner_end2 {V u wo W : ℂ} {β θ y ρ₀ : ℝ} (hwo : wo = exp ((θ : ℂ) * I))
    (hβ0 : 0 < β) (hβθ : 2 * β ≤ θ) (hW : |arg W + β| < β / 2) (hy : 0 < y)
    (hyW : y * ‖W‖ < ρ₀) :
    V + u * ((y : ℂ) * wo * W) ∈ (fun p : ℝ × ℝ => V + u * ((p.1 : ℂ) * exp ((p.2 : ℂ) * I))) ''
      (Ioo 0 ρ₀ ×ˢ Icc (β / 2) (θ - β / 2)) := by
  have hW0 : W ≠ 0 := by
    intro h
    rw [h, arg_zero, zero_add, abs_of_pos hβ0] at hW
    linarith
  refine ⟨(y * ‖W‖, θ + arg W), ⟨⟨by have := norm_pos_iff.2 hW0; positivity, hyW⟩,
    ⟨by linarith [(abs_lt.1 hW).1], by linarith [(abs_lt.1 hW).2]⟩⟩, ?_⟩
  simp only
  rw [hwo]
  push_cast
  rw [add_mul, Complex.exp_add, show (y : ℂ) * ‖W‖ * (exp ((θ : ℂ) * I) * exp ((arg W : ℂ) * I)) =
    (y : ℂ) * exp ((θ : ℂ) * I) * ((‖W‖ : ℂ) * exp ((arg W : ℂ) * I)) by ring,
    Complex.norm_mul_exp_arg_mul_I]

/-- Representation near the start of an arc: `c x = c 0 + u x (1 + e)`, `‖e‖ ≤ η`. -/
theorem fx_p2_rep0 {c : ℝ → ℂ} {u : ℂ} {η t₁ : ℝ} (hu : u ≠ 0)
    (hb : ∀ x ∈ Icc (0 : ℝ) t₁, ‖c x - c 0 - (x : ℂ) * u‖ ≤ η * ‖u‖ * x) :
    ∀ x ∈ Ioc (0 : ℝ) t₁, ∃ e : ℂ, ‖e‖ ≤ η ∧ c x = c 0 + u * ((x : ℂ) * (1 + e)) := by
  intro x hx
  have hun : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
  refine ⟨(c x - c 0 - x * u) / (x * u), ?_, ?_⟩
  · rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1,
      div_le_iff₀ (mul_pos hx.1 hun)]
    calc ‖c x - c 0 - x * u‖ ≤ η * ‖u‖ * x := hb x ⟨hx.1.le, hx.2⟩
      _ = η * (x * ‖u‖) := by ring
  · field_simp
    ring

/-- Representation near the end of an arc: `c x = c 1 + (-v) (1 - x) (1 + e)`, `‖e‖ ≤ η`. -/
theorem fx_p2_rep1 {c : ℝ → ℂ} {v : ℂ} {η t₁ : ℝ} (hv : v ≠ 0)
    (hb : ∀ x ∈ Icc (1 - t₁) 1, ‖c x - c 1 + ((1 - x : ℝ) : ℂ) * v‖ ≤ η * ‖v‖ * (1 - x)) :
    ∀ x ∈ Ico (1 - t₁) 1, ∃ e : ℂ, ‖e‖ ≤ η ∧
      c x = c 1 + (-v) * (((1 - x : ℝ) : ℂ) * (1 + e)) := by
  intro x hx
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hx0 : ((1 - x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx1.ne'
  refine ⟨-(c x - c 1 + ((1 - x : ℝ) : ℂ) * v) / (((1 - x : ℝ) : ℂ) * v), ?_, ?_⟩
  · rw [norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx1,
      div_le_iff₀ (mul_pos hx1 hvn)]
    calc ‖c x - c 1 + ((1 - x : ℝ) : ℂ) * v‖ ≤ η * ‖v‖ * (1 - x) := hb x ⟨hx.1, hx.2.le⟩
      _ = η * ((1 - x) * ‖v‖) := by ring
  · field_simp
    ring

/-- The algebra of a normal segment in the normalised coordinate. -/
theorem fx_p2_seg_alg {V u z d e D : ℂ} {t ε : ℝ} (ht : t ≠ 0)
    (hz : z = V + u * ((t : ℂ) * (1 + e))) (hd : d = u * D) :
    z + (ε : ℂ) * I * d = V + u * ((t : ℂ) * (1 + (e + ((ε / t : ℝ) : ℂ) * I * D))) := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  subst hz hd
  push_cast
  field_simp
  ring

/-- Size of the normal-segment error `e + q i D` for `0 ≤ q ≤ κ`. -/
theorem fx_p2_seg_err {e D : ℂ} {η κ q M : ℝ} (he : ‖e‖ ≤ η) (hD : ‖D‖ ≤ M) (hq0 : 0 ≤ q)
    (hq : q ≤ κ) : ‖e + (q : ℂ) * I * D‖ ≤ η + κ * M := by
  calc ‖e + (q : ℂ) * I * D‖ ≤ ‖e‖ + ‖(q : ℂ) * I * D‖ := norm_add_le _ _
    _ = ‖e‖ + q * ‖D‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hq0]
    _ ≤ η + κ * M := add_le_add he (mul_le_mul hq hD (norm_nonneg _)
        (hq0.trans hq))

/-- **Positivity passes through a corner** (the sector argument): for suitable parameters `t`
near `0` on side `j` and `s` near `1` on side `j - 1`, the left normals are both in `A` or both
not. -/
theorem fx_p2_chain_corner {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) {A B : Set ℂ} (hAo : IsOpen A) (hBo : IsOpen B) (hAB : Disjoint A B)
    (huniv : A ∪ B ∪ (⋃ j, side j '' Icc (0 : ℝ) 1) = univ) (j : Fin n) :
    ∃ t ∈ Ioo (0 : ℝ) 1, ∃ s ∈ Ioo (0 : ℝ) 1,
      (fx_p2_PosAt A side j t ↔ fx_p2_PosAt A side (j - 1) s) := by
  classical
  have hpi := Real.pi_pos
  set C := ⋃ k, side k '' Icc (0 : ℝ) 1 with hCdef
  set dj := derivWithin (side j) (Icc 0 1) with hdj
  set dk := derivWithin (side (j - 1)) (Icc 0 1) with hdk
  set u := dj 0 with hu
  set v := dk 1 with hv
  set V := side j 0 with hV
  have hu0 : u ≠ 0 := hC.tan0 j
  have hv0 : v ≠ 0 := hC.tan1 (j - 1)
  have hun : 0 < ‖u‖ := norm_pos_iff.2 hu0
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hV1 : side (j - 1) 1 = V := by rw [hC.next, hV, sub_add_cancel]
  set r₀ := -v / u with hr₀
  have hr₀0 : r₀ ≠ 0 := div_ne_zero (neg_ne_zero.2 hv0) hu0
  have hr₀n : 0 < ‖r₀‖ := norm_pos_iff.2 hr₀0
  have hur₀ : u * r₀ = -v := by rw [hr₀]; field_simp
  have hnr₀ : ‖u‖ * ‖r₀‖ = ‖v‖ := by rw [← norm_mul, hur₀, norm_neg]
  have hcusp : arg r₀ ≠ 0 := hC.no_cusp j
  obtain ⟨hθ0, hθ2, hθexp, -⟩ := fx_p2_angle_facts (arg_mem_Ioc r₀) hcusp
  set θ := (if 0 < arg r₀ then arg r₀ else arg r₀ + 2 * π) with hθ
  set wo : ℂ := exp ((θ : ℂ) * I) with hwo
  have hwon : ‖wo‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hr₀wo : r₀ = ((‖r₀‖ : ℝ) : ℂ) * wo := by
    rw [hθexp, Complex.norm_mul_exp_arg_mul_I]
  have hvwo : -v = u * (((‖r₀‖ : ℝ) : ℂ) * wo) := by rw [← hr₀wo, hur₀]
  have hwo1 : wo ≠ 1 := by
    intro h
    rw [h, mul_one] at hr₀wo
    exact hcusp (by rw [hr₀wo]; exact Complex.arg_ofReal_of_nonneg (norm_nonneg _))
  set g := ‖wo - 1‖ with hg
  have hg0 : 0 < g := norm_pos_iff.2 (sub_ne_zero.2 hwo1)
  have hwoc : wo * conj wo = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hwon]; norm_num
  have hgc : ‖conj wo - 1‖ = g := by
    rw [hg, ← Complex.norm_conj (wo - 1), map_sub, map_one]
  -- choice of `κ` and `β = arg (1 + κ i) < θ/2`
  have hargc : ContinuousAt (fun κ : ℝ => arg (1 + (κ : ℂ) * I)) 0 := by
    have h2 : ContinuousAt arg (1 + ((0 : ℝ) : ℂ) * I) :=
      Complex.continuousAt_arg (by simp)
    exact h2.comp (f := fun κ : ℝ => 1 + (κ : ℂ) * I) (by fun_prop)
  obtain ⟨κ₀, hκ₀, hκ₀'⟩ := Metric.continuousAt_iff.1 hargc (θ / 2) (by positivity)
  set κ := min (κ₀ / 2) (min (g / 16) (1 / 16)) with hκ
  have hκ0 : 0 < κ := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have hκ1 : κ ≤ 1 / 16 := (min_le_right _ _).trans (min_le_right _ _)
  have hκg : κ ≤ g / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hκκ₀ : κ < κ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set W₀ : ℂ := 1 + (κ : ℂ) * I with hW₀
  set β := arg W₀ with hβ
  have hW₀re : W₀.re = 1 := by simp [hW₀]
  have hW₀im : W₀.im = κ := by simp [hW₀]
  have hβ0 : 0 < β := by
    refine lt_of_le_of_ne (arg_nonneg_iff.2 (by rw [hW₀im]; exact hκ0.le)) (Ne.symm ?_)
    intro h
    have := (arg_eq_zero_iff.1 h).2
    rw [hW₀im] at this
    exact hκ0.ne' this
  have hβθ : β < θ / 2 := by
    have := hκ₀' (show dist κ 0 < κ₀ by rw [Real.dist_eq, sub_zero, abs_of_pos hκ0]; exact hκκ₀)
    simp only [Complex.ofReal_zero, zero_mul, add_zero, arg_one, Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  have hβθ' : 2 * β ≤ θ := by linarith
  set a := β / 2 with ha
  have ha0 : 0 < a := by positivity
  have haπ : a ≤ π := by linarith [arg_le_pi W₀]
  have hm₁0 : 0 < 2 - 2 * Real.cos a := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl haπ ha0
    rw [Real.cos_zero] at this
    linarith
  -- continuity of `arg` at `W₀` and at `conj W₀`
  have hW₀sl : W₀ ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl (by rw [hW₀re]; norm_num))
  obtain ⟨η₁, hη₁, hη₁'⟩ := Metric.continuousAt_iff.1 (Complex.continuousAt_arg hW₀sl) (β / 2)
    (by positivity)
  set W₁ : ℂ := 1 - (κ : ℂ) * I with hW₁
  have hW₁sl : W₁ ∈ slitPlane := mem_slitPlane_iff.2 (Or.inl (by simp [hW₁]))
  have hW₁arg : arg W₁ = -β := by
    have : W₁ = conj W₀ := by
      rw [hW₁, hW₀, map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [this, arg_conj, ite_eq_right]
    rw [arg_eq_pi_iff, hW₀re]
    norm_num
  obtain ⟨η₂, hη₂, hη₂'⟩ := Metric.continuousAt_iff.1 (Complex.continuousAt_arg hW₁sl) (β / 2)
    (by positivity)
  set η := min (1 / 8) (min (g / 16) (min (η₁ / 4) (min (η₂ / 4)
    ((2 - 2 * Real.cos a) / 8)))) with hη
  have hη0 : 0 < η := by
    refine lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity)
      (lt_min (by positivity) (by positivity))))
  have hη1 : η ≤ 1 / 8 := min_le_left _ _
  have hηg : η ≤ g / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hηη₁ : η ≤ η₁ / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηη₂ : η ≤ η₂ / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hηm : η ≤ (2 - 2 * Real.cos a) / 8 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hη4 : 4 * η ^ 2 < 2 - 2 * Real.cos a := by
    have : 4 * η ^ 2 ≤ 4 * η * ((2 - 2 * Real.cos a) / 8) :=
      by rw [sq, ← mul_assoc]; exact mul_le_mul_of_nonneg_left hηm (by positivity)
    have h2 : 4 * η * ((2 - 2 * Real.cos a) / 8) ≤ (2 - 2 * Real.cos a) / 16 := by
      have := mul_le_mul_of_nonneg_right hη1 (show 0 ≤ (2 - 2 * Real.cos a) / 8 by positivity)
      linarith
    linarith
  have hsmall : η + κ * (1 + η) ≤ 1 / 4 := by
    have : κ * (1 + η) ≤ 1 / 16 * (9 / 8) := mul_le_mul hκ1 (by linarith) (by positivity)
      (by norm_num)
    linarith
  have hsep : 2 * (η + κ * (1 + η)) + 2 * η < g := by
    have : κ * (1 + η) ≤ g / 16 * (9 / 8) := mul_le_mul hκg (by linarith) (by positivity)
      (by positivity)
    linarith
  -- near the vertex
  obtain ⟨tA, htA0, htA1, hA'⟩ := fx_p2_near0 (hC.smooth j) hη0 hu0
  obtain ⟨tB, htB0, htB1, hB'⟩ := fx_p2_near1 (hC.smooth (j - 1)) hη0 hv0
  set t₁ := min tA tB with ht₁
  have ht₁0 : 0 < t₁ := lt_min htA0 htB0
  have ht₁A : t₁ ≤ tA := min_le_left _ _
  have ht₁B : t₁ ≤ tB := min_le_right _ _
  have ht₁h : t₁ ≤ 1 / 2 := ht₁A.trans htA1
  -- the far part
  obtain ⟨ρf, hρf, hfar⟩ := fx_p2_chain_far hC
    (fun k => (if k = j then Iio t₁ else ∅) ∪ (if k = j - 1 then Ioi (1 - t₁) else ∅))
    (fun k => by
      refine IsOpen.union ?_ ?_ <;> split_ifs <;> first | exact isOpen_Iio | exact isOpen_Ioi |
        exact isOpen_empty) V (by
      intro k s hs hks
      rcases eq_or_lt_of_le hs.2 with h1 | h1
      · rw [h1, hC.next] at hks
        have := (hC.simple _ _ 0 ⟨le_rfl, zero_lt_one⟩ 0 ⟨le_rfl, zero_lt_one⟩ hks).1
        have hk : k = j - 1 := eq_sub_of_add_eq this
        refine Or.inr ?_
        simp only [hk, ite_true, h1]
        exact show 1 - t₁ < 1 by linarith
      · have := hC.simple _ _ s ⟨hs.1, h1⟩ 0 ⟨le_rfl, zero_lt_one⟩ hks
        obtain ⟨rfl, rfl⟩ := this
        refine Or.inl ?_
        simp only [ite_true]
        exact ht₁0)
  have hnear : ∀ z ∈ C, ‖z - V‖ < ρf →
      (∃ x ∈ Ico (0 : ℝ) t₁, z = side j x) ∨ (∃ x ∈ Ioc (1 - t₁) 1, z = side (j - 1) x) := by
    intro z hz hzV
    obtain ⟨k, x, hx, rfl⟩ := mem_iUnion.1 hz
    have := hfar k x hx hzV
    rcases this with h | h
    · by_cases hk : k = j
      · subst hk; simp only [ite_true] at h; exact Or.inl ⟨x, ⟨hx.1, h⟩, rfl⟩
      · simp only [hk, ite_false] at h; exact h.elim
    · by_cases hk : k = j - 1
      · subst hk; simp only [ite_true] at h; exact Or.inr ⟨x, ⟨h, hx.2⟩, rfl⟩
      · simp only [hk, ite_false] at h; exact h.elim
  -- representations near the vertex
  have hRj : ∀ x ∈ Ioc (0 : ℝ) t₁, ∃ e : ℂ, ‖e‖ ≤ η ∧ side j x = V + u * ((x : ℂ) * (1 + e)) :=
    fun x hx => fx_p2_rep0 hu0 (fun y hy => (hA' y ⟨hy.1, hy.2.trans ht₁A⟩).2) x hx
  have hRk : ∀ x ∈ Ico (1 - t₁) 1, ∃ e : ℂ, ‖e‖ ≤ η ∧
      side (j - 1) x = V + (-v) * (((1 - x : ℝ) : ℂ) * (1 + e)) := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := fx_p2_rep1 (t₁ := t₁) hv0
      (fun y hy => (hB' y ⟨by linarith [hy.1], hy.2⟩).2) x ⟨by linarith [hx.1], hx.2⟩
    exact ⟨e, he, by rw [hxe, hV1]⟩
  have hRk' : ∀ x ∈ Ico (1 - t₁) 1, ∃ e : ℂ, ‖e‖ ≤ η ∧
      side (j - 1) x = V + u * ((((1 - x) * ‖r₀‖ : ℝ) : ℂ) * wo * (1 + e)) := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := hRk x hx
    refine ⟨e, he, ?_⟩
    rw [hxe, hvwo]
    push_cast
    ring
  have hRj' : ∀ x ∈ Ioc (0 : ℝ) t₁, ∃ e : ℂ, ‖e‖ ≤ η ∧
      side j x = V + (-v) * (((x / ‖r₀‖ : ℝ) : ℂ) * conj wo * (1 + e)) := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := hRj x hx
    refine ⟨e, he, ?_⟩
    rw [hxe, hvwo]
    have hr' : ((‖r₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr₀n.ne'
    push_cast
    rw [show u * ((‖r₀‖ : ℂ) * wo) * ((x : ℂ) / (‖r₀‖ : ℂ) * conj wo * (1 + e)) =
      u * ((x : ℂ) * (1 + e)) * (wo * conj wo) * ((‖r₀‖ : ℂ) / (‖r₀‖ : ℂ)) by ring, hwoc,
      div_self hr', mul_one, mul_one]
  -- the three forms of `hnear`
  have hnearS : ∀ z ∈ C, ‖z - V‖ < ρf → z = V ∨
      (∃ x : ℝ, 0 < x ∧ ∃ e : ℂ, ‖e‖ ≤ η ∧ z = V + u * ((x : ℂ) * (1 + e))) ∨
      (∃ x : ℝ, 0 < x ∧ ∃ e : ℂ, ‖e‖ ≤ η ∧ z = V + u * ((x : ℂ) * wo * (1 + e))) := by
    intro z hz hzV
    rcases hnear z hz hzV with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · rcases eq_or_lt_of_le hx.1 with hx0 | hx0
      · exact Or.inl (by rw [← hx0])
      · obtain ⟨e, he, hxe⟩ := hRj x ⟨hx0, hx.2.le⟩
        exact Or.inr (Or.inl ⟨x, hx0, e, he, hxe⟩)
    · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
      · exact Or.inl (by rw [hx1, hV1])
      · obtain ⟨e, he, hxe⟩ := hRk' x ⟨hx.1.le, hx1⟩
        exact Or.inr (Or.inr ⟨(1 - x) * ‖r₀‖, by
          have : 0 < 1 - x := by linarith
          positivity, e, he, hxe⟩)
  have hnearJ : ∀ z ∈ C, ‖z - V‖ < ρf → z ∈ side j '' Icc 0 t₁ ∨ z = V ∨
      (∃ x : ℝ, 0 < x ∧ ∃ e : ℂ, ‖e‖ ≤ η ∧ z = V + u * ((x : ℂ) * wo * (1 + e))) := by
    intro z hz hzV
    rcases hnear z hz hzV with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · exact Or.inl ⟨x, ⟨hx.1, hx.2.le⟩, rfl⟩
    · rcases eq_or_lt_of_le hx.2 with hx1 | hx1
      · exact Or.inr (Or.inl (by rw [hx1, hV1]))
      · obtain ⟨e, he, hxe⟩ := hRk' x ⟨hx.1.le, hx1⟩
        exact Or.inr (Or.inr ⟨(1 - x) * ‖r₀‖, by
          have : 0 < 1 - x := by linarith
          positivity, e, he, hxe⟩)
  have hnearK : ∀ z ∈ C, ‖z - V‖ < ρf → z ∈ side (j - 1) '' Icc (1 - t₁) 1 ∨ z = V ∨
      (∃ x : ℝ, 0 < x ∧ ∃ e : ℂ, ‖e‖ ≤ η ∧ z = V + (-v) * ((x : ℂ) * conj wo * (1 + e))) := by
    intro z hz hzV
    rcases hnear z hz hzV with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · rcases eq_or_lt_of_le hx.1 with hx0 | hx0
      · exact Or.inr (Or.inl (by rw [← hx0]))
      · obtain ⟨e, he, hxe⟩ := hRj' x ⟨hx0, hx.2.le⟩
        exact Or.inr (Or.inr ⟨x / ‖r₀‖, by positivity, e, he, hxe⟩)
    · exact Or.inl ⟨x, ⟨hx.1.le, hx.2⟩, rfl⟩
  -- parameters
  set t := min (t₁ / 2) (ρf / (4 * ‖u‖)) with ht
  set σ := min (t₁ / 2) (ρf / (4 * ‖v‖)) with hσ
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have hσ0 : 0 < σ := lt_min (by positivity) (by positivity)
  have htt₁ : t < t₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hσt₁ : σ < t₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htρ : t * ‖u‖ ≤ ρf / 4 := by
    have := min_le_right (t₁ / 2) (ρf / (4 * ‖u‖))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hσρ : σ * ‖v‖ ≤ ρf / 4 := by
    have := min_le_right (t₁ / 2) (ρf / (4 * ‖v‖))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  set s := 1 - σ with hs
  have hσs : 1 - s = σ := by rw [hs]; ring
  have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨ht0, by linarith⟩
  have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  -- the tangent errors at `t` and `s`
  set e₂j := (dj t - u) / u with he₂jdef
  set e₂k := (dk s - v) / v with he₂kdef
  have he₂j : ‖e₂j‖ ≤ η := by
    rw [he₂jdef, norm_div, div_le_iff₀ hun]
    exact (hA' t ⟨ht0.le, htt₁.le.trans ht₁A⟩).1
  have he₂k : ‖e₂k‖ ≤ η := by
    rw [he₂kdef, norm_div, div_le_iff₀ hvn]
    exact (hB' s ⟨by linarith, by linarith⟩).1
  have hdjt : dj t = u * (1 + e₂j) := by rw [he₂jdef]; field_simp; ring
  have hdks : dk s = (-v) * (-(1 + e₂k)) := by rw [he₂kdef]; field_simp; ring
  have h1e₂j : ‖1 + e₂j‖ ≤ 1 + η := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  have h1e₂k : ‖-(1 + e₂k)‖ ≤ 1 + η := by
    rw [norm_neg]; exact (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  obtain ⟨ej, hej, hsj⟩ := hRj t ⟨ht0, htt₁.le⟩
  obtain ⟨ek, hek, hsk⟩ := hRk s ⟨by linarith, by linarith⟩
  rw [hσs] at hsk
  have hNj : ∀ ε : ℝ, side j t + (ε : ℂ) * I * dj t =
      V + u * ((t : ℂ) * (1 + (ej + ((ε / t : ℝ) : ℂ) * I * (1 + e₂j)))) :=
    fun ε => fx_p2_seg_alg ht0.ne' hsj hdjt
  have hNk : ∀ ε : ℝ, side (j - 1) s + (ε : ℂ) * I * dk s =
      V + (-v) * ((σ : ℂ) * (1 + (ek + ((ε / σ : ℝ) : ℂ) * I * (-(1 + e₂k))))) :=
    fun ε => fx_p2_seg_alg hσ0.ne' hsk hdks
  -- the tube bounds for the two sides
  have hηu : η * ‖u‖ ≤ ‖u‖ / 4 := by
    have := mul_le_mul_of_nonneg_right hη1 hun.le
    linarith only [this, hun]
  have hηv : η * ‖v‖ ≤ ‖v‖ / 4 := by
    have := mul_le_mul_of_nonneg_right hη1 hvn.le
    linarith only [this, hvn]
  have htubej : ∀ ε : ℝ, ε ≠ 0 → side j t + (ε : ℂ) * I * dj t ∉ side j '' Icc 0 t₁ := by
    rintro ε hε ⟨x, hx, hxe⟩
    have hsub : Icc (0 : ℝ) t₁ ⊆ Icc 0 1 := Icc_subset_Icc le_rfl (by linarith)
    refine fx_p2_tube_ne (c := side j) (c' := dj)
      (fun y hy => (fx_p2_hasDerivWithinAt_of_contDiffOn (hC.smooth j) y (hsub hy)).mono hsub) hu0
      (fun y hy => ((hA' y ⟨hy.1, hy.2.trans ht₁A⟩).1).trans hηu) hx
      ⟨ht0.le, htt₁.le⟩ hε (w := I * dj t) ?_ (by rw [hxe]; ring)
    rw [← mul_sub, norm_mul, Complex.norm_I, one_mul]
    exact ((hA' t ⟨ht0.le, htt₁.le.trans ht₁A⟩).1).trans hηu
  have htubek : ∀ ε : ℝ, ε ≠ 0 →
      side (j - 1) s + (ε : ℂ) * I * dk s ∉ side (j - 1) '' Icc (1 - t₁) 1 := by
    rintro ε hε ⟨x, hx, hxe⟩
    have hsub : Icc (1 - t₁) 1 ⊆ Icc 0 1 := Icc_subset_Icc (by linarith) le_rfl
    refine fx_p2_tube_ne (c := side (j - 1)) (c' := dk) (t := s)
      (fun y hy => (fx_p2_hasDerivWithinAt_of_contDiffOn (hC.smooth (j - 1)) y (hsub hy)).mono hsub)
      hv0 (fun y hy => ((hB' y ⟨by linarith [hy.1], hy.2⟩).1).trans hηv) hx
      ⟨by linarith, by linarith⟩ hε (w := I * dk s) ?_ (by rw [hxe]; ring)
    rw [← mul_sub, norm_mul, Complex.norm_I, one_mul]
    exact ((hB' s ⟨by linarith, by linarith⟩).1).trans hηv
  -- (OJ) and (OK): the normal segments miss the trace
  have hOJ : ∀ ε ∈ Ioc (0 : ℝ) (κ * t), side j t + (ε : ℂ) * I * dj t ∉ C := by
    intro ε hε
    have hq0 : 0 ≤ ε / t := div_nonneg hε.1.le ht0.le
    have hqκ : ε / t ≤ κ := by rw [div_le_iff₀ ht0]; exact hε.2
    have hE := fx_p2_seg_err hej h1e₂j hq0 hqκ
    refine fx_p2_corner_seg_off hu0 hwon hη1 hnearJ (htubej ε hε.1.ne') ht0 (hE.trans hsmall)
      (by linarith) (hNj ε) ?_
    rw [hNj ε, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0]
    have h5 : ‖1 + (ej + ((ε / t : ℝ) : ℂ) * I * (1 + e₂j))‖ ≤ 5 / 4 :=
      (norm_add_le _ _).trans (by rw [norm_one]; linarith)
    calc ‖u‖ * (t * ‖1 + (ej + ((ε / t : ℝ) : ℂ) * I * (1 + e₂j))‖) ≤ ‖u‖ * (t * (5 / 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 ht0.le) hun.le
      _ < ρf := by linarith
  have hOK : ∀ ε ∈ Ioc (0 : ℝ) (κ * σ), side (j - 1) s + (ε : ℂ) * I * dk s ∉ C := by
    intro ε hε
    have hq0 : 0 ≤ ε / σ := div_nonneg hε.1.le hσ0.le
    have hqκ : ε / σ ≤ κ := by rw [div_le_iff₀ hσ0]; exact hε.2
    have hE := fx_p2_seg_err hek h1e₂k hq0 hqκ
    have hv0' : -v ≠ 0 := neg_ne_zero.2 hv0
    refine fx_p2_corner_seg_off hv0' (by rw [Complex.norm_conj, hwon]) hη1 hnearK
      (htubek ε hε.1.ne') hσ0 (hE.trans hsmall) (by rw [hgc]; linarith) (hNk ε) ?_
    rw [hNk ε, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hσ0, norm_neg]
    have h5 : ‖1 + (ek + ((ε / σ : ℝ) : ℂ) * I * (-(1 + e₂k)))‖ ≤ 5 / 4 :=
      (norm_add_le _ _).trans (by rw [norm_one]; linarith)
    calc ‖v‖ * (σ * ‖1 + (ek + ((ε / σ : ℝ) : ℂ) * I * (-(1 + e₂k)))‖) ≤ ‖v‖ * (σ * (5 / 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hσ0.le) hvn.le
      _ < ρf := by linarith
  -- the sector
  set ρ₀ := ρf / ‖u‖ with hρ₀
  set Sec := (fun p : ℝ × ℝ => V + u * ((p.1 : ℂ) * exp ((p.2 : ℂ) * I))) ''
    (Ioo 0 ρ₀ ×ˢ Icc (β / 2) (θ - β / 2)) with hSec
  have hSecc : IsPreconnected Sec :=
    (isPreconnected_Ioo.prod isPreconnected_Icc).image _ (by fun_prop : Continuous
      (fun p : ℝ × ℝ => V + u * ((p.1 : ℂ) * exp ((p.2 : ℂ) * I)))).continuousOn
  have hSecC : ∀ z ∈ Sec, z ∉ C := by
    rintro _ ⟨⟨ρ, α⟩, ⟨hρ, hα⟩, rfl⟩
    exact fx_p2_corner_sector_off hu0 rfl ha0 hθ2 hη4 hη1 hnearS ρ hρ α hα
  -- (MJ), (MK): the end points of the normal segments lie in the sector
  have hMJ : side j t + ((κ * t : ℝ) : ℂ) * I * dj t ∈ Sec := by
    have hE₀ : ‖ej + (κ : ℂ) * I * e₂j‖ ≤ 2 * η := by
      have := fx_p2_seg_err (D := e₂j) (κ := κ) (M := η) hej he₂j hκ0.le le_rfl
      have h2 := mul_le_mul_of_nonneg_right (hκ1.trans (by norm_num : (1 : ℝ) / 16 ≤ 1)) hη0.le
      linarith only [this, h2]
    have hWarg : |arg (W₀ + (ej + (κ : ℂ) * I * e₂j)) - β| < β / 2 := by
      have := hη₁' (show dist (W₀ + (ej + (κ : ℂ) * I * e₂j)) W₀ < η₁ by
        rw [dist_eq_norm, add_sub_cancel_left]; linarith)
      rwa [Real.dist_eq] at this
    have hWb : ‖W₀ + (ej + (κ : ℂ) * I * e₂j)‖ ≤ 2 := by
      have : ‖W₀‖ ≤ 1 + κ := (norm_add_le _ _).trans (by
        rw [norm_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hκ0])
      exact (norm_add_le _ _).trans (by linarith)
    have heq : side j t + ((κ * t : ℝ) : ℂ) * I * dj t =
        V + u * ((t : ℂ) * (W₀ + (ej + (κ : ℂ) * I * e₂j))) := by
      rw [hNj, hW₀]
      have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      push_cast
      field_simp
      ring
    rw [heq]
    refine fx_p2_corner_end1 hβ0 hβθ' hWarg ht0 ?_
    rw [hρ₀, lt_div_iff₀ hun]
    calc t * ‖W₀ + (ej + (κ : ℂ) * I * e₂j)‖ * ‖u‖
        = ‖W₀ + (ej + (κ : ℂ) * I * e₂j)‖ * (t * ‖u‖) := by ring
      _ ≤ 2 * (ρf / 4) := mul_le_mul hWb htρ (by positivity) (by norm_num)
      _ < ρf := by linarith only [hρf]
  have hMK : side (j - 1) s + ((κ * σ : ℝ) : ℂ) * I * dk s ∈ Sec := by
    have hE₀ : ‖ek - (κ : ℂ) * I * e₂k‖ ≤ 2 * η := by
      have := fx_p2_seg_err (e := ek) (D := -e₂k) (κ := κ) (M := η) hek
        (by rw [norm_neg]; exact he₂k)
        hκ0.le le_rfl
      rw [show ek + (κ : ℂ) * I * -e₂k = ek - (κ : ℂ) * I * e₂k by ring] at this
      have h2 := mul_le_mul_of_nonneg_right (hκ1.trans (by norm_num : (1 : ℝ) / 16 ≤ 1)) hη0.le
      linarith only [this, h2]
    have hWarg : |arg (W₁ + (ek - (κ : ℂ) * I * e₂k)) + β| < β / 2 := by
      have := hη₂' (show dist (W₁ + (ek - (κ : ℂ) * I * e₂k)) W₁ < η₂ by
        rw [dist_eq_norm, add_sub_cancel_left]; linarith)
      rwa [Real.dist_eq, hW₁arg, sub_neg_eq_add] at this
    have hWb : ‖W₁ + (ek - (κ : ℂ) * I * e₂k)‖ ≤ 2 := by
      have : ‖W₁‖ ≤ 1 + κ := (norm_sub_le _ _).trans (by
        rw [norm_one, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hκ0])
      exact (norm_add_le _ _).trans (by linarith)
    have heq : side (j - 1) s + ((κ * σ : ℝ) : ℂ) * I * dk s =
        V + u * (((σ * ‖r₀‖ : ℝ) : ℂ) * wo * (W₁ + (ek - (κ : ℂ) * I * e₂k))) := by
      rw [hNk, hvwo, hW₁]
      have hσ' : (σ : ℂ) ≠ 0 := by exact_mod_cast hσ0.ne'
      push_cast
      field_simp
      ring
    rw [heq]
    refine fx_p2_corner_end2 rfl hβ0 hβθ' hWarg (by positivity) ?_
    rw [hρ₀, lt_div_iff₀ hun]
    have h2 : σ * ‖r₀‖ * ‖W₁ + (ek - (κ : ℂ) * I * e₂k)‖ * ‖u‖ =
        (σ * ‖v‖) * ‖W₁ + (ek - (κ : ℂ) * I * e₂k)‖ := by rw [← hnr₀]; ring
    rw [h2]
    calc σ * ‖v‖ * ‖W₁ + (ek - (κ : ℂ) * I * e₂k)‖
        = ‖W₁ + (ek - (κ : ℂ) * I * e₂k)‖ * (σ * ‖v‖) := by ring
      _ ≤ 2 * (ρf / 4) := mul_le_mul hWb hσρ (by positivity) (by norm_num)
      _ < ρf := by linarith only [hρf]
  -- conclusion
  have hSegJ := fx_p2_seg_iff hAo hBo hAB huniv (c := side j t) (w := dj t) (L := κ * t)
    (by positivity) hOJ
  have hSegK := fx_p2_seg_iff hAo hBo hAB huniv (c := side (j - 1) s) (w := dk s) (L := κ * σ)
    (by positivity) hOK
  refine ⟨t, htI, s, hsI, ?_⟩
  unfold fx_p2_PosAt
  rw [fx_p2_deriv_eq_derivWithin htI, fx_p2_deriv_eq_derivWithin hsI, ← hdj, ← hdk, hSegJ, hSegK]
  rcases fx_p2_sub_or_sub hAo hBo hAB huniv hSecc hSecC with hA | hB
  · exact ⟨fun _ => hA hMK, fun _ => hA hMJ⟩
  · exact ⟨fun h => absurd (hB hMJ) (Set.disjoint_left.1 hAB h),
      fun h => absurd (hB hMK) (Set.disjoint_left.1 hAB h)⟩

/-- **Positivity is global**: positivity at one smooth point of a chain gives it at all. -/
theorem fx_p2_chain_pos_all {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) {A B : Set ℂ} (hAo : IsOpen A) (hBo : IsOpen B) (hAB : Disjoint A B)
    (huniv : A ∪ B ∪ (⋃ j, side j '' Icc (0 : ℝ) 1) = univ) {j₀ : Fin n} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hpos : fx_p2_PosAt A side j₀ t₀) :
    ∀ j, ∀ t ∈ Ioo (0 : ℝ) 1, fx_p2_PosAt A side j t := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  -- `Q j`: positivity at the midpoint of side `j`
  have hside : ∀ j, ∀ t ∈ Ioo (0 : ℝ) 1, (fx_p2_PosAt A side j t ↔ fx_p2_PosAt A side j (1 / 2)) :=
    fun j t ht => fx_p2_chain_pos_side hC hAo hBo hAB huniv j ht hhalf
  have hstep : ∀ j : Fin n,
      (fx_p2_PosAt A side (j + 1) (1 / 2) ↔ fx_p2_PosAt A side j (1 / 2)) := by
    intro j
    obtain ⟨t, ht, s, hs, h⟩ := fx_p2_chain_corner hC hAo hBo hAB huniv (j + 1)
    rw [add_sub_cancel_right] at h
    rw [← hside _ t ht, ← hside _ s hs]
    exact h
  have hind : ∀ k : ℕ, (fx_p2_PosAt A side (j₀ + Fin.ofNat n k) (1 / 2) ↔
      fx_p2_PosAt A side j₀ (1 / 2)) := by
    intro k
    induction k with
    | zero =>
      have : j₀ + Fin.ofNat n 0 = j₀ := by
        rw [add_eq_left]; ext; simp
      rw [this]
    | succ k ih =>
      have : j₀ + Fin.ofNat n (k + 1) = (j₀ + Fin.ofNat n k) + 1 := by
        rw [add_assoc]; congr 1; ext; simp [Fin.val_add]
      rw [this, hstep, ih]
  have h0 : fx_p2_PosAt A side j₀ (1 / 2) := (hside j₀ t₀ ht₀).1 hpos
  intro j t ht
  rw [hside j t ht]
  have hj : j = j₀ + Fin.ofNat n (j - j₀).val := by
    have : Fin.ofNat n (j - j₀).val = j - j₀ := by
      ext; simp
    rw [this]; abel
  rw [hj, hind]
  exact h0

/-- **Some smooth point is positive in one of the two orientations** (closest-point argument:
a point of `A` near a smooth point of the trace sees its nearest trace point along a normal). -/
theorem fx_p2_chain_exists_pos {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) {A B : Set ℂ} (hAo : IsOpen A) (hBo : IsOpen B) (hAB : Disjoint A B)
    (hAC : Disjoint A (⋃ j, side j '' Icc (0 : ℝ) 1))
    (huniv : A ∪ B ∪ (⋃ j, side j '' Icc (0 : ℝ) 1) = univ)
    (hfr : (⋃ j, side j '' Icc (0 : ℝ) 1) ⊆ closure A) :
    ∃ s ∈ Ioo (0 : ℝ) 1, fx_p2_PosAt A side 0 s ∨
      (∀ᶠ ε : ℝ in 𝓝[>] 0, side 0 s - (ε : ℂ) * I * deriv (side 0) s ∈ A) := by
  set C := ⋃ j, side j '' Icc (0 : ℝ) 1 with hCdef
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  obtain ⟨ρ, hρ, hfar⟩ := fx_p2_chain_far_interior hC 0 hhalf (δ := 1 / 4) (by norm_num)
  set p := side 0 (1 / 2) with hp
  have hpC : p ∈ C := mem_iUnion.2 ⟨0, 1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
  obtain ⟨a, haA, hpa⟩ := Metric.mem_closure_iff.1 (hfr hpC) (ρ / 2) (by positivity)
  have hCc : IsCompact C :=
    isCompact_iUnion fun j => isCompact_Icc.image_of_continuousOn (hC.smooth j).continuousOn
  obtain ⟨z, hzC, hmin⟩ := hCc.exists_isMinOn ⟨p, hpC⟩
    ((continuous_norm.comp (continuous_sub_right a)).continuousOn)
  have hmin' : ∀ w ∈ C, ‖z - a‖ ≤ ‖w - a‖ := fun w hw => hmin hw
  obtain ⟨k, s, hs, rfl⟩ := mem_iUnion.1 hzC
  have hzp : ‖side k s - p‖ < ρ := by
    have h1 := hmin' p hpC
    rw [dist_eq_norm] at hpa
    calc ‖side k s - p‖ = ‖(side k s - a) - (p - a)‖ := by ring_nf
      _ ≤ ‖side k s - a‖ + ‖p - a‖ := norm_sub_le _ _
      _ < ρ := by linarith
  obtain ⟨rfl, hs'⟩ := hfar k s hs hzp
  have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
  refine ⟨s, hsI, ?_⟩
  set Z := a - side 0 s with hZ
  have haC : a ∉ C := fun h => Set.disjoint_left.1 hAC haA h
  have hZ0 : Z ≠ 0 := by
    intro h
    apply haC
    rw [show a = side 0 s by linear_combination h]
    exact mem_iUnion.2 ⟨0, s, hs, rfl⟩
  set d := ‖Z‖ with hd
  have hd0 : 0 < d := norm_pos_iff.2 hZ0
  -- the open ball `B(a, d)` misses the trace, hence lies in `A`
  have hball : ball a d ⊆ A := by
    have hbC : ∀ w ∈ ball a d, w ∉ C := by
      intro w hw hwC
      have := hmin' w hwC
      have hd' : d = ‖side 0 s - a‖ := by rw [hd, hZ, norm_sub_rev]
      rw [mem_ball, dist_eq_norm] at hw
      linarith
    rcases fx_p2_sub_or_sub hAo hBo hAB huniv (convex_ball a d).isPreconnected hbC with h | h
    · exact h
    · exact absurd (h (mem_ball_self hd0)) (Set.disjoint_left.1 hAB haA)
  -- the first-order condition at the nearest point
  obtain ⟨θ, hθ⟩ := hC.straight 0
  have hdiff : DifferentiableAt ℝ (side 0) s := (hθ s hsI).1
  set D := deriv (side 0) s with hD
  have hD0 : D ≠ 0 := (hθ s hsI).2.1
  have hderiv : HasDerivAt (fun x => ‖side 0 x - a‖ ^ 2) (2 * inner ℝ (side 0 s - a) D) s :=
    (hdiff.hasDerivAt.sub_const a).norm_sq
  have hlocmin : IsLocalMin (fun x => ‖side 0 x - a‖ ^ 2) s := by
    filter_upwards [Icc_mem_nhds hsI.1 hsI.2] with x hx
    have := hmin' (side 0 x) (mem_iUnion.2 ⟨0, x, hx, rfl⟩)
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hinner : inner ℝ (side 0 s - a) D = 0 := by
    have := hlocmin.hasDerivAt_eq_zero hderiv
    linarith
  rw [Complex.inner] at hinner
  -- `Z = lam i D` with `lam` real
  have hre : (conj D * Z).re = 0 := by
    have : conj D * Z = -conj (D * conj (side 0 s - a)) := by
      rw [hZ, map_mul, Complex.conj_conj]; ring
    rw [this, neg_re, Complex.conj_re, hinner, neg_zero]
  set lam := (conj D * Z).im / ‖D‖ ^ 2 with hlam
  have hDn : 0 < ‖D‖ := norm_pos_iff.2 hD0
  have hZeq : Z = (lam : ℂ) * I * D := by
    have h1 : conj D * Z = ((conj D * Z).im : ℂ) * I := by
      apply Complex.ext <;> simp [hre]
    have h3 : ((‖D‖ : ℂ)) ^ 2 = D * conj D := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have hDn' : (‖D‖ : ℂ) ≠ 0 := by exact_mod_cast hDn.ne'
    have hcD : conj D ≠ 0 := (map_ne_zero _).2 hD0
    have key : Z * (D * conj D) = ((conj D * Z).im : ℂ) * I * D := by rw [← h1]; ring
    have hDD : D * conj D ≠ 0 := mul_ne_zero hD0 hcD
    calc Z = Z * (D * conj D) / (D * conj D) := by field_simp
      _ = ((conj D * Z).im : ℂ) * I * D / (D * conj D) := by rw [key]
      _ = (lam : ℂ) * I * D := by rw [hlam]; push_cast; rw [h3]; ring
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h] at hZeq
    simp at hZeq
    exact hZ0 hZeq
  have hmemA : ∀ q : ℝ, 0 < q → q < 1 → side 0 s + (q : ℂ) * Z ∈ A := by
    intro q hq0 hq1
    apply hball
    rw [mem_ball, dist_eq_norm]
    have : side 0 s + (q : ℂ) * Z - a = ((q - 1 : ℝ) : ℂ) * Z := by
      rw [hZ]; push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith), ← hd]
    nlinarith
  rcases lt_or_gt_of_ne hlam0 with hneg | hpos
  · right
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < -lam by linarith)] with ε hε
    have := hmemA (ε / -lam) (div_pos hε.1 (by linarith)) (by
      rw [div_lt_one (by linarith)]; exact hε.2)
    convert this using 1
    rw [hZeq]
    have : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam0
    push_cast
    field_simp
    ring
  · left
    show ∀ᶠ ε : ℝ in 𝓝[>] 0, side 0 s + (ε : ℂ) * I * D ∈ A
    filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
    have := hmemA (ε / lam) (div_pos hε.1 hpos) (by rw [div_lt_one hpos]; exact hε.2)
    convert this using 1
    rw [hZeq]
    have : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam0
    push_cast
    field_simp

/-- The reversed listing of a chain: `side' j t = side (-j - 1) (1 - t)`. -/
def fx_p2_revSide {n : ℕ} [NeZero n] (side : Fin n → ℝ → ℂ) (j : Fin n) (t : ℝ) : ℂ :=
  side (-j - 1) (1 - t)

/-- The reversed side as an affine reparametrisation. -/
theorem fx_p2_revSide_eq {n : ℕ} [NeZero n] (side : Fin n → ℝ → ℂ) (j : Fin n) :
    fx_p2_revSide side j = fun τ => side (-j - 1) (1 + (-1) * τ) := by
  funext τ
  simp only [fx_p2_revSide]
  ring_nf

/-- One-sided derivatives of the reversed sides. -/
theorem fx_p2_rev_derivWithin {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) (j : Fin n) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    derivWithin (fx_p2_revSide side j) (Icc 0 1) x =
      -derivWithin (side (-j - 1)) (Icc 0 1) (1 - x) := by
  rw [fx_p2_revSide_eq,
    fx_p2_derivWithin_affine (fx_p2_hasDerivWithinAt_of_contDiffOn (hC.smooth _)) zero_lt_one
      (fun τ hτ => ⟨by linarith [hτ.2], by linarith [hτ.1]⟩) hx]
  push_cast
  ring_nf

/-- Derivatives of the reversed sides at interior points. -/
theorem fx_p2_rev_deriv {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) (j : Fin n) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (fx_p2_revSide side j) x = -deriv (side (-j - 1)) (1 - x) := by
  have hx' : 1 - x ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  rw [fx_p2_deriv_eq_derivWithin hx, fx_p2_deriv_eq_derivWithin hx',
    fx_p2_rev_derivWithin hC j ⟨hx.1.le, hx.2.le⟩]

/-- The corner ratio of the reversed listing is the inverse of the original one. -/
theorem fx_p2_rev_ratio {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) (j : Fin n) :
    -(derivWithin (fx_p2_revSide side (j - 1)) (Icc 0 1) 1) /
        derivWithin (fx_p2_revSide side j) (Icc 0 1) 0 =
      (-(derivWithin (side (-j - 1)) (Icc 0 1) 1) / derivWithin (side (-j)) (Icc 0 1) 0)⁻¹ := by
  rw [fx_p2_rev_derivWithin hC _ ⟨zero_le_one, le_rfl⟩,
    fx_p2_rev_derivWithin hC _ ⟨le_rfl, zero_le_one⟩,
    show -(j - 1) - 1 = -j by abel, sub_self, sub_zero, inv_div]
  have h1 := hC.tan0 (-j)
  have h2 := hC.tan1 (-j - 1)
  field_simp

/-- The reversal of a chain is a chain. -/
theorem fx_p2_chain_rev {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) : fx_IsChain φ (fx_p2_revSide side) where
  straight j := by
    obtain ⟨θ, hθ⟩ := hC.straight (-j - 1)
    refine ⟨θ, fun t ht => ?_⟩
    have ht' : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    obtain ⟨hd, hd0, hne, harg⟩ := hθ (1 - t) ht'
    have hda : HasDerivAt (fx_p2_revSide side j) (-deriv (side (-j - 1)) (1 - t)) t := by
      have h1 : HasDerivAt (fun τ : ℝ => 1 - τ) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub 1
      have := hd.hasDerivAt.scomp t h1
      show HasDerivAt (fun x => side (-j - 1) (1 - x)) _ t
      simpa [Function.comp_def] using this
    refine ⟨hda.differentiableAt, ?_, ?_, ?_⟩
    · rw [hda.deriv]; exact neg_ne_zero.2 hd0
    · rw [hda.deriv, neg_sq]; exact hne
    · rw [hda.deriv, neg_sq]; exact harg
  smooth j := by
    rw [fx_p2_revSide_eq]
    exact fx_p2_contDiffOn_affine (hC.smooth _)
      (fun τ hτ => ⟨by linarith [hτ.2], by linarith [hτ.1]⟩)
  mem j := by
    rintro _ ⟨t, ht, rfl⟩
    exact hC.mem (-j - 1) ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  next j := by
    simp only [fx_p2_revSide, sub_self, sub_zero]
    rw [hC.next]
    congr 1
    abel
  simple i j s hs t ht h := by
    simp only [fx_p2_revSide] at h
    rcases eq_or_lt_of_le hs.1 with hs0 | hs0 <;> rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · rw [← hs0, ← ht0, sub_zero, hC.next, hC.next] at h
      have := (hC.simple _ _ 0 ⟨le_rfl, zero_lt_one⟩ 0 ⟨le_rfl, zero_lt_one⟩ h).1
      refine ⟨?_, by rw [← hs0, ← ht0]⟩
      have : -i = -j := by
        have e1 : -i - 1 + 1 = -i := by abel
        have e2 : -j - 1 + 1 = -j := by abel
        rwa [e1, e2] at this
      exact neg_injective this
    · rw [← hs0, sub_zero, hC.next] at h
      have := (hC.simple _ _ 0 ⟨le_rfl, zero_lt_one⟩ (1 - t)
        ⟨by linarith [ht.2], by linarith⟩ h).2
      linarith [ht.2]
    · rw [← ht0, sub_zero, hC.next] at h
      have := (hC.simple _ _ (1 - s) ⟨by linarith [hs.2], by linarith⟩ 0
        ⟨le_rfl, zero_lt_one⟩ h).2
      linarith [hs.2]
    · have := hC.simple _ _ (1 - s) ⟨by linarith [hs.2], by linarith⟩ (1 - t)
        ⟨by linarith [ht.2], by linarith⟩ h
      refine ⟨?_, by linarith [this.2]⟩
      have h2 : -i = -j := by
        have := this.1
        have e1 : -i - 1 + 1 = -i := by abel
        have e2 : -j - 1 + 1 = -j := by abel
        rw [← e1, ← e2, this]
      exact neg_injective h2
  tan0 j := by
    rw [fx_p2_rev_derivWithin hC j ⟨le_rfl, zero_le_one⟩, sub_zero]
    exact neg_ne_zero.2 (hC.tan1 _)
  tan1 j := by
    rw [fx_p2_rev_derivWithin hC j ⟨zero_le_one, le_rfl⟩, sub_self]
    exact neg_ne_zero.2 (hC.tan0 _)
  no_cusp j := by
    rw [fx_p2_rev_ratio hC j, arg_inv]
    have h := hC.no_cusp (-j)
    split_ifs with hπ
    · exact Real.pi_ne_zero
    · exact neg_ne_zero.2 h

/-- The corner angles of the reversed listing are `2π - θ`. -/
theorem fx_p2_rev_chainAngle {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) (j : Fin n) :
    fx_chainAngle (fx_p2_revSide side) j = 2 * π - fx_chainAngle side (-j) := by
  unfold fx_chainAngle
  rw [fx_p2_rev_ratio hC j, arg_inv]
  set x := -(derivWithin (side (-j - 1)) (Icc 0 1) 1) / derivWithin (side (-j)) (Icc 0 1) 0
  have h0 : arg x ≠ 0 := hC.no_cusp (-j)
  have hmem := arg_mem_Ioc x
  have hpi := Real.pi_pos
  by_cases hπ : arg x = π
  · simp only [hπ, ite_true, ite_eq_left hpi]
    ring
  · simp only [hπ, ite_false]
    rcases lt_or_gt_of_ne h0 with hn | hp
    · rw [ite_eq_left (show 0 < -arg x by linarith), ite_eq_right (show ¬ 0 < arg x by linarith)]
      ring
    · rw [ite_eq_right (show ¬ 0 < -arg x by linarith), ite_eq_left hp]
      ring

/-- Positivity of the reversed listing is right-positivity of the original one. -/
theorem fx_p2_rev_pos_iff {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) (A : Set ℂ) (j : Fin n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    fx_p2_PosAt A (fx_p2_revSide side) j t ↔
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        side (-j - 1) (1 - t) - (ε : ℂ) * I * deriv (side (-j - 1)) (1 - t) ∈ A := by
  unfold fx_p2_PosAt
  rw [fx_p2_rev_deriv hC j ht]
  simp only [fx_p2_revSide, mul_neg, ← sub_eq_add_neg]

/-- The reversed listing has the same trace. -/
theorem fx_p2_rev_trace {n : ℕ} [NeZero n] (side : Fin n → ℝ → ℂ) :
    (⋃ j, fx_p2_revSide side j '' Icc (0 : ℝ) 1) = ⋃ j, side j '' Icc (0 : ℝ) 1 := by
  ext z
  simp only [mem_iUnion, mem_image]
  constructor
  · rintro ⟨j, t, ht, rfl⟩
    exact ⟨-j - 1, 1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  · rintro ⟨k, t, ht, rfl⟩
    refine ⟨-k - 1, 1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    simp only [fx_p2_revSide, sub_sub_cancel]
    congr 1
    abel

/-- **Building the `PhiPolygon`** from a positively oriented chain. -/
theorem fx_p2_chain_phiPolygon {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) {A : Set ℂ} (hJ : IsJordanDomain A) (hcl : closure A ⊆ unitDisc)
    (hfr : frontier A = ⋃ j, side j '' Icc (0 : ℝ) 1)
    (hpos : ∀ j, ∀ t ∈ Ioo (0 : ℝ) 1, fx_p2_PosAt A side j t) :
    ∃ P : PhiPolygon φ n, ∀ j, P.vert j = side j 0 ∧ P.angle j = fx_chainAngle side j := by
  refine ⟨⟨A, fun j => side j 0, side, fx_chainAngle side, hJ, hcl,
    fun j => ⟨hC.straight j, hC.smooth j⟩, fun j => rfl, fun j => hC.next j, hfr,
    fun j => ?_, fun j => ?_, hpos, hC.simple⟩, fun j => ⟨rfl, rfl⟩⟩
  · obtain ⟨h1, h2, -, -⟩ := fx_p2_angle_facts (arg_mem_Ioc _) (hC.no_cusp j)
    exact ⟨h1, h2⟩
  · obtain ⟨-, -, -, k, hk⟩ := fx_p2_angle_facts (arg_mem_Ioc _) (hC.no_cusp j)
    exact ⟨k, hk⟩
/-! ### Trajectory pieces as chain sides; no closed trajectories -/

/-- A trajectory piece `γ|[a, b]`, rescaled to `[0, 1]`, is a `φ`-straight arc. -/
theorem fx_p2_htrajP_straight {φ : ℂ → ℂ} {γ : ℝ → ℂ} {T : ℝ} (hγ : fx_p2_htrajP φ γ T) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ T) :
    IsPhiStraightArc φ (fun τ => γ (a + (b - a) * τ)) 0 1 := by
  refine ⟨0, fun τ hτ => ?_⟩
  set x := a + (b - a) * τ with hxdef
  have hba : 0 < b - a := sub_pos.2 hab
  have hx : x ∈ Ioo 0 T := ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  have hxI : x ∈ Icc 0 T := ⟨hx.1.le, hx.2.le⟩
  have hdx : HasDerivAt γ (derivWithin γ (Icc 0 T) x) x :=
    (fx_p2_hasDerivWithinAt_of_contDiffOn hγ.2.1 x hxI).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  have he : HasDerivAt (fun τ : ℝ => a + (b - a) * τ) (b - a) τ := by
    simpa using ((hasDerivAt_id τ).const_mul (b - a)).const_add a
  have hc' : HasDerivAt (fun τ => γ (a + (b - a) * τ))
      (((b - a : ℝ) : ℂ) * derivWithin γ (Icc 0 T) x) τ := by
    simpa [Function.comp_def, Complex.real_smul] using hdx.scomp τ he
  have hw : derivWithin γ (Icc 0 T) x ≠ 0 := by
    intro h
    have := hγ.2.2.2 x hxI
    rw [h] at this
    simp at this
  have hsq : φ (γ x) * (((b - a : ℝ) : ℂ) * derivWithin γ (Icc 0 T) x) ^ 2 =
      (((b - a) ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, ← mul_assoc, mul_comm (φ (γ x)), mul_assoc, hγ.2.2.2 x hxI]
    push_cast
    ring
  refine ⟨hc'.differentiableAt, ?_, ?_, ?_⟩
  · rw [hc'.deriv]
    exact mul_ne_zero (by exact_mod_cast hba.ne') hw
  · rw [hc'.deriv, hsq]
    exact_mod_cast (pow_pos hba 2).ne'
  · rw [hc'.deriv, hsq]
    simp only [Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one]
    exact Complex.arg_ofReal_of_nonneg (sq_nonneg _)

/-- Uniform local injectivity of a unit-speed trajectory. -/
theorem fx_p2_htrajP_locInj {φ : ℂ → ℂ} {γ : ℝ → ℂ} {T : ℝ} (hγ : fx_p2_htrajP φ γ T) :
    ∃ δ > 0, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s < t → t - s < δ → γ s ≠ γ t := by
  set d := derivWithin γ (Icc 0 T) with hd
  have hdc : ContinuousOn d (Icc 0 T) :=
    hγ.2.1.continuousOn_derivWithin (uniqueDiffOn_Icc hγ.1) le_rfl
  have hd0 : ∀ x ∈ Icc 0 T, d x ≠ 0 := by
    intro x hx h
    have := hγ.2.2.2 x hx
    rw [← hd, h] at this
    simp at this
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, le_rfl, hγ.1.le⟩
    (continuous_norm.comp_continuousOn hdc)
  set m₀ := ‖d x₀‖ with hm₀
  have hm₀0 : 0 < m₀ := norm_pos_iff.2 (hd0 x₀ hx₀)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hdc) (m₀ / 2) (by positivity)
  refine ⟨δ, hδ, fun s hs t ht hst htd heq => ?_⟩
  have hsub : Icc s t ⊆ Icc 0 T := Icc_subset_Icc hs.1 ht.2
  set g : ℝ → ℂ := fun x => γ x - (x : ℂ) * d s with hg
  have hgd : ∀ x ∈ Icc s t, HasDerivWithinAt g (d x - d s) (Icc s t) x := by
    intro x hx
    have h1 : HasDerivWithinAt (fun x : ℝ => (x : ℂ) * d s) (d s) (Icc s t) x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const (d s)).hasDerivWithinAt
    exact ((fx_p2_hasDerivWithinAt_of_contDiffOn hγ.2.1 x (hsub hx)).mono hsub).sub h1
  have hbd : ∀ x ∈ Icc s t, ‖d x - d s‖ ≤ m₀ / 2 := by
    intro x hx
    have hdist : dist x s < δ := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]
    have := hδ' x (hsub hx) s hs hdist
    rw [dist_eq_norm] at this
    exact this.le
  have hmv := (convex_Icc s t).norm_image_sub_le_of_norm_hasDerivWithin_le hgd hbd
    ⟨le_rfl, hst.le⟩ ⟨hst.le, le_rfl⟩
  simp only [hg, heq, sub_sub_sub_cancel_left, Real.norm_eq_abs] at hmv
  rw [show (s : ℂ) * d s - (t : ℂ) * d s = -(((t - s : ℝ) : ℂ) * d s) by push_cast; ring, norm_neg,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.2 hst)] at hmv
  have h2 : m₀ ≤ ‖d s‖ := hmin hs
  have h3 : (t - s) * ‖d s‖ ≤ (t - s) * (m₀ / 2) := by linarith
  have h4 := le_of_mul_le_mul_left h3 (sub_pos.2 hst)
  linarith

/-- **No closed trajectories** (helper form of `fx_htraj_injOn`): a trajectory is injective,
given that there is no closed one-sided chain. -/
theorem fx_p2_htrajP_injOn {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hCF : ∀ side : Fin 1 → ℝ → ℂ, ¬ fx_IsChain φ side) {γ : ℝ → ℂ} {T : ℝ}
    (hγ : fx_p2_htrajP φ γ T) : InjOn γ (Icc 0 T) := by
  obtain ⟨δ, hδ, hloc⟩ := fx_p2_htrajP_locInj hγ
  by_contra hni
  have hex : ∃ s ∈ Icc 0 T, ∃ t ∈ Icc 0 T, s < t ∧ γ s = γ t := by
    simp only [InjOn, not_forall] at hni
    obtain ⟨s, hs, t, ht, heq, hne⟩ := hni
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨s, hs, t, ht, h, heq⟩
    · exact ⟨t, ht, s, hs, h, heq.symm⟩
  obtain ⟨s₀, hs₀, t₀, ht₀, hst₀, heq₀⟩ := hex
  -- the compact set of return pairs
  set P : Set (ℝ × ℝ) := (Icc 0 T ×ˢ Icc 0 T) ∩ (fun p : ℝ × ℝ => γ p.1 - γ p.2) ⁻¹' {0} ∩
    {p | p.1 + δ ≤ p.2} with hP
  have hPc : IsCompact P := by
    refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_
      (inter_subset_left.trans inter_subset_left)
    refine IsClosed.inter ?_ (isClosed_le (continuous_fst.add continuous_const) continuous_snd)
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ (isClosed_Icc.prod isClosed_Icc)
      isClosed_singleton
    exact (hγ.2.1.continuousOn.comp continuous_fst.continuousOn (fun p hp => hp.1)).sub
      (hγ.2.1.continuousOn.comp continuous_snd.continuousOn (fun p hp => hp.2))
  have hmemP : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s < t → γ s = γ t → (s, t) ∈ P := by
    intro s hs t ht hst heq
    refine ⟨⟨⟨hs, ht⟩, by simp [heq]⟩, ?_⟩
    show s + δ ≤ t
    by_contra h
    exact hloc s hs t ht hst (by linarith) heq
  obtain ⟨⟨a, b⟩, hab, hmin⟩ := hPc.exists_isMinOn ⟨_, hmemP s₀ hs₀ t₀ ht₀ hst₀ heq₀⟩
    ((continuous_snd.sub continuous_fst).continuousOn)
  obtain ⟨⟨⟨ha, hb⟩, hab0⟩, habδ⟩ := hab
  have habeq : γ a = γ b := sub_eq_zero.1 hab0
  have habδ' : a + δ ≤ b := habδ
  have hlt : a < b := by linarith
  have hmin' : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s < t → γ s = γ t → b - a ≤ t - s :=
    fun s hs t ht hst heq => hmin (hmemP s hs t ht hst heq)
  have hinj : InjOn γ (Ico a b) := by
    intro s hs t ht heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hmin' s ⟨ha.1.trans hs.1, by linarith [hs.2, hb.2]⟩ t
        ⟨by linarith [ha.1, ht.1], by linarith [ht.2, hb.2]⟩ h heq
      linarith [hs.1, ht.2]
    · have := hmin' t ⟨ha.1.trans ht.1, by linarith [ht.2, hb.2]⟩ s
        ⟨by linarith [ha.1, hs.1], by linarith [hs.2, hb.2]⟩ h heq.symm
      linarith [ht.1, hs.2]
  set d := derivWithin γ (Icc 0 T) with hd
  have hda := hγ.2.2.2 a ha
  have hdb := hγ.2.2.2 b hb
  rw [← hd] at hda hdb
  rw [habeq] at hda
  have hφb : φ (γ b) ≠ 0 := (hγ.2.2.1 b hb).2
  have hsq : d a ^ 2 = d b ^ 2 := mul_left_cancel₀ hφb (hda.trans hdb.symm)
  have hd0 : d a ≠ 0 := by
    intro h; rw [h] at hda; simp at hda
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hpm | hpm
  · -- the same velocity: a closed trajectory, i.e. a one-sided chain
    apply hCF (fun _ τ => γ (a + (b - a) * τ))
    have hmap : ∀ τ ∈ Icc (0 : ℝ) 1, a + (b - a) * τ ∈ Icc 0 T :=
      fun τ hτ => ⟨by nlinarith [hτ.1, ha.1], by nlinarith [hτ.2, hb.2]⟩
    have hder : ∀ τ ∈ Icc (0 : ℝ) 1, derivWithin (fun τ => γ (a + (b - a) * τ)) (Icc 0 1) τ =
        ((b - a : ℝ) : ℂ) * d (a + (b - a) * τ) :=
      fun τ hτ => fx_p2_derivWithin_affine (fx_p2_hasDerivWithinAt_of_contDiffOn hγ.2.1) zero_lt_one
        hmap hτ
    have hba : ((b - a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.2 hlt).ne'
    refine ⟨fun _ => fx_p2_htrajP_straight hγ ha.1 hlt hb.2,
      fun _ => fx_p2_contDiffOn_affine hγ.2.1 hmap,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ _ ⟨τ, hτ, rfl⟩
      exact (hγ.2.2.1 _ (hmap τ hτ)).1
    · intro _
      simp only [mul_one, mul_zero, add_zero, add_sub_cancel]
      exact habeq.symm
    · intro i j s hs t ht heq
      refine ⟨Subsingleton.elim i j, ?_⟩
      have h1 := hinj ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
        ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩ heq
      have h2 : (b - a) * s = (b - a) * t := by linarith
      exact mul_left_cancel₀ (sub_pos.2 hlt).ne' h2
    · intro _
      rw [hder 0 ⟨le_rfl, zero_le_one⟩, mul_zero, add_zero]
      exact mul_ne_zero hba hd0
    · intro _
      rw [hder 1 ⟨zero_le_one, le_rfl⟩, mul_one, add_sub_cancel, ← hpm]
      exact mul_ne_zero hba hd0
    · intro _
      rw [hder 1 ⟨zero_le_one, le_rfl⟩, hder 0 ⟨le_rfl, zero_le_one⟩, mul_one, mul_zero, add_zero,
        add_sub_cancel, ← hpm, neg_div, div_self (mul_ne_zero hba hd0), Complex.arg_neg_one]
      exact Real.pi_ne_zero
  · -- opposite velocity: the trajectory retraces itself, contradicting minimality
    have hL : 0 < b - a := sub_pos.2 hlt
    have hm1 : ∀ τ ∈ Icc 0 (b - a), a + 1 * τ ∈ Icc 0 T :=
      fun τ hτ => ⟨by linarith [hτ.1, ha.1], by linarith [hτ.2, hb.2]⟩
    have hm2 : ∀ τ ∈ Icc 0 (b - a), b + (-1) * τ ∈ Icc 0 T :=
      fun τ hτ => ⟨by linarith [hτ.2, ha.1], by linarith [hτ.1, hb.2]⟩
    have h1 := fx_p2_htrajP_affine hγ (by norm_num) hL hm1
    have h2 := fx_p2_htrajP_affine hγ (by norm_num) hL hm2
    have hu := fx_p2_htrajP_unique hφ h1 h2 (by simp [habeq]) (by
      rw [fx_p2_htrajP_derivWithin_affine hγ hL hm1 ⟨le_rfl, hL.le⟩,
        fx_p2_htrajP_derivWithin_affine hγ hL hm2 ⟨le_rfl, hL.le⟩]
      simp only [mul_zero, add_zero, Complex.ofReal_one, one_mul, Complex.ofReal_neg,
        neg_one_mul]
      rw [← hd, hpm])
    have := hu ((b - a) / 4) ⟨by linarith, by rw [min_self]; linarith⟩
    simp only [one_mul] at this
    have h3 := hmin' (a + (b - a) / 4) ⟨by linarith [ha.1], by linarith [hb.2]⟩
      (b + -1 * ((b - a) / 4)) ⟨by linarith [ha.1], by linarith [hb.2]⟩ (by linarith) this
    linarith
/-! ### Affine pieces of vertical edges; the star lemma -/

/-- An affine reparametrisation (preserving `(0, 1)`) of a `φ`-straight arc is `φ`-straight. -/
theorem fx_p2_straight_affine {φ : ℂ → ℂ} {c : ℝ → ℂ} (hc : IsPhiStraightArc φ c 0 1) {α β : ℝ}
    (hβ : β ≠ 0) (hmap : ∀ τ ∈ Ioo (0 : ℝ) 1, α + β * τ ∈ Ioo (0 : ℝ) 1) :
    IsPhiStraightArc φ (fun τ => c (α + β * τ)) 0 1 := by
  obtain ⟨θ, hθ⟩ := hc
  refine ⟨θ, fun τ hτ => ?_⟩
  obtain ⟨hd, hd0, hne, harg⟩ := hθ _ (hmap τ hτ)
  have he : HasDerivAt (fun τ : ℝ => α + β * τ) β τ := by
    simpa using ((hasDerivAt_id τ).const_mul β).const_add α
  have hc' : HasDerivAt (fun τ => c (α + β * τ)) ((β : ℂ) * deriv c (α + β * τ)) τ := by
    simpa [Function.comp_def, Complex.real_smul] using hd.hasDerivAt.scomp τ he
  have hsq : φ (c (α + β * τ)) * ((β : ℂ) * deriv c (α + β * τ)) ^ 2 =
      ((β ^ 2 : ℝ) : ℂ) * (φ (c (α + β * τ)) * deriv c (α + β * τ) ^ 2) := by
    push_cast; ring
  have hβ2 : 0 < β ^ 2 := by positivity
  refine ⟨hc'.differentiableAt, ?_, ?_, ?_⟩
  · rw [hc'.deriv]; exact mul_ne_zero (by exact_mod_cast hβ) hd0
  · rw [hc'.deriv, hsq]; exact mul_ne_zero (by exact_mod_cast hβ2.ne') hne
  · rw [hc'.deriv, hsq, mul_assoc, Complex.arg_real_mul _ hβ2]
    exact harg

/-- An affine reparametrisation (preserving `(0, 1)`) of a vertical arc is vertical. -/
theorem fx_p2_vertical_affine {φ : ℂ → ℂ} {c : ℝ → ℂ} (hc : IsVerticalArc φ c 0 1) {α β : ℝ}
    (hβ : β ≠ 0) (hmap : ∀ τ ∈ Ioo (0 : ℝ) 1, α + β * τ ∈ Ioo (0 : ℝ) 1) :
    IsVerticalArc φ (fun τ => c (α + β * τ)) 0 1 := by
  intro τ hτ
  obtain ⟨hd, hd0, hne, him, hre⟩ := hc _ (hmap τ hτ)
  have he : HasDerivAt (fun τ : ℝ => α + β * τ) β τ := by
    simpa using ((hasDerivAt_id τ).const_mul β).const_add α
  have hc' : HasDerivAt (fun τ => c (α + β * τ)) ((β : ℂ) * deriv c (α + β * τ)) τ := by
    simpa [Function.comp_def, Complex.real_smul] using hd.hasDerivAt.scomp τ he
  have hsq : φ (c (α + β * τ)) * ((β : ℂ) * deriv c (α + β * τ)) ^ 2 =
      ((β ^ 2 : ℝ) : ℂ) * (φ (c (α + β * τ)) * deriv c (α + β * τ) ^ 2) := by
    push_cast; ring
  have hβ2 : 0 < β ^ 2 := by positivity
  refine ⟨hc'.differentiableAt, ?_, hne, ?_, ?_⟩
  · rw [hc'.deriv]; exact mul_ne_zero (by exact_mod_cast hβ) hd0
  · rw [hc'.deriv, hsq, Complex.im_ofReal_mul, him, mul_zero]
  · rw [hc'.deriv, hsq, Complex.re_ofReal_mul]
    exact mul_neg_of_pos_of_neg hβ2 hre

/-- A function `C¹` on `[0, 1)` has its `derivWithin (Icc 0 1)` as derivative within any `[0, σ]`,
`σ < 1`. -/
theorem fx_p2_hasDerivWithinAt_Ico {c : ℝ → ℂ} (hc : ContDiffOn ℝ 1 c (Ico 0 1)) {σ : ℝ}
    (hσ : σ < 1) : ∀ x ∈ Icc 0 σ, HasDerivWithinAt c (derivWithin c (Icc 0 1) x) (Icc 0 σ) x := by
  intro x hx
  have hx1 : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
  have hd : DifferentiableWithinAt ℝ c (Icc 0 1) x := by
    refine ((hc.differentiableOn one_ne_zero) x hx1).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Iio 1, isOpen_Iio, hx1.2, fun y hy => ⟨hy.2.1, hy.1⟩⟩
  exact hd.hasDerivWithinAt.mono (Icc_subset_Icc le_rfl hσ.le)

/-- **Normalised edge at an incident zero**: an edge incident to `q` can be reparametrised to
start at `q`, keeping its interior trace, with outgoing tangent `fx_outTangent`. -/
theorem fx_p2_normEdge {φ : ℂ → ℂ} {c : ℝ → ℂ} {s₀ q : ℂ} {d₀ : Option ℂ}
    (hv : IsVerticalArc φ c 0 1) (hmem : ∀ t ∈ Ioo (0 : ℝ) 1, c t ∈ unitDisc)
    (hinj : InjOn c (Ioo 0 1)) (hsm : ContDiffOn ℝ 1 c (Ico 0 1))
    (hsrc : c 0 = s₀ ∧ s₀ ∈ unitDisc ∧ φ s₀ = 0) (htan : derivWithin c (Icc 0 1) 0 ≠ 0)
    (hsad : ∀ q', d₀ = some q' → q' ∈ unitDisc ∧ φ q' = 0 ∧ q' ≠ s₀ ∧
      ContDiffOn ℝ 1 c (Icc 0 1) ∧ c 1 = q' ∧ derivWithin c (Icc 0 1) 1 ≠ 0)
    (hinc : s₀ = q ∨ d₀ = some q) :
    ∃ e : ℝ → ℂ, e 0 = q ∧ q ∈ unitDisc ∧ φ q = 0 ∧ IsVerticalArc φ e 0 1 ∧
      ContDiffOn ℝ 1 e (Ico 0 1) ∧ InjOn e (Ioo 0 1) ∧ (∀ t ∈ Ioo (0 : ℝ) 1, e t ∈ unitDisc) ∧
      e '' Ioo 0 1 = c '' Ioo 0 1 ∧
      derivWithin e (Icc 0 1) 0 =
        (if s₀ = q then derivWithin c (Icc 0 1) 0 else -derivWithin c (Icc 0 1) 1) ∧
      derivWithin e (Icc 0 1) 0 ≠ 0 := by
  by_cases hsq : s₀ = q
  · subst hsq
    refine ⟨c, hsrc.1, hsrc.2.1, hsrc.2.2, hv, hsm, hinj, hmem, rfl, by rw [ite_eq_left rfl],
      htan⟩
  · have hd : d₀ = some q := hinc.resolve_left hsq
    obtain ⟨hq, hq0, -, hsm', hc1, htan1⟩ := hsad q hd
    have hmap : ∀ τ ∈ Icc (0 : ℝ) 1, 1 + (-1) * τ ∈ Icc (0 : ℝ) 1 :=
      fun τ hτ => ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    have hder : derivWithin (fun τ => c (1 + (-1) * τ)) (Icc 0 1) 0 =
        -derivWithin c (Icc 0 1) 1 := by
      rw [fx_p2_derivWithin_affine (fx_p2_hasDerivWithinAt_of_contDiffOn hsm') zero_lt_one hmap
        ⟨le_rfl, zero_le_one⟩]
      simp
    refine ⟨fun τ => c (1 + (-1) * τ), by simp [hc1], hq, hq0,
      fx_p2_vertical_affine hv (by norm_num)
      (fun τ hτ => ⟨by linarith [hτ.2], by linarith [hτ.1]⟩),
      (fx_p2_contDiffOn_affine hsm' hmap).mono Ico_subset_Icc_self, ?_, ?_, ?_, ?_, ?_⟩
    · intro s hs t ht h
      have := hinj ⟨by linarith [hs.2], by linarith [hs.1]⟩
        ⟨by linarith [ht.2], by linarith [ht.1]⟩ h
      linarith
    · intro t ht
      exact hmem _ ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨1 + (-1) * t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp only; ring_nf⟩
    · rw [hder, ite_eq_right hsq]
    · rw [hder]; exact neg_ne_zero.2 htan1

/-- **Pieces of a normalised edge**: `τ ↦ e (α + β τ)` with values in `[0, σ]`, `σ < 1`. -/
theorem fx_p2_npiece {φ : ℂ → ℂ} {e : ℝ → ℂ} (hv : IsVerticalArc φ e 0 1)
    (hsm : ContDiffOn ℝ 1 e (Ico 0 1)) (hmem : ∀ t ∈ Ioo (0 : ℝ) 1, e t ∈ unitDisc)
    (he0 : e 0 ∈ unitDisc) {σ α β : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) (hβ : β ≠ 0)
    (hmap : ∀ τ ∈ Icc (0 : ℝ) 1, α + β * τ ∈ Icc 0 σ)
    (hmapo : ∀ τ ∈ Ioo (0 : ℝ) 1, α + β * τ ∈ Ioo (0 : ℝ) 1) :
    IsPhiStraightArc φ (fun τ => e (α + β * τ)) 0 1 ∧
      ContDiffOn ℝ 1 (fun τ => e (α + β * τ)) (Icc 0 1) ∧
      (fun τ => e (α + β * τ)) '' Icc 0 1 ⊆ unitDisc ∧
      ∀ τ ∈ Icc (0 : ℝ) 1, derivWithin (fun τ => e (α + β * τ)) (Icc 0 1) τ =
        (β : ℂ) * derivWithin e (Icc 0 1) (α + β * τ) := by
  have hsub : Icc 0 σ ⊆ Ico (0 : ℝ) 1 := fun x hx => ⟨hx.1, by linarith [hx.2, hσ.2]⟩
  refine ⟨fx_p2_straight_affine ((horizontal_vertical_isPhiStraight).2 hv) hβ hmapo,
    fx_p2_contDiffOn_affine (hsm.mono hsub) hmap, ?_,
    fun τ hτ => fx_p2_derivWithin_affine (fx_p2_hasDerivWithinAt_Ico hsm hσ.2) zero_lt_one hmap hτ⟩
  rintro _ ⟨τ, hτ, rfl⟩
  have hx := hmap τ hτ
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · simp only; rw [← h0]; exact he0
  · exact hmem _ ⟨h0, by linarith [hx.2, hσ.2]⟩

/-- A generic criterion for `fx_IsChain.simple`. -/
theorem fx_p2_simple_of {n : ℕ} {side : Fin n → ℝ → ℂ} (hinj : ∀ k, InjOn (side k) (Ico 0 1))
    (hv : ∀ k l, side k 0 = side l 0 → k = l)
    (hvi : ∀ k l, ∀ s ∈ Ioo (0 : ℝ) 1, side k 0 ≠ side l s)
    (hii : ∀ k l, k ≠ l → ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Ioo (0 : ℝ) 1, side k s ≠ side l t) :
    ∀ i j : Fin n, ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1, side i s = side j t →
      i = j ∧ s = t := by
  intro i j s hs t ht h
  rcases eq_or_lt_of_le hs.1 with hs0 | hs0 <;> rcases eq_or_lt_of_le ht.1 with ht0 | ht0
  · rw [← hs0, ← ht0] at h ⊢; exact ⟨hv i j h, rfl⟩
  · rw [← hs0] at h; exact absurd h (hvi i j t ⟨ht0, ht.2⟩)
  · rw [← ht0] at h; exact absurd h.symm (hvi j i s ⟨hs0, hs.2⟩)
  · by_cases hij : i = j
    · subst hij; exact ⟨rfl, hinj i hs ht h⟩
    · exact absurd h (hii i j hij s ⟨hs0, hs.2⟩ t ⟨ht0, ht.2⟩)

/-- A complex number whose square is a negative real has nonzero argument. -/
theorem fx_p2_arg_ne_of_sq_neg {r : ℂ} (h : (r ^ 2).re < 0) : arg r ≠ 0 := by
  intro h0
  obtain ⟨hre, him⟩ := arg_eq_zero_iff.1 h0
  have : (r ^ 2).re = r.re ^ 2 := by rw [sq, Complex.mul_re, him]; ring
  rw [this] at h
  nlinarith [sq_nonneg r.re]

/-- **Blunt ratios** (the raw form of `fx_IsBluntRatio`), scaled by `c > 0`: nonzero argument, and
the `(0, 2π]`-representative of the argument lies in `[2π/(m+2), 2π - 2π/(m+2)]`. -/
theorem fx_p2_bluntRatio {m : ℕ} {r : ℂ}
    (hr : (r ^ (m + 2)).im = 0 ∧ 0 < (r ^ (m + 2)).re ∧ ¬ (r.im = 0 ∧ 0 < r.re)) {c : ℝ}
    (hc : 0 < c) :
    arg ((c : ℂ) * r) ≠ 0 ∧
      2 * π / ((m : ℝ) + 2) ≤ (if 0 < arg ((c : ℂ) * r) then arg ((c : ℂ) * r)
        else arg ((c : ℂ) * r) + 2 * π) ∧
      (if 0 < arg ((c : ℂ) * r) then arg ((c : ℂ) * r) else arg ((c : ℂ) * r) + 2 * π) ≤
        2 * π - 2 * π / ((m : ℝ) + 2) := by
  rw [Complex.arg_real_mul r hc]
  have hpi := Real.pi_pos
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have hα0 : arg r ≠ 0 := by
    intro h
    obtain ⟨hre, him⟩ := arg_eq_zero_iff.1 h
    apply hr.2.2
    refine ⟨him, lt_of_le_of_ne hre (fun h' => hr0 (Complex.ext h'.symm him))⟩
  -- `(m + 2) α ∈ 2πℤ`
  set N : ℕ := m + 2 with hN
  have hN2 : (2 : ℝ) ≤ N := by rw [hN]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hNpos : (0 : ℝ) < N := by linarith
  have hexp : exp (((N * arg r : ℝ) : ℂ) * I) = 1 := by
    have hrn : 0 < ‖r‖ := norm_pos_iff.2 hr0
    have h1 : r ^ N = ((‖r‖ ^ N : ℝ) : ℂ) * exp (((N * arg r : ℝ) : ℂ) * I) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I r]
      rw [mul_pow, ← Complex.exp_nat_mul]
      push_cast
      ring_nf
    have h2 : r ^ N = (((r ^ N).re : ℝ) : ℂ) := Complex.ext rfl (by simp [hr.1])
    have hpos : (0 : ℝ) < ‖r‖ ^ N := by positivity
    have h3 : exp (((N * arg r : ℝ) : ℂ) * I) = (((r ^ N).re / ‖r‖ ^ N : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, eq_div_iff (by exact_mod_cast hpos.ne'), ← h2, h1]; ring
    have h4 : ‖exp (((N * arg r : ℝ) : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    rw [h3, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hr.2.1 hpos)] at h4
    rw [h3, h4, Complex.ofReal_one]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 hexp
  have hk' : (N : ℝ) * arg r = k * (2 * π) := by
    have h5 : ((N * arg r : ℝ) : ℂ) = ((k * (2 * π) : ℝ) : ℂ) := by
      apply mul_right_cancel₀ Complex.I_ne_zero
      rw [hk]
      push_cast
      ring
    exact_mod_cast h5
  have hmem := arg_mem_Ioc r
  have hcast : ((m : ℝ) + 2) = N := by rw [hN]; push_cast; ring
  rw [hcast]
  -- `2π/N ≤ x ↔ 2π ≤ x N`
  have key : ∀ x : ℝ, 2 * π ≤ x * N → 2 * π / N ≤ x := fun x hx => by
    rw [div_le_iff₀ hNpos]; exact hx
  have hπk : ∀ y : ℝ, 0 ≤ y → 0 ≤ π * y := fun y hy => mul_nonneg hpi.le hy
  rcases lt_or_gt_of_ne hα0 with hneg | hpos
  · rw [ite_eq_right (show ¬ 0 < arg r by linarith)]
    have hNa : (N : ℝ) * arg r < 0 := mul_neg_of_pos_of_neg hNpos hneg
    have hk0 : (k : ℝ) < 0 := by
      by_contra h
      push Not at h
      have := mul_nonneg h (show (0 : ℝ) ≤ 2 * π by positivity)
      linarith
    have hk1 : (k : ℝ) ≤ -1 := by
      have : k < 0 := by exact_mod_cast hk0
      exact_mod_cast Int.le_sub_one_of_lt this
    have hlow : (N : ℝ) * (-π) < N * arg r := mul_lt_mul_of_pos_left hmem.1 hNpos
    refine ⟨hα0, key _ ?_, ?_⟩
    · -- `(arg r + 2π) N = 2π (k + N) ≥ 2π`
      have h1 : 0 < π * (2 * k + N) := by nlinarith
      have h2 : 0 < 2 * (k : ℝ) + N := pos_of_mul_pos_right h1 hpi.le
      have h3 := hπk (2 * k + 2 * N - 2) (by linarith)
      nlinarith
    · have h4 := hπk (-2 * k - 2) (by linarith)
      have := key (-arg r) (by nlinarith)
      linarith
  · rw [ite_eq_left hpos]
    have hk0 : (0 : ℝ) < k := by
      by_contra h
      push Not at h
      have := mul_nonpos_of_nonpos_of_nonneg h (show (0 : ℝ) ≤ 2 * π by positivity)
      nlinarith
    have hk1 : (1 : ℝ) ≤ k := by
      have : 0 < k := by exact_mod_cast hk0
      exact_mod_cast Int.add_one_le_of_lt this
    have hup : (N : ℝ) * arg r ≤ N * π := mul_le_mul_of_nonneg_left hmem.2 hNpos.le
    refine ⟨hα0, key _ ?_, ?_⟩
    · have h4 := hπk (2 * k - 2) (by linarith)
      nlinarith
    · have h1 : 0 ≤ π * (N - 2 * k) := by nlinarith
      have h2 : 0 ≤ (N : ℝ) - 2 * k := nonneg_of_mul_nonneg_right h1 hpi
      have h3 := hπk (N - 2) (by linarith)
      have := key (2 * π - arg r) (by nlinarith)
      linarith
/-- The outgoing tangent (a verbatim copy of the body of `fx_outTangent`). -/
def fx_p2_oT {ι : Type} (par : ι → ℝ → ℂ) (src : ι → ℂ) (i : ι) (q : ℂ) : ℂ :=
  if src i = q then derivWithin (par i) (Icc 0 1) 0 else -derivWithin (par i) (Icc 0 1) 1

/-- Blunt ratios (a verbatim copy of the body of `fx_IsBluntRatio`). -/
def fx_p2_bluntR (m : ℕ) (r : ℂ) : Prop :=
  (r ^ (m + 2)).im = 0 ∧ 0 < (r ^ (m + 2)).re ∧ ¬ (r.im = 0 ∧ 0 < r.re)

/-- The square of `-(σ e'(σ)) / ((t₂ - t₁) γ'(t₁))` at a crossing of a vertical edge by a unit-speed
horizontal trajectory is a negative real (the corner is at a right angle). -/
theorem fx_p2_corner_hv {φy dv dh : ℂ} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : (φy * dv ^ 2).re < 0) (hh : φy * dh ^ 2 = 1) :
    arg (-((a : ℂ) * dv) / ((b : ℂ) * dh)) ≠ 0 := by
  apply fx_p2_arg_ne_of_sq_neg
  have hdh : dh ≠ 0 := by rintro rfl; simp at hh
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have hφ : φy = 1 / dh ^ 2 := by field_simp; linear_combination hh
  have : (-((a : ℂ) * dv) / ((b : ℂ) * dh)) ^ 2 = (((a / b) ^ 2 : ℝ) : ℂ) * (φy * dv ^ 2) := by
    rw [hφ]; push_cast; field_simp
  rw [this, Complex.re_ofReal_mul]
  exact mul_neg_of_pos_of_neg (by positivity) hv

/-- The mirror corner: the square of `-(b γ'(t₂)) / (a e'(σ))` is a negative real. -/
theorem fx_p2_corner_vh {φy dv dh : ℂ} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hv : (φy * dv ^ 2).re < 0) (hh : φy * dh ^ 2 = 1) :
    arg (-((b : ℂ) * dh) / ((a : ℂ) * dv)) ≠ 0 := by
  apply fx_p2_arg_ne_of_sq_neg
  have hX : φy * dv ^ 2 ≠ 0 := by intro h; rw [h] at hv; simp at hv
  have hdv : dv ≠ 0 := by rintro rfl; simp at hX
  have hφ0 : φy ≠ 0 := by rintro rfl; simp at hX
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have : (-((b : ℂ) * dh) / ((a : ℂ) * dv)) ^ 2 = (((b / a) ^ 2 : ℝ) : ℂ) * (φy * dv ^ 2)⁻¹ := by
    have hdh2 : dh ^ 2 = 1 / φy := by field_simp; linear_combination hh
    rw [div_pow, mul_pow, neg_sq, mul_pow, hdh2]
    push_cast
    field_simp
  rw [this, Complex.re_ofReal_mul, Complex.inv_re]
  have hn : 0 < Complex.normSq (φy * dv ^ 2) := Complex.normSq_pos.2 hX
  exact mul_neg_of_pos_of_neg (by positivity) (div_neg_of_neg_of_pos hv hn)

/-- **The star chain.**  A leaf arc from a crossing of edge `i` to a crossing of edge `j` (both
incident to the zero `q`, normalised to start at `q`), closed up by the two edge pieces through `q`,
is a closed chain whose corner at `q` is blunt. -/
theorem fx_p2_star_chain {φ : ℂ → ℂ} {γ ei ej : ℝ → ℂ} {T t₁ t₂ σ₁ σ₂ : ℝ} {q : ℂ}
    (hγ : fx_p2_htrajP φ γ T) (hγinj : InjOn γ (Icc 0 T)) (ht₁0 : 0 ≤ t₁) (ht₁₂ : t₁ < t₂)
    (ht₂T : t₂ ≤ T) (hq : q ∈ unitDisc) (hq0 : φ q = 0)
    (hei0 : ei 0 = q) (heiv : IsVerticalArc φ ei 0 1) (heis : ContDiffOn ℝ 1 ei (Ico 0 1))
    (heii : InjOn ei (Ioo 0 1)) (heim : ∀ t ∈ Ioo (0 : ℝ) 1, ei t ∈ unitDisc)
    (hej0 : ej 0 = q) (hejv : IsVerticalArc φ ej 0 1) (hejs : ContDiffOn ℝ 1 ej (Ico 0 1))
    (heji : InjOn ej (Ioo 0 1)) (hejm : ∀ t ∈ Ioo (0 : ℝ) 1, ej t ∈ unitDisc)
    (hσ₁ : σ₁ ∈ Ioo (0 : ℝ) 1) (hy : ei σ₁ = γ t₁) (hσ₂ : σ₂ ∈ Ioo (0 : ℝ) 1) (hy' : ej σ₂ = γ t₂)
    (hij : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Ioo (0 : ℝ) 1, ei s ≠ ej t)
    (hoffi : ∀ t ∈ Ioo t₁ t₂, ∀ s ∈ Ioo (0 : ℝ) 1, γ t ≠ ei s)
    (hoffj : ∀ t ∈ Ioo t₁ t₂, ∀ s ∈ Ioo (0 : ℝ) 1, γ t ≠ ej s)
    (heit0 : derivWithin ei (Icc 0 1) 0 ≠ 0) (hejt0 : derivWithin ej (Icc 0 1) 0 ≠ 0)
    (hbl : ∃ m : ℕ, meromorphicOrderAt φ q = (m : ℤ) ∧
      fx_p2_bluntR m (derivWithin ej (Icc 0 1) 0 / derivWithin ei (Icc 0 1) 0)) :
    ∃ side : Fin 3 → ℝ → ℂ, fx_IsChain φ side ∧ fx_IsBlunt φ side 2 := by
  have hL : 0 < t₂ - t₁ := sub_pos.2 ht₁₂
  have hσ₁0 := hσ₁.1
  have hσ₂0 := hσ₂.1
  set dγ := derivWithin γ (Icc 0 T) with hdγ
  set dei := derivWithin ei (Icc 0 1) with hdei
  set dej := derivWithin ej (Icc 0 1) with hdej
  have hmap0 : ∀ τ ∈ Icc (0 : ℝ) 1, t₁ + (t₂ - t₁) * τ ∈ Icc 0 T :=
    fun τ hτ => ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  have hd0 : ∀ τ ∈ Icc (0 : ℝ) 1, derivWithin (fun τ => γ (t₁ + (t₂ - t₁) * τ)) (Icc 0 1) τ =
      ((t₂ - t₁ : ℝ) : ℂ) * dγ (t₁ + (t₂ - t₁) * τ) :=
    fun τ hτ => fx_p2_derivWithin_affine (fx_p2_hasDerivWithinAt_of_contDiffOn hγ.2.1) zero_lt_one
      hmap0 hτ
  obtain ⟨p1s, p1c, p1m, p1d⟩ := fx_p2_npiece hejv hejs hejm (hej0 ▸ hq) hσ₂ (α := σ₂) (β := -σ₂)
    (neg_ne_zero.2 hσ₂0.ne') (fun τ hτ => ⟨by nlinarith [hτ.2], by nlinarith [hτ.1]⟩)
    (fun τ hτ => ⟨by nlinarith [hτ.2], by nlinarith [hτ.1, hσ₂.2]⟩)
  obtain ⟨p2s, p2c, p2m, p2d⟩ := fx_p2_npiece heiv heis heim (hei0 ▸ hq) hσ₁ (α := 0) (β := σ₁)
    hσ₁0.ne' (fun τ hτ => ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩)
    (fun τ hτ => ⟨by nlinarith [hτ.1], by nlinarith [hτ.2, hσ₁.2]⟩)
  -- regularity along the vertical edges
  have hreg_i : ∀ s ∈ Ioo (0 : ℝ) 1, φ (ei s) ≠ 0 := fun s hs => (heiv s hs).2.2.1
  have hreg_j : ∀ s ∈ Ioo (0 : ℝ) 1, φ (ej s) ≠ 0 := fun s hs => (hejv s hs).2.2.1
  have hγreg : ∀ t ∈ Icc 0 T, φ (γ t) ≠ 0 := fun t ht => (hγ.2.2.1 t ht).2
  have hmemI : ∀ τ ∈ Ioo (0 : ℝ) 1, t₁ + (t₂ - t₁) * τ ∈ Ioo t₁ t₂ :=
    fun τ hτ => ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  have hI1 : ∀ τ ∈ Ioo (0 : ℝ) 1, σ₂ + -σ₂ * τ ∈ Ioo (0 : ℝ) 1 :=
    fun τ hτ => ⟨by nlinarith [hτ.2], by nlinarith [hτ.1, hσ₂.2]⟩
  have hI2 : ∀ τ ∈ Ioo (0 : ℝ) 1, 0 + σ₁ * τ ∈ Ioo (0 : ℝ) 1 :=
    fun τ hτ => ⟨by nlinarith [hτ.1], by nlinarith [hτ.2, hσ₁.2]⟩
  have ht₁I : t₁ ∈ Icc 0 T := ⟨ht₁0, by linarith⟩
  have ht₂I : t₂ ∈ Icc 0 T := ⟨by linarith, ht₂T⟩
  have hγq : ∀ t ∈ Icc 0 T, γ t ≠ q := fun t ht h => hγreg t ht (by rw [h]; exact hq0)
  have heiq : ∀ s ∈ Ioo (0 : ℝ) 1, ei s ≠ q := fun s hs h => hreg_i s hs (by rw [h]; exact hq0)
  have hejq : ∀ s ∈ Ioo (0 : ℝ) 1, ej s ≠ q := fun s hs h => hreg_j s hs (by rw [h]; exact hq0)
  -- derivatives at the ends
  have hγd1 := hγ.2.2.2 t₁ ht₁I
  have hγd2 := hγ.2.2.2 t₂ ht₂I
  have hdγ1 : dγ t₁ ≠ 0 := by intro h; rw [← hdγ, h] at hγd1; simp at hγd1
  have hdγ2 : dγ t₂ ≠ 0 := by intro h; rw [← hdγ, h] at hγd2; simp at hγd2
  have hei_d : ∀ s ∈ Ioo (0 : ℝ) 1, dei s = deriv ei s := fun s hs =>
    (fx_p2_deriv_eq_derivWithin hs).symm
  have hej_d : ∀ s ∈ Ioo (0 : ℝ) 1, dej s = deriv ej s := fun s hs =>
    (fx_p2_deriv_eq_derivWithin hs).symm
  have hdei1 : dei σ₁ ≠ 0 := by rw [hei_d σ₁ hσ₁]; exact (heiv σ₁ hσ₁).2.1
  have hdej2 : dej σ₂ ≠ 0 := by rw [hej_d σ₂ hσ₂]; exact (hejv σ₂ hσ₂).2.1
  have e00 : derivWithin (fun τ => γ (t₁ + (t₂ - t₁) * τ)) (Icc 0 1) 0 =
      ((t₂ - t₁ : ℝ) : ℂ) * dγ t₁ := by
    rw [hd0 0 ⟨le_rfl, zero_le_one⟩, mul_zero, add_zero]
  have e01 : derivWithin (fun τ => γ (t₁ + (t₂ - t₁) * τ)) (Icc 0 1) 1 =
      ((t₂ - t₁ : ℝ) : ℂ) * dγ t₂ := by
    rw [hd0 1 ⟨zero_le_one, le_rfl⟩, mul_one, add_sub_cancel]
  have e10 : derivWithin (fun τ => ej (σ₂ + -σ₂ * τ)) (Icc 0 1) 0 = ((-σ₂ : ℝ) : ℂ) * dej σ₂ := by
    rw [p1d 0 ⟨le_rfl, zero_le_one⟩, mul_zero, add_zero]
  have e11 : derivWithin (fun τ => ej (σ₂ + -σ₂ * τ)) (Icc 0 1) 1 = ((-σ₂ : ℝ) : ℂ) * dej 0 := by
    rw [p1d 1 ⟨zero_le_one, le_rfl⟩, mul_one, add_neg_cancel]
  have e20 : derivWithin (fun τ => ei (0 + σ₁ * τ)) (Icc 0 1) 0 = ((σ₁ : ℝ) : ℂ) * dei 0 := by
    rw [p2d 0 ⟨le_rfl, zero_le_one⟩, mul_zero, add_zero]
  have e21 : derivWithin (fun τ => ei (0 + σ₁ * τ)) (Icc 0 1) 1 = ((σ₁ : ℝ) : ℂ) * dei σ₁ := by
    rw [p2d 1 ⟨zero_le_one, le_rfl⟩, mul_one, zero_add]
  have hσ₁c : ((σ₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hσ₁0.ne'
  have hσ₂c : ((-σ₂ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (neg_ne_zero.2 hσ₂0.ne')
  have hLc : ((t₂ - t₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  -- the blunt corner at `q`
  obtain ⟨m, hm, hr⟩ := hbl
  have hratio : -(((-σ₂ : ℝ) : ℂ) * dej 0) / (((σ₁ : ℝ) : ℂ) * dei 0) =
      ((σ₂ / σ₁ : ℝ) : ℂ) * (dej 0 / dei 0) := by
    push_cast; field_simp
  obtain ⟨hne2, hlo2, hhi2⟩ := fx_p2_bluntRatio hr (div_pos hσ₂0 hσ₁0)
  set S0 : ℝ → ℂ := fun τ => γ (t₁ + (t₂ - t₁) * τ) with hS0
  set S1 : ℝ → ℂ := fun τ => ej (σ₂ + -σ₂ * τ) with hS1
  set S2 : ℝ → ℂ := fun τ => ei (0 + σ₁ * τ) with hS2
  refine ⟨![S0, S1, S2], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro k
    fin_cases k
    · exact fx_p2_htrajP_straight hγ ht₁0 ht₁₂ ht₂T
    · exact p1s
    · exact p2s
  · intro k
    fin_cases k
    · exact fx_p2_contDiffOn_affine hγ.2.1 hmap0
    · exact p1c
    · exact p2c
  · intro k
    fin_cases k
    · rintro _ ⟨τ, hτ, rfl⟩
      exact (hγ.2.2.1 _ (hmap0 τ hτ)).1
    · exact p1m
    · exact p2m
  · intro k
    fin_cases k
    · show γ (t₁ + (t₂ - t₁) * 1) = ej (σ₂ + -σ₂ * 0)
      rw [mul_one, add_sub_cancel, mul_zero, add_zero, hy']
    · show ej (σ₂ + -σ₂ * 1) = ei (0 + σ₁ * 0)
      rw [mul_one, add_neg_cancel, mul_zero, add_zero, hej0, hei0]
    · show ei (0 + σ₁ * 1) = γ (t₁ + (t₂ - t₁) * 0)
      rw [mul_one, zero_add, mul_zero, add_zero, hy]
  · refine fx_p2_simple_of ?_ ?_ ?_ ?_
    · intro k
      fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, hS0, hS1, hS2]
      · intro s hs t ht h
        have := hγinj (hmap0 s (Ico_subset_Icc_self hs)) (hmap0 t (Ico_subset_Icc_self ht)) h
        exact mul_left_cancel₀ hL.ne' (by linarith)
      · intro s hs t ht h
        have h1 : σ₂ + -σ₂ * s ∈ Ioo (0 : ℝ) 1 := ⟨by nlinarith [hs.2], by nlinarith [hs.1, hσ₂.2]⟩
        have h2 : σ₂ + -σ₂ * t ∈ Ioo (0 : ℝ) 1 := ⟨by nlinarith [ht.2], by nlinarith [ht.1, hσ₂.2]⟩
        have := heji h1 h2 h
        have : σ₂ * s = σ₂ * t := by linarith
        exact mul_left_cancel₀ hσ₂0.ne' this
      · intro s hs t ht h
        simp only at h
        rcases eq_or_lt_of_le hs.1 with hs0 | hs0 <;> rcases eq_or_lt_of_le ht.1 with ht0 | ht0
        · rw [← hs0, ← ht0]
        · rw [← hs0, mul_zero, add_zero, hei0] at h
          exact absurd h.symm (heiq _ (hI2 t ⟨ht0, ht.2⟩))
        · rw [← ht0, mul_zero, add_zero, hei0] at h
          exact absurd h (heiq _ (hI2 s ⟨hs0, hs.2⟩))
        · have := heii (hI2 s ⟨hs0, hs.2⟩) (hI2 t ⟨ht0, ht.2⟩) h
          exact mul_left_cancel₀ hσ₁0.ne' (by linarith)
    · intro k l h
      fin_cases k <;> fin_cases l <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_zero, add_zero, hei0,
        hS0, hS1, hS2] at h ⊢
      · exact absurd (hy.trans h) (hij σ₁ hσ₁ σ₂ hσ₂)
      · exact absurd h (hγq t₁ ht₁I)
      · exact absurd (hy.trans h.symm) (hij σ₁ hσ₁ σ₂ hσ₂)
      · exact absurd h (hejq σ₂ hσ₂)
      · exact absurd h.symm (hγq t₁ ht₁I)
      · exact absurd h.symm (hejq σ₂ hσ₂)
    · intro k l s hs
      fin_cases k <;> fin_cases l <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_zero, add_zero, hei0,
        hS0, hS1, hS2]
      · intro h
        have := hγinj ht₁I (hmap0 s (Ioo_subset_Icc_self hs)) h
        nlinarith [hs.1]
      · intro h
        exact hij σ₁ hσ₁ _ (hI1 s hs) (by rw [hy, h])
      · intro h
        have := heii hσ₁ (hI2 s hs) (by rw [hy, h])
        nlinarith [hs.2]
      · intro h
        exact hoffj _ (hmemI s hs) σ₂ hσ₂ (by rw [← h, hy'])
      · intro h
        have := heji hσ₂ (hI1 s hs) h
        nlinarith [hs.1]
      · intro h
        exact hij _ (hI2 s hs) σ₂ hσ₂ (by rw [← h])
      · intro h
        exact hγq _ (hmap0 s (Ioo_subset_Icc_self hs)) h.symm
      · intro h
        exact hejq _ (hI1 s hs) h.symm
      · intro h
        exact heiq _ (hI2 s hs) h.symm
    · intro k l hkl s hs t ht
      fin_cases k <;> fin_cases l <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, ne_eq, not_true_eq_false,
        hS0, hS1, hS2] at hkl ⊢
      · exact fun h => hoffj _ (hmemI s hs) _ (hI1 t ht) h
      · exact fun h => hoffi _ (hmemI s hs) _ (hI2 t ht) h
      · exact fun h => hoffj _ (hmemI t ht) _ (hI1 s hs) h.symm
      · exact fun h => hij _ (hI2 t ht) _ (hI1 s hs) h.symm
      · exact fun h => hoffi _ (hmemI t ht) _ (hI2 s hs) h.symm
      · exact fun h => hij _ (hI2 s hs) _ (hI1 t ht) h
  · intro k
    fin_cases k
    · show derivWithin (fun τ => γ (t₁ + (t₂ - t₁) * τ)) (Icc 0 1) 0 ≠ 0
      rw [e00]; exact mul_ne_zero hLc hdγ1
    · show derivWithin (fun τ => ej (σ₂ + -σ₂ * τ)) (Icc 0 1) 0 ≠ 0
      rw [e10]; exact mul_ne_zero hσ₂c hdej2
    · show derivWithin (fun τ => ei (0 + σ₁ * τ)) (Icc 0 1) 0 ≠ 0
      rw [e20]; exact mul_ne_zero hσ₁c heit0
  · intro k
    fin_cases k
    · show derivWithin (fun τ => γ (t₁ + (t₂ - t₁) * τ)) (Icc 0 1) 1 ≠ 0
      rw [e01]; exact mul_ne_zero hLc hdγ2
    · show derivWithin (fun τ => ej (σ₂ + -σ₂ * τ)) (Icc 0 1) 1 ≠ 0
      rw [e11]; exact mul_ne_zero hσ₂c hejt0
    · show derivWithin (fun τ => ei (0 + σ₁ * τ)) (Icc 0 1) 1 ≠ 0
      rw [e21]; exact mul_ne_zero hσ₁c hdei1
  · intro k
    fin_cases k
    · show arg (-(derivWithin (fun τ => ei (0 + σ₁ * τ)) (Icc 0 1) 1) /
        derivWithin (fun τ => γ (t₁ + (t₂ - t₁) * τ)) (Icc 0 1) 0) ≠ 0
      rw [e21, e00]
      have hv : (φ (γ t₁) * dei σ₁ ^ 2).re < 0 := by
        rw [← hy, hei_d σ₁ hσ₁]; exact (heiv σ₁ hσ₁).2.2.2.2
      exact fx_p2_corner_hv hσ₁0.ne' hL.ne' hv hγd1
    · show arg (-(derivWithin (fun τ => γ (t₁ + (t₂ - t₁) * τ)) (Icc 0 1) 1) /
        derivWithin (fun τ => ej (σ₂ + -σ₂ * τ)) (Icc 0 1) 0) ≠ 0
      rw [e01, e10]
      have hv : (φ (γ t₂) * dej σ₂ ^ 2).re < 0 := by
        rw [← hy', hej_d σ₂ hσ₂]; exact (hejv σ₂ hσ₂).2.2.2.2
      exact fx_p2_corner_vh (neg_ne_zero.2 hσ₂0.ne') hL.ne' hv hγd2
    · show arg (-(derivWithin (fun τ => ej (σ₂ + -σ₂ * τ)) (Icc 0 1) 1) /
        derivWithin (fun τ => ei (0 + σ₁ * τ)) (Icc 0 1) 0) ≠ 0
      rw [e11, e20, hratio]
      exact hne2
  · have h2 : (![S0, S1, S2] : Fin 3 → ℝ → ℂ) 2 = S2 := rfl
    have h21 : (![S0, S1, S2] : Fin 3 → ℝ → ℂ) (2 - 1) = S1 := rfl
    have hang : fx_chainAngle (![S0, S1, S2] : Fin 3 → ℝ → ℂ) 2 =
        (if 0 < arg (((σ₂ / σ₁ : ℝ) : ℂ) * (dej 0 / dei 0)) then
          arg (((σ₂ / σ₁ : ℝ) : ℂ) * (dej 0 / dei 0))
        else arg (((σ₂ / σ₁ : ℝ) : ℂ) * (dej 0 / dei 0)) + 2 * π) := by
      unfold fx_chainAngle
      rw [h21, h2, e11, e20, hratio]
    refine ⟨m, ?_, ?_, ?_⟩
    · rw [h2]
      show meromorphicOrderAt φ (ei (0 + σ₁ * 0)) = (m : ℤ)
      rw [mul_zero, add_zero, hei0]
      exact hm
    · rw [hang]; exact hlo2
    · rw [hang]; exact hhi2
/-- **Crossing times are closed**: the times at which a trajectory lies on an edge of the forest
form a closed set (near its ends the edge tends to a zero or leaves every compact subset of `Δ`,
so it meets the compact trajectory only in a compact sub-arc). -/
theorem fx_p2_cross_closed {φ : ℂ → ℂ} {c : ℝ → ℂ} {s₀ : ℂ} {d₀ : Option ℂ}
    (hsm : ContDiffOn ℝ 1 c (Ico 0 1)) (hsrc : c 0 = s₀ ∧ s₀ ∈ unitDisc ∧ φ s₀ = 0)
    (hsad : ∀ q', d₀ = some q' → q' ∈ unitDisc ∧ φ q' = 0 ∧ q' ≠ s₀ ∧
      ContDiffOn ℝ 1 c (Icc 0 1) ∧ c 1 = q' ∧ derivWithin c (Icc 0 1) 1 ≠ 0)
    (hbdry : d₀ = none → ∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc →
      ∀ᶠ t in 𝓝[<] (1 : ℝ), c t ∉ K)
    {γ : ℝ → ℂ} {T : ℝ} (hγ : fx_p2_htrajP φ γ T) :
    IsClosed {t | t ∈ Icc 0 T ∧ γ t ∈ c '' Ioo 0 1} := by
  set K := γ '' Icc 0 T with hKdef
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hγ.2.1.continuousOn
  have hKreg : ∀ w ∈ K, φ w ≠ 0 := by
    rintro _ ⟨t, ht, rfl⟩
    exact (hγ.2.2.1 t ht).2
  have hKD : K ⊆ unitDisc := by
    rintro _ ⟨t, ht, rfl⟩
    exact (hγ.2.2.1 t ht).1
  have hKc : IsOpen Kᶜ := hK.isClosed.isOpen_compl
  -- near the source
  have h0 : ∀ᶠ s in 𝓝[>] (0 : ℝ), c s ∉ K := by
    have hcont : Tendsto c (𝓝[>] 0) (𝓝 s₀) := by
      rw [← hsrc.1]
      exact (hsm.continuousOn.continuousWithinAt ⟨le_rfl, zero_lt_one⟩).mono_of_mem_nhdsWithin
        (mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) Ioo_subset_Ico_self)
    exact hcont.eventually (hKc.mem_nhds fun h => hKreg s₀ h hsrc.2.2)
  -- near the other end
  have h1 : ∀ᶠ s in 𝓝[<] (1 : ℝ), c s ∉ K := by
    cases hd : d₀ with
    | none => exact hbdry hd K hK hKD
    | some q' =>
      obtain ⟨-, hq'0, -, hsm', hc1, -⟩ := hsad q' hd
      have hcont : Tendsto c (𝓝[<] 1) (𝓝 q') := by
        rw [← hc1]
        exact (hsm'.continuousOn.continuousWithinAt ⟨zero_le_one, le_rfl⟩).mono_of_mem_nhdsWithin
          (mem_of_superset (Ioo_mem_nhdsLT zero_lt_one) Ioo_subset_Icc_self)
      exact hcont.eventually (hKc.mem_nhds fun h => hKreg q' h hq'0)
  obtain ⟨a, ha, haS⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h0
  obtain ⟨b, hb, hbS⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 h1
  set a' := min a (1 / 2) with ha'
  set b' := max b (1 / 2) with hb'
  have ha'0 : 0 < a' := lt_min ha (by norm_num)
  have ha'h : a' ≤ 1 / 2 := min_le_right _ _
  have hb'1 : b' < 1 := max_lt hb (by norm_num)
  have hb'h : 1 / 2 ≤ b' := le_max_right _ _
  have hsub : Icc a' b' ⊆ Ico (0 : ℝ) 1 := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have heq : {t | t ∈ Icc 0 T ∧ γ t ∈ c '' Ioo 0 1} = Icc 0 T ∩ γ ⁻¹' (c '' Icc a' b') := by
    ext t
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_image]
    constructor
    · rintro ⟨ht, s, hs, hst⟩
      refine ⟨ht, s, ⟨?_, ?_⟩, hst⟩
      · by_contra h
        push Not at h
        exact haS ⟨hs.1, lt_of_lt_of_le h (min_le_left _ _)⟩ (hst ▸ ⟨t, ht, rfl⟩)
      · by_contra h
        push Not at h
        exact hbS ⟨lt_of_le_of_lt (le_max_left _ _) h, hs.2⟩ (hst ▸ ⟨t, ht, rfl⟩)
    · rintro ⟨ht, s, hs, hst⟩
      exact ⟨ht, s, ⟨by linarith [hs.1], by linarith [hs.2]⟩, hst⟩
  rw [heq]
  exact hγ.2.1.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc
    (isCompact_Icc.image_of_continuousOn (hsm.continuousOn.mono hsub)).isClosed

/-- **The star lemma** (helper form of `fx_star`, with Teichmüller's exclusion principle and the
fields of the forest as hypotheses). -/
theorem fx_p2_star_core {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hCF : ∀ {n : ℕ} [NeZero n] (side : Fin n → ℝ → ℂ), fx_IsChain φ side →
      3 ≤ {j | ¬ fx_IsBlunt φ side j}.ncard)
    {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hvert : ∀ i, IsVerticalArc φ (par i) 0 1)
    (hmem : ∀ i, ∀ t ∈ Ioo (0 : ℝ) 1, par i t ∈ unitDisc)
    (hinj : ∀ i, InjOn (par i) (Ioo 0 1))
    (hsmooth : ∀ i, ContDiffOn ℝ 1 (par i) (Ico 0 1))
    (hsrc : ∀ i, par i 0 = src i ∧ src i ∈ unitDisc ∧ φ (src i) = 0)
    (hsrc_tan : ∀ i, derivWithin (par i) (Icc 0 1) 0 ≠ 0)
    (hsaddle : ∀ i q, dst i = some q → q ∈ unitDisc ∧ φ q = 0 ∧ q ≠ src i ∧
      ContDiffOn ℝ 1 (par i) (Icc 0 1) ∧ par i 1 = q ∧ derivWithin (par i) (Icc 0 1) 1 ≠ 0)
    (hbdry : ∀ i, dst i = none → ∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc →
      ∀ᶠ t in 𝓝[<] (1 : ℝ), par i t ∉ K)
    (hdisj : ∀ i j, i ≠ j → Disjoint (par i '' Ioo 0 1) (par j '' Ioo 0 1))
    (hblunt : ∀ q ∈ unitDisc, φ q = 0 → ∀ i j, (src i = q ∨ dst i = some q) →
      (src j = q ∨ dst j = some q) → i ≠ j → ∃ m : ℕ, meromorphicOrderAt φ q = (m : ℤ) ∧
        fx_p2_bluntR m (fx_p2_oT par src i q / fx_p2_oT par src j q))
    {z q : ℂ} {i j : ι} (hi : src i = q ∨ dst i = some q) (hj : src j = q ∨ dst j = some q)
    (hzi : (fx_p2_leafP φ z ∩ par i '' Ioo 0 1).Nonempty)
    (hzj : (fx_p2_leafP φ z ∩ par j '' Ioo 0 1).Nonempty) : i = j := by
  classical
  by_contra hij
  have hCF1 : ∀ side : Fin 1 → ℝ → ℂ, ¬ fx_IsChain φ side := fun side hC => by
    have h3 := hCF side hC
    have h1 : {j : Fin 1 | ¬ fx_IsBlunt φ side j}.ncard ≤ 1 := by
      calc {j : Fin 1 | ¬ fx_IsBlunt φ side j}.ncard ≤ (univ : Set (Fin 1)).ncard :=
            Set.ncard_le_ncard (subset_univ _)
        _ = 1 := by simp
    omega
  obtain ⟨x, hxz, σ₀, hσ₀, rfl⟩ := hzi
  obtain ⟨x', hx'z, σ₀', hσ₀', rfl⟩ := hzj
  have hnot : ∀ w, w ∈ par i '' Ioo 0 1 → w ∉ par j '' Ioo 0 1 :=
    fun w h1 h2 => Set.disjoint_left.1 (hdisj i j hij) h1 h2
  obtain ⟨γ, T, hγ, hγ0, hγT⟩ : ∃ (γ : ℝ → ℂ) (T : ℝ), fx_p2_htrajP φ γ T ∧ γ 0 = par i σ₀ ∧
      γ T = par j σ₀' := by
    rcases fx_p2_leafP_trans hφ (fx_p2_leafP_symm hxz) hx'z with ⟨h, -, -⟩ | h
    · exact absurd ⟨σ₀', hσ₀', rfl⟩ (hnot _ ⟨σ₀, hσ₀, h.symm⟩)
    · exact h
  have hγinj := fx_p2_htrajP_injOn hφ hCF1 hγ
  have hEi : IsClosed {t | t ∈ Icc 0 T ∧ γ t ∈ par i '' Ioo 0 1} :=
    fx_p2_cross_closed (hsmooth i) (hsrc i) (hsaddle i) (hbdry i) hγ
  have hEj : IsClosed {t | t ∈ Icc 0 T ∧ γ t ∈ par j '' Ioo 0 1} :=
    fx_p2_cross_closed (hsmooth j) (hsrc j) (hsaddle j) (hbdry j) hγ
  set Ei := {t | t ∈ Icc 0 T ∧ γ t ∈ par i '' Ioo 0 1} with hEidef
  set Ej := {t | t ∈ Icc 0 T ∧ γ t ∈ par j '' Ioo 0 1} with hEjdef
  have hT0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hγ.1.le⟩
  have hTT : T ∈ Icc 0 T := ⟨hγ.1.le, le_rfl⟩
  have hEjT : T ∈ Ej := ⟨hTT, by rw [hγT]; exact ⟨σ₀', hσ₀', rfl⟩⟩
  have hEjb : BddBelow Ej := ⟨0, fun t ht => ht.1.1⟩
  set t₂ := sInf Ej with ht₂def
  have ht₂ : t₂ ∈ Ej := hEj.csInf_mem ⟨T, hEjT⟩ hEjb
  have ht₂le : ∀ t ∈ Ej, t₂ ≤ t := fun t ht => csInf_le hEjb ht
  have ht₂0 : 0 < t₂ := by
    rcases eq_or_lt_of_le ht₂.1.1 with h | h
    · exfalso
      have := ht₂.2
      rw [← h, hγ0] at this
      exact hnot _ ⟨σ₀, hσ₀, rfl⟩ this
    · exact h
  set Ei' := Ei ∩ Icc 0 t₂ with hEi'def
  have hEi'c : IsClosed Ei' := hEi.inter isClosed_Icc
  have hEi'0 : (0 : ℝ) ∈ Ei' := ⟨⟨hT0, by rw [hγ0]; exact ⟨σ₀, hσ₀, rfl⟩⟩, le_rfl, ht₂0.le⟩
  have hEi'b : BddAbove Ei' := ⟨t₂, fun t ht => ht.2.2⟩
  set t₁ := sSup Ei' with ht₁def
  have ht₁ : t₁ ∈ Ei' := hEi'c.csSup_mem ⟨0, hEi'0⟩ hEi'b
  have ht₁ge : ∀ t ∈ Ei', t ≤ t₁ := fun t ht => le_csSup hEi'b ht
  have ht₁₂ : t₁ < t₂ := by
    rcases eq_or_lt_of_le ht₁.2.2 with h | h
    · exfalso
      have h1 := ht₁.1.2
      rw [h] at h1
      exact hnot _ h1 ht₂.2
    · exact h
  have ht₁0 : 0 ≤ t₁ := ht₁.2.1
  have ht₂T : t₂ ≤ T := ht₂.1.2
  have hoffi : ∀ t ∈ Ioo t₁ t₂, γ t ∉ par i '' Ioo 0 1 := fun t ht h =>
    absurd (ht₁ge t ⟨⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, h⟩, by linarith [ht.1], ht.2.le⟩)
      (not_le.2 ht.1)
  have hoffj : ∀ t ∈ Ioo t₁ t₂, γ t ∉ par j '' Ioo 0 1 := fun t ht h =>
    absurd (ht₂le t ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, h⟩) (not_le.2 ht.2)
  -- normalised edges at `q`
  obtain ⟨ei, hei0, hq, hq0, heiv, heis, heii, heim, heiI, heit, heit0⟩ :=
    fx_p2_normEdge (hvert i) (hmem i) (hinj i) (hsmooth i) (hsrc i) (hsrc_tan i) (hsaddle i) hi
  obtain ⟨ej, hej0, -, -, hejv, hejs, heji, hejm, hejI, hejt, hejt0⟩ :=
    fx_p2_normEdge (hvert j) (hmem j) (hinj j) (hsmooth j) (hsrc j) (hsrc_tan j) (hsaddle j) hj
  obtain ⟨σ₁, hσ₁, hy⟩ : ∃ σ₁ ∈ Ioo (0 : ℝ) 1, ei σ₁ = γ t₁ := by
    have h := ht₁.1.2
    rw [← heiI] at h
    obtain ⟨s, hs, hs'⟩ := h
    exact ⟨s, hs, hs'⟩
  obtain ⟨σ₂, hσ₂, hy'⟩ : ∃ σ₂ ∈ Ioo (0 : ℝ) 1, ej σ₂ = γ t₂ := by
    have h := ht₂.2
    rw [← hejI] at h
    obtain ⟨s, hs, hs'⟩ := h
    exact ⟨s, hs, hs'⟩
  have hij' : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Ioo (0 : ℝ) 1, ei s ≠ ej t := by
    intro s hs t ht h
    have h1 : ei s ∈ par i '' Ioo 0 1 := by rw [← heiI]; exact ⟨s, hs, rfl⟩
    have h2 : ei s ∈ par j '' Ioo 0 1 := by rw [h, ← hejI]; exact ⟨t, ht, rfl⟩
    exact hnot _ h1 h2
  have hoffi' : ∀ t ∈ Ioo t₁ t₂, ∀ s ∈ Ioo (0 : ℝ) 1, γ t ≠ ei s := fun t ht s hs h =>
    hoffi t ht (by rw [h, ← heiI]; exact ⟨s, hs, rfl⟩)
  have hoffj' : ∀ t ∈ Ioo t₁ t₂, ∀ s ∈ Ioo (0 : ℝ) 1, γ t ≠ ej s := fun t ht s hs h =>
    hoffj t ht (by rw [h, ← hejI]; exact ⟨s, hs, rfl⟩)
  have hbl : ∃ m : ℕ, meromorphicOrderAt φ q = (m : ℤ) ∧
      fx_p2_bluntR m (derivWithin ej (Icc 0 1) 0 / derivWithin ei (Icc 0 1) 0) := by
    rw [heit, hejt]
    exact hblunt q hq hq0 j i hj hi (Ne.symm hij)
  obtain ⟨side, hC, hbl2⟩ := fx_p2_star_chain hγ hγinj ht₁0 ht₁₂ ht₂T hq hq0 hei0 heiv heis heii
    heim hej0 hejv hejs heji hejm hσ₁ hy hσ₂ hy' hij' hoffi' hoffj' heit0 hejt0 hbl
  have h3 := hCF side hC
  have hsub : {k : Fin 3 | ¬ fx_IsBlunt φ side k} ⊆ {0, 1} := by
    intro k hk
    fin_cases k
    · simp
    · simp
    · exact absurd hbl2 hk
  have h2 : {k : Fin 3 | ¬ fx_IsBlunt φ side k}.ncard ≤ 2 :=
    (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (by rw [Set.ncard_pair (by decide)])
  omega
/-! ### No cycles of saddle connections -/

/-- The whole edge `c` oriented from its end `x` (a verbatim orientation switch). -/
def fx_p2_wedge (c : ℝ → ℂ) (s₀ x : ℂ) : ℝ → ℂ :=
  fun τ => if s₀ = x then c τ else c (1 - τ)

/-- An edge incident to two distinct points is a saddle connection between them. -/
theorem fx_p2_two_ends {ι : Type} {src : ι → ℂ} {dst : ι → Option ℂ} {i : ι} {x y : ℂ}
    (hx : src i = x ∨ dst i = some x) (hy : src i = y ∨ dst i = some y) (hxy : x ≠ y) :
    ∃ q, dst i = some q ∧ ((x = src i ∧ y = q) ∨ (x = q ∧ y = src i)) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact absurd (hx.symm.trans hy) hxy
  · exact ⟨y, hy, Or.inl ⟨hx.symm, rfl⟩⟩
  · exact ⟨x, hx, Or.inr ⟨rfl, hy.symm⟩⟩
  · exact absurd (Option.some_injective _ (hx.symm.trans hy)) hxy

/-- **Facts on an oriented saddle connection** `c` from `x` to `y` (`{x, y} = {c 0, c 1}`). -/
theorem fx_p2_wedge_facts {φ : ℂ → ℂ} {c : ℝ → ℂ} {s₀ q x y : ℂ}
    (hv : IsVerticalArc φ c 0 1) (hmem : ∀ t ∈ Ioo (0 : ℝ) 1, c t ∈ unitDisc)
    (hinj : InjOn c (Ioo 0 1)) (hsm : ContDiffOn ℝ 1 c (Icc 0 1)) (hc0 : c 0 = s₀)
    (hc1 : c 1 = q) (hs₀ : s₀ ∈ unitDisc) (hq : q ∈ unitDisc) (hsq : q ≠ s₀)
    (hxy : (x = s₀ ∧ y = q) ∨ (x = q ∧ y = s₀)) :
    fx_p2_wedge c s₀ x 0 = x ∧ fx_p2_wedge c s₀ x 1 = y ∧
      IsPhiStraightArc φ (fx_p2_wedge c s₀ x) 0 1 ∧
      ContDiffOn ℝ 1 (fx_p2_wedge c s₀ x) (Icc 0 1) ∧ fx_p2_wedge c s₀ x '' Icc 0 1 ⊆ unitDisc ∧
      derivWithin (fx_p2_wedge c s₀ x) (Icc 0 1) 0 =
        (if s₀ = x then derivWithin c (Icc 0 1) 0 else -derivWithin c (Icc 0 1) 1) ∧
      derivWithin (fx_p2_wedge c s₀ x) (Icc 0 1) 1 =
        -(if s₀ = y then derivWithin c (Icc 0 1) 0 else -derivWithin c (Icc 0 1) 1) ∧
      InjOn (fx_p2_wedge c s₀ x) (Ioo 0 1) ∧ fx_p2_wedge c s₀ x '' Ioo 0 1 = c '' Ioo 0 1 := by
  have hmap : ∀ τ ∈ Icc (0 : ℝ) 1, 1 + (-1) * τ ∈ Icc (0 : ℝ) 1 :=
    fun τ hτ => ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hmem' : c '' Icc 0 1 ⊆ unitDisc := by
    rintro _ ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, hc0]; exact hs₀
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · rw [h1, hc1]; exact hq
    · exact hmem t ⟨h0, h1⟩
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hW : fx_p2_wedge c x x = c := by funext τ; simp [fx_p2_wedge]
    rw [hW, ite_eq_left rfl, ite_eq_right hsq.symm]
    exact ⟨hc0, hc1, (horizontal_vertical_isPhiStraight).2 hv, hsm, hmem', rfl, by ring,
      hinj, rfl⟩
  · have hW : fx_p2_wedge c y x = fun τ => c (1 + (-1) * τ) := by
      funext τ; simp only [fx_p2_wedge, ite_eq_right hsq.symm]; ring_nf
    have hder : ∀ τ ∈ Icc (0 : ℝ) 1, derivWithin (fun τ => c (1 + (-1) * τ)) (Icc 0 1) τ =
        -derivWithin c (Icc 0 1) (1 + (-1) * τ) := by
      intro τ hτ
      rw [fx_p2_derivWithin_affine (fx_p2_hasDerivWithinAt_of_contDiffOn hsm) zero_lt_one hmap hτ]
      simp
    rw [hW, ite_eq_right hsq.symm, ite_eq_left rfl, hder 0 ⟨le_rfl, zero_le_one⟩,
      hder 1 ⟨zero_le_one, le_rfl⟩]
    refine ⟨by simp [hc1], by simp [hc0], fx_p2_straight_affine
      ((horizontal_vertical_isPhiStraight).2 hv) (by norm_num)
      (fun τ hτ => ⟨by linarith [hτ.2], by linarith [hτ.1]⟩), fx_p2_contDiffOn_affine hsm hmap, ?_,
      by simp, by simp, ?_, ?_⟩
    · rintro _ ⟨τ, hτ, rfl⟩
      exact hmem' ⟨_, hmap τ hτ, rfl⟩
    · intro s hs t ht h
      have := hinj ⟨by linarith [hs.2], by linarith [hs.1]⟩
        ⟨by linarith [ht.2], by linarith [ht.1]⟩ h
      linarith
    · ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨1 + (-1) * t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp only; ring_nf⟩

/-- **A cycle of saddle connections** in the graph of the edges of `A` through the finite set `S`
(every edge of `A` at a zero of `S` returns to `S`; at least two such edges at every zero of `S`):
a non-backtracking walk, cut at its first repeated vertex. -/
theorem fx_p2_cycle_exists {ι : Type} {src : ι → ℂ} {dst : ι → Option ℂ} {S : Set ℂ}
    (hSf : S.Finite) (hSne : S.Nonempty) {A : Set ι}
    (hloop : ∀ i q, dst i = some q → q ≠ src i)
    (hA : ∀ q ∈ S, 2 ≤ {i | i ∈ A ∧ (src i = q ∨ dst i = some q)}.ncard)
    (H : ∀ q ∈ S, ∀ i ∈ A, (src i = q → ∃ q', dst i = some q' ∧ q' ∈ S) ∧
      (dst i = some q → src i ∈ S)) :
    ∃ (L : ℕ) (vv : ℕ → ℂ) (ee : ℕ → ι), 2 ≤ L ∧ vv L = vv 0 ∧
      (∀ k < L, vv k ∈ S ∧ ee k ∈ A ∧ (src (ee k) = vv k ∨ dst (ee k) = some (vv k)) ∧
        (src (ee k) = vv (k + 1) ∨ dst (ee k) = some (vv (k + 1))) ∧ vv k ≠ vv (k + 1)) ∧
      (∀ k < L, ∀ l < L, vv k = vv l → k = l) ∧ (∀ k < L, ∀ l < L, ee k = ee l → k = l) := by
  classical
  -- one step of the walk
  have hstep : ∀ p : ℂ × ι, p.1 ∈ S → p.2 ∈ A → (src p.2 = p.1 ∨ dst p.2 = some p.1) →
      ∃ p' : ℂ × ι, p'.1 ∈ S ∧ p'.2 ∈ A ∧ (src p'.2 = p'.1 ∨ dst p'.2 = some p'.1) ∧
        (src p.2 = p'.1 ∨ dst p.2 = some p'.1) ∧ p'.1 ≠ p.1 ∧ p'.2 ≠ p.2 := by
    rintro ⟨q, i⟩ hq hi hinc
    simp only at hq hi hinc ⊢
    -- the other end `q'` of `i`
    obtain ⟨q', hq'S, hinc', hq'q⟩ : ∃ q', q' ∈ S ∧ (src i = q' ∨ dst i = some q') ∧ q' ≠ q := by
      by_cases hs : src i = q
      · obtain ⟨q', hd, hq'⟩ := (H q hq i hi).1 hs
        exact ⟨q', hq', Or.inr hd, fun h => hloop i q' hd (h.trans hs.symm)⟩
      · have hd : dst i = some q := hinc.resolve_left hs
        exact ⟨src i, (H q hq i hi).2 hd, Or.inl rfl, hs⟩
    -- another edge at `q'`
    have h2 := hA q' hq'S
    have hfin := Set.finite_of_ncard_pos (lt_of_lt_of_le (by norm_num) h2)
    obtain ⟨a, ha, b, hb, hab⟩ := (Set.one_lt_ncard hfin).1 (lt_of_lt_of_le (by norm_num) h2)
    by_cases hai : a = i
    · exact ⟨(q', b), hq'S, hb.1, hb.2, hinc', hq'q, fun h => hab (hai.trans h.symm)⟩
    · exact ⟨(q', a), hq'S, ha.1, ha.2, hinc', hq'q, hai⟩
  -- states and the walk
  set St := {p : ℂ × ι // p.1 ∈ S ∧ p.2 ∈ A ∧ (src p.2 = p.1 ∨ dst p.2 = some p.1)}
  let nxt : St → St := fun s => ⟨Classical.choose (hstep s.1 s.2.1 s.2.2.1 s.2.2.2),
    (Classical.choose_spec (hstep s.1 s.2.1 s.2.2.1 s.2.2.2)).1,
    (Classical.choose_spec (hstep s.1 s.2.1 s.2.2.1 s.2.2.2)).2.1,
    (Classical.choose_spec (hstep s.1 s.2.1 s.2.2.1 s.2.2.2)).2.2.1⟩
  have hnxt : ∀ s : St, (src s.1.2 = (nxt s).1.1 ∨ dst s.1.2 = some (nxt s).1.1) ∧
      (nxt s).1.1 ≠ s.1.1 ∧ (nxt s).1.2 ≠ s.1.2 :=
    fun s => (Classical.choose_spec (hstep s.1 s.2.1 s.2.2.1 s.2.2.2)).2.2.2
  obtain ⟨q₀, hq₀⟩ := hSne
  have h2 := hA q₀ hq₀
  obtain ⟨i₀, hi₀⟩ := Set.nonempty_of_ncard_ne_zero
    (s := {i | i ∈ A ∧ (src i = q₀ ∨ dst i = some q₀)}) (by omega)
  set s₀ : St := ⟨(q₀, i₀), hq₀, hi₀.1, hi₀.2⟩
  set w : ℕ → St := fun k => nxt^[k] s₀ with hw
  have hwsucc : ∀ k, w (k + 1) = nxt (w k) := fun k => Function.iterate_succ_apply' nxt k s₀
  set v : ℕ → ℂ := fun k => (w k).1.1 with hv
  set e : ℕ → ι := fun k => (w k).1.2 with he
  have hvS : ∀ k, v k ∈ S := fun k => (w k).2.1
  have heA : ∀ k, e k ∈ A := fun k => (w k).2.2.1
  have hinc0 : ∀ k, src (e k) = v k ∨ dst (e k) = some (v k) := fun k => (w k).2.2.2
  have hinc1 : ∀ k, src (e k) = v (k + 1) ∨ dst (e k) = some (v (k + 1)) := by
    intro k; simp only [hv, he, hwsucc]; exact (hnxt (w k)).1
  have hvne : ∀ k, v (k + 1) ≠ v k := by
    intro k; simp only [hv, hwsucc]; exact (hnxt (w k)).2.1
  have hene : ∀ k, e (k + 1) ≠ e k := by
    intro k; simp only [he, hwsucc]; exact (hnxt (w k)).2.2
  -- the first repetition
  have hrep : ∃ b, ∃ a < b, v a = v b := by
    obtain ⟨m, n, hmn, h⟩ := hSf.exists_lt_map_eq_of_forall_mem hvS
    exact ⟨n, m, hmn, h⟩
  set b := Nat.find hrep with hb
  obtain ⟨a, hab, hvab⟩ := Nat.find_spec hrep
  have hmin : ∀ b' < b, ∀ a' < b', v a' ≠ v b' := by
    intro b' hb' a' ha' h
    exact Nat.find_min hrep hb' ⟨a', ha', h⟩
  -- distinct vertices on `[0, b)`
  have hdist : ∀ k < b, ∀ l < b, v k = v l → k = l := by
    intro k hk l hl h
    rcases lt_trichotomy k l with h' | h' | h'
    · exact absurd h (hmin l hl k h')
    · exact h'
    · exact absurd h.symm (hmin k hk l h')
  refine ⟨b - a, fun k => v (a + k), fun k => e (a + k), ?_, ?_, ?_, ?_, ?_⟩
  · by_contra hL
    have h1 : b = a + 1 := by omega
    exact hvne a (by rw [← h1]; exact hvab.symm)
  · simp only [add_zero]
    rw [show a + (b - a) = b by omega]
    exact hvab.symm
  · intro k hk
    refine ⟨hvS _, heA _, hinc0 _, ?_, ?_⟩
    · show src (e (a + k)) = v (a + (k + 1)) ∨ dst (e (a + k)) = some (v (a + (k + 1)))
      rw [← add_assoc]; exact hinc1 _
    · show v (a + k) ≠ v (a + (k + 1))
      rw [← add_assoc]; exact (hvne _).symm
  · intro k hk l hl h
    have := hdist (a + k) (by omega) (a + l) (by omega) h
    omega
  · intro k hk l hl h
    by_contra hkl
    -- WLOG `k < l`
    have key : ∀ k l : ℕ, k < l → l < b - a → e (a + k) = e (a + l) → False := by
      intro k l hkl hl h
      obtain ⟨q, hq, hends⟩ := fx_p2_two_ends (hinc0 (a + k)) (hinc1 (a + k)) (hvne _).symm
      have hl' := hinc0 (a + l)
      rw [← h] at hl'
      have hv3 : v (a + l) = v (a + k) ∨ v (a + l) = v (a + k + 1) := by
        rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hl' with h3 | h3
        · exact Or.inl (h3.symm.trans h1.symm)
        · exact Or.inr (by rw [h2]; exact Option.some_injective _ (h3.symm.trans hq))
        · exact Or.inr (h3.symm.trans h2.symm)
        · exact Or.inl (by rw [h1]; exact Option.some_injective _ (h3.symm.trans hq))
      rcases hv3 with h3 | h3
      · have := hdist _ (by omega) _ (by omega) h3
        omega
      · have := hdist _ (by omega) _ (by omega) h3
        have hlk : l = k + 1 := by omega
        subst hlk
        exact hene (a + k) (by rw [← add_assoc] at h; exact h.symm)
    rcases lt_or_gt_of_ne hkl with h' | h'
    · exact key k l h' hl h
    · exact key l k h' hk h.symm
/-- **The cycle chain**: a cycle of distinct saddle connections through distinct zeros, each
oriented from one vertex to the next, is a closed chain all of whose corners are blunt. -/
theorem fx_p2_cycle_chain {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ}
    (hvert : ∀ i, IsVerticalArc φ (par i) 0 1)
    (hmem : ∀ i, ∀ t ∈ Ioo (0 : ℝ) 1, par i t ∈ unitDisc)
    (hinj : ∀ i, InjOn (par i) (Ioo 0 1))
    (hsrc : ∀ i, par i 0 = src i ∧ src i ∈ unitDisc ∧ φ (src i) = 0)
    (hsrc_tan : ∀ i, derivWithin (par i) (Icc 0 1) 0 ≠ 0)
    (hsaddle : ∀ i q, dst i = some q → q ∈ unitDisc ∧ φ q = 0 ∧ q ≠ src i ∧
      ContDiffOn ℝ 1 (par i) (Icc 0 1) ∧ par i 1 = q ∧ derivWithin (par i) (Icc 0 1) 1 ≠ 0)
    (hdisj : ∀ i j, i ≠ j → Disjoint (par i '' Ioo 0 1) (par j '' Ioo 0 1))
    (hblunt : ∀ q ∈ unitDisc, φ q = 0 → ∀ i j, (src i = q ∨ dst i = some q) →
      (src j = q ∨ dst j = some q) → i ≠ j → ∃ m : ℕ, meromorphicOrderAt φ q = (m : ℤ) ∧
        fx_p2_bluntR m (fx_p2_oT par src i q / fx_p2_oT par src j q))
    {L : ℕ} [NeZero L] (hL : 2 ≤ L) {vv : ℕ → ℂ} {ee : ℕ → ι} (hcl : vv L = vv 0)
    (hcyc : ∀ k < L, (src (ee k) = vv k ∨ dst (ee k) = some (vv k)) ∧
      (src (ee k) = vv (k + 1) ∨ dst (ee k) = some (vv (k + 1))) ∧ vv k ≠ vv (k + 1))
    (hvd : ∀ k < L, ∀ l < L, vv k = vv l → k = l)
    (hed : ∀ k < L, ∀ l < L, ee k = ee l → k = l) :
    fx_IsChain φ (fun k : Fin L => fx_p2_wedge (par (ee k)) (src (ee k)) (vv k)) ∧
      ∀ k : Fin L,
        fx_IsBlunt φ (fun k : Fin L => fx_p2_wedge (par (ee k)) (src (ee k)) (vv k)) k := by
  classical
  set side : Fin L → ℝ → ℂ := fun k => fx_p2_wedge (par (ee k)) (src (ee k)) (vv k) with hside
  -- the per-edge package
  have hpack : ∀ k < L, ∃ q, dst (ee k) = some q ∧ q ∈ unitDisc ∧ φ q = 0 ∧ q ≠ src (ee k) ∧
      derivWithin (par (ee k)) (Icc 0 1) 1 ≠ 0 ∧
      ((vv k = src (ee k) ∧ vv (k + 1) = q) ∨ (vv k = q ∧ vv (k + 1) = src (ee k))) ∧
      (fx_p2_wedge (par (ee k)) (src (ee k)) (vv k) 0 = vv k ∧
      fx_p2_wedge (par (ee k)) (src (ee k)) (vv k) 1 = vv (k + 1) ∧
      IsPhiStraightArc φ (fx_p2_wedge (par (ee k)) (src (ee k)) (vv k)) 0 1 ∧
      ContDiffOn ℝ 1 (fx_p2_wedge (par (ee k)) (src (ee k)) (vv k)) (Icc 0 1) ∧
      fx_p2_wedge (par (ee k)) (src (ee k)) (vv k) '' Icc 0 1 ⊆ unitDisc ∧
      derivWithin (fx_p2_wedge (par (ee k)) (src (ee k)) (vv k)) (Icc 0 1) 0 =
        (if src (ee k) = vv k then derivWithin (par (ee k)) (Icc 0 1) 0
          else -derivWithin (par (ee k)) (Icc 0 1) 1) ∧
      derivWithin (fx_p2_wedge (par (ee k)) (src (ee k)) (vv k)) (Icc 0 1) 1 =
        -(if src (ee k) = vv (k + 1) then derivWithin (par (ee k)) (Icc 0 1) 0
          else -derivWithin (par (ee k)) (Icc 0 1) 1) ∧
      InjOn (fx_p2_wedge (par (ee k)) (src (ee k)) (vv k)) (Ioo 0 1) ∧
      fx_p2_wedge (par (ee k)) (src (ee k)) (vv k) '' Ioo 0 1 = par (ee k) '' Ioo 0 1) := by
    intro k hk
    obtain ⟨hk0, hk1, hkne⟩ := hcyc k hk
    obtain ⟨q, hq, hends⟩ := fx_p2_two_ends hk0 hk1 hkne
    obtain ⟨hqD, hq0, hqs, hsm, hc1, htan1⟩ := hsaddle (ee k) q hq
    refine ⟨q, hq, hqD, hq0, hqs, htan1, hends, ?_⟩
    exact fx_p2_wedge_facts (hvert _) (hmem _) (hinj _) hsm (hsrc _).1 hc1 (hsrc _).2.1 hqD hqs
      hends
  have hzero : ∀ k < L, vv k ∈ unitDisc ∧ φ (vv k) = 0 := by
    intro k hk
    obtain ⟨q, -, hqD, hq0, -, -, hends, -⟩ := hpack k hk
    rcases hends with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]; exact (hsrc _).2
    · rw [h1]; exact ⟨hqD, hq0⟩
  have hL1 : 1 < L := by omega
  -- index arithmetic
  have hnext : ∀ k : Fin L, vv (((k + 1 : Fin L) : ℕ)) = vv ((k : ℕ) + 1) := by
    intro k
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hL1]
    by_cases h : (k : ℕ) + 1 < L
    · rw [Nat.mod_eq_of_lt h]
    · have : (k : ℕ) + 1 = L := by omega
      rw [this, Nat.mod_self, hcl]
  have hprev : ∀ k : Fin L, vv (((k - 1 : Fin L) : ℕ) + 1) = vv (k : ℕ) := by
    intro k
    rw [← hnext, sub_add_cancel]
  have hreg : ∀ k : Fin L, ∀ s ∈ Ioo (0 : ℝ) 1, φ (side k s) ≠ 0 := by
    intro k s hs
    obtain ⟨q, -, -, -, -, -, -, -, -, -, -, -, -, -, -, himg⟩ := hpack k k.isLt
    have : side k s ∈ par (ee k) '' Ioo 0 1 := himg ▸ ⟨s, hs, rfl⟩
    obtain ⟨t, ht, hts⟩ := this
    rw [← hts]
    exact (hvert _ t ht).2.2.1
  have hv0 : ∀ k : Fin L, side k 0 = vv k := fun k => (hpack k k.isLt).choose_spec.2.2.2.2.2.2.1
  have hint : ∀ k : Fin L, ∀ s ∈ Ioo (0 : ℝ) 1, side k s ∈ par (ee k) '' Ioo 0 1 := by
    intro k s hs
    obtain ⟨q, -, -, -, -, -, -, -, -, -, -, -, -, -, -, himg⟩ := hpack k k.isLt
    exact himg ▸ ⟨s, hs, rfl⟩
  have hoT0 : ∀ k : Fin L, derivWithin (side k) (Icc 0 1) 0 ≠ 0 := by
    intro k
    obtain ⟨q, hq, -, -, hqs, htan1, hends, -, -, -, -, -, hd0, -⟩ := hpack k k.isLt
    show derivWithin (fx_p2_wedge (par (ee k)) (src (ee k)) (vv k)) (Icc 0 1) 0 ≠ 0
    rw [hd0]
    split_ifs
    · exact hsrc_tan _
    · exact neg_ne_zero.2 htan1
  have hoT1 : ∀ k : Fin L, derivWithin (side k) (Icc 0 1) 1 ≠ 0 := by
    intro k
    obtain ⟨q, hq, -, -, hqs, htan1, hends, -, -, -, -, -, -, hd1, -⟩ := hpack k k.isLt
    show derivWithin (fx_p2_wedge (par (ee k)) (src (ee k)) (vv k)) (Icc 0 1) 1 ≠ 0
    rw [hd1]
    refine neg_ne_zero.2 ?_
    split_ifs
    · exact hsrc_tan _
    · exact neg_ne_zero.2 htan1
  -- the corner ratios are blunt
  have hne_prev : ∀ k : Fin L, ee ((k - 1 : Fin L) : ℕ) ≠ ee (k : ℕ) := by
    intro k h
    have := hed _ (k - 1).isLt _ k.isLt h
    have hk : k - 1 = k := Fin.ext this
    have : (1 : Fin L) = 0 := by
      have := congrArg (fun x => k - x) hk
      simp only [sub_sub_cancel, sub_self] at this
      exact this
    have := congrArg Fin.val this
    rw [Fin.val_one', Nat.mod_eq_of_lt hL1, Fin.val_zero] at this
    exact one_ne_zero this
  have hratio : ∀ k : Fin L, ∃ m : ℕ, meromorphicOrderAt φ (side k 0) = (m : ℤ) ∧
      fx_p2_bluntR m
        (-(derivWithin (side (k - 1)) (Icc 0 1) 1) / derivWithin (side k) (Icc 0 1) 0) := by
    intro k
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hd1p, -⟩ := hpack _ (k - 1).isLt
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hd0, -⟩ := hpack k k.isLt
    have hincp : src (ee ((k - 1 : Fin L) : ℕ)) = vv k ∨
        dst (ee ((k - 1 : Fin L) : ℕ)) = some (vv k) := by
      rw [← hprev k]; exact (hcyc _ (k - 1).isLt).2.1
    obtain ⟨m, hm, hr⟩ := hblunt (vv k) (hzero k k.isLt).1 (hzero k k.isLt).2 _ _ hincp
      (hcyc k k.isLt).1 (hne_prev k)
    refine ⟨m, by rw [hv0 k]; exact hm, ?_⟩
    show fx_p2_bluntR m (-(derivWithin (fx_p2_wedge (par (ee ((k - 1 : Fin L) : ℕ)))
      (src (ee ((k - 1 : Fin L) : ℕ))) (vv ((k - 1 : Fin L) : ℕ))) (Icc 0 1) 1) /
      derivWithin (fx_p2_wedge (par (ee k)) (src (ee k)) (vv k)) (Icc 0 1) 0)
    rw [hd1p, hd0, neg_neg, hprev k]
    exact hr
  refine ⟨⟨fun k => (hpack k k.isLt).choose_spec.2.2.2.2.2.2.2.2.1,
    fun k => (hpack k k.isLt).choose_spec.2.2.2.2.2.2.2.2.2.1,
    fun k => (hpack k k.isLt).choose_spec.2.2.2.2.2.2.2.2.2.2.1, ?_, ?_, hoT0, hoT1, ?_⟩, ?_⟩
  · intro k
    obtain ⟨-, -, -, -, -, -, -, -, h1, -⟩ := hpack k k.isLt
    show fx_p2_wedge (par (ee k)) (src (ee k)) (vv k) 1 = side (k + 1) 0
    rw [h1, hv0, hnext]
  · refine fx_p2_simple_of ?_ ?_ ?_ ?_
    · intro k s hs t ht h
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hinjk, -⟩ := hpack k k.isLt
      rcases eq_or_lt_of_le hs.1 with hs0 | hs0 <;> rcases eq_or_lt_of_le ht.1 with ht0 | ht0
      · rw [← hs0, ← ht0]
      · rw [← hs0, hv0] at h
        exact absurd (hzero k k.isLt).2 (h ▸ hreg k t ⟨ht0, ht.2⟩)
      · rw [← ht0, hv0] at h
        exact absurd (hzero k k.isLt).2 (h ▸ hreg k s ⟨hs0, hs.2⟩)
      · exact hinjk ⟨hs0, hs.2⟩ ⟨ht0, ht.2⟩ h
    · intro k l h
      rw [hv0, hv0] at h
      exact Fin.ext (hvd _ k.isLt _ l.isLt h)
    · intro k l s hs h
      rw [hv0] at h
      exact hreg l s hs (h ▸ (hzero k k.isLt).2)
    · intro k l hkl s hs t ht h
      have hne : ee (k : ℕ) ≠ ee (l : ℕ) := fun h' => hkl (Fin.ext (hed _ k.isLt _ l.isLt h'))
      exact Set.disjoint_left.1 (hdisj _ _ hne) (hint k s hs) (h ▸ hint l t ht)
  · intro k
    obtain ⟨m, -, hr⟩ := hratio k
    have := (fx_p2_bluntRatio hr zero_lt_one).1
    rwa [Complex.ofReal_one, one_mul] at this
  · intro k
    obtain ⟨m, hm, hr⟩ := hratio k
    obtain ⟨-, h1, h2⟩ := fx_p2_bluntRatio hr zero_lt_one
    simp only [Complex.ofReal_one, one_mul] at h1 h2
    exact ⟨m, hm, h1, h2⟩

/-- **No cycles** (helper form of `fx_nocycle`). -/
theorem fx_p2_nocycle_core {φ : ℂ → ℂ}
    (hCF : ∀ {n : ℕ} [NeZero n] (side : Fin n → ℝ → ℂ), fx_IsChain φ side →
      3 ≤ {j | ¬ fx_IsBlunt φ side j}.ncard)
    {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hzf : {q : ℂ | q ∈ unitDisc ∧ φ q = 0}.Finite)
    (hvert : ∀ i, IsVerticalArc φ (par i) 0 1)
    (hmem : ∀ i, ∀ t ∈ Ioo (0 : ℝ) 1, par i t ∈ unitDisc)
    (hinj : ∀ i, InjOn (par i) (Ioo 0 1))
    (hsrc : ∀ i, par i 0 = src i ∧ src i ∈ unitDisc ∧ φ (src i) = 0)
    (hsrc_tan : ∀ i, derivWithin (par i) (Icc 0 1) 0 ≠ 0)
    (hsaddle : ∀ i q, dst i = some q → q ∈ unitDisc ∧ φ q = 0 ∧ q ≠ src i ∧
      ContDiffOn ℝ 1 (par i) (Icc 0 1) ∧ par i 1 = q ∧ derivWithin (par i) (Icc 0 1) 1 ≠ 0)
    (hdisj : ∀ i j, i ≠ j → Disjoint (par i '' Ioo 0 1) (par j '' Ioo 0 1))
    (hblunt : ∀ q ∈ unitDisc, φ q = 0 → ∀ i j, (src i = q ∨ dst i = some q) →
      (src j = q ∨ dst j = some q) → i ≠ j → ∃ m : ℕ, meromorphicOrderAt φ q = (m : ℤ) ∧
        fx_p2_bluntR m (fx_p2_oT par src i q / fx_p2_oT par src j q))
    {S : Set ℂ} (hS : S ⊆ {q | q ∈ unitDisc ∧ φ q = 0}) (hSne : S.Nonempty) {A : Set ι}
    (hA : ∀ q ∈ S, 2 ≤ {i | i ∈ A ∧ (src i = q ∨ dst i = some q)}.ncard) :
    ∃ q ∈ S, ∃ i ∈ A, (src i = q ∧ ∀ q', dst i = some q' → q' ∉ S) ∨
      (dst i = some q ∧ src i ∉ S) := by
  by_contra hcon
  have H : ∀ q ∈ S, ∀ i ∈ A, (src i = q → ∃ q', dst i = some q' ∧ q' ∈ S) ∧
      (dst i = some q → src i ∈ S) := by
    intro q hq i hi
    refine ⟨fun hs => ?_, fun hd => ?_⟩
    · by_contra h
      push Not at h
      exact hcon ⟨q, hq, i, hi, Or.inl ⟨hs, fun q' hq' => h q' hq'⟩⟩
    · by_contra h
      exact hcon ⟨q, hq, i, hi, Or.inr ⟨hd, h⟩⟩
  obtain ⟨L, vv, ee, hL, hcl, hcyc, hvd, hed⟩ := fx_p2_cycle_exists (hzf.subset hS) hSne
    (fun i q hd => (hsaddle i q hd).2.2.1) hA H
  have : NeZero L := ⟨by omega⟩
  obtain ⟨hC, hbl⟩ := fx_p2_cycle_chain hvert hmem hinj hsrc hsrc_tan hsaddle hdisj hblunt hL hcl
    (fun k hk => ⟨(hcyc k hk).2.2.1, (hcyc k hk).2.2.2.1, (hcyc k hk).2.2.2.2⟩) hvd hed
  have h3 := hCF _ hC
  have h0 : {j : Fin L | ¬ fx_IsBlunt φ (fun k : Fin L => fx_p2_wedge (par (ee k)) (src (ee k))
      (vv k)) j} = ∅ := by
    ext j
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_not]
    exact hbl j
  rw [h0, Set.ncard_empty] at h3
  omega

/-- **Orientation.**  A closed chain bounds a Jordan domain in `Δ` lying on one side of all its
sides, so it is a `PhiPolygon` in one of its two listings: as given (angles `fx_chainAngle`), or
reversed (`side' j t = side (-j-1) (1-t)`, vertices `side (-j) 0`, angles `2π - fx_chainAngle`). -/
theorem fx_chain_polygon {φ : ℂ → ℂ} {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) :
    ∃ P : PhiPolygon φ n,
      (∀ j, P.vert j = side j 0 ∧ P.angle j = fx_chainAngle side j) ∨
        (∀ j, P.vert j = side (-j) 0 ∧ P.angle j = 2 * π - fx_chainAngle side (-j)) := by
  obtain ⟨A, B, hAo, hBo, hAB, hAC, hBC, huniv, hfr, hJ, hcl⟩ := fx_p2_chain_jct hC
  have hsub : (⋃ j, side j '' Icc (0 : ℝ) 1) ⊆ closure A := hfr ▸ frontier_subset_closure
  obtain ⟨s, hs, hP | hN⟩ := fx_p2_chain_exists_pos hC hAo hBo hAB hAC huniv hsub
  · obtain ⟨P, hPv⟩ := fx_p2_chain_phiPolygon hC hJ hcl hfr
      (fx_p2_chain_pos_all hC hAo hBo hAB huniv hs hP)
    exact ⟨P, Or.inl hPv⟩
  · have hR := fx_p2_chain_rev hC
    have htr := fx_p2_rev_trace side
    have hs' : 1 - s ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have hP' : fx_p2_PosAt A (fx_p2_revSide side) (-1) (1 - s) := by
      rw [fx_p2_rev_pos_iff hC A (-1) hs', neg_neg, sub_self, sub_sub_cancel]
      exact hN
    have hall := fx_p2_chain_pos_all hR hAo hBo hAB (by rw [htr]; exact huniv) hs' hP'
    obtain ⟨P, hPv⟩ := fx_p2_chain_phiPolygon hR hJ hcl (hfr.trans htr.symm) hall
    refine ⟨P, Or.inr fun j => ⟨?_, ?_⟩⟩
    · rw [(hPv j).1]
      simp only [fx_p2_revSide, sub_zero]
      rw [hC.next, sub_add_cancel]
    · rw [(hPv j).2, fx_p2_rev_chainAngle hC j]

/-- **Teichmüller's lemma for chains (symmetric form).**  At least three corners of a closed chain
satisfy `θⱼ < 2π/(mⱼ+2)` in one of the two orientations.  This is the ONLY use of the global input
`thm25_2_polygon`. -/
theorem fx_teich_symm {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) :
    3 ≤ {j : Fin n | ∃ m : ℕ, meromorphicOrderAt φ (side j 0) = (m : ℤ) ∧
        fx_chainAngle side j < 2 * π / ((m : ℝ) + 2)}.ncard ∨
      3 ≤ {j : Fin n | ∃ m : ℕ, meromorphicOrderAt φ (side j 0) = (m : ℤ) ∧
        2 * π - fx_chainAngle side j < 2 * π / ((m : ℝ) + 2)}.ncard := by
  obtain ⟨P, hP⟩ := fx_chain_polygon hC
  have h := thm25_2_polygon hφ hne P
  rcases hP with hP | hP
  · left
    have hset : {j : Fin n | ∃ m : ℕ, meromorphicOrderAt φ (P.vert j) = (m : ℤ) ∧
          P.angle j < 2 * π / ((m : ℝ) + 2)} =
        {j : Fin n | ∃ m : ℕ, meromorphicOrderAt φ (side j 0) = (m : ℤ) ∧
          fx_chainAngle side j < 2 * π / ((m : ℝ) + 2)} := by
      ext j
      simp only [mem_ofPred_eq, (hP j).1, (hP j).2]
    rwa [hset] at h
  · right
    set S := {j : Fin n | ∃ m : ℕ, meromorphicOrderAt φ (P.vert j) = (m : ℤ) ∧
      P.angle j < 2 * π / ((m : ℝ) + 2)} with hS
    have hset : {j : Fin n | ∃ m : ℕ, meromorphicOrderAt φ (side j 0) = (m : ℤ) ∧
        2 * π - fx_chainAngle side j < 2 * π / ((m : ℝ) + 2)} = (fun j : Fin n => -j) '' S := by
      ext k
      simp only [mem_ofPred_eq, mem_image, hS]
      constructor
      · intro hk
        refine ⟨-k, ?_, neg_neg k⟩
        rw [(hP (-k)).1, (hP (-k)).2, neg_neg]
        exact hk
      · rintro ⟨j, hj, rfl⟩
        rw [(hP j).1, (hP j).2] at hj
        exact hj
    rw [hset, Set.ncard_image_of_injective _ neg_injective]
    exact h

/-- **The exclusion principle** used by every polygon argument of the route: a closed chain has at
least three non-blunt corners.  Hence no closed chain with at most two sides exists (closed
trajectories, bigons), and none whose corners are all blunt except at most two (vertical cycles
through zeros; a leaf arc through two edges at one zero). -/
theorem fx_chain_false {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ}
    (hC : fx_IsChain φ side) :
    3 ≤ {j : Fin n | ¬ fx_IsBlunt φ side j}.ncard := by
  have key : ∀ j : Fin n, ∀ m m' : ℕ, meromorphicOrderAt φ (side j 0) = (m : ℤ) →
      meromorphicOrderAt φ (side j 0) = (m' : ℤ) → m = m' := by
    intro j m m' h h'
    rw [h] at h'
    have h2 : ((m : ℤ) : WithTop ℤ) = ((m' : ℤ) : WithTop ℤ) := h'
    exact_mod_cast WithTop.coe_injective h2
  rcases fx_teich_symm hφ hne hC with h | h
  · refine h.trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
    rintro j ⟨m, hm, hlt⟩ ⟨m', hm', hle, -⟩
    have := key j m m' hm hm'
    subst this
    linarith
  · refine h.trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
    rintro j ⟨m, hm, hlt⟩ ⟨m', hm', -, hle⟩
    have := key j m m' hm hm'
    subst this
    linarith

/-! ## §2 Flow boxes, horizontal trajectories and leaves -/

/-- A **flow box** (natural-parameter chart): `N ⊆ Δ` open, `ζ` holomorphic and injective on `N`
with `ζ'² = φ ≠ 0`, mapping `N` onto an open square.  Horizontal plaques are `{Im ζ = const}`,
vertical plaques `{Re ζ = const}`. -/
def fx_IsFlowBox (φ : ℂ → ℂ) (ζ : ℂ → ℂ) (N : Set ℂ) : Prop :=
  IsOpen N ∧ N ⊆ unitDisc ∧ InjOn ζ N ∧
    (∀ z ∈ N, φ z ≠ 0 ∧ DifferentiableAt ℂ ζ z ∧ deriv ζ z ^ 2 = φ z) ∧
    ∃ (c : ℂ) (δ : ℝ), 0 < δ ∧ ζ '' N = {w : ℂ | |w.re - c.re| < δ ∧ |w.im - c.im| < δ}

/-- A unit-speed horizontal trajectory `γ : [0, T] → Δ` through regular points:
`γ` is `C¹` on `[0, T]` and `φ(γ t) γ'(t)² = 1`.  (For `-φ`: a unit-speed vertical trajectory.) -/
def fx_IsHTraj (φ : ℂ → ℂ) (γ : ℝ → ℂ) (T : ℝ) : Prop :=
  0 < T ∧ ContDiffOn ℝ 1 γ (Icc 0 T) ∧ (∀ t ∈ Icc 0 T, γ t ∈ unitDisc ∧ φ (γ t) ≠ 0) ∧
    ∀ t ∈ Icc 0 T, φ (γ t) * derivWithin γ (Icc 0 T) t ^ 2 = 1

/-- The **horizontal leaf** of `z` in `Δ`: the points reachable from the regular point `z` along a
horizontal trajectory in `Δ` through regular points (empty if `z` is not a regular point of `Δ`). -/
def fx_leaf (φ : ℂ → ℂ) (z : ℂ) : Set ℂ :=
  {w | (w = z ∧ z ∈ unitDisc ∧ φ z ≠ 0) ∨
    ∃ (γ : ℝ → ℂ) (T : ℝ), fx_IsHTraj φ γ T ∧ γ 0 = z ∧ γ T = w}

/-- The open square `{|Re (w - c)| < δ, |Im (w - c)| < δ}` is convex. -/
theorem fx_p3_square_convex (c : ℂ) (δ : ℝ) :
    Convex ℝ {w : ℂ | |w.re - c.re| < δ ∧ |w.im - c.im| < δ} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    smul_eq_mul] at hx hy ⊢
  have e1 : a * x.re + b * y.re - c.re = a * (x.re - c.re) + b * (y.re - c.re) := by
    linear_combination c.re * hab
  have e2 : a * x.im + b * y.im - c.im = a * (x.im - c.im) + b * (y.im - c.im) := by
    linear_combination c.im * hab
  rw [e1, e2]
  constructor
  · calc |a * (x.re - c.re) + b * (y.re - c.re)|
        ≤ |a * (x.re - c.re)| + |b * (y.re - c.re)| := abs_add_le _ _
      _ = a * |x.re - c.re| + b * |y.re - c.re| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ < δ := by
          rcases ha.lt_or_eq with ha' | ha'
          · calc a * |x.re - c.re| + b * |y.re - c.re| < a * δ + b * δ := by
                  have := mul_lt_mul_of_pos_left hx.1 ha'
                  have := mul_le_mul_of_nonneg_left hy.1.le hb
                  linarith
              _ = δ := by rw [← add_mul, hab, one_mul]
          · subst ha'
            simp only [zero_add] at hab
            subst hab
            simpa using hy.1
  · calc |a * (x.im - c.im) + b * (y.im - c.im)|
        ≤ |a * (x.im - c.im)| + |b * (y.im - c.im)| := abs_add_le _ _
      _ = a * |x.im - c.im| + b * |y.im - c.im| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ < δ := by
          rcases ha.lt_or_eq with ha' | ha'
          · calc a * |x.im - c.im| + b * |y.im - c.im| < a * δ + b * δ := by
                  have := mul_lt_mul_of_pos_left hx.2 ha'
                  have := mul_le_mul_of_nonneg_left hy.2.le hb
                  linarith
              _ = δ := by rw [← add_mul, hab, one_mul]
          · subst ha'
            simp only [zero_add] at hab
            subst hab
            simpa using hy.2

/-- The local inverse of a flow-box chart: `ψ = ζ⁻¹` on `ζ '' N`, holomorphic with
`ψ' = 1 / (ζ' ∘ ψ)`. -/
theorem fx_p3_box_inverse {φ ζ : ℂ → ℂ} {N : Set ℂ} (hN : fx_IsFlowBox φ ζ N) :
    IsOpen (ζ '' N) ∧ (∀ z ∈ N, Function.invFunOn ζ N (ζ z) = z) ∧
      ∀ w ∈ ζ '' N, Function.invFunOn ζ N w ∈ N ∧ ζ (Function.invFunOn ζ N w) = w ∧
        HasDerivAt (Function.invFunOn ζ N) (deriv ζ (Function.invFunOn ζ N w))⁻¹ w := by
  obtain ⟨hNo, -, hinj, hreg, -⟩ := hN
  have hconf : IsConformalOnto ζ N (ζ '' N) :=
    ⟨fun z hz => (hreg z hz).2.1.differentiableWithinAt, hinj, rfl⟩
  have hopen : IsOpen (ζ '' N) := hconf.isOpen hNo
  have hsymm := hconf.symm hNo
  refine ⟨hopen, fun z hz => hinj.leftInvOn_invFunOn hz, fun w hw => ?_⟩
  have hmem : Function.invFunOn ζ N w ∈ N := by
    have h := mem_image_of_mem (Function.invFunOn ζ N) hw
    rwa [hsymm.2.2] at h
  have hζψ : ζ (Function.invFunOn ζ N w) = w := Function.invFunOn_eq hw
  have hψd : DifferentiableAt ℂ (Function.invFunOn ζ N) w :=
    hsymm.1.differentiableAt (hopen.mem_nhds hw)
  have hζd : HasDerivAt ζ (deriv ζ (Function.invFunOn ζ N w)) (Function.invFunOn ζ N w) :=
    (hreg _ hmem).2.1.hasDerivAt
  have hcomp := hζd.comp w hψd.hasDerivAt
  have hid : id =ᶠ[𝓝 w] ζ ∘ Function.invFunOn ζ N := by
    filter_upwards [hopen.mem_nhds hw] with y hy
    exact (Function.invFunOn_eq hy).symm
  have hone : deriv ζ (Function.invFunOn ζ N w) * deriv (Function.invFunOn ζ N) w = 1 := by
    have h := (hcomp.congr_of_eventuallyEq hid).deriv
    rw [deriv_id] at h
    exact h.symm
  refine ⟨hmem, hζψ, ?_⟩
  have hval : deriv (Function.invFunOn ζ N) w = (deriv ζ (Function.invFunOn ζ N w))⁻¹ :=
    eq_inv_of_mul_eq_one_right hone
  rw [← hval]
  exact hψd.hasDerivAt

/-- **Regular chart data** at a regular point `p`: the natural parameter `ζ` (`ζ p = 0`) is
analytic and injective on `closedBall p r ⊆ Δ` with `ζ'² = φ`, `ζ' ≠ 0`, and its image of the open ball
contains `ball 0 ρ0`. -/
def fx_p3_RegChart (φ ζ : ℂ → ℂ) (p : ℂ) (r ρ0 : ℝ) : Prop :=
  0 < r ∧ 0 < ρ0 ∧ closedBall p r ⊆ unitDisc ∧ ζ p = 0 ∧ InjOn ζ (closedBall p r) ∧
    (∀ z ∈ closedBall p r, AnalyticAt ℂ ζ z ∧ deriv ζ z ^ 2 = φ z ∧ deriv ζ z ≠ 0) ∧
    ball 0 ρ0 ⊆ ζ '' ball p r

/-- Regular charts exist at every regular point of `Δ`, of arbitrarily small radius
(`psa_chart`, `psa_inverse`). -/
theorem fx_p3_regChart_exists {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {p : ℂ}
    (hp : p ∈ unitDisc) (hp0 : φ p ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ζ : ℂ → ℂ) (r ρ0 : ℝ), fx_p3_RegChart φ ζ p r ρ0 ∧ r < ε := by
  have hDo : IsOpen (unitDisc ∩ ball p ε) := isOpen_ball.inter isOpen_ball
  obtain ⟨ζ, r, hr, hBD, hζ0, hinj, han⟩ :=
    psa_chart hDo (hφ.mono inter_subset_left) ⟨hp, mem_ball_self hε⟩ hp0
  obtain ⟨hopen, -⟩ := psa_inverse hr hinj fun z hz => ⟨(han z hz).1, (han z hz).2.2⟩
  have h0mem : (0 : ℂ) ∈ ζ '' ball p r := ⟨p, mem_ball_self hr, hζ0⟩
  obtain ⟨ρ0, hρ0, hρB⟩ := Metric.isOpen_iff.1 hopen 0 h0mem
  refine ⟨ζ, r, ρ0, ⟨hr, hρ0, fun z hz => (hBD hz).1, hζ0, hinj, han, hρB⟩, ?_⟩
  have hmem : p + (r : ℂ) ∈ closedBall p r := by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
  have h := (hBD hmem).2
  rwa [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr] at h

/-- The inverse `ψ = ζ⁻¹` of a regular chart on `ζ(ball p r)` (`psa_inverse`). -/
theorem fx_p3_RegChart.inv {φ ζ : ℂ → ℂ} {p : ℂ} {r ρ0 : ℝ} (hR : fx_p3_RegChart φ ζ p r ρ0) :
    IsOpen (ζ '' ball p r) ∧ (∀ z ∈ ball p r, Function.invFunOn ζ (ball p r) (ζ z) = z) ∧
      ∀ w ∈ ζ '' ball p r, Function.invFunOn ζ (ball p r) w ∈ ball p r ∧
        ζ (Function.invFunOn ζ (ball p r) w) = w ∧
        HasDerivAt (Function.invFunOn ζ (ball p r))
          (deriv ζ (Function.invFunOn ζ (ball p r) w))⁻¹ w := by
  obtain ⟨hr, -, -, -, hinj, han, -⟩ := hR
  obtain ⟨hopen, hψ⟩ := psa_inverse hr hinj fun z hz => ⟨(han z hz).1, (han z hz).2.2⟩
  exact ⟨hopen, fun z hz => (hinj.mono ball_subset_closedBall).leftInvOn_invFunOn hz, hψ⟩

/-- The **coordinate boxes** of a regular chart: `ball p r ∩ ζ⁻¹(square(0, δ))` is a flow box for
`δ ≤ ρ0 / 2`, and contains `p`. -/
theorem fx_p3_RegChart.box {φ ζ : ℂ → ℂ} {p : ℂ} {r ρ0 : ℝ} (hR : fx_p3_RegChart φ ζ p r ρ0) {δ : ℝ}
    (hδ : 0 < δ) (hδρ : δ ≤ ρ0 / 2) :
    p ∈ ball p r ∩ ζ ⁻¹' {w : ℂ | |w.re - (0 : ℂ).re| < δ ∧ |w.im - (0 : ℂ).im| < δ} ∧
      fx_IsFlowBox φ ζ (ball p r ∩ ζ ⁻¹' {w : ℂ | |w.re - (0 : ℂ).re| < δ ∧
        |w.im - (0 : ℂ).im| < δ}) := by
  obtain ⟨hr, hρ0, hBD, hζ0, hinj, han, hρB⟩ := hR
  have hsub : ball p r ⊆ closedBall p r := ball_subset_closedBall
  have hcont : ContinuousOn ζ (ball p r) := fun z hz =>
    (han z (hsub hz)).1.continuousAt.continuousWithinAt
  set S : Set ℂ := {w : ℂ | |w.re - (0 : ℂ).re| < δ ∧ |w.im - (0 : ℂ).im| < δ} with hS
  have hSo : IsOpen S := by
    refine IsOpen.inter ?_ ?_
    · exact isOpen_lt ((Complex.continuous_re.sub continuous_const).abs) continuous_const
    · exact isOpen_lt ((Complex.continuous_im.sub continuous_const).abs) continuous_const
  have hSB : S ⊆ ball 0 ρ0 := by
    intro w hw
    simp only [hS, mem_ofPred_eq, Complex.zero_re, Complex.zero_im, sub_zero] at hw
    rw [mem_ball_zero_iff]
    calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
      _ < δ + δ := add_lt_add hw.1 hw.2
      _ ≤ ρ0 := by linarith
  refine ⟨⟨mem_ball_self hr, ?_⟩, hcont.isOpen_inter_preimage isOpen_ball hSo,
    fun z hz => hBD (hsub hz.1), hinj.mono (inter_subset_left.trans hsub), fun z hz => ?_, 0, δ,
    hδ, ?_⟩
  · show ζ p ∈ S
    rw [hζ0]
    simp only [hS, mem_ofPred_eq, sub_self, abs_zero]
    exact ⟨hδ, hδ⟩
  · obtain ⟨h1, h2, h3⟩ := han z (hsub hz.1)
    refine ⟨fun h => h3 ?_, h1.differentiableAt, h2⟩
    rw [h] at h2
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
  · apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hz.2
    · intro w hw
      obtain ⟨z, hz, hzw⟩ := hρB (hSB hw)
      exact ⟨z, ⟨hz, by rw [mem_preimage, hzw]; exact hw⟩, hzw⟩

/-- **Flow boxes exist** around every regular point, inside any prescribed ball
(from `psa_chart` / `psa_inverse`). -/
theorem fx_flowBox_exists {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {p : ℂ}
    (hp : p ∈ unitDisc) (hp0 : φ p ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ζ : ℂ → ℂ) (N : Set ℂ), p ∈ N ∧ N ⊆ ball p ε ∧ fx_IsFlowBox φ ζ N := by
  obtain ⟨ζ, r, ρ0, hR, hrε⟩ := fx_p3_regChart_exists hφ hp hp0 hε
  obtain ⟨hpN, hN⟩ := hR.box (half_pos hR.2.1) le_rfl
  exact ⟨ζ, _, hpN, fun z hz => ball_subset_ball hrε.le hz.1, hN⟩

/-- **Plaques lie in leaves**: two points of a flow box on the same horizontal plaque are on the
same leaf. -/
theorem fx_plaque_leaf {φ ζ : ℂ → ℂ} {N : Set ℂ} (hN : fx_IsFlowBox φ ζ N) {z z' : ℂ}
    (hz : z ∈ N) (hz' : z' ∈ N) (h : (ζ z).im = (ζ z').im) : z' ∈ fx_leaf φ z := by
  obtain ⟨hopen, hleft, hψ⟩ := fx_p3_box_inverse hN
  obtain ⟨-, hND, hinj, hreg, c, δ, -, hsq⟩ := hN
  by_cases hzz : z' = z
  · exact Or.inl ⟨hzz, hND hz, (hreg z hz).1⟩
  right
  set ψ := Function.invFunOn ζ N with hψdef
  set a := ζ z with ha
  set b := ζ z' with hb
  have hab : a ≠ b := fun e => hzz (hinj hz hz' e).symm
  set d : ℝ := (b - a).re with hd
  have hba : b - a = (d : ℂ) := by
    apply Complex.ext
    · simp [hd]
    · simp [hd, Complex.sub_im, h]
  have hd0 : d ≠ 0 := by
    intro e
    apply hab
    have : b - a = 0 := by rw [hba, e, Complex.ofReal_zero]
    exact (sub_eq_zero.1 this).symm
  set T : ℝ := |d| with hT
  have hT0 : 0 < T := abs_pos.2 hd0
  set u : ℂ := (d : ℂ) / (T : ℂ) with hu
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hT0.ne'
  have hu2 : u ^ 2 = 1 := by
    rw [hu, div_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow, hT, sq_abs, div_self]
    exact Complex.ofReal_ne_zero.2 (pow_ne_zero 2 hd0)
  have hTu : (T : ℂ) * u = b - a := by
    rw [hu, mul_div_cancel₀ _ hTc, hba]
  set ℓ : ℝ → ℂ := fun t => a + (t : ℂ) * u with hℓ
  have hℓd : ∀ t : ℝ, HasDerivAt ℓ u t := fun t => by
    rw [hℓ]
    simpa using ((hasDerivAt_id' t).ofReal_comp.mul_const u).const_add a
  have haV : a ∈ ζ '' N := mem_image_of_mem ζ hz
  have hbV : b ∈ ζ '' N := mem_image_of_mem ζ hz'
  have hℓV : ∀ t ∈ Icc 0 T, ℓ t ∈ ζ '' N := by
    intro t ht
    have hconv : Convex ℝ (ζ '' N) := by rw [hsq]; exact fx_p3_square_convex c δ
    have ht' : t / T ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hT0.le, (div_le_one hT0).2 ht.2⟩
    have hmem := hconv.add_smul_sub_mem haV hbV ht'
    have e : a + (t / T : ℝ) • (b - a) = ℓ t := by
      simp only [hℓ, Complex.real_smul]
      rw [← hTu]
      push_cast
      field_simp
    rwa [e] at hmem
  set γ : ℝ → ℂ := fun t => ψ (ℓ t) with hγ
  have hγd : ∀ t ∈ Icc 0 T, HasDerivAt γ ((deriv ζ (γ t))⁻¹ * u) t := by
    intro t ht
    have h1 := (hψ _ (hℓV t ht)).2.2
    exact h1.comp t (hℓd t)
  refine ⟨γ, T, ⟨hT0, ?_, fun t ht => ?_, fun t ht => ?_⟩, ?_, ?_⟩
  · have hψc : ContDiffOn ℂ 1 ψ (ζ '' N) := by
      refine DifferentiableOn.contDiffOn (fun w hw => ?_) hopen
      exact (hψ w hw).2.2.differentiableAt.differentiableWithinAt
    have hℓc : ContDiff ℝ 1 ℓ := by
      rw [hℓ]
      exact contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
    exact hψc.restrict_scalars ℝ |>.comp hℓc.contDiffOn hℓV
  · have hmem := (hψ _ (hℓV t ht)).1
    exact ⟨hND hmem, (hreg _ hmem).1⟩
  · rw [(hγd t ht).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hT0 t ht)]
    have hmem := (hψ _ (hℓV t ht)).1
    obtain ⟨hφ0, -, hsq2⟩ := hreg _ hmem
    have hζ0 : deriv ζ (γ t) ≠ 0 := by
      intro e
      apply hφ0
      rw [← hsq2, e, zero_pow two_ne_zero]
    rw [mul_pow, hu2, mul_one, inv_pow, ← hsq2]
    exact mul_inv_cancel₀ (pow_ne_zero 2 hζ0)
  · show ψ (a + ((0 : ℝ) : ℂ) * u) = z
    rw [Complex.ofReal_zero, zero_mul, add_zero, ha]
    exact hleft z hz
  · show ψ (a + (T : ℂ) * u) = z'
    rw [hTu, add_sub_cancel, hb]
    exact hleft z' hz'

/-- **Uniqueness of trajectories**: two unit-speed horizontal trajectories with the same initial
point and velocity agree on their common interval. -/
theorem fx_htraj_unique {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {γ₁ γ₂ : ℝ → ℂ}
    {T₁ T₂ : ℝ} (h₁ : fx_IsHTraj φ γ₁ T₁) (h₂ : fx_IsHTraj φ γ₂ T₂) (h0 : γ₁ 0 = γ₂ 0)
    (hd : derivWithin γ₁ (Icc 0 T₁) 0 = derivWithin γ₂ (Icc 0 T₂) 0) :
    ∀ t ∈ Icc 0 (min T₁ T₂), γ₁ t = γ₂ t := by
  exact fx_p2_htrajP_unique hφ h₁ h₂ h0 hd

/-- **No closed trajectories**: a horizontal trajectory in `Δ` is injective (a return would give
a retracing, impossible at unit speed, or a closed trajectory, a one-sided chain excluded by
`fx_chain_false`). -/
theorem fx_htraj_injOn {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {γ : ℝ → ℂ} {T : ℝ} (hγ : fx_IsHTraj φ γ T) :
    InjOn γ (Icc 0 T) := by
  exact fx_p2_htrajP_injOn hφ (fun side hC => by
    have h3 := fx_chain_false hφ hne hC
    have h1 : {j : Fin 1 | ¬ fx_IsBlunt φ side j}.ncard ≤ 1 := by
      calc {j : Fin 1 | ¬ fx_IsBlunt φ side j}.ncard ≤ (univ : Set (Fin 1)).ncard :=
            Set.ncard_le_ncard (subset_univ _)
        _ = 1 := by simp
    omega) hγ

/-- **Leaves are symmetric** (reverse the trajectory). -/
theorem fx_leaf_symm {φ : ℂ → ℂ} {z w : ℂ} (h : w ∈ fx_leaf φ z) : z ∈ fx_leaf φ w := by
  exact fx_p2_leafP_symm h

/-- **Leaves are transitive** (concatenate, or cut a retraced piece using
`fx_htraj_unique`). -/
theorem fx_leaf_trans {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {z w v : ℂ}
    (hw : w ∈ fx_leaf φ z) (hv : v ∈ fx_leaf φ w) : v ∈ fx_leaf φ z := by
  exact fx_p2_leafP_trans hφ hw hv

/-- Points of a leaf are regular points of `Δ`. -/
theorem fx_p4_leaf_reg {φ : ℂ → ℂ} {z w : ℂ} (h : w ∈ fx_leaf φ z) : w ∈ unitDisc ∧ φ w ≠ 0 := by
  rcases h with ⟨rfl, hz, hz0⟩ | ⟨γ, T, hγ, -, rfl⟩
  · exact ⟨hz, hz0⟩
  · exact hγ.2.2.1 T ⟨hγ.1.le, le_rfl⟩

/-- The chart of a flow box has nonvanishing derivative. -/
theorem fx_p4_flowBox_deriv_ne {φ ζ : ℂ → ℂ} {N : Set ℂ} (hN : fx_IsFlowBox φ ζ N) {z : ℂ}
    (hz : z ∈ N) : deriv ζ z ≠ 0 := by
  intro h0
  apply (hN.2.2.2.1 z hz).1
  rw [← (hN.2.2.2.1 z hz).2.2, h0]
  ring

/-- The chart of a flow box is holomorphic on the box. -/
theorem fx_p4_flowBox_diffOn {φ ζ : ℂ → ℂ} {N : Set ℂ} (hN : fx_IsFlowBox φ ζ N) :
    DifferentiableOn ℂ ζ N := fun w hw => (hN.2.2.2.1 w hw).2.1.differentiableWithinAt

/-- The chart of a flow box maps open subsets of the box onto open sets (open mapping). -/
theorem fx_p4_flowBox_isOpen_image {φ ζ : ℂ → ℂ} {N : Set ℂ} (hN : fx_IsFlowBox φ ζ N) {U : Set ℂ}
    (hU : IsOpen U) (hUN : U ⊆ N) : IsOpen (ζ '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  have han : AnalyticAt ℂ ζ z := (fx_p4_flowBox_diffOn hN).analyticAt (hN.1.mem_nhds (hUN hz))
  rw [← han.hasStrictDerivAt.map_nhds_eq (fx_p4_flowBox_deriv_ne hN (hUN hz))]
  exact image_mem_map (hU.mem_nhds hz)

/-- Inside a flow box, the preimage of a preconnected part of the square is preconnected (the chart
is a homeomorphism of the box onto the square). -/
theorem fx_p4_flowBox_preimage_isPreconnected {φ ζ : ℂ → ℂ} {N : Set ℂ} (hN : fx_IsFlowBox φ ζ N)
    {Q : Set ℂ} (hQ : IsPreconnected Q) (hQN : Q ⊆ ζ '' N) : IsPreconnected (N ∩ ζ ⁻¹' Q) := by
  set g := Function.invFunOn ζ N with hg
  have hgN : ∀ w ∈ ζ '' N, g w ∈ N ∧ ζ (g w) = w := fun w hw =>
    ⟨Function.invFunOn_mem hw, Function.invFunOn_eq hw⟩
  have hginv : ∀ z ∈ N, g (ζ z) = z := fun z hz =>
    hN.2.2.1 (hgN _ ⟨z, hz, rfl⟩).1 hz (hgN _ ⟨z, hz, rfl⟩).2
  have hcont : ContinuousOn g (ζ '' N) := by
    rw [_root_.continuousOn_iff']
    intro t ht
    refine ⟨ζ '' (N ∩ t), fx_p4_flowBox_isOpen_image hN (hN.1.inter ht) inter_subset_left, ?_⟩
    ext w
    simp only [mem_inter_iff, mem_preimage, mem_image]
    constructor
    · rintro ⟨hwt, hw⟩
      exact ⟨⟨g w, ⟨(hgN w hw).1, hwt⟩, (hgN w hw).2⟩, hw⟩
    · rintro ⟨⟨z, ⟨hzN, hzt⟩, rfl⟩, hw⟩
      exact ⟨by rw [hginv z hzN]; exact hzt, hw⟩
  have heq : N ∩ ζ ⁻¹' Q = g '' Q := by
    ext z
    constructor
    · rintro ⟨hzN, hzQ⟩
      exact ⟨ζ z, hzQ, hginv z hzN⟩
    · rintro ⟨w, hwQ, rfl⟩
      refine ⟨(hgN w (hQN hwQ)).1, ?_⟩
      show ζ (g w) ∈ Q
      rw [(hgN w (hQN hwQ)).2]
      exact hwQ
  rw [heq]
  exact hQ.image g (hcont.mono hQN)

/-- The square of a flow box is convex. -/
theorem fx_p4_square_convex (c : ℂ) (δ : ℝ) :
    Convex ℝ {w : ℂ | |w.re - c.re| < δ ∧ |w.im - c.im| < δ} := by
  have h1 : Convex ℝ {w : ℂ | |w.re - c.re| < δ} := by
    have := (convex_ball c.re δ).linear_preimage Complex.reLm
    convert this using 1
    ext w
    simp [Real.dist_eq]
  have h2 : Convex ℝ {w : ℂ | |w.im - c.im| < δ} := by
    have := (convex_ball c.im δ).linear_preimage Complex.imLm
    convert this using 1
    ext w
    simp [Real.dist_eq]
  exact h1.inter h2

/-- Two natural parameters on a preconnected open part `W` of a flow box agree up to sign and an
additive constant. -/
theorem fx_p4_flowBox_sign {φ ζ : ℂ → ℂ} {N : Set ℂ} (hN : fx_IsFlowBox φ ζ N) {W : Set ℂ}
    (hWN : W ⊆ N) (hWo : IsOpen W) (hWc : IsPreconnected W) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ W) (hΦ2 : ∀ z ∈ W, deriv Φ z ^ 2 = φ z) :
    ∃ C : ℂ, (∀ z ∈ W, Φ z = ζ z + C) ∨ (∀ z ∈ W, Φ z = -ζ z + C) := by
  rcases W.eq_empty_or_nonempty with hW | ⟨z₀, hz₀⟩
  · exact ⟨0, Or.inl fun z hz => by simp [hW] at hz⟩
  have hcont : ContinuousOn (fun z => deriv Φ z / deriv ζ z) W :=
    ((hΦ.deriv hWo).continuousOn).div
      (((fx_p4_flowBox_diffOn hN).deriv hN.1).continuousOn.mono hWN)
      fun z hz => fx_p4_flowBox_deriv_ne hN (hWN hz)
  have hmaps : MapsTo (fun z => deriv Φ z / deriv ζ z) W ({1, -1} : Set ℂ) := by
    intro z hz
    have hsq : (deriv Φ z / deriv ζ z) ^ 2 = 1 := by
      rw [div_pow, hΦ2 z hz, (hN.2.2.2.1 z (hWN hz)).2.2]
      exact div_self (hN.2.2.2.1 z (hWN hz)).1
    have h' : (deriv Φ z / deriv ζ z - 1) * (deriv Φ z / deriv ζ z + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.1 h' with h1 | h1
    · left; linear_combination h1
    · right; show _ = _; linear_combination h1
  have hconst : ∀ z ∈ W, deriv Φ z / deriv ζ z = deriv Φ z₀ / deriv ζ z₀ := fun z hz =>
    hWc.constant_of_mapsTo (Set.toFinite _).isDiscrete hcont hmaps hz hz₀
  set s := deriv Φ z₀ / deriv ζ z₀ with hs
  have hF : ∀ z ∈ W, HasDerivAt (fun w => Φ w - s * ζ w) 0 z := by
    intro z hz
    have h1 := (hΦ.differentiableAt (hWo.mem_nhds hz)).hasDerivAt
    have h2 := (hN.2.2.2.1 z (hWN hz)).2.1.hasDerivAt
    have h3 := h1.sub (h2.const_mul s)
    convert h3 using 1
    rw [← hconst z hz, div_mul_cancel₀ _ (fx_p4_flowBox_deriv_ne hN (hWN hz)), sub_self]
  have hFc : ∀ z ∈ W, Φ z - s * ζ z = Φ z₀ - s * ζ z₀ := fun z hz =>
    hWo.is_const_of_deriv_eq_zero hWc
      (fun w hw => (hF w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => by rw [(hF w hw).deriv]; rfl) hz hz₀
  refine ⟨Φ z₀ - s * ζ z₀, ?_⟩
  rcases hmaps hz₀ with h1 | h1
  · left
    intro z hz
    have := hFc z hz
    have hs1 : s = 1 := h1
    rw [hs1] at this ⊢
    linear_combination this
  · right
    intro z hz
    have := hFc z hz
    have hs1 : s = -1 := h1
    rw [hs1] at this ⊢
    linear_combination this

/-- The real part of a natural parameter on a preconnected open part of a flow box is
`± (Re ζ - a) + v`. -/
theorem fx_p4_flowBox_re {φ ζ : ℂ → ℂ} {N : Set ℂ} (hN : fx_IsFlowBox φ ζ N) {W : Set ℂ}
    (hWN : W ⊆ N) (hWo : IsOpen W) (hWc : IsPreconnected W) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ W) (hΦ2 : ∀ z ∈ W, deriv Φ z ^ 2 = φ z) (a : ℝ) :
    ∃ v : ℝ, ∀ z ∈ W, |(Φ z).re - v| = |(ζ z).re - a| := by
  obtain ⟨C, hC | hC⟩ := fx_p4_flowBox_sign hN hWN hWo hWc hΦ hΦ2
  · refine ⟨a + C.re, fun z hz => ?_⟩
    rw [hC z hz, add_re]
    congr 1
    ring
  · refine ⟨-a + C.re, fun z hz => ?_⟩
    rw [hC z hz, add_re, neg_re, ← abs_neg]
    congr 1
    ring

/-- Negating the chart of a flow box gives a flow box. -/
theorem fx_p4_flowBox_neg {φ ζ : ℂ → ℂ} {N : Set ℂ} (hN : fx_IsFlowBox φ ζ N) :
    fx_IsFlowBox φ (fun z => -ζ z) N := by
  obtain ⟨hNo, hND, hinj, hreg, c, δ, hδ, hsq⟩ := hN
  refine ⟨hNo, hND, fun x hx y hy h => hinj hx hy (neg_inj.1 h), fun z hz => ?_, -c, δ, hδ, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hreg z hz
    refine ⟨h1, h2.neg, ?_⟩
    rw [deriv.fun_neg, neg_sq, h3]
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      have : ζ z ∈ ζ '' N := ⟨z, hz, rfl⟩
      rw [hsq] at this
      obtain ⟨h1, h2⟩ := this
      refine ⟨?_, ?_⟩
      · rw [neg_re, neg_re, show -(ζ z).re - -c.re = -((ζ z).re - c.re) by ring, abs_neg]
        exact h1
      · rw [neg_im, neg_im, show -(ζ z).im - -c.im = -((ζ z).im - c.im) by ring, abs_neg]
        exact h2
    · rintro ⟨h1, h2⟩
      have : -w ∈ ζ '' N := by
        rw [hsq]
        refine ⟨?_, ?_⟩
        · rw [neg_re, show -w.re - c.re = -(w.re - -c.re) by ring, abs_neg]
          simpa using h1
        · rw [neg_im, show -w.im - c.im = -(w.im - -c.im) by ring, abs_neg]
          simpa using h2
      obtain ⟨z, hz, hzw⟩ := this
      exact ⟨z, hz, by show -ζ z = w; rw [hzw, neg_neg]⟩

/-- A property that is locally constant on a preconnected set holds everywhere or nowhere. -/
theorem fx_p4_preconn_prop {α : Type*} [TopologicalSpace α] {S : Set α} (hS : IsPreconnected S)
    (P : α → Prop) (hloc : ∀ t ∈ S, ∀ᶠ t' in 𝓝[S] t, (P t' ↔ P t)) {t₁ t₂ : α} (h₁ : t₁ ∈ S)
    (h₂ : t₂ ∈ S) (hP : P t₁) : P t₂ := by
  classical
  have hc : ContinuousOn (fun t => decide (P t)) S := by
    intro t ht
    rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]
    filter_upwards [hloc t ht] with t' ht'
    exact decide_eq_decide.2 ht'
  have := hS.constant hc h₁ h₂
  simp only [hP, decide_true] at this
  exact of_decide_eq_true this.symm

/-- Along a unit-speed horizontal trajectory inside a flow box, `Im ζ` is constant. -/
theorem fx_p4_htraj_im_const {φ ζ : ℂ → ℂ} {N : Set ℂ} (hN : fx_IsFlowBox φ ζ N) {γ : ℝ → ℂ}
    {T : ℝ} (hγ : fx_IsHTraj φ γ T) {a b : ℝ} (ha : 0 ≤ a) (hbT : b ≤ T)
    (hsub : ∀ s ∈ Icc a b, γ s ∈ N) : ∀ s ∈ Icc a b, (ζ (γ s)).im = (ζ (γ a)).im := by
  have hdiff : DifferentiableOn ℝ γ (Icc 0 T) := hγ.2.1.differentiableOn one_ne_zero
  have hder : ∀ s ∈ Icc a b,
      HasDerivWithinAt (fun s => (ζ (γ s)).im) (0 : ℝ) (Icc a b) s := by
    intro s hs
    have hs0 : s ∈ Icc 0 T := ⟨ha.trans hs.1, hs.2.trans hbT⟩
    have h1 : HasDerivWithinAt γ (derivWithin γ (Icc 0 T) s) (Icc 0 T) s :=
      (hdiff s hs0).hasDerivWithinAt
    obtain ⟨-, hζd, hζ2⟩ := hN.2.2.2.1 (γ s) (hsub s hs)
    have h2 := (hζd.hasDerivAt.comp_hasDerivWithinAt s h1).mono (Icc_subset_Icc ha hbT)
    have h3 := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt s h2
    have hval : (deriv ζ (γ s) * derivWithin γ (Icc 0 T) s).im = 0 := by
      have hsq : (deriv ζ (γ s) * derivWithin γ (Icc 0 T) s) ^ 2 = 1 := by
        rw [mul_pow, hζ2]
        exact hγ.2.2.2 s hs0
      have h' : (deriv ζ (γ s) * derivWithin γ (Icc 0 T) s - 1) *
          (deriv ζ (γ s) * derivWithin γ (Icc 0 T) s + 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.1 h' with h' | h'
      · rw [sub_eq_zero.1 h']; simp
      · rw [eq_neg_of_add_eq_zero_left h']; simp
    have h4 : HasDerivWithinAt (fun s => (ζ (γ s)).im)
        (Complex.imCLM (deriv ζ (γ s) * derivWithin γ (Icc 0 T) s)) (Icc a b) s := h3
    rw [Complex.imCLM_apply, hval] at h4
    exact h4
  intro s hs
  have hab : a ≤ b := hs.1.trans hs.2
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hder (fun _ _ => by simp)
    (convex_Icc a b) ⟨le_rfl, hab⟩ hs
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at this
  exact this

/-- **Holonomy step.**  If `S` is leaf-saturated inside a flow box, a point on the horizontal plaque
of an interior point of `S` is again an interior point of `S`. -/
theorem fx_p4_sat_interior {φ ζ : ℂ → ℂ} {N : Set ℂ} (hN : fx_IsFlowBox φ ζ N) {S : Set ℂ}
    (hS : ∀ z ∈ N, ∀ b ∈ N, b ∈ fx_leaf φ z → b ∈ S → z ∈ S) {x y : ℂ} (hx : x ∈ N)
    (hy : y ∈ N) (hxy : (ζ x).im = (ζ y).im) (hxS : x ∈ interior S) : y ∈ interior S := by
  set B := interior S ∩ N with hB
  have hBo : IsOpen (ζ '' B) :=
    fx_p4_flowBox_isOpen_image hN (isOpen_interior.inter hN.1) inter_subset_right
  have hζc : ContinuousOn ζ N := (fx_p4_flowBox_diffOn hN).continuousOn
  set h : ℂ → ℂ := fun z => ((ζ x).re : ℂ) + ((ζ z).im : ℂ) * I with hh
  have hhc : ContinuousOn h N := by
    have : Continuous fun w : ℂ => ((ζ x).re : ℂ) + ((w.im : ℝ) : ℂ) * I := by fun_prop
    exact this.comp_continuousOn hζc
  set O := N ∩ h ⁻¹' (ζ '' B) with hO
  have hOo : IsOpen O := hhc.isOpen_inter_preimage hN.1 hBo
  have hyO : y ∈ O := by
    refine ⟨hy, x, ⟨hxS, hx⟩, ?_⟩
    apply Complex.ext <;> simp [hh, hxy]
  have hOS : O ⊆ S := by
    rintro z ⟨hzN, b, ⟨hbS, hbN⟩, hb⟩
    have hbz : (ζ z).im = (ζ b).im := by rw [hb]; simp [hh]
    exact hS z hzN b hbN (fx_plaque_leaf hN hzN hbN hbz) (interior_subset hbS)
  exact interior_maximal hOS hOo hyO

/-- **Saturation of a transversal set is open** (holonomy along a compact trajectory): if every
regular point of `V` has a flow box in which `V` is the vertical plaque through it, the set of
regular points whose leaf meets `V` is open. -/
theorem fx_sat_open {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {V : Set ℂ}
    (hV : ∀ p ∈ V, φ p ≠ 0 → ∃ (ζ : ℂ → ℂ) (N : Set ℂ), p ∈ N ∧ fx_IsFlowBox φ ζ N ∧
      V ∩ N = {z | z ∈ N ∧ (ζ z).re = (ζ p).re}) :
    IsOpen {z | z ∈ unitDisc ∧ φ z ≠ 0 ∧ (fx_leaf φ z ∩ V).Nonempty} := by
  set S := {z | z ∈ unitDisc ∧ φ z ≠ 0 ∧ (fx_leaf φ z ∩ V).Nonempty} with hSdef
  -- `S` is leaf-saturated inside every flow box
  have hsat : ∀ {ζ : ℂ → ℂ} {N : Set ℂ}, fx_IsFlowBox φ ζ N →
      ∀ z ∈ N, ∀ b ∈ N, b ∈ fx_leaf φ z → b ∈ S → z ∈ S := by
    intro ζ N hN z hz b _ hbz hbS
    obtain ⟨-, -, v, hv, hvV⟩ := hbS
    exact ⟨hN.2.1 hz, (hN.2.2.2.1 z hz).1, v, fx_leaf_trans hφ hbz hv, hvV⟩
  -- regular points of `V` are interior points of `S`
  have hVint : ∀ p ∈ V, φ p ≠ 0 → p ∈ interior S := by
    intro p hpV hp0
    obtain ⟨ζ, N, hpN, hN, hVN⟩ := hV p hpV hp0
    obtain ⟨c, δ, _, hsq⟩ := hN.2.2.2.2
    refine interior_maximal (fun z hz => ?_) hN.1 hpN
    have hw : ((ζ p).re : ℂ) + ((ζ z).im : ℂ) * I ∈ ζ '' N := by
      have hp' : ζ p ∈ ζ '' N := ⟨p, hpN, rfl⟩
      have hz' : ζ z ∈ ζ '' N := ⟨z, hz, rfl⟩
      rw [hsq] at hp' hz' ⊢
      exact ⟨by simpa using hp'.1, by simpa using hz'.2⟩
    obtain ⟨b, hbN, hb⟩ := hw
    have hbV : b ∈ V := by
      have : b ∈ V ∩ N := by
        rw [hVN]
        exact ⟨hbN, by rw [hb]; simp⟩
      exact this.1
    exact ⟨hN.2.1 hz, (hN.2.2.2.1 z hz).1, b,
      fx_plaque_leaf hN hz hbN (by rw [hb]; simp), hbV⟩
  rw [isOpen_iff_mem_nhds]
  intro z hzS
  rw [← mem_interior_iff_mem_nhds]
  obtain ⟨hz, hz0, v, hv, hvV⟩ := hzS
  rcases hv with ⟨rfl, -, -⟩ | ⟨γ, T, hγ, hγ0, hγT⟩
  · exact hVint v hvV hz0
  -- holonomy along the trajectory from `z` to `v`
  have hvreg := hγ.2.2.1 T ⟨hγ.1.le, le_rfl⟩
  have hPT : γ T ∈ interior S := by rw [hγT]; exact hVint v hvV (hγT ▸ hvreg.2)
  have hloc : ∀ t ∈ Icc 0 T, ∀ᶠ t' in 𝓝[Icc 0 T] t,
      (γ t' ∈ interior S ↔ γ t ∈ interior S) := by
    intro t ht
    obtain ⟨hγt, hγt0⟩ := hγ.2.2.1 t ht
    obtain ⟨ζ, N, hpN, _, hN⟩ := fx_flowBox_exists hφ hγt hγt0 one_pos
    have hpre : γ ⁻¹' N ∈ 𝓝[Icc 0 T] t :=
      (hγ.2.1.continuousOn t ht).preimage_mem_nhdsWithin (hN.1.mem_nhds hpN)
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.1 hpre
    filter_upwards [inter_mem_nhdsWithin (Icc 0 T) (Metric.ball_mem_nhds t hε),
      self_mem_nhdsWithin] with t' ht' ht'I
    have ht'b : |t' - t| < ε := by
      have := ht'.2
      rwa [mem_ball, Real.dist_eq] at this
    have hint : ∀ s ∈ Icc (min t t') (max t t'), γ s ∈ N := by
      intro s hs
      apply hεsub
      have h1 := hs.1
      have h2 := hs.2
      rw [min_le_iff] at h1
      rw [le_max_iff] at h2
      rw [abs_lt] at ht'b
      refine ⟨?_, ?_, ?_⟩
      · rw [mem_ball, Real.dist_eq, abs_lt]
        constructor
        · rcases h1 with h1 | h1 <;> linarith
        · rcases h2 with h2 | h2 <;> linarith
      · exact le_trans (le_min ht.1 ht'I.1) hs.1
      · exact le_trans hs.2 (max_le ht.2 ht'I.2)
    have hmin0 : 0 ≤ min t t' := le_min ht.1 ht'I.1
    have hmaxT : max t t' ≤ T := max_le ht.2 ht'I.2
    have hc := fx_p4_htraj_im_const hN hγ hmin0 hmaxT hint
    have hct := hc t ⟨min_le_left _ _, le_max_left _ _⟩
    have hct' := hc t' ⟨min_le_right _ _, le_max_right _ _⟩
    have hIm : (ζ (γ t)).im = (ζ (γ t')).im := hct.trans hct'.symm
    have htN : γ t ∈ N := hint t ⟨min_le_left _ _, le_max_left _ _⟩
    have ht'N : γ t' ∈ N := hint t' ⟨min_le_right _ _, le_max_right _ _⟩
    exact ⟨fun h => fx_p4_sat_interior hN (hsat hN) ht'N htN hIm.symm h,
      fun h => fx_p4_sat_interior hN (hsat hN) htN ht'N hIm h⟩
  have h0 := fx_p4_preconn_prop isPreconnected_Icc (fun t => γ t ∈ interior S) hloc
    ⟨hγ.1.le, le_rfl⟩ ⟨le_rfl, hγ.1.le⟩ hPT
  rw [← hγ0]
  exact h0

/-! ## §3 The critical vertical forest -/

/-- The edge `i` is incident to `q`: `q` is its source or its (saddle) target. -/
def fx_Incident {ι : Type} (src : ι → ℂ) (dst : ι → Option ℂ) (i : ι) (q : ℂ) : Prop :=
  src i = q ∨ dst i = some q

/-- The outgoing tangent of the edge `i` at its end `q`: `par'(0)` at the source, `-par'(1)` at a
saddle target. -/
def fx_outTangent {ι : Type} (par : ι → ℝ → ℂ) (src : ι → ℂ) (i : ι) (q : ℂ) : ℂ :=
  if src i = q then derivWithin (par i) (Icc 0 1) 0 else -derivWithin (par i) (Icc 0 1) 1

/-- The ratio `r` of two tangent directions at a zero of order `m` is **blunt**: `r^(m+2) > 0` but
`r` is not a positive real, i.e. `arg r ∈ {2πk/(m+2) : 1 ≤ k ≤ m+1}`. -/
def fx_IsBluntRatio (m : ℕ) (r : ℂ) : Prop :=
  (r ^ (m + 2)).im = 0 ∧ 0 < (r ^ (m + 2)).re ∧ ¬ (r.im = 0 ∧ 0 < r.re)

/-- **The critical vertical forest** of `φ` in `Δ` .  The edges `i : ι` are
the maximal vertical trajectories leaving the zeros of `φ` in `Δ`, each listed once:
`par i : [0, 1) → Δ` is a `C¹` regular vertical arc from the zero `src i`, which either ends at
another zero (`dst i = some q`, a saddle connection, `C¹` on `[0, 1]`) or leaves every compact
subset of `Δ` (`dst i = none`). -/
structure fx_IsVForest (φ : ℂ → ℂ) {ι : Type} (par : ι → ℝ → ℂ) (src : ι → ℂ)
    (dst : ι → Option ℂ) : Prop where
  /-- `φ` has finitely many zeros in `Δ` -/
  zeros_finite : {q : ℂ | q ∈ unitDisc ∧ φ q = 0}.Finite
  /-- every edge is a regular vertical arc on `(0, 1)` -/
  vert : ∀ i, IsVerticalArc φ (par i) 0 1
  /-- the edges lie in `Δ` -/
  mem : ∀ i, ∀ t ∈ Ioo (0 : ℝ) 1, par i t ∈ unitDisc
  /-- the edges are injective -/
  inj : ∀ i, InjOn (par i) (Ioo 0 1)
  /-- the edges are `C¹` up to the source -/
  smooth : ∀ i, ContDiffOn ℝ 1 (par i) (Ico 0 1)
  /-- the source is a zero of `φ` in `Δ` -/
  src_zero : ∀ i, par i 0 = src i ∧ src i ∈ unitDisc ∧ φ (src i) = 0
  /-- nonzero tangent at the source -/
  src_tan : ∀ i, derivWithin (par i) (Icc 0 1) 0 ≠ 0
  /-- a saddle connection ends at another zero, `C¹` with nonzero tangent there -/
  saddle : ∀ i q, dst i = some q → q ∈ unitDisc ∧ φ q = 0 ∧ q ≠ src i ∧
    ContDiffOn ℝ 1 (par i) (Icc 0 1) ∧ par i 1 = q ∧ derivWithin (par i) (Icc 0 1) 1 ≠ 0
  /-- a boundary edge leaves every compact subset of `Δ` -/
  bdry : ∀ i, dst i = none → ∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc →
    ∀ᶠ t in 𝓝[<] (1 : ℝ), par i t ∉ K
  /-- distinct edges are disjoint -/
  disj : ∀ i j, i ≠ j → Disjoint (par i '' Ioo 0 1) (par j '' Ioo 0 1)
  /-- along an edge, a flow box meets the forest exactly in the vertical plaque of the edge -/
  box : ∀ i, ∀ t ∈ Ioo (0 : ℝ) 1, ∃ (ζ : ℂ → ℂ) (N : Set ℂ), par i t ∈ N ∧ fx_IsFlowBox φ ζ N ∧
    par i '' Ioo 0 1 ∩ N = {z | z ∈ N ∧ (ζ z).re = (ζ (par i t)).re} ∧
    ∀ j, j ≠ i → par j '' Ioo 0 1 ∩ N = ∅
  /-- at least three edges at every zero -/
  star_card : ∀ q ∈ unitDisc, φ q = 0 → 3 ≤ {i | fx_Incident src dst i q}.ncard
  /-- distinct edges at a zero leave it at blunt angles -/
  blunt : ∀ q ∈ unitDisc, φ q = 0 → ∀ i j, fx_Incident src dst i q → fx_Incident src dst j q →
    i ≠ j → ∃ m : ℕ, meromorphicOrderAt φ q = (m : ℤ) ∧
      fx_IsBluntRatio m (fx_outTangent par src i q / fx_outTangent par src j q)

/-- A **unit-speed vertical trajectory** of `φ` on the parameter set `I` (an open interval in all
uses): `γ` is `C¹` on `I`, runs through regular points of `Δ`, and `φ(γ t) γ'(t)² = -1`. -/
def fx_p3_VT (φ : ℂ → ℂ) (γ : ℝ → ℂ) (I : Set ℝ) : Prop :=
  ContDiffOn ℝ 1 γ I ∧ ∀ t ∈ I, γ t ∈ unitDisc ∧ φ (γ t) ≠ 0 ∧ φ (γ t) * deriv γ t ^ 2 = -1

/-- An open interval of parameters: open and order-connected. -/
def fx_p3_IsOI (I : Set ℝ) : Prop := IsOpen I ∧ I.OrdConnected

/-- `Ioo a b` is an open interval. -/
theorem fx_p3_isOI_Ioo (a b : ℝ) : fx_p3_IsOI (Ioo a b) := ⟨isOpen_Ioo, ordConnected_Ioo⟩

/-- `Ioi a` is an open interval. -/
theorem fx_p3_isOI_Ioi (a : ℝ) : fx_p3_IsOI (Ioi a) := ⟨isOpen_Ioi, ordConnected_Ioi⟩

/-- Intersections of open intervals are open intervals. -/
theorem fx_p3_IsOI.inter {I J : Set ℝ} (hI : fx_p3_IsOI I) (hJ : fx_p3_IsOI J) : fx_p3_IsOI (I ∩ J) :=
  ⟨hI.1.inter hJ.1, hI.2.inter hJ.2⟩

/-- Reflected open intervals are open intervals. -/
theorem fx_p3_IsOI.neg {I : Set ℝ} (hI : fx_p3_IsOI I) : fx_p3_IsOI {t | -t ∈ I} := by
  refine ⟨hI.1.preimage continuous_neg, ⟨fun x hx y hy z hz => ?_⟩⟩
  exact hI.2.out hy hx ⟨neg_le_neg hz.2, neg_le_neg hz.1⟩

/-- An open interval is preconnected. -/
theorem fx_p3_IsOI.isPreconnected {I : Set ℝ} (hI : fx_p3_IsOI I) : IsPreconnected I :=
  hI.2.isPreconnected

/-- Restriction of a trajectory. -/
theorem fx_p3_VT.mono {φ : ℂ → ℂ} {γ : ℝ → ℂ} {I J : Set ℝ} (h : fx_p3_VT φ γ I) (hJ : J ⊆ I) :
    fx_p3_VT φ γ J :=
  ⟨h.1.mono hJ, fun t ht => h.2 t (hJ ht)⟩

/-- A trajectory is differentiable at the points of its (open) parameter set. -/
theorem fx_p3_VT.hasDerivAt {φ : ℂ → ℂ} {γ : ℝ → ℂ} {I : Set ℝ} (h : fx_p3_VT φ γ I) (hI : IsOpen I)
    {t : ℝ} (ht : t ∈ I) : HasDerivAt γ (deriv γ t) t :=
  ((h.1.differentiableOn one_ne_zero t ht).differentiableAt (hI.mem_nhds ht)).hasDerivAt

/-- A trajectory is continuous. -/
theorem fx_p3_VT.continuousOn {φ : ℂ → ℂ} {γ : ℝ → ℂ} {I : Set ℝ} (h : fx_p3_VT φ γ I) :
    ContinuousOn γ I :=
  h.1.continuousOn

/-- The velocity of a trajectory never vanishes. -/
theorem fx_p3_VT.deriv_ne {φ : ℂ → ℂ} {γ : ℝ → ℂ} {I : Set ℝ} (h : fx_p3_VT φ γ I) {t : ℝ}
    (ht : t ∈ I) : deriv γ t ≠ 0 := by
  intro e
  have := (h.2 t ht).2.2
  rw [e] at this
  norm_num at this

/-- Time shift of a trajectory. -/
theorem fx_p3_VT.shift {φ : ℂ → ℂ} {γ : ℝ → ℂ} {I : Set ℝ} (h : fx_p3_VT φ γ I) (c : ℝ) :
    fx_p3_VT φ (fun t => γ (t + c)) {t | t + c ∈ I} := by
  refine ⟨h.1.comp (contDiff_id.add contDiff_const).contDiffOn fun t ht => ht, fun t ht => ?_⟩
  rw [deriv_comp_add_const]
  exact h.2 _ ht

/-- Time reversal of a trajectory. -/
theorem fx_p3_VT.reverse {φ : ℂ → ℂ} {γ : ℝ → ℂ} {I : Set ℝ} (h : fx_p3_VT φ γ I) (c : ℝ) :
    fx_p3_VT φ (fun t => γ (c - t)) {t | c - t ∈ I} := by
  refine ⟨h.1.comp (contDiff_const.sub contDiff_id).contDiffOn fun t ht => ht, fun t ht => ?_⟩
  rw [deriv_comp_const_sub, neg_sq]
  exact h.2 _ ht

/-- A trajectory, restricted to a compact sub-interval and shifted, is a unit-speed horizontal
trajectory of `-φ` in the sense of `fx_IsHTraj`. -/
theorem fx_p3_VT.htraj {φ : ℂ → ℂ} {γ : ℝ → ℂ} {I : Set ℝ} (h : fx_p3_VT φ γ I) (hI : IsOpen I)
    {c T : ℝ} (hT : 0 < T) (hsub : Icc c (c + T) ⊆ I) :
    fx_IsHTraj (-φ) (fun s => γ (c + s)) T ∧
      derivWithin (fun s => γ (c + s)) (Icc 0 T) 0 = deriv γ c := by
  have hmem : ∀ s ∈ Icc (0 : ℝ) T, c + s ∈ I := fun s hs =>
    hsub ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hd : ∀ s ∈ Icc (0 : ℝ) T, HasDerivAt (fun s => γ (c + s)) (deriv γ (c + s)) s := by
    intro s hs
    exact HasDerivAt.comp_const_add c s (h.hasDerivAt hI (hmem s hs))
  have hdw : ∀ s ∈ Icc (0 : ℝ) T,
      derivWithin (fun s => γ (c + s)) (Icc 0 T) s = deriv γ (c + s) := fun s hs =>
    (hd s hs).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hT s hs)
  refine ⟨⟨hT, ?_, fun s hs => ?_, fun s hs => ?_⟩, ?_⟩
  · exact h.1.comp (contDiff_const.add contDiff_id).contDiffOn fun s hs => hmem s hs
  · obtain ⟨h1, h2, -⟩ := h.2 _ (hmem s hs)
    exact ⟨h1, neg_ne_zero.2 h2⟩
  · rw [hdw s hs]
    obtain ⟨-, -, h3⟩ := h.2 _ (hmem s hs)
    simp only [Pi.neg_apply, neg_mul, h3, neg_neg]
  · rw [hdw 0 ⟨le_rfl, hT.le⟩, add_zero]

/-- **Forward uniqueness** of trajectories (from `fx_htraj_unique` for `-φ`). -/
theorem fx_p3_VT.unique_fwd {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {γ₁ γ₂ : ℝ → ℂ}
    {I₁ I₂ : Set ℝ} (hI₁ : fx_p3_IsOI I₁) (hI₂ : fx_p3_IsOI I₂) (h₁ : fx_p3_VT φ γ₁ I₁)
    (h₂ : fx_p3_VT φ γ₂ I₂) {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ I₁) (ht₂ : t₂ ∈ I₂) (hx : γ₁ t₁ = γ₂ t₂)
    (hv : deriv γ₁ t₁ = deriv γ₂ t₂) {s : ℝ} (hs : 0 ≤ s) (hs₁ : t₁ + s ∈ I₁)
    (hs₂ : t₂ + s ∈ I₂) : γ₁ (t₁ + s) = γ₂ (t₂ + s) := by
  rcases hs.eq_or_lt with rfl | hs'
  · simpa using hx
  have hsub₁ : Icc t₁ (t₁ + s) ⊆ I₁ := hI₁.2.out ht₁ hs₁
  have hsub₂ : Icc t₂ (t₂ + s) ⊆ I₂ := hI₂.2.out ht₂ hs₂
  obtain ⟨hh₁, hd₁⟩ := h₁.htraj hI₁.1 hs' hsub₁
  obtain ⟨hh₂, hd₂⟩ := h₂.htraj hI₂.1 hs' hsub₂
  have := fx_htraj_unique hφ.neg hh₁ hh₂ (by simpa using hx) (by rw [hd₁, hd₂, hv]) s
    ⟨hs, by rw [min_self]⟩
  exact this

/-- **Uniqueness** of trajectories, in both time directions. -/
theorem fx_p3_VT.unique {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {γ₁ γ₂ : ℝ → ℂ}
    {I₁ I₂ : Set ℝ} (hI₁ : fx_p3_IsOI I₁) (hI₂ : fx_p3_IsOI I₂) (h₁ : fx_p3_VT φ γ₁ I₁)
    (h₂ : fx_p3_VT φ γ₂ I₂) {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ I₁) (ht₂ : t₂ ∈ I₂) (hx : γ₁ t₁ = γ₂ t₂)
    (hv : deriv γ₁ t₁ = deriv γ₂ t₂) {s : ℝ} (hs₁ : t₁ + s ∈ I₁) (hs₂ : t₂ + s ∈ I₂) :
    γ₁ (t₁ + s) = γ₂ (t₂ + s) := by
  rcases le_or_gt 0 s with hs | hs
  · exact h₁.unique_fwd hφ hI₁ hI₂ h₂ ht₁ ht₂ hx hv hs hs₁ hs₂
  -- backward: reverse both trajectories
  have hr₁ := h₁.reverse 0
  have hr₂ := h₂.reverse 0
  have hJ₁ : fx_p3_IsOI {t | 0 - t ∈ I₁} := by simpa using hI₁.neg
  have hJ₂ : fx_p3_IsOI {t | 0 - t ∈ I₂} := by simpa using hI₂.neg
  have h := hr₁.unique_fwd hφ hJ₁ hJ₂ hr₂ (t₁ := -t₁) (t₂ := -t₂) (by simpa using ht₁)
    (by simpa using ht₂) (by simpa using hx)
    (by rw [deriv_comp_const_sub, deriv_comp_const_sub]; simpa using hv) (s := -s) (by linarith)
    (by show 0 - (-t₁ + -s) ∈ I₁; convert hs₁ using 1; ring)
    (by show 0 - (-t₂ + -s) ∈ I₂; convert hs₂ using 1; ring)
  convert h using 2 <;> ring

/-- **Uniqueness, opposite velocities**: a trajectory meeting another with the opposite velocity
retraces it backwards. -/
theorem fx_p3_VT.unique_rev {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {γ₁ γ₂ : ℝ → ℂ}
    {I₁ I₂ : Set ℝ} (hI₁ : fx_p3_IsOI I₁) (hI₂ : fx_p3_IsOI I₂) (h₁ : fx_p3_VT φ γ₁ I₁)
    (h₂ : fx_p3_VT φ γ₂ I₂) {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ I₁) (ht₂ : t₂ ∈ I₂) (hx : γ₁ t₁ = γ₂ t₂)
    (hv : deriv γ₁ t₁ = -deriv γ₂ t₂) {s : ℝ} (hs₁ : t₁ + s ∈ I₁) (hs₂ : t₂ - s ∈ I₂) :
    γ₁ (t₁ + s) = γ₂ (t₂ - s) := by
  have hr₂ := h₂.reverse 0
  have hJ₂ : fx_p3_IsOI {t | 0 - t ∈ I₂} := by simpa using hI₂.neg
  have h := h₁.unique hφ hI₁ hJ₂ hr₂ (t₂ := -t₂) ht₁ (by simpa using ht₂) (by simpa using hx)
    (by rw [deriv_comp_const_sub]; simpa using hv) (s := s) hs₁
    (by show 0 - (-t₂ + s) ∈ I₂; convert hs₂ using 1; ring)
  rw [h]
  congr 1
  ring

/-- Two trajectories which agree on a nonempty open set agree on their common interval. -/
theorem fx_p3_VT.eqOn_of_eqOn {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {γ₁ γ₂ : ℝ → ℂ}
    {I₁ I₂ : Set ℝ} (hI₁ : fx_p3_IsOI I₁) (hI₂ : fx_p3_IsOI I₂) (h₁ : fx_p3_VT φ γ₁ I₁)
    (h₂ : fx_p3_VT φ γ₂ I₂) {J : Set ℝ} (hJ : IsOpen J) (hJne : J.Nonempty) (hJ₁ : J ⊆ I₁)
    (hJ₂ : J ⊆ I₂) (heq : EqOn γ₁ γ₂ J) : EqOn γ₁ γ₂ (I₁ ∩ I₂) := by
  obtain ⟨c, hc⟩ := hJne
  have hev : γ₁ =ᶠ[𝓝 c] γ₂ := Filter.eventually_of_mem (hJ.mem_nhds hc) heq
  intro t ht
  have h := h₁.unique hφ hI₁ hI₂ h₂ (hJ₁ hc) (hJ₂ hc) (heq hc) hev.deriv_eq (s := t - c)
    (by simpa using ht.1) (by simpa using ht.2)
  simpa using h

/-- Trajectories are injective (`fx_htraj_injOn` for `-φ`). -/
theorem fx_p3_VT.injOn {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {γ : ℝ → ℂ} {I : Set ℝ} (hI : fx_p3_IsOI I)
    (h : fx_p3_VT φ γ I) : InjOn γ I := by
  have hne' : ∃ z ∈ unitDisc, (-φ) z ≠ 0 := by
    obtain ⟨z, hz, hz0⟩ := hne
    exact ⟨z, hz, by simpa using hz0⟩
  suffices key : ∀ t ∈ I, ∀ t' ∈ I, t < t' → γ t ≠ γ t' by
    intro t ht t' ht' e
    rcases lt_trichotomy t t' with hlt | heq | hgt
    · exact absurd e (key t ht t' ht' hlt)
    · exact heq
    · exact absurd e.symm (key t' ht' t ht hgt)
  intro t ht t' ht' hlt e
  have hT : 0 < t' - t := by linarith
  have hsub : Icc t (t + (t' - t)) ⊆ I := by
    rw [add_sub_cancel]; exact hI.2.out ht ht'
  obtain ⟨hh, -⟩ := h.htraj hI.1 hT hsub
  have hinj := fx_htraj_injOn hφ.neg hne' hh
  have := hinj ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩ (by simp only [add_zero, add_sub_cancel]; exact e)
  linarith

/-- **Gluing**: being a trajectory is a local property. -/
theorem fx_p3_VT.of_local {φ : ℂ → ℂ} {γ : ℝ → ℂ} {I : Set ℝ}
    (h : ∀ t ∈ I, ∃ (γ' : ℝ → ℂ) (J : Set ℝ), IsOpen J ∧ t ∈ J ∧ fx_p3_VT φ γ' J ∧ EqOn γ γ' J) :
    fx_p3_VT φ γ I := by
  refine ⟨contDiffOn_of_locally_contDiffOn fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨γ', J, hJ, htJ, hγ', heq⟩ := h t ht
    exact ⟨J, hJ, htJ, (hγ'.1.mono inter_subset_right).congr fun s hs => heq hs.2⟩
  · obtain ⟨γ', J, hJ, htJ, hγ', heq⟩ := h t ht
    have hev : γ =ᶠ[𝓝 t] γ' := Filter.eventually_of_mem (hJ.mem_nhds htJ) heq
    rw [hev.deriv_eq, heq htJ]
    exact hγ'.2 t htJ

/-- In a regular chart, the pulled-back vertical lines `s ↦ ψ(w + s e)` (`e² = -1`) are unit-speed
vertical trajectories. -/
theorem fx_p3_RegChart.vseg {φ ζ : ℂ → ℂ} {p : ℂ} {r ρ0 : ℝ} (hR : fx_p3_RegChart φ ζ p r ρ0)
    {w e : ℂ} (he : e ^ 2 = -1) {J : Set ℝ}
    (hJV : ∀ s ∈ J, w + (s : ℂ) * e ∈ ζ '' ball p r) :
    fx_p3_VT φ (fun s => Function.invFunOn ζ (ball p r) (w + (s : ℂ) * e)) J := by
  obtain ⟨hopen, -, hψ⟩ := hR.inv
  obtain ⟨-, -, hBD, -, -, han, -⟩ := hR
  set ψ := Function.invFunOn ζ (ball p r) with hψdef
  have hℓd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => w + (s : ℂ) * e) e s := fun s => by
    simpa using ((hasDerivAt_id' s).ofReal_comp.mul_const e).const_add w
  have hd : ∀ s ∈ J, HasDerivAt (fun s : ℝ => ψ (w + (s : ℂ) * e))
      ((deriv ζ (ψ (w + (s : ℂ) * e)))⁻¹ * e) s := fun s hs => by
    have h := (hψ _ (hJV s hs)).2.2.comp s (hℓd s)
    exact h
  refine ⟨?_, fun s hs => ?_⟩
  · have hψc : ContDiffOn ℂ 1 ψ (ζ '' ball p r) := by
      refine DifferentiableOn.contDiffOn (fun w hw => ?_) hopen
      exact (hψ w hw).2.2.differentiableAt.differentiableWithinAt
    have hℓc : ContDiff ℝ 1 (fun s : ℝ => w + (s : ℂ) * e) :=
      contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)
    exact (hψc.restrict_scalars ℝ).comp hℓc.contDiffOn hJV
  · have hmem := (hψ _ (hJV s hs)).1
    obtain ⟨-, h2, h3⟩ := han _ (ball_subset_closedBall hmem)
    refine ⟨hBD (ball_subset_closedBall hmem), ?_, ?_⟩
    · rw [← h2]
      exact pow_ne_zero 2 h3
    · rw [(hd s hs).deriv, mul_pow, he, inv_pow, ← h2]
      field_simp

/-- **Local form of a trajectory in a regular chart**: near a time `t₀` with `γ t₀ ∈ ball p r`,
`γ(t₀ + s) = ψ(ζ(γ t₀) + s e)` with `e = ζ'(γ t₀) γ'(t₀)`, `e² = -1`, as long as the chart line stays
in `ball 0 ρ0`. -/
theorem fx_p3_RegChart.local_form {φ ζ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {p : ℂ}
    {r ρ0 : ℝ} (hR : fx_p3_RegChart φ ζ p r ρ0) {γ : ℝ → ℂ} {I : Set ℝ} (hI : fx_p3_IsOI I)
    (hγ : fx_p3_VT φ γ I) {t₀ : ℝ} (ht₀ : t₀ ∈ I) (hγt₀ : γ t₀ ∈ ball p r) :
    (deriv ζ (γ t₀) * deriv γ t₀) ^ 2 = -1 ∧
      ∀ s : ℝ, t₀ + s ∈ I → |s| < ρ0 - ‖ζ (γ t₀)‖ →
        γ (t₀ + s) = Function.invFunOn ζ (ball p r)
          (ζ (γ t₀) + (s : ℂ) * (deriv ζ (γ t₀) * deriv γ t₀)) := by
  obtain ⟨hopen, hleft, hψ⟩ := hR.inv
  have han := hR.2.2.2.2.2.1
  have hρB := hR.2.2.2.2.2.2
  obtain ⟨-, h2, h3⟩ := han _ (ball_subset_closedBall hγt₀)
  set e := deriv ζ (γ t₀) * deriv γ t₀ with he
  set w₀ := ζ (γ t₀) with hw₀
  have he2 : e ^ 2 = -1 := by
    rw [he, mul_pow, h2]
    exact (hγ.2 t₀ ht₀).2.2
  have hen : ‖e‖ = 1 := by
    have h := congr_arg norm he2
    rw [norm_pow, norm_neg, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg e) two_ne_zero).1 h
  refine ⟨he2, fun s hs hsρ => ?_⟩
  set R := ρ0 - ‖w₀‖ with hR'
  have hJV : ∀ s ∈ Ioo (-R) R, w₀ + (s : ℂ) * e ∈ ζ '' ball p r := by
    intro s' hs'
    apply hρB
    rw [mem_ball_zero_iff]
    calc ‖w₀ + (s' : ℂ) * e‖ ≤ ‖w₀‖ + ‖(s' : ℂ) * e‖ := norm_add_le _ _
      _ = ‖w₀‖ + |s'| := by rw [norm_mul, hen, mul_one, Complex.norm_real, Real.norm_eq_abs]
      _ < ‖w₀‖ + R := by
          have : |s'| < R := abs_lt.2 ⟨hs'.1, hs'.2⟩
          linarith
      _ = ρ0 := by rw [hR']; ring
  have hβ := hR.vseg he2 hJV
  have hR0 : 0 < R := lt_of_le_of_lt (abs_nonneg s) hsρ
  have h0 : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR0⟩
  have hβ0 : Function.invFunOn ζ (ball p r) (w₀ + ((0 : ℝ) : ℂ) * e) = γ t₀ := by
    rw [Complex.ofReal_zero, zero_mul, add_zero, hw₀]
    exact hleft _ hγt₀
  have hβd : deriv (fun s : ℝ => Function.invFunOn ζ (ball p r) (w₀ + (s : ℂ) * e)) 0 =
      deriv γ t₀ := by
    have hℓd : HasDerivAt (fun s : ℝ => w₀ + (s : ℂ) * e) e 0 := by
      simpa using ((hasDerivAt_id' (0 : ℝ)).ofReal_comp.mul_const e).const_add w₀
    have hmem : w₀ + ((0 : ℝ) : ℂ) * e ∈ ζ '' ball p r := hJV 0 h0
    have hd := (hψ _ hmem).2.2.comp (0 : ℝ) hℓd
    have hd' : HasDerivAt (fun s : ℝ => Function.invFunOn ζ (ball p r) (w₀ + (s : ℂ) * e))
        ((deriv ζ (Function.invFunOn ζ (ball p r) (w₀ + ((0 : ℝ) : ℂ) * e)))⁻¹ * e) 0 := hd
    rw [hd'.deriv, hβ0, he]
    field_simp
  have h := hγ.unique hφ hI (fx_p3_isOI_Ioo (-R) R) hβ ht₀ h0 hβ0.symm hβd.symm (s := s) hs
    (by rw [zero_add]; exact ⟨by linarith [neg_abs_le s], lt_of_le_of_lt (le_abs_self s) hsρ⟩)
  rw [h, zero_add]

/-- A zero `q ∈ Δ` of a tame `φ ≢ 0` has a finite positive order `m`: `φ = (z - q)^m g` near `q`
with `g q ≠ 0`, and `meromorphicOrderAt φ q = m`. -/
theorem fx_p3_zero_order {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {q : ℂ} (hq : q ∈ unitDisc) (hq0 : φ q = 0) :
    ∃ m : ℕ, 0 < m ∧ meromorphicOrderAt φ q = (m : ℤ) ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g q ∧ g q ≠ 0 ∧ ∀ᶠ z in 𝓝 q, φ z = (z - q) ^ m * g z := by
  have hDB : unitDisc ⊆ ball (0 : ℂ) ρ := ball_subset_ball hρ.le
  have han : AnalyticOnNhd ℂ φ (ball 0 ρ) := hφ.analyticOnNhd isOpen_ball
  have hqa : AnalyticAt ℂ φ q := han q (hDB hq)
  have htop : analyticOrderAt φ q ≠ ⊤ := by
    intro h
    obtain ⟨z, hz, hz0⟩ := hne
    have h0 : φ =ᶠ[𝓝 q] 0 := analyticOrderAt_eq_top.1 h
    have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 ρ).isPreconnected
      (hDB hq) h0 (hDB hz)
    exact hz0 this
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 htop
  have hm0 : m ≠ 0 := by
    rintro rfl
    have h1 : analyticOrderAt φ q ≠ 0 := analyticOrderAt_ne_zero.2 ⟨hqa, hq0⟩
    exact h1 hm.symm
  obtain ⟨g, hg, hg0, hfac⟩ := hqa.analyticOrderAt_eq_natCast.1 hm.symm
  refine ⟨m, Nat.pos_of_ne_zero hm0, ?_, g, hg, hg0, ?_⟩
  · rw [hqa.meromorphicOrderAt_eq, ← hm]
    rfl
  · filter_upwards [hfac] with z hz
    rw [hz, smul_eq_mul]

/-- **Zero chart data** at a zero `q` of order `m`: a natural parameter `ζ` (`ζ q = 0`), analytic and
injective on `closedBall q r ⊆ Δ` with `ζ' ≠ 0` and `φ = ((m+2)/2)² ζ^m ζ'²` there, and
`ball 0 ρ0 ⊆ ζ(ball q r)`. -/
def fx_p3_ZeroChart (φ ζ : ℂ → ℂ) (q : ℂ) (m : ℕ) (r ρ0 : ℝ) : Prop :=
  0 < r ∧ 0 < ρ0 ∧ closedBall q r ⊆ unitDisc ∧ ζ q = 0 ∧ InjOn ζ (closedBall q r) ∧
    (∀ z ∈ closedBall q r, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      φ z = ((m + 2 : ℂ) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2) ∧
    ball 0 ρ0 ⊆ ζ '' ball q r

/-- Zero charts exist (`eq25_5_natural_parameter_zero`, then the inverse function theorem as in
`psa_chart`). -/
theorem fx_p3_zeroChart_exists {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ)
    (hφ : DifferentiableOn ℂ φ (ball 0 ρ)) (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {q : ℂ}
    (hq : q ∈ unitDisc) (hq0 : φ q = 0) :
    ∃ m : ℕ, 0 < m ∧ meromorphicOrderAt φ q = (m : ℤ) ∧
      ∃ (ζ : ℂ → ℂ) (r ρ0 : ℝ), fx_p3_ZeroChart φ ζ q m r ρ0 := by
  obtain ⟨m, hm, hord, g, hg, hg0, hfac⟩ := fx_p3_zero_order hρ hφ hne hq hq0
  refine ⟨m, hm, hord, ?_⟩
  obtain ⟨ζ, hζ, hζ0, hζ'0, hζφ⟩ := eq25_5_natural_parameter_zero hm hg hg0 hfac
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, ∀ᶠ x in 𝓝 q, G (ζ x) = x :=
    ⟨_, hζ.hasStrictDerivAt.eventually_left_inverse hζ'0⟩
  have hd' : ∀ᶠ z in 𝓝 q, deriv ζ z ≠ 0 := hζ.deriv.continuousAt.eventually_ne hζ'0
  have hall : ∀ᶠ z in 𝓝 q, AnalyticAt ℂ ζ z ∧ deriv ζ z ≠ 0 ∧
      φ z = ((m + 2 : ℂ) / 2) ^ 2 * ζ z ^ m * deriv ζ z ^ 2 ∧ z ∈ unitDisc ∧ G (ζ z) = z := by
    filter_upwards [hζ.eventually_analyticAt, hd', hζφ, isOpen_ball.mem_nhds hq, hG]
      with z h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hall
  have hmem : ∀ z ∈ closedBall q (ε / 2), dist z q < ε := fun z hz =>
    lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith)
  have hinj : InjOn ζ (closedBall q (ε / 2)) := by
    intro x hx y hy hxy
    have hx' := (hball (hmem x hx)).2.2.2.2
    have hy' := (hball (hmem y hy)).2.2.2.2
    rw [← hx', ← hy', hxy]
  have hr : 0 < ε / 2 := by positivity
  obtain ⟨hopen, -⟩ := psa_inverse hr hinj fun z hz =>
    ⟨(hball (hmem z hz)).1, (hball (hmem z hz)).2.1⟩
  have h0mem : (0 : ℂ) ∈ ζ '' ball q (ε / 2) := ⟨q, mem_ball_self hr, hζ0⟩
  obtain ⟨ρ0, hρ0, hρB⟩ := Metric.isOpen_iff.1 hopen 0 h0mem
  exact ⟨ζ, ε / 2, ρ0, hr, hρ0, fun z hz => (hball (hmem z hz)).2.2.2.1, hζ0, hinj,
    fun z hz => ⟨(hball (hmem z hz)).1, (hball (hmem z hz)).2.1, (hball (hmem z hz)).2.2.1⟩,
    hρB⟩

/-- The inverse `ψ = ζ⁻¹` of a zero chart (`psa_inverse`). -/
theorem fx_p3_ZeroChart.inv {φ ζ : ℂ → ℂ} {q : ℂ} {m : ℕ} {r ρ0 : ℝ}
    (hZ : fx_p3_ZeroChart φ ζ q m r ρ0) :
    IsOpen (ζ '' ball q r) ∧ (∀ z ∈ ball q r, Function.invFunOn ζ (ball q r) (ζ z) = z) ∧
      ∀ w ∈ ζ '' ball q r, Function.invFunOn ζ (ball q r) w ∈ ball q r ∧
        ζ (Function.invFunOn ζ (ball q r) w) = w ∧
        HasDerivAt (Function.invFunOn ζ (ball q r))
          (deriv ζ (Function.invFunOn ζ (ball q r) w))⁻¹ w := by
  obtain ⟨hr, -, -, -, hinj, han, -⟩ := hZ
  obtain ⟨hopen, hψ⟩ := psa_inverse hr hinj fun z hz => ⟨(han z hz).1, (han z hz).2.1⟩
  exact ⟨hopen, fun z hz => (hinj.mono ball_subset_closedBall).leftInvOn_invFunOn hz, hψ⟩

/-- In a zero chart, `q` is the only zero of `φ`. -/
theorem fx_p3_ZeroChart.ne_zero {φ ζ : ℂ → ℂ} {q : ℂ} {m : ℕ} {r ρ0 : ℝ}
    (hZ : fx_p3_ZeroChart φ ζ q m r ρ0) {z : ℂ} (hz : z ∈ closedBall q r) (hzq : z ≠ q) :
    φ z ≠ 0 := by
  obtain ⟨hr, -, -, hζ0, hinj, han, -⟩ := hZ
  obtain ⟨-, h2, h3⟩ := han z hz
  rw [h3]
  have hζz : ζ z ≠ 0 := by
    intro e
    exact hzq (hinj hz (mem_closedBall_self hr.le) (by rw [e, hζ0]))
  have hc : ((m + 2 : ℂ) / 2) ≠ 0 := by
    have : (m + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : m + 2 ≠ 0)
    exact div_ne_zero this two_ne_zero
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero m hζz)) (pow_ne_zero 2 h2)

/-- The critical directions at a zero of order `m`: `u^(m+2) = -1` has finitely many solutions. -/
theorem fx_p3_roots_finite (m : ℕ) : {u : ℂ | u ^ (m + 2) = -1}.Finite := by
  refine (Polynomial.nthRoots (m + 2) (-1 : ℂ)).toFinset.finite_toSet.subset ?_
  intro u hu
  rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)]
  exact hu

/-- A critical direction has modulus one. -/
theorem fx_p3_root_norm {m : ℕ} {u : ℂ} (hu : u ^ (m + 2) = -1) : ‖u‖ = 1 := by
  have h := congr_arg norm hu
  rw [norm_pow, norm_neg, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg u) (by omega)).1 h

/-- The exponent `κ = 2/(m+2)` of the model rays, and the relation `κ (m+2) = 2`. -/
theorem fx_p3_kappa_mul (m : ℕ) : 2 / ((m : ℝ) + 2) * ((m : ℝ) + 2) = 2 := by
  have : ((m : ℝ) + 2) ≠ 0 := by positivity
  field_simp

/-- `(t^κ)^m (t^(κ-1))² = 1` for `t > 0`, `κ = 2/(m+2)`. -/
theorem fx_p3_kappa_pow_identity (m : ℕ) {t : ℝ} (ht : 0 < t) :
    (t ^ (2 / ((m : ℝ) + 2))) ^ m * (t ^ (2 / ((m : ℝ) + 2) - 1)) ^ 2 = 1 := by
  rw [← Real.rpow_mul_natCast ht.le, ← Real.rpow_mul_natCast ht.le, ← Real.rpow_add ht]
  have hk := fx_p3_kappa_mul m
  have : 2 / ((m : ℝ) + 2) * (m : ℝ) + (2 / ((m : ℝ) + 2) - 1) * ((2 : ℕ) : ℝ) = 0 := by
    push_cast
    linear_combination hk
  rw [this, Real.rpow_zero]

/-- **The model critical rays** at a zero: `t ↦ ψ(t^κ u)` (`κ = 2/(m+2)`, `u^(m+2) = -1`) is a
unit-speed vertical trajectory for `0 < t < ρ0^(1/κ)`. -/
theorem fx_p3_ZeroChart.model {φ ζ : ℂ → ℂ} {q : ℂ} {m : ℕ} {r ρ0 : ℝ}
    (hZ : fx_p3_ZeroChart φ ζ q m r ρ0) {u : ℂ} (hu : u ^ (m + 2) = -1) :
    fx_p3_VT φ (fun t : ℝ => Function.invFunOn ζ (ball q r)
      (((t ^ (2 / ((m : ℝ) + 2)) : ℝ) : ℂ) * u)) (Ioo 0 (ρ0 ^ (((m : ℝ) + 2) / 2))) := by
  obtain ⟨hopen, -, hψ⟩ := hZ.inv
  have hZ' := hZ
  obtain ⟨hr, hρ0, hBD, hζ0, hinj, han, hρB⟩ := hZ'
  set κ : ℝ := 2 / ((m : ℝ) + 2) with hκ
  have hκ0 : 0 < κ := by positivity
  set ψ := Function.invFunOn ζ (ball q r) with hψdef
  have hun := fx_p3_root_norm hu
  have hmemV : ∀ t ∈ Ioo (0 : ℝ) (ρ0 ^ (((m : ℝ) + 2) / 2)),
      ((t ^ κ : ℝ) : ℂ) * u ∈ ζ '' ball q r := by
    intro t ht
    apply hρB
    rw [mem_ball_zero_iff, norm_mul, hun, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    have h1 : t ^ κ < (ρ0 ^ (((m : ℝ) + 2) / 2)) ^ κ :=
      Real.rpow_lt_rpow ht.1.le ht.2 hκ0
    have h2 : (ρ0 ^ (((m : ℝ) + 2) / 2)) ^ κ = ρ0 := by
      rw [← Real.rpow_mul hρ0.le]
      have : ((m : ℝ) + 2) / 2 * κ = 1 := by
        rw [hκ]; have : ((m : ℝ) + 2) ≠ 0 := by positivity
        field_simp
      rw [this, Real.rpow_one]
    rwa [h2] at h1
  have hℓd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => ((t ^ κ : ℝ) : ℂ) * u)
      (((κ * t ^ (κ - 1) : ℝ) : ℂ) * u) t := fun t ht =>
    ((Real.hasDerivAt_rpow_const (Or.inl ht.ne')).ofReal_comp).mul_const u
  have hd : ∀ t ∈ Ioo (0 : ℝ) (ρ0 ^ (((m : ℝ) + 2) / 2)),
      HasDerivAt (fun t : ℝ => ψ (((t ^ κ : ℝ) : ℂ) * u))
        ((deriv ζ (ψ (((t ^ κ : ℝ) : ℂ) * u)))⁻¹ * (((κ * t ^ (κ - 1) : ℝ) : ℂ) * u)) t := by
    intro t ht
    have h := (hψ _ (hmemV t ht)).2.2.comp t (hℓd t ht.1)
    exact h
  refine ⟨?_, fun t ht => ?_⟩
  · have hψc : ContDiffOn ℂ 1 ψ (ζ '' ball q r) := by
      refine DifferentiableOn.contDiffOn (fun w hw => ?_) hopen
      exact (hψ w hw).2.2.differentiableAt.differentiableWithinAt
    have hℓc : ContDiffOn ℝ 1 (fun t : ℝ => ((t ^ κ : ℝ) : ℂ) * u)
        (Ioo 0 (ρ0 ^ (((m : ℝ) + 2) / 2))) := by
      intro t ht
      have h1 : ContDiffAt ℝ 1 (fun t : ℝ => t ^ κ) t := Real.contDiffAt_rpow_const_of_ne ht.1.ne'
      have h2 : ContDiffAt ℝ 1 (fun t : ℝ => ((t ^ κ : ℝ) : ℂ) * u) t :=
        (Complex.ofRealCLM.contDiff.contDiffAt.comp t h1).mul contDiffAt_const
      exact h2.contDiffWithinAt
    exact (hψc.restrict_scalars ℝ).comp hℓc hmemV
  · obtain ⟨hmem, hζψ, -⟩ := hψ _ (hmemV t ht)
    have hcb : ψ (((t ^ κ : ℝ) : ℂ) * u) ∈ closedBall q r := ball_subset_closedBall hmem
    obtain ⟨-, hζ'0, hφeq⟩ := han _ hcb
    have hw0 : ((t ^ κ : ℝ) : ℂ) * u ≠ 0 := by
      refine mul_ne_zero ?_ (by rintro rfl; simp at hun)
      exact Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos ht.1 _).ne'
    have hne : ψ (((t ^ κ : ℝ) : ℂ) * u) ≠ q := by
      intro e
      apply hw0
      rw [← hζψ, e, hζ0]
    refine ⟨hBD hcb, hZ.ne_zero hcb hne, ?_⟩
    rw [(hd t ht).deriv, hφeq, hζψ]
    have hid := fx_p3_kappa_pow_identity m ht.1
    have hpk : ((m : ℝ) + 2) / 2 * κ = 1 := by
      rw [hκ]; have : ((m : ℝ) + 2) ≠ 0 := by positivity
      field_simp
    have hidC : (((t ^ κ) ^ m * (t ^ (κ - 1)) ^ 2 : ℝ) : ℂ) = 1 := by rw [hid]; simp
    have hpkC : ((((m : ℝ) + 2) / 2 * κ : ℝ) : ℂ) = 1 := by rw [hpk]; simp
    push_cast at hidC hpkC
    have e1 : ((m + 2 : ℂ) / 2) ^ 2 * (((t ^ κ : ℝ) : ℂ) * u) ^ m *
        deriv ζ (ψ (((t ^ κ : ℝ) : ℂ) * u)) ^ 2 *
        ((deriv ζ (ψ (((t ^ κ : ℝ) : ℂ) * u)))⁻¹ * (((κ * t ^ (κ - 1) : ℝ) : ℂ) * u)) ^ 2 =
        ((((m : ℂ) + 2) / 2 * (κ : ℂ)) ^ 2 * (((t ^ κ : ℝ) : ℂ) ^ m *
          ((t ^ (κ - 1) : ℝ) : ℂ) ^ 2)) * u ^ (m + 2) := by
      push_cast
      field_simp
      ring
    rw [e1, hidC, hpkC, hu]
    ring

/-- Along a trajectory inside a zero chart, `w = ζ ∘ γ` satisfies `w' = ζ'(γ) γ'`,
`((m+2)/2)² w^m w'² = -1`, and `w ≠ 0`. -/
theorem fx_p3_ZeroChart.along {φ ζ : ℂ → ℂ} {q : ℂ} {m : ℕ} {r ρ0 : ℝ}
    (hZ : fx_p3_ZeroChart φ ζ q m r ρ0) (hm : 0 < m) {γ : ℝ → ℂ} {I : Set ℝ} (hI : IsOpen I)
    (hγ : fx_p3_VT φ γ I) (hγB : ∀ t ∈ I, γ t ∈ ball q r) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun t => ζ (γ t)) (deriv ζ (γ t) * deriv γ t) t ∧
      ((m + 2 : ℂ) / 2) ^ 2 * ζ (γ t) ^ m * (deriv ζ (γ t) * deriv γ t) ^ 2 = -1 ∧
      ζ (γ t) ≠ 0 := by
  obtain ⟨hr, -, -, hζ0, hinj, han, -⟩ := hZ
  have hcb : γ t ∈ closedBall q r := ball_subset_closedBall (hγB t ht)
  obtain ⟨h1, -, h3⟩ := han _ hcb
  refine ⟨h1.differentiableAt.hasDerivAt.comp t (hγ.hasDerivAt hI ht), ?_, ?_⟩
  · have e := (hγ.2 t ht).2.2
    rw [h3] at e
    linear_combination e
  · intro e
    have hq : γ t = q := hinj hcb (mem_closedBall_self hr.le) (by rw [e, hζ0])
    have := (hγ.2 t ht).2.1
    rw [h3, e, zero_pow hm.ne'] at this
    simp at this

/-- **The first integral at a zero.**  For a trajectory inside a zero chart, with
`F = (ζ ∘ γ)^(m+2)`, the quantity `|F| + Re F` is constant (it is `2 (Re √F)²`, and `Re √F` is the
horizontal natural coordinate, constant along vertical trajectories). -/
theorem fx_p3_ZeroChart.invariant {φ ζ : ℂ → ℂ} {q : ℂ} {m : ℕ} {r ρ0 : ℝ}
    (hZ : fx_p3_ZeroChart φ ζ q m r ρ0) (hm : 0 < m) {γ : ℝ → ℂ} {I : Set ℝ} (hI : fx_p3_IsOI I)
    (hγ : fx_p3_VT φ γ I) (hγB : ∀ t ∈ I, γ t ∈ ball q r) :
    ∃ c : ℝ, ∀ t ∈ I, ‖ζ (γ t) ^ (m + 2)‖ + (ζ (γ t) ^ (m + 2)).re = c := by
  set F : ℝ → ℂ := fun t => ζ (γ t) ^ (m + 2) with hF
  set H : ℝ → ℝ := fun t => √((F t).re ^ 2 + (F t).im ^ 2) + (F t).re with hH
  have hHd : ∀ t ∈ I, HasDerivAt H 0 t := by
    intro t ht
    obtain ⟨hw, he, hw0⟩ := hZ.along hm hI.1 hγ hγB ht
    set w := ζ (γ t) with hwdef
    set w' := deriv ζ (γ t) * deriv γ t with hw'def
    have hFd : HasDerivAt F (((m + 2 : ℕ) : ℂ) * w ^ (m + 1) * w') t := by
      have h1 := (hasDerivAt_pow (m + 2) w).comp t hw
      have e : m + 2 - 1 = m + 1 := by omega
      rw [e] at h1
      exact h1
    set F' := ((m + 2 : ℕ) : ℂ) * w ^ (m + 1) * w' with hF'
    have hsq : F' ^ 2 = ((-4 : ℝ) : ℂ) * F t := by
      simp only [hF', hF]
      push_cast
      linear_combination (4 * w ^ (m + 2)) * he
    have hre : HasDerivAt (fun t => (F t).re) F'.re t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hFd
    have him : HasDerivAt (fun t => (F t).im) F'.im t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hFd
    have hFne : F t ≠ 0 := pow_ne_zero _ hw0
    have hS : (F t).re ^ 2 + (F t).im ^ 2 ≠ 0 := by
      intro h
      apply hFne
      have hX : (F t).re = 0 := by nlinarith [sq_nonneg (F t).re, sq_nonneg (F t).im]
      have hY : (F t).im = 0 := by nlinarith [sq_nonneg (F t).re, sq_nonneg (F t).im]
      exact Complex.ext hX hY
    have hre2 : F'.re ^ 2 - F'.im ^ 2 = -4 * (F t).re := by
      have := congr_arg Complex.re hsq
      rw [Complex.re_ofReal_mul, sq, Complex.mul_re] at this
      linarith
    have him2 : 2 * F'.re * F'.im = -4 * (F t).im := by
      have := congr_arg Complex.im hsq
      rw [Complex.im_ofReal_mul, sq, Complex.mul_im] at this
      linarith
    have hAB : F'.re ^ 2 + F'.im ^ 2 ≠ 0 := by
      intro h
      have hA : F'.re = 0 := by nlinarith [sq_nonneg F'.re, sq_nonneg F'.im]
      have hB : F'.im = 0 := by nlinarith [sq_nonneg F'.re, sq_nonneg F'.im]
      apply hS
      have hX : (F t).re = 0 := by rw [hA, hB] at hre2; linarith
      have hY : (F t).im = 0 := by rw [hA, hB] at him2; linarith
      rw [hX, hY]; ring
    have hX : (F t).re = -(F'.re ^ 2 - F'.im ^ 2) / 4 := by linarith
    have hY : (F t).im = -(F'.re * F'.im) / 2 := by linarith
    have hsqrt : √((F t).re ^ 2 + (F t).im ^ 2) = (F'.re ^ 2 + F'.im ^ 2) / 4 := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), hX, hY]
      ring
    have hd1 : HasDerivAt (fun t => (F t).re ^ 2 + (F t).im ^ 2)
        (2 * (F t).re * F'.re + 2 * (F t).im * F'.im) t := by
      have := (hre.pow 2).add (him.pow 2)
      convert this using 1
      push_cast
      ring
    have hd2 := (hd1.sqrt hS).add hre
    convert hd2 using 1
    rw [hsqrt, hX, hY]
    field_simp
    ring
  obtain ⟨c, hc⟩ := hI.1.exists_is_const_of_deriv_eq_zero hI.isPreconnected
    (fun t ht => (hHd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hHd t ht).deriv)
  refine ⟨c, fun t ht => ?_⟩
  rw [← hc t ht, Complex.norm_eq_sqrt_sq_add_sq]

/-- **Darboux sign lemma**: if `G' = D ∈ {1, -1}` on an open interval, then `D` is constant. -/
theorem fx_p3_darboux_sign {G D : ℝ → ℝ} {I : Set ℝ} (hI : fx_p3_IsOI I)
    (hG : ∀ t ∈ I, HasDerivAt G (D t) t) (hD : ∀ t ∈ I, D t = 1 ∨ D t = -1) :
    ∀ t ∈ I, ∀ t' ∈ I, D t = D t' := by
  have key : ∀ t ∈ I, ∀ t' ∈ I, t < t' → D t = D t' := by
    intro t ht t' ht' hlt
    have hsub : Icc t t' ⊆ I := hI.2.out ht ht'
    have hf : ∀ x ∈ Icc t t', HasDerivWithinAt G (D x) (Icc t t') x := fun x hx =>
      (hG x (hsub hx)).hasDerivWithinAt
    by_contra hne
    rcases hD t ht with h1 | h1 <;> rcases hD t' ht' with h2 | h2
    · exact hne (h1.trans h2.symm)
    · obtain ⟨c, hc, hc0⟩ := exists_hasDerivWithinAt_eq_of_lt_of_gt hlt.le hf
        (m := 0) (by rw [h1]; norm_num) (by rw [h2]; norm_num)
      rcases hD c (hsub (Ioo_subset_Icc_self hc)) with h | h <;> rw [h] at hc0 <;> norm_num at hc0
    · obtain ⟨c, hc, hc0⟩ := exists_hasDerivWithinAt_eq_of_gt_of_lt hlt.le hf
        (m := 0) (by rw [h1]; norm_num) (by rw [h2]; norm_num)
      rcases hD c (hsub (Ioo_subset_Icc_self hc)) with h | h <;> rw [h] at hc0 <;> norm_num at hc0
    · exact hne (h1.trans h2.symm)
  intro t ht t' ht'
  rcases lt_trichotomy t t' with h | rfl | h
  · exact key t ht t' ht' h
  · rfl
  · exact (key t' ht' t ht h).symm

/-- **Trajectories on a critical ray.**  If the first integral vanishes along a trajectory inside a
zero chart, the trajectory runs along one critical ray: `ζ(γ t) = (C + σ t)^κ u` with `σ = ±1`,
`u^(m+2) = -1`, `C + σ t > 0`. -/
theorem fx_p3_ZeroChart.ray_form {φ ζ : ℂ → ℂ} {q : ℂ} {m : ℕ} {r ρ0 : ℝ}
    (hZ : fx_p3_ZeroChart φ ζ q m r ρ0) (hm : 0 < m) {γ : ℝ → ℂ} {I : Set ℝ} (hI : fx_p3_IsOI I)
    (hγ : fx_p3_VT φ γ I) (hγB : ∀ t ∈ I, γ t ∈ ball q r) (hIne : I.Nonempty)
    (hH : ∀ t ∈ I, ‖ζ (γ t) ^ (m + 2)‖ + (ζ (γ t) ^ (m + 2)).re = 0) :
    ∃ u : ℂ, u ^ (m + 2) = -1 ∧ ∃ σ C : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ t ∈ I, 0 < C + σ * t ∧
        ζ (γ t) = (((C + σ * t) ^ (2 / ((m : ℝ) + 2)) : ℝ) : ℂ) * u := by
  set F : ℝ → ℂ := fun t => ζ (γ t) ^ (m + 2) with hF
  -- pointwise facts
  have hpt : ∀ t ∈ I, (F t).im = 0 ∧ (F t).re < 0 ∧ ‖F t‖ = -(F t).re := by
    intro t ht
    obtain ⟨-, -, hw0⟩ := hZ.along hm hI.1 hγ hγB ht
    have hFne : F t ≠ 0 := pow_ne_zero _ hw0
    have h1 : ‖F t‖ = -(F t).re := by linarith [hH t ht]
    have h2 : ‖F t‖ ^ 2 = (F t).re ^ 2 + (F t).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hY : (F t).im = 0 := by
      rw [h1] at h2
      nlinarith [sq_nonneg (F t).im]
    refine ⟨hY, ?_, h1⟩
    have hpos : 0 < ‖F t‖ := norm_pos_iff.2 hFne
    linarith
  set G : ℝ → ℝ := fun t => √(-(F t).re) with hG
  have hGpos : ∀ t ∈ I, 0 < G t := fun t ht => Real.sqrt_pos.2 (by linarith [(hpt t ht).2.1])
  -- the derivative of `G`
  have hderiv : ∀ t ∈ I, ∃ D : ℝ, HasDerivAt G D t ∧ (D = 1 ∨ D = -1) := by
    intro t ht
    obtain ⟨hw, he, hw0⟩ := hZ.along hm hI.1 hγ hγB ht
    set w := ζ (γ t) with hwdef
    set w' := deriv ζ (γ t) * deriv γ t with hw'def
    have hFd : HasDerivAt F (((m + 2 : ℕ) : ℂ) * w ^ (m + 1) * w') t := by
      have h1 := (hasDerivAt_pow (m + 2) w).comp t hw
      have e : m + 2 - 1 = m + 1 := by omega
      rw [e] at h1
      exact h1
    set F' := ((m + 2 : ℕ) : ℂ) * w ^ (m + 1) * w' with hF'
    have hsq : F' ^ 2 = ((-4 : ℝ) : ℂ) * F t := by
      simp only [hF', hF]
      push_cast
      linear_combination (4 * w ^ (m + 2)) * he
    have hre : HasDerivAt (fun t => (F t).re) F'.re t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hFd
    have him : HasDerivAt (fun t => (F t).im) F'.im t :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hFd
    have hB : F'.im = 0 := by
      have h0 : HasDerivAt (fun t => (F t).im) 0 t := by
        refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
        filter_upwards [hI.1.mem_nhds ht] with s hs
        exact (hpt s hs).1
      exact him.unique h0
    have hA2 : F'.re ^ 2 = -4 * (F t).re := by
      have := congr_arg Complex.re hsq
      rw [Complex.re_ofReal_mul, sq, Complex.mul_re, hB] at this
      linarith
    have hXne : -(F t).re ≠ 0 := by linarith [(hpt t ht).2.1]
    have hGd := hre.neg.sqrt hXne
    refine ⟨-F'.re / (2 * √(-(F t).re)), hGd, ?_⟩
    have hG2 : √(-(F t).re) ^ 2 = -(F t).re := Real.sq_sqrt (by linarith [(hpt t ht).2.1])
    have hGp : 0 < √(-(F t).re) := hGpos t ht
    have hX0 : (F t).re ≠ 0 := by linarith [(hpt t ht).2.1]
    have hsq1 : (-F'.re / (2 * √(-(F t).re))) ^ 2 = 1 := by
      rw [div_pow, mul_pow, hG2, neg_sq, hA2]
      field_simp
      norm_num
    have h2 : (-F'.re / (2 * √(-(F t).re)) - 1) * (-F'.re / (2 * √(-(F t).re)) + 1) = 0 := by
      linear_combination hsq1
    rcases mul_eq_zero.1 h2 with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  choose! D hD hD1 using hderiv
  obtain ⟨t₀, ht₀⟩ := hIne
  have hconst := fx_p3_darboux_sign hI hD hD1
  set σ := D t₀ with hσ
  have hG' : ∃ C, ∀ t ∈ I, G t - σ * t = C := by
    have hd : ∀ t ∈ I, HasDerivAt (fun t => G t - σ * t) 0 t := by
      intro t ht
      refine ((hD t ht).sub ((hasDerivAt_id t).const_mul σ)).congr_deriv ?_
      rw [hconst t ht t₀ ht₀, hσ]
      ring
    exact hI.1.exists_is_const_of_deriv_eq_zero hI.isPreconnected
      (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt) (fun t ht => (hd t ht).deriv)
  obtain ⟨C, hC⟩ := hG'
  -- the direction
  set U : ℝ → ℂ := fun t => ζ (γ t) / (‖ζ (γ t)‖ : ℂ) with hU
  have hUmaps : MapsTo U I {u : ℂ | u ^ (m + 2) = -1} := by
    intro t ht
    obtain ⟨-, -, hw0⟩ := hZ.along hm hI.1 hγ hγB ht
    obtain ⟨hY, -, hN⟩ := hpt t ht
    show (ζ (γ t) / (‖ζ (γ t)‖ : ℂ)) ^ (m + 2) = -1
    have hn : (‖ζ (γ t)‖ : ℂ) ^ (m + 2) = (‖F t‖ : ℂ) := by
      simp only [hF, norm_pow]; push_cast; ring
    have hFeq : F t = -((‖F t‖ : ℝ) : ℂ) := Complex.ext (by simp [hN]) (by simp [hY])
    have hnc : (‖F t‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_pos_iff.2 (pow_ne_zero (m + 2) hw0)).ne'
    rw [div_pow, hn]
    have e : ζ (γ t) ^ (m + 2) = F t := rfl
    rw [e]
    generalize hNdef : ‖F t‖ = N at hFeq hnc ⊢
    rw [hFeq]
    field_simp
  have hUc : ContinuousOn U I := by
    have hwc : ContinuousOn (fun t => ζ (γ t)) I := fun t ht =>
      (hZ.along hm hI.1 hγ hγB ht).1.continuousAt.continuousWithinAt
    refine hwc.div (Complex.continuous_ofReal.comp_continuousOn hwc.norm) fun t ht => ?_
    obtain ⟨-, -, hw0⟩ := hZ.along hm hI.1 hγ hγB ht
    exact_mod_cast (norm_pos_iff.2 hw0).ne'
  have hUconst : ∀ t ∈ I, U t = U t₀ := fun t ht =>
    hI.isPreconnected.constant_of_mapsTo (fx_p3_roots_finite m).isDiscrete hUc hUmaps ht ht₀
  refine ⟨U t₀, hUmaps ht₀, σ, C, hD1 t₀ ht₀, fun t ht => ⟨?_, ?_⟩⟩
  · have := hC t ht
    have := hGpos t ht
    linarith
  · obtain ⟨-, -, hw0⟩ := hZ.along hm hI.1 hγ hγB ht
    obtain ⟨hY, hX, hN⟩ := hpt t ht
    have hGt : G t = C + σ * t := by linarith [hC t ht]
    have hnorm : ‖ζ (γ t)‖ = (C + σ * t) ^ (2 / ((m : ℝ) + 2)) := by
      rw [← hGt]
      have h1 : ‖ζ (γ t)‖ ^ (m + 2) = G t ^ 2 := by
        rw [hG, Real.sq_sqrt (by linarith), ← hN, hF]
        simp [norm_pow]
      have h2 : ‖ζ (γ t)‖ = (‖ζ (γ t)‖ ^ (m + 2)) ^ (((m + 2 : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (norm_nonneg _) (by omega)).symm
      rw [h2, h1, ← Real.rpow_natCast, ← Real.rpow_mul (hGpos t ht).le]
      congr 1
      push_cast
      ring
    rw [← hUconst t ht, hU]
    simp only
    rw [← hnorm]
    have hnc : (‖ζ (γ t)‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hw0).ne'
    field_simp

/-- **Maximal extension** of a trajectory germ `M` on `(0, t₀)`: a trajectory `Γ` agreeing with `M`,
defined either on a maximal bounded interval `(0, L)` (no trajectory agreeing with `M` near `0`
lives longer), or on `(0, ∞)`. -/
theorem fx_p3_maxTraj {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {M : ℝ → ℂ} {t₀ : ℝ}
    (ht₀ : 0 < t₀) (hM : fx_p3_VT φ M (Ioo 0 t₀)) :
    ∃ Γ : ℝ → ℂ, EqOn Γ M (Ioo 0 t₀) ∧
      ((∃ L, t₀ ≤ L ∧ fx_p3_VT φ Γ (Ioo 0 L) ∧
          ∀ (γ : ℝ → ℂ) (T ε : ℝ), 0 < ε → fx_p3_VT φ γ (Ioo 0 T) → EqOn γ M (Ioo 0 ε) → T ≤ L) ∨
        fx_p3_VT φ Γ (Ioi 0)) := by
  classical
  set W : Set ℝ := {T | 0 < T ∧ ∃ (γ : ℝ → ℂ) (ε : ℝ), 0 < ε ∧ fx_p3_VT φ γ (Ioo 0 T) ∧
    EqOn γ M (Ioo 0 ε)} with hW
  -- any two witnesses agree
  have agree : ∀ (γ₁ γ₂ : ℝ → ℂ) (T₁ T₂ ε₁ ε₂ : ℝ), 0 < ε₁ → 0 < ε₂ → 0 < T₁ → 0 < T₂ →
      fx_p3_VT φ γ₁ (Ioo 0 T₁) → fx_p3_VT φ γ₂ (Ioo 0 T₂) → EqOn γ₁ M (Ioo 0 ε₁) →
      EqOn γ₂ M (Ioo 0 ε₂) → EqOn γ₁ γ₂ (Ioo 0 (min T₁ T₂)) := by
    intro γ₁ γ₂ T₁ T₂ ε₁ ε₂ hε₁ hε₂ hT₁ hT₂ h₁ h₂ hM₁ hM₂
    set e := min (min ε₁ ε₂) (min T₁ T₂) with he
    have he0 : 0 < e := lt_min (lt_min hε₁ hε₂) (lt_min hT₁ hT₂)
    have h := h₁.eqOn_of_eqOn hφ (fx_p3_isOI_Ioo 0 T₁) (fx_p3_isOI_Ioo 0 T₂) h₂ (J := Ioo 0 e)
      isOpen_Ioo ⟨e / 2, by positivity, by linarith⟩
      (Ioo_subset_Ioo_right ((min_le_right _ _).trans (min_le_left _ _)))
      (Ioo_subset_Ioo_right ((min_le_right _ _).trans (min_le_right _ _)))
      (fun t ht => by
        rw [hM₁ ⟨ht.1, lt_of_lt_of_le ht.2 ((min_le_left _ _).trans (min_le_left _ _))⟩,
          hM₂ ⟨ht.1, lt_of_lt_of_le ht.2 ((min_le_left _ _).trans (min_le_right _ _))⟩])
    intro t ht
    exact h ⟨⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩,
      ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩⟩
  have ht₀W : t₀ ∈ W := ⟨ht₀, M, t₀, ht₀, hM, fun _ _ => rfl⟩
  have hWex : ∀ T ∈ W, ∃ (γ : ℝ → ℂ) (ε : ℝ), 0 < ε ∧ fx_p3_VT φ γ (Ioo 0 T) ∧
      EqOn γ M (Ioo 0 ε) := fun T hT => hT.2
  choose! γW εW hεW hγW hγWM using hWex
  set Γ : ℝ → ℂ := fun t => if h : ∃ T ∈ W, t < T then γW (Classical.choose h) t else 0
    with hΓdef
  have hΓW : ∀ T ∈ W, EqOn Γ (γW T) (Ioo 0 T) := by
    intro T hT t ht
    have h : ∃ T ∈ W, t < T := ⟨T, hT, ht.2⟩
    have hΓt : Γ t = γW (Classical.choose h) t := by simp only [hΓdef, dite_eq_left h]
    obtain ⟨hT', htT'⟩ := Classical.choose_spec h
    rw [hΓt]
    exact agree _ _ _ _ _ _ (hεW _ hT') (hεW _ hT) hT'.1 hT.1 (hγW _ hT') (hγW _ hT)
      (hγWM _ hT') (hγWM _ hT) ⟨ht.1, lt_min htT' ht.2⟩
  have hΓloc : ∀ t, (∃ T ∈ W, t ∈ Ioo 0 T) →
      ∃ (γ' : ℝ → ℂ) (J : Set ℝ), IsOpen J ∧ t ∈ J ∧ fx_p3_VT φ γ' J ∧ EqOn Γ γ' J := by
    rintro t ⟨T, hT, ht⟩
    exact ⟨γW T, Ioo 0 T, isOpen_Ioo, ht, hγW T hT, hΓW T hT⟩
  have hΓM : EqOn Γ M (Ioo 0 t₀) := by
    intro t ht
    rw [hΓW t₀ ht₀W ht]
    have := agree _ _ _ _ _ _ (hεW _ ht₀W) ht₀ ht₀ ht₀ (hγW _ ht₀W) hM (hγWM _ ht₀W)
      (fun _ _ => rfl) (by rwa [min_self])
    exact this
  refine ⟨Γ, hΓM, ?_⟩
  by_cases hbdd : BddAbove W
  · left
    have hWne : W.Nonempty := ⟨t₀, ht₀W⟩
    refine ⟨sSup W, le_csSup hbdd ht₀W, ?_, ?_⟩
    · refine fx_p3_VT.of_local fun t ht => hΓloc t ?_
      obtain ⟨T, hT, htT⟩ := exists_lt_of_lt_csSup hWne ht.2
      exact ⟨T, hT, ht.1, htT⟩
    · intro γ T ε hε hγ hγM
      by_cases hT : T ≤ 0
      · exact hT.trans (ht₀.le.trans (le_csSup hbdd ht₀W))
      · exact le_csSup hbdd ⟨not_le.1 hT, γ, ε, hε, hγ, hγM⟩
  · right
    refine fx_p3_VT.of_local fun t ht => hΓloc t ?_
    rw [not_bddAbove_iff] at hbdd
    obtain ⟨T, hT, htT⟩ := hbdd t
    exact ⟨T, hT, ht, htT⟩

/-- **No regular limit point at a finite end.**  A maximal trajectory on `(0, L)` cannot accumulate
at a regular point of `Δ` as `t → L⁻`: the chart line through a nearby point would extend it. -/
theorem fx_p3_maxTraj_no_regular_cluster {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    {M Γ : ℝ → ℂ} {t₀ L : ℝ} (ht₀ : 0 < t₀) (hΓM : EqOn Γ M (Ioo 0 t₀)) (hL : t₀ ≤ L)
    (hΓ : fx_p3_VT φ Γ (Ioo 0 L))
    (hmax : ∀ (γ : ℝ → ℂ) (T ε : ℝ), 0 < ε → fx_p3_VT φ γ (Ioo 0 T) → EqOn γ M (Ioo 0 ε) → T ≤ L)
    {p : ℂ} (hp : p ∈ unitDisc) (hp0 : φ p ≠ 0) : ¬ MapClusterPt p (𝓝[<] L) Γ := by
  intro hcl
  obtain ⟨ζ, r, ρ0, hR, -⟩ := fx_p3_regChart_exists hφ hp hp0 one_pos
  have hr := hR.1
  have hρ0 := hR.2.1
  have hζ0 := hR.2.2.2.1
  have han := hR.2.2.2.2.2.1
  have hρB := hR.2.2.2.2.2.2
  have hζc : ContinuousAt ζ p := (han p (mem_closedBall_self hr.le)).1.continuousAt
  obtain ⟨r₁, hr₁, hr₁ζ⟩ : ∃ r₁ > 0, ∀ z, dist z p < r₁ → ‖ζ z‖ < ρ0 / 4 := by
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hζc (ρ0 / 4) (by positivity)
    exact ⟨δ, hδ, fun z hz => by simpa [hζ0] using hδ' hz⟩
  have hfreq : ∃ᶠ t in 𝓝[<] L, Γ t ∈ ball p (min r r₁) :=
    (mapClusterPt_iff_frequently.1 hcl) _ (ball_mem_nhds p (lt_min hr hr₁))
  have hL0 : 0 < L := ht₀.trans_le hL
  have hev : ∀ᶠ t in 𝓝[<] L, t ∈ Ioo (max 0 (L - ρ0 / 4)) L :=
    Ioo_mem_nhdsLT (max_lt hL0 (by linarith))
  obtain ⟨t, htB, htI⟩ := (hfreq.and_eventually hev).exists
  have htI' : t ∈ Ioo 0 L := ⟨lt_of_le_of_lt (le_max_left _ _) htI.1, htI.2⟩
  have hLt : L - t < ρ0 / 4 := by linarith [le_max_right 0 (L - ρ0 / 4), htI.1]
  have htBr : Γ t ∈ ball p r := ball_subset_ball (min_le_left _ _) htB
  have hwt : ‖ζ (Γ t)‖ < ρ0 / 4 := hr₁ζ _ (lt_of_lt_of_le htB (min_le_right _ _))
  obtain ⟨he2, hloc⟩ := hR.local_form hφ (fx_p3_isOI_Ioo 0 L) hΓ htI' htBr
  set e := deriv ζ (Γ t) * deriv Γ t with he
  set w := ζ (Γ t) with hw
  set ψ := Function.invFunOn ζ (ball p r) with hψ
  have hen : ‖e‖ = 1 := by
    have h := congr_arg norm he2
    rw [norm_pow, norm_neg, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg e) two_ne_zero).1 h
  have hβ : fx_p3_VT φ (fun s : ℝ => ψ ((w - (t : ℂ) * e) + (s : ℂ) * e))
      (Ioo (t - ρ0 / 2) (t + ρ0 / 2)) := by
    refine hR.vseg he2 fun s hs => hρB ?_
    rw [mem_ball_zero_iff]
    have e1 : (w - (t : ℂ) * e) + (s : ℂ) * e = w + ((s - t : ℝ) : ℂ) * e := by push_cast; ring
    rw [e1]
    calc ‖w + ((s - t : ℝ) : ℂ) * e‖ ≤ ‖w‖ + ‖((s - t : ℝ) : ℂ) * e‖ := norm_add_le _ _
      _ = ‖w‖ + |s - t| := by rw [norm_mul, hen, mul_one, Complex.norm_real, Real.norm_eq_abs]
      _ < ρ0 / 4 + ρ0 / 2 := by
          have : |s - t| < ρ0 / 2 := abs_lt.2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
          linarith
      _ < ρ0 := by linarith
  set γ' : ℝ → ℂ := fun s => if s < t then Γ s else ψ (w + ((s - t : ℝ) : ℂ) * e) with hγ'
  have hγ'V : fx_p3_VT φ γ' (Ioo 0 (t + ρ0 / 2)) := by
    refine fx_p3_VT.of_local fun s hs => ?_
    by_cases hsL : s < L
    · refine ⟨Γ, Ioo 0 L, isOpen_Ioo, ⟨hs.1, hsL⟩, hΓ, fun s' hs' => ?_⟩
      by_cases h : s' < t
      · simp only [hγ', ite_eq_left h]
      · simp only [hγ', ite_eq_right h]
        have h1 := hloc (s' - t) (by rw [add_sub_cancel]; exact hs')
          (by
            rw [abs_of_nonneg (by linarith [not_lt.1 h])]
            linarith [hs'.2])
        rw [add_sub_cancel] at h1
        exact h1.symm
    · refine ⟨_, Ioo t (t + ρ0 / 2), isOpen_Ioo, ⟨by linarith [htI'.2], hs.2⟩,
        hβ.mono (Ioo_subset_Ioo_left (by linarith)), fun s' hs' => ?_⟩
      simp only [hγ', ite_eq_right (not_lt.2 hs'.1.le)]
      congr 1
      push_cast
      ring
  have hγ'M : EqOn γ' M (Ioo 0 (min t₀ t)) := by
    intro s hs
    have hst : s < t := lt_of_lt_of_le hs.2 (min_le_right _ _)
    simp only [hγ', ite_eq_left hst]
    exact hΓM ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
  have := hmax γ' (t + ρ0 / 2) (min t₀ t) (lt_min ht₀ htI'.1) hγ'V hγ'M
  linarith

/-- **Accumulation at a zero forces convergence.**  Along a tail filter `l` of an open interval `I`
(basis of tails `{t ∈ I | t > t₀}`), a continuous path in `Δ` with no regular cluster points, which
does not leave every compact subset of `Δ`, converges to a zero of `φ` (else it would cross a small
circle around the zero infinitely often, producing a regular cluster point). -/
theorem fx_p3_tail_to_zero {φ : ℂ → ℂ} {Γ : ℝ → ℂ} {I : Set ℝ} (hI : fx_p3_IsOI I)
    (hΓc : ContinuousOn Γ I) {l : Filter ℝ} (hlI : ∀ᶠ t in l, t ∈ I)
    (hbasis : ∀ U ∈ l, ∃ t₀ ∈ I, ∀ t ∈ I, t₀ < t → t ∈ U)
    (hlgt : ∀ t₀ ∈ I, ∀ᶠ t in l, t₀ < t)
    (hreg : ∀ p ∈ unitDisc, φ p ≠ 0 → ¬ MapClusterPt p l Γ)
    (hiso : ∀ q ∈ unitDisc, φ q = 0 → ∃ ε > 0, closedBall q ε ⊆ unitDisc ∧
      ∀ z ∈ closedBall q ε, z ≠ q → φ z ≠ 0)
    (hK : ¬ ∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc → ∀ᶠ t in l, Γ t ∉ K) :
    ∃ q ∈ unitDisc, φ q = 0 ∧ Tendsto Γ l (𝓝 q) := by
  push Not at hK
  obtain ⟨K, hKc, hKD, hKf⟩ := hK
  obtain ⟨q, hqK, hqcl⟩ := hKc.exists_mapClusterPt_of_frequently hKf
  have hqD := hKD hqK
  have hq0 : φ q = 0 := by
    by_contra h
    exact hreg q hqD h hqcl
  refine ⟨q, hqD, hq0, ?_⟩
  by_contra hnt
  obtain ⟨ε, hε, hεD, hεz⟩ := hiso q hqD hq0
  rw [Metric.tendsto_nhds] at hnt
  push Not at hnt
  obtain ⟨ε₀, hε₀, hfar₀⟩ := hnt
  set ε₁ := min ε₀ ε with hε₁
  have hε₁0 : 0 < ε₁ := lt_min hε₀ hε
  have hfar : ∃ᶠ t in l, ε₁ ≤ dist (Γ t) q :=
    hfar₀.mono fun t ht => (min_le_left _ _).trans ht
  have hnear : ∃ᶠ t in l, Γ t ∈ ball q (ε₁ / 2) :=
    (mapClusterPt_iff_frequently.1 hqcl) _ (ball_mem_nhds q (by positivity))
  have hsph : ∃ᶠ t in l, Γ t ∈ sphere q (3 * ε₁ / 4) := by
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨t₀, ht₀I, ht₀U⟩ := hbasis U hU
    obtain ⟨ta, hta, htaI, htat₀⟩ := (hnear.and_eventually (hlI.and (hlgt t₀ ht₀I))).exists
    obtain ⟨tb, htb, htbI, htbta⟩ := (hfar.and_eventually (hlI.and (hlgt ta htaI))).exists
    have hsub : Icc ta tb ⊆ I := hI.2.out htaI htbI
    have hf : ContinuousOn (fun t => dist (Γ t) q) (Icc ta tb) :=
      continuous_dist.comp_continuousOn ((hΓc.mono hsub).prodMk continuousOn_const)
    have hmem : 3 * ε₁ / 4 ∈ Icc (dist (Γ ta) q) (dist (Γ tb) q) := by
      rw [mem_ball] at hta
      constructor <;> linarith
    obtain ⟨tc, htc, htcv⟩ := intermediate_value_Icc htbta.le hf hmem
    refine ⟨tc, ht₀U tc (hsub htc) (lt_of_lt_of_le htat₀ htc.1), ?_⟩
    rw [mem_sphere]
    exact htcv
  obtain ⟨p, hpS, hpcl⟩ := (isCompact_sphere q (3 * ε₁ / 4)).exists_mapClusterPt_of_frequently hsph
  have hpq : dist p q = 3 * ε₁ / 4 := mem_sphere.1 hpS
  have hpB : p ∈ closedBall q ε := by
    rw [mem_closedBall, hpq]
    have : ε₁ ≤ ε := min_le_right _ _
    linarith
  have hpne : p ≠ q := by
    intro h
    rw [h, dist_self] at hpq
    linarith
  exact hreg p (hεD hpB) (hεz p hpB hpne) hpcl

/-- **Arrival at a zero.**  A trajectory converging (along a tail filter) to a zero `q` eventually
runs along a critical ray of the zero chart: `Γ t = ψ((C + σ t)^κ u)`, with `(C + σ t)² → 0`. -/
theorem fx_p3_ZeroChart.arrival {φ ζ : ℂ → ℂ} {q : ℂ} {m : ℕ} {r ρ0 : ℝ}
    (hZ : fx_p3_ZeroChart φ ζ q m r ρ0) (hm : 0 < m) {Γ : ℝ → ℂ} {I : Set ℝ} (hI : fx_p3_IsOI I)
    (hΓ : fx_p3_VT φ Γ I) {l : Filter ℝ} [l.NeBot] (hlI : ∀ᶠ t in l, t ∈ I)
    (hbasis : ∀ U ∈ l, ∃ t₀ ∈ I, ∀ t ∈ I, t₀ < t → t ∈ U)
    (hlgt : ∀ t₀ ∈ I, ∀ᶠ t in l, t₀ < t) (hT : Tendsto Γ l (𝓝 q)) :
    ∃ u : ℂ, u ^ (m + 2) = -1 ∧ ∃ σ C t₁ : ℝ, (σ = 1 ∨ σ = -1) ∧ t₁ ∈ I ∧
      (∀ t ∈ I, t₁ < t → 0 < C + σ * t ∧
        Γ t = Function.invFunOn ζ (ball q r)
          ((((C + σ * t) ^ (2 / ((m : ℝ) + 2)) : ℝ) : ℂ) * u)) ∧
      Tendsto (fun t => (C + σ * t) ^ 2) l (𝓝 0) := by
  obtain ⟨-, hleft, -⟩ := hZ.inv
  have hr := hZ.1
  have hζ0 := hZ.2.2.2.1
  have han := hZ.2.2.2.2.2.1
  have hball : ∀ᶠ t in l, Γ t ∈ ball q r := hT (ball_mem_nhds q hr)
  obtain ⟨t₁, ht₁I, ht₁⟩ := hbasis _ hball
  set I' := I ∩ Ioi t₁ with hI'
  have hI'OI : fx_p3_IsOI I' := hI.inter (fx_p3_isOI_Ioi t₁)
  have hlI' : ∀ᶠ t in l, t ∈ I' := (hlI.and (hlgt t₁ ht₁I)).mono fun t ht => ⟨ht.1, ht.2⟩
  have hI'ne : I'.Nonempty := hlI'.exists
  have hΓ' : fx_p3_VT φ Γ I' := hΓ.mono inter_subset_left
  have hB' : ∀ t ∈ I', Γ t ∈ ball q r := fun t ht => ht₁ t ht.1 ht.2
  obtain ⟨c, hc⟩ := hZ.invariant hm hI'OI hΓ' hB'
  -- the first integral tends to `0`
  have hζc : ContinuousAt ζ q := (han q (mem_closedBall_self hr.le)).1.continuousAt
  have hw : Tendsto (fun t => ζ (Γ t)) l (𝓝 0) := by
    have := hζc.tendsto.comp hT
    rwa [hζ0] at this
  have hg : Continuous (fun w : ℂ => ‖w ^ (m + 2)‖ + (w ^ (m + 2)).re) := by fun_prop
  have hH0 : Tendsto (fun t => ‖ζ (Γ t) ^ (m + 2)‖ + (ζ (Γ t) ^ (m + 2)).re) l (𝓝 0) := by
    have h0 : ‖(0 : ℂ) ^ (m + 2)‖ + ((0 : ℂ) ^ (m + 2)).re = 0 := by
      rw [zero_pow (by omega : m + 2 ≠ 0)]; simp
    have := (hg.tendsto 0).comp hw
    rw [h0] at this
    exact this
  have hHc : Tendsto (fun t => ‖ζ (Γ t) ^ (m + 2)‖ + (ζ (Γ t) ^ (m + 2)).re) l (𝓝 c) :=
    tendsto_const_nhds.congr' (hlI'.mono fun t ht => (hc t ht).symm)
  have hc0 : c = 0 := tendsto_nhds_unique hHc hH0
  obtain ⟨u, hu, σ, C, hσ, hform⟩ := hZ.ray_form hm hI'OI hΓ' hB' hI'ne
    (fun t ht => (hc t ht).trans hc0)
  refine ⟨u, hu, σ, C, t₁, hσ, ht₁I, fun t ht ht' => ⟨(hform t ⟨ht, ht'⟩).1, ?_⟩, ?_⟩
  · rw [← (hform t ⟨ht, ht'⟩).2]
    exact (hleft _ (hB' t ⟨ht, ht'⟩)).symm
  · have hn : Tendsto (fun t => ‖ζ (Γ t)‖ ^ (m + 2)) l (𝓝 0) := by
      have := (continuous_norm.tendsto (0 : ℂ)).comp hw
      have h2 := this.pow (m + 2)
      simpa [zero_pow (by omega : m + 2 ≠ 0)] using h2
    refine hn.congr' (hlI'.mono fun t ht => ?_)
    obtain ⟨hpos, heq⟩ := hform t ht
    have hun := fx_p3_root_norm hu
    rw [heq, norm_mul, hun, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hpos.le _), ← Real.rpow_mul_natCast hpos.le]
    have : 2 / ((m : ℝ) + 2) * ((m + 2 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) := by
      push_cast
      exact fx_p3_kappa_mul m
    rw [this, Real.rpow_natCast]

/-- On `(0, ∞)`, a trajectory cannot converge to a zero (the arrival parameter `C + σ t` would tend
to `0` while `t → ∞`). -/
theorem fx_p3_ZeroChart.no_arrival_Ioi {φ ζ : ℂ → ℂ} {q : ℂ} {m : ℕ} {r ρ0 : ℝ}
    (hZ : fx_p3_ZeroChart φ ζ q m r ρ0) (hm : 0 < m) {Γ : ℝ → ℂ} (hΓ : fx_p3_VT φ Γ (Ioi 0))
    (hT : Tendsto Γ atTop (𝓝 q)) : False := by
  have hbasis : ∀ U ∈ (atTop : Filter ℝ), ∃ t₀ ∈ Ioi (0 : ℝ), ∀ t ∈ Ioi (0 : ℝ), t₀ < t → t ∈ U := by
    intro U hU
    obtain ⟨a, ha⟩ := mem_atTop_sets.1 hU
    refine ⟨max a 1, mem_Ioi.2 (lt_of_lt_of_le one_pos (le_max_right _ _)), fun t _ ht => ha t ?_⟩
    exact (le_max_left _ _).trans ht.le
  obtain ⟨u, -, σ, C, t₁, hσ, -, -, hlim⟩ := hZ.arrival hm (fx_p3_isOI_Ioi 0) hΓ
    (eventually_gt_atTop 0) hbasis (fun t₀ _ => eventually_gt_atTop t₀) hT
  have h1 : ∀ᶠ t in atTop, (C + σ * t) ^ 2 < 1 := hlim.eventually (gt_mem_nhds one_pos)
  obtain ⟨t, ht1, ht2⟩ := (h1.and (eventually_gt_atTop (|C| + 1))).exists
  have hC := neg_abs_le C
  have hC' := le_abs_self C
  rcases hσ with rfl | rfl
  · nlinarith
  · nlinarith

/-- On `(0, L)`, a trajectory converging to a zero arrives along a critical ray with the exact
parametrization `Γ t = ψ((L - t)^κ u)` near `L`. -/
theorem fx_p3_ZeroChart.arrival_Ioo {φ ζ : ℂ → ℂ} {q : ℂ} {m : ℕ} {r ρ0 : ℝ}
    (hZ : fx_p3_ZeroChart φ ζ q m r ρ0) (hm : 0 < m) {Γ : ℝ → ℂ} {L : ℝ} (hL : 0 < L)
    (hΓ : fx_p3_VT φ Γ (Ioo 0 L)) (hT : Tendsto Γ (𝓝[<] L) (𝓝 q)) :
    ∃ u : ℂ, u ^ (m + 2) = -1 ∧ ∃ t₁ ∈ Ioo 0 L, ∀ t ∈ Ioo t₁ L,
      Γ t = Function.invFunOn ζ (ball q r) ((((L - t) ^ (2 / ((m : ℝ) + 2)) : ℝ) : ℂ) * u) := by
  have hbasis : ∀ U ∈ 𝓝[<] L, ∃ t₀ ∈ Ioo (0 : ℝ) L, ∀ t ∈ Ioo (0 : ℝ) L, t₀ < t → t ∈ U := by
    intro U hU
    obtain ⟨a, ha, haU⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' (show (0 : ℝ) < L from hL)).1 hU
    refine ⟨max a (L / 2), ⟨by positivity, max_lt ha (by linarith)⟩, fun t ht htt => haU ?_⟩
    exact ⟨lt_of_le_of_lt (le_max_left _ _) htt, ht.2⟩
  have hlI : ∀ᶠ t in 𝓝[<] L, t ∈ Ioo (0 : ℝ) L := Ioo_mem_nhdsLT hL
  have hlgt : ∀ t₀ ∈ Ioo (0 : ℝ) L, ∀ᶠ t in 𝓝[<] L, t₀ < t := fun t₀ ht₀ =>
    Filter.eventually_of_mem (Ioo_mem_nhdsLT ht₀.2) fun t ht => ht.1
  obtain ⟨u, hu, σ, C, t₁, hσ, ht₁, hform, hlim⟩ := hZ.arrival hm (fx_p3_isOI_Ioo 0 L) hΓ hlI
    hbasis hlgt hT
  have hcont : Tendsto (fun t => (C + σ * t) ^ 2) (𝓝[<] L) (𝓝 ((C + σ * L) ^ 2)) :=
    ((continuous_const.add (continuous_const.mul continuous_id)).pow 2).tendsto L
      |>.mono_left nhdsWithin_le_nhds
  have hCL : (C + σ * L) ^ 2 = 0 := tendsto_nhds_unique hcont hlim
  have hCL' : C + σ * L = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hCL
  have hmid : (t₁ + L) / 2 ∈ Ioo (0 : ℝ) L := ⟨by linarith [ht₁.1], by linarith [ht₁.2]⟩
  have hpos := (hform _ hmid (by linarith [ht₁.2])).1
  rcases hσ with rfl | rfl
  · exfalso
    nlinarith [ht₁.2]
  · refine ⟨u, hu, t₁, ht₁, fun t ht => ?_⟩
    have htI : t ∈ Ioo (0 : ℝ) L := ⟨by linarith [ht₁.1, ht.1], ht.2⟩
    rw [(hform t htI ht.1).2]
    congr 4
    linarith

/-- `e² = -1` forces `e = ±i`: `Re e = 0` and `(Im e)² = 1`. -/
theorem fx_p3_sq_eq_neg_one {e : ℂ} (he : e ^ 2 = -1) : e.re = 0 ∧ e.im ^ 2 = 1 := by
  have h1 := congr_arg Complex.re he
  have h2 := congr_arg Complex.im he
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.one_re, Complex.one_im] at h1 h2
  have hre : e.re = 0 := by
    rcases mul_eq_zero.1 (show e.re * e.im = 0 by linarith) with h | h
    · exact h
    · rw [h] at h1; nlinarith [sq_nonneg e.re]
  refine ⟨hre, ?_⟩
  rw [hre] at h1
  nlinarith

/-- A nonzero purely imaginary number has nonzero argument. -/
theorem fx_p3_arg_ne_zero_of_re_eq_zero {z : ℂ} (hre : z.re = 0) (hz : z ≠ 0) : arg z ≠ 0 := by
  intro h
  rw [Complex.arg_eq_zero_iff] at h
  exact hz (Complex.ext hre h.2)

/-- `derivWithin` on `[0, 1]` of a function differentiable at a point of `[0, 1]`. -/
theorem fx_p3_derivWithin_Icc {f : ℝ → ℂ} {f' : ℂ} {τ : ℝ} (hf : HasDerivAt f f' τ)
    (hτ : τ ∈ Icc (0 : ℝ) 1) : derivWithin f (Icc 0 1) τ = f' :=
  hf.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one τ hτ)

/-- A vertical piece `τ ↦ Γ(s₁ + τ (s₂ - s₁))` of a trajectory, as a chain side. -/
theorem fx_p3_VT.piece {φ : ℂ → ℂ} {Γ : ℝ → ℂ} {I : Set ℝ} (hI : fx_p3_IsOI I) (hΓ : fx_p3_VT φ Γ I)
    {s₁ s₂ : ℝ} (h12 : s₁ < s₂) (hs₁ : s₁ ∈ I) (hs₂ : s₂ ∈ I) :
    (∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt (fun τ => Γ (s₁ + τ * (s₂ - s₁)))
      (((s₂ - s₁ : ℝ) : ℂ) * deriv Γ (s₁ + τ * (s₂ - s₁))) τ) ∧
      IsPhiStraightArc φ (fun τ => Γ (s₁ + τ * (s₂ - s₁))) 0 1 ∧
      ContDiffOn ℝ 1 (fun τ => Γ (s₁ + τ * (s₂ - s₁))) (Icc 0 1) ∧
      (fun τ => Γ (s₁ + τ * (s₂ - s₁))) '' Icc 0 1 ⊆ unitDisc := by
  have hsub : Icc s₁ s₂ ⊆ I := hI.2.out hs₁ hs₂
  have hmem : ∀ τ ∈ Icc (0 : ℝ) 1, s₁ + τ * (s₂ - s₁) ∈ I := fun τ hτ =>
    hsub ⟨by nlinarith [hτ.1], by nlinarith [hτ.2]⟩
  have hd : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt (fun τ => Γ (s₁ + τ * (s₂ - s₁)))
      (((s₂ - s₁ : ℝ) : ℂ) * deriv Γ (s₁ + τ * (s₂ - s₁))) τ := by
    intro τ hτ
    have hℓ : HasDerivAt (fun τ : ℝ => s₁ + τ * (s₂ - s₁)) (s₂ - s₁) τ := by
      simpa using ((hasDerivAt_id τ).mul_const (s₂ - s₁)).const_add s₁
    have h := (hΓ.hasDerivAt hI.1 (hmem τ hτ)).scomp τ hℓ
    rw [Complex.real_smul] at h
    exact h
  refine ⟨hd, ?_, ?_, ?_⟩
  · refine (horizontal_vertical_isPhiStraight).2 fun τ hτ => ?_
    have hτ' := Ioo_subset_Icc_self hτ
    obtain ⟨-, h2, h3⟩ := hΓ.2 _ (hmem τ hτ')
    have hne : ((s₂ - s₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
    have hval : φ (Γ (s₁ + τ * (s₂ - s₁))) *
        (((s₂ - s₁ : ℝ) : ℂ) * deriv Γ (s₁ + τ * (s₂ - s₁))) ^ 2 =
        ((-(s₂ - s₁) ^ 2 : ℝ) : ℂ) := by
      rw [mul_pow, mul_left_comm, h3]
      push_cast
      ring
    refine ⟨(hd τ hτ').differentiableAt, ?_, h2, ?_, ?_⟩
    · rw [(hd τ hτ').deriv]
      exact mul_ne_zero hne (hΓ.deriv_ne (hmem τ hτ'))
    · rw [(hd τ hτ').deriv, hval, Complex.ofReal_im]
    · rw [(hd τ hτ').deriv, hval, Complex.ofReal_re]
      nlinarith
  · exact hΓ.1.comp (contDiff_const.add (contDiff_id.mul contDiff_const)).contDiffOn hmem
  · rintro _ ⟨τ, hτ, rfl⟩
    exact (hΓ.2 _ (hmem τ hτ)).1

/-- A horizontal piece `τ ↦ ψ(x₂ + τ (x₁ - x₂))` of a regular chart, as a chain side. -/
theorem fx_p3_RegChart.hpiece {φ ζ : ℂ → ℂ} {p : ℂ} {r ρ0 : ℝ} (hR : fx_p3_RegChart φ ζ p r ρ0)
    {x₁ x₂ : ℝ} (hne : x₁ ≠ x₂)
    (hV : ∀ τ ∈ Icc (0 : ℝ) 1, (((x₂ + τ * (x₁ - x₂) : ℝ)) : ℂ) ∈ ζ '' ball p r) :
    (∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt
      (fun τ : ℝ => Function.invFunOn ζ (ball p r) (((x₂ + τ * (x₁ - x₂) : ℝ)) : ℂ))
      ((deriv ζ (Function.invFunOn ζ (ball p r) (((x₂ + τ * (x₁ - x₂) : ℝ)) : ℂ)))⁻¹ *
        ((x₁ - x₂ : ℝ) : ℂ)) τ) ∧
      IsPhiStraightArc φ
        (fun τ : ℝ => Function.invFunOn ζ (ball p r) (((x₂ + τ * (x₁ - x₂) : ℝ)) : ℂ)) 0 1 ∧
      ContDiffOn ℝ 1
        (fun τ : ℝ => Function.invFunOn ζ (ball p r) (((x₂ + τ * (x₁ - x₂) : ℝ)) : ℂ))
        (Icc 0 1) ∧
      (fun τ : ℝ => Function.invFunOn ζ (ball p r) (((x₂ + τ * (x₁ - x₂) : ℝ)) : ℂ)) ''
        Icc 0 1 ⊆ unitDisc := by
  obtain ⟨hopen, -, hψ⟩ := hR.inv
  have hBD := hR.2.2.1
  have han := hR.2.2.2.2.2.1
  set ψ := Function.invFunOn ζ (ball p r) with hψdef
  have hℓ : ∀ τ : ℝ, HasDerivAt (fun τ : ℝ => (((x₂ + τ * (x₁ - x₂) : ℝ)) : ℂ))
      ((x₁ - x₂ : ℝ) : ℂ) τ := fun τ => by
    have h := (((hasDerivAt_id τ).mul_const (x₁ - x₂)).const_add x₂).ofReal_comp
    simpa using h
  have hd : ∀ τ ∈ Icc (0 : ℝ) 1, HasDerivAt
      (fun τ : ℝ => ψ (((x₂ + τ * (x₁ - x₂) : ℝ)) : ℂ))
      ((deriv ζ (ψ (((x₂ + τ * (x₁ - x₂) : ℝ)) : ℂ)))⁻¹ * ((x₁ - x₂ : ℝ) : ℂ)) τ := by
    intro τ hτ
    have h := (hψ _ (hV τ hτ)).2.2.comp τ (hℓ τ)
    exact h
  refine ⟨hd, ?_, ?_, ?_⟩
  · refine (horizontal_vertical_isPhiStraight).1 fun τ hτ => ?_
    have hτ' := Ioo_subset_Icc_self hτ
    have hmem := (hψ _ (hV τ hτ')).1
    obtain ⟨-, h2, h3⟩ := han _ (ball_subset_closedBall hmem)
    have hx : ((x₁ - x₂ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (sub_ne_zero.2 hne)
    have hval : φ (ψ (((x₂ + τ * (x₁ - x₂) : ℝ)) : ℂ)) *
        ((deriv ζ (ψ (((x₂ + τ * (x₁ - x₂) : ℝ)) : ℂ)))⁻¹ * ((x₁ - x₂ : ℝ) : ℂ)) ^ 2 =
        (((x₁ - x₂) ^ 2 : ℝ) : ℂ) := by
      rw [← h2]
      field_simp
      push_cast
      ring
    refine ⟨(hd τ hτ').differentiableAt, ?_, ?_, ?_, ?_⟩
    · rw [(hd τ hτ').deriv]
      exact mul_ne_zero (inv_ne_zero h3) hx
    · rw [← h2]; exact pow_ne_zero 2 h3
    · rw [(hd τ hτ').deriv, hval, Complex.ofReal_im]
    · rw [(hd τ hτ').deriv, hval, Complex.ofReal_re]
      have : x₁ - x₂ ≠ 0 := sub_ne_zero.2 hne
      positivity
  · have hψc : ContDiffOn ℂ 1 ψ (ζ '' ball p r) := by
      refine DifferentiableOn.contDiffOn (fun w hw => ?_) hopen
      exact (hψ w hw).2.2.differentiableAt.differentiableWithinAt
    have hℓc : ContDiff ℝ 1 (fun τ : ℝ => (((x₂ + τ * (x₁ - x₂) : ℝ)) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_const.add (contDiff_id.mul contDiff_const))
    exact (hψc.restrict_scalars ℝ).comp hℓc.contDiffOn hV
  · rintro _ ⟨τ, hτ, rfl⟩
    exact hBD (ball_subset_closedBall (hψ _ (hV τ hτ)).1)

/-- **No recurrence** (the bigon argument).  A vertical trajectory on `(0, ∞)` has no regular cluster
point as `t → ∞`: otherwise it crosses a short horizontal chart segment `K` through the cluster point
at two consecutive times `s₁ < s₂`, and the vertical arc `Γ[s₁, s₂]` closed up by the piece of `K`
between the crossings is a closed chain of two `φ`-straight sides, contradicting `fx_chain_false`. -/
theorem fx_p3_no_recurrence {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {Γ : ℝ → ℂ} (hΓ : fx_p3_VT φ Γ (Ioi 0)) {p : ℂ}
    (hp : p ∈ unitDisc) (hp0 : φ p ≠ 0) : ¬ MapClusterPt p atTop Γ := by
  intro hcl
  obtain ⟨ζ, r, ρ0, hR, -⟩ := fx_p3_regChart_exists hφ hp hp0 one_pos
  obtain ⟨hopen, hleft, hψ⟩ := hR.inv
  have hr := hR.1
  have hρ0 := hR.2.1
  have hζ0 := hR.2.2.2.1
  have han := hR.2.2.2.2.2.1
  have hρB := hR.2.2.2.2.2.2
  set ψ := Function.invFunOn ζ (ball p r) with hψdef
  set δ := ρ0 / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  have hIOI : fx_p3_IsOI (Ioi (0 : ℝ)) := fx_p3_isOI_Ioi 0
  have hΓc : ContinuousOn Γ (Ioi 0) := hΓ.continuousOn
  have hinjΓ : InjOn Γ (Ioi 0) := hΓ.injOn hφ hne hIOI
  -- the horizontal chart segment `K = ψ([-δ, δ])`
  have hxV : ∀ x : ℝ, x ∈ Icc (-δ) δ → (x : ℂ) ∈ ζ '' ball p r := by
    intro x hx
    apply hρB
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    have : |x| ≤ δ := abs_le.2 hx
    linarith
  set K : Set ℂ := (fun x : ℝ => ψ (x : ℂ)) '' Icc (-δ) δ with hK
  have hKc : IsCompact K := by
    refine isCompact_Icc.image_of_continuousOn fun x hx => ?_
    have h1 : ContinuousAt ψ (x : ℂ) := (hψ _ (hxV x hx)).2.2.continuousAt
    exact (h1.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  -- local structure near a time where `Γ` is close to `p`
  have hloc : ∀ t : ℝ, 0 < t → Γ t ∈ ball p r → ‖ζ (Γ t)‖ ≤ δ →
      (deriv ζ (Γ t) * deriv Γ t) ^ 2 = -1 ∧ ∀ s : ℝ, 0 < t + s → |s| < 3 * δ →
        Γ (t + s) = ψ (ζ (Γ t) + (s : ℂ) * (deriv ζ (Γ t) * deriv Γ t)) := by
    intro t ht htB htδ
    obtain ⟨he2, h⟩ := hR.local_form hφ hIOI hΓ ht htB
    refine ⟨he2, fun s hs hsδ => h s hs ?_⟩
    linarith
  -- crossings of `K` exist at arbitrarily late times
  have hζc : ContinuousAt ζ p := (han p (mem_closedBall_self hr.le)).1.continuousAt
  obtain ⟨r₁, hr₁, hr₁ζ⟩ : ∃ r₁ > 0, ∀ z, dist z p < r₁ → ‖ζ z‖ < δ := by
    obtain ⟨ε, hε, hε'⟩ := Metric.continuousAt_iff.1 hζc δ hδ0
    exact ⟨ε, hε, fun z hz => by simpa [hζ0] using hε' hz⟩
  have hfreq : ∃ᶠ t in atTop, Γ t ∈ ball p (min r r₁) :=
    (mapClusterPt_iff_frequently.1 hcl) _ (ball_mem_nhds p (lt_min hr hr₁))
  have hcross : ∀ T : ℝ, ∃ t, T < t ∧ 0 < t ∧ Γ t ∈ K := by
    intro T
    obtain ⟨t, htB, htT⟩ := (hfreq.and_eventually (eventually_gt_atTop (max T 0 + δ))).exists
    have htB' : Γ t ∈ ball p r := ball_subset_ball (min_le_left _ _) htB
    have hwt : ‖ζ (Γ t)‖ < δ := hr₁ζ _ (lt_of_lt_of_le htB (min_le_right _ _))
    have ht0 : 0 < t := by linarith [le_max_right T 0]
    obtain ⟨he2, hl⟩ := hloc t ht0 htB' hwt.le
    set e := deriv ζ (Γ t) * deriv Γ t with he
    set w := ζ (Γ t) with hw
    obtain ⟨here, heim⟩ := fx_p3_sq_eq_neg_one he2
    set s := -w.im * e.im with hs
    have habs : |s| = |w.im| := by
      rw [hs, abs_mul, abs_neg]
      have : |e.im| = 1 := by
        have h := heim
        rw [← sq_abs] at h
        exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).1 h
      rw [this, mul_one]
    have hwim : |w.im| < δ := lt_of_le_of_lt (Complex.abs_im_le_norm w) hwt
    have hwre : |w.re| ≤ δ := (Complex.abs_re_le_norm w).trans hwt.le
    have hpt : w + (s : ℂ) * e = (w.re : ℂ) := by
      apply Complex.ext
      · rw [Complex.add_re, Complex.re_ofReal_mul, here, mul_zero, add_zero, Complex.ofReal_re]
      · rw [Complex.add_im, Complex.im_ofReal_mul, Complex.ofReal_im, hs]
        linear_combination (-w.im) * heim
    have hsb : |s| < δ := habs ▸ hwim
    have hs1 := (abs_lt.1 hsb).1
    have hpos : 0 < t + s := by linarith [le_max_right T 0]
    refine ⟨t + s, by linarith [le_max_left T 0], hpos, ?_⟩
    rw [hl s hpos (by linarith), hpt]
    exact ⟨w.re, abs_le.1 hwre, rfl⟩
  -- membership in `K`
  have hKmem : ∀ z ∈ K, ∃ x : ℝ, x ∈ Icc (-δ) δ ∧ z = ψ (x : ℂ) ∧ z ∈ ball p r ∧
      ζ z = (x : ℂ) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨h1, h2, -⟩ := hψ _ (hxV x hx)
    exact ⟨x, hx, rfl, h1, h2⟩
  -- crossings are isolated
  have hiso : ∀ t, 0 < t → Γ t ∈ K → ∀ s, 0 < s → s < 3 * δ → Γ (t + s) ∉ K := by
    intro t ht htK s hs hs3 hK'
    obtain ⟨a, ha, -, haB, haζ⟩ := hKmem _ htK
    have haδ : ‖ζ (Γ t)‖ ≤ δ := by
      rw [haζ, Complex.norm_real, Real.norm_eq_abs]; exact abs_le.2 ha
    obtain ⟨he2, hl⟩ := hloc t ht haB haδ
    obtain ⟨-, heim⟩ := fx_p3_sq_eq_neg_one he2
    obtain ⟨x, -, -, -, hxζ⟩ := hKmem _ hK'
    have h1 := hl s (by linarith) (by rw [abs_of_pos hs]; exact hs3)
    have hen : ‖deriv ζ (Γ t) * deriv Γ t‖ = 1 := by
      have h := congr_arg norm he2
      rw [norm_pow, norm_neg, norm_one] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
    have hV : ζ (Γ t) + (s : ℂ) * (deriv ζ (Γ t) * deriv Γ t) ∈ ζ '' ball p r := by
      apply hρB
      rw [mem_ball_zero_iff]
      calc ‖ζ (Γ t) + (s : ℂ) * (deriv ζ (Γ t) * deriv Γ t)‖
          ≤ ‖ζ (Γ t)‖ + ‖(s : ℂ) * (deriv ζ (Γ t) * deriv Γ t)‖ := norm_add_le _ _
        _ = ‖ζ (Γ t)‖ + s := by
            rw [norm_mul, hen, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
        _ < ρ0 := by linarith
    have h2 : ζ (Γ (t + s)) = ζ (Γ t) + (s : ℂ) * (deriv ζ (Γ t) * deriv Γ t) := by
      rw [h1]; exact (hψ _ hV).2.1
    rw [hxζ, haζ] at h2
    have h3 := congr_arg Complex.im h2
    rw [Complex.ofReal_im, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul,
      zero_add] at h3
    have hne : (deriv ζ (Γ t) * deriv Γ t).im ≠ 0 := by
      intro h; rw [h] at heim; norm_num at heim
    exact hne ((mul_eq_zero.1 h3.symm).resolve_left hs.ne')
  -- two consecutive crossings
  obtain ⟨s₁, -, hs₁0, hs₁K⟩ := hcross 0
  set A' : Set ℝ := Ici (s₁ + δ) ∩ Γ ⁻¹' K with hA'
  have hA'c : IsClosed A' :=
    (hΓc.mono fun t ht => lt_of_lt_of_le (by linarith) (mem_Ici.1 ht)).preimage_isClosed_of_isClosed
      isClosed_Ici hKc.isClosed
  obtain ⟨t', ht'1, -, ht'K⟩ := hcross (s₁ + δ)
  have hA'ne : A'.Nonempty := ⟨t', mem_Ici.2 ht'1.le, ht'K⟩
  have hA'bdd : BddBelow A' := ⟨s₁ + δ, fun t ht => ht.1⟩
  set s₂ := sInf A' with hs₂def
  have hs₂A : s₂ ∈ A' := hA'c.csInf_mem hA'ne hA'bdd
  have hs₂ge : s₁ + δ ≤ s₂ := hs₂A.1
  have hs₁s₂ : s₁ < s₂ := by linarith
  have hs₂0 : 0 < s₂ := by linarith
  have hgap : ∀ t ∈ Ioo s₁ s₂, Γ t ∉ K := by
    intro t ht htK
    by_cases h : t < s₁ + δ
    · have := hiso s₁ hs₁0 hs₁K (t - s₁) (by linarith [ht.1]) (by linarith)
      rw [add_sub_cancel] at this
      exact this htK
    · exact absurd (csInf_le hA'bdd ⟨not_lt.1 h, htK⟩) (not_le.2 ht.2)
  obtain ⟨x₁, hx₁, hx₁z, hx₁B, hx₁ζ⟩ := hKmem _ hs₁K
  obtain ⟨x₂, hx₂, hx₂z, hx₂B, hx₂ζ⟩ := hKmem _ hs₂A.2
  have hx12 : x₁ ≠ x₂ := by
    intro h
    have : Γ s₁ = Γ s₂ := by rw [hx₁z, hx₂z, h]
    exact absurd (hinjΓ hs₁0 hs₂0 this) (ne_of_lt hs₁s₂)
  have hconv : ∀ τ ∈ Icc (0 : ℝ) 1, x₂ + τ * (x₁ - x₂) ∈ Icc (-δ) δ := by
    intro τ hτ
    constructor <;> nlinarith [hx₁.1, hx₁.2, hx₂.1, hx₂.2, hτ.1, hτ.2]
  have hV12 : ∀ τ ∈ Icc (0 : ℝ) 1, ((x₂ + τ * (x₁ - x₂) : ℝ) : ℂ) ∈ ζ '' ball p r :=
    fun τ hτ => hxV _ (hconv τ hτ)
  obtain ⟨hd0, hst0, hsm0, hmem0⟩ := hΓ.piece hIOI hs₁s₂ hs₁0 hs₂0
  obtain ⟨hd1, hst1, hsm1, hmem1⟩ := hR.hpiece hx12 hV12
  set c₀ : ℝ → ℂ := fun τ => Γ (s₁ + τ * (s₂ - s₁)) with hc₀
  set c₁ : ℝ → ℂ := fun τ => ψ (((x₂ + τ * (x₁ - x₂) : ℝ)) : ℂ) with hc₁
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hI1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hc₀0 : c₀ 0 = Γ s₁ := by simp [hc₀]
  have hc₀1 : c₀ 1 = Γ s₂ := by simp [hc₀]
  have hc₁0 : c₁ 0 = Γ s₂ := by simp [hc₁, hx₂z]
  have hc₁1 : c₁ 1 = Γ s₁ := by simp [hc₁, hx₁z]
  have hdc₀0 : derivWithin c₀ (Icc 0 1) 0 = ((s₂ - s₁ : ℝ) : ℂ) * deriv Γ s₁ := by
    rw [fx_p3_derivWithin_Icc (hd0 0 hI0) hI0]; simp
  have hdc₀1 : derivWithin c₀ (Icc 0 1) 1 = ((s₂ - s₁ : ℝ) : ℂ) * deriv Γ s₂ := by
    rw [fx_p3_derivWithin_Icc (hd0 1 hI1) hI1]; simp
  have hdc₁0 : derivWithin c₁ (Icc 0 1) 0 =
      (deriv ζ (Γ s₂))⁻¹ * ((x₁ - x₂ : ℝ) : ℂ) := by
    rw [fx_p3_derivWithin_Icc (hd1 0 hI0) hI0]
    show (deriv ζ (c₁ 0))⁻¹ * ((x₁ - x₂ : ℝ) : ℂ) = _
    rw [hc₁0]
  have hdc₁1 : derivWithin c₁ (Icc 0 1) 1 =
      (deriv ζ (Γ s₁))⁻¹ * ((x₁ - x₂ : ℝ) : ℂ) := by
    rw [fx_p3_derivWithin_Icc (hd1 1 hI1) hI1]
    show (deriv ζ (c₁ 1))⁻¹ * ((x₁ - x₂ : ℝ) : ℂ) = _
    rw [hc₁1]
  -- the vertical velocities in the chart
  have he₁ : (deriv ζ (Γ s₁) * deriv Γ s₁) ^ 2 = -1 :=
    (hR.local_form hφ hIOI hΓ hs₁0 hx₁B).1
  have he₂ : (deriv ζ (Γ s₂) * deriv Γ s₂) ^ 2 = -1 :=
    (hR.local_form hφ hIOI hΓ hs₂0 hx₂B).1
  have hζ₁ : deriv ζ (Γ s₁) ≠ 0 := (han _ (ball_subset_closedBall hx₁B)).2.2
  have hζ₂ : deriv ζ (Γ s₂) ≠ 0 := (han _ (ball_subset_closedBall hx₂B)).2.2
  have hΓ₁ : deriv Γ s₁ ≠ 0 := hΓ.deriv_ne hs₁0
  have hΓ₂ : deriv Γ s₂ ≠ 0 := hΓ.deriv_ne hs₂0
  have hs21 : ((s₂ - s₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by linarith)
  have hx21 : ((x₁ - x₂ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (sub_ne_zero.2 hx12)
  set side : Fin 2 → ℝ → ℂ := ![c₀, c₁] with hside
  have hC : fx_IsChain φ side := by
    refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, ?_, fun j => ?_, fun j => ?_,
      fun j => ?_⟩
    · fin_cases j
      · exact hst0
      · exact hst1
    · fin_cases j
      · exact hsm0
      · exact hsm1
    · fin_cases j
      · exact hmem0
      · exact hmem1
    · fin_cases j
      · show c₀ 1 = c₁ 0
        rw [hc₀1, hc₁0]
      · show c₁ 1 = c₀ 0
        rw [hc₁1, hc₀0]
    · have hζc₁ : ∀ t ∈ Icc (0 : ℝ) 1, ζ (c₁ t) = (((x₂ + t * (x₁ - x₂) : ℝ)) : ℂ) :=
        fun t ht => (hψ _ (hV12 t ht)).2.1
      have hc₁K : ∀ t ∈ Icc (0 : ℝ) 1, c₁ t ∈ K := fun t ht => ⟨_, hconv t ht, rfl⟩
      have hcross01 : ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1, c₀ s = c₁ t → False := by
        intro s hs t ht h
        have ht' : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
        rcases hs.1.eq_or_lt with h0 | h0
        · subst h0
          rw [hc₀0] at h
          have h1 := congr_arg ζ h
          rw [hx₁ζ, hζc₁ t ht'] at h1
          have h2 : x₁ = x₂ + t * (x₁ - x₂) := Complex.ofReal_injective h1
          have h3 : (1 - t) * (x₁ - x₂) = 0 := by linarith
          rcases mul_eq_zero.1 h3 with h4 | h4
          · linarith [ht.2]
          · exact hx12 (sub_eq_zero.1 h4)
        · have hu : s₁ + s * (s₂ - s₁) ∈ Ioo s₁ s₂ := by
            constructor <;> nlinarith [hs.2]
          have hK1 : c₀ s ∈ K := by rw [h]; exact hc₁K t ht'
          exact hgap _ hu hK1
      intro i j s hs t ht hst
      fin_cases i <;> fin_cases j
      · refine ⟨rfl, ?_⟩
        have h : Γ (s₁ + s * (s₂ - s₁)) = Γ (s₁ + t * (s₂ - s₁)) := hst
        have hpos : ∀ u ∈ Ico (0 : ℝ) 1, s₁ + u * (s₂ - s₁) ∈ Ioi 0 := fun u hu => by
          have := mul_nonneg hu.1 (sub_nonneg.2 hs₁s₂.le)
          exact mem_Ioi.2 (by linarith)
        have h1 := hinjΓ (hpos s hs) (hpos t ht) h
        have hne : s₂ - s₁ ≠ 0 := by linarith
        exact mul_right_cancel₀ hne (by linarith)
      · exact (hcross01 s hs t ht hst).elim
      · exact (hcross01 t ht s hs hst.symm).elim
      · refine ⟨rfl, ?_⟩
        have h1 := congr_arg ζ (show c₁ s = c₁ t from hst)
        rw [hζc₁ s (Ico_subset_Icc_self hs), hζc₁ t (Ico_subset_Icc_self ht)] at h1
        have h2 : x₂ + s * (x₁ - x₂) = x₂ + t * (x₁ - x₂) := Complex.ofReal_injective h1
        exact mul_right_cancel₀ (sub_ne_zero.2 hx12) (by linarith)
    · fin_cases j
      · show derivWithin c₀ (Icc 0 1) 0 ≠ 0
        rw [hdc₀0]; exact mul_ne_zero hs21 hΓ₁
      · show derivWithin c₁ (Icc 0 1) 0 ≠ 0
        rw [hdc₁0]; exact mul_ne_zero (inv_ne_zero hζ₂) hx21
    · fin_cases j
      · show derivWithin c₀ (Icc 0 1) 1 ≠ 0
        rw [hdc₀1]; exact mul_ne_zero hs21 hΓ₂
      · show derivWithin c₁ (Icc 0 1) 1 ≠ 0
        rw [hdc₁1]; exact mul_ne_zero (inv_ne_zero hζ₁) hx21
    · fin_cases j
      · show arg (-(derivWithin c₁ (Icc 0 1) 1) / derivWithin c₀ (Icc 0 1) 0) ≠ 0
        rw [hdc₁1, hdc₀0]
        obtain ⟨hre, -⟩ := fx_p3_sq_eq_neg_one he₁
        have hid : -((deriv ζ (Γ s₁))⁻¹ * ((x₁ - x₂ : ℝ) : ℂ)) / (((s₂ - s₁ : ℝ) : ℂ) *
            deriv Γ s₁) = (((x₁ - x₂) / (s₂ - s₁) : ℝ) : ℂ) *
            (deriv ζ (Γ s₁) * deriv Γ s₁) := by
          rw [div_eq_iff (mul_ne_zero hs21 hΓ₁), Complex.ofReal_div]
          calc -((deriv ζ (Γ s₁))⁻¹ * ((x₁ - x₂ : ℝ) : ℂ))
              = (deriv ζ (Γ s₁))⁻¹ * ((x₁ - x₂ : ℝ) : ℂ) * (-1) := by ring
            _ = (deriv ζ (Γ s₁))⁻¹ * ((x₁ - x₂ : ℝ) : ℂ) * (deriv ζ (Γ s₁) * deriv Γ s₁) ^ 2 := by
                rw [he₁]
            _ = ((x₁ - x₂ : ℝ) : ℂ) / ((s₂ - s₁ : ℝ) : ℂ) * (deriv ζ (Γ s₁) * deriv Γ s₁) *
                (((s₂ - s₁ : ℝ) : ℂ) * deriv Γ s₁) := by
                field_simp
        rw [hid]
        refine fx_p3_arg_ne_zero_of_re_eq_zero ?_ ?_
        · rw [Complex.re_ofReal_mul, hre, mul_zero]
        · refine mul_ne_zero (Complex.ofReal_ne_zero.2 ?_) (mul_ne_zero hζ₁ hΓ₁)
          exact div_ne_zero (sub_ne_zero.2 hx12) (by linarith)
      · show arg (-(derivWithin c₀ (Icc 0 1) 1) / derivWithin c₁ (Icc 0 1) 0) ≠ 0
        rw [hdc₀1, hdc₁0]
        obtain ⟨hre, -⟩ := fx_p3_sq_eq_neg_one he₂
        have hid : -(((s₂ - s₁ : ℝ) : ℂ) * deriv Γ s₂) / ((deriv ζ (Γ s₂))⁻¹ *
            ((x₁ - x₂ : ℝ) : ℂ)) = ((-(s₂ - s₁) / (x₁ - x₂) : ℝ) : ℂ) *
            (deriv ζ (Γ s₂) * deriv Γ s₂) := by
          rw [div_eq_iff (mul_ne_zero (inv_ne_zero hζ₂) hx21), Complex.ofReal_div,
            Complex.ofReal_neg]
          field_simp
        rw [hid]
        refine fx_p3_arg_ne_zero_of_re_eq_zero ?_ ?_
        · rw [Complex.re_ofReal_mul, hre, mul_zero]
        · refine mul_ne_zero (Complex.ofReal_ne_zero.2 ?_) (mul_ne_zero hζ₂ hΓ₂)
          exact div_ne_zero (by linarith) (sub_ne_zero.2 hx12)
  have h3 := fx_chain_false hφ hne hC
  have h2 : {j : Fin 2 | ¬ fx_IsBlunt φ side j}.ncard ≤ 2 := by
    calc {j : Fin 2 | ¬ fx_IsBlunt φ side j}.ncard ≤ (univ : Set (Fin 2)).ncard :=
          Set.ncard_le_ncard (subset_univ _)
      _ = 2 := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

/-- A tame `φ ≢ 0` has finitely many zeros in `Δ` (isolated zeros of an analytic function on the
connected `ball 0 ρ ⊇ closedBall 0 1`). -/
theorem fx_p3_zeros_finite {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) : {q : ℂ | q ∈ unitDisc ∧ φ q = 0}.Finite := by
  by_contra hinf
  have hsub : {q : ℂ | q ∈ unitDisc ∧ φ q = 0} ⊆ closedBall 0 1 := fun q hq =>
    ball_subset_closedBall hq.1
  obtain ⟨z, hz, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    (isCompact_closedBall 0 1) hsub
  have hzρ : z ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff]
    have := mem_closedBall_zero_iff.1 hz
    linarith
  have han : AnalyticOnNhd ℂ φ (ball 0 ρ) := hφ.analyticOnNhd isOpen_ball
  have hfreq : ∃ᶠ w in 𝓝[≠] z, φ w = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hacc
    exact hacc.mono fun w hw => hw.2
  have := han.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball 0 ρ).isPreconnected
    hzρ hfreq
  obtain ⟨w, hw, hw0⟩ := hne
  exact hw0 (this (ball_subset_ball hρ.le hw))

/-- **The dichotomy for a maximal vertical ray.**  A maximal trajectory either leaves every compact
subset of `Δ` (along its tail filter), or it lives on a bounded interval `(0, L)` and converges to a
zero of `φ` as `t → L`.  (Regular cluster points are excluded by maximality on `(0, L)` and by the
bigon argument on `(0, ∞)`; a cluster point at a zero forces convergence; convergence to a zero is
impossible on `(0, ∞)`.) -/
theorem fx_p3_ray_dichotomy {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {M Γ : ℝ → ℂ} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hΓM : EqOn Γ M (Ioo 0 t₀))
    (hcase : (∃ L, t₀ ≤ L ∧ fx_p3_VT φ Γ (Ioo 0 L) ∧
          ∀ (γ : ℝ → ℂ) (T ε : ℝ), 0 < ε → fx_p3_VT φ γ (Ioo 0 T) → EqOn γ M (Ioo 0 ε) → T ≤ L) ∨
        fx_p3_VT φ Γ (Ioi 0)) :
    (∃ L, t₀ ≤ L ∧ fx_p3_VT φ Γ (Ioo 0 L) ∧
        ((∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc → ∀ᶠ t in 𝓝[<] L, Γ t ∉ K) ∨
          ∃ q, q ∈ unitDisc ∧ φ q = 0 ∧ Tendsto Γ (𝓝[<] L) (𝓝 q))) ∨
      (fx_p3_VT φ Γ (Ioi 0) ∧ ∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc → ∀ᶠ t in atTop, Γ t ∉ K) := by
  have hφD : DifferentiableOn ℂ φ unitDisc := hφ.mono (ball_subset_ball hρ.le)
  have hiso : ∀ q ∈ unitDisc, φ q = 0 → ∃ ε > 0, closedBall q ε ⊆ unitDisc ∧
      ∀ z ∈ closedBall q ε, z ≠ q → φ z ≠ 0 := by
    intro q hq hq0
    obtain ⟨m, -, -, ζ, r, ρ0, hZ⟩ := fx_p3_zeroChart_exists hρ hφ hne hq hq0
    exact ⟨r, hZ.1, hZ.2.2.1, fun z hz hzq => hZ.ne_zero hz hzq⟩
  rcases hcase with ⟨L, hL, hΓ, hmax⟩ | hΓ
  · left
    refine ⟨L, hL, hΓ, ?_⟩
    by_cases hK : ∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc → ∀ᶠ t in 𝓝[<] L, Γ t ∉ K
    · exact Or.inl hK
    right
    have hL0 : 0 < L := ht₀.trans_le hL
    have hbasis : ∀ U ∈ 𝓝[<] L, ∃ a ∈ Ioo (0 : ℝ) L, ∀ t ∈ Ioo (0 : ℝ) L, a < t → t ∈ U := by
      intro U hU
      obtain ⟨a, ha, haU⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hL0).1 hU
      refine ⟨max a (L / 2), ⟨by positivity, max_lt ha (by linarith)⟩, fun t ht htt => haU ?_⟩
      exact ⟨lt_of_le_of_lt (le_max_left _ _) htt, ht.2⟩
    exact fx_p3_tail_to_zero (fx_p3_isOI_Ioo 0 L) hΓ.continuousOn (Ioo_mem_nhdsLT hL0) hbasis
      (fun a ha => Filter.eventually_of_mem (Ioo_mem_nhdsLT ha.2) fun t ht => ht.1)
      (fun p hp hp0 => fx_p3_maxTraj_no_regular_cluster hφD ht₀ hΓM hL hΓ hmax hp hp0) hiso hK
  · right
    refine ⟨hΓ, ?_⟩
    by_contra hK
    have hbasis : ∀ U ∈ (atTop : Filter ℝ), ∃ a ∈ Ioi (0 : ℝ), ∀ t ∈ Ioi (0 : ℝ), a < t → t ∈ U := by
      intro U hU
      obtain ⟨a, ha⟩ := mem_atTop_sets.1 hU
      refine ⟨max a 1, mem_Ioi.2 (lt_of_lt_of_le one_pos (le_max_right _ _)),
        fun t _ ht => ha t ?_⟩
      exact (le_max_left _ _).trans ht.le
    obtain ⟨q, hq, hq0, hT⟩ := fx_p3_tail_to_zero (fx_p3_isOI_Ioi 0) hΓ.continuousOn
      (eventually_gt_atTop 0) hbasis (fun a _ => eventually_gt_atTop a)
      (fun p hp hp0 => fx_p3_no_recurrence hφD hne hΓ hp hp0) hiso hK
    obtain ⟨m, hm, -, ζ, r, ρ0, hZ⟩ := fx_p3_zeroChart_exists hρ hφ hne hq hq0
    exact hZ.no_arrival_Ioi hm hΓ hT

/-- End function at `0`: `s ↦ A s g(s)^(-κ)` is `C¹` near `0` with derivative `A` there, when `g` is
`C¹` near `0` with `g 0 = 1`. -/
theorem fx_p3_endfun0 {g : ℝ → ℝ} (hg : ContDiffAt ℝ 1 g 0) (hg0 : g 0 = 1) (A κ : ℝ) :
    ContDiffAt ℝ 1 (fun s => A * s * g s ^ (-κ)) 0 ∧
      HasDerivAt (fun s => A * s * g s ^ (-κ)) A 0 := by
  have hG : ContDiffAt ℝ 1 (fun s => g s ^ (-κ)) 0 := hg.rpow_const_of_ne (by rw [hg0]; norm_num)
  refine ⟨(contDiffAt_const.mul contDiffAt_id).mul hG, ?_⟩
  have hGd : HasDerivAt (fun s => g s ^ (-κ)) (deriv (fun s => g s ^ (-κ)) 0) 0 :=
    (hG.differentiableAt one_ne_zero).hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => A * s) A 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul A
  exact (h1.mul hGd).congr_deriv (by simp [hg0])

/-- End function at `1`: `s ↦ A (1 - s) g(s)^(-κ)` is `C¹` near `1` with derivative `-A` there, when
`g` is `C¹` near `1` with `g 1 = 1`. -/
theorem fx_p3_endfun1 {g : ℝ → ℝ} (hg : ContDiffAt ℝ 1 g 1) (hg1 : g 1 = 1) (A κ : ℝ) :
    ContDiffAt ℝ 1 (fun s => A * (1 - s) * g s ^ (-κ)) 1 ∧
      HasDerivAt (fun s => A * (1 - s) * g s ^ (-κ)) (-A) 1 := by
  have hG : ContDiffAt ℝ 1 (fun s => g s ^ (-κ)) 1 := hg.rpow_const_of_ne (by rw [hg1]; norm_num)
  refine ⟨(contDiffAt_const.mul (contDiffAt_const.sub contDiffAt_id)).mul hG, ?_⟩
  have hGd : HasDerivAt (fun s => g s ^ (-κ)) (deriv (fun s => g s ^ (-κ)) 1) 1 :=
    (hG.differentiableAt one_ne_zero).hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => A * (1 - s)) (A * (-1)) 1 :=
    ((hasDerivAt_id (1 : ℝ)).const_sub 1).const_mul A
  exact (h1.mul hGd).congr_deriv (by simp [hg1])

/-- **Reparametrization of an unbounded ray**: `σ(s) = s^a / (1 - s)` maps `(0, 1)` increasingly
onto `(0, ∞)`, is `C¹` with `σ' > 0`, tends to `∞` at `1`, and `σ^κ = s (1 - s)^(-κ)` (`a κ = 1`). -/
theorem fx_p3_sigma_inf {a κ : ℝ} (ha : 1 ≤ a) (haκ : a * κ = 1) :
    (∀ s ∈ Ioo (0 : ℝ) 1, 0 < s ^ a / (1 - s)) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, ∃ d > 0, HasDerivAt (fun s : ℝ => s ^ a / (1 - s)) d s) ∧
      StrictMonoOn (fun s : ℝ => s ^ a / (1 - s)) (Ioo 0 1) ∧
      (∀ τ > 0, ∃ s ∈ Ioo (0 : ℝ) 1, s ^ a / (1 - s) = τ) ∧
      Tendsto (fun s : ℝ => s ^ a / (1 - s)) (𝓝[<] 1) atTop ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, (s ^ a / (1 - s)) ^ κ = 1 * s * (1 - s) ^ (-κ)) ∧
      ContDiffAt ℝ 1 (fun s : ℝ => 1 - s) 0 ∧ (fun s : ℝ => 1 - s) 0 = 1 := by
  set σ : ℝ → ℝ := fun s => s ^ a / (1 - s) with hσ
  have hpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < σ s := fun s hs =>
    div_pos (Real.rpow_pos_of_pos hs.1 a) (by linarith [hs.2])
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt σ
      ((a * s ^ (a - 1) * (1 - s) - s ^ a * (-1)) / (1 - s) ^ 2) s := by
    intro s hs
    have h1 := Real.hasDerivAt_rpow_const (x := s) (p := a) (Or.inl hs.1.ne')
    have h2 : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub 1
    exact h1.div h2 (by linarith [hs.2])
  have hdpos : ∀ s ∈ Ioo (0 : ℝ) 1,
      0 < (a * s ^ (a - 1) * (1 - s) - s ^ a * (-1)) / (1 - s) ^ 2 := by
    intro s hs
    have h1 : 0 < 1 - s := by linarith [hs.2]
    have h2 := Real.rpow_pos_of_pos hs.1 (a - 1)
    have h3 := Real.rpow_pos_of_pos hs.1 a
    apply div_pos _ (by positivity)
    have : 0 < a * s ^ (a - 1) * (1 - s) := by positivity
    linarith
  have hmono : StrictMonoOn σ (Ioo 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo 0 1) ?_ ?_
    · intro s hs; exact (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ioo] at hs
      rw [(hderiv s hs).deriv]
      exact hdpos s hs
  have hlim1 : Tendsto σ (𝓝[<] 1) atTop := by
    have h1 : Tendsto (fun s : ℝ => s ^ a) (𝓝[<] 1) (𝓝 1) := by
      have := (Real.continuousAt_rpow_const 1 a (Or.inl one_ne_zero)).tendsto
      rw [Real.one_rpow] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun s : ℝ => (1 - s)⁻¹) (𝓝[<] 1) atTop := by
      refine tendsto_inv_nhdsGT_zero.comp ?_
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h : Tendsto (fun s : ℝ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) :=
          tendsto_const_nhds.sub tendsto_id
        rw [sub_self] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact sub_pos.2 (mem_Iio.1 hs)
    have := h1.pos_mul_atTop one_pos h2
    refine this.congr fun s => ?_
    simp [hσ, div_eq_mul_inv]
  have hlim0 : Tendsto σ (𝓝[>] 0) (𝓝 0) := by
    have h : ContinuousAt σ 0 := by
      exact (Real.continuousAt_rpow_const 0 a (Or.inr (by linarith))).div
        (continuous_const.sub continuous_id').continuousAt (by norm_num)
    have h0 : σ 0 = 0 := by simp [hσ, Real.zero_rpow (by linarith : a ≠ 0)]
    have h1 := h.tendsto
    rw [h0] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  refine ⟨hpos, fun s hs => ⟨_, hdpos s hs, hderiv s hs⟩, hmono, ?_, hlim1, ?_, ?_, by norm_num⟩
  · intro τ hτ
    obtain ⟨sa, hsa1, hsa2⟩ : ∃ s ∈ Ioo (0 : ℝ) 1, σ s < τ := by
      have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), σ s < τ := hlim0.eventually (gt_mem_nhds hτ)
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
      obtain ⟨s, hs1, hs2⟩ := (h1.and h2).exists
      exact ⟨s, hs2, hs1⟩
    obtain ⟨sb, hsb1, hsb2⟩ : ∃ s ∈ Ioo (0 : ℝ) 1, τ < σ s := by
      have h1 : ∀ᶠ s in 𝓝[<] (1 : ℝ), τ < σ s := hlim1.eventually (eventually_gt_atTop τ)
      have h2 : ∀ᶠ s in 𝓝[<] (1 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT one_pos
      obtain ⟨s, hs1, hs2⟩ := (h1.and h2).exists
      exact ⟨s, hs2, hs1⟩
    have hab : sa < sb := by
      by_contra h
      have := hmono.monotoneOn hsb1 hsa1 (not_lt.1 h)
      linarith
    have hsub : Icc sa sb ⊆ Ioo 0 1 := fun s hs => ⟨lt_of_lt_of_le hsa1.1 hs.1,
      lt_of_le_of_lt hs.2 hsb1.2⟩
    have hc : ContinuousOn σ (Icc sa sb) := fun s hs =>
      (hderiv s (hsub hs)).continuousAt.continuousWithinAt
    obtain ⟨s, hs, hsτ⟩ := intermediate_value_Icc hab.le hc ⟨hsa2.le, hsb2.le⟩
    exact ⟨s, hsub hs, hsτ⟩
  · intro s hs
    have h1 : 0 < 1 - s := by linarith [hs.2]
    rw [Real.div_rpow (Real.rpow_nonneg hs.1.le a) h1.le, ← Real.rpow_mul hs.1.le, haκ,
      Real.rpow_one, Real.rpow_neg h1.le, one_mul, div_eq_mul_inv]
  · exact contDiffAt_const.sub contDiffAt_id

/-- `s ↦ s^a` is `C¹` on `ℝ` for `a ≥ 1`. -/
theorem fx_p3_rpow_C1 {a : ℝ} (ha : 1 ≤ a) : ContDiff ℝ 1 (fun s : ℝ => s ^ a) := by
  have h := Real.contDiff_rpow_const_of_le (p := a) (n := 1) (by exact_mod_cast ha)
  exact_mod_cast h

/-- **Reparametrization of a bounded ray**: `σ(s) = L s^a / (s^a + (1 - s)^b)` maps `(0, 1)`
increasingly onto `(0, L)`, is `C¹` with `σ' > 0`, tends to `L` at `1`, and
`σ^κ = L^κ s g(s)^(-κ)`, `(L - σ)^κ' = L^κ' (1 - s) g(s)^(-κ')` with `g = s^a + (1 - s)^b`
(`a κ = 1 = b κ'`). -/
theorem fx_p3_sigma_fin {a b κ κ' L : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (haκ : a * κ = 1)
    (hbκ : b * κ' = 1) (hL : 0 < L) :
    (∀ s ∈ Ioo (0 : ℝ) 1, L * s ^ a / (s ^ a + (1 - s) ^ b) ∈ Ioo 0 L) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, ∃ d > 0,
        HasDerivAt (fun s : ℝ => L * s ^ a / (s ^ a + (1 - s) ^ b)) d s) ∧
      StrictMonoOn (fun s : ℝ => L * s ^ a / (s ^ a + (1 - s) ^ b)) (Ioo 0 1) ∧
      (∀ τ ∈ Ioo 0 L, ∃ s ∈ Ioo (0 : ℝ) 1, L * s ^ a / (s ^ a + (1 - s) ^ b) = τ) ∧
      Tendsto (fun s : ℝ => L * s ^ a / (s ^ a + (1 - s) ^ b)) (𝓝[<] 1) (𝓝[<] L) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, (L * s ^ a / (s ^ a + (1 - s) ^ b)) ^ κ =
        L ^ κ * s * (s ^ a + (1 - s) ^ b) ^ (-κ)) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, (L - L * s ^ a / (s ^ a + (1 - s) ^ b)) ^ κ' =
        L ^ κ' * (1 - s) * (s ^ a + (1 - s) ^ b) ^ (-κ')) ∧
      ContDiffAt ℝ 1 (fun s : ℝ => s ^ a + (1 - s) ^ b) 0 ∧
      (fun s : ℝ => s ^ a + (1 - s) ^ b) 0 = 1 ∧
      ContDiffAt ℝ 1 (fun s : ℝ => s ^ a + (1 - s) ^ b) 1 ∧
      (fun s : ℝ => s ^ a + (1 - s) ^ b) 1 = 1 := by
  set g : ℝ → ℝ := fun s => s ^ a + (1 - s) ^ b with hg
  set σ : ℝ → ℝ := fun s => L * s ^ a / g s with hσ
  have ha0 : a ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  have hgpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < g s := by
    intro s hs
    rcases hs.1.eq_or_lt with h | h
    · subst h; simp [hg, Real.zero_rpow ha0]
    · have := Real.rpow_pos_of_pos h a
      have := Real.rpow_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s) b
      simp only [hg]; linarith
  have hg0 : g 0 = 1 := by simp [hg, Real.zero_rpow ha0]
  have hg1 : g 1 = 1 := by simp [hg, Real.zero_rpow hb0]
  have hpos : ∀ s ∈ Ioo (0 : ℝ) 1, σ s ∈ Ioo 0 L := by
    intro s hs
    have h1 := Real.rpow_pos_of_pos hs.1 a
    have h2 := Real.rpow_pos_of_pos (by linarith [hs.2] : (0 : ℝ) < 1 - s) b
    have hg' : 0 < g s := hgpos s (Ioo_subset_Icc_self hs)
    refine ⟨div_pos (mul_pos hL h1) hg', ?_⟩
    rw [div_lt_iff₀ hg']
    simp only [hg]
    nlinarith
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt σ
      ((L * (a * s ^ (a - 1)) * g s - L * s ^ a *
        (a * s ^ (a - 1) + -1 * b * (1 - s) ^ (b - 1))) / g s ^ 2) s := by
    intro s hs
    have h1 := (Real.hasDerivAt_rpow_const (x := s) (p := a) (Or.inl hs.1.ne')).const_mul L
    have h2 : HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub 1
    have h3 := h2.rpow_const (p := b) (Or.inl (by linarith [hs.2]))
    have h4 := (Real.hasDerivAt_rpow_const (x := s) (p := a) (Or.inl hs.1.ne')).add h3
    exact h1.div h4 (hgpos s (Ioo_subset_Icc_self hs)).ne'
  have hdpos : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < (L * (a * s ^ (a - 1)) * g s - L * s ^ a *
      (a * s ^ (a - 1) + -1 * b * (1 - s) ^ (b - 1))) / g s ^ 2 := by
    intro s hs
    have h1 := Real.rpow_pos_of_pos hs.1 (a - 1)
    have h2 := Real.rpow_pos_of_pos hs.1 a
    have h3 := Real.rpow_pos_of_pos (by linarith [hs.2] : (0 : ℝ) < 1 - s) b
    have h4 := Real.rpow_pos_of_pos (by linarith [hs.2] : (0 : ℝ) < 1 - s) (b - 1)
    have hg' : 0 < g s := hgpos s (Ioo_subset_Icc_self hs)
    apply div_pos _ (by positivity)
    have e : L * (a * s ^ (a - 1)) * g s - L * s ^ a *
        (a * s ^ (a - 1) + -1 * b * (1 - s) ^ (b - 1)) =
        L * a * s ^ (a - 1) * (1 - s) ^ b + L * b * s ^ a * (1 - s) ^ (b - 1) := by
      simp only [hg]; ring
    rw [e]
    have : 0 < a := by linarith
    have : 0 < b := by linarith
    positivity
  have hmono : StrictMonoOn σ (Ioo 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo 0 1) ?_ ?_
    · intro s hs; exact (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ioo] at hs
      rw [(hderiv s hs).deriv]
      exact hdpos s hs
  have hgc : Continuous g := by
    refine (Real.continuous_rpow_const (by linarith)).add ?_
    exact (Real.continuous_rpow_const (by linarith)).comp (continuous_const.sub continuous_id)
  have hσcA : ∀ s ∈ Icc (0 : ℝ) 1, ContinuousAt σ s := by
    intro s hs
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const s a (Or.inr (by linarith)))).div
      hgc.continuousAt (hgpos s hs).ne'
  have hI0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hI1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hσ0 : σ 0 = 0 := by simp [hσ, Real.zero_rpow ha0]
  have hσ1 : σ 1 = L := by
    show L * 1 ^ a / g 1 = L
    rw [hg1, Real.one_rpow, mul_one, div_one]
  have hlim1 : Tendsto σ (𝓝[<] 1) (𝓝[<] L) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h := (hσcA 1 hI1).tendsto
      rw [hσ1] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT (zero_lt_one' ℝ)] with s hs
      exact (hpos s hs).2
  have hlim0 : Tendsto σ (𝓝[>] 0) (𝓝 0) := by
    have h := (hσcA 0 hI0).tendsto
    rw [hσ0] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine ⟨hpos, fun s hs => ⟨_, hdpos s hs, hderiv s hs⟩, hmono, ?_, hlim1, ?_, ?_, ?_, hg0,
    ?_, hg1⟩
  · intro τ hτ
    obtain ⟨sa, hsa1, hsa2⟩ : ∃ s ∈ Ioo (0 : ℝ) 1, σ s < τ := by
      have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), σ s < τ := hlim0.eventually (gt_mem_nhds hτ.1)
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT one_pos
      obtain ⟨s, hs1, hs2⟩ := (h1.and h2).exists
      exact ⟨s, hs2, hs1⟩
    obtain ⟨sb, hsb1, hsb2⟩ : ∃ s ∈ Ioo (0 : ℝ) 1, τ < σ s := by
      have h1 : ∀ᶠ s in 𝓝[<] (1 : ℝ), τ < σ s :=
        (hlim1.mono_right nhdsWithin_le_nhds).eventually (lt_mem_nhds hτ.2)
      have h2 : ∀ᶠ s in 𝓝[<] (1 : ℝ), s ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT one_pos
      obtain ⟨s, hs1, hs2⟩ := (h1.and h2).exists
      exact ⟨s, hs2, hs1⟩
    have hab : sa < sb := by
      by_contra h
      have := hmono.monotoneOn hsb1 hsa1 (not_lt.1 h)
      linarith
    have hsub : Icc sa sb ⊆ Ioo 0 1 := fun s hs => ⟨lt_of_lt_of_le hsa1.1 hs.1,
      lt_of_le_of_lt hs.2 hsb1.2⟩
    have hc : ContinuousOn σ (Icc sa sb) := fun s hs =>
      (hderiv s (hsub hs)).continuousAt.continuousWithinAt
    obtain ⟨s, hs, hsτ⟩ := intermediate_value_Icc hab.le hc ⟨hsa2.le, hsb2.le⟩
    exact ⟨s, hsub hs, hsτ⟩
  · intro s hs
    have hg' : 0 < g s := hgpos s (Ioo_subset_Icc_self hs)
    show (L * s ^ a / g s) ^ κ = L ^ κ * s * g s ^ (-κ)
    rw [Real.div_rpow (mul_nonneg hL.le (Real.rpow_nonneg hs.1.le a)) hg'.le,
      Real.mul_rpow hL.le (Real.rpow_nonneg hs.1.le a), ← Real.rpow_mul hs.1.le, haκ,
      Real.rpow_one, Real.rpow_neg hg'.le, div_eq_mul_inv]
  · intro s hs
    have hg' : 0 < g s := hgpos s (Ioo_subset_Icc_self hs)
    have h1s : 0 ≤ 1 - s := by linarith [hs.2]
    show (L - L * s ^ a / g s) ^ κ' = L ^ κ' * (1 - s) * g s ^ (-κ')
    have e : L - L * s ^ a / g s = L * (1 - s) ^ b / g s := by
      field_simp
      simp only [hg]
      ring
    rw [e, Real.div_rpow (mul_nonneg hL.le (Real.rpow_nonneg h1s b)) hg'.le,
      Real.mul_rpow hL.le (Real.rpow_nonneg h1s b), ← Real.rpow_mul h1s, hbκ,
      Real.rpow_one, Real.rpow_neg hg'.le, div_eq_mul_inv]
  · exact (fx_p3_rpow_C1 ha).contDiffAt.add
      ((contDiffAt_const.sub contDiffAt_id).rpow_const_of_ne (by norm_num))
  · exact (fx_p3_rpow_C1 ha).contDiffAt.add
      ((fx_p3_rpow_C1 hb).contDiffAt.comp (1 : ℝ) (contDiffAt_const.sub contDiffAt_id))

/-- The unbounded reparametrization is `C¹` on `(0, 1)`. -/
theorem fx_p3_sigma_inf_C1 {a : ℝ} {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 1 (fun s : ℝ => s ^ a / (1 - s)) s :=
  (Real.contDiffAt_rpow_const_of_ne hs.1.ne').div (contDiffAt_const.sub contDiffAt_id)
    (by show (1 : ℝ) - s ≠ 0; linarith [hs.2])

/-- The bounded reparametrization is `C¹` on `(0, 1)`. -/
theorem fx_p3_sigma_fin_C1 {a b L : ℝ} (ha : 1 ≤ a) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 1 (fun s : ℝ => L * s ^ a / (s ^ a + (1 - s) ^ b)) s := by
  have h1 := Real.rpow_pos_of_pos hs.1 a
  have h2 := Real.rpow_pos_of_pos (by linarith [hs.2] : (0 : ℝ) < 1 - s) b
  refine (contDiffAt_const.mul (fx_p3_rpow_C1 ha).contDiffAt).div
    ((fx_p3_rpow_C1 ha).contDiffAt.add
      ((contDiffAt_const.sub contDiffAt_id).rpow_const_of_ne ?_)) ?_
  · show (1 : ℝ) - s ≠ 0; linarith [hs.2]
  · positivity

/-- In a zero chart, `s ↦ ψ(μ(s) u)` is `C¹` near `c` and has derivative `(ζ' q)⁻¹ (μ'(c) u)` at a
point `c` where `μ c = 0` (a straight chart segment through the zero). -/
theorem fx_p3_ZeroChart.chart_curve {φ ζ : ℂ → ℂ} {q : ℂ} {m : ℕ} {r ρ0 : ℝ}
    (hZ : fx_p3_ZeroChart φ ζ q m r ρ0) {μ : ℝ → ℝ} {c A : ℝ} {u : ℂ}
    (hμc : ContDiffAt ℝ 1 μ c) (hμd : HasDerivAt μ A c) (hμ0 : μ c = 0) :
    ContDiffAt ℝ 1 (fun s => Function.invFunOn ζ (ball q r) ((μ s : ℂ) * u)) c ∧
      HasDerivAt (fun s => Function.invFunOn ζ (ball q r) ((μ s : ℂ) * u))
        ((deriv ζ q)⁻¹ * ((A : ℂ) * u)) c ∧
      Function.invFunOn ζ (ball q r) ((μ c : ℂ) * u) = q := by
  obtain ⟨hopen, hleft, hψ⟩ := hZ.inv
  have hr := hZ.1
  have hζ0 := hZ.2.2.2.1
  have hρB := hZ.2.2.2.2.2.2
  set ψ := Function.invFunOn ζ (ball q r) with hψdef
  have h0V : (0 : ℂ) ∈ ζ '' ball q r := hρB (mem_ball_self hZ.2.1)
  have hψ0 : ψ 0 = q := by
    have := hleft q (mem_ball_self hr)
    rwa [hζ0] at this
  have hℓ0 : (μ c : ℂ) * u = 0 := by rw [hμ0, Complex.ofReal_zero, zero_mul]
  have hψC : ContDiffAt ℂ 1 ψ 0 := by
    have hdiff : DifferentiableOn ℂ ψ (ζ '' ball q r) := fun w hw =>
      (hψ w hw).2.2.differentiableAt.differentiableWithinAt
    exact (hdiff.contDiffOn hopen).contDiffAt (hopen.mem_nhds h0V)
  have hℓC : ContDiffAt ℝ 1 (fun s : ℝ => (μ s : ℂ) * u) c :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp c hμc).mul contDiffAt_const
  have hℓd : HasDerivAt (fun s : ℝ => (μ s : ℂ) * u) ((A : ℂ) * u) c :=
    hμd.ofReal_comp.mul_const u
  refine ⟨?_, ?_, by rw [hℓ0, hψ0]⟩
  · have h := (hψC.restrict_scalars ℝ)
    rw [← hℓ0] at h
    exact h.comp c hℓC
  · have h := (hψ 0 h0V).2.2
    rw [hψ0, ← hℓ0] at h
    exact h.comp c hℓd

/-- **The reparametrized edge near its source.**  If `par = Γ ∘ σ` on `(0, 1)`, `par 0 = q`, and
`σ^κ = μ` with `μ` `C¹` at `0`, `μ 0 = 0`, `μ'(0) = A`, then `par` is `C¹` on `[0, 1)`, a vertical
arc on `(0, 1)`, with one-sided derivative `A u / ζ'(q)` at the source. -/
theorem fx_p3_par_start {φ ζ : ℂ → ℂ} {q u : ℂ} {m : ℕ} {r ρ0 : ℝ}
    (hZ : fx_p3_ZeroChart φ ζ q m r ρ0) {Γ : ℝ → ℂ} {I : Set ℝ} (hI : fx_p3_IsOI I)
    (hI0 : I ⊆ Ioi 0) (hΓ : fx_p3_VT φ Γ I) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hmodel : ∀ t ∈ Ioo 0 t₀, Γ t =
      Function.invFunOn ζ (ball q r) (((t ^ (2 / ((m : ℝ) + 2)) : ℝ) : ℂ) * u))
    {σ : ℝ → ℝ} (hσI : ∀ s ∈ Ioo (0 : ℝ) 1, σ s ∈ I)
    (hσC : ∀ s ∈ Ioo (0 : ℝ) 1, ContDiffAt ℝ 1 σ s)
    (hσd : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ d > 0, HasDerivAt σ d s)
    {μ : ℝ → ℝ} {A : ℝ} (hμc : ContDiffAt ℝ 1 μ 0) (hμd : HasDerivAt μ A 0) (hμ0 : μ 0 = 0)
    (hσμ : ∀ s ∈ Ioo (0 : ℝ) 1, σ s ^ (2 / ((m : ℝ) + 2)) = μ s)
    {par : ℝ → ℂ} (hp0 : par 0 = q) (hp : ∀ s ∈ Ioo (0 : ℝ) 1, par s = Γ (σ s)) :
    ContDiffOn ℝ 1 par (Ico 0 1) ∧ IsVerticalArc φ par 0 1 ∧
      derivWithin par (Icc 0 1) 0 = (A : ℂ) * u * (deriv ζ q)⁻¹ := by
  set κ : ℝ := 2 / ((m : ℝ) + 2) with hκ
  have hκ0 : 0 < κ := by positivity
  obtain ⟨hFC, hFd, hF0⟩ := hZ.chart_curve (u := u) hμc hμd hμ0
  set F : ℝ → ℂ := fun s => Function.invFunOn ζ (ball q r) ((μ s : ℂ) * u) with hF
  -- near `0`, `par = F`
  obtain ⟨s₁, hs₁, hs₁1, hnear⟩ : ∃ s₁ > 0, s₁ ≤ 1 ∧ ∀ s ∈ Ioo 0 s₁, σ s < t₀ := by
    have hμt : ∀ᶠ s in 𝓝 (0 : ℝ), μ s < t₀ ^ κ := by
      have hlt : μ 0 < t₀ ^ κ := by rw [hμ0]; exact Real.rpow_pos_of_pos ht₀ κ
      exact hμc.continuousAt.eventually (Iio_mem_nhds hlt)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hμt
    refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun s hs => ?_⟩
    have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
    have hμs : μ s < t₀ ^ κ := hδ' (by
      rw [Real.dist_eq, sub_zero, abs_of_pos hs.1]; exact lt_of_lt_of_le hs.2 (min_le_left _ _))
    rw [← hσμ s hsI] at hμs
    exact (Real.rpow_lt_rpow_iff (le_of_lt (hI0 (hσI s hsI))) ht₀.le hκ0).1 hμs
  have hpF : ∀ s ∈ Ico 0 s₁, par s = F s := by
    intro s hs
    rcases hs.1.eq_or_lt with h | h
    · subst h; rw [hp0]; exact hF0.symm
    · have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨h, lt_of_lt_of_le hs.2 hs₁1⟩
      rw [hp s hsI, hmodel _ ⟨hI0 (hσI s hsI), hnear s ⟨h, hs.2⟩⟩, hσμ s hsI]
  have hev : ∀ t : Set ℝ, t ⊆ Ici 0 → par =ᶠ[𝓝[t] 0] F := by
    intro t ht
    filter_upwards [inter_mem_nhdsWithin t (Iio_mem_nhds hs₁)] with s hs
    exact hpF s ⟨ht hs.1, hs.2⟩
  have hΓC : ∀ τ ∈ I, ContDiffAt ℝ 1 Γ τ := fun τ hτ => hΓ.1.contDiffAt (hI.1.mem_nhds hτ)
  have hevI : ∀ s ∈ Ioo (0 : ℝ) 1, par =ᶠ[𝓝 s] fun s => Γ (σ s) := by
    intro s hs
    filter_upwards [isOpen_Ioo.mem_nhds hs] with s' hs'
    exact hp s' hs'
  refine ⟨fun s hs => ?_, fun s hs => ?_, ?_⟩
  · rcases hs.1.eq_or_lt with h | h
    · subst h
      exact hFC.contDiffWithinAt.congr_of_eventuallyEq (hev _ fun x hx => hx.1) (by rw [hp0]; exact hF0.symm)
    · have hsI : s ∈ Ioo (0 : ℝ) 1 := ⟨h, hs.2⟩
      have h1 : ContDiffAt ℝ 1 (fun s => Γ (σ s)) s := (hΓC _ (hσI s hsI)).comp s (hσC s hsI)
      exact (h1.congr_of_eventuallyEq (hevI s hsI)).contDiffWithinAt
  · obtain ⟨d, hd, hσds⟩ := hσd s hs
    have h1 : HasDerivAt (fun s => Γ (σ s)) (d • deriv Γ (σ s)) s :=
      (hΓ.hasDerivAt hI.1 (hσI s hs)).scomp s hσds
    have h2 : HasDerivAt par ((d : ℂ) * deriv Γ (σ s)) s := by
      rw [← Complex.real_smul]
      exact h1.congr_of_eventuallyEq (hevI s hs)
    obtain ⟨hmem, hφ0, heq⟩ := hΓ.2 _ (hσI s hs)
    have hval : φ (par s) * ((d : ℂ) * deriv Γ (σ s)) ^ 2 = ((-d ^ 2 : ℝ) : ℂ) := by
      rw [hp s hs, mul_pow, mul_left_comm, heq]
      push_cast
      ring
    refine ⟨h2.differentiableAt, ?_, ?_, ?_, ?_⟩
    · rw [h2.deriv]
      exact mul_ne_zero (Complex.ofReal_ne_zero.2 hd.ne') (hΓ.deriv_ne (hσI s hs))
    · rw [hp s hs]; exact hφ0
    · rw [h2.deriv, hval, Complex.ofReal_im]
    · rw [h2.deriv, hval, Complex.ofReal_re]
      nlinarith
  · have h := (hFd.hasDerivWithinAt (s := Icc 0 1)).congr_of_eventuallyEq
      (hev _ fun x hx => hx.1) (by rw [hp0]; exact hF0.symm)
    rw [h.derivWithin (uniqueDiffOn_Icc zero_lt_one 0 ⟨le_rfl, zero_le_one⟩)]
    ring

/-- **The reparametrized saddle edge near its target.**  If near `L` the trajectory arrives along a
critical ray of the zero chart at `q'` (`Γ t = ψ'((L - t)^κ' u')`), `par = Γ ∘ σ` on `(0, 1)`,
`par 1 = q'`, and `(L - σ)^κ' = ν` with `ν` `C¹` at `1`, `ν 1 = 0`, `ν'(1) = -A'`, then `par` is
`C¹` on `[0, 1]` with one-sided derivative `-A' u' / ζ'(q')` at `1`. -/
theorem fx_p3_par_end {φ ζ' : ℂ → ℂ} {q' u' : ℂ} {m' : ℕ} {r' ρ0' : ℝ}
    (hZ' : fx_p3_ZeroChart φ ζ' q' m' r' ρ0') {Γ : ℝ → ℂ} {L t₁ : ℝ} (ht₁ : t₁ < L)
    (harr : ∀ t ∈ Ioo t₁ L, Γ t =
      Function.invFunOn ζ' (ball q' r') ((((L - t) ^ (2 / ((m' : ℝ) + 2))) : ℝ) * u'))
    {σ : ℝ → ℝ} (hσL : ∀ s ∈ Ioo (0 : ℝ) 1, σ s < L) (hσlim : Tendsto σ (𝓝[<] 1) (𝓝 L))
    {ν : ℝ → ℝ} {A' : ℝ} (hνc : ContDiffAt ℝ 1 ν 1) (hνd : HasDerivAt ν (-A') 1) (hν1 : ν 1 = 0)
    (hσν : ∀ s ∈ Ioo (0 : ℝ) 1, (L - σ s) ^ (2 / ((m' : ℝ) + 2)) = ν s)
    {par : ℝ → ℂ} (hp1 : par 1 = q') (hp : ∀ s ∈ Ioo (0 : ℝ) 1, par s = Γ (σ s))
    (hstart : ContDiffOn ℝ 1 par (Ico 0 1)) :
    ContDiffOn ℝ 1 par (Icc 0 1) ∧
      derivWithin par (Icc 0 1) 1 = -((A' : ℂ) * u' * (deriv ζ' q')⁻¹) := by
  obtain ⟨hGC, hGd, hG1⟩ := hZ'.chart_curve (u := u') hνc hνd hν1
  set G : ℝ → ℂ := fun s => Function.invFunOn ζ' (ball q' r') ((ν s : ℂ) * u') with hG
  -- near `1`, `par = G`
  have hev1 : ∀ᶠ s in 𝓝[<] (1 : ℝ), t₁ < σ s ∧ s ∈ Ioo (0 : ℝ) 1 :=
    (hσlim.eventually (lt_mem_nhds ht₁)).and (Ioo_mem_nhdsLT one_pos)
  obtain ⟨s₂, hs₂, hs₂'⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' (zero_lt_one' ℝ)).1 hev1
  have hpG : ∀ s ∈ Ioc s₂ 1, par s = G s := by
    intro s hs
    rcases hs.2.eq_or_lt with h | h
    · subst h; rw [hp1]; exact hG1.symm
    · obtain ⟨h1, h2⟩ := hs₂' ⟨hs.1, h⟩
      rw [hp s h2, harr _ ⟨h1, hσL s h2⟩, hσν s h2]
  have hev : par =ᶠ[𝓝[Icc 0 1] 1] G := by
    filter_upwards [inter_mem_nhdsWithin (Icc (0 : ℝ) 1) (Ioi_mem_nhds (mem_Iio.1 hs₂))]
      with s hs
    exact hpG s ⟨hs.2, hs.1.2⟩
  refine ⟨fun s hs => ?_, ?_⟩
  · rcases hs.2.eq_or_lt with h | h
    · subst h
      exact hGC.contDiffWithinAt.congr_of_eventuallyEq hev (by rw [hp1]; exact hG1.symm)
    · have h1 := hstart s ⟨hs.1, h⟩
      refine h1.mono_of_mem_nhdsWithin ?_
      filter_upwards [inter_mem_nhdsWithin (Icc (0 : ℝ) 1) (Iio_mem_nhds h)] with x hx
      exact ⟨hx.1.1, hx.2⟩
  · have h := (hGd.hasDerivWithinAt (s := Icc 0 1)).congr_of_eventuallyEq hev (by rw [hp1]; exact hG1.symm)
    rw [h.derivWithin (uniqueDiffOn_Icc zero_lt_one 1 ⟨zero_le_one, le_rfl⟩)]
    push_cast
    ring

/-- **Packaging of a reparametrized ray**: for `par = q` at `0`, `qe` at `1`, and `Γ ∘ σ` on
`(0, 1)`, with `σ` a `C¹` increasing bijection of `(0, 1)` onto `I` and `σ^κ = μ` near the source. -/
theorem fx_p3_pack {φ ζ : ℂ → ℂ} {q u : ℂ} {m : ℕ} {r ρ0 : ℝ}
    (hZ : fx_p3_ZeroChart φ ζ q m r ρ0) (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {Γ : ℝ → ℂ} {I : Set ℝ} (hI : fx_p3_IsOI I)
    (hI0 : I ⊆ Ioi 0) (hΓ : fx_p3_VT φ Γ I) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hmodel : ∀ t ∈ Ioo 0 t₀, Γ t =
      Function.invFunOn ζ (ball q r) (((t ^ (2 / ((m : ℝ) + 2)) : ℝ) : ℂ) * u))
    {σ : ℝ → ℝ} (hσI : ∀ s ∈ Ioo (0 : ℝ) 1, σ s ∈ I)
    (hσC : ∀ s ∈ Ioo (0 : ℝ) 1, ContDiffAt ℝ 1 σ s)
    (hσd : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ d > 0, HasDerivAt σ d s) (hσm : StrictMonoOn σ (Ioo 0 1))
    (hσs : ∀ τ ∈ I, ∃ s ∈ Ioo (0 : ℝ) 1, σ s = τ)
    {μ : ℝ → ℝ} {A : ℝ} (hμc : ContDiffAt ℝ 1 μ 0) (hμd : HasDerivAt μ A 0) (hμ0 : μ 0 = 0)
    (hσμ : ∀ s ∈ Ioo (0 : ℝ) 1, σ s ^ (2 / ((m : ℝ) + 2)) = μ s) (qe : ℂ) {par : ℝ → ℂ}
    (hpar : ∀ s, par s = if s ≤ 0 then q else if 1 ≤ s then qe else Γ (σ s)) :
    par 0 = q ∧ par 1 = qe ∧ (∀ s ∈ Ioo (0 : ℝ) 1, par s = Γ (σ s)) ∧
      par '' Ioo 0 1 = Γ '' I ∧ InjOn par (Ioo 0 1) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, ∃ τ ∈ I, par s = Γ τ) ∧
      ContDiffOn ℝ 1 par (Ico 0 1) ∧ IsVerticalArc φ par 0 1 ∧
      derivWithin par (Icc 0 1) 0 = (A : ℂ) * u * (deriv ζ q)⁻¹ := by
  have hp0 : par 0 = q := by rw [hpar]; simp
  have hp1 : par 1 = qe := by rw [hpar]; simp
  have hp : ∀ s ∈ Ioo (0 : ℝ) 1, par s = Γ (σ s) := by
    intro s hs
    rw [hpar, ite_eq_right (not_le.2 hs.1), ite_eq_right (not_le.2 hs.2)]
  have hΓinj : InjOn Γ I := hΓ.injOn hφ hne hI
  obtain ⟨hC, hV, hD⟩ := fx_p3_par_start hZ hI hI0 hΓ ht₀ hmodel hσI hσC hσd hμc hμd hμ0 hσμ
    hp0 hp
  refine ⟨hp0, hp1, hp, ?_, ?_, fun s hs => ⟨σ s, hσI s hs, hp s hs⟩, hC, hV, hD⟩
  · apply Subset.antisymm
    · rintro _ ⟨s, hs, rfl⟩
      exact ⟨σ s, hσI s hs, (hp s hs).symm⟩
    · rintro _ ⟨τ, hτ, rfl⟩
      obtain ⟨s, hs, rfl⟩ := hσs τ hτ
      exact ⟨s, hs, hp s hs⟩
  · intro s hs s' hs' h
    rw [hp s hs, hp s' hs'] at h
    exact hσm.injOn hs hs' (hΓinj (hσI s hs) (hσI s' hs') h)

/-- **The critical vertical ray** leaving a zero `q` in the critical direction `u` (for chosen zero
charts `ζZ q`): the maximal unit-speed trajectory `Γ` on `I = (0, L)` or `(0, ∞)` starting as the model
ray `ψ_q(t^κ u)`, its `C¹` reparametrization `par` on `[0, 1)` (with nonzero one-sided tangent
`A u / ζ'(q)` at the source), and the end dichotomy: it leaves every compact subset of `Δ`, or it is
a saddle connection arriving at a zero `qe` along the critical direction `ue`, `C¹` on `[0, 1]`. -/
theorem fx_p3_ray {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) (mZ : ℂ → ℕ) (ζZ : ℂ → ℂ → ℂ) (rZ ρZ : ℂ → ℝ)
    (hZ : ∀ q, q ∈ unitDisc → φ q = 0 →
      0 < mZ q ∧ fx_p3_ZeroChart φ (ζZ q) q (mZ q) (rZ q) (ρZ q))
    {q u : ℂ} (hq : q ∈ unitDisc) (hq0 : φ q = 0) (hu : u ^ (mZ q + 2) = -1) :
    ∃ (Γ : ℝ → ℂ) (I : Set ℝ) (l : Filter ℝ) (t₀ : ℝ) (par : ℝ → ℂ) (qe ue : ℂ) (L t₁ A : ℝ),
      fx_p3_IsOI I ∧ I ⊆ Ioi 0 ∧ fx_p3_VT φ Γ I ∧ 0 < t₀ ∧ Ioo 0 t₀ ⊆ I ∧
      (∀ t ∈ Ioo 0 t₀, Γ t = Function.invFunOn (ζZ q) (ball q (rZ q))
        (((t ^ (2 / ((mZ q : ℝ) + 2)) : ℝ) : ℂ) * u)) ∧
      ((0 < L ∧ I = Ioo 0 L ∧ l = 𝓝[<] L) ∨ (I = Ioi 0 ∧ l = atTop)) ∧
      par 0 = q ∧ par '' Ioo 0 1 = Γ '' I ∧ InjOn par (Ioo 0 1) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, ∃ τ ∈ I, par s = Γ τ) ∧
      ContDiffOn ℝ 1 par (Ico 0 1) ∧ IsVerticalArc φ par 0 1 ∧ 0 < A ∧
      derivWithin par (Icc 0 1) 0 = (A : ℂ) * u * (deriv (ζZ q) q)⁻¹ ∧
      (((∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc → ∀ᶠ t in l, Γ t ∉ K) ∧
          (∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc → ∀ᶠ s in 𝓝[<] (1 : ℝ), par s ∉ K)) ∨
        (0 < L ∧ I = Ioo 0 L ∧ l = 𝓝[<] L ∧ qe ∈ unitDisc ∧ φ qe = 0 ∧
          ue ^ (mZ qe + 2) = -1 ∧ t₁ ∈ Ioo 0 L ∧
          (∀ t ∈ Ioo t₁ L, Γ t = Function.invFunOn (ζZ qe) (ball qe (rZ qe))
            ((((L - t) ^ (2 / ((mZ qe : ℝ) + 2))) : ℝ) * ue)) ∧
          par 1 = qe ∧ ContDiffOn ℝ 1 par (Icc 0 1) ∧
          ∃ A' : ℝ, 0 < A' ∧ derivWithin par (Icc 0 1) 1 = -((A' : ℂ) * ue * (deriv (ζZ qe) qe)⁻¹))) := by
  classical
  have hφD : DifferentiableOn ℂ φ unitDisc := hφ.mono (ball_subset_ball hρ.le)
  obtain ⟨hm, hZq⟩ := hZ q hq hq0
  set m := mZ q with hmdef
  set κ : ℝ := 2 / ((m : ℝ) + 2) with hκ
  set a : ℝ := ((m : ℝ) + 2) / 2 with ha
  have ha1 : 1 ≤ a := by rw [ha]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
  have haκ : a * κ = 1 := by
    rw [ha, hκ]; have : ((m : ℝ) + 2) ≠ 0 := by positivity
    field_simp
  set t₀ : ℝ := ρZ q ^ (((m : ℝ) + 2) / 2) with ht₀
  have ht₀0 : 0 < t₀ := Real.rpow_pos_of_pos hZq.2.1 _
  have hM := hZq.model hu
  set M : ℝ → ℂ := fun t : ℝ => Function.invFunOn (ζZ q) (ball q (rZ q))
    (((t ^ (2 / ((m : ℝ) + 2)) : ℝ) : ℂ) * u) with hMdef
  obtain ⟨Γ, hΓM, hcase⟩ := fx_p3_maxTraj hφD ht₀0 hM
  have hdich := fx_p3_ray_dichotomy hρ hφ hne ht₀0 hΓM hcase
  have hmodel : ∀ t ∈ Ioo 0 t₀, Γ t = Function.invFunOn (ζZ q) (ball q (rZ q))
      (((t ^ (2 / ((m : ℝ) + 2)) : ℝ) : ℂ) * u) := fun t ht => hΓM ht
  rcases hdich with ⟨L, hL, hΓL, hend⟩ | ⟨hΓI, hK⟩
  · have hL0 : 0 < L := ht₀0.trans_le hL
    have hI0 : Ioo (0 : ℝ) L ⊆ Ioi 0 := fun t ht => ht.1
    have hsub : Ioo 0 t₀ ⊆ Ioo 0 L := Ioo_subset_Ioo_right hL
    rcases hend with hK | ⟨q', hq', hq'0, hT⟩
    · -- a bounded boundary ray
      obtain ⟨hσI, hσd, hσm, hσs, hσlim, hσμ, -, hgC0, hg0, -, -⟩ :=
        fx_p3_sigma_fin (a := a) (b := 1) (κ := κ) (κ' := 1) (L := L) ha1 le_rfl haκ
          (by norm_num) hL0
      obtain ⟨hμc, hμd⟩ := fx_p3_endfun0 hgC0 hg0 (L ^ κ) κ
      obtain ⟨hp0, -, hp, himg, hinj, hpτ, hC, hV, hD⟩ := fx_p3_pack hZq hφD hne
        (fx_p3_isOI_Ioo 0 L) hI0 hΓL ht₀0 hmodel hσI (fun s hs => fx_p3_sigma_fin_C1 ha1 hs) hσd
        hσm hσs hμc hμd (by simp) hσμ q (par := fun s => if s ≤ 0 then q else if 1 ≤ s then q
          else Γ (L * s ^ a / (s ^ a + (1 - s) ^ (1 : ℝ)))) (fun s => rfl)
      refine ⟨Γ, Ioo 0 L, 𝓝[<] L, t₀, _, q, 0, L, 0, L ^ κ, fx_p3_isOI_Ioo 0 L, hI0, hΓL, ht₀0,
        hsub, hmodel, Or.inl ⟨hL0, rfl, rfl⟩, hp0, himg, hinj, hpτ, hC, hV,
        Real.rpow_pos_of_pos hL0 κ, hD, Or.inl ⟨hK, ?_⟩⟩
      intro K hKc hKD
      filter_upwards [hσlim.eventually (hK K hKc hKD), Ioo_mem_nhdsLT one_pos] with s hs1 hs2
      rw [hp s hs2]
      exact hs1
    · -- a saddle connection
      obtain ⟨hm', hZq'⟩ := hZ q' hq' hq'0
      obtain ⟨u', hu', t₁, ht₁, harr⟩ := hZq'.arrival_Ioo hm' hL0 hΓL hT
      set a' : ℝ := ((mZ q' : ℝ) + 2) / 2 with ha'
      set κ' : ℝ := 2 / ((mZ q' : ℝ) + 2) with hκ'
      have ha'1 : 1 ≤ a' := by
        rw [ha']; have : (0 : ℝ) ≤ mZ q' := Nat.cast_nonneg _; linarith
      have ha'κ' : a' * κ' = 1 := by
        rw [ha', hκ']; have : ((mZ q' : ℝ) + 2) ≠ 0 := by positivity
        field_simp
      obtain ⟨hσI, hσd, hσm, hσs, hσlim, hσμ, hσν, hgC0, hg0, hgC1, hg1⟩ :=
        fx_p3_sigma_fin (L := L) ha1 ha'1 haκ ha'κ' hL0
      obtain ⟨hμc, hμd⟩ := fx_p3_endfun0 hgC0 hg0 (L ^ κ) κ
      obtain ⟨hνc, hνd⟩ := fx_p3_endfun1 hgC1 hg1 (L ^ κ') κ'
      obtain ⟨hp0, hp1, hp, himg, hinj, hpτ, hC, hV, hD⟩ := fx_p3_pack hZq hφD hne
        (fx_p3_isOI_Ioo 0 L) hI0 hΓL ht₀0 hmodel hσI (fun s hs => fx_p3_sigma_fin_C1 ha1 hs) hσd
        hσm hσs hμc hμd (by simp) hσμ q' (par := fun s => if s ≤ 0 then q else if 1 ≤ s then q'
          else Γ (L * s ^ a / (s ^ a + (1 - s) ^ a'))) (fun s => rfl)
      obtain ⟨hCI, hD1⟩ := fx_p3_par_end hZq' ht₁.2 harr (fun s hs => (hσI s hs).2)
        (hσlim.mono_right nhdsWithin_le_nhds) hνc hνd (by simp) hσν hp1 hp hC
      exact ⟨Γ, Ioo 0 L, 𝓝[<] L, t₀, _, q', u', L, t₁, L ^ κ, fx_p3_isOI_Ioo 0 L, hI0, hΓL, ht₀0,
        hsub, hmodel, Or.inl ⟨hL0, rfl, rfl⟩, hp0, himg, hinj, hpτ, hC, hV,
        Real.rpow_pos_of_pos hL0 κ, hD, Or.inr ⟨hL0, rfl, rfl, hq', hq'0, hu', ht₁, harr, hp1, hCI,
          L ^ κ', Real.rpow_pos_of_pos hL0 κ', hD1⟩⟩
  · -- an unbounded boundary ray
    obtain ⟨hσpos, hσd, hσm, hσs, hσlim, hσμ, hgC0, hg0⟩ := fx_p3_sigma_inf ha1 haκ
    obtain ⟨hμc, hμd⟩ := fx_p3_endfun0 hgC0 hg0 1 κ
    have hI0 : Ioi (0 : ℝ) ⊆ Ioi 0 := subset_rfl
    obtain ⟨hp0, -, hp, himg, hinj, hpτ, hC, hV, hD⟩ := fx_p3_pack hZq hφD hne
      (fx_p3_isOI_Ioi 0) hI0 hΓI ht₀0 hmodel (fun s hs => hσpos s hs)
      (fun s hs => fx_p3_sigma_inf_C1 hs) hσd hσm (fun τ hτ => hσs τ hτ) hμc hμd (by simp) hσμ q
      (par := fun s => if s ≤ 0 then q else if 1 ≤ s then q else Γ (s ^ a / (1 - s)))
      (fun s => rfl)
    refine ⟨Γ, Ioi 0, atTop, t₀, _, q, 0, 0, 0, 1, fx_p3_isOI_Ioi 0, hI0, hΓI, ht₀0,
      fun t ht => ht.1, hmodel, Or.inr ⟨rfl, rfl⟩, hp0, himg, hinj, hpτ, hC, hV, one_pos, ?_,
      Or.inl ⟨hK, ?_⟩⟩
    · rw [hD]
    · intro K hKc hKD
      filter_upwards [hσlim.eventually (hK K hKc hKD), Ioo_mem_nhdsLT one_pos] with s hs1 hs2
      rw [hp s hs2]
      exact hs1

/-- The model ray converges to the zero: `ψ(t^κ u) → q` as `t → 0⁺`. -/
theorem fx_p3_ZeroChart.model_tendsto {φ ζ : ℂ → ℂ} {q : ℂ} {m : ℕ} {r ρ0 : ℝ}
    (hZ : fx_p3_ZeroChart φ ζ q m r ρ0) (u : ℂ) :
    Tendsto (fun t : ℝ => Function.invFunOn ζ (ball q r)
      (((t ^ (2 / ((m : ℝ) + 2)) : ℝ) : ℂ) * u)) (𝓝[>] 0) (𝓝 q) := by
  obtain ⟨hopen, hleft, hψ⟩ := hZ.inv
  have hr := hZ.1
  have hζ0 := hZ.2.2.2.1
  have h0V : (0 : ℂ) ∈ ζ '' ball q r := hZ.2.2.2.2.2.2 (mem_ball_self hZ.2.1)
  have hψ0 : Function.invFunOn ζ (ball q r) 0 = q := by
    have := hleft q (mem_ball_self hr)
    rwa [hζ0] at this
  have hψc : ContinuousAt (Function.invFunOn ζ (ball q r)) 0 := (hψ 0 h0V).2.2.continuousAt
  have hκ : 0 < 2 / ((m : ℝ) + 2) := by positivity
  have h1 : Tendsto (fun t : ℝ => (((t ^ (2 / ((m : ℝ) + 2)) : ℝ) : ℂ) * u)) (𝓝[>] 0)
      (𝓝 0) := by
    have h2 : Tendsto (fun t : ℝ => t ^ (2 / ((m : ℝ) + 2))) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 _ (Or.inr hκ.le)).tendsto
      rw [Real.zero_rpow hκ.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h3 := (Complex.continuous_ofReal.tendsto 0).comp h2
    rw [Complex.ofReal_zero] at h3
    simpa using h3.mul_const u
  have := hψc.tendsto.comp h1
  rwa [hψ0] at this

/-- Two critical directions giving the same model ray near the zero are equal. -/
theorem fx_p3_ZeroChart.dir_unique {φ ζ : ℂ → ℂ} {q : ℂ} {m : ℕ} {r ρ0 : ℝ}
    (hZ : fx_p3_ZeroChart φ ζ q m r ρ0) {u u' : ℂ} (hu : u ^ (m + 2) = -1)
    (hu' : u' ^ (m + 2) = -1) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ t ∈ Ioo (0 : ℝ) ε, Function.invFunOn ζ (ball q r)
      (((t ^ (2 / ((m : ℝ) + 2)) : ℝ) : ℂ) * u) =
      Function.invFunOn ζ (ball q r) (((t ^ (2 / ((m : ℝ) + 2)) : ℝ) : ℂ) * u')) : u = u' := by
  obtain ⟨-, -, hψ⟩ := hZ.inv
  have hρB := hZ.2.2.2.2.2.2
  have hρ0 := hZ.2.1
  set κ : ℝ := 2 / ((m : ℝ) + 2) with hκ
  have hκ0 : 0 < κ := by positivity
  -- a small positive time with `t^κ < ρ0`
  obtain ⟨t, ht, htκ⟩ : ∃ t ∈ Ioo (0 : ℝ) ε, t ^ κ < ρ0 := by
    have h2 : Tendsto (fun t : ℝ => t ^ κ) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 _ (Or.inr hκ0.le)).tendsto
      rw [Real.zero_rpow hκ0.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    obtain ⟨t, h1, h2⟩ := ((h2.eventually (gt_mem_nhds hρ0)).and (Ioo_mem_nhdsGT hε)).exists
    exact ⟨t, h2, h1⟩
  have hmem : ∀ v : ℂ, v ^ (m + 2) = -1 → (((t ^ κ : ℝ)) : ℂ) * v ∈ ζ '' ball q r := by
    intro v hv
    apply hρB
    rw [mem_ball_zero_iff, norm_mul, fx_p3_root_norm hv, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    exact htκ
  have h1 := congr_arg ζ (h t ht)
  rw [(hψ _ (hmem u hu)).2.1, (hψ _ (hmem u' hu')).2.1] at h1
  have hne : (((t ^ κ : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos ht.1 _).ne'
  exact mul_left_cancel₀ hne h1

/-- Unit-speed data of the critical ray from `q` in the direction `u` (for chosen zero charts): a
trajectory on `I = (0, L)` or `(0, ∞)` (tail filter `l`) starting as the model ray. -/
def fx_p3_URay (φ : ℂ → ℂ) (mZ : ℂ → ℕ) (ζZ : ℂ → ℂ → ℂ) (rZ : ℂ → ℝ) (q u : ℂ)
    (Γ : ℝ → ℂ) (I : Set ℝ) (l : Filter ℝ) (t₀ L : ℝ) : Prop :=
  fx_p3_IsOI I ∧ I ⊆ Ioi 0 ∧ fx_p3_VT φ Γ I ∧ 0 < t₀ ∧ Ioo 0 t₀ ⊆ I ∧
    (∀ t ∈ Ioo 0 t₀, Γ t = Function.invFunOn (ζZ q) (ball q (rZ q))
      (((t ^ (2 / ((mZ q : ℝ) + 2)) : ℝ) : ℂ) * u)) ∧
    ((0 < L ∧ I = Ioo 0 L ∧ l = 𝓝[<] L) ∨ (I = Ioi 0 ∧ l = atTop))

/-- The saddle end of a ray (unit-speed form): it lives on `(0, L)` and arrives at the zero `qe`
along the critical direction `ue`. -/
def fx_p3_USad (φ : ℂ → ℂ) (mZ : ℂ → ℕ) (ζZ : ℂ → ℂ → ℂ) (rZ : ℂ → ℝ) (Γ : ℝ → ℂ)
    (I : Set ℝ) (l : Filter ℝ) (qe ue : ℂ) (L t₁ : ℝ) : Prop :=
  0 < L ∧ I = Ioo 0 L ∧ l = 𝓝[<] L ∧ qe ∈ unitDisc ∧ φ qe = 0 ∧ ue ^ (mZ qe + 2) = -1 ∧
    t₁ ∈ Ioo 0 L ∧ ∀ t ∈ Ioo t₁ L, Γ t = Function.invFunOn (ζZ qe) (ball qe (rZ qe))
      ((((L - t) ^ (2 / ((mZ qe : ℝ) + 2))) : ℝ) * ue)

/-- The boundary end of a ray (unit-speed form): it leaves every compact subset of `Δ`. -/
def fx_p3_UBd (Γ : ℝ → ℂ) (l : Filter ℝ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc → ∀ᶠ t in l, Γ t ∉ K

/-- A path leaving every compact subset of `Δ` has no limit in `Δ`. -/
theorem fx_p3_bd_no_limit {Γ : ℝ → ℂ} {l : Filter ℝ} [l.NeBot] (hbd : fx_p3_UBd Γ l) {z : ℂ}
    (hz : z ∈ unitDisc) : ¬ Tendsto Γ l (𝓝 z) := by
  intro hT
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 isOpen_ball z hz
  have hK : closedBall z (ε / 2) ⊆ unitDisc :=
    (closedBall_subset_ball (by linarith)).trans hεD
  have h1 := hbd _ (isCompact_closedBall z (ε / 2)) hK
  have h2 : ∀ᶠ t in l, Γ t ∈ closedBall z (ε / 2) :=
    hT (closedBall_mem_nhds z (by positivity))
  obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
  exact ht1 ht2

/-- `s ↦ a + s` sends `(-a, ·)` to `(0, ·)`. -/
theorem fx_p3_tendsto_add_nhdsGT (a : ℝ) :
    Tendsto (fun s : ℝ => a + s) (𝓝[>] (-a)) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun s : ℝ => a + s) (𝓝 (-a)) (𝓝 (a + -a)) :=
      tendsto_const_nhds.add tendsto_id
    rw [add_neg_cancel] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    show 0 < a + s
    have : -a < s := hs
    linarith

/-- `s ↦ b - s` sends `(·, b)` to `(0, ·)`. -/
theorem fx_p3_tendsto_sub_nhdsLT (b : ℝ) :
    Tendsto (fun s : ℝ => b - s) (𝓝[<] b) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun s : ℝ => b - s) (𝓝 b) (𝓝 (b - b)) :=
      tendsto_const_nhds.sub tendsto_id
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    show 0 < b - s
    have : s < b := hs
    linarith

/-- `τ ↦ τ - a` sends `(·, L)` to `(·, L - a)`. -/
theorem fx_p3_tendsto_sub_right_nhdsLT (L a : ℝ) :
    Tendsto (fun τ : ℝ => τ - a) (𝓝[<] L) (𝓝[<] (L - a)) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun τ : ℝ => τ - a) (𝓝 L) (𝓝 (L - a)) :=
      tendsto_id.sub tendsto_const_nhds
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    show s - a < L - a
    have : s < L := hs
    linarith

/-- A ray converges to its source zero at `t → 0⁺`. -/
theorem fx_p3_URay.tendsto0 {φ : ℂ → ℂ} {mZ : ℂ → ℕ} {ζZ : ℂ → ℂ → ℂ} {rZ ρZ : ℂ → ℝ}
    {q u : ℂ} {Γ : ℝ → ℂ} {I : Set ℝ} {l : Filter ℝ} {t₀ L : ℝ}
    (hx : fx_p3_URay φ mZ ζZ rZ q u Γ I l t₀ L)
    (hZq : fx_p3_ZeroChart φ (ζZ q) q (mZ q) (rZ q) (ρZ q)) :
    Tendsto Γ (𝓝[>] 0) (𝓝 q) := by
  obtain ⟨-, -, -, ht₀, -, hmodel, -⟩ := hx
  refine (hZq.model_tendsto u).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht
  exact (hmodel t ht).symm

/-- A saddle ray converges to its target zero at `t → L⁻`. -/
theorem fx_p3_USad.tendsto {φ : ℂ → ℂ} {mZ : ℂ → ℕ} {ζZ : ℂ → ℂ → ℂ} {rZ ρZ : ℂ → ℝ}
    {Γ : ℝ → ℂ} {I : Set ℝ} {l : Filter ℝ} {qe ue : ℂ} {L t₁ : ℝ}
    (hs : fx_p3_USad φ mZ ζZ rZ Γ I l qe ue L t₁)
    (hZqe : fx_p3_ZeroChart φ (ζZ qe) qe (mZ qe) (rZ qe) (ρZ qe)) :
    Tendsto Γ (𝓝[<] L) (𝓝 qe) := by
  obtain ⟨-, -, -, -, -, -, ht₁, harr⟩ := hs
  have h := (hZqe.model_tendsto ue).comp (fx_p3_tendsto_sub_nhdsLT L)
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ht₁.2] with t ht
  exact (harr t ht).symm

/-- A saddle ray does not leave every compact subset. -/
theorem fx_p3_USad.not_bd {φ : ℂ → ℂ} {mZ : ℂ → ℕ} {ζZ : ℂ → ℂ → ℂ} {rZ ρZ : ℂ → ℝ}
    {Γ : ℝ → ℂ} {I : Set ℝ} {l : Filter ℝ} {qe ue : ℂ} {L t₁ : ℝ}
    (hs : fx_p3_USad φ mZ ζZ rZ Γ I l qe ue L t₁)
    (hZqe : fx_p3_ZeroChart φ (ζZ qe) qe (mZ qe) (rZ qe) (ρZ qe)) : ¬ fx_p3_UBd Γ l := by
  intro hbd
  have hl : l = 𝓝[<] L := hs.2.2.1
  subst hl
  exact fx_p3_bd_no_limit hbd hs.2.2.2.1 (hs.tendsto hZqe)

/-- A point of a ray's parameter interval: every smaller positive time is also in it. -/
theorem fx_p3_URay.mem_of_le {φ : ℂ → ℂ} {mZ : ℂ → ℕ} {ζZ : ℂ → ℂ → ℂ} {rZ : ℂ → ℝ}
    {q u : ℂ} {Γ : ℝ → ℂ} {I : Set ℝ} {l : Filter ℝ} {t₀ L : ℝ}
    (hx : fx_p3_URay φ mZ ζZ rZ q u Γ I l t₀ L) {t s : ℝ} (ht : t ∈ I) (hs : 0 < s)
    (hst : s ≤ t) : s ∈ I := by
  rcases hx.2.2.2.2.2.2 with ⟨-, hI, -⟩ | ⟨hI, -⟩
  · rw [hI] at ht ⊢; exact ⟨hs, lt_of_le_of_lt hst ht.2⟩
  · rw [hI]; exact hs

/-- The shape of a ray's parameter interval when a given positive time is not in it. -/
theorem fx_p3_URay.bounded_of_not_mem {φ : ℂ → ℂ} {mZ : ℂ → ℕ} {ζZ : ℂ → ℂ → ℂ} {rZ : ℂ → ℝ}
    {q u : ℂ} {Γ : ℝ → ℂ} {I : Set ℝ} {l : Filter ℝ} {t₀ L : ℝ}
    (hx : fx_p3_URay φ mZ ζZ rZ q u Γ I l t₀ L) {T : ℝ} (hT : 0 < T) (hTI : T ∉ I) :
    0 < L ∧ I = Ioo 0 L ∧ l = 𝓝[<] L ∧ L ≤ T := by
  rcases hx.2.2.2.2.2.2 with ⟨hL, hI, hl⟩ | ⟨hI, -⟩
  · refine ⟨hL, hI, hl, ?_⟩
    by_contra h
    exact hTI (hI ▸ ⟨hT, not_le.1 h⟩)
  · exact absurd (hI ▸ (hT : T ∈ Ioi 0)) hTI

/-- **The times agree for rays meeting with equal velocities** (auxiliary). -/
theorem fx_p3_meet_aux {φ : ℂ → ℂ} {a b : ℝ} {Γa Γb : ℝ → ℂ} {Ia Ib : Set ℝ} {qa : ℂ}
    (ha0 : 0 < a) (hab : a < b) (hIa : ∀ s, 0 < s → s ≤ a → s ∈ Ia)
    (hIb : ∀ s, 0 < s → s ≤ b → s ∈ Ib) (hla : Tendsto Γa (𝓝[>] 0) (𝓝 qa))
    (hcb : ∀ τ ∈ Ib, ContinuousAt Γb τ) (hrb : ∀ τ ∈ Ib, φ (Γb τ) ≠ 0) (hqa : φ qa = 0)
    (hU : ∀ s, a + s ∈ Ia → b + s ∈ Ib → Γa (a + s) = Γb (b + s)) : False := by
  have hba : b - a ∈ Ib := hIb _ (by linarith) (by linarith)
  have h1 : Tendsto (fun s => Γa (a + s)) (𝓝[>] (-a)) (𝓝 qa) :=
    hla.comp (fx_p3_tendsto_add_nhdsGT a)
  have h2 : Tendsto (fun s => Γb (b + s)) (𝓝[>] (-a)) (𝓝 (Γb (b - a))) := by
    have h3 : Tendsto (fun s : ℝ => b + s) (𝓝 (-a)) (𝓝 (b + -a)) :=
      tendsto_const_nhds.add tendsto_id
    rw [← sub_eq_add_neg] at h3
    exact ((hcb _ hba).tendsto.comp h3).mono_left nhdsWithin_le_nhds
  have heq : (fun s => Γa (a + s)) =ᶠ[𝓝[>] (-a)] fun s => Γb (b + s) := by
    filter_upwards [Ioo_mem_nhdsGT (show -a < 0 by linarith)] with s hs
    exact hU s (hIa _ (by linarith [hs.1]) (by linarith [hs.2]))
      (hIb _ (by linarith [hs.1]) (by linarith [hs.2]))
  have := tendsto_nhds_unique (h1.congr' heq) h2
  exact hrb _ hba (this ▸ hqa)

/-- **Retracing rays end where the other starts** (auxiliary): if `Γa(a + s) = Γb(b - s)` and
`a + b` lies in `Ia`, the second ray would reach a regular point at its source time `0`. -/
theorem fx_p3_meet_aux2 {φ : ℂ → ℂ} {a b : ℝ} {Γa Γb : ℝ → ℂ} {Ia Ib : Set ℝ} {qb : ℂ}
    (hb0 : 0 < b) (hIa : Ia.OrdConnected) (haI : a ∈ Ia) (habI : a + b ∈ Ia)
    (hIb : ∀ s, 0 < s → s ≤ b → s ∈ Ib) (hlb : Tendsto Γb (𝓝[>] 0) (𝓝 qb))
    (hca : ∀ τ ∈ Ia, ContinuousAt Γa τ) (hra : ∀ τ ∈ Ia, φ (Γa τ) ≠ 0) (hqb : φ qb = 0)
    (hU : ∀ s, a + s ∈ Ia → b - s ∈ Ib → Γa (a + s) = Γb (b - s)) : False := by
  have h1 : Tendsto (fun s => Γb (b - s)) (𝓝[<] b) (𝓝 qb) :=
    hlb.comp (fx_p3_tendsto_sub_nhdsLT b)
  have h2 : Tendsto (fun s => Γa (a + s)) (𝓝[<] b) (𝓝 (Γa (a + b))) := by
    have h3 : Tendsto (fun s : ℝ => a + s) (𝓝 b) (𝓝 (a + b)) :=
      tendsto_const_nhds.add tendsto_id
    exact ((hca _ habI).tendsto.comp h3).mono_left nhdsWithin_le_nhds
  have heq : (fun s => Γa (a + s)) =ᶠ[𝓝[<] b] fun s => Γb (b - s) := by
    filter_upwards [Ioo_mem_nhdsLT hb0] with s hs
    exact hU s (hIa.out haI habI ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (hIb _ (by linarith [hs.2]) (by linarith [hs.1]))
  have := tendsto_nhds_unique (h2.congr' heq) h1
  exact hra _ habI (this ▸ hqb)

/-- **Retracing rays have matching lengths** (auxiliary): if `Γa(a + s) = Γb(b - s)`, `Γa` lives on
`(0, La)` with `La ≤ a + b` and has no regular limit in `Δ` at `La`, then `La = a + b`. -/
theorem fx_p3_meet_aux3 {φ : ℂ → ℂ} {a b La : ℝ} {Γa Γb : ℝ → ℂ} {Ib : Set ℝ}
    (haI : a ∈ Ioo 0 La) (hLa : La ≤ a + b)
    (hIb : ∀ s, 0 < s → s ≤ b → s ∈ Ib)
    (hcb : ∀ τ ∈ Ib, ContinuousAt Γb τ) (hrb : ∀ τ ∈ Ib, φ (Γb τ) ≠ 0)
    (hDb : ∀ τ ∈ Ib, Γb τ ∈ unitDisc)
    (hend : ∀ w ∈ unitDisc, φ w ≠ 0 → ¬ Tendsto Γa (𝓝[<] La) (𝓝 w))
    (hU : ∀ s, a + s ∈ Ioo 0 La → b - s ∈ Ib → Γa (a + s) = Γb (b - s)) : La = a + b := by
  by_contra hne
  have hlt : La < a + b := lt_of_le_of_ne hLa hne
  set s₀ := La - a with hs₀
  have hs₀0 : 0 < s₀ := by linarith [haI.2]
  have hw : b - s₀ ∈ Ib := hIb _ (by linarith) (by linarith)
  have h1 : Tendsto (fun s => Γb (b - s)) (𝓝[<] s₀) (𝓝 (Γb (b - s₀))) := by
    have h3 : Tendsto (fun s : ℝ => b - s) (𝓝 s₀) (𝓝 (b - s₀)) :=
      tendsto_const_nhds.sub tendsto_id
    exact ((hcb _ hw).tendsto.comp h3).mono_left nhdsWithin_le_nhds
  have heq : (fun s => Γa (a + s)) =ᶠ[𝓝[<] s₀] fun s => Γb (b - s) := by
    filter_upwards [Ioo_mem_nhdsLT hs₀0] with s hs
    exact hU s ⟨by linarith [haI.1, hs.1], by linarith [hs.2]⟩
      (hIb _ (by linarith [hs.2]) (by linarith [hs.1]))
  have h2 : Tendsto (fun s => Γa (a + s)) (𝓝[<] s₀) (𝓝 (Γb (b - s₀))) := h1.congr' heq.symm
  have h3 : Tendsto Γa (𝓝[<] La) (𝓝 (Γb (b - s₀))) := by
    have h4 := h2.comp (fx_p3_tendsto_sub_right_nhdsLT La a)
    refine h4.congr fun τ => ?_
    simp only [Function.comp]
    rw [add_sub_cancel]
  exact hend _ (hDb _ hw) (hrb _ hw) h3

/-- **Meeting of two critical rays.**  If two critical rays share an interior point, either they are
the same ray (same zero and direction, same time), or they are the two listings of one saddle
connection (each arrives at the other's source along the other's initial direction). -/
theorem fx_p3_meet {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    {mZ : ℂ → ℕ} {ζZ : ℂ → ℂ → ℂ} {rZ ρZ : ℂ → ℝ}
    (hZ : ∀ q, q ∈ unitDisc → φ q = 0 →
      0 < mZ q ∧ fx_p3_ZeroChart φ (ζZ q) q (mZ q) (rZ q) (ρZ q))
    {q u : ℂ} {Γ : ℝ → ℂ} {I : Set ℝ} {l : Filter ℝ} {t₀ L : ℝ} {qe ue : ℂ} {t₁ : ℝ}
    (hx : fx_p3_URay φ mZ ζZ rZ q u Γ I l t₀ L) (hq : q ∈ unitDisc) (hq0 : φ q = 0)
    (hu : u ^ (mZ q + 2) = -1)
    (hxe : fx_p3_UBd Γ l ∨ fx_p3_USad φ mZ ζZ rZ Γ I l qe ue L t₁)
    {q₂ u₂ : ℂ} {Γ₂ : ℝ → ℂ} {I₂ : Set ℝ} {l₂ : Filter ℝ} {t₀₂ L₂ : ℝ} {qe₂ ue₂ : ℂ} {t₁₂ : ℝ}
    (hy : fx_p3_URay φ mZ ζZ rZ q₂ u₂ Γ₂ I₂ l₂ t₀₂ L₂) (hq₂ : q₂ ∈ unitDisc) (hq₂0 : φ q₂ = 0)
    (hu₂ : u₂ ^ (mZ q₂ + 2) = -1)
    (hye : fx_p3_UBd Γ₂ l₂ ∨ fx_p3_USad φ mZ ζZ rZ Γ₂ I₂ l₂ qe₂ ue₂ L₂ t₁₂)
    {t t₂ : ℝ} (ht : t ∈ I) (ht₂ : t₂ ∈ I₂) (hmeet : Γ t = Γ₂ t₂) :
    (q = q₂ ∧ u = u₂ ∧ t = t₂) ∨
      (fx_p3_USad φ mZ ζZ rZ Γ I l qe ue L t₁ ∧ fx_p3_USad φ mZ ζZ rZ Γ₂ I₂ l₂ qe₂ ue₂ L₂ t₁₂ ∧
        qe = q₂ ∧ qe₂ = q ∧ ue = u₂ ∧ ue₂ = u ∧ L₂ = L ∧ t₂ = L - t) := by
  have hx' := hx
  have hy' := hy
  obtain ⟨hIx, hI0x, hΓx, ht₀x, hsubx, hmodx, hshx⟩ := hx'
  obtain ⟨hIy, hI0y, hΓy, ht₀y, hsuby, hmody, hshy⟩ := hy'
  obtain ⟨hm, hZq⟩ := hZ q hq hq0
  obtain ⟨hm₂, hZq₂⟩ := hZ q₂ hq₂ hq₂0
  have hlim0x : Tendsto Γ (𝓝[>] 0) (𝓝 q) := hx.tendsto0 hZq
  have hlim0y : Tendsto Γ₂ (𝓝[>] 0) (𝓝 q₂) := hy.tendsto0 hZq₂
  have hcx : ∀ τ ∈ I, ContinuousAt Γ τ := fun τ hτ =>
    (hΓx.hasDerivAt hIx.1 hτ).continuousAt
  have hcy : ∀ τ ∈ I₂, ContinuousAt Γ₂ τ := fun τ hτ =>
    (hΓy.hasDerivAt hIy.1 hτ).continuousAt
  have hregx : ∀ τ ∈ I, φ (Γ τ) ≠ 0 := fun τ hτ => (hΓx.2 τ hτ).2.1
  have hregy : ∀ τ ∈ I₂, φ (Γ₂ τ) ≠ 0 := fun τ hτ => (hΓy.2 τ hτ).2.1
  have hDx : ∀ τ ∈ I, Γ τ ∈ unitDisc := fun τ hτ => (hΓx.2 τ hτ).1
  have hDy : ∀ τ ∈ I₂, Γ₂ τ ∈ unitDisc := fun τ hτ => (hΓy.2 τ hτ).1
  have hmx : ∀ s, 0 < s → s ≤ t → s ∈ I := fun s hs hst => hx.mem_of_le ht hs hst
  have hmy : ∀ s, 0 < s → s ≤ t₂ → s ∈ I₂ := fun s hs hst => hy.mem_of_le ht₂ hs hst
  have ht0 : 0 < t := hI0x ht
  have ht₂0 : 0 < t₂ := hI0y ht₂
  -- velocities at the meeting point
  have hv : deriv Γ t = deriv Γ₂ t₂ ∨ deriv Γ t = -deriv Γ₂ t₂ := by
    have h1 := (hΓx.2 t ht).2.2
    have h2 := (hΓy.2 t₂ ht₂).2.2
    rw [← hmeet] at h2
    have h3 : φ (Γ t) * (deriv Γ t ^ 2 - deriv Γ₂ t₂ ^ 2) = 0 := by
      linear_combination h1 - h2
    have h4 := (mul_eq_zero.1 h3).resolve_left (hregx t ht)
    exact sq_eq_sq_iff_eq_or_eq_neg.1 (sub_eq_zero.1 h4)
  rcases hv with hv | hv
  · -- same direction: the same ray
    left
    have hU : ∀ s, t + s ∈ I → t₂ + s ∈ I₂ → Γ (t + s) = Γ₂ (t₂ + s) := fun s h1 h2 =>
      hΓx.unique hφ hIx hIy hΓy ht ht₂ hmeet hv h1 h2
    have htt : t = t₂ := by
      rcases lt_trichotomy t t₂ with h | h | h
      · exact (fx_p3_meet_aux ht0 h hmx hmy hlim0x hcy hregy hq0 hU).elim
      · exact h
      · exact (fx_p3_meet_aux ht₂0 h hmy hmx hlim0y hcx hregx hq₂0
          fun s h1 h2 => (hU s h2 h1).symm).elim
    subst htt
    have heq0 : Γ =ᶠ[𝓝[>] 0] Γ₂ := by
      filter_upwards [Ioo_mem_nhdsGT ht0] with s hs
      have := hU (s - t) (by rw [add_sub_cancel]; exact hmx s hs.1 hs.2.le)
        (by rw [add_sub_cancel]; exact hmy s hs.1 hs.2.le)
      rwa [add_sub_cancel] at this
    have hqq : q = q₂ := tendsto_nhds_unique (hlim0x.congr' heq0) hlim0y
    subst hqq
    refine ⟨rfl, ?_, rfl⟩
    refine hZq.dir_unique hu hu₂ (ε := min t (min t₀ t₀₂)) (by positivity) fun τ hτ => ?_
    have hτt : τ < t := lt_of_lt_of_le hτ.2 (min_le_left _ _)
    have hτ₀ : τ < t₀ := lt_of_lt_of_le hτ.2 ((min_le_right _ _).trans (min_le_left _ _))
    have hτ₀₂ : τ < t₀₂ := lt_of_lt_of_le hτ.2 ((min_le_right _ _).trans (min_le_right _ _))
    rw [← hmodx τ ⟨hτ.1, hτ₀⟩, ← hmody τ ⟨hτ.1, hτ₀₂⟩]
    have := hU (τ - t) (by rw [add_sub_cancel]; exact hmx τ hτ.1 hτt.le)
      (by rw [add_sub_cancel]; exact hmy τ hτ.1 hτt.le)
    rwa [add_sub_cancel] at this
  · -- opposite directions: a saddle connection listed both ways
    right
    have hU : ∀ s, t + s ∈ I → t₂ - s ∈ I₂ → Γ (t + s) = Γ₂ (t₂ - s) := fun s h1 h2 =>
      hΓx.unique_rev hφ hIx hIy hΓy ht ht₂ hmeet hv h1 h2
    have hU' : ∀ s, t₂ + s ∈ I₂ → t - s ∈ I → Γ₂ (t₂ + s) = Γ (t - s) := by
      intro s h1 h2
      have := hU (-s) (by rwa [← sub_eq_add_neg]) (by rwa [sub_neg_eq_add])
      rw [← sub_eq_add_neg, sub_neg_eq_add] at this
      exact this.symm
    -- neither `t + t₂ ∈ I` nor `t + t₂ ∈ I₂`
    have hnx : t + t₂ ∉ I := fun h =>
      fx_p3_meet_aux2 ht₂0 hIx.2 ht h hmy hlim0y hcx hregx hq₂0 hU
    have hny : t + t₂ ∉ I₂ := fun h =>
      fx_p3_meet_aux2 ht0 hIy.2 ht₂ (by rwa [add_comm]) hmx hlim0x hcy hregy hq0 hU'
    obtain ⟨hL0, hIxL, hlx, hLx⟩ := hx.bounded_of_not_mem (by linarith) hnx
    obtain ⟨hL₂0, hIyL, hly, hLy⟩ := hy.bounded_of_not_mem (by linarith) hny
    -- the ends have no regular limits in `Δ`
    have hendx : ∀ w ∈ unitDisc, φ w ≠ 0 → ¬ Tendsto Γ (𝓝[<] L) (𝓝 w) := by
      intro w hwD hw hT
      rcases hxe with hbd | hsad
      · rw [hlx] at hbd
        exact fx_p3_bd_no_limit hbd hwD hT
      · obtain ⟨-, hZe⟩ := hZ qe hsad.2.2.2.1 hsad.2.2.2.2.1
        have := tendsto_nhds_unique hT (hsad.tendsto hZe)
        exact hw (this ▸ hsad.2.2.2.2.1)
    have hendy : ∀ w ∈ unitDisc, φ w ≠ 0 → ¬ Tendsto Γ₂ (𝓝[<] L₂) (𝓝 w) := by
      intro w hwD hw hT
      rcases hye with hbd | hsad
      · rw [hly] at hbd
        exact fx_p3_bd_no_limit hbd hwD hT
      · obtain ⟨-, hZe⟩ := hZ qe₂ hsad.2.2.2.1 hsad.2.2.2.2.1
        have := tendsto_nhds_unique hT (hsad.tendsto hZe)
        exact hw (this ▸ hsad.2.2.2.2.1)
    have hLeq : L = t + t₂ :=
      fx_p3_meet_aux3 (hIxL ▸ ht) hLx hmy hcy hregy hDy hendx
        fun s h1 h2 => hU s (hIxL ▸ h1) h2
    have hL₂eq : L₂ = t₂ + t :=
      fx_p3_meet_aux3 (hIyL ▸ ht₂) (by linarith) hmx hcx hregx hDx hendy
        fun s h1 h2 => hU' s (hIyL ▸ h1) h2
    -- the second ray is the first one reversed
    have hrev : ∀ τ ∈ Ioo 0 L, Γ₂ τ = Γ (L - τ) := by
      intro τ hτ
      have h1 : t + (t₂ - τ) ∈ I := by rw [hIxL]; constructor <;> linarith [hτ.1, hτ.2]
      have h2 : t₂ - (t₂ - τ) ∈ I₂ := by rw [hIyL]; constructor <;> linarith [hτ.1, hτ.2]
      have := hU (t₂ - τ) h1 h2
      rw [show t + (t₂ - τ) = L - τ by linarith, sub_sub_cancel] at this
      exact this.symm
    have hrev' : ∀ τ ∈ Ioo 0 L, Γ τ = Γ₂ (L - τ) := by
      intro τ hτ
      rw [hrev (L - τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩, sub_sub_cancel]
    have hlimLx : Tendsto Γ (𝓝[<] L) (𝓝 q₂) := by
      refine (hlim0y.comp (fx_p3_tendsto_sub_nhdsLT L)).congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hL0] with τ hτ
      exact (hrev' τ hτ).symm
    have hlimLy : Tendsto Γ₂ (𝓝[<] L) (𝓝 q) := by
      refine (hlim0x.comp (fx_p3_tendsto_sub_nhdsLT L)).congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hL0] with τ hτ
      exact (hrev τ hτ).symm
    have hL₂L : L₂ = L := by linarith
    -- both are saddles
    have hsx : fx_p3_USad φ mZ ζZ rZ Γ I l qe ue L t₁ := by
      rcases hxe with hbd | hsad
      · rw [hlx] at hbd
        exact (fx_p3_bd_no_limit hbd hq₂ hlimLx).elim
      · exact hsad
    have hsy : fx_p3_USad φ mZ ζZ rZ Γ₂ I₂ l₂ qe₂ ue₂ L₂ t₁₂ := by
      rcases hye with hbd | hsad
      · rw [hly, hL₂L] at hbd
        exact (fx_p3_bd_no_limit hbd hq hlimLy).elim
      · exact hsad
    obtain ⟨-, hZqe⟩ := hZ qe hsx.2.2.2.1 hsx.2.2.2.2.1
    obtain ⟨-, hZqe₂⟩ := hZ qe₂ hsy.2.2.2.1 hsy.2.2.2.2.1
    have hqe : qe = q₂ := tendsto_nhds_unique (hsx.tendsto hZqe) hlimLx
    have hqe₂ : qe₂ = q := tendsto_nhds_unique (hsy.tendsto hZqe₂) (hL₂L ▸ hlimLy)
    refine ⟨hsx, hsy, hqe, hqe₂, ?_, ?_, hL₂L, by linarith⟩
    · -- the arrival direction of the first ray is the initial direction of the second
      obtain ⟨-, -, -, -, -, hue, ht₁, harr⟩ := hsx
      subst hqe
      refine hZqe.dir_unique hue hu₂ (ε := min (L - t₁) t₀₂) (lt_min (by linarith [ht₁.2]) ht₀y)
        fun τ hτ => ?_
      have hτ1 : τ < L - t₁ := lt_of_lt_of_le hτ.2 (min_le_left _ _)
      have hτ2 : τ < t₀₂ := lt_of_lt_of_le hτ.2 (min_le_right _ _)
      have hτL : τ ∈ Ioo 0 L := ⟨hτ.1, by linarith [ht₁.1]⟩
      have h1 := harr (L - τ) ⟨by linarith, by linarith [hτ.1]⟩
      rw [sub_sub_cancel] at h1
      rw [← h1, ← hmody τ ⟨hτ.1, hτ2⟩, hrev τ hτL]
    · obtain ⟨-, -, -, -, -, hue₂, ht₁₂, harr₂⟩ := hsy
      subst hqe₂
      rw [hL₂L] at ht₁₂ harr₂
      refine hZqe₂.dir_unique hue₂ hu (ε := min (L - t₁₂) t₀) (lt_min (by linarith [ht₁₂.2]) ht₀x)
        fun τ hτ => ?_
      have hτ1 : τ < L - t₁₂ := lt_of_lt_of_le hτ.2 (min_le_left _ _)
      have hτ2 : τ < t₀ := lt_of_lt_of_le hτ.2 (min_le_right _ _)
      have hτL : τ ∈ Ioo 0 L := ⟨hτ.1, by linarith [ht₁₂.1]⟩
      have h1 := harr₂ (L - τ) ⟨by linarith, by linarith [hτ.1]⟩
      rw [sub_sub_cancel] at h1
      rw [← h1, ← hmodx τ ⟨hτ.1, hτ2⟩, hrev' τ hτL]

/-- If `c > 0` and `v, w` are unit vectors with `arg (c v / w) = 0`, then `v = w`. -/
theorem fx_p3_arg_unit_ratio {c : ℝ} (hc : 0 < c) {v w : ℂ} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (h : arg ((c : ℂ) * (v / w)) = 0) : v = w := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  set z := (c : ℂ) * (v / w) with hz
  rw [Complex.arg_eq_zero_iff] at h
  have hzn : ‖z‖ = c := by
    rw [hz, norm_mul, norm_div, hv, hw, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    simp
  have hzre : z = (c : ℂ) := by
    have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h.2])
    have hre : z.re = c := by
      have h1 : ‖z‖ = |z.re| := by rw [hz']; simp [Complex.norm_real]
      rw [hzn, abs_of_nonneg h.1] at h1
      exact h1.symm
    rw [hz', hre]
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
  have h2 : v / w = 1 := by
    have := hzre
    rw [hz] at this
    field_simp at this
    field_simp
    linear_combination this
  field_simp at h2
  exact h2

/-- **No self-saddle** (one-sided chains are excluded): a saddle connection cannot return to its own
source zero.  Otherwise, if it returned along the same critical direction it would retrace itself
(contradicting injectivity); along a different direction, the closed edge is a chain with one side and
one (blunt) corner, excluded by `fx_chain_false`. -/
theorem fx_p3_no_loop {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {mZ : ℂ → ℕ} {ζZ : ℂ → ℂ → ℂ} {rZ ρZ : ℂ → ℝ}
    (hZ : ∀ q, q ∈ unitDisc → φ q = 0 →
      0 < mZ q ∧ fx_p3_ZeroChart φ (ζZ q) q (mZ q) (rZ q) (ρZ q))
    {q u : ℂ} {Γ : ℝ → ℂ} {I : Set ℝ} {l : Filter ℝ} {t₀ L : ℝ} {qe ue : ℂ} {t₁ : ℝ}
    (hx : fx_p3_URay φ mZ ζZ rZ q u Γ I l t₀ L) (hq : q ∈ unitDisc) (hq0 : φ q = 0)
    (hu : u ^ (mZ q + 2) = -1) (hsad : fx_p3_USad φ mZ ζZ rZ Γ I l qe ue L t₁)
    {par : ℝ → ℂ} {A A' : ℝ} (hp0 : par 0 = q) (hp1 : par 1 = qe)
    (hpτ : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ τ ∈ I, par s = Γ τ) (hinj : InjOn par (Ioo 0 1))
    (hC : ContDiffOn ℝ 1 par (Icc 0 1)) (hV : IsVerticalArc φ par 0 1) (hA : 0 < A)
    (hD0 : derivWithin par (Icc 0 1) 0 = (A : ℂ) * u * (deriv (ζZ q) q)⁻¹) (hA' : 0 < A')
    (hD1 : derivWithin par (Icc 0 1) 1 = -((A' : ℂ) * ue * (deriv (ζZ qe) qe)⁻¹)) :
    qe ≠ q := by
  intro hqe
  subst hqe
  obtain ⟨hIx, hI0x, hΓx, ht₀x, hsubx, hmodx, hshx⟩ := hx
  obtain ⟨hL0, hIL, hlL, -, -, hue, ht₁, harr⟩ := hsad
  obtain ⟨hm, hZq⟩ := hZ qe hq hq0
  have hζ' : deriv (ζZ qe) qe ≠ 0 := (hZq.2.2.2.2.2.1 qe (mem_closedBall_self hZq.1.le)).2.1
  -- the arrival direction differs from the initial one
  have hdir : ue ≠ u := by
    intro hue'
    subst hue'
    have hinjΓ := hΓx.injOn hφ hne hIx
    set τ := min (min (L - t₁) t₀) (L / 2) / 2 with hτ
    have hτ0 : 0 < τ := by
      have : 0 < min (min (L - t₁) t₀) (L / 2) :=
        lt_min (lt_min (by linarith [ht₁.2]) ht₀x) (by linarith)
      positivity
    have hτ1 : τ < L - t₁ := by
      have := min_le_left (min (L - t₁) t₀) (L / 2)
      have := min_le_left (L - t₁) t₀
      have : 0 < min (min (L - t₁) t₀) (L / 2) :=
        lt_min (lt_min (by linarith [ht₁.2]) ht₀x) (by linarith)
      linarith
    have hτ2 : τ < t₀ := by
      have := min_le_left (min (L - t₁) t₀) (L / 2)
      have := min_le_right (L - t₁) t₀
      have : 0 < min (min (L - t₁) t₀) (L / 2) :=
        lt_min (lt_min (by linarith [ht₁.2]) ht₀x) (by linarith)
      linarith
    have hτ3 : τ < L / 2 := by
      have := min_le_right (min (L - t₁) t₀) (L / 2)
      have : 0 < min (min (L - t₁) t₀) (L / 2) :=
        lt_min (lt_min (by linarith [ht₁.2]) ht₀x) (by linarith)
      linarith
    have h1 := harr (L - τ) ⟨by linarith, by linarith⟩
    rw [sub_sub_cancel, ← hmodx τ ⟨hτ0, hτ2⟩] at h1
    have h2 := hinjΓ (hIL ▸ ⟨by linarith, by linarith⟩ : L - τ ∈ I) (hsubx ⟨hτ0, hτ2⟩) h1
    linarith
  -- the one-sided chain
  set side : Fin 1 → ℝ → ℂ := fun _ => par with hside
  have hpar_reg : ∀ s ∈ Ioo (0 : ℝ) 1, par s ∈ unitDisc ∧ φ (par s) ≠ 0 := by
    intro s hs
    obtain ⟨τ, hτI, hτ⟩ := hpτ s hs
    rw [hτ]
    exact ⟨(hΓx.2 τ hτI).1, (hΓx.2 τ hτI).2.1⟩
  have hunit : ‖ue‖ = 1 := fx_p3_root_norm hue
  have hunit' : ‖u‖ = 1 := fx_p3_root_norm hu
  have hu0 : u ≠ 0 := by rintro rfl; simp at hunit'
  have hue0 : ue ≠ 0 := by rintro rfl; simp at hunit
  have hC1 : fx_IsChain φ side := by
    refine ⟨fun _ => (horizontal_vertical_isPhiStraight).2 hV, fun _ => hC, fun _ => ?_,
      fun _ => ?_, ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · rintro _ ⟨s, hs, rfl⟩
      rcases hs.1.eq_or_lt with h | h
      · subst h; show par 0 ∈ unitDisc; rw [hp0]; exact hq
      rcases hs.2.eq_or_lt with h' | h'
      · subst h'; show par 1 ∈ unitDisc; rw [hp1]; exact hq
      exact (hpar_reg s ⟨h, h'⟩).1
    · show par 1 = par 0
      rw [hp1, hp0]
    · intro i j s hs t ht hst
      refine ⟨Subsingleton.elim i j, ?_⟩
      change par s = par t at hst
      rcases hs.1.eq_or_lt with h | h <;> rcases ht.1.eq_or_lt with h' | h'
      · rw [← h, ← h']
      · subst h
        exfalso
        rw [hp0] at hst
        exact (hpar_reg t ⟨h', ht.2⟩).2 (hst ▸ hq0)
      · subst h'
        exfalso
        rw [hp0] at hst
        exact (hpar_reg s ⟨h, hs.2⟩).2 (hst.symm ▸ hq0)
      · exact hinj ⟨h, hs.2⟩ ⟨h', ht.2⟩ hst
    · show derivWithin par (Icc 0 1) 0 ≠ 0
      rw [hD0]
      exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.2 hA.ne') hu0) (inv_ne_zero hζ')
    · show derivWithin par (Icc 0 1) 1 ≠ 0
      rw [hD1]
      exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.2 hA'.ne') hue0)
        (inv_ne_zero hζ'))
    · show arg (-(derivWithin par (Icc 0 1) 1) / derivWithin par (Icc 0 1) 0) ≠ 0
      rw [hD1, hD0, neg_neg]
      have hid : (A' : ℂ) * ue * (deriv (ζZ qe) qe)⁻¹ / ((A : ℂ) * u * (deriv (ζZ qe) qe)⁻¹) =
          ((A' / A : ℝ) : ℂ) * (ue / u) := by
        rw [Complex.ofReal_div]
        field_simp
      rw [hid]
      intro h
      exact hdir (fx_p3_arg_unit_ratio (div_pos hA' hA) hunit hunit' h)
  have h3 := fx_chain_false hφ hne hC1
  have h2 : {j : Fin 1 | ¬ fx_IsBlunt φ side j}.ncard ≤ 1 := by
    calc {j : Fin 1 | ¬ fx_IsBlunt φ side j}.ncard ≤ (univ : Set (Fin 1)).ncard :=
          Set.ncard_le_ncard (subset_univ _)
      _ = 1 := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  omega

/-- **Avoidance of a point** (compact middle plus two tails): a continuous path on an open interval,
bounded away from `p` near both ends and never equal to `p` at the allowed times `W` (closed), stays
at a positive distance from `p` at the allowed times. -/
theorem fx_p3_avoid {Γ : ℝ → ℂ} {I : Set ℝ} (hI : fx_p3_IsOI I) (hc : ContinuousOn Γ I) {p : ℂ}
    {W : Set ℝ} (hW : IsClosed W) (hne : ∀ τ ∈ I ∩ W, Γ τ ≠ p)
    (h0 : ∃ δ₀ ∈ I, ∃ ε₀ > 0, ∀ τ ∈ I, τ ≤ δ₀ → ε₀ ≤ dist (Γ τ) p)
    (h1 : ∃ b ∈ I, ∃ ε₂ > 0, ∀ τ ∈ I, b ≤ τ → ε₂ ≤ dist (Γ τ) p) :
    ∃ ε > 0, ∀ τ ∈ I ∩ W, ε ≤ dist (Γ τ) p := by
  obtain ⟨δ₀, hδ₀, ε₀, hε₀, hA⟩ := h0
  obtain ⟨b, hb, ε₂, hε₂, hB⟩ := h1
  by_cases hM : (Icc δ₀ b ∩ W).Nonempty
  · have hMc : IsCompact (Icc δ₀ b ∩ W) := isCompact_Icc.inter_right hW
    have hMI : Icc δ₀ b ∩ W ⊆ I := fun τ hτ => hI.2.out hδ₀ hb hτ.1
    have hf : ContinuousOn (fun τ => dist (Γ τ) p) (Icc δ₀ b ∩ W) :=
      continuous_dist.comp_continuousOn ((hc.mono hMI).prodMk continuousOn_const)
    obtain ⟨τm, hτm, hmin⟩ := hMc.exists_isMinOn hM hf
    have hpos : 0 < dist (Γ τm) p := dist_pos.2 (hne τm ⟨hMI hτm, hτm.2⟩)
    refine ⟨min ε₀ (min ε₂ (dist (Γ τm) p)), lt_min hε₀ (lt_min hε₂ hpos), fun τ hτ => ?_⟩
    by_cases h1 : τ ≤ δ₀
    · exact (min_le_left _ _).trans (hA τ hτ.1 h1)
    by_cases h2 : b ≤ τ
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans (hB τ hτ.1 h2)
    have hτM : τ ∈ Icc δ₀ b ∩ W := ⟨⟨(not_le.1 h1).le, (not_le.1 h2).le⟩, hτ.2⟩
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans (hmin hτM)
  · refine ⟨min ε₀ ε₂, lt_min hε₀ hε₂, fun τ hτ => ?_⟩
    by_cases h1 : τ ≤ δ₀
    · exact (min_le_left _ _).trans (hA τ hτ.1 h1)
    by_cases h2 : b ≤ τ
    · exact (min_le_right _ _).trans (hB τ hτ.1 h2)
    exact (hM ⟨τ, ⟨(not_le.1 h1).le, (not_le.1 h2).le⟩, hτ.2⟩).elim

/-- **The flow box along an edge** (`box` of the forest): at an interior point `Γ τ` of a vertical
trajectory whose far part stays away from `Γ τ` (proper embedding) and away from a set `E` (the other
edges), a coordinate box of a regular chart meets the trajectory exactly in the vertical plaque through
`Γ τ`, and misses `E`. -/
theorem fx_p3_box_at {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {Γ : ℝ → ℂ}
    {I : Set ℝ} (hI : fx_p3_IsOI I) (hΓ : fx_p3_VT φ Γ I) {τ : ℝ} (hτ : τ ∈ I)
    (hfar : ∀ η > 0, ∃ ε > 0, ∀ τ' ∈ I, η ≤ |τ' - τ| → ε ≤ dist (Γ τ') (Γ τ))
    {E : Set ℂ} (hE : ∃ ε > 0, ∀ z ∈ E, ε ≤ dist z (Γ τ)) :
    ∃ (ζ : ℂ → ℂ) (N : Set ℂ), Γ τ ∈ N ∧ fx_IsFlowBox φ ζ N ∧
      Γ '' I ∩ N = {z | z ∈ N ∧ (ζ z).re = (ζ (Γ τ)).re} ∧ E ∩ N = ∅ := by
  set p := Γ τ with hp
  obtain ⟨hpD, hp0, -⟩ := hΓ.2 τ hτ
  obtain ⟨ζ, r, ρ0, hR, -⟩ := fx_p3_regChart_exists hφ hpD hp0 one_pos
  obtain ⟨hopen, hleft, hψ⟩ := hR.inv
  have hr := hR.1
  have hρ0 := hR.2.1
  have hζ0 := hR.2.2.2.1
  have hρB := hR.2.2.2.2.2.2
  set ψ := Function.invFunOn ζ (ball p r) with hψdef
  -- the local form of `Γ` near `τ`
  obtain ⟨he2, hloc⟩ := hR.local_form hφ hI hΓ hτ (mem_ball_self hr)
  rw [hζ0, norm_zero, sub_zero] at hloc
  simp only [zero_add] at hloc
  set e := deriv ζ (Γ τ) * deriv Γ τ with he
  obtain ⟨here, heim⟩ := fx_p3_sq_eq_neg_one he2
  have heim1 : |e.im| = 1 := by
    rw [← sq_abs] at heim
    exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).1 heim
  -- a window around `τ` inside `I` on which `Γ` is the chart line
  obtain ⟨η₀, hη₀, hη₀I⟩ := Metric.isOpen_iff.1 hI.1 τ hτ
  set η := min η₀ ρ0 / 2 with hη
  have hη0 : 0 < η := by positivity
  have hηI : ∀ s, |s| < η → τ + s ∈ I := by
    intro s hs
    apply hη₀I
    rw [mem_ball, Real.dist_eq, add_sub_cancel_left]
    have : η ≤ η₀ / 2 := by rw [hη]; linarith [min_le_left η₀ ρ0]
    linarith
  have hηρ : η < ρ0 := by rw [hη]; linarith [min_le_right η₀ ρ0]
  obtain ⟨ε₁, hε₁, hfar'⟩ := hfar η hη0
  obtain ⟨ε₂, hε₂, hE'⟩ := hE
  -- `ψ` is continuous at `0`, so small boxes lie in `ball p (min ε₁ ε₂)`
  have h0V : (0 : ℂ) ∈ ζ '' ball p r := hρB (mem_ball_self hρ0)
  have hψ0 : ψ 0 = p := by
    have := hleft p (mem_ball_self hr)
    rwa [hζ0] at this
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousAt_iff.1 (hψ 0 h0V).2.2.continuousAt
    (min ε₁ ε₂) (lt_min hε₁ hε₂)
  set δ := min (min δ₁ η) ρ0 / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  have hδρ : δ ≤ ρ0 / 2 := by rw [hδ]; linarith [min_le_right (min δ₁ η) ρ0]
  have hδη : δ < η := by
    rw [hδ]; linarith [min_le_left (min δ₁ η) ρ0, min_le_right δ₁ η]
  have hδδ₁ : 2 * δ < δ₁ := by
    rw [hδ]; linarith [min_le_left (min δ₁ η) ρ0, min_le_left δ₁ η]
  obtain ⟨hpN, hN⟩ := hR.box hδ0 hδρ
  set N := ball p r ∩ ζ ⁻¹' {w : ℂ | |w.re - (0 : ℂ).re| < δ ∧ |w.im - (0 : ℂ).im| < δ} with hNdef
  -- points of `N` are close to `p`
  have hNclose : ∀ z ∈ N, dist z p < min ε₁ ε₂ := by
    intro z hz
    have hzψ : z = ψ (ζ z) := (hleft z hz.1).symm
    have hw : ‖ζ z‖ < δ₁ := by
      have h1 := hz.2
      simp only [mem_preimage, mem_ofPred_eq, Complex.zero_re, Complex.zero_im, sub_zero] at h1
      calc ‖ζ z‖ ≤ |(ζ z).re| + |(ζ z).im| := Complex.norm_le_abs_re_add_abs_im _
        _ < δ + δ := add_lt_add h1.1 h1.2
        _ < δ₁ := by linarith
    have := hδ₁' (x := ζ z) (by rw [dist_zero_right]; exact hw)
    rw [hψ0, ← hzψ] at this
    exact this
  refine ⟨ζ, N, hpN, hN, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro z ⟨⟨τ', hτ', rfl⟩, hzN⟩
      refine ⟨hzN, ?_⟩
      -- `τ'` is close to `τ`
      have hclose : |τ' - τ| < η := by
        by_contra h
        have := hfar' τ' hτ' (not_lt.1 h)
        have := hNclose _ hzN
        linarith [min_le_left ε₁ ε₂]
      have h1 := hloc (τ' - τ) (by rw [add_sub_cancel]; exact hτ')
        (by rw [abs_lt] at hclose ⊢; constructor <;> linarith)
      rw [add_sub_cancel] at h1
      have hV : ((τ' - τ : ℝ) : ℂ) * e ∈ ζ '' ball p r := by
        apply hρB
        rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hen : ‖e‖ = 1 := by
          have h := congr_arg norm he2
          rw [norm_pow, norm_neg, norm_one] at h
          exact (pow_eq_one_iff_of_nonneg (norm_nonneg e) two_ne_zero).1 h
        rw [hen, mul_one]
        linarith
      rw [h1, (hψ _ hV).2.1, hζ0, Complex.re_ofReal_mul, here, mul_zero]
      rfl
    · rintro z ⟨hzN, hzre⟩
      rw [hζ0] at hzre
      have hy := hzN.2
      simp only [mem_preimage, mem_ofPred_eq, Complex.zero_re, Complex.zero_im, sub_zero] at hy
      set s := (ζ z).im * e.im with hs
      have hsabs : |s| < δ := by rw [hs, abs_mul, heim1, mul_one]; exact hy.2
      have hsη : |s| < η := lt_trans hsabs hδη
      have hζz : ζ z = (s : ℂ) * e := by
        apply Complex.ext
        · rw [Complex.re_ofReal_mul, here, mul_zero]; exact hzre
        · rw [Complex.im_ofReal_mul, hs, mul_assoc, ← sq, heim, mul_one]
      refine ⟨⟨τ + s, hηI s hsη, ?_⟩, hzN⟩
      rw [hloc s (hηI s hsη) (by linarith), ← hζz]
      exact hleft z hzN.1
  · apply eq_empty_of_forall_notMem
    rintro z ⟨hzE, hzN⟩
    have := hE' z hzE
    have := hNclose z hzN
    linarith [min_le_right ε₁ ε₂]

/-- The data of a critical ray (the output of `fx_p3_ray`) as a predicate: unit-speed data, the
`C¹` reparametrization `par` with its source tangent, and the end dichotomy. -/
def fx_p3_RayOK (φ : ℂ → ℂ) (mZ : ℂ → ℕ) (ζZ : ℂ → ℂ → ℂ) (rZ : ℂ → ℝ) (q u : ℂ)
    (Γ : ℝ → ℂ) (I : Set ℝ) (l : Filter ℝ) (t₀ : ℝ) (par : ℝ → ℂ) (qe ue : ℂ)
    (L t₁ A : ℝ) : Prop :=
  fx_p3_URay φ mZ ζZ rZ q u Γ I l t₀ L ∧
    par 0 = q ∧ par '' Ioo 0 1 = Γ '' I ∧ InjOn par (Ioo 0 1) ∧
    (∀ s ∈ Ioo (0 : ℝ) 1, ∃ τ ∈ I, par s = Γ τ) ∧
    ContDiffOn ℝ 1 par (Ico 0 1) ∧ IsVerticalArc φ par 0 1 ∧ 0 < A ∧
    derivWithin par (Icc 0 1) 0 = (A : ℂ) * u * (deriv (ζZ q) q)⁻¹ ∧
    ((fx_p3_UBd Γ l ∧
        ∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc → ∀ᶠ s in 𝓝[<] (1 : ℝ), par s ∉ K) ∨
      (fx_p3_USad φ mZ ζZ rZ Γ I l qe ue L t₁ ∧ par 1 = qe ∧ ContDiffOn ℝ 1 par (Icc 0 1) ∧
        ∃ A' : ℝ, 0 < A' ∧
          derivWithin par (Icc 0 1) 1 = -((A' : ℂ) * ue * (deriv (ζZ qe) qe)⁻¹)))

/-- Every critical ray has its data (`fx_p3_ray`, repackaged). -/
theorem fx_p3_rayOK {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) (mZ : ℂ → ℕ) (ζZ : ℂ → ℂ → ℂ) (rZ ρZ : ℂ → ℝ)
    (hZ : ∀ q, q ∈ unitDisc → φ q = 0 →
      0 < mZ q ∧ fx_p3_ZeroChart φ (ζZ q) q (mZ q) (rZ q) (ρZ q))
    {q u : ℂ} (hq : q ∈ unitDisc) (hq0 : φ q = 0) (hu : u ^ (mZ q + 2) = -1) :
    ∃ (Γ : ℝ → ℂ) (I : Set ℝ) (l : Filter ℝ) (t₀ : ℝ) (par : ℝ → ℂ) (qe ue : ℂ) (L t₁ A : ℝ),
      fx_p3_RayOK φ mZ ζZ rZ q u Γ I l t₀ par qe ue L t₁ A := by
  obtain ⟨Γ, I, l, t₀, par, qe, ue, L, t₁, A, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16⟩ := fx_p3_ray hρ hφ hne mZ ζZ rZ ρZ hZ hq hq0 hu
  refine ⟨Γ, I, l, t₀, par, qe, ue, L, t₁, A, ⟨h1, h2, h3, h4, h5, h6, h7⟩, h8, h9, h10, h11, h12,
    h13, h14, h15, ?_⟩
  rcases h16 with h | ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩
  · exact Or.inl h
  · exact Or.inr ⟨⟨s1, s2, s3, s4, s5, s6, s7, s8⟩, s9, s10, s11⟩

/-- A strict total order on `ℂ` (lexicographic in `(re, im)`), used to list each saddle connection
once. -/
def fx_p3_lex (a b : ℂ) : Prop := a.re < b.re ∨ (a.re = b.re ∧ a.im < b.im)

/-- The lexicographic order is asymmetric. -/
theorem fx_p3_lex_asymm {a b : ℂ} (h : fx_p3_lex a b) : ¬ fx_p3_lex b a := by
  unfold fx_p3_lex at *
  rintro (h' | ⟨h1', h2'⟩) <;> rcases h with h | ⟨h1, h2⟩ <;> linarith

/-- The lexicographic order is total on distinct points. -/
theorem fx_p3_lex_total {a b : ℂ} (hab : a ≠ b) : fx_p3_lex a b ∨ fx_p3_lex b a := by
  unfold fx_p3_lex
  rcases lt_trichotomy a.re b.re with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy a.im b.im with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact absurd (Complex.ext h h') hab
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

/-- There are at least three critical directions at a zero of order `m ≥ 1`: `e^{±iπ/(m+2)}` and
`e^{3iπ/(m+2)}`. -/
theorem fx_p3_three_roots {m : ℕ} (hm0 : 0 < m) : 3 ≤ {u : ℂ | u ^ (m + 2) = -1}.ncard := by
  have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hm3 : (3 : ℝ) ≤ (m : ℝ) + 2 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    linarith
  set θ : ℝ := π / ((m : ℝ) + 2) with hθ
  have hθ0 : 0 < θ := by positivity
  have hmθ : ((m : ℝ) + 2) * θ = π := by rw [hθ]; field_simp
  have hθ3 : 3 * θ ≤ π := by nlinarith
  have hroot : ∀ (α : ℝ) (k : ℤ), ((m : ℝ) + 2) * α = (2 * k + 1) * π →
      (Complex.exp ((α : ℂ) * I)) ^ (m + 2) = -1 := by
    intro α k hα
    rw [← Complex.exp_nat_mul]
    have hαC : ((m : ℂ) + 2) * (α : ℂ) = (2 * (k : ℂ) + 1) * π := by exact_mod_cast hα
    have : ((m + 2 : ℕ) : ℂ) * ((α : ℂ) * I) = (k : ℂ) * (2 * π * I) + π * I := by
      push_cast
      linear_combination I * hαC
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_pi_mul_I]
  have harg : ∀ α : ℝ, α ∈ Ioc (-π) π → arg (Complex.exp ((α : ℂ) * I)) = α := by
    intro α hα
    rw [Complex.arg_exp_mul_I, toIocMod_eq_self]
    exact ⟨hα.1, by linarith [hα.2]⟩
  have ha₁ := harg θ ⟨by linarith [Real.pi_pos], by linarith⟩
  have ha₂ := harg (3 * θ) ⟨by linarith [Real.pi_pos], hθ3⟩
  have ha₃ := harg (-θ) ⟨by linarith, by linarith [Real.pi_pos]⟩
  have h12 : Complex.exp ((θ : ℂ) * I) ≠ Complex.exp (((3 * θ : ℝ) : ℂ) * I) := fun h => by
    have := congr_arg arg h; rw [ha₁, ha₂] at this; linarith
  have h13 : Complex.exp ((θ : ℂ) * I) ≠ Complex.exp (((-θ : ℝ) : ℂ) * I) := fun h => by
    have := congr_arg arg h; rw [ha₁, ha₃] at this; linarith
  have h23 : Complex.exp (((3 * θ : ℝ) : ℂ) * I) ≠ Complex.exp (((-θ : ℝ) : ℂ) * I) := fun h => by
    have := congr_arg arg h; rw [ha₂, ha₃] at this; linarith
  have hsub : ({Complex.exp ((θ : ℂ) * I), Complex.exp (((3 * θ : ℝ) : ℂ) * I),
      Complex.exp (((-θ : ℝ) : ℂ) * I)} : Set ℂ) ⊆ {u : ℂ | u ^ (m + 2) = -1} := by
    intro v hv
    rcases hv with rfl | rfl | rfl
    · exact hroot θ 0 (by push_cast; linarith)
    · exact hroot (3 * θ) 1 (by push_cast; linarith)
    · exact hroot (-θ) (-1) (by push_cast; linarith)
  calc 3 = ({Complex.exp ((θ : ℂ) * I), Complex.exp (((3 * θ : ℝ) : ℂ) * I),
        Complex.exp (((-θ : ℝ) : ℂ) * I)} : Set ℂ).ncard :=
        (Set.ncard_eq_three.2 ⟨_, _, _, h12, h13, h23, rfl⟩).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (fx_p3_roots_finite m)

/-- Tails of a ray's filter: an eventual property holds on a final segment of the interval. -/
theorem fx_p3_URay.tail {φ : ℂ → ℂ} {mZ : ℂ → ℕ} {ζZ : ℂ → ℂ → ℂ} {rZ : ℂ → ℝ}
    {q u : ℂ} {Γ : ℝ → ℂ} {I : Set ℝ} {l : Filter ℝ} {t₀ L : ℝ}
    (hx : fx_p3_URay φ mZ ζZ rZ q u Γ I l t₀ L) {P : ℝ → Prop} (hP : ∀ᶠ τ in l, P τ) :
    ∃ b ∈ I, ∀ τ ∈ I, b ≤ τ → P τ := by
  rcases hx.2.2.2.2.2.2 with ⟨hL, hI, hl⟩ | ⟨hI, hl⟩
  · subst hI hl
    obtain ⟨a, ha, haP⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hL).1 hP
    refine ⟨(max a 0 + L) / 2, ⟨by linarith [le_max_right a 0], by
      linarith [max_lt (mem_Iio.1 ha) hL]⟩, fun τ hτ hbτ => haP ⟨?_, hτ.2⟩⟩
    linarith [le_max_left a 0, max_lt (mem_Iio.1 ha) hL]
  · subst hI hl
    obtain ⟨a, ha⟩ := mem_atTop_sets.1 hP
    exact ⟨max a 1, mem_Ioi.2 (lt_of_lt_of_le one_pos (le_max_right _ _)),
      fun τ _ hτ => ha τ ((le_max_left _ _).trans hτ)⟩

/-- **The ends of a ray stay away from a regular point**: near its source zero, and along its tail
(boundary ray: it leaves a small closed disc around `p`; saddle: it converges to a zero). -/
theorem fx_p3_ends {φ : ℂ → ℂ} {mZ : ℂ → ℕ} {ζZ : ℂ → ℂ → ℂ} {rZ ρZ : ℂ → ℝ}
    (hZ : ∀ q, q ∈ unitDisc → φ q = 0 →
      0 < mZ q ∧ fx_p3_ZeroChart φ (ζZ q) q (mZ q) (rZ q) (ρZ q))
    {q u : ℂ} {Γ : ℝ → ℂ} {I : Set ℝ} {l : Filter ℝ} {t₀ L : ℝ} {qe ue : ℂ} {t₁ : ℝ}
    (hx : fx_p3_URay φ mZ ζZ rZ q u Γ I l t₀ L) (hq : q ∈ unitDisc) (hq0 : φ q = 0)
    (hxe : fx_p3_UBd Γ l ∨ fx_p3_USad φ mZ ζZ rZ Γ I l qe ue L t₁) {p : ℂ}
    (hp : p ∈ unitDisc) (hp0 : φ p ≠ 0) :
    (∃ δ₀ ∈ I, ∃ ε₀ > 0, ∀ τ ∈ I, τ ≤ δ₀ → ε₀ ≤ dist (Γ τ) p) ∧
      (∃ b ∈ I, ∃ ε₂ > 0, ∀ τ ∈ I, b ≤ τ → ε₂ ≤ dist (Γ τ) p) := by
  obtain ⟨-, hZq⟩ := hZ q hq hq0
  have hpq : p ≠ q := fun h => hp0 (h ▸ hq0)
  have hd : 0 < dist p q := dist_pos.2 hpq
  constructor
  · have h1 : ∀ᶠ τ in 𝓝[>] (0 : ℝ), dist (Γ τ) q < dist p q / 2 :=
      (hx.tendsto0 hZq).eventually (ball_mem_nhds q (by positivity))
    obtain ⟨δ, hδ, hδP⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' (zero_lt_one' ℝ)).1 h1
    have hδ0 : 0 < δ := hδ
    set δ₀ := min δ t₀ / 2 with hδ₀
    have ht₀ := hx.2.2.2.1
    have hδ₀pos : 0 < δ₀ := by positivity
    have hδ₀t : δ₀ < t₀ := by rw [hδ₀]; linarith [min_le_right δ t₀]
    have hδ₀δ : δ₀ < δ := by rw [hδ₀]; linarith [min_le_left δ t₀]
    refine ⟨δ₀, hx.2.2.2.2.1 ⟨hδ₀pos, hδ₀t⟩, dist p q / 2, by positivity, fun τ hτ hτδ => ?_⟩
    have := hδP ⟨hx.2.1 hτ, lt_of_le_of_lt hτδ hδ₀δ⟩
    have h2 := dist_triangle p (Γ τ) q
    rw [dist_comm p (Γ τ)] at h2
    simp only [mem_ofPred_eq] at this
    linarith
  · rcases hxe with hbd | hsad
    · obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 isOpen_ball p hp
      have hK : closedBall p (ε / 2) ⊆ unitDisc :=
        (closedBall_subset_ball (by linarith)).trans hεD
      obtain ⟨b, hb, hbP⟩ := hx.tail (hbd _ (isCompact_closedBall p (ε / 2)) hK)
      refine ⟨b, hb, ε / 2, by positivity, fun τ hτ hbτ => ?_⟩
      have := hbP τ hτ hbτ
      rw [mem_closedBall, not_le] at this
      exact this.le
    · obtain ⟨-, hZe⟩ := hZ qe hsad.2.2.2.1 hsad.2.2.2.2.1
      have hpe : p ≠ qe := fun h => hp0 (h ▸ hsad.2.2.2.2.1)
      have hde : 0 < dist p qe := dist_pos.2 hpe
      have hl : l = 𝓝[<] L := hsad.2.2.1
      have h1 : ∀ᶠ τ in l, dist (Γ τ) qe < dist p qe / 2 := by
        rw [hl]
        exact (hsad.tendsto hZe).eventually (ball_mem_nhds qe (by positivity))
      obtain ⟨b, hb, hbP⟩ := hx.tail h1
      refine ⟨b, hb, dist p qe / 2, by positivity, fun τ hτ hbτ => ?_⟩
      have := hbP τ hτ hbτ
      have h2 := dist_triangle p (Γ τ) qe
      rw [dist_comm p (Γ τ)] at h2
      linarith

/-- **Assembly of the critical vertical forest** from a family of critical rays (one for each zero
`q` and critical direction `u`): the edges are the boundary rays and the saddle connections listed
from their lexicographically smaller end. -/
theorem fx_p3_forest {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {mZ : ℂ → ℕ} {ζZ : ℂ → ℂ → ℂ} {rZ ρZ : ℂ → ℝ}
    (hZ : ∀ q, q ∈ unitDisc → φ q = 0 →
      0 < mZ q ∧ fx_p3_ZeroChart φ (ζZ q) q (mZ q) (rZ q) (ρZ q))
    (hord : ∀ q, q ∈ unitDisc → φ q = 0 → meromorphicOrderAt φ q = ((mZ q : ℕ) : ℤ))
    {Γ : ℂ × ℂ → ℝ → ℂ} {I : ℂ × ℂ → Set ℝ} {l : ℂ × ℂ → Filter ℝ} {t₀ : ℂ × ℂ → ℝ}
    {par : ℂ × ℂ → ℝ → ℂ} {qe ue : ℂ × ℂ → ℂ} {L t₁ A : ℂ × ℂ → ℝ}
    (hray : ∀ x : ℂ × ℂ, x.1 ∈ unitDisc → φ x.1 = 0 → x.2 ^ (mZ x.1 + 2) = -1 →
      fx_p3_RayOK φ mZ ζZ rZ x.1 x.2 (Γ x) (I x) (l x) (t₀ x) (par x) (qe x) (ue x) (L x)
        (t₁ x) (A x)) :
    ∃ (ι : Type) (_ : Fintype ι) (par : ι → ℝ → ℂ) (src : ι → ℂ) (dst : ι → Option ℂ),
      fx_IsVForest φ par src dst := by
  classical
  have hφD : DifferentiableOn ℂ φ unitDisc := hφ.mono (ball_subset_ball hρ.le)
  set R : Set (ℂ × ℂ) := {x | x.1 ∈ unitDisc ∧ φ x.1 = 0 ∧ x.2 ^ (mZ x.1 + 2) = -1} with hR
  set sad : ℂ × ℂ → Prop := fun x =>
    fx_p3_USad φ mZ ζZ rZ (Γ x) (I x) (l x) (qe x) (ue x) (L x) (t₁ x) with hsad
  set S : Set (ℂ × ℂ) := {x | x ∈ R ∧ (¬ sad x ∨ fx_p3_lex x.1 (qe x))} with hS
  have hZfin := fx_p3_zeros_finite hρ hφ hne
  have hRfin : R.Finite := by
    refine (hZfin.biUnion (t := fun q => ({q} : Set ℂ) ×ˢ {u : ℂ | u ^ (mZ q + 2) = -1})
      fun q _ => (finite_singleton q).prod (fx_p3_roots_finite _)).subset ?_
    intro x hx
    exact mem_biUnion (x := x.1) ⟨hx.1, hx.2.1⟩ ⟨mem_singleton _, hx.2.2⟩
  have hSfin : S.Finite := hRfin.subset fun x hx => hx.1
  -- per-ray facts
  have hRay : ∀ x ∈ R, fx_p3_RayOK φ mZ ζZ rZ x.1 x.2 (Γ x) (I x) (l x) (t₀ x) (par x) (qe x)
      (ue x) (L x) (t₁ x) (A x) := fun x hx => hray x hx.1 hx.2.1 hx.2.2
  have hEnd : ∀ x ∈ R, fx_p3_UBd (Γ x) (l x) ∨ sad x := by
    intro x hx
    rcases (hRay x hx).2.2.2.2.2.2.2.2.2 with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hSadFull : ∀ x ∈ R, sad x → par x 1 = qe x ∧ ContDiffOn ℝ 1 (par x) (Icc 0 1) ∧
      ∃ A' : ℝ, 0 < A' ∧
        derivWithin (par x) (Icc 0 1) 1 = -((A' : ℂ) * ue x * (deriv (ζZ (qe x)) (qe x))⁻¹) := by
    intro x hx hs
    rcases (hRay x hx).2.2.2.2.2.2.2.2.2 with h | h
    · obtain ⟨-, hZe⟩ := hZ (qe x) hs.2.2.2.1 hs.2.2.2.2.1
      exact absurd h.1 (hs.not_bd hZe)
    · exact h.2
  have hBd : ∀ x ∈ R, ¬ sad x → ∀ K : Set ℂ, IsCompact K → K ⊆ unitDisc →
      ∀ᶠ s in 𝓝[<] (1 : ℝ), par x s ∉ K := by
    intro x hx hs
    rcases (hRay x hx).2.2.2.2.2.2.2.2.2 with h | h
    · exact h.2
    · exact absurd h.1 hs
  have hMeet : ∀ x ∈ R, ∀ y ∈ R, ∀ t ∈ I x, ∀ t' ∈ I y, Γ x t = Γ y t' →
      x = y ∨ (sad x ∧ sad y ∧ qe x = y.1 ∧ qe y = x.1 ∧ ue x = y.2 ∧ ue y = x.2) := by
    intro x hx y hy t ht t' ht' h
    rcases fx_p3_meet hφD hZ (hRay x hx).1 hx.1 hx.2.1 hx.2.2 (hEnd x hx) (hRay y hy).1 hy.1
      hy.2.1 hy.2.2 (hEnd y hy) ht ht' h with ⟨h1, h2, -⟩ | ⟨h1, h2, h3, h4, h5, h6, -⟩
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr ⟨h1, h2, h3, h4, h5, h6⟩
  -- the reverse listing of a saddle connection
  have hRev : ∀ x ∈ R, sad x → (qe x, ue x) ∈ R ∧ sad (qe x, ue x) ∧
      qe (qe x, ue x) = x.1 ∧ ue (qe x, ue x) = x.2 ∧ qe x ≠ x.1 := by
    intro x hx hs
    have hs' := hs
    obtain ⟨hL0, hIL, hlL, hqeD, hqe0, hue, ht₁, harr⟩ := hs'
    have hyR : (qe x, ue x) ∈ R := ⟨hqeD, hqe0, hue⟩
    have hRx := hRay x hx
    have hloop : qe x ≠ x.1 := by
      obtain ⟨A', hA', hD1⟩ := (hSadFull x hx hs).2.2
      exact fx_p3_no_loop hφD hne hZ hRx.1 hx.1 hx.2.1 hx.2.2 hs hRx.2.1
        (hSadFull x hx hs).1 hRx.2.2.2.2.1 hRx.2.2.2.1 (hSadFull x hx hs).2.1 hRx.2.2.2.2.2.2.1
        hRx.2.2.2.2.2.2.2.1 hRx.2.2.2.2.2.2.2.2.1 hA' hD1
    have hRy := hRay (qe x, ue x) hyR
    obtain ⟨-, -, -, ht₀y, hsuby, hmody, -⟩ := hRy.1
    set τ := min (L x - t₁ x) (t₀ (qe x, ue x)) / 2 with hτ
    have hτ0 : 0 < τ := by
      have : 0 < min (L x - t₁ x) (t₀ (qe x, ue x)) := lt_min (by linarith [ht₁.2]) ht₀y
      positivity
    have hτ1 : τ < L x - t₁ x := by
      have := min_le_left (L x - t₁ x) (t₀ (qe x, ue x))
      have : 0 < min (L x - t₁ x) (t₀ (qe x, ue x)) := lt_min (by linarith [ht₁.2]) ht₀y
      linarith
    have hτ2 : τ < t₀ (qe x, ue x) := by
      have := min_le_right (L x - t₁ x) (t₀ (qe x, ue x))
      have : 0 < min (L x - t₁ x) (t₀ (qe x, ue x)) := lt_min (by linarith [ht₁.2]) ht₀y
      linarith
    have hmeet : Γ x (L x - τ) = Γ (qe x, ue x) τ := by
      rw [harr (L x - τ) ⟨by linarith, by linarith⟩, hmody τ ⟨hτ0, hτ2⟩, sub_sub_cancel]
    rcases hMeet x hx _ hyR (L x - τ) (hIL ▸ ⟨by linarith [ht₁.1], by linarith⟩) τ
      (hsuby ⟨hτ0, hτ2⟩) hmeet with h | ⟨-, h2, -, h4, -, h6⟩
    · exact absurd (congr_arg Prod.fst h).symm hloop
    · exact ⟨hyR, h2, h4, h6, hloop⟩
  -- the listed rays: boundary rays, and saddles from their smaller end
  have hSlex : ∀ i : ↥S, sad i.1 → fx_p3_lex i.1.1 (qe i.1) := fun i hs =>
    i.2.2.resolve_left (not_not.2 hs)
  have hRevS : ∀ x ∈ R, x ∉ S → sad x ∧ (qe x, ue x) ∈ S := by
    intro x hx hxS
    have hs : sad x := by
      by_contra h
      exact hxS ⟨hx, Or.inl h⟩
    refine ⟨hs, ?_⟩
    obtain ⟨hyR, -, hqy, -, hloop⟩ := hRev x hx hs
    refine ⟨hyR, Or.inr ?_⟩
    rw [hqy]
    have hnl : ¬ fx_p3_lex x.1 (qe x) := fun h => hxS ⟨hx, Or.inr h⟩
    rcases fx_p3_lex_total hloop with h | h
    · exact h
    · exact absurd h hnl
  -- the listed edge leaving the zero `x.1` in the critical direction `x.2`
  let E : ∀ x : ℂ × ℂ, x ∈ R → ↥S := fun x hx =>
    if h : x ∈ S then ⟨x, h⟩ else ⟨(qe x, ue x), (hRevS x hx h).2⟩
  have hE1 : ∀ x (hx : x ∈ R) (h : x ∈ S), E x hx = ⟨x, h⟩ := fun x hx h => by
    simp only [E, dite_eq_left h]
  have hE2 : ∀ x (hx : x ∈ R) (h : x ∉ S), E x hx = ⟨(qe x, ue x), (hRevS x hx h).2⟩ :=
    fun x hx h => by simp only [E, dite_eq_right h]
  have hSf : Fintype ↥S := hSfin.fintype
  refine ⟨↥S, hSf, fun i => par i.1, fun i => i.1.1,
    fun i => if sad i.1 then some (qe i.1) else none, ?_⟩
  have hiR : ∀ i : ↥S, i.1 ∈ R := fun i => i.2.1
  -- the outgoing tangent of the edge `E x`
  have hEdir : ∀ x (hx : x ∈ R), ∃ c : ℝ, 0 < c ∧
      fx_outTangent (fun i : ↥S => par i.1) (fun i : ↥S => i.1.1) (E x hx) x.1 =
        (c : ℂ) * x.2 * (deriv (ζZ x.1) x.1)⁻¹ := by
    intro x hx
    by_cases h : x ∈ S
    · rw [hE1 x hx h]
      obtain ⟨-, -, -, -, -, -, -, hA, hD0, -⟩ := hRay x hx
      refine ⟨A x, hA, ?_⟩
      unfold fx_outTangent
      rw [ite_eq_left rfl]
      exact hD0
    · rw [hE2 x hx h]
      have hs := (hRevS x hx h).1
      obtain ⟨hyR, hys, hqy, huy, hloop⟩ := hRev x hx hs
      obtain ⟨-, -, A', hA', hD1⟩ := hSadFull _ hyR hys
      refine ⟨A', hA', ?_⟩
      unfold fx_outTangent
      rw [ite_eq_right hloop]
      simp only at hD1 ⊢
      rw [hD1, hqy, huy, neg_neg]
  -- every incident edge is some `E x`
  have hE4 : ∀ (i : ↥S) (q : ℂ), fx_Incident (fun i : ↥S => i.1.1)
      (fun i : ↥S => if sad i.1 then some (qe i.1) else none) i q →
      ∃ u : ℂ, ∃ hu : (q, u) ∈ R, E (q, u) hu = i := by
    intro i q hi
    rcases hi with hi | hi
    · have hx : (q, i.1.2) = i.1 := Prod.ext hi.symm rfl
      refine ⟨i.1.2, hx ▸ hiR i, ?_⟩
      rw [hE1 _ (hx ▸ hiR i) (hx ▸ i.2)]
      exact Subtype.ext hx
    · by_cases hs : sad i.1
      · simp only [hs, ite_true, Option.some.injEq] at hi
        obtain ⟨hyR, hys, hqy, huy, hloop⟩ := hRev i.1 (hiR i) hs
        rw [hi] at hyR hys hqy huy hloop
        refine ⟨ue i.1, hyR, ?_⟩
        have hnS : (q, ue i.1) ∉ S := by
          rintro ⟨-, hS'⟩
          rcases hS' with h | h
          · exact h hys
          · rw [hqy] at h
            have := hSlex i hs
            rw [hi] at this
            exact fx_p3_lex_asymm this h
        rw [hE2 _ hyR hnS]
        exact Subtype.ext (Prod.ext hqy huy)
      · simp only [hs, ite_false, reduceCtorEq] at hi
  refine ⟨hZfin, fun i => (hRay i.1 (hiR i)).2.2.2.2.2.2.1, ?_, fun i => (hRay i.1 (hiR i)).2.2.2.1,
    fun i => (hRay i.1 (hiR i)).2.2.2.2.2.1, fun i => ⟨(hRay i.1 (hiR i)).2.1, (hiR i).1,
      (hiR i).2.1⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- mem
    intro i t ht
    obtain ⟨τ, hτ, hpt⟩ := (hRay i.1 (hiR i)).2.2.2.2.1 t ht
    show par i.1 t ∈ unitDisc
    rw [hpt]
    exact ((hRay i.1 (hiR i)).1.2.2.1.2 τ hτ).1
  · -- src_tan
    intro i
    obtain ⟨-, -, -, -, -, -, -, hA, hD0, -⟩ := hRay i.1 (hiR i)
    show derivWithin (par i.1) (Icc 0 1) 0 ≠ 0
    rw [hD0]
    have hu := fx_p3_root_norm (hiR i).2.2
    have hu0 : i.1.2 ≠ 0 := by intro h; rw [h] at hu; simp at hu
    obtain ⟨-, hZq⟩ := hZ i.1.1 (hiR i).1 (hiR i).2.1
    have hζ' := (hZq.2.2.2.2.2.1 i.1.1 (mem_closedBall_self hZq.1.le)).2.1
    exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.2 hA.ne') hu0) (inv_ne_zero hζ')
  · -- saddle
    intro i q' hq'
    by_cases hs : sad i.1
    · simp only [hs, ite_true, Option.some.injEq] at hq'
      subst hq'
      obtain ⟨hp1, hCI, A', hA', hD1⟩ := hSadFull i.1 (hiR i) hs
      obtain ⟨-, -, -, -, hloop⟩ := hRev i.1 (hiR i) hs
      obtain ⟨-, hZqe⟩ := hZ (qe i.1) hs.2.2.2.1 hs.2.2.2.2.1
      have hζ' := (hZqe.2.2.2.2.2.1 _ (mem_closedBall_self hZqe.1.le)).2.1
      have hu := fx_p3_root_norm hs.2.2.2.2.2.1
      have hu0 : ue i.1 ≠ 0 := by intro h; rw [h] at hu; simp at hu
      refine ⟨hs.2.2.2.1, hs.2.2.2.2.1, hloop, hCI, hp1, ?_⟩
      rw [hD1]
      exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.2 hA'.ne') hu0)
        (inv_ne_zero hζ'))
    · simp only [hs, ite_false, reduceCtorEq] at hq'
  · -- bdry
    intro i hi
    have hs : ¬ sad i.1 := by
      intro hs
      simp only [hs, ite_true, reduceCtorEq] at hi
    exact hBd i.1 (hiR i) hs
  · -- disj
    intro i j hij
    rw [Set.disjoint_left]
    rintro z ⟨s, hs, rfl⟩ ⟨s', hs', hzz⟩
    obtain ⟨τ, hτ, hpτ⟩ := (hRay i.1 (hiR i)).2.2.2.2.1 s hs
    obtain ⟨τ', hτ', hpτ'⟩ := (hRay j.1 (hiR j)).2.2.2.2.1 s' hs'
    rw [hpτ, hpτ'] at hzz
    rcases hMeet j.1 (hiR j) i.1 (hiR i) τ' hτ' τ hτ hzz with h | ⟨hs1, hs2, h3, h4, -, -⟩
    · exact hij (Subtype.ext h).symm
    · exact fx_p3_lex_asymm (h3 ▸ hSlex j hs1) (h4 ▸ hSlex i hs2)
  · -- box
    intro i t ht
    obtain ⟨hU, -, himg, -, hpτ, -, -, -, -, -⟩ := hRay i.1 (hiR i)
    obtain ⟨τ, hτ, hpt⟩ := hpτ t ht
    have hΓx := hU.2.2.1
    have hIx := hU.1
    obtain ⟨hpD, hp0', -⟩ := hΓx.2 τ hτ
    have hfar : ∀ η > 0, ∃ ε > 0, ∀ τ' ∈ I i.1, η ≤ |τ' - τ| →
        ε ≤ dist (Γ i.1 τ') (Γ i.1 τ) := by
      intro η hη
      obtain ⟨h0, h1⟩ := fx_p3_ends hZ hU (hiR i).1 (hiR i).2.1 (hEnd i.1 (hiR i)) hpD hp0'
      have hW : IsClosed {τ' : ℝ | η ≤ |τ' - τ|} :=
        isClosed_le continuous_const (continuous_abs.comp (continuous_id.sub continuous_const))
      obtain ⟨ε, hε, hεW⟩ := fx_p3_avoid hIx hΓx.continuousOn hW (fun τ' hτ' h => by
          have h1 := hΓx.injOn hφD hne hIx hτ'.1 hτ h
          have h2 : η ≤ |τ' - τ| := hτ'.2
          rw [h1, sub_self, abs_zero] at h2
          linarith) h0 h1
      exact ⟨ε, hε, fun τ' hτ' hη' => hεW τ' ⟨hτ', hη'⟩⟩
    have hother : ∀ j : ↥S, ∃ ε > 0, j ≠ i → ∀ τ' ∈ I j.1, ε ≤ dist (Γ j.1 τ') (Γ i.1 τ) := by
      intro j
      by_cases hji : j = i
      · exact ⟨1, one_pos, fun h => absurd hji h⟩
      obtain ⟨hUj, -⟩ := hRay j.1 (hiR j)
      obtain ⟨h0, h1⟩ := fx_p3_ends hZ hUj (hiR j).1 (hiR j).2.1 (hEnd j.1 (hiR j)) hpD hp0'
      obtain ⟨ε, hε, hεW⟩ := fx_p3_avoid hUj.1 hUj.2.2.1.continuousOn isClosed_univ
        (fun τ' hτ' h => by
          rcases hMeet j.1 (hiR j) i.1 (hiR i) τ' hτ'.1 τ hτ h with h' | ⟨hs1, hs2, h3, h4, -, -⟩
          · exact hji (Subtype.ext h')
          · exact fx_p3_lex_asymm (h3 ▸ hSlex j hs1) (h4 ▸ hSlex i hs2)) h0 h1
      exact ⟨ε, hε, fun _ τ' hτ' => hεW τ' ⟨hτ', mem_univ _⟩⟩
    choose εf hεf hεfW using hother
    have hε : 0 < Finset.univ.inf' ⟨i, Finset.mem_univ i⟩ εf :=
      (Finset.lt_inf'_iff _).2 fun j _ => hεf j
    have hE : ∃ ε > 0, ∀ z ∈ {z : ℂ | ∃ j : ↥S, j ≠ i ∧ z ∈ par j.1 '' Ioo 0 1},
        ε ≤ dist z (Γ i.1 τ) := by
      refine ⟨_, hε, ?_⟩
      rintro z ⟨j, hji, s, hs, rfl⟩
      obtain ⟨τ', hτ', hpτ'⟩ := (hRay j.1 (hiR j)).2.2.2.2.1 s hs
      rw [hpτ']
      exact (Finset.inf'_le _ (Finset.mem_univ j)).trans (hεfW j hji τ' hτ')
    obtain ⟨ζ, N, hpN, hN, hplaque, hEN⟩ := fx_p3_box_at hφD hIx hΓx hτ hfar hE
    refine ⟨ζ, N, ?_, hN, ?_, fun j hji => ?_⟩
    · show par i.1 t ∈ N
      rw [hpt]
      exact hpN
    · show par i.1 '' Ioo 0 1 ∩ N = {z | z ∈ N ∧ (ζ z).re = (ζ (par i.1 t)).re}
      rw [himg, hplaque, hpt]
    · apply eq_empty_of_forall_notMem
      rintro z ⟨hz, hzN⟩
      have : z ∈ {z : ℂ | ∃ j : ↥S, j ≠ i ∧ z ∈ par j.1 '' Ioo 0 1} ∩ N := ⟨⟨j, hji, hz⟩, hzN⟩
      rw [hEN] at this
      exact this
  · -- star_card
    intro q hq hq0
    set U : Set ℂ := {u : ℂ | u ^ (mZ q + 2) = -1} with hU
    have hqu : ∀ u ∈ U, (q, u) ∈ R := fun u hu => ⟨hq, hq0, hu⟩
    set g : ↥U → ↥S := fun u => E (q, u.1) (hqu u.1 u.2) with hg
    have hinc : ∀ u : ↥U, fx_Incident (fun i : ↥S => i.1.1)
        (fun i : ↥S => if sad i.1 then some (qe i.1) else none) (g u) q := by
      intro u
      by_cases h : (q, u.1) ∈ S
      · left
        show (E (q, u.1) (hqu u.1 u.2)).1.1 = q
        rw [hE1 _ (hqu u.1 u.2) h]
      · right
        show (if sad (E (q, u.1) (hqu u.1 u.2)).1 then some (qe (E (q, u.1) (hqu u.1 u.2)).1)
          else none) = some q
        rw [hE2 _ (hqu u.1 u.2) h]
        obtain ⟨-, hys, hqy, -, -⟩ := hRev (q, u.1) (hqu u.1 u.2) (hRevS _ (hqu u.1 u.2) h).1
        simp only [hys, ite_true, hqy]
    have hginj : Function.Injective g := by
      intro u v huv
      obtain ⟨cu, hcu, hdu⟩ := hEdir (q, u.1) (hqu u.1 u.2)
      obtain ⟨cv, hcv, hdv⟩ := hEdir (q, v.1) (hqu v.1 v.2)
      have h1 : fx_outTangent (fun i : ↥S => par i.1) (fun i : ↥S => i.1.1) (g u) q =
          fx_outTangent (fun i : ↥S => par i.1) (fun i : ↥S => i.1.1) (g v) q := by rw [huv]
      simp only [hg] at h1
      rw [hdu, hdv] at h1
      obtain ⟨-, hZq⟩ := hZ q hq hq0
      have hζ' := (hZq.2.2.2.2.2.1 q (mem_closedBall_self hZq.1.le)).2.1
      have h2 : (cu : ℂ) * u.1 = (cv : ℂ) * v.1 := mul_right_cancel₀ (inv_ne_zero hζ') h1
      have hnu := fx_p3_root_norm u.2
      have hnv := fx_p3_root_norm v.2
      have h3 : cu = cv := by
        have := congr_arg norm h2
        rw [norm_mul, norm_mul, hnu, hnv, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hcu.le, Real.norm_of_nonneg hcv.le] at this
        linarith
      rw [h3] at h2
      exact Subtype.ext (mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hcv.ne') h2)
    calc 3 ≤ U.ncard := fx_p3_three_roots (hZ q hq hq0).1
      _ = (univ : Set ↥U).ncard := by rw [Set.ncard_univ, Nat.card_coe_set_eq]
      _ ≤ _ := Set.ncard_le_ncard_of_injOn g (fun u _ => hinc u) hginj.injOn (Set.toFinite _)
  · -- blunt
    intro q hq hq0 i j hi hj hij
    obtain ⟨u, hu, rfl⟩ := hE4 i q hi
    obtain ⟨v, hv, rfl⟩ := hE4 j q hj
    have huv : u ≠ v := by
      rintro rfl
      exact hij rfl
    obtain ⟨cu, hcu, hdu⟩ := hEdir (q, u) hu
    obtain ⟨cv, hcv, hdv⟩ := hEdir (q, v) hv
    refine ⟨mZ q, hord q hq hq0, ?_⟩
    simp only at hdu hdv
    rw [hdu, hdv]
    obtain ⟨-, hZq⟩ := hZ q hq hq0
    have hζ' := (hZq.2.2.2.2.2.1 q (mem_closedBall_self hZq.1.le)).2.1
    have hnu := fx_p3_root_norm hu.2.2
    have hnv := fx_p3_root_norm hv.2.2
    have hv0 : v ≠ 0 := by intro h; rw [h] at hnv; simp at hnv
    have hr : (cu : ℂ) * u * (deriv (ζZ q) q)⁻¹ / ((cv : ℂ) * v * (deriv (ζZ q) q)⁻¹) =
        ((cu / cv : ℝ) : ℂ) * (u / v) := by
      rw [Complex.ofReal_div]
      field_simp
    rw [hr]
    have hpow : (((cu / cv : ℝ) : ℂ) * (u / v)) ^ (mZ q + 2) = (((cu / cv) ^ (mZ q + 2) : ℝ) : ℂ) := by
      rw [mul_pow, div_pow, hu.2.2, hv.2.2, neg_div_neg_eq, div_one, mul_one]
      push_cast
      ring
    refine ⟨by rw [hpow, Complex.ofReal_im], by rw [hpow, Complex.ofReal_re]; positivity, ?_⟩
    rintro ⟨h1, h2⟩
    have harg : arg (((cu / cv : ℝ) : ℂ) * (u / v)) = 0 := Complex.arg_eq_zero_iff.2 ⟨h2.le, h1⟩
    exact huv (fx_p3_arg_unit_ratio (div_pos hcu hcv) hnu hnv harg)

/-- **The critical vertical graph of a tame `φ ≢ 0` is a finite forest.**  Maximal vertical
rays from the zeros (local normal form `eq25_5_natural_parameter_zero`); a recurrent ray gives a
bigon and a closed ray a one-sided chain (`fx_chain_false`), so every ray is a saddle connection
or leaves every compact subset of `Δ`. -/
theorem fx_vforest_exists {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) :
    ∃ (ι : Type) (_ : Fintype ι) (par : ι → ℝ → ℂ) (src : ι → ℂ) (dst : ι → Option ℂ),
      fx_IsVForest φ par src dst := by
  -- zero charts at all zeros
  have hZC : ∀ q : ℂ, ∃ (m : ℕ) (ζ : ℂ → ℂ) (r ρ0 : ℝ), q ∈ unitDisc → φ q = 0 →
      0 < m ∧ meromorphicOrderAt φ q = (m : ℤ) ∧ fx_p3_ZeroChart φ ζ q m r ρ0 := by
    intro q
    by_cases h : q ∈ unitDisc ∧ φ q = 0
    · obtain ⟨m, hm, hord, ζ, r, ρ0, hZ⟩ := fx_p3_zeroChart_exists hρ hφ hne h.1 h.2
      exact ⟨m, ζ, r, ρ0, fun _ _ => ⟨hm, hord, hZ⟩⟩
    · exact ⟨0, id, 0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose mZ ζZ rZ ρZ hZC using hZC
  have hZ : ∀ q, q ∈ unitDisc → φ q = 0 →
      0 < mZ q ∧ fx_p3_ZeroChart φ (ζZ q) q (mZ q) (rZ q) (ρZ q) :=
    fun q hq hq0 => ⟨(hZC q hq hq0).1, (hZC q hq hq0).2.2⟩
  have hord : ∀ q, q ∈ unitDisc → φ q = 0 → meromorphicOrderAt φ q = ((mZ q : ℕ) : ℤ) :=
    fun q hq hq0 => (hZC q hq hq0).2.1
  -- the critical rays at all zeros and critical directions
  have hR : ∀ x : ℂ × ℂ, ∃ (Γ : ℝ → ℂ) (I : Set ℝ) (l : Filter ℝ) (t₀ : ℝ) (par : ℝ → ℂ)
      (qe ue : ℂ) (L t₁ A : ℝ), x.1 ∈ unitDisc → φ x.1 = 0 → x.2 ^ (mZ x.1 + 2) = -1 →
        fx_p3_RayOK φ mZ ζZ rZ x.1 x.2 Γ I l t₀ par qe ue L t₁ A := by
    intro x
    by_cases h : x.1 ∈ unitDisc ∧ φ x.1 = 0 ∧ x.2 ^ (mZ x.1 + 2) = -1
    · obtain ⟨Γ, I, l, t₀, par, qe, ue, L, t₁, A, hok⟩ :=
        fx_p3_rayOK hρ hφ hne mZ ζZ rZ ρZ hZ h.1 h.2.1 h.2.2
      exact ⟨Γ, I, l, t₀, par, qe, ue, L, t₁, A, fun _ _ _ => hok⟩
    · exact ⟨fun _ => 0, ∅, ⊥, 0, fun _ => 0, 0, 0, 0, 0, 0,
        fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose Γ I l t₀ par qe ue L t₁ A hray using hR
  exact fx_p3_forest hρ hφ hne hZ hord hray

/-- **Star lemma**: a horizontal leaf meets at most one edge at each zero (a leaf arc through
two edges at `q` closes up with them to a chain whose only non-blunt corners are the two crossing
points; the crossings are chosen consecutive along the leaf and nearest to `q` along the edges, so
that the chain is simple). -/
theorem fx_star {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) {z q : ℂ} {i j : ι} (hi : fx_Incident src dst i q)
    (hj : fx_Incident src dst j q) (hzi : (fx_leaf φ z ∩ par i '' Ioo 0 1).Nonempty)
    (hzj : (fx_leaf φ z ∩ par j '' Ioo 0 1).Nonempty) : i = j := by
  exact fx_p2_star_core hφ (fun side hC => fx_chain_false hφ hne hC) hF.vert hF.mem hF.inj hF.smooth
    hF.src_zero hF.src_tan hF.saddle hF.bdry hF.disj hF.blunt hi hj hzi hzj

/-- **No cycles**: if every zero of a nonempty set `S` of zeros has at least two incident edges
in `A`, some zero of `S` has an edge of `A` leaving `S` (to the boundary or to a zero outside `S`).
Otherwise the edges of `A` inside `S` contain a cycle of saddle connections: a chain with only blunt
corners. -/
theorem fx_nocycle {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {ι : Type} [Fintype ι] {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) {S : Set ℂ}
    (hS : S ⊆ {q | q ∈ unitDisc ∧ φ q = 0}) (hSne : S.Nonempty) {A : Set ι}
    (hA : ∀ q ∈ S, 2 ≤ {i | i ∈ A ∧ fx_Incident src dst i q}.ncard) :
    ∃ q ∈ S, ∃ i ∈ A, (src i = q ∧ ∀ q', dst i = some q' → q' ∉ S) ∨
      (dst i = some q ∧ src i ∉ S) := by
  exact fx_p2_nocycle_core (fun side hC => fx_chain_false hφ hne hC) hF.zeros_finite hF.vert hF.mem
    hF.inj hF.src_zero hF.src_tan hF.saddle hF.disj hF.blunt hS hSne hA

/-! ## §4 Cut calibrations and the covering -/

/-- A **cut choice**: every zero `q` of `φ` in `Δ` picks an incident edge `pick q`, whose other end is
the boundary or a zero of strictly smaller rank.  Following the picks reaches `∂Δ`, so the picked
edges form hanging trees. -/
def fx_IsCutChoice (φ : ℂ → ℂ) {ι : Type} (src : ι → ℂ) (dst : ι → Option ℂ)
    (pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι) (rk : ℂ → ℕ) : Prop :=
  ∀ q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0},
    (src (pick q) = q.1 ∧ ∀ q', dst (pick q) = some q' → rk q' < rk q.1) ∨
      (dst (pick q) = some q.1 ∧ rk (src (pick q)) < rk q.1)

/-- The **cut set** of a choice: all zeros of `φ` in `Δ` and the picked edges. -/
def fx_cutSet (φ : ℂ → ℂ) {ι : Type} (par : ι → ℝ → ℂ)
    (pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι) : Set ℂ :=
  {q | q ∈ unitDisc ∧ φ q = 0} ∪ ⋃ q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}, par (pick q) '' Ioo 0 1

/-- **A calibrated saturated set** : `R ⊆ Δ` measurable, of regular points; `u` is
Lipschitz on `Δ` with `|Du| ≤ |φ|^{1/2}` a.e.; and near every regular point there is a flow box
which either misses `R`, or in which `R` is a union of horizontal plaques and `u = Re ζ + c`. -/
structure fx_IsCalib (φ : ℂ → ℂ) (R : Set ℂ) (u : ℂ → ℝ) : Prop where
  /-- `R` is measurable -/
  meas : MeasurableSet R
  /-- `R ⊆ Δ` -/
  sub : R ⊆ unitDisc
  /-- `R` consists of regular points -/
  reg : ∀ z ∈ R, φ z ≠ 0
  /-- `u` is Lipschitz on `Δ` -/
  lip : ∃ L : ℝ≥0, LipschitzOnWith L u unitDisc
  /-- `u` is `φ`-1-Lipschitz infinitesimally, a.e. -/
  grad : ∀ᵐ y ∂(volume.restrict unitDisc), DifferentiableAt ℝ u y ∧
    ‖fderiv ℝ u y‖ ≤ Real.sqrt ‖φ y‖
  /-- local saturation and calibration -/
  box : ∀ p ∈ unitDisc, φ p ≠ 0 → ∃ (ζ : ℂ → ℂ) (N : Set ℂ), p ∈ N ∧ fx_IsFlowBox φ ζ N ∧
    (R ∩ N = ∅ ∨ ((∃ E : Set ℝ, R ∩ N = {z | z ∈ N ∧ (ζ z).im ∈ E}) ∧
      ∃ c : ℝ, ∀ z ∈ N, u z = (ζ z).re + c))

/-- Interior points of the edges of a vertical forest are regular points of `Δ`. -/
theorem fx_p4_edge_reg {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) (i : ι) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : par i t ∈ unitDisc ∧ φ (par i t) ≠ 0 := by
  obtain ⟨ζ, N, hpN, hN, -⟩ := hF.box i t ht
  exact ⟨hN.2.1 hpN, (hN.2.2.2.1 _ hpN).1⟩

/-- A point off the image of a compact parameter interval has a ball around it missing that
image. -/
theorem fx_p4_avoid_compact {c : ℝ → ℂ} {a b : ℝ} (hc : ContinuousOn c (Icc a b)) {y : ℂ}
    (hy : ∀ t ∈ Icc a b, c t ≠ y) : ∃ r > 0, ∀ t ∈ Icc a b, c t ∉ ball y r := by
  have hK : IsCompact (c '' Icc a b) := isCompact_Icc.image_of_continuousOn hc
  have hyK : y ∉ c '' Icc a b := by
    rintro ⟨t, ht, h⟩
    exact hy t ht h
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl y hyK
  refine ⟨r, hr, fun t ht hct => ?_⟩
  exact hball hct ⟨t, ht, rfl⟩

/-- A boundary edge eventually leaves a small ball around any point of `Δ`. -/
theorem fx_p4_avoid_tail {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) {i : ι} (hi : dst i = none) {y : ℂ}
    (hy : y ∈ unitDisc) : ∃ r > 0, ∃ η < 1, ∀ t ∈ Ioo η 1, par i t ∉ ball y r := by
  have hy1 : ‖y‖ < 1 := by simpa [unitDisc] using hy
  set r₀ := (1 - ‖y‖) / 2 with hr₀
  have hr₀p : 0 < r₀ := by rw [hr₀]; linarith
  have hK : closedBall y r₀ ⊆ unitDisc := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    show x ∈ ball 0 1
    rw [mem_ball, dist_zero_right]
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
      _ < 1 := by linarith
  obtain ⟨η, hη, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1
    (hF.bdry i hi (closedBall y r₀) (isCompact_closedBall y r₀) hK)
  exact ⟨r₀, hr₀p, η, hη, fun t ht hb => hsub ht (ball_subset_closedBall hb)⟩

/-- A point `y ∈ Δ` which `par i` avoids on `[a, 1)`, and which is not the saddle end of the edge,
has a ball around it missing `par i '' [a, 1)`. -/
theorem fx_p4_avoid_Ico {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) (i : ι) {a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a < 1) {y : ℂ} (hy : y ∈ unitDisc) (hyi : ∀ t ∈ Ico a 1, par i t ≠ y)
    (hyd : ∀ q, dst i = some q → q ≠ y) : ∃ r > 0, ∀ t ∈ Ico a 1, par i t ∉ ball y r := by
  rcases hdi : dst i with _ | q
  · obtain ⟨r₁, hr₁, η, hη, htail⟩ := fx_p4_avoid_tail hF hdi hy
    have hb1 : max a η < 1 := max_lt ha1 hη
    have hcont : ContinuousOn (par i) (Icc a (max a η)) :=
      (hF.smooth i).continuousOn.mono (fun t ht => ⟨ha0.trans ht.1, ht.2.trans_lt hb1⟩)
    obtain ⟨r₂, hr₂, hcomp⟩ := fx_p4_avoid_compact hcont
      (fun t ht => hyi t ⟨ht.1, ht.2.trans_lt hb1⟩)
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun t ht hball => ?_⟩
    by_cases htb : t ≤ max a η
    · exact hcomp t ⟨ht.1, htb⟩ (ball_subset_ball (min_le_right _ _) hball)
    · push Not at htb
      exact htail t ⟨(le_max_right a η).trans_lt htb, ht.2⟩
        (ball_subset_ball (min_le_left _ _) hball)
  · obtain ⟨-, -, -, hcd, h1, -⟩ := hF.saddle i q hdi
    obtain ⟨r, hr, hcomp⟩ := fx_p4_avoid_compact (hcd.continuousOn.mono (Icc_subset_Icc ha0 le_rfl))
      (fun t ht => by
        rcases eq_or_lt_of_le ht.2 with h | h
        · rw [h, h1]
          exact hyd q hdi
        · exact hyi t ⟨ht.1, h⟩)
    exact ⟨r, hr, fun t ht => hcomp t ⟨ht.1, ht.2.le⟩⟩

/-- The zeros of `φ` in `Δ` form a finite type. -/
theorem fx_p4_zsub_finite {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) :
    Finite {q : ℂ // q ∈ unitDisc ∧ φ q = 0} :=
  hF.zeros_finite.to_subtype

/-- Near a regular point `y ∈ Δ`, the cut set consists only of points of the picked edges through
`y`. -/
theorem fx_p4_cut_local {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) (pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι) {y : ℂ}
    (hy : y ∈ unitDisc) (hy0 : φ y ≠ 0) :
    ∃ r > 0, ball y r ⊆ unitDisc ∧ ∀ x ∈ ball y r, x ∈ fx_cutSet φ par pick →
      ∃ q, y ∈ par (pick q) '' Ioo 0 1 ∧ x ∈ par (pick q) '' Ioo 0 1 := by
  have := fx_p4_zsub_finite hF
  have hΔρ : unitDisc ⊆ ball (0 : ℂ) ρ := ball_subset_ball hρ.le
  have h1 : ∀ᶠ x in 𝓝 y, x ∈ unitDisc := isOpen_ball.mem_nhds hy
  have h2 : ∀ᶠ x in 𝓝 y, φ x ≠ 0 :=
    ((hφ.continuousOn.mono hΔρ).continuousAt (isOpen_ball.mem_nhds hy)).eventually_ne hy0
  have h3 : ∀ q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}, ∀ᶠ x in 𝓝 y,
      y ∉ par (pick q) '' Ioo 0 1 → x ∉ par (pick q) '' Ioo 0 1 := by
    intro q
    by_cases hyq : y ∈ par (pick q) '' Ioo 0 1
    · exact Filter.Eventually.of_forall fun x h => absurd hyq h
    obtain ⟨r, hr, hav⟩ := fx_p4_avoid_Ico hF (pick q) le_rfl zero_lt_one hy
      (fun t ht h => by
        rcases eq_or_lt_of_le ht.1 with h0 | h0
        · rw [← h0, (hF.src_zero (pick q)).1] at h
          exact hy0 (h ▸ (hF.src_zero (pick q)).2.2)
        · exact hyq ⟨t, ⟨h0, ht.2⟩, h⟩)
      (fun q' hq' h => hy0 (h ▸ (hF.saddle _ q' hq').2.1))
    filter_upwards [Metric.ball_mem_nhds y hr] with x hx _ hxq
    obtain ⟨t, ht, hxt⟩ := hxq
    exact hav t ⟨ht.1.le, ht.2⟩ (hxt ▸ hx)
  obtain ⟨r, hr, hball⟩ :=
    Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and (Filter.eventually_all.2 h3)))
  refine ⟨r, hr, fun x hx => (hball x hx).1, fun x hx hxc => ?_⟩
  obtain ⟨-, hx0, hxq⟩ := hball x hx
  rcases hxc with ⟨-, hxz⟩ | hxe
  · exact absurd hxz hx0
  · obtain ⟨q, hq⟩ := mem_iUnion.1 hxe
    by_cases hyq : y ∈ par (pick q) '' Ioo 0 1
    · exact ⟨q, hyq, hq⟩
    · exact absurd hq (hxq q hyq)

/-- The complement of the cut set in `Δ` is open. -/
theorem fx_p4_cut_isOpen {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) (pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι) :
    IsOpen (unitDisc \ fx_cutSet φ par pick) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hy, hyc⟩
  have hy0 : φ y ≠ 0 := fun h => hyc (Or.inl ⟨hy, h⟩)
  obtain ⟨r, hr, hsub, hloc⟩ := fx_p4_cut_local hρ hφ hF pick hy hy0
  filter_upwards [Metric.ball_mem_nhds y hr] with x hx
  refine ⟨hsub hx, fun hxc => ?_⟩
  obtain ⟨q, hyq, -⟩ := hloc x hx hxc
  exact hyc (Or.inr (mem_iUnion.2 ⟨q, hyq⟩))

/-- An edge of the forest is a Lebesgue-null set (a `C¹` curve in the plane). -/
theorem fx_p4_edge_null {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) (i : ι) :
    volume (par i '' Ioo 0 1) = 0 := by
  set s : Set ℂ := {z | z.im = 0 ∧ z.re ∈ Ioo (0 : ℝ) 1} with hsdef
  have hker : (LinearMap.ker Complex.imLm : Submodule ℝ ℂ) ≠ ⊤ := by
    intro h
    have : Complex.I ∈ LinearMap.ker Complex.imLm := h ▸ Submodule.mem_top
    simp at this
  have hs : volume s = 0 :=
    measure_mono_null (fun z hz => by simpa [LinearMap.mem_ker] using hz.1)
      (Measure.addHaar_submodule volume _ hker)
  have hd : DifferentiableOn ℝ (fun z : ℂ => par i z.re) s := by
    intro z hz
    have h1 : DifferentiableAt ℝ (par i) z.re :=
      ((hF.smooth i).differentiableOn one_ne_zero).differentiableAt
        (Ico_mem_nhds hz.2.1 hz.2.2)
    exact (h1.comp z Complex.reCLM.differentiableAt).differentiableWithinAt
  have := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd hs
  refine measure_mono_null ?_ this
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨(t : ℂ), ⟨by simp, by simpa using ht⟩, by simp⟩

/-- The cut set is Lebesgue-null. -/
theorem fx_p4_cut_null {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst)
    (pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι) : volume (fx_cutSet φ par pick) = 0 := by
  have := fx_p4_zsub_finite hF
  refine measure_union_null (hF.zeros_finite.measure_zero volume) ?_
  exact measure_iUnion_null fun q => fx_p4_edge_null hF (pick q)

/-- The complement of the cut set is dense in `Δ`. -/
theorem fx_p4_cut_dense {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst)
    (pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι) {y : ℂ} (hy : y ∈ unitDisc) :
    y ∈ closure (unitDisc \ fx_cutSet φ par pick) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_contra h
  push Not at h
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 isOpen_ball y hy
  have hsub : ball y (min ε r) ⊆ fx_cutSet φ par pick := by
    intro x hx
    by_contra hxc
    have hxD : x ∈ unitDisc := hrsub (ball_subset_ball (min_le_right _ _) hx)
    have h1 := h x ⟨hxD, hxc⟩
    rw [mem_ball, dist_comm] at hx
    exact absurd (hx.trans_le (min_le_left _ _)) (not_lt.2 h1)
  have := measure_mono_null hsub (fx_p4_cut_null hF pick)
  exact (Metric.measure_ball_pos volume y (lt_min hε hr)).ne' this

/-- The picked edge of a zero is incident to it. -/
theorem fx_p4_pick_inc {φ : ℂ → ℂ} {ι : Type} {src : ι → ℂ} {dst : ι → Option ℂ}
    {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι} {rk : ℂ → ℕ}
    (hpick : fx_IsCutChoice φ src dst pick rk) (q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}) :
    fx_Incident src dst (pick q) q.1 := by
  rcases hpick q with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

/-- A picked edge incident to another zero `q` comes from a zero of larger rank. -/
theorem fx_p4_pick_rank {φ : ℂ → ℂ} {ι : Type} {src : ι → ℂ} {dst : ι → Option ℂ}
    {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι} {rk : ℂ → ℕ}
    (hpick : fx_IsCutChoice φ src dst pick rk) {q q' : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}}
    (hne : q'.1 ≠ q.1) (hinc : fx_Incident src dst (pick q') q.1) : rk q.1 < rk q'.1 := by
  rcases hpick q' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hinc with h | h
  · exact absurd (h1.symm.trans h) hne
  · exact h2 q.1 h
  · rw [← h]
    exact h2
  · rw [h1] at h
    exact absurd (Option.some_injective _ h) hne

/-- The closure of an edge meets `Δ` only in the edge and its end zeros. -/
theorem fx_p4_edge_closure {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) (i : ι) {y : ℂ} (hy : y ∈ unitDisc)
    (hyc : y ∈ closure (par i '' Ioo 0 1)) :
    y ∈ par i '' Ioo 0 1 ∨ y = src i ∨ dst i = some y := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨r, hr, hav⟩ := fx_p4_avoid_Ico hF i le_rfl zero_lt_one hy
    (fun t ht hty => by
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · rw [← h0, (hF.src_zero i).1] at hty
        exact h2 hty.symm
      · exact h1 ⟨t, ⟨h0, ht.2⟩, hty⟩)
    (fun q hq hqy => h3 (hqy ▸ hq))
  rw [Metric.mem_closure_iff] at hyc
  obtain ⟨b, ⟨t, ht, rfl⟩, hb⟩ := hyc r hr
  exact hav t ⟨ht.1.le, ht.2⟩ (by rw [mem_ball, dist_comm]; exact hb)

/-- The closure of an edge is connected. -/
theorem fx_p4_edge_closure_conn {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) (i : ι) :
    IsConnected (closure (par i '' Ioo 0 1)) :=
  ((isConnected_Ioo zero_lt_one).image _
    ((hF.smooth i).continuousOn.mono Ioo_subset_Ico_self)).closure

/-- The source of an edge lies in its closure. -/
theorem fx_p4_edge_src_mem {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) (i : ι) :
    src i ∈ closure (par i '' Ioo 0 1) := by
  rw [← (hF.src_zero i).1]
  refine ContinuousWithinAt.mem_closure_image ?_ ?_
  · exact ((hF.smooth i).continuousOn 0 ⟨le_rfl, zero_lt_one⟩).mono Ioo_subset_Ico_self
  · rw [closure_Ioo zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩

/-- The saddle end of an edge lies in its closure. -/
theorem fx_p4_edge_dst_mem {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) {i : ι} {q : ℂ}
    (hq : dst i = some q) : q ∈ closure (par i '' Ioo 0 1) := by
  obtain ⟨-, -, -, hcd, h1, -⟩ := hF.saddle i q hq
  rw [← h1]
  refine ContinuousWithinAt.mem_closure_image ?_ ?_
  · exact (hcd.continuousOn 1 ⟨zero_le_one, le_rfl⟩).mono Ioo_subset_Icc_self
  · rw [closure_Ioo zero_ne_one]
    exact ⟨zero_le_one, le_rfl⟩

/-- The closure of a boundary edge reaches `ℂ ∖ Δ`. -/
theorem fx_p4_edge_bdry_closure {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) {i : ι} (hi : dst i = none) :
    (closure (par i '' Ioo 0 1) ∩ unitDiscᶜ).Nonempty := by
  by_contra h
  have hsub : closure (par i '' Ioo 0 1) ⊆ unitDisc := fun x hx => by
    by_contra hx'
    exact h ⟨x, hx, hx'⟩
  have hK : IsCompact (closure (par i '' Ioo 0 1)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure (Metric.isBounded_ball.subset hsub)
  have hev := hF.bdry i hi _ hK hsub
  have hev2 : ∀ᶠ t in 𝓝[<] (1 : ℝ), par i t ∈ closure (par i '' Ioo 0 1) := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with t ht
    exact subset_closure ⟨t, ht, rfl⟩
  obtain ⟨t, h1, h2⟩ := (hev.and hev2).exists
  exact h1 h2

/-- **The complement of `Δ ∖ cutSet` is preconnected**: every picked edge hangs, through edges of
decreasing rank, down to `ℂ ∖ Δ`. -/
theorem fx_p4_cut_compl_preconn {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst)
    {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι} {rk : ℂ → ℕ}
    (hpick : fx_IsCutChoice φ src dst pick rk) :
    IsPreconnected (unitDisc \ fx_cutSet φ par pick)ᶜ := by
  set C := (unitDisc \ fx_cutSet φ par pick)ᶜ with hC
  have hCmem : ∀ x, x ∉ unitDisc → x ∈ C := fun x hx h => hx h.1
  have hcut : ∀ x ∈ fx_cutSet φ par pick, x ∈ C := fun x hx h => h.2 hx
  have hclC : ∀ q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0},
      closure (par (pick q) '' Ioo 0 1) ⊆ C := by
    intro q x hx
    by_cases hxD : x ∈ unitDisc
    · apply hcut
      rcases fx_p4_edge_closure hF (pick q) hxD hx with h | h | h
      · exact Or.inr (mem_iUnion.2 ⟨q, h⟩)
      · exact Or.inl ⟨hxD, h ▸ (hF.src_zero _).2.2⟩
      · exact Or.inl ⟨hxD, (hF.saddle _ x h).2.1⟩
    · exact hCmem x hxD
  have hA : ∀ n, ∀ q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}, rk q.1 = n →
      ∃ A : Set ℂ, IsPreconnected A ∧ A ⊆ C ∧ q.1 ∈ A ∧
        closure (par (pick q) '' Ioo 0 1) ⊆ A ∧ (A ∩ unitDiscᶜ).Nonempty := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih q hqn
    have hcc := fx_p4_edge_closure_conn hF (pick q)
    rcases hpick q with ⟨hs, hd⟩ | ⟨hd, hs⟩
    · rcases hdi : dst (pick q) with _ | q'
      · refine ⟨closure (par (pick q) '' Ioo 0 1), hcc.isPreconnected, hclC q, ?_, subset_rfl,
          fx_p4_edge_bdry_closure hF hdi⟩
        rw [← hs]
        exact fx_p4_edge_src_mem hF _
      · obtain ⟨hq'D, hq'0, -⟩ := hF.saddle _ q' hdi
        have hlt := hd q' hdi
        obtain ⟨A', hA'c, hA'C, hq'A', -, hA'b⟩ :=
          ih (rk q') (hqn ▸ hlt) ⟨q', hq'D, hq'0⟩ rfl
        refine ⟨closure (par (pick q) '' Ioo 0 1) ∪ A',
          hcc.isPreconnected.union q' (fx_p4_edge_dst_mem hF hdi) hq'A' hA'c,
          union_subset (hclC q) hA'C, ?_, subset_union_left,
          hA'b.mono (inter_subset_inter_left _ subset_union_right)⟩
        left
        rw [← hs]
        exact fx_p4_edge_src_mem hF _
    · have hsD := (hF.src_zero (pick q)).2
      obtain ⟨A', hA'c, hA'C, hsA', -, hA'b⟩ :=
        ih (rk (src (pick q))) (hqn ▸ hs) ⟨src (pick q), hsD.1, hsD.2⟩ rfl
      exact ⟨closure (par (pick q) '' Ioo 0 1) ∪ A',
        hcc.isPreconnected.union (src (pick q)) (fx_p4_edge_src_mem hF _) hsA' hA'c,
        union_subset (hclC q) hA'C, Or.inl (fx_p4_edge_dst_mem hF hd), subset_union_left,
        hA'b.mono (inter_subset_inter_left _ subset_union_right)⟩
  choose A hAc hAC hqA hclA hAb using
    fun q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} => hA (rk q.1) q rfl
  have hext : IsPreconnected (unitDiscᶜ : Set ℂ) := by
    have : (unitDiscᶜ : Set ℂ) = {z : ℂ | 1 ≤ ‖z‖} := by
      ext z
      simp [unitDisc]
    rw [this]
    exact isPreconnected_normGE zero_le_one
  have h2 : (2 : ℂ) ∈ (unitDiscᶜ : Set ℂ) := by
    simp only [unitDisc, mem_compl_iff, mem_ball, dist_zero_right, not_lt]
    norm_num
  set B : Option {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → Set ℂ :=
    fun o => o.elim unitDiscᶜ (fun q => A q ∪ unitDiscᶜ) with hB
  have hCeq : C = ⋃ o, B o := by
    ext x
    constructor
    · intro hx
      by_cases hxD : x ∈ unitDisc
      · have hxc : x ∈ fx_cutSet φ par pick := by
          by_contra h
          exact hx ⟨hxD, h⟩
        rcases hxc with ⟨-, hx0⟩ | hxe
        · exact mem_iUnion.2 ⟨some ⟨x, hxD, hx0⟩, Or.inl (hqA _)⟩
        · obtain ⟨q, hq⟩ := mem_iUnion.1 hxe
          exact mem_iUnion.2 ⟨some q, Or.inl (hclA q (subset_closure hq))⟩
      · exact mem_iUnion.2 ⟨none, hxD⟩
    · intro hx
      obtain ⟨o, ho⟩ := mem_iUnion.1 hx
      rcases o with _ | q
      · exact hCmem x ho
      · rcases ho with ho | ho
        · exact hAC q ho
        · exact hCmem x ho
  rw [hCeq]
  refine isPreconnected_iUnion ⟨2, mem_iInter.2 fun o => ?_⟩ fun o => ?_
  · rcases o with _ | q
    · exact h2
    · exact Or.inr h2
  · rcases o with _ | q
    · exact hext
    · obtain ⟨y, hyA, hyD⟩ := hAb q
      exact (hAc q).union y hyA hyD hext

/-- Each component of an open `Ω ⊆ Δ` whose complement is preconnected has connected complement in
`ℂ̄`. -/
theorem fx_p4_comp_compl_conn {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩD : Ω ⊆ unitDisc)
    (hC : IsPreconnected Ωᶜ) (x₀ : ℂ) :
    IsConnected (toExt (connectedComponentIn Ω x₀))ᶜ := by
  set U := connectedComponentIn Ω x₀ with hU
  have h2 : (2 : ℂ) ∈ Ωᶜ := fun h => by
    have := hΩD h
    simp only [unitDisc, mem_ball, dist_zero_right] at this
    norm_num at this
  have hV : ∀ x ∈ Ω, IsPreconnected (connectedComponentIn Ω x ∪ Ωᶜ) := by
    intro x hx
    have hVc : IsPreconnected (connectedComponentIn Ω x) := isPreconnected_connectedComponentIn
    obtain ⟨c, hcV, hcC⟩ : (closure (connectedComponentIn Ω x) ∩ Ωᶜ).Nonempty := by
      by_contra hne
      have hsub : closure (connectedComponentIn Ω x) ⊆ Ω := fun y hy => by
        by_contra h'
        exact hne ⟨y, hy, h'⟩
      have hcl : closure (connectedComponentIn Ω x) ⊆ connectedComponentIn Ω x :=
        hVc.closure.subset_connectedComponentIn
          (subset_closure (mem_connectedComponentIn hx)) hsub
      have hclopen : IsClopen (connectedComponentIn Ω x) :=
        ⟨closure_subset_iff_isClosed.1 hcl, hΩo.connectedComponentIn⟩
      rcases isClopen_iff.1 hclopen with h | h
      · have := mem_connectedComponentIn hx
        rw [h] at this
        exact this
      · have : (2 : ℂ) ∈ connectedComponentIn Ω x := h ▸ mem_univ _
        exact h2 (connectedComponentIn_subset _ _ this)
    have h1 : IsPreconnected (connectedComponentIn Ω x ∪ {c}) :=
      hVc.subset_closure subset_union_left
        (union_subset subset_closure (singleton_subset_iff.2 hcV))
    have h3 := h1.union c (Or.inr rfl) hcC hC
    have : connectedComponentIn Ω x ∪ {c} ∪ Ωᶜ = connectedComponentIn Ω x ∪ Ωᶜ := by
      ext y
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · rw [mem_singleton_iff.1 h]
          exact Or.inr hcC
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    rwa [this] at h3
  have hUc : IsPreconnected Uᶜ := by
    have heq : Uᶜ = ⋃₀ (insert Ωᶜ ((fun x => connectedComponentIn Ω x ∪ Ωᶜ) '' (Ω \ U))) := by
      ext y
      constructor
      · intro hy
        by_cases hyΩ : y ∈ Ω
        · exact ⟨_, Or.inr ⟨y, ⟨hyΩ, hy⟩, rfl⟩, Or.inl (mem_connectedComponentIn hyΩ)⟩
        · exact ⟨Ωᶜ, Or.inl rfl, hyΩ⟩
      · rintro ⟨S, hS, hyS⟩
        rcases hS with rfl | ⟨x, ⟨hxΩ, hxU⟩, rfl⟩
        · exact fun hyU => hyS (connectedComponentIn_subset _ _ hyU)
        · rcases hyS with hyV | hyC
          · intro hyU
            apply hxU
            have e1 : connectedComponentIn Ω x = connectedComponentIn Ω y :=
              connectedComponentIn_eq hyV
            have e2 : connectedComponentIn Ω x₀ = connectedComponentIn Ω y :=
              connectedComponentIn_eq hyU
            rw [hU, e2, ← e1]
            exact mem_connectedComponentIn hxΩ
          · exact fun hyU => hyC (connectedComponentIn_subset _ _ hyU)
    rw [heq]
    refine isPreconnected_sUnion 2 _ ?_ ?_
    · rintro S (rfl | ⟨x, -, rfl⟩)
      · exact h2
      · exact Or.inr h2
    · rintro S (rfl | ⟨x, ⟨hxΩ, -⟩, rfl⟩)
      · exact hC
      · exact hV x hxΩ
  rw [compl_toExt]
  refine ⟨⟨extInf, Or.inr rfl⟩, ?_⟩
  have hK : IsPreconnected (toExt Uᶜ) := hUc.image _ OnePoint.continuous_coe.continuousOn
  refine hK.subset_closure subset_union_left
    (union_subset subset_closure (singleton_subset_iff.2 ?_))
  refine extInf_mem_closure_toExt_of_unbounded fun R => ⟨((|R| + 2 : ℝ) : ℂ), ?_, ?_⟩
  · intro hU'
    have := hΩD (connectedComponentIn_subset _ _ hU')
    rw [unitDisc, mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)] at this
    linarith [abs_nonneg R]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith [le_abs_self R]

/-- **A primitive of `√φ` on the complement of the cuts** (componentwise, through the
connected-complement bridge). -/
theorem fx_p4_cut_primitive {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι}
    {rk : ℂ → ℕ} (hpick : fx_IsCutChoice φ src dst pick rk) :
    ∃ Φ : ℂ → ℂ, DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par pick) ∧
      ∀ z ∈ unitDisc \ fx_cutSet φ par pick, deriv Φ z ^ 2 = φ z := by
  set Ω := unitDisc \ fx_cutSet φ par pick with hΩ
  have hΩo : IsOpen Ω := fx_p4_cut_isOpen hρ hφ hF pick
  have hΩD : Ω ⊆ unitDisc := sdiff_subset
  have hC := fx_p4_cut_compl_preconn hF hpick
  have hcomp : ∀ U : Set ℂ, ∃ F : ℂ → ℂ, (∃ x ∈ Ω, U = connectedComponentIn Ω x) →
      DifferentiableOn ℂ F U ∧ ∀ w ∈ U, deriv F w ^ 2 = φ w := by
    intro U
    by_cases hU : ∃ x ∈ Ω, U = connectedComponentIn Ω x
    · obtain ⟨x, hx, rfl⟩ := hU
      have hVo : IsOpen (connectedComponentIn Ω x) := hΩo.connectedComponentIn
      have hVc : IsConnected (connectedComponentIn Ω x) :=
        isConnected_connectedComponentIn_iff.2 hx
      have hVcc := fx_p4_comp_compl_conn hΩo hΩD hC x
      have hVΩ : connectedComponentIn Ω x ⊆ Ω := connectedComponentIn_subset _ _
      have hφV : DifferentiableOn ℂ φ (connectedComponentIn Ω x) :=
        hφ.mono (hVΩ.trans (hΩD.trans (ball_subset_ball hρ.le)))
      have hφne : ∀ z ∈ connectedComponentIn Ω x, φ z ≠ 0 := fun z hz h0 =>
        (hVΩ hz).2 (Or.inl ⟨(hVΩ hz).1, h0⟩)
      obtain ⟨L, hL, hLe⟩ := exists_log_of_isConnected_compl hVo hVc hVcc hφV hφne
      have hs : DifferentiableOn ℂ (fun z => exp (L z / 2)) (connectedComponentIn Ω x) :=
        (hL.div_const 2).cexp
      have hs2 : ∀ z ∈ connectedComponentIn Ω x, exp (L z / 2) ^ 2 = φ z := by
        intro z hz
        rw [← Complex.exp_nat_mul, ← hLe z hz]
        congr 1
        push_cast
        ring
      have hzero : ∀ v : List ℂ, polyTrace v ⊆ connectedComponentIn Ω x →
          polyIntegral (fun z => exp (L z / 2)) v = 0 := fun v hv =>
        polyIntegral_eq_zero_of_polyWinding_eq_zero hVo hs hv fun a ha =>
          polyWinding_eq_zero_of_isConnected_compl hVcc hv ha
      obtain ⟨F, hFd, hF'⟩ := exists_primitive_of_polyIntegral_eq_zero hVo hVc hs hzero
      exact ⟨F, fun _ => ⟨hFd, fun w hw => by rw [hF' w hw]; exact hs2 w hw⟩⟩
    · exact ⟨0, fun h => absurd h hU⟩
  choose Fc hFc using hcomp
  have hloc : ∀ z ∈ Ω, (fun w => Fc (connectedComponentIn Ω w) w) =ᶠ[𝓝 z]
      Fc (connectedComponentIn Ω z) := by
    intro z hz
    filter_upwards [hΩo.connectedComponentIn.mem_nhds (mem_connectedComponentIn hz)] with w hw
    rw [← connectedComponentIn_eq hw]
  refine ⟨fun w => Fc (connectedComponentIn Ω w) w, fun z hz => ?_, fun z hz => ?_⟩
  · have hd := (hFc _ ⟨z, hz, rfl⟩).1
    have hda : DifferentiableAt ℂ (Fc (connectedComponentIn Ω z)) z :=
      hd.differentiableAt (hΩo.connectedComponentIn.mem_nhds (mem_connectedComponentIn hz))
    exact ((hloc z hz).differentiableAt_iff.2 hda).differentiableWithinAt
  · rw [(hloc z hz).deriv_eq]
    exact (hFc _ ⟨z, hz, rfl⟩).2 z (mem_connectedComponentIn hz)

/-- `|Φ'| = |φ|^{1/2}` is bounded on `Δ` for tame `φ`. -/
theorem fx_p4_cut_bound {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {Ω : Set ℂ} (hΩD : Ω ⊆ unitDisc) {Φ : ℂ → ℂ} (hΦ2 : ∀ z ∈ Ω, deriv Φ z ^ 2 = φ z) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Ω, ‖deriv Φ z‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (hφ.continuousOn.mono (closedBall_subset_ball hρ))
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun z hz => ?_⟩
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (mem_closedBall_self zero_le_one))
  rw [Real.le_sqrt (norm_nonneg _) hC0, ← norm_pow, hΦ2 z hz]
  exact hC z (ball_subset_closedBall (hΩD hz))

/-- The oscillation of `Re Φ` through `Ω` at `x` is at most `ε`. -/
def fx_p4_OscLe (Ω : Set ℂ) (Φ : ℂ → ℂ) (ε : ℝ) (x : ℂ) : Prop :=
  ∀ δ > 0, ∃ W ∈ 𝓝 x, ∀ w ∈ W ∩ Ω, ∀ w' ∈ W ∩ Ω, |(Φ w).re - (Φ w').re| ≤ ε + δ

/-- The extension of `Re Φ` from `Ω` by limits. -/
def fx_p4_uext (Ω : Set ℂ) (Φ : ℂ → ℂ) (x : ℂ) : ℝ :=
  limUnder (𝓝[Ω] x) (fun w => (Φ w).re)

/-- An oscillation bound for every `ε > 0` gives oscillation `0`. -/
theorem fx_p4_osc_zero_of_forall {Ω : Set ℂ} {Φ : ℂ → ℂ} {x : ℂ}
    (h : ∀ ε > 0, fx_p4_OscLe Ω Φ ε x) : fx_p4_OscLe Ω Φ 0 x := by
  intro δ hδ
  obtain ⟨W, hW, hb⟩ := h (δ / 2) (by linarith) (δ / 2) (by linarith)
  exact ⟨W, hW, fun w hw w' hw' => (hb w hw w' hw').trans (by linarith)⟩

/-- `Re Φ` has oscillation `0` at the points of `Ω` where `Φ` is continuous. -/
theorem fx_p4_osc_of_mem {Ω : Set ℂ} (hΩo : IsOpen Ω) {Φ : ℂ → ℂ} (hΦ : ContinuousOn Φ Ω) {x : ℂ}
    (hx : x ∈ Ω) : fx_p4_OscLe Ω Φ 0 x := by
  intro δ hδ
  have hc : ContinuousAt (fun w => (Φ w).re) x :=
    Complex.continuous_re.continuousAt.comp (hΦ.continuousAt (hΩo.mem_nhds hx))
  have hev := Metric.tendsto_nhds.1 hc (δ / 2) (by linarith)
  refine ⟨{w | dist (Φ w).re (Φ x).re < δ / 2}, hev, fun w hw w' hw' => ?_⟩
  have h1 : dist (Φ w).re (Φ x).re < δ / 2 := hw.1
  have h2 : dist (Φ w').re (Φ x).re < δ / 2 := hw'.1
  rw [Real.dist_eq] at h1 h2
  calc |(Φ w).re - (Φ w').re| ≤ |(Φ w).re - (Φ x).re| + |(Φ w').re - (Φ x).re| := by
        rw [abs_sub_comm ((Φ w').re)]
        exact abs_sub_le _ _ _
    _ ≤ 0 + δ := by linarith

/-- At a point of oscillation `0` in the closure of `Ω`, `Re Φ` tends to `fx_p4_uext`. -/
theorem fx_p4_uext_tendsto {Ω : Set ℂ} {Φ : ℂ → ℂ} {x : ℂ} (hx : fx_p4_OscLe Ω Φ 0 x)
    (hxc : x ∈ closure Ω) :
    Tendsto (fun w => (Φ w).re) (𝓝[Ω] x) (𝓝 (fx_p4_uext Ω Φ x)) := by
  have hne : (𝓝[Ω] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxc
  apply tendsto_nhds_limUnder
  rw [← cauchy_map_iff_exists_tendsto, Metric.cauchy_iff]
  refine ⟨hne.map _, fun ε hε => ?_⟩
  obtain ⟨W, hW, hb⟩ := hx (ε / 2) (by linarith)
  refine ⟨(fun w => (Φ w).re) '' (W ∩ Ω), ?_, ?_⟩
  · rw [mem_map]
    exact mem_of_superset (inter_mem_nhdsWithin Ω hW) (fun w hw => ⟨w, ⟨hw.2, hw.1⟩, rfl⟩)
  · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    rw [Real.dist_eq]
    linarith [hb w hw w' hw']

/-- On `Ω`, `fx_p4_uext Ω Φ = Re Φ`. -/
theorem fx_p4_uext_eq {Ω : Set ℂ} (hΩo : IsOpen Ω) {Φ : ℂ → ℂ} (hΦ : ContinuousOn Φ Ω) {x : ℂ}
    (hx : x ∈ Ω) : fx_p4_uext Ω Φ x = (Φ x).re := by
  have hne : (𝓝[Ω] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hx)
  have hc : Tendsto (fun w => (Φ w).re) (𝓝[Ω] x) (𝓝 (Φ x).re) :=
    (Complex.continuous_re.continuousAt.comp
      (hΦ.continuousAt (hΩo.mem_nhds hx))).tendsto.mono_left nhdsWithin_le_nhds
  exact hc.limUnder_eq

/-- `fx_p4_uext` is continuous at a point all of whose nearby points have oscillation `0` and lie in
the closure of `Ω`. -/
theorem fx_p4_uext_continuousAt {Ω : Set ℂ} {Φ : ℂ → ℂ} {x : ℂ}
    (h : ∀ᶠ y in 𝓝 x, fx_p4_OscLe Ω Φ 0 y ∧ y ∈ closure Ω) : ContinuousAt (fx_p4_uext Ω Φ) x := by
  have hx := h.self_of_nhds
  have hT := fx_p4_uext_tendsto hx.1 hx.2
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨W, hW, hb⟩ : ∃ W ∈ 𝓝 x, ∀ w ∈ W ∩ Ω, |(Φ w).re - fx_p4_uext Ω Φ x| < ε / 2 := by
    have h1 := Metric.tendsto_nhds.1 hT (ε / 2) (by linarith)
    rw [eventually_nhdsWithin_iff] at h1
    exact ⟨_, h1, fun w hw => by have h2 := hw.1 hw.2; rwa [Real.dist_eq] at h2⟩
  filter_upwards [h, eventually_eventually_nhds.2 hW] with y hy hyW
  have hTy := fx_p4_uext_tendsto hy.1 hy.2
  have hne : (𝓝[Ω] y).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hy.2
  have hev : ∀ᶠ w in 𝓝[Ω] y,
      (Φ w).re ∈ Icc (fx_p4_uext Ω Φ x - ε / 2) (fx_p4_uext Ω Φ x + ε / 2) := by
    filter_upwards [nhdsWithin_le_nhds hyW, self_mem_nhdsWithin] with w hw hwΩ
    have h3 := hb w ⟨hw, hwΩ⟩
    rw [abs_lt] at h3
    exact ⟨by linarith, by linarith⟩
  have hmem := isClosed_Icc.mem_of_tendsto hTy hev
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

/-- **Lipschitz bound without an a.e. argument**: a continuous `f` on `[a, b]` with `|f'| ≤ L` at
the points of an open set `O`, whose values off `O` form a countable set, satisfies
`|f b - f a| ≤ L (b - a)` (the image has measure `≤ L (b - a)` and contains `[f a, f b]`). -/
theorem fx_p4_abs_sub_le {f : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b) (hL : 0 ≤ L)
    (hf : ContinuousOn f (Icc a b)) {O : Set ℝ} (hO : IsOpen O)
    (hd : ∀ t ∈ Ioo a b ∩ O, ∃ f' : ℝ, HasDerivAt f f' t ∧ |f'| ≤ L)
    (hbad : (f '' (Icc a b \ O)).Countable) : |f b - f a| ≤ L * (b - a) := by
  classical
  have hd' : ∀ t, ∃ f' : ℝ, t ∈ Ioo a b ∩ O → HasDerivAt f f' t ∧ |f'| ≤ L := by
    intro t
    by_cases ht : t ∈ Ioo a b ∩ O
    · obtain ⟨f', h1, h2⟩ := hd t ht
      exact ⟨f', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose F hF using hd'
  have hsm : MeasurableSet (Ioo a b ∩ O) := measurableSet_Ioo.inter hO.measurableSet
  have himg : volume (f '' (Ioo a b ∩ O)) ≤ ENNReal.ofReal (L * (b - a)) := by
    have h1 := addHaar_image_le_lintegral_abs_det_fderiv volume hsm
      (f' := fun t => (1 : ℝ →L[ℝ] ℝ).smulRight (F t))
      (fun t ht => (hF t ht).1.hasFDerivAt.hasFDerivWithinAt)
    refine h1.trans ?_
    calc ∫⁻ t in Ioo a b ∩ O, ENNReal.ofReal |((1 : ℝ →L[ℝ] ℝ).smulRight (F t)).det|
        ≤ ∫⁻ _ in Ioo a b ∩ O, ENNReal.ofReal L := by
          refine setLIntegral_mono measurable_const fun t ht => ?_
          apply ENNReal.ofReal_le_ofReal
          simpa using (hF t ht).2
      _ = ENNReal.ofReal L * volume (Ioo a b ∩ O) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal (b - a) := by
          gcongr
          calc volume (Ioo a b ∩ O) ≤ volume (Ioo a b) := measure_mono inter_subset_left
            _ = ENNReal.ofReal (b - a) := Real.volume_Ioo
      _ = ENNReal.ofReal (L * (b - a)) := (ENNReal.ofReal_mul hL).symm
  have hbadnull : volume (f '' (Icc a b \ (Ioo a b ∩ O))) = 0 := by
    have hsub : f '' (Icc a b \ (Ioo a b ∩ O)) ⊆ {f a, f b} ∪ f '' (Icc a b \ O) := by
      rintro _ ⟨t, ⟨ht, hts⟩, rfl⟩
      by_cases htO : t ∈ O
      · have : t = a ∨ t = b := by
          by_contra h
          push Not at h
          exact hts ⟨⟨lt_of_le_of_ne ht.1 (Ne.symm h.1), lt_of_le_of_ne ht.2 h.2⟩, htO⟩
        rcases this with rfl | rfl
        · exact Or.inl (Or.inl rfl)
        · exact Or.inl (Or.inr rfl)
      · exact Or.inr ⟨t, ⟨ht, htO⟩, rfl⟩
    exact measure_mono_null hsub (((Set.toFinite _).countable.union hbad).measure_zero volume)
  have hIVT : uIcc (f a) (f b) ⊆ f '' Icc a b := by
    have := intermediate_value_uIcc (a := a) (b := b) (f := f) (by rwa [uIcc_of_le hab])
    rwa [uIcc_of_le hab] at this
  have htot : ENNReal.ofReal |f b - f a| ≤ ENNReal.ofReal (L * (b - a)) := by
    rw [← Real.volume_interval]
    calc volume (uIcc (f a) (f b)) ≤ volume (f '' Icc a b) := measure_mono hIVT
      _ ≤ volume (f '' (Ioo a b ∩ O) ∪ f '' (Icc a b \ (Ioo a b ∩ O))) := by
          apply measure_mono
          rw [← image_union]
          apply image_mono
          intro t ht
          by_cases h : t ∈ Ioo a b ∩ O
          · exact Or.inl h
          · exact Or.inr ⟨ht, h⟩
      _ ≤ volume (f '' (Ioo a b ∩ O)) + volume (f '' (Icc a b \ (Ioo a b ∩ O))) :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (L * (b - a)) + 0 := add_le_add himg hbadnull.le
      _ = ENNReal.ofReal (L * (b - a)) := add_zero _
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hL (sub_nonneg.2 hab))).1 htot

/-- The Lipschitz bound along a `C¹` curve: if `u = Re Φ` on `Ω` with `|Φ'| ≤ M`, and `u ∘ c` is
continuous and takes countably many values off `Ω`, then `|u(c b) - u(c a)| ≤ M K (b - a)`. -/
theorem fx_p4_curve_bound {Ω : Set ℂ} (hΩo : IsOpen Ω) {Φ : ℂ → ℂ} (hΦd : DifferentiableOn ℂ Φ Ω)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z ∈ Ω, ‖deriv Φ z‖ ≤ M) {u : ℂ → ℝ}
    (hu : ∀ z ∈ Ω, u z = (Φ z).re) {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ t, ‖c' t‖ ≤ K) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn (fun t => u (c t)) (Icc a b))
    (hbad : ((fun t => u (c t)) '' (Icc a b \ c ⁻¹' Ω)).Countable) :
    |u (c b) - u (c a)| ≤ M * K * (b - a) := by
  have hcc : Continuous c := continuous_iff_continuousAt.2 fun t => (hc t).continuousAt
  refine fx_p4_abs_sub_le hab (mul_nonneg hM0 hK0) hcont (hΩo.preimage hcc) (fun t ht => ?_) hbad
  have htΩ : c t ∈ Ω := ht.2
  have hΦt : HasDerivAt Φ (deriv Φ (c t)) (c t) :=
    (hΦd.differentiableAt (hΩo.mem_nhds htΩ)).hasDerivAt
  have h1 : HasDerivAt (fun s => Φ (c s)) (deriv Φ (c t) * c' t) t := hΦt.comp t (hc t)
  have h2 : HasDerivAt (fun s => (Φ (c s)).re) (Complex.reCLM (deriv Φ (c t) * c' t)) t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
  rw [Complex.reCLM_apply] at h2
  have hev : (fun s => u (c s)) =ᶠ[𝓝 t] (fun s => (Φ (c s)).re) := by
    filter_upwards [hcc.continuousAt.preimage_mem_nhds (hΩo.mem_nhds htΩ)] with s hs
    exact hu _ hs
  refine ⟨_, h2.congr_of_eventuallyEq hev, ?_⟩
  calc |(deriv Φ (c t) * c' t).re| ≤ ‖deriv Φ (c t) * c' t‖ := Complex.abs_re_le_norm _
    _ = ‖deriv Φ (c t)‖ * ‖c' t‖ := norm_mul _ _
    _ ≤ M * K := mul_le_mul (hM _ htΩ) (hK t) (norm_nonneg _) hM0

/-- In a flow box straddling a cut, the oscillation of `Re Φ` at a point of the cut plaque is the
jump `|vP - vM|` between the two sides. -/
theorem fx_p4_box_osc {φ ζ : ℂ → ℂ} {N Ω : Set ℂ} (hN : fx_IsFlowBox φ ζ N) {a : ℝ}
    (hΩN : ∀ z ∈ N, z ∈ Ω ↔ (ζ z).re ≠ a) {Φ : ℂ → ℂ} {vP vM : ℝ}
    (hvP : ∀ z ∈ N, a < (ζ z).re → |(Φ z).re - vP| = |(ζ z).re - a|)
    (hvM : ∀ z ∈ N, (ζ z).re < a → |(Φ z).re - vM| = |(ζ z).re - a|) {x : ℂ} (hx : x ∈ N)
    (hxa : (ζ x).re = a) {ε : ℝ} (hε : 0 ≤ ε) : fx_p4_OscLe Ω Φ ε x ↔ |vP - vM| ≤ ε := by
  have hζc : ContinuousOn ζ N := (fx_p4_flowBox_diffOn hN).continuousOn
  constructor
  · intro hosc
    by_contra hlt
    push Not at hlt
    set δ := (|vP - vM| - ε) / 3 with hδ
    have hδp : 0 < δ := by rw [hδ]; linarith
    obtain ⟨W, hW, hWb⟩ := hosc δ hδp
    obtain ⟨O, hOW, hOo, hxO⟩ := _root_.mem_nhds_iff.1 hW
    have hOpen : IsOpen (ζ '' (O ∩ N)) :=
      fx_p4_flowBox_isOpen_image hN (hOo.inter hN.1) inter_subset_right
    obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hOpen (ζ x) ⟨x, ⟨hxO, hx⟩, rfl⟩
    set s := min η δ / 2 with hs
    have hs0 : 0 < s := by positivity
    have hsη : s < η := by rw [hs]; linarith [min_le_left η δ]
    have hsδ : s < δ := by rw [hs]; linarith [min_le_right η δ]
    have hmem : ∀ σ : ℝ, |σ| = s → ζ x + σ ∈ ζ '' (O ∩ N) := fun σ hσ => hball (by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, hσ]
      exact hsη)
    obtain ⟨wP, ⟨hwPO, hwPN⟩, hwP⟩ := hmem s (abs_of_pos hs0)
    obtain ⟨wM, ⟨hwMO, hwMN⟩, hwM⟩ := hmem (-s) (by rw [abs_neg, abs_of_pos hs0])
    have hreP : (ζ wP).re = a + s := by rw [hwP, add_re, ofReal_re, hxa]
    have hreM : (ζ wM).re = a - s := by
      rw [hwM, add_re, ofReal_re, hxa]
      ring
    have hwPΩ : wP ∈ Ω := (hΩN wP hwPN).2 (by rw [hreP]; linarith)
    have hwMΩ : wM ∈ Ω := (hΩN wM hwMN).2 (by rw [hreM]; linarith)
    have eP := hvP wP hwPN (by rw [hreP]; linarith)
    have eM := hvM wM hwMN (by rw [hreM]; linarith)
    rw [hreP, add_sub_cancel_left, abs_of_pos hs0] at eP
    rw [hreM, show a - s - a = -s by ring, abs_neg, abs_of_pos hs0] at eM
    have hb := hWb wP ⟨hOW hwPO, hwPΩ⟩ wM ⟨hOW hwMO, hwMΩ⟩
    have htri := abs_add_three (-((Φ wP).re - vP)) ((Φ wP).re - (Φ wM).re) ((Φ wM).re - vM)
    rw [abs_neg, eP, eM, show -((Φ wP).re - vP) + ((Φ wP).re - (Φ wM).re) + ((Φ wM).re - vM) =
      vP - vM by ring] at htri
    linarith
  · intro hle δ hδ
    refine ⟨N ∩ (fun z => (ζ z).re) ⁻¹' ball a (δ / 2), ?_, fun w hw w' hw' => ?_⟩
    · have ho : IsOpen (N ∩ (fun z => (ζ z).re) ⁻¹' ball a (δ / 2)) :=
        (Complex.continuous_re.comp_continuousOn hζc).isOpen_inter_preimage hN.1 isOpen_ball
      refine ho.mem_nhds ⟨hx, ?_⟩
      show (ζ x).re ∈ ball a (δ / 2)
      rw [hxa]
      exact mem_ball_self (half_pos hδ)
    · have key : ∀ y ∈ (N ∩ (fun z => (ζ z).re) ⁻¹' ball a (δ / 2)) ∩ Ω,
          ∃ v ∈ ({vP, vM} : Set ℝ), |(Φ y).re - v| < δ / 2 := by
        rintro y ⟨⟨hyN, hyb⟩, hyΩ⟩
        have hya : (ζ y).re ≠ a := (hΩN y hyN).1 hyΩ
        have hyb' : |(ζ y).re - a| < δ / 2 := by
          have : (ζ y).re ∈ ball a (δ / 2) := hyb
          rwa [mem_ball, Real.dist_eq] at this
        rcases lt_or_gt_of_ne hya with h | h
        · exact ⟨vM, Or.inr rfl, by rw [hvM y hyN h]; exact hyb'⟩
        · exact ⟨vP, Or.inl rfl, by rw [hvP y hyN h]; exact hyb'⟩
      obtain ⟨v, hv, hwv⟩ := key w hw
      obtain ⟨v', hv', hwv'⟩ := key w' hw'
      have hvv : |v - v'| ≤ ε := by
        rcases hv with rfl | rfl <;> rcases hv' with rfl | rfl
        · simpa using hε
        · exact hle
        · rw [abs_sub_comm]
          exact hle
        · simpa using hε
      have htri := abs_add_three ((Φ w).re - v) (v - v') (-((Φ w').re - v'))
      rw [abs_neg, show (Φ w).re - v + (v - v') + -((Φ w').re - v') = (Φ w).re - (Φ w').re by
        ring] at htri
      linarith

/-- In a flow box without jump, `Re Φ` converges at the points of the cut plaque. -/
theorem fx_p4_box_tendsto {φ ζ : ℂ → ℂ} {N Ω : Set ℂ} (hN : fx_IsFlowBox φ ζ N) {a : ℝ}
    (hΩN : ∀ z ∈ N, z ∈ Ω ↔ (ζ z).re ≠ a) {Φ : ℂ → ℂ} {v : ℝ}
    (hvP : ∀ z ∈ N, a < (ζ z).re → |(Φ z).re - v| = |(ζ z).re - a|)
    (hvM : ∀ z ∈ N, (ζ z).re < a → |(Φ z).re - v| = |(ζ z).re - a|) {x : ℂ} (hx : x ∈ N)
    (hxa : (ζ x).re = a) : Tendsto (fun w => (Φ w).re) (𝓝[Ω] x) (𝓝 v) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have hζc : ContinuousOn ζ N := (fx_p4_flowBox_diffOn hN).continuousOn
  have ho : IsOpen (N ∩ (fun z => (ζ z).re) ⁻¹' ball a η) :=
    (Complex.continuous_re.comp_continuousOn hζc).isOpen_inter_preimage hN.1 isOpen_ball
  have hxo : x ∈ N ∩ (fun z => (ζ z).re) ⁻¹' ball a η := by
    refine ⟨hx, ?_⟩
    show (ζ x).re ∈ ball a η
    rw [hxa]
    exact mem_ball_self hη
  filter_upwards [nhdsWithin_le_nhds (ho.mem_nhds hxo), self_mem_nhdsWithin] with w hw hwΩ
  have hwa := (hΩN w hw.1).1 hwΩ
  have hwb : |(ζ w).re - a| < η := by
    have : (ζ w).re ∈ ball a η := hw.2
    rwa [mem_ball, Real.dist_eq] at this
  rw [Real.dist_eq]
  rcases lt_or_gt_of_ne hwa with h | h
  · rw [hvM w hw.1 h]
    exact hwb
  · rw [hvP w hw.1 h]
    exact hwb

/-- **The flow box along a cut edge**: the forest's box at an interior point of a picked edge meets
the cut set exactly in the edge's vertical plaque, and on each side `Re Φ = ± (Re ζ - a) + v±`. -/
theorem fx_p4_cut_box {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι}
    {Φ : ℂ → ℂ} (hΦd : DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par pick))
    (hΦ2 : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, deriv Φ z ^ 2 = φ z)
    (q₀ : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ (ζ : ℂ → ℂ) (N : Set ℂ), par (pick q₀) t ∈ N ∧ fx_IsFlowBox φ ζ N ∧
      (∀ z ∈ N, z ∈ unitDisc \ fx_cutSet φ par pick ↔ (ζ z).re ≠ (ζ (par (pick q₀) t)).re) ∧
      (∀ z ∈ N, z ∈ par (pick q₀) '' Ioo 0 1 ↔ (ζ z).re = (ζ (par (pick q₀) t)).re) ∧
      ∃ vP vM : ℝ,
        (∀ z ∈ N, (ζ (par (pick q₀) t)).re < (ζ z).re →
          |(Φ z).re - vP| = |(ζ z).re - (ζ (par (pick q₀) t)).re|) ∧
        (∀ z ∈ N, (ζ z).re < (ζ (par (pick q₀) t)).re →
          |(Φ z).re - vM| = |(ζ z).re - (ζ (par (pick q₀) t)).re|) := by
  obtain ⟨ζ, N, hpN, hN, hplaque, hother⟩ := hF.box (pick q₀) t ht
  set a := (ζ (par (pick q₀) t)).re with ha
  have heN : ∀ z ∈ N, z ∈ par (pick q₀) '' Ioo 0 1 ↔ (ζ z).re = a := by
    intro z hz
    constructor
    · intro h
      have : z ∈ par (pick q₀) '' Ioo 0 1 ∩ N := ⟨h, hz⟩
      rw [hplaque] at this
      exact this.2
    · intro h
      have : z ∈ {z | z ∈ N ∧ (ζ z).re = a} := ⟨hz, h⟩
      rw [← hplaque] at this
      exact this.1
  have hΩN : ∀ z ∈ N, z ∈ unitDisc \ fx_cutSet φ par pick ↔ (ζ z).re ≠ a := by
    intro z hz
    rw [← not_iff_not, not_not, ← heN z hz]
    constructor
    · intro h
      have hzc : z ∈ fx_cutSet φ par pick := by
        by_contra hc
        exact h ⟨hN.2.1 hz, hc⟩
      rcases hzc with ⟨-, hz0⟩ | hze
      · exact absurd hz0 (hN.2.2.2.1 z hz).1
      · obtain ⟨q, hq⟩ := mem_iUnion.1 hze
        by_cases hqi : pick q = pick q₀
        · rwa [hqi] at hq
        · have h' : z ∈ par (pick q) '' Ioo 0 1 ∩ N := ⟨hq, hz⟩
          rw [hother (pick q) hqi] at h'
          exact absurd h' (notMem_empty z)
    · intro h hΩ
      exact hΩ.2 (Or.inr (mem_iUnion.2 ⟨q₀, h⟩))
  have hζc : ContinuousOn ζ N := (fx_p4_flowBox_diffOn hN).continuousOn
  obtain ⟨c, δ, -, hsq⟩ := hN.2.2.2.2
  have hsqc : Convex ℝ (ζ '' N) := by
    rw [hsq]
    exact fx_p4_square_convex c δ
  have half : ∀ (H : Set ℂ), IsOpen H → Convex ℝ H → (∀ z ∈ N, ζ z ∈ H → (ζ z).re ≠ a) →
      ∃ v : ℝ, ∀ z ∈ N, ζ z ∈ H → |(Φ z).re - v| = |(ζ z).re - a| := by
    intro H hHo hHc hHa
    have hW : IsPreconnected (N ∩ ζ ⁻¹' (ζ '' N ∩ H)) :=
      fx_p4_flowBox_preimage_isPreconnected hN (hsqc.inter hHc).isPreconnected inter_subset_left
    have hWeq : N ∩ ζ ⁻¹' (ζ '' N ∩ H) = N ∩ ζ ⁻¹' H := by
      ext z
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, ⟨z, h.1, rfl⟩, h.2⟩⟩
    rw [hWeq] at hW
    have hWo : IsOpen (N ∩ ζ ⁻¹' H) := hζc.isOpen_inter_preimage hN.1 hHo
    have hWΩ : N ∩ ζ ⁻¹' H ⊆ unitDisc \ fx_cutSet φ par pick := fun z hz =>
      (hΩN z hz.1).2 (hHa z hz.1 hz.2)
    obtain ⟨v, hv⟩ := fx_p4_flowBox_re hN inter_subset_left hWo hW (hΦd.mono hWΩ)
      (fun z hz => hΦ2 z (hWΩ hz)) a
    exact ⟨v, fun z hz hzH => hv z ⟨hz, hzH⟩⟩
  obtain ⟨vP, hvP⟩ := half {w | a < w.re} (isOpen_lt continuous_const Complex.continuous_re)
    (convex_halfSpace_re_gt a) (fun z _ h => (ne_of_lt h).symm)
  obtain ⟨vM, hvM⟩ := half {w | w.re < a} (isOpen_lt Complex.continuous_re continuous_const)
    (convex_halfSpace_re_lt a) (fun z _ h => ne_of_lt h)
  exact ⟨ζ, N, hpN, hN, hΩN, heN, vP, vM, fun z hz h => hvP z hz h, fun z hz h => hvM z hz h⟩

/-- The oscillation bound propagates along a picked edge (it is locally constant along the
edge). -/
theorem fx_p4_edge_osc_all {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst)
    {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι} {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par pick))
    (hΦ2 : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, deriv Φ z ^ 2 = φ z)
    (q₀ : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}) {ε : ℝ} (hε : 0 ≤ ε) {t₁ t₂ : ℝ}
    (h₁ : t₁ ∈ Ioo (0 : ℝ) 1) (h₂ : t₂ ∈ Ioo (0 : ℝ) 1)
    (h : fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ ε (par (pick q₀) t₁)) :
    fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ ε (par (pick q₀) t₂) := by
  refine fx_p4_preconn_prop isPreconnected_Ioo
    (fun t => fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ ε (par (pick q₀) t)) ?_ h₁ h₂ h
  intro t ht
  obtain ⟨ζ, N, hpN, hN, hΩN, heN, vP, vM, hvP, hvM⟩ := fx_p4_cut_box hF hΦd hΦ2 q₀ ht
  have hcont : ContinuousAt (par (pick q₀)) t :=
    (hF.smooth _).continuousOn.continuousAt (Ico_mem_nhds ht.1 ht.2)
  have hev : ∀ᶠ t' in 𝓝 t, par (pick q₀) t' ∈ N := hcont.preimage_mem_nhds (hN.1.mem_nhds hpN)
  filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with t' ht'N ht'
  have ha' : (ζ (par (pick q₀) t')).re = (ζ (par (pick q₀) t)).re :=
    (heN _ ht'N).1 ⟨t', ht', rfl⟩
  rw [fx_p4_box_osc hN hΩN hvP hvM ht'N ha' hε, fx_p4_box_osc hN hΩN hvP hvM hpN rfl hε]

/-- Along a healed picked edge, `fx_p4_uext` is constant. -/
theorem fx_p4_edge_u_const {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst)
    {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι} {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par pick))
    (hΦ2 : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, deriv Φ z ^ 2 = φ z)
    (q₀ : {q : ℂ // q ∈ unitDisc ∧ φ q = 0})
    (hheal : ∀ t ∈ Ioo (0 : ℝ) 1,
      fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ 0 (par (pick q₀) t)) :
    ∃ c : ℝ, ∀ t ∈ Ioo (0 : ℝ) 1,
      fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ (par (pick q₀) t) = c := by
  have h12 : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  refine ⟨fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ (par (pick q₀) (1 / 2)), fun t ht => ?_⟩
  refine fx_p4_preconn_prop isPreconnected_Ioo
    (fun t => fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ (par (pick q₀) t) =
      fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ (par (pick q₀) (1 / 2))) ?_ h12 ht rfl
  intro t₀ ht₀
  obtain ⟨ζ, N, hpN, hN, hΩN, heN, vP, vM, hvP, hvM⟩ := fx_p4_cut_box hF hΦd hΦ2 q₀ ht₀
  have hjump : vP = vM := by
    have := (fx_p4_box_osc hN hΩN hvP hvM hpN rfl le_rfl).1 (hheal t₀ ht₀)
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  subst hjump
  have hval : ∀ t' ∈ Ioo (0 : ℝ) 1, par (pick q₀) t' ∈ N →
      fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ (par (pick q₀) t') = vP := by
    intro t' ht' ht'N
    have ha' := (heN _ ht'N).1 ⟨t', ht', rfl⟩
    have hT := fx_p4_box_tendsto hN hΩN hvP hvM ht'N ha'
    have hdense := fx_p4_cut_dense hF pick (fx_p4_edge_reg hF (pick q₀) ht').1
    have hne := mem_closure_iff_nhdsWithin_neBot.1 hdense
    exact tendsto_nhds_unique (fx_p4_uext_tendsto (hheal t' ht') hdense) hT
  have hcont : ContinuousAt (par (pick q₀)) t₀ :=
    (hF.smooth _).continuousOn.continuousAt (Ico_mem_nhds ht₀.1 ht₀.2)
  filter_upwards [nhdsWithin_le_nhds (hcont.preimage_mem_nhds (hN.1.mem_nhds hpN)),
    self_mem_nhdsWithin] with t' ht'N ht'
  rw [hval t' ht' ht'N, hval t₀ ht₀ hpN]

/-- **Radial crossing**: a curve leaving `q` with nonzero speed crosses each small circle around `q`
exactly once, with positive radial speed. -/
theorem fx_p4_radial_cross {γ γ' : ℝ → ℂ} {q d₀ : ℂ} (hc : ContinuousOn γ (Ico 0 1)) (h0 : γ 0 = q)
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt γ (γ' t) t) (hd₀ : d₀ ≠ 0)
    (hslope : Tendsto (slope γ 0) (𝓝[>] 0) (𝓝 d₀)) (hder : Tendsto γ' (𝓝[>] 0) (𝓝 d₀))
    (hfar : ∀ a ∈ Ioo (0 : ℝ) 1, ∃ r > 0, ∀ t ∈ Ico a 1, γ t ∉ ball q r) :
    ∃ r₁ > 0, ∀ r ∈ Ioo 0 r₁, ∃ t ∈ Ioo (0 : ℝ) 1, ‖γ t - q‖ = r ∧
      (∀ t' ∈ Ioo (0 : ℝ) 1, ‖γ t' - q‖ = r → t' = t) ∧
      0 < (starRingEnd ℂ (γ t - q) * γ' t).re := by
  have hlim : Tendsto (fun t => starRingEnd ℂ (slope γ 0 t) * γ' t) (𝓝[>] 0)
      (𝓝 (starRingEnd ℂ d₀ * d₀)) :=
    ((Complex.continuous_conj.tendsto d₀).comp hslope).mul hder
  have hpos : 0 < (starRingEnd ℂ d₀ * d₀).re := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_pos.2 hd₀
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < (starRingEnd ℂ (slope γ 0 t) * γ' t).re :=
    ((Complex.continuous_re.tendsto _).comp hlim).eventually (lt_mem_nhds hpos)
  obtain ⟨η, hη, hηsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hη0 : (0 : ℝ) < η := hη
  have hmin : 0 < min η 1 := lt_min hη0 zero_lt_one
  set b := min η 1 / 2 with hb
  have hb0 : 0 < b := by positivity
  have hbη : b < η := by linarith [min_le_left η 1]
  have hb1 : b < 1 := by linarith [min_le_right η 1]
  have hrad : ∀ t ∈ Ioo 0 η, 0 < (starRingEnd ℂ (γ t - q) * γ' t).re := by
    intro t ht
    have h1 : 0 < (starRingEnd ℂ (slope γ 0 t) * γ' t).re := hηsub ht
    rw [slope_def_module, h0, sub_zero, Complex.real_smul, map_mul, Complex.conj_ofReal,
      mul_assoc, Complex.re_ofReal_mul] at h1
    exact (mul_pos_iff_of_pos_left (inv_pos.2 ht.1)).1 h1
  have hcb : ContinuousOn γ (Icc 0 b) := hc.mono fun t ht => ⟨ht.1, ht.2.trans_lt hb1⟩
  have hmono : StrictMonoOn (fun t => ‖γ t - q‖ ^ 2) (Icc 0 b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 b)
    · exact ((hcb.sub continuousOn_const).norm).pow 2
    · intro t ht
      rw [interior_Icc] at ht
      have hD := ((hd t ⟨ht.1, ht.2.trans hb1⟩).sub_const q).norm_sq
      rw [hD.deriv, Complex.inner]
      have := hrad t ⟨ht.1, ht.2.trans hbη⟩
      rw [mul_comm] at this
      linarith
  obtain ⟨r₂, hr₂, hfar'⟩ := hfar b ⟨hb0, hb1⟩
  have hγb : 0 < ‖γ b - q‖ := by
    have := hmono ⟨le_rfl, hb0.le⟩ ⟨hb0.le, le_rfl⟩ hb0
    simp only [h0, sub_self, norm_zero] at this
    nlinarith [norm_nonneg (γ b - q)]
  refine ⟨min r₂ ‖γ b - q‖, lt_min hr₂ hγb, fun r hr => ?_⟩
  have hcn : ContinuousOn (fun t => ‖γ t - q‖) (Icc 0 b) := (hcb.sub continuousOn_const).norm
  have hrmem : r ∈ Ioo ((fun t => ‖γ t - q‖) 0) ((fun t => ‖γ t - q‖) b) := by
    refine ⟨?_, hr.2.trans_le (min_le_right _ _)⟩
    simp only [h0, sub_self, norm_zero]
    exact hr.1
  obtain ⟨t, ht, htr⟩ := intermediate_value_Ioo hb0.le hcn hrmem
  simp only at htr
  refine ⟨t, ⟨ht.1, ht.2.trans hb1⟩, htr, fun t' ht' ht'r => ?_, hrad t ⟨ht.1, ht.2.trans hbη⟩⟩
  have ht'b : t' < b := by
    by_contra h
    push Not at h
    have := hfar' t' ⟨h, ht'.2⟩
    rw [mem_ball, dist_eq_norm, not_lt, ht'r] at this
    linarith [hr.2.trans_le (min_le_left _ _)]
  exact hmono.injOn ⟨ht'.1.le, ht'b.le⟩ ⟨ht.1.le, ht.2.le⟩ (by simp only [ht'r, htr])

/-- A parametrization of an edge from one of its end zeros `q`, with nonzero initial speed and
continuous derivative up to `q`, which stays away from `q` on `[a, 1)`. -/
theorem fx_p4_edge_param {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) {i : ι} {q : ℂ}
    (hinc : fx_Incident src dst i q) :
    ∃ (γ γ' : ℝ → ℂ) (d₀ : ℂ), (∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ par i '' Ioo 0 1) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, ∃ t ∈ Ioo (0 : ℝ) 1, γ t = par i s) ∧
      ContinuousOn γ (Ico 0 1) ∧ γ 0 = q ∧ (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt γ (γ' t) t) ∧
      d₀ ≠ 0 ∧ Tendsto (slope γ 0) (𝓝[>] 0) (𝓝 d₀) ∧ Tendsto γ' (𝓝[>] 0) (𝓝 d₀) ∧
      ∀ a ∈ Ioo (0 : ℝ) 1, ∃ r > 0, ∀ t ∈ Ico a 1, γ t ∉ ball q r := by
  by_cases hsrc : src i = q
  · have hcd := hF.smooth i
    have hdiff : DifferentiableOn ℝ (par i) (Ico 0 1) := hcd.differentiableOn one_ne_zero
    have hIcoIcc : Ico (0 : ℝ) 1 =ᶠ[𝓝 0] Icc 0 1 := by
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with x hx
      exact ⟨fun h => ⟨h.1, h.2.le⟩, fun h => ⟨h.1, hx⟩⟩
    have hq : q ∈ unitDisc ∧ φ q = 0 := hsrc ▸ (hF.src_zero i).2
    refine ⟨par i, deriv (par i), derivWithin (par i) (Ico 0 1) 0, fun t ht => ⟨t, ht, rfl⟩,
      fun s hs => ⟨s, hs, rfl⟩, hcd.continuousOn, (hF.src_zero i).1.trans hsrc,
      fun t ht => (hdiff.differentiableAt (Ico_mem_nhds ht.1 ht.2)).hasDerivAt, ?_, ?_, ?_, ?_⟩
    · rw [derivWithin_congr_set hIcoIcc]
      exact hF.src_tan i
    · have h1 : HasDerivWithinAt (par i) (derivWithin (par i) (Ico 0 1) 0) (Ico 0 1) 0 :=
        (hdiff 0 ⟨le_rfl, zero_lt_one⟩).hasDerivWithinAt
      rw [hasDerivWithinAt_iff_tendsto_slope, Set.Ico_sdiff_left,
        nhdsWithin_Ioo_eq_nhdsGT zero_lt_one] at h1
      exact h1
    · have h1 : ContinuousWithinAt (derivWithin (par i) (Ico 0 1)) (Ico 0 1) 0 :=
        hcd.continuousOn_derivWithin (uniqueDiffOn_Ico 0 1) le_rfl 0 ⟨le_rfl, zero_lt_one⟩
      have h2 : Tendsto (derivWithin (par i) (Ico 0 1)) (𝓝[>] 0)
          (𝓝 (derivWithin (par i) (Ico 0 1) 0)) := by
        refine h1.tendsto.mono_left ?_
        rw [← nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
        exact nhdsWithin_mono _ Ioo_subset_Ico_self
      refine h2.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
      exact derivWithin_of_mem_nhds (Ico_mem_nhds ht.1 ht.2)
    · intro a ha
      refine fx_p4_avoid_Ico hF i ha.1.le ha.2 hq.1 (fun t ht h => ?_) (fun q' hq' h => ?_)
      · exact (fx_p4_edge_reg hF i ⟨ha.1.trans_le ht.1, ht.2⟩).2 (h ▸ hq.2)
      · exact (hF.saddle i q' hq').2.2.1 (h.trans hsrc.symm)
  · have hdq : dst i = some q := hinc.resolve_left hsrc
    obtain ⟨-, hq0, hqs, hcd, h1, hd1⟩ := hF.saddle i q hdq
    have hdiff : DifferentiableOn ℝ (par i) (Icc 0 1) := hcd.differentiableOn one_ne_zero
    refine ⟨fun t => par i (1 - t), fun t => -deriv (par i) (1 - t),
      -derivWithin (par i) (Icc 0 1) 1,
      fun t ht => ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩,
      fun s hs => ⟨1 - s, ⟨by linarith [hs.2], by linarith [hs.1]⟩, by simp⟩, ?_,
      by simp [h1], ?_, neg_ne_zero.2 hd1, ?_, ?_, ?_⟩
    · exact hcd.continuousOn.comp (continuousOn_const.sub continuousOn_id)
        (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    · intro t ht
      have hpar : HasDerivAt (par i) (deriv (par i) (1 - t)) (1 - t) :=
        (hdiff.differentiableAt
          (Icc_mem_nhds (by linarith [ht.2]) (by linarith [ht.1]))).hasDerivAt
      have h3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub 1
      have := hpar.scomp t h3
      simpa [Function.comp_def] using this
    · have h3 : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
      have hpar : HasDerivWithinAt (par i) (derivWithin (par i) (Icc 0 1) 1) (Icc 0 1)
          ((fun x : ℝ => 1 - x) 0) := by
        have e : (fun x : ℝ => 1 - x) 0 = 1 := by norm_num
        rw [e]
        exact (hdiff 1 ⟨zero_le_one, le_rfl⟩).hasDerivWithinAt
      have h2 := hpar.scomp (0 : ℝ) (h3.hasDerivWithinAt (s := Ico 0 1))
        (fun t ht => ⟨by show (0 : ℝ) ≤ 1 - t; linarith [ht.2],
          by show 1 - t ≤ (1 : ℝ); linarith [ht.1]⟩)
      rw [hasDerivWithinAt_iff_tendsto_slope, Set.Ico_sdiff_left,
        nhdsWithin_Ioo_eq_nhdsGT zero_lt_one] at h2
      simpa [Function.comp_def] using h2
    · have hcw : ContinuousWithinAt (derivWithin (par i) (Icc 0 1)) (Icc 0 1) 1 :=
        hcd.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl 1
          ⟨zero_le_one, le_rfl⟩
      have hmap : Tendsto (fun t : ℝ => 1 - t) (𝓝[>] 0) (𝓝[Icc 0 1] 1) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have : Tendsto (fun t : ℝ => 1 - t) (𝓝 0) (𝓝 (1 - 0)) :=
            tendsto_const_nhds.sub tendsto_id
          rw [sub_zero] at this
          exact this.mono_left nhdsWithin_le_nhds
        · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
          exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have h3 := (hcw.tendsto.comp hmap).neg
      refine h3.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
      simp only [Function.comp]
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds (by linarith [ht.2]) (by linarith [ht.1]))]
    · intro a ha
      obtain ⟨r, hr, hav⟩ := fx_p4_avoid_compact (a := 0) (b := 1 - a)
        (hcd.continuousOn.mono (Icc_subset_Icc le_rfl (by linarith [ha.1])))
        (fun s hs h => by
          rcases eq_or_lt_of_le hs.1 with h0 | h0
          · rw [← h0, (hF.src_zero i).1] at h
            exact hqs h.symm
          · exact (fx_p4_edge_reg hF i ⟨h0, by linarith [hs.2, ha.1]⟩).2 (h ▸ hq0))
      exact ⟨r, hr, fun t ht => hav (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩

/-- **Crossing of an edge with small circles** around an end zero `q`: a unique crossing point,
where a local parametrization of the edge has nonzero radial speed. -/
theorem fx_p4_edge_cross {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) {i : ι} {q : ℂ}
    (hinc : fx_Incident src dst i q) :
    ∃ r₁ > 0, ∀ r ∈ Ioo 0 r₁, ∃ p ∈ par i '' Ioo 0 1, ‖p - q‖ = r ∧
      (∀ p' ∈ par i '' Ioo 0 1, ‖p' - q‖ = r → p' = p) ∧
      ∃ (γ : ℝ → ℂ) (t : ℝ) (v : ℂ), γ t = p ∧ HasDerivAt γ v t ∧
        (∀ᶠ t' in 𝓝 t, γ t' ∈ par i '' Ioo 0 1) ∧ (starRingEnd ℂ (p - q) * v).re ≠ 0 := by
  obtain ⟨γ, γ', d₀, hγe, hγs, hc, h0, hd, hd₀, hslope, hder, hfar⟩ := fx_p4_edge_param hF hinc
  obtain ⟨r₁, hr₁, hcr⟩ := fx_p4_radial_cross hc h0 hd hd₀ hslope hder hfar
  refine ⟨r₁, hr₁, fun r hr => ?_⟩
  obtain ⟨t, ht, htr, huniq, hrad⟩ := hcr r hr
  refine ⟨γ t, hγe t ht, htr, fun p' hp' hp'r => ?_, γ, t, γ' t, rfl, hd t ht, ?_, hrad.ne'⟩
  · obtain ⟨s, hs, rfl⟩ := hp'
    obtain ⟨t', ht', ht's⟩ := hγs s hs
    rw [← ht's] at hp'r ⊢
    rw [huniq t' ht' hp'r]
  · filter_upwards [Ioo_mem_nhds ht.1 ht.2] with t' ht'
    exact hγe t' ht'

/-- The circle `θ ↦ q + r e^{iθ}` is differentiable. -/
theorem fx_p4_circle_hasDerivAt (q : ℂ) (r θ : ℝ) :
    HasDerivAt (fun θ : ℝ => q + (r : ℂ) * exp ((θ : ℂ) * I))
      ((r : ℂ) * exp ((θ : ℂ) * I) * I) θ := by
  have h : HasDerivAt (fun y : ℝ => exp ((y : ℂ) * I)) (exp ((θ : ℂ) * I) * I) θ := by
    simpa using (((hasDerivAt_id (θ : ℂ)).mul_const I).cexp).comp_ofReal
  have h2 := (h.const_mul (r : ℂ)).const_add q
  convert h2 using 1
  ring

/-- Points of the circle `θ ↦ q + r e^{iθ}` are at distance `r` from `q`. -/
theorem fx_p4_circle_norm (q : ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖q + (r : ℂ) * exp ((θ : ℂ) * I) - q‖ = r := by
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The circle `θ ↦ q + r e^{iθ}` has speed `r`. -/
theorem fx_p4_circle_deriv_norm {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖(r : ℂ) * exp ((θ : ℂ) * I) * I‖ = r := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
    Complex.norm_exp_ofReal_mul_I, Complex.norm_I, mul_one, mul_one]

/-- The circle through `p` reaches `p` at the argument of `p - q`. -/
theorem fx_p4_circle_arg {p q : ℂ} {r : ℝ} (hpr : ‖p - q‖ = r) :
    q + (r : ℂ) * exp ((arg (p - q) : ℂ) * I) = p := by
  rw [← hpr, Complex.norm_mul_exp_arg_mul_I]
  ring

/-- The circle is `2π`-periodic. -/
theorem fx_p4_circle_period (q : ℂ) (r θ : ℝ) :
    q + (r : ℂ) * exp (((θ + 2 * π : ℝ) : ℂ) * I) = q + (r : ℂ) * exp ((θ : ℂ) * I) := by
  rw [show ((θ + 2 * π : ℝ) : ℂ) * I = (θ : ℂ) * I + 2 * π * I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- Two parameters of the same point of the circle differ by a multiple of `2π`. -/
theorem fx_p4_circle_inj (q : ℂ) {r : ℝ} (hr : 0 < r) {θ θ' : ℝ}
    (h : q + (r : ℂ) * exp ((θ : ℂ) * I) = q + (r : ℂ) * exp ((θ' : ℂ) * I)) :
    ∃ n : ℤ, θ = θ' + n * (2 * π) := by
  have h1 : exp ((θ : ℂ) * I) = exp ((θ' : ℂ) * I) :=
    mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hr.ne') (add_left_cancel h)
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 h1
  refine ⟨n, ?_⟩
  have := congrArg Complex.im hn
  simp at this
  linarith

/-- A function vanishing at `θ₀` with nonzero derivative there changes sign across `θ₀`. -/
theorem fx_p4_sign_change {F : ℝ → ℝ} {F' θ₀ : ℝ} (hF : HasDerivAt F F' θ₀) (h0 : F θ₀ = 0)
    (hF' : F' ≠ 0) : ∀ᶠ δ in 𝓝[>] (0 : ℝ), F (θ₀ + δ) * F (θ₀ - δ) < 0 := by
  have hT := hasDerivAt_iff_tendsto_slope.1 hF
  have hT2 : Tendsto (fun θ => slope F θ₀ θ * F') (𝓝[≠] θ₀) (𝓝 (F' * F')) := hT.mul_const F'
  have hev : ∀ᶠ θ in 𝓝[≠] θ₀, 0 < slope F θ₀ θ * F' :=
    hT2.eventually (lt_mem_nhds (mul_self_pos.2 hF'))
  have hp : Tendsto (fun δ => θ₀ + δ) (𝓝[>] 0) (𝓝[≠] θ₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun δ : ℝ => θ₀ + δ) (𝓝 0) (𝓝 (θ₀ + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      intro h
      have h' : θ₀ + δ = θ₀ := h
      have hδ' : (0 : ℝ) < δ := hδ
      linarith
  have hm : Tendsto (fun δ => θ₀ - δ) (𝓝[>] 0) (𝓝[≠] θ₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun δ : ℝ => θ₀ - δ) (𝓝 0) (𝓝 (θ₀ - 0)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      intro h
      have h' : θ₀ - δ = θ₀ := h
      have hδ' : (0 : ℝ) < δ := hδ
      linarith
  filter_upwards [hp.eventually hev, hm.eventually hev, self_mem_nhdsWithin] with δ h1 h2 hδ
  have hδ' : (0 : ℝ) < δ := hδ
  rw [slope_def_field, h0, sub_zero, show θ₀ + δ - θ₀ = δ by ring] at h1
  rw [slope_def_field, h0, sub_zero, show θ₀ - δ - θ₀ = -δ by ring] at h2
  have hprod := mul_pos h1 h2
  have e : F (θ₀ + δ) / δ * F' * (F (θ₀ - δ) / -δ * F') =
      -(F (θ₀ + δ) * F (θ₀ - δ)) * (F' * F' / (δ * δ)) := by
    field_simp
  rw [e] at hprod
  have hpos : 0 < F' * F' / (δ * δ) := div_pos (mul_self_pos.2 hF') (mul_pos hδ' hδ')
  have := (mul_pos_iff_of_pos_right hpos).1 hprod
  linarith

/-- **Transversality at a crossing**: if a curve through `p` runs inside the vertical plaque of a
flow box and meets the circle `|z - q| = |p - q|` with nonzero radial speed, then `Re ζ` has
nonzero derivative along the circle at `p`. -/
theorem fx_p4_transversal {φ ζ : ℂ → ℂ} {N : Set ℂ} (hN : fx_IsFlowBox φ ζ N) {p q : ℂ}
    (hp : p ∈ N) {γ : ℝ → ℂ} {t : ℝ} {v : ℂ} (hγt : γ t = p) (hγd : HasDerivAt γ v t)
    (hγv : ∀ᶠ t' in 𝓝 t, (ζ (γ t')).re = (ζ p).re)
    (hrad : (starRingEnd ℂ (p - q) * v).re ≠ 0) :
    (deriv ζ p * (I * (p - q))).re ≠ 0 := by
  have hζ : HasDerivAt ζ (deriv ζ p) (γ t) := by
    rw [hγt]
    exact (hN.2.2.2.1 p hp).2.1.hasDerivAt
  have h1 : HasDerivAt (fun s => ζ (γ s)) (deriv ζ p * v) t := hζ.comp t hγd
  have h2 : HasDerivAt (fun s => (ζ (γ s)).re) (Complex.reCLM (deriv ζ p * v)) t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
  rw [Complex.reCLM_apply] at h2
  have h3 : HasDerivAt (fun s => (ζ (γ s)).re) 0 t :=
    (hasDerivAt_const t (ζ p).re).congr_of_eventuallyEq hγv
  have hre : (deriv ζ p * v).re = 0 := h2.unique h3
  have hv : v ≠ 0 := by
    rintro rfl
    simp at hrad
  have hα : deriv ζ p ≠ 0 := fx_p4_flowBox_deriv_ne hN hp
  have him : (deriv ζ p * v).im ≠ 0 := by
    intro him
    exact mul_ne_zero hα hv (Complex.ext hre him)
  have key : (deriv ζ p * (I * (p - q))).re * Complex.normSq v =
      -((deriv ζ p * v).im * (starRingEnd ℂ (p - q) * v).re) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re,
      Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply] at hre ⊢
    linear_combination (-((p.im - q.im) * v.re - (p.re - q.re) * v.im)) * hre
  intro h0
  rw [h0, zero_mul] at key
  have := mul_ne_zero him hrad
  exact this (neg_eq_zero.1 key.symm)

/-- The local picture at a zero `q`: a small closed disc in `Δ` without other zeros, met only by
edges incident to `q`. -/
theorem fx_p4_zero_local {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {ι : Type} [Fintype ι] {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) {q : ℂ} (hq : q ∈ unitDisc) (hq0 : φ q = 0) :
    ∃ r₀ > 0, closedBall q r₀ ⊆ unitDisc ∧ (∀ x ∈ ball q r₀, x ≠ q → φ x ≠ 0) ∧
      ∀ x ∈ ball q r₀, ∀ j : ι, x ∈ par j '' Ioo 0 1 → fx_Incident src dst j q := by
  have _ := hρ
  have _ := hφ
  have hZ : ∀ᶠ x in 𝓝 q, x ∉ {x | x ∈ unitDisc ∧ φ x = 0} \ {q} :=
    ((hF.zeros_finite.subset sdiff_subset).isClosed.isOpen_compl).mem_nhds (fun h => h.2 rfl)
  have h1 : ∀ᶠ x in 𝓝 q, x ∈ unitDisc := isOpen_ball.mem_nhds hq
  have h3 : ∀ j : ι, ∀ᶠ x in 𝓝 q, ¬ fx_Incident src dst j q → x ∉ par j '' Ioo 0 1 := by
    intro j
    by_cases hj : fx_Incident src dst j q
    · exact Filter.Eventually.of_forall fun x h => absurd hj h
    obtain ⟨r, hr, hav⟩ := fx_p4_avoid_Ico hF j le_rfl zero_lt_one hq
      (fun t ht h => by
        rcases eq_or_lt_of_le ht.1 with h0 | h0
        · rw [← h0, (hF.src_zero j).1] at h
          exact hj (Or.inl h)
        · exact (fx_p4_edge_reg hF j ⟨h0, ht.2⟩).2 (h ▸ hq0))
      (fun q' hq' h => hj (Or.inr (h ▸ hq')))
    filter_upwards [Metric.ball_mem_nhds q hr] with x hx _ hxj
    obtain ⟨t, ht, hxt⟩ := hxj
    exact hav t ⟨ht.1.le, ht.2⟩ (hxt ▸ hx)
  obtain ⟨r, hr, hball⟩ :=
    Metric.eventually_nhds_iff_ball.1 (h1.and (hZ.and (Filter.eventually_all.2 h3)))
  refine ⟨r / 2, half_pos hr, ?_, ?_, ?_⟩
  · intro x hx
    exact (hball x (closedBall_subset_ball (half_lt_self hr) hx)).1
  · intro x hx hxq h0
    obtain ⟨hxD, hxZ, -⟩ := hball x (ball_subset_ball (half_le_self hr.le) hx)
    exact hxZ ⟨⟨hxD, h0⟩, hxq⟩
  · intro x hx j hxj
    by_contra hj
    exact (hball x (ball_subset_ball (half_le_self hr.le) hx)).2.2 j hj hxj

/-- Near a regular point of `Δ` all of whose picked edges are healed, every point is healed. -/
theorem fx_p4_healed_near {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι}
    {Φ : ℂ → ℂ} (hΦd : DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par pick)) {y : ℂ}
    (hy : y ∈ unitDisc) (hy0 : φ y ≠ 0)
    (hh : ∀ q, y ∈ par (pick q) '' Ioo 0 1 → ∀ t ∈ Ioo (0 : ℝ) 1,
      fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ 0 (par (pick q) t)) :
    ∀ᶠ x in 𝓝 y, fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ 0 x := by
  obtain ⟨r, hr, hsub, hloc⟩ := fx_p4_cut_local hρ hφ hF pick hy hy0
  have hΩo := fx_p4_cut_isOpen hρ hφ hF pick
  filter_upwards [Metric.ball_mem_nhds y hr] with x hx
  by_cases hxΩ : x ∈ unitDisc \ fx_cutSet φ par pick
  · exact fx_p4_osc_of_mem hΩo hΦd.continuousOn hxΩ
  · have hxc : x ∈ fx_cutSet φ par pick := by
      by_contra h
      exact hxΩ ⟨hsub hx, h⟩
    obtain ⟨q, hyq, t, ht, rfl⟩ := hloc x hx hxc
    exact hh q hyq t ht

/-- The values of `fx_p4_uext` at the zeros and at the points of healed picked edges form a countable
set. -/
theorem fx_p4_u_cut_countable {φ : ℂ → ℂ} {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst)
    {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι} {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par pick))
    (hΦ2 : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, deriv Φ z ^ 2 = φ z) :
    (fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ '' {x | x ∈ unitDisc ∧ (φ x = 0 ∨
      ∃ q, x ∈ par (pick q) '' Ioo 0 1 ∧ ∀ t ∈ Ioo (0 : ℝ) 1,
        fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ 0 (par (pick q) t))}).Countable := by
  have := fx_p4_zsub_finite hF
  have hc : ∀ q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}, ∃ c : ℝ, (∀ t ∈ Ioo (0 : ℝ) 1,
      fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ 0 (par (pick q) t)) →
      ∀ t ∈ Ioo (0 : ℝ) 1, fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ (par (pick q) t) = c := by
    intro q
    by_cases h : ∀ t ∈ Ioo (0 : ℝ) 1,
        fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ 0 (par (pick q) t)
    · obtain ⟨c, hc⟩ := fx_p4_edge_u_const hF hΦd hΦ2 q h
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose cv hcv using hc
  refine ((hF.zeros_finite.image (fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ)).countable.union
    (Set.countable_range cv)).mono ?_
  rintro _ ⟨x, ⟨hxD, hx⟩, rfl⟩
  rcases hx with hx0 | ⟨q, ⟨t, ht, rfl⟩, hh⟩
  · exact Or.inl ⟨x, ⟨hxD, hx0⟩, rfl⟩
  · exact Or.inr ⟨q, (hcv q hh t ht).symm⟩

/-- **Arc bound.**  Along a `C¹` curve in `Δ` all of whose points have healed neighbourhoods,
`fx_p4_uext` changes by at most `M K (b - a)`, provided its values off `Δ ∖ cutSet` along the curve
form a countable set. -/
theorem fx_p4_arc_bound {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι}
    {Φ : ℂ → ℂ} (hΦd : DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par pick))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, ‖deriv Φ z‖ ≤ M)
    {c c' : ℝ → ℂ} (hc : ∀ t, HasDerivAt c (c' t) t) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t, ‖c' t‖ ≤ K) {a b : ℝ} (hab : a ≤ b)
    (hheal : ∀ t ∈ Icc a b, c t ∈ unitDisc ∧
      ∀ᶠ y in 𝓝 (c t), fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ 0 y)
    (hbad : ((fun t => fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ (c t)) ''
      (Icc a b \ c ⁻¹' (unitDisc \ fx_cutSet φ par pick))).Countable) :
    |fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ (c b) -
      fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ (c a)| ≤ M * K * (b - a) := by
  have hΩo := fx_p4_cut_isOpen hρ hφ hF pick
  refine fx_p4_curve_bound hΩo hΦd hM0 hM (fun z hz => fx_p4_uext_eq hΩo hΦd.continuousOn hz) hc hK0
    hK hab ?_ hbad
  intro t ht
  obtain ⟨hctD, hev⟩ := hheal t ht
  have h1 : ∀ᶠ y in 𝓝 (c t), fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ 0 y ∧
      y ∈ closure (unitDisc \ fx_cutSet φ par pick) := by
    filter_upwards [hev, isOpen_ball.mem_nhds hctD] with y hy hyD
    exact ⟨hy, fx_p4_cut_dense hF pick hyD⟩
  exact ((fx_p4_uext_continuousAt h1).comp (hc t).continuousAt).continuousWithinAt

/-- **The circle argument at a zero** (one jump): if every other picked edge at the zero `q` is
healed, a small circle around `q` crosses the picked edge of `q` exactly once and nothing unhealed,
so the jump of `Re Φ` across that edge is at most `2π M r`, for every small `r`. -/
theorem fx_p4_circle_jump {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {ι : Type} [Fintype ι] {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι}
    {Φ : ℂ → ℂ} (hΦd : DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par pick))
    (hΦ2 : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, deriv Φ z ^ 2 = φ z)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, ‖deriv Φ z‖ ≤ M)
    (q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}) (hinc : fx_Incident src dst (pick q) q.1)
    (hheal : ∀ q' : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}, pick q' ≠ pick q →
      fx_Incident src dst (pick q') q.1 → ∀ t ∈ Ioo (0 : ℝ) 1,
        fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ 0 (par (pick q') t))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ Ioo (0 : ℝ) 1, fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ ε (par (pick q) t) := by
  have hΩo := fx_p4_cut_isOpen hρ hφ hF pick
  obtain ⟨r₀, hr₀, hcl, hreg, hincl⟩ := fx_p4_zero_local hρ hφ hF q.2.1 q.2.2
  obtain ⟨r₁, hr₁, hcross⟩ := fx_p4_edge_cross hF hinc
  have hden : 0 < 2 * π * M + 1 := by positivity
  have hmin : 0 < min r₀ r₁ := lt_min hr₀ hr₁
  set r := min (min r₀ r₁ / 2) (ε / (2 * π * M + 1)) with hr
  have hrpos : 0 < r := lt_min (by positivity) (div_pos hε hden)
  have hr1 : r ≤ min r₀ r₁ / 2 := min_le_left _ _
  have hrr₀ : r < r₀ := by linarith [min_le_left r₀ r₁]
  have hrr₁ : r < r₁ := by linarith [min_le_right r₀ r₁]
  have hrε : 2 * π * M * r ≤ ε := by
    have h1 : r ≤ ε / (2 * π * M + 1) := min_le_right _ _
    have h2 : r * (2 * π * M + 1) ≤ ε := by rwa [le_div_iff₀ hden] at h1
    nlinarith
  obtain ⟨p, ⟨s, hs, hps⟩, hpr, huniq, γ, t, v, hγt, hγd, hγe, hrad⟩ := hcross r ⟨hrpos, hrr₁⟩
  subst hps
  obtain ⟨ζ, N, hpN, hN, hΩN, heN, vP, vM, hvP, hvM⟩ := fx_p4_cut_box hF hΦd hΦ2 q hs
  refine ⟨s, hs, ?_⟩
  rw [fx_p4_box_osc hN hΩN hvP hvM hpN rfl hε.le]
  refine le_trans ?_ hrε
  set p := par (pick q) s with hp
  set C : ℝ → ℂ := fun θ => q.1 + (r : ℂ) * exp ((θ : ℂ) * I) with hC
  set θ₀ := arg (p - q.1) with hθ₀
  have hCθ₀ : C θ₀ = p := fx_p4_circle_arg hpr
  have hCd : ∀ θ : ℝ, HasDerivAt C ((r : ℂ) * exp ((θ : ℂ) * I) * I) θ :=
    fun θ => fx_p4_circle_hasDerivAt q.1 r θ
  have hCn : ∀ θ, ‖C θ - q.1‖ = r := fun θ => fx_p4_circle_norm q.1 hrpos.le θ
  have hCball : ∀ θ, C θ ∈ ball q.1 r₀ := fun θ => by
    rw [mem_ball, dist_eq_norm, hCn]
    exact hrr₀
  have hCD : ∀ θ, C θ ∈ unitDisc := fun θ => hcl (ball_subset_closedBall (hCball θ))
  have hCne : ∀ θ, C θ ≠ q.1 := fun θ h => by
    have := hCn θ
    rw [h, sub_self, norm_zero] at this
    exact hrpos.ne this
  have hCreg : ∀ θ, φ (C θ) ≠ 0 := fun θ => hreg _ (hCball θ) (hCne θ)
  have hCc : Continuous C := continuous_iff_continuousAt.2 fun θ => (hCd θ).continuousAt
  -- transversality of the circle and the edge at `p`
  have hζp : HasDerivAt ζ (deriv ζ p) (C θ₀) := by
    rw [hCθ₀]
    exact (hN.2.2.2.1 p hpN).2.1.hasDerivAt
  have hF1 : HasDerivAt (fun θ => ζ (C θ)) (deriv ζ p * ((r : ℂ) * exp ((θ₀ : ℂ) * I) * I)) θ₀ :=
    hζp.comp θ₀ (hCd θ₀)
  have hF2 : HasDerivAt (fun θ => (ζ (C θ)).re - (ζ p).re)
      (Complex.reCLM (deriv ζ p * ((r : ℂ) * exp ((θ₀ : ℂ) * I) * I))) θ₀ :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ₀ hF1).sub_const _
  rw [Complex.reCLM_apply] at hF2
  have hexp : (r : ℂ) * exp ((θ₀ : ℂ) * I) = p - q.1 := by
    have h := hCθ₀
    simp only [hC] at h
    linear_combination h
  have hF'ne : (deriv ζ p * ((r : ℂ) * exp ((θ₀ : ℂ) * I) * I)).re ≠ 0 := by
    rw [hexp, show (p - q.1) * I = I * (p - q.1) by ring]
    refine fx_p4_transversal hN hpN hγt hγd ?_ hrad
    have hγc : ContinuousAt γ t := hγd.continuousAt
    have hγtN : γ t ∈ N := by rw [hγt]; exact hpN
    filter_upwards [hγe, hγc.preimage_mem_nhds (hN.1.mem_nhds hγtN)] with t' h1 h2
    exact (heN _ h2).1 h1
  set F : ℝ → ℝ := fun θ => (ζ (C θ)).re - (ζ p).re with hFdef
  have hF0 : F θ₀ = 0 := by
    show (ζ (C θ₀)).re - (ζ p).re = 0
    rw [hCθ₀, sub_self]
  have hsign := fx_p4_sign_change hF2 hF0 hF'ne
  have hplus : Tendsto (fun δ : ℝ => θ₀ + δ) (𝓝[>] 0) (𝓝 θ₀) := by
    have : Tendsto (fun δ : ℝ => θ₀ + δ) (𝓝 0) (𝓝 (θ₀ + 0)) := tendsto_const_nhds.add tendsto_id
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hminus : Tendsto (fun δ : ℝ => θ₀ - δ) (𝓝[>] 0) (𝓝 θ₀) := by
    have : Tendsto (fun δ : ℝ => θ₀ - δ) (𝓝 0) (𝓝 (θ₀ - 0)) := tendsto_const_nhds.sub tendsto_id
    rw [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hNev : ∀ᶠ θ in 𝓝 θ₀, C θ ∈ N := by
    have hCθ₀N : C θ₀ ∈ N := by rw [hCθ₀]; exact hpN
    exact hCc.continuousAt.preimage_mem_nhds (hN.1.mem_nhds hCθ₀N)
  have hFev : ∀ η > 0, ∀ᶠ θ in 𝓝 θ₀, |F θ| < η := fun η hη => by
    have := Metric.tendsto_nhds.1 hF2.continuousAt η hη
    filter_upwards [this] with θ hθ
    have h' : dist (F θ) (F θ₀) < η := hθ
    rwa [Real.dist_eq, hF0, sub_zero] at h'
  -- the circle minus `p` meets only healed edges
  have hcnt := fx_p4_u_cut_countable hF hΦd hΦ2 (pick := pick)
  have key : ∀ δ > 0, ∀ θ ∈ Icc (θ₀ + δ) (θ₀ + (2 * π - δ)), ∀ q' : {q : ℂ // q ∈ unitDisc ∧ φ q = 0},
      C θ ∈ par (pick q') '' Ioo 0 1 → pick q' ≠ pick q := by
    intro δ hδ θ hθ q' hq' hpq
    rw [hpq] at hq'
    have hCp : C θ = p := huniq _ hq' (hCn θ)
    obtain ⟨n, hn⟩ := fx_p4_circle_inj q.1 hrpos (hCp.trans hCθ₀.symm)
    have hpi := Real.pi_pos
    have h1 : (0 : ℝ) < n * (2 * π) := by linarith [hθ.1]
    have h2 : (n : ℝ) * (2 * π) < 2 * π := by linarith [hθ.2]
    have h3 : (0 : ℝ) < n := by
      by_contra h
      push Not at h
      nlinarith
    have h4 : (n : ℝ) < 1 := by
      by_contra h
      push Not at h
      nlinarith
    have h5 : (0 : ℤ) < n := by exact_mod_cast h3
    have h6 : n < 1 := by exact_mod_cast h4
    omega
  have harc : ∀ δ ∈ Ioo 0 π,
      |fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ (C (θ₀ + (2 * π - δ))) -
        fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ (C (θ₀ + δ))| ≤ M * r * (2 * π - 2 * δ) := by
    intro δ hδ
    have hb := fx_p4_arc_bound hρ hφ hF hΦd hM0 hM hCd hrpos.le
      (fun θ => (fx_p4_circle_deriv_norm hrpos.le θ).le) (a := θ₀ + δ) (b := θ₀ + (2 * π - δ))
      (by linarith [hδ.2]) ?_ ?_
    · calc _ ≤ M * r * (θ₀ + (2 * π - δ) - (θ₀ + δ)) := hb
        _ = M * r * (2 * π - 2 * δ) := by ring
    · intro θ hθ
      refine ⟨hCD θ, fx_p4_healed_near hρ hφ hF hΦd (hCD θ) (hCreg θ) fun q' hq' => ?_⟩
      exact hheal q' (key δ hδ.1 θ hθ q' hq') (hincl _ (hCball θ) _ hq')
    · refine hcnt.mono ?_
      rintro _ ⟨θ, ⟨hθ, hθΩ⟩, rfl⟩
      refine ⟨C θ, ⟨hCD θ, Or.inr ?_⟩, rfl⟩
      have hcut : C θ ∈ fx_cutSet φ par pick := by
        by_contra h
        exact hθΩ ⟨hCD θ, h⟩
      rcases hcut with ⟨-, h0⟩ | he
      · exact absurd h0 (hCreg θ)
      · obtain ⟨q', hq'⟩ := mem_iUnion.1 he
        exact ⟨q', hq', hheal q' (key δ hδ.1 θ hθ q' hq') (hincl _ (hCball θ) _ hq')⟩
  have hper : ∀ δ : ℝ, C (θ₀ + (2 * π - δ)) = C (θ₀ - δ) := fun δ => by
    have := fx_p4_circle_period q.1 r (θ₀ - δ)
    simp only [hC]
    rw [show θ₀ + (2 * π - δ) = θ₀ - δ + 2 * π by ring]
    exact this
  -- conclusion: `|vP - vM| ≤ 2π M r`
  apply le_of_forall_pos_lt_add
  intro η hη
  have hev := (hsign.and ((hplus.eventually hNev).and (hminus.eventually hNev))).and
    (((hplus.eventually (hFev (η / 2) (half_pos hη))).and
      (hminus.eventually (hFev (η / 2) (half_pos hη)))).and (Ioo_mem_nhdsGT Real.pi_pos))
  obtain ⟨δ, ⟨hsg, hN1, hN2⟩, ⟨hF1', hF2'⟩, hδ⟩ := hev.exists
  have hne1 : F (θ₀ + δ) ≠ 0 := fun h => by
    rw [h, zero_mul] at hsg
    exact lt_irrefl 0 hsg
  have hne2 : F (θ₀ - δ) ≠ 0 := fun h => by
    rw [h, mul_zero] at hsg
    exact lt_irrefl 0 hsg
  have hw1Ω : C (θ₀ + δ) ∈ unitDisc \ fx_cutSet φ par pick :=
    (hΩN _ hN1).2 (sub_ne_zero.1 hne1)
  have hw2Ω : C (θ₀ - δ) ∈ unitDisc \ fx_cutSet φ par pick :=
    (hΩN _ hN2).2 (sub_ne_zero.1 hne2)
  have harcδ := harc δ hδ
  rw [hper δ, fx_p4_uext_eq hΩo hΦd.continuousOn hw1Ω, fx_p4_uext_eq hΩo hΦd.continuousOn hw2Ω]
    at harcδ
  have hMr : M * r * (2 * π - 2 * δ) ≤ 2 * π * M * r := by
    have : 0 ≤ M * r := mul_nonneg hM0 hrpos.le
    nlinarith [hδ.1]
  have hF1'' : |(ζ (C (θ₀ + δ))).re - (ζ p).re| < η / 2 := hF1'
  have hF2'' : |(ζ (C (θ₀ - δ))).re - (ζ p).re| < η / 2 := hF2'
  have hsg' : ((ζ (C (θ₀ + δ))).re - (ζ p).re) * ((ζ (C (θ₀ - δ))).re - (ζ p).re) < 0 := hsg
  rcases lt_or_gt_of_ne hne1 with h1 | h1
  · have h1' : (ζ (C (θ₀ + δ))).re - (ζ p).re < 0 := h1
    have h2' : 0 < (ζ (C (θ₀ - δ))).re - (ζ p).re := by nlinarith
    have e1 := hvM _ hN1 (by linarith)
    have e2 := hvP _ hN2 (by linarith)
    have htri := abs_add_three (vP - (Φ (C (θ₀ - δ))).re)
      ((Φ (C (θ₀ - δ))).re - (Φ (C (θ₀ + δ))).re) ((Φ (C (θ₀ + δ))).re - vM)
    rw [show vP - (Φ (C (θ₀ - δ))).re + ((Φ (C (θ₀ - δ))).re - (Φ (C (θ₀ + δ))).re) +
      ((Φ (C (θ₀ + δ))).re - vM) = vP - vM by ring, abs_sub_comm vP (Φ (C (θ₀ - δ))).re, e2,
      e1] at htri
    linarith
  · have h1' : 0 < (ζ (C (θ₀ + δ))).re - (ζ p).re := h1
    have h2' : (ζ (C (θ₀ - δ))).re - (ζ p).re < 0 := by nlinarith
    have e1 := hvP _ hN1 (by linarith)
    have e2 := hvM _ hN2 (by linarith)
    have htri := abs_add_three (vP - (Φ (C (θ₀ + δ))).re)
      ((Φ (C (θ₀ + δ))).re - (Φ (C (θ₀ - δ))).re) ((Φ (C (θ₀ - δ))).re - vM)
    rw [show vP - (Φ (C (θ₀ + δ))).re + ((Φ (C (θ₀ + δ))).re - (Φ (C (θ₀ - δ))).re) +
      ((Φ (C (θ₀ - δ))).re - vM) = vP - vM by ring, abs_sub_comm vP (Φ (C (θ₀ + δ))).re, e1,
      e2, abs_sub_comm (Φ (C (θ₀ + δ))).re] at htri
    linarith

/-- **The circle argument at a zero** (no jump left): if all picked edges at the zero `q` are
healed, `Re Φ` has oscillation `0` at `q`. -/
theorem fx_p4_zero_healed {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {ι : Type} [Fintype ι] {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι}
    {Φ : ℂ → ℂ} (hΦd : DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par pick))
    (hΦ2 : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, deriv Φ z ^ 2 = φ z)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, ‖deriv Φ z‖ ≤ M)
    (q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}) (hinc : fx_Incident src dst (pick q) q.1)
    (hheal : ∀ q' : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}, fx_Incident src dst (pick q') q.1 →
      ∀ t ∈ Ioo (0 : ℝ) 1, fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ 0 (par (pick q') t)) :
    fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ 0 q.1 := by
  have hΩo := fx_p4_cut_isOpen hρ hφ hF pick
  obtain ⟨r₀, hr₀, hcl, hreg, hincl⟩ := fx_p4_zero_local hρ hφ hF q.2.1 q.2.2
  obtain ⟨r₁, hr₁, hcross⟩ := fx_p4_edge_cross hF hinc
  obtain ⟨c₀, hc₀⟩ := fx_p4_edge_u_const hF hΦd hΦ2 q (hheal q hinc)
  have hcnt := fx_p4_u_cut_countable hF hΦd hΦ2 (pick := pick)
  have key : ∀ y ∈ ball q.1 (min r₀ r₁), y ≠ q.1 →
      |fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ y - c₀| ≤ 2 * π * M * ‖y - q.1‖ := by
    intro y hy hyq
    set r := ‖y - q.1‖ with hr
    have hrpos : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hyq)
    have hrR : r < min r₀ r₁ := by rwa [mem_ball, dist_eq_norm] at hy
    obtain ⟨p, ⟨s, hs, hps⟩, hpr, -, -⟩ := hcross r ⟨hrpos, hrR.trans_le (min_le_right _ _)⟩
    set C : ℝ → ℂ := fun θ => q.1 + (r : ℂ) * exp ((θ : ℂ) * I) with hC
    have hCp : C (arg (p - q.1)) = p := fx_p4_circle_arg hpr
    have hCy : C (arg (y - q.1)) = y := fx_p4_circle_arg rfl
    have hCd : ∀ θ : ℝ, HasDerivAt C ((r : ℂ) * exp ((θ : ℂ) * I) * I) θ :=
      fun θ => fx_p4_circle_hasDerivAt q.1 r θ
    have hCn : ∀ θ, ‖C θ - q.1‖ = r := fun θ => fx_p4_circle_norm q.1 hrpos.le θ
    have hCball : ∀ θ, C θ ∈ ball q.1 r₀ := fun θ => by
      rw [mem_ball, dist_eq_norm, hCn]
      exact hrR.trans_le (min_le_left _ _)
    have hCD : ∀ θ, C θ ∈ unitDisc := fun θ => hcl (ball_subset_closedBall (hCball θ))
    have hCne : ∀ θ, C θ ≠ q.1 := fun θ h => by
      have := hCn θ
      rw [h, sub_self, norm_zero] at this
      exact hrpos.ne this
    have hCreg : ∀ θ, φ (C θ) ≠ 0 := fun θ => hreg _ (hCball θ) (hCne θ)
    have hup : fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ p = c₀ := by
      rw [← hps]
      exact hc₀ s hs
    have hbound : ∀ α β : ℝ, α ≤ β →
        |fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ (C β) -
          fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ (C α)| ≤ M * r * (β - α) := by
      intro α β hαβ
      refine fx_p4_arc_bound hρ hφ hF hΦd hM0 hM hCd hrpos.le
        (fun θ => (fx_p4_circle_deriv_norm hrpos.le θ).le) hαβ ?_ ?_
      · intro θ _
        refine ⟨hCD θ, fx_p4_healed_near hρ hφ hF hΦd (hCD θ) (hCreg θ) fun q' hq' => ?_⟩
        exact hheal q' (hincl _ (hCball θ) _ hq')
      · refine hcnt.mono ?_
        rintro _ ⟨θ, ⟨_, hθΩ⟩, rfl⟩
        refine ⟨C θ, ⟨hCD θ, Or.inr ?_⟩, rfl⟩
        have hcut : C θ ∈ fx_cutSet φ par pick := by
          by_contra h
          exact hθΩ ⟨hCD θ, h⟩
        rcases hcut with ⟨-, h0⟩ | he
        · exact absurd h0 (hCreg θ)
        · obtain ⟨q', hq'⟩ := mem_iUnion.1 he
          exact ⟨q', hq', hheal q' (hincl _ (hCball θ) _ hq')⟩
    have hargs : |arg (y - q.1) - arg (p - q.1)| ≤ 2 * π := by
      have h1 := Complex.neg_pi_lt_arg (y - q.1)
      have h2 := Complex.arg_le_pi (y - q.1)
      have h3 := Complex.neg_pi_lt_arg (p - q.1)
      have h4 := Complex.arg_le_pi (p - q.1)
      rw [abs_le]
      constructor <;> linarith
    have hpos : 0 ≤ M * r := mul_nonneg hM0 hrpos.le
    rcases le_total (arg (p - q.1)) (arg (y - q.1)) with h | h
    · have hb := hbound _ _ h
      rw [hCp, hCy, hup] at hb
      calc |fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ y - c₀|
          ≤ M * r * (arg (y - q.1) - arg (p - q.1)) := hb
        _ ≤ M * r * (2 * π) := by
          gcongr
          linarith [le_abs_self (arg (y - q.1) - arg (p - q.1))]
        _ = 2 * π * M * r := by ring
    · have hb := hbound _ _ h
      rw [hCp, hCy, hup, abs_sub_comm] at hb
      calc |fx_p4_uext (unitDisc \ fx_cutSet φ par pick) Φ y - c₀|
          ≤ M * r * (arg (p - q.1) - arg (y - q.1)) := hb
        _ ≤ M * r * (2 * π) := by
          gcongr
          linarith [neg_abs_le (arg (y - q.1) - arg (p - q.1))]
        _ = 2 * π * M * r := by ring
  intro δ hδ
  have hden : 0 < 4 * π * M + 1 := by positivity
  have hmin : 0 < min r₀ r₁ := lt_min hr₀ hr₁
  set r' := min (min r₀ r₁ / 2) (δ / (4 * π * M + 1)) with hr'
  have hr'pos : 0 < r' := lt_min (by positivity) (div_pos hδ hden)
  have hr'R : r' < min r₀ r₁ := by
    linarith [min_le_left (min r₀ r₁ / 2) (δ / (4 * π * M + 1))]
  have hr'δ : 4 * π * M * r' ≤ δ := by
    have h1 : r' ≤ δ / (4 * π * M + 1) := min_le_right _ _
    have h2 : r' * (4 * π * M + 1) ≤ δ := by rwa [le_div_iff₀ hden] at h1
    nlinarith
  refine ⟨ball q.1 r', ball_mem_nhds _ hr'pos, fun w hw w' hw' => ?_⟩
  have hqΩ : q.1 ∉ unitDisc \ fx_cutSet φ par pick := fun h => h.2 (Or.inl q.2)
  have hwq : w ≠ q.1 := fun h => hqΩ (h ▸ hw.2)
  have hw'q : w' ≠ q.1 := fun h => hqΩ (h ▸ hw'.2)
  have e1 := key w (ball_subset_ball hr'R.le hw.1) hwq
  have e2 := key w' (ball_subset_ball hr'R.le hw'.1) hw'q
  rw [fx_p4_uext_eq hΩo hΦd.continuousOn hw.2] at e1
  rw [fx_p4_uext_eq hΩo hΦd.continuousOn hw'.2] at e2
  have hn1 : ‖w - q.1‖ < r' := by
    have := hw.1
    rwa [mem_ball, dist_eq_norm] at this
  have hn2 : ‖w' - q.1‖ < r' := by
    have := hw'.1
    rwa [mem_ball, dist_eq_norm] at this
  have hMpos : 0 ≤ 2 * π * M := by positivity
  have h3 : 2 * π * M * ‖w - q.1‖ ≤ 2 * π * M * r' := mul_le_mul_of_nonneg_left hn1.le hMpos
  have h4 : 2 * π * M * ‖w' - q.1‖ ≤ 2 * π * M * r' := mul_le_mul_of_nonneg_left hn2.le hMpos
  calc |(Φ w).re - (Φ w').re| ≤ |(Φ w).re - c₀| + |c₀ - (Φ w').re| := abs_sub_le _ _ _
    _ ≤ 0 + δ := by
      rw [abs_sub_comm c₀]
      linarith

/-- **All picked edges are healed** (downward induction on the rank; at each zero, the edges from
higher ranks are already healed and the circle argument heals the zero's own edge). -/
theorem fx_p4_cut_heal_edges {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ)
    (hφ : DifferentiableOn ℂ φ (ball 0 ρ)) {ι : Type} [Fintype ι] {par : ι → ℝ → ℂ}
    {src : ι → ℂ} {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst)
    {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι} {rk : ℂ → ℕ}
    (hpick : fx_IsCutChoice φ src dst pick rk) {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par pick))
    (hΦ2 : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, deriv Φ z ^ 2 = φ z)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, ‖deriv Φ z‖ ≤ M) :
    ∀ q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}, ∀ t ∈ Ioo (0 : ℝ) 1,
      fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ 0 (par (pick q) t) := by
  have := fx_p4_zsub_finite hF
  obtain ⟨B, hB⟩ := (Set.finite_range (fun q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} => rk q.1)).bddAbove
  have hB' : ∀ q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}, rk q.1 ≤ B := fun q => hB ⟨q, rfl⟩
  have key : ∀ n, ∀ q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}, B - rk q.1 = n →
      ∀ t ∈ Ioo (0 : ℝ) 1, fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ 0 (par (pick q) t) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih q hqn
    have hoth : ∀ q' : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}, pick q' ≠ pick q →
        fx_Incident src dst (pick q') q.1 → ∀ t ∈ Ioo (0 : ℝ) 1,
          fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ 0 (par (pick q') t) := by
      intro q' hne hinc
      have hqq : q'.1 ≠ q.1 := fun h => hne (by rw [Subtype.ext h])
      have hlt := fx_p4_pick_rank hpick hqq hinc
      have hq'B := hB' q'
      exact ih (B - rk q'.1) (by omega) q' rfl
    have hε : ∀ ε > 0, ∀ t ∈ Ioo (0 : ℝ) 1,
        fx_p4_OscLe (unitDisc \ fx_cutSet φ par pick) Φ ε (par (pick q) t) := by
      intro ε hε t ht
      obtain ⟨t₀, ht₀, h₀⟩ :=
        fx_p4_circle_jump hρ hφ hF hΦd hΦ2 hM0 hM q (fx_p4_pick_inc hpick q) hoth hε
      exact fx_p4_edge_osc_all hF hΦd hΦ2 q hε.le ht₀ ht h₀
    intro t ht
    exact fx_p4_osc_zero_of_forall fun ε hε' => hε ε hε' t ht
  exact fun q => key _ q rfl

/-- The regular points of `Δ` whose leaf meets a picked edge form an open set (`fx_sat_open` with
the forest's flow boxes). -/
theorem fx_p4_cut_sat_open {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) (pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι) :
    IsOpen {z | z ∈ unitDisc ∧ φ z ≠ 0 ∧
      (fx_leaf φ z ∩ ⋃ q, par (pick q) '' Ioo 0 1).Nonempty} := by
  refine fx_sat_open (hφ.mono (ball_subset_ball hρ.le)) fun x hx _ => ?_
  obtain ⟨q, t, ht, rfl⟩ := mem_iUnion.1 hx
  obtain ⟨ζ, N, hxN, hN, hplaque, hother⟩ := hF.box (pick q) t ht
  refine ⟨ζ, N, hxN, hN, ?_⟩
  rw [← hplaque]
  ext z
  constructor
  · rintro ⟨hz, hzN⟩
    obtain ⟨q', hq'⟩ := mem_iUnion.1 hz
    by_cases h : pick q' = pick q
    · rw [h] at hq'
      exact ⟨hq', hzN⟩
    · have h' : z ∈ par (pick q') '' Ioo 0 1 ∩ N := ⟨hq', hzN⟩
      rw [hother (pick q') h] at h'
      exact absurd h' (notMem_empty z)
  · rintro ⟨hz, hzN⟩
    exact ⟨mem_iUnion.2 ⟨q, hz⟩, hzN⟩

/-- The set of regular points whose leaf avoids the cut set is measurable. -/
theorem fx_p4_cut_R_meas {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) (pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι) :
    MeasurableSet {x | x ∈ unitDisc ∧ φ x ≠ 0 ∧ Disjoint (fx_leaf φ x) (fx_cutSet φ par pick)} := by
  have hreg : IsOpen {x | x ∈ unitDisc ∧ φ x ≠ 0} := by
    have := (hφ.continuousOn.mono (ball_subset_ball hρ.le)).isOpen_inter_preimage
      (isOpen_ball : IsOpen (unitDisc : Set ℂ)) (isOpen_compl_singleton (x := (0 : ℂ)))
    convert this using 1
    ext x
    exact Iff.rfl
  have heq : {x | x ∈ unitDisc ∧ φ x ≠ 0 ∧ Disjoint (fx_leaf φ x) (fx_cutSet φ par pick)} =
      {x | x ∈ unitDisc ∧ φ x ≠ 0} ∩ {z | z ∈ unitDisc ∧ φ z ≠ 0 ∧
        (fx_leaf φ z ∩ ⋃ q, par (pick q) '' Ioo 0 1).Nonempty}ᶜ := by
    ext x
    constructor
    · rintro ⟨hx, hx0, hd⟩
      refine ⟨⟨hx, hx0⟩, ?_⟩
      rintro ⟨-, -, w, hw, hwe⟩
      exact Set.disjoint_left.1 hd hw (Or.inr hwe)
    · rintro ⟨⟨hx, hx0⟩, hS⟩
      refine ⟨hx, hx0, Set.disjoint_left.2 fun w hw hwc => ?_⟩
      rcases hwc with ⟨-, hw0⟩ | hwe
      · exact (fx_p4_leaf_reg hw).2 hw0
      · exact hS ⟨hx, hx0, w, hw, hwe⟩
  rw [heq]
  exact hreg.measurableSet.inter (fx_p4_cut_sat_open hρ hφ hF pick).measurableSet.compl

/-- **The gradient bound** for a cut calibration: off the null cut set, `u = Re Φ` is differentiable
with `|Du| = |Φ'| = |φ|^{1/2}`. -/
theorem fx_p4_cut_grad {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) (pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι)
    {Φ : ℂ → ℂ} {u : ℂ → ℝ} (hΦd : DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par pick))
    (hΦu : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, deriv Φ z ^ 2 = φ z ∧ u z = (Φ z).re) :
    ∀ᵐ y ∂(volume.restrict unitDisc), DifferentiableAt ℝ u y ∧
      ‖fderiv ℝ u y‖ ≤ Real.sqrt ‖φ y‖ := by
  have hΩo := fx_p4_cut_isOpen hρ hφ hF pick
  have hmD : MeasurableSet (unitDisc : Set ℂ) := measurableSet_ball
  rw [ae_restrict_iff' hmD, ae_iff]
  refine measure_mono_null (fun y hy => ?_) (fx_p4_cut_null hF pick)
  by_contra hyc
  apply hy
  intro hyD
  have hyΩ : y ∈ unitDisc \ fx_cutSet φ par pick := ⟨hyD, hyc⟩
  set a := deriv Φ y with ha
  have hΦy : HasDerivAt Φ a y := (hΦd.differentiableAt (hΩo.mem_nhds hyΩ)).hasDerivAt
  set L : ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) a).restrictScalars ℝ)
    with hL
  have hre : HasFDerivAt (fun w => (Φ w).re) L y :=
    Complex.reCLM.hasFDerivAt.comp y (hΦy.hasFDerivAt.restrictScalars ℝ)
  have hev : u =ᶠ[𝓝 y] fun w => (Φ w).re := by
    filter_upwards [hΩo.mem_nhds hyΩ] with w hw
    exact (hΦu w hw).2
  have hu : HasFDerivAt u L y := hre.congr_of_eventuallyEq hev
  refine ⟨hu.differentiableAt, ?_⟩
  rw [hu.fderiv]
  have hna : ‖a‖ = Real.sqrt ‖φ y‖ := by
    rw [← (hΦu y hyΩ).1, norm_pow, Real.sqrt_sq (norm_nonneg _)]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun w => ?_
  simp only [hL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul,
    Complex.reCLM_apply, Real.norm_eq_abs]
  calc |(w * a).re| ≤ ‖w * a‖ := Complex.abs_re_le_norm _
    _ = Real.sqrt ‖φ y‖ * ‖w‖ := by rw [norm_mul, hna, mul_comm]

/-- **The flow-box field of a cut calibration**: a leaf-saturated set `R` of regular points whose
leaves avoid the cut set is, in a small flow box around each regular point, either absent or a union
of horizontal plaques on which `u = Re ζ + c`. -/
theorem fx_p4_cut_calib_box {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) (pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι)
    {Φ : ℂ → ℂ} {u : ℂ → ℝ} (hΦd : DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par pick))
    (hΦu : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, deriv Φ z ^ 2 = φ z ∧ u z = (Φ z).re)
    {R : Set ℂ} (hRsub : ∀ x ∈ R, Disjoint (fx_leaf φ x) (fx_cutSet φ par pick))
    (hRsat : ∀ z₀ ∈ R, ∀ z ∈ fx_leaf φ z₀, z ∈ R) :
    ∀ p ∈ unitDisc, φ p ≠ 0 → ∃ (ζ : ℂ → ℂ) (N : Set ℂ), p ∈ N ∧ fx_IsFlowBox φ ζ N ∧
      (R ∩ N = ∅ ∨ ((∃ E : Set ℝ, R ∩ N = {z | z ∈ N ∧ (ζ z).im ∈ E}) ∧
        ∃ c : ℝ, ∀ z ∈ N, u z = (ζ z).re + c)) := by
  have hφD : DifferentiableOn ℂ φ unitDisc := hφ.mono (ball_subset_ball hρ.le)
  have hΩo := fx_p4_cut_isOpen hρ hφ hF pick
  -- saturation inside a flow box
  have hplaq : ∀ {ζ : ℂ → ℂ} {N : Set ℂ}, fx_IsFlowBox φ ζ N →
      R ∩ N = {z | z ∈ N ∧ (ζ z).im ∈ {y | ∃ z₀ ∈ R ∩ N, (ζ z₀).im = y}} := by
    intro ζ N hN
    ext z
    constructor
    · rintro ⟨hzR, hzN⟩
      exact ⟨hzN, z, ⟨hzR, hzN⟩, rfl⟩
    · rintro ⟨hzN, z₀, ⟨hz₀R, hz₀N⟩, hz₀⟩
      exact ⟨hRsat z₀ hz₀R z (fx_plaque_leaf hN hz₀N hzN hz₀), hzN⟩
  intro p hp hp0
  by_cases hpc : p ∈ fx_cutSet φ par pick
  · -- a flow box across the picked edge through `p` misses `R`
    rcases hpc with ⟨-, h0⟩ | hpe
    · exact absurd h0 hp0
    obtain ⟨q, t, ht, rfl⟩ := mem_iUnion.1 hpe
    obtain ⟨ζ, N, hpN, hN, hplaque, -⟩ := hF.box (pick q) t ht
    refine ⟨ζ, N, hpN, hN, Or.inl ?_⟩
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hzR hzN
    obtain ⟨c, δ, -, hsq⟩ := hN.2.2.2.2
    have hw : ((ζ (par (pick q) t)).re : ℂ) + ((ζ z).im : ℂ) * I ∈ ζ '' N := by
      have hp' : ζ (par (pick q) t) ∈ ζ '' N := ⟨_, hpN, rfl⟩
      have hz' : ζ z ∈ ζ '' N := ⟨z, hzN, rfl⟩
      rw [hsq] at hp' hz' ⊢
      exact ⟨by simpa using hp'.1, by simpa using hz'.2⟩
    obtain ⟨b, hbN, hb⟩ := hw
    have hbe : b ∈ par (pick q) '' Ioo 0 1 := by
      have : b ∈ {z | z ∈ N ∧ (ζ z).re = (ζ (par (pick q) t)).re} := ⟨hbN, by rw [hb]; simp⟩
      rw [← hplaque] at this
      exact this.1
    have hbl : b ∈ fx_leaf φ z := fx_plaque_leaf hN hzN hbN (by rw [hb]; simp)
    exact Set.disjoint_left.1 (hRsub z hzR) hbl (Or.inr (mem_iUnion.2 ⟨q, hbe⟩))
  · -- a flow box inside `Δ ∖ cutSet`, where `Φ = ± ζ + C`
    have hpΩ : p ∈ unitDisc \ fx_cutSet φ par pick := ⟨hp, hpc⟩
    obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩo p hpΩ
    obtain ⟨ζ, N, hpN, hNε, hN⟩ := fx_flowBox_exists hφD hp hp0 hε
    have hNΩ : N ⊆ unitDisc \ fx_cutSet φ par pick := hNε.trans hεΩ
    obtain ⟨c, δ, -, hsq⟩ := hN.2.2.2.2
    have hNc : IsPreconnected N := by
      have hQ : IsPreconnected (ζ '' N) := by
        rw [hsq]
        exact (fx_p4_square_convex c δ).isPreconnected
      have := fx_p4_flowBox_preimage_isPreconnected hN hQ subset_rfl
      have e : N ∩ ζ ⁻¹' (ζ '' N) = N := inter_eq_left.2 (subset_preimage_image ζ N)
      rwa [e] at this
    obtain ⟨C, hC | hC⟩ := fx_p4_flowBox_sign hN subset_rfl hN.1 hNc (hΦd.mono hNΩ)
      (fun z hz => (hΦu z (hNΩ hz)).1)
    · refine ⟨ζ, N, hpN, hN, Or.inr ⟨⟨_, hplaq hN⟩, C.re, fun z hz => ?_⟩⟩
      rw [(hΦu z (hNΩ hz)).2, hC z hz, add_re]
    · have hN' := fx_p4_flowBox_neg hN
      refine ⟨fun z => -ζ z, N, hpN, hN', Or.inr ⟨⟨_, hplaq hN'⟩, C.re, fun z hz => ?_⟩⟩
      rw [(hΦu z (hNΩ hz)).2, hC z hz, add_re]

/-- **Cut calibration.**  For a cut choice, `φ` has a holomorphic square root with a primitive
`Φ` on `Δ ∖ cutSet` (each component has connected complement in `ℂ̄`, no zeros), and `u := Re Φ`
extends to a Lipschitz function on `Δ`: the jump across each picked edge is constant along it, the
jumps at a zero telescope, and induction on the rank kills them all. -/
theorem fx_cutCalib {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {ι : Type} [Fintype ι] {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι}
    {rk : ℂ → ℕ} (hpick : fx_IsCutChoice φ src dst pick rk) :
    ∃ (u : ℂ → ℝ) (Φ : ℂ → ℂ), DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par pick) ∧
      (∀ z ∈ unitDisc \ fx_cutSet φ par pick, deriv Φ z ^ 2 = φ z ∧ u z = (Φ z).re) ∧
      ∃ L : ℝ≥0, LipschitzOnWith L u unitDisc := by
  set Ω := unitDisc \ fx_cutSet φ par pick with hΩ
  have hΩo : IsOpen Ω := fx_p4_cut_isOpen hρ hφ hF pick
  obtain ⟨Φ, hΦd, hΦ2⟩ := fx_p4_cut_primitive hρ hφ hF hpick
  obtain ⟨M, hM0, hM⟩ := fx_p4_cut_bound hρ hφ (sdiff_subset : Ω ⊆ unitDisc) hΦ2
  have hedge := fx_p4_cut_heal_edges hρ hφ hF hpick hΦd hΦ2 hM0 hM
  have hzero : ∀ q : {q : ℂ // q ∈ unitDisc ∧ φ q = 0}, fx_p4_OscLe Ω Φ 0 q.1 := fun q =>
    fx_p4_zero_healed hρ hφ hF hΦd hΦ2 hM0 hM q (fx_p4_pick_inc hpick q) (fun q' _ => hedge q')
  have hall : ∀ x ∈ unitDisc, fx_p4_OscLe Ω Φ 0 x := by
    intro x hx
    by_cases hxΩ : x ∈ Ω
    · exact fx_p4_osc_of_mem hΩo hΦd.continuousOn hxΩ
    · have hxc : x ∈ fx_cutSet φ par pick := by
        by_contra h
        exact hxΩ ⟨hx, h⟩
      rcases hxc with ⟨hxD, hx0⟩ | hxe
      · exact hzero ⟨x, hxD, hx0⟩
      · obtain ⟨q, t, ht, rfl⟩ := mem_iUnion.1 hxe
        exact hedge q t ht
  have hcnt := fx_p4_u_cut_countable hF hΦd hΦ2 (pick := pick)
  refine ⟨fx_p4_uext Ω Φ, Φ, hΦd, fun z hz => ⟨hΦ2 z hz, fx_p4_uext_eq hΩo hΦd.continuousOn hz⟩,
    ⟨M, hM0⟩, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hcd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => y + (t : ℂ) * (x - y)) (x - y) t := by
    intro t
    have := (((hasDerivAt_id (t : ℂ)).mul_const (x - y)).comp_ofReal).const_add y
    simpa using this
  have hcD : ∀ t ∈ Icc (0 : ℝ) 1, y + (t : ℂ) * (x - y) ∈ unitDisc := by
    intro t ht
    have := (convex_ball (0 : ℂ) 1).add_smul_sub_mem hy hx ht
    rwa [Complex.real_smul] at this
  have hb := fx_p4_arc_bound hρ hφ hF hΦd hM0 hM hcd (norm_nonneg (x - y)) (fun _ => le_rfl)
    zero_le_one ?_ ?_
  · have e1 : y + ((1 : ℝ) : ℂ) * (x - y) = x := by push_cast; ring
    have e0 : y + ((0 : ℝ) : ℂ) * (x - y) = y := by push_cast; ring
    rw [e1, e0, sub_zero, mul_one] at hb
    rw [Real.dist_eq, dist_eq_norm]
    exact hb
  · intro t ht
    refine ⟨hcD t ht, ?_⟩
    filter_upwards [isOpen_ball.mem_nhds (hcD t ht)] with w hw
    exact hall w hw
  · refine hcnt.mono ?_
    rintro _ ⟨t, ⟨ht, htΩ⟩, rfl⟩
    refine ⟨_, ⟨hcD t ht, ?_⟩, rfl⟩
    have hcut : y + (t : ℂ) * (x - y) ∈ fx_cutSet φ par pick := by
      by_contra h
      exact htΩ ⟨hcD t ht, h⟩
    rcases hcut with ⟨-, h0⟩ | he
    · exact Or.inl h0
    · obtain ⟨q, hq⟩ := mem_iUnion.1 he
      exact Or.inr ⟨q, hq, hedge q⟩

/-- **Every leaf avoids some cut system** (`fx_star` leaves at least two free edges at each
zero; `fx_nocycle` orders the zeros). -/
theorem fx_cutChoice_avoid {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {ι : Type} [Fintype ι] {par : ι → ℝ → ℂ} {src : ι → ℂ}
    {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) {z : ℂ} (hz : z ∈ unitDisc)
    (hz0 : φ z ≠ 0) :
    ∃ (pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι) (rk : ℂ → ℕ),
      fx_IsCutChoice φ src dst pick rk ∧ Disjoint (fx_leaf φ z) (fx_cutSet φ par pick) := by
  classical
  have _ := hz
  have _ := hz0
  have hφD : DifferentiableOn ℂ φ unitDisc := hφ.mono (ball_subset_ball hρ.le)
  have hZf : Set.Finite {q : ℂ | q ∈ unitDisc ∧ φ q = 0} := hF.zeros_finite
  -- the edges not met by the leaf of `z`
  set A : Set ι := {i | ∀ w ∈ fx_leaf φ z, w ∉ par i '' Ioo 0 1} with hA
  have hA2 : ∀ q ∈ {q : ℂ | q ∈ unitDisc ∧ φ q = 0},
      2 ≤ {i | i ∈ A ∧ fx_Incident src dst i q}.ncard := by
    intro q hq
    have h3 := hF.star_card q hq.1 hq.2
    have hsub : {i | fx_Incident src dst i q} ⊆
        {i | i ∈ A ∧ fx_Incident src dst i q} ∪ {i | fx_Incident src dst i q ∧ i ∉ A} := by
      intro i hi
      by_cases hiA : i ∈ A
      · exact Or.inl ⟨hiA, hi⟩
      · exact Or.inr ⟨hi, hiA⟩
    have hmeet : ∀ i, i ∉ A → (fx_leaf φ z ∩ par i '' Ioo 0 1).Nonempty := by
      intro i hi
      by_contra h
      apply hi
      intro w hw hwi
      exact h ⟨w, hw, hwi⟩
    have hle1 : {i | fx_Incident src dst i q ∧ i ∉ A}.ncard ≤ 1 := by
      rw [Set.ncard_le_one_iff]
      intro i j hi hj
      exact fx_star hφD hne hF hi.1 hj.1 (hmeet i hi.2) (hmeet j hj.2)
    have := (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_union_le _ _)
    omega
  -- a cut choice all of whose picked edges avoid the leaf
  have hmain : ∃ (pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι) (rk : ℂ → ℕ),
      fx_IsCutChoice φ src dst pick rk ∧ ∀ q, pick q ∈ A := by
    rcases Set.eq_empty_or_nonempty {q : ℂ | q ∈ unitDisc ∧ φ q = 0} with hZe | ⟨q₁, hq₁⟩
    · have hE : IsEmpty {q : ℂ // q ∈ unitDisc ∧ φ q = 0} := by
        refine ⟨fun q => ?_⟩
        have : q.1 ∈ {q : ℂ | q ∈ unitDisc ∧ φ q = 0} := q.2
        rw [hZe] at this
        exact this
      exact ⟨fun q => (hE.false q).elim, fun _ => 0, fun q => (hE.false q).elim,
        fun q => (hE.false q).elim⟩
    obtain ⟨i₁, -⟩ : {i | fx_Incident src dst i q₁}.Nonempty := by
      apply Set.nonempty_of_ncard_ne_zero
      have := hF.star_card q₁ hq₁.1 hq₁.2
      omega
    have hpeel : ∀ n, ∀ S ⊆ {q : ℂ | q ∈ unitDisc ∧ φ q = 0}, S.ncard = n →
        ∃ (pk : ℂ → ι) (rk : ℂ → ℕ), ∀ q ∈ S, pk q ∈ A ∧
          ((src (pk q) = q ∧ ∀ q', dst (pk q) = some q' → (q' ∉ S ∨ rk q' < rk q)) ∨
            (dst (pk q) = some q ∧ (src (pk q) ∉ S ∨ rk (src (pk q)) < rk q))) := by
      intro n
      induction n with
      | zero =>
        intro S hS hSn
        refine ⟨fun _ => i₁, fun _ => 0, fun q hq => ?_⟩
        have hS0 : S = ∅ := (Set.ncard_eq_zero (hZf.subset hS)).1 hSn
        rw [hS0] at hq
        exact absurd hq (Set.notMem_empty q)
      | succ n ih =>
        intro S hS hSn
        have hSne : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
        obtain ⟨q₀, hq₀S, i₀, hi₀A, hi₀⟩ :=
          fx_nocycle hφD hne hF hS hSne (fun q hq => hA2 q (hS hq))
        have hS'n : (S \ {q₀}).ncard = n := by
          rw [Set.ncard_sdiff_singleton_of_mem hq₀S]
          omega
        obtain ⟨pk, rk, hpk⟩ := ih (S \ {q₀}) (sdiff_subset.trans hS) hS'n
        refine ⟨fun q => if q = q₀ then i₀ else pk q, fun q => if q = q₀ then 0 else rk q + 1,
          fun q hq => ?_⟩
        by_cases hqq : q = q₀
        · subst hqq
          simp only [↓reduceIte]
          refine ⟨hi₀A, ?_⟩
          rcases hi₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, fun q' hq' => Or.inl (h2 q' hq')⟩
          · exact Or.inr ⟨h1, Or.inl h2⟩
        · simp only [hqq, ↓reduceIte]
          obtain ⟨hA', hcase⟩ := hpk q ⟨hq, hqq⟩
          refine ⟨hA', ?_⟩
          rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · refine Or.inl ⟨h1, fun q' hq' => ?_⟩
            by_cases hq'0 : q' = q₀
            · right
              simp only [hq'0, ↓reduceIte]
              omega
            · simp only [hq'0, ↓reduceIte]
              rcases h2 q' hq' with h | h
              · left
                exact fun hq'S => h ⟨hq'S, hq'0⟩
              · right
                omega
          · refine Or.inr ⟨h1, ?_⟩
            by_cases hs0 : src (pk q) = q₀
            · right
              simp only [hs0, ↓reduceIte]
              omega
            · simp only [hs0, ↓reduceIte]
              rcases h2 with h | h
              · left
                exact fun hsS => h ⟨hsS, hs0⟩
              · right
                omega
    obtain ⟨pk, rk, hpk⟩ := hpeel _ _ subset_rfl rfl
    refine ⟨fun q => pk q.1, rk, fun q => ?_, fun q => (hpk q.1 q.2).1⟩
    rcases (hpk q.1 q.2).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨h1, fun q' hq' => ?_⟩
      rcases h2 q' hq' with h | h
      · exact absurd ⟨(hF.saddle _ q' hq').1, (hF.saddle _ q' hq').2.1⟩ h
      · exact h
    · refine Or.inr ⟨h1, ?_⟩
      rcases h2 with h | h
      · exact absurd (hF.src_zero _).2 h
      · exact h
  obtain ⟨pick, rk, hpick, hpA⟩ := hmain
  refine ⟨pick, rk, hpick, Set.disjoint_left.2 fun w hw hwc => ?_⟩
  rcases hwc with ⟨-, hw0⟩ | hwe
  · exact (fx_p4_leaf_reg hw).2 hw0
  · obtain ⟨q, hq⟩ := mem_iUnion.1 hwe
    exact hpA q w hw hq

/-- **The covering.**  The sets `R = {regular z : leaf z ∩ cutSet = ∅}` (measurable by
`fx_sat_open`, saturated by `fx_leaf_trans`), for the finitely many cut sets, disjointified, with the
calibrations of `fx_cutCalib`, cover `Δ` up to the finite zero set. -/
theorem fx_cover_of_forest {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ)
    (hφ : DifferentiableOn ℂ φ (ball 0 ρ)) (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {ι : Type} [Fintype ι]
    {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ} (hF : fx_IsVForest φ par src dst) :
    ∃ (N : ℕ) (R : Fin N → Set ℂ) (u : Fin N → ℂ → ℝ),
      Pairwise (Function.onFun Disjoint R) ∧ volume (unitDisc \ ⋃ i, R i) = 0 ∧
        ∀ i, fx_IsCalib φ (R i) (u i) := by
  classical
  have hφD : DifferentiableOn ℂ φ unitDisc := hφ.mono (ball_subset_ball hρ.le)
  have hZfin := fx_p4_zsub_finite hF
  set P : Set ({q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι) :=
    {pk | ∃ rk, fx_IsCutChoice φ src dst pk rk} with hP
  have hPfin : Finite P := Subtype.finite
  set e : Fin (Nat.card P) ≃ P := (Finite.equivFin P).symm with he
  have hcal : ∀ p : P, ∃ (u : ℂ → ℝ) (Φ : ℂ → ℂ),
      DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par p.1) ∧
      (∀ z ∈ unitDisc \ fx_cutSet φ par p.1, deriv Φ z ^ 2 = φ z ∧ u z = (Φ z).re) ∧
      ∃ L : ℝ≥0, LipschitzOnWith L u unitDisc := by
    intro p
    obtain ⟨rk, hrk⟩ := p.2
    exact fx_cutCalib hρ hφ hF hrk
  choose U Φ hΦd hΦu hL using hcal
  set R : P → Set ℂ := fun p =>
    {x | x ∈ unitDisc ∧ φ x ≠ 0 ∧ Disjoint (fx_leaf φ x) (fx_cutSet φ par p.1)} with hR
  -- membership in `R p` only depends on the leaf
  have hRinv : ∀ p z₀ z, z₀ ∈ unitDisc → φ z₀ ≠ 0 → z ∈ fx_leaf φ z₀ →
      (z ∈ R p ↔ z₀ ∈ R p) := by
    intro p z₀ z hz₀ hz₀0 hz
    have hzreg := fx_p4_leaf_reg hz
    have hset : fx_leaf φ z = fx_leaf φ z₀ := Set.ext fun w =>
      ⟨fun hw => fx_leaf_trans hφD hz hw, fun hw => fx_leaf_trans hφD (fx_leaf_symm hz) hw⟩
    show (z ∈ unitDisc ∧ φ z ≠ 0 ∧ Disjoint (fx_leaf φ z) (fx_cutSet φ par p.1)) ↔
      (z₀ ∈ unitDisc ∧ φ z₀ ≠ 0 ∧ Disjoint (fx_leaf φ z₀) (fx_cutSet φ par p.1))
    rw [hset]
    exact ⟨fun h => ⟨hz₀, hz₀0, h.2.2⟩, fun h => ⟨hzreg.1, hzreg.2, h.2.2⟩⟩
  set R' : Fin (Nat.card P) → Set ℂ := fun k =>
    {x | x ∈ R (e k) ∧ ∀ j : Fin (Nat.card P), j < k → x ∉ R (e j)} with hR'
  refine ⟨Nat.card P, R', fun k => U (e k), ?_, ?_, fun k => ?_⟩
  · intro j k hjk
    refine Set.disjoint_left.2 fun x hxj hxk => ?_
    rcases lt_or_gt_of_ne hjk with h | h
    · exact hxk.2 j h hxj.1
    · exact hxj.2 k h hxk.1
  · have hsub : unitDisc \ ⋃ k, R' k ⊆ {x | x ∈ unitDisc ∧ φ x = 0} := by
      rintro x ⟨hxD, hxU⟩
      refine ⟨hxD, ?_⟩
      by_contra hx0
      obtain ⟨pk, rk, hpk, hdisj⟩ := fx_cutChoice_avoid hρ hφ hne hF hxD hx0
      have hxR : x ∈ R (e (e.symm ⟨pk, rk, hpk⟩)) := by
        rw [Equiv.apply_symm_apply]
        exact ⟨hxD, hx0, hdisj⟩
      set S := Finset.univ.filter (fun k : Fin (Nat.card P) => x ∈ R (e k)) with hS
      have hSne : S.Nonempty := ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hxR⟩⟩
      apply hxU
      refine mem_iUnion.2 ⟨S.min' hSne, (Finset.mem_filter.1 (S.min'_mem hSne)).2,
        fun j hj hjx => ?_⟩
      have := S.min'_le j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hjx⟩)
      exact absurd hj (not_lt.2 this)
    exact measure_mono_null hsub (hF.zeros_finite.measure_zero volume)
  · have hRsat : ∀ z₀ ∈ R' k, ∀ z ∈ fx_leaf φ z₀, z ∈ R' k := by
      intro z₀ hz₀ z hz
      have hz₀' := hz₀.1
      refine ⟨(hRinv (e k) z₀ z hz₀'.1 hz₀'.2.1 hz).2 hz₀', fun j hj hzj => hz₀.2 j hj ?_⟩
      exact (hRinv (e j) z₀ z hz₀'.1 hz₀'.2.1 hz).1 hzj
    have hm : ∀ j, MeasurableSet (R (e j)) := fun j => fx_p4_cut_R_meas hρ hφ hF (e j).1
    have heq : R' k = R (e k) ∩ ⋂ j : Fin (Nat.card P), ⋂ (_ : j < k), (R (e j))ᶜ := by
      ext x
      simp only [hR', mem_inter_iff, mem_iInter, mem_compl_iff]
      rfl
    refine ⟨?_, fun x hx => hx.1.1, fun x hx => hx.1.2.1, hL (e k),
      fx_p4_cut_grad hρ hφ hF (e k).1 (hΦd (e k)) (hΦu (e k)),
      fx_p4_cut_calib_box hρ hφ hF (e k).1 (hΦd (e k)) (hΦu (e k)) (fun x hx => hx.1.2.2) hRsat⟩
    rw [heq]
    exact (hm k).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hm j).compl)

/-- **The geometric output**: for tame `φ ≢ 0`, `Δ` is covered, up to a null set, by finitely many
disjoint calibrated saturated sets. -/
theorem fx_cover {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) :
    ∃ (N : ℕ) (R : Fin N → Set ℂ) (u : Fin N → ℂ → ℝ),
      Pairwise (Function.onFun Disjoint R) ∧ volume (unitDisc \ ⋃ i, R i) = 0 ∧
        ∀ i, fx_IsCalib φ (R i) (u i) := by
  obtain ⟨ι, hι, par, src, dst, hF⟩ := fx_vforest_exists hρ hφ hne
  exact fx_cover_of_forest hρ hφ hne hF

/-! ## §5 The analysis -/

/-- A **good self-map** of `Δ`: `K`-quasiconformal, onto, and `g z - z → 0` uniformly as
`|z| → 1` (the boundary values are the identity). -/
def fx_IsGoodSelfMap (g : ℂ → ℂ) (K : ℝ) : Prop :=
  IsKQC g unitDisc K ∧ g '' unitDisc = unitDisc ∧
    ∀ ε > 0, ∃ δ > 0, ∀ z ∈ unitDisc, 1 - δ < ‖z‖ → ‖g z - z‖ < ε

/-! ### Helpers for the analysis: boundary identity, Pratt's lemma, flux engine -/

/-- A point of the unit circle lies in the closure of `Δ` in `ℂ̄`. -/
theorem fx_coe_mem_closure_toExt_unitDisc {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) :
    ((ζ : ℂ) : ExtPlane) ∈ closure (toExt unitDisc) := by
  have h1 : ζ ∈ closure unitDisc := by
    rw [unitDisc, closure_ball (0 : ℂ) one_ne_zero, mem_closedBall, dist_zero_right]
    exact hζ
  exact image_closure_subset_closure_image OnePoint.continuous_coe (mem_image_of_mem _ h1)

/-- **Uniform boundary identity.**  If `H` is continuous on the closed disc of `ℂ̄`, restricts to
`g` on `Δ` and to the identity on the unit circle, then `g z - z → 0` uniformly as `|z| → 1`. -/
theorem fx_boundary_uniform {g : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hHc : ContinuousOn H (closure (toExt unitDisc)))
    (hHg : ∀ z ∈ unitDisc, H (z : ExtPlane) = ((g z : ℂ) : ExtPlane))
    (hHid : ∀ ζ : ℂ, ‖ζ‖ = 1 → H (ζ : ExtPlane) = (ζ : ExtPlane)) :
    ∀ ε > 0, ∃ δ > 0, ∀ z ∈ unitDisc, 1 - δ < ‖z‖ → ‖g z - z‖ < ε := by
  intro ε hε
  -- local convergence at each point of the circle
  have hloc : ∀ ζ ∈ sphere (0 : ℂ) 1, ∀ᶠ z in 𝓝 ζ, z ∈ unitDisc → ‖g z - z‖ < ε := by
    intro ζ hζ
    have hζ1 : ‖ζ‖ = 1 := by simpa using hζ
    have hcl := fx_coe_mem_closure_toExt_unitDisc hζ1.le
    have hH : Tendsto H (𝓝[closure (toExt unitDisc)] (ζ : ExtPlane)) (𝓝 (ζ : ExtPlane)) := by
      have := hHc _ hcl
      rwa [ContinuousWithinAt, hHid ζ hζ1] at this
    have hcoe : Tendsto (fun z : ℂ => (z : ExtPlane)) (𝓝[unitDisc] ζ)
        (𝓝[closure (toExt unitDisc)] (ζ : ExtPlane)) :=
      OnePoint.continuous_coe.continuousWithinAt.tendsto_nhdsWithin
        (fun z hz => subset_closure (mem_image_of_mem _ hz))
    have h2 : Tendsto (fun z : ℂ => ((g z : ℂ) : ExtPlane)) (𝓝[unitDisc] ζ) (𝓝 (ζ : ExtPlane)) :=
      (hH.comp hcoe).congr' (eventually_nhdsWithin_of_forall fun z hz => hHg z hz)
    have h3 : Tendsto g (𝓝[unitDisc] ζ) (𝓝 ζ) :=
      (OnePoint.isOpenEmbedding_coe.isInducing.tendsto_nhds_iff).2 h2
    have h4 : Tendsto (fun z => g z - z) (𝓝[unitDisc] ζ) (𝓝 0) := by
      have := h3.sub (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 ζ)))
      rwa [sub_self] at this
    have h5 : ∀ᶠ z in 𝓝[unitDisc] ζ, ‖g z - z‖ < ε := by
      have h6 := h4.norm
      rw [norm_zero] at h6
      exact h6.eventually (gt_mem_nhds hε)
    exact eventually_nhdsWithin_iff.1 h5
  have hS : ∀ᶠ z in 𝓝ˢ (sphere (0 : ℂ) 1), z ∈ unitDisc → ‖g z - z‖ < ε :=
    eventually_nhdsSet_iff_forall.2 hloc
  obtain ⟨δ, hδ, hδS⟩ :=
    (Metric.hasBasis_nhdsSet_thickening (isCompact_sphere (0 : ℂ) 1)).eventually_iff.1 hS
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), fun z hz hzn => ?_⟩
  have hz0 : 0 < ‖z‖ := by
    have := min_le_right δ (1 / 2 : ℝ)
    linarith
  have hz1 : ‖z‖ < 1 := by simpa [unitDisc] using hz
  apply hδS _ hz
  rw [mem_thickening_iff]
  refine ⟨((1 / ‖z‖ : ℝ) : ℂ) * z, ?_, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.2 hz0), one_div, inv_mul_cancel₀ hz0.ne']
  · rw [dist_eq_norm]
    have e : z - ((1 / ‖z‖ : ℝ) : ℂ) * z = ((1 - 1 / ‖z‖ : ℝ) : ℂ) * z := by
      push_cast; ring
    rw [e, norm_mul, norm_real, Real.norm_eq_abs]
    have hlt : 1 - 1 / ‖z‖ < 0 := by
      rw [sub_neg, lt_one_div (by norm_num) hz0]
      simpa using hz1
    rw [abs_of_neg hlt]
    have : -(1 - 1 / ‖z‖) * ‖z‖ = 1 - ‖z‖ := by field_simp; ring
    rw [this]
    have := min_le_left δ (1 / 2 : ℝ)
    linarith

/-- **Pratt's lemma** (generalized dominated convergence, lower-integral form): if `f n ≤ d n`,
`f n → F` and `d n → D` a.e., `∫ d n → ∫ D < ∞`, and `e n ≤ ∫ f n` with `e n → A`, then
`A ≤ ∫ F`.  (Fatou applied to `d n - f n`.) -/
theorem fx_pratt {α : Type*} [MeasurableSpace α] {μ : Measure α} {f d : ℕ → α → ℝ≥0∞}
    {F D : α → ℝ≥0∞} {e : ℕ → ℝ≥0∞} {A : ℝ≥0∞}
    (hfm : ∀ n, AEMeasurable (f n) μ) (hdm : ∀ n, AEMeasurable (d n) μ)
    (hfd : ∀ n, f n ≤ᵐ[μ] d n)
    (hf : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hd : ∀ᵐ x ∂μ, Tendsto (fun n => d n x) atTop (𝓝 (D x)))
    (hint : Tendsto (fun n => ∫⁻ x, d n x ∂μ) atTop (𝓝 (∫⁻ x, D x ∂μ)))
    (hD : ∫⁻ x, D x ∂μ ≠ ⊤)
    (he : Tendsto e atTop (𝓝 A)) (hef : ∀ n, e n ≤ ∫⁻ x, f n x ∂μ) :
    A ≤ ∫⁻ x, F x ∂μ := by
  have hFm : AEMeasurable F μ := aemeasurable_of_tendsto_metrizable_ae' hfm hf
  have hDm : AEMeasurable D μ := aemeasurable_of_tendsto_metrizable_ae' hdm hd
  have hFD : F ≤ᵐ[μ] D := by
    have hall : ∀ᵐ x ∂μ, ∀ n, f n x ≤ d n x := ae_all_iff.2 hfd
    filter_upwards [hf, hd, hall] with x h1 h2 h3
    exact le_of_tendsto_of_tendsto' h1 h2 h3
  have hDfin : ∀ᵐ x ∂μ, D x ≠ ⊤ := (ae_lt_top' hDm hD).mono fun x hx => hx.ne
  have hFint : ∫⁻ x, F x ∂μ ≠ ⊤ := ne_top_of_le_ne_top hD (lintegral_mono_ae hFD)
  -- Fatou on `d n - f n`
  have hfatou := lintegral_liminf_le' (μ := μ) (u := atTop)
    (fun n => (hdm n).sub (hfm n))
  have hlim : ∀ᵐ x ∂μ, liminf (fun n => d n x - f n x) atTop = D x - F x := by
    filter_upwards [hf, hd, hDfin] with x h1 h2 h3
    exact (ENNReal.Tendsto.sub h2 h1 (Or.inl h3)).liminf_eq
  simp only [Pi.sub_apply] at hfatou
  rw [lintegral_congr_ae hlim, lintegral_sub' hFm hFint hFD] at hfatou
  -- `∫ (d n - f n) ≤ ∫ d n - e n` eventually
  have hev : ∀ᶠ n in atTop, ∫⁻ x, d n x - f n x ∂μ ≤ (∫⁻ x, d n x ∂μ) - e n := by
    have hlt : ∀ᶠ n in atTop, ∫⁻ x, d n x ∂μ < ⊤ :=
      hint.eventually (gt_mem_nhds (lt_top_iff_ne_top.2 hD))
    filter_upwards [hlt] with n hn
    have hfn : ∫⁻ x, f n x ∂μ ≠ ⊤ :=
      ne_top_of_le_ne_top hn.ne (lintegral_mono_ae (hfd n))
    rw [lintegral_sub' (hfm n) hfn (hfd n)]
    exact tsub_le_tsub_left (hef n) _
  have hlim2 : Tendsto (fun n => (∫⁻ x, d n x ∂μ) - e n) atTop (𝓝 ((∫⁻ x, D x ∂μ) - A)) :=
    ENNReal.Tendsto.sub hint he (Or.inl hD)
  have hkey : (∫⁻ x, D x ∂μ) - ∫⁻ x, F x ∂μ ≤ (∫⁻ x, D x ∂μ) - A := by
    refine hfatou.trans ?_
    rw [← hlim2.liminf_eq]
    exact liminf_le_liminf hev
  have hAD : A ≤ ∫⁻ x, D x ∂μ := by
    refine le_of_tendsto_of_tendsto' he hint fun n => (hef n).trans ?_
    exact lintegral_mono_ae (hfd n)
  have hFD' : ∫⁻ x, F x ∂μ ≤ ∫⁻ x, D x ∂μ := lintegral_mono_ae hFD
  calc A = (∫⁻ x, D x ∂μ) - ((∫⁻ x, D x ∂μ) - A) := (ENNReal.sub_sub_cancel hD hAD).symm
    _ ≤ (∫⁻ x, D x ∂μ) - ((∫⁻ x, D x ∂μ) - ∫⁻ x, F x ∂μ) := tsub_le_tsub_left hkey _
    _ = ∫⁻ x, F x ∂μ := ENNReal.sub_sub_cancel hD hFD'

/-- The dilation `z ↦ r z` maps `Δ` conformally onto `B(0, r)`. -/
theorem fx_isConformalOnto_mul_real {r : ℝ} (hr : 0 < r) :
    IsConformalOnto (fun z : ℂ => (r : ℂ) * z) unitDisc (ball 0 r) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨(differentiable_id.const_mul _).differentiableOn, fun z _ w _ h => mul_left_cancel₀ hr0 h,
    ?_⟩
  ext w
  simp only [mem_image, unitDisc, mem_ball_zero_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hr]
    nlinarith [norm_nonneg z]
  · intro hw
    refine ⟨w / r, ?_, by field_simp⟩
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr, div_lt_one hr]
    exact hw

/-- `A_{φ_r}(Δ) = A_φ(B(0, r))` for `φ_r(z) = r² φ(r z)`. -/
theorem fx_phiArea_rescale (φ : ℂ → ℂ) {r : ℝ} (hr : 0 < r) :
    phiArea (fun z => (r : ℂ) ^ 2 * φ (r * z)) unitDisc =
      ∫⁻ w in ball 0 r, ENNReal.ofReal ‖φ w‖ := by
  rw [lintegral_image_conformal isOpen_ball (fx_isConformalOnto_mul_real hr)
    (fun w => ENNReal.ofReal ‖φ w‖), phiArea]
  refine setLIntegral_congr_fun isOpen_ball.measurableSet fun z _ => ?_
  have hd : deriv (fun z : ℂ => (r : ℂ) * z) z = r := by
    simp
  rw [hd, norm_mul, norm_pow, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The pointwise integrand `|p| λ = √|p| √|q| |A + B p/|p||` (also when `p = 0`). -/
theorem fx_norm_mul_lambda (p q A B : ℂ) :
    ‖p‖ * (Real.sqrt ‖q‖ * ‖A + B * (p / (‖p‖ : ℂ))‖ / Real.sqrt ‖p‖) =
      Real.sqrt ‖p‖ * Real.sqrt ‖q‖ * ‖A + B * (p / (‖p‖ : ℂ))‖ := by
  by_cases hp : p = 0
  · simp [hp]
  have hpos : 0 < Real.sqrt ‖p‖ := Real.sqrt_pos.2 (norm_pos_iff.2 hp)
  have hs : Real.sqrt ‖p‖ * Real.sqrt ‖p‖ = ‖p‖ := Real.mul_self_sqrt (norm_nonneg _)
  set X := ‖A + B * (p / (‖p‖ : ℂ))‖
  set a := Real.sqrt ‖p‖
  rw [mul_div_assoc', div_eq_iff hpos.ne', ← hs]
  ring

/-- The AM–GM domination `√|p| √|q| |A + B p/|p|| ≤ |p| + K J |q|` when `(|A|+|B|)² ≤ K J`. -/
theorem fx_amgm_bound (p q A B : ℂ) {K J : ℝ} (hKJ : (‖A‖ + ‖B‖) ^ 2 ≤ K * J) :
    Real.sqrt ‖p‖ * Real.sqrt ‖q‖ * ‖A + B * (p / (‖p‖ : ℂ))‖ ≤ ‖p‖ + K * J * ‖q‖ := by
  set X := ‖A + B * (p / (‖p‖ : ℂ))‖
  have hX : X ≤ ‖A‖ + ‖B‖ := by
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul]
    have : ‖p / (‖p‖ : ℂ)‖ ≤ 1 := by
      by_cases hp : p = 0
      · simp [hp]
      rw [norm_div, norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hp)]
    nlinarith [norm_nonneg B]
  have hX0 : 0 ≤ X := norm_nonneg _
  set a := Real.sqrt ‖p‖
  set b := Real.sqrt ‖q‖
  have ha : a ^ 2 = ‖p‖ := Real.sq_sqrt (norm_nonneg _)
  have hb : b ^ 2 = ‖q‖ := Real.sq_sqrt (norm_nonneg _)
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have h1 : a * b * X ≤ a ^ 2 + b ^ 2 * X ^ 2 := by nlinarith [sq_nonneg (a - b * X)]
  have h2 : X ^ 2 ≤ K * J := by nlinarith
  have h3 : b ^ 2 * X ^ 2 ≤ K * J * b ^ 2 := by nlinarith [sq_nonneg b]
  rw [← ha, ← hb]
  linarith

/-- Continuity of `(p, q) ↦ √|p| √|q| |A + B p/|p||` along sequences (it tends to `0` at `p = 0`). -/
theorem fx_tendsto_P {A B : ℂ} {p q : ℕ → ℂ} {p₀ q₀ : ℂ} (hp : Tendsto p atTop (𝓝 p₀))
    (hq : Tendsto q atTop (𝓝 q₀)) :
    Tendsto (fun n => Real.sqrt ‖p n‖ * Real.sqrt ‖q n‖ * ‖A + B * (p n / (‖p n‖ : ℂ))‖) atTop
      (𝓝 (Real.sqrt ‖p₀‖ * Real.sqrt ‖q₀‖ * ‖A + B * (p₀ / (‖p₀‖ : ℂ))‖)) := by
  have hsp : Tendsto (fun n => Real.sqrt ‖p n‖) atTop (𝓝 (Real.sqrt ‖p₀‖)) :=
    (Real.continuous_sqrt.tendsto _).comp hp.norm
  have hsq : Tendsto (fun n => Real.sqrt ‖q n‖) atTop (𝓝 (Real.sqrt ‖q₀‖)) :=
    (Real.continuous_sqrt.tendsto _).comp hq.norm
  by_cases h0 : p₀ = 0
  · subst h0
    simp only [norm_zero, Real.sqrt_zero, zero_mul]
    have hsp0 : Tendsto (fun n => Real.sqrt ‖p n‖) atTop (𝓝 0) := by
      simp only [norm_zero, Real.sqrt_zero] at hsp
      exact hsp
    have hbound : Tendsto (fun n => Real.sqrt ‖p n‖ * Real.sqrt ‖q n‖ * (‖A‖ + ‖B‖)) atTop
        (𝓝 0) := by
      simpa using (hsp0.mul hsq).mul_const (‖A‖ + ‖B‖)
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hbound
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul]
    have : ‖p n / (‖p n‖ : ℂ)‖ ≤ 1 := by
      by_cases hpn : p n = 0
      · simp [hpn]
      rw [norm_div, norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hpn)]
    nlinarith [norm_nonneg B]
  · have hn : Tendsto (fun n => ((‖p n‖ : ℝ) : ℂ)) atTop (𝓝 ((‖p₀‖ : ℝ) : ℂ)) :=
      (continuous_ofReal.tendsto _).comp hp.norm
    have hdiv : Tendsto (fun n => p n / (‖p n‖ : ℂ)) atTop (𝓝 (p₀ / (‖p₀‖ : ℂ))) :=
      hp.div hn (by exact_mod_cast (norm_ne_zero_iff.2 h0))
    exact (hsp.mul hsq).mul ((tendsto_const_nhds.add (tendsto_const_nhds.mul hdiv)).norm)

/-- `φ_r(z) = r² φ(r z) → φ(z)` as `r → 1`, at a point of continuity. -/
theorem fx_tendsto_rescale {φ : ℂ → ℂ} {z : ℂ} (hφ : ContinuousAt φ z) {r : ℕ → ℝ}
    (hr : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => (r n : ℂ) ^ 2 * φ (r n * z)) atTop (𝓝 (φ z)) := by
  have hrc : Tendsto (fun n => (r n : ℂ)) atTop (𝓝 (1 : ℂ)) := by
    have h := (continuous_ofReal.tendsto 1).comp hr
    rw [Complex.ofReal_one] at h
    exact h
  have h1 : Tendsto (fun n => (r n : ℂ) * z) atTop (𝓝 z) := by
    simpa using hrc.mul_const z
  have h2 : Tendsto (fun n => φ ((r n : ℂ) * z)) atTop (𝓝 (φ z)) := hφ.tendsto.comp h1
  simpa using (hrc.pow 2).mul h2

/-- A tame `φ ≢ 0` has finitely many zeros in `Δ` (identity theorem on `B(0, ρ)`, `ρ > 1`). -/
theorem fx_zeros_finite {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) : {q : ℂ | q ∈ unitDisc ∧ φ q = 0}.Finite := by
  by_contra hinf
  have hsub : {q : ℂ | q ∈ unitDisc ∧ φ q = 0} ⊆ closedBall 0 1 := fun q hq =>
    ball_subset_closedBall hq.1
  obtain ⟨x, hx, hacc⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
    (isCompact_closedBall 0 1) hsub
  have hxρ : x ∈ ball (0 : ℂ) ρ := closedBall_subset_ball hρ hx
  have han : AnalyticOnNhd ℂ φ (ball 0 ρ) := hφ.analyticOnNhd isOpen_ball
  have hfreq : ∃ᶠ z in 𝓝[≠] x, φ z = 0 := by
    rw [accPt_iff_frequently_nhdsNE] at hacc
    exact hacc.mono fun z hz => hz.2
  have h0 := han.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball (0 : ℂ) ρ).isPreconnected hxρ hfreq
  obtain ⟨z, hz, hz0⟩ := hne
  exact hz0 (h0 (ball_subset_ball hρ.le hz))

/-- The product of two bounded Lipschitz functions is Lipschitz. -/
theorem fx_lipschitz_mul {f h : ℂ → ℝ} {Cf Ch : ℝ≥0} {Mf Mh : ℝ} (hf : LipschitzWith Cf f)
    (hh : LipschitzWith Ch h) (hfM : ∀ x, |f x| ≤ Mf) (hhM : ∀ x, |h x| ≤ Mh) :
    ∃ C : ℝ≥0, LipschitzWith C (fun x => f x * h x) := by
  have hMf : 0 ≤ Mf := (abs_nonneg _).trans (hfM 0)
  have hMh : 0 ≤ Mh := (abs_nonneg _).trans (hhM 0)
  refine ⟨⟨Mf * Ch + Mh * Cf, by positivity⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simp only [Real.dist_eq]
  have e : f x * h x - f y * h y = f x * (h x - h y) + h y * (f x - f y) := by ring
  rw [e]
  have h1 : |h x - h y| ≤ Ch * dist x y := by
    rw [← Real.dist_eq]; exact hh.dist_le_mul x y
  have h2 : |f x - f y| ≤ Cf * dist x y := by
    rw [← Real.dist_eq]; exact hf.dist_le_mul x y
  calc |f x * (h x - h y) + h y * (f x - f y)|
      ≤ |f x| * |h x - h y| + |h y| * |f x - f y| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ Mf * (Ch * dist x y) + Mh * (Cf * dist x y) := by
        gcongr
        · exact hfM x
        · exact hhM y
    _ = (Mf * Ch + Mh * Cf) * dist x y := by ring

/-- A Lipschitz function with compact support is bounded. -/
theorem fx_bound_of_lipschitz {ψ : ℂ → ℝ} {C : ℝ≥0} (hψ : LipschitzWith C ψ)
    (hc : HasCompactSupport ψ) : ∃ M, ∀ x, |ψ x| ≤ M := by
  obtain ⟨M, hM⟩ := hψ.continuous.bounded_above_of_compact_support hc
  exact ⟨M, fun x => by simpa using hM x⟩

/-- **Partition of unity, by induction on a finite cover.**  A functional `T`, additive on
Lipschitz functions of compact support, which vanishes on those supported in any member of a finite
family of open sets, vanishes on those supported in their union. -/
theorem fx_partition (T : (ℂ → ℝ) → ℝ)
    (hadd : ∀ ψ₁ ψ₂ : ℂ → ℝ, (∃ C, LipschitzWith C ψ₁) → HasCompactSupport ψ₁ →
      (∃ C, LipschitzWith C ψ₂) → HasCompactSupport ψ₂ → T (ψ₁ + ψ₂) = T ψ₁ + T ψ₂)
    (s : Finset (Set ℂ))
    (hs : ∀ N ∈ s, IsOpen N ∧ ∀ ψ : ℂ → ℝ, (∃ C, LipschitzWith C ψ) → HasCompactSupport ψ →
      tsupport ψ ⊆ N → T ψ = 0) :
    ∀ ψ : ℂ → ℝ, (∃ C, LipschitzWith C ψ) → HasCompactSupport ψ →
      tsupport ψ ⊆ ⋃ N ∈ s, N → T ψ = 0 := by
  classical
  have hT0 : T 0 = 0 := by
    have h := hadd 0 0 ⟨0, LipschitzWith.const 0⟩ HasCompactSupport.zero ⟨0, LipschitzWith.const 0⟩
      HasCompactSupport.zero
    rw [add_zero] at h
    linarith
  induction s using Finset.induction_on with
  | empty =>
    intro ψ _ _ hsub
    have hψ : ψ = 0 := by
      funext x
      by_contra hx
      have := hsub (subset_tsupport ψ hx)
      simp at this
    rw [hψ, hT0]
  | insert a s has ih =>
    intro ψ ⟨C, hψl⟩ hψc hsub
    have hs' : ∀ N ∈ s, IsOpen N ∧ ∀ ψ : ℂ → ℝ, (∃ C, LipschitzWith C ψ) → HasCompactSupport ψ →
        tsupport ψ ⊆ N → T ψ = 0 := fun N hN => hs N (Finset.mem_insert_of_mem hN)
    obtain ⟨hao, haT⟩ := hs a (Finset.mem_insert_self a s)
    set U : Set ℂ := ⋃ N ∈ s, N with hU
    have hUo : IsOpen U := isOpen_biUnion fun N hN => (hs' N hN).1
    set Kψ := tsupport ψ with hKψ
    set A : Set ℂ := Kψ \ U with hA
    have hAc : IsCompact A := hψc.isCompact.diff hUo
    have hAa : A ⊆ a := by
      intro z hz
      have h1 := hsub hz.1
      simp only [Finset.set_biUnion_insert, mem_union] at h1
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd h1 hz.2
    rcases A.eq_empty_or_nonempty with hA0 | hAne
    · refine ih hs' ψ ⟨C, hψl⟩ hψc fun z hz => ?_
      by_contra hzU
      have : z ∈ A := ⟨hz, hzU⟩
      rw [hA0] at this
      exact this
    obtain ⟨δ, hδ, hδa⟩ := hAc.exists_cthickening_subset_open hao hAa
    set r := δ / 2 with hr
    have hr0 : 0 < r := by positivity
    set h : ℂ → ℝ := fun z => max 0 (min 1 (2 - infDist z A / r)) with hh
    have hhl : LipschitzWith (⟨1 / r, by positivity⟩ : ℝ≥0) h := by
      have h1 : LipschitzWith (⟨1 / r, by positivity⟩ : ℝ≥0) (fun z => 2 - infDist z A / r) := by
        refine LipschitzWith.of_dist_le_mul fun x y => ?_
        simp only [Real.dist_eq]
        have := (lipschitz_infDist_pt (s := A)).dist_le_mul x y
        simp only [NNReal.coe_one, one_mul, Real.dist_eq] at this
        rw [show 2 - infDist x A / r - (2 - infDist y A / r) = -((infDist x A - infDist y A) / r)
          by ring, abs_neg, abs_div, abs_of_pos hr0]
        rw [div_le_iff₀ hr0]
        calc |infDist x A - infDist y A| ≤ dist x y := this
          _ = 1 / r * dist x y * r := by field_simp
      exact (h1.const_min 1).const_max 0
    have hh01 : ∀ z, |h z| ≤ 1 := fun z => by
      rw [abs_le]
      constructor
      · have : 0 ≤ h z := le_max_left _ _
        linarith
      · exact max_le zero_le_one (min_le_left _ _)
    have h1h01 : ∀ z, |1 - h z| ≤ 1 := fun z => by
      have h1 : 0 ≤ h z := le_max_left _ _
      have h2 : h z ≤ 1 := max_le zero_le_one (min_le_left _ _)
      rw [abs_le]
      constructor <;> linarith
    have hhsupp : tsupport h ⊆ a := by
      refine (closure_mono ?_).trans ((closure_thickening_subset_cthickening δ A).trans hδa)
      intro z hz
      rw [mem_thickening_iff_infDist_lt hAne]
      by_contra hle
      push Not at hle
      apply hz
      simp only [hh]
      have : 2 - infDist z A / r ≤ 0 := by
        rw [sub_nonpos, le_div_iff₀ hr0]
        linarith
      rw [min_eq_right (this.trans zero_le_one), max_eq_left this]
    have hh1 : ∀ z ∈ thickening r A, h z = 1 := by
      intro z hz
      rw [mem_thickening_iff_infDist_lt hAne] at hz
      simp only [hh]
      have : 1 ≤ 2 - infDist z A / r := by
        rw [le_sub_comm, div_le_iff₀ hr0]
        linarith
      rw [min_eq_left this, max_eq_right zero_le_one]
    obtain ⟨Mψ, hMψ⟩ := fx_bound_of_lipschitz hψl hψc
    have hl1 : LipschitzWith (⟨1 / r, by positivity⟩ : ℝ≥0) (fun z => 1 - h z) := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, show 1 - h x - (1 - h y) = -(h x - h y) by ring, abs_neg, ← Real.dist_eq]
      exact hhl.dist_le_mul x y
    obtain ⟨C₁, hC₁⟩ := fx_lipschitz_mul hhl hψl hh01 hMψ
    obtain ⟨C₂, hC₂⟩ := fx_lipschitz_mul hl1 hψl h1h01 hMψ
    have hc₁ : HasCompactSupport (fun z => h z * ψ z) := hψc.mul_left
    have hc₂ : HasCompactSupport (fun z => (1 - h z) * ψ z) := hψc.mul_left
    have hsplit : ψ = (fun z => h z * ψ z) + (fun z => (1 - h z) * ψ z) := by
      funext z
      simp only [Pi.add_apply]
      ring
    rw [hsplit, hadd _ _ ⟨C₁, hC₁⟩ hc₁ ⟨C₂, hC₂⟩ hc₂]
    have hT1 : T (fun z => h z * ψ z) = 0 :=
      haT _ ⟨C₁, hC₁⟩ hc₁ ((tsupport_mul_subset_left (f := h) (g := ψ)).trans hhsupp)
    have hT2 : T (fun z => (1 - h z) * ψ z) = 0 := by
      refine ih hs' _ ⟨C₂, hC₂⟩ hc₂ fun z hz => ?_
      have hz1 : z ∈ tsupport (fun z => 1 - h z) := tsupport_mul_subset_left hz
      have hz2 : z ∈ Kψ := tsupport_mul_subset_right hz
      have hz3 : z ∉ thickening r A := by
        have hcl : tsupport (fun z => 1 - h z) ⊆ (thickening r A)ᶜ := by
          refine closure_minimal (fun y hy => ?_) isOpen_thickening.isClosed_compl
          intro hyA
          apply hy
          simp only [hh1 y hyA, sub_self]
        exact hcl hz1
      by_contra hzU
      exact hz3 (self_subset_thickening hr0 A ⟨hz2, hzU⟩)
    rw [hT1, hT2, add_zero]

/-- Pulling back an a.e. statement on `Δ` through a q.c. self-map of `Δ` (Lusin (N) for the
inverse). -/
theorem fx_ae_comp {g : ℂ → ℂ} {K : ℝ} (hgK : IsKQC g unitDisc K) (hgs : g '' unitDisc = unitDisc)
    {P : ℂ → Prop} (hP : ∀ᵐ y ∂(volume.restrict unitDisc), P y) :
    ∀ᵐ z ∂(volume.restrict unitDisc), P (g z) := by
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  set ginv := Function.invFunOn g unitDisc with hginv
  have hinvK : IsKQC ginv unitDisc K := by
    have h := thm7_2_inv hgK
    rwa [hgs] at h
  set B : Set ℂ := {y | y ∈ unitDisc ∧ ¬ P y} with hB
  have hB0 : volume B = 0 := by
    rw [ae_restrict_iff' hΔ, ae_iff] at hP
    refine measure_mono_null (fun y hy => ?_) hP
    exact fun h => hy.2 (h hy.1)
  have hBimg : volume (ginv '' B) = 0 :=
    ac_n_volume_image_null_of_isKQC hinvK (fun y hy => hy.1) hB0
  rw [ae_restrict_iff' hΔ, ae_iff]
  refine measure_mono_null (fun z hz => ?_) hBimg
  simp only [Classical.not_imp, mem_ofPred_eq] at hz
  obtain ⟨hzΔ, hPz⟩ := hz
  have hgz : g z ∈ unitDisc := hgs ▸ mem_image_of_mem g hzΔ
  exact ⟨g z, ⟨hgz, hPz⟩, hgK.2.2.1.2.1.leftInvOn_invFunOn hzΔ⟩

/-- The gradient vector `∇u = u_x + i u_y` of a real function, as a complex number. -/
def fx_grad (u : ℂ → ℝ) (z : ℂ) : ℂ := (fderiv ℝ u z 1 : ℂ) + I * (fderiv ℝ u z I : ℂ)

/-- A real-linear functional on `ℂ` is determined by its values at `1` and `i`. -/
theorem fx_clm_apply (A : ℂ →L[ℝ] ℝ) (v : ℂ) : A v = v.re * A 1 + v.im * A I := by
  conv_lhs => rw [← Complex.re_add_im v]
  rw [show (v.re : ℂ) + v.im * I = v.re • (1 : ℂ) + v.im • I by simp, map_add, map_smul,
    map_smul, smul_eq_mul, smul_eq_mul]

/-- In a chart where `u = Re ζ + c` near `z` with `ζ'(z) = s`: `u'(z)(h) = Re (s h)` and
`∇u(z) = conj s`. -/
theorem fx_fderiv_of_eq_re {u : ℂ → ℝ} {ζ : ℂ → ℂ} {z s : ℂ} {c : ℝ}
    (hu : ∀ᶠ y in 𝓝 z, u y = (ζ y).re + c) (hζ : HasDerivAt ζ s z) :
    (∀ h : ℂ, fderiv ℝ u z h = (s * h).re) ∧ fx_grad u z = conj s := by
  have hF : HasFDerivAt (fun w => (ζ w).re + c)
      (Complex.reCLM.comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) s).restrictScalars ℝ))
      z :=
    (Complex.reCLM.hasFDerivAt.comp z (hζ.hasFDerivAt.restrictScalars ℝ)).add_const c
  have hF' : HasFDerivAt u
      (Complex.reCLM.comp ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) s).restrictScalars ℝ))
      z := hF.congr_of_eventuallyEq hu
  have hval : ∀ h : ℂ, fderiv ℝ u z h = (s * h).re := by
    intro h
    rw [hF'.fderiv]
    simp [mul_comm]
  refine ⟨hval, ?_⟩
  rw [fx_grad, hval, hval]
  apply Complex.ext <;> simp

/-- Fubini on the open rectangle `(a, b) × (c, d)`, integrating first in `x` (real-valued). -/
theorem fx_setIntegral_openRect_symm {G : ℂ → ℝ} {a b c d : ℝ}
    (hG : IntegrableOn G (openRect a b c d)) :
    ∫ z in openRect a b c d, G z =
      ∫ y in Ioo c d, ∫ x in Ioo a b, G ((x : ℂ) + (y : ℂ) * I) := by
  have he := Complex.measurableEquivRealProd.symm.measurableEmbedding
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' openRect a b c d = Ioo a b ×ˢ Ioo c d := by
    ext p
    simp [openRect, Complex.measurableEquivRealProd, and_assoc]
  have himg : Complex.measurableEquivRealProd.symm '' (Ioo a b ×ˢ Ioo c d) = openRect a b c d := by
    rw [← hpre, image_preimage_eq_of_subset]
    intro z _
    exact ⟨Complex.measurableEquivRealProd z, by simp⟩
  have hint : IntegrableOn (fun p => G (Complex.measurableEquivRealProd.symm p))
      (Ioo a b ×ˢ Ioo c d) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod, ← hpre]
    exact (he.integrableOn_map_iff).1 (by rw [hmp.map_eq]; exact hG)
  rw [← himg, hmp.setIntegral_image_emb he, Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod_symm _ (by rw [Measure.prod_restrict]; exact hint)]
  refine setIntegral_congr_fun measurableSet_Ioo fun y _ =>
    setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
  congr 1
  apply Complex.ext <;> simp [Complex.measurableEquivRealProd]

/-- Off the topological support, the derivative vanishes. -/
theorem fx_fderiv_eq_zero_of_notMem {ψ : ℂ → ℝ} {z : ℂ} (hz : z ∉ tsupport ψ) :
    fderiv ℝ ψ z = 0 := by
  by_contra h
  exact hz (support_fderiv_subset ℝ h)

/-- `conj s = |s|² s⁻¹` (as a real multiple). -/
theorem fx_conj_eq_smul_inv {s : ℂ} (hs : s ≠ 0) : conj s = (‖s‖ ^ 2 : ℝ) • s⁻¹ := by
  rw [Complex.real_smul]
  have h1 : ((‖s‖ ^ 2 : ℝ) : ℂ) = s * conj s := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h1]
  field_simp

/-- **The local flux identity** in a flow box `N` in which `R` is a union of horizontal plaques and
`u = Re ζ + c`: for `ψ` Lipschitz with compact support in `N`,
`∬_R ψ ⟨∇u, ∇w⟩ + w ⟨∇u, ∇ψ⟩ = 0`, `w = u ∘ g - u`.  In the natural parameter the integrand is
`∂_ξ (ψ w)` on the plaques (the conformal factors cancel), and `ξ ↦ ψ w` is absolutely continuous
on almost every plaque (`g ∘ ζ⁻¹` is A.C.L., `u` is Lipschitz). -/
theorem fx_flux_local {φ ζ g : ℂ → ℂ} {u ψ : ℂ → ℝ} {N R : Set ℂ} {E : Set ℝ} {c K : ℝ}
    {Lu Lψ : ℝ≥0}
    (hN : fx_IsFlowBox φ ζ N) (hRN : R ∩ N = {z | z ∈ N ∧ (ζ z).im ∈ E})
    (hu : ∀ z ∈ N, u z = (ζ z).re + c) (hR : MeasurableSet R)
    (hgK : IsKQC g unitDisc K) (hgm : MapsTo g unitDisc unitDisc)
    (hul : LipschitzOnWith Lu u unitDisc)
    (hψl : LipschitzWith Lψ ψ) (hψc : HasCompactSupport ψ) (hψN : tsupport ψ ⊆ N)
    (hwd : ∀ᵐ z ∂(volume.restrict unitDisc), DifferentiableAt ℝ (fun y => u (g y) - u y) z)
    (hint : IntegrableOn (fun z => ψ z * fderiv ℝ (fun y => u (g y) - u y) z (fx_grad u z) +
       (u (g z) - u z) * fderiv ℝ ψ z (fx_grad u z)) R) :
    ∫ z in R, (ψ z * fderiv ℝ (fun y => u (g y) - u y) z (fx_grad u z) +
       (u (g z) - u z) * fderiv ℝ ψ z (fx_grad u z)) = 0 := by
  obtain ⟨hNo, hNΔ, hζi, hζ, c0, δ, hδ, hQ⟩ := hN
  set w : ℂ → ℝ := fun y => u (g y) - u y with hw
  set F : ℂ → ℝ := fun z => ψ z * fderiv ℝ w z (fx_grad u z) +
    w z * fderiv ℝ ψ z (fx_grad u z) with hF
  set Q := ζ '' N with hQdef
  have hζd : DifferentiableOn ℂ ζ N := fun z hz => (hζ z hz).2.1.differentiableWithinAt
  have hζconf : IsConformalOnto ζ N Q := ⟨hζd, hζi, rfl⟩
  have hQo : IsOpen Q := hζconf.isOpen hNo
  set ψ₀ := Function.invFunOn ζ N with hψ₀
  have hψ₀conf : IsConformalOnto ψ₀ Q N := hζconf.symm hNo
  have hψ₀N : ∀ x ∈ Q, ψ₀ x ∈ N := fun x hx => Function.invFunOn_mem hx
  have hζψ₀ : ∀ x ∈ Q, ζ (ψ₀ x) = x := fun x hx => Function.invFunOn_eq hx
  have hψ₀ζ : ∀ z ∈ N, ψ₀ (ζ z) = z := fun z hz => hζi.leftInvOn_invFunOn hz
  have hs0 : ∀ z ∈ N, deriv ζ z ≠ 0 := fun z hz h0 =>
    (hζ z hz).1 (by rw [← (hζ z hz).2.2, h0]; ring)
  set e : ℂ → ℂ := fun x => (deriv ζ (ψ₀ x))⁻¹ with he
  have hψ₀d : ∀ x ∈ Q, HasDerivAt ψ₀ (e x) x := by
    intro x hx
    have hc : ContinuousAt ψ₀ x :=
      (hψ₀conf.1.differentiableAt (hQo.mem_nhds hx)).continuousAt
    have hd : HasDerivAt ζ (deriv ζ (ψ₀ x)) (ψ₀ x) := (hζ _ (hψ₀N x hx)).2.1.hasDerivAt
    exact HasDerivAt.of_local_left_inverse hc hd (hs0 _ (hψ₀N x hx))
      (eventually_of_mem (hQo.mem_nhds hx) fun y hy => hζψ₀ y hy)
  have hgrad : ∀ z ∈ N, fx_grad u z = conj (deriv ζ z) := fun z hz =>
    (fx_fderiv_of_eq_re (eventually_of_mem (hNo.mem_nhds hz) hu) (hζ z hz).2.1.hasDerivAt).2
  -- the integrand in the natural parameter
  set h : ℂ → ℝ := fun x => ψ (ψ₀ x) * fderiv ℝ w (ψ₀ x) (e x) +
    w (ψ₀ x) * fderiv ℝ ψ (ψ₀ x) (e x) with hh
  set G : ℂ → ℝ := {x : ℂ | x.im ∈ E}.indicator h with hG
  have hFz : ∀ z ∈ N, R.indicator F z = ‖deriv ζ z‖ ^ 2 • G (ζ z) := by
    intro z hz
    have hconj := fx_conj_eq_smul_inv (hs0 z hz)
    have hFe : F z = ‖deriv ζ z‖ ^ 2 * h (ζ z) := by
      simp only [hF, hh, he, hψ₀ζ z hz, hgrad z hz, hconj, map_smul, smul_eq_mul]
      ring
    by_cases hzR : z ∈ R
    · have hE : (ζ z).im ∈ E := by
        have : z ∈ R ∩ N := ⟨hzR, hz⟩
        rw [hRN] at this
        exact this.2
      rw [indicator_of_mem hzR, hG, indicator_of_mem (show ζ z ∈ {x : ℂ | x.im ∈ E} from hE),
        smul_eq_mul, hFe]
    · have hE : (ζ z).im ∉ E := by
        intro hE
        have : z ∈ R ∩ N := by rw [hRN]; exact ⟨hz, hE⟩
        exact hzR this.1
      rw [indicator_of_notMem hzR, hG,
        indicator_of_notMem (show ζ z ∉ {x : ℂ | x.im ∈ E} from hE), smul_zero]
  have hF0 : ∀ z, z ∉ N → F z = 0 := by
    intro z hz
    have hzs : z ∉ tsupport ψ := fun h' => hz (hψN h')
    simp only [hF, image_eq_zero_of_notMem_tsupport hzs, fx_fderiv_eq_zero_of_notMem hzs,
      zero_apply, zero_mul, mul_zero, add_zero]
  -- change of variables into the square `Q`
  have hTQ : ∫ z in R, F z = ∫ x in Q, G x := by
    rw [ahP_integral_image hNo hζd hζi G,
      ← setIntegral_congr_fun hNo.measurableSet (fun z hz => hFz z hz),
      setIntegral_indicator hR]
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hR inter_subset_right
      fun z hz => ?_)
    exact hF0 z fun hzN => hz.2 ⟨hzN, hz.1⟩
  have hGint : IntegrableOn G Q := by
    rw [ahP_integrableOn_image hNo hζd hζi G]
    have h1 : IntegrableOn (R.indicator F) N :=
      ((integrable_indicator_iff hR).2 hint).integrableOn
    exact h1.congr_fun (fun z hz => hFz z hz) hNo.measurableSet
  -- `Q` is an open square
  have hQrect : Q = openRect (c0.re - δ) (c0.re + δ) (c0.im - δ) (c0.im + δ) := by
    rw [hQ]
    ext x
    simp only [mem_ofPred_eq, openRect, abs_lt]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  -- a square of radius `δ₂ < δ` containing `ζ(supp ψ)` well inside
  set m : ℂ → ℝ := fun x => max |x.re - c0.re| |x.im - c0.im| with hm
  have hmc : Continuous m :=
    ((continuous_re.sub continuous_const).abs).max ((continuous_im.sub continuous_const).abs)
  have hmQ : ∀ x ∈ Q, m x < δ := by
    intro x hx
    rw [hQ] at hx
    exact max_lt hx.1 hx.2
  have hK1 : IsCompact (ζ '' tsupport ψ) :=
    hψc.isCompact.image_of_continuousOn (hζd.continuousOn.mono hψN)
  obtain ⟨δ₁, hδ₁0, hδ₁δ, hδ₁⟩ : ∃ δ₁ : ℝ, 0 ≤ δ₁ ∧ δ₁ < δ ∧ ∀ x ∈ ζ '' tsupport ψ, m x ≤ δ₁ := by
    rcases (ζ '' tsupport ψ).eq_empty_or_nonempty with h0 | hne
    · exact ⟨0, le_rfl, hδ, by simp [h0]⟩
    obtain ⟨x₀, hx₀, hmax⟩ := hK1.exists_isMaxOn hne hmc.continuousOn
    refine ⟨m x₀, le_max_of_le_left (abs_nonneg _), hmQ x₀ (image_mono hψN hx₀),
      fun x hx => hmax hx⟩
  set δ₂ := (δ₁ + δ) / 2 with hδ₂
  have hδ₁₂ : δ₁ < δ₂ := by rw [hδ₂]; linarith
  have hδ₂δ : δ₂ < δ := by rw [hδ₂]; linarith
  set a := c0.re - δ₂ with ha
  set b := c0.re + δ₂ with hb
  set c₁ := c0.im - δ₂ with hc₁
  set d₁ := c0.im + δ₂ with hd₁
  have hab : a < b := by rw [ha, hb]; linarith
  have hcd : c₁ < d₁ := by rw [hc₁, hd₁]; linarith
  -- off `ζ(supp ψ)` the integrand vanishes
  have hsupp : ∀ x ∈ Q, δ₁ < m x → ψ (ψ₀ x) = 0 ∧ fderiv ℝ ψ (ψ₀ x) = 0 := by
    intro x hx hmx
    have hnot : ψ₀ x ∉ tsupport ψ := by
      intro hin
      have := hδ₁ (ζ (ψ₀ x)) (mem_image_of_mem ζ hin)
      rw [hζψ₀ x hx] at this
      linarith
    exact ⟨image_eq_zero_of_notMem_tsupport hnot, fx_fderiv_eq_zero_of_notMem hnot⟩
  have hh0 : ∀ x ∈ Q, δ₁ < m x → h x = 0 := by
    intro x hx hmx
    obtain ⟨h1, h2⟩ := hsupp x hx hmx
    simp only [hh, h1, h2, zero_apply, zero_mul, mul_zero, add_zero]
  have hmemQ : ∀ x y : ℝ, |x - c0.re| < δ → |y - c0.im| < δ → (x : ℂ) + (y : ℂ) * I ∈ Q := by
    intro x y hx hy
    rw [hQ]
    simp only [mem_ofPred_eq, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
      mul_one, sub_zero, add_im, mul_im, zero_add, add_zero]
    exact ⟨hx, hy⟩
  have hmval : ∀ x y : ℝ, m ((x : ℂ) + (y : ℂ) * I) = max |x - c0.re| |y - c0.im| := by
    intro x y
    simp [hm]
  -- `g ∘ ζ⁻¹` is quasiconformal on `Q`, hence A.C.L.
  have hψ₀K : IsKQC ψ₀ Q 1 := isKQC_one_of_conformal hQo hψ₀conf
  have hgψ₀K : IsKQC (g ∘ ψ₀) Q (1 * K) :=
    thm7_1_comp hψ₀K hgK (hψ₀conf.2.2.subset.trans hNΔ)
  have hRsub : closedRect a b c₁ d₁ ⊆ Q := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := hx
    rw [hQ]
    refine ⟨abs_lt.2 ⟨by linarith, by linarith⟩, abs_lt.2 ⟨by linarith, by linarith⟩⟩
  have hacl := ((thm9_1_isACL hgψ₀K).2 a b c₁ d₁ hab hcd hRsub).2
  -- the good points: `ψ` and `w` are differentiable at `ζ⁻¹(x)`
  set Bd : Set ℂ := {x | x ∈ Q ∧ ¬ (DifferentiableAt ℝ ψ (ψ₀ x) ∧
    DifferentiableAt ℝ w (ψ₀ x))} with hBd
  have hBd0 : volume Bd = 0 := by
    set BN : Set ℂ := {z | z ∈ N ∧ ¬ (DifferentiableAt ℝ ψ z ∧ DifferentiableAt ℝ w z)} with hBN
    have hBN0 : volume BN = 0 := by
      have h1 : (volume : Measure ℂ) {z : ℂ | ¬ DifferentiableAt ℝ ψ z} = 0 := by
        rw [← ae_iff]
        exact hψl.ae_differentiableAt
      have h2 : (volume : Measure ℂ) {z : ℂ | ¬ (z ∈ unitDisc → DifferentiableAt ℝ w z)} = 0 := by
        rw [← ae_iff]
        exact (ae_restrict_iff' measurableSet_ball).1 hwd
      refine measure_mono_null (fun z hz => ?_) (measure_union_null h1 h2)
      obtain ⟨hzN, hz⟩ := hz
      by_cases hψz : DifferentiableAt ℝ ψ z
      · exact Or.inr fun h' => hz ⟨hψz, h' (hNΔ hzN)⟩
      · exact Or.inl hψz
    have himg : volume (ζ '' BN) = 0 :=
      addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
        ((hζd.restrictScalars ℝ).mono fun z hz => hz.1) hBN0
    refine measure_mono_null (fun x hx => ?_) himg
    exact ⟨ψ₀ x, ⟨hψ₀N x hx.1, hx.2⟩, hζψ₀ x hx.1⟩
  set T0 := toMeasurable volume Bd with hT0
  have hT0m : MeasurableSet {z : ℂ | z ∉ T0} := (measurableSet_toMeasurable _ _).compl
  have hT0ae : ∀ᵐ z : ℂ, z ∉ T0 := by
    rw [ae_iff]
    simp only [not_not, ofPred_mem_eq]
    rw [measure_toMeasurable]
    exact hBd0
  have hgoodxy := abR_c_ae_ae_of_ae_symm hT0m hT0ae a b c₁ d₁
  -- for almost every plaque, the integral of `∂_ξ (ψ w)` vanishes
  have hline : ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo (c0.im - δ) (c0.im + δ))),
      ∫ x in Ioo (c0.re - δ) (c0.re + δ), G ((x : ℂ) + (y : ℂ) * I) = 0 := by
    have hgood : ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioo (c0.im - δ) (c0.im + δ))), y ∈ Ioo c₁ d₁ →
        AbsolutelyContinuousOnInterval (fun x : ℝ => (g ∘ ψ₀) ((x : ℂ) + (y : ℂ) * I)) a b ∧
        ∀ᵐ (x : ℝ) ∂(volume.restrict (Ioo a b)), (x : ℂ) + (y : ℂ) * I ∉ T0 :=
      ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).1 (hacl.and hgoodxy))
    filter_upwards [hgood, ae_restrict_mem measurableSet_Ioo] with y hy hyI
    by_cases hyE : y ∉ E
    · refine setIntegral_eq_zero_of_forall_eq_zero fun x _ => ?_
      rw [hG, indicator_of_notMem]
      simpa using hyE
    push Not at hyE
    have hGh : ∀ x : ℝ, G ((x : ℂ) + (y : ℂ) * I) = h ((x : ℂ) + (y : ℂ) * I) := fun x => by
      rw [hG, indicator_of_mem]
      simpa using hyE
    simp only [hGh]
    have hyδ : |y - c0.im| < δ := abs_lt.2 ⟨by linarith [hyI.1], by linarith [hyI.2]⟩
    by_cases hyc : y ∈ Ioo c₁ d₁
    swap
    · refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
      have hxδ : |x - c0.re| < δ := abs_lt.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
      refine hh0 _ (hmemQ x y hxδ hyδ) ?_
      rw [hmval]
      refine lt_max_of_lt_right ?_
      rw [lt_abs]
      simp only [mem_Ioo, not_and_or, not_lt] at hyc
      rcases hyc with h1 | h1
      · right; rw [hc₁] at h1; linarith
      · left; rw [hd₁] at h1; linarith
    obtain ⟨hAC, hgx⟩ := hy hyc
    set β : ℝ → ℝ := fun x => ψ (ψ₀ ((x : ℂ) + (y : ℂ) * I)) with hβ
    set W : ℝ → ℝ := fun x => w (ψ₀ ((x : ℂ) + (y : ℂ) * I)) with hW
    have hmemI : ∀ x ∈ uIcc a b, (x : ℂ) + (y : ℂ) * I ∈ Q := fun x hx => by
      rw [uIcc_of_le hab.le] at hx
      exact hmemQ x y (abs_lt.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩) hyδ
    -- the plaque is `C¹` in the natural parameter
    have hlineC : ContDiffOn ℝ 1 (fun x : ℝ => ψ₀ ((x : ℂ) + (y : ℂ) * I)) (uIcc a b) := by
      have h1 : ContDiffOn ℂ 1 ψ₀ Q := hψ₀conf.1.contDiffOn hQo
      have h2 : ContDiffOn ℝ 1 ψ₀ Q := h1.restrict_scalars ℝ
      have h3 : ContDiff ℝ 1 (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) :=
        ofRealCLM.contDiff.add contDiff_const
      exact h2.comp h3.contDiffOn (fun x hx => hmemI x hx)
    have hβAC : AbsolutelyContinuousOnInterval β a b :=
      hψl.comp_absolutelyContinuousOnInterval hlineC.absolutelyContinuousOnInterval
    have hWAC : AbsolutelyContinuousOnInterval W a b := by
      have h1 : AbsolutelyContinuousOnInterval
          (fun x : ℝ => u (g (ψ₀ ((x : ℂ) + (y : ℂ) * I)))) a b :=
        hul.comp_absolutelyContinuousOnInterval
          (fun x hx => hgm (hNΔ (hψ₀N _ (hmemI x hx)))) hAC
      have h2 : AbsolutelyContinuousOnInterval
          (fun x : ℝ => u (ψ₀ ((x : ℂ) + (y : ℂ) * I))) a b := by
        have hlin : AbsolutelyContinuousOnInterval (fun x : ℝ => x + c) a b :=
          (contDiff_id.add contDiff_const).contDiffOn.absolutelyContinuousOnInterval
        refine hlin.congr fun x hx => ?_
        have hp := hmemI x hx
        simp only [hu _ (hψ₀N _ hp), hζψ₀ _ hp, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
          mul_zero, mul_one, sub_zero, add_zero]
      exact h1.sub h2
    have hFTC := AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hβAC hWAC
    have hβa : β a = 0 := by
      refine (hsupp _ (hmemI a left_mem_uIcc) ?_).1
      rw [hmval]
      refine lt_max_of_lt_left ?_
      rw [ha, show c0.re - δ₂ - c0.re = -δ₂ by ring, abs_neg, abs_of_pos (by linarith)]
      exact hδ₁₂
    have hβb : β b = 0 := by
      refine (hsupp _ (hmemI b right_mem_uIcc) ?_).1
      rw [hmval]
      refine lt_max_of_lt_left ?_
      rw [hb, show c0.re + δ₂ - c0.re = δ₂ by ring, abs_of_pos (by linarith)]
      exact hδ₁₂
    have hderiv : ∀ x : ℝ, x ∈ Ioo a b → (x : ℂ) + (y : ℂ) * I ∉ T0 →
        deriv β x * W x + β x * deriv W x = h ((x : ℂ) + (y : ℂ) * I) := by
      intro x hx hxT
      have hpQ : (x : ℂ) + (y : ℂ) * I ∈ Q := hmemI x (by
        rw [uIcc_of_le hab.le]; exact Ioo_subset_Icc_self hx)
      have hgd : DifferentiableAt ℝ ψ (ψ₀ ((x : ℂ) + (y : ℂ) * I)) ∧
          DifferentiableAt ℝ w (ψ₀ ((x : ℂ) + (y : ℂ) * I)) := by
        by_contra hbad
        exact hxT (subset_toMeasurable _ _ ⟨hpQ, hbad⟩)
      have hl : HasDerivAt (fun t : ℝ => ψ₀ ((t : ℂ) + (y : ℂ) * I))
          (e ((x : ℂ) + (y : ℂ) * I)) x := by
        have h1 : HasDerivAt (fun q : ℂ => ψ₀ (q + (y : ℂ) * I)) (e ((x : ℂ) + (y : ℂ) * I))
            (x : ℂ) := by
          have := (hψ₀d _ hpQ).comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I))
          rw [mul_one] at this
          exact this
        exact h1.comp_ofReal
      have hdβ : HasDerivAt β (fderiv ℝ ψ (ψ₀ ((x : ℂ) + (y : ℂ) * I))
          (e ((x : ℂ) + (y : ℂ) * I))) x := by
        have := hgd.1.hasFDerivAt.comp_hasDerivAt x hl
        exact this
      have hdW : HasDerivAt W (fderiv ℝ w (ψ₀ ((x : ℂ) + (y : ℂ) * I))
          (e ((x : ℂ) + (y : ℂ) * I))) x := by
        have := hgd.2.hasFDerivAt.comp_hasDerivAt x hl
        exact this
      rw [hdβ.deriv, hdW.deriv]
      simp only [hh, hβ, hW]
      ring
    have hIoo : ∫ x in Ioo (c0.re - δ) (c0.re + δ), h ((x : ℂ) + (y : ℂ) * I) =
        ∫ x in Ioo a b, h ((x : ℂ) + (y : ℂ) * I) := by
      refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
        (Ioo_subset_Ioo (by rw [ha]; linarith) (by rw [hb]; linarith)) fun x hx => ?_
      have hxδ : |x - c0.re| < δ := abs_lt.2 ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
      refine hh0 _ (hmemQ x y hxδ hyδ) ?_
      rw [hmval]
      refine lt_max_of_lt_left ?_
      have hx2 := hx.2
      simp only [mem_Ioo, not_and_or, not_lt] at hx2
      rw [lt_abs]
      rcases hx2 with h1 | h1
      · right; rw [ha] at h1; linarith
      · left; rw [hb] at h1; linarith
    rw [hIoo, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab.le]
    have hzero : ∫ x in a..b, (deriv β x * W x + β x * deriv W x) = 0 := by
      rw [hFTC, hβa, hβb]
      ring
    rw [← hzero]
    refine intervalIntegral.integral_congr_ae ?_
    have hgx' : ∀ᵐ x : ℝ, x ∈ Ioo a b → (x : ℂ) + (y : ℂ) * I ∉ T0 :=
      (ae_restrict_iff' measurableSet_Ioo).1 hgx
    have hne : ∀ᵐ x : ℝ, x ∉ ({b} : Set ℝ) := (Set.countable_singleton b).ae_notMem volume
    filter_upwards [hgx', hne] with x hx1 hx2 hx3
    rw [uIoc_of_le hab.le] at hx3
    have hxIoo : x ∈ Ioo a b := ⟨hx3.1, lt_of_le_of_ne hx3.2 (fun h' => hx2 h')⟩
    exact (hderiv x hxIoo (hx1 hxIoo)).symm
  rw [hTQ, hQrect, fx_setIntegral_openRect_symm (hQrect ▸ hGint)]
  exact integral_eq_zero_of_ae hline

/-- The cut-off `η_n = clamp((n+1) dist(·, B) - 1)`: `0` within `1/(n+1)` of `B`, `1` beyond
`2/(n+1)`, `(n+1)`-Lipschitz. -/
def fx_cutoff (B : Set ℂ) (n : ℕ) (z : ℂ) : ℝ :=
  max 0 (min 1 (((n : ℝ) + 1) * infDist z B - 1))

/-- The cut-off is `(n+1)`-Lipschitz. -/
theorem fx_cutoff_lipschitz (B : Set ℂ) (n : ℕ) :
    LipschitzWith (⟨(n : ℝ) + 1, by positivity⟩ : ℝ≥0) (fx_cutoff B n) := by
  have h1 : LipschitzWith (⟨(n : ℝ) + 1, by positivity⟩ : ℝ≥0)
      (fun z => ((n : ℝ) + 1) * infDist z B - 1) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [Real.dist_eq]
    have := (lipschitz_infDist_pt (s := B)).dist_le_mul x y
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at this
    rw [show ((n : ℝ) + 1) * infDist x B - 1 - (((n : ℝ) + 1) * infDist y B - 1) =
      ((n : ℝ) + 1) * (infDist x B - infDist y B) by ring, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  exact (h1.const_min 1).const_max 0

/-- The cut-off takes values in `[0, 1]`. -/
theorem fx_cutoff_abs_le (B : Set ℂ) (n : ℕ) (z : ℂ) : |fx_cutoff B n z| ≤ 1 := by
  unfold fx_cutoff
  rw [abs_le]
  constructor
  · have : (0 : ℝ) ≤ max 0 (min 1 (((n : ℝ) + 1) * infDist z B - 1)) := le_max_left _ _
    linarith
  · exact max_le zero_le_one (min_le_left _ _)

/-- The cut-off vanishes within `1/(n+1)` of `B`. -/
theorem fx_cutoff_eq_zero {B : Set ℂ} {n : ℕ} {z : ℂ} (hz : infDist z B ≤ 1 / ((n : ℝ) + 1)) :
    fx_cutoff B n z = 0 := by
  unfold fx_cutoff
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have : ((n : ℝ) + 1) * infDist z B - 1 ≤ 0 := by
    have := mul_le_mul_of_nonneg_left hz hpos.le
    rw [mul_one_div_cancel hpos.ne'] at this
    linarith
  rw [min_eq_right (this.trans zero_le_one), max_eq_left this]

/-- The cut-off is `1` beyond `2/(n+1)` from `B`. -/
theorem fx_cutoff_eq_one {B : Set ℂ} {n : ℕ} {z : ℂ} (hz : 2 / ((n : ℝ) + 1) ≤ infDist z B) :
    fx_cutoff B n z = 1 := by
  unfold fx_cutoff
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have : 1 ≤ ((n : ℝ) + 1) * infDist z B - 1 := by
    have := mul_le_mul_of_nonneg_left hz hpos.le
    rw [mul_div_cancel₀ _ hpos.ne'] at this
    linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

/-- The topological support of the cut-off stays at distance `≥ 1/(n+1)` from `B`. -/
theorem fx_cutoff_tsupport (B : Set ℂ) (n : ℕ) :
    tsupport (fx_cutoff B n) ⊆ {z | 1 / ((n : ℝ) + 1) ≤ infDist z B} := by
  refine closure_minimal (fun z hz => ?_) (isClosed_le continuous_const
    (continuous_infDist_pt B))
  show 1 / ((n : ℝ) + 1) ≤ infDist z B
  by_contra hlt
  push Not at hlt
  exact hz (fx_cutoff_eq_zero hlt.le)

/-- The cut-off is locally constant (`= 1`) beyond `2/(n+1)`, so its derivative vanishes there. -/
theorem fx_cutoff_fderiv {B : Set ℂ} {n : ℕ} {z : ℂ} (hz : 2 / ((n : ℝ) + 1) < infDist z B) :
    fderiv ℝ (fx_cutoff B n) z = 0 := by
  have h : fx_cutoff B n =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
    have hopen : IsOpen {y : ℂ | 2 / ((n : ℝ) + 1) < infDist y B} :=
      isOpen_lt continuous_const (continuous_infDist_pt B)
    filter_upwards [hopen.mem_nhds hz] with y hy
    exact fx_cutoff_eq_one (le_of_lt hy)
  rw [h.fderiv_eq]
  exact fderiv_const_apply 1

/-- The cut-offs tend to `1` off `B`. -/
theorem fx_cutoff_tendsto {B : Set ℂ} {z : ℂ} (hz : 0 < infDist z B) :
    Tendsto (fun n => fx_cutoff B n z) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / infDist z B)
  filter_upwards [eventually_ge_atTop N] with n hn
  symm
  refine fx_cutoff_eq_one ?_
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  rw [div_lt_iff₀ hz] at hN
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- `vol(B(a, r)) = π r²`. -/
theorem fx_volume_ball (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball a r) = ENNReal.ofReal (π * r ^ 2) := by
  rw [Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr, mul_comm]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]

/-- `vol(B̄(a, r)) = π r²`. -/
theorem fx_volume_closedBall (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall a r) = ENNReal.ofReal (π * r ^ 2) := by
  rw [Complex.volume_closedBall, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr,
    mul_comm]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]

/-- The annulus `1 - t < |z| < 1` has area `≤ 2π t`. -/
theorem fx_volume_annulus_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    volume {z : ℂ | z ∈ unitDisc ∧ 1 - t < ‖z‖} ≤ ENNReal.ofReal (2 * π * t) := by
  have hsub : {z : ℂ | z ∈ unitDisc ∧ 1 - t < ‖z‖} ⊆ ball 0 1 \ closedBall 0 (1 - t) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    rw [mem_closedBall, dist_zero_right, not_le]
    exact hz.2
  have hcb : closedBall (0 : ℂ) (1 - t) ⊆ ball 0 1 := closedBall_subset_ball (by linarith)
  have hcbv := fx_volume_closedBall (0 : ℂ) (show 0 ≤ 1 - t by linarith)
  calc volume {z : ℂ | z ∈ unitDisc ∧ 1 - t < ‖z‖}
      ≤ volume (ball (0 : ℂ) 1 \ closedBall 0 (1 - t)) := measure_mono hsub
    _ = volume (ball (0 : ℂ) 1) - volume (closedBall (0 : ℂ) (1 - t)) :=
        measure_sdiff hcb measurableSet_closedBall.nullMeasurableSet
          (by rw [hcbv]; exact ENNReal.ofReal_ne_top)
    _ = ENNReal.ofReal (π * 1 ^ 2) - ENNReal.ofReal (π * (1 - t) ^ 2) := by
        rw [fx_volume_ball 0 zero_le_one, hcbv]
    _ = ENNReal.ofReal (π * 1 ^ 2 - π * (1 - t) ^ 2) :=
        (ENNReal.ofReal_sub _ (by positivity)).symm
    _ ≤ ENNReal.ofReal (2 * π * t) :=
        ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos, sq_nonneg t])

/-- **The cut-off error.**  Let `B = (ℂ ∖ Δ) ∪ Z` with `Z` finite, and `0 ≤ e ≤ E₀` on `Δ` with
`e → 0` uniformly at `∂Δ`.  If `|F n| ≤ (n+1) C e` on `R ⊆ Δ` and `F n = 0` where
`dist(·, B) > 2/(n+1)`, then `∫_R F n → 0` (the transition layers have area `O(1/n)` at `∂Δ`,
where `e` is small, and `O(1/n²)` at the zeros). -/
theorem fx_err_tendsto {R : Set ℂ} (hRm : MeasurableSet R) (hRΔ : R ⊆ unitDisc) {Z : Set ℂ} (hZ : Z.Finite)
    {e : ℂ → ℝ} {C E₀ : ℝ} (hC : 0 ≤ C) (he : ∀ z ∈ unitDisc, 0 ≤ e z ∧ e z ≤ E₀)
    (heb : ∀ ε > 0, ∃ δ > 0, ∀ z ∈ unitDisc, 1 - δ < ‖z‖ → e z < ε)
    {F : ℕ → ℂ → ℝ}
    (hFb : ∀ n : ℕ, ∀ z ∈ R, |F n z| ≤ ((n : ℝ) + 1) * C * e z)
    (hF0 : ∀ n : ℕ, ∀ z ∈ R, 2 / ((n : ℝ) + 1) < infDist z (unitDiscᶜ ∪ Z) → F n z = 0) :
    Tendsto (fun n => ∫ z in R, F n z) atTop (𝓝 0) := by
  set B : Set ℂ := unitDiscᶜ ∪ Z with hB
  have hBne : B.Nonempty := ⟨2, Or.inl (by simp [unitDisc])⟩
  have hE₀ : 0 ≤ E₀ := (he 0 (by simp [unitDisc])).1.trans (he 0 (by simp [unitDisc])).2
  set Zf := hZ.toFinset with hZf
  set k : ℝ := (Zf.card : ℝ) with hk
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  rw [Metric.tendsto_atTop]
  intro ε' hε'
  set ε := ε' / (2 * (6 * π * C + 1)) with hεdef
  have hden : 0 < 2 * (6 * π * C + 1) := by positivity
  have hε : 0 < ε := div_pos hε' hden
  have hεb : 6 * π * C * ε < ε' / 2 := by
    rw [hεdef, mul_div_assoc']
    rw [div_lt_div_iff₀ hden (by norm_num)]
    nlinarith [Real.pi_pos]
  obtain ⟨δ, hδ, hδb⟩ := heb ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max (3 / min δ 1) (2 * (9 * π * C * E₀ * k) / ε'))
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hmin : 0 < min δ 1 := lt_min hδ one_pos
  set t : ℝ := 3 / ((n : ℝ) + 1) with ht
  have ht0 : 0 < t := by positivity
  have htδ : t < min δ 1 := by
    rw [ht, div_lt_iff₀ hn1]
    have h1 := lt_of_le_of_lt (le_max_left _ _) hN
    rw [div_lt_iff₀ hmin] at h1
    nlinarith
  have ht1 : t ≤ 1 := (htδ.trans_le (min_le_right _ _)).le
  have htδ' : t < δ := htδ.trans_le (min_le_left _ _)
  have h2t : 2 / ((n : ℝ) + 1) < t := by
    rw [ht]; exact div_lt_div_of_pos_right (by norm_num) hn1
  set A : Set ℂ := {z : ℂ | z ∈ unitDisc ∧ 1 - t < ‖z‖} with hA
  set U : Set ℂ := ⋃ q ∈ Zf, ball q t with hU
  have hAm : MeasurableSet A :=
    measurableSet_ball.inter (measurableSet_lt measurable_const measurable_norm)
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion _ fun q _ => measurableSet_ball
  have hAv : volume A ≤ ENNReal.ofReal (2 * π * t) := fx_volume_annulus_le ht0 ht1
  have hUv : volume U ≤ ENNReal.ofReal (k * (π * t ^ 2)) := by
    calc volume U ≤ ∑ q ∈ Zf, volume (ball q t) := measure_biUnion_finset_le _ _
      _ = ∑ q ∈ Zf, ENNReal.ofReal (π * t ^ 2) :=
          Finset.sum_congr rfl fun q _ => fx_volume_ball q ht0.le
      _ = ENNReal.ofReal (k * (π * t ^ 2)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hk, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
  have hAfin : volume A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hAv
  have hUfin : volume U ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hUv
  set b : ℂ → ℝ := fun z => ((n : ℝ) + 1) * C * (ε * A.indicator 1 z + E₀ * U.indicator 1 z)
    with hbdef
  have hb0 : ∀ z, 0 ≤ b z := fun z => by
    have h1 : 0 ≤ A.indicator (1 : ℂ → ℝ) z := indicator_nonneg (fun _ _ => zero_le_one) z
    have h2 : 0 ≤ U.indicator (1 : ℂ → ℝ) z := indicator_nonneg (fun _ _ => zero_le_one) z
    positivity
  have hAi : Integrable (A.indicator (1 : ℂ → ℝ)) :=
    (integrable_indicator_iff hAm).2 (integrableOn_const hAfin)
  have hUi : Integrable (U.indicator (1 : ℂ → ℝ)) :=
    (integrable_indicator_iff hUm).2 (integrableOn_const hUfin)
  have hbi : Integrable b := ((hAi.const_mul ε).add (hUi.const_mul E₀)).const_mul _
  -- the pointwise bound on `R`
  have hpt : ∀ z ∈ R, ‖F n z‖ ≤ b z := by
    intro z hz
    rw [Real.norm_eq_abs]
    by_cases hfar : 2 / ((n : ℝ) + 1) < infDist z B
    · rw [hF0 n z hz hfar, abs_zero]; exact hb0 z
    push Not at hfar
    obtain ⟨y, hyB, hyz⟩ := (infDist_lt_iff hBne).1 (hfar.trans_lt h2t)
    have hzΔ := hRΔ hz
    obtain ⟨he0, heE⟩ := he z hzΔ
    have hA1 : 0 ≤ A.indicator (1 : ℂ → ℝ) z := indicator_nonneg (fun _ _ => zero_le_one) z
    have hU1 : 0 ≤ U.indicator (1 : ℂ → ℝ) z := indicator_nonneg (fun _ _ => zero_le_one) z
    have hnC : 0 ≤ ((n : ℝ) + 1) * C := by positivity
    rcases hyB with hyΔ | hyZ
    · -- near the circle: `e < ε`
      have hy1 : 1 ≤ ‖y‖ := by simpa [unitDisc] using hyΔ
      have hzA : z ∈ A := by
        refine ⟨hzΔ, ?_⟩
        have := norm_sub_norm_le y z
        rw [← dist_eq_norm, dist_comm] at this
        linarith
      have hez : e z < ε := hδb z hzΔ (by linarith [hzA.2])
      calc |F n z| ≤ ((n : ℝ) + 1) * C * e z := hFb n z hz
        _ ≤ ((n : ℝ) + 1) * C * ε := mul_le_mul_of_nonneg_left hez.le hnC
        _ ≤ b z := by
            simp only [hbdef, indicator_of_mem hzA, Pi.one_apply, mul_one]
            exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hE₀ hU1)) hnC
    · -- near a zero
      have hzU : z ∈ U := by
        rw [hU, mem_iUnion₂]
        exact ⟨y, (Set.Finite.mem_toFinset hZ).2 hyZ, hyz⟩
      calc |F n z| ≤ ((n : ℝ) + 1) * C * e z := hFb n z hz
        _ ≤ ((n : ℝ) + 1) * C * E₀ := mul_le_mul_of_nonneg_left heE hnC
        _ ≤ b z := by
            simp only [hbdef, indicator_of_mem hzU, Pi.one_apply, mul_one]
            exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (mul_nonneg hε.le hA1)) hnC
  have hint : ∫ z, b z = ((n : ℝ) + 1) * C * (ε * volume.real A + E₀ * volume.real U) := by
    simp only [hbdef]
    rw [integral_const_mul, integral_add (hAi.const_mul ε) (hUi.const_mul E₀),
      integral_const_mul, integral_const_mul, integral_indicator_one hAm,
      integral_indicator_one hUm]
  have hAr : volume.real A ≤ 2 * π * t := by
    rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal (by positivity) hAv
  have hUr : volume.real U ≤ k * (π * t ^ 2) := by
    rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal (by positivity) hUv
  have hmain : ‖∫ z in R, F n z‖ ≤ 6 * π * C * ε + 9 * π * C * E₀ * k / ((n : ℝ) + 1) := by
    calc ‖∫ z in R, F n z‖ ≤ ∫ z in R, b z :=
          norm_integral_le_of_norm_le hbi.integrableOn
            ((ae_restrict_iff' hRm).2 (Eventually.of_forall hpt))
      _ ≤ ∫ z, b z := setIntegral_le_integral hbi (Eventually.of_forall hb0)
      _ = ((n : ℝ) + 1) * C * (ε * volume.real A + E₀ * volume.real U) := hint
      _ ≤ ((n : ℝ) + 1) * C * (ε * (2 * π * t) + E₀ * (k * (π * t ^ 2))) := by
          gcongr
      _ = 6 * π * C * ε + 9 * π * C * E₀ * k / ((n : ℝ) + 1) := by
          rw [ht]
          field_simp
          ring
  have hsecond : 9 * π * C * E₀ * k / ((n : ℝ) + 1) < ε' / 2 := by
    rw [div_lt_iff₀ hn1]
    have h1 := lt_of_le_of_lt (le_max_right _ _) hN
    rw [div_lt_iff₀ hε'] at h1
    nlinarith [Real.pi_pos, mul_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hC) hE₀) hk0]
  rw [dist_zero_right]
  linarith

/-- At a point of a calibrated set: `∇u = conj s` with `s² = φ`, `u` is differentiable and
`u'(z)(h) = Re (s h)`. -/
theorem fx_calib_at {φ : ℂ → ℂ} {R : Set ℂ} {u : ℂ → ℝ} (hcal : fx_IsCalib φ R u) {z : ℂ}
    (hz : z ∈ R) :
    ∃ s : ℂ, s ^ 2 = φ z ∧ DifferentiableAt ℝ u z ∧ (∀ h : ℂ, fderiv ℝ u z h = (s * h).re) ∧
      fx_grad u z = conj s := by
  obtain ⟨ζ, N, hzN, hN, hcase⟩ := hcal.box z (hcal.sub hz) (hcal.reg z hz)
  rcases hcase with h0 | ⟨-, c, hc⟩
  · have : z ∈ R ∩ N := ⟨hz, hzN⟩
    rw [h0] at this
    exact absurd this (notMem_empty z)
  obtain ⟨hNo, -, -, hζ, -⟩ := hN
  have hev : ∀ᶠ y in 𝓝 z, u y = (ζ y).re + c := eventually_of_mem (hNo.mem_nhds hzN) hc
  obtain ⟨h1, h2⟩ := fx_fderiv_of_eq_re hev (hζ z hzN).2.1.hasDerivAt
  have hdiff : DifferentiableAt ℝ u z := by
    have h3 : DifferentiableAt ℝ (fun y => (ζ y).re + c) z :=
      (Complex.reCLM.differentiableAt.comp z ((hζ z hzN).2.1.restrictScalars ℝ)).add_const c
    exact h3.congr_of_eventuallyEq hev
  exact ⟨deriv ζ z, (hζ z hzN).2.2, hdiff, h1, h2⟩

/-- On a calibrated set `|∇u| = |φ|^{1/2} ≤ M^{1/2}` and `⟨∇u, ∇u⟩ = |φ|`. -/
theorem fx_calib_grad {φ : ℂ → ℂ} {R : Set ℂ} {u : ℂ → ℝ} (hcal : fx_IsCalib φ R u) {z : ℂ}
    (hz : z ∈ R) :
    ‖fx_grad u z‖ = Real.sqrt ‖φ z‖ ∧ fderiv ℝ u z (fx_grad u z) = ‖φ z‖ := by
  obtain ⟨s, hs, -, hfd, hgr⟩ := fx_calib_at hcal hz
  have hns : ‖s‖ ^ 2 = ‖φ z‖ := by rw [← hs, norm_pow]
  refine ⟨?_, ?_⟩
  · rw [hgr, Complex.norm_conj, ← hns, Real.sqrt_sq (norm_nonneg _)]
  · rw [hgr, hfd, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, hns]

/-- The `L¹` bound `|∂g| + |∂̄g| ∈ L¹(Δ)` for a q.c. self-map of `Δ` (from `(|∂g| + |∂̄g|)² ≤ K J_g`
and `∬ J_g ≤ |g(Δ)|`). -/
theorem fx_integrable_dz_add {g : ℂ → ℂ} {K : ℝ} (hgK : IsKQC g unitDisc K)
    (hgs : g '' unitDisc = unitDisc) :
    IntegrableOn (fun z => ‖dz g z‖ + ‖dzbar g z‖) unitDisc := by
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  have hK0 : 0 ≤ K := zero_le_one.trans hgK.2.1
  have hgm : Measurable fun z => ‖dz g z‖ + ‖dzbar g z‖ :=
    (measurable_dz g).norm.add (measurable_dzbar g).norm
  have hsq : ∀ᵐ z ∂(volume.restrict unitDisc),
      ‖dz g z‖ + ‖dzbar g z‖ ≤ 1 + K * jacobian g z ∧ 0 ≤ K * jacobian g z := by
    filter_upwards [thm9_4_dilatation_ae hgK] with z hz
    have h0 : 0 ≤ ‖dz g z‖ + ‖dzbar g z‖ := by positivity
    have hKJ : (‖dz g z‖ + ‖dzbar g z‖) ^ 2 ≤ K * jacobian g z := by
      unfold jacobian
      nlinarith
    constructor
    · nlinarith [sq_nonneg (‖dz g z‖ + ‖dzbar g z‖ - 1)]
    · nlinarith
  have hJ : ∫⁻ z in unitDisc, ENNReal.ofReal (jacobian g z) ≤ volume (g '' unitDisc) :=
    lintegral_jacobian_le_volume_image hgK hΔ subset_rfl
  have hΔfin : volume unitDisc < ⊤ := measure_ball_lt_top
  refine ⟨hgm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z => by positivity)]
  calc ∫⁻ z in unitDisc, ENNReal.ofReal (‖dz g z‖ + ‖dzbar g z‖)
      ≤ ∫⁻ z in unitDisc, (1 + ENNReal.ofReal K * ENNReal.ofReal (jacobian g z)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hsq] with z hz
        calc ENNReal.ofReal (‖dz g z‖ + ‖dzbar g z‖)
            ≤ ENNReal.ofReal (1 + K * jacobian g z) := ENNReal.ofReal_le_ofReal hz.1
          _ = 1 + ENNReal.ofReal (K * jacobian g z) := by
              rw [ENNReal.ofReal_add zero_le_one hz.2, ENNReal.ofReal_one]
          _ ≤ 1 + ENNReal.ofReal K * ENNReal.ofReal (jacobian g z) := by
              gcongr
              rw [← ENNReal.ofReal_mul hK0]
    _ = volume unitDisc + ENNReal.ofReal K * ∫⁻ z in unitDisc, ENNReal.ofReal (jacobian g z) := by
        rw [lintegral_add_left measurable_const, setLIntegral_const, one_mul,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := by
        refine ENNReal.add_lt_top.2 ⟨hΔfin, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_⟩
        rw [hgs] at hJ
        exact hJ.trans_lt hΔfin

/-- The flux integrand `⟨∇u, ∇w⟩` is integrable on a calibrated set when `|∇w| ∈ L¹(Δ)`. -/
theorem fx_flux_integrable {φ : ℂ → ℂ} {R : Set ℂ} {u w : ℂ → ℝ} (hcal : fx_IsCalib φ R u)
    {M : ℝ} (hM : ∀ z ∈ unitDisc, ‖φ z‖ ≤ M)
    (hwint : IntegrableOn (fun z => ‖fderiv ℝ w z‖) unitDisc) :
    IntegrableOn (fun z => fderiv ℝ w z (fx_grad u z)) R := by
  have hVm : Measurable (fx_grad u) :=
    (Complex.measurable_ofReal.comp (measurable_fderiv_apply_const ℝ u 1)).add
      (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_fderiv_apply_const ℝ u I)))
  have hCwm : AEStronglyMeasurable (fun z => fderiv ℝ w z (fx_grad u z)) (volume.restrict R) := by
    have e : (fun z => fderiv ℝ w z (fx_grad u z)) =
        fun z => (fx_grad u z).re * fderiv ℝ w z 1 + (fx_grad u z).im * fderiv ℝ w z I :=
      funext fun z => fx_clm_apply _ _
    rw [e]
    exact ((hVm.re.mul (measurable_fderiv_apply_const ℝ w 1)).add
      (hVm.im.mul (measurable_fderiv_apply_const ℝ w I))).aestronglyMeasurable
  refine Integrable.mono' ((hwint.mono_set hcal.sub).mul_const (Real.sqrt M)) hCwm ?_
  refine (ae_restrict_iff' hcal.meas).2 (Eventually.of_forall fun z hz => ?_)
  calc ‖fderiv ℝ w z (fx_grad u z)‖ ≤ ‖fderiv ℝ w z‖ * ‖fx_grad u z‖ :=
        (fderiv ℝ w z).le_opNorm _
    _ ≤ ‖fderiv ℝ w z‖ * Real.sqrt M := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [(fx_calib_grad hcal hz).1]
        exact Real.sqrt_le_sqrt (hM z (hcal.sub hz))

/-- **The flux identity** `∬_R ⟨∇u, ∇w⟩ = 0`, `w = u ∘ g - u`: the cut-offs `η_n` (vanishing near the
zeros and near `∂Δ`) are split along finitely many flow boxes (`fx_partition`), where the local
identity `fx_flux_local` holds; the cut-off error tends to `0` (`fx_err_tendsto`, `w → 0` at `∂Δ`). -/
theorem fx_flux_identity {g φ : ℂ → ℂ} {K : ℝ} (hg : fx_IsGoodSelfMap g K) {ρ : ℝ} (hρ : 1 < ρ)
    (hφ : DifferentiableOn ℂ φ (ball 0 ρ)) {R : Set ℂ} {u : ℂ → ℝ} (hcal : fx_IsCalib φ R u)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {M : ℝ} (hM : ∀ z ∈ unitDisc, ‖φ z‖ ≤ M)
    (hwd : ∀ᵐ z ∂(volume.restrict unitDisc), DifferentiableAt ℝ (fun y => u (g y) - u y) z)
    (hwint : IntegrableOn (fun z => ‖fderiv ℝ (fun y => u (g y) - u y) z‖) unitDisc) :
    ∫ z in R, fderiv ℝ (fun y => u (g y) - u y) z (fx_grad u z) = 0 := by
  classical
  obtain ⟨hgK, hgs, hgb⟩ := hg
  have hgm : MapsTo g unitDisc unitDisc := fun z hz => hgs ▸ mem_image_of_mem g hz
  have hR : MeasurableSet R := hcal.meas
  have hRΔ : R ⊆ unitDisc := hcal.sub
  have hRfin : volume R ≠ ⊤ := ((measure_mono hRΔ).trans_lt measure_ball_lt_top).ne
  obtain ⟨L, hL⟩ := hcal.lip
  set w : ℂ → ℝ := fun y => u (g y) - u y with hw
  set V : ℂ → ℂ := fx_grad u with hV
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp [unitDisc]))
  have hVb : ∀ z ∈ R, ‖V z‖ ≤ Real.sqrt M := fun z hz => by
    rw [hV, (fx_calib_grad hcal hz).1]
    exact Real.sqrt_le_sqrt (hM z (hRΔ hz))
  have hwb : ∀ z ∈ unitDisc, |w z| ≤ L * ‖g z - z‖ := by
    intro z hz
    have := hL.dist_le_mul (g z) (hgm hz) z hz
    rwa [Real.dist_eq, dist_eq_norm] at this
  have hgz2 : ∀ z ∈ unitDisc, ‖g z - z‖ ≤ 2 := by
    intro z hz
    have h1 : ‖g z‖ < 1 := by simpa [unitDisc] using hgm hz
    have h2 : ‖z‖ < 1 := by simpa [unitDisc] using hz
    linarith [norm_sub_le (g z) z]
  have hVm : Measurable V :=
    (Complex.measurable_ofReal.comp (measurable_fderiv_apply_const ℝ u 1)).add
      (measurable_const.mul (Complex.measurable_ofReal.comp (measurable_fderiv_apply_const ℝ u I)))
  have hwc : ContinuousOn w unitDisc :=
    (hL.continuousOn.comp hgK.2.2.1.1 hgm).sub hL.continuousOn
  have hwm : AEStronglyMeasurable w (volume.restrict R) := (hwc.mono hRΔ).aestronglyMeasurable hR
  have hCwm : AEStronglyMeasurable (fun z => fderiv ℝ w z (V z)) (volume.restrict R) := by
    have e : (fun z => fderiv ℝ w z (V z)) =
        fun z => (V z).re * fderiv ℝ w z 1 + (V z).im * fderiv ℝ w z I :=
      funext fun z => fx_clm_apply _ _
    rw [e]
    exact ((hVm.re.mul (measurable_fderiv_apply_const ℝ w 1)).add
      (hVm.im.mul (measurable_fderiv_apply_const ℝ w I))).aestronglyMeasurable
  have hCwint : IntegrableOn (fun z => fderiv ℝ w z (V z)) R := fx_flux_integrable hcal hM hwint
  -- the flux functional
  have hT1 : ∀ ψ : ℂ → ℝ, (∃ C, LipschitzWith C ψ) → HasCompactSupport ψ →
      IntegrableOn (fun z => ψ z * fderiv ℝ w z (V z)) R := by
    rintro ψ ⟨C, hψl⟩ hψc
    obtain ⟨Mψ, hMψ⟩ := fx_bound_of_lipschitz hψl hψc
    refine Integrable.mono' (hCwint.norm.const_mul Mψ)
      (hψl.continuous.aestronglyMeasurable.mul hCwm) (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hMψ z) (abs_nonneg _)
  have hT2 : ∀ ψ : ℂ → ℝ, (∃ C, LipschitzWith C ψ) →
      IntegrableOn (fun z => w z * fderiv ℝ ψ z (V z)) R := by
    rintro ψ ⟨C, hψl⟩
    have hDm : AEStronglyMeasurable (fun z => fderiv ℝ ψ z (V z)) (volume.restrict R) := by
      have e : (fun z => fderiv ℝ ψ z (V z)) =
          fun z => (V z).re * fderiv ℝ ψ z 1 + (V z).im * fderiv ℝ ψ z I :=
        funext fun z => fx_clm_apply _ _
      rw [e]
      exact ((hVm.re.mul (measurable_fderiv_apply_const ℝ ψ 1)).add
        (hVm.im.mul (measurable_fderiv_apply_const ℝ ψ I))).aestronglyMeasurable
    refine Integrable.mono' (integrableOn_const (C := (L : ℝ) * 2 * (C * Real.sqrt M)) hRfin)
      (hwm.mul hDm) ((ae_restrict_iff' hR).2 (Eventually.of_forall fun z hz => ?_))
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |w z| ≤ L * 2 :=
      (hwb z (hRΔ hz)).trans (mul_le_mul_of_nonneg_left (hgz2 z (hRΔ hz)) L.2)
    have h2 : |fderiv ℝ ψ z (V z)| ≤ C * Real.sqrt M := by
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ ψ z (V z)‖ ≤ ‖fderiv ℝ ψ z‖ * ‖V z‖ := (fderiv ℝ ψ z).le_opNorm _
        _ ≤ C * Real.sqrt M :=
            mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hψl) (hVb z hz) (norm_nonneg _) C.2
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  set T : (ℂ → ℝ) → ℝ := fun ψ => ∫ z in R, (ψ z * fderiv ℝ w z (V z) +
    w z * fderiv ℝ ψ z (V z)) with hT
  have hadd : ∀ ψ₁ ψ₂ : ℂ → ℝ, (∃ C, LipschitzWith C ψ₁) → HasCompactSupport ψ₁ →
      (∃ C, LipschitzWith C ψ₂) → HasCompactSupport ψ₂ → T (ψ₁ + ψ₂) = T ψ₁ + T ψ₂ := by
    rintro ψ₁ ψ₂ ⟨C1, hl1⟩ hc1 ⟨C2, hl2⟩ hc2
    simp only [hT]
    have hi1 : IntegrableOn (fun z => ψ₁ z * fderiv ℝ w z (V z) + w z * fderiv ℝ ψ₁ z (V z)) R :=
      (hT1 ψ₁ ⟨C1, hl1⟩ hc1).add (hT2 ψ₁ ⟨C1, hl1⟩)
    have hi2 : IntegrableOn (fun z => ψ₂ z * fderiv ℝ w z (V z) + w z * fderiv ℝ ψ₂ z (V z)) R :=
      (hT1 ψ₂ ⟨C2, hl2⟩ hc2).add (hT2 ψ₂ ⟨C2, hl2⟩)
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae hl1.ae_differentiableAt,
      ae_restrict_of_ae hl2.ae_differentiableAt] with z hz1 hz2
    have hfd : fderiv ℝ (ψ₁ + ψ₂) z = fderiv ℝ ψ₁ z + fderiv ℝ ψ₂ z := fderiv_add hz1 hz2
    simp only [Pi.add_apply, hfd, add_apply]
    ring
  -- vanishing on functions supported in a flow box
  have hbox : ∀ p : ℂ, ∃ N : Set ℂ, p ∈ unitDisc → φ p ≠ 0 → p ∈ N ∧ IsOpen N ∧
      ∀ ψ : ℂ → ℝ, (∃ C, LipschitzWith C ψ) → HasCompactSupport ψ → tsupport ψ ⊆ N →
        T ψ = 0 := by
    intro p
    by_cases hp : p ∈ unitDisc ∧ φ p ≠ 0
    · obtain ⟨ζ, N, hpN, hN, hcase⟩ := hcal.box p hp.1 hp.2
      refine ⟨N, fun _ _ => ⟨hpN, hN.1, ?_⟩⟩
      rintro ψ ⟨C, hψl⟩ hψc hψN
      rcases hcase with h0 | ⟨⟨E, hE⟩, c, hc⟩
      · simp only [hT]
        refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
        have hzN : z ∉ N := fun h' => by
          have : z ∈ R ∩ N := ⟨hz, h'⟩
          rw [h0] at this
          exact this
        have hzs : z ∉ tsupport ψ := fun h' => hzN (hψN h')
        simp [image_eq_zero_of_notMem_tsupport hzs, fx_fderiv_eq_zero_of_notMem hzs]
      · exact fx_flux_local hN hE hc hR hgK hgm hL hψl hψc hψN hwd
          ((hT1 ψ ⟨C, hψl⟩ hψc).add (hT2 ψ ⟨C, hψl⟩))
    · exact ⟨univ, fun h1 h2 => absurd ⟨h1, h2⟩ hp⟩
  choose Nf hNf using hbox
  -- the cut-offs
  have hZ := fx_zeros_finite hρ hφ hne
  set Z : Set ℂ := {q : ℂ | q ∈ unitDisc ∧ φ q = 0} with hZdef
  set B : Set ℂ := unitDiscᶜ ∪ Z with hB
  have hBne : B.Nonempty := ⟨2, Or.inl (by simp [unitDisc])⟩
  have hBc : IsClosed B := isOpen_ball.isClosed_compl.union hZ.isClosed
  have hBR : ∀ z ∈ R, 0 < infDist z B := by
    intro z hz
    have hzB : z ∉ B := by
      rintro (h | h)
      · exact h (hRΔ hz)
      · exact hcal.reg z hz h.2
    exact (hBc.notMem_iff_infDist_pos hBne).1 hzB
  have hηc : ∀ n, HasCompactSupport (fx_cutoff B n) := by
    intro n
    have hK : IsCompact {z : ℂ | 1 / ((n : ℝ) + 1) ≤ infDist z B} := by
      refine Metric.isCompact_of_isClosed_isBounded
        (isClosed_le continuous_const (continuous_infDist_pt B)) ?_
      refine (isBounded_ball (x := (0 : ℂ)) (r := 1)).subset fun z hz => ?_
      by_contra hzΔ
      have h0 : infDist z B = 0 := infDist_zero_of_mem (Or.inl hzΔ)
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      rw [mem_ofPred_eq, h0] at hz
      linarith
    exact hK.of_isClosed_subset (isClosed_tsupport _) (fx_cutoff_tsupport B n)
  have hηT : ∀ n, T (fx_cutoff B n) = 0 := by
    intro n
    set Kn := {z : ℂ | 1 / ((n : ℝ) + 1) ≤ infDist z B} with hKn
    have hKreg : ∀ z ∈ Kn, z ∈ unitDisc ∧ φ z ≠ 0 := by
      intro z hz
      have hpos : 0 < infDist z B := lt_of_lt_of_le (by positivity) hz
      have hzB : z ∉ B := fun h' => by
        rw [infDist_zero_of_mem h'] at hpos
        exact lt_irrefl 0 hpos
      have hzΔ : z ∈ unitDisc := by
        by_contra h
        exact hzB (Or.inl h)
      exact ⟨hzΔ, fun h => hzB (Or.inr ⟨hzΔ, h⟩)⟩
    have hKc : IsCompact Kn := by
      refine Metric.isCompact_of_isClosed_isBounded
        (isClosed_le continuous_const (continuous_infDist_pt B)) ?_
      exact (isBounded_ball (x := (0 : ℂ)) (r := 1)).subset fun z hz => (hKreg z hz).1
    obtain ⟨t, htK, hcov⟩ := hKc.elim_nhds_subcover Nf fun p hp =>
      (hNf p (hKreg p hp).1 (hKreg p hp).2).2.1.mem_nhds (hNf p (hKreg p hp).1 (hKreg p hp).2).1
    refine fx_partition T hadd (t.image Nf) ?_ (fx_cutoff B n) ⟨_, fx_cutoff_lipschitz B n⟩
      (hηc n) ?_
    · intro N hN
      obtain ⟨p, hpt, rfl⟩ := Finset.mem_image.1 hN
      have hp := hKreg p (htK p hpt)
      exact ⟨(hNf p hp.1 hp.2).2.1, (hNf p hp.1 hp.2).2.2⟩
    · intro z hz
      have h1 := hcov (fx_cutoff_tsupport B n hz)
      rw [mem_iUnion₂] at h1 ⊢
      obtain ⟨p, hpt, hzp⟩ := h1
      exact ⟨Nf p, Finset.mem_image_of_mem Nf hpt, hzp⟩
  -- splitting `T η_n = 0`
  have hsplit : ∀ n, ∫ z in R, fx_cutoff B n z * fderiv ℝ w z (V z) =
      -∫ z in R, w z * fderiv ℝ (fx_cutoff B n) z (V z) := by
    intro n
    have h0 := hηT n
    simp only [hT] at h0
    rw [integral_add (hT1 _ ⟨_, fx_cutoff_lipschitz B n⟩ (hηc n))
      (hT2 _ ⟨_, fx_cutoff_lipschitz B n⟩)] at h0
    linarith
  have hlim1 : Tendsto (fun n => ∫ z in R, fx_cutoff B n z * fderiv ℝ w z (V z)) atTop
      (𝓝 (∫ z in R, fderiv ℝ w z (V z))) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖fderiv ℝ w z (V z)‖)
      (fun n => (fx_cutoff_lipschitz B n).continuous.aestronglyMeasurable.mul hCwm)
      hCwint.norm (fun n => Eventually.of_forall fun z => ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (fx_cutoff_abs_le B n z)
    · refine (ae_restrict_iff' hR).2 (Eventually.of_forall fun z hz => ?_)
      have := (fx_cutoff_tendsto (hBR z hz)).mul_const (fderiv ℝ w z (V z))
      rwa [one_mul] at this
  have hlim2 : Tendsto (fun n => ∫ z in R, w z * fderiv ℝ (fx_cutoff B n) z (V z)) atTop
      (𝓝 0) := by
    refine fx_err_tendsto (e := fun z => L * ‖g z - z‖) (C := Real.sqrt M) (E₀ := L * 2) hR
      hRΔ hZ (Real.sqrt_nonneg _) (fun z hz => ⟨by positivity,
        mul_le_mul_of_nonneg_left (hgz2 z hz) L.2⟩) ?_ ?_ ?_
    · intro ε hε
      obtain ⟨δ, hδ, hδb⟩ := hgb (ε / ((L : ℝ) + 1)) (by positivity)
      refine ⟨δ, hδ, fun z hz hzn => ?_⟩
      have h1 := hδb z hz hzn
      have hL1 : (0 : ℝ) < (L : ℝ) + 1 := by positivity
      calc (L : ℝ) * ‖g z - z‖ ≤ L * (ε / ((L : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left h1.le L.2
        _ < ε := by
            rw [mul_div_assoc', div_lt_iff₀ hL1]
            nlinarith
    · intro n z hz
      rw [abs_mul]
      have h2 : |fderiv ℝ (fx_cutoff B n) z (V z)| ≤ ((n : ℝ) + 1) * Real.sqrt M := by
        rw [← Real.norm_eq_abs]
        calc ‖fderiv ℝ (fx_cutoff B n) z (V z)‖ ≤ ‖fderiv ℝ (fx_cutoff B n) z‖ * ‖V z‖ :=
              (fderiv ℝ (fx_cutoff B n) z).le_opNorm _
          _ ≤ ((n : ℝ) + 1) * Real.sqrt M :=
              mul_le_mul (norm_fderiv_le_of_lipschitz ℝ (fx_cutoff_lipschitz B n)) (hVb z hz)
                (norm_nonneg _) (by positivity)
      calc |w z| * |fderiv ℝ (fx_cutoff B n) z (V z)|
          ≤ (L * ‖g z - z‖) * (((n : ℝ) + 1) * Real.sqrt M) :=
            mul_le_mul (hwb z (hRΔ hz)) h2 (abs_nonneg _) (by positivity)
        _ = ((n : ℝ) + 1) * Real.sqrt M * (L * ‖g z - z‖) := by ring
    · intro n z _ hfar
      rw [fx_cutoff_fderiv hfar, zero_apply, mul_zero]
  have hlim3 : Tendsto (fun n => ∫ z in R, fx_cutoff B n z * fderiv ℝ w z (V z)) atTop
      (𝓝 0) := by
    have := hlim2.neg
    rw [neg_zero] at this
    exact this.congr fun n => (hsplit n).symm
  exact tendsto_nhds_unique hlim1 hlim3

/-- **The map `g = f⁻¹ ∘ f₀` of (35.5) is a good self-map** (`thm7_1_comp`, `thm7_2_inv`;
`F⁻¹ ∘ F₀` is uniformly continuous on the closed disc and the identity on `∂Δ`). -/
theorem fx_isGoodSelfMap_of_boundary {f f₀ : ℂ → ℂ} (hf : IsQuasiconformal f unitDisc)
    (hf₀ : IsQuasiconformal f₀ unitDisc) (hfs : f '' unitDisc = unitDisc)
    (hf₀s : f₀ '' unitDisc = unitDisc) {F F₀ : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f unitDisc unitDisc F) (hF₀ : IsHomeoExtension f₀ unitDisc unitDisc F₀)
    (hbd : ∀ ζ : ℂ, ‖ζ‖ = 1 → F ζ = F₀ ζ) :
    ∃ K : ℝ, fx_IsGoodSelfMap (Function.invFunOn f unitDisc ∘ f₀) K := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨K₀, hK₀⟩ := hf₀
  set a := Function.invFunOn f unitDisc with hadef
  have haK : IsKQC a unitDisc K := by
    have h := thm7_2_inv hK
    rwa [hfs] at h
  have hfi : InjOn f unitDisc := hK.2.2.1.2.1
  have hgK : IsKQC (a ∘ f₀) unitDisc (K₀ * K) := thm7_1_comp hK₀ haK hf₀s.subset
  have hgimg : (a ∘ f₀) '' unitDisc = unitDisc := by
    rw [image_comp, hf₀s]
    conv_lhs => rw [← hfs]
    exact hfi.leftInvOn_invFunOn.image_image
  refine ⟨K₀ * K, hgK, hgimg, ?_⟩
  obtain ⟨hF1, hF2, hF3, hF4⟩ := hF
  obtain ⟨hG1, hG2, -, hG4⟩ := hF₀
  set C := closure (toExt unitDisc) with hC
  set H : ExtPlane → ExtPlane := Function.invFunOn F C ∘ F₀ with hH
  have hinvc : ContinuousOn (Function.invFunOn F C) C := by
    have h := continuousOn_invFunOn_of_isClosed isClosed_closure hF2 hF3
    rwa [hF4] at h
  have hHc : ContinuousOn H C :=
    hinvc.comp hG2 (fun p hp => hG4 ▸ mem_image_of_mem F₀ hp)
  refine fx_boundary_uniform hHc (fun z hz => ?_) (fun ζ hζ => ?_)
  · have hw : f₀ z ∈ f '' unitDisc := by rw [hfs, ← hf₀s]; exact mem_image_of_mem f₀ hz
    obtain ⟨y, hy, hyz⟩ := hw
    have hyC : ((y : ℂ) : ExtPlane) ∈ C := subset_closure (mem_image_of_mem _ hy)
    show Function.invFunOn F C (F₀ (z : ExtPlane)) = ((a (f₀ z) : ℂ) : ExtPlane)
    rw [hG1 z hz, ← hyz, ← hF1 y hy, hF3.leftInvOn_invFunOn hyC, hadef,
      hfi.leftInvOn_invFunOn hy]
  · have hζC : ((ζ : ℂ) : ExtPlane) ∈ C := fx_coe_mem_closure_toExt_unitDisc hζ.le
    show Function.invFunOn F C (F₀ (ζ : ExtPlane)) = (ζ : ExtPlane)
    rw [← hbd ζ hζ, hF3.leftInvOn_invFunOn hζC]

/-- **The flux engine.**  On a calibrated saturated set,
`∬_R |φ| = ∬_R ⟨∇u, ∇u⟩ = ∬_R ⟨∇u, ∇(u ∘ g)⟩ ≤ ∬_R |φ| λ_{g,φ}`: the middle equality is the vanishing
of the flux of `1_R ∇u` against `w = u ∘ g - u` (ACL in flow-box coordinates, `w → 0` at `∂Δ` by the
Lipschitz bound; partition of unity, cut-offs at the zeros and at `∂Δ`), the inequality is
`t25_pointwise_lipschitz_calibration` at a.e. point (Lusin (N) for `g⁻¹`). -/
theorem fx_flux_engine {g : ℂ → ℂ} {K : ℝ} (hg : fx_IsGoodSelfMap g K) {φ : ℂ → ℂ} {ρ : ℝ}
    (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ)) {R : Set ℂ} {u : ℂ → ℝ}
    (hcal : fx_IsCalib φ R u) :
    ∫⁻ z in R, ENNReal.ofReal ‖φ z‖ ≤
      ∫⁻ z in R, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z) := by
  have hgK : IsKQC g unitDisc K := hg.1
  have hgs : g '' unitDisc = unitDisc := hg.2.1
  have hΔo : IsOpen unitDisc := isOpen_ball
  have hR : MeasurableSet R := hcal.meas
  have hRΔ : R ⊆ unitDisc := hcal.sub
  by_cases hne : ∃ z ∈ unitDisc, φ z ≠ 0
  swap
  · push Not at hne
    have hR0 : R = ∅ := eq_empty_of_forall_notMem fun z hz =>
      hcal.reg z hz (hne z (hRΔ hz))
    rw [hR0]
    simp
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ unitDisc, ‖φ z‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
      (hφ.continuousOn.mono (closedBall_subset_ball hρ))
    exact ⟨M, fun z hz => by simpa using hM z (ball_subset_closedBall hz)⟩
  obtain ⟨L, hL⟩ := hcal.lip
  -- a.e. differentiability and the chain rule
  have hgd := thm9_3_differentiable_ae hgK
  have hug := fx_ae_comp hgK hgs hcal.grad
  have hu := hcal.grad
  have hwd : ∀ᵐ z ∂(volume.restrict unitDisc),
      DifferentiableAt ℝ (fun y => u (g y) - u y) z := by
    filter_upwards [hgd, hug, hu] with z h1 h2 h3
    exact (h2.1.comp z h1).sub h3.1
  have hwint : IntegrableOn (fun z => ‖fderiv ℝ (fun y => u (g y) - u y) z‖) unitDisc := by
    have hbd : IntegrableOn (fun z => (L : ℝ) * (‖dz g z‖ + ‖dzbar g z‖) + L) unitDisc :=
      ((fx_integrable_dz_add hgK hgs).const_mul (L : ℝ)).add
        (integrableOn_const measure_ball_lt_top.ne)
    refine Integrable.mono' hbd (measurable_fderiv ℝ _).norm.aestronglyMeasurable ?_
    filter_upwards [hgd, hug, hu, ae_restrict_mem measurableSet_ball] with z h1 h2 h3 hz
    have hgz : g z ∈ unitDisc := hgs ▸ mem_image_of_mem g hz
    have hfd : fderiv ℝ (fun y => u (g y) - u y) z =
        (fderiv ℝ u (g z)).comp (fderiv ℝ g z) - fderiv ℝ u z := by
      have hc : HasFDerivAt (fun y => u (g y)) ((fderiv ℝ u (g z)).comp (fderiv ℝ g z)) z :=
        h2.1.hasFDerivAt.comp z h1.hasFDerivAt
      exact (hc.sub h3.1.hasFDerivAt).fderiv
    have hLu : ∀ y ∈ unitDisc, ‖fderiv ℝ u y‖ ≤ L := fun y hy =>
      norm_fderiv_le_of_lipschitzOn ℝ (hΔo.mem_nhds hy) hL
    have hgn : ‖fderiv ℝ g z‖ ≤ ‖dz g z‖ + ‖dzbar g z‖ := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      rw [sp_c_fderiv_eq_dz_dzbar]
      calc ‖dz g z * v + dzbar g z * conj v‖ ≤ ‖dz g z * v‖ + ‖dzbar g z * conj v‖ :=
            norm_add_le _ _
        _ = (‖dz g z‖ + ‖dzbar g z‖) * ‖v‖ := by
            rw [norm_mul, norm_mul, Complex.norm_conj]; ring
    rw [norm_norm, hfd]
    calc ‖(fderiv ℝ u (g z)).comp (fderiv ℝ g z) - fderiv ℝ u z‖
        ≤ ‖fderiv ℝ u (g z)‖ * ‖fderiv ℝ g z‖ + ‖fderiv ℝ u z‖ :=
          (norm_sub_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) le_rfl)
      _ ≤ L * (‖dz g z‖ + ‖dzbar g z‖) + L :=
          add_le_add (mul_le_mul (hLu _ hgz) hgn (norm_nonneg _) L.2) (hLu z hz)
  have hflux := fx_flux_identity hg hρ hφ hcal hne hM hwd hwint
  have hCwint := fx_flux_integrable hcal hM hwint
  -- on `R`: `⟨∇u, ∇(u ∘ g)⟩ = ⟨∇u, ∇w⟩ + |φ|` and `⟨∇u, ∇(u ∘ g)⟩ ≤ |φ| λ` a.e.
  set Bf : ℂ → ℝ := fun z => fderiv ℝ (fun y => u (g y)) z (fx_grad u z) with hBf
  have hae : ∀ᵐ z ∂(volume.restrict R),
      Bf z = fderiv ℝ (fun y => u (g y) - u y) z (fx_grad u z) + ‖φ z‖ ∧
        Bf z ≤ ‖φ z‖ * lambdaStretchPlane φ φ g z := by
    have h1 := ae_restrict_of_ae_restrict_of_subset hRΔ (hgd.and hug)
    filter_upwards [h1, ae_restrict_mem hR] with z hz hzR
    obtain ⟨hgz, hugz⟩ := hz
    obtain ⟨s, hs, hud, -, hgr⟩ := fx_calib_at hcal hzR
    have hcomp : DifferentiableAt ℝ (fun y => u (g y)) z := hugz.1.comp z hgz
    have hfcomp : fderiv ℝ (fun y => u (g y)) z = (fderiv ℝ u (g z)).comp (fderiv ℝ g z) :=
      fderiv_comp z hugz.1 hgz
    constructor
    · have hfd : fderiv ℝ (fun y => u (g y) - u y) z =
          fderiv ℝ (fun y => u (g y)) z - fderiv ℝ u z :=
        (hcomp.hasFDerivAt.sub hud.hasFDerivAt).fderiv
      rw [hfd, sub_apply, (fx_calib_grad hcal hzR).2]
      simp only [hBf]
      ring
    · have hcal' := t25_pointwise_lipschitz_calibration (φ := φ) (g := g)
        (L := fderiv ℝ u (g z)) hugz.2 hs
      calc Bf z ≤ |Bf z| := le_abs_self _
        _ = |fderiv ℝ u (g z) (fderiv ℝ g z (conj s))| := by
            simp only [hBf, hfcomp, hgr, ContinuousLinearMap.comp_apply]
        _ ≤ ‖φ z‖ * lambdaStretchPlane φ φ g z := hcal'
  have hφint : IntegrableOn (fun z => ‖φ z‖) R := by
    refine Integrable.mono' (integrableOn_const (C := M)
      ((measure_mono hRΔ).trans_lt measure_ball_lt_top).ne)
      ((hφ.continuousOn.mono ((hRΔ.trans (ball_subset_ball hρ.le)))).norm.aestronglyMeasurable hR)
      ((ae_restrict_iff' hR).2 (Eventually.of_forall fun z hz => ?_))
    rw [norm_norm]
    exact hM z (hRΔ hz)
  have hBint : IntegrableOn Bf R :=
    (hCwint.add hφint).congr (hae.mono fun z hz => hz.1.symm)
  have heq : ∫ z in R, ‖φ z‖ = ∫ z in R, Bf z := by
    have h1 : ∫ z in R, Bf z =
        ∫ z in R, (fderiv ℝ (fun y => u (g y) - u y) z (fx_grad u z) + ‖φ z‖) :=
      integral_congr_ae (hae.mono fun z hz => hz.1)
    rw [h1, integral_add hCwint hφint, hflux, zero_add]
  calc ∫⁻ z in R, ENNReal.ofReal ‖φ z‖ = ENNReal.ofReal (∫ z in R, ‖φ z‖) :=
        (ofReal_integral_eq_lintegral_ofReal hφint
          (Eventually.of_forall fun z => norm_nonneg _)).symm
    _ = ENNReal.ofReal (∫ z in R, Bf z) := by rw [heq]
    _ ≤ ENNReal.ofReal (∫ z in R, max (Bf z) 0) :=
        ENNReal.ofReal_le_ofReal (integral_mono hBint hBint.pos_part fun z => le_max_left _ _)
    _ = ∫⁻ z in R, ENNReal.ofReal (max (Bf z) 0) :=
        ofReal_integral_eq_lintegral_ofReal hBint.pos_part
          (Eventually.of_forall fun z => le_max_right _ _)
    _ = ∫⁻ z in R, ENNReal.ofReal (Bf z) := by
        refine lintegral_congr fun z => ?_
        rcases le_total (Bf z) 0 with h | h
        · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
        · rw [max_eq_left h]
    _ ≤ ∫⁻ z in R, ENNReal.ofReal (‖φ z‖ * lambdaStretchPlane φ φ g z) :=
        lintegral_mono_ae (hae.mono fun z hz => ENNReal.ofReal_le_ofReal hz.2)
    _ = ∫⁻ z in R, ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z) :=
        lintegral_congr fun z => ENNReal.ofReal_mul (norm_nonneg _)

/-- **(35.5) for tame `φ`** (holomorphic on a disc of radius `> 1`): sum the flux engine over the
covering `fx_cover`. -/
theorem fx_eq35_5_tame {g : ℂ → ℂ} {K : ℝ} (hg : fx_IsGoodSelfMap g K) {φ : ℂ → ℂ} {ρ : ℝ}
    (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ)) :
    phiArea φ unitDisc ≤ ∫⁻ z in unitDisc,
      ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z) := by
  by_cases hne : ∃ z ∈ unitDisc, φ z ≠ 0
  · obtain ⟨N, R, u, hdisj, hcov, hcal⟩ := fx_cover hρ hφ hne
    have hUsub : (⋃ i, R i) ⊆ unitDisc := iUnion_subset fun i => (hcal i).sub
    have hae : (⋃ i, R i : Set ℂ) =ᵐ[volume] (unitDisc : Set ℂ) :=
      ae_eq_set.2 ⟨by rw [sdiff_eq_empty.2 hUsub, measure_empty], hcov⟩
    have hm : ∀ i, MeasurableSet (R i) := fun i => (hcal i).meas
    calc phiArea φ unitDisc = ∫⁻ z in ⋃ i, R i, ENNReal.ofReal ‖φ z‖ := by
          rw [phiArea, setLIntegral_congr hae]
      _ = ∑ i, ∫⁻ z in R i, ENNReal.ofReal ‖φ z‖ := by
          rw [lintegral_iUnion hm hdisj, tsum_fintype]
      _ ≤ ∑ i, ∫⁻ z in R i,
            ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z) :=
          Finset.sum_le_sum fun i _ => fx_flux_engine hg hρ hφ (hcal i)
      _ = ∫⁻ z in ⋃ i, R i,
            ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z) := by
          rw [lintegral_iUnion hm hdisj, tsum_fintype]
      _ = ∫⁻ z in unitDisc,
            ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z) :=
          setLIntegral_congr hae
  · push Not at hne
    have h0 : phiArea φ unitDisc = 0 :=
      setLIntegral_eq_zero measurableSet_ball fun z hz => by simp [hne z hz]
    rw [h0]
    exact bot_le

/-- **The approximation step** `φ_r(z) = r² φ(r z)`: (35.5) for all tame `ψ` implies it for every
`φ` holomorphic in `Δ` with `‖φ‖ < ∞` (monotone convergence on the left; Pratt's lemma on the right, with the dominator
`(|φ_r| + K |φ_r ∘ g| J_g)/2` and the change of variables through `g`). -/
theorem fx_eq35_5_limit {g : ℂ → ℂ} {K : ℝ} (hg : fx_IsGoodSelfMap g K)
    (htame : ∀ (ψ : ℂ → ℂ) (ρ : ℝ), 1 < ρ → DifferentiableOn ℂ ψ (ball 0 ρ) →
      phiArea ψ unitDisc ≤ ∫⁻ z in unitDisc,
        ENNReal.ofReal ‖ψ z‖ * ENNReal.ofReal (lambdaStretchPlane ψ ψ g z))
    {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc ∧ phiArea φ unitDisc < ⊤) :
    phiArea φ unitDisc ≤ ∫⁻ z in unitDisc,
      ENNReal.ofReal ‖φ z‖ * ENNReal.ofReal (lambdaStretchPlane φ φ g z) := by
  obtain ⟨hgK, hgs, -⟩ := hg
  obtain ⟨hφd, hφA⟩ := hφ
  have hΔ : MeasurableSet unitDisc := measurableSet_ball
  have hΔo : IsOpen unitDisc := isOpen_ball
  have hK0 : 0 ≤ K := zero_le_one.trans hgK.2.1
  have hgc : ContinuousOn g unitDisc := hgK.2.2.1.1
  have hgm : MapsTo g unitDisc unitDisc := fun z hz => hgs ▸ mem_image_of_mem g hz
  have hφc : ContinuousOn φ unitDisc := hφd.continuousOn
  -- the radii `r n = 1 - 1/(n+2) ↑ 1`
  set r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hrdef
  have hr0 : ∀ n, 0 < r n := fun n => by
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)])
    simp only [hrdef]
    linarith
  have hr1 : ∀ n, r n < 1 := fun n => by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    simp only [hrdef]
    linarith
  have hrmono : Monotone r := by
    intro m n hmn
    simp only [hrdef]
    have : 1 / ((n : ℝ) + 2) ≤ 1 / ((m : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : m + 2 ≤ n + 2))
    linarith
  have hrt : Tendsto r atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      exact squeeze_zero (fun n => by positivity)
        (fun n => one_div_le_one_div_of_le (by positivity) (by linarith)) this
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub h
    rw [sub_zero] at h2
    exact h2
  -- the rescaled differentials
  set ψ : ℕ → ℂ → ℂ := fun n z => (r n : ℂ) ^ 2 * φ (r n * z) with hψdef
  have hmapsr : ∀ n, ∀ z ∈ ball (0 : ℂ) (1 / r n), (r n : ℂ) * z ∈ unitDisc := by
    intro n z hz
    rw [mem_ball_zero_iff] at hz
    rw [unitDisc, mem_ball_zero_iff, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (hr0 n)]
    calc r n * ‖z‖ < r n * (1 / r n) := mul_lt_mul_of_pos_left hz (hr0 n)
      _ = 1 := mul_one_div_cancel (hr0 n).ne'
  have hψd : ∀ n, DifferentiableOn ℂ (ψ n) (ball 0 (1 / r n)) := fun n =>
    (differentiableOn_const _).mul (hφd.comp ((differentiable_id.const_mul _).differentiableOn)
      (hmapsr n))
  have hρ : ∀ n, 1 < 1 / r n := fun n => by
    rw [lt_one_div (by norm_num) (hr0 n)]
    simpa using hr1 n
  have hsub : ∀ n, unitDisc ⊆ ball (0 : ℂ) (1 / r n) := fun n =>
    ball_subset_ball (le_of_lt (hρ n))
  have hψc : ∀ n, ContinuousOn (ψ n) unitDisc := fun n => ((hψd n).mono (hsub n)).continuousOn
  have htn := fun n => htame (ψ n) (1 / r n) (hρ n) (hψd n)
  -- pointwise convergence
  have hψt : ∀ z ∈ unitDisc, Tendsto (fun n => ψ n z) atTop (𝓝 (φ z)) := fun z hz =>
    fx_tendsto_rescale (hφc.continuousAt (hΔo.mem_nhds hz)) hrt
  -- the integrands
  set P : ℂ → ℂ → ℂ → ℝ := fun z p q =>
    Real.sqrt ‖p‖ * Real.sqrt ‖q‖ * ‖dz g z + dzbar g z * (p / (‖p‖ : ℂ))‖ with hPdef
  have hI : ∀ (χ : ℂ → ℂ) (z : ℂ), ENNReal.ofReal ‖χ z‖ *
      ENNReal.ofReal (lambdaStretchPlane χ χ g z) = ENNReal.ofReal (P z (χ z) (χ (g z))) := by
    intro χ z
    rw [← ENNReal.ofReal_mul (norm_nonneg _)]
    congr 1
    exact fx_norm_mul_lambda _ _ _ _
  set μ := volume.restrict unitDisc with hμ
  set f : ℕ → ℂ → ℝ≥0∞ := fun n z => ENNReal.ofReal (P z (ψ n z) (ψ n (g z))) with hfdef
  set F : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (P z (φ z) (φ (g z))) with hFdef
  set d : ℕ → ℂ → ℝ≥0∞ := fun n z => ENNReal.ofReal ‖ψ n z‖ +
    ENNReal.ofReal K * (ENNReal.ofReal (jacobian g z) * ENNReal.ofReal ‖ψ n (g z)‖) with hddef
  set D : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal ‖φ z‖ +
    ENNReal.ofReal K * (ENNReal.ofReal (jacobian g z) * ENNReal.ofReal ‖φ (g z)‖) with hDdef
  -- measurability
  have hJm : Measurable (jacobian g) :=
    ((measurable_dz g).norm.pow_const 2).sub ((measurable_dzbar g).norm.pow_const 2)
  have hPm : ∀ χ : ℂ → ℂ, ContinuousOn χ unitDisc →
      AEMeasurable (fun z => ENNReal.ofReal (P z (χ z) (χ (g z)))) μ := by
    intro χ hχ
    have h1 : AEMeasurable χ μ := (hχ.aestronglyMeasurable hΔ).aemeasurable
    have h2 : AEMeasurable (fun z => χ (g z)) μ :=
      ((hχ.comp hgc hgm).aestronglyMeasurable hΔ).aemeasurable
    have h3 : AEMeasurable (fun z => ((‖χ z‖ : ℝ) : ℂ)) μ :=
      Complex.measurable_ofReal.comp_aemeasurable h1.norm
    refine ENNReal.measurable_ofReal.comp_aemeasurable ?_
    exact ((Real.continuous_sqrt.measurable.comp_aemeasurable h1.norm).mul
      (Real.continuous_sqrt.measurable.comp_aemeasurable h2.norm)).mul
      (((measurable_dz g).aemeasurable.add ((measurable_dzbar g).aemeasurable.mul
        (h1.div h3))).norm)
  have hDm : ∀ χ : ℂ → ℂ, ContinuousOn χ unitDisc →
      AEMeasurable (fun z => ENNReal.ofReal ‖χ z‖ +
        ENNReal.ofReal K * (ENNReal.ofReal (jacobian g z) * ENNReal.ofReal ‖χ (g z)‖)) μ := by
    intro χ hχ
    have h1 : AEMeasurable χ μ := (hχ.aestronglyMeasurable hΔ).aemeasurable
    have h2 : AEMeasurable (fun z => χ (g z)) μ :=
      ((hχ.comp hgc hgm).aestronglyMeasurable hΔ).aemeasurable
    exact (ENNReal.measurable_ofReal.comp_aemeasurable h1.norm).add
      (aemeasurable_const.mul ((ENNReal.measurable_ofReal.comp hJm).aemeasurable.mul
        (ENNReal.measurable_ofReal.comp_aemeasurable h2.norm)))
  -- the integral of the dominator
  have hdint : ∀ χ : ℂ → ℂ, ContinuousOn χ unitDisc →
      ∫⁻ z in unitDisc, (ENNReal.ofReal ‖χ z‖ +
        ENNReal.ofReal K * (ENNReal.ofReal (jacobian g z) * ENNReal.ofReal ‖χ (g z)‖)) =
        phiArea χ unitDisc + ENNReal.ofReal K * phiArea χ unitDisc := by
    intro χ hχ
    have h1 : AEMeasurable χ μ := (hχ.aestronglyMeasurable hΔ).aemeasurable
    have h1' : AEMeasurable (fun z => ENNReal.ofReal ‖χ z‖) μ :=
      ENNReal.measurable_ofReal.comp_aemeasurable h1.norm
    rw [lintegral_add_left' h1',
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, phiArea]
    congr 2
    have hcv := fx_lintegral_image_eq hgK (fun w => ENNReal.ofReal ‖χ w‖)
    rw [hgs] at hcv
    exact hcv.symm
  -- the left-hand sides converge
  have he : Tendsto (fun n => phiArea (ψ n) unitDisc) atTop (𝓝 (phiArea φ unitDisc)) := by
    have hball : ∀ n, phiArea (ψ n) unitDisc =
        (volume.withDensity fun w => ENNReal.ofReal ‖φ w‖) (ball 0 (r n)) := fun n => by
      rw [withDensity_apply _ measurableSet_ball]
      exact fx_phiArea_rescale φ (hr0 n)
    have hmono : Monotone fun n => ball (0 : ℂ) (r n) := fun m n hmn =>
      ball_subset_ball (hrmono hmn)
    have hU : (⋃ n, ball (0 : ℂ) (r n)) = unitDisc := by
      ext z
      simp only [mem_iUnion, unitDisc, mem_ball_zero_iff]
      constructor
      · rintro ⟨n, hn⟩
        exact hn.trans (hr1 n)
      · intro hz
        obtain ⟨n, hn⟩ := (hrt.eventually (lt_mem_nhds hz)).exists
        exact ⟨n, hn⟩
    have := tendsto_measure_iUnion_atTop (μ := volume.withDensity fun w => ENNReal.ofReal ‖φ w‖)
      hmono
    rw [hU, withDensity_apply _ hΔ] at this
    simp only [Function.comp_def, ← hball] at this
    exact this
  have hmain : phiArea φ unitDisc ≤ ∫⁻ z, F z ∂μ := by
    refine fx_pratt (μ := μ) (f := f) (d := d) (F := F) (D := D)
      (fun n => hPm (ψ n) (hψc n)) (fun n => hDm (ψ n) (hψc n)) (fun n => ?_) ?_ ?_ ?_ ?_ he
      (fun n => ?_)
    · -- domination
      filter_upwards [thm9_4_dilatation_ae hgK] with z hz
      have hA := norm_nonneg (dz g z)
      have hB := norm_nonneg (dzbar g z)
      have hBA : ‖dzbar g z‖ ≤ ‖dz g z‖ := by
        by_contra hlt
        push Not at hlt
        have : K * (‖dz g z‖ - ‖dzbar g z‖) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hK0 (by linarith)
        linarith
      have hJ0 : 0 ≤ jacobian g z := by
        unfold jacobian
        nlinarith
      have hKJ : (‖dz g z‖ + ‖dzbar g z‖) ^ 2 ≤ K * jacobian g z := by
        unfold jacobian
        nlinarith
      have hb := fx_amgm_bound (ψ n z) (ψ n (g z)) (dz g z) (dzbar g z) hKJ
      show ENNReal.ofReal (P z (ψ n z) (ψ n (g z))) ≤ _
      calc ENNReal.ofReal (P z (ψ n z) (ψ n (g z)))
          ≤ ENNReal.ofReal (‖ψ n z‖ + K * jacobian g z * ‖ψ n (g z)‖) :=
            ENNReal.ofReal_le_ofReal hb
        _ = _ := by
            rw [ENNReal.ofReal_add (norm_nonneg _) (by positivity), mul_assoc,
              ENNReal.ofReal_mul hK0, ENNReal.ofReal_mul hJ0]
    · -- `f n → F`
      filter_upwards [ae_restrict_mem hΔ] with z hz
      exact (ENNReal.tendsto_ofReal (fx_tendsto_P (hψt z hz) (hψt (g z) (hgm hz))))
    · -- `d n → D`
      filter_upwards [ae_restrict_mem hΔ] with z hz
      exact (ENNReal.tendsto_ofReal (hψt z hz).norm).add
        (ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul
          (ENNReal.tendsto_ofReal (hψt (g z) (hgm hz)).norm) (Or.inr ENNReal.ofReal_ne_top))
          (Or.inr ENNReal.ofReal_ne_top))
    · -- `∫ d n → ∫ D`
      show Tendsto (fun n => ∫⁻ z in unitDisc, d n z) atTop (𝓝 (∫⁻ z in unitDisc, D z))
      simp only [hddef, hDdef]
      rw [hdint φ hφc]
      simp only [fun n => hdint (ψ n) (hψc n)]
      exact he.add (ENNReal.Tendsto.const_mul he (Or.inr ENNReal.ofReal_ne_top))
    · show ∫⁻ z in unitDisc, D z ≠ ⊤
      simp only [hDdef]
      rw [hdint φ hφc]
      exact ENNReal.add_ne_top.2 ⟨hφA.ne, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hφA.ne⟩
    · show phiArea (ψ n) unitDisc ≤ ∫⁻ z in unitDisc, f n z
      refine (htn n).trans (le_of_eq ?_)
      exact lintegral_congr fun z => hI (ψ n) z
  refine hmain.trans (le_of_eq ?_)
  exact lintegral_congr fun z => (hI φ z).symm

/-- **(35.5) of the module** (`eq35_5_integrated` with the S35 aliases unfolded:
`lambdaStretchDisc φ g = lambdaStretchPlane φ φ g`, `φ ∈ integrableQD ↔ DifferentiableOn ℂ φ unitDisc ∧
phiArea φ unitDisc < ⊤`), assembled from the pieces above. -/
theorem fx_eq35_5 {f f₀ : ℂ → ℂ} (hf : IsQuasiconformal f unitDisc)
    (hf₀ : IsQuasiconformal f₀ unitDisc)
    (hfs : f '' unitDisc = unitDisc) (hf₀s : f₀ '' unitDisc = unitDisc) {F F₀ : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f unitDisc unitDisc F) (hF₀ : IsHomeoExtension f₀ unitDisc unitDisc F₀)
    (hbd : ∀ ζ : ℂ, ‖ζ‖ = 1 → F ζ = F₀ ζ) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc ∧ phiArea φ unitDisc < ⊤) :
    phiArea φ unitDisc ≤ ∫⁻ z in unitDisc,
      ENNReal.ofReal ‖φ z‖ *
        ENNReal.ofReal (lambdaStretchPlane φ φ (Function.invFunOn f unitDisc ∘ f₀) z) := by
  obtain ⟨K, hg⟩ := fx_isGoodSelfMap_of_boundary hf hf₀ hfs hf₀s hF hF₀ hbd
  exact fx_eq35_5_limit hg (fun ψ ρ hρ hψ => fx_eq35_5_tame hg hρ hψ) hφ

/-! ## §6 The geodesic property (not on the (35.5) path) -/

/-- A complex number whose square is a positive real is real. -/
theorem fx_p5_im_eq_zero_of_sq {w : ℂ} (him : (w ^ 2).im = 0) (hre : 0 < (w ^ 2).re) :
    w.im = 0 := by
  have h1 : (w ^ 2).im = 2 * w.re * w.im := by rw [sq, mul_im]; ring
  have h2 : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by rw [sq, mul_re]; ring
  rw [h1] at him
  rw [h2] at hre
  rcases mul_eq_zero.1 him with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · norm_num at h'
    · rw [h'] at hre
      nlinarith [sq_nonneg w.im]
  · exact h

/-- **Slope comparison.**  If `|f s - f τ| ≤ ‖G (γ s) - G (γ τ)‖` near `τ`, then
`|f'(τ)| ≤ ‖G'‖ ‖γ'(τ)‖`. -/
theorem fx_p5_slope_bound {f : ℝ → ℝ} {γ : ℝ → ℂ} {G : ℂ → ℂ} {τ f' : ℝ} {γ' G' : ℂ}
    (hf : HasDerivAt f f' τ) (hγ : HasDerivAt γ γ' τ) (hG : HasDerivAt G G' (γ τ))
    (hb : ∀ᶠ s in 𝓝 τ, |f s - f τ| ≤ ‖G (γ s) - G (γ τ)‖) : |f'| ≤ ‖G'‖ * ‖γ'‖ := by
  have hGγ : HasDerivAt (fun s => G (γ s)) (G' * γ') τ := hG.comp τ hγ
  have h1 := (hasDerivAt_iff_tendsto_slope.1 hf).norm
  have h2 := (hasDerivAt_iff_tendsto_slope.1 hGγ).norm
  rw [← norm_mul, ← Real.norm_eq_abs]
  refine le_of_tendsto_of_tendsto h1 h2 ?_
  filter_upwards [nhdsWithin_le_nhds hb] with s hs
  rw [slope_def_module, slope_def_module, norm_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left (by rwa [Real.norm_eq_abs]) (norm_nonneg _)

/-- FTC for a nonnegative derivative, in `ℝ≥0∞`. -/
theorem fx_p5_lintegral_deriv_nonneg {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b)) (hd : ∀ t ∈ Ioo a b, HasDerivAt f (f' t) t)
    (hpos : ∀ t ∈ Ioo a b, 0 ≤ f' t) :
    ∫⁻ t in Ioo a b, ENNReal.ofReal (f' t) = ENNReal.ofReal (f b - f a) := by
  have hint : IntegrableOn f' (Ioc a b) := intervalIntegral.integrableOn_deriv_of_nonneg hcont hd hpos
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hd
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hint)
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at hftc
  rw [← hftc, ofReal_integral_eq_lintegral_ofReal (hint.mono_set Ioo_subset_Ioc_self)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall hpos))]

/-- The parameters at which a curve passes through a given point with nonzero velocity form a
countable set (each of them is isolated among the passages). -/
theorem fx_p5_pass_countable (β : ℝ → ℂ) (q : ℂ) :
    {τ | β τ = q ∧ DifferentiableAt ℝ β τ ∧ deriv β τ ≠ 0}.Countable := by
  refine (countable_setOfPred_isolated_right_within (s := β ⁻¹' {q})).mono ?_
  rintro τ ⟨hq, hd, hne⟩
  refine ⟨hq, ?_⟩
  have hev : ∀ᶠ s in 𝓝[≠] τ, β s ≠ q := by
    have h := hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt
    filter_upwards [h.eventually_ne hne] with s hs hβs
    apply hs
    rw [slope_def_module, hβs, hq, sub_self, smul_zero]
  rw [← empty_mem_iff_bot]
  have hle : 𝓝[β ⁻¹' {q} ∩ Ioi τ] τ ≤ 𝓝[≠] τ :=
    nhdsWithin_mono _ fun s hs => ne_of_gt hs.2
  filter_upwards [hle hev, self_mem_nhdsWithin] with s hs hs'
  exact hs hs'.1

/-- One-sided density in a flow box: if `|u w - v| = |Re ζ w - a|` on the side `Re ζ > a` and `u` is
continuous at a point `z` of the plaque `Re ζ = a`, then `u z = v`. -/
theorem fx_p5_box_side {φ ζ : ℂ → ℂ} {N : Set ℂ} (hN : fx_IsFlowBox φ ζ N) {a v : ℝ}
    {u : ℂ → ℝ} (hv : ∀ w ∈ N, a < (ζ w).re → |u w - v| = |(ζ w).re - a|) {z : ℂ} (hz : z ∈ N)
    (hza : (ζ z).re = a) (huz : ContinuousAt u z) : u z = v := by
  by_contra hne
  set d := |u z - v| with hd
  have hdpos : 0 < d := abs_pos.2 (sub_ne_zero.2 hne)
  have hev : ∀ᶠ w in 𝓝 z, |u w - u z| < d / 2 := by
    have := Metric.tendsto_nhds.1 huz (d / 2) (by linarith)
    filter_upwards [this] with w hw
    rwa [Real.dist_eq] at hw
  obtain ⟨U, hUsub, hUo, hzU⟩ := _root_.mem_nhds_iff.1 hev
  have hopen : IsOpen (ζ '' (U ∩ N)) :=
    fx_p4_flowBox_isOpen_image hN (hUo.inter hN.1) inter_subset_right
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hopen (ζ z) ⟨z, ⟨hzU, hz⟩, rfl⟩
  set s := min (η / 2) (d / 2) with hs
  have hspos : 0 < s := lt_min (by linarith) (by linarith)
  have hsd : s ≤ d / 2 := min_le_right _ _
  have hmem : ζ z + (s : ℂ) ∈ ball (ζ z) η := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hspos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨w, ⟨hwU, hwN⟩, hw⟩ := hball hmem
  have hwre : (ζ w).re = a + s := by rw [hw, add_re, ofReal_re, hza]
  have h1 := hv w hwN (by rw [hwre]; linarith)
  rw [hwre, add_sub_cancel_left, abs_of_pos hspos] at h1
  have h2 : |u w - u z| < d / 2 := hUsub hwU
  have h3 : |u z - v| ≤ |u z - u w| + |u w - v| := abs_sub_le _ _ _
  rw [abs_sub_comm (u z) (u w)] at h3
  have : d < d := by
    calc d = |u z - v| := rfl
      _ ≤ |u w - u z| + |u w - v| := h3
      _ < d / 2 + d / 2 := by linarith
      _ = d := by ring
  exact lt_irrefl _ this
/-- **Pointwise upper gradient of a cut calibration.**  At every regular point `p` of `Δ` there is a
local natural parameter `G` (`G'² = φ p`) with `|u z - u p| ≤ ‖G z - G p‖` near `p`: off the cuts
`G = Φ`; on a picked edge `G = ζ`, the chart of the forest's flow box (there `u` is continuous and
`|Re Φ - v±| = |Re ζ - a|` on the two sides, so `u = v± = u p` on the plaque). -/
theorem fx_p5_pug {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ) (hφ : DifferentiableOn ℂ φ (ball 0 ρ))
    {ι : Type} {par : ι → ℝ → ℂ} {src : ι → ℂ} {dst : ι → Option ℂ}
    (hF : fx_IsVForest φ par src dst) {pick : {q : ℂ // q ∈ unitDisc ∧ φ q = 0} → ι}
    {Φ : ℂ → ℂ} (hΦd : DifferentiableOn ℂ Φ (unitDisc \ fx_cutSet φ par pick))
    (hΦ2 : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, deriv Φ z ^ 2 = φ z) {u : ℂ → ℝ}
    (hu : ∀ z ∈ unitDisc \ fx_cutSet φ par pick, u z = (Φ z).re) (hucont : ContinuousOn u unitDisc)
    {p : ℂ} (hp : p ∈ unitDisc) (hp0 : φ p ≠ 0) :
    ∃ (G : ℂ → ℂ) (G' : ℂ), HasDerivAt G G' p ∧ G' ^ 2 = φ p ∧
      ∀ᶠ z in 𝓝 p, |u z - u p| ≤ ‖G z - G p‖ := by
  have hΩo : IsOpen (unitDisc \ fx_cutSet φ par pick) := fx_p4_cut_isOpen hρ hφ hF pick
  by_cases hpΩ : p ∈ unitDisc \ fx_cutSet φ par pick
  · refine ⟨Φ, deriv Φ p, (hΦd.differentiableAt (hΩo.mem_nhds hpΩ)).hasDerivAt, hΦ2 p hpΩ, ?_⟩
    filter_upwards [hΩo.mem_nhds hpΩ] with z hz
    rw [hu z hz, hu p hpΩ, ← sub_re]
    exact abs_re_le_norm _
  have hpc : p ∈ fx_cutSet φ par pick := by
    by_contra h
    exact hpΩ ⟨hp, h⟩
  rcases hpc with ⟨-, h0⟩ | he
  · exact absurd h0 hp0
  obtain ⟨q₀, t, ht, rfl⟩ := mem_iUnion.1 he
  obtain ⟨ζ, N, hpN, hN, hΩN, -, vP, vM, hvP, hvM⟩ := fx_p4_cut_box hF hΦd hΦ2 q₀ ht
  have hcontN : ∀ z ∈ N, ContinuousAt u z := fun z hz =>
    hucont.continuousAt (isOpen_ball.mem_nhds (hN.2.1 hz))
  have hvP' : ∀ w ∈ N, (ζ (par (pick q₀) t)).re < (ζ w).re →
      |u w - vP| = |(ζ w).re - (ζ (par (pick q₀) t)).re| := fun w hw h => by
    rw [hu w ((hΩN w hw).2 (ne_of_gt h))]
    exact hvP w hw h
  have hvM' : ∀ w ∈ N, (ζ w).re < (ζ (par (pick q₀) t)).re →
      |u w - vM| = |(ζ w).re - (ζ (par (pick q₀) t)).re| := fun w hw h => by
    rw [hu w ((hΩN w hw).2 (ne_of_lt h))]
    exact hvM w hw h
  have hvM'' : ∀ w ∈ N, -(ζ (par (pick q₀) t)).re < (-ζ w).re →
      |u w - vM| = |(-ζ w).re - -(ζ (par (pick q₀) t)).re| := fun w hw h => by
    rw [neg_re] at h ⊢
    rw [show -(ζ w).re - -(ζ (par (pick q₀) t)).re =
      -((ζ w).re - (ζ (par (pick q₀) t)).re) by ring, abs_neg]
    exact hvM' w hw (by linarith)
  have hPl : ∀ z ∈ N, (ζ z).re = (ζ (par (pick q₀) t)).re → u z = vP := fun z hz hza =>
    fx_p5_box_side hN hvP' hz hza (hcontN z hz)
  have hMl : ∀ z ∈ N, (ζ z).re = (ζ (par (pick q₀) t)).re → u z = vM := fun z hz hza =>
    fx_p5_box_side (fx_p4_flowBox_neg hN) hvM'' hz (by simp only [neg_re, hza]) (hcontN z hz)
  refine ⟨ζ, deriv ζ (par (pick q₀) t), (hN.2.2.2.1 _ hpN).2.1.hasDerivAt,
    (hN.2.2.2.1 _ hpN).2.2, ?_⟩
  filter_upwards [hN.1.mem_nhds hpN] with z hz
  have hre : |(ζ z).re - (ζ (par (pick q₀) t)).re| ≤ ‖ζ z - ζ (par (pick q₀) t)‖ := by
    rw [← sub_re]
    exact abs_re_le_norm _
  rcases lt_trichotomy (ζ z).re (ζ (par (pick q₀) t)).re with h | h | h
  · rw [hMl _ hpN rfl, hvM' z hz h]
    exact hre
  · rw [hPl z hz h, hPl _ hpN rfl, sub_self, abs_zero]
    exact norm_nonneg _
  · rw [hPl _ hpN rfl, hvP' z hz h]
    exact hre

/-- **A horizontal arc stays on one leaf**: `c t ∈ fx_leaf φ (c s)` for `s, t ∈ (a, b)`.  In a flow
box `Im ζ ∘ c` is locally constant, because `((ζ ∘ c)')² = φ(c) c'² > 0`; then `fx_plaque_leaf`
and connectedness of `(a, b)`. -/
theorem fx_p5_arc_leaf {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc) {c : ℝ → ℂ} {a b : ℝ}
    (hc : IsHorizontalArc φ c a b) (hcD : ∀ t ∈ Ioo a b, c t ∈ unitDisc) {s t : ℝ}
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) : c t ∈ fx_leaf φ (c s) := by
  refine isPreconnected_Ioo.induction₂ (fun x y => c y ∈ fx_leaf φ (c x)) ?_ ?_ ?_ hs ht
  · intro x hx
    obtain ⟨hdx, -, hx0, -, -⟩ := hc x hx
    obtain ⟨ζ, N, hxN, -, hN⟩ := fx_flowBox_exists hφ (hcD x hx) hx0 one_pos
    have hev : ∀ᶠ y in 𝓝 x, y ∈ Ioo a b ∧ c y ∈ N :=
      Filter.Eventually.and (Ioo_mem_nhds hx.1 hx.2 : ∀ᶠ y in 𝓝 x, y ∈ Ioo a b)
        (hdx.continuousAt.preimage_mem_nhds (hN.1.mem_nhds hxN))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
    have hderiv : ∀ y ∈ ball x δ, HasDerivAt (fun y => (ζ (c y)).im) 0 y := by
      intro y hy
      obtain ⟨hyI, hyN⟩ := hball y hy
      obtain ⟨hdy, -, -, him, hre⟩ := hc y hyI
      have hζ := (hN.2.2.2.1 (c y) hyN).2.1.hasDerivAt
      have h1 : HasDerivAt (fun y => ζ (c y)) (deriv ζ (c y) * deriv c y) y :=
        hζ.comp y hdy.hasDerivAt
      have h2 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y h1
      have hsq : (deriv ζ (c y) * deriv c y) ^ 2 = φ (c y) * deriv c y ^ 2 := by
        rw [mul_pow, (hN.2.2.2.1 (c y) hyN).2.2]
      have h0 : (deriv ζ (c y) * deriv c y).im = 0 :=
        fx_p5_im_eq_zero_of_sq (by rw [hsq]; exact him) (by rw [hsq]; exact hre)
      rw [Complex.imCLM_apply, h0] at h2
      exact h2
    have hconst : ∀ y ∈ ball x δ, (ζ (c y)).im = (ζ (c x)).im := fun y hy =>
      isOpen_ball.is_const_of_deriv_eq_zero (convex_ball x δ).isPreconnected
        (fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt)
        (fun z hz => (hderiv z hz).deriv) hy (mem_ball_self hδ)
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds x hδ)] with y hy
    exact fx_plaque_leaf hN hxN (hball y hy).2 (hconst y hy).symm
  · intro x y z _ _ _ hxy hyz
    exact fx_leaf_trans hφ hxy hyz
  · intro x y _ _ hxy
    exact fx_leaf_symm hxy

/-- **Horizontal arcs are calibrated**: if `c (a, b)` avoids the cuts, `u ∘ c` has derivative
`± |φ(c)|^{1/2} |c'|` of constant sign (Darboux), so the `φ`-length of `c` is `|u(c b) - u(c a)|`. -/
theorem fx_p5_arc_len {φ : ℂ → ℂ} {Ω : Set ℂ} (hΩo : IsOpen Ω) {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ Ω) (hΦ2 : ∀ z ∈ Ω, deriv Φ z ^ 2 = φ z) {u : ℂ → ℝ}
    (hu : ∀ z ∈ Ω, u z = (Φ z).re) {c : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hc : IsHorizontalArc φ c a b) (hcΩ : ∀ t ∈ Ioo a b, c t ∈ Ω)
    (hcont : ContinuousOn (fun t => u (c t)) (Icc a b)) :
    ∫⁻ t in Ioo a b, phiDensity φ (c t) * ‖deriv c t‖ₑ ≤ ENNReal.ofReal |u (c b) - u (c a)| := by
  have hd : ∀ t ∈ Ioo a b,
      HasDerivAt (fun t => u (c t)) (deriv Φ (c t) * deriv c t).re t := by
    intro t ht
    have hΦt : HasDerivAt Φ (deriv Φ (c t)) (c t) :=
      (hΦd.differentiableAt (hΩo.mem_nhds (hcΩ t ht))).hasDerivAt
    have h1 : HasDerivAt (fun s => Φ (c s)) (deriv Φ (c t) * deriv c t) t :=
      hΦt.comp t (hc t ht).1.hasDerivAt
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
    rw [Complex.reCLM_apply] at h2
    have hev : (fun s => u (c s)) =ᶠ[𝓝 t] fun s => (Φ (c s)).re := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact hu _ (hcΩ s hs)
    exact h2.congr_of_eventuallyEq hev
  have hval : ∀ t ∈ Ioo a b, |(deriv Φ (c t) * deriv c t).re| =
      Real.sqrt ‖φ (c t)‖ * ‖deriv c t‖ ∧ (deriv Φ (c t) * deriv c t).re ≠ 0 := by
    intro t ht
    obtain ⟨-, hc0, hφ0, him, hre⟩ := hc t ht
    have hsq : (deriv Φ (c t) * deriv c t) ^ 2 = φ (c t) * deriv c t ^ 2 := by
      rw [mul_pow, hΦ2 _ (hcΩ t ht)]
    have h0 := fx_p5_im_eq_zero_of_sq (by rw [hsq]; exact him) (by rw [hsq]; exact hre)
    have hnorm : |(deriv Φ (c t) * deriv c t).re| = ‖deriv Φ (c t) * deriv c t‖ :=
      Complex.abs_re_eq_norm.2 h0
    have hΦn : ‖deriv Φ (c t)‖ = Real.sqrt ‖φ (c t)‖ := by
      rw [← hΦ2 _ (hcΩ t ht), norm_pow, Real.sqrt_sq (norm_nonneg _)]
    refine ⟨by rw [hnorm, norm_mul, hΦn], fun h => ?_⟩
    have h' : ‖deriv Φ (c t) * deriv c t‖ = 0 := by rw [← hnorm, h, abs_zero]
    rw [norm_mul, hΦn] at h'
    rcases mul_eq_zero.1 h' with h1 | h1
    · exact hφ0 (norm_eq_zero.1 ((Real.sqrt_eq_zero (norm_nonneg _)).1 h1))
    · exact hc0 (norm_eq_zero.1 h1)
  have hLHS : ∫⁻ t in Ioo a b, phiDensity φ (c t) * ‖deriv c t‖ₑ =
      ∫⁻ t in Ioo a b, ENNReal.ofReal |(deriv Φ (c t) * deriv c t).re| := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [(hval t ht).1, phiDensity, ENNReal.ofReal_mul (Real.sqrt_nonneg _), ofReal_norm]
  rw [hLHS]
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (convex_Ioo a b)
      (fun t ht => (hd t ht).hasDerivWithinAt) (fun t ht => (hval t ht).2) with hneg | hpos
  · have h := fx_p5_lintegral_deriv_nonneg (f := fun t => -u (c t))
      (f' := fun t => -(deriv Φ (c t) * deriv c t).re) hab.le hcont.neg
      (fun t ht => (hd t ht).neg) (fun t ht => by linarith [hneg t ht])
    calc ∫⁻ t in Ioo a b, ENNReal.ofReal |(deriv Φ (c t) * deriv c t).re|
        = ∫⁻ t in Ioo a b, ENNReal.ofReal (-(deriv Φ (c t) * deriv c t).re) :=
          setLIntegral_congr_fun measurableSet_Ioo fun t ht => by
            rw [abs_of_neg (hneg t ht)]
      _ = ENNReal.ofReal (-u (c b) - -u (c a)) := h
      _ ≤ ENNReal.ofReal |u (c b) - u (c a)| := by
          apply ENNReal.ofReal_le_ofReal
          rw [show -u (c b) - -u (c a) = -(u (c b) - u (c a)) by ring]
          exact neg_le_abs _
  · have h := fx_p5_lintegral_deriv_nonneg (f := fun t => u (c t))
      (f' := fun t => (deriv Φ (c t) * deriv c t).re) hab.le hcont
      (fun t ht => hd t ht) (fun t ht => (hpos t ht).le)
    calc ∫⁻ t in Ioo a b, ENNReal.ofReal |(deriv Φ (c t) * deriv c t).re|
        = ∫⁻ t in Ioo a b, ENNReal.ofReal ((deriv Φ (c t) * deriv c t).re) :=
          setLIntegral_congr_fun measurableSet_Ioo fun t ht => by
            rw [abs_of_pos (hpos t ht)]
      _ = ENNReal.ofReal (u (c b) - u (c a)) := h
      _ ≤ ENNReal.ofReal |u (c b) - u (c a)| := ENNReal.ofReal_le_ofReal (le_abs_self _)
/-- `phiDensity φ z * ‖v‖ₑ` as the `ofReal` of a real product. -/
theorem fx_p5_density_mul (φ : ℂ → ℂ) (z v : ℂ) :
    phiDensity φ z * ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ‖φ z‖ * ‖v‖) := by
  rw [phiDensity, ENNReal.ofReal_mul (Real.sqrt_nonneg _), ofReal_norm]

/-- **The calibration inequality along a sub-arc of a curve.**  If `u` is Lipschitz on `Δ` and has
the pointwise upper gradient `|φ|^{1/2}` at the regular points (as in `fx_p5_pug`), then
`|u(β t) - u(β s)| ≤ l_φ(β)` for `0 < s ≤ t < 1`: `u ∘ β` is Lipschitz on `[s, t]` (FTC for
absolutely continuous functions), and a.e. `|(u ∘ β)'| ≤ |φ(β)|^{1/2} |β'|` (at the countably many
passages through zeros with `β' ≠ 0` the bound may fail; where `β' = 0` the Lipschitz bound gives
`(u ∘ β)' = 0`). -/
theorem fx_p5_curve_ineq {φ : ℂ → ℂ} {u : ℂ → ℝ} {L : ℝ≥0} (hL : LipschitzOnWith L u unitDisc)
    (hZ : {q : ℂ | q ∈ unitDisc ∧ φ q = 0}.Countable)
    (hpug : ∀ p ∈ unitDisc, φ p ≠ 0 → ∃ (G : ℂ → ℂ) (G' : ℂ), HasDerivAt G G' p ∧ G' ^ 2 = φ p ∧
      ∀ᶠ z in 𝓝 p, |u z - u p| ≤ ‖G z - G p‖)
    (β : LRCurve) (hβ : β.trace ⊆ unitDisc) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < 1) :
    ENNReal.ofReal |u (β.toFun t) - u (β.toFun s)| ≤ phiLength φ β := by
  have hIcc : Icc s t ⊆ Ioo 0 1 := Icc_subset_Ioo hs ht
  obtain ⟨K, hK⟩ :=
    (β.locallyLipschitzOn.mono hIcc).exists_lipschitzOnWith_of_compact isCompact_Icc
  have hmaps : MapsTo β.toFun (Icc s t) unitDisc := fun τ hτ => hβ ⟨τ, hIcc hτ, rfl⟩
  have hFL : LipschitzOnWith (L * K) (fun τ => u (β.toFun τ)) (Icc s t) := hL.comp hK hmaps
  have hAC : AbsolutelyContinuousOnInterval (fun τ => u (β.toFun τ)) s t :=
    LipschitzOnWith.absolutelyContinuousOnInterval (by rw [uIcc_of_le hst]; exact hFL)
  have hACβ : AbsolutelyContinuousOnInterval β.toFun s t :=
    LipschitzOnWith.absolutelyContinuousOnInterval (by rw [uIcc_of_le hst]; exact hK)
  have hftc := hAC.integral_deriv_eq_sub
  have hint := hAC.intervalIntegrable_deriv
  have hSc : (⋃ q ∈ {q : ℂ | q ∈ unitDisc ∧ φ q = 0},
      {τ | β.toFun τ = q ∧ DifferentiableAt ℝ β.toFun τ ∧ deriv β.toFun τ ≠ 0}).Countable :=
    hZ.biUnion fun q _ => fx_p5_pass_countable β.toFun q
  have hae : ∀ᵐ τ ∂(volume.restrict (Ioc s t)),
      ENNReal.ofReal |deriv (fun τ => u (β.toFun τ)) τ| ≤
        phiDensity φ (β.toFun τ) * ‖deriv β.toFun τ‖ₑ := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hACβ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc,
      measure_eq_zero_iff_ae_notMem.1 (hSc.measure_zero volume)] with τ hτd hτS hτ
    have hτI : τ ∈ Icc s t := Ioc_subset_Icc_self hτ
    have hβd : DifferentiableAt ℝ β.toFun τ := hτd (by rw [uIcc_of_le hst]; exact hτI)
    have hpτ : β.toFun τ ∈ unitDisc := hmaps hτI
    by_cases hFd : DifferentiableAt ℝ (fun τ => u (β.toFun τ)) τ
    swap
    · rw [deriv_zero_of_not_differentiableAt hFd, abs_zero, ENNReal.ofReal_zero]
      exact zero_le
    rw [fx_p5_density_mul]
    apply ENNReal.ofReal_le_ofReal
    by_cases hβ0 : deriv β.toFun τ = 0
    · have hb : ∀ᶠ σ in 𝓝 τ, |u (β.toFun σ) - u (β.toFun τ)| ≤
          ‖β.toFun σ * (L : ℂ) - β.toFun τ * (L : ℂ)‖ := by
        filter_upwards [hβd.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds hpτ)] with σ hσ
        rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq,
          ← dist_eq_norm, ← Real.dist_eq, mul_comm]
        exact hL.dist_le_mul _ hσ _ hpτ
      have h := fx_p5_slope_bound hFd.hasDerivAt hβd.hasDerivAt (hasDerivAt_mul_const (L : ℂ)) hb
      rw [hβ0, norm_zero, mul_zero] at h
      rw [hβ0, norm_zero, mul_zero]
      exact h
    · have hp0 : φ (β.toFun τ) ≠ 0 := fun h0 =>
        hτS (mem_biUnion (x := β.toFun τ) ⟨hpτ, h0⟩ ⟨rfl, hβd, hβ0⟩)
      obtain ⟨G, G', hG, hG2, hGb⟩ := hpug _ hpτ hp0
      have hb := hβd.continuousAt.tendsto.eventually hGb
      have h := fx_p5_slope_bound hFd.hasDerivAt hβd.hasDerivAt hG hb
      have hG' : ‖G'‖ = Real.sqrt ‖φ (β.toFun τ)‖ := by
        rw [← hG2, norm_pow, Real.sqrt_sq (norm_nonneg _)]
      rwa [hG'] at h
  have h1 : |u (β.toFun t) - u (β.toFun s)| ≤
      ∫ τ in s..t, |deriv (fun τ => u (β.toFun τ)) τ| := by
    rw [← hftc]
    exact intervalIntegral.abs_integral_le_integral_abs hst
  have h2 : ENNReal.ofReal (∫ τ in s..t, |deriv (fun τ => u (β.toFun τ)) τ|) =
      ∫⁻ τ in Ioc s t, ENNReal.ofReal |deriv (fun τ => u (β.toFun τ)) τ| := by
    rw [intervalIntegral.integral_of_le hst]
    exact ofReal_integral_eq_lintegral_ofReal hint.1.abs
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  calc ENNReal.ofReal |u (β.toFun t) - u (β.toFun s)|
      ≤ ENNReal.ofReal (∫ τ in s..t, |deriv (fun τ => u (β.toFun τ)) τ|) :=
        ENNReal.ofReal_le_ofReal h1
    _ = ∫⁻ τ in Ioc s t, ENNReal.ofReal |deriv (fun τ => u (β.toFun τ)) τ| := h2
    _ ≤ ∫⁻ τ in Ioc s t, phiDensity φ (β.toFun τ) * ‖deriv β.toFun τ‖ₑ := lintegral_mono_ae hae
    _ ≤ ∫⁻ τ in Ioo 0 1, phiDensity φ (β.toFun τ) * ‖deriv β.toFun τ‖ₑ :=
        lintegral_mono_set fun τ hτ => ⟨hs.trans hτ.1, hτ.2.trans_lt ht⟩
    _ = phiLength φ β := rfl

/-- Passing to the end points of the curve in the calibration inequality. -/
theorem fx_p5_curve_ends {φ : ℂ → ℂ} {u : ℂ → ℝ} (hucont : ContinuousOn u unitDisc)
    (β : LRCurve) (hβ : β.trace ⊆ unitDisc) {z₀ z₁ : ℂ} (h0 : z₀ ∈ unitDisc) (h1 : z₁ ∈ unitDisc)
    (hβa : Tendsto β.toFun (𝓝[>] 0) (𝓝 z₀)) (hβb : Tendsto β.toFun (𝓝[<] 1) (𝓝 z₁))
    (hsub : ∀ s t : ℝ, 0 < s → s ≤ t → t < 1 →
      ENNReal.ofReal |u (β.toFun t) - u (β.toFun s)| ≤ phiLength φ β) :
    ENNReal.ofReal |u z₁ - u z₀| ≤ phiLength φ β := by
  by_cases htop : phiLength φ β = ⊤
  · rw [htop]
    exact le_top
  have hsub' : ∀ s t : ℝ, 0 < s → s ≤ t → t < 1 →
      |u (β.toFun t) - u (β.toFun s)| ≤ (phiLength φ β).toReal := fun s t hs hst ht =>
    (ENNReal.ofReal_le_iff_le_toReal htop).1 (hsub s t hs hst ht)
  have hmem0 : ∀ᶠ τ in 𝓝[>] (0 : ℝ), β.toFun τ ∈ unitDisc := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with τ hτ
    exact hβ ⟨τ, hτ, rfl⟩
  have hmem1 : ∀ᶠ τ in 𝓝[<] (1 : ℝ), β.toFun τ ∈ unitDisc := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with τ hτ
    exact hβ ⟨τ, hτ, rfl⟩
  have hu0 : Tendsto (fun τ => u (β.toFun τ)) (𝓝[>] 0) (𝓝 (u z₀)) :=
    (hucont z₀ h0).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hβa, hmem0⟩)
  have hu1 : Tendsto (fun τ => u (β.toFun τ)) (𝓝[<] 1) (𝓝 (u z₁)) :=
    (hucont z₁ h1).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hβb, hmem1⟩)
  have hstep : ∀ s ∈ Ioo (0 : ℝ) 1, |u z₁ - u (β.toFun s)| ≤ (phiLength φ β).toReal := by
    intro s hs
    refine le_of_tendsto ((hu1.sub_const (u (β.toFun s))).abs) ?_
    filter_upwards [Ioo_mem_nhdsLT hs.2] with t ht
    exact hsub' s t hs.1 ht.1.le ht.2
  have hfin : |u z₁ - u z₀| ≤ (phiLength φ β).toReal := by
    refine le_of_tendsto ((hu0.const_sub (u z₁)).abs) ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with s hs
    exact hstep s hs
  exact (ENNReal.ofReal_le_iff_le_toReal htop).2 hfin

/-- **The geodesic property for tame `φ`** (holomorphic on a disc of radius `> 1`): the forest,
a cut choice avoiding the leaf of `c`, its calibration `u`; then
`l_φ(c) = |u(c b) - u(c a)| ≤ l_φ(β)`. -/
theorem fx_p5_arc_shortest_tame {φ : ℂ → ℂ} {ρ : ℝ} (hρ : 1 < ρ)
    (hφ : DifferentiableOn ℂ φ (ball 0 ρ)) {c : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hc : IsHorizontalArc φ c a b) (hcc : ContinuousOn c (Icc a b)) (hcD : c '' Icc a b ⊆ unitDisc)
    (β : LRCurve) (hβ : β.trace ⊆ unitDisc) (hβa : Tendsto β.toFun (𝓝[>] 0) (𝓝 (c a)))
    (hβb : Tendsto β.toFun (𝓝[<] 1) (𝓝 (c b))) :
    ∫⁻ t in Ioo a b, phiDensity φ (c t) * ‖deriv c t‖ₑ ≤ phiLength φ β := by
  have hφD : DifferentiableOn ℂ φ unitDisc := hφ.mono (ball_subset_ball hρ.le)
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hcD' : ∀ t ∈ Ioo a b, c t ∈ unitDisc := fun t ht => hcD ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  have hm0 : φ (c ((a + b) / 2)) ≠ 0 := (hc _ hm).2.2.1
  have hne : ∃ z ∈ unitDisc, φ z ≠ 0 := ⟨_, hcD' _ hm, hm0⟩
  obtain ⟨ι, hι, par, src, dst, hF⟩ := fx_vforest_exists hρ hφ hne
  obtain ⟨pick, rk, hpick, hdisj⟩ := fx_cutChoice_avoid hρ hφ hne hF (hcD' _ hm) hm0
  obtain ⟨u, Φ, hΦd, hΦu, L, hL⟩ := fx_cutCalib hρ hφ hF hpick
  have hΩo : IsOpen (unitDisc \ fx_cutSet φ par pick) := fx_p4_cut_isOpen hρ hφ hF pick
  have hcΩ : ∀ t ∈ Ioo a b, c t ∈ unitDisc \ fx_cutSet φ par pick := fun t ht =>
    ⟨hcD' t ht, fun hcut => Set.disjoint_left.1 hdisj (fx_p5_arc_leaf hφD hc hcD' hm ht) hcut⟩
  have hucont : ContinuousOn u unitDisc := hL.continuousOn
  have hcont : ContinuousOn (fun t => u (c t)) (Icc a b) :=
    hucont.comp hcc fun t ht => hcD ⟨t, ht, rfl⟩
  refine (fx_p5_arc_len hΩo hΦd (fun z hz => (hΦu z hz).1) (fun z hz => (hΦu z hz).2) hab hc
    hcΩ hcont).trans ?_
  exact fx_p5_curve_ends hucont β hβ (hcD ⟨a, left_mem_Icc.2 hab.le, rfl⟩)
    (hcD ⟨b, right_mem_Icc.2 hab.le, rfl⟩) hβa hβb fun s t hs hst ht =>
      fx_p5_curve_ineq hL hF.zeros_finite.countable
        (fun p hp hp0 => fx_p5_pug hρ hφ hF hΦd (fun z hz => (hΦu z hz).1)
          (fun z hz => (hΦu z hz).2) hucont hp hp0) β hβ hs hst ht


/-- The extension of an open curve by its end limits is continuous on `[0, 1]`. -/
theorem fx_p5_ext_continuousOn (β : LRCurve) {z₀ z₁ : ℂ}
    (hβa : Tendsto β.toFun (𝓝[>] 0) (𝓝 z₀)) (hβb : Tendsto β.toFun (𝓝[<] 1) (𝓝 z₁)) :
    ContinuousOn (fun τ : ℝ => if τ ≤ 0 then z₀ else if 1 ≤ τ then z₁ else β.toFun τ)
      (Icc 0 1) := by
  set f : ℝ → ℂ := fun τ => if τ ≤ 0 then z₀ else if 1 ≤ τ then z₁ else β.toFun τ with hf
  have heq : ∀ τ ∈ Ioo (0 : ℝ) 1, f τ = β.toFun τ := fun τ hτ => by
    simp [hf, not_le.2 hτ.1, not_le.2 hτ.2]
  have h10 : ¬ (1 : ℝ) ≤ 0 := by norm_num
  have hf0 : f 0 = z₀ := by simp [hf]
  have hf1 : f 1 = z₁ := by simp [hf, h10]
  intro τ hτ
  rcases eq_or_lt_of_le hτ.1 with h0 | h0
  · subst h0
    rw [← Ioc_insert_left zero_le_one, continuousWithinAt_insert_self, ContinuousWithinAt, hf0]
    have hev : β.toFun =ᶠ[𝓝[>] 0] f := by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with σ hσ
      exact (heq σ hσ).symm
    exact (hβa.congr' hev).mono_left (nhdsWithin_mono _ Ioc_subset_Ioi_self)
  rcases eq_or_lt_of_le hτ.2 with h1 | h1
  · subst h1
    rw [← Ico_insert_right zero_le_one, continuousWithinAt_insert_self, ContinuousWithinAt, hf1]
    have hev : β.toFun =ᶠ[𝓝[<] 1] f := by
      filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with σ hσ
      exact (heq σ hσ).symm
    exact (hβb.congr' hev).mono_left (nhdsWithin_mono _ Ico_subset_Iio_self)
  have hβc : ContinuousAt β.toFun τ :=
    β.locallyLipschitzOn.continuousOn.continuousAt (Ioo_mem_nhds h0 h1)
  have hev : β.toFun =ᶠ[𝓝 τ] f := by
    filter_upwards [Ioo_mem_nhds h0 h1] with σ hσ
    exact (heq σ hσ).symm
  exact (hβc.congr hev).continuousWithinAt

/-- Rescaling: `|ψ|^{1/2} |dz|` is invariant under `ψ(w) = r² φ(r w)` and `z ↦ z / r`. -/
theorem fx_p5_density_rescale (φ : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (z v : ℂ) :
    phiDensity (fun w => (r : ℂ) ^ 2 * φ ((r : ℂ) * w)) ((r : ℂ)⁻¹ * z) * ‖(r : ℂ)⁻¹ * v‖ₑ =
      phiDensity φ z * ‖v‖ₑ := by
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr.ne'
  rw [fx_p5_density_mul, fx_p5_density_mul]
  congr 1
  simp only [← mul_assoc, mul_inv_cancel₀ hrC, one_mul]
  simp only [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
  field_simp

/-- **(Optional) Horizontal arcs are shortest**: a horizontal arc `c|[a, b]` in `Δ` is no longer than
any curve in `Δ` joining its end points.  (The left side is S35's `rayLength φ c a b`, unfolded.)
(Rescale to a disc `Δ_r ⊇ trace β ∪ c[a, b]` where `φ` is tame, and apply a cut calibration avoiding
the leaf of `c`.)  With `circular_arcs_short` it gives
`lemma35_3` and `lemma35_2` (in S35). -/
theorem fx_arc_shortest {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ unitDisc)
    (hne : ∃ z ∈ unitDisc, φ z ≠ 0) {c : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hc : IsHorizontalArc φ c a b) (hcc : ContinuousOn c (Icc a b)) (hcD : c '' Icc a b ⊆ unitDisc)
    (β : LRCurve) (hβ : β.trace ⊆ unitDisc) (hβa : Tendsto β.toFun (𝓝[>] 0) (𝓝 (c a)))
    (hβb : Tendsto β.toFun (𝓝[<] 1) (𝓝 (c b))) :
    ∫⁻ t in Ioo a b, phiDensity φ (c t) * ‖deriv c t‖ₑ ≤ phiLength φ β := by
  have _ := hne
  -- a disc `Δ_r`, `r < 1`, containing `c [a, b]` and the closure of the trace of `β`
  set βe : ℝ → ℂ := fun τ => if τ ≤ 0 then c a else if 1 ≤ τ then c b else β.toFun τ with hβe
  have hβec : ContinuousOn βe (Icc 0 1) := fx_p5_ext_continuousOn β hβa hβb
  have hcaD : c a ∈ unitDisc := hcD ⟨a, left_mem_Icc.2 hab.le, rfl⟩
  have hcbD : c b ∈ unitDisc := hcD ⟨b, right_mem_Icc.2 hab.le, rfl⟩
  have hβeq : ∀ τ ∈ Ioo (0 : ℝ) 1, βe τ = β.toFun τ := fun τ hτ => by
    simp [hβe, not_le.2 hτ.1, not_le.2 hτ.2]
  have hK : IsCompact (c '' Icc a b ∪ βe '' Icc 0 1) :=
    (isCompact_Icc.image_of_continuousOn hcc).union (isCompact_Icc.image_of_continuousOn hβec)
  have hKD : c '' Icc a b ∪ βe '' Icc 0 1 ⊆ ball (0 : ℂ) 1 := by
    rintro z (hz | ⟨τ, hτ, rfl⟩)
    · exact hcD hz
    by_cases h0 : τ ≤ 0
    · have e : βe τ = c a := by simp [hβe, h0]
      rw [e]
      exact hcaD
    by_cases h1 : 1 ≤ τ
    · have e : βe τ = c b := by simp [hβe, h0, h1]
      rw [e]
      exact hcbD
    rw [hβeq τ ⟨not_le.1 h0, not_le.1 h1⟩]
    exact hβ ⟨τ, ⟨not_le.1 h0, not_le.1 h1⟩, rfl⟩
  obtain ⟨r, hr1, hKr⟩ := exists_lt_subset_ball hK.isClosed hKD
  have hcK : ∀ t ∈ Icc a b, ‖c t‖ < r := fun t ht =>
    mem_ball_zero_iff.1 (hKr (Or.inl ⟨t, ht, rfl⟩))
  have hβK : ∀ τ ∈ Ioo (0 : ℝ) 1, ‖β.toFun τ‖ < r := fun τ hτ => by
    have h := hKr (Or.inr ⟨τ, Ioo_subset_Icc_self hτ, rfl⟩)
    rw [hβeq τ hτ] at h
    exact mem_ball_zero_iff.1 h
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) (hcK a (left_mem_Icc.2 hab.le))
  have hrC : (r : ℂ) ≠ 0 := ofReal_ne_zero.2 hr0.ne'
  have hsmall : ∀ z : ℂ, ‖z‖ < r → (r : ℂ)⁻¹ * z ∈ unitDisc := fun z hz => by
    show _ ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0]
    calc r⁻¹ * ‖z‖ < r⁻¹ * r := mul_lt_mul_of_pos_left hz (inv_pos.2 hr0)
      _ = 1 := inv_mul_cancel₀ hr0.ne'
  -- the rescaled (tame) quadratic differential `ψ(w) = r² φ(r w)` on `ball 0 r⁻¹`
  have hρ : 1 < r⁻¹ := (one_lt_inv₀ hr0).2 hr1
  have hψd : DifferentiableOn ℂ (fun w => (r : ℂ) ^ 2 * φ ((r : ℂ) * w)) (ball 0 r⁻¹) := by
    have hmaps : MapsTo (fun w : ℂ => (r : ℂ) * id w) (ball 0 r⁻¹) unitDisc := by
      intro w hw
      show (r : ℂ) * w ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff] at hw ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
      calc r * ‖w‖ < r * r⁻¹ := mul_lt_mul_of_pos_left hw hr0
        _ = 1 := mul_inv_cancel₀ hr0.ne'
    exact (hφ.comp (differentiableOn_id.const_mul (r : ℂ)) hmaps).const_mul _
  -- the rescaled arc
  have hdcr : ∀ t, deriv (fun t => (r : ℂ)⁻¹ * c t) t = (r : ℂ)⁻¹ * deriv c t := fun t =>
    deriv_const_mul_field _
  have hcr : IsHorizontalArc (fun w => (r : ℂ) ^ 2 * φ ((r : ℂ) * w))
      (fun t => (r : ℂ)⁻¹ * c t) a b := by
    intro t ht
    obtain ⟨hd, hd0, hφ0, him, hre⟩ := hc t ht
    have hval : (r : ℂ) ^ 2 * φ ((r : ℂ) * ((r : ℂ)⁻¹ * c t)) = (r : ℂ) ^ 2 * φ (c t) := by
      rw [← mul_assoc (r : ℂ), mul_inv_cancel₀ hrC, one_mul]
    have hkey : (r : ℂ) ^ 2 * φ ((r : ℂ) * ((r : ℂ)⁻¹ * c t)) * ((r : ℂ)⁻¹ * deriv c t) ^ 2 =
        φ (c t) * deriv c t ^ 2 := by
      rw [hval]
      field_simp
    refine ⟨hd.const_mul _, ?_, ?_, ?_, ?_⟩
    · rw [hdcr]
      exact mul_ne_zero (inv_ne_zero hrC) hd0
    · show (r : ℂ) ^ 2 * φ ((r : ℂ) * ((r : ℂ)⁻¹ * c t)) ≠ 0
      rw [hval]
      exact mul_ne_zero (pow_ne_zero 2 hrC) hφ0
    · rw [hdcr]
      show ((r : ℂ) ^ 2 * φ ((r : ℂ) * ((r : ℂ)⁻¹ * c t)) * ((r : ℂ)⁻¹ * deriv c t) ^ 2).im = 0
      rw [hkey]
      exact him
    · rw [hdcr]
      show 0 < ((r : ℂ) ^ 2 * φ ((r : ℂ) * ((r : ℂ)⁻¹ * c t)) * ((r : ℂ)⁻¹ * deriv c t) ^ 2).re
      rw [hkey]
      exact hre
  have hcrc : ContinuousOn (fun t => (r : ℂ)⁻¹ * c t) (Icc a b) := continuousOn_const.mul hcc
  have hcrD : (fun t => (r : ℂ)⁻¹ * c t) '' Icc a b ⊆ unitDisc := by
    rintro _ ⟨t, ht, rfl⟩
    exact hsmall _ (hcK t ht)
  -- the rescaled curve
  have hLip : LipschitzWith ‖(r : ℂ)⁻¹‖₊ (fun z : ℂ => (r : ℂ)⁻¹ * z) := by
    simpa only [smul_eq_mul] using lipschitzWith_smul (β := ℂ) ((r : ℂ)⁻¹)
  have hβrL : LocallyLipschitzOn (Ioo 0 1) (fun τ => (r : ℂ)⁻¹ * β.toFun τ) := by
    intro τ hτ
    obtain ⟨K', t', ht', hK'⟩ := β.locallyLipschitzOn hτ
    exact ⟨_, t', ht', hLip.comp_lipschitzOnWith hK'⟩
  have hβrD : (LRCurve.mk _ hβrL).trace ⊆ unitDisc := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact hsmall _ (hβK τ hτ)
  have hβra : Tendsto (LRCurve.mk _ hβrL).toFun (𝓝[>] 0) (𝓝 ((r : ℂ)⁻¹ * c a)) :=
    hβa.const_mul _
  have hβrb : Tendsto (LRCurve.mk _ hβrL).toFun (𝓝[<] 1) (𝓝 ((r : ℂ)⁻¹ * c b)) :=
    hβb.const_mul _
  have key := fx_p5_arc_shortest_tame hρ hψd hab hcr hcrc hcrD (LRCurve.mk _ hβrL) hβrD hβra hβrb
  have hLHS : ∫⁻ t in Ioo a b, phiDensity φ (c t) * ‖deriv c t‖ₑ =
      ∫⁻ t in Ioo a b, phiDensity (fun w => (r : ℂ) ^ 2 * φ ((r : ℂ) * w)) ((r : ℂ)⁻¹ * c t) *
        ‖deriv (fun t => (r : ℂ)⁻¹ * c t) t‖ₑ := by
    refine lintegral_congr fun t => ?_
    rw [hdcr, fx_p5_density_rescale φ hr0]
  have hRHS : phiLength (fun w => (r : ℂ) ^ 2 * φ ((r : ℂ) * w)) (LRCurve.mk _ hβrL) =
      phiLength φ β := by
    simp only [phiLength, LRCurve.rhoLength]
    refine lintegral_congr fun τ => ?_
    rw [deriv_const_mul_field, fx_p5_density_rescale φ hr0]
  rw [hLHS, ← hRHS]
  exact key

end LiZhongQC

end
