import LiZhongQC.Ch06.S23_QCOnSurfaces
import LiZhongQC.Ch05.S21_UniversalTeichmuller

/-!
# §24 拟 Fuchs 群与同时单值化定理 — Quasi-Fuchsian groups and simultaneous uniformization

* Definition (§24.1): quasi-Fuchsian groups of the first and second kind — `IsQuasiFuchsian`
* deformations `Γ_μ = f_μ Γ f_μ⁻¹` of Fuchsian groups are quasi-Fuchsian — `fuchsian_deformation`
* every homotopy class of orientation preserving homeomorphisms of closed surfaces of the same
  genus contains a quasiconformal map                                    — `exists_qc_in_homotopy_class`
* Theorem 24.1 (Bers: simultaneous uniformization)                       — `thm24_1_simultaneous_uniformization`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u v

/-- **Definition** (§24.1, 拟 Fuchs 群).  A Klein group `Γ` is quasi-Fuchsian with invariant Jordan
curve `C` if every element maps `C` onto itself and each complementary component of `C` onto
itself.  It is of the first kind if `Λ(Γ) = C`, of the second kind otherwise. -/
def IsQuasiFuchsian (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) (C : Set ExtPlane) : Prop :=
  IsKleinGroup Γ ∧ IsJordanCurve C ∧ ∀ γ ∈ Γ, mobiusSL γ '' C = C ∧
    ∀ p ∈ Cᶜ, mobiusSL γ '' connectedComponentIn Cᶜ p = connectedComponentIn Cᶜ p

/-- A quasi-Fuchsian group of the first kind. -/
def IsQuasiFuchsianFirstKind (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) (C : Set ExtPlane) :
    Prop :=
  IsQuasiFuchsian Γ C ∧ limitSet Γ = C

/-- The embedding `SL(2, ℝ) → SL(2, ℂ)`. -/
def slRealToComplex (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℂ :=
  Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ

/-- A Beltrami coefficient `μ` on `ℍ` compatible with the Fuchsian group `Γ` (a lift of a Beltrami
differential of `ℍ/Γ`): `μ(z) = μ(γz) conj(γ'(z))/γ'(z)` a.e. for `γ ∈ Γ`. -/
def IsGammaCompatible (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (μ : ℂ → ℂ) : Prop :=
  ∀ γ ∈ Γ, ∀ᵐ z ∂(volume.restrict upperHalf),
    μ z = μ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) *
      (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2))

/-! ### s24k track (coordinator 553e2d): `fuchsian_deformation` -/

/-! ### s24k F1: the relation `f̂_μ ∘ γ̂ = γ̂_μ ∘ f̂_μ` on `ℂ̄` and the invariant quasicircle -/

/-! #### The MOB core (copied from S33: `bg_ae_of_halves`, `bg2_d_*`, `bg2_dil_comp`, `bg2_m1_*`,
`b33_e_normalize`, `b33_e_mob_core`) -/

/-- A property which holds a.e. on `ℍ` and a.e. on `𝕃` holds a.e. on `ℂ` (the real axis is null). -/
theorem k24_ae_of_halves {p : ℂ → Prop} (hU : ∀ᵐ z ∂(volume.restrict upperHalf), p z)
    (hL : ∀ᵐ z ∂(volume.restrict lowerHalf), p z) : ∀ᵐ z, p z := by
  have hnull : ∀ᵐ z : ℂ, z ∉ {w : ℂ | w.im = 0} :=
    measure_eq_zero_iff_ae_notMem.1 gzE_volume_im_eq_zero
  rw [ae_restrict_iff' isOpen_upperHalf.measurableSet] at hU
  rw [ae_restrict_iff' isOpen_lowerHalf.measurableSet] at hL
  filter_upwards [hU, hL, hnull] with z h1 h2 h3
  rcases lt_or_gt_of_ne (h3 : z.im ≠ 0) with h | h
  · exact h2 h
  · exact h1 h

/-- The derivative of `z ↦ (a z + b)/(c z + d)` with `a d - b c = 1` off its pole is `1/(c z + d)²`. -/
theorem k24_d_deriv {a b c d : ℂ} (h : a * d - b * c = 1) {z : ℂ} (hz : c * z + d ≠ 0) :
    HasDerivAt (mobiusFn a b c d) (1 / (c * z + d) ^ 2) z := by
  have h1 : HasDerivAt (fun y : ℂ => a * y + b) a z := by
    simpa using ((hasDerivAt_id' z).const_mul a).add_const b
  have h2 : HasDerivAt (fun y : ℂ => c * y + d) c z := by
    simpa using ((hasDerivAt_id' z).const_mul c).add_const d
  have h3 := h1.fun_div h2 hz
  have he : a * (c * z + d) - (a * z + b) * c = 1 := by rw [← h]; ring
  rw [he] at h3
  exact h3

/-- The complex dilatation of `g ∘ T` for `T z = (a z + b)/(c z + d)` with `a d - b c = 1`, off the pole:
`μ_{g ∘ T}(z) = μ_g(T z) (c z + d)²/conj (c z + d)²`. -/
theorem k24_d_dil_mobius (g : ℂ → ℂ) {a b c d : ℂ} (h : a * d - b * c = 1) {z : ℂ} (hz : c * z + d ≠ 0) :
    complexDilatation (g ∘ mobiusFn a b c d) z =
      complexDilatation g (mobiusFn a b c d z) * ((c * z + d) ^ 2 / conj ((c * z + d) ^ 2)) := by
  have hne : a * d - b * c ≠ 0 := by rw [h]; exact one_ne_zero
  have hne' : d * a - -b * -c ≠ 0 := by rw [show d * a - -b * -c = a * d - b * c by ring]; exact hne
  have hT := k24_d_deriv h hz
  have hden : -c * mobiusFn a b c d z + a ≠ 0 := mobiusFn_inv_den_ne_zero hne hz
  have hS : DifferentiableAt ℂ (mobiusFn d (-b) (-c) a) (mobiusFn a b c d z) := by
    show DifferentiableAt ℂ (fun w => (d * w + -b) / (-c * w + a)) (mobiusFn a b c d z)
    exact DifferentiableAt.fun_div (by fun_prop) (by fun_prop) hden
  have hST : ∀ᶠ w in 𝓝 z, mobiusFn d (-b) (-c) a (mobiusFn a b c d w) = w := by
    have hc : Continuous fun w : ℂ => c * w + d := by fun_prop
    filter_upwards [hc.continuousAt.eventually_ne hz] with w hw
    exact mobiusFn_inv_apply hne hw
  have hTS : ∀ᶠ u in 𝓝 (mobiusFn a b c d z), mobiusFn a b c d (mobiusFn d (-b) (-c) a u) = u := by
    have hc : Continuous fun u : ℂ => -c * u + a := by fun_prop
    filter_upwards [hc.continuousAt.eventually_ne hden] with u hu
    have h' := mobiusFn_inv_apply hne' hu
    simpa only [neg_neg] using h'
  rw [s23_dilatation_comp_right hT.differentiableAt hS hST hTS, hT.deriv]
  congr 1
  have hsq : (c * z + d) ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have hsq' : conj ((c * z + d) ^ 2) ≠ 0 := (map_ne_zero _).2 hsq
  rw [map_div₀, map_one]
  field_simp

/-- `μ_{f_μ} = μ` a.e. pulls back through a Möbius transformation `T` (`a d - b c ≠ 0`) on an open set `U` free of its
pole: `μ_{f_μ}(T z) = μ(T z)` for a.e. `z ∈ U`. -/
theorem k24_d_pullback (μ : BeltramiH) {a b c d : ℂ} (h : a * d - b * c ≠ 0) {U : Set ℂ} (hU : IsOpen U)
    (hpole : ∀ z ∈ U, c * z + d ≠ 0) :
    ∀ᵐ z ∂(volume.restrict U),
      complexDilatation (normalizedSolution μ.1) (mobiusFn a b c d z) = μ.1 (mobiusFn a b c d z) := by
  have hconf : IsConformalOnto (mobiusFn a b c d) U (mobiusFn a b c d '' U) := by
    refine ⟨fun z hz => ?_, fun z₁ hz₁ z₂ hz₂ heq => ?_, rfl⟩
    · have hd : DifferentiableAt ℂ (fun w => (a * w + b) / (c * w + d)) z :=
        DifferentiableAt.fun_div (by fun_prop) (by fun_prop) (hpole z hz)
      exact hd.differentiableWithinAt
    · rw [← mobiusFn_inv_apply h (hpole z₁ hz₁), ← mobiusFn_inv_apply h (hpole z₂ hz₂), heq]
  have hae : ∀ᵐ u ∂(volume.restrict univ), complexDilatation (normalizedSolution μ.1) u = μ.1 u := by
    rw [Measure.restrict_univ]
    exact (ut_spec μ).2.2.2.2
  exact s23_c2_ae_pullback (P := fun u => complexDilatation (normalizedSolution μ.1) u = μ.1 u)
    (isKQC_one_of_conformal hU hconf) (subset_univ _) hae

/-- **D** (the dilatation of `f_μ ∘ γ`): for a `Γ`-compatible `μ ∈ M` and `γ ∈ Γ`, `μ_{f_μ ∘ γ} = μ` a.e.  On `ℍ` by
`Γ`-compatibility, on `𝕃` both sides vanish (`γ(𝕃) ⊆ 𝕃`), and `ℝ` is null. -/
theorem k24_dil_comp {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : BeltramiH)
    (hμ : IsGammaCompatible Γ μ.1) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) :
    ∀ᵐ z, complexDilatation (normalizedSolution μ.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z = μ.1 z := by
  have hdetR : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdetR
  have hne : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 ≠ 0 := by rw [hdet]; exact one_ne_zero
  have hpole : ∀ z : ℂ, z.im ≠ 0 → (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := fun z hz => k24_d_den_ne_zero hdetR hz
  refine k24_ae_of_halves ?_ ?_
  · filter_upwards [k24_d_pullback μ hne isOpen_upperHalf fun z hz => hpole z (show 0 < z.im from hz).ne',
      hμ γ hγ, ae_restrict_mem isOpen_upperHalf.measurableSet] with z h1 h2 hz
    rw [k24_d_dil_mobius _ hdet (hpole z (show 0 < z.im from hz).ne'), h1]
    exact h2.symm
  · filter_upwards [k24_d_pullback μ hne isOpen_lowerHalf fun z hz => hpole z (show z.im < 0 from hz).ne,
      ae_restrict_mem isOpen_lowerHalf.measurableSet] with z h1 hz
    have hz' : z.im < 0 := hz
    have hTz : (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z).im ≤ 0 := by
      rw [mobiusFn_im_real, hdetR, one_mul]
      exact div_nonpos_of_nonpos_of_nonneg hz'.le (Complex.normSq_nonneg _)
    rw [k24_d_dil_mobius _ hdet (hpole z hz'.ne), h1, μ.2.2 _ hTz, μ.2.2 z hz'.le, zero_mul]

/-- Normalization: a `K`-q.c. self-map `G` of the plane with the dilatation `τ` of a normalized solution `g` a.e.
satisfies `g = (G - G 0)/(G 1 - G 0)` (`thm13_5_uniqueness_plane`). -/
theorem k24_normalize {g τ G : ℂ → ℂ} {K : ℝ} (hg : IsNormalizedSolution g τ) (hG : IsKQC G univ K)
    (hs : G '' univ = univ) (hd : ∀ᵐ z, complexDilatation G z = τ z) :
    ∀ z, g z = (G z - G 0) / (G 1 - G 0) := by
  have ha : G 1 - G 0 ≠ 0 := fun h =>
    one_ne_zero (hG.2.2.1.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
  obtain ⟨hK, hs'⟩ := bB_l_affine_isKQC hG hs (G 0) ha
  have hGc : Continuous G := continuousOn_univ.1 hG.2.2.1.1
  have hdil : ∀ z, complexDilatation (fun ζ => (G ζ - G 0) / (G 1 - G 0)) z = complexDilatation G z := by
    intro z
    exact s23_dilatation_comp_left (g := G) (z := z) (h := fun w => (w - G 0) / (G 1 - G 0))
      (k := fun u => (G 1 - G 0) * u + G 0) hGc.continuousAt (by fun_prop) (by fun_prop)
      (Eventually.of_forall fun w => by field_simp; ring)
  obtain ⟨hq, hsq, hq0, hq1, hgd⟩ := hg
  have heq := thm13_5_uniqueness_plane hq ⟨K, hK⟩ hsq hs' ?_ hq0 hq1 (by simp) (by simp [div_self ha])
  · exact fun z => congrFun heq z
  · filter_upwards [hgd, hd] with z h1 h2
    rw [h1, hdil z, h2]

/-- The inversion conjugate `z ↦ 1/(f(p + q/(z + r)) - f(p))` (`q ≠ 0`) of a `K`-q.c. map `f` of the plane onto itself
is a
homeomorphism of the plane onto itself (`nxI1_exists_homeo`). -/
theorem k24_m1_isHomeomorphOnto {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hs : f '' univ = univ)
    (p q r : ℂ) (hq : q ≠ 0) :
    IsHomeomorphOnto (fun z : ℂ => (f (p + q * (z + r)⁻¹) - f p)⁻¹) univ univ := by
  obtain ⟨e, rfl⟩ := t1_homeomorph hf hs
  set e₁ : ℂ ≃ₜ ℂ := ((Homeomorph.mulLeft₀ q hq).trans (Homeomorph.addLeft p)).trans
    (e.trans (Homeomorph.subRight (e p))) with he₁
  have h0 : e₁ 0 = 0 := by simp [he₁]
  obtain ⟨E, hE⟩ := nxI1_exists_homeo e₁ h0
  have hG : ⇑((Homeomorph.addRight r).trans E) = fun z : ℂ => (e (p + q * (z + r)⁻¹) - e p)⁻¹ := by
    funext z
    simp [hE, nxInvConj, he₁]
  rw [← hG]
  exact nxI1_isHomeomorphOnto_of_homeomorph _

/-- The inversion conjugate `z ↦ 1/(f(p + q/(z + r)) - f(p))` (`q ≠ 0`) of a `K`-q.c. map `f` of the plane is `K`-q.c.
off
the pole `-r`. -/
theorem k24_m1_isKQC {f : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (p q r : ℂ) (hq : q ≠ 0) :
    IsKQC (fun z : ℂ => (f (p + q * (z + r)⁻¹) - f p)⁻¹) {-r}ᶜ K := by
  have hT : IsKQC (fun z : ℂ => p + q * (z + r)⁻¹) {-r}ᶜ 1 := by
    refine isKQC_one_of_conformal (D' := (fun z : ℂ => p + q * (z + r)⁻¹) '' {-r}ᶜ)
      isOpen_compl_singleton ⟨fun z hz => ?_, fun a _ b _ hab => ?_, rfl⟩
    · have h1 : z + r ≠ 0 := fun h => hz (mem_singleton_iff.mpr (eq_neg_of_add_eq_zero_left h))
      have h2 : DifferentiableAt ℂ (fun w : ℂ => p + q * (w + r)⁻¹) z := by fun_prop (disch := exact h1)
      exact h2.differentiableWithinAt
    · exact add_right_cancel (inv_injective (mul_left_cancel₀ hq (add_left_cancel hab)))
  have h1 := thm7_1_comp hT hf (subset_univ _)
  have hsub : (f ∘ fun z : ℂ => p + q * (z + r)⁻¹) '' {-r}ᶜ ⊆ {f p}ᶜ := by
    rintro _ ⟨z, hz, rfl⟩ h
    have heq := hf.2.2.1.2.1 (mem_univ _) (mem_univ _) (mem_singleton_iff.mp h)
    rw [add_eq_left, mul_eq_zero, inv_eq_zero] at heq
    rcases heq with h0 | h0
    · exact hq h0
    · exact hz (mem_singleton_iff.mpr (eq_neg_of_add_eq_zero_left h0))
  have h2 := thm7_1_comp h1 (b4_qc_invShift_isKQC (f p)) hsub
  rw [one_mul, mul_one] at h2
  exact h2

/-- The pole of `γ` (`c ≠ 0`): `c z + d = 0` iff `z = -d/c`. -/
theorem k24_m1_pole_iff {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : γ 1 0 ≠ 0) (z : ℂ) :
    (γ 1 0 : ℂ) * z + γ 1 1 = 0 ↔ z = -((γ 1 1 : ℂ) / γ 1 0) := by
  have hc' : (γ 1 0 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- `γ z = a/c - (1/c²)/(z + d/c)` off the pole `-d/c` of `γ` (`c ≠ 0`, `ad - bc = 1`). -/
theorem k24_m1_mobius_eq {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : γ 1 0 ≠ 0) {z : ℂ}
    (hz : z ≠ -((γ 1 1 : ℂ) / γ 1 0)) :
    mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z =
      (γ 0 0 : ℂ) / γ 1 0 + -((γ 1 0 : ℂ) ^ 2)⁻¹ * (z + (γ 1 1 : ℂ) / γ 1 0)⁻¹ := by
  have hc' : (γ 1 0 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := fun h => hz ((k24_m1_pole_iff hc z).1 h)
  have hzr : z + (γ 1 1 : ℂ) / γ 1 0 = ((γ 1 0 : ℂ) * z + γ 1 1) / γ 1 0 := by
    field_simp
  have hden' : z * (γ 1 0 : ℂ) + γ 1 1 ≠ 0 := by rwa [mul_comm]
  rw [mobiusFn, hzr, inv_div]
  field_simp
  linear_combination -hdet

/-- **MOB core** (generic, after `b33_e_mob_core`): let `f` be a `K`-q.c. map of the plane onto itself with `f 0 = 0`
such that `f ∘ γ` has a.e. the dilatation `τ` of a normalized solution `g`.  Then `f ∘ γ = M ∘ g` on all of `ℂ` for a
Möbius `M = (A, B, C, D)` (at the pole of `γ` both sides are Lean's `0`). -/
theorem k24_mob_core {f g τ : ℂ → ℂ} {K : ℝ} (hf : IsKQC f univ K) (hfs : f '' univ = univ) (hf0 : f 0 = 0)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hd : ∀ᵐ z, complexDilatation (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z = τ z)
    (hg : IsNormalizedSolution g τ) :
    ∃ A B C D : ℂ, A * D - B * C ≠ 0 ∧
      ∀ z : ℂ, f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = mobiusFn A B C D (g z) := by
  have hdetR : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  rcases eq_or_ne (γ 1 0) 0 with hc | hc
  · -- the affine case
    have hdet1 := hdetR
    rw [hc, mul_zero, sub_zero] at hdet1
    have h00 : (γ 0 0 : ℂ) ≠ 0 := by
      rw [ofReal_ne_zero]
      rintro h
      rw [h, zero_mul] at hdet1
      exact zero_ne_one hdet1
    have h11 : (γ 1 1 : ℂ) ≠ 0 := by
      rw [ofReal_ne_zero]
      rintro h
      rw [h, mul_zero] at hdet1
      exact zero_ne_one hdet1
    have hT : mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) =
        fun u => (u - (-(γ 0 1 : ℂ) / γ 0 0)) / ((γ 1 1 : ℂ) / γ 0 0) := by
      funext u
      simp only [mobiusFn, hc, ofReal_zero, zero_mul, zero_add]
      field_simp
      ring
    have hTc : IsConformalOnto (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) univ univ := by
      rw [hT]
      exact nxE_affine_isConformalOnto (div_ne_zero h11 h00)
    have hG := thm7_1_comp (isKQC_one_of_conformal isOpen_univ hTc) hf (subset_univ _)
    have hs : (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) '' univ = univ := by
      rw [image_comp, hTc.2.2, hfs]
    have hN := k24_normalize hg hG hs hd
    set G := f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) with hGdef
    have hΔ : G 1 - G 0 ≠ 0 := fun h =>
      one_ne_zero (hG.2.2.1.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
    refine ⟨G 1 - G 0, G 0, 0, 1, by simpa using hΔ, fun z => ?_⟩
    show G z = ((G 1 - G 0) * g z + G 0) / (0 * g z + 1)
    rw [hN z, zero_mul, zero_add, div_one, mul_div_cancel₀ _ hΔ, sub_add_cancel]
  · -- the pole case, with the pole itself
    have hs := hfs
    have hc' : (γ 1 0 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
    obtain ⟨p, hp⟩ : ∃ p : ℂ, p = (γ 0 0 : ℂ) / γ 1 0 := ⟨_, rfl⟩
    obtain ⟨q, hq'⟩ : ∃ q : ℂ, q = -((γ 1 0 : ℂ) ^ 2)⁻¹ := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r : ℂ, r = (γ 1 1 : ℂ) / γ 1 0 := ⟨_, rfl⟩
    have hq : q ≠ 0 := by
      rw [hq']
      exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hc'))
    have hM : ∀ z : ℂ, z ≠ -r → mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z = p + q * (z + r)⁻¹ := by
      intro z hz
      subst hp hq' hr
      exact k24_m1_mobius_eq hc hz
    have hpole : ∀ z : ℂ, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 ↔ z ≠ -r := by
      intro z
      rw [hr]
      exact not_congr (k24_m1_pole_iff hc z)
    obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, G = fun z => (f (p + q * (z + r)⁻¹) - f p)⁻¹ := ⟨_, rfl⟩
    have hGh : IsHomeomorphOnto G univ univ := hG ▸ k24_m1_isHomeomorphOnto hf hs p q r hq
    have hGK : IsKQC G univ K := b4_isKQC_univ_of_punctured hGh (hG ▸ k24_m1_isKQC hf p q r hq)
    have hfc : Continuous f := continuousOn_univ.1 hf.2.2.1.1
    have hfi : Function.Injective f := fun a b hab => hf.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
    have hne : ∀ z : ℂ, z ≠ -r → f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) - f p ≠ 0 := by
      intro z hz h
      have h1 := hfi (sub_eq_zero.1 h)
      rw [hM z hz, add_eq_left, mul_eq_zero, inv_eq_zero] at h1
      rcases h1 with h0 | h0
      · exact hq h0
      · exact hz (eq_neg_of_add_eq_zero_left h0)
    have hGd : ∀ᵐ z, complexDilatation G z = τ z := by
      filter_upwards [hd, compl_mem_ae_iff.mpr (measure_singleton (-r))] with z h1 h2
      have hz : z ≠ -r := h2
      rw [← h1]
      have heq : EqOn G ((fun w => (w - f p)⁻¹) ∘ (f ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1))) {-r}ᶜ := by
        intro w hw
        simp only [hG, Function.comp_apply, hM w hw]
      rw [abR_t_complexDilatation_congr isOpen_compl_singleton heq h2]
      have hden : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 := (hpole z).2 hz
      have hMc : ContinuousAt (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z := by
        unfold mobiusFn
        exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
          ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hden
      refine s23_dilatation_comp_left (k := fun u => f p + u⁻¹) (hfc.continuousAt.comp hMc) ?_ ?_ ?_
      · exact (differentiableAt_id.sub (differentiableAt_const _)).inv (hne z hz)
      · exact (differentiableAt_const _).add (differentiableAt_id.inv (inv_ne_zero (hne z hz)))
      · exact Eventually.of_forall fun w => by
          simp only [inv_inv]
          ring
    have hnorm : ∀ z, g z = (G z - G 0) / (G 1 - G 0) := k24_normalize hg hGK hGh.2.2.1 hGd
    have hΔ : G 1 - G 0 ≠ 0 := fun h =>
      one_ne_zero (hGh.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
    have hGg : ∀ z, (G 1 - G 0) * g z + G 0 = G z := fun z => by
      rw [hnorm z]
      field_simp
      ring
    refine ⟨f p * (G 1 - G 0), f p * G 0 + 1, G 1 - G 0, G 0, ?_, fun z => ?_⟩
    · intro h
      apply hΔ
      linear_combination -h
    · by_cases hz' : z = -r
      · -- the pole: both sides are Lean's `0`
        have hden : (γ 1 0 : ℂ) * z + γ 1 1 = 0 := by
          by_contra h
          exact ((hpole z).1 h) hz'
        have hGr : G z = 0 := by
          rw [hG]
          show (f (p + q * (z + r)⁻¹) - f p)⁻¹ = 0
          rw [hz', neg_add_cancel, inv_zero, mul_zero, add_zero, sub_self, inv_zero]
        rw [mobiusFn, hden, div_zero, hf0, mobiusFn, hGg z, hGr, div_zero]
      · have hGz : G z = (f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) - f p)⁻¹ := by
          simp only [hG, hM z hz']
        have hnum : f p * (G 1 - G 0) * g z + (f p * G 0 + 1) = f p * ((G 1 - G 0) * g z + G 0) + 1 := by
          ring
        show f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
          (f p * (G 1 - G 0) * g z + (f p * G 0 + 1)) / ((G 1 - G 0) * g z + G 0)
        rw [hnum, hGg z, hGz]
        have := hne z hz'
        field_simp
        ring

/-! #### Fractional linear transformations of `ℂ̄`: composition, scaling, the real case -/

/-- The entries of `slRealToComplex γ` are the (coerced) entries of `γ`. -/
theorem k24_slReal_apply (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (i j : Fin 2) :
    slRealToComplex γ i j = (γ i j : ℂ) := by
  simp [slRealToComplex]

/-- `mobiusSL` of an embedded real matrix is the real fractional linear transformation. -/
theorem k24_mobiusSL_real (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    mobiusSL (slRealToComplex γ) = mobiusExt (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) := by
  simp only [mobiusSL, k24_slReal_apply]

/-- The determinant of `g ∈ SL(2, ℂ)` in coordinates. -/
theorem k24_det_SL (g : Matrix.SpecialLinearGroup (Fin 2) ℂ) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe g
  rwa [Matrix.det_fin_two] at h

/-- The determinant of `γ ∈ SL(2, ℝ)` in (complex) coordinates. -/
theorem k24_det_real (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

/-- Composition of fractional linear transformations of `ℂ̄` is given by the matrix product (the inner one
invertible). -/
theorem k24_mobiusExt_comp {a b c d a' b' c' d' : ℂ} (h' : a' * d' - b' * c' ≠ 0) (p : ExtPlane) :
    mobiusExt a b c d (mobiusExt a' b' c' d' p) =
      mobiusExt (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') p := by
  induction p using OnePoint.rec with
  | infty =>
    by_cases hc' : c' = 0
    · have ha' : a' ≠ 0 := by
        rintro rfl
        apply h'
        simp [hc']
      rw [mobiusExt_infty_of_eq hc']
      by_cases hc : c = 0
      · rw [mobiusExt_infty_of_eq hc, mobiusExt_infty_of_eq (by simp [hc, hc'])]
      · have hne : c * a' + d * c' ≠ 0 := by
          rw [hc', mul_zero, add_zero]
          exact mul_ne_zero hc ha'
        rw [mobiusExt_infty_of_ne hc, mobiusExt_infty_of_ne hne]
        congr 1
        rw [div_eq_div_iff hc hne, hc']
        ring
    · rw [mobiusExt_infty_of_ne hc']
      have e : c * a' + d * c' = (c * (a' / c') + d) * c' := by
        field_simp
      by_cases hden : c * (a' / c') + d = 0
      · rw [mobiusExt_coe_of_eq_zero hden, mobiusExt_infty_of_eq (by rw [e, hden, zero_mul])]
      · have hne : c * a' + d * c' ≠ 0 := by
          rw [e]
          exact mul_ne_zero hden hc'
        rw [mobiusExt_coe hden, mobiusExt_infty_of_ne hne]
        congr 1
        rw [mobiusFn, div_eq_div_iff hden hne]
        field_simp
  | coe z =>
    by_cases hz : c' * z + d' = 0
    · have hnum : a' * z + b' ≠ 0 := by
        intro hab
        apply h'
        linear_combination a' * hz - c' * hab
      rw [mobiusExt_coe_of_eq_zero hz]
      have hden : (c * a' + d * c') * z + (c * b' + d * d') = c * (a' * z + b') := by
        linear_combination d * hz
      by_cases hc : c = 0
      · rw [mobiusExt_infty_of_eq hc, mobiusExt_coe_of_eq_zero (by rw [hden, hc, zero_mul])]
      · have hne : (c * a' + d * c') * z + (c * b' + d * d') ≠ 0 := by
          rw [hden]
          exact mul_ne_zero hc hnum
        rw [mobiusExt_infty_of_ne hc, mobiusExt_coe hne]
        congr 1
        rw [mobiusFn, div_eq_div_iff hc hne]
        linear_combination (a * d - b * c) * hz
    · rw [mobiusExt_coe hz]
      have hmd := mobiusFn_mul_den (a := a') (b := b') hz
      have key : (c * a' + d * c') * z + (c * b' + d * d') = (c * mobiusFn a' b' c' d' z + d) * (c' * z + d') := by
        linear_combination (-c) * hmd
      have keyN : (a * a' + b * c') * z + (a * b' + b * d') = (a * mobiusFn a' b' c' d' z + b) * (c' * z + d') := by
        linear_combination (-a) * hmd
      by_cases hw : c * mobiusFn a' b' c' d' z + d = 0
      · rw [mobiusExt_coe_of_eq_zero hw, mobiusExt_coe_of_eq_zero (by rw [key, hw, zero_mul])]
      · rw [mobiusExt_coe hw, mobiusExt_coe (by rw [key]; exact mul_ne_zero hw hz)]
        congr 1
        show (a * mobiusFn a' b' c' d' z + b) / (c * mobiusFn a' b' c' d' z + d) =
          ((a * a' + b * c') * z + (a * b' + b * d')) / ((c * a' + d * c') * z + (c * b' + d * d'))
        rw [key, keyN, mul_div_mul_right _ _ hz]

/-- Scaling all four coefficients by `σ ≠ 0` does not change the transformation. -/
theorem k24_mobiusExt_scale {σ : ℂ} (hσ : σ ≠ 0) (a b c d : ℂ) (p : ExtPlane) :
    mobiusExt (a / σ) (b / σ) (c / σ) (d / σ) p = mobiusExt a b c d p := by
  induction p using OnePoint.rec with
  | infty =>
    by_cases hc : c = 0
    · rw [mobiusExt_infty_of_eq hc, mobiusExt_infty_of_eq (by rw [hc, zero_div])]
    · rw [mobiusExt_infty_of_ne hc, mobiusExt_infty_of_ne (div_ne_zero hc hσ)]
      congr 1
      exact div_div_div_cancel_right₀ hσ a c
  | coe z =>
    have e : c / σ * z + d / σ = (c * z + d) / σ := by ring
    by_cases hz : c * z + d = 0
    · rw [mobiusExt_coe_of_eq_zero hz, mobiusExt_coe_of_eq_zero (by rw [e, hz, zero_div])]
    · rw [mobiusExt_coe hz, mobiusExt_coe (by rw [e]; exact div_ne_zero hz hσ)]
      congr 1
      rw [mobiusFn, mobiusFn, e, show a / σ * z + b / σ = (a * z + b) / σ by ring,
        div_div_div_cancel_right₀ hσ]

/-- `mobiusSL` turns products into compositions. -/
theorem k24_mobiusSL_mul (g h : Matrix.SpecialLinearGroup (Fin 2) ℂ) (p : ExtPlane) :
    mobiusSL (g * h) p = mobiusSL g (mobiusSL h p) := by
  have hh : h 0 0 * h 1 1 - h 0 1 * h 1 0 ≠ 0 := by rw [k24_det_SL]; exact one_ne_zero
  rw [mobiusSL, mobiusSL, mobiusSL, k24_mobiusExt_comp hh]
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

/-- `mobiusSL 1` is the identity. -/
theorem k24_mobiusSL_one (p : ExtPlane) : mobiusSL 1 p = p := by
  have h : mobiusSL 1 = mobiusExt 1 0 0 1 := by
    simp [mobiusSL]
  rw [h]
  induction p using OnePoint.rec with
  | infty => exact mobiusExt_infty_of_eq rfl
  | coe z =>
    rw [mobiusExt_coe (by simp)]
    simp [mobiusFn]

/-- `mobiusSL g⁻¹` inverts `mobiusSL g`. -/
theorem k24_mobiusSL_inv_apply (g : Matrix.SpecialLinearGroup (Fin 2) ℂ) (p : ExtPlane) :
    mobiusSL g⁻¹ (mobiusSL g p) = p := by
  rw [← k24_mobiusSL_mul, inv_mul_cancel, k24_mobiusSL_one]

/-- `mobiusSL g` inverts `mobiusSL g⁻¹`. -/
theorem k24_mobiusSL_apply_inv (g : Matrix.SpecialLinearGroup (Fin 2) ℂ) (p : ExtPlane) :
    mobiusSL g (mobiusSL g⁻¹ p) = p := by
  rw [← k24_mobiusSL_mul, mul_inv_cancel, k24_mobiusSL_one]

/-- `mobiusSL g` as a homeomorphism of `ℂ̄`. -/
def k24_mobiusSLHomeo (g : Matrix.SpecialLinearGroup (Fin 2) ℂ) : ExtPlane ≃ₜ ExtPlane :=
  mobiusHomeomorph (g 0 0) (g 0 1) (g 1 0) (g 1 1) (by rw [k24_det_SL]; exact one_ne_zero)

/-! #### A plane relation `f ∘ γ = M ∘ f` extends to `ℂ̄` -/

/-- The zero set of `c z + d` with `(c, d) ≠ 0` is a subsingleton. -/
theorem k24_affine_zero_subsingleton {c d : ℂ} (hcd : ¬ (c = 0 ∧ d = 0)) :
    {z : ℂ | c * z + d = 0}.Subsingleton := by
  intro z₁ h₁ z₂ h₂
  have h₁' : c * z₁ + d = 0 := h₁
  have h₂' : c * z₂ + d = 0 := h₂
  have hc : c ≠ 0 := by
    rintro rfl
    apply hcd
    refine ⟨rfl, ?_⟩
    simpa using h₁'
  have : c * (z₁ - z₂) = 0 := by linear_combination h₁' - h₂'
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hc)

/-- A Möbius relation `f ∘ T = M ∘ f` in the plane, valid off the pole of `T`, extends to `ℂ̄` for a homeomorphism `f`
of the plane: both sides are continuous on `ℂ̄` and agree off finitely many points. -/
theorem k24_ext_relation {f : ℂ → ℂ} (e : ℂ ≃ₜ ℂ) (he : ⇑e = f) {a b c d A B C D : ℂ}
    (h1 : a * d - b * c ≠ 0) (h2 : A * D - B * C ≠ 0)
    (hrel : ∀ z : ℂ, c * z + d ≠ 0 → f (mobiusFn a b c d z) = mobiusFn A B C D (f z)) (p : ExtPlane) :
    OnePoint.map f (mobiusExt a b c d p) = mobiusExt A B C D (OnePoint.map f p) := by
  have hFe : ⇑e.onePointCongr = OnePoint.map f := by
    funext q
    rw [Homeomorph.onePointCongr_apply, he]
  have hF : Continuous (OnePoint.map f) := hFe ▸ e.onePointCongr.continuous
  have hcd : ¬ (c = 0 ∧ d = 0) := by
    rintro ⟨rfl, rfl⟩
    exact h1 (by ring)
  have hCD : ¬ (C = 0 ∧ D = 0) := by
    rintro ⟨rfl, rfl⟩
    exact h2 (by ring)
  set S : Set ℂ := {z | c * z + d = 0} ∪ f ⁻¹' {w | C * w + D = 0} with hS
  have hSfin : S.Finite := by
    refine (k24_affine_zero_subsingleton hcd).finite.union ?_
    refine Set.Subsingleton.finite ?_
    intro z₁ h₁ z₂ h₂
    have h := k24_affine_zero_subsingleton hCD h₁ h₂
    rw [← he] at h
    exact e.injective h
  have hdense : Dense (((↑) : ℂ → ExtPlane) '' (univ \ S)) :=
    OnePoint.denseRange_coe.dense_image OnePoint.continuous_coe (dense_univ.sdiff_finite hSfin)
  have heq := Continuous.ext_on hdense (hF.comp (continuous_mobiusExt h1))
    ((continuous_mobiusExt h2).comp hF) (by
      rintro _ ⟨z, ⟨-, hz⟩, rfl⟩
      have hz1 : c * z + d ≠ 0 := fun h => hz (Or.inl h)
      have hz2 : C * f z + D ≠ 0 := fun h => hz (Or.inr h)
      simp only [Function.comp_apply]
      rw [mobiusExt_coe hz1, OnePoint.map_some, OnePoint.map_some, mobiusExt_coe hz2, hrel z hz1])
  exact congrFun heq p

/-- **The relation on `ℂ̄`**: for a `Γ`-compatible `μ ∈ M` and `γ ∈ Γ` there is `γ_μ ∈ SL(2, ℂ)` with
`f̂_μ ∘ γ̂ = γ̂_μ ∘ f̂_μ` on all of `ℂ̄` (MOB core, extension by density, rescaling to determinant `1`). -/
theorem k24_rel_exists {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : BeltramiH)
    (hμ : IsGammaCompatible Γ μ.1) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) :
    ∃ γμ : Matrix.SpecialLinearGroup (Fin 2) ℂ, ∀ p : ExtPlane,
      OnePoint.map (normalizedSolution μ.1) (mobiusSL (slRealToComplex γ) p) =
        mobiusSL γμ (OnePoint.map (normalizedSolution μ.1) p) := by
  obtain ⟨K, hK⟩ := (ut_spec μ).1
  have hs := (ut_spec μ).2.1
  obtain ⟨e, he⟩ := t1_homeomorph hK hs
  obtain ⟨A, B, C, D, hdet, hrel⟩ :=
    k24_mob_core hK hs (ut_spec μ).2.2.1 γ (k24_dil_comp μ hμ hγ) (ut_spec μ)
  obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_pow_nat_eq (A * D - B * C) (by norm_num : 0 < 2)
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    apply hdet
    rw [← hσ]
    ring
  have hdet1 : Matrix.det !![A / σ, B / σ; C / σ, D / σ] = 1 := by
    rw [Matrix.det_fin_two_of, div_mul_div_comm, div_mul_div_comm, ← sub_div, ← pow_two, hσ,
      div_self hdet]
  refine ⟨⟨!![A / σ, B / σ; C / σ, D / σ], hdet1⟩, fun p => ?_⟩
  have hγdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 ≠ 0 := by rw [k24_det_real]; exact one_ne_zero
  rw [k24_mobiusSL_real, k24_ext_relation e he hγdet hdet (fun z _ => hrel z) p]
  exact (k24_mobiusExt_scale hσ0 A B C D _).symm

/-! #### The deformed group `Γ_μ` -/

/-- `slRealToComplex` is multiplicative. -/
theorem k24_slReal_mul (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    slRealToComplex (γ₁ * γ₂) = slRealToComplex γ₁ * slRealToComplex γ₂ :=
  map_mul (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) γ₁ γ₂

/-- `slRealToComplex` preserves `1`. -/
theorem k24_slReal_one : slRealToComplex 1 = 1 :=
  map_one (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))

/-- `slRealToComplex` preserves inverses. -/
theorem k24_slReal_inv (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    slRealToComplex γ⁻¹ = (slRealToComplex γ)⁻¹ :=
  map_inv (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) γ

/-- The deformed group: all `g ∈ SL(2, ℂ)` conjugate under `F` to an element of `Γ`, i.e. with
`F ∘ γ̂ = ĝ ∘ F` for some `γ ∈ Γ` (both `±g` qualify). -/
def k24_deformGroup (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (F : ExtPlane → ExtPlane) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ) where
  carrier := {g | ∃ γ ∈ Γ, ∀ p, F (mobiusSL (slRealToComplex γ) p) = mobiusSL g (F p)}
  one_mem' := ⟨1, Γ.one_mem, fun p => by rw [k24_slReal_one, k24_mobiusSL_one, k24_mobiusSL_one]⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨γ₁, hγ₁, h₁⟩ ⟨γ₂, hγ₂, h₂⟩
    refine ⟨γ₁ * γ₂, Γ.mul_mem hγ₁ hγ₂, fun p => ?_⟩
    rw [k24_slReal_mul, k24_mobiusSL_mul, h₁, h₂, k24_mobiusSL_mul]
  inv_mem' := by
    rintro g ⟨γ, hγ, h⟩
    refine ⟨γ⁻¹, Γ.inv_mem hγ, fun p => ?_⟩
    have h' := h (mobiusSL (slRealToComplex γ⁻¹) p)
    rw [k24_slReal_inv, k24_mobiusSL_apply_inv] at h'
    rw [k24_slReal_inv, h', k24_mobiusSL_inv_apply]

/-- Membership in the deformed group. -/
theorem k24_mem_deformGroup {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {F : ExtPlane → ExtPlane}
    {g : Matrix.SpecialLinearGroup (Fin 2) ℂ} :
    g ∈ k24_deformGroup Γ F ↔ ∃ γ ∈ Γ, ∀ p, F (mobiusSL (slRealToComplex γ) p) = mobiusSL g (F p) :=
  Iff.rfl

/-! #### `ℝ̂`, `ℍ`, `𝕃` in `ℂ̄` and the action of `SL(2, ℝ)` -/

/-- A point of `ℂ̄` off `ℝ̂` lies in `ℍ` or in `𝕃`. -/
theorem k24_mem_halves {q : ExtPlane} (hq : q ∉ extRealLine) :
    q ∈ toExt upperHalf ∨ q ∈ toExt lowerHalf := by
  induction q using OnePoint.rec with
  | infty => exact (hq (Or.inr rfl)).elim
  | coe z =>
    rcases lt_trichotomy z.im 0 with h | h | h
    · exact Or.inr ⟨z, h, rfl⟩
    · exact (hq (Or.inl ⟨z, h, rfl⟩)).elim
    · exact Or.inl ⟨z, h, rfl⟩

/-- `ℍ` misses `ℝ̂` in `ℂ̄`. -/
theorem k24_upper_not_mem {q : ExtPlane} (hq : q ∈ toExt upperHalf) : q ∉ extRealLine := by
  obtain ⟨z, hz, rfl⟩ := hq
  rintro (⟨w, hw, hwz⟩ | h)
  · have hwz' : w = z := OnePoint.coe_injective hwz
    rw [hwz'] at hw
    exact (show 0 < z.im from hz).ne' hw
  · exact OnePoint.coe_ne_infty z h

/-- `𝕃` misses `ℝ̂` in `ℂ̄`. -/
theorem k24_lower_not_mem {q : ExtPlane} (hq : q ∈ toExt lowerHalf) : q ∉ extRealLine := by
  obtain ⟨z, hz, rfl⟩ := hq
  rintro (⟨w, hw, hwz⟩ | h)
  · have hwz' : w = z := OnePoint.coe_injective hwz
    rw [hwz'] at hw
    exact (show z.im < 0 from hz).ne hw
  · exact OnePoint.coe_ne_infty z h

/-- `γ ∈ SL(2, ℝ)` maps `ℍ` into `ℍ` in `ℂ̄`. -/
theorem k24_real_mapsTo_upper (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {q : ExtPlane}
    (hq : q ∈ toExt upperHalf) : mobiusSL (slRealToComplex γ) q ∈ toExt upperHalf := by
  obtain ⟨z, hz, rfl⟩ := hq
  have hden := k24_d_den_ne_zero (k24_det_realR γ) (show 0 < z.im from hz).ne'
  rw [k24_mobiusSL_real, mobiusExt_coe hden]
  exact ⟨_, mobiusFn_mem_upperHalf (by rw [k24_det_realR]; exact one_pos) hz, rfl⟩

/-- `γ ∈ SL(2, ℝ)` maps `𝕃` into `𝕃` in `ℂ̄`. -/
theorem k24_real_mapsTo_lower (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {q : ExtPlane}
    (hq : q ∈ toExt lowerHalf) : mobiusSL (slRealToComplex γ) q ∈ toExt lowerHalf := by
  obtain ⟨z, hz, rfl⟩ := hq
  have hz' : z.im < 0 := hz
  have hden := k24_d_den_ne_zero (k24_det_realR γ) hz'.ne
  rw [k24_mobiusSL_real, mobiusExt_coe hden]
  refine ⟨_, ?_, rfl⟩
  show (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z).im < 0
  rw [mobiusFn_im_real, k24_det_realR, one_mul]
  exact div_neg_of_neg_of_pos hz' (Complex.normSq_pos.2 hden)

/-- `γ ∈ SL(2, ℝ)` maps `ℝ̂` into `ℝ̂`. -/
theorem k24_real_mapsTo_extRealLine (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {q : ExtPlane}
    (hq : q ∈ extRealLine) : mobiusSL (slRealToComplex γ) q ∈ extRealLine := by
  rw [k24_mobiusSL_real]
  rcases hq with ⟨z, hz, rfl⟩ | hq
  · by_cases hden : (γ 1 0 : ℂ) * z + γ 1 1 = 0
    · rw [mobiusExt_coe_of_eq_zero hden]
      exact Or.inr rfl
    · rw [mobiusExt_coe hden]
      refine Or.inl ⟨_, ?_, rfl⟩
      show (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z).im = 0
      rw [mobiusFn_im_real, show z.im = 0 from hz, mul_zero, zero_div]
  · rw [mem_singleton_iff.1 hq]
    by_cases hc : (γ 1 0 : ℂ) = 0
    · rw [mobiusExt_infty_of_eq hc]
      exact Or.inr rfl
    · rw [mobiusExt_infty_of_ne hc]
      refine Or.inl ⟨_, ?_, rfl⟩
      show ((γ 0 0 : ℂ) / γ 1 0).im = 0
      rw [← ofReal_div, ofReal_im]

/-- `γ ∈ SL(2, ℝ)` maps `ℝ̂` onto `ℝ̂`. -/
theorem k24_real_image_extRealLine (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    mobiusSL (slRealToComplex γ) '' extRealLine = extRealLine := by
  refine Subset.antisymm (image_subset_iff.2 fun q hq => k24_real_mapsTo_extRealLine γ hq) fun y hy => ?_
  refine ⟨mobiusSL (slRealToComplex γ)⁻¹ y, ?_, k24_mobiusSL_apply_inv _ y⟩
  by_contra hx
  rcases k24_mem_halves hx with h | h
  · exact k24_upper_not_mem (k24_real_mapsTo_upper γ h) (by rwa [k24_mobiusSL_apply_inv])
  · exact k24_lower_not_mem (k24_real_mapsTo_lower γ h) (by rwa [k24_mobiusSL_apply_inv])

/-- The image in `ℂ̄` of a preconnected plane set is preconnected. -/
theorem k24_toExt_isPreconnected {s : Set ℂ} (hs : IsPreconnected s) : IsPreconnected (toExt s) :=
  hs.image _ OnePoint.continuous_coe.continuousOn

/-! #### The invariant curve `F(ℝ̂)` and its complementary components -/

/-- Points of a preconnected set `H ⊆ ℂ̄ ∖ ℝ̂` stay in one component of `ℂ̄ ∖ F(ℝ̂)` under a homeomorphism `F`. -/
theorem k24_comp_mem (F : ExtPlane ≃ₜ ExtPlane) {H : Set ExtPlane} (hH : IsPreconnected H)
    (hHR : ∀ x ∈ H, x ∉ extRealLine) {q x : ExtPlane} (hq : q ∈ H) (hx : x ∈ H) :
    F x ∈ connectedComponentIn (F '' extRealLine)ᶜ (F q) := by
  refine (hH.image F F.continuous.continuousOn).subset_connectedComponentIn ⟨q, hq, rfl⟩ ?_ ⟨x, hx, rfl⟩
  rintro _ ⟨y, hy, rfl⟩ ⟨w, hw, hwy⟩
  exact hHR y hy (F.injective hwy ▸ hw)

/-- `mobiusSL g` as a function is the homeomorphism `k24_mobiusSLHomeo g`. -/
theorem k24_mobiusSLHomeo_coe (g : Matrix.SpecialLinearGroup (Fin 2) ℂ) :
    ⇑(k24_mobiusSLHomeo g) = mobiusSL g := rfl

/-- **Invariance**: if `F` is a homeomorphism of `ℂ̄`, `γ ∈ SL(2, ℝ)` and `F ∘ γ̂ = ĝ ∘ F`, then `ĝ` maps `F(ℝ̂)` onto
itself and each complementary component of `F(ℝ̂)` onto itself (`γ̂` preserves `ℝ̂`, `ℍ` and `𝕃`). -/
theorem k24_conj_invariant (F : ExtPlane ≃ₜ ExtPlane) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (g : Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (hrel : ∀ p, F (mobiusSL (slRealToComplex γ) p) = mobiusSL g (F p)) :
    mobiusSL g '' (F '' extRealLine) = F '' extRealLine ∧
      ∀ p ∈ (F '' extRealLine)ᶜ, mobiusSL g '' connectedComponentIn (F '' extRealLine)ᶜ p =
        connectedComponentIn (F '' extRealLine)ᶜ p := by
  have hC : mobiusSL g '' (F '' extRealLine) = F '' extRealLine := by
    rw [image_image]
    have h : (fun x => mobiusSL g (F x)) = fun x => F (mobiusSL (slRealToComplex γ) x) :=
      funext fun x => (hrel x).symm
    rw [h, ← image_image F, k24_real_image_extRealLine]
  refine ⟨hC, fun p hp => ?_⟩
  rw [← k24_mobiusSLHomeo_coe] at hC ⊢
  have hGC : ⇑(k24_mobiusSLHomeo g) '' (F '' extRealLine)ᶜ = (F '' extRealLine)ᶜ := by
    rw [image_compl_eq (k24_mobiusSLHomeo g).bijective, hC]
  have h := (k24_mobiusSLHomeo g).image_connectedComponentIn hp
  rw [hGC] at h
  refine h.trans (connectedComponentIn_eq ?_).symm
  obtain ⟨q, rfl⟩ := F.surjective p
  have hq : q ∉ extRealLine := fun h => hp ⟨q, h, rfl⟩
  rw [k24_mobiusSLHomeo_coe, ← hrel]
  rcases k24_mem_halves hq with hq' | hq'
  · exact k24_comp_mem F (k24_toExt_isPreconnected isConnected_upperHalf.isPreconnected)
      (fun x hx => k24_upper_not_mem hx) hq' (k24_real_mapsTo_upper γ hq')
  · exact k24_comp_mem F (k24_toExt_isPreconnected bA_isConnected_lowerHalf.isPreconnected)
      (fun x hx => k24_lower_not_mem hx) hq' (k24_real_mapsTo_lower γ hq')

/-! #### Assembly -/

/-- **Assembly** of `fuchsian_deformation`, with the Klein-group transport (`k24_klein_of_conj`) as a hypothesis:
`Γ_μ := {g | ∃ γ ∈ Γ, f̂_μ ∘ γ̂ = ĝ ∘ f̂_μ}` is a subgroup, contains a lift of every `γ ∈ Γ` (MOB core), and preserves
the
Jordan curve `f̂_μ(ℝ̂)` together with each of its complementary components. -/
theorem k24_main {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (μ : BeltramiH)
    (hμ : IsGammaCompatible Γ μ.1)
    (hK : ∀ (F : ExtPlane ≃ₜ ExtPlane) {Γμ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)},
      (∀ γ ∈ Γ, ∃ γμ ∈ Γμ, ∀ p, F (mobiusSL (slRealToComplex γ) p) = mobiusSL γμ (F p)) →
      (∀ γμ ∈ Γμ, ∃ γ ∈ Γ, ∀ p, F (mobiusSL (slRealToComplex γ) p) = mobiusSL γμ (F p)) →
      IsKleinGroup Γμ) :
    ∃ Γμ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ),
      IsQuasiFuchsian Γμ (OnePoint.map (normalizedSolution μ.1) '' extRealLine) ∧
      (∀ γ ∈ Γ, ∃ γμ ∈ Γμ, ∀ p : ExtPlane,
        OnePoint.map (normalizedSolution μ.1) (mobiusSL (slRealToComplex γ) p) =
          mobiusSL γμ (OnePoint.map (normalizedSolution μ.1) p)) ∧
      ∀ γμ ∈ Γμ, ∃ γ ∈ Γ, ∀ p : ExtPlane,
        OnePoint.map (normalizedSolution μ.1) (mobiusSL (slRealToComplex γ) p) =
          mobiusSL γμ (OnePoint.map (normalizedSolution μ.1) p) := by
  obtain ⟨K, hKqc⟩ := (ut_spec μ).1
  obtain ⟨e, he⟩ := t1_homeomorph hKqc (ut_spec μ).2.1
  have hFf : ⇑e.onePointCongr = OnePoint.map (normalizedSolution μ.1) := by
    funext p
    rw [Homeomorph.onePointCongr_apply, he]
  rw [← hFf]
  set F := e.onePointCongr
  have h1 : ∀ γ ∈ Γ, ∃ γμ ∈ k24_deformGroup Γ F, ∀ p,
      F (mobiusSL (slRealToComplex γ) p) = mobiusSL γμ (F p) := by
    intro γ hγ
    obtain ⟨g, hg⟩ := k24_rel_exists μ hμ hγ
    rw [← hFf] at hg
    exact ⟨g, k24_mem_deformGroup.2 ⟨γ, hγ, hg⟩, hg⟩
  have h2 : ∀ γμ ∈ k24_deformGroup Γ F, ∃ γ ∈ Γ, ∀ p,
      F (mobiusSL (slRealToComplex γ) p) = mobiusSL γμ (F p) :=
    fun _ hg => k24_mem_deformGroup.1 hg
  refine ⟨k24_deformGroup Γ F,
    ⟨hK F h1 h2, uq_isJordanCurve_image F tp_c1_isJordanCurve_extRealLine, fun g hg => ?_⟩, h1, h2⟩
  obtain ⟨γ, -, hrel⟩ := k24_mem_deformGroup.1 hg
  exact k24_conj_invariant F γ g hrel

/-! #### The Klein-group transport and the discontinuity core (scout F2) -/

/-! ### Möbius maps determine their `SL(2, ℂ)` matrices up to sign -/

/-- The pole set of `z ↦ (az+b)/(cz+d)` with `ad - bc = 1` has at most one point. -/
theorem k24_c_pole_subset {a b c d : ℂ} (h : a * d - b * c = 1) :
    {z : ℂ | c * z + d = 0} ⊆ {-d / c} := by
  intro z hz
  simp only [mem_ofPred_eq] at hz
  have hc : c ≠ 0 := by
    rintro rfl
    have hd : d = 0 := by simpa using hz
    rw [hd] at h
    simp at h
  rw [mem_singleton_iff, eq_div_iff hc]
  linear_combination hz

/-- Two matrices of `SL(2, ℂ)` inducing the same Möbius map of `ℂ̂` agree up to sign. -/
theorem k24_c_mobiusSL_eq_or_neg {g g' : Matrix.SpecialLinearGroup (Fin 2) ℂ}
    (h : mobiusSL g = mobiusSL g') : g' = g ∨ g' = -g := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rwa [Matrix.det_fin_two] at this
  have hdet' : g' 0 0 * g' 1 1 - g' 0 1 * g' 1 0 = 1 := by
    have := g'.2
    rwa [Matrix.det_fin_two] at this
  obtain ⟨E1, hE1⟩ : ∃ e : ℂ, e = g 0 0 * g' 1 0 - g' 0 0 * g 1 0 := ⟨_, rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ e : ℂ,
      e = g 0 0 * g' 1 1 + g 0 1 * g' 1 0 - g' 0 0 * g 1 1 - g' 0 1 * g 1 0 := ⟨_, rfl⟩
  obtain ⟨E3, hE3⟩ : ∃ e : ℂ, e = g 0 1 * g' 1 1 - g' 0 1 * g 1 1 := ⟨_, rfl⟩
  have hP : (Polynomial.C E1 * Polynomial.X ^ 2 + Polynomial.C E2 * Polynomial.X +
      Polynomial.C E3 : Polynomial ℂ) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hfin : ({z : ℂ | g 1 0 * z + g 1 1 = 0} ∪ {z : ℂ | g' 1 0 * z + g' 1 1 = 0}).Finite :=
      ((finite_singleton _).subset (k24_c_pole_subset hdet)).union
        ((finite_singleton _).subset (k24_c_pole_subset hdet'))
    refine hfin.infinite_compl.mono ?_
    intro z hz
    simp only [mem_compl_iff, mem_union, mem_ofPred_eq, not_or] at hz
    obtain ⟨hz1, hz2⟩ := hz
    have hv := congrFun h (z : ExtPlane)
    simp only [mobiusSL] at hv
    rw [mobiusExt_coe hz1, mobiusExt_coe hz2] at hv
    have hv' := OnePoint.coe_injective hv
    simp only [mobiusFn] at hv'
    rw [div_eq_div_iff hz1 hz2] at hv'
    simp only [mem_ofPred_eq, Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hE1, hE2, hE3]
    linear_combination hv'
  have c2 := congrArg (Polynomial.coeff · 2) hP
  have c1 := congrArg (Polynomial.coeff · 1) hP
  have c0 := congrArg (Polynomial.coeff · 0) hP
  simp [Polynomial.coeff_X, Polynomial.coeff_C] at c2 c1 c0
  rw [hE1] at c2
  rw [hE2] at c1
  rw [hE3] at c0
  obtain ⟨α, hα⟩ : ∃ α, α = g' 0 0 * g 1 1 - g' 0 1 * g 1 0 := ⟨_, rfl⟩
  have hβ : g 0 0 * g' 0 1 - g' 0 0 * g 0 1 = 0 := by
    linear_combination (-(g 0 1) ^ 2) * c2 + (g 0 0 * g 0 1) * c1 + (-(g 0 0) ^ 2) * c0 -
      (g 0 0 * g' 0 1 - g' 0 0 * g 0 1) * hdet
  have hγ : g' 1 0 * g 1 1 - g 1 0 * g' 1 1 = 0 := by
    linear_combination (g 1 1) ^ 2 * c2 + (-(g 1 0 * g 1 1)) * c1 + (g 1 0) ^ 2 * c0 -
      (g' 1 0 * g 1 1 - g 1 0 * g' 1 1) * hdet
  have hδ : g 0 0 * g' 1 1 - g 0 1 * g' 1 0 - α = 0 := by
    linear_combination (-2 * g 0 1 * g 1 1) * c2 + (g 0 0 * g 1 1 + g 0 1 * g 1 0) * c1 +
      (-2 * g 0 0 * g 1 0) * c0 -
      (g 0 0 * g' 1 1 - g 0 1 * g' 1 0 - (g' 0 0 * g 1 1 - g' 0 1 * g 1 0)) * hdet - hα
  have ha : g' 0 0 = α * g 0 0 := by
    linear_combination g 1 0 * hβ - g' 0 0 * hdet - g 0 0 * hα
  have hb : g' 0 1 = α * g 0 1 := by
    linear_combination g 1 1 * hβ - g' 0 1 * hdet - g 0 1 * hα
  have hc : g' 1 0 = α * g 1 0 := by
    linear_combination g 0 0 * hγ + g 1 0 * hδ - g' 1 0 * hdet
  have hd : g' 1 1 = α * g 1 1 := by
    linear_combination g 0 1 * hγ + g 1 1 * hδ - g' 1 1 * hdet
  rw [ha, hb, hc, hd] at hdet'
  have hα2 : (α - 1) * (α + 1) = 0 := by
    linear_combination hdet' - α ^ 2 * hdet
  rcases mul_eq_zero.1 hα2 with h1 | h1
  · left
    have hα1 : α = 1 := by linear_combination h1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd, hα1]
  · right
    have hα1 : α = -1 := by linear_combination h1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd, hα1, Matrix.SpecialLinearGroup.coe_neg]

/-- The fibres of `γ ↦ mobiusSL γ` are finite (they have at most two elements). -/
theorem k24_c_mobiusSL_fiber_finite (f : ExtPlane → ExtPlane) :
    (mobiusSL ⁻¹' {f}).Finite := by
  by_cases hf : ∃ g, mobiusSL g = f
  · obtain ⟨g, rfl⟩ := hf
    refine ((finite_singleton (-g)).insert g).subset ?_
    intro g' hg'
    rcases k24_c_mobiusSL_eq_or_neg (g := g) (g' := g') hg'.symm with h | h
    · exact Or.inl h
    · exact Or.inr h
  · convert finite_empty
    ext g
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    exact fun h => hf ⟨g, h⟩

/-! ### Sequences -/

/-- A sequence with infinite range has an injective subsequence (along indices tending to
infinity). -/
theorem k24_c_exists_injective_subseq {α : Type*} {s : ℕ → α} (hs : (range s).Infinite) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧ Function.Injective (s ∘ φ) := by
  let e := hs.natEmbedding
  have hmem : ∀ n, ∃ m, s m = (e n : α) := fun n => (e n).2
  choose φ hφ using hmem
  have hinj : Function.Injective (s ∘ φ) := by
    intro n m hnm
    apply e.injective
    apply Subtype.ext
    simpa only [Function.comp_apply, hφ] using hnm
  refine ⟨φ, ?_, hinj⟩
  have := (Function.Injective.of_comp hinj).tendsto_cofinite
  rwa [Nat.cofinite_eq_atTop] at this

/-! ### Transport of limit sets and of discontinuity through a conjugating map -/

/-- If a continuous injective `F` conjugates every element of `G₁` into `G₂`, then
`F(Λ(G₁)) ⊆ Λ(G₂)`. -/
theorem k24_c_limitSet_image_subset {G₁ G₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    {F : ExtPlane → ExtPlane} (hFc : Continuous F) (hFi : Function.Injective F)
    (h : ∀ g ∈ G₁, ∃ g' ∈ G₂, ∀ p, F (mobiusSL g p) = mobiusSL g' (F p)) :
    F '' limitSet G₁ ⊆ limitSet G₂ := by
  rintro _ ⟨p, ⟨q, γs, hinj, hlim⟩, rfl⟩
  choose g' hg'mem hg' using fun n => h (γs n) (γs n).2
  let s : ℕ → G₂ := fun n => ⟨g' n, hg'mem n⟩
  have hinf : (range s).Infinite := by
    intro hfin
    have heq : (fun n => F ∘ mobiusSL (γs n)) =
        (fun x : G₂ => mobiusSL (x : Matrix.SpecialLinearGroup (Fin 2) ℂ) ∘ F) ∘ s := by
      funext n w
      simp [s, hg']
    have h1 : (range fun n => F ∘ mobiusSL (γs n)).Finite := by
      rw [heq, range_comp]
      exact hfin.image _
    have h2 : (range fun n => mobiusSL (γs n)).Finite := by
      refine Set.Finite.of_finite_image ?_ (fun _ _ _ _ hxy => hFi.comp_left hxy)
      rw [← range_comp]
      exact h1
    have h3 : (range fun n => ((γs n : Matrix.SpecialLinearGroup (Fin 2) ℂ))).Finite := by
      refine (h2.preimage' fun f _ => k24_c_mobiusSL_fiber_finite f).subset ?_
      rintro _ ⟨n, rfl⟩
      exact ⟨n, rfl⟩
    exact Set.infinite_range_of_injective (Subtype.val_injective.comp hinj) h3
  obtain ⟨φ, hφ, hφinj⟩ := k24_c_exists_injective_subseq hinf
  refine ⟨F q, s ∘ φ, hφinj, ?_⟩
  have := ((hFc.tendsto p).comp hlim).comp hφ
  refine this.congr fun n => ?_
  simp [s, hg']

/-- Discontinuity on compacts of `Ω(G₁)` transports through a homeomorphism `F` conjugating
every element of `G₂` back into `G₁`, provided `F(Λ(G₁)) ⊆ Λ(G₂)`. -/
theorem k24_c_disc_transport {G₁ G₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    (F : ExtPlane ≃ₜ ExtPlane)
    (h : ∀ g' ∈ G₂, ∃ g ∈ G₁, ∀ p, F (mobiusSL g p) = mobiusSL g' (F p))
    (hdisc : ∀ C : Set ExtPlane, IsCompact C → C ⊆ (limitSet G₁)ᶜ →
      {γ ∈ G₁ | (mobiusSL γ '' C ∩ C).Nonempty}.Finite)
    (hsub : F '' limitSet G₁ ⊆ limitSet G₂)
    (C : Set ExtPlane) (hC : IsCompact C) (hCΛ : C ⊆ (limitSet G₂)ᶜ) :
    {γ ∈ G₂ | (mobiusSL γ '' C ∩ C).Nonempty}.Finite := by
  have hC' : IsCompact (F.symm '' C) := hC.image F.symm.continuous
  have hC'Λ : F.symm '' C ⊆ (limitSet G₁)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩ hmem
    exact hCΛ hx (by simpa using hsub ⟨_, hmem, rfl⟩)
  have hfin := (hdisc _ hC' hC'Λ).image
    (fun g => (F : ExtPlane → ExtPlane) ∘ mobiusSL g ∘ F.symm)
  refine (hfin.preimage' fun f _ => k24_c_mobiusSL_fiber_finite f).subset ?_
  rintro g' ⟨hg'G, x, ⟨y, hy, hyx⟩, hxC⟩
  obtain ⟨g, hgG, hg⟩ := h g' hg'G
  have hconj : mobiusSL g' = (F : ExtPlane → ExtPlane) ∘ mobiusSL g ∘ F.symm := by
    funext w
    simp only [Function.comp_apply]
    rw [hg, F.apply_symm_apply]
  refine ⟨g, ⟨hgG, F.symm x, ⟨F.symm y, ⟨y, hy, rfl⟩, ?_⟩, ⟨x, hxC, rfl⟩⟩, hconj.symm⟩
  rw [← hyx, hconj]
  simp

/-! ### Fuchsian groups: bounded elements are finite in number -/

/-- A compact subset of `ℍ`: `{τ | 1/R ≤ Im τ, |τ| ≤ R}`. -/
theorem k24_c_isCompact_box {R : ℝ} (hR : 0 < R) :
    IsCompact {τ : UpperHalfPlane | 1 / R ≤ τ.im ∧ ‖(τ : ℂ)‖ ≤ R} := by
  have hK : IsCompact ({z : ℂ | 1 / R ≤ z.im} ∩ closedBall 0 R) :=
    (isCompact_closedBall 0 R).inter_left (isClosed_le continuous_const continuous_im)
  have hsub : {z : ℂ | 1 / R ≤ z.im} ∩ closedBall 0 R ⊆ range UpperHalfPlane.coe := by
    rintro z ⟨hz, -⟩
    have hpos : 0 < z.im := lt_of_lt_of_le (by positivity) hz
    exact ⟨⟨z, hpos⟩, rfl⟩
  have := (UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage_iff hsub).2 hK
  convert this using 1
  ext τ
  simp [mem_closedBall, dist_zero_right]

/-- An element of `SL(2, ℝ)` with entries bounded by `M` maps `i` into the compact box of
parameter `2M² + 1`. -/
theorem k24_c_smul_I_mem_box (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {M : ℝ}
    (hM : ∀ i j, |γ i j| ≤ M) :
    γ • UpperHalfPlane.I ∈ {τ : UpperHalfPlane | 1 / (2 * M ^ 2 + 1) ≤ τ.im ∧
      ‖(τ : ℂ)‖ ≤ 2 * M ^ 2 + 1} := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rwa [Matrix.det_fin_two] at this
  have hsq : ∀ i j, (γ i j) ^ 2 ≤ M ^ 2 := fun i j => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM i j) 2
  set a := γ 0 0
  set b := γ 0 1
  set c := γ 1 0
  set d := γ 1 1
  have hPQ : 1 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a * c + b * d)]
  have hQpos : 0 < c ^ 2 + d ^ 2 := by
    rcases (add_nonneg (sq_nonneg c) (sq_nonneg d)).lt_or_eq with h | h
    · exact h
    · rw [← h] at hPQ; simp at hPQ; linarith
  have hP : a ^ 2 + b ^ 2 ≤ 2 * M ^ 2 := by linarith [hsq 0 0, hsq 0 1]
  have hQ : c ^ 2 + d ^ 2 ≤ 2 * M ^ 2 := by linarith [hsq 1 0, hsq 1 1]
  have hval : ((γ • UpperHalfPlane.I : UpperHalfPlane) : ℂ) =
      ((a : ℂ) * Complex.I + b) / ((c : ℂ) * Complex.I + d) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [a, b, c, d]
  have hnormSq : Complex.normSq ((c : ℂ) * Complex.I + d) = c ^ 2 + d ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have hnormSq' : Complex.normSq ((a : ℂ) * Complex.I + b) = a ^ 2 + b ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have him : (((a : ℂ) * Complex.I + b) / ((c : ℂ) * Complex.I + d)).im = 1 / (c ^ 2 + d ^ 2) := by
    rw [Complex.div_im, hnormSq]
    simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [← sub_div]
    congr 1
    linear_combination hdet
  have hnorm2 : ‖((a : ℂ) * Complex.I + b) / ((c : ℂ) * Complex.I + d)‖ ^ 2 =
      (a ^ 2 + b ^ 2) / (c ^ 2 + d ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_div, hnormSq, hnormSq']
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 0)
  set R := 2 * M ^ 2 + 1 with hRdef
  have hRpos : 0 < R := by positivity
  refine ⟨?_, ?_⟩
  · show 1 / R ≤ ((γ • UpperHalfPlane.I : UpperHalfPlane) : ℂ).im
    rw [hval, him]
    exact one_div_le_one_div_of_le hQpos (by linarith)
  · show ‖((γ • UpperHalfPlane.I : UpperHalfPlane) : ℂ)‖ ≤ R
    rw [hval]
    have hP0 : 0 ≤ a ^ 2 + b ^ 2 := by positivity
    have hle : (a ^ 2 + b ^ 2) / (c ^ 2 + d ^ 2) ≤ R ^ 2 := by
      rw [div_le_iff₀ hQpos]
      have h1 : a ^ 2 + b ^ 2 ≤ (a ^ 2 + b ^ 2) ^ 2 * (c ^ 2 + d ^ 2) := by
        nlinarith [mul_le_mul_of_nonneg_left hPQ hP0]
      have h2 : (a ^ 2 + b ^ 2) ^ 2 ≤ R ^ 2 :=
        pow_le_pow_left₀ hP0 (by linarith) 2
      nlinarith [mul_le_mul_of_nonneg_right h2 hQpos.le]
    rw [← hnorm2] at hle
    nlinarith [norm_nonneg (((a : ℂ) * Complex.I + b) / ((c : ℂ) * Complex.I + d))]

/-- The entries of `slRealToComplex`-type images are the real entries. -/
theorem k24_c_map_apply (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ) i j = ((γ i j : ℝ) : ℂ) := by
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

/-- (c) Distinct elements of a Fuchsian group have norms tending to infinity. -/
theorem k24_c_norm_tendsto {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) (γs : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℂ)
    (hinj : Function.Injective γs)
    (hmem : ∀ n, γs n ∈ Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) :
    Tendsto (fun n => ‖γs n 0 0‖ + ‖γs n 0 1‖ + ‖γs n 1 0‖ + ‖γs n 1 1‖) atTop atTop := by
  choose γr hγrΓ hγr using fun n => Subgroup.mem_map.1 (hmem n)
  have hγrinj : Function.Injective γr := fun n m h => hinj (by rw [← hγr n, ← hγr m, h])
  have hent : ∀ n i j, ‖γs n i j‖ = |γr n i j| := by
    intro n i j
    rw [← hγr n, k24_c_map_apply, Complex.norm_real, Real.norm_eq_abs]
  rw [Filter.tendsto_atTop]
  intro M
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hinf : {n | ¬ M ≤ ‖γs n 0 0‖ + ‖γs n 0 1‖ + ‖γs n 1 0‖ + ‖γs n 1 1‖}.Infinite :=
    Nat.frequently_atTop_iff_infinite.1 hcon
  set K := {τ : UpperHalfPlane | 1 / (2 * M ^ 2 + 1) ≤ τ.im ∧ ‖(τ : ℂ)‖ ≤ 2 * M ^ 2 + 1}
  have hK : IsCompact (insert UpperHalfPlane.I K) :=
    (k24_c_isCompact_box (by positivity)).insert _
  have hfin := hΓ _ hK
  refine (hinf.image hγrinj.injOn) (hfin.subset ?_)
  rintro _ ⟨n, hn, rfl⟩
  simp only [mem_ofPred_eq, not_le] at hn
  have hbd : ∀ i j, |γr n i j| ≤ M := by
    intro i j
    have h00 := norm_nonneg (γs n 0 0)
    have h01 := norm_nonneg (γs n 0 1)
    have h10 := norm_nonneg (γs n 1 0)
    have h11 := norm_nonneg (γs n 1 1)
    rw [← hent]
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  refine ⟨hγrΓ n, γr n • UpperHalfPlane.I, ⟨UpperHalfPlane.I, mem_insert _ _, rfl⟩,
    mem_insert_of_mem _ (k24_c_smul_I_mem_box (γr n) hbd)⟩

/-- The Möbius map of the complexification of a real matrix. -/
theorem k24_c_mobiusSL_map (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ) =
      mobiusExt ((γ 0 0 : ℝ) : ℂ) ((γ 0 1 : ℝ) : ℂ) ((γ 1 0 : ℝ) : ℂ) ((γ 1 1 : ℝ) : ℂ) := by
  simp only [mobiusSL, k24_c_map_apply]

/-- (b) The point `i` is not a limit point of a Fuchsian group acting on `ℂ̂`. -/
theorem k24_c_I_not_mem_limitSet {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) :
    ((Complex.I : ℂ) : ExtPlane) ∉
      limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) := by
  rintro ⟨q, γs, hinj, hlim⟩
  choose γr hγrΓ hγr using fun n => Subgroup.mem_map.1 (γs n).2
  have hγrinj : Function.Injective γr := fun n m h =>
    hinj (Subtype.ext (by rw [← hγr n, ← hγr m, h]))
  have hmob : ∀ n, mobiusSL (γs n) =
      mobiusExt ((γr n 0 0 : ℝ) : ℂ) ((γr n 0 1 : ℝ) : ℂ) ((γr n 1 0 : ℝ) : ℂ)
        ((γr n 1 1 : ℝ) : ℂ) := by
    intro n
    rw [← hγr n, k24_c_mobiusSL_map]
  have hdetr : ∀ n, γr n 0 0 * γr n 1 1 - γr n 0 1 * γr n 1 0 = 1 := by
    intro n
    have := (γr n).2
    rwa [Matrix.det_fin_two] at this
  by_cases hq : q ∈ toExt upperHalf
  · obtain ⟨z, hz, rfl⟩ := hq
    let τ : UpperHalfPlane := ⟨z, hz⟩
    have hval : ∀ n, mobiusSL (γs n) (z : ExtPlane) =
        (((γr n • τ : UpperHalfPlane) : ℂ) : ExtPlane) := by
      intro n
      rw [hmob n, mobiusExt_coe (mobiusFn_den_ne_zero_real (by rw [hdetr n]; norm_num) hz)]
      congr 1
      rw [UpperHalfPlane.coe_specialLinearGroup_apply]
      simp [mobiusFn, τ]
    have h1 : Tendsto (fun n => ((γr n • τ : UpperHalfPlane) : ℂ)) atTop (𝓝 Complex.I) := by
      have h0 : Tendsto (fun n => (((γr n • τ : UpperHalfPlane) : ℂ) : ExtPlane)) atTop
          (𝓝 ((Complex.I : ℂ) : ExtPlane)) := by
        refine hlim.congr fun n => ?_
        exact hval n
      exact (OnePoint.isOpenEmbedding_coe.isEmbedding.tendsto_nhds_iff).2 h0
    have h2 : Tendsto (fun n => γr n • τ) atTop (𝓝 UpperHalfPlane.I) := by
      rw [UpperHalfPlane.isEmbedding_coe.tendsto_nhds_iff]
      exact h1
    obtain ⟨K, hK, hKI⟩ := exists_compact_mem_nhds UpperHalfPlane.I
    have hfin := hΓ _ (hK.insert τ)
    have hev : ∀ᶠ n in atTop,
        γr n ∈ {γ ∈ Γ | ((γ • ·) '' insert τ K ∩ insert τ K).Nonempty} := by
      filter_upwards [h2 hKI] with n hn
      exact ⟨hγrΓ n, γr n • τ, ⟨τ, mem_insert _ _, rfl⟩, mem_insert_of_mem _ hn⟩
    have hcof := hγrinj.tendsto_cofinite
    rw [Nat.cofinite_eq_atTop] at hcof
    obtain ⟨n, hn1, hn2⟩ := (hev.and (hcof hfin.compl_mem_cofinite)).exists
    exact hn2 hn1
  · have hcl : IsClosed (toExt upperHalf)ᶜ :=
      (OnePoint.isOpen_image_coe.2 (isOpen_lt continuous_const continuous_im)).isClosed_compl
    have hstay : ∀ n, mobiusSL (γs n) q ∈ (toExt upperHalf)ᶜ := by
      intro n hn
      rw [hmob n, ← mobiusExt_image_toExt_upperHalf (by rw [hdetr n]; norm_num)] at hn
      obtain ⟨y, hy, hyq⟩ := hn
      have hne : ((γr n 0 0 : ℝ) : ℂ) * ((γr n 1 1 : ℝ) : ℂ) -
          ((γr n 0 1 : ℝ) : ℂ) * ((γr n 1 0 : ℝ) : ℂ) ≠ 0 := by
        rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, hdetr n]
        norm_num
      have := (Function.LeftInverse.injective (mobiusExt_inv_apply hne)) hyq
      exact hq (this ▸ hy)
    have := hcl.mem_of_tendsto hlim (Eventually.of_forall hstay)
    exact this ⟨Complex.I, by simp [upperHalf], rfl⟩

/-! ### The core: a Fuchsian group acts discontinuously on `Ω(Γ)` -/

/-- (d) THE CORE.  The complexification of a Fuchsian group acts discontinuously on compact
subsets of the complement of its limit set. -/
theorem k24_c_core {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (C : Set ExtPlane) (hC : IsCompact C)
    (hCΛ : C ⊆ (limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))))ᶜ) :
    {γ ∈ Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) |
      (mobiusSL γ '' C ∩ C).Nonempty}.Finite := by
  by_contra hinf
  let e := Set.Infinite.natEmbedding _ hinf
  let γs : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℂ := fun n => (e n : _)
  have hγsmem : ∀ n, γs n ∈ Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) ∧
      (mobiusSL (γs n) '' C ∩ C).Nonempty := fun n => (e n).2
  have hγsinj : Function.Injective γs := fun n m h => e.injective (Subtype.ext h)
  obtain ⟨φ, a, b, hφ, hatt, hrep⟩ :=
    k22_convergence γs (k24_c_norm_tendsto hΓ γs hγsinj fun n => (hγsmem n).1)
  have hA : a ∈ limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) := by
    obtain ⟨q, hq⟩ := exists_ne b
    refine ⟨q, fun n => ⟨γs (φ n), (hγsmem (φ n)).1⟩,
      fun n m h => hφ.injective (hγsinj (by have h' := congrArg Subtype.val h; exact h')), ?_⟩
    rw [Filter.tendsto_def]
    intro U hU
    filter_upwards [hatt {q} isCompact_singleton (fun h => hq (mem_singleton_iff.1 h).symm)
      U hU] with n hn
    exact hn ⟨q, rfl, rfl⟩
  have hB : b ∈ limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) := by
    obtain ⟨q, hq⟩ := exists_ne a
    refine ⟨q, fun n => ⟨(γs (φ n))⁻¹, Subgroup.inv_mem _ (hγsmem (φ n)).1⟩,
      fun n m h => hφ.injective
        (hγsinj (inv_injective (by have h' := congrArg Subtype.val h; exact h'))), ?_⟩
    rw [Filter.tendsto_def]
    intro U hU
    filter_upwards [hrep {q} isCompact_singleton (fun h => hq (mem_singleton_iff.1 h).symm)
      U hU] with n hn
    exact hn ⟨q, rfl, rfl⟩
  have haC : a ∉ C := fun h => hCΛ h hA
  have hbC : b ∉ C := fun h => hCΛ h hB
  obtain ⟨n, hn⟩ := (hatt C hC hbC Cᶜ (hC.isClosed.isOpen_compl.mem_nhds haC)).exists
  obtain ⟨x, hx1, hx2⟩ := (hγsmem (φ n)).2
  exact hn hx1 hx2

/-! ### Assembly -/

/-- **Target (F2).**  A group `Γμ ⊆ SL(2, ℂ)` conjugate by a homeomorphism `F` of `ℂ̂` (in the
two-way sense of `h1`, `h2`) to a Fuchsian group `Γ` with more than two limit points is a Klein
group. -/
theorem k24_klein_of_conj {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hΓne : 2 < (limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)))).encard)
    (F : ExtPlane ≃ₜ ExtPlane) {Γμ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    (h1 : ∀ γ ∈ Γ, ∃ γμ ∈ Γμ, ∀ p, F (mobiusSL (slRealToComplex γ) p) = mobiusSL γμ (F p))
    (h2 : ∀ γμ ∈ Γμ, ∃ γ ∈ Γ, ∀ p, F (mobiusSL (slRealToComplex γ) p) = mobiusSL γμ (F p)) :
    IsKleinGroup Γμ := by
  have h1' : ∀ g ∈ Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)), ∃ g' ∈ Γμ,
      ∀ p, F (mobiusSL g p) = mobiusSL g' (F p) := by
    intro g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hg
    exact h1 γ hγ
  have h2' : ∀ g' ∈ Γμ, ∃ g ∈ Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)),
      ∀ p, F (mobiusSL g p) = mobiusSL g' (F p) := by
    intro g' hg'
    obtain ⟨γ, hγ, hrel⟩ := h2 g' hg'
    exact ⟨slRealToComplex γ, Subgroup.mem_map_of_mem _ hγ, hrel⟩
  have h2'' : ∀ g' ∈ Γμ, ∃ g ∈ Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)),
      ∀ p, F.symm (mobiusSL g' p) = mobiusSL g (F.symm p) := by
    intro g' hg'
    obtain ⟨g, hg, hrel⟩ := h2' g' hg'
    refine ⟨g, hg, fun p => ?_⟩
    have := hrel (F.symm p)
    rw [F.apply_symm_apply] at this
    rw [← this, F.symm_apply_apply]
  have inc1 := k24_c_limitSet_image_subset F.continuous F.injective h1'
  have inc2 := k24_c_limitSet_image_subset F.symm.continuous F.symm.injective h2''
  refine ⟨⟨F ((Complex.I : ℂ) : ExtPlane), fun hmem => k24_c_I_not_mem_limitSet hΓ ?_⟩, ?_, ?_⟩
  · simpa using inc2 ⟨_, hmem, rfl⟩
  · calc (2 : ℕ∞) < _ := hΓne
      _ = (F '' limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)))).encard :=
        (F.injective.encard_image _).symm
      _ ≤ _ := Set.encard_le_encard inc1
  · exact k24_c_disc_transport F h2' (k24_c_core hΓ) inc1

/-- §24.1: for a Fuchsian group `Γ` and a `Γ`-compatible Beltrami coefficient `μ` supported in `ℍ`,
every `f_μ γ f_μ⁻¹`, `γ ∈ Γ`, is a fractional linear transformation, and the group
`Γ_μ = f_μ Γ f_μ⁻¹` is quasi-Fuchsian with invariant curve `f_μ(ℝ) ∪ {∞}`. -/
theorem fuchsian_deformation {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hΓne : 2 < (limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)))).encard)
    (μ : BeltramiH) (hμ : IsGammaCompatible Γ μ.1) :
    ∃ Γμ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ),
      IsQuasiFuchsian Γμ (OnePoint.map (normalizedSolution μ.1) '' extRealLine) ∧
      (∀ γ ∈ Γ, ∃ γμ ∈ Γμ, ∀ p : ExtPlane,
        OnePoint.map (normalizedSolution μ.1) (mobiusSL (slRealToComplex γ) p) =
          mobiusSL γμ (OnePoint.map (normalizedSolution μ.1) p)) ∧
      ∀ γμ ∈ Γμ, ∃ γ ∈ Γ, ∀ p : ExtPlane,
        OnePoint.map (normalizedSolution μ.1) (mobiusSL (slRealToComplex γ) p) =
          mobiusSL γμ (OnePoint.map (normalizedSolution μ.1) p) := by
  exact k24_main μ hμ fun F {_} h1 h2 => k24_klein_of_conj hΓ hΓne F h1 h2

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S₁ : Type v} [TopologicalSpace S₁] [ChartedSpace ℂ S₁]

/-- An orientation preserving homeomorphism of Riemann surfaces (保向同胚): its local expressions are
sense preserving. -/
def IsOrientationPreservingRS (f : S₀ ≃ₜ S₁) : Prop :=
  ∀ x : S₀, IsSensePreserving (localMapExpr f x) (localMapDomain f x)

/-- §24.2: if `S₀` and `S₁` are closed Riemann surfaces of the same genus, every homotopy class of
orientation preserving homeomorphisms `S₀ → S₁` contains a quasiconformal map. -/
theorem exists_qc_in_homotopy_class [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (h₀ : HasGenus S₀ g)
    (h₁ : HasGenus S₁ g) (f : S₀ ≃ₜ S₁) (hf : IsOrientationPreservingRS f) :
    ∃ q : S₀ ≃ₜ S₁, IsQCRS q ∧ ContinuousMap.Homotopic (f : C(S₀, S₁)) (q : C(S₀, S₁)) := by
  sorry

/-- `p : ℂ → S` realizes `S` as `D/Γ` for a plane domain `D` invariant under the Klein group `Γ`:
a holomorphic covering of `S` by `D` whose fibres are the `Γ`-orbits. -/
def IsKleinUniformization {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) (D : TopologicalSpace.Opens ℂ) (p : ℂ → S) :
    Prop :=
  IsCoveringMap (fun z : D => p z) ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : D => p z) ∧
    p '' D = univ ∧ ∀ z ∈ D, ∀ w ∈ D, p z = p w ↔
      ∃ γ ∈ Γ, (γ 1 0 * z + γ 1 1 ≠ 0) ∧ w = (γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)

/-- **Theorem 24.1** (Bers, 同时单值化定理).  Two closed Riemann surfaces `S₀`, `S₁` of the same genus
`g > 1` can be uniformized by the same quasi-Fuchsian group: there are a quasi-Fuchsian group `Γ`
with invariant Jordan curve `C` (through `∞`) and complementary components `D`, `D*` such that
`S₀ = D/Γ` and `S₁ = D*/Γ`. -/
theorem thm24_1_simultaneous_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g) :
    ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) (C : Set ExtPlane)
      (D D' : TopologicalSpace.Opens ℂ) (p₀ : ℂ → S₀) (p₁ : ℂ → S₁),
      IsQuasiFuchsian Γ C ∧ extInf ∈ C ∧ AreComplementaryComponents C (toExt D) (toExt D') ∧
      IsKleinUniformization Γ D p₀ ∧ IsKleinUniformization Γ D' p₁ := by
  sorry

end LiZhongQC
