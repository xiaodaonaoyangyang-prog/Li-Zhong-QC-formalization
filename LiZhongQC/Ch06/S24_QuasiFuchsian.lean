import LiZhongQC.Ch06.S23_QCOnSurfaces
import LiZhongQC.Ch05.S21_UniversalTeichmuller
import LiZhongQC.Lemmas.DEDescent
import LiZhongQC.Lemmas.NielsenBoundary
import LiZhongQC.Lemmas.LowGenusQC

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

/-- The deck correspondence of a lift is onto: every `δ ∈ Γ₁` is `F ∘ γ ∘ F⁻¹` for some `γ ∈ Γ₀` (`h23l_deck` for
the lift `F⁻¹` of `f⁻¹`). -/
theorem s24q_deck_surj {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    {p₁ : UpperHalfPlane → S₁} (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁) {f : S₀ ≃ₜ S₁}
    {F : UpperHalfPlane ≃ₜ UpperHalfPlane} (hF : IsLift p₀ p₁ f F) {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hδ : δ ∈ Γ₁) : ∃ γ ∈ Γ₀, ∀ τ, F (γ • τ) = δ • F τ := by
  -- `F⁻¹` lifts `f⁻¹`
  have hFs : IsLift p₁ p₀ f.symm F.symm := by
    intro τ
    have h := hF (F.symm τ)
    rw [F.apply_symm_apply] at h
    rw [h, f.symm_apply_apply]
  obtain ⟨γ, hγ, hγδ⟩ := h23l_deck hp₁ hp₀ hFs hδ
  refine ⟨γ, hγ, fun τ => ?_⟩
  have h := hγδ (F τ)
  rw [F.symm_apply_apply] at h
  rw [← h, F.apply_symm_apply]

/-- An equivariant homeomorphism of `ℍ` whose deck correspondence is a bijection `Γ₀ ↔ Γ₁` descends to a
homeomorphism `S₀ → S₁`. -/
theorem s24q_descend {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    {p₁ : UpperHalfPlane → S₁} (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁)
    (E : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (h₀₁ : ∀ γ ∈ Γ₀, ∃ δ ∈ Γ₁, ∀ τ, E (γ • τ) = δ • E τ)
    (h₁₀ : ∀ δ ∈ Γ₁, ∃ γ ∈ Γ₀, ∀ τ, E (γ • τ) = δ • E τ) :
    ∃ q : S₀ ≃ₜ S₁, IsLift p₀ p₁ q E := by
  choose σ₀ hσ₀ using hp₀.2.2.1
  choose σ₁ hσ₁ using hp₁.2.2.1
  have hq₀ : IsQuotientMap p₀ :=
    hp₀.1.isOpenMap.isQuotientMap hp₀.1.continuous hp₀.2.2.1
  have hq₁ : IsQuotientMap p₁ :=
    hp₁.1.isOpenMap.isQuotientMap hp₁.1.continuous hp₁.2.2.1
  -- `q (p₀ τ) = p₁ (E τ)`
  have hfac : ∀ τ, p₁ (E (σ₀ (p₀ τ))) = p₁ (E τ) := by
    intro τ
    obtain ⟨γ, hγ, hγτ⟩ := (hp₀.2.2.2 (σ₀ (p₀ τ)) τ).1 (hσ₀ _)
    obtain ⟨δ, hδ, hE⟩ := h₀₁ γ hγ
    have h : E τ = δ • E (σ₀ (p₀ τ)) := by
      conv_lhs => rw [← hγτ]
      exact hE _
    rw [h]
    exact (hp₁.2.2.2 _ _).2 ⟨δ, hδ, rfl⟩
  -- `r (p₁ τ) = p₀ (E⁻¹ τ)`
  have hfac' : ∀ τ, p₀ (E.symm (σ₁ (p₁ τ))) = p₀ (E.symm τ) := by
    intro τ
    obtain ⟨δ, hδ, hδτ⟩ := (hp₁.2.2.2 (σ₁ (p₁ τ)) τ).1 (hσ₁ _)
    obtain ⟨γ, hγ, hE⟩ := h₁₀ δ hδ
    have h : E.symm τ = γ • E.symm (σ₁ (p₁ τ)) := by
      apply E.injective
      rw [E.apply_symm_apply, hE, E.apply_symm_apply, hδτ]
    rw [h]
    exact (hp₀.2.2.2 _ _).2 ⟨γ, hγ, rfl⟩
  set q : S₀ → S₁ := fun x => p₁ (E (σ₀ x)) with hqdef
  set r : S₁ → S₀ := fun y => p₀ (E.symm (σ₁ y)) with hrdef
  have hqp : ∀ τ, q (p₀ τ) = p₁ (E τ) := hfac
  have hrp : ∀ τ, r (p₁ τ) = p₀ (E.symm τ) := hfac'
  have hrq : ∀ x, r (q x) = x := by
    intro x
    obtain ⟨τ, rfl⟩ := hp₀.2.2.1 x
    rw [hqp, hrp, E.symm_apply_apply]
  have hqr : ∀ y, q (r y) = y := by
    intro y
    obtain ⟨τ, rfl⟩ := hp₁.2.2.1 y
    rw [hrp, hqp, E.apply_symm_apply]
  have hqc : Continuous q := by
    rw [hq₀.continuous_iff]
    have : q ∘ p₀ = p₁ ∘ E := funext hqp
    rw [this]
    exact hp₁.1.continuous.comp E.continuous
  have hrc : Continuous r := by
    rw [hq₁.continuous_iff]
    have : r ∘ p₁ = p₀ ∘ E.symm := funext hrp
    rw [this]
    exact hp₀.1.continuous.comp E.symm.continuous
  let Q : S₀ ≃ₜ S₁ :=
    { toFun := q, invFun := r, left_inv := hrq, right_inv := hqr,
      continuous_toFun := hqc, continuous_invFun := hrc }
  exact ⟨Q, fun τ => (hqp τ).symm⟩

/-- The converse of `h23l_lift_isKQC`: a homeomorphism whose lift is `K`-q.c. on `ℍ` is `K`-q.c. (the charts of the
projections are `1`-q.c., `h23l_chart_proj`). -/
theorem s24q_isKQCRS [IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    {p₁ : UpperHalfPlane → S₁} (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁) {q : S₀ ≃ₜ S₁}
    {E : UpperHalfPlane ≃ₜ UpperHalfPlane} (hq : IsLift p₀ p₁ q E) {K : ℝ}
    (hE : IsKQC (liftToC E) upperHalf K) : IsKQCRS q K := by
  refine ⟨hE.2.1, fun x => ?_⟩
  refine s23_lg (s23_localMapDomain_isOpen q.continuous x) hE.2.1 ?_ fun z₀ hz₀ => ?_
  · -- injectivity of the local expression
    intro a ha b hb hab
    have ha' := ha.1
    have hb' := hb.1
    have h1 : q ((chartAt ℂ x).symm a) = q ((chartAt ℂ x).symm b) :=
      (chartAt ℂ (q x)).injOn ha.2 hb.2 hab
    have h2 := q.injective h1
    rw [← (chartAt ℂ x).right_inv ha', ← (chartAt ℂ x).right_inv hb', h2]
  · -- near `z₀` the local expression is `ψ₁ ∘ E ∘ ψ₀⁻¹` with `1`-q.c. charts `ψᵢ` of the projections
    have hz₀t : z₀ ∈ (chartAt ℂ x).target := hz₀.1
    set y := (chartAt ℂ x).symm z₀ with hy
    have hys : y ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hz₀t
    have hqy : q y ∈ (chartAt ℂ (q x)).source := hz₀.2
    obtain ⟨τ₀, hτ₀⟩ := hp₀.2.2.1 y
    obtain ⟨U₀, hU₀o, hτU₀, hU₀H, hU₀s, hψ₀⟩ :=
      h23l_chart_proj (τ := τ₀) hp₀.1 hp₀.2.1 x (by rw [hτ₀]; exact hys)
    have hE₀ : p₁ (E τ₀) = q y := by rw [hq τ₀, hτ₀]
    obtain ⟨U₁, hU₁o, hτU₁, -, hU₁s, hψ₁⟩ :=
      h23l_chart_proj (τ := E τ₀) hp₁.1 hp₁.2.1 (q x) (by rw [hE₀]; exact hqy)
    set ψ₀ : ℂ → ℂ := fun z => chartAt ℂ x (p₀ (UpperHalfPlane.ofComplex z)) with hψ₀def
    set ψ₁ : ℂ → ℂ := fun z => chartAt ℂ (q x) (p₁ (UpperHalfPlane.ofComplex z)) with hψ₁def
    set V : Set ℂ := U₀ ∩ liftToC E ⁻¹' U₁ with hVdef
    have hV : IsOpen V :=
      ((h23l_liftToC_continuousOn E.continuous).mono hU₀H).isOpen_inter_preimage hU₀o hU₁o
    have hVH : V ⊆ upperHalf := fun z hz => hU₀H hz.1
    have hofc : ∀ z ∈ upperHalf, UpperHalfPlane.ofComplex (liftToC E z) = E (UpperHalfPlane.ofComplex z) := by
      intro z hz
      rw [h23l_liftToC_eq _ hz]
      exact UpperHalfPlane.ofComplex_apply _
    -- the key identity `L ∘ ψ₀ = ψ₁ ∘ liftToC E` on `V`
    have hkey : ∀ z ∈ V, localMapExpr q x (ψ₀ z) = ψ₁ (liftToC E z) := by
      intro z hz
      simp only [hψ₀def, hψ₁def, localMapExpr]
      rw [(chartAt ℂ x).left_inv (hU₀s z hz.1), hofc z (hVH hz), hq]
    have hdom : ∀ z ∈ V, ψ₀ z ∈ localMapDomain q x := by
      intro z hz
      refine ⟨(chartAt ℂ x).map_source (hU₀s z hz.1), ?_⟩
      show q ((chartAt ℂ x).symm (chartAt ℂ x (p₀ (UpperHalfPlane.ofComplex z)))) ∈ (chartAt ℂ (q x)).source
      rw [(chartAt ℂ x).left_inv (hU₀s z hz.1), ← hq, ← hofc z (hVH hz)]
      exact hU₁s _ hz.2
    have h0 := ac_t_isKQC_restrict hψ₀ hV inter_subset_left
    have h1 := thm7_1_comp (ac_t_isKQC_restrict hE hV hVH) hψ₁ (by
      rintro _ ⟨z, hz, rfl⟩
      exact hz.2)
    have h2 := thm7_1_comp (thm7_2_inv h0) h1 (by
      rintro _ ⟨w, ⟨z, hz, rfl⟩, rfl⟩
      exact Function.invFunOn_mem ⟨z, hz, rfl⟩)
    rw [one_mul, mul_one] at h2
    have hτ₀V : ((τ₀ : ℂ)) ∈ V := by
      refine ⟨hτU₀, ?_⟩
      show liftToC E (τ₀ : ℂ) ∈ U₁
      rw [h23l_liftToC_coe]
      exact hτU₁
    have hz₀W : z₀ ∈ ψ₀ '' V := by
      refine ⟨τ₀, hτ₀V, ?_⟩
      simp only [hψ₀def, UpperHalfPlane.ofComplex_apply, hτ₀, hy]
      exact (chartAt ℂ x).right_inv hz₀t
    refine ⟨ψ₀ '' V, (thm7_2_inv h0).1, hz₀W, ?_, ad_isKQC_congr h2 ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact hdom z hz
    · rintro _ ⟨z, hz, rfl⟩
      have hex : ∃ a ∈ V, ψ₀ a = ψ₀ z := ⟨z, hz, rfl⟩
      have hmem := Function.invFunOn_mem hex
      have heq := Function.invFunOn_eq hex
      simp only [Function.comp_apply]
      rw [← heq, hkey _ hmem, heq]

/-- Genus zero: the sphere models of both surfaces, then `s24q_genus_zero_of_model`. -/
theorem s24q_genus_zero [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] (h₀ : HasGenus S₀ 0)
    (h₁ : HasGenus S₁ 0) (f : S₀ ≃ₜ S₁) (hf : IsOrientationPreservingRS f) :
    ∃ q : S₀ ≃ₜ S₁, IsQCRS q ∧ ContinuousMap.Homotopic (f : C(S₀, S₁)) (q : C(S₀, S₁)) := by
  have : CompactSpace S₀ := h₀.1
  have : CompactSpace S₁ := h₁.1
  obtain ⟨c₀, hc₀⟩ := s24q_sphere_model h₀
  obtain ⟨c₁, hc₁⟩ := s24q_sphere_model h₁
  exact s24q_genus_zero_of_model hc₀ hc₁ f hf

/-- Genus one: the torus cover of both surfaces, then `s24q_torus_qc`. -/
theorem s24q_genus_one [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] (h₀ : HasGenus S₀ 1)
    (h₁ : HasGenus S₁ 1) (f : S₀ ≃ₜ S₁) (hf : IsOrientationPreservingRS f) :
    ∃ q : S₀ ≃ₜ S₁, IsQCRS q ∧ ContinuousMap.Homotopic (f : C(S₀, S₁)) (q : C(S₀, S₁)) := by
  obtain ⟨L₀, p₀, hp₀⟩ := s24q_torus_cover h₀
  obtain ⟨L₁, p₁, hp₁⟩ := s24q_torus_cover h₁
  exact s24q_torus_qc hp₀ hp₁ f hf

/-- Genus `> 1`: uniformize both surfaces (S22), lift `f`, take the Nielsen boundary map, its Douady–Earle extension
(equivariant by naturality, `sup |μ| < 1` by compactness), descend it, and compare the deck correspondences
(Theorem 23.1 with `γ₁ = 1`). -/
theorem s24q_genus_ge_two [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g) (h₀ : HasGenus S₀ g)
    (h₁ : HasGenus S₁ g) (f : S₀ ≃ₜ S₁) (hf : IsOrientationPreservingRS f) :
    ∃ q : S₀ ≃ₜ S₁, IsQCRS q ∧ ContinuousMap.Homotopic (f : C(S₀, S₁)) (q : C(S₀, S₁)) := by
  have : CompactSpace S₀ := h₀.1
  have : CompactSpace S₁ := h₁.1
  obtain ⟨Γ₀, p₀, hΓ₀, hfree₀, hp₀⟩ := s22hg_exists_fuchsian_uniformization hg h₀
  obtain ⟨Γ₁, p₁, hΓ₁, hfree₁, hp₁⟩ := s22hg_exists_fuchsian_uniformization hg h₁
  obtain ⟨τ₀⟩ : Nonempty UpperHalfPlane := inferInstance
  obtain ⟨τ₁, hτ₁⟩ := hp₁.2.2.1 (f (p₀ τ₀))
  obtain ⟨F, hF, -⟩ := exists_lift hp₀ hp₁ f τ₀ τ₁ hτ₁
  obtain ⟨φ, hφ, hφc, hor, hbd⟩ := s24q_boundary hΓ₀ hfree₀ hp₀ hΓ₁ hfree₁ hp₁ hf hF
  obtain ⟨E, hE, hC1, hlt⟩ := s24q_de_upper φ hφ hφc hor
  -- `E` has the deck correspondence of `F`
  have hFE : ∀ γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ ∈ Γ₀ → (∀ τ, F (γ • τ) = δ • F τ) →
      ∀ τ, E (γ • τ) = δ • E τ := fun γ δ hγ hγδ =>
    s24q_de_equivariant hφ hφc hE (hbd γ δ hγ hγδ)
  have h₀₁ : ∀ γ ∈ Γ₀, ∃ δ ∈ Γ₁, ∀ τ, E (γ • τ) = δ • E τ := by
    intro γ hγ
    obtain ⟨δ, hδ, hγδ⟩ := h23l_deck hp₀ hp₁ hF hγ
    exact ⟨δ, hδ, hFE γ δ hγ hγδ⟩
  have h₁₀ : ∀ δ ∈ Γ₁, ∃ γ ∈ Γ₀, ∀ τ, E (γ • τ) = δ • E τ := by
    intro δ hδ
    obtain ⟨γ, hγ, hγδ⟩ := s24q_deck_surj hp₀ hp₁ hF hδ
    exact ⟨γ, hγ, hFE γ δ hγ hγδ⟩
  obtain ⟨k, hk0, hk1, hk⟩ := s24q_sup_lt_one hp₀ hC1 hlt fun γ hγ => by
    obtain ⟨δ, -, h⟩ := h₀₁ γ hγ
    exact ⟨δ, h⟩
  obtain ⟨q, hq⟩ := s24q_descend hp₀ hp₁ E h₀₁ h₁₀
  refine ⟨q, ⟨_, s24q_isKQCRS hp₀ hp₁ hq (s24q_isKQC_of_bound hC1 hlt hk0 hk1 hk)⟩, ?_⟩
  -- Theorem 23.1 with `γ₁ = 1`: both lifts induce `γ ↦ δ`
  refine (thm23_1_homotopy_iff hp₀ hp₁ f q hF hq).2 ⟨1, Γ₁.one_mem, fun γ hγ τ => ?_⟩
  obtain ⟨δ, -, hγδ⟩ := h23l_deck hp₀ hp₁ hF hγ
  have hE' := hFE γ δ hγ hγδ
  rw [one_smul, inv_one, one_smul, hγδ, hE', Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

/-- §24.2: if `S₀` and `S₁` are closed Riemann surfaces of the same genus, every homotopy class of
orientation preserving homeomorphisms `S₀ → S₁` contains a quasiconformal map. -/
theorem exists_qc_in_homotopy_class [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (h₀ : HasGenus S₀ g)
    (h₁ : HasGenus S₁ g) (f : S₀ ≃ₜ S₁) (hf : IsOrientationPreservingRS f) :
    ∃ q : S₀ ≃ₜ S₁, IsQCRS q ∧ ContinuousMap.Homotopic (f : C(S₀, S₁)) (q : C(S₀, S₁)) := by
  rcases Nat.lt_or_ge 1 g with hg | hg
  · exact s24q_genus_ge_two hg h₀ h₁ f hf
  · interval_cases g
    · exact s24q_genus_zero h₀ h₁ f hf
    · exact s24q_genus_one h₀ h₁ f hf

/-- `p : ℂ → S` realizes `S` as `D/Γ` for a plane domain `D` invariant under the Klein group `Γ`:
a holomorphic covering of `S` by `D` whose fibres are the `Γ`-orbits. -/
def IsKleinUniformization {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) (D : TopologicalSpace.Opens ℂ) (p : ℂ → S) :
    Prop :=
  IsCoveringMap (fun z : D => p z) ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : D => p z) ∧
    p '' D = univ ∧ ∀ z ∈ D, ∀ w ∈ D, p z = p w ↔
      ∃ γ ∈ Γ, (γ 1 0 * z + γ 1 1 ≠ 0) ∧ w = (γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)

section bsu24_helpers

/-! ### `thm24_1` helper stubs (prefix `bsu24_`).  Route: the real mirror group `Γs = σ⁻¹ Γ₀ σ` (`σ τ = -τ̄`,
so `ℍ/Γs` is the mirror of `S₀`); an orientation preserving equivariant lift `κ = G ∘ σ : ℍ → ℍ` of the reversing
`f`; Douady–Earle `E`; `μ = μ_E` on `ℍ`; `fuchsian_deformation`; the two Klein uniformizations. -/

/-- The reflection `τ ↦ -τ̄` of `ℍ` as a homeomorphism. -/
theorem bsu24_x_sigma :
    ∃ σ : UpperHalfPlane ≃ₜ UpperHalfPlane, ∀ τ, ((σ τ : UpperHalfPlane) : ℂ) = -conj (τ : ℂ) := by
  let f : UpperHalfPlane → UpperHalfPlane := fun τ => ⟨-conj (τ : ℂ), by simpa using τ.im_pos⟩
  have hf : ∀ τ, ((f τ : UpperHalfPlane) : ℂ) = -conj (τ : ℂ) := fun _ => rfl
  have hff : ∀ τ, f (f τ) = τ := fun τ => UpperHalfPlane.ext (by rw [hf, hf]; simp)
  have hc : Continuous f := UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr (by
    have : (fun τ : UpperHalfPlane => (τ : ℂ)) ∘ f = fun τ : UpperHalfPlane => -conj (τ : ℂ) := funext hf
    rw [this]
    exact (Complex.continuous_conj.comp UpperHalfPlane.continuous_coe).neg)
  exact ⟨⟨⟨f, f, hff, hff⟩, hc, hc⟩, hf⟩

/-- Conjugation by `diag(1, -1)`: for every `γ₀ ∈ SL(2, ℝ)` there is `γ` with `σ ∘ γ = γ₀ ∘ σ`. -/
theorem bsu24_x_eps {σ : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hσ : ∀ τ, ((σ τ : UpperHalfPlane) : ℂ) = -conj (τ : ℂ))
    (γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ τ, σ (γ • τ) = γ₀ • σ τ := by
  have hdet := γ₀.det_coe
  rw [Matrix.det_fin_two] at hdet
  obtain ⟨γ, h00, h01, h10, h11⟩ : ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ 0 0 = γ₀ 0 0 ∧
      γ 0 1 = -γ₀ 0 1 ∧ γ 1 0 = -γ₀ 1 0 ∧ γ 1 1 = γ₀ 1 1 := by
    refine ⟨⟨!![γ₀ 0 0, -γ₀ 0 1; -γ₀ 1 0, γ₀ 1 1], ?_⟩, rfl, rfl, rfl, rfl⟩
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    linarith
  refine ⟨γ, fun τ => ?_⟩
  apply UpperHalfPlane.ext
  rw [hσ, h23l_b_coe_smul, h23l_b_coe_smul, hσ, h00, h01, h10, h11]
  simp only [Complex.ofReal_neg, map_div₀, map_add, map_mul, map_neg, Complex.conj_ofReal]
  rw [← neg_div]
  congr 1 <;> ring

/-- The mirror group: `Γs = {γ | σ γ σ⁻¹ ∈ Γ₀}` for the reflection `σ τ = -τ̄` of `ℍ` (conjugation by `diag(1,-1)`,
`[a b; c d] ↦ [a -b; -c d]`).  It is Fuchsian and free when `Γ₀` is. -/
theorem bsu24_mirror_group {Γ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ₀ : IsFuchsian Γ₀)
    (hfree₀ : ActsFreely Γ₀) :
    ∃ (Γs : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (σ : UpperHalfPlane ≃ₜ UpperHalfPlane),
      IsFuchsian Γs ∧ ActsFreely Γs ∧ (∀ τ, ((σ τ : UpperHalfPlane) : ℂ) = -conj (τ : ℂ)) ∧
      (∀ γ ∈ Γs, ∃ γ₀ ∈ Γ₀, ∀ τ, σ (γ • τ) = γ₀ • σ τ) ∧
      (∀ γ₀ ∈ Γ₀, ∃ γ ∈ Γs, ∀ τ, σ (γ • τ) = γ₀ • σ τ) := by
  obtain ⟨σ, hσ⟩ := bsu24_x_sigma
  choose ε hε using bsu24_x_eps hσ
  have hfaith : ∀ m : Matrix.SpecialLinearGroup (Fin 2) ℝ, (∀ τ : UpperHalfPlane, m • τ = τ) → m = 1 ∨ m = -1 :=
    fun m hm => utm_sl2_eq_of_bounded_displacement m (C := 0) fun z => by rw [hm z, dist_self]
  refine ⟨{ carrier := {γ | ∃ γ₀ ∈ Γ₀, ∀ τ, σ (γ • τ) = γ₀ • σ τ}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, σ, ?_, ?_, hσ, fun γ hγ => hγ, fun γ₀ hγ₀ => ?_⟩
  · rintro a b ⟨a₀, ha₀, ha⟩ ⟨b₀, hb₀, hb⟩
    exact ⟨a₀ * b₀, Γ₀.mul_mem ha₀ hb₀, fun τ => by rw [mul_smul, ha, hb, mul_smul]⟩
  · exact ⟨1, Γ₀.one_mem, fun τ => by rw [one_smul, one_smul]⟩
  · rintro a ⟨a₀, ha₀, ha⟩
    refine ⟨a₀⁻¹, Γ₀.inv_mem ha₀, fun τ => ?_⟩
    have h := ha (a⁻¹ • τ)
    rw [smul_inv_smul] at h
    rw [eq_inv_smul_iff]
    exact h.symm
  · -- Fuchsian
    intro C hC
    have hS := hΓ₀ (σ '' C) (hC.image σ.continuous)
    refine ((hS.image ε).union (hS.image fun g => -ε g)).subset ?_
    rintro γ ⟨⟨γ₀, hγ₀, hrel⟩, y, ⟨τ, hτ, rfl⟩, hy⟩
    have hsame : ∀ τ' : UpperHalfPlane, ((ε γ₀)⁻¹ * γ) • τ' = τ' := by
      intro τ'
      rw [mul_smul]
      have : γ • τ' = ε γ₀ • τ' := σ.injective (by rw [hrel, hε])
      rw [this, inv_smul_smul]
    rcases hfaith _ hsame with h | h
    · left
      exact ⟨γ₀, ⟨hγ₀, σ (γ • τ), ⟨σ τ, ⟨τ, hτ, rfl⟩, (hrel τ).symm⟩, ⟨_, hy, rfl⟩⟩, by rw [inv_mul_eq_one] at h; exact h⟩
    · right
      refine ⟨γ₀, ⟨hγ₀, σ (γ • τ), ⟨σ τ, ⟨τ, hτ, rfl⟩, (hrel τ).symm⟩, ⟨_, hy, rfl⟩⟩, ?_⟩
      rw [inv_mul_eq_iff_eq_mul] at h
      simp [h]
  · -- free action
    rintro γ ⟨γ₀, hγ₀, hrel⟩ (τ : UpperHalfPlane) hτ
    have h1 : γ₀ • σ τ = σ τ := by rw [← hrel, hτ]
    have h2 : ∀ τ' : UpperHalfPlane, γ • τ' = τ' := by
      intro τ'
      apply σ.injective
      rw [hrel]
      rcases hfree₀ γ₀ hγ₀ (σ τ) h1 with h | h
      · rw [h, one_smul]
      · rw [h]
        apply UpperHalfPlane.ext
        rw [h23l_b_coe_smul]
        simp
    exact hfaith γ h2
  · obtain ⟨γ, hγ⟩ := bsu24_x_eps hσ γ₀
    exact ⟨γ, ⟨γ₀, hγ₀, hγ⟩, hγ⟩

/-- A group covering a compact surface has a compact set of `ℍ` meeting every orbit; it transports along the
reflection `σ` to the mirror group (`σ` is a homeomorphism). -/
theorem bsu24_cocompact {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [CompactSpace X]
    {Γ₀ Γs : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → X}
    (hp₀ : IsUniformization Γ₀ p₀) (σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hs : ∀ γ₀ ∈ Γ₀, ∃ γ ∈ Γs, ∀ τ, σ (γ • τ) = γ₀ • σ τ) :
    ∃ K : Set UpperHalfPlane, IsCompact K ∧ ∀ τ : UpperHalfPlane, ∃ γ ∈ Γs, γ • τ ∈ K := by
  have hsurj := hp₀.2.2.1
  choose τs hτs using hsurj
  have hC : ∀ τ : UpperHalfPlane, ∃ C : Set UpperHalfPlane, IsCompact C ∧ C ∈ 𝓝 τ := fun τ =>
    exists_compact_mem_nhds τ
  choose C hCc hCn using hC
  obtain ⟨t, -, ht⟩ := (isCompact_univ (X := X)).elim_nhds_subcover (fun x => p₀ '' C (τs x)) fun x _ => by
    have h := hp₀.1.isOpenMap.image_mem_nhds (hCn (τs x))
    rwa [hτs x] at h
  set K₀ : Set UpperHalfPlane := ⋃ x ∈ t, C (τs x) with hK₀def
  have hK₀ : IsCompact K₀ := t.isCompact_biUnion fun x _ => hCc (τs x)
  have hcover : ∀ τ : UpperHalfPlane, ∃ κ ∈ K₀, p₀ κ = p₀ τ := by
    intro τ
    obtain ⟨x, hx, hmem⟩ := mem_iUnion₂.1 (ht (mem_univ (p₀ τ)))
    obtain ⟨κ, hκ, hκτ⟩ := hmem
    exact ⟨κ, mem_iUnion₂.2 ⟨x, hx, hκ⟩, hκτ⟩
  refine ⟨σ ⁻¹' K₀, ?_, fun τ => ?_⟩
  · have := hK₀.image σ.symm.continuous
    rwa [σ.symm.image_eq_preimage_symm, Homeomorph.symm_symm] at this
  · obtain ⟨κ, hκ, hκτ⟩ := hcover (σ τ)
    obtain ⟨γ₀, hγ₀, hγκ⟩ := (hp₀.2.2.2 (σ τ) κ).1 hκτ.symm
    obtain ⟨γ, hγ, hγσ⟩ := hs γ₀ hγ₀
    refine ⟨γ, hγ, ?_⟩
    show σ (γ • τ) ∈ K₀
    rw [hγσ, hγκ]
    exact hκ

/-- Every real number is a limit point of a Fuchsian group with a compact set meeting all orbits: for
`τ_k = x + i/(k+1)` pick `γ_k` with `γ_k τ_k ∈ K`; `dist (γ_k⁻¹ i) τ_k ≤ r` bounded, hence (`dist_coe_le`)
`γ_k⁻¹ i → x`. -/
theorem bsu24_x_real_limit {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {K : Set UpperHalfPlane}
    (hKc : IsCompact K) (hK : ∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, γ • τ ∈ K) (x : ℝ) :
    ((x : ℂ) : ExtPlane) ∈ limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) := by
  classical
  obtain ⟨r, hr⟩ := hKc.isBounded.subset_closedBall UpperHalfPlane.I
  have key : ∀ c : ℝ, ((x : ℂ) + (c : ℂ) * Complex.I).im = c := fun c => by simp
  let τ : ℕ → UpperHalfPlane := fun k =>
    ⟨(x : ℂ) + (((1 : ℝ) / ((k : ℝ) + 1) : ℝ) : ℂ) * Complex.I, by
      rw [key]; positivity⟩
  have hτre : ∀ k, (τ k : ℂ) = (x : ℂ) + (((1 : ℝ) / ((k : ℝ) + 1) : ℝ) : ℂ) * Complex.I := fun _ => rfl
  have hτim : ∀ k, (τ k).im = 1 / ((k : ℝ) + 1) := by
    intro k
    show ((τ k : ℂ)).im = _
    rw [hτre, key]
  choose γ hγΓ hγK using fun k => hK (τ k)
  set δ : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ := fun k => (γ k)⁻¹ with hδdef
  set w : ℕ → UpperHalfPlane := fun k => δ k • UpperHalfPlane.I with hwdef
  have hd : ∀ k, dist (w k) (τ k) ≤ r := by
    intro k
    have h1 : dist (γ k • w k) (γ k • τ k) = dist (w k) (τ k) := dist_smul (γ k) (w k) (τ k)
    have h2 : γ k • w k = UpperHalfPlane.I := smul_inv_smul (γ k) UpperHalfPlane.I
    rw [← h1, h2, dist_comm]
    exact mem_closedBall.1 (hr (hγK k))
  have hE : ∀ k, dist ((w k : ℂ)) ((τ k : ℂ)) ≤ (1 / ((k : ℝ) + 1)) * (Real.exp r - 1) := by
    intro k
    have h := UpperHalfPlane.dist_coe_le (w k) (τ k)
    rw [hτim] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have := Real.exp_le_exp.2 (hd k)
    linarith
  have hτx : ∀ k, dist ((τ k : ℂ)) (x : ℂ) = 1 / ((k : ℝ) + 1) := by
    intro k
    rw [hτre, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hlim : Tendsto (fun k => (w k : ℂ)) atTop (𝓝 (x : ℂ)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hb : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) * (Real.exp r - 1 + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (Real.exp r - 1 + 1)
    refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) hb
    calc dist (w k : ℂ) (x : ℂ) ≤ dist (w k : ℂ) (τ k : ℂ) + dist (τ k : ℂ) (x : ℂ) := dist_triangle _ _ _
      _ ≤ (1 / ((k : ℝ) + 1)) * (Real.exp r - 1) + 1 / ((k : ℝ) + 1) := by
        rw [hτx]
        exact add_le_add (hE k) le_rfl
      _ = (1 / ((k : ℝ) + 1)) * (Real.exp r - 1 + 1) := by ring
  have him : Tendsto (fun k => (w k).im) atTop (𝓝 0) := by
    have := (Complex.continuous_im.tendsto _).comp hlim
    simpa [Function.comp_def] using this
  have hinf : (range δ).Infinite := by
    intro hfin
    have hfin' : (range w).Finite :=
      (hfin.image (fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ => g • UpperHalfPlane.I)).subset
        (by rintro _ ⟨k, rfl⟩; exact ⟨δ k, ⟨k, rfl⟩, rfl⟩)
    obtain ⟨a, ⟨k0, rfl⟩, hmin⟩ :=
      Set.exists_min_image (range w) (fun t : UpperHalfPlane => t.im) hfin' ⟨w 0, 0, rfl⟩
    obtain ⟨k, hk⟩ := (him.eventually (gt_mem_nhds (w k0).im_pos)).exists
    exact absurd (hmin (w k) ⟨k, rfl⟩) (not_le.2 hk)
  obtain ⟨φ, hφ, hinjφ⟩ := k24_c_exists_injective_subseq hinf
  have hmapinj : Function.Injective (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) :
      Matrix.SpecialLinearGroup (Fin 2) ℝ → Matrix.SpecialLinearGroup (Fin 2) ℂ) := by
    intro a b hab
    ext i j
    have := congrArg (fun m : Matrix.SpecialLinearGroup (Fin 2) ℂ => m i j) hab
    simp only [k24_c_map_apply] at this
    exact_mod_cast this
  refine ⟨((Complex.I : ℂ) : ExtPlane),
    fun n => ⟨Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) (δ (φ n)),
      Subgroup.mem_map_of_mem _ (Γ.inv_mem (hγΓ (φ n)))⟩, ?_, ?_⟩
  · intro m n hmn
    exact hinjφ (hmapinj (congrArg Subtype.val hmn))
  · have hval : ∀ n, mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) (δ (φ n)))
        ((Complex.I : ℂ) : ExtPlane) = ((w (φ n) : ℂ) : ExtPlane) := by
      intro n
      rw [k24_c_mobiusSL_map, mobiusExt_coe (k24_d_den_ne_zero (k24_det_realR _) (by simp))]
      congr 1
      exact (h23l_b_coe_smul (δ (φ n)) UpperHalfPlane.I).symm
    simp only [hval]
    exact (OnePoint.continuous_coe.tendsto _).comp (hlim.comp hφ)

/-- A Fuchsian group with a compact set meeting every orbit has more than two limit points (so
`fuchsian_deformation` applies). -/
theorem bsu24_limitSet {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) {K : Set UpperHalfPlane} (hKc : IsCompact K)
    (hK : ∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, γ • τ ∈ K) :
    2 < (limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)))).encard := by
  have h0 := bsu24_x_real_limit hKc hK 0
  have h1 := bsu24_x_real_limit hKc hK 1
  have h2 := bsu24_x_real_limit hKc hK 2
  have hsub : ({((((0 : ℝ) : ℂ)) : ExtPlane), ((((1 : ℝ) : ℂ)) : ExtPlane), ((((2 : ℝ) : ℂ)) : ExtPlane)} :
      Set ExtPlane) ⊆ limitSet (Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ))) := by
    intro p hp
    rcases hp with rfl | rfl | rfl <;> assumption
  have hne01 : ((((0 : ℝ) : ℂ)) : ExtPlane) ≠ ((((1 : ℝ) : ℂ)) : ExtPlane) := fun h => by
    have := OnePoint.coe_injective h
    norm_num at this
  have hne02 : ((((0 : ℝ) : ℂ)) : ExtPlane) ≠ ((((2 : ℝ) : ℂ)) : ExtPlane) := fun h => by
    have := OnePoint.coe_injective h
    norm_num at this
  have hne12 : ((((1 : ℝ) : ℂ)) : ExtPlane) ≠ ((((2 : ℝ) : ℂ)) : ExtPlane) := fun h => by
    have := OnePoint.coe_injective h
    norm_num at this
  refine lt_of_lt_of_le ?_ (Set.encard_le_encard hsub)
  rw [Set.encard_insert_of_notMem (by simp [hne01, hne02]), Set.encard_pair hne12]
  norm_num

/-- Complex conjugation reverses the standard circle parameter. -/
theorem bsu24_rev_circle_conj (z : ℂ) (ρ t : ℝ) :
    conj (z + ρ * Complex.exp (2 * π * I * t)) =
      conj z + ρ * Complex.exp (2 * π * I * ((1 - t : ℝ) : ℂ)) := by
  have he : Complex.exp (2 * π * I * ((1 - t : ℝ) : ℂ)) =
      conj (Complex.exp (2 * π * I * t)) := by
    rw [← Complex.exp_conj]
    have ha : 2 * π * I * ((1 - t : ℝ) : ℂ) =
        2 * π * I + conj (2 * π * I * t) := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
      push_cast
      ring
    rw [ha, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]
  rw [map_add, map_mul, Complex.conj_ofReal, he]

/-- Double conjugation preserves local winding +1: the parameter reversal and conjugation
of the imaginary logarithmic increment contribute opposite signs. -/
theorem bsu24_rev_winding_conj_conj {F : ℂ → ℂ} {z₀ : ℂ}
    (hw : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ,
      ContinuousOn Lg (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (Lg t) =
        F (z₀ + ρ * Complex.exp (2 * π * I * t)) - F z₀) →
      Lg 1 - Lg 0 = 2 * π * I) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ,
      ContinuousOn Lg (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (Lg t) =
        conj (F (conj (conj z₀ + ρ * Complex.exp (2 * π * I * t)))) -
          conj (F z₀)) →
      Lg 1 - Lg 0 = 2 * π * I := by
  obtain ⟨ρ₁, hρ₁, hw⟩ := hw
  refine ⟨ρ₁, hρ₁, ?_⟩
  intro ρ hρ hρlt Lg hLg hLe
  have ht : MapsTo (fun t : ℝ => 1 - t) (Icc 0 1) (Icc 0 1) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hMc : ContinuousOn (fun t : ℝ => conj (Lg (1 - t))) (Icc 0 1) :=
    Complex.continuous_conj.comp_continuousOn
      (hLg.comp (continuous_const.sub continuous_id).continuousOn ht)
  have hMe : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (conj (Lg (1 - t))) =
      F (z₀ + ρ * Complex.exp (2 * π * I * t)) - F z₀ := by
    intro t hti
    rw [Complex.exp_conj, hLe (1 - t) (ht hti), map_sub, Complex.conj_conj,
      Complex.conj_conj, bsu24_rev_circle_conj, Complex.conj_conj]
    have htime : (1 : ℝ) - (1 - t) = t := by ring
    rw [htime]
  have h := hw ρ hρ hρlt _ hMc hMe
  simp only [sub_self, sub_zero] at h
  have hc := congrArg (fun z : ℂ => conj z) h
  simp only [map_sub, Complex.conj_conj, map_mul, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I] at hc
  linear_combination -hc

/-- A reversing local expression becomes preserving after conjugating the target and
negating the source. This reuses LocalWinding with holomorphic transformed charts. -/
theorem bsu24_rev_reflected_chart_winding {F h ψ₀ ψ₁ : ℂ → ℂ} {z₀ : ℂ} {U V D : Set ℂ}
    (hU : IsOpen U) (hz₀ : z₀ ∈ U) (hV : IsOpen V) (hD : IsOpen D)
    (hψ₀ : DifferentiableOn ℂ ψ₀ U) (hψ₀i : InjOn ψ₀ U)
    (hψ₁ : DifferentiableOn ℂ ψ₁ V) (hψ₁i : InjOn ψ₁ V)
    (hFc : ContinuousAt F z₀) (hFz : F z₀ ∈ V) (hψD : MapsTo ψ₀ U D)
    (hcomm : ∀ z ∈ U, F z ∈ V → ψ₁ (F z) = h (ψ₀ z))
    (hhc : ContinuousOn h D) (hhi : InjOn h D)
    (hhs : IsSensePreserving (fun z => conj (h z)) D) :
    ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ,
      ContinuousOn Lg (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (Lg t) =
        conj (F (-(-z₀ + ρ * Complex.exp (2 * π * I * t)))) - conj (F z₀)) →
      Lg 1 - Lg 0 = 2 * π * I := by
  have hUd : IsOpen ((fun z : ℂ => -z) ⁻¹' U) := hU.preimage continuous_neg
  have hVd : IsOpen ((fun z : ℂ => conj z) ⁻¹' V) :=
    hV.preimage Complex.continuous_conj
  have hs : DifferentiableOn ℂ (fun z => ψ₀ (-z)) ((fun z : ℂ => -z) ⁻¹' U) :=
    hψ₀.comp differentiable_neg.differentiableOn (fun z hz => hz)
  have hsi : InjOn (fun z => ψ₀ (-z)) ((fun z : ℂ => -z) ⁻¹' U) := by
    intro z hz w hw h
    exact neg_injective (hψ₀i hz hw h)
  have hd : DifferentiableOn ℂ (fun z => conj (ψ₁ (conj z)))
      ((fun z : ℂ => conj z) ⁻¹' V) := by
    intro z hz
    have h := (hψ₁.differentiableAt (hV.mem_nhds hz)).conj_conj
    convert! h.differentiableWithinAt using 1 <;>
      simp only [Function.comp_def, Complex.conj_conj]
  have hdi : InjOn (fun z => conj (ψ₁ (conj z))) ((fun z : ℂ => conj z) ⁻¹' V) := by
    intro z hz w hw h
    exact (starRingEnd ℂ).injective (hψ₁i hz hw ((starRingEnd ℂ).injective h))
  have hFc' : ContinuousAt (fun z => conj (F (-z))) (-z₀) := by
    have hFc₀ : ContinuousAt F (-(-z₀)) := by simpa only [neg_neg] using hFc
    exact Complex.continuous_conj.continuousAt.comp
      (hFc₀.comp (continuous_neg.continuousAt : ContinuousAt (fun z : ℂ => -z) (-z₀)))
  have hw := s24q_lw_winding_conj
    (F := fun z => conj (F (-z))) (h := fun z => conj (h z))
    (ψ₀ := fun z => ψ₀ (-z)) (ψ₁ := fun z => conj (ψ₁ (conj z)))
    (z₀ := -z₀) (U := (fun z : ℂ => -z) ⁻¹' U) (V := (fun z : ℂ => conj z) ⁻¹' V)
    (D := D) hUd (by simpa only [mem_preimage, neg_neg] using hz₀) hVd hD
    hs hsi hd hdi hFc' (by simpa only [mem_preimage, neg_neg, Complex.conj_conj] using hFz)
    (fun z hz => hψD hz) (by
      intro z hz hVz
      have hFz' : F (-z) ∈ V := by simpa only [mem_preimage, Complex.conj_conj] using hVz
      simpa only [Complex.conj_conj] using congrArg (fun w : ℂ => conj w) (hcomm (-z) hz hFz'))
    (Complex.continuous_conj.comp_continuousOn hhc)
    (fun z hz w hw h => hhi hz hw ((starRingEnd ℂ).injective h)) hhs
  simpa only [neg_neg] using hw

/-- The real reflection in the frozen interface acts on liftToC by z ↦ -conj z.
Both arguments lie in the upper half-plane simultaneously, including the off-domain branch. -/
theorem bsu24_rev_lift_sigma (G σ : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hσ : ∀ τ, ((σ τ : UpperHalfPlane) : ℂ) = -conj (τ : ℂ)) (z : ℂ) :
    liftToC (σ.trans G) z = liftToC G (-conj z) := by
  have him : (-conj z).im = z.im := by simp
  by_cases hz : 0 < z.im
  · let τ : UpperHalfPlane := ⟨z, hz⟩
    have h₁ := h23l_liftToC_coe (σ.trans G) τ
    have h₂ := h23l_liftToC_coe G (σ τ)
    rw [hσ] at h₂
    exact h₁.trans h₂.symm
  · simp only [liftToC, hz, him, ↓reduceDIte]

/-- **Reversing lift.**  A lift `G` of the reversing `f` (`exists_lift`) is reversing on `ℍ`; `κ = G ∘ σ` is a
homeomorphism of `ℍ` with `p₁ ∘ κ = f ∘ p₀ ∘ σ` which is of local winding `+1` (local expressions: `liftToC κ` is
locally `ψ₁⁻¹ ∘ L ∘ conj ∘ (conj ∘ ψ₀ ∘ σ̃)`; the local winding `+1` comes from `rc_hloc_of_sensePreserving` applied to
`conj ∘ L`).  Lift-level: no conjugate surface type is needed. -/
theorem bsu24_reversing_lift [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁]
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    {p₁ : UpperHalfPlane → S₁} (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁)
    {f : S₀ ≃ₜ S₁}
    (hf : ∀ x : S₀, IsSensePreserving (fun z => conj (localMapExpr f x z)) (localMapDomain f x))
    {σ : UpperHalfPlane ≃ₜ UpperHalfPlane} (hσ : ∀ τ, ((σ τ : UpperHalfPlane) : ℂ) = -conj (τ : ℂ)) :
    ∃ κ : UpperHalfPlane ≃ₜ UpperHalfPlane, (∀ τ, p₁ (κ τ) = f (p₀ (σ τ))) ∧
      (∀ τ : UpperHalfPlane, ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ,
        ContinuousOn Lg (Set.Icc 0 1) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) =
          liftToC κ ((τ : ℂ) + ρ * Complex.exp (2 * π * Complex.I * t)) - liftToC κ (τ : ℂ)) →
        Lg 1 - Lg 0 = 2 * π * Complex.I) := by
  obtain ⟨τ₀⟩ : Nonempty UpperHalfPlane := inferInstance
  obtain ⟨τ₁, hτ₁⟩ := hp₁.2.2.1 (f (p₀ τ₀))
  obtain ⟨G, hG, -⟩ := exists_lift hp₀ hp₁ f τ₀ τ₁ hτ₁
  refine ⟨σ.trans G, fun τ => hG (σ τ), ?_⟩
  intro τ
  obtain ⟨U₀, hU₀o, hτU₀, hU₀H, hU₀s, hψ₀⟩ :=
    h23l_chart_proj (τ := σ τ) hp₀.1 hp₀.2.1 (p₀ (σ τ)) (mem_chart_source ℂ _)
  obtain ⟨U₁, hU₁o, hτU₁, -, -, hψ₁⟩ :=
    h23l_chart_proj (τ := G (σ τ)) hp₁.1 hp₁.2.1 (p₁ (G (σ τ))) (mem_chart_source ℂ _)
  have hFx : p₁ (G (σ τ)) = f (p₀ (σ τ)) := hG (σ τ)
  have hkey : ∀ z ∈ U₀, chartAt ℂ (p₁ (G (σ τ))) (p₁ (UpperHalfPlane.ofComplex (liftToC G z))) =
      localMapExpr f (p₀ (σ τ)) (chartAt ℂ (p₀ (σ τ)) (p₀ (UpperHalfPlane.ofComplex z))) := by
    intro z hz
    rw [h23l_liftToC_eq G (hU₀H hz), UpperHalfPlane.ofComplex_apply, hFx, hG (UpperHalfPlane.ofComplex z)]
    unfold localMapExpr
    rw [(chartAt ℂ (p₀ (σ τ))).left_inv (hU₀s z hz)]
  set V : Set ℂ := (U₀ ∩ liftToC G ⁻¹' U₁) ∩
    (fun z => chartAt ℂ (p₀ (σ τ)) (p₀ (UpperHalfPlane.ofComplex z))) ⁻¹'
      localMapDomain f (p₀ (σ τ)) with hVdef
  have hV : IsOpen V :=
    (hψ₀.2.2.1.1.mono inter_subset_left).isOpen_inter_preimage
      (((h23l_liftToC_continuousOn G.continuous).mono hU₀H).isOpen_inter_preimage hU₀o hU₁o)
      (s23_localMapDomain_isOpen f.continuous _)
  have hτV : ((σ τ : UpperHalfPlane) : ℂ) ∈ V := by
    refine ⟨⟨hτU₀, ?_⟩, ?_⟩
    · show liftToC G (σ τ : ℂ) ∈ U₁
      rw [h23l_liftToC_coe]
      exact hτU₁
    · have e : UpperHalfPlane.ofComplex (σ τ : ℂ) = σ τ := UpperHalfPlane.ofComplex_apply (σ τ)
      simp only [mem_preimage, e]
      exact (s23_h_center f _).1
  have hc₀ := thm7_3_one_qc_conformal hψ₀
  have hc₁ := thm7_3_one_qc_conformal hψ₁
  have hGc : ContinuousAt (liftToC G) (σ τ : ℂ) :=
    (h23l_liftToC_continuousOn G.continuous).continuousAt
      (isOpen_upperHalf.mem_nhds (σ τ).coe_im_pos)
  have hw := bsu24_rev_reflected_chart_winding (F := liftToC G)
    (U := V) (V := U₁) (D := localMapDomain f (p₀ (σ τ)))
    (ψ₀ := fun z => chartAt ℂ (p₀ (σ τ)) (p₀ (UpperHalfPlane.ofComplex z)))
    (ψ₁ := fun z => chartAt ℂ (p₁ (G (σ τ))) (p₁ (UpperHalfPlane.ofComplex z)))
    (h := localMapExpr f (p₀ (σ τ))) hV hτV hψ₁.1 (s23_localMapDomain_isOpen f.continuous _)
    (hc₀.1.mono (fun z hz => hz.1.1)) (hc₀.2.1.mono (fun z hz => hz.1.1))
    hc₁.1 hc₁.2.1 hGc (by rw [h23l_liftToC_coe]; exact hτU₁)
    (fun z hz => hz.2) (fun z hz _ => hkey z hz.1.1)
    (s24q_nb_localMapExpr_continuousOn f.continuous _)
    (s23_c1_injOn_localMapExpr f.injective _) (hf _)
  have hw' := bsu24_rev_winding_conj_conj
    (F := fun z => conj (liftToC G (-z))) (z₀ := -(σ τ : ℂ)) (by simpa only [neg_neg] using hw)
  have hcenter : conj (-(σ τ : ℂ)) = (τ : ℂ) := by
    rw [hσ, neg_neg, Complex.conj_conj]
  obtain ⟨ρ₁, hρ₁, hw'⟩ := hw'
  refine ⟨ρ₁, hρ₁, ?_⟩
  intro ρ hρ hρlt Lg hLg hLe
  apply hw' ρ hρ hρlt Lg hLg
  intro t ht
  simpa only [hcenter, Complex.conj_conj, neg_neg, hσ,
    bsu24_rev_lift_sigma G σ hσ] using hLe t ht

/-- The deck correspondence of `κ`: from `p₁ ∘ κ = f ∘ p₀ ∘ σ`, both directions (uniqueness of lifts,
as `h23l_deck` / `s24q_deck_surj`). -/
theorem bsu24_deck [T2Space S₀] [T2Space S₁]
    {Γ₀ Γ₁ Γs : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    {p₁ : UpperHalfPlane → S₁} (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁)
    {f : S₀ ≃ₜ S₁} {σ κ : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hs₁ : ∀ γ ∈ Γs, ∃ γ₀ ∈ Γ₀, ∀ τ, σ (γ • τ) = γ₀ • σ τ)
    (hs₂ : ∀ γ₀ ∈ Γ₀, ∃ γ ∈ Γs, ∀ τ, σ (γ • τ) = γ₀ • σ τ)
    (hκ : ∀ τ, p₁ (κ τ) = f (p₀ (σ τ))) :
    (∀ γ ∈ Γs, ∃ δ ∈ Γ₁, ∀ τ, κ (γ • τ) = δ • κ τ) ∧
      (∀ δ ∈ Γ₁, ∃ γ ∈ Γs, ∀ τ, κ (γ • τ) = δ • κ τ) := by
  have hfib₁ : ∀ τ (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ), δ ∈ Γ₁ → p₁ (δ • τ) = p₁ τ :=
    fun τ δ hδ => ((hp₁.2.2.2 τ (δ • τ)).2 ⟨δ, hδ, rfl⟩).symm
  have hfib₀ : ∀ τ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ), γ ∈ Γ₀ → p₀ (γ • τ) = p₀ τ :=
    fun τ γ hγ => ((hp₀.2.2.2 τ (γ • τ)).2 ⟨γ, hγ, rfl⟩).symm
  -- uniqueness of lifts
  have key : ∀ γ ∈ Γs, ∀ δ ∈ Γ₁, κ (γ • UpperHalfPlane.I) = δ • κ UpperHalfPlane.I →
      ∀ τ, κ (γ • τ) = δ • κ τ := by
    intro γ hγ δ hδ hbase
    obtain ⟨γ₀, hγ₀, hrel⟩ := hs₁ γ hγ
    have hcomp : p₁ ∘ (fun τ => κ (γ • τ)) = p₁ ∘ (fun τ => δ • κ τ) := by
      funext τ
      simp only [Function.comp_apply]
      rw [hκ, hrel, hfib₀ _ _ hγ₀, hfib₁ _ _ hδ, hκ]
    have h := hp₁.1.eq_of_comp_eq (κ.continuous.comp (continuous_const_smul γ))
      ((continuous_const_smul δ).comp κ.continuous) hcomp UpperHalfPlane.I hbase
    exact fun τ => congrFun h τ
  refine ⟨fun γ hγ => ?_, fun δ hδ => ?_⟩
  · obtain ⟨γ₀, hγ₀, hrel⟩ := hs₁ γ hγ
    have h0 : p₁ (κ UpperHalfPlane.I) = p₁ (κ (γ • UpperHalfPlane.I)) := by
      rw [hκ, hκ, hrel, hfib₀ _ _ hγ₀]
    obtain ⟨δ, hδ, hδe⟩ := (hp₁.2.2.2 _ _).1 h0
    exact ⟨δ, hδ, key γ hγ δ hδ hδe.symm⟩
  · set q : UpperHalfPlane := κ.symm (δ • κ UpperHalfPlane.I) with hq
    have hκq : κ q = δ • κ UpperHalfPlane.I := κ.apply_symm_apply _
    have h1 : p₀ (σ UpperHalfPlane.I) = p₀ (σ q) := by
      apply f.injective
      rw [← hκ, ← hκ, hκq, hfib₁ _ _ hδ]
    obtain ⟨γ₀, hγ₀, hγ₀e⟩ := (hp₀.2.2.2 _ _).1 h1
    obtain ⟨γ, hγ, hrel⟩ := hs₂ γ₀ hγ₀
    have hγq : γ • UpperHalfPlane.I = q := by
      apply σ.injective
      rw [hrel, hγ₀e]
    refine ⟨γ, hγ, key γ hγ δ hδ ?_⟩
    rw [hγq, hκq]

/-- **Douady–Earle for the mirror group**: the Nielsen boundary map of the preserving equivariant `κ`
(`s24q_boundary` with the orientation hypothesis read off `κ`), its extension `E` (`s24q_de_upper`), equivariant
with the same deck correspondence (`s24q_de_equivariant`). -/
theorem bsu24_de {Γs Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓs : IsFuchsian Γs)
    (hfrees : ActsFreely Γs) (hΓ₁ : IsFuchsian Γ₁) (hfree₁ : ActsFreely Γ₁) {K : Set UpperHalfPlane}
    (hKc : IsCompact K) (hK : ∀ τ : UpperHalfPlane, ∃ γ ∈ Γs, γ • τ ∈ K)
    {κ : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hκ : (∀ τ : UpperHalfPlane, ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ,
        ContinuousOn Lg (Set.Icc 0 1) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) =
          liftToC κ ((τ : ℂ) + ρ * Complex.exp (2 * π * Complex.I * t)) - liftToC κ (τ : ℂ)) →
        Lg 1 - Lg 0 = 2 * π * Complex.I))
    (hd₁ : ∀ γ ∈ Γs, ∃ δ ∈ Γ₁, ∀ τ, κ (γ • τ) = δ • κ τ)
    (hd₂ : ∀ δ ∈ Γ₁, ∃ γ ∈ Γs, ∀ τ, κ (γ • τ) = δ • κ τ) :
    ∃ E : UpperHalfPlane ≃ₜ UpperHalfPlane, ContDiffOn ℝ 1 (liftToC E) upperHalf ∧
      (∀ z ∈ upperHalf, ‖dzbar (liftToC E) z‖ < ‖dz (liftToC E) z‖) ∧
      ∀ γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ ∈ Γs → (∀ τ, κ (γ • τ) = δ • κ τ) →
        ∀ τ, E (γ • τ) = δ • E τ := by
  have hK₀ : ∃ K' : Set UpperHalfPlane, IsCompact K' ∧ ∀ z, ∃ γ ∈ Γs, γ • z ∈ K' := ⟨K, hKc, hK⟩
  have hK₁ : ∃ K' : Set UpperHalfPlane, IsCompact K' ∧ ∀ z, ∃ δ ∈ Γ₁, δ • z ∈ K' := by
    refine ⟨κ '' K, hKc.image κ.continuous, fun w => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hK (κ.symm w)
    obtain ⟨δ, hδ, h⟩ := hd₁ γ hγ
    exact ⟨δ, hδ, γ • κ.symm w, hγK, by rw [h, κ.apply_symm_apply]⟩
  obtain ⟨L, c, hL, hc, hqi⟩ := s24q_nb_qi κ hK₀ hK₁ hd₁ hd₂
  obtain ⟨L', c', hL', hc', hqi'⟩ := s24q_nb_qi κ.symm hK₁ hK₀
    (fun δ hδ => by
      obtain ⟨γ, hγ, h⟩ := hd₂ δ hδ
      exact ⟨γ, hγ, fun τ => by
        have := h (κ.symm τ)
        rw [Homeomorph.apply_symm_apply] at this
        rw [← this]; simp⟩)
    (fun γ hγ => by
      obtain ⟨δ, hδ, h⟩ := hd₁ γ hγ
      exact ⟨δ, hδ, fun τ => by
        have := h (κ.symm τ)
        rw [Homeomorph.apply_symm_apply] at this
        rw [← this]; simp⟩)
  obtain ⟨φ, hφc, hφ⟩ := s24q_nb_limit κ L c hL hc hqi
  obtain ⟨ψ, hψc, hψ⟩ := s24q_nb_limit κ.symm L' c' hL' hc' hqi'
  have h1 := s24q_nb_inverse_limit κ hφ hψ
  have h2 : ∀ ζ : Circle, φ (ψ ζ) = ζ := s24q_nb_inverse_limit κ.symm hψ (by simpa using hφ)
  have hbij : Function.Bijective φ :=
    ⟨fun a b hab => by rw [← h1 a, ← h1 b, hab], fun ζ => ⟨ψ ζ, h2 ζ⟩⟩
  have hw := hκ
  have hinc := s24q_nb_increasing hw hbij hφc hφ
  obtain ⟨E, hE, hC1, hlt⟩ := s24q_de_upper φ hbij hφc hinc
  exact ⟨E, hC1, hlt, fun γ δ _ hγδ =>
    s24q_de_equivariant hbij hφc hE fun ζ ζ' h => s24q_nb_equivariant κ hφ γ δ hγδ ζ ζ' h⟩

/-- The Beltrami coefficient `μ = μ_E` (zero off `ℍ`): `sup |μ| < 1` by cocompactness (`s24q_sup_lt_one` with a
compact set instead of a surface) and `IsGammaCompatible Γs μ` from `h23l_dilatation_conj`. -/
theorem bsu24_beltrami {Γs : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {K : Set UpperHalfPlane}
    (hKc : IsCompact K) (hK : ∀ τ : UpperHalfPlane, ∃ γ ∈ Γs, γ • τ ∈ K)
    {E : UpperHalfPlane ≃ₜ UpperHalfPlane} (hC1 : ContDiffOn ℝ 1 (liftToC E) upperHalf)
    (hlt : ∀ z ∈ upperHalf, ‖dzbar (liftToC E) z‖ < ‖dz (liftToC E) z‖)
    (heq : ∀ γ ∈ Γs, ∃ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ τ, E (γ • τ) = δ • E τ) :
    ∃ μ : BeltramiH, IsGammaCompatible Γs μ.1 ∧
      ∀ z ∈ upperHalf, μ.1 z = complexDilatation (liftToC E) z := by
  classical
  -- continuity of the dilatation on `ℍ`
  have hfd : ContinuousOn (fderiv ℝ (liftToC E)) upperHalf :=
    hC1.continuousOn_fderiv_of_isOpen isOpen_upperHalf le_rfl
  have hdzc : ContinuousOn (dz (liftToC E)) upperHalf := by
    unfold dz
    exact (((hfd.clm_apply continuousOn_const).sub
      (continuousOn_const.mul (hfd.clm_apply continuousOn_const))).div_const _)
  have hdzbarc : ContinuousOn (dzbar (liftToC E)) upperHalf := by
    unfold dzbar
    exact (((hfd.clm_apply continuousOn_const).add
      (continuousOn_const.mul (hfd.clm_apply continuousOn_const))).div_const _)
  have hdz0 : ∀ z ∈ upperHalf, dz (liftToC E) z ≠ 0 := fun z hz h => by
    have := hlt z hz
    rw [h, norm_zero] at this
    exact absurd this (not_lt.2 (norm_nonneg _))
  have hdilc : ContinuousOn (complexDilatation (liftToC E)) upperHalf := by
    unfold complexDilatation
    exact hdzbarc.div hdzc hdz0
  have hμc : ContinuousOn (fun z => ‖complexDilatation (liftToC E) z‖) upperHalf := hdilc.norm
  have hμlt : ∀ z ∈ upperHalf, ‖complexDilatation (liftToC E) z‖ < 1 := by
    intro z hz
    unfold complexDilatation
    rw [norm_div, div_lt_one (norm_pos_iff.2 (hdz0 z hz))]
    exact hlt z hz
  set m : UpperHalfPlane → ℝ := fun τ => ‖complexDilatation (liftToC E) τ‖ with hmdef
  have hmc : Continuous m :=
    hμc.comp_continuous UpperHalfPlane.continuous_coe fun τ => τ.coe_im_pos
  -- `|μ|` is `Γs`-invariant
  have hinv : ∀ γ ∈ Γs, ∀ κ : UpperHalfPlane, m (γ • κ) = m κ := by
    intro γ hγ κ
    obtain ⟨δ, hδ⟩ := heq γ hγ
    have h := h23l_dilatation_conj hδ κ.coe_im_pos
    have hden := h23l_b_den_ne γ κ.coe_im_pos
    have hfac : ‖(((γ 1 0 : ℂ) * κ + γ 1 1) ^ 2 / conj (((γ 1 0 : ℂ) * κ + γ 1 1) ^ 2))‖ = 1 := by
      rw [norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 (pow_ne_zero _ hden))]
    simp only [hmdef]
    rw [h, norm_mul, hfac, mul_one, h23l_b_coe_smul]
  have hne : K.Nonempty := by
    obtain ⟨γ, -, hγ⟩ := hK (Classical.arbitrary UpperHalfPlane)
    exact ⟨_, hγ⟩
  obtain ⟨κ₀, hκ₀, hmax⟩ := hKc.exists_isMaxOn hne hmc.continuousOn
  have hbound : ∀ z ∈ upperHalf, ‖complexDilatation (liftToC E) z‖ ≤ m κ₀ := by
    intro z hz
    set τ : UpperHalfPlane := UpperHalfPlane.mk z hz with hτdef
    obtain ⟨γ, hγ, hγτ⟩ := hK τ
    have hmτ : m τ = m (γ • τ) := (hinv γ hγ τ).symm
    have : ‖complexDilatation (liftToC E) z‖ = m τ := rfl
    rw [this, hmτ]
    exact hmax hγτ
  have hk0 : 0 ≤ m κ₀ := norm_nonneg _
  have hk1 : m κ₀ < 1 := hμlt _ κ₀.coe_im_pos
  -- the extension by zero
  have hB : IsBeltramiCoeff (upperHalf.indicator (complexDilatation (liftToC E))) univ (m κ₀) := by
    rw [IsBeltramiCoeff, Measure.restrict_univ]
    refine ⟨?_, ?_⟩
    · exact (aestronglyMeasurable_indicator_iff isOpen_upperHalf.measurableSet).2
        (hdilc.aestronglyMeasurable isOpen_upperHalf.measurableSet)
    · refine Filter.Eventually.of_forall fun z => ?_
      by_cases hz : z ∈ upperHalf
      · rw [indicator_of_mem hz]
        exact hbound z hz
      · rw [indicator_of_notMem hz, norm_zero]
        exact hk0
  refine ⟨⟨upperHalf.indicator (complexDilatation (liftToC E)), ⟨_, hk0, hk1, hB⟩, fun (z : ℂ) (hz : z.im ≤ 0) => ?_⟩, ?_, ?_⟩
  · exact Set.indicator_of_notMem (s := upperHalf)
      (fun h => absurd hz (not_le.2 (show (0 : ℝ) < z.im from h))) (complexDilatation (liftToC E))
  · intro γ hγ
    obtain ⟨δ, hδ⟩ := heq γ hγ
    filter_upwards [ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz
    have hz' : 0 < z.im := hz
    have hgz : ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) ∈ upperHalf := by
      rw [← h23l_b_coe_smul γ ⟨z, hz'⟩]
      exact (γ • (⟨z, hz'⟩ : UpperHalfPlane)).coe_im_pos
    simp only [indicator_of_mem hz, indicator_of_mem hgz]
    exact h23l_dilatation_conj hδ hz
  · intro z hz
    exact indicator_of_mem hz _

/-- The dilatation `μ_E` of a `C¹` homeomorphism with `|μ_E| < 1`, which agrees on `ℍ` with a Beltrami coefficient `μ`
(bounded by `k < 1` a.e.), is bounded by `k` everywhere on `ℍ` (it is continuous there). -/
theorem bsu24_x_bound (μ : BeltramiH) {E : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hC1 : ContDiffOn ℝ 1 (liftToC E) upperHalf)
    (hlt : ∀ z ∈ upperHalf, ‖dzbar (liftToC E) z‖ < ‖dz (liftToC E) z‖)
    (hμ : ∀ z ∈ upperHalf, μ.1 z = complexDilatation (liftToC E) z) :
    ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ z ∈ upperHalf, ‖complexDilatation (liftToC E) z‖ ≤ k := by
  obtain ⟨⟨k, hk0, hk1, hμk⟩, -⟩ := μ.2
  refine ⟨k, hk0, hk1, fun z₀ hz₀ => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have hfd : ContinuousOn (fderiv ℝ (liftToC E)) upperHalf :=
    hC1.continuousOn_fderiv_of_isOpen isOpen_upperHalf le_rfl
  have hdzc : ContinuousOn (dz (liftToC E)) upperHalf := by
    unfold dz
    exact (((hfd.clm_apply continuousOn_const).sub
      (continuousOn_const.mul (hfd.clm_apply continuousOn_const))).div_const _)
  have hdzbarc : ContinuousOn (dzbar (liftToC E)) upperHalf := by
    unfold dzbar
    exact (((hfd.clm_apply continuousOn_const).add
      (continuousOn_const.mul (hfd.clm_apply continuousOn_const))).div_const _)
  have hdz0 : ∀ z ∈ upperHalf, dz (liftToC E) z ≠ 0 := fun z hz h => by
    have := hlt z hz
    rw [h, norm_zero] at this
    exact absurd this (not_lt.2 (norm_nonneg _))
  have hdilc : ContinuousOn (complexDilatation (liftToC E)) upperHalf := by
    unfold complexDilatation
    exact hdzbarc.div hdzc hdz0
  have hU : IsOpen {z ∈ upperHalf | k < ‖complexDilatation (liftToC E) z‖} := by
    have h1 : IsOpen (upperHalf ∩ (fun z => ‖complexDilatation (liftToC E) z‖) ⁻¹' Ioi k) :=
      hdilc.norm.isOpen_inter_preimage isOpen_upperHalf isOpen_Ioi
    exact h1
  have hpos : 0 < volume {z ∈ upperHalf | k < ‖complexDilatation (liftToC E) z‖} :=
    hU.measure_pos volume ⟨z₀, hz₀, hcon⟩
  have hnull : volume {z ∈ upperHalf | k < ‖complexDilatation (liftToC E) z‖} = 0 := by
    have h := hμk.2
    rw [Measure.restrict_univ, ae_iff] at h
    refine measure_mono_null (fun z hz => ?_) h
    simp only [Set.mem_ofPred_eq, not_le]
    rw [hμ z hz.1]
    exact hz.2
  exact hpos.ne' hnull

/-- `f_μ ∘ E⁻¹` is holomorphic on `ℍ` when `μ_{f_μ} = μ = μ_E` there (equal dilatations; Weyl). -/
theorem bsu24_conformal (μ : BeltramiH) {E : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hC1 : ContDiffOn ℝ 1 (liftToC E) upperHalf)
    (hlt : ∀ z ∈ upperHalf, ‖dzbar (liftToC E) z‖ < ‖dz (liftToC E) z‖)
    (hμ : ∀ z ∈ upperHalf, μ.1 z = complexDilatation (liftToC E) z) :
    DifferentiableOn ℂ (normalizedSolution μ.1 ∘ liftToC E.symm) upperHalf := by
  obtain ⟨k, hk0, hk1, hbd⟩ := bsu24_x_bound μ hC1 hlt hμ
  have hKQC : IsKQC (liftToC E) upperHalf ((1 + k) / (1 - k)) := s24q_isKQC_of_bound hC1 hlt hk0 hk1 hbd
  obtain ⟨K, hK⟩ := (ut_spec μ).1
  have hg : IsKQC (normalizedSolution μ.1) upperHalf K := ac_t_isKQC_restrict hK isOpen_upperHalf (subset_univ _)
  have hae : ∀ᵐ z ∂(volume.restrict upperHalf),
      complexDilatation (normalizedSolution μ.1) z = complexDilatation (liftToC E) z := by
    filter_upwards [ae_restrict_of_ae (ut_spec μ).2.2.2.2, ae_restrict_mem isOpen_upperHalf.measurableSet]
      with z h1 h2
    rw [h1, hμ z h2]
  obtain ⟨hμ', hfs⟩ := thm10_2_genHomeoSolution_of_isKQC hKQC
  have hgs := nxS_genHomeoSolution_congr (thm10_2_genHomeoSolution_of_isKQC hg).2 hae
  have hK1 : (1 : ℝ) ≤ (1 + k) / (1 - k) := hKQC.2.1
  have hk' : ((1 + k) / (1 - k) - 1) / ((1 + k) / (1 - k) + 1) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  obtain ⟨φ, hφ, hgφ⟩ := same_dilatation_conformal hKQC.1 hk' hμ' hfs hgs
  have hinv : ∀ w ∈ upperHalf, liftToC E.symm w ∈ upperHalf ∧ liftToC E (liftToC E.symm w) = w := by
    intro w hw
    have hw' : 0 < w.im := hw
    have e1 : liftToC E.symm w = ((E.symm ⟨w, hw'⟩ : UpperHalfPlane) : ℂ) := by
      rw [h23l_liftToC_eq _ hw, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    refine ⟨by rw [e1]; exact (E.symm ⟨w, hw'⟩).coe_im_pos, ?_⟩
    rw [e1, h23l_liftToC_coe, E.apply_symm_apply]
  have hsub : upperHalf ⊆ liftToC E '' upperHalf := fun w hw =>
    ⟨liftToC E.symm w, (hinv w hw).1, (hinv w hw).2⟩
  refine (hφ.1.mono hsub).congr fun w hw => ?_
  obtain ⟨h1, h2⟩ := hinv w hw
  show normalizedSolution μ.1 (liftToC E.symm w) = φ w
  rw [hgφ _ h1, h2]

/-- `f_μ` is conformal on `𝕃` (`μ = 0` there). -/
theorem bsu24_conformal_lower (μ : BeltramiH) :
    DifferentiableOn ℂ (normalizedSolution μ.1) lowerHalf := by
  exact (ut_conformal_lowerHalf μ).1

/-- `OnePoint.map` of a point of the plane. -/
theorem bsu24_x_map_coe (f : ℂ → ℂ) (u : ℂ) : OnePoint.map f (u : ExtPlane) = ((f u : ℂ) : ExtPlane) := rfl

/-- The orbit relation of the deformed group in terms of `Γs`: `γ̂` is an element of `Γs` acting on `z ∉ ℝ`, and
`f̂_μ ∘ γ̂ = γ̂μ ∘ f̂_μ`. -/
theorem bsu24_x_orbit {Γs : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {Γμ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)} (μ : BeltramiH) (e : ℂ ≃ₜ ℂ)
    (he : ⇑e = normalizedSolution μ.1)
    (h₁ : ∀ γ ∈ Γs, ∃ γμ ∈ Γμ, ∀ p : ExtPlane,
      OnePoint.map (normalizedSolution μ.1) (mobiusSL (slRealToComplex γ) p) =
        mobiusSL γμ (OnePoint.map (normalizedSolution μ.1) p))
    (h₂ : ∀ γμ ∈ Γμ, ∃ γ ∈ Γs, ∀ p : ExtPlane,
      OnePoint.map (normalizedSolution μ.1) (mobiusSL (slRealToComplex γ) p) =
        mobiusSL γμ (OnePoint.map (normalizedSolution μ.1) p))
    {z w : ℂ} (hz : z.im ≠ 0) :
    (∃ γ ∈ Γs, w = ((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)) ↔
      ∃ γμ ∈ Γμ, (γμ 1 0 * e z + γμ 1 1 ≠ 0) ∧
        e w = (γμ 0 0 * e z + γμ 0 1) / (γμ 1 0 * e z + γμ 1 1) := by
  have hL : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      mobiusSL (slRealToComplex γ) (z : ExtPlane) =
        ((((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1) : ℂ) : ExtPlane) := by
    intro γ
    rw [k24_mobiusSL_real, mobiusExt_coe (k24_d_den_ne_zero (k24_det_realR γ) hz)]
    rfl
  have hR : ∀ γμ : Matrix.SpecialLinearGroup (Fin 2) ℂ, γμ 1 0 * e z + γμ 1 1 ≠ 0 →
      mobiusSL γμ (OnePoint.map (normalizedSolution μ.1) (z : ExtPlane)) =
        ((((γμ 0 0 * e z + γμ 0 1) / (γμ 1 0 * e z + γμ 1 1) : ℂ)) : ExtPlane) := by
    intro γμ hden
    rw [bsu24_x_map_coe, ← he]
    exact mobiusExt_coe hden
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨γμ, hγμ, hrel⟩ := h₁ γ hγ
    have h := hrel (z : ExtPlane)
    rw [hL] at h
    by_cases hden : γμ 1 0 * e z + γμ 1 1 = 0
    · rw [bsu24_x_map_coe, bsu24_x_map_coe, ← he, mobiusSL, mobiusExt_coe_of_eq_zero hden] at h
      exact absurd h (OnePoint.coe_ne_infty _)
    · rw [hR γμ hden, bsu24_x_map_coe] at h
      refine ⟨γμ, hγμ, hden, ?_⟩
      have h' := OnePoint.coe_injective h
      rw [← he] at h'
      exact h'
  · rintro ⟨γμ, hγμ, hden, hw⟩
    obtain ⟨γ, hγ, hrel⟩ := h₂ γμ hγμ
    have h := hrel (z : ExtPlane)
    rw [hL, hR γμ hden, ← hw, bsu24_x_map_coe] at h
    refine ⟨γ, hγ, ?_⟩
    have h' := OnePoint.coe_injective h
    rw [← he] at h'
    exact (e.injective h').symm

/-- A map into `ℍ` which is continuous and holomorphic as a map into `ℂ` is `MDifferentiable`. -/
theorem bsu24_x_mdiff_into_upper {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {g : X → UpperHalfPlane} (hc : Continuous g)
    (hd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x => ((g x : UpperHalfPlane) : ℂ))) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
  intro x
  refine mdifferentiableAt_iff_target.mpr ⟨hc.continuousAt, ?_⟩
  exact hd x

/-- **Klein uniformization from a holomorphic covering and an orbit relation.** -/
theorem bsu24_x_klein {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γμ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)} (e : ℂ ≃ₜ ℂ) {V : Set ℂ} (hV : IsOpen V)
    (Θ : V ≃ₜ UpperHalfPlane) {P : UpperHalfPlane → S} (hPc : IsCoveringMap P)
    (hPd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P) (hPs : Function.Surjective P) (Ψ : ℂ → ℂ)
    (hΨe : ∀ v : V, Ψ (e v) = ((Θ v : UpperHalfPlane) : ℂ)) (hΨ : DifferentiableOn ℂ Ψ (e '' V))
    (hrel : ∀ z : V, ∀ w : V, P (Θ z) = P (Θ w) ↔ ∃ γ ∈ Γμ, (γ 1 0 * e z + γ 1 1 ≠ 0) ∧
      e w = (γ 0 0 * e z + γ 0 1) / (γ 1 0 * e z + γ 1 1)) :
    ∃ (D : TopologicalSpace.Opens ℂ) (p : ℂ → S),
      (D : Set ℂ) = e '' V ∧ IsKleinUniformization Γμ D p := by
  classical
  let D : TopologicalSpace.Opens ℂ := ⟨e '' V, e.isOpenMap V hV⟩
  have hmem : ∀ z : D, e.symm (z : ℂ) ∈ V := by
    rintro ⟨_, v, hv, rfl⟩
    simpa using hv
  let g : D ≃ₜ UpperHalfPlane := ((e.image V).symm).trans Θ
  have hg : ∀ z : D, g z = Θ ⟨e.symm (z : ℂ), hmem z⟩ := by
    intro z
    show Θ ((e.image V).symm z) = _
    congr 1
  let p : ℂ → S := fun w => if h : e.symm w ∈ V then P (Θ ⟨e.symm w, h⟩) else P UpperHalfPlane.I
  have hpg : (fun z : D => p z) = P ∘ g := by
    funext z
    show (if h : e.symm (z : ℂ) ∈ V then P (Θ ⟨e.symm (z : ℂ), h⟩) else P UpperHalfPlane.I) = P (g z)
    rw [dif_pos (hmem z), hg]
  have hgΨ : ∀ z : D, ((g z : UpperHalfPlane) : ℂ) = Ψ (z : ℂ) := by
    intro z
    rw [hg]
    have := hΨe ⟨e.symm (z : ℂ), hmem z⟩
    simp only [Homeomorph.apply_symm_apply] at this
    exact this.symm
  refine ⟨D, p, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hpg]
    exact hPc.comp_homeomorph g
  · rw [hpg]
    refine hPd.comp ?_
    refine bsu24_x_mdiff_into_upper g.continuous ?_
    intro z
    have hfun : (fun x : D => ((g x : UpperHalfPlane) : ℂ)) = Ψ ∘ Subtype.val := by
      funext x
      exact hgΨ x
    rw [hfun]
    exact ((hΨ.differentiableAt (D.isOpen.mem_nhds z.2)).mdifferentiableAt).comp z
      ((contMDiff_subtype_val (n := ω)).mdifferentiable (by simp) z)
  · rw [eq_univ_iff_forall]
    intro s
    obtain ⟨τ, hτ⟩ := hPs s
    refine ⟨e (Θ.symm τ), ⟨Θ.symm τ, (Θ.symm τ).2, rfl⟩, ?_⟩
    have h1 : e.symm (e (Θ.symm τ)) ∈ V := by simpa using (Θ.symm τ).2
    show (if h : e.symm (e (Θ.symm τ)) ∈ V then P (Θ ⟨e.symm (e (Θ.symm τ)), h⟩) else P UpperHalfPlane.I) = s
    rw [dif_pos h1]
    have : (⟨e.symm (e (Θ.symm τ)), h1⟩ : V) = Θ.symm τ := Subtype.ext (by simp)
    rw [this, Homeomorph.apply_symm_apply, hτ]
  · rintro z hz w hw
    obtain ⟨z', hz', rfl⟩ := hz
    obtain ⟨w', hw', rfl⟩ := hw
    have e1 : e.symm (e z') ∈ V := by simpa using hz'
    have e2 : e.symm (e w') ∈ V := by simpa using hw'
    show (if h : e.symm (e z') ∈ V then P (Θ ⟨e.symm (e z'), h⟩) else P UpperHalfPlane.I) =
      (if h : e.symm (e w') ∈ V then P (Θ ⟨e.symm (e w'), h⟩) else P UpperHalfPlane.I) ↔ _
    rw [dif_pos e1, dif_pos e2]
    have h1 : (⟨e.symm (e z'), e1⟩ : V) = ⟨z', hz'⟩ := Subtype.ext (by simp)
    have h2 : (⟨e.symm (e w'), e2⟩ : V) = ⟨w', hw'⟩ := Subtype.ext (by simp)
    rw [h1, h2]
    exact hrel ⟨z', hz'⟩ ⟨w', hw'⟩

/-- `liftToC` of the inverse is a right inverse on `ℍ`. -/
theorem bsu24_x_liftToC_inv (F : UpperHalfPlane ≃ₜ UpperHalfPlane) {w : ℂ} (hw : w ∈ upperHalf) :
    liftToC F.symm w ∈ upperHalf ∧ liftToC F (liftToC F.symm w) = w := by
  have hw' : 0 < w.im := hw
  have e1 : liftToC F.symm w = ((F.symm ⟨w, hw'⟩ : UpperHalfPlane) : ℂ) := by
    rw [h23l_liftToC_eq _ hw, UpperHalfPlane.ofComplex_apply_of_im_pos hw']
  refine ⟨by rw [e1]; exact (F.symm ⟨w, hw'⟩).coe_im_pos, ?_⟩
  rw [e1, h23l_liftToC_coe, F.apply_symm_apply]

/-- The identification `{z | 0 < Im z} ≃ₜ ℍ`. -/
theorem bsu24_x_upperHomeo :
    ∃ ι : (upperHalf : Set ℂ) ≃ₜ UpperHalfPlane, ∀ z, ((ι z : UpperHalfPlane) : ℂ) = (z : ℂ) := by
  refine ⟨{ toFun := fun z => ⟨z.1, z.2⟩
            invFun := fun τ => ⟨τ, τ.coe_im_pos⟩
            left_inv := fun z => rfl
            right_inv := fun τ => rfl
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun z => rfl⟩
  · exact UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr continuous_subtype_val
  · exact Continuous.subtype_mk UpperHalfPlane.continuous_coe _

/-- **`S₁ = D'/Γμ`** with `D' = f_μ(ℍ)`: `p₁' = p₁ ∘ E ∘ f_μ⁻¹` is a holomorphic covering whose fibres are the
`Γμ`-orbits (the deck correspondence of `E` and the `fuchsian_deformation` relation). -/
theorem bsu24_klein_upper
    {Γs Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₁ : UpperHalfPlane → S₁}
    (hp₁ : IsUniformization Γ₁ p₁) (μ : BeltramiH) {E : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hC1 : ContDiffOn ℝ 1 (liftToC E) upperHalf)
    (hlt : ∀ z ∈ upperHalf, ‖dzbar (liftToC E) z‖ < ‖dz (liftToC E) z‖)
    (hμ : ∀ z ∈ upperHalf, μ.1 z = complexDilatation (liftToC E) z)
    (hd₁ : ∀ γ ∈ Γs, ∃ δ ∈ Γ₁, ∀ τ, E (γ • τ) = δ • E τ)
    (hd₂ : ∀ δ ∈ Γ₁, ∃ γ ∈ Γs, ∀ τ, E (γ • τ) = δ • E τ)
    {Γμ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    (h₁ : ∀ γ ∈ Γs, ∃ γμ ∈ Γμ, ∀ p : ExtPlane,
      OnePoint.map (normalizedSolution μ.1) (mobiusSL (slRealToComplex γ) p) =
        mobiusSL γμ (OnePoint.map (normalizedSolution μ.1) p))
    (h₂ : ∀ γμ ∈ Γμ, ∃ γ ∈ Γs, ∀ p : ExtPlane,
      OnePoint.map (normalizedSolution μ.1) (mobiusSL (slRealToComplex γ) p) =
        mobiusSL γμ (OnePoint.map (normalizedSolution μ.1) p)) :
    ∃ (D' : TopologicalSpace.Opens ℂ) (p : ℂ → S₁),
      (D' : Set ℂ) = normalizedSolution μ.1 '' upperHalf ∧ IsKleinUniformization Γμ D' p := by
  classical
  obtain ⟨K, hKqc⟩ := (ut_spec μ).1
  obtain ⟨e, he⟩ := t1_homeomorph hKqc (ut_spec μ).2.1
  obtain ⟨ι, hι⟩ := bsu24_x_upperHomeo
  have hdiff := bsu24_conformal μ hC1 hlt hμ
  -- `h = f_μ ∘ E⁻¹` is conformal from `ℍ` onto `f_μ(ℍ)`
  have hinvE : ∀ w ∈ upperHalf,
      liftToC E.symm w ∈ upperHalf ∧ liftToC E (liftToC E.symm w) = w := by
    intro w hw
    exact bsu24_x_liftToC_inv E hw
  have hinvE' : ∀ w ∈ upperHalf,
      liftToC E w ∈ upperHalf ∧ liftToC E.symm (liftToC E w) = w := by
    intro w hw
    simpa only [Homeomorph.symm_symm] using bsu24_x_liftToC_inv E.symm hw
  have hinj : InjOn (normalizedSolution μ.1 ∘ liftToC E.symm) upperHalf := by
    intro a ha b hb hab
    have h1 : liftToC E.symm a = liftToC E.symm b := by
      have := e.injective (show e (liftToC E.symm a) = e (liftToC E.symm b) by rw [he]; exact hab)
      exact this
    have h2 := congrArg (liftToC E) h1
    rwa [(hinvE a ha).2, (hinvE b hb).2] at h2
  have himg : (normalizedSolution μ.1 ∘ liftToC E.symm) '' upperHalf = e '' upperHalf := by
    ext w
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨liftToC E.symm a, (hinvE a ha).1, by rw [he]; rfl⟩
    · rintro ⟨v, hv, rfl⟩
      refine ⟨liftToC E v, (hinvE' v hv).1, ?_⟩
      show normalizedSolution μ.1 (liftToC E.symm (liftToC E v)) = e v
      rw [(hinvE' v hv).2, he]
  have hconf : IsConformalOnto (normalizedSolution μ.1 ∘ liftToC E.symm) upperHalf (e '' upperHalf) :=
    ⟨hdiff, hinj, himg⟩
  have hsymm := hconf.symm isOpen_upperHalf
  have hΨ : DifferentiableOn ℂ (fun w => liftToC E (e.symm w)) (e '' upperHalf) := by
    refine hsymm.1.congr fun w hw => ?_
    obtain ⟨v, hv, rfl⟩ := hw
    have hx : liftToC E v ∈ upperHalf := (hinvE' v hv).1
    have hhx : (normalizedSolution μ.1 ∘ liftToC E.symm) (liftToC E v) = e v := by
      show normalizedSolution μ.1 (liftToC E.symm (liftToC E v)) = e v
      rw [(hinvE' v hv).2, he]
    have hleft := hinj.leftInvOn_invFunOn hx
    rw [hhx] at hleft
    simpa only [Homeomorph.symm_apply_apply] using hleft.symm
  rw [← he]
  refine bsu24_x_klein (Γμ := Γμ) e isOpen_upperHalf (ι.trans E) hp₁.1 hp₁.2.1 hp₁.2.2.1
    (fun w => liftToC E (e.symm w)) ?_ hΨ ?_
  · intro z
    simp only [Homeomorph.symm_apply_apply]
    change liftToC E (z : ℂ) = ((E (ι z) : UpperHalfPlane) : ℂ)
    rw [← hι z, h23l_liftToC_coe]
  · intro z w
    change p₁ (E (ι z)) = p₁ (E (ι w)) ↔ _
    have hor : p₁ (E (ι z)) = p₁ (E (ι w)) ↔
        ∃ γ ∈ Γs, (w : ℂ) =
          ((γ 0 0 : ℂ) * (z : ℂ) + γ 0 1) / ((γ 1 0 : ℂ) * (z : ℂ) + γ 1 1) := by
      constructor
      · intro hp
        obtain ⟨δ, hδ, hδe⟩ := (hp₁.2.2.2 _ _).1 hp
        obtain ⟨γ, hγ, hEγ⟩ := hd₂ δ hδ
        have hγτ : γ • ι z = ι w := E.injective ((hEγ (ι z)).trans hδe)
        refine ⟨γ, hγ, ?_⟩
        have hval := congrArg (fun τ : UpperHalfPlane => (τ : ℂ)) hγτ
        rw [h23l_b_coe_smul, hι, hι] at hval
        exact hval.symm
      · rintro ⟨γ, hγ, hw⟩
        obtain ⟨δ, hδ, hEγ⟩ := hd₁ γ hγ
        have hγτ : γ • ι z = ι w := by
          apply UpperHalfPlane.ext
          rw [h23l_b_coe_smul, hι, hι]
          exact hw.symm
        refine (hp₁.2.2.2 _ _).2 ⟨δ, hδ, ?_⟩
        rw [← hEγ, hγτ]
    exact hor.trans (bsu24_x_orbit μ e he h₁ h₂ (ne_of_gt z.2))

/-- The holomorphic identification of the lower half-plane with `ℍ` is `z ↦ -z`. -/
theorem bsu24_x_lowerHomeo :
    ∃ ρ : (lowerHalf : Set ℂ) ≃ₜ UpperHalfPlane,
      ∀ z, ((ρ z : UpperHalfPlane) : ℂ) = -(z : ℂ) := by
  refine ⟨{ toFun := fun z => ⟨-z.1, by
              change 0 < -(z : ℂ).im
              exact neg_pos.mpr (z.2 : (z : ℂ).im < 0)⟩
            invFun := fun τ => ⟨-(τ : ℂ), by
              change -(τ : ℂ).im < 0
              exact neg_neg_of_pos τ.coe_im_pos⟩
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun z => rfl⟩
  · intro z
    apply Subtype.ext
    exact neg_neg _
  · intro τ
    apply UpperHalfPlane.ext
    exact neg_neg _
  · exact UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr continuous_subtype_val.neg
  · exact Continuous.subtype_mk UpperHalfPlane.continuous_coe.neg _

/-- The real mirror-group action on the lower half-plane becomes the original action
under `ρ z = -z`. The identity follows by conjugating the upper-half-plane relation. -/
theorem bsu24_x_lower_conj {σ : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hσ : ∀ τ, ((σ τ : UpperHalfPlane) : ℂ) = -conj (τ : ℂ))
    {ρ : (lowerHalf : Set ℂ) ≃ₜ UpperHalfPlane}
    (hρ : ∀ z, ((ρ z : UpperHalfPlane) : ℂ) = -(z : ℂ))
    {γ γ₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : ∀ τ, σ (γ • τ) = γ₀ • σ τ) (z w : (lowerHalf : Set ℂ)) :
    ((w : ℂ) = ((γ 0 0 : ℂ) * (z : ℂ) + γ 0 1) /
      ((γ 1 0 : ℂ) * (z : ℂ) + γ 1 1)) ↔ ρ w = γ₀ • ρ z := by
  let τ : UpperHalfPlane := ⟨conj (z : ℂ), by
    change 0 < -(z : ℂ).im
    exact neg_pos.mpr (z.2 : (z : ℂ).im < 0)⟩
  have hτ : (τ : ℂ) = conj (z : ℂ) := rfl
  have hστ : σ τ = ρ z := by
    apply UpperHalfPlane.ext
    rw [hσ, hρ, hτ]
    simp only [Complex.conj_conj]
  have hval : -(((γ 0 0 : ℂ) * (z : ℂ) + γ 0 1) /
      ((γ 1 0 : ℂ) * (z : ℂ) + γ 1 1)) = ((γ₀ • ρ z : UpperHalfPlane) : ℂ) := by
    have h := congrArg (fun t : UpperHalfPlane => (t : ℂ)) (hγ τ)
    rw [hσ, hστ, h23l_b_coe_smul, hτ] at h
    simpa only [map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_conj] using h
  constructor
  · intro hw
    apply UpperHalfPlane.ext
    rw [hρ, hw]
    exact hval
  · intro hw
    have h := congrArg (fun t : UpperHalfPlane => (t : ℂ)) hw
    rw [hρ, ← hval] at h
    exact neg_injective h

/-- **`S₀ = D/Γμ`** with `D = f_μ(𝕃)`: `p₀' w = p₀ (ρ (f_μ⁻¹ w))` with the holomorphic `ρ : 𝕃 → ℍ`, `ρ z = -z`
(`= σ ∘ conj`), which conjugates `Γs` on `𝕃` to `Γ₀` (`hs`): a holomorphic covering whose fibres are the
`Γμ`-orbits. -/
theorem bsu24_klein_lower
    {Γ₀ Γs : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p₀ : UpperHalfPlane → S₀}
    (hp₀ : IsUniformization Γ₀ p₀) (μ : BeltramiH) {σ : UpperHalfPlane ≃ₜ UpperHalfPlane}
    (hσ : ∀ τ, ((σ τ : UpperHalfPlane) : ℂ) = -conj (τ : ℂ))
    (hs₁ : ∀ γ ∈ Γs, ∃ γ₀ ∈ Γ₀, ∀ τ, σ (γ • τ) = γ₀ • σ τ)
    (hs₂ : ∀ γ₀ ∈ Γ₀, ∃ γ ∈ Γs, ∀ τ, σ (γ • τ) = γ₀ • σ τ)
    {Γμ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)}
    (h₁ : ∀ γ ∈ Γs, ∃ γμ ∈ Γμ, ∀ p : ExtPlane,
      OnePoint.map (normalizedSolution μ.1) (mobiusSL (slRealToComplex γ) p) =
        mobiusSL γμ (OnePoint.map (normalizedSolution μ.1) p))
    (h₂ : ∀ γμ ∈ Γμ, ∃ γ ∈ Γs, ∀ p : ExtPlane,
      OnePoint.map (normalizedSolution μ.1) (mobiusSL (slRealToComplex γ) p) =
        mobiusSL γμ (OnePoint.map (normalizedSolution μ.1) p)) :
    ∃ (D : TopologicalSpace.Opens ℂ) (p : ℂ → S₀),
      (D : Set ℂ) = normalizedSolution μ.1 '' lowerHalf ∧ IsKleinUniformization Γμ D p := by
  classical
  obtain ⟨K, hKqc⟩ := (ut_spec μ).1
  obtain ⟨e, he⟩ := t1_homeomorph hKqc (ut_spec μ).2.1
  obtain ⟨ρ, hρ⟩ := bsu24_x_lowerHomeo
  have hconf := ut_conformal_lowerHalf μ
  have himg : normalizedSolution μ.1 '' lowerHalf = e '' lowerHalf := by
    rw [← he]
  have hinve : DifferentiableOn ℂ (fun w => e.symm w) (e '' lowerHalf) := by
    have hsymm := hconf.symm isOpen_lowerHalf
    rw [himg] at hsymm
    rw [← he] at hsymm
    refine hsymm.1.congr fun w hw => ?_
    obtain ⟨z, hz, rfl⟩ := hw
    have hleft := hconf.2.1.leftInvOn_invFunOn hz
    rw [← he] at hleft
    simpa only [Homeomorph.symm_apply_apply] using hleft.symm
  rw [← he]
  refine bsu24_x_klein (Γμ := Γμ) e isOpen_lowerHalf ρ hp₀.1 hp₀.2.1 hp₀.2.2.1
    (fun w => -e.symm w) ?_ hinve.neg ?_
  · intro z
    simpa only [Homeomorph.symm_apply_apply] using (hρ z).symm
  · intro z w
    have hor : p₀ (ρ z) = p₀ (ρ w) ↔
        ∃ γ ∈ Γs, (w : ℂ) =
          ((γ 0 0 : ℂ) * (z : ℂ) + γ 0 1) / ((γ 1 0 : ℂ) * (z : ℂ) + γ 1 1) := by
      constructor
      · intro hp
        obtain ⟨γ₀, hγ₀, hγ₀e⟩ := (hp₀.2.2.2 _ _).1 hp
        obtain ⟨γ, hγ, hσγ⟩ := hs₂ γ₀ hγ₀
        exact ⟨γ, hγ, (bsu24_x_lower_conj hσ hρ hσγ z w).2 hγ₀e.symm⟩
      · rintro ⟨γ, hγ, hw⟩
        obtain ⟨γ₀, hγ₀, hσγ⟩ := hs₁ γ hγ
        have hρw := (bsu24_x_lower_conj hσ hρ hσγ z w).1 hw
        exact (hp₀.2.2.2 _ _).2 ⟨γ₀, hγ₀, hρw.symm⟩
    exact hor.trans (bsu24_x_orbit μ e he h₁ h₂ (ne_of_lt z.2))

/-- A homeomorphism of `ℂ̄` maps a component of `ℂ̄ ∖ ℝ̂` onto a component of `ℂ̄ ∖ F(ℝ̂)`. -/
theorem bsu24_x_comp (F : ExtPlane ≃ₜ ExtPlane) {H H' : Set ExtPlane} (hHo : IsOpen H)
    (hH'o : IsOpen H') (hdisj : Disjoint H H') (hH : IsPreconnected H)
    (hHR : ∀ x ∈ H, x ∉ extRealLine) (hcov : ∀ x, x ∉ extRealLine → x ∈ H ∨ x ∈ H')
    {q : ExtPlane} (hq : q ∈ H) :
    connectedComponentIn (F '' extRealLine)ᶜ (F q) = F '' H := by
  apply Subset.antisymm
  · intro y hy
    have hFq : F q ∈ (F '' extRealLine)ᶜ := by
      rintro ⟨w, hw, hwq⟩
      exact hHR q hq (F.injective hwq ▸ hw)
    have hpc := (isPreconnected_connectedComponentIn (x := F q) (F := (F '' extRealLine)ᶜ)).image
      F.symm F.symm.continuous.continuousOn
    have hsub : F.symm '' connectedComponentIn (F '' extRealLine)ᶜ (F q) ⊆ H ∪ H' := by
      rintro _ ⟨z, hz, rfl⟩
      have hz' := connectedComponentIn_subset _ _ hz
      have : F.symm z ∉ extRealLine := fun h => hz' ⟨_, h, F.apply_symm_apply z⟩
      exact hcov _ this
    have hne : (F.symm '' connectedComponentIn (F '' extRealLine)ᶜ (F q) ∩ H).Nonempty :=
      ⟨q, ⟨F q, mem_connectedComponentIn hFq, F.symm_apply_apply q⟩, hq⟩
    have := hpc.subset_left_of_subset_union hHo hH'o hdisj hsub hne
    exact ⟨F.symm y, this ⟨y, hy, rfl⟩, F.apply_symm_apply y⟩
  · rintro y ⟨x, hx, rfl⟩
    exact k24_comp_mem F hH hHR hq hx

/-- `f̂_μ(ℝ̂)` is a Jordan curve whose complementary components are `f_μ(𝕃)` and `f_μ(ℍ)`
(`f̂_μ` is a homeomorphism of `ℂ̄` mapping the two half-planes, the components of `ℝ̂ᶜ`, onto them). -/
theorem bsu24_components (μ : BeltramiH) :
    AreComplementaryComponents (OnePoint.map (normalizedSolution μ.1) '' extRealLine)
      (toExt (normalizedSolution μ.1 '' lowerHalf)) (toExt (normalizedSolution μ.1 '' upperHalf)) := by
  obtain ⟨K, hKqc⟩ := (ut_spec μ).1
  obtain ⟨e, he⟩ := t1_homeomorph hKqc (ut_spec μ).2.1
  have hFf : ⇑e.onePointCongr = OnePoint.map (normalizedSolution μ.1) := by
    funext p
    rw [Homeomorph.onePointCongr_apply, he]
  rw [← hFf]
  set F := e.onePointCongr with hF
  have himg : ∀ s : Set ℂ, toExt (normalizedSolution μ.1 '' s) = F '' toExt s := by
    intro s
    rw [toExt, toExt, image_image, image_image]
    refine image_congr fun z _ => ?_
    rw [hF, Homeomorph.onePointCongr_apply, he]
    rfl
  have hUo : IsOpen (toExt upperHalf) := OnePoint.isOpen_image_coe.2 isOpen_upperHalf
  have hLo : IsOpen (toExt lowerHalf) := OnePoint.isOpen_image_coe.2 isOpen_lowerHalf
  have hdisj : Disjoint (toExt upperHalf) (toExt lowerHalf) := by
    rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
    have : w = z := OnePoint.coe_injective hwz
    rw [this] at hw
    exact absurd (show z.im < 0 from hw) (not_lt.2 (le_of_lt (show 0 < z.im from hz)))
  have hI : ((Complex.I : ℂ) : ExtPlane) ∈ toExt upperHalf := ⟨Complex.I, by simp [upperHalf], rfl⟩
  have hnI : ((-Complex.I : ℂ) : ExtPlane) ∈ toExt lowerHalf := ⟨-Complex.I, by simp [lowerHalf], rfl⟩
  refine ⟨uq_isJordanCurve_image F tp_c1_isJordanCurve_extRealLine, F ((-Complex.I : ℂ) : ExtPlane), ?_,
    F ((Complex.I : ℂ) : ExtPlane), ?_, ?_, ?_, ?_⟩
  · rintro ⟨w, hw, hwq⟩
    exact k24_lower_not_mem hnI (F.injective hwq ▸ hw)
  · rintro ⟨w, hw, hwq⟩
    exact k24_upper_not_mem hI (F.injective hwq ▸ hw)
  · rw [bsu24_x_comp F hLo hUo hdisj.symm
      (k24_toExt_isPreconnected bA_isConnected_lowerHalf.isPreconnected) (fun x hx => k24_lower_not_mem hx)
      (fun x hx => (k24_mem_halves hx).symm) hnI, himg]
  · rw [bsu24_x_comp F hUo hLo hdisj
      (k24_toExt_isPreconnected isConnected_upperHalf.isPreconnected) (fun x hx => k24_upper_not_mem hx)
      (fun x hx => k24_mem_halves hx) hI, himg]
  · rw [himg, himg]
    intro h
    have h1 : F ((-Complex.I : ℂ) : ExtPlane) ∈ F '' toExt lowerHalf := ⟨_, hnI, rfl⟩
    rw [h] at h1
    obtain ⟨x, hx, hxy⟩ := h1
    exact Set.disjoint_left.1 hdisj hx (F.injective hxy ▸ hnI)

end bsu24_helpers

/-- **Theorem 24.1** (Bers, 同时单值化定理).  Two closed Riemann surfaces `S₀`, `S₁` of the same genus
`g > 1` can be uniformized by the same quasi-Fuchsian group: there are a quasi-Fuchsian group `Γ`
with invariant Jordan curve `C` (through `∞`) and complementary components `D`, `D*` such that
`S₀ = D/Γ` and `S₁ = D*/Γ`.

**Statement change (2026-10-13, user decision).**  The hypothesis `hhom` was added: an
orientation-**reversing** homeomorphism `f : S₀ → S₁` (every local expression of `f`, followed by `z ↦ z̄`,
is sense preserving).  The book's proof starts from a homeomorphism `S₀ → S₁` ("surfaces of the same genus
are homeomorphic").  That step is the topological classification of closed surfaces, which is not
formalized; `HasGenus` gives only `π₁ ≅ surfaceGroup g`.  The marking must reverse orientation because
`D*/Γ` with the holomorphic covering `p₁` is, in the Fuchsian case `D* = 𝕃`, the mirror image of `ℍ/Γ`.
`hhom` holds for any two closed surfaces of the same genus. -/
theorem thm24_1_simultaneous_uniformization [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    [T2Space S₁] [ConnectedSpace S₁] [IsManifold 𝓘(ℂ) ω S₁] {g : ℕ} (hg : 1 < g)
    (h₀ : HasGenus S₀ g) (h₁ : HasGenus S₁ g)
    (hhom : ∃ f : S₀ ≃ₜ S₁, ∀ x : S₀,
      IsSensePreserving (fun z => conj (localMapExpr f x z)) (localMapDomain f x)) :
    ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℂ)) (C : Set ExtPlane)
      (D D' : TopologicalSpace.Opens ℂ) (p₀ : ℂ → S₀) (p₁ : ℂ → S₁),
      IsQuasiFuchsian Γ C ∧ extInf ∈ C ∧ AreComplementaryComponents C (toExt D) (toExt D') ∧
      IsKleinUniformization Γ D p₀ ∧ IsKleinUniformization Γ D' p₁ := by
  classical
  have : CompactSpace S₀ := h₀.1
  have : CompactSpace S₁ := h₁.1
  obtain ⟨f, hf⟩ := hhom
  obtain ⟨Γ₀, p₀, hΓ₀, hfree₀, hp₀⟩ := s22hg_exists_fuchsian_uniformization hg h₀
  obtain ⟨Γ₁, p₁, hΓ₁, hfree₁, hp₁⟩ := s22hg_exists_fuchsian_uniformization hg h₁
  -- the mirror group `Γs`, its cocompactness, the preserving equivariant lift `κ`
  obtain ⟨Γs, σ, hΓs, hfrees, hσ, hs₁, hs₂⟩ := bsu24_mirror_group hΓ₀ hfree₀
  obtain ⟨K, hKc, hK⟩ := bsu24_cocompact hp₀ σ hs₂
  obtain ⟨κ, hκp, hκo⟩ := bsu24_reversing_lift hp₀ hp₁ hf hσ
  obtain ⟨hd₁, hd₂⟩ := bsu24_deck hp₀ hp₁ hs₁ hs₂ hκp
  -- Douady-Earle extension and its Beltrami coefficient
  obtain ⟨E, hE1, hE2, hE3⟩ := bsu24_de hΓs hfrees hΓ₁ hfree₁ hKc hK hκo hd₁ hd₂
  have hdE₁ : ∀ γ ∈ Γs, ∃ δ ∈ Γ₁, ∀ τ, E (γ • τ) = δ • E τ := fun γ hγ => by
    obtain ⟨δ, hδ, h⟩ := hd₁ γ hγ
    exact ⟨δ, hδ, hE3 γ δ hγ h⟩
  have hdE₂ : ∀ δ ∈ Γ₁, ∃ γ ∈ Γs, ∀ τ, E (γ • τ) = δ • E τ := fun δ hδ => by
    obtain ⟨γ, hγ, h⟩ := hd₂ δ hδ
    exact ⟨γ, hγ, hE3 γ δ hγ h⟩
  obtain ⟨μ, hμc, hμE⟩ := bsu24_beltrami hKc hK hE1 hE2 fun γ hγ => by
    obtain ⟨δ, -, h⟩ := hdE₁ γ hγ
    exact ⟨δ, h⟩
  -- the quasi-Fuchsian deformation and the two Klein uniformizations
  obtain ⟨Γμ, hqf, h₁, h₂⟩ := fuchsian_deformation hΓs (bsu24_limitSet hΓs hfrees hKc hK) μ hμc
  obtain ⟨D', p₁', hD', hU'⟩ := bsu24_klein_upper hp₁ μ hE1 hE2 hμE hdE₁ hdE₂ h₁ h₂
  obtain ⟨D, p₀', hD, hU⟩ := bsu24_klein_lower hp₀ μ hσ hs₁ hs₂ h₁ h₂
  refine ⟨Γμ, OnePoint.map (normalizedSolution μ.1) '' extRealLine, D, D', p₀', p₁', hqf, ?_, ?_,
    hU, hU'⟩
  · refine ⟨extInf, Or.inr rfl, ?_⟩
    simp [extInf]
  · rw [hD, hD']
    exact bsu24_components μ

end LiZhongQC
