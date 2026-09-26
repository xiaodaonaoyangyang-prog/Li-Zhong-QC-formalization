import LiZhongQC.Ch10.S33_BersEmbedding

/-!
# §34 Bers 纤维空间 — The Bers fiber space

* §34.1 holomorphic families of closed Riemann surfaces (Kodaira–Spencer); `T_{G₀} = Ψ(T(S₀))`,
  the quasidiscs `D_φ = f_μ(ℍ)`, the groups `G_φ = f_μ G₀ f_μ⁻¹`, the Bers fiber space
  `F(G₀) = {(φ, z) : φ ∈ T_{G₀}, z ∈ D_φ}`, the action of `G₀`, `V(G₀) = F(G₀)/G₀` and the
  projection `pr`                                           — `IsHolomorphicFamily`, `bersDisc`,
                                                             `BersFiberSpace`, `bersFiberAction`,
                                                             `BersQuotient`, `bersProjection`
* §34.2 `G₀` acts discontinuously on `F(G₀)`; `V(G₀)` is a complex manifold of dimension `3g - 2`
  with local coordinates `(t₁, …, t_{3g-3}, z)`; Theorem 34.1 (Bers): `(V(G₀), T_{G₀}, pr)` is a
  holomorphic family of closed Riemann surfaces of genus `g`
                                                           — `bersFiber_action_discontinuous`,
                                                             `thm34_1_bers`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

/-- **§34.1 (全纯族, Kodaira–Spencer).**  `pr : V → M`, `V` an `(n+1)`-dimensional and `M` an
`n`-dimensional complex manifold, is a holomorphic family of closed Riemann surfaces if
(i) `pr` is holomorphic and surjective with surjective differential everywhere,
(ii) `pr` is proper (the preimage of a compact set is compact), and
(iii) every fibre `pr⁻¹(τ)` is a closed Riemann surface. -/
def IsHolomorphicFamily {n : ℕ} {V : Type u} [TopologicalSpace V] [ChartedSpace (Fin (n + 1) → ℂ) V]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (Fin n → ℂ) M] (pr : V → M) : Prop :=
  MDifferentiable 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin n → ℂ) pr ∧ Function.Surjective pr ∧
    (∀ v, Function.Surjective (mfderiv 𝓘(ℂ, Fin (n + 1) → ℂ) 𝓘(ℂ, Fin n → ℂ) pr v)) ∧ IsProperMap pr ∧
    ∀ t : M, ∃ (X : ClosedRS.{u}) (j : X.carrier → V), MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) j ∧
      Topology.IsEmbedding j ∧ range j = pr ⁻¹' {t}

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- §34.1: `T_{G₀} = Ψ(T(S₀)) ⊆ Q(G₀, 𝕃)`, the image of the Bers embedding. -/
def bersImage (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set (ℂ → ℂ) := range (bersMapGamma Γ)

/-- §34.1: the quasidisc `D_φ = f_μ(ℍ)` attached to `φ = φ_μ ∈ T_{G₀}` (the union over all
representatives `μ`, which all give the same domain). -/
def bersDisc (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (φ : ℂ → ℂ) : Set ℂ :=
  {z | ∃ μ : BeltramiGamma Γ, bersFunctionGamma μ = φ ∧ z ∈ normalizedSolution μ.1.1 '' upperHalf}

/-- §34.1: `D_φ` does not depend on the representative `μ` of `φ`: `f_μ(ℍ)` is determined by `f_μ|ℝ`. -/
theorem bersDisc_wellDefined {μ ν : BeltramiGamma Γ} (h : bersFunctionGamma μ = bersFunctionGamma ν) :
    normalizedSolution μ.1.1 '' upperHalf = normalizedSolution ν.1.1 '' upperHalf ∧
      bersDisc Γ (bersFunctionGamma μ) = normalizedSolution μ.1.1 '' upperHalf := by
  have hS : ∀ z ∈ lowerHalf, schwarzian (normalizedSolution μ.1.1) z =
      schwarzian (normalizedSolution ν.1.1) z := by
    intro z hz
    have h1 := congrFun h z
    simp only [bersFunctionGamma, bersFunction, indicator_of_mem hz] at h1
    exact h1
  refine ⟨(ut_welding (bA_equiv_of_schwarzian_eq hS)).2, ?_⟩
  ext w
  constructor
  · rintro ⟨ν', hν', hw'⟩
    have hS' : ∀ z ∈ lowerHalf, schwarzian (normalizedSolution μ.1.1) z =
        schwarzian (normalizedSolution ν'.1.1) z := by
      intro z hz
      have h1 := congrFun hν' z
      simp only [bersFunctionGamma, bersFunction, indicator_of_mem hz] at h1
      exact h1.symm
    rw [(ut_welding (bA_equiv_of_schwarzian_eq hS')).2]
    exact hw'
  · intro hw'
    exact ⟨μ, rfl, hw'⟩

open scoped Classical in
/-- §34.1: the element `γ_φ = f_μ ∘ γ ∘ f_μ⁻¹ ∈ G_φ` of the group `G_φ = f_μ G₀ f_μ⁻¹` acting on `D_φ`
(computed with a representative `μ` of `φ`; the identity if `φ ∉ T_{G₀}`). -/
def bersFiberAction (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  if h : ∃ μ : BeltramiGamma Γ, bersFunctionGamma μ = φ then
    normalizedSolution h.choose.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
      (Function.invFunOn (normalizedSolution h.choose.1.1) univ z))
  else z

/-! ### S34 basics track interface (coordinator 553e2d): MOB with explicit coefficients -/

/-- The pole-case normalizer of `γ = (a b; c d)` (`c ≠ 0`) for a map `f`: `G z = (f(p + q (z + r)⁻¹) - f(p))⁻¹` with
`p = a/c`, `q = -1/c²`, `r = d/c`.  Off the pole `-d/c` this is `(f(γ z) - f(γ ∞))⁻¹` (`bg2_m1_mobius_eq`), and at the
pole it is `0` (Lean's `0⁻¹ = 0`); for `f = f_μ` it is the plane homeomorphism of `bg2_mob_pole`. -/
def s34_G (f : ℂ → ℂ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℂ) : ℂ :=
  (f ((γ 0 0 : ℂ) / γ 1 0 + -((γ 1 0 : ℂ) ^ 2)⁻¹ * (z + (γ 1 1 : ℂ) / γ 1 0)⁻¹) - f ((γ 0 0 : ℂ) / γ 1 0))⁻¹

/-- **K0** (MOB, affine case, explicit): for `γ ∈ G₀` with `c = 0`, `f_μ ∘ γ = Δ f_μ + f_μ(γ 0)` with
`Δ = f_μ(γ 1) - f_μ(γ 0)` (`f_μ ∘ γ` is a normalized-up-to-affine q.c. map with dilatation `μ`: `bg2_dil_comp`,
`bg2_normalize`). -/
theorem s34_affine_norm (μ : BeltramiGamma Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (hc : γ 1 0 = 0) (z : ℂ) :
    normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
      (normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) 1) -
          normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) 0)) * normalizedSolution μ.1.1 z +
        normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) 0) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  rw [hc, mul_zero, sub_zero] at hdet
  have h00 : (γ 0 0 : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]
    rintro h
    rw [h, zero_mul] at hdet
    exact zero_ne_one hdet
  have h11 : (γ 1 1 : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]
    rintro h
    rw [h, mul_zero] at hdet
    exact zero_ne_one hdet
  -- `γ z = (γ₀₀ z + γ₀₁)/γ₁₁` is affine with nonzero slope, hence conformal onto `ℂ`
  have hT : mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) =
      fun u => (u - (-(γ 0 1 : ℂ) / γ 0 0)) / ((γ 1 1 : ℂ) / γ 0 0) := by
    funext u
    simp only [mobiusFn, hc, ofReal_zero, zero_mul, zero_add]
    field_simp
    ring
  have hTc : IsConformalOnto (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) univ univ := by
    rw [hT]
    exact nxE_affine_isConformalOnto (div_ne_zero h11 h00)
  -- `G = f_μ ∘ γ` is a q.c. map of the plane onto itself with dilatation `μ` a.e.
  obtain ⟨K, hK⟩ := (ut_spec μ.1).1
  have hG := thm7_1_comp (isKQC_one_of_conformal isOpen_univ hTc) hK (subset_univ _)
  have hs : (normalizedSolution μ.1.1 ∘ mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) '' univ = univ := by
    rw [image_comp, hTc.2.2, (ut_spec μ.1).2.1]
  have hN := bg2_normalize μ.1 hG hs (bg2_dil_comp μ hγ)
  have hΔ : normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) 1) -
      normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) 0) ≠ 0 := fun h =>
    one_ne_zero (hG.2.2.1.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
  -- `f_μ = (G - G 0)/(G 1 - G 0)`, i.e. `G = (G 1 - G 0) f_μ + G 0`
  simp only [Function.comp_apply] at hN
  rw [hN z, mul_div_cancel₀ _ hΔ, sub_add_cancel]

/-- **K1** (MOB, pole case, explicit): for `γ ∈ G₀` with `c ≠ 0`, `G = s34_G f_μ γ` is a q.c. homeomorphism of the plane
(`bg2_m1_isHomeomorphOnto`, `bg2_m1_isKQC`, `b4_isKQC_univ_of_punctured`) with dilatation `μ` a.e. (as in
`bg2_mob_pole`), so `G = Δ f_μ + G 0` with `Δ = G 1 - G 0` (`bg2_normalize`). -/
theorem s34_pole_norm (μ : BeltramiGamma Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (hc : γ 1 0 ≠ 0) (z : ℂ) :
    s34_G (normalizedSolution μ.1.1) γ z =
      (s34_G (normalizedSolution μ.1.1) γ 1 - s34_G (normalizedSolution μ.1.1) γ 0) * normalizedSolution μ.1.1 z +
        s34_G (normalizedSolution μ.1.1) γ 0 := by
  obtain ⟨K, hK⟩ := (ut_spec μ.1).1
  have hs := (ut_spec μ.1).2.1
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
    exact bg2_m1_mobius_eq hc hz
  have hpole : ∀ z : ℂ, (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 ↔ z ≠ -r := by
    intro z
    rw [hr]
    exact not_congr (bg2_m1_pole_iff hc z)
  have hGG : s34_G (normalizedSolution μ.1.1) γ =
      fun z => (normalizedSolution μ.1.1 (p + q * (z + r)⁻¹) - normalizedSolution μ.1.1 p)⁻¹ := by
    subst hp hq' hr
    rfl
  set f := normalizedSolution μ.1.1
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, G = fun z => (f (p + q * (z + r)⁻¹) - f p)⁻¹ := ⟨_, rfl⟩
  have hGG' : s34_G f γ = G := by rw [hG]; exact hGG
  rw [hGG']
  -- `G` is a `K`-q.c. homeomorphism of the plane (as in `bg2_mob_pole`)
  have hGh : IsHomeomorphOnto G univ univ := hG ▸ bg2_m1_isHomeomorphOnto hK hs p q r hq
  have hGK : IsKQC G univ K := b4_isKQC_univ_of_punctured hGh (hG ▸ bg2_m1_isKQC hK p q r hq)
  have hfc : Continuous f := continuousOn_univ.1 hK.2.2.1.1
  have hfi : Function.Injective f := fun a b hab => hK.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
  -- off the pole, `f (γ z) ≠ f p`
  have hne : ∀ z : ℂ, z ≠ -r → f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) - f p ≠ 0 := by
    intro z hz h
    have h1 := hfi (sub_eq_zero.1 h)
    rw [hM z hz, add_eq_left, mul_eq_zero, inv_eq_zero] at h1
    rcases h1 with h0 | h0
    · exact hq h0
    · exact hz (eq_neg_of_add_eq_zero_left h0)
  -- the dilatation of `G = N ∘ f ∘ γ` is `μ` a.e.
  have hGd : ∀ᵐ z, complexDilatation G z = μ.1.1 z := by
    filter_upwards [bg2_dil_comp μ hγ, compl_mem_ae_iff.mpr (measure_singleton (-r))] with z h1 h2
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
  -- `f = (G - G 0)/(G 1 - G 0)`, i.e. `G = (G 1 - G 0) f + G 0`
  have hnorm : ∀ z, f z = (G z - G 0) / (G 1 - G 0) := bg2_normalize μ.1 hGK hGh.2.2.1 hGd
  have hΔ : G 1 - G 0 ≠ 0 := fun h =>
    one_ne_zero (hGh.2.1 (mem_univ _) (mem_univ _) (sub_eq_zero.1 h))
  rw [hnorm z, mul_div_cancel₀ _ hΔ, sub_add_cancel]

/-- **KF0** (the action, affine case): `f_μ ∘ γ ∘ f_μ⁻¹` is the affine map `w ↦ Δ w + f_μ(γ 0)` (`s34_affine_norm`, `f_μ`
onto). -/
theorem s34_F_affine (μ : BeltramiGamma Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (hc : γ 1 0 = 0) (w : ℂ) :
    normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
        (Function.invFunOn (normalizedSolution μ.1.1) univ w)) =
      (normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) 1) -
          normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) 0)) * w +
        normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) 0) := by
  have hwi : w ∈ normalizedSolution μ.1.1 '' univ := by
    rw [(ut_spec μ.1).2.1]
    exact mem_univ w
  rw [s34_affine_norm μ hγ hc (Function.invFunOn (normalizedSolution μ.1.1) univ w),
    Function.invFunOn_eq hwi]

/-- **KF1** (the action, pole case): off the pole image `f_μ(-d/c)`, `f_μ ∘ γ ∘ f_μ⁻¹` is the Möbius map
`w ↦ f_μ(a/c) + (Δ w + G 0)⁻¹` with `G = s34_G f_μ γ`, `Δ = G 1 - G 0` (`s34_pole_norm`; `G u = (f_μ(γ u) - f_μ(a/c))⁻¹ ≠ 0`
off the pole, `bg2_m1_mobius_eq`, `f_μ` injective), and `Δ w + G 0 ≠ 0` there. -/
theorem s34_F_pole (μ : BeltramiGamma Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (hc : γ 1 0 ≠ 0) {w : ℂ} (hw : w ≠ normalizedSolution μ.1.1 (-((γ 1 1 : ℂ) / γ 1 0))) :
    (s34_G (normalizedSolution μ.1.1) γ 1 - s34_G (normalizedSolution μ.1.1) γ 0) * w +
        s34_G (normalizedSolution μ.1.1) γ 0 ≠ 0 ∧
      normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
          (Function.invFunOn (normalizedSolution μ.1.1) univ w)) =
        normalizedSolution μ.1.1 ((γ 0 0 : ℂ) / γ 1 0) +
          ((s34_G (normalizedSolution μ.1.1) γ 1 - s34_G (normalizedSolution μ.1.1) γ 0) * w +
            s34_G (normalizedSolution μ.1.1) γ 0)⁻¹ := by
  obtain ⟨K, hK⟩ := (ut_spec μ.1).1
  have hfi : Function.Injective (normalizedSolution μ.1.1) := fun a b hab =>
    hK.2.2.1.2.1 (mem_univ a) (mem_univ b) hab
  have hc' : (γ 1 0 : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc
  have hwi : w ∈ normalizedSolution μ.1.1 '' univ := by
    rw [(ut_spec μ.1).2.1]
    exact mem_univ w
  have hu := Function.invFunOn_eq hwi
  set u := Function.invFunOn (normalizedSolution μ.1.1) univ w
  -- `u = f⁻¹ w` is not the pole `-d/c` of `γ`
  have hu' : u ≠ -((γ 1 1 : ℂ) / γ 1 0) := by
    intro h
    apply hw
    rw [← hu, h]
  have hTu := bg2_m1_mobius_eq hc hu'
  -- `f (γ u) ≠ f (a/c)`, so `G u = (f (γ u) - f (a/c))⁻¹ ≠ 0`
  have hne : normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) u) -
      normalizedSolution μ.1.1 ((γ 0 0 : ℂ) / γ 1 0) ≠ 0 := by
    intro h
    have h1 := hfi (sub_eq_zero.1 h)
    rw [hTu, add_eq_left, mul_eq_zero, inv_eq_zero] at h1
    rcases h1 with h0 | h0
    · exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hc')) h0
    · exact hu' (eq_neg_of_add_eq_zero_left h0)
  have hGu : s34_G (normalizedSolution μ.1.1) γ u =
      (normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) u) -
        normalizedSolution μ.1.1 ((γ 0 0 : ℂ) / γ 1 0))⁻¹ := by
    unfold s34_G
    rw [hTu]
  -- `G u = Δ w + G 0` (`s34_pole_norm` at `u`, `f u = w`)
  have hK1 := s34_pole_norm μ hγ hc u
  rw [hu] at hK1
  rw [← hK1, hGu]
  refine ⟨inv_ne_zero hne, ?_⟩
  rw [inv_inv]
  ring

/-- `f_μ` is injective (it is a quasiconformal homeomorphism of the plane). -/
theorem s34_w_inj (μ : BeltramiH) : Function.Injective (normalizedSolution μ.1) := by
  obtain ⟨K, hK⟩ := (ut_spec μ).1
  exact fun a b hab => hK.2.2.1.2.1 (mem_univ a) (mem_univ b) hab

/-- `f_μ⁻¹ (f_μ u) = u` for the inverse `invFunOn f_μ univ` (`f_μ` injective). -/
theorem s34_w_invFun_apply (μ : BeltramiH) (u : ℂ) :
    Function.invFunOn (normalizedSolution μ.1) univ (normalizedSolution μ.1 u) = u :=
  (s34_w_inj μ).injOn.leftInvOn_invFunOn (mem_univ u)

/-- Equal Bers functions `φ_μ = φ_ν` give `f_μ = f_ν` on `ℝ`: the Schwarzians agree on `𝕃`
(`bA_equiv_of_schwarzian_eq`). -/
theorem s34_w_real_eq {μ ν : BeltramiGamma Γ} (h : bersFunctionGamma μ = bersFunctionGamma ν) (x : ℝ) :
    normalizedSolution μ.1.1 x = normalizedSolution ν.1.1 x := by
  have hS : ∀ z ∈ lowerHalf, schwarzian (normalizedSolution μ.1.1) z =
      schwarzian (normalizedSolution ν.1.1) z := by
    intro z hz
    have h1 := congrFun h z
    simp only [bersFunctionGamma, bersFunction, indicator_of_mem hz] at h1
    exact h1
  have h2 : teichSetoid μ.1 ν.1 := bA_equiv_of_schwarzian_eq hS
  exact h2 x

/-- `γ ∈ SL(2, ℝ)` maps real points to real points (`x/0 = 0` at the pole). -/
theorem s34_w_mobius_ofReal (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (t : ℝ) :
    mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (t : ℂ) =
      (((γ 0 0 * t + γ 0 1) / (γ 1 0 * t + γ 1 1) : ℝ) : ℂ) := by
  unfold mobiusFn
  push_cast
  rfl

/-- `s34_G f γ` at a real point only evaluates `f` at real points, so it is the same for maps `f`, `g`
that agree on `ℝ`. -/
theorem s34_w_G_congr {f g : ℂ → ℂ} (h : ∀ x : ℝ, f x = g x) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (t : ℝ) : s34_G f γ t = s34_G g γ t := by
  have e1 : (γ 0 0 : ℂ) / γ 1 0 + -((γ 1 0 : ℂ) ^ 2)⁻¹ * ((t : ℂ) + (γ 1 1 : ℂ) / γ 1 0)⁻¹ =
      ((γ 0 0 / γ 1 0 + -(γ 1 0 ^ 2)⁻¹ * (t + γ 1 1 / γ 1 0)⁻¹ : ℝ) : ℂ) := by
    push_cast
    ring
  have e2 : (γ 0 0 : ℂ) / γ 1 0 = ((γ 0 0 / γ 1 0 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [s34_G, s34_G, e1, e2, h, h]

/-- At the image `f_μ(-d/c)` of the pole of `γ` (`c ≠ 0`), `f_μ ∘ γ ∘ f_μ⁻¹` takes the value `f_μ(0) = 0`:
`f_μ⁻¹(f_μ(-d/c)) = -d/c` and `γ(-d/c) = x/0 = 0`. -/
theorem s34_w_pole_val (μ : BeltramiH) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hc : γ 1 0 ≠ 0) :
    normalizedSolution μ.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
      (Function.invFunOn (normalizedSolution μ.1) univ
        (normalizedSolution μ.1 (-((γ 1 1 : ℂ) / γ 1 0))))) = 0 := by
  rw [s34_w_invFun_apply, mobiusFn, (bg2_m1_pole_iff hc _).2 rfl, div_zero]
  exact (ut_spec μ).2.2.1

/-- **(a)** `f_μ ∘ γ ∘ f_μ⁻¹` depends only on `φ_μ`: for `φ_μ = φ_ν` and `γ ∈ G₀` it is the same map for `μ` and `ν`
(`s34_F_affine`, `s34_F_pole`: all coefficients are values at real points, where `f_μ = f_ν`; at the pole image
both maps take the value `0`). -/
theorem s34_w_F_eq {μ ν : BeltramiGamma Γ} (h : bersFunctionGamma μ = bersFunctionGamma ν)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) (z : ℂ) :
    normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
        (Function.invFunOn (normalizedSolution μ.1.1) univ z)) =
      normalizedSolution ν.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
        (Function.invFunOn (normalizedSolution ν.1.1) univ z)) := by
  have hr := s34_w_real_eq h
  by_cases hc : γ 1 0 = 0
  · have e0 := s34_w_mobius_ofReal γ 0
    have e1 := s34_w_mobius_ofReal γ 1
    rw [ofReal_zero] at e0
    rw [ofReal_one] at e1
    rw [s34_F_affine μ hγ hc, s34_F_affine ν hγ hc, e0, e1, hr, hr]
  · have epole : -((γ 1 1 : ℂ) / γ 1 0) = ((-(γ 1 1 / γ 1 0) : ℝ) : ℂ) := by
      push_cast
      ring
    have ep : (γ 0 0 : ℂ) / γ 1 0 = ((γ 0 0 / γ 1 0 : ℝ) : ℂ) := by
      push_cast
      ring
    have hG0 := s34_w_G_congr hr γ 0
    have hG1 := s34_w_G_congr hr γ 1
    rw [ofReal_zero] at hG0
    rw [ofReal_one] at hG1
    by_cases hz : z = normalizedSolution μ.1.1 (-((γ 1 1 : ℂ) / γ 1 0))
    · rw [hz, s34_w_pole_val μ.1 hc, epole, hr, ← epole, s34_w_pole_val ν.1 hc]
    · have hz' : z ≠ normalizedSolution ν.1.1 (-((γ 1 1 : ℂ) / γ 1 0)) := by
        rwa [epole, ← hr, ← epole]
      rw [(s34_F_pole μ hγ hc hz).2, (s34_F_pole ν hγ hc hz').2, hG0, hG1, ep, hr]

/-- An affine map `w ↦ a w + b` with `a ≠ 0` is a fractional linear transformation on `ℂ`. -/
theorem s34_w_isMobius_affine {F : ℂ → ℂ} {a b : ℂ} (ha : a ≠ 0) (hF : ∀ w, F w = a * w + b) :
    IsMobiusOn F univ := by
  refine ⟨a, b, 0, 1, ?_, fun z _ _ => ?_⟩
  · rw [mul_one, mul_zero, sub_zero]
    exact ha
  · rw [hF, zero_mul, zero_add, div_one]

/-- A map that is `w ↦ A + (Δ w + B)⁻¹` with `Δ w + B ≠ 0` off a zero `w₀` of `Δ w + B` is a fractional linear
transformation on `ℂ`, with coefficients `(A Δ, A B + 1, Δ, B)` of determinant `-Δ ≠ 0`. -/
theorem s34_w_isMobius_pole {F : ℂ → ℂ} {A Δ B w₀ : ℂ} (h0 : Δ * w₀ + B = 0)
    (hF : ∀ w, w ≠ w₀ → Δ * w + B ≠ 0 ∧ F w = A + (Δ * w + B)⁻¹) : IsMobiusOn F univ := by
  have hΔ : Δ ≠ 0 := by
    intro h
    have h1 := (hF (w₀ + 1) (by simp)).1
    rw [h, zero_mul, zero_add] at h1 h0
    exact h1 h0
  refine ⟨A * Δ, A * B + 1, Δ, B, ?_, fun z _ hz => ?_⟩
  · intro h
    apply hΔ
    linear_combination -h
  · have hzw : z ≠ w₀ := by
      rintro rfl
      exact hz h0
    rw [(hF z hzw).2]
    field_simp
    ring

/-- **(b)** `f_μ ∘ γ ∘ f_μ⁻¹` is a fractional linear transformation for `γ ∈ G₀`: affine if `c = 0`
(`s34_F_affine`; the slope is `≠ 0` as `f_μ ∘ γ` is injective), and `w ↦ f_μ(a/c) + (Δ w + G 0)⁻¹` off the pole
image `f_μ(-d/c)` if `c ≠ 0` (`s34_F_pole`), where `Δ f_μ(-d/c) + G 0 = G(-d/c) = 0` (`s34_pole_norm`). -/
theorem s34_w_isMobius (μ : BeltramiGamma Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) :
    IsMobiusOn (fun z => normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
      (Function.invFunOn (normalizedSolution μ.1.1) univ z))) univ := by
  by_cases hc : γ 1 0 = 0
  · have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have h := Matrix.SpecialLinearGroup.det_coe γ
      rwa [Matrix.det_fin_two] at h
    have hdetC : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 ≠ 0 := by
      have h : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by exact_mod_cast hdet
      rw [h]
      exact one_ne_zero
    have h11 : (γ 1 1 : ℂ) ≠ 0 := by
      rw [ofReal_ne_zero]
      intro h
      rw [h, hc, mul_zero, mul_zero, sub_zero] at hdet
      exact zero_ne_one hdet
    have hden : ∀ t : ℂ, (γ 1 0 : ℂ) * t + γ 1 1 ≠ 0 := by
      intro t
      rw [hc, ofReal_zero, zero_mul, zero_add]
      exact h11
    refine s34_w_isMobius_affine ?_ (s34_F_affine μ hγ hc)
    intro h
    have h1 := congrArg (mobiusFn (γ 1 1) (-(γ 0 1 : ℂ)) (-(γ 1 0 : ℂ)) (γ 0 0)) (s34_w_inj μ.1 (sub_eq_zero.1 h))
    rw [mobiusFn_inv_apply hdetC (hden 1), mobiusFn_inv_apply hdetC (hden 0)] at h1
    exact one_ne_zero h1
  · have hGpole : s34_G (normalizedSolution μ.1.1) γ (-((γ 1 1 : ℂ) / γ 1 0)) = 0 := by
      simp only [s34_G, neg_add_cancel, inv_zero, mul_zero, add_zero, sub_self]
    rw [s34_pole_norm μ hγ hc] at hGpole
    exact s34_w_isMobius_pole hGpole fun w hw => s34_F_pole μ hγ hc hw

/-- `γ ∈ SL(2, ℝ)` maps `ℍ` onto `ℍ`: `Im (γ z) = Im z/|cz + d|²` (`mobiusFn_im_real`), and the inverse
`w ↦ (dw - b)/(-cw + a)` also has determinant `1` (`mobiusFn_inv_apply`). -/
theorem s34_w_image_upperHalf (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) '' upperHalf = upperHalf := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  apply Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    have hu' : 0 < u.im := hu
    show 0 < (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) u).im
    rw [mobiusFn_im_real, hdet, one_mul]
    exact div_pos hu' (normSq_pos.2 (bg2_d_den_ne_zero hdet hu'.ne'))
  · intro w hw
    have hw' : 0 < w.im := hw
    have hdet' : γ 1 1 * γ 0 0 - -γ 0 1 * -γ 1 0 = 1 := by linear_combination hdet
    have hden : ((-γ 1 0 : ℝ) : ℂ) * w + (γ 0 0 : ℝ) ≠ 0 := bg2_d_den_ne_zero hdet' hw'.ne'
    have him := mobiusFn_im_real (γ 1 1) (-γ 0 1) (-γ 1 0) (γ 0 0) w
    rw [hdet', one_mul] at him
    have hne : ((γ 1 1 : ℝ) : ℂ) * (γ 0 0 : ℝ) - ((-γ 0 1 : ℝ) : ℂ) * ((-γ 1 0 : ℝ) : ℂ) ≠ 0 := by
      have h : ((γ 1 1 : ℝ) : ℂ) * (γ 0 0 : ℝ) - ((-γ 0 1 : ℝ) : ℂ) * ((-γ 1 0 : ℝ) : ℂ) = 1 := by
        exact_mod_cast hdet'
      rw [h]
      exact one_ne_zero
    have hinv := mobiusFn_inv_apply hne hden
    refine ⟨mobiusFn (γ 1 1) (-γ 0 1 : ℝ) (-γ 1 0 : ℝ) (γ 0 0) w, ?_, ?_⟩
    · show 0 < (mobiusFn (γ 1 1) (-γ 0 1 : ℝ) (-γ 1 0 : ℝ) (γ 0 0) w).im
      rw [him]
      exact div_pos hw' (normSq_pos.2 hden)
    · simpa only [ofReal_neg, neg_neg] using hinv

/-- §34.1: `γ_φ` is well defined (independent of the representative), is a fractional linear
transformation mapping `D_φ` onto itself, and `G_φ = {γ_φ}` is a quasi-Fuchsian group (a Fuchsian
group when `D_φ` is a disc), the covering group of `D_φ/G_φ`. -/
theorem bersFiberAction_wellDefined (hΓ : IsFuchsian Γ) (μ : BeltramiGamma Γ) {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hγ : γ ∈ Γ) :
    (∀ z, bersFiberAction Γ γ (bersFunctionGamma μ) z =
      normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
        (Function.invFunOn (normalizedSolution μ.1.1) univ z))) ∧
    IsMobiusOn (bersFiberAction Γ γ (bersFunctionGamma μ)) univ ∧
    bersFiberAction Γ γ (bersFunctionGamma μ) '' bersDisc Γ (bersFunctionGamma μ) = bersDisc Γ (bersFunctionGamma μ) := by
  have _hΓ := hΓ
  have hex : ∃ ν : BeltramiGamma Γ, bersFunctionGamma ν = bersFunctionGamma μ := ⟨μ, rfl⟩
  have hA : ∀ z, bersFiberAction Γ γ (bersFunctionGamma μ) z =
      normalizedSolution μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
        (Function.invFunOn (normalizedSolution μ.1.1) univ z)) := by
    intro z
    rw [bersFiberAction, dite_eq_left hex]
    exact s34_w_F_eq hex.choose_spec hγ z
  refine ⟨hA, ?_, ?_⟩
  · rw [funext hA]
    exact s34_w_isMobius μ hγ
  · rw [(bersDisc_wellDefined (μ := μ) (ν := μ) rfl).2]
    ext w
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      rw [hA, s34_w_invFun_apply]
      exact ⟨_, (s34_w_image_upperHalf γ).subset ⟨u, hu, rfl⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      rw [← s34_w_image_upperHalf γ] at hu
      obtain ⟨v, hv, rfl⟩ := hu
      refine ⟨normalizedSolution μ.1.1 v, ⟨v, hv, rfl⟩, ?_⟩
      rw [hA, s34_w_invFun_apply]

/-- **§34.1 (Bers 纤维空间).**  `F(G₀) = {(φ, z) : φ ∈ T_{G₀}, z ∈ D_φ}`. -/
def BersFiberSpace (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Set ((ℂ → ℂ) × ℂ) :=
  {p | p.1 ∈ bersImage Γ ∧ p.2 ∈ bersDisc Γ p.1}

/-- §34.1: the action of `G₀` on `F(G₀)`: `γ(φ, z) = (φ, γ_φ(z))`. -/
def bersFiberSpaceAction (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (p : (ℂ → ℂ) × ℂ) : (ℂ → ℂ) × ℂ :=
  (p.1, bersFiberAction Γ γ p.1 p.2)

/-- §34.1: the equivalence relation on `F(G₀)` generated by the action of `G₀`. -/
def bersFiberRel (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p q : BersFiberSpace Γ) : Prop :=
  ∃ γ ∈ Γ, bersFiberSpaceAction Γ γ p.1 = q.1

/-- **§34.1**: the quotient `V(G₀) = F(G₀)/G₀`; its points `[φ, z]` are the `G₀`-orbits. -/
def BersQuotient (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : Type := Quot (bersFiberRel Γ)

/-- §34.1: the projection `pr : V(G₀) → T_{G₀}`, `[φ, z] ↦ φ`, induced by `(φ, z) ↦ φ`. -/
def bersProjection (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) : BersQuotient Γ → ℂ → ℂ :=
  Quot.lift (fun p : BersFiberSpace Γ => p.1.1) fun _ _ h => by
    obtain ⟨γ, -, hγ⟩ := h
    exact (congrArg Prod.fst hγ).symm ▸ rfl

/-- §34.1: the fibre `pr⁻¹(φ)` is `D_φ/G_φ`: the points `[φ, z]`, `z ∈ D_φ`, modulo `G_φ`. -/
theorem bersProjection_fiber (φ : ℂ → ℂ) (hφ : φ ∈ bersImage Γ) :
    bersProjection Γ ⁻¹' {φ} = {v | ∃ (z : ℂ) (hz : z ∈ bersDisc Γ φ), v = Quot.mk _ ⟨(φ, z), hφ, hz⟩} := by
  ext v
  induction v using Quot.ind with
  | mk p =>
    constructor
    · intro hv
      obtain ⟨⟨φ', z⟩, hφ', hz⟩ := p
      have h1 : φ' = φ := hv
      subst h1
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, hv⟩
      rw [hv]
      rfl

/-! ## §34.2 Bers' theorem -/

/-! ### s34b track (coordinator 553e2d), part A: representatives and convergence (target 1) -/

/-- The integrand of `‖(μ - ν)/(1 - ν̄μ)‖_∞` is bounded a.e. on `ℂ` by its essential supremum over `ℍ`: on `ℍ` by
`ENNReal.ae_le_essSup` (the supremum is finite, `≤ 2k/(1 + k²)` by `ahQ_pseudo_bound`), off `ℍ` since `μ = ν = 0`
there. -/
theorem b34_a_ae_le_dDN (μ ν : BeltramiH) :
    ∀ᵐ z, ‖(μ.1 z - ν.1 z) / (1 - conj (ν.1 z) * μ.1 z)‖ ≤ UniversalTeichmuller.dilatationDiffNorm μ.1 ν.1 := by
  obtain ⟨⟨kμ, hkμ0, hkμ1, -, hbμ⟩, hμ0⟩ := μ.2
  obtain ⟨⟨kν, -, hkν1, -, hbν⟩, hν0⟩ := ν.2
  rw [Measure.restrict_univ] at hbμ hbν
  have hk0 : 0 ≤ max kμ kν := le_max_of_le_left hkμ0
  have hk1 : max kμ kν < 1 := max_lt hkμ1 hkν1
  have hnn : ∀ x : ℂ, (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := fun x => (ofReal_norm x).symm
  have hne : essSup (fun z => (‖(μ.1 z - ν.1 z) / (1 - conj (ν.1 z) * μ.1 z)‖₊ : ℝ≥0∞))
      (volume.restrict upperHalf) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 2 * max kμ kν / (1 + max kμ kν ^ 2)))
      (essSup_le_of_ae_le _ ?_)
    filter_upwards [ae_restrict_of_ae hbμ, ae_restrict_of_ae hbν] with z h1 h2
    rw [hnn]
    exact ENNReal.ofReal_le_ofReal
      (ahQ_pseudo_bound hk0 hk1 (h1.trans (le_max_left _ _)) (h2.trans (le_max_right _ _)))
  have hae := ENNReal.ae_le_essSup (μ := volume.restrict upperHalf)
    (fun z => (‖(μ.1 z - ν.1 z) / (1 - conj (ν.1 z) * μ.1 z)‖₊ : ℝ≥0∞))
  rw [ae_restrict_iff' isOpen_upperHalf.measurableSet] at hae
  filter_upwards [hae] with z hz
  by_cases hi : 0 < z.im
  · have h1 := ENNReal.toReal_mono hne (hz hi)
    rw [ENNReal.coe_toReal, coe_nnnorm] at h1
    exact h1
  · rw [hμ0 z (not_lt.1 hi), hν0 z (not_lt.1 hi), sub_self, zero_div, norm_zero]
    exact ENNReal.toReal_nonneg

/-- **Q**: `f_ν ∘ f_{μ₀}⁻¹` is the normalized solution of `ahQuot ν μ₀ f_{μ₀}` (`ah_quotient`), a coefficient bounded
a.e. by `‖(ν - μ₀)/(1 - μ̄₀ν)‖_∞` (`b34_a_ae_le_dDN`, pulled back through `f_{μ₀}⁻¹`, `ahT_qmp_inv`). -/
theorem b34_a_quot (μ₀ ν : BeltramiH) :
    IsNormalizedSolution (normalizedSolution ν.1 ∘ Function.invFunOn (normalizedSolution μ₀.1) univ)
        (ahQuot ν.1 μ₀.1 (normalizedSolution μ₀.1)) ∧
      IsBeltramiCoeff (ahQuot ν.1 μ₀.1 (normalizedSolution μ₀.1)) univ
        (UniversalTeichmuller.dilatationDiffNorm ν.1 μ₀.1) := by
  obtain ⟨⟨kμ, hkμ0, hkμ1, hmμ, hbμ⟩, -⟩ := μ₀.2
  obtain ⟨⟨kν, -, hkν1, hmν, hbν⟩, -⟩ := ν.2
  have hk0 : 0 ≤ max kν kμ := le_max_of_le_right hkμ0
  have hk1 : max kν kμ < 1 := max_lt hkν1 hkμ1
  obtain ⟨hN, hB⟩ := ah_quotient hk0 hk1 ⟨hmν, hbν.mono fun z hz => hz.trans (le_max_left _ _)⟩
    ⟨hmμ, hbμ.mono fun z hz => hz.trans (le_max_right _ _)⟩ (ut_spec ν) (ut_spec μ₀)
  refine ⟨hN, hB.1, ?_⟩
  obtain ⟨hq, himg, -, -, -⟩ := ut_spec μ₀
  have hqmp := ahT_qmp_inv hq himg
  rw [Measure.restrict_univ]
  filter_upwards [hqmp.ae (b34_a_ae_le_dDN ν μ₀)] with w hw
  unfold ahQuot
  rw [norm_mul]
  exact (mul_le_mul hw (ahT_norm_div_conj_le _) (norm_nonneg _) ENNReal.toReal_nonneg).trans_eq (mul_one _)

/-- **PT**: normalized solutions `Fₙ` of coefficients with `‖νₙ‖_∞ ≤ εₙ → 0` converge pointwise to the identity:
`|Fₙ(w) - w| ≤ |Fₙ(w) - w - V[νₙ](w)| + |V[νₙ](w)| ≤ (1 + C_w) εₙ'` (`ah_first_variation`, `ah_var_bound`), with
`εₙ' = |εₙ| + 1/(n + 1) > 0`. -/
theorem b34_a_pt {F : ℕ → ℂ → ℂ} {ν : ℕ → ℂ → ℂ} {ε : ℕ → ℝ}
    (hF : ∀ n, IsNormalizedSolution (F n) (ν n)) (hν : ∀ n, IsBeltramiCoeff (ν n) univ (ε n))
    (hε : Tendsto ε atTop (𝓝 0)) (w : ℂ) : Tendsto (fun n => F n w) atTop (𝓝 w) := by
  set e : ℕ → ℝ := fun n => |ε n| + 1 / ((n : ℝ) + 1) with he
  have hepos : ∀ n, 0 < e n := fun n => by positivity
  have he0 : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => |ε n|) atTop (𝓝 0) := by simpa using hε.abs
    have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3
  have hνe : ∀ n, IsBeltramiCoeff (ν n) univ (e n) := fun n =>
    ⟨(hν n).1, (hν n).2.mono fun z hz =>
      hz.trans ((le_abs_self _).trans (le_add_of_nonneg_right (by positivity)))⟩
  obtain ⟨δ, hδ, hfv⟩ := ah_first_variation w 1 one_pos
  set C : ℝ := 1 / π * ∫ ζ, ‖ahKer w ζ‖ with hC
  have hC0 : 0 ≤ C := mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (by simpa using he0.const_mul (1 + C))
  filter_upwards [he0.eventually (ge_mem_nhds hδ)] with n hn
  have h1 := hfv (ν n) (F n) (e n) (hepos n) hn (hνe n) (hF n)
  have h2 := ah_var_bound w (hνe n)
  calc ‖F n w - w‖ = ‖(F n w - w - ahVar (ν n) w) + ahVar (ν n) w‖ := by ring_nf
    _ ≤ ‖F n w - w - ahVar (ν n) w‖ + ‖ahVar (ν n) w‖ := norm_add_le _ _
    _ ≤ 1 * e n + C * e n := add_le_add h1 h2
    _ = (1 + C) * e n := by ring

/-- **K**: a normalized solution of a coefficient with `‖ν‖_∞ ≤ ε ≤ 1/2` is a normalized `3`-q.c. map of the plane
(Theorem 13.7 with its uniqueness clause, `k = 1/2`). -/
theorem b34_a_K3 {F ν : ℂ → ℂ} {ε : ℝ} (hF : IsNormalizedSolution F ν) (hν : IsBeltramiCoeff ν univ ε)
    (hε : ε ≤ 1 / 2) : IsKQCNormalizedPlane F 3 := by
  have hν' : IsBeltramiCoeff ν univ (1 / 2) := ⟨hν.1, hν.2.mono fun z hz => hz.trans hε⟩
  obtain ⟨f, -, hfK, huniq⟩ := thm13_7_normalized_existence (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) hν'
  have e := huniq F hF
  refine ⟨?_, hF.2.1, hF.2.2.1, hF.2.2.2.1⟩
  rw [e]
  convert hfK using 1
  norm_num

/-- **U**: normalized `K`-q.c. maps of the plane converging pointwise to the identity converge uniformly on compact
sets (by contradiction: a bad subsequence has a locally uniformly convergent subsequence, `ut2_nf_extract`, whose limit
is the pointwise limit `id`). -/
theorem b34_a_tuo_id {h : ℕ → ℂ → ℂ} {K : ℝ} (hK : ∀ n, IsKQCNormalizedPlane (h n) K)
    (hpt : ∀ w, Tendsto (fun n => h n w) atTop (𝓝 w)) {S : Set ℂ} (hS : IsCompact S) :
    TendstoUniformlyOn h id atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hcon
  obtain ⟨ψ, hψ, G, hG⟩ := UniversalTeichmuller.ut2_nf_extract (fun n => hK (φ n))
  have hGid : G = id := by
    funext w
    exact tendsto_nhds_unique
      ((tendstoLocallyUniformly_iff_forall_isCompact.1 hG {w} isCompact_singleton).tendsto_at (mem_singleton w))
      ((hpt w).comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
  rw [hGid] at hG
  have hU := Metric.tendstoUniformlyOn_iff.1 (tendstoLocallyUniformly_iff_forall_isCompact.1 hG S hS) ε hε
  obtain ⟨n, hn⟩ := hU.exists
  exact hbad (ψ n) hn

/-- Uniform convergence on `S` of a shifted sequence `n ↦ F (n + N)` gives that of `F`. -/
theorem b34_a_tuo_shift {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {S : Set ℂ} (N : ℕ)
    (h : TendstoUniformlyOn (fun n => F (n + N)) f atTop S) : TendstoUniformlyOn F f atTop S := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  obtain ⟨M, hM⟩ := eventually_atTop.1 (h ε hε)
  refine eventually_atTop.2 ⟨M + N, fun n hn => ?_⟩
  have h1 := hM (n - N) (by omega)
  rwa [Nat.sub_add_cancel (by omega)] at h1

/-- **CONT** (continuous dependence in `‖(ν - μ₀)/(1 - μ̄₀ν)‖_∞`): if `‖(νₙ - μ₀)/(1 - μ̄₀νₙ)‖_∞ → 0` then
`f_{νₙ} → f_{μ₀}` uniformly on compact sets.  `hₙ = f_{νₙ} ∘ f_{μ₀}⁻¹` are normalized solutions of coefficients
`→ 0` in `L^∞` (`b34_a_quot`), hence tend to `id` pointwise (`b34_a_pt`), eventually `3`-q.c. (`b34_a_K3`), so
uniformly on the compact set `f_{μ₀}(S)` (`b34_a_tuo_id`); compose with `f_{μ₀}`. -/
theorem b34_a_cont (μ₀ : BeltramiH) {νs : ℕ → BeltramiH}
    (hd : Tendsto (fun n => UniversalTeichmuller.dilatationDiffNorm (νs n).1 μ₀.1) atTop (𝓝 0))
    {S : Set ℂ} (hS : IsCompact S) :
    TendstoUniformlyOn (fun n => normalizedSolution (νs n).1) (normalizedSolution μ₀.1) atTop S := by
  have hQ := fun n => b34_a_quot μ₀ (νs n)
  have hpt : ∀ w, Tendsto (fun n => (normalizedSolution (νs n).1 ∘
      Function.invFunOn (normalizedSolution μ₀.1) univ) w) atTop (𝓝 w) :=
    b34_a_pt (fun n => (hQ n).1) (fun n => (hQ n).2) hd
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hd.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have hK : ∀ n, IsKQCNormalizedPlane (normalizedSolution (νs (n + N)).1 ∘
      Function.invFunOn (normalizedSolution μ₀.1) univ) 3 := fun n =>
    b34_a_K3 (hQ (n + N)).1 (hQ (n + N)).2 (hN (n + N) (by omega))
  obtain ⟨K₀, hK₀⟩ := (ut_spec μ₀).1
  have hc : Continuous (normalizedSolution μ₀.1) := continuousOn_univ.1 hK₀.2.2.1.1
  have hS' : IsCompact (normalizedSolution μ₀.1 '' S) := hS.image hc
  have hU : TendstoUniformlyOn (fun n => normalizedSolution (νs n).1 ∘
      Function.invFunOn (normalizedSolution μ₀.1) univ) id atTop (normalizedSolution μ₀.1 '' S) :=
    b34_a_tuo_shift N (b34_a_tuo_id hK (fun w => (hpt w).comp (tendsto_add_atTop_nat N)) hS')
  have hU2 := (hU.comp (normalizedSolution μ₀.1)).mono (subset_preimage_image (normalizedSolution μ₀.1) S)
  refine hU2.congr (Eventually.of_forall fun n z _ => ?_)
  simp only [Function.comp_apply, s34_w_invFun_apply]

/-- **REP** (the representative, Theorem 33.1's construction at base point `μ₀`): if `‖χ(φ_μ)‖ < 1/2`, Lemma 33.3 for
`Γ^{μ₀}` gives `λ' ∈ M(Γ^{μ₀})` with `φ_{λ'} = χ(φ_μ)` and `λ' = -2y²χ(φ_μ)(z̄)` on `ℍ`; the pull-back
`ν = 1_ℍ μ_{f^{λ'} ∘ f^{μ₀}}` is `Γ`-compatible, `ν ∼ μ` (injectivity of `χ`), and
`‖(ν - μ₀)/(1 - μ̄₀ν)‖_∞ = ‖λ(ν)‖_∞ = ‖λ'‖_∞ ≤ 2‖χ(φ_μ)‖` (`b33_t_dd_tb`, `λ(μ₀) = 0`, `f^{λ(ν)} = f^{λ'}`). -/
theorem b34_a_rep (hΓ : IsFuchsian Γ) (μ₀ : BeltramiGamma Γ) {Γμ₀ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hFμ₀ : IsFuchsian Γμ₀)
    (hΓμ₀1 : ∀ γ ∈ Γ, ∃ γ' ∈ Γμ₀, ∀ z ∈ upperHalf,
      fMuSym μ₀.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
        mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ₀.1.1 z))
    {χ : (ℂ → ℂ) → (ℂ → ℂ)}
    (c2 : ∀ μ : BeltramiH, χ (bersFunction μ.1) = bersFunction (translatedBeltrami μ₀.1.1 μ.1))
    (c5 : ∀ μ : BeltramiH, bersFunction μ.1 ∈ automorphicQD Γ ↔ χ (bersFunction μ.1) ∈ automorphicQD Γμ₀)
    (c6 : InjOn χ (range fun μ : BeltramiH => bersFunction μ.1))
    (μ : BeltramiGamma Γ) (hsmall : bersNormL (χ (bersFunction μ.1.1)) < ENNReal.ofReal (1 / 2)) :
    ∃ ν : BeltramiGamma Γ, teichSetoidGamma Γ ν μ ∧
      UniversalTeichmuller.dilatationDiffNorm ν.1.1 μ₀.1.1 ≤ 2 * (bersNormL (χ (bersFunction μ.1.1))).toReal := by
  have hauto : χ (bersFunction μ.1.1) ∈ automorphicQD Γμ₀ := (c5 μ.1).1 (bersFunctionGamma_mem hΓ μ).1
  obtain ⟨lam, hlamμ, hlam⟩ := (lemma33_3 hFμ₀).2 _ hauto hsmall
  rw [bg_bersMapGamma_eq rfl] at hlam
  have hdef : ∀ γ' ∈ Γμ₀, ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ z ∈ upperHalf,
      fMuSym lam.1.1 (mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) z) =
        mobiusFn (A 0 0) (A 0 1) (A 1 0) (A 1 1) (fMuSym lam.1.1 z) := fun γ' hγ' => by
    obtain ⟨Γl, -, hc, -⟩ := exists_deformation_group hFμ₀ lam
    obtain ⟨A, -, hA⟩ := hc γ' hγ'
    exact ⟨A, hA⟩
  let ν : BeltramiGamma Γ := ⟨b33_t_pb μ₀.1 lam.1, b33_t_pb_compat μ₀.1 lam.1 hΓμ₀1 hdef⟩
  refine ⟨ν, ?_, ?_⟩
  · -- `χ(φ_ν) = χ(φ_μ)`, so `φ_ν = φ_μ` and `ν ∼ μ`
    have hχ : χ (bersFunction (b33_t_pb μ₀.1 lam.1).1) = χ (bersFunction μ.1.1) := by
      rw [c2, ← hlam]
      exact (b33_t_bf_eq_iff (b33_t_tb μ₀.1 (b33_t_pb μ₀.1 lam.1)) lam.1).2 (b33_t_tb_pb_equiv μ₀.1 lam.1)
    have hbf : bersFunction (b33_t_pb μ₀.1 lam.1).1 = bersFunction μ.1.1 := c6 ⟨_, rfl⟩ ⟨μ.1, rfl⟩ hχ
    exact (lemma33_1 ν.1 μ.1).2 ((b33_t_bf_eq_iff ν.1 μ.1).1 hbf)
  · -- the distance
    obtain ⟨hle, hs0, -⟩ := t203_t_toReal hsmall
    have hφs : ∀ z ∈ lowerHalf, ‖χ (bersFunction μ.1.1) z‖ * z.im ^ 2 ≤
        (bersNormL (χ (bersFunction μ.1.1))).toReal := by
      intro z hz
      have h1 : ENNReal.ofReal (‖χ (bersFunction μ.1.1) z‖ * z.im ^ 2) ≤ bersNormL (χ (bersFunction μ.1.1)) := by
        unfold bersNormL
        exact le_iSup₂_of_le z hz le_rfl
      exact (ENNReal.ofReal_le_ofReal_iff hs0).1 (h1.trans hle)
    -- `λ(ν) = 1_ℍ μ_{f^{λ'}}`
    have hcomp : fMuSym (b33_t_pb μ₀.1 lam.1).1 ∘ Function.invFunOn (fMuSym μ₀.1.1) univ = fMuSym lam.1.1 :=
      (b33_t_tb_fMuSym μ₀.1 (b33_t_pb μ₀.1 lam.1)).symm.trans (b33_t_tb_pb_fMuSym μ₀.1 lam.1)
    have htb : translatedBeltrami μ₀.1.1 (b33_t_pb μ₀.1 lam.1).1 =
        upperHalf.indicator (complexDilatation (fMuSym lam.1.1)) := by
      unfold translatedBeltrami
      rw [hcomp]
    have hdd : UniversalTeichmuller.dilatationDiffNorm ν.1.1 μ₀.1.1 =
        UniversalTeichmuller.dilatationDiffNorm (translatedBeltrami μ₀.1.1 (b33_t_pb μ₀.1 lam.1).1) 0 := by
      rw [← b33_t_tb_self μ₀.1]
      exact (b33_t_dd_tb μ₀.1 ν.1 μ₀.1).symm
    rw [hdd, bB_l_dilatationDiffNorm_zero, htb]
    obtain ⟨-, -, -, -, -, -, -, hdl⟩ := b33_t_fs_spec lam.1
    have hnn : ∀ x : ℂ, (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := fun x => (ofReal_norm x).symm
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (essSup_le_of_ae_le _ ?_)
    filter_upwards [hdl, ae_restrict_mem isOpen_upperHalf.measurableSet] with z hz hzU
    rw [hnn, indicator_of_mem hzU, hz, hlamμ z hzU]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hφs (conj z) (l333_bel_conj_mem hzU)
    rw [Complex.conj_im, neg_sq] at h
    simp only [norm_mul, norm_neg, norm_pow, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    nlinarith

/-- §34.2: `φₙ → φ₀` in `Q(G₀, 𝕃)` allows representatives with `‖μₙ - μ₀‖_∞ → 0`, and then
`f_{μₙ} → f_{μ₀}` uniformly on compact subsets of `ℂ`. -/
theorem normalizedSolution_tendsto_of_bers (hΓ : IsFuchsian Γ) {μn : ℕ → BeltramiGamma Γ} {μ₀ : BeltramiGamma Γ}
    (hconv : Tendsto (fun n => bersNormL (bersFunctionGamma (μn n) - bersFunctionGamma μ₀)) atTop (𝓝 0)) :
    ∃ νn : ℕ → BeltramiGamma Γ, (∀ n, teichSetoidGamma Γ (νn n) (μn n)) ∧
      Tendsto (fun n => UniversalTeichmuller.dilatationDiffNorm (νn n).1.1 μ₀.1.1) atTop (𝓝 0) ∧
      ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn (fun n => normalizedSolution (νn n).1.1) (normalizedSolution μ₀.1.1) atTop K := by
  obtain ⟨Γμ₀, hFμ₀, hΓμ₀1, hΓμ₀2⟩ := exists_deformation_group hΓ μ₀
  obtain ⟨χ, -, c2, c3, c4, c5, c6, -⟩ := eq33_12_translation hΓ μ₀ ⟨hΓμ₀1, hΓμ₀2⟩
  -- `‖χ(φ_{μₙ})‖ → 0` (clause (4) at `μ₀` and `χ(φ_{μ₀}) = 0`)
  have hs : Tendsto (fun n => bersNormL (χ (bersFunction (μn n).1.1))) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    by_cases htop : ε = ⊤
    · exact Eventually.of_forall fun n => htop ▸ le_top
    have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
    obtain ⟨δ, hδ, hcont⟩ := c4 μ₀.1 ε.toReal hεr
    filter_upwards [hconv.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ))] with n hn
    have h := hcont (μn n).1 hn
    rw [c3, sub_zero, ENNReal.ofReal_toReal htop] at h
    exact h.le
  -- the representatives
  have hrep : ∀ n, ∃ ν : BeltramiGamma Γ, teichSetoidGamma Γ ν (μn n) ∧
      (bersNormL (χ (bersFunction (μn n).1.1)) < ENNReal.ofReal (1 / 2) →
        UniversalTeichmuller.dilatationDiffNorm ν.1.1 μ₀.1.1 ≤
          2 * (bersNormL (χ (bersFunction (μn n).1.1))).toReal) := by
    intro n
    by_cases hn : bersNormL (χ (bersFunction (μn n).1.1)) < ENNReal.ofReal (1 / 2)
    · obtain ⟨ν, h1, h2⟩ := b34_a_rep hΓ μ₀ hFμ₀ hΓμ₀1 c2 c5 c6 (μn n) hn
      exact ⟨ν, h1, fun _ => h2⟩
    · exact ⟨μn n, fun _ => rfl, fun h => absurd h hn⟩
  choose νn hνn1 hνn2 using hrep
  have hd : Tendsto (fun n => UniversalTeichmuller.dilatationDiffNorm (νn n).1.1 μ₀.1.1) atTop (𝓝 0) := by
    have hsr : Tendsto (fun n => 2 * (bersNormL (χ (bersFunction (μn n).1.1))).toReal) atTop (𝓝 0) := by
      have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hs
      simpa using h.const_mul 2
    refine squeeze_zero' (Eventually.of_forall fun n => ENNReal.toReal_nonneg) ?_ hsr
    filter_upwards [hs.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (by norm_num : (0 : ℝ) < 1 / 2)))]
      with n hn
    exact hνn2 n hn
  exact ⟨νn, hνn1, hd, fun K hK => b34_a_cont (νs := fun n => (νn n).1) μ₀.1 hd hK⟩

/-! ### s34b track (coordinator 553e2d), part B: the discontinuity of the action (target 2) -/

/-- `f_μ` is a homeomorphism of the plane onto itself (`t203_pack_homeo`). -/
theorem b34_b_homeo (μ : BeltramiH) : ∃ e : ℂ ≃ₜ ℂ, ⇑e = normalizedSolution μ.1 := by
  obtain ⟨⟨K, hK⟩, hs, -⟩ := ut_spec μ
  exact t203_pack_homeo hK hs

/-- A sequence with `‖x n - x₀‖ < 1/(n+1)` tends to `x₀`. -/
theorem b34_b_tendsto_of_lt {x : ℕ → ℂ} {x₀ : ℂ} (h : ∀ n : ℕ, ‖x n - x₀‖ < 1 / ((n : ℝ) + 1)) :
    Tendsto x atTop (𝓝 x₀) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => (h n).le) tendsto_one_div_add_atTop_nhds_zero_nat

/-- A sequence in `ℝ≥0∞` with `a n < ofReal (1/(n+1))` tends to `0`. -/
theorem b34_b_ennreal_tendsto {a : ℕ → ℝ≥0∞} (h : ∀ n : ℕ, a n < ENNReal.ofReal (1 / ((n : ℝ) + 1))) :
    Tendsto a atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ => zero_le)
    (fun n => (h n).le)

/-- **Inverse convergence.**  If continuous, injective, open maps `F n` converge to a continuous injective `f`
uniformly on compact sets, `F n (w n) = z n` and `z n → f w₀`, then `w n → w₀`.  For `r > 0` let
`δ = min_{|w - w₀| = r} |f w - f w₀| > 0`; for large `n` the ball `B(f w₀, 2δ/3)` misses `F n (∂B(w₀, r))` and meets
`F n (B(w₀, r))` (at `F n w₀`), so by connectedness it lies in the open set `F n (B(w₀, r))`; it contains `z n`, and
injectivity puts `w n` in `B(w₀, r)`. -/
theorem b34_b_inv_tendsto {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hFo : ∀ n, IsOpenMap (F n))
    (hFc : ∀ n, Continuous (F n)) (hFi : ∀ n, Function.Injective (F n)) (hfc : Continuous f)
    (hfi : Function.Injective f) (hconv : ∀ K : Set ℂ, IsCompact K → TendstoUniformlyOn F f atTop K)
    {z w : ℕ → ℂ} {w₀ : ℂ} (hz : Tendsto z atTop (𝓝 (f w₀))) (hw : ∀ n, F n (w n) = z n) :
    Tendsto w atTop (𝓝 w₀) := by
  rw [Metric.tendsto_atTop]
  intro r hr
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere w₀ r).exists_isMinOn (NormedSpace.sphere_nonempty.2 hr.le)
    (hfc.sub continuous_const).norm.continuousOn
  have hδ : 0 < ‖f u - f w₀‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    intro h
    have h' := hfi h
    rw [mem_sphere, h', dist_self] at hu
    exact hr.ne hu
  set δ := ‖f u - f w₀‖ with hδdef
  have h1 := Metric.tendstoUniformlyOn_iff.1 (hconv _ (isCompact_closedBall w₀ r)) (δ / 3) (by positivity)
  have h2 := Metric.tendsto_nhds.1 hz (δ / 3) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h1.and h2)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hA, hB⟩ := hN n hn
  have key : ball (f w₀) (2 * δ / 3) ⊆ F n '' ball w₀ r := by
    refine IsPreconnected.subset_left_of_subset_union (hFo n _ isOpen_ball)
      ((isCompact_closedBall w₀ r).image (hFc n)).isClosed.isOpen_compl
      (disjoint_compl_right_iff_subset.2 (image_mono ball_subset_closedBall)) ?_ ?_ isPreconnected_ball
    · intro y hy
      by_cases hy' : y ∈ F n '' closedBall w₀ r
      · left
        obtain ⟨v, hv, rfl⟩ := hy'
        refine ⟨v, ?_, rfl⟩
        rw [mem_ball]
        rcases (mem_closedBall.1 hv).lt_or_eq with hlt | heq
        · exact hlt
        · exfalso
          have hm : δ ≤ ‖f v - f w₀‖ := isMinOn_iff.1 hmin v (mem_sphere.2 heq)
          have hc := hA v hv
          rw [mem_ball, dist_eq_norm] at hy
          rw [dist_eq_norm] at hc
          have := norm_sub_le_norm_sub_add_norm_sub (f v) (F n v) (f w₀)
          linarith
      · right
        exact hy'
    · refine ⟨F n w₀, ?_, w₀, mem_ball_self hr, rfl⟩
      have := hA w₀ (mem_closedBall_self hr.le)
      rw [mem_ball, dist_comm]
      linarith
  obtain ⟨v, hv, hvz⟩ := key (show z n ∈ ball (f w₀) (2 * δ / 3) by
    rw [mem_ball]
    linarith)
  have hwv : w n = v := hFi n (by rw [hw n, hvz])
  rw [hwv]
  exact hv

/-- **Discreteness.**  If `w n → w₀` in `ℍ` and `γ n (w n) → w₀` with `γ n ∈ Γ ∖ {±1}`, then `Γ` is not a freely
acting Fuchsian group: on the compact disc `C = B̄(w₀, Im w₀/2) ⊆ ℍ` only finitely many `γ ∈ Γ` move a point of `C`
into `C` (`IsFuchsian`), so some `γ ≠ ±1` equals `γ n` for infinitely many `n`, and then `γ w₀ = w₀`, contradicting
`ActsFreely`. -/
theorem b34_b_fuchsian_contra (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {w : ℕ → ℂ} {w₀ : ℂ}
    (hw : ∀ n, w n ∈ upperHalf) (hw₀ : w₀ ∈ upperHalf) (hlim : Tendsto w atTop (𝓝 w₀))
    {γ : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : ∀ n, γ n ∈ Γ) (hγ1 : ∀ n, γ n ≠ 1)
    (hγ2 : ∀ n, γ n ≠ -1)
    (hlim' : Tendsto (fun n => mobiusFn (γ n 0 0) (γ n 0 1) (γ n 1 0) (γ n 1 1) (w n)) atTop (𝓝 w₀)) :
    False := by
  have hw₀' : 0 < w₀.im := hw₀
  have hr0 : 0 < w₀.im / 2 := by positivity
  have hball : closedBall w₀ (w₀.im / 2) ⊆ range UpperHalfPlane.coe := by
    intro z hz
    refine ⟨⟨z, ?_⟩, rfl⟩
    have h1 : |z.im - w₀.im| ≤ w₀.im / 2 := by
      have := abs_im_le_norm (z - w₀)
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [sub_im] at this
      linarith
    have := (abs_le.1 h1).1
    linarith
  set C : Set UpperHalfPlane := UpperHalfPlane.coe ⁻¹' closedBall w₀ (w₀.im / 2) with hCdef
  have hC : IsCompact C :=
    UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage' (isCompact_closedBall _ _) hball
  have hfin : {γ ∈ Γ | ((γ • ·) '' C ∩ C).Nonempty}.Finite := hΓ C hC
  have hev : ∀ᶠ n in atTop, γ n ∈ {γ ∈ Γ | ((γ • ·) '' C ∩ C).Nonempty} := by
    filter_upwards [hlim (closedBall_mem_nhds w₀ hr0), hlim' (closedBall_mem_nhds w₀ hr0)] with n h1 h2
    refine ⟨hγ n, γ n • (⟨w n, hw n⟩ : UpperHalfPlane), ⟨⟨w n, hw n⟩, h1, rfl⟩, ?_⟩
    show ((γ n • (⟨w n, hw n⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ closedBall w₀ (w₀.im / 2)
    rw [← b33_d_mobiusFn_smul]
    exact h2
  obtain ⟨g, hg, hfreq⟩ : ∃ g ∈ {γ ∈ Γ | ((γ • ·) '' C ∩ C).Nonempty}, ∃ᶠ n in atTop, γ n = g := by
    by_contra hcon
    simp only [not_exists, not_and, Filter.not_frequently] at hcon
    have hall : ∀ᶠ n in atTop, ∀ g ∈ {γ ∈ Γ | ((γ • ·) '' C ∩ C).Nonempty}, γ n ≠ g :=
      (eventually_all_finite hfin).2 hcon
    obtain ⟨n, hn1, hn2⟩ := (hev.and hall).exists
    exact hn2 _ hn1 rfl
  obtain ⟨n₀, hn₀⟩ := hfreq.exists
  have hg1 : g ≠ 1 := hn₀ ▸ hγ1 n₀
  have hg2 : g ≠ -1 := hn₀ ▸ hγ2 n₀
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rwa [Matrix.det_fin_two] at h
  have hden : ((g 1 0 : ℝ) : ℂ) * w₀ + ((g 1 1 : ℝ) : ℂ) ≠ 0 := bg2_d_den_ne_zero hdet hw₀'.ne'
  have hgc : ContinuousAt (mobiusFn (g 0 0) (g 0 1) (g 1 0) (g 1 1)) w₀ := by
    unfold mobiusFn
    exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hden
  have hfix : mobiusFn (g 0 0) (g 0 1) (g 1 0) (g 1 1) w₀ = w₀ :=
    tendsto_nhds_unique_of_frequently_eq (hgc.tendsto.comp hlim) hlim' (hfreq.mono fun n hn => by
      simp only [Function.comp_apply, hn])
  have hfix' : g • (⟨w₀, hw₀'⟩ : UpperHalfPlane) = ⟨w₀, hw₀'⟩ := by
    apply UpperHalfPlane.ext
    rw [← b33_d_mobiusFn_smul]
    exact hfix
  rcases hfree g hg.1 _ hfix' with h | h
  · exact hg1 h
  · exact hg2 h

/-- **Main (§34.2 discontinuity), modulo target 1.**  Given the representative/convergence statement of
`normalizedSolution_tendsto_of_bers` as the hypothesis `h1`, `G₀` acts discontinuously on `F(G₀)`: otherwise, with
`ε = 1/(n+1)`, there are `γₙ ∈ Γ ∖ {±1}` and `(φₙ, zₙ)`, `(φₙ, z'ₙ)` near `(φ₀, z₀)` with `(γₙ)_{φₙ}(zₙ) = z'ₙ`; `h1`
gives representatives `νₙ` of `φₙ` with `f_{νₙ} → f_{μ₀}` locally uniformly, so `wₙ = f_{νₙ}⁻¹(zₙ) → w₀` and
`γₙ(wₙ) = f_{νₙ}⁻¹(z'ₙ) → w₀` (`b34_b_inv_tendsto`), which contradicts `b34_b_fuchsian_contra`. -/
theorem b34_b_main (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (h1 : ∀ {μn : ℕ → BeltramiGamma Γ} {μ₀ : BeltramiGamma Γ},
      Tendsto (fun n => bersNormL (bersFunctionGamma (μn n) - bersFunctionGamma μ₀)) atTop (𝓝 0) →
      ∃ νn : ℕ → BeltramiGamma Γ, (∀ n, teichSetoidGamma Γ (νn n) (μn n)) ∧
        Tendsto (fun n => UniversalTeichmuller.dilatationDiffNorm (νn n).1.1 μ₀.1.1) atTop (𝓝 0) ∧
        ∀ K : Set ℂ, IsCompact K →
          TendstoUniformlyOn (fun n => normalizedSolution (νn n).1.1) (normalizedSolution μ₀.1.1) atTop K)
    (p₀ : BersFiberSpace Γ) :
    ∃ ε > 0, ∀ γ ∈ Γ, γ ≠ 1 → γ ≠ -1 → ∀ p q : BersFiberSpace Γ,
      bersNormL (p.1.1 - p₀.1.1) < ENNReal.ofReal ε → ‖p.1.2 - p₀.1.2‖ < ε →
      bersNormL (q.1.1 - p₀.1.1) < ENNReal.ofReal ε → ‖q.1.2 - p₀.1.2‖ < ε →
      bersFiberSpaceAction Γ γ p.1 ≠ q.1 := by
  by_contra hcon
  have key : ∀ n : ℕ, ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ ∈ Γ ∧ γ ≠ 1 ∧ γ ≠ -1 ∧
      ∃ p q : BersFiberSpace Γ, bersNormL (p.1.1 - p₀.1.1) < ENNReal.ofReal (1 / ((n : ℝ) + 1)) ∧
        ‖p.1.2 - p₀.1.2‖ < 1 / ((n : ℝ) + 1) ∧ ‖q.1.2 - p₀.1.2‖ < 1 / ((n : ℝ) + 1) ∧
        bersFiberSpaceAction Γ γ p.1 = q.1 := by
    intro n
    by_contra hn
    apply hcon
    exact ⟨1 / ((n : ℝ) + 1), by positivity, fun γ hγ hγ1 hγ2 p q hp1 hp2 _ hq2 heq =>
      hn ⟨γ, hγ, hγ1, hγ2, p, q, hp1, hp2, hq2, heq⟩⟩
  choose γ hγ hγ1 hγ2 p q hp1 hp2 hq2 heq using key
  -- a representative `μ₀` of `φ₀` and `z₀ = f_{μ₀}(w₀)`, `w₀ ∈ ℍ`
  obtain ⟨μ₀, hμ₀, w₀, hw₀, hfw₀⟩ := p₀.2.2
  -- representatives `μₙ` of `φₙ`
  have hrep : ∀ n, ∃ μ : BeltramiGamma Γ, bersFunctionGamma μ = (p n).1.1 := fun n => by
    obtain ⟨μ, hμ, -⟩ := (p n).2.2
    exact ⟨μ, hμ⟩
  choose μn hμn using hrep
  have hconv : Tendsto (fun n => bersNormL (bersFunctionGamma (μn n) - bersFunctionGamma μ₀)) atTop (𝓝 0) := by
    refine b34_b_ennreal_tendsto fun n => ?_
    rw [hμn n, hμ₀]
    exact hp1 n
  obtain ⟨νn, hequiv, -, hunif⟩ := h1 hconv
  have hφν : ∀ n, bersFunctionGamma (νn n) = (p n).1.1 := fun n =>
    (bersFunctionGamma_eq_of_equiv (hequiv n)).trans (hμn n)
  -- `zₙ = f_{νₙ}(wₙ)` with `wₙ ∈ ℍ`
  have hpre : ∀ n, ∃ v ∈ upperHalf, normalizedSolution (νn n).1.1 v = (p n).1.2 := fun n => by
    have h := (p n).2.2
    rw [← hφν n, (bersDisc_wellDefined (μ := νn n) (ν := νn n) rfl).2] at h
    exact h
  choose w hw hfw using hpre
  -- `z'ₙ = (γₙ)_{φₙ}(zₙ) = f_{νₙ}(γₙ wₙ)`
  have hq : ∀ n, normalizedSolution (νn n).1.1 (mobiusFn (γ n 0 0) (γ n 0 1) (γ n 1 0) (γ n 1 1) (w n)) =
      (q n).1.2 := fun n => by
    have h2 : bersFiberAction Γ (γ n) (p n).1.1 (p n).1.2 = (q n).1.2 := congrArg Prod.snd (heq n)
    rw [← h2, ← hφν n, (bersFiberAction_wellDefined hΓ (νn n) (hγ n)).1, ← hfw n, s34_w_invFun_apply]
  -- the maps are homeomorphisms of the plane
  have hFo : ∀ n, IsOpenMap (normalizedSolution (νn n).1.1) := fun n => by
    obtain ⟨e, he⟩ := b34_b_homeo (νn n).1
    rw [← he]
    exact e.isOpenMap
  have hFc : ∀ n, Continuous (normalizedSolution (νn n).1.1) := fun n => by
    obtain ⟨e, he⟩ := b34_b_homeo (νn n).1
    rw [← he]
    exact e.continuous
  have hFi : ∀ n, Function.Injective (normalizedSolution (νn n).1.1) := fun n => s34_w_inj (νn n).1
  have hfc : Continuous (normalizedSolution μ₀.1.1) := by
    obtain ⟨e, he⟩ := b34_b_homeo μ₀.1
    rw [← he]
    exact e.continuous
  have hfi : Function.Injective (normalizedSolution μ₀.1.1) := s34_w_inj μ₀.1
  have hz : Tendsto (fun n => (p n).1.2) atTop (𝓝 (normalizedSolution μ₀.1.1 w₀)) := by
    rw [hfw₀]
    exact b34_b_tendsto_of_lt hp2
  have hz' : Tendsto (fun n => (q n).1.2) atTop (𝓝 (normalizedSolution μ₀.1.1 w₀)) := by
    rw [hfw₀]
    exact b34_b_tendsto_of_lt hq2
  have hwlim := b34_b_inv_tendsto (F := fun n => normalizedSolution (νn n).1.1) hFo hFc hFi hfc hfi hunif hz hfw
  have hwlim' := b34_b_inv_tendsto (F := fun n => normalizedSolution (νn n).1.1) hFo hFc hFi hfc hfi hunif hz' hq
  exact b34_b_fuchsian_contra hΓ hfree hw hw₀ hwlim hγ hγ1 hγ2 hwlim'

/-- §34.2: `G₀` acts discontinuously on `F(G₀)`: every point `(φ₀, z₀)` has a neighbourhood `N`
(for the norm of `Q(G₀, 𝕃)` in the first and the Euclidean metric in the second coordinate) with
`γ(N) ∩ N = ∅` for every `γ ∈ G₀ ∖ {±I}`.  (If not, `(γₙ)_{φₙ}(zₙ) → z₀` with `zₙ → z₀`, and
`f_{μₙ} → f_{μ₀}` locally uniformly gives `(γₙ)_{φ₀}(U) ∩ U ≠ ∅`, contradicting the discontinuity of
`G_{φ₀}`.) -/
theorem bersFiber_action_discontinuous (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (p₀ : BersFiberSpace Γ) :
    ∃ ε > 0, ∀ γ ∈ Γ, γ ≠ 1 → γ ≠ -1 → ∀ p q : BersFiberSpace Γ,
      bersNormL (p.1.1 - p₀.1.1) < ENNReal.ofReal ε → ‖p.1.2 - p₀.1.2‖ < ε →
      bersNormL (q.1.1 - p₀.1.1) < ENNReal.ofReal ε → ‖q.1.2 - p₀.1.2‖ < ε →
      bersFiberSpaceAction Γ γ p.1 ≠ q.1 := by
  exact b34_b_main hΓ hfree (fun h => normalizedSolution_tendsto_of_bers hΓ h) p₀

/-- The normalized solution `f_μ` of a Beltrami coefficient `μ ∈ M(𝕃)` is injective on the whole plane (it is a
quasiconformal homeomorphism of `ℂ`). -/
theorem s34_h_injective (μ : BeltramiH) : Function.Injective (normalizedSolution μ.1) := by
  obtain ⟨K, hK⟩ := (ut_spec μ).1
  exact injOn_univ.1 hK.2.2.1.2.1

/-- A point `z` of the quasidisc `f_μ(ℍ)` is never the image `f_μ(w)` of a real point `w` (`f_μ` is injective and
`w ∉ ℍ`). -/
theorem s34_h_ne_pole (μ : BeltramiH) {w z : ℂ} (hw : w.im = 0) (hz : z ∈ normalizedSolution μ.1 '' upperHalf) :
    z ≠ normalizedSolution μ.1 w := by
  obtain ⟨u, hu, rfl⟩ := hz
  intro h
  have huw : u = w := s34_h_injective μ h
  have hu' : 0 < u.im := hu
  rw [huw, hw] at hu'
  exact lt_irrefl 0 hu'

/-- For a family `F t` of injective maps depending differentiably on `t` at every fixed point, `t ↦ (F t a - F t b)⁻¹`
is differentiable at `t₀` for any fixed `a, b` (the difference never vanishes if `a ≠ b`, and it is `0⁻¹ = 0` if
`a = b`). -/
theorem s34_h_inv_sub_diff (F : ℂ → ℂ → ℂ) {t₀ : ℂ} (hF : ∀ w, DifferentiableAt ℂ (fun t => F t w) t₀)
    (hinj : Function.Injective (F t₀)) (a b : ℂ) : DifferentiableAt ℂ (fun t => (F t a - F t b)⁻¹) t₀ := by
  by_cases hab : a = b
  · subst hab
    simp only [sub_self, inv_zero]
    exact differentiableAt_const _
  · exact ((hF a).sub (hF b)).inv (sub_ne_zero.2 fun h => hab (hinj h))

/-- §34.2: the holomorphic dependence behind the complex structure of `V(G₀)`: if the complex
dilatation `μ_t` depends holomorphically on parameters `t`, so does the normalized quasiconformal
map `f_{μ_t}(z)` (representation theorem); hence the transition maps `ζ = γ_φ(z)` of the local
coordinates `(t₁, …, t_{3g-3}, z)` of `V(G₀)` are holomorphic in `(t, z)`.

The second conjunct is taken over the parameters `t` for which `z` is a point of the fibre, `z ∈ D_{φ_t}`
(corrected 2026-09-25): `γ_{φ_t}` is a Möbius map whose pole `f_t(-d/c)` moves with `t`, so for a fixed `z`
the map `t ↦ γ_{φ_t}(z)` is not holomorphic at a parameter putting `z` on the pole. -/
theorem bersFiber_holomorphic_dependence (hΓ : IsFuchsian Γ) {P : Set ℂ} (hP : IsOpen P)
    {μ : ℂ → BeltramiGamma Γ} (hhol : ∀ z, DifferentiableOn ℂ (fun t => (μ t).1.1 z) P) {k : ℝ} (hk : k < 1)
    (hbound : ∀ t ∈ P, ∀ z, ‖(μ t).1.1 z‖ ≤ k) :
    (∀ z, DifferentiableOn ℂ (fun t => normalizedSolution (μ t).1.1 z) P) ∧
      ∀ γ ∈ Γ, ∀ z, DifferentiableOn ℂ (fun t => bersFiberAction Γ γ (bersFunctionGamma (μ t)) z)
        {t ∈ P | z ∈ bersDisc Γ (bersFunctionGamma (μ t))} := by
  have hA : ∀ z, DifferentiableOn ℂ (fun t => normalizedSolution (μ t).1.1 z) P := by
    intro z t₀ ht₀
    have hk₀ : 0 ≤ k := (norm_nonneg _).trans (hbound t₀ ht₀ 0)
    have hkP : ∀ t ∈ P, IsBeltramiCoeff (μ t).1.1 univ k := by
      intro t ht
      obtain ⟨_, -, -, hm, -⟩ := (μ t).1.2.1
      exact ⟨hm, Eventually.of_forall fun w => hbound t ht w⟩
    exact thm13_8_ahlfors_bers_holomorphic (μ := fun t => (μ t).1.1)
      (f := fun t => normalizedSolution (μ t).1.1) hP hk₀ hk hkP hhol (fun t _ => ut_spec (μ t).1) z t₀ ht₀
  refine ⟨hA, fun γ hγ z t₀ ht₀ => ?_⟩
  have hact : ∀ t, bersFiberAction Γ γ (bersFunctionGamma (μ t)) z =
      normalizedSolution (μ t).1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
        (Function.invFunOn (normalizedSolution (μ t).1.1) univ z)) :=
    fun t => (bersFiberAction_wellDefined hΓ (μ t) hγ).1 z
  have hAt : ∀ w, DifferentiableAt ℂ (fun t => normalizedSolution (μ t).1.1 w) t₀ :=
    fun w => (hA w).differentiableAt (hP.mem_nhds ht₀.1)
  by_cases hc : γ 1 0 = 0
  · have hD : DifferentiableAt ℂ (fun t =>
        (normalizedSolution (μ t).1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) 1) -
          normalizedSolution (μ t).1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) 0)) * z +
        normalizedSolution (μ t).1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) 0)) t₀ :=
      (((hAt _).sub (hAt _)).mul_const z).add (hAt _)
    refine hD.differentiableWithinAt.congr (fun t _ => ?_) ?_
    · rw [hact, s34_F_affine (μ t) hγ hc]
    · rw [hact, s34_F_affine (μ t₀) hγ hc]
  · have hne : ∀ t ∈ {t ∈ P | z ∈ bersDisc Γ (bersFunctionGamma (μ t))},
        z ≠ normalizedSolution (μ t).1.1 (-((γ 1 1 : ℂ) / γ 1 0)) := by
      intro t ht
      have hz : z ∈ normalizedSolution (μ t).1.1 '' upperHalf := by
        have h2 := ht.2
        rwa [(bersDisc_wellDefined (μ := μ t) (ν := μ t) rfl).2] at h2
      refine s34_h_ne_pole (μ t).1 ?_ hz
      rw [← Complex.ofReal_div, ← Complex.ofReal_neg, Complex.ofReal_im]
    have hG : ∀ x, DifferentiableAt ℂ (fun t => s34_G (normalizedSolution (μ t).1.1) γ x) t₀ :=
      fun x => s34_h_inv_sub_diff (fun t => normalizedSolution (μ t).1.1) hAt (s34_h_injective (μ t₀).1) _ _
    have hD : DifferentiableAt ℂ (fun t => normalizedSolution (μ t).1.1 ((γ 0 0 : ℂ) / γ 1 0) +
        ((s34_G (normalizedSolution (μ t).1.1) γ 1 - s34_G (normalizedSolution (μ t).1.1) γ 0) * z +
          s34_G (normalizedSolution (μ t).1.1) γ 0)⁻¹) t₀ :=
      (hAt _).add (((((hG 1).sub (hG 0)).mul_const z).add (hG 0)).inv (s34_F_pole (μ t₀) hγ hc (hne t₀ ht₀)).1)
    refine hD.differentiableWithinAt.congr (fun t ht => ?_) ?_
    · rw [hact, (s34_F_pole (μ t) hγ hc (hne t ht)).2]
    · rw [hact, (s34_F_pole (μ t₀) hγ hc (hne t₀ ht₀)).2]

/-- §34.2: `V(G₀)` is a complex manifold of dimension `3g - 2`: a point `[φ, z]` has the local
coordinates `(t₁, …, t_{3g-3}, z)` of `(φ, z)` in a neighbourhood `N` on which the action is free,
`φ = t₁φ₁ + ⋯ + t_{3g-3}φ_{3g-3}`; and `pr` is holomorphic, `(t, z) ↦ t` in these coordinates. -/
theorem bersQuotient_manifold {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ∃ (coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ) (_ : Function.Injective coords) (hopen : IsOpen (range coords))
      (_ : TopologicalSpace (BersQuotient Γ)) (_ : ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ)),
      IsManifold 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) ω (BersQuotient Γ) ∧
      ∃ pr : BersQuotient Γ → (⟨range coords, hopen⟩ : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ)),
        MDifferentiable 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) 𝓘(ℂ, Fin (3 * g - 3) → ℂ) pr ∧
        ∀ (q : TeichGamma Γ) (v : BersQuotient Γ), bersProjection Γ v = bersMapGamma Γ q → (pr v : Fin (3 * g - 3) → ℂ) = coords q := by
  sorry

/-- **Theorem 34.1 (Bers)**: `(V(G₀), T_{G₀}, pr)` is a holomorphic family, in the sense of
Kodaira–Spencer, of closed Riemann surfaces of genus `g > 1`; the fibre over `φ` is `D_φ/G_φ`, the
Riemann surface corresponding to the point `φ ∈ T_{G₀}`. -/
theorem thm34_1_bers {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S]
    [IsManifold 𝓘(ℂ) ω S] {g : ℕ} (hg : 1 < g) (hS : HasGenus S g) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {p : UpperHalfPlane → S} (hp : IsUniformization Γ p) :
    ∃ (coords : TeichGamma Γ → Fin (3 * g - 3) → ℂ) (_ : Function.Injective coords) (hopen : IsOpen (range coords))
      (_ : TopologicalSpace (BersQuotient Γ)) (_ : ChartedSpace (Fin (3 * g - 3 + 1) → ℂ) (BersQuotient Γ))
      (_ : IsManifold 𝓘(ℂ, Fin (3 * g - 3 + 1) → ℂ) ω (BersQuotient Γ))
      (pr : BersQuotient Γ → (⟨range coords, hopen⟩ : TopologicalSpace.Opens (Fin (3 * g - 3) → ℂ))),
      IsHolomorphicFamily (n := 3 * g - 3) pr ∧
      ∀ q : TeichGamma Γ, ∃ (X : ClosedRS.{u}) (j : X.carrier → BersQuotient Γ) (cov : ℂ → X.carrier),
        HasGenus X.carrier g ∧ Topology.IsEmbedding j ∧
        (range j = pr ⁻¹' {⟨coords q, mem_range_self q⟩}) ∧
        (∀ z (hz : z ∈ bersDisc Γ (bersMapGamma Γ q)), j (cov z) = Quot.mk _ ⟨(bersMapGamma Γ q, z), ⟨q, rfl⟩, hz⟩) ∧
        MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) cov (bersDisc Γ (bersMapGamma Γ q)) ∧
        ∀ z ∈ bersDisc Γ (bersMapGamma Γ q), ∀ w ∈ bersDisc Γ (bersMapGamma Γ q),
          (cov z = cov w ↔ ∃ γ ∈ Γ, w = bersFiberAction Γ γ (bersMapGamma Γ q) z) := by
  sorry

end LiZhongQC
