import LiZhongQC.Ch04.S16_Quasicircles

/-!
# §17 拟共形映射的边界值与拟共形扩张 — Boundary values of quasiconformal maps and extensions

* (17.2) the ratio `Δ(x, t)`; Theorem 17.1 (boundary values are `λ(K)`-quasisymmetric)
* Definition 17.1 (`ρ`-quasisymmetric functions)          — `IsQuasisymmetric`
* the Beurling–Ahlfors extension (17.6)                   — `beurlingAhlfors`
* Theorem 17.2 (Beurling–Ahlfors, `K ≤ 8ρ(ρ+1)`) and (17.7) (`K ≤ ρ²` for a suitable `r`)
* quasi-isometry of the Beurling–Ahlfors extension (17.20)
* corollary: a Jordan curve is a quasicircle iff its welding homeomorphism is quasisymmetric

## What is proved here

(17.13), and (2026-09-25) Theorem 17.1: the boundary values of a `K`-q.c. self-map of `ℍ` fixing `∞` are
`λ(K)`-quasisymmetric (reflection extension, normalization `-1, 0, 1 ↦ -1, 0, r`, and the ring bound
`Λ(R) ≤ K Λ(R')` from Teichmüller's extremal problem via bounded sub-rings of `T_R`).  The Beurling–Ahlfors theorem
and (17.20) are the substance of the rest of the section, and the two corollaries need the welding theorem of §16.3.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace LiZhongQC

/-- (17.2): `Δ(x, t) = (h(x+t) - h(x))/(h(x) - h(x-t))`. -/
def qsRatio (h : ℝ → ℝ) (x t : ℝ) : ℝ := (h (x + t) - h x) / (h x - h (x - t))

/-- **Definition 17.1** (`ρ` 拟对称).  An increasing homeomorphism `h : ℝ → ℝ` is
`ρ`-quasisymmetric: `ρ⁻¹ ≤ (h(x+t) - h(x))/(h(x) - h(x-t)) ≤ ρ` for all `x` and `t > 0`. -/
def IsQuasisymmetric (h : ℝ → ℝ) (ρ : ℝ) : Prop :=
  StrictMono h ∧ Continuous h ∧ Tendsto h atTop atTop ∧ Tendsto h atBot atBot ∧
    ∀ x t : ℝ, 0 < t → ρ⁻¹ ≤ qsRatio h x t ∧ qsRatio h x t ≤ ρ

/-- `g` is a `K`-q.c. self-map of the upper half-plane with boundary values `h` on `ℝ`. -/
def HasQCExtensionH (h : ℝ → ℝ) (g : ℂ → ℂ) (K : ℝ) : Prop :=
  IsKQC g upperHalf K ∧ g '' upperHalf = upperHalf ∧
    ∃ G : ExtPlane → ExtPlane, IsHomeoExtension g upperHalf upperHalf G ∧ G extInf = extInf ∧
      ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = (((h x : ℝ) : ℂ) : ExtPlane)

/-! ### Batch-4 interface (coordinator 553e2d): boundary values of q.c. self-maps of `ℍ` -/

/-- A boundary extension `G` of a self-map `g` of `ℍ` with `G ∞ = ∞` forces `g(z) → ∞` as `z → ∞` in `ℍ`: `G` is
continuous at `∞` within `closure ℍ` in `ℂ̄`, and `z → ∞` in `ℂ` means `↑z → ∞` in `ℂ̄`. -/
theorem b4_ext_tendsto_cocompact {g : ℂ → ℂ} {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension g upperHalf upperHalf G) (hGinf : G extInf = extInf) :
    Tendsto g (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) := by
  have hcoe : Tendsto ((↑) : ℂ → ExtPlane) (cocompact ℂ ⊓ 𝓟 upperHalf)
      (𝓝[closure (toExt upperHalf)] extInf) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, mem_inf_of_right (mem_principal.2 fun z hz =>
      subset_closure (show ((z : ℂ) : ExtPlane) ∈ toExt upperHalf from mem_image_of_mem _ hz))⟩
    rw [← Filter.coclosedCompact_eq_cocompact]
    exact OnePoint.tendsto_coe_infty.mono_left inf_le_left
  have hGt : Tendsto (G ∘ ((↑) : ℂ → ExtPlane)) (cocompact ℂ ⊓ 𝓟 upperHalf) (𝓝 extInf) := by
    have h := (hG.2.1 extInf s13x_rf_infty_mem_closure).tendsto.comp hcoe
    rwa [hGinf] at h
  have heq : (G ∘ ((↑) : ℂ → ExtPlane)) =ᶠ[cocompact ℂ ⊓ 𝓟 upperHalf]
      (fun z => ((g z : ℂ) : ExtPlane)) :=
    mem_inf_of_right (mem_principal.2 fun z hz => hG.1 z hz)
  have hlim : Tendsto g (cocompact ℂ ⊓ 𝓟 upperHalf) (comap ((↑) : ℂ → ExtPlane) (𝓝 extInf)) :=
    tendsto_comap_iff.2 (hGt.congr' heq)
  rwa [OnePoint.comap_coe_nhds_infty, Filter.coclosedCompact_eq_cocompact] at hlim

/-- A continuous map `G₀` of the plane equal to `g` on `ℍ` agrees on `ℝ` with the boundary extension `G` of `g`:
approach `x ∈ ℝ` from inside `ℍ` and use the continuity of `G` within `closure ℍ` in `ℂ̄`. -/
theorem b4_ext_coe_eq_of_real {g G₀ : ℂ → ℂ} {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension g upperHalf upperHalf G) (hG₀ : Continuous G₀)
    (hG₀g : EqOn G₀ g upperHalf) (x : ℝ) :
    ((G₀ (x : ℂ) : ℂ) : ExtPlane) = G ((x : ℂ) : ExtPlane) := by
  have hx : (x : ℂ) ∈ closure upperHalf := by
    rw [show upperHalf = {z : ℂ | 0 < z.im} from rfl, Complex.closure_setOfPred_lt_im]
    exact (Complex.ofReal_im x).ge
  have : (𝓝[upperHalf] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hx
  have h₁ : Tendsto (fun z => ((G₀ z : ℂ) : ExtPlane)) (𝓝[upperHalf] (x : ℂ))
      (𝓝 ((G₀ (x : ℂ) : ℂ) : ExtPlane)) :=
    ((OnePoint.continuous_coe.comp hG₀).tendsto _).mono_left nhdsWithin_le_nhds
  have hcoe : Tendsto ((↑) : ℂ → ExtPlane) (𝓝[upperHalf] (x : ℂ))
      (𝓝[closure (toExt upperHalf)] ((x : ℂ) : ExtPlane)) :=
    OnePoint.continuous_coe.continuousWithinAt.tendsto_nhdsWithin fun z hz =>
      subset_closure (show ((z : ℂ) : ExtPlane) ∈ toExt upperHalf from mem_image_of_mem _ hz)
  have h₂ : Tendsto (G ∘ ((↑) : ℂ → ExtPlane)) (𝓝[upperHalf] (x : ℂ))
      (𝓝 (G ((x : ℂ) : ExtPlane))) :=
    (hG.2.1 _ (s13x_rf_coe_mem_closure (Complex.ofReal_im x).ge)).tendsto.comp hcoe
  have heq : (fun z => ((G₀ z : ℂ) : ExtPlane)) =ᶠ[𝓝[upperHalf] (x : ℂ)]
      (G ∘ ((↑) : ℂ → ExtPlane)) :=
    eventually_nhdsWithin_of_forall fun z hz => by
      show ((G₀ z : ℂ) : ExtPlane) = G z
      rw [hG₀g hz, hG.1 z hz]
  exact tendsto_nhds_unique (h₁.congr' heq) h₂

/-- The reflected extension: a `K`-q.c. self-map `g` of `ℍ` with boundary values `h` fixing `∞` extends to a `K`-q.c.
map of the plane onto itself that equals `h` on `ℝ` (`qc_reflection_extension`, whose hypothesis at `∞` follows from
`G ∞ = ∞` and the continuity of `G`; on `ℝ` the extension agrees with `G` by continuity). -/
theorem b4_qs_extension {h : ℝ → ℝ} {g : ℂ → ℂ} {K : ℝ} (hg : HasQCExtensionH h g K) :
    ∃ G₀ : ℂ → ℂ, IsKQC G₀ univ K ∧ G₀ '' univ = univ ∧ ∀ x : ℝ, G₀ (x : ℂ) = (h x : ℂ) := by
  obtain ⟨hgK, himg, G, hG, hGinf, hGh⟩ := hg
  obtain ⟨G₀, hG₀K, hG₀s, hG₀g, -⟩ :=
    qc_reflection_extension hgK himg (b4_ext_tendsto_cocompact hG hGinf)
  exact ⟨G₀, hG₀K, hG₀s, fun x => OnePoint.coe_injective
    ((b4_ext_coe_eq_of_real hG (continuousOn_univ.1 hG₀K.2.2.1.1) hG₀g x).trans (hGh x))⟩

/-- A strictly decreasing `4`-tuple of reals is not in cyclically strictly increasing order: every cyclic shift
`i ↦ y (i + k)` has two consecutive indices (`0, 1` for `k ≠ 3`, `1, 2` for `k = 3`) that do not wrap around. -/
theorem b4_mono_not_cyclicStrictMono_of_strictAnti {y : Fin 4 → ℝ} (hy : StrictAnti y) :
    ¬ CyclicStrictMono y := by
  rintro ⟨k, hk⟩
  have h01 := hk (show (0 : Fin 4) < 1 by decide)
  have h12 := hk (show (1 : Fin 4) < 2 by decide)
  have a01 := hy (show (0 : Fin 4) < 1 by decide)
  have a12 := hy (show (1 : Fin 4) < 2 by decide)
  have a23 := hy (show (2 : Fin 4) < 3 by decide)
  fin_cases k <;> simp at h01 h12 <;> linarith

/-- The boundary values `h` of a `K`-q.c. self-map of `ℍ` fixing `∞` form an increasing homeomorphism of `ℝ` onto `ℝ`:
`h` is continuous and injective, increasing by sense preservation (the cyclic order of boundary points is preserved,
`cyclicOrder_preserved_of_isHomeoExtension_of_fixes_infty` with the local winding `qcl_r_hloc_of_isKQC`), and
`h(x) → ±∞` as `x → ±∞` since `G ∞ = ∞`. -/
theorem b4_qs_monotone {h : ℝ → ℝ} {g : ℂ → ℂ} {K : ℝ} (hg : HasQCExtensionH h g K) :
    StrictMono h ∧ Continuous h ∧ Tendsto h atTop atTop ∧ Tendsto h atBot atBot := by
  obtain ⟨G₀, hG₀, hG₀s, hG₀h⟩ := b4_qs_extension hg
  obtain ⟨hgK, hgs, G, hG, hinf, hGh⟩ := hg
  obtain ⟨e, he⟩ := t1_homeomorph hG₀ hG₀s
  have heh : ∀ x : ℝ, e (x : ℂ) = (h x : ℂ) := fun x => by rw [he, hG₀h x]
  -- continuity and injectivity: `h x = Re e(x)`
  have hcont : Continuous h := by
    have hfun : h = fun x : ℝ => (e (x : ℂ)).re := funext fun x => by rw [heh x, Complex.ofReal_re]
    rw [hfun]
    exact Complex.continuous_re.comp (e.continuous.comp Complex.continuous_ofReal)
  have hinj : Function.Injective h := fun a b hab =>
    Complex.ofReal_injective (e.injective (by rw [heh a, heh b, hab]))
  -- orientation: a decreasing `h` would reverse the cyclic order of `0, 1, 2, 3`
  have hmono : StrictMono h := by
    refine (hcont.strictMono_of_inj hinj).resolve_right fun hanti => ?_
    have hI : I ∈ upperHalf := by
      show (0 : ℝ) < I.im
      simp
    have hx : StrictMono fun i : Fin 4 => ((i : ℕ) : ℝ) := fun i j hij =>
      Nat.cast_lt.mpr (Fin.lt_def.mp hij)
    have hcyc := cyclicOrder_preserved_of_isHomeoExtension_of_fixes_infty hG hgs hinf hI
      (qcl_r_hloc_of_isKQC hgK hI) (fun i : Fin 4 => ((i : ℕ) : ℝ))
      ⟨0, by simpa only [add_zero] using hx⟩ (fun i => h ((i : ℕ) : ℝ)) (fun i => hGh _)
    exact b4_mono_not_cyclicStrictMono_of_strictAnti (hanti.comp_strictMono hx) hcyc
  -- `|h x| = ‖e(x)‖ → ∞` as `x → ±∞`
  have habs : Tendsto (fun x : ℝ => |h x|) (atTop ⊔ atBot) atTop := by
    have h1 : Tendsto (fun x : ℝ => (x : ℂ)) (atTop ⊔ atBot) (cocompact ℂ) :=
      Complex.isUniformEmbedding_ofReal.isClosedEmbedding.tendsto_cocompact.mono_left
        (sup_le atTop_le_cocompact atBot_le_cocompact)
    refine (tendsto_norm_cocompact_atTop.comp (e.isClosedEmbedding.tendsto_cocompact.comp h1)).congr
      fun x => ?_
    simp only [Function.comp_apply, heh, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨hmono, hcont, ?_, ?_⟩
  · refine tendsto_atTop_mono' atTop ?_
      (tendsto_atTop_add_const_right atTop (-(2 * |h 0|)) (habs.mono_left le_sup_left))
    filter_upwards [eventually_ge_atTop 0] with x hx
    have h0 := hmono.monotone hx
    rcases le_or_gt 0 (h x) with hpos | hneg
    · rw [abs_of_nonneg hpos]
      linarith [abs_nonneg (h 0)]
    · rw [abs_of_neg hneg]
      linarith [neg_abs_le (h 0)]
  · refine tendsto_atBot_mono' atBot ?_ (tendsto_atBot_add_const_right atBot (2 * |h 0|)
      (tendsto_neg_atTop_atBot.comp (habs.mono_left le_sup_right)))
    filter_upwards [eventually_le_atBot 0] with x hx
    have h0 := hmono.monotone hx
    simp only [Function.comp_apply]
    rcases le_or_gt (h x) 0 with hnp | hpos
    · rw [abs_of_nonpos hnp]
      linarith [abs_nonneg (h 0)]
    · rw [abs_of_pos hpos]
      linarith [le_abs_self (h 0)]

/-- `Λ(ρ) > 0` for `ρ > 0`: `Λ(ρ)` is the modulus of the quadrilateral `ℍ(∞, -1, 0, ρ)`. -/
theorem b4_rat_quadLambda_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < quadLambda ρ :=
  modulus_pos ⟨upperHalf, _, isTopQuad_upperHalf_lambda hρ⟩

/-- An affine map `z ↦ α z + β` with `α ≠ 0` is a conformal map of the plane onto itself. -/
theorem b4_rat_affine_conformal {α : ℂ} (β : ℂ) (hα : α ≠ 0) :
    IsConformalOnto (fun z => α * z + β) univ univ := by
  refine ⟨?_, ?_, ?_⟩
  · fun_prop
  · intro z _ w _ hzw
    simpa [hα] using hzw
  · refine eq_univ_of_forall fun w => ⟨(w - β) / α, mem_univ _, ?_⟩
    field_simp
    ring

/-- Pre- and post-composing a `K`-q.c. map `G₀` of the plane onto itself with the affine maps `z ↦ α z + β` and
`w ↦ γ w + δ` (`α, γ ≠ 0`) gives a `K`-q.c. map of the plane onto itself. -/
theorem b4_rat_affine_comp {G₀ : ℂ → ℂ} {K : ℝ} (hG : IsKQC G₀ univ K) (hs : G₀ '' univ = univ)
    {α γ : ℂ} (β δ : ℂ) (hα : α ≠ 0) (hγ : γ ≠ 0) :
    IsKQC (fun z => γ * G₀ (α * z + β) + δ) univ K ∧ (fun z => γ * G₀ (α * z + β) + δ) '' univ = univ := by
  have h₁ := b4_rat_affine_conformal β hα
  have h₂ := b4_rat_affine_conformal δ hγ
  have hc := thm7_1_comp (thm7_1_comp (isKQC_one_of_conformal isOpen_univ h₁) hG (subset_univ _))
    (isKQC_one_of_conformal isOpen_univ h₂) (subset_univ _)
  rw [one_mul, mul_one] at hc
  refine ⟨hc, ?_⟩
  change ((fun w => γ * w + δ) ∘ (G₀ ∘ fun z => α * z + β)) '' univ = univ
  rw [image_comp, image_comp, h₁.2.2, hs, h₂.2.2]

/-- The quasisymmetry bounds (17.5): if `G₀` is a `K`-q.c. map of the plane onto itself equal to the increasing `h` on
`ℝ`, then `1/λ(K) ≤ (h(x+t) - h(x))/(h(x) - h(x-t)) ≤ λ(K)`.  (Normalize `F(z) = (G₀(x + tz) - h(x))/(h(x) - h(x-t))`,
so `F(-1) = -1`, `F(0) = 0`, `F(1) = r`; `b4_three_point_bound` for `F` and `F⁻¹` gives `Λ(1) ≤ K Λ(r)` and
`Λ(r) ≤ K Λ(1)`, then (5.20) and `b4_le_lambdaInv`.) -/
theorem b4_qs_ratio_bounds {h : ℝ → ℝ} {G₀ : ℂ → ℂ} {K : ℝ} (hG : IsKQC G₀ univ K) (hs : G₀ '' univ = univ)
    (hGh : ∀ x : ℝ, G₀ (x : ℂ) = (h x : ℂ)) (hmono : StrictMono h) {x t : ℝ} (ht : 0 < t) :
    (lambdaInv K)⁻¹ ≤ qsRatio h x t ∧ qsRatio h x t ≤ lambdaInv K := by
  have hab : h (x - t) < h x := hmono (by linarith)
  have hbc : h x < h (x + t) := hmono (by linarith)
  have hr : 0 < qsRatio h x t := div_pos (sub_pos.2 hbc) (sub_pos.2 hab)
  have hba : (h x : ℂ) - (h (x - t) : ℂ) ≠ 0 := by
    rw [← ofReal_sub]
    exact ofReal_ne_zero.2 (sub_pos.2 hab).ne'
  -- the normalized map `F(z) = (G₀(x + tz) - h(x))/(h(x) - h(x-t))`: `-1, 0, 1 ↦ -1, 0, r`
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → ℂ, F = fun z => ((h x : ℂ) - (h (x - t) : ℂ))⁻¹ * G₀ ((t : ℂ) * z + (x : ℂ)) +
      -(h x : ℂ) / ((h x : ℂ) - (h (x - t) : ℂ)) := ⟨_, rfl⟩
  obtain ⟨hF, hFs⟩ : IsKQC F univ K ∧ F '' univ = univ := by
    rw [hFdef]
    exact b4_rat_affine_comp hG hs _ _ (ofReal_ne_zero.2 ht.ne') (inv_ne_zero hba)
  have hFm1 : F (-1) = -1 := by
    simp only [hFdef]
    rw [show (t : ℂ) * (-1) + (x : ℂ) = ((x - t : ℝ) : ℂ) by push_cast; ring, hGh]
    field_simp
    ring
  have hF0 : F 0 = 0 := by
    simp only [hFdef]
    rw [show (t : ℂ) * 0 + (x : ℂ) = ((x : ℝ) : ℂ) by ring, hGh]
    field_simp
    ring
  have hF1 : F ((1 : ℝ) : ℂ) = ((qsRatio h x t : ℝ) : ℂ) := by
    simp only [hFdef]
    rw [show (t : ℂ) * ((1 : ℝ) : ℂ) + (x : ℂ) = ((x + t : ℝ) : ℂ) by push_cast; ring, hGh, qsRatio]
    push_cast
    field_simp
    ring
  -- lower bound: `Λ(1) ≤ K Λ(r)`, so `Λ(1/r) ≤ K` by (5.20) and `1/r ≤ λ(K)`
  have hlow := b4_three_point_bound hF hFs one_pos hr hFm1 hF0 hF1
  rw [b4_quadLambda_one] at hlow
  have hpos := b4_rat_quadLambda_pos (one_div_pos.2 hr)
  have hK : quadLambda (1 / qsRatio h x t) ≤ K := by
    calc quadLambda (1 / qsRatio h x t) = quadLambda (1 / qsRatio h x t) * 1 := (mul_one _).symm
      _ ≤ quadLambda (1 / qsRatio h x t) * (K * quadLambda (qsRatio h x t)) :=
          mul_le_mul_of_nonneg_left hlow hpos.le
      _ = K * (quadLambda (qsRatio h x t) * quadLambda (1 / qsRatio h x t)) := by ring
      _ = K := by rw [eq5_20 hr, mul_one]
  have hle := b4_le_lambdaInv (one_div_pos.2 hr) hK
  have hL : 0 < lambdaInv K := (one_div_pos.2 hr).trans_le hle
  rw [one_div] at hle
  -- upper bound: `F⁻¹` is `K`-q.c. with `-1, 0, r ↦ -1, 0, 1`, so `Λ(r) ≤ K Λ(1) = K`
  have hinv : ∀ z, Function.invFunOn F univ (F z) = z :=
    fun z => hF.2.2.1.2.1.leftInvOn_invFunOn (mem_univ z)
  have hG' := thm7_2_inv hF
  rw [hFs] at hG'
  have hGs' : Function.invFunOn F univ '' univ = univ :=
    eq_univ_of_forall fun z => ⟨F z, mem_univ _, hinv z⟩
  have hIm1 := hinv (-1)
  rw [hFm1] at hIm1
  have hI0 := hinv 0
  rw [hF0] at hI0
  have hIr := hinv ((1 : ℝ) : ℂ)
  rw [hF1] at hIr
  have hup := b4_three_point_bound hG' hGs' hr one_pos hIm1 hI0 hIr
  rw [b4_quadLambda_one, mul_one] at hup
  exact ⟨(inv_le_comm₀ hL hr).2 hle, b4_le_lambdaInv hr hup⟩

/-- **Theorem 17.1** (17.5): the boundary values `h` of a `K`-q.c. self-map of `ℍ` fixing `∞`
satisfy `1/λ(K) ≤ (h(x+t) - h(x))/(h(x) - h(x-t)) ≤ λ(K)`, i.e. `h` is `λ(K)`-quasisymmetric. -/
theorem thm17_1_quasisymmetric {h : ℝ → ℝ} {g : ℂ → ℂ} {K : ℝ} (hg : HasQCExtensionH h g K) :
    IsQuasisymmetric h (lambdaInv K) := by
  obtain ⟨hmono, hcont, htop, hbot⟩ := b4_qs_monotone hg
  obtain ⟨G₀, hG₀, hG₀s, hG₀h⟩ := b4_qs_extension hg
  exact ⟨hmono, hcont, htop, hbot, fun x t ht => b4_qs_ratio_bounds hG₀ hG₀s hG₀h hmono ht⟩

/-- The Beurling–Ahlfors extension (17.6) of `h` with parameter `r > 0`:
`u = ½ ∫₀¹ (h(x+ty) + h(x-ty)) dt`, `v = (r/2) ∫₀¹ (h(x+ty) - h(x-ty)) dt`. -/
def beurlingAhlfors (h : ℝ → ℝ) (r : ℝ) (z : ℂ) : ℂ :=
  ((1 / 2 * ∫ t in (0 : ℝ)..1, (h (z.re + t * z.im) + h (z.re - t * z.im)) : ℝ) : ℂ) +
    ((r / 2 * ∫ t in (0 : ℝ)..1, (h (z.re + t * z.im) - h (z.re - t * z.im)) : ℝ) : ℂ) * I

/-! ### Beurling–Ahlfors track (coordinator 553e2d): the homeomorphism step (proved by the scout) -/

/-- (P2) Local injectivity from the inverse function theorem: a map `f : ℂ → ℂ` that is real
`C¹` near `z` with invertible real derivative at `z` (nonzero determinant) is injective on a
neighbourhood of `z`. -/
theorem ba_injOn_of_contDiff {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 1 f z)
    (hJ : LinearMap.det (fderiv ℝ f z : ℂ →ₗ[ℝ] ℂ) ≠ 0) : ∃ U ∈ 𝓝 z, InjOn f U := by
  have hker : LinearMap.ker (fderiv ℝ f z : ℂ →ₗ[ℝ] ℂ) = ⊥ := by
    by_contra hne
    exact hJ (LinearMap.det_eq_zero_iff_ker_ne_bot.2 hne)
  have hrange : LinearMap.range (fderiv ℝ f z : ℂ →ₗ[ℝ] ℂ) = ⊤ :=
    LinearMap.ker_eq_bot_iff_range_eq_top.1 hker
  set e' : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.ofBijective (fderiv ℝ f z) hker hrange with he'
  have hstrict : HasStrictFDerivAt f (e' : ℂ →L[ℝ] ℂ) z := by
    have heq : (e' : ℂ →L[ℝ] ℂ) = fderiv ℝ f z := by
      rw [he']
      exact ContinuousLinearEquiv.coe_ofBijective _ _ _
    rw [heq]
    exact hf.hasStrictFDerivAt one_ne_zero
  refine ⟨(hstrict.toOpenPartialHomeomorph f).source,
    (hstrict.toOpenPartialHomeomorph f).open_source.mem_nhds
      hstrict.mem_toOpenPartialHomeomorph_source, ?_⟩
  have hinj := (hstrict.toOpenPartialHomeomorph f).injOn
  rwa [hstrict.toOpenPartialHomeomorph_coe] at hinj

/-- Abstract homeomorphism criterion on a domain `D ⊆ ℂ` homeomorphic to `ℂ` via `E : ℂ → D`
with inverse `L` (continuous on `D`): a continuous self-map `f` of `D` that is injective near
every point of `D` and proper relative to `D` (every compact `K ⊆ D` has its `f`-preimage in `D`
inside a compact `K' ⊆ D`) is a homeomorphism of `D` onto itself.

Proof: conjugate to `w = L ∘ f ∘ E : ℂ → ℂ`, which is continuous, locally injective and proper,
hence a homeomorphism of `ℂ` by Lemma 12.1; then transfer back. -/
theorem ba_homeomorph_of_conj {f E L : ℂ → ℂ} {D : Set ℂ}
    (hE : Continuous E) (hEmem : ∀ z, E z ∈ D) (hL : ContinuousOn L D)
    (hLE : ∀ z, L (E z) = z) (hEL : ∀ v ∈ D, E (L v) = v)
    (hc : ContinuousOn f D) (hmaps : MapsTo f D D)
    (hloc : ∀ z ∈ D, ∃ U ∈ 𝓝 z, InjOn f U)
    (hprop : ∀ K ⊆ D, IsCompact K → ∃ K' ⊆ D, IsCompact K' ∧ ∀ z ∈ D, f z ∈ K → z ∈ K') :
    IsHomeomorphOnto f D D := by
  set w : ℂ → ℂ := fun z => L (f (E z)) with hw_def
  have hfE : Continuous (fun z => f (E z)) := hc.comp_continuous hE hEmem
  have hwc : Continuous w := hL.comp_continuous hfE (fun z => hmaps (hEmem z))
  have hEw : ∀ z, E (w z) = f (E z) := fun z => hEL _ (hmaps (hEmem z))
  have hwloc : ∀ z₀ : ℂ, ∃ U ∈ 𝓝 z₀, InjOn w U := by
    intro z₀
    obtain ⟨U, hU, hinj⟩ := hloc (E z₀) (hEmem z₀)
    refine ⟨E ⁻¹' U, hE.continuousAt.preimage_mem_nhds hU, ?_⟩
    intro a ha b hb hab
    have h1 : f (E a) = f (E b) := by
      rw [← hEw a, ← hEw b, hab]
    have h2 : E a = E b := hinj ha hb h1
    rw [← hLE a, ← hLE b, h2]
  have hwinf : Tendsto w (cocompact ℂ) (cocompact ℂ) := by
    refine (hasBasis_cocompact.tendsto_iff hasBasis_cocompact).2 fun C hC => ?_
    have hKD : E '' C ⊆ D := by
      rintro _ ⟨z, -, rfl⟩
      exact hEmem z
    obtain ⟨K', hK'D, hK', hK'prop⟩ := hprop (E '' C) hKD (hC.image hE)
    refine ⟨L '' K', hK'.image_of_continuousOn (hL.mono hK'D), fun z hz hwz => hz ?_⟩
    have hfEz : f (E z) ∈ E '' C := ⟨w z, hwz, hEw z⟩
    exact ⟨E z, hK'prop (E z) (hEmem z) hfEz, hLE z⟩
  obtain ⟨e, he⟩ := lemma12_1 hwc hwinf hwloc
  have hfEe : ∀ z, f (E z) = E (e z) := by
    intro z
    rw [he, hEw z]
  have hinj : InjOn f D := by
    intro a ha b hb hab
    have h1 : e (L a) = e (L b) := by
      rw [he]
      show L (f (E (L a))) = L (f (E (L b)))
      rw [hEL a ha, hEL b hb, hab]
    have h2 : L a = L b := e.injective h1
    rw [← hEL a ha, ← hEL b hb, h2]
  set G : ℂ → ℂ := fun v => E (e.symm (L v)) with hG_def
  have hGmem : ∀ v, G v ∈ D := fun v => hEmem _
  have hfG : ∀ v ∈ D, f (G v) = v := by
    intro v hv
    simp only [hG_def]
    rw [hfEe, e.apply_symm_apply, hEL v hv]
  have hsurj : f '' D = D :=
    Subset.antisymm hmaps.image_subset fun v hv => ⟨G v, hGmem v, hfG v hv⟩
  have hGc : ContinuousOn G D :=
    hE.comp_continuousOn (e.symm.continuous.comp_continuousOn hL)
  refine ⟨hc, hinj, hsurj, hGc.congr fun v hv => ?_⟩
  have h := hinj.leftInvOn_invFunOn (hGmem v)
  rw [hfG v hv] at h
  exact h

/-- The map `E z = Re z + e^{Im z} i` sends `ℂ` into the upper half-plane `ℍ`. -/
theorem ba_expIm_mem_upperHalf (z : ℂ) :
    ((z.re : ℂ) + (Real.exp z.im : ℂ) * I) ∈ upperHalf := by
  show 0 < ((z.re : ℂ) + (Real.exp z.im : ℂ) * I).im
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add]
  exact Real.exp_pos _

/-- (P1) Abstract homeomorphism criterion on `ℍ`: a continuous self-map of the upper half-plane
that is injective near every point and proper relative to `ℍ` (preimages of compact subsets of
`ℍ` lie in compact subsets of `ℍ`) is a homeomorphism of `ℍ` onto itself.

Proof: conjugate by the homeomorphism `E z = Re z + e^{Im z} i` of `ℂ` onto `ℍ` (inverse
`L w = Re w + (log Im w) i`) and apply `ba_homeomorph_of_conj` (i.e. Lemma 12.1). -/
theorem ba_homeomorph_upperHalf {f : ℂ → ℂ} (hc : ContinuousOn f upperHalf)
    (hmaps : MapsTo f upperHalf upperHalf)
    (hloc : ∀ z ∈ upperHalf, ∃ U ∈ 𝓝 z, InjOn f U)
    (hprop : ∀ K ⊆ upperHalf, IsCompact K → ∃ K' ⊆ upperHalf, IsCompact K' ∧
      ∀ z ∈ upperHalf, f z ∈ K → z ∈ K') :
    IsHomeomorphOnto f upperHalf upperHalf := by
  refine ba_homeomorph_of_conj (E := fun z => (z.re : ℂ) + (Real.exp z.im : ℂ) * I)
    (L := fun v => (v.re : ℂ) + (Real.log v.im : ℂ) * I) ?_ ba_expIm_mem_upperHalf ?_ ?_ ?_
    hc hmaps hloc hprop
  · exact (continuous_ofReal.comp continuous_re).add
      ((continuous_ofReal.comp (Real.continuous_exp.comp continuous_im)).mul continuous_const)
  · refine (continuous_ofReal.comp continuous_re).continuousOn.add
      ((continuous_ofReal.comp_continuousOn
        (continuous_im.continuousOn.log fun v hv => ?_)).mul continuousOn_const)
    exact (show (0 : ℝ) < v.im from hv).ne'
  · intro z
    apply Complex.ext <;> simp [Complex.exp_ofReal_re]
  · intro v hv
    have hv' : (0 : ℝ) < v.im := hv
    apply Complex.ext <;> simp [Real.exp_log hv']

/-- Properness relative to `ℍ` from boundary behaviour: if `f(z) → ∞` as `z → ∞` within `ℍ`
and `Im f(z) → 0` as `z` tends within `ℍ` to any real point, then every compact `K ⊆ ℍ` has its
`f`-preimage in `ℍ` inside a compact `K' ⊆ ℍ` (namely the closure of that preimage). -/
theorem ba_proper_upperHalf_of_tendsto {f : ℂ → ℂ}
    (hinf : Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ))
    (hbdry : ∀ x : ℝ, Tendsto (fun z => (f z).im) (𝓝[upperHalf] (x : ℂ)) (𝓝 0)) :
    ∀ K ⊆ upperHalf, IsCompact K → ∃ K' ⊆ upperHalf, IsCompact K' ∧
      ∀ z ∈ upperHalf, f z ∈ K → z ∈ K' := by
  intro K hKH hK
  set A : Set ℂ := {z | z ∈ upperHalf ∧ f z ∈ K} with hA
  obtain ⟨C, hC, hAC⟩ : ∃ C, IsCompact C ∧ A ⊆ C := by
    have h1 : f ⁻¹' Kᶜ ∈ cocompact ℂ ⊓ 𝓟 upperHalf := hinf hK.compl_mem_cocompact
    rw [mem_inf_principal] at h1
    obtain ⟨C, hC, hCsub⟩ := mem_cocompact.1 h1
    refine ⟨C, hC, fun z hz => ?_⟩
    by_contra hzC
    exact hCsub hzC hz.1 hz.2
  refine ⟨closure A, ?_, hC.of_isClosed_subset isClosed_closure
    (closure_minimal hAC hC.isClosed), fun z hz hfz => subset_closure ⟨hz, hfz⟩⟩
  intro z hz
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · have hAe : A = ∅ := by
      ext a
      simp [hA, hKe]
    rw [hAe, closure_empty] at hz
    exact hz.elim
  obtain ⟨k₀, hk₀K, hk₀min⟩ := hK.exists_isMinOn hKne continuous_im.continuousOn
  have hδ : (0 : ℝ) < k₀.im := hKH hk₀K
  have hz0 : 0 ≤ z.im := by
    have hcl : closure A ⊆ {w : ℂ | 0 ≤ w.im} :=
      closure_minimal (fun w hw => le_of_lt (show (0 : ℝ) < w.im from hw.1))
        (isClosed_le continuous_const continuous_im)
    exact hcl hz
  rcases hz0.lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    have hzre : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [← hzero]
    have hev : ∀ᶠ w in 𝓝[upperHalf] z, (f w).im < k₀.im := by
      rw [hzre]
      exact (hbdry z.re).eventually (gt_mem_nhds hδ)
    have hne : (𝓝[A] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hz
    have hle : 𝓝[A] z ≤ 𝓝[upperHalf] z := nhdsWithin_mono z (fun a ha => by exact ha.1)
    have hevA : ∀ᶠ w in 𝓝[A] z, (f w).im < k₀.im := hle hev
    have hA' : ∀ᶠ w in 𝓝[A] z, w ∈ A := self_mem_nhdsWithin
    obtain ⟨w, hw1, hw2⟩ := (hevA.and hA').exists
    have hmin : k₀.im ≤ (f w).im := isMinOn_iff.1 hk₀min (f w) hw2.2
    linarith

/-- Homeomorphism criterion on `ℍ` in boundary form: a continuous, locally injective self-map
of `ℍ` with `f(z) → ∞` as `z → ∞` within `ℍ` and `Im f(z) → 0` at every real boundary point is
a homeomorphism of `ℍ` onto itself. -/
theorem ba_homeomorph_upperHalf_of_tendsto {f : ℂ → ℂ} (hc : ContinuousOn f upperHalf)
    (hmaps : MapsTo f upperHalf upperHalf)
    (hloc : ∀ z ∈ upperHalf, ∃ U ∈ 𝓝 z, InjOn f U)
    (hinf : Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ))
    (hbdry : ∀ x : ℝ, Tendsto (fun z => (f z).im) (𝓝[upperHalf] (x : ℂ)) (𝓝 0)) :
    IsHomeomorphOnto f upperHalf upperHalf :=
  ba_homeomorph_upperHalf hc hmaps hloc (ba_proper_upperHalf_of_tendsto hinf hbdry)

/-- Homeomorphism criterion on `ℍ` in the shape of the Beurling–Ahlfors step: a real-`C¹` self-map
of `ℍ` with positive Jacobian, `f(z) → ∞` as `z → ∞` within `ℍ`, and `Im f(z) → 0` at every real
boundary point is a homeomorphism of `ℍ` onto itself. -/
theorem ba_homeomorph_upperHalf_of_contDiff {f : ℂ → ℂ} (hf : ContDiffOn ℝ 1 f upperHalf)
    (hJ : ∀ z ∈ upperHalf, 0 < jacobian f z)
    (hmaps : MapsTo f upperHalf upperHalf)
    (hinf : Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ))
    (hbdry : ∀ x : ℝ, Tendsto (fun z => (f z).im) (𝓝[upperHalf] (x : ℂ)) (𝓝 0)) :
    IsHomeomorphOnto f upperHalf upperHalf := by
  have hopen : IsOpen upperHalf := isOpen_lt continuous_const continuous_im
  refine ba_homeomorph_upperHalf_of_tendsto hf.continuousOn hmaps (fun z hz => ?_) hinf hbdry
  have hfz : ContDiffAt ℝ 1 f z := hf.contDiffAt (hopen.mem_nhds hz)
  refine ba_injOn_of_contDiff hfz ?_
  rw [det_fderiv_eq_jacobian (hfz.differentiableAt one_ne_zero)]
  exact (hJ z hz).ne'

/-- Schwarz reflection as a homeomorphism of `ℂ`: let `f` be continuous on the closed upper
half-plane, map `ℍ` injectively into `ℍ`, take real values on `ℝ` with `x ↦ f x` injective
there, and tend to `∞` at `∞` within the closed half-plane.  Then the reflected map
`F z = f z` (`Im z ≥ 0`), `F z = conj (f (conj z))` (`Im z < 0`) is a homeomorphism of `ℂ`
(it is continuous, injective and proper, so Lemma 12.1 applies). -/
theorem ba_reflect_homeomorph {f : ℂ → ℂ}
    (hc : ContinuousOn f {z | 0 ≤ z.im})
    (hmaps : MapsTo f upperHalf upperHalf)
    (hinj : InjOn f upperHalf)
    (hreal : ∀ x : ℝ, (f x).im = 0)
    (hinjR : Function.Injective (fun x : ℝ => (f x).re))
    (hinf : Tendsto f (cocompact ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (cocompact ℂ)) :
    ∃ e : ℂ ≃ₜ ℂ, ∀ z : ℂ, e z = if (0 : ℝ) ≤ z.im then f z
      else starRingEnd ℂ (f (starRingEnd ℂ z)) := by
  set F : ℂ → ℂ := fun z => if (0 : ℝ) ≤ z.im then f z
    else starRingEnd ℂ (f (starRingEnd ℂ z)) with hF_def
  have hconjH : ∀ z : ℂ, z.im < 0 → starRingEnd ℂ z ∈ upperHalf := by
    intro z hz
    show 0 < (starRingEnd ℂ z).im
    rw [conj_im]
    linarith
  have hreal' : ∀ z : ℂ, z.im = 0 → (f z).im = 0 := by
    intro z hz
    have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz])
    rw [hz']
    exact hreal _
  -- continuity
  have hFc : Continuous F := by
    refine continuous_if_le continuous_const continuous_im hc ?_ ?_
    · refine continuous_conj.comp_continuousOn (hc.comp continuous_conj.continuousOn ?_)
      intro z hz
      show 0 ≤ (starRingEnd ℂ z).im
      rw [conj_im]
      linarith [show z.im ≤ 0 from hz]
    · intro z hz
      have hz0 : z.im = 0 := hz.symm
      have hz' : starRingEnd ℂ z = z := conj_eq_iff_im.2 hz0
      rw [hz']
      exact (conj_eq_iff_im.2 (hreal' z hz0)).symm
  -- the sign of `Im F z` is the sign of `Im z`
  have hFpos : ∀ z : ℂ, 0 < z.im → F z = f z ∧ 0 < (F z).im := by
    intro z hz
    have hFz : F z = f z := ite_eq_left hz.le
    exact ⟨hFz, hFz ▸ hmaps hz⟩
  have hFzero : ∀ z : ℂ, z.im = 0 → F z = f z ∧ (F z).im = 0 := by
    intro z hz
    have hFz : F z = f z := ite_eq_left hz.ge
    exact ⟨hFz, hFz ▸ hreal' z hz⟩
  have hFneg : ∀ z : ℂ, z.im < 0 →
      F z = starRingEnd ℂ (f (starRingEnd ℂ z)) ∧ (F z).im < 0 := by
    intro z hz
    have hFz : F z = starRingEnd ℂ (f (starRingEnd ℂ z)) := ite_eq_right (not_le.2 hz)
    refine ⟨hFz, ?_⟩
    rw [hFz, conj_im]
    have := hmaps (hconjH z hz)
    have h' : (0 : ℝ) < (f (starRingEnd ℂ z)).im := this
    linarith
  -- injectivity
  have hFinj : Function.Injective F := by
    intro a b hab
    rcases lt_trichotomy a.im 0 with ha | ha | ha
    · -- `Im a < 0`
      have hb : b.im < 0 := by
        rcases lt_trichotomy b.im 0 with hb | hb | hb
        · exact hb
        · have h1 := (hFneg a ha).2
          rw [hab, (hFzero b hb).2] at h1
          exact absurd h1 (lt_irrefl 0)
        · have h1 := (hFneg a ha).2
          rw [hab] at h1
          exact absurd (hFpos b hb).2 (not_lt.2 h1.le)
      have h1 : starRingEnd ℂ (f (starRingEnd ℂ a)) = starRingEnd ℂ (f (starRingEnd ℂ b)) := by
        rw [← (hFneg a ha).1, ← (hFneg b hb).1, hab]
      have h2 : f (starRingEnd ℂ a) = f (starRingEnd ℂ b) := by
        have := congrArg (starRingEnd ℂ) h1
        simpa using this
      have h3 : starRingEnd ℂ a = starRingEnd ℂ b := hinj (hconjH a ha) (hconjH b hb) h2
      have := congrArg (starRingEnd ℂ) h3
      simpa using this
    · -- `Im a = 0`
      have hb : b.im = 0 := by
        rcases lt_trichotomy b.im 0 with hb | hb | hb
        · have h1 := (hFneg b hb).2
          rw [← hab, (hFzero a ha).2] at h1
          exact absurd h1 (lt_irrefl 0)
        · exact hb
        · have h1 := (hFpos b hb).2
          rw [← hab, (hFzero a ha).2] at h1
          exact absurd h1 (lt_irrefl 0)
      have h1 : f a = f b := by
        rw [← (hFzero a ha).1, ← (hFzero b hb).1, hab]
      have ha' : a = (a.re : ℂ) := Complex.ext (by simp) (by simp [ha])
      have hb' : b = (b.re : ℂ) := Complex.ext (by simp) (by simp [hb])
      have h2 : a.re = b.re := by
        apply hinjR
        show (f (a.re : ℂ)).re = (f (b.re : ℂ)).re
        rw [← ha', ← hb', h1]
      rw [ha', hb', h2]
    · -- `Im a > 0`
      have hb : 0 < b.im := by
        rcases lt_trichotomy b.im 0 with hb | hb | hb
        · have h1 := (hFneg b hb).2
          rw [← hab] at h1
          exact absurd (hFpos a ha).2 (not_lt.2 h1.le)
        · have h1 := (hFpos a ha).2
          rw [hab, (hFzero b hb).2] at h1
          exact absurd h1 (lt_irrefl 0)
        · exact hb
      have h1 : f a = f b := by
        rw [← (hFpos a ha).1, ← (hFpos b hb).1, hab]
      exact hinj ha hb h1
  -- properness
  set φ : ℂ → ℂ := fun z => if (0 : ℝ) ≤ z.im then z else starRingEnd ℂ z with hφ_def
  have hφ : Tendsto φ (cocompact ℂ) (cocompact ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) := by
    refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (Eventually.of_forall fun z => ?_)⟩
    · rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      have hnorm : (fun z => ‖φ z‖) = fun z => ‖z‖ := by
        funext z
        simp only [hφ_def]
        split_ifs
        · rfl
        · exact Complex.norm_conj z
      rw [hnorm]
      exact tendsto_norm_cobounded_atTop
    · show 0 ≤ (φ z).im
      simp only [hφ_def]
      split_ifs with h
      · exact h
      · rw [conj_im]
        linarith [not_le.1 h]
  have hFinf : Tendsto F (cocompact ℂ) (cocompact ℂ) := by
    have h1 := hinf.comp hφ
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded] at h1 ⊢
    have hnorm : (fun z => ‖F z‖) = fun z => ‖(f ∘ φ) z‖ := by
      funext z
      simp only [hF_def, hφ_def, Function.comp]
      split_ifs
      · rfl
      · exact Complex.norm_conj _
    rw [hnorm]
    exact h1
  obtain ⟨e, he⟩ := lemma12_1 hFc hFinf (fun _ => ⟨univ, univ_mem, hFinj.injOn⟩)
  exact ⟨e, fun z => by rw [he]⟩

/-- Reflection extension (abstract form of the boundary step of the Beurling–Ahlfors track): under
the hypotheses of `ba_reflect_homeomorph`, the one-point extension `Ĝ` of the reflected homeomorphism
is a homeomorphic extension of `f : ℍ → f(ℍ)` to `ℂ̄`, with `Ĝ ∞ = ∞` and `Ĝ x = f x` on `ℝ`. -/
theorem ba_isHomeoExtension_of_reflect {f : ℂ → ℂ}
    (hc : ContinuousOn f {z | 0 ≤ z.im})
    (hmaps : MapsTo f upperHalf upperHalf)
    (hinj : InjOn f upperHalf)
    (hreal : ∀ x : ℝ, (f x).im = 0)
    (hinjR : Function.Injective (fun x : ℝ => (f x).re))
    (hinf : Tendsto f (cocompact ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (cocompact ℂ)) :
    ∃ G : ExtPlane → ExtPlane, IsHomeoExtension f upperHalf (f '' upperHalf) G ∧
      G extInf = extInf ∧ ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = ((f x : ℂ) : ExtPlane) := by
  obtain ⟨e, he⟩ := ba_reflect_homeomorph hc hmaps hinj hreal hinjR hinf
  have heq : EqOn (⇑e) f upperHalf := by
    intro z hz
    rw [he z]
    exact ite_eq_left (le_of_lt (show (0 : ℝ) < z.im from hz))
  refine ⟨e.onePointCongr, ?_, rfl, fun x => ?_⟩
  · have h := s13x_de_isHomeoExtension_homeomorph e upperHalf
    rw [heq.image_eq] at h
    exact s13x_de_isHomeoExtension_congr h heq
  · show ((e x : ℂ) : ExtPlane) = ((f x : ℂ) : ExtPlane)
    rw [he (x : ℂ), ite_eq_left (by simp)]

/-- Boundary behaviour from continuity: if `f` is continuous within `ℍ` at every real point and
real on `ℝ`, then `Im f(z) → 0` as `z` tends within `ℍ` to any real point. -/
theorem ba_bdry_of_continuousWithinAt {f : ℂ → ℂ}
    (hcont : ∀ x : ℝ, ContinuousWithinAt f upperHalf (x : ℂ)) (hreal : ∀ x : ℝ, (f x).im = 0) :
    ∀ x : ℝ, Tendsto (fun z => (f z).im) (𝓝[upperHalf] (x : ℂ)) (𝓝 0) := by
  intro x
  have h := (continuous_im.continuousAt (x := f x)).tendsto.comp (hcont x)
  rw [hreal x] at h
  exact h

/-- The homeomorphism step of the Beurling–Ahlfors track, packaged: a real-`C¹` self-map `f` of `ℍ`
with positive Jacobian, continuous on the closed half-plane, equal on `ℝ` to a strictly increasing
`h`, and tending to `∞` at `∞` within the closed half-plane, maps `ℍ` onto `ℍ` and has a homeomorphic
extension `G` to `ℂ̄` with `G ∞ = ∞` and `G x = h x` on `ℝ` (the non-q.c. part of
`HasQCExtensionH h f K`). -/
theorem ba_homeo_package {f : ℂ → ℂ} {h : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f upperHalf) (hJ : ∀ z ∈ upperHalf, 0 < jacobian f z)
    (hc : ContinuousOn f {z | 0 ≤ z.im}) (hmaps : MapsTo f upperHalf upperHalf)
    (hbd : ∀ x : ℝ, f x = h x) (hh : StrictMono h)
    (hinf : Tendsto f (cocompact ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (cocompact ℂ)) :
    f '' upperHalf = upperHalf ∧ ∃ G : ExtPlane → ExtPlane,
      IsHomeoExtension f upperHalf upperHalf G ∧ G extInf = extInf ∧
        ∀ x : ℝ, G ((x : ℂ) : ExtPlane) = (((h x : ℝ) : ℂ) : ExtPlane) := by
  have hreal : ∀ x : ℝ, (f x).im = 0 := fun x => by
    rw [hbd x]
    simp
  have hHsub : upperHalf ⊆ {z : ℂ | 0 ≤ z.im} := fun z hz =>
    le_of_lt (show (0 : ℝ) < z.im from hz)
  have hbdry := ba_bdry_of_continuousWithinAt
    (fun x => (hc (x : ℂ) (by simp)).mono hHsub) hreal
  have hinf' : Tendsto f (cocompact ℂ ⊓ 𝓟 upperHalf) (cocompact ℂ) :=
    hinf.mono_left (inf_le_inf_left _ (principal_mono.2 hHsub))
  obtain ⟨-, hinj, himg, -⟩ := ba_homeomorph_upperHalf_of_contDiff hf hJ hmaps hinf' hbdry
  have hinjR : Function.Injective (fun x : ℝ => (f x).re) := by
    intro a b hab
    have hab' : h a = h b := by simpa [hbd] using hab
    exact hh.injective hab'
  obtain ⟨G, hG, hGinf, hGx⟩ := ba_isHomeoExtension_of_reflect hc hmaps hinj hreal hinjR hinf
  rw [himg] at hG
  refine ⟨himg, G, hG, hGinf, fun x => ?_⟩
  rw [hGx x, hbd x]

/-! ### Beurling–Ahlfors track interface (coordinator 553e2d): the formula, the dilatation, properness, and the
quasi-isometry bound for the extension `f = beurlingAhlfors h 1` -/

/-- The primitive `H(s) = ∫₀ˢ h` of `h`, used for the closed form of the Beurling–Ahlfors extension. -/
def ba_f1h_prim (h : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, h t

/-- `H' = h` for continuous `h` (fundamental theorem of calculus). -/
theorem ba_f1h_prim_hasDerivAt {h : ℝ → ℝ} (hcont : Continuous h) (s : ℝ) :
    HasDerivAt (ba_f1h_prim h) (h s) s :=
  (hcont.integral_hasStrictDerivAt 0 s).hasDerivAt

/-- `H` is `C¹` for continuous `h`. -/
theorem ba_f1h_prim_contDiff {h : ℝ → ℝ} (hcont : Continuous h) : ContDiff ℝ 1 (ba_f1h_prim h) := by
  rw [contDiff_one_iff_deriv]
  have hd : deriv (ba_f1h_prim h) = h := funext fun s => (ba_f1h_prim_hasDerivAt hcont s).deriv
  rw [hd]
  exact ⟨fun s => (ba_f1h_prim_hasDerivAt hcont s).differentiableAt, hcont⟩

/-- `H(b) - H(a) = ∫ₐᵇ h`. -/
theorem ba_f1h_prim_sub {h : ℝ → ℝ} (hcont : Continuous h) (a b : ℝ) :
    ba_f1h_prim h b - ba_f1h_prim h a = ∫ t in a..b, h t :=
  intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable 0 b) (hcont.intervalIntegrable 0 a)

/-- `∫₀¹ h(x + t y) dt = (H(x+y) - H(x))/y` for `y ≠ 0`. -/
theorem ba_f1h_int_plus {h : ℝ → ℝ} (hcont : Continuous h) (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ∫ t in (0 : ℝ)..1, h (x + t * y) = (ba_f1h_prim h (x + y) - ba_f1h_prim h x) / y := by
  have hfun : (fun t : ℝ => h (x + t * y)) = fun t : ℝ => h (x + y * t) := by
    funext t
    rw [mul_comm]
  rw [hfun, intervalIntegral.integral_comp_add_mul h hy x, ba_f1h_prim_sub hcont, mul_zero, add_zero, mul_one,
    smul_eq_mul, inv_mul_eq_div]

/-- `∫₀¹ h(x - t y) dt = (H(x) - H(x-y))/y` for `y ≠ 0`. -/
theorem ba_f1h_int_minus {h : ℝ → ℝ} (hcont : Continuous h) (x : ℝ) {y : ℝ} (hy : y ≠ 0) :
    ∫ t in (0 : ℝ)..1, h (x - t * y) = (ba_f1h_prim h x - ba_f1h_prim h (x - y)) / y := by
  have hfun : (fun t : ℝ => h (x - t * y)) = fun t : ℝ => h (x - y * t) := by
    funext t
    rw [mul_comm]
  rw [hfun, intervalIntegral.integral_comp_sub_mul h hy x, ba_f1h_prim_sub hcont, mul_zero, sub_zero, mul_one,
    smul_eq_mul, inv_mul_eq_div]

/-- The closed form of the Beurling–Ahlfors extension (`r = 1`) off the real axis:
`u = (H(x+y) - H(x-y))/2y`, `v = (H(x+y) - 2H(x) + H(x-y))/2y` with `H = ∫₀ h`. -/
def ba_f1h_closed (h : ℝ → ℝ) (z : ℂ) : ℂ :=
  (((ba_f1h_prim h (z.re + z.im) - ba_f1h_prim h (z.re - z.im)) / (2 * z.im) : ℝ) : ℂ) +
    (((ba_f1h_prim h (z.re + z.im) - 2 * ba_f1h_prim h z.re + ba_f1h_prim h (z.re - z.im)) / (2 * z.im) : ℝ) : ℂ) *
      I

/-- Off the real axis the Beurling–Ahlfors extension (`r = 1`) equals its closed form. -/
theorem ba_f1h_eq_closed {h : ℝ → ℝ} (hcont : Continuous h) {z : ℂ} (hz : z.im ≠ 0) :
    beurlingAhlfors h 1 z = ba_f1h_closed h z := by
  have hi1 : IntervalIntegrable (fun t : ℝ => h (z.re + t * z.im)) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => h (z.re + t * z.im)).intervalIntegrable 0 1
  have hi2 : IntervalIntegrable (fun t : ℝ => h (z.re - t * z.im)) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => h (z.re - t * z.im)).intervalIntegrable 0 1
  have e1 : 1 / 2 * ((ba_f1h_prim h (z.re + z.im) - ba_f1h_prim h z.re) / z.im +
      (ba_f1h_prim h z.re - ba_f1h_prim h (z.re - z.im)) / z.im) =
      (ba_f1h_prim h (z.re + z.im) - ba_f1h_prim h (z.re - z.im)) / (2 * z.im) := by
    field_simp
    ring
  have e2 : 1 / 2 * ((ba_f1h_prim h (z.re + z.im) - ba_f1h_prim h z.re) / z.im -
      (ba_f1h_prim h z.re - ba_f1h_prim h (z.re - z.im)) / z.im) =
      (ba_f1h_prim h (z.re + z.im) - 2 * ba_f1h_prim h z.re + ba_f1h_prim h (z.re - z.im)) / (2 * z.im) := by
    field_simp
    ring
  rw [beurlingAhlfors, ba_f1h_closed, intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_sub hi1 hi2,
    ba_f1h_int_plus hcont _ hz, ba_f1h_int_minus hcont _ hz, e1, e2]

/-- The closed form is `C¹` on `ℍ`. -/
theorem ba_f1h_closed_contDiffOn {h : ℝ → ℝ} (hcont : Continuous h) :
    ContDiffOn ℝ 1 (ba_f1h_closed h) upperHalf := by
  have hP := ba_f1h_prim_contDiff hcont
  have hre : ContDiff ℝ 1 (fun z : ℂ => z.re) := reCLM.contDiff
  have him : ContDiff ℝ 1 (fun z : ℂ => z.im) := imCLM.contDiff
  have hof : ContDiff ℝ 1 (fun r : ℝ => (r : ℂ)) := ofRealCLM.contDiff
  have hne : ∀ z ∈ upperHalf, (fun z : ℂ => 2 * z.im) z ≠ 0 := fun z hz =>
    mul_ne_zero two_ne_zero (show (0 : ℝ) < z.im from hz).ne'
  have hden : ContDiffOn ℝ 1 (fun z : ℂ => 2 * z.im) upperHalf := (contDiff_const.mul him).contDiffOn
  have hU : ContDiffOn ℝ 1 (fun z : ℂ =>
      (ba_f1h_prim h (z.re + z.im) - ba_f1h_prim h (z.re - z.im)) / (2 * z.im)) upperHalf :=
    ContDiffOn.div ((hP.comp (hre.add him)).sub (hP.comp (hre.sub him))).contDiffOn hden hne
  have hV : ContDiffOn ℝ 1 (fun z : ℂ =>
      (ba_f1h_prim h (z.re + z.im) - 2 * ba_f1h_prim h z.re + ba_f1h_prim h (z.re - z.im)) / (2 * z.im))
      upperHalf :=
    ContDiffOn.div (((hP.comp (hre.add him)).sub (contDiff_const.mul (hP.comp hre))).add
      (hP.comp (hre.sub him))).contDiffOn hden hne
  exact (hof.comp_contDiffOn hU).add ((hof.comp_contDiffOn hV).mul contDiffOn_const)

/-- The Beurling–Ahlfors extension of a continuous `h` is continuous on `ℂ`. -/
theorem ba_f1h_continuous {h : ℝ → ℝ} (hcont : Continuous h) (r : ℝ) : Continuous (beurlingAhlfors h r) := by
  have h1 : Continuous fun z : ℂ => ∫ t in (0 : ℝ)..1, (h (z.re + t * z.im) + h (z.re - t * z.im)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (show Continuous fun p : ℂ × ℝ => h (p.1.re + p.2 * p.1.im) + h (p.1.re - p.2 * p.1.im) by fun_prop) 0 1
  have h2 : Continuous fun z : ℂ => ∫ t in (0 : ℝ)..1, (h (z.re + t * z.im) - h (z.re - t * z.im)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (show Continuous fun p : ℂ × ℝ => h (p.1.re + p.2 * p.1.im) - h (p.1.re - p.2 * p.1.im) by fun_prop) 0 1
  unfold beurlingAhlfors
  fun_prop

/-- The Beurling–Ahlfors extension (`r = 1`) of a continuous `h` is `C¹` on `ℍ`. -/
theorem ba_f1h_contDiffOn {h : ℝ → ℝ} (hcont : Continuous h) :
    ContDiffOn ℝ 1 (beurlingAhlfors h 1) upperHalf :=
  (ba_f1h_closed_contDiffOn hcont).congr fun _ hz => ba_f1h_eq_closed hcont (show (0 : ℝ) < _ from hz).ne'

/-- On `ℝ` the Beurling–Ahlfors extension equals `h`. -/
theorem ba_f1h_real (h : ℝ → ℝ) (x : ℝ) : beurlingAhlfors h 1 x = h x := by
  simp [beurlingAhlfors]
  ring

/-- The chain rule for `H`: `(H ∘ g)' = h(g) g'`. -/
theorem ba_f1h_prim_comp {h : ℝ → ℝ} (hcont : Continuous h) {g : ℝ → ℝ} {g' x : ℝ} (hg : HasDerivAt g g' x) :
    HasDerivAt (fun t => ba_f1h_prim h (g t)) (h (g x) * g') x :=
  (ba_f1h_prim_hasDerivAt hcont (g x)).comp x hg

/-- The derivative of the closed form along the horizontal line through `z`. -/
theorem ba_f1h_closed_line_re {h : ℝ → ℝ} (hcont : Continuous h) (z : ℂ) :
    HasDerivAt (fun t : ℝ => ba_f1h_closed h (z + t))
      ((((h (z.re + z.im) - h (z.re - z.im)) / (2 * z.im) : ℝ) : ℂ) +
        (((h (z.re + z.im) - 2 * h z.re + h (z.re - z.im)) / (2 * z.im) : ℝ) : ℂ) * I) 0 := by
  have hA : HasDerivAt (fun t : ℝ => ba_f1h_prim h (z.re + t + z.im)) (h (z.re + z.im)) 0 :=
    (ba_f1h_prim_comp hcont (((hasDerivAt_id' (x := (0 : ℝ))).const_add z.re).add_const z.im)).congr_deriv
      (by simp)
  have hB : HasDerivAt (fun t : ℝ => ba_f1h_prim h (z.re + t - z.im)) (h (z.re - z.im)) 0 :=
    (ba_f1h_prim_comp hcont (((hasDerivAt_id' (x := (0 : ℝ))).const_add z.re).sub_const z.im)).congr_deriv
      (by simp)
  have hC : HasDerivAt (fun t : ℝ => ba_f1h_prim h (z.re + t)) (h z.re) 0 :=
    (ba_f1h_prim_comp hcont ((hasDerivAt_id' (x := (0 : ℝ))).const_add z.re)).congr_deriv (by simp)
  have hU := ((hA.sub hB).div_const (2 * z.im)).ofReal_comp
  have hV := ((((hA.sub (hC.const_mul 2)).add hB).div_const (2 * z.im)).ofReal_comp).mul_const I
  have hfun : (fun t : ℝ => ba_f1h_closed h (z + t)) = fun t : ℝ =>
      (((ba_f1h_prim h (z.re + t + z.im) - ba_f1h_prim h (z.re + t - z.im)) / (2 * z.im) : ℝ) : ℂ) +
      (((ba_f1h_prim h (z.re + t + z.im) - 2 * ba_f1h_prim h (z.re + t) + ba_f1h_prim h (z.re + t - z.im)) /
        (2 * z.im) : ℝ) : ℂ) * I := by
    funext t
    simp only [ba_f1h_closed, add_re, ofReal_re, add_im, ofReal_im, add_zero]
  rw [hfun]
  exact hU.add hV

/-- The derivative of the closed form along the vertical line through `z` (`Im z ≠ 0`). -/
theorem ba_f1h_closed_line_im {h : ℝ → ℝ} (hcont : Continuous h) {z : ℂ} (hz : z.im ≠ 0) :
    HasDerivAt (fun t : ℝ => ba_f1h_closed h (z + t * I))
      ((((h (z.re + z.im) + h (z.re - z.im)) / (2 * z.im) -
            (∫ t in (z.re - z.im)..(z.re + z.im), h t) / (2 * z.im ^ 2) : ℝ) : ℂ) +
          (((h (z.re + z.im) - h (z.re - z.im)) / (2 * z.im) -
            ((∫ t in z.re..(z.re + z.im), h t) - ∫ t in (z.re - z.im)..z.re, h t) / (2 * z.im ^ 2) : ℝ) : ℂ) *
            I) 0 := by
  have hA : HasDerivAt (fun t : ℝ => ba_f1h_prim h (z.re + (z.im + t))) (h (z.re + z.im)) 0 :=
    (ba_f1h_prim_comp hcont (((hasDerivAt_id' (x := (0 : ℝ))).const_add z.im).const_add z.re)).congr_deriv
      (by simp)
  have hB : HasDerivAt (fun t : ℝ => ba_f1h_prim h (z.re - (z.im + t))) (-h (z.re - z.im)) 0 :=
    (ba_f1h_prim_comp hcont (((hasDerivAt_id' (x := (0 : ℝ))).const_add z.im).const_sub z.re)).congr_deriv
      (by simp)
  have hD : HasDerivAt (fun t : ℝ => 2 * (z.im + t)) 2 0 :=
    (((hasDerivAt_id' (x := (0 : ℝ))).const_add z.im).const_mul (2 : ℝ)).congr_deriv (mul_one _)
  have hden : 2 * (z.im + 0) ≠ 0 := by
    rw [add_zero]
    exact mul_ne_zero two_ne_zero hz
  have hNU : HasDerivAt (fun t : ℝ => ba_f1h_prim h (z.re + (z.im + t)) - ba_f1h_prim h (z.re - (z.im + t)))
      (h (z.re + z.im) + h (z.re - z.im)) 0 :=
    (hA.sub hB).congr_deriv (by ring)
  have hNV : HasDerivAt (fun t : ℝ => ba_f1h_prim h (z.re + (z.im + t)) - 2 * ba_f1h_prim h z.re +
      ba_f1h_prim h (z.re - (z.im + t))) (h (z.re + z.im) - h (z.re - z.im)) 0 :=
    ((hA.sub (hasDerivAt_const (0 : ℝ) (2 * ba_f1h_prim h z.re))).add hB).congr_deriv (by ring)
  have hU : HasDerivAt (fun t : ℝ => (ba_f1h_prim h (z.re + (z.im + t)) - ba_f1h_prim h (z.re - (z.im + t))) /
      (2 * (z.im + t)))
      ((h (z.re + z.im) + h (z.re - z.im)) / (2 * z.im) -
        (∫ t in (z.re - z.im)..(z.re + z.im), h t) / (2 * z.im ^ 2)) 0 := by
    refine (hNU.fun_div hD hden).congr_deriv ?_
    rw [← ba_f1h_prim_sub hcont]
    simp only [add_zero]
    field_simp
  have hV : HasDerivAt (fun t : ℝ => (ba_f1h_prim h (z.re + (z.im + t)) - 2 * ba_f1h_prim h z.re +
      ba_f1h_prim h (z.re - (z.im + t))) / (2 * (z.im + t)))
      ((h (z.re + z.im) - h (z.re - z.im)) / (2 * z.im) -
        ((∫ t in z.re..(z.re + z.im), h t) - ∫ t in (z.re - z.im)..z.re, h t) / (2 * z.im ^ 2)) 0 := by
    refine (hNV.fun_div hD hden).congr_deriv ?_
    rw [← ba_f1h_prim_sub hcont, ← ba_f1h_prim_sub hcont]
    simp only [add_zero]
    field_simp
    ring
  have hfun : (fun t : ℝ => ba_f1h_closed h (z + t * I)) = fun t : ℝ =>
      (((ba_f1h_prim h (z.re + (z.im + t)) - ba_f1h_prim h (z.re - (z.im + t))) / (2 * (z.im + t)) : ℝ) : ℂ) +
      (((ba_f1h_prim h (z.re + (z.im + t)) - 2 * ba_f1h_prim h z.re + ba_f1h_prim h (z.re - (z.im + t))) /
        (2 * (z.im + t)) : ℝ) : ℂ) * I := by
    funext t
    simp only [ba_f1h_closed, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
      sub_zero, add_zero, mul_one]
  rw [hfun]
  exact hU.ofReal_comp.add (hV.ofReal_comp.mul_const I)

/-- **F1** (the formula): the Beurling–Ahlfors extension (`r = 1`) of a strictly increasing continuous `h` is continuous
on `ℂ`, `C¹` on `ℍ`, equal to `h` on `ℝ`, and maps `ℍ` into `ℍ` (`u = (1/2y)∫_{x-y}^{x+y} h`,
`v = (1/2y)(∫_x^{x+y} h - ∫_{x-y}^x h) > 0`). -/
theorem ba_f1_basic {h : ℝ → ℝ} (hmono : StrictMono h) (hcont : Continuous h) :
    Continuous (beurlingAhlfors h 1) ∧ ContDiffOn ℝ 1 (beurlingAhlfors h 1) upperHalf ∧
      (∀ x : ℝ, beurlingAhlfors h 1 x = h x) ∧ MapsTo (beurlingAhlfors h 1) upperHalf upperHalf := by
  refine ⟨ba_f1h_continuous hcont 1, ba_f1h_contDiffOn hcont, ba_f1h_real h, fun z hz => ?_⟩
  have hy : 0 < z.im := hz
  show 0 < (beurlingAhlfors h 1 z).im
  have him : (beurlingAhlfors h 1 z).im =
      1 / 2 * ∫ t in (0 : ℝ)..1, (h (z.re + t * z.im) - h (z.re - t * z.im)) := by
    simp [beurlingAhlfors]
  rw [him]
  refine mul_pos one_half_pos (intervalIntegral.intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous fun t : ℝ => h (z.re + t * z.im) - h (z.re - t * z.im)).intervalIntegrable 0 1)
    (fun t ht => sub_pos.2 (hmono ?_)) one_pos)
  nlinarith [ht.1]

/-- **F1'** (the partial derivatives, (17.8)–(17.9)): at `z = x + iy ∈ ℍ`, with `α = h(x+y)/2y`, `β = h(x-y)/2y`,
`γ = h(x)/2y`, `α₁ = (1/2y²)∫_x^{x+y} h`, `β₁ = (1/2y²)∫_{x-y}^x h`:
`f_x = (α - β) + i(α + β - 2γ)` and `f_y = (α + β - α₁ - β₁) + i((α - β) - (α₁ - β₁))`. -/
theorem ba_f1_partials {h : ℝ → ℝ} (hcont : Continuous h) {z : ℂ} (hz : z ∈ upperHalf) :
    fderiv ℝ (beurlingAhlfors h 1) z 1 =
        (((h (z.re + z.im) - h (z.re - z.im)) / (2 * z.im) : ℝ) : ℂ) +
          (((h (z.re + z.im) - 2 * h z.re + h (z.re - z.im)) / (2 * z.im) : ℝ) : ℂ) * I ∧
      fderiv ℝ (beurlingAhlfors h 1) z I =
        (((h (z.re + z.im) + h (z.re - z.im)) / (2 * z.im) -
            (∫ t in (z.re - z.im)..(z.re + z.im), h t) / (2 * z.im ^ 2) : ℝ) : ℂ) +
          (((h (z.re + z.im) - h (z.re - z.im)) / (2 * z.im) -
            ((∫ t in z.re..(z.re + z.im), h t) - ∫ t in (z.re - z.im)..z.re, h t) / (2 * z.im ^ 2) : ℝ) : ℂ) *
            I := by
  have hev : beurlingAhlfors h 1 =ᶠ[𝓝 z] ba_f1h_closed h :=
    Filter.eventually_of_mem (isOpen_upperHalf.mem_nhds hz) fun w hw =>
      ba_f1h_eq_closed hcont (show (0 : ℝ) < w.im from hw).ne'
  have hdiff : DifferentiableAt ℝ (ba_f1h_closed h) z :=
    ((ba_f1h_closed_contDiffOn hcont).contDiffAt (isOpen_upperHalf.mem_nhds hz)).differentiableAt one_ne_zero
  rw [hev.fderiv_eq, ← partialX_eq_of_differentiableAt hdiff, ← partialY_eq_of_differentiableAt hdiff]
  exact ⟨(ba_f1h_closed_line_re hcont z).deriv,
    (ba_f1h_closed_line_im hcont (show (0 : ℝ) < z.im from hz).ne').deriv⟩

/-- The Jacobian and the sum of the squared Wirtinger derivatives in terms of the real partials: if
`f_x = u_x + i v_x` and `f_y = u_y + i v_y` at `z`, then `|f_z|² - |f_z̄|² = u_x v_y - u_y v_x` and
`|f_z|² + |f_z̄|² = (u_x² + u_y² + v_x² + v_y²)/2`. -/
theorem ba_f2h_wirtinger {f : ℂ → ℂ} {z : ℂ} {ux vx uy vy : ℝ}
    (h1 : fderiv ℝ f z 1 = (ux : ℂ) + (vx : ℂ) * I) (hI : fderiv ℝ f z I = (uy : ℂ) + (vy : ℂ) * I) :
    ‖dz f z‖ ^ 2 - ‖dzbar f z‖ ^ 2 = ux * vy - uy * vx ∧
      ‖dz f z‖ ^ 2 + ‖dzbar f z‖ ^ 2 = (ux ^ 2 + uy ^ 2 + vx ^ 2 + vy ^ 2) / 2 := by
  simp only [dz, dzbar, h1, hI, Complex.sq_norm, Complex.normSq_apply]
  simp only [div_ofNat_re, sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, zero_mul, add_im, mul_im, zero_add, one_mul, zero_sub, sub_neg_eq_add, div_ofNat_im, sub_im]
  constructor <;> ring

/-- For `|f_z̄| < |f_z|`: `D_f (|f_z|² - |f_z̄|²) ≤ 2(|f_z|² + |f_z̄|²)`, because
`D_f = (|f_z| + |f_z̄|)/(|f_z| - |f_z̄|)` and `(|f_z| + |f_z̄|)² ≤ 2(|f_z|² + |f_z̄|²)`. -/
theorem ba_f2h_dq_mul_le {f : ℂ → ℂ} {z : ℂ} (hlt : ‖dzbar f z‖ < ‖dz f z‖) :
    dilatationQuotient f z * (‖dz f z‖ ^ 2 - ‖dzbar f z‖ ^ 2) ≤ 2 * (‖dz f z‖ ^ 2 + ‖dzbar f z‖ ^ 2) := by
  have hB := norm_nonneg (dzbar f z)
  have hA : 0 < ‖dz f z‖ := hB.trans_lt hlt
  have hAB : 0 < ‖dz f z‖ - ‖dzbar f z‖ := sub_pos.2 hlt
  have hD : dilatationQuotient f z = (‖dz f z‖ + ‖dzbar f z‖) / (‖dz f z‖ - ‖dzbar f z‖) := by
    unfold dilatationQuotient complexDilatation
    rw [norm_div]
    field_simp
  rw [hD, div_mul_eq_mul_div, div_le_iff₀ hAB]
  nlinarith [mul_nonneg hAB.le (sq_nonneg (‖dz f z‖ - ‖dzbar f z‖))]

/-- Midpoint bounds for the integral of a monotone continuous `h` over `[x, x + y]` (`y ≥ 0`):
`(y/2)(h(x) + h(x + y/2)) ≤ ∫_x^{x+y} h ≤ (y/2)(h(x + y/2) + h(x + y))`. -/
theorem ba_f2h_int_bounds {h : ℝ → ℝ} (hmono : Monotone h) (hcont : Continuous h) (x : ℝ) {y : ℝ}
    (hy : 0 ≤ y) :
    y / 2 * (h x + h (x + y / 2)) ≤ ∫ t in x..(x + y), h t ∧
      ∫ t in x..(x + y), h t ≤ y / 2 * (h (x + y / 2) + h (x + y)) := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) x (x + y / 2)) (hcont.intervalIntegrable (x + y / 2) (x + y))
  have h1 : x ≤ x + y / 2 := by linarith
  have h2 : x + y / 2 ≤ x + y := by linarith
  have l1 : ∫ _ in x..(x + y / 2), h x ≤ ∫ t in x..(x + y / 2), h t :=
    intervalIntegral.integral_mono_on h1 intervalIntegrable_const (hcont.intervalIntegrable _ _)
      (fun t ht => by exact hmono ht.1)
  have u1 : ∫ t in x..(x + y / 2), h t ≤ ∫ _ in x..(x + y / 2), h (x + y / 2) :=
    intervalIntegral.integral_mono_on h1 (hcont.intervalIntegrable _ _) intervalIntegrable_const
      (fun t ht => by exact hmono ht.2)
  have l2 : ∫ _ in (x + y / 2)..(x + y), h (x + y / 2) ≤ ∫ t in (x + y / 2)..(x + y), h t :=
    intervalIntegral.integral_mono_on h2 intervalIntegrable_const (hcont.intervalIntegrable _ _)
      (fun t ht => by exact hmono ht.1)
  have u2 : ∫ t in (x + y / 2)..(x + y), h t ≤ ∫ _ in (x + y / 2)..(x + y), h (x + y) :=
    intervalIntegral.integral_mono_on h2 (hcont.intervalIntegrable _ _) intervalIntegrable_const
      (fun t ht => by exact hmono ht.2)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at l1 u1 l2 u2
  rw [show x + y / 2 - x = y / 2 by ring] at l1 u1
  rw [show x + y - (x + y / 2) = y / 2 by ring] at l2 u2
  constructor <;> linarith

/-- A `ρ`-quasisymmetric function has `ρ > 0` (`0 < Δ(0, 1) ≤ ρ`). -/
theorem ba_f2h_rho_pos {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) : 0 < ρ := by
  have hhi := (hh.2.2.2.2 0 1 one_pos).2
  unfold qsRatio at hhi
  exact (div_pos (sub_pos.2 (hh.1 (by norm_num))) (sub_pos.2 (hh.1 (by norm_num)))).trans_le hhi

/-- The quasisymmetry inequalities in multiplicative form: for `t > 0`,
`h(x+t) - h(x) ≤ ρ(h(x) - h(x-t))` and `h(x) - h(x-t) ≤ ρ(h(x+t) - h(x))`. -/
theorem ba_f2h_qs_mul {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    h (x + t) - h x ≤ ρ * (h x - h (x - t)) ∧ h x - h (x - t) ≤ ρ * (h (x + t) - h x) := by
  obtain ⟨hlo, hhi⟩ := hh.2.2.2.2 x t ht
  have hρ := ba_f2h_rho_pos hh
  have hd : 0 < h x - h (x - t) := sub_pos.2 (hh.1 (by linarith))
  unfold qsRatio at hlo hhi
  rw [div_le_iff₀ hd] at hhi
  rw [le_div_iff₀ hd] at hlo
  refine ⟨by linarith, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hlo hρ.le
  rwa [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul] at hmul

/-- The pure-algebra step of (17.10)–(17.19): for `P, Q, S, T > 0` with `S ≤ Q`, `P ≤ T`, `T ≤ ρQ`, `Q ≤ ρT`,
`T ≤ (2ρ+2)P`, `Q ≤ (2ρ+2)S` and `ρ ≥ 0`, `P² + Q² + S² + T² ≤ 8ρ(ρ+1)(PQ + ST)` (the four squares are bounded by
`ρ·PQ`, `2ρ(ρ+1)·PQ`, `2ρ(ρ+1)·PQ` and `2ρ(ρ+1)·ST`). -/
theorem ba_f2h_alg {P Q S T ρ : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hS : 0 < S) (hT : 0 < T) (hρ0 : 0 ≤ ρ)
    (hSQ : S ≤ Q) (hPT : P ≤ T) (hTQ : T ≤ ρ * Q) (hQT : Q ≤ ρ * T) (hTP : T ≤ (2 * ρ + 2) * P)
    (hQS : Q ≤ (2 * ρ + 2) * S) :
    P ^ 2 + Q ^ 2 + S ^ 2 + T ^ 2 ≤ 8 * ρ * (ρ + 1) * (P * Q + S * T) := by
  have hk : 0 ≤ 2 * ρ * (ρ + 1) := by positivity
  have hQP : Q ≤ 2 * ρ * (ρ + 1) * P :=
    calc Q ≤ ρ * T := hQT
      _ ≤ ρ * ((2 * ρ + 2) * P) := mul_le_mul_of_nonneg_left hTP hρ0
      _ = 2 * ρ * (ρ + 1) * P := by ring
  have hTS : T ≤ 2 * ρ * (ρ + 1) * S :=
    calc T ≤ ρ * Q := hTQ
      _ ≤ ρ * ((2 * ρ + 2) * S) := mul_le_mul_of_nonneg_left hQS hρ0
      _ = 2 * ρ * (ρ + 1) * S := by ring
  have e1 : P ^ 2 ≤ ρ * (P * Q) :=
    calc P ^ 2 = P * P := sq P
      _ ≤ P * (ρ * Q) := mul_le_mul_of_nonneg_left (hPT.trans hTQ) hP.le
      _ = ρ * (P * Q) := by ring
  have e2 : Q ^ 2 ≤ 2 * ρ * (ρ + 1) * (P * Q) :=
    calc Q ^ 2 = Q * Q := sq Q
      _ ≤ Q * (2 * ρ * (ρ + 1) * P) := mul_le_mul_of_nonneg_left hQP hQ.le
      _ = 2 * ρ * (ρ + 1) * (P * Q) := by ring
  have e3 : S ^ 2 ≤ 2 * ρ * (ρ + 1) * (P * Q) :=
    calc S ^ 2 = S * S := sq S
      _ ≤ S * (2 * ρ * (ρ + 1) * P) := mul_le_mul_of_nonneg_left (hSQ.trans hQP) hS.le
      _ = 2 * ρ * (ρ + 1) * (P * S) := by ring
      _ ≤ 2 * ρ * (ρ + 1) * (P * Q) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSQ hP.le) hk
  have e4 : T ^ 2 ≤ 2 * ρ * (ρ + 1) * (S * T) :=
    calc T ^ 2 = T * T := sq T
      _ ≤ T * (2 * ρ * (ρ + 1) * S) := mul_le_mul_of_nonneg_left hTS hT.le
      _ = 2 * ρ * (ρ + 1) * (S * T) := by ring
  have hPQ : 0 ≤ ρ * (4 * ρ + 3) * (P * Q) := by positivity
  have hST : 0 ≤ ρ * (ρ + 1) * (S * T) := by positivity
  linarith

/-- The monotonicity facts and the bounds (17.11)–(17.18) in the scaled variables
`P = y h(x+y) - ∫_x^{x+y} h`, `Q = y(h(x) - h(x-y))`, `S = ∫_{x-y}^x h - y h(x-y)`, `T = y(h(x+y) - h(x))`
(`2y²` times the book's `α - α₁`, `γ - β`, `β₁ - β`, `α - γ`): the midpoint bounds of `∫ h` and the quasisymmetry
inequalities at `x` and `x ± y/2` give `PQ + ST > 0` and `P² + Q² + S² + T² ≤ 8ρ(ρ+1)(PQ + ST)`. -/
theorem ba_f2h_core {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) (x : ℝ) {y : ℝ} (hy : 0 < y)
    {P Q S T : ℝ} (hP : P = y * h (x + y) - ∫ t in x..(x + y), h t) (hQ : Q = y * (h x - h (x - y)))
    (hS : S = (∫ t in (x - y)..x, h t) - y * h (x - y)) (hT : T = y * (h (x + y) - h x)) :
    0 < P * Q + S * T ∧ P ^ 2 + Q ^ 2 + S ^ 2 + T ^ 2 ≤ 8 * ρ * (ρ + 1) * (P * Q + S * T) := by
  have hρ := ba_f2h_rho_pos hh
  have hmono := hh.1
  have hy2 : 0 < y / 2 := half_pos hy
  obtain ⟨hR1, hR2⟩ := ba_f2h_int_bounds hmono.monotone hh.2.1 x hy.le
  obtain ⟨hL1, hL2⟩ := ba_f2h_int_bounds hmono.monotone hh.2.1 (x - y) hy.le
  rw [show x - y + y = x by ring, show x - y + y / 2 = x - y / 2 by ring] at hL1 hL2
  obtain ⟨hq3, hq4⟩ := ba_f2h_qs_mul hh x hy
  have hq1 := (ba_f2h_qs_mul hh (x + y / 2) hy2).2
  have hq2 := (ba_f2h_qs_mul hh (x - y / 2) hy2).1
  rw [show x + y / 2 + y / 2 = x + y by ring, show x + y / 2 - y / 2 = x by ring] at hq1
  rw [show x - y / 2 + y / 2 = x by ring, show x - y / 2 - y / 2 = x - y by ring] at hq2
  have m1 : h (x - y) < h (x - y / 2) := hmono (by linarith)
  have m2 : h (x - y / 2) < h x := hmono (by linarith)
  have m3 : h x < h (x + y / 2) := hmono (by linarith)
  have m4 : h (x + y / 2) < h (x + y) := hmono (by linarith)
  subst hP hQ hS hT
  set Ip := ∫ t in x..(x + y), h t
  set Im := ∫ t in (x - y)..x, h t
  have p1 := mul_pos hy2 (sub_pos.2 m4)
  have p2 := mul_pos hy2 (sub_pos.2 m1)
  have p3 := mul_pos hy (sub_pos.2 m2)
  have p4 := mul_pos hy (sub_pos.2 m3)
  have hPlow : y / 2 * (h (x + y) - h (x + y / 2)) ≤ y * h (x + y) - Ip := by linarith
  have hSlow : y / 2 * (h (x - y / 2) - h (x - y)) ≤ Im - y * h (x - y) := by linarith
  have hPpos : 0 < y * h (x + y) - Ip := by linarith
  have hQpos : 0 < y * (h x - h (x - y)) := mul_pos hy (sub_pos.2 (m1.trans m2))
  have hSpos : 0 < Im - y * h (x - y) := by linarith
  have hTpos : 0 < y * (h (x + y) - h x) := mul_pos hy (sub_pos.2 (m3.trans m4))
  have hk : 0 ≤ 2 * ρ + 2 := by linarith
  have r1 := mul_le_mul_of_nonneg_left hq1 hy.le
  have r2 := mul_le_mul_of_nonneg_left hq2 hy.le
  have r3 := mul_le_mul_of_nonneg_left hq3 hy.le
  have r4 := mul_le_mul_of_nonneg_left hq4 hy.le
  have r5 := mul_le_mul_of_nonneg_left hPlow hk
  have r6 := mul_le_mul_of_nonneg_left hSlow hk
  refine ⟨add_pos (mul_pos hPpos hQpos) (mul_pos hSpos hTpos), ba_f2h_alg hPpos hQpos hSpos hTpos hρ.le
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)⟩

/-- The algebraic identities behind (17.10): with `u_x = (a - b)/2y`, `v_x = (a - 2c + b)/2y`,
`u_y = (a + b)/2y - (I₋ + I₊)/2y²`, `v_y = (a - b)/2y - (I₊ - I₋)/2y²` and `P = ya - I₊`, `Q = y(c - b)`,
`S = I₋ - yb`, `T = y(a - c)`: `u_x v_y - u_y v_x = (PQ + ST)/2y⁴` and
`(u_x² + u_y² + v_x² + v_y²)/2 = (P² + Q² + S² + T²)/4y⁴`. -/
theorem ba_f2h_ident {a b c Ip Im y : ℝ} (hy : y ≠ 0) :
    (a - b) / (2 * y) * ((a - b) / (2 * y) - (Ip - Im) / (2 * y ^ 2)) -
        ((a + b) / (2 * y) - (Im + Ip) / (2 * y ^ 2)) * ((a - 2 * c + b) / (2 * y)) =
      ((y * a - Ip) * (y * (c - b)) + (Im - y * b) * (y * (a - c))) / (2 * y ^ 4) ∧
    (((a - b) / (2 * y)) ^ 2 + ((a + b) / (2 * y) - (Im + Ip) / (2 * y ^ 2)) ^ 2 +
        ((a - 2 * c + b) / (2 * y)) ^ 2 + ((a - b) / (2 * y) - (Ip - Im) / (2 * y ^ 2)) ^ 2) / 2 =
      ((y * a - Ip) ^ 2 + (y * (c - b)) ^ 2 + (Im - y * b) ^ 2 + (y * (a - c)) ^ 2) / (4 * y ^ 4) := by
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- **F2** (the Jacobian and the dilatation, (17.10)–(17.19)): for `ρ`-quasisymmetric `h`,
`J_f = 2[(α - α₁)(γ - β) + (β₁ - β)(α - γ)] > 0` and `D_f ≤ 8ρ(ρ + 1)` on `ℍ`. -/
theorem ba_f2_dilatation {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) {z : ℂ} (hz : z ∈ upperHalf) :
    0 < jacobian (beurlingAhlfors h 1) z ∧ ‖dzbar (beurlingAhlfors h 1) z‖ < ‖dz (beurlingAhlfors h 1) z‖ ∧
      dilatationQuotient (beurlingAhlfors h 1) z ≤ 8 * ρ * (ρ + 1) := by
  have hy : 0 < z.im := hz
  obtain ⟨hfx, hfy⟩ := ba_f1_partials hh.2.1 hz
  rw [← intervalIntegral.integral_add_adjacent_intervals (hh.2.1.intervalIntegrable (z.re - z.im) z.re)
    (hh.2.1.intervalIntegrable z.re (z.re + z.im))] at hfy
  obtain ⟨hJ, hSum⟩ := ba_f2h_wirtinger hfx hfy
  obtain ⟨eJ, eSum⟩ := ba_f2h_ident (c := h z.re) hy.ne'
  rw [eJ] at hJ
  rw [eSum] at hSum
  obtain ⟨hpos, hle⟩ := ba_f2h_core hh z.re hy rfl rfl rfl rfl
  have hW := div_pos hpos (show (0 : ℝ) < 2 * z.im ^ 4 by positivity)
  have hJpos : 0 < jacobian (beurlingAhlfors h 1) z := by
    rw [jacobian, hJ]
    exact hW
  have hlt : ‖dzbar (beurlingAhlfors h 1) z‖ < ‖dz (beurlingAhlfors h 1) z‖ := by
    have h2 : ‖dzbar (beurlingAhlfors h 1) z‖ ^ 2 < ‖dz (beurlingAhlfors h 1) z‖ ^ 2 := by
      rw [jacobian] at hJpos
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2
  refine ⟨hJpos, hlt, ?_⟩
  have key := ba_f2h_dq_mul_le hlt
  rw [hJ, hSum] at key
  refine le_of_mul_le_mul_right (key.trans ?_) hW
  rw [show ∀ X : ℝ, 2 * (X / (4 * z.im ^ 4)) = X / (2 * z.im ^ 4) from fun X => by field_simp; ring,
    mul_div_assoc']
  exact div_le_div_of_nonneg_right hle (by positivity)

/-- The real and imaginary parts of the Beurling–Ahlfors extension `f = beurlingAhlfors h 1` of a continuous `h`:
`Re f = (α' + β')/2` and `Im f = (α' - β')/2` with `α' = ∫₀¹ h(x + ty) dt` and `β' = ∫₀¹ h(x - ty) dt`. -/
theorem ba_f3h_re_im {h : ℝ → ℝ} (hcont : Continuous h) (z : ℂ) :
    (beurlingAhlfors h 1 z).re =
        1 / 2 * ((∫ t in (0 : ℝ)..1, h (z.re + t * z.im)) + ∫ t in (0 : ℝ)..1, h (z.re - t * z.im)) ∧
      (beurlingAhlfors h 1 z).im =
        1 / 2 * ((∫ t in (0 : ℝ)..1, h (z.re + t * z.im)) - ∫ t in (0 : ℝ)..1, h (z.re - t * z.im)) := by
  have h1 : IntervalIntegrable (fun t : ℝ => h (z.re + t * z.im)) volume 0 1 :=
    (hcont.comp (continuous_const.add (continuous_id.mul continuous_const))).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun t : ℝ => h (z.re - t * z.im)) volume 0 1 :=
    (hcont.comp (continuous_const.sub (continuous_id.mul continuous_const))).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_add h1 h2, ← intervalIntegral.integral_sub h1 h2]
  simp [beurlingAhlfors]

/-- For increasing `h` and `y ≥ 0`: `∫₀¹ h(x - ty) dt ≤ h(x) ≤ ∫₀¹ h(x + ty) dt`, and, splitting at `t = ½`,
`½h(x) + ½h(x + y/2) ≤ ∫₀¹ h(x + ty) dt`. -/
theorem ba_f3h_bounds {h : ℝ → ℝ} (hmono : Monotone h) (hcont : Continuous h) (x : ℝ) {y : ℝ}
    (hy : 0 ≤ y) :
    (∫ t in (0 : ℝ)..1, h (x - t * y)) ≤ h x ∧ h x ≤ (∫ t in (0 : ℝ)..1, h (x + t * y)) ∧
      1 / 2 * h x + 1 / 2 * h (x + y / 2) ≤ ∫ t in (0 : ℝ)..1, h (x + t * y) := by
  have h1 : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => h (x + t * y)) volume a b := fun a b =>
    (hcont.comp (continuous_const.add (continuous_id.mul continuous_const))).intervalIntegrable a b
  have h2 : IntervalIntegrable (fun t : ℝ => h (x - t * y)) volume 0 1 :=
    (hcont.comp (continuous_const.sub (continuous_id.mul continuous_const))).intervalIntegrable 0 1
  have hc : ∀ c a b : ℝ, IntervalIntegrable (fun _ : ℝ => c) volume a b := fun _ _ _ =>
    intervalIntegrable_const
  refine ⟨?_, ?_, ?_⟩
  · have e := intervalIntegral.integral_mono_on zero_le_one h2 (hc (h x) 0 1) fun t ht =>
      hmono (by nlinarith [ht.1])
    simpa using e
  · have e := intervalIntegral.integral_mono_on zero_le_one (hc (h x) 0 1) (h1 0 1) fun t ht =>
      hmono (by nlinarith [ht.1])
    simpa using e
  · have e1 := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1 / 2) (hc (h x) 0 (1 / 2))
      (h1 0 (1 / 2)) fun t ht => hmono (by nlinarith [ht.1])
    have e2 := intervalIntegral.integral_mono_on (by norm_num : (1 / 2 : ℝ) ≤ 1)
      (hc (h (x + y / 2)) (1 / 2) 1) (h1 (1 / 2) 1) fun t ht => hmono (by nlinarith [ht.1])
    rw [← intervalIntegral.integral_add_adjacent_intervals (h1 0 (1 / 2)) (h1 (1 / 2) 1)]
    simp only [intervalIntegral.integral_const, smul_eq_mul] at e1 e2
    linarith

/-- Bounded preimages on the closed upper half-plane: for every `M` there is `R` with `‖z‖ ≤ R` whenever `Im z ≥ 0` and
`‖f z‖ ≤ M`, `f = beurlingAhlfors h 1` (`|α'|, |β'| ≤ 2M` gives `|h(x)| ≤ 2M`, hence `x ∈ (a, c)`, and
`h(x + y/2) ≤ 2α' - h(x) ≤ 6M` gives `x + y/2 < c`). -/
theorem ba_f3h_bounded {h : ℝ → ℝ} (hmono : StrictMono h) (hcont : Continuous h)
    (htop : Tendsto h atTop atTop) (hbot : Tendsto h atBot atBot) (M : ℝ) :
    ∃ R : ℝ, ∀ z : ℂ, 0 ≤ z.im → ‖beurlingAhlfors h 1 z‖ ≤ M → ‖z‖ ≤ R := by
  obtain ⟨a, ha⟩ := Filter.eventually_atBot.1 (hbot.eventually_lt_atBot (-(2 * M)))
  obtain ⟨c, hc⟩ := Filter.eventually_atTop.1 (htop.eventually_gt_atTop (6 * M))
  refine ⟨3 * (|a| + |c|), fun z hy hM => ?_⟩
  obtain ⟨hre, him⟩ := ba_f3h_re_im hcont z
  obtain ⟨hb1, hb2, hb3⟩ := ba_f3h_bounds hmono.monotone hcont z.re hy
  have hr := abs_le.1 ((Complex.abs_re_le_norm (beurlingAhlfors h 1 z)).trans hM)
  have hi := abs_le.1 ((Complex.abs_im_le_norm (beurlingAhlfors h 1 z)).trans hM)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hxa : a < z.re := by
    by_contra hcon
    push Not at hcon
    have := ha _ hcon
    linarith
  have hxc : z.re < c := by
    by_contra hcon
    push Not at hcon
    have := hc _ hcon
    linarith
  have hyc : z.re + z.im / 2 < c := by
    by_contra hcon
    push Not at hcon
    have := hc _ hcon
    linarith
  have hre' : |z.re| ≤ |a| + |c| :=
    abs_le.2 ⟨by linarith [neg_abs_le a, abs_nonneg c], by linarith [le_abs_self c, abs_nonneg a]⟩
  have him' : |z.im| ≤ 2 * (|a| + |c|) := by
    rw [abs_of_nonneg hy]
    linarith [neg_abs_le a, le_abs_self c]
  linarith [Complex.norm_le_abs_re_add_abs_im z]

/-- **F3** (properness at `∞`): `f(z) → ∞` as `z → ∞` in the closed upper half-plane (with `α' = ∫₀¹ h(x + ty) dt`,
`β' = ∫₀¹ h(x - ty) dt`: `β' ≤ h(x) ≤ α'` bounds `x`, and `α' ≥ ½h(x) + ½h(x + y/2)` bounds `y`). -/
theorem ba_f3_tendsto {h : ℝ → ℝ} (hmono : StrictMono h) (hcont : Continuous h)
    (htop : Tendsto h atTop atTop) (hbot : Tendsto h atBot atBot) :
    Tendsto (beurlingAhlfors h 1) (cocompact ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (cocompact ℂ) := by
  refine ((hasBasis_cocompact.inf_principal _).tendsto_iff hasBasis_cocompact).2 fun K hK => ?_
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨R, hR⟩ := ba_f3h_bounded hmono hcont htop hbot M
  refine ⟨closedBall 0 R, isCompact_closedBall 0 R, fun z hz hfz => hz.1 ?_⟩
  have hfM := hM hfz
  rw [mem_closedBall, dist_zero_right] at hfM ⊢
  exact hR z hz.2 hfM

/-- The Jacobian in real coordinates: `J_f = u_x v_y - u_y v_x` with `f_x = fderiv f z 1 = u_x + i v_x` and
`f_y = fderiv f z I = u_y + i v_y`. -/
theorem ba_qih_jacobian_eq (f : ℂ → ℂ) (z : ℂ) :
    jacobian f z = (fderiv ℝ f z 1).re * (fderiv ℝ f z I).im - (fderiv ℝ f z 1).im * (fderiv ℝ f z I).re := by
  simp only [jacobian, dz, dzbar, Complex.sq_norm, Complex.normSq_apply, Complex.div_re, Complex.div_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  norm_num
  ring

/-- The real and imaginary parts of `a + b i` for real `a`, `b`. -/
theorem ba_qih_re_im (a b : ℝ) : ((a : ℂ) + (b : ℂ) * I).re = a ∧ ((a : ℂ) + (b : ℂ) * I).im = b := by
  constructor <;> simp

/-- (17.21), first half: `‖df(z)‖ ≤ |∂_z f| + |∂_{z̄} f|`, since `df(z) w = ∂_z f · w + ∂_{z̄} f · w̄`. -/
theorem ba_qih_norm_fderiv_le {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    ‖fderiv ℝ f z‖ ≤ ‖dz f z‖ + ‖dzbar f z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [fderiv_eq_dz_dzbar hf w]
  calc ‖dz f z * w + dzbar f z * conj w‖ ≤ ‖dz f z * w‖ + ‖dzbar f z * conj w‖ := norm_add_le _ _
    _ = (‖dz f z‖ + ‖dzbar f z‖) * ‖w‖ := by rw [norm_mul, norm_mul, Complex.norm_conj]; ring

/-- (17.21), second half: `(|∂_z f| + |∂_{z̄} f|)² = D_f J_f ≤ K J_f` when `|∂_{z̄} f| < |∂_z f|`, `J_f > 0` and
`D_f ≤ K`. -/
theorem ba_qih_sq_le {f : ℂ → ℂ} {z : ℂ} {K : ℝ} (hJ : 0 < jacobian f z) (hlt : ‖dzbar f z‖ < ‖dz f z‖)
    (hD : dilatationQuotient f z ≤ K) : (‖dz f z‖ + ‖dzbar f z‖) ^ 2 ≤ K * jacobian f z := by
  have ha : 0 < ‖dz f z‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have hμ : ‖complexDilatation f z‖ = ‖dzbar f z‖ / ‖dz f z‖ := by rw [complexDilatation, norm_div]
  have hne : ‖dz f z‖ - ‖dzbar f z‖ ≠ 0 := (sub_pos.2 hlt).ne'
  have heq : (‖dz f z‖ + ‖dzbar f z‖) ^ 2 = dilatationQuotient f z * jacobian f z := by
    rw [dilatationQuotient, hμ, jacobian]
    field_simp
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hD hJ.le

/-- (17.22): `y² J_f ≤ ρ (h(x) - h(x-y))²` at `z = x + iy ∈ ℍ` for the Beurling–Ahlfors extension of a
`ρ`-quasisymmetric `h`: `J_f = 2[(α - α₁)(γ - β) + (β₁ - β)(α - γ)] ≤ 4(α - γ)(γ - β)` since `α₁ ≥ γ ≥ β₁`, and
`α - γ ≤ ρ(γ - β)`, `γ - β = (h(x) - h(x-y))/2y`. -/
theorem ba_qih_jacobian_le {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) {z : ℂ} (hz : z ∈ upperHalf) :
    z.im ^ 2 * jacobian (beurlingAhlfors h 1) z ≤ ρ * (h z.re - h (z.re - z.im)) ^ 2 := by
  obtain ⟨hmono, hcont, -, -, hqs⟩ := hh
  have hy : 0 < z.im := hz
  obtain ⟨hfx, hfy⟩ := ba_f1_partials hcont hz
  have htot := intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable (μ := volume)
    (z.re - z.im) z.re) (hcont.intervalIntegrable z.re (z.re + z.im))
  rw [ba_qih_jacobian_eq, hfx, hfy, (ba_qih_re_im _ _).1, (ba_qih_re_im _ _).2, (ba_qih_re_im _ _).1,
    (ba_qih_re_im _ _).2, ← htot]
  -- `α₁ ≥ γ ≥ β₁`: `∫_x^{x+y} h ≥ y h(x) ≥ ∫_{x-y}^x h`
  have hP : z.im * h z.re ≤ ∫ t in z.re..(z.re + z.im), h t := by
    have h1 := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => h z.re) (g := h)
      (show z.re ≤ z.re + z.im by linarith) (continuous_const.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _) (fun t ht => by exact hmono.monotone ht.1)
    rwa [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at h1
  have hM : ∫ t in (z.re - z.im)..z.re, h t ≤ z.im * h z.re := by
    have h1 := intervalIntegral.integral_mono_on (μ := volume) (f := h) (g := fun _ => h z.re)
      (show z.re - z.im ≤ z.re by linarith) (hcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) (fun t ht => by exact hmono.monotone ht.2)
    rwa [intervalIntegral.integral_const, smul_eq_mul, sub_sub_cancel] at h1
  have hCB : 0 < h z.re - h (z.re - z.im) := sub_pos.2 (hmono (by linarith))
  have hAC : 0 < h (z.re + z.im) - h z.re := sub_pos.2 (hmono (by linarith))
  -- quasisymmetry: `α - γ ≤ ρ (γ - β)`
  have hq : h (z.re + z.im) - h z.re ≤ ρ * (h z.re - h (z.re - z.im)) :=
    (div_le_iff₀ hCB).1 (hqs z.re z.im hy).2
  set A := h (z.re + z.im)
  set B := h (z.re - z.im)
  set C := h z.re
  set P := ∫ t in z.re..(z.re + z.im), h t
  set M := ∫ t in (z.re - z.im)..z.re, h t
  set y := z.im
  have hy0 : y ≠ 0 := hy.ne'
  have hk : 0 ≤ ((P - y * C) * (C - B) + (y * C - M) * (A - C)) / (2 * y) :=
    div_nonneg (add_nonneg (mul_nonneg (by linarith) hCB.le) (mul_nonneg (by linarith) hAC.le)) (by positivity)
  calc _ = (A - C) * (C - B) - ((P - y * C) * (C - B) + (y * C - M) * (A - C)) / (2 * y) := by
        field_simp
        ring
    _ ≤ (A - C) * (C - B) := sub_le_self _ hk
    _ ≤ ρ * (C - B) * (C - B) := mul_le_mul_of_nonneg_right hq hCB.le
    _ = ρ * (C - B) ^ 2 := by ring

/-- (17.23): `Im f(z) ≥ (h(x) - h(x-y))/(4(ρ+1))` at `z = x + iy ∈ ℍ`: `Im f = ½∫₀¹ (h(x+ty) - h(x-ty)) dt`, the
integrand is `≥ 0` on `[0, ½]` and `≥ h(x) - h(x-y/2)` on `[½, 1]`, and quasisymmetry at `(x - y/2, y/2)` gives
`h(x) - h(x-y) ≤ (1 + ρ)(h(x) - h(x-y/2))`. -/
theorem ba_qih_im_lower {h : ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ) (hh : IsQuasisymmetric h ρ) {z : ℂ}
    (hz : z ∈ upperHalf) :
    h z.re - h (z.re - z.im) ≤ 4 * (ρ + 1) * (beurlingAhlfors h 1 z).im := by
  obtain ⟨hmono, hcont, -, -, hqs⟩ := hh
  have hy : 0 < z.im := hz
  have him : (beurlingAhlfors h 1 z).im =
      1 / 2 * ∫ t in (0 : ℝ)..1, (h (z.re + t * z.im) - h (z.re - t * z.im)) := by
    rw [beurlingAhlfors, (ba_qih_re_im _ _).2]
  have hFc : Continuous fun t : ℝ => h (z.re + t * z.im) - h (z.re - t * z.im) := by fun_prop
  -- `∫₀¹ ≥ ∫_{1/2}^1 ≥ (h(x) - h(x - y/2))/2`
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hFc.intervalIntegrable (μ := volume) 0 (1 / 2))
    (hFc.intervalIntegrable (1 / 2) 1)
  have h1 : 0 ≤ ∫ t in (0 : ℝ)..(1 / 2), (h (z.re + t * z.im) - h (z.re - t * z.im)) :=
    intervalIntegral.integral_nonneg (by norm_num) fun t ht =>
      sub_nonneg.2 (hmono.monotone (by nlinarith [ht.1]))
  have h2 := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => h z.re - h (z.re - z.im / 2))
    (g := fun t => h (z.re + t * z.im) - h (z.re - t * z.im)) (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    (continuous_const.intervalIntegrable _ _) (hFc.intervalIntegrable _ _) fun t ht => by
      have e1 := hmono.monotone (show z.re ≤ z.re + t * z.im by nlinarith [ht.1])
      have e2 := hmono.monotone (show z.re - t * z.im ≤ z.re - z.im / 2 by nlinarith [ht.1])
      linarith
  rw [intervalIntegral.integral_const, smul_eq_mul] at h2
  -- quasisymmetry at `(x - y/2, y/2)`: `h(x) - h(x-y) ≤ (1 + ρ)(h(x) - h(x - y/2))`
  have hlo := (hqs (z.re - z.im / 2) (z.im / 2) (by linarith)).1
  rw [qsRatio, show z.re - z.im / 2 + z.im / 2 = z.re by ring,
    show z.re - z.im / 2 - z.im / 2 = z.re - z.im by ring] at hlo
  have hb : 0 < h (z.re - z.im / 2) - h (z.re - z.im) := sub_pos.2 (hmono (by linarith))
  have hb' : h (z.re - z.im / 2) - h (z.re - z.im) ≤ ρ * (h z.re - h (z.re - z.im / 2)) := by
    rw [le_div_iff₀ hb] at hlo
    have := mul_le_mul_of_nonneg_left hlo hρ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul] at this
  rw [him]
  nlinarith

/-- **QI** (the quasi-isometry bound (17.20)–(17.23)): `‖df(z)‖/Im f(z) ≤ √(128ρ²(ρ+1)³)/Im z` on `ℍ`
(`‖df‖² ≤ D_f J ≤ 8ρ(ρ+1) J`, `y² J ≤ ρ (h(x) - h(x-y))²`, `Im f ≥ (h(x) - h(x-y))/(4(ρ+1))`). -/
theorem ba_qi_bound {h : ℝ → ℝ} {ρ : ℝ} (hρ : 1 ≤ ρ) (hh : IsQuasisymmetric h ρ) {z : ℂ} (hz : z ∈ upperHalf) :
    ‖fderiv ℝ (beurlingAhlfors h 1) z‖ / (beurlingAhlfors h 1 z).im ≤
      Real.sqrt (128 * ρ ^ 2 * (ρ + 1) ^ 3) / z.im := by
  have hy : 0 < z.im := hz
  have hρ0 : 0 < ρ := by linarith
  obtain ⟨hJ, hlt, hD⟩ := ba_f2_dilatation hh hz
  -- `f` is differentiable at `z`: otherwise `df(z) = 0` and `J_f(z) = 0`
  have hdiff : DifferentiableAt ℝ (beurlingAhlfors h 1) z := by
    by_contra hnd
    have h0 := fderiv_zero_of_not_differentiableAt hnd
    have hJ0 : jacobian (beurlingAhlfors h 1) z = 0 := by simp [jacobian, dz, dzbar, h0]
    linarith
  have h1 := ba_qih_norm_fderiv_le hdiff
  have h2 := ba_qih_sq_le hJ hlt hD
  have h3 := ba_qih_jacobian_le hh hz
  have h4 := ba_qih_im_lower hρ0 hh hz
  have hD0 : 0 < h z.re - h (z.re - z.im) := sub_pos.2 (hh.1 (by linarith))
  have hv : 0 < (beurlingAhlfors h 1 z).im := by nlinarith
  rw [div_le_div_iff₀ hv hy]
  set n := ‖fderiv ℝ (beurlingAhlfors h 1) z‖
  set v := (beurlingAhlfors h 1 z).im
  set J := jacobian (beurlingAhlfors h 1) z
  set S := ‖dz (beurlingAhlfors h 1) z‖ + ‖dzbar (beurlingAhlfors h 1) z‖
  set D := h z.re - h (z.re - z.im)
  set y := z.im
  have hn : 0 ≤ n := norm_nonneg _
  have hsq : (n * y) ^ 2 ≤ 128 * ρ ^ 2 * (ρ + 1) ^ 3 * v ^ 2 := by
    calc (n * y) ^ 2 = n ^ 2 * y ^ 2 := by ring
      _ ≤ S ^ 2 * y ^ 2 := by gcongr
      _ ≤ 8 * ρ * (ρ + 1) * J * y ^ 2 := by gcongr
      _ = 8 * ρ * (ρ + 1) * (y ^ 2 * J) := by ring
      _ ≤ 8 * ρ * (ρ + 1) * (ρ * D ^ 2) := by gcongr
      _ ≤ 8 * ρ * (ρ + 1) * (ρ * (4 * (ρ + 1) * v) ^ 2) := by gcongr
      _ = 128 * ρ ^ 2 * (ρ + 1) ^ 3 * v ^ 2 := by ring
  calc n * y = Real.sqrt ((n * y) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (128 * ρ ^ 2 * (ρ + 1) ^ 3 * v ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (128 * ρ ^ 2 * (ρ + 1) ^ 3) * v := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hv.le]

/-- A `ρ`-quasisymmetric function has `ρ ≥ 1` (`ρ⁻¹ ≤ Δ ≤ ρ` with `Δ > 0`). -/
theorem ba_one_le_rho {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) : 1 ≤ ρ := by
  obtain ⟨hlo, hhi⟩ := hh.2.2.2.2 0 1 one_pos
  have hpos : 0 < qsRatio h 0 1 := by
    unfold qsRatio
    exact div_pos (sub_pos.2 (hh.1 (by norm_num))) (sub_pos.2 (hh.1 (by norm_num)))
  have hρ : 0 < ρ := hpos.trans_le hhi
  have h1 : ρ⁻¹ ≤ ρ := hlo.trans hhi
  by_contra hlt
  push Not at hlt
  have : 1 < ρ⁻¹ := one_lt_inv_iff₀.2 ⟨hρ, hlt⟩
  linarith

/-- **Theorem 17.2** (Beurling–Ahlfors).  For a `ρ`-quasisymmetric `h`, the extension (17.6) with
`r = 1` is a `C¹` `K`-q.c. self-map of `ℍ` with boundary values `h` and `K ≤ 8ρ(ρ+1)`. -/
theorem thm17_2_beurling_ahlfors {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) :
    ContDiffOn ℝ 1 (beurlingAhlfors h 1) upperHalf ∧
      HasQCExtensionH h (beurlingAhlfors h 1) (8 * ρ * (ρ + 1)) := by
  obtain ⟨hcont0, hC1, hbd, hmaps⟩ := ba_f1_basic hh.1 hh.2.1
  have hJ : ∀ z ∈ upperHalf, 0 < jacobian (beurlingAhlfors h 1) z := fun z hz => (ba_f2_dilatation hh hz).1
  have hinf := ba_f3_tendsto hh.1 hh.2.1 hh.2.2.1 hh.2.2.2.1
  obtain ⟨himg, G, hG, hGinf, hGx⟩ :=
    ba_homeo_package hC1 hJ hcont0.continuousOn hmaps hbd hh.1 hinf
  refine ⟨hC1, ?_, himg, G, hG, hGinf, hGx⟩
  have hHsub : upperHalf ⊆ {z : ℂ | 0 ≤ z.im} := fun z hz => le_of_lt (show (0 : ℝ) < z.im from hz)
  have hreal : ∀ x : ℝ, (beurlingAhlfors h 1 x).im = 0 := fun x => by rw [hbd x]; simp
  have hhom := ba_homeomorph_upperHalf_of_contDiff hC1 hJ hmaps
    (hinf.mono_left (inf_le_inf_left _ (principal_mono.2 hHsub)))
    (ba_bdry_of_continuousWithinAt (fun x => hcont0.continuousAt.continuousWithinAt) hreal)
  have hhom' : IsHomeomorphOnto (beurlingAhlfors h 1) upperHalf (beurlingAhlfors h 1 '' upperHalf) := by
    rw [himg]
    exact hhom
  have hρ := ba_one_le_rho hh
  refine isKQC_of_isC1Quasiconformal ⟨isOpen_upperHalf, by nlinarith, hC1, hhom', fun z hz => ?_⟩
  exact ⟨(ba_f2_dilatation hh hz).2.1, (ba_f2_dilatation hh hz).2.2⟩

/-! ### (17.7) track (s21u P1, prover Q17): the Beurling–Ahlfors extension with `r = 2` has `K ≤ ρ²` -/

/-- The normalized dilatation defect of the Beurling–Ahlfors map with `r = 2`: with `ξ = b/a`, `A = p/a`, `B = n/b`
(`a = h(x+y) - h(x)`, `b = h(x) - h(x-y)`, `p`, `n` the one-sided means), the normalized partials are
`U_x = (1+ξ)/2`, `U_y = (1-ξ)/2 - (A - ξB)/2`, `V_x = 1 - ξ`, `V_y = (1+ξ) - (A + ξB)`, and
`Dba = ρ²(U_x² + U_y² + V_x² + V_y²) - (ρ⁴ + 1)(U_x V_y - U_y V_x)`; `Dba ≤ 0` means `K ≤ ρ²`. -/
def s17p_Dba (ρ ξ A B : ℝ) : ℝ :=
  ρ ^ 2 * (((1 + ξ) / 2) ^ 2 + ((1 - ξ) / 2 - (A - ξ * B) / 2) ^ 2 + (1 - ξ) ^ 2 +
      ((1 + ξ) - (A + ξ * B)) ^ 2)
    - (ρ ^ 4 + 1) * (((1 + ξ) / 2) * ((1 + ξ) - (A + ξ * B)) - ((1 - ξ) / 2 - (A - ξ * B) / 2) * (1 - ξ))

/-- A quadratic with nonnegative leading coefficient is bounded on `[lo, hi]` by its endpoint values. -/
theorem s17p_quad_le_max {f : ℝ → ℝ} {α lo hi t : ℝ} (hα : 0 ≤ α) (hlo : lo ≤ t) (hhi : t ≤ hi)
    (hid : (hi - t) * f lo + (t - lo) * f hi - (hi - lo) * f t =
      α * (t - lo) * (hi - t) * (hi - lo)) :
    f t ≤ max (f lo) (f hi) := by
  rcases eq_or_lt_of_le (hlo.trans hhi) with heq | hlt
  · have h1 : t = lo := le_antisymm (heq ▸ hhi) hlo
    rw [h1]
    exact le_max_left _ _
  · have hpos : 0 < hi - lo := sub_pos.2 hlt
    have hM1 : f lo ≤ max (f lo) (f hi) := le_max_left _ _
    have hM2 : f hi ≤ max (f lo) (f hi) := le_max_right _ _
    have h3 : 0 ≤ α * (t - lo) * (hi - t) * (hi - lo) :=
      mul_nonneg (mul_nonneg (mul_nonneg hα (sub_nonneg.2 hlo)) (sub_nonneg.2 hhi)) hpos.le
    have key : (hi - lo) * f t ≤ (hi - lo) * max (f lo) (f hi) := by
      nlinarith [mul_le_mul_of_nonneg_left hM1 (sub_nonneg.2 hhi),
        mul_le_mul_of_nonneg_left hM2 (sub_nonneg.2 hlo)]
    exact le_of_mul_le_mul_left key hpos

/-- If `D s = -P` with `s > 0` and `P ≥ 0`, then `D ≤ 0`. -/
theorem s17p_nonpos_of_mul_sq {D s P : ℝ} (hs : 0 < s) (hP : 0 ≤ P) (h : D * s = -P) : D ≤ 0 := by
  by_contra hc
  push Not at hc
  have := mul_pos hc hs
  linarith

/-- Vertex `ξ = 1/ρ`, `A = 1/(1+ρ)`, `B = 1/(1+ρ)` (`ρ = 1 + t`): `Dba = -P(t)/((1+t)(2+t))²`, `P ≥ 0`. -/
theorem s17p_v_inv_lo_lo {t : ℝ} (ht : 0 ≤ t) :
    s17p_Dba (1 + t) (1 / (1 + t)) (1 / (1 + (1 + t))) (1 / (1 + (1 + t))) ≤ 0 := by
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have h2 : (0 : ℝ) < 1 + (1 + t) := by linarith
  refine s17p_nonpos_of_mul_sq (s := ((1 + t) * (1 + (1 + t))) ^ 2) (by positivity)
    (P := (35/4:ℝ) * t^2 + (33:ℝ) * t^3 + (197/4:ℝ) * t^4 + (73/2:ℝ) * t^5 + (27/2:ℝ) * t^6 + (2:ℝ) * t^7)
    (by positivity) ?_
  unfold s17p_Dba
  field_simp
  ring

/-- Vertex `ξ = 1/ρ`, `A = 1/(1+ρ)`, `B = ρ/(1+ρ)` (`ρ = 1 + t`): `Dba = -P(t)/((1+t)(2+t))²`, `P ≥ 0`. -/
theorem s17p_v_inv_lo_hi {t : ℝ} (ht : 0 ≤ t) :
    s17p_Dba (1 + t) (1 / (1 + t)) (1 / (1 + (1 + t))) ((1 + t) / (1 + (1 + t))) ≤ 0 := by
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have h2 : (0 : ℝ) < 1 + (1 + t) := by linarith
  refine s17p_nonpos_of_mul_sq (s := ((1 + t) * (1 + (1 + t))) ^ 2) (by positivity)
    (P := (7:ℝ) * t^2 + (21:ℝ) * t^3 + (53/2:ℝ) * t^4 + (18:ℝ) * t^5 + (13/2:ℝ) * t^6 + (1:ℝ) * t^7)
    (by positivity) ?_
  unfold s17p_Dba
  field_simp
  ring

/-- Vertex `ξ = 1/ρ`, `A = ρ/(1+ρ)`, `B = 1/(1+ρ)` (`ρ = 1 + t`): `Dba = -P(t)/((1+t)(2+t))²`, `P ≥ 0`. -/
theorem s17p_v_inv_hi_lo {t : ℝ} (ht : 0 ≤ t) :
    s17p_Dba (1 + t) (1 / (1 + t)) ((1 + t) / (1 + (1 + t))) (1 / (1 + (1 + t))) ≤ 0 := by
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have h2 : (0 : ℝ) < 1 + (1 + t) := by linarith
  refine s17p_nonpos_of_mul_sq (s := ((1 + t) * (1 + (1 + t))) ^ 2) (by positivity)
    (P := (12:ℝ) * t^2 + (36:ℝ) * t^3 + (171/4:ℝ) * t^4 + (51/2:ℝ) * t^5 + (31/4:ℝ) * t^6 + (1:ℝ) * t^7)
    (by positivity) ?_
  unfold s17p_Dba
  field_simp
  ring

/-- Vertex `ξ = 1/ρ`, `A = ρ/(1+ρ)`, `B = ρ/(1+ρ)` (`ρ = 1 + t`): `Dba = -P(t)/((1+t)(2+t))²`, `P ≥ 0`. -/
theorem s17p_v_inv_hi_hi {t : ℝ} (ht : 0 ≤ t) :
    s17p_Dba (1 + t) (1 / (1 + t)) ((1 + t) / (1 + (1 + t))) ((1 + t) / (1 + (1 + t))) ≤ 0 := by
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have h2 : (0 : ℝ) < 1 + (1 + t) := by linarith
  refine s17p_nonpos_of_mul_sq (s := ((1 + t) * (1 + (1 + t))) ^ 2) (by positivity)
    (P := (35/4:ℝ) * t^2 + (39/2:ℝ) * t^3 + (31/2:ℝ) * t^4 + (11/2:ℝ) * t^5 + (3/4:ℝ) * t^6)
    (by positivity) ?_
  unfold s17p_Dba
  field_simp
  ring

/-- Vertex `ξ = ρ`, `A = 1/(1+ρ)`, `B = 1/(1+ρ)` (`ρ = 1 + t`): `Dba = -P(t)/((1+t)(2+t))²`, `P ≥ 0`. -/
theorem s17p_v_rho_lo_lo {t : ℝ} (ht : 0 ≤ t) :
    s17p_Dba (1 + t) (1 + t) (1 / (1 + (1 + t))) (1 / (1 + (1 + t))) ≤ 0 := by
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have h2 : (0 : ℝ) < 1 + (1 + t) := by linarith
  refine s17p_nonpos_of_mul_sq (s := ((1 + t) * (1 + (1 + t))) ^ 2) (by positivity)
    (P := (35/4:ℝ) * t^2 + (101/2:ℝ) * t^3 + (124:ℝ) * t^4 + (168:ℝ) * t^5 + (543/4:ℝ) * t^6 +
      (131/2:ℝ) * t^7 + (35/2:ℝ) * t^8 + (2:ℝ) * t^9)
    (by positivity) ?_
  unfold s17p_Dba
  field_simp
  ring

/-- Vertex `ξ = ρ`, `A = 1/(1+ρ)`, `B = ρ/(1+ρ)` (`ρ = 1 + t`): `Dba = -P(t)/((1+t)(2+t))²`, `P ≥ 0`. -/
theorem s17p_v_rho_lo_hi {t : ℝ} (ht : 0 ≤ t) :
    s17p_Dba (1 + t) (1 + t) (1 / (1 + (1 + t))) ((1 + t) / (1 + (1 + t))) ≤ 0 := by
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have h2 : (0 : ℝ) < 1 + (1 + t) := by linarith
  refine s17p_nonpos_of_mul_sq (s := ((1 + t) * (1 + (1 + t))) ^ 2) (by positivity)
    (P := (12:ℝ) * t^2 + (60:ℝ) * t^3 + (507/4:ℝ) * t^4 + (147:ℝ) * t^5 + (203/2:ℝ) * t^6 +
      (42:ℝ) * t^7 + (39/4:ℝ) * t^8 + (1:ℝ) * t^9)
    (by positivity) ?_
  unfold s17p_Dba
  field_simp
  ring

/-- Vertex `ξ = ρ`, `A = ρ/(1+ρ)`, `B = 1/(1+ρ)` (`ρ = 1 + t`): `Dba = -P(t)/((1+t)(2+t))²`, `P ≥ 0`. -/
theorem s17p_v_rho_hi_lo {t : ℝ} (ht : 0 ≤ t) :
    s17p_Dba (1 + t) (1 + t) ((1 + t) / (1 + (1 + t))) (1 / (1 + (1 + t))) ≤ 0 := by
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have h2 : (0 : ℝ) < 1 + (1 + t) := by linarith
  refine s17p_nonpos_of_mul_sq (s := ((1 + t) * (1 + (1 + t))) ^ 2) (by positivity)
    (P := (7:ℝ) * t^2 + (35:ℝ) * t^3 + (151/2:ℝ) * t^4 + (92:ℝ) * t^5 + (69:ℝ) * t^6 +
      (32:ℝ) * t^7 + (17/2:ℝ) * t^8 + (1:ℝ) * t^9)
    (by positivity) ?_
  unfold s17p_Dba
  field_simp
  ring

/-- Vertex `ξ = ρ`, `A = ρ/(1+ρ)`, `B = ρ/(1+ρ)` (`ρ = 1 + t`): `Dba = -P(t)/((1+t)(2+t))²`, `P ≥ 0`. -/
theorem s17p_v_rho_hi_hi {t : ℝ} (ht : 0 ≤ t) :
    s17p_Dba (1 + t) (1 + t) ((1 + t) / (1 + (1 + t))) ((1 + t) / (1 + (1 + t))) ≤ 0 := by
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have h2 : (0 : ℝ) < 1 + (1 + t) := by linarith
  refine s17p_nonpos_of_mul_sq (s := ((1 + t) * (1 + (1 + t))) ^ 2) (by positivity)
    (P := (35/4:ℝ) * t^2 + (37:ℝ) * t^3 + (253/4:ℝ) * t^4 + (56:ℝ) * t^5 + (109/4:ℝ) * t^6 +
      (7:ℝ) * t^7 + (3/4:ℝ) * t^8)
    (by positivity) ?_
  unfold s17p_Dba
  field_simp
  ring

/-- `Dba` is a convex quadratic in `ξ`: on `[1/ρ, ρ]` it is bounded by its endpoint values. -/
theorem s17p_step_xi {ρ ξ A B : ℝ} (hρ : 0 < ρ) (h1 : 1 / ρ ≤ ξ) (h2 : ξ ≤ ρ) :
    s17p_Dba ρ ξ A B ≤ max (s17p_Dba ρ (1 / ρ) A B) (s17p_Dba ρ ρ A B) :=
  s17p_quad_le_max (f := fun ξ => s17p_Dba ρ ξ A B) (α := 5 * ρ ^ 2 * (1 + (1 - B) ^ 2) / 4) (by positivity)
    h1 h2 (by simp only [s17p_Dba]; ring)

/-- `Dba` is a convex quadratic in `B`: on `[lo, hi]` it is bounded by its endpoint values. -/
theorem s17p_step_B {ρ ξ A B lo hi : ℝ} (h1 : lo ≤ B) (h2 : B ≤ hi) :
    s17p_Dba ρ ξ A B ≤ max (s17p_Dba ρ ξ A lo) (s17p_Dba ρ ξ A hi) :=
  s17p_quad_le_max (f := fun B => s17p_Dba ρ ξ A B) (α := 5 * ρ ^ 2 * ξ ^ 2 / 4) (by positivity)
    h1 h2 (by simp only [s17p_Dba]; ring)

/-- `Dba` is a convex quadratic in `A`: on `[lo, hi]` it is bounded by its endpoint values. -/
theorem s17p_step_A {ρ ξ A B lo hi : ℝ} (h1 : lo ≤ A) (h2 : A ≤ hi) :
    s17p_Dba ρ ξ A B ≤ max (s17p_Dba ρ ξ lo B) (s17p_Dba ρ ξ hi B) :=
  s17p_quad_le_max (f := fun A => s17p_Dba ρ ξ A B) (α := 5 * ρ ^ 2 / 4) (by positivity)
    h1 h2 (by simp only [s17p_Dba]; ring)

/-- **The algebraic core of (17.7)**: on the box `ξ ∈ [1/ρ, ρ]`, `A, B ∈ [1/(1+ρ), ρ/(1+ρ)]`, `Dba ≤ 0`, i.e. the
Beurling–Ahlfors map with `r = 2` has `K + 1/K ≤ ρ² + ρ⁻²` (separate convexity reduces to the 8 vertices). -/
theorem s17p_ba_core {ρ ξ A B : ℝ} (hρ : 1 ≤ ρ) (hξ1 : 1 / ρ ≤ ξ) (hξ2 : ξ ≤ ρ)
    (hA1 : 1 / (1 + ρ) ≤ A) (hA2 : A ≤ ρ / (1 + ρ)) (hB1 : 1 / (1 + ρ) ≤ B) (hB2 : B ≤ ρ / (1 + ρ)) :
    s17p_Dba ρ ξ A B ≤ 0 := by
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 ≤ t ∧ ρ = 1 + t := ⟨ρ - 1, by linarith, by ring⟩
  have hρ0 : (0 : ℝ) < 1 + t := by linarith
  have hvx : ∀ A' B' : ℝ, (A' = 1 / (1 + (1 + t)) ∨ A' = (1 + t) / (1 + (1 + t))) →
      (B' = 1 / (1 + (1 + t)) ∨ B' = (1 + t) / (1 + (1 + t))) → s17p_Dba (1 + t) ξ A' B' ≤ 0 := by
    intro A' B' hA' hB'
    refine (s17p_step_xi hρ0 hξ1 hξ2).trans (max_le ?_ ?_) <;>
      rcases hA' with rfl | rfl <;> rcases hB' with rfl | rfl
    exacts [s17p_v_inv_lo_lo ht, s17p_v_inv_lo_hi ht, s17p_v_inv_hi_lo ht, s17p_v_inv_hi_hi ht,
      s17p_v_rho_lo_lo ht, s17p_v_rho_lo_hi ht, s17p_v_rho_hi_lo ht, s17p_v_rho_hi_hi ht]
  have hvB : ∀ A' : ℝ, (A' = 1 / (1 + (1 + t)) ∨ A' = (1 + t) / (1 + (1 + t))) →
      s17p_Dba (1 + t) ξ A' B ≤ 0 := fun A' hA' =>
    (s17p_step_B hB1 hB2).trans (max_le (hvx A' _ hA' (Or.inl rfl)) (hvx A' _ hA' (Or.inr rfl)))
  exact (s17p_step_A hA1 hA2).trans (max_le (hvB _ (Or.inl rfl)) (hvB _ (Or.inr rfl)))

/-- (17.7) in the raw variables `A₁ = h(x+y)`, `B₁ = h(x-y)`, `C₁ = h(x)`, `I₊ = ∫_x^{x+y} h`, `I₋ = ∫_{x-y}^x h`: under
the quasisymmetry bounds at `x` and the mean-value bounds, the partials of `beurlingAhlfors h 2`
(`u_x`, `u_y`, `v_x`, `v_y`, from `ba_f1_partials` with `v` doubled) satisfy
`ρ²(u_x² + u_y² + v_x² + v_y²) ≤ (ρ⁴ + 1)(u_x v_y - u_y v_x)` and `u_x v_y - u_y v_x > 0`. -/
theorem s17p_alg {ρ y A1 B1 C1 Ip Im : ℝ} (hρ : 1 ≤ ρ) (hy : 0 < y) (hBC : B1 < C1) (hCA : C1 < A1)
    (hq1 : A1 - C1 ≤ ρ * (C1 - B1)) (hq2 : C1 - B1 ≤ ρ * (A1 - C1))
    (hP1 : 1 / (1 + ρ) * (A1 - C1) ≤ Ip / y - C1) (hP2 : Ip / y - C1 ≤ ρ / (1 + ρ) * (A1 - C1))
    (hN1 : 1 / (1 + ρ) * (C1 - B1) ≤ C1 - Im / y) (hN2 : C1 - Im / y ≤ ρ / (1 + ρ) * (C1 - B1)) :
    ρ ^ 2 * (((A1 - B1) / (2 * y)) ^ 2 + ((A1 + B1) / (2 * y) - (Im + Ip) / (2 * y ^ 2)) ^ 2 +
        (2 * ((A1 - 2 * C1 + B1) / (2 * y))) ^ 2 +
        (2 * ((A1 - B1) / (2 * y) - (Ip - Im) / (2 * y ^ 2))) ^ 2) ≤
      (ρ ^ 4 + 1) * ((A1 - B1) / (2 * y) * (2 * ((A1 - B1) / (2 * y) - (Ip - Im) / (2 * y ^ 2))) -
        ((A1 + B1) / (2 * y) - (Im + Ip) / (2 * y ^ 2)) * (2 * ((A1 - 2 * C1 + B1) / (2 * y)))) ∧
    0 < (A1 - B1) / (2 * y) * (2 * ((A1 - B1) / (2 * y) - (Ip - Im) / (2 * y ^ 2))) -
        ((A1 + B1) / (2 * y) - (Im + Ip) / (2 * y ^ 2)) * (2 * ((A1 - 2 * C1 + B1) / (2 * y))) := by
  have ha : 0 < A1 - C1 := sub_pos.2 hCA
  have hb : 0 < C1 - B1 := sub_pos.2 hBC
  have hρ0 : 0 < ρ := by linarith
  have ha0 : A1 - C1 ≠ 0 := ha.ne'
  have hb0 : C1 - B1 ≠ 0 := hb.ne'
  have hy0 : y ≠ 0 := hy.ne'
  -- the normalized variables
  have hξ1 : 1 / ρ ≤ (C1 - B1) / (A1 - C1) := by
    rw [div_le_div_iff₀ hρ0 ha]
    linarith
  have hξ2 : (C1 - B1) / (A1 - C1) ≤ ρ := by
    rw [div_le_iff₀ ha]
    linarith
  have hA1 : 1 / (1 + ρ) ≤ (Ip / y - C1) / (A1 - C1) := by
    rw [le_div_iff₀ ha]
    linarith
  have hA2 : (Ip / y - C1) / (A1 - C1) ≤ ρ / (1 + ρ) := by
    rw [div_le_iff₀ ha]
    linarith
  have hB1 : 1 / (1 + ρ) ≤ (C1 - Im / y) / (C1 - B1) := by
    rw [le_div_iff₀ hb]
    linarith
  have hB2 : (C1 - Im / y) / (C1 - B1) ≤ ρ / (1 + ρ) := by
    rw [div_le_iff₀ hb]
    linarith
  have hcore := s17p_ba_core hρ hξ1 hξ2 hA1 hA2 hB1 hB2
  have hid : s17p_Dba ρ ((C1 - B1) / (A1 - C1)) ((Ip / y - C1) / (A1 - C1)) ((C1 - Im / y) / (C1 - B1)) *
      ((A1 - C1) / y) ^ 2 =
      ρ ^ 2 * (((A1 - B1) / (2 * y)) ^ 2 + ((A1 + B1) / (2 * y) - (Im + Ip) / (2 * y ^ 2)) ^ 2 +
        (2 * ((A1 - 2 * C1 + B1) / (2 * y))) ^ 2 +
        (2 * ((A1 - B1) / (2 * y) - (Ip - Im) / (2 * y ^ 2))) ^ 2) -
      (ρ ^ 4 + 1) * ((A1 - B1) / (2 * y) * (2 * ((A1 - B1) / (2 * y) - (Ip - Im) / (2 * y ^ 2))) -
        ((A1 + B1) / (2 * y) - (Im + Ip) / (2 * y ^ 2)) * (2 * ((A1 - 2 * C1 + B1) / (2 * y)))) := by
    unfold s17p_Dba
    field_simp
    ring
  have hsq : 0 < ((A1 - C1) / y) ^ 2 := by positivity
  have hle := mul_nonpos_of_nonpos_of_nonneg hcore hsq.le
  rw [hid] at hle
  have hux : 0 < (A1 - B1) / (2 * y) := div_pos (by linarith) (by positivity)
  have hS : 0 < ρ ^ 2 * (((A1 - B1) / (2 * y)) ^ 2 + ((A1 + B1) / (2 * y) - (Im + Ip) / (2 * y ^ 2)) ^ 2 +
        (2 * ((A1 - 2 * C1 + B1) / (2 * y))) ^ 2 +
        (2 * ((A1 - B1) / (2 * y) - (Ip - Im) / (2 * y ^ 2))) ^ 2) := by positivity
  refine ⟨by linarith, ?_⟩
  by_contra hcon
  push Not at hcon
  have h4 : 0 < ρ ^ 4 + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcon h4.le]

/-- If `|f_z̄| < |f_z|`, `K ≥ 1` and `2K(|f_z|² + |f_z̄|²) ≤ (K² + 1)(|f_z|² - |f_z̄|²)` (i.e. `D + 1/D ≤ K + 1/K`),
then `D_f ≤ K`: the hypothesis is `((K+1)|f_z̄|)² ≤ ((K-1)|f_z|)²`. -/
theorem s17p_dq_le {f : ℂ → ℂ} {z : ℂ} {K : ℝ} (hK : 1 ≤ K) (hlt : ‖dzbar f z‖ < ‖dz f z‖)
    (hle : K * (2 * (‖dz f z‖ ^ 2 + ‖dzbar f z‖ ^ 2)) ≤ (K ^ 2 + 1) * (‖dz f z‖ ^ 2 - ‖dzbar f z‖ ^ 2)) :
    dilatationQuotient f z ≤ K := by
  have hB := norm_nonneg (dzbar f z)
  have hA : 0 < ‖dz f z‖ := hB.trans_lt hlt
  have hAB : 0 < ‖dz f z‖ - ‖dzbar f z‖ := sub_pos.2 hlt
  have hD : dilatationQuotient f z = (‖dz f z‖ + ‖dzbar f z‖) / (‖dz f z‖ - ‖dzbar f z‖) := by
    unfold dilatationQuotient complexDilatation
    rw [norm_div]
    field_simp
  rw [hD, div_le_iff₀ hAB]
  have hsq : ((K + 1) * ‖dzbar f z‖) ^ 2 ≤ ((K - 1) * ‖dz f z‖) ^ 2 := by nlinarith
  have h2 : (K + 1) * ‖dzbar f z‖ ≤ (K - 1) * ‖dz f z‖ :=
    (sq_le_sq₀ (by positivity) (mul_nonneg (by linarith) hA.le)).1 hsq
  nlinarith

/-- Quasisymmetry is invariant under affine changes of variable: if `h` is `ρ`-quasisymmetric, `α > 0` and `γ > 0`,
then so is `t ↦ γ (h(αt + β) - δ)` (its ratio `Δ(x, t)` is `Δ_h(αx + β, αt)`). -/
theorem s17p_qs_affine {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) {α γ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
    (β δ : ℝ) : IsQuasisymmetric (fun t => γ * (h (α * t + β) - δ)) ρ := by
  obtain ⟨hmono, hcont, htop, hbot, hqs⟩ := hh
  have hlin : Tendsto (fun t : ℝ => α * t + β) atTop atTop :=
    tendsto_atTop_add_const_right _ β (tendsto_id.const_mul_atTop hα)
  have hlin' : Tendsto (fun t : ℝ => α * t + β) atBot atBot :=
    tendsto_atBot_add_const_right _ β (tendsto_id.const_mul_atBot hα)
  refine ⟨fun s t hst => ?_, by fun_prop, ?_, ?_, fun x t ht => ?_⟩
  · have h1 : h (α * s + β) < h (α * t + β) := hmono (by nlinarith)
    show γ * (h (α * s + β) - δ) < γ * (h (α * t + β) - δ)
    nlinarith
  · have h1 := tendsto_atTop_add_const_right _ (-δ) (htop.comp hlin)
    refine (h1.const_mul_atTop hγ).congr fun t => ?_
    simp only [Function.comp, sub_eq_add_neg]
  · have h1 := tendsto_atBot_add_const_right _ (-δ) (hbot.comp hlin')
    refine (h1.const_mul_atBot hγ).congr fun t => ?_
    simp only [Function.comp, sub_eq_add_neg]
  · have e : qsRatio (fun t => γ * (h (α * t + β) - δ)) x t = qsRatio h (α * x + β) (α * t) := by
      simp only [qsRatio]
      rw [show α * (x + t) + β = α * x + β + α * t by ring, show α * (x - t) + β = α * x + β - α * t by ring]
      rw [show γ * (h (α * x + β + α * t) - δ) - γ * (h (α * x + β) - δ) =
          γ * (h (α * x + β + α * t) - h (α * x + β)) by ring,
        show γ * (h (α * x + β) - δ) - γ * (h (α * x + β - α * t) - δ) =
          γ * (h (α * x + β) - h (α * x + β - α * t)) by ring,
        mul_div_mul_left _ _ hγ.ne']
    rw [e]
    exact hqs _ _ (mul_pos hα ht)

/-- If `h` is `ρ`-quasisymmetric, so is `s ↦ -h(-s)` (its ratio `Δ(x, t)` is `1/Δ_h(-x, t)`). -/
theorem s17p_qs_reflect {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) :
    IsQuasisymmetric (fun s => -h (-s)) ρ := by
  have hρ := ba_f2h_rho_pos hh
  obtain ⟨hmono, hcont, htop, hbot, hqs⟩ := hh
  refine ⟨fun s t hst => neg_lt_neg (hmono (neg_lt_neg hst)), by fun_prop,
    tendsto_neg_atBot_atTop.comp (hbot.comp tendsto_neg_atTop_atBot),
    tendsto_neg_atTop_atBot.comp (htop.comp tendsto_neg_atBot_atTop), fun x t ht => ?_⟩
  obtain ⟨h1, h2⟩ := hqs (-x) t ht
  have hA : 0 < h (-x + t) - h (-x) := sub_pos.2 (hmono (by linarith))
  have hB : 0 < h (-x) - h (-x - t) := sub_pos.2 (hmono (by linarith))
  have e : qsRatio (fun s => -h (-s)) x t = (qsRatio h (-x) t)⁻¹ := by
    simp only [qsRatio]
    rw [show -(x + t) = -x - t by ring, show -(x - t) = -x + t by ring, inv_div]
    congr 1 <;> ring
  rw [e]
  have hq : 0 < qsRatio h (-x) t := div_pos hA hB
  refine ⟨inv_anti₀ hq h2, ?_⟩
  calc (qsRatio h (-x) t)⁻¹ ≤ (ρ⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 hρ) h1
    _ = ρ := inv_inv ρ

/-- (17.13), proved here ahead of (17.7), which uses it (the book statement `eq17_13` below is a one-line wrapper): a
`ρ`-quasisymmetric `h` with `h(0) = 0`, `h(1) = 1` satisfies `1/(1+ρ) ≤ h(1/2) ≤ ρ/(1+ρ)` (quasisymmetry at
`x = t = 1/2`). -/
theorem s17p_half_bounds {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) (h0 : h 0 = 0) (h1 : h 1 = 1) :
    1 / (1 + ρ) ≤ h (1 / 2) ∧ h (1 / 2) ≤ ρ / (1 + ρ) := by
  obtain ⟨hmono, -, -, -, hqs⟩ := hh
  obtain ⟨hlow, hhigh⟩ := hqs (1 / 2) (1 / 2) (by norm_num)
  simp only [qsRatio] at hlow hhigh
  norm_num [h0, h1] at hlow hhigh
  have hu0 : 0 < h (1 / 2) := by
    have := hmono (show (0 : ℝ) < 1 / 2 by norm_num)
    rwa [h0] at this
  have hu1 : h (1 / 2) < 1 := by
    have := hmono (show (1 : ℝ) / 2 < 1 by norm_num)
    rwa [h1] at this
  have hρ : 0 < ρ := lt_of_lt_of_le (div_pos (by linarith) hu0) hhigh
  have hden : (0 : ℝ) < 1 + ρ := by linarith
  constructor
  · rw [div_le_iff₀ hu0] at hhigh
    rw [div_le_iff₀ hden]
    linarith
  · rw [le_div_iff₀ hu0] at hlow
    have hmul := mul_le_mul_of_nonneg_left hlow hρ.le
    rw [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul] at hmul
    rw [le_div_iff₀ hden]
    linarith

/-- The dyadic splitting of the mean: for a `ρ`-quasisymmetric `g` with `g 0 = 0`, `g 1 = 1` and `θ = g(1/2)`,
`∫₀¹ g = (θ m₁ + (1 - θ) m₂ + θ)/2`, where `m₁ = ∫₀¹ g₁`, `m₂ = ∫₀¹ g₂` for the normalized `ρ`-quasisymmetric maps
`g₁(t) = g(t/2)/θ` and `g₂(t) = (g((t+1)/2) - θ)/(1 - θ)`. -/
theorem s17p_mean_split {g : ℝ → ℝ} {ρ : ℝ} (hg : IsQuasisymmetric g ρ) (h0 : g 0 = 0) (h1 : g 1 = 1) :
    ∃ g₁ g₂ : ℝ → ℝ, (IsQuasisymmetric g₁ ρ ∧ g₁ 0 = 0 ∧ g₁ 1 = 1) ∧
      (IsQuasisymmetric g₂ ρ ∧ g₂ 0 = 0 ∧ g₂ 1 = 1) ∧
      ∫ t in (0 : ℝ)..1, g t =
        (g (1 / 2) * (∫ t in (0 : ℝ)..1, g₁ t) + (1 - g (1 / 2)) * (∫ t in (0 : ℝ)..1, g₂ t) + g (1 / 2)) / 2 := by
  have hθ0 : 0 < g (1 / 2) := by
    rw [← h0]
    exact hg.1 (by norm_num)
  have hθ1 : g (1 / 2) < 1 := by
    have h2 := hg.1 (show (1 / 2 : ℝ) < 1 by norm_num)
    rwa [h1] at h2
  have hc := hg.2.1
  have hθ0' : g (1 / 2) ≠ 0 := hθ0.ne'
  have hθ1' : 1 - g (1 / 2) ≠ 0 := (sub_pos.2 hθ1).ne'
  refine ⟨fun t => (g (1 / 2))⁻¹ * (g ((1 / 2) * t + 0) - 0),
    fun t => (1 - g (1 / 2))⁻¹ * (g ((1 / 2) * t + 1 / 2) - g (1 / 2)),
    ⟨s17p_qs_affine hg (by norm_num) (inv_pos.2 hθ0) 0 0, ?_, ?_⟩,
    ⟨s17p_qs_affine hg (by norm_num) (inv_pos.2 (sub_pos.2 hθ1)) (1 / 2) (g (1 / 2)), ?_, ?_⟩, ?_⟩
  · simp [h0]
  · show (g (1 / 2))⁻¹ * (g ((1 / 2) * 1 + 0) - 0) = 1
    rw [show (1 / 2 : ℝ) * 1 + 0 = 1 / 2 by norm_num, sub_zero, inv_mul_cancel₀ hθ0']
  · show (1 - g (1 / 2))⁻¹ * (g ((1 / 2) * 0 + 1 / 2) - g (1 / 2)) = 0
    rw [show (1 / 2 : ℝ) * 0 + 1 / 2 = 1 / 2 by norm_num, sub_self, mul_zero]
  · show (1 - g (1 / 2))⁻¹ * (g ((1 / 2) * 1 + 1 / 2) - g (1 / 2)) = 1
    rw [show (1 / 2 : ℝ) * 1 + 1 / 2 = 1 by norm_num, h1, inv_mul_cancel₀ hθ1']
  · have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (μ := volume) 0 (1 / 2)) (hc.intervalIntegrable (1 / 2) 1)
    have I1 : ∫ t in (0 : ℝ)..1, (g (1 / 2))⁻¹ * (g ((1 / 2) * t + 0) - 0) =
        (g (1 / 2))⁻¹ * (2 * ∫ t in (0 : ℝ)..(1 / 2), g t) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      simp only [sub_zero]
      rw [intervalIntegral.integral_comp_mul_add g (by norm_num : (1 / 2 : ℝ) ≠ 0) 0]
      norm_num
    have I2 : ∫ t in (0 : ℝ)..1, (1 - g (1 / 2))⁻¹ * (g ((1 / 2) * t + 1 / 2) - g (1 / 2)) =
        (1 - g (1 / 2))⁻¹ * (2 * (∫ t in (1 / 2 : ℝ)..1, g t) - g (1 / 2)) := by
      have hI : IntervalIntegrable (fun t : ℝ => g ((1 / 2) * t + 1 / 2)) volume 0 1 :=
        (by fun_prop : Continuous fun t : ℝ => g ((1 / 2) * t + 1 / 2)).intervalIntegrable 0 1
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [intervalIntegral.integral_sub hI intervalIntegrable_const,
        intervalIntegral.integral_comp_mul_add g (by norm_num : (1 / 2 : ℝ) ≠ 0) (1 / 2)]
      norm_num
    rw [I1, I2, ← hsplit]
    field_simp
    ring

/-- **The Beurling–Ahlfors mean-value bound** (sharp form of (17.13) for means): a `ρ`-quasisymmetric `g` with
`g 0 = 0`, `g 1 = 1` has `1/(1+ρ) ≤ ∫₀¹ g ≤ ρ/(1+ρ)`.  The supremum `M` and the infimum `m` of `∫₀¹ k` over all such
`k` satisfy `M ≤ (M + ρ/(1+ρ))/2` and `m ≥ (m + 1/(1+ρ))/2` by `s17p_mean_split` and (17.13) (`s17p_half_bounds`). -/
theorem s17p_mean_bound {g : ℝ → ℝ} {ρ : ℝ} (hg : IsQuasisymmetric g ρ) (h0 : g 0 = 0) (h1 : g 1 = 1) :
    1 / (1 + ρ) ≤ ∫ t in (0 : ℝ)..1, g t ∧ ∫ t in (0 : ℝ)..1, g t ≤ ρ / (1 + ρ) := by
  have hρ := ba_f2h_rho_pos hg
  set S : Set ℝ := {m | ∃ k : ℝ → ℝ, IsQuasisymmetric k ρ ∧ k 0 = 0 ∧ k 1 = 1 ∧ m = ∫ t in (0 : ℝ)..1, k t}
    with hS
  have hmem : (∫ t in (0 : ℝ)..1, g t) ∈ S := ⟨g, hg, h0, h1, rfl⟩
  have hbd : ∀ m ∈ S, 0 ≤ m ∧ m ≤ 1 := by
    rintro m ⟨k, hk, hk0, hk1, rfl⟩
    have hle : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ k t ∧ k t ≤ 1 := fun t ht =>
      ⟨by rw [← hk0]; exact hk.1.monotone ht.1, by rw [← hk1]; exact hk.1.monotone ht.2⟩
    refine ⟨intervalIntegral.integral_nonneg zero_le_one fun t ht => (hle t ht).1, ?_⟩
    have := intervalIntegral.integral_mono_on zero_le_one (hk.2.1.intervalIntegrable 0 1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1) fun t ht => (hle t ht).2
    simpa using this
  have hne : S.Nonempty := ⟨_, hmem⟩
  have hup : BddAbove S := ⟨1, fun m hm => (hbd m hm).2⟩
  have hlo : BddBelow S := ⟨0, fun m hm => (hbd m hm).1⟩
  have hsplit : ∀ m ∈ S, ∃ θ m₁ m₂ : ℝ, m₁ ∈ S ∧ m₂ ∈ S ∧ 1 / (1 + ρ) ≤ θ ∧ θ ≤ ρ / (1 + ρ) ∧
      m = (θ * m₁ + (1 - θ) * m₂ + θ) / 2 := by
    rintro m ⟨k, hk, hk0, hk1, rfl⟩
    obtain ⟨g₁, g₂, ⟨hg₁, hg₁0, hg₁1⟩, ⟨hg₂, hg₂0, hg₂1⟩, heq⟩ := s17p_mean_split hk hk0 hk1
    obtain ⟨hθ1, hθ2⟩ := s17p_half_bounds hk hk0 hk1
    exact ⟨k (1 / 2), _, _, ⟨g₁, hg₁, hg₁0, hg₁1, rfl⟩, ⟨g₂, hg₂, hg₂0, hg₂1, rfl⟩, hθ1, hθ2, heq⟩
  have hc1 : ρ / (1 + ρ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hd0 : 0 ≤ 1 / (1 + ρ) := by positivity
  have hM : sSup S ≤ ρ / (1 + ρ) := by
    have key : sSup S ≤ (sSup S + ρ / (1 + ρ)) / 2 := csSup_le hne fun m hm => by
      obtain ⟨θ, m₁, m₂, hm₁, hm₂, hθ1, hθ2, rfl⟩ := hsplit m hm
      have e1 := le_csSup hup hm₁
      have e2 := le_csSup hup hm₂
      nlinarith [mul_le_mul_of_nonneg_left e1 (hd0.trans hθ1), mul_le_mul_of_nonneg_left e2
        (show 0 ≤ 1 - θ by linarith)]
    linarith
  have hm : 1 / (1 + ρ) ≤ sInf S := by
    have key : (sInf S + 1 / (1 + ρ)) / 2 ≤ sInf S := le_csInf hne fun m hm => by
      obtain ⟨θ, m₁, m₂, hm₁, hm₂, hθ1, hθ2, rfl⟩ := hsplit m hm
      have e1 := csInf_le hlo hm₁
      have e2 := csInf_le hlo hm₂
      nlinarith [mul_le_mul_of_nonneg_left e1 (hd0.trans hθ1), mul_le_mul_of_nonneg_left e2
        (show 0 ≤ 1 - θ by linarith)]
    linarith
  exact ⟨hm.trans (csInf_le hlo hmem), (le_csSup hup hmem).trans hM⟩

/-- The right-hand mean-value bound: for `ρ`-quasisymmetric `h` and `y > 0`,
`(h(x+y) - h(x))/(1+ρ) ≤ (1/y)∫_x^{x+y} h - h(x) ≤ ρ(h(x+y) - h(x))/(1+ρ)`. -/
theorem s17p_mean_plus {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    1 / (1 + ρ) * (h (x + y) - h x) ≤ (∫ t in x..(x + y), h t) / y - h x ∧
      (∫ t in x..(x + y), h t) / y - h x ≤ ρ / (1 + ρ) * (h (x + y) - h x) := by
  have ha : 0 < h (x + y) - h x := sub_pos.2 (hh.1 (by linarith))
  have hg := s17p_qs_affine hh hy (inv_pos.2 ha) x (h x)
  have e : (fun t => (h (x + y) - h x)⁻¹ * (h (y * t + x) - h x)) =
      fun t => (h (x + y) - h x)⁻¹ * (h (x + t * y) - h x) := by
    funext t
    rw [show y * t + x = x + t * y by ring]
  rw [e] at hg
  have hg0 : (h (x + y) - h x)⁻¹ * (h (x + 0 * y) - h x) = 0 := by simp
  have hg1 : (h (x + y) - h x)⁻¹ * (h (x + 1 * y) - h x) = 1 := by
    rw [one_mul]
    exact inv_mul_cancel₀ ha.ne'
  obtain ⟨b1, b2⟩ := s17p_mean_bound hg hg0 hg1
  have hint : ∫ t in (0 : ℝ)..1, (h (x + y) - h x)⁻¹ * (h (x + t * y) - h x) =
      (h (x + y) - h x)⁻¹ * ((∫ t in x..(x + y), h t) / y - h x) := by
    have hc := hh.2.1
    have hI : IntervalIntegrable (fun t : ℝ => h (x + t * y)) volume 0 1 :=
      (by fun_prop : Continuous fun t : ℝ => h (x + t * y)).intervalIntegrable 0 1
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hI intervalIntegrable_const,
      ba_f1h_int_plus hc x hy.ne', ba_f1h_prim_sub hc]
    simp
  rw [hint] at b1 b2
  have c1 := mul_le_mul_of_nonneg_left b1 ha.le
  have c2 := mul_le_mul_of_nonneg_left b2 ha.le
  rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at c1 c2
  constructor <;> linarith

/-- The left-hand mean-value bound: for `ρ`-quasisymmetric `h` and `y > 0`,
`(h(x) - h(x-y))/(1+ρ) ≤ h(x) - (1/y)∫_{x-y}^x h ≤ ρ(h(x) - h(x-y))/(1+ρ)` (apply `s17p_mean_bound` to the
normalized reflection `t ↦ (h(x) - h(x - ty))/(h(x) - h(x-y))`). -/
theorem s17p_mean_minus {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    1 / (1 + ρ) * (h x - h (x - y)) ≤ h x - (∫ t in (x - y)..x, h t) / y ∧
      h x - (∫ t in (x - y)..x, h t) / y ≤ ρ / (1 + ρ) * (h x - h (x - y)) := by
  have hb : 0 < h x - h (x - y) := sub_pos.2 (hh.1 (by linarith))
  have hg := s17p_qs_affine (s17p_qs_reflect hh) hy (inv_pos.2 hb) (-x) (-h x)
  have e : (fun t => (h x - h (x - y))⁻¹ * ((fun s => -h (-s)) (y * t + -x) - -h x)) =
      fun t => (h x - h (x - y))⁻¹ * (h x - h (x - t * y)) := by
    funext t
    beta_reduce
    rw [show -(y * t + -x) = x - t * y by ring]
    ring
  rw [e] at hg
  have hg0 : (h x - h (x - y))⁻¹ * (h x - h (x - 0 * y)) = 0 := by simp
  have hg1 : (h x - h (x - y))⁻¹ * (h x - h (x - 1 * y)) = 1 := by
    rw [one_mul]
    exact inv_mul_cancel₀ hb.ne'
  obtain ⟨b1, b2⟩ := s17p_mean_bound hg hg0 hg1
  have hint : ∫ t in (0 : ℝ)..1, (h x - h (x - y))⁻¹ * (h x - h (x - t * y)) =
      (h x - h (x - y))⁻¹ * (h x - (∫ t in (x - y)..x, h t) / y) := by
    have hc := hh.2.1
    have hI : IntervalIntegrable (fun t : ℝ => h (x - t * y)) volume 0 1 :=
      (by fun_prop : Continuous fun t : ℝ => h (x - t * y)).intervalIntegrable 0 1
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub intervalIntegrable_const hI,
      ba_f1h_int_minus hc x hy.ne', ba_f1h_prim_sub hc]
    simp
  rw [hint] at b1 b2
  have c1 := mul_le_mul_of_nonneg_left b1 hb.le
  have c2 := mul_le_mul_of_nonneg_left b2 hb.le
  rw [← mul_assoc, mul_inv_cancel₀ hb.ne', one_mul] at c1 c2
  constructor <;> linarith

/-- The real-linear stretch `S₂ w = w + (Im w) i = Re w + 2i Im w`; `beurlingAhlfors h 2 = S₂ ∘ beurlingAhlfors h 1`. -/
def s17p_stretch : ℂ →L[ℝ] ℂ := ContinuousLinearMap.id ℝ ℂ + imCLM.smulRight I

/-- `Re (S₂ w) = Re w` and `Im (S₂ w) = 2 Im w`. -/
theorem s17p_stretch_re_im (w : ℂ) : (s17p_stretch w).re = w.re ∧ (s17p_stretch w).im = 2 * w.im := by
  refine ⟨by simp [s17p_stretch], ?_⟩
  simp [s17p_stretch, Complex.real_smul]
  ring

/-- `S₂ (u + v i) = u + (2v) i` for real `u`, `v`. -/
theorem s17p_stretch_mk (u v : ℝ) : s17p_stretch ((u : ℂ) + (v : ℂ) * I) = (u : ℂ) + ((2 * v : ℝ) : ℂ) * I := by
  apply Complex.ext
  · rw [(s17p_stretch_re_im _).1]
    simp
  · rw [(s17p_stretch_re_im _).2]
    simp

/-- `|w| ≤ |S₂ w|`. -/
theorem s17p_norm_le_stretch (w : ℂ) : ‖w‖ ≤ ‖s17p_stretch w‖ := by
  have h1 : ‖w‖ ^ 2 ≤ ‖s17p_stretch w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply,
      (s17p_stretch_re_im w).1, (s17p_stretch_re_im w).2]
    nlinarith [sq_nonneg w.im]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

/-- The Beurling–Ahlfors extension with `r = 2` is the stretch of the one with `r = 1`:
`beurlingAhlfors h 2 z = S₂ (beurlingAhlfors h 1 z)`. -/
theorem s17p_ba2_apply (h : ℝ → ℝ) (z : ℂ) :
    beurlingAhlfors h 2 z = s17p_stretch (beurlingAhlfors h 1 z) := by
  apply Complex.ext
  · rw [(s17p_stretch_re_im _).1]
    simp [beurlingAhlfors]
  · rw [(s17p_stretch_re_im _).2]
    simp [beurlingAhlfors]

/-- The pointwise dilatation bound for `beurlingAhlfors h 2` (`ρ`-quasisymmetric `h`): at every `z ∈ ℍ`,
`J > 0`, `|f_z̄| < |f_z|` and `D_f ≤ ρ²` (the partials are those of `ba_f1_partials` with `v` doubled; then
`s17p_alg` and `s17p_dq_le`). -/
theorem s17p_ba2_pointwise {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) {z : ℂ} (hz : z ∈ upperHalf) :
    0 < jacobian (beurlingAhlfors h 2) z ∧ ‖dzbar (beurlingAhlfors h 2) z‖ < ‖dz (beurlingAhlfors h 2) z‖ ∧
      dilatationQuotient (beurlingAhlfors h 2) z ≤ ρ ^ 2 := by
  have hy : 0 < z.im := hz
  have hρ := ba_one_le_rho hh
  have hcont := hh.2.1
  obtain ⟨hfx, hfy⟩ := ba_f1_partials hcont hz
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable (z.re - z.im) z.re)
    (hcont.intervalIntegrable z.re (z.re + z.im))] at hfy
  have hdiff : DifferentiableAt ℝ (beurlingAhlfors h 1) z :=
    ((ba_f1h_contDiffOn hcont).contDiffAt (isOpen_upperHalf.mem_nhds hz)).differentiableAt one_ne_zero
  have hfun : beurlingAhlfors h 2 = fun w => s17p_stretch (beurlingAhlfors h 1 w) :=
    funext fun w => s17p_ba2_apply h w
  have hD : fderiv ℝ (beurlingAhlfors h 2) z = s17p_stretch.comp (fderiv ℝ (beurlingAhlfors h 1) z) := by
    rw [hfun]
    exact (s17p_stretch.hasFDerivAt.comp z hdiff.hasFDerivAt).fderiv
  have hfx3 : fderiv ℝ (beurlingAhlfors h 2) z 1 = s17p_stretch (fderiv ℝ (beurlingAhlfors h 1) z 1) := by
    rw [hD]
    rfl
  have hfy3 : fderiv ℝ (beurlingAhlfors h 2) z I = s17p_stretch (fderiv ℝ (beurlingAhlfors h 1) z I) := by
    rw [hD]
    rfl
  rw [hfx, s17p_stretch_mk] at hfx3
  rw [hfy, s17p_stretch_mk] at hfy3
  obtain ⟨hJ, hS⟩ := ba_f2h_wirtinger hfx3 hfy3
  obtain ⟨hq1, hq2⟩ := ba_f2h_qs_mul hh z.re hy
  obtain ⟨hP1, hP2⟩ := s17p_mean_plus hh z.re hy
  obtain ⟨hN1, hN2⟩ := s17p_mean_minus hh z.re hy
  obtain ⟨hkey, hJpos⟩ := s17p_alg hρ hy (hh.1 (by linarith)) (hh.1 (by linarith)) hq1 hq2 hP1 hP2 hN1 hN2
  have hJ0 : 0 < jacobian (beurlingAhlfors h 2) z := by
    rw [jacobian, hJ]
    exact hJpos
  have hlt : ‖dzbar (beurlingAhlfors h 2) z‖ < ‖dz (beurlingAhlfors h 2) z‖ := by
    have h2 : ‖dzbar (beurlingAhlfors h 2) z‖ ^ 2 < ‖dz (beurlingAhlfors h 2) z‖ ^ 2 := by
      rw [jacobian] at hJ0
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h2
  refine ⟨hJ0, hlt, s17p_dq_le (by nlinarith) hlt ?_⟩
  rw [hJ, hS, show (ρ ^ 2) ^ 2 = ρ ^ 4 by ring]
  linarith

/-- **(17.7), uniform form** (non-book lemma recording what is actually proved): for every `ρ`-quasisymmetric `h`,
the Beurling–Ahlfors extension with `r = 2` is a `ρ²`-q.c. self-map of `ℍ` with boundary values `h`. -/
theorem s17p_beurlingAhlfors_two {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) :
    HasQCExtensionH h (beurlingAhlfors h 2) (ρ ^ 2) := by
  have hcont := hh.2.1
  have hfun : beurlingAhlfors h 2 = fun w => s17p_stretch (beurlingAhlfors h 1 w) :=
    funext fun w => s17p_ba2_apply h w
  have hC1 : ContDiffOn ℝ 1 (beurlingAhlfors h 2) upperHalf := by
    rw [hfun]
    exact s17p_stretch.contDiff.comp_contDiffOn (ba_f1h_contDiffOn hcont)
  have hcont2 : Continuous (beurlingAhlfors h 2) := ba_f1h_continuous hcont 2
  have hJ : ∀ z ∈ upperHalf, 0 < jacobian (beurlingAhlfors h 2) z := fun z hz => (s17p_ba2_pointwise hh hz).1
  have hbd : ∀ x : ℝ, beurlingAhlfors h 2 x = h x := fun x => by
    rw [s17p_ba2_apply, ba_f1h_real, show (h x : ℂ) = (h x : ℂ) + ((0 : ℝ) : ℂ) * I by simp, s17p_stretch_mk]
    simp
  have hmaps : MapsTo (beurlingAhlfors h 2) upperHalf upperHalf := fun z hz => by
    have h1 : 0 < (beurlingAhlfors h 1 z).im := (ba_f1_basic hh.1 hcont).2.2.2 hz
    show 0 < (beurlingAhlfors h 2 z).im
    rw [s17p_ba2_apply, (s17p_stretch_re_im _).2]
    linarith
  have hinf : Tendsto (beurlingAhlfors h 2) (cocompact ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (cocompact ℂ) := by
    have h1 := ba_f3_tendsto hh.1 hcont hh.2.2.1 hh.2.2.2.1
    rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded] at h1 ⊢
    refine tendsto_atTop_mono (fun z => ?_) h1
    rw [s17p_ba2_apply]
    exact s17p_norm_le_stretch _
  obtain ⟨himg, G, hG, hGinf, hGx⟩ := ba_homeo_package hC1 hJ hcont2.continuousOn hmaps hbd hh.1 hinf
  refine ⟨?_, himg, G, hG, hGinf, hGx⟩
  have hHsub : upperHalf ⊆ {z : ℂ | 0 ≤ z.im} := fun z hz => le_of_lt (show (0 : ℝ) < z.im from hz)
  have hreal : ∀ x : ℝ, (beurlingAhlfors h 2 x).im = 0 := fun x => by
    rw [hbd x]
    simp
  have hhom := ba_homeomorph_upperHalf_of_contDiff hC1 hJ hmaps
    (hinf.mono_left (inf_le_inf_left _ (principal_mono.2 hHsub)))
    (ba_bdry_of_continuousWithinAt (fun x => hcont2.continuousAt.continuousWithinAt) hreal)
  have hhom' : IsHomeomorphOnto (beurlingAhlfors h 2) upperHalf (beurlingAhlfors h 2 '' upperHalf) := by
    rw [himg]
    exact hhom
  have hρ := ba_one_le_rho hh
  refine isKQC_of_isC1Quasiconformal ⟨isOpen_upperHalf, by nlinarith, hC1, hhom', fun z hz => ?_⟩
  exact ⟨(s17p_ba2_pointwise hh hz).2.1, (s17p_ba2_pointwise hh hz).2.2⟩

/-- (17.7): with a suitable choice of the parameter `r`, the Beurling–Ahlfors extension satisfies
`K ≤ ρ²`. -/
theorem eq17_7 {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) :
    ∃ r : ℝ, 0 < r ∧ HasQCExtensionH h (beurlingAhlfors h r) (ρ ^ 2) := by
  exact ⟨2, two_pos, s17p_beurlingAhlfors_two hh⟩

/-- (17.13): a `ρ`-quasisymmetric `h` normalized by `h(0) = 0`, `h(1) = 1` satisfies
`1/(1+ρ) ≤ h(1/2) ≤ ρ/(1+ρ)`. -/
theorem eq17_13 {h : ℝ → ℝ} {ρ : ℝ} (hh : IsQuasisymmetric h ρ) (h0 : h 0 = 0) (h1 : h 1 = 1) :
    1 / (1 + ρ) ≤ h (1 / 2) ∧ h (1 / 2) ≤ ρ / (1 + ρ) := by
  exact s17p_half_bounds hh h0 h1

/-- (17.20): the Beurling–Ahlfors extension `f` is quasi-isometric for the Poincaré metric of `ℍ`:
`|df(z)|/Im f(z) ≤ C |dz|/Im z` with `C` depending only on `ρ`. -/
theorem eq17_20_quasi_isometry {ρ : ℝ} (hρ : 1 ≤ ρ) :
    ∃ C : ℝ, ∀ h : ℝ → ℝ, IsQuasisymmetric h ρ → ∀ z ∈ upperHalf,
      ‖fderiv ℝ (beurlingAhlfors h 1) z‖ / (beurlingAhlfors h 1 z).im ≤ C / z.im := by
  exact ⟨Real.sqrt (128 * ρ ^ 2 * (ρ + 1) ^ 3), fun h hh z hz => ba_qi_bound hρ hh hz⟩

/-- Corollary of Theorems 16.3, 17.1 and 17.2: `h` is the boundary value of a q.c. self-map of `ℍ`
iff it is quasisymmetric. -/
theorem hasQCExtension_iff_quasisymmetric {h : ℝ → ℝ} (hh : StrictMono h) (hc : Continuous h)
    (htop : Tendsto h atTop atTop) (hbot : Tendsto h atBot atBot) :
    (∃ (g : ℂ → ℂ) (K : ℝ), HasQCExtensionH h g K) ↔ ∃ ρ : ℝ, IsQuasisymmetric h ρ := by
  constructor
  · rintro ⟨g, K, hg⟩
    exact ⟨lambdaInv K, thm17_1_quasisymmetric hg⟩
  · rintro ⟨ρ, hρ⟩
    exact ⟨beurlingAhlfors h 1, 8 * ρ * (ρ + 1),
      (thm17_2_beurling_ahlfors ⟨hh, hc, htop, hbot, hρ.2.2.2.2⟩).2⟩

/-- Corollary (§17.2): a Jordan curve through `∞` is a quasicircle iff the homeomorphism of `ℝ`
induced by the conformal maps of its two complementary components onto `ℍ` and `𝕃` is
quasisymmetric. -/
theorem quasicircle_iff_welding_quasisymmetric {C : Set ExtPlane} {A₁ A₂ : Set ℂ} (hinf : extInf ∈ C)
    (hC : AreComplementaryComponents C (toExt A₁) (toExt A₂)) {φ ψ : ℂ → ℂ}
    {Φ Ψ : ExtPlane → ExtPlane} (hφ : IsConformalOnto φ A₁ upperHalf)
    (hψ : IsConformalOnto ψ A₂ lowerHalf) (hΦ : IsHomeoExtension φ A₁ upperHalf Φ)
    (hΨ : IsHomeoExtension ψ A₂ lowerHalf Ψ) (hΦinf : Φ extInf = extInf) (hΨinf : Ψ extInf = extInf)
    {h : ℝ → ℝ} (hh : ∀ z : ℂ, (z : ExtPlane) ∈ C →
      ∃ x : ℝ, Φ z = ((x : ℂ) : ExtPlane) ∧ Ψ z = (((h x : ℝ) : ℂ) : ExtPlane)) :
    IsQuasicircle C ↔ ∃ ρ : ℝ, IsQuasisymmetric h ρ := by
  constructor
  · intro hq
    obtain ⟨g, G, K, hg, hgs, hG, hGinf, hGx⟩ := wd_forward hinf hC hφ hψ hΦ hΨ hΦinf hΨinf hh hq
    exact ⟨lambdaInv K, thm17_1_quasisymmetric ⟨hg, hgs, G, hG, hGinf, hGx⟩⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨-, hK, hs, G, hG, -, hGx⟩ := thm17_2_beurling_ahlfors hρ
    exact (thm16_3_welding hinf hC hφ hψ hΦ hΨ hΦinf hΨinf hh).2 ⟨_, G, _, hK, hs, hG, hGx⟩

end LiZhongQC
