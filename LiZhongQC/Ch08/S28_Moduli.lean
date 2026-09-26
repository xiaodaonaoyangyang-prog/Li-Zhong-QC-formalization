import LiZhongQC.Ch07.S27_TeichmullerExistence

/-!
# §28 Riemann 曲面的模问题 — The moduli problem for Riemann surfaces

* §28.1 moduli of tori `ℂ/Λ`: `ℂ/Λ ≅ ℂ/Λ'` iff `τ = (ατ' + β)/(γτ' + δ)` with an integer matrix
  of determinant `1`; the modular group `M` and its fundamental domain `D`; `R₁ ↔ ℍ/M`
                                                   — `torus_conformal_iff`, `modularGroupSL2Z`
* the moduli space `R_g` of closed surfaces of genus `g` and the map `T(S₀) → R_g`
                                                   — `ModuliSpace`, `LiesOver`
* §28.2 the modular group `Mod(S₀)`: `σ* : [S, f] ↦ [S, f ∘ σ]`, dependence on the homotopy class
  only, `Mod_g ≅` mapping class group for `g > 2`; (28.1) `R_g = T(S₀)/Mod(S₀)`
                                                   — `ModTransform`, `ModAction`, `eq28_1`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

/-! ## §28.1 Moduli of tori -/

/-- `X` is a torus with periods `(1, τ)`, `Im τ > 0`: a closed Riemann surface with a holomorphic
covering `p : ℂ → X` whose fibres are the cosets of the lattice `Λ = ℤ + ℤτ`. -/
def IsTorusWithPeriod {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] (τ : ℂ) (p : ℂ → X) : Prop :=
  0 < τ.im ∧ IsCoveringMap p ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p ∧ Function.Surjective p ∧
    ∀ z w, p z = p w ↔ ∃ n m : ℤ, z - w = n + m * τ

/-! ### Torus track interface (coordinator 553e2d): lifts of torus maps -/

/-- **A** (covering lift): a continuous map `g : ℂ → X` lifts through a surjective covering `p : ℂ → X` (`ℂ` is
simply connected and locally path connected). -/
theorem tor_exists_lift {X : Type*} [TopologicalSpace X] {p : ℂ → X} (hpc : IsCoveringMap p)
    (hps : Function.Surjective p) {g : ℂ → X} (hg : Continuous g) :
    ∃ F : ℂ → ℂ, Continuous F ∧ ∀ z, p (F z) = g z := by
  obtain ⟨e₀, he₀⟩ := hps (g 0)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := hpc.existsUnique_continuousMap_lifts ⟨g, hg⟩ 0 e₀ he₀
  exact ⟨F, F.continuous, fun z => congrFun hF z⟩

/-- **H, chart transfer**: if `q : ℂ → X` is holomorphic at `u` (a Riemann surface `X` with a holomorphic atlas) and
`q u` lies in the source of the chart `φ` at an arbitrary point `x`, then `φ ∘ q` is complex differentiable at `u`.
The chart at `q u` need not be `φ`: the holomorphic atlas makes the choice of target chart irrelevant
(`mdifferentiableAt_iff_target_of_mem_source`). -/
theorem tor_h_differentiableAt_chart_comp {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {q : ℂ → X} {u : ℂ} (hq : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) q u) {x : X}
    (hx : q u ∈ (chartAt ℂ x).source) : DifferentiableAt ℂ (fun v => chartAt ℂ x (q v)) u := by
  have h := ((mdifferentiableAt_iff_target_of_mem_source hx).1 hq).2
  have h2 : DifferentiableAt ℂ (extChartAt 𝓘(ℂ) x ∘ q) u := h.differentiableAt
  simp only [mfld_simps] at h2
  exact h2

/-- **H, lifting through an injective holomorphic map**: if `h` is holomorphic and injective on an open set `U`,
`ψ` is complex differentiable at `z₀`, and `F` is continuous at `z₀` with `F z₀ ∈ U` and `h ∘ F = ψ` near `z₀`, then
`F` is complex differentiable at `z₀`: `h'(F z₀) ≠ 0` (`deriv_ne_zero_of_injOn`), so `h` has a holomorphic local
inverse `L` near `F z₀`, and `F = L ∘ ψ` near `z₀`. -/
theorem tor_h_differentiableAt_of_comp_eq {h ψ F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U) (hinj : InjOn h U) {z₀ : ℂ} (hFz : F z₀ ∈ U)
    (hF : ContinuousAt F z₀) (hψ : DifferentiableAt ℂ ψ z₀) (hhF : ∀ᶠ z in 𝓝 z₀, h (F z) = ψ z) :
    DifferentiableAt ℂ F z₀ := by
  have hne : deriv h (F z₀) ≠ 0 := deriv_ne_zero_of_injOn hU hh hinj hFz
  have hs : HasStrictDerivAt h (deriv h (F z₀)) (F z₀) :=
    (hh.analyticAt (hU.mem_nhds hFz)).hasStrictDerivAt
  have hL := hs.to_localInverse hne
  have hleft := hs.eventually_left_inverse hne
  have hψz : ψ z₀ = h (F z₀) := hhF.self_of_nhds.symm
  have hLd : DifferentiableAt ℂ (hs.localInverse h (deriv h (F z₀)) (F z₀) hne) (ψ z₀) := by
    rw [hψz]
    exact hL.hasDerivAt.differentiableAt
  refine (hLd.comp z₀ hψ).congr_of_eventuallyEq ?_
  filter_upwards [hF.tendsto.eventually hleft, hhF] with z hz1 hz2
  rw [Function.comp_apply, ← hz2, hz1]

/-- **H** (holomorphy of lifts): if `p : ℂ → X` is a holomorphic covering of a Riemann surface with a holomorphic
atlas, `g : ℂ → X` is holomorphic and `F : ℂ → ℂ` is a continuous lift of `g`, then `F` is entire (near every
point `F = (φ ∘ p)⁻¹ ∘ φ ∘ g` for a chart `φ`, and `φ ∘ p` is holomorphic and injective near `F z`). -/
theorem tor_differentiable_lift {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {p : ℂ → X} (hpc : IsCoveringMap p) (hpd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) {g : ℂ → X}
    (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) {F : ℂ → ℂ} (hF : Continuous F) (hFg : ∀ z, p (F z) = g z) :
    Differentiable ℂ F := by
  intro z₀
  obtain ⟨U₀, hU₀o, hwU₀, hinj₀⟩ := hpc.isLocalHomeomorph.isLocallyInjective (F z₀)
  have hU : IsOpen (U₀ ∩ p ⁻¹' (chartAt ℂ (p (F z₀))).source) :=
    hU₀o.inter ((chartAt ℂ (p (F z₀))).open_source.preimage hpc.continuous)
  have hwU : F z₀ ∈ U₀ ∩ p ⁻¹' (chartAt ℂ (p (F z₀))).source := ⟨hwU₀, mem_chart_source ℂ _⟩
  refine tor_h_differentiableAt_of_comp_eq (h := fun w => chartAt ℂ (p (F z₀)) (p w))
    (ψ := fun z => chartAt ℂ (p (F z₀)) (g z)) hU ?_ ?_ hwU hF.continuousAt ?_
    (Eventually.of_forall fun z => by simp only [hFg])
  · intro w hw
    exact (tor_h_differentiableAt_chart_comp (hpd w) hw.2).differentiableWithinAt
  · intro w₁ hw₁ w₂ hw₂ he
    exact hinj₀ hw₁.1 hw₂.1 ((chartAt ℂ (p (F z₀))).injOn hw₁.2 hw₂.2 he)
  · refine tor_h_differentiableAt_chart_comp (hg z₀) ?_
    rw [← hFg z₀]
    exact mem_chart_source ℂ _

/-- Chart transfer for maps out of `ℂ`: if `p : ℂ → X` is holomorphic at `u` (into a Riemann surface with a
holomorphic atlas) and `p u` lies in the source of the chart at `y`, then `φ_y ∘ p` is complex differentiable at
`u` (the chart `φ_y` is holomorphic on its source since the atlas is holomorphic). -/
theorem tor_d_differentiableAt_chart_comp {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] {p : ℂ → X} {u : ℂ} (hp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) p u) (y : X)
    (hu : p u ∈ (chartAt ℂ y).source) : DifferentiableAt ℂ (fun z => chartAt ℂ y (p z)) u :=
  ((mdifferentiableAt_atlas (chart_mem_atlas ℂ y) hu).comp u hp).differentiableAt

/-- Holomorphic local sections: if `p : ℂ → X` is a holomorphic local homeomorphism into a Riemann surface with
a holomorphic atlas, then for every `u₀` there is a map `s : X → ℂ`, holomorphic at `p u₀`, with `s (p u₀) = u₀`
and `p ∘ s = id` near `p u₀` (`s = (φ ∘ p|_W)⁻¹ ∘ φ` for the chart `φ` at `p u₀` and a neighbourhood `W` of `u₀`
on which `p` is injective; the inverse of the injective holomorphic `φ ∘ p` is holomorphic). -/
theorem tor_d_local_section {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {p : ℂ → X} (hpl : IsLocalHomeomorph p) (hpd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (u₀ : ℂ) :
    ∃ s : X → ℂ, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) s (p u₀) ∧ s (p u₀) = u₀ ∧
      ∀ᶠ y in 𝓝 (p u₀), p (s y) = y := by
  obtain ⟨e, he, hpe⟩ := hpl u₀
  have hpcont : Continuous p := hpl.continuous
  let W : Set ℂ := e.source ∩ p ⁻¹' (chartAt ℂ (p u₀)).source
  have hW : IsOpen W := e.open_source.inter (hpcont.isOpen_preimage _ (chartAt ℂ (p u₀)).open_source)
  let h : ℂ → ℂ := fun z => chartAt ℂ (p u₀) (p z)
  have hhd : DifferentiableOn ℂ h W := fun z hz =>
    (tor_d_differentiableAt_chart_comp (hpd z) (p u₀) hz.2).differentiableWithinAt
  have hinj : InjOn h W := by
    intro a ha b hb hab
    have hab' : p a = p b := (chartAt ℂ (p u₀)).injOn ha.2 hb.2 hab
    rw [hpe] at hab'
    exact e.injOn ha.1 hb.1 hab'
  obtain ⟨hopen, hgd⟩ := RMT.differentiableOn_invFunOn_of_injOn hW hhd hinj
  have hu₀W : u₀ ∈ W := ⟨he, mem_chart_source ℂ (p u₀)⟩
  have hmem : chartAt ℂ (p u₀) (p u₀) ∈ h '' W := ⟨u₀, hu₀W, rfl⟩
  have hgD : DifferentiableAt ℂ (Function.invFunOn h W) (chartAt ℂ (p u₀) (p u₀)) :=
    hgd.differentiableAt (hopen.mem_nhds hmem)
  refine ⟨Function.invFunOn h W ∘ chartAt ℂ (p u₀), ?_, ?_, ?_⟩
  · exact hgD.mdifferentiableAt.comp (p u₀)
      (mdifferentiableAt_atlas (chart_mem_atlas ℂ (p u₀)) (mem_chart_source ℂ (p u₀)))
  · exact hinj.leftInvOn_invFunOn hu₀W
  · have hxt : p u₀ ∈ e.target := by
      rw [hpe]
      exact e.map_source he
    have hnhds : e.target ∩ (chartAt ℂ (p u₀)).source ∈ 𝓝 (p u₀) :=
      (e.open_target.inter (chartAt ℂ (p u₀)).open_source).mem_nhds ⟨hxt, mem_chart_source ℂ (p u₀)⟩
    filter_upwards [hnhds] with y hy
    have h1 : e.symm y ∈ e.source := e.map_target hy.1
    have h2 : p (e.symm y) = y := by
      rw [hpe]
      exact e.right_inv hy.1
    have h3 : e.symm y ∈ W := ⟨h1, by rw [Set.mem_preimage, h2]; exact hy.2⟩
    have h4 : Function.invFunOn h W (chartAt ℂ (p u₀) y) = e.symm y := by
      have h5 : chartAt ℂ (p u₀) y = h (e.symm y) := by
        simp only [h, h2]
      rw [h5]
      exact hinj.leftInvOn_invFunOn h3
    show p (Function.invFunOn h W (chartAt ℂ (p u₀) y)) = y
    rw [h4, h2]

/-- **D** (descent of holomorphy): if `p : ℂ → X` is a surjective holomorphic covering of a Riemann surface with a
holomorphic atlas and `f : X → Y` has `f ∘ p` holomorphic, then `f` is holomorphic (near every point
`f = (f ∘ p) ∘ s` for a local section `s` of `p`, which is holomorphic in charts). -/
theorem tor_mdifferentiable_descend {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace Y] [ChartedSpace ℂ Y] {p : ℂ → X}
    (hpc : IsCoveringMap p) (hpd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p) (hps : Function.Surjective p) {f : X → Y}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∘ p)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  intro x
  obtain ⟨u₀, rfl⟩ := hps x
  obtain ⟨s, hs, hsx, hps'⟩ := tor_d_local_section hpc.isLocalHomeomorph hpd u₀
  have h1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ((f ∘ p) ∘ s) (p u₀) := by
    refine MDifferentiableAt.comp (p u₀) ?_ hs
    rw [hsx]
    exact hf u₀
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hps'] with y hy
  show f y = f (p (s y))
  rw [hy]

/-- A continuous map `ℂ → ℝ` with integer values (`f = k` for some `k : ℂ → ℤ`) is constant: `k` is continuous
since `ℤ → ℝ` is an embedding, and `ℂ` is connected. -/
theorem tor_el_int_valued_const {f : ℂ → ℝ} (hf : Continuous f) {k : ℂ → ℤ}
    (hk : ∀ z, f z = k z) (z w : ℂ) : k z = k w := by
  have hkc : Continuous k := by
    rw [Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff]
    exact hf.congr hk
  exact PreconnectedSpace.constant inferInstance hkc

/-- **E** (discreteness of the lattice): a continuous map `ℂ → ℂ` with values in `ℤ + ℤτ'` (`Im τ' > 0`) is
constant. -/
theorem tor_lattice_const {τ' : ℂ} (hτ' : 0 < τ'.im) {G : ℂ → ℂ} (hG : Continuous G)
    (hmem : ∀ z, ∃ n m : ℤ, G z = n + m * τ') (z w : ℂ) : G z = G w := by
  choose n m hnm using hmem
  have him : ∀ z, (G z).im / τ'.im = m z := by
    intro z
    rw [hnm z]
    simp [hτ'.ne']
  have hm : ∀ z w, m z = m w :=
    tor_el_int_valued_const ((Complex.continuous_im.comp hG).div_const _) him
  have hre : ∀ z, (G z).re - (G z).im / τ'.im * τ'.re = n z := by
    intro z
    rw [him z, hnm z]
    simp
  have hn : ∀ z w, n z = n w :=
    tor_el_int_valued_const ((Complex.continuous_re.comp hG).sub
      (((Complex.continuous_im.comp hG).div_const _).mul continuous_const)) hre
  rw [hnm z, hnm w, hn z w, hm z w]

/-- A continuous `1`- and `τ`-periodic function `ℂ → ℂ` (`Im τ > 0`) has bounded range: every value is
taken on the compact parallelogram `{s + tτ : s, t ∈ [0, 1]}` (reduce `z = s + tτ` by `⌊s⌋ + ⌊t⌋τ`). -/
theorem tor_el_bounded_of_periodic {τ : ℂ} (hτ : 0 < τ.im) {D : ℂ → ℂ} (hD : Continuous D)
    (h1 : Function.Periodic D 1) (h2 : Function.Periodic D τ) : Bornology.IsBounded (range D) := by
  set φ : ℝ × ℝ → ℂ := fun q => (q.1 : ℂ) + (q.2 : ℂ) * τ with hφ
  have hφc : Continuous φ := by fun_prop
  have hK : IsCompact ((D ∘ φ) '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image (hD.comp hφc)
  refine hK.isBounded.subset ?_
  rintro _ ⟨z, rfl⟩
  set t : ℝ := z.im / τ.im with ht
  set s : ℝ := z.re - t * τ.re with hs
  have hz0 : z = (s : ℂ) + (t : ℂ) * τ := by
    apply Complex.ext
    · simp [hs]
    · simp [ht]
      field_simp
  have hz : z = ((s - ⌊s⌋ : ℝ) : ℂ) + ((t - ⌊t⌋ : ℝ) : ℂ) * τ + (⌊s⌋ : ℂ) + (⌊t⌋ : ℂ) * τ := by
    rw [hz0]
    push_cast
    ring
  refine ⟨(s - ⌊s⌋, t - ⌊t⌋), ⟨⟨Int.fract_nonneg s, (Int.fract_lt_one s).le⟩,
    ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩⟩, ?_⟩
  simp only [Function.comp_apply, hφ]
  rw [hz, h2.int_mul, ← mul_one ((⌊s⌋ : ℤ) : ℂ), h1.int_mul]

/-- **L** (Liouville): an entire `F` with `F(z + 1) - F(z)` and `F(z + τ) - F(z)` constant (`Im τ > 0`) is affine:
`F'` is entire and doubly periodic, hence bounded, hence constant. -/
theorem tor_affine_of_periodic {τ : ℂ} (hτ : 0 < τ.im) {F : ℂ → ℂ} (hF : Differentiable ℂ F) {c₁ c₂ : ℂ}
    (h1 : ∀ z, F (z + 1) = F z + c₁) (h2 : ∀ z, F (z + τ) = F z + c₂) :
    ∃ a b : ℂ, ∀ z, F z = a + b * z := by
  have hD : Differentiable ℂ (deriv F) := hF.deriv
  have hp1 : Function.Periodic (deriv F) 1 := by
    intro z
    rw [← deriv_comp_add_const F 1 z]
    simp_rw [h1]
    exact deriv_add_const c₁
  have hp2 : Function.Periodic (deriv F) τ := by
    intro z
    rw [← deriv_comp_add_const F τ z]
    simp_rw [h2]
    exact deriv_add_const c₂
  have hb := tor_el_bounded_of_periodic hτ hD.continuous hp1 hp2
  have hconst : ∀ z, deriv F z = deriv F 0 := fun z => hD.apply_eq_apply_of_bounded hb z 0
  have hH : ∀ z, HasDerivAt (fun z => F z - deriv F 0 * z) 0 z := by
    intro z
    have := (hF z).hasDerivAt.sub ((hasDerivAt_id z).const_mul (deriv F 0))
    rw [hconst z, mul_one, sub_self] at this
    exact this
  have hc := is_const_of_deriv_eq_zero (fun z => (hH z).differentiableAt) (fun z => (hH z).deriv)
  refine ⟨F 0, deriv F 0, fun z => ?_⟩
  have := hc z 0
  simp only [mul_zero, sub_zero] at this
  rw [← this]
  ring

/-- Coefficient comparison in `ℤ + ℤτ'` (`Im τ' > 0`): `x + yτ' = u + vτ'` forces `x = u` and `y = v`
(compare imaginary parts, then real parts). -/
theorem tor_m_coeff_eq {τ' : ℂ} (hτ' : 0 < τ'.im) {x y u v : ℤ}
    (h : (x : ℂ) + y * τ' = u + v * τ') : x = u ∧ y = v := by
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [add_im, add_re, intCast_re, intCast_im, mul_re, mul_im, zero_mul, add_zero, zero_add,
    sub_zero] at him hre
  have hyv : (y : ℝ) = v := mul_right_cancel₀ (ne_of_gt hτ') him
  have hyv' : y = v := by exact_mod_cast hyv
  subst hyv'
  refine ⟨?_, rfl⟩
  have : (x : ℝ) = u := by linarith
  exact_mod_cast this

/-- **M** (lattice map ⇒ modular relation): if `z ↦ bz` maps `ℤ + ℤτ` onto `ℤ + ℤτ'` (`Im τ, Im τ' > 0`), then
`τ = (ατ' + β)/(γτ' + δ)` with an integer matrix of determinant `1` (`b = γτ' + δ`, `bτ = ατ' + β`; the
determinant is `±1` since the inverse matrix is integral, and `+1` since `Im τ = det · Im τ'/|b|²`). -/
theorem tor_sl2_of_lattice {τ τ' b : ℂ} (hτ : 0 < τ.im) (hτ' : 0 < τ'.im) (hb : b ≠ 0)
    (hto : ∀ n m : ℤ, ∃ n' m' : ℤ, b * (n + m * τ) = n' + m' * τ')
    (hfrom : ∀ n' m' : ℤ, ∃ n m : ℤ, (n' : ℂ) + m' * τ' = b * (n + m * τ)) :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, τ = (γ 0 0 * τ' + γ 0 1) / (γ 1 0 * τ' + γ 1 1) := by
  obtain ⟨n₁, m₁, e1⟩ := hto 1 0
  obtain ⟨n₂, m₂, e2⟩ := hto 0 1
  obtain ⟨p₁, q₁, e3⟩ := hfrom 1 0
  obtain ⟨p₂, q₂, e4⟩ := hfrom 0 1
  push_cast at e1 e2 e3 e4
  -- `b = n₁ + m₁τ'` and `bτ = n₂ + m₂τ'`
  have e1' : b = n₁ + m₁ * τ' := by linear_combination e1
  have e2' : b * τ = n₂ + m₂ * τ' := by linear_combination e2
  -- the inverse matrix `[[p₁, p₂], [q₁, q₂]]` is integral
  have f1 : ((p₁ * n₁ + q₁ * n₂ : ℤ) : ℂ) + ((p₁ * m₁ + q₁ * m₂ : ℤ) : ℂ) * τ'
      = ((1 : ℤ) : ℂ) + ((0 : ℤ) : ℂ) * τ' := by
    push_cast
    linear_combination -e3 - (p₁ : ℂ) * e1' - (q₁ : ℂ) * e2'
  have f2 : ((p₂ * n₁ + q₂ * n₂ : ℤ) : ℂ) + ((p₂ * m₁ + q₂ * m₂ : ℤ) : ℂ) * τ'
      = ((0 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * τ' := by
    push_cast
    linear_combination -e4 - (p₂ : ℂ) * e1' - (q₂ : ℂ) * e2'
  obtain ⟨g1, g2⟩ := tor_m_coeff_eq hτ' f1
  obtain ⟨g3, g4⟩ := tor_m_coeff_eq hτ' f2
  have hdet1 : (m₂ * n₁ - n₂ * m₁) * (p₁ * q₂ - p₂ * q₁) = 1 := by
    linear_combination (p₂ * m₁ + q₂ * m₂) * g1 + g4 - (p₂ * n₁ + q₂ * n₂) * g2
  -- the sign: `Im τ · |b|² = det · Im τ'`
  have key : τ.im * Complex.normSq b = ((m₂ * n₁ - n₂ * m₁ : ℤ) : ℝ) * τ'.im := by
    have E1 := congrArg Complex.re e2'
    have E2 := congrArg Complex.im e2'
    have E3 := congrArg Complex.re e1'
    have E4 := congrArg Complex.im e1'
    simp only [mul_re, mul_im, add_re, add_im, intCast_re, intCast_im, zero_mul, sub_zero,
      add_zero, zero_add] at E1 E2 E3 E4
    rw [Complex.normSq_apply]
    push_cast
    linear_combination b.re * E2 - b.im * E1 + (m₂ : ℝ) * τ'.im * E3
      - ((n₂ : ℝ) + m₂ * τ'.re) * E4
  have hpos : 0 < ((m₂ * n₁ - n₂ * m₁ : ℤ) : ℝ) := by
    have h0 : 0 < τ.im * Complex.normSq b := mul_pos hτ (Complex.normSq_pos.2 hb)
    rw [key] at h0
    exact pos_of_mul_pos_left h0 hτ'.le
  have hpos' : 0 < m₂ * n₁ - n₂ * m₁ := by exact_mod_cast hpos
  have hdet : m₂ * n₁ - n₂ * m₁ = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet1 with h | h
    · exact h
    · omega
  refine ⟨⟨!![m₂, n₂; m₁, n₁], by rw [Matrix.det_fin_two_of]; linarith⟩, ?_⟩
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  have hb' : (m₁ : ℂ) * τ' + n₁ ≠ 0 := by rw [add_comm, ← e1']; exact hb
  rw [eq_div_iff hb']
  linear_combination e2' - τ * e1'

/-- **M'** (modular relation ⇒ lattice map): if `τ = (ατ' + β)/(γτ' + δ)` with an integer matrix of
determinant `1` and `Im τ' > 0`, then `b = γτ' + δ ≠ 0` and `z ↦ bz` maps `ℤ + ℤτ` onto `ℤ + ℤτ'`. -/
theorem tor_lattice_of_sl2 {τ τ' : ℂ} (hτ' : 0 < τ'.im) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h : τ = (γ 0 0 * τ' + γ 0 1) / (γ 1 0 * τ' + γ 1 1)) :
    ((γ 1 0 : ℂ) * τ' + γ 1 1 ≠ 0) ∧
      (∀ n m : ℤ, ∃ n' m' : ℤ, ((γ 1 0 : ℂ) * τ' + γ 1 1) * (n + m * τ) = n' + m' * τ') ∧
      ∀ n' m' : ℤ, ∃ n m : ℤ, (n' : ℂ) + m' * τ' = ((γ 1 0 : ℂ) * τ' + γ 1 1) * (n + m * τ) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h1 := γ.det_coe
    rwa [Matrix.det_fin_two] at h1
  generalize γ 0 0 = a at hdet h ⊢
  generalize γ 0 1 = β at hdet h ⊢
  generalize γ 1 0 = c at hdet h ⊢
  generalize γ 1 1 = d at hdet h ⊢
  have hdetC : (a : ℂ) * d - β * c = 1 := by exact_mod_cast hdet
  -- `b = cτ' + d ≠ 0`: `Im b = c · Im τ'`, and `c = 0` forces `d ≠ 0` since `ad = 1`
  have hb : (c : ℂ) * τ' + d ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, zero_im] at him
    have hc : (c : ℝ) = 0 := by
      rcases mul_eq_zero.1 him with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt hτ')
    have hc' : c = 0 := by exact_mod_cast hc
    subst hc'
    have hd : (d : ℂ) = 0 := by simpa using h0
    have hd' : d = 0 := by exact_mod_cast hd
    subst hd'
    simp at hdet
  have hbτ : ((c : ℂ) * τ' + d) * τ = a * τ' + β := by
    rw [h, mul_div_cancel₀ _ hb]
  -- `b(n + mτ) = (nd + mβ) + (nc + ma)τ'`, inverted by the adjugate matrix
  refine ⟨hb, fun n m => ⟨n * d + m * β, n * c + m * a, ?_⟩, fun n' m' =>
    ⟨a * n' - β * m', -c * n' + d * m', ?_⟩⟩
  · push_cast
    linear_combination (m : ℂ) * hbτ
  · push_cast
    linear_combination (-(-(c : ℂ) * n' + d * m')) * hbτ - (n' : ℂ) * hdetC - (m' : ℂ) * τ' * hdetC

/-- (§28.1, converse direction) If `z ↦ bz` (`b ≠ 0`) maps the lattice `ℤ + ℤτ` onto `ℤ + ℤτ'`, then the tori
`p : ℂ → X` and `p' : ℂ → X'` are conformally equivalent: `f (p z) = p' (bz)` is well defined, holomorphic by
descent through `p`, with holomorphic inverse `g (p' w) = p (w / b)`. -/
theorem tor_t_conformal_of_lattice {X X' : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace X'] [ChartedSpace ℂ X'] [IsManifold 𝓘(ℂ) ω X']
    {τ τ' b : ℂ} {p : ℂ → X} {p' : ℂ → X'} (hp : IsTorusWithPeriod τ p)
    (hp' : IsTorusWithPeriod τ' p') (hb : b ≠ 0)
    (hto : ∀ n m : ℤ, ∃ n' m' : ℤ, b * (n + m * τ) = n' + m' * τ')
    (hfrom : ∀ n' m' : ℤ, ∃ n m : ℤ, (n' : ℂ) + m' * τ' = b * (n + m * τ)) :
    RSConformallyEquivalent X X' := by
  obtain ⟨-, hpc, hpd, hps, hpfib⟩ := hp
  obtain ⟨-, hpc', hpd', hps', hpfib'⟩ := hp'
  have hs : ∀ x, p (Function.surjInv hps x) = x := Function.surjInv_eq hps
  have hs' : ∀ y, p' (Function.surjInv hps' y) = y := Function.surjInv_eq hps'
  let f : X → X' := fun x => p' (b * Function.surjInv hps x)
  let g : X' → X := fun y => p (Function.surjInv hps' y / b)
  -- well-definedness: the formulas on the covering planes
  have hf : ∀ z, f (p z) = p' (b * z) := by
    intro z
    show p' (b * Function.surjInv hps (p z)) = p' (b * z)
    obtain ⟨n, m, h⟩ := (hpfib _ _).1 (hs (p z))
    obtain ⟨n', m', h'⟩ := hto n m
    exact (hpfib' _ _).2 ⟨n', m', by rw [← h', ← h]; ring⟩
  have hg : ∀ w, g (p' w) = p (w / b) := by
    intro w
    show p (Function.surjInv hps' (p' w) / b) = p (w / b)
    obtain ⟨n', m', h'⟩ := (hpfib' _ _).1 (hs' (p' w))
    obtain ⟨n, m, h⟩ := hfrom n' m'
    refine (hpfib _ _).2 ⟨n, m, ?_⟩
    rw [← sub_div, h', h, mul_div_cancel_left₀ _ hb]
  -- holomorphy by descent
  have hfd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
    refine tor_mdifferentiable_descend hpc hpd hps ?_
    have hcomp : f ∘ p = p' ∘ fun z => b * z := funext hf
    rw [hcomp]
    exact hpd'.comp (differentiable_id.const_mul b).mdifferentiable
  have hgd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := by
    refine tor_mdifferentiable_descend hpc' hpd' hps' ?_
    have hcomp : g ∘ p' = p ∘ fun w => w / b := funext hg
    rw [hcomp]
    exact hpd.comp (differentiable_id.div_const b).mdifferentiable
  refine ⟨f, hfd, g, hgd, fun x => ?_, fun y => ?_⟩
  · obtain ⟨z, rfl⟩ := hps x
    rw [hf, hg, mul_div_cancel_left₀ _ hb]
  · obtain ⟨w, rfl⟩ := hps' y
    rw [hg, hf, mul_div_cancel₀ _ hb]

/-- §28.1: a biholomorphic map `f : ℂ/Λ → ℂ/Λ'` lifts to a biholomorphic map `F(z) = a + bz` of `ℂ`
mapping `Λ`-equivalent points to `Λ'`-equivalent points.

The holomorphic atlases `IsManifold 𝓘(ℂ) ω` are assumed (corrected 2026-09-25): on a bare `ChartedSpace`,
`MDifferentiable` only tests the preferred charts at a point and its image, at that point, so a
non-affine lattice-equivariant map can be "biholomorphic" for suitable non-holomorphic atlases. -/
theorem torus_map_lift {X X' : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace X'] [ChartedSpace ℂ X'] [IsManifold 𝓘(ℂ) ω X'] {τ τ' : ℂ} {p : ℂ → X} {p' : ℂ → X'}
    (hp : IsTorusWithPeriod τ p)
    (hp' : IsTorusWithPeriod τ' p') {f : X → X'} (hf : IsBiholomorphic f) :
    ∃ a b : ℂ, b ≠ 0 ∧ ∀ z, f (p z) = p' (a + b * z) := by
  obtain ⟨hτ, hpc, hpd, -, hpfib⟩ := hp
  obtain ⟨hτ', hpc', hpd', hps', hpfib'⟩ := hp'
  obtain ⟨hfd, g, -, hgf, -⟩ := hf
  -- a continuous, hence entire, lift `F` of `f ∘ p` through `p'`
  obtain ⟨F, hFc, hFp⟩ := tor_exists_lift hpc' hps' (hfd.continuous.comp hpc.continuous)
  have hFd : Differentiable ℂ F := tor_differentiable_lift hpc' hpd' (hfd.comp hpd) hFc hFp
  have hFp' : ∀ z, f (p z) = p' (F z) := fun z => (hFp z).symm
  -- `F (z + w) - F z` is a constant for every period `w` of `p`
  have hper : ∀ n₀ m₀ : ℤ, ∃ c : ℂ, ∀ z, F (z + (n₀ + m₀ * τ)) = F z + c := by
    intro n₀ m₀
    have hmem : ∀ z, ∃ n m : ℤ, F (z + (n₀ + m₀ * τ)) - F z = n + m * τ' := by
      intro z
      refine (hpfib' _ _).1 ?_
      rw [← hFp', ← hFp']
      exact congrArg f ((hpfib _ _).2 ⟨n₀, m₀, by ring⟩)
    have hG : Continuous (fun z => F (z + (n₀ + m₀ * τ)) - F z) :=
      (hFc.comp (continuous_id.add continuous_const)).sub hFc
    refine ⟨F (0 + (n₀ + m₀ * τ)) - F 0, fun z => ?_⟩
    have h := tor_lattice_const hτ' hG hmem z 0
    linear_combination h
  obtain ⟨c₁, hc₁⟩ := hper 1 0
  obtain ⟨c₂, hc₂⟩ := hper 0 1
  obtain ⟨a, b, hab⟩ := tor_affine_of_periodic hτ hFd (c₁ := c₁) (c₂ := c₂)
    (fun z => by simpa using hc₁ z) (fun z => by simpa using hc₂ z)
  refine ⟨a, b, ?_, fun z => by rw [hFp', hab]⟩
  -- `b ≠ 0`: otherwise `f (p 0) = f (p (1/2))`, so `1/2 ∈ Λ`
  intro hb0
  have h1 : f (p 0) = f (p (1 / 2)) := by
    rw [hFp', hFp', hab, hab, hb0, zero_mul, zero_mul]
  have h2 : p 0 = p (1 / 2) := by
    have h := congrArg g h1
    rwa [hgf, hgf] at h
  obtain ⟨n, m, hnm⟩ := (hpfib _ _).1 h2
  have him := congrArg Complex.im hnm
  have hre := congrArg Complex.re hnm
  simp at him hre
  obtain rfl : m = 0 := him.resolve_right hτ.ne'
  norm_num at hre
  have h2n : ((2 * n : ℤ) : ℝ) = -1 := by push_cast; linarith
  have h2n' : 2 * n = -1 := by exact_mod_cast h2n
  omega

/-- **§28.1**: the tori `ℂ/(ℤ + ℤτ)` and `ℂ/(ℤ + ℤτ')` are conformally equivalent iff
`τ = (ατ' + β)/(γτ' + δ)` for integers `α, β, γ, δ` with `αδ - βγ = 1`. -/
theorem torus_conformal_iff {X X' : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X]
    [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [TopologicalSpace X'] [ChartedSpace ℂ X'] [T2Space X']
    [ConnectedSpace X'] [IsManifold 𝓘(ℂ) ω X'] {τ τ' : ℂ} {p : ℂ → X} {p' : ℂ → X'}
    (hp : IsTorusWithPeriod τ p) (hp' : IsTorusWithPeriod τ' p') :
    RSConformallyEquivalent X X' ↔
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, τ = (γ 0 0 * τ' + γ 0 1) / (γ 1 0 * τ' + γ 1 1) := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨a, b, hb, hfab⟩ := torus_map_lift hp hp' hf
    obtain ⟨hτ, -, -, -, hpfib⟩ := hp
    obtain ⟨hτ', -, -, -, hpfib'⟩ := hp'
    obtain ⟨-, g, -, hgf, -⟩ := hf
    refine tor_sl2_of_lattice hτ hτ' hb (fun n m => ?_) (fun n' m' => ?_)
    · -- `bΛ ⊆ Λ'`: `p' (a + bω) = f (p ω) = f (p 0) = p' a`
      have h : p' (a + b * (n + m * τ)) = p' (a + b * 0) := by
        rw [← hfab, ← hfab]
        exact congrArg f ((hpfib _ _).2 ⟨n, m, by ring⟩)
      obtain ⟨n', m', h'⟩ := (hpfib' _ _).1 h
      exact ⟨n', m', by linear_combination h'⟩
    · -- `Λ' ⊆ bΛ`: `f (p (ω'/b)) = p' (a + ω') = p' a = f (p 0)` and `f` is injective
      have hbb : b * ((n' + m' * τ') / b) = n' + m' * τ' := mul_div_cancel₀ _ hb
      have h1 : f (p ((n' + m' * τ') / b)) = f (p 0) := by
        rw [hfab, hfab]
        exact (hpfib' _ _).2 ⟨n', m', by rw [hbb]; ring⟩
      have h2 : p ((n' + m' * τ') / b) = p 0 := by
        have h := congrArg g h1
        rwa [hgf, hgf] at h
      obtain ⟨n, m, h⟩ := (hpfib _ _).1 h2
      refine ⟨n, m, ?_⟩
      rw [← h, sub_zero, hbb]
  · rintro ⟨γ, hγ⟩
    obtain ⟨hb, hto, hfrom⟩ := tor_lattice_of_sl2 hp'.1 γ hγ
    exact tor_t_conformal_of_lattice hp hp' hb hto hfrom

/-- §28.1: the modular group `M = {τ ↦ (ατ + β)/(γτ + δ) : α, β, γ, δ ∈ ℤ, αδ - βγ = 1}`, acting on
`ℍ` (Mathlib's action of `SL(2, ℤ)` on `ℍ`). -/
def modularGroupOrbitRel : Setoid UpperHalfPlane :=
  MulAction.orbitRel (Matrix.SpecialLinearGroup (Fin 2) ℤ) UpperHalfPlane

/-- §28.1: the fundamental polygon `D = {τ : |Re τ| ≤ 1/2, |τ| ≥ 1}` of `M` (Figure 8.28.1). -/
def modularFundamentalDomain : Set ℂ := {τ | |τ.re| ≤ 1 / 2 ∧ 1 ≤ ‖τ‖ ∧ 0 < τ.im}

/-- §28.1: every `τ ∈ ℍ` is `M`-equivalent to a point of `D`, and two points of `D` are equivalent
only if they are symmetric boundary points (`Re τ = ±1/2` or `|τ| = 1`, `τ ↦ -τ̄`).  Hence
`R₁ ↔ ℍ/M ↔ D` with symmetric boundary points identified. -/
theorem modularFundamentalDomain_property :
    (∀ τ : UpperHalfPlane, ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ((γ • τ : UpperHalfPlane) : ℂ) ∈ modularFundamentalDomain) ∧
      ∀ τ τ' : UpperHalfPlane, (τ : ℂ) ∈ modularFundamentalDomain → (τ' : ℂ) ∈ modularFundamentalDomain →
        (∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ • τ = τ') →
        τ = τ' ∨ (τ' : ℂ) = -conj (τ : ℂ) := by
  -- The project's `D ⊆ ℂ` is Mathlib's closed fundamental domain `𝒟 ⊆ ℍ` read through the
  -- coercion: the three conjuncts agree (cf. `ModularGroup.coe_fd`).
  have hmem : ∀ τ : UpperHalfPlane, (τ : ℂ) ∈ modularFundamentalDomain ↔ τ ∈ ModularGroup.fd := by
    intro τ
    simp only [modularFundamentalDomain, Set.mem_setOf_eq, ModularGroup.fd,
      Complex.one_le_normSq_iff]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, τ.im_pos⟩⟩
  -- All three boundary identifications are the single map `τ ↦ -τ̄`.
  have hS : ∀ z : UpperHalfPlane, ‖(z : ℂ)‖ = 1 →
      ((ModularGroup.S • z : UpperHalfPlane) : ℂ) = -conj (z : ℂ) := by
    intro z hz
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [neg_mul_neg, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hT : ∀ z : UpperHalfPlane, z.re = -1 / 2 →
      ((ModularGroup.T • z : UpperHalfPlane) : ℂ) = -conj (z : ℂ) := by
    intro z hz
    rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]
    exact Complex.ext (by norm_num [hz]) (by simp)
  have hT' : ∀ z : UpperHalfPlane, z.re = 1 / 2 →
      ((ModularGroup.T⁻¹ • z : UpperHalfPlane) : ℂ) = -conj (z : ℂ) := by
    intro z hz
    rw [show (ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
        = ModularGroup.T ^ (-1 : ℤ) by simp, UpperHalfPlane.modular_T_zpow_smul,
      UpperHalfPlane.coe_vadd]
    exact Complex.ext (by norm_num [hz]) (by simp)
  -- The corner `ρ` and its translate `1 + ρ`, and the four identities relating them.
  have hPcoe : (((1 : ℝ) +ᵥ UpperHalfPlane.ρ : UpperHalfPlane) : ℂ)
      = 1 + (UpperHalfPlane.ρ : ℂ) := by
    rw [UpperHalfPlane.coe_vadd]; norm_num
  have hconjρ : -conj (UpperHalfPlane.ρ : ℂ) = 1 + (UpperHalfPlane.ρ : ℂ) := by
    simp [UpperHalfPlane.ρ, Complex.ext_iff]
    norm_num
  have hc : conj (UpperHalfPlane.ρ : ℂ) = -(1 + (UpperHalfPlane.ρ : ℂ)) := by
    rw [← hconjρ]; ring
  have hconjP : -conj (((1 : ℝ) +ᵥ UpperHalfPlane.ρ : UpperHalfPlane) : ℂ)
      = (UpperHalfPlane.ρ : ℂ) := by
    rw [hPcoe, map_add, map_one, hc]; ring
  have hnormP : ‖(((1 : ℝ) +ᵥ UpperHalfPlane.ρ : UpperHalfPlane) : ℂ)‖ = 1 := by
    rw [hPcoe, ← hconjρ, norm_neg, Complex.norm_conj, UpperHalfPlane.norm_ρ]
  have hPre : ((1 : ℝ) +ᵥ UpperHalfPlane.ρ : UpperHalfPlane).re = 1 / 2 := by
    rw [← UpperHalfPlane.coe_re, hPcoe]; norm_num [UpperHalfPlane.ρ]
  have hTρ : ModularGroup.T • UpperHalfPlane.ρ = ((1 : ℝ) +ᵥ UpperHalfPlane.ρ) :=
    UpperHalfPlane.modular_T_smul _
  have hSρ : ModularGroup.S • UpperHalfPlane.ρ = ((1 : ℝ) +ᵥ UpperHalfPlane.ρ) := by
    rw [← UpperHalfPlane.coe_inj, hS _ UpperHalfPlane.norm_ρ, hconjρ, hPcoe]
  have hSP : ModularGroup.S • ((1 : ℝ) +ᵥ UpperHalfPlane.ρ) = UpperHalfPlane.ρ := by
    rw [← UpperHalfPlane.coe_inj, hS _ hnormP, hconjP]
  have hTiP : ModularGroup.T⁻¹ • ((1 : ℝ) +ᵥ UpperHalfPlane.ρ) = UpperHalfPlane.ρ := by
    rw [← UpperHalfPlane.coe_inj, hT' _ hPre, hconjP]
  refine ⟨fun τ => ?_, ?_⟩
  · -- existence: Mathlib's first fundamental domain lemma
    obtain ⟨g, hgmem⟩ := ModularGroup.exists_smul_mem_fd τ
    exact ⟨g, (hmem _).2 hgmem⟩
  · -- uniqueness: Mathlib classifies the closed-domain coincidences into ten cases
    rintro τ τ' hτ hτ' ⟨g, rfl⟩
    have hz : τ ∈ ModularGroup.fd := (hmem τ).1 hτ
    have hgz : g • τ ∈ ModularGroup.fd := (hmem _).1 hτ'
    rcases ModularGroup.cases_of_mem_fd_smul_mem_fd hz hgz with
      h | ⟨h, hre⟩ | ⟨h, hre⟩ | ⟨h, hnorm⟩ | ⟨h, hpt⟩ | ⟨h, hpt⟩ | ⟨h, hpt⟩ |
        ⟨h, hpt⟩ | ⟨h, hpt⟩ | ⟨h, hpt⟩
    · -- `g = ±1`
      exact Or.inl (by rcases h with rfl | rfl <;> simp [-ModularGroup.sl_moeb, ModularGroup.SL_neg_smul])
    · -- `g = ±T` on `Re τ = -1/2`
      refine Or.inr ?_
      rcases h with rfl | rfl
      · exact hT τ hre
      · rw [ModularGroup.SL_neg_smul]; exact hT τ hre
    · -- `g = ±T⁻¹` on `Re τ = 1/2`
      refine Or.inr ?_
      rcases h with rfl | rfl
      · exact hT' τ hre
      · rw [ModularGroup.SL_neg_smul]; exact hT' τ hre
    · -- `g = ±S` on `|τ| = 1`
      refine Or.inr ?_
      rcases h with rfl | rfl
      · exact hS τ hnorm
      · rw [ModularGroup.SL_neg_smul]; exact hS τ hnorm
    · -- `g = ±(T * S)` at `τ = 1 + ρ`: fixes it
      refine Or.inl ?_
      subst hpt
      rcases h with rfl | rfl <;>
        simp [-ModularGroup.sl_moeb, ModularGroup.SL_neg_smul, mul_smul, hSP, hTρ]
    · -- `g = ±(T⁻¹ * S * T⁻¹)` at `τ = 1 + ρ`: sends it to `ρ = -conj (1 + ρ)`
      refine Or.inr ?_
      subst hpt
      rw [hconjP, UpperHalfPlane.coe_inj]
      rcases h with rfl | rfl <;>
        simp [-ModularGroup.sl_moeb, ModularGroup.SL_neg_smul, mul_smul, hTiP, hSρ]
    · -- `g = ±(S * T⁻¹)` at `τ = 1 + ρ`: fixes it
      refine Or.inl ?_
      subst hpt
      rcases h with rfl | rfl <;>
        simp [-ModularGroup.sl_moeb, ModularGroup.SL_neg_smul, mul_smul, hTiP, hSρ]
    · -- `g = ±(S * T)` at `τ = ρ`: fixes it
      refine Or.inl ?_
      subst hpt
      rcases h with rfl | rfl <;>
        simp [-ModularGroup.sl_moeb, ModularGroup.SL_neg_smul, mul_smul, hTρ, hSP]
    · -- `g = ±(T * S * T)` at `τ = ρ`: sends it to `1 + ρ = -conj ρ`
      refine Or.inr ?_
      subst hpt
      rw [hconjρ, ← hPcoe, UpperHalfPlane.coe_inj]
      rcases h with rfl | rfl <;>
        simp [-ModularGroup.sl_moeb, ModularGroup.SL_neg_smul, mul_smul, hTρ, hSP]
    · -- `g = ±(T⁻¹ * S)` at `τ = ρ`: fixes it
      refine Or.inl ?_
      subst hpt
      rcases h with rfl | rfl <;>
        simp [-ModularGroup.sl_moeb, ModularGroup.SL_neg_smul, mul_smul, hSρ, hTiP]

/-! ## The moduli space `R_g` -/

/-- **§28.1**: the moduli space `R_g`: conformal equivalence classes of closed Riemann surfaces of
genus `g` (Riemann's assertion: for `g > 1` it is described by `6g - 6` real parameters). -/
def ModuliSpace (g : ℕ) : Type (u + 1) :=
  Quot (fun X Y : {X : ClosedRS.{u} // HasGenus X.carrier g} =>
    RSConformallyEquivalent X.1.carrier Y.1.carrier)

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

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

/-- §28.1: the map `T(S₀) → R_g`, `[S, f] ↦ [S]`, as a relation: `p` lies over `r`. -/
def LiesOver {g : ℕ} (p : TeichSpace S₀) (r : ModuliSpace.{u} g) : Prop :=
  ∃ (m : MarkedRS S₀) (h : HasGenus m.X.carrier g), p = Quot.mk _ m ∧ r = Quot.mk _ ⟨m.X, h⟩

/-- §28.1: the map `T(S₀) → R_g` is well defined and surjective; every `[S] ∈ R_g` corresponds to
infinitely (countably) many points `[S, f] ∈ T(S₀)`, `f` running through the homotopy classes of
homeomorphisms `S₀ → S`. -/
theorem liesOver_wellDefined_surjective [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S₀ g) :
    (∀ (p : TeichSpace S₀) (r r' : ModuliSpace.{u} g), LiesOver p r → LiesOver p r' → r = r') ∧
      (∀ r : ModuliSpace.{u} g, ∃ p : TeichSpace S₀, LiesOver p r) ∧
      ∀ r : ModuliSpace.{u} g, (Set.Infinite {p : TeichSpace S₀ | LiesOver p r} ∧
        Set.Countable {p : TeichSpace S₀ | LiesOver p r}) := by
  sorry

/-! ## §28.2 The modular group -/

/-- §28.2: a (quasiconformal) orientation preserving self-homeomorphism `σ` of `S₀`; it induces the
modular transformation `σ* : [S, f] ↦ [S, f ∘ σ]`. -/
def ModTransform (S₀ : Type u) [TopologicalSpace S₀] [ChartedSpace ℂ S₀] : Type u :=
  {h : S₀ ≃ₜ S₀ // IsOrientationPreservingRS h ∧ IsQCRS h}

/-- §28.2: the action `σ*([S, f]) = [S, f ∘ σ]` as a relation `ModAction σ p q` ("`σ*` sends `p`
to `q`"). -/
def ModAction (h : ModTransform S₀) (p q : TeichSpace S₀) : Prop :=
  ∃ (m : MarkedRS S₀) (hqc : IsQCRS (h.1.trans m.marking)),
    p = Quot.mk _ m ∧ q = Quot.mk _ ⟨m.X, h.1.trans m.marking, hqc⟩

/-- §28.2: `σ*` is a well defined bijection of `T(S₀)`; homotopic `σ, σ'` induce the same
transformation, `(σ')* = σ*`. -/
theorem modAction_bijective [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (h : ModTransform S₀) :
    (∀ p, ∃! q, ModAction h p q) ∧ (∀ q, ∃! p, ModAction h p q) ∧
      ∀ h' : ModTransform S₀, ContinuousMap.Homotopic (h.1 : C(S₀, S₀)) (h'.1 : C(S₀, S₀)) →
        ∀ p q, ModAction h p q ↔ ModAction h' p q := by
  sorry

/-- §28.2: conversely, if `σ* = (σ')*` then `f ∘ σ' ∘ σ⁻¹ ∘ f⁻¹` is homotopic to a conformal map for
every `f : S₀ → S`; for `g > 2` this implies `σ ≃ σ'` (not proved in the book), so that for `g > 2`
the modular transformations `σ*` correspond bijectively to the homotopy classes `[σ]` and `Mod_g`
is isomorphic to the mapping class group. -/
theorem modAction_eq_iff_homotopic [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]
    {g : ℕ} (hg : 2 < g) (hS : HasGenus S₀ g) (h h' : ModTransform S₀) :
    (∀ p q, ModAction h p q ↔ ModAction h' p q) ↔
      ContinuousMap.Homotopic (h.1 : C(S₀, S₀)) (h'.1 : C(S₀, S₀)) := by
  sorry

/-- **(28.1)** `R_g = T(S₀)/Mod(S₀)`: two closed surfaces `S₁`, `S₂` of genus `g` are conformally
equivalent iff for all quasiconformal `fⱼ : S₀ → Sⱼ` the points `[S₁, f₁]`, `[S₂, f₂]` are
equivalent under `Mod(S₀)`, i.e. `σ*([S₂, f₂]) = [S₁, f₁]` for some `σ` (take
`σ = f₂⁻¹ ∘ h ∘ f₁` for a conformal `h : S₁ → S₂`).  Equivalently: two points of `T(S₀)` lie over
the same point of `R_g` iff they are related by a modular transformation. -/
theorem eq28_1_moduli_eq_quotient [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ}
    (hg : 1 < g) (hS : HasGenus S₀ g) (m₁ m₂ : MarkedRS S₀) :
    RSConformallyEquivalent m₁.X.carrier m₂.X.carrier ↔
      ∃ h : ModTransform S₀, ModAction h (Quot.mk _ m₂) (Quot.mk _ m₁) := by
  sorry

/-- (28.1) in terms of `LiesOver`: `p` and `q` lie over the same point of `R_g` iff `q = σ*(p)` for
some modular transformation. -/
theorem liesOver_same_iff [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {g : ℕ} (hg : 1 < g)
    (hS : HasGenus S₀ g) {p q : TeichSpace S₀} {r : ModuliSpace.{u} g} (hp : LiesOver p r) :
    LiesOver q r ↔ ∃ h : ModTransform S₀, ModAction h p q := by
  sorry

end LiZhongQC
