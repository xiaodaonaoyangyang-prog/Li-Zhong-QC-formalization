import LiZhongQC.Ch09.S31_FiniteType
import Jacobians.Monodromy.HolomorphicPrimitiveMonodromy
import Jacobians.Monodromy.HolomorphicPrimitiveLocal
import Jacobians.CanonicalForms.FormRemovableSingularity

/-!
# Eigenspaces of an anticonformal involution on real characters

`s78no_anticonformal_character_eigen`: for an anticonformal involution `J` of a closed Riemann
surface `X` fixing `x`, the involution `A` of `Hom(π₁(X, x), ℝ)` induced by `J` has
`dim ker (A - 1) = dim ker (A + 1) = genus X`.

* `s78no_exists_conj_pullback`: the conjugate pullback `conj (J* η)` of a holomorphic 1-form is a
  holomorphic 1-form, with local primitives `conj ∘ F ∘ J`.
* `s78no_pathPrimValue_conj_pullback`: `∫_γ conj (J* η) = conj (∫_{J ∘ γ} η)`.
* The real period map `P` (`k22rr_exists_real_period_map`, bijective) intertwines the conjugate
  pullback with `A`, and `P ∘ (i ·) ∘ P⁻¹` anticommutes with `A`; with `A² = 1` and
  `dim Hom(π₁, ℝ) = 2 g` this gives both eigenspace dimensions.
-/

open Complex Set Topology Filter
open scoped ComplexConjugate Manifold ContDiff

noncomputable section
namespace LiZhongQC
universe u

section Local

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Holomorphy of `conj ∘ F ∘ J` in charts.**  If `J` is an anticonformal involution and `F` is
holomorphic on an open set `U ∋ J x₀`, then `z ↦ conj (F (J (φ⁻¹ z)))` (`φ` the chart at `x₀`) is
complex differentiable near `φ x₀`: it is `(conj ∘ (F ∘ ψ⁻¹) ∘ conj) ∘ (conj ∘ ψ ∘ J ∘ φ⁻¹)`, `ψ` the
chart at `J x₀`. -/
theorem s78no_conj_comp_eventually_differentiableAt {J : X ≃ₜ X}
    (hJ : IsAnticonformalInvolution J) (x₀ : X) {F : X → ℂ} {U : Set X} (hU : IsOpen U)
    (hJx : J x₀ ∈ U) (hF : ∀ p ∈ U, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F p) :
    ∀ᶠ z in 𝓝 ((chartAt ℂ x₀) x₀),
      DifferentiableAt ℂ (fun w => conj (F (J ((chartAt ℂ x₀).symm w)))) z := by
  set φ := chartAt ℂ x₀ with hφ
  set ψ := chartAt ℂ (J x₀) with hψ
  have hD : IsOpen (localMapDomain J x₀) :=
    φ.isOpen_inter_preimage_symm ((ψ.open_source).preimage J.continuous)
  have hUo : IsOpen (φ.target ∩ φ.symm ⁻¹' (J ⁻¹' U)) :=
    φ.isOpen_inter_preimage_symm (hU.preimage J.continuous)
  have hx₀D : φ x₀ ∈ localMapDomain J x₀ := by
    refine ⟨φ.map_source (mem_chart_source ℂ x₀), ?_⟩
    simp only [mem_preimage]
    rw [φ.left_inv (mem_chart_source ℂ x₀)]
    exact mem_chart_source ℂ (J x₀)
  have hx₀U : φ x₀ ∈ φ.target ∩ φ.symm ⁻¹' (J ⁻¹' U) := by
    refine ⟨φ.map_source (mem_chart_source ℂ x₀), ?_⟩
    simp only [mem_preimage]
    rw [φ.left_inv (mem_chart_source ℂ x₀)]
    exact hJx
  filter_upwards [hD.mem_nhds hx₀D, hUo.mem_nhds hx₀U] with z hzD hzU
  -- the anticonformal factor
  have hk : DifferentiableAt ℂ (fun w => conj (localMapExpr J x₀ w)) z :=
    (hJ.2 x₀).differentiableAt (hD.mem_nhds hzD)
  -- the holomorphic factor
  set p := J (φ.symm z) with hp
  have hpψ : p ∈ ψ.source := hzD.2
  have hpU : p ∈ U := hzU.2
  have hH : DifferentiableAt ℂ (F ∘ ψ.symm) (ψ p) :=
    Jacobians.differentiableAt_comp_chart_symm hpψ (hF p hpU)
  have hH' : DifferentiableAt ℂ (conj ∘ (F ∘ ψ.symm) ∘ conj) (conj (ψ p)) :=
    hH.hasDerivAt.conj_conj.differentiableAt
  have hcomp : DifferentiableAt ℂ
      ((conj ∘ (F ∘ ψ.symm) ∘ conj) ∘ fun w => conj (localMapExpr J x₀ w)) z := by
    have : conj (localMapExpr J x₀ z) = conj (ψ p) := rfl
    rw [← this] at hH'
    exact hH'.comp z hk
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hD.mem_nhds hzD] with w hw
  simp only [Function.comp_apply, conj_conj, localMapExpr]
  rw [← hψ, ψ.left_inv hw.2]

/-- `conj ∘ F ∘ J` is holomorphic at every point `y` with `J y` in the holomorphy domain of `F`. -/
theorem s78no_mdifferentiableAt_conj_comp {J : X ≃ₜ X} (hJ : IsAnticonformalInvolution J)
    {F : X → ℂ} {U : Set X} (hU : IsOpen U)
    (hF : ∀ p ∈ U, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F p) {y : X} (hy : J y ∈ U) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun p => conj (F (J p))) y := by
  have h := (s78no_conj_comp_eventually_differentiableAt hJ y hU hy hF).self_of_nhds
  have hm := Jacobians.Dolbeault.mdifferentiableAt_of_differentiableAt_comp
    (fun p => conj (F (J p))) ((chartAt ℂ y).map_source (mem_chart_source ℂ y)) h
  rwa [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)] at hm

end Local

section Global

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Two primitives of the same form give the same differential after `conj ∘ (·) ∘ J`. -/
theorem s78no_mfderiv_conj_comp_eq {J : X ≃ₜ X} (hJ : IsAnticonformalInvolution J)
    {η : Jacobians.HolomorphicOneForms X} {F F' : X → ℂ} {U U' : Set X} (hU : IsOpen U)
    (hU' : IsOpen U') (hF : Jacobians.IsLocalPrimitiveOn η F U)
    (hF' : Jacobians.IsLocalPrimitiveOn η F' U') {y : X} (hy : J y ∈ U) (hy' : J y ∈ U') :
    ∀ v : TangentSpace 𝓘(ℂ) y, mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun p => conj (F (J p))) y v =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun p => conj (F' (J p))) y v := by
  intro v
  have hloc := Jacobians.isLocalPrimitiveOn_sub_locally_const (hU.inter hU')
    (fun w hw => hF w hw.1) (fun w hw => hF' w hw.2) (⟨hy, hy'⟩ : J y ∈ U ∩ U')
  set c := F (J y) - F' (J y) with hc
  have hev : (fun p => conj (F (J p))) =ᶠ[𝓝 y]
      (fun p => conj (F' (J p))) + fun _ => conj c := by
    filter_upwards [J.continuous.continuousAt.preimage_mem_nhds hloc] with p hp
    have hp' : F (J p) - F' (J p) = c := hp
    simp only [Pi.add_apply]
    rw [← map_add, ← hp']; ring_nf
  rw [hev.mfderiv_eq]
  change mfderiv 𝓘(ℂ) 𝓘(ℂ) ((fun p => conj (F' (J p))) + fun _ => conj c) y v = _
  rw [mfderiv_add (s78no_mdifferentiableAt_conj_comp hJ hU'
    (fun p hp => (hF' p hp).1) hy') mdifferentiableAt_const, mfderiv_const]
  exact add_zero _

/-- **The conjugate pullback of a holomorphic 1-form along an anticonformal involution.**  For
every holomorphic 1-form `η` there is a holomorphic 1-form `η'` (`= conj (J* η)`) whose local
primitives are the functions `conj ∘ F ∘ J`, `F` a local primitive of `η`. -/
theorem s78no_exists_conj_pullback {J : X ≃ₜ X} (hJ : IsAnticonformalInvolution J)
    (η : Jacobians.HolomorphicOneForms X) :
    ∃ η' : Jacobians.HolomorphicOneForms X, ∀ (U : Set X) (F : X → ℂ), IsOpen U →
      Jacobians.IsLocalPrimitiveOn η F U →
      Jacobians.IsLocalPrimitiveOn η' (fun p => conj (F (J p))) (J ⁻¹' U) := by
  classical
  choose Uf Ff hUo hmem _ hprim using fun y : X => Jacobians.exists_isLocalPrimitiveOn η (J y)
  let L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y := fun y =>
    mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun p => conj (Ff y (J p))) y
  have hAn : ∀ x₀ : X,
      letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      AnalyticAt ℂ
        (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
        ((chartAt ℂ x₀) x₀) := by
    intro x₀
    set φ := chartAt ℂ x₀ with hφ
    have hd := s78no_conj_comp_eventually_differentiableAt hJ x₀ (hUo x₀) (hmem x₀)
      (fun p hp => (hprim x₀ p hp).1)
    have han : AnalyticAt ℂ (fun w => conj (Ff x₀ (J (φ.symm w)))) (φ x₀) :=
      Complex.analyticAt_iff_eventually_differentiableAt.mpr hd
    apply han.deriv.congr
    -- near the centre the representative is the derivative of the centre's function
    have hT : φ.target ∈ 𝓝 (φ x₀) := φ.open_target.mem_nhds (mem_chart_target ℂ x₀)
    have hJU : ∀ᶠ z in 𝓝 (φ x₀), J (φ.symm z) ∈ Uf x₀ := by
      have hc : ContinuousAt (fun z => J (φ.symm z)) (φ x₀) :=
        J.continuous.continuousAt.comp (φ.continuousAt_symm (mem_chart_target ℂ x₀))
      apply hc.preimage_mem_nhds
      rw [φ.left_inv (mem_chart_source ℂ x₀)]
      exact (hUo x₀).mem_nhds (hmem x₀)
    filter_upwards [hT, hJU] with z hz hzU
    set y := φ.symm z with hy
    have hys : y ∈ φ.source := φ.map_target hz
    have h1 := s78no_mfderiv_conj_comp_eq hJ (hUo y) (hUo x₀) (hprim y) (hprim x₀) (hmem y) hzU
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1)
    have h2 := Jacobians.Dolbeault.mfderiv_apply_symmL_eq_deriv
      (fun p => conj (Ff x₀ (J p))) hys
      (s78no_mdifferentiableAt_conj_comp hJ (hUo x₀) (fun p hp => (hprim x₀ p hp).1) hzU)
    have h3 : φ y = z := φ.right_inv hz
    rw [h3] at h2
    exact (h1.trans h2).symm
  refine ⟨Jacobians.Dolbeault.holOfLocalRepAnalyticAt L hAn, fun U F hU hF => ?_⟩
  intro y hy
  refine ⟨s78no_mdifferentiableAt_conj_comp hJ hU (fun p hp => (hF p hp).1) hy, fun v => ?_⟩
  show L y v = _
  simp only [L]
  exact s78no_mfderiv_conj_comp_eq hJ (hUo y) hU (hprim y) hF (hmem y) hy v

/-- **Path identity.**  If `η'` is the conjugate pullback of `η` along `J`, then
`∫_γ η' = conj (∫_{J ∘ γ} η)`: a primitive chain of `η` along `J ∘ γ` is transported to the chain
`(J⁻¹ Uᵢ, conj ∘ Fᵢ ∘ J)` of `η'` along `γ`. -/
theorem s78no_pathPrimValue_conj_pullback {J : X ≃ₜ X}
    {η η' : Jacobians.HolomorphicOneForms X}
    (hη' : ∀ (U : Set X) (F : X → ℂ), IsOpen U → Jacobians.IsLocalPrimitiveOn η F U →
      Jacobians.IsLocalPrimitiveOn η' (fun p => conj (F (J p))) (J ⁻¹' U))
    {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1)) :
    Jacobians.pathPrimValue η' γ hγ =
      conj (Jacobians.pathPrimValue η (fun s => J (γ s)) (J.continuous.comp_continuousOn hγ)) := by
  classical
  obtain ⟨C⟩ : Nonempty (Jacobians.PrimitiveChain η (fun s => J (γ s))) :=
    Jacobians.exists_primitiveChain η (J.continuous.comp_continuousOn hγ)
  let D : Jacobians.PrimitiveChain η' γ :=
    { n := C.n
      t := C.t
      t_zero := C.t_zero
      t_stab := C.t_stab
      mono := C.mono
      U := fun i => J ⁻¹' C.U i
      F := fun i p => conj (C.F i (J p))
      isOpen := fun i => (C.isOpen i).preimage J.continuous
      prim := fun i => hη' _ _ (C.isOpen i) (C.prim i)
      covers := fun i s hs => C.covers i s hs }
  rw [Jacobians.pathPrimValue_eq η' _ D, Jacobians.pathPrimValue_eq η _ C]
  change (∑ i ∈ Finset.range C.n,
      (conj (C.F i (J (γ (C.t (i + 1))))) - conj (C.F i (J (γ (C.t i)))))) =
    conj (∑ i ∈ Finset.range C.n, (C.F i (J (γ (C.t (i + 1)))) - C.F i (J (γ (C.t i)))))
  rw [map_sum]
  simp only [map_sub]

end Global

/-- **Eigenspaces of an anticonformal involution on real characters.**  For an anticonformal
involution `J` of a closed Riemann surface fixing `x`, the induced involution `A` of
`Hom(π₁(X, x), ℝ)` has both eigenspaces `±1` of dimension `genus X`.

Proof: the real period map `P : ℂ^g → Hom(π₁, ℝ)` (`k22rr_exists_real_period_map`, bijective) carries
the conjugate pullback `η ↦ conj (J* η)` to `A` (`s78no_pathPrimValue_conj_pullback`), and
multiplication by `i` to an automorphism `I` with `A I = - I A`; so `I` exchanges the two
eigenspaces, and `A² = 1` (from `J ∘ J = id`) splits `Hom(π₁, ℝ)`, of dimension `2 g`, into them. -/
theorem s78no_anticonformal_character_eigen (X : Type u) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (J : X ≃ₜ X) (hJ : IsAnticonformalInvolution J) (x : X) (hx : J x = x)
    (A : Module.End ℝ (Additive (FundamentalGroup X x) →+ ℝ))
    (hA : ∀ χ (γ : FundamentalGroup X x),
      A χ (Additive.ofMul γ) =
        χ (Additive.ofMul (FundamentalGroup.mapOfEq (J : C(X, X)) hx γ))) :
    Module.finrank ℝ (LinearMap.ker (A - 1)) = genus X ∧
      Module.finrank ℝ (LinearMap.ker (A + 1)) = genus X := by
  classical
  obtain ⟨P, hP⟩ := k22rr_exists_real_period_map (X := X) x
  have hbij : Function.Bijective P := ⟨k22rr_pi_injective x P hP, k22rr_pd_surjective x P hP⟩
  let e := LinearEquiv.ofBijective P hbij
  choose pb hpb using s78no_exists_conj_pullback hJ
  -- the loop `J ∘ p`
  let q : Path x x → Path x x := fun p => (p.map J.continuous).cast hx.symm hx.symm
  have hloopJ : ∀ p : Path x x,
      FundamentalGroup.mapOfEq (J : C(X, X)) hx (FundamentalGroup.fromPath ⟦p⟧) =
        FundamentalGroup.fromPath ⟦q p⟧ := by
    intro p
    rw [FundamentalGroup.mapOfEq_apply]
    rfl
  have hpath : ∀ p : Path x x, q (q p) = p := by
    intro p
    ext t
    exact hJ.1 (p t)
  have hinv : ∀ γ : FundamentalGroup X x,
      FundamentalGroup.mapOfEq (J : C(X, X)) hx
        (FundamentalGroup.mapOfEq (J : C(X, X)) hx γ) = γ := by
    intro γ
    obtain ⟨γ⟩ := γ
    refine Quotient.inductionOn γ (fun p => ?_)
    rw [hloopJ, hloopJ, hpath]
  have hA2 : ∀ χ, A (A χ) = χ := by
    intro χ
    refine AddMonoidHom.ext fun a => ?_
    obtain ⟨γ, rfl⟩ := Additive.ofMul.surjective a
    rw [hA, hA, hinv]
  -- the period map intertwines the conjugate pullback with `A`
  have hconj : ∀ (v : Fin (genus X) → ℂ) (p : Path x x),
      Jacobians.pathPrimValue (pb (Jacobians.ambientIso X v)) p.extend
          p.continuous_extend.continuousOn =
        conj (Jacobians.pathPrimValue (Jacobians.ambientIso X v) (q p).extend
          (q p).continuous_extend.continuousOn) := fun v p =>
    s78no_pathPrimValue_conj_pullback (hpb _) p.continuous_extend.continuousOn
  have hF1 : ∀ (v : Fin (genus X) → ℂ) (p : Path x x),
      A (P v) (Additive.ofMul (FundamentalGroup.fromPath ⟦p⟧)) =
        (Jacobians.pathPrimValue (Jacobians.ambientIso X v) (q p).extend
          (q p).continuous_extend.continuousOn).re := by
    intro v p
    rw [hA, hloopJ, hP]
  let σ : (Fin (genus X) → ℂ) → (Fin (genus X) → ℂ) := fun v =>
    (Jacobians.ambientIso X).symm (pb (Jacobians.ambientIso X v))
  have hσ : ∀ v, Jacobians.ambientIso X (σ v) = pb (Jacobians.ambientIso X v) := fun v =>
    (Jacobians.ambientIso X).apply_symm_apply _
  have hAP : ∀ v, A (P v) = P (σ v) := by
    intro v
    refine AddMonoidHom.ext fun a => ?_
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective a
    obtain ⟨a⟩ := a
    refine Quotient.inductionOn a (fun p => ?_)
    rw [hF1, hP, hσ, hconj, Complex.conj_re]
  -- multiplication by `i`
  let Ri : (Fin (genus X) → ℂ) →ₗ[ℝ] (Fin (genus X) → ℂ) :=
    { toFun := fun v => Complex.I • v
      map_add' := fun v w => smul_add _ _ _
      map_smul' := fun r v => smul_comm _ _ _ }
  let I : (Additive (FundamentalGroup X x) →+ ℝ) →ₗ[ℝ] (Additive (FundamentalGroup X x) →+ ℝ) :=
    P ∘ₗ Ri ∘ₗ e.symm.toLinearMap
  have hIP : ∀ v, I (P v) = P (Complex.I • v) := by
    intro v
    change P (Ri (e.symm (e v))) = _
    rw [e.symm_apply_apply]
    rfl
  have hIinj : Function.Injective I := fun a b h =>
    e.symm.injective (smul_right_injective _ Complex.I_ne_zero (hbij.1 h))
  have hanti : ∀ χ, A (I χ) = -I (A χ) := by
    intro χ
    obtain ⟨v, rfl⟩ := hbij.2 χ
    rw [hIP, hAP, hAP, hIP]
    refine AddMonoidHom.ext fun a => ?_
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective a
    obtain ⟨a⟩ := a
    refine Quotient.inductionOn a (fun p => ?_)
    rw [AddMonoidHom.neg_apply, hP, hP, hσ, hconj, map_smul, map_smul, k22rr_pathPrimValue_smul,
      k22rr_pathPrimValue_smul, hσ, hconj]
    simp only [smul_eq_mul, map_mul, Complex.conj_I, Complex.conj_re, Complex.conj_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    ring
  -- linear algebra
  have : FiniteDimensional ℝ (Additive (FundamentalGroup X x) →+ ℝ) :=
    LinearEquiv.finiteDimensional e
  have hn : Module.finrank ℝ (Additive (FundamentalGroup X x) →+ ℝ) = 2 * genus X := by
    rw [← e.finrank_eq, finrank_real_of_complex, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  have hm1 : ∀ χ, χ ∈ LinearMap.ker (A - 1) ↔ A χ = χ := by
    intro χ
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hp1 : ∀ χ, χ ∈ LinearMap.ker (A + 1) ↔ A χ = -χ := by
    intro χ
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg]
  have hI12 : ∀ χ ∈ LinearMap.ker (A - 1), I χ ∈ LinearMap.ker (A + 1) := by
    intro χ hχ
    rw [hp1, hanti, (hm1 χ).1 hχ]
  have hI21 : ∀ χ ∈ LinearMap.ker (A + 1), I χ ∈ LinearMap.ker (A - 1) := by
    intro χ hχ
    rw [hm1, hanti, (hp1 χ).1 hχ, map_neg, neg_neg]
  have hle12 := LinearMap.finrank_le_finrank_of_injective (f := I.restrict hI12)
    (fun a b h => Subtype.ext (hIinj (congrArg Subtype.val h)))
  have hle21 := LinearMap.finrank_le_finrank_of_injective (f := I.restrict hI21)
    (fun a b h => Subtype.ext (hIinj (congrArg Subtype.val h)))
  have hinf : LinearMap.ker (A - 1) ⊓ LinearMap.ker (A + 1) = ⊥ := by
    rw [eq_bot_iff]
    intro χ hχ
    have h1 := (hm1 χ).1 hχ.1
    have h2 := (hp1 χ).1 hχ.2
    rw [h1] at h2
    rw [Submodule.mem_bot]
    have h3 : (2 : ℝ) • χ = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h2]
      exact neg_add_cancel χ
    exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (A - 1))
    (LinearMap.ker (A + 1))
  rw [hinf, finrank_bot] at hsup
  have hsupl := Submodule.finrank_le (LinearMap.ker (A - 1) ⊔ LinearMap.ker (A + 1))
  have hrange : LinearMap.range (A + 1) ≤ LinearMap.ker (A - 1) := by
    rintro _ ⟨χ, rfl⟩
    rw [hm1, LinearMap.add_apply, Module.End.one_apply, map_add, hA2, add_comm]
  have hr := Submodule.finrank_mono hrange
  have hrn := LinearMap.finrank_range_add_finrank_ker (A + 1)
  omega

end LiZhongQC
