import LiZhongQC.Ch11.S36_Hamilton

/-!
# Foundation piece F0: `ℍ/Γ` as a Riemann surface (R83 S36 foundation lane, 下属1)

For a Fuchsian group `Γ` acting freely up to `±1`, the orbit space `ℍ/Γ` is a Riemann surface uniformized by `Γ`.
Construction (no new definitions): `S = MulAction.orbitRel.Quotient G ℍ` for the image `G` of `Γ` in `Equiv.Perm ℍ`
(this removes `±1`, so `G` acts freely); `G` acts properly discontinuously (`IsFuchsian`), so Mathlib's
`MulAction.instChartedSpaceQuotient`, `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul` and
`t2Space_of_properlyDiscontinuousSMul_of_t2Space` give charts, the covering and `T2`; the chart transitions are locally
Möbius maps, hence analytic (`IsManifold 𝓘(ℂ) ω`). The later pieces F1–F4 are stated for an arbitrary `(S, p)` with
`IsUniformization Γ p`, so only this existential statement is consumed.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- `-1 ∈ SL(2, ℝ)` acts trivially on `ℍ`. -/
theorem ft0_neg_one_smul (x : UpperHalfPlane) : ((-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • x) = x := by
  ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

/-- A Möbius map `z ↦ γ • z` of `SL(2, ℝ)`, read in `ℂ` through `ofComplex`, is analytic near every point of the
upper half plane. -/
theorem ft0_mobius_contDiffAt (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℂ ω (fun z' : ℂ => ((γ • UpperHalfPlane.ofComplex z' : UpperHalfPlane) : ℂ)) z := by
  have hev : (fun z' : ℂ => ((γ • UpperHalfPlane.ofComplex z' : UpperHalfPlane) : ℂ)) =ᶠ[𝓝 z]
      fun z' => ((γ 0 0 : ℂ) * z' + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z' + (γ 1 1 : ℂ)) := by
    filter_upwards [(Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds hz] with z' hz'
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    simp
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have hden : (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.zero_im] at him
    have hc : γ 1 0 = 0 := by
      rcases mul_eq_zero.1 him with h | h
      · exact h
      · exact absurd h hz.ne'
    have hre := congrArg Complex.re h0
    simp only [hc, Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_re, Complex.zero_re] at hre
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    simp [hc, hre] at hdet
  exact ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const).div
    ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const) hden

/-- **F0.** For a Fuchsian group `Γ` acting freely up to `±1` there are a Riemann surface `S` and a holomorphic covering
`p : ℍ → S` whose fibres are the `Γ`-orbits. -/
theorem ft0_quotient (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) :
    ∃ (S : Type) (_ : TopologicalSpace S) (_ : ChartedSpace ℂ S) (_ : T2Space S)
      (_ : ConnectedSpace S) (_ : IsManifold 𝓘(ℂ) ω S) (p : UpperHalfPlane → S), IsUniformization Γ p := by
  classical
  -- the image `G` of `Γ` in `Perm ℍ` (this kills `±1`)
  set φ := MulAction.toPermHom Γ UpperHalfPlane with hφ
  set G := φ.range with hG
  have hσ : ∀ σ : G, ∃ γ ∈ Γ, ∀ x : UpperHalfPlane, σ • x = γ • x := by
    rintro ⟨σ, γ, rfl⟩
    exact ⟨γ, γ.2, fun x => rfl⟩
  have hγσ : ∀ γ ∈ Γ, ∃ σ : G, ∀ x : UpperHalfPlane, σ • x = γ • x :=
    fun γ hγ => ⟨φ.rangeRestrict ⟨γ, hγ⟩, fun x => rfl⟩
  -- `G` acts properly discontinuously
  have hpd : ProperlyDiscontinuousSMul G UpperHalfPlane := ⟨fun {K L} hK hL => by
    have hfin := hΓ _ (hK.union hL)
    have hB : {γ : Γ | ((fun x => (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • x) '' (K ∪ L) ∩
        (K ∪ L)).Nonempty}.Finite :=
      (hfin.preimage Subtype.val_injective.injOn).subset fun γ hγ => ⟨γ.2, hγ⟩
    refine (hB.image φ.rangeRestrict).subset ?_
    rintro ⟨σ, γ, rfl⟩ ⟨_, ⟨k, hk, rfl⟩, hkL⟩
    exact ⟨γ, ⟨γ • k, ⟨k, Or.inl hk, rfl⟩, Or.inr hkL⟩, rfl⟩⟩
  -- `G` acts by homeomorphisms
  have hcont : ContinuousConstSMul G UpperHalfPlane := ⟨fun σ => by
    obtain ⟨γ, -, h⟩ := hσ σ
    have : (fun x : UpperHalfPlane => σ • x) = fun x => γ • x := funext h
    rw [this]
    exact continuous_const_smul γ⟩
  -- `G` acts freely
  have hcancel : IsCancelSMul G UpperHalfPlane := by
    refine isCancelSMul_iff_eq_one_of_smul_eq.2 fun σ c h => ?_
    obtain ⟨γ, hγ, hγx⟩ := hσ σ
    have htriv : ∀ x : UpperHalfPlane, σ • x = x := by
      intro x
      rw [hγx x]
      rcases hfree γ hγ c (by rw [← hγx]; exact h) with h1 | h1
      · rw [h1, one_smul]
      · rw [h1, ft0_neg_one_smul]
    exact Subtype.ext (Equiv.ext fun x => htriv x)
  -- the quotient and its projection
  let p : UpperHalfPlane → MulAction.orbitRel.Quotient G UpperHalfPlane := Quotient.mk _
  have hcov : IsCoveringMap p := isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
  have hloc : IsLocalHomeomorph p := hcov.isLocalHomeomorph
  have hporb : ∀ (σ : G) (x : UpperHalfPlane), p (σ • x) = p x := fun σ x => Quotient.sound ⟨σ, rfl⟩
  -- the local inverses of `p`, read in `ℂ`, are locally Möbius maps
  have key : ∀ (x₀ : UpperHalfPlane) (z : ℂ), 0 < z.im →
      p (UpperHalfPlane.ofComplex z) ∈ (hloc.localInverseAt x₀).source →
      ContDiffAt ℂ ω (fun z' : ℂ => ((hloc.localInverseAt x₀ (p (UpperHalfPlane.ofComplex z')) :
        UpperHalfPlane) : ℂ)) z := by
    intro x₀ z hz hs
    set L := hloc.localInverseAt x₀ with hL
    have hu : p (L (p (UpperHalfPlane.ofComplex z))) = p (UpperHalfPlane.ofComplex z) :=
      hloc.apply_localInverseAt_of_mem hs
    obtain ⟨σ₀, hσ₀⟩ := Quotient.exact hu
    obtain ⟨γ₀, -, hγ₀⟩ := hσ σ₀
    have hcz : ContinuousAt UpperHalfPlane.ofComplex z :=
      UpperHalfPlane.ofComplex.continuousAt (by simpa [UpperHalfPlane.ofComplex] using hz)
    have hpz : ContinuousAt (fun z' => p (UpperHalfPlane.ofComplex z')) z := hcov.continuous.continuousAt.comp hcz
    have hf1 : ContinuousAt (fun z' => L (p (UpperHalfPlane.ofComplex z'))) z :=
      (L.continuousAt hs).comp (f := fun z' => p (UpperHalfPlane.ofComplex z')) hpz
    have hf2 : ContinuousAt (fun z' => γ₀ • UpperHalfPlane.ofComplex z') z :=
      (continuous_const_smul γ₀).continuousAt.comp hcz
    have hmem : L (p (UpperHalfPlane.ofComplex z)) ∈ L.target := L.map_source hs
    have h2z : γ₀ • UpperHalfPlane.ofComplex z = L (p (UpperHalfPlane.ofComplex z)) := by
      rw [← hγ₀]
      exact hσ₀
    have hev : (fun z' : ℂ => ((L (p (UpperHalfPlane.ofComplex z')) : UpperHalfPlane) : ℂ)) =ᶠ[𝓝 z]
        fun z' => ((γ₀ • UpperHalfPlane.ofComplex z' : UpperHalfPlane) : ℂ) := by
      have e1 := hf1.preimage_mem_nhds (L.open_target.mem_nhds hmem)
      have e2 := hf2.preimage_mem_nhds (L.open_target.mem_nhds (h2z ▸ hmem))
      have e3 := hpz.preimage_mem_nhds (L.open_source.mem_nhds hs)
      filter_upwards [e1, e2, e3] with z' h1 h2 h3
      congr 1
      refine hloc.injOn_localInverseAt_target h1 h2 ?_
      rw [hloc.apply_localInverseAt_of_mem h3, ← hγ₀, hporb]
    exact (ft0_mobius_contDiffAt γ₀ hz).congr_of_eventuallyEq hev
  -- the charts of the quotient are `L x₀ ≫ coe`
  have hatlas : ∀ e ∈ atlas ℂ (MulAction.orbitRel.Quotient G UpperHalfPlane),
      ∃ x₀ : UpperHalfPlane, e = (hloc.localInverseAt x₀).trans (chartAt ℂ x₀) := by
    rintro e ⟨q, rfl⟩
    exact ⟨_, rfl⟩
  have hchart : ∀ q : MulAction.orbitRel.Quotient G UpperHalfPlane,
      ∃ x₀ : UpperHalfPlane, chartAt ℂ q = (hloc.localInverseAt x₀).trans (chartAt ℂ x₀) :=
    fun q => ⟨_, rfl⟩
  -- the inverse of a chart is `p ∘ ofComplex`
  have hsymm : ∀ x₀ : UpperHalfPlane, ∀ z : ℂ,
      ((hloc.localInverseAt x₀).trans (chartAt ℂ x₀)).symm z = p (UpperHalfPlane.ofComplex z) := by
    intro x₀ z
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans,
      Function.comp_apply, IsLocalHomeomorph.localInverseAt_symm]
    rfl
  have htarget : ∀ x₀ : UpperHalfPlane, ∀ z ∈ ((hloc.localInverseAt x₀).trans (chartAt ℂ x₀)).target,
      0 < z.im := by
    intro x₀ z hz
    rw [OpenPartialHomeomorph.trans_target] at hz
    obtain ⟨τ, -, rfl⟩ := hz.1
    exact τ.im_pos
  -- analytic transitions
  have hman : IsManifold 𝓘(ℂ) ω (MulAction.orbitRel.Quotient G UpperHalfPlane) := by
    refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
    obtain ⟨a, rfl⟩ := hatlas e he
    obtain ⟨b, rfl⟩ := hatlas e' he'
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id, Set.inter_univ,
      Set.preimage_id_eq, Function.id_comp, Function.comp_id]
    intro z hz
    rw [OpenPartialHomeomorph.trans_source] at hz
    have hz1 : z ∈ ((hloc.localInverseAt a).trans (chartAt ℂ a)).target := hz.1
    have hz2 := hz.2
    rw [Set.mem_preimage, hsymm, OpenPartialHomeomorph.trans_source] at hz2
    have hfun : ⇑(((hloc.localInverseAt a).trans (chartAt ℂ a)).symm ≫ₕ
        (hloc.localInverseAt b).trans (chartAt ℂ b)) =
        fun z' : ℂ => ((hloc.localInverseAt b (p (UpperHalfPlane.ofComplex z')) : UpperHalfPlane) : ℂ) := by
      funext z'
      rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hsymm]
      rfl
    rw [hfun]
    exact (key b z (htarget a z hz1) hz2.1).contDiffWithinAt
  -- `p` is holomorphic
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) p := by
    intro x
    refine ContMDiffAt.mdifferentiableAt (n := ω) ?_ (by simp)
    rw [contMDiffAt_iff]
    refine ⟨hcov.continuous.continuousAt, ?_⟩
    obtain ⟨x₀, hx₀⟩ := hchart (p x)
    have hs : p (UpperHalfPlane.ofComplex (x : ℂ)) ∈ (hloc.localInverseAt x₀).source := by
      rw [UpperHalfPlane.ofComplex_apply]
      have h := mem_chart_source ℂ (p x)
      rw [hx₀, OpenPartialHomeomorph.trans_source] at h
      exact h.1
    have hk := key x₀ x x.im_pos hs
    have hfun : (extChartAt 𝓘(ℂ) (p x) ∘ p ∘ (extChartAt 𝓘(ℂ) x).symm) =
        fun z' : ℂ => ((hloc.localInverseAt x₀ (p (UpperHalfPlane.ofComplex z')) : UpperHalfPlane) : ℂ) := by
      funext z'
      simp only [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
        PartialEquiv.trans_refl, OpenPartialHomeomorph.toFun_eq_coe, Function.comp_apply,
        OpenPartialHomeomorph.coe_toPartialEquiv_symm, hx₀]
      rfl
    rw [hfun]
    simpa using hk.contDiffWithinAt
  refine ⟨MulAction.orbitRel.Quotient G UpperHalfPlane, inferInstance, inferInstance, inferInstance,
    inferInstance, hman, p, hcov, hmd, fun q => Quotient.inductionOn q fun x => ⟨x, rfl⟩, ?_⟩
  intro τ₁ τ₂
  constructor
  · intro h
    obtain ⟨σ, hσ'⟩ := Quotient.exact h
    obtain ⟨γ, hγ, hγx⟩ := hσ σ
    refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
    have hσ'' : σ • τ₂ = τ₁ := hσ'
    rw [← hσ'', hγx, inv_smul_smul]
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨σ, hσx⟩ := hγσ γ hγ
    rw [← hσx, hporb]

end LiZhongQC
