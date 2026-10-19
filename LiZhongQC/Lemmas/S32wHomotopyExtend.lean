import LiZhongQC.Ch09.S31_FiniteType
import LiZhongQC.Lemmas.LowGenusQC
import LiZhongQC.Lemmas.Winding

/-!
# (b6) Homotopies of the punctured doubles extend to the closed doubles (`s32wh_`, conjunct 4 of
`symmetric_extension_properties`)

Two homeomorphisms `fd, fd' : X₀ → X₁` of closed Riemann surfaces of genus `G` that restrict to homotopic
homeomorphisms `fdp ≃ fdp'` of the punctured surfaces `Xᵢ ∖ Pᵢ` are homotopic (for `G = 0` we need `|P₀| ≥ 3`:
`z ↦ 1/z̄` on `ℂ̂` with `P = {0, ∞}` is homotopic to `id` on `ℂ*` but not on `ℂ̂`).
Purely topological: no quasiconformality is used.
* `G ≥ 1`: lift to the universal covers `Eᵢ` (`ℍ`, resp. `ℂ`); lift the punctured homotopy over the connected dense
  `p₀⁻¹(X₀ ∖ P₀)` (`s32wh_deck_transfer`): the deck correspondences of `F` and of `δ ∘ F'` agree. Then
  `thm23_1_homotopy_iff` (`G ≥ 2`), resp. the equivariant straight-line homotopy (`G = 1`).
* `G = 0`: `ψ = fd'⁻¹ ∘ fd` is homotopic to `id` off `P₀`; in a sphere model with three punctures at `0, 1, ∞` the
  winding of small circles about each finite puncture is preserved, so `ψ` fixes every puncture with local winding
  `+1` (`s32wh_sphere_core`), and `s24q_sp_core` gives `ψ ≃ id`.
-/

open Complex Set Filter Topology
open scoped Pointwise ContDiff Manifold Real

noncomputable section

namespace LiZhongQC

universe u

/-- The upper half-plane is homeomorphic to `ℂ` (`τ ↦ re τ + i log (im τ)`). -/
theorem s32wh_hp_homeomorph : Nonempty (UpperHalfPlane ≃ₜ ℂ) := by
  have him : ∀ z : ℂ, 0 < (((z.re : ℂ) + (Real.exp z.im : ℂ) * I)).im := fun z => by
    simp [-Complex.ofReal_exp, Real.exp_pos]
  refine ⟨{ toFun := fun τ => ((τ : ℂ).re : ℂ) + (Real.log (τ : ℂ).im : ℂ) * I
            invFun := fun z => UpperHalfPlane.mk ((z.re : ℂ) + (Real.exp z.im : ℂ) * I) (him z)
            left_inv := fun τ => ?_
            right_inv := fun z => ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }⟩
  · apply UpperHalfPlane.ext
    apply Complex.ext
    · simp
    · simp [-Complex.ofReal_exp, Real.exp_log τ.im_pos]
  · apply Complex.ext
    · simp [-Complex.ofReal_exp]
    · simp [-Complex.ofReal_exp]
  · have h1 : Continuous fun τ : UpperHalfPlane => (τ : ℂ) := UpperHalfPlane.continuous_coe
    have h2 : Continuous fun τ : UpperHalfPlane => Real.log (τ : ℂ).im :=
      (Complex.continuous_im.comp h1).log fun τ => τ.coe_im_pos.ne'
    exact (Complex.continuous_ofReal.comp (Complex.continuous_re.comp h1)).add
      ((Complex.continuous_ofReal.comp h2).mul continuous_const)
  · refine Continuous.upperHalfPlaneMk ?_ him
    exact (Complex.continuous_ofReal.comp Complex.continuous_re).add
      ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp Complex.continuous_im)).mul continuous_const)

/-- The complement of a countable set in a space homeomorphic to `ℂ` is preconnected. -/
theorem s32wh_compl_countable_preconnected {E : Type*} [TopologicalSpace E] (Φ : E ≃ₜ ℂ) {C : Set E}
    (hC : C.Countable) : IsPreconnected Cᶜ := by
  have h1 : IsPreconnected ((Φ '' C)ᶜ) :=
    ((hC.image Φ).isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected
  have h2 : (Φ.symm : ℂ → E) '' (Φ '' C)ᶜ = Cᶜ := by
    rw [Set.image_compl_eq Φ.symm.bijective]
    congr 1
    ext x
    simp
  rw [← h2]
  exact h1.image _ Φ.symm.continuous.continuousOn

/-- A finite subset of a charted space over `ℂ` has empty interior. -/
theorem s32wh_finite_interior {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] {P : Set X}
    (hP : P.Finite) : interior P = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  have hV : (chartAt ℂ x) '' interior P ∈ 𝓝 (chartAt ℂ x x) :=
    (chartAt ℂ x).image_mem_nhds (mem_chart_source ℂ x) (isOpen_interior.mem_nhds hx)
  exact infinite_of_mem_nhds _ hV ((hP.image _).subset (image_mono interior_subset))

/-- The preimage of a finite set with empty interior under a covering map with second countable total space is
countable, and its complement is dense. -/
theorem s32wh_cover_preimage {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [SecondCountableTopology E]
    {p : E → X} (hp : IsCoveringMap p) {P : Set X} (hP : P.Finite) (hPi : interior P = ∅) :
    (p ⁻¹' P).Countable ∧ Dense (p ⁻¹' P)ᶜ := by
  refine ⟨?_, ?_⟩
  · rw [← Set.biUnion_preimage_singleton]
    refine hP.countable.biUnion fun x _ => ?_
    have : DiscreteTopology (p ⁻¹' {x}) := (hp x).discreteTopology_fiber
    have : SecondCountableTopology (p ⁻¹' {x}) := inferInstance
    have : Countable (p ⁻¹' {x}) := (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
    exact Set.countable_coe_iff.1 this
  · rw [← interior_eq_empty_iff_dense_compl]
    have h1 : p '' interior (p ⁻¹' P) ⊆ interior P :=
      interior_maximal ((image_mono interior_subset).trans (image_preimage_subset p P))
        (hp.isOpenMap _ isOpen_interior)
    rw [hPi, subset_empty_iff, image_eq_empty] at h1
    exact h1

/-- **Deck transfer along a punctured homotopy.**  `F, F'` lift `fd, fd'` to coverings, `fd ≃ fd'` off the
punctures, and `A = p₀⁻¹(X₀ ∖ P₀)` is preconnected and dense.  Then for a suitable deck map `D i₁` of `p₁`, the
deck correspondence of `D i₁ ∘ F'` is that of `F`: whenever `F ∘ γ = δ ∘ F` with `p₀ ∘ γ = p₀` and
`p₁ ∘ δ = p₁`, also `D i₁ ∘ F' ∘ γ = δ ∘ D i₁ ∘ F'`.  (Lift the homotopy on `I × A` from `F`; its end is
`D i₁ ∘ F'` on `A` by uniqueness of lifts; the `γ`-relation is constant in `t`; density of `A`.) -/
theorem s32wh_deck_transfer {E₀ E₁ X₀ X₁ : Type*} [TopologicalSpace E₀] [TopologicalSpace E₁] [T2Space E₁]
    [TopologicalSpace X₀] [T2Space X₀] [TopologicalSpace X₁] [T2Space X₁]
    {p₀ : E₀ → X₀} (hp₀ : Continuous p₀) {p₁ : E₁ → X₁} (hp₁ : IsCoveringMap p₁)
    {P₀ : Finset X₀} {P₁ : Finset X₁}
    (hA : IsPreconnected {e | p₀ e ∉ P₀}) (hAne : {e | p₀ e ∉ P₀}.Nonempty) (hAd : Dense {e | p₀ e ∉ P₀})
    {fd fd' : X₀ ≃ₜ X₁} {fdp fdp' : puncturedOpens P₀ ≃ₜ puncturedOpens P₁}
    (hfdp : ∀ y, (fdp y : X₁) = fd y) (hfdp' : ∀ y, (fdp' y : X₁) = fd' y)
    (hhom : ContinuousMap.Homotopic (fdp : C(puncturedOpens P₀, puncturedOpens P₁))
      (fdp' : C(puncturedOpens P₀, puncturedOpens P₁)))
    {F F' : E₀ → E₁} (hF : Continuous F) (hF' : Continuous F')
    (hFl : ∀ e, p₁ (F e) = fd (p₀ e)) (hF'l : ∀ e, p₁ (F' e) = fd' (p₀ e))
    {ι : Type*} (D : ι → E₁ → E₁) (hDc : ∀ i, Continuous (D i)) (hDp : ∀ i y, p₁ (D i y) = p₁ y)
    (hDt : ∀ y y', p₁ y = p₁ y' → ∃ i, D i y = y') :
    ∃ i₁, ∀ γ : E₀ → E₀, Continuous γ → (∀ e, p₀ (γ e) = p₀ e) → ∀ δ : E₁ → E₁, Continuous δ →
      (∀ y, p₁ (δ y) = p₁ y) → (∀ e, F (γ e) = δ (F e)) → ∀ e, D i₁ (F' (γ e)) = δ (D i₁ (F' e)) := by
  classical
  set A : Set E₀ := {e | p₀ e ∉ P₀} with hAdef
  have : PreconnectedSpace A := Subtype.preconnectedSpace hA
  obtain ⟨H⟩ := hhom
  have hmem : ∀ a : A, p₀ a ∈ puncturedOpens P₀ := fun a => a.2
  set ι₀ : A → puncturedOpens P₀ := fun a => ⟨p₀ a, hmem a⟩ with hι₀
  have hι₀c : Continuous ι₀ := (hp₀.comp continuous_subtype_val).subtype_mk _
  set H' : C(unitInterval × A, X₁) := ⟨fun x => ((H (x.1, ι₀ x.2) : puncturedOpens P₁) : X₁),
    continuous_subtype_val.comp (H.continuous.comp (continuous_fst.prodMk (hι₀c.comp continuous_snd)))⟩ with hH'
  set f₀ : C(A, E₁) := ⟨fun a => F a, hF.comp continuous_subtype_val⟩ with hf₀
  have H_0 : ∀ a, H' (0, a) = p₁ (f₀ a) := fun a => by
    show ((H (0, ι₀ a) : puncturedOpens P₁) : X₁) = p₁ (F a)
    rw [H.apply_zero, hFl]
    exact hfdp _
  set K := hp₁.liftHomotopy H' f₀ H_0 with hK
  have hK0 : ∀ a, K (0, a) = F a := fun a => hp₁.liftHomotopy_zero H' f₀ H_0 a
  have hKl : ∀ t a, p₁ (K (t, a)) = H' (t, a) := fun t a =>
    congrFun (hp₁.liftHomotopy_lifts H' f₀ H_0) (t, a)
  have hK1 : ∀ a : A, p₁ (K (1, a)) = p₁ (F' a) := fun a => by
    rw [hKl, hF'l]
    show ((H (1, ι₀ a) : puncturedOpens P₁) : X₁) = _
    rw [H.apply_one]
    exact hfdp' _
  obtain ⟨e₀, he₀⟩ := hAne
  set a₀ : A := ⟨e₀, he₀⟩
  obtain ⟨i₁, hi₁⟩ := hDt (F' a₀) (K (1, a₀)) (hK1 a₀).symm
  have hcK1 : Continuous fun a : A => K (1, a) := K.continuous.comp (continuous_const.prodMk continuous_id)
  have hend : ∀ a : A, K (1, a) = D i₁ (F' a) := by
    have h := hp₁.eq_of_comp_eq hcK1 ((hDc i₁).comp (hF'.comp continuous_subtype_val))
      (funext fun a => by simp only [Function.comp_apply]; rw [hK1, hDp]) a₀ hi₁.symm
    exact fun a => congrFun h a
  refine ⟨i₁, fun γ hγ hpγ δ hδ hpδ hFγ => ?_⟩
  have hγA : ∀ a : A, γ a ∈ A := fun a => by
    show p₀ (γ a) ∉ P₀
    rw [hpγ]; exact a.2
  set γA : A → A := fun a => ⟨γ a, hγA a⟩ with hγAdef
  have hγAc : Continuous γA := (hγ.comp continuous_subtype_val).subtype_mk _
  have hι₀γ : ∀ a, ι₀ (γA a) = ι₀ a := fun a => Subtype.ext (hpγ a)
  have hk : (fun x : unitInterval × A => K (x.1, γA x.2)) = fun x => δ (K x) := by
    refine hp₁.eq_of_comp_eq (K.continuous.comp (continuous_fst.prodMk (hγAc.comp continuous_snd)))
      (hδ.comp K.continuous) (funext fun x => ?_) (0, a₀) ?_
    · simp only [Function.comp_apply]
      rw [hpδ, hKl, hKl]
      show ((H (x.1, ι₀ (γA x.2)) : puncturedOpens P₁) : X₁) = ((H (x.1, ι₀ x.2) : puncturedOpens P₁) : X₁)
      rw [hι₀γ]
    · show K (0, γA a₀) = δ (K (0, a₀))
      rw [hK0, hK0]
      exact hFγ e₀
  have hA' : ∀ e ∈ A, D i₁ (F' (γ e)) = δ (D i₁ (F' e)) := fun e he => by
    have h := congrFun hk (1, ⟨e, he⟩)
    simp only at h
    rw [hend, hend] at h
    exact h
  have hcl : IsClosed {e | D i₁ (F' (γ e)) = δ (D i₁ (F' e))} :=
    isClosed_eq ((hDc i₁).comp (hF'.comp hγ)) (hδ.comp ((hDc i₁).comp hF'))
  intro e
  have : e ∈ closure A := by rw [hAd.closure_eq]; exact mem_univ e
  exact hcl.closure_subset_iff.2 hA' this

/-- **(b6), genus `≥ 2`**: uniformize the closed surfaces by `ℍ`, transfer the deck correspondence
(`s32wh_deck_transfer` with `D γ = γ • ·`, `γ ∈ Γ₁`) and apply `thm23_1_homotopy_iff`. -/
theorem s32wh_genus_ge_two {X₀ X₁ : ClosedRS.{u}} {G : ℕ} (hG : 1 < G) (h₀ : HasGenus X₀.carrier G)
    (h₁ : HasGenus X₁.carrier G) {P₀ : Finset X₀.carrier} {P₁ : Finset X₁.carrier}
    {fd fd' : X₀.carrier ≃ₜ X₁.carrier} {fdp fdp' : puncturedOpens P₀ ≃ₜ puncturedOpens P₁}
    (hfdp : ∀ y, (fdp y : X₁.carrier) = fd y) (hfdp' : ∀ y, (fdp' y : X₁.carrier) = fd' y)
    (hhom : ContinuousMap.Homotopic (fdp : C(puncturedOpens P₀, puncturedOpens P₁))
      (fdp' : C(puncturedOpens P₀, puncturedOpens P₁))) :
    ContinuousMap.Homotopic (fd : C(X₀.carrier, X₁.carrier)) (fd' : C(X₀.carrier, X₁.carrier)) := by
  classical
  obtain ⟨Γ₀, p₀, -, -, hp₀⟩ := s22hg_exists_fuchsian_uniformization hG h₀
  obtain ⟨Γ₁, p₁, -, -, hp₁⟩ := s22hg_exists_fuchsian_uniformization hG h₁
  obtain ⟨τ₀⟩ : Nonempty UpperHalfPlane := inferInstance
  obtain ⟨τ₁, hτ₁⟩ := hp₁.2.2.1 (fd (p₀ τ₀))
  obtain ⟨F, hF, -⟩ := exists_lift hp₀ hp₁ fd τ₀ τ₁ hτ₁
  obtain ⟨τ₁', hτ₁'⟩ := hp₁.2.2.1 (fd' (p₀ τ₀))
  obtain ⟨F', hF', -⟩ := exists_lift hp₀ hp₁ fd' τ₀ τ₁' hτ₁'
  have : SecondCountableTopology UpperHalfPlane := UpperHalfPlane.isEmbedding_coe.secondCountableTopology
  obtain ⟨hcount, hdense⟩ := s32wh_cover_preimage hp₀.1 P₀.finite_toSet
    (s32wh_finite_interior P₀.finite_toSet)
  obtain ⟨Φ⟩ := s32wh_hp_homeomorph
  have hApre : IsPreconnected {e | p₀ e ∉ P₀} := s32wh_compl_countable_preconnected Φ hcount
  obtain ⟨i₁, htr⟩ := s32wh_deck_transfer hp₀.1.continuous hp₁.1 hApre hdense.nonempty hdense hfdp hfdp' hhom
    F.continuous F'.continuous hF hF' (fun (i : Γ₁) (y : UpperHalfPlane) => (i : Matrix.SpecialLinearGroup (Fin 2) ℝ) • y)
    (fun i => continuous_const_smul _) (fun i y => ((hp₁.2.2.2 y _).2 ⟨i, i.2, rfl⟩).symm)
    (fun y y' h => by
      obtain ⟨γ, hγ, hγe⟩ := (hp₁.2.2.2 y y').1 h
      exact ⟨⟨γ, hγ⟩, hγe⟩)
  refine (thm23_1_homotopy_iff hp₀ hp₁ fd fd' hF hF').2
    ⟨(i₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ), i₁.2, fun γ hγ τ => ?_⟩
  obtain ⟨δ, hδ, hFδ⟩ := h23l_deck hp₀ hp₁ hF hγ
  have h := htr (fun e => γ • e) (continuous_const_smul γ)
    (fun e => ((hp₀.2.2.2 e (γ • e)).2 ⟨γ, hγ, rfl⟩).symm) (fun y => δ • y) (continuous_const_smul δ)
    (fun y => ((hp₁.2.2.2 y (δ • y)).2 ⟨δ, hδ, rfl⟩).symm) hFδ
    (F'.symm ((i₁ : Matrix.SpecialLinearGroup (Fin 2) ℝ)⁻¹ • τ))
  rw [hFδ, F.apply_symm_apply, h, F'.apply_symm_apply, smul_inv_smul]

/-- **(b6), genus `1`**: the torus covers `ℂ → Xᵢ`; the lifts `F` and `F' + c` have the same linear part
(`s32wh_deck_transfer` with the lattice translations), and both maps are homotopic to the same affine
representative (`s24q_tq_homotopy`). -/
theorem s32wh_genus_one {X₀ X₁ : ClosedRS.{u}} (h₀ : HasGenus X₀.carrier 1)
    (h₁ : HasGenus X₁.carrier 1) {P₀ : Finset X₀.carrier} {P₁ : Finset X₁.carrier}
    {fd fd' : X₀.carrier ≃ₜ X₁.carrier} {fdp fdp' : puncturedOpens P₀ ≃ₜ puncturedOpens P₁}
    (hfdp : ∀ y, (fdp y : X₁.carrier) = fd y) (hfdp' : ∀ y, (fdp' y : X₁.carrier) = fd' y)
    (hhom : ContinuousMap.Homotopic (fdp : C(puncturedOpens P₀, puncturedOpens P₁))
      (fdp' : C(puncturedOpens P₀, puncturedOpens P₁))) :
    ContinuousMap.Homotopic (fd : C(X₀.carrier, X₁.carrier)) (fd' : C(X₀.carrier, X₁.carrier)) := by
  classical
  obtain ⟨L₀, p₀, hc₀, -, hs₀, hf₀⟩ := s24q_torus_cover h₀
  obtain ⟨L₁, p₁, hc₁, -, hs₁, hf₁⟩ := s24q_torus_cover h₁
  obtain ⟨F, hF⟩ := s24q_tq_homeo hc₀ hs₀ hf₀ hc₁ hs₁ hf₁ fd
  obtain ⟨F', hF'⟩ := s24q_tq_homeo hc₀ hs₀ hf₀ hc₁ hs₁ hf₁ fd'
  have hp₀l : ∀ z, ∀ l ∈ L₀.lattice, p₀ (z + l) = p₀ z := fun z l hl => (hf₀ _ _).2 (by simpa using hl)
  have hp₁l : ∀ z, ∀ l ∈ L₁.lattice, p₁ (z + l) = p₁ z := fun z l hl => (hf₁ _ _).2 (by simpa using hl)
  obtain ⟨A, hA1, hFA⟩ := s24q_tq_equivariant hf₁ F.continuous (L₀ := L₀) (fun z l hl => by
    rw [hF, hF, hp₀l z l hl])
  obtain ⟨hcount, hdense⟩ := s32wh_cover_preimage hc₀ P₀.finite_toSet (s32wh_finite_interior P₀.finite_toSet)
  have hApre : IsPreconnected {e | p₀ e ∉ P₀} :=
    s32wh_compl_countable_preconnected (Homeomorph.refl ℂ) hcount
  obtain ⟨i₁, htr⟩ := s32wh_deck_transfer hc₀.continuous hc₁ hApre hdense.nonempty hdense hfdp hfdp' hhom
    F.continuous F'.continuous hF hF' (fun (l : L₁.lattice) (y : ℂ) => y + l)
    (fun l => continuous_id.add continuous_const) (fun l y => hp₁l y l l.2)
    (fun y y' h => ⟨⟨y' - y, (hf₁ y' y).1 h.symm⟩, by simp⟩)
  set c : ℂ := i₁.1 with hc
  have hcL : c ∈ L₁.lattice := i₁.2
  have hF'A : ∀ z, ∀ l ∈ L₀.lattice, F' (z + l) + c = F' z + c + A l := fun z l hl =>
    htr (fun e => e + l) (continuous_id.add continuous_const) (fun e => hp₀l e l hl) (fun y => y + A l)
      (continuous_id.add continuous_const) (fun y => hp₁l y (A l) (hA1 l hl)) (fun e => hFA e l hl) z
  -- the equivariant straight-line homotopy from `F` to `F' + c`
  set φ : unitInterval × ℂ → ℂ := fun x => (1 - ((x.1 : ℝ) : ℂ)) * F x.2 + ((x.1 : ℝ) : ℂ) * (F' x.2 + c)
    with hφ
  have ht : Continuous fun x : unitInterval × ℂ => ((x.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
  have hφc : Continuous φ :=
    ((continuous_const.sub ht).mul (F.continuous.comp continuous_snd)).add
      (ht.mul ((F'.continuous.comp continuous_snd).add continuous_const))
  have hcomp : ∀ (t : unitInterval) z w, p₀ z = p₀ w → p₁ (φ (t, z)) = p₁ (φ (t, w)) := by
    intro t z w h
    obtain ⟨l, hl, rfl⟩ : ∃ l ∈ L₀.lattice, z = w + l := ⟨z - w, (hf₀ z w).1 h, by ring⟩
    have e : φ (t, w + l) = φ (t, w) + A l := by
      simp only [hφ]
      rw [hFA w l hl, hF'A w l hl]
      ring
    rw [e, hp₁l _ _ (hA1 l hl)]
  obtain ⟨q, hqc, hq⟩ := s24q_tq_descend2 hc₀.continuous hs₀ hc₀.isOpenMap hc₁.continuous hφc hcomp
  refine ⟨⟨⟨q, hqc⟩, fun x => ?_, fun x => ?_⟩⟩
  · obtain ⟨z, rfl⟩ := hs₀ x
    show q (0, p₀ z) = fd (p₀ z)
    rw [hq, ← hF z]
    congr 1
    simp [hφ]
  · obtain ⟨z, rfl⟩ := hs₀ x
    show q (1, p₀ z) = fd' (p₀ z)
    rw [hq, ← hF' z, ← hp₁l (F' z) c hcL]
    congr 1
    simp [hφ]

/-- The finite chart of `ℂ̂` along a continuous map avoiding `∞` is continuous and recovers the map. -/
theorem s32wh_sphere_fin {Y : Type*} [TopologicalSpace Y] {g : Y → OnePoint ℂ} (hg : Continuous g)
    (hgi : ∀ y, g y ≠ OnePoint.infty) :
    Continuous (fun y => RiemannDynamics.sphereChartFinite (g y)) ∧
      ∀ y, ((RiemannDynamics.sphereChartFinite (g y) : ℂ) : OnePoint ℂ) = g y := by
  refine ⟨RiemannDynamics.sphereChartFinite.continuousOn.comp_continuous hg (fun y => by
    rw [RiemannDynamics.sphereChartFinite_source]; exact hgi y), fun y => ?_⟩
  obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp (hgi y)
  rw [← hw, RiemannDynamics.sphereChartFinite_coe]

/-- Isolation of a point from the other finite points of a finite subset of `ℂ̂`. -/
theorem s32wh_sphere_radius (P : Finset (OnePoint ℂ)) (a : ℂ) :
    ∃ ρ₁ > 0, ∀ z : ℂ, z ≠ a → ‖z - a‖ < ρ₁ → ((z : ℂ) : OnePoint ℂ) ∉ P := by
  classical
  have hS : ({z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ P} \ {a}).Finite :=
    ((P.finite_toSet.preimage (OnePoint.coe_injective.injOn))).sdiff
  have hn : ({z : ℂ | ((z : ℂ) : OnePoint ℂ) ∈ P} \ {a})ᶜ ∈ 𝓝 a :=
    hS.isClosed.isOpen_compl.mem_nhds (fun h => h.2 rfl)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hn
  refine ⟨ε, hε, fun z hza hz hzP => hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hz) ⟨hzP, hza⟩⟩

/-- The circle `t ↦ a + ρ e^{2πit}`: continuous, closed, at distance `ρ` from `a`, with winding `2πi` about `a`. -/
theorem s32wh_circle (a : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (fun t : ℝ => a + ρ * Complex.exp (2 * π * Complex.I * t)) ∧
      (a + ρ * Complex.exp (2 * π * Complex.I * ((1 : ℝ) : ℂ)) = a + ρ * Complex.exp (2 * π * Complex.I * ((0 : ℝ) : ℂ))) ∧
      (∀ t : ℝ, ‖(a + ρ * Complex.exp (2 * π * Complex.I * t)) - a‖ = ρ) ∧
      ∃ M : ℝ → ℂ, ContinuousOn M (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (M t) = (a + ρ * Complex.exp (2 * π * Complex.I * t)) - a) ∧
        M 1 - M 0 = 2 * π * Complex.I := by
  refine ⟨continuous_const.add (continuous_const.mul (Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal))), ?_, fun t => ?_, ?_⟩
  · simp [Complex.exp_two_pi_mul_I]
  · rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    have : 2 * π * Complex.I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]
  · refine ⟨fun t => (Real.log ρ : ℂ) + 2 * π * Complex.I * t, (continuous_const.add
      (continuous_const.mul Complex.continuous_ofReal)).continuousOn, fun t _ => ?_, ?_⟩
    · rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hρ]
      ring
    · push_cast; ring

/-- **Homotopy invariance of the winding about the punctures.**  If `hp ≃ id` on `ℂ̂ ∖ P` (`∞ ∈ P`), a closed curve
`c` in `ℂ ∖ P` and its image under `h` wind equally about every finite puncture `q`. -/
theorem s32wh_sphere_W {P : Finset (OnePoint ℂ)} (hinfP : (OnePoint.infty : OnePoint ℂ) ∈ P)
    {h : OnePoint ℂ ≃ₜ OnePoint ℂ} {hp : puncturedOpens P ≃ₜ puncturedOpens P}
    (hhp : ∀ y, (hp y : OnePoint ℂ) = h y)
    (hhom : ContinuousMap.Homotopic (hp : C(puncturedOpens P, puncturedOpens P))
      (ContinuousMap.id (puncturedOpens P)))
    {c : ℝ → ℂ} (hc : Continuous c) (hc1 : c 1 = c 0) (hcP : ∀ t, ((c t : ℂ) : OnePoint ℂ) ∉ P)
    {q : ℂ} (hq : ((q : ℂ) : OnePoint ℂ) ∈ P) {L M : ℝ → ℂ} (hL : ContinuousOn L (Icc 0 1))
    (hM : ContinuousOn M (Icc 0 1))
    (hLe : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = RiemannDynamics.sphereChartFinite (h (c t)) - q)
    (hMe : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (M t) = c t - q) :
    L 1 - L 0 = M 1 - M 0 := by
  obtain ⟨K⟩ := hhom
  have hmem : ∀ t, ((c t : ℂ) : OnePoint ℂ) ∈ puncturedOpens P := hcP
  set g : ℝ × ℝ → OnePoint ℂ := fun x =>
    ((K (Set.projIcc (0 : ℝ) 1 zero_le_one x.1, ⟨((c x.2 : ℂ) : OnePoint ℂ), hmem x.2⟩) :
      puncturedOpens P) : OnePoint ℂ) with hg
  have hgc : Continuous g := continuous_subtype_val.comp (K.continuous.comp
    ((continuous_projIcc.comp continuous_fst).prodMk
      ((OnePoint.continuous_coe.comp (hc.comp continuous_snd)).subtype_mk _)))
  have hgP : ∀ x, g x ∉ P := fun x => (K _).2
  have hgi : ∀ x, g x ≠ OnePoint.infty := fun x he => hgP x (he ▸ hinfP)
  obtain ⟨hHc, hHe⟩ := s32wh_sphere_fin hgc hgi
  set H : ℝ → ℝ → ℂ := fun s t => RiemannDynamics.sphereChartFinite (g (s, t)) with hH
  have hp0 : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = (0 : unitInterval) := Subtype.ext (by simp)
  have hp1 : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = (1 : unitInterval) := Subtype.ext (by simp)
  have hH0 : ∀ t, H 0 t = RiemannDynamics.sphereChartFinite (h (c t)) := fun t => by
    show RiemannDynamics.sphereChartFinite (g (0, t)) = _
    simp only [hg, hp0, K.apply_zero]
    exact congrArg _ (hhp _)
  have hH1 : ∀ t, H 1 t = c t := fun t => by
    show RiemannDynamics.sphereChartFinite (g (1, t)) = _
    simp only [hg, hp1, K.apply_one, ContinuousMap.id_apply]
    exact RiemannDynamics.sphereChartFinite_coe _
  have hc1' : (⟨((c 1 : ℂ) : OnePoint ℂ), hmem 1⟩ : puncturedOpens P) = ⟨((c 0 : ℂ) : OnePoint ℂ), hmem 0⟩ :=
    Subtype.ext (by simp only [hc1])
  refine lift_change_eq_of_homotopy (H := H) (w := q) ?_ (fun s _ => ?_) (fun s _ t _ he => ?_) hL hM
    (fun t ht => by rw [hLe t ht, hH0]) (fun t ht => by rw [hMe t ht, hH1])
  · exact (hHc.comp (continuous_fst.prodMk continuous_snd)).continuousOn
  · show RiemannDynamics.sphereChartFinite (g (s, 1)) = RiemannDynamics.sphereChartFinite (g (s, 0))
    simp only [hg, hc1']
  · have := hHe (s, t)
    change ((H s t : ℂ) : OnePoint ℂ) = g (s, t) at this
    rw [he] at this
    exact hgP (s, t) (this ▸ hq)

/-- `h` maps the punctures to punctures (its restriction `hp` maps `ℂ̂ ∖ P` onto itself). -/
theorem s32wh_sphere_mapsP {P : Finset (OnePoint ℂ)} {h : OnePoint ℂ ≃ₜ OnePoint ℂ}
    {hp : puncturedOpens P ≃ₜ puncturedOpens P} (hhp : ∀ y, (hp y : OnePoint ℂ) = h y) :
    (∀ x, x ∉ P → h x ∉ P) ∧ ∀ x, x ∈ P → h x ∈ P := by
  refine ⟨fun x hx hhx => ?_, fun x hx => ?_⟩
  · have := (hp ⟨x, hx⟩).2
    rw [hhp] at this
    exact this hhx
  · by_contra hhx
    obtain ⟨y, hy⟩ := hp.surjective ⟨h x, hhx⟩
    have h1 : h (y : OnePoint ℂ) = h x := by rw [← hhp, hy]
    have h2 : (y : OnePoint ℂ) = x := h.injective h1
    exact y.2 (h2 ▸ hx)

/-- **The punctures are fixed.**  With `hp ≃ id` on `ℂ̂ ∖ P` (`∞ ∈ P`), `h` fixes every finite puncture `a` as soon
as there is another finite puncture `q₂`: a small circle about `a` winds once about `a` and not about `q₂`, and so
does its image; if `h a` were finite and `≠ a` the image would wind `0` times about `a`, and if `h a = ∞` it would
wind equally about `a` and `q₂`. -/
theorem s32wh_sphere_fix {P : Finset (OnePoint ℂ)} (hinfP : (OnePoint.infty : OnePoint ℂ) ∈ P)
    {h : OnePoint ℂ ≃ₜ OnePoint ℂ} {hp : puncturedOpens P ≃ₜ puncturedOpens P}
    (hhp : ∀ y, (hp y : OnePoint ℂ) = h y)
    (hhom : ContinuousMap.Homotopic (hp : C(puncturedOpens P, puncturedOpens P))
      (ContinuousMap.id (puncturedOpens P)))
    {a q₂ : ℂ} (ha : ((a : ℂ) : OnePoint ℂ) ∈ P) (hq₂ : ((q₂ : ℂ) : OnePoint ℂ) ∈ P) (hne : q₂ ≠ a) :
    h (a : OnePoint ℂ) = (a : OnePoint ℂ) := by
  classical
  have hPP := (s32wh_sphere_mapsP hhp).1
  obtain ⟨ρ₁, hρ₁, hiso⟩ := s32wh_sphere_radius P a
  have hq₂d : ρ₁ ≤ ‖q₂ - a‖ := by
    by_contra h'
    push Not at h'
    exact hiso q₂ hne h' hq₂
  -- the circle of radius `ρ < ρ₁` about `a`, and its image
  have hcirc : ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ →
      (∀ t : ℝ, ((a + ρ * Complex.exp (2 * π * Complex.I * t) : ℂ) : OnePoint ℂ) ∉ P) ∧
      Continuous (fun t : ℝ => RiemannDynamics.sphereChartFinite
        (h ((a + ρ * Complex.exp (2 * π * Complex.I * t) : ℂ) : OnePoint ℂ))) ∧
      (∀ t : ℝ, ((RiemannDynamics.sphereChartFinite
        (h ((a + ρ * Complex.exp (2 * π * Complex.I * t) : ℂ) : OnePoint ℂ)) : ℂ) : OnePoint ℂ) =
          h ((a + ρ * Complex.exp (2 * π * Complex.I * t) : ℂ) : OnePoint ℂ)) := by
    intro ρ hρ hρρ
    obtain ⟨hcc, -, hcn, -⟩ := s32wh_circle a hρ
    have hP' : ∀ t : ℝ, ((a + ρ * Complex.exp (2 * π * Complex.I * t) : ℂ) : OnePoint ℂ) ∉ P := fun t =>
      hiso _ (fun he => by have := hcn t; rw [he, sub_self, norm_zero] at this; exact hρ.ne this)
        (by rw [hcn t]; exact hρρ)
    obtain ⟨h1, h2⟩ := s32wh_sphere_fin (g := fun t : ℝ => h ((a + ρ * Complex.exp (2 * π * Complex.I * t) : ℂ) :
      OnePoint ℂ)) (h.continuous.comp (OnePoint.continuous_coe.comp hcc))
      (fun t he => hPP _ (hP' t) (he ▸ hinfP))
    exact ⟨hP', h1, h2⟩
  -- the image of a circle avoids every finite puncture
  have havoid : ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ q : ℂ, ((q : ℂ) : OnePoint ℂ) ∈ P → ∀ t : ℝ,
      RiemannDynamics.sphereChartFinite (h ((a + ρ * Complex.exp (2 * π * Complex.I * t) : ℂ) : OnePoint ℂ)) ≠ q :=
    fun ρ hρ hρρ q hq t he => by
      obtain ⟨hP', -, he'⟩ := hcirc ρ hρ hρρ
      have := he' t
      rw [he] at this
      exact hPP _ (hP' t) (this ▸ hq)
  by_contra hfix
  by_cases hinf : h (a : OnePoint ℂ) = OnePoint.infty
  · -- `h a = ∞`: the image of a small circle stays near `∞`
    set R : ℝ := ‖q₂‖ + ‖q₂ - a‖ with hR
    have hU : IsOpen (((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall 0 R)ᶜ :=
      OnePoint.isOpen_compl_image_coe.2 ⟨Metric.isClosed_closedBall, isCompact_closedBall 0 R⟩
    have hinfU : (OnePoint.infty : OnePoint ℂ) ∈ (((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall 0 R)ᶜ := by
      rintro ⟨z, -, hz⟩
      exact OnePoint.coe_ne_infty z hz
    have hn : (fun z : ℂ => h (z : OnePoint ℂ)) ⁻¹' (((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall 0 R)ᶜ ∈ 𝓝 a :=
      (hU.preimage (h.continuous.comp OnePoint.continuous_coe)).mem_nhds (by
        show h (a : OnePoint ℂ) ∈ (((↑) : ℂ → OnePoint ℂ) '' Metric.closedBall 0 R)ᶜ
        rw [hinf]; exact hinfU)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hn
    set ρ : ℝ := min ρ₁ ε / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρρ : ρ < ρ₁ := by
      have := min_le_left ρ₁ ε; rw [hρdef]; linarith
    have hρε : ρ < ε := by
      have := min_le_right ρ₁ ε; rw [hρdef]; linarith
    obtain ⟨hcc, hc1, hcn, M₁, hM₁c, hM₁e, hM₁⟩ := s32wh_circle a hρ
    obtain ⟨hP', hgc, hge⟩ := hcirc ρ hρ hρρ
    set c : ℝ → ℂ := fun t => a + ρ * Complex.exp (2 * π * Complex.I * t) with hcdef
    set w : ℝ → ℂ := fun t => RiemannDynamics.sphereChartFinite (h ((c t : ℂ) : OnePoint ℂ)) with hwdef
    have hwR : ∀ t, R < ‖w t‖ := fun t => by
      have hmem : c t ∈ Metric.ball a ε := by rw [Metric.mem_ball, dist_eq_norm, hcn t]; exact hρε
      have h1 := hball hmem
      simp only [mem_preimage] at h1
      rw [← hge t] at h1
      by_contra hle
      push Not at hle
      exact h1 ⟨w t, by rw [Metric.mem_closedBall, dist_zero_right]; exact hle, rfl⟩
    have hwc : ContinuousOn w (Icc 0 1) := hgc.continuousOn
    obtain ⟨L₁, hL₁c, hL₁e⟩ := exists_continuousOn_log_lift hwc (fun t _ => havoid ρ hρ hρρ a ha t)
    obtain ⟨L₂, hL₂c, hL₂e⟩ := exists_continuousOn_log_lift hwc (fun t _ => havoid ρ hρ hρρ q₂ hq₂ t)
    obtain ⟨M₂, hM₂c, hM₂e⟩ := exists_continuousOn_log_lift (w := q₂) hcc.continuousOn (fun t _ he => by
      have h3 : ‖c t - a‖ = ρ := hcn t
      rw [he] at h3
      rw [h3] at hq₂d; linarith)
    have hW₁ := s32wh_sphere_W hinfP hhp hhom hcc hc1 hP' ha hL₁c hM₁c hL₁e hM₁e
    have hW₂ := s32wh_sphere_W hinfP hhp hhom hcc hc1 hP' hq₂ hL₂c hM₂c hL₂e hM₂e
    -- the circle does not wind about `q₂`
    have hM₂0 : M₂ 1 - M₂ 0 = 0 := by
      have hne' : a - q₂ ≠ 0 := sub_ne_zero.2 hne.symm
      have := lift_change_eq_of_norm_sub_lt (γ := fun t => c t - q₂) (β := fun _ => a - q₂)
        (hcc.continuousOn.sub continuousOn_const) continuousOn_const (by simp only [hcdef]; rw [hc1])
        rfl (fun t _ => by
          rw [sub_sub_sub_cancel_right, hcn t, ← norm_neg, neg_sub]; linarith)
        hM₂c continuousOn_const hM₂e (M := fun _ => Complex.log (a - q₂)) (fun t _ => Complex.exp_log hne')
      rw [this, sub_self]
    -- far from the punctures, the windings about `a` and `q₂` agree
    have hw1 : w 1 = w 0 := by simp only [hwdef, hcdef]; rw [hc1]
    have hsame := lift_change_eq_of_norm_sub_lt (γ := fun t => w t - a) (β := fun t => w t - q₂)
      (hwc.sub continuousOn_const) (hwc.sub continuousOn_const) (by simp only [hw1]) (by simp only [hw1])
      (fun t _ => by
        rw [sub_sub_sub_cancel_left]
        have h1 := hwR t
        have h2 : ‖w t‖ ≤ ‖w t - q₂‖ + ‖q₂‖ := by
          calc ‖w t‖ = ‖(w t - q₂) + q₂‖ := by rw [sub_add_cancel]
            _ ≤ ‖w t - q₂‖ + ‖q₂‖ := norm_add_le _ _
        rw [hR] at h1; linarith)
      hL₁c hL₂c hL₁e hL₂e
    rw [hW₁, hW₂, hM₁, hM₂0] at hsame
    exact Complex.two_pi_I_ne_zero hsame
  · -- `h a = b` finite, `b ≠ a`: the image of a small circle stays near `b`
    obtain ⟨b, hb⟩ := OnePoint.ne_infty_iff_exists.mp hinf
    have hba : b ≠ a := fun e => hfix (by rw [← hb, e])
    have hca : ContinuousAt (fun z : ℂ => RiemannDynamics.sphereChartFinite (h (z : OnePoint ℂ))) a :=
      (RiemannDynamics.sphereChartFinite.continuousAt (by
        rw [RiemannDynamics.sphereChartFinite_source]; exact hinf)).comp
        ((h.continuous.comp OnePoint.continuous_coe).continuousAt)
    have hva : RiemannDynamics.sphereChartFinite (h (a : OnePoint ℂ)) = b := by
      rw [← hb, RiemannDynamics.sphereChartFinite_coe]
    have hpos : 0 < ‖b - a‖ := norm_pos_iff.2 (sub_ne_zero.2 hba)
    obtain ⟨ε, hε, hεc⟩ := Metric.continuousAt_iff.1 hca _ hpos
    set ρ : ℝ := min ρ₁ ε / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρρ : ρ < ρ₁ := by
      have := min_le_left ρ₁ ε; rw [hρdef]; linarith
    have hρε : ρ < ε := by
      have := min_le_right ρ₁ ε; rw [hρdef]; linarith
    obtain ⟨hcc, hc1, hcn, M₁, hM₁c, hM₁e, hM₁⟩ := s32wh_circle a hρ
    obtain ⟨hP', hgc, hge⟩ := hcirc ρ hρ hρρ
    set c : ℝ → ℂ := fun t => a + ρ * Complex.exp (2 * π * Complex.I * t) with hcdef
    set w : ℝ → ℂ := fun t => RiemannDynamics.sphereChartFinite (h ((c t : ℂ) : OnePoint ℂ)) with hwdef
    have hwc : ContinuousOn w (Icc 0 1) := hgc.continuousOn
    obtain ⟨L₁, hL₁c, hL₁e⟩ := exists_continuousOn_log_lift hwc (fun t _ => havoid ρ hρ hρρ a ha t)
    have hW₁ := s32wh_sphere_W hinfP hhp hhom hcc hc1 hP' ha hL₁c hM₁c hL₁e hM₁e
    have hw1 : w 1 = w 0 := by simp only [hwdef, hcdef]; rw [hc1]
    have hba' : b - a ≠ 0 := sub_ne_zero.2 hba
    have hnear := lift_change_eq_of_norm_sub_lt (γ := fun t => w t - a) (β := fun _ => b - a)
      (hwc.sub continuousOn_const) continuousOn_const (by simp only [hw1]) rfl
      (fun t _ => by
        rw [sub_sub_sub_cancel_right]
        have := hεc (x := c t) (by rw [dist_eq_norm, hcn t]; exact hρε)
        rw [hva, dist_eq_norm] at this
        exact this)
      hL₁c continuousOn_const hL₁e (M := fun _ => Complex.log (b - a)) (fun t _ => Complex.exp_log hba')
    rw [hW₁, hM₁, sub_self] at hnear
    exact Complex.two_pi_I_ne_zero hnear

/-- **Sphere core.**  A homeomorphism `h` of `ℂ̂` preserving a finite set `P ∋ 0, 1, ∞` whose restriction to `ℂ̂ ∖ P` is
homotopic to the identity (in `ℂ̂ ∖ P`) is homotopic to the identity: the winding about `0` of `h` along small
circles about every finite puncture `a` equals that of the circles, so `h a = a`, `h ∞ = ∞`, and `h` has local
winding `+1` at `0`; then `s24q_sp_core`. -/
theorem s32wh_sphere_core {P : Finset (OnePoint ℂ)} (h0P : ((0 : ℂ) : OnePoint ℂ) ∈ P)
    (h1P : ((1 : ℂ) : OnePoint ℂ) ∈ P) (hinfP : (OnePoint.infty : OnePoint ℂ) ∈ P) {h : OnePoint ℂ ≃ₜ OnePoint ℂ}
    {hp : puncturedOpens P ≃ₜ puncturedOpens P} (hhp : ∀ y, (hp y : OnePoint ℂ) = h y)
    (hhom : ContinuousMap.Homotopic (hp : C(puncturedOpens P, puncturedOpens P))
      (ContinuousMap.id (puncturedOpens P))) :
    ContinuousMap.Homotopic (h : C(OnePoint ℂ, OnePoint ℂ)) (ContinuousMap.id (OnePoint ℂ)) := by
  classical
  have h0 : h ((0 : ℂ) : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) :=
    s32wh_sphere_fix hinfP hhp hhom h0P h1P one_ne_zero
  have hinf : h OnePoint.infty = OnePoint.infty := by
    have hmem := (s32wh_sphere_mapsP hhp).2 _ hinfP
    by_contra hne
    obtain ⟨b, hb⟩ := OnePoint.ne_infty_iff_exists.mp hne
    have hbP : ((b : ℂ) : OnePoint ℂ) ∈ P := hb ▸ hmem
    have hfix : h (b : OnePoint ℂ) = (b : OnePoint ℂ) := by
      by_cases hb0 : b = 0
      · rw [hb0]; exact h0
      · exact s32wh_sphere_fix hinfP hhp hhom hbP h0P (Ne.symm hb0)
    exact OnePoint.coe_ne_infty b (h.injective (hfix.trans hb))
  have e1 : chartAt ℂ ((0 : ℂ) : OnePoint ℂ) = RiemannDynamics.sphereChartFinite := rfl
  have key : ∀ z : ℂ, localMapExpr h ((0 : ℂ) : OnePoint ℂ) z =
      RiemannDynamics.sphereChartFinite (h (z : OnePoint ℂ)) := by
    intro z
    simp only [localMapExpr, h0, e1]
    rw [RiemannDynamics.sphereChartFinite_symm_apply]
  have hc0 : chartAt ℂ ((0 : ℂ) : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ) = 0 := by
    rw [e1, RiemannDynamics.sphereChartFinite_coe]
  obtain ⟨ρ₁, hρ₁, hiso⟩ := s32wh_sphere_radius P 0
  have hw : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ Lg : ℝ → ℂ, ContinuousOn Lg (Set.Icc 0 1) →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Complex.exp (Lg t) =
        localMapExpr h ((0 : ℂ) : OnePoint ℂ) (chartAt ℂ ((0 : ℂ) : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ) +
          ρ * Complex.exp (2 * π * Complex.I * t)) -
          localMapExpr h ((0 : ℂ) : OnePoint ℂ) (chartAt ℂ ((0 : ℂ) : OnePoint ℂ) ((0 : ℂ) : OnePoint ℂ))) →
        Lg 1 - Lg 0 = 2 * π * Complex.I := by
    refine ⟨ρ₁, hρ₁, fun ρ hρ hρρ Lg hLc hLe => ?_⟩
    obtain ⟨hcc, hc1, hcn, M₁, hM₁c, hM₁e, hM₁⟩ := s32wh_circle 0 hρ
    have hP' : ∀ t : ℝ, (((0 : ℂ) + ρ * Complex.exp (2 * π * Complex.I * t) : ℂ) : OnePoint ℂ) ∉ P := fun t =>
      hiso _ (fun he => by have := hcn t; rw [he, sub_self, norm_zero] at this; exact hρ.ne this)
        (by rw [hcn t]; exact hρρ)
    have hLe' : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (Lg t) = RiemannDynamics.sphereChartFinite
        (h (((0 : ℂ) + ρ * Complex.exp (2 * π * Complex.I * t) : ℂ) : OnePoint ℂ)) - 0 := fun t ht => by
      rw [hLe t ht, hc0, key, key, h0, RiemannDynamics.sphereChartFinite_coe]
    rw [s32wh_sphere_W hinfP hhp hhom hcc hc1 hP' h0P hLc hM₁c hLe' hM₁e, hM₁]
  obtain ⟨G, hG0, hG1⟩ := s24q_sp_core h h0 hinf hw
  exact ⟨⟨G, hG0, hG1⟩⟩

/-- **(b6), genus `0`** (at least three punctures): `ψ = fd'⁻¹ ∘ fd` is homotopic to the identity off `P₀`;
conjugate by a sphere model sending three punctures to `0, 1, ∞` and apply `s32wh_sphere_core`. -/
theorem s32wh_genus_zero {X₀ X₁ : ClosedRS.{u}} (h₀ : HasGenus X₀.carrier 0)
    {P₀ : Finset X₀.carrier} {P₁ : Finset X₁.carrier} (hP : 3 ≤ P₀.card)
    {fd fd' : X₀.carrier ≃ₜ X₁.carrier} {fdp fdp' : puncturedOpens P₀ ≃ₜ puncturedOpens P₁}
    (hfdp : ∀ y, (fdp y : X₁.carrier) = fd y) (hfdp' : ∀ y, (fdp' y : X₁.carrier) = fd' y)
    (hhom : ContinuousMap.Homotopic (fdp : C(puncturedOpens P₀, puncturedOpens P₁))
      (fdp' : C(puncturedOpens P₀, puncturedOpens P₁))) :
    ContinuousMap.Homotopic (fd : C(X₀.carrier, X₁.carrier)) (fd' : C(X₀.carrier, X₁.carrier)) := by
  classical
  -- `ψ = fd'⁻¹ ∘ fd` is homotopic to the identity off `P₀`
  set ψ : X₀.carrier ≃ₜ X₀.carrier := fd.trans fd'.symm with hψ
  set ψp : puncturedOpens P₀ ≃ₜ puncturedOpens P₀ := fdp.trans fdp'.symm with hψp
  have hψψp : ∀ y, (ψp y : X₀.carrier) = ψ y := fun y => by
    show ((fdp'.symm (fdp y) : puncturedOpens P₀) : X₀.carrier) = fd'.symm (fd y)
    apply fd'.injective
    rw [fd'.apply_symm_apply, ← hfdp', fdp'.apply_symm_apply, hfdp]
  have hψh : ContinuousMap.Homotopic (ψp : C(puncturedOpens P₀, puncturedOpens P₀))
      (ContinuousMap.id (puncturedOpens P₀)) := by
    have := (ContinuousMap.Homotopic.refl (fdp'.symm : C(puncturedOpens P₁, puncturedOpens P₀))).comp hhom
    convert this using 1
    · ext y; simp [hψp]
    · ext y; simp
  -- a sphere model sending three punctures to `0, 1, ∞`
  obtain ⟨c₀, -⟩ := s24q_sphere_model h₀
  obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, h12, h13, h23⟩ := Finset.two_lt_card.1 (by omega : 2 < P₀.card)
  obtain ⟨g, hg1, hg2, hg3⟩ := RiemannDynamics.exists_gl_smul_eq_zero_one_infty
    (c₀.injective.ne h12) (c₀.injective.ne h13) (c₀.injective.ne h23)
  obtain ⟨γ, hγ⟩ := s24q_mb_gl_sl g
  obtain ⟨T, hT, -⟩ := s24q_mb_homeo γ
  set e : X₀.carrier ≃ₜ OnePoint ℂ := c₀.trans T with he
  have he' : ∀ x, e x = g • c₀ x := fun x => by
    show T (c₀ x) = _
    rw [hT, hγ]
  set P : Finset (OnePoint ℂ) := P₀.map e.toEquiv.toEmbedding with hPdef
  have hmemP : ∀ x, e x ∈ P ↔ x ∈ P₀ := fun x => Finset.mem_map' _
  have hiff : ∀ x : X₀.carrier, x ∈ puncturedOpens P₀ ↔ e x ∈ puncturedOpens P := fun x => by
    show x ∉ (P₀ : Set X₀.carrier) ↔ e x ∉ (P : Set (OnePoint ℂ))
    rw [Finset.mem_coe, Finset.mem_coe, hmemP]
  set E : puncturedOpens P₀ ≃ₜ puncturedOpens P := e.subtype hiff with hE
  have hEc : ∀ x, (E x : OnePoint ℂ) = e x := fun x => rfl
  have hEs : ∀ y, ((E.symm y : puncturedOpens P₀) : X₀.carrier) = e.symm y := fun y => by
    apply e.injective
    rw [e.apply_symm_apply, ← hEc, E.apply_symm_apply]
  -- the conjugated map of `ℂ̂`
  set hs : OnePoint ℂ ≃ₜ OnePoint ℂ := e.symm.trans (ψ.trans e) with hhs
  set hsp : puncturedOpens P ≃ₜ puncturedOpens P := E.symm.trans (ψp.trans E) with hhsp
  have hhsp' : ∀ y, (hsp y : OnePoint ℂ) = hs y := fun y => by
    show ((E (ψp (E.symm y)) : puncturedOpens P) : OnePoint ℂ) = e (ψ (e.symm y))
    rw [hEc, hψψp, hEs]
  have hsph : ContinuousMap.Homotopic (hsp : C(puncturedOpens P, puncturedOpens P))
      (ContinuousMap.id (puncturedOpens P)) := by
    have := (ContinuousMap.Homotopic.refl (E : C(puncturedOpens P₀, puncturedOpens P))).comp
      (hψh.comp (ContinuousMap.Homotopic.refl (E.symm : C(puncturedOpens P, puncturedOpens P₀))))
    convert this using 1
    · ext y; simp [hhsp]
    · ext y; simp
  have h0P : ((0 : ℂ) : OnePoint ℂ) ∈ P := by
    rw [← hg1, ← he', hmemP]; exact hx₁
  have h1P : ((1 : ℂ) : OnePoint ℂ) ∈ P := by
    rw [← hg2, ← he', hmemP]; exact hx₂
  have hinfP : (OnePoint.infty : OnePoint ℂ) ∈ P := by
    rw [← hg3, ← he', hmemP]; exact hx₃
  have hcore := s32wh_sphere_core h0P h1P hinfP hhsp' hsph
  -- back to `X₀`: `ψ ≃ id`, so `fd = fd' ∘ ψ ≃ fd'`
  have hψid : ContinuousMap.Homotopic (ψ : C(X₀.carrier, X₀.carrier)) (ContinuousMap.id X₀.carrier) := by
    have := (ContinuousMap.Homotopic.refl (e.symm : C(OnePoint ℂ, X₀.carrier))).comp
      (hcore.comp (ContinuousMap.Homotopic.refl (e : C(X₀.carrier, OnePoint ℂ))))
    convert this using 1
    · ext x; simp [hhs]
    · ext x; simp
  have := (ContinuousMap.Homotopic.refl (fd' : C(X₀.carrier, X₁.carrier))).comp hψid
  convert this using 1
  · ext x; simp [hψ]
  · ext x; simp

/-- **(b6)** Homotopic restrictions to the punctured surfaces give homotopic homeomorphisms of the closed surfaces
(genus `G`; at least three punctures when `G = 0`).  Topological: no quasiconformality is used. -/
theorem s32w_homotopy_extend_punctures {X₀ X₁ : ClosedRS.{u}} {G : ℕ} (h₀ : HasGenus X₀.carrier G)
    (h₁ : HasGenus X₁.carrier G) {P₀ : Finset X₀.carrier} {P₁ : Finset X₁.carrier} (hP : G ≠ 0 ∨ 3 ≤ P₀.card)
    {fd fd' : X₀.carrier ≃ₜ X₁.carrier} {fdp fdp' : puncturedOpens P₀ ≃ₜ puncturedOpens P₁}
    (hfdp : ∀ y, (fdp y : X₁.carrier) = fd y) (hfdp' : ∀ y, (fdp' y : X₁.carrier) = fd' y)
    (hhom : ContinuousMap.Homotopic (fdp : C(puncturedOpens P₀, puncturedOpens P₁))
      (fdp' : C(puncturedOpens P₀, puncturedOpens P₁))) :
    ContinuousMap.Homotopic (fd : C(X₀.carrier, X₁.carrier)) (fd' : C(X₀.carrier, X₁.carrier)) := by
  rcases Nat.lt_or_ge 1 G with hG | hG
  · exact s32wh_genus_ge_two hG h₀ h₁ hfdp hfdp' hhom
  · interval_cases G
    · exact s32wh_genus_zero h₀ (hP.resolve_left (by norm_num)) hfdp hfdp' hhom
    · exact s32wh_genus_one h₀ h₁ hfdp hfdp' hhom

end LiZhongQC
