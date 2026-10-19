import LiZhongQC.Lemmas.SchottkyGenusBridge1
import LiZhongExternal.Classification.SchottkyClassification09
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology Metric
open scoped Manifold ContDiff

namespace LiZhongQC
noncomputable section

/-- The complex plane embeds openly in the model half-space. -/
theorem s78dg_plane_openEmbedding_halfspace :
    ∃ f : ℂ → EuclideanHalfSpace 2, Topology.IsOpenEmbedding f := by
  let L : ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    Complex.equivRealProdCLM.toHomeomorph.trans
      ((Homeomorph.prodComm ℝ ℝ).trans
        ((Homeomorph.finTwoArrow : (Fin 2 → ℝ) ≃ₜ ℝ × ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm.toHomeomorph))
  have hL : ∀ z, (L z) 0 = z.im := fun _ => rfl
  let h : {z : ℂ | 0 ≤ z.im} ≃ₜ EuclideanHalfSpace 2 :=
    L.subtype (fun z => show 0 ≤ z.im ↔ 0 ≤ (L z) 0 from by rw [hL])
  let e : ℂ ≃ₜ {z : ℂ | 0 < z.im} := {
    toFun := fun z => ⟨⟨z.re, Real.exp z.im⟩, Real.exp_pos z.im⟩
    invFun := fun z => ⟨z.val.re, Real.log z.val.im⟩
    left_inv := by
      intro z
      apply Complex.ext
      · rfl
      · exact Real.log_exp z.im
    right_inv := by
      intro z
      apply Subtype.ext
      apply Complex.ext
      · rfl
      · exact Real.exp_log z.property
    continuous_toFun :=
      (Complex.equivRealProdCLM.symm.continuous.comp
        (continuous_re.prodMk (Real.continuous_exp.comp continuous_im))).subtype_mk _
    continuous_invFun :=
      Complex.equivRealProdCLM.symm.continuous.comp
        ((continuous_re.comp continuous_subtype_val).prodMk
          ((continuous_im.comp continuous_subtype_val).log
            (fun z => ne_of_gt z.property))) }
  have hle : ∀ z : {z : ℂ | 0 < z.im}, z.val ∈ {z : ℂ | 0 ≤ z.im} := fun z =>
    le_of_lt (show (0 : ℝ) < z.val.im from z.property)
  let k : {z : ℂ | 0 < z.im} → {z : ℂ | 0 ≤ z.im} :=
    fun z => ⟨z.val, hle z⟩
  have hpos : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const continuous_im
  have hk : Topology.IsOpenEmbedding k :=
    Topology.IsOpenEmbedding.of_isEmbedding_isOpenMap
      (hpos.isOpenEmbedding_subtypeVal.isEmbedding.codRestrict _ hle)
      (hpos.isOpenEmbedding_subtypeVal.isOpenMap.subtype_mk hle)
  exact ⟨h ∘ k ∘ e, h.isOpenEmbedding.comp (hk.comp e.isOpenEmbedding)⟩

/-- Every Riemann surface (complex charted space) is charted over the model half-space, with charts
landing in the interior; this is the `C⁰` structure used by the classification of surfaces. -/
theorem s78dg_halfspace_chartedSpace (S : Type*) [TopologicalSpace S] [ChartedSpace ℂ S] :
    Nonempty (ChartedSpace (EuclideanHalfSpace 2) S) := by
  obtain ⟨f, hf⟩ := s78dg_plane_openEmbedding_halfspace
  let J : OpenPartialHomeomorph ℂ (EuclideanHalfSpace 2) := hf.toOpenPartialHomeomorph f
  exact ⟨{ atlas := Set.range (fun x : S => (chartAt ℂ x).trans J)
           chartAt := fun x => (chartAt ℂ x).trans J
           mem_chart_source := fun x => by
             refine ⟨mem_chart_source ℂ x, ?_⟩
             show x ∈ _
             simp [J, hf.toOpenPartialHomeomorph_source]
           chart_mem_atlas := fun x => ⟨x, rfl⟩ }⟩


/-- A subset of the disc on which the equivalence relation is trivial embeds openly in the quotient. -/
theorem s78dg_free_open_embedding (R : ClosedUnitDisc → ClosedUnitDisc → Prop) (S : Set ClosedUnitDisc)
    (hS : IsOpen S) (hfree : ∀ x ∈ S, ∀ y, Relation.EqvGen R x y → x = y) :
    IsOpenEmbedding (fun z : S => (Quot.mk R (z : ClosedUnitDisc))) := by
  have hinj : Function.Injective (fun z : S => (Quot.mk R (z : ClosedUnitDisc))) := by
    intro z w hzw
    exact Subtype.ext (hfree z z.2 w (Quot.eqvGen_exact hzw))
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (continuous_quot_mk.comp continuous_subtype_val) hinj ?_
  intro W hW
  obtain ⟨W', hW', rfl⟩ := isOpen_induced_iff.mp hW
  have hsub : (Subtype.val : S → ClosedUnitDisc) '' (Subtype.val ⁻¹' W') = W' ∩ S := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hz, z.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨y, h2⟩, h1, rfl⟩
  have himg : (fun z : S => (Quot.mk R (z : ClosedUnitDisc))) '' (Subtype.val ⁻¹' W') =
      (Quot.mk R) '' (W' ∩ S) := by
    rw [← hsub, ← Set.image_comp]
    rfl
  rw [himg]
  have hsat : (Quot.mk R) ⁻¹' ((Quot.mk R) '' (W' ∩ S)) = W' ∩ S := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have := Quot.eqvGen_exact hxy
      rw [← hfree x hx.2 y this]
      exact hx
    · intro hy
      exact ⟨y, hy, rfl⟩
  rw [← isQuotientMap_quot_mk.isOpen_preimage, hsat]
  exact hW'.inter hS

/-- **A free boundary arc has no plane neighbourhood.**  If the relation does not touch the part of the
unit disc within `r` of a boundary point `z₀`, then the image of `z₀` in the quotient has no open
neighbourhood homeomorphic to the plane (invariance of domain). -/
theorem s78dg_free_arc_no_plane (R : ClosedUnitDisc → ClosedUnitDisc → Prop) (z₀ : ClosedUnitDisc)
    (hz₀ : ‖(z₀ : ℂ)‖ = 1) (r : ℝ) (hr : 0 < r)
    (hfree : ∀ x : ClosedUnitDisc, ‖(x : ℂ) - z₀‖ < r → ∀ y, Relation.EqvGen R x y → x = y)
    (U : Set (Quot R)) (hU : IsOpen U) (hq : Quot.mk R z₀ ∈ U)
    (h : ↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) : False := by
  classical
  let B : Set ClosedUnitDisc := {x | ‖(x : ℂ) - z₀‖ < r}
  have hB : IsOpen B :=
    isOpen_lt ((continuous_subtype_val.sub continuous_const).norm) continuous_const
  have hemb := s78dg_free_open_embedding R B hB (fun x hx y hy => hfree x hx y hy)
  let eB : B ≃ₜ Set.range (fun z : B => Quot.mk R (z : ClosedUnitDisc)) :=
    hemb.isEmbedding.toHomeomorph
  let f : EuclideanSpace ℝ (Fin 2) → Quot R := fun y => (h.symm y).val
  have hfc : Continuous f := continuous_subtype_val.comp h.symm.continuous
  have hfi : Function.Injective f := Subtype.val_injective.comp h.symm.injective
  let D : Set (EuclideanSpace ℝ (Fin 2)) := f ⁻¹' Set.range (fun z : B => Quot.mk R (z : ClosedUnitDisc))
  have hD : IsOpen D := hemb.isOpen_range.preimage hfc
  let L : ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    Complex.equivRealProdCLM.toHomeomorph.trans
      ((Homeomorph.prodComm ℝ ℝ).trans
        ((Homeomorph.finTwoArrow : (Fin 2 → ℝ) ≃ₜ ℝ × ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm.toHomeomorph))
  let g : EuclideanSpace ℝ (Fin 2) → ℂ := fun y =>
    if hy : y ∈ D then ((eB.symm ⟨f y, hy⟩ : B) : ClosedUnitDisc) else 0
  have hg : ∀ y (hy : y ∈ D), g y = (((eB.symm ⟨f y, hy⟩ : B) : ClosedUnitDisc) : ℂ) :=
    fun y hy => dif_pos hy
  have hgc : ContinuousOn g D := by
    rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous (fun y : D => (((eB.symm ⟨f y, y.2⟩ : B) : ClosedUnitDisc) : ℂ)) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp (eB.symm.continuous.comp
        (Continuous.subtype_mk (hfc.comp continuous_subtype_val) (fun y => y.2))))
    convert hc using 1
    funext y
    exact hg y y.2
  have hgi : Set.InjOn g D := by
    intro a ha b hb hab
    rw [hg a ha, hg b hb] at hab
    have h1 : eB.symm ⟨f a, ha⟩ = eB.symm ⟨f b, hb⟩ := Subtype.ext (Subtype.ext hab)
    have h2 := eB.symm.injective h1
    have h3 : f a = f b := congrArg (fun x : Set.range (fun z : B => Quot.mk R (z : ClosedUnitDisc)) =>
      (x : Quot R)) h2
    exact hfi h3
  let g' : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun y => L (g y)
  have hopen : IsOpen (g' '' D) :=
    InvarianceOfDomain.invariance_of_domain_open_map g' D hD (L.continuous.comp_continuousOn hgc)
      (fun a ha b hb hab => hgi ha hb (L.injective hab))
  have hopen2 : IsOpen (g '' D) := by
    have : g '' D = L ⁻¹' (g' '' D) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, hyz⟩; exact ⟨y, hy, L.injective hyz⟩
    rw [this]; exact hopen.preimage L.continuous
  let y₀ : EuclideanSpace ℝ (Fin 2) := h ⟨Quot.mk R z₀, hq⟩
  have hfy₀ : f y₀ = Quot.mk R z₀ := by
    show (h.symm (h ⟨Quot.mk R z₀, hq⟩)).val = _
    rw [Homeomorph.symm_apply_apply]
  have hz₀B : z₀ ∈ B := by
    show ‖(z₀ : ℂ) - z₀‖ < r
    simpa using hr
  have hy₀D : y₀ ∈ D := ⟨⟨z₀, hz₀B⟩, hfy₀.symm⟩
  have hg₀ : g y₀ = (z₀ : ℂ) := by
    rw [hg y₀ hy₀D]
    have : (⟨f y₀, hy₀D⟩ : Set.range (fun z : B => Quot.mk R (z : ClosedUnitDisc))) =
        eB ⟨z₀, hz₀B⟩ := Subtype.ext hfy₀
    rw [this, Homeomorph.symm_apply_apply]
  -- the image is an open subset of the plane containing a point of the unit circle, inside the disc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen2 (g y₀) ⟨y₀, hy₀D, rfl⟩
  have hsub : g '' D ⊆ Metric.closedBall (0 : ℂ) 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hg y hy]
    exact ((eB.symm ⟨f y, hy⟩ : B) : ClosedUnitDisc).2
  -- a point slightly outside the unit disc
  let t : ℝ := min (ε / 2) 1
  have ht0 : 0 < t := lt_min (by linarith) one_pos
  have hz0 : (z₀ : ℂ) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hz₀; exact zero_ne_one hz₀
  let w : ℂ := (1 + t) • (z₀ : ℂ)
  have hw : w ∈ Metric.ball (g y₀) ε := by
    rw [Metric.mem_ball, hg₀, dist_eq_norm]
    show ‖(1 + t) • (z₀ : ℂ) - z₀‖ < ε
    have : (1 + t) • (z₀ : ℂ) - z₀ = t • (z₀ : ℂ) := by rw [add_smul, one_smul]; abel
    rw [this, norm_smul, hz₀, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
    have := min_le_left (ε / 2) 1
    linarith
  have hin := hsub (hball hw)
  rw [mem_closedBall_zero_iff] at hin
  have : ‖w‖ = 1 + t := by
    show ‖(1 + t) • (z₀ : ℂ)‖ = _
    rw [norm_smul, hz₀, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [this] at hin
  linarith

theorem s78dg_bdy_coe (t : ℝ) :
    ((ClosedUnitDisc.bdyPtOfReal t : ClosedUnitDisc) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)) := by
  have h := s78dg_cs_bdy_coe 1 le_rfl t
  simpa using h

theorem s78dg_bdy_continuous : Continuous ClosedUnitDisc.bdyPtOfReal := by
  refine continuous_induced_rng.2 ?_
  have : (Subtype.val ∘ ClosedUnitDisc.bdyPtOfReal : ℝ → ℂ) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((t : ℝ) : ℂ)) := funext s78dg_bdy_coe
  rw [this]
  fun_prop

theorem s78dg_bdy_eq_iff (s t : ℝ) :
    ClosedUnitDisc.bdyPtOfReal s = ClosedUnitDisc.bdyPtOfReal t ↔ ∃ m : ℤ, s = t + m := by
  have h := s78dg_cs_exp_eq_iff (N := 1) one_ne_zero s t
  simp only [div_one] at h
  constructor
  · intro hst
    have := congrArg Subtype.val hst
    rw [s78dg_bdy_coe, s78dg_bdy_coe] at this
    simpa using h.1 this
  · intro hm
    apply Subtype.ext
    rw [s78dg_bdy_coe, s78dg_bdy_coe]
    exact h.2 (by simpa using hm)

theorem s78dg_eqv_in_set (R : ClosedUnitDisc → ClosedUnitDisc → Prop) (F : Set ClosedUnitDisc)
    (hR : ∀ x y, R x y → x ∈ F ∧ y ∈ F) {a b : ClosedUnitDisc} (h : Relation.EqvGen R a b) :
    a = b ∨ (a ∈ F ∧ b ∈ F) := by
  induction h with
  | rel a b hab => exact Or.inr (hR a b hab)
  | refl a => exact Or.inl rfl
  | symm a b _ ih =>
    rcases ih with rfl | h1
    · exact Or.inl rfl
    · exact Or.inr ⟨h1.2, h1.1⟩
  | trans a b c _ _ ih1 ih2 =>
    rcases ih1 with rfl | h1
    · exact ih2
    · rcases ih2 with rfl | h2
      · exact Or.inr h1
      · exact Or.inr ⟨h1.1, h2.2⟩

/-- **A boundary point avoiding all glued arcs has no plane neighbourhood.** -/
theorem s78dg_free_param (R : ClosedUnitDisc → ClosedUnitDisc → Prop) (T : Set ℝ)
    (hT : IsCompact T)
    (hR : ∀ x y, R x y → x ∈ ClosedUnitDisc.bdyPtOfReal '' T ∧ y ∈ ClosedUnitDisc.bdyPtOfReal '' T)
    (s₀ : ℝ) (hs₀ : ∀ t ∈ T, ∀ m : ℤ, s₀ ≠ t + m)
    (U : Set (Quot R)) (hU : IsOpen U) (hq : Quot.mk R (ClosedUnitDisc.bdyPtOfReal s₀) ∈ U)
    (h : ↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) : False := by
  let F : Set ClosedUnitDisc := ClosedUnitDisc.bdyPtOfReal '' T
  have hFc : IsClosed F := (hT.image s78dg_bdy_continuous).isClosed
  have hz : ClosedUnitDisc.bdyPtOfReal s₀ ∉ F := by
    rintro ⟨t, ht, hts⟩
    obtain ⟨m, hm⟩ := (s78dg_bdy_eq_iff t s₀).1 hts
    exact hs₀ t ht (-m) (by rw [hm]; push_cast; ring)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hFc.isOpen_compl _ hz
  have hnorm : ‖((ClosedUnitDisc.bdyPtOfReal s₀ : ClosedUnitDisc) : ℂ)‖ = 1 := by
    rw [s78dg_bdy_coe]
    have := s78dg_cs_norm_param 1 s₀ one_pos
    simpa using this
  refine s78dg_free_arc_no_plane R _ hnorm ε hε ?_ U hU hq h
  intro x hx y hxy
  have hxF : x ∉ F := hball (by
    rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
    exact hx)
  rcases s78dg_eqv_in_set R F hR hxy with h1 | h1
  · exact h1
  · exact absurd h1.1 hxF

theorem s78dg_noint (N v : ℝ) (hN : 0 < N) (h1 : -N < v) (h2 : v < N) (h3 : v ≠ 0) (m : ℤ) :
    (m : ℝ) * N ≠ v := by
  intro h
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
    nlinarith
  · subst hm; simp at h; exact h3 h.symm
  · have : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
    nlinarith

/-- Bounds `a ≤ t·N ≤ b` for a point of `[a/N, b/N]`. -/
theorem s78dg_icc_mul {N a b t : ℝ} (hN : 0 < N) (h : t ∈ Set.Icc (a / N) (b / N)) :
    a ≤ t * N ∧ t * N ≤ b :=
  ⟨(div_le_iff₀ hN).1 h.1, (le_div_iff₀ hN).1 h.2⟩

/-- **The free arc of `Quot (OrientableRel p n)`, `n ≥ 1`, has no plane neighbourhood.** -/
theorem s78dg_orientable_free (p n : ℕ) (hn : 1 ≤ n)
    (U : Set (Quot (OrientableRel p n))) (hU : IsOpen U)
    (hq : Quot.mk (OrientableRel p n)
      (ClosedUnitDisc.bdyPtOfReal (-(3 / 2 : ℝ) / (4 * p + 3 * n))) ∈ U)
    (h : ↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) : False := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpr : (0 : ℝ) ≤ p := by positivity
  set N : ℝ := 4 * p + 3 * n with hNdef
  have hN : 0 < N := by rw [hNdef]; linarith
  let T : Set ℝ := Set.Icc 0 (4 * p / N) ∪ ⋃ j : Fin n,
    (Set.Icc (-(3 * (j : ℝ) + 1) / N) (-(3 * (j : ℝ)) / N) ∪
      Set.Icc (-(3 * (j : ℝ) + 3) / N) (-(3 * (j : ℝ) + 2) / N))
  have hT : IsCompact T := by
    refine isCompact_Icc.union (isCompact_iUnion fun j => isCompact_Icc.union isCompact_Icc)
  refine s78dg_free_param _ T hT ?_ (-(3 / 2 : ℝ) / N) ?_ U hU hq h
  · intro x y hxy
    have hmem : ∀ {a b u : ℝ}, a ≤ u → u ≤ b → u / N ∈ Set.Icc (a / N) (b / N) :=
      fun h1 h2 => ⟨div_le_div_of_nonneg_right h1 hN.le, div_le_div_of_nonneg_right h2 hN.le⟩
    have hmem0 : ∀ {b u : ℝ}, 0 ≤ u → u ≤ b → u / N ∈ Set.Icc (0 : ℝ) (b / N) :=
      fun h1 h2 => ⟨div_nonneg h1 hN.le, div_le_div_of_nonneg_right h2 hN.le⟩
    cases hxy with
    | a x i =>
      have hi : ((i : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast i.2
      have hx0 := x.2.1
      have hx1 := x.2.2
      have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      exact ⟨⟨_, Or.inl (hmem0 (by linarith) (by linarith)), rfl⟩,
        ⟨_, Or.inl (hmem0 (by linarith) (by linarith)), rfl⟩⟩
    | b x i =>
      have hi : ((i : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast i.2
      have hx0 := x.2.1
      have hx1 := x.2.2
      have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      exact ⟨⟨_, Or.inl (hmem0 (by linarith) (by linarith)), rfl⟩,
        ⟨_, Or.inl (hmem0 (by linarith) (by linarith)), rfl⟩⟩
    | c x i =>
      have hx0 := x.2.1
      have hx1 := x.2.2
      exact ⟨⟨_, Or.inr (Set.mem_iUnion.2 ⟨i, Or.inl (hmem (by linarith) (by linarith))⟩), rfl⟩,
        ⟨_, Or.inr (Set.mem_iUnion.2 ⟨i, Or.inr (hmem (by linarith) (by linarith))⟩), rfl⟩⟩
  · intro t ht m hm
    rw [div_eq_iff hN.ne'] at hm
    have hmN : (m : ℝ) * N = -3 / 2 - t * N := by nlinarith [hm]
    have hp4 : (0 : ℝ) ≤ 4 * p := by linarith
    have hNge : (3 : ℝ) ≤ 3 * n := by linarith
    rcases ht with h | h
    · have h1 : 0 ≤ t * N := mul_nonneg h.1 hN.le
      have h2 : t * N ≤ 4 * p := (le_div_iff₀ hN).1 h.2
      exact s78dg_noint N (-3 / 2 - t * N) hN (by linarith) (by linarith) (by linarith) m hmN
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h
      have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
      have hj1 : ((j : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast j.2
      rcases hj with h | h
      · obtain ⟨h1, h2⟩ := s78dg_icc_mul hN h
        rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | h0
        · have : ((j : ℕ) : ℝ) = 0 := by rw [h0]; simp
          rw [this] at h1 h2
          exact s78dg_noint N (-3 / 2 - t * N) hN (by linarith) (by linarith) (by linarith) m hmN
        · have : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h0
          exact s78dg_noint N (-3 / 2 - t * N) hN (by linarith) (by linarith) (by linarith) m hmN
      · obtain ⟨h1, h2⟩ := s78dg_icc_mul hN h
        exact s78dg_noint N (-3 / 2 - t * N) hN (by linarith) (by linarith) (by linarith) m hmN

/-- A chart into the Euclidean plane gives an open neighbourhood homeomorphic to the plane. -/
theorem s78dg_euclid_nbhd {S : Type*} [TopologicalSpace S]
    (e : OpenPartialHomeomorph S (EuclideanSpace ℝ (Fin 2))) {x : S} (hx : x ∈ e.source) :
    ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 e.open_target (e x) (e.map_source hx)
  let b : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
    OpenPartialHomeomorph.univBall (e x) r
  have hbt : b.target = ball (e x) r := OpenPartialHomeomorph.univBall_target _ hr
  have hbs : b.source = univ := OpenPartialHomeomorph.univBall_source _ _
  let e2 := e.trans b.symm
  have hsrc : e2.source = e.source ∩ e ⁻¹' ball (e x) r := by
    show e.source ∩ e ⁻¹' b.symm.source = _
    rw [OpenPartialHomeomorph.symm_source, hbt]
  have htgt : e2.target = univ := by
    show b.symm.target ∩ b.symm.symm ⁻¹' e.target = univ
    rw [OpenPartialHomeomorph.symm_target, hbs, OpenPartialHomeomorph.symm_symm]
    ext z
    simp only [mem_inter_iff, mem_univ, mem_preimage, true_and]
    have hz : b z ∈ b.target := b.map_source (by rw [hbs]; exact mem_univ z)
    rw [hbt] at hz
    exact iff_true_intro (hball hz)
  have hxs : x ∈ e2.source := by
    rw [hsrc]
    exact ⟨hx, mem_ball_self hr⟩
  refine ⟨e2.source, e2.open_source, hxs, ⟨?_⟩⟩
  exact e2.toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr htgt).trans (Homeomorph.Set.univ _))


/-- Every point of a Riemann surface has an open neighbourhood homeomorphic to the plane. -/
theorem s78dg_riemann_plane_nbhd (S : Type*) [TopologicalSpace S] [ChartedSpace ℂ S] (x : S) :
    ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
  let L : ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
    Complex.equivRealProdCLM.toHomeomorph.trans
      ((Homeomorph.prodComm ℝ ℝ).trans
        ((Homeomorph.finTwoArrow : (Fin 2 → ℝ) ≃ₜ ℝ × ℝ).symm.trans
          (EuclideanSpace.equiv (Fin 2) ℝ).symm.toHomeomorph))
  exact s78dg_euclid_nbhd ((chartAt ℂ x).trans L.toOpenPartialHomeomorph) (x := x)
    ⟨mem_chart_source ℂ x, by simp⟩

/-- **No surface without boundary is homeomorphic to a polygon quotient with free boundary arcs**
(orientable normal form with `n ≥ 1`). -/
theorem s78dg_no_orientable_boundary {S : Type*} [TopologicalSpace S]
    (hS : ∀ x : S, ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)))
    (p n : ℕ) (hn : 1 ≤ n) (φ : S ≃ₜ Quot (OrientableRel p n)) : False := by
  let q₀ := Quot.mk (OrientableRel p n) (ClosedUnitDisc.bdyPtOfReal (-(3 / 2 : ℝ) / (4 * p + 3 * n)))
  obtain ⟨U, hU, hxU, ⟨h⟩⟩ := hS (φ.symm q₀)
  refine s78dg_orientable_free p n hn (φ '' U) (φ.isOpenMap U hU) ?_ ((φ.image U).symm.trans h)
  exact ⟨φ.symm q₀, hxU, φ.apply_symm_apply q₀⟩

end

end LiZhongQC
