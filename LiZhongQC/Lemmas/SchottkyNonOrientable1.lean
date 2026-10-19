import LiZhongQC.Lemmas.SchottkyGenusBridge3

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval

namespace LiZhongQC

/-- The image of the open disc in the closed surface `Quot R` (the open 2-cell). -/
def s78dg_gr_V (R : ClosedUnitDisc → ClosedUnitDisc → Prop) : Set (Quot R) :=
  (Quot.mk R) '' {z : ClosedUnitDisc | ‖(z : ℂ)‖ < 1}

/-- The image of the punctured disc: the closed surface minus the centre of the 2-cell. -/
def s78dg_gr_U (R : ClosedUnitDisc → ClosedUnitDisc → Prop) : Set (Quot R) :=
  (Quot.mk R) '' {z : ClosedUnitDisc | (z : ℂ) ≠ 0}

variable {R : ClosedUnitDisc → ClosedUnitDisc → Prop}
  (hb : ∀ x y, R x y → ‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1)
include hb

/-- The equivalence closure identifies only boundary points. -/
theorem s78dg_gr_eqv_boundary {x y : ClosedUnitDisc}
    (h : Relation.EqvGen R x y) :
    x = y ∨ (‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1) := by
  induction h with
  | rel a b hab => exact Or.inr (hb a b hab)
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

/-- An interior point is related only to itself. -/
theorem s78dg_gr_interior_class {x y : ClosedUnitDisc} (hx : ‖(x : ℂ)‖ < 1)
    (h : Relation.EqvGen R x y) : x = y := by
  rcases s78dg_gr_eqv_boundary hb h with h1 | h1
  · exact h1
  · exact absurd h1.1 hx.ne

/-- Quotient classes of interior points are singletons: `π⁻¹ π S = S` for `S` inside the open disc. -/
theorem s78dg_gr_saturated_interior {S : Set ClosedUnitDisc}
    (hS : ∀ x ∈ S, ‖(x : ℂ)‖ < 1) :
    (Quot.mk R) ⁻¹' ((Quot.mk R) '' S) = S := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    have := Quot.eqvGen_exact hxy
    rw [← s78dg_gr_interior_class hb (hS x hx) this]
    exact hx
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- An open subset of the disc lying inside the open disc embeds as an open subset of the quotient. -/
theorem s78dg_gr_open_embedding (S : Set ClosedUnitDisc) (hS : IsOpen S)
    (hSi : ∀ x ∈ S, ‖(x : ℂ)‖ < 1) :
    IsOpenEmbedding (fun z : S => (Quot.mk R (z : ClosedUnitDisc))) := by
  have hinj : Function.Injective (fun z : S => (Quot.mk R (z : ClosedUnitDisc))) := by
    intro z w hzw
    have := Quot.eqvGen_exact hzw
    exact Subtype.ext (s78dg_gr_interior_class hb (hSi z z.2) this)
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
  have hsat := s78dg_gr_saturated_interior hb
    (S := W' ∩ S) (fun x hx => hSi x hx.2)
  have hopen : IsOpen (W' ∩ S) := hW'.inter hS
  rw [← isQuotientMap_quot_mk.isOpen_preimage, hsat]
  exact hopen

theorem s78dg_gr_V_open : IsOpen (s78dg_gr_V R) := by
  have hsat := s78dg_gr_saturated_interior hb
    (S := {z : ClosedUnitDisc | ‖(z : ℂ)‖ < 1}) (fun x hx => hx)
  rw [← isQuotientMap_quot_mk.isOpen_preimage]
  change IsOpen ((Quot.mk R) ⁻¹'
    ((Quot.mk R) '' {z : ClosedUnitDisc | ‖(z : ℂ)‖ < 1}))
  rw [hsat]
  exact isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const

theorem s78dg_gr_U_open : IsOpen (s78dg_gr_U R) := by
  rw [← isQuotientMap_quot_mk.isOpen_preimage]
  have : (Quot.mk R) ⁻¹' (s78dg_gr_U R) = {z : ClosedUnitDisc | (z : ℂ) ≠ 0} := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have := Quot.eqvGen_exact hxy
      rcases s78dg_gr_eqv_boundary hb this with h | h
      · rw [← h]; exact hx
      · intro hy0
        have := h.2
        rw [hy0, norm_zero] at this
        exact zero_ne_one this
    · intro hy
      exact ⟨y, hy, rfl⟩
  rw [this]
  exact isOpen_ne_fun (continuous_subtype_val) continuous_const

theorem s78dg_gr_cover : s78dg_gr_U R ∪ s78dg_gr_V R = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro q
  obtain ⟨z, rfl⟩ := Quot.exists_rep q
  by_cases hz : (z : ℂ) = 0
  · right
    exact ⟨z, by show ‖(z : ℂ)‖ < 1; rw [hz]; simp, rfl⟩
  · left
    exact ⟨z, hz, rfl⟩

/-- The open 2-cell is homeomorphic to the open unit disc. -/
theorem s78dg_gr_V_homeo :
    Nonempty (↥(s78dg_gr_V R) ≃ₜ ↥(Metric.ball (0 : ℂ) 1)) := by
  let S : Set ClosedUnitDisc := {z | ‖(z : ℂ)‖ < 1}
  have hS : IsOpen S := isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  have hemb := s78dg_gr_open_embedding hb S hS (fun x hx => hx)
  have hrange : Set.range (fun z : S => (Quot.mk R (z : ClosedUnitDisc))) =
      s78dg_gr_V R := by
    ext q
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  let e1 : S ≃ₜ ↥(s78dg_gr_V R) :=
    hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  let e2 : S ≃ₜ ↥(Metric.ball (0 : ℂ) 1) :=
    { toFun := fun z => ⟨(z.1 : ℂ), mem_ball_zero_iff.2 z.2⟩
      invFun := fun w => ⟨⟨(w : ℂ), mem_closedBall_zero_iff.2 (mem_ball_zero_iff.1 w.2).le⟩, mem_ball_zero_iff.1 w.2⟩
      left_inv := fun z => rfl
      right_inv := fun w => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact ⟨e1.symm.trans e2⟩

theorem s78dg_gr_V_contractible : ContractibleSpace ↥(s78dg_gr_V R) := by
  obtain ⟨e⟩ := s78dg_gr_V_homeo hb
  have : ContractibleSpace ↥(Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, by simp⟩
  exact e.contractibleSpace


/-- The overlap of the two charts is the image of the punctured open disc. -/
theorem s78dg_gr_overlap_range :
    Set.range (fun z : {z : ClosedUnitDisc | 0 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < 1} =>
      (Quot.mk R (z : ClosedUnitDisc))) =
      s78dg_gr_U R ∩ s78dg_gr_V R := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨⟨z, fun h => z.2.1.ne' (by rw [h, norm_zero]), rfl⟩, ⟨z, z.2.2, rfl⟩⟩
  · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have h := Quot.eqvGen_exact hxy
    rcases s78dg_gr_eqv_boundary hb h with h1 | h1
    · have hy' : ‖(y : ℂ)‖ < 1 := hy
      rw [h1] at hy'
      exact ⟨⟨x, ⟨norm_pos_iff.2 hx, hy'⟩⟩, rfl⟩
    · have hy' : ‖(y : ℂ)‖ < 1 := hy
      exact absurd h1.1 hy'.ne


/-- **π₁ of the overlap.**  The overlap of the two charts has fundamental group `ℤ`, generated by the
loop `t ↦ π(½·e^{2πit})`. -/
theorem s78dg_gr_overlap_generator :
    ∃ (b : ↥(s78dg_gr_U R ∩ s78dg_gr_V R)) (γ : Path b b),
      (∀ t : I, ∃ x : ClosedUnitDisc,
        (x : ℂ) = (1 / 2 : ℝ) • ((Circle.exp (2 * Real.pi * (t : ℝ)) : Circle) : ℂ) ∧
          ((γ t : ↥(s78dg_gr_U R ∩ s78dg_gr_V R)) : Quot R) =
            Quot.mk R x) ∧
        ∀ z : FundamentalGroup ↥(s78dg_gr_U R ∩ s78dg_gr_V R) b,
          z ∈ Subgroup.zpowers (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) := by
  -- the homeomorphism from the punctured disc onto the overlap
  let S' : Set ClosedUnitDisc := {z | 0 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < 1}
  have hS' : IsOpen S' :=
    (isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)).inter
      (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const)
  have hemb := s78dg_gr_open_embedding hb S' hS' (fun x hx => hx.2)
  let e1 : S' ≃ₜ ↥(s78dg_gr_U R ∩ s78dg_gr_V R) :=
    hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr (s78dg_gr_overlap_range hb))
  let e2 : S' ≃ₜ {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    { toFun := fun z => ⟨(z.1 : ℂ), z.2⟩
      invFun := fun w => ⟨⟨(w : ℂ), mem_closedBall_zero_iff.2 w.2.2.le⟩, w.2⟩
      left_inv := fun z => rfl
      right_inv := fun w => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let Φ : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} ≃ₜ ↥(s78dg_gr_U R ∩ s78dg_gr_V R) := e2.symm.trans e1
  obtain ⟨i, hi, hibij⟩ := s78dg_punctured_disc_pi1
  obtain ⟨γc, hγc, hgen⟩ := s78dg_circle_generator
  let Φc : C({z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}, ↥(s78dg_gr_U R ∩ s78dg_gr_V R)) :=
    ⟨Φ, Φ.continuous⟩
  have hΦbij := s78dg_pi1_homeo_bijective Φ (i 0)
  refine ⟨Φ (i 0), ((γc.map i.continuous).map Φc.continuous), ?_, ?_⟩
  · intro t
    refine ⟨((e2.symm (i (γc t)) : S') : ClosedUnitDisc), ?_, rfl⟩
    change ((i (γc t) : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}) : ℂ) = _
    rw [hi, hγc t]
    congr 2
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
    congr 1
    simp
  · intro z
    obtain ⟨y, rfl⟩ := hΦbij.2 z
    obtain ⟨x, rfl⟩ := hibij.2 y
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hgen x)
    refine ⟨m, ?_⟩
    rw [← hm]
    simp only [map_zpow]
    rfl


end LiZhongQC
