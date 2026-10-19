import LiZhongExternal.Classification.SchottkyClassification01
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology

namespace LiZhongQC

theorem s78dg_cs_bdy_norm (r : ℝ) : ‖((ClosedUnitDisc.bdyPtOfReal r : ClosedUnitDisc) : ℂ)‖ = 1 := by
  simp [ClosedUnitDisc.bdyPtOfReal]

/-- Both ends of a gluing relation of the orientable normal form lie on the boundary circle. -/
theorem s78dg_cs_rel_boundary {p n : ℕ} {x y : ClosedUnitDisc} (h : OrientableRel p n x y) :
    ‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1 := by
  cases h <;> exact ⟨s78dg_cs_bdy_norm _, s78dg_cs_bdy_norm _⟩

/-- The equivalence closure identifies only boundary points. -/
theorem s78dg_cs_eqv_boundary {p n : ℕ} {x y : ClosedUnitDisc}
    (h : Relation.EqvGen (OrientableRel p n) x y) :
    x = y ∨ (‖(x : ℂ)‖ = 1 ∧ ‖(y : ℂ)‖ = 1) := by
  induction h with
  | rel a b hab => exact Or.inr (s78dg_cs_rel_boundary hab)
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
theorem s78dg_cs_interior_class {p n : ℕ} {x y : ClosedUnitDisc} (hx : ‖(x : ℂ)‖ < 1)
    (h : Relation.EqvGen (OrientableRel p n) x y) : x = y := by
  rcases s78dg_cs_eqv_boundary h with h1 | h1
  · exact h1
  · exact absurd h1.1 hx.ne

/-- Quotient classes of interior points are singletons: `π⁻¹ π S = S` for `S` inside the open disc. -/
theorem s78dg_cs_saturated_interior {p n : ℕ} {S : Set ClosedUnitDisc}
    (hS : ∀ x ∈ S, ‖(x : ℂ)‖ < 1) :
    (Quot.mk (OrientableRel p n)) ⁻¹' ((Quot.mk (OrientableRel p n)) '' S) = S := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    have := Quot.eqvGen_exact hxy
    rw [← s78dg_cs_interior_class (hS x hx) this]
    exact hx
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- An open subset of the disc lying inside the open disc embeds as an open subset of the quotient. -/
theorem s78dg_cs_open_embedding {p n : ℕ} (S : Set ClosedUnitDisc) (hS : IsOpen S)
    (hSi : ∀ x ∈ S, ‖(x : ℂ)‖ < 1) :
    IsOpenEmbedding (fun z : S => (Quot.mk (OrientableRel p n) (z : ClosedUnitDisc))) := by
  have hinj : Function.Injective (fun z : S => (Quot.mk (OrientableRel p n) (z : ClosedUnitDisc))) := by
    intro z w hzw
    have := Quot.eqvGen_exact hzw
    exact Subtype.ext (s78dg_cs_interior_class (hSi z z.2) this)
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
  have himg : (fun z : S => (Quot.mk (OrientableRel p n) (z : ClosedUnitDisc))) '' (Subtype.val ⁻¹' W') =
      (Quot.mk (OrientableRel p n)) '' (W' ∩ S) := by
    rw [← hsub, ← Set.image_comp]
    rfl
  rw [himg]
  have hsat := s78dg_cs_saturated_interior (p := p) (n := n)
    (S := W' ∩ S) (fun x hx => hSi x hx.2)
  have hopen : IsOpen (W' ∩ S) := hW'.inter hS
  rw [← isQuotientMap_quot_mk.isOpen_preimage, hsat]
  exact hopen

/-- The image of the open disc in the closed surface `Quot (OrientableRel p n)` (the open 2-cell). -/
def s78dg_cs_V (p n : ℕ) : Set (Quot (OrientableRel p n)) :=
  (Quot.mk (OrientableRel p n)) '' {z : ClosedUnitDisc | ‖(z : ℂ)‖ < 1}

/-- The image of the punctured disc: the closed surface minus the centre of the 2-cell. -/
def s78dg_cs_U (p n : ℕ) : Set (Quot (OrientableRel p n)) :=
  (Quot.mk (OrientableRel p n)) '' {z : ClosedUnitDisc | (z : ℂ) ≠ 0}

theorem s78dg_cs_V_open (p n : ℕ) : IsOpen (s78dg_cs_V p n) := by
  have hsat := s78dg_cs_saturated_interior (p := p) (n := n)
    (S := {z : ClosedUnitDisc | ‖(z : ℂ)‖ < 1}) (fun x hx => hx)
  rw [← isQuotientMap_quot_mk.isOpen_preimage]
  change IsOpen ((Quot.mk (OrientableRel p n)) ⁻¹'
    ((Quot.mk (OrientableRel p n)) '' {z : ClosedUnitDisc | ‖(z : ℂ)‖ < 1}))
  rw [hsat]
  exact isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const

theorem s78dg_cs_U_open (p n : ℕ) : IsOpen (s78dg_cs_U p n) := by
  rw [← isQuotientMap_quot_mk.isOpen_preimage]
  have : (Quot.mk (OrientableRel p n)) ⁻¹' (s78dg_cs_U p n) = {z : ClosedUnitDisc | (z : ℂ) ≠ 0} := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have := Quot.eqvGen_exact hxy
      rcases s78dg_cs_eqv_boundary this with h | h
      · rw [← h]; exact hx
      · intro hy0
        have := h.2
        rw [hy0, norm_zero] at this
        exact zero_ne_one this
    · intro hy
      exact ⟨y, hy, rfl⟩
  rw [this]
  exact isOpen_ne_fun (continuous_subtype_val) continuous_const

theorem s78dg_cs_cover (p n : ℕ) : s78dg_cs_U p n ∪ s78dg_cs_V p n = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro q
  obtain ⟨z, rfl⟩ := Quot.exists_rep q
  by_cases hz : (z : ℂ) = 0
  · right
    exact ⟨z, by show ‖(z : ℂ)‖ < 1; rw [hz]; simp, rfl⟩
  · left
    exact ⟨z, hz, rfl⟩

/-- The open 2-cell is homeomorphic to the open unit disc. -/
theorem s78dg_cs_V_homeo (p n : ℕ) :
    Nonempty (↥(s78dg_cs_V p n) ≃ₜ ↥(Metric.ball (0 : ℂ) 1)) := by
  let S : Set ClosedUnitDisc := {z | ‖(z : ℂ)‖ < 1}
  have hS : IsOpen S := isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  have hemb := s78dg_cs_open_embedding (p := p) (n := n) S hS (fun x hx => hx)
  have hrange : Set.range (fun z : S => (Quot.mk (OrientableRel p n) (z : ClosedUnitDisc))) =
      s78dg_cs_V p n := by
    ext q
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, z.2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
  let e1 : S ≃ₜ ↥(s78dg_cs_V p n) :=
    hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  let e2 : S ≃ₜ ↥(Metric.ball (0 : ℂ) 1) :=
    { toFun := fun z => ⟨(z.1 : ℂ), mem_ball_zero_iff.2 z.2⟩
      invFun := fun w => ⟨⟨(w : ℂ), mem_closedBall_zero_iff.2 (mem_ball_zero_iff.1 w.2).le⟩, mem_ball_zero_iff.1 w.2⟩
      left_inv := fun z => rfl
      right_inv := fun w => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact ⟨e1.symm.trans e2⟩

theorem s78dg_cs_V_contractible (p n : ℕ) : ContractibleSpace ↥(s78dg_cs_V p n) := by
  obtain ⟨e⟩ := s78dg_cs_V_homeo p n
  have : ContractibleSpace ↥(Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, by simp⟩
  exact e.contractibleSpace

end LiZhongQC
