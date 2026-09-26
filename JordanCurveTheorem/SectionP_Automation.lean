/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionO_ComplementConnectivity

/-!
# Section P: Geometric Transformations and Plane Graph Images
## HOL Light: Section P (Lines 32514–34152)

This section defines:
- `planeGraphImage`: the image of a plane graph under a homeomorphism `f : E2' ≃ₜ E2'`
- `hCompat` / `vCompat`: horizontal/vertical line-segment compatibility
- `hTranslate` / `vTranslate`: horizontal and vertical translations
- `rScale` / `uScale`: conditional coordinate scalings
- Proofs that all four transformations are homeomorphisms with h/v-compatibility

The HOL Light tactical infrastructure (UNDISCHQ_TAC, UNABBREV_TAC, SUBAGOAL_TAC,
RSIMP_TAC, EVERY_STEP_TAC, extend_simp_rewrites) is not needed in Lean — Lean's
native tactic framework covers all of these.
-/

open Set Metric Topology Function

noncomputable section

/-! ## subset_imp (helper lemma) -/

/-- HOL Light: `subset_imp` (line 32570). -/
theorem subset_imp {α : Type*} {A B : Set α} {x : α} (hx : x ∈ A) (hAB : A ⊆ B) :
    x ∈ B :=
  hAB hx

/-! ## Plane graph image under a homeomorphism -/

/-- Image of a plane graph under a homeomorphism `f : E2' ≃ₜ E2'`.
    HOL Light: `plane_graph_image` (line 32586). -/
def planeGraphImage (f : E2' ≃ₜ E2') (G : HolGraph E2' (Set E2'))
    (_hG : IsPlaneGraph G) :
    HolGraph E2' (Set E2') where
  vertexSet := f '' G.vertexSet
  edgeSet := (f '' ·) '' G.edgeSet
  inc := fun e' => {v | ∃ e ∈ G.edgeSet, f '' e = e' ∧ ∃ v' ∈ G.inc e, f v' = v}
  well_formed := by
    rintro _ ⟨e, he, rfl⟩
    have hwf := G.well_formed e he
    have inc_eq : {v | ∃ e₂ ∈ G.edgeSet, f '' e₂ = f '' e ∧ ∃ v' ∈ G.inc e₂, f v' = v} =
        f '' (G.inc e) := by
      ext v; simp only [Set.mem_setOf_eq, Set.mem_image]; constructor
      · rintro ⟨e₂, he₂, hfe₂, v', hv', rfl⟩
        exact ⟨v', f.injective.image_injective hfe₂ ▸ hv', rfl⟩
      · rintro ⟨v', hv', rfl⟩; exact ⟨e, he, rfl, v', hv', rfl⟩
    rw [inc_eq]
    exact ⟨Set.image_mono hwf.1, (Set.ncard_image_of_injective _ f.injective).trans hwf.2⟩

/-- Edge set of `planeGraphImage`.
    HOL Light: `plane_graph_image_e` (line 32596). -/
theorem planeGraphImage_edgeSet (f : E2' ≃ₜ E2') (G : HolGraph E2' (Set E2'))
    (hG : IsPlaneGraph G) :
    (planeGraphImage f G hG).edgeSet = (f '' ·) '' G.edgeSet := by
  rfl

/-- Vertex set of `planeGraphImage`.
    HOL Light: `plane_graph_image_v` (line 32607). -/
theorem planeGraphImage_vertexSet (f : E2' ≃ₜ E2') (G : HolGraph E2' (Set E2'))
    (hG : IsPlaneGraph G) :
    (planeGraphImage f G hG).vertexSet = f '' G.vertexSet := by
  rfl

/-- Incidence of `planeGraphImage`.
    HOL Light: `plane_graph_image_i` (line 32618). -/
theorem planeGraphImage_inc (f : E2' ≃ₜ E2') (G : HolGraph E2' (Set E2'))
    (hG : IsPlaneGraph G) (e' : Set E2') :
    (planeGraphImage f G hG).inc e' =
      {v | ∃ e ∈ G.edgeSet, f '' e = e' ∧ ∃ v' ∈ G.inc e, f v' = v} := by
  rfl

/-- HOL Light: `plane_graph_image_bij` (line 32631).
    A homeomorphism is bijective on vertices and on edges (as sets). -/
theorem planeGraphImage_bij (f : E2' ≃ₜ E2') (G : HolGraph E2' (Set E2'))
    (_hG : IsPlaneGraph G) :
    BijOn f G.vertexSet (f '' G.vertexSet) ∧
    BijOn (f '' ·) G.edgeSet ((f '' ·) '' G.edgeSet) :=
  ⟨f.injective.injOn.bijOn_image, f.injective.image_injective.injOn.bijOn_image⟩

/-- HOL Light: `plane_graph_image_iso` (line 32668).
    A homeomorphism induces a graph isomorphism. -/
theorem planeGraphImage_iso (f : E2' ≃ₜ E2') (G : HolGraph E2' (Set E2'))
    (hG : IsPlaneGraph G) :
    GraphIsomorphic G (planeGraphImage f G hG) :=
  ⟨{
    vertexMap := f
    edgeMap := (f '' ·)
    vertexBij := f.injective.injOn.bijOn_image
    edgeBij := f.injective.image_injective.injOn.bijOn_image
    preserves_inc := by
      intro e he
      ext v; simp only [planeGraphImage, Set.mem_setOf_eq, Set.mem_image]; constructor
      · rintro ⟨e₂, he₂, hfe₂, v', hv', rfl⟩
        exact ⟨v', f.injective.image_injective hfe₂ ▸ hv', rfl⟩
      · rintro ⟨v', hv', rfl⟩; exact ⟨e, he, rfl, v', hv', rfl⟩
  }⟩

/-- HOL Light: `simple_arc_end_cont` (line 32758).
    Alternative characterization of `IsSimpleArcEnd` using continuous injective
    function on `[0,1]`. In Lean, `IsSimpleArcEnd` is already defined this way,
    so this is `Iff.rfl`. -/
theorem isSimpleArcEnd_iff_continuous_inj (C : Set E2') (v v' : E2') :
    IsSimpleArcEnd C v v' ↔
    ∃ f : ℝ → E2', C = f '' Icc 0 1 ∧
      Continuous f ∧ InjOn f (Icc 0 1) ∧ f 0 = v ∧ f 1 = v' := by
  rfl

-- HOL Light: `graph_edge_euclid` (line 32789).
-- Not applicable to Lean: edges of a `Graph E2' (Set E2')` are `Set E2'`
-- by construction, so they are trivially subsets of the universe.

/-- HOL Light: `plane_graph_image_plane` (line 32803).
    A homeomorphism applied to a good plane graph yields a good plane graph. -/
theorem planeGraphImage_goodPlaneGraph (f : E2' ≃ₜ E2')
    (G : HolGraph E2' (Set E2')) (hG : IsGoodPlaneGraph G) :
    IsGoodPlaneGraph (planeGraphImage f G hG.1) := by
  set PGI := planeGraphImage f G hG.1
  have inc_eq : ∀ e ∈ G.edgeSet, PGI.inc (f '' e) = f '' (G.inc e) := by
    intro e he; ext v; simp only [Set.mem_image]; constructor
    · rintro ⟨e₂, he₂, hfe₂, v', hv', rfl⟩
      exact ⟨v', f.injective.image_injective hfe₂ ▸ hv', rfl⟩
    · rintro ⟨v', hv', rfl⟩; exact ⟨e, he, rfl, v', hv', rfl⟩
  have arc_transport : ∀ (C : Set E2') (v v' : E2'),
      IsSimpleArcEnd C v v' → IsSimpleArcEnd (f '' C) (f v) (f v') := by
    intro C v v' ⟨g, hC, hcont, hinj, hg0, hg1⟩
    exact ⟨f ∘ g, by rw [hC, Set.image_comp], f.continuous.comp hcont,
      f.injective.comp_injOn hinj, by simp [hg0], by simp [hg1]⟩
  constructor
  · constructor
    · -- edges_are_arcs
      rintro _ ⟨e, he, rfl⟩
      obtain ⟨v, v', hv, hv', hne, hsae⟩ := hG.1.edges_are_arcs e he
      exact ⟨f v, f v', by rw [inc_eq e he]; exact Set.mem_image_of_mem f hv,
        by rw [inc_eq e he]; exact Set.mem_image_of_mem f hv',
        f.injective.ne hne, arc_transport e v v' hsae⟩
    · -- vertex_on_edge
      rintro _ ⟨e, he, rfl⟩ _ ⟨v₀, hv₀, rfl⟩ ⟨w, hw, hwf⟩
      rw [inc_eq e he]
      have : w = v₀ := f.injective hwf; subst this
      exact Set.mem_image_of_mem f (hG.1.vertex_on_edge e he w hv₀ hw)
    · -- edges_disjoint_interior
      rintro _ _ ⟨e₁, he₁, rfl⟩ ⟨e₂, he₂, rfl⟩ hne
      have hne' : e₁ ≠ e₂ := fun h => hne (congrArg (f '' ·) h)
      intro v ⟨⟨w₁, hw₁, hwf₁⟩, ⟨w₂, hw₂, hwf₂⟩⟩
      subst hwf₁
      have : w₁ = w₂ := f.injective hwf₂.symm; subst this
      exact Set.mem_image_of_mem f (hG.1.edges_disjoint_interior e₁ e₂ he₁ he₂ hne' ⟨hw₁, hw₂⟩)
  · -- IsGoodPlaneGraph condition
    rintro _ ⟨e, he, rfl⟩ v v' hv hv' hne
    rw [inc_eq e he] at hv hv'
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    obtain ⟨v₀', hv₀', rfl⟩ := hv'
    exact arc_transport e v₀ v₀' (hG.2 e he v₀ v₀' hv₀ hv₀' (fun h => hne (congrArg f h)))

/-! ## h_compat and v_compat -/

/-- A function is horizontally compatible: it maps horizontal line segments
    (segments between points with equal y-coordinate) to line segments.
    HOL Light: `h_compat` (line 32954). -/
def hCompat (f : E2' → E2') : Prop :=
  ∀ x y : ℝ × ℝ, x.2 = y.2 →
    f '' mkLine (point x) (point y) = mkLine (f (point x)) (f (point y))

/-- A function is vertically compatible: it maps vertical line segments
    (segments between points with equal x-coordinate) to line segments.
    HOL Light: `v_compat` (line 32955). -/
def vCompat (f : E2' → E2') : Prop :=
  ∀ x y : ℝ × ℝ, x.1 = y.1 →
    f '' mkLine (point x) (point y) = mkLine (f (point x)) (f (point y))

/-! ## Geometric transformations: definitions -/

/-- Horizontal translation by `r`.
    HOL Light: `h_translate` (line 32956). -/
def hTranslate (r : ℝ) (p : E2') : E2' :=
  (WithLp.equiv 2 _).symm (p.ofLp + fun i => if i = (0 : Fin 2) then r else 0)

/-- Vertical translation by `r`.
    HOL Light: `v_translate` (line 32958). -/
def vTranslate (r : ℝ) (p : E2') : E2' :=
  (WithLp.equiv 2 _).symm (p.ofLp + fun i => if i = (1 : Fin 2) then r else 0)

/-- Right-half-plane x-coordinate scaling by `r`.
    Scales the x-coordinate by `r` when `x > 0`; identity otherwise.
    HOL Light: `r_scale` (line 32960). -/
def rScale (r : ℝ) (p : E2') : E2' :=
  if 0 < p 0 then point (r * p 0, p 1) else p

/-- Upper-half-plane y-coordinate scaling by `r`.
    Scales the y-coordinate by `r` when `y > 0`; identity otherwise.
    HOL Light: `u_scale` (line 32963). -/
def uScale (r : ℝ) (p : E2') : E2' :=
  if 0 < p 1 then point (p 0, r * p 1) else p

/-! ## cont_domain -/

/-- If `f` is continuous and `g` agrees with `f` everywhere, then `g` is continuous.
    HOL Light: `cont_domain` (line 32966).
    In Lean this follows from `Continuous.congr`. -/
theorem cont_domain {f g : E2' → E2'} (hf : Continuous f)
    (hfg : ∀ x, f x = g x) : Continuous g :=
  hf.congr (fun x => hfg x)

/-! ## Inverses (needed before bijectivity) -/

/-- HOL Light: `h_translate_inv` (line 33160). -/
theorem hTranslate_leftInverse (r : ℝ) :
    LeftInverse (hTranslate (-r)) (hTranslate r) := by
  intro p; ext i; simp [hTranslate]; split_ifs <;> linarith

/-- HOL Light: `v_translate_inv` (line 33177). -/
theorem vTranslate_leftInverse (r : ℝ) :
    LeftInverse (vTranslate (-r)) (vTranslate r) := by
  intro p; ext i; simp [vTranslate]; split_ifs <;> linarith

private theorem rScale_eq_pos {r : ℝ} (p : E2') (h : 0 < p 0) :
    rScale r p = point (r * p 0, p 1) := by
  simp [rScale, h]

private theorem rScale_eq_nonpos {r : ℝ} (p : E2') (h : ¬(0 < p 0)) :
    rScale r p = p := by
  simp [rScale, h]

private theorem uScale_eq_pos {r : ℝ} (p : E2') (h : 0 < p 1) :
    uScale r p = point (p 0, r * p 1) := by
  simp [uScale, h]

private theorem uScale_eq_nonpos {r : ℝ} (p : E2') (h : ¬(0 < p 1)) :
    uScale r p = p := by
  simp [uScale, h]

/-- HOL Light: `r_scale_inv` (line 33228). -/
theorem rScale_leftInverse {r : ℝ} (hr : 0 < r) :
    LeftInverse (rScale r⁻¹) (rScale r) := by
  intro p
  by_cases h : (0 : ℝ) < p 0
  · rw [rScale_eq_pos p h]
    have h2 : (0 : ℝ) < (point (r * p 0, p 1)) 0 := by simp [mul_pos hr h]
    rw [rScale_eq_pos _ h2]
    simp only [Fin.isValue, point_coord_zero, point_coord_one, ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hr), one_mul]
    exact (point_surjective p).symm
  · rw [rScale_eq_nonpos p h, rScale_eq_nonpos p h]

/-- HOL Light: `u_scale_inv` (line 33253). -/
theorem uScale_leftInverse {r : ℝ} (hr : 0 < r) :
    LeftInverse (uScale r⁻¹) (uScale r) := by
  intro p
  by_cases h : (0 : ℝ) < p 1
  · rw [uScale_eq_pos p h]
    have h2 : (0 : ℝ) < (point (p 0, r * p 1)) 1 := by simp [mul_pos hr h]
    rw [uScale_eq_pos _ h2]
    simp only [Fin.isValue, point_coord_zero, point_coord_one, ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hr), one_mul]
    exact (point_surjective p).symm
  · rw [uScale_eq_nonpos p h, uScale_eq_nonpos p h]

/-! ## Bijectivity (using inverses) -/

private theorem translate_bijective_of_leftInverse
    {f g : E2' → E2'} (hfg : LeftInverse g f) (hgf : LeftInverse f g) :
    Bijective f :=
  ⟨hfg.injective, hgf.surjective⟩

/-- HOL Light: `h_translate_bij` (line 32979). -/
theorem hTranslate_bijective (r : ℝ) : Bijective (hTranslate r) := by
  refine translate_bijective_of_leftInverse (hTranslate_leftInverse r) ?_
  have h := hTranslate_leftInverse (-r)
  simp only [neg_neg] at h; exact h

/-- HOL Light: `v_translate_bij` (line 33008). -/
theorem vTranslate_bijective (r : ℝ) : Bijective (vTranslate r) := by
  refine translate_bijective_of_leftInverse (vTranslate_leftInverse r) ?_
  have h := vTranslate_leftInverse (-r)
  simp only [neg_neg] at h; exact h

/-- HOL Light: `r_scale_bij` (line 33040). -/
theorem rScale_bijective {r : ℝ} (hr : 0 < r) : Bijective (rScale r) := by
  refine translate_bijective_of_leftInverse (rScale_leftInverse hr) ?_
  have h := rScale_leftInverse (inv_pos.mpr hr)
  simp only [inv_inv] at h; exact h

/-- HOL Light: `u_scale_bij` (line 33101). -/
theorem uScale_bijective {r : ℝ} (hr : 0 < r) : Bijective (uScale r) := by
  refine translate_bijective_of_leftInverse (uScale_leftInverse hr) ?_
  have h := uScale_leftInverse (inv_pos.mpr hr)
  simp only [inv_inv] at h; exact h

/-! ## Continuity -/

-- HOL Light: `metric_continuous_continuous_top2` (line 33275).
-- Not applicable to Lean: metric and topological continuity coincide
-- on `EuclideanSpace ℝ (Fin 2)` by Mathlib's instance.

/-- HOL Light: `h_translate_cont` (line 33291). -/
theorem hTranslate_continuous (r : ℝ) : Continuous (hTranslate r) := by
  change Continuous
    (· + ((WithLp.equiv 2 (Fin 2 → ℝ)).symm
      fun i => if i = (0 : Fin 2) then r else 0 : E2'))
  fun_prop

/-- HOL Light: `v_translate_cont` (line 33311). -/
theorem vTranslate_continuous (r : ℝ) : Continuous (vTranslate r) := by
  change Continuous
    (· + ((WithLp.equiv 2 (Fin 2 → ℝ)).symm
      fun i => if i = (1 : Fin 2) then r else 0 : E2'))
  fun_prop

/-- The real function `x ↦ if 0 < x then r * x else x` is continuous. -/
private theorem continuous_rscale_coord (r : ℝ) :
    Continuous (fun x : ℝ => if x ≤ 0 then x else r * x) :=
  continuous_if_le continuous_id continuous_const continuousOn_id
    (continuousOn_const.mul continuousOn_id) (fun _ h => by simp [h])

/-- The real function `y ↦ if 0 < y then r * y else y` is continuous. -/
private theorem continuous_uscale_coord (r : ℝ) :
    Continuous (fun x : ℝ => if x ≤ 0 then x else r * x) :=
  continuous_rscale_coord r

/-- HOL Light: `r_scale_cont` (line 33332). -/
theorem rScale_continuous {r : ℝ} (_hr : 0 < r) : Continuous (rScale r) := by
  have key : ∀ p : E2', rScale r p =
      point (if p 0 ≤ 0 then p 0 else r * p 0, p 1) := by
    intro p
    simp only [rScale]
    split_ifs with h1 h2 <;> simp_all only [Fin.isValue, not_le.mpr, not_false_eq_true, not_lt]
    exact point_surjective p
  refine (Continuous.congr ?_ (fun p => (key p).symm))
  change Continuous (fun p : E2' =>
    point (if p 0 ≤ 0 then p 0 else r * p 0, p 1))
  unfold point
  apply (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i; fin_cases i
  · simpa [Function.comp_def] using (continuous_rscale_coord r).comp
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)
  · simpa using PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1

/-- HOL Light: `u_scale_cont` (line 33444). -/
theorem uScale_continuous {r : ℝ} (_hr : 0 < r) : Continuous (uScale r) := by
  have key : ∀ p : E2', uScale r p =
      point (p 0, if p 1 ≤ 0 then p 1 else r * p 1) := by
    intro p
    simp only [uScale]
    split_ifs with h1 h2 <;> simp_all only [Fin.isValue, not_le.mpr, not_false_eq_true, not_lt]
    exact point_surjective p
  refine (Continuous.congr ?_ (fun p => (key p).symm))
  change Continuous (fun p : E2' =>
    point (p 0, if p 1 ≤ 0 then p 1 else r * p 1))
  unfold point
  apply (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i; fin_cases i
  · simpa using PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0
  · simpa [Function.comp_def] using (continuous_uscale_coord r).comp
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)

/-! ## Homeomorphisms -/

/-- HOL Light: `h_translate_hom` (line 33556). -/
def hTranslate_homeomorph (r : ℝ) : E2' ≃ₜ E2' where
  toFun := hTranslate r
  invFun := hTranslate (-r)
  left_inv := hTranslate_leftInverse r
  right_inv x := by
    have := hTranslate_leftInverse (-r) x; simp only [neg_neg] at this
    exact this
  continuous_toFun := hTranslate_continuous r
  continuous_invFun := hTranslate_continuous (-r)

/-- HOL Light: `v_translate_hom` (line 33568). -/
def vTranslate_homeomorph (r : ℝ) : E2' ≃ₜ E2' where
  toFun := vTranslate r
  invFun := vTranslate (-r)
  left_inv := vTranslate_leftInverse r
  right_inv x := by
    have := vTranslate_leftInverse (-r) x; simp only [neg_neg] at this
    exact this
  continuous_toFun := vTranslate_continuous r
  continuous_invFun := vTranslate_continuous (-r)

/-- HOL Light: `r_scale_hom` (line 33580). -/
def rScale_homeomorph {r : ℝ} (hr : 0 < r) : E2' ≃ₜ E2' where
  toFun := rScale r
  invFun := rScale r⁻¹
  left_inv := rScale_leftInverse hr
  right_inv x := by
    have := rScale_leftInverse (inv_pos.mpr hr) x
    simp only [inv_inv] at this; exact this
  continuous_toFun := rScale_continuous hr
  continuous_invFun := rScale_continuous (inv_pos.mpr hr)

/-- HOL Light: `u_scale_hom` (line 33592). -/
def uScale_homeomorph {r : ℝ} (hr : 0 < r) : E2' ≃ₜ E2' where
  toFun := uScale r
  invFun := uScale r⁻¹
  left_inv := uScale_leftInverse hr
  right_inv x := by
    have := uScale_leftInverse (inv_pos.mpr hr) x
    simp only [inv_inv] at this; exact this
  continuous_toFun := uScale_continuous hr
  continuous_invFun := uScale_continuous (inv_pos.mpr hr)

/-! ## h/v compatibility: translations -/

/-- HOL Light: `h_translate_h` (line 33606). -/
theorem hTranslate_hCompat (r : ℝ) : hCompat (hTranslate r) := by
  have key : ∀ (a b : E2') (t : ℝ),
      hTranslate r (t • a + (1 - t) • b) =
      t • hTranslate r a + (1 - t) • hTranslate r b := by
    intro a b t; ext i; simp only [hTranslate, Fin.isValue, WithLp.equiv_symm_apply,
      WithLp.toLp_add, WithLp.toLp_ofLp, WithLp.ofLp_add, PiLp.add_apply]
    fin_cases i <;> simp ; ring
  intro x y _
  ext z; simp only [mkLine, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, ⟨t, rfl⟩, rfl⟩; exact ⟨t, key _ _ t⟩
  · rintro ⟨t, ht⟩; exact ⟨_, ⟨t, rfl⟩, by rw [key]; exact ht.symm⟩

/-- HOL Light: `v_translate_v` (line 33618). -/
theorem vTranslate_vCompat (r : ℝ) : vCompat (vTranslate r) := by
  have key : ∀ (a b : E2') (t : ℝ),
      vTranslate r (t • a + (1 - t) • b) =
      t • vTranslate r a + (1 - t) • vTranslate r b := by
    intro a b t; ext i; simp only [vTranslate, Fin.isValue, WithLp.equiv_symm_apply,
      WithLp.toLp_add, WithLp.toLp_ofLp, WithLp.ofLp_add, PiLp.add_apply]
    fin_cases i <;> simp ; ring
  intro x y _
  ext z; simp only [mkLine, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, ⟨t, rfl⟩, rfl⟩; exact ⟨t, key _ _ t⟩
  · rintro ⟨t, ht⟩; exact ⟨_, ⟨t, rfl⟩, by rw [key]; exact ht.symm⟩

/-- HOL Light: `h_translate_v` (line 33622). -/
theorem hTranslate_vCompat (r : ℝ) : vCompat (hTranslate r) := by
  have key : ∀ (a b : E2') (t : ℝ),
      hTranslate r (t • a + (1 - t) • b) =
      t • hTranslate r a + (1 - t) • hTranslate r b := by
    intro a b t; ext i; simp only [hTranslate, Fin.isValue, WithLp.equiv_symm_apply,
      WithLp.toLp_add, WithLp.toLp_ofLp, WithLp.ofLp_add, PiLp.add_apply]
    fin_cases i <;> simp ; ring
  intro x y _
  ext z; simp only [mkLine, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, ⟨t, rfl⟩, rfl⟩; exact ⟨t, key _ _ t⟩
  · rintro ⟨t, ht⟩; exact ⟨_, ⟨t, rfl⟩, by rw [key]; exact ht.symm⟩

/-- HOL Light: `v_translate_h` (line 33626). -/
theorem vTranslate_hCompat (r : ℝ) : hCompat (vTranslate r) := by
  have key : ∀ (a b : E2') (t : ℝ),
      vTranslate r (t • a + (1 - t) • b) =
      t • vTranslate r a + (1 - t) • vTranslate r b := by
    intro a b t; ext i; simp only [vTranslate, Fin.isValue, WithLp.equiv_symm_apply,
      WithLp.toLp_add, WithLp.toLp_ofLp, WithLp.ofLp_add, PiLp.add_apply]
    fin_cases i <;> simp ; ring
  intro x y _
  ext z; simp only [mkLine, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, ⟨t, rfl⟩, rfl⟩; exact ⟨t, key _ _ t⟩
  · rintro ⟨t, ht⟩; exact ⟨_, ⟨t, rfl⟩, by rw [key]; exact ht.symm⟩

/-! ## Helper lemmas for compatibility proofs -/

/-- HOL Light: `lin_solve_x` (line 33630). -/
theorem lin_solve_x {c a : ℝ} (hc : c ≠ 0) : ∃ t : ℝ, c * t = a :=
  ⟨a / c, by field_simp⟩

/-- HOL Light: `mk_line_pt` (line 33634). -/
theorem mkLine_self (x : E2') : mkLine x x = {x} := by
  ext z; simp only [mkLine, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, ht⟩; rw [ht]; simp [← add_smul]
  · rintro rfl; exact ⟨0, by simp⟩

/-- HOL Light: `h_compat_bij` (line 33638).
    Sufficient condition for h-compatibility: bijective + preserves y-coord. -/
theorem hCompat_of_bijective_snd (f : E2' → E2') (hbij : Bijective f)
    (hsnd : ∀ x : ℝ × ℝ, (f (point x)) 1 = x.2) : hCompat f := by
  have hf1 : ∀ w : E2', (f w) 1 = w 1 := by
    intro w; have := hsnd (w 0, w 1); rwa [← point_surjective w] at this
  have f_hyp (c : ℝ) : f '' hyperplane2 1 c = hyperplane2 1 c := by
    ext z; simp only [hyperplane2, Set.mem_image, Set.mem_setOf_eq]; constructor
    · rintro ⟨w, hw, rfl⟩; exact (hf1 w).trans hw
    · intro hz; obtain ⟨w, rfl⟩ := hbij.2 z; exact ⟨w, (hf1 w).symm.trans hz, rfl⟩
  have mkLine_hyp (a b : ℝ × ℝ) (hsnd_eq : a.2 = b.2) (hfst : a.1 ≠ b.1) :
      mkLine (point a) (point b) = hyperplane2 1 a.2 := by
    rw [← mkLine_eq_hyperplane2_1 a.2]
    exact (mkLine_eq_of_mem
      (by rw [mkLine_eq_hyperplane2_1]; simp [hyperplane2])
      (by rw [mkLine_eq_hyperplane2_1]; simp [hyperplane2, hsnd_eq])
      (fun h => hfst (congr_arg Prod.fst (point_injective h)))).symm
  intro x y hxy
  by_cases hxy' : x = y
  · subst hxy'; simp [mkLine_self, Set.image_singleton]
  · have hfst : x.1 ≠ y.1 := fun h => hxy' (Prod.ext h hxy)
    have hfne : f (point x) ≠ f (point y) :=
      fun h => hxy' (point_injective (hbij.1 h))
    have hfst' : (f (point x)) 0 ≠ (f (point y)) 0 := by
      intro h
      exact hfne (by ext i; fin_cases i <;>
        [exact h; exact (hsnd x).trans (hxy ▸ (hsnd y).symm)])
    rw [mkLine_hyp x y hxy hfst]
    conv_rhs =>
      rw [point_surjective (f (point x)), point_surjective (f (point y))]
    rw [mkLine_hyp _ _ (by simp [hsnd, hxy]) hfst',
      show (f (point x)) 1 = x.2 from hsnd x]
    exact f_hyp x.2

/-! ## h/v compatibility: scalings -/

/-- HOL Light: `r_scale_h` (line 33773). -/
theorem rScale_hCompat {r : ℝ} (hr : 0 < r) : hCompat (rScale r) := by
  apply hCompat_of_bijective_snd _ (rScale_bijective hr)
  intro x; simp only [rScale]; split_ifs <;> simp

/-- HOL Light: `h_compat_bij2` (line 33862).
    Generalized sufficient condition for h-compatibility. -/
theorem hCompat_of_bijective_snd_inj (f : E2' → E2') (hbij : Bijective f)
    (s : ℝ → ℝ) (hs_inj : Injective s)
    (hsnd : ∀ x : ℝ × ℝ, (f (point x)) 1 = s x.2) : hCompat f := by
  have hf1 : ∀ w : E2', (f w) 1 = s (w 1) := by
    intro w; have := hsnd (w 0, w 1); rwa [← point_surjective w] at this
  have f_hyp (c : ℝ) : f '' hyperplane2 1 c = hyperplane2 1 (s c) := by
    ext z; simp only [hyperplane2, Set.mem_image, Set.mem_setOf_eq]; constructor
    · rintro ⟨w, hw, rfl⟩; exact (hf1 w).trans (congrArg s hw)
    · intro hz; obtain ⟨w, rfl⟩ := hbij.2 z
      exact ⟨w, hs_inj ((hf1 w).symm.trans hz), rfl⟩
  have mkLine_hyp (a b : ℝ × ℝ) (hsnd_eq : a.2 = b.2) (hfst : a.1 ≠ b.1) :
      mkLine (point a) (point b) = hyperplane2 1 a.2 := by
    rw [← mkLine_eq_hyperplane2_1 a.2]
    exact (mkLine_eq_of_mem
      (by rw [mkLine_eq_hyperplane2_1]; simp [hyperplane2])
      (by rw [mkLine_eq_hyperplane2_1]; simp [hyperplane2, hsnd_eq])
      (fun h => hfst (congr_arg Prod.fst (point_injective h)))).symm
  intro x y hxy
  by_cases hxy' : x = y
  · subst hxy'; simp [mkLine_self, Set.image_singleton]
  · have hfst : x.1 ≠ y.1 := fun h => hxy' (Prod.ext h hxy)
    have hfne : f (point x) ≠ f (point y) :=
      fun h => hxy' (point_injective (hbij.1 h))
    have hfst' : (f (point x)) 0 ≠ (f (point y)) 0 := by
      intro h
      exact hfne (by ext i; fin_cases i <;>
        [exact h; exact (hsnd x).trans (hxy ▸ (hsnd y).symm)])
    rw [mkLine_hyp x y hxy hfst]
    conv_rhs =>
      rw [point_surjective (f (point x)), point_surjective (f (point y))]
    rw [mkLine_hyp _ _ (by simp [hsnd, hxy]) hfst',
      show (f (point x)) 1 = s x.2 from hsnd x]
    exact f_hyp x.2

/-- HOL Light: `u_scale_h` (line 33982). -/
theorem uScale_hCompat {r : ℝ} (hr : 0 < r) : hCompat (uScale r) := by
  refine hCompat_of_bijective_snd_inj _ (uScale_bijective hr)
    (fun z => if 0 < z then r * z else z) (fun a b hab => ?_) (fun x => ?_)
  · by_cases ha : 0 < a <;> by_cases hb : 0 < b <;>
      simp only [ha, hb, ite_true, ite_false] at hab
    · exact mul_left_cancel₀ (ne_of_gt hr) hab
    · linarith [mul_pos hr ha]
    · linarith [mul_pos hr hb]
    · exact hab
  · obtain ⟨x1, x2⟩ := x; simp only [uScale, point_coord_one]; split_ifs <;> simp

/-- HOL Light: `v_compat_bij2` (line 34005).
    Sufficient condition for v-compatibility. -/
theorem vCompat_of_bijective_fst_inj (f : E2' → E2') (hbij : Bijective f)
    (s : ℝ → ℝ) (hs_inj : Injective s)
    (hfst : ∀ x : ℝ × ℝ, (f (point x)) 0 = s x.1) : vCompat f := by
  have hf0 : ∀ w : E2', (f w) 0 = s (w 0) := by
    intro w; have := hfst (w 0, w 1); rwa [← point_surjective w] at this
  have f_hyp (c : ℝ) : f '' hyperplane2 0 c = hyperplane2 0 (s c) := by
    ext z; simp only [hyperplane2, Set.mem_image, Set.mem_setOf_eq]; constructor
    · rintro ⟨w, hw, rfl⟩; exact (hf0 w).trans (congrArg s hw)
    · intro hz; obtain ⟨w, rfl⟩ := hbij.2 z
      exact ⟨w, hs_inj ((hf0 w).symm.trans hz), rfl⟩
  have mkLine_hyp (a b : ℝ × ℝ) (hfst_eq : a.1 = b.1) (hsnd : a.2 ≠ b.2) :
      mkLine (point a) (point b) = hyperplane2 0 a.1 := by
    rw [← mkLine_eq_hyperplane2_0 a.1]
    exact (mkLine_eq_of_mem
      (by rw [mkLine_eq_hyperplane2_0]; simp [hyperplane2])
      (by rw [mkLine_eq_hyperplane2_0]; simp [hyperplane2, hfst_eq])
      (fun h => hsnd (congr_arg Prod.snd (point_injective h)))).symm
  intro x y hxy
  by_cases hxy' : x = y
  · subst hxy'; simp [mkLine_self, Set.image_singleton]
  · have hsnd_ne : x.2 ≠ y.2 := fun h => hxy' (Prod.ext hxy h)
    have hfne : f (point x) ≠ f (point y) :=
      fun h => hxy' (point_injective (hbij.1 h))
    have hsnd' : (f (point x)) 1 ≠ (f (point y)) 1 := by
      intro h
      exact hfne (by ext i; fin_cases i <;>
        [exact (hfst x).trans (hxy ▸ (hfst y).symm); exact h])
    rw [mkLine_hyp x y hxy hsnd_ne]
    conv_rhs =>
      rw [point_surjective (f (point x)), point_surjective (f (point y))]
    rw [mkLine_hyp _ _ (by simp [hfst, hxy]) hsnd',
      show (f (point x)) 0 = s x.1 from hfst x]
    exact f_hyp x.1

/-- HOL Light: `r_scale_v` (line 34090). -/
theorem rScale_vCompat {r : ℝ} (hr : 0 < r) : vCompat (rScale r) := by
  refine vCompat_of_bijective_fst_inj _ (rScale_bijective hr)
    (fun z => if 0 < z then r * z else z) (fun a b hab => ?_) (fun x => ?_)
  · by_cases ha : 0 < a <;> by_cases hb : 0 < b <;>
      simp only [ha, hb, ite_true, ite_false] at hab
    · exact mul_left_cancel₀ (ne_of_gt hr) hab
    · linarith [mul_pos hr ha]
    · linarith [mul_pos hr hb]
    · exact hab
  · obtain ⟨x1, x2⟩ := x; simp only [rScale, point_coord_zero]; split_ifs <;> simp

/-- HOL Light: `u_scale_v` (line 34127). -/
theorem uScale_vCompat {r : ℝ} (hr : 0 < r) : vCompat (uScale r) := by
  apply vCompat_of_bijective_fst_inj _ (uScale_bijective hr) id injective_id
  intro x; simp only [uScale, id]; split_ifs <;> simp

end
