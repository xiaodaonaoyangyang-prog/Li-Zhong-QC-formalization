import LiZhongQC.Ch01.S01_Quadrilateral
import LiZhongQC.Ch01.S03_ExtremalLength

/-!
# Sides of quadrilaterals

Auxiliary results for §4 (Theorem 4.1):

* the sides of a quadrilateral are carried onto sides by an embedding, or by a map continuous
  and injective on a closed subset of `ℂ̄`             — `image_boundaryArc_of_isEmbedding`,
                                                        `image_boundaryArc_of_injOn`;
* a boundary extension of a conformal map carries `∂U` onto `∂V`
                                                      — `IsHomeoExtension.image_frontier`,
                                                        `TopQuad.image_side`;
* the sides `(0, a)` and `(a + bi, bi)` of the rectangle `R(0, a, a+bi, bi)` are its bottom and
  top edges                                           — `boundaryArc_frontier_toExt_rectangle_bottom`,
                                                        `boundaryArc_frontier_toExt_rectangle_top`.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace LiZhongQC

section BoundaryArc

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The closed arc of `K` from `u` to `v` not containing `w` (the shape of `TopQuad.side`): the
points `u`, `v` and the points of `K ∖ {u, v}` lying in a different component than `w`. -/
def boundaryArc (K : Set X) (u v w : X) : Set X :=
  {p ∈ K | p = u ∨ p = v ∨
    connectedComponentIn (K \ {u, v}) p ≠ connectedComponentIn (K \ {u, v}) w}

/-- An embedding maps connected components (in a subset) onto connected components. -/
theorem image_connectedComponentIn_of_isEmbedding {f : X → Y} (hf : IsEmbedding f) (S : Set X)
    (x : X) : f '' connectedComponentIn S x = connectedComponentIn (f '' S) (f x) := by
  by_cases hx : x ∈ S
  · refine subset_antisymm (hf.continuous.image_connectedComponentIn_subset hx) ?_
    have hsub : connectedComponentIn (f '' S) (f x) ⊆ f '' S := connectedComponentIn_subset _ _
    have himg : f '' (f ⁻¹' connectedComponentIn (f '' S) (f x)) =
        connectedComponentIn (f '' S) (f x) :=
      image_preimage_eq_of_subset (hsub.trans (image_subset_range _ _))
    have hpre : IsPreconnected (f ⁻¹' connectedComponentIn (f '' S) (f x)) := by
      rw [← hf.isInducing.isPreconnected_image, himg]
      exact isPreconnected_connectedComponentIn
    rw [← himg]
    refine image_mono (hpre.subset_connectedComponentIn ?_ ?_)
    · exact mem_connectedComponentIn (mem_image_of_mem f hx)
    · intro y hy
      obtain ⟨s, hs, hsy⟩ := hsub hy
      rwa [← hf.injective hsy]
  · rw [connectedComponentIn_eq_empty hx, image_empty, connectedComponentIn_eq_empty]
    rintro ⟨s, hs, hsx⟩
    exact hx (hf.injective hsx ▸ hs)

/-- An embedding maps boundary arcs onto boundary arcs. -/
theorem image_boundaryArc_of_isEmbedding {f : X → Y} (hf : IsEmbedding f) (K : Set X)
    (u v w : X) : f '' boundaryArc K u v w = boundaryArc (f '' K) (f u) (f v) (f w) := by
  have hdiff : f '' (K \ {u, v}) = f '' K \ {f u, f v} := by
    rw [image_diff hf.injective, image_pair]
  ext q
  constructor
  · rintro ⟨p, ⟨hpK, hp⟩, rfl⟩
    refine ⟨mem_image_of_mem f hpK, ?_⟩
    rcases hp with rfl | rfl | hne
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · refine Or.inr (Or.inr fun h => hne (hf.injective.image_injective ?_))
      rwa [image_connectedComponentIn_of_isEmbedding hf,
        image_connectedComponentIn_of_isEmbedding hf, hdiff]
  · rintro ⟨⟨p, hpK, rfl⟩, hp⟩
    refine ⟨p, ⟨hpK, ?_⟩, rfl⟩
    rcases hp with h | h | hne
    · exact Or.inl (hf.injective h)
    · exact Or.inr (Or.inl (hf.injective h))
    · refine Or.inr (Or.inr fun h => hne ?_)
      rw [← hdiff, ← image_connectedComponentIn_of_isEmbedding hf,
        ← image_connectedComponentIn_of_isEmbedding hf, h]

end BoundaryArc

theorem TopQuad.side_eq_boundaryArc (Q : TopQuad) (i : Fin 4) :
    Q.side i =
      boundaryArc (frontier (toExt Q.dom)) (Q.vert i) (Q.vert (i + 1)) (Q.vert (i + 2)) :=
  rfl

/-- A map continuous and injective on a closed subset `C` of `ℂ̄` maps boundary arcs of subsets of
`C` onto boundary arcs. -/
theorem image_boundaryArc_of_injOn {F : ExtPlane → ExtPlane} {C K : Set ExtPlane}
    (hC : IsClosed C) (hF : ContinuousOn F C) (hinj : InjOn F C) (hK : K ⊆ C)
    {u v w : ExtPlane} (hu : u ∈ C) (hv : v ∈ C) (hw : w ∈ C) :
    F '' boundaryArc K u v w = boundaryArc (F '' K) (F u) (F v) (F w) := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC.isCompact
  have he : IsEmbedding (fun x : C => F x) :=
    (hF.restrict.isClosedEmbedding fun x y h => Subtype.ext (hinj x.2 y.2 h)).isEmbedding
  have hK' : ((↑) : C → ExtPlane) '' (((↑) : C → ExtPlane) ⁻¹' K) = K := by
    rw [Subtype.image_preimage_coe, inter_eq_right.2 hK]
  have h1 := image_boundaryArc_of_isEmbedding IsEmbedding.subtypeVal
    (((↑) : C → ExtPlane) ⁻¹' K) ⟨u, hu⟩ ⟨v, hv⟩ ⟨w, hw⟩
  have h2 := image_boundaryArc_of_isEmbedding he
    (((↑) : C → ExtPlane) ⁻¹' K) ⟨u, hu⟩ ⟨v, hv⟩ ⟨w, hw⟩
  rw [hK'] at h1
  dsimp only at h1 h2
  have h3 : (fun x : C => F x) '' (((↑) : C → ExtPlane) ⁻¹' K) = F '' K := by
    conv_rhs => rw [← hK']
    rw [image_image]
  rw [← h1, image_image, h2, h3]

/-- A boundary extension of a conformal map `f : U → V` maps `∂U` onto `∂V` (in `ℂ̄`). -/
theorem IsHomeoExtension.image_frontier {f : ℂ → ℂ} {U V : Set ℂ} {F : ExtPlane → ExtPlane}
    (hU : IsOpen U) (hV : IsOpen V) (hfUV : f '' U = V) (hF : IsHomeoExtension f U V F) :
    F '' frontier (toExt U) = frontier (toExt V) := by
  obtain ⟨hFf, -, hinj, himg⟩ := hF
  have hUo : IsOpen (toExt U) := OnePoint.isOpen_image_coe.2 hU
  have hVo : IsOpen (toExt V) := OnePoint.isOpen_image_coe.2 hV
  have hFU : F '' toExt U = toExt V := by
    rw [← hfUV]
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨f z, mem_image_of_mem f hz, (hFf z hz).symm⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨_, ⟨z, hz, rfl⟩, hFf z hz⟩
  rw [hUo.frontier_eq, hVo.frontier_eq, hinj.image_diff_subset subset_closure, himg, hFU]

/-- A boundary extension of a conformal map `f` of `Q` onto `V` maps the sides of `Q` onto the
corresponding arcs of `∂V`. -/
theorem TopQuad.image_side {Q : TopQuad} {V : Set ℂ} (hV : IsOpen V) {f : ℂ → ℂ}
    {F : ExtPlane → ExtPlane} (hf : IsConformalOnto f Q.dom V) (hF : IsHomeoExtension f Q.dom V F)
    (i : Fin 4) :
    F '' Q.side i = boundaryArc (frontier (toExt V)) (F (Q.vert i)) (F (Q.vert (i + 1)))
      (F (Q.vert (i + 2))) := by
  have hQ := Q.isTopQuad
  have hfr : frontier (toExt Q.dom) ⊆ closure (toExt Q.dom) := frontier_subset_closure
  rw [Q.side_eq_boundaryArc, image_boundaryArc_of_injOn isClosed_closure hF.2.1 hF.2.2.1 hfr
    (hfr (hQ.2.1 i)) (hfr (hQ.2.1 _)) (hfr (hQ.2.1 _)), hF.image_frontier hQ.1.1 hV hf.2.2]

/-! ## The rectangle -/

section Rectangle

variable {a b : ℝ}

theorem rectangle_eq_reProdIm (a b : ℝ) : rectangle a b = Ioo 0 a ×ℂ Ioo 0 b := by
  ext z
  simp only [rectangle, mem_setOf_eq, mem_reProdIm, mem_Ioo, and_assoc]

theorem isOpen_rectangle (a b : ℝ) : IsOpen (rectangle a b) := by
  rw [rectangle_eq_reProdIm]
  exact isOpen_Ioo.reProdIm isOpen_Ioo

theorem isBounded_rectangle (a b : ℝ) : Bornology.IsBounded (rectangle a b) := by
  rw [rectangle_eq_reProdIm]
  exact (Metric.isBounded_Ioo 0 a).reProdIm (Metric.isBounded_Ioo 0 b)

theorem frontier_rectangle (ha : 0 < a) (hb : 0 < b) :
    frontier (rectangle a b) = Icc 0 a ×ℂ {0, b} ∪ {0, a} ×ℂ Icc 0 b := by
  rw [rectangle_eq_reProdIm, frontier_reProdIm, closure_Ioo ha.ne, closure_Ioo hb.ne,
    frontier_Ioo ha, frontier_Ioo hb]

/-- The closure in `ℂ̄` of a bounded set of `ℂ` does not contain `∞`. -/
theorem closure_toExt_of_isBounded {A : Set ℂ} (hA : Bornology.IsBounded A) :
    closure (toExt A) = toExt (closure A) := by
  unfold toExt
  refine subset_antisymm (closure_minimal (image_mono subset_closure) ?_)
    (image_closure_subset_closure_image OnePoint.continuous_coe)
  exact OnePoint.isClosed_image_coe.2 ⟨isClosed_closure, hA.isCompact_closure⟩

theorem frontier_toExt_of_isBounded {A : Set ℂ} (hA : Bornology.IsBounded A) (hAo : IsOpen A) :
    frontier (toExt A) = toExt (frontier A) := by
  have hAo' : IsOpen (toExt A) := OnePoint.isOpen_image_coe.2 hAo
  rw [hAo'.frontier_eq, closure_toExt_of_isBounded hA, hAo.frontier_eq]
  exact (image_diff OnePoint.coe_injective _ _).symm

theorem isPreconnected_reProdIm {s t : Set ℝ} (hs : IsPreconnected s) (ht : IsPreconnected t) :
    IsPreconnected (s ×ℂ t) := by
  have h : s ×ℂ t = equivRealProdCLM.symm '' (s ×ˢ t) := by
    rw [ContinuousLinearEquiv.image_symm_eq_preimage]
    ext z
    simp [mem_reProdIm]
  rw [h]
  exact (hs.prod ht).image _ equivRealProdCLM.symm.continuous.continuousOn

/-- The side `(0, a)` of `∂R(0, a, a+bi, bi)` (relative to the vertex `a + bi`) is the bottom edge.
The open bottom edge is relatively clopen in `∂R ∖ {0, a}`, whose remaining part is connected. -/
theorem boundaryArc_rectangle_bottom (ha : 0 < a) (hb : 0 < b) :
    boundaryArc (frontier (rectangle a b)) 0 (a : ℂ) ((a : ℂ) + (b : ℂ) * I) =
      Icc 0 a ×ℂ {0} := by
  have hc_re : ((a : ℂ) + (b : ℂ) * I).re = a := by simp
  have hc_im : ((a : ℂ) + (b : ℂ) * I).im = b := by simp
  have hbI_re : ((b : ℂ) * I).re = 0 := by simp
  have hbI_im : ((b : ℂ) * I).im = b := by simp
  have hK : ∀ z : ℂ, z ∈ frontier (rectangle a b) ↔
      (0 ≤ z.re ∧ z.re ≤ a) ∧ (z.im = 0 ∨ z.im = b) ∨
        (z.re = 0 ∨ z.re = a) ∧ (0 ≤ z.im ∧ z.im ≤ b) := by
    intro z
    rw [frontier_rectangle ha hb]
    simp only [mem_union, mem_reProdIm, mem_Icc, mem_insert_iff, mem_singleton_iff]
  have h0 : ∀ z : ℂ, z = 0 ↔ z.re = 0 ∧ z.im = 0 := fun z => by simp [Complex.ext_iff]
  have ha' : ∀ z : ℂ, z = (a : ℂ) ↔ z.re = a ∧ z.im = 0 := fun z => by simp [Complex.ext_iff]
  have hS : ∀ z : ℂ, z ∈ frontier (rectangle a b) \ {0, (a : ℂ)} ↔
      z ∈ frontier (rectangle a b) ∧ ¬ (z.re = 0 ∧ z.im = 0) ∧ ¬ (z.re = a ∧ z.im = 0) := by
    intro z
    simp only [mem_diff, mem_insert_iff, mem_singleton_iff, h0, ha', not_or]
  -- the open bottom edge is relatively clopen
  have hsub : ∀ s ⊆ frontier (rectangle a b) \ {0, (a : ℂ)}, IsPreconnected s →
      ∀ p ∈ s, p.im = 0 → s ⊆ Ioo 0 a ×ℂ {0} := by
    intro s hs hpre p hps hp0
    have hu : IsOpen {z : ℂ | 0 < z.re ∧ z.re < a ∧ z.im < b} :=
      (isOpen_lt continuous_const continuous_re).inter
        ((isOpen_lt continuous_re continuous_const).inter (isOpen_lt continuous_im continuous_const))
    have hv : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne_fun continuous_im continuous_const
    have hcov : s ⊆ {z : ℂ | 0 < z.re ∧ z.re < a ∧ z.im < b} ∪ {z : ℂ | z.im ≠ 0} := by
      intro z hz
      obtain ⟨hzK, hz0, hza⟩ := (hS z).1 (hs hz)
      rw [hK] at hzK
      by_cases hzi : z.im = 0
      · refine Or.inl ?_
        rcases hzK with ⟨⟨h1, h2⟩, -⟩ | ⟨h4 | h4, -⟩
        · exact ⟨lt_of_le_of_ne h1 fun h => hz0 ⟨h.symm, hzi⟩,
            lt_of_le_of_ne h2 fun h => hza ⟨h, hzi⟩, by rw [hzi]; exact hb⟩
        · exact absurd ⟨h4, hzi⟩ hz0
        · exact absurd ⟨h4, hzi⟩ hza
      · exact Or.inr hzi
    have hdisj : s ∩ ({z : ℂ | 0 < z.re ∧ z.re < a ∧ z.im < b} ∩ {z : ℂ | z.im ≠ 0}) = ∅ := by
      refine eq_empty_iff_forall_notMem.2 fun z ⟨hz, ⟨h1, h2, h3⟩, h4⟩ => ?_
      obtain ⟨hzK, -, -⟩ := (hS z).1 (hs hz)
      rw [hK] at hzK
      rcases hzK with ⟨-, h5 | h5⟩ | ⟨h5 | h5, -⟩
      · exact h4 h5
      · linarith
      · linarith
      · linarith
    rcases isPreconnected_iff_subset_of_disjoint.1 hpre _ _ hu hv hcov hdisj with h | h
    · intro z hz
      obtain ⟨hzK, -, -⟩ := (hS z).1 (hs hz)
      obtain ⟨h1, h2, h3⟩ := h hz
      rw [hK] at hzK
      refine mem_reProdIm.2 ⟨⟨h1, h2⟩, ?_⟩
      rcases hzK with ⟨-, h4 | h4⟩ | ⟨h4 | h4, -⟩
      · exact h4
      · linarith
      · linarith
      · linarith
    · exact absurd hp0 (h hps)
  -- the rest of `∂R ∖ {0, a}` is connected
  have hT : IsPreconnected ({0} ×ℂ Ioc 0 b ∪ Icc 0 a ×ℂ {b} ∪ {a} ×ℂ Ioc 0 b) := by
    refine IsPreconnected.union ((a : ℂ) + (b : ℂ) * I)
      (mem_union_right _ (mem_reProdIm.2 ⟨by rw [hc_re]; exact ⟨ha.le, le_rfl⟩,
        by rw [hc_im]; exact mem_singleton _⟩))
      (mem_reProdIm.2 ⟨by rw [hc_re]; exact mem_singleton _, by rw [hc_im]; exact ⟨hb, le_rfl⟩⟩)
      ?_ (isPreconnected_reProdIm isPreconnected_singleton isPreconnected_Ioc)
    exact IsPreconnected.union ((b : ℂ) * I)
      (mem_reProdIm.2 ⟨by rw [hbI_re]; exact mem_singleton _, by rw [hbI_im]; exact ⟨hb, le_rfl⟩⟩)
      (mem_reProdIm.2 ⟨by rw [hbI_re]; exact ⟨le_rfl, ha.le⟩, by rw [hbI_im]; exact mem_singleton _⟩)
      (isPreconnected_reProdIm isPreconnected_singleton isPreconnected_Ioc)
      (isPreconnected_reProdIm isPreconnected_Icc isPreconnected_singleton)
  have hTS : {0} ×ℂ Ioc 0 b ∪ Icc 0 a ×ℂ {b} ∪ {a} ×ℂ Ioc 0 b ⊆
      frontier (rectangle a b) \ {0, (a : ℂ)} := by
    intro z hz
    simp only [mem_union, mem_reProdIm, mem_singleton_iff, mem_Ioc, mem_Icc] at hz
    rw [hS, hK]
    rcases hz with (⟨h1, h2, h3⟩ | ⟨⟨h1, h2⟩, h3⟩) | ⟨h1, h2, h3⟩
    · exact ⟨Or.inr ⟨Or.inl h1, h2.le, h3⟩, fun h => by linarith [h.2],
        fun h => by linarith [h.2]⟩
    · exact ⟨Or.inl ⟨⟨h1, h2⟩, Or.inr h3⟩, fun h => by linarith [h.2],
        fun h => by linarith [h.2]⟩
    · exact ⟨Or.inr ⟨Or.inr h1, h2.le, h3⟩, fun h => by linarith [h.2],
        fun h => by linarith [h.2]⟩
  have hcT : (a : ℂ) + (b : ℂ) * I ∈ {0} ×ℂ Ioc 0 b ∪ Icc 0 a ×ℂ {b} ∪ {a} ×ℂ Ioc 0 b :=
    mem_union_right _ (mem_reProdIm.2 ⟨by rw [hc_re]; exact mem_singleton _,
      by rw [hc_im]; exact ⟨hb, le_rfl⟩⟩)
  have hrest : ∀ p ∈ frontier (rectangle a b) \ {0, (a : ℂ)}, p.im ≠ 0 →
      p ∈ connectedComponentIn (frontier (rectangle a b) \ {0, (a : ℂ)})
        ((a : ℂ) + (b : ℂ) * I) := by
    intro p hp hpi
    refine hT.subset_connectedComponentIn hcT hTS ?_
    obtain ⟨hpK, -, -⟩ := (hS p).1 hp
    rw [hK] at hpK
    simp only [mem_union, mem_reProdIm, mem_singleton_iff, mem_Ioc, mem_Icc]
    rcases hpK with ⟨h1, h2 | h2⟩ | ⟨h1 | h1, h2, h3⟩
    · exact absurd h2 hpi
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact Or.inl (Or.inl ⟨h1, lt_of_le_of_ne h2 (Ne.symm hpi), h3⟩)
    · exact Or.inr ⟨h1, lt_of_le_of_ne h2 (Ne.symm hpi), h3⟩
  ext z
  simp only [boundaryArc, mem_setOf_eq]
  constructor
  · rintro ⟨hzK, h | h | hne⟩
    · rw [h]
      simp [mem_reProdIm, ha.le]
    · rw [h]
      simp [mem_reProdIm, ha.le]
    · by_cases hzS : z ∈ frontier (rectangle a b) \ {0, (a : ℂ)}
      · by_contra hzn
        have hzi : z.im ≠ 0 := by
          intro hzi
          apply hzn
          rw [hK] at hzK
          refine mem_reProdIm.2 ⟨?_, hzi⟩
          rcases hzK with ⟨h1, -⟩ | ⟨h1 | h1, -⟩
          · exact h1
          · exact ⟨h1.ge, h1 ▸ ha.le⟩
          · exact ⟨h1 ▸ ha.le, h1.le⟩
        exact hne (connectedComponentIn_eq (hrest z hzS hzi)).symm
      · have h01 : z = 0 ∨ z = (a : ℂ) := by
          by_contra h
          exact hzS ⟨hzK, h⟩
        rcases h01 with rfl | rfl
        · simp [mem_reProdIm, ha.le]
        · simp [mem_reProdIm, ha.le]
  · intro hz
    rw [mem_reProdIm, mem_Icc, mem_singleton_iff] at hz
    obtain ⟨⟨h1, h2⟩, h3⟩ := hz
    have hzK : z ∈ frontier (rectangle a b) := (hK z).2 (Or.inl ⟨⟨h1, h2⟩, Or.inl h3⟩)
    refine ⟨hzK, ?_⟩
    rcases eq_or_lt_of_le h1 with h1' | h1'
    · exact Or.inl ((h0 z).2 ⟨h1'.symm, h3⟩)
    rcases eq_or_lt_of_le h2 with h2' | h2'
    · exact Or.inr (Or.inl ((ha' z).2 ⟨h2', h3⟩))
    refine Or.inr (Or.inr fun heq => ?_)
    have hzS : z ∈ frontier (rectangle a b) \ {0, (a : ℂ)} :=
      (hS z).2 ⟨hzK, fun h => h1'.ne' h.1, fun h => h2'.ne h.1⟩
    have hsubB := hsub _ (connectedComponentIn_subset _ _) isPreconnected_connectedComponentIn z
      (mem_connectedComponentIn hzS) h3
    have hmem : (a : ℂ) + (b : ℂ) * I ∈
        connectedComponentIn (frontier (rectangle a b) \ {0, (a : ℂ)}) z := by
      rw [heq]
      exact mem_connectedComponentIn (hTS hcT)
    have hc := hsubB hmem
    rw [mem_reProdIm, hc_im] at hc
    exact hb.ne' hc.2

/-- The side `(a + bi, bi)` of `∂R(0, a, a+bi, bi)` (relative to the vertex `0`) is the top edge
(the image of the bottom edge under the symmetry `z ↦ a + bi - z` of `R`). -/
theorem boundaryArc_rectangle_top (ha : 0 < a) (hb : 0 < b) :
    boundaryArc (frontier (rectangle a b)) ((a : ℂ) + (b : ℂ) * I) ((b : ℂ) * I) 0 =
      Icc 0 a ×ℂ {b} := by
  have hσ : IsEmbedding (fun z : ℂ => (a : ℂ) + (b : ℂ) * I - z) :=
    (Homeomorph.subLeft ((a : ℂ) + (b : ℂ) * I)).isEmbedding
  have hinv : ∀ A : Set ℂ, (fun z : ℂ => (a : ℂ) + (b : ℂ) * I - z) '' A =
      (fun z : ℂ => (a : ℂ) + (b : ℂ) * I - z) ⁻¹' A := fun A =>
    congrFun (image_eq_preimage_of_inverse (f := fun z : ℂ => (a : ℂ) + (b : ℂ) * I - z)
      (g := fun z : ℂ => (a : ℂ) + (b : ℂ) * I - z) (fun z => sub_sub_cancel _ z)
      (fun z => sub_sub_cancel _ z)) A
  have hre : ∀ z : ℂ, ((a : ℂ) + (b : ℂ) * I - z).re = a - z.re := fun z => by simp
  have him : ∀ z : ℂ, ((a : ℂ) + (b : ℂ) * I - z).im = b - z.im := fun z => by simp
  have hK : (fun z : ℂ => (a : ℂ) + (b : ℂ) * I - z) '' frontier (rectangle a b) =
      frontier (rectangle a b) := by
    rw [hinv, frontier_rectangle ha hb]
    ext z
    simp only [mem_preimage, mem_union, mem_reProdIm, mem_Icc, mem_insert_iff, mem_singleton_iff,
      hre, him]
    constructor
    · rintro (⟨⟨h1, h2⟩, h3 | h3⟩ | ⟨h1 | h1, h2, h3⟩)
      · exact Or.inl ⟨⟨by linarith, by linarith⟩, Or.inr (by linarith)⟩
      · exact Or.inl ⟨⟨by linarith, by linarith⟩, Or.inl (by linarith)⟩
      · exact Or.inr ⟨Or.inr (by linarith), by linarith, by linarith⟩
      · exact Or.inr ⟨Or.inl (by linarith), by linarith, by linarith⟩
    · rintro (⟨⟨h1, h2⟩, h3 | h3⟩ | ⟨h1 | h1, h2, h3⟩)
      · exact Or.inl ⟨⟨by linarith, by linarith⟩, Or.inr (by linarith)⟩
      · exact Or.inl ⟨⟨by linarith, by linarith⟩, Or.inl (by linarith)⟩
      · exact Or.inr ⟨Or.inr (by linarith), by linarith, by linarith⟩
      · exact Or.inr ⟨Or.inl (by linarith), by linarith, by linarith⟩
  have hbot : (fun z : ℂ => (a : ℂ) + (b : ℂ) * I - z) '' (Icc 0 a ×ℂ {0}) = Icc 0 a ×ℂ {b} := by
    rw [hinv]
    ext z
    simp only [mem_preimage, mem_reProdIm, mem_Icc, mem_singleton_iff, hre, him]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  have h := image_boundaryArc_of_isEmbedding hσ (frontier (rectangle a b)) 0 (a : ℂ)
    ((a : ℂ) + (b : ℂ) * I)
  rw [boundaryArc_rectangle_bottom ha hb, hK, hbot] at h
  have e1 : (a : ℂ) + (b : ℂ) * I - (a : ℂ) = (b : ℂ) * I := by ring
  simp only [sub_zero, sub_self, e1] at h
  exact h.symm

/-- The first side of `R(0, a, a+bi, bi)`, in `ℂ̄`, is the bottom edge. -/
theorem boundaryArc_frontier_toExt_rectangle_bottom (ha : 0 < a) (hb : 0 < b) :
    boundaryArc (frontier (toExt (rectangle a b))) (rectVert a b 0) (rectVert a b 1)
      (rectVert a b 2) = toExt (Icc 0 a ×ℂ {0}) := by
  rw [frontier_toExt_of_isBounded (isBounded_rectangle a b) (isOpen_rectangle a b)]
  have h := image_boundaryArc_of_isEmbedding OnePoint.isOpenEmbedding_coe.isEmbedding
    (frontier (rectangle a b)) 0 (a : ℂ) ((a : ℂ) + (b : ℂ) * I)
  rw [boundaryArc_rectangle_bottom ha hb] at h
  unfold toExt
  rw [h]
  rfl

/-- The third side of `R(0, a, a+bi, bi)`, in `ℂ̄`, is the top edge. -/
theorem boundaryArc_frontier_toExt_rectangle_top (ha : 0 < a) (hb : 0 < b) :
    boundaryArc (frontier (toExt (rectangle a b))) (rectVert a b 2) (rectVert a b 3)
      (rectVert a b 0) = toExt (Icc 0 a ×ℂ {b}) := by
  rw [frontier_toExt_of_isBounded (isBounded_rectangle a b) (isOpen_rectangle a b)]
  have h := image_boundaryArc_of_isEmbedding OnePoint.isOpenEmbedding_coe.isEmbedding
    (frontier (rectangle a b)) ((a : ℂ) + (b : ℂ) * I) ((b : ℂ) * I) 0
  rw [boundaryArc_rectangle_top ha hb] at h
  unfold toExt
  rw [h]
  rfl

end Rectangle

/-! ## Curves joining the sides -/

/-- The inverse of a map continuous and injective on a closed subset of `ℂ̄` is continuous. -/
theorem continuousOn_invFunOn_of_isClosed {F : ExtPlane → ExtPlane} {C : Set ExtPlane}
    (hC : IsClosed C) (hF : ContinuousOn F C) (hinj : InjOn F C) :
    ContinuousOn (Function.invFunOn F C) (F '' C) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  refine ⟨F '' (t ∩ C), ((ht.inter hC).isCompact.image_of_continuousOn
    (hF.mono inter_subset_right)).isClosed, ?_⟩
  ext y
  constructor
  · rintro ⟨hyt, x, hx, rfl⟩
    rw [mem_preimage, hinj.leftInvOn_invFunOn hx] at hyt
    exact ⟨⟨x, ⟨hyt, hx⟩, rfl⟩, x, hx, rfl⟩
  · rintro ⟨⟨x, ⟨hxt, hxC⟩, rfl⟩, -⟩
    refine ⟨?_, x, hxC, rfl⟩
    rw [mem_preimage, hinj.leftInvOn_invFunOn hxC]
    exact hxt

/-- A locally Lipschitz curve in `U` followed by a holomorphic map on `U` is locally Lipschitz. -/
theorem locallyLipschitzOn_comp_of_differentiableOn {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) {γ : ℝ → ℂ} {s : Set ℝ} (hs : IsOpen s)
    (hγ : LocallyLipschitzOn s γ) (hmaps : MapsTo γ s U) : LocallyLipschitzOn s (g ∘ γ) := by
  intro t ht
  obtain ⟨K₁, V₁, hV₁, hK₁⟩ := hγ ht
  have hcd : ContDiffAt ℂ 1 g (γ t) :=
    (hg.contDiffOn (n := 1) hU).contDiffAt (hU.mem_nhds (hmaps ht))
  obtain ⟨K₂, V₂, hV₂, hK₂⟩ := hcd.exists_lipschitzOnWith
  have hcont : ContinuousAt γ t := hγ.continuousOn.continuousAt (hs.mem_nhds ht)
  refine ⟨K₂ * K₁, V₁ ∩ γ ⁻¹' V₂,
    inter_mem hV₁ (mem_nhdsWithin_of_mem_nhds (hcont.preimage_mem_nhds hV₂)), ?_⟩
  exact hK₂.comp (hK₁.mono inter_subset_left) fun x hx => hx.2

/-- Limits at boundary points are carried along by a boundary extension. -/
theorem IsHomeoExtension.tendsto_comp {f : ℂ → ℂ} {U V : Set ℂ} {F : ExtPlane → ExtPlane}
    (hF : IsHomeoExtension f U V F) {ι : Type*} {l : Filter ι} {γ : ι → ℂ} {p : ExtPlane}
    (hp : p ∈ closure (toExt U)) (hγU : ∀ᶠ t in l, γ t ∈ U)
    (hγ : Tendsto (fun t => (γ t : ExtPlane)) l (𝓝 p)) :
    Tendsto (fun t => (f (γ t) : ExtPlane)) l (𝓝 (F p)) := by
  have h1 : Tendsto (fun t => (γ t : ExtPlane)) l (𝓝[closure (toExt U)] p) :=
    tendsto_nhdsWithin_iff.2
      ⟨hγ, hγU.mono fun t ht => subset_closure (mem_image_of_mem ((↑) : ℂ → ExtPlane) ht)⟩
  refine ((hF.2.1 p hp).tendsto.comp h1).congr' ?_
  filter_upwards [hγU] with t ht
  exact hF.1 _ ht

/-- The curves in `R(0, a, a+bi, bi)` joining the bottom edge to the top edge. -/
def rectJoiningCurves (a b : ℝ) : Set LRCurve :=
  {γ | γ.trace ⊆ rectangle a b ∧
    (∃ p ∈ Icc 0 a ×ℂ {0}, Tendsto γ.toFun (𝓝[>] 0) (𝓝 p)) ∧
    ∃ q ∈ Icc 0 a ×ℂ {b}, Tendsto γ.toFun (𝓝[<] 1) (𝓝 q)}

/-! ## The extremal length of the rectangle family -/

section RectangleExtremalLength

/-- The area of `R(0, a, a+bi, bi)`. -/
theorem volume_rectangle (a b : ℝ) :
    volume (rectangle a b) = ENNReal.ofReal a * ENNReal.ofReal b := by
  have hpre : Complex.measurableEquivRealProd ⁻¹' (Ioo 0 a ×ˢ Ioo 0 b) = rectangle a b := by
    ext z
    simp [rectangle, and_assoc]
  rw [← hpre, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo, sub_zero, sub_zero]

/-- Fubini's theorem on the rectangle. -/
theorem setLIntegral_rectangle {a b : ℝ} {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    ∫⁻ z in rectangle a b, ρ z =
      ∫⁻ x in Ioo 0 a, ∫⁻ y in Ioo 0 b, ρ ((x : ℂ) + (y : ℂ) * I) := by
  have himg : Complex.measurableEquivRealProd.symm '' (Ioo 0 a ×ˢ Ioo 0 b) = rectangle a b := by
    rw [MeasurableEquiv.image_symm]
    ext z
    simp [rectangle, and_assoc]
  rw [← himg, ← (Complex.volume_preserving_equiv_real_prod.symm).setLIntegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding, Measure.volume_eq_prod,
    setLIntegral_prod (fun p => ρ (Complex.measurableEquivRealProd.symm p))
      (hρ.comp Complex.measurableEquivRealProd.symm.measurable).aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioo fun x _ =>
    setLIntegral_congr_fun measurableSet_Ioo fun y _ => ?_
  congr 1
  apply Complex.ext <;> simp

/-- Cauchy–Schwarz: `(∬_s ρ)² ≤ m(s) ∬_s ρ²`. -/
theorem setLIntegral_sq_le {s : Set ℂ} {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    (∫⁻ z in s, ρ z) ^ 2 ≤ volume s * ∫⁻ z in s, ρ z ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict s) Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ≥0∞)) (g := ρ) aemeasurable_const hρ.aemeasurable
  simp only [Pi.mul_apply, lintegral_const, Measure.restrict_apply_univ, ENNReal.rpow_two,
    one_pow, one_mul] at h
  calc (∫⁻ z in s, ρ z) ^ 2
      ≤ (volume s ^ (1 / 2 : ℝ) * (∫⁻ z in s, ρ z ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' h 2
    _ = volume s * ∫⁻ z in s, ρ z ^ 2 := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

/-- Cauchy–Schwarz: `(∬_s f g)² ≤ ∬_s f² ∬_s g²`. -/
theorem setLIntegral_mul_sq_le {s : Set ℂ} {f g : ℂ → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) :
    (∫⁻ z in s, f z * g z) ^ 2 ≤ (∫⁻ z in s, f z ^ 2) * ∫⁻ z in s, g z ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict s) Real.HolderConjugate.two_two
    hf.aemeasurable hg.aemeasurable
  simp only [Pi.mul_apply, ENNReal.rpow_two] at h
  calc (∫⁻ z in s, f z * g z) ^ 2
      ≤ ((∫⁻ z in s, f z ^ 2) ^ (1 / 2 : ℝ) * (∫⁻ z in s, g z ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left' h 2
    _ = (∫⁻ z in s, f z ^ 2) * ∫⁻ z in s, g z ^ 2 := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

/-- The imaginary part of a differentiable curve is differentiable. -/
theorem hasDerivAt_im_of_hasDerivAt {γ : ℝ → ℂ} {γ' : ℂ} {u : ℝ} (h : HasDerivAt γ γ' u) :
    HasDerivAt (fun v => (γ v).im) γ'.im u := by
  rw [hasDerivAt_iff_isLittleO] at h ⊢
  refine Asymptotics.IsBigO.trans_isLittleO
    (Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun v => ?_)) h
  have e : (γ v).im - (γ u).im - (v - u) • γ'.im = (γ v - γ u - (v - u) • γ').im := by simp
  simp only [one_mul]
  rw [e, Real.norm_eq_abs]
  exact abs_im_le_norm _


/-- For a locally rectifiable curve `γ` and a real-linear functional `L` of norm at most `1`,
the variation of `L ∘ γ` between two interior parameters is at most the length of `γ`
(the fundamental theorem of calculus for the absolutely continuous function `L ∘ γ`). -/
theorem LRCurve.enorm_clm_sub_le_length (γ : LRCurve) {L : ℂ →L[ℝ] ℝ}
    (hL : ∀ z : ℂ, |L z| ≤ ‖z‖) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht1 : t < 1) :
    ‖L (γ.toFun t) - L (γ.toFun s)‖ₑ ≤ γ.length := by
  have hA := LocallyLipschitzOn.ae_differentiableAt_Ioo γ.locallyLipschitzOn
  have hlen : γ.length = ∫⁻ u in Ioo 0 1, ‖deriv γ.toFun u‖ₑ := by
    simp [LRCurve.length, LRCurve.rhoLength]
  have hsub : Icc s t ⊆ Ioo 0 1 := Icc_subset_Ioo hs ht1
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
    (LocallyLipschitzOn.mono γ.locallyLipschitzOn hsub)
  have hKL : LipschitzOnWith (‖L‖₊ * K) (fun u => L (γ.toFun u)) (uIcc s t) := by
    rw [uIcc_of_le hst]
    exact L.lipschitz.comp_lipschitzOnWith hK
  have hftc : ∫ u in s..t, deriv (fun u => L (γ.toFun u)) u = L (γ.toFun t) - L (γ.toFun s) :=
    hKL.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  rw [← hftc, intervalIntegral.integral_of_le hst, hlen]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  calc ∫⁻ u in Ioc s t, ‖deriv (fun u => L (γ.toFun u)) u‖ₑ
      ≤ ∫⁻ u in Ioc s t, ‖deriv γ.toFun u‖ₑ := by
        refine setLIntegral_mono_ae' measurableSet_Ioc ?_
        filter_upwards [hA] with u hu huI
        have hu01 : u ∈ Ioo (0 : ℝ) 1 := ⟨hs.trans huI.1, huI.2.trans_lt ht1⟩
        have hd : HasDerivAt (fun u => L (γ.toFun u)) (L (deriv γ.toFun u)) u :=
          L.hasFDerivAt.comp_hasDerivAt u (hu hu01).hasDerivAt
        rw [hd.deriv, ← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (hL _)
    _ ≤ ∫⁻ u in Ioo 0 1, ‖deriv γ.toFun u‖ₑ :=
        lintegral_mono_set fun u hu => ⟨hs.trans hu.1, hu.2.trans_lt ht1⟩

/-- If a locally rectifiable curve has the limit `p` as `t → 0⁺` and the limit `q` as `t → 1⁻`,
then `|L q - L p| ≤ length γ` for every real-linear functional `L` of norm at most `1`. -/
theorem LRCurve.enorm_clm_sub_le_length_of_tendsto {γ : LRCurve} {L : ℂ →L[ℝ] ℝ}
    (hL : ∀ z : ℂ, |L z| ≤ ‖z‖) {p q : ℂ} (hp : Tendsto γ.toFun (𝓝[>] 0) (𝓝 p))
    (hq : Tendsto γ.toFun (𝓝[<] 1) (𝓝 q)) : ‖L q - L p‖ₑ ≤ γ.length := by
  have hlim0 : Tendsto (fun s => L (γ.toFun s)) (𝓝[>] 0) (𝓝 (L p)) :=
    (L.continuous.tendsto p).comp hp
  have hlim1 : Tendsto (fun t => L (γ.toFun t)) (𝓝[<] 1) (𝓝 (L q)) :=
    (L.continuous.tendsto q).comp hq
  have step : ∀ s : ℝ, 0 < s → s < 1 → ‖L q - L (γ.toFun s)‖ₑ ≤ γ.length := by
    intro s hs hs1
    have ht : Tendsto (fun t => ‖L (γ.toFun t) - L (γ.toFun s)‖ₑ) (𝓝[<] 1)
        (𝓝 ‖L q - L (γ.toFun s)‖ₑ) :=
      (continuous_enorm.tendsto _).comp (hlim1.sub_const _)
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hs1] with t ht'
    exact γ.enorm_clm_sub_le_length hL hs ht'.1.le ht'.2
  have hs : Tendsto (fun s => ‖L q - L (γ.toFun s)‖ₑ) (𝓝[>] 0) (𝓝 ‖L q - L p‖ₑ) :=
    (continuous_enorm.tendsto _).comp (tendsto_const_nhds.sub hlim0)
  refine le_of_tendsto hs ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with s hs'
  exact step s hs'.1 hs'.2

/-- A locally rectifiable curve with limits `p` at `0` and `q` at `1` has length at least
`Im q - Im p`. -/
theorem LRCurve.ofReal_im_sub_le_length {γ : LRCurve} {p q : ℂ}
    (hp : Tendsto γ.toFun (𝓝[>] 0) (𝓝 p)) (hq : Tendsto γ.toFun (𝓝[<] 1) (𝓝 q)) :
    ENNReal.ofReal (q.im - p.im) ≤ γ.length := by
  have h := LRCurve.enorm_clm_sub_le_length_of_tendsto (L := Complex.imCLM)
    (fun z => abs_im_le_norm z) hp hq
  simp only [Complex.imCLM_apply] at h
  refine le_trans (le_trans (ENNReal.ofReal_le_ofReal ?_) (le_of_eq (ofReal_norm _))) h
  rw [Real.norm_eq_abs]
  exact le_abs_self _

/-- A locally rectifiable curve with limits `p` at `0` and `q` at `1` has length at least
`Re q - Re p`. -/
theorem LRCurve.ofReal_re_sub_le_length {γ : LRCurve} {p q : ℂ}
    (hp : Tendsto γ.toFun (𝓝[>] 0) (𝓝 p)) (hq : Tendsto γ.toFun (𝓝[<] 1) (𝓝 q)) :
    ENNReal.ofReal (q.re - p.re) ≤ γ.length := by
  have h := LRCurve.enorm_clm_sub_le_length_of_tendsto (L := Complex.reCLM)
    (fun z => abs_re_le_norm z) hp hq
  simp only [Complex.reCLM_apply] at h
  refine le_trans (le_trans (ENNReal.ofReal_le_ofReal ?_) (le_of_eq (ofReal_norm _))) h
  rw [Real.norm_eq_abs]
  exact le_abs_self _
/-- A curve joining the bottom and top edges of `R(0, a, a+bi, bi)` has length at least `b`
(fundamental theorem of calculus for the absolutely continuous function `Im γ`). -/
theorem LRCurve.ofReal_le_rhoLength_one {a b : ℝ} (hb : 0 < b) {γ : LRCurve}
    (hγ : γ ∈ rectJoiningCurves a b) : ENNReal.ofReal b ≤ γ.rhoLength 1 := by
  obtain ⟨-, ⟨p, hp, hpγ⟩, ⟨q, hq, hqγ⟩⟩ := hγ
  have hpi : p.im = 0 := hp.2
  have hqi : q.im = b := hq.2
  have hA := LocallyLipschitzOn.ae_differentiableAt_Ioo γ.locallyLipschitzOn
  have hlen : γ.rhoLength 1 = ∫⁻ u in Ioo 0 1, ‖deriv γ.toFun u‖ₑ := by
    simp [LRCurve.rhoLength]
  have key : ∀ s t : ℝ, 0 < s → s ≤ t → t < 1 →
      ‖(γ.toFun t).im - (γ.toFun s).im‖ₑ ≤ γ.rhoLength 1 := by
    intro s t hs hst ht1
    have hsub : Icc s t ⊆ Ioo 0 1 := Icc_subset_Ioo hs ht1
    obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
      (LocallyLipschitzOn.mono γ.locallyLipschitzOn hsub)
    have hKim : LipschitzOnWith (‖Complex.imCLM‖₊ * K) (fun u => (γ.toFun u).im) (uIcc s t) := by
      rw [uIcc_of_le hst]
      exact Complex.imCLM.lipschitz.comp_lipschitzOnWith hK
    have hftc : ∫ u in s..t, deriv (fun u => (γ.toFun u).im) u =
        (γ.toFun t).im - (γ.toFun s).im :=
      hKim.absolutelyContinuousOnInterval.integral_deriv_eq_sub
    rw [← hftc, intervalIntegral.integral_of_le hst, hlen]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ u in Ioc s t, ‖deriv (fun u => (γ.toFun u).im) u‖ₑ
        ≤ ∫⁻ u in Ioc s t, ‖deriv γ.toFun u‖ₑ := by
          refine setLIntegral_mono_ae' measurableSet_Ioc ?_
          filter_upwards [hA] with u hu huI
          have hu01 : u ∈ Ioo (0 : ℝ) 1 := ⟨hs.trans huI.1, huI.2.trans_lt ht1⟩
          have hd : HasDerivAt (fun u => (γ.toFun u).im) (deriv γ.toFun u).im u :=
            hasDerivAt_im_of_hasDerivAt (hu hu01).hasDerivAt
          rw [hd.deriv, ← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (abs_im_le_norm _)
      _ ≤ ∫⁻ u in Ioo 0 1, ‖deriv γ.toFun u‖ₑ :=
          lintegral_mono_set fun u hu => ⟨hs.trans hu.1, hu.2.trans_lt ht1⟩
  have hlim0 : Tendsto (fun s => (γ.toFun s).im) (𝓝[>] 0) (𝓝 0) := by
    have h := (continuous_im.tendsto p).comp hpγ
    rwa [hpi] at h
  have hlim1 : Tendsto (fun t => (γ.toFun t).im) (𝓝[<] 1) (𝓝 b) := by
    have h := (continuous_im.tendsto q).comp hqγ
    rwa [hqi] at h
  have step : ∀ s : ℝ, 0 < s → s < 1 → ‖b - (γ.toFun s).im‖ₑ ≤ γ.rhoLength 1 := by
    intro s hs hs1
    have ht : Tendsto (fun t => ‖(γ.toFun t).im - (γ.toFun s).im‖ₑ) (𝓝[<] 1)
        (𝓝 ‖b - (γ.toFun s).im‖ₑ) :=
      (continuous_enorm.tendsto _).comp (hlim1.sub_const _)
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hs1] with t ht'
    exact key s t hs ht'.1.le ht'.2
  have hs : Tendsto (fun s => ‖b - (γ.toFun s).im‖ₑ) (𝓝[>] 0) (𝓝 ‖b - 0‖ₑ) :=
    (continuous_enorm.tendsto _).comp (tendsto_const_nhds.sub hlim0)
  rw [sub_zero, Real.enorm_eq_ofReal hb.le] at hs
  refine le_of_tendsto hs ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with s hs'
  exact step s hs'.1 hs'.2

/-- `ofReal (∫ f) ≤ ∫⁻ ofReal f` for real functions. -/
theorem ofReal_integral_le_lintegral_ofReal_real {μ : Measure ℝ} {f : ℝ → ℝ} :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hf : Integrable f μ
  · calc ENNReal.ofReal (∫ x, f x ∂μ) ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂μ) :=
          ENNReal.ofReal_le_ofReal (integral_mono hf hf.pos_part fun x => le_max_left _ _)
      _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂μ :=
          ofReal_integral_eq_lintegral_ofReal hf.pos_part
            (Eventually.of_forall fun x => le_max_right _ _)
      _ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
          congr 1
          funext x
          rcases le_total (f x) 0 with h | h
          · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
          · rw [max_eq_left h]
  · rw [integral_undef hf, ENNReal.ofReal_zero]
    exact zero_le

/-- A curve joining the bottom and top edges of `R(0, a, a+bi, bi)` satisfies `b ≤ ∫ Im γ'`
(the fundamental theorem of calculus for `Im γ`). -/
theorem LRCurve.ofReal_le_lintegral_im_deriv {a b : ℝ} (_hb : 0 < b) {γ : LRCurve}
    (hγ : γ ∈ rectJoiningCurves a b) :
    ENNReal.ofReal b ≤ ∫⁻ u in Ioo 0 1, ENNReal.ofReal (deriv γ.toFun u).im := by
  obtain ⟨-, ⟨p, hp, hpγ⟩, ⟨q, hq, hqγ⟩⟩ := hγ
  have hpi : p.im = 0 := hp.2
  have hqi : q.im = b := hq.2
  have hA := LocallyLipschitzOn.ae_differentiableAt_Ioo γ.locallyLipschitzOn
  have key : ∀ s t : ℝ, 0 < s → s ≤ t → t < 1 →
      ENNReal.ofReal ((γ.toFun t).im - (γ.toFun s).im) ≤
        ∫⁻ u in Ioo 0 1, ENNReal.ofReal (deriv γ.toFun u).im := by
    intro s t hs hst ht1
    have hsub : Icc s t ⊆ Ioo 0 1 := Icc_subset_Ioo hs ht1
    obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc
      (LocallyLipschitzOn.mono γ.locallyLipschitzOn hsub)
    have hKim : LipschitzOnWith (‖Complex.imCLM‖₊ * K) (fun u => (γ.toFun u).im) (uIcc s t) := by
      rw [uIcc_of_le hst]
      exact Complex.imCLM.lipschitz.comp_lipschitzOnWith hK
    have hftc : ∫ u in s..t, deriv (fun u => (γ.toFun u).im) u =
        (γ.toFun t).im - (γ.toFun s).im :=
      hKim.absolutelyContinuousOnInterval.integral_deriv_eq_sub
    rw [← hftc, intervalIntegral.integral_of_le hst]
    refine ofReal_integral_le_lintegral_ofReal_real.trans ?_
    calc ∫⁻ u in Ioc s t, ENNReal.ofReal (deriv (fun u => (γ.toFun u).im) u)
        ≤ ∫⁻ u in Ioc s t, ENNReal.ofReal (deriv γ.toFun u).im := by
          refine setLIntegral_mono_ae' measurableSet_Ioc ?_
          filter_upwards [hA] with u hu huI
          have hu01 : u ∈ Ioo (0 : ℝ) 1 := ⟨hs.trans huI.1, huI.2.trans_lt ht1⟩
          have hd : HasDerivAt (fun u => (γ.toFun u).im) (deriv γ.toFun u).im u :=
            hasDerivAt_im_of_hasDerivAt (hu hu01).hasDerivAt
          rw [hd.deriv]
      _ ≤ ∫⁻ u in Ioo 0 1, ENNReal.ofReal (deriv γ.toFun u).im :=
          lintegral_mono_set fun u hu => ⟨hs.trans hu.1, hu.2.trans_lt ht1⟩
  have hlim0 : Tendsto (fun s => (γ.toFun s).im) (𝓝[>] 0) (𝓝 0) := by
    have h := (continuous_im.tendsto p).comp hpγ
    rwa [hpi] at h
  have hlim1 : Tendsto (fun t => (γ.toFun t).im) (𝓝[<] 1) (𝓝 b) := by
    have h := (continuous_im.tendsto q).comp hqγ
    rwa [hqi] at h
  have step : ∀ s : ℝ, 0 < s → s < 1 → ENNReal.ofReal (b - (γ.toFun s).im) ≤
      ∫⁻ u in Ioo 0 1, ENNReal.ofReal (deriv γ.toFun u).im := by
    intro s hs hs1
    have ht : Tendsto (fun t => ENNReal.ofReal ((γ.toFun t).im - (γ.toFun s).im)) (𝓝[<] 1)
        (𝓝 (ENNReal.ofReal (b - (γ.toFun s).im))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hlim1.sub_const _)
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hs1] with t ht'
    exact key s t hs ht'.1.le ht'.2
  have hs : Tendsto (fun s => ENNReal.ofReal (b - (γ.toFun s).im)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (b - 0))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub hlim0)
  rw [sub_zero] at hs
  refine le_of_tendsto hs ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with s hs'
  exact step s hs'.1 hs'.2

/-- The vertical segment `t ↦ x + t b i` (`0 < t < 1`). -/
def vertSeg (b x : ℝ) : LRCurve where
  toFun t := (x : ℂ) + (t : ℂ) * ((b : ℂ) * I)
  locallyLipschitzOn := fun _ _ => ⟨‖(b : ℂ) * I‖₊, univ, univ_mem,
    (LipschitzWith.of_dist_le_mul fun t s => le_of_eq (by
      rw [dist_eq_norm, dist_eq_norm, coe_nnnorm,
        show (x : ℂ) + (t : ℂ) * ((b : ℂ) * I) - ((x : ℂ) + (s : ℂ) * ((b : ℂ) * I)) =
          ((t - s : ℝ) : ℂ) * ((b : ℂ) * I) by push_cast; ring,
        norm_mul, norm_real, mul_comm])).lipschitzOnWith⟩

theorem vertSeg_mem {a b x : ℝ} (hb : 0 < b) (hx : x ∈ Ioo 0 a) :
    vertSeg b x ∈ rectJoiningCurves a b := by
  have hcont : Continuous (vertSeg b x).toFun := by
    show Continuous fun t : ℝ => (x : ℂ) + (t : ℂ) * ((b : ℂ) * I)
    fun_prop
  refine ⟨?_, ⟨(x : ℂ), ?_, ?_⟩, ⟨(x : ℂ) + (b : ℂ) * I, ?_, ?_⟩⟩
  · rintro _ ⟨t, ht, rfl⟩
    have hre : ((vertSeg b x).toFun t).re = x := by simp [vertSeg]
    have him : ((vertSeg b x).toFun t).im = t * b := by simp [vertSeg]
    show 0 < ((vertSeg b x).toFun t).re ∧ ((vertSeg b x).toFun t).re < a ∧
      0 < ((vertSeg b x).toFun t).im ∧ ((vertSeg b x).toFun t).im < b
    rw [hre, him]
    exact ⟨hx.1, hx.2, mul_pos ht.1 hb, mul_lt_of_lt_one_left hb ht.2⟩
  · simp [mem_reProdIm, hx.1.le, hx.2.le]
  · have h : Tendsto (vertSeg b x).toFun (𝓝[>] 0) (𝓝 ((vertSeg b x).toFun 0)) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa [vertSeg] using h
  · simp [mem_reProdIm, hx.1.le, hx.2.le]
  · have h : Tendsto (vertSeg b x).toFun (𝓝[<] 1) (𝓝 ((vertSeg b x).toFun 1)) :=
      (hcont.tendsto 1).mono_left nhdsWithin_le_nhds
    simpa [vertSeg] using h

theorem vertSeg_rhoLength {b x : ℝ} (hb : 0 < b) (ρ : ℂ → ℝ≥0∞) :
    (vertSeg b x).rhoLength ρ = ∫⁻ y in Ioo 0 b, ρ ((x : ℂ) + (y : ℂ) * I) := by
  have hderiv : ∀ t, deriv (vertSeg b x).toFun t = (b : ℂ) * I := fun t => by
    have h : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * ((b : ℂ) * I)) ((b : ℂ) * I) t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.mul_const ((b : ℂ) * I)).const_add (x : ℂ)
    exact h.deriv
  have hnorm : ‖(b : ℂ) * I‖ₑ = ENNReal.ofReal b := by
    rw [← ofReal_norm, norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg hb.le]
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) 1))
    (fun t _ => (hasDerivAt_mul_const b).hasDerivWithinAt) (mul_left_injective₀ hb.ne').injOn
    (fun y => ρ ((x : ℂ) + (y : ℂ) * I))
  rw [image_mul_right_Ioo 0 1 hb, zero_mul, one_mul] at hcv
  rw [hcv, LRCurve.rhoLength]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  rw [hderiv, hnorm, abs_of_pos hb, mul_comm]
  congr 2
  show (x : ℂ) + (t : ℂ) * ((b : ℂ) * I) = (x : ℂ) + ((t * b : ℝ) : ℂ) * I
  push_cast
  ring

/-- **§4.1**: the extremal length of the curves joining the bottom and top edges of
`R(0, a, a+bi, bi)` is `b / a`. -/
theorem extremalLength_rectJoiningCurves {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    extremalLength (rectJoiningCurves a b) = ENNReal.ofReal (b / a) := by
  apply le_antisymm
  · -- the vertical segments and the Cauchy–Schwarz inequality
    unfold extremalLength extremalLengthIn
    refine iSup₂_le fun ρ hρ => ?_
    obtain ⟨hρm, hρ0, hρtop⟩ := hρ
    rw [← iInf_rhoLength_sq, ENNReal.div_le_iff hρ0.ne' hρtop.ne]
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, (⨅ γ ∈ rectJoiningCurves a b, γ.rhoLength ρ) = ℓ := ⟨_, rfl⟩
    rw [hℓ]
    have hA0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
    have hAt : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
    have hℓle : ℓ * ENNReal.ofReal a ≤ ∫⁻ z in rectangle a b, ρ z := by
      calc ℓ * ENNReal.ofReal a = ∫⁻ _ in Ioo 0 a, ℓ := by
            rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
        _ ≤ ∫⁻ x in Ioo 0 a, ∫⁻ y in Ioo 0 b, ρ ((x : ℂ) + (y : ℂ) * I) :=
            setLIntegral_mono' measurableSet_Ioo fun x hx => by
              rw [← hℓ, ← vertSeg_rhoLength hb ρ]
              exact iInf₂_le _ (vertSeg_mem hb hx)
        _ = ∫⁻ z in rectangle a b, ρ z := (setLIntegral_rectangle hρm).symm
    have hkey : ENNReal.ofReal a * (ENNReal.ofReal a * ℓ ^ 2) ≤
        ENNReal.ofReal a * (ENNReal.ofReal b * rhoArea ρ univ) := by
      calc ENNReal.ofReal a * (ENNReal.ofReal a * ℓ ^ 2) = (ℓ * ENNReal.ofReal a) ^ 2 := by ring
        _ ≤ (∫⁻ z in rectangle a b, ρ z) ^ 2 := pow_le_pow_left' hℓle 2
        _ ≤ volume (rectangle a b) * ∫⁻ z in rectangle a b, ρ z ^ 2 := setLIntegral_sq_le hρm
        _ ≤ ENNReal.ofReal a * ENNReal.ofReal b * rhoArea ρ univ := by
            rw [volume_rectangle a b]
            gcongr
            exact lintegral_mono_set (subset_univ _)
        _ = ENNReal.ofReal a * (ENNReal.ofReal b * rhoArea ρ univ) := by ring
    have hinvA : ∀ y : ℝ≥0∞, (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a * y) = y := fun y => by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hA0 hAt, one_mul]
    calc ℓ ^ 2 = (ENNReal.ofReal a)⁻¹ * ((ENNReal.ofReal a)⁻¹ *
          (ENNReal.ofReal a * (ENNReal.ofReal a * ℓ ^ 2))) := by rw [hinvA, hinvA]
      _ ≤ (ENNReal.ofReal a)⁻¹ * ((ENNReal.ofReal a)⁻¹ *
          (ENNReal.ofReal a * (ENNReal.ofReal b * rhoArea ρ univ))) := by
          gcongr (ENNReal.ofReal a)⁻¹ * ((ENNReal.ofReal a)⁻¹ * ?_)
      _ = ENNReal.ofReal (b / a) * rhoArea ρ univ := by
          rw [hinvA, ← mul_assoc, ENNReal.ofReal_div_of_pos ha, div_eq_mul_inv,
            mul_comm (ENNReal.ofReal b)]
  · -- the density `1` on the rectangle
    have hm : Measurable ((rectangle a b).indicator (1 : ℂ → ℝ≥0∞)) :=
      measurable_one.indicator (isOpen_rectangle a b).measurableSet
    have harea : rhoArea ((rectangle a b).indicator 1) univ =
        ENNReal.ofReal a * ENNReal.ofReal b := by
      rw [rhoArea_indicator_univ _ (isOpen_rectangle a b).measurableSet]
      simp only [Pi.one_apply, one_pow, setLIntegral_const, one_mul]
      exact volume_rectangle a b
    have h := le_extremalLengthIn isOpen_univ univ_nonempty (rectJoiningCurves a b) hm
      (by rw [harea]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    refine le_trans ?_ h
    rw [harea]
    have hlen : ∀ γ ∈ rectJoiningCurves a b,
        ENNReal.ofReal b ^ 2 ≤ γ.rhoLength ((rectangle a b).indicator 1) ^ 2 := by
      intro γ hγ
      rw [LRCurve.rhoLength_congr fun z hz => indicator_of_mem (hγ.1 hz) (1 : ℂ → ℝ≥0∞)]
      exact pow_le_pow_left' (LRCurve.ofReal_le_rhoLength_one hb hγ) 2
    calc ENNReal.ofReal (b / a) = ENNReal.ofReal b ^ 2 / (ENNReal.ofReal a * ENNReal.ofReal b) := by
          rw [← ENNReal.ofReal_pow hb.le, ← ENNReal.ofReal_mul ha.le,
            ← ENNReal.ofReal_div_of_pos (mul_pos ha hb)]
          congr 1
          rw [div_eq_div_iff ha.ne' (mul_pos ha hb).ne']
          ring
      _ ≤ _ := ENNReal.div_le_div_right (le_iInf₂ hlen) _

end RectangleExtremalLength

end LiZhongQC
