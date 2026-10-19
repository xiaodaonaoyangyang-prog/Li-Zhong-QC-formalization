import LiZhongQC.Lemmas.SchottkyDoubleCarrier
import LiZhongQC.Lemmas.HurwitzQuotientChart

/-! Topological sewing on the one actual Schottky quotient.
The supplied half-plane homeomorphism is local coordinate data; neither a
double chart nor analytic compatibility is assumed. -/

open Complex Set Topology
open scoped ComplexConjugate

noncomputable section
namespace LiZhongQC

/-- Folding two closed upper half-planes onto the plane is a quotient map.
It is closed because each of its two restrictions is a closed embedding. -/
theorem s78ra_halfplane_fold_quotient :
    IsQuotientMap (fun x : Bool × {z : ℂ | 0 ≤ z.im} =>
      if x.1 then conj x.2.val else x.2.val) := by
  let H := {z : ℂ | 0 ≤ z.im}
  let f : Bool × H → ℂ := fun x => if x.1 then conj x.2.val else x.2.val
  have hc : Continuous f := by
    apply continuous_prod_of_discrete_left.2
    intro b
    cases b
    · exact continuous_subtype_val
    · exact continuous_conj.comp continuous_subtype_val
  have hs : Function.Surjective f := by
    intro z
    by_cases hz : 0 ≤ z.im
    · exact ⟨(false, ⟨z, hz⟩), rfl⟩
    · have hz' : 0 ≤ (conj z).im := by
        rw [conj_im]
        linarith
      refine ⟨(true, ⟨conj z, hz'⟩), ?_⟩
      exact conj_conj z
  have hclosed : IsClosedMap f := by
    intro A hA
    let A₀ : Set H := (fun z : H => (false, z)) ⁻¹' A
    let A₁ : Set H := (fun z : H => (true, z)) ⁻¹' A
    have h₀ : IsClosed A₀ := hA.preimage (continuous_const.prodMk continuous_id)
    have h₁ : IsClosed A₁ := hA.preimage (continuous_const.prodMk continuous_id)
    have hH : IsClosed H := isClosed_le continuous_const continuous_im
    have himg : f '' A = (Subtype.val '' A₀) ∪ conj '' (Subtype.val '' A₁) := by
      ext z
      constructor
      · rintro ⟨⟨b, w⟩, hw, rfl⟩
        cases b
        · exact Or.inl ⟨w, hw, rfl⟩
        · exact Or.inr ⟨w.val, ⟨w, hw, rfl⟩, rfl⟩
      · rintro (⟨w, hw, rfl⟩ | ⟨_, ⟨w, hw, rfl⟩, rfl⟩)
        · exact ⟨(false, w), hw, rfl⟩
        · exact ⟨(true, w), hw, rfl⟩
    rw [himg]
    exact (hH.isClosedMap_subtype_val A₀ h₀).union
      (Complex.conjCLE.toHomeomorph.isClosedMap _ (hH.isClosedMap_subtype_val A₁ h₁))
  exact hclosed.isQuotientMap hc hs

/-- The two folded halves intersect exactly on the real axis. -/
theorem s78ra_upper_eq_conj_iff (z w : {z : ℂ | 0 ≤ z.im}) :
    z.val = conj w.val ↔ z = w ∧ z.val.im = 0 := by
  constructor
  · intro h
    have hi := congrArg Complex.im h
    simp only [conj_im] at hi
    have hz0 : 0 ≤ z.val.im := z.property
    have hw0 : 0 ≤ w.val.im := w.property
    have hz : z.val.im = 0 := by linarith
    have hw : w.val.im = 0 := by linarith
    rw [conj_eq_iff_im.2 hw] at h
    exact ⟨Subtype.ext h, hz⟩
  · rintro ⟨rfl, hz⟩
    exact (conj_eq_iff_im.2 hz).symm

/-- Exact fibers of the actual two-sheet fold. -/
theorem s78ra_halfplane_fold_fibers
    (x y : Bool × {z : ℂ | 0 ≤ z.im}) :
    (if x.1 then conj x.2.val else x.2.val) =
      (if y.1 then conj y.2.val else y.2.val) ↔
      x.2 = y.2 ∧ (x.1 = y.1 ∨ x.2.val.im = 0) := by
  rcases x with ⟨b, z⟩
  rcases y with ⟨c, w⟩
  cases b <;> cases c
  · constructor
    · intro he
      exact ⟨Subtype.ext he, Or.inl rfl⟩
    · intro he
      exact congrArg Subtype.val he.1
  · simpa using s78ra_upper_eq_conj_iff z w
  · have h := s78ra_upper_eq_conj_iff w z
    constructor
    · intro he
      have he' : w.val = conj z.val := he.symm
      obtain ⟨hwz, hw⟩ := h.1 he'
      exact ⟨hwz.symm, Or.inr (hwz ▸ hw)⟩
    · intro he
      change z = w ∧ (true = false ∨ z.val.im = 0) at he
      have hz : z.val.im = 0 := he.2.resolve_left (by decide)
      have hzw : z = w := he.1
      exact (h.2 ⟨hzw.symm, hzw ▸ hz⟩).symm
  · constructor
    · intro he
      exact ⟨Subtype.ext (Complex.conjCLE.injective he), Or.inl rfl⟩
    · intro he
      exact congrArg (fun z : {z : ℂ | 0 ≤ z.im} => conj z.val) he.1

/-- A real-boundary half-plane coordinate on an open part of the actual
core sews to a genuine chart homeomorphism on the actual quotient window.
The formulas on both actual side inclusions are retained. -/
theorem s78ra_sew_actual_halfplane
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m)
    (V : Set (s31dt_Core F)) (hV : IsOpen V)
    (h : ↥V ≃ₜ {z : ℂ | 0 ≤ z.im})
    (hboundary : ∀ x : ↥V, x.val ∈ s31dt_boundary F ↔ (h x).val.im = 0) :
    ∃ E : ↥(s31dt_project F ⁻¹' V) ≃ₜ ℂ,
      ∀ b (x : ↥V), E ⟨s31dt_side F b x.val, x.property⟩ =
        if b then conj (h x).val else (h x).val := by
  let W : Set (s31dt_Double F) := s31dt_project F ⁻¹' V
  have hW : IsOpen W := hV.preimage (s31dt_continuous_project F)
  let R : Bool × ↥V ≃ₜ ↥(s31dt_mk F ⁻¹' W) := {
    toFun := fun x => ⟨(x.1, x.2.val), x.2.property⟩
    invFun := fun x => (x.val.1, ⟨x.val.2, x.property⟩)
    left_inv := by intro x; rfl
    right_inv := by intro x; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let q : Bool × ↥V → ↥W := fun x => ⟨s31dt_side F x.1 x.2.val, x.2.property⟩
  have hmk : IsQuotientMap (s31dt_mk F) := isQuotientMap_quotient_mk'
  have hq : IsQuotientMap q :=
    (hmk.restrictPreimage_isOpen hW).comp R.isQuotientMap
  let T : Bool × ↥V ≃ₜ Bool × {z : ℂ | 0 ≤ z.im} :=
    (Homeomorph.refl Bool).prodCongr h
  let f : Bool × ↥V → ℂ := fun x => if x.1 then conj (h x.2).val else (h x.2).val
  have hf : IsQuotientMap f := s78ra_halfplane_fold_quotient.comp T.isQuotientMap
  have hker : ∀ x y, q x = q y ↔ f x = f y := by
    intro x y
    have hqeq : q x = q y ↔
        x.2 = y.2 ∧ (x.1 = y.1 ∨ x.2.val ∈ s31dt_boundary F) := by
      rw [Subtype.ext_iff]
      change s31dt_side F x.1 x.2.val = s31dt_side F y.1 y.2.val ↔ _
      rw [s31dt_side_eq_iff]
      exact and_congr_left (fun _ => Subtype.val_injective.eq_iff)
    rw [hqeq]
    change _ ↔ (if x.1 then conj (h x.2).val else (h x.2).val) =
      (if y.1 then conj (h y.2).val else (h y.2).val)
    change _ ↔ (if (T x).1 then conj (T x).2.val else (T x).2.val) =
      (if (T y).1 then conj (T y).2.val else (T y).2.val)
    rw [s78ra_halfplane_fold_fibers (T x) (T y)]
    change _ ↔ h x.2 = h y.2 ∧ (x.1 = y.1 ∨ (h x.2).val.im = 0)
    rw [h.injective.eq_iff, hboundary x.2]
  obtain ⟨E, hE⟩ := h84g_homeomorph_of_same_fibers q f hq hf hker
  exact ⟨E, fun b x => hE (b, x)⟩

/-- The sewn homeomorphism gives an actual open partial chart on the
shared quotient. Its exact flip-equivariance is ready for the already
proved Schwarz compatibility theorem. -/
theorem s78ra_actual_quotient_boundary_chart
    {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m)
    (V : Set (s31dt_Core F)) (hV : IsOpen V)
    (h : ↥V ≃ₜ {z : ℂ | 0 ≤ z.im})
    (hboundary : ∀ x : ↥V, x.val ∈ s31dt_boundary F ↔ (h x).val.im = 0) :
    ∃ u : OpenPartialHomeomorph (s31dt_Double F) ℂ,
      u.source = s31dt_project F ⁻¹' V ∧ u.target = univ ∧
      (∀ b (x : ↥V), u (s31dt_side F b x.val) =
        if b then conj (h x).val else (h x).val) ∧
      (∀ q ∈ u.source, s31dt_flip F q ∈ u.source ∧
        u (s31dt_flip F q) = conj (u q)) := by
  let W : Set (s31dt_Double F) := s31dt_project F ⁻¹' V
  have hW : IsOpen W := hV.preimage (s31dt_continuous_project F)
  obtain ⟨E, hE⟩ := s78ra_sew_actual_halfplane F V hV h hboundary
  have hWne : W.Nonempty := by
    let x : ↥V := h.symm ⟨0, by simp⟩
    exact ⟨s31dt_side F false x.val, x.property⟩
  let E' : ↥W ≃ₜ (univ : Set ℂ) := E.trans (Homeomorph.Set.univ ℂ).symm
  obtain ⟨u, huS, huT, hu⟩ := h84g_open_subspaces_chart W univ hW isOpen_univ
    hWne ⟨0, mem_univ _⟩ E'
  have hside : ∀ b (x : ↥V), u (s31dt_side F b x.val) =
      if b then conj (h x).val else (h x).val := by
    intro b x
    have hux := hu ⟨s31dt_side F b x.val, x.property⟩
    change u (s31dt_side F b x.val) = E ⟨s31dt_side F b x.val, x.property⟩ at hux
    exact hux.trans (hE b x)
  refine ⟨u, huS, huT, hside, ?_⟩
  intro q
  refine Quotient.inductionOn q ?_
  intro x hx
  rcases x with ⟨b, x⟩
  have hxV : x ∈ V := by
    rw [huS] at hx
    exact hx
  change s31dt_flip F (s31dt_side F b x) ∈ u.source ∧
    u (s31dt_flip F (s31dt_side F b x)) = conj (u (s31dt_side F b x))
  rw [s31dt_flip_side]
  constructor
  · rw [huS]
    exact hxV
  · rw [hside (!b) ⟨x, hxV⟩, hside b ⟨x, hxV⟩]
    cases b <;> simp

end LiZhongQC
