import LiZhongExternal.Classification.SchottkyClassification28
import LiZhongQC.Lemmas.SchottkyCoreC0Atlas
import LiZhongQC.Lemmas.SchottkyDoubleConnected
import LiZhongQC.Lemmas.SchottkyBoundaryRankModel
import LiZhongQC.Lemmas.SchottkyCoreBoundaryComponents
import LiZhongQC.Lemmas.SchottkyBoundaryRankSphere
import LiZhongQC.Lemmas.SchottkyCoreModelBoundary
import Mathlib

/-!
# Boundary rank of the core (route β)

* B1: the classification of compact surfaces applied to the core `s31dt_Core F`.
* B4: circle-valued maps on the core with prescribed winding along the `m` boundary loops.
* B5: the induced characters of the fundamental group of the core.
-/

open Complex Set Topology LeanEval.Topology.ClassificationOfSurfaces

namespace LiZhongQC

universe u

/-- A continuous integer-valued function on a preconnected set is constant. -/
theorem s78rb_int_const (f : ℝ → ℝ) {s : Set ℝ} (hs : IsPreconnected s) (hc : ContinuousOn f s)
    (hint : ∀ t ∈ s, ∃ k : ℤ, f t = k) : ∀ a ∈ s, ∀ b ∈ s, f a = f b := by
  intro a ha b hb
  by_contra hne
  obtain ⟨ka, hka⟩ := hint a ha
  obtain ⟨kb, hkb⟩ := hint b hb
  have hk : ka ≠ kb := fun h => hne (by rw [hka, hkb, h])
  rcases lt_or_gt_of_ne hk with h | h
  · have h1 : (ka : ℝ) + 1 ≤ kb := by exact_mod_cast h
    obtain ⟨c, hc, hfc⟩ := hs.intermediate_value ha hb hc
      (show f a + 1 / 2 ∈ Icc (f a) (f b) by constructor <;> linarith)
    obtain ⟨kc, hkc⟩ := hint c hc
    have : (2 : ℝ) * (kc - ka) = 1 := by linarith
    have : (2 : ℤ) * (kc - ka) = 1 := by exact_mod_cast this
    omega
  · have h1 : (kb : ℝ) + 1 ≤ ka := by exact_mod_cast h
    obtain ⟨c, hc, hfc⟩ := hs.intermediate_value hb ha hc
      (show f b + 1 / 2 ∈ Icc (f b) (f a) by constructor <;> linarith)
    obtain ⟨kc, hkc⟩ := hint c hc
    have : (2 : ℝ) * (kc - kb) = 1 := by linarith
    have : (2 : ℤ) * (kc - kb) = 1 := by exact_mod_cast this
    omega

/-- Two reals with the same image in `AddCircle 1` differ by an integer. -/
theorem s78rb_coe_eq_int (x y : ℝ) (h : (x : AddCircle (1 : ℝ)) = y) : ∃ k : ℤ, x = y + k := by
  have h0 : ((x - y : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp h0
  refine ⟨k, ?_⟩
  rw [zsmul_one] at hk
  linarith

/-- Every continuous map `ℝ → AddCircle 1` has a continuous real lift. -/
theorem s78rb_lift_real (f : C(ℝ, AddCircle (1 : ℝ))) :
    ∃ L : C(ℝ, ℝ), ∀ t, f t = (L t : AddCircle (1 : ℝ)) := by
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  obtain ⟨e₀, he₀⟩ := QuotientAddGroup.mk_surjective (f 0)
  obtain ⟨F, ⟨-, hF⟩, -⟩ :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts f 0 e₀ he₀
  exact ⟨F, fun t => (congrFun hF t).symm⟩

/-- A lift whose shift by one period is the same point of the circle has a constant integer increment. -/
theorem s78rb_lift_increment (L : C(ℝ, ℝ)) (h : ∀ t, ((L (t + 1) : ℝ) : AddCircle (1 : ℝ)) = L t) :
    ∃ D : ℤ, ∀ t, L (t + 1) = L t + D := by
  have hint : ∀ t ∈ (univ : Set ℝ), ∃ k : ℤ, L (t + 1) - L t = k := by
    intro t _
    obtain ⟨k, hk⟩ := s78rb_coe_eq_int _ _ (h t)
    exact ⟨k, by linarith⟩
  have hc : ContinuousOn (fun t => L (t + 1) - L t) univ :=
    ((L.continuous.comp (continuous_id.add continuous_const)).sub L.continuous).continuousOn
  obtain ⟨D, hD⟩ := hint 0 (mem_univ _)
  refine ⟨D, fun t => ?_⟩
  have := s78rb_int_const (fun t => L (t + 1) - L t) isPreconnected_univ hc hint t (mem_univ _) 0
    (mem_univ _)
  linarith

/-- Iterating a constant increment. -/
theorem s78rb_lift_iter (L : ℝ → ℝ) (D : ℝ) (h : ∀ t, L (t + 1) = L t + D) (k : ℤ) (x : ℝ) :
    L (x + k) = L x + k * D := by
  induction k using Int.induction_on generalizing x with
  | zero => simp
  | succ k ih =>
      have := h (x + k)
      have ih' := ih x
      push_cast at ih' ⊢
      rw [show x + ((k : ℝ) + 1) = x + k + 1 by ring, this, ih']
      ring
  | pred k ih =>
      have := h (x + (-(k : ℝ) - 1))
      push_cast
      rw [show x + (-(k : ℝ) - 1) + 1 = x + -(k : ℝ) by ring] at this
      have ih' := ih x
      push_cast at ih'
      linarith

/-- **Degree ±1.**  A real function continuous on `[0,1]`, injective modulo `1` on `[0,1)`, whose values at
`0` and `1` differ by an integer `e`, has `e = ±1`. -/
theorem s78rb_degree_unit (G : ℝ → ℝ) (hG : ContinuousOn G (Icc 0 1)) (e : ℤ) (he : G 1 = G 0 + e)
    (hinj : InjOn (fun t => (G t : AddCircle (1 : ℝ))) (Ico 0 1)) : e = 1 ∨ e = -1 := by
  -- two distinct points of `[0,1)` with the same value modulo `1` are impossible
  have key : ∀ t ∈ Ico (0 : ℝ) 1, ∀ t' ∈ Ico (0 : ℝ) 1, t ≠ t' →
      (G t : AddCircle (1 : ℝ)) ≠ G t' := fun t ht t' ht' hne h => hne (hinj ht ht' h)
  have hcoe : ∀ x : ℝ, ∀ k : ℤ, ((x + k : ℝ) : AddCircle (1 : ℝ)) = x := by
    intro x k
    rw [AddCircle.coe_add, show ((k : ℝ) : AddCircle (1 : ℝ)) = 0 from by
      rw [AddCircle.coe_eq_zero_iff]; exact ⟨k, by simp⟩, add_zero]
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, add_zero] at he
    by_cases hmid : G (1 / 2) = G 0
    · exact key 0 ⟨le_rfl, one_pos⟩ (1 / 2) ⟨by norm_num, by norm_num⟩ (by norm_num)
        (by rw [hmid])
    · set v := (G 0 + G (1 / 2)) / 2 with hv
      have hc1 : ContinuousOn G (Icc 0 (1 / 2)) := hG.mono (Icc_subset_Icc le_rfl (by norm_num))
      have hc2 : ContinuousOn G (Icc (1 / 2) 1) := hG.mono (Icc_subset_Icc (by norm_num) le_rfl)
      have hv1 : v ∈ uIcc (G 0) (G (1 / 2)) := by
        rcases lt_or_gt_of_ne hmid with h | h
        · rw [uIcc_of_ge h.le]; constructor <;> linarith
        · rw [uIcc_of_le h.le]; constructor <;> linarith
      have hv2 : v ∈ uIcc (G (1 / 2)) (G 1) := by rw [he, uIcc_comm]; exact hv1
      obtain ⟨t1, ht1, hGt1⟩ := intermediate_value_uIcc (a := (0 : ℝ)) (b := 1 / 2)
        (by rwa [uIcc_of_le (by norm_num)]) hv1
      obtain ⟨t2, ht2, hGt2⟩ := intermediate_value_uIcc (a := (1 / 2 : ℝ)) (b := 1)
        (by rwa [uIcc_of_le (by norm_num)]) hv2
      rw [uIcc_of_le (by norm_num)] at ht1 ht2
      have hvne0 : v ≠ G 0 := by intro h; apply hmid; linarith
      have hvne1 : v ≠ G (1 / 2) := by intro h; apply hmid; linarith
      have ht1a : t1 ≠ 0 := by rintro rfl; exact hvne0 hGt1.symm
      have ht1b : t1 ≠ 1 / 2 := by rintro rfl; exact hvne1 hGt1.symm
      have ht2a : t2 ≠ 1 / 2 := by rintro rfl; exact hvne1 hGt2.symm
      have ht2b : t2 ≠ 1 := by rintro rfl; rw [he] at hGt2; exact hvne0 hGt2.symm
      have hlt1 : t1 < 1 / 2 := lt_of_le_of_ne ht1.2 ht1b
      have hlt2 : 1 / 2 < t2 := lt_of_le_of_ne ht2.1 (Ne.symm ht2a)
      exact key t1 ⟨ht1.1, by linarith⟩ t2 ⟨by linarith, lt_of_le_of_ne ht2.2 ht2b⟩ (by linarith)
        (by rw [hGt1, hGt2])
  -- `|e| ≥ 2` gives two points with values `G 0 + 1/2` and `G 0 + 3/2` (or their negatives)
  have hbig : ¬ (2 ≤ e) := by
    intro h2
    have h2' : (2 : ℝ) ≤ e := by exact_mod_cast h2
    have hmem : ∀ v ∈ Ioo (G 0) (G 0 + 2), ∃ t ∈ Ioo (0 : ℝ) 1, G t = v := by
      intro v hv
      obtain ⟨t, ht, hGt⟩ := intermediate_value_Icc zero_le_one hG
        (show v ∈ Icc (G 0) (G 1) by rw [he]; constructor <;> linarith [hv.1, hv.2])
      refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, hGt⟩
      · rintro rfl; linarith [hv.1]
      · rintro rfl; rw [he] at hGt; linarith [hv.2]
    obtain ⟨t1, ht1, h1⟩ := hmem (G 0 + 1 / 2) ⟨by linarith, by linarith⟩
    obtain ⟨t2, ht2, h2⟩ := hmem (G 0 + 3 / 2) ⟨by linarith, by linarith⟩
    refine key t1 ⟨ht1.1.le, ht1.2⟩ t2 ⟨ht2.1.le, ht2.2⟩ (fun h => ?_) ?_
    · rw [h] at h1; linarith
    · rw [h1, h2, show G 0 + 3 / 2 = (G 0 + 1 / 2) + ((1 : ℤ) : ℝ) by push_cast; ring, hcoe]
  have hsmall : ¬ (e ≤ -2) := by
    intro h2
    have h2' : (e : ℝ) ≤ -2 := by exact_mod_cast h2
    have hmem : ∀ v ∈ Ioo (G 0 - 2) (G 0), ∃ t ∈ Ioo (0 : ℝ) 1, G t = v := by
      intro v hv
      obtain ⟨t, ht, hGt⟩ := intermediate_value_Icc' zero_le_one hG
        (show v ∈ Icc (G 1) (G 0) by rw [he]; constructor <;> linarith [hv.1, hv.2])
      refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, hGt⟩
      · rintro rfl; linarith [hv.2]
      · rintro rfl; rw [he] at hGt; linarith [hv.1]
    obtain ⟨t1, ht1, h1⟩ := hmem (G 0 - 1 / 2) ⟨by linarith, by linarith⟩
    obtain ⟨t2, ht2, h2⟩ := hmem (G 0 - 3 / 2) ⟨by linarith, by linarith⟩
    refine key t1 ⟨ht1.1.le, ht1.2⟩ t2 ⟨ht2.1.le, ht2.2⟩ (fun h => ?_) ?_
    · rw [h] at h1; linarith
    · rw [h1, h2, show G 0 - 1 / 2 = (G 0 - 3 / 2) + ((1 : ℤ) : ℝ) by push_cast; ring, hcoe]
  omega

/-- An integer translate is the same point of `AddCircle 1`. -/
theorem s78rb_coe_add_int (x : ℝ) (k : ℤ) : ((x + k : ℝ) : AddCircle (1 : ℝ)) = x := by
  rw [AddCircle.coe_add, show ((k : ℝ) : AddCircle (1 : ℝ)) = 0 from by
    rw [AddCircle.coe_eq_zero_iff]; exact ⟨k, by simp⟩, add_zero]

/-- **Winding along an embedded loop.**  Let `β` be a `1`-periodic loop in a Hausdorff space, injective on
`[0,1)`, and `pa` an arc on `[0,1]` with the same image, closing up and injective on `[0,1)`.  There is a sign
`ε = ±1` such that for every circle-valued map `f` which is affine of integer slope `w` along `pa`, the lift
of `f ∘ β` has increment `ε w` per period. -/
theorem s78rb_arc_winding {X : Type*} [TopologicalSpace X] [T2Space X]
    (β : C(ℝ, X)) (hper : ∀ t, β (t + 1) = β t) (hinj : InjOn β (Ico 0 1))
    (pa : ℝ → X) (hpc : ContinuousOn pa (Icc 0 1)) (hp01 : pa 0 = pa 1)
    (hpinj : InjOn pa (Ico 0 1)) (hrange : pa '' Icc 0 1 = range β) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (f : C(X, AddCircle (1 : ℝ))) (a : ℝ) (w : ℤ),
      (∀ t ∈ Icc (0 : ℝ) 1, f (pa t) = ((a + w * t : ℝ) : AddCircle (1 : ℝ))) →
      ∃ L : C(ℝ, ℝ), (∀ t, f (β t) = (L t : AddCircle (1 : ℝ))) ∧
        ∀ t, L (t + 1) = L t + ε * w := by
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hβp : Function.Periodic β 1 := hper
  -- the circle map of `β`
  let B : AddCircle (1 : ℝ) → X := hβp.lift
  have hBc : Continuous B := β.continuous.quotient_liftOn' _
  have hBcoe : ∀ s : ℝ, B (s : AddCircle (1 : ℝ)) = β s := fun s => rfl
  have hrep : ∀ θ : AddCircle (1 : ℝ), ∃ s ∈ Ico (0 : ℝ) 1, θ = s := by
    intro θ
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective θ
    refine ⟨toIcoMod one_pos 0 s, by simpa using toIcoMod_mem_Ico one_pos 0 s, ?_⟩
    have hk : toIcoMod one_pos 0 s = s + ((-toIcoDiv one_pos 0 s : ℤ) : ℝ) := by
      simp [toIcoMod, sub_eq_add_neg]
    rw [hk, s78rb_coe_add_int]
  have hBinj : Function.Injective B := by
    intro θ θ' h
    obtain ⟨s, hs, rfl⟩ := hrep θ
    obtain ⟨s', hs', rfl⟩ := hrep θ'
    rw [hBcoe, hBcoe] at h
    rw [hinj hs hs' h]
  have hemb := hBc.isClosedEmbedding hBinj
  let E := hemb.isEmbedding.toHomeomorph
  have hrangeB : range B = range β := by
    ext x
    constructor
    · rintro ⟨θ, rfl⟩
      obtain ⟨s, -, rfl⟩ := hrep θ
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s, rfl⟩
  have hpmem : ∀ t ∈ Icc (0 : ℝ) 1, pa t ∈ range B := by
    intro t ht
    rw [hrangeB, ← hrange]
    exact ⟨t, ht, rfl⟩
  -- the arc as a path in the circle
  let P : C(unitInterval, range B) :=
    ⟨fun t => ⟨pa t, hpmem t t.2⟩,
      (hpc.comp_continuous continuous_subtype_val fun t => t.2).subtype_mk _⟩
  let γ : C(unitInterval, AddCircle (1 : ℝ)) := ⟨fun t => E.symm (P t), E.symm.continuous.comp P.continuous⟩
  obtain ⟨g₀, hg₀⟩ := QuotientAddGroup.mk_surjective (γ 0)
  obtain ⟨Γ, hΓ, -⟩ := (AddCircle.isCoveringMap_coe (1 : ℝ)).exists_path_lifts γ g₀ hg₀.symm
  let G : ℝ → ℝ := fun t => Γ (Set.projIcc 0 1 zero_le_one t)
  have hGc : Continuous G := Γ.continuous.comp continuous_projIcc
  have hGcoe : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      (G t : AddCircle (1 : ℝ)) = E.symm (P ⟨t, ht⟩) := by
    intro t ht
    show ((Γ (Set.projIcc 0 1 zero_le_one t) : ℝ) : AddCircle (1 : ℝ)) = _
    rw [Set.projIcc_of_mem zero_le_one ht]
    exact congrFun hΓ ⟨t, ht⟩
  have hBG : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1), B (G t) = pa t := by
    intro t ht
    rw [hGcoe t ht]
    exact congrArg Subtype.val (E.apply_symm_apply (P ⟨t, ht⟩))
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℤ, G 1 = G 0 + e := by
    apply s78rb_coe_eq_int
    rw [hGcoe 1 h1, hGcoe 0 h0]
    have hP : P ⟨1, h1⟩ = P ⟨0, h0⟩ := Subtype.ext hp01.symm
    rw [hP]
  have hdeg : e = 1 ∨ e = -1 := by
    refine s78rb_degree_unit G hGc.continuousOn e he ?_
    intro t ht t' ht' h
    have ht0 : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
    have ht0' : t' ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht'
    simp only at h
    rw [hGcoe t ht0, hGcoe t' ht0'] at h
    have := congrArg Subtype.val (E.symm.injective h)
    exact hpinj ht ht' this
  refine ⟨e, hdeg, fun f a w hf => ?_⟩
  obtain ⟨L, hL⟩ := s78rb_lift_real (f.comp β)
  obtain ⟨D, hD⟩ := s78rb_lift_increment L (fun t => by
    rw [← hL, ← hL]
    show f (β (t + 1)) = f (β t)
    rw [hper])
  have hint : ∀ t ∈ Icc (0 : ℝ) 1, ∃ k : ℤ, L (G t) - (a + w * t) = k := by
    intro t ht
    have hc : ((L (G t) : ℝ) : AddCircle (1 : ℝ)) = ((a + w * t : ℝ) : AddCircle (1 : ℝ)) := by
      rw [← hL]
      show f (β (G t)) = _
      rw [← hBcoe, hBG t ht, hf t ht]
    obtain ⟨k, hk⟩ := s78rb_coe_eq_int _ _ hc
    exact ⟨k, by linarith⟩
  have hcont : ContinuousOn (fun t => L (G t) - (a + w * t)) (Icc 0 1) :=
    ((L.continuous.comp hGc).sub (continuous_const.add (continuous_const.mul continuous_id))).continuousOn
  have heq := s78rb_int_const _ isPreconnected_Icc hcont hint 0 h0 1 h1
  simp only [mul_zero, add_zero, mul_one] at heq
  have hiter := s78rb_lift_iter L D hD e (G 0)
  rw [← he] at hiter
  have hwD : (w : ℝ) = e * D := by linarith
  refine ⟨L, fun t => hL t, fun t => ?_⟩
  rw [hD t]
  have hDw : (D : ℝ) = e * w := by
    rcases hdeg with h | h <;> rw [h] at hwD ⊢ <;> push_cast at hwD ⊢ <;> linarith
  rw [hDw]



/-! ### B4 -/

/-- Boundary points of the disc depend continuously on the parameter. -/
theorem s78rb_bdyPt_continuous : Continuous ClosedUnitDisc.bdyPtOfReal :=
  (continuous_subtype_val.comp Real.continuous_fourierChar).subtype_mk _

/-- The weight vector `e_k − e_{k₀}` sums to zero. -/
theorem s78rb_weight_sum {q : ℕ} (a b : Fin q) :
    ∑ i : Fin q, ((if i = a then (1 : ℤ) else 0) - (if i = b then 1 else 0)) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ a, Finset.sum_ite_eq' Finset.univ b]
  simp

/-- The shared assembly step for one model: from a homeomorphism `φ` of the core onto a quotient `Q`,
a matching `σ` of the boundary circles with the free arcs, the model characters and the embedded-loop
facts, produce the B4 conclusion. -/
theorem s78rb_assembly {X Q : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Q]
    {m q : ℕ} (hm : m ≠ 0) (φ : X ≃ₜ Q) (arc : Fin q → ℝ → Q) (harc : ∀ i, Continuous (arc i))
    (hloop : ∀ i, arc i 0 = arc i 1 ∧ InjOn (arc i) (Ico 0 1))
    (σ : Fin m ≃ Fin q) (C : Fin m → Set X) (hσ : ∀ j, φ '' C j = arc (σ j) '' Icc 0 1)
    (hchar : ∀ w : Fin q → ℤ, ∑ i, w i = 0 → ∃ χ : C(Q, AddCircle (1 : ℝ)), ∃ a : Fin q → ℝ,
      ∀ (i : Fin q) (t : ℝ), t ∈ Icc (0 : ℝ) 1 → χ (arc i t) = ((a i + w i * t : ℝ) : AddCircle (1 : ℝ)))
    (β : Fin m → C(ℝ, X)) (hβper : ∀ j t, β j (t + 1) = β j t) (hβinj : ∀ j, InjOn (β j) (Ico 0 1))
    (hβrange : ∀ j, range (β j) = C j) :
    ∃ (χ : Fin m → C(X, AddCircle (1 : ℝ))) (ε : Fin m → ℤ),
      (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ k j, ∃ L : C(ℝ, ℝ), (∀ t, χ k (β j t) = (L t : AddCircle (1 : ℝ))) ∧
        ∀ t, L (t + 1) = L t + ε j * ((if j = k then 1 else 0) -
          (if j = ⟨0, Nat.pos_of_ne_zero hm⟩ then 1 else 0)) := by
  set j₀ : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
  -- the arcs pulled back to `X`
  let pa : Fin m → ℝ → X := fun j t => φ.symm (arc (σ j) t)
  have hwind : ∀ j, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (f : C(X, AddCircle (1 : ℝ))) (a : ℝ) (w : ℤ),
      (∀ t ∈ Icc (0 : ℝ) 1, f (pa j t) = ((a + w * t : ℝ) : AddCircle (1 : ℝ))) →
      ∃ L : C(ℝ, ℝ), (∀ t, f (β j t) = (L t : AddCircle (1 : ℝ))) ∧
        ∀ t, L (t + 1) = L t + ε * w := by
    intro j
    refine s78rb_arc_winding (β j) (hβper j) (hβinj j) (pa j)
      (φ.symm.continuous.comp (harc (σ j))).continuousOn
      (by simp only [pa]; rw [(hloop (σ j)).1]) ?_ ?_
    · intro t ht t' ht' h
      exact (hloop (σ j)).2 ht ht' (φ.symm.injective h)
    · rw [hβrange j, ← image_image, ← hσ j]
      simp only [Set.image_image, Homeomorph.symm_apply_apply, Set.image_id']
  choose ε hε hwind using hwind
  let w : Fin m → Fin q → ℤ := fun k i =>
    if k = j₀ then 0 else (if i = σ k then 1 else 0) - (if i = σ j₀ then 1 else 0)
  have hw : ∀ k, ∑ i, w k i = 0 := by
    intro k
    by_cases hk : k = j₀
    · simp [w, hk]
    · simp only [w, hk, if_false]
      exact s78rb_weight_sum _ _
  choose χm a hχm using fun k => hchar (w k) (hw k)
  refine ⟨fun k => (χm k).comp ⟨φ, φ.continuous⟩, ε, hε, fun k j => ?_⟩
  obtain ⟨L, hL, hLper⟩ := hwind j ((χm k).comp ⟨φ, φ.continuous⟩) (a k (σ j)) (w k (σ j))
    (fun t ht => by
      show χm k (φ (φ.symm (arc (σ j) t))) = _
      rw [φ.apply_symm_apply]
      exact hχm k (σ j) t ht)
  refine ⟨L, hL, fun t => ?_⟩
  rw [hLper t]
  congr 1
  congr 1
  simp only [w, σ.injective.eq_iff]
  by_cases hk : k = j₀
  · subst hk
    by_cases hj : j = j₀ <;> simp [hj]
  · by_cases hj : j = k
    · subst hj
      simp [hk]
    · by_cases hj0 : j = j₀ <;> simp [hk, hj, hj0]


/-! ### B5, generic part -/

/-- **Winding along an embedded loop, general form.**  As `s78rb_arc_winding`, but the circle-valued map
is only assumed to have a continuous lift `Lp` along the arc with increment `w`. -/
theorem s78rb_arc_winding_gen {X : Type*} [TopologicalSpace X] [T2Space X]
    (β : C(ℝ, X)) (hper : ∀ t, β (t + 1) = β t) (hinj : InjOn β (Ico 0 1))
    (pa : ℝ → X) (hpc : ContinuousOn pa (Icc 0 1)) (hp01 : pa 0 = pa 1)
    (hpinj : InjOn pa (Ico 0 1)) (hrange : pa '' Icc 0 1 = range β) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (f : C(X, AddCircle (1 : ℝ))) (Lp : ℝ → ℝ) (w : ℤ),
      ContinuousOn Lp (Icc 0 1) → Lp 1 = Lp 0 + w →
      (∀ t ∈ Icc (0 : ℝ) 1, f (pa t) = ((Lp t : ℝ) : AddCircle (1 : ℝ))) →
      ∃ L : C(ℝ, ℝ), (∀ t, f (β t) = (L t : AddCircle (1 : ℝ))) ∧
        ∀ t, L (t + 1) = L t + ε * w := by
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hβp : Function.Periodic β 1 := hper
  let B : AddCircle (1 : ℝ) → X := hβp.lift
  have hBc : Continuous B := β.continuous.quotient_liftOn' _
  have hBcoe : ∀ s : ℝ, B (s : AddCircle (1 : ℝ)) = β s := fun s => rfl
  have hrep : ∀ θ : AddCircle (1 : ℝ), ∃ s ∈ Ico (0 : ℝ) 1, θ = s := by
    intro θ
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective θ
    refine ⟨toIcoMod one_pos 0 s, by simpa using toIcoMod_mem_Ico one_pos 0 s, ?_⟩
    have hk : toIcoMod one_pos 0 s = s + ((-toIcoDiv one_pos 0 s : ℤ) : ℝ) := by
      simp [toIcoMod, sub_eq_add_neg]
    rw [hk, s78rb_coe_add_int]
  have hBinj : Function.Injective B := by
    intro θ θ' h
    obtain ⟨s, hs, rfl⟩ := hrep θ
    obtain ⟨s', hs', rfl⟩ := hrep θ'
    rw [hBcoe, hBcoe] at h
    rw [hinj hs hs' h]
  have hemb := hBc.isClosedEmbedding hBinj
  let E := hemb.isEmbedding.toHomeomorph
  have hrangeB : range B = range β := by
    ext x
    constructor
    · rintro ⟨θ, rfl⟩
      obtain ⟨s, -, rfl⟩ := hrep θ
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s, rfl⟩
  have hpmem : ∀ t ∈ Icc (0 : ℝ) 1, pa t ∈ range B := by
    intro t ht
    rw [hrangeB, ← hrange]
    exact ⟨t, ht, rfl⟩
  let P : C(unitInterval, range B) :=
    ⟨fun t => ⟨pa t, hpmem t t.2⟩,
      (hpc.comp_continuous continuous_subtype_val fun t => t.2).subtype_mk _⟩
  let γ : C(unitInterval, AddCircle (1 : ℝ)) := ⟨fun t => E.symm (P t), E.symm.continuous.comp P.continuous⟩
  obtain ⟨g₀, hg₀⟩ := QuotientAddGroup.mk_surjective (γ 0)
  obtain ⟨Γ, hΓ, -⟩ := (AddCircle.isCoveringMap_coe (1 : ℝ)).exists_path_lifts γ g₀ hg₀.symm
  let G : ℝ → ℝ := fun t => Γ (Set.projIcc 0 1 zero_le_one t)
  have hGc : Continuous G := Γ.continuous.comp continuous_projIcc
  have hGcoe : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
      (G t : AddCircle (1 : ℝ)) = E.symm (P ⟨t, ht⟩) := by
    intro t ht
    show ((Γ (Set.projIcc 0 1 zero_le_one t) : ℝ) : AddCircle (1 : ℝ)) = _
    rw [Set.projIcc_of_mem zero_le_one ht]
    exact congrFun hΓ ⟨t, ht⟩
  have hBG : ∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1), B (G t) = pa t := by
    intro t ht
    rw [hGcoe t ht]
    exact congrArg Subtype.val (E.apply_symm_apply (P ⟨t, ht⟩))
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℤ, G 1 = G 0 + e := by
    apply s78rb_coe_eq_int
    rw [hGcoe 1 h1, hGcoe 0 h0]
    have hP : P ⟨1, h1⟩ = P ⟨0, h0⟩ := Subtype.ext hp01.symm
    rw [hP]
  have hdeg : e = 1 ∨ e = -1 := by
    refine s78rb_degree_unit G hGc.continuousOn e he ?_
    intro t ht t' ht' h
    have ht0 : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
    have ht0' : t' ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht'
    simp only at h
    rw [hGcoe t ht0, hGcoe t' ht0'] at h
    have := congrArg Subtype.val (E.symm.injective h)
    exact hpinj ht ht' this
  refine ⟨e, hdeg, fun f Lp w hLpc hLp hf => ?_⟩
  obtain ⟨L, hL⟩ := s78rb_lift_real (f.comp β)
  obtain ⟨D, hD⟩ := s78rb_lift_increment L (fun t => by
    rw [← hL, ← hL]
    show f (β (t + 1)) = f (β t)
    rw [hper])
  have hint : ∀ t ∈ Icc (0 : ℝ) 1, ∃ k : ℤ, L (G t) - Lp t = k := by
    intro t ht
    have hc : ((L (G t) : ℝ) : AddCircle (1 : ℝ)) = ((Lp t : ℝ) : AddCircle (1 : ℝ)) := by
      rw [← hL]
      show f (β (G t)) = _
      rw [← hBcoe, hBG t ht, hf t ht]
    obtain ⟨k, hk⟩ := s78rb_coe_eq_int _ _ hc
    exact ⟨k, by linarith⟩
  have hcont : ContinuousOn (fun t => L (G t) - Lp t) (Icc 0 1) :=
    (L.continuous.comp hGc).continuousOn.sub hLpc
  have heq := s78rb_int_const _ isPreconnected_Icc hcont hint 0 h0 1 h1
  have hiter := s78rb_lift_iter L D hD e (G 0)
  rw [← he] at hiter
  have hwD : (w : ℝ) = e * D := by linarith
  refine ⟨L, fun t => hL t, fun t => ?_⟩
  rw [hD t]
  have hDw : (D : ℝ) = e * w := by
    rcases hdeg with h | h <;> rw [h] at hwD ⊢ <;> push_cast at hwD ⊢ <;> linarith
  rw [hDw]

/-- **The winding homomorphism.**  A circle-valued map `f` induces an additive character of the
fundamental group, whose value on a conjugated loop `a · ℓ · a⁻¹` is the increment of any lift of
`f ∘ ℓ`. -/
theorem s78rb_winding_hom {X : Type*} [TopologicalSpace X] (f : C(X, AddCircle (1 : ℝ))) (x₀ : X) :
    ∃ ψ : Additive (FundamentalGroup X x₀) →+ ℝ, ∀ (y : X) (ℓ : Path y y) (a : Path x₀ y)
      (Λ : C(unitInterval, ℝ)), (∀ t, f (ℓ t) = (Λ t : AddCircle (1 : ℝ))) →
      ψ (Additive.ofMul (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm)))) = Λ 1 - Λ 0 := by
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let hp := AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)
  let cov := hp.isCoveringMap
  let p : C(ℝ, AddCircle (1 : ℝ)) := ⟨(↑), cov.continuous⟩
  obtain ⟨e₀, he₀⟩ := QuotientAddGroup.mk_surjective (f x₀)
  let e : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {f x₀} := ⟨e₀, he₀⟩
  let Φ := hp.fundamentalGroupToMulOpposite e
  let M := FundamentalGroup.map f x₀
  let val : FundamentalGroup X x₀ → ℝ := fun c => (((Φ (M c)).unop.toAdd : AddSubgroup.zmultiples (1 : ℝ)) : ℝ)
  have hval : ∀ c, val c + e₀ = (cov.monodromy (M c).asHom e).1 := by
    intro c
    have := hp.unop_fundamentalGroupToMulOpposite_smul (e := e) (γ := M c)
    rw [← this]
    rfl
  let ψ : Additive (FundamentalGroup X x₀) →+ ℝ :=
    { toFun := fun c => val (Additive.toMul c)
      map_zero' := by
        show val 1 = 0
        have h := hval 1
        have h1 : cov.monodromy (1 : FundamentalGroup (AddCircle (1 : ℝ)) (f x₀)).asHom e = e :=
          congrFun cov.monodromy_refl e
        rw [map_one, h1] at h
        show val 1 = 0
        linarith
      map_add' := fun c d => by
        show val (Additive.toMul c * Additive.toMul d) = val (Additive.toMul c) + val (Additive.toMul d)
        simp only [val, map_mul, MulOpposite.unop_mul, toAdd_mul, AddSubgroup.coe_add]
        ring }
  refine ⟨ψ, fun y ℓ a Λ hΛ => ?_⟩
  set c : FundamentalGroup X x₀ :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm)) with hc
  show val c = _
  set a' : Path (f x₀) (f y) := a.map f.continuous with ha'
  set ℓ' : Path (f y) (f y) := ℓ.map f.continuous with hℓ'
  have hMc : (M c).asHom = ((Path.Homotopic.Quotient.mk a').trans (Path.Homotopic.Quotient.mk ℓ')).trans
      (Path.Homotopic.Quotient.mk a').symm := by
    show Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm)) f = _
    rw [← Path.Homotopic.Quotient.mk_map, Path.map_trans, Path.map_trans, ← Path.map_symm,
      Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm]
  set D : ℝ := Λ 1 - Λ 0 with hDdef
  have hΛ0 : ((Λ 0 : ℝ) : AddCircle (1 : ℝ)) = f y := by rw [← hΛ 0, ℓ.source]
  have hΛ1 : ((Λ 1 : ℝ) : AddCircle (1 : ℝ)) = f y := by rw [← hΛ 1, ℓ.target]
  have hD0 : ((D : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [hDdef, AddCircle.coe_sub, hΛ0, hΛ1, sub_self]
  have hA0 : (a' : C(unitInterval, AddCircle (1 : ℝ))) 0 = ((e₀ : ℝ) : AddCircle (1 : ℝ)) := by
    show f (a 0) = _
    rw [a.source, he₀]
  let A := cov.liftPath (a' : C(unitInterval, AddCircle (1 : ℝ))) e₀ hA0
  set e1 := cov.monodromy (Path.Homotopic.Quotient.mk a') e with he1def
  have he1 : (e1 : ℝ) = A 1 := rfl
  have hAl : ∀ s, ((A s : ℝ) : AddCircle (1 : ℝ)) = a' s := fun s =>
    congrFun (cov.liftPath_lifts _ _ hA0) s
  have hA1 : ((A 1 : ℝ) : AddCircle (1 : ℝ)) = f y := by rw [hAl]; exact a'.target
  have hmemA : (((e1 : ℝ) + D : ℝ) : AddCircle (1 : ℝ)) = f y := by
    rw [AddCircle.coe_add, hD0, add_zero, he1, hA1]
  have hclaimA : cov.monodromy (Path.Homotopic.Quotient.mk ℓ') e1 = ⟨(e1 : ℝ) + D, hmemA⟩ := by
    let LP : Path (e1 : ℝ) ((e1 : ℝ) + D) :=
      { toFun := fun t => Λ t - Λ 0 + e1
        continuous_toFun := by fun_prop
        source' := by simp
        target' := by simp only [hDdef]; ring }
    apply cov.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk LP)
    rw [← Path.Homotopic.Quotient.mk_map]
    refine (congrArg Path.Homotopic.Quotient.mk ?_).trans (Path.Homotopic.Quotient.mk_cast ℓ' _ _)
    ext t
    show ((Λ t - Λ 0 + e1 : ℝ) : AddCircle (1 : ℝ)) = f (ℓ t)
    rw [AddCircle.coe_add, AddCircle.coe_sub, ← hΛ t, hΛ0, he1, hA1]
    abel
  have hmemB : ((e₀ + D : ℝ) : AddCircle (1 : ℝ)) = f x₀ := by
    rw [AddCircle.coe_add, hD0, add_zero, he₀]
  have hclaimB : cov.monodromy (Path.Homotopic.Quotient.mk a').symm ⟨(e1 : ℝ) + D, hmemA⟩ =
      ⟨e₀ + D, hmemB⟩ := by
    let Ap : Path e₀ (e1 : ℝ) :=
      { toFun := A
        continuous_toFun := A.continuous
        source' := cov.liftPath_zero _ _ hA0
        target' := he1.symm }
    let τ : C(ℝ, ℝ) := ⟨fun x => x + D, by fun_prop⟩
    apply cov.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk ((Ap.map τ.continuous).symm))
    rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_symm]
    refine (congrArg Path.Homotopic.Quotient.mk ?_).trans (Path.Homotopic.Quotient.mk_cast a'.symm _ _)
    ext t
    show ((A (unitInterval.symm t) + D : ℝ) : AddCircle (1 : ℝ)) = a' (unitInterval.symm t)
    rw [AddCircle.coe_add, hD0, add_zero, hAl]
  have hfinal : ((cov.monodromy (M c).asHom e : ℝ)) = e₀ + D := by
    rw [hMc, cov.monodromy_trans_apply, cov.monodromy_trans_apply, ← he1def, hclaimA, hclaimB]
  have := hval c
  linarith


section core

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [ConnectedSpace S]
  {g n m : ℕ} (F : FiniteTypeStructure S g n m)

/-- **B1.**  The core is homeomorphic to one of the classification models. -/
theorem s78rb_core_classification :
    Nonempty (s31dt_Core F ≃ₜ SphereRepresentative) ∨
      ∃ p q : ℕ, ((1 ≤ p ∨ 1 ≤ q) ∧ Nonempty (s31dt_Core F ≃ₜ Quot (OrientableRel p q))) ∨
        (1 ≤ p ∧ Nonempty (s31dt_Core F ≃ₜ Quot (NonOrientableRel p q))) := by
  obtain ⟨c, hc⟩ := s31dt_core_C0_manifold F
  letI := c
  haveI := hc
  haveI := s31dt_core_compact F
  haveI := s31dt_core_connected F
  exact classification_of_surfaces (s31dt_Core F)

/-- **B4.**  Circle-valued maps on the core whose windings along the boundary loops are
`ε j (δ_{jk} − δ_{j0})`, `ε j = ±1`. -/
theorem s78rb_boundary_characters (hm : m ≠ 0)
    (β : Fin m → C(ℝ, s31dt_Core F))
    (hβper : ∀ j t, β j (t + 1) = β j t)
    (hβinj : ∀ j, InjOn (β j) (Ico 0 1))
    (hβrange : ∀ j, range (β j) = {x : s31dt_Core F | x.val ∈ frontier (F.D j)}) :
    ∃ (χ : Fin m → C(s31dt_Core F, AddCircle (1 : ℝ))) (ε : Fin m → ℤ),
      (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ k j, ∃ L : C(ℝ, ℝ), (∀ t, χ k (β j t) = (L t : AddCircle (1 : ℝ))) ∧
        ∀ t, L (t + 1) = L t + ε j * ((if j = k then 1 else 0) -
          (if j = ⟨0, Nat.pos_of_ne_zero hm⟩ then 1 else 0)) := by
  rcases s78rb_core_classification F with hS | ⟨p, q, ⟨hpq, hφ⟩ | ⟨hp, hφ⟩⟩
  · exact (s78rb_core_not_sphere F hm hS.some).elim
  · set φ := hφ.some
    obtain ⟨σ, hσ⟩ := s78rb_core_model_boundary_orientable F hm hpq φ
    exact s78rb_assembly hm φ
      (fun i t => Quot.mk _ (ClosedUnitDisc.bdyPtOfReal ((t - (3 * ((i : ℕ) : ℝ) + 2)) / (4 * p + 3 * q))))
      (fun i => continuous_quot_mk.comp
        (s78rb_bdyPt_continuous.comp ((continuous_id.sub continuous_const).div_const _)))
      (fun i => s78rb_hole_loop_orientable p q hpq i) σ _ hσ
      (fun w hw => s78rb_orientable_character p q w hw) β hβper hβinj hβrange
  · set φ := hφ.some
    obtain ⟨σ, hσ⟩ := s78rb_core_model_boundary_nonorientable F hm hp φ
    exact s78rb_assembly hm φ
      (fun i t => Quot.mk _ (ClosedUnitDisc.bdyPtOfReal ((t - (3 * ((i : ℕ) : ℝ) + 2)) / (2 * p + 3 * q))))
      (fun i => continuous_quot_mk.comp
        (s78rb_bdyPt_continuous.comp ((continuous_id.sub continuous_const).div_const _)))
      (fun i => s78rb_hole_loop_nonorientable p q hp i) σ _ hσ
      (fun w hw => s78rb_nonorientable_character p q w hw) β hβper hβinj hβrange

/-- A periodic loop covers its range already on `[0,1]`. -/
theorem s78rb_periodic_image_Icc {X : Type*} [TopologicalSpace X] (β : C(ℝ, X))
    (hper : ∀ t, β (t + 1) = β t) : β '' Icc 0 1 = range β := by
  have hβp : Function.Periodic β 1 := hper
  ext x
  constructor
  · rintro ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, ?_⟩
    have := hβp.int_mul (⌊t⌋) (Int.fract t)
    rw [mul_one, Int.fract_add_floor] at this
    exact this.symm

/-- Reference parametrization of the boundary circle `j` of the core. -/
theorem s78rb_reference_loop (j : Fin m) :
    ∃ β : C(ℝ, s31dt_Core F), (∀ t, β (t + 1) = β t) ∧ InjOn β (Ico 0 1) ∧
      range β = {x : s31dt_Core F | x.val ∈ frontier (F.D j)} := by
  obtain ⟨h⟩ := s31dt_boundary_circle_homeomorph F j
  let c : ℝ → Metric.sphere (0 : ℂ) 1 := fun t =>
    ⟨(Circle.exp (2 * Real.pi * t) : ℂ), mem_sphere_zero_iff_norm.2 (Circle.norm_coe _)⟩
  have hc : Continuous c :=
    ((continuous_subtype_val.comp (Circle.exp.continuous.comp
      (continuous_const.mul continuous_id)))).subtype_mk _
  refine ⟨⟨fun t => (h (c t)).val, continuous_subtype_val.comp (h.continuous.comp hc)⟩, ?_, ?_, ?_⟩
  · intro t
    show (h (c (t + 1))).val = (h (c t)).val
    have : c (t + 1) = c t := by
      apply Subtype.ext
      show ((Circle.exp (2 * Real.pi * (t + 1)) : ℂ)) = (Circle.exp (2 * Real.pi * t) : ℂ)
      rw [show 2 * Real.pi * (t + 1) = 2 * Real.pi * t + 2 * Real.pi by ring, Circle.exp_add_two_pi]
    rw [this]
  · intro t ht t' ht' hEq
    have h1 : c t = c t' := h.injective (Subtype.ext hEq)
    have h2 : Circle.exp (2 * Real.pi * t) = Circle.exp (2 * Real.pi * t') :=
      Circle.ext (congrArg Subtype.val h1)
    have hpi : 0 < Real.pi := Real.pi_pos
    have h3 := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by linarith)
      ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩ ⟨by nlinarith [ht'.1], by nlinarith [ht'.2]⟩ h2
    nlinarith
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (h (c t)).2
    · intro hx
      let y := h.symm ⟨x, hx⟩
      let z : Circle := ⟨y.1, y.2⟩
      obtain ⟨r, hr⟩ := Circle.exp_surjective z
      refine ⟨r / (2 * Real.pi), ?_⟩
      show (h (c (r / (2 * Real.pi)))).val = x
      have : c (r / (2 * Real.pi)) = y := by
        apply Subtype.ext
        show ((Circle.exp (2 * Real.pi * (r / (2 * Real.pi))) : ℂ)) = y.1
        rw [show 2 * Real.pi * (r / (2 * Real.pi)) = r by field_simp, hr]
      rw [this, Homeomorph.apply_symm_apply]

/-- **B5.**  Characters of the fundamental group of the core with prescribed values on the boundary
loops. -/
theorem s78rb_boundary_characters_pi1 (hm : m ≠ 0) (x₀ : s31dt_Core F) :
    ∃ ψ : Fin m → (Additive (FundamentalGroup (s31dt_Core F) x₀) →+ ℝ),
      ∀ (j : Fin m) (β : C(ℝ, s31dt_Core F)), (∀ t, β (t + 1) = β t) → InjOn β (Ico 0 1) →
        range β = {x : s31dt_Core F | x.val ∈ frontier (F.D j)} →
        ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          ∀ (k : Fin m) (ℓ : Path (β 0) (β 0)), (∀ t : unitInterval, ℓ t = β t) →
            ∀ a : Path x₀ (β 0),
              ψ k (Additive.ofMul (FundamentalGroup.fromPath
                (Path.Homotopic.Quotient.mk ((a.trans ℓ).trans a.symm)))) =
                ((ε * ((if j = k then 1 else 0) -
                  (if j = ⟨0, Nat.pos_of_ne_zero hm⟩ then 1 else 0)) : ℤ) : ℝ) := by
  choose β₀ hβ₀per hβ₀inj hβ₀range using s78rb_reference_loop F
  obtain ⟨χ, ε₀, hε₀, hwind⟩ := s78rb_boundary_characters F hm β₀ hβ₀per hβ₀inj hβ₀range
  choose ψ hψ using fun k => s78rb_winding_hom (χ k) x₀
  refine ⟨ψ, fun j β hper hinj hrange => ?_⟩
  have hp01 : β₀ j 0 = β₀ j 1 := by
    have := hβ₀per j 0
    rw [zero_add] at this
    exact this.symm
  obtain ⟨ε', hε', hgen⟩ := s78rb_arc_winding_gen β hper hinj (β₀ j) (β₀ j).continuous.continuousOn
    hp01 (hβ₀inj j) (by rw [s78rb_periodic_image_Icc _ (hβ₀per j), hβ₀range j, hrange])
  refine ⟨ε' * ε₀ j, ?_, fun k ℓ hℓ a => ?_⟩
  · rcases hε' with h | h <;> rcases hε₀ j with h' | h' <;> rw [h, h'] <;> norm_num
  · set w : ℤ := ε₀ j * ((if j = k then 1 else 0) - (if j = ⟨0, Nat.pos_of_ne_zero hm⟩ then 1 else 0)) with hw
    obtain ⟨L0, hL0, hL0per⟩ := hwind k j
    have hL01 : L0 1 = L0 0 + w := by
      have := hL0per 0
      rw [zero_add] at this
      rw [this, hw]
      push_cast
      ring
    obtain ⟨L, hL, hLper⟩ := hgen (χ k) L0 w L0.continuous.continuousOn hL01 (fun t _ => hL0 t)
    let Λ : C(unitInterval, ℝ) := L.comp ⟨Subtype.val, continuous_subtype_val⟩
    have hΛ : ∀ t : unitInterval, (χ k) (ℓ t) = (Λ t : AddCircle (1 : ℝ)) := by
      intro t
      rw [hℓ t]
      exact hL t
    rw [hψ k (β 0) ℓ a Λ hΛ]
    show L 1 - L 0 = _
    have := hLper 0
    rw [zero_add] at this
    rw [this, hw]
    push_cast
    ring

end core

end LiZhongQC
