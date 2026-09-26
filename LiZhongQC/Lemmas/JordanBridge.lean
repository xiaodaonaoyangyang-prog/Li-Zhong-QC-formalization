import LiZhongQC.Basic
import JordanCurveTheorem.JordanCurveTheoremStatement

/-!
# Bridge to the vendored Jordan curve theorem

The vendored library `JordanCurveTheorem` (epfl-lara, after T. C. Hales's HOL Light proof) proves

  `JordanCurveTheorem.jordan_curve_theorem : IsSimpleClosedCurve C →
     ∃ A B, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
       Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ A ∪ B ∪ C = univ`

for subsets `C` of `EuclideanSpace ℝ (Fin 2)`, where `IsSimpleClosedCurve C` means that `C` is
the image of a continuous `f : ℝ → ℝ²` on `[0, 1]`, injective on `[0, 1)`, with `f 0 = f 1`.

This file translates that statement to the conventions of the project (`Basic.lean`): a Jordan
curve is a set `toExt C ⊆ ℂ̄` which is the range of a continuous injection `Circle → ℂ̄`.

* `complexToE2 : ℂ ≃ₜ EuclideanSpace ℝ (Fin 2)` is the identification through the orthonormal
  basis `1, i` (an isometry);
* `isSimpleClosedCurve_image_of_isJordanCurve`: `IsJordanCurve (toExt C)` for `C ⊆ ℂ` gives
  `IsSimpleClosedCurve (complexToE2 '' C)`;
* `jordan_curve_theorem_complex`: the Jordan curve theorem in `ℂ`, in the form above;
* `jordan_curve_theorem_complex_bounded`: the same with the two pieces ordered as the bounded
  ("inside") and the unbounded ("outside") one;
* `card_connectedComponents_compl_eq_two_of_isJordanCurve`: `ℂ ∖ C` has exactly two connected
  components, in the `Nat.card (ConnectedComponents _) = 2` form used by `IsNConnected`.

The vendored theorem gives nothing about the frontiers of the two pieces (the statement
"`frontier A = frontier B = C`", HOL Light's `JORDAN_INSIDE_OUTSIDE`, is not part of Hales's
proof), nor about arcs not separating the plane; see the scoping notes in the session report.

This is a leaf: it imports only `LiZhongQC.Basic` and the statement file of the vendored library
(hence the whole library).  It is not registered in the root `LiZhongQC.lean`.
-/

open Topology Metric Filter Set Complex
open scoped Real

noncomputable section

namespace LiZhongQC

/-! ### The plane `ℂ` as `ℝ²` -/

/-- The identification of `ℂ` with the Euclidean plane `EuclideanSpace ℝ (Fin 2)` through the
orthonormal basis `1, i`, as a homeomorphism (it is in fact an isometry). -/
def complexToE2 : ℂ ≃ₜ EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph

theorem complexToE2_apply (z : ℂ) : complexToE2 z = Complex.orthonormalBasisOneI.repr z := rfl

/-! ### Jordan curves of `ℂ̄` lying in `ℂ` -/

/-- A Jordan curve `toExt C` of the extended plane lying in `ℂ` is the range of a continuous
injection `Circle → ℂ`. -/
theorem exists_circle_param_of_isJordanCurve_toExt {C : Set ℂ} (hC : IsJordanCurve (toExt C)) :
    ∃ γ : Circle → ℂ, Continuous γ ∧ Function.Injective γ ∧ range γ = C := by
  obtain ⟨γ, hγc, hγi, hγr⟩ := hC
  have hmem : ∀ w, ∃ z : ℂ, (z : ExtPlane) = γ w := by
    intro w
    have : γ w ∈ toExt C := by rw [← hγr]; exact mem_range_self w
    obtain ⟨z, -, hz⟩ := this
    exact ⟨z, hz⟩
  choose γ' hγ' using hmem
  have hcomp : OnePoint.some ∘ γ' = γ := funext hγ'
  refine ⟨γ', ?_, ?_, ?_⟩
  · rw [OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff, hcomp]
    exact hγc
  · intro w₁ w₂ h
    exact hγi (by rw [← hγ', ← hγ', h])
  · ext z
    constructor
    · rintro ⟨w, rfl⟩
      have : γ w ∈ toExt C := by rw [← hγr]; exact mem_range_self w
      obtain ⟨z', hz', hzz'⟩ := this
      rw [← hγ'] at hzz'
      exact OnePoint.coe_injective hzz' ▸ hz'
    · intro hz
      have : ((z : ℂ) : ExtPlane) ∈ range γ := by rw [hγr]; exact ⟨z, hz, rfl⟩
      obtain ⟨w, hw⟩ := this
      exact ⟨w, OnePoint.coe_injective (by rw [hγ', hw])⟩

/-- A Jordan curve of `ℂ̄` lying in `ℂ` is compact. -/
theorem isCompact_of_isJordanCurve_toExt {C : Set ℂ} (hC : IsJordanCurve (toExt C)) :
    IsCompact C := by
  obtain ⟨γ, hγc, -, hγr⟩ := exists_circle_param_of_isJordanCurve_toExt hC
  rw [← hγr]
  exact isCompact_range hγc

/-- **Bridge to the vendored library.**  If `toExt C` is a Jordan curve of the extended plane
(with `C ⊆ ℂ`), then `C`, transported to `ℝ²`, is a simple closed curve in the sense of the
vendored library: it is parametrized by `t ↦ γ (exp (2π i t))` on `[0, 1]`. -/
theorem isSimpleClosedCurve_image_of_isJordanCurve {C : Set ℂ} (hC : IsJordanCurve (toExt C)) :
    IsSimpleClosedCurve (complexToE2 '' C) := by
  obtain ⟨γ, hγc, hγi, hγr⟩ := exists_circle_param_of_isJordanCurve_toExt hC
  have h2π : (0 : ℝ) < 2 * π := by positivity
  refine ⟨fun t => complexToE2 (γ (Circle.exp (2 * π * t))), ?_, ?_, ?_, ?_⟩
  · -- the image of `[0, 1]` is `C`
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← hγr] at hz
      obtain ⟨w, rfl⟩ := hz
      by_cases hneg : 0 ≤ arg (w : ℂ)
      · refine ⟨arg (w : ℂ) / (2 * π), ⟨div_nonneg hneg h2π.le, ?_⟩, ?_⟩
        · rw [div_le_one h2π]
          linarith [arg_le_pi (w : ℂ), Real.pi_pos]
        · simp only [mul_div_cancel₀ _ h2π.ne', Circle.exp_arg]
      · push Not at hneg
        refine ⟨arg (w : ℂ) / (2 * π) + 1, ⟨?_, ?_⟩, ?_⟩
        · have : -1 / 2 < arg (w : ℂ) / (2 * π) := by
            rw [lt_div_iff₀ h2π]
            linarith [neg_pi_lt_arg (w : ℂ), Real.pi_pos]
          linarith
        · have : arg (w : ℂ) / (2 * π) < 0 := div_neg_of_neg_of_pos hneg h2π
          linarith
        · simp only [mul_add, mul_one, mul_div_cancel₀ _ h2π.ne', Circle.exp_add,
            Circle.exp_two_pi, Circle.exp_arg]
    · rintro ⟨t, -, rfl⟩
      exact ⟨γ (Circle.exp (2 * π * t)), by rw [← hγr]; exact mem_range_self _, rfl⟩
  · -- continuity
    exact complexToE2.continuous.comp
      (hγc.comp (Circle.exp.continuous.comp (continuous_const.mul continuous_id)))
  · -- injectivity on `[0, 1)`
    intro s hs t ht hst
    have h1 : Circle.exp (2 * π * s) = Circle.exp (2 * π * t) :=
      hγi (complexToE2.injective hst)
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.1 h1
    have hm' : s - t - m = 0 := by
      have h0 : 2 * π * (s - t - m) = 0 := by linarith
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h h2π.ne'
      · exact h
    have hm1 : (m : ℝ) < 1 := by linarith [hs.1, hs.2, ht.1, ht.2]
    have hm2 : (-1 : ℝ) < m := by linarith [hs.1, hs.2, ht.1, ht.2]
    have hm1' : m < 1 := by exact_mod_cast hm1
    have hm2' : -1 < m := by exact_mod_cast hm2
    have hm0 : m = 0 := by omega
    rw [hm0] at hm'
    simp at hm'
    linarith
  · -- closing up
    simp only [mul_zero, Circle.exp_zero, mul_one, Circle.exp_two_pi]

/-! ### The Jordan curve theorem in `ℂ` -/

/-- **The Jordan curve theorem in `ℂ`**, transported from the vendored library: if `toExt C` is a
Jordan curve of `ℂ̄` with `C ⊆ ℂ`, then `ℂ ∖ C` is the disjoint union of two open connected
sets. -/
theorem jordan_curve_theorem_complex {C : Set ℂ} (hC : IsJordanCurve (toExt C)) :
    ∃ A B : Set ℂ, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ A ∪ B ∪ C = univ := by
  obtain ⟨A', B', hA', hB', hAc', hBc', hAB', hAC', hBC', huniv'⟩ :=
    JordanCurveTheorem.jordan_curve_theorem (isSimpleClosedCurve_image_of_isJordanCurve hC)
  refine ⟨complexToE2 ⁻¹' A', complexToE2 ⁻¹' B', hA'.preimage complexToE2.continuous,
    hB'.preimage complexToE2.continuous, complexToE2.isConnected_preimage.2 hAc',
    complexToE2.isConnected_preimage.2 hBc', hAB'.preimage _, ?_, ?_, ?_⟩
  · have h := hAC'.preimage complexToE2
    rwa [preimage_image_eq C complexToE2.injective] at h
  · have h := hBC'.preimage complexToE2
    rwa [preimage_image_eq C complexToE2.injective] at h
  · have h := congrArg (fun S => complexToE2 ⁻¹' S) huniv'
    simpa only [preimage_union, preimage_image_eq C complexToE2.injective, preimage_univ] using h

/-- The exterior `{r < ‖z‖}` of a disc is preconnected (polar coordinates). -/
theorem isPreconnected_setOf_lt_norm {r : ℝ} (hr : 0 ≤ r) :
    IsPreconnected {z : ℂ | r < ‖z‖} := by
  have hmap : (fun p : ℝ × ℝ => (p.1 : ℂ) * exp ((p.2 : ℂ) * I)) '' (Ioi r ×ˢ univ)
      = {z : ℂ | r < ‖z‖} := by
    apply Subset.antisymm
    · rintro _ ⟨⟨ρ, θ⟩, ⟨hρ, -⟩, rfl⟩
      show r < ‖(ρ : ℂ) * exp ((θ : ℂ) * I)‖
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hr.trans (le_of_lt hρ))]
      exact hρ
    · intro z hz
      exact ⟨(‖z‖, arg z), ⟨hz, mem_univ _⟩, Complex.norm_mul_exp_arg_mul_I z⟩
  rw [← hmap]
  exact (isPreconnected_Ioi.prod isPreconnected_univ).image _
    (Continuous.continuousOn (by fun_prop))

/-- **Inside and outside.**  The two complementary pieces of a Jordan curve in `ℂ` can be taken
as a bounded one and an unbounded one. -/
theorem jordan_curve_theorem_complex_bounded {C : Set ℂ} (hC : IsJordanCurve (toExt C)) :
    ∃ A B : Set ℂ, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧ A ∪ B ∪ C = univ ∧
      Bornology.IsBounded A ∧ ¬ Bornology.IsBounded B := by
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hAC, hBC, huniv⟩ := jordan_curve_theorem_complex hC
  obtain ⟨r, hr⟩ := isBounded_iff_subset_closedBall (0 : ℂ) |>.1
    (isCompact_of_isJordanCurve_toExt hC).isBounded
  -- the exterior of the disc of radius `max r 0` lies in `A ∪ B` and is preconnected
  set R : ℝ := max r 0 with hR
  have hR0 : 0 ≤ R := le_max_right _ _
  have hext : {z : ℂ | R < ‖z‖} ⊆ A ∪ B := by
    intro z hz
    have hzC : z ∉ C := fun h => by
      have := mem_closedBall_zero_iff.1 (hr h)
      have : r ≤ R := le_max_left _ _
      simp only [mem_setOf_eq] at hz
      linarith
    have : z ∈ A ∪ B ∪ C := huniv ▸ mem_univ z
    rcases this with h | h
    · exact h
    · exact absurd h hzC
  have hdisj : {z : ℂ | R < ‖z‖} ∩ (A ∩ B) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨-, hzA, hzB⟩
    exact Set.disjoint_left.1 hAB hzA hzB
  -- a piece containing the exterior is unbounded, the other one is bounded
  have key : ∀ U V : Set ℂ, Disjoint U V → {z : ℂ | R < ‖z‖} ⊆ V →
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V := by
    intro U V hUV hV
    constructor
    · refine (isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun z hz => ?_
      rw [mem_closedBall_zero_iff]
      by_contra hcon
      push Not at hcon
      exact Set.disjoint_left.1 hUV hz (hV hcon)
    · intro hVb
      obtain ⟨R', hR'⟩ := isBounded_iff_subset_closedBall (0 : ℂ) |>.1 hVb
      have hmem : ((max R R' + 1 : ℝ) : ℂ) ∈ V := by
        apply hV
        simp only [mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (by linarith [le_max_left R R'])]
        linarith [le_max_left R R']
      have := mem_closedBall_zero_iff.1 (hR' hmem)
      simp only [Complex.norm_real, Real.norm_eq_abs] at this
      rw [abs_of_nonneg (by linarith [le_max_left R R'])] at this
      linarith [le_max_right R R']
  rcases (isPreconnected_iff_subset_of_disjoint.1 (isPreconnected_setOf_lt_norm hR0)) A B hA hB
    hext hdisj with h | h
  · obtain ⟨hBb, hAb⟩ := key B A hAB.symm h
    exact ⟨B, A, hB, hA, hBc, hAc, hAB.symm, hBC, hAC, by rw [← huniv, union_comm A B], hBb, hAb⟩
  · obtain ⟨hAb, hBb⟩ := key A B hAB h
    exact ⟨A, B, hA, hB, hAc, hBc, hAB, hAC, hBC, huniv, hAb, hBb⟩

/-! ### Counting the components -/

/-- If a set `S` is the disjoint union of two open connected sets, then `S` has exactly two
connected components. -/
theorem card_connectedComponents_eq_two_of_union {X : Type*} [TopologicalSpace X]
    {S A B : Set X} (hA : IsOpen A) (hB : IsOpen B) (hAc : IsConnected A) (hBc : IsConnected B)
    (hAB : Disjoint A B) (hS : S = A ∪ B) : Nat.card (ConnectedComponents ↥S) = 2 := by
  subst hS
  have hAsub : A ⊆ A ∪ B := subset_union_left
  have hBsub : B ⊆ A ∪ B := subset_union_right
  -- the preimages of `A` and `B` in the subtype are complementary, open and preconnected
  have hAo : IsOpen (Subtype.val ⁻¹' A : Set ↥(A ∪ B)) := hA.preimage continuous_subtype_val
  have hBo : IsOpen (Subtype.val ⁻¹' B : Set ↥(A ∪ B)) := hB.preimage continuous_subtype_val
  have hcompl : (Subtype.val ⁻¹' A : Set ↥(A ∪ B))ᶜ = Subtype.val ⁻¹' B := by
    ext ⟨x, hx⟩
    simp only [mem_compl_iff, mem_preimage]
    rcases hx with hxA | hxB
    · exact ⟨fun h => absurd hxA h, fun hxB => absurd hxB (Set.disjoint_left.1 hAB hxA)⟩
    · exact ⟨fun _ => hxB, fun _ hxA => Set.disjoint_left.1 hAB hxA hxB⟩
  have hAclopen : IsClopen (Subtype.val ⁻¹' A : Set ↥(A ∪ B)) :=
    ⟨by rw [← isOpen_compl_iff, hcompl]; exact hBo, hAo⟩
  have hBclopen : IsClopen (Subtype.val ⁻¹' B : Set ↥(A ∪ B)) :=
    ⟨by rw [← isOpen_compl_iff, ← hcompl, compl_compl]; exact hAo, hBo⟩
  have hApre : IsPreconnected (Subtype.val ⁻¹' A : Set ↥(A ∪ B)) := by
    rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.2 hAsub]
    exact hAc.isPreconnected
  have hBpre : IsPreconnected (Subtype.val ⁻¹' B : Set ↥(A ∪ B)) := by
    rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.2 hBsub]
    exact hBc.isPreconnected
  -- the connected components are exactly these two sets
  have hcompA : ∀ x : ↥(A ∪ B), (x : X) ∈ A → connectedComponent x = Subtype.val ⁻¹' A :=
    fun x hx =>
      Subset.antisymm (hAclopen.connectedComponent_subset hx) (hApre.subset_connectedComponent hx)
  have hcompB : ∀ x : ↥(A ∪ B), (x : X) ∈ B → connectedComponent x = Subtype.val ⁻¹' B :=
    fun x hx =>
      Subset.antisymm (hBclopen.connectedComponent_subset hx) (hBpre.subset_connectedComponent hx)
  obtain ⟨a, ha⟩ := hAc.nonempty
  obtain ⟨b, hb⟩ := hBc.nonempty
  rw [Nat.card_eq_two_iff]
  refine ⟨ConnectedComponents.mk ⟨a, hAsub ha⟩, ConnectedComponents.mk ⟨b, hBsub hb⟩, ?_, ?_⟩
  · intro h
    rw [ConnectedComponents.coe_eq_coe, hcompA _ ha, hcompB _ hb] at h
    have hbA : (⟨b, hBsub hb⟩ : ↥(A ∪ B)) ∈ Subtype.val ⁻¹' A := by
      rw [h]; exact hb
    exact Set.disjoint_left.1 hAB hbA hb
  · ext c
    simp only [mem_insert_iff, mem_singleton_iff, mem_univ, iff_true]
    obtain ⟨⟨x, hx⟩, rfl⟩ := ConnectedComponents.surjective_coe c
    rcases hx with hxA | hxB
    · left
      rw [ConnectedComponents.coe_eq_coe, hcompA _ hxA, hcompA _ ha]
    · right
      rw [ConnectedComponents.coe_eq_coe, hcompB _ hxB, hcompB _ hb]

/-- **A Jordan curve in `ℂ` has exactly two complementary components**, in the form used by
`IsNConnected`. -/
theorem card_connectedComponents_compl_eq_two_of_isJordanCurve {C : Set ℂ}
    (hC : IsJordanCurve (toExt C)) : Nat.card (ConnectedComponents ↥Cᶜ) = 2 := by
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hAC, hBC, huniv⟩ := jordan_curve_theorem_complex hC
  refine card_connectedComponents_eq_two_of_union hA hB hAc hBc hAB ?_
  ext z
  constructor
  · intro hz
    have : z ∈ A ∪ B ∪ C := huniv ▸ mem_univ z
    rcases this with h | h
    · exact h
    · exact absurd h hz
  · rintro (h | h)
    · exact Set.disjoint_left.1 hAC h
    · exact Set.disjoint_left.1 hBC h

/-! ### Bounded Jordan domains -/

/-- **A bounded Jordan domain is the inside of its boundary curve.**  If `Ω ⊆ ℂ` is open,
connected and bounded and its frontier (in `ℂ`) is a Jordan curve, then `ℂ ∖ closure Ω` is
connected and unbounded: `Ω` is the bounded complementary component of `∂Ω` and `ℂ ∖ closure Ω`
the unbounded one.  (For `IsJordanDomain Ω`, whose curve is `frontier (toExt Ω)`, use
`frontier_toExt_of_isBounded` of `Lemmas/Quadrilateral.lean` to pass to `toExt (frontier Ω)`.)

Route: `Ω` is connected and misses `∂Ω`, so it lies in one of the two pieces `A` (bounded) or
`B` (unbounded) given by `jordan_curve_theorem_complex_bounded`; a piece containing `Ω` is
covered by the disjoint open sets `Ω` and `ℂ ∖ closure Ω`, hence equals `Ω` by connectedness, so
it is the bounded piece `A`, and then `B = ℂ ∖ closure Ω`. -/
theorem isConnected_compl_closure_of_isJordanCurve_frontier {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hΩc : IsConnected Ω) (hb : Bornology.IsBounded Ω) (hJ : IsJordanCurve (toExt (frontier Ω))) :
    IsConnected (closure Ω)ᶜ ∧ ¬ Bornology.IsBounded (closure Ω)ᶜ := by
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hAC, hBC, huniv, hAb, hBb⟩ :=
    jordan_curve_theorem_complex_bounded hJ
  have hcl : closure Ω = Ω ∪ frontier Ω := by
    rw [closure_eq_interior_union_frontier, hΩ.interior_eq]
  have hΩfr : Disjoint Ω (frontier Ω) := by
    rw [hΩ.frontier_eq]
    exact Set.disjoint_sdiff_right
  have hΩsub : Ω ⊆ A ∪ B := by
    intro z hz
    have : z ∈ A ∪ B ∪ frontier Ω := huniv ▸ mem_univ z
    rcases this with h | h
    · exact h
    · exact absurd h (Set.disjoint_left.1 hΩfr hz)
  -- a connected open set containing `Ω` and missing `∂Ω` is `Ω`
  have key : ∀ U : Set ℂ, IsOpen U → IsConnected U → Disjoint U (frontier Ω) → Ω ⊆ U →
      U = Ω := by
    intro U hU hUc hUf hΩU
    refine Subset.antisymm ?_ hΩU
    have hcover : U ⊆ Ω ∪ (closure Ω)ᶜ := by
      intro z hz
      by_cases h : z ∈ closure Ω
      · rw [hcl] at h
        rcases h with h | h
        · exact Or.inl h
        · exact absurd h (Set.disjoint_left.1 hUf hz)
      · exact Or.inr h
    have hdisj : U ∩ (Ω ∩ (closure Ω)ᶜ) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨-, hzΩ, hzc⟩
      exact hzc (subset_closure hzΩ)
    rcases (isPreconnected_iff_subset_of_disjoint.1 hUc.isPreconnected) _ _ hΩ
      isClosed_closure.isOpen_compl hcover hdisj with h | h
    · exact h
    · exfalso
      obtain ⟨z, hz⟩ := hΩc.nonempty
      exact h (hΩU hz) (subset_closure hz)
  rcases (isPreconnected_iff_subset_of_disjoint.1 hΩc.isPreconnected) A B hA hB hΩsub
    (by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨-, hzA, hzB⟩
      exact Set.disjoint_left.1 hAB hzA hzB) with h | h
  · -- `Ω ⊆ A`, so `A = Ω` and `B = ℂ ∖ closure Ω`
    have hAΩ : A = Ω := key A hA hAc hAC h
    have hBeq : B = (closure Ω)ᶜ := by
      ext z
      constructor
      · intro hz hcl'
        rw [hcl] at hcl'
        rcases hcl' with h1 | h1
        · exact Set.disjoint_left.1 hAB (hAΩ ▸ h1) hz
        · exact Set.disjoint_left.1 hBC hz h1
      · intro hz
        have : z ∈ A ∪ B ∪ frontier Ω := huniv ▸ mem_univ z
        rcases this with (h1 | h1) | h1
        · exact absurd (subset_closure (hAΩ ▸ h1)) hz
        · exact h1
        · exact absurd (frontier_subset_closure h1) hz
    rw [← hBeq]
    exact ⟨hBc, hBb⟩
  · -- `Ω ⊆ B` would make the unbounded piece equal to the bounded set `Ω`
    exfalso
    apply hBb
    rw [key B hB hBc hBC h]
    exact hb

end LiZhongQC
