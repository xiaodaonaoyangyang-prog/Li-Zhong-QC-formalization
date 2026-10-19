import LiZhongExternal.Classification.SchottkyClassification01
import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Boundary rank, B2 (ii)(B): Euclidean neighbourhoods of glued-edge interior points

In the quotients of the closed disc by `OrientableRel p n` and `NonOrientableRel p n`, every point
in the interior of a glued edge (not a vertex) has an open neighbourhood homeomorphic to the plane.
The proof glues two polar half-chart neighbourhoods of the closed disc along their boundary arcs.
-/

open Set Function Topology Complex
open scoped Real
open scoped Real

namespace LiZhongQC

/-- The open square `(-1,1)²` is homeomorphic to the Euclidean plane. -/
theorem s78rb_square_homeo_plane :
    Nonempty (↥(Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
  let eI : Ioo (-1 : ℝ) 1 ≃ₜ ℝ := (orderIsoIooNegOneOne ℝ).symm.toHomeomorph
  let e1 : ↥(Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1) ≃ₜ (Ioo (-1 : ℝ) 1 × Ioo (-1 : ℝ) 1) :=
    Homeomorph.Set.prod _ _
  let e2 : (Ioo (-1 : ℝ) 1 × Ioo (-1 : ℝ) 1) ≃ₜ (ℝ × ℝ) := eI.prodCongr eI
  let e3 : EuclideanSpace ℝ (Fin 2) ≃ₜ (Fin 2 → ℝ) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph
  let e4 : (Fin 2 → ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.finTwoArrow
  exact ⟨(e1.trans e2).trans ((e3.trans e4).symm)⟩

/-- Abstract gluing lemma: two half-chart neighbourhoods `V₁`, `V₂` whose boundaries are identified
by the relation `R` give an open neighbourhood in `Quot R` homeomorphic to the plane. -/
theorem s78rb_glue_chart {Y : Type*} [TopologicalSpace Y] (R : Y → Y → Prop)
    (V₁ V₂ : Set Y) (c₁ c₂ : Y → ℝ × ℝ) (g₁ g₂ : ℝ × ℝ → Y)
    (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂) (hdisj : Disjoint V₁ V₂)
    (hc₁ : ContinuousOn c₁ V₁) (hc₂ : ContinuousOn c₂ V₂)
    (hg₁ : ContinuousOn g₁ (Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1))
    (hg₂ : ContinuousOn g₂ (Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1))
    (hmc₁ : MapsTo c₁ V₁ (Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1))
    (hmc₂ : MapsTo c₂ V₂ (Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1))
    (hmg₁ : MapsTo g₁ (Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) V₁)
    (hmg₂ : MapsTo g₂ (Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) V₂)
    (hl₁ : ∀ y ∈ V₁, g₁ (c₁ y) = y) (hl₂ : ∀ y ∈ V₂, g₂ (c₂ y) = y)
    (hr₁ : ∀ p ∈ Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1, c₁ (g₁ p) = p)
    (hr₂ : ∀ p ∈ Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1, c₂ (g₂ p) = p)
    (hsat : ∀ y y', R y y' → (y ∈ V₁ ∪ V₂ ↔ y' ∈ V₁ ∪ V₂))
    (hrel₁ : ∀ y y', R y y' → y ∈ V₁ → y' ∈ V₂ ∧ c₂ y' = c₁ y ∧ (c₁ y).2 = 0)
    (hrel₂ : ∀ y y', R y y' → y ∈ V₂ → y' ∈ V₁ ∧ c₁ y' = c₂ y ∧ (c₂ y).2 = 0)
    (hglue : ∀ s ∈ Ioo (-1 : ℝ) 1, Quot.mk R (g₁ (s, 0)) = Quot.mk R (g₂ (s, 0))) :
    ∃ U : Set (Quot R), IsOpen U ∧ Quot.mk R (g₁ (0, 0)) ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
  classical
  set B : Set (ℝ × ℝ) := Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1 with hB
  set V : Set Y := V₁ ∪ V₂ with hV
  -- the glued chart
  let F : Y → ℝ × ℝ := fun y => if y ∈ V₁ then c₁ y else ((c₂ y).1, -(c₂ y).2)
  have hFV₁ : ∀ y ∈ V₁, F y = c₁ y := fun y hy => if_pos hy
  have hFV₂ : ∀ y ∈ V₂, F y = ((c₂ y).1, -(c₂ y).2) := fun y hy =>
    if_neg (fun h => (Set.disjoint_left.mp hdisj h hy))
  -- invariance of the class
  have hQ : ∀ a b, Relation.EqvGen R a b → ((a ∈ V ↔ b ∈ V) ∧ (a ∈ V → F a = F b)) := by
    intro a b h
    induction h with
    | rel x y hxy =>
      refine ⟨hsat x y hxy, fun hx => ?_⟩
      rcases hx with hx | hx
      · obtain ⟨hy, hc, h0⟩ := hrel₁ x y hxy hx
        rw [hFV₁ x hx, hFV₂ y hy, hc]
        ext
        · rfl
        · simp [h0]
      · obtain ⟨hy, hc, h0⟩ := hrel₂ x y hxy hx
        rw [hFV₂ x hx, hFV₁ y hy, hc]
        ext
        · rfl
        · simp [h0]
    | refl x => exact ⟨Iff.rfl, fun _ => rfl⟩
    | symm x y _ ih =>
      exact ⟨ih.1.symm, fun hy => (ih.2 (ih.1.mpr hy)).symm⟩
    | trans x y z _ _ ih1 ih2 =>
      exact ⟨ih1.1.trans ih2.1, fun hx => (ih1.2 hx).trans (ih2.2 (ih1.1.mp hx))⟩
  let F' : Y → ℝ × ℝ := fun y => if y ∈ V then F y else (0, 0)
  have hF'R : ∀ a b, R a b → F' a = F' b := by
    intro a b hab
    have h := hQ a b (Relation.EqvGen.rel a b hab)
    by_cases ha : a ∈ V
    · have hb : b ∈ V := h.1.mp ha
      simp only [F', if_pos ha, if_pos hb]
      exact h.2 ha
    · have hb : b ∉ V := fun hb => ha (h.1.mpr hb)
      simp only [F', if_neg ha, if_neg hb]
  let f : Quot R → ℝ × ℝ := Quot.lift F' hF'R
  have hfmk : ∀ y, f (Quot.mk R y) = F' y := fun y => rfl
  -- the open set
  set U : Set (Quot R) := Quot.mk R '' V with hU
  have hpre : Quot.mk R ⁻¹' U = V := by
    ext y
    constructor
    · rintro ⟨y', hy', hyy'⟩
      have := hQ y' y (Quot.eqvGen_exact hyy')
      exact this.1.mp hy'
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hVopen : IsOpen V := hV₁.union hV₂
  have hUopen : IsOpen U := by
    rw [← isQuotientMap_quot_mk.isOpen_preimage, hpre]
    exact hVopen
  -- F is continuous on V
  have hFcont : ContinuousOn F V := by
    refine ContinuousOn.union_of_isOpen ?_ ?_ hV₁ hV₂
    · exact hc₁.congr (fun y hy => hFV₁ y hy)
    · exact ((continuous_fst.comp_continuousOn hc₂).prodMk
        ((continuous_neg.comp_continuousOn (continuous_snd.comp_continuousOn hc₂)))).congr
        (fun y hy => hFV₂ y hy)
  have hF'cont : ContinuousOn F' V :=
    hFcont.congr (fun y hy => by simp only [F', if_pos hy])
  have hfcontU : ContinuousOn f U := by
    have hq := isQuotientMap_quot_mk (r := R)
    have hqU := hq.restrictPreimage_isOpen hUopen
    rw [continuousOn_iff_continuous_restrict]
    rw [hqU.continuous_iff]
    have hF'cont' : ContinuousOn F' (Quot.mk R ⁻¹' U) := by
      rw [hpre]; exact hF'cont
    exact continuousOn_iff_continuous_restrict.mp hF'cont'
  -- the square
  set S : Set (ℝ × ℝ) := Ioo (-1 : ℝ) 1 ×ˢ Ioo (-1 : ℝ) 1 with hS
  have hBS : B ⊆ S := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    exact ⟨hs, ⟨by linarith [ht.1], ht.2⟩⟩
  let ginv : ℝ × ℝ → Quot R := fun p =>
    if 0 ≤ p.2 then Quot.mk R (g₁ p) else Quot.mk R (g₂ (p.1, -p.2))
  have hV₁V : V₁ ⊆ V := subset_union_left
  have hV₂V : V₂ ⊆ V := subset_union_right
  have hfU : ∀ u ∈ U, f u ∈ S := by
    rintro u ⟨y, hy, rfl⟩
    rw [hfmk]
    simp only [F', if_pos hy]
    rcases hy with hy | hy
    · rw [hFV₁ y hy]; exact hBS (hmc₁ hy)
    · rw [hFV₂ y hy]
      obtain ⟨h1, h2⟩ := hmc₂ hy
      exact ⟨h1, ⟨by linarith [h2.2], by linarith [h2.1]⟩⟩
  have hginvU : ∀ p ∈ S, ginv p ∈ U := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    by_cases h0 : 0 ≤ t
    · have : ginv (s, t) = Quot.mk R (g₁ (s, t)) := if_pos h0
      rw [this]
      exact ⟨g₁ (s, t), hV₁V (hmg₁ ⟨hs, ⟨h0, ht.2⟩⟩), rfl⟩
    · have : ginv (s, t) = Quot.mk R (g₂ (s, -t)) := if_neg h0
      rw [this]
      push_neg at h0
      exact ⟨g₂ (s, -t), hV₂V (hmg₂ ⟨hs, ⟨by linarith, by linarith [ht.1]⟩⟩), rfl⟩
  have hleft : ∀ u ∈ U, ginv (f u) = u := by
    rintro u ⟨y, hy, rfl⟩
    rw [hfmk]
    simp only [F', if_pos hy]
    rcases hy with hy | hy
    · rw [hFV₁ y hy]
      have h0 : 0 ≤ (c₁ y).2 := (hmc₁ hy).2.1
      have : ginv (c₁ y) = Quot.mk R (g₁ (c₁ y)) := if_pos h0
      rw [this, hl₁ y hy]
    · have hy1 : y ∉ V₁ := fun h => Set.disjoint_left.mp hdisj h hy
      rw [hFV₂ y hy]
      rcases hc : c₂ y with ⟨s, t⟩
      have hB2 := hmc₂ hy
      rw [hc] at hB2
      obtain ⟨hs, ht⟩ := hB2
      have hyy : g₂ (s, t) = y := by rw [← hc]; exact hl₂ y hy
      by_cases h0 : 0 ≤ -t
      · have ht0 : t = 0 := by linarith [ht.1]
        have : ginv (s, -t) = Quot.mk R (g₁ (s, -t)) := if_pos h0
        rw [this, ht0, neg_zero, hglue s hs, ← hyy, ht0]
      · have : ginv (s, -t) = Quot.mk R (g₂ (s, - -t)) := if_neg h0
        rw [this, neg_neg, hyy]
  have hright : ∀ p ∈ S, f (ginv p) = p := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    by_cases h0 : 0 ≤ t
    · have : ginv (s, t) = Quot.mk R (g₁ (s, t)) := if_pos h0
      rw [this, hfmk]
      have hp : g₁ (s, t) ∈ V₁ := hmg₁ ⟨hs, ⟨h0, ht.2⟩⟩
      simp only [F', if_pos (hV₁V hp)]
      rw [hFV₁ _ hp, hr₁ _ ⟨hs, ⟨h0, ht.2⟩⟩]
    · have : ginv (s, t) = Quot.mk R (g₂ (s, -t)) := if_neg h0
      rw [this, hfmk]
      push_neg at h0
      have hB' : (s, -t) ∈ B := ⟨hs, ⟨by linarith, by linarith [ht.1]⟩⟩
      have hp : g₂ (s, -t) ∈ V₂ := hmg₂ hB'
      simp only [F', if_pos (hV₂V hp)]
      rw [hFV₂ _ hp, hr₂ _ hB']
      simp
  have hginvcont : ContinuousOn ginv S := by
    show ContinuousOn (fun p : ℝ × ℝ =>
      if 0 ≤ p.2 then Quot.mk R (g₁ p) else Quot.mk R (g₂ (p.1, -p.2))) S
    refine ContinuousOn.if (p := fun p : ℝ × ℝ => 0 ≤ p.2) ?_ ?_ ?_
    · rintro ⟨s, t⟩ ⟨⟨hs, ht⟩, hfr⟩
      have hfr' : t = 0 := by
        have := frontier_le_subset_eq (continuous_const (y := (0 : ℝ))) continuous_snd hfr
        simpa using this.symm
      subst hfr'
      simp only [neg_zero]
      exact hglue s hs
    · have hcl : closure {a : ℝ × ℝ | 0 ≤ a.2} = {a : ℝ × ℝ | 0 ≤ a.2} :=
        (isClosed_le continuous_const continuous_snd).closure_eq
      rw [hcl]
      refine continuous_quot_mk.comp_continuousOn (hg₁.mono ?_)
      rintro ⟨s, t⟩ ⟨⟨hs, ht⟩, h0⟩
      exact ⟨hs, ⟨h0, ht.2⟩⟩
    · have hcl : closure {a : ℝ × ℝ | ¬ 0 ≤ a.2} ⊆ {a : ℝ × ℝ | a.2 ≤ 0} := by
        have := closure_lt_subset_le (continuous_snd (X := ℝ) (Y := ℝ))
          (continuous_const (y := (0 : ℝ)))
        simpa [not_le] using this
      have hcont2 : ContinuousOn (fun p : ℝ × ℝ => g₂ (p.1, -p.2)) (S ∩ closure {a : ℝ × ℝ | ¬ 0 ≤ a.2}) := by
        refine hg₂.comp (continuous_fst.prodMk continuous_snd.neg).continuousOn ?_
        rintro ⟨s, t⟩ ⟨⟨hs, ht⟩, hcl'⟩
        have := hcl hcl'
        exact ⟨hs, ⟨by simp at this ⊢; linarith, by simp; linarith [ht.1]⟩⟩
      exact continuous_quot_mk.comp_continuousOn hcont2
  let e : ↥U ≃ₜ ↥S :=
    { toFun := fun u => ⟨f u.1, hfU u.1 u.2⟩
      invFun := fun p => ⟨ginv p.1, hginvU p.1 p.2⟩
      left_inv := fun u => Subtype.ext (hleft u.1 u.2)
      right_inv := fun p => Subtype.ext (hright p.1 p.2)
      continuous_toFun :=
        Continuous.subtype_mk (continuousOn_iff_continuous_restrict.mp hfcontU) _
      continuous_invFun :=
        Continuous.subtype_mk (continuousOn_iff_continuous_restrict.mp hginvcont) _ }
  obtain ⟨eP⟩ := s78rb_square_homeo_plane
  refine ⟨U, hUopen, ⟨g₁ (0, 0), hV₁V (hmg₁ ⟨⟨by norm_num, by norm_num⟩, ⟨le_refl _, by norm_num⟩⟩), rfl⟩, ⟨e.trans eP⟩⟩


theorem s78rb_arg_real_mul_exp (m θ : ℝ) (hm : 0 < m) (hθ : θ ∈ Ioc (-π) π) :
    Complex.arg ((m : ℂ) * Complex.exp (θ * Complex.I)) = θ := by
  rw [Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I]
  exact (toIocMod_eq_self _).2 ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩

/-- Polar half-chart of the closed unit disc around the boundary point `exp (2π i r0)`: the open
set `V` of points with norm `> 1 - δ` and angle within `2πρ` of `2π r0`, charted onto
`(-1,1) × [0,1)` with the boundary corresponding to `t = 0`. -/
theorem s78rb_disc_chart (r0 ρ δ ε : ℝ) (hρ : 0 < ρ) (hρ2 : ρ < 1 / 2) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : ε = 1 ∨ ε = -1) :
    ∃ (V : Set ClosedUnitDisc) (c : ClosedUnitDisc → ℝ × ℝ) (g : ℝ × ℝ → ClosedUnitDisc),
      IsOpen V ∧ ContinuousOn c V ∧
      ContinuousOn g (Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) ∧
      MapsTo c V (Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) ∧
      MapsTo g (Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) V ∧
      (∀ y ∈ V, g (c y) = y) ∧ (∀ p ∈ Ioo (-1 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1, c (g p) = p) ∧
      (∀ s : ℝ, g (s, 0) = ClosedUnitDisc.bdyPtOfReal (r0 + ε * ρ * s)) ∧
      (∀ y ∈ V, (c y).2 = 0 ↔ ‖(y : ℂ)‖ = 1) ∧
      (∀ y ∈ V, ∃ a ∈ Ioo (r0 - ρ) (r0 + ρ),
        (y : ℂ) = ((‖(y : ℂ)‖ : ℝ) : ℂ) * Complex.exp (((2 * π * a : ℝ) : ℂ) * Complex.I)) ∧
      (∀ y ∈ V, 1 - δ < ‖(y : ℂ)‖) := by
  classical
  have hπ := Real.pi_pos
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεa : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have h2πρ : 0 < 2 * π * ρ := by positivity
  have h2πρπ : 2 * π * ρ < π := by nlinarith
  set ω : ℂ := Complex.exp (((-(2 * π * r0) : ℝ) : ℂ) * Complex.I) with hω
  have hωn : ‖ω‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  set A : ClosedUnitDisc → ℝ := fun y => Complex.arg ((y : ℂ) * ω) with hA
  set V : Set ClosedUnitDisc := {y | 1 - δ < ‖(y : ℂ)‖ ∧ |A y| < 2 * π * ρ} with hV
  have hynorm : ∀ y : ClosedUnitDisc, ‖(y : ℂ) * ω‖ = ‖(y : ℂ)‖ := fun y => by
    rw [norm_mul, hωn, mul_one]
  have hyle : ∀ y : ClosedUnitDisc, ‖(y : ℂ)‖ ≤ 1 := fun y => mem_closedBall_zero_iff.mp y.2
  have hdec : ∀ y : ClosedUnitDisc, (y : ℂ) =
      ((‖(y : ℂ)‖ : ℝ) : ℂ) * Complex.exp (((A y + 2 * π * r0 : ℝ) : ℂ) * Complex.I) := by
    intro y
    have h1 := Complex.norm_mul_exp_arg_mul_I ((y : ℂ) * ω)
    rw [hynorm] at h1
    have h2 : (y : ℂ) = ((y : ℂ) * ω) * Complex.exp (((2 * π * r0 : ℝ) : ℂ) * Complex.I) := by
      rw [mul_assoc, hω, ← Complex.exp_add]
      have : ((-(2 * π * r0) : ℝ) : ℂ) * Complex.I + ((2 * π * r0 : ℝ) : ℂ) * Complex.I = 0 := by
        push_cast; ring
      rw [this, Complex.exp_zero, mul_one]
    calc (y : ℂ) = ((y : ℂ) * ω) * Complex.exp (((2 * π * r0 : ℝ) : ℂ) * Complex.I) := h2
      _ = ((‖(y : ℂ)‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg ((y : ℂ) * ω) : ℝ) * Complex.I) *
            Complex.exp (((2 * π * r0 : ℝ) : ℂ) * Complex.I) := by rw [h1]
      _ = ((‖(y : ℂ)‖ : ℝ) : ℂ) * Complex.exp (((A y + 2 * π * r0 : ℝ) : ℂ) * Complex.I) := by
        rw [mul_assoc, ← Complex.exp_add]
        congr 2
        simp only [hA]
        push_cast
        ring
  have hAcont : ∀ y : ClosedUnitDisc, y ∈ V → ContinuousAt A y := by
    intro y hy
    have hy0 : (y : ℂ) * ω ≠ 0 := by
      intro h
      have := hynorm y
      rw [h, norm_zero] at this
      linarith [hy.1]
    have hslit : (y : ℂ) * ω ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff_arg]
      refine ⟨?_, hy0⟩
      intro h
      have : |A y| < π := lt_trans hy.2 h2πρπ
      have h' : A y = π := h
      rw [h', abs_of_pos hπ] at this
      exact lt_irrefl _ this
    exact ContinuousAt.comp (g := Complex.arg) (f := fun y : ClosedUnitDisc => (y : ℂ) * ω)
      (x := y) (Complex.continuousAt_arg hslit)
      (Continuous.continuousAt (continuous_subtype_val.mul continuous_const))
  have hnormc : Continuous (fun y : ClosedUnitDisc => ‖(y : ℂ)‖) :=
    continuous_norm.comp continuous_subtype_val
  have hVopen : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hev : ∀ᶠ y' in 𝓝 y, |A y'| < 2 * π * ρ :=
      (continuous_abs.continuousAt.comp (hAcont y hy)).eventually_lt continuousAt_const hy.2
    have hev2 : ∀ᶠ y' : ClosedUnitDisc in 𝓝 y, 1 - δ < ‖(y' : ℂ)‖ :=
      ContinuousAt.eventually_lt (f := fun _ => 1 - δ)
        (g := fun y' : ClosedUnitDisc => ‖(y' : ℂ)‖) continuousAt_const hnormc.continuousAt hy.1
    exact hev2.and hev
  have hcont : ∀ y ∈ V, ContinuousAt (fun y : ClosedUnitDisc =>
      (ε * A y / (2 * π * ρ), (1 - ‖(y : ℂ)‖) / δ)) y := by
    intro y hy
    refine ContinuousAt.prodMk ?_ ?_
    · exact (continuousAt_const.mul (hAcont y hy)).div_const _
    · exact (continuousAt_const.sub hnormc.continuousAt).div_const _
  have hcA : ∀ y ∈ V, |ε * A y / (2 * π * ρ)| < 1 := by
    intro y hy
    rw [abs_div, abs_mul, hεa, one_mul, abs_of_pos h2πρ]
    exact (div_lt_one h2πρ).2 hy.2
  have hct : ∀ y ∈ V, (1 - ‖(y : ℂ)‖) / δ ∈ Ico (0 : ℝ) 1 := by
    intro y hy
    refine ⟨div_nonneg (by linarith [hyle y]) hδ.le, (div_lt_one hδ).2 (by linarith [hy.1])⟩
  -- the inverse chart
  let tcl : ℝ → ℝ := fun t => max 0 (min t 1)
  have htcl0 : ∀ t, 0 ≤ tcl t := fun t => le_max_left _ _
  have htcl1 : ∀ t, tcl t ≤ 1 := fun t => max_le (by norm_num) (min_le_right _ _)
  have htclid : ∀ t, 0 ≤ t → t ≤ 1 → tcl t = t := by
    intro t h0 h1
    simp only [tcl, min_eq_left h1, max_eq_right h0]
  have htclc : Continuous tcl := continuous_const.max (continuous_id.min continuous_const)
  let G : ℝ × ℝ → ℂ := fun p => ((1 - δ * tcl p.2 : ℝ) : ℂ) *
    Complex.exp (((2 * π * r0 + ε * (2 * π * ρ) * p.1 : ℝ) : ℂ) * Complex.I)
  have hGpos : ∀ p : ℝ × ℝ, 0 < 1 - δ * tcl p.2 := fun p => by
    nlinarith [htcl0 p.2, htcl1 p.2]
  have hGnorm : ∀ p : ℝ × ℝ, ‖G p‖ = 1 - δ * tcl p.2 := by
    intro p
    simp only [G]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (hGpos p).le]
  have hGle : ∀ p : ℝ × ℝ, ‖G p‖ ≤ 1 := fun p => by
    rw [hGnorm]; nlinarith [htcl0 p.2, htcl1 p.2]
  have hGc : Continuous G := by
    simp only [G]
    fun_prop
  let g : ℝ × ℝ → ClosedUnitDisc := fun p => ⟨G p, mem_closedBall_zero_iff.2 (hGle p)⟩
  have hgval : ∀ p, ((g p : ClosedUnitDisc) : ℂ) = G p := fun p => rfl
  -- argument of G p * ω
  have hGarg : ∀ p : ℝ × ℝ, |p.1| < 1 → A (g p) = ε * (2 * π * ρ) * p.1 := by
    intro p hp
    have hGω : (g p : ℂ) * ω = ((1 - δ * tcl p.2 : ℝ) : ℂ) *
        Complex.exp (((ε * (2 * π * ρ) * p.1 : ℝ) : ℂ) * Complex.I) := by
      rw [hgval]
      simp only [G, hω]
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    show Complex.arg ((g p : ℂ) * ω) = _
    rw [hGω]
    refine s78rb_arg_real_mul_exp _ _ (hGpos p) ⟨?_, ?_⟩
    · have : |ε * (2 * π * ρ) * p.1| < π := by
        rw [abs_mul, abs_mul, hεa, one_mul, abs_of_pos h2πρ]
        nlinarith [abs_nonneg p.1]
      linarith [(abs_lt.mp this).1]
    · have : |ε * (2 * π * ρ) * p.1| < π := by
        rw [abs_mul, abs_mul, hεa, one_mul, abs_of_pos h2πρ]
        nlinarith [abs_nonneg p.1]
      linarith [(abs_lt.mp this).2]
  refine ⟨V, fun y => (ε * A y / (2 * π * ρ), (1 - ‖(y : ℂ)‖) / δ), g, hVopen, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun y hy => (hcont y hy).continuousWithinAt
  · exact (Continuous.subtype_mk hGc _).continuousOn
  · intro y hy
    exact ⟨abs_lt.mp (hcA y hy), hct y hy⟩
  · rintro ⟨s, t⟩ ⟨hs, ht⟩
    have hs' : |s| < 1 := abs_lt.2 hs
    have hn : ‖(g (s, t) : ℂ)‖ = 1 - δ * t := by
      rw [hgval, hGnorm]
      simp only [htclid t ht.1 ht.2.le]
    refine ⟨?_, ?_⟩
    · rw [hn]
      nlinarith [ht.2]
    · rw [hGarg (s, t) hs']
      show |ε * (2 * π * ρ) * s| < 2 * π * ρ
      rw [abs_mul, abs_mul, hεa, one_mul, abs_of_pos h2πρ]
      nlinarith
  · intro y hy
    apply Subtype.ext
    rw [hgval]
    have ht := hct y hy
    have htc : tcl ((1 - ‖(y : ℂ)‖) / δ) = (1 - ‖(y : ℂ)‖) / δ := htclid _ ht.1 ht.2.le
    have hδne : δ ≠ 0 := hδ.ne'
    have h1 : 1 - δ * tcl ((1 - ‖(y : ℂ)‖) / δ) = ‖(y : ℂ)‖ := by
      rw [htc]; field_simp; ring
    have h2 : 2 * π * r0 + ε * (2 * π * ρ) * (ε * A y / (2 * π * ρ)) = A y + 2 * π * r0 := by
      rw [show ε * (2 * π * ρ) * (ε * A y / (2 * π * ρ)) = (ε * ε) * A y by field_simp, hε2]
      ring
    conv_rhs => rw [hdec y]
    simp only [G]
    rw [h1, h2]
  · rintro ⟨s, t⟩ ⟨hs, ht⟩
    have hs' : |s| < 1 := abs_lt.2 hs
    have hn : ‖(g (s, t) : ℂ)‖ = 1 - δ * t := by
      rw [hgval, hGnorm]
      simp only [htclid t ht.1 ht.2.le]
    show (ε * A (g (s, t)) / (2 * π * ρ), (1 - ‖(g (s, t) : ℂ)‖) / δ) = (s, t)
    rw [hGarg (s, t) hs', hn]
    ext
    · show ε * (ε * (2 * π * ρ) * s) / (2 * π * ρ) = s
      rw [show ε * (ε * (2 * π * ρ) * s) / (2 * π * ρ) = (ε * ε) * s by field_simp, hε2, one_mul]
    · show (1 - (1 - δ * t)) / δ = t
      field_simp
      ring
  · intro s
    apply Subtype.ext
    rw [hgval]
    have htcl0' : tcl 0 = 0 := by simp [tcl]
    show G (s, 0) = ((Real.fourierChar (r0 + ε * ρ * s) : Circle) : ℂ)
    rw [Real.fourierChar_apply]
    simp only [G, htcl0', mul_zero, sub_zero, Complex.ofReal_one, one_mul]
    rw [show 2 * π * r0 + ε * (2 * π * ρ) * s = 2 * π * (r0 + ε * ρ * s) by ring]
  · intro y hy
    constructor
    · intro h
      have : 1 - ‖(y : ℂ)‖ = 0 := by
        have hδne : δ ≠ 0 := hδ.ne'
        rcases div_eq_zero_iff.mp h with h | h
        · exact h
        · exact absurd h hδne
      linarith
    · intro h
      show (1 - ‖(y : ℂ)‖) / δ = 0
      rw [h]; simp
  · intro y hy
    refine ⟨r0 + A y / (2 * π), ⟨?_, ?_⟩, ?_⟩
    · have := (abs_lt.mp hy.2).1
      have : -ρ < A y / (2 * π) := by
        rw [lt_div_iff₀ (by positivity)]; nlinarith
      linarith
    · have := (abs_lt.mp hy.2).2
      have : A y / (2 * π) < ρ := by
        rw [div_lt_iff₀ (by positivity)]; nlinarith
      linarith
    · have h := hdec y
      have e : 2 * π * (r0 + A y / (2 * π)) = A y + 2 * π * r0 := by
        field_simp
        ring
      rw [e]
      exact h
  · intro y hy
    exact hy.1


/-! ## Part 3: circle arithmetic and the edge lemma -/

theorem s78rb_bdy_norm (r : ℝ) : ‖((ClosedUnitDisc.bdyPtOfReal r : ClosedUnitDisc) : ℂ)‖ = 1 := by
  show ‖((Real.fourierChar r : Circle) : ℂ)‖ = 1
  exact Circle.norm_coe _

theorem s78rb_bdy_coe (r : ℝ) :
    ((ClosedUnitDisc.bdyPtOfReal r : ClosedUnitDisc) : ℂ) =
      Complex.exp (((2 * π * r : ℝ) : ℂ) * Complex.I) := by
  show ((Real.fourierChar r : Circle) : ℂ) = _
  exact Real.fourierChar_apply r

theorem s78rb_bdy_eq_exists_int (a b : ℝ)
    (h : ClosedUnitDisc.bdyPtOfReal a = ClosedUnitDisc.bdyPtOfReal b) :
    ∃ n : ℤ, a = b + n := by
  have h1 := congrArg (fun z : ClosedUnitDisc => (z : ℂ)) h
  simp only [s78rb_bdy_coe] at h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  refine ⟨n, ?_⟩
  have h2 : (((a - b - n : ℝ) : ℂ)) * (2 * π * Complex.I) = 0 := by
    push_cast at hn ⊢
    linear_combination hn
  have hne : (2 * π * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have h3 : ((a - b - n : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · exact absurd h hne
  have h4 : a - b - n = 0 := by exact_mod_cast h3
  linarith

theorem s78rb_bdy_add_int (r : ℝ) (n : ℤ) :
    ClosedUnitDisc.bdyPtOfReal (r + n) = ClosedUnitDisc.bdyPtOfReal r := by
  apply Subtype.ext
  rw [s78rb_bdy_coe, s78rb_bdy_coe]
  have : ((2 * π * (r + n) : ℝ) : ℂ) * Complex.I =
      ((2 * π * r : ℝ) : ℂ) * Complex.I + n * (2 * π * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem s78rb_bdy_inj_N (N a b : ℝ) (hN : 0 < N) (ha0 : 0 ≤ a) (haN : a ≤ N) (hb0 : 0 < b)
    (hbN : b < N)
    (h : ClosedUnitDisc.bdyPtOfReal (a / N) = ClosedUnitDisc.bdyPtOfReal (b / N)) : a = b := by
  obtain ⟨n, hn⟩ := s78rb_bdy_eq_exists_int _ _ h
  have h1 : a = b + n * N := by
    have := hn
    field_simp at this
    linarith
  have h2 : (n : ℝ) < 1 := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have h3 : (-1 : ℝ) < n := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have h4 : n = 0 := by
    have : n < 1 := by exact_mod_cast h2
    have : -1 < n := by exact_mod_cast h3
    omega
  rw [h1, h4]
  simp

theorem s78rb_unit_arc (kF k : ℤ) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1)
    (h : (kF : ℝ) + τ ∈ Ioo (k : ℝ) (k + 1)) : kF = k := by
  have h1 : (kF : ℝ) < k + 1 := by linarith [h.2, hτ.1]
  have h2 : (k : ℝ) < kF + 1 := by linarith [h.1, hτ.2]
  have h1' : kF < k + 1 := by exact_mod_cast h1
  have h2' : k < kF + 1 := by exact_mod_cast h2
  omega

/-- Local Euclidean structure at the interior point of a glued edge. -/
theorem s78rb_edge_euclid (R : ClosedUnitDisc → ClosedUnitDisc → Prop) (N : ℝ) (hN : 0 < N)
    (k₁ k₂ : ℤ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hk₁ : 0 ≤ k₁) (hk₁N : (k₁ : ℝ) + 1 ≤ N)
    (hk₂ : 0 ≤ k₂) (hk₂N : (k₂ : ℝ) + 1 ≤ N) (hk12 : k₁ ≠ k₂) (φ0 ε : ℝ)
    (hφ : (ε = 1 ∧ φ0 = 0) ∨ (ε = -1 ∧ φ0 = 1))
    (hgen : ∀ y y', R y y' → ∃ (kF kG : ℤ) (τF τG : ℝ),
      y = ClosedUnitDisc.bdyPtOfReal ((kF + τF) / N) ∧
      y' = ClosedUnitDisc.bdyPtOfReal ((kG + τG) / N) ∧
      τF ∈ Icc (0 : ℝ) 1 ∧ τG ∈ Icc (0 : ℝ) 1 ∧
      0 ≤ kF ∧ (kF : ℝ) + 1 ≤ N ∧ 0 ≤ kG ∧ (kG : ℝ) + 1 ≤ N ∧
      (kF = k₁ → kG = k₂ ∧ τG = φ0 + ε * τF) ∧
      (kF = k₂ → kG = k₁ ∧ τG = φ0 + ε * τF) ∧
      (kG = k₁ → kF = k₂ ∧ τF = φ0 + ε * τG) ∧
      (kG = k₂ → kF = k₁ ∧ τF = φ0 + ε * τG))
    (hglue : ∀ τ ∈ Ioo (0 : ℝ) 1,
      Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((k₁ + τ) / N)) =
        Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((k₂ + (φ0 + ε * τ)) / N))) :
    ∃ U : Set (Quot R), IsOpen U ∧
      Quot.mk R (ClosedUnitDisc.bdyPtOfReal ((k₁ + x) / N)) ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
  have hπ := Real.pi_pos
  have hε : ε = 1 ∨ ε = -1 := by rcases hφ with h | h <;> [left; right] <;> exact h.1
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεa : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hN1 : 1 ≤ N := by
    have : (0 : ℝ) ≤ k₁ := by exact_mod_cast hk₁
    linarith
  obtain ⟨hx0, hx1⟩ := hx
  -- window size
  set w : ℝ := min x (1 - x) / 2 with hw
  have hw0 : 0 < w := by
    have : 0 < min x (1 - x) := lt_min hx0 (by linarith)
    linarith
  have hwx : w ≤ x / 2 := by
    have := min_le_left x (1 - x); linarith
  have hwx' : w ≤ (1 - x) / 2 := by
    have := min_le_right x (1 - x); linarith
  have hw4 : w ≤ 1 / 4 := by linarith
  set τ2 : ℝ := φ0 + ε * x with hτ2
  have hτ2w : w ≤ τ2 / 2 ∧ w ≤ (1 - τ2) / 2 := by
    rcases hφ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [hτ2]; constructor <;> linarith
    · simp only [hτ2]; constructor <;> linarith
  have hρ0 : 0 < w / N := div_pos hw0 hN
  have hρ2 : w / N < 1 / 2 := by
    rw [div_lt_iff₀ hN]; linarith
  set r1 : ℝ := (k₁ + x) / N with hr1
  set r2 : ℝ := (k₂ + τ2) / N with hr2
  obtain ⟨V₁, c₁, g₁, hV₁, hc₁, hg₁c, hmc₁, hmg₁, hl₁, hr₁, hD2₁, hD3₁, hD4₁, hD5₁⟩ :=
    s78rb_disc_chart r1 (w / N) (1 / 2) 1 hρ0 hρ2 (by norm_num) (by norm_num) (Or.inl rfl)
  obtain ⟨V₂, c₂, g₂, hV₂, hc₂, hg₂c, hmc₂, hmg₂, hl₂, hr₂, hD2₂, hD3₂, hD4₂, hD5₂⟩ :=
    s78rb_disc_chart r2 (w / N) (1 / 2) ε hρ0 hρ2 (by norm_num) (by norm_num) hε
  have hg₁s : ∀ s : ℝ, g₁ (s, 0) = ClosedUnitDisc.bdyPtOfReal ((k₁ + (x + w * s)) / N) := by
    intro s
    rw [hD2₁ s]
    congr 1
    simp only [hr1]
    field_simp
    ring
  have hg₂s : ∀ s : ℝ,
      g₂ (s, 0) = ClosedUnitDisc.bdyPtOfReal ((k₂ + (φ0 + ε * (x + w * s))) / N) := by
    intro s
    rw [hD2₂ s]
    congr 1
    simp only [hr2, hτ2]
    field_simp
    ring
  -- boundary points of a chart are determined by their real parameter
  have hside₁ : ∀ (kX : ℤ) (τX : ℝ) (y : ClosedUnitDisc), τX ∈ Icc (0 : ℝ) 1 → 0 ≤ kX →
      (kX : ℝ) + 1 ≤ N → y = ClosedUnitDisc.bdyPtOfReal ((kX + τX) / N) → y ∈ V₁ →
      ∃ s ∈ Ioo (-1 : ℝ) 1, kX = k₁ ∧ τX = x + w * s ∧ y = g₁ (s, 0) ∧ c₁ y = (s, 0) := by
    intro kX τX y hτX hkX hkXN hy hyV
    have hn1 : ‖(y : ℂ)‖ = 1 := by rw [hy]; exact s78rb_bdy_norm _
    have h0 : (c₁ y).2 = 0 := (hD3₁ y hyV).2 hn1
    have hB := hmc₁ hyV
    set s := (c₁ y).1 with hs
    have hcy : c₁ y = (s, 0) := Prod.ext rfl h0
    have hys : y = g₁ (s, 0) := by rw [← hcy]; exact (hl₁ y hyV).symm
    have hs1 : s ∈ Ioo (-1 : ℝ) 1 := hB.1
    have heq : ClosedUnitDisc.bdyPtOfReal ((kX + τX) / N) =
        ClosedUnitDisc.bdyPtOfReal ((k₁ + (x + w * s)) / N) :=
      hy.symm.trans (hys.trans (hg₁s s))
    have hkX0 : (0 : ℝ) ≤ kX := by exact_mod_cast hkX
    have hk1 : (0 : ℝ) ≤ k₁ := by exact_mod_cast hk₁
    have hb : (kX : ℝ) + τX = k₁ + (x + w * s) := by
      refine s78rb_bdy_inj_N N _ _ hN (by linarith [hτX.1]) (by linarith [hτX.2]) ?_ ?_ heq
      · nlinarith [hs1.1, hs1.2]
      · nlinarith [hs1.1, hs1.2]
    have hrange : (kX : ℝ) + τX ∈ Ioo (k₁ : ℝ) (k₁ + 1) := by
      rw [hb]
      constructor <;> nlinarith [hs1.1, hs1.2]
    have hkk : kX = k₁ := s78rb_unit_arc kX k₁ τX hτX hrange
    refine ⟨s, hs1, hkk, ?_, hys, hcy⟩
    rw [hkk] at hb
    linarith
  have hτ2val : ∀ s ∈ Ioo (-1 : ℝ) 1, φ0 + ε * (x + w * s) ∈ Ioo (0 : ℝ) 1 := by
    intro s hs1
    have h1 : |ε * (w * s)| < w := by
      have habs : |s| < 1 := abs_lt.2 hs1
      rw [abs_mul, abs_mul, hεa, one_mul, abs_of_pos hw0]
      nlinarith [mul_pos hw0 (sub_pos.2 habs)]
    have h2 := abs_lt.mp h1
    have h3 : φ0 + ε * (x + w * s) = τ2 + ε * (w * s) := by simp only [hτ2]; ring
    rw [h3]
    constructor <;> linarith [hτ2w.1, hτ2w.2, h2.1, h2.2]
  have hside₂ : ∀ (kX : ℤ) (τX : ℝ) (y : ClosedUnitDisc), τX ∈ Icc (0 : ℝ) 1 → 0 ≤ kX →
      (kX : ℝ) + 1 ≤ N → y = ClosedUnitDisc.bdyPtOfReal ((kX + τX) / N) → y ∈ V₂ →
      ∃ s ∈ Ioo (-1 : ℝ) 1, kX = k₂ ∧ τX = φ0 + ε * (x + w * s) ∧ y = g₂ (s, 0) ∧
        c₂ y = (s, 0) := by
    intro kX τX y hτX hkX hkXN hy hyV
    have hn1 : ‖(y : ℂ)‖ = 1 := by rw [hy]; exact s78rb_bdy_norm _
    have h0 : (c₂ y).2 = 0 := (hD3₂ y hyV).2 hn1
    have hB := hmc₂ hyV
    set s := (c₂ y).1 with hs
    have hcy : c₂ y = (s, 0) := Prod.ext rfl h0
    have hys : y = g₂ (s, 0) := by rw [← hcy]; exact (hl₂ y hyV).symm
    have hs1 : s ∈ Ioo (-1 : ℝ) 1 := hB.1
    have heq : ClosedUnitDisc.bdyPtOfReal ((kX + τX) / N) =
        ClosedUnitDisc.bdyPtOfReal ((k₂ + (φ0 + ε * (x + w * s))) / N) :=
      hy.symm.trans (hys.trans (hg₂s s))
    have hkX0 : (0 : ℝ) ≤ kX := by exact_mod_cast hkX
    have hk2 : (0 : ℝ) ≤ k₂ := by exact_mod_cast hk₂
    have hτv := hτ2val s hs1
    have hb : (kX : ℝ) + τX = k₂ + (φ0 + ε * (x + w * s)) := by
      refine s78rb_bdy_inj_N N _ _ hN (by linarith [hτX.1]) (by linarith [hτX.2]) ?_ ?_ heq
      · linarith [hτv.1]
      · linarith [hτv.2]
    have hrange : (kX : ℝ) + τX ∈ Ioo (k₂ : ℝ) (k₂ + 1) := by
      rw [hb]
      constructor <;> linarith [hτv.1, hτv.2]
    have hkk : kX = k₂ := s78rb_unit_arc kX k₂ τX hτX hrange
    refine ⟨s, hs1, hkk, ?_, hys, hcy⟩
    rw [hkk] at hb
    linarith
  -- the four transfer statements
  have hφinv : ∀ t : ℝ, φ0 + ε * (φ0 + ε * t) = t := by
    intro t
    rcases hφ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> ring
  have hmemg₁ : ∀ s ∈ Ioo (-1 : ℝ) 1, g₁ (s, 0) ∈ V₁ := fun s hs =>
    hmg₁ ⟨hs, ⟨le_refl _, by norm_num⟩⟩
  have hmemg₂ : ∀ s ∈ Ioo (-1 : ℝ) 1, g₂ (s, 0) ∈ V₂ := fun s hs =>
    hmg₂ ⟨hs, ⟨le_refl _, by norm_num⟩⟩
  have hcg₁ : ∀ s ∈ Ioo (-1 : ℝ) 1, c₁ (g₁ (s, 0)) = (s, 0) := fun s hs =>
    hr₁ _ ⟨hs, ⟨le_refl _, by norm_num⟩⟩
  have hcg₂ : ∀ s ∈ Ioo (-1 : ℝ) 1, c₂ (g₂ (s, 0)) = (s, 0) := fun s hs =>
    hr₂ _ ⟨hs, ⟨le_refl _, by norm_num⟩⟩
  have F1 : ∀ y y', R y y' → y ∈ V₁ → y' ∈ V₂ ∧ c₂ y' = c₁ y ∧ (c₁ y).2 = 0 := by
    intro y y' hR hy
    obtain ⟨kF, kG, τF, τG, hyF, hyG, hτF, hτG, hkF, hkFN, hkG, hkGN, c1, c2, c3, c4⟩ :=
      hgen y y' hR
    obtain ⟨s, hs, hk, hτ, hys, hcy⟩ := hside₁ kF τF y hτF hkF hkFN hyF hy
    obtain ⟨hkG', hτG'⟩ := c1 hk
    have hy' : y' = g₂ (s, 0) := by
      rw [hyG, hg₂s s, hkG', hτG', hτ]
    refine ⟨hy' ▸ hmemg₂ s hs, ?_, by rw [hcy]⟩
    rw [hy', hcg₂ s hs, hcy]
  have F2 : ∀ y y', R y y' → y ∈ V₂ → y' ∈ V₁ ∧ c₁ y' = c₂ y ∧ (c₂ y).2 = 0 := by
    intro y y' hR hy
    obtain ⟨kF, kG, τF, τG, hyF, hyG, hτF, hτG, hkF, hkFN, hkG, hkGN, c1, c2, c3, c4⟩ :=
      hgen y y' hR
    obtain ⟨s, hs, hk, hτ, hys, hcy⟩ := hside₂ kF τF y hτF hkF hkFN hyF hy
    obtain ⟨hkG', hτG'⟩ := c2 hk
    have hy' : y' = g₁ (s, 0) := by
      rw [hyG, hg₁s s, hkG', hτG', hτ, hφinv]
    refine ⟨hy' ▸ hmemg₁ s hs, ?_, by rw [hcy]⟩
    rw [hy', hcg₁ s hs, hcy]
  have F3 : ∀ y y', R y y' → y' ∈ V₁ → y ∈ V₂ := by
    intro y y' hR hy'
    obtain ⟨kF, kG, τF, τG, hyF, hyG, hτF, hτG, hkF, hkFN, hkG, hkGN, c1, c2, c3, c4⟩ :=
      hgen y y' hR
    obtain ⟨s, hs, hk, hτ, hys, hcy⟩ := hside₁ kG τG y' hτG hkG hkGN hyG hy'
    obtain ⟨hkF', hτF'⟩ := c3 hk
    have hy : y = g₂ (s, 0) := by
      rw [hyF, hg₂s s, hkF', hτF', hτ]
    exact hy ▸ hmemg₂ s hs
  have F4 : ∀ y y', R y y' → y' ∈ V₂ → y ∈ V₁ := by
    intro y y' hR hy'
    obtain ⟨kF, kG, τF, τG, hyF, hyG, hτF, hτG, hkF, hkFN, hkG, hkGN, c1, c2, c3, c4⟩ :=
      hgen y y' hR
    obtain ⟨s, hs, hk, hτ, hys, hcy⟩ := hside₂ kG τG y' hτG hkG hkGN hyG hy'
    obtain ⟨hkF', hτF'⟩ := c4 hk
    have hy : y = g₁ (s, 0) := by
      rw [hyF, hg₁s s, hkF', hτF', hτ, hφinv]
    exact hy ▸ hmemg₁ s hs
  -- disjointness of the two neighbourhoods
  have hdisj : Disjoint V₁ V₂ := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    obtain ⟨a, ha, hya⟩ := hD4₁ y hy1
    obtain ⟨b, hb, hyb⟩ := hD4₂ y hy2
    have hnorm : (0 : ℝ) < ‖(y : ℂ)‖ := by
      have := hD5₁ y hy1; norm_num at this; linarith
    have hexp : Complex.exp (((2 * π * a : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((2 * π * b : ℝ) : ℂ) * Complex.I) := by
      have h1 := hya.symm.trans hyb
      have hne : ((‖(y : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnorm.ne'
      exact mul_left_cancel₀ hne h1
    have hAB : ClosedUnitDisc.bdyPtOfReal a = ClosedUnitDisc.bdyPtOfReal b := by
      apply Subtype.ext
      rw [s78rb_bdy_coe, s78rb_bdy_coe]
      exact hexp
    obtain ⟨n, hn⟩ := s78rb_bdy_eq_exists_int a b hAB
    have hk1 : (0 : ℝ) ≤ k₁ := by exact_mod_cast hk₁
    have hk2 : (0 : ℝ) ≤ k₂ := by exact_mod_cast hk₂
    have hwN : w / N * N = w := by field_simp
    have e1 : r1 * N = k₁ + x := by simp only [hr1]; field_simp
    have e2 : r2 * N = k₂ + τ2 := by simp only [hr2]; field_simp
    have e3 : (r1 - w / N) * N = k₁ + x - w := by rw [sub_mul, e1, hwN]
    have e4 : (r1 + w / N) * N = k₁ + x + w := by rw [add_mul, e1, hwN]
    have e5 : (r2 - w / N) * N = k₂ + τ2 - w := by rw [sub_mul, e2, hwN]
    have e6 : (r2 + w / N) * N = k₂ + τ2 + w := by rw [add_mul, e2, hwN]
    have ha' : a * N ∈ Ioo ((k₁ : ℝ)) (k₁ + 1) := by
      obtain ⟨ha1, ha2⟩ := ha
      have h1 := mul_lt_mul_of_pos_right ha1 hN
      have h2 := mul_lt_mul_of_pos_right ha2 hN
      constructor <;> linarith [hwx, hwx']
    have hb' : b * N ∈ Ioo ((k₂ : ℝ)) (k₂ + 1) := by
      obtain ⟨hb1, hb2⟩ := hb
      have h1 := mul_lt_mul_of_pos_right hb1 hN
      have h2 := mul_lt_mul_of_pos_right hb2 hN
      constructor <;> linarith [hτ2w.1, hτ2w.2]
    have hkey : (n : ℝ) * N = a * N - b * N := by rw [hn]; ring
    have hn1 : (n : ℝ) < 1 := by
      by_contra hcon; push_neg at hcon
      have := mul_le_mul_of_nonneg_right hcon hN.le
      linarith [ha'.1, ha'.2, hb'.1, hb'.2]
    have hn2 : (-1 : ℝ) < n := by
      by_contra hcon; push_neg at hcon
      have := mul_le_mul_of_nonneg_right hcon hN.le
      linarith [ha'.1, ha'.2, hb'.1, hb'.2]
    have hn0 : n = 0 := by
      have h1 : n < 1 := by exact_mod_cast hn1
      have h2 : -1 < n := by exact_mod_cast hn2
      omega
    rw [hn0] at hn
    simp at hn
    have hab : a * N = b * N := by rw [hn]
    have h1 : (k₁ : ℝ) < k₂ + 1 := by linarith [ha'.1, hb'.2]
    have h2 : (k₂ : ℝ) < k₁ + 1 := by linarith [hb'.1, ha'.2]
    have h1' : k₁ < k₂ + 1 := by exact_mod_cast h1
    have h2' : k₂ < k₁ + 1 := by exact_mod_cast h2
    omega
  have hsat : ∀ y y', R y y' → (y ∈ V₁ ∪ V₂ ↔ y' ∈ V₁ ∪ V₂) := by
    intro y y' hR
    constructor
    · rintro (hy | hy)
      · exact Or.inr (F1 y y' hR hy).1
      · exact Or.inl (F2 y y' hR hy).1
    · rintro (hy | hy)
      · exact Or.inr (F3 y y' hR hy)
      · exact Or.inl (F4 y y' hR hy)
  have hglue' : ∀ s ∈ Ioo (-1 : ℝ) 1, Quot.mk R (g₁ (s, 0)) = Quot.mk R (g₂ (s, 0)) := by
    intro s hs
    rw [hg₁s s, hg₂s s]
    refine hglue (x + w * s) ⟨?_, ?_⟩
    · nlinarith [hs.1, hs.2]
    · nlinarith [hs.1, hs.2]
  obtain ⟨U, hU, hmem, hhomeo⟩ := s78rb_glue_chart R V₁ V₂ c₁ c₂ g₁ g₂ hV₁ hV₂ hdisj hc₁ hc₂
    hg₁c hg₂c hmc₁ hmc₂ hmg₁ hmg₂ hl₁ hl₂ hr₁ hr₂ hsat F1 F2 hglue'
  refine ⟨U, hU, ?_, hhomeo⟩
  have : g₁ (0, 0) = ClosedUnitDisc.bdyPtOfReal ((k₁ + x) / N) := by
    rw [hg₁s 0]; simp
  rw [← this]
  exact hmem


/-! ## Part 4: the two classification models -/

open LeanEval.Topology.ClassificationOfSurfaces

theorem s78rb_orientable_gen (p n : ℕ) (y y' : ClosedUnitDisc) (h : OrientableRel p n y y') :
    ∃ (kF kG : ℤ) (τF τG : ℝ),
      y = ClosedUnitDisc.bdyPtOfReal ((kF + τF) / (4 * p + 3 * n)) ∧
      y' = ClosedUnitDisc.bdyPtOfReal ((kG + τG) / (4 * p + 3 * n)) ∧
      τF ∈ Icc (0 : ℝ) 1 ∧ τG ∈ Icc (0 : ℝ) 1 ∧ τG = 1 - τF ∧
      ((∃ i : ℕ, i < p ∧ kF = 4 * i ∧ kG = 4 * i + 2) ∨
        (∃ i : ℕ, i < p ∧ kF = 4 * i + 1 ∧ kG = 4 * i + 3) ∨
        (∃ j : ℕ, j < n ∧ kF = 4 * p + 3 * n - 3 * j - 1 ∧ kG = 4 * p + 3 * n - 3 * j - 3)) := by
  cases h with
  | a x i =>
    refine ⟨4 * (i : ℕ), 4 * (i : ℕ) + 2, x, 1 - x, ?_, ?_, x.2, ?_, rfl,
      Or.inl ⟨i, i.2, rfl, rfl⟩⟩
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring
    · exact ⟨by linarith [x.2.2], by linarith [x.2.1]⟩
  | b x i =>
    refine ⟨4 * (i : ℕ) + 1, 4 * (i : ℕ) + 3, x, 1 - x, ?_, ?_, x.2, ?_, rfl,
      Or.inr (Or.inl ⟨i, i.2, rfl, rfl⟩)⟩
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring
    · exact ⟨by linarith [x.2.2], by linarith [x.2.1]⟩
  | c x j =>
    have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos j
    have hN : (0 : ℝ) < 4 * p + 3 * n := by positivity
    refine ⟨4 * (p : ℕ) + 3 * (n : ℕ) - 3 * (j : ℕ) - 1, 4 * (p : ℕ) + 3 * (n : ℕ) - 3 * (j : ℕ) - 3,
      1 - x, x, ?_, ?_, ⟨by linarith [x.2.2], by linarith [x.2.1]⟩, x.2, by ring,
      Or.inr (Or.inr ⟨j, j.2, rfl, rfl⟩)⟩
    · rw [← s78rb_bdy_add_int _ 1]
      congr 1
      push_cast
      field_simp
      ring
    · rw [← s78rb_bdy_add_int _ 1]
      congr 1
      push_cast
      field_simp
      ring

/-- Interior points of the glued edges of the orientable model, abstract form. -/
theorem s78rb_orientable_aux (p n : ℕ) (k₁ k₂ : ℤ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hcase : (∃ i : ℕ, i < p ∧ k₁ = 4 * i ∧ k₂ = 4 * i + 2) ∨
      (∃ i : ℕ, i < p ∧ k₁ = 4 * i + 1 ∧ k₂ = 4 * i + 3) ∨
      (∃ j : ℕ, j < n ∧ k₁ = 4 * p + 3 * n - 3 * j - 1 ∧ k₂ = 4 * p + 3 * n - 3 * j - 3)) :
    ∃ U : Set (Quot (OrientableRel p n)), IsOpen U ∧
      Quot.mk _ (ClosedUnitDisc.bdyPtOfReal ((k₁ + x) / (4 * p + 3 * n))) ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
  have hint : 0 ≤ k₁ ∧ k₁ + 1 ≤ 4 * (p : ℤ) + 3 * n ∧ 0 ≤ k₂ ∧ k₂ + 1 ≤ 4 * (p : ℤ) + 3 * n ∧
      k₁ ≠ k₂ ∧ 0 < 4 * (p : ℤ) + 3 * n := by
    rcases hcase with ⟨i, hi, h1, h2⟩ | ⟨i, hi, h1, h2⟩ | ⟨j, hj, h1, h2⟩ <;> omega
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hint
  have hN : (0 : ℝ) < 4 * p + 3 * n := by exact_mod_cast h6
  refine s78rb_edge_euclid (OrientableRel p n) (4 * p + 3 * n) hN k₁ k₂ x hx h1
    (by exact_mod_cast h2) h3 (by exact_mod_cast h4) h5 1 (-1) (Or.inr ⟨rfl, rfl⟩) ?_ ?_
  · intro y y' hR
    obtain ⟨kF, kG, τF, τG, hy, hy', hτF, hτG, hflip, hcls⟩ := s78rb_orientable_gen p n y y' hR
    have hk : (kF = k₁ → kG = k₂) ∧ (kF = k₂ → kG = k₁) ∧ (kG = k₁ → kF = k₂) ∧
        (kG = k₂ → kF = k₁) ∧ 0 ≤ kF ∧ kF + 1 ≤ 4 * (p : ℤ) + 3 * n ∧ 0 ≤ kG ∧
        kG + 1 ≤ 4 * (p : ℤ) + 3 * n := by
      rcases hcls with ⟨i, hi, e1, e2⟩ | ⟨i, hi, e1, e2⟩ | ⟨j, hj, e1, e2⟩ <;>
        rcases hcase with ⟨i', hi', f1, f2⟩ | ⟨i', hi', f1, f2⟩ | ⟨j', hj', f1, f2⟩ <;> omega
    obtain ⟨k1', k2', k3', k4', b1, b2, b3, b4⟩ := hk
    refine ⟨kF, kG, τF, τG, hy, hy', hτF, hτG, b1, by exact_mod_cast b2, b3,
      by exact_mod_cast b4, ?_, ?_, ?_, ?_⟩
    · exact fun h => ⟨k1' h, by rw [hflip]; ring⟩
    · exact fun h => ⟨k2' h, by rw [hflip]; ring⟩
    · exact fun h => ⟨k3' h, by rw [hflip]; ring⟩
    · exact fun h => ⟨k4' h, by rw [hflip]; ring⟩
  · intro τ hτ
    have hτ' : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1.le, hτ.2.le⟩
    rcases hcase with ⟨i, hi, e1, e2⟩ | ⟨i, hi, e1, e2⟩ | ⟨j, hj, e1, e2⟩
    · subst e1 e2
      have := Quot.sound (OrientableRel.a (p := p) (n := n) ⟨τ, hτ'⟩ ⟨i, hi⟩)
      convert this using 4 <;> push_cast <;> ring
    · subst e1 e2
      have := Quot.sound (OrientableRel.b (p := p) (n := n) ⟨τ, hτ'⟩ ⟨i, hi⟩)
      convert this using 4 <;> push_cast <;> ring
    · subst e1 e2
      have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hj)
      have hNN : (4 * (p : ℝ) + 3 * n) ≠ 0 := hN.ne'
      have := Quot.sound (OrientableRel.c (p := p) (n := n) ⟨1 - τ, ⟨by linarith [hτ.2], by linarith [hτ.1]⟩⟩
        ⟨j, hj⟩)
      rw [← s78rb_bdy_add_int _ 1, ← s78rb_bdy_add_int ((-(3 * (j : ℝ) + 3 - (1 - τ))) / _) 1] at this
      convert this using 4 <;> push_cast <;> field_simp <;> ring

theorem s78rb_euclid_orientable_edge (p n : ℕ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∀ i : Fin p, ∃ U : Set (Quot (OrientableRel p n)), IsOpen U ∧
      Quot.mk _ (ClosedUnitDisc.bdyPtOfReal ((4 * (i : ℝ) + x) / (4 * p + 3 * n))) ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))) ∧
    (∀ i : Fin p, ∃ U : Set (Quot (OrientableRel p n)), IsOpen U ∧
      Quot.mk _ (ClosedUnitDisc.bdyPtOfReal ((4 * (i : ℝ) + 1 + x) / (4 * p + 3 * n))) ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))) ∧
    (∀ j : Fin n, ∃ U : Set (Quot (OrientableRel p n)), IsOpen U ∧
      Quot.mk _ (ClosedUnitDisc.bdyPtOfReal (-(3 * (j : ℝ) + x) / (4 * p + 3 * n))) ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    obtain ⟨U, hU, hmem, hh⟩ := s78rb_orientable_aux p n (4 * (i : ℕ)) (4 * (i : ℕ) + 2) x hx
      (Or.inl ⟨i, i.2, rfl, rfl⟩)
    refine ⟨U, hU, ?_, hh⟩
    convert hmem using 3
    push_cast; ring
  · intro i
    obtain ⟨U, hU, hmem, hh⟩ := s78rb_orientable_aux p n (4 * (i : ℕ) + 1) (4 * (i : ℕ) + 3) x hx
      (Or.inr (Or.inl ⟨i, i.2, rfl, rfl⟩))
    refine ⟨U, hU, ?_, hh⟩
    convert hmem using 3
    push_cast; ring
  · intro j
    have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos j
    have hN : (0 : ℝ) < 4 * p + 3 * n := by positivity
    obtain ⟨U, hU, hmem, hh⟩ := s78rb_orientable_aux p n (4 * (p : ℕ) + 3 * (n : ℕ) - 3 * (j : ℕ) - 1)
      (4 * (p : ℕ) + 3 * (n : ℕ) - 3 * (j : ℕ) - 3) (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
      (Or.inr (Or.inr ⟨j, j.2, rfl, rfl⟩))
    refine ⟨U, hU, ?_, hh⟩
    have e : ClosedUnitDisc.bdyPtOfReal (-(3 * (j : ℝ) + x) / (4 * p + 3 * n)) =
        ClosedUnitDisc.bdyPtOfReal
          ((((4 * (p : ℕ) + 3 * (n : ℕ) - 3 * (j : ℕ) - 1 : ℤ) : ℝ) + (1 - x)) /
            (4 * p + 3 * n)) := by
      rw [← s78rb_bdy_add_int _ 1]
      congr 1
      push_cast
      field_simp
      ring
    rw [e]
    exact hmem


/-! ## Part 5: the non-orientable model -/

theorem s78rb_nonorientable_gen (p n : ℕ) (y y' : ClosedUnitDisc) (h : NonOrientableRel p n y y') :
    ∃ (kF kG : ℤ) (τF τG : ℝ),
      y = ClosedUnitDisc.bdyPtOfReal ((kF + τF) / (2 * p + 3 * n)) ∧
      y' = ClosedUnitDisc.bdyPtOfReal ((kG + τG) / (2 * p + 3 * n)) ∧
      τF ∈ Icc (0 : ℝ) 1 ∧ τG ∈ Icc (0 : ℝ) 1 ∧
      ((∃ i : ℕ, i < p ∧ kF = 2 * i ∧ kG = 2 * i + 1 ∧ τG = τF) ∨
        (∃ j : ℕ, j < n ∧ kF = 2 * p + 3 * n - 3 * j - 1 ∧ kG = 2 * p + 3 * n - 3 * j - 3 ∧
          τG = 1 - τF)) := by
  cases h with
  | a x i =>
    refine ⟨2 * (i : ℕ), 2 * (i : ℕ) + 1, x, x, ?_, ?_, x.2, x.2,
      Or.inl ⟨i, i.2, rfl, rfl, rfl⟩⟩
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring
  | c x j =>
    have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos j
    have hN : (0 : ℝ) < 2 * p + 3 * n := by positivity
    refine ⟨2 * (p : ℕ) + 3 * (n : ℕ) - 3 * (j : ℕ) - 1, 2 * (p : ℕ) + 3 * (n : ℕ) - 3 * (j : ℕ) - 3,
      1 - x, x, ?_, ?_, ⟨by linarith [x.2.2], by linarith [x.2.1]⟩, x.2,
      Or.inr ⟨j, j.2, rfl, rfl, by ring⟩⟩
    · rw [← s78rb_bdy_add_int _ 1]
      congr 1
      push_cast
      field_simp
      ring
    · rw [← s78rb_bdy_add_int _ 1]
      congr 1
      push_cast
      field_simp
      ring

/-- Interior points of the glued edges of the non-orientable model, abstract form. -/
theorem s78rb_nonorientable_aux (p n : ℕ) (k₁ k₂ : ℤ) (x φ0 ε : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1)
    (hcase : (∃ i : ℕ, i < p ∧ k₁ = 2 * i ∧ k₂ = 2 * i + 1 ∧ ε = 1 ∧ φ0 = 0) ∨
      (∃ j : ℕ, j < n ∧ k₁ = 2 * p + 3 * n - 3 * j - 1 ∧ k₂ = 2 * p + 3 * n - 3 * j - 3 ∧
        ε = -1 ∧ φ0 = 1)) :
    ∃ U : Set (Quot (NonOrientableRel p n)), IsOpen U ∧
      Quot.mk _ (ClosedUnitDisc.bdyPtOfReal ((k₁ + x) / (2 * p + 3 * n))) ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2)) := by
  have hint : 0 ≤ k₁ ∧ k₁ + 1 ≤ 2 * (p : ℤ) + 3 * n ∧ 0 ≤ k₂ ∧ k₂ + 1 ≤ 2 * (p : ℤ) + 3 * n ∧
      k₁ ≠ k₂ ∧ 0 < 2 * (p : ℤ) + 3 * n := by
    rcases hcase with ⟨i, hi, h1, h2, -, -⟩ | ⟨j, hj, h1, h2, -, -⟩ <;> omega
  have hφ : (ε = 1 ∧ φ0 = 0) ∨ (ε = -1 ∧ φ0 = 1) := by
    rcases hcase with ⟨i, hi, h1, h2, h3, h4⟩ | ⟨j, hj, h1, h2, h3, h4⟩
    · exact Or.inl ⟨h3, h4⟩
    · exact Or.inr ⟨h3, h4⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hint
  have hN : (0 : ℝ) < 2 * p + 3 * n := by exact_mod_cast h6
  refine s78rb_edge_euclid (NonOrientableRel p n) (2 * p + 3 * n) hN k₁ k₂ x hx h1
    (by exact_mod_cast h2) h3 (by exact_mod_cast h4) h5 φ0 ε hφ ?_ ?_
  · intro y y' hR
    obtain ⟨kF, kG, τF, τG, hy, hy', hτF, hτG, hcls⟩ := s78rb_nonorientable_gen p n y y' hR
    have hb : 0 ≤ kF ∧ kF + 1 ≤ 2 * (p : ℤ) + 3 * n ∧ 0 ≤ kG ∧ kG + 1 ≤ 2 * (p : ℤ) + 3 * n := by
      rcases hcls with ⟨i, hi, e1, e2, -⟩ | ⟨j, hj, e1, e2, -⟩ <;> omega
    obtain ⟨b1, b2, b3, b4⟩ := hb
    refine ⟨kF, kG, τF, τG, hy, hy', hτF, hτG, b1, by exact_mod_cast b2, b3,
      by exact_mod_cast b4, ?_, ?_, ?_, ?_⟩ <;>
    · intro h
      rcases hcls with ⟨i, hi, e1, e2, hτ⟩ | ⟨j, hj, e1, e2, hτ⟩ <;>
        rcases hcase with ⟨i', hi', f1, f2, hε1, hφ1⟩ | ⟨j', hj', f1, f2, hε1, hφ1⟩ <;>
        first
          | (exfalso; omega)
          | exact ⟨by omega, by rw [hτ, hε1, hφ1]; ring⟩
          | exact ⟨by omega, by rw [hε1, hφ1] at *; linarith⟩
  · intro τ hτ
    have hτ' : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1.le, hτ.2.le⟩
    rcases hcase with ⟨i, hi, e1, e2, hε1, hφ1⟩ | ⟨j, hj, e1, e2, hε1, hφ1⟩
    · subst e1 e2 hε1 hφ1
      have := Quot.sound (NonOrientableRel.a (p := p) (n := n) ⟨τ, hτ'⟩ ⟨i, hi⟩)
      convert this using 4 <;> push_cast <;> ring
    · subst e1 e2 hε1 hφ1
      have hn : (0 : ℝ) < n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hj)
      have hNN : (2 * (p : ℝ) + 3 * n) ≠ 0 := hN.ne'
      have := Quot.sound (NonOrientableRel.c (p := p) (n := n)
        ⟨1 - τ, ⟨by linarith [hτ.2], by linarith [hτ.1]⟩⟩ ⟨j, hj⟩)
      rw [← s78rb_bdy_add_int _ 1, ← s78rb_bdy_add_int ((-(3 * (j : ℝ) + 3 - (1 - τ))) / _) 1]
        at this
      convert this using 4 <;> push_cast <;> field_simp <;> ring

theorem s78rb_euclid_nonorientable_edge (p n : ℕ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∀ i : Fin p, ∃ U : Set (Quot (NonOrientableRel p n)), IsOpen U ∧
      Quot.mk _ (ClosedUnitDisc.bdyPtOfReal ((2 * (i : ℝ) + x) / (2 * p + 3 * n))) ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))) ∧
    (∀ j : Fin n, ∃ U : Set (Quot (NonOrientableRel p n)), IsOpen U ∧
      Quot.mk _ (ClosedUnitDisc.bdyPtOfReal (-(3 * (j : ℝ) + x) / (2 * p + 3 * n))) ∈ U ∧
      Nonempty (↥U ≃ₜ EuclideanSpace ℝ (Fin 2))) := by
  refine ⟨?_, ?_⟩
  · intro i
    obtain ⟨U, hU, hmem, hh⟩ := s78rb_nonorientable_aux p n (2 * (i : ℕ)) (2 * (i : ℕ) + 1) x 0 1 hx
      (Or.inl ⟨i, i.2, rfl, rfl, rfl, rfl⟩)
    refine ⟨U, hU, ?_, hh⟩
    convert hmem using 3
    push_cast; ring
  · intro j
    have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos j
    have hN : (0 : ℝ) < 2 * p + 3 * n := by positivity
    obtain ⟨U, hU, hmem, hh⟩ := s78rb_nonorientable_aux p n
      (2 * (p : ℕ) + 3 * (n : ℕ) - 3 * (j : ℕ) - 1)
      (2 * (p : ℕ) + 3 * (n : ℕ) - 3 * (j : ℕ) - 3) (1 - x) 1 (-1)
      ⟨by linarith [hx.2], by linarith [hx.1]⟩
      (Or.inr ⟨j, j.2, rfl, rfl, rfl, rfl⟩)
    refine ⟨U, hU, ?_, hh⟩
    have e : ClosedUnitDisc.bdyPtOfReal (-(3 * (j : ℝ) + x) / (2 * p + 3 * n)) =
        ClosedUnitDisc.bdyPtOfReal
          ((((2 * (p : ℕ) + 3 * (n : ℕ) - 3 * (j : ℕ) - 1 : ℤ) : ℝ) + (1 - x)) /
            (2 * p + 3 * n)) := by
      rw [← s78rb_bdy_add_int _ 1]
      congr 1
      push_cast
      field_simp
      ring
    rw [e]
    exact hmem

end LiZhongQC
