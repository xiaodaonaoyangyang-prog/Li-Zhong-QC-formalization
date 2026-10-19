import LiZhongQC.Lemmas.SchottkyClosedSurface1
import LiZhongQC.Lemmas.SchottkyCircleFundamental
import LiZhongQC.Lemmas.SchottkyPi1Deformation
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval

namespace LiZhongQC

/-- The overlap of the two charts is the image of the punctured open disc. -/
theorem s78dg_cs_overlap_range (p n : ℕ) :
    Set.range (fun z : {z : ClosedUnitDisc | 0 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < 1} =>
      (Quot.mk (OrientableRel p n) (z : ClosedUnitDisc))) =
      s78dg_cs_U p n ∩ s78dg_cs_V p n := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨⟨z, fun h => z.2.1.ne' (by rw [h, norm_zero]), rfl⟩, ⟨z, z.2.2, rfl⟩⟩
  · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have h := Quot.eqvGen_exact hxy
    rcases s78dg_cs_eqv_boundary h with h1 | h1
    · have hy' : ‖(y : ℂ)‖ < 1 := hy
      rw [h1] at hy'
      exact ⟨⟨x, ⟨norm_pos_iff.2 hx, hy'⟩⟩, rfl⟩
    · have hy' : ‖(y : ℂ)‖ < 1 := hy
      exact absurd h1.1 hy'.ne

/-- A homeomorphism induces a bijection on fundamental groups. -/
theorem s78dg_pi1_homeo_bijective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    Function.Bijective (FundamentalGroup.map (⟨e, e.continuous⟩ : C(X, Y)) x) := by
  let f : C(X, Y) := ⟨e, e.continuous⟩
  let g : C(Y, X) := ⟨e.symm, e.symm.continuous⟩
  have hri : ∀ y, g (f y) = y := fun y => e.symm_apply_apply y
  have hcomp : f.comp g = ContinuousMap.id Y := by
    ext y; exact e.apply_symm_apply y
  let H : ContinuousMap.Homotopy (ContinuousMap.id Y) (f.comp g) :=
    (ContinuousMap.Homotopy.refl (ContinuousMap.id Y)).cast rfl hcomp.symm
  exact s78dg_pi1_deformation_bijective f g hri H (fun y s => by simp [H]) x

/-- The punctured open unit disc deformation retracts onto the circle of radius `1/2`, so the
inclusion of the circle induces a bijection on fundamental groups. -/
theorem s78dg_punctured_disc_pi1 :
    ∃ i : C(AddCircle (1 : ℝ), {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}),
      (∀ t, ((i t : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}) : ℂ) =
        (1 / 2 : ℝ) • ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero t : Circle) : ℂ)) ∧
      Function.Bijective (FundamentalGroup.map i 0) := by
  let hc := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hnorm : ∀ t, ‖((hc t : Circle) : ℂ)‖ = 1 := fun t => by simp
  let i : C(AddCircle (1 : ℝ), {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}) :=
    ⟨fun t => ⟨(1 / 2 : ℝ) • ((hc t : Circle) : ℂ), by
      rw [norm_smul, hnorm]; norm_num⟩, by
      refine Continuous.subtype_mk ?_ _
      exact (continuous_const : Continuous fun _ : AddCircle (1 : ℝ) => (1 / 2 : ℝ)).smul
        (continuous_subtype_val.comp hc.continuous)⟩
  refine ⟨i, fun t => rfl, ?_⟩
  -- the retraction
  let ρ : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} → Circle := fun z =>
    ⟨(z : ℂ) / (‖(z : ℂ)‖ : ℂ), by
      have : ‖(z : ℂ)‖ ≠ 0 := z.2.1.ne'
      simp [Submonoid.unitSphere, this]⟩
  have hρ : Continuous ρ := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_subtype_val.div (Complex.continuous_ofReal.comp (continuous_norm.comp
      continuous_subtype_val)) (fun z => ?_)
    exact_mod_cast z.2.1.ne'
  let r : C({z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}, AddCircle (1 : ℝ)) := ⟨fun z => hc.symm (ρ z), hc.symm.continuous.comp hρ⟩
  have hri : ∀ t, r (i t) = t := by
    intro t
    change hc.symm (ρ (i t)) = t
    have : ρ (i t) = hc t := by
      apply Subtype.ext
      change ((1 / 2 : ℝ) • ((hc t : Circle) : ℂ)) / (‖(1 / 2 : ℝ) • ((hc t : Circle) : ℂ)‖ : ℂ) = _
      rw [norm_smul, hnorm, Real.norm_of_nonneg (by norm_num), mul_one, Complex.real_smul]
      push_cast
      field_simp
    rw [this]
    exact hc.symm_apply_apply t
  -- the homotopy
  let F : I × {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} → {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} := fun q =>
    ⟨(((1 - (q.1 : ℝ)) + (q.1 : ℝ) / (2 * ‖(q.2 : ℂ)‖) : ℝ)) • (q.2 : ℂ), by
      have h0 := q.2.2.1
      have h1 := q.2.2.2
      have hs0 : 0 ≤ (q.1 : ℝ) := q.1.2.1
      have hs1 : (q.1 : ℝ) ≤ 1 := q.1.2.2
      have hpos : 0 < (1 - (q.1 : ℝ)) + (q.1 : ℝ) / (2 * ‖(q.2 : ℂ)‖) := by
        have : 0 ≤ (q.1 : ℝ) / (2 * ‖(q.2 : ℂ)‖) := by positivity
        rcases eq_or_lt_of_le hs1 with h | h
        · have : 0 < (q.1 : ℝ) / (2 * ‖(q.2 : ℂ)‖) := by rw [h]; positivity
          linarith
        · linarith
      have hval : ((1 - (q.1 : ℝ)) + (q.1 : ℝ) / (2 * ‖(q.2 : ℂ)‖)) * ‖(q.2 : ℂ)‖ =
          (1 - (q.1 : ℝ)) * ‖(q.2 : ℂ)‖ + (q.1 : ℝ) / 2 := by
        field_simp
      rw [norm_smul, Real.norm_of_nonneg hpos.le, hval]
      refine ⟨by nlinarith, ?_⟩
      nlinarith⟩
  have hFc : Continuous F := by
    refine Continuous.subtype_mk ?_ _
    have hn : ∀ q : I × {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}, 2 * ‖(q.2 : ℂ)‖ ≠ 0 := fun q => by
      have := q.2.2.1; positivity
    have hg : Continuous fun q : I × {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} => (q.2 : ℂ) :=
      continuous_subtype_val.comp continuous_snd
    have hf : Continuous fun q : I × {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} =>
        (1 - (q.1 : ℝ)) + (q.1 : ℝ) / (2 * ‖(q.2 : ℂ)‖) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
        ((continuous_subtype_val.comp continuous_fst).div
          (continuous_const.mul (continuous_norm.comp hg)) hn)
    exact hf.smul hg
  let H : ContinuousMap.Homotopy (ContinuousMap.id {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}) (i.comp r) :=
    { toFun := F
      continuous_toFun := hFc
      map_zero_left := fun z => by
        apply Subtype.ext
        simp [F]
      map_one_left := fun z => by
        apply Subtype.ext
        have hρz : ((ρ z : Circle) : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := rfl
        change (((1 - ((1 : I) : ℝ)) + ((1 : I) : ℝ) / (2 * ‖(z : ℂ)‖) : ℝ)) • (z : ℂ) =
          (1 / 2 : ℝ) • ((hc (hc.symm (ρ z)) : Circle) : ℂ)
        rw [hc.apply_symm_apply, hρz]
        have : ‖(z : ℂ)‖ ≠ 0 := z.2.1.ne'
        simp only [Complex.real_smul]
        push_cast
        simp
        field_simp }
  refine s78dg_pi1_deformation_bijective i r hri H (fun y s => ?_) 0
  apply Subtype.ext
  change (((1 - (s : ℝ)) + (s : ℝ) / (2 * ‖((i y : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}) : ℂ)‖) : ℝ)) •
    ((i y : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}) : ℂ) = ((i y : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}) : ℂ)
  have hn : ‖((i y : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}) : ℂ)‖ = 1 / 2 := by
    change ‖(1 / 2 : ℝ) • ((hc y : Circle) : ℂ)‖ = _
    rw [norm_smul, hnorm]; norm_num
  rw [hn]
  have : (1 - (s : ℝ)) + (s : ℝ) / (2 * (1 / 2)) = 1 := by ring
  rw [this, one_smul]


/-- **π₁ of the overlap.**  The overlap of the two charts has fundamental group `ℤ`, generated by the
loop `t ↦ π(½·e^{2πit})`. -/
theorem s78dg_cs_overlap_generator (p n : ℕ) :
    ∃ (b : ↥(s78dg_cs_U p n ∩ s78dg_cs_V p n)) (γ : Path b b),
      (∀ t : I, ∃ x : ClosedUnitDisc,
        (x : ℂ) = (1 / 2 : ℝ) • ((Circle.exp (2 * Real.pi * (t : ℝ)) : Circle) : ℂ) ∧
          ((γ t : ↥(s78dg_cs_U p n ∩ s78dg_cs_V p n)) : Quot (OrientableRel p n)) =
            Quot.mk (OrientableRel p n) x) ∧
        ∀ z : FundamentalGroup ↥(s78dg_cs_U p n ∩ s78dg_cs_V p n) b,
          z ∈ Subgroup.zpowers (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) := by
  -- the homeomorphism from the punctured disc onto the overlap
  let S' : Set ClosedUnitDisc := {z | 0 < ‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖ < 1}
  have hS' : IsOpen S' :=
    (isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)).inter
      (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const)
  have hemb := s78dg_cs_open_embedding (p := p) (n := n) S' hS' (fun x hx => hx.2)
  let e1 : S' ≃ₜ ↥(s78dg_cs_U p n ∩ s78dg_cs_V p n) :=
    hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr (s78dg_cs_overlap_range p n))
  let e2 : S' ≃ₜ {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    { toFun := fun z => ⟨(z.1 : ℂ), z.2⟩
      invFun := fun w => ⟨⟨(w : ℂ), mem_closedBall_zero_iff.2 w.2.2.le⟩, w.2⟩
      left_inv := fun z => rfl
      right_inv := fun w => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let Φ : {z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1} ≃ₜ ↥(s78dg_cs_U p n ∩ s78dg_cs_V p n) := e2.symm.trans e1
  obtain ⟨i, hi, hibij⟩ := s78dg_punctured_disc_pi1
  obtain ⟨γc, hγc, hgen⟩ := s78dg_circle_generator
  let Φc : C({z : ℂ // 0 < ‖z‖ ∧ ‖z‖ < 1}, ↥(s78dg_cs_U p n ∩ s78dg_cs_V p n)) :=
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
