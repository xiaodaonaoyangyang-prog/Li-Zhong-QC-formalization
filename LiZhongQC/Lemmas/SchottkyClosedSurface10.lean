import LiZhongQC.Lemmas.SchottkyClosedSurface9

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval

universe u

namespace LiZhongQC

/-- Restricting an ambient subspace to a smaller set. -/
theorem s78dg_sub_homeo {Q : Type*} [TopologicalSpace Q] {B : Set Q} (W : Set Q) (hW : W ⊆ B) :
    ∃ e : ↥(Subtype.val ⁻¹' W : Set ↥B) ≃ₜ ↥W,
      ∀ y : ↥W, (((e.symm y : ↥(Subtype.val ⁻¹' W : Set ↥B)) : ↥B) : Q) = (y : Q) :=
  ⟨{ toFun := fun x => ⟨x.1.1, x.2⟩
     invFun := fun y => ⟨⟨y.1, hW y.2⟩, y.2⟩
     left_inv := fun x => rfl
     right_inv := fun y => rfl
     continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
     continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _ },
   fun y => rfl⟩

/-- Composition of maps inducing bijections on `π₁`. -/
theorem s78dg_pi1_comp_bijective {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] (f : C(A, B)) (g : C(B, C)) (a : A)
    (hf : Function.Bijective (FundamentalGroup.map f a))
    (hg : Function.Bijective (FundamentalGroup.map g (f a))) :
    Function.Bijective (FundamentalGroup.map (g.comp f) a) := by
  have h : ∀ x, FundamentalGroup.map (g.comp f) a x =
      FundamentalGroup.map g (f a) (FundamentalGroup.map f a x) := by
    intro x
    induction x using Quotient.inductionOn with
    | h γ => rfl
  have h2 : (FundamentalGroup.map (g.comp f) a : _ → _) =
      (FundamentalGroup.map g (f a)) ∘ (FundamentalGroup.map f a) := funext h
  rw [h2]
  exact hg.comp hf

/-- A point of `S P` can be joined to a vertex by a segment inside `S P`. -/
theorem s78dg_cs_S_segment (p : ℕ) (P : ℕ → Prop) {u : ℝ} (hu : u ∈ s78dg_cs_S p P) :
    ∃ j : ℤ, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (j : ℝ) + s * (u - j) ∈ s78dg_cs_S p P := by
  rcases hu with ⟨j, hj⟩ | hP
  · refine ⟨j, fun s hs0 hs1 => Or.inl ⟨j, ?_⟩⟩
    rw [show (j : ℝ) + s * (u - j) - j = s * (u - j) by ring, abs_mul, abs_of_nonneg hs0]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) hs1) hj
  · refine ⟨⌊u⌋, fun s hs0 hs1 => Or.inr ?_⟩
    have h0 : (0 : ℝ) ≤ u - ⌊u⌋ := sub_nonneg.2 (Int.floor_le u)
    have h1 : u - ⌊u⌋ < 1 := by have := Int.lt_floor_add_one u; linarith
    have hfl : ⌊(⌊u⌋ : ℝ) + s * (u - ⌊u⌋)⌋ = ⌊u⌋ := by
      rw [Int.floor_eq_iff]
      constructor
      · have := mul_nonneg hs0 h0; linarith
      · have : s * (u - ⌊u⌋) < 1 := lt_of_le_of_lt (mul_le_of_le_one_left h0 hs1) h1
        linarith
    rw [hfl]
    exact hP

theorem s78dg_cs_Y_pathConnected (p : ℕ) (hp : 1 ≤ p) (P : ℕ → Prop) :
    PathConnectedSpace ↥(s78dg_cs_Y p hp (s78dg_cs_S p P)) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  let Y := s78dg_cs_Y p hp (s78dg_cs_S p P)
  let one : Set.Ioc (0 : ℝ) 1 := ⟨1, zero_lt_one, le_rfl⟩
  have hone : (one : ℝ) = 1 := rfl
  let cl : ℝ → ℝ := fun s => max 0 (min 1 s)
  have hcl : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have hcl0 : ∀ s, 0 ≤ cl s := fun s => le_max_left _ _
  have hcl1 : ∀ s, cl s ≤ 1 := fun s => max_le zero_le_one (min_le_left _ _)
  have hcl_0 : cl 0 = 0 := by simp [cl]
  have hcl_1 : cl 1 = 1 := by simp [cl]
  have h0S : (0 : ℝ) ∈ s78dg_cs_S p P := Or.inl ⟨0, by simp⟩
  let v : Quot (OrientableRel p 0) :=
    ((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))
  have hv : v ∈ Y := ⟨(one, 0), h0S, rfl⟩
  refine ⟨v, hv, ?_⟩
  rintro y ⟨⟨ρ, u⟩, hu, rfl⟩
  obtain ⟨j, hj⟩ := s78dg_cs_S_segment p P hu
  -- segment on the boundary
  have hseg : JoinedIn Y
      ((s78dg_cs_Psi_fun p hp (one, (j : ℝ)) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))
      ((s78dg_cs_Psi_fun p hp (one, u) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) := by
    refine JoinedIn.ofLine (f := fun s => ((s78dg_cs_Psi_fun p hp (one, (j : ℝ) + cl s * (u - j)) :
      ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) ?_ ?_ ?_ ?_
    · refine (continuous_subtype_val.comp ((s78dg_cs_Psi_quot p hp).continuous.comp
        (continuous_const.prodMk (continuous_const.add (hcl.mul continuous_const))))).continuousOn
    · simp [hcl_0]
    · simp [hcl_1]
    · rintro _ ⟨s, _, rfl⟩
      exact ⟨(one, _), hj _ (hcl0 s) (hcl1 s), rfl⟩
  have hrad : JoinedIn Y
      ((s78dg_cs_Psi_fun p hp (ρ, u) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))
      ((s78dg_cs_Psi_fun p hp (one, u) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) := by
    have hρ0 := ρ.2.1
    have hρ1 := ρ.2.2
    let r : ℝ → Set.Ioc (0 : ℝ) 1 := fun s =>
      ⟨(ρ : ℝ) + cl s * (1 - ρ), by
        have := mul_nonneg (hcl0 s) (sub_nonneg.2 hρ1); linarith, by
        have := mul_le_mul_of_nonneg_right (hcl1 s) (sub_nonneg.2 hρ1); linarith⟩
    have hrc : Continuous r :=
      Continuous.subtype_mk (continuous_const.add (hcl.mul continuous_const)) _
    refine JoinedIn.ofLine (f := fun s => ((s78dg_cs_Psi_fun p hp (r s, u) :
      ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) ?_ ?_ ?_ ?_
    · exact (continuous_subtype_val.comp ((s78dg_cs_Psi_quot p hp).continuous.comp
        (hrc.prodMk continuous_const))).continuousOn
    · have : r 0 = ρ := Subtype.ext (by simp [r, hcl_0])
      rw [this]
    · have : r 1 = one := Subtype.ext (by simp [r, hcl_1, hone])
      rw [this]
    · rintro _ ⟨s, _, rfl⟩
      exact ⟨(r s, u), hu, rfl⟩
  have hvert : ((s78dg_cs_Psi_fun p hp (one, (j : ℝ)) : ↥(s78dg_cs_U p 0)) :
      Quot (OrientableRel p 0)) = v := by
    rw [s78dg_cs_Psi_vertex p hp one hone j]
  rw [hvert] at hseg
  exact hseg.trans hrad.symm


theorem s78dg_cs_v_mem (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (P : ℕ → Prop) :
    ((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) ∈
      s78dg_cs_Y p hp (s78dg_cs_S p P) :=
  ⟨(one, 0), Or.inl ⟨0, by simp⟩, rfl⟩

theorem s78dg_cs_E_mem_lt (p m : ℕ) (hm : m < 2 * p) (k : ℕ) (hmk : m < k) {x : ℝ} (h0 : 0 ≤ x)
    (h1 : x ≤ 1) : s78dg_cs_E m + x ∈ s78dg_cs_S p (fun n => n < k) := by
  rcases s78dg_cs_E_mem p m hm h0 h1 with h | h
  · exact Or.inl h
  · right
    have h' : s78dg_cs_kappa p ⌊s78dg_cs_E m + x⌋ = m := h
    show s78dg_cs_kappa p ⌊s78dg_cs_E m + x⌋ < k
    rw [h']; exact hmk

theorem s78dg_cs_S_succ (p k : ℕ) :
    s78dg_cs_S p (fun m => m < k + 1) =
      s78dg_cs_S p (fun m => m < k) ∪ s78dg_cs_S p (fun m => m = k) := by
  ext u
  simp only [s78dg_cs_S, Set.mem_setOf_eq, Set.mem_union]
  have key : ∀ n : ℕ, n < k + 1 ↔ n < k ∨ n = k := fun n => by omega
  rw [key]
  tauto

theorem s78dg_cs_S_inter (p k : ℕ) :
    s78dg_cs_S p (fun m => m < k) ∩ s78dg_cs_S p (fun m => m = k) =
      s78dg_cs_S p (fun _ => False) := by
  ext u
  simp only [s78dg_cs_S, Set.mem_setOf_eq, Set.mem_inter_iff]
  have key : ∀ n : ℕ, ¬ (n < k ∧ n = k) := fun n => by omega
  have := key (s78dg_cs_kappa p ⌊u⌋)
  tauto

theorem s78dg_cs_S_zero (p : ℕ) :
    s78dg_cs_S p (fun m => m < 0) = s78dg_cs_S p (fun _ => False) := by
  ext u
  simp [s78dg_cs_S]


open DifferentialGeometry.Topology.VanKampen

/-- **One petal step.**  Adding the petal `k` to the first `k` petals adds one free generator. -/
theorem s78dg_cs_petal_step (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (k : ℕ) (hk : k < 2 * p)
    (IH : ∃ e : FundamentalGroup ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k)))
        (⟨((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
          s78dg_cs_v_mem p hp one _⟩) ≃* FreeGroup (Fin k),
      ∀ (j : ℕ) (hj : j < k) (L : Path
          (⟨((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
            s78dg_cs_v_mem p hp one (fun m => m < k)⟩ : ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k))))
          (⟨((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
            s78dg_cs_v_mem p hp one (fun m => m < k)⟩ : ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k))))),
        (∀ t, (((L t : ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k)))) :
            Quot (OrientableRel p 0))) =
          ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + Int.fract (t : ℝ)) : ↥(s78dg_cs_U p 0)) :
            Quot (OrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩) :
    ∃ e : FundamentalGroup ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k + 1)))
        (⟨((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
          s78dg_cs_v_mem p hp one _⟩) ≃* FreeGroup (Fin (k + 1)),
      ∀ (j : ℕ) (hj : j < k + 1) (L : Path
          (⟨((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
            s78dg_cs_v_mem p hp one (fun m => m < k + 1)⟩ :
              ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k + 1))))
          (⟨((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
            s78dg_cs_v_mem p hp one (fun m => m < k + 1)⟩ :
              ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k + 1))))),
        (∀ t, (((L t : ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k + 1)))) :
            Quot (OrientableRel p 0))) =
          ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + Int.fract (t : ℝ)) : ↥(s78dg_cs_U p 0)) :
            Quot (OrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩ := by
  obtain ⟨eA, heA⟩ := IH
  have hSsat := s78dg_cs_S_sat p
  have hSun := s78dg_cs_S_succ p k
  have hSin := s78dg_cs_S_inter p k
  have hYun : s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k + 1)) =
      s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k)) ∪
        s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m = k)) := by
    rw [hSun]; exact s78dg_cs_Y_union p hp _ _
  have hYin : s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k)) ∩
        s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m = k)) =
      s78dg_cs_Y p hp (s78dg_cs_S p (fun _ => False)) := by
    rw [s78dg_cs_Y_inter p hp _ _ (hSsat _) (hSsat _), hSin]
  have hsubU : s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k)) ⊆
      s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k + 1)) := by
    rw [hYun]; exact Set.subset_union_left
  have hsubV : s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m = k)) ⊆
      s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k + 1)) := by
    rw [hYun]; exact Set.subset_union_right
  have hsubI : s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k)) ∩
        s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m = k)) ⊆
      s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k + 1)) := fun x hx => hsubU hx.1
  -- the ambient space and the cover
  let X := ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k + 1)))
  let U : Set X := Subtype.val ⁻¹' s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k))
  let V : Set X := Subtype.val ⁻¹' s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m = k))
  have hopen : ∀ P : ℕ → Prop, IsOpen (s78dg_cs_Y p hp (s78dg_cs_S p P)) := fun P =>
    s78dg_cs_Y_open p hp _ (s78dg_cs_S_open p P) (hSsat P).1 (hSsat P).2.1 (hSsat P).2.2
  have hU : IsOpen U := (hopen _).preimage continuous_subtype_val
  have hV : IsOpen V := (hopen _).preimage continuous_subtype_val
  have hcover : U ∪ V = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact (Set.ext_iff.1 hYun x.1).1 x.2
  let x₀ : X := ⟨((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
    s78dg_cs_v_mem p hp one _⟩
  have hx₀ : x₀ ∈ U ∩ V := ⟨s78dg_cs_v_mem p hp one _, s78dg_cs_v_mem p hp one _⟩
  -- homeomorphisms
  obtain ⟨eU, heU⟩ := s78dg_sub_homeo (B := s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k + 1)))
    (s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k))) hsubU
  obtain ⟨eV, heV⟩ := s78dg_sub_homeo (B := s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k + 1)))
    (s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m = k))) hsubV
  obtain ⟨eI, heI⟩ := s78dg_sub_homeo (B := s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k + 1)))
    (s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k)) ∩
        s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m = k))) hsubI
  let eI' : ↥(U ∩ V) ≃ₜ ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun _ => False))) :=
    eI.trans (Homeomorph.setCongr hYin)
  haveI : PathConnectedSpace ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k))) :=
    s78dg_cs_Y_pathConnected p hp _
  haveI : PathConnectedSpace ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m = k))) :=
    s78dg_cs_Y_pathConnected p hp _
  haveI : PathConnectedSpace ↥U := eU.symm.pathConnectedSpace
  haveI : PathConnectedSpace ↥V := eV.symm.pathConnectedSpace
  haveI : ContractibleSpace ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun _ => False))) :=
    s78dg_cs_Y0_contractible p hp
  haveI : ContractibleSpace ↥(U ∩ V) := eI'.contractibleSpace
  -- the petal circle
  obtain ⟨i, hi, hibij⟩ := s78dg_cs_petal_pi1 p hp k hk one hone
  obtain ⟨φ, γ, hγ, hφ⟩ := s78dg_circle_core
  let fA : C(↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k))), ↥U) :=
    ⟨eU.symm, eU.symm.continuous⟩
  let gV : C(↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m = k))), ↥V) :=
    ⟨eV.symm, eV.symm.continuous⟩
  let fB : C(AddCircle (1 : ℝ), ↥V) := gV.comp i
  let a₀ : ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k))) :=
    ⟨((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
      s78dg_cs_v_mem p hp one _⟩
  have hA : fA a₀ = leftBasepoint U x₀ hx₀.1 := Subtype.ext (Subtype.ext (heU a₀))
  have hAb : Function.Bijective (FundamentalGroup.map fA a₀) :=
    s78dg_pi1_homeo_bijective eU.symm a₀
  have hi0 : ((i (0 : AddCircle (1 : ℝ)) : ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m = k)))) :
      Quot (OrientableRel p 0)) =
      ((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) := by
    have h := hi 0
    rw [AddCircle.coe_zero] at h
    rw [h, Int.fract_zero, add_zero]
    have hE0 : s78dg_cs_E k = (((4 * (k / 2) + k % 2 : ℕ) : ℤ) : ℝ) := by
      unfold s78dg_cs_E; exact (Int.cast_natCast _).symm
    rw [hE0, s78dg_cs_Psi_vertex p hp one hone _]
  have hB : fB 0 = rightBasepoint V x₀ hx₀.2 :=
    Subtype.ext (Subtype.ext ((heV (i 0)).trans hi0))
  have hBb : Function.Bijective (FundamentalGroup.map fB 0) :=
    s78dg_pi1_comp_bijective i gV 0 (hibij 0) (s78dg_pi1_homeo_bijective eV.symm (i 0))
  let eB : FundamentalGroup (AddCircle (1 : ℝ)) 0 ≃* FreeGroup Unit :=
    φ.trans (FreeGroup.mulEquivIntOfUnique (α := Unit)).symm
  have heB : eB (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = FreeGroup.of () := by
    show (FreeGroup.mulEquivIntOfUnique (α := Unit)).symm (φ (Path.Homotopic.Quotient.mk γ)) = _
    rw [hφ]
    rw [MulEquiv.symm_apply_eq]
    simp [FreeGroup.mulEquivIntOfUnique, FreeGroup.equivIntOfUnique]
  obtain ⟨e, he1, he2⟩ := s78dg_wedge_step_loops U V hU hV hcover x₀ hx₀ fA a₀ hA hAb eA fB 0 hB hBb eB
  let sg : Fin k ⊕ Unit ≃ Fin (k + 1) :=
    (Equiv.sumCongr (Equiv.refl (Fin k)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv
  refine ⟨e.trans (FreeGroup.freeGroupCongr sg), ?_⟩
  intro j hj L hL
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hjk | hjk
  · have hmem : ∀ t : I, ((L t : X) : Quot (OrientableRel p 0)) ∈
        s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k)) := fun t => by
      rw [hL t]
      exact ⟨(one, s78dg_cs_E j + Int.fract (t : ℝ)),
        s78dg_cs_E_mem_lt p j (by omega) k hjk (Int.fract_nonneg _) (Int.fract_lt_one _).le, rfl⟩
    let ℓ : Path a₀ a₀ :=
      { toFun := fun t => ⟨((L t : X) : Quot (OrientableRel p 0)), hmem t⟩
        continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp L.continuous) _
        source' := Subtype.ext (congrArg (fun x : X => (x : Quot (OrientableRel p 0))) L.source)
        target' := Subtype.ext (congrArg (fun x : X => (x : Quot (OrientableRel p 0))) L.target) }
    have hLℓ : ∀ t, L t = ((fA (ℓ t) : ↥U) : X) := fun t => Subtype.ext (heU (ℓ t)).symm
    have h1 := he1 ℓ L hLℓ
    have h2 := heA j hjk ℓ (fun t => hL t)
    rw [MulEquiv.trans_apply, h1, h2]
    simp [FreeGroup.freeGroupCongr, sg]
  · have hL' : ∀ t : I, ((L t : X) : Quot (OrientableRel p 0)) =
        ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E k + Int.fract (t : ℝ)) : ↥(s78dg_cs_U p 0)) :
          Quot (OrientableRel p 0)) := fun t => by have h := hL t; rw [hjk] at h; exact h
    have hLγ : ∀ t, L t = ((fB (γ t) : ↥V) : X) := fun t => by
      apply Subtype.ext
      rw [hL' t, hγ t]
      exact (hi (t : ℝ)).symm.trans (heV (i _)).symm
    have h1 := he2 γ L hLγ
    rw [MulEquiv.trans_apply, h1, heB]
    have hsg : (⟨j, hj⟩ : Fin (k + 1)) = sg (Sum.inr ()) := Fin.ext (by simp [sg, hjk])
    rw [hsg]
    simp [FreeGroup.freeGroupCongr]


/-- **Petal induction.**  The union of the vertex star and the first `k` petals has free `π₁` on `k`
generators, the generators being the petal loops. -/
theorem s78dg_cs_petal_induction (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1)
    (k : ℕ) (hk : k ≤ 2 * p) :
    ∃ e : FundamentalGroup ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k)))
        (⟨((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
          s78dg_cs_v_mem p hp one _⟩) ≃* FreeGroup (Fin k),
      ∀ (j : ℕ) (hj : j < k) (L : Path
          (⟨((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
            s78dg_cs_v_mem p hp one (fun m => m < k)⟩ : ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k))))
          (⟨((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
            s78dg_cs_v_mem p hp one (fun m => m < k)⟩ : ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k))))),
        (∀ t, (((L t : ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < k)))) :
            Quot (OrientableRel p 0))) =
          ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + Int.fract (t : ℝ)) : ↥(s78dg_cs_U p 0)) :
            Quot (OrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩ := by
  induction k with
  | zero =>
    have hc : ContractibleSpace ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < 0))) := by
      rw [s78dg_cs_S_zero p]
      exact s78dg_cs_Y0_contractible p hp
    have hFG : ∀ x : FreeGroup (Fin 0), x = 1 := by
      intro x
      induction x using FreeGroup.induction_on with
      | one => rfl
      | of a => exact a.elim0
      | inv_of a _ => exact a.elim0
      | mul _ _ h1 h2 => rw [h1, h2, mul_one]
    haveI : Subsingleton (FundamentalGroup ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < 0)))
        (⟨((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
          s78dg_cs_v_mem p hp one _⟩)) := inferInstance
    haveI : Subsingleton (FreeGroup (Fin 0)) := ⟨fun a b => (hFG a).trans (hFG b).symm⟩
    refine ⟨{ toFun := fun _ => 1
              invFun := fun _ => 1
              left_inv := fun x => Subsingleton.elim _ _
              right_inv := fun x => Subsingleton.elim _ _
              map_mul' := fun _ _ => (mul_one _).symm }, ?_⟩
    intro j hj
    exact absurd hj (Nat.not_lt_zero _)
  | succ k ih =>
    exact s78dg_cs_petal_step p hp one hone k (by omega) (ih (by omega))


theorem s78dg_cs_kappa_lt (p : ℕ) (hp : 1 ≤ p) (j : ℤ) : s78dg_cs_kappa p j < 2 * p := by
  have hN : (0 : ℤ) < ((4 * p : ℕ) : ℤ) := by positivity
  have h0 := Int.emod_nonneg j hN.ne'
  have h1 := Int.emod_lt_of_pos j hN
  unfold s78dg_cs_kappa
  omega

theorem s78dg_cs_Y_full (p : ℕ) (hp : 1 ≤ p) :
    s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < 2 * p)) = s78dg_cs_U p 0 := by
  ext q
  constructor
  · exact fun hq => s78dg_cs_Y_sub_U p hp _ hq
  · intro hq
    obtain ⟨a, ha⟩ := (s78dg_cs_Psi_quot p hp).surjective (⟨q, hq⟩ : ↥(s78dg_cs_U p 0))
    refine ⟨a, Or.inr (s78dg_cs_kappa_lt p hp _), ?_⟩
    rw [ha]

/-- **π₁ of the punctured chart is free on the petal loops.** -/
theorem s78dg_cs_pi1_free (p : ℕ) (hp : 1 ≤ p) (one : Set.Ioc (0 : ℝ) 1) (hone : (one : ℝ) = 1) :
    ∃ e : FundamentalGroup ↥(s78dg_cs_U p 0) (s78dg_cs_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin (2 * p)),
      ∀ (j : ℕ) (hj : j < 2 * p) (L : Path (s78dg_cs_Psi_fun p hp (one, 0))
          (s78dg_cs_Psi_fun p hp (one, 0))),
        (∀ t, (((L t : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) =
          ((s78dg_cs_Psi_fun p hp (one, s78dg_cs_E j + Int.fract (t : ℝ)) : ↥(s78dg_cs_U p 0)) :
            Quot (OrientableRel p 0))) →
        e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = FreeGroup.of ⟨j, hj⟩ := by
  obtain ⟨e0, he0⟩ := s78dg_cs_petal_induction p hp one hone (2 * p) le_rfl
  have hset := s78dg_cs_Y_full p hp
  let h : ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < 2 * p))) ≃ₜ ↥(s78dg_cs_U p 0) :=
    Homeomorph.setCongr hset
  let a₀ : ↥(s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < 2 * p))) :=
    ⟨((s78dg_cs_Psi_fun p hp (one, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
      s78dg_cs_v_mem p hp one _⟩
  let m := FundamentalGroup.map (⟨h, h.continuous⟩ : C(_, _)) a₀
  have hm : Function.Bijective m := s78dg_pi1_homeo_bijective h a₀
  let e : FundamentalGroup ↥(s78dg_cs_U p 0) (s78dg_cs_Psi_fun p hp (one, 0)) ≃* FreeGroup (Fin (2 * p)) :=
    (MulEquiv.ofBijective m hm).symm.trans e0
  refine ⟨e, fun j hj L hL => ?_⟩
  have hmem : ∀ t : I, ((L t : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) ∈
      s78dg_cs_Y p hp (s78dg_cs_S p (fun m => m < 2 * p)) := fun t =>
    (Set.ext_iff.1 hset _).2 (L t).2
  let Lℓ : Path a₀ a₀ :=
    { toFun := fun t => ⟨((L t : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)), hmem t⟩
      continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp L.continuous) _
      source' := Subtype.ext (congrArg (fun x : ↥(s78dg_cs_U p 0) =>
        (x : Quot (OrientableRel p 0))) L.source)
      target' := Subtype.ext (congrArg (fun x : ↥(s78dg_cs_U p 0) =>
        (x : Quot (OrientableRel p 0))) L.target) }
  have hLeq : L = Lℓ.map h.continuous := Path.ext (funext fun t => Subtype.ext rfl)
  have key : e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Lℓ.map h.continuous))) =
      e0 (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Lℓ)) :=
    congrArg e0 (MulEquiv.symm_apply_apply (MulEquiv.ofBijective m hm)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Lℓ)))
  rw [hLeq, key]
  exact he0 j hj Lℓ (fun t => hL t)


end LiZhongQC
