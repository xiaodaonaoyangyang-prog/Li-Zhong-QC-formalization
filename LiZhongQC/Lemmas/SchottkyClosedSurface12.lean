import LiZhongQC.Lemmas.SchottkyClosedSurface11
import LiZhongQC.Lemmas.SchottkyOneCellSVK

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval

universe u

namespace LiZhongQC

/-- A free group is the presented group with no relations. -/
theorem s78dg_free_presented_empty (α : Type) :
    ∃ T : FreeGroup α ≃* PresentedGroup (∅ : Set (FreeGroup α)),
      ∀ x, T x = PresentedGroup.mk (∅ : Set (FreeGroup α)) x := by
  let T : FreeGroup α ≃* PresentedGroup (∅ : Set (FreeGroup α)) :=
    (QuotientGroup.quotientBot (G := FreeGroup α)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (Subgroup.normalClosure_empty (G := FreeGroup α)).symm)
  exact ⟨T, fun x => rfl⟩

/-- The relabelling of generators `aᵢ ↦ x₂ᵢ⁻¹`, `bᵢ ↦ x₂ᵢ₊₁⁻¹`. -/
theorem s78dg_free_equiv_double (p : ℕ) :
    ∃ θ : FreeGroup (Fin p ⊕ Fin p) ≃* FreeGroup (Fin (2 * p)),
      (∀ i : Fin p, θ (FreeGroup.of (Sum.inl i)) = (FreeGroup.of ⟨2 * (i : ℕ), by omega⟩)⁻¹) ∧
      (∀ i : Fin p, θ (FreeGroup.of (Sum.inr i)) = (FreeGroup.of ⟨2 * (i : ℕ) + 1, by omega⟩)⁻¹) := by
  let f : FreeGroup (Fin p ⊕ Fin p) →* FreeGroup (Fin (2 * p)) :=
    FreeGroup.lift (Sum.elim (fun i : Fin p => (FreeGroup.of ⟨2 * (i : ℕ), by omega⟩ :
        FreeGroup (Fin (2 * p)))⁻¹) (fun i : Fin p => (FreeGroup.of ⟨2 * (i : ℕ) + 1, by omega⟩ :
        FreeGroup (Fin (2 * p)))⁻¹))
  let g : FreeGroup (Fin (2 * p)) →* FreeGroup (Fin p ⊕ Fin p) :=
    FreeGroup.lift (fun j : Fin (2 * p) =>
      if h : (j : ℕ) % 2 = 0 then (FreeGroup.of (Sum.inl ⟨(j : ℕ) / 2, by omega⟩) :
          FreeGroup (Fin p ⊕ Fin p))⁻¹
      else (FreeGroup.of (Sum.inr ⟨(j : ℕ) / 2, by omega⟩) : FreeGroup (Fin p ⊕ Fin p))⁻¹)
  have hgf : g.comp f = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro s
    rcases s with i | i
    · have : g (FreeGroup.of ⟨2 * (i : ℕ), by omega⟩) = (FreeGroup.of (Sum.inl i))⁻¹ := by
        simp only [g, FreeGroup.lift_apply_of]
        rw [dif_pos (by simp)]
        congr 3
        ext; simp <;> omega
      simp [f, this]
    · have : g (FreeGroup.of ⟨2 * (i : ℕ) + 1, by omega⟩) = (FreeGroup.of (Sum.inr i))⁻¹ := by
        simp only [g, FreeGroup.lift_apply_of]
        rw [dif_neg (by simp)]
        congr 3
        ext; simp <;> omega
      simp [f, this]
  have hfg : f.comp g = MonoidHom.id _ := by
    apply FreeGroup.ext_hom
    intro j
    by_cases h : (j : ℕ) % 2 = 0
    · simp only [g, MonoidHom.comp_apply, FreeGroup.lift_apply_of, dif_pos h, map_inv, MonoidHom.id_apply]
      simp only [f, FreeGroup.lift_apply_of, Sum.elim_inl]
      rw [inv_inv]
      exact congrArg FreeGroup.of (Fin.ext (by simp; omega))
    · simp only [g, MonoidHom.comp_apply, FreeGroup.lift_apply_of, dif_neg h, map_inv, MonoidHom.id_apply]
      simp only [f, FreeGroup.lift_apply_of, Sum.elim_inr]
      rw [inv_inv]
      exact congrArg FreeGroup.of (Fin.ext (by simp; omega))
  refine ⟨MonoidHom.toMulEquiv f g hgf hfg, fun i => ?_, fun i => ?_⟩
  · simp [f]
  · simp [f]


theorem s78dg_cs_norm_param (ρ r : ℝ) (h : 0 < ρ) :
    ‖(ρ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = ρ := by
  rw [norm_mul, show (2 * Real.pi * Complex.I * (r : ℂ)) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos h, mul_one]

theorem s78dg_cs_overlap_char (p : ℕ) (hp : 1 ≤ p) (q : Quot (OrientableRel p 0)) :
    q ∈ s78dg_cs_U p 0 ∩ s78dg_cs_V p 0 ↔
      ∃ a : Set.Ioc (0 : ℝ) 1 × ℝ, (a.1 : ℝ) < 1 ∧
        ((s78dg_cs_Psi_fun p hp a : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) = q := by
  constructor
  · rintro ⟨hqU, ⟨y, hy, hyq⟩⟩
    obtain ⟨a, ha⟩ := (s78dg_cs_Psi_quot p hp).surjective (⟨q, hqU⟩ : ↥(s78dg_cs_U p 0))
    refine ⟨a, ?_, congrArg Subtype.val ha⟩
    obtain ⟨z, hz, hz'⟩ := s78dg_cs_Psi_spec p hp a.1 a.2
    have hq : Quot.mk (OrientableRel p 0) z = Quot.mk (OrientableRel p 0) y :=
      hz'.symm.trans ((congrArg Subtype.val ha).trans hyq.symm)
    rcases s78dg_cs_eqv_boundary (Quot.eqvGen_exact hq) with h | h
    · have hy' : ‖(y : ℂ)‖ < 1 := hy
      rw [← h] at hy'
      rw [hz, s78dg_cs_norm_param _ _ a.1.2.1] at hy'
      exact hy'
    · have hy' : ‖(y : ℂ)‖ < 1 := hy
      exact absurd h.2 hy'.ne
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(s78dg_cs_Psi_fun p hp a).2, ?_⟩
    obtain ⟨z, hz, hz'⟩ := s78dg_cs_Psi_spec p hp a.1 a.2
    refine ⟨z, ?_, hz'.symm⟩
    show ‖(z : ℂ)‖ < 1
    rw [hz, s78dg_cs_norm_param _ _ a.1.2.1]
    exact ha

theorem s78dg_cs_overlap_pathConnected (p : ℕ) (hp : 1 ≤ p) :
    PathConnectedSpace ↥(s78dg_cs_U p 0 ∩ s78dg_cs_V p 0) := by
  rw [← isPathConnected_iff_pathConnectedSpace]
  let W := s78dg_cs_U p 0 ∩ s78dg_cs_V p 0
  let half : Set.Ioc (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  let cl : ℝ → ℝ := fun s => max 0 (min 1 s)
  have hcl : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have hcl0 : ∀ s, 0 ≤ cl s := fun s => le_max_left _ _
  have hcl1 : ∀ s, cl s ≤ 1 := fun s => max_le zero_le_one (min_le_left _ _)
  have hcl_0 : cl 0 = 0 := by simp [cl]
  have hcl_1 : cl 1 = 1 := by simp [cl]
  have hmem : ∀ (ρ : Set.Ioc (0 : ℝ) 1) (u : ℝ), (ρ : ℝ) < 1 →
      ((s78dg_cs_Psi_fun p hp (ρ, u) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) ∈ W :=
    fun ρ u h => (s78dg_cs_overlap_char p hp _).2 ⟨(ρ, u), h, rfl⟩
  refine ⟨((s78dg_cs_Psi_fun p hp (half, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)),
    hmem half 0 (by show (1 : ℝ) / 2 < 1; norm_num), ?_⟩
  intro q hq
  obtain ⟨⟨ρ, u⟩, hρ, rfl⟩ := (s78dg_cs_overlap_char p hp q).1 hq
  have hρ0 := ρ.2.1
  -- radial segment at height `u` from `ρ` to `1/2`
  let r : ℝ → Set.Ioc (0 : ℝ) 1 := fun s =>
    ⟨(ρ : ℝ) + cl s * (1 / 2 - ρ), by
      have : (0 : ℝ) < (1 - cl s) * ρ + cl s * (1 / 2) := by
        have := hcl0 s; have := hcl1 s
        rcases eq_or_lt_of_le (hcl1 s) with h | h
        · rw [h]; norm_num
        · have : 0 < 1 - cl s := by linarith
          positivity
      nlinarith, by
      have h1 := hcl0 s
      have h2 := hcl1 s
      nlinarith⟩
  have hrc : Continuous r :=
    Continuous.subtype_mk (continuous_const.add (hcl.mul continuous_const)) _
  have hrad : JoinedIn W
      ((s78dg_cs_Psi_fun p hp (half, u) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))
      ((s78dg_cs_Psi_fun p hp (ρ, u) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) := by
    refine JoinedIn.ofLine (f := fun s => ((s78dg_cs_Psi_fun p hp (r (1 - s), u) :
      ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) ?_ ?_ ?_ ?_
    · exact (continuous_subtype_val.comp ((s78dg_cs_Psi_quot p hp).continuous.comp
        ((hrc.comp (continuous_const.sub continuous_id)).prodMk continuous_const))).continuousOn
    · have : r (1 - 0) = half := Subtype.ext (by simp [r, hcl_1, half])
      rw [this]
    · have : r (1 - 1) = ρ := Subtype.ext (by simp [r, hcl_0])
      rw [this]
    · rintro _ ⟨s, _, rfl⟩
      refine hmem _ _ ?_
      have h1 := hcl0 (1 - s)
      have h2 := hcl1 (1 - s)
      show (ρ : ℝ) + cl (1 - s) * (1 / 2 - ρ) < 1
      nlinarith
  -- rotate
  have hrot : JoinedIn W
      ((s78dg_cs_Psi_fun p hp (half, 0) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))
      ((s78dg_cs_Psi_fun p hp (half, u) : ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0)) := by
    refine JoinedIn.ofLine (f := fun s => ((s78dg_cs_Psi_fun p hp (half, cl s * u) :
      ↥(s78dg_cs_U p 0)) : Quot (OrientableRel p 0))) ?_ ?_ ?_ ?_
    · exact (continuous_subtype_val.comp ((s78dg_cs_Psi_quot p hp).continuous.comp
        (continuous_const.prodMk (hcl.mul continuous_const)))).continuousOn
    · simp [hcl_0]
    · simp [hcl_1]
    · rintro _ ⟨s, _, rfl⟩
      exact hmem _ _ (by show (1 : ℝ) / 2 < 1; norm_num)
  exact hrot.trans hrad

theorem s78dg_cs_U_pathConnected (p : ℕ) (hp : 1 ≤ p) : PathConnectedSpace ↥(s78dg_cs_U p 0) := by
  haveI := s78dg_cs_Y_pathConnected p hp (fun m => m < 2 * p)
  exact (Homeomorph.setCongr (s78dg_cs_Y_full p hp)).pathConnectedSpace


open DifferentialGeometry.Topology.VanKampen

/-- **π₁ of the closed orientable surface of genus `p`, at one base point.** -/
theorem s78dg_cs_pi1_closed_base (p : ℕ) (hp : 1 ≤ p) :
    ∃ x : Quot (OrientableRel p 0), Nonempty (FundamentalGroup (Quot (OrientableRel p 0)) x ≃*
      PresentedGroup {(List.ofFn fun i : Fin p =>
        FreeGroup.of (Sum.inl i : Fin p ⊕ Fin p) * FreeGroup.of (Sum.inr i) *
          (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod}) := by
  let one : Set.Ioc (0 : ℝ) 1 := ⟨1, zero_lt_one, le_rfl⟩
  have hone : (one : ℝ) = 1 := rfl
  let half : Set.Ioc (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  have hhalf : (half : ℝ) = 1 / 2 := rfl
  obtain ⟨e, he⟩ := s78dg_cs_pi1_free p hp one hone
  obtain ⟨β, hβ, hW⟩ := s78dg_cs_boundary_word p hp one hone e he
  obtain ⟨b, γ, hγv, hγgen⟩ := s78dg_cs_overlap_generator p 0
  obtain ⟨θ, hθa, hθb⟩ := s78dg_free_equiv_double p
  obtain ⟨T, hT⟩ := s78dg_free_presented_empty (Fin p ⊕ Fin p)
  haveI : PathConnectedSpace ↥(s78dg_cs_U p 0) := s78dg_cs_U_pathConnected p hp
  haveI := s78dg_cs_V_contractible p 0
  haveI := s78dg_cs_overlap_pathConnected p hp
  refine ⟨(b : Quot (OrientableRel p 0)), ?_⟩
  have hx₀ : (b : Quot (OrientableRel p 0)) ∈ s78dg_cs_U p 0 ∩ s78dg_cs_V p 0 := b.2
  let x₁ : ↥(s78dg_cs_U p 0) := ⟨(b : Quot (OrientableRel p 0)), hx₀.1⟩
  let c : Path x₁ x₁ :=
    { toFun := fun t => ⟨((γ t : ↥(s78dg_cs_U p 0 ∩ s78dg_cs_V p 0)) : Quot (OrientableRel p 0)),
        (γ t).2.1⟩
      continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp γ.continuous) _
      source' := Subtype.ext (congrArg (fun x : ↥(s78dg_cs_U p 0 ∩ s78dg_cs_V p 0) =>
        (x : Quot (OrientableRel p 0))) γ.source)
      target' := Subtype.ext (congrArg (fun x : ↥(s78dg_cs_U p 0 ∩ s78dg_cs_V p 0) =>
        (x : Quot (OrientableRel p 0))) γ.target) }
  have hc : ∀ t : I, c t = s78dg_cs_Psi_fun p hp (half, 4 * (p : ℝ) * (t : ℝ)) := by
    intro t
    obtain ⟨x, hx, hxq⟩ := hγv t
    obtain ⟨z, hz, hz'⟩ := s78dg_cs_Psi_spec p hp half (4 * (p : ℝ) * (t : ℝ))
    have hN : (4 * (p : ℝ)) ≠ 0 := by positivity
    have hzx : z = x := by
      apply Subtype.ext
      rw [hz, hx, Complex.real_smul, Circle.coe_exp]
      have h1 : (4 * (p : ℝ) * (t : ℝ)) / (4 * p) = t := by field_simp
      rw [h1]
      congr 1
      congr 1
      push_cast; ring
    apply Subtype.ext
    rw [hz']
    show ((γ t : ↥(s78dg_cs_U p 0 ∩ s78dg_cs_V p 0)) : Quot (OrientableRel p 0)) = _
    rw [hxq, hzx]
  obtain ⟨r, hr⟩ := s78dg_cs_circle_conj p hp one hone half hhalf x₁ c hc β hβ
  let E : FundamentalGroup ↥(s78dg_cs_U p 0) x₁ ≃* FreeGroup (Fin p ⊕ Fin p) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPath r).trans (e.trans θ.symm)
  let eU : fundamentalGroupFactor (s78dg_cs_U p 0) (s78dg_cs_V p 0) (b : Quot (OrientableRel p 0)) hx₀
      false ≃* PresentedGroup (∅ : Set (FreeGroup (Fin p ⊕ Fin p))) := E.trans T
  let γ' : FundamentalGroup ↑(s78dg_cs_U p 0 ∩ s78dg_cs_V p 0)
      (overlapBasepoint (s78dg_cs_U p 0) (s78dg_cs_V p 0) (b : Quot (OrientableRel p 0)) hx₀) :=
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))⁻¹
  have hγ' : ∀ z, z ∈ Subgroup.zpowers γ' := fun z => by
    have := hγgen z
    rwa [← Subgroup.zpowers_inv] at this
  let w : FreeGroup (Fin p ⊕ Fin p) :=
    (List.ofFn fun i : Fin p =>
        FreeGroup.of (Sum.inl i : Fin p ⊕ Fin p) * FreeGroup.of (Sum.inr i) *
          (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod
  have hθw : θ w = (List.ofFn fun i : Fin p =>
      ((FreeGroup.of ⟨2 * (i : ℕ), by omega⟩ : FreeGroup (Fin (2 * p)))⁻¹ *
        (FreeGroup.of ⟨2 * (i : ℕ) + 1, by omega⟩)⁻¹ * FreeGroup.of ⟨2 * (i : ℕ), by omega⟩ *
          FreeGroup.of ⟨2 * (i : ℕ) + 1, by omega⟩)).prod := by
    simp only [w, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    simp [hθa i, hθb i]
  have hw : PresentedGroup.mk (∅ : Set (FreeGroup (Fin p ⊕ Fin p))) w =
      eU (fundamentalGroupAmalgamation (s78dg_cs_U p 0) (s78dg_cs_V p 0)
        (b : Quot (OrientableRel p 0)) hx₀ false γ') := by
    have h2 : FundamentalGroup.mapOfEq (interToLeft (s78dg_cs_U p 0) (s78dg_cs_V p 0))
        (interToLeft_overlapBasepoint (s78dg_cs_U p 0) (s78dg_cs_V p 0)
          (b : Quot (OrientableRel p 0)) hx₀) (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c) :=
      s78dg_pi1_mapOfEq_mk (interToLeft _ _) _ _
        (interToLeft_overlapBasepoint _ _ _ hx₀) γ c (fun t => rfl)
    have h1 : fundamentalGroupAmalgamation (s78dg_cs_U p 0) (s78dg_cs_V p 0)
        (b : Quot (OrientableRel p 0)) hx₀ false γ' =
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c))⁻¹ :=
      (map_inv (FundamentalGroup.mapOfEq (interToLeft (s78dg_cs_U p 0) (s78dg_cs_V p 0))
        (interToLeft_overlapBasepoint (s78dg_cs_U p 0) (s78dg_cs_V p 0)
          (b : Quot (OrientableRel p 0)) hx₀)) _).trans (congrArg _ h2)
    rw [h1]
    have h3 : eU (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c))⁻¹ =
        T (θ.symm ((e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk β)))⁻¹)) := by
      show T (E _) = _
      rw [map_inv]
      show T ((θ.symm (e (FundamentalGroup.fundamentalGroupMulEquivOfPath r
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk c)))))⁻¹) = _
      rw [hr, map_inv, map_inv]
      exact (map_inv T _).symm
    rw [h3, hW, ← hT, ← hθw]
    simp
  obtain ⟨e2⟩ := s78dg_svk_one_cell (s78dg_cs_U p 0) (s78dg_cs_V p 0) (s78dg_cs_U_open p 0)
    (s78dg_cs_V_open p 0) (s78dg_cs_cover p 0) (b : Quot (OrientableRel p 0)) hx₀ eU γ' hγ' w hw
  have hins : insert w (∅ : Set (FreeGroup (Fin p ⊕ Fin p))) = {w} := by
    ext x; simp
  rw [hins] at e2
  exact ⟨e2⟩


theorem s78dg_cs_closed_pathConnected (p : ℕ) (hp : 1 ≤ p) :
    PathConnectedSpace (Quot (OrientableRel p 0)) := by
  haveI := s78dg_cs_U_pathConnected p hp
  haveI := s78dg_cs_V_contractible p 0
  have hU : IsPathConnected (s78dg_cs_U p 0) := isPathConnected_iff_pathConnectedSpace.2 inferInstance
  have hV : IsPathConnected (s78dg_cs_V p 0) := isPathConnected_iff_pathConnectedSpace.2 inferInstance
  have hne : (s78dg_cs_U p 0 ∩ s78dg_cs_V p 0).Nonempty := by
    haveI := s78dg_cs_overlap_pathConnected p hp
    obtain ⟨b⟩ := (inferInstance : Nonempty ↥(s78dg_cs_U p 0 ∩ s78dg_cs_V p 0))
    exact ⟨b, b.2⟩
  have := hU.union hV hne
  rw [s78dg_cs_cover p 0] at this
  exact pathConnectedSpace_iff_univ.2 this

/-- **π₁ of the closed orientable surface of genus `p ≥ 1`** is the surface group, at every base
point: `⟨a₁, b₁, …, a_p, b_p | a₁b₁a₁⁻¹b₁⁻¹ ⋯ a_p b_p a_p⁻¹ b_p⁻¹⟩`. -/
theorem s78dg_cs_pi1_closed (p : ℕ) (hp : 1 ≤ p) (x : Quot (OrientableRel p 0)) :
    Nonempty (FundamentalGroup (Quot (OrientableRel p 0)) x ≃*
      PresentedGroup {(List.ofFn fun i : Fin p =>
        FreeGroup.of (Sum.inl i : Fin p ⊕ Fin p) * FreeGroup.of (Sum.inr i) *
          (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod}) := by
  obtain ⟨x₀, ⟨f⟩⟩ := s78dg_cs_pi1_closed_base p hp
  haveI := s78dg_cs_closed_pathConnected p hp
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x x₀).trans f⟩


end LiZhongQC
