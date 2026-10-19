import LiZhongQC.Lemmas.FoundationQuotient
import LiZhongQC.Lemmas.JordanBridge
import LiZhongQC.Lemmas.CaratheodoryJordan

/-! F1 B6: fill all relatively compact complementary components (`ft1gb_fill_compact_holes`).
Jordan sides of the frontier loops (installed planar Jordan theorem) and of the proper
frontier lines (closed up through infinity on the sphere), local sides from the flat charts,
and the component classification of the complement. No new definitions. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- An embedded circle in the upper half-plane bounds a relatively compact inner side.
Both sides have the circle as frontier; the closed lower half-plane lies on the outer side. -/
theorem ft1fh_loop_sides (κ : Circle → UpperHalfPlane) (hκ : Continuous κ)
    (hinj : Function.Injective κ) :
    ∃ H E : Set UpperHalfPlane, IsOpen H ∧ IsOpen E ∧ Disjoint H E ∧
      H ∪ E = (Set.range κ)ᶜ ∧ frontier H = Set.range κ ∧ frontier E = Set.range κ ∧
      IsConnected H ∧ IsCompact (closure H) := by
  let ι : UpperHalfPlane → ℂ := fun z => (z : ℂ)
  have hιo : IsOpenMap ι := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap
  have hιc : Continuous ι := UpperHalfPlane.continuous_coe
  have hιinj : Function.Injective ι := UpperHalfPlane.isEmbedding_coe.injective
  have hrange : ∀ z : ℂ, 0 < z.im → z ∈ Set.range ι := fun z hz => ⟨⟨z, hz⟩, rfl⟩
  let C : Set ℂ := ι '' Set.range κ
  have hJ : IsJordanCurve (toExt C) := by
    refine ⟨fun c => ((κ c : ℂ) : ExtPlane), OnePoint.continuous_coe.comp (hιc.comp hκ),
      OnePoint.coe_injective.comp (hιinj.comp hinj), ?_⟩
    show Set.range ((fun z : ℂ => (z : ExtPlane)) ∘ ι ∘ κ) = _
    rw [Set.range_comp, Set.range_comp]
    rfl
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hAC, hBC, huniv, hAb, -⟩ :=
    jordan_curve_theorem_complex_bounded hJ
  obtain ⟨hfA, hfB⟩ :=
    frontier_pieces_eq_of_jordan_curve_theorem_complex hJ hA hB hAc hBc hAB hAC hBC huniv
  have hCup : ∀ z ∈ C, 0 < z.im := by
    rintro _ ⟨w, -, rfl⟩
    exact w.im_pos
  have hLB : {z : ℂ | z.im ≤ 0} ⊆ B := by
    have hsub : {z : ℂ | z.im ≤ 0} ⊆ A ∪ B := by
      intro z hz
      have hzC : z ∉ C := fun h => absurd (hCup z h) (not_lt.2 hz)
      have hz' : z ∈ A ∪ B ∪ C := by rw [huniv]; exact Set.mem_univ z
      rcases hz' with (h | h) | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hzC
    rcases (convex_halfSpace_im_le (r := 0)).isPreconnected.subset_or_subset hA hB hAB hsub
      with h | h
    · exfalso
      obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (hAb.subset h)
      have hz : (((|R| + 1 : ℝ)) : ℂ) ∈ {z : ℂ | z.im ≤ 0} := by
        show (((|R| + 1 : ℝ)) : ℂ).im ≤ 0
        rw [Complex.ofReal_im]
      have h1 := hR _ hz
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
      linarith [le_abs_self R]
    · exact h
  have hAup : ∀ z ∈ A, 0 < z.im := by
    intro z hz
    by_contra h
    exact Set.disjoint_left.1 hAB hz (hLB (not_lt.1 h))
  refine ⟨ι ⁻¹' A, ι ⁻¹' B, hA.preimage hιc, hB.preimage hιc, hAB.preimage ι, ?_, ?_, ?_, ?_, ?_⟩
  · ext z
    have hz : ι z ∈ A ∪ B ∪ C := by rw [huniv]; exact Set.mem_univ _
    have hzC : ι z ∈ C ↔ z ∈ Set.range κ := hιinj.mem_set_image
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff]
    constructor
    · rintro (h | h) hk
      · exact Set.disjoint_left.1 hAC h (hzC.2 hk)
      · exact Set.disjoint_left.1 hBC h (hzC.2 hk)
    · intro hk
      rcases hz with (h | h) | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (hzC.1 h) hk
  · rw [← hιo.preimage_frontier_eq_frontier_preimage hιc, hfA]
    exact hιinj.preimage_image _
  · rw [← hιo.preimage_frontier_eq_frontier_preimage hιc, hfB]
    exact hιinj.preimage_image _
  · refine ⟨?_, ?_⟩
    · obtain ⟨a, ha⟩ := hAc.nonempty
      exact ⟨⟨a, hAup a ha⟩, ha⟩
    · rw [← UpperHalfPlane.isEmbedding_coe.isInducing.isPreconnected_image,
        Set.image_preimage_eq_of_subset (fun z hz => hrange z (hAup z hz))]
      exact hAc.isPreconnected
  · rw [← hιo.preimage_closure_eq_closure_preimage hιc]
    have hcl : closure A ⊆ Set.range ι := by
      intro z hz
      rw [closure_eq_self_union_frontier, hfA] at hz
      rcases hz with hz | hz
      · exact hrange z (hAup z hz)
      · exact hrange z (hCup z hz)
    rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff, Set.image_preimage_eq_of_subset hcl]
    exact hAb.isCompact_closure

/-- The upper half-plane is homeomorphic to the plane, by `x + iy ↦ x + i log y`. -/
theorem ft1fh_homeo : Nonempty (UpperHalfPlane ≃ₜ ℂ) := by
  refine ⟨{
    toFun := fun z => (z.re : ℂ) + (Real.log z.im : ℂ) * Complex.I
    invFun := fun w => ⟨(w.re : ℂ) + (Real.exp w.im : ℂ) * Complex.I, by
      simp [-Complex.ofReal_exp, Real.exp_pos]⟩
    left_inv := fun z => by
      apply UpperHalfPlane.ext
      apply Complex.ext
      · simp
      · simp [Real.exp_log z.im_pos]
    right_inv := fun w => by
      apply Complex.ext
      · simp [-Complex.ofReal_exp]
      · simp [-Complex.ofReal_exp, Real.log_exp]
    continuous_toFun := by
      apply Continuous.add
      · exact Complex.continuous_ofReal.comp UpperHalfPlane.continuous_re
      · exact (Complex.continuous_ofReal.comp
          (UpperHalfPlane.continuous_im.log fun z => z.im_pos.ne')).mul continuous_const
    continuous_invFun := by
      rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
      exact (Complex.continuous_ofReal.comp Complex.continuous_re).add
        ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp Complex.continuous_im)).mul
          continuous_const) }⟩

/-- Three disjoint pieces with common frontier: if two disjoint open sets cover the
complement of `D` and `D` lies in both closures, both frontiers equal `D`. -/
theorem ft1fh_frontier_of_cover {X : Type*} [TopologicalSpace X] {P₁ P₂ D : Set X}
    (h₁ : IsOpen P₁) (h₂ : IsOpen P₂) (h12 : Disjoint P₁ P₂) (hcov : P₁ ∪ P₂ = Dᶜ)
    (hD₁ : D ⊆ closure P₁) (hD₂ : D ⊆ closure P₂) :
    frontier P₁ = D ∧ frontier P₂ = D := by
  have hP₁D : Disjoint P₁ D := by
    rw [Set.disjoint_right]
    intro x hx h
    have : x ∈ P₁ ∪ P₂ := Or.inl h
    rw [hcov] at this
    exact this hx
  have hP₂D : Disjoint P₂ D := by
    rw [Set.disjoint_right]
    intro x hx h
    have : x ∈ P₁ ∪ P₂ := Or.inr h
    rw [hcov] at this
    exact this hx
  have key : ∀ {P Q : Set X}, IsOpen P → IsOpen Q → Disjoint P Q → P ∪ Q = Dᶜ →
      Disjoint P D → D ⊆ closure P → frontier P = D := by
    intro P Q hP hQ hPQ hc hPD hDP
    rw [hP.frontier_eq]
    ext x
    constructor
    · rintro ⟨hx, hxP⟩
      by_contra hxD
      have : x ∈ P ∪ Q := by rw [hc]; exact hxD
      rcases this with h | h
      · exact hxP h
      · exact (Set.disjoint_left.1 (hPQ.closure_left hQ) hx) h
    · intro hx
      exact ⟨hDP hx, fun h => Set.disjoint_left.1 hPD h hx⟩
  exact ⟨key h₁ h₂ h12 hcov hP₁D hD₁, key h₂ h₁ h12.symm (by rw [Set.union_comm]; exact hcov) hP₂D hD₂⟩

/-- A spherical Jordan curve through infinity has exactly two complementary sides: open,
connected, disjoint, covering the complement, each with the curve as frontier. -/
theorem ft1fh_sphere_sides {C : Set ExtPlane} (hC : IsJordanCurve C) (hinf : extInf ∈ C) :
    ∃ P₁ P₂ : Set ExtPlane, IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧ P₁ ∪ P₂ = Cᶜ ∧
      frontier P₁ = C ∧ frontier P₂ = C ∧ IsConnected P₁ ∧ IsConnected P₂ := by
  obtain ⟨b, hb⟩ := s18v_c_exists_finite_notMem hC hinf
  let T := mobiusHomeomorph 0 1 1 (-b) (uq_j_inv_det b)
  have hTb : T (b : ExtPlane) = extInf := uq_j_mobiusInv_apply_self b
  have hinfTC : extInf ∉ T '' C := by
    rintro ⟨c, hc, hce⟩
    rw [← hTb] at hce
    rw [T.injective hce] at hc
    exact hb hc
  let C₀ : Set ℂ := ((↑) : ℂ → ExtPlane) ⁻¹' (T '' C)
  have hC₀e : toExt C₀ = T '' C := uq_j_toExt_preimage_coe hinfTC
  have hJ₀ : IsJordanCurve (toExt C₀) := by
    rw [hC₀e]
    exact uq_isJordanCurve_image T hC
  obtain ⟨A, B, hA, hB, hAc, hBc, hAB, hAC, hBC, huniv, hAb, hBb⟩ :=
    jordan_curve_theorem_complex_bounded hJ₀
  obtain ⟨hfA, hfB⟩ :=
    frontier_pieces_eq_of_jordan_curve_theorem_complex hJ₀ hA hB hAc hBc hAB hAC hBC huniv
  have hcompl : (A ∪ C₀)ᶜ = B := by
    ext z
    constructor
    · intro hz
      have hz' : z ∈ A ∪ B ∪ C₀ := by rw [huniv]; exact Set.mem_univ z
      rcases hz' with (h' | h') | h'
      · exact absurd (Or.inl h') hz
      · exact h'
      · exact absurd (Or.inr h') hz
    · rintro hz (h' | h')
      · exact Set.disjoint_left.1 hAB h' hz
      · exact Set.disjoint_left.1 hBC hz h'
  have hK : IsCompact (A ∪ C₀) := by
    refine Metric.isCompact_of_isClosed_isBounded ?_
      (hAb.union (isCompact_of_isJordanCurve_toExt hJ₀).isBounded)
    rw [← isOpen_compl_iff, hcompl]
    exact hB
  let Q₁ : Set ExtPlane := toExt A
  let Q₂ : Set ExtPlane := (toExt (A ∪ C₀))ᶜ
  have hQ₁o : IsOpen Q₁ := OnePoint.isOpen_image_coe.2 hA
  have hQ₂o : IsOpen Q₂ := OnePoint.isOpen_compl_image_coe.2 ⟨hK.isClosed, hK⟩
  have hQ12 : Disjoint Q₁ Q₂ := by
    show Disjoint (toExt A) (toExt (A ∪ C₀))ᶜ
    rw [disjoint_compl_right_iff_subset]
    exact Set.image_mono Set.subset_union_left
  have hQ₂eq : Q₂ = toExt B ∪ {extInf} := by
    ext p
    induction p using OnePoint.rec with
    | infty =>
      simp only [Q₂, Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, or_true, iff_true]
      rintro ⟨z, -, hz⟩
      exact OnePoint.coe_ne_infty z hz
    | coe z =>
      simp only [Q₂, Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff,
        OnePoint.coe_ne_infty, or_false, coe_mem_toExt_iff]
      constructor
      · intro h
        rw [← hcompl]
        exact h
      · intro h
        rw [← hcompl] at h
        exact h
  have hcov : Q₁ ∪ Q₂ = (T '' C)ᶜ := by
    rw [← hC₀e]
    ext p
    induction p using OnePoint.rec with
    | infty =>
      simp only [Set.mem_union, Set.mem_compl_iff]
      constructor
      · rintro - ⟨z, -, hz⟩
        exact OnePoint.coe_ne_infty z hz
      · intro _
        right
        rw [hQ₂eq]
        exact Or.inr rfl
    | coe z =>
      simp only [Q₁, Q₂, Set.mem_union, Set.mem_compl_iff, coe_mem_toExt_iff]
      constructor
      · rintro (h | h) hz
        · exact Set.disjoint_left.1 hAC h hz
        · exact h (Or.inr hz)
      · intro hz
        by_cases hzA : z ∈ A
        · exact Or.inl hzA
        · exact Or.inr (fun h => h.elim hzA hz)
  have hQ₁c : IsConnected Q₁ := hAc.image _ OnePoint.continuous_coe.continuousOn
  have hBcl : extInf ∈ closure (toExt B) := extInf_mem_closure_toExt_of_not_isBounded hBb
  have hQ₂c : IsConnected Q₂ := by
    have hBc' : IsConnected (toExt B) := hBc.image _ OnePoint.continuous_coe.continuousOn
    refine hBc'.subset_closure ?_ ?_
    · rw [hQ₂eq]
      exact Set.subset_union_left
    · rw [hQ₂eq]
      exact Set.union_subset subset_closure (Set.singleton_subset_iff.2 hBcl)
  have hD₁ : T '' C ⊆ closure Q₁ := by
    rw [← hC₀e]
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ closure A := by
      rw [← hfA] at hz
      exact frontier_subset_closure hz
    exact image_closure_subset_closure_image OnePoint.continuous_coe ⟨z, hz', rfl⟩
  have hD₂ : T '' C ⊆ closure Q₂ := by
    rw [← hC₀e]
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ closure B := by
      rw [← hfB] at hz
      exact frontier_subset_closure hz
    have h1 : ((z : ℂ) : ExtPlane) ∈ closure (toExt B) :=
      image_closure_subset_closure_image OnePoint.continuous_coe ⟨z, hz', rfl⟩
    refine closure_mono ?_ h1
    rw [hQ₂eq]
    exact Set.subset_union_left
  obtain ⟨hfQ₁, hfQ₂⟩ := ft1fh_frontier_of_cover hQ₁o hQ₂o hQ12 hcov hD₁ hD₂
  refine ⟨T ⁻¹' Q₁, T ⁻¹' Q₂, hQ₁o.preimage T.continuous, hQ₂o.preimage T.continuous,
    hQ12.preimage T, ?_, ?_, ?_, T.isConnected_preimage.2 hQ₁c, T.isConnected_preimage.2 hQ₂c⟩
  · rw [← Set.preimage_union, hcov, Set.preimage_compl, T.preimage_image]
  · rw [← T.preimage_frontier, hfQ₁, T.preimage_image]
  · rw [← T.preimage_frontier, hfQ₂, T.preimage_image]

/-- A proper embedded line in the plane, closed up at infinity, is a spherical Jordan curve.
The extended real line is reparametrized through the one-point extension of the line. -/
theorem ft1fh_line_jordan (σ : ℝ → ℂ) (hσ : Continuous σ) (hinj : Function.Injective σ)
    (hproper : ∀ K : Set ℂ, IsCompact K → IsCompact (σ ⁻¹' K)) :
    IsJordanCurve (toExt (Set.range σ) ∪ {extInf}) := by
  obtain ⟨γ₀, hγ₀c, hγ₀i, hγ₀r⟩ := tp_c1_isJordanCurve_extRealLine
  let m : OnePoint ℝ → ExtPlane := OnePoint.map (fun t : ℝ => (t : ℂ))
  have hmc : Continuous m := by
    refine OnePoint.continuous_map Complex.continuous_ofReal ?_
    rw [Filter.coclosedCompact_eq_cocompact, Filter.coclosedCompact_eq_cocompact]
    exact Complex.isometry_ofReal.isClosedEmbedding.tendsto_cocompact
  have hσt : Tendsto σ (coclosedCompact ℝ) (coclosedCompact ℂ) := by
    rw [Filter.coclosedCompact_eq_cocompact, Filter.coclosedCompact_eq_cocompact]
    exact (hasBasis_cocompact.tendsto_iff hasBasis_cocompact).2
      fun K hK => ⟨σ ⁻¹' K, hproper K hK, fun t ht => ht⟩
  have hmapσ : Continuous (OnePoint.map σ) := OnePoint.continuous_map hσ hσt
  have hmapσi : Function.Injective (OnePoint.map σ) := by
    intro p q hpq
    induction p using OnePoint.rec with
    | infty =>
      induction q using OnePoint.rec with
      | infty => rfl
      | coe t => exact absurd hpq.symm (OnePoint.coe_ne_infty (σ t))
    | coe s =>
      induction q using OnePoint.rec with
      | infty => exact absurd hpq (OnePoint.coe_ne_infty (σ s))
      | coe t => exact congrArg _ (hinj (OnePoint.coe_injective hpq))
  have hmi : Function.Injective m := by
    intro p q hpq
    induction p using OnePoint.rec with
    | infty =>
      induction q using OnePoint.rec with
      | infty => rfl
      | coe t => exact absurd hpq.symm (OnePoint.coe_ne_infty _)
    | coe s =>
      induction q using OnePoint.rec with
      | infty => exact absurd hpq (OnePoint.coe_ne_infty _)
      | coe t => exact congrArg _ (Complex.ofReal_injective (OnePoint.coe_injective hpq))
  have hmce : IsClosedEmbedding m := hmc.isClosedEmbedding hmi
  have hrm : Set.range m = toExt realLine ∪ {extInf} := by
    ext p
    induction p using OnePoint.rec with
    | infty =>
      simp only [Set.mem_union, Set.mem_singleton_iff, or_true, iff_true]
      exact ⟨OnePoint.infty, rfl⟩
    | coe z =>
      simp only [Set.mem_union, Set.mem_singleton_iff, OnePoint.coe_ne_infty, or_false,
        coe_mem_toExt_iff]
      constructor
      · rintro ⟨q, hq⟩
        induction q using OnePoint.rec with
        | infty => exact absurd hq.symm (OnePoint.coe_ne_infty z)
        | coe t =>
          have : (t : ℂ) = z := OnePoint.coe_injective hq
          rw [← this]
          show ((t : ℂ)).im = 0
          exact Complex.ofReal_im t
      · intro hz
        refine ⟨((z.re : ℝ) : OnePoint ℝ), ?_⟩
        show (((z.re : ℝ) : ℂ) : ExtPlane) = (z : ExtPlane)
        congr 1
        exact Complex.ext (by simp) (by simp [show z.im = 0 from hz])
  let G : ExtPlane → ExtPlane := OnePoint.map (fun z : ℂ => σ z.re)
  have hGm : G ∘ m = OnePoint.map σ := by
    funext p
    induction p using OnePoint.rec with
    | infty => rfl
    | coe t =>
      show (((σ ((t : ℂ)).re) : ℂ) : ExtPlane) = ((σ t : ℂ) : ExtPlane)
      rw [Complex.ofReal_re]
  have hGc : ContinuousOn G (Set.range m) := by
    rw [← Set.image_univ, hmce.isInducing.continuousOn_image_iff, hGm]
    exact hmapσ.continuousOn
  have hγ₀m : ∀ c, γ₀ c ∈ Set.range m := fun c => by
    rw [hrm, ← hγ₀r]
    exact Set.mem_range_self c
  refine ⟨G ∘ γ₀, hGc.comp_continuous hγ₀c hγ₀m, ?_, ?_⟩
  · intro c c' hcc
    obtain ⟨p, hp⟩ := hγ₀m c
    obtain ⟨q, hq⟩ := hγ₀m c'
    have h1 : OnePoint.map σ p = OnePoint.map σ q := by
      rw [← hGm]
      show G (m p) = G (m q)
      rw [hp, hq]
      exact hcc
    apply hγ₀i
    rw [← hp, ← hq, hmapσi h1]
  · rw [Set.range_comp, hγ₀r, ← hrm, ← Set.range_comp, hGm]
    ext p
    induction p using OnePoint.rec with
    | infty =>
      simp only [Set.mem_union, Set.mem_singleton_iff, or_true, iff_true]
      exact ⟨OnePoint.infty, rfl⟩
    | coe z =>
      simp only [Set.mem_union, Set.mem_singleton_iff, OnePoint.coe_ne_infty, or_false,
        coe_mem_toExt_iff]
      constructor
      · rintro ⟨q, hq⟩
        induction q using OnePoint.rec with
        | infty => exact absurd hq.symm (OnePoint.coe_ne_infty z)
        | coe t => exact ⟨t, OnePoint.coe_injective hq⟩
      · rintro ⟨t, rfl⟩
        exact ⟨(t : OnePoint ℝ), rfl⟩

/-- A proper embedded line in the upper half-plane has exactly two complementary sides:
open, connected, disjoint, covering the complement, each with the line as frontier. -/
theorem ft1fh_line_sides (ρ : ℝ → UpperHalfPlane) (hρ : Topology.IsEmbedding ρ)
    (hproper : ∀ L : Set UpperHalfPlane, IsCompact L → IsCompact (ρ ⁻¹' L)) :
    ∃ S₁ S₂ : Set UpperHalfPlane, IsOpen S₁ ∧ IsOpen S₂ ∧ Disjoint S₁ S₂ ∧
      S₁ ∪ S₂ = (Set.range ρ)ᶜ ∧ frontier S₁ = Set.range ρ ∧ frontier S₂ = Set.range ρ ∧
      IsConnected S₁ ∧ IsConnected S₂ := by
  obtain ⟨Φ⟩ := ft1fh_homeo
  let σ : ℝ → ℂ := fun t => Φ (ρ t)
  have hσc : Continuous σ := Φ.continuous.comp hρ.continuous
  have hσi : Function.Injective σ := Φ.injective.comp hρ.injective
  have hσp : ∀ K : Set ℂ, IsCompact K → IsCompact (σ ⁻¹' K) := fun K hK =>
    hproper _ (Φ.isCompact_preimage.2 hK)
  obtain ⟨P₁, P₂, hP₁, hP₂, hP12, hPcov, hfP₁, hfP₂, hP₁c, hP₂c⟩ :=
    ft1fh_sphere_sides (ft1fh_line_jordan σ hσc hσi hσp) (Or.inr rfl)
  let j : UpperHalfPlane → ExtPlane := fun z => ((Φ z : ℂ) : ExtPlane)
  have hjc : Continuous j := OnePoint.continuous_coe.comp Φ.continuous
  have hjo : IsOpenMap j := OnePoint.isOpenMap_coe.comp Φ.isOpenMap
  have hji : Function.Injective j := OnePoint.coe_injective.comp Φ.injective
  have hje : IsOpenEmbedding j := .of_continuous_injective_isOpenMap hjc hji hjo
  have hjC : j ⁻¹' (toExt (Set.range σ) ∪ {extInf}) = Set.range ρ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff, j,
      OnePoint.coe_ne_infty, or_false, coe_mem_toExt_iff]
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t, Φ.injective ht⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
  have hjr : ∀ P : Set ExtPlane, P ⊆ (toExt (Set.range σ) ∪ {extInf})ᶜ → j '' (j ⁻¹' P) = P := by
    intro P hP
    apply Set.image_preimage_eq_of_subset
    intro p hp
    induction p using OnePoint.rec with
    | infty => exact absurd (Or.inr rfl) (hP hp)
    | coe w => exact ⟨Φ.symm w, by simp [j]⟩
  have hsub₁ : P₁ ⊆ (toExt (Set.range σ) ∪ {extInf})ᶜ := by
    rw [← hPcov]; exact Set.subset_union_left
  have hsub₂ : P₂ ⊆ (toExt (Set.range σ) ∪ {extInf})ᶜ := by
    rw [← hPcov]; exact Set.subset_union_right
  have hconn : ∀ P : Set ExtPlane, P ⊆ (toExt (Set.range σ) ∪ {extInf})ᶜ → IsConnected P →
      IsConnected (j ⁻¹' P) := by
    intro P hP hPc
    have hPP := hjr P hP
    refine ⟨?_, ?_⟩
    · obtain ⟨p, hp⟩ := hPc.nonempty
      rw [← hPP] at hp
      obtain ⟨z, hz, -⟩ := hp
      exact ⟨z, hz⟩
    · rw [← hje.isInducing.isPreconnected_image, hPP]
      exact hPc.isPreconnected
  refine ⟨j ⁻¹' P₁, j ⁻¹' P₂, hP₁.preimage hjc, hP₂.preimage hjc, hP12.preimage j, ?_, ?_, ?_,
    hconn P₁ hsub₁ hP₁c, hconn P₂ hsub₂ hP₂c⟩
  · rw [← Set.preimage_union, hPcov, Set.preimage_compl, hjC]
  · rw [← hjo.preimage_frontier_eq_frontier_preimage hjc, hfP₁, hjC]
  · rw [← hjo.preimage_frontier_eq_frontier_preimage hjc, hfP₂, hjC]

/-- At a point of a flat frontier component `ℓ` with two complementary sides, one chart
neighborhood meets one side only inside `U` and the other side only outside `U`. -/
theorem ft1fh_chart_local {U ℓ S₁ S₂ : Set UpperHalfPlane} (hUc : IsClosed U)
    (hflat : ∀ p ∈ frontier U, ∃ e : OpenPartialHomeomorph UpperHalfPlane ℂ,
      p ∈ e.source ∧ e p = 0 ∧ e.target = ball 0 1 ∧
      ∀ x ∈ e.source, x ∈ U ↔ 0 ≤ (e x).im)
    (hℓ : ∀ p ∈ ℓ, connectedComponentIn (frontier U) p = ℓ)
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (h12 : Disjoint S₁ S₂) (hcov : S₁ ∪ S₂ = ℓᶜ)
    (hf₁ : frontier S₁ = ℓ) (hf₂ : frontier S₂ = ℓ)
    {p : UpperHalfPlane} (hp : p ∈ ℓ) :
    ∃ N : Set UpperHalfPlane, IsOpen N ∧ p ∈ N ∧
      ((N ∩ S₂ ⊆ U ∧ N ∩ S₁ ⊆ Uᶜ) ∨ (N ∩ S₁ ⊆ U ∧ N ∩ S₂ ⊆ Uᶜ)) := by
  have hℓF : ℓ ⊆ frontier U := fun x hx =>
    connectedComponentIn_subset _ _ (by rw [hℓ x hx]; exact hx)
  have hℓU : ℓ ⊆ U := hℓF.trans hUc.frontier_subset
  obtain ⟨e, hpe, hep, het, heU⟩ := hflat p (hℓF hp)
  let UH := e.source ∩ e ⁻¹' {w : ℂ | 0 < w.im}
  let L := e.source ∩ e ⁻¹' {w : ℂ | w.im < 0}
  let M := e.source ∩ e ⁻¹' ({w : ℂ | w.im ≤ 0} ∩ {w : ℂ | 0 ≤ w.im})
  have hUHo : IsOpen UH :=
    e.isOpen_inter_preimage (isOpen_lt continuous_const Complex.continuous_im)
  have hUHU : UH ⊆ U := fun x hx => (heU x hx.1).2 (le_of_lt hx.2)
  have hLU : L ⊆ Uᶜ := fun x hx h => absurd ((heU x hx.1).1 h) (not_le.2 hx.2)
  have hpre : ∀ s : Set ℂ, Convex ℝ s → IsPreconnected (e.source ∩ e ⁻¹' s) := by
    intro s hs
    have h : e.source ∩ e ⁻¹' s = e.symm '' (e.target ∩ s) :=
      (e.toPartialEquiv.symm_image_target_inter_eq' s).symm
    rw [h]
    apply IsPreconnected.image _ _ (e.continuousOn_symm.mono Set.inter_subset_left)
    rw [het]
    exact ((convex_ball 0 1).inter hs).isPreconnected
  have hUHc : IsPreconnected UH := hpre _ (convex_halfSpace_im_gt (r := 0))
  have hLc : IsPreconnected L := hpre _ (convex_halfSpace_im_lt (r := 0))
  have hMc : IsPreconnected M :=
    hpre _ ((convex_halfSpace_im_le (r := 0)).inter (convex_halfSpace_im_ge (r := 0)))
  -- the real-axis part of the chart lies in the frontier, hence in `ℓ`
  have hMF : M ⊆ frontier U := by
    intro x hx
    have hw0 : (e x).im = 0 := le_antisymm hx.2.1 hx.2.2
    refine ⟨subset_closure ((heU x hx.1).2 hx.2.2), fun hint => ?_⟩
    let w := e x
    have hwt : w ∈ e.target := e.map_source hx.1
    have hlin : Tendsto (fun ε : ℝ => w - (ε : ℂ) * Complex.I) (𝓝 0) (𝓝 w) := by
      have hc : Continuous (fun ε : ℝ => w - (ε : ℂ) * Complex.I) :=
        continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)
      simpa using hc.tendsto 0
    have hsym : Tendsto (fun ε : ℝ => e.symm (w - (ε : ℂ) * Complex.I)) (𝓝 0) (𝓝 x) := by
      have h := (e.continuousAt_symm hwt).tendsto.comp hlin
      rwa [Function.comp_def, e.left_inv hx.1] at h
    have hev1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, e.symm (w - (ε : ℂ) * Complex.I) ∈ interior U :=
      (hsym.eventually (isOpen_interior.mem_nhds hint)).filter_mono nhdsWithin_le_nhds
    have hev2 : ∀ᶠ ε : ℝ in 𝓝[>] 0, w - (ε : ℂ) * Complex.I ∈ e.target :=
      (hlin.eventually (e.open_target.mem_nhds hwt)).filter_mono nhdsWithin_le_nhds
    obtain ⟨ε, h1, h2, h3⟩ := (hev1.and (hev2.and self_mem_nhdsWithin)).exists
    have hy : e.symm (w - (ε : ℂ) * Complex.I) ∈ e.source := e.map_target h2
    have hyU := (heU _ hy).1 (interior_subset h1)
    rw [e.right_inv h2] at hyU
    have him : (w - (ε : ℂ) * Complex.I).im = -ε := by
      simp [w, hw0]
    rw [him] at hyU
    exact absurd hyU (not_le.2 (neg_neg_of_pos h3))
  have hpM : p ∈ M := ⟨hpe, by simp [hep]⟩
  have hMℓ : M ⊆ ℓ := by
    rw [← hℓ p hp]
    exact hMc.subset_connectedComponentIn hpM hMF
  have hSℓ : ∀ {S : Set UpperHalfPlane}, S ⊆ S₁ ∪ S₂ → ∀ x ∈ S, x ∉ ℓ := by
    intro S hS x hx hxℓ
    have : x ∈ S₁ ∪ S₂ := hS hx
    rw [hcov] at this
    exact this hxℓ
  have hUHℓ : UH ⊆ S₁ ∪ S₂ := by
    rw [hcov]
    intro x hx hxℓ
    exact (hℓF hxℓ).2 (interior_maximal hUHU hUHo hx)
  have hLℓ : L ⊆ S₁ ∪ S₂ := by
    rw [hcov]
    intro x hx hxℓ
    exact hLU hx (hℓU hxℓ)
  have hsplit : ∀ {S : Set UpperHalfPlane}, S ⊆ S₁ ∪ S₂ → e.source ∩ S ⊆ UH ∪ L := by
    intro S hS x hx
    rcases lt_trichotomy (e x).im 0 with h | h | h
    · exact Or.inr ⟨hx.1, h⟩
    · exact absurd (hMℓ ⟨hx.1, h.le, h.ge⟩) (hSℓ hS x hx.2)
    · exact Or.inl ⟨hx.1, h⟩
  have hne : ∀ {S : Set UpperHalfPlane}, frontier S = ℓ → (e.source ∩ S).Nonempty := by
    intro S hS
    have : p ∈ closure S := by
      rw [← hS] at hp
      exact frontier_subset_closure hp
    exact _root_.mem_closure_iff.1 this e.source e.open_source hpe
  have hsub₁ : S₁ ⊆ S₁ ∪ S₂ := Set.subset_union_left
  have hsub₂ : S₂ ⊆ S₁ ∪ S₂ := Set.subset_union_right
  refine ⟨e.source, e.open_source, hpe, ?_⟩
  rcases hUHc.subset_or_subset hS₁ hS₂ h12 hUHℓ with hU1 | hU2 <;>
    rcases hLc.subset_or_subset hS₁ hS₂ h12 hLℓ with hL1 | hL2
  · exfalso
    obtain ⟨x, hx⟩ := hne hf₂
    rcases hsplit hsub₂ hx with h | h
    · exact Set.disjoint_left.1 h12 (hU1 h) hx.2
    · exact Set.disjoint_left.1 h12 (hL1 h) hx.2
  · right
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rcases hsplit hsub₁ hx with h | h
      · exact hUHU h
      · exact absurd hx.2 (Set.disjoint_right.1 h12 (hL2 h))
    · rcases hsplit hsub₂ hx with h | h
      · exact absurd (hU1 h) (Set.disjoint_right.1 h12 hx.2)
      · exact hLU h
  · left
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rcases hsplit hsub₂ hx with h | h
      · exact hUHU h
      · exact absurd (hL1 h) (Set.disjoint_right.1 h12 hx.2)
    · rcases hsplit hsub₁ hx with h | h
      · exact absurd hx.2 (Set.disjoint_right.1 h12 (hU2 h))
      · exact hLU h
  · exfalso
    obtain ⟨x, hx⟩ := hne hf₁
    rcases hsplit hsub₁ hx with h | h
    · exact Set.disjoint_left.1 h12 hx.2 (hU2 h)
    · exact Set.disjoint_left.1 h12 hx.2 (hL2 h)

/-- If near every point of `ℓ` one side `S` lies outside `U` and the other inside, the
connected set `U` misses `S` entirely, and `Uᶜ` is locally inside `S` along `ℓ`. -/
theorem ft1fh_side_of_local {U ℓ S S' : Set UpperHalfPlane} (hUconn : IsPreconnected U)
    (hℓU : ℓ ⊆ U) (hℓne : ℓ.Nonempty) (hS : IsOpen S) (hS' : IsOpen S')
    (hSS' : Disjoint S S') (hcov : S ∪ S' = ℓᶜ)
    (hloc : ∀ p ∈ ℓ, ∃ N : Set UpperHalfPlane, IsOpen N ∧ p ∈ N ∧ N ∩ S' ⊆ U ∧ N ∩ S ⊆ Uᶜ) :
    Disjoint U S ∧ ∀ p ∈ ℓ, ∃ N ∈ 𝓝 p, N ∩ Uᶜ ⊆ S := by
  refine ⟨?_, ?_⟩
  · have hcl : ∀ x ∈ U, x ∈ closure (U ∩ S) → x ∈ S := by
      intro x hxU hx
      by_cases hxℓ : x ∈ ℓ
      · obtain ⟨N, hNo, hxN, -, hN⟩ := hloc x hxℓ
        obtain ⟨y, hyN, hyU, hyS⟩ := _root_.mem_closure_iff.1 hx N hNo hxN
        exact absurd hyU (hN ⟨hyN, hyS⟩)
      · have : x ∈ S ∪ S' := by rw [hcov]; exact hxℓ
        rcases this with h | h
        · exact h
        · obtain ⟨y, hyS', -, hyS⟩ := _root_.mem_closure_iff.1 hx S' hS' h
          exact absurd hyS (Set.disjoint_right.1 hSS' hyS')
    rcases isPreconnected_iff_subset_of_disjoint.1 hUconn S (closure (U ∩ S))ᶜ hS
      isClosed_closure.isOpen_compl (fun x hx => by
        by_cases hxS : x ∈ S
        · exact Or.inl hxS
        · exact Or.inr (fun h => hxS (hcl x hx h)))
      (by
        apply Set.eq_empty_iff_forall_notMem.2
        rintro x ⟨hxU, hxS, hxc⟩
        exact hxc (subset_closure ⟨hxU, hxS⟩)) with h | h
    · exfalso
      obtain ⟨q, hq⟩ := hℓne
      have h1 : q ∈ S ∪ S' := Or.inl (h (hℓU hq))
      rw [hcov] at h1
      exact h1 hq
    · exact Set.disjoint_left.2 fun x hxU hxS => h hxU (subset_closure ⟨hxU, hxS⟩)
  · intro p hp
    obtain ⟨N, hNo, hpN, hN', -⟩ := hloc p hp
    refine ⟨N, hNo.mem_nhds hpN, ?_⟩
    rintro x ⟨hxN, hxU⟩
    have hxℓ : x ∈ ℓᶜ := fun h => hxU (hℓU h)
    rw [← hcov] at hxℓ
    rcases hxℓ with h | h
    · exact h
    · exact absurd (hN' ⟨hxN, h⟩) hxU

/-- Side selection along a flat frontier component: exactly one complementary side misses the
connected closed set `U`, and `Uᶜ` lies locally in that side along the component. -/
theorem ft1fh_side_select {U ℓ S₁ S₂ : Set UpperHalfPlane} (hUc : IsClosed U)
    (hUconn : IsPreconnected U)
    (hflat : ∀ p ∈ frontier U, ∃ e : OpenPartialHomeomorph UpperHalfPlane ℂ,
      p ∈ e.source ∧ e p = 0 ∧ e.target = ball 0 1 ∧
      ∀ x ∈ e.source, x ∈ U ↔ 0 ≤ (e x).im)
    (hℓ : ∀ p ∈ ℓ, connectedComponentIn (frontier U) p = ℓ) (hℓne : ℓ.Nonempty)
    (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂) (h12 : Disjoint S₁ S₂) (hcov : S₁ ∪ S₂ = ℓᶜ)
    (hf₁ : frontier S₁ = ℓ) (hf₂ : frontier S₂ = ℓ) :
    (Disjoint U S₁ ∧ ∀ p ∈ ℓ, ∃ N ∈ 𝓝 p, N ∩ Uᶜ ⊆ S₁) ∨
      (Disjoint U S₂ ∧ ∀ p ∈ ℓ, ∃ N ∈ 𝓝 p, N ∩ Uᶜ ⊆ S₂) := by
  have hℓF : ℓ ⊆ frontier U := fun x hx =>
    connectedComponentIn_subset _ _ (by rw [hℓ x hx]; exact hx)
  have hℓU : ℓ ⊆ U := hℓF.trans hUc.frontier_subset
  obtain ⟨p₀, hp₀⟩ := hℓne
  have hℓc : IsPreconnected ℓ := by
    rw [← hℓ p₀ hp₀]
    exact isPreconnected_connectedComponentIn
  let O₁ := ⋃₀ {N : Set UpperHalfPlane | IsOpen N ∧ N ∩ S₂ ⊆ U ∧ N ∩ S₁ ⊆ Uᶜ}
  let O₂ := ⋃₀ {N : Set UpperHalfPlane | IsOpen N ∧ N ∩ S₁ ⊆ U ∧ N ∩ S₂ ⊆ Uᶜ}
  have hO₁ : IsOpen O₁ := isOpen_sUnion fun N hN => hN.1
  have hO₂ : IsOpen O₂ := isOpen_sUnion fun N hN => hN.1
  have hcover : ℓ ⊆ O₁ ∪ O₂ := by
    intro p hp
    obtain ⟨N, hNo, hpN, h | h⟩ := ft1fh_chart_local hUc hflat hℓ hS₁ hS₂ h12 hcov hf₁ hf₂ hp
    · exact Or.inl ⟨N, ⟨hNo, h⟩, hpN⟩
    · exact Or.inr ⟨N, ⟨hNo, h⟩, hpN⟩
  have hdisj : ℓ ∩ (O₁ ∩ O₂) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    rintro p ⟨hp, ⟨N₁, ⟨hN₁o, hN₁a, -⟩, hpN₁⟩, ⟨N₂, ⟨hN₂o, hN₂a, -⟩, hpN₂⟩⟩
    have hpc : p ∈ closure Uᶜ := by
      have := hℓF hp
      rw [← frontier_compl] at this
      exact frontier_subset_closure this
    obtain ⟨x, ⟨hx1, hx2⟩, hxU⟩ :=
      _root_.mem_closure_iff.1 hpc (N₁ ∩ N₂) (hN₁o.inter hN₂o) ⟨hpN₁, hpN₂⟩
    have hxℓ : x ∈ ℓᶜ := fun h => hxU (hℓU h)
    rw [← hcov] at hxℓ
    rcases hxℓ with h | h
    · exact hxU (hN₂a ⟨hx2, h⟩)
    · exact hxU (hN₁a ⟨hx1, h⟩)
  rcases isPreconnected_iff_subset_of_disjoint.1 hℓc O₁ O₂ hO₁ hO₂ hcover hdisj with h | h
  · left
    refine ft1fh_side_of_local hUconn hℓU ⟨p₀, hp₀⟩ hS₁ hS₂ h12 hcov fun p hp => ?_
    obtain ⟨N, ⟨hNo, hNa, hNb⟩, hpN⟩ := h hp
    exact ⟨N, hNo, hpN, hNa, hNb⟩
  · right
    refine ft1fh_side_of_local hUconn hℓU ⟨p₀, hp₀⟩ hS₂ hS₁ h12.symm
      (by rw [Set.union_comm]; exact hcov) fun p hp => ?_
    obtain ⟨N, ⟨hNo, hNa, hNb⟩, hpN⟩ := h hp
    exact ⟨N, hNo, hpN, hNa, hNb⟩

/-- A connected side `Y` of a curve `ℓ ⊆ U`, missing `U`, is a whole component of `Uᶜ`. -/
theorem ft1fh_side_component {U ℓ Y Y' : Set UpperHalfPlane} (hℓU : ℓ ⊆ U)
    (hY : IsOpen Y) (hY' : IsOpen Y') (hYY' : Disjoint Y Y') (hcov : Y ∪ Y' = ℓᶜ)
    (hYc : IsConnected Y) (hUY : Disjoint U Y) {x : UpperHalfPlane} (hx : x ∈ Y) :
    connectedComponentIn Uᶜ x = Y := by
  have hxU : x ∈ Uᶜ := fun h => Set.disjoint_left.1 hUY h hx
  apply Set.Subset.antisymm
  · have hsub : connectedComponentIn Uᶜ x ⊆ Y ∪ Y' := by
      intro z hz
      rw [hcov]
      exact fun hzℓ => connectedComponentIn_subset _ _ hz (hℓU hzℓ)
    rcases isPreconnected_connectedComponentIn.subset_or_subset hY hY' hYY' hsub with h | h
    · exact h
    · exact absurd (h (mem_connectedComponentIn hxU)) (Set.disjoint_left.1 hYY' hx)
  · exact hYc.isPreconnected.subset_connectedComponentIn hx
      (fun z hz h => Set.disjoint_left.1 hUY h hz)

/-- A component of `Uᶜ` accumulating at a point of `ℓ` is the adjacent side `Y`. -/
theorem ft1fh_component_eq_side {U ℓ Y Y' : Set UpperHalfPlane} (hℓU : ℓ ⊆ U)
    (hY : IsOpen Y) (hY' : IsOpen Y') (hYY' : Disjoint Y Y') (hcov : Y ∪ Y' = ℓᶜ)
    (hYc : IsConnected Y) (hUY : Disjoint U Y)
    (hloc : ∀ p ∈ ℓ, ∃ N ∈ 𝓝 p, N ∩ Uᶜ ⊆ Y)
    {z y : UpperHalfPlane} (hy : y ∈ ℓ) (hyf : y ∈ closure (connectedComponentIn Uᶜ z)) :
    connectedComponentIn Uᶜ z = Y := by
  obtain ⟨N, hN, hNY⟩ := hloc y hy
  obtain ⟨v, hvN, hvΩ⟩ := mem_closure_iff_nhds.1 hyf N hN
  have hvY : v ∈ Y := hNY ⟨hvN, connectedComponentIn_subset _ _ hvΩ⟩
  rw [connectedComponentIn_eq hvΩ]
  exact ft1fh_side_component hℓU hY hY' hYY' hcov hYc hUY hvY

/-- The frontier of a component of the complement of a closed set lies in its frontier. -/
theorem ft1fh_frontier_component_subset {U : Set UpperHalfPlane} (hUc : IsClosed U)
    (z : UpperHalfPlane) : frontier (connectedComponentIn Uᶜ z) ⊆ frontier U := by
  intro y hy
  have hΩo : IsOpen (connectedComponentIn Uᶜ z) := hUc.isOpen_compl.connectedComponentIn
  have hyU : y ∈ U := by
    by_contra hyU
    have hcy : IsOpen (connectedComponentIn Uᶜ y) := hUc.isOpen_compl.connectedComponentIn
    obtain ⟨v, hv1, hv2⟩ := _root_.mem_closure_iff.1 hy.1 _ hcy (mem_connectedComponentIn hyU)
    have h1 := connectedComponentIn_eq hv1
    have h2 := connectedComponentIn_eq hv2
    have hyΩ : y ∈ connectedComponentIn Uᶜ z := by
      rw [h2, ← h1]
      exact mem_connectedComponentIn hyU
    exact hy.2 (by rw [hΩo.interior_eq]; exact hyΩ)
  refine ⟨subset_closure hyU, fun hint => ?_⟩
  have h : y ∈ closure Uᶜ := closure_mono (connectedComponentIn_subset _ _) hy.1
  rw [closure_compl] at h
  exact h hint

/-- The upper half-plane is connected. -/
theorem ft1fh_connectedSpace : ConnectedSpace UpperHalfPlane := by
  have hc : Continuous (fun w : ℂ => (⟨(w.re : ℂ) + (Real.exp w.im : ℂ) * Complex.I, by
      simp [-Complex.ofReal_exp, Real.exp_pos]⟩ : UpperHalfPlane)) := by
    rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
    exact (Complex.continuous_ofReal.comp Complex.continuous_re).add
      ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp Complex.continuous_im)).mul
        continuous_const)
  refine Function.Surjective.connectedSpace (fun z => ⟨(z.re : ℂ) + (Real.log z.im : ℂ) * Complex.I,
    ?_⟩) hc
  apply UpperHalfPlane.ext
  apply Complex.ext
  · simp
  · simp [-Complex.ofReal_exp, Real.exp_log z.im_pos]

/-- A component of the complement of a nonempty closed proper subset has nonempty frontier. -/
theorem ft1fh_frontier_component_nonempty {U : Set UpperHalfPlane} (hUc : IsClosed U)
    (hUn : U.Nonempty) {z : UpperHalfPlane} (hz : z ∈ Uᶜ) :
    (frontier (connectedComponentIn Uᶜ z)).Nonempty := by
  have := ft1fh_connectedSpace
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hΩo : IsOpen (connectedComponentIn Uᶜ z) := hUc.isOpen_compl.connectedComponentIn
  have hΩcl : IsClosed (connectedComponentIn Uᶜ z) := by
    rw [← closure_subset_iff_isClosed, closure_eq_self_union_frontier, h, Set.union_empty]
  rcases isClopen_iff.1 ⟨hΩcl, hΩo⟩ with h1 | h1
  · rw [Set.eq_empty_iff_forall_notMem] at h1
    exact h1 z (mem_connectedComponentIn hz)
  · obtain ⟨u, hu⟩ := hUn
    have : u ∈ connectedComponentIn Uᶜ z := by rw [h1]; exact Set.mem_univ u
    exact connectedComponentIn_subset _ _ this hu

/-- Components of the complement of an invariant set are permuted by the group. -/
theorem ft1fh_component_smul {U : Set UpperHalfPlane}
    (hUi : ∀ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' U = U)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {z : UpperHalfPlane} (hz : z ∈ Uᶜ) :
    (fun τ : UpperHalfPlane => γ • τ) '' connectedComponentIn Uᶜ z =
      connectedComponentIn Uᶜ (γ • z) := by
  have h := (Homeomorph.smul γ : UpperHalfPlane ≃ₜ UpperHalfPlane).image_connectedComponentIn hz
  have hc : (Homeomorph.smul γ : UpperHalfPlane ≃ₜ UpperHalfPlane) '' Uᶜ = Uᶜ := by
    rw [Set.image_compl_eq (Homeomorph.smul γ).bijective]
    exact congrArg _ (hUi γ hγ)
  rw [hc] at h
  exact h

/-- A component of `Uᶜ` accumulating at a translated point of `ℓ` is the translated side. -/
theorem ft1fh_component_translate {U ℓ Y Y' : Set UpperHalfPlane}
    (hUi : ∀ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' U = U) (hℓU : ℓ ⊆ U)
    (hY : IsOpen Y) (hY' : IsOpen Y') (hYY' : Disjoint Y Y') (hcov : Y ∪ Y' = ℓᶜ)
    (hYc : IsConnected Y) (hUY : Disjoint U Y)
    (hloc : ∀ p ∈ ℓ, ∃ N ∈ 𝓝 p, N ∩ Uᶜ ⊆ Y)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {z y : UpperHalfPlane}
    (hz : z ∈ Uᶜ) (hy : y ∈ (fun τ : UpperHalfPlane => γ • τ) '' ℓ)
    (hyf : y ∈ closure (connectedComponentIn Uᶜ z)) :
    connectedComponentIn Uᶜ z = (fun τ : UpperHalfPlane => γ • τ) '' Y := by
  obtain ⟨k, hk, rfl⟩ := hy
  have hz' : γ⁻¹ • z ∈ Uᶜ := by
    intro h
    apply hz
    have : γ • (γ⁻¹ • z) ∈ (fun τ : UpperHalfPlane => γ • τ) '' U := ⟨_, h, rfl⟩
    rwa [hUi γ hγ, smul_inv_smul] at this
  have hΩ' := ft1fh_component_smul hUi (Γ.inv_mem hγ) hz
  have hkcl : k ∈ closure (connectedComponentIn Uᶜ (γ⁻¹ • z)) := by
    rw [← hΩ']
    have h := (Homeomorph.smul γ⁻¹ : UpperHalfPlane ≃ₜ UpperHalfPlane).image_closure
      (connectedComponentIn Uᶜ z)
    have hmem : γ⁻¹ • (γ • k) ∈
        (Homeomorph.smul γ⁻¹ : UpperHalfPlane ≃ₜ UpperHalfPlane) '' closure
          (connectedComponentIn Uᶜ z) := ⟨_, hyf, rfl⟩
    rw [h, inv_smul_smul] at hmem
    exact hmem
  have hside := ft1fh_component_eq_side hℓU hY hY' hYY' hcov hYc hUY hloc hk hkcl
  have hback := ft1fh_component_smul hUi hγ hz'
  rw [smul_inv_smul, hside] at hback
  exact hback.symm

/-- The orbit saturation of any set is invariant. -/
theorem ft1fh_saturation_inv (C : Set UpperHalfPlane) :
    ∀ δ ∈ Γ, (fun τ : UpperHalfPlane => δ • τ) ''
      (⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' C) =
      ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' C := by
  intro δ hδ
  ext x
  simp only [Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨y, ⟨γ, hγ, c, hc, rfl⟩, rfl⟩
    exact ⟨δ * γ, Γ.mul_mem hδ hγ, c, hc, mul_smul δ γ c⟩
  · rintro ⟨γ, hγ, c, hc, rfl⟩
    refine ⟨(δ⁻¹ * γ) • c, ⟨δ⁻¹ * γ, Γ.mul_mem (Γ.inv_mem hδ) hγ, c, hc, rfl⟩, ?_⟩
    rw [← mul_smul, mul_inv_cancel_left]

/-- B6. Fill ALL relatively compact complementary components using the finite compact-loop
orbit representatives. Construct the compact filled core and the uniquely determined exterior
side of each proper line. Exact coverage is part of the OUTPUT, not an assumed classification. -/
theorem ft1gb_fill_compact_holes (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {K U : Set UpperHalfPlane} (hK : IsCompact K)
    (hU : U = ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' K)
    (hUc : IsClosed U) (hUconn : IsConnected U) (hUb : ¬ Bornology.IsBounded U)
    (hUi : ∀ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' U = U)
    (hflat : ∀ p ∈ frontier U, ∃ e : OpenPartialHomeomorph UpperHalfPlane ℂ,
      p ∈ e.source ∧ e p = 0 ∧ e.target = ball 0 1 ∧
      ∀ x ∈ e.source, x ∈ U ↔ 0 ≤ (e x).im)
    (L N : ℕ) (κ : Fin L → Circle → UpperHalfPlane)
    (ρ : Fin N → ℝ → UpperHalfPlane)
    (h : Fin N → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hcurves : (∀ i, Topology.IsEmbedding (κ i) ∧
        Set.range (κ i) = connectedComponentIn (frontier U) (κ i 1)) ∧
      (∀ j, Topology.IsEmbedding (ρ j) ∧
        (∀ L : Set UpperHalfPlane, IsCompact L → IsCompact ((ρ j) ⁻¹' L)) ∧
        Set.range (ρ j) = connectedComponentIn (frontier U) (ρ j 0)) ∧
      (∀ j, h j ∈ Γ ∧ h j ≠ 1 ∧ h j ≠ -1 ∧
        ∀ t : ℝ, ρ j (t + 1) = h j • ρ j t) ∧
      (∀ i j γ, γ ∈ Γ →
        (((fun τ : UpperHalfPlane => γ • τ) '' Set.range (κ i)) ∩ Set.range (κ j)).Nonempty →
        i = j ∧ (γ = 1 ∨ γ = -1)) ∧
      (∀ i j γ, γ ∈ Γ →
        (((fun τ : UpperHalfPlane => γ • τ) '' Set.range (ρ i)) ∩ Set.range (ρ j)).Nonempty →
        i = j ∧ ∃ k : ℤ, γ = h i ^ k ∨ γ = -h i ^ k) ∧
      (∀ i j γ, γ ∈ Γ →
        Disjoint ((fun τ : UpperHalfPlane => γ • τ) '' Set.range (κ i)) (Set.range (ρ j))) ∧
      frontier U =
        (⋃ γ ∈ Γ, ⋃ i, (fun τ : UpperHalfPlane => γ • τ) '' Set.range (κ i)) ∪
        (⋃ γ ∈ Γ, ⋃ j, (fun τ : UpperHalfPlane => γ • τ) '' Set.range (ρ j))) :
    ∃ (H : Fin L → Set UpperHalfPlane) (C : Set UpperHalfPlane)
      (W : Fin N → Set UpperHalfPlane),
      let U₁ : Set UpperHalfPlane := ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' C
      (∀ i, IsOpen (H i) ∧ IsConnected (H i) ∧ IsCompact (closure (H i)) ∧
        Disjoint U (H i) ∧ frontier (H i) = Set.range (κ i) ∧
        ∀ x ∈ H i, connectedComponentIn Uᶜ x = H i) ∧
      C = K ∪ (⋃ i, closure (H i)) ∧ IsCompact C ∧
      IsConnected U₁ ∧ IsClosed U₁ ∧
      (∀ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' U₁ = U₁) ∧
      U₁ = U ∪ {x : UpperHalfPlane | ∃ y ∈ Uᶜ,
        x ∈ connectedComponentIn Uᶜ y ∧ IsCompact (closure (connectedComponentIn Uᶜ y))} ∧
      (∀ j, IsOpen (W j) ∧ IsConnected (W j) ∧ Disjoint U₁ (W j) ∧
        frontier (W j) = Set.range (ρ j) ∧
        (∀ x ∈ W j, connectedComponentIn U₁ᶜ x = W j) ∧
        ∀ V : Set UpperHalfPlane, IsOpen V → IsConnected V → Disjoint U₁ V →
          frontier V = Set.range (ρ j) → V = W j) ∧
      U₁ᶜ = ⋃ γ ∈ Γ, ⋃ j, (fun τ : UpperHalfPlane => γ • τ) '' W j := by
  -- The filling is purely topological: the frozen hypotheses `hΓ` and `hfree` (and the
  -- periodicity/precise-invariance parts of `hcurves`) are not needed, and the statement stays
  -- true without them.
  have _ := hΓ
  have _ := hfree
  obtain ⟨hκ, hρ, -, -, -, -, hFr⟩ := hcurves
  have hFU : frontier U ⊆ U := hUc.frontier_subset
  have hUconn' : IsPreconnected U := hUconn.isPreconnected
  have hUne : U.Nonempty := hUconn.nonempty
  have hUsmul : ∀ γ ∈ Γ, ∀ x : UpperHalfPlane, γ • x ∈ U ↔ x ∈ U := by
    intro γ hγ x
    constructor
    · intro h
      have : γ⁻¹ • (γ • x) ∈ (fun τ : UpperHalfPlane => γ⁻¹ • τ) '' U := ⟨_, h, rfl⟩
      rwa [hUi γ⁻¹ (Γ.inv_mem hγ), inv_smul_smul] at this
    · intro h
      have : γ • x ∈ (fun τ : UpperHalfPlane => γ • τ) '' U := ⟨x, h, rfl⟩
      rwa [hUi γ hγ] at this
  -- each loop and each line is a full frontier component
  have hℓκ : ∀ i, ∀ p ∈ Set.range (κ i), connectedComponentIn (frontier U) p = Set.range (κ i) := by
    intro i p hp
    rw [(hκ i).2] at hp ⊢
    exact (connectedComponentIn_eq hp).symm
  have hℓρ : ∀ j, ∀ p ∈ Set.range (ρ j), connectedComponentIn (frontier U) p = Set.range (ρ j) := by
    intro j p hp
    rw [(hρ j).2.2] at hp ⊢
    exact (connectedComponentIn_eq hp).symm
  have hκU : ∀ i, Set.range (κ i) ⊆ U := fun i => by
    rw [(hκ i).2]
    exact (connectedComponentIn_subset _ _).trans hFU
  have hρU : ∀ j, Set.range (ρ j) ⊆ U := fun j => by
    rw [(hρ j).2.2]
    exact (connectedComponentIn_subset _ _).trans hFU
  -- the holes: the bounded side of each loop misses `U` (otherwise `U` is bounded)
  have hHex : ∀ i, ∃ H H' : Set UpperHalfPlane, IsOpen H ∧ IsOpen H' ∧ Disjoint H H' ∧
      H ∪ H' = (Set.range (κ i))ᶜ ∧ frontier H = Set.range (κ i) ∧ IsConnected H ∧
      IsCompact (closure H) ∧ Disjoint U H ∧
      ∀ p ∈ Set.range (κ i), ∃ N ∈ 𝓝 p, N ∩ Uᶜ ⊆ H := by
    intro i
    obtain ⟨H, E, hHo, hEo, hHE, hcov, hfH, hfE, hHc, hHk⟩ :=
      ft1fh_loop_sides (κ i) (hκ i).1.continuous (hκ i).1.injective
    rcases ft1fh_side_select hUc hUconn' hflat (hℓκ i) (Set.range_nonempty _) hHo hEo hHE hcov
      hfH hfE with ⟨hUH, hloc⟩ | ⟨hUE, -⟩
    · exact ⟨H, E, hHo, hEo, hHE, hcov, hfH, hHc, hHk, hUH, hloc⟩
    · exfalso
      apply hUb
      refine hHk.isBounded.subset fun x hx => ?_
      by_cases hxℓ : x ∈ Set.range (κ i)
      · rw [← hfH] at hxℓ
        exact frontier_subset_closure hxℓ
      · have : x ∈ H ∪ E := by rw [hcov]; exact hxℓ
        rcases this with h | h
        · exact subset_closure h
        · exact absurd h (Set.disjoint_left.1 hUE hx)
  choose H H' hHo hH'o hHH' hHcov hHf hHc hHk hUH hHloc using hHex
  -- the exteriors: the side of each line missing `U`
  have hWex : ∀ j, ∃ W W' : Set UpperHalfPlane, IsOpen W ∧ IsOpen W' ∧ Disjoint W W' ∧
      W ∪ W' = (Set.range (ρ j))ᶜ ∧ frontier W = Set.range (ρ j) ∧ IsConnected W ∧
      Disjoint U W ∧ ∀ p ∈ Set.range (ρ j), ∃ N ∈ 𝓝 p, N ∩ Uᶜ ⊆ W := by
    intro j
    obtain ⟨S₁, S₂, h₁, h₂, h12, hcov, hf₁, hf₂, hc₁, hc₂⟩ :=
      ft1fh_line_sides (ρ j) (hρ j).1 (hρ j).2.1
    rcases ft1fh_side_select hUc hUconn' hflat (hℓρ j) (Set.range_nonempty _) h₁ h₂ h12 hcov
      hf₁ hf₂ with ⟨hU1, hl1⟩ | ⟨hU2, hl2⟩
    · exact ⟨S₁, S₂, h₁, h₂, h12, hcov, hf₁, hc₁, hU1, hl1⟩
    · exact ⟨S₂, S₁, h₂, h₁, h12.symm, by rw [Set.union_comm]; exact hcov, hf₂, hc₂, hU2, hl2⟩
  choose W W' hWo hW'o hWW' hWcov hWf hWc hUW hWloc using hWex
  have hHcomp : ∀ i, ∀ x ∈ H i, connectedComponentIn Uᶜ x = H i := fun i x hx =>
    ft1fh_side_component (hκU i) (hHo i) (hH'o i) (hHH' i) (hHcov i) (hHc i) (hUH i) hx
  have hWcomp : ∀ j, ∀ x ∈ W j, connectedComponentIn Uᶜ x = W j := fun j x hx =>
    ft1fh_side_component (hρU j) (hWo j) (hW'o j) (hWW' j) (hWcov j) (hWc j) (hUW j) hx
  have hWnc : ∀ j, ¬ IsCompact (closure (W j)) := by
    intro j hk
    have h1 : IsCompact (Set.range (ρ j)) := by
      rw [← hWf j]
      exact hk.of_isClosed_subset isClosed_frontier frontier_subset_closure
    have h2 := (hρ j).2.1 _ h1
    rw [Set.preimage_range] at h2
    exact noncompact_univ ℝ h2
  -- translated holes and exteriors
  have hHimgk : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) i,
      IsCompact (closure ((fun τ : UpperHalfPlane => γ • τ) '' H i)) := by
    intro γ i
    change IsCompact (closure ((Homeomorph.smul γ : UpperHalfPlane ≃ₜ UpperHalfPlane) '' H i))
    rw [← Homeomorph.image_closure]
    exact (hHk i).image (Homeomorph.smul γ).continuous
  have hWimgnc : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) j,
      ¬ IsCompact (closure ((fun τ : UpperHalfPlane => γ • τ) '' W j)) := by
    intro γ j hk
    change IsCompact (closure ((Homeomorph.smul γ : UpperHalfPlane ≃ₜ UpperHalfPlane) '' W j))
      at hk
    rw [← Homeomorph.image_closure] at hk
    have h := hk.image (Homeomorph.smul γ).symm.continuous
    rw [Set.image_image] at h
    simp only [Homeomorph.symm_apply_apply, Set.image_id'] at h
    exact hWnc j h
  have hHimg : ∀ γ ∈ Γ, ∀ i, ∀ x ∈ (fun τ : UpperHalfPlane => γ • τ) '' H i,
      connectedComponentIn Uᶜ x = (fun τ : UpperHalfPlane => γ • τ) '' H i := by
    rintro γ hγ i _ ⟨y, hy, rfl⟩
    have hyU : y ∈ Uᶜ := fun h => Set.disjoint_left.1 (hUH i) h hy
    show connectedComponentIn Uᶜ (γ • y) = _
    rw [← ft1fh_component_smul hUi hγ hyU, hHcomp i y hy]
  have hWimg : ∀ γ ∈ Γ, ∀ j, ∀ x ∈ (fun τ : UpperHalfPlane => γ • τ) '' W j,
      connectedComponentIn Uᶜ x = (fun τ : UpperHalfPlane => γ • τ) '' W j := by
    rintro γ hγ j _ ⟨y, hy, rfl⟩
    have hyU : y ∈ Uᶜ := fun h => Set.disjoint_left.1 (hUW j) h hy
    show connectedComponentIn Uᶜ (γ • y) = _
    rw [← ft1fh_component_smul hUi hγ hyU, hWcomp j y hy]
  -- every component of `Uᶜ` is a translated hole or a translated exterior
  have hclass : ∀ z ∈ Uᶜ,
      (∃ γ ∈ Γ, ∃ i, connectedComponentIn Uᶜ z = (fun τ : UpperHalfPlane => γ • τ) '' H i) ∨
        (∃ γ ∈ Γ, ∃ j, connectedComponentIn Uᶜ z = (fun τ : UpperHalfPlane => γ • τ) '' W j) := by
    intro z hz
    obtain ⟨y, hy⟩ := ft1fh_frontier_component_nonempty hUc hUne hz
    have hyF := ft1fh_frontier_component_subset hUc z hy
    rw [hFr] at hyF
    rcases hyF with hyF | hyF
    · obtain ⟨γ, hγ, hyi⟩ := Set.mem_iUnion₂.1 hyF
      obtain ⟨i, hyi⟩ := Set.mem_iUnion.1 hyi
      exact Or.inl ⟨γ, hγ, i, ft1fh_component_translate hUi (hκU i) (hHo i) (hH'o i) (hHH' i)
        (hHcov i) (hHc i) (hUH i) (hHloc i) hγ hz hyi (frontier_subset_closure hy)⟩
    · obtain ⟨γ, hγ, hyj⟩ := Set.mem_iUnion₂.1 hyF
      obtain ⟨j, hyj⟩ := Set.mem_iUnion.1 hyj
      exact Or.inr ⟨γ, hγ, j, ft1fh_component_translate hUi (hρU j) (hWo j) (hW'o j) (hWW' j)
        (hWcov j) (hWc j) (hUW j) (hWloc j) hγ hz hyj (frontier_subset_closure hy)⟩
  -- the filled core
  have hclH : ∀ i, closure (H i) = H i ∪ Set.range (κ i) := fun i => by
    rw [closure_eq_self_union_frontier, hHf i]
  let C : Set UpperHalfPlane := K ∪ ⋃ i, closure (H i)
  have hU₁eq : (⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' C) =
      U ∪ ⋃ γ ∈ Γ, ⋃ i, (fun τ : UpperHalfPlane => γ • τ) '' H i := by
    ext x
    constructor
    · intro hx
      obtain ⟨γ, hγ, c, hc, rfl⟩ := Set.mem_iUnion₂.1 hx
      rcases hc with hc | hc
      · left
        rw [hU]
        exact Set.mem_iUnion₂.2 ⟨γ, hγ, c, hc, rfl⟩
      · obtain ⟨i, hc⟩ := Set.mem_iUnion.1 hc
        rw [hclH i] at hc
        rcases hc with hc | hc
        · exact Or.inr (Set.mem_iUnion₂.2 ⟨γ, hγ, Set.mem_iUnion.2 ⟨i, c, hc, rfl⟩⟩)
        · exact Or.inl ((hUsmul γ hγ c).2 (hκU i hc))
    · rintro (hx | hx)
      · rw [hU] at hx
        obtain ⟨γ, hγ, c, hc, rfl⟩ := Set.mem_iUnion₂.1 hx
        exact Set.mem_iUnion₂.2 ⟨γ, hγ, c, Or.inl hc, rfl⟩
      · obtain ⟨γ, hγ, hx⟩ := Set.mem_iUnion₂.1 hx
        obtain ⟨i, c, hc, rfl⟩ := Set.mem_iUnion.1 hx
        exact Set.mem_iUnion₂.2 ⟨γ, hγ, c, Or.inr (Set.mem_iUnion.2 ⟨i, subset_closure hc⟩), rfl⟩
  refine ⟨H, C, W, ?_⟩
  intro U₁
  have hU₁ : U₁ = U ∪ ⋃ γ ∈ Γ, ⋃ i, (fun τ : UpperHalfPlane => γ • τ) '' H i := hU₁eq
  have hUU₁ : U ⊆ U₁ := by rw [hU₁]; exact Set.subset_union_left
  have h9 : U₁ᶜ = ⋃ γ ∈ Γ, ⋃ j, (fun τ : UpperHalfPlane => γ • τ) '' W j := by
    ext x
    constructor
    · intro hx
      have hxU : x ∈ Uᶜ := fun h => hx (hUU₁ h)
      have hxc := mem_connectedComponentIn hxU
      rcases hclass x hxU with ⟨γ, hγ, i, hcc⟩ | ⟨γ, hγ, j, hcc⟩
      · exfalso
        apply hx
        rw [hcc] at hxc
        rw [hU₁]
        exact Or.inr (Set.mem_iUnion₂.2 ⟨γ, hγ, Set.mem_iUnion.2 ⟨i, hxc⟩⟩)
      · rw [hcc] at hxc
        exact Set.mem_iUnion₂.2 ⟨γ, hγ, Set.mem_iUnion.2 ⟨j, hxc⟩⟩
    · intro hx hxU₁
      obtain ⟨γ, hγ, hx⟩ := Set.mem_iUnion₂.1 hx
      obtain ⟨j, hx⟩ := Set.mem_iUnion.1 hx
      have e1 := hWimg γ hγ j x hx
      rw [hU₁] at hxU₁
      rcases hxU₁ with h | h
      · obtain ⟨w, hw, rfl⟩ := hx
        exact Set.disjoint_left.1 (hUW j) ((hUsmul γ hγ w).1 h) hw
      · obtain ⟨δ, hδ, h⟩ := Set.mem_iUnion₂.1 h
        obtain ⟨i, h⟩ := Set.mem_iUnion.1 h
        have e2 := hHimg δ hδ i x h
        rw [e1] at e2
        exact hWimgnc γ j (by rw [e2]; exact hHimgk δ i)
  have h5 : IsClosed U₁ := by
    rw [← isOpen_compl_iff, h9]
    exact isOpen_biUnion fun γ _ => isOpen_iUnion fun j =>
      (Homeomorph.smul γ : UpperHalfPlane ≃ₜ UpperHalfPlane).isOpenMap _ (hWo j)
  have h7 : U₁ = U ∪ {x : UpperHalfPlane | ∃ y ∈ Uᶜ,
      x ∈ connectedComponentIn Uᶜ y ∧ IsCompact (closure (connectedComponentIn Uᶜ y))} := by
    rw [hU₁]
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl hx
      · obtain ⟨γ, hγ, hx⟩ := Set.mem_iUnion₂.1 hx
        obtain ⟨i, hx⟩ := Set.mem_iUnion.1 hx
        have hcc := hHimg γ hγ i x hx
        have hxU : x ∈ Uᶜ := by
          obtain ⟨y, hy, rfl⟩ := hx
          exact fun h => Set.disjoint_left.1 (hUH i) ((hUsmul γ hγ y).1 h) hy
        refine Or.inr ⟨x, hxU, mem_connectedComponentIn hxU, ?_⟩
        rw [hcc]
        exact hHimgk γ i
    · rintro (hx | ⟨y, hyU, hxy, hyk⟩)
      · exact Or.inl hx
      · right
        rcases hclass y hyU with ⟨γ, hγ, i, hcc⟩ | ⟨γ, hγ, j, hcc⟩
        · rw [hcc] at hxy
          exact Set.mem_iUnion₂.2 ⟨γ, hγ, Set.mem_iUnion.2 ⟨i, hxy⟩⟩
        · exfalso
          rw [hcc] at hyk
          exact hWimgnc γ j hyk
  have h8 : ∀ j, IsOpen (W j) ∧ IsConnected (W j) ∧ Disjoint U₁ (W j) ∧
      frontier (W j) = Set.range (ρ j) ∧
      (∀ x ∈ W j, connectedComponentIn U₁ᶜ x = W j) ∧
      ∀ V : Set UpperHalfPlane, IsOpen V → IsConnected V → Disjoint U₁ V →
        frontier V = Set.range (ρ j) → V = W j := by
    intro j
    have hdisj : Disjoint U₁ (W j) := by
      rw [Set.disjoint_right]
      intro w hw hwU₁
      have : w ∈ U₁ᶜ := by
        rw [h9]
        exact Set.mem_iUnion₂.2 ⟨1, Γ.one_mem, Set.mem_iUnion.2 ⟨j, w, hw, one_smul _ w⟩⟩
      exact this hwU₁
    refine ⟨hWo j, hWc j, hdisj, hWf j, ?_, ?_⟩
    · intro x hx
      apply Set.Subset.antisymm
      · rw [← hWcomp j x hx]
        exact connectedComponentIn_mono x (Set.compl_subset_compl.2 hUU₁)
      · exact (hWc j).isPreconnected.subset_connectedComponentIn hx
          (fun w hw h => Set.disjoint_left.1 hdisj h hw)
    · intro V hVo hVc hU₁V hfV
      have hVU : Disjoint U V := Set.disjoint_of_subset_left hUU₁ hU₁V
      obtain ⟨y, hy⟩ : (Set.range (ρ j)).Nonempty := Set.range_nonempty _
      obtain ⟨N, hN, hNW⟩ := hWloc j y hy
      have hycl : y ∈ closure V := by
        rw [← hfV] at hy
        exact frontier_subset_closure hy
      obtain ⟨v, hvN, hvV⟩ := mem_closure_iff_nhds.1 hycl N hN
      have hvW : v ∈ W j := hNW ⟨hvN, fun h => Set.disjoint_left.1 hVU h hvV⟩
      have hVW : V ⊆ W j := by
        rw [← hWcomp j v hvW]
        exact hVc.isPreconnected.subset_connectedComponentIn hvV
          (fun x hx h => Set.disjoint_left.1 hVU h hx)
      apply Set.Subset.antisymm hVW
      apply (hWc j).isPreconnected.subset_of_closure_inter_subset hVo ⟨v, hvW, hvV⟩
      rintro x ⟨hxcl, hxW⟩
      rw [closure_eq_self_union_frontier, hfV] at hxcl
      rcases hxcl with h | h
      · exact h
      · exact absurd (hρU j h) (Set.disjoint_right.1 (hUW j) hxW)
  have h4 : IsConnected U₁ := by
    obtain ⟨u₀, hu₀⟩ := hUne
    let P : (Γ × Fin L) → Set UpperHalfPlane := fun q =>
      U ∪ (fun τ : UpperHalfPlane => q.1.1 • τ) '' closure (H q.2)
    have hPc : ∀ q, IsConnected (P q) := by
      intro q
      refine IsConnected.union ?_ hUconn ((hHc q.2).closure.image _
        (continuous_const_smul _).continuousOn)
      refine ⟨q.1.1 • κ q.2 1, (hUsmul q.1.1 q.1.2 _).2 (hκU q.2 (Set.mem_range_self 1)),
        κ q.2 1, ?_, rfl⟩
      rw [hclH q.2]
      exact Or.inr (Set.mem_range_self 1)
    have hU₁s : U₁ = ⋃₀ (insert U (Set.range P)) := by
      rw [hU₁]
      ext x
      simp only [Set.sUnion_insert, Set.mem_union, Set.sUnion_range, Set.mem_iUnion]
      constructor
      · rintro (hx | hx)
        · exact Or.inl hx
        · obtain ⟨γ, hγ, i, c, hc, rfl⟩ := hx
          exact Or.inr ⟨(⟨γ, hγ⟩, i), Or.inr ⟨c, subset_closure hc, rfl⟩⟩
      · rintro (hx | ⟨q, hx | hx⟩)
        · exact Or.inl hx
        · exact Or.inl hx
        · obtain ⟨c, hc, rfl⟩ := hx
          rw [hclH q.2] at hc
          rcases hc with hc | hc
          · exact Or.inr ⟨q.1.1, q.1.2, q.2, c, hc, rfl⟩
          · exact Or.inl ((hUsmul q.1.1 q.1.2 c).2 (hκU q.2 hc))
    refine ⟨⟨u₀, hUU₁ hu₀⟩, ?_⟩
    rw [hU₁s]
    refine isPreconnected_sUnion u₀ _ ?_ ?_
    · rintro s (rfl | ⟨q, rfl⟩)
      · exact hu₀
      · exact Or.inl hu₀
    · rintro s (rfl | ⟨q, rfl⟩)
      · exact hUconn'
      · exact (hPc q).isPreconnected
  exact ⟨fun i => ⟨hHo i, hHc i, hHk i, hUH i, hHf i, hHcomp i⟩, rfl,
    hK.union (isCompact_iUnion hHk), h4, h5, ft1fh_saturation_inv C, h7, h8, h9⟩

end LiZhongQC
