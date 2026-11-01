import LiZhongQC.Lemmas.SchottkyGenusBridge5
import LiZhongQC.Lemmas.SchottkyCollarConnectivity
import LiZhongQC.Lemmas.SchottkyHalfFundamentalEquivalence

universe u

namespace LiZhongQC

open Set Metric Topology DifferentialGeometry.Topology.VanKampen


theorem s78dg_dbl_half_open {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (Nu : Set (s31dt_Core F)) (hNu : IsOpen Nu)
    (hB : s31dt_boundary F ⊆ Nu) (b : Bool) :
    IsOpen (range (s31dt_side F b) ∪ s31dt_project F ⁻¹' Nu) := by
  haveI := s31dt_core_compact F
  haveI := s31dt_double_t2 F
  have hK : IsClosed ((s31dt_side F (!b)) '' Nuᶜ) :=
    (hNu.isClosed_compl.isCompact.image (s31dt_continuous_side F (!b))).isClosed
  have heq : range (s31dt_side F b) ∪ s31dt_project F ⁻¹' Nu =
      ((s31dt_side F (!b)) '' Nuᶜ)ᶜ := by
    ext q
    have hq : q ∈ range (s31dt_side F false) ∪ range (s31dt_side F true) := by
      rw [s31dt_side_cover F]; trivial
    obtain ⟨c, y, rfl⟩ : ∃ c y, q = s31dt_side F c y := by
      rcases hq with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨false, y, hy.symm⟩
      · exact ⟨true, y, hy.symm⟩
    simp only [mem_union, mem_range, mem_preimage, s31dt_project_side, mem_compl_iff, mem_image,
      not_exists, not_and]
    constructor
    · intro hq y' hy' hEq
      rw [s31dt_side_eq_iff] at hEq
      obtain ⟨rfl, hc⟩ := hEq
      rcases hq with ⟨x, hx⟩ | hy
      · rw [s31dt_side_eq_iff] at hx
        obtain ⟨rfl, hbc⟩ := hx
        rcases hbc with hbc | hbd
        · rcases hc with hc | hc
          · cases b <;> simp_all
          · exact hy' (hB hc)
        · exact hy' (hB hbd)
      · exact hy' hy
    · intro h
      by_cases hy : y ∈ Nu
      · exact Or.inr hy
      · cases c <;> cases b
        · exact Or.inl ⟨y, rfl⟩
        · exact absurd rfl (h y hy)
        · exact absurd rfl (h y hy)
        · exact Or.inl ⟨y, rfl⟩
  rw [heq]
  exact hK.isOpen_compl

theorem s78dg_dbl_inter {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (Nu : Set (s31dt_Core F))
    (hB : s31dt_boundary F ⊆ Nu) :
    (range (s31dt_side F false) ∪ s31dt_project F ⁻¹' Nu) ∩
      (range (s31dt_side F true) ∪ s31dt_project F ⁻¹' Nu) = s31dt_project F ⁻¹' Nu := by
  ext q
  constructor
  · rintro ⟨h0 | h0, h1 | h1⟩
    · obtain ⟨x, rfl⟩ := h0
      obtain ⟨y, hy⟩ := h1
      have := (s31dt_opposite_eq_iff F x y).mp hy.symm
      exact hB this.2
    · exact h1
    · exact h0
    · exact h0
  · intro h
    exact ⟨Or.inr h, Or.inr h⟩

theorem s78dg_dbl_loop_lift {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (b : Bool) (U : Set (s31dt_Double F))
    (e : C(s31dt_Core F, U)) (he : ∀ x, (e x).val = s31dt_side F b x) (x : s31dt_Core F)
    (hsurj : Function.Surjective (FundamentalGroup.map e x))
    (y : s31dt_Double F) (hxy : s31dt_side F b x = y) (ℓ : Path y y) (hℓ : range ℓ ⊆ U) :
    ∃ γ : FundamentalGroup (s31dt_Core F) x,
      FundamentalGroup.mapOfEq (⟨s31dt_side F b, s31dt_continuous_side F b⟩ :
        C(s31dt_Core F, s31dt_Double F)) hxy γ =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ) := by
  subst hxy
  let ℓU : Path (e x) (e x) :=
    { toFun := fun t => ⟨ℓ t, hℓ ⟨t, rfl⟩⟩
      continuous_toFun := ℓ.continuous.subtype_mk _
      source' := Subtype.ext (ℓ.source.trans (he x).symm)
      target' := Subtype.ext (ℓ.target.trans (he x).symm) }
  obtain ⟨γ, hγ⟩ := hsurj (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓU))
  refine ⟨γ, ?_⟩
  have hsd : (⟨s31dt_side F b, s31dt_continuous_side F b⟩ : C(s31dt_Core F, s31dt_Double F)) =
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, s31dt_Double F)).comp e := by
    ext z
    exact (he z).symm
  have hℓeq : ℓ = (ℓU.map continuous_subtype_val).cast (he x).symm (he x).symm := by
    ext t
    rfl
  suffices key : ∀ (f : C(s31dt_Core F, s31dt_Double F))
      (hf : f = (⟨Subtype.val, continuous_subtype_val⟩ : C(U, s31dt_Double F)).comp e)
      (hx : f x = s31dt_side F b x),
      FundamentalGroup.mapOfEq f hx γ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ) by
    exact key _ hsd _
  intro f hf hx
  subst hf
  have hγ' : Path.Homotopic.Quotient.map γ.asHom e = Path.Homotopic.Quotient.mk ℓU :=
    congrArg CategoryTheory.End.asHom hγ
  rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.map_comp, hγ', hℓeq]
  rw [Path.Homotopic.Quotient.mk_cast]
  rfl

theorem s78dg_dbl_side_path {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) [PathConnectedSpace (s31dt_Core F)] (s : Bool)
    (x y : s31dt_Core F) (hx : x ∈ s31dt_boundary F) (hy : y ∈ s31dt_boundary F) :
    ∃ b : Path (s31dt_side F false x) (s31dt_side F false y),
      range b ⊆ range (s31dt_side F s) := by
  have hxy : ∀ z, z ∈ s31dt_boundary F → s31dt_side F false z = s31dt_side F true z := fun z hz =>
    ((s31dt_opposite_eq_iff F z z).mpr ⟨rfl, hz⟩)
  let a : Path x y := PathConnectedSpace.somePath x y
  cases s
  · refine ⟨a.map (s31dt_continuous_side F false), ?_⟩
    rintro _ ⟨t, rfl⟩
    exact ⟨a t, rfl⟩
  · refine ⟨(a.map (s31dt_continuous_side F true)).cast (hxy x hx) (hxy y hy), ?_⟩
    rintro _ ⟨t, rfl⟩
    exact ⟨a t, rfl⟩

theorem s78dg_dbl_collar_facts {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m)
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ)
    (hR : ∀ j, 1 < R j) (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j)
    (p : Fin m → s31dt_Core F) (hp : ∀ j, (p j).val ∈ frontier (F.D j)) :
    IsOpen (⋃ j, (Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j)) : Set (s31dt_Core F))) ∧
      s31dt_boundary F ⊆ ⋃ j, (Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j)) : Set (s31dt_Core F)) ∧
      ∀ j, p j ∈ (Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j)) : Set (s31dt_Core F)) := by
  have hNopen : ∀ j, IsOpen (Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j)) : Set (s31dt_Core F)) :=
    fun j => ((v j).isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans (hs j))).preimage continuous_subtype_val
  refine ⟨isOpen_iUnion hNopen, ?_, ?_⟩
  · intro x hx
    obtain ⟨j, hj⟩ := hx
    have hxD : x.val ∈ F.D j := by
      have hc := frontier_subset_closure hj
      rwa [(s31eg_disc_compact (F.disc j)).isClosed.closure_eq] at hc
    obtain ⟨z, hz, hzx⟩ := (hD j).symm ▸ hxD
    exact mem_iUnion.mpr ⟨j, z,
      mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hz).trans_lt (hR j)), hzx⟩
  · intro j
    have hpD : (p j).val ∈ F.D j := by
      have hc := frontier_subset_closure (hp j)
      rwa [(s31eg_disc_compact (F.disc j)).isClosed.closure_eq] at hc
    obtain ⟨z, hz, hzp⟩ := (hD j).symm ▸ hpD
    exact ⟨z, mem_ball_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp hz).trans_lt (hR j)), hzp⟩

theorem s78dg_dbl_half_data {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m)
    (v : Fin m → OpenPartialHomeomorph ℂ F.X.carrier) (R : Fin m → ℝ)
    (hR : ∀ j, 1 < R j) (hs : ∀ j, closedBall (0 : ℂ) (R j) ⊆ (v j).source)
    (hD : ∀ j, v j '' closedBall (0 : ℂ) 1 = F.D j)
    (hdisj : Pairwise fun i j => Disjoint
      (v i '' closedBall (0 : ℂ) (R i)) (v j '' closedBall (0 : ℂ) (R j)))
    (b : Bool) :
    ∃ e : C(s31dt_Core F, ↥(range (s31dt_side F b) ∪
        s31dt_project F ⁻¹' (⋃ j, (Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j)) :
          Set (s31dt_Core F))))),
      (∀ x, (e x).val = s31dt_side F b x) ∧
        ∀ x, Function.Surjective (FundamentalGroup.map e x) := by
  obtain ⟨r, e, hre, hr, he, hE⟩ := s78dg_actual_half_core_equiv F v R hR hs hD hdisj b
  refine ⟨e, he, fun x => ?_⟩
  obtain ⟨E, hE1, -⟩ := hE x
  intro δ
  exact ⟨E.symm δ, by rw [← hE1]; exact E.apply_symm_apply δ⟩

theorem s78dg_double_generation {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
    [ConnectedSpace S] {g n m : ℕ} (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) :
    ∃ (x₀ : s31dt_Core F) (p : Fin m → s31dt_Core F),
      x₀ ∈ s31dt_boundary F ∧ (∀ j, (p j).val ∈ frontier (F.D j)) ∧
      ∀ H : Subgroup (FundamentalGroup (s31dt_Double F) (s31dt_side F false x₀)),
        (∀ (b : Bool) (e : s31dt_side F b x₀ = s31dt_side F false x₀)
          (γ : FundamentalGroup (s31dt_Core F) x₀),
          FundamentalGroup.mapOfEq (⟨s31dt_side F b, s31dt_continuous_side F b⟩ :
            C(s31dt_Core F, s31dt_Double F)) e γ ∈ H) →
        (∀ (j : Fin m) (a0 a1 : Path (s31dt_side F false x₀) (s31dt_side F false (p j))),
          range a0 ⊆ range (s31dt_side F false) → range a1 ⊆ range (s31dt_side F true) →
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (a0.trans a1.symm)) ∈ H) →
        H = ⊤ := by
  obtain ⟨v, R, hv, hd⟩ := s31sd_disjoint_disc_coordinates F
  obtain ⟨p, hpi, hp⟩ := s31sd_distinct_seam_points F
  have hR := fun k => (hv k).1
  have hs := fun k => (hv k).2.1
  have hD := fun k => (hv k).2.2.1
  obtain ⟨hWpath, hcore, hUpath, -, -⟩ := s31dt_actual_collar_path_data F v R hR hs hD hd p hp
  obtain ⟨hNuo, hBN, hpN⟩ := s78dg_dbl_collar_facts F v R hR hs hD p hp
  have hpos : 0 < m := Nat.pos_of_ne_zero hm
  have hbd : ∀ j, p j ∈ s31dt_boundary F := fun j => ⟨j, hp j⟩
  refine ⟨p ⟨0, hpos⟩, p, hbd _, hp, ?_⟩
  intro H hA hL
  letI := hcore
  let x₀ := p ⟨0, hpos⟩
  let Nu : Set (s31dt_Core F) :=
    ⋃ j, (Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j)) : Set (s31dt_Core F))
  let sd : Bool → Set (s31dt_Double F) := fun b => range (s31dt_side F b) ∪ s31dt_project F ⁻¹' Nu
  have hopen : ∀ b, IsOpen (sd b) := fun b => s78dg_dbl_half_open F Nu hNuo hBN b
  have hcover : sd true ∪ sd false = univ := by
    apply eq_univ_of_forall
    intro q
    have h : q ∈ range (s31dt_side F false) ∪ range (s31dt_side F true) := by
      rw [s31dt_side_cover F]; trivial
    rcases h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inl h)
  have hinter : sd false ∩ sd true = s31dt_project F ⁻¹' Nu := s78dg_dbl_inter F Nu hBN
  have hbx : ∀ z, z ∈ s31dt_boundary F → s31dt_side F false z = s31dt_side F true z :=
    fun z hz => (s31dt_opposite_eq_iff F z z).mpr ⟨rfl, hz⟩
  have hxy : ∀ b, s31dt_side F b x₀ = s31dt_side F false x₀ := by
    intro b
    cases b
    · rfl
    · exact (hbx _ (hbd _)).symm
  have hx0 : ∀ b, s31dt_side F false x₀ ∈ sd b := by
    intro b
    cases b
    · exact Or.inl ⟨x₀, rfl⟩
    · exact Or.inl ⟨x₀, hxy true⟩
  have hJ : ∀ b y, y ∈ sd b → JoinedIn (sd b) (s31dt_side F false x₀) y :=
    fun b y hy => (hUpath b).joinedIn _ (hx0 b) y hy
  let c : ∀ (b : Bool) (y : s31dt_Double F), y ∈ sd b → Path (s31dt_side F false x₀) y :=
    fun b y hy => (hJ b y hy).somePath
  have hc : ∀ b y (hy : y ∈ sd b), range (c b y hy) ⊆ sd b := by
    intro b y hy
    rintro _ ⟨t, rfl⟩
    exact (hJ b y hy).somePath_mem t
  let P : Path.Homotopic.Quotient (s31dt_side F false x₀) (s31dt_side F false x₀) → Prop :=
    fun a => FundamentalGroup.fromPath a ∈ H
  have hP : ∀ a b, P a → P b → P (a.trans b) := fun a b ha hb => H.mul_mem hb ha
  have hPs : ∀ b (ℓ : Path (s31dt_side F false x₀) (s31dt_side F false x₀)),
      range ℓ ⊆ sd b → P (Path.Homotopic.Quotient.mk ℓ) := by
    intro b ℓ hℓ
    obtain ⟨e, he, hsurj⟩ := s78dg_dbl_half_data F v R hR hs hD hd b
    obtain ⟨γ, hγ⟩ := s78dg_dbl_loop_lift F b (sd b) e he x₀ (hsurj x₀)
      (s31dt_side F false x₀) (hxy b) ℓ hℓ
    show FundamentalGroup.fromPath _ ∈ H
    rw [← hγ]
    exact hA b (hxy b) γ
  have hmu0 : ∀ (s s' : Bool) (q : s31dt_Double F) (hqs : q ∈ sd s) (hqs' : q ∈ sd s')
      (β β' : Path (s31dt_side F false x₀) q), range β ⊆ sd s → range β' ⊆ sd s' →
      P (Path.Homotopic.Quotient.mk (β.trans β'.symm)) →
      P ((Path.Homotopic.Quotient.mk (c s q hqs)).trans
        (Path.Homotopic.Quotient.mk (c s' q hqs')).symm) := by
    intro s s' q hqs hqs' β β' hβ hβ' hmid
    rw [← s78dg_gen_alg2 (Path.Homotopic.Quotient.mk (c s q hqs))
      (Path.Homotopic.Quotient.mk (c s' q hqs')) (Path.Homotopic.Quotient.mk β)
      (Path.Homotopic.Quotient.mk β')]
    refine hP _ _ (hP _ _ ?_ hmid) ?_
    · apply hPs s
      rw [Path.trans_range, Path.symm_range]
      exact union_subset (hc s q hqs) hβ
    · apply hPs s'
      rw [Path.trans_range, Path.symm_range]
      exact union_subset hβ' (hc s' q hqs')
  have hlam : ∀ (s s' : Bool) (z : s31dt_Double F) (hz : z ∈ sd s) (hz' : z ∈ sd s'),
      P ((Path.Homotopic.Quotient.mk (c s z hz)).trans
        (Path.Homotopic.Quotient.mk (c s' z hz')).symm) := by
    intro s s' z hz hz'
    by_cases hss : s = s'
    · subst hss
      show FundamentalGroup.fromPath _ ∈ H
      rw [Path.Homotopic.Quotient.trans_symm]
      exact H.one_mem
    · have hzF : z ∈ sd false := by
        cases s
        · exact hz
        · cases s'
          · exact hz'
          · exact absurd rfl hss
      have hzT : z ∈ sd true := by
        cases s
        · cases s'
          · exact absurd rfl hss
          · exact hz'
        · exact hz
      have hzW : z ∈ s31dt_project F ⁻¹' Nu := hinter ▸ ⟨hzF, hzT⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp hzW
      have hWsd : ∀ b, s31dt_project F ⁻¹' (Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j)) :
          Set (s31dt_Core F)) ⊆ sd b :=
        fun b y hy => Or.inr (mem_iUnion.mpr ⟨j, hy⟩)
      have hq : s31dt_side F false (p j) ∈ s31dt_project F ⁻¹'
          (Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j)) : Set (s31dt_Core F)) := hpN j
      obtain ⟨a, ha⟩ : ∃ a : Path (s31dt_side F false (p j)) z, range a ⊆ s31dt_project F ⁻¹'
          (Subtype.val ⁻¹' (v j '' ball (0 : ℂ) (R j)) : Set (s31dt_Core F)) := by
        have hJa := (hWpath j).joinedIn _ hq z hj
        exact ⟨hJa.somePath, by rintro _ ⟨t, rfl⟩; exact hJa.somePath_mem t⟩
      have hqs : ∀ b, s31dt_side F false (p j) ∈ sd b := fun b => hWsd b hq
      have hmu : P ((Path.Homotopic.Quotient.mk (c s _ (hqs s))).trans
          (Path.Homotopic.Quotient.mk (c s' _ (hqs s'))).symm) := by
        obtain ⟨bs, hbs⟩ := s78dg_dbl_side_path F s x₀ (p j) (hbd _) (hbd j)
        obtain ⟨bs', hbs'⟩ := s78dg_dbl_side_path F s' x₀ (p j) (hbd _) (hbd j)
        have hsub : ∀ b, range (s31dt_side F b) ⊆ sd b := fun b => subset_union_left
        refine hmu0 s s' _ (hqs s) (hqs s') bs bs' (hbs.trans (hsub s)) (hbs'.trans (hsub s')) ?_
        cases s
        · cases s'
          · exact absurd rfl hss
          · exact hL j bs bs' hbs hbs'
        · cases s'
          · have h1 := H.inv_mem (hL j bs' bs hbs' hbs)
            have h2 : Path.Homotopic.Quotient.mk (bs.trans bs'.symm) =
                (Path.Homotopic.Quotient.mk (bs'.trans bs.symm)).symm := by
              rw [← Path.Homotopic.Quotient.mk_symm]
              congr 1
              simp
            show FundamentalGroup.fromPath _ ∈ H
            rw [h2]
            exact h1
          · exact absurd rfl hss
      have e1 := s78dg_gen_lam_alg (Path.Homotopic.Quotient.mk (c s z hz))
        (Path.Homotopic.Quotient.mk (c s' z hz'))
        (Path.Homotopic.Quotient.mk (c s _ (hqs s)))
        (Path.Homotopic.Quotient.mk (c s' _ (hqs s'))) (Path.Homotopic.Quotient.mk a)
      rw [← e1]
      refine hP _ _ ?_ (hP _ _ hmu ?_)
      · apply hPs s
        rw [Path.trans_range, Path.trans_range, Path.symm_range, Path.symm_range]
        exact union_subset (union_subset (hc s z hz) ((ha.trans (hWsd s)))) (hc s _ (hqs s))
      · apply hPs s'
        rw [Path.trans_range, Path.trans_range, Path.symm_range]
        exact union_subset (union_subset (hc s' _ (hqs s')) (ha.trans (hWsd s'))) (hc s' z hz')
  have key := fun (ℓ : Path (s31dt_side F false x₀) (s31dt_side F false x₀)) =>
    s78dg_gen_two_cover sd hopen hcover (s31dt_side F false x₀) c hc P hP hPs hlam ℓ
  rw [eq_top_iff]
  intro γ _
  obtain ⟨ℓ, hℓ⟩ := Quotient.exists_rep (FundamentalGroup.toPath γ)
  obtain ⟨b, hb, h, hPh, heq⟩ := key ℓ
  have hγ : γ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ) :=
    CategoryTheory.End.ext hℓ.symm
  rw [hγ, heq]
  exact hP _ _ hPh (hPs b _ (hc b _ hb))

end LiZhongQC
