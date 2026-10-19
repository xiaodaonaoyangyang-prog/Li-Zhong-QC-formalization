import LiZhongQC.Lemmas.SchottkyClosedSurface12
import Mathlib.Analysis.Normed.Module.Connected

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Topology unitInterval

universe u

namespace LiZhongQC

open DifferentialGeometry.Topology.VanKampen

/-- Transport of the fundamental group along a homeomorphism. -/
theorem s78dg_pi1_transport {S Q : Type*} [TopologicalSpace S] [TopologicalSpace Q] (e : S ≃ₜ Q)
    {G : Type*} [Group G] (h : ∀ y : Q, Nonempty (FundamentalGroup Q y ≃* G)) (x : S) :
    Nonempty (FundamentalGroup S x ≃* G) := by
  obtain ⟨f⟩ := h (e x)
  exact ⟨(MulEquiv.ofBijective (FundamentalGroup.map (⟨e, e.continuous⟩ : C(S, Q)) x)
    (s78dg_pi1_homeo_bijective e x)).trans f⟩

/-- **Van Kampen with simply connected pieces.**  A space covered by two open simply connected path
connected sets with path connected overlap is simply connected. -/
theorem s78dg_svk_trivial {X : Type u} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace U] [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))]
    [SimplyConnectedSpace U] [SimplyConnectedSpace V] :
    Subsingleton (FundamentalGroup X x₀) := by
  have h1 : Subsingleton (fundamentalGroupFactor U V x₀ hx₀ true) :=
    inferInstanceAs (Subsingleton (FundamentalGroup V (rightBasepoint V x₀ hx₀.2)))
  have h0 : Subsingleton (fundamentalGroupFactor U V x₀ hx₀ false) :=
    inferInstanceAs (Subsingleton (FundamentalGroup U (leftBasepoint U x₀ hx₀.1)))
  obtain ⟨e2⟩ := s78dg_pushoutI_one_trivial (fundamentalGroupAmalgamation U V x₀ hx₀)
  have hq : Subsingleton (fundamentalGroupFactor U V x₀ hx₀ false ⧸
      Subgroup.normalClosure ((fundamentalGroupAmalgamation U V x₀ hx₀ false).range :
        Set (fundamentalGroupFactor U V x₀ hx₀ false))) :=
    QuotientGroup.mk_surjective.subsingleton
  exact ((fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x₀ hx₀).symm.trans e2).injective.subsingleton

theorem s78dg_mulEquiv_of_subsingleton {G H : Type*} [Group G] [Group H] [Subsingleton G]
    [Subsingleton H] : Nonempty (G ≃* H) :=
  ⟨{ toFun := fun _ => 1
     invFun := fun _ => 1
     left_inv := fun x => Subsingleton.elim _ _
     right_inv := fun x => Subsingleton.elim _ _
     map_mul' := fun _ _ => (mul_one _).symm }⟩

theorem s78dg_free_fin_zero_subsingleton : Subsingleton (FreeGroup (Fin 0 ⊕ Fin 0)) := by
  refine ⟨fun a b => ?_⟩
  have h : ∀ x : FreeGroup (Fin 0 ⊕ Fin 0), x = 1 := by
    intro x
    induction x using FreeGroup.induction_on with
    | one => rfl
    | of a => rcases a with a | a <;> exact a.elim0
    | inv_of a _ => rcases a with a | a <;> exact a.elim0
    | mul _ _ h1 h2 => rw [h1, h2, mul_one]
  rw [h a, h b]

theorem s78dg_sphere_contractible {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] (w : Metric.sphere (0 : E) 1) :
    ContractibleSpace ↥(({w}ᶜ : Set (Metric.sphere (0 : E) 1))) := by
  let h : ↥(({w}ᶜ : Set (Metric.sphere (0 : E) 1))) ≃ₜ ↥(Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    (Homeomorph.setCongr (stereographic'_source (n := n) w).symm).trans
      (((stereographic' n w).toHomeomorphSourceTarget).trans
        (Homeomorph.setCongr (stereographic'_target (n := n) w)))
  haveI : ContractibleSpace ↥(Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    (convex_univ).contractibleSpace ⟨0, trivial⟩
  exact h.contractibleSpace

theorem s78dg_sphere_overlap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] (hn : 1 < n) (v : Metric.sphere (0 : E) 1) :
    IsPathConnected (({v}ᶜ : Set (Metric.sphere (0 : E) 1)) ∩ {-v}ᶜ) := by
  let e := stereographic' n v
  have hr : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; exact_mod_cast hn
  have hmv : (-v) ∈ e.source := by
    rw [stereographic'_source]
    intro h
    have h2 : (-v : Metric.sphere (0 : E) 1) = v := h
    have h3 : ((-v : Metric.sphere (0 : E) 1) : E) = (v : E) := congrArg Subtype.val h2
    have h4 : (v : E) = 0 := by
      have : -(v : E) = (v : E) := h3
      have h5 : (2 : ℝ) • (v : E) = 0 := by rw [two_smul]; nth_rewrite 1 [← this]; simp
      exact (smul_eq_zero.1 h5).resolve_left (by norm_num)
    have := v.2
    rw [h4] at this
    simp at this
  have hset : (({v}ᶜ : Set (Metric.sphere (0 : E) 1)) ∩ {-v}ᶜ) =
      e.symm '' ({e (-v)}ᶜ) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      have hxs : x ∈ e.source := by rw [stereographic'_source]; exact hx1
      refine ⟨e x, ?_, e.left_inv hxs⟩
      intro h
      exact hx2 (e.injOn hxs hmv h)
    · rintro ⟨y, hy, rfl⟩
      have hyt : y ∈ e.target := by rw [stereographic'_target]; trivial
      refine ⟨?_, ?_⟩
      · have := e.map_target hyt
        rw [stereographic'_source] at this
        exact this
      · intro h
        apply hy
        have : e (e.symm y) = e (-v) := congrArg e h
        rwa [e.right_inv hyt] at this
  rw [hset]
  refine (isPathConnected_compl_singleton_of_one_lt_rank hr _).image' ?_
  refine e.continuousOn_symm.mono ?_
  intro y _
  rw [stereographic'_target]; trivial

/-- **The sphere.**  `π₁(S², x)` is trivial, i.e. isomorphic to the genus-`0` surface group. -/
theorem s78dg_sphere_pi1 (x : SphereRepresentative) :
    Nonempty (FundamentalGroup SphereRepresentative x ≃*
      PresentedGroup {(List.ofFn fun i : Fin 0 =>
        FreeGroup.of (Sum.inl i : Fin 0 ⊕ Fin 0) * FreeGroup.of (Sum.inr i) *
          (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod}) := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hov := s78dg_sphere_overlap (n := 2) (E := EuclideanSpace ℝ (Fin 3)) (by norm_num) v
  haveI hcU := s78dg_sphere_contractible (n := 2) (E := EuclideanSpace ℝ (Fin 3)) v
  haveI hcV := s78dg_sphere_contractible (n := 2) (E := EuclideanSpace ℝ (Fin 3)) (-v)
  haveI : PathConnectedSpace ↥(({v}ᶜ : Set SphereRepresentative) ∩ {-v}ᶜ) :=
    isPathConnected_iff_pathConnectedSpace.1 hov
  have hcover : (({v}ᶜ : Set SphereRepresentative)) ∪ {-v}ᶜ = Set.univ := by
    ext y
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    by_contra h
    simp only [not_or, not_not] at h
    have h1 : y = v := h.1
    have h2 : y = -v := h.2
    have : v = -v := h1.symm.trans h2
    have h3 : ((-v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3)) =
        (v : EuclideanSpace ℝ (Fin 3)) := congrArg Subtype.val this.symm
    have h4 : (v : EuclideanSpace ℝ (Fin 3)) = 0 := by
      have h6 : -(v : EuclideanSpace ℝ (Fin 3)) = (v : EuclideanSpace ℝ (Fin 3)) := h3
      have h5 : (2 : ℝ) • (v : EuclideanSpace ℝ (Fin 3)) = 0 := by
        rw [two_smul]; nth_rewrite 1 [← h6]; simp
      exact (smul_eq_zero.1 h5).resolve_left (by norm_num)
    have := v.2
    rw [h4] at this
    simp at this
  haveI : PathConnectedSpace SphereRepresentative := by
    have h := (isPathConnected_iff_pathConnectedSpace.2 (inferInstance :
      PathConnectedSpace ↥(({v}ᶜ : Set SphereRepresentative)))).union
      (isPathConnected_iff_pathConnectedSpace.2 (inferInstance :
      PathConnectedSpace ↥(({-v}ᶜ : Set SphereRepresentative)))) (by
        obtain ⟨y, hy⟩ := hov.nonempty
        exact ⟨y, hy⟩)
    rw [hcover] at h
    exact pathConnectedSpace_iff_univ.2 h
  obtain ⟨x₀, hx₀⟩ := hov.nonempty
  haveI : Subsingleton (FundamentalGroup SphereRepresentative x₀) :=
    s78dg_svk_trivial ({v}ᶜ : Set SphereRepresentative) ({-v}ᶜ : Set SphereRepresentative)
      isOpen_compl_singleton isOpen_compl_singleton hcover x₀ hx₀
  haveI : Subsingleton (FundamentalGroup SphereRepresentative x) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x x₀).injective.subsingleton
  haveI := s78dg_free_fin_zero_subsingleton
  haveI : Subsingleton (PresentedGroup {(List.ofFn fun i : Fin 0 =>
        FreeGroup.of (Sum.inl i : Fin 0 ⊕ Fin 0) * FreeGroup.of (Sum.inr i) *
          (FreeGroup.of (Sum.inl i))⁻¹ * (FreeGroup.of (Sum.inr i))⁻¹).prod}) :=
    QuotientGroup.mk_surjective.subsingleton
  exact s78dg_mulEquiv_of_subsingleton

end LiZhongQC
