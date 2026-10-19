import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Ch08.S29_TeichmullerMetric
import LiZhongQC.Lemmas.UniformizedTeichmuller
import LiZhongQC.Lemmas.SchottkyCollarFromDouble
import LiZhongQC.Lemmas.QDDimension

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u


/-- The local expression of a restriction to an open subset is the local expression of the ambient map. -/
theorem s82cmp_opens_localMapExpr {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    (U : TopologicalSpace.Opens X) {J : X ≃ₜ X} (Ju : U ≃ₜ U) (hJu : ∀ y, (Ju y : X) = J y) (x : U) :
    ∀ z ∈ (chartAt ℂ x).target, localMapExpr Ju x z = localMapExpr J (x : X) z := by
  intro z hz
  have hne : Nonempty U := ⟨x⟩
  have hsymm : (((chartAt ℂ x).symm z : U) : X) = (chartAt ℂ (x : X)).symm z :=
    OpenPartialHomeomorph.subtypeRestr_symm_apply (chartAt ℂ (x : X)) hne hz
  simp only [localMapExpr]
  show chartAt ℂ ((Ju x : U) : X) ((Ju ((chartAt ℂ x).symm z) : U) : X) =
    chartAt ℂ (J (x : X)) (J ((chartAt ℂ (x : X)).symm z))
  rw [hJu, hJu, hsymm]

/-- The restriction of an anticonformal involution to an invariant open subset is an anticonformal involution. -/
theorem s82cmp_opens_involution {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (U : TopologicalSpace.Opens X) {J : X ≃ₜ X} (hJ : IsAnticonformalInvolution J)
    (Ju : U ≃ₜ U) (hJu : ∀ y, (Ju y : X) = J y) : IsAnticonformalInvolution Ju := by
  refine ⟨fun y => Subtype.ext (by rw [hJu, hJu]; exact hJ.1 y), fun x z hz => ?_⟩
  have hne : Nonempty U := ⟨x⟩
  have hzt : z ∈ (chartAt ℂ x).target := hz.1
  have hz' : z ∈ (chartAt ℂ (x : X)).target :=
    OpenPartialHomeomorph.subtypeRestr_target_subset (chartAt ℂ (x : X)) hne hzt
  have hsymm : (((chartAt ℂ x).symm z : U) : X) = (chartAt ℂ (x : X)).symm z :=
    OpenPartialHomeomorph.subtypeRestr_symm_apply (chartAt ℂ (x : X)) hne hzt
  have hdomJ : z ∈ localMapDomain J (x : X) := by
    refine ⟨hz', ?_⟩
    show J ((chartAt ℂ (x : X)).symm z) ∈ (chartAt ℂ (J (x : X))).source
    have h2 : Ju ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (Ju x)).source := hz.2
    have h3 : ((Ju ((chartAt ℂ x).symm z) : U) : X) ∈ (chartAt ℂ ((Ju x : U) : X)).source := by
      have h2' := h2
      rwa [show chartAt ℂ (Ju x) = (chartAt ℂ ((Ju x : U) : X)).subtypeRestr ⟨Ju x⟩ from rfl,
        OpenPartialHomeomorph.subtypeRestr_source] at h2'
    rw [hJu, hJu, hsymm] at h3
    exact h3
  have hdiffJ : DifferentiableAt ℂ (fun w => conj (localMapExpr J (x : X) w)) z :=
    (hJ.2 (x : X)).differentiableAt ((s23_localMapDomain_isOpen J.continuous (x : X)).mem_nhds hdomJ)
  have hev : (fun w => conj (localMapExpr Ju x w)) =ᶠ[𝓝 z] fun w => conj (localMapExpr J (x : X) w) := by
    filter_upwards [(chartAt ℂ x).open_target.mem_nhds hzt] with w hw
    rw [s82cmp_opens_localMapExpr U Ju hJu x w hw]
  exact (hdiffJ.congr_of_eventuallyEq hev).differentiableWithinAt


/-- The double of a non-exceptional type `(g, n, m)`, `m ≠ 0`, is of non-exceptional type `(2g + m - 1, 2n, 0)`. -/
theorem s82cmp_hex_double {g n m : ℕ} (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m) :
    ¬ IsExceptionalType (2 * g + m - 1) (2 * n) 0 := by
  intro h
  unfold IsExceptionalType at h
  rcases h with h | h | h | h | h | h | h
  · have hgd : 2 * g + m - 1 = 0 := congrArg Prod.fst h
    have hnd : 2 * n = 0 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h
    have hg0 : g = 0 := by omega
    have hn0 : n = 0 := by omega
    have hm1 : m = 1 := by omega
    exact hex (by simp [IsExceptionalType, hg0, hn0, hm1])
  · have hnd : 2 * n = 1 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h
    omega
  · have hgd : 2 * g + m - 1 = 1 := congrArg Prod.fst h
    have hnd : 2 * n = 0 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h
    have hg0 : g = 0 := by omega
    have hn0 : n = 0 := by omega
    have hm2 : m = 2 := by omega
    exact hex (by simp [IsExceptionalType, hg0, hn0, hm2])
  · have hgd : 2 * g + m - 1 = 0 := congrArg Prod.fst h
    have hnd : 2 * n = 2 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h
    have hg0 : g = 0 := by omega
    have hn1 : n = 1 := by omega
    have hm1 : m = 1 := by omega
    exact hex (by simp [IsExceptionalType, hg0, hn1, hm1])
  · have hmd : (0 : ℕ) = 1 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) h
    omega
  · have hmd : (0 : ℕ) = 1 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) h
    omega
  · have hmd : (0 : ℕ) = 2 := congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) h
    omega

/-- A holomorphic open embedding into `X` that misses `P` is a holomorphic open embedding into `X ∖ P`. -/
theorem s82cmp_punct_embedding {S X : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S]
    [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [T2Space X]
    (P : Finset X) {ι : S → X} (hι : Topology.IsOpenEmbedding ι) (hιd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι)
    (G : S → puncturedOpens P) (hG : ∀ x, (G x : X) = ι x) :
    Topology.IsOpenEmbedding G ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G := by
  have hcomp : (Subtype.val ∘ G) = ι := funext hG
  have hGc : Continuous G := continuous_induced_rng.2 (by rw [hcomp]; exact hι.continuous)
  have hemb : Topology.IsEmbedding G :=
    Topology.IsEmbedding.of_comp hGc continuous_subtype_val (by rw [hcomp]; exact hι.isEmbedding)
  have hrange : Set.range G = Subtype.val ⁻¹' Set.range ι := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩; exact ⟨s, (hG s).symm⟩
    · rintro ⟨s, hs⟩; exact ⟨s, Subtype.ext (by rw [hG]; exact hs)⟩
  refine ⟨⟨hemb, by rw [hrange]; exact hι.isOpen_range.preimage continuous_subtype_val⟩, fun s => ?_⟩
  have hs : s ∈ (chartAt ℂ s).source := mem_chart_source ℂ s
  have hGs : G s ∈ (chartAt ℂ (G s)).source := mem_chart_source ℂ (G s)
  refine ((s23_mdifferentiableAt_iff hs hGs).2 ⟨hGc.continuousAt, ?_⟩)
  have hs' : ι s ∈ (chartAt ℂ (ι s)).source := mem_chart_source ℂ (ι s)
  have h := ((s23_mdifferentiableAt_iff hs hs').1 (hιd s)).2
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
  show chartAt ℂ ((G s : puncturedOpens P) : X) ((G ((chartAt ℂ s).symm z) : puncturedOpens P) : X) =
    chartAt ℂ (ι s) (ι ((chartAt ℂ s).symm z))
  rw [hG, hG]

/-- The restriction of an involution to the complement of an invariant finite set. -/
theorem s82cmp_punct_J {X : Type u} [TopologicalSpace X] [T2Space X] (P : Finset X) (J : X ≃ₜ X)
    (hinv : ∀ y, J (J y) = y) (hP : J '' (↑P : Set X) = ↑P) :
    ∃ Jd : puncturedOpens P ≃ₜ puncturedOpens P, ∀ y, (Jd y : X) = J y := by
  have hmem : ∀ y : X, y ∉ (↑P : Set X) → J y ∉ (↑P : Set X) := by
    intro y hy hJy
    apply hy
    have : J (J y) ∈ J '' (↑P : Set X) := ⟨J y, hJy, rfl⟩
    rw [hP, hinv] at this
    exact this
  let f : puncturedOpens P → puncturedOpens P := fun y => ⟨J y.1, hmem y.1 y.2⟩
  have hff : ∀ y, f (f y) = y := fun y => Subtype.ext (hinv y.1)
  have hfc : Continuous f := Continuous.subtype_mk (J.continuous.comp continuous_subtype_val) _
  exact ⟨⟨⟨f, f, hff, hff⟩, hfc, hfc⟩, fun y => rfl⟩

end LiZhongQC
