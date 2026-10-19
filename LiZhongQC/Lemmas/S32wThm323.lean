import LiZhongQC.Lemmas.S32wDTPlanar
import LiZhongQC.Lemmas.S32wSymmetricExtension
import LiZhongQC.Lemmas.Thm321

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

universe u

section Aux

/-- The punctured double carries a finite-type structure of type `(2g+m-1, 2n, 0)`. -/
theorem s32w_t33_punct_structure {Xd : ClosedRS.{u}} {Pd : Finset Xd.carrier} {G N : ℕ}
    (hg : HasGenus Xd.carrier G) (hc : Pd.card = N) :
    Nonempty (FiniteTypeStructure (puncturedOpens Pd) G N 0) := by
  refine ⟨{ X := Xd
            P := Pd
            D := fun j => Fin.elim0 j
            ι := Subtype.val
            genus := hg
            card_P := hc
            disc := fun j => Fin.elim0 j
            disjoint := fun i => Fin.elim0 i
            disjoint_P := fun j => Fin.elim0 j
            embedding := (puncturedOpens Pd).isOpen.isOpenEmbedding_subtypeVal
            holomorphic := (contMDiff_subtype_val (I := 𝓘(ℂ)) (n := ω)).mdifferentiable (by simp)
            range_ι := ?_ }⟩
  ext y
  simp [puncturedOpens]

end Aux

section Main

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- The identity is a Teichmüller map with `k = 0` for any nonzero holomorphic quadratic differential. -/
theorem s32w_t33_id_teich {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y] [T2Space Y]
    [ConnectedSpace Y] [IsManifold 𝓘(ℂ) ω Y] {Q : Y → ℂ → ℂ} (hQ : IsHolQuadDiff Q) (hne : Q ≠ 0) :
    IsTeichmullerMap (Homeomorph.refl Y) Q Q 0 := by
  have hbi : IsBiholomorphic (Homeomorph.refl Y) :=
    ⟨mdifferentiable_id, id, mdifferentiable_id, fun _ => rfl, fun _ => rfl⟩
  refine ⟨⟨1, (isKQCRS_one_iff _).2 hbi⟩, hQ, hne, hQ, le_rfl, one_pos, ?_, ?_⟩
  · intro p hp
    obtain ⟨m, ζ, han, h0, hd, hev⟩ := s25e_natural_chart hQ hne p
    have hm : m = 0 := by
      by_contra hm0
      apply hp
      have := hev.self_of_nhds
      show Q p (chartAt ℂ p p) = 0
      rw [this, h0, zero_pow hm0]
      simp
    subst hm
    have hnat : IsNaturalParameterAt Q p ζ := by
      refine ⟨han, h0, hd, hev.mono fun z hz => ?_⟩
      rw [hz]
      norm_num
    refine ⟨hp, ζ, ζ, hnat, hnat, ?_⟩
    filter_upwards [(chartAt ℂ p).open_target.mem_nhds ((chartAt ℂ p).map_source (mem_chart_source ℂ p))]
      with z hz
    show ζ (chartAt ℂ p ((chartAt ℂ p).symm z)) = teichStretch 0 (ζ z)
    rw [(chartAt ℂ p).right_inv hz]
    simp [teichStretch]
  · intro p n hp
    exact hp

/-- **Theorem 32.3** (book helper; statement of `thm32_3_uniqueness_gnm`). -/
theorem s32w_thm32_3_uniqueness_gnm {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m) {f₀ : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ}
    (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k) {f : S₀ ≃ₜ S} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    maxDilatationRS f₀ ≤ maxDilatationRS f ∧ (maxDilatationRS f = maxDilatationRS f₀ → ⇑f = ⇑f₀) := by
  classical
  by_cases hm : m = 0
  · subst hm
    exact s82lc_thm32_1_uniqueness_gn hex F₀ F₁ hf₀ hf hhom
  obtain ⟨Xd₀, J₀, ιd₀, Pd₀, hd₀⟩ := exists_schottkyDouble hm F₀
  obtain ⟨Xd₁, J₁, ιd₁, Pd₁, hd₁⟩ := exists_schottkyDouble hm F₁
  have hf₀qc : IsQCRS f₀ := hf₀.2.qc
  obtain ⟨fd₀, hfd₀, hfd₀Q, hK₀⟩ := s32w_symmetric_extension hm F₀ F₁ hd₀ hd₁ f₀ hf₀qc
  obtain ⟨fd, hfd, hfdQ, hK⟩ := s32w_symmetric_extension hm F₀ F₁ hd₀ hd₁ f hf
  obtain ⟨fdp₀, fdp, hfdp₀, hfdp, hQ₀, hQ, hhomd⟩ :=
    s32w_symm_ext_punctured hm hex F₀ F₁ hd₀ hd₁ hf₀qc hf hfd₀ hfd hfd₀Q hfdQ hhom
  obtain ⟨Fd₀⟩ := s32w_t33_punct_structure hd₀.genus hd₀.card_Pd
  obtain ⟨Fd₁⟩ := s32w_t33_punct_structure hd₁.genus hd₁.card_Pd
  obtain ⟨Jd₀, hJd₀⟩ := s32w_restrict_reflection hd₀
  have hoff := s32w_double_range_off_Pd F₀ hd₀
  let G₀ : C(S₀, ↥(puncturedOpens Pd₀)) :=
    ⟨fun x => ⟨ιd₀ x, hoff x⟩, Continuous.subtype_mk hd₀.embedding.continuous _⟩
  have hG₀ : ∀ x, (G₀ x : Xd₀.carrier) = ιd₀ x := fun x => rfl
  haveI : ConnectedSpace (puncturedOpens Pd₀) := s32w_punctured_connectedSpace Pd₀
  haveI : ConnectedSpace (puncturedOpens Pd₁) := s32w_punctured_connectedSpace Pd₁
  have hexd : ¬ IsExceptionalType (2 * g + m - 1) (2 * n) 0 := by
    intro hE
    apply hex
    unfold IsExceptionalType at hE
    rcases hE with h | h | h | h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨h1, h2, h3⟩ := h
    · have : g = 0 ∧ n = 0 ∧ m = 1 := by omega
      unfold IsExceptionalType
      simp [this.1, this.2.1, this.2.2]
    · exact absurd h2 (by omega)
    · have : g = 0 ∧ n = 0 ∧ m = 2 := by omega
      unfold IsExceptionalType
      simp [this.1, this.2.1, this.2.2]
    · have : g = 0 ∧ n = 1 ∧ m = 1 := by omega
      unfold IsExceptionalType
      simp [this.1, this.2.1, this.2.2]
    · exact absurd h3 (by omega)
    · exact absurd h3 (by omega)
    · exact absurd h3 (by omega)
  -- the Teichmüller map of the punctured double
  have hKT : ∃ (Q : puncturedOpens Pd₀ → ℂ → ℂ) (Q' : puncturedOpens Pd₁ → ℂ → ℂ),
      IsAdmissibleTeichmullerMap Fd₀ fdp₀ Q Q' k := by
    rcases hf₀.2.k_nonneg.eq_or_lt with hk0 | hkpos
    · subst hk0
      obtain ⟨Q, hQint, -, -, hQne'⟩ := s32w_dt_Q hm F₀ hd₀ Fd₀ Jd₀ hJd₀ G₀ hG₀ hf₀.1
      have hQne : Q ≠ 0 := hQne' hf₀.2.initial_ne
      have hQhol : IsHolQuadDiff Q := (admissibleQDInterior_holomorphic Fd₀).1 Q hQint
      -- `fdp₀` is conformal
      have hmax : maxDilatationRS fd₀ = 1 := by
        rw [hK₀, (teichmullerMap_beltrami hf₀.2).2]
        simp
      have hKfd₀ := s29_m_isKQCRS_maxDil hfd₀Q
      rw [hmax] at hKfd₀
      have hKfd₀' : IsKQCRS fd₀ 1 := by simpa using hKfd₀
      have hK1 : IsKQCRS fdp₀ 1 := s32w_isKQCRS_restrict_opens hfdp₀ hKfd₀'
      have hbi : IsBiholomorphic fdp₀ := (isKQCRS_one_iff _).1 hK1
      obtain ⟨Q', hT⟩ := s32w_dt_teich_comp (Homeomorph.refl _) fdp₀ hbi (s32w_t33_id_teich hQhol hQne)
      refine ⟨Q, Q', hQint, ?_⟩
      have hc : (Homeomorph.refl (puncturedOpens Pd₀)).trans fdp₀ = fdp₀ := Homeomorph.ext (fun y => rfl)
      rw [hc] at hT
      exact hT
    · obtain ⟨Q, Q', hT, -, -⟩ := s32w_double_teichmuller hm hex F₀ F₁ hd₀ hd₁ Fd₀ hf₀ hkpos hfd₀ hfd₀Q
        hfdp₀ Jd₀ hJd₀ G₀ hG₀
      exact ⟨Q, Q', hT⟩
  obtain ⟨Q, Q', hT⟩ := hKT
  have huniq := s82lc_thm32_1_uniqueness_gn hexd Fd₀ Fd₁ hT hQ hhomd
  have hKteich : maxDilatationRS f₀ = maxDilatationRS fdp₀ :=
    (teichmullerMap_beltrami hf₀.2).2.trans (teichmullerMap_beltrami hT.2).2.symm
  have hKdp : maxDilatationRS fdp ≤ maxDilatationRS fd := by
    have hKfd := s29_m_isKQCRS_maxDil hfdQ
    have hfdpK := s32w_isKQCRS_restrict_opens hfdp hKfd
    calc maxDilatationRS fdp ≤ ENNReal.ofReal (maxDilatationRS fd).toReal := maxDilatationRS_le hfdpK
      _ = maxDilatationRS fd := ENNReal.ofReal_toReal (s29_m_maxDilatationRS_ne_top hfdQ)
  refine ⟨?_, fun hEq => ?_⟩
  · calc maxDilatationRS f₀ = maxDilatationRS fdp₀ := hKteich
      _ ≤ maxDilatationRS fdp := huniq.1
      _ ≤ maxDilatationRS fd := hKdp
      _ = maxDilatationRS f := hK
  · have hle : maxDilatationRS fdp ≤ maxDilatationRS fdp₀ := by
      calc maxDilatationRS fdp ≤ maxDilatationRS fd := hKdp
        _ = maxDilatationRS f := hK
        _ = maxDilatationRS f₀ := hEq
        _ = maxDilatationRS fdp₀ := hKteich
    have hfun := huniq.2 (le_antisymm hle huniq.1)
    funext x
    apply hd₁.embedding.injective
    calc ιd₁ (f x) = fd (ιd₀ x) := (hfd.1 x).symm
      _ = (fdp (G₀ x) : Xd₁.carrier) := by rw [hfdp, hG₀]
      _ = (fdp₀ (G₀ x) : Xd₁.carrier) := by rw [show fdp (G₀ x) = fdp₀ (G₀ x) from congrFun hfun _]
      _ = fd₀ (ιd₀ x) := by rw [hfdp₀, hG₀]
      _ = ιd₁ (f₀ x) := hfd₀.1 x

end Main

section RelocatedS32

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- **Theorem 32.3**: let `S₀` be a non-exceptional surface of type `(g, n, m)`, `ω` an admissible
quadratic differential on `S₀`, and `f : S₀ → S` a Teichmüller map with associated differential `ω`.
Then `f` is the unique extremal map of its homotopy class. -/
theorem thm32_3_uniqueness_gnm {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) (F₀ : FiniteTypeStructure S₀ g n m)
    (F₁ : FiniteTypeStructure S g n m) {f₀ : S₀ ≃ₜ S} {q : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ} {k : ℝ}
    (hf₀ : IsAdmissibleTeichmullerMap F₀ f₀ q q' k) {f : S₀ ≃ₜ S} (hf : IsQCRS f)
    (hhom : ContinuousMap.Homotopic (f₀ : C(S₀, S)) (f : C(S₀, S))) :
    maxDilatationRS f₀ ≤ maxDilatationRS f ∧ (maxDilatationRS f = maxDilatationRS f₀ → ⇑f = ⇑f₀) := by
  exact s32w_thm32_3_uniqueness_gnm hex F₀ F₁ hf₀ hf hhom

end RelocatedS32

end LiZhongQC
