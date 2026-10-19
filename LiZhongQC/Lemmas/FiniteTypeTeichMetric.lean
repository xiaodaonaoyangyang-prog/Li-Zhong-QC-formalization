import LiZhongQC.Ch09.S32_FiniteTypeTeichmuller
import LiZhongQC.Lemmas.UniformizedUniqueness
import LiZhongQC.Ch08.S29_TeichmullerMetric
import LiZhongQC.Lemmas.UniformizedTeichmuller
import LiZhongQC.Lemmas.FiniteTypeCover
import LiZhongQC.Lemmas.FiniteTypeTeichBasic
import LiZhongQC.Lemmas.FiniteTypeComparison
import LiZhongQC.Lemmas.FiniteTypeTeichSpace

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- The set whose `sInf` is `teichDistanceFT p q` (literally the body of the definition). -/
def ft_teichSet {g n m : ℕ} (p q : TeichSpaceFiniteType S₀ g n m) : Set ℝ :=
  {d | ∃ (m₁ : MarkedFiniteTypeRS S₀ g n m) (m₂ : MarkedFiniteTypeRS S₀ g n m) (h : m₁.X.carrier ≃ₜ m₂.X.carrier),
    Quot.mk _ m₁ = p ∧ Quot.mk _ m₂ = q ∧ IsQCRS h ∧
      ContinuousMap.Homotopic ((m₁.marking.trans h : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier))
        (m₂.marking : C(S₀, m₂.X.carrier)) ∧
    d = (1 / 2) * Real.log (maxDilatationRS h).toReal}

theorem ft_teichDistanceFT_eq {g n m : ℕ} (p q : TeichSpaceFiniteType S₀ g n m) :
    teichDistanceFT p q = sInf (ft_teichSet p q) := rfl

theorem ft_teichSet_nonneg {g n m : ℕ} (p q : TeichSpaceFiniteType S₀ g n m) :
    ∀ d ∈ ft_teichSet p q, 0 ≤ d := by
  rintro d ⟨m₁, m₂, h, -, -, hh, -, rfl⟩
  letI : Nonempty m₁.X.carrier := ConnectedSpace.toNonempty
  exact s29_m_half_log_nonneg hh

theorem ft_teichSet_bddBelow {g n m : ℕ} (p q : TeichSpaceFiniteType S₀ g n m) :
    BddBelow (ft_teichSet p q) :=
  ⟨0, ft_teichSet_nonneg p q⟩

theorem ft_equiv_of_eq {g n m : ℕ} {m₁ m₂ : MarkedFiniteTypeRS S₀ g n m}
    (h : (Quot.mk _ m₁ : TeichSpaceFiniteType S₀ g n m) = Quot.mk _ m₂) : m₁.Equiv m₂ :=
  (ft_quotient_exact m₁ m₂).1 h

theorem ft_homotopic_symm {g n m : ℕ} {m₁ m₂ : MarkedFiniteTypeRS S₀ g n m}
    {h : m₁.X.carrier ≃ₜ m₂.X.carrier}
    (hhom : ContinuousMap.Homotopic ((m₁.marking.trans h : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier))
        (m₂.marking : C(S₀, m₂.X.carrier))) :
    ContinuousMap.Homotopic ((m₂.marking.trans h.symm : S₀ ≃ₜ m₁.X.carrier) : C(S₀, m₁.X.carrier))
      (m₁.marking : C(S₀, m₁.X.carrier)) := by
  rw [coe_homeomorph_trans] at hhom ⊢
  have hcancel : (h.symm : C(m₂.X.carrier, m₁.X.carrier)).comp
      ((h : C(m₁.X.carrier, m₂.X.carrier)).comp (m₁.marking : C(S₀, m₁.X.carrier))) =
      (m₁.marking : C(S₀, m₁.X.carrier)) := by
    ext x
    exact h.symm_apply_apply _
  have := (ContinuousMap.Homotopic.refl (h.symm : C(m₂.X.carrier, m₁.X.carrier))).comp hhom.symm
  rwa [hcancel] at this

theorem ft_transport {g n m : ℕ} {m₁ m₂ n₁ n₂ : MarkedFiniteTypeRS S₀ g n m}
    (h₁ : m₁.Equiv n₁) (h₂ : m₂.Equiv n₂) {h : m₁.X.carrier ≃ₜ m₂.X.carrier} (hg : IsQCRS h)
    (hhom : ContinuousMap.Homotopic ((m₁.marking.trans h : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier))
        (m₂.marking : C(S₀, m₂.X.carrier))) :
    ∃ h' : n₁.X.carrier ≃ₜ n₂.X.carrier, IsQCRS h' ∧ maxDilatationRS h' ≤ maxDilatationRS h ∧
      ContinuousMap.Homotopic ((n₁.marking.trans h' : S₀ ≃ₜ n₂.X.carrier) : C(S₀, n₂.X.carrier))
        (n₂.marking : C(S₀, n₂.X.carrier)) := by
  obtain ⟨c₁, hc₁, hh₁⟩ := h₁
  obtain ⟨c₂, hc₂, hh₂⟩ := h₂
  obtain ⟨hqc, hle⟩ := s29_m_maxDil_conj_biholo hg hc₁.homeomorph_symm hc₂
  refine ⟨c₁.symm.trans (h.trans c₂), hqc, hle, ?_⟩
  rw [coe_homeomorph_trans] at hhom hh₁ hh₂
  rw [coe_homeomorph_trans, coe_homeomorph_trans, coe_homeomorph_trans]
  have hcancel : (c₁.symm : C(n₁.X.carrier, m₁.X.carrier)).comp
      ((c₁ : C(m₁.X.carrier, n₁.X.carrier)).comp (m₁.marking : C(S₀, m₁.X.carrier))) =
      (m₁.marking : C(S₀, m₁.X.carrier)) := by
    ext x
    exact c₁.symm_apply_apply _
  have e1 : ContinuousMap.Homotopic ((c₁.symm : C(n₁.X.carrier, m₁.X.carrier)).comp
      (n₁.marking : C(S₀, n₁.X.carrier))) (m₁.marking : C(S₀, m₁.X.carrier)) := by
    have := (ContinuousMap.Homotopic.refl (c₁.symm : C(n₁.X.carrier, m₁.X.carrier))).comp hh₁.symm
    rwa [hcancel] at this
  have e2 := (ContinuousMap.Homotopic.refl ((c₂ : C(m₂.X.carrier, n₂.X.carrier)).comp
    (h : C(m₁.X.carrier, m₂.X.carrier)))).comp e1
  have e3 := (ContinuousMap.Homotopic.refl (c₂ : C(m₂.X.carrier, n₂.X.carrier))).comp hhom
  exact e2.trans (e3.trans hh₂)

theorem ft_teichSet_nonempty {g n m : ℕ} (p q : TeichSpaceFiniteType S₀ g n m) :
    (ft_teichSet p q).Nonempty := by
  obtain ⟨m₁, rfl⟩ := Quot.exists_rep p
  obtain ⟨m₂, rfl⟩ := Quot.exists_rep q
  obtain ⟨K₁, hK₁⟩ := m₁.qc
  obtain ⟨K₂, hK₂⟩ := m₂.qc
  have h := (eq23_4 (s29_m_isKQCRS_symm hK₁) hK₂).1
  refine ⟨_, m₁, m₂, m₁.marking.symm.trans m₂.marking, rfl, rfl, ⟨_, h⟩, ?_, rfl⟩
  have : ((m₁.marking.trans (m₁.marking.symm.trans m₂.marking) : S₀ ≃ₜ m₂.X.carrier) :
      C(S₀, m₂.X.carrier)) = (m₂.marking : C(S₀, m₂.X.carrier)) := by
    ext x
    simp
  rw [this]

theorem ft_teichDistanceFT_nonneg {g n m : ℕ} (p q : TeichSpaceFiniteType S₀ g n m) :
    0 ≤ teichDistanceFT p q :=
  Real.sInf_nonneg (ft_teichSet_nonneg p q)

theorem ft_teichDistanceFT_self {g n m : ℕ} (p : TeichSpaceFiniteType S₀ g n m) :
    teichDistanceFT p p = 0 := by
  refine le_antisymm ?_ (ft_teichDistanceFT_nonneg p p)
  obtain ⟨m', rfl⟩ := Quot.exists_rep p
  letI : Nonempty m'.X.carrier := ConnectedSpace.toNonempty
  have h1 : IsKQCRS (Homeomorph.refl m'.X.carrier) 1 :=
    (isKQCRS_one_iff _).2
      (isBiholomorphic_id : IsBiholomorphic ((Homeomorph.refl m'.X.carrier : _ ≃ₜ _) : m'.X.carrier → m'.X.carrier))
  have hmem : (1 / 2 : ℝ) * Real.log (maxDilatationRS (Homeomorph.refl m'.X.carrier : _ → _)).toReal ∈
      ft_teichSet (Quot.mk _ m') (Quot.mk _ m') :=
    ⟨m', m', Homeomorph.refl _, rfl, rfl, ⟨1, h1⟩, ContinuousMap.Homotopic.refl _, rfl⟩
  have hK : maxDilatationRS (Homeomorph.refl m'.X.carrier : _ → _) = 1 :=
    le_antisymm (by simpa using maxDilatationRS_le h1) (s29_m_one_le_maxDilatationRS ⟨1, h1⟩)
  refine (csInf_le (ft_teichSet_bddBelow _ _) hmem).trans (le_of_eq ?_)
  rw [hK]
  simp

theorem ft_teichDistanceFT_symm {g n m : ℕ} (p q : TeichSpaceFiniteType S₀ g n m) :
    teichDistanceFT p q = teichDistanceFT q p := by
  have key : ∀ p q : TeichSpaceFiniteType S₀ g n m, ∀ a ∈ ft_teichSet p q, ∃ b ∈ ft_teichSet q p, b ≤ a := by
    intro p q a ⟨m₁, m₂, h, hm₁, hm₂, hg, hhom, ha⟩
    letI : Nonempty m₁.X.carrier := ConnectedSpace.toNonempty
    obtain ⟨hgs, hle⟩ := s29_m_maxDil_symm_le hg
    exact ⟨_, ⟨m₂, m₁, h.symm, hm₂, hm₁, hgs, ft_homotopic_symm hhom, rfl⟩,
      ha ▸ s29_m_half_log_mono hgs hg hle⟩
  exact s29_m_sInf_eq (ft_teichSet_bddBelow _ _) (ft_teichSet_bddBelow _ _) (key p q) (key q p)

theorem ft_teichDistanceFT_triangle_aux {g n m : ℕ} (p q r : TeichSpaceFiniteType S₀ g n m) :
    teichDistanceFT p q ≤ teichDistanceFT p r + teichDistanceFT q r := by
  have key : ∀ a ∈ ft_teichSet p r, ∀ b ∈ ft_teichSet q r, ∃ c ∈ ft_teichSet p q, c ≤ a + b := by
    rintro a ⟨m₁, m₃, g₁, hm₁, hm₃, hg₁, hhom₁, rfl⟩ b ⟨m₂, m₃', g₂, hm₂, hm₃', hg₂, hhom₂, rfl⟩
    letI : Nonempty m₁.X.carrier := ConnectedSpace.toNonempty
    letI : Nonempty m₂.X.carrier := ConnectedSpace.toNonempty
    obtain ⟨g₂', hg₂', hle₂, hhom₂'⟩ := ft_transport (ft_marked_equiv_equivalence.refl m₂)
      (ft_equiv_of_eq (hm₃'.trans hm₃.symm)) hg₂ hhom₂
    obtain ⟨hg₂s, hle₂s⟩ := s29_m_maxDil_symm_le hg₂'
    have hK₁ := s29_m_isKQCRS_maxDil hg₁
    have hK₂ := s29_m_isKQCRS_maxDil hg₂s
    obtain ⟨hc, hcle⟩ := eq23_4 hK₁ hK₂
    refine ⟨_, ⟨m₁, m₂, g₁.trans g₂'.symm, hm₁, hm₂, ⟨_, hc⟩, ?_, rfl⟩, ?_⟩
    · have e1 := ft_homotopic_symm hhom₂'
      rw [coe_homeomorph_trans] at hhom₁ e1
      rw [coe_homeomorph_trans, coe_homeomorph_trans]
      have e2 := (ContinuousMap.Homotopic.refl (g₂'.symm : C(m₃.X.carrier, m₂.X.carrier))).comp hhom₁
      exact e2.trans e1
    · have hKle : maxDilatationRS (g₁.trans g₂'.symm) ≤ maxDilatationRS g₂ * maxDilatationRS g₁ :=
        calc maxDilatationRS (g₁.trans g₂'.symm) = maxDilatationRS (g₂'.symm ∘ g₁) := rfl
          _ ≤ maxDilatationRS g₂'.symm * maxDilatationRS g₁ := hcle
          _ ≤ maxDilatationRS g₂ * maxDilatationRS g₁ := by gcongr; exact hle₂s.trans hle₂
      have hne : maxDilatationRS g₂ * maxDilatationRS g₁ ≠ ⊤ :=
        ENNReal.mul_ne_top (s29_m_maxDilatationRS_ne_top hg₂) (s29_m_maxDilatationRS_ne_top hg₁)
      have hc1 := s29_m_one_le_toReal (⟨_, hc⟩ : IsQCRS (g₁.trans g₂'.symm))
      have h1 := s29_m_one_le_toReal hg₁
      have h2 := s29_m_one_le_toReal hg₂
      have hmono : (maxDilatationRS (g₁.trans g₂'.symm)).toReal ≤
          (maxDilatationRS g₂).toReal * (maxDilatationRS g₁).toReal := by
        rw [← ENNReal.toReal_mul]
        exact ENNReal.toReal_mono hne hKle
      have := Real.log_le_log (by linarith) hmono
      rw [Real.log_mul (by positivity) (by positivity)] at this
      linarith
  obtain ⟨a₀, ha₀⟩ := ft_teichSet_nonempty p r
  obtain ⟨b₀, hb₀⟩ := ft_teichSet_nonempty q r
  show sInf (ft_teichSet p q) ≤ sInf (ft_teichSet p r) + sInf (ft_teichSet q r)
  have hA : sInf (ft_teichSet p q) - sInf (ft_teichSet q r) ≤ sInf (ft_teichSet p r) := by
    refine le_csInf ⟨a₀, ha₀⟩ fun a ha => ?_
    have : sInf (ft_teichSet p q) - a ≤ sInf (ft_teichSet q r) := by
      refine le_csInf ⟨b₀, hb₀⟩ fun b hb => ?_
      obtain ⟨c, hc, hcab⟩ := key a ha b hb
      have := csInf_le (ft_teichSet_bddBelow p q) hc
      linarith
    linarith
  linarith

theorem ft_teichDistanceFT_triangle {g n m : ℕ} (p q r : TeichSpaceFiniteType S₀ g n m) :
    teichDistanceFT p r ≤ teichDistanceFT p q + teichDistanceFT q r := by
  have := ft_teichDistanceFT_triangle_aux p r q
  rw [ft_teichDistanceFT_symm r q] at this
  exact this

theorem ft_homotopic_of_marking {g n m : ℕ} {A C : MarkedFiniteTypeRS S₀ g n m}
    {G : A.X.carrier ≃ₜ C.X.carrier}
    (hG : ContinuousMap.Homotopic ((A.marking.trans G : S₀ ≃ₜ C.X.carrier) : C(S₀, C.X.carrier))
        (C.marking : C(S₀, C.X.carrier))) :
    ContinuousMap.Homotopic ((A.marking.symm.trans C.marking : A.X.carrier ≃ₜ C.X.carrier) :
      C(A.X.carrier, C.X.carrier)) (G : C(A.X.carrier, C.X.carrier)) := by
  have h1 := hG.comp (ContinuousMap.Homotopic.refl (A.marking.symm : C(A.X.carrier, S₀)))
  have e1 : ((A.marking.trans G : S₀ ≃ₜ C.X.carrier) : C(S₀, C.X.carrier)).comp
      (A.marking.symm : C(A.X.carrier, S₀)) = (G : C(A.X.carrier, C.X.carrier)) := by
    ext x
    change G (A.marking (A.marking.symm x)) = G x
    rw [A.marking.apply_symm_apply]
  have e2 : (C.marking : C(S₀, C.X.carrier)).comp (A.marking.symm : C(A.X.carrier, S₀)) =
      ((A.marking.symm.trans C.marking : A.X.carrier ≃ₜ C.X.carrier) : C(A.X.carrier, C.X.carrier)) := rfl
  rw [e1, e2] at h1
  exact h1.symm

theorem ft_attained {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) (A C : MarkedFiniteTypeRS S₀ g n m) :
    ∃ h : A.X.carrier ≃ₜ C.X.carrier, IsQCRS h ∧
      ContinuousMap.Homotopic ((A.marking.trans h : S₀ ≃ₜ C.X.carrier) : C(S₀, C.X.carrier))
        (C.marking : C(S₀, C.X.carrier)) ∧
      teichDistanceFT (Quot.mk _ A) (Quot.mk _ C) = (1 / 2) * Real.log (maxDilatationRS h).toReal ∧
      ∀ f : A.X.carrier ≃ₜ C.X.carrier, IsQCRS f →
        ContinuousMap.Homotopic ((A.marking.trans f : S₀ ≃ₜ C.X.carrier) : C(S₀, C.X.carrier))
          (C.marking : C(S₀, C.X.carrier)) → maxDilatationRS h ≤ maxDilatationRS f := by
  classical
  letI : Nonempty A.X.carrier := ConnectedSpace.toNonempty
  let F : A.X.carrier ≃ₜ C.X.carrier := A.marking.symm.trans C.marking
  have hFqc : IsQCRS F := by
    obtain ⟨K₁, hK₁⟩ := A.qc
    obtain ⟨K₂, hK₂⟩ := C.qc
    exact ⟨_, (eq23_4 (s29_m_isKQCRS_symm hK₁) hK₂).1⟩
  obtain ⟨f₀, hFf₀, hcase⟩ := s32w_thm32_4 hex A.X.structure' C.X.structure' F hFqc
  have hMF : ((A.marking.trans F : S₀ ≃ₜ C.X.carrier) : C(S₀, C.X.carrier)) =
      (C.marking : C(S₀, C.X.carrier)) := by
    ext x
    change C.marking (A.marking.symm (A.marking x)) = C.marking x
    rw [A.marking.symm_apply_apply]
  have hmark : ContinuousMap.Homotopic
      ((A.marking.trans f₀ : S₀ ≃ₜ C.X.carrier) : C(S₀, C.X.carrier))
      (C.marking : C(S₀, C.X.carrier)) := by
    have h2 := hFf₀.symm.comp
      (ContinuousMap.Homotopic.refl (A.marking : C(S₀, A.X.carrier)))
    rw [← coe_homeomorph_trans, ← coe_homeomorph_trans, hMF] at h2
    exact h2
  have hext : IsQCRS f₀ ∧ ∀ f : A.X.carrier ≃ₜ C.X.carrier, IsQCRS f →
      ContinuousMap.Homotopic ((A.marking.trans f : S₀ ≃ₜ C.X.carrier) : C(S₀, C.X.carrier))
        (C.marking : C(S₀, C.X.carrier)) → maxDilatationRS f₀ ≤ maxDilatationRS f := by
    rcases hcase with hb | ⟨q, q', k, hq⟩
    · have h1 : IsKQCRS f₀ 1 := (isKQCRS_one_iff f₀).2 hb
      refine ⟨⟨1, h1⟩, fun f hf _ => ?_⟩
      exact (by simpa using maxDilatationRS_le h1 : maxDilatationRS f₀ ≤ 1).trans
        (s29_m_one_le_maxDilatationRS hf)
    · refine ⟨hq.2.qc, fun f hf hfh => ?_⟩
      exact (s32w_thm32_3_uniqueness_gnm hex A.X.structure' C.X.structure' hq hf
        (hFf₀.symm.trans (ft_homotopic_of_marking hfh))).1
  refine ⟨f₀, hext.1, hmark, ?_, hext.2⟩
  have hmem : (1 / 2 : ℝ) * Real.log (maxDilatationRS f₀).toReal ∈
      ft_teichSet (Quot.mk _ A) (Quot.mk _ C) :=
    ⟨A, C, f₀, rfl, rfl, hext.1, hmark, rfl⟩
  show sInf (ft_teichSet (Quot.mk _ A : TeichSpaceFiniteType S₀ g n m) (Quot.mk _ C)) = _
  apply le_antisymm
  · exact csInf_le (ft_teichSet_bddBelow _ _) hmem
  · apply le_csInf ⟨_, hmem⟩
    rintro d ⟨n₁, n₂, G, hn₁, hn₂, hG, hGHom, rfl⟩
    obtain ⟨G', hG', hle, hhom⟩ :=
      ft_transport (ft_equiv_of_eq hn₁) (ft_equiv_of_eq hn₂) hG hGHom
    have hmin : maxDilatationRS f₀ ≤ maxDilatationRS G' := hext.2 G' hG' hhom
    exact (s29_m_half_log_mono hext.1 hG' hmin).trans
      (s29_m_half_log_mono hG' hG hle)

theorem ft_teichDistanceFT_eq_zero {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (p q : TeichSpaceFiniteType S₀ g n m) (h0 : teichDistanceFT p q = 0) : p = q := by
  obtain ⟨A, rfl⟩ := Quot.exists_rep p
  obtain ⟨C, rfl⟩ := Quot.exists_rep q
  letI : Nonempty A.X.carrier := ConnectedSpace.toNonempty
  obtain ⟨h, hh, hhom, hd, -⟩ := ft_attained hex A C
  rw [hd] at h0
  have h1 := s29_m_one_le_toReal hh
  have hlog : Real.log (maxDilatationRS h).toReal = 0 := by linarith
  have hK : (maxDilatationRS h).toReal = 1 := by
    rcases Real.log_eq_zero.1 hlog with h' | h' | h'
    · linarith
    · exact h'
    · linarith
  have hKe : maxDilatationRS h = 1 := by
    have := (ENNReal.toReal_eq_toReal_iff' (s29_m_maxDilatationRS_ne_top hh) ENNReal.one_ne_top).1
      (by simpa using hK)
    exact this
  have hconf : IsBiholomorphic h := (isKQCRS_one_iff h).1 (utm_isKQCRS_one_of_maxDil hh hKe)
  exact Quot.sound ⟨h, hconf, hhom⟩

end

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- The base point `[S₀, id]` of `TeichSpaceFiniteType S₀ g n m`. -/
theorem ft_radial_distance {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) (A : MarkedFiniteTypeRS S₀ g n m) (f : S₀ ≃ₜ A.X.carrier)
    {q : S₀ → ℂ → ℂ} {q' : A.X.carrier → ℂ → ℂ} {k : ℝ}
    (hq : IsAdmissibleTeichmullerMap F₀ f q q' k)
    (hhom : ContinuousMap.Homotopic (A.marking : C(S₀, A.X.carrier)) (f : C(S₀, A.X.carrier))) :
    teichDistanceFT
      (Quot.mk _ (⟨⟨S₀, F₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩ : MarkedFiniteTypeRS S₀ g n m))
      (Quot.mk _ A) = (1 / 2) * Real.log ((1 + k) / (1 - k)) := by
  classical
  let B : MarkedFiniteTypeRS S₀ g n m := ⟨⟨S₀, F₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩
  obtain ⟨h, hh, hmark, hd, hmin⟩ := ft_attained hex B A
  have hfmark : ContinuousMap.Homotopic
      ((B.marking.trans f : S₀ ≃ₜ A.X.carrier) : C(S₀, A.X.carrier)) (A.marking : C(S₀, A.X.carrier)) := by
    exact hhom.symm
  have h1 : maxDilatationRS h ≤ maxDilatationRS f := hmin f hq.2.qc hfmark
  have hhm : ContinuousMap.Homotopic (f : C(S₀, A.X.carrier)) (h : C(S₀, A.X.carrier)) :=
    hhom.symm.trans hmark.symm
  have h2 : maxDilatationRS f ≤ maxDilatationRS h :=
    (s32w_thm32_3_uniqueness_gnm hex F₀ A.X.structure' hq hh hhm).1
  have h3 : maxDilatationRS h = maxDilatationRS f := le_antisymm h1 h2
  have hk0 := hq.2.k_nonneg
  have hk1 := hq.2.k_lt_one
  have hK : maxDilatationRS f = ENNReal.ofReal ((1 + k) / (1 - k)) :=
    (teichmullerMap_beltrami hq.2).2
  rw [hd, h3, hK, ENNReal.toReal_ofReal (div_nonneg (by linarith) (by linarith))]

end

theorem ft_ball_bound {M : ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h : (1 / 2) * Real.log ((1 + t) / (1 - t)) ≤ M) :
    t ≤ (Real.exp (2 * M) - 1) / (Real.exp (2 * M) + 1) := by
  have hE : 0 < Real.exp (2 * M) := Real.exp_pos _
  have h1 : 0 < 1 - t := by linarith
  have hR : 0 < (1 + t) / (1 - t) := div_pos (by linarith) h1
  have h2 : Real.log ((1 + t) / (1 - t)) ≤ 2 * M := by linarith
  have h3 : (1 + t) / (1 - t) ≤ Real.exp (2 * M) := (Real.log_le_iff_le_exp hR).1 h2
  have h4 : 1 + t ≤ Real.exp (2 * M) * (1 - t) := (div_le_iff₀ h1).1 h3
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem ft_radius_lt_one (M : ℝ) : (Real.exp (2 * M) - 1) / (Real.exp (2 * M) + 1) < 1 := by
  have hE : 0 < Real.exp (2 * M) := Real.exp_pos _
  rw [div_lt_one (by positivity)]
  linarith

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

theorem ft_complete_of_chart {g n m N : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m)
    (Φ : EuclideanSpace ℝ (Fin N) → TeichSpaceFiniteType S₀ g n m)
    (R1 : InjOn Φ (ball 0 1))
    (R2 : ∀ p : TeichSpaceFiniteType S₀ g n m, ∃ v ∈ ball (0 : EuclideanSpace ℝ (Fin N)) 1, Φ v = p)
    (R3 : Φ 0 = Quot.mk _ (⟨⟨S₀, F₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩ : MarkedFiniteTypeRS S₀ g n m))
    (R4 : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin N)) 1, v ≠ 0 →
      ∃ (A : MarkedFiniteTypeRS S₀ g n m) (f : S₀ ≃ₜ A.X.carrier) (q : S₀ → ℂ → ℂ)
        (q' : A.X.carrier → ℂ → ℂ) (k : ℝ),
        Quot.mk _ A = Φ v ∧
          ContinuousMap.Homotopic (A.marking : C(S₀, A.X.carrier)) (f : C(S₀, A.X.carrier)) ∧
          IsAdmissibleTeichmullerMap F₀ f q q' k ∧ 0 < k ∧ k < 1 ∧ ‖v‖ = k)
    (R5 : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin N)) 1, ∀ vs : ℕ → EuclideanSpace ℝ (Fin N),
      (∀ i, vs i ∈ ball (0 : EuclideanSpace ℝ (Fin N)) 1) → Tendsto vs atTop (𝓝 v) →
      Tendsto (fun j => teichDistanceFT (Φ (vs j)) (Φ v)) atTop (𝓝 0)) :
    (∀ p : ℕ → TeichSpaceFiniteType S₀ g n m,
      (∀ ε > 0, ∃ N, ∀ i ≥ N, ∀ j ≥ N, teichDistanceFT (p i) (p j) < ε) →
        ∃ q, Tendsto (fun i => teichDistanceFT (p i) q) atTop (𝓝 0)) ∧
    ∀ (v : EuclideanSpace ℝ (Fin N)) (vs : ℕ → EuclideanSpace ℝ (Fin N)),
      v ∈ ball 0 1 → (∀ i, vs i ∈ ball 0 1) →
      (Tendsto vs atTop (𝓝 v) ↔ Tendsto (fun i => teichDistanceFT (Φ (vs i)) (Φ v)) atTop (𝓝 0)) := by
  classical
  set o : TeichSpaceFiniteType S₀ g n m :=
    Quot.mk _ (⟨⟨S₀, F₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩ : MarkedFiniteTypeRS S₀ g n m) with ho
  have hrad : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin N)) 1,
      teichDistanceFT o (Φ v) = (1 / 2) * Real.log ((1 + ‖v‖) / (1 - ‖v‖)) := by
    intro v hv
    by_cases h0 : v = 0
    · subst h0
      rw [R3, ft_teichDistanceFT_self]
      simp
    · obtain ⟨A, f, q, q', k, hA, hhom, hq, -, -, hk⟩ := R4 v hv h0
      rw [← hA, ft_radial_distance hex F₀ A f hq hhom, hk]
  have hnorm : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin N)) 1, 0 ≤ ‖v‖ ∧ ‖v‖ < 1 := fun v hv =>
    ⟨norm_nonneg _, by simpa using hv⟩
  have hball : ∀ M : ℝ, ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin N)) 1, teichDistanceFT o (Φ v) ≤ M →
      v ∈ closedBall (0 : EuclideanSpace ℝ (Fin N)) ((Real.exp (2 * M) - 1) / (Real.exp (2 * M) + 1)) := by
    intro M v hv hM
    rw [mem_closedBall_zero_iff]
    rw [hrad v hv] at hM
    exact ft_ball_bound (hnorm v hv).1 (hnorm v hv).2 hM
  refine ⟨fun p hp => ?_, fun v vs hv hvs => ⟨fun h => R5 v hv vs hvs h, fun hd => ?_⟩⟩
  · obtain ⟨M, hM⟩ := s29_m_cauchy_bounded_of_triangle (fun a b => teichDistanceFT a b)
      ft_teichDistanceFT_triangle_aux o p hp
    choose vn hvn hvp using fun n => R2 (p n)
    have hcl : ∀ n, vn n ∈ closedBall (0 : EuclideanSpace ℝ (Fin N))
        ((Real.exp (2 * M) - 1) / (Real.exp (2 * M) + 1)) := fun n =>
      hball M (vn n) (hvn n) (by rw [hvp n]; exact hM n)
    obtain ⟨v, hvr, φ, hφ, hlim⟩ :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin N))
        ((Real.exp (2 * M) - 1) / (Real.exp (2 * M) + 1))).tendsto_subseq hcl
    have hvball : v ∈ ball (0 : EuclideanSpace ℝ (Fin N)) 1 := by
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt (mem_closedBall_zero_iff.1 hvr) (ft_radius_lt_one M)
    refine ⟨Φ v, ?_⟩
    refine s29_t1_cauchy_subseq (fun a b : TeichSpaceFiniteType S₀ g n m => teichDistanceFT a b)
      ft_teichDistanceFT_symm ft_teichDistanceFT_triangle_aux p hp hφ (q := Φ v) ?_
    have h := R5 v hvball (fun n => vn (φ n)) (fun n => hvn _) hlim
    refine h.congr fun n => ?_
    show teichDistanceFT (Φ (vn (φ n))) (Φ v) = teichDistanceFT (p (φ n)) (Φ v)
    rw [hvp]
  · obtain ⟨C, hC⟩ := hd.bddAbove_range
    have hcl : ∀ j, vs j ∈ closedBall (0 : EuclideanSpace ℝ (Fin N))
        ((Real.exp (2 * (teichDistanceFT o (Φ v) + C)) - 1) / (Real.exp (2 * (teichDistanceFT o (Φ v) + C)) + 1)) := by
      intro j
      refine hball _ (vs j) (hvs j) ?_
      have h1 := ft_teichDistanceFT_triangle_aux o (Φ (vs j)) (Φ v)
      have h2 := hC ⟨j, rfl⟩
      linarith
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨w, hw, ψ, hψ, hlim⟩ :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin N))
        ((Real.exp (2 * (teichDistanceFT o (Φ v) + C)) - 1) /
          (Real.exp (2 * (teichDistanceFT o (Φ v) + C)) + 1))).tendsto_subseq
        (x := fun j => vs (ns j)) (fun j => hcl (ns j))
    refine ⟨ψ, ?_⟩
    have hwball : w ∈ ball (0 : EuclideanSpace ℝ (Fin N)) 1 := by
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt (mem_closedBall_zero_iff.1 hw) (ft_radius_lt_one _)
    have hw' := R5 w hwball (fun j => vs (ns (ψ j))) (fun j => hvs _) hlim
    have hv' : Tendsto (fun j => teichDistanceFT (Φ (vs (ns (ψ j)))) (Φ v)) atTop (𝓝 0) :=
      hd.comp (hns.comp hψ.tendsto_atTop)
    have hle : teichDistanceFT (Φ w) (Φ v) ≤ 0 := by
      refine le_of_tendsto_of_tendsto' tendsto_const_nhds (by simpa using hw'.add hv') fun j => ?_
      have h1 := ft_teichDistanceFT_triangle_aux (Φ w) (Φ v) (Φ (vs (ns (ψ j))))
      have h2 := ft_teichDistanceFT_symm (Φ w) (Φ (vs (ns (ψ j))))
      have h3 := ft_teichDistanceFT_symm (Φ v) (Φ (vs (ns (ψ j))))
      linarith
    have heq : Φ w = Φ v :=
      ft_teichDistanceFT_eq_zero hex _ _ (le_antisymm hle (ft_teichDistanceFT_nonneg _ _))
    have hwv : w = v := R1 hwball hv heq
    rw [hwv] at hlim
    exact hlim

end



/-- Chart partitions on a second countable charted space subordinate to a neighbourhood system
(the non-compact analogue of `s26_exists_chartPartition`). -/
theorem ft_exists_chartPartition {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    [SecondCountableTopology S] [Nonempty S] (V : S → Set S) (hVo : ∀ p, IsOpen (V p))
    (hVp : ∀ p, p ∈ V p) (hVs : ∀ p, V p ⊆ (chartAt ℂ p).source) :
    ∃ (x : ℕ → S) (P : ℕ → Set S), IsChartPartition S x P ∧ ∀ i, P i ⊆ V (x i) := by
  classical
  obtain ⟨t, htc, ht⟩ := (isLindelof_univ (X := S)).elim_countable_subcover V hVo
    (fun p _ => mem_iUnion.2 ⟨p, hVp p⟩)
  obtain ⟨p₀⟩ := (inferInstance : Nonempty S)
  have htne : (t ∪ {p₀}).Nonempty := ⟨p₀, Or.inr rfl⟩
  obtain ⟨x, hx⟩ := (htc.union (countable_singleton p₀)).exists_eq_range htne
  set W : ℕ → Set S := fun i => V (x i) with hW
  have hWo : ∀ i, IsOpen (W i) := fun i => hVo _
  refine ⟨x, disjointed W, ⟨fun i => ⟨?_, ?_⟩, disjoint_disjointed W, ?_⟩, fun i => ?_⟩
  · exact (disjointed_subset W i).trans (hVs _)
  · rw [disjointed_eq_inter_compl]
    exact s26_measurableSet_chart_image (x i) W hWo i (hVs _)
  · rw [iUnion_disjointed, eq_univ_iff_forall]
    intro p
    obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.1 (ht (mem_univ p))
    have hq' : q ∈ range x := hx ▸ Or.inl hq
    obtain ⟨i, rfl⟩ := hq'
    exact mem_iUnion.2 ⟨i, hpq⟩
  · exact disjointed_subset W i




section

theorem ft_eq29_3 [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {Sn : Type u}
    [TopologicalSpace Sn] [ChartedSpace ℂ Sn] [IsManifold 𝓘(ℂ) ω Sn] {f : S₀ ≃ₜ S} {fn : S₀ ≃ₜ Sn}
    {q qn : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ}
    {qn' : Sn → ℂ → ℂ} {k kn : ℝ} (hf : IsTeichmullerMap f q q' k) (hfn : IsTeichmullerMap fn qn qn' kn) :
    ∀ x : S₀, ∀ᵐ z ∂(volume.restrict (localMapDomain f x)),
      ‖complexDilatation (localMapExprAt (f.symm.trans fn) (f x) (localMapExpr f x z))
          (localMapExpr f x z)‖ ≤
        ‖teichmullerBeltrami kn qn x z - teichmullerBeltrami k q x z‖ / (1 - kn * k) := by
  intro x
  refine (ae_restrict_iff' (s23_localMapDomain_isOpen f.continuous x).measurableSet).2 ?_
  filter_upwards [(s26u_zeros_countable hf.initial hf.initial_ne x).ae_notMem volume,
    (s26u_zeros_countable hfn.initial hfn.initial_ne x).ae_notMem volume] with z hzZ hzZn hz
  exact s29_e_pointwise hf hfn x hz (fun h0 => hzZ ⟨hz.1, h0⟩) (fun h0 => hzZn ⟨hz.1, h0⟩)


theorem ft_null_cover {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [SecondCountableTopology X] {B : Set X} (W : X → Set X) (hWo : ∀ p, IsOpen (W p)) (hWp : ∀ p, p ∈ W p)
    (hWs : ∀ p, W p ⊆ (chartAt ℂ p).source) (hB : ∀ p, volume (chartAt ℂ p '' (B ∩ W p)) = 0) (x : X) :
    volume (chartAt ℂ x '' (B ∩ (chartAt ℂ x).source)) = 0 := by
  obtain ⟨t, htc, ht⟩ := (isLindelof_univ (X := X)).elim_countable_subcover W hWo (fun p _ => mem_iUnion.2 ⟨p, hWp p⟩)
  have hsub : chartAt ℂ x '' (B ∩ (chartAt ℂ x).source) ⊆
      ⋃ p ∈ t, chartAt ℂ x '' (B ∩ W p ∩ (chartAt ℂ x).source) := by
    rintro _ ⟨q, ⟨hqB, hqs⟩, rfl⟩
    have := ht (mem_univ q)
    simp only [mem_iUnion] at this
    obtain ⟨p, hpt, hqp⟩ := this
    exact mem_biUnion hpt ⟨q, ⟨⟨hqB, hqp⟩, hqs⟩, rfl⟩
  refine measure_mono_null hsub ?_
  refine (measure_biUnion_null_iff htc).2 fun p _ => ?_
  set A : Set ℂ := chartAt ℂ p '' (B ∩ W p ∩ (chartAt ℂ x).source) with hAdef
  have hA0 : volume A = 0 :=
    measure_mono_null (image_mono (f := chartAt ℂ p)
      (show B ∩ W p ∩ (chartAt ℂ x).source ⊆ B ∩ W p from fun q hq => ⟨hq.1.1, hq.1.2⟩)) (hB p)
  have himg : chartAt ℂ x '' (B ∩ W p ∩ (chartAt ℂ x).source) = chartTransition x p '' A := by
    ext w
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨chartAt ℂ p q, ⟨q, hq, rfl⟩, ?_⟩
      simp only [chartTransition]
      rw [(chartAt ℂ p).left_inv (hWs p hq.1.2)]
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨q, hq, ?_⟩
      simp only [chartTransition]
      rw [(chartAt ℂ p).left_inv (hWs p hq.1.2)]
  rw [himg]
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_ hA0
  rintro _ ⟨q, hq, rfl⟩
  have hz : chartAt ℂ p q ∈ (chartAt ℂ p).target := (chartAt ℂ p).map_source (hWs p hq.1.2)
  have hzx : (chartAt ℂ p).symm (chartAt ℂ p q) ∈ (chartAt ℂ x).source := by
    rw [(chartAt ℂ p).left_inv (hWs p hq.1.2)]
    exact hq.2
  exact ((s23_transition_differentiableAt x p hz hzx).restrictScalars ℝ).differentiableWithinAt


theorem ft_ae [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [SecondCountableTopology X]
    {e : S₀ ≃ₜ X} {q : S₀ → ℂ → ℂ} {q' : X → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap e q q' k) {Y : ℕ → Type u} [∀ n, TopologicalSpace (Y n)] [∀ n, ChartedSpace ℂ (Y n)] [∀ n, IsManifold 𝓘(ℂ) ω (Y n)]
    {en : ∀ n, S₀ ≃ₜ Y n}
    {qn : ℕ → S₀ → ℂ → ℂ} {qn' : ∀ n, Y n → ℂ → ℂ} {kn : ℕ → ℝ}
    (hfn : ∀ n, IsTeichmullerMap (en n) (qn n) (qn' n) (kn n))
    (hconv : ∀ x z, Tendsto (fun n => qn n x z) atTop (𝓝 (q x z))) (hkconv : Tendsto kn atTop (𝓝 k)) :
    ∀ x : X, ∀ᵐ z ∂(volume.restrict (chartAt ℂ x).target),
      Tendsto (fun n => dilatationQuotient (localMapExprAt (e.symm.trans (en n)) x z) z) atTop (𝓝 1) := by
  classical
  have hq := hf.initial
  have hne := hf.initial_ne
  have hk0 := hf.k_nonneg
  have hk1 := hf.k_lt_one
  obtain ⟨K, hK⟩ := hf.qc
  -- the exceptional points of `X`
  set B : Set X := {p | ¬ Tendsto (fun n => dilatationQuotient
    (localMapExpr (e.symm.trans (en n)) p) (chartAt ℂ p p)) atTop (𝓝 1)} with hB
  set W : X → Set X := fun p =>
    e '' ((chartAt ℂ (e.symm p)).source ∩ e ⁻¹' (chartAt ℂ p).source) with hW
  have hWo : ∀ p, IsOpen (W p) := fun p => e.isOpenMap _
    ((chartAt ℂ (e.symm p)).open_source.inter (e.continuous.isOpen_preimage _ (chartAt ℂ p).open_source))
  have hWp : ∀ p, p ∈ W p := fun p =>
    ⟨e.symm p, ⟨mem_chart_source ℂ _, by simpa using mem_chart_source ℂ p⟩, e.apply_symm_apply p⟩
  have hWs : ∀ p, W p ⊆ (chartAt ℂ p).source := by
    rintro p _ ⟨q₀, ⟨-, hq₀⟩, rfl⟩
    exact hq₀
  have hBnull : ∀ p, volume (chartAt ℂ p '' (B ∩ W p)) = 0 := by
    intro p
    obtain ⟨x', rfl⟩ := e.surjective p
    set L := localMapExpr e x' with hL
    set dom := localMapDomain e x' with hdom
    have hdomo : IsOpen dom := s23_localMapDomain_isOpen e.continuous x'
    have hz1 : ∀ n, ∀ᵐ z ∂(volume.restrict dom),
        ‖complexDilatation (localMapExprAt (e.symm.trans (en n)) (e x') (localMapExpr e x' z))
            (localMapExpr e x' z)‖ ≤
          ‖teichmullerBeltrami (kn n) (qn n) x' z - teichmullerBeltrami k q x' z‖ / (1 - kn n * k) :=
      fun n => ft_eq29_3 hf (hfn n) x'
    have hzq : ∀ᵐ z ∂(volume.restrict dom), q x' z ≠ 0 := by
      have h0 : volume {z | z ∈ (chartAt ℂ x').target ∧ q x' z = 0} = 0 :=
        (s26u_zeros_countable hq hne x').measure_zero _
      filter_upwards [ae_restrict_mem hdomo.measurableSet,
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 h0)] with z hzd hz hq0
      exact hz ⟨hzd.1, hq0⟩
    have hzn : ∀ n, ∀ᵐ z ∂(volume.restrict dom), qn n x' z ≠ 0 := by
      intro n
      have h0 : volume {z | z ∈ (chartAt ℂ x').target ∧ qn n x' z = 0} = 0 :=
        (s26u_zeros_countable (hfn n).initial (hfn n).initial_ne x').measure_zero _
      filter_upwards [ae_restrict_mem hdomo.measurableSet,
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 h0)] with z hzd hz hq0
      exact hz ⟨hzd.1, hq0⟩
    have hgood : ∀ᵐ z ∂(volume.restrict dom), q x' z ≠ 0 ∧ (∀ n, qn n x' z ≠ 0) ∧
        ∀ n, ‖complexDilatation (localMapExprAt (e.symm.trans (en n)) (e x') (localMapExpr e x' z))
            (localMapExpr e x' z)‖ ≤
          ‖teichmullerBeltrami (kn n) (qn n) x' z - teichmullerBeltrami k q x' z‖ / (1 - kn n * k) := by
      filter_upwards [hzq, ae_all_iff.2 hzn, ae_all_iff.2 hz1] with z a b c using ⟨a, b, c⟩
    set N : Set ℂ := {z | ¬ (z ∈ dom → (q x' z ≠ 0 ∧ (∀ n, qn n x' z ≠ 0) ∧
        ∀ n, ‖complexDilatation (localMapExprAt (e.symm.trans (en n)) (e x') (localMapExpr e x' z))
            (localMapExpr e x' z)‖ ≤
          ‖teichmullerBeltrami (kn n) (qn n) x' z - teichmullerBeltrami k q x' z‖ / (1 - kn n * k)))}
      with hN
    have hN0 : volume N = 0 := by
      have := (ae_restrict_iff' hdomo.measurableSet).1 hgood
      rw [ae_iff] at this
      exact this
    obtain ⟨N', hNN', hN'm, hN'0⟩ := exists_measurable_superset_of_null hN0
    set s : Set ℂ := N' ∩ dom with hs
    have hs0 : volume s = 0 := measure_mono_null inter_subset_left hN'0
    have hinj : InjOn L s := by
      intro z₁ hz₁ z₂ hz₂ h
      have h1 := hz₁.2
      have h2 := hz₂.2
      have h3 : e ((chartAt ℂ x').symm z₁) = e ((chartAt ℂ x').symm z₂) :=
        (chartAt ℂ (e x')).injOn h1.2 h2.2 h
      have h4 := e.injective h3
      calc z₁ = (chartAt ℂ x') ((chartAt ℂ x').symm z₁) := ((chartAt ℂ x').right_inv h1.1).symm
        _ = (chartAt ℂ x') ((chartAt ℂ x').symm z₂) := by rw [h4]
        _ = z₂ := (chartAt ℂ x').right_inv h2.1
    have hLimg : volume (L '' s) = 0 := by
      have h := s26w_lintegral_image (g := L) (D := dom) (K := K)
        (fun z hz => ⟨dom, hdomo, hz, subset_rfl, hK.2 x'⟩) (hN'm.inter hdomo.measurableSet)
        inter_subset_right hinj (fun _ => (1 : ℝ≥0∞))
      rw [setLIntegral_measure_zero s _ hs0] at h
      simpa using h
    refine measure_mono_null ?_ hLimg
    rintro _ ⟨q₁, ⟨hqB, hqW⟩, rfl⟩
    obtain ⟨q₀, ⟨hq₀s0, hq₀e⟩, rfl⟩ := hqW
    have hq₀s : q₀ ∈ (chartAt ℂ x').source := by simpa [e.symm_apply_apply] using hq₀s0
    have hzt : chartAt ℂ x' q₀ ∈ (chartAt ℂ x').target := (chartAt ℂ x').map_source hq₀s
    have hzd : chartAt ℂ x' q₀ ∈ dom := by
      refine ⟨hzt, ?_⟩
      show e ((chartAt ℂ x').symm (chartAt ℂ x' q₀)) ∈ (chartAt ℂ (e x')).source
      rw [(chartAt ℂ x').left_inv hq₀s]
      exact hq₀e
    have hLz : L (chartAt ℂ x' q₀) = chartAt ℂ (e x') (e q₀) := by
      show (chartAt ℂ (e x')) (e ((chartAt ℂ x').symm (chartAt ℂ x' q₀))) = _
      rw [(chartAt ℂ x').left_inv hq₀s]
    refine ⟨chartAt ℂ x' q₀, (⟨?_, hzd⟩ : chartAt ℂ x' q₀ ∈ N' ∩ dom), hLz⟩
    by_contra hzN
    have hzgood : q x' (chartAt ℂ x' q₀) ≠ 0 ∧ (∀ n, qn n x' (chartAt ℂ x' q₀) ≠ 0) ∧
        ∀ n, ‖complexDilatation (localMapExprAt (e.symm.trans (en n)) (e x')
            (localMapExpr e x' (chartAt ℂ x' q₀))) (localMapExpr e x' (chartAt ℂ x' q₀))‖ ≤
          ‖teichmullerBeltrami (kn n) (qn n) x' (chartAt ℂ x' q₀) -
            teichmullerBeltrami k q x' (chartAt ℂ x' q₀)‖ / (1 - kn n * k) := by
      by_contra hcon
      exact hzN (hNN' (show chartAt ℂ x' q₀ ∈ N from fun hh => hcon (hh hzd)))
    obtain ⟨hz0, -, hzb⟩ := hzgood
    apply hqB
    have hLt : L (chartAt ℂ x' q₀) ∈ (chartAt ℂ (e x')).target := by
      rw [hLz]
      exact (chartAt ℂ (e x')).map_source hq₀e
    have hU : ∀ n, dilatationQuotient (localMapExpr (e.symm.trans (en n)) (e q₀)) (chartAt ℂ (e q₀) (e q₀)) =
        dilatationQuotient (localMapExprAt (e.symm.trans (en n)) (e x') (L (chartAt ℂ x' q₀)))
          (L (chartAt ℂ x' q₀)) := by
      intro n
      rw [s29_e7_D_inv (⇑(e.symm.trans (en n))) (e x') hLt, hLz, (chartAt ℂ (e x')).left_inv hq₀e]
    simp only [hU]
    have := s29_e12_ae_analysis (q := q x' (chartAt ℂ x' q₀)) (qn := fun n => qn n x' (chartAt ℂ x' q₀))
      (k := k) (kn := kn) (m := fun n => ‖complexDilatation (localMapExprAt (e.symm.trans (en n)) (e x')
        (L (chartAt ℂ x' q₀))) (L (chartAt ℂ x' q₀))‖) hz0 (hconv x' _) hkconv hk0 hk1
      (fun n => norm_nonneg _) hzb
    exact this
  have hnull := ft_null_cover W hWo hWp hWs hBnull
  intro x
  refine (ae_restrict_iff' (chartAt ℂ x).open_target.measurableSet).2 ?_
  rw [ae_iff]
  refine measure_mono_null ?_ (hnull x)
  intro z hz
  obtain ⟨hzt, hnot⟩ := not_imp.1 hz
  have hqs : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hzt
  refine ⟨(chartAt ℂ x).symm z, ⟨?_, hqs⟩, (chartAt ℂ x).right_inv hzt⟩
  intro hT
  apply hnot
  have hfun : (fun n => dilatationQuotient (localMapExprAt (e.symm.trans (en n)) x z) z) =
      fun n => dilatationQuotient (localMapExpr (e.symm.trans (en n)) ((chartAt ℂ x).symm z))
        (chartAt ℂ ((chartAt ℂ x).symm z) ((chartAt ℂ x).symm z)) :=
    funext fun n => s29_e7_D_inv (⇑(e.symm.trans (en n))) x hzt
  rw [hfun]
  exact hT


theorem ft_measurable_D_at {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [SecondCountableTopology Y] {f : X → Y} (hf : Continuous f) (x : X) :
    AEMeasurable (fun z => dilatationQuotient (localMapExprAt f x z) z)
      (volume.restrict (chartAt ℂ x).target) := by
  obtain ⟨s, hsc, hs⟩ := (isLindelof_univ (X := Y)).elim_countable_subcover (fun c : Y => (chartAt ℂ c).source)
    (fun c => (chartAt ℂ c).open_source) (fun y _ => mem_iUnion.2 ⟨y, mem_chart_source ℂ y⟩)
  haveI : Countable s := hsc.to_subtype
  set E : Y → Set ℂ := fun c => (chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' (f ⁻¹' (chartAt ℂ c).source)
    with hE
  have hEo : ∀ c, IsOpen (E c) := fun c =>
    (chartAt ℂ x).isOpen_inter_preimage_symm (hf.isOpen_preimage _ (chartAt ℂ c).open_source)
  have hcover : (chartAt ℂ x).target = ⋃ c : s, E c.1 := by
    ext z
    constructor
    · intro hz
      have := hs (mem_univ (f ((chartAt ℂ x).symm z)))
      simp only [mem_iUnion] at this
      obtain ⟨c, hcs, hc⟩ := this
      exact mem_iUnion.2 ⟨⟨c, hcs⟩, ⟨hz, hc⟩⟩
    · intro hz
      obtain ⟨c, hc⟩ := mem_iUnion.1 hz
      exact hc.1
  rw [hcover]
  refine aemeasurable_iUnion_iff.2 fun c => ?_
  set c := c.1
  have hae : (fun z => dilatationQuotient (localMapExprAt f x z) z) =ᵐ[volume.restrict (E c)]
      (fun z => dilatationQuotient (fun w => chartAt ℂ c (f ((chartAt ℂ x).symm w))) z) := by
    refine (ae_restrict_iff' (hEo c).measurableSet).2 (ae_of_all _ fun z hz => ?_)
    exact s29_e12_exprAt_gen hf x c hz.1 hz.2
  exact ((s29_e7_measurable_D _).aemeasurable).congr hae.symm


theorem ft_D_le_ae {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [SecondCountableTopology X] [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] {h : X ≃ₜ Y} {K : ℝ}
    (hh : IsKQCRS h K) (x : X) :
    ∀ᵐ z ∂(volume.restrict (chartAt ℂ x).target),
      dilatationQuotient (localMapExprAt h x z) z ≤ K := by
  set B : Set X := {p | ¬ (dilatationQuotient (localMapExpr h p) (chartAt ℂ p p) ≤ K)} with hB
  set W : X → Set X := fun p => (chartAt ℂ p).source ∩ h ⁻¹' (chartAt ℂ (h p)).source with hW
  have hWo : ∀ p, IsOpen (W p) := fun p =>
    (chartAt ℂ p).open_source.inter (h.continuous.isOpen_preimage _ (chartAt ℂ (h p)).open_source)
  have hWp : ∀ p, p ∈ W p := fun p => ⟨mem_chart_source ℂ p, mem_chart_source ℂ (h p)⟩
  have hWs : ∀ p, W p ⊆ (chartAt ℂ p).source := fun p => inter_subset_left
  have hBnull : ∀ p, volume (chartAt ℂ p '' (B ∩ W p)) = 0 := by
    intro p
    have hae := s29_e12_D_le_ae_local (hh.2 p)
    have hdom : MeasurableSet (localMapDomain h p) := (s23_localMapDomain_isOpen h.continuous p).measurableSet
    have hnull : volume {z | ¬ (z ∈ localMapDomain h p →
        dilatationQuotient (localMapExpr h p) z ≤ K)} = 0 :=
      (ae_restrict_iff' hdom).1 hae |> fun h' => by simpa [ae_iff] using h'
    refine measure_mono_null ?_ hnull
    rintro _ ⟨q, ⟨hqB, hqW⟩, rfl⟩
    have hqs : q ∈ (chartAt ℂ p).source := hqW.1
    have hz : chartAt ℂ p q ∈ localMapDomain h p := by
      refine ⟨(chartAt ℂ p).map_source hqs, ?_⟩
      show h ((chartAt ℂ p).symm (chartAt ℂ p q)) ∈ (chartAt ℂ (h p)).source
      rw [(chartAt ℂ p).left_inv hqs]
      exact hqW.2
    intro hcontra
    apply hqB
    have h1 := s29_e7_D_inv (⇑h) p (z := chartAt ℂ p q) ((chartAt ℂ p).map_source hqs)
    rw [(chartAt ℂ p).left_inv hqs] at h1
    have h2 := s29_e12_exprAt_gen h.continuous p (h p) (z := chartAt ℂ p q)
      ((chartAt ℂ p).map_source hqs) (by rw [(chartAt ℂ p).left_inv hqs]; exact hqW.2)
    calc dilatationQuotient (localMapExpr h q) (chartAt ℂ q q) =
          dilatationQuotient (localMapExprAt (⇑h) p (chartAt ℂ p q)) (chartAt ℂ p q) := h1.symm
      _ = dilatationQuotient (localMapExpr h p) (chartAt ℂ p q) := h2
      _ ≤ K := hcontra hz
  have hnullx := ft_null_cover W hWo hWp hWs hBnull x
  refine (ae_restrict_iff' (chartAt ℂ x).open_target.measurableSet).2 ?_
  rw [ae_iff]
  refine measure_mono_null ?_ hnullx
  intro z hz
  obtain ⟨hzt, hnot⟩ := not_imp.1 hz
  have hqs : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := (chartAt ℂ x).map_target hzt
  refine ⟨(chartAt ℂ x).symm z, ⟨?_, hqs⟩, (chartAt ℂ x).right_inv hzt⟩
  intro hle
  apply hnot
  rw [s29_e7_D_inv (⇑h) x hzt]
  exact hle

end


section

theorem ft_dom {X : Type u} {N : ℕ} (Q : Submodule ℝ (X → ℂ → ℂ)) (e : Q ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    (om : Q) (x : X) (z : ℂ) :
    ‖om.1 x z‖ ≤ ‖e om‖ * ∑ j : Fin N, ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 x z‖ := by
  have hrepr : om = ∑ j : Fin N, (e om j) • e.symm (EuclideanSpace.single j (1 : ℝ)) := by
    apply e.injective
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    have h := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr (e om)
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using h.symm
  have hval : om.1 x z = ∑ j : Fin N, ((e om j : ℝ) : ℂ) * (e.symm (EuclideanSpace.single j (1 : ℝ))).1 x z := by
    conv_lhs => rw [hrepr]
    simp [Complex.real_smul]
  rw [hval]
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le (e om) j) (norm_nonneg _)

theorem ft_Gsum {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {N : ℕ}
    (Q : Submodule ℝ (X → ℂ → ℂ)) (hQ : ∀ q ∈ Q, IsHolQuadDiff q) (e : Q ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    {x : ℕ → X} {P : ℕ → Set X} (hP : IsChartPartition X x P) :
    ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ∑ j : Fin N, ENNReal.ofReal ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖ =
      ∑ j : Fin N, quadDiffNorm (e.symm (EuclideanSpace.single j (1 : ℝ))).1 := by
  have hint : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ∑ j : Fin N, ENNReal.ofReal ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖ =
      ∑ j : Fin N, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ENNReal.ofReal ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖ := fun i =>
    lintegral_finsetSum' _ fun j _ => s29_e12_meas_norm (hQ _ (e.symm _).2) (x i) (hP.1 i).2
      (s29_e12_piece_sub hP i)
  simp only [hint]
  rw [Summable.tsum_finsetSum (fun j _ => ENNReal.summable)]
  exact Finset.sum_congr rfl fun j _ => (s29_e12_psum (hQ _ (e.symm _).2) hP).symm

theorem ft_key {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] {N : ℕ}
    (Q : Submodule ℝ (X → ℂ → ℂ)) (hQ : ∀ q ∈ Q, IsHolQuadDiff q) (e : Q ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    {x : ℕ → X} {P : ℕ → Set X} (hP : IsChartPartition X x P)
    (om om' : Q) :
    quadDiffNorm om.1 ≤ quadDiffNorm om'.1 + ENNReal.ofReal ‖e (om - om')‖ *
      ∑ j : Fin N, quadDiffNorm (e.symm (EuclideanSpace.single j (1 : ℝ))).1 := by
  rw [s29_e12_psum (hQ _ om.2) hP, s29_e12_psum (hQ _ om'.2) hP, ← ft_Gsum Q hQ e hP, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_add_left' (s29_e12_meas_norm (hQ _ om'.2) (x i) (hP.1 i).2 (s29_e12_piece_sub hP i))]
  refine lintegral_mono fun z => ?_
  have hd := ft_dom Q e (om - om') (x i) z
  have hsub : (om - om').1 (x i) z = om.1 (x i) z - om'.1 (x i) z := rfl
  rw [hsub] at hd
  have h1 : ‖om.1 (x i) z‖ ≤ ‖om'.1 (x i) z‖ + ‖e (om - om')‖ *
      ∑ j : Fin N, ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖ := by
    calc ‖om.1 (x i) z‖ = ‖om'.1 (x i) z + (om.1 (x i) z - om'.1 (x i) z)‖ := by rw [add_sub_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add_right hd _)
  calc ENNReal.ofReal ‖om.1 (x i) z‖
      ≤ ENNReal.ofReal (‖om'.1 (x i) z‖ + ‖e (om - om')‖ *
          ∑ j : Fin N, ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖) := ENNReal.ofReal_le_ofReal h1
    _ ≤ ENNReal.ofReal ‖om'.1 (x i) z‖ + ENNReal.ofReal ‖e (om - om')‖ *
          ∑ j : Fin N, ENNReal.ofReal ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖ := by
        refine (ENNReal.ofReal_add_le).trans (add_le_add_right (le_of_eq ?_) _)
        rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_sum_of_nonneg fun j _ => norm_nonneg _]
    _ = _ := by rw [add_comm]


theorem ft_quadDiffNorm_zero {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [SecondCountableTopology X] [Nonempty X] : quadDiffNorm (0 : X → ℂ → ℂ) = 0 := by
  obtain ⟨x, P, hP, -⟩ := ft_exists_chartPartition (S := X) (fun p => (chartAt ℂ p).source)
    (fun p => (chartAt ℂ p).open_source) (fun p => mem_chart_source ℂ p) (fun _ => subset_rfl)
  have hq0 : IsHolQuadDiff (0 : X → ℂ → ℂ) := (holQuadDiffSubmodule X).zero_mem
  rw [s29_e12_psum hq0 hP]
  simp

theorem ft_fin {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] {N : ℕ} (Q : Submodule ℝ (X → ℂ → ℂ))
    (hQ : ∀ q ∈ Q, IsHolQuadDiff q) (e : Q ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    (hb : ∀ j : Fin N, quadDiffNorm (e.symm (EuclideanSpace.single j (1 : ℝ))).1 ≠ ⊤)
    (v : EuclideanSpace ℝ (Fin N)) : quadDiffNorm (e.symm v).1 ≠ ⊤ := by
  have : Nonempty X := ConnectedSpace.toNonempty
  obtain ⟨x, P, hP, -⟩ := ft_exists_chartPartition (S := X) (fun p => (chartAt ℂ p).source)
    (fun p => (chartAt ℂ p).open_source) (fun p => mem_chart_source ℂ p) (fun _ => subset_rfl)
  have h := ft_key Q hQ e hP (e.symm v) 0
  have h0 : quadDiffNorm ((0 : Q).1) = 0 := ft_quadDiffNorm_zero
  rw [h0, zero_add] at h
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.sum_ne_top.2 fun j _ => hb j)) h

theorem ft_lower {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] {N : ℕ} (Q : Submodule ℝ (X → ℂ → ℂ)) (hQ : ∀ q ∈ Q, IsHolQuadDiff q)
    (e : Q ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    (hb : ∀ j : Fin N, quadDiffNorm (e.symm (EuclideanSpace.single j (1 : ℝ))).1 ≠ ⊤)
    [Nonempty X] :
    ∃ c : ℝ, 0 < c ∧ ∀ om : Q, ‖e om‖ = 1 →
      ENNReal.ofReal c ≤ quadDiffNorm om.1 := by
  by_cases hne : ∃ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1
  swap
  · exact ⟨1, one_pos, fun om hom => absurd ⟨e om, hom⟩ hne⟩
  obtain ⟨x, P, hP, -⟩ := ft_exists_chartPartition (S := X) (fun p => (chartAt ℂ p).source)
    (fun p => (chartAt ℂ p).open_source) (fun p => mem_chart_source ℂ p) (fun _ => subset_rfl)
  set A : ℝ≥0∞ := ∑ j : Fin N, quadDiffNorm (e.symm (EuclideanSpace.single j (1 : ℝ))).1 with hA
  have hAfin : A ≠ ⊤ := ENNReal.sum_ne_top.2 fun j _ => hb j
  set f : EuclideanSpace ℝ (Fin N) → ℝ := fun v => (quadDiffNorm (e.symm v).1).toReal with hf
  have hfin : ∀ v, quadDiffNorm (e.symm v).1 ≠ ⊤ := fun v => ft_fin Q hQ e hb v
  have hLip : ∀ v v', f v ≤ f v' + A.toReal * ‖v - v'‖ := by
    intro v v'
    have h := ft_key Q hQ e hP (e.symm v) (e.symm v')
    rw [← map_sub, LinearEquiv.apply_symm_apply] at h
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin v', ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin⟩) h
    rw [ENNReal.toReal_add (hfin v') (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)] at h2
    linarith
  have hlip : LipschitzWith A.toReal.toNNReal f := by
    refine LipschitzWith.of_dist_le_mul fun v v' => ?_
    rw [Real.coe_toNNReal _ ENNReal.toReal_nonneg, Real.dist_eq, dist_eq_norm, abs_le]
    constructor
    · have := hLip v' v
      rw [norm_sub_rev] at this
      linarith
    · have := hLip v v'
      linarith
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin N)) 1).exists_isMinOn
    (by obtain ⟨v, hv⟩ := hne; exact ⟨v, by simpa using hv⟩) hlip.continuous.continuousOn
  have hv₀n : ‖v₀‖ = 1 := by simpa using hv₀
  have hpos : ∀ v : EuclideanSpace ℝ (Fin N), ‖v‖ = 1 → 0 < f v := by
    intro v hv
    have hv0 : v ≠ 0 := by
      rintro rfl
      simp at hv
    have hne0 : (e.symm v).1 ≠ 0 := by
      intro h0
      apply hv0
      have : e.symm v = 0 := Subtype.ext h0
      simpa using congrArg e this
    exact ENNReal.toReal_pos (s26_quadDiffNorm_pos (hQ _ (e.symm v).2) hne0) (hfin v)
  refine ⟨f v₀, hpos v₀ hv₀n, fun om hom => ?_⟩
  have h1 : f v₀ ≤ f (e om) := hmin (by simpa using hom)
  have h2 : f (e om) = (quadDiffNorm om.1).toReal := by simp [hf]
  rw [h2] at h1
  calc ENNReal.ofReal (f v₀) ≤ ENNReal.ofReal (quadDiffNorm om.1).toReal := ENNReal.ofReal_le_ofReal h1
    _ = quadDiffNorm om.1 := ENNReal.ofReal_toReal (by simpa using hfin (e om))


theorem ft_dct {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] {N : ℕ} (Q : Submodule ℝ (X → ℂ → ℂ))
    (hQ : ∀ q ∈ Q, IsHolQuadDiff q) (e : Q ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    (hb : ∀ j : Fin N, quadDiffNorm (e.symm (EuclideanSpace.single j (1 : ℝ))).1 ≠ ⊤)
    {Y : ℕ → Type u} [∀ n, TopologicalSpace (Y n)] [∀ n, ChartedSpace ℂ (Y n)]
    [∀ n, IsManifold 𝓘(ℂ) ω (Y n)] [∀ n, SecondCountableTopology (Y n)]
    (h : ∀ n, X ≃ₜ Y n) {K : ℝ}
    (hK : ∀ᶠ n in atTop, IsKQCRS (h n) K)
    (hconv : ∀ x : X, ∀ᵐ z ∂(volume.restrict (chartAt ℂ x).target),
      Tendsto (fun n => dilatationQuotient (localMapExprAt (h n) x z) z) atTop (𝓝 1))
    (om : ℕ → Q) {M : ℝ} (hM : ∀ n, ‖e (om n)‖ ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      surfaceIntegral (om n).1 (fun x z =>
          ENNReal.ofReal (dilatationQuotient (localMapExprAt (h n) x z) z)) ≤
        quadDiffNorm (om n).1 + ENNReal.ofReal ε := by
  classical
  have : Nonempty X := ConnectedSpace.toNonempty
  obtain ⟨x, P, hP, -⟩ := ft_exists_chartPartition (S := X) (fun p => (chartAt ℂ p).source)
    (fun p => (chartAt ℂ p).open_source) (fun p => mem_chart_source ℂ p) (fun _ => subset_rfl)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hK
  set G0 : ℕ → ℂ → ℝ≥0∞ := fun i z =>
    ∑ j : Fin N, ENNReal.ofReal ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖ with hG0
  set G : ℕ → ℂ → ℝ≥0∞ := fun i z => ENNReal.ofReal M * G0 i z with hG
  have hA0 : ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, G0 i z =
      ∑ j : Fin N, quadDiffNorm (e.symm (EuclideanSpace.single j (1 : ℝ))).1 := ft_Gsum Q hQ e hP
  have hA : ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, G i z =
      ENNReal.ofReal M * ∑ j : Fin N, quadDiffNorm (e.symm (EuclideanSpace.single j (1 : ℝ))).1 := by
    simp only [hG]
    simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [ENNReal.tsum_mul_left, hA0]
  have hAfin : ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, G i z ≠ ⊤ := by
    rw [hA]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.2 fun j _ => hb j)
  have hG0fin : ∀ i z, G0 i z ≠ ⊤ := fun i z => ENNReal.sum_ne_top.2 fun j _ => ENNReal.ofReal_ne_top
  have hGfin : ∀ i z, G i z ≠ ⊤ := fun i z => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hG0fin i z)
  have hgi : ∀ i, ∫⁻ z in chartAt ℂ (x i) '' P i, G i z ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top hAfin (ENNReal.le_tsum (f := fun i => ∫⁻ z in chartAt ℂ (x i) '' P i, G i z) i)
  have hGmeas : ∀ i, AEMeasurable (G i) (volume.restrict (chartAt ℂ (x i) '' P i)) := fun i =>
    (Finset.aemeasurable_fun_sum _ fun j _ =>
      s29_e12_meas_norm (hQ _ (e.symm _).2) (x i) (hP.1 i).2 (s29_e12_piece_sub hP i)).const_mul _
  set Dn : ℕ → ℕ → ℂ → ℝ := fun n i z => dilatationQuotient (localMapExprAt (h n) (x i) z) z with hDn
  set F : ℕ → ℕ → ℂ → ℝ≥0∞ := fun n i z => ENNReal.ofReal (Dn n i z - 1) * G i z with hF
  set a : ℕ → ℕ → ℝ≥0∞ := fun n i => ∫⁻ z in chartAt ℂ (x i) '' P i, F n i z with ha
  -- (1) for each piece, the remainders tend to `0` (dominated convergence on the piece)
  have hlimi : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 0) := by
    intro i
    have hmeasD : ∀ n, AEMeasurable (fun z => Dn n i z) (volume.restrict (chartAt ℂ (x i) '' P i)) :=
      fun n => (ft_measurable_D_at (h n).continuous (x i)).mono_set (s29_e12_piece_sub hP i)
    have hmeasF : ∀ n, AEMeasurable (F n i) (volume.restrict (chartAt ℂ (x i) '' P i)) := fun n =>
      (ENNReal.measurable_ofReal.comp_aemeasurable ((hmeasD n).sub_const 1)).mul (hGmeas i)
    have hbound : ∀ n, N0 ≤ n → ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)),
        F n i z ≤ ENNReal.ofReal (K - 1) * G i z := by
      intro n hn
      have h1 := ft_D_le_ae (hN0 n hn) (x i)
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (s29_e12_piece_sub hP i) h1] with z hz
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
    have hfinb : ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal (K - 1) * G i z ≠ ⊤ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hgi i)
    have hlim : ∀ᵐ z ∂(volume.restrict (chartAt ℂ (x i) '' P i)),
        Tendsto (fun n => F n i z) atTop (𝓝 0) := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset (s29_e12_piece_sub hP i) (hconv (x i))] with z hz
      have h1 : Tendsto (fun n => ENNReal.ofReal (Dn n i z - 1)) atTop (𝓝 0) := by
        have := ENNReal.tendsto_ofReal (hz.sub_const 1)
        simpa using this
      have := ENNReal.Tendsto.mul_const h1 (Or.inr (hGfin i z))
      simpa using this
    have hshift : Tendsto (fun n => a (n + N0) i) atTop (𝓝 0) := by
      have := tendsto_lintegral_of_dominated_convergence'
        (μ := volume.restrict (chartAt ℂ (x i) '' P i)) (F := fun n z => F (n + N0) i z)
        (f := fun _ => (0 : ℝ≥0∞)) (fun z => ENNReal.ofReal (K - 1) * G i z)
        (fun n => hmeasF _) (fun n => hbound (n + N0) (by omega)) hfinb
        (hlim.mono fun z hz => hz.comp (tendsto_add_atTop_nat N0))
      simpa using this
    exact (tendsto_add_atTop_iff_nat N0).1 hshift
  -- (2) the series of remainders tends to `0` (dominated convergence for the counting measure)
  have hR : Tendsto (fun n => ∑' i, a n i) atTop (𝓝 0) := by
    have hbi : ∀ n, N0 ≤ n → ∀ i, a n i ≤ ENNReal.ofReal (K - 1) *
        ∫⁻ z in chartAt ℂ (x i) '' P i, G i z := by
      intro n hn i
      have h1 := ft_D_le_ae (hN0 n hn) (x i)
      calc a n i ≤ ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal (K - 1) * G i z := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_of_ae_restrict_of_subset (s29_e12_piece_sub hP i) h1] with z hz
            exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    have hfin : (∫⁻ i, ENNReal.ofReal (K - 1) * (∫⁻ z in chartAt ℂ (x i) '' P i, G i z) ∂Measure.count) ≠ ⊤ := by
      rw [lintegral_count, ENNReal.tsum_mul_left]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAfin
    have hser : Tendsto (fun n => ∫⁻ i, a (n + N0) i ∂Measure.count) atTop
        (𝓝 (∫⁻ _, (0 : ℝ≥0∞) ∂Measure.count)) :=
      tendsto_lintegral_of_dominated_convergence (μ := Measure.count)
        (F := fun n (i : ℕ) => a (n + N0) i)
        (f := fun _ => (0 : ℝ≥0∞))
        (fun i => ENNReal.ofReal (K - 1) * ∫⁻ z in chartAt ℂ (x i) '' P i, G i z)
        (fun n => Measurable.of_discrete) (fun n => ae_of_all _ fun i => hbi (n + N0) (by omega) i) hfin
        (ae_of_all _ fun i => (hlimi i).comp (tendsto_add_atTop_nat N0))
    simp only [lintegral_count, lintegral_zero] at hser
    exact (tendsto_add_atTop_iff_nat N0).1 hser
  -- (3) the estimate for each `n`
  filter_upwards [hR.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))] with n hRn
  have h1 : surfaceIntegral (om n).1 (fun x z =>
        ENNReal.ofReal (dilatationQuotient (localMapExprAt (h n) x z) z)) ≤
      quadDiffNorm (om n).1 + ∑' i, a n i := by
    rw [s29_e7_D_partition (h n) (hQ _ (om n).2) hP, s29_e12_psum (hQ _ (om n).2) hP, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [ha]
    simp only [hF]
    rw [← lintegral_add_left' (s29_e12_meas_norm (hQ _ (om n).2) (x i) (hP.1 i).2 (s29_e12_piece_sub hP i))]
    refine lintegral_mono fun z => ?_
    have hd := ft_dom Q e (om n) (x i) z
    have hQG : ENNReal.ofReal ‖(om n).1 (x i) z‖ ≤ G i z := by
      have hd' : ‖(om n).1 (x i) z‖ ≤ M * ∑ j : Fin N, ‖(e.symm (EuclideanSpace.single j (1 : ℝ))).1 (x i) z‖ :=
        hd.trans (mul_le_mul_of_nonneg_right (hM n) (Finset.sum_nonneg fun j _ => norm_nonneg _))
      refine (ENNReal.ofReal_le_ofReal hd').trans (le_of_eq ?_)
      rw [hG, hG0, ENNReal.ofReal_mul hM0, ENNReal.ofReal_sum_of_nonneg fun j _ => norm_nonneg _]
    have hD : ENNReal.ofReal (Dn n i z) ≤ 1 + ENNReal.ofReal (Dn n i z - 1) := by
      calc ENNReal.ofReal (Dn n i z) = ENNReal.ofReal (1 + (Dn n i z - 1)) := by rw [add_sub_cancel]
        _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (Dn n i z - 1) := ENNReal.ofReal_add_le
        _ = 1 + ENNReal.ofReal (Dn n i z - 1) := by rw [ENNReal.ofReal_one]
    calc ENNReal.ofReal (Dn n i z) * ENNReal.ofReal ‖(om n).1 (x i) z‖
        ≤ (1 + ENNReal.ofReal (Dn n i z - 1)) * ENNReal.ofReal ‖(om n).1 (x i) z‖ :=
          mul_le_mul' hD le_rfl
      _ = ENNReal.ofReal ‖(om n).1 (x i) z‖ + ENNReal.ofReal (Dn n i z - 1) *
            ENNReal.ofReal ‖(om n).1 (x i) z‖ := by rw [add_mul, one_mul]
      _ ≤ ENNReal.ofReal ‖(om n).1 (x i) z‖ + ENNReal.ofReal (Dn n i z - 1) * G i z :=
          add_le_add_right (mul_le_mul' le_rfl hQG) _
  exact h1.trans (add_le_add_right hRn.le _)


end


/-- The carrier of a surface of finite type is second countable. -/
theorem ft_secondCountable {g n m : ℕ} (Z : FiniteTypeRS.{u} g n m) : SecondCountableTopology Z.carrier := by
  haveI : SecondCountableTopology Z.structure'.X.carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ℂ Z.structure'.X.carrier
  exact Z.structure'.embedding.isEmbedding.secondCountableTopology

/-- `K`-quasiconformality of a Teichmüller map with parameter `k`: `K = (1 + k) / (1 - k)`. -/
theorem ft_isKQCRS_of_teich {S₁ : Type u} [TopologicalSpace S₁] [ChartedSpace ℂ S₁] [IsManifold 𝓘(ℂ) ω S₁]
    [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf : IsTeichmullerMap f q q' k) :
    IsKQCRS f ((1 + k) / (1 - k)) := by
  have h0 := hf.k_nonneg
  have h1 := hf.k_lt_one
  refine s29_m_isKQCRS_of_le hf.qc ?_ (teichmullerMap_beltrami hf).2.le
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- A uniform quasiconformal bound for the comparison maps `fₙ ∘ f⁻¹`. -/
theorem ft_uniform_K {S₁ : Type u} [TopologicalSpace S₁] [ChartedSpace ℂ S₁] [IsManifold 𝓘(ℂ) ω S₁]
    {Y : ℕ → Type u} [∀ j, TopologicalSpace (Y j)] [∀ j, ChartedSpace ℂ (Y j)] [∀ j, IsManifold 𝓘(ℂ) ω (Y j)]
    [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
    {f : S₀ ≃ₜ S₁} {q : S₀ → ℂ → ℂ} {q' : S₁ → ℂ → ℂ} {k : ℝ} (hf : IsTeichmullerMap f q q' k)
    {fn : ∀ j, S₀ ≃ₜ Y j} {qn : ℕ → S₀ → ℂ → ℂ} {qn' : ∀ j, Y j → ℂ → ℂ} {kn : ℕ → ℝ}
    (hfn : ∀ j, IsTeichmullerMap (fn j) (qn j) (qn' j) (kn j)) (hkconv : Tendsto kn atTop (𝓝 k)) :
    ∃ K : ℝ, ∀ᶠ j in atTop, IsKQCRS (f.symm.trans (fn j)) K := by
  have hk0 := hf.k_nonneg
  have hk1 := hf.k_lt_one
  have hK₁ := ft_isKQCRS_of_teich hf
  have hlt : k < (k + 1) / 2 := by linarith
  have hev : ∀ᶠ j in atTop, kn j < (k + 1) / 2 := hkconv.eventually (eventually_lt_nhds hlt)
  refine ⟨(1 + (k + 1) / 2) / (1 - (k + 1) / 2) * ((1 + k) / (1 - k)), ?_⟩
  filter_upwards [hev] with j hj
  have hkn0 := (hfn j).k_nonneg
  have hKn := ft_isKQCRS_of_teich (hfn j)
  have hmono : (1 + kn j) / (1 - kn j) ≤ (1 + (k + 1) / 2) / (1 - (k + 1) / 2) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hKn' : IsKQCRS (fn j) ((1 + (k + 1) / 2) / (1 - (k + 1) / 2)) :=
    s29_m_isKQCRS_of_le (hfn j).qc (hKn.1.trans hmono)
      ((maxDilatationRS_le hKn).trans (ENNReal.ofReal_le_ofReal hmono))
  have := (eq23_4 (s29_m_isKQCRS_symm hK₁) hKn').1
  rwa [mul_comm] at this


/-- Evaluation of an element of a finite-dimensional space of differentials in the coordinate basis. -/
theorem ft_eval {X : Type u} {N : ℕ} (Q : Submodule ℝ (X → ℂ → ℂ))
    (e : Q ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N)) (om : Q) (x : X) (z : ℂ) :
    om.1 x z = ∑ j : Fin N, ((e om j : ℝ) : ℂ) * (e.symm (EuclideanSpace.single j (1 : ℝ))).1 x z := by
  have hrepr : om = ∑ j : Fin N, (e om j) • e.symm (EuclideanSpace.single j (1 : ℝ)) := by
    apply e.injective
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    have h := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr (e om)
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using h.symm
  conv_lhs => rw [hrepr]
  simp [Complex.real_smul]

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- **Finite area of the coordinate basis.**  Every direction of `Q(S₁)` is the initial differential of an
admissible Teichmüller map (the chart), hence has finite area (`s82cmp_core_all`). -/
theorem ft_basis_finite {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) {N : ℕ}
    (F₀ : FiniteTypeStructure S₀ g n m) (e : admissibleQDInterior F₀ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    (Φ : EuclideanSpace ℝ (Fin N) → TeichSpaceFiniteType S₀ g n m)
    (R4 : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin N)) 1, v ≠ 0 →
        ∃ (A : MarkedFiniteTypeRS S₀ g n m) (f : S₀ ≃ₜ A.X.carrier) (q : admissibleQDInterior F₀)
          (q' : A.X.carrier → ℂ → ℂ) (k : ℝ),
          Quot.mk _ A = Φ v ∧ ContinuousMap.Homotopic (A.marking : C(S₀, A.X.carrier)) (f : C(S₀, A.X.carrier)) ∧
          IsAdmissibleTeichmullerMap F₀ f q.1 q' k ∧ 0 < k ∧ k < 1 ∧ ‖v‖ = k ∧ v = (k / ‖e q‖) • e q)
    (j : Fin N) : quadDiffNorm (e.symm (EuclideanSpace.single j (1 : ℝ))).1 ≠ ⊤ := by
  classical
  set w : EuclideanSpace ℝ (Fin N) := EuclideanSpace.single j (1 : ℝ) with hw
  have hw1 : ‖w‖ = 1 := by simp [hw]
  set v : EuclideanSpace ℝ (Fin N) := (1 / 2 : ℝ) • w with hv
  have hvn : ‖v‖ = 1 / 2 := by
    rw [hv, norm_smul, hw1, mul_one, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  have hvb : v ∈ ball (0 : EuclideanSpace ℝ (Fin N)) 1 := by
    rw [mem_ball_zero_iff, hvn]; norm_num
  have hv0 : v ≠ 0 := by
    intro h; rw [h, norm_zero] at hvn; norm_num at hvn
  obtain ⟨A, f, q, q', k, -, -, hadm, hk0, hk1, hkn, hdir⟩ := R4 v hvb hv0
  have hk : k = 1 / 2 := by rw [← hkn, hvn]
  have hqne : e q ≠ 0 := by
    intro h; apply hv0; rw [hdir, h, smul_zero]
  have hcpos : 0 < ‖e q‖ := norm_pos_iff.2 hqne
  set c := ‖e q‖ with hc
  have heq : e q = c • w := by
    have h1 : (c / k) • v = e q := by
      rw [hdir, smul_smul, show c / k * (k / c) = 1 by field_simp, one_smul]
    rw [← h1, hv, smul_smul, hk]
    congr 1
    field_simp
  have hqeq : q = c • e.symm w := by
    apply e.injective
    rw [heq, map_smul, LinearEquiv.apply_symm_apply]
  have hq1 : q.1 = (c : ℂ) • (e.symm w).1 := by
    rw [hqeq]
    funext x z
    simp [Complex.real_smul]
  have hfin : quadDiffNorm q.1 < ⊤ :=
    (s82cmp_core_all hex F₀ A.X f hadm.2.qc hadm hk0 (ContinuousMap.Homotopic.refl _)).1
  rw [hq1, s82cmp_quadDiffNorm_smul _ hcpos] at hfin
  intro htop
  rw [htop, ENNReal.mul_top (by simpa using hcpos)] at hfin
  exact lt_irrefl _ hfin

end

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- The coordinate bound: a differential of area `1` has coordinates of norm `≤ c⁻¹`. -/
theorem ft_coord_bound {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] {N : ℕ} (Q : Submodule ℝ (X → ℂ → ℂ))
    (hQ : ∀ q ∈ Q, IsHolQuadDiff q) (e : Q ≃ₗ[ℝ] EuclideanSpace ℝ (Fin N))
    (hb : ∀ j : Fin N, quadDiffNorm (e.symm (EuclideanSpace.single j (1 : ℝ))).1 ≠ ⊤) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ om : Q, quadDiffNorm om.1 = 1 → ‖e om‖ ≤ M := by
  have : Nonempty X := ConnectedSpace.toNonempty
  obtain ⟨c, hc, hlow⟩ := ft_lower Q hQ e hb
  refine ⟨c⁻¹, (inv_pos.2 hc).le, fun om hom => ?_⟩
  have hne : e om ≠ 0 := by
    intro h0
    have : om = 0 := e.injective (by rw [h0, map_zero])
    rw [this] at hom
    have h00 : quadDiffNorm ((0 : Q).1) = 0 := ft_quadDiffNorm_zero
    rw [h00] at hom
    exact zero_ne_one hom
  set t := ‖e om‖ with ht
  have htpos : 0 < t := norm_pos_iff.2 hne
  have h1 : ‖e ((t⁻¹ : ℝ) • om)‖ = 1 := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 htpos)]
    exact inv_mul_cancel₀ htpos.ne'
  have h2 := hlow _ h1
  have h3 : ((t⁻¹ : ℝ) • om).1 = ((t⁻¹ : ℝ) : ℂ) • om.1 := by
    funext x z; simp [Complex.real_smul]
  rw [h3, s82cmp_quadDiffNorm_smul _ (inv_pos.2 htpos), hom, mul_one] at h2
  have h4 := (ENNReal.ofReal_le_ofReal_iff (inv_pos.2 htpos).le).1 h2
  rw [le_inv_comm₀ hc htpos] at h4
  exact h4

/-- **Core of L32318.**  If the Teichmüller data `(fₙ, qₙ, kₙ)` converge pointwise to `(f, q, k)`, the marked surfaces
`Aₙ` converge to `A` in `d_T`. -/
theorem ft_core {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    {A : MarkedFiniteTypeRS S₀ g n m} {f : S₀ ≃ₜ A.X.carrier}
    (hfA : ContinuousMap.Homotopic (A.marking : C(S₀, A.X.carrier)) (f : C(S₀, A.X.carrier)))
    {q : S₀ → ℂ → ℂ} {q' : A.X.carrier → ℂ → ℂ} {k : ℝ} (hf : IsTeichmullerMap f q q' k)
    {An : ℕ → MarkedFiniteTypeRS S₀ g n m} {fn : ∀ j, S₀ ≃ₜ (An j).X.carrier}
    (hfn : ∀ j, ContinuousMap.Homotopic ((An j).marking : C(S₀, (An j).X.carrier)) (fn j : C(S₀, (An j).X.carrier)))
    {qn : ℕ → S₀ → ℂ → ℂ} {qn' : ∀ j, (An j).X.carrier → ℂ → ℂ} {kn : ℕ → ℝ}
    (hTn : ∀ j, IsTeichmullerMap (fn j) (qn j) (qn' j) (kn j))
    (hconv : ∀ x z, Tendsto (fun j => qn j x z) atTop (𝓝 (q x z))) (hkconv : Tendsto kn atTop (𝓝 k))
    (eA : admissibleQDInterior A.X.structure' ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior A.X.structure'))))
    (hb : ∀ j, quadDiffNorm (eA.symm (EuclideanSpace.single j (1 : ℝ))).1 ≠ ⊤) :
    Tendsto (fun j => teichDistanceFT (Quot.mk _ A) (Quot.mk _ (An j))) atTop (𝓝 0) := by
  classical
  haveI : SecondCountableTopology A.X.carrier := ft_secondCountable A.X
  haveI : ∀ j, SecondCountableTopology (An j).X.carrier := fun j => ft_secondCountable (An j).X
  haveI : Nonempty A.X.carrier := ConnectedSpace.toNonempty
  have hQ : ∀ q ∈ admissibleQDInterior A.X.structure', IsHolQuadDiff q :=
    (admissibleQDInterior_holomorphic A.X.structure').1
  obtain ⟨M, hM0, hMb⟩ := ft_coord_bound (admissibleQDInterior A.X.structure') hQ eA hb
  obtain ⟨K, hK⟩ := ft_uniform_K hf hTn hkconv
  have hae := ft_ae hf hTn hconv hkconv
  set a : ∀ j, A.X.carrier ≃ₜ (An j).X.carrier := fun j => f.symm.trans (fn j) with ha
  have haqc : ∀ j, IsQCRS (a j) := by
    intro j
    obtain ⟨K1, h1⟩ := hf.qc
    obtain ⟨K2, h2⟩ := (hTn j).qc
    exact ⟨_, (eq23_4 (s29_m_isKQCRS_symm h1) h2).1⟩
  -- the extremal comparison maps
  have hext := fun j => s82cmp_extremal_comparison hex A.X.structure' (An j).X (a j) (haqc j)
  choose h hhqc hhhom hhmin hhcase using hext
  -- the differentials of the extremal comparison
  have hom_ex : ∀ j, ∃ om : admissibleQDInterior A.X.structure', ‖eA om‖ ≤ M ∧ (IsBiholomorphic (h j) ∨ (quadDiffNorm om.1 = 1 ∧
      maxDilatationRS (h j) ≤ surfaceIntegral om.1
        (fun x z => ENNReal.ofReal (dilatationQuotient (localMapExprAt (a j) x z) z)))) := by
    intro j
    rcases hhcase j with hb' | ⟨r, r', kk, hkk, hadm, hr1, hle⟩
    · exact ⟨0, by simpa using hM0, Or.inl hb'⟩
    · have hmem : r ∈ admissibleQDInterior A.X.structure' := hadm.1
      exact ⟨⟨r, hmem⟩, hMb ⟨r, hmem⟩ hr1, Or.inr ⟨hr1, hle⟩⟩
  choose om hom hcase using hom_ex
  -- distance estimates
  have hdist : ∀ j, teichDistanceFT (Quot.mk _ A) (Quot.mk _ (An j)) ≤
      (1 / 2) * Real.log (maxDilatationRS (h j)).toReal := by
    intro j
    refine csInf_le (ft_teichSet_bddBelow _ _) ⟨A, An j, h j, rfl, rfl, hhqc j, ?_, rfl⟩
    -- `h j ∘ marking_A ≃ a j ∘ f = f_j ≃ marking_{A_j}`
    have e1 : ContinuousMap.Homotopic ((h j : C(A.X.carrier, (An j).X.carrier)).comp
        (A.marking : C(S₀, A.X.carrier))) ((a j : C(A.X.carrier, (An j).X.carrier)).comp
        (A.marking : C(S₀, A.X.carrier))) :=
      (hhhom j).comp (ContinuousMap.Homotopic.refl _)
    have e2 : ContinuousMap.Homotopic ((a j : C(A.X.carrier, (An j).X.carrier)).comp
        (A.marking : C(S₀, A.X.carrier))) ((a j : C(A.X.carrier, (An j).X.carrier)).comp
        (f : C(S₀, A.X.carrier))) :=
      (ContinuousMap.Homotopic.refl _).comp hfA
    have e3 : (a j : C(A.X.carrier, (An j).X.carrier)).comp (f : C(S₀, A.X.carrier)) =
        (fn j : C(S₀, (An j).X.carrier)) := by
      ext x
      simp [ha]
    rw [e3] at e2
    exact e1.trans (e2.trans (hfn j).symm)
  have hnn : ∀ j, 0 ≤ teichDistanceFT (Quot.mk _ A) (Quot.mk _ (An j)) :=
    fun j => ft_teichDistanceFT_nonneg _ _
  refine tendsto_order.2 ⟨fun a' ha' => Eventually.of_forall fun j => lt_of_lt_of_le ha' (hnn j), fun a' ha' => ?_⟩
  -- choose `ε` with `½ log (1 + ε) < a'`
  have hε : 0 < Real.exp a' - 1 := by linarith [Real.add_one_lt_exp ha'.ne']
  have hdct := ft_dct (admissibleQDInterior A.X.structure') hQ eA hb (Y := fun j => (An j).X.carrier) (fun j => a j) hK hae om hom hε
  filter_upwards [hdct] with j hj
  refine lt_of_le_of_lt (hdist j) ?_
  have hKb : maxDilatationRS (h j) ≤ ENNReal.ofReal (Real.exp a') := by
    rcases hcase j with hbh | ⟨h1, hle⟩
    · have h1' : IsKQCRS (h j) 1 := (isKQCRS_one_iff (h j)).2 hbh
      calc maxDilatationRS (h j) ≤ ENNReal.ofReal 1 := maxDilatationRS_le h1'
        _ ≤ ENNReal.ofReal (Real.exp a') := ENNReal.ofReal_le_ofReal (by
          have := Real.add_one_le_exp a'
          linarith)
    · refine hle.trans (hj.trans (le_of_eq ?_))
      rw [h1, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hε.le]
      congr 1
      ring
  have hKt : (maxDilatationRS (h j)).toReal ≤ Real.exp a' :=
    (ENNReal.toReal_le_toReal (s29_m_maxDilatationRS_ne_top (hhqc j)) ENNReal.ofReal_ne_top).2 hKb
      |>.trans (le_of_eq (ENNReal.toReal_ofReal (Real.exp_pos a').le))
  have hone : 1 ≤ (maxDilatationRS (h j)).toReal := s29_m_one_le_toReal (hhqc j)
  have hlog : Real.log (maxDilatationRS (h j)).toReal ≤ a' := by
    calc Real.log (maxDilatationRS (h j)).toReal ≤ Real.log (Real.exp a') :=
          Real.log_le_log (by linarith) hKt
      _ = a' := Real.log_exp a'
  have hlogn : 0 ≤ Real.log (maxDilatationRS (h j)).toReal := Real.log_nonneg hone
  linarith

end

section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

/-- The radial function `t ↦ ½ log((1 + t)/(1 - t))` tends to `0` at `0`. -/
theorem ft_radial_tendsto :
    Tendsto (fun t : ℝ => (1 / 2 : ℝ) * Real.log ((1 + t) / (1 - t))) (𝓝 0) (𝓝 0) := by
  have hc : ContinuousAt (fun t : ℝ => (1 / 2 : ℝ) * Real.log ((1 + t) / (1 - t))) 0 := by
    refine continuousAt_const.mul (ContinuousAt.log ?_ ?_)
    · exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
    · norm_num
  have := hc.tendsto
  simpa using this

/-- **L32318: parameter convergence implies metric convergence.** -/
theorem s82td_param_to_metric {g n m : ℕ} (hex : ¬ IsExceptionalType g n m) (F₀ : FiniteTypeStructure S₀ g n m)
    (e : admissibleQDInterior F₀ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))))
    (Φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))) → TeichSpaceFiniteType S₀ g n m)
    (R3 : Φ 0 = Quot.mk _ ⟨⟨S₀, F₀⟩, Homeomorph.refl S₀, isQCRS_refl⟩)
    (R4 : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1, v ≠ 0 →
        ∃ (A : MarkedFiniteTypeRS S₀ g n m) (f : S₀ ≃ₜ A.X.carrier) (q : admissibleQDInterior F₀) (q' : A.X.carrier → ℂ → ℂ) (k : ℝ),
          Quot.mk _ A = Φ v ∧ ContinuousMap.Homotopic (A.marking : C(S₀, A.X.carrier)) (f : C(S₀, A.X.carrier)) ∧
          IsAdmissibleTeichmullerMap F₀ f q.1 q' k ∧ 0 < k ∧ k < 1 ∧ ‖v‖ = k ∧ v = (k / ‖e q‖) • e q) :
    ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1,
      ∀ vs : ℕ → EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))),
        (∀ i, vs i ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1) →
        Tendsto vs atTop (𝓝 v) → Tendsto (fun j => teichDistanceFT (Φ (vs j)) (Φ v)) atTop (𝓝 0) := by
  classical
  intro v hv vs hvs hlim
  by_cases hv0 : v = 0
  · -- radial case
    subst hv0
    have hrad : ∀ j, teichDistanceFT (Φ (vs j)) (Φ 0) = (1 / 2 : ℝ) * Real.log ((1 + ‖vs j‖) / (1 - ‖vs j‖)) := by
      intro j
      by_cases hz : vs j = 0
      · rw [hz, norm_zero]
        simp [ft_teichDistanceFT_self]
      · obtain ⟨A, f, q, q', k, h1, h2, h3, h4, h5, h6, -⟩ := R4 (vs j) (hvs j) hz
        have := ft_radial_distance hex F₀ A f h3 h2
        rw [ft_teichDistanceFT_symm, R3, ← h1, this, ← h6]
    simp_rw [hrad]
    have h0 : Tendsto (fun j => ‖vs j‖) atTop (𝓝 0) := by
      simpa using hlim.norm
    exact ft_radial_tendsto.comp h0
  · -- data at `v` and at the `vs j`
    obtain ⟨A, f, q, q', k, hA, hAhom, hadm, hk0, hk1, hkn, hdir⟩ := R4 v hv hv0
    have hdata : ∀ j, ∃ (Aj : MarkedFiniteTypeRS S₀ g n m) (fj : S₀ ≃ₜ Aj.X.carrier) (qj : admissibleQDInterior F₀)
        (qj' : Aj.X.carrier → ℂ → ℂ) (kj : ℝ),
        ContinuousMap.Homotopic (Aj.marking : C(S₀, Aj.X.carrier)) (fj : C(S₀, Aj.X.carrier)) ∧
        IsAdmissibleTeichmullerMap F₀ fj qj.1 qj' kj ∧
        (vs j ≠ 0 → Quot.mk _ Aj = Φ (vs j) ∧ ‖vs j‖ = kj ∧ vs j = (kj / ‖e qj‖) • e qj) := by
      intro j
      by_cases hz : vs j = 0
      · exact ⟨A, f, q, q', k, hAhom, hadm, fun h => absurd hz h⟩
      · obtain ⟨Aj, fj, qj, qj', kj, h1, h2, h3, h4, h5, h6, h7⟩ := R4 (vs j) (hvs j) hz
        exact ⟨Aj, fj, qj, qj', kj, h2, h3, fun _ => ⟨h1, h6, h7⟩⟩
    choose Aj fj qj qj' kj hhomj hadmj hprop using hdata
    -- eventually `vs j ≠ 0`
    have hev : ∀ᶠ j in atTop, vs j ≠ 0 := hlim.eventually (isOpen_ne.mem_nhds hv0)
    -- the chart of the limit surface
    obtain ⟨eA, ΦA, -, -, -, R4A⟩ := s82td_deformation_chart hex A.X.structure'
    have hb := fun j => ft_basis_finite hex A.X.structure' eA ΦA R4A j
    -- normalisation of the differentials
    have hqne : ∀ j, e (qj j) ≠ 0 := by
      intro j h0
      have h00 : qj j = 0 := e.injective (by rw [h0, map_zero])
      exact (hadmj j).2.initial_ne (by simpa [h00] using rfl)
    have hqne0 : e q ≠ 0 := by
      intro h0
      have h00 : q = 0 := e.injective (by rw [h0, map_zero])
      exact hadm.2.initial_ne (by simpa [h00] using rfl)
    have hc : ∀ j, 0 < ‖e (qj j)‖⁻¹ := fun j => inv_pos.2 (norm_pos_iff.2 (hqne j))
    have hc0 : 0 < ‖e q‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hqne0)
    set qn : ℕ → S₀ → ℂ → ℂ := fun j => ((‖e (qj j)‖⁻¹ : ℝ) : ℂ) • (qj j).1 with hqn
    set qn' : ∀ j, (Aj j).X.carrier → ℂ → ℂ := fun j => ((‖e (qj j)‖⁻¹ : ℝ) : ℂ) • qj' j with hqn'
    have hTn : ∀ j, IsTeichmullerMap (fj j) (qn j) (qn' j) (kj j) :=
      fun j => s29_e12_teichMap_smul (hadmj j).2 (hc j)
    have hf0 := s29_e12_teichMap_smul hadm.2 hc0
    have hqnj : ∀ j, qn j = ((‖e (qj j)‖⁻¹ : ℝ) • qj j : admissibleQDInterior F₀).1 := by
      intro j; funext x z; simp [hqn, Complex.real_smul]
    have hcoord : ∀ j, vs j ≠ 0 → e ((‖e (qj j)‖⁻¹ : ℝ) • qj j) = ‖vs j‖⁻¹ • vs j := by
      intro j hz
      obtain ⟨-, hk, hvd⟩ := hprop j hz
      have hkpos : kj j ≠ 0 := by rw [← hk]; exact norm_ne_zero_iff.2 hz
      have hn : ‖e (qj j)‖ ≠ 0 := (norm_pos_iff.2 (hqne j)).ne'
      have h1 : ‖vs j‖⁻¹ • vs j = ‖e (qj j)‖⁻¹ • e (qj j) := by
        calc ‖vs j‖⁻¹ • vs j = (kj j)⁻¹ • ((kj j / ‖e (qj j)‖) • e (qj j)) := by
              rw [hk]; exact congrArg (fun w => (kj j)⁻¹ • w) hvd
          _ = ‖e (qj j)‖⁻¹ • e (qj j) := by
              rw [smul_smul]; congr 1; field_simp
      rw [map_smul, h1]
    have hcoord0 : e ((‖e q‖⁻¹ : ℝ) • q) = ‖v‖⁻¹ • v := by
      have hkpos : k ≠ 0 := hk0.ne'
      have hn : ‖e q‖ ≠ 0 := (norm_pos_iff.2 hqne0).ne'
      have h1 : ‖v‖⁻¹ • v = ‖e q‖⁻¹ • e q := by
        calc ‖v‖⁻¹ • v = k⁻¹ • ((k / ‖e q‖) • e q) := by
              rw [hkn]; exact congrArg (fun w => k⁻¹ • w) hdir
          _ = ‖e q‖⁻¹ • e q := by
              rw [smul_smul]; congr 1; field_simp
      rw [map_smul, h1]
    have hnormconv : Tendsto (fun j => ‖vs j‖⁻¹ • vs j) atTop (𝓝 (‖v‖⁻¹ • v)) :=
      (hlim.norm.inv₀ (norm_ne_zero_iff.2 hv0)).smul hlim
    have hqconv : ∀ x z, Tendsto (fun j => qn j x z) atTop (𝓝 (((‖e q‖⁻¹ : ℝ) : ℂ) • q.1 x z)) := by
      intro x z
      have hq0 : ((‖e q‖⁻¹ : ℝ) : ℂ) • q.1 x z = ((‖e q‖⁻¹ : ℝ) • q : admissibleQDInterior F₀).1 x z := by
        simp [Complex.real_smul]
      rw [hq0]
      rw [ft_eval (admissibleQDInterior F₀) e ((‖e q‖⁻¹ : ℝ) • q) x z, hcoord0]
      have hsum : Tendsto (fun j => ∑ i : Fin (Module.finrank ℝ (admissibleQDInterior F₀)), (((‖vs j‖⁻¹ • vs j) i : ℝ) : ℂ) *
          (e.symm (EuclideanSpace.single i (1 : ℝ))).1 x z) atTop
          (𝓝 (∑ i : Fin (Module.finrank ℝ (admissibleQDInterior F₀)), (((‖v‖⁻¹ • v) i : ℝ) : ℂ) * (e.symm (EuclideanSpace.single i (1 : ℝ))).1 x z)) := by
        refine tendsto_finset_sum _ fun i _ => ?_
        have h1 : Tendsto (fun j => (‖vs j‖⁻¹ • vs j) i) atTop (𝓝 ((‖v‖⁻¹ • v) i)) :=
          ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))) →L[ℝ] ℝ).continuous.tendsto _).comp hnormconv
        exact ((Complex.continuous_ofReal.tendsto _).comp h1).mul_const _
      refine hsum.congr' ?_
      filter_upwards [hev] with j hj
      rw [hqnj j, ft_eval (admissibleQDInterior F₀) e ((‖e (qj j)‖⁻¹ : ℝ) • qj j) x z, hcoord j hj]
    have hkconv : Tendsto kj atTop (𝓝 k) := by
      rw [← hkn]
      refine hlim.norm.congr' ?_
      filter_upwards [hev] with j hj
      exact (hprop j hj).2.1
    have hcore := ft_core hex hAhom hf0 hhomj hTn hqconv hkconv eA (hb)
    -- translate back to `Φ`
    have hcore' : Tendsto (fun j => teichDistanceFT (Φ (vs j)) (Φ v)) atTop (𝓝 0) := by
      refine hcore.congr' ?_
      filter_upwards [hev] with j hj
      rw [hA, (hprop j hj).1, ft_teichDistanceFT_symm]
    exact hcore'

end


section
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]

theorem s82tm_teichDistanceFT_complete_metric {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) :
    (∀ p q : TeichSpaceFiniteType S₀ g n m, teichDistanceFT p q = 0 ↔ p = q) ∧
      (∀ p q : TeichSpaceFiniteType S₀ g n m, teichDistanceFT p q = teichDistanceFT q p) ∧
      (∀ p q r : TeichSpaceFiniteType S₀ g n m, teichDistanceFT p r ≤ teichDistanceFT p q + teichDistanceFT q r) ∧
      (∀ p : ℕ → TeichSpaceFiniteType S₀ g n m, (∀ ε > 0, ∃ N, ∀ i ≥ N, ∀ j ≥ N, teichDistanceFT (p i) (p j) < ε) →
        ∃ q, Tendsto (fun i => teichDistanceFT (p i) q) atTop (𝓝 0)) ∧
      ∃ Φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))) → TeichSpaceFiniteType S₀ g n m,
        InjOn Φ (ball 0 1) ∧
        (∀ p, ∃ v ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1, Φ v = p) ∧
        ∀ (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))))
          (vs : ℕ → EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))),
          v ∈ ball 0 1 → (∀ i, vs i ∈ ball 0 1) →
          (Tendsto vs atTop (𝓝 v) ↔ Tendsto (fun i => teichDistanceFT (Φ (vs i)) (Φ v)) atTop (𝓝 0)) := by
  obtain ⟨e, Φ, R1, R2, R3, R4⟩ := s82td_deformation_chart hex F₀
  have R5 := s82td_param_to_metric hex F₀ e Φ R3 R4
  have R4' : ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1, v ≠ 0 →
      ∃ (A : MarkedFiniteTypeRS S₀ g n m) (f : S₀ ≃ₜ A.X.carrier) (q : S₀ → ℂ → ℂ)
        (q' : A.X.carrier → ℂ → ℂ) (k : ℝ),
        Quot.mk _ A = Φ v ∧
          ContinuousMap.Homotopic (A.marking : C(S₀, A.X.carrier)) (f : C(S₀, A.X.carrier)) ∧
          IsAdmissibleTeichmullerMap F₀ f q q' k ∧ 0 < k ∧ k < 1 ∧ ‖v‖ = k := by
    intro v hv h0
    obtain ⟨A, f, q, q', k, h1, h2, h3, h4, h5, h6, -⟩ := R4 v hv h0
    exact ⟨A, f, q.1, q', k, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨hc, hiff⟩ := ft_complete_of_chart hex F₀ Φ R1 R2 R3 R4' R5
  exact ⟨fun p q => ⟨ft_teichDistanceFT_eq_zero hex p q, fun h => h ▸ ft_teichDistanceFT_self p⟩,
    ft_teichDistanceFT_symm, ft_teichDistanceFT_triangle, hc, Φ, R1, R2, hiff⟩

end

section RelocatedS32

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]
variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀]
variable [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]

/-- §32.3: `d_T` is a complete metric on `T_{g,n,m}`, and the bijection with the unit ball of
`ℝ^{6g-6+2n+3m}` is a homeomorphism (the proof repeats Chapter 7 without essential change).
The homeomorphism is stated as in `thm29_1`: a bijection `Φ` of the open unit ball of
`ℝ^{dim Q̃(S₀)}` (dimension `6g-6+2n+3m` by `teichSpaceFiniteType_ball`) onto `T_{g,n,m}` under which
convergence in the ball and `d_T`-convergence agree. Both topologies are metric, so sequential continuity of
`Φ` and of its inverse is the homeomorphism property.

**Correction** (2026-10-09, user decision). The statement had only the metric axioms and completeness; the
homeomorphism claim of the book (and of this docstring) was missing. It is the last conjunct. -/
theorem teichDistanceFT_complete_metric {g n m : ℕ} (hex : ¬ IsExceptionalType g n m)
    (F₀ : FiniteTypeStructure S₀ g n m) :
    (∀ p q : TeichSpaceFiniteType S₀ g n m, teichDistanceFT p q = 0 ↔ p = q) ∧
      (∀ p q : TeichSpaceFiniteType S₀ g n m, teichDistanceFT p q = teichDistanceFT q p) ∧
      (∀ p q r : TeichSpaceFiniteType S₀ g n m, teichDistanceFT p r ≤ teichDistanceFT p q + teichDistanceFT q r) ∧
      (∀ p : ℕ → TeichSpaceFiniteType S₀ g n m, (∀ ε > 0, ∃ N, ∀ i ≥ N, ∀ j ≥ N, teichDistanceFT (p i) (p j) < ε) →
        ∃ q, Tendsto (fun i => teichDistanceFT (p i) q) atTop (𝓝 0)) ∧
      ∃ Φ : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))) → TeichSpaceFiniteType S₀ g n m,
        InjOn Φ (ball 0 1) ∧
        (∀ p, ∃ v ∈ ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))) 1, Φ v = p) ∧
        ∀ (v : EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀))))
          (vs : ℕ → EuclideanSpace ℝ (Fin (Module.finrank ℝ (admissibleQDInterior F₀)))),
          v ∈ ball 0 1 → (∀ i, vs i ∈ ball 0 1) →
          (Tendsto vs atTop (𝓝 v) ↔ Tendsto (fun i => teichDistanceFT (Φ (vs i)) (Φ v)) atTop (𝓝 0)) := by
  exact s82tm_teichDistanceFT_complete_metric hex F₀

end RelocatedS32

end LiZhongQC
