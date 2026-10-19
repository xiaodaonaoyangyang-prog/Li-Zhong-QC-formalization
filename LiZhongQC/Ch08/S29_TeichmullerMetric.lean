import LiZhongQC.Ch08.S28_Moduli

/-!
# §29 Teichmüller 度量 — The Teichmüller metric

* §29.1 the Teichmüller distance `d_T(τ₁, τ₂) = ½ inf {ln K[f] : f ≃ f₂ ∘ f₁⁻¹}`; it is attained by
  a Teichmüller map; independence of representatives; the metric axioms
                                                          — `teichDistance`, `teichDistance_*`
* the topology of the ball: (29.1) `kₙ → k, ωₙ → ω` ⟺ (29.2) `d_T → 0`; (29.3)–(29.8);
  Theorem 29.1                                             — (see the last bullets)
* §29.2 Theorem 29.2 (completeness)                        — (see the last bullets)
* §29.3 modular transformations are isometries              — `modAction_isometry`
* The two implications (29.1) ⟺ (29.2) of the topology of the ball are stated and proved in
  `LiZhongQC.Lemmas.UniformizedTeichmuller` as well.
* Theorem 29.1 and Theorem 29.2 (completeness) are stated and proved in
  `LiZhongQC.Lemmas.UniformizedTeichmuller` as well.
* The existence of the extremal map realizing `d_T` and the implication `d_T(τ₁, τ₂) = 0 → τ₁ = τ₂` are stated (same
  docstring and statement) and proved in `LiZhongQC.Lemmas.UniformizedTeichmuller`, whose proofs need that module (it is
  downstream of this file).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

variable {S₀ : Type u} [TopologicalSpace S₀] [ChartedSpace ℂ S₀]

/-- **§29.1 (Teichmüller 度量).**  The Teichmüller distance of `τ₁ = [S₁, f₁]` and `τ₂ = [S₂, f₂]`:
`d_T(τ₁, τ₂) = ½ inf {ln K[f] : f : S₁ → S₂ quasiconformal, f ≃ f₂ ∘ f₁⁻¹}` (the factor `½` is
inessential and omitted in many texts).

Written as the `sInf` of a set of reals.  The nested form `⨅ m₁ m₂ g (_ : …), …` is identically `0` in `ℝ`:
for a triple outside the classes the innermost infimum is over an empty proposition, `sInf ∅ = 0`, and all values
are `≥ 0` (corrected 2026-09-25, as for `UniversalTeichmuller.dist`). -/
def teichDistance (p q : TeichSpace S₀) : ℝ :=
  sInf {d | ∃ (m₁ : MarkedRS S₀) (m₂ : MarkedRS S₀) (g : m₁.X.carrier ≃ₜ m₂.X.carrier),
    Quot.mk _ m₁ = p ∧ Quot.mk _ m₂ = q ∧ IsQCRS g ∧
      ContinuousMap.Homotopic ((m₁.marking.trans g : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier))
        (m₂.marking : C(S₀, m₂.X.carrier)) ∧
    d = (1 / 2) * Real.log (maxDilatationRS g).toReal}

variable [T2Space S₀] [ConnectedSpace S₀] [IsManifold 𝓘(ℂ) ω S₀] [CompactSpace S₀]

/-- The set whose `sInf` is `teichDistance p q` (literally the body of the definition): the values `½ ln K[g]`
over the q.c. maps `g` between representatives of `p` and `q` compatible with the markings. -/
def s29_m_teichSet {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (p q : TeichSpace Z) : Set ℝ :=
  {d | ∃ (m₁ : MarkedRS Z) (m₂ : MarkedRS Z) (g : m₁.X.carrier ≃ₜ m₂.X.carrier),
    Quot.mk _ m₁ = p ∧ Quot.mk _ m₂ = q ∧ IsQCRS g ∧
      ContinuousMap.Homotopic ((m₁.marking.trans g : Z ≃ₜ m₂.X.carrier) : C(Z, m₂.X.carrier))
        (m₂.marking : C(Z, m₂.X.carrier)) ∧
    d = (1 / 2) * Real.log (maxDilatationRS g).toReal}

/-- Every element of `s29_m_teichSet p q` is non-negative (`1 ≤ K` for q.c. maps). -/
theorem s29_m_teichSet_nonneg {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (p q : TeichSpace Z) :
    ∀ d ∈ s29_m_teichSet p q, 0 ≤ d := by
  rintro d ⟨m₁, m₂, g, -, -, hg, -, rfl⟩
  exact s29_m_half_log_nonneg hg

/-- `s29_m_teichSet p q` is bounded below (by `0`). -/
theorem s29_m_teichSet_bddBelow {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (p q : TeichSpace Z) :
    BddBelow (s29_m_teichSet p q) :=
  ⟨0, s29_m_teichSet_nonneg p q⟩

/-- Two sets of reals, bounded below, each of whose elements dominates an element of the other, have the same
`sInf` (also when they are empty). -/
theorem s29_m_sInf_eq {s t : Set ℝ} (hs : BddBelow s) (ht : BddBelow t) (h1 : ∀ a ∈ s, ∃ b ∈ t, b ≤ a)
    (h2 : ∀ b ∈ t, ∃ a ∈ s, a ≤ b) : sInf s = sInf t := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · have : t = ∅ := eq_empty_of_forall_notMem fun b hb => by
      obtain ⟨a, ha, -⟩ := h2 b hb
      exact ha
    rw [this]
  · have htne : t.Nonempty := by
      obtain ⟨a, ha⟩ := hsne
      obtain ⟨b, hb, -⟩ := h1 a ha
      exact ⟨b, hb⟩
    apply le_antisymm
    · exact le_csInf htne fun b hb => by
        obtain ⟨a, ha, hab⟩ := h2 b hb
        exact (csInf_le hs ha).trans hab
    · exact le_csInf hsne fun a ha => by
        obtain ⟨b, hb, hba⟩ := h1 a ha
        exact (csInf_le ht hb).trans hba

/-- Equality of two classes in `T(Z)` is the equivalence `MarkedRS.Equiv` of their representatives. -/
theorem s29_m_equiv_of_eq {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] {m₁ m₂ : MarkedRS Z}
    (h : (Quot.mk _ m₁ : TeichSpace Z) = Quot.mk _ m₂) : m₁.Equiv m₂ :=
  (Equivalence.eqvGen_iff markedRS_equiv_equivalence).1 (Quot.eqvGen_exact h)

/-- **Transport.**  A q.c. `g : m₁ → m₂` compatible with the markings and conformal equivalences `m₁ ~ n₁`,
`m₂ ~ n₂` give a q.c. `g' : n₁ → n₂` compatible with the markings, with `K[g'] ≤ K[g]`. -/
theorem s29_m_transport {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] {m₁ m₂ n₁ n₂ : MarkedRS Z}
    (h₁ : m₁.Equiv n₁) (h₂ : m₂.Equiv n₂) {g : m₁.X.carrier ≃ₜ m₂.X.carrier} (hg : IsQCRS g)
    (hhom : ContinuousMap.Homotopic ((m₁.marking.trans g : Z ≃ₜ m₂.X.carrier) : C(Z, m₂.X.carrier))
        (m₂.marking : C(Z, m₂.X.carrier))) :
    ∃ g' : n₁.X.carrier ≃ₜ n₂.X.carrier, IsQCRS g' ∧ maxDilatationRS g' ≤ maxDilatationRS g ∧
      ContinuousMap.Homotopic ((n₁.marking.trans g' : Z ≃ₜ n₂.X.carrier) : C(Z, n₂.X.carrier))
        (n₂.marking : C(Z, n₂.X.carrier)) := by
  obtain ⟨c₁, hc₁, hh₁⟩ := h₁
  obtain ⟨c₂, hc₂, hh₂⟩ := h₂
  obtain ⟨hqc, hle⟩ := s29_m_maxDil_conj_biholo hg hc₁.homeomorph_symm hc₂
  refine ⟨c₁.symm.trans (g.trans c₂), hqc, hle, ?_⟩
  rw [coe_homeomorph_trans] at hhom hh₁ hh₂
  rw [coe_homeomorph_trans, coe_homeomorph_trans, coe_homeomorph_trans]
  -- `c₁⁻¹ ∘ n₁ ≃ c₁⁻¹ ∘ c₁ ∘ m₁ = m₁`
  have hcancel : (c₁.symm : C(n₁.X.carrier, m₁.X.carrier)).comp
      ((c₁ : C(m₁.X.carrier, n₁.X.carrier)).comp (m₁.marking : C(Z, m₁.X.carrier))) =
      (m₁.marking : C(Z, m₁.X.carrier)) := by
    ext x
    exact c₁.symm_apply_apply _
  have e1 : ContinuousMap.Homotopic ((c₁.symm : C(n₁.X.carrier, m₁.X.carrier)).comp
      (n₁.marking : C(Z, n₁.X.carrier))) (m₁.marking : C(Z, m₁.X.carrier)) := by
    have := (ContinuousMap.Homotopic.refl (c₁.symm : C(n₁.X.carrier, m₁.X.carrier))).comp hh₁.symm
    rwa [hcancel] at this
  -- `c₂ ∘ g ∘ (c₁⁻¹ ∘ n₁) ≃ c₂ ∘ g ∘ m₁ ≃ c₂ ∘ m₂ ≃ n₂`
  have e2 := (ContinuousMap.Homotopic.refl ((c₂ : C(m₂.X.carrier, n₂.X.carrier)).comp
    (g : C(m₁.X.carrier, m₂.X.carrier)))).comp e1
  have e3 := (ContinuousMap.Homotopic.refl (c₂ : C(m₂.X.carrier, n₂.X.carrier))).comp hhom
  exact e2.trans (e3.trans hh₂)

/-- `g⁻¹ ∘ f₂ ≃ f₁` from `g ∘ f₁ ≃ f₂`, for the markings `f₁`, `f₂` of `m₁`, `m₂`. -/
theorem s29_m_homotopic_symm {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] {m₁ m₂ : MarkedRS Z}
    {g : m₁.X.carrier ≃ₜ m₂.X.carrier}
    (hhom : ContinuousMap.Homotopic ((m₁.marking.trans g : Z ≃ₜ m₂.X.carrier) : C(Z, m₂.X.carrier))
        (m₂.marking : C(Z, m₂.X.carrier))) :
    ContinuousMap.Homotopic ((m₂.marking.trans g.symm : Z ≃ₜ m₁.X.carrier) : C(Z, m₁.X.carrier))
      (m₁.marking : C(Z, m₁.X.carrier)) := by
  rw [coe_homeomorph_trans] at hhom ⊢
  have hcancel : (g.symm : C(m₂.X.carrier, m₁.X.carrier)).comp
      ((g : C(m₁.X.carrier, m₂.X.carrier)).comp (m₁.marking : C(Z, m₁.X.carrier))) =
      (m₁.marking : C(Z, m₁.X.carrier)) := by
    ext x
    exact g.symm_apply_apply _
  have := (ContinuousMap.Homotopic.refl (g.symm : C(m₂.X.carrier, m₁.X.carrier))).comp hhom.symm
  rwa [hcancel] at this

/-- Any two classes are joined by a q.c. map compatible with the markings (`f₂ ∘ f₁⁻¹`), so
`s29_m_teichSet p q` is nonempty. -/
theorem s29_m_teichSet_nonempty {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (p q : TeichSpace Z) : (s29_m_teichSet p q).Nonempty := by
  obtain ⟨m₁, rfl⟩ := Quot.exists_rep p
  obtain ⟨m₂, rfl⟩ := Quot.exists_rep q
  obtain ⟨K₁, hK₁⟩ := m₁.qc
  obtain ⟨K₂, hK₂⟩ := m₂.qc
  have h := (eq23_4 (s29_m_isKQCRS_symm hK₁) hK₂).1
  refine ⟨_, m₁, m₂, m₁.marking.symm.trans m₂.marking, rfl, rfl, ⟨_, h⟩, ?_, rfl⟩
  have : ((m₁.marking.trans (m₁.marking.symm.trans m₂.marking) : Z ≃ₜ m₂.X.carrier) : C(Z, m₂.X.carrier)) =
      (m₂.marking : C(Z, m₂.X.carrier)) := by
    ext x
    simp
  rw [this]

/-- The Teichmüller distance is non-negative: `0 ≤ d_T(p, q)`. -/
theorem s29_m_teichDistance_nonneg {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (p q : TeichSpace Z) :
    0 ≤ teichDistance p q :=
  Real.sInf_nonneg (s29_m_teichSet_nonneg p q)

/-- `d_T(p, p) = 0`: the identity of a representative is conformal, so `K = 1`. -/
theorem s29_m_teichDistance_self {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (p : TeichSpace Z) :
    teichDistance p p = 0 := by
  refine le_antisymm ?_ (s29_m_teichDistance_nonneg p p)
  obtain ⟨m, rfl⟩ := Quot.exists_rep p
  have h1 : IsKQCRS (Homeomorph.refl m.X.carrier) 1 :=
    (isKQCRS_one_iff _).2
      (isBiholomorphic_id : IsBiholomorphic ((Homeomorph.refl m.X.carrier : _ ≃ₜ _) : m.X.carrier → m.X.carrier))
  have hmem : (1 / 2 : ℝ) * Real.log (maxDilatationRS (Homeomorph.refl m.X.carrier : _ → _)).toReal ∈
      s29_m_teichSet (Quot.mk _ m) (Quot.mk _ m) :=
    ⟨m, m, Homeomorph.refl _, rfl, rfl, ⟨1, h1⟩, ContinuousMap.Homotopic.refl _, rfl⟩
  have hK : maxDilatationRS (Homeomorph.refl m.X.carrier : _ → _) = 1 :=
    le_antisymm (by simpa using maxDilatationRS_le h1) (s29_m_one_le_maxDilatationRS ⟨1, h1⟩)
  refine (csInf_le (s29_m_teichSet_bddBelow _ _) hmem).trans (le_of_eq ?_)
  rw [hK]
  simp

/-- The Teichmüller distance is symmetric, `d_T(p, q) = d_T(q, p)`: the inverse of a q.c. map `g` has
`K[g⁻¹] ≤ K[g]`. -/
theorem s29_m_teichDistance_symm {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] (p q : TeichSpace Z) :
    teichDistance p q = teichDistance q p := by
  have key : ∀ p q : TeichSpace Z, ∀ a ∈ s29_m_teichSet p q, ∃ b ∈ s29_m_teichSet q p, b ≤ a := by
    intro p q a ⟨m₁, m₂, g, hm₁, hm₂, hg, hhom, ha⟩
    obtain ⟨hgs, hle⟩ := s29_m_maxDil_symm_le hg
    exact ⟨_, ⟨m₂, m₁, g.symm, hm₂, hm₁, hgs, s29_m_homotopic_symm hhom, rfl⟩,
      ha ▸ s29_m_half_log_mono hgs hg hle⟩
  exact s29_m_sInf_eq (s29_m_teichSet_bddBelow _ _) (s29_m_teichSet_bddBelow _ _) (key p q) (key q p)

/-- The triangle inequality in the form `d_T(p, q) ≤ d_T(p, r) + d_T(q, r)`, from
`K[g₂⁻¹ ∘ g₁] ≤ K[g₂] K[g₁]` ((23.4)). -/
theorem s29_m_teichDistance_triangle {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (p q r : TeichSpace Z) : teichDistance p q ≤ teichDistance p r + teichDistance q r := by
  -- every `a ∈ S(p,r)`, `b ∈ S(q,r)` bound an element of `S(p,q)`
  have key : ∀ a ∈ s29_m_teichSet p r, ∀ b ∈ s29_m_teichSet q r, ∃ c ∈ s29_m_teichSet p q, c ≤ a + b := by
    rintro a ⟨m₁, m₃, g₁, hm₁, hm₃, hg₁, hhom₁, rfl⟩ b ⟨m₂, m₃', g₂, hm₂, hm₃', hg₂, hhom₂, rfl⟩
    obtain ⟨g₂', hg₂', hle₂, hhom₂'⟩ := s29_m_transport (markedRS_equiv_equivalence.refl m₂)
      (s29_m_equiv_of_eq (hm₃'.trans hm₃.symm)) hg₂ hhom₂
    obtain ⟨hg₂s, hle₂s⟩ := s29_m_maxDil_symm_le hg₂'
    have hK₁ := s29_m_isKQCRS_maxDil hg₁
    have hK₂ := s29_m_isKQCRS_maxDil hg₂s
    obtain ⟨hc, hcle⟩ := eq23_4 hK₁ hK₂
    refine ⟨_, ⟨m₁, m₂, g₁.trans g₂'.symm, hm₁, hm₂, ⟨_, hc⟩, ?_, rfl⟩, ?_⟩
    · -- `g₂'⁻¹ ∘ g₁ ∘ m₁ ≃ g₂'⁻¹ ∘ m₃ ≃ m₂`
      have e1 := s29_m_homotopic_symm hhom₂'
      rw [coe_homeomorph_trans] at hhom₁ e1
      rw [coe_homeomorph_trans, coe_homeomorph_trans]
      have e2 := (ContinuousMap.Homotopic.refl (g₂'.symm : C(m₃.X.carrier, m₂.X.carrier))).comp hhom₁
      exact e2.trans e1
    · -- `K[g₂'⁻¹ ∘ g₁] ≤ K[g₂] K[g₁]`
      have hKle : maxDilatationRS (g₁.trans g₂'.symm) ≤ maxDilatationRS g₂ * maxDilatationRS g₁ :=
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
  obtain ⟨a₀, ha₀⟩ := s29_m_teichSet_nonempty p r
  obtain ⟨b₀, hb₀⟩ := s29_m_teichSet_nonempty q r
  show sInf (s29_m_teichSet p q) ≤ sInf (s29_m_teichSet p r) + sInf (s29_m_teichSet q r)
  have hA : sInf (s29_m_teichSet p q) - sInf (s29_m_teichSet q r) ≤ sInf (s29_m_teichSet p r) := by
    refine le_csInf ⟨a₀, ha₀⟩ fun a ha => ?_
    have : sInf (s29_m_teichSet p q) - a ≤ sInf (s29_m_teichSet q r) := by
      refine le_csInf ⟨b₀, hb₀⟩ fun b hb => ?_
      obtain ⟨c, hc, hcab⟩ := key a ha b hb
      have := csInf_le (s29_m_teichSet_bddBelow p q) hc
      linarith
    linarith
  linarith

/-- §29.1: `d_T` satisfies the axioms of a metric: it is non-negative, `d_T(τ₁, τ₂) = 0` iff
`τ₁ = τ₂` (the Teichmüller map has `K = 1`, i.e. is conformal), symmetric, and satisfies the
triangle inequality (from `K[g₁⁻¹ ∘ g₂] ≤ K[g₁] K[g₂]`).

**Split (2026-09-26).**  The conjunct `d_T(τ₁, τ₂) = 0 → τ₁ = τ₂`, which needs the existence of extremal
maps, is stated separately as `teichDistance_eq_of_eq_zero`; the other four conjuncts are here. -/
theorem teichDistance_metric {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) :
    (∀ p q : TeichSpace S₀, 0 ≤ teichDistance p q) ∧
      (∀ p : TeichSpace S₀, teichDistance p p = 0) ∧
      (∀ p q : TeichSpace S₀, teichDistance p q = teichDistance q p) ∧
      ∀ p q r : TeichSpace S₀, teichDistance p q ≤ teichDistance p r + teichDistance q r := by
  have _ := hg
  have _ := hS
  have _ : T2Space S₀ := inferInstance
  have _ : ConnectedSpace S₀ := inferInstance
  have _ : CompactSpace S₀ := inferInstance
  exact ⟨s29_m_teichDistance_nonneg, s29_m_teichDistance_self, s29_m_teichDistance_symm,
    s29_m_teichDistance_triangle⟩

/-- §29.1: along a Teichmüller deformation `[S_{q,k}, f]`, `d_T([S₀, id], [S_{q,k}, f]) = ½ ln((1+k)/(1-k))`. -/
theorem teichDistance_deformation {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (hid : IsQCRS (Homeomorph.refl S₀))
    {q : S₀ → ℂ → ℂ} {k : ℝ} {p : TeichSpace S₀} (h : IsDeformationPoint q k p) :
    teichDistance (TeichSpace.basePoint hid) p = (1 / 2) * Real.log ((1 + k) / (1 - k)) := by
  classical
  obtain ⟨X, e, hqc, q', hT, hp⟩ := h
  have hX : HasGenus X.carrier g := hasGenus_of_homeomorph hS e
  have he : IsTeichmullerMap e q q' k :=
    teichDeformation_isTeichmullerMap hT
  -- Fuchsian uniformization of this deformation's `X` (genus transported along `e`).
  obtain ⟨ΓX, pX, _hFuchsianX, _hFreeX, hpX⟩ :=
    s22hg_exists_fuchsian_uniformization (S := X.carrier) hg hX
  have hK : 1 ≤ (1 + k) / (1 - k) :=
    s26u_one_le_K hT.k_nonneg hT.k_lt_one
  have hK0 : 0 ≤ (1 + k) / (1 - k) := zero_le_one.trans hK
  have hmax : maxDilatationRS e = ENNReal.ofReal ((1 + k) / (1 - k)) :=
    (teichmullerMap_beltrami he).2
  have hlog : (1 / 2 : ℝ) * Real.log (maxDilatationRS e).toReal =
      (1 / 2) * Real.log ((1 + k) / (1 - k)) := by
    rw [hmax, ENNReal.toReal_ofReal hK0]
  let m0 : MarkedRS S₀ := ⟨⟨S₀⟩, Homeomorph.refl S₀, hid⟩
  let mD : MarkedRS S₀ := ⟨X, e, hqc⟩
  have hp0 : (Quot.mk _ m0 : TeichSpace S₀) =
      TeichSpace.basePoint hid := rfl
  have hpd : p = (Quot.mk _ mD : TeichSpace S₀) := hp
  have hmark : ContinuousMap.Homotopic
      (((Homeomorph.refl S₀).trans e : S₀ ≃ₜ X.carrier) : C(S₀, X.carrier))
      (e : C(S₀, X.carrier)) := by
    have hident :
        (((Homeomorph.refl S₀).trans e : S₀ ≃ₜ X.carrier) : C(S₀, X.carrier)) =
          (e : C(S₀, X.carrier)) := by
      ext x
      rfl
    rw [hident]
  have hmem : (1 / 2 : ℝ) * Real.log ((1 + k) / (1 - k)) ∈
      s29_m_teichSet (TeichSpace.basePoint hid) p := by
    exact ⟨m0, mD, e, hp0, hpd.symm, hqc, hmark, hlog.symm⟩
  -- The actual deformation map supplies a member of the infimum set.
  have hupper : teichDistance (TeichSpace.basePoint hid) p ≤
      (1 / 2) * Real.log ((1 + k) / (1 - k)) := by
    change sInf (s29_m_teichSet (TeichSpace.basePoint hid) p) ≤ _
    exact csInf_le (s29_m_teichSet_bddBelow _ _) hmem
  refine le_antisymm hupper ?_
  change (1 / 2 : ℝ) * Real.log ((1 + k) / (1 - k)) ≤
    sInf (s29_m_teichSet (TeichSpace.basePoint hid) p)
  refine le_csInf ⟨_, hmem⟩ ?_
  intro a ha
  obtain ⟨m₁, m₂, G, hm₁, hm₂, hG, hhomG, haeq⟩ := ha
  have h₁ : m₁.Equiv m0 :=
    s29_m_equiv_of_eq (hm₁.trans hp0.symm)
  have h₂ : m₂.Equiv mD :=
    s29_m_equiv_of_eq (hm₂.trans hpd)
  -- Transport each competitor to S₀ and this same X, preserving marking homotopy.
  have htransport :
      ∃ F : S₀ ≃ₜ X.carrier, IsQCRS F ∧ maxDilatationRS F ≤ maxDilatationRS G ∧
        ContinuousMap.Homotopic
          (((Homeomorph.refl S₀).trans F : S₀ ≃ₜ X.carrier) : C(S₀, X.carrier))
          (e : C(S₀, X.carrier)) := by
    exact s29_m_transport h₁ h₂ hG hhomG
  obtain ⟨F, hF, hFG, hhomF⟩ := htransport
  have hhom : ContinuousMap.Homotopic
      (e : C(S₀, X.carrier)) (F : C(S₀, X.carrier)) := by
    have hident :
        (((Homeomorph.refl S₀).trans F : S₀ ≃ₜ X.carrier) : C(S₀, X.carrier)) =
          (F : C(S₀, X.carrier)) := by
      ext x
      rfl
    rw [hident] at hhomF
    exact hhomF.symm
  -- UU needs only the target uniformization, and only its inequality is used.
  have hL2 : quadDiffNorm q' ≤
      surfaceIntegral q' fun x z =>
        ENNReal.ofReal (lambdaStretch q' q' (e.symm.trans F) x z) :=
    utm_lemma26_2_target (S₀ := S₀) (S₁ := X.carrier) hg hX he hF hhom hpX
  have heF : maxDilatationRS e ≤ maxDilatationRS F := by
    rw [hmax]
    exact utm_thm26_2_ineq (S₀ := S₀) (S₁ := X.carrier) hg hS hX he hF hL2
  calc
    (1 / 2 : ℝ) * Real.log ((1 + k) / (1 - k)) =
        (1 / 2) * Real.log (maxDilatationRS e).toReal := hlog.symm
    _ ≤ (1 / 2) * Real.log (maxDilatationRS F).toReal :=
      s29_m_half_log_mono hqc hF heF
    _ ≤ (1 / 2) * Real.log (maxDilatationRS G).toReal :=
      s29_m_half_log_mono hF hG hFG
    _ = a := haeq.symm

/-! ### The Teichmüller metric and the topology of the ball -/

/-! ### Helpers for `eq29_3` (`s29_e_`): the dilatation of `fₙ ∘ f⁻¹` where `q_x ≠ 0 ≠ qₙ_x` -/

/-- The quotient `(|a| + |b|)/(|a| - |b|)` equals `(1 + k)/(1 - k) > 0` (`0 ≤ k < 1`) only if `a ≠ 0`: for
`a = 0` it is `-(|b|/|b|) ≤ 0`. -/
theorem s29_e_ne_zero_of_quot {a b : ℂ} {k : ℝ} (hk₀ : 0 ≤ k) (hk : k < 1)
    (h : (‖a‖ + ‖b‖) / (‖a‖ - ‖b‖) = (1 + k) / (1 - k)) : a ≠ 0 := by
  intro ha
  rw [ha, norm_zero, zero_add, zero_sub, div_neg] at h
  have h1 : 0 ≤ ‖b‖ / ‖b‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have h2 : 0 < (1 + k) / (1 - k) := div_pos (by linarith) (by linarith)
  linarith

/-- `|k φ̄/|φ|| ≤ k` at every point (it is `k` where `φ ≠ 0` and `0` where `φ = 0`). -/
theorem s29_e_beltrami_norm_le {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] {k : ℝ} (hk₀ : 0 ≤ k)
    (q : X → ℂ → ℂ) (x : X) (z : ℂ) : ‖teichmullerBeltrami k q x z‖ ≤ k := by
  show ‖(k : ℂ) * conj (q x z) / (‖q x z‖ : ℂ)‖ ≤ k
  by_cases h0 : q x z = 0
  · simp [h0, hk₀]
  refine le_of_eq ?_
  rw [norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hk₀, Real.norm_of_nonneg (norm_nonneg _), mul_div_assoc,
    div_self (norm_ne_zero_iff.2 h0), mul_one]

/-- **The local expression of a Teichmüller map where `q_x ≠ 0`**: `g = φ_{f x} ∘ f ∘ φ_x⁻¹` has `∂g(z) ≠ 0` and
`∂̄g(z) = (k q̄_x/|q_x|)(z) ∂g(z)` (`s26b_pointwise`; `∂g ≠ 0` since the dilatation quotient is `(1 + k)/(1 - k)`). -/
theorem s29_e_local {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace ℂ Y] {f : X ≃ₜ Y} {q : X → ℂ → ℂ} {q' : Y → ℂ → ℂ} {k : ℝ} (hf : IsTeichmullerMap f q q' k)
    (x : X) {z : ℂ} (hz : z ∈ localMapDomain f x) (hq0 : q x z ≠ 0) :
    dz (localMapExpr f x) z ≠ 0 ∧
      dzbar (localMapExpr f x) z = teichmullerBeltrami k q x z * dz (localMapExpr f x) z := by
  obtain ⟨h1, h2⟩ := s26b_pointwise hf x hz hq0
  have ha : dz (localMapExpr f x) z ≠ 0 := s29_e_ne_zero_of_quot hf.k_nonneg hf.k_lt_one h2
  refine ⟨ha, ?_⟩
  rw [← h1, complexDilatation, div_mul_cancel₀ _ ha]

/-- **The same, read in the chart at the image point**: for `z` in the chart at `x` with `q_x(z) ≠ 0`, the map
`localMapExprAt f x z = φ_{f p} ∘ f ∘ φ_x⁻¹` (`p = φ_x⁻¹ z`) has `∂ ≠ 0` and `∂̄ = (k q̄_x/|q_x|) ∂` at `z`.  Near `z`
it is `(φ_{f p} ∘ f ∘ φ_p⁻¹) ∘ τ` with the holomorphic transition `τ = φ_p ∘ φ_x⁻¹` (`s23_wirtinger_comp_right`);
then `s29_e_local` at `(p, τ z)` and the `(-1, 1)` law of `k q̄/|q|` under `q_x = q_p(τ) τ'²`
(`teichmullerBeltrami_transform_aux`). -/
theorem s29_e_localAt {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y] {f : X ≃ₜ Y} {q : X → ℂ → ℂ} {q' : Y → ℂ → ℂ} {k : ℝ}
    (hf : IsTeichmullerMap f q q' k) (x : X) {z : ℂ} (hz : z ∈ (chartAt ℂ x).target) (hq0 : q x z ≠ 0) :
    dz (localMapExprAt f x z) z ≠ 0 ∧
      dzbar (localMapExprAt f x z) z = teichmullerBeltrami k q x z * dz (localMapExprAt f x z) z := by
  set p := (chartAt ℂ x).symm z with hp
  have hzp : (chartAt ℂ x).symm z ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  have hus : (chartAt ℂ p).symm (chartTransition p x z) = p := (chartAt ℂ p).left_inv hzp
  have huD : chartTransition p x z ∈ localMapDomain f p := by
    refine ⟨(chartAt ℂ p).map_source hzp, ?_⟩
    show f ((chartAt ℂ p).symm (chartTransition p x z)) ∈ (chartAt ℂ (f p)).source
    rw [hus]
    exact mem_chart_source ℂ (f p)
  have hlaw : q x z = q p (chartTransition p x z) * deriv (chartTransition p x) z ^ 2 :=
    s26u_law hf.initial x p hz hzp
  have hqu : q p (chartTransition p x z) ≠ 0 := fun h0 => hq0 (by rw [hlaw, h0, zero_mul])
  obtain ⟨hd1, hd2⟩ := s29_e_local hf p huD hqu
  obtain ⟨hm1, hm2, -⟩ := s23_transition_mem hz hzp
  obtain ⟨hTd, hT'⟩ := s23_transition p x hz hzp
  obtain ⟨hw1, hw2⟩ := s23_wirtinger_comp_right (g := localMapExpr f p) hTd (s23_transition x p hm1 hm2).1
    (s23_transition_inv p x hz hzp) (s23_transition_inv x p hm1 hm2)
  have hev : localMapExprAt f x z =ᶠ[𝓝 z] localMapExpr f p ∘ chartTransition p x := by
    filter_upwards [((chartAt ℂ x).isOpen_inter_preimage_symm (chartAt ℂ p).open_source).mem_nhds ⟨hz, hzp⟩]
      with w hw
    simp only [localMapExprAt, localMapExpr, Function.comp_apply, chartTransition]
    rw [(chartAt ℂ p).left_inv hw.2]
  have e1 : dz (localMapExprAt f x z) z = dz (localMapExpr f p ∘ chartTransition p x) z := by
    simp only [dz, hev.fderiv_eq (𝕜 := ℝ)]
  have e2 : dzbar (localMapExprAt f x z) z = dzbar (localMapExpr f p ∘ chartTransition p x) z := by
    simp only [dzbar, hev.fderiv_eq (𝕜 := ℝ)]
  have htb : teichmullerBeltrami k q x z = teichmullerBeltrami k q p (chartTransition p x z) *
      (deriv (chartTransition p x) z)⁻¹ * conj (deriv (chartTransition p x) z) := by
    simp only [teichmullerBeltrami]
    rw [hlaw, teichmullerBeltrami_transform_aux, zpow_neg_one, zpow_one]
  rw [e1, e2, hw1, hw2]
  refine ⟨mul_ne_zero hd1 hT', ?_⟩
  rw [hd2, htb]
  field_simp

/-- **The algebra of (29.3)**: if `a₂ = a a₁ + b b̄₁` and `b₂ = a b₁ + b ā₁` (the chain rule (6.2) for `G ∘ L = F`,
with `(a, b)`, `(a₁, b₁)`, `(a₂, b₂)` the Wirtinger derivatives of `G`, `L`, `F`), `b₁ = μ₁ a₁` with `a₁ ≠ 0`,
`b₂ = μ₂ a₂`, `|μ₁| ≤ k < 1` and `|μ₂| ≤ kₙ < 1`, then `|b/a| ≤ |μ₂ - μ₁|/(1 - kₙ k)`: indeed
`a a₁ (μ₂ - μ₁) = b ā₁ (1 - μ₂ μ̄₁)` and `|1 - μ₂ μ̄₁| ≥ 1 - kₙ k > 0` (for `a = 0`, `b/a = 0`). -/
theorem s29_e_algebra {a b a₁ b₁ a₂ b₂ μ₁ μ₂ : ℂ} {k kn : ℝ} (hk : k < 1) (hkn₀ : 0 ≤ kn) (hkn : kn < 1)
    (hμ₁ : ‖μ₁‖ ≤ k) (hμ₂ : ‖μ₂‖ ≤ kn) (ha₁ : a₁ ≠ 0) (hb₁ : b₁ = μ₁ * a₁) (hb₂ : b₂ = μ₂ * a₂)
    (h₂ : a₂ = a * a₁ + b * conj b₁) (h₃ : b₂ = a * b₁ + b * conj a₁) :
    ‖b / a‖ ≤ ‖μ₂ - μ₁‖ / (1 - kn * k) := by
  have hk₀ : 0 ≤ k := (norm_nonneg _).trans hμ₁
  have hkk : kn * k ≤ kn := mul_le_of_le_one_right hkn₀ hk.le
  have hden : 0 < 1 - kn * k := by linarith
  by_cases ha : a = 0
  · rw [ha, div_zero, norm_zero]
    exact div_nonneg (norm_nonneg _) hden.le
  have key : a * a₁ * (μ₂ - μ₁) = b * conj a₁ * (1 - μ₂ * conj μ₁) := by
    rw [hb₂, h₂, hb₁, map_mul] at h₃
    linear_combination h₃
  have hn := congrArg norm key
  simp only [norm_mul, Complex.norm_conj] at hn
  have hn' : ‖a‖ * ‖μ₂ - μ₁‖ = ‖b‖ * ‖1 - μ₂ * conj μ₁‖ := by
    refine mul_right_cancel₀ (norm_ne_zero_iff.2 ha₁) ?_
    linear_combination hn
  have hlow : 1 - kn * k ≤ ‖1 - μ₂ * conj μ₁‖ := by
    have h1 : ‖μ₂ * conj μ₁‖ ≤ kn * k := by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul hμ₂ hμ₁ (norm_nonneg _) hkn₀
    have h2 := norm_sub_norm_le (1 : ℂ) (μ₂ * conj μ₁)
    rw [norm_one] at h2
    linarith
  rw [norm_div, div_le_div_iff₀ (norm_pos_iff.2 ha) hden]
  calc ‖b‖ * (1 - kn * k) ≤ ‖b‖ * ‖1 - μ₂ * conj μ₁‖ := mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
    _ = ‖μ₂ - μ₁‖ * ‖a‖ := by rw [← hn']; ring

/-- **(29.3) at one point.**  At `z ∈ φ_x(U_x ∩ f⁻¹ U_{f x})` with `q_x(z) ≠ 0 ≠ qₙ_x(z)`, put
`L = φ_{f x} ∘ f ∘ φ_x⁻¹`, `F = localMapExprAt fₙ x z` and `G = localMapExprAt (fₙ ∘ f⁻¹) (f x) (L z)`.  Then
`G ∘ L = F` near `z`; if `G` is differentiable at `L z`, the chain rule (6.2) with `∂̄L = μ ∂L`, `∂L ≠ 0`
(`s29_e_local`) and `∂̄F = μₙ ∂F` (`s29_e_localAt`) gives `|μ_G(L z)| ≤ |μₙ - μ|/(1 - kₙ k)` (`s29_e_algebra`).
Otherwise `μ_G(L z) = 0` (in fact `G` is real-smooth near `L z`, but the bound needs no differentiability). -/
theorem s29_e_pointwise {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {Sn : Type u} [TopologicalSpace Sn] [ChartedSpace ℂ Sn]
    {f : X ≃ₜ S} {fn : X ≃ₜ Sn} {q qn : X → ℂ → ℂ} {q' : S → ℂ → ℂ} {qn' : Sn → ℂ → ℂ} {k kn : ℝ}
    (hf : IsTeichmullerMap f q q' k) (hfn : IsTeichmullerMap fn qn qn' kn) (x : X) {z : ℂ}
    (hz : z ∈ localMapDomain f x) (hq0 : q x z ≠ 0) (hqn0 : qn x z ≠ 0) :
    ‖complexDilatation (localMapExprAt (f.symm.trans fn) (f x) (localMapExpr f x z))
        (localMapExpr f x z)‖ ≤
      ‖teichmullerBeltrami kn qn x z - teichmullerBeltrami k q x z‖ / (1 - kn * k) := by
  have hden : 0 < 1 - kn * k := by
    have hkk : kn * k ≤ kn := mul_le_of_le_one_right hfn.k_nonneg hf.k_lt_one.le
    linarith [hfn.k_lt_one]
  obtain ⟨ha₁, hb₁⟩ := s29_e_local hf x hz hq0
  obtain ⟨-, hb₂⟩ := s29_e_localAt hfn x hz.1 hqn0
  set L := localMapExpr f x with hL
  set G := localMapExprAt (f.symm.trans fn) (f x) (L z) with hG
  set F := localMapExprAt fn x z with hF
  by_cases hGd : DifferentiableAt ℝ G (L z)
  swap
  · have h0 : complexDilatation G (L z) = 0 := by
      simp [complexDilatation, dz, dzbar, fderiv_zero_of_not_differentiableAt hGd]
    rw [h0, norm_zero]
    exact div_nonneg (norm_nonneg _) hden.le
  have hLd : DifferentiableAt ℝ L z := by
    by_contra hnd
    exact ha₁ (by simp [dz, fderiv_zero_of_not_differentiableAt hnd])
  have hFGL : F =ᶠ[𝓝 z] G ∘ L := by
    filter_upwards [(s23_localMapDomain_isOpen f.continuous x).mem_nhds hz] with u hu
    have e1 : (chartAt ℂ (f x)).symm (L u) = f ((chartAt ℂ x).symm u) := (chartAt ℂ (f x)).left_inv hu.2
    have e2 : (chartAt ℂ (f x)).symm (L z) = f ((chartAt ℂ x).symm z) := (chartAt ℂ (f x)).left_inv hz.2
    simp only [hF, hG, localMapExprAt, Function.comp_apply, Homeomorph.trans_apply, e1, e2,
      Homeomorph.symm_apply_apply]
  have e1 : dz F z = dz (G ∘ L) z := by
    simp only [dz, hFGL.fderiv_eq (𝕜 := ℝ)]
  have e2 : dzbar F z = dzbar (G ∘ L) z := by
    simp only [dzbar, hFGL.fderiv_eq (𝕜 := ℝ)]
  obtain ⟨h3, h4⟩ := eq6_3 hLd
  have h1 := eq6_2_dz_comp hLd hGd
  have h2 := eq6_2_dzbar_comp hLd hGd
  rw [← h4, ← e1] at h1
  rw [← h3, ← e2] at h2
  rw [complexDilatation]
  exact s29_e_algebra hf.k_lt_one hfn.k_nonneg hfn.k_lt_one (s29_e_beltrami_norm_le hf.k_nonneg q x z)
    (s29_e_beltrami_norm_le hfn.k_nonneg qn x z) ha₁ hb₁ hb₂ h1 h2

/-- (29.3): for Teichmüller maps `fₙ`, `f` with complex dilatations `kₙ ω̄ₙ/|ωₙ|`, `k ω̄/|ω|`, the
complex dilatation `μₙ` of `fₙ ∘ f⁻¹ : S → Sₙ` satisfies
`|μₙ|_p ≤ |kₙ ω̄ₙ/|ωₙ| - k ω̄/|ω||_{f⁻¹(p)} (1 - kₙk)⁻¹`; hence (29.4) `|μₙ| → 0` a.e. when
`kₙ → k`, `ωₙ → ω`.

**Correction.**  The composite `fₙ ∘ f⁻¹` was read in the chart at `fₙ x`, but nothing puts `fₙ(p)` in that
chart, whose values outside its source are junk; the statement was **false** (flat torus, `f = fₙ = id`,
`k = kₙ = 0`, `Sₙ` with an atlas of small balls: left side `1`, right side `0`).  It is now read in the chart
at the image point (`localMapExprAt`, as in the §26 correction of `lambdaStretch`), and `S`, `Sₙ` carry
holomorphic atlases. -/
theorem eq29_3 {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [IsManifold 𝓘(ℂ) ω S] {Sn : Type u}
    [TopologicalSpace Sn] [ChartedSpace ℂ Sn] [IsManifold 𝓘(ℂ) ω Sn] {f : S₀ ≃ₜ S} {fn : S₀ ≃ₜ Sn}
    {q qn : S₀ → ℂ → ℂ} {q' : S → ℂ → ℂ}
    {qn' : Sn → ℂ → ℂ} {k kn : ℝ} (hf : IsTeichmullerMap f q q' k) (hfn : IsTeichmullerMap fn qn qn' kn) :
    ∀ x : S₀, ∀ᵐ z ∂(volume.restrict (localMapDomain f x)),
      ‖complexDilatation (localMapExprAt (f.symm.trans fn) (f x) (localMapExpr f x z))
          (localMapExpr f x z)‖ ≤
        ‖teichmullerBeltrami kn qn x z - teichmullerBeltrami k q x z‖ / (1 - kn * k) := by
  have _ : CompactSpace S₀ := inferInstance
  intro x
  refine (ae_restrict_iff' (s23_localMapDomain_isOpen f.continuous x).measurableSet).2 ?_
  filter_upwards [(s26u_zeros_countable hf.initial hf.initial_ne x).ae_notMem volume,
    (s26u_zeros_countable hfn.initial hfn.initial_ne x).ae_notMem volume] with z hzZ hzZn hz
  exact s29_e_pointwise hf hfn x hz (fun h0 => hzZ ⟨hz.1, h0⟩) (fun h0 => hzZn ⟨hz.1, h0⟩)

/-! ### Helpers for `eq29_7` (`s29_e7_`): Teichmüller's main inequality for `fₙ ∘ f⁻¹`, read through the inverse
Teichmüller map `gₙ⁻¹` (initial differential `-qₙ'`, terminal differential `-Kₙ² qₙ`) and the chain `utm_d_chain` -/

/-- The pointwise estimate at a good point: `D ≥ 0`, `J ≥ 0` and `λ² ≤ D J`, with `D` read at the image-point chart. -/
theorem s29_e7_pointwise {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] {Y : Type u} [TopologicalSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] {f : X ≃ₜ Y} {q : X → ℂ → ℂ} {q' : Y → ℂ → ℂ}
    (x : X) {z : ℂ} (hz : z ∈ localMapDomain f x) (hq0 : q x z ≠ 0)
    (hd : DifferentiableAt ℝ (localMapExpr f x) z)
    (hlt : ‖dzbar (localMapExpr f x) z‖ < ‖dz (localMapExpr f x) z‖) :
    0 ≤ jacobianQD q q' f x z ∧ 0 ≤ dilatationQuotient (localMapExprAt f x z) z ∧
      dilatationQuotient (localMapExprAt f x z) z = dilatationQuotient (localMapExpr f x) z ∧
      lambdaStretch q q' f x z ^ 2 ≤ dilatationQuotient (localMapExprAt f x z) z * jacobianQD q q' f x z := by
  obtain ⟨c, hc0, hdzc, hdzbarc, hdiff⟩ := utm_d_exprAt f.continuous x hz
  set G := localMapExprAt f x z with hG
  set g := localMapExpr f x with hg
  have hc : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have ha : 0 < ‖dz g z‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have hltG : ‖dzbar G z‖ < ‖dz G z‖ := by
    rw [hdzc, hdzbarc, norm_mul, norm_mul]
    exact mul_lt_mul_of_pos_left hlt hc
  have hJG : 0 ≤ jacobian G z := by
    unfold jacobian
    nlinarith [norm_nonneg (dzbar G z)]
  have hJ : 0 ≤ jacobianQD q q' f x z := by
    unfold jacobianQD
    rw [← hG]
    positivity
  have hDeq : dilatationQuotient G z = dilatationQuotient g z := by
    unfold dilatationQuotient complexDilatation
    rw [norm_div, hdzc, hdzbarc, norm_mul, norm_mul, mul_div_mul_left _ _ hc.ne', norm_div]
  have hD0 : 0 ≤ dilatationQuotient G z := by
    unfold dilatationQuotient complexDilatation
    have h1 : ‖dzbar G z / dz G z‖ < 1 := by
      rw [norm_div]
      exact (div_lt_one (lt_of_le_of_lt (norm_nonneg _) hltG)).2 hltG
    exact div_nonneg (by positivity) (by linarith)
  refine ⟨hJ, hD0, hDeq, ?_⟩
  by_cases hq'0 : q' (f ((chartAt ℂ x).symm z)) (localMapExprAt f x z z) = 0
  · have hl : lambdaStretch q q' f x z = 0 := by
      unfold lambdaStretch lambdaStretchPlane
      rw [hq'0]
      simp
    rw [hl]
    simpa using mul_nonneg hD0 hJ
  · obtain ⟨h1, -⟩ := eq26_13 (q := q) (q' := q') (f := f) x (hdiff hd) hltG hq0 hq'0
    exact h1

/-- `2 λ ≤ D + J` at a good point (AM-GM). -/
theorem s29_e7_amgm {l D J : ℝ} (_hl : 0 ≤ l) (hD : 0 ≤ D) (hJ : 0 ≤ J) (h : l ^ 2 ≤ D * J) : 2 * l ≤ D + J := by
  nlinarith [sq_nonneg (D - J), sq_nonneg (2 * l), sq_nonneg (D + J), mul_nonneg hD hJ]

/-- `D(localMapExpr f x)` is measurable (derivatives of a fixed function are measurable). -/
theorem s29_e7_measurable_D (g : ℂ → ℂ) : Measurable (fun z => dilatationQuotient g z) := by
  unfold dilatationQuotient complexDilatation dz dzbar
  have hf : Measurable (fun z => fderiv ℝ g z) := measurable_fderiv ℝ g
  have h1 : Measurable (fun z => fderiv ℝ g z 1) := hf.apply_continuousLinearMap (1 : ℂ)
  have h2 : Measurable (fun z => fderiv ℝ g z Complex.I) := hf.apply_continuousLinearMap Complex.I
  fun_prop

/-- **[stub] The chain on one piece, with the dilatation quotient** (the analogue of `utm_d_chain_piece`, whose
constants `K/K₀`, `K₀` are replaced by the local `D_f` and `1`): for a `K`-q.c. `f` and a measurable `E` inside the
domain of `localMapExpr f x`, `2 ∬_E λ_f |q| ≤ ∬_E D_f |q| + ∬_E J_f |q|`.  At the a.e. good points
(`utm_d_ae_good`) `λ_f² ≤ D_f J_f` (`eq26_13`, `utm_d_pointwise`) and `2 λ ≤ D + J` (AM-GM); `D_f` read in the chart
at the image point agrees a.e. with `D` of `localMapExpr f x` (`utm_d_exprAt`), which is measurable (derivatives of a
fixed function), so the sum of the two integrals splits (`lintegral_add_right'`). -/
theorem s29_e7_piece {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [T2Space X] [ConnectedSpace X]
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] {f : X ≃ₜ Y} {K : ℝ}
    (hf : IsKQCRS f K) {q : X → ℂ → ℂ} {q' : Y → ℂ → ℂ} (hq : IsHolQuadDiff q) (hne : q ≠ 0) (x : X)
    {E : Set ℂ} (hEm : MeasurableSet E) (hE : E ⊆ localMapDomain f x) :
    2 * ∫⁻ z in E, ENNReal.ofReal (lambdaStretch q q' f x z) * ENNReal.ofReal ‖q x z‖ ≤
      (∫⁻ z in E, ENNReal.ofReal (dilatationQuotient (localMapExprAt f x z) z) * ENNReal.ofReal ‖q x z‖) +
        ∫⁻ z in E, ENNReal.ofReal (jacobianQD q q' f x z) * ENNReal.ofReal ‖q x z‖ := by
  have hq' : IsDiffFamily 2 0 q ∧ ∀ x : X, DifferentiableOn ℂ (q x) (chartAt ℂ x).target := hq
  have hmeasQ : AEMeasurable (fun z => ENNReal.ofReal ‖q x z‖) (volume.restrict E) := by
    have hc : ContinuousOn (q x) E := (hq'.2 x).continuousOn.mono fun z hz => (hE hz).1
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hc.aemeasurable hEm).norm
  have hgood := utm_d_ae_good hf hq hne x hEm hE
  have hDm : AEMeasurable (fun z => ENNReal.ofReal (dilatationQuotient (localMapExprAt f x z) z) *
      ENNReal.ofReal ‖q x z‖) (volume.restrict E) := by
    have hae : (fun z => ENNReal.ofReal (dilatationQuotient (localMapExprAt f x z) z) *
        ENNReal.ofReal ‖q x z‖) =ᵐ[volume.restrict E]
        (fun z => ENNReal.ofReal (dilatationQuotient (localMapExpr f x) z) * ENNReal.ofReal ‖q x z‖) := by
      filter_upwards [hgood] with z hz
      obtain ⟨hzE, hq0, hd, hlt, -⟩ := hz
      rw [(s29_e7_pointwise (q' := q') x (hE hzE) hq0 hd hlt).2.2.1]
    refine AEMeasurable.congr ?_ hae.symm
    exact ((ENNReal.measurable_ofReal.comp (s29_e7_measurable_D _)).aemeasurable.mul hmeasQ)
  rw [← lintegral_const_mul' 2 _ (by norm_num), ← lintegral_add_left' hDm]
  refine lintegral_mono_ae ?_
  filter_upwards [hgood] with z hz
  obtain ⟨hzE, hq0, hd, hlt, -⟩ := hz
  obtain ⟨hJ, hD, -, hlJ⟩ := s29_e7_pointwise (q' := q') x (hE hzE) hq0 hd hlt
  have hl := utm_d_lambdaStretch_nonneg q q' f x z
  have hQ := norm_nonneg (q x z)
  have hr := s29_e7_amgm hl hD hJ hlJ
  calc 2 * (ENNReal.ofReal (lambdaStretch q q' f x z) * ENNReal.ofReal ‖q x z‖)
      = ENNReal.ofReal (2 * (lambdaStretch q q' f x z * ‖q x z‖)) := by
        rw [← ENNReal.ofReal_mul hl, two_mul, two_mul,
          ENNReal.ofReal_add (mul_nonneg hl hQ) (mul_nonneg hl hQ)]
    _ ≤ ENNReal.ofReal ((dilatationQuotient (localMapExprAt f x z) z + jacobianQD q q' f x z) * ‖q x z‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc 2 * (lambdaStretch q q' f x z * ‖q x z‖) = (2 * lambdaStretch q q' f x z) * ‖q x z‖ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hr hQ
    _ = ENNReal.ofReal (dilatationQuotient (localMapExprAt f x z) z) * ENNReal.ofReal ‖q x z‖ +
          ENNReal.ofReal (jacobianQD q q' f x z) * ENNReal.ofReal ‖q x z‖ := by
        rw [add_mul, ENNReal.ofReal_add (mul_nonneg hD hQ) (mul_nonneg hJ hQ), ENNReal.ofReal_mul hD,
          ENNReal.ofReal_mul hJ]

/-- `localMapExprAt f p (φ_p p)` is `localMapExpr f p`. -/
theorem s29_e7_exprAt_center {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
    [ChartedSpace ℂ Y] (f : X → Y) (p : X) : localMapExprAt f p (chartAt ℂ p p) = localMapExpr f p := by
  funext w
  simp only [localMapExprAt, localMapExpr]
  rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]

/-- **Chart independence of `D`** read at the image point: for `p = φ_y⁻¹ z`,
`D(localMapExprAt f y z) z = D(localMapExpr f p) (φ_p p)`. -/
theorem s29_e7_D_inv {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y] (f : X → Y) (y : X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ y).target) :
    dilatationQuotient (localMapExprAt f y z) z =
      dilatationQuotient (localMapExpr f ((chartAt ℂ y).symm z)) (chartAt ℂ ((chartAt ℂ y).symm z) ((chartAt ℂ y).symm z)) := by
  set p := (chartAt ℂ y).symm z with hp
  have hzp : (chartAt ℂ y).symm z ∈ (chartAt ℂ p).source := mem_chart_source ℂ p
  obtain ⟨hm1, hm2, -⟩ := s23_transition_mem (x := p) (y := y) hz hzp
  obtain ⟨hTd, hT'⟩ := s23_transition p y hz hzp
  obtain ⟨hw1, hw2⟩ := s23_wirtinger_comp_right (g := localMapExpr f p) hTd
    (s23_transition y p hm1 hm2).1 (s23_transition_inv p y hz hzp) (s23_transition_inv y p hm1 hm2)
  have hev : localMapExprAt f y z =ᶠ[𝓝 z] localMapExpr f p ∘ chartTransition p y := by
    filter_upwards [((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ p).open_source).mem_nhds ⟨hz, hzp⟩]
      with w hw
    simp only [localMapExprAt, localMapExpr, Function.comp_apply, chartTransition]
    rw [(chartAt ℂ p).left_inv hw.2]
  have e1 : dz (localMapExprAt f y z) z = dz (localMapExpr f p ∘ chartTransition p y) z := by
    simp only [dz, hev.fderiv_eq (𝕜 := ℝ)]
  have e2 : dzbar (localMapExprAt f y z) z = dzbar (localMapExpr f p ∘ chartTransition p y) z := by
    simp only [dzbar, hev.fderiv_eq (𝕜 := ℝ)]
  have hτ : chartTransition p y z = chartAt ℂ p p := rfl
  have hT0 : ‖deriv (chartTransition p y) z‖ ≠ 0 := norm_ne_zero_iff.2 hT'
  unfold dilatationQuotient complexDilatation
  rw [e1, e2, hw1, hw2, hτ, norm_div, norm_mul, norm_mul, Complex.norm_conj, mul_div_mul_right _ _ hT0, ← norm_div]

/-- **[stub] Partition independence of the `D`-integral.**  `D_f` read in the chart at the image point is
chart-independent: for `p = φ_x⁻¹ z`, `D(localMapExprAt f x z) z = D(localMapExprAt f p (φ_p p)) (φ_p p)`, because
`localMapExprAt f x z = localMapExprAt f p (φ_p p) ∘ τ` near `z` with the holomorphic transition `τ = φ_p ∘ φ_x⁻¹`
(`s23_wirtinger_comp_right`: `∂(g ∘ τ) = ∂g τ'`, `∂̄(g ∘ τ) = ∂̄g τ̄'`, so the quotient is unchanged; where `g` is not
differentiable both sides are `D = 1`).  Hence `s26v_surfaceIntegral_eq_tsum` applies to the point function
`p ↦ D(localMapExprAt f p (φ_p p)) (φ_p p)`: the surface integral is the partition sum over **any** chart partition. -/
theorem s29_e7_D_partition {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace ℂ Y] (f : X ≃ₜ Y) {q : X → ℂ → ℂ} (hq : IsHolQuadDiff q)
    {x : ℕ → X} {P : ℕ → Set X} (hP : IsChartPartition X x P) :
    surfaceIntegral q (fun y z => ENNReal.ofReal (dilatationQuotient (localMapExprAt f y z) z)) =
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ENNReal.ofReal (dilatationQuotient (localMapExprAt f (x i) z) z) * ENNReal.ofReal ‖q (x i) z‖ := by
  -- the point function `U p = D_f(p)`
  set U : X → ℝ≥0∞ := fun p => ENNReal.ofReal (dilatationQuotient (localMapExpr f p) (chartAt ℂ p p)) with hU
  have hpt : ∀ y : X, ∀ p ∈ (chartAt ℂ y).source,
      ENNReal.ofReal (dilatationQuotient (localMapExprAt f y (chartAt ℂ y p)) (chartAt ℂ y p)) =
        U ((chartAt ℂ y).symm (chartAt ℂ y p)) := by
    intro y p hp
    have hz : chartAt ℂ y p ∈ (chartAt ℂ y).target := (chartAt ℂ y).map_source hp
    rw [s29_e7_D_inv f y hz]
  have h1 : surfaceIntegral q (fun y z => ENNReal.ofReal (dilatationQuotient (localMapExprAt f y z) z)) =
      surfaceIntegral q (fun y z => U ((chartAt ℂ y).symm z)) :=
    s26v_a_surfaceIntegral_congr_off q ∅ (fun x => by simp) (fun y p hp _ => hpt y p hp)
  rw [h1, s26v_surfaceIntegral_eq_tsum hq U hP]
  refine tsum_congr fun i => ?_
  refine setLIntegral_congr_fun (hP.1 i).2 fun z hz => ?_
  obtain ⟨a, ha, rfl⟩ := hz
  rw [hpt (x i) a ((hP.1 i).1 ha)]

/-- The inverse of a homotopic pair is homotopic: `gn ≃ F` gives `gn⁻¹ ≃ F⁻¹`. -/
theorem s29_e7_homotopic_symm {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] {g F : A ≃ₜ B}
    (h : ContinuousMap.Homotopic (g : C(A, B)) (F : C(A, B))) :
    ContinuousMap.Homotopic (g.symm : C(B, A)) (F.symm : C(B, A)) := by
  have h1 := (ContinuousMap.Homotopic.refl (g.symm : C(B, A))).comp h.symm
  have h2 := h1.comp (ContinuousMap.Homotopic.refl (F.symm : C(B, A)))
  have e1 : ((g.symm : C(B, A)).comp (F : C(A, B))).comp (F.symm : C(B, A)) = (g.symm : C(B, A)) := by
    ext y
    simp
  have e2 : ((g.symm : C(B, A)).comp (g : C(A, B))).comp (F.symm : C(B, A)) = (F.symm : C(B, A)) := by
    ext y
    simp
  rw [e1, e2] at h2
  exact h2

/-- (29.6)–(29.7): for the extremal map `gₙ : Sₙ → S` in the class of `f ∘ fₙ⁻¹` with terminal
differential `ω̃ₙ'` normalized by `∬_S dA = 1`, `Kₙ = K[gₙ] ≤ ∬_S D[fₙ ∘ f⁻¹] dA_{ω̃ₙ'}`, where `D`
is the local dilatation quotient; since `D[fₙ ∘ f⁻¹] ≤ K[f] (1+kₙ)/(1-kₙ)` is uniformly bounded and
`→ 1` a.e., `Kₙ → 1` (29.5).

**Correction.**  The integrand read `fₙ ∘ f⁻¹` in the chart at `fₙ(f⁻¹ x)` on the whole piece of a chart
partition, where its values are junk, and `surfaceIntegral` is an infimum over partitions; the statement
was **false** (on any closed surface of genus `g > 1`, `f = fₙ = gₙ = id` and `Sₙ` with an atlas of small
balls give left side `1`, right side `< 1`).  The integrand now reads `D` in the chart at the image point
(`localMapExprAt`); the statement is Teichmüller's main inequality for `fₙ ∘ f⁻¹ ≃ gₙ⁻¹`. -/
theorem eq29_7 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {S Sn : Type u} [TopologicalSpace S]
    [ChartedSpace ℂ S] [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] [CompactSpace S]
    [TopologicalSpace Sn] [ChartedSpace ℂ Sn] [T2Space Sn] [ConnectedSpace Sn] [IsManifold 𝓘(ℂ) ω Sn]
    [CompactSpace Sn] (hS' : HasGenus S g) (hSn : HasGenus Sn g) {f : S₀ ≃ₜ S} {fn : S₀ ≃ₜ Sn}
    (hf : IsQCRS f) (hfn : IsQCRS fn) {gn : Sn ≃ₜ S} {qn : Sn → ℂ → ℂ} {qn' : S → ℂ → ℂ} {kn : ℝ}
    (hgn : IsTeichmullerMap gn qn qn' kn)
    (hhom : ContinuousMap.Homotopic (gn : C(Sn, S)) ((fn.symm.trans f : Sn ≃ₜ S) : C(Sn, S)))
    (hnorm : quadDiffNorm qn' = 1) :
    ENNReal.ofReal ((1 + kn) / (1 - kn)) ≤
      surfaceIntegral qn' fun x z =>
        ENNReal.ofReal (dilatationQuotient (localMapExprAt (f.symm.trans fn) x z) z) := by
  classical
  have _ := hg
  have _ := hS
  have _ := hS'
  have : Nonempty S := ConnectedSpace.toNonempty
  have : Nonempty Sn := ConnectedSpace.toNonempty
  set K : ℝ := (1 + kn) / (1 - kn) with hK
  have hK0 : 0 < K := div_pos (by linarith [hgn.k_nonneg]) (by linarith [hgn.k_lt_one])
  -- `h = fₙ ∘ f⁻¹ : S → Sₙ` is q.c.
  obtain ⟨K₁, hK₁⟩ := hf
  obtain ⟨K₂, hK₂⟩ := hfn
  have hh : IsKQCRS (f.symm.trans fn) (K₁ * K₂) := (eq23_4 (s29_m_isKQCRS_symm hK₁) hK₂).1
  -- the inverse of `gₙ` is a Teichmüller map with initial differential `-qₙ'` and terminal `-Kₙ² qₙ`
  have hG : IsTeichmullerMap gn.symm (-qn') ((((-(K ^ 2) : ℝ)) : ℂ) • qn) kn :=
    utm_x_teichmullerMap_symm hgn
  have hhomG : ContinuousMap.Homotopic (gn.symm : C(S, Sn)) ((f.symm.trans fn : S ≃ₜ Sn) : C(S, Sn)) := by
    have h1 := s29_e7_homotopic_symm hhom
    have e : (fn.symm.trans f).symm = f.symm.trans fn := by
      ext x
      simp
    rwa [e] at h1
  -- Lemma 26.2 on the target `Sₙ` (uniformized by `s22hg`)
  obtain ⟨Γ, p, -, -, hp⟩ := s22hg_exists_fuchsian_uniformization hg hSn
  have hL2 := utm_lemma26_2_target (S₀ := S) (S₁ := Sn) hg hSn hG ⟨_, hh⟩ hhomG hp
  -- a chart partition of `S` subordinate to `h`, and the chain over it
  obtain ⟨p₀⟩ : Nonempty S := inferInstance
  obtain ⟨x, P, hP, hPV, -, -⟩ :=
    utm_d_good_partition (f.symm.trans fn) (f.symm.trans fn).continuous p₀
  obtain ⟨hL, hC, -, -⟩ := utm_d_chain hG hh hL2 hP hPV
  have hq : IsHolQuadDiff (-qn') := hG.initial
  have hne : (-qn') ≠ 0 := hG.initial_ne
  have hpiece := fun i => s29_e7_piece (q' := (((-(K ^ 2) : ℝ)) : ℂ) • qn) hh hq hne (x i) (hP.1 i).2 (utm_d_piece_sub _ (hPV i))
  have hsum : 2 * ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ENNReal.ofReal (lambdaStretch (-qn') ((((-(K ^ 2) : ℝ)) : ℂ) • qn) (f.symm.trans fn) (x i) z) *
          ENNReal.ofReal ‖(-qn') (x i) z‖ ≤
      (∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ENNReal.ofReal (dilatationQuotient (localMapExprAt (f.symm.trans fn) (x i) z) z) *
          ENNReal.ofReal ‖(-qn') (x i) z‖) +
      ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ENNReal.ofReal (jacobianQD (-qn') ((((-(K ^ 2) : ℝ)) : ℂ) • qn) (f.symm.trans fn) (x i) z) *
          ENNReal.ofReal ‖(-qn') (x i) z‖ := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum hpiece
  -- the norm of the terminal differential is `K`
  have hN : quadDiffNorm ((((-(K ^ 2) : ℝ)) : ℂ) • qn) = ENNReal.ofReal K := by
    have h1 : quadDiffNorm qn' = ENNReal.ofReal K * quadDiffNorm qn := s26w_quadDiffNorm_teich hgn
    have h2 : quadDiffNorm ((((-(K ^ 2) : ℝ)) : ℂ) • qn) = ENNReal.ofReal (K ^ 2) * quadDiffNorm qn := by
      have := s26_surfaceIntegral_smul qn (fun _ _ => (1 : ℝ≥0∞)) (((-(K ^ 2) : ℝ)) : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg K)] at this
      exact this
    rw [h2, pow_two, ENNReal.ofReal_mul hK0.le, mul_assoc, ← h1, hnorm, mul_one]
  have hNt : quadDiffNorm ((((-(K ^ 2) : ℝ)) : ℂ) • qn) ≠ ⊤ := by
    rw [hN]
    exact ENNReal.ofReal_ne_top
  have h2 : quadDiffNorm ((((-(K ^ 2) : ℝ)) : ℂ) • qn) + quadDiffNorm ((((-(K ^ 2) : ℝ)) : ℂ) • qn) ≤
      (∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
        ENNReal.ofReal (dilatationQuotient (localMapExprAt (f.symm.trans fn) (x i) z) z) *
          ENNReal.ofReal ‖(-qn') (x i) z‖) +
        quadDiffNorm ((((-(K ^ 2) : ℝ)) : ℂ) • qn) := by
    calc _ = 2 * quadDiffNorm ((((-(K ^ 2) : ℝ)) : ℂ) • qn) := (two_mul _).symm
      _ ≤ 2 * ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i,
          ENNReal.ofReal (lambdaStretch (-qn') ((((-(K ^ 2) : ℝ)) : ℂ) • qn) (f.symm.trans fn) (x i) z) *
            ENNReal.ofReal ‖(-qn') (x i) z‖ := mul_le_mul' le_rfl hL
      _ ≤ _ := hsum
      _ = _ := by rw [hC]
  have h3 := ENNReal.le_of_add_le_add_right hNt h2
  -- the surface integral is the partition sum over this partition (`s29_e7_D_partition`)
  have hneg : surfaceIntegral (-qn') (fun y z =>
      ENNReal.ofReal (dilatationQuotient (localMapExprAt (f.symm.trans fn) y z) z)) =
      surfaceIntegral qn' (fun y z =>
        ENNReal.ofReal (dilatationQuotient (localMapExprAt (f.symm.trans fn) y z) z)) := by
    have : Nonempty S := ⟨p₀⟩
    have := s26_surfaceIntegral_smul qn' (fun y z =>
      ENNReal.ofReal (dilatationQuotient (localMapExprAt (f.symm.trans fn) y z) z)) (-1)
    rwa [neg_one_smul, norm_neg, norm_one, ENNReal.ofReal_one, one_mul] at this
  rw [← hneg, s29_e7_D_partition (f.symm.trans fn) hq hP]
  rw [hN] at h3
  exact h3

/-- (29.8): if `d_T([Sₙ, fₙ], [S, f]) → 0` then the distances to `[S₀, id]` are bounded, so
`kₙ ≤ k₀ < 1` for all `n`. -/
theorem eq29_8 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (hid : IsQCRS (Homeomorph.refl S₀))
    {pn : ℕ → TeichSpace S₀} {p : TeichSpace S₀} (hconv : Tendsto (fun n => teichDistance (pn n) p) atTop (𝓝 0))
    {qn : ℕ → S₀ → ℂ → ℂ} {kn : ℕ → ℝ} (hpn : ∀ n, IsDeformationPoint (qn n) (kn n) (pn n)) :
    ∃ k₀ : ℝ, k₀ < 1 ∧ ∀ n, kn n ≤ k₀ := by
  obtain ⟨B, hB⟩ := hconv.bddAbove_range
  let M : ℝ := teichDistance (TeichSpace.basePoint hid) p + B
  let E : ℝ := Real.exp (2 * M)
  have hE : 0 < E := Real.exp_pos _
  have hE1 : 0 < E + 1 := by linarith
  refine ⟨(E - 1) / (E + 1), ?_, ?_⟩
  · exact (div_lt_iff₀ hE1).2 (by linarith)
  · intro n
    have hBn : teichDistance (pn n) p ≤ B := hB ⟨n, rfl⟩
    have hdist : teichDistance (TeichSpace.basePoint hid) (pn n) ≤ M := by
      calc
        teichDistance (TeichSpace.basePoint hid) (pn n) ≤
            teichDistance (TeichSpace.basePoint hid) p + teichDistance (pn n) p :=
          s29_m_teichDistance_triangle _ _ _
        _ ≤ M := by
          dsimp [M]
          linarith
    have hformula := teichDistance_deformation hg hS hid (hpn n)
    have hparams : 0 ≤ kn n ∧ kn n < 1 := by
      obtain ⟨X, e, hqc, q', hT, hp⟩ := hpn n
      exact ⟨hT.k_nonneg, hT.k_lt_one⟩
    have hden : 0 < 1 - kn n := by linarith [hparams.2]
    have hnum : 0 < 1 + kn n := by linarith [hparams.1]
    have hratio : 0 < (1 + kn n) / (1 - kn n) := div_pos hnum hden
    have hlog : Real.log ((1 + kn n) / (1 - kn n)) ≤ 2 * M := by
      rw [hformula] at hdist
      linarith
    have hquot : (1 + kn n) / (1 - kn n) ≤ E :=
      (Real.log_le_iff_le_exp hratio).1 hlog
    have hmul : 1 + kn n ≤ E * (1 - kn n) :=
      (div_le_iff₀ hden).1 hquot
    apply (le_div_iff₀ hE1).2
    nlinarith

/-! ## §29.2 Completeness -/

/-- A Cauchy sequence for a function `d` with the triangle inequality in the form `d p q ≤ d p r + d q r` is
bounded as seen from any base point `b`: a finite maximum over the first terms, and the tail bound. -/
theorem s29_m_cauchy_bounded_of_triangle {α : Type*} (d : α → α → ℝ)
    (htri : ∀ p q r, d p q ≤ d p r + d q r) (b : α) (p : ℕ → α)
    (hp : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, d (p m) (p n) < ε) : ∃ M : ℝ, ∀ n, d b (p n) ≤ M := by
  obtain ⟨N, hN⟩ := hp 1 one_pos
  refine ⟨(∑ n ∈ Finset.range (N + 1), |d b (p n)|) + |d b (p N)| + 1, fun n => ?_⟩
  have hsum : ∀ n ∈ Finset.range (N + 1), |d b (p n)| ≤ ∑ n ∈ Finset.range (N + 1), |d b (p n)| :=
    fun n hn => Finset.single_le_sum (f := fun n => |d b (p n)|) (fun _ _ => abs_nonneg _) hn
  have hs0 : 0 ≤ ∑ n ∈ Finset.range (N + 1), |d b (p n)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  rcases le_or_gt n N with hn | hn
  · have := hsum n (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
    have := le_abs_self (d b (p n))
    have := abs_nonneg (d b (p N))
    linarith
  · have h1 := htri b (p n) (p N)
    have h2 := hN n hn.le N le_rfl
    have := le_abs_self (d b (p N))
    linarith

/-- §29.2 (the proof of Theorem 29.2): a Cauchy sequence is bounded, `d_T(τ₀, τₙ) ≤ M`, so its
image in the ball lies in a ball of radius `r₀ < 1` and has a convergent subsequence. -/
theorem cauchy_bounded_in_ball {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (hid : IsQCRS (Homeomorph.refl S₀))
    (p : ℕ → TeichSpace S₀) (hp : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, teichDistance (p m) (p n) < ε) :
    ∃ M : ℝ, ∀ n, teichDistance (TeichSpace.basePoint hid) (p n) ≤ M := by
  exact s29_m_cauchy_bounded_of_triangle teichDistance (teichDistance_metric hg hS).2.2.2 _ p hp

/-! ## §29.3 Modular transformations are isometries -/

/-- **§29.3 (模变换的保距性)**: every modular transformation `σ*` is an isometry of the Teichmüller
metric, `d_T(σ*(τ₁), σ*(τ₂)) = d_T(τ₁, τ₂)`; in particular it is a homeomorphism of `T(S₀)`. -/
theorem modAction_isometry {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (h : ModTransform S₀)
    {p p' q q' : TeichSpace S₀} (hp : ModAction h p p') (hq : ModAction h q q') :
    teichDistance p' q' = teichDistance p q := by
  have _ := hg
  have _ := hS
  have _ : T2Space S₀ := inferInstance
  have _ : ConnectedSpace S₀ := inferInstance
  have _ : IsManifold 𝓘(ℂ) ω S₀ := inferInstance
  have _ : CompactSpace S₀ := inferInstance
  obtain ⟨m, hmσ, rfl, rfl⟩ := hp
  obtain ⟨n, hnσ, rfl, rfl⟩ := hq
  set σ : S₀ ≃ₜ S₀ := h.1
  show sInf (s29_m_teichSet _ _) = sInf (s29_m_teichSet _ _)
  refine s29_m_sInf_eq (s29_m_teichSet_bddBelow _ _) (s29_m_teichSet_bddBelow _ _) ?_ ?_
  · -- an element for `(p', q')` gives one for `(p, q)`
    rintro a ⟨m₁, m₂, G, hm₁, hm₂, hG, hhom, rfl⟩
    obtain ⟨G', hG', hle, hhom'⟩ :=
      s29_m_transport (s29_m_equiv_of_eq hm₁) (s29_m_equiv_of_eq hm₂) hG hhom
    refine ⟨_, ⟨m, n, G', rfl, rfl, hG', ?_, rfl⟩, s29_m_half_log_mono hG' hG hle⟩
    -- precompose the homotopy with `σ⁻¹`
    have := hhom'.comp (ContinuousMap.Homotopic.refl (σ.symm : C(S₀, S₀)))
    rw [coe_homeomorph_trans, coe_homeomorph_trans] at this
    simp only [coe_homeomorph_trans] at this
    have hc1 : ((G' : C(m.X.carrier, n.X.carrier)).comp
        ((m.marking : C(S₀, m.X.carrier)).comp (σ : C(S₀, S₀)))).comp (σ.symm : C(S₀, S₀)) =
        (G' : C(m.X.carrier, n.X.carrier)).comp (m.marking : C(S₀, m.X.carrier)) := by
      ext x
      simp
    have hc2 : ((n.marking : C(S₀, n.X.carrier)).comp (σ : C(S₀, S₀))).comp (σ.symm : C(S₀, S₀)) =
        (n.marking : C(S₀, n.X.carrier)) := by
      ext x
      simp
    rw [coe_homeomorph_trans]
    exact (hc1 ▸ hc2 ▸ this)
  · -- an element for `(p, q)` gives one for `(p', q')`
    rintro a ⟨m₁, m₂, G, hm₁, hm₂, hG, hhom, rfl⟩
    obtain ⟨G', hG', hle, hhom'⟩ :=
      s29_m_transport (s29_m_equiv_of_eq hm₁) (s29_m_equiv_of_eq hm₂) hG hhom
    refine ⟨_, ⟨⟨m.X, σ.trans m.marking, hmσ⟩, ⟨n.X, σ.trans n.marking, hnσ⟩, G', rfl, rfl, hG', ?_, rfl⟩,
      s29_m_half_log_mono hG' hG hle⟩
    -- precompose the homotopy with `σ`
    have := hhom'.comp (ContinuousMap.Homotopic.refl (σ : C(S₀, S₀)))
    show ContinuousMap.Homotopic (((σ.trans m.marking).trans G' : S₀ ≃ₜ n.X.carrier) : C(S₀, n.X.carrier))
      ((σ.trans n.marking : S₀ ≃ₜ n.X.carrier) : C(S₀, n.X.carrier))
    rw [coe_homeomorph_trans, coe_homeomorph_trans, coe_homeomorph_trans]
    rw [coe_homeomorph_trans] at this
    exact this

end LiZhongQC
