import LiZhongQC.Ch08.S28_Moduli

/-!
# §29 Teichmüller 度量 — The Teichmüller metric

* §29.1 the Teichmüller distance `d_T(τ₁, τ₂) = ½ inf {ln K[f] : f ≃ f₂ ∘ f₁⁻¹}`; it is attained by
  a Teichmüller map; independence of representatives; the metric axioms
                                                          — `teichDistance`, `teichDistance_*`
* the topology of the ball: (29.1) `kₙ → k, ωₙ → ω` ⟺ (29.2) `d_T → 0`; (29.3)–(29.8);
  Theorem 29.1                                             — `eq29_1_imp_eq29_2`, `eq29_2_imp_eq29_1`,
                                                            `thm29_1`
* §29.2 Theorem 29.2 (completeness)                        — `thm29_2_complete`
* §29.3 modular transformations are isometries              — `modAction_isometry`
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

/-- §29.1: the infimum is attained at a Teichmüller map (or a conformal map): there is a Teichmüller
map `f₀ : S₁ → S₂` with `f₀ ≃ f₂ ∘ f₁⁻¹` and `d_T(τ₁, τ₂) = ½ ln K[f₀]`; the value does not depend on
the representatives `(Sⱼ, fⱼ)`. -/
theorem teichDistance_attained {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (m₁ m₂ : MarkedRS S₀) :
    ∃ f : m₁.X.carrier ≃ₜ m₂.X.carrier, IsExtremalInHomotopyClass f ∧
      (IsBiholomorphic f ∨ ∃ (q : m₁.X.carrier → ℂ → ℂ) (q' : m₂.X.carrier → ℂ → ℂ) (k : ℝ),
        IsTeichmullerMap f q q' k) ∧
      ContinuousMap.Homotopic ((m₁.marking.trans f : S₀ ≃ₜ m₂.X.carrier) : C(S₀, m₂.X.carrier))
        (m₂.marking : C(S₀, m₂.X.carrier)) ∧
      teichDistance (Quot.mk _ m₁) (Quot.mk _ m₂) = (1 / 2) * Real.log (maxDilatationRS f).toReal := by
  sorry

/-- Theorem 10.1 in the plane: a `K`-q.c. map `f` of `D` whose maximal dilatation satisfies `K[f] ≤ K'`, with
`1 ≤ K'`, is `K'`-q.c. -/
theorem s29_m_isKQC_of_maxDilatation_le {f : ℂ → ℂ} {D : Set ℂ} {K K' : ℝ} (hf : IsKQC f D K)
    (hK' : 1 ≤ K') (hle : maxDilatation f D ≤ ENNReal.ofReal K') : IsKQC f D K' := by
  have hD : IsOpen D := hf.1
  have hhom : IsHomeomorphOnto f D (f '' D) := hf.2.2.1
  refine (thm10_1_isKQC_iff hD hK' hhom).2 ⟨thm9_1_isACL hf, ?_⟩
  have hae := ae_le_essSup (μ := volume.restrict D)
    (f := fun z => ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) / (‖dz f z‖ - ‖dzbar f z‖)))
  filter_upwards [hae, thm9_6_cor2_jacobian_pos hf] with z h1 hJ
  have h2 : ENNReal.ofReal ((‖dz f z‖ + ‖dzbar f z‖) / (‖dz f z‖ - ‖dzbar f z‖)) ≤ ENNReal.ofReal K' :=
    h1.trans hle
  have h3 := (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 h2
  unfold jacobian at hJ
  have ha : 0 ≤ ‖dz f z‖ := norm_nonneg _
  have hb : 0 ≤ ‖dzbar f z‖ := norm_nonneg _
  have hlt : ‖dzbar f z‖ < ‖dz f z‖ := by nlinarith
  rw [div_le_iff₀ (sub_pos.2 hlt)] at h3
  linarith

/-- `1 ≤ K[f]` for a q.c. map `f` of a nonempty surface: every local expression has positive Jacobian almost
everywhere (Theorem 9.6). -/
theorem s29_m_one_le_maxDilatationRS {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [Nonempty A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} (hf : IsQCRS f) :
    1 ≤ maxDilatationRS f := by
  obtain ⟨K, -, hK⟩ := hf
  obtain ⟨x⟩ := (inferInstance : Nonempty A)
  refine le_trans ?_ (le_iSup (fun x => maxDilatation (localMapExpr f x) (localMapDomain f x)) x)
  have hΩ := s23_localMapDomain_isOpen f.continuous x
  have hne : (localMapDomain f x).Nonempty := ⟨_, (s23_h_center f x).1⟩
  have hμ : volume.restrict (localMapDomain f x) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact hΩ.measure_ne_zero volume hne
  rw [maxDilatation, ← essSup_const (1 : ℝ≥0∞) hμ]
  refine essSup_mono_ae ?_
  filter_upwards [thm9_6_cor2_jacobian_pos (hK x)] with z hJ
  unfold jacobian at hJ
  set a := ‖dz (localMapExpr f x) z‖
  set b := ‖dzbar (localMapExpr f x) z‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hlt : b < a := by nlinarith
  show (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((a + b) / (a - b))
  rw [ENNReal.one_le_ofReal, one_le_div (sub_pos.2 hlt)]
  linarith

/-- `K[f] ≠ ∞` for a q.c. map `f` of surfaces. -/
theorem s29_m_maxDilatationRS_ne_top {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} (hf : IsQCRS f) :
    maxDilatationRS f ≠ ⊤ := by
  obtain ⟨K, hK⟩ := hf
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (maxDilatationRS_le hK)

/-- `1 ≤ K[f]` in `ℝ`, for a q.c. map `f` of a nonempty surface. -/
theorem s29_m_one_le_toReal {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [Nonempty A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} (hf : IsQCRS f) :
    1 ≤ (maxDilatationRS f).toReal := by
  have := ENNReal.toReal_mono (s29_m_maxDilatationRS_ne_top hf) (s29_m_one_le_maxDilatationRS hf)
  simpa using this

/-- A q.c. map `f` of surfaces with `K[f] ≤ K'`, `1 ≤ K'`, is `K'`-q.c. (Theorem 10.1 in every chart). -/
theorem s29_m_isKQCRS_of_le {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} (hf : IsQCRS f) {K' : ℝ}
    (hK' : 1 ≤ K') (hle : maxDilatationRS f ≤ ENNReal.ofReal K') : IsKQCRS f K' := by
  obtain ⟨K, -, hK⟩ := hf
  refine ⟨hK', fun x => s29_m_isKQC_of_maxDilatation_le (hK x) hK' ?_⟩
  exact (le_iSup (fun x => maxDilatation (localMapExpr f x) (localMapDomain f x)) x).trans hle

/-- A q.c. map `f` of a nonempty surface is `K[f]`-q.c. -/
theorem s29_m_isKQCRS_maxDil {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [Nonempty A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} (hf : IsQCRS f) :
    IsKQCRS f (maxDilatationRS f).toReal :=
  s29_m_isKQCRS_of_le hf (s29_m_one_le_toReal hf)
    (by rw [ENNReal.ofReal_toReal (s29_m_maxDilatationRS_ne_top hf)])

/-- The inverse of a `K`-q.c. map of surfaces is `K`-q.c.: in charts it is the inverse of the local expression
(`thm7_2_inv`). -/
theorem s29_m_isKQCRS_symm {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} {K : ℝ} (hf : IsKQCRS f K) :
    IsKQCRS f.symm K := by
  refine ⟨hf.1, fun y => ?_⟩
  set x := f.symm y
  have hfx : f x = y := f.apply_symm_apply y
  set L := localMapExpr f x with hLdef
  set D := localMapDomain f x with hDdef
  have hL : IsKQC L D K := hf.2 x
  have hinj : InjOn L D := hL.2.2.1.2.1
  have hLz : ∀ z ∈ D, L z = chartAt ℂ y (f ((chartAt ℂ x).symm z)) := by
    intro z _
    simp only [hLdef, localMapExpr, hfx]
  have hDz : ∀ z ∈ D, z ∈ (chartAt ℂ x).target ∧ f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ y).source := by
    intro z hz
    have hz' := hz
    simp only [hDdef, localMapDomain, mem_inter_iff, mem_preimage] at hz'
    rw [hfx] at hz'
    exact hz'
  have hback : ∀ z ∈ D, localMapExpr f.symm y (L z) = z := by
    intro z hz
    obtain ⟨h1, h2⟩ := hDz z hz
    rw [hLz z hz]
    simp only [localMapExpr]
    rw [(chartAt ℂ y).left_inv h2, f.symm_apply_apply, (chartAt ℂ x).right_inv h1]
  have himg : L '' D = localMapDomain f.symm y := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨h1, h2⟩ := hDz z hz
      rw [hLz z hz]
      refine ⟨(chartAt ℂ y).map_source h2, ?_⟩
      show f.symm ((chartAt ℂ y).symm (chartAt ℂ y (f ((chartAt ℂ x).symm z)))) ∈
        (chartAt ℂ (f.symm y)).source
      rw [(chartAt ℂ y).left_inv h2, f.symm_apply_apply]
      exact (chartAt ℂ x).map_target h1
    · rintro ⟨hw1, hw2⟩
      have hw2' : f.symm ((chartAt ℂ y).symm w) ∈ (chartAt ℂ x).source := hw2
      have hzD : chartAt ℂ x (f.symm ((chartAt ℂ y).symm w)) ∈ D := by
        simp only [hDdef, localMapDomain, mem_inter_iff, mem_preimage, hfx]
        refine ⟨(chartAt ℂ x).map_source hw2', ?_⟩
        rw [(chartAt ℂ x).left_inv hw2', f.apply_symm_apply]
        exact (chartAt ℂ y).map_target hw1
      refine ⟨chartAt ℂ x (f.symm ((chartAt ℂ y).symm w)), hzD, ?_⟩
      rw [hLz _ hzD, (chartAt ℂ x).left_inv hw2', f.apply_symm_apply, (chartAt ℂ y).right_inv hw1]
  have hinv := thm7_2_inv hL
  rw [himg] at hinv
  refine ad_isKQC_congr hinv fun w hw => ?_
  rw [← himg] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  rw [hback z hz, hinj.leftInvOn_invFunOn hz]

/-- The inverse of a q.c. map `f` of a nonempty surface is q.c., with `K[f⁻¹] ≤ K[f]`. -/
theorem s29_m_maxDil_symm_le {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [Nonempty A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} (hf : IsQCRS f) :
    IsQCRS f.symm ∧ maxDilatationRS f.symm ≤ maxDilatationRS f := by
  have h := s29_m_isKQCRS_symm (s29_m_isKQCRS_maxDil hf)
  refine ⟨⟨_, h⟩, ?_⟩
  have := maxDilatationRS_le h
  rwa [ENNReal.ofReal_toReal (s29_m_maxDilatationRS_ne_top hf)] at this

/-- `0 ≤ ½ ln K[f]` for a q.c. map `f` of a nonempty surface. -/
theorem s29_m_half_log_nonneg {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [Nonempty A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {f : A ≃ₜ B} (hf : IsQCRS f) :
    0 ≤ (1 / 2 : ℝ) * Real.log (maxDilatationRS f).toReal := by
  have := Real.log_nonneg (s29_m_one_le_toReal hf)
  positivity

/-- `½ ln K` is monotone: `K[g'] ≤ K[g]` gives `½ ln K[g'] ≤ ½ ln K[g]`, for q.c. maps `g'` (of a nonempty
surface) and `g`. -/
theorem s29_m_half_log_mono {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [Nonempty A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] {C : Type*} [TopologicalSpace C] [ChartedSpace ℂ C]
    {D : Type*} [TopologicalSpace D] [ChartedSpace ℂ D] {g' : A ≃ₜ B} (hg' : IsQCRS g') {g : C ≃ₜ D}
    (hg : IsQCRS g) (hle : maxDilatationRS g' ≤ maxDilatationRS g) :
    (1 / 2 : ℝ) * Real.log (maxDilatationRS g').toReal ≤
      (1 / 2 : ℝ) * Real.log (maxDilatationRS g).toReal := by
  have h1 := s29_m_one_le_toReal hg'
  have h2 : (maxDilatationRS g').toReal ≤ (maxDilatationRS g).toReal :=
    ENNReal.toReal_mono (s29_m_maxDilatationRS_ne_top hg) hle
  have := Real.log_le_log (by linarith) h2
  linarith

/-- Conformal invariance of `K` ((23.4)): for a q.c. `g` and biholomorphic `c₁`, `c₂`, the map `c₂ ∘ g ∘ c₁` is
q.c. with `K[c₂ ∘ g ∘ c₁] ≤ K[g]`. -/
theorem s29_m_maxDil_conj_biholo {A : Type*} [TopologicalSpace A] [ChartedSpace ℂ A] [IsManifold 𝓘(ℂ) ω A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ω B]
    {C : Type*} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ) ω C]
    {D : Type*} [TopologicalSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ) ω D]
    {g : B ≃ₜ C} (hg : IsQCRS g) {c₁ : A ≃ₜ B} (hc₁ : IsBiholomorphic c₁) {c₂ : C ≃ₜ D}
    (hc₂ : IsBiholomorphic c₂) :
    IsQCRS (c₁.trans (g.trans c₂)) ∧ maxDilatationRS (c₁.trans (g.trans c₂)) ≤ maxDilatationRS g := by
  obtain ⟨K, hK⟩ := hg
  have h1 : IsKQCRS c₁ 1 := (isKQCRS_one_iff c₁).2 hc₁
  have h2 : IsKQCRS c₂ 1 := (isKQCRS_one_iff c₂).2 hc₂
  have hc₁le : maxDilatationRS c₁ ≤ 1 := by simpa using maxDilatationRS_le h1
  have hc₂le : maxDilatationRS c₂ ≤ 1 := by simpa using maxDilatationRS_le h2
  obtain ⟨hgc, hgcle⟩ := eq23_4 hK h2
  obtain ⟨hall, hallle⟩ := eq23_4 h1 hgc
  refine ⟨⟨_, hall⟩, ?_⟩
  calc maxDilatationRS (c₁.trans (g.trans c₂)) = maxDilatationRS ((g.trans c₂) ∘ c₁) := rfl
    _ ≤ maxDilatationRS (g.trans c₂) * maxDilatationRS c₁ := hallle
    _ ≤ maxDilatationRS (g.trans c₂) * 1 := by gcongr
    _ = maxDilatationRS (c₂ ∘ g) := by rw [mul_one]; rfl
    _ ≤ maxDilatationRS c₂ * maxDilatationRS g := hgcle
    _ ≤ 1 * maxDilatationRS g := by gcongr
    _ = maxDilatationRS g := one_mul _

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

/-- §29.1 (the third metric axiom, split off from `teichDistance_metric`): `d_T(τ₁, τ₂) = 0` only if
`τ₁ = τ₂`; the Teichmüller map realizing the distance has `K = 1`, so it is conformal. -/
theorem teichDistance_eq_of_eq_zero {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) :
    ∀ p q : TeichSpace S₀, teichDistance p q = 0 → p = q := by
  sorry

/-- §29.1: along a Teichmüller deformation `[S_{q,k}, f]`, `d_T([S₀, id], [S_{q,k}, f]) = ½ ln((1+k)/(1-k))`. -/
theorem teichDistance_deformation {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (hid : IsQCRS (Homeomorph.refl S₀))
    {q : S₀ → ℂ → ℂ} {k : ℝ} {p : TeichSpace S₀} (h : IsDeformationPoint q k p) :
    teichDistance (TeichSpace.basePoint hid) p = (1 / 2) * Real.log ((1 + k) / (1 - k)) := by
  sorry

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
  sorry

/-- §29.1, (29.1) ⟹ (29.2): if `kₙ → k` and `ωₙ → ω` (coordinates in `Q(S₀)`, equivalently the
local coefficients), then `d_T([Sₙ, fₙ], [S, f]) → 0`. -/
theorem eq29_1_imp_eq29_2 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) {qn : ℕ → S₀ → ℂ → ℂ}
    {q : S₀ → ℂ → ℂ} (hqn : ∀ n, IsHolQuadDiff (qn n)) (hq : IsHolQuadDiff q)
    (hconv : ∀ x z, Tendsto (fun n => qn n x z) atTop (𝓝 (q x z))) {kn : ℕ → ℝ} {k : ℝ}
    (hkn : ∀ n, 0 ≤ kn n ∧ kn n < 1) (hk : 0 ≤ k) (hk' : k < 1) (hkconv : Tendsto kn atTop (𝓝 k))
    {pn : ℕ → TeichSpace S₀} {p : TeichSpace S₀} (hpn : ∀ n, IsDeformationPoint (qn n) (kn n) (pn n))
    (hp : IsDeformationPoint q k p) :
    Tendsto (fun n => teichDistance (pn n) p) atTop (𝓝 0) := by
  sorry

/-- (29.8): if `d_T([Sₙ, fₙ], [S, f]) → 0` then the distances to `[S₀, id]` are bounded, so
`kₙ ≤ k₀ < 1` for all `n`. -/
theorem eq29_8 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (hid : IsQCRS (Homeomorph.refl S₀))
    {pn : ℕ → TeichSpace S₀} {p : TeichSpace S₀} (hconv : Tendsto (fun n => teichDistance (pn n) p) atTop (𝓝 0))
    {qn : ℕ → S₀ → ℂ → ℂ} {kn : ℕ → ℝ} (hpn : ∀ n, IsDeformationPoint (qn n) (kn n) (pn n)) :
    ∃ k₀ : ℝ, k₀ < 1 ∧ ∀ n, kn n ≤ k₀ := by
  sorry

/-- §29.1, (29.2) ⟹ (29.1): if `d_T([Sₙ, fₙ], [S, f]) → 0` (with `(ωₙ, kₙ)`, `(ω, k)` the
normalized Teichmüller data, `‖e(ωₙ)‖ = ‖e(ω)‖ = 1`), then `kₙ → k` and, when `k ≠ 0`,
`ωₙ → ω` (by compactness of the unit sphere and the first part). -/
theorem eq29_2_imp_eq29_1 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6)))
    {qn : ℕ → (holQuadDiffSubmodule S₀).restrictScalars ℝ} {q : (holQuadDiffSubmodule S₀).restrictScalars ℝ}
    (hqn : ∀ n, ‖e (qn n)‖ = 1) (hq : ‖e q‖ = 1) {kn : ℕ → ℝ} {k : ℝ} (hkn : ∀ n, 0 ≤ kn n ∧ kn n < 1)
    (hk : 0 ≤ k) (hk' : k < 1) {pn : ℕ → TeichSpace S₀} {p : TeichSpace S₀}
    (hpn : ∀ n, IsDeformationPoint (qn n) (kn n) (pn n)) (hp : IsDeformationPoint q k p)
    (hconv : Tendsto (fun n => teichDistance (pn n) p) atTop (𝓝 0)) :
    Tendsto kn atTop (𝓝 k) ∧ (k ≠ 0 → Tendsto (fun n => e (qn n)) atTop (𝓝 (e q))) := by
  sorry

/-- **Theorem 29.1**: with the Teichmüller metric, `T(S₀)` is homeomorphic to the unit ball of
`ℝ^{6g-6}` (`g > 1` the genus of `S₀`): the bijection `T̃(S₀) → T(S₀)` is a homeomorphism for the
ball topology and the Teichmüller metric. -/
theorem thm29_1 {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g)
    (e : (holQuadDiffSubmodule S₀).restrictScalars ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (6 * g - 6))) :
    ∃ Φ : EuclideanSpace ℝ (Fin (6 * g - 6)) → TeichSpace S₀,
      InjOn Φ (ball 0 1) ∧ (∀ p : TeichSpace S₀, ∃ v ∈ ball (0 : EuclideanSpace ℝ (Fin (6 * g - 6))) 1, Φ v = p) ∧
      (∀ (q : (holQuadDiffSubmodule S₀).restrictScalars ℝ) (k : ℝ), ‖e q‖ = 1 → 0 < k → k < 1 →
        IsDeformationPoint q k (Φ (k • e q))) ∧
      ∀ (v : EuclideanSpace ℝ (Fin (6 * g - 6))) (vn : ℕ → EuclideanSpace ℝ (Fin (6 * g - 6))),
        v ∈ ball 0 1 → (∀ n, vn n ∈ ball 0 1) →
        (Tendsto vn atTop (𝓝 v) ↔ Tendsto (fun n => teichDistance (Φ (vn n)) (Φ v)) atTop (𝓝 0)) := by
  sorry

/-! ## §29.2 Completeness -/

/-- **Theorem 29.2**: `T(S₀)` with the Teichmüller metric is a complete metric space. -/
theorem thm29_2_complete {g : ℕ} (hg : 1 < g) (hS : HasGenus S₀ g) (p : ℕ → TeichSpace S₀)
    (hp : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, teichDistance (p m) (p n) < ε) :
    ∃ q : TeichSpace S₀, Tendsto (fun n => teichDistance (p n) q) atTop (𝓝 0) := by
  sorry

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
