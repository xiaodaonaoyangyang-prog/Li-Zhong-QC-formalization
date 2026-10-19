import LiZhongQC.Ch11.S36_Hamilton

/-!
E2 countable-domain producer. Source-only candidate, not compiled.
The countable tiling argument is generalized from worker1's current
StrebelGammaG1cTiles.lean. Its finite interfaces can be thin specializations of
this shared producer once the leader chooses final placement.
No str_* proof is copied. No new global definitions or instances.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

variable {Γ Λ Δ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- An actual right transversal for an arbitrary subgroup, with the identity among
the representatives. No finite-index or selector assumption is made. -/
theorem s36e_right_transversal :
    ∃ T : (Γ ⧸ Λ.subgroupOf Γ) → Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ q, T q ∈ Γ) ∧ (∃ q, T q = 1) ∧
      ∀ γ ∈ Γ, ∃! q : Γ ⧸ Λ.subgroupOf Γ, ∃ δ ∈ Λ, γ = δ * T q := by
  classical
  let K : Subgroup Γ := Λ.subgroupOf Γ
  let q₀ : Γ ⧸ K := QuotientGroup.mk (1 : Γ)
  let R : (Γ ⧸ K) → Γ := fun q => if q = q₀ then 1 else q.out
  have hR : ∀ q : Γ ⧸ K, QuotientGroup.mk (R q) = q := by
    intro q
    by_cases hq : q = q₀
    · change QuotientGroup.mk (if q = q₀ then (1 : Γ) else q.out) = q
      rw [if_pos hq]
      exact hq.symm
    · change QuotientGroup.mk (if q = q₀ then (1 : Γ) else q.out) = q
      rw [if_neg hq]
      exact Quotient.out_eq' q
  let T : (Γ ⧸ K) → Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    fun q => (R q).val⁻¹
  have hT : ∀ q, T q ∈ Γ := fun q => Γ.inv_mem (R q).property
  have hsep : ∀ i j : Γ ⧸ K, T i * (T j)⁻¹ ∈ Λ → i = j := by
    intro i j hij
    have hmem : (R i)⁻¹ * R j ∈ K := by
      change (R i).val⁻¹ * (R j).val ∈ Λ
      simpa only [T, inv_inv] using hij
    have heq : (QuotientGroup.mk (R i) : Γ ⧸ K) = QuotientGroup.mk (R j) :=
      QuotientGroup.eq.mpr hmem
    rwa [hR i, hR j] at heq
  refine ⟨T, hT, ?_, ?_⟩
  · refine ⟨q₀, ?_⟩
    change (R q₀).val⁻¹ = 1
    simp only [R, if_pos rfl, Subgroup.coe_one, inv_one]
  · intro γ hγ
    let a : Γ := ⟨γ, hγ⟩
    let q : Γ ⧸ K := QuotientGroup.mk a⁻¹
    have hq : (QuotientGroup.mk (R q) : Γ ⧸ K) = QuotientGroup.mk a⁻¹ := hR q
    have hmem : (R q)⁻¹ * a⁻¹ ∈ K := QuotientGroup.eq.mp hq
    have hδ : γ * (T q)⁻¹ ∈ Λ := by
      have hh := K.inv_mem hmem
      change ((((R q)⁻¹ * a⁻¹)⁻¹ : Γ).val) ∈ Λ at hh
      simpa only [mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, a, T] using hh
    refine ⟨q, ⟨γ * (T q)⁻¹, hδ, by group⟩, ?_⟩
    intro j hj
    obtain ⟨δ, hδΛ, hγδ⟩ := hj
    apply hsep j q
    have heq : T j * (T q)⁻¹ = δ⁻¹ * (γ * (T q)⁻¹) := by
      rw [hγδ]
      group
    rw [heq]
    exact Λ.mul_mem (Λ.inv_mem hδΛ) hδ


/-- Uniqueness in a right transversal compares representatives after a subgroup multiplier. -/
theorem s36e_countable_right_coset_index {ι : Type*} [Countable ι]
    (T : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ) (hT : ∀ i, T i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : ι, ∃ δ ∈ Δ, γ = δ * T i)
    {i j : ι} {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hδ : δ ∈ Δ) (heq : δ * T i = T j) : i = j := by
  obtain ⟨k, hk, hu⟩ := hcos (T j) (hT j)
  have hi := hu i ⟨δ, hδ, heq.symm⟩
  have hj := hu j ⟨1, Δ.one_mem, by simp⟩
  exact hi.trans hj.symm

/-- A.e. uniqueness modulo sign becomes true coset uniqueness when Delta contains Gamma's kernel. -/
theorem s36e_countable_signed_coset_rigidity (hle : Δ ≤ Γ)
    (hker : Γ ⊓ Subgroup.zpowers (-1) ≤ Δ)
    {ι : Type*} [Countable ι] (T : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hT : ∀ i, T i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : ι, ∃ δ ∈ Δ, γ = δ * T i)
    {i j : ι} {δ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hδ : δ ∈ Δ)
    (heq : (T j)⁻¹ * δ = (T i)⁻¹ ∨ (T j)⁻¹ * δ = -((T i)⁻¹)) :
    i = j ∧ (δ = 1 ∨ δ = -1) := by
  rcases heq with hp | hn
  · have hprod : δ * T i = T j := by
      calc δ * T i = T j * (((T j)⁻¹ * δ) * T i) := by group
        _ = T j := by rw [hp]; group
    have hij := s36e_countable_right_coset_index T hT hcos hδ hprod
    refine ⟨hij, Or.inl ?_⟩
    have h := congrArg (fun x => x * (T i)⁻¹) hprod
    simpa only [← hij, mul_assoc, mul_inv_cancel, mul_one] using h
  · have hprod : δ * T i = -(T j) := by
      calc δ * T i = T j * (((T j)⁻¹ * δ) * T i) := by group
        _ = -(T j) := by rw [hn]; simp
    have hmΓ : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ Γ := by
      have h := Γ.mul_mem (Γ.mul_mem (hle hδ) (hT i)) (Γ.inv_mem (hT j))
      simpa only [hprod, neg_mul, mul_inv_cancel] using h
    have hmΔ : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) ∈ Δ :=
      hker ⟨hmΓ, Subgroup.mem_zpowers (-1)⟩
    have hnegδ : -δ ∈ Δ := by
      simpa only [neg_one_mul] using Δ.mul_mem hmΔ hδ
    have hprod' : (-δ) * T i = T j := by rw [neg_mul, hprod, neg_neg]
    have hij := s36e_countable_right_coset_index T hT hcos hnegδ hprod'
    refine ⟨hij, Or.inr ?_⟩
    have h := congrArg (fun x => x * (T i)⁻¹) hprod
    simpa only [← hij, mul_assoc, mul_inv_cancel, mul_one, neg_mul] using h

/-- Gamma's a.e. uniqueness simultaneously separates the countable tiles and their Delta translates. -/
theorem s36e_countable_ae_tile_rigidity (hΓ : IsFuchsian Γ) (hle : Δ ≤ Γ)
    (hker : Γ ⊓ Subgroup.zpowers (-1) ≤ Δ)
    {ι : Type*} [Countable ι] (T : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hT : ∀ i, T i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : ι, ∃ δ ∈ Δ, γ = δ * T i)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    ∀ᵐ z ∂(volume.restrict upperHalf), ∀ (i j : ι),
      ∀ δ ∈ Δ, z ∈ h36p_m (T i) '' F →
      h36p_m δ z ∈ h36p_m (T j) '' F → i = j ∧ (δ = 1 ∨ δ = -1) := by
  filter_upwards [h36p_ae_unique hΓ hF, ae_restrict_mem isOpen_upperHalf.measurableSet]
    with z hz hzH i j δ hδ hzi hzj
  rw [h36p_a_image_eq (T i) hF.1] at hzi
  rw [h36p_a_image_eq (T j) hF.1] at hzj
  have hmem : h36p_m ((T j)⁻¹ * δ) z ∈ F := by
    rw [h36p_a_m_mul _ _ hzH]
    exact hzj.1
  have heq := hz ((T j)⁻¹ * δ) (Γ.mul_mem (Γ.inv_mem (hT j)) (hle hδ))
    (T i)⁻¹ (Γ.inv_mem (hT i)) hmem hzi.1
  exact s36e_countable_signed_coset_rigidity hle hker T hT hcos hδ heq

/-- Distinct right-coset tiles have null intersection, even with elliptic points in Gamma. -/
theorem s36e_countable_tiles_null_inter (hΓ : IsFuchsian Γ) (hle : Δ ≤ Γ)
    (hker : Γ ⊓ Subgroup.zpowers (-1) ≤ Δ)
    {ι : Type*} [Countable ι] (T : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hT : ∀ i, T i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : ι, ∃ δ ∈ Δ, γ = δ * T i)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (i j : ι) (hij : i ≠ j) :
    volume ((h36p_m (T i) '' F) ∩ (h36p_m (T j) '' F)) = 0 := by
  have h := s36e_countable_ae_tile_rigidity hΓ hle hker T hT hcos hF
  rw [ae_restrict_iff' isOpen_upperHalf.measurableSet] at h
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [h] with z hz hzI
  obtain ⟨w, hw, hwz⟩ := hzI.1
  have hzH : z ∈ upperHalf := hwz ▸ h36p_m_mem (T i) (hF.1 hw)
  have hzj : h36p_m 1 z ∈ h36p_m (T j) '' F := by
    rw [h36p_a_m_one]
    exact hzI.2
  exact hij (hz hzH i j 1 Δ.one_mem hzI.1 hzj).1

/-- The countable union of right-coset tiles meets every Delta orbit. -/
theorem s36e_countable_tiles_cover (hle : Δ ≤ Γ)
    {ι : Type*} [Countable ι] (T : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hcos : ∀ γ ∈ Γ, ∃! i : ι, ∃ δ ∈ Δ, γ = δ * T i)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) (τ : UpperHalfPlane) :
    ∃ δ ∈ Δ, ((δ • τ : UpperHalfPlane) : ℂ) ∈ ⋃ i : ι, h36p_m (T i) '' F := by
  have _ := hle
  obtain ⟨γ, hγ, hγF⟩ := hF.2.2.1 τ
  obtain ⟨i, hi, -⟩ := hcos γ⁻¹ (Γ.inv_mem hγ)
  obtain ⟨δ, hδ, heq⟩ := hi
  refine ⟨δ⁻¹, Δ.inv_mem hδ, mem_iUnion.mpr ⟨i, ?_⟩⟩
  refine ⟨((γ • τ : UpperHalfPlane) : ℂ), hγF, ?_⟩
  rw [h36p_m_coe]
  apply congrArg (fun w : UpperHalfPlane => (w : ℂ))
  have hmat : T i * γ = δ⁻¹ := by
    calc T i * γ = δ⁻¹ * (δ * T i) * γ := by group
      _ = δ⁻¹ := by rw [← heq]; group
  rw [← mul_smul, hmat]

/-- A countable right transversal tiles a fundamental domain for Delta.
The full central kernel condition prevents coincident tiles coming from opposite signs. -/
theorem s36e_countable_fundamental_tiling (hΓ : IsFuchsian Γ) (hle : Δ ≤ Γ)
    (hker : Γ ⊓ Subgroup.zpowers (-1) ≤ Δ)
    {ι : Type*} [Countable ι] (T : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hT : ∀ i, T i ∈ Γ)
    (hcos : ∀ γ ∈ Γ, ∃! i : ι, ∃ δ ∈ Δ, γ = δ * T i)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F) :
    IsFundamentalDomainH Δ (⋃ i : ι, h36p_m (T i) '' F) ∧
      (∀ i, MeasurableSet (h36p_m (T i) '' F)) ∧
      (∀ i j : ι, i ≠ j →
        volume ((h36p_m (T i) '' F) ∩ (h36p_m (T j) '' F)) = 0) := by
  classical
  let E : Set ℂ := ⋃ i : ι, h36p_m (T i) '' F
  have hm : ∀ i, MeasurableSet (h36p_m (T i) '' F) := by
    intro i
    rw [h36p_a_image_eq (T i) hF.1]
    exact (h36p_m_measurable _ hF.2.1).inter isOpen_upperHalf.measurableSet
  have hEH : E ⊆ upperHalf := by
    intro z hz
    obtain ⟨i, w, hw, rfl⟩ := mem_iUnion.mp hz
    exact h36p_m_mem (T i) (hF.1 hw)
  have hEm : MeasurableSet E := MeasurableSet.iUnion hm
  have ha := s36e_countable_ae_tile_rigidity hΓ hle hker T hT hcos hF
  rw [ae_restrict_iff' isOpen_upperHalf.measurableSet] at ha
  have hint : ∀ τ₁ τ₂ : UpperHalfPlane,
      (τ₁ : ℂ) ∈ interior E → (τ₂ : ℂ) ∈ interior E →
      (∃ δ ∈ Δ, δ • τ₁ = τ₂) → τ₁ = τ₂ := by
    intro τ₁ τ₂ hτ₁ hτ₂ hrel
    obtain ⟨δ, hδ, hδτ⟩ := hrel
    by_cases h1 : δ = 1
    · simpa only [h1, one_smul] using hδτ
    by_cases hm1 : δ = -1
    · apply UpperHalfPlane.ext
      have hh := congrArg (fun τ : UpperHalfPlane => (τ : ℂ)) hδτ
      rw [← h36p_m_coe δ τ₁, hm1, h36p_a_m_neg, h36p_a_m_one] at hh
      exact hh
    let U : Set ℂ := interior E ∩ (upperHalf ∩ h36p_m δ ⁻¹' interior E)
    have hcont : ContinuousOn (h36p_m δ) upperHalf := by
      intro z hz
      exact (h36p_m_hasDerivAt δ hz).continuousAt.continuousWithinAt
    have hU : IsOpen U := isOpen_interior.inter
      (hcont.isOpen_inter_preimage isOpen_upperHalf isOpen_interior)
    have hU0 : volume U = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [ha] with z hz hzU
      obtain ⟨i, hi⟩ := mem_iUnion.mp (interior_subset hzU.1 : z ∈ E)
      obtain ⟨j, hj⟩ := mem_iUnion.mp
        (interior_subset hzU.2.2 : h36p_m δ z ∈ E)
      rcases (hz hzU.2.1 i j δ hδ hi hj).2 with h | h
      · exact h1 h
      · exact hm1 h
    have hτU : (τ₁ : ℂ) ∈ U := by
      refine ⟨hτ₁, τ₁.im_pos, ?_⟩
      change h36p_m δ (τ₁ : ℂ) ∈ interior E
      rw [h36p_m_coe δ τ₁, hδτ]
      exact hτ₂
    rw [hU.eq_empty_of_measure_zero hU0] at hτU
    exact False.elim hτU
  have hnull : volume (E \ interior E) = 0 := by
    have hbad : E \ interior E ⊆
        ⋃ i : ι, h36p_m (T i) '' (F \ interior F) := by
      intro z hz
      obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hz.1
      refine mem_iUnion.mpr ⟨i, y, ⟨hy, ?_⟩, rfl⟩
      intro hyint
      apply hz.2
      have hopen : IsOpen (h36p_m (T i) '' interior F) := by
        rw [h36p_a_image_eq (T i) (interior_subset.trans hF.1), inter_comm]
        have hc : ContinuousOn (h36p_m (T i)⁻¹) upperHalf := fun w hw =>
          (h36p_m_hasDerivAt (T i)⁻¹ hw).continuousAt.continuousWithinAt
        exact hc.isOpen_inter_preimage isOpen_upperHalf isOpen_interior
      apply mem_interior_iff_mem_nhds.mpr
      refine Filter.mem_of_superset (hopen.mem_nhds ⟨y, hyint, rfl⟩) ?_
      intro w hw
      apply mem_iUnion.mpr
      exact ⟨i, (image_mono interior_subset) hw⟩
    apply measure_mono_null hbad
    apply measure_iUnion_null_iff.mpr
    intro i
    apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (s := F \ interior F)
    · intro z hz
      exact ((h36p_m_hasDerivAt (T i) (hF.1 hz.1)).differentiableAt.restrictScalars ℝ).differentiableWithinAt
    · exact hF.2.2.2.2
  refine ⟨⟨hEH, hEm, ?_, hint, hnull⟩, hm,
    s36e_countable_tiles_null_inter hΓ hle hker T hT hcos hF⟩
  exact s36e_countable_tiles_cover hle T hcos hF

/-- E2: a subgroup fundamental domain containing the supplied ambient domain.
Construct by coset translates, respecting the common ineffective kernel.
The conclusion includes the full installed definition, in particular interior uniqueness
and null boundary; a merely measurable selector is not sufficient. -/
theorem s36e_domain_over (hΓ : IsFuchsian Γ)
    {F : Set ℂ} (hF : IsFundamentalDomainH Γ F)
    {Λ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΛ : Λ ≤ Γ)
    (hker : Γ ⊓ Subgroup.zpowers (-1) ≤ Λ) :
    ∃ D : Set ℂ, IsFundamentalDomainH Λ D ∧ F ⊆ D := by
  classical
  letI : Countable Γ := (h36p_countable hΓ).to_subtype
  letI : Countable (Γ ⧸ Λ.subgroupOf Γ) := Quotient.out_injective.countable
  obtain ⟨T, hT, ⟨q₀, hq₀⟩, hcos⟩ :=
    s36e_right_transversal (Γ := Γ) (Λ := Λ)
  obtain ⟨hD, hDm, hdisj⟩ :=
    s36e_countable_fundamental_tiling hΓ hΛ hker T hT hcos hF
  refine ⟨⋃ q : Γ ⧸ Λ.subgroupOf Γ, h36p_m (T q) '' F, hD, ?_⟩
  intro z hz
  refine mem_iUnion.2 ⟨q₀, z, hz, ?_⟩
  rw [hq₀, h36p_a_m_one]

end LiZhongQC
