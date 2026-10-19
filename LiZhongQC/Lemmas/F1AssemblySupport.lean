import LiZhongQC.Lemmas.FoundationSmallSupport
import LiZhongQC.Lemmas.S36BersOrdinary
import LiZhongQC.Lemmas.StrebelDoubleDomain
import LiZhongQC.Lemmas.F1LocalGeometry
import LiZhongQC.Lemmas.FoundationLocalEnds
import LiZhongQC.Lemmas.FoundationQuotient

/-! F1 assembly support 002: repair of the five compile errors of 2064725d. -/

/- BEGIN F1FunnelArc.lean -/
/-! Full ordinary funnel arcs from the authorized pointwise F4a extraction.
Source-only; requires Root's later SmallSupport revision exporting ft4a_one_ordinary. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- A positive real dilation is represented by an actual determinant-one real matrix. -/
theorem ft1fas_positive_dilation (t : ℝ) (ht : 0 < t) :
    ∃ D : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ τ : UpperHalfPlane, ((D • τ : UpperHalfPlane) : ℂ) = (t : ℂ) * (τ : ℂ)) ∧
      mobiusSL (slRealToComplex D) ((1 : ℂ) : ExtPlane) = ((t : ℂ) : ExtPlane) := by
  let s : ℝ := Real.sqrt t
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have hs2 : (s : ℂ) ^ 2 = (t : ℂ) := by
    exact_mod_cast Real.sq_sqrt ht.le
  let D : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    ⟨!![s, 0; 0, s⁻¹], by rw [Matrix.det_fin_two_of, mul_inv_cancel₀ hs]; ring⟩
  have hD : ∀ τ : UpperHalfPlane, ((D • τ : UpperHalfPlane) : ℂ) = (t : ℂ) * (τ : ℂ) := by
    intro τ
    rw [← h36p_m_coe D τ]
    change ((s : ℂ) * (τ : ℂ) + 0) / (0 * (τ : ℂ) + ((s⁻¹ : ℝ) : ℂ)) =
      (t : ℂ) * (τ : ℂ)
    simp only [zero_mul, add_zero, zero_add, Complex.ofReal_inv, div_inv_eq_mul]
    calc (s : ℂ) * (τ : ℂ) * (s : ℂ) = (s : ℂ) ^ 2 * (τ : ℂ) := by ring
      _ = _ := by rw [hs2]
  refine ⟨D, hD, ?_⟩
  rw [k24_mobiusSL_real]
  change mobiusExt (s : ℂ) 0 0 ((s⁻¹ : ℝ) : ℂ) ((1 : ℂ) : ExtPlane) =
    ((t : ℂ) : ExtPlane)
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [mobiusExt_coe (by simpa using inv_ne_zero hsC)]
  refine congrArg (fun z : ℂ => (z : ExtPlane)) ?_
  show ((s : ℂ) * 1 + 0) / (0 * 1 + ((s⁻¹ : ℝ) : ℂ)) = (t : ℂ)
  simp only [mul_one, zero_mul, add_zero, zero_add, Complex.ofReal_inv, div_inv_eq_mul]
  rw [← pow_two, hs2]

/-- Every point of the full open funnel arc is ordinary. This strengthens the existing
F4a existential endpoint; it must retain the arbitrary positive real parameter. -/
theorem ft1fas_funnel_arc_ordinary (hΓ : IsFuchsian Γ)
    (B h : Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam θ : ℝ)
    (hh : h ∈ Γ) (hlam : 1 < lam) (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hscale : ∀ τ : UpperHalfPlane, ((B⁻¹ • (h • (B • τ)) : UpperHalfPlane) : ℂ) =
      (lam : ℂ) * (τ : ℂ))
    (hprec : ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, arg (τ : ℂ) < θ →
      arg ((B⁻¹ • (γ • (B • τ)) : UpperHalfPlane) : ℂ) < θ →
      ∃ k : ℤ, γ = h ^ k ∨ γ = -h ^ k) :
    ∀ t : ℝ, 0 < t → mobiusSL (slRealToComplex B) ((t : ℂ) : ExtPlane) ∈ ordinarySet Γ := by
  intro t ht
  obtain ⟨D, hD, hD1⟩ := ft1fas_positive_dilation t ht
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hargD : ∀ τ : UpperHalfPlane, arg ((D • τ : UpperHalfPlane) : ℂ) = arg (τ : ℂ) := by
    intro τ
    rw [hD]
    exact Complex.arg_real_mul _ ht
  have hargDi : ∀ τ : UpperHalfPlane, arg ((D⁻¹ • τ : UpperHalfPlane) : ℂ) = arg (τ : ℂ) := by
    intro τ
    have hv := hargD (D⁻¹ • τ)
    rw [smul_inv_smul] at hv
    exact hv.symm
  have hscale' : ∀ τ : UpperHalfPlane,
      (((B * D)⁻¹ • (h • ((B * D) • τ)) : UpperHalfPlane) : ℂ) =
        (lam : ℂ) * (τ : ℂ) := by
    intro τ
    simp only [mul_inv_rev, mul_smul]
    apply mul_left_cancel₀ htC
    have hv := hD (D⁻¹ • (B⁻¹ • (h • (B • (D • τ)))))
    rw [smul_inv_smul] at hv
    rw [← hv, hscale, hD]
    ring
  have hprec' : ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, arg (τ : ℂ) < θ →
      arg (((B * D)⁻¹ • (γ • ((B * D) • τ)) : UpperHalfPlane) : ℂ) < θ →
      ∃ k : ℤ, γ = h ^ k ∨ γ = -h ^ k := by
    intro γ hγ τ hτ hγτ
    apply hprec γ hγ (D • τ)
    · rwa [hargD]
    · simpa only [mul_inv_rev, mul_smul, hargDi] using hγτ
  have hpoint := ft4a_one_ordinary hΓ (B * D) h lam θ hh hlam hθ0 hθπ hscale' hprec'
  have hmap : slRealToComplex (B * D) = slRealToComplex B * slRealToComplex D := by
    exact map_mul (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) B D
  rw [hmap, k24_mobiusSL_mul, hD1] at hpoint
  exact hpoint

end LiZhongQC
end -- original noncomputable section
/- END F1FunnelArc.lean -/

/- BEGIN F1CompactOrbitLocal.lean -/
/-! Local closedness of a compact orbit saturation in the ordinary locus.
Source-only; uses the approved narrow ordinary-action producer, not a new discontinuity proof. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- A point outside a compact orbit saturation has a neighborhood avoiding it in the ordinary locus. -/
theorem ft1fas_compact_orbit_local (hΓ : IsFuchsian Γ)
    (K : Set ExtPlane) (hK : IsCompact K)
    (hKΛ : ∀ p ∈ K, p ∉ fuchsianLimitSet Γ)
    (x : ExtPlane) (hxΛ : x ∉ fuchsianLimitSet Γ)
    (hxmiss : ∀ γ : Γ,
      x ∉ mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ.1) '' K) :
    ∃ V : Set ExtPlane, IsOpen V ∧ x ∈ V ∧
      Disjoint V (⋃ γ : Γ, mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ.1) '' K) := by
  obtain ⟨N, hN, hxN, hNΛ⟩ :=
    exists_compact_subset (s36x_limitSet_closed hΓ).isOpen_compl hxΛ
  have hKNΛ : ∀ p ∈ K ∪ N, p ∉ fuchsianLimitSet Γ := by
    intro p hp
    rcases hp with hp | hp
    · exact hKΛ p hp
    · exact hNΛ hp
  let S : Set Γ := {γ |
    (mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ.1) '' (K ∪ N) ∩ (K ∪ N)).Nonempty}
  have hS : S.Finite := s36x_fin hΓ (hK.union hN) hKNΛ
  let Z : Set ExtPlane := ⋃ γ ∈ S,
    mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ.1) '' K
  have hZ : IsClosed Z := hS.isClosed_biUnion fun γ _ =>
    (hK.image (k22_t_continuous _)).isClosed
  have hxZ : x ∉ Z := by
    intro hx
    obtain ⟨γ, hγ, hxγ⟩ := mem_iUnion₂.mp hx
    exact hxmiss γ hxγ
  refine ⟨interior N \ Z, isOpen_interior.sdiff hZ, ⟨hxN, hxZ⟩, ?_⟩
  apply Set.disjoint_left.mpr
  intro y hy hyorbit
  obtain ⟨γ, k, hk, hky⟩ := mem_iUnion.mp hyorbit
  have hγS : γ ∈ S := by
    refine ⟨y, ⟨k, Or.inl hk, hky⟩, Or.inr (interior_subset hy.1)⟩
  exact hy.2 (mem_biUnion hγS ⟨k, hk, hky⟩)

/-- The whole orbit saturation of a compact interior set stays out of a sufficiently
small neighborhood of every ordinary boundary point, including infinity. -/
theorem ft1fas_compact_saturation_avoids_ordinary (hΓ : IsFuchsian Γ)
    (C : Set UpperHalfPlane) (hC : IsCompact C)
    (x : ExtPlane) (hx : x ∈ ordinarySet Γ) :
    ∃ V : Set ExtPlane, IsOpen V ∧ x ∈ V ∧
      Disjoint V {p : ExtPlane | ∃ γ ∈ Γ, ∃ τ ∈ C,
        p = (((γ • τ : UpperHalfPlane) : ℂ) : ExtPlane)} := by
  let K : Set ExtPlane := (fun τ : UpperHalfPlane => ((τ : ℂ) : ExtPlane)) '' C
  have hK : IsCompact K := hC.image
    (OnePoint.continuous_coe.comp UpperHalfPlane.continuous_coe)
  have hnotreal : ∀ τ : UpperHalfPlane, ((τ : ℂ) : ExtPlane) ∉ extRealLine := by
    intro τ hτ
    rcases hτ with hτ | hτ
    · obtain ⟨z, hz, hzτ⟩ := hτ
      have heq : z = (τ : ℂ) := OnePoint.coe_injective hzτ
      rw [heq] at hz
      exact τ.im_pos.ne' hz
    · exact OnePoint.coe_ne_infty (τ : ℂ) hτ
  have hKΛ : ∀ p ∈ K, p ∉ fuchsianLimitSet Γ := by
    intro p hp
    obtain ⟨τ, hτ, rfl⟩ := hp
    intro hlim
    exact hnotreal τ (s36a_limit_real hΓ hlim)
  have hxmiss : ∀ γ : Γ,
      x ∉ mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) γ.1) '' K := by
    intro γ hp
    obtain ⟨p, hpK, hpx⟩ := hp
    obtain ⟨τ, hτ, rfl⟩ := hpK
    change mobiusSL (slRealToComplex γ.1) ((τ : ℂ) : ExtPlane) = x at hpx
    rw [h36t_mobiusSL_coe] at hpx
    apply hnotreal (γ.1 • τ)
    rw [hpx]
    exact hx.1
  obtain ⟨V, hVo, hxV, hdisj⟩ := ft1fas_compact_orbit_local hΓ K hK hKΛ x hx.2 hxmiss
  refine ⟨V, hVo, hxV, hdisj.mono_right ?_⟩
  intro p hp
  obtain ⟨γ, hγ, τ, hτ, hpτ⟩ := hp
  apply mem_iUnion.mpr
  refine ⟨⟨γ, hγ⟩, ((τ : ℂ) : ExtPlane), ⟨τ, hτ, rfl⟩, ?_⟩
  change mobiusSL (slRealToComplex γ) ((τ : ℂ) : ExtPlane) = p
  rw [h36t_mobiusSL_coe]
  exact hpτ.symm

end LiZhongQC
end -- original noncomputable section
/- END F1CompactOrbitLocal.lean -/

/- BEGIN F1ResidualCover.lean -/
/-! Explicit finite residual core after funnel-angle shrinking. Source-only candidate. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- A nonsymmetric closed angular band is a closed subset of a compact symmetric band. -/
theorem ft1fas_closed_band_compact (lam a b : ℝ) (hlam : 1 < lam)
    (ha : 0 < a) (hb : b < Real.pi) :
    IsCompact {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧ ‖(τ : ℂ)‖ ≤ lam ∧
      a ≤ arg (τ : ℂ) ∧ arg (τ : ℂ) ≤ b} := by
  let ε : ℝ := min a (min (Real.pi - b) (Real.pi / 2)) / 2
  have hmin : 0 < min a (min (Real.pi - b) (Real.pi / 2)) :=
    lt_min ha (lt_min (sub_pos.mpr hb) (by positivity))
  have hε : 0 < ε := half_pos hmin
  have hεa : ε ≤ a := by
    have h := min_le_left a (min (Real.pi - b) (Real.pi / 2))
    dsimp [ε]
    linarith
  have hεb : ε ≤ Real.pi - b := by
    have h := (min_le_right a (min (Real.pi - b) (Real.pi / 2))).trans
      (min_le_left (Real.pi - b) (Real.pi / 2))
    dsimp [ε]
    linarith
  have hεπ : ε < Real.pi / 2 := by
    have h := (min_le_right a (min (Real.pi - b) (Real.pi / 2))).trans
      (min_le_right (Real.pi - b) (Real.pi / 2))
    dsimp [ε]
    linarith [Real.pi_pos]
  have hc : Continuous (fun τ : UpperHalfPlane => ‖(τ : ℂ)‖) :=
    UpperHalfPlane.continuous_coe.norm
  have hclosed : IsClosed {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧ ‖(τ : ℂ)‖ ≤ lam ∧
      a ≤ arg (τ : ℂ) ∧ arg (τ : ℂ) ≤ b} :=
    (isClosed_le continuous_const hc).inter ((isClosed_le hc continuous_const).inter
      ((isClosed_le continuous_const ft1g_arg_continuous).inter
        (isClosed_le ft1g_arg_continuous continuous_const)))
  apply (ft1g_annular_band_compact lam ε hlam hε hεπ).of_isClosed_subset hclosed
  intro τ hτ
  refine ⟨hτ.1, hτ.2.1, hεa.trans hτ.2.2.1, ?_⟩
  linarith [hτ.2.2.2]

/-- Shrinking finite funnel collars adds explicit closed angular bands to the compact core.
The incoming high-collar coverage is produced from B and the local period residuals;
the outgoing horoball height is literally one. -/
theorem ft1fas_cover_after_shrinking {n m : ℕ}
    (C₀ : Set UpperHalfPlane) (hC₀ : IsCompact C₀)
    (A : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ) (Y : Fin n → ℝ)
    (B h : Fin m → Matrix.SpecialLinearGroup (Fin 2) ℝ) (lam θ₀ θ : Fin m → ℝ)
    (hY : ∀ i, 1 < Y i)
    (hdata : ∀ j, h j ∈ Γ ∧ 1 < lam j ∧ 0 < θ j ∧ θ j ≤ θ₀ j ∧ θ₀ j < Real.pi ∧
      ∀ τ : UpperHalfPlane, (((B j)⁻¹ • (h j • (B j • τ)) : UpperHalfPlane) : ℂ) =
        (lam j : ℂ) * (τ : ℂ))
    (hcover : ∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, γ • τ ∈ C₀ ∨
      (∃ i, Y i < ((A i)⁻¹ • (γ • τ)).im) ∨
      ∃ j, arg (((B j)⁻¹ • (γ • τ) : UpperHalfPlane) : ℂ) < θ₀ j) :
    let C : Set UpperHalfPlane := C₀ ∪ ⋃ j : Fin m,
      (fun τ : UpperHalfPlane => B j • τ) ''
        {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧ ‖(τ : ℂ)‖ ≤ lam j ∧
          θ j ≤ arg (τ : ℂ) ∧ arg (τ : ℂ) ≤ θ₀ j}
    IsCompact C ∧ ∀ τ : UpperHalfPlane, ∃ γ ∈ Γ, γ • τ ∈ C ∨
      (∃ i, 1 < ((A i)⁻¹ • (γ • τ)).im) ∨
      ∃ j, arg (((B j)⁻¹ • (γ • τ) : UpperHalfPlane) : ℂ) < θ j := by
  dsimp only
  have hband : ∀ j : Fin m, IsCompact {τ : UpperHalfPlane | 1 ≤ ‖(τ : ℂ)‖ ∧
      ‖(τ : ℂ)‖ ≤ lam j ∧ θ j ≤ arg (τ : ℂ) ∧ arg (τ : ℂ) ≤ θ₀ j} := by
    intro j
    exact ft1fas_closed_band_compact (lam j) (θ j) (θ₀ j)
      (hdata j).2.1 (hdata j).2.2.1 (hdata j).2.2.2.2.1
  refine ⟨hC₀.union (isCompact_iUnion fun j => (hband j).image (continuous_const_smul (B j))), ?_⟩
  intro τ
  obtain ⟨γ, hγ, hγτ⟩ := hcover τ
  rcases hγτ with hcore | hcusp | hfun
  · exact ⟨γ, hγ, Or.inl (Or.inl hcore)⟩
  · obtain ⟨i, hi⟩ := hcusp
    exact ⟨γ, hγ, Or.inr (Or.inl ⟨i, (hY i).trans hi⟩)⟩
  · obtain ⟨j, hj⟩ := hfun
    by_cases hthin : arg (((B j)⁻¹ • (γ • τ) : UpperHalfPlane) : ℂ) < θ j
    · exact ⟨γ, hγ, Or.inr (Or.inr ⟨j, hthin⟩)⟩
    let σ : UpperHalfPlane := (B j)⁻¹ • (γ • τ)
    obtain ⟨k, hk0, hk1⟩ := ft1g_scale_to_annulus (lam j) (hdata j).2.1 σ
    let σ' : UpperHalfPlane := (B j)⁻¹ • (h j ^ k • (B j • σ))
    have hσ' : (σ' : ℂ) = (lam j : ℂ) ^ k * (σ : ℂ) :=
      ft4a_scale_zpow (hdata j).2.2.2.2.2 k σ
    have harg : arg (σ' : ℂ) = arg (σ : ℂ) := by
      rw [hσ']
      have hcast : (lam j : ℂ) ^ k = ((lam j ^ k : ℝ) : ℂ) := by norm_cast
      rw [hcast]
      exact Complex.arg_real_mul _ (zpow_pos (lt_trans zero_lt_one (hdata j).2.1) k)
    refine ⟨h j ^ k * γ, Γ.mul_mem (Γ.zpow_mem (hdata j).1 k) hγ, Or.inl (Or.inr ?_)⟩
    apply mem_iUnion.mpr
    refine ⟨j, σ', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa only [hσ'] using hk0
    · simpa only [hσ'] using hk1
    · rw [harg]
      exact le_of_not_gt hthin
    · rw [harg]
      exact hj.le
    · simp only [σ', σ, smul_inv_smul, mul_smul]

end LiZhongQC
end -- original noncomputable section
/- END F1ResidualCover.lean -/

/- BEGIN F1HeightOneCusps.lean -/
/-! Height-one cusp separation from actual high collars and the approved C/D transition bound.
Source-only; no local C/D proof is duplicated. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- High cusps belonging to distinct precisely invariant exteriors extend to the fixed
height-one horoballs without overlap. The nonzero-transition case consumes worker3's bound;
the zero-transition case is proved by overlapping sufficiently high original cusps. -/
theorem ft1fas_height_one_cusp_separation (hΓ : IsFuchsian Γ) {n : ℕ}
    (W : Fin n → Set UpperHalfPlane)
    (A π₀ : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ) (Y : Fin n → ℝ)
    (hcusp : ∀ i, π₀ i ∈ Γ ∧ ∀ τ : UpperHalfPlane,
      π₀ i • (A i • τ) = A i • ((1 : ℝ) +ᵥ τ))
    (hhigh : ∀ i, {τ : UpperHalfPlane | Y i < τ.im} ⊆ (fun τ => A i • τ) ⁻¹' W i)
    (hstab : ∀ i, ∀ β ∈ Γ, ((A i)⁻¹ * β * A i) 1 0 = 0 →
      ∃ k : ℤ, β = π₀ i ^ k ∨ β = -π₀ i ^ k)
    (hprec : ∀ i i' γ, γ ∈ Γ →
      (((fun τ : UpperHalfPlane => γ • τ) '' W i) ∩ W i').Nonempty →
      i = i' ∧ ∃ k : ℤ, γ = π₀ i ^ k ∨ γ = -π₀ i ^ k) :
    ∀ i i' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im →
      1 < ((A i')⁻¹ • (γ • (A i • τ))).im →
      i = i' ∧ ∃ k : ℤ, γ = π₀ i ^ k ∨ γ = -π₀ i ^ k := by
  intro i i' γ hγ τ hτ hγτ
  let M : Matrix.SpecialLinearGroup (Fin 2) ℝ := (A i')⁻¹ * γ * A i
  by_cases hc : M 1 0 = 0
  · -- If the fixed ideal points agree, the original HIGH collars overlap;
    -- precision gives the stronger conclusion without using the particular test point.
    have hd : M 1 1 ≠ 0 := by
      intro hd0
      have hdet := hnf_sl2_det M
      rw [hc, hd0] at hdet
      norm_num at hdet
    have hdsq : 0 < (M 1 1) ^ 2 := sq_pos_of_ne_zero hd
    obtain ⟨y, hy⟩ := exists_gt (max (0 : ℝ) (max (Y i) ((M 1 1) ^ 2 * Y i')))
    have hy0 : 0 < y := (le_max_left _ _).trans_lt hy
    have hyi : Y i < y := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hy
    have hyi' : (M 1 1) ^ 2 * Y i' < y :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hy
    let σ : UpperHalfPlane := ⟨⟨0, y⟩, hy0⟩
    have hMim : (M • σ).im = y / (M 1 1) ^ 2 := by
      rw [show (M • σ).im = ((M • σ : UpperHalfPlane) : ℂ).im from rfl,
        h36t_coe_smul, utm_im_mobius (hnf_sl2_det M), hc]
      simp only [Complex.ofReal_zero, zero_mul, zero_add, Complex.normSq_ofReal]
      show y / (M 1 1 * M 1 1) = y / (M 1 1) ^ 2
      rw [pow_two]
    have hMhigh : Y i' < (M • σ).im := by
      rw [hMim]
      apply (lt_div_iff₀ hdsq).mpr
      simpa only [mul_comm] using hyi'
    have hWi : A i • σ ∈ W i := hhigh i hyi
    have hWi' : γ • (A i • σ) ∈ W i' := by
      have hh := hhigh i' hMhigh
      simpa only [M, mul_smul, Set.mem_preimage, smul_inv_smul] using hh
    exact hprec i i' γ hγ ⟨γ • (A i • σ), ⟨A i • σ, hWi, rfl⟩, hWi'⟩
  · have hbound := (ft1gc_cusp_transition_bound hΓ (A i') (A i) (π₀ i') (π₀ i)
      (hcusp i').1 (hcusp i).1 (hcusp i').2 (hcusp i).2 (hstab i') γ hγ hc).2 τ hτ
    exact False.elim ((not_lt_of_ge hbound) hγτ)

end LiZhongQC
end -- original noncomputable section
/- END F1HeightOneCusps.lean -/

/- BEGIN F1CuspNumerics.lean -/
/-! Independent coefficient estimate for cusp-family separation; source-only. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- A horoball reaching a small box over an interval separated from its ideal tangency
point contains the same fixed interior point. The two quadratic inequalities are the
denominator form of Im(M^-1 z)>1 at u+i*v and x+i*eps respectively. -/
theorem ft1fas_horoball_common_point {a c x u v ε : ℝ}
    (hε : 0 < ε) (hv : 0 < v) (hsmall : 8 * v < ε)
    (hux : |u - x| < ε / 2)
    (hsep : ε * |c| ≤ |a - c * x|)
    (hin : (a - c * u) ^ 2 + (c * v) ^ 2 < v) :
    (a - c * x) ^ 2 + (c * ε) ^ 2 < ε := by
  have _ := hv
  have htri : |a - c * x| ≤ |a - c * u| + |c| * |u - x| := by
    calc |a - c * x| = |(a - c * u) + c * (u - x)| := by congr 1; ring
      _ ≤ |a - c * u| + |c * (u - x)| := abs_add_le _ _
      _ = _ := by rw [abs_mul]
  have hmul : |c| * |u - x| ≤ |c| * (ε / 2) :=
    mul_le_mul_of_nonneg_left hux.le (abs_nonneg c)
  have hcU : ε * |c| ≤ 2 * |a - c * u| := by linarith
  have haU : |a - c * x| ≤ 2 * |a - c * u| := by linarith
  have hsA := pow_le_pow_left₀ (abs_nonneg (a - c * x)) haU 2
  have hsC := pow_le_pow_left₀ (mul_nonneg hε.le (abs_nonneg c)) hcU 2
  simp only [mul_pow, sq_abs] at hsA hsC
  have hU : (a - c * u) ^ 2 < v := by nlinarith [sq_nonneg (c * v)]
  nlinarith

end LiZhongQC
end -- original noncomputable section
/- END F1CuspNumerics.lean -/
