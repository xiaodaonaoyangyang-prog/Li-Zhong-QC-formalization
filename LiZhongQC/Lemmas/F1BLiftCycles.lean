import LiZhongQC.Lemmas.F1BLiftCycles1
import LiZhongQC.Lemmas.F1BElementary

/-! F1 B4, part two: frontier components through the half-plane charts, loop and line
parametrizations, infinite order of noncentral returns, and the frozen B4 assembly. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- In a half-plane chart of a closed set, the frontier is exactly the real axis of the chart. -/
theorem s36b4_flat_frontier {U : Set UpperHalfPlane} (hUc : IsClosed U)
    (e : OpenPartialHomeomorph UpperHalfPlane ℂ) (htar : e.target = ball 0 1)
    (hU : ∀ x ∈ e.source, x ∈ U ↔ 0 ≤ (e x).im) {x : UpperHalfPlane} (hx : x ∈ e.source) :
    x ∈ frontier U ↔ (e x).im = 0 := by
  rw [hUc.frontier_eq]
  constructor
  · rintro ⟨hxU, hxi⟩
    have h0 := (hU x hx).1 hxU
    refine le_antisymm ?_ h0
    by_contra hpos
    push Not at hpos
    apply hxi
    have hW : IsOpen (e.source ∩ e ⁻¹' {w : ℂ | 0 < w.im}) :=
      e.isOpen_inter_preimage (isOpen_lt continuous_const Complex.continuous_im)
    refine mem_interior.2 ⟨_, ?_, hW, ⟨hx, hpos⟩⟩
    intro y hy
    exact (hU y hy.1).2 (le_of_lt hy.2)
  · intro him
    refine ⟨(hU x hx).2 him.ge, ?_⟩
    intro hint
    obtain ⟨W, hWU, hWo, hxW⟩ := mem_interior.1 hint
    have hcont : ContinuousAt e.symm (e x) := e.continuousAt_symm (e.map_source hx)
    have hpre : e.symm ⁻¹' W ∈ 𝓝 (e x) := by
      apply hcont
      rw [e.left_inv hx]
      exact hWo.mem_nhds hxW
    have htarN : e.target ∈ 𝓝 (e x) := e.open_target.mem_nhds (e.map_source hx)
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hpre htarN)
    set w : ℂ := e x - ((ε / 2 : ℝ) : ℂ) * I with hwdef
    have hw : w ∈ ball (e x) ε := by
      rw [mem_ball, dist_eq_norm, show w - e x = -(((ε / 2 : ℝ) : ℂ) * I) by rw [hwdef]; ring,
        norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
    obtain ⟨hwW, hwT⟩ := hεsub hw
    have hys : e.symm w ∈ e.source := e.map_target hwT
    have hyU : e.symm w ∈ U := hWU hwW
    have h1 := (hU _ hys).1 hyU
    rw [e.right_inv hwT, hwdef] at h1
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, zero_mul, add_zero, him] at h1
    linarith

/-- A continuous injective function on `[t - δ, t + δ]` vanishing at `t` changes sign there. -/
theorem s36b4_opposite_signs (φ : ℝ → ℝ) (t δ : ℝ) (hδ : 0 < δ)
    (hc : ContinuousOn φ (Icc (t - δ) (t + δ))) (hinj : InjOn φ (Icc (t - δ) (t + δ)))
    (h0 : φ t = 0) : φ (t - δ) * φ (t + δ) < 0 := by
  have hmL : t - δ ∈ Icc (t - δ) (t + δ) := ⟨le_rfl, by linarith⟩
  have hmR : t + δ ∈ Icc (t - δ) (t + δ) := ⟨by linarith, le_rfl⟩
  have hmt : t ∈ Icc (t - δ) (t + δ) := ⟨by linarith, by linarith⟩
  have hA : φ (t - δ) ≠ 0 := fun h => by
    have := hinj hmL hmt (h.trans h0.symm)
    linarith
  have hB : φ (t + δ) ≠ 0 := fun h => by
    have := hinj hmR hmt (h.trans h0.symm)
    linarith
  have key : ∀ ψ : ℝ → ℝ, ContinuousOn ψ (Icc (t - δ) (t + δ)) → InjOn ψ (Icc (t - δ) (t + δ)) →
      ψ t = 0 → ¬ (0 < ψ (t - δ) ∧ 0 < ψ (t + δ)) := by
    rintro ψ hψc hψi hψ0 ⟨hL, hR⟩
    set y := min (ψ (t - δ)) (ψ (t + δ)) / 2 with hy
    have hy0 : 0 < y := half_pos (lt_min hL hR)
    have hyL : y < ψ (t - δ) := by
      have := min_le_left (ψ (t - δ)) (ψ (t + δ))
      linarith
    have hyR : y < ψ (t + δ) := by
      have := min_le_right (ψ (t - δ)) (ψ (t + δ))
      linarith
    obtain ⟨x₁, hx₁, hx₁e⟩ := intermediate_value_Icc' (show t - δ ≤ t by linarith)
      (hψc.mono (Icc_subset_Icc le_rfl (by linarith))) ⟨by rw [hψ0]; exact hy0.le, hyL.le⟩
    obtain ⟨x₂, hx₂, hx₂e⟩ := intermediate_value_Icc (show t ≤ t + δ by linarith)
      (hψc.mono (Icc_subset_Icc (by linarith) le_rfl)) ⟨by rw [hψ0]; exact hy0.le, hyR.le⟩
    have hx12 : x₁ = x₂ := hψi ⟨hx₁.1, by linarith [hx₁.2]⟩ ⟨by linarith [hx₂.1], hx₂.2⟩
      (hx₁e.trans hx₂e.symm)
    have hxt : x₁ = t := le_antisymm hx₁.2 (by rw [hx12]; exact hx₂.1)
    rw [hxt, hψ0] at hx₁e
    linarith
  rcases lt_or_gt_of_ne hA with hA' | hA' <;> rcases lt_or_gt_of_ne hB with hB' | hB'
  · exfalso
    refine key (fun x => -φ x) hc.neg (fun x hx y hy h => hinj hx hy (neg_inj.1 h)) (by simp [h0])
      ⟨by show 0 < -φ (t - δ); linarith, by show 0 < -φ (t + δ); linarith⟩
  · exact mul_neg_of_neg_of_pos hA' hB'
  · exact mul_neg_of_pos_of_neg hA' hB'
  · exact absurd ⟨hA', hB'⟩ (key φ hc hinj h0)

/-- A continuous chain in the frontier, injective near `t`, contains a whole frontier
neighbourhood of its point at `t` (one-dimensional invariance of domain in the chart). -/
theorem s36b4_local_open {U : Set UpperHalfPlane} (hUc : IsClosed U)
    (hflat : ∀ p ∈ frontier U, ∃ e : OpenPartialHomeomorph UpperHalfPlane ℂ,
      p ∈ e.source ∧ e p = 0 ∧ e.target = ball 0 1 ∧
      ∀ x ∈ e.source, x ∈ U ↔ 0 ≤ (e x).im)
    (c : ℝ → UpperHalfPlane) (hc : Continuous c) (hcF : ∀ t, c t ∈ frontier U)
    (t δ₀ : ℝ) (hδ₀ : 0 < δ₀) (hinj : InjOn c (Ioo (t - δ₀) (t + δ₀))) :
    ∃ W : Set UpperHalfPlane, IsOpen W ∧ c t ∈ W ∧ W ∩ frontier U ⊆ Set.range c := by
  obtain ⟨e, hpe, he0, htar, hU⟩ := hflat (c t) (hcF t)
  have hpre : c ⁻¹' e.source ∈ 𝓝 t :=
    hc.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hpe)
  obtain ⟨δ₁, hδ₁, hsub⟩ := Metric.mem_nhds_iff.1 hpre
  set δ := min (δ₀ / 2) (δ₁ / 2) with hδdef
  have hδpos : 0 < δ := lt_min (half_pos hδ₀) (half_pos hδ₁)
  have hδ0 : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ₀)
  have hδ1 : δ < δ₁ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ₁)
  have hI : ∀ x ∈ Icc (t - δ) (t + δ), c x ∈ e.source ∧ x ∈ Ioo (t - δ₀) (t + δ₀) := by
    intro x hx
    refine ⟨hsub ?_, ⟨by linarith [hx.1], by linarith [hx.2]⟩⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  set φ : ℝ → ℝ := fun x => (e (c x)).re with hφdef
  have hφc : ContinuousOn φ (Icc (t - δ) (t + δ)) := by
    intro x hx
    exact (Complex.continuous_re.continuousAt.comp
      ((e.continuousAt (hI x hx).1).comp hc.continuousAt)).continuousWithinAt
  have himz : ∀ x ∈ Icc (t - δ) (t + δ), (e (c x)).im = 0 := fun x hx =>
    (s36b4_flat_frontier hUc e htar hU (hI x hx).1).1 (hcF x)
  have hreal : ∀ x ∈ Icc (t - δ) (t + δ), e (c x) = (φ x : ℂ) := fun x hx =>
    Complex.ext (by simp [hφdef]) (by simp [hφdef, himz x hx])
  have hφinj : InjOn φ (Icc (t - δ) (t + δ)) := by
    intro x hx y hy hxy
    apply hinj (hI x hx).2 (hI y hy).2
    apply e.injOn (hI x hx).1 (hI y hy).1
    rw [hreal x hx, hreal y hy]
    exact congrArg _ hxy
  have hφt : φ t = 0 := by
    show (e (c t)).re = 0
    rw [he0, Complex.zero_re]
  have hsign := s36b4_opposite_signs φ t δ hδpos hφc hφinj hφt
  set A := φ (t - δ) with hAdef
  set B := φ (t + δ) with hBdef
  have hA0 : A ≠ 0 := fun h => by rw [h, zero_mul] at hsign; exact lt_irrefl _ hsign
  have hB0 : B ≠ 0 := fun h => by rw [h, mul_zero] at hsign; exact lt_irrefl _ hsign
  set ε := min |A| |B| with hεdef
  have hε : 0 < ε := lt_min (abs_pos.2 hA0) (abs_pos.2 hB0)
  refine ⟨e.source ∩ e ⁻¹' ball 0 ε, e.isOpen_inter_preimage isOpen_ball,
    ⟨hpe, by rw [Set.mem_preimage, he0]; exact mem_ball_self hε⟩, ?_⟩
  rintro x ⟨⟨hxs, hxb⟩, hxF⟩
  have hxim : (e x).im = 0 := (s36b4_flat_frontier hUc e htar hU hxs).1 hxF
  have hxre : |(e x).re| < ε := by
    have : ‖e x‖ < ε := by simpa [mem_ball, dist_zero_right] using hxb
    exact lt_of_le_of_lt (Complex.abs_re_le_norm _) this
  have h1 : |(e x).re| < |A| := lt_of_lt_of_le hxre (min_le_left _ _)
  have h2 : |(e x).re| < |B| := lt_of_lt_of_le hxre (min_le_right _ _)
  have hmem : (e x).re ∈ uIcc A B := by
    rcases lt_or_gt_of_ne hA0 with hA' | hA'
    · have hB' : 0 < B := by
        by_contra hb
        push Not at hb
        nlinarith
      rw [abs_of_neg hA'] at h1
      rw [abs_of_pos hB'] at h2
      rw [abs_lt] at h1 h2
      rw [Set.uIcc_of_le (by linarith)]
      exact ⟨by linarith, by linarith⟩
    · have hB' : B < 0 := by
        by_contra hb
        push Not at hb
        nlinarith
      rw [abs_of_pos hA'] at h1
      rw [abs_of_neg hB'] at h2
      rw [abs_lt] at h1 h2
      rw [Set.uIcc_of_ge (by linarith)]
      exact ⟨by linarith, by linarith⟩
  have hφcu : ContinuousOn φ (uIcc (t - δ) (t + δ)) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact hφc
  obtain ⟨y, hy, hye⟩ := intermediate_value_uIcc hφcu hmem
  have hyI : y ∈ Icc (t - δ) (t + δ) := by rwa [Set.uIcc_of_le (by linarith)] at hy
  refine ⟨y, e.injOn (hI y hyI).1 hxs ?_⟩
  rw [hreal y hyI, hye]
  exact Complex.ext (by simp) (by simp [hxim])

/-- A closed connected subset of `F` which is relatively open in `F` is a connected component. -/
theorem s36b4_range_component {F Z : Set UpperHalfPlane} (hZF : Z ⊆ F) (hZc : IsClosed Z)
    (hZconn : IsPreconnected Z)
    (hloc : ∀ p ∈ Z, ∃ W : Set UpperHalfPlane, IsOpen W ∧ p ∈ W ∧ W ∩ F ⊆ Z)
    {z : UpperHalfPlane} (hz : z ∈ Z) : Z = connectedComponentIn F z := by
  apply Subset.antisymm (hZconn.subset_connectedComponentIn hz hZF)
  choose! W hWo hpW hWF using hloc
  set O := ⋃ p ∈ Z, W p with hO
  have hOo : IsOpen O := isOpen_biUnion fun p hp => hWo p hp
  have hC : IsPreconnected (connectedComponentIn F z) := isPreconnected_connectedComponentIn
  have hCF : connectedComponentIn F z ⊆ F := connectedComponentIn_subset F z
  have hzC : z ∈ connectedComponentIn F z := mem_connectedComponentIn (hZF hz)
  have h1 : connectedComponentIn F z ⊆ O ∪ Zᶜ := by
    intro x _
    by_cases hxZ : x ∈ Z
    · exact Or.inl (mem_iUnion₂.2 ⟨x, hxZ, hpW x hxZ⟩)
    · exact Or.inr hxZ
  have h2 : connectedComponentIn F z ∩ (O ∩ Zᶜ) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    rintro ⟨hx, hxO, hxZ⟩
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hxO
    exact hxZ (hWF p hp ⟨hxp, hCF hx⟩)
  rcases isPreconnected_iff_subset_of_disjoint.1 hC O Zᶜ hOo hZc.isOpen_compl h1 h2 with h | h
  · intro x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 (h hx)
    exact hWF p hp ⟨hxp, hCF hx⟩
  · exact absurd hz (h hzC)

/-- In a free Fuchsian group a noncentral element has infinite order (B5 on its cyclic group). -/
theorem s36b4_zpow_injective (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {H : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hH : H ∈ Γ) (h1 : H ≠ 1) (h2 : H ≠ -1) :
    Function.Injective (fun q : ℤ => H ^ q) := by
  intro q q' hqq
  by_contra hne
  have hle : Subgroup.zpowers H ≤ Γ := (Subgroup.zpowers_le).2 hH
  have hF' : IsFuchsian (Subgroup.zpowers H) := fun C hC =>
    (hΓ C hC).subset (fun γ hγ => ⟨hle hγ.1, hγ.2⟩)
  have hfree' : ActsFreely (Subgroup.zpowers H) := fun γ hγ τ hτ => hfree γ (hle hγ) τ hτ
  have hHm : H ^ (q - q') = 1 := by
    have e : H ^ q = H ^ q' := hqq
    rw [zpow_sub, e, mul_inv_cancel]
  set N : ℕ := (q - q').natAbs with hNdef
  have hN : 0 < N := Int.natAbs_pos.2 (sub_ne_zero.2 hne)
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  have hHN : H ^ (N : ℤ) = 1 := by
    rcases Int.natAbs_eq (q - q') with h | h
    · rw [hNdef, ← h]
      exact hHm
    · rw [show (N : ℤ) = -(q - q') by omega, zpow_neg, hHm, inv_one]
  have hred : ∀ k : ℤ, H ^ k = H ^ (k % N) := by
    intro k
    conv_lhs => rw [← Int.emod_add_mul_ediv k N]
    rw [zpow_add, zpow_mul, hHN, one_zpow, mul_one]
  set O : Set UpperHalfPlane := {x | ∃ k : ℤ, x = H ^ k • UpperHalfPlane.I} with hOdef
  have hOfin : O.Finite := by
    refine ((Finset.range N).finite_toSet.image
      (fun j : ℕ => H ^ (j : ℤ) • UpperHalfPlane.I)).subset ?_
    rintro x ⟨k, rfl⟩
    have hk0 := Int.emod_nonneg k hNz.ne'
    have hk1 := Int.emod_lt_of_pos k hNz
    refine ⟨(k % N).toNat, ?_, ?_⟩
    · simp only [Finset.coe_range, mem_Iio]
      omega
    · show H ^ (((k % N).toNat : ℕ) : ℤ) • UpperHalfPlane.I = H ^ k • UpperHalfPlane.I
      rw [Int.toNat_of_nonneg hk0, ← hred]
  have hOinv : ∀ γ ∈ Subgroup.zpowers H, (fun τ : UpperHalfPlane => γ • τ) '' O = O := by
    intro γ hγ
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hγ
    ext x
    constructor
    · rintro ⟨y, ⟨k, rfl⟩, rfl⟩
      exact ⟨j + k, by
        show H ^ j • H ^ k • UpperHalfPlane.I = H ^ (j + k) • UpperHalfPlane.I
        rw [zpow_add, mul_smul]⟩
    · rintro ⟨k, rfl⟩
      refine ⟨H ^ (k - j) • UpperHalfPlane.I, ⟨k - j, rfl⟩, ?_⟩
      show H ^ j • H ^ (k - j) • UpperHalfPlane.I = H ^ k • UpperHalfPlane.I
      rw [← mul_smul, ← zpow_add, show j + (k - j) = k by ring]
  have hOne : O.Nonempty := ⟨H ^ (0 : ℤ) • UpperHalfPlane.I, by rw [hOdef]; exact ⟨0, rfl⟩⟩
  have hall := ft1gb_bounded_invariant_trivial hF' hfree' hOne hOfin.isBounded hOinv
  rcases hall H (Subgroup.mem_zpowers H) with h | h
  · exact h1 h
  · exact h2 h

/-- A periodic chain whose only self-coincidences are whole periods closes into an embedded circle
with the same image. -/
theorem s36b4_loop_param (c : ℝ → UpperHalfPlane) (hc : Continuous c) (ell : ℝ) (hell : 0 < ell)
    (hper : ∀ t, c (t + ell) = c t) (hinj : ∀ t t', c t = c t' → ∃ q : ℤ, t = t' + q * ell) :
    ∃ κ : Circle → UpperHalfPlane, Topology.IsEmbedding κ ∧ Set.range κ = Set.range c := by
  haveI : Fact (0 < 2 * π) := ⟨by positivity⟩
  have hπ : 0 < 2 * π := by positivity
  set f : ℝ → UpperHalfPlane := fun x => c (ell * x / (2 * π)) with hfdef
  have hf : Continuous f := hc.comp ((continuous_const.mul continuous_id).div_const _)
  have hfper : ∀ x, f (x + 2 * π) = f x := by
    intro x
    show c (ell * (x + 2 * π) / (2 * π)) = c (ell * x / (2 * π))
    rw [show ell * (x + 2 * π) / (2 * π) = ell * x / (2 * π) + ell by field_simp, hper]
  have hzp := s36b4_periodic_zpow c ell 1 (fun t => by rw [one_smul]; exact hper t)
  have hcmod : ∀ t : ℝ, ∃ t₀ ∈ Ico (0 : ℝ) ell, c t = c t₀ := by
    intro t
    refine ⟨t - ⌊t / ell⌋ * ell, ⟨?_, ?_⟩, ?_⟩
    · have := (le_div_iff₀ hell).1 (Int.floor_le (t / ell))
      linarith
    · have := (div_lt_iff₀ hell).1 (Int.lt_floor_add_one (t / ell))
      rw [add_mul, one_mul] at this
      linarith
    · have e := hzp ⌊t / ell⌋ (t - ⌊t / ell⌋ * ell)
      rw [sub_add_cancel, one_zpow, one_smul] at e
      exact e
  set κ₀ : AddCircle (2 * π) → UpperHalfPlane := AddCircle.liftIco (2 * π) 0 f with hκ₀def
  have hκ₀c : Continuous κ₀ :=
    AddCircle.liftIco_continuous (p := 2 * π) (a := 0) (hfper 0).symm hf.continuousOn
  have hval : ∀ y : AddCircle (2 * π),
      κ₀ y = f (AddCircle.equivIco (2 * π) 0 y : ℝ) := fun y => rfl
  have hκ₀inj : Function.Injective κ₀ := by
    intro y y' h
    rw [hval, hval] at h
    have hx := (AddCircle.equivIco (2 * π) 0 y).2
    have hx' := (AddCircle.equivIco (2 * π) 0 y').2
    set x := (AddCircle.equivIco (2 * π) 0 y : ℝ) with hxdef
    set x' := (AddCircle.equivIco (2 * π) 0 y' : ℝ) with hx'def
    obtain ⟨q, hq⟩ := hinj _ _ h
    have hkey : x - x' - q * (2 * π) =
        (2 * π / ell) * (ell * x / (2 * π) - (ell * x' / (2 * π) + q * ell)) := by
      field_simp
      ring
    rw [← hq, sub_self, mul_zero] at hkey
    rw [zero_add] at hx hx'
    have hq1 : (q : ℝ) < 1 := by
      by_contra hc1
      push Not at hc1
      have := mul_le_mul_of_nonneg_right hc1 hπ.le
      linarith [hx.1, hx.2, hx'.1, hx'.2]
    have hq2 : (-1 : ℝ) < q := by
      by_contra hc2
      push Not at hc2
      have := mul_le_mul_of_nonneg_right hc2 hπ.le
      linarith [hx.1, hx.2, hx'.1, hx'.2]
    have hq1' : q < 1 := by exact_mod_cast hq1
    have hq2' : -1 < q := by exact_mod_cast hq2
    have hq0 : q = 0 := by omega
    rw [hq0] at hkey
    have hxx : x = x' := by
      push_cast at hkey
      linarith
    calc y = ((AddCircle.equivIco (2 * π) 0 y : ℝ) : AddCircle (2 * π)) :=
          AddCircle.coe_equivIco.symm
      _ = ((AddCircle.equivIco (2 * π) 0 y' : ℝ) : AddCircle (2 * π)) := by
          rw [← hxdef, ← hx'def, hxx]
      _ = y' := AddCircle.coe_equivIco
  refine ⟨κ₀ ∘ AddCircle.homeomorphCircle'.symm, ?_, ?_⟩
  · have hcont : Continuous (κ₀ ∘ AddCircle.homeomorphCircle'.symm) :=
      hκ₀c.comp AddCircle.homeomorphCircle'.symm.continuous
    exact (hcont.isClosedEmbedding
      (hκ₀inj.comp AddCircle.homeomorphCircle'.symm.injective)).isEmbedding
  · apply Subset.antisymm
    · rintro _ ⟨z, rfl⟩
      exact ⟨_, rfl⟩
    · rintro _ ⟨t, rfl⟩
      obtain ⟨t₀, ht₀, he⟩ := hcmod t
      set x₀ : ℝ := 2 * π * t₀ / ell with hx₀
      have hx₀m : x₀ ∈ Ico (0 : ℝ) (0 + 2 * π) := by
        rw [zero_add, hx₀]
        constructor
        · exact div_nonneg (mul_nonneg hπ.le ht₀.1) hell.le
        · rw [div_lt_iff₀ hell]
          nlinarith [ht₀.2]
      refine ⟨AddCircle.homeomorphCircle' (x₀ : AddCircle (2 * π)), ?_⟩
      show κ₀ (AddCircle.homeomorphCircle'.symm (AddCircle.homeomorphCircle' _)) = c t
      rw [Homeomorph.symm_apply_apply, hκ₀def, AddCircle.liftIco_coe_apply hx₀m, he]
      show c (ell * x₀ / (2 * π)) = c t₀
      congr 1
      rw [hx₀]
      field_simp

/-- A proper injective periodic chain gives an embedded proper line with period one. -/
theorem s36b4_line_param (c : ℝ → UpperHalfPlane) (hc : Continuous c) (hinj : Function.Injective c)
    (ell : ℝ) (hell : 0 < ell) (H : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hper : ∀ t, c (t + ell) = H • c t)
    (hprop : ∀ L : Set UpperHalfPlane, IsCompact L → IsCompact (c ⁻¹' L)) :
    ∃ ρ : ℝ → UpperHalfPlane, Topology.IsEmbedding ρ ∧
      (∀ L : Set UpperHalfPlane, IsCompact L → IsCompact (ρ ⁻¹' L)) ∧
      Set.range ρ = Set.range c ∧ (∀ t, ρ (t + 1) = H • ρ t) ∧ IsClosed (Set.range c) := by
  set ρ : ℝ → UpperHalfPlane := fun t => c (ell * t) with hρdef
  have hρc : Continuous ρ := hc.comp (continuous_const.mul continuous_id)
  have hρinj : Function.Injective ρ := fun x y h => by
    have := hinj h
    exact mul_left_cancel₀ hell.ne' this
  have hρprop : ∀ L : Set UpperHalfPlane, IsCompact L → IsCompact (ρ ⁻¹' L) := by
    intro L hL
    have e : ρ ⁻¹' L = (Homeomorph.mulLeft₀ ell hell.ne') ⁻¹' (c ⁻¹' L) := rfl
    rw [e]
    exact (Homeomorph.mulLeft₀ ell hell.ne').isCompact_preimage.2 (hprop L hL)
  have hP : IsProperMap ρ := isProperMap_iff_isCompact_preimage.2 ⟨hρc, fun K hK => hρprop K hK⟩
  have hemb := Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hρc hρinj hP.isClosedMap
  have hrange : Set.range ρ = Set.range c := by
    apply Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      exact ⟨_, rfl⟩
    · rintro _ ⟨t, rfl⟩
      refine ⟨t / ell, ?_⟩
      show c (ell * (t / ell)) = c t
      rw [mul_div_cancel₀ t hell.ne']
  refine ⟨ρ, hemb.isEmbedding, hρprop, hrange, fun t => ?_, ?_⟩
  · show c (ell * (t + 1)) = H • c (ell * t)
    rw [mul_add, mul_one, hper]
  · rw [← hrange]
    exact hemb.isClosed_range

/-- B4. Lift the constructed transition graph. A central return word gives a compact
Jordan loop; a noncentral least return gives a proper embedded periodic line and its FULL
primitive stabilizer. None of those conclusions is an input of this theorem. -/
theorem ft1gb_lift_boundary_cycles (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    {U : Set UpperHalfPlane} (hUc : IsClosed U) (hUconn : IsConnected U)
    (hUi : ∀ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) '' U = U)
    (hflat : ∀ p ∈ frontier U, ∃ e : OpenPartialHomeomorph UpperHalfPlane ℂ,
      p ∈ e.source ∧ e p = 0 ∧ e.target = ball 0 1 ∧
      ∀ x ∈ e.source, x ∈ U ↔ 0 ≤ (e x).im)
    (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane)
    (σ : Equiv.Perm (Fin n)) (d : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hgraph : (∀ i, Topology.IsEmbedding (a i) ∧ Set.range (a i) ⊆ frontier U) ∧
      frontier U = (⋃ γ ∈ Γ, ⋃ i, (fun τ : UpperHalfPlane => γ • τ) '' Set.range (a i)) ∧
      (∀ i j γ, γ ∈ Γ → ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
        ∀ s : unitInterval, γ • a i t = a j s →
          i = j ∧ (γ = 1 ∨ γ = -1) ∧ t = s) ∧
      (∀ i, d i ∈ Γ ∧ a i 1 = d i • a (σ i) 0) ∧
      (∀ i j γ, γ ∈ Γ → a i 1 = γ • a j 0 →
        j = σ i ∧ (γ = d i ∨ γ = -d i))) :
    ∃ (L N : ℕ) (κ : Fin L → Circle → UpperHalfPlane)
      (ρ : Fin N → ℝ → UpperHalfPlane)
      (h : Fin N → Matrix.SpecialLinearGroup (Fin 2) ℝ),
      ((∀ i, Topology.IsEmbedding (κ i) ∧
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
        (⋃ γ ∈ Γ, ⋃ j, (fun τ : UpperHalfPlane => γ • τ) '' Set.range (ρ j))) ∧
      (∀ j, ∃ (i : Fin n) (ell : ℕ), 0 < ell ∧ (σ ^ ell) i = i ∧
        (∀ k : ℕ, 0 < k → k < ell → (σ ^ k) i ≠ i) ∧
        h j = (List.ofFn (fun k : Fin ell => d ((σ ^ (k : ℕ)) i))).prod) := by
  classical
  -- connectedness of the core is part of the frozen contract; the lift does not need it
  have _hUconn := hUconn
  obtain ⟨hemb, hcov, hint, hdj, hend⟩ := hgraph
  obtain ⟨N₀, r, ell, hcyc, huniq⟩ := ft1gb_minimal_cycles n σ
  have hpath := fun j : Fin N₀ => s36b4_cycle_path hUi a σ d hemb hint hdj hend (r j) (ell j)
    (hcyc j).1 (hcyc j).2.1 (hcyc j).2.2
  choose H c hHdef hcc hcF hHΓ hcper hrig harc hrep using hpath
  have hellpos : ∀ j, (0 : ℝ) < ell j := fun j => by exact_mod_cast (hcyc j).1
  have hfrI : ∀ γ ∈ Γ, ∀ x ∈ frontier U, γ • x ∈ frontier U := by
    intro γ hγ x hx
    have h1 : (fun τ : UpperHalfPlane => γ • τ) '' frontier U = frontier U := by
      calc
        (fun τ : UpperHalfPlane => γ • τ) '' frontier U =
            frontier ((fun τ : UpperHalfPlane => γ • τ) '' U) :=
          (Homeomorph.smul γ : UpperHalfPlane ≃ₜ UpperHalfPlane).image_frontier U
        _ = frontier U := by rw [hUi γ hγ]
    rw [← h1]
    exact ⟨x, hx, rfl⟩
  have hpm : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (x : UpperHalfPlane),
      (γ = 1 ∨ γ = -1) → γ • x = x := by
    rintro γ x (rfl | rfl)
    · exact one_smul _ x
    · exact (s30l_neg_smul 1 x).trans (one_smul _ x)
  have hpmpow : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (q : ℤ),
      (γ = 1 ∨ γ = -1) → (γ ^ q = 1 ∨ γ ^ q = -1) := by
    rintro γ q (rfl | rfl)
    · exact Or.inl (one_zpow q)
    · rcases Int.even_or_odd q with he | ho
      · exact Or.inl (by rw [he.neg_zpow, one_zpow])
      · exact Or.inr (by rw [ho.neg_zpow, one_zpow])
  have hone : (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) ≠ -1 := by
    intro h
    have e := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) ℝ => g 0 0) h
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply,
      Matrix.one_apply_eq] at e
    norm_num at e
  -- positions of a cycle reduce modulo its length
  have hfixz : ∀ j (m : ℤ), ((σ ^ ell j) ^ m) (r j) = r j := by
    intro j m
    induction m using Int.induction_on with
    | zero => simp
    | succ m ih => rw [zpow_add_one, Equiv.Perm.mul_apply, (hcyc j).2.1, ih]
    | pred m ih =>
      rw [zpow_sub_one, Equiv.Perm.mul_apply]
      have : ((σ ^ ell j)⁻¹) (r j) = r j := by
        rw [Equiv.Perm.inv_eq_iff_eq, (hcyc j).2.1]
      rw [this, ih]
  have hmodred : ∀ j (k : ℤ), (σ ^ k) (r j) = (σ ^ ((k % (ell j : ℤ)).toNat)) (r j) := by
    intro j k
    have hz : (0 : ℤ) < ell j := by exact_mod_cast (hcyc j).1
    have hk0 := Int.emod_nonneg k hz.ne'
    conv_lhs => rw [← Int.emod_add_mul_ediv k (ell j)]
    rw [zpow_add, zpow_mul, zpow_natCast, Equiv.Perm.mul_apply, hfixz, ← zpow_natCast,
      Int.toNat_of_nonneg hk0]
  have hsame : ∀ j j' (k k' : ℤ), (σ ^ k) (r j) = (σ ^ k') (r j') → j = j' := by
    intro j j' k k' h
    have hz : (0 : ℤ) < ell j := by exact_mod_cast (hcyc j).1
    have hz' : (0 : ℤ) < ell j' := by exact_mod_cast (hcyc j').1
    have hl : (k % (ell j : ℤ)).toNat < ell j := by
      have := Int.emod_lt_of_pos k hz
      have := Int.emod_nonneg k hz.ne'
      omega
    have hl' : (k' % (ell j' : ℤ)).toNat < ell j' := by
      have := Int.emod_lt_of_pos k' hz'
      have := Int.emod_nonneg k' hz'.ne'
      omega
    obtain ⟨p, -, hpu⟩ := huniq ((σ ^ k) (r j))
    have e1 := hpu ⟨j, ⟨_, hl⟩⟩ (hmodred j k)
    have e2 := hpu ⟨j', ⟨_, hl'⟩⟩ (h.trans (hmodred j' k'))
    exact congrArg Sigma.fst (e1.trans e2.symm)
  -- two chains meeting under the group belong to the same cycle
  have hcross : ∀ j j' (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ), γ ∈ Γ → ∀ t t' : ℝ,
      γ • c j t = c j' t' → j = j' := by
    intro j j' γ hγ t t' he
    obtain ⟨k, g, hg, s, hs, hct⟩ := hrep j t
    obtain ⟨k', g', hg', s', hs', hct'⟩ := hrep j' t'
    have hβ : g'⁻¹ * γ * g ∈ Γ := mul_mem (mul_mem (inv_mem hg') hγ) hg
    have heq : (g'⁻¹ * γ * g) • a ((σ ^ k) (r j)) s = a ((σ ^ k') (r j')) s' := by
      rw [mul_smul, mul_smul, ← hct, he, hct', inv_smul_smul]
    obtain ⟨hii, -, -⟩ := s36b4_arc_rigidity a σ d hint hdj hend _ _ _ hβ s' s hs' hs heq
    exact hsame j j' k k' hii
  -- local injectivity, local openness and components
  have hwin : ∀ j (t : ℝ), InjOn (c j) (Ioo (t - ell j / 2) (t + ell j / 2)) := by
    intro j t x hx y hy hxy
    obtain ⟨q, hq, -⟩ := hrig j 1 (one_mem Γ) x y (by rw [one_smul]; exact hxy.symm)
    have hq1 : (q : ℝ) < 1 := by
      by_contra h
      push Not at h
      have := mul_le_mul_of_nonneg_right h (hellpos j).le
      linarith [hx.1, hx.2, hy.1, hy.2]
    have hq2 : (-1 : ℝ) < q := by
      by_contra h
      push Not at h
      have := mul_le_mul_of_nonneg_right h (hellpos j).le
      linarith [hx.1, hx.2, hy.1, hy.2]
    have hq1' : q < 1 := by exact_mod_cast hq1
    have hq2' : -1 < q := by exact_mod_cast hq2
    have hq0 : q = 0 := by omega
    rw [hq, hq0]
    simp
  have hloc : ∀ j, ∀ p ∈ Set.range (c j), ∃ W : Set UpperHalfPlane,
      IsOpen W ∧ p ∈ W ∧ W ∩ frontier U ⊆ Set.range (c j) := by
    rintro j _ ⟨t, rfl⟩
    exact s36b4_local_open hUc hflat (c j) (hcc j) (hcF j) t (ell j / 2) (half_pos (hellpos j))
      (hwin j t)
  have hcomp : ∀ j, IsClosed (Set.range (c j)) → ∀ z ∈ Set.range (c j),
      Set.range (c j) = connectedComponentIn (frontier U) z := fun j hcl z hz =>
    s36b4_range_component (by rintro _ ⟨t, rfl⟩; exact hcF j t) hcl
      (isPreconnected_range (hcc j)) (hloc j) hz
  -- central cycles close into loops
  have hloop : ∀ j, (H j = 1 ∨ H j = -1) → ∃ κ : Circle → UpperHalfPlane,
      Topology.IsEmbedding κ ∧ Set.range κ = Set.range (c j) ∧ IsClosed (Set.range (c j)) := by
    intro j hj
    have hper' : ∀ t, c j (t + ell j) = c j t := fun t => (hcper j t).trans (hpm _ _ hj)
    obtain ⟨κ, hκ, hκr⟩ := s36b4_loop_param (c j) (hcc j) (ell j) (hellpos j) hper'
      (fun t t' h => by
        obtain ⟨q, hq, -⟩ := hrig j 1 (one_mem Γ) t t' (by rw [one_smul]; exact h.symm)
        exact ⟨q, hq⟩)
    refine ⟨κ, hκ, hκr, ?_⟩
    rw [← hκr]
    exact (isCompact_range hκ.continuous).isClosed
  -- noncentral cycles give proper periodic lines
  have hline : ∀ j, ¬ (H j = 1 ∨ H j = -1) → ∃ ρ : ℝ → UpperHalfPlane,
      Topology.IsEmbedding ρ ∧ (∀ L : Set UpperHalfPlane, IsCompact L → IsCompact (ρ ⁻¹' L)) ∧
      Set.range ρ = Set.range (c j) ∧ (∀ t, ρ (t + 1) = H j • ρ t) ∧
      IsClosed (Set.range (c j)) := by
    intro j hj
    have hinjH := s36b4_zpow_injective hΓ hfree (hHΓ j) (fun h => hj (Or.inl h))
      (fun h => hj (Or.inr h))
    have hcinj : Function.Injective (c j) := by
      intro x y hxy
      obtain ⟨q, hq, hγ⟩ := hrig j 1 (one_mem Γ) x y (by rw [one_smul]; exact hxy.symm)
      have hq0 : q = 0 := by
        rcases hγ with h | h
        · exact hinjH (show H j ^ q = H j ^ (0 : ℤ) by rw [← h, zpow_zero])
        · exfalso
          have hm : H j ^ q = -1 := by rw [← neg_neg (H j ^ q), ← h]
          have h2 : H j ^ (q + q) = H j ^ (0 : ℤ) := by
            rw [zpow_add, hm, zpow_zero, neg_mul, one_mul, neg_neg]
          have hqq : q + q = 0 := hinjH h2
          have hq0 : q = 0 := by omega
          rw [hq0, zpow_zero] at hm
          exact hone hm
      rw [hq, hq0]
      simp
    exact s36b4_line_param (c j) (hcc j) hcinj (ell j) (hellpos j) (H j) (hcper j)
      (s36b4_proper hΓ (c j) (hcc j) (ell j) (hellpos j) (H j) (hHΓ j) (hcper j) hinjH)
  choose! κ' hκ' using hloop
  choose! ρ' hρ' using hline
  set eC := Fintype.equivFin {j : Fin N₀ // H j = 1 ∨ H j = -1} with heC
  set eN := Fintype.equivFin {j : Fin N₀ // ¬ (H j = 1 ∨ H j = -1)} with heN
  refine ⟨Fintype.card {j : Fin N₀ // H j = 1 ∨ H j = -1},
    Fintype.card {j : Fin N₀ // ¬ (H j = 1 ∨ H j = -1)},
    fun i => κ' (eC.symm i).1, fun i => ρ' (eN.symm i).1, fun i => H (eN.symm i).1,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · beta_reduce
    -- loops: embeddings onto whole frontier components
    intro i
    obtain ⟨hemb', hr, hcl⟩ := hκ' (eC.symm i).1 (eC.symm i).2
    refine ⟨hemb', ?_⟩
    rw [hr]
    exact hcomp _ hcl _ (by rw [← hr]; exact ⟨1, rfl⟩)
  · beta_reduce
    -- lines: proper embeddings onto whole frontier components
    intro i
    obtain ⟨hemb', hprop, hr, -, hcl⟩ := hρ' (eN.symm i).1 (eN.symm i).2
    refine ⟨hemb', hprop, ?_⟩
    rw [hr]
    exact hcomp _ hcl _ (by rw [← hr]; exact ⟨0, rfl⟩)
  · beta_reduce
    -- primitive noncentral generators
    intro i
    have hj := (eN.symm i).2
    obtain ⟨-, -, -, hper, -⟩ := hρ' (eN.symm i).1 hj
    exact ⟨hHΓ _, fun h => hj (Or.inl h), fun h => hj (Or.inr h), hper⟩
  · beta_reduce
    -- loop orbits are distinct and loops have trivial stabilizers
    rintro i i' γ hγ ⟨x, ⟨y, hy, rfl⟩, hx⟩
    obtain ⟨-, hr, -⟩ := hκ' (eC.symm i).1 (eC.symm i).2
    obtain ⟨-, hr', -⟩ := hκ' (eC.symm i').1 (eC.symm i').2
    rw [hr] at hy
    rw [hr'] at hx
    obtain ⟨t, rfl⟩ := hy
    obtain ⟨t', ht'⟩ := hx
    have hjj := hcross _ _ γ hγ t t' ht'.symm
    have hii : eC.symm i = eC.symm i' := Subtype.ext hjj
    refine ⟨eC.symm.injective hii, ?_⟩
    rw [← hjj] at ht'
    obtain ⟨q, -, hq⟩ := hrig _ γ hγ t' t ht'.symm
    rcases hpmpow _ q (eC.symm i).2 with h | h
    · rcases hq with hq | hq
      · exact Or.inl (hq.trans h)
      · exact Or.inr (by rw [hq, h])
    · rcases hq with hq | hq
      · exact Or.inr (hq.trans h)
      · exact Or.inl (by rw [hq, h, neg_neg])
  · beta_reduce
    -- line orbits are distinct and line stabilizers are exactly ±h^k
    rintro i i' γ hγ ⟨x, ⟨y, hy, rfl⟩, hx⟩
    obtain ⟨-, -, hr, -, -⟩ := hρ' (eN.symm i).1 (eN.symm i).2
    obtain ⟨-, -, hr', -, -⟩ := hρ' (eN.symm i').1 (eN.symm i').2
    rw [hr] at hy
    rw [hr'] at hx
    obtain ⟨t, rfl⟩ := hy
    obtain ⟨t', ht'⟩ := hx
    have hjj := hcross _ _ γ hγ t t' ht'.symm
    have hii : eN.symm i = eN.symm i' := Subtype.ext hjj
    refine ⟨eN.symm.injective hii, ?_⟩
    rw [← hjj] at ht'
    obtain ⟨q, -, hq⟩ := hrig _ γ hγ t' t ht'.symm
    exact ⟨q, hq⟩
  · beta_reduce
    -- no translate of a loop meets a line
    intro i i' γ hγ
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hx
    obtain ⟨-, hr, -⟩ := hκ' (eC.symm i).1 (eC.symm i).2
    obtain ⟨-, -, hr', -, -⟩ := hρ' (eN.symm i').1 (eN.symm i').2
    rw [hr] at hy
    rw [hr'] at hx
    obtain ⟨t, rfl⟩ := hy
    obtain ⟨t', ht'⟩ := hx
    have hjj := hcross _ _ γ hγ t t' ht'.symm
    have h1 := (eC.symm i).2
    rw [hjj] at h1
    exact (eN.symm i').2 h1
  · beta_reduce
    -- the frontier is exhausted by the translated loops and lines
    apply Subset.antisymm
    · rw [hcov]
      intro x hx
      obtain ⟨γ, hγ, hx⟩ := mem_iUnion₂.1 hx
      obtain ⟨i, hx⟩ := mem_iUnion.1 hx
      obtain ⟨_, ⟨s, rfl⟩, rfl⟩ := hx
      obtain ⟨⟨j, p⟩, hp, -⟩ := huniq i
      obtain ⟨γ', hγ', he⟩ := harc j p p.2 s
      have hxe : γ • a i s = (γ * γ') • c j (((p : ℕ) : ℝ) + s) := by
        rw [mul_smul, ← he, hp]
      by_cases hP : H j = 1 ∨ H j = -1
      · left
        obtain ⟨-, hr, -⟩ := hκ' j hP
        have hm : c j (((p : ℕ) : ℝ) + s) ∈ Set.range (κ' j) := by rw [hr]; exact ⟨_, rfl⟩
        obtain ⟨z, hz⟩ := hm
        refine mem_iUnion₂.2 ⟨γ * γ', mul_mem hγ hγ', mem_iUnion.2 ⟨eC ⟨j, hP⟩, ?_⟩⟩
        refine ⟨c j (((p : ℕ) : ℝ) + s), ⟨z, ?_⟩, hxe.symm⟩
        rw [Equiv.symm_apply_apply]
        exact hz
      · right
        obtain ⟨-, -, hr, -, -⟩ := hρ' j hP
        have hm : c j (((p : ℕ) : ℝ) + s) ∈ Set.range (ρ' j) := by rw [hr]; exact ⟨_, rfl⟩
        obtain ⟨z, hz⟩ := hm
        refine mem_iUnion₂.2 ⟨γ * γ', mul_mem hγ hγ', mem_iUnion.2 ⟨eN ⟨j, hP⟩, ?_⟩⟩
        refine ⟨c j (((p : ℕ) : ℝ) + s), ⟨z, ?_⟩, hxe.symm⟩
        rw [Equiv.symm_apply_apply]
        exact hz
    · rintro x (hx | hx)
      · obtain ⟨γ, hγ, hx⟩ := mem_iUnion₂.1 hx
        obtain ⟨i, hx⟩ := mem_iUnion.1 hx
        obtain ⟨_, ⟨z, rfl⟩, rfl⟩ := hx
        obtain ⟨-, hr, -⟩ := hκ' (eC.symm i).1 (eC.symm i).2
        have hz : κ' (eC.symm i).1 z ∈ Set.range (c (eC.symm i).1) := by rw [← hr]; exact ⟨z, rfl⟩
        obtain ⟨t, ht⟩ := hz
        show γ • κ' (eC.symm i).1 z ∈ frontier U
        rw [← ht]
        exact hfrI γ hγ _ (hcF _ t)
      · obtain ⟨γ, hγ, hx⟩ := mem_iUnion₂.1 hx
        obtain ⟨i, hx⟩ := mem_iUnion.1 hx
        obtain ⟨_, ⟨z, rfl⟩, rfl⟩ := hx
        obtain ⟨-, -, hr, -, -⟩ := hρ' (eN.symm i).1 (eN.symm i).2
        have hz : ρ' (eN.symm i).1 z ∈ Set.range (c (eN.symm i).1) := by rw [← hr]; exact ⟨z, rfl⟩
        obtain ⟨t, ht⟩ := hz
        show γ • ρ' (eN.symm i).1 z ∈ frontier U
        rw [← ht]
        exact hfrI γ hγ _ (hcF _ t)
  · beta_reduce
    -- each generator is the ordered least-return word of its cycle
    intro i
    set j := (eN.symm i).1
    exact ⟨r j, ell j, (hcyc j).1, (hcyc j).2.1, (hcyc j).2.2, hHdef j⟩

end LiZhongQC
