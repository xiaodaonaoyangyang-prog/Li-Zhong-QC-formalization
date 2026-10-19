import LiZhongQC.Lemmas.FoundationSmallSupport
import LiZhongQC.Lemmas.StrebelDoubleDomain
import LiZhongQC.Lemmas.F1AssemblySupport
import LiZhongQC.Lemmas.S36BersOrdinary

/-! Cusp-family package 001: genuine parabolic endpoints, equality of overlapping
translated horoballs, spherical boundary avoidance, and the full ordinary-set adapter.
Source-only. Import the existing numerical estimate; do not export it twice. -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- An infinite-order group element fixing a spherical point puts that point in the
literal orbit-limit definition. Injectivity of the powers is essential: no finite stabilizer is used. -/
theorem ft1fas_infinite_fixed_point_limit (g : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hg : g ∈ Γ) (hinj : Function.Injective (fun n : ℕ => g ^ n))
    (p : ExtPlane) (hfix : mobiusSL (slRealToComplex g) p = p) :
    p ∈ fuchsianLimitSet Γ := by
  let seq : ℕ → Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) := fun n =>
    ⟨slRealToComplex (g ^ n), Subgroup.mem_map.mpr ⟨g ^ n, Γ.pow_mem hg n, rfl⟩⟩
  have hseq : Function.Injective seq := by
    intro m n heq
    apply hinj
    ext i j
    have hentry := congrArg
      (fun q : Γ.map (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) =>
        (q.1 : Matrix (Fin 2) (Fin 2) ℂ) i j) heq
    simp only [seq, slRealToComplex, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply] at hentry
    exact_mod_cast hentry
  have hpowers : ∀ n : ℕ, mobiusSL (slRealToComplex (g ^ n)) p = p := by
    intro n
    induction n with
    | zero => simpa only [pow_zero, slRealToComplex, map_one] using k24_mobiusSL_one p
    | succ n ih =>
      have hmap : slRealToComplex (g ^ n * g) =
          slRealToComplex (g ^ n) * slRealToComplex g :=
        map_mul (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) _ _
      rw [pow_succ, hmap, k24_mobiusSL_mul, hfix, ih]
  refine ⟨p, seq, hseq, ?_⟩
  exact tendsto_const_nhds.congr fun n => (hpowers n).symm

/-- A normalized cusp fixed point is a genuine limit point, by its distinct translation orbit.
Kept separate from the hyperbolic case so zero funnel indices require no dummy element. -/
theorem ft1fas_parabolic_endpoint_limit (hΓ : IsFuchsian Γ)
    (A π₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hπ : π₀ ∈ Γ)
    (htrans : ∀ τ : UpperHalfPlane, π₀ • (A • τ) = A • ((1 : ℝ) +ᵥ τ)) :
    mobiusSL (slRealToComplex A) extInf ∈ fuchsianLimitSet Γ := by
  have _ := hΓ
  have hinj : Function.Injective (fun n : ℕ => π₀ ^ n) := by
    intro m n hmn
    have hm : π₀ ^ m • (A • UpperHalfPlane.I) = A • ((m : ℝ) +ᵥ UpperHalfPlane.I) := by
      simpa only [zpow_natCast, Int.cast_natCast] using
        ft1e_zpow_smul htrans (m : ℤ) UpperHalfPlane.I
    have hn : π₀ ^ n • (A • UpperHalfPlane.I) = A • ((n : ℝ) +ᵥ UpperHalfPlane.I) := by
      simpa only [zpow_natCast, Int.cast_natCast] using
        ft1e_zpow_smul htrans (n : ℤ) UpperHalfPlane.I
    have heq := congrArg (fun q : Matrix.SpecialLinearGroup (Fin 2) ℝ =>
      q • (A • UpperHalfPlane.I)) hmn
    rw [hm, hn] at heq
    have hre : (m : ℝ) = (n : ℝ) := by
      simpa using congrArg (fun τ : UpperHalfPlane => τ.re) (smul_left_cancel A heq)
    exact_mod_cast hre
  let N : Matrix.SpecialLinearGroup (Fin 2) ℝ := A⁻¹ * π₀ * A
  have hN : ∀ τ : UpperHalfPlane, N • τ = (1 : ℝ) +ᵥ τ := by
    intro τ
    dsimp only [N]
    rw [mul_smul, mul_smul, htrans, inv_smul_smul]
  have hNfix : mobiusSL (slRealToComplex N) extInf = extInf :=
    (s36a_mextinf N).2 (ft1e_translation_entries hN).1
  have hmul : slRealToComplex π₀ * slRealToComplex A =
      slRealToComplex A * slRealToComplex N := by
    change (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) π₀ *
        (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) A =
      (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) A *
        (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ)) N
    rw [← map_mul, ← map_mul]
    congr 1
    dsimp only [N]
    group
  apply ft1fas_infinite_fixed_point_limit π₀ hπ hinj
  rw [← k24_mobiusSL_mul, hmul, k24_mobiusSL_mul, hNfix]

/-- Two translated height-one cusp horoballs which meet are literally equal.
The proof uses the full signed primitive-power conclusion, not only equality of cusp indices. -/
theorem ft1fas_cusp_horoballs_eq_of_meet {n : ℕ}
    (A π₀ : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hcusp : ∀ i, π₀ i ∈ Γ ∧ ∀ τ : UpperHalfPlane,
      π₀ i • (A i • τ) = A i • ((1 : ℝ) +ᵥ τ))
    (hpc : ∀ i i' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im →
      1 < ((A i')⁻¹ • (γ • (A i • τ))).im →
      i = i' ∧ ∃ k : ℤ, γ = π₀ i ^ k ∨ γ = -π₀ i ^ k)
    (γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hγ : γ ∈ Γ) (hδ : δ ∈ Γ)
    (i j : Fin n)
    (hmeet : (((fun τ : UpperHalfPlane => γ • (A i • τ)) '' {τ | 1 < τ.im}) ∩
      ((fun τ : UpperHalfPlane => δ • (A j • τ)) '' {τ | 1 < τ.im})).Nonempty) :
    (fun τ : UpperHalfPlane => γ • (A i • τ)) '' {τ | 1 < τ.im} =
      (fun τ : UpperHalfPlane => δ • (A j • τ)) '' {τ | 1 < τ.im} := by
  obtain ⟨z, hzγ, hzδ⟩ := hmeet
  obtain ⟨u, hu, huz⟩ := hzγ
  obtain ⟨v, hv, hvz⟩ := hzδ
  have huz' : γ • (A i • u) = z := huz
  have hvz' : δ • (A j • v) = z := hvz
  have heq : (A j)⁻¹ • ((δ⁻¹ * γ) • (A i • u)) = v := by
    rw [mul_smul, huz', ← hvz', inv_smul_smul, inv_smul_smul]
  obtain ⟨hij, k, hk⟩ := hpc i j (δ⁻¹ * γ) (Γ.mul_mem (Γ.inv_mem hδ) hγ)
    u hu (by rw [heq]; exact hv)
  subst j
  have haction : ∀ τ : UpperHalfPlane,
      γ • (A i • τ) = δ • (A i • ((k : ℝ) +ᵥ τ)) := by
    intro τ
    calc γ • (A i • τ) = δ • ((δ⁻¹ * γ) • (A i • τ)) := by
          simp only [mul_smul, smul_inv_smul]
      _ = δ • (A i • ((k : ℝ) +ᵥ τ)) := by
          rcases hk with h | h
          · rw [h, ft1e_zpow_smul (hcusp i).2]
          · rw [h, s30l_neg_smul, ft1e_zpow_smul (hcusp i).2]
  ext w
  constructor
  · intro hw
    obtain ⟨τ, hτ, hτw⟩ := hw
    refine ⟨(k : ℝ) +ᵥ τ, ?_, (haction τ).symm.trans hτw⟩
    simpa using hτ
  · intro hw
    obtain ⟨τ, hτ, hτw⟩ := hw
    refine ⟨(-(k : ℝ)) +ᵥ τ, ?_, ?_⟩
    · simpa using hτ
    · show γ • (A i • ((-(k : ℝ)) +ᵥ τ)) = w
      rw [haction, vadd_vadd, add_neg_cancel, zero_vadd]
      exact hτw

/-- The inverse-image height test for an actual determinant-one horoball, in real
coordinates. The positive denominator is proved on the upper half-plane. -/
theorem ft1fas_horoball_mem_iff (M : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (z : UpperHalfPlane) :
    z ∈ (fun τ : UpperHalfPlane => M • τ) '' {τ : UpperHalfPlane | 1 < τ.im} ↔
      (M 0 0 - M 1 0 * z.re) ^ 2 + (M 1 0 * z.im) ^ 2 < z.im := by
  have h10 : M⁻¹ 1 0 = -M 1 0 := (s36a_inv_entries M).2
  have h11 : M⁻¹ 1 1 = M 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have hnorm : Complex.normSq ((M⁻¹ 1 0 : ℂ) * (z : ℂ) + M⁻¹ 1 1) =
      (M 0 0 - M 1 0 * z.re) ^ 2 + (M 1 0 * z.im) ^ 2 := by
    rw [h10, h11]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hpos : 0 < (M 0 0 - M 1 0 * z.re) ^ 2 + (M 1 0 * z.im) ^ 2 := by
    rw [← hnorm]
    exact Complex.normSq_pos.mpr (h36t_den_ne M⁻¹ z)
  have him : (M⁻¹ • z).im = z.im /
      ((M 0 0 - M 1 0 * z.re) ^ 2 + (M 1 0 * z.im) ^ 2) := by
    change (((M⁻¹ • z : UpperHalfPlane) : ℂ)).im = _
    rw [h36t_coe_smul, utm_im_mobius (k24_det_realR M⁻¹), hnorm, UpperHalfPlane.coe_im]
  have hmem : z ∈ (fun τ : UpperHalfPlane => M • τ) '' {τ : UpperHalfPlane | 1 < τ.im} ↔
      1 < (M⁻¹ • z).im := by
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      simpa only [inv_smul_smul, Set.mem_setOf_eq] using hτ
    · intro hz
      exact ⟨M⁻¹ • z, hz, smul_inv_smul M z⟩
  rw [hmem, him, lt_div_iff₀ hpos, one_mul]

/-- Finite-coordinate part of horoball avoidance. A closed set of ideal endpoints
separates their coefficients uniformly; all horoballs entering the resulting box
contain one common interior point, and hence are identical. -/
theorem ft1fas_horoball_family_finite_avoid {ι : Type*}
    (M : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (K : Set ExtPlane) (hK : IsClosed K)
    (hend : ∀ i, mobiusSL (slRealToComplex (M i)) extInf ∈ K)
    (hpair : ∀ i j,
      (((fun τ : UpperHalfPlane => M i • τ) '' {τ : UpperHalfPlane | 1 < τ.im}) ∩
        ((fun τ : UpperHalfPlane => M j • τ) '' {τ : UpperHalfPlane | 1 < τ.im})).Nonempty →
      (fun τ : UpperHalfPlane => M i • τ) '' {τ : UpperHalfPlane | 1 < τ.im} =
        (fun τ : UpperHalfPlane => M j • τ) '' {τ : UpperHalfPlane | 1 < τ.im})
    (x : ℝ) (hxK : ((x : ℂ) : ExtPlane) ∉ K) :
    ∃ V : Set ExtPlane, IsOpen V ∧ ((x : ℂ) : ExtPlane) ∈ V ∧
      Disjoint V {p : ExtPlane | ∃ i : ι, ∃ τ : UpperHalfPlane,
        1 < τ.im ∧ p = (((M i • τ : UpperHalfPlane) : ℂ) : ExtPlane)} := by
  classical
  have hopen : IsOpen {t : ℝ | ((t : ℂ) : ExtPlane) ∉ K} :=
    hK.isOpen_compl.preimage (OnePoint.continuous_coe.comp Complex.continuous_ofReal)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hxK)
  have hsep : ∀ i, ε * |M i 1 0| ≤ |M i 0 0 - M i 1 0 * x| := by
    intro i
    by_cases hc : M i 1 0 = 0
    · simpa only [hc, abs_zero, mul_zero, zero_mul, sub_zero] using abs_nonneg (M i 0 0)
    · have hout : ¬ |M i 0 0 / M i 1 0 - x| < ε := by
        intro hlt
        have hk := hend i
        change mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) (M i)) extInf ∈ K at hk
        rw [(s36a_mextinf (M i)).1 hc] at hk
        exact hball (by simpa only [Metric.mem_ball, Real.dist_eq] using hlt) hk
      have hdiv : (M i 0 0 - M i 1 0 * x) / M i 1 0 = M i 0 0 / M i 1 0 - x := by
        field_simp [hc]
        <;> ring
      have hle : ε ≤ |M i 0 0 - M i 1 0 * x| / |M i 1 0| := by
        rw [← abs_div, hdiv]
        exact le_of_not_gt hout
      exact (le_div_iff₀ (abs_pos.mpr hc)).mp hle
  have hnonzero : ∀ i, M i 0 0 - M i 1 0 * x ≠ 0 := by
    intro i heq
    by_cases hc : M i 1 0 = 0
    · have ha : M i 0 0 = 0 := by simpa only [hc, zero_mul, sub_zero] using heq
      have hd := k24_det_realR (M i)
      rw [ha, hc] at hd
      norm_num at hd
    · have hh := hsep i
      rw [heq, abs_zero] at hh
      exact (not_le_of_gt (mul_pos hε (abs_pos.mpr hc))) hh
  let U : Set ℂ := {z | |z.re - x| < ε / 2 ∧ 8 * z.im < ε}
  have hUo : IsOpen U := by
    show IsOpen ({z : ℂ | |z.re - x| < ε / 2} ∩ {z : ℂ | 8 * z.im < ε})
    exact (isOpen_lt (Complex.continuous_re.sub continuous_const).abs continuous_const).inter
      (isOpen_lt (continuous_const.mul Complex.continuous_im) continuous_const)
  have hxU : (x : ℂ) ∈ U := by
    change |(x : ℂ).re - x| < ε / 2 ∧ 8 * (x : ℂ).im < ε
    simp only [Complex.ofReal_re, Complex.ofReal_im, sub_self, abs_zero, mul_zero]
    exact ⟨by linarith, hε⟩
  let w : UpperHalfPlane := ⟨(x : ℂ) + (ε : ℂ) * Complex.I, by simpa using hε⟩
  have hwre : w.re = x := by simp [w]
  have hwim : w.im = ε := by simp [w]
  have hcommon : ∀ i (z : UpperHalfPlane), (z : ℂ) ∈ U →
      z ∈ (fun τ : UpperHalfPlane => M i • τ) '' {τ : UpperHalfPlane | 1 < τ.im} →
      w ∈ (fun τ : UpperHalfPlane => M i • τ) '' {τ : UpperHalfPlane | 1 < τ.im} := by
    intro i z hzU hz
    apply (ft1fas_horoball_mem_iff (M i) w).mpr
    rw [hwre, hwim]
    exact ft1fas_horoball_common_point hε z.im_pos hzU.2 hzU.1 (hsep i)
      ((ft1fas_horoball_mem_iff (M i) z).mp hz)
  by_cases hhit : ∃ (i : ι) (z : UpperHalfPlane), (z : ℂ) ∈ U ∧
      z ∈ (fun τ : UpperHalfPlane => M i • τ) '' {τ : UpperHalfPlane | 1 < τ.im}
  · obtain ⟨i₀, z₀, hz₀U, hz₀⟩ := hhit
    have hw₀ := hcommon i₀ z₀ hz₀U hz₀
    let P : Set ℂ := {z | z.im < (M i₀ 0 0 - M i₀ 1 0 * z.re) ^ 2 +
      (M i₀ 1 0 * z.im) ^ 2}
    have hPo : IsOpen P := by
      show IsOpen {z : ℂ | z.im < (M i₀ 0 0 - M i₀ 1 0 * z.re) ^ 2 + (M i₀ 1 0 * z.im) ^ 2}
      exact isOpen_lt Complex.continuous_im (by fun_prop)
    have hxP : (x : ℂ) ∈ P := by
      change (x : ℂ).im < (M i₀ 0 0 - M i₀ 1 0 * (x : ℂ).re) ^ 2 +
        (M i₀ 1 0 * (x : ℂ).im) ^ 2
      rw [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_pow two_ne_zero, add_zero]
      exact sq_pos_of_ne_zero (hnonzero i₀)
    refine ⟨((↑) : ℂ → ExtPlane) '' (U ∩ P),
      OnePoint.isOpen_image_coe.mpr (hUo.inter hPo), ⟨(x : ℂ), ⟨hxU, hxP⟩, rfl⟩, ?_⟩
    apply Set.disjoint_left.mpr
    intro p hp hpf
    obtain ⟨z, hz, hzp⟩ := hp
    obtain ⟨i, τ, hτ, hpτ⟩ := hpf
    have heq : z = ((M i • τ : UpperHalfPlane) : ℂ) :=
      OnePoint.coe_injective (hzp.trans hpτ)
    have hτU : (((M i • τ : UpperHalfPlane) : ℂ)) ∈ U := heq ▸ hz.1
    have hτmem : M i • τ ∈
        (fun τ : UpperHalfPlane => M i • τ) '' {τ : UpperHalfPlane | 1 < τ.im} :=
      ⟨τ, hτ, rfl⟩
    have hsame := hpair i i₀ ⟨w, hcommon i (M i • τ) hτU hτmem, hw₀⟩
    have hineq := (ft1fas_horoball_mem_iff (M i₀) (M i • τ)).mp (hsame ▸ hτmem)
    have hzP := hz.2
    change z.im < (M i₀ 0 0 - M i₀ 1 0 * z.re) ^ 2 + (M i₀ 1 0 * z.im) ^ 2 at hzP
    rw [heq] at hzP
    exact (not_lt_of_ge hineq.le) hzP
  · refine ⟨((↑) : ℂ → ExtPlane) '' U, OnePoint.isOpen_image_coe.mpr hUo,
      ⟨(x : ℂ), hxU, rfl⟩, ?_⟩
    apply Set.disjoint_left.mpr
    intro p hp hpf
    obtain ⟨z, hz, hzp⟩ := hp
    obtain ⟨i, τ, hτ, hpτ⟩ := hpf
    have heq := OnePoint.coe_injective (hzp.trans hpτ)
    exact hhit ⟨i, M i • τ, heq ▸ hz, ⟨τ, hτ, rfl⟩⟩

/-- A disjoint-or-identical family of actual Mobius horoballs accumulates on the real
sphere only in the closure of its ideal tangency points. The numerical common-point
estimate handles finite boundary coordinates; real Mobius inversion handles infinity. -/
theorem ft1fas_horoball_family_boundary_avoid {ι : Type*}
    (M : ι → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (K : Set ExtPlane) (hK : IsClosed K) (hKR : K ⊆ extRealLine)
    (hend : ∀ i, mobiusSL (slRealToComplex (M i)) extInf ∈ K)
    (hpair : ∀ i j,
      (((fun τ : UpperHalfPlane => M i • τ) '' {τ : UpperHalfPlane | 1 < τ.im}) ∩
        ((fun τ : UpperHalfPlane => M j • τ) '' {τ : UpperHalfPlane | 1 < τ.im})).Nonempty →
      (fun τ : UpperHalfPlane => M i • τ) '' {τ : UpperHalfPlane | 1 < τ.im} =
        (fun τ : UpperHalfPlane => M j • τ) '' {τ : UpperHalfPlane | 1 < τ.im})
    (x : ExtPlane) (hxR : x ∈ extRealLine) (hxK : x ∉ K) :
    ∃ V : Set ExtPlane, IsOpen V ∧ x ∈ V ∧
      Disjoint V {p : ExtPlane | ∃ i : ι, ∃ τ : UpperHalfPlane,
        1 < τ.im ∧ p = (((M i • τ : UpperHalfPlane) : ℂ) : ExtPlane)} := by
  -- The argument only needs closedness and containment of all ideal endpoints.
  have _ := hKR
  obtain ⟨B, hBx⟩ := s27l_exists_to_infty hxR
  let J : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    ⟨!![0, -1; 1, 0], by norm_num [Matrix.det_fin_two_of]⟩
  have hJ : mobiusSL (slRealToComplex J) extInf = ((0 : ℂ) : ExtPlane) := by
    change mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) J) extInf = ((0 : ℂ) : ExtPlane)
    simpa [J] using (s36a_mextinf J).1 (by norm_num [J])
  let T := J * B
  have hTx : mobiusSL (slRealToComplex T) x = ((0 : ℂ) : ExtPlane) := by
    rw [show T = J * B from rfl, k24_slReal_mul, k24_mobiusSL_mul, hBx, hJ]
  have hinv : ∀ p : ExtPlane,
      mobiusSL (slRealToComplex T⁻¹) (mobiusSL (slRealToComplex T) p) = p := by
    intro p
    rw [k24_slReal_inv, k24_mobiusSL_inv_apply]
  let K' : Set ExtPlane := mobiusSL (slRealToComplex T⁻¹) ⁻¹' K
  have hK' : IsClosed K' := hK.preimage (k22_t_continuous _)
  have hxK' : ((0 : ℂ) : ExtPlane) ∉ K' := by
    change mobiusSL (slRealToComplex T⁻¹) ((0 : ℂ) : ExtPlane) ∉ K
    rw [← hTx, hinv]
    exact hxK
  have hend' : ∀ i, mobiusSL (slRealToComplex (T * M i)) extInf ∈ K' := by
    intro i
    change mobiusSL (slRealToComplex T⁻¹)
      (mobiusSL (slRealToComplex (T * M i)) extInf) ∈ K
    rw [k24_slReal_mul, k24_mobiusSL_mul, hinv]
    exact hend i
  have hpair' : ∀ i j,
      (((fun τ : UpperHalfPlane => (T * M i) • τ) '' {τ : UpperHalfPlane | 1 < τ.im}) ∩
        ((fun τ : UpperHalfPlane => (T * M j) • τ) '' {τ : UpperHalfPlane | 1 < τ.im})).Nonempty →
      (fun τ : UpperHalfPlane => (T * M i) • τ) '' {τ : UpperHalfPlane | 1 < τ.im} =
        (fun τ : UpperHalfPlane => (T * M j) • τ) '' {τ : UpperHalfPlane | 1 < τ.im} := by
    intro i j hij
    obtain ⟨z, ⟨u, hu, huz⟩, ⟨v, hv, hvz⟩⟩ := hij
    have huz' : (T * M i) • u = z := huz
    have hvz' : (T * M j) • v = z := hvz
    have huinv : M i • u = T⁻¹ • z := by rw [← huz', mul_smul, inv_smul_smul]
    have hvinv : M j • v = T⁻¹ • z := by rw [← hvz', mul_smul, inv_smul_smul]
    have heq := hpair i j ⟨T⁻¹ • z, ⟨u, hu, huinv⟩, ⟨v, hv, hvinv⟩⟩
    have hi : (fun τ : UpperHalfPlane => (T * M i) • τ) '' {τ : UpperHalfPlane | 1 < τ.im} =
        (fun z : UpperHalfPlane => T • z) ''
          ((fun τ : UpperHalfPlane => M i • τ) '' {τ : UpperHalfPlane | 1 < τ.im}) := by
      rw [Set.image_image]
      congr 1
      funext τ
      exact mul_smul T (M i) τ
    have hj : (fun τ : UpperHalfPlane => (T * M j) • τ) '' {τ : UpperHalfPlane | 1 < τ.im} =
        (fun z : UpperHalfPlane => T • z) ''
          ((fun τ : UpperHalfPlane => M j • τ) '' {τ : UpperHalfPlane | 1 < τ.im}) := by
      rw [Set.image_image]
      congr 1
      funext τ
      exact mul_smul T (M j) τ
    rw [hi, hj, heq]
  obtain ⟨V, hVo, hV0, hVdisj⟩ := ft1fas_horoball_family_finite_avoid
    (fun i => T * M i) K' hK' hend' hpair' 0 (by simpa only [Complex.ofReal_zero] using hxK')
  refine ⟨mobiusSL (slRealToComplex T) ⁻¹' V,
    hVo.preimage (k22_t_continuous _), ?_, ?_⟩
  · change mobiusSL (slRealToComplex T) x ∈ V
    rw [hTx]
    simpa only [Complex.ofReal_zero] using hV0
  · apply Set.disjoint_left.mpr
    intro p hp hpf
    obtain ⟨i, τ, hτ, rfl⟩ := hpf
    apply Set.disjoint_left.mp hVdisj hp
    refine ⟨i, τ, hτ, ?_⟩
    rw [h36t_mobiusSL_coe]
    simp only [T, mul_smul]

/-- Expanded height-one cusp families stay away from a compact subset of the ordinary
boundary. The statement controls all group translates, not a selected finite subfamily. -/
theorem ft1fas_cusp_family_avoids_ordinary_compact (hΓ : IsFuchsian Γ) {n : ℕ}
    (A π₀ : Fin n → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hcusp : ∀ i, π₀ i ∈ Γ ∧ ∀ τ : UpperHalfPlane,
      π₀ i • (A i • τ) = A i • ((1 : ℝ) +ᵥ τ))
    (hpc : ∀ i i' γ, γ ∈ Γ → ∀ τ : UpperHalfPlane, 1 < τ.im →
      1 < ((A i')⁻¹ • (γ • (A i • τ))).im →
      i = i' ∧ ∃ k : ℤ, γ = π₀ i ^ k ∨ γ = -π₀ i ^ k)
    (L : Set ExtPlane) (hL : IsCompact L) (hLord : L ⊆ ordinarySet Γ) :
    ∃ V : Set ExtPlane, IsOpen V ∧ L ⊆ V ∧
      Disjoint V {p : ExtPlane | ∃ γ ∈ Γ, ∃ i : Fin n, ∃ τ : UpperHalfPlane,
        1 < τ.im ∧ p = (((γ • (A i • τ) : UpperHalfPlane) : ℂ) : ExtPlane)} := by
  classical
  -- Pointwise avoidance gives an open union for any ordinary subset; compactness
  -- is retained in the frozen contract for its compact-fundamental-arc consumer.
  have _ := hL
  let M : (Γ × Fin n) → Matrix.SpecialLinearGroup (Fin 2) ℝ := fun q => q.1.1 * A q.2
  have hend : ∀ q, mobiusSL (slRealToComplex (M q)) extInf ∈ fuchsianLimitSet Γ := by
    intro q
    change mobiusSL (slRealToComplex (q.1.1 * A q.2)) extInf ∈ fuchsianLimitSet Γ
    rw [k24_slReal_mul, k24_mobiusSL_mul]
    exact k22_t_limitSet_smul (Subgroup.mem_map_of_mem _ q.1.2)
      (ft1fas_parabolic_endpoint_limit hΓ (A q.2) (π₀ q.2) (hcusp q.2).1 (hcusp q.2).2)
  have hpair : ∀ q r,
      (((fun τ : UpperHalfPlane => M q • τ) '' {τ : UpperHalfPlane | 1 < τ.im}) ∩
        ((fun τ : UpperHalfPlane => M r • τ) '' {τ : UpperHalfPlane | 1 < τ.im})).Nonempty →
      (fun τ : UpperHalfPlane => M q • τ) '' {τ : UpperHalfPlane | 1 < τ.im} =
        (fun τ : UpperHalfPlane => M r • τ) '' {τ : UpperHalfPlane | 1 < τ.im} := by
    intro q r hmeet
    simpa only [M, mul_smul] using ft1fas_cusp_horoballs_eq_of_meet A π₀ hcusp hpc
      q.1.1 r.1.1 q.1.2 r.1.2 q.2 r.2 (by simpa only [M, mul_smul] using hmeet)
  let S : Set ExtPlane := {p | ∃ γ ∈ Γ, ∃ i : Fin n, ∃ τ : UpperHalfPlane,
    1 < τ.im ∧ p = (((γ • (A i • τ) : UpperHalfPlane) : ℂ) : ExtPlane)}
  have hpoint : ∀ x ∈ L, ∃ V : Set ExtPlane, IsOpen V ∧ x ∈ V ∧ Disjoint V S := by
    intro x hx
    obtain ⟨V, hVo, hxV, hdisj⟩ := ft1fas_horoball_family_boundary_avoid M
      (fuchsianLimitSet Γ) (s36x_limitSet_closed hΓ) (s36a_limit_real hΓ) hend hpair x
      (hLord hx).1 (hLord hx).2
    refine ⟨V, hVo, hxV, Set.disjoint_left.mpr ?_⟩
    intro p hp hpS
    obtain ⟨γ, hγ, i, τ, hτ, hpτ⟩ := hpS
    apply Set.disjoint_left.mp hdisj hp
    refine ⟨(⟨γ, hγ⟩, i), τ, hτ, ?_⟩
    simpa only [M, mul_smul] using hpτ
  let V : Set ExtPlane := ⋃ U : {U : Set ExtPlane // IsOpen U ∧ Disjoint U S}, U.1
  refine ⟨V, isOpen_iUnion (fun U => U.2.1), ?_, Set.disjoint_left.mpr ?_⟩
  · intro x hx
    obtain ⟨U, hUo, hxU, hUS⟩ := hpoint x hx
    exact Set.mem_iUnion.mpr ⟨⟨U, hUo, hUS⟩, hxU⟩
  · intro p hp hpS
    obtain ⟨U, hpU⟩ := Set.mem_iUnion.mp hp
    exact Set.disjoint_left.mp U.2.2 hpU hpS

end LiZhongQC
