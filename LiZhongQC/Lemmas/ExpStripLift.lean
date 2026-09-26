import LiZhongQC.Lemmas.CanonicalForm
import LiZhongQC.Lemmas.Conformal
import LiZhongQC.Lemmas.Mobius
import LiZhongQC.Lemmas.ExpStripBasic
import LiZhongQC.Lemmas.StripAutomorphism

/-!
# `expStrip A` is conformally onto some strip (Theorem 2.1 case (iii), piece B)
-/


open Complex Set Metric Filter Topology Bornology
open scoped ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ### Step 0: basic facts about `expStrip` (def + isOpen_expStrip now in ExpStripBasic) -/

theorem one_lt_norm_exp_iff (z : ℂ) : 1 < ‖Complex.exp z‖ ↔ 0 < z.re := by
  rw [Complex.norm_exp, ← Real.exp_zero]
  exact Real.exp_lt_exp

theorem expStrip_eq_preimage_diff (A : Set ℂ) :
    expStrip A = Complex.exp ⁻¹' (A \ closedBall (0:ℂ) 1) := by
  ext z
  simp only [expStrip, mem_setOf_eq, mem_preimage, mem_diff, mem_closedBall, dist_zero_right,
    not_le, ← one_lt_norm_exp_iff]
  tauto

/-! ### Step 1: lifting an arbitrary path along `exp`

Adapted from `S04_ModulusExtremalLength.lean`'s `exists_continuous_arg_lift` (not imported here:
`S04` imports `S02`, and piece B belongs upstream of that).

**KNOWN DUPLICATION, not silent debt**: this is a deliberate copy of `exists_continuous_arg_lift`
at `S04_ModulusExtremalLength.lean:2263`, forced by the import direction (`S04` → `S02`, so a
`Lemmas` file consumed by `S02` cannot import `S04`). Once this lands and `S02`'s case-(iii) sorry
closes, the right cleanup is to relocate `exists_continuous_arg_lift` into a `Lemmas/` file so
`S04` and this leaf share one copy. Do not do that now (mid-build); flagging so the duplication
gets cleaned up deliberately rather than forgotten. -/

theorem exists_continuous_log_lift {γ : ℝ → ℂ} (hc : ContinuousOn γ (Icc 0 1))
    (hne : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ 0) :
    ∃ Γ : ℝ → ℂ, Continuous Γ ∧ ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (Γ t) = γ t := by
  have hne' : ∀ t : unitInterval, (‖γ t‖ : ℂ) ≠ 0 := fun t =>
    ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne t t.2))
  have hmem : ∀ t : unitInterval, γ t / (‖γ t‖ : ℂ) ∈ Submonoid.unitSphere ℂ := fun t =>
    mem_sphere_zero_iff_norm.2 (by
      rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 (hne t t.2))])
  have hcI : Continuous fun t : unitInterval => γ t :=
    hc.comp_continuous continuous_subtype_val fun t => t.2
  let c : C(unitInterval, Circle) :=
    ⟨fun t => ⟨γ t / (‖γ t‖ : ℂ), hmem t⟩,
      Continuous.subtype_mk (hcI.div (continuous_ofReal.comp (continuous_norm.comp hcI)) hne') _⟩
  obtain ⟨Θ, hΘ, -⟩ :=
    Circle.isCoveringMap_exp.exists_path_lifts c (Complex.arg (c 0 : ℂ)) (Circle.exp_arg (c 0)).symm
  have hkey : ∀ x : unitInterval, Complex.exp (Θ x * Complex.I) = γ x / (‖γ (x : ℝ)‖ : ℂ) :=
    fun x => congrArg ((↑) : Circle → ℂ) (congrFun hΘ x)
  have hlogcont : Continuous fun s : unitInterval => (Real.log ‖γ (s : ℝ)‖ : ℂ) := by
    apply Complex.continuous_ofReal.comp
    exact Real.continuousOn_log.comp_continuous (continuous_norm.comp hcI)
      fun s => norm_ne_zero_iff.mpr (hne (s:ℝ) s.2)
  have hFcont : Continuous fun s : unitInterval => (Real.log ‖γ (s : ℝ)‖ : ℂ) + Θ s * Complex.I :=
    hlogcont.add ((Complex.continuous_ofReal.comp Θ.continuous).mul continuous_const)
  refine ⟨fun t => (Real.log ‖γ (projIcc 0 1 zero_le_one t : ℝ)‖ : ℂ) +
      Θ (projIcc 0 1 zero_le_one t) * Complex.I, hFcont.comp continuous_projIcc, fun t ht => ?_⟩
  · simp only [projIcc_of_mem zero_le_one ht]
    have h := hkey (projIcc 0 1 zero_le_one t)
    rw [projIcc_of_mem zero_le_one ht] at h
    have hlogexp : Complex.exp ((Real.log ‖γ t‖ : ℂ)) = (‖γ t‖ : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr (hne t ht))]
    have hn : (‖γ t‖ : ℂ) ≠ 0 := ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne t ht))
    rw [Complex.exp_add, hlogexp, h]
    field_simp

/-! ### Step 2. General form: connectedness of `exp ⁻¹' U`, for `U` open connected avoiding `0`
and containing a full circle of some radius `a`. Reused for BOTH `expStrip A` (with
`U = A \ closedBall 0 1`, `a` near `1`) and the outer piece `exp ⁻¹' Aᶜ` (with `a` large, from
boundedness of `A`). -/

theorem two_pi_mul_I_mem_connectedComponentIn_exp_preimage {U : Set ℂ} {a : ℝ} (ha0 : 0 < a)
    (haU : ∀ t ∈ Icc (0:ℝ) 1, (a:ℂ) * Complex.exp ((t * (2*Real.pi) : ℝ) * Complex.I) ∈ U) :
    ((Real.log a : ℂ) + 2*Real.pi*Complex.I) ∈
      connectedComponentIn (Complex.exp ⁻¹' U) (Real.log a : ℂ) := by
  set z0 : ℂ := (Real.log a : ℂ) with hz0
  set Γ : ℝ → ℂ := fun t => z0 + (t:ℂ) * (2*Real.pi*Complex.I) with hΓ
  have hexpz0 : Complex.exp z0 = (a : ℂ) := by
    rw [hz0, ← Complex.ofReal_exp, Real.exp_log ha0]
  have hcont : Continuous Γ := by
    apply Continuous.add continuous_const
    exact Complex.continuous_ofReal.mul continuous_const
  have hsub : Γ '' (Icc (0:ℝ) 1) ⊆ Complex.exp ⁻¹' U := by
    rintro w ⟨t, ht, rfl⟩
    show Complex.exp (z0 + (t:ℂ) * (2*Real.pi*Complex.I)) ∈ U
    have hcast : (t:ℂ) * (2*Real.pi*Complex.I) = ((t * (2*Real.pi) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    have heq : Complex.exp (z0 + (t:ℂ) * (2*Real.pi*Complex.I)) =
        (a:ℂ) * Complex.exp ((t * (2*Real.pi) : ℝ) * Complex.I) := by
      rw [Complex.exp_add, hexpz0, hcast]
    rw [heq]
    exact haU t ht
  have hz0mem : z0 ∈ Γ '' (Icc (0:ℝ) 1) :=
    ⟨0, by norm_num, by simp [hΓ]⟩
  have hpre : IsPreconnected (Γ '' (Icc (0:ℝ) 1)) :=
    isPreconnected_Icc.image Γ hcont.continuousOn
  have hkey := hpre.subset_connectedComponentIn hz0mem hsub
  have h1mem : (z0 + 2*Real.pi*Complex.I) ∈ Γ '' (Icc (0:ℝ) 1) :=
    ⟨1, by norm_num, by simp [hΓ]⟩
  exact hkey h1mem

theorem exp_preimage_add_two_pi_mul_I_mem {U : Set ℂ} {z : ℂ} (hz : z ∈ Complex.exp ⁻¹' U) :
    z + 2*Real.pi*Complex.I ∈ Complex.exp ⁻¹' U := by
  show Complex.exp (z + 2*Real.pi*Complex.I) ∈ U
  rwa [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem exp_preimage_sub_two_pi_mul_I_mem {U : Set ℂ} {z : ℂ} (hz : z ∈ Complex.exp ⁻¹' U) :
    z - 2*Real.pi*Complex.I ∈ Complex.exp ⁻¹' U := by
  show Complex.exp (z - 2*Real.pi*Complex.I) ∈ U
  have hexp : Complex.exp (z - 2*Real.pi*Complex.I) = Complex.exp z := by
    rw [Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  rwa [hexp]

theorem connectedComponentIn_exp_preimage_add_two_pi_mul_I {U : Set ℂ} {z0 : ℂ}
    (hz0 : z0 ∈ Complex.exp ⁻¹' U)
    (hshift : z0 + 2*Real.pi*Complex.I ∈ connectedComponentIn (Complex.exp ⁻¹' U) z0) :
    (fun w => w + 2*Real.pi*Complex.I) '' connectedComponentIn (Complex.exp ⁻¹' U) z0 =
      connectedComponentIn (Complex.exp ⁻¹' U) z0 := by
  have heq : connectedComponentIn (Complex.exp ⁻¹' U) z0 =
      connectedComponentIn (Complex.exp ⁻¹' U) (z0 + 2*Real.pi*Complex.I) :=
    connectedComponentIn_eq hshift
  have hz0mem : z0 ∈ connectedComponentIn (Complex.exp ⁻¹' U) z0 := mem_connectedComponentIn hz0
  have hsub1 : (fun w => w + 2*Real.pi*Complex.I) '' connectedComponentIn (Complex.exp ⁻¹' U) z0 ⊆
      connectedComponentIn (Complex.exp ⁻¹' U) z0 := by
    have hpre : IsPreconnected
        ((fun w => w + 2*Real.pi*Complex.I) '' connectedComponentIn (Complex.exp ⁻¹' U) z0) :=
      (isPreconnected_connectedComponentIn).image _ (Continuous.add continuous_id
        continuous_const).continuousOn
    have hsubA : (fun w => w + 2*Real.pi*Complex.I) '' connectedComponentIn
        (Complex.exp ⁻¹' U) z0 ⊆ Complex.exp ⁻¹' U := by
      rintro w ⟨v, hv, rfl⟩
      exact exp_preimage_add_two_pi_mul_I_mem (connectedComponentIn_subset _ _ hv)
    have hmem : z0 + 2*Real.pi*Complex.I ∈
        (fun w => w + 2*Real.pi*Complex.I) '' connectedComponentIn (Complex.exp ⁻¹' U) z0 :=
      ⟨z0, hz0mem, rfl⟩
    have hkey := hpre.subset_connectedComponentIn hmem hsubA
    rwa [← heq] at hkey
  have hsub2 : connectedComponentIn (Complex.exp ⁻¹' U) z0 ⊆
      (fun w => w + 2*Real.pi*Complex.I) '' connectedComponentIn (Complex.exp ⁻¹' U) z0 := by
    intro z hz
    refine ⟨z - 2*Real.pi*Complex.I, ?_, by ring⟩
    have hpre : IsPreconnected
        ((fun w => w - 2*Real.pi*Complex.I) '' connectedComponentIn (Complex.exp ⁻¹' U) z0) :=
      (isPreconnected_connectedComponentIn).image _ (Continuous.sub continuous_id
        continuous_const).continuousOn
    have hsubA : (fun w => w - 2*Real.pi*Complex.I) '' connectedComponentIn
        (Complex.exp ⁻¹' U) z0 ⊆ Complex.exp ⁻¹' U := by
      rintro w ⟨v, hv, rfl⟩
      exact exp_preimage_sub_two_pi_mul_I_mem (connectedComponentIn_subset _ _ hv)
    have hz0mem' : z0 ∈
        (fun w => w - 2*Real.pi*Complex.I) '' connectedComponentIn (Complex.exp ⁻¹' U) z0 :=
      ⟨z0 + 2*Real.pi*Complex.I, hshift, by ring⟩
    have hkey := hpre.subset_connectedComponentIn hz0mem' hsubA
    exact hkey ⟨z, hz, rfl⟩
  exact hsub1.antisymm hsub2

/-- If a set is invariant under `+2πi` (as an image equation), then membership of `v+2πi` is
equivalent to membership of `v`, for every `v` (not just a fixed basepoint). -/
theorem add_two_pi_mul_I_mem_iff {S : Set ℂ}
    (himg : (fun w => w + 2*Real.pi*Complex.I) '' S = S) (v : ℂ) :
    v + 2*Real.pi*Complex.I ∈ S ↔ v ∈ S := by
  constructor
  · intro h
    rw [← himg] at h
    obtain ⟨u, hu, hueq⟩ := h
    have : u = v := by linear_combination hueq
    rwa [← this]
  · intro h
    rw [← himg]
    exact ⟨v, h, rfl⟩

/-- Consequently, membership of `w + k•2πi` for any integer `k` is equivalent to membership
of `w`. -/
theorem add_int_two_pi_mul_I_mem_iff {S : Set ℂ}
    (himg : (fun w => w + 2*Real.pi*Complex.I) '' S = S) (w : ℂ) (k : ℤ) :
    w + (k:ℂ) * (2*Real.pi*Complex.I) ∈ S ↔ w ∈ S := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have hcast : w + (((n:ℤ)+1 : ℤ):ℂ) * (2*Real.pi*Complex.I) =
        (w + (n:ℂ) * (2*Real.pi*Complex.I)) + 2*Real.pi*Complex.I := by push_cast; ring
    rw [hcast, add_two_pi_mul_I_mem_iff himg]
    exact ih
  | pred n ih =>
    have hcast : w + ((-(n:ℤ) : ℤ):ℂ) * (2*Real.pi*Complex.I) =
        (w + ((-(n:ℤ) - 1) : ℤ) * (2*Real.pi*Complex.I)) + 2*Real.pi*Complex.I := by
      push_cast; ring
    rw [hcast, add_two_pi_mul_I_mem_iff himg] at ih
    exact ih

theorem isConnected_exp_preimage {U : Set ℂ} (hUpc : IsPathConnected U)
    (h0U : (0:ℂ) ∉ U) {a : ℝ} (ha0 : 0 < a)
    (hcircle : ∀ t : ℝ, (a:ℂ) * Complex.exp ((t * (2*Real.pi) : ℝ) * Complex.I) ∈ U) :
    IsConnected (Complex.exp ⁻¹' U) := by
  set z0 : ℂ := (Real.log a : ℂ) with hz0_def
  have hexpz0 : Complex.exp z0 = (a:ℂ) := by
    rw [hz0_def, ← Complex.ofReal_exp, Real.exp_log ha0]
  have haU : (a:ℂ) ∈ U := by simpa using hcircle 0
  have hz0mem : z0 ∈ Complex.exp ⁻¹' U := by show Complex.exp z0 ∈ U; rwa [hexpz0]
  have hshift : z0 + 2*Real.pi*Complex.I ∈ connectedComponentIn (Complex.exp ⁻¹' U) z0 :=
    two_pi_mul_I_mem_connectedComponentIn_exp_preimage ha0 (fun t _ => hcircle t)
  have himg := connectedComponentIn_exp_preimage_add_two_pi_mul_I hz0mem hshift
  refine ⟨⟨z0, hz0mem⟩, ?_⟩
  have hsub : Complex.exp ⁻¹' U ⊆ connectedComponentIn (Complex.exp ⁻¹' U) z0 := by
    intro z hz
    have hzU : Complex.exp z ∈ U := hz
    have hjoin : JoinedIn U (Complex.exp z) (a:ℂ) := hUpc.joinedIn _ hzU _ haU
    set p : Path (Complex.exp z) (a:ℂ) := hjoin.somePath with hp_def
    set γ : ℝ → ℂ := fun t => p (projIcc 0 1 zero_le_one t) with hγ_def
    have hγcont : Continuous γ := p.continuous.comp continuous_projIcc
    have hγmem : ∀ t ∈ Icc (0:ℝ) 1, γ t ∈ U := by
      intro t ht
      rw [hγ_def]
      simp only [projIcc_of_mem zero_le_one ht]
      exact hjoin.somePath_mem _
    have hγne : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ 0 := fun t ht hcon => by
      have hmemU := hγmem t ht
      rw [hcon] at hmemU
      exact h0U hmemU
    obtain ⟨Γ, hΓcont, hΓeq⟩ := exists_continuous_log_lift hγcont.continuousOn hγne
    have hγ0 : γ 0 = Complex.exp z := by
      rw [hγ_def]; simp only [projIcc_of_mem zero_le_one (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)]
      exact p.source
    have hγ1 : γ 1 = Complex.exp z0 := by
      rw [hγ_def]; simp only [projIcc_of_mem zero_le_one (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)]
      rw [hexpz0]; exact p.target
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp
      ((hΓeq 0 (by norm_num)).trans hγ0)
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp
      ((hΓeq 1 (by norm_num)).trans hγ1)
    have hΓsub : Γ '' (Icc (0:ℝ) 1) ⊆ Complex.exp ⁻¹' U := by
      rintro w ⟨t, ht, rfl⟩
      show Complex.exp (Γ t) ∈ U
      rw [hΓeq t ht]
      exact hγmem t ht
    have hpre : IsPreconnected (Γ '' Icc (0:ℝ) 1) := isPreconnected_Icc.image Γ hΓcont.continuousOn
    have h0mem : Γ 0 ∈ Γ '' Icc (0:ℝ) 1 := ⟨0, by norm_num, rfl⟩
    have hΓ0mem : Γ 0 ∈ Complex.exp ⁻¹' U := hΓsub h0mem
    have h1mem : Γ 1 ∈ connectedComponentIn (Complex.exp ⁻¹' U) (Γ 0) :=
      hpre.subset_connectedComponentIn h0mem hΓsub ⟨1, by norm_num, rfl⟩
    rw [hk, hm] at h1mem
    have hz0Comp0 : z0 ∈ connectedComponentIn (Complex.exp ⁻¹' U) z0 :=
      mem_connectedComponentIn hz0mem
    have hm0 : z0 + (m:ℂ) * (2*Real.pi*Complex.I) ∈
        connectedComponentIn (Complex.exp ⁻¹' U) z0 :=
      (add_int_two_pi_mul_I_mem_iff himg z0 m).mpr hz0Comp0
    have heq1 : connectedComponentIn (Complex.exp ⁻¹' U) (z + (k:ℂ) * (2*Real.pi*Complex.I)) =
        connectedComponentIn (Complex.exp ⁻¹' U) (z0 + (m:ℂ) * (2*Real.pi*Complex.I)) :=
      connectedComponentIn_eq h1mem
    have heq2 : connectedComponentIn (Complex.exp ⁻¹' U) (z0 + (m:ℂ) * (2*Real.pi*Complex.I)) =
        connectedComponentIn (Complex.exp ⁻¹' U) z0 :=
      (connectedComponentIn_eq hm0).symm
    have hzkmem : z + (k:ℂ) * (2*Real.pi*Complex.I) ∈
        connectedComponentIn (Complex.exp ⁻¹' U) (z + (k:ℂ) * (2*Real.pi*Complex.I)) :=
      mem_connectedComponentIn (hk ▸ hΓ0mem)
    rw [heq1, heq2] at hzkmem
    exact (add_int_two_pi_mul_I_mem_iff himg z k).mp hzkmem
  have heq : Complex.exp ⁻¹' U = connectedComponentIn (Complex.exp ⁻¹' U) z0 :=
    hsub.antisymm (connectedComponentIn_subset _ _)
  rw [heq]
  exact isPreconnected_connectedComponentIn

/-! ### Step 3: the two corollaries — `expStrip A` connected, and the outer piece connected -/

theorem isConnected_expStrip {A : Set ℂ} (hAo : IsOpen A)
    (hAconn : IsConnected (A \ closedBall (0:ℂ) 1))
    (hcollar : ∃ r : ℝ, 1 < r ∧ {ζ : ℂ | 1 < ‖ζ‖ ∧ ‖ζ‖ < r} ⊆ A) :
    IsConnected (expStrip A) := by
  rw [expStrip_eq_preimage_diff]
  obtain ⟨r, hr1, hrsub⟩ := hcollar
  have hBopen : IsOpen (A \ closedBall (0:ℂ) 1) := hAo.sdiff isClosed_closedBall
  set a : ℝ := (1 + r) / 2 with ha_def
  have ha1 : 1 < a := by rw [ha_def]; linarith
  have har : a < r := by rw [ha_def]; linarith
  have ha0 : 0 < a := by linarith
  have hanorm : ‖(a:ℂ)‖ = a := by rw [Complex.norm_real, Real.norm_of_nonneg ha0.le]
  have h0notmem : (0:ℂ) ∉ A \ closedBall (0:ℂ) 1 := fun h => h.2 (by simp)
  have hApc : IsPathConnected (A \ closedBall (0:ℂ) 1) :=
    hBopen.isConnected_iff_isPathConnected.mp hAconn
  refine isConnected_exp_preimage hApc h0notmem ha0 (fun t => ?_)
  have hnormt : ‖(a:ℂ) * Complex.exp ((t * (2*Real.pi) : ℝ) * Complex.I)‖ = a := by
    rw [Complex.norm_mul, hanorm, norm_exp_ofReal_mul_I, mul_one]
  refine ⟨hrsub ?_, ?_⟩
  · simp only [mem_setOf_eq, hnormt]; exact ⟨ha1, har⟩
  · simp only [mem_closedBall, dist_zero_right, not_le, hnormt]; exact ha1

theorem isConnected_exp_preimage_compl {A : Set ℂ} (hAcompl : IsPathConnected Aᶜ)
    (hball : closedBall (0:ℂ) 1 ⊆ A) (hAbdd : Bornology.IsBounded A) :
    IsConnected (Complex.exp ⁻¹' Aᶜ) := by
  have h0notmem : (0:ℂ) ∉ Aᶜ := fun h => h (hball (mem_closedBall_self zero_le_one))
  obtain ⟨r, hr1, hrsub⟩ := hAbdd.subset_ball_lt 1 (0:ℂ)
  set a : ℝ := r with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hanorm : ‖(a:ℂ)‖ = a := by rw [Complex.norm_real, Real.norm_of_nonneg ha0.le]
  refine isConnected_exp_preimage hAcompl h0notmem ha0 (fun t => ?_)
  have hnormt : ‖(a:ℂ) * Complex.exp ((t * (2*Real.pi) : ℝ) * Complex.I)‖ = a := by
    rw [Complex.norm_mul, hanorm, norm_exp_ofReal_mul_I, mul_one]
  intro hcon
  have := hrsub hcon
  rw [mem_ball_zero_iff, hnormt] at this
  exact absurd this (lt_irrefl a)

/-! ### Step 4: gluing the two complement pieces at `∞` -/

theorem expStrip_compl_eq {A : Set ℂ} :
    (expStrip A)ᶜ = {z : ℂ | z.re ≤ 0} ∪ Complex.exp ⁻¹' Aᶜ := by
  ext z
  simp only [expStrip, mem_compl_iff, mem_setOf_eq, mem_union, mem_preimage, not_and, not_lt]
  constructor
  · intro h
    by_cases hre : z.re ≤ 0
    · exact Or.inl hre
    · exact Or.inr (h (not_le.mp hre))
  · rintro (h | h) hre
    · linarith
    · exact h

theorem extInf_mem_closure_toExt_of_not_isBounded {S : Set ℂ} (hS : ¬ Bornology.IsBounded S) :
    extInf ∈ closure (toExt S) := by
  rw [mem_closure_iff_nhds_basis OnePoint.hasBasis_nhds_infty]
  rintro s ⟨-, hs⟩
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 hs.isBounded
  rw [isBounded_iff_forall_norm_le] at hS
  push_neg at hS
  obtain ⟨z, hzS, hzR⟩ := hS R
  refine ⟨(z : ExtPlane), ⟨z, hzS, rfl⟩, Or.inl ⟨z, ?_, rfl⟩⟩
  intro hmem
  have := hR _ hmem
  linarith

theorem isPreconnected_toExt_union_extInf_of_unbounded {S : Set ℂ} (hSpre : IsPreconnected S)
    (hSub : ¬ Bornology.IsBounded S) : IsPreconnected (toExt S ∪ {extInf}) := by
  have h1 : IsPreconnected (toExt S) := hSpre.image _ OnePoint.continuous_coe.continuousOn
  exact h1.subset_closure subset_union_left
    (union_subset subset_closure
      (singleton_subset_iff.2 (extInf_mem_closure_toExt_of_not_isBounded hSub)))

theorem isConnected_compl_toExt_expStrip {A : Set ℂ}
    (hAbdd : Bornology.IsBounded A) (hAcompl : IsPathConnected Aᶜ)
    (hball : closedBall (0:ℂ) 1 ⊆ A) :
    IsConnected (toExt (expStrip A))ᶜ := by
  have hRconn : IsConnected (Complex.exp ⁻¹' Aᶜ) :=
    isConnected_exp_preimage_compl hAcompl hball hAbdd
  set L : Set ℂ := {z : ℂ | z.re ≤ 0} with hL_def
  set R : Set ℂ := Complex.exp ⁻¹' Aᶜ with hR_def
  have hLpre : IsPreconnected L := (convex_halfSpace_re_le (0:ℝ)).isPreconnected
  have hLub : ¬ Bornology.IsBounded L := by
    intro hb
    obtain ⟨r, hr⟩ := hb.subset_closedBall (0:ℂ)
    have hmemL : ((-(|r|+1):ℝ):ℂ) ∈ L := by
      show ((-(|r|+1):ℝ):ℂ).re ≤ 0
      simp; linarith [abs_nonneg r]
    have hin := hr hmemL
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith [abs_nonneg r] : (-(|r|+1):ℝ) < 0)] at hin
    linarith [le_abs_self r]
  have hRub : ¬ Bornology.IsBounded R := by
    intro hb
    obtain ⟨r, hr⟩ := hb.subset_closedBall (0:ℂ)
    obtain ⟨r', hr'1, hrsub'⟩ := hAbdd.subset_ball_lt (max r 1) (0:ℂ)
    set a : ℝ := r' with ha_def
    have ha0 : 0 < a := by rw [ha_def]; linarith [le_max_right r (1:ℝ)]
    have haR : (a:ℂ) ∈ R := by
      show Complex.exp (a:ℂ) ∈ Aᶜ
      rw [mem_compl_iff]
      intro haA
      have hlt := hrsub' haA
      rw [mem_ball_zero_iff] at hlt
      have hexpa : Complex.exp ((a:ℝ):ℂ) = ((Real.exp a : ℝ) : ℂ) := (Complex.ofReal_exp a).symm
      rw [hexpa, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos a).le] at hlt
      nlinarith [Real.add_one_le_exp a]
    have hin := hr haR
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg ha0.le] at hin
    have hra : r < a := lt_of_le_of_lt (le_max_left r 1) hr'1
    linarith
  have hLext := isPreconnected_toExt_union_extInf_of_unbounded hLpre hLub
  have hRext := isPreconnected_toExt_union_extInf_of_unbounded hRconn.2 hRub
  have hextInfL : extInf ∈ toExt L ∪ {extInf} := Or.inr rfl
  have hextInfR : extInf ∈ toExt R ∪ {extInf} := Or.inr rfl
  have hunion := hLext.union extInf hextInfL hextInfR hRext
  have heq : toExt L ∪ {extInf} ∪ (toExt R ∪ {extInf}) = toExt ((expStrip A)ᶜ) ∪ {extInf} := by
    rw [expStrip_compl_eq, ← hL_def, ← hR_def]
    have hsplit : toExt (L ∪ R) = toExt L ∪ toExt R := by
      ext w
      rcases w with _ | z
      · exact iff_of_false (extInf_notMem_toExt (L ∪ R))
          (fun h => h.elim (extInf_notMem_toExt L) (extInf_notMem_toExt R))
      · have : (some z : ExtPlane) = ((z : ℂ) : ExtPlane) := rfl
        rw [this, mem_union, coe_mem_toExt_iff, coe_mem_toExt_iff, coe_mem_toExt_iff, mem_union]
    rw [hsplit]
    ext w
    simp only [mem_union, mem_singleton_iff]
    tauto
  rw [heq] at hunion
  rw [compl_toExt]
  exact ⟨⟨extInf, Or.inr rfl⟩, hunion⟩

/-! ### Step 5: `HasHolomorphicSqrt` for both `expStrip A` and the target strip -/

theorem hasHolomorphicSqrt_expStrip {A : Set ℂ} (hAo : IsOpen A)
    (hAconn : IsConnected (A \ closedBall (0:ℂ) 1))
    (hAbdd : Bornology.IsBounded A)
    (hcollar : ∃ r : ℝ, 1 < r ∧ {ζ : ℂ | 1 < ‖ζ‖ ∧ ‖ζ‖ < r} ⊆ A)
    (hAcompl : IsPathConnected Aᶜ) (hball : closedBall (0:ℂ) 1 ⊆ A) :
    RMT.HasHolomorphicSqrt (expStrip A) :=
  hasHolomorphicSqrt_of_isConnected_compl (isOpen_expStrip hAo)
    (isConnected_expStrip hAo hAconn hcollar) (isConnected_compl_toExt_expStrip hAbdd hAcompl hball)

/-! ### Step 6: piece B's final deliverable — some conformal `g : expStrip A → strip d` -/

theorem exists_conformal_expStrip_strip {A : Set ℂ} (hAo : IsOpen A)
    (hAconn : IsConnected (A \ closedBall (0:ℂ) 1))
    (hAbdd : Bornology.IsBounded A)
    (hcollar : ∃ r : ℝ, 1 < r ∧ {ζ : ℂ | 1 < ‖ζ‖ ∧ ‖ζ‖ < r} ⊆ A)
    (hball : closedBall (0:ℂ) 1 ⊆ A) (hAcompl : IsPathConnected Aᶜ) :
    ∃ d > 0, ∃ g : ℂ → ℂ, IsConformalOnto g (expStrip A) (strip d) := by
  have hSo : IsOpen (expStrip A) := isOpen_expStrip hAo
  have hSconn : IsConnected (expStrip A) := isConnected_expStrip hAo hAconn hcollar
  have hHS : RMT.HasHolomorphicSqrt (expStrip A) :=
    hasHolomorphicSqrt_expStrip hAo hAconn hAbdd hcollar hAcompl hball
  obtain ⟨z₀, hz₀⟩ := hSconn.1
  have hSne : (expStrip A)ᶜ.Nonempty := by
    refine ⟨(-1 : ℂ), ?_⟩
    show ¬ (0 < ((-1 : ℂ)).re ∧ Complex.exp (-1 : ℂ) ∈ A)
    rintro ⟨hre, -⟩
    norm_num at hre
  obtain ⟨f, hf, hfbij⟩ :=
    RMT.exists_riemannMap_of_hasHolomorphicSqrt hSo hSconn hSne hHS hz₀
  have hfconf : IsConformalOnto f (expStrip A) RMT.disc :=
    ⟨hf.diff, hf.injOn, hfbij.image_eq⟩
  have hdiscunit : RMT.disc = unitDisc := rfl
  refine ⟨1, one_pos, stripDiscInv 1 ∘ f, ?_⟩
  rw [hdiscunit] at hfconf
  exact (isConformalOnto_stripDiscInv one_pos).comp hfconf
end LiZhongQC
