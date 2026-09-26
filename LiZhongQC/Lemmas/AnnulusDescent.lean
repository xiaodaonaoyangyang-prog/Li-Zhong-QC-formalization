import LiZhongQC.Lemmas.CanonicalForm
import LiZhongQC.Lemmas.Conformal
import LiZhongQC.Lemmas.ExpStripBasic

/-!
# D1, D2 (B conformally equiv. to B'' minus the closed disc) and D4 (descent through `exp`)
-/


open Complex Set Metric Filter Topology Bornology
open scoped ComplexConjugate

noncomputable section

namespace LiZhongQC

/-! ## D1, D2 (the assembler's own theorems; `K`, `A`, `Φ` scoped to this section). -/

section AnnulusDescentD1D2

variable {K A : Set ℂ} {Φ : ℂ → ℂ}

theorem sdiff_closedBall_eq_image
    (hΦbij : BijOn Φ (univ \ K) {ζ : ℂ | 1 < ‖ζ‖})
    (hAeq : A = closedBall 0 1 ∪ Φ '' (unitDisc \ K)) :
    A \ closedBall 0 1 = Φ '' (unitDisc \ K) := by
  have himg : Φ '' (unitDisc \ K) ⊆ {ζ : ℂ | 1 < ‖ζ‖} := by
    rintro _ ⟨w, hw, rfl⟩
    exact hΦbij.mapsTo ⟨mem_univ w, hw.2⟩
  ext ζ
  simp only [hAeq, mem_diff, mem_union, mem_closedBall, dist_zero_right, not_le]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd h1 (not_le.2 h2)
    · exact h1
  · intro h
    exact ⟨Or.inr h, himg h⟩

/-- D2: hence `B` is conformally equivalent to `B''`. -/
theorem conformallyEquivalent_sdiff_closedBall {B : Set ℂ}
    (hBK : ConformallyEquivalent B (unitDisc \ K))
    (hΦd : DifferentiableOn ℂ Φ (univ \ K))
    (hΦbij : BijOn Φ (univ \ K) {ζ : ℂ | 1 < ‖ζ‖})
    (hAeq : A = closedBall 0 1 ∪ Φ '' (unitDisc \ K)) :
    ConformallyEquivalent B (A \ closedBall 0 1) := by
  have hsub : unitDisc \ K ⊆ univ \ K := fun w hw => ⟨mem_univ w, hw.2⟩
  have hconf : IsConformalOnto Φ (unitDisc \ K) (A \ closedBall 0 1) :=
    ⟨hΦd.mono hsub, hΦbij.injOn.mono hsub, (sdiff_closedBall_eq_image hΦbij hAeq).symm⟩
  exact hBK.trans ⟨Φ, hconf⟩

end AnnulusDescentD1D2

/-! ## D4: descent of a periodic conformal map through `exp`. -/
/-! ## Part 1: periodicity of `expStrip A` and of `g` under `z ↦ z + 2πi` -/

theorem re_two_pi_mul_I_mul_int (n : ℤ) : ((n : ℂ) * (2 * (Real.pi : ℂ) * I)).re = 0 := by
  have h : (n : ℂ) * (2 * (Real.pi : ℂ) * I) = ((2 * Real.pi * n : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [h]
  simp [Complex.mul_re]

theorem expStrip_add_two_pi_mul_I {A : Set ℂ} {z : ℂ} (hz : z ∈ expStrip A) (n : ℤ) :
    z + (n : ℂ) * (2 * (Real.pi : ℂ) * I) ∈ expStrip A := by
  refine ⟨?_, ?_⟩
  · show 0 < (z + (n : ℂ) * (2 * (Real.pi : ℂ) * I)).re
    rw [Complex.add_re, re_two_pi_mul_I_mul_int]
    simpa using hz.1
  · have hexp := (Complex.exp_periodic.int_mul n) z
    rw [hexp]
    exact hz.2

theorem g_shift_two_pi_mul_I_int {A : Set ℂ} {g : ℂ → ℂ} {s : ℝ}
    (hper : ∀ z ∈ expStrip A, g (z + 2 * (Real.pi : ℂ) * I) = g z + (s : ℂ) * I)
    {z : ℂ} (hz : z ∈ expStrip A) (n : ℤ) :
    g (z + (n : ℂ) * (2 * (Real.pi : ℂ) * I)) = g z + (n : ℂ) * (s : ℂ) * I := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih =>
    push_cast
    push_cast at ih
    have hmem : z + (i : ℂ) * (2 * (Real.pi : ℂ) * I) ∈ expStrip A := by
      have := expStrip_add_two_pi_mul_I hz (i : ℤ)
      simpa using this
    have hstep := hper (z + (i : ℂ) * (2 * (Real.pi : ℂ) * I)) hmem
    have harg : z + (i : ℂ) * (2 * (Real.pi : ℂ) * I) + 2 * (Real.pi : ℂ) * I
        = z + ((i : ℂ) + 1) * (2 * (Real.pi : ℂ) * I) := by ring
    rw [harg] at hstep
    rw [hstep, ih]
    ring
  | pred i ih =>
    push_cast
    push_cast at ih
    have hmem : z + (-(i : ℂ) - 1) * (2 * (Real.pi : ℂ) * I) ∈ expStrip A := by
      have := expStrip_add_two_pi_mul_I hz (-(i : ℤ) - 1)
      simpa using this
    have hstep := hper (z + (-(i : ℂ) - 1) * (2 * (Real.pi : ℂ) * I)) hmem
    have harg : z + (-(i : ℂ) - 1) * (2 * (Real.pi : ℂ) * I) + 2 * (Real.pi : ℂ) * I
        = z + (-(i : ℂ)) * (2 * (Real.pi : ℂ) * I) := by ring
    rw [harg] at hstep
    have hstep2 : g (z + (-(i : ℂ) - 1) * (2 * (Real.pi : ℂ) * I))
        = g (z + (-(i : ℂ)) * (2 * (Real.pi : ℂ) * I)) - (s : ℂ) * I := by
      rw [hstep]; ring
    rw [hstep2, ih]
    ring

/-! ## Part 2: well-definedness of the descended map -/

theorem exp_g_well_defined {A : Set ℂ} {s : ℝ} (hs : 0 < s) {g : ℂ → ℂ}
    (hper : ∀ z ∈ expStrip A, g (z + 2 * (Real.pi : ℂ) * I) = g z + (s : ℂ) * I)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ expStrip A) (hz₂ : z₂ ∈ expStrip A)
    (heq : Complex.exp z₁ = Complex.exp z₂) :
    Complex.exp ((2 * Real.pi / s : ℝ) * g z₁) = Complex.exp ((2 * Real.pi / s : ℝ) * g z₂) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq
  have hgz : g z₁ = g z₂ + (n : ℂ) * (s : ℂ) * I := by
    rw [hn]; exact g_shift_two_pi_mul_I_int hper hz₂ n
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hrw : (2 * Real.pi / s : ℝ) * g z₁
      = (2 * Real.pi / s : ℝ) * g z₂ + (n : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    rw [hgz]; push_cast; field_simp
  rw [hrw]
  exact (Complex.exp_periodic.int_mul n) ((2 * Real.pi / s : ℝ) * g z₂)

/-- The descended map, well-defined via `Function.invFunOn` (any preimage under `exp` inside
`expStrip A` gives the same value, `exp_g_well_defined`). -/
def hFun (A : Set ℂ) (s : ℝ) (g : ℂ → ℂ) (ζ : ℂ) : ℂ :=
  Complex.exp ((2 * Real.pi / s : ℝ) * g (Function.invFunOn Complex.exp (expStrip A) ζ))

/-! ## Part 3: a local branch of `log`, and holomorphy of `hFun` -/

/-- A local branch of `log` obtained by rotating the branch cut away from `θ`. -/
def localLogBranch (θ : ℝ) (ζ : ℂ) : ℂ :=
  Complex.log (Complex.exp (-I * (θ : ℂ)) * ζ) + I * (θ : ℂ)

theorem exp_localLogBranch {θ : ℝ} {ζ : ℂ}
    (hζ : Complex.exp (-I * (θ : ℂ)) * ζ ∈ Complex.slitPlane) :
    Complex.exp (localLogBranch θ ζ) = ζ := by
  have hne : Complex.exp (-I * (θ : ℂ)) * ζ ≠ 0 := (Complex.mem_slitPlane_iff_arg.mp hζ).2
  rw [localLogBranch, Complex.exp_add, Complex.exp_log hne]
  have : Complex.exp (-I * (θ : ℂ)) * Complex.exp (I * (θ : ℂ)) = 1 := by
    rw [← Complex.exp_add]; simp
  calc Complex.exp (-I * (θ : ℂ)) * ζ * Complex.exp (I * (θ : ℂ))
      = (Complex.exp (-I * (θ : ℂ)) * Complex.exp (I * (θ : ℂ))) * ζ := by ring
    _ = ζ := by rw [this]; ring

theorem norm_exp_neg_I_mul_real (θ : ℝ) : ‖Complex.exp (-I * (θ : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have : (-I * (θ : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [this, Real.exp_zero]

theorem re_localLogBranch (θ : ℝ) (ζ : ℂ) :
    (localLogBranch θ ζ).re = Real.log ‖ζ‖ := by
  have hnorm : ‖Complex.exp (-I * (θ : ℂ)) * ζ‖ = ‖ζ‖ := by
    rw [norm_mul, norm_exp_neg_I_mul_real, one_mul]
  rw [localLogBranch]
  simp only [Complex.add_re, Complex.log_re, hnorm]
  simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

theorem rotate_self_eq_norm (ζ₀ : ℂ) (hζ₀ : ζ₀ ≠ 0) :
    Complex.exp (-I * (ζ₀.arg : ℂ)) * ζ₀ = (‖ζ₀‖ : ℂ) := by
  have hpolar := Complex.norm_mul_exp_arg_mul_I ζ₀
  have : Complex.exp (-I * (ζ₀.arg : ℂ)) * ζ₀
      = Complex.exp (-I * (ζ₀.arg : ℂ)) * ((‖ζ₀‖ : ℂ) * Complex.exp ((ζ₀.arg : ℂ) * I)) := by
    rw [hpolar]
  rw [this]
  have h2 : Complex.exp (-I * (ζ₀.arg : ℂ)) * Complex.exp ((ζ₀.arg : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]; simp; ring_nf; simp
  calc Complex.exp (-I * (ζ₀.arg : ℂ)) * ((‖ζ₀‖ : ℂ) * Complex.exp ((ζ₀.arg : ℂ) * I))
      = (Complex.exp (-I * (ζ₀.arg : ℂ)) * Complex.exp ((ζ₀.arg : ℂ) * I)) * (‖ζ₀‖ : ℂ) := by
        ring
    _ = (‖ζ₀‖ : ℂ) := by rw [h2]; ring

theorem differentiableAt_localLogBranch {θ : ℝ} {ζ : ℂ}
    (hζ : Complex.exp (-I * (θ : ℂ)) * ζ ∈ Complex.slitPlane) :
    DifferentiableAt ℂ (localLogBranch θ) ζ := by
  have hf : DifferentiableAt ℂ (fun ζ => Complex.exp (-I * (θ : ℂ)) * ζ) ζ := by fun_prop
  have hlog : DifferentiableAt ℂ (fun ζ => Complex.log (Complex.exp (-I * (θ : ℂ)) * ζ)) ζ :=
    DifferentiableAt.clog hf hζ
  exact hlog.add (differentiableAt_const _)

theorem isOpen_rotSet (θ : ℝ) :
    IsOpen {ζ : ℂ | Complex.exp (-I * (θ : ℂ)) * ζ ∈ Complex.slitPlane} :=
  Complex.isOpen_slitPlane.preimage (by fun_prop)

theorem differentiableAt_hFun {A : Set ℂ} (hAo : IsOpen A) {d s : ℝ} (hs : 0 < s) {g : ℂ → ℂ}
    (hg : IsConformalOnto g (expStrip A) (strip d))
    (hper : ∀ z ∈ expStrip A, g (z + 2 * (Real.pi : ℂ) * I) = g z + (s : ℂ) * I)
    (hAexp : A \ closedBall 0 1 = Complex.exp '' expStrip A)
    {ζ₀ : ℂ} (hζ₀ : ζ₀ ∈ A \ closedBall 0 1) :
    DifferentiableAt ℂ (hFun A s g) ζ₀ := by
  have hζ₀_gt1 : 1 < ‖ζ₀‖ := by
    have h2 := hζ₀.2
    rw [mem_closedBall_zero_iff] at h2
    exact not_le.mp h2
  have hnorm_pos : (0 : ℝ) < ‖ζ₀‖ := by linarith
  have hζ₀ne : ζ₀ ≠ 0 := norm_pos_iff.mp hnorm_pos
  set θ : ℝ := ζ₀.arg with hθdef
  have hrot0 : Complex.exp (-I * (θ : ℂ)) * ζ₀ = (‖ζ₀‖ : ℂ) := rotate_self_eq_norm ζ₀ hζ₀ne
  have hζ₀_slit : Complex.exp (-I * (θ : ℂ)) * ζ₀ ∈ Complex.slitPlane := by
    rw [hrot0]
    exact Or.inl (by exact_mod_cast hnorm_pos)
  set V : Set ℂ :=
      {ζ : ℂ | Complex.exp (-I * (θ : ℂ)) * ζ ∈ Complex.slitPlane} ∩ A ∩ {ζ : ℂ | 1 < ‖ζ‖}
    with hVdef
  have hVo : IsOpen V :=
    ((isOpen_rotSet θ).inter hAo).inter (isOpen_lt continuous_const continuous_norm)
  have hζ₀V : ζ₀ ∈ V := ⟨⟨hζ₀_slit, hζ₀.1⟩, hζ₀_gt1⟩
  have hmemA : ∀ ζ : ℂ, ζ ∈ A → 1 < ‖ζ‖ → ζ ∈ Complex.exp '' expStrip A := by
    intro ζ hζA hζnorm
    rw [← hAexp]
    refine ⟨hζA, ?_⟩
    rw [mem_closedBall_zero_iff]
    linarith
  have heq_on_V : ∀ ζ ∈ V,
      hFun A s g ζ = Complex.exp ((2 * Real.pi / s : ℝ) * g (localLogBranch θ ζ)) := by
    intro ζ hζ
    obtain ⟨⟨hζslit, hζA⟩, hζnorm⟩ := hζ
    have hLmem : localLogBranch θ ζ ∈ expStrip A := by
      refine ⟨?_, ?_⟩
      · rw [re_localLogBranch]; exact Real.log_pos hζnorm
      · rw [exp_localLogBranch hζslit]; exact hζA
    have hexpL : Complex.exp (localLogBranch θ ζ) = ζ := exp_localLogBranch hζslit
    have himg : ζ ∈ Complex.exp '' expStrip A := hmemA ζ hζA hζnorm
    have hinvmem : Function.invFunOn Complex.exp (expStrip A) ζ ∈ expStrip A :=
      Function.invFunOn_mem himg
    have hinveq : Complex.exp (Function.invFunOn Complex.exp (expStrip A) ζ) = ζ :=
      Function.invFunOn_eq himg
    show Complex.exp ((2 * Real.pi / s : ℝ) * g (Function.invFunOn Complex.exp (expStrip A) ζ))
        = Complex.exp ((2 * Real.pi / s : ℝ) * g (localLogBranch θ ζ))
    exact exp_g_well_defined hs hper hinvmem hLmem (by rw [hinveq, hexpL])
  have hLmem₀ : localLogBranch θ ζ₀ ∈ expStrip A := by
    refine ⟨?_, ?_⟩
    · rw [re_localLogBranch]; exact Real.log_pos hζ₀_gt1
    · rw [exp_localLogBranch hζ₀_slit]; exact hζ₀.1
  have hdiff_local : DifferentiableAt ℂ
      (fun ζ => Complex.exp ((2 * Real.pi / s : ℝ) * g (localLogBranch θ ζ))) ζ₀ := by
    have hL : DifferentiableAt ℂ (localLogBranch θ) ζ₀ := differentiableAt_localLogBranch hζ₀_slit
    have hgdiff : DifferentiableAt ℂ g (localLogBranch θ ζ₀) :=
      hg.1.differentiableAt ((isOpen_expStrip hAo).mem_nhds hLmem₀)
    have hcomp : DifferentiableAt ℂ (fun ζ => g (localLogBranch θ ζ)) ζ₀ := hgdiff.comp ζ₀ hL
    have hcmul : DifferentiableAt ℂ (fun ζ => (2 * Real.pi / s : ℝ) * g (localLogBranch θ ζ)) ζ₀ :=
      (differentiableAt_const _).mul hcomp
    exact Complex.differentiable_exp.differentiableAt.comp ζ₀ hcmul
  have heqf : hFun A s g =ᶠ[𝓝 ζ₀]
      (fun ζ => Complex.exp ((2 * Real.pi / s : ℝ) * g (localLogBranch θ ζ))) :=
    Filter.eventuallyEq_of_mem (hVo.mem_nhds hζ₀V) heq_on_V
  exact (Filter.EventuallyEq.differentiableAt_iff heqf).2 hdiff_local

/-! ## Part 4: injectivity -/

theorem injOn_hFun {A : Set ℂ} {d s : ℝ} (hs : 0 < s) {g : ℂ → ℂ}
    (hg : IsConformalOnto g (expStrip A) (strip d))
    (hper : ∀ z ∈ expStrip A, g (z + 2 * (Real.pi : ℂ) * I) = g z + (s : ℂ) * I)
    (hAexp : A \ closedBall 0 1 = Complex.exp '' expStrip A) :
    InjOn (hFun A s g) (A \ closedBall 0 1) := by
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hpine : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  intro ζ₁ hζ₁ ζ₂ hζ₂ heq
  have himg₁ : ζ₁ ∈ Complex.exp '' expStrip A := hAexp ▸ hζ₁
  have himg₂ : ζ₂ ∈ Complex.exp '' expStrip A := hAexp ▸ hζ₂
  set z₁ := Function.invFunOn Complex.exp (expStrip A) ζ₁ with hz₁def
  set z₂ := Function.invFunOn Complex.exp (expStrip A) ζ₂ with hz₂def
  have hz₁mem : z₁ ∈ expStrip A := Function.invFunOn_mem himg₁
  have hz₂mem : z₂ ∈ expStrip A := Function.invFunOn_mem himg₂
  have hz₁eq : Complex.exp z₁ = ζ₁ := Function.invFunOn_eq himg₁
  have hz₂eq : Complex.exp z₂ = ζ₂ := Function.invFunOn_eq himg₂
  have heq' : Complex.exp ((2 * Real.pi / s : ℝ) * g z₁)
      = Complex.exp ((2 * Real.pi / s : ℝ) * g z₂) := heq
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq'
  have hshift := g_shift_two_pi_mul_I_int hper hz₂mem m
  have hgz : g z₁ = g z₂ + (m : ℂ) * (s : ℂ) * I := by
    have e1 : (s : ℂ) / (2 * (Real.pi : ℂ)) * ((2 * Real.pi / s : ℝ) * g z₁) = g z₁ := by
      push_cast; field_simp
    have e2 : (s : ℂ) / (2 * (Real.pi : ℂ)) *
        ((2 * Real.pi / s : ℝ) * g z₂ + (m : ℂ) * (2 * (Real.pi : ℂ) * I))
        = g z₂ + (m : ℂ) * (s : ℂ) * I := by
      push_cast; field_simp
    rw [← e1, ← e2, hm]
  have hgz2 : g z₁ = g (z₂ + (m : ℂ) * (2 * (Real.pi : ℂ) * I)) := by rw [hshift, hgz]
  have hz12 : z₁ = z₂ + (m : ℂ) * (2 * (Real.pi : ℂ) * I) :=
    hg.2.1 hz₁mem (expStrip_add_two_pi_mul_I hz₂mem m) hgz2
  rw [← hz₁eq, ← hz₂eq, hz12]
  exact (Complex.exp_periodic.int_mul m) z₂

/-! ## Part 5: `hFun` on a preimage, the modulus identity, and surjectivity -/

theorem hFun_exp_eq {A : Set ℂ} {s : ℝ} (hs : 0 < s) {g : ℂ → ℂ}
    (hper : ∀ z ∈ expStrip A, g (z + 2 * (Real.pi : ℂ) * I) = g z + (s : ℂ) * I)
    {z : ℂ} (hz : z ∈ expStrip A) :
    hFun A s g (Complex.exp z) = Complex.exp ((2 * Real.pi / s : ℝ) * g z) := by
  have himg : Complex.exp z ∈ Complex.exp '' expStrip A := ⟨z, hz, rfl⟩
  have hinvmem : Function.invFunOn Complex.exp (expStrip A) (Complex.exp z) ∈ expStrip A :=
    Function.invFunOn_mem himg
  have hinveq : Complex.exp (Function.invFunOn Complex.exp (expStrip A) (Complex.exp z))
      = Complex.exp z := Function.invFunOn_eq himg
  show Complex.exp ((2 * Real.pi / s : ℝ) *
      g (Function.invFunOn Complex.exp (expStrip A) (Complex.exp z)))
      = Complex.exp ((2 * Real.pi / s : ℝ) * g z)
  exact exp_g_well_defined hs hper hinvmem hz hinveq

theorem re_real_mul (c : ℝ) (z : ℂ) : ((c : ℂ) * z).re = c * z.re := by
  simp [Complex.mul_re]

theorem norm_hFun_exp {A : Set ℂ} {s : ℝ} (hs : 0 < s) {g : ℂ → ℂ}
    (hper : ∀ z ∈ expStrip A, g (z + 2 * (Real.pi : ℂ) * I) = g z + (s : ℂ) * I)
    {z : ℂ} (hz : z ∈ expStrip A) :
    ‖hFun A s g (Complex.exp z)‖ = Real.exp ((2 * Real.pi / s : ℝ) * (g z).re) := by
  rw [hFun_exp_eq hs hper hz, Complex.norm_exp, re_real_mul]

theorem image_const_mul_strip {c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    (fun z : ℂ => (c : ℂ) * z) '' strip d = strip (c * d) := by
  ext w
  simp only [strip, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [re_real_mul]
    constructor
    · exact mul_pos hc hz.1
    · exact mul_lt_mul_of_pos_left hz.2 hc
  · rintro ⟨h1, h2⟩
    have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have hkey : (c : ℂ) * (w / (c : ℂ)) = w := by field_simp
    have hre := congrArg Complex.re hkey
    rw [re_real_mul] at hre
    have hxeq : (w / (c : ℂ)).re = w.re / c := by
      have h3 : (w / (c : ℂ)).re * c = w.re := by rw [mul_comm]; exact hre
      exact (eq_div_iff hc.ne').mpr h3
    refine ⟨w / (c : ℂ), ⟨?_, ?_⟩, hkey⟩
    · rw [hxeq]; exact div_pos h1 hc
    · rw [hxeq]; rw [div_lt_iff₀ hc]; linarith [h2, mul_comm c d]

theorem exists_preimage_of_mem_annulus {A : Set ℂ} {d s : ℝ} (hd : 0 < d) (hs : 0 < s)
    {g : ℂ → ℂ} (hg : IsConformalOnto g (expStrip A) (strip d))
    (hper : ∀ z ∈ expStrip A, g (z + 2 * (Real.pi : ℂ) * I) = g z + (s : ℂ) * I)
    (hAexp : A \ closedBall 0 1 = Complex.exp '' expStrip A)
    {w : ℂ} (hw1 : 1 < ‖w‖) (hw2 : ‖w‖ < Real.exp (2 * Real.pi * d / s)) :
    ∃ ζ ∈ A \ closedBall 0 1, hFun A s g ζ = w := by
  have hwne : w ≠ 0 := by intro h; rw [h] at hw1; norm_num at hw1
  set z' : ℂ := Complex.log w with hz'def
  have hz're : z'.re = Real.log ‖w‖ := Complex.log_re w
  have hz'mem : z' ∈ strip (2 * Real.pi * d / s) := by
    refine ⟨?_, ?_⟩
    · rw [hz're]; exact Real.log_pos hw1
    · rw [hz're]
      have hlt := Real.log_lt_log (lt_trans one_pos hw1) hw2
      rwa [Real.log_exp] at hlt
  have hcpos : (0 : ℝ) < 2 * Real.pi / s := by positivity
  have himgeq : (fun z : ℂ => ((2 * Real.pi / s : ℝ) : ℂ) * g z) '' expStrip A
      = strip (2 * Real.pi * d / s) := by
    have h1 : (fun z : ℂ => ((2 * Real.pi / s : ℝ) : ℂ) * z) '' strip d
        = strip (2 * Real.pi / s * d) := image_const_mul_strip hcpos hd
    rw [show (2 * Real.pi / s * d : ℝ) = 2 * Real.pi * d / s by ring] at h1
    rw [← hg.2.2, ← Set.image_comp] at h1
    exact h1
  rw [← himgeq] at hz'mem
  obtain ⟨z, hz, hzeq⟩ := hz'mem
  simp only at hzeq
  have hζre : (0 : ℝ) < z.re := hz.1
  refine ⟨Complex.exp z, ⟨hz.2, ?_⟩, ?_⟩
  · rw [mem_closedBall_zero_iff, Complex.norm_exp]
    exact not_le.mpr (by simpa using Real.exp_lt_exp.mpr hζre)
  · rw [hFun_exp_eq hs hper hz, hzeq, hz'def, Complex.exp_log hwne]

/-! ## Part 6: `A \ closedBall 0 1 = exp '' expStrip A` is a general fact, no extra hypothesis -/

theorem exp_expStrip_eq (A : Set ℂ) : Complex.exp '' expStrip A = A \ closedBall 0 1 := by
  ext ζ
  simp only [Set.mem_image, expStrip, Set.mem_setOf_eq, Set.mem_diff, mem_closedBall_zero_iff]
  constructor
  · rintro ⟨z, ⟨hzre, hzA⟩, rfl⟩
    refine ⟨hzA, ?_⟩
    rw [Complex.norm_exp]
    exact not_le.mpr (by simpa using Real.exp_lt_exp.mpr hzre)
  · rintro ⟨hζA, hζnorm⟩
    have hζgt1 : 1 < ‖ζ‖ := not_le.mp hζnorm
    have hζne : ζ ≠ 0 := norm_pos_iff.mp (lt_trans one_pos hζgt1)
    exact ⟨Complex.log ζ, ⟨by rw [Complex.log_re]; exact Real.log_pos hζgt1,
      by rwa [Complex.exp_log hζne]⟩, Complex.exp_log hζne⟩

/-! ## Part 7: final assembly -/

theorem conformallyEquivalent_annulus_of_periodic
    {A : Set ℂ} {d s : ℝ} {g : ℂ → ℂ}
    (hAo : IsOpen A) (hd : 0 < d) (hs : 0 < s)
    (hg : IsConformalOnto g (expStrip A) (strip d))
    (hper : ∀ z ∈ expStrip A, g (z + 2 * (Real.pi : ℂ) * I) = g z + (s : ℂ) * I) :
    ConformallyEquivalent (A \ closedBall 0 1)
      (annulus 1 (Real.exp (2 * Real.pi * d / s))) := by
  have hAexp : A \ closedBall 0 1 = Complex.exp '' expStrip A := (exp_expStrip_eq A).symm
  refine ⟨hFun A s g, ?_, ?_, ?_⟩
  · intro ζ hζ
    exact (differentiableAt_hFun hAo hs hg hper hAexp hζ).differentiableWithinAt
  · exact injOn_hFun hs hg hper hAexp
  · ext w
    simp only [annulus, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨ζ, hζ, rfl⟩
      obtain ⟨z, hz, hzeq⟩ : ζ ∈ Complex.exp '' expStrip A := hAexp ▸ hζ
      rw [← hzeq, hFun_exp_eq hs hper hz, Complex.norm_exp, re_real_mul]
      have hgzmem : g z ∈ strip d := hg.2.2 ▸ Set.mem_image_of_mem g hz
      have hcpos : (0 : ℝ) < 2 * Real.pi / s := by positivity
      constructor
      · calc (1 : ℝ) = Real.exp 0 := (Real.exp_zero).symm
          _ < Real.exp ((2 * Real.pi / s : ℝ) * (g z).re) :=
              Real.exp_lt_exp.mpr (mul_pos hcpos hgzmem.1)
      · calc Real.exp ((2 * Real.pi / s : ℝ) * (g z).re)
            < Real.exp ((2 * Real.pi / s : ℝ) * d) :=
              Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hgzmem.2 hcpos)
          _ = Real.exp (2 * Real.pi * d / s) := by rw [show (2 * Real.pi / s * d : ℝ)
              = 2 * Real.pi * d / s by ring]
    · intro hw
      obtain ⟨ζ, hζmem, hζeq⟩ :=
        exists_preimage_of_mem_annulus hd hs hg hper hAexp hw.1 hw.2
      exact ⟨ζ, hζmem, hζeq⟩
end LiZhongQC
