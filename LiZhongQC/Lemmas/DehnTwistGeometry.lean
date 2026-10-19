import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity

/-!
# Plane hyperbolic geometry for a Dehn twist (`s28m_`, for the infinitude in §28.1)

Let `Γ` be a Fuchsian group containing the dilation `g₀ : w ↦ l w` (`l > 1`) of smallest displacement, so that
the projected imaginary axis `L` is a simple closed geodesic of `ℍ/Γ`.  Write `ς w = Im w / ‖w‖ = sin (arg w)`
(`ς = 1` exactly on `L`, `ς (l w) = ς w`) and `N̄ₛ = {ς ≥ s}` for the closed collar.  The three results below are
the geometry used for the Dehn twist about `L`: the axis stabiliser (`s28m_stab_axis`), the embedded collar
(`s28m_collar`) and the *far-point lemma* (`s28m_far`): the component of `ℍ ∖ ⋃ γ N̄ₛ` next to a collar edge
reaches points arbitrarily close to the real axis (so a deck element that moves points of it by a bounded
hyperbolic distance is trivial).
-/

open Set Filter Topology
open scoped UpperHalfPlane

noncomputable section

namespace LiZhongQC

/-- Integer powers of the dilation `g₀` act as multiplication by `l ^ j`. -/
theorem s28m_far_zpow {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ)) (j : ℤ) (w : ℍ) :
    ((g₀ ^ j • w : ℍ) : ℂ) = (l : ℂ) ^ j * (w : ℂ) := by
  have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast (by linarith : l ≠ 0)
  induction j using Int.induction_on generalizing w with
  | zero => simp
  | succ i ih =>
    rw [zpow_add_one, mul_smul, ih, hdil, zpow_add_one₀ hl0]
    ring
  | pred i ih =>
    have h1 : ((g₀⁻¹ • w : ℍ) : ℂ) = (l : ℂ)⁻¹ * (w : ℂ) := by
      have := hdil (g₀⁻¹ • w)
      rw [smul_inv_smul] at this
      rw [this]
      field_simp
    rw [zpow_sub_one, mul_smul, ih, h1, zpow_sub_one₀ hl0]
    ring

/-- `ς = Im / ‖·‖` is invariant under `g₀ ^ j`. -/
theorem s28m_far_sig_zpow {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ)) (j : ℤ) (w : ℍ) :
    (g₀ ^ j • w : ℍ).im / ‖((g₀ ^ j • w : ℍ) : ℂ)‖ = w.im / ‖(w : ℂ)‖ := by
  have h := s28m_far_zpow hl hdil j w
  have hpos : (0 : ℝ) < l ^ j := zpow_pos (by linarith) j
  have him : (g₀ ^ j • w : ℍ).im = l ^ j * w.im := by
    have hc : ((l : ℂ) ^ j) = ((l ^ j : ℝ) : ℂ) := (Complex.ofReal_zpow l j).symm
    have := congrArg Complex.im h
    rw [hc, Complex.im_ofReal_mul] at this
    simpa [UpperHalfPlane.coe_im] using this
  have hn : ‖((g₀ ^ j • w : ℍ) : ℂ)‖ = l ^ j * ‖(w : ℂ)‖ := by
    rw [h, norm_mul]
    congr 1
    rw [← Complex.ofReal_zpow, Complex.norm_real, Real.norm_of_nonneg hpos.le]
  rw [him, hn]
  have : (0 : ℝ) < ‖(w : ℂ)‖ := norm_pos_iff.2 w.ne_zero
  field_simp

/-- Every point can be moved by a power of `g₀` into the annulus `1 ≤ ‖w‖ < l`. -/
theorem s28m_far_reduce {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ)) (w : ℍ) :
    ∃ j : ℤ, 1 ≤ ‖((g₀ ^ j • w : ℍ) : ℂ)‖ ∧ ‖((g₀ ^ j • w : ℍ) : ℂ)‖ < l := by
  have hw : (0 : ℝ) < ‖(w : ℂ)‖ := norm_pos_iff.2 w.ne_zero
  have hll : 0 < Real.log l := Real.log_pos hl
  set k : ℤ := ⌊Real.log ‖(w : ℂ)‖ / Real.log l⌋ with hk
  refine ⟨-k, ?_⟩
  have h := s28m_far_zpow hl hdil (-k) w
  have hn : ‖((g₀ ^ (-k) • w : ℍ) : ℂ)‖ = l ^ (-k) * ‖(w : ℂ)‖ := by
    rw [h, norm_mul, ← Complex.ofReal_zpow, Complex.norm_real,
      Real.norm_of_nonneg (zpow_pos (by linarith) _).le]
  rw [hn]
  have hk1 : (k : ℝ) ≤ Real.log ‖(w : ℂ)‖ / Real.log l := Int.floor_le _
  have hk2 : Real.log ‖(w : ℂ)‖ / Real.log l < k + 1 := Int.lt_floor_add_one _
  have e1 : (k : ℝ) * Real.log l ≤ Real.log ‖(w : ℂ)‖ := by
    have := (le_div_iff₀ hll).1 hk1
    linarith
  have e2 : Real.log ‖(w : ℂ)‖ < ((k : ℝ) + 1) * Real.log l := (div_lt_iff₀ hll).1 hk2
  have hlk : l ^ (k : ℤ) = Real.exp (k * Real.log l) := by
    rw [← Real.log_zpow, Real.exp_log (zpow_pos (by linarith) _)]
  have hlk1 : l ^ ((k : ℤ) + 1) = Real.exp ((k + 1) * Real.log l) := by
    rw [zpow_add_one₀ (by linarith), hlk, add_mul, one_mul, Real.exp_add, Real.exp_log (by linarith)]
  have hlow : l ^ (k : ℤ) ≤ ‖(w : ℂ)‖ := by
    rw [hlk, ← Real.exp_log hw]
    exact Real.exp_le_exp.2 e1
  have hup : ‖(w : ℂ)‖ < l ^ ((k : ℤ) + 1) := by
    rw [hlk1, ← Real.exp_log hw]
    exact Real.exp_lt_exp.2 e2
  have hp : (0 : ℝ) < l ^ (k : ℤ) := zpow_pos (by linarith) _
  have hinv : l ^ (-k) = (l ^ k)⁻¹ := zpow_neg l k
  rw [hinv]
  constructor
  · rw [inv_mul_eq_div, le_div_iff₀ hp]; linarith
  · rw [inv_mul_eq_div, div_lt_iff₀ hp]
    have : l ^ ((k : ℤ) + 1) = l ^ k * l := zpow_add_one₀ (by linarith) k
    rw [this] at hup
    linarith


/-- The compact piece `{ς ≥ a, 1 ≤ ‖w‖ ≤ l}` of the collar. -/
theorem s28m_far_compact {l a : ℝ} (ha : 0 < a) :
    IsCompact {w : ℍ | a ≤ w.im / ‖(w : ℂ)‖ ∧ 1 ≤ ‖(w : ℂ)‖ ∧ ‖(w : ℂ)‖ ≤ l} := by
  set S : Set ℂ := {z : ℂ | a * ‖z‖ ≤ z.im ∧ 1 ≤ ‖z‖ ∧ ‖z‖ ≤ l} with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have c1 : IsClosed {z : ℂ | a * ‖z‖ ≤ z.im} :=
        isClosed_le (f := fun z : ℂ => a * ‖z‖) (g := fun z : ℂ => z.im) (by fun_prop) (by fun_prop)
      have c2 : IsClosed {z : ℂ | 1 ≤ ‖z‖} :=
        isClosed_le (f := fun _ : ℂ => (1 : ℝ)) (g := fun z : ℂ => ‖z‖) (by fun_prop) (by fun_prop)
      have c3 : IsClosed {z : ℂ | ‖z‖ ≤ l} :=
        isClosed_le (f := fun z : ℂ => ‖z‖) (g := fun _ : ℂ => l) (by fun_prop) (by fun_prop)
      exact c1.inter (c2.inter c3)
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := l)).subset ?_
      intro z hz
      simpa using hz.2.2
  have himg : (fun w : ℍ => (w : ℂ)) '' {w : ℍ | a ≤ w.im / ‖(w : ℂ)‖ ∧ 1 ≤ ‖(w : ℂ)‖ ∧ ‖(w : ℂ)‖ ≤ l} = S := by
    ext z
    constructor
    · rintro ⟨w, ⟨h1, h2, h3⟩, rfl⟩
      refine ⟨?_, h2, h3⟩
      have hw : (0 : ℝ) < ‖(w : ℂ)‖ := norm_pos_iff.2 w.ne_zero
      have := (le_div_iff₀ hw).1 h1
      simpa [UpperHalfPlane.coe_im] using this
    · rintro ⟨h1, h2, h3⟩
      have hpos : 0 < z.im := by
        have : 0 < a * ‖z‖ := mul_pos ha (by linarith)
        linarith
      refine ⟨⟨z, hpos⟩, ⟨?_, h2, h3⟩, rfl⟩
      have hw : (0 : ℝ) < ‖z‖ := by linarith
      show a ≤ z.im / ‖z‖
      rw [le_div_iff₀ hw]
      exact h1
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff, himg]
  exact hSc


/-- The union of the translates `δ {ς ≥ s}` over a subset `D ⊆ Γ`, stable under right multiplication by powers of
`g₀`, is closed (local finiteness of the translates of a compact piece). -/
theorem s28m_far_isClosed_union {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ)) {s : ℝ} (hs : 0 < s)
    {D : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hDΓ : D ⊆ Γ) (hD : ∀ δ ∈ D, ∀ j : ℤ, δ * g₀ ^ j ∈ D) :
    IsClosed {w : ℍ | ∃ δ ∈ D, ∃ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ ∧ δ • w' = w} := by
  set Q : Set ℍ := {w : ℍ | s ≤ w.im / ‖(w : ℂ)‖ ∧ 1 ≤ ‖(w : ℂ)‖ ∧ ‖(w : ℂ)‖ ≤ l} with hQ
  have hQc : IsCompact Q := s28m_far_compact hs
  have heq : {w : ℍ | ∃ δ ∈ D, ∃ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ ∧ δ • w' = w} =
      ⋃ δ : D, (fun z => (δ : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z) '' Q := by
    ext w
    simp only [mem_ofPred_eq, mem_iUnion, mem_image]
    constructor
    · rintro ⟨δ, hδ, w', hw', rfl⟩
      obtain ⟨j, hj1, hj2⟩ := s28m_far_reduce hl hdil w'
      have hsig := s28m_far_sig_zpow hl hdil j w'
      refine ⟨⟨δ * g₀ ^ (-j), hD δ hδ _⟩, g₀ ^ j • w', ⟨?_, hj1, hj2.le⟩, ?_⟩
      · rw [hsig]; exact hw'
      · show (δ * g₀ ^ (-j)) • (g₀ ^ j • w') = δ • w'
        rw [← mul_smul, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    · rintro ⟨δ, w', ⟨h1, _, _⟩, rfl⟩
      exact ⟨δ, δ.2, w', h1, rfl⟩
  rw [heq]
  have hlf := (s30b_locallyFinite hΓ hQc).comp_injective
    (g := fun δ : D => (⟨δ, hDΓ δ.2⟩ : Γ)) (fun a b h => Subtype.ext (by
      have := congrArg (fun z : Γ => (z : Matrix.SpecialLinearGroup (Fin 2) ℝ)) h
      simpa using this))
  exact hlf.isClosed_iUnion fun δ => (hQc.image (continuous_const_smul _)).isClosed

/-- The union of the translates `γ {ς ≥ s}` is closed. -/
theorem s28m_far_isClosed_bad {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg₀ : g₀ ∈ Γ) {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ)) {s : ℝ} (hs : 0 < s) :
    IsClosed {w : ℍ | ∃ γ ∈ Γ, ∃ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ ∧ γ • w' = w} :=
  s28m_far_isClosed_union hΓ hl hdil hs (D := (Γ : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ))) subset_rfl
    fun _ hδ j => Γ.mul_mem hδ (Γ.zpow_mem hg₀ j)

/-- The complement `E` of the union of the translates is open. -/
theorem s28m_far_isOpen_E {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg₀ : g₀ ∈ Γ) {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ)) {s : ℝ} (hs : 0 < s) :
    IsOpen {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w} := by
  have h := (s28m_far_isClosed_bad hΓ hg₀ hl hdil hs).isOpen_compl
  convert h using 1
  ext w
  simp only [mem_ofPred_eq, mem_compl_iff, not_exists, not_and]


/-- Scaling `w ↦ exp u * w` of `ℍ`, jointly continuous in `(u, w)`. -/
theorem s28m_far_scale :
    ∃ F : ℝ → ℍ → ℍ, (∀ u w, ((F u w : ℍ) : ℂ) = (Real.exp u : ℂ) * (w : ℂ)) ∧
      Continuous (fun q : ℝ × ℍ => F q.1 q.2) := by
  have hpos : ∀ (u : ℝ) (w : ℍ), 0 < ((Real.exp u : ℂ) * (w : ℂ)).im := by
    intro u w
    rw [Complex.im_ofReal_mul]
    exact mul_pos (Real.exp_pos u) w.im_pos
  refine ⟨fun u w => ⟨(Real.exp u : ℂ) * (w : ℂ), hpos u w⟩, fun u w => rfl, ?_⟩
  refine UpperHalfPlane.isEmbedding_coe.continuous_iff.2 ?_
  show Continuous (fun q : ℝ × ℍ => (Real.exp q.1 : ℂ) * (q.2 : ℂ))
  fun_prop

/-- A point of the shell `s₁ ≤ ς < s` lies in `E`. -/
theorem s28m_far_shell_mem {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ)) {s₁ s : ℝ}
    (hdisj : ∀ γ ∈ Γ, (∀ j : ℤ, ∃ w : ℍ, γ • w ≠ g₀ ^ j • w) →
      ∀ w w' : ℍ, s₁ ≤ w.im / ‖(w : ℂ)‖ → s₁ ≤ w'.im / ‖(w' : ℂ)‖ → γ • w ≠ w')
    (hs₁s : s₁ < s) {z : ℍ} (hz₁ : s₁ ≤ z.im / ‖(z : ℂ)‖) (hz₂ : z.im / ‖(z : ℂ)‖ < s) :
    z ∈ {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w} := by
  intro γ hγ w' hw' heq
  by_cases hp : ∀ j : ℤ, ∃ w : ℍ, γ • w ≠ g₀ ^ j • w
  · exact hdisj γ hγ hp w' z (by linarith) hz₁ heq
  · push Not at hp
    obtain ⟨j, hj⟩ := hp
    rw [hj w'] at heq
    have := s28m_far_sig_zpow hl hdil j w'
    rw [heq] at this
    linarith

/-- The set `E` is invariant under `g₀ ^ j`. -/
theorem s28m_far_E_invariant {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg₀ : g₀ ∈ Γ) {s : ℝ} (j : ℤ) {w : ℍ}
    (hw : w ∈ {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w}) :
    g₀ ^ j • w ∈ {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w} := by
  intro γ hγ w' hw' heq
  apply hw (g₀ ^ (-j) * γ) (Γ.mul_mem (Γ.zpow_mem hg₀ _) hγ) w' hw'
  rw [mul_smul, heq, ← mul_smul, ← zpow_add, neg_add_cancel, zpow_zero, one_smul]


/-- `ς (exp u * w) = ς w`. -/
theorem s28m_far_scale_sig {F : ℝ → ℍ → ℍ} (hF : ∀ u w, ((F u w : ℍ) : ℂ) = (Real.exp u : ℂ) * (w : ℂ))
    (u : ℝ) (w : ℍ) : (F u w).im / ‖((F u w : ℍ) : ℂ)‖ = w.im / ‖(w : ℂ)‖ := by
  have h1 : (F u w).im = Real.exp u * w.im := by
    have := congrArg Complex.im (hF u w)
    rw [Complex.im_ofReal_mul] at this
    simpa using this
  have h2 : ‖((F u w : ℍ) : ℂ)‖ = Real.exp u * ‖(w : ℂ)‖ := by
    rw [hF, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos u).le]
  rw [h1, h2]
  have : (0 : ℝ) < ‖(w : ℂ)‖ := norm_pos_iff.2 w.ne_zero
  have := Real.exp_pos u
  field_simp

/-- `g₀ ^ j` is the scaling by `exp (j log l)`. -/
theorem s28m_far_zpow_eq_scale {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ)) {F : ℝ → ℍ → ℍ}
    (hF : ∀ u w, ((F u w : ℍ) : ℂ) = (Real.exp u : ℂ) * (w : ℂ)) (j : ℤ) (w : ℍ) :
    g₀ ^ j • w = F (j * Real.log l) w := by
  apply UpperHalfPlane.ext
  rw [s28m_far_zpow hl hdil, hF]
  have h : Real.exp (j * Real.log l) = l ^ j := by
    rw [← Real.log_zpow, Real.exp_log (zpow_pos (by linarith) _)]
  rw [h, Complex.ofReal_zpow]

/-- The component of a shell point is invariant under `g₀ ^ j`. -/
theorem s28m_far_comp_zpow {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg₀ : g₀ ∈ Γ) {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ)) {s₁ s : ℝ}
    (hdisj : ∀ γ ∈ Γ, (∀ j : ℤ, ∃ w : ℍ, γ • w ≠ g₀ ^ j • w) →
      ∀ w w' : ℍ, s₁ ≤ w.im / ‖(w : ℂ)‖ → s₁ ≤ w'.im / ‖(w' : ℂ)‖ → γ • w ≠ w')
    (hs₁s : s₁ < s) {p : ℍ} (hp₁ : s₁ ≤ p.im / ‖(p : ℂ)‖) (hp₂ : p.im / ‖(p : ℂ)‖ < s) (j : ℤ) {w : ℍ}
    (hw : w ∈ connectedComponentIn {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w} p) :
    g₀ ^ j • w ∈ connectedComponentIn {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w} p := by
  obtain ⟨F, hF, hFc⟩ := s28m_far_scale
  set E : Set ℍ := {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w} with hE
  have hpE : p ∈ E := s28m_far_shell_mem hl hdil hdisj hs₁s hp₁ hp₂
  -- `g₀ ^ j • p` lies in the component of `p`
  have hjp : g₀ ^ j • p ∈ connectedComponentIn E p := by
    have hS : (fun u => F u p) '' Set.uIcc 0 (j * Real.log l) ⊆ connectedComponentIn E p := by
      have hcu : Continuous (fun u : ℝ => F u p) :=
        hFc.comp (by fun_prop : Continuous (fun u : ℝ => (u, p)))
      refine IsPreconnected.subset_connectedComponentIn (isPreconnected_uIcc.image _
        hcu.continuousOn) ⟨0, by simp, ?_⟩ ?_
      · have := hF 0 p
        apply UpperHalfPlane.ext
        simp [this]
      · rintro _ ⟨u, -, rfl⟩
        exact s28m_far_shell_mem hl hdil hdisj hs₁s (by rw [s28m_far_scale_sig hF]; exact hp₁)
          (by rw [s28m_far_scale_sig hF]; exact hp₂)
    rw [s28m_far_zpow_eq_scale hl hdil hF]
    exact hS ⟨j * Real.log l, right_mem_uIcc, rfl⟩
  -- the image of the component under `g₀ ^ j` is connected, inside `E`, and meets the component
  have himg : (fun z => g₀ ^ j • z) '' connectedComponentIn E p ⊆ connectedComponentIn E (g₀ ^ j • p) := by
    refine IsPreconnected.subset_connectedComponentIn ?_ ⟨p, mem_connectedComponentIn hpE, rfl⟩ ?_
    · exact (isPreconnected_connectedComponentIn).image _ (continuous_const_smul _).continuousOn
    · rintro _ ⟨z, hz, rfl⟩
      exact s28m_far_E_invariant hg₀ j (connectedComponentIn_subset E p hz)
  rw [connectedComponentIn_eq hjp]
  exact himg ⟨w, hw, rfl⟩


/-- A point of `E` in the closure of a component of `E` belongs to the component. -/
theorem s28m_far_closure_mem {E : Set ℍ} (hE : IsOpen E) {p x : ℍ} (hx : x ∈ E)
    (hcl : x ∈ closure (connectedComponentIn E p)) : x ∈ connectedComponentIn E p := by
  obtain ⟨V, ⟨hVo, hxV, hVc⟩, hVE⟩ := (LocallyConnectedSpace.open_connected_basis x).mem_iff.1 (hE.mem_nhds hx)
  obtain ⟨c, hcV, hcC⟩ := mem_closure_iff.1 hcl V hVo hxV
  have hVsub : V ⊆ connectedComponentIn E c := hVc.isPreconnected.subset_connectedComponentIn hcV hVE
  rw [connectedComponentIn_eq hcC]
  exact hVsub hxV

/-- `ς = Im / ‖·‖` has no local minimum on `ℍ`: horizontal translation away from the imaginary axis lowers it. -/
theorem s28m_far_no_local_min (x : ℍ) {U : Set ℍ} (hU : U ∈ 𝓝 x) :
    ∃ y ∈ U, y.im / ‖(y : ℂ)‖ < x.im / ‖(x : ℂ)‖ := by
  set c : ℝ := if 0 ≤ (x : ℂ).re then 1 else -1 with hc
  have hc2 : c ^ 2 = 1 := by
    by_cases h : 0 ≤ (x : ℂ).re
    · simp only [hc, h, ↓reduceIte]; norm_num
    · simp only [hc, h, ↓reduceIte]; norm_num
  have hcx : 0 ≤ c * (x : ℂ).re := by
    by_cases h : 0 ≤ (x : ℂ).re
    · simp only [hc, h, ↓reduceIte]; linarith
    · simp only [hc, h, ↓reduceIte]; push Not at h; linarith
  have hpos : ∀ τ : ℝ, 0 < (((x : ℂ) + ((c * τ : ℝ) : ℂ))).im := by
    intro τ
    simpa using x.im_pos
  let y : ℝ → ℍ := fun τ => ⟨(x : ℂ) + ((c * τ : ℝ) : ℂ), hpos τ⟩
  have hycont : Continuous y := by
    refine UpperHalfPlane.isEmbedding_coe.continuous_iff.2 ?_
    show Continuous (fun τ : ℝ => (x : ℂ) + ((c * τ : ℝ) : ℂ))
    fun_prop
  have hy0 : y 0 = x := by
    apply UpperHalfPlane.ext
    simp [y]
  have hev : ∀ᶠ τ in 𝓝[>] (0 : ℝ), y τ ∈ U := by
    have : ∀ᶠ τ in 𝓝 (0 : ℝ), y τ ∈ U := by
      have h0 : Tendsto y (𝓝 0) (𝓝 (y 0)) := hycont.tendsto 0
      rw [hy0] at h0
      exact h0.eventually hU
    exact nhdsWithin_le_nhds this
  obtain ⟨τ, hτU, hτ⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨y τ, hτU, ?_⟩
  have hτ' : 0 < τ := hτ
  have him : (y τ).im = x.im := by simp [y]
  have hxn : (0 : ℝ) < ‖(x : ℂ)‖ := norm_pos_iff.2 x.ne_zero
  have hnorm : ‖(x : ℂ)‖ < ‖((y τ : ℍ) : ℂ)‖ := by
    have e1 : ‖((y τ : ℍ) : ℂ)‖ ^ 2 = ‖(x : ℂ)‖ ^ 2 + 2 * (c * (x : ℂ).re) * τ + τ ^ 2 := by
      have hh : ((y τ : ℍ) : ℂ) = (x : ℂ) + ((c * τ : ℝ) : ℂ) := rfl
      rw [hh, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
      have : (c * τ) ^ 2 = τ ^ 2 := by rw [mul_pow, hc2, one_mul]
      nlinarith [this]
    have e2 : ‖(x : ℂ)‖ ^ 2 < ‖((y τ : ℍ) : ℂ)‖ ^ 2 := by
      rw [e1]
      have : 0 ≤ 2 * (c * (x : ℂ).re) * τ := by positivity
      nlinarith [sq_pos_of_pos hτ']
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) e2
  rw [him]
  exact div_lt_div_of_pos_left x.im_pos hxn hnorm


/-- The value of `ς` at `γ • z` in terms of the entries of `γ`: `ς (γ z) = Im z / (‖c z + d‖ ‖a z + b‖)`. -/
theorem s28m_far_sig_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    (γ • z : ℍ).im / ‖((γ • z : ℍ) : ℂ)‖ =
      z.im / (‖((γ 1 0 : ℝ) : ℂ) * (z : ℂ) + ((γ 1 1 : ℝ) : ℂ)‖ *
        ‖((γ 0 0 : ℝ) : ℂ) * (z : ℂ) + ((γ 0 1 : ℝ) : ℂ)‖) := by
  have hc := UpperHalfPlane.coe_specialLinearGroup_apply γ z
  simp only [Algebra.algebraMap_self_apply] at hc
  set n : ℂ := ((γ 0 0 : ℝ) : ℂ) * (z : ℂ) + ((γ 0 1 : ℝ) : ℂ) with hn
  set d : ℂ := ((γ 1 0 : ℝ) : ℂ) * (z : ℂ) + ((γ 1 1 : ℝ) : ℂ) with hd
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  have hd0 : d ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    have hre := congrArg Complex.re h0
    simp only [hd, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.zero_im, Complex.add_re, Complex.mul_re, Complex.zero_re, sub_zero] at him hre
    have hz : 0 < (z : ℂ).im := z.im_pos
    rcases mul_eq_zero.1 him with h1 | h1
    · rw [h1] at hre
      simp at hre
      rw [h1, hre] at hdet
      simp at hdet
    · exact absurd h1 hz.ne'
  have hnd : 0 < Complex.normSq d := Complex.normSq_pos.2 hd0
  have him : (γ • z : ℍ).im = z.im / Complex.normSq d := by
    have h1 : ((γ • z : ℍ) : ℂ).im = (n / d).im := by rw [hc]
    rw [Complex.div_im] at h1
    have h2 : (γ • z : ℍ).im = n.im * d.re / Complex.normSq d - n.re * d.im / Complex.normSq d := h1
    rw [h2, ← sub_div]
    congr 1
    simp only [hn, hd, Complex.add_im, Complex.mul_im, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, sub_zero]
    have e : (z : ℂ).im = z.im := rfl
    rw [e]
    linear_combination z.im * hdet
  have hnorm : ‖((γ • z : ℍ) : ℂ)‖ = ‖n‖ / ‖d‖ := by rw [hc, norm_div]
  rw [him, hnorm, Complex.normSq_eq_norm_sq]
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd0
  by_cases hn0 : ‖n‖ = 0
  · simp [hn0]
  · field_simp


/-- **Ends of an edge.**  If `γ` does not preserve the imaginary axis (`a c ≠ 0` or `b d ≠ 0`), then `ς (γ z)` is
arbitrarily small along the ray `u ↦ exp u * x`. -/
theorem s28m_far_endpoint {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (h : γ 0 0 * γ 1 0 ≠ 0 ∨ γ 0 1 * γ 1 1 ≠ 0) {F : ℝ → ℍ → ℍ}
    (hF : ∀ u w, ((F u w : ℍ) : ℂ) = (Real.exp u : ℂ) * (w : ℂ)) (x : ℍ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℝ, (γ • F u x : ℍ).im / ‖((γ • F u x : ℍ) : ℂ)‖ < ε := by
  set a : ℝ := γ 0 0
  set b : ℝ := γ 0 1
  set c : ℝ := γ 1 0
  set d : ℝ := γ 1 1
  have hxn : (0 : ℝ) < ‖(x : ℂ)‖ := norm_pos_iff.2 x.ne_zero
  have hform : ∀ u : ℝ, (γ • F u x : ℍ).im / ‖((γ • F u x : ℍ) : ℂ)‖ =
      Real.exp u * x.im / (‖(c : ℂ) * ((Real.exp u : ℂ) * (x : ℂ)) + (d : ℂ)‖ *
        ‖(a : ℂ) * ((Real.exp u : ℂ) * (x : ℂ)) + (b : ℂ)‖) := by
    intro u
    rw [s28m_far_sig_smul, hF]
    have : (F u x).im = Real.exp u * x.im := by
      have := congrArg Complex.im (hF u x)
      rw [Complex.im_ofReal_mul] at this
      simpa using this
    rw [this]
  rcases h with hac | hbd
  · -- `u → +∞`
    have hform' : ∀ u : ℝ, (γ • F u x : ℍ).im / ‖((γ • F u x : ℍ) : ℂ)‖ =
        x.im / (Real.exp u * (‖(c : ℂ) * (x : ℂ) + (d : ℂ) * (Real.exp (-u) : ℂ)‖ *
          ‖(a : ℂ) * (x : ℂ) + (b : ℂ) * (Real.exp (-u) : ℂ)‖)) := by
      intro u
      rw [hform]
      have e1 : (c : ℂ) * ((Real.exp u : ℂ) * (x : ℂ)) + (d : ℂ) =
          (Real.exp u : ℂ) * ((c : ℂ) * (x : ℂ) + (d : ℂ) * (Real.exp (-u) : ℂ)) := by
        have : (Real.exp u : ℂ) * (Real.exp (-u) : ℂ) = 1 := by
          rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
        linear_combination (d : ℂ) * (-this)
      have e2 : (a : ℂ) * ((Real.exp u : ℂ) * (x : ℂ)) + (b : ℂ) =
          (Real.exp u : ℂ) * ((a : ℂ) * (x : ℂ) + (b : ℂ) * (Real.exp (-u) : ℂ)) := by
        have : (Real.exp u : ℂ) * (Real.exp (-u) : ℂ) = 1 := by
          rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
        linear_combination (b : ℂ) * (-this)
      rw [e1, e2, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos u).le]
      have := Real.exp_pos u
      set A := ‖(c : ℂ) * (x : ℂ) + (d : ℂ) * (Real.exp (-u) : ℂ)‖ with hA
      set B := ‖(a : ℂ) * (x : ℂ) + (b : ℂ) * (Real.exp (-u) : ℂ)‖ with hB
      rcases eq_or_ne A 0 with hA0 | hA0
      · simp [hA0]
      rcases eq_or_ne B 0 with hB0 | hB0
      · simp [hB0]
      field_simp
    have hP : Tendsto (fun u : ℝ => ‖(c : ℂ) * (x : ℂ) + (d : ℂ) * (Real.exp (-u) : ℂ)‖ *
        ‖(a : ℂ) * (x : ℂ) + (b : ℂ) * (Real.exp (-u) : ℂ)‖) atTop (𝓝 (‖(c : ℂ) * (x : ℂ)‖ * ‖(a : ℂ) * (x : ℂ)‖)) := by
      have h0 : Tendsto (fun u : ℝ => (Real.exp (-u) : ℂ)) atTop (𝓝 0) := by
        simpa only [Complex.ofReal_zero, Function.comp_def] using
          (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
      have h1 : Tendsto (fun u : ℝ => (c : ℂ) * (x : ℂ) + (d : ℂ) * (Real.exp (-u) : ℂ)) atTop
          (𝓝 ((c : ℂ) * (x : ℂ) + (d : ℂ) * 0)) := tendsto_const_nhds.add (tendsto_const_nhds.mul h0)
      have h2 : Tendsto (fun u : ℝ => (a : ℂ) * (x : ℂ) + (b : ℂ) * (Real.exp (-u) : ℂ)) atTop
          (𝓝 ((a : ℂ) * (x : ℂ) + (b : ℂ) * 0)) := tendsto_const_nhds.add (tendsto_const_nhds.mul h0)
      simp only [mul_zero, add_zero] at h1 h2
      exact h1.norm.mul h2.norm
    have hpos : 0 < ‖(c : ℂ) * (x : ℂ)‖ * ‖(a : ℂ) * (x : ℂ)‖ := by
      have hc : c ≠ 0 := fun h0 => hac (mul_eq_zero_of_right _ h0)
      have ha : a ≠ 0 := fun h0 => hac (mul_eq_zero_of_left h0 _)
      have hx0 : (x : ℂ) ≠ 0 := x.ne_zero
      exact mul_pos (norm_pos_iff.2 (mul_ne_zero (by exact_mod_cast hc) hx0))
        (norm_pos_iff.2 (mul_ne_zero (by exact_mod_cast ha) hx0))
    have hlim : Tendsto (fun u : ℝ => Real.exp u * (‖(c : ℂ) * (x : ℂ) + (d : ℂ) * (Real.exp (-u) : ℂ)‖ *
        ‖(a : ℂ) * (x : ℂ) + (b : ℂ) * (Real.exp (-u) : ℂ)‖)) atTop atTop :=
      Real.tendsto_exp_atTop.atTop_mul_pos hpos hP
    have hfin : Tendsto (fun u : ℝ => x.im / (Real.exp u * (‖(c : ℂ) * (x : ℂ) + (d : ℂ) * (Real.exp (-u) : ℂ)‖ *
        ‖(a : ℂ) * (x : ℂ) + (b : ℂ) * (Real.exp (-u) : ℂ)‖))) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hlim
    obtain ⟨u, hu⟩ := (hfin.eventually (gt_mem_nhds hε)).exists
    exact ⟨u, by rw [hform']; exact hu⟩
  · -- `u → -∞`
    have hnum : Tendsto (fun u : ℝ => Real.exp u * x.im) atBot (𝓝 0) := by
      simpa using Real.tendsto_exp_atBot.mul_const x.im
    have h0 : Tendsto (fun u : ℝ => (Real.exp u : ℂ)) atBot (𝓝 0) := by
      simpa only [Complex.ofReal_zero, Function.comp_def] using
        (Complex.continuous_ofReal.tendsto 0).comp Real.tendsto_exp_atBot
    have h1 : Tendsto (fun u : ℝ => (c : ℂ) * ((Real.exp u : ℂ) * (x : ℂ)) + (d : ℂ)) atBot
        (𝓝 ((c : ℂ) * (0 * (x : ℂ)) + (d : ℂ))) :=
      (tendsto_const_nhds.mul (h0.mul tendsto_const_nhds)).add tendsto_const_nhds
    have h2 : Tendsto (fun u : ℝ => (a : ℂ) * ((Real.exp u : ℂ) * (x : ℂ)) + (b : ℂ)) atBot
        (𝓝 ((a : ℂ) * (0 * (x : ℂ)) + (b : ℂ))) :=
      (tendsto_const_nhds.mul (h0.mul tendsto_const_nhds)).add tendsto_const_nhds
    simp only [zero_mul, mul_zero, zero_add] at h1 h2
    have hden : Tendsto (fun u : ℝ => ‖(c : ℂ) * ((Real.exp u : ℂ) * (x : ℂ)) + (d : ℂ)‖ *
        ‖(a : ℂ) * ((Real.exp u : ℂ) * (x : ℂ)) + (b : ℂ)‖) atBot (𝓝 (‖(d : ℂ)‖ * ‖(b : ℂ)‖)) :=
      h1.norm.mul h2.norm
    have hne : ‖(d : ℂ)‖ * ‖(b : ℂ)‖ ≠ 0 := by
      have hb : b ≠ 0 := fun h0 => hbd (mul_eq_zero_of_left h0 _)
      have hd : d ≠ 0 := fun h0 => hbd (mul_eq_zero_of_right _ h0)
      simp [hb, hd]
    have hfin := hnum.div hden hne
    rw [zero_div] at hfin
    obtain ⟨u, hu⟩ := (hfin.eventually (gt_mem_nhds hε)).exists
    exact ⟨u, by rw [hform]; exact hu⟩


/-- **Edge propagation.**  If one point `γ x₀` of the edge `γ {ς = s}` of a translated collar lies in the closure of a
component `C` of `E`, so does the whole edge `u ↦ γ (exp u * x₀)`.  (Locally the other translates stay away, so the
side of the edge outside the collar is connected and lies in `E`; sliding along the edge keeps us in `C`.) -/
theorem s28m_far_propagate {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg₀ : g₀ ∈ Γ) {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ)) {s₁ s : ℝ} (hs₁ : 0 < s₁) (hs₁s : s₁ < s)
    (hdisj : ∀ γ ∈ Γ, (∀ j : ℤ, ∃ w : ℍ, γ • w ≠ g₀ ^ j • w) →
      ∀ w w' : ℍ, s₁ ≤ w.im / ‖(w : ℂ)‖ → s₁ ≤ w'.im / ‖(w' : ℂ)‖ → γ • w ≠ w')
    {F : ℝ → ℍ → ℍ} (hF : ∀ u w, ((F u w : ℍ) : ℂ) = (Real.exp u : ℂ) * (w : ℂ))
    (hFc : Continuous (fun q : ℝ × ℍ => F q.1 q.2))
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ) {x₀ : ℍ} (hx₀ : x₀.im / ‖(x₀ : ℂ)‖ = s)
    {C : Set ℍ} (hCE : C ⊆ {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w})
    (hC : ∀ c ∈ C, C = connectedComponentIn {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w} c)
    (hcl : γ • x₀ ∈ closure C) (u : ℝ) : γ • F u x₀ ∈ closure C := by
  set E : Set ℍ := {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w} with hE
  have hs : 0 < s := by linarith
  have hF0 : F 0 x₀ = x₀ := by
    apply UpperHalfPlane.ext
    simp [hF]
  have hFadd : ∀ r u₀ : ℝ, ∀ y : ℍ, F r (F u₀ y) = F (r + u₀) y := by
    intro r u₀ y
    apply UpperHalfPlane.ext
    rw [hF, hF, hF, Real.exp_add, Complex.ofReal_mul]
    ring
  let T : Set ℝ := {u | γ • F u x₀ ∈ closure C}
  have hTc : IsClosed T := by
    have hcont : Continuous (fun u : ℝ => γ • F u x₀) :=
      (continuous_const_smul γ).comp (hFc.comp (by fun_prop : Continuous (fun u : ℝ => (u, x₀))))
    exact isClosed_closure.preimage hcont
  have hTo : IsOpen T := by
    rw [isOpen_iff_mem_nhds]
    intro u₀ hu₀
    -- the relevant data at `x₁ = exp u₀ * x₀`
    set x₁ : ℍ := F u₀ x₀ with hx₁
    have hx₁s : x₁.im / ‖(x₁ : ℂ)‖ = s := by rw [hx₁, s28m_far_scale_sig hF]; exact hx₀
    have hz₁ : γ • x₁ ∈ closure C := hu₀
    -- the set `D` of group elements whose collar differs from `γ {ς ≥ s}`
    set D : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) :=
      {δ | δ ∈ Γ ∧ ¬ ∃ j : ℤ, ∀ w : ℍ, δ • w = γ • g₀ ^ j • w} with hD
    have hDΓ : D ⊆ Γ := fun δ hδ => hδ.1
    have hDm : ∀ δ ∈ D, ∀ j : ℤ, δ * g₀ ^ j ∈ D := by
      rintro δ ⟨hδΓ, hδ⟩ j
      refine ⟨Γ.mul_mem hδΓ (Γ.zpow_mem hg₀ j), ?_⟩
      rintro ⟨k, hk⟩
      apply hδ
      refine ⟨k - j, fun w => ?_⟩
      have h1 : (δ * g₀ ^ j) • (g₀ ^ (-j) • w) = δ • w := by
        rw [← mul_smul, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
      have h2 : g₀ ^ k • (g₀ ^ (-j) • w) = g₀ ^ (k - j) • w := by
        rw [← mul_smul, ← zpow_add, ← sub_eq_add_neg]
      rw [← h1, hk (g₀ ^ (-j) • w), h2]
    have hBad' := s28m_far_isClosed_union hΓ hl hdil hs hDΓ hDm
    obtain ⟨B, hBdef⟩ : ∃ B : Set ℍ, B = {w : ℍ | ∃ δ ∈ D, ∃ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ ∧ δ • w' = w} :=
      ⟨_, rfl⟩
    rw [← hBdef] at hBad'
    have hBmem : ∀ w : ℍ, w ∈ B ↔ ∃ δ ∈ D, ∃ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ ∧ δ • w' = w := by
      intro w; rw [hBdef]; rfl
    have hz₁V : γ • x₁ ∉ B := by
      rw [hBmem]
      rintro ⟨δ, hδD, w', hw', hδw⟩
      have hne : ∀ j : ℤ, ∃ w : ℍ, (γ⁻¹ * δ) • w ≠ g₀ ^ j • w := by
        intro j
        by_contra hcon
        push Not at hcon
        apply hδD.2
        refine ⟨j, fun w => ?_⟩
        have := hcon w
        rw [mul_smul, inv_smul_eq_iff] at this
        exact this
      refine hdisj (γ⁻¹ * δ) (Γ.mul_mem (Γ.inv_mem hγ) hδD.1) hne w' x₁ (by linarith) (by rw [hx₁s]; linarith) ?_
      rw [mul_smul, hδw, inv_smul_smul]
    have hVn : Bᶜ ∈ 𝓝 (γ • x₁) := hBad'.isOpen_compl.mem_nhds hz₁V
    -- continuity of `(r, y) ↦ γ • F r y` at `(0, x₁)`
    have hΦ : Continuous (fun q : ℝ × ℍ => γ • F q.1 q.2) := (continuous_const_smul γ).comp hFc
    have hnhds : (fun q : ℝ × ℍ => γ • F q.1 q.2) ⁻¹' Bᶜ ∈ 𝓝 ((0 : ℝ), x₁) := by
      apply hΦ.continuousAt.preimage_mem_nhds
      have hF0' : F 0 x₁ = x₁ := by
        apply UpperHalfPlane.ext
        simp [hF]
      show Bᶜ ∈ 𝓝 (γ • F 0 x₁)
      rw [hF0']; exact hVn
    obtain ⟨A, hA, W, hW, hAW⟩ := mem_nhds_prod_iff.1 hnhds
    obtain ⟨δ₀, hδ₀, hball⟩ := Metric.mem_nhds_iff.1 hA
    have hkey : ∀ (r : ℝ) (y : ℍ), r ∈ A → y ∈ W → γ • F r y ∉ B :=
      fun r y hr hy => by
        have h := hAW (Set.mk_mem_prod hr hy)
        rw [Set.mem_preimage, Set.mem_compl_iff] at h
        exact h
    -- show that a ball around `u₀` lies in `T`
    refine Metric.mem_nhds_iff.2 ⟨δ₀, hδ₀, fun u hu => ?_⟩
    have hr : |u - u₀| < δ₀ := by simpa [Real.dist_eq] using hu
    show γ • F u x₀ ∈ closure C
    have hux : γ • F u x₀ = γ • F (u - u₀) x₁ := by
      rw [hx₁, hFadd]
      congr 2
      ring
    rw [hux, mem_closure_iff]
    intro O hO hOt
    -- a neighbourhood of `x₁` which `y ↦ γ • F (u - u₀) y` sends into `O`
    have hΨ : Continuous (fun y : ℍ => γ • F (u - u₀) y) :=
      (continuous_const_smul γ).comp (hFc.comp (by fun_prop : Continuous (fun y : ℍ => (u - u₀, y))))
    have hW₂ : (fun y : ℍ => γ • F (u - u₀) y) ⁻¹' O ∈ 𝓝 x₁ := hΨ.continuousAt.preimage_mem_nhds (hO.mem_nhds hOt)
    have hN : (fun c : ℍ => γ⁻¹ • c) ⁻¹' (W ∩ (fun y : ℍ => γ • F (u - u₀) y) ⁻¹' O) ∈ 𝓝 (γ • x₁) := by
      apply (continuous_const_smul γ⁻¹).continuousAt.preimage_mem_nhds
      rw [inv_smul_smul]
      exact Filter.inter_mem hW hW₂
    obtain ⟨c, hcN, hcC⟩ := mem_closure_iff_nhds.1 hz₁ _ hN
    obtain ⟨hcW, hcO⟩ := hcN
    set y : ℍ := γ⁻¹ • c with hy
    have hcy : γ • y = c := by rw [hy, smul_inv_smul]
    -- `ς y < s`
    have hysig : y.im / ‖(y : ℂ)‖ < s := by
      by_contra hcon
      push Not at hcon
      exact hCE hcC γ hγ y hcon hcy
    refine ⟨γ • F (u - u₀) y, hcO, ?_⟩
    -- the slide from `c` to `γ • F (u - u₀) y` stays in `E`
    have hcont : Continuous (fun r : ℝ => γ • F r y) :=
      (continuous_const_smul γ).comp (hFc.comp (by fun_prop : Continuous (fun r : ℝ => (r, y))))
    have hS : (fun r : ℝ => γ • F r y) '' Set.uIcc 0 (u - u₀) ⊆ connectedComponentIn E c := by
      refine IsPreconnected.subset_connectedComponentIn (isPreconnected_uIcc.image _ hcont.continuousOn)
        ⟨0, by simp, ?_⟩ ?_
      · show γ • F 0 y = c
        have : F 0 y = y := by
          apply UpperHalfPlane.ext
          simp [hF]
        rw [this, hcy]
      · rintro _ ⟨r, hr', rfl⟩
        have hrδ : |r| < δ₀ := by
          have h1 : |r| ≤ |u - u₀| := by
            rcases Set.mem_uIcc.1 hr' with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [abs_of_nonneg h1, abs_of_nonneg (le_trans h1 h2)]; exact h2
            · rw [abs_of_nonpos h2, abs_of_nonpos (le_trans h1 h2)]; linarith
          linarith
        have hrA : r ∈ A := hball (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hrδ)
        have hmem : γ • F r y ∉ B := hkey r y hrA hcW
        intro δ hδ w' hw' hδw
        by_cases hδD : ∃ j : ℤ, ∀ w : ℍ, δ • w = γ • g₀ ^ j • w
        · obtain ⟨j, hj⟩ := hδD
          rw [hj w'] at hδw
          have h1 : F r y = g₀ ^ j • w' := smul_left_cancel γ hδw.symm
          have h2 := s28m_far_sig_zpow hl hdil j w'
          rw [← h1, s28m_far_scale_sig hF] at h2
          linarith
        · exact hmem ((hBmem _).2 ⟨δ, ⟨hδ, hδD⟩, w', hw', hδw⟩)
    have hmemS : γ • F (u - u₀) y ∈ connectedComponentIn E c :=
      hS ⟨u - u₀, Set.right_mem_uIcc, rfl⟩
    have hCc : C = connectedComponentIn E c := hC c hcC
    rw [← hCc] at hmemS
    exact hmemS
  have hne : T.Nonempty := ⟨0, by simpa [T, hF0] using hcl⟩
  have := IsClopen.eq_univ (s := T) ⟨hTc, hTo⟩ hne
  have hu : u ∈ T := by rw [this]; trivial
  exact hu


/-- If `a c = 0` and `b d = 0` then `γ` maps the imaginary axis to itself. -/
theorem s28m_far_axis_of_entries {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hac : γ 0 0 * γ 1 0 = 0) (hbd : γ 0 1 * γ 1 1 = 0) {z : ℍ} (hz : (z : ℂ).re = 0) :
    ((γ • z : ℍ) : ℂ).re = 0 := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  have hc := UpperHalfPlane.coe_specialLinearGroup_apply γ z
  simp only [Algebra.algebraMap_self_apply] at hc
  rw [hc]
  have hz0 : (z : ℂ) ≠ 0 := z.ne_zero
  have hzre : (z : ℂ) = (z.im : ℂ) * Complex.I := by
    have hz' : z.re = 0 := hz
    apply Complex.ext <;> simp [hz']
  rcases mul_eq_zero.1 hac with ha | hc'
  · -- `a = 0`: then `b c = -1`, `d = 0`
    have hb : γ 0 1 ≠ 0 := by
      intro h0; rw [ha, h0] at hdet; simp at hdet
    have hd : γ 1 1 = 0 := by
      rcases mul_eq_zero.1 hbd with h | h
      · exact absurd h hb
      · exact h
    rw [ha, hd]
    simp only [Complex.ofReal_zero, zero_mul, zero_add, add_zero]
    rw [hzre]
    simp [Complex.div_re, Complex.normSq]
  · -- `c = 0`: then `a d = 1`, `b = 0`
    have ha : γ 0 0 ≠ 0 := by
      intro h0; rw [h0, hc'] at hdet; simp at hdet
    have hd : γ 1 1 ≠ 0 := by
      intro h0; rw [h0, hc'] at hdet; simp at hdet
    have hb : γ 0 1 = 0 := by
      rcases mul_eq_zero.1 hbd with h | h
      · exact h
      · exact absurd h hd
    rw [hc', hb]
    simp only [Complex.ofReal_zero, zero_mul, zero_add, add_zero]
    rw [hzre]
    simp [Complex.div_re, Complex.normSq]


/-- `ς` is continuous on `ℍ`. -/
theorem s28m_far_sig_continuous : Continuous (fun w : ℍ => w.im / ‖(w : ℂ)‖) :=
  Continuous.div (by fun_prop) (by fun_prop) (fun w => (norm_pos_iff.2 w.ne_zero).ne')

/-- **Minimum displacement.** A freely acting cocompact Fuchsian group with a
nontrivial action has a positive globally minimal displacement, attained by an
element and a point. The comparison is over elements acting nontrivially, not
over matrices merely different from 1. Use the finite bounded length spectrum
and attainment of each hyperbolic element's translation length. -/
theorem s28m_min_disp {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hc : IsCocompact Γ)
    (hnt : ∃ γ ∈ Γ, ∃ w : ℍ, γ • w ≠ w) :
    ∃ (g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ) (w₀ : ℍ),
      g₀ ∈ Γ ∧ (∃ w : ℍ, g₀ • w ≠ w) ∧ 0 < dist w₀ (g₀ • w₀) ∧
      ∀ γ ∈ Γ, (∃ w : ℍ, γ • w ≠ w) →
        ∀ w : ℍ, dist w₀ (g₀ • w₀) ≤ dist w (γ • w) := by
  classical
  have hhyp : ∀ γ ∈ Γ, (∃ w : ℍ, γ • w ≠ w) → IsHyperbolic γ := by
    intro γ hγ hntγ
    obtain ⟨w, hw⟩ := hntγ
    apply cocompact_elements_hyperbolic hΓ hfree hc γ hγ
    · intro h
      apply hw
      rw [h, one_smul]
    · intro h
      apply hw
      rw [h, s27g_neg_one_smul]
  obtain ⟨g, hg, hng⟩ := hnt
  have hhg := hhyp g hg hng
  let L := translationLength g
  let B : Set ℝ := {t ∈ lengthSpectrum Γ | t ≤ L}
  have hB : B.Finite := (lengthSpectrum_discrete hΓ hfree hc L).1
  have hLB : L ∈ B := ⟨⟨g, hg, hhg, rfl⟩, le_rfl⟩
  obtain ⟨t, ht, hleast⟩ := Set.exists_min_image B id hB ⟨L, hLB⟩
  obtain ⟨g₀, hg₀, hhg₀, htg₀⟩ := ht.1
  obtain ⟨w₀, hw₀⟩ := (translationLength_eq_inf_dist hhg₀).2.1
  have hpos : 0 < dist w₀ (g₀ • w₀) := by
    rw [hw₀]
    exact s30a_tl_pos hhg₀
  refine ⟨g₀, w₀, hg₀, ⟨w₀, ?_⟩, hpos, ?_⟩
  · intro heq
    rw [heq, dist_self] at hpos
    exact (lt_irrefl 0) hpos
  · intro γ hγ hntγ w
    have hhγ := hhyp γ hγ hntγ
    have hlow : t ≤ translationLength γ := by
      by_cases hle : translationLength γ ≤ L
      · exact hleast _ ⟨⟨γ, hγ, hhγ, rfl⟩, hle⟩
      · exact ht.2.trans (le_of_lt (lt_of_not_ge hle))
    have hdist : translationLength γ ≤ dist w (γ • w) := by
      rw [(translationLength_eq_inf_dist hhγ).1]
      exact ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact dist_nonneg⟩ w
    rw [hw₀, ← htg₀]
    exact hlow.trans hdist

/-- **Normalize a displacement minimizer.** Conjugate the chosen element to
a dilation by l > 1. Its logarithm is the attained minimum, and the identical
global lower bound holds for every nontrivial action in the conjugate group.
This supplies exactly hdil and hmin of the frozen axis-stabilizer statement. -/
theorem s28m_min_hyperbolic {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (hc : IsCocompact Γ)
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg₀ : g₀ ∈ Γ)
    (hnt : ∃ w : ℍ, g₀ • w ≠ w) {w₀ : ℍ}
    (hmin : ∀ γ ∈ Γ, (∃ w : ℍ, γ • w ≠ w) →
      ∀ w : ℍ, dist w₀ (g₀ • w₀) ≤ dist w (γ • w)) :
    ∃ (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (l : ℝ),
      1 < l ∧ Real.log l = dist w₀ (g₀ • w₀) ∧
      A * g₀ * A⁻¹ ∈ conjGroup Γ A ∧
      (∀ w : ℍ, (((A * g₀ * A⁻¹) • w : ℍ) : ℂ) = l * (w : ℂ)) ∧
      ∀ γ ∈ conjGroup Γ A, (∃ w : ℍ, γ • w ≠ w) →
        ∀ w : ℍ, Real.log l ≤ dist w (γ • w) := by
  obtain ⟨z, hz⟩ := hnt
  have hhg₀ : IsHyperbolic g₀ := by
    apply cocompact_elements_hyperbolic hΓ hfree hc g₀ hg₀
    · intro h
      apply hz
      rw [h, one_smul]
    · intro h
      apply hz
      rw [h, s27g_neg_one_smul]
  obtain ⟨u, hu⟩ := (translationLength_eq_inf_dist hhg₀).2.1
  have hlen : translationLength g₀ = dist w₀ (g₀ • w₀) := by
    apply le_antisymm
    · rw [(translationLength_eq_inf_dist hhg₀).1]
      exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact dist_nonneg⟩ w₀
    · rw [← hu]
      exact hmin g₀ hg₀ ⟨z, hz⟩ u
  obtain ⟨A, lam, hlam, hlog, hdil⟩ := s30w_conj_dilation hhg₀
  refine ⟨A, lam ^ 2, by nlinarith, hlog.trans hlen,
    s30l_mem_conjGroup.2 ⟨g₀, hg₀, rfl⟩, hdil, ?_⟩
  intro γ hγ hntγ w
  obtain ⟨δ, hδ, rfl⟩ := s30l_mem_conjGroup.1 hγ
  have hntδ : ∃ v : ℍ, δ • v ≠ v := by
    obtain ⟨v, hv⟩ := hntγ
    refine ⟨A⁻¹ • v, ?_⟩
    intro heq
    apply hv
    simpa only [mul_smul, smul_inv_smul] using congrArg (fun x : ℍ => A • x) heq
  have hcomp := hmin δ hδ hntδ (A⁻¹ • w)
  rw [hlog, hlen]
  calc
    dist w₀ (g₀ • w₀) ≤ dist (A⁻¹ • w) (δ • A⁻¹ • w) := hcomp
    _ = dist w ((A * δ * A⁻¹) • w) := by
      rw [mul_smul, mul_smul, ← dist_smul A (A⁻¹ • w) (δ • A⁻¹ • w),
        smul_inv_smul]

/-- **Conjugate uniformization data.** The existing adjusted projection is a
uniformization for the conjugate group; proper discontinuity, freeness modulo
the central kernel, and compact orbit representatives are preserved. -/
theorem s28m_conj_uniformization {S : Type*} [TopologicalSpace S] [ChartedSpace ℂ S]
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → S}
    (hp : IsUniformization Γ p) (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hc : IsCocompact Γ) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    IsUniformization (conjGroup Γ A) (adjustProjection p A) ∧
      IsFuchsian (conjGroup Γ A) ∧ ActsFreely (conjGroup Γ A) ∧
      IsCocompact (conjGroup Γ A) := by
  refine ⟨adjustProjection_isUniformization hp A, s30l_isFuchsian_conj hΓ A, ?_, ?_⟩
  · intro γ hγ w hw
    obtain ⟨δ, hδ, rfl⟩ := s30l_mem_conjGroup.1 hγ
    have hfix : δ • (A⁻¹ • w) = A⁻¹ • w := by
      simpa only [mul_smul, inv_smul_smul] using
        congrArg (fun x : ℍ => A⁻¹ • x) hw
    rcases hfree δ hδ (A⁻¹ • w) hfix with heq | heq
    · left
      simp only [heq, mul_one, mul_inv_cancel]
    · right
      simp only [heq, mul_neg, mul_one, neg_mul, mul_inv_cancel]
  · obtain ⟨C, hC, hrep⟩ := hc
    refine ⟨(fun x : ℍ => A • x) '' C, hC.image (continuous_const_smul A), ?_⟩
    intro w
    obtain ⟨δ, hδ, hδC⟩ := hrep (A⁻¹ • w)
    refine ⟨A * δ * A⁻¹, s30l_mem_conjGroup.2 ⟨δ, hδ, rfl⟩,
      δ • (A⁻¹ • w), hδC, ?_⟩
    simp only [mul_smul]

/-- **Axis stabiliser.**  If `g₀ : w ↦ l w` has the smallest displacement among all elements of `Γ` acting
nontrivially, then an element of `Γ` that maps one point of the imaginary axis to the imaginary axis is a power
of `g₀`.  (Reduce `γ` by a power of `g₀` so that the displacement along the axis is `< log l`.) -/
theorem s28m_stab_axis {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg₀ : g₀ ∈ Γ) {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ))
    (hmin : ∀ γ ∈ Γ, (∃ w : ℍ, γ • w ≠ w) → ∀ w : ℍ, Real.log l ≤ dist w (γ • w)) :
    ∀ γ ∈ Γ, ∀ w : ℍ, (w : ℂ).re = 0 → ((γ • w : ℍ) : ℂ).re = 0 →
      ∃ j : ℤ, ∀ w' : ℍ, γ • w' = g₀ ^ j • w' := by
  intro γ hγ w hw hγw
  have hll : 0 < Real.log l := Real.log_pos hl
  have hl0 : 0 < l := by linarith
  set a : ℝ := Real.log ((γ • w : ℍ).im / w.im) with ha
  set j : ℤ := round (a / Real.log l) with hj
  refine ⟨j, ?_⟩
  set δ : Matrix.SpecialLinearGroup (Fin 2) ℝ := g₀ ^ (-j) * γ with hδ
  have hδΓ : δ ∈ Γ := Γ.mul_mem (Γ.zpow_mem hg₀ _) hγ
  have hδw : δ • w = g₀ ^ (-j) • (γ • w) := mul_smul _ _ _
  have hcoe : ((δ • w : ℍ) : ℂ) = (l : ℂ) ^ (-j) * ((γ • w : ℍ) : ℂ) := by
    rw [hδw, s28m_far_zpow hl hdil]
  have hc2 : (l : ℂ) ^ (-j) = ((l ^ (-j) : ℝ) : ℂ) := (Complex.ofReal_zpow l (-j)).symm
  have hre : ((δ • w : ℍ) : ℂ).re = ((w : ℍ) : ℂ).re := by
    rw [hcoe, hc2, Complex.re_ofReal_mul, hγw, mul_zero, hw]
  have him : (δ • w : ℍ).im = l ^ (-j) * (γ • w : ℍ).im := by
    have := congrArg Complex.im hcoe
    rw [hc2, Complex.im_ofReal_mul] at this
    simpa using this
  have hdist : dist w (δ • w) = |j * Real.log l - a| := by
    rw [UpperHalfPlane.dist_of_re_eq (by simpa using hre.symm), Real.dist_eq, him]
    have h1 : 0 < w.im := w.im_pos
    have h2 : 0 < (γ • w : ℍ).im := (γ • w).im_pos
    rw [Real.log_mul (zpow_pos hl0 _).ne' h2.ne', Real.log_zpow, ha, Real.log_div h2.ne' h1.ne']
    congr 1
    push_cast
    ring
  have hle : |j * Real.log l - a| ≤ Real.log l / 2 := by
    have h := abs_sub_round (a / Real.log l)
    rw [← hj, abs_sub_comm] at h
    have : |j * Real.log l - a| = |(j : ℝ) - a / Real.log l| * Real.log l := by
      rw [← abs_of_pos hll, ← abs_mul, abs_of_pos hll]
      congr 1
      field_simp
    rw [this]
    nlinarith [abs_nonneg ((j : ℝ) - a / Real.log l)]
  by_contra hcon
  push Not at hcon
  obtain ⟨w', hw'⟩ := hcon
  have hnt : ∃ v : ℍ, δ • v ≠ v := by
    refine ⟨w', fun h => hw' ?_⟩
    have h1 : g₀ ^ (-j) • (γ • w') = w' := by rw [← mul_smul]; exact h
    calc γ • w' = g₀ ^ j • (g₀ ^ (-j) • (γ • w')) := by
          rw [← mul_smul, ← zpow_add, add_neg_cancel, zpow_zero, one_smul]
      _ = g₀ ^ j • w' := by rw [h1]
  have := hmin δ hδΓ hnt w
  rw [hdist] at this
  linarith [hle]

/-- Only the imaginary axis can have angular collar coordinate at least one. -/
theorem s28m_collar_axis_of_one {w : ℍ} (hw : 1 ≤ w.im / ‖(w : ℂ)‖) :
    (w : ℂ).re = 0 := by
  have hn : 0 < ‖(w : ℂ)‖ := norm_pos_iff.2 w.ne_zero
  have hle : ‖(w : ℂ)‖ ≤ w.im := by
    have h := (le_div_iff₀ hn).1 hw
    simpa only [one_mul] using h
  have heq : ‖(w : ℂ)‖ = w.im := le_antisymm hle (Complex.im_le_norm (w : ℂ))
  have hs : ‖(w : ℂ)‖ ^ 2 = (w : ℂ).re * (w : ℂ).re + w.im * w.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    rfl
  rw [heq] at hs
  nlinarith [sq_nonneg (w : ℂ).re]

/-- A fixed non-power group element separates sufficiently thin collars in a compact piece.
The bound is obtained from the maximum of the two collar coordinates' minimum. -/
theorem s28m_collar_compact_separation
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (hstab : ∀ γ ∈ Γ, ∀ w : ℍ, (w : ℂ).re = 0 → ((γ • w : ℍ) : ℂ).re = 0 →
      ∃ j : ℤ, ∀ w' : ℍ, γ • w' = g₀ ^ j • w')
    {Q : Set ℍ} (hQc : IsCompact Q)
    {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hγ : γ ∈ Γ)
    (hnot : ∀ j : ℤ, ∃ w : ℍ, γ • w ≠ g₀ ^ j • w) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      ∀ w ∈ Q, ∀ w' ∈ Q, s ≤ w.im / ‖(w : ℂ)‖ →
        s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w ≠ w' := by
  let K : Set ℍ := Q ∩ (fun w : ℍ => γ • w) ⁻¹' Q
  have hKc : IsCompact K :=
    hQc.inter_right (hQc.isClosed.preimage (continuous_const_smul γ))
  rcases K.eq_empty_or_nonempty with hKempty | hKne
  · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    -- Here Q and its preimage are disjoint, independently of the collar threshold.
    intro w hw w' hw' _ _ heq
    have hwK : w ∈ K := ⟨hw, by change γ • w ∈ Q; rw [heq]; exact hw'⟩
    rw [hKempty] at hwK
    exact hwK
  · let f : ℍ → ℝ := fun w =>
      min (w.im / ‖(w : ℂ)‖) ((γ • w : ℍ).im / ‖((γ • w : ℍ) : ℂ)‖)
    have hfc : Continuous f := s28m_far_sig_continuous.min
      (s28m_far_sig_continuous.comp (continuous_const_smul γ))
    obtain ⟨q, hqK, hqmax⟩ := hKc.exists_isMaxOn hKne hfc.continuousOn
    have hq_lt : f q < 1 := by
      by_contra hq
      have hq_ge : 1 ≤ f q := le_of_not_gt hq
      have h1 : 1 ≤ q.im / ‖(q : ℂ)‖ := hq_ge.trans (min_le_left _ _)
      have h2 : 1 ≤ (γ • q : ℍ).im / ‖((γ • q : ℍ) : ℂ)‖ :=
        hq_ge.trans (min_le_right _ _)
      obtain ⟨j, hj⟩ := hstab γ hγ q
        (s28m_collar_axis_of_one h1) (s28m_collar_axis_of_one h2)
      obtain ⟨w, hw⟩ := hnot j
      exact hw (hj w)
    let s : ℝ := (max 0 (f q) + 1) / 2
    have hm : max 0 (f q) < 1 := max_lt_iff.2 ⟨by norm_num, hq_lt⟩
    have hs0 : 0 < s := by
      have := le_max_left (0 : ℝ) (f q)
      dsimp [s]
      linarith
    have hs1 : s < 1 := by dsimp [s]; linarith
    have hqs : f q < s := by
      have := le_max_right (0 : ℝ) (f q)
      dsimp [s]
      linarith
    refine ⟨s, hs0, hs1, ?_⟩
    intro w hw w' hw' hsw hsw' heq
    have hwK : w ∈ K := ⟨hw, by change γ • w ∈ Q; rw [heq]; exact hw'⟩
    have hlow : s ≤ f w := by
      change s ≤ min (w.im / ‖(w : ℂ)‖)
        ((γ • w : ℍ).im / ‖((γ • w : ℍ) : ℂ)‖)
      rw [heq]
      exact le_min hsw hsw'
    have hhigh : f w ≤ f q := hqmax hwK
    exact (not_le_of_gt hqs) (hlow.trans hhigh)

/-- **The embedded collar.**  If `Γ` is Fuchsian, `g₀ : w ↦ l w` lies in `Γ` and an element of `Γ` that maps a
point of the imaginary axis to the imaginary axis is a power of `g₀`, then for `s₁ < 1` close to `1` the closed
collar `{ς ≥ s₁}` is disjoint from its images under all `γ ∈ Γ` that are not powers of `g₀`.  (Compactness:
normalise by `g₀` into a compact piece of the collar, finitely many `γ` by `IsFuchsian`, and let `s₁ → 1`.) -/
theorem s28m_collar {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg₀ : g₀ ∈ Γ) {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ))
    (hstab : ∀ γ ∈ Γ, ∀ w : ℍ, (w : ℂ).re = 0 → ((γ • w : ℍ) : ℂ).re = 0 →
      ∃ j : ℤ, ∀ w' : ℍ, γ • w' = g₀ ^ j • w') :
    ∃ s₁ : ℝ, 0 < s₁ ∧ s₁ < 1 ∧
      ∀ γ ∈ Γ, (∀ j : ℤ, ∃ w : ℍ, γ • w ≠ g₀ ^ j • w) →
        ∀ w w' : ℍ, s₁ ≤ w.im / ‖(w : ℂ)‖ → s₁ ≤ w'.im / ‖(w' : ℂ)‖ → γ • w ≠ w' := by
  classical
  let Q : Set ℍ := {w : ℍ |
    (1 : ℝ) / 2 ≤ w.im / ‖(w : ℂ)‖ ∧ 1 ≤ ‖(w : ℂ)‖ ∧ ‖(w : ℂ)‖ ≤ l}
  have hQc : IsCompact Q := s28m_far_compact (by norm_num : (0 : ℝ) < 1 / 2)
  -- Proper discontinuity restricts the normalized intersections to a finite set.
  have hfin : {γ ∈ Γ | ((fun w : ℍ => γ • w) '' Q ∩ Q).Nonempty}.Finite :=
    hΓ Q hQc
  let F := hfin.toFinset
  have hFsep : ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      ∀ γ ∈ F, γ ∈ Γ → (∀ j : ℤ, ∃ w : ℍ, γ • w ≠ g₀ ^ j • w) →
        ∀ w ∈ Q, ∀ w' ∈ Q, s ≤ w.im / ‖(w : ℂ)‖ →
          s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w ≠ w' := by
    induction F using Finset.induction_on with
    | empty =>
        refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
        intro γ hγ
        simp at hγ
    | @insert γ F hγF ih =>
        obtain ⟨s, hs0, hs1, hs⟩ := ih
        have hγsep : ∃ t : ℝ, 0 < t ∧ t < 1 ∧
            (γ ∈ Γ → (∀ j : ℤ, ∃ w : ℍ, γ • w ≠ g₀ ^ j • w) →
              ∀ w ∈ Q, ∀ w' ∈ Q, t ≤ w.im / ‖(w : ℂ)‖ →
                t ≤ w'.im / ‖(w' : ℂ)‖ → γ • w ≠ w') := by
          by_cases hγΓ : γ ∈ Γ
          · by_cases hnot : ∀ j : ℤ, ∃ w : ℍ, γ • w ≠ g₀ ^ j • w
            · obtain ⟨t, ht0, ht1, ht⟩ :=
                s28m_collar_compact_separation hstab hQc hγΓ hnot
              exact ⟨t, ht0, ht1, fun _ _ => ht⟩
            · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
              intro _ hbad
              exact False.elim (hnot hbad)
          · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
            intro hmem
            exact False.elim (hγΓ hmem)
        obtain ⟨t, ht0, ht1, ht⟩ := hγsep
        refine ⟨max s t, lt_of_lt_of_le hs0 (le_max_left _ _),
          max_lt_iff.2 ⟨hs1, ht1⟩, ?_⟩
        intro δ hδ hδΓ hnot w hw w' hw' hsw hsw'
        rcases Finset.mem_insert.1 hδ with hδeq | hδF
        · subst δ
          exact ht hδΓ hnot w hw w' hw'
            ((le_max_right _ _).trans hsw) ((le_max_right _ _).trans hsw')
        · exact hs δ hδF hδΓ hnot w hw w' hw'
            ((le_max_left _ _).trans hsw) ((le_max_left _ _).trans hsw')
  obtain ⟨s, hs0, hs1, hsep⟩ := hFsep
  let s₁ : ℝ := max (1 / 2) s
  have hs₁0 : 0 < s₁ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
    (le_max_left _ _)
  have hs₁1 : s₁ < 1 := max_lt_iff.2 ⟨by norm_num, hs1⟩
  refine ⟨s₁, hs₁0, hs₁1, ?_⟩
  intro γ hγ hnot w w' hw hw' heq
  -- Normalize both ends, not just the input point.
  obtain ⟨j, hj1, hj2⟩ := s28m_far_reduce hl hdil w
  obtain ⟨k, hk1, hk2⟩ := s28m_far_reduce hl hdil w'
  let x : ℍ := g₀ ^ j • w
  let y : ℍ := g₀ ^ k • w'
  let δ : Matrix.SpecialLinearGroup (Fin 2) ℝ := g₀ ^ k * γ * g₀ ^ (-j)
  have hx_sig : x.im / ‖(x : ℂ)‖ = w.im / ‖(w : ℂ)‖ :=
    s28m_far_sig_zpow hl hdil j w
  have hy_sig : y.im / ‖(y : ℂ)‖ = w'.im / ‖(w' : ℂ)‖ :=
    s28m_far_sig_zpow hl hdil k w'
  have hxQ : x ∈ Q := ⟨by rw [hx_sig]; exact (le_max_left _ _).trans hw, hj1, hj2.le⟩
  have hyQ : y ∈ Q := ⟨by rw [hy_sig]; exact (le_max_left _ _).trans hw', hk1, hk2.le⟩
  have hδΓ : δ ∈ Γ :=
    Γ.mul_mem (Γ.mul_mem (Γ.zpow_mem hg₀ k) hγ) (Γ.zpow_mem hg₀ (-j))
  have hδxy : δ • x = y := by
    dsimp [δ, x, y]
    simp only [mul_smul, zpow_neg, inv_smul_smul]
    rw [heq]
  have hδnot : ∀ n : ℤ, ∃ z : ℍ, δ • z ≠ g₀ ^ n • z := by
    intro n
    by_contra hn
    push Not at hn
    obtain ⟨z, hz⟩ := hnot (-k + n + j)
    apply hz
    calc
      γ • z = g₀ ^ (-k) • (δ • (g₀ ^ j • z)) := by
        dsimp [δ]
        simp only [mul_smul, zpow_neg, inv_smul_smul]
      _ = g₀ ^ (-k) • (g₀ ^ n • (g₀ ^ j • z)) := by rw [hn]
      _ = g₀ ^ (-k + n + j) • z := by
        rw [← mul_smul, ← mul_smul, ← zpow_add, ← zpow_add]
  have hδF : δ ∈ F := by
    apply hfin.mem_toFinset.2
    exact ⟨hδΓ, y, ⟨x, hxQ, hδxy⟩, hyQ⟩
  have hsx : s ≤ x.im / ‖(x : ℂ)‖ := by
    rw [hx_sig]
    exact (le_max_right _ _).trans hw
  have hsy : s ≤ y.im / ‖(y : ℂ)‖ := by
    rw [hy_sig]
    exact (le_max_right _ _).trans hw'
  exact hsep δ hδF hδΓ hδnot x hxQ y hyQ hsx hsy hδxy

/-- **Far points.**  Let `s₁ < s < 1`, suppose the closed collar `{ς ≥ s₁}` is disjoint from its images under the
`γ ∈ Γ` that are not powers of `g₀`, and `γ ∈ Γ` mapping an axis point to the axis is a power of `g₀`.  Let `E`
be `ℍ` with all images `γ {ς ≥ s}` removed, and `p ∈ E` with `s₁ ≤ ς p < s` (a point just outside the collar).
Then the connected component of `p` in `E` contains points with `ς` arbitrarily small, i.e. it is not contained
in any bounded neighbourhood of the axis.  (`ς` attains its infimum `σ` on the closure of the component, by
`g₀`-periodicity; the minimiser is not in `E` (`ς` has no local minimum) and not in `{ς ≥ s}`, so it lies on an
edge of a collar `γ {ς ≥ s}` with `γ` not a power of `g₀`; the edge is then entirely in the closure, by local
finiteness and connectedness of the edge, and has an end at a point of `ℝ ∖ {0}`, where `ς → 0`.) -/
theorem s28m_far {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {g₀ : Matrix.SpecialLinearGroup (Fin 2) ℝ} (hg₀ : g₀ ∈ Γ) {l : ℝ} (hl : 1 < l)
    (hdil : ∀ w : ℍ, ((g₀ • w : ℍ) : ℂ) = l * (w : ℂ)) {s₁ s : ℝ} (hs₁ : 0 < s₁) (hs₁s : s₁ < s) (hs : s < 1)
    (hdisj : ∀ γ ∈ Γ, (∀ j : ℤ, ∃ w : ℍ, γ • w ≠ g₀ ^ j • w) →
      ∀ w w' : ℍ, s₁ ≤ w.im / ‖(w : ℂ)‖ → s₁ ≤ w'.im / ‖(w' : ℂ)‖ → γ • w ≠ w')
    (hstab : ∀ γ ∈ Γ, ∀ w : ℍ, (w : ℂ).re = 0 → ((γ • w : ℍ) : ℂ).re = 0 →
      ∃ j : ℤ, ∀ w' : ℍ, γ • w' = g₀ ^ j • w')
    {p : ℍ} (hp₁ : s₁ ≤ p.im / ‖(p : ℂ)‖) (hp₂ : p.im / ‖(p : ℂ)‖ < s) {ε : ℝ} (hε : 0 < ε) :
    ∃ w ∈ connectedComponentIn {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w} p,
      w.im / ‖(w : ℂ)‖ < ε := by
  -- the hypothesis `s < 1` is not needed: `{ς ≥ s}` is empty for `s > 1`, and `s₁ ≤ ς p < s ≤ 1` is the real content
  have _hs := hs
  by_contra hcon
  push Not at hcon
  have hs0 : 0 < s := by linarith
  obtain ⟨F, hF, hFc⟩ := s28m_far_scale
  set E : Set ℍ := {w : ℍ | ∀ γ ∈ Γ, ∀ w' : ℍ, s ≤ w'.im / ‖(w' : ℂ)‖ → γ • w' ≠ w} with hE
  have hEo : IsOpen E := s28m_far_isOpen_E hΓ hg₀ hl hdil hs0
  have hpE : p ∈ E := s28m_far_shell_mem hl hdil hdisj hs₁s hp₁ hp₂
  set C : Set ℍ := connectedComponentIn E p with hC
  have hpC : p ∈ C := mem_connectedComponentIn hpE
  have hCE : C ⊆ E := connectedComponentIn_subset E p
  have hCinv : ∀ (j : ℤ), ∀ w ∈ C, g₀ ^ j • w ∈ C := fun j w hw =>
    s28m_far_comp_zpow hg₀ hl hdil hdisj hs₁s hp₁ hp₂ j hw
  have hsigc := s28m_far_sig_continuous
  -- `ε ≤ ς` on the closure of `C`
  have hεcl : ∀ x ∈ closure C, ε ≤ x.im / ‖(x : ℂ)‖ := by
    intro x hx
    have : closure C ⊆ {w : ℍ | ε ≤ w.im / ‖(w : ℂ)‖} :=
      closure_minimal (fun w hw => hcon w hw) (isClosed_le continuous_const hsigc)
    exact this hx
  have hclinv : ∀ (j : ℤ), ∀ x ∈ closure C, g₀ ^ j • x ∈ closure C := fun j x hx =>
    map_mem_closure (continuous_const_smul (g₀ ^ j)) hx (fun w hw => hCinv j w hw)
  -- the compact set `K`
  set Q : Set ℍ := {w : ℍ | ε ≤ w.im / ‖(w : ℂ)‖ ∧ 1 ≤ ‖(w : ℂ)‖ ∧ ‖(w : ℂ)‖ ≤ l} with hQ
  have hQc : IsCompact Q := s28m_far_compact hε
  have hKc : IsCompact (closure C ∩ Q) := hQc.inter_left isClosed_closure
  have hKne : (closure C ∩ Q).Nonempty := by
    obtain ⟨j, hj1, hj2⟩ := s28m_far_reduce hl hdil p
    have hjp := hCinv j p hpC
    refine ⟨g₀ ^ j • p, subset_closure hjp, ?_, hj1, hj2.le⟩
    exact hcon _ hjp
  obtain ⟨q, hqK, hqmin⟩ := hKc.exists_isMinOn hKne hsigc.continuousOn
  have hqmin' : ∀ x ∈ closure C, q.im / ‖(q : ℂ)‖ ≤ x.im / ‖(x : ℂ)‖ := by
    intro x hx
    obtain ⟨j, hj1, hj2⟩ := s28m_far_reduce hl hdil x
    have hx' := hclinv j x hx
    have h := hqmin (show g₀ ^ j • x ∈ closure C ∩ Q from ⟨hx', hεcl _ hx', hj1, hj2.le⟩)
    have h' : q.im / ‖(q : ℂ)‖ ≤ (g₀ ^ j • x : ℍ).im / ‖((g₀ ^ j • x : ℍ) : ℂ)‖ := h
    rw [s28m_far_sig_zpow hl hdil j x] at h'
    exact h'
  have hσ : q.im / ‖(q : ℂ)‖ < s :=
    lt_of_le_of_lt (hqmin' p (subset_closure hpC)) hp₂
  have hqcl : q ∈ closure C := hqK.1
  by_cases hqE : q ∈ E
  · -- `q ∈ C`, an interior point where `ς` has no local minimum
    have hqC : q ∈ C := s28m_far_closure_mem hEo hqE hqcl
    obtain ⟨y, hyC, hy⟩ := s28m_far_no_local_min q (hEo.connectedComponentIn.mem_nhds hqC)
    exact absurd (hqmin' y (subset_closure hyC)) (not_le.2 hy)
  · -- `q ∈ γ {ς ≥ s}`
    simp only [hE, mem_ofPred_eq] at hqE
    push Not at hqE
    obtain ⟨γ, hγ, w', hw', hγw⟩ := hqE
    by_cases hpow : ∀ j : ℤ, ∃ w : ℍ, γ • w ≠ g₀ ^ j • w
    · -- not a power of `g₀`: an edge of a different collar
      have hw's : w'.im / ‖(w' : ℂ)‖ = s := by
        by_contra hne
        have hgt : s < w'.im / ‖(w' : ℂ)‖ := lt_of_le_of_ne hw' (Ne.symm hne)
        have hU : IsOpen {z : ℍ | s < (γ⁻¹ • z).im / ‖((γ⁻¹ • z : ℍ) : ℂ)‖} :=
          isOpen_lt continuous_const (hsigc.comp (continuous_const_smul γ⁻¹))
        have hqU : q ∈ {z : ℍ | s < (γ⁻¹ • z).im / ‖((γ⁻¹ • z : ℍ) : ℂ)‖} := by
          show s < (γ⁻¹ • q).im / ‖((γ⁻¹ • q : ℍ) : ℂ)‖
          rw [← hγw, inv_smul_smul]; exact hgt
        obtain ⟨c, hcU, hcC⟩ := mem_closure_iff.1 hqcl _ hU hqU
        exact hCE hcC γ hγ (γ⁻¹ • c) hcU.le (smul_inv_smul γ c)
      have hC' : ∀ c ∈ C, C = connectedComponentIn E c := fun c hc => connectedComponentIn_eq hc
      have hprop := s28m_far_propagate hΓ hg₀ hl hdil hs₁ hs₁s hdisj hF hFc hγ hw's hCE hC'
        (by rw [hγw]; exact hqcl)
      have hent : γ 0 0 * γ 1 0 ≠ 0 ∨ γ 0 1 * γ 1 1 ≠ 0 := by
        by_contra hno
        push Not at hno
        obtain ⟨j, hj⟩ := hstab γ hγ UpperHalfPlane.I (by simp)
          (s28m_far_axis_of_entries hno.1 hno.2 (by simp))
        obtain ⟨w, hw⟩ := hpow j
        exact hw (hj w)
      obtain ⟨u, hu⟩ := s28m_far_endpoint hent hF w' hε
      exact absurd (hεcl _ (hprop u)) (not_le.2 hu)
    · -- a power of `g₀`: `q` lies in the collar itself, but `ς q < s`
      push Not at hpow
      obtain ⟨j, hj⟩ := hpow
      rw [hj w'] at hγw
      have h2 := s28m_far_sig_zpow hl hdil j w'
      rw [hγw] at h2
      linarith

end LiZhongQC
