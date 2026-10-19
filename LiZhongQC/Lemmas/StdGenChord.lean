import LiZhongQC.Lemmas.StdGenModel

open LeanEval.Topology.ClassificationOfSurfaces Complex Set Metric Filter Topology unitInterval
open scoped Manifold ContDiff

/-!
# Chord loops of the last handle (R83, S27 `[b']`; 下属1)

* `s83sg_chord_classes` [b']: the two chord loops `α`, `β` through the centre of the normal form `Q g` represent
  `b` and `b a⁻¹ b⁻¹` (for the last handle) under a suitable `π₁(Q, α 0) ≃* surfaceGroup g`.

Route: all homotopies are straight-line homotopies in the closed disc pushed to `Q` (`s83cb_homotopic`, for paths
lying over complex paths with the same endpoints); the gluings only enter pointwise. Then groupoid cancellation
(`s83cb_alpha_core`, `s83cb_beta_core`), transport along the ray `R₁` to the vertex, and `s83sg_tracked_pi1`.
-/

noncomputable section
namespace LiZhongQC

/-- Two paths of `Q` lying over complex paths with the same endpoints are homotopic (straight-line homotopy in the
closed disc, pushed forward). -/
theorem s83cb_homotopic {g : ℕ} {x y : Quot (OrientableRel g 0)} (L L' : Path x y) {a b : ℂ} (C C' : Path a b)
    (hL : ∀ t, ∃ z : ClosedUnitDisc, (z : ℂ) = C t ∧ L t = Quot.mk (OrientableRel g 0) z)
    (hL' : ∀ t, ∃ z : ClosedUnitDisc, (z : ℂ) = C' t ∧ L' t = Quot.mk (OrientableRel g 0) z) :
    L.Homotopic L' := by
  have hC : ∀ t, C t ∈ Metric.closedBall (0 : ℂ) 1 := fun t => by
    obtain ⟨z, hz, -⟩ := hL t
    rw [← hz]
    exact z.2
  have hC' : ∀ t, C' t ∈ Metric.closedBall (0 : ℂ) 1 := fun t => by
    obtain ⟨z, hz, -⟩ := hL' t
    rw [← hz]
    exact z.2
  have hmem : ∀ st : I × I,
      (1 - (st.1 : ℝ)) • C st.2 + (st.1 : ℝ) • C' st.2 ∈ Metric.closedBall (0 : ℂ) 1 :=
    fun st => convex_closedBall (0 : ℂ) 1 (hC st.2) (hC' st.2) (sub_nonneg.2 st.1.2.2) st.1.2.1 (by ring)
  have hval : ∀ (t : I) (w : ClosedUnitDisc), (w : ℂ) = C t → L t = Quot.mk (OrientableRel g 0) w := by
    intro t w hw
    obtain ⟨z, hz, hz'⟩ := hL t
    rw [hz']
    congr 1
    exact Subtype.ext (hz.trans hw.symm)
  have hval' : ∀ (t : I) (w : ClosedUnitDisc), (w : ℂ) = C' t → L' t = Quot.mk (OrientableRel g 0) w := by
    intro t w hw
    obtain ⟨z, hz, hz'⟩ := hL' t
    rw [hz']
    congr 1
    exact Subtype.ext (hz.trans hw.symm)
  have hcont : Continuous fun st : I × I => (1 - (st.1 : ℝ)) • C st.2 + (st.1 : ℝ) • C' st.2 :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (C.continuous.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul (C'.continuous.comp continuous_snd))
  refine ⟨{ toFun := fun st => Quot.mk (OrientableRel g 0) ⟨_, hmem st⟩
            continuous_toFun := continuous_quot_mk.comp (hcont.subtype_mk _)
            map_zero_left := fun t => (hval t ⟨_, hmem (0, t)⟩ (by simp)).symm
            map_one_left := fun t => (hval' t ⟨_, hmem (1, t)⟩ (by simp)).symm
            prop' := ?_ }⟩
  intro s t ht
  rcases ht with rfl | rfl
  · refine (hval 0 ⟨_, hmem (s, 0)⟩ ?_).symm
    show (1 - (s : ℝ)) • C 0 + (s : ℝ) • C' 0 = C 0
    rw [C.source, C'.source, ← add_smul, sub_add_cancel, one_smul]
  · refine (hval 1 ⟨_, hmem (s, 1)⟩ ?_).symm
    show (1 - (s : ℝ)) • C 1 + (s : ℝ) • C' 1 = C 1
    rw [C.target, C'.target, ← add_smul, sub_add_cancel, one_smul]

/-- Lying over is compatible with concatenation. -/
theorem s83cb_over_trans {g : ℕ} {x y z : Quot (OrientableRel g 0)} (L₁ : Path x y) (L₂ : Path y z)
    {a b c : ℂ} (C₁ : Path a b) (C₂ : Path b c)
    (h₁ : ∀ t, ∃ w : ClosedUnitDisc, (w : ℂ) = C₁ t ∧ L₁ t = Quot.mk (OrientableRel g 0) w)
    (h₂ : ∀ t, ∃ w : ClosedUnitDisc, (w : ℂ) = C₂ t ∧ L₂ t = Quot.mk (OrientableRel g 0) w) :
    ∀ t, ∃ w : ClosedUnitDisc, (w : ℂ) = (C₁.trans C₂) t ∧
      (L₁.trans L₂) t = Quot.mk (OrientableRel g 0) w := by
  intro t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact h₁ _
  · exact h₂ _

/-- Lying over is compatible with reversal. -/
theorem s83cb_over_symm {g : ℕ} {x y : Quot (OrientableRel g 0)} (L : Path x y) {a b : ℂ} (C : Path a b)
    (h : ∀ t, ∃ w : ClosedUnitDisc, (w : ℂ) = C t ∧ L t = Quot.mk (OrientableRel g 0) w) :
    ∀ t, ∃ w : ClosedUnitDisc, (w : ℂ) = C.symm t ∧ L.symm t = Quot.mk (OrientableRel g 0) w := by
  intro t
  rw [Path.symm_apply, Path.symm_apply]
  exact h _

/-- Groupoid cancellation `γ (γ⁻¹ δ) = δ`. -/
theorem s83cb_cancel {X : Type*} [TopologicalSpace X] {x y z : X} (γ : Path.Homotopic.Quotient x y)
    (δ : Path.Homotopic.Quotient x z) : γ.trans (γ.symm.trans δ) = δ := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

/-- Groupoid cancellation `γ⁻¹ (γ δ) = δ`. -/
theorem s83cb_cancel' {X : Type*} [TopologicalSpace X] {x y z : X} (γ : Path.Homotopic.Quotient y x)
    (δ : Path.Homotopic.Quotient x z) : γ.symm.trans (γ.trans δ) = δ := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

/-- Groupoid algebra for the loop `α ≃ R₁ G G⁻¹ R₂⁻¹`, `R₂⁻¹ ≃ L_b⁻¹ R₁⁻¹`. -/
theorem s83cb_alpha_core {X : Type*} [TopologicalSpace X] {P V M : X} (L : Path P P) (A1 : Path P M)
    (A2 : Path M P) (R1 R2 : Path P V) (G : Path V M) (Lb : Path V V) (hL : L = A1.trans A2)
    (h1 : A1.Homotopic (R1.trans G)) (h2 : A2.Homotopic (G.symm.trans R2.symm))
    (h3 : R2.symm.Homotopic (Lb.symm.trans R1.symm)) :
    Path.Homotopic.Quotient.mk (R1.symm.trans (L.trans R1)) = Path.Homotopic.Quotient.mk Lb.symm := by
  subst hL
  have e1 := Path.Homotopic.Quotient.eq.2 h1
  have e2 := Path.Homotopic.Quotient.eq.2 h2
  have e3 := Path.Homotopic.Quotient.eq.2 h3
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm] at e1 e2 e3 ⊢
  rw [e1, e2, e3]
  simp only [Path.Homotopic.Quotient.trans_assoc, s83cb_cancel, s83cb_cancel',
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]

/-- Groupoid algebra for the loop `β ≃ R₂ G G⁻¹ R₃⁻¹`, `R₃⁻¹ ≃ L_a R₂⁻¹`, `R₂ ≃ R₁ L_b`. -/
theorem s83cb_beta_core {X : Type*} [TopologicalSpace X] {P V M : X} (L : Path P P) (B1 : Path P M)
    (B2 : Path M P) (R1 R2 R3 : Path P V) (G : Path V M) (La Lb : Path V V) (hL : L = B1.trans B2)
    (h1 : B1.Homotopic (R2.trans G)) (h2 : B2.Homotopic (G.symm.trans R3.symm))
    (h3 : R3.symm.Homotopic (La.trans R2.symm)) (h4 : R2.Homotopic (R1.trans Lb))
    (h5 : R2.symm.Homotopic (Lb.symm.trans R1.symm)) :
    Path.Homotopic.Quotient.mk (R1.symm.trans (L.trans R1)) =
      Path.Homotopic.Quotient.mk (Lb.trans (La.trans Lb.symm)) := by
  subst hL
  have e1 := Path.Homotopic.Quotient.eq.2 h1
  have e2 := Path.Homotopic.Quotient.eq.2 h2
  have e3 := Path.Homotopic.Quotient.eq.2 h3
  have e4 := Path.Homotopic.Quotient.eq.2 h4
  have e5 := Path.Homotopic.Quotient.eq.2 h5
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm] at e1 e2 e3 e4 e5 ⊢
  rw [e1, e2, e3, e5, e4]
  simp only [Path.Homotopic.Quotient.trans_assoc, s83cb_cancel, s83cb_cancel',
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]

/-! Sub-stub `[b']` of `s83sg_chord_model` (R83, S27): the classes of the two chord loops of the last handle.
`Q := Quot (OrientableRel g 0)`, `π := Quot.mk _`.  Positions on the boundary circle are in units of `2π/(4g)`:
the last handle is `a_{g-1} b_{g-1} a_{g-1}⁻¹ b_{g-1}⁻¹` on `[m, m+4]`, `m = 4(g-1)`; the midpoints of its four
sides are at angles `θ_j = 2π (m + j + 1/2)/(4g)` (`j = 0, 1, 2, 3`).  The loop `α` runs out along the ray of
angle `θ₀` to the midpoint of the first copy of `a` (which is glued to the midpoint of the second copy, angle
`θ₂`) and returns along the ray `θ₂`; `β` does the same with `θ₁`, `θ₃` (sides `b`, `b⁻¹`).  Homotopy proof
sketch (all homotopies take place in the convex disc and are pushed forward): with `R_k` the images of the rays
to the vertices (all vertices are one point `V`), `R_{k+1} ≃ R_k * arc_k`, `α ≃ R₀ a R₂⁻¹`, `β ≃ R₁ b R₃⁻¹`, so after
transport along `R₁`, `α ↦ b⁻¹` and `β ↦ b a b⁻¹`, then apply `s83sg_tracked_pi1`. -/
theorem s83sg_chord_classes (g : ℕ) (hg : 1 < g) (α β : ℝ → Quot (OrientableRel g 0))
    (hα1 : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ z : ClosedUnitDisc,
      (z : ℂ) = ((2 * t : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * (4 * ((g : ℝ) - 1) + 0 + 1 / 2) / (4 * g) : ℝ) : ℂ) * Complex.I) ∧
        α t = Quot.mk (OrientableRel g 0) z)
    (hα2 : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∃ z : ClosedUnitDisc,
      (z : ℂ) = ((2 * (1 - t) : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * (4 * ((g : ℝ) - 1) + 2 + 1 / 2) / (4 * g) : ℝ) : ℂ) * Complex.I) ∧
        α t = Quot.mk (OrientableRel g 0) z)
    (hβ1 : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ z : ClosedUnitDisc,
      (z : ℂ) = ((2 * t : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * (4 * ((g : ℝ) - 1) + 1 + 1 / 2) / (4 * g) : ℝ) : ℂ) * Complex.I) ∧
        β t = Quot.mk (OrientableRel g 0) z)
    (hβ2 : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, ∃ z : ClosedUnitDisc,
      (z : ℂ) = ((2 * (1 - t) : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * (4 * ((g : ℝ) - 1) + 3 + 1 / 2) / (4 * g) : ℝ) : ℂ) * Complex.I) ∧
        β t = Quot.mk (OrientableRel g 0) z) :
    ∃ (e₀ : FundamentalGroup (Quot (OrientableRel g 0)) (α 0) ≃* surfaceGroup g) (ga gb : surfaceGroup g)
      (s₁ s₂ s₃ : ℤ),
      ga = (PresentedGroup.of (Sum.inl ⟨g - 1, by omega⟩ : Fin g ⊕ Fin g) : surfaceGroup g) ∧
      gb = (PresentedGroup.of (Sum.inr ⟨g - 1, by omega⟩ : Fin g ⊕ Fin g) : surfaceGroup g) ∧
      (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧ (s₃ = 1 ∨ s₃ = -1) ∧
      (∀ L : Path (α 0) (α 0), (∀ t : I, L t = α t) →
        e₀ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = gb ^ s₁) ∧
      (∀ L : Path (α 0) (α 0), (∀ t : I, L t = β t) →
        e₀ (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L)) = gb ^ s₂ * ga ^ s₃ * gb ^ (-s₂)) := by
  classical
  have hp : 1 ≤ g := by omega
  let one : Set.Ioc (0 : ℝ) 1 := ⟨1, zero_lt_one, le_rfl⟩
  obtain ⟨e, he⟩ := s83sg_tracked_pi1 g hp one rfl
  let Ψ : ℝ → Quot (OrientableRel g 0) := fun u =>
    ((s78dg_cs_Psi_fun g hp (one, u) : ↥(s78dg_cs_U g 0)) : Quot (OrientableRel g 0))
  let w : ℝ → ℂ := fun u => Complex.exp (2 * Real.pi * Complex.I * ((u / (4 * g) : ℝ) : ℂ))
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = 4 * ((g : ℝ) - 1) := ⟨_, rfl⟩
  -- basic facts on `w` and `Ψ`
  have hwc : Continuous w :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_id.div_const _)))
  have hw1 : ∀ u, ‖w u‖ = 1 := fun u => by
    show ‖Complex.exp (2 * Real.pi * Complex.I * ((u / (4 * g) : ℝ) : ℂ))‖ = 1
    rw [show (2 * Real.pi * Complex.I * ((u / (4 * g) : ℝ) : ℂ)) =
      ((2 * Real.pi * (u / (4 * g)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hmem : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → ∀ u, (ρ : ℂ) * w u ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro ρ h0 h1 u
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, hw1, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1
  have hbd : ∀ u, w u ∈ Metric.closedBall (0 : ℂ) 1 := fun u => by
    rw [Metric.mem_closedBall, dist_zero_right, hw1]
  have hΨ : ∀ (u : ℝ) (z : ClosedUnitDisc), (z : ℂ) = w u → Quot.mk (OrientableRel g 0) z = Ψ u := by
    intro u z hz
    obtain ⟨z', hz', hΨ'⟩ := s78dg_cs_Psi_spec g hp one u
    rw [show Ψ u = _ from hΨ']
    congr 1
    apply Subtype.ext
    rw [hz, hz']
    show w u = ((1 : ℝ) : ℂ) * _
    rw [Complex.ofReal_one, one_mul]
  have hΨc : Continuous Ψ := continuous_subtype_val.comp (s78dg_cs_Psi_cont g hp one)
  have hvert : ∀ k : ℕ, Ψ (m + k) = Ψ 0 := by
    intro k
    have h := s78dg_cs_Psi_vertex g hp one rfl ((4 * (g - 1) + k : ℕ) : ℤ)
    have hc : (((4 * (g - 1) + k : ℕ) : ℤ) : ℝ) = m + k := by
      rw [hm]
      push_cast [Nat.cast_sub hp]
      ring
    rw [hc] at h
    exact congrArg Subtype.val h
  have hv0 : Ψ m = Ψ 0 := by simpa using hvert 0
  have hv1 : Ψ (m + 1) = Ψ 0 := by simpa using hvert 1
  have hv2 : Ψ (m + 2) = Ψ 0 := by simpa using hvert 2
  have hv3 : Ψ (m + 3) = Ψ 0 := by simpa using hvert 3
  let i₀ : Fin g := ⟨g - 1, by omega⟩
  have hi₀ : 4 * ((i₀ : ℕ) : ℝ) = m := by
    rw [hm]
    show 4 * (((g - 1 : ℕ)) : ℝ) = _
    rw [Nat.cast_sub hp, Nat.cast_one]
  have hrelA : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Ψ (m + x) = Ψ (m + 3 - x) := by
    intro x h0 h1
    have h := congrArg Subtype.val (s78dg_cs_Psi_rel_a g hp one rfl i₀ x h0 h1)
    rw [hi₀] at h
    exact h
  have hrelB : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Ψ (m + 1 + x) = Ψ (m + 4 - x) := by
    intro x h0 h1
    have h := congrArg Subtype.val (s78dg_cs_Psi_rel_b g hp one rfl i₀ x h0 h1)
    rw [hi₀] at h
    exact h
  have hP : ∀ z : ClosedUnitDisc, (z : ℂ) = 0 → Quot.mk (OrientableRel g 0) z = α 0 := by
    intro z hz
    obtain ⟨z0, hz0, hα0⟩ := hα1 0 ⟨le_rfl, by norm_num⟩
    rw [hα0]
    congr 1
    apply Subtype.ext
    rw [hz, hz0]
    simp
  have hexp : ∀ c : ℝ, Complex.exp (((2 * Real.pi * (4 * ((g : ℝ) - 1) + c + 1 / 2) / (4 * g) : ℝ) : ℂ) *
      Complex.I) = w (m + c + 1 / 2) := by
    intro c
    rw [hm]
    show _ = Complex.exp _
    congr 1
    push_cast
    ring
  -- complex paths
  let seg : ∀ u : ℝ, Path (0 : ℂ) (w u) := fun u =>
    { toFun := fun t => ((t : ℝ) : ℂ) * w u
      continuous_toFun := (Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const
      source' := by simp
      target' := by simp }
  let arc : ∀ u v : ℝ, Path (w u) (w v) := fun u v =>
    { toFun := fun t => w (u + (v - u) * t)
      continuous_toFun := hwc.comp (continuous_const.add (continuous_const.mul continuous_subtype_val))
      source' := by simp
      target' := by simp }
  -- paths of `Q`
  let ray : ∀ u : ℝ, Path (α 0) (Ψ u) := fun u =>
    { toFun := fun t => Quot.mk (OrientableRel g 0) ⟨((t : ℝ) : ℂ) * w u, hmem t t.2.1 t.2.2 u⟩
      continuous_toFun := continuous_quot_mk.comp (Continuous.subtype_mk
        ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const) _)
      source' := hP _ (by simp)
      target' := hΨ _ _ (by simp) }
  let parc : ∀ (u v : ℝ) (x y : Quot (OrientableRel g 0)), Ψ u = x → Ψ v = y → Path x y :=
    fun u v x y hx hy =>
      { toFun := fun t => Ψ (u + (v - u) * t)
        continuous_toFun := hΨc.comp (continuous_const.add (continuous_const.mul continuous_subtype_val))
        source' := by simpa using hx
        target' := by simpa using hy }
  have hray : ∀ u t, ∃ z : ClosedUnitDisc, (z : ℂ) = seg u t ∧ ray u t = Quot.mk (OrientableRel g 0) z :=
    fun u t => ⟨_, rfl, rfl⟩
  have hover : ∀ {x y : Quot (OrientableRel g 0)} (L : Path x y) {a b : ℂ} (C : Path a b) (f f' : I → ℝ),
      (∀ t, L t = Ψ (f t)) → (∀ t, C t = w (f' t)) → (∀ t, Ψ (f t) = Ψ (f' t)) →
      ∀ t, ∃ z : ClosedUnitDisc, (z : ℂ) = C t ∧ L t = Quot.mk (OrientableRel g 0) z :=
    fun {x y} L {a b} C f f' h1 h2 h3 t =>
      ⟨⟨w (f' t), hbd _⟩, (h2 t).symm, (h1 t).trans ((h3 t).trans (hΨ _ _ rfl).symm)⟩
  let R1 : Path (α 0) (Ψ 0) := (ray (m + 1)).cast rfl hv1.symm
  let R2 : Path (α 0) (Ψ 0) := (ray (m + 2)).cast rfl hv2.symm
  let R3 : Path (α 0) (Ψ 0) := (ray (m + 3)).cast rfl hv3.symm
  let La : Path (Ψ 0) (Ψ 0) := parc m (m + 1) _ _ hv0 hv1
  let Lb : Path (Ψ 0) (Ψ 0) := parc (m + 1) (m + 2) _ _ hv1 hv2
  let Ga : Path (Ψ 0) (Ψ (m + 0 + 1 / 2)) := parc (m + 1) (m + 0 + 1 / 2) _ _ hv1 rfl
  let Gb : Path (Ψ 0) (Ψ (m + 1 + 1 / 2)) := parc (m + 2) (m + 1 + 1 / 2) _ _ hv2 rfl
  have hMa : Ψ (m + 0 + 1 / 2) = Ψ (m + 2 + 1 / 2) := by
    have h := hrelA (1 / 2) (by norm_num) (by norm_num)
    convert h using 2 <;> ring
  have hMb : Ψ (m + 1 + 1 / 2) = Ψ (m + 3 + 1 / 2) := by
    have h := hrelB (1 / 2) (by norm_num) (by norm_num)
    convert h using 2
    ring
  let A1 : Path (α 0) (Ψ (m + 0 + 1 / 2)) := ray (m + 0 + 1 / 2)
  let A2 : Path (Ψ (m + 0 + 1 / 2)) (α 0) := (ray (m + 2 + 1 / 2)).symm.cast hMa rfl
  let B1 : Path (α 0) (Ψ (m + 1 + 1 / 2)) := ray (m + 1 + 1 / 2)
  let B2 : Path (Ψ (m + 1 + 1 / 2)) (α 0) := (ray (m + 3 + 1 / 2)).symm.cast hMb rfl
  -- over-facts
  have oR1 : ∀ t, ∃ z : ClosedUnitDisc, (z : ℂ) = seg (m + 1) t ∧ R1 t = Quot.mk (OrientableRel g 0) z :=
    fun t => hray _ t
  have oR2 : ∀ t, ∃ z : ClosedUnitDisc, (z : ℂ) = seg (m + 2) t ∧ R2 t = Quot.mk (OrientableRel g 0) z :=
    fun t => hray _ t
  have oR3 : ∀ t, ∃ z : ClosedUnitDisc, (z : ℂ) = seg (m + 3) t ∧ R3 t = Quot.mk (OrientableRel g 0) z :=
    fun t => hray _ t
  have oLb := hover Lb (arc (m + 1) (m + 2)) (fun t => m + 1 + (m + 2 - (m + 1)) * t)
    (fun t => m + 1 + (m + 2 - (m + 1)) * t) (fun t => rfl) (fun t => rfl) (fun t => rfl)
  have oLa := hover La (arc (m + 3) (m + 2)) (fun t => m + (m + 1 - m) * t)
    (fun t => m + 3 + (m + 2 - (m + 3)) * t) (fun t => rfl) (fun t => rfl) (fun t => by
      have h := hrelA t t.2.1 t.2.2
      convert h using 2 <;> ring)
  have oGa := hover Ga (arc (m + 1) (m + 0 + 1 / 2)) (fun t => m + 1 + (m + 0 + 1 / 2 - (m + 1)) * t)
    (fun t => m + 1 + (m + 0 + 1 / 2 - (m + 1)) * t) (fun t => rfl) (fun t => rfl) (fun t => rfl)
  have oGa' := hover Ga (arc (m + 2) (m + 2 + 1 / 2)) (fun t => m + 1 + (m + 0 + 1 / 2 - (m + 1)) * t)
    (fun t => m + 2 + (m + 2 + 1 / 2 - (m + 2)) * t) (fun t => rfl) (fun t => rfl) (fun t => by
      have h := hrelA (1 - (t : ℝ) / 2) (by linarith [t.2.2]) (by linarith [t.2.1])
      convert h using 2 <;> ring)
  have oGb := hover Gb (arc (m + 2) (m + 1 + 1 / 2)) (fun t => m + 2 + (m + 1 + 1 / 2 - (m + 2)) * t)
    (fun t => m + 2 + (m + 1 + 1 / 2 - (m + 2)) * t) (fun t => rfl) (fun t => rfl) (fun t => rfl)
  have oGb' := hover Gb (arc (m + 3) (m + 3 + 1 / 2)) (fun t => m + 2 + (m + 1 + 1 / 2 - (m + 2)) * t)
    (fun t => m + 3 + (m + 3 + 1 / 2 - (m + 3)) * t) (fun t => rfl) (fun t => rfl) (fun t => by
      have h := hrelB (1 - (t : ℝ) / 2) (by linarith [t.2.2]) (by linarith [t.2.1])
      convert h using 2 <;> ring)
  -- homotopies
  have hA1 : A1.Homotopic (R1.trans Ga) :=
    s83cb_homotopic A1 _ (seg (m + 0 + 1 / 2)) ((seg (m + 1)).trans (arc (m + 1) (m + 0 + 1 / 2)))
      (hray _) (s83cb_over_trans R1 Ga _ _ oR1 oGa)
  have hA2 : A2.Homotopic (Ga.symm.trans R2.symm) :=
    s83cb_homotopic A2 _ (seg (m + 2 + 1 / 2)).symm
      ((arc (m + 2) (m + 2 + 1 / 2)).symm.trans (seg (m + 2)).symm)
      (s83cb_over_symm (ray (m + 2 + 1 / 2)) _ (hray _))
      (s83cb_over_trans _ _ _ _ (s83cb_over_symm Ga _ oGa') (s83cb_over_symm R2 _ oR2))
  have hR2s : R2.symm.Homotopic (Lb.symm.trans R1.symm) :=
    s83cb_homotopic _ _ (seg (m + 2)).symm ((arc (m + 1) (m + 2)).symm.trans (seg (m + 1)).symm)
      (s83cb_over_symm R2 _ oR2)
      (s83cb_over_trans _ _ _ _ (s83cb_over_symm Lb _ oLb) (s83cb_over_symm R1 _ oR1))
  have hR2 : R2.Homotopic (R1.trans Lb) :=
    s83cb_homotopic _ _ (seg (m + 2)) ((seg (m + 1)).trans (arc (m + 1) (m + 2))) oR2
      (s83cb_over_trans R1 Lb _ _ oR1 oLb)
  have hB1 : B1.Homotopic (R2.trans Gb) :=
    s83cb_homotopic B1 _ (seg (m + 1 + 1 / 2)) ((seg (m + 2)).trans (arc (m + 2) (m + 1 + 1 / 2)))
      (hray _) (s83cb_over_trans R2 Gb _ _ oR2 oGb)
  have hB2 : B2.Homotopic (Gb.symm.trans R3.symm) :=
    s83cb_homotopic B2 _ (seg (m + 3 + 1 / 2)).symm
      ((arc (m + 3) (m + 3 + 1 / 2)).symm.trans (seg (m + 3)).symm)
      (s83cb_over_symm (ray (m + 3 + 1 / 2)) _ (hray _))
      (s83cb_over_trans _ _ _ _ (s83cb_over_symm Gb _ oGb') (s83cb_over_symm R3 _ oR3))
  have hR3s : R3.symm.Homotopic (La.trans R2.symm) :=
    s83cb_homotopic _ _ (seg (m + 3)).symm ((arc (m + 3) (m + 2)).trans (seg (m + 2)).symm)
      (s83cb_over_symm R3 _ oR3) (s83cb_over_trans La _ _ _ oLa (s83cb_over_symm R2 _ oR2))
  -- the loops are the concatenations
  have hLα : ∀ L : Path (α 0) (α 0), (∀ t : I, L t = α t) → L = A1.trans A2 := by
    intro L hL
    ext t
    rw [hL t, Path.trans_apply]
    split_ifs with ht
    · obtain ⟨z, hz, hαz⟩ := hα1 t ⟨t.2.1, ht⟩
      rw [hαz]
      congr 1
      apply Subtype.ext
      rw [hz, hexp]
    · obtain ⟨z, hz, hαz⟩ := hα2 t ⟨(not_le.1 ht).le, t.2.2⟩
      rw [hαz]
      show _ = Quot.mk (OrientableRel g 0) ⟨_, _⟩
      congr 1
      apply Subtype.ext
      rw [hz, hexp]
      show _ = (((σ ⟨2 * (t : ℝ) - 1, _⟩ : I) : ℝ) : ℂ) * _
      rw [unitInterval.coe_symm_eq]
      congr 1
      push_cast
      ring
  have hLβ : ∀ L : Path (α 0) (α 0), (∀ t : I, L t = β t) → L = B1.trans B2 := by
    intro L hL
    ext t
    rw [hL t, Path.trans_apply]
    split_ifs with ht
    · obtain ⟨z, hz, hβz⟩ := hβ1 t ⟨t.2.1, ht⟩
      rw [hβz]
      congr 1
      apply Subtype.ext
      rw [hz, hexp]
    · obtain ⟨z, hz, hβz⟩ := hβ2 t ⟨(not_le.1 ht).le, t.2.2⟩
      rw [hβz]
      show _ = Quot.mk (OrientableRel g 0) ⟨_, _⟩
      congr 1
      apply Subtype.ext
      rw [hz, hexp]
      show _ = (((σ ⟨2 * (t : ℝ) - 1, _⟩ : I) : ℝ) : ℂ) * _
      rw [unitInterval.coe_symm_eq]
      congr 1
      push_cast
      ring
  -- petals
  have hfract : ∀ (c : ℝ), (∃ k : ℕ, c = m + k) → ∀ t : I, Ψ (c + t) = Ψ (c + Int.fract (t : ℝ)) := by
    rintro c ⟨k, rfl⟩ t
    rcases lt_or_eq_of_le t.2.2 with ht | ht
    · rw [Int.fract_eq_self.2 ⟨t.2.1, ht⟩]
    · rw [ht, Int.fract_one, add_zero, add_assoc]
      have h1 := hvert (k + 1)
      push_cast at h1
      rw [h1, hvert k]
  have hEa : s78dg_cs_E (2 * (i₀ : ℕ)) = m := by
    unfold s78dg_cs_E
    have h : 4 * (2 * (i₀ : ℕ) / 2) + 2 * (i₀ : ℕ) % 2 = 4 * (g - 1) := by
      show 4 * (2 * (g - 1) / 2) + 2 * (g - 1) % 2 = 4 * (g - 1)
      omega
    rw [h, hm]
    push_cast [Nat.cast_sub hp]
    ring
  have hEb : s78dg_cs_E (2 * (i₀ : ℕ) + 1) = m + 1 := by
    unfold s78dg_cs_E
    have h : 4 * ((2 * (i₀ : ℕ) + 1) / 2) + (2 * (i₀ : ℕ) + 1) % 2 = 4 * (g - 1) + 1 := by
      show 4 * ((2 * (g - 1) + 1) / 2) + (2 * (g - 1) + 1) % 2 = 4 * (g - 1) + 1
      omega
    rw [h, hm]
    push_cast [Nat.cast_sub hp]
    ring
  have ha : e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk La)) =
      (PresentedGroup.of (Sum.inl i₀ : Fin g ⊕ Fin g) : surfaceGroup g)⁻¹ := by
    refine (he i₀ La).1 fun t => ?_
    show Ψ (m + (m + 1 - m) * t) = Ψ (s78dg_cs_E (2 * (i₀ : ℕ)) + Int.fract (t : ℝ))
    rw [hEa, ← hfract m ⟨0, by simp⟩ t]
    congr 1
    ring
  have hb : e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Lb)) =
      (PresentedGroup.of (Sum.inr i₀ : Fin g ⊕ Fin g) : surfaceGroup g)⁻¹ := by
    refine (he i₀ Lb).2 fun t => ?_
    show Ψ (m + 1 + (m + 2 - (m + 1)) * t) = Ψ (s78dg_cs_E (2 * (i₀ : ℕ) + 1) + Int.fract (t : ℝ))
    rw [hEb, ← hfract (m + 1) ⟨1, by simp⟩ t]
    congr 1
    ring
  -- assembly
  refine ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPath R1).trans e, _, _, 1, 1, -1, rfl, rfl,
    Or.inl rfl, Or.inl rfl, Or.inr rfl, fun L hL => ?_, fun L hL => ?_⟩
  · have hc := s83cb_alpha_core L A1 A2 R1 R2 Ga Lb (hLα L hL) hA1 hA2 hR2s
    show e (FundamentalGroup.fundamentalGroupMulEquivOfPath R1
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L))) = _
    rw [s78dg_conj_mk, hc, Path.Homotopic.Quotient.mk_symm]
    show e (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Lb))⁻¹ = _
    rw [map_inv, hb]
    exact (inv_inv _).trans (zpow_one _).symm
  · have hc := s83cb_beta_core L B1 B2 R1 R2 R3 Gb La Lb (hLβ L hL) hB1 hB2 hR3s hR2 hR2s
    show e (FundamentalGroup.fundamentalGroupMulEquivOfPath R1
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk L))) = _
    rw [s78dg_conj_mk, hc, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_symm]
    show e ((FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Lb))⁻¹ *
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk La) *
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Lb)) = _
    rw [map_mul, map_mul, map_inv, ha, hb]
    exact congrArg₂ (· * ·) (congrArg₂ (· * ·) ((inv_inv _).trans (zpow_one _).symm) (zpow_neg_one _).symm)
      (zpow_neg_one _).symm

end LiZhongQC
