import Mathlib

/-!
# Winding numbers, boundary angles and Hopf's Umlaufsatz for piecewise-`C¹` loops

The planar part of Teichmüller's lemma (Theorem 25.2), imported by
`LiZhongQC.Ch07.S25_QuadraticDifferentials`.  It is purely planar and imports only
`Mathlib`: no project file, no Jordan curve theorem (the one consequence of the JCT that is needed,
connectedness of `(closure dom)ᶜ`, is a hypothesis, supplied in S25 from `JordanBridge`).

A *corner loop* is a family `c : Fin n → ℝ → ℂ` of `C¹` arcs on `[0, 1]` with non-vanishing
(one-sided at the ends) derivatives, `c j 1 = c (j + 1) 0`, meeting only at consecutive vertices,
and without cusps.  Angles along a curve are recorded by *angle functions*
(`b2_IsAngleFn f a b θ`: `θ` continuous on `[a, b]` and `f = |f| e^{iθ}` on `(a, b)`), so that no
branch of `arg` and no `deriv` junk value enters any statement.

Public results (consumed by S25):
* `b2_wind_in` / `b2_wind_out`: the positively oriented boundary winds once around interior points
  and not at all around exterior points;
* `b2_bwa`: the boundary winding angle at a vertex is the interior angle `π - b2_extAngle c k`;
* `b2_umlaufsatz`: the total tangent turning along the sides is `2π - Σ (exterior angles)`;
* `b2_exists_angleFn_tangent/off/vertex`: the angle functions these statements quantify over exist.

Internally everything is reduced to the glued `n`-periodic loop `b2_loop c` (`Fin.CommRing` is
opened locally for the cast `ℤ → Fin n`):
* loop, tangents, chord estimates, angle-function toolkit, per-side ↔ loop sums, winding
  basics (`b2_wind_rebase/int/const/far`, whence `b2_wind_loop_out`);
* `b2_wind_loop_in`, `b2_bwa_loop` (local jump at a boundary point + orientation);
* `b2_hopf_loop` (Hopf's secant-map argument; orientation free).
-/

open Complex Set Metric Filter Topology
open scoped Real

noncomputable section

namespace LiZhongQC

/-! ## Corner loops, positively bounded domains and angle functions -/

/-- `c : Fin n → ℝ → ℂ` is a *corner loop*: each side `c j` is `C¹` on `[0, 1]` with non-vanishing
derivative (one-sided at the end points), side `j` ends where side `j + 1` starts, two sides meet only
at consecutive vertices (injectivity on the half-open parameter intervals), and there are no cusps (the
turning `u_j / v_{j-1}` from the incoming to the outgoing direction at the vertex `c j 0` is not a
negative real). -/
def b2_IsCornerLoop {n : ℕ} [NeZero n] (c : Fin n → ℝ → ℂ) : Prop :=
  (∀ j, ContDiffOn ℝ 1 (c j) (Icc 0 1)) ∧
    (∀ j, ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (c j) (Icc 0 1) t ≠ 0) ∧
    (∀ j, c j 1 = c (j + 1) 0) ∧
    (∀ i j : Fin n, ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1, c i s = c j t → i = j ∧ s = t) ∧
    (∀ j, derivWithin (c j) (Icc 0 1) 0 / derivWithin (c (j - 1)) (Icc 0 1) 1 ∈ slitPlane)

/-- The exterior (turning) angle of a corner loop at the vertex `c k 0`: the principal argument of
`u_k / v_{k-1}`, `u_k` the outgoing and `v_{k-1}` the incoming direction.  For a corner loop it lies in
`(-π, π)`; the interior angle is `π - b2_extAngle c k`. -/
def b2_extAngle {n : ℕ} [NeZero n] (c : Fin n → ℝ → ℂ) (k : Fin n) : ℝ :=
  arg (derivWithin (c k) (Icc 0 1) 0 / derivWithin (c (k - 1)) (Icc 0 1) 1)

/-- `dom` is a bounded domain positively bounded by the corner loop `c`: open, connected, bounded,
with connected exterior `(closure dom)ᶜ` (the Jordan-curve-theorem input), frontier the trace of the
loop, and lying to the left of the loop at (at least) one smooth boundary point. -/
def b2_IsPosBoundary {n : ℕ} [NeZero n] (c : Fin n → ℝ → ℂ) (dom : Set ℂ) : Prop :=
  IsOpen dom ∧ IsConnected dom ∧ Bornology.IsBounded dom ∧ IsConnected (closure dom)ᶜ ∧
    frontier dom = ⋃ j, c j '' Icc 0 1 ∧
    ∃ j, ∃ t ∈ Ioo (0 : ℝ) 1, ∀ᶠ ε : ℝ in 𝓝[>] 0, c j t + (ε : ℂ) * I * deriv (c j) t ∈ dom

/-- `θ` is a continuous angle function of `f` on `[a, b]`: `θ` is continuous on the closed interval
and `f t = |f t| e^{i θ t}` on the open interval.  (The end values of `θ` are thereby limits; `f` itself
may be undefined, zero or discontinuous at the end points.) -/
def b2_IsAngleFn (f : ℝ → ℂ) (a b : ℝ) (θ : ℝ → ℝ) : Prop :=
  ContinuousOn θ (Icc a b) ∧ ∀ t ∈ Ioo a b, f t = (‖f t‖ : ℂ) * exp ((θ t : ℂ) * I)

/-! ## Angle-function toolkit -/

/-- The change of an angle function does not depend on the choice: two angle functions of the
same `f`, non-vanishing on `(a, b)`, differ by a constant. -/
theorem b2_angleFn_change_eq {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf : ∀ t ∈ Ioo a b, f t ≠ 0)
    {θ₁ θ₂ : ℝ → ℝ} (h₁ : b2_IsAngleFn f a b θ₁) (h₂ : b2_IsAngleFn f a b θ₂) :
    θ₁ b - θ₁ a = θ₂ b - θ₂ a := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · ring
  set D : ℝ → ℂ := fun t => ((θ₁ t - θ₂ t : ℝ) : ℂ) * I with hDdef
  have hDmem : ∀ t ∈ Ioo a b, D t ∈ AddSubgroup.zmultiples (2 * π * I) := by
    intro t ht
    have hn : (‖f t‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 (hf t ht)
    have he : exp ((θ₁ t : ℂ) * I) = exp ((θ₂ t : ℂ) * I) :=
      mul_left_cancel₀ hn ((h₁.2 t ht).symm.trans (h₂.2 t ht))
    have h1 : exp (D t) = 1 := by
      rw [hDdef]
      push_cast
      rw [sub_mul, Complex.exp_sub, he, div_self (Complex.exp_ne_zero _)]
    rw [AddSubgroup.mem_zmultiples_iff]
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h1
    exact ⟨k, by rw [hk]; simp⟩
  classical
  let F : ℝ → AddSubgroup.zmultiples (2 * π * I) := fun t =>
    if h : t ∈ Ioo a b then ⟨D t, hDmem t h⟩ else 0
  have hFval : ∀ t ∈ Ioo a b, (F t : ℂ) = D t := fun t ht => by simp only [F, dite_eq_left, ht]
  have hDc : ContinuousOn D (Icc a b) := by
    have : ContinuousOn (fun t => θ₁ t - θ₂ t) (Icc a b) := h₁.1.sub h₂.1
    exact (Complex.continuous_ofReal.comp_continuousOn this).mul continuousOn_const
  have hFc : ContinuousOn F (Ioo a b) := by
    have h1 : ContinuousOn (fun t => (F t : ℂ)) (Ioo a b) :=
      (hDc.mono Ioo_subset_Icc_self).congr hFval
    exact (Topology.IsEmbedding.subtypeVal.isInducing).continuousOn_iff.2 h1
  set m : ℝ := (a + b) / 2 with hmdef
  have hm : m ∈ Ioo a b := ⟨by rw [hmdef]; linarith, by rw [hmdef]; linarith⟩
  have hconst : EqOn (fun t => θ₁ t - θ₂ t) (fun _ => θ₁ m - θ₂ m) (Ioo a b) := by
    intro t ht
    have hFt : F t = F m := IsPreconnected.constant isPreconnected_Ioo hFc ht hm
    have := congrArg Subtype.val hFt
    rw [hFval t ht, hFval m hm, hDdef] at this
    have h2 := congrArg Complex.im this
    simpa using h2
  have hcl : EqOn (fun t => θ₁ t - θ₂ t) (fun _ => θ₁ m - θ₂ m) (Icc a b) :=
    hconst.of_subset_closure (h₁.1.sub h₂.1) continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo hlt.ne])
  have ha := hcl (left_mem_Icc.2 hab)
  have hb := hcl (right_mem_Icc.2 hab)
  simp only at ha hb
  linarith

/-- Existence of angle functions: if on `(a, b)` the function `f` is a positive multiple of a
function `g` that is continuous and non-vanishing on `[a, b]`, then `f` has an angle function. -/
theorem b2_exists_angleFn {f g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Icc a b))
    (hg0 : ∀ t ∈ Icc a b, g t ≠ 0) (hfg : ∀ t ∈ Ioo a b, ∃ r : ℝ, 0 < r ∧ f t = r * g t) :
    ∃ θ, b2_IsAngleFn f a b θ := by
  set ge : ℝ → ℂ := Set.IccExtend hab ((Icc a b).domRestrict g) with hgedef
  have hge : Continuous ge :=
    continuous_IccExtend_iff.2 (continuousOn_iff_continuous_domRestrict.mp hg)
  have hgeq : ∀ t ∈ Icc a b, ge t = g t := fun t ht => IccExtend_of_mem hab _ ht
  have hgne : ∀ t, ge t ≠ 0 := fun t => hg0 _ (projIcc a b hab t).2
  have hU : IsSimplyConnected (univ : Set ℝ) := by
    unfold IsSimplyConnected
    have : ContractibleSpace (univ : Set ℝ) :=
      (convex_univ : Convex ℝ (univ : Set ℝ)).contractibleSpace univ_nonempty
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨L, hLc, hLe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hU isOpen_univ
    hge.continuousOn (by rintro ⟨t, -, ht⟩; exact hgne t ht)
  refine ⟨fun t => (L t).im, ?_, fun t ht => ?_⟩
  · exact Complex.continuous_im.comp_continuousOn (hLc.mono (subset_univ _))
  · obtain ⟨r, hr, hfr⟩ := hfg t ht
    have hexp : exp (L t) = g t := by
      have := hLe (mem_univ t)
      simp only [Function.comp_apply] at this
      rw [this, hgeq t (Ioo_subset_Icc_self ht)]
    have hsplit : exp (L t) = (Real.exp (L t).re : ℂ) * exp (((L t).im : ℂ) * I) := by
      conv_lhs => rw [← Complex.re_add_im (L t)]
      rw [Complex.exp_add, Complex.ofReal_exp]
    have hnorm : ‖f t‖ = r * Real.exp (L t).re := by
      rw [hfr, norm_mul, ← hexp, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg hr.le]
    simp only
    rw [hnorm, hfr, ← hexp, hsplit]
    push_cast
    ring

/-- Angle functions add under products. -/
theorem b2_angleFn_mul {f g : ℝ → ℂ} {a b : ℝ} {θ₁ θ₂ : ℝ → ℝ} (h₁ : b2_IsAngleFn f a b θ₁)
    (h₂ : b2_IsAngleFn g a b θ₂) : b2_IsAngleFn (fun t => f t * g t) a b (fun t => θ₁ t + θ₂ t) := by
  refine ⟨h₁.1.add h₂.1, fun t ht => ?_⟩
  calc f t * g t = ((‖f t‖ : ℂ) * exp ((θ₁ t : ℂ) * I)) * ((‖g t‖ : ℂ) * exp ((θ₂ t : ℂ) * I)) :=
        congrArg₂ (· * ·) (h₁.2 t ht) (h₂.2 t ht)
    _ = (‖f t * g t‖ : ℂ) * exp (((θ₁ t + θ₂ t : ℝ) : ℂ) * I) := by
        rw [norm_mul]; push_cast; rw [add_mul, Complex.exp_add]; ring

/-- Negation adds `π` to an angle function. -/
theorem b2_angleFn_neg {f : ℝ → ℂ} {a b : ℝ} {θ : ℝ → ℝ} (h : b2_IsAngleFn f a b θ) :
    b2_IsAngleFn (fun t => -f t) a b (fun t => θ t + π) := by
  refine ⟨h.1.add continuousOn_const, fun t ht => ?_⟩
  calc -f t = -((‖f t‖ : ℂ) * exp ((θ t : ℂ) * I)) := by rw [← h.2 t ht]
    _ = (‖-f t‖ : ℂ) * exp (((θ t + π : ℝ) : ℂ) * I) := by
        rw [norm_neg]; push_cast; rw [add_mul, Complex.exp_add, Complex.exp_pi_mul_I]; ring

/-- Angle functions multiply under natural powers. -/
theorem b2_angleFn_pow {f : ℝ → ℂ} {a b : ℝ} {θ : ℝ → ℝ} (h : b2_IsAngleFn f a b θ) (m : ℕ) :
    b2_IsAngleFn (fun t => f t ^ m) a b (fun t => (m : ℝ) * θ t) := by
  refine ⟨continuousOn_const.mul h.1, fun t ht => ?_⟩
  calc f t ^ m = ((‖f t‖ : ℂ) * exp ((θ t : ℂ) * I)) ^ m := by rw [← h.2 t ht]
    _ = (‖f t ^ m‖ : ℂ) * exp ((((m : ℝ) * θ t : ℝ) : ℂ) * I) := by
        rw [mul_pow, norm_pow, ← Complex.exp_nat_mul]; push_cast; ring_nf

/-- Angle functions add under finite products. -/
theorem b2_angleFn_prod {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ} {a b : ℝ} {θ : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, b2_IsAngleFn (f i) a b (θ i)) :
    b2_IsAngleFn (fun t => ∏ i ∈ s, f i t) a b (fun t => ∑ i ∈ s, θ i t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, fun t _ => ?_⟩
    · simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc a b))
    · simp
  | insert i s hi ih =>
    have h' := b2_angleFn_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hi, Finset.sum_insert hi] using h'

/-- `Im G` is an angle function of `exp G`, when it is continuous. -/
theorem b2_angleFn_exp {G : ℝ → ℂ} {a b : ℝ} (hG : ContinuousOn (fun t => (G t).im) (Icc a b)) :
    b2_IsAngleFn (fun t => exp (G t)) a b (fun t => (G t).im) := by
  refine ⟨hG, fun t _ => ?_⟩
  simp only
  rw [Complex.norm_exp]
  conv_lhs => rw [← Complex.re_add_im (G t)]
  rw [Complex.exp_add, Complex.ofReal_exp]

/-- The principal argument is an angle function of a continuous function with values in the
slit plane. -/
theorem b2_angleFn_arg {f : ℝ → ℂ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hslit : ∀ t ∈ Icc a b, f t ∈ slitPlane) : b2_IsAngleFn f a b (fun t => arg (f t)) := by
  refine ⟨?_, fun t _ => (Complex.norm_mul_exp_arg_mul_I (f t)).symm⟩
  exact ContinuousOn.comp (g := arg) (fun z hz => (Complex.continuousAt_arg hz).continuousWithinAt)
    hf (fun t ht => hslit t ht)

/-- Angle functions restrict to sub-intervals. -/
theorem b2_angleFn_mono {f : ℝ → ℂ} {a b a' b' : ℝ} {θ : ℝ → ℝ} (h : b2_IsAngleFn f a b θ)
    (ha : a ≤ a') (hb : b' ≤ b) : b2_IsAngleFn f a' b' θ := by
  exact ⟨h.1.mono (Icc_subset_Icc ha hb),
    fun t ht => h.2 t ⟨lt_of_le_of_lt ha ht.1, lt_of_lt_of_le ht.2 hb⟩⟩

/-! ## Per-side existence of the angle functions used by S25 -/

/-- The tangent `c_j'` of a side of a corner loop has an angle function on `[0, 1]`. -/
theorem b2_exists_angleFn_tangent {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    (j : Fin n) : ∃ θ, b2_IsAngleFn (deriv (c j)) 0 1 θ := by
  obtain ⟨hC, hd, -⟩ := hc
  refine b2_exists_angleFn zero_le_one
    ((hC j).continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl) (hd j)
    (fun t ht => ⟨1, one_pos, ?_⟩)
  rw [Complex.ofReal_one, one_mul, derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]

/-- For a point `p` off the loop, `c_j - p` has an angle function on `[0, 1]`. -/
theorem b2_exists_angleFn_off {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    {p : ℂ} (hp : p ∉ ⋃ j, c j '' Icc 0 1) (j : Fin n) :
    ∃ θ, b2_IsAngleFn (fun t => c j t - p) 0 1 θ := by
  obtain ⟨hC, -⟩ := hc
  exact b2_exists_angleFn zero_le_one ((hC j).continuousOn.sub continuousOn_const)
    (fun t ht h => hp (mem_iUnion.2 ⟨j, t, ht, sub_eq_zero.1 h⟩))
    (fun t _ => ⟨1, one_pos, by simp⟩)

/-- An angle function satisfies its defining equation also at the end points, when `f` is
continuous on the closed interval. -/
theorem b2_angleFn_eq_Icc {f : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    {θ : ℝ → ℝ} (h : b2_IsAngleFn f a b θ) :
    ∀ t ∈ Icc a b, f t = (‖f t‖ : ℂ) * exp ((θ t : ℂ) * I) := by
  have hc : ContinuousOn (fun t => (‖f t‖ : ℂ) * exp ((θ t : ℂ) * I)) (Icc a b) :=
    (Complex.continuous_ofReal.comp_continuousOn hf.norm).mul
      (Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn h.1).mul continuousOn_const))
  exact EqOn.of_subset_closure h.2 hf hc Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])

/-- Angle functions only see the open interval. -/
theorem b2_angleFn_congr {f g : ℝ → ℂ} {a b : ℝ} {θ : ℝ → ℝ} (h : b2_IsAngleFn f a b θ)
    (hfg : ∀ t ∈ Ioo a b, f t = g t) : b2_IsAngleFn g a b θ :=
  ⟨h.1, fun t ht => by rw [← hfg t ht]; exact h.2 t ht⟩

/-- Two angle functions on adjacent intervals glue to one, when `f` is continuous and non-zero at
the common end point. -/
theorem b2_angleFn_glue {f : ℝ → ℂ} {a m b : ℝ} (ham : a < m) (hmb : m < b)
    (hf : ContinuousOn f (Icc a b)) (hm : f m ≠ 0) {θ₁ θ₂ : ℝ → ℝ}
    (h₁ : b2_IsAngleFn f a m θ₁) (h₂ : b2_IsAngleFn f m b θ₂) : ∃ θ, b2_IsAngleFn f a b θ := by
  have e₁ := b2_angleFn_eq_Icc ham (hf.mono (Icc_subset_Icc le_rfl hmb.le)) h₁ m ⟨ham.le, le_rfl⟩
  have e₂ := b2_angleFn_eq_Icc hmb (hf.mono (Icc_subset_Icc ham.le le_rfl)) h₂ m ⟨le_rfl, hmb.le⟩
  have hn : (‖f m‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hm
  have he : exp ((θ₁ m : ℂ) * I) = exp ((θ₂ m : ℂ) * I) := mul_left_cancel₀ hn (e₁.symm.trans e₂)
  have hed : ∀ x : ℝ, exp (((x + (θ₁ m - θ₂ m) : ℝ) : ℂ) * I) =
      exp ((x : ℂ) * I) * exp ((θ₁ m : ℂ) * I) / exp ((θ₂ m : ℂ) * I) := by
    intro x
    push_cast
    rw [add_mul, sub_mul, Complex.exp_add, Complex.exp_sub]
    ring
  refine ⟨fun t => if t ≤ m then θ₁ t else θ₂ t + (θ₁ m - θ₂ m), ?_, fun t ht => ?_⟩
  · rw [← Icc_union_Icc_eq_Icc ham.le hmb.le]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · refine h₁.1.congr fun t ht => ?_
      simp [ht.2]
    · refine (h₂.1.add (continuousOn_const (c := θ₁ m - θ₂ m))).congr fun t ht => ?_
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h]
        simp
      · simp [not_le.2 h]
  · simp only
    split_ifs with htm
    · rcases eq_or_lt_of_le htm with h | h
      · rw [h]
        exact e₁
      · exact h₁.2 t ⟨ht.1, h⟩
    · rw [hed, he, mul_div_assoc, div_self (Complex.exp_ne_zero _), mul_one]
      exact h₂.2 t ⟨not_le.1 htm, ht.2⟩

/-- Angle functions through the difference quotient at a left end point where `f` vanishes with
non-zero one-sided derivative. -/
theorem b2_exists_angleFn_left {f : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hf0 : ∀ t ∈ Ioc a b, f t ≠ 0) {d : ℂ} (hd : d ≠ 0) (ha : f a = 0)
    (hda : HasDerivWithinAt f d (Icc a b) a) : ∃ θ, b2_IsAngleFn f a b θ := by
  classical
  set g : ℝ → ℂ := fun t => if t = a then d else f t / ((t - a : ℝ) : ℂ) with hg
  have hga : g a = d := by simp [hg]
  have hgt : ∀ t, t ≠ a → g t = f t / ((t - a : ℝ) : ℂ) := fun t ht => by simp [hg, ht]
  refine b2_exists_angleFn hab.le (g := g) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
  · rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, ← continuousWithinAt_sdiff_self, ContinuousWithinAt, hga]
      refine (hasDerivWithinAt_iff_tendsto_slope.1 hda).congr' ?_
      refine eventually_nhdsWithin_of_forall fun x hx => ?_
      rw [hgt x hx.2, slope_def_module, ha, sub_zero, Complex.real_smul, div_eq_inv_mul]
      push_cast
      rfl
    · have hF : ContinuousWithinAt (fun t => f t / ((t - a : ℝ) : ℂ)) (Icc a b) t :=
        (hf t ht).div (Complex.continuous_ofReal.comp (continuous_id.sub continuous_const)).continuousWithinAt
          (Complex.ofReal_ne_zero.2 (sub_ne_zero.2 h.ne'))
      refine hF.congr_of_eventuallyEq ?_ (hgt t h.ne')
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds h.ne')] with x hx
      exact hgt x hx
  · rcases eq_or_lt_of_le ht.1 with h | h
    · rw [← h, hga]
      exact hd
    · rw [hgt t h.ne']
      exact div_ne_zero (hf0 t ⟨h, ht.2⟩) (Complex.ofReal_ne_zero.2 (sub_ne_zero.2 h.ne'))
  · refine ⟨t - a, sub_pos.2 ht.1, ?_⟩
    rw [hgt t ht.1.ne', mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 (sub_ne_zero.2 ht.1.ne'))]

/-- Angle functions through the difference quotient at a right end point where `f` vanishes with
non-zero one-sided derivative. -/
theorem b2_exists_angleFn_right {f : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hf0 : ∀ t ∈ Ico a b, f t ≠ 0) {d : ℂ} (hd : d ≠ 0) (hb : f b = 0)
    (hdb : HasDerivWithinAt f d (Icc a b) b) : ∃ θ, b2_IsAngleFn f a b θ := by
  classical
  set g : ℝ → ℂ := fun t => if t = b then -d else f t / ((b - t : ℝ) : ℂ) with hg
  have hgb : g b = -d := by simp [hg]
  have hgt : ∀ t, t ≠ b → g t = f t / ((b - t : ℝ) : ℂ) := fun t ht => by simp [hg, ht]
  refine b2_exists_angleFn hab.le (g := g) (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
  · rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h, ← continuousWithinAt_sdiff_self, ContinuousWithinAt, hgb]
      refine (hasDerivWithinAt_iff_tendsto_slope.1 hdb).neg.congr' ?_
      refine eventually_nhdsWithin_of_forall fun x hx => ?_
      rw [hgt x hx.2]
      simp only
      rw [slope_def_module, hb, sub_zero, Complex.real_smul]
      have hx0 : ((x - b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (sub_ne_zero.2 hx.2)
      have hx1 : ((b - x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (sub_ne_zero.2 (Ne.symm hx.2))
      push_cast at hx0 hx1 ⊢
      field_simp
      ring
    · have hF : ContinuousWithinAt (fun t => f t / ((b - t : ℝ) : ℂ)) (Icc a b) t :=
        (hf t ht).div (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id)).continuousWithinAt
          (Complex.ofReal_ne_zero.2 (sub_ne_zero.2 h.ne'))
      refine hF.congr_of_eventuallyEq ?_ (hgt t h.ne)
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_ne_nhds h.ne)] with x hx
      exact hgt x hx
  · rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h, hgb]
      exact neg_ne_zero.2 hd
    · rw [hgt t h.ne]
      exact div_ne_zero (hf0 t ⟨ht.1, h⟩) (Complex.ofReal_ne_zero.2 (sub_ne_zero.2 h.ne'))
  · refine ⟨b - t, sub_pos.2 ht.2, ?_⟩
    rw [hgt t ht.2.ne, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 (sub_ne_zero.2 ht.2.ne'))]

/-- Angle functions exist for `f` continuous on `[a, b]` and non-zero on `(a, b)`, when at each
end point `f` is either non-zero or vanishes with non-zero one-sided derivative. -/
theorem b2_exists_angleFn_ends {f : ℝ → ℂ} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hf0 : ∀ t ∈ Ioo a b, f t ≠ 0)
    (ha : f a ≠ 0 ∨ ∃ d, d ≠ 0 ∧ f a = 0 ∧ HasDerivWithinAt f d (Icc a b) a)
    (hb : f b ≠ 0 ∨ ∃ d, d ≠ 0 ∧ f b = 0 ∧ HasDerivWithinAt f d (Icc a b) b) :
    ∃ θ, b2_IsAngleFn f a b θ := by
  have ham : a < (a + b) / 2 := by linarith
  have hmb : (a + b) / 2 < b := by linarith
  have hsub₁ : Icc a ((a + b) / 2) ⊆ Icc a b := Icc_subset_Icc le_rfl hmb.le
  have hsub₂ : Icc ((a + b) / 2) b ⊆ Icc a b := Icc_subset_Icc ham.le le_rfl
  have h₁ : ∃ θ, b2_IsAngleFn f a ((a + b) / 2) θ := by
    rcases ha with ha | ⟨d, hd, ha, hda⟩
    · refine b2_exists_angleFn ham.le (hf.mono hsub₁) (fun t ht => ?_)
        (fun t _ => ⟨1, one_pos, by simp⟩)
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h]
        exact ha
      · exact hf0 t ⟨h, lt_of_le_of_lt ht.2 hmb⟩
    · exact b2_exists_angleFn_left ham (hf.mono hsub₁)
        (fun t ht => hf0 t ⟨ht.1, lt_of_le_of_lt ht.2 hmb⟩) hd ha (hda.mono hsub₁)
  have h₂ : ∃ θ, b2_IsAngleFn f ((a + b) / 2) b θ := by
    rcases hb with hb | ⟨d, hd, hb, hdb⟩
    · refine b2_exists_angleFn hmb.le (hf.mono hsub₂) (fun t ht => ?_)
        (fun t _ => ⟨1, one_pos, by simp⟩)
      rcases eq_or_lt_of_le ht.2 with h | h
      · rw [h]
        exact hb
      · exact hf0 t ⟨lt_of_lt_of_le ham ht.1, h⟩
    · exact b2_exists_angleFn_right hmb (hf.mono hsub₂)
        (fun t ht => hf0 t ⟨lt_of_lt_of_le ham ht.1, ht.2⟩) hd hb (hdb.mono hsub₂)
  obtain ⟨θ₁, h₁⟩ := h₁
  obtain ⟨θ₂, h₂⟩ := h₂
  exact b2_angleFn_glue ham hmb hf (hf0 _ ⟨ham, hmb⟩) h₁ h₂

/-- No integer multiple of `n > 0` lies strictly between `0` and `n`. -/
theorem b2_int_mul_not_mem_Ioo {n : ℕ} [NeZero n] (k : ℤ) (h1 : 0 < (k : ℝ) * n)
    (h2 : (k : ℝ) * n < n) : False := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hk0 : (0 : ℝ) < k := pos_of_mul_pos_left h1 hn.le
  have hk1 : (k : ℝ) < 1 := by nlinarith
  have hk0' : (0 : ℤ) < k := by exact_mod_cast hk0
  have hk1' : k < (1 : ℤ) := by exact_mod_cast hk1
  omega

/-- For a vertex `c k 0`, `c_j - c k 0` has an angle function on `[0, 1]` (for the two sides
adjacent to the vertex, through the one-sided difference quotients). -/
theorem b2_exists_angleFn_vertex {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    (k j : Fin n) : ∃ θ, b2_IsAngleFn (fun t => c j t - c k 0) 0 1 θ := by
  obtain ⟨hC, hd, hcl, hs, -⟩ := hc
  have hdiff : ∀ i : Fin n, ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (c i) (derivWithin (c i) (Icc 0 1) t) (Icc 0 1) t :=
    fun i t ht => (((hC i).differentiableOn one_ne_zero) t ht).hasDerivWithinAt
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hz : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, zero_lt_one⟩
  refine b2_exists_angleFn_ends zero_lt_one ((hC j).continuousOn.sub continuousOn_const)
    (fun t ht h => ?_) ?_ ?_
  · exact ht.1.ne' (hs j k t ⟨ht.1.le, ht.2⟩ 0 hz (sub_eq_zero.1 h)).2
  · by_cases hjk : j = k
    · subst hjk
      exact Or.inr ⟨_, hd j 0 h0, sub_self _, (hdiff j 0 h0).sub_const _⟩
    · exact Or.inl fun h => hjk (hs j k 0 hz 0 hz (sub_eq_zero.1 h)).1
  · by_cases hjk : j + 1 = k
    · subst hjk
      exact Or.inr ⟨_, hd j 1 h1, by simp only [hcl j, sub_self], (hdiff j 1 h1).sub_const _⟩
    · refine Or.inl fun h => hjk ?_
      simp only [hcl j] at h
      exact (hs _ _ 0 hz 0 hz (sub_eq_zero.1 h)).1

/-! ## The glued loop -/

section Loop

open Fin.CommRing

/-- The corner loop glued into one `n`-periodic curve: `b2_loop c (j + t) = c j t` for `j ∈ ℤ`
(read modulo `n`) and `t ∈ [0, 1)`. -/
def b2_loop {n : ℕ} [NeZero n] (c : Fin n → ℝ → ℂ) (t : ℝ) : ℂ :=
  c ((⌊t⌋ : ℤ) : Fin n) (Int.fract t)

/-- The right tangent of the glued loop at `x`: the derivative of the side through `[⌊x⌋, ⌊x⌋ + 1]`
(one-sided at an integer `x`, where it is the outgoing direction `u`). -/
def b2_tanR {n : ℕ} [NeZero n] (c : Fin n → ℝ → ℂ) (x : ℝ) : ℂ :=
  derivWithin (c ((⌊x⌋ : ℤ) : Fin n)) (Icc 0 1) (Int.fract x)

/-- The left tangent of the glued loop at `x`: the derivative of the side through `[⌈x⌉ - 1, ⌈x⌉]`
(one-sided at an integer `x`, where it is the incoming direction `v`). -/
def b2_tanL {n : ℕ} [NeZero n] (c : Fin n → ℝ → ℂ) (x : ℝ) : ℂ :=
  derivWithin (c ((⌈x⌉ - 1 : ℤ) : Fin n)) (Icc 0 1) (x - ((⌈x⌉ - 1 : ℤ) : ℝ))

/-- The glued loop is `n`-periodic. -/
theorem b2_loop_periodic {n : ℕ} [NeZero n] (c : Fin n → ℝ → ℂ) :
    Function.Periodic (b2_loop c) n := by
  intro t
  simp only [b2_loop]
  rw [Int.floor_add_natCast, Int.fract_add_natCast]
  push_cast
  simp

/-- On `[j, j + 1]` the glued loop is side `j` (also at `t = 1`, by the closing condition). -/
theorem b2_loop_apply {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) (j : ℤ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : b2_loop c (j + t) = c (j : Fin n) t := by
  obtain ⟨-, -, hcl, -⟩ := hc
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst h1
    simp only [b2_loop]
    rw [show ((j : ℝ) + 1) = ((j + 1 : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast,
      Int.fract_intCast, Int.cast_add, Int.cast_one]
    exact (hcl (j : Fin n)).symm
  · simp only [b2_loop]
    rw [Int.floor_intCast_add, Int.fract_intCast_add, Int.floor_eq_zero_iff.2 ⟨ht.1, h1⟩, add_zero,
      Int.fract_eq_self.2 ⟨ht.1, h1⟩]

/-- Two integers with the same image in `Fin n` are congruent modulo `n`. -/
theorem b2_intCast_fin_eq {n : ℕ} [NeZero n] {a b : ℤ} (h : (a : Fin n) = (b : Fin n)) :
    (n : ℤ) ∣ b - a := by
  have h2 := congrArg Fin.val h
  rw [Fin.val_intCast, Fin.val_intCast] at h2
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have h3 : a % n = b % n := by
    have := Int.emod_nonneg a hn.ne'
    have := Int.emod_nonneg b hn.ne'
    omega
  exact Int.ModEq.dvd h3

/-- On `[j, j + 1]` the glued loop is side `j`, reparametrized. -/
theorem b2_loop_eq_piece {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) (j : ℤ)
    {t : ℝ} (ht : t ∈ Icc (j : ℝ) (j + 1)) : b2_loop c t = c (j : Fin n) (t - j) := by
  have h := b2_loop_apply hc j (t := t - j) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rwa [show (j : ℝ) + (t - j) = t by ring] at h

/-- On `[j, j + 1]` the glued loop has the derivative of side `j` (one-sided at the ends). -/
theorem b2_loop_hasDerivWithinAt_piece {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ}
    (hc : b2_IsCornerLoop c) (j : ℤ) {x : ℝ} (hx : x ∈ Icc (j : ℝ) (j + 1)) :
    HasDerivWithinAt (b2_loop c) (derivWithin (c (j : Fin n)) (Icc 0 1) (x - j))
      (Icc (j : ℝ) (j + 1)) x := by
  have hmaps : MapsTo (fun t : ℝ => t - j) (Icc (j : ℝ) (j + 1)) (Icc 0 1) :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hD : HasDerivWithinAt (c (j : Fin n)) (derivWithin (c (j : Fin n)) (Icc 0 1) (x - j))
      (Icc 0 1) (x - j) :=
    (((hc.1 _).differentiableOn one_ne_zero) _ (hmaps hx)).hasDerivWithinAt
  have hsub : HasDerivWithinAt (fun t : ℝ => t - j) 1 (Icc (j : ℝ) (j + 1)) x :=
    (hasDerivWithinAt_id x _).sub_const _
  have h := hD.scomp x hsub hmaps
  rw [one_smul] at h
  exact h.congr (fun t ht => b2_loop_eq_piece hc j ht) (b2_loop_eq_piece hc j hx)

/-- The right derivative of the glued loop is the right tangent. -/
theorem b2_loop_hasDerivWithinAt_right {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ}
    (hc : b2_IsCornerLoop c) (x : ℝ) : HasDerivWithinAt (b2_loop c) (b2_tanR c x) (Ici x) x := by
  have hx : x ∈ Icc ((⌊x⌋ : ℤ) : ℝ) (⌊x⌋ + 1) := ⟨Int.floor_le x, (Int.lt_floor_add_one x).le⟩
  have h := b2_loop_hasDerivWithinAt_piece hc ⌊x⌋ hx
  refine h.mono_of_mem_nhdsWithin ?_
  exact mem_of_superset (Icc_mem_nhdsGE (Int.lt_floor_add_one x))
    (Icc_subset_Icc (Int.floor_le x) le_rfl)

/-- The left derivative of the glued loop is the left tangent. -/
theorem b2_loop_hasDerivWithinAt_left {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ}
    (hc : b2_IsCornerLoop c) (x : ℝ) : HasDerivWithinAt (b2_loop c) (b2_tanL c x) (Iic x) x := by
  have h1 : (((⌈x⌉ - 1 : ℤ)) : ℝ) < x := by
    push_cast
    linarith [Int.ceil_lt_add_one x]
  have h2 : x ≤ (((⌈x⌉ - 1 : ℤ)) : ℝ) + 1 := by
    push_cast
    linarith [Int.le_ceil x]
  have h := b2_loop_hasDerivWithinAt_piece hc (⌈x⌉ - 1) ⟨h1.le, h2⟩
  refine h.mono_of_mem_nhdsWithin ?_
  exact mem_of_superset (Icc_mem_nhdsLE h1) (Icc_subset_Icc le_rfl h2)

/-- Uniform chord estimate on the pieces, with the reference parameter `r` anywhere in the piece
within `η` of the chord. -/
theorem b2_chord_uniform_aux {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ η > 0, ∀ (j : ℤ) (s r t : ℝ), (j : ℝ) ≤ s → s ≤ t → t ≤ j + 1 → (j : ℝ) ≤ r → r ≤ j + 1 →
      t - r ≤ η → r - s ≤ η →
      ‖b2_loop c t - b2_loop c s - ((t - s : ℝ) : ℂ) * derivWithin (c (j : Fin n)) (Icc 0 1) (r - j)‖
        ≤ κ * (t - s) := by
  have huc : ∀ i : Fin n, ∃ δ > 0, ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, dist x y < δ →
      dist (derivWithin (c i) (Icc 0 1) x) (derivWithin (c i) (Icc 0 1) y) < κ := fun i =>
    Metric.uniformContinuousOn_iff.1 (isCompact_Icc.uniformContinuousOn_of_continuous
      ((hc.1 i).continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl)) κ hκ
  choose δ hδ hδc using huc
  have hinf : 0 < Finset.univ.inf' Finset.univ_nonempty δ :=
    (Finset.lt_inf'_iff _).2 fun i _ => hδ i
  refine ⟨Finset.univ.inf' Finset.univ_nonempty δ / 2, half_pos hinf,
    fun j s r t hjs hst htj hjr hrj htr hrs => ?_⟩
  have hηi : Finset.univ.inf' Finset.univ_nonempty δ / 2 < δ (j : Fin n) := by
    have := Finset.inf'_le δ (Finset.mem_univ (j : Fin n))
    linarith
  have hsub : Icc (s - j) (t - j) ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc (by linarith) (by linarith)
  have hder : ∀ x ∈ Icc (s - j) (t - j), HasDerivWithinAt
      (fun y => c (j : Fin n) y - y • derivWithin (c (j : Fin n)) (Icc 0 1) (r - j))
      (derivWithin (c (j : Fin n)) (Icc 0 1) x - derivWithin (c (j : Fin n)) (Icc 0 1) (r - j))
      (Icc (s - j) (t - j)) x := by
    intro x hx
    have h1 := (((hc.1 (j : Fin n)).differentiableOn one_ne_zero) x
      (hsub hx)).hasDerivWithinAt.mono hsub
    have h2 := (hasDerivWithinAt_id x (Icc (s - j) (t - j))).smul_const
      (derivWithin (c (j : Fin n)) (Icc 0 1) (r - j))
    rw [one_smul] at h2
    exact h1.sub h2
  have hbound : ∀ x ∈ Icc (s - j) (t - j),
      ‖derivWithin (c (j : Fin n)) (Icc 0 1) x - derivWithin (c (j : Fin n)) (Icc 0 1) (r - j)‖
        ≤ κ := by
    intro x hx
    have h := hδc (j : Fin n) x (hsub hx) (r - j) ⟨by linarith, by linarith⟩
      (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2])
    rw [dist_eq_norm] at h
    exact h.le
  have h := (convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound
    ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩
  rw [b2_loop_eq_piece hc j ⟨hjs.trans hst, htj⟩, b2_loop_eq_piece hc j ⟨hjs, hst.trans htj⟩]
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith), Complex.real_smul, Complex.real_smul] at h
  convert h using 2
  · push_cast
    ring
  · ring

/-- The glued loop is continuous. -/
theorem b2_loop_continuous {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) :
    Continuous (b2_loop c) := by
  refine continuous_iff_continuousAt.2 fun x => continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
  · exact (b2_loop_hasDerivWithinAt_left hc x).continuousWithinAt
  · exact (b2_loop_hasDerivWithinAt_right hc x).continuousWithinAt

/-- The glued loop is simple: it takes the same value exactly at parameters congruent mod `n`. -/
theorem b2_loop_eq_iff {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) {s t : ℝ} :
    b2_loop c s = b2_loop c t ↔ ∃ k : ℤ, t = s + k * n := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := hc.2.2.2.1 _ _ _ ⟨Int.fract_nonneg s, Int.fract_lt_one s⟩ _
      ⟨Int.fract_nonneg t, Int.fract_lt_one t⟩ h
    obtain ⟨k, hk⟩ := b2_intCast_fin_eq h1
    refine ⟨k, ?_⟩
    have hk' : ((⌊t⌋ : ℤ) : ℝ) = ⌊s⌋ + k * n := by
      have h3 : ((⌊t⌋ - ⌊s⌋ : ℤ) : ℝ) = ((n * k : ℤ) : ℝ) := by rw [hk]
      push_cast at h3
      linarith
    have ht := Int.floor_add_fract t
    have hs := Int.floor_add_fract s
    linarith
  · rintro ⟨k, rfl⟩
    exact ((b2_loop_periodic c).int_mul k s).symm

/-- The trace of the glued loop is the union of the sides. -/
theorem b2_loop_range {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) :
    range (b2_loop c) = ⋃ j, c j '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact mem_iUnion.2 ⟨_, Int.fract t, ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩, rfl⟩
  · intro hz
    obtain ⟨j, τ, hτ, rfl⟩ := mem_iUnion.1 hz
    refine ⟨(((j : ℕ) : ℤ) : ℝ) + τ, ?_⟩
    rw [b2_loop_apply hc _ hτ]
    simp

/-- The right tangent at an integer is the outgoing direction of side `j`. -/
theorem b2_tanR_int {n : ℕ} [NeZero n] (c : Fin n → ℝ → ℂ) (j : ℤ) :
    b2_tanR c j = derivWithin (c (j : Fin n)) (Icc 0 1) 0 := by
  simp [b2_tanR]

/-- The left tangent at an integer is the incoming direction of side `j - 1`. -/
theorem b2_tanL_int {n : ℕ} [NeZero n] (c : Fin n → ℝ → ℂ) (j : ℤ) :
    b2_tanL c j = derivWithin (c ((j : Fin n) - 1)) (Icc 0 1) 1 := by
  simp [b2_tanL]

/-- Off the integers the two tangents agree and are the derivative of the side. -/
theorem b2_tan_of_fract_ne_zero {n : ℕ} [NeZero n] (c : Fin n → ℝ → ℂ) {x : ℝ}
    (hx : Int.fract x ≠ 0) :
    b2_tanL c x = b2_tanR c x ∧ b2_tanR c x = deriv (c ((⌊x⌋ : ℤ) : Fin n)) (Int.fract x) := by
  have hceil : ⌈x⌉ = ⌊x⌋ + 1 := by
    have h := Int.ceil_eq_add_one_sub_fract hx
    have h2 : (⌈x⌉ : ℝ) = ((⌊x⌋ + 1 : ℤ) : ℝ) := by
      rw [h, Int.fract]; push_cast; ring
    exact_mod_cast h2
  have hfr : Int.fract x ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hx),
    Int.fract_lt_one x⟩
  refine ⟨?_, ?_⟩
  · simp only [b2_tanL, b2_tanR, hceil, add_sub_cancel_right, Int.fract]
  · exact derivWithin_of_mem_nhds (Icc_mem_nhds hfr.1 hfr.2)

/-- The tangents of a corner loop do not vanish. -/
theorem b2_tan_ne_zero {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) (x : ℝ) :
    b2_tanR c x ≠ 0 ∧ b2_tanL c x ≠ 0 := by
  obtain ⟨-, hd, -⟩ := hc
  refine ⟨hd _ _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩, hd _ _ ⟨?_, ?_⟩⟩
  · have := Int.ceil_lt_add_one x
    push_cast
    linarith
  · have := Int.le_ceil x
    push_cast
    linarith

/-- `b2_tanR c x` is the right derivative of the glued loop at `x`. -/
theorem b2_hasDerivWithinAt_tanR {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    (x : ℝ) : HasDerivWithinAt (b2_loop c) (b2_tanR c x) (Ici x) x := by
  exact b2_loop_hasDerivWithinAt_right hc x

/-- `b2_tanL c x` is the left derivative of the glued loop at `x`. -/
theorem b2_hasDerivWithinAt_tanL {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    (x : ℝ) : HasDerivWithinAt (b2_loop c) (b2_tanL c x) (Iic x) x := by
  exact b2_loop_hasDerivWithinAt_left hc x

/-- Uniform chord estimate on the pieces: for `s ≤ r ≤ t` in one piece `[j, j + 1]` with
`t - s ≤ η`, the chord `Γ t - Γ s` is `(t - s)` times the tangent at `r`, up to `κ (t - s)`. -/
theorem b2_chord_uniform {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ η > 0, ∀ (j : ℤ) (s r t : ℝ), (j : ℝ) ≤ s → s ≤ r → r ≤ t → t ≤ j + 1 → t - s ≤ η →
      ‖b2_loop c t - b2_loop c s - ((t - s : ℝ) : ℂ) * derivWithin (c (j : Fin n)) (Icc 0 1) (r - j)‖
        ≤ κ * (t - s) := by
  obtain ⟨η, hη, h⟩ := b2_chord_uniform_aux hc hκ
  exact ⟨η, hη, fun j s r t hjs hsr hrt htj hts => h j s r t hjs (hsr.trans hrt) htj
    (hjs.trans hsr) (hrt.trans htj) (by linarith) (by linarith)⟩

/-- Chord estimate at a point `x₀` (a corner or not): near `x₀` the chord is the left tangent
times the time spent left of `x₀` plus the right tangent times the time spent right of `x₀`, up to
`κ (t - s)`. -/
theorem b2_chord_approx {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) (x₀ : ℝ)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ η > 0, ∀ s t : ℝ, x₀ - η ≤ s → s ≤ t → t ≤ x₀ + η →
      ‖b2_loop c t - b2_loop c s - (((min t x₀ - min s x₀ : ℝ) : ℂ) * b2_tanL c x₀ +
        ((max t x₀ - max s x₀ : ℝ) : ℂ) * b2_tanR c x₀)‖ ≤ κ * (t - s) := by
  obtain ⟨η₀, hη₀, h⟩ := b2_chord_uniform_aux hc hκ
  have hR : 0 < ((⌊x₀⌋ : ℤ) : ℝ) + 1 - x₀ := by linarith [Int.lt_floor_add_one x₀]
  have hL : 0 < x₀ - (((⌈x₀⌉ - 1 : ℤ)) : ℝ) := by
    push_cast
    linarith [Int.ceil_lt_add_one x₀]
  have hL' : x₀ ≤ (((⌈x₀⌉ - 1 : ℤ)) : ℝ) + 1 := by
    push_cast
    linarith [Int.le_ceil x₀]
  refine ⟨min η₀ (min (((⌊x₀⌋ : ℤ) : ℝ) + 1 - x₀) (x₀ - (((⌈x₀⌉ - 1 : ℤ)) : ℝ))),
    lt_min hη₀ (lt_min hR hL), fun s t hs hst ht => ?_⟩
  have hη1 := min_le_left η₀ (min (((⌊x₀⌋ : ℤ) : ℝ) + 1 - x₀) (x₀ - (((⌈x₀⌉ - 1 : ℤ)) : ℝ)))
  have hη2 := (min_le_right η₀ (min (((⌊x₀⌋ : ℤ) : ℝ) + 1 - x₀) (x₀ - (((⌈x₀⌉ - 1 : ℤ)) : ℝ)))).trans
    (min_le_left (((⌊x₀⌋ : ℤ) : ℝ) + 1 - x₀) (x₀ - (((⌈x₀⌉ - 1 : ℤ)) : ℝ)))
  have hη3 := (min_le_right η₀ (min (((⌊x₀⌋ : ℤ) : ℝ) + 1 - x₀) (x₀ - (((⌈x₀⌉ - 1 : ℤ)) : ℝ)))).trans
    (min_le_right (((⌊x₀⌋ : ℤ) : ℝ) + 1 - x₀) (x₀ - (((⌈x₀⌉ - 1 : ℤ)) : ℝ)))
  generalize min η₀ (min (((⌊x₀⌋ : ℤ) : ℝ) + 1 - x₀) (x₀ - (((⌈x₀⌉ - 1 : ℤ)) : ℝ))) = η
    at hs ht hη1 hη2 hη3
  have hsplit : ∀ u, b2_loop c (min u x₀) + b2_loop c (max u x₀) = b2_loop c u + b2_loop c x₀ := by
    intro u
    rcases le_total u x₀ with hu | hu
    · rw [min_eq_left hu, max_eq_right hu]
    · rw [min_eq_right hu, max_eq_left hu, add_comm]
  have hms : x₀ - η ≤ min s x₀ := le_min hs (by linarith)
  have hmst : min s x₀ ≤ min t x₀ := min_le_min hst le_rfl
  have hMst : max s x₀ ≤ max t x₀ := max_le_max hst le_rfl
  have hMt : max t x₀ ≤ x₀ + η := max_le ht (by linarith)
  have hleft := h (⌈x₀⌉ - 1) (min s x₀) x₀ (min t x₀) (by linarith) hmst
    ((min_le_right t x₀).trans hL') (by linarith) hL' (by linarith [min_le_right t x₀])
    (by linarith)
  have hright := h ⌊x₀⌋ (max s x₀) x₀ (max t x₀) (by linarith [le_max_right s x₀, Int.floor_le x₀])
    hMst (by linarith) (Int.floor_le x₀) (by linarith) (by linarith)
    (by linarith [le_max_right s x₀])
  have hsum : (min t x₀ - min s x₀) + (max t x₀ - max s x₀) = t - s := by
    linarith [min_add_max t x₀, min_add_max s x₀]
  calc ‖b2_loop c t - b2_loop c s - (((min t x₀ - min s x₀ : ℝ) : ℂ) * b2_tanL c x₀ +
        ((max t x₀ - max s x₀ : ℝ) : ℂ) * b2_tanR c x₀)‖
      = ‖(b2_loop c (min t x₀) - b2_loop c (min s x₀) -
          ((min t x₀ - min s x₀ : ℝ) : ℂ) * b2_tanL c x₀) +
        (b2_loop c (max t x₀) - b2_loop c (max s x₀) -
          ((max t x₀ - max s x₀ : ℝ) : ℂ) * b2_tanR c x₀)‖ := by
        congr 1
        linear_combination hsplit s - hsplit t
    _ ≤ κ * (min t x₀ - min s x₀) + κ * (max t x₀ - max s x₀) :=
        (norm_add_le _ _).trans (add_le_add hleft hright)
    _ = κ * (t - s) := by rw [← mul_add, hsum]

/-- Angle functions of `Γ - q` over one period exist, when `q` is off the loop or is the base
point `Γ x₀` (then through the one-sided difference quotients at both ends). -/
theorem b2_exists_angleFn_loop {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    (x₀ : ℝ) {q : ℂ} (hq : q = b2_loop c x₀ ∨ q ∉ range (b2_loop c)) :
    ∃ θ, b2_IsAngleFn (fun t => b2_loop c t - q) x₀ (x₀ + n) θ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hcont := b2_loop_continuous hc
  rcases hq with rfl | hq
  · refine b2_exists_angleFn_ends (by linarith) (hcont.continuousOn.sub continuousOn_const)
      (fun t ht h => ?_) ?_ ?_
    · obtain ⟨k, hk⟩ := (b2_loop_eq_iff hc).1 (sub_eq_zero.1 h)
      exact b2_int_mul_not_mem_Ioo (n := n) (-k) (by push_cast; linarith [ht.1])
        (by push_cast; linarith [ht.2])
    · exact Or.inr ⟨_, (b2_tan_ne_zero hc x₀).1, sub_self _,
        ((b2_hasDerivWithinAt_tanR hc x₀).sub_const _).mono Icc_subset_Ici_self⟩
    · refine Or.inr ⟨_, (b2_tan_ne_zero hc (x₀ + n)).2, ?_,
        ((b2_hasDerivWithinAt_tanL hc (x₀ + n)).sub_const _).mono Icc_subset_Iic_self⟩
      simp only [b2_loop_periodic c x₀, sub_self]
  · exact b2_exists_angleFn (by linarith) (hcont.continuousOn.sub continuousOn_const)
      (fun t _ h => hq ⟨t, sub_eq_zero.1 h⟩) (fun t _ => ⟨1, one_pos, by simp⟩)

/-- Per-side angle changes add up to the angle change over one period of the loop starting at
an integer `a`, for a point `q` not met on the open period `(a, a + n)`. -/
theorem b2_angle_sum_eq {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) {q : ℂ}
    (a : ℤ) (hq : ∀ t ∈ Ioo (a : ℝ) (a + n), b2_loop c t ≠ q)
    {L : Fin n → ℝ → ℝ} (hL : ∀ j, b2_IsAngleFn (fun t => c j t - q) 0 1 (L j))
    {Λ : ℝ → ℝ} (hΛ : b2_IsAngleFn (fun t => b2_loop c t - q) a (a + n) Λ) :
    ∑ j, (L j 1 - L j 0) = Λ (a + n) - Λ a := by
  have hpiece : ∀ i : ℕ, i < n →
      L ((a + i : ℤ) : Fin n) 1 - L ((a + i : ℤ) : Fin n) 0 =
        Λ (a + ((i + 1 : ℕ) : ℝ)) - Λ (a + (i : ℝ)) := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hj : (((a + i : ℤ)) : ℝ) = a + i := by push_cast; ring
    have h1 : b2_IsAngleFn (fun t => b2_loop c t - q) ((a + i : ℤ) : ℝ) ((a + i : ℤ) + 1)
        (fun t => L ((a + i : ℤ) : Fin n) (t - ((a + i : ℤ) : ℝ))) := by
      refine ⟨(hL _).1.comp (continuousOn_id.sub continuousOn_const)
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩), fun t ht => ?_⟩
      simp only
      rw [b2_loop_eq_piece hc _ (Ioo_subset_Icc_self ht)]
      exact (hL _).2 _ ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h2 : b2_IsAngleFn (fun t => b2_loop c t - q) ((a + i : ℤ) : ℝ) ((a + i : ℤ) + 1) Λ :=
      b2_angleFn_mono hΛ (by rw [hj]; linarith) (by rw [hj]; linarith)
    have h3 := b2_angleFn_change_eq (by linarith) (fun t ht => sub_ne_zero.2 (hq t
      ⟨by rw [hj] at ht; linarith [ht.1], by rw [hj] at ht; linarith [ht.2]⟩)) h1 h2
    simp only [add_sub_cancel_left, sub_self] at h3
    rw [h3, hj]
    push_cast
    ring_nf
  have hsum : ∑ j, (L j 1 - L j 0) = ∑ i : Fin n,
      (L ((a + ((i : ℕ) : ℤ) : ℤ) : Fin n) 1 - L ((a + ((i : ℕ) : ℤ) : ℤ) : Fin n) 0) := by
    refine (Equiv.sum_comp (Equiv.addLeft ((a : ℤ) : Fin n)) (fun j => L j 1 - L j 0)).symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ((a + ((i : ℕ) : ℤ) : ℤ) : Fin n) = (a : Fin n) + i := by
      push_cast
      simp
    rw [this]
    rfl
  rw [hsum, Fin.sum_univ_eq_sum_range (fun i : ℕ => L ((a + i : ℤ) : Fin n) 1 -
    L ((a + i : ℤ) : Fin n) 0) n, Finset.sum_congr rfl fun i hi => hpiece i (Finset.mem_range.1 hi),
    Finset.sum_range_sub (fun i : ℕ => Λ (a + (i : ℝ))) n]
  simp

/-! ## Winding-number basics (loop form) -/

/-- Local constancy of the angle change of `Γ - p` over one period, for `p` off the loop: points
`p'` close to `p` give the same change. -/
theorem b2_wind_near {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) {p : ℂ}
    (hp : p ∉ range (b2_loop c)) : ∃ δ > 0, ∀ p', dist p' p < δ → ∀ (x₀ : ℝ) (Λ Λ' : ℝ → ℝ),
      b2_IsAngleFn (fun t => b2_loop c t - p) x₀ (x₀ + n) Λ →
      b2_IsAngleFn (fun t => b2_loop c t - p') x₀ (x₀ + n) Λ' →
      Λ (x₀ + n) - Λ x₀ = Λ' (x₀ + n) - Λ' x₀ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hcont := b2_loop_continuous hc
  have hK : IsCompact (range (b2_loop c)) :=
    (b2_loop_periodic c).compact_of_continuous hn.ne' hcont
  obtain ⟨z₀, ⟨t₀, rfl⟩, hmin⟩ := hK.exists_isMinOn (range_nonempty _)
    (f := fun z : ℂ => ‖z - p‖) (by fun_prop)
  have hfar : ∀ t, ‖b2_loop c t₀ - p‖ ≤ ‖b2_loop c t - p‖ :=
    fun t => isMinOn_iff.1 hmin _ (mem_range_self t)
  have hδ : 0 < ‖b2_loop c t₀ - p‖ := norm_pos_iff.2 fun h => hp ⟨t₀, sub_eq_zero.1 h⟩
  refine ⟨_, hδ, fun p' hp' x₀ Λ Λ' hΛ hΛ' => ?_⟩
  rw [dist_eq_norm] at hp'
  have hne : ∀ t, b2_loop c t - p ≠ 0 := fun t => norm_pos_iff.1 (hδ.trans_le (hfar t))
  have hne' : ∀ t, b2_loop c t - p' ≠ 0 := by
    intro t h
    have h1 : b2_loop c t - p = p' - p := by linear_combination h
    have h2 := hfar t
    rw [h1] at h2
    linarith
  have hre : ∀ t, 0 < (1 - (p' - p) / (b2_loop c t - p)).re := by
    intro t
    have hsmall : ‖(p' - p) / (b2_loop c t - p)‖ < 1 := by
      rw [norm_div, div_lt_one (norm_pos_iff.2 (hne t))]
      linarith [hfar t]
    rw [sub_re, one_re]
    linarith [Complex.re_le_norm ((p' - p) / (b2_loop c t - p))]
  have hhc : ContinuousOn (fun t => 1 - (p' - p) / (b2_loop c t - p)) (Icc x₀ (x₀ + n)) :=
    (continuous_const.sub (continuous_const.div (hcont.sub continuous_const) hne)).continuousOn
  have hA := b2_angleFn_mul hΛ
    (b2_angleFn_arg hhc fun t _ => mem_slitPlane_iff.2 (Or.inl (hre t)))
  have hA' : b2_IsAngleFn (fun t => b2_loop c t - p') x₀ (x₀ + n)
      (fun t => Λ t + arg (1 - (p' - p) / (b2_loop c t - p))) := by
    refine b2_angleFn_congr hA fun t _ => ?_
    have := hne t
    field_simp
    ring
  have h := b2_angleFn_change_eq (by linarith) (fun t _ => hne' t) hΛ' hA'
  simp only [b2_loop_periodic c x₀] at h
  linarith

/-- The angle change of `Γ - p` over one period does not depend on the base point
(`p` off the loop). -/
theorem b2_wind_rebase {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) {p : ℂ}
    (hp : p ∉ range (b2_loop c)) {x₁ x₂ : ℝ} {Λ₁ Λ₂ : ℝ → ℝ}
    (h₁ : b2_IsAngleFn (fun t => b2_loop c t - p) x₁ (x₁ + n) Λ₁)
    (h₂ : b2_IsAngleFn (fun t => b2_loop c t - p) x₂ (x₂ + n) Λ₂) :
    Λ₁ (x₁ + n) - Λ₁ x₁ = Λ₂ (x₂ + n) - Λ₂ x₂ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hne : ∀ t, b2_loop c t - p ≠ 0 := fun t h => hp ⟨t, sub_eq_zero.1 h⟩
  have hcont : Continuous fun t => b2_loop c t - p :=
    (b2_loop_continuous hc).sub continuous_const
  have key : ∀ y₁ y₂ : ℝ, y₁ ≤ y₂ → ∀ Λ₁ Λ₂ : ℝ → ℝ,
      b2_IsAngleFn (fun t => b2_loop c t - p) y₁ (y₁ + n) Λ₁ →
      b2_IsAngleFn (fun t => b2_loop c t - p) y₂ (y₂ + n) Λ₂ →
      Λ₁ (y₁ + n) - Λ₁ y₁ = Λ₂ (y₂ + n) - Λ₂ y₂ := by
    intro y₁ y₂ hy Λ₁ Λ₂ h₁ h₂
    obtain ⟨Θ, hΘ⟩ := b2_exists_angleFn (f := fun t => b2_loop c t - p) (a := y₁) (b := y₂ + n)
      (by linarith)
      hcont.continuousOn (fun t _ => hne t) (fun t _ => ⟨1, one_pos, by simp⟩)
    have e₁ := b2_angleFn_change_eq (by linarith) (fun t _ => hne t) h₁
      (b2_angleFn_mono hΘ le_rfl (by linarith))
    have e₂ := b2_angleFn_change_eq (by linarith) (fun t _ => hne t) h₂
      (b2_angleFn_mono hΘ hy le_rfl)
    have hsh : b2_IsAngleFn (fun t => b2_loop c t - p) y₁ y₂ (fun t => Θ (t + n)) := by
      refine ⟨hΘ.1.comp (continuousOn_id.add continuousOn_const)
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩), fun t ht => ?_⟩
      have h := hΘ.2 (t + n) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      simp only [b2_loop_periodic c t] at h
      exact h
    have e₃ := b2_angleFn_change_eq hy (fun t _ => hne t) hsh
      (b2_angleFn_mono hΘ le_rfl (by linarith))
    linarith
  rcases le_total x₁ x₂ with h | h
  · exact key x₁ x₂ h Λ₁ Λ₂ h₁ h₂
  · exact (key x₂ x₁ h Λ₂ Λ₁ h₂ h₁).symm

/-- The angle change of `Γ - p` over one period is an integer multiple of `2π`. -/
theorem b2_wind_int {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) {p : ℂ}
    (hp : p ∉ range (b2_loop c)) {x₀ : ℝ} {Λ : ℝ → ℝ}
    (hΛ : b2_IsAngleFn (fun t => b2_loop c t - p) x₀ (x₀ + n) Λ) :
    ∃ k : ℤ, Λ (x₀ + n) - Λ x₀ = 2 * π * k := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hf : ContinuousOn (fun t => b2_loop c t - p) (Icc x₀ (x₀ + n)) :=
    ((b2_loop_continuous hc).sub continuous_const).continuousOn
  have e₀ := b2_angleFn_eq_Icc (by linarith) hf hΛ x₀ ⟨le_rfl, by linarith⟩
  have e₁ := b2_angleFn_eq_Icc (by linarith) hf hΛ (x₀ + n) ⟨by linarith, le_rfl⟩
  simp only [b2_loop_periodic c x₀] at e₀ e₁
  have hne : b2_loop c x₀ - p ≠ 0 := fun h => hp ⟨x₀, sub_eq_zero.1 h⟩
  have hn0 : (‖b2_loop c x₀ - p‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hne
  have he : exp ((Λ (x₀ + n) : ℂ) * I) = exp ((Λ x₀ : ℂ) * I) :=
    mul_left_cancel₀ hn0 (e₁.symm.trans e₀)
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  refine ⟨k, ?_⟩
  have h := congrArg Complex.im hk
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.add_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re] at h
  simp at h
  linarith

/-- The angle change of `Γ - p` over one period is constant for `p` in a preconnected set
off the loop (it is locally constant on the complement of the trace). -/
theorem b2_wind_const {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) {U : Set ℂ}
    (hU : IsPreconnected U) (hUc : Disjoint U (range (b2_loop c))) {p p' : ℂ} (hp : p ∈ U)
    (hp' : p' ∈ U) {x₀ : ℝ} {Λ Λ' : ℝ → ℝ}
    (hΛ : b2_IsAngleFn (fun t => b2_loop c t - p) x₀ (x₀ + n) Λ)
    (hΛ' : b2_IsAngleFn (fun t => b2_loop c t - p') x₀ (x₀ + n) Λ') :
    Λ (x₀ + n) - Λ x₀ = Λ' (x₀ + n) - Λ' x₀ := by
  have hU' : ∀ q ∈ U, q ∉ range (b2_loop c) := fun q hq h => hUc.le_bot ⟨hq, h⟩
  refine hU.induction₂' (fun q q' => ∀ Λ Λ' : ℝ → ℝ,
      b2_IsAngleFn (fun t => b2_loop c t - q) x₀ (x₀ + n) Λ →
      b2_IsAngleFn (fun t => b2_loop c t - q') x₀ (x₀ + n) Λ' →
      Λ (x₀ + n) - Λ x₀ = Λ' (x₀ + n) - Λ' x₀) ?_ ?_ hp hp' Λ Λ' hΛ hΛ'
  · intro q hq
    obtain ⟨δ, hδ, h⟩ := b2_wind_near hc (hU' q hq)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds q hδ)]
      with y hy
    exact ⟨fun Λ Λ' h₁ h₂ => h y hy x₀ Λ Λ' h₁ h₂, fun Λ Λ' h₁ h₂ => (h y hy x₀ Λ' Λ h₂ h₁).symm⟩
  · intro x y z _ hy _ hxy hyz Λ Λ' h₁ h₂
    obtain ⟨Θ, hΘ⟩ := b2_exists_angleFn_loop hc x₀ (Or.inr (hU' y hy))
    rw [hxy Λ Θ h₁ hΘ, hyz Θ Λ' hΘ h₂]

/-- The loop does not wind around far away points. -/
theorem b2_wind_far {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) :
    ∃ R : ℝ, ∀ p : ℂ, R < ‖p‖ → ∀ (x₀ : ℝ) (Λ : ℝ → ℝ),
      b2_IsAngleFn (fun t => b2_loop c t - p) x₀ (x₀ + n) Λ → Λ (x₀ + n) - Λ x₀ = 0 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hcont := b2_loop_continuous hc
  obtain ⟨M, hM⟩ :=
    ((b2_loop_periodic c).compact_of_continuous hn.ne' hcont).isBounded.exists_norm_le
  refine ⟨M, fun p hp x₀ Λ hΛ => ?_⟩
  have hM' : ∀ t, ‖b2_loop c t‖ ≤ M := fun t => hM _ (mem_range_self t)
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hp
    linarith [hM' 0, norm_nonneg (b2_loop c 0)]
  have hre : ∀ t, 0 < (1 - b2_loop c t / p).re := by
    intro t
    have hsmall : ‖b2_loop c t / p‖ < 1 := by
      rw [norm_div, div_lt_one (norm_pos_iff.2 hp0)]
      linarith [hM' t]
    rw [sub_re, one_re]
    linarith [Complex.re_le_norm (b2_loop c t / p)]
  have hne : ∀ t, b2_loop c t - p ≠ 0 := by
    intro t h
    have h1 := hM' t
    rw [sub_eq_zero.1 h] at h1
    linarith
  have hhc : ContinuousOn (fun t => 1 - b2_loop c t / p) (Icc x₀ (x₀ + n)) :=
    (continuous_const.sub (hcont.div_const p)).continuousOn
  have hconst : b2_IsAngleFn (fun _ => -p) x₀ (x₀ + n) (fun _ => arg (-p)) :=
    ⟨continuousOn_const, fun t _ => (Complex.norm_mul_exp_arg_mul_I (-p)).symm⟩
  have hA := b2_angleFn_mul hconst
    (b2_angleFn_arg hhc fun t _ => mem_slitPlane_iff.2 (Or.inl (hre t)))
  have hA' : b2_IsAngleFn (fun t => b2_loop c t - p) x₀ (x₀ + n)
      (fun t => arg (-p) + arg (1 - b2_loop c t / p)) := by
    refine b2_angleFn_congr hA fun t _ => ?_
    field_simp
    ring
  have h := b2_angleFn_change_eq (by linarith) (fun t _ => hne t) hΛ hA'
  simp only [b2_loop_periodic c x₀] at h
  linarith

/-- The boundary loop does not wind around points of the exterior `(closure dom)ᶜ` (connected and
unbounded, so it contains far points). -/
theorem b2_wind_loop_out {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    {dom : Set ℂ} (hD : b2_IsPosBoundary c dom) {p : ℂ} (hp : p ∉ closure dom) (x₀ : ℝ)
    {Λ : ℝ → ℝ} (hΛ : b2_IsAngleFn (fun t => b2_loop c t - p) x₀ (x₀ + n) Λ) :
    Λ (x₀ + n) - Λ x₀ = 0 := by
  obtain ⟨-, -, hdb, hext, hfr, -⟩ := hD
  have hdisj : Disjoint (closure dom)ᶜ (range (b2_loop c)) := by
    rw [b2_loop_range hc, ← hfr]
    exact disjoint_compl_left_iff_subset.2 frontier_subset_closure
  obtain ⟨R, hR⟩ := b2_wind_far hc
  obtain ⟨R', hR'⟩ := hdb.closure.subset_ball (0 : ℂ)
  set q : ℂ := ((|R| + |R'| + 1 : ℝ) : ℂ) with hqdef
  have hqn : ‖q‖ = |R| + |R'| + 1 := by
    rw [hqdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hq : q ∈ (closure dom)ᶜ := by
    intro hq
    have := hR' hq
    rw [mem_ball, dist_zero_right, hqn] at this
    linarith [le_abs_self R', abs_nonneg R]
  have hqR : q ∉ range (b2_loop c) := fun h => hdisj.le_bot ⟨hq, h⟩
  obtain ⟨Λq, hΛq⟩ := b2_exists_angleFn_loop hc x₀ (Or.inr hqR)
  rw [b2_wind_const hc hext.isPreconnected hdisj hp hq hΛ hΛq]
  exact hR q (by rw [hqn]; linarith [le_abs_self R, abs_nonneg R']) x₀ Λq hΛq

/-! ## Winding number one and the boundary winding angle (loop form) -/

/-- A constant has the constant angle function `arg`. -/
theorem b2_lc_angleFn_const (z : ℂ) (s t : ℝ) : b2_IsAngleFn (fun _ => z) s t (fun _ => arg z) :=
  ⟨continuousOn_const, fun _ _ => (Complex.norm_mul_exp_arg_mul_I z).symm⟩

/-- Half-plane lemma: if `f` is continuous on `[s, t]` with values in the open half-plane
`{z | 0 < re (z γ)}`, an angle function of `f` changes by the difference of the rotated principal
arguments `arg (f · γ)` at the ends. -/
theorem b2_lc_hp_change {f : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t) (hf : ContinuousOn f (Icc s t)) {γ : ℂ}
    (hγ : ∀ τ ∈ Icc s t, 0 < (f τ * γ).re) {θ : ℝ → ℝ} (hθ : b2_IsAngleFn f s t θ) :
    θ t - θ s = arg (f t * γ) - arg (f s * γ) := by
  have hslit : ∀ τ ∈ Icc s t, f τ * γ ∈ slitPlane := fun τ hτ =>
    Complex.mem_slitPlane_iff.2 (Or.inl (hγ τ hτ))
  have h1 := b2_angleFn_arg (f := fun τ => f τ * γ) (hf.mul continuousOn_const) hslit
  have h2 := b2_angleFn_mul hθ (b2_lc_angleFn_const γ s t)
  have hne : ∀ τ ∈ Ioo s t, f τ * γ ≠ 0 := fun τ hτ h => by
    have := hγ τ (Ioo_subset_Icc_self hτ)
    rw [h, Complex.zero_re] at this
    exact lt_irrefl _ this
  have := b2_angleFn_change_eq hst hne h2 h1
  linarith

/-- Comparison of two angle functions through a quotient in the right half-plane: if `g` does
not vanish and `f / g` has positive real part on `[s, t]`, the angle changes of `f` and `g` differ
by the change of the principal argument of `f / g`. -/
theorem b2_lc_quot_change {f g : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t) (hf : ContinuousOn f (Icc s t))
    (hg : ContinuousOn g (Icc s t)) (hg0 : ∀ τ ∈ Icc s t, g τ ≠ 0)
    (hq : ∀ τ ∈ Icc s t, 0 < (f τ / g τ).re) {θf θg : ℝ → ℝ} (hθf : b2_IsAngleFn f s t θf)
    (hθg : b2_IsAngleFn g s t θg) :
    θf t - θf s = θg t - θg s + (arg (f t / g t) - arg (f s / g s)) := by
  have hslit : ∀ τ ∈ Icc s t, f τ / g τ ∈ slitPlane := fun τ hτ =>
    Complex.mem_slitPlane_iff.2 (Or.inl (hq τ hτ))
  have h1 := b2_angleFn_arg (f := fun τ => f τ / g τ) (hf.div hg hg0) hslit
  have h2 := b2_angleFn_mul hθg h1
  have h3 : b2_IsAngleFn f s t (fun τ => θg τ + arg (f τ / g τ)) := by
    refine ⟨h2.1, fun τ hτ => ?_⟩
    have := h2.2 τ hτ
    simp only [mul_div_cancel₀ _ (hg0 τ (Ioo_subset_Icc_self hτ))] at this
    exact this
  have hfne : ∀ τ ∈ Ioo s t, f τ ≠ 0 := fun τ hτ h => by
    have := hq τ (Ioo_subset_Icc_self hτ)
    rw [h, zero_div, Complex.zero_re] at this
    exact lt_irrefl _ this
  have := b2_angleFn_change_eq hst hfne hθf h3
  linarith

/-- Near a point `P` of the right half-plane the argument is close to `arg P`, uniformly under
positive scaling: `‖w - σ P‖ < σ r` forces `0 < re w` and `|arg w - arg P| < α`. -/
theorem b2_lc_arg_near {P : ℂ} (hP : 0 < P.re) {α : ℝ} (hα : 0 < α) :
    ∃ r > 0, r ≤ P.re ∧ ∀ σ : ℝ, 0 < σ → ∀ w : ℂ, ‖w - σ * P‖ < σ * r →
      0 < w.re ∧ |arg w - arg P| < α := by
  have hc := Complex.continuousAt_arg (Complex.mem_slitPlane_iff.2 (Or.inl hP))
  obtain ⟨r₀, hr₀, H⟩ := Metric.continuousAt_iff.1 hc α hα
  refine ⟨min r₀ P.re, lt_min hr₀ hP, min_le_right _ _, fun σ hσ w hw => ?_⟩
  set z : ℂ := ((σ⁻¹ : ℝ) : ℂ) * w with hz
  have hwz : w = (σ : ℂ) * z := by
    rw [hz, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hσ.ne', Complex.ofReal_one,
      one_mul]
  have hzP : ‖z - P‖ < min r₀ P.re := by
    have e : w - σ * P = (σ : ℂ) * (z - P) := by rw [hwz]; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ.le] at hw
    exact lt_of_mul_lt_mul_left hw hσ.le
  refine ⟨?_, ?_⟩
  · rw [hwz, Complex.re_ofReal_mul]
    have h1 : P.re - z.re ≤ ‖z - P‖ := by
      have := Complex.abs_re_le_norm (z - P)
      rw [Complex.sub_re] at this
      linarith [neg_abs_le (z.re - P.re)]
    have h2 : 0 < z.re := by linarith [min_le_right r₀ P.re]
    positivity
  · rw [hwz, Complex.arg_real_mul _ hσ]
    have := H (show dist z P < r₀ from
      lt_of_lt_of_le (by rw [dist_eq_norm]; exact hzP) (min_le_left _ _))
    rwa [Real.dist_eq] at this

/-- A bound on an open interval extends, by continuity, to the closed interval. -/
theorem b2_lc_bound_closure {Λ : ℝ → ℝ} {s t : ℝ} (hst : s < t) (hΛ : ContinuousOn Λ (Icc s t))
    {C α : ℝ} (h : ∀ u ∈ Ioo s t, |Λ u - C| ≤ α) : ∀ u ∈ Icc s t, |Λ u - C| ≤ α := by
  intro u hu
  rw [← closure_Ioo hst.ne] at hu
  refine le_on_closure (f := fun u => |Λ u - C|) (g := fun _ => α) h ?_ continuousOn_const hu
  rw [closure_Ioo hst.ne]
  exact (hΛ.sub continuousOn_const).abs

/-- The glued loop does not return to its base point within one open period. -/
theorem b2_lc_loop_ne_base {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    {x₀ τ : ℝ} (hτ : τ ∈ Ioo x₀ (x₀ + n)) : b2_loop c τ ≠ b2_loop c x₀ := by
  intro h
  obtain ⟨m, hm⟩ := (b2_loop_eq_iff hc).1 h.symm
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have h1 : (0 : ℝ) < m * n := by linarith [hτ.1]
  have h2 : (m : ℝ) * n < n := by linarith [hτ.2]
  have hm0 : (0 : ℝ) < m := pos_of_mul_pos_left h1 hn.le
  have hm1 : (m : ℝ) < 1 := by nlinarith
  have hm0' : (0 : ℤ) < m := by exact_mod_cast hm0
  have hm1' : m < (1 : ℤ) := by exact_mod_cast hm1
  omega

/-- `r e^{iψ}` with `r > 0` and `|ψ| < π / 2` lies in the right half-plane and has argument `ψ`. -/
theorem b2_lc_polar_right {z : ℂ} {r ψ : ℝ} (hz : z = (r : ℂ) * exp ((ψ : ℂ) * I)) (hr : 0 < r)
    (hψ : |ψ| < π / 2) : 0 < z.re ∧ arg z = ψ := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hψ
  subst hz
  constructor
  · rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    exact mul_pos hr (Real.cos_pos_of_mem_Ioo ⟨h1, h2⟩)
  · rw [Complex.arg_real_mul _ hr, Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

/-- Product of unit complex numbers: `e^{ix} e^{iy} = e^{iz}` for `x + y = z`. -/
theorem b2_lc_exp_mul_exp {x y z : ℝ} (h : x + y = z) :
    exp ((x : ℂ) * I) * exp ((y : ℂ) * I) = exp ((z : ℂ) * I) := by
  rw [← h, ← Complex.exp_add]
  push_cast
  ring_nf

/-- Negation of a unit complex number: `-e^{ix} = e^{iy}` for `x - π = y`. -/
theorem b2_lc_neg_exp_sub {x y : ℝ} (h : x - π = y) : -exp ((x : ℂ) * I) = exp ((y : ℂ) * I) := by
  rw [← h, Complex.ofReal_sub, sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I, div_neg, div_one]

/-- Negation of a unit complex number: `-e^{ix} = e^{iy}` for `x + π = y`. -/
theorem b2_lc_neg_exp_add {x y : ℝ} (h : x + π = y) : -exp ((x : ℂ) * I) = exp ((y : ℂ) * I) := by
  rw [← h, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

/-- The incoming direction in polar form relative to the outgoing one:
`-a = |a| e^{i(arg b + (π - arg (b / a)))}`. -/
theorem b2_lc_neg_polar {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    -a = (‖a‖ : ℂ) * exp (((arg b + (π - arg (b / a)) : ℝ) : ℂ) * I) := by
  have hz : b / a ≠ 0 := div_ne_zero hb ha
  have e1 := Complex.norm_mul_exp_arg_mul_I b
  have e2 := Complex.norm_mul_exp_arg_mul_I (b / a)
  set E := exp (((arg b + (π - arg (b / a)) : ℝ) : ℂ) * I) with hE
  have key : E * exp ((arg (b / a) : ℂ) * I) = -exp ((arg b : ℂ) * I) := by
    rw [hE, b2_lc_exp_mul_exp (show arg b + (π - arg (b / a)) + arg (b / a) = arg b + π by ring),
      ← b2_lc_neg_exp_add rfl]
  have hn : (‖a‖ : ℂ) * (‖b / a‖ : ℂ) = (‖b‖ : ℂ) := by
    rw [← Complex.ofReal_mul, norm_div, mul_div_cancel₀ _ (norm_ne_zero_iff.2 ha)]
  apply mul_right_cancel₀ hz
  rw [show -a * (b / a) = -b by field_simp]
  linear_combination e1 + ((‖a‖ : ℂ) * E) * e2 - ((‖a‖ : ℂ) * (‖b / a‖ : ℂ)) * key +
    exp ((arg b : ℂ) * I) * hn

/-- The turning `tanR / tanL` of a corner loop lies in the slit plane (no cusps at the vertices;
it is `1` at the other points). -/
theorem b2_lc_tan_slit {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) (x : ℝ) :
    b2_tanR c x / b2_tanL c x ∈ slitPlane := by
  by_cases hx : Int.fract x = 0
  · obtain ⟨k, rfl⟩ : ∃ k : ℤ, x = k := ⟨⌊x⌋, by
      have := Int.floor_add_fract x
      rw [hx, add_zero] at this
      exact this.symm⟩
    rw [b2_tanR_int, b2_tanL_int]
    exact hc.2.2.2.2 _
  · obtain ⟨hLR, -⟩ := b2_tan_of_fract_ne_zero c hx
    rw [hLR, div_self (b2_tan_ne_zero hc x).1]
    exact Complex.mem_slitPlane_iff.2 (Or.inl (by simp))

/-- One-sided chord estimates at `x₀`: `Γ (x₀ + σ) ≈ Γ x₀ + σ tanR` and
`Γ (x₀ - σ) ≈ Γ x₀ - σ tanL` up to `k σ`. -/
theorem b2_lc_chord_onesided {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    (x₀ : ℝ) :
    ∀ k > 0, ∃ η > 0, ∀ σ : ℝ, 0 ≤ σ → σ ≤ η →
      ‖b2_loop c (x₀ + σ) - b2_loop c x₀ - σ * b2_tanR c x₀‖ ≤ k * σ ∧
      ‖b2_loop c (x₀ - σ) - b2_loop c x₀ + σ * b2_tanL c x₀‖ ≤ k * σ := by
  intro k hk
  obtain ⟨η, hη, H⟩ := b2_chord_approx hc x₀ hk
  refine ⟨η, hη, fun σ hσ0 hση => ⟨?_, ?_⟩⟩
  · have h := H x₀ (x₀ + σ) (by linarith) (by linarith) (by linarith)
    rw [min_eq_right (by linarith : x₀ ≤ x₀ + σ), min_self,
      max_eq_left (by linarith : x₀ ≤ x₀ + σ), max_self, sub_self, add_sub_cancel_left] at h
    simpa using h
  · have h := H (x₀ - σ) x₀ (by linarith) (by linarith) (by linarith)
    rw [min_self, min_eq_left (by linarith : x₀ - σ ≤ x₀), max_self,
      max_eq_right (by linarith : x₀ - σ ≤ x₀), sub_self, sub_sub_cancel] at h
    rw [← norm_neg]
    convert h using 2
    push_cast
    ring

/-- **Local comparison (LC)** at a point `Γ x₀` of a continuous `N`-periodic curve that does not
return to `Γ x₀` within an open period and has one-sided tangents `b` (right) and `a` (left) there.
Let `v`, `γR`, `γL` be unit vectors such that `b`, `-v` lie in the open half-plane
`{re (· γR) > 0}` and `-v`, `-a` in `{re (· γL) > 0}`.  Then for small `ε > 0` the point
`p = Γ x₀ + ε v` is off the curve, and the angle change of `Γ - p` over one period exceeds the one
of `Γ - Γ x₀` by `arg (b γR) - arg (-v γR) + arg (-v γL) - arg (-a γL)`, up to any given `κ > 0`.
(Proof: near the two ends the curve and `-ε v` stay in the half-planes, where the rotated principal
argument is an angle function; on the rest the quotient `(Γ - p) / (Γ - Γ x₀)` is close to `1`.) -/
theorem b2_lc_core {Γ : ℝ → ℂ} {N x₀ : ℝ} (hN : 0 < N) (hΓc : Continuous Γ)
    (hper : Function.Periodic Γ N) (hne : ∀ τ ∈ Ioo x₀ (x₀ + N), Γ τ ≠ Γ x₀) {a b : ℂ}
    (hch : ∀ k > 0, ∃ η > 0, ∀ σ : ℝ, 0 ≤ σ → σ ≤ η →
      ‖Γ (x₀ + σ) - Γ x₀ - σ * b‖ ≤ k * σ ∧ ‖Γ (x₀ - σ) - Γ x₀ + σ * a‖ ≤ k * σ)
    {v γR γL : ℂ} (hv : ‖v‖ = 1) (hγR : ‖γR‖ = 1) (hγL : ‖γL‖ = 1)
    (h1 : 0 < (b * γR).re) (h2 : 0 < (-v * γR).re) (h3 : 0 < (-v * γL).re)
    (h4 : 0 < (-a * γL).re)
    {Λ : ℝ → ℝ} (hΛ : b2_IsAngleFn (fun t => Γ t - Γ x₀) x₀ (x₀ + N) Λ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, Γ x₀ + ε * v ∉ range Γ ∧
      ∀ Λp : ℝ → ℝ, b2_IsAngleFn (fun t => Γ t - (Γ x₀ + ε * v)) x₀ (x₀ + N) Λp →
        |(Λp (x₀ + N) - Λp x₀) - (Λ (x₀ + N) - Λ x₀) -
          (arg (b * γR) - arg (-v * γR) + arg (-v * γL) - arg (-a * γL))| ≤ κ := by
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, Γ x₀ = z₀ := ⟨_, rfl⟩
  have hperx : Γ (x₀ + N) = z₀ := by rw [hper x₀, hz₀]
  rw [hz₀] at hch hΛ hne ⊢
  obtain ⟨α, hα⟩ : ∃ α, α = κ / 8 := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; positivity
  obtain ⟨r₁, hr₁, hr₁P, H₁⟩ := b2_lc_arg_near h1 hα0
  obtain ⟨r₄, hr₄, hr₄P, H₄⟩ := b2_lc_arg_near h4 hα0
  obtain ⟨r₇, hr₇, -, H₇⟩ := b2_lc_arg_near (P := 1) (by norm_num) hα0
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, k₀ = min r₁ r₄ / 2 := ⟨_, rfl⟩
  have hk₀0 : 0 < k₀ := by rw [hk₀]; positivity
  have hk₀1 : k₀ ≤ r₁ / 2 := by have := min_le_left r₁ r₄; rw [hk₀]; linarith
  have hk₀4 : k₀ ≤ r₄ / 2 := by have := min_le_right r₁ r₄; rw [hk₀]; linarith
  obtain ⟨η, hη, hch'⟩ := hch k₀ hk₀0
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = min η (N / 3) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min hη (by positivity)
  have hδη : δ ≤ η := by rw [hδ]; exact min_le_left _ _
  have hδN : δ ≤ N / 3 := by rw [hδ]; exact min_le_right _ _
  have hR : ∀ σ : ℝ, 0 ≤ σ → σ ≤ δ → ‖Γ (x₀ + σ) - z₀ - σ * b‖ ≤ k₀ * σ :=
    fun σ h0 h1 => (hch' σ h0 (h1.trans hδη)).1
  have hL : ∀ σ : ℝ, 0 ≤ σ → σ ≤ δ → ‖Γ (x₀ + N - σ) - z₀ + σ * a‖ ≤ k₀ * σ := by
    intro σ h0 h1
    have e : Γ (x₀ + N - σ) = Γ (x₀ - σ) := by
      rw [show x₀ + N - σ = x₀ - σ + N by ring]
      exact hper _
    rw [e]
    exact (hch' σ h0 (h1.trans hδη)).2
  have hs12 : x₀ + δ ≤ x₀ + N - δ := by linarith
  have hgc : Continuous (fun t => Γ t - z₀) := hΓc.sub continuous_const
  obtain ⟨m, hm0, hm⟩ : ∃ m > 0, ∀ τ ∈ Icc (x₀ + δ) (x₀ + N - δ), m ≤ ‖Γ τ - z₀‖ := by
    obtain ⟨τm, hτm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hs12)
      (hgc.norm.continuousOn)
    refine ⟨‖Γ τm - z₀‖, norm_pos_iff.2 (sub_ne_zero.2 (hne τm ⟨by linarith [hτm.1],
      by linarith [hτm.2]⟩)), fun τ hτ => isMinOn_iff.1 hmin τ hτ⟩
  -- the degenerate ends of `Λ`
  have W1 : ∀ σ : ℝ, 0 < σ → σ ≤ δ → 0 < ((Γ (x₀ + σ) - z₀) * γR).re ∧
      |arg ((Γ (x₀ + σ) - z₀) * γR) - arg (b * γR)| < α := by
    intro σ hσ hσδ
    refine H₁ σ hσ _ ?_
    have e : (Γ (x₀ + σ) - z₀) * γR - σ * (b * γR) = (Γ (x₀ + σ) - z₀ - σ * b) * γR := by ring
    rw [e, norm_mul, hγR, mul_one]
    calc ‖Γ (x₀ + σ) - z₀ - σ * b‖ ≤ k₀ * σ := hR σ hσ.le hσδ
      _ < σ * r₁ := by
        have := mul_lt_mul_of_pos_left (show k₀ < r₁ by linarith) hσ
        linarith
  have W3 : ∀ σ : ℝ, 0 < σ → σ ≤ δ → 0 < ((Γ (x₀ + N - σ) - z₀) * γL).re ∧
      |arg ((Γ (x₀ + N - σ) - z₀) * γL) - arg (-a * γL)| < α := by
    intro σ hσ hσδ
    refine H₄ σ hσ _ ?_
    have e : (Γ (x₀ + N - σ) - z₀) * γL - σ * (-a * γL) =
        (Γ (x₀ + N - σ) - z₀ + σ * a) * γL := by ring
    rw [e, norm_mul, hγL, mul_one]
    calc ‖Γ (x₀ + N - σ) - z₀ + σ * a‖ ≤ k₀ * σ := hL σ hσ.le hσδ
      _ < σ * r₄ := by
        have := mul_lt_mul_of_pos_left (show k₀ < r₄ by linarith) hσ
        linarith
  have E4 : |Λ x₀ - Λ (x₀ + δ)| ≤ 2 * α := by
    refine b2_lc_bound_closure (by linarith : x₀ < x₀ + δ)
      (hΛ.1.mono (Icc_subset_Icc le_rfl (by linarith))) ?_ x₀ (left_mem_Icc.2 (by linarith))
    intro u hu
    have hhp : ∀ τ ∈ Icc u (x₀ + δ), 0 < ((Γ τ - z₀) * γR).re := by
      intro τ hτ
      have := (W1 (τ - x₀) (by linarith [hu.1, hτ.1]) (by linarith [hτ.2])).1
      rwa [show x₀ + (τ - x₀) = τ by ring] at this
    have C := b2_lc_hp_change (f := fun t => Γ t - z₀) (γ := γR) hu.2.le hgc.continuousOn hhp
      (b2_angleFn_mono hΛ hu.1.le (by linarith))
    have w1 := (W1 δ hδ0 le_rfl).2
    have w2 := (W1 (u - x₀) (by linarith [hu.1]) (by linarith [hu.2])).2
    rw [show x₀ + (u - x₀) = u by ring] at w2
    obtain ⟨w1a, w1b⟩ := abs_lt.1 w1
    obtain ⟨w2a, w2b⟩ := abs_lt.1 w2
    rw [abs_le]
    constructor <;> linarith
  have E5 : |Λ (x₀ + N) - Λ (x₀ + N - δ)| ≤ 2 * α := by
    refine b2_lc_bound_closure (by linarith : x₀ + N - δ < x₀ + N)
      (hΛ.1.mono (Icc_subset_Icc (by linarith) le_rfl)) ?_ (x₀ + N)
      (right_mem_Icc.2 (by linarith))
    intro u hu
    have hhp : ∀ τ ∈ Icc (x₀ + N - δ) u, 0 < ((Γ τ - z₀) * γL).re := by
      intro τ hτ
      have := (W3 (x₀ + N - τ) (by linarith [hu.2, hτ.2]) (by linarith [hτ.1])).1
      rwa [show x₀ + N - (x₀ + N - τ) = τ by ring] at this
    have C := b2_lc_hp_change (f := fun t => Γ t - z₀) (γ := γL) hu.1.le hgc.continuousOn hhp
      (b2_angleFn_mono hΛ (by linarith) hu.2.le)
    have w1 := (W3 δ hδ0 le_rfl).2
    have w2 := (W3 (x₀ + N - u) (by linarith [hu.2]) (by linarith [hu.1])).2
    rw [show x₀ + N - (x₀ + N - u) = u by ring] at w2
    obtain ⟨w1a, w1b⟩ := abs_lt.1 w1
    obtain ⟨w2a, w2b⟩ := abs_lt.1 w2
    rw [abs_le]
    constructor <;> linarith
  -- the point `p`
  have hε₀ : 0 < min (min (δ * r₁ / 2) (δ * r₄ / 2)) (m * r₇) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
  obtain ⟨hε0, hεε₀⟩ := hε
  have hε1 : ε < δ * r₁ / 2 := lt_of_lt_of_le hεε₀ ((min_le_left _ _).trans (min_le_left _ _))
  have hε4 : ε < δ * r₄ / 2 := lt_of_lt_of_le hεε₀ ((min_le_left _ _).trans (min_le_right _ _))
  have hε7 : ε < m * r₇ := lt_of_lt_of_le hεε₀ (min_le_right _ _)
  obtain ⟨p, hp⟩ : ∃ p, z₀ + ε * v = p := ⟨_, rfl⟩
  rw [hp]
  have hnεv : ‖(ε : ℂ) * v‖ = ε := by
    rw [norm_mul, hv, mul_one, Complex.norm_real, Real.norm_of_nonneg hε0.le]
  have hfc : Continuous (fun t => Γ t - p) := hΓc.sub continuous_const
  -- (N1) near the right end, `Γ - p` lies in the half-plane of `γR`
  have N1 : ∀ τ ∈ Icc x₀ (x₀ + δ), 0 < ((Γ τ - p) * γR).re := by
    intro τ hτ
    have hσ0 : 0 ≤ τ - x₀ := by linarith [hτ.1]
    have e := hR (τ - x₀) hσ0 (by linarith [hτ.2])
    rw [show x₀ + (τ - x₀) = τ by ring] at e
    have hsplit : (Γ τ - p) * γR = (Γ τ - z₀ - ((τ - x₀ : ℝ) : ℂ) * b) * γR +
        ((τ - x₀ : ℝ) : ℂ) * (b * γR) + (ε : ℂ) * (-v * γR) := by rw [← hp]; ring
    have hre : -((Γ τ - z₀ - ((τ - x₀ : ℝ) : ℂ) * b) * γR).re ≤ k₀ * (τ - x₀) := by
      have := Complex.abs_re_le_norm ((Γ τ - z₀ - ((τ - x₀ : ℝ) : ℂ) * b) * γR)
      rw [norm_mul, hγR, mul_one] at this
      linarith [neg_abs_le ((Γ τ - z₀ - ((τ - x₀ : ℝ) : ℂ) * b) * γR).re]
    have hk := mul_le_mul_of_nonneg_left (show k₀ ≤ (b * γR).re by linarith) hσ0
    rw [hsplit, Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    linarith [mul_pos hε0 h2]
  -- (N2) near the left end, `Γ - p` lies in the half-plane of `γL`
  have N2 : ∀ τ ∈ Icc (x₀ + N - δ) (x₀ + N), 0 < ((Γ τ - p) * γL).re := by
    intro τ hτ
    have hσ0 : 0 ≤ x₀ + N - τ := by linarith [hτ.2]
    have e := hL (x₀ + N - τ) hσ0 (by linarith [hτ.1])
    rw [show x₀ + N - (x₀ + N - τ) = τ by ring] at e
    have hsplit : (Γ τ - p) * γL = (Γ τ - z₀ + ((x₀ + N - τ : ℝ) : ℂ) * a) * γL +
        ((x₀ + N - τ : ℝ) : ℂ) * (-a * γL) + (ε : ℂ) * (-v * γL) := by rw [← hp]; ring
    have hre : -((Γ τ - z₀ + ((x₀ + N - τ : ℝ) : ℂ) * a) * γL).re ≤ k₀ * (x₀ + N - τ) := by
      have := Complex.abs_re_le_norm ((Γ τ - z₀ + ((x₀ + N - τ : ℝ) : ℂ) * a) * γL)
      rw [norm_mul, hγL, mul_one] at this
      linarith [neg_abs_le ((Γ τ - z₀ + ((x₀ + N - τ : ℝ) : ℂ) * a) * γL).re]
    have hk := mul_le_mul_of_nonneg_left (show k₀ ≤ (-a * γL).re by linarith) hσ0
    rw [hsplit, Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    linarith [mul_pos hε0 h3]
  -- (N3) on the far part the quotient `(Γ - p) / (Γ - Γ x₀)` is close to `1`
  have N3 : ∀ τ ∈ Icc (x₀ + δ) (x₀ + N - δ), Γ τ - z₀ ≠ 0 ∧
      0 < ((Γ τ - p) / (Γ τ - z₀)).re ∧ |arg ((Γ τ - p) / (Γ τ - z₀)) - arg 1| < α := by
    intro τ hτ
    have hmτ := hm τ hτ
    have hg : Γ τ - z₀ ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hm0 hmτ)
    refine ⟨hg, H₇ 1 one_pos _ ?_⟩
    have e : (Γ τ - p) / (Γ τ - z₀) - ((1 : ℝ) : ℂ) * 1 = -((ε : ℂ) * v) / (Γ τ - z₀) := by
      rw [← hp, Complex.ofReal_one, mul_one, div_sub_one hg]
      congr 1
      ring
    rw [e, norm_div, norm_neg, hnεv, one_mul, div_lt_iff₀ (norm_pos_iff.2 hg)]
    linarith [mul_le_mul_of_nonneg_right hmτ hr₇.le]
  -- `p` is off the curve
  have hpR : p ∉ range Γ := by
    rintro ⟨τ, hτ⟩
    obtain ⟨y, hy, hyτ⟩ := hper.exists_mem_Ico hN τ x₀
    rw [hyτ] at hτ
    by_cases hy1 : y ≤ x₀ + δ
    · have := N1 y ⟨hy.1, hy1⟩
      rw [hτ, sub_self, zero_mul, Complex.zero_re] at this
      exact lt_irrefl _ this
    by_cases hy2 : x₀ + N - δ ≤ y
    · have := N2 y ⟨hy2, hy.2.le⟩
      rw [hτ, sub_self, zero_mul, Complex.zero_re] at this
      exact lt_irrefl _ this
    · have := (N3 y ⟨(not_le.1 hy1).le, (not_le.1 hy2).le⟩).2.1
      rw [hτ, sub_self, zero_div, Complex.zero_re] at this
      exact lt_irrefl _ this
  refine ⟨hpR, fun Λp hΛp => ?_⟩
  -- the three pieces of the change of `Λp`
  have A1 := b2_lc_hp_change (f := fun t => Γ t - p) (γ := γR) (by linarith : x₀ ≤ x₀ + δ)
    hfc.continuousOn N1 (b2_angleFn_mono hΛp le_rfl (by linarith))
  have e0R : (Γ x₀ - p) * γR = (ε : ℂ) * (-v * γR) := by rw [hz₀, ← hp]; ring
  rw [e0R, Complex.arg_real_mul _ hε0] at A1
  have B1 : |arg ((Γ (x₀ + δ) - p) * γR) - arg (b * γR)| < α := by
    refine (H₁ δ hδ0 _ ?_).2
    have e : (Γ (x₀ + δ) - p) * γR - δ * (b * γR) =
        (Γ (x₀ + δ) - z₀ - δ * b) * γR + (ε : ℂ) * (-v * γR) := by rw [← hp]; ring
    have h5 : ‖(ε : ℂ) * (-v * γR)‖ = ε := by
      rw [← mul_assoc, norm_mul, hγR, mul_one, mul_neg, norm_neg, hnεv]
    rw [e]
    calc _ ≤ ‖(Γ (x₀ + δ) - z₀ - δ * b) * γR‖ + ‖(ε : ℂ) * (-v * γR)‖ := norm_add_le _ _
      _ = ‖Γ (x₀ + δ) - z₀ - δ * b‖ + ε := by rw [norm_mul, hγR, mul_one, h5]
      _ < δ * r₁ := by
        have := hR δ hδ0.le le_rfl
        linarith [mul_le_mul_of_nonneg_right hk₀1 hδ0.le]
  have A3 := b2_lc_hp_change (f := fun t => Γ t - p) (γ := γL)
    (by linarith : x₀ + N - δ ≤ x₀ + N) hfc.continuousOn N2
    (b2_angleFn_mono hΛp (by linarith) le_rfl)
  have e0L : (Γ (x₀ + N) - p) * γL = (ε : ℂ) * (-v * γL) := by rw [hperx, ← hp]; ring
  rw [e0L, Complex.arg_real_mul _ hε0] at A3
  have B3 : |arg ((Γ (x₀ + N - δ) - p) * γL) - arg (-a * γL)| < α := by
    refine (H₄ δ hδ0 _ ?_).2
    have e : (Γ (x₀ + N - δ) - p) * γL - δ * (-a * γL) =
        (Γ (x₀ + N - δ) - z₀ + δ * a) * γL + (ε : ℂ) * (-v * γL) := by rw [← hp]; ring
    have h5 : ‖(ε : ℂ) * (-v * γL)‖ = ε := by
      rw [← mul_assoc, norm_mul, hγL, mul_one, mul_neg, norm_neg, hnεv]
    rw [e]
    calc _ ≤ ‖(Γ (x₀ + N - δ) - z₀ + δ * a) * γL‖ + ‖(ε : ℂ) * (-v * γL)‖ := norm_add_le _ _
      _ = ‖Γ (x₀ + N - δ) - z₀ + δ * a‖ + ε := by rw [norm_mul, hγL, mul_one, h5]
      _ < δ * r₄ := by
        have := hL δ hδ0.le le_rfl
        linarith [mul_le_mul_of_nonneg_right hk₀4 hδ0.le]
  have A2 := b2_lc_quot_change (f := fun t => Γ t - p) (g := fun t => Γ t - z₀) hs12
    hfc.continuousOn hgc.continuousOn (fun τ hτ => (N3 τ hτ).1) (fun τ hτ => (N3 τ hτ).2.1)
    (b2_angleFn_mono hΛp (by linarith) (by linarith))
    (b2_angleFn_mono hΛ (by linarith) (by linarith))
  have B2a := (N3 (x₀ + δ) ⟨le_rfl, hs12⟩).2.2
  have B2b := (N3 (x₀ + N - δ) ⟨hs12, le_rfl⟩).2.2
  rw [Complex.arg_one] at B2a B2b
  obtain ⟨b1a, b1b⟩ := abs_lt.1 B1
  obtain ⟨b3a, b3b⟩ := abs_lt.1 B3
  obtain ⟨b2a, b2b⟩ := abs_lt.1 B2a
  obtain ⟨b2c, b2d⟩ := abs_lt.1 B2b
  obtain ⟨e4a, e4b⟩ := abs_le.1 E4
  obtain ⟨e5a, e5b⟩ := abs_le.1 E5
  rw [abs_le]
  constructor <;> linarith

/-- **The jump at a boundary point** (curve form).  At `Γ x₀`, with right tangent `b`, left tangent
`a`, `b / a` in the slit plane, let `θ = π - arg (b / a) ∈ (0, 2π)` be the interior angle and
`w = e^{i (arg b + θ / 2)}` the unit interior bisector.  Then for small `ε > 0` the points
`Γ x₀ ± ε w` are off the curve, and the angle changes of `Γ - (Γ x₀ ± ε w)` over one period are,
up to `κ`, `B + 2π - θ` and `B - θ`, `B` the angle change of `Γ - Γ x₀` (the boundary winding
angle). -/
theorem b2_lc_jump_core {Γ : ℝ → ℂ} {N x₀ : ℝ} (hN : 0 < N) (hΓc : Continuous Γ)
    (hper : Function.Periodic Γ N) (hne : ∀ τ ∈ Ioo x₀ (x₀ + N), Γ τ ≠ Γ x₀) {a b : ℂ}
    (hch : ∀ k > 0, ∃ η > 0, ∀ σ : ℝ, 0 ≤ σ → σ ≤ η →
      ‖Γ (x₀ + σ) - Γ x₀ - σ * b‖ ≤ k * σ ∧ ‖Γ (x₀ - σ) - Γ x₀ + σ * a‖ ≤ k * σ)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hslit : b / a ∈ slitPlane)
    {Λ : ℝ → ℝ} (hΛ : b2_IsAngleFn (fun t => Γ t - Γ x₀) x₀ (x₀ + N) Λ) {κ : ℝ} (hκ : 0 < κ)
    {w : ℂ} (hw : w = exp (((arg b + (π - arg (b / a)) / 2 : ℝ) : ℂ) * I)) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (Γ x₀ + ε * w ∉ range Γ ∧ ∀ Λp : ℝ → ℝ,
        b2_IsAngleFn (fun t => Γ t - (Γ x₀ + ε * w)) x₀ (x₀ + N) Λp →
          |(Λp (x₀ + N) - Λp x₀) - (Λ (x₀ + N) - Λ x₀) - (π + arg (b / a))| ≤ κ) ∧
      (Γ x₀ + ε * (-w) ∉ range Γ ∧ ∀ Λp : ℝ → ℝ,
        b2_IsAngleFn (fun t => Γ t - (Γ x₀ + ε * (-w))) x₀ (x₀ + N) Λp →
          |(Λp (x₀ + N) - Λp x₀) - (Λ (x₀ + N) - Λ x₀) + (π - arg (b / a))| ≤ κ) := by
  have hap := b2_lc_neg_polar ha0 hb0
  have hbp := (Complex.norm_mul_exp_arg_mul_I b).symm
  have hζ1 := Complex.neg_pi_lt_arg (b / a)
  have hζ2 : arg (b / a) < π :=
    lt_of_le_of_ne (Complex.arg_le_pi _) (Complex.mem_slitPlane_iff_arg.1 hslit).1
  obtain ⟨φ, hφ⟩ : ∃ φ, arg b = φ := ⟨_, rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ, π - arg (b / a) = θ := ⟨_, rfl⟩
  have hζ : arg (b / a) = π - θ := by linarith
  rw [hφ, hθ] at hw hap
  rw [hφ] at hbp
  rw [hζ]
  have hθ0 : 0 < θ := by linarith
  have hθ2 : θ < 2 * π := by linarith
  obtain ⟨rb, hrb⟩ : ∃ rb, ‖b‖ = rb := ⟨_, rfl⟩
  obtain ⟨ra, hra⟩ : ∃ ra, ‖a‖ = ra := ⟨_, rfl⟩
  have hrb0 : 0 < rb := by rw [← hrb]; exact norm_pos_iff.2 hb0
  have hra0 : 0 < ra := by rw [← hra]; exact norm_pos_iff.2 ha0
  rw [hrb] at hbp
  rw [hra] at hap
  have hwn : ‖w‖ = 1 := by rw [hw, Complex.norm_exp_ofReal_mul_I]
  have hwn' : ‖-w‖ = 1 := by rw [norm_neg, hwn]
  -- the half-plane directions (as multipliers `γ = e^{-i (direction)}`)
  obtain ⟨γ1, hγ1⟩ : ∃ γ : ℂ, γ = exp (((π / 2 - θ / 4 - φ : ℝ) : ℂ) * I) := ⟨_, rfl⟩
  obtain ⟨γ2, hγ2⟩ : ∃ γ : ℂ, γ = exp (((-(π / 2) - 3 * θ / 4 - φ : ℝ) : ℂ) * I) := ⟨_, rfl⟩
  obtain ⟨γ3, hγ3⟩ : ∃ γ : ℂ, γ = exp (((-(θ / 4) - φ : ℝ) : ℂ) * I) := ⟨_, rfl⟩
  obtain ⟨γ4, hγ4⟩ : ∃ γ : ℂ, γ = exp (((-(3 * θ / 4) - φ : ℝ) : ℂ) * I) := ⟨_, rfl⟩
  have hn1 : ‖γ1‖ = 1 := by rw [hγ1, Complex.norm_exp_ofReal_mul_I]
  have hn2 : ‖γ2‖ = 1 := by rw [hγ2, Complex.norm_exp_ofReal_mul_I]
  have hn3 : ‖γ3‖ = 1 := by rw [hγ3, Complex.norm_exp_ofReal_mul_I]
  have hn4 : ‖γ4‖ = 1 := by rw [hγ4, Complex.norm_exp_ofReal_mul_I]
  have hψ1 : |π / 2 - θ / 4| < π / 2 := by rw [abs_lt]; constructor <;> linarith
  have hψ2 : |θ / 4 - π / 2| < π / 2 := by rw [abs_lt]; constructor <;> linarith
  have hψ3 : |-(θ / 4)| < π / 2 := by rw [abs_lt]; constructor <;> linarith
  have hψ4 : |θ / 4| < π / 2 := by rw [abs_lt]; constructor <;> linarith
  -- the eight rotated directions
  have Q1 := b2_lc_polar_right (z := b * γ1) (r := rb) (ψ := π / 2 - θ / 4)
    (by rw [hbp, hγ1, mul_assoc, b2_lc_exp_mul_exp (z := π / 2 - θ / 4) (by ring)]) hrb0 hψ1
  have Q2 := b2_lc_polar_right (z := -w * γ1) (r := 1) (ψ := θ / 4 - π / 2)
    (by rw [hw, hγ1, neg_mul, b2_lc_exp_mul_exp (z := θ / 4 + π / 2) (by ring),
      b2_lc_neg_exp_sub (y := θ / 4 - π / 2) (by ring), Complex.ofReal_one, one_mul]) one_pos hψ2
  have Q3 := b2_lc_polar_right (z := -w * γ2) (r := 1) (ψ := π / 2 - θ / 4)
    (by rw [hw, hγ2, neg_mul, b2_lc_exp_mul_exp (z := -(θ / 4) - π / 2) (by ring),
      b2_lc_neg_exp_add (y := π / 2 - θ / 4) (by ring), Complex.ofReal_one, one_mul]) one_pos hψ1
  have Q4 := b2_lc_polar_right (z := -a * γ2) (r := ra) (ψ := θ / 4 - π / 2)
    (by rw [hap, hγ2, mul_assoc, b2_lc_exp_mul_exp (z := θ / 4 - π / 2) (by ring)]) hra0 hψ2
  have Q5 := b2_lc_polar_right (z := b * γ3) (r := rb) (ψ := -(θ / 4))
    (by rw [hbp, hγ3, mul_assoc, b2_lc_exp_mul_exp (z := -(θ / 4)) (by ring)]) hrb0 hψ3
  have Q6 := b2_lc_polar_right (z := -(-w) * γ3) (r := 1) (ψ := θ / 4)
    (by rw [neg_neg, hw, hγ3, b2_lc_exp_mul_exp (z := θ / 4) (by ring), Complex.ofReal_one,
      one_mul]) one_pos hψ4
  have Q7 := b2_lc_polar_right (z := -(-w) * γ4) (r := 1) (ψ := -(θ / 4))
    (by rw [neg_neg, hw, hγ4, b2_lc_exp_mul_exp (z := -(θ / 4)) (by ring), Complex.ofReal_one,
      one_mul]) one_pos hψ3
  have Q8 := b2_lc_polar_right (z := -a * γ4) (r := ra) (ψ := θ / 4)
    (by rw [hap, hγ4, mul_assoc, b2_lc_exp_mul_exp (z := θ / 4) (by ring)]) hra0 hψ4
  have Lp := b2_lc_core hN hΓc hper hne hch hwn hn1 hn2 Q1.1 Q2.1 Q3.1 Q4.1 hΛ hκ
  have Lm := b2_lc_core hN hΓc hper hne hch hwn' hn3 hn4 Q5.1 Q6.1 Q7.1 Q8.1 hΛ hκ
  filter_upwards [Lp, Lm] with ε hp hm
  rw [Q1.2, Q2.2, Q3.2, Q4.2] at hp
  rw [Q5.2, Q6.2, Q7.2, Q8.2] at hm
  refine ⟨⟨hp.1, fun Λp hΛp => ?_⟩, ⟨hm.1, fun Λp hΛp => ?_⟩⟩
  · have := hp.2 Λp hΛp
    convert this using 2
    ring
  · have := hm.2 Λp hΛp
    convert this using 2
    ring

/-- **The jump at a boundary point** (loop form): `b2_lc_jump_core` for the glued loop, with
`θ = π - arg (tanR / tanL)` the interior angle at `Γ x₀`. -/
theorem b2_lc_jump {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) (x₀ : ℝ)
    {Λ : ℝ → ℝ} (hΛ : b2_IsAngleFn (fun t => b2_loop c t - b2_loop c x₀) x₀ (x₀ + n) Λ)
    {κ : ℝ} (hκ : 0 < κ) {w : ℂ}
    (hw : w = exp (((arg (b2_tanR c x₀) + (π - arg (b2_tanR c x₀ / b2_tanL c x₀)) / 2 : ℝ) : ℂ) *
      I)) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (b2_loop c x₀ + ε * w ∉ range (b2_loop c) ∧ ∀ Λp : ℝ → ℝ,
        b2_IsAngleFn (fun t => b2_loop c t - (b2_loop c x₀ + ε * w)) x₀ (x₀ + n) Λp →
          |(Λp (x₀ + n) - Λp x₀) - (Λ (x₀ + n) - Λ x₀) -
            (π + arg (b2_tanR c x₀ / b2_tanL c x₀))| ≤ κ) ∧
      (b2_loop c x₀ + ε * (-w) ∉ range (b2_loop c) ∧ ∀ Λp : ℝ → ℝ,
        b2_IsAngleFn (fun t => b2_loop c t - (b2_loop c x₀ + ε * (-w))) x₀ (x₀ + n) Λp →
          |(Λp (x₀ + n) - Λp x₀) - (Λ (x₀ + n) - Λ x₀) +
            (π - arg (b2_tanR c x₀ / b2_tanL c x₀))| ≤ κ) :=
  b2_lc_jump_core (by exact_mod_cast NeZero.pos n) (b2_loop_continuous hc) (b2_loop_periodic c)
    (fun _ hτ => b2_lc_loop_ne_base hc hτ) (b2_lc_chord_onesided hc x₀) (b2_tan_ne_zero hc x₀).2
    (b2_tan_ne_zero hc x₀).1 (b2_lc_tan_slit hc x₀) hΛ hκ hw

/-- The positively oriented boundary loop winds once around every point of `dom`. -/
theorem b2_wind_loop_in {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    {dom : Set ℂ} (hD : b2_IsPosBoundary c dom) {p : ℂ} (hp : p ∈ dom) (x₀ : ℝ)
    {Λ : ℝ → ℝ} (hΛ : b2_IsAngleFn (fun t => b2_loop c t - p) x₀ (x₀ + n) Λ) :
    Λ (x₀ + n) - Λ x₀ = 2 * π := by
  have hD' := hD
  obtain ⟨hdo, hdc, -, -, hfr, j, t, ht, hpos⟩ := hD
  have hrange : range (b2_loop c) = frontier dom := by rw [b2_loop_range hc, hfr]
  have hdisj : Disjoint dom (range (b2_loop c)) := by
    rw [hrange, hdo.frontier_eq]
    exact Set.disjoint_left.2 fun z hz h => h.2 hz
  have hpR : p ∉ range (b2_loop c) := fun h => Set.disjoint_left.1 hdisj hp h
  obtain ⟨k, hk⟩ := b2_wind_int hc hpR hΛ
  -- the positivity point as a parameter `y₀` of the loop
  obtain ⟨y₀, hy₀⟩ : ∃ y : ℝ, y = (((j : ℕ) : ℤ) : ℝ) + t := ⟨_, rfl⟩
  have hjj : ((((j : ℕ) : ℤ)) : Fin n) = j := by simp
  have hΓy : b2_loop c y₀ = c j t := by
    rw [hy₀, b2_loop_apply hc _ (Ioo_subset_Icc_self ht), hjj]
  have hfr_y : Int.fract y₀ = t := by
    rw [hy₀, Int.fract_intCast_add, Int.fract_eq_self.2 ⟨ht.1.le, ht.2⟩]
  have hfl_y : ⌊y₀⌋ = ((j : ℕ) : ℤ) := by
    rw [hy₀, Int.floor_intCast_add, Int.floor_eq_zero_iff.2 ⟨ht.1.le, ht.2⟩, add_zero]
  have hfy0 : Int.fract y₀ ≠ 0 := by rw [hfr_y]; exact ht.1.ne'
  obtain ⟨hLR, hRd⟩ := b2_tan_of_fract_ne_zero c hfy0
  rw [hfl_y, hfr_y, hjj] at hRd
  have hR0 := (b2_tan_ne_zero hc y₀).1
  have hu0 : deriv (c j) t ≠ 0 := hRd ▸ hR0
  have hnu : 0 < ‖deriv (c j) t‖ := norm_pos_iff.2 hu0
  -- at a smooth point the interior bisector is `i u / |u|`
  have hbis : exp (((arg (b2_tanR c y₀) + (π - arg (b2_tanR c y₀ / b2_tanL c y₀)) / 2 : ℝ) : ℂ) *
      I) = ((‖deriv (c j) t‖⁻¹ : ℝ) : ℂ) * I * deriv (c j) t := by
    rw [hLR, div_self hR0, Complex.arg_one, hRd]
    have e1 := Complex.norm_mul_exp_arg_mul_I (deriv (c j) t)
    have e2 : exp (((arg (deriv (c j) t) + (π - 0) / 2 : ℝ) : ℂ) * I) =
        exp ((arg (deriv (c j) t) : ℂ) * I) * I := by
      rw [← b2_lc_exp_mul_exp (show arg (deriv (c j) t) + π / 2 =
        arg (deriv (c j) t) + (π - 0) / 2 by ring),
        show ((π / 2 : ℝ) : ℂ) = (π : ℂ) / 2 by push_cast; ring, Complex.exp_pi_div_two_mul_I]
    have hn0 : (‖deriv (c j) t‖ : ℂ) ≠ 0 := by exact_mod_cast hnu.ne'
    rw [e2]
    calc exp ((arg (deriv (c j) t) : ℂ) * I) * I =
        ((‖deriv (c j) t‖⁻¹ : ℝ) : ℂ) * I *
          ((‖deriv (c j) t‖ : ℂ) * exp ((arg (deriv (c j) t) : ℂ) * I)) := by
          push_cast
          field_simp
      _ = _ := by rw [e1]
  obtain ⟨Λ₀, hΛ₀⟩ := b2_exists_angleFn_loop hc y₀ (Or.inl rfl)
  have hJ := b2_lc_jump hc y₀ hΛ₀ one_pos rfl
  have hpos' : ∀ᶠ ε : ℝ in 𝓝[>] 0, b2_loop c y₀ + ε *
      exp (((arg (b2_tanR c y₀) + (π - arg (b2_tanR c y₀ / b2_tanL c y₀)) / 2 : ℝ) : ℂ) * I) ∈
        dom := by
    have ht' : Tendsto (fun ε : ℝ => ε / ‖deriv (c j) t‖) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h0 : Tendsto (fun ε : ℝ => ε / ‖deriv (c j) t‖) (𝓝 0) (𝓝 (0 / ‖deriv (c j) t‖)) :=
          (continuous_id.div_const _).tendsto 0
        rw [zero_div] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact div_pos hε hnu
    filter_upwards [ht'.eventually hpos] with ε hε
    rw [hbis, hΓy]
    convert hε using 2
    push_cast
    ring
  obtain ⟨ε, ⟨hp₁, hm₁⟩, hin⟩ := (hJ.and hpos').exists
  -- the two points `Γ y₀ ± ε w`
  obtain ⟨Λp, hΛp⟩ := b2_exists_angleFn_loop hc y₀ (Or.inr hp₁.1)
  obtain ⟨Λm, hΛm⟩ := b2_exists_angleFn_loop hc y₀ (Or.inr hm₁.1)
  have ep := hp₁.2 Λp hΛp
  have em := hm₁.2 Λm hΛm
  rw [hLR, div_self hR0, Complex.arg_one] at ep em
  obtain ⟨ep1, ep2⟩ := abs_le.1 ep
  obtain ⟨em1, em2⟩ := abs_le.1 em
  -- the change around `p` is the change around the inner point `Γ y₀ + ε w`
  obtain ⟨Λpx, hΛpx⟩ := b2_exists_angleFn_loop hc x₀ (Or.inr hp₁.1)
  have r₁ := b2_wind_rebase hc hp₁.1 hΛp hΛpx
  have c₁ := b2_wind_const hc hdc.isPreconnected hdisj hp hin hΛ hΛpx
  -- the point `Γ y₀ - ε w` lies outside `closure dom`
  have hout : b2_loop c y₀ + ε * -exp (((arg (b2_tanR c y₀) +
      (π - arg (b2_tanR c y₀ / b2_tanL c y₀)) / 2 : ℝ) : ℂ) * I) ∉ closure dom := by
    intro hcl
    have hmem : b2_loop c y₀ + ε * -exp (((arg (b2_tanR c y₀) +
        (π - arg (b2_tanR c y₀ / b2_tanL c y₀)) / 2 : ℝ) : ℂ) * I) ∈ dom := by
      by_contra hnd
      apply hm₁.1
      rw [hrange]
      exact ⟨hcl, by rwa [hdo.interior_eq]⟩
    have := b2_wind_const hc hdc.isPreconnected hdisj hin hmem hΛp hΛm
    linarith [Real.pi_gt_three]
  have z₁ := b2_wind_loop_out hc hD' hout y₀ hΛm
  have hW1 : Λ (x₀ + n) - Λ x₀ ≤ 2 * π + 2 := by linarith
  have hW2 : 2 * π - 2 ≤ Λ (x₀ + n) - Λ x₀ := by linarith
  rw [hk] at hW1 hW2 ⊢
  have hk1 : (k : ℝ) < 2 := lt_of_not_ge fun h => by nlinarith [Real.pi_gt_three]
  have hk2 : (0 : ℝ) < k := lt_of_not_ge fun h => by nlinarith [Real.pi_gt_three]
  have hk3 : k = 1 := by
    have h1 : k < 2 := by exact_mod_cast hk1
    have h2 : 0 < k := by exact_mod_cast hk2
    omega
  rw [hk3, Int.cast_one, mul_one]

/-- **Boundary winding angle.**  Seen from a boundary point `Γ x₀`, the positively oriented
boundary turns once around by the interior angle `π - arg (u / v)` there (`= π` at a smooth point). -/
theorem b2_bwa_loop {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    {dom : Set ℂ} (hD : b2_IsPosBoundary c dom) (x₀ : ℝ)
    {Λ : ℝ → ℝ} (hΛ : b2_IsAngleFn (fun t => b2_loop c t - b2_loop c x₀) x₀ (x₀ + n) Λ) :
    Λ (x₀ + n) - Λ x₀ = π - arg (b2_tanR c x₀ / b2_tanL c x₀) := by
  have hD' := hD
  obtain ⟨hdo, -, -, -, hfr, -⟩ := hD
  have hrange : range (b2_loop c) = frontier dom := by rw [b2_loop_range hc, hfr]
  -- off the loop, the change is `2π` (inside) or `0` (outside)
  have hval : ∀ q : ℂ, q ∉ range (b2_loop c) → ∀ Λq : ℝ → ℝ,
      b2_IsAngleFn (fun t => b2_loop c t - q) x₀ (x₀ + n) Λq →
        Λq (x₀ + n) - Λq x₀ = 2 * π ∨ Λq (x₀ + n) - Λq x₀ = 0 := by
    intro q hq Λq hΛq
    by_cases hqd : q ∈ dom
    · exact Or.inl (b2_wind_loop_in hc hD' hqd x₀ hΛq)
    · refine Or.inr (b2_wind_loop_out hc hD' (fun hcl => hq ?_) x₀ hΛq)
      rw [hrange]
      exact ⟨hcl, by rwa [hdo.interior_eq]⟩
  have key : ∀ κ : ℝ, 0 < κ → κ < π / 2 →
      |Λ (x₀ + n) - Λ x₀ - (π - arg (b2_tanR c x₀ / b2_tanL c x₀))| ≤ κ := by
    intro κ hκ hκπ
    obtain ⟨ε, hp₁, hm₁⟩ := (b2_lc_jump hc x₀ hΛ hκ rfl).exists
    obtain ⟨Λp, hΛp⟩ := b2_exists_angleFn_loop hc x₀ (Or.inr hp₁.1)
    obtain ⟨Λm, hΛm⟩ := b2_exists_angleFn_loop hc x₀ (Or.inr hm₁.1)
    obtain ⟨a1, a2⟩ := abs_le.1 (hp₁.2 Λp hΛp)
    obtain ⟨b1, b2⟩ := abs_le.1 (hm₁.2 Λm hΛm)
    rw [abs_le]
    rcases hval _ hp₁.1 Λp hΛp with v1 | v1 <;> rcases hval _ hm₁.1 Λm hΛm with v2 | v2 <;>
      constructor <;> linarith [Real.pi_pos]
  by_contra hne
  have hpos : 0 < |Λ (x₀ + n) - Λ x₀ - (π - arg (b2_tanR c x₀ / b2_tanL c x₀))| :=
    abs_pos.2 (sub_ne_zero.2 hne)
  have h1 := key (min (|Λ (x₀ + n) - Λ x₀ - (π - arg (b2_tanR c x₀ / b2_tanL c x₀))| / 2)
    (π / 4)) (lt_min (half_pos hpos) (by positivity))
    (lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos]))
  have h2 := min_le_left (|Λ (x₀ + n) - Λ x₀ - (π - arg (b2_tanR c x₀ / b2_tanL c x₀))| / 2)
    (π / 4)
  linarith

/-! ## Hopf's Umlaufsatz (loop form) -/

/-- **Square lift.**  A continuous non-vanishing `H` on the closed square `[0, 1]²` has a continuous
logarithm there: clamp `H` to `ℝ²` (through `projIcc`) and lift it on the simply connected plane. -/
theorem b2_square_log {H : ℝ × ℝ → ℂ} (hc : ContinuousOn H (Icc 0 1 ×ˢ Icc 0 1))
    (hH : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, H p ≠ 0) :
    ∃ L : ℝ × ℝ → ℂ, ContinuousOn L (Icc 0 1 ×ˢ Icc 0 1) ∧
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, exp (L p) = H p := by
  set q : ℝ × ℝ → ℝ × ℝ := fun p =>
    ((projIcc (0 : ℝ) 1 zero_le_one p.1 : ℝ), (projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ)) with hqdef
  have hqc : Continuous q := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)
    · exact continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd)
  have hqmem : ∀ p, q p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := fun p =>
    ⟨(projIcc (0 : ℝ) 1 zero_le_one p.1).2, (projIcc (0 : ℝ) 1 zero_le_one p.2).2⟩
  have hqid : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, q p = p := fun p hp => by
    obtain ⟨h1, h2⟩ := hp
    simp only [hqdef, projIcc_of_mem _ h1, projIcc_of_mem _ h2]
  have hGc : Continuous (H ∘ q) :=
    hc.comp_continuous hqc hqmem
  have hU : IsSimplyConnected (univ : Set (ℝ × ℝ)) := by
    unfold IsSimplyConnected
    have : ContractibleSpace (univ : Set (ℝ × ℝ)) :=
      (convex_univ : Convex ℝ (univ : Set (ℝ × ℝ))).contractibleSpace univ_nonempty
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨L, hLc, hL⟩ := Complex.exists_continuousOn_eqOn_exp_comp hU isOpen_univ
    hGc.continuousOn (by rintro ⟨p, -, hp⟩; exact hH _ (hqmem p) hp)
  refine ⟨L, hLc.mono (subset_univ _), fun p hp => ?_⟩
  have := hL (mem_univ p)
  simp only [Function.comp_apply, hqid p hp] at this
  exact this

/-- A continuous `ℓ` with `f = r e^{ℓ}` for some `r > 0` at each point of the open interval gives
the angle function `Im ℓ` of `f`. -/
theorem b2_angleFn_of_exp {f ℓ : ℝ → ℂ} {a b : ℝ} (hℓ : ContinuousOn ℓ (Icc a b))
    (h : ∀ t ∈ Ioo a b, ∃ r : ℝ, 0 < r ∧ f t = r * exp (ℓ t)) :
    b2_IsAngleFn f a b (fun t => (ℓ t).im) := by
  refine ⟨Complex.continuous_im.comp_continuousOn hℓ, fun t ht => ?_⟩
  obtain ⟨r, hr, hfr⟩ := h t ht
  have hsplit : exp (ℓ t) = (Real.exp (ℓ t).re : ℂ) * exp (((ℓ t).im : ℂ) * I) := by
    conv_lhs => rw [← Complex.re_add_im (ℓ t)]
    rw [Complex.exp_add, Complex.ofReal_exp]
  have hnorm : ‖f t‖ = r * Real.exp (ℓ t).re := by
    rw [hfr, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [hnorm, hfr, hsplit]
  push_cast
  ring

/-- Angle functions translate. -/
theorem b2_angleFn_shift {f : ℝ → ℂ} {a b : ℝ} {θ : ℝ → ℝ} (h : b2_IsAngleFn f a b θ) (k : ℝ) :
    b2_IsAngleFn (fun s => f (s - k)) (a + k) (b + k) (fun s => θ (s - k)) := by
  refine ⟨h.1.comp (continuous_id.sub continuous_const).continuousOn
    (fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩),
    fun s hs => h.2 (s - k) ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩

/-- Stability of angle changes: if `f` is relatively `δ`-close to the non-vanishing `g` on `(a, b)`,
then the angle changes of `f` and `g` over `[a, b]` differ by at most `ε`. -/
theorem b2_angleFn_approx {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {f g : ℝ → ℂ} {a b : ℝ} {θf θg : ℝ → ℝ}, a ≤ b → b2_IsAngleFn f a b θf →
      b2_IsAngleFn g a b θg → (∀ t ∈ Ioo a b, g t ≠ 0 ∧ ‖f t - g t‖ ≤ δ * ‖g t‖) →
      |(θf b - θf a) - (θg b - θg a)| ≤ ε := by
  have hc : ContinuousAt arg 1 := Complex.continuousAt_arg one_mem_slitPlane
  obtain ⟨ρ, hρ, hρa⟩ := Metric.continuousAt_iff.1 hc (ε / 2) (by linarith)
  refine ⟨min (ρ / 4) (1 / 4), by positivity, ?_⟩
  intro f g a b θf θg hab hf hg hfg
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp [hε.le]
  set e : ℝ → ℂ := fun t => exp (((θf t - θg t : ℝ) : ℂ) * I) with hedef
  have hθc : ContinuousOn (fun t => θf t - θg t) (Icc a b) := hf.1.sub hg.1
  have hec : ContinuousOn e (Icc a b) :=
    Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hθc).mul continuousOn_const)
  have hclose : ∀ t ∈ Ioo a b, ‖e t - 1‖ ≤ 2 * min (ρ / 4) (1 / 4) := by
    intro t ht
    obtain ⟨hg0, hle⟩ := hfg t ht
    have hgn : (0 : ℝ) < ‖g t‖ := norm_pos_iff.2 hg0
    have hδ : min (ρ / 4) (1 / 4) ≤ 1 / 4 := min_le_right _ _
    have hf0 : f t ≠ 0 := by
      intro h0
      rw [h0, zero_sub, norm_neg] at hle
      nlinarith
    have hfn : (0 : ℝ) < ‖f t‖ := norm_pos_iff.2 hf0
    have hFe : exp ((θf t : ℂ) * I) = f t / (‖f t‖ : ℂ) := by
      rw [eq_div_iff (by exact_mod_cast hfn.ne'), mul_comm]; exact (hf.2 t ht).symm
    have hGe : exp ((θg t : ℂ) * I) = g t / (‖g t‖ : ℂ) := by
      rw [eq_div_iff (by exact_mod_cast hgn.ne'), mul_comm]; exact (hg.2 t ht).symm
    have het : e t = (f t / (‖f t‖ : ℂ)) / (g t / (‖g t‖ : ℂ)) := by
      simp only [hedef]
      push_cast
      rw [sub_mul, Complex.exp_sub, hFe, hGe]
    have hGn : ‖g t / (‖g t‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hgn.le, div_self hgn.ne']
    have hG0 : g t / (‖g t‖ : ℂ) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hGn; exact zero_ne_one hGn
    have h1 : ‖e t - 1‖ = ‖f t / (‖f t‖ : ℂ) - g t / (‖g t‖ : ℂ)‖ := by
      rw [het, show f t / (‖f t‖ : ℂ) / (g t / (‖g t‖ : ℂ)) - 1 =
        (f t / (‖f t‖ : ℂ) - g t / (‖g t‖ : ℂ)) / (g t / (‖g t‖ : ℂ)) by
          rw [sub_div, div_self hG0],
        norm_div, hGn, div_one]
    have hkey : f t / (‖f t‖ : ℂ) - g t / (‖g t‖ : ℂ) =
        (f t - g t) / (‖g t‖ : ℂ) +
          (f t / (‖f t‖ : ℂ)) * (((‖g t‖ - ‖f t‖ : ℝ) : ℂ) / (‖g t‖ : ℂ)) := by
      have h1' : (‖f t‖ : ℂ) ≠ 0 := by exact_mod_cast hfn.ne'
      have h2' : (‖g t‖ : ℂ) ≠ 0 := by exact_mod_cast hgn.ne'
      push_cast
      field_simp
      ring
    have hFn : ‖f t / (‖f t‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hfn.le, div_self hfn.ne']
    have hrev : |‖g t‖ - ‖f t‖| ≤ ‖f t - g t‖ := by
      rw [abs_sub_comm]; exact abs_norm_sub_norm_le _ _
    rw [h1, hkey]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hFn, one_mul, norm_div, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hgn.le, Real.norm_eq_abs]
    rw [← add_div, div_le_iff₀ hgn]
    nlinarith
  have hcl : ∀ t ∈ Icc a b, ‖e t - 1‖ ≤ 2 * min (ρ / 4) (1 / 4) := by
    intro t ht
    rw [← closure_Ioo hlt.ne] at ht
    refine le_on_closure hclose ?_ continuousOn_const ht
    rw [closure_Ioo hlt.ne]
    exact (hec.sub continuousOn_const).norm
  have hslit : ∀ t ∈ Icc a b, e t ∈ slitPlane := by
    intro t ht
    apply ball_one_subset_slitPlane
    rw [mem_ball, dist_eq_norm]
    have := hcl t ht
    have : min (ρ / 4) (1 / 4) ≤ 1 / 4 := min_le_right _ _
    linarith
  have hA1 : b2_IsAngleFn e a b (fun t => arg (e t)) := b2_angleFn_arg hec hslit
  have hA2 : b2_IsAngleFn e a b (fun t => θf t - θg t) := by
    refine ⟨hθc, fun t _ => ?_⟩
    simp only [hedef]
    rw [Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, one_mul]
  have hch := b2_angleFn_change_eq hab
    (fun t ht => slitPlane_ne_zero (hslit t (Ioo_subset_Icc_self ht))) hA2 hA1
  have harg : ∀ t ∈ Icc a b, |arg (e t)| < ε / 2 := by
    intro t ht
    have h1 : dist (e t) 1 < ρ := by
      rw [dist_eq_norm]
      have := hcl t ht
      have : min (ρ / 4) (1 / 4) ≤ ρ / 4 := min_le_left _ _
      linarith
    have := hρa h1
    rwa [Complex.arg_one, Real.dist_eq, sub_zero] at this
  have hb := harg b (right_mem_Icc.2 hab)
  have ha := harg a (left_mem_Icc.2 hab)
  have : (θf b - θf a) - (θg b - θg a) = arg (e b) - arg (e a) := by linarith
  rw [this]
  rw [abs_le]
  constructor <;> linarith [abs_lt.1 hb, abs_lt.1 ha]

/-- The glued loop takes different values at two parameters whose distance lies strictly between
`0` and `n`. -/
theorem b2_loop_ne {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) {s t : ℝ}
    (h1 : s < t) (h2 : t < s + n) : b2_loop c t ≠ b2_loop c s := by
  intro h
  obtain ⟨k, hk⟩ := (b2_loop_eq_iff hc).1 h.symm
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hk0 : (0 : ℝ) < k := pos_of_mul_pos_left (by linarith : (0 : ℝ) < k * n) hn.le
  have hk1 : (k : ℝ) < 1 := by nlinarith
  have h0 : (0 : ℤ) < k := by exact_mod_cast hk0
  have h1' : k < (1 : ℤ) := by exact_mod_cast hk1
  omega

/-- **Hopf's triangle.**  For `0 < h < n`, the secant map `(s, t) ↦ Γ t - Γ s` on the triangle
`x₀ ≤ s`, `t ≤ x₀ + n`, `t - s ≥ h` (normalized at the corner `(x₀, x₀ + n)` by the tangent at the
smooth point `x₀`) lifts through a square parametrization.  Hence the angle change of the short
chords `Γ (s + h) - Γ s` along `[x₀, x₀ + n - h]` is the sum of the angle changes of `Γ - Γ x₀`
along the two legs. -/
theorem b2_hopf_triangle {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) (x₀ : ℝ)
    (hx₀ : Int.fract x₀ ≠ 0)
    {Λ : ℝ → ℝ} (hΛ : b2_IsAngleFn (fun t => b2_loop c t - b2_loop c x₀) x₀ (x₀ + n) Λ)
    {h : ℝ} (h0 : 0 < h) (hn : h < n) :
    ∃ Φ : ℝ → ℝ, b2_IsAngleFn (fun s => b2_loop c (s + h) - b2_loop c s) x₀ (x₀ + n - h) Φ ∧
      Φ (x₀ + n - h) - Φ x₀ = (Λ (x₀ + n) - Λ (x₀ + h)) + (Λ (x₀ + n - h) - Λ x₀) := by
  set Γ := b2_loop c with hΓ
  have hΓc : Continuous Γ := b2_loop_continuous hc
  have hper : ∀ t, Γ (t + n) = Γ t := b2_loop_periodic c
  set N : ℝ := n - h with hN
  have hNpos : 0 < N := by rw [hN]; linarith
  set X : ℝ := x₀ + n with hX
  set T : ℂ := b2_tanR c X with hT
  have hT0 : T ≠ 0 := (b2_tan_ne_zero hc X).1
  have hΓX : Γ X = Γ x₀ := hper x₀
  -- the chord estimate at the smooth point `X`
  have hfrX : Int.fract X ≠ 0 := by rw [hX, Int.fract_add_natCast]; exact hx₀
  have hLR := (b2_tan_of_fract_ne_zero c hfrX).1
  have hchord : ∀ κ > 0, ∃ η > 0, ∀ s t : ℝ, X - η ≤ s → s ≤ t → t ≤ X + η →
      ‖Γ t - Γ s - ((t - s : ℝ) : ℂ) * T‖ ≤ κ * (t - s) := by
    intro κ hκ
    obtain ⟨η, hη, hηc⟩ := b2_chord_approx hc X hκ
    refine ⟨η, hη, fun s t h1 h2 h3 => ?_⟩
    have := hηc s t h1 h2 h3
    rw [hLR, ← add_mul, ← Complex.ofReal_add] at this
    have e : (min t X - min s X) + (max t X - max s X) = t - s := by
      linarith [min_add_max t X, min_add_max s X]
    rwa [e] at this
  -- the normalized secant map on the square
  set S : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 with hS
  set H : ℝ × ℝ → ℂ := fun p => if p.2 = 0 then -T else
      (Γ (X - p.1 * p.2 * N) - Γ (x₀ + p.2 * (1 - p.1) * N)) / ((p.2 * N : ℝ) : ℂ) with hHdef
  have hHne : ∀ p : ℝ × ℝ, p.2 ≠ 0 →
      H p = (Γ (X - p.1 * p.2 * N) - Γ (x₀ + p.2 * (1 - p.1) * N)) / ((p.2 * N : ℝ) : ℂ) := by
    intro p hp
    simp only [hHdef, hp, ↓reduceIte]
  have hH0 : ∀ p : ℝ × ℝ, p.2 = 0 → H p = -T := by
    intro p hp
    simp only [hHdef, hp, ↓reduceIte]
  have hHc : ContinuousOn H S := by
    intro p hp
    by_cases hp2 : p.2 = 0
    · rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨η, hη, hηc⟩ := hchord (ε / 2) (by linarith)
      refine ⟨η / N, div_pos hη hNpos, fun {q} hq hqp => ?_⟩
      rw [hH0 p hp2]
      by_cases hq2 : q.2 = 0
      · rw [hH0 q hq2, dist_self]; exact hε
      have hq2pos : 0 < q.2 := lt_of_le_of_ne hq.2.1 (Ne.symm hq2)
      have hq2η : q.2 * N < η := by
        have h1 : dist q.2 p.2 < η / N := lt_of_le_of_lt (le_max_right _ _) hqp
        rw [hp2, Real.dist_eq, sub_zero, abs_of_pos hq2pos, lt_div_iff₀ hNpos] at h1
        exact h1
      have hq1 := hq.1
      have hqN : 0 < q.2 * N := mul_pos hq2pos hNpos
      set t₁ : ℝ := X - q.1 * q.2 * N with ht₁
      set s₁ : ℝ := X + q.2 * (1 - q.1) * N with hs₁
      have hΓs₁ : Γ (x₀ + q.2 * (1 - q.1) * N) = Γ s₁ := by
        rw [hs₁, hX, show x₀ + ↑n + q.2 * (1 - q.1) * N = x₀ + q.2 * (1 - q.1) * N + n by ring,
          hper]
      have hst : s₁ - t₁ = q.2 * N := by rw [hs₁, ht₁]; ring
      have hle := hηc t₁ s₁ (by rw [ht₁]; nlinarith [hq1.1, hq1.2])
        (by rw [ht₁, hs₁]; nlinarith [hq1.1, hq1.2]) (by rw [hs₁]; nlinarith [hq1.1, hq1.2])
      rw [hst] at hle
      rw [hHne q hq2, hΓs₁, dist_eq_norm, sub_neg_eq_add]
      have hqNc : ((q.2 * N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hqN.ne'
      rw [show (Γ t₁ - Γ s₁) / ((q.2 * N : ℝ) : ℂ) + T =
          -((Γ s₁ - Γ t₁ - ((q.2 * N : ℝ) : ℂ) * T) / ((q.2 * N : ℝ) : ℂ)) by
        field_simp; ring]
      rw [norm_neg, norm_div, Complex.norm_real, Real.norm_of_nonneg hqN.le, div_lt_iff₀ hqN]
      nlinarith
    · have hev : H =ᶠ[𝓝 p] fun q => (Γ (X - q.1 * q.2 * N) - Γ (x₀ + q.2 * (1 - q.1) * N)) /
          ((q.2 * N : ℝ) : ℂ) := by
        filter_upwards [(isOpen_ne_fun continuous_snd continuous_const).mem_nhds hp2] with q hq
        exact hHne q hq
      refine (ContinuousAt.congr ?_ hev.symm).continuousWithinAt
      refine ContinuousAt.div ?_ ?_ ?_
      · refine ContinuousAt.sub ?_ ?_
        · exact hΓc.continuousAt.comp (by fun_prop)
        · exact hΓc.continuousAt.comp (by fun_prop)
      · exact Complex.continuous_ofReal.continuousAt.comp (by fun_prop)
      · exact_mod_cast mul_ne_zero hp2 hNpos.ne'
  have hHnz : ∀ p ∈ S, H p ≠ 0 := by
    intro p hp
    by_cases hp2 : p.2 = 0
    · rw [hH0 p hp2]; exact neg_ne_zero.2 hT0
    have hp2pos : 0 < p.2 := lt_of_le_of_ne hp.2.1 (Ne.symm hp2)
    rw [hHne p hp2]
    refine div_ne_zero (sub_ne_zero.2 ?_) (by exact_mod_cast (mul_pos hp2pos hNpos).ne')
    have hp1 := hp.1
    have hp2' := hp.2
    refine b2_loop_ne hc ?_ ?_
    · rw [hX]; nlinarith [mul_le_mul_of_nonneg_left hp2'.2 hNpos.le]
    · rw [hX]; nlinarith [mul_le_mul_of_nonneg_left hp2'.2 hNpos.le]
  obtain ⟨L, hLc, hL⟩ := b2_square_log hHc hHnz
  -- the leg `s = x₀`
  have hA : b2_IsAngleFn (fun t => Γ t - Γ x₀) (x₀ + h) X (fun t => (L (1, (X - t) / N)).im) := by
    refine b2_angleFn_of_exp (ℓ := fun t => L (1, (X - t) / N)) ?_ ?_
    · refine hLc.comp (by fun_prop) (fun t ht => ⟨⟨zero_le_one, le_rfl⟩, ?_, ?_⟩)
      · exact div_nonneg (by linarith [ht.2]) hNpos.le
      · rw [div_le_one hNpos, hN]; linarith [ht.1]
    · intro t ht
      have hb : (X - t) / N ≠ 0 := div_ne_zero (by linarith [ht.2]) hNpos.ne'
      refine ⟨X - t, by linarith [ht.2], ?_⟩
      rw [hL _ ⟨⟨zero_le_one, le_rfl⟩, div_nonneg (by linarith [ht.2]) hNpos.le,
        by rw [div_le_one hNpos, hN]; linarith [ht.1]⟩, hHne _ hb]
      have e1 : X - 1 * ((X - t) / N) * N = t := by field_simp; ring
      have e2 : x₀ + (X - t) / N * (1 - 1) * N = x₀ := by ring
      have e3 : (X - t) / N * N = X - t := by field_simp
      simp only
      rw [e1, e2, e3, mul_div_cancel₀]
      exact_mod_cast (show X - t ≠ 0 by linarith [ht.2])
  have hΛA : b2_IsAngleFn (fun t => Γ t - Γ x₀) (x₀ + h) X Λ :=
    b2_angleFn_mono hΛ (by linarith) le_rfl
  have hchA := b2_angleFn_change_eq (by rw [hX]; linarith)
    (fun t ht => sub_ne_zero.2
      (b2_loop_ne hc (by linarith [ht.1]) (by rw [hX] at ht; linarith [ht.2]))) hA hΛA
  -- the leg `t = x₀ + n`
  have hC : b2_IsAngleFn (fun s => -(Γ s - Γ x₀)) x₀ (x₀ + N)
      (fun s => (L (0, (s - x₀) / N)).im) := by
    refine b2_angleFn_of_exp (ℓ := fun s => L (0, (s - x₀) / N)) ?_ ?_
    · refine hLc.comp (by fun_prop) (fun s hs => ⟨⟨le_rfl, zero_le_one⟩, ?_, ?_⟩)
      · exact div_nonneg (by linarith [hs.1]) hNpos.le
      · rw [div_le_one hNpos]; linarith [hs.2]
    · intro s hs
      have hb : (s - x₀) / N ≠ 0 := div_ne_zero (by linarith [hs.1]) hNpos.ne'
      refine ⟨s - x₀, by linarith [hs.1], ?_⟩
      rw [hL _ ⟨⟨le_rfl, zero_le_one⟩, div_nonneg (by linarith [hs.1]) hNpos.le,
        by rw [div_le_one hNpos]; linarith [hs.2]⟩, hHne _ hb]
      have e1 : X - 0 * ((s - x₀) / N) * N = X := by ring
      have e2 : x₀ + (s - x₀) / N * (1 - 0) * N = s := by field_simp; ring
      have e3 : (s - x₀) / N * N = s - x₀ := by field_simp
      simp only
      rw [e1, e2, e3, hΓX, mul_div_cancel₀]
      · ring
      · exact_mod_cast (show s - x₀ ≠ 0 by linarith [hs.1])
  have hΛC : b2_IsAngleFn (fun s => -(Γ s - Γ x₀)) x₀ (x₀ + N) (fun s => Λ s + π) :=
    b2_angleFn_mono (b2_angleFn_neg hΛ) le_rfl (by rw [hN]; linarith)
  have hchC := b2_angleFn_change_eq (by linarith)
    (fun s hs => neg_ne_zero.2 (sub_ne_zero.2
      (b2_loop_ne hc (by linarith [hs.1]) (by rw [hN] at hs; linarith [hs.2])))) hC hΛC
  -- the degenerate edge at the corner `(x₀, x₀ + n)`
  have hB : b2_IsAngleFn (fun _ => -T) 0 1 (fun a => (L (a, 0)).im) := by
    refine b2_angleFn_of_exp (ℓ := fun a => L (a, 0)) ?_ ?_
    · exact hLc.comp (by fun_prop) (fun a ha => ⟨ha, le_rfl, zero_le_one⟩)
    · intro a ha
      refine ⟨1, one_pos, ?_⟩
      rw [hL _ ⟨Ioo_subset_Icc_self ha, le_rfl, zero_le_one⟩, hH0 _ rfl, Complex.ofReal_one,
        one_mul]
  have hB' : b2_IsAngleFn (fun _ => -T) 0 1 (fun _ => arg (-T)) :=
    ⟨continuousOn_const, fun _ _ => (Complex.norm_mul_exp_arg_mul_I _).symm⟩
  have hchB := b2_angleFn_change_eq zero_le_one (fun _ _ => neg_ne_zero.2 hT0) hB hB'
  -- the diagonal `t = s + h`
  have hD : b2_IsAngleFn (fun s => Γ (s + h) - Γ s) x₀ (x₀ + N)
      (fun s => (L (1 - (s - x₀) / N, 1)).im) := by
    refine b2_angleFn_of_exp (ℓ := fun s => L (1 - (s - x₀) / N, 1)) ?_ ?_
    · refine hLc.comp (by fun_prop) (fun s hs => ⟨⟨?_, ?_⟩, zero_le_one, le_rfl⟩)
      · rw [sub_nonneg, div_le_one hNpos]; linarith [hs.2]
      · have : 0 ≤ (s - x₀) / N := div_nonneg (by linarith [hs.1]) hNpos.le
        linarith
    · intro s hs
      refine ⟨N, hNpos, ?_⟩
      have ha1 : 0 ≤ 1 - (s - x₀) / N := by rw [sub_nonneg, div_le_one hNpos]; linarith [hs.2]
      have ha2 : 1 - (s - x₀) / N ≤ 1 := by
        have : 0 ≤ (s - x₀) / N := div_nonneg (by linarith [hs.1]) hNpos.le
        linarith
      rw [hL _ ⟨⟨ha1, ha2⟩, zero_le_one, le_rfl⟩, hHne _ one_ne_zero]
      have e1 : X - (1 - (s - x₀) / N) * 1 * N = s + h := by
        rw [hX]; field_simp; rw [hN]; ring
      have e2 : x₀ + 1 * (1 - (1 - (s - x₀) / N)) * N = s := by field_simp; ring
      simp only
      rw [e1, e2, one_mul, mul_div_cancel₀]
      exact_mod_cast hNpos.ne'
  have hend : x₀ + n - h = x₀ + N := by rw [hN]; ring
  refine ⟨fun s => (L (1 - (s - x₀) / N, 1)).im, ?_, ?_⟩
  · rw [hend]; exact hD
  · rw [hend]
    have v1 : (X - (x₀ + h)) / N = 1 := by rw [div_eq_one_iff_eq hNpos.ne', hX, hN]; ring
    have v2 : (X - X) / N = 0 := by simp
    have v3 : (x₀ + N - x₀) / N = 1 := by rw [add_sub_cancel_left, div_self hNpos.ne']
    have v4 : (x₀ - x₀) / N = 0 := by simp
    simp only [v1, v2] at hchA
    simp only [v3, v4] at hchC
    simp only [v3, sub_self, zero_div, sub_zero]
    linarith

/-- The model chord at a vertex.  For `u / v` in the slit plane, the segment
`(k - s) v + (s + h - k) u`, `s ∈ [k - h, k]`, stays at distance `≥ m h` from `0` and has an angle
function turning by `arg (u / v)`. -/
theorem b2_corner_model {u v : ℂ} (hv : v ≠ 0) (hz : u / v ∈ slitPlane) :
    ∃ m > 0, ∀ k h : ℝ, 0 < h →
      (∀ s ∈ Icc (k - h) k, m * h ≤ ‖((k - s : ℝ) : ℂ) * v + ((s + h - k : ℝ) : ℂ) * u‖) ∧
      ∃ θ : ℝ → ℝ,
        b2_IsAngleFn (fun s => ((k - s : ℝ) : ℂ) * v + ((s + h - k : ℝ) : ℂ) * u) (k - h) k θ ∧
        θ k - θ (k - h) = arg (u / v) := by
  set z := u / v with hzdef
  set w : ℝ → ℂ := fun l => ((1 - l : ℝ) : ℂ) + (l : ℂ) * z with hwdef
  have hwc : Continuous w := by rw [hwdef]; fun_prop
  have hwslit : ∀ l ∈ Icc (0 : ℝ) 1, w l ∈ slitPlane := by
    intro l hl
    have := starConvex_one_slitPlane hz (sub_nonneg.2 hl.2) hl.1 (by ring : (1 - l) + l = 1)
    simpa [hwdef, Complex.real_smul] using this
  obtain ⟨l₀, hl₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) hwc.norm.continuousOn
  have hm : 0 < ‖v‖ * ‖w l₀‖ :=
    mul_pos (norm_pos_iff.2 hv) (norm_pos_iff.2 (slitPlane_ne_zero (hwslit l₀ hl₀)))
  have hvc : v ≠ 0 := hv
  refine ⟨‖v‖ * ‖w l₀‖, hm, fun k h hh => ⟨?_, ?_⟩⟩
  · intro s hs
    have hl : (s + h - k) / h ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (by linarith [hs.1]) hh.le, by rw [div_le_one hh]; linarith [hs.2]⟩
    have heq : ((k - s : ℝ) : ℂ) * v + ((s + h - k : ℝ) : ℂ) * u =
        (h : ℂ) * v * w ((s + h - k) / h) := by
      have hhc : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
      simp only [hwdef, hzdef]
      push_cast
      field_simp
      ring
    rw [heq, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh.le]
    have := isMinOn_iff.1 hmin _ hl
    have hv0 := norm_nonneg v
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hh.le hv0)]
  · refine ⟨fun s => arg v + arg (w ((s + h - k) / h)), ?_, ?_⟩
    · have hfun : (fun s => ((k - s : ℝ) : ℂ) * v + ((s + h - k : ℝ) : ℂ) * u) =
          fun s => ((h : ℂ) * v) * w ((s + h - k) / h) := by
        funext s
        have hhc : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
        simp only [hwdef, hzdef]
        push_cast
        field_simp
        ring
      rw [hfun]
      have h1 : b2_IsAngleFn (fun _ => (h : ℂ) * v) (k - h) k (fun _ => arg v) := by
        refine ⟨continuousOn_const, fun _ _ => ?_⟩
        conv_rhs => rw [← Complex.arg_real_mul v hh]
        exact (Complex.norm_mul_exp_arg_mul_I _).symm
      have h2 : b2_IsAngleFn (fun s => w ((s + h - k) / h)) (k - h) k
          (fun s => arg (w ((s + h - k) / h))) := by
        refine b2_angleFn_arg (hwc.comp (by fun_prop)).continuousOn (fun s hs => hwslit _ ?_)
        exact ⟨div_nonneg (by linarith [hs.1]) hh.le, by rw [div_le_one hh]; linarith [hs.2]⟩
      exact b2_angleFn_mul h1 h2
    · have e1 : (k + h - k) / h = 1 := by rw [add_sub_cancel_left, div_self hh.ne']
      have e0 : (k - h + h - k) / h = 0 := by simp
      simp only [e1, e0, hwdef]
      simp

/-- The tangents of the sides of a corner loop are bounded away from `0`. -/
theorem b2_derivWithin_lower {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) :
    ∃ M > 0, ∀ j, ∀ τ ∈ Icc (0 : ℝ) 1, M ≤ ‖derivWithin (c j) (Icc 0 1) τ‖ := by
  obtain ⟨hC, hd, -⟩ := hc
  have hmin : ∀ j, ∃ τ ∈ Icc (0 : ℝ) 1,
      IsMinOn (fun t => ‖derivWithin (c j) (Icc 0 1) t‖) (Icc 0 1) τ := fun j =>
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one)
      ((hC j).continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl).norm
  choose τ hτ hτmin using hmin
  have : Nonempty (Fin n) := ⟨0⟩
  obtain ⟨j₀, hj₀⟩ := Finite.exists_min (fun j => ‖derivWithin (c j) (Icc 0 1) (τ j)‖)
  exact ⟨_, norm_pos_iff.2 (hd j₀ _ (hτ j₀)),
    fun j t ht => (hj₀ j).trans (isMinOn_iff.1 (hτmin j) t ht)⟩

/-- **Chords across a vertex.**  For small `h`, the angle change of the chords `Γ (s + h) - Γ s`
over `s ∈ [k - h, k]` (the chords straddling the vertex at the integer `k`) is within `ε` of the
exterior angle at that vertex. -/
theorem b2_hopf_corner {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) (k : ℤ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ Φ : ℝ → ℝ,
      b2_IsAngleFn (fun s => b2_loop c (s + h) - b2_loop c s) (k - h) k Φ →
      |(Φ k - Φ (k - h)) - b2_extAngle c (k : Fin n)| ≤ ε := by
  set u := b2_tanR c k with hu
  set v := b2_tanL c k with hv
  have hv0 : v ≠ 0 := (b2_tan_ne_zero hc k).2
  have hext : b2_extAngle c (k : Fin n) = arg (u / v) := by
    rw [hu, hv, b2_tanR_int, b2_tanL_int]; rfl
  have hz : u / v ∈ slitPlane := by
    rw [hu, hv, b2_tanR_int, b2_tanL_int]; exact hc.2.2.2.2 _
  obtain ⟨m, hm, hmod⟩ := b2_corner_model hv0 hz
  obtain ⟨δ, hδ, happ⟩ := b2_angleFn_approx hε
  obtain ⟨η, hη, hch⟩ := b2_chord_approx hc (k : ℝ) (mul_pos hδ hm)
  filter_upwards [Ioo_mem_nhdsGT hη] with h hh Φ hΦ
  obtain ⟨hlow, θ, hθ, hθch⟩ := hmod k h hh.1
  rw [hext, ← hθch]
  refine happ (by linarith [hh.1]) hΦ hθ (fun s hs => ⟨?_, ?_⟩)
  · intro h0
    have := hlow s (Ioo_subset_Icc_self hs)
    rw [h0, norm_zero] at this
    nlinarith [hh.1]
  · have hs' := Ioo_subset_Icc_self hs
    have := hch s (s + h) (by linarith [hs'.1, hh.2]) (by linarith [hh.1])
      (by linarith [hs'.2, hh.2])
    rw [min_eq_right (by linarith [hs'.1] : (k : ℝ) ≤ s + h), min_eq_left hs'.2,
      max_eq_left (by linarith [hs'.1] : (k : ℝ) ≤ s + h), max_eq_right hs'.2,
      show s + h - s = h by ring] at this
    have hl := hlow s hs'
    calc ‖b2_loop c (s + h) - b2_loop c s - (((k - s : ℝ) : ℂ) * v + ((s + h - k : ℝ) : ℂ) * u)‖
        = ‖b2_loop c (s + h) - b2_loop c s - (((k - s : ℝ) : ℂ) * b2_tanL c k +
          ((s + h - k : ℝ) : ℂ) * b2_tanR c k)‖ := by rw [hu, hv]
      _ ≤ δ * m * h := this
      _ ≤ δ * ‖((k - s : ℝ) : ℂ) * v + ((s + h - k : ℝ) : ℂ) * u‖ := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hl hδ.le

/-- **Chords along a side.**  For small `h`, on any `[a, b] ⊆ [k, k + 1 - h]` (inside the side `k`)
the angle change of the chords `Γ (s + h) - Γ s` is within `ε` of the tangent turning
`ψ_k (b - k) - ψ_k (a - k)`. -/
theorem b2_hopf_side {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    {ψ : Fin n → ℝ → ℝ} (hψ : ∀ j, b2_IsAngleFn (deriv (c j)) 0 1 (ψ j)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ (k : ℤ) (a b : ℝ), (k : ℝ) ≤ a → a ≤ b → b + h ≤ k + 1 →
      ∀ Φ : ℝ → ℝ, b2_IsAngleFn (fun s => b2_loop c (s + h) - b2_loop c s) a b Φ →
      |(Φ b - Φ a) - (ψ (k : Fin n) (b - k) - ψ (k : Fin n) (a - k))| ≤ ε := by
  obtain ⟨M, hM, hMle⟩ := b2_derivWithin_lower hc
  obtain ⟨δ, hδ, happ⟩ := b2_angleFn_approx hε
  obtain ⟨η, hη, hch⟩ := b2_chord_uniform hc (mul_pos hδ hM)
  filter_upwards [Ioo_mem_nhdsGT hη] with h hh k a b hka hab hbk Φ hΦ
  set j : Fin n := (k : Fin n) with hj
  have hψs : b2_IsAngleFn (fun s => deriv (c j) (s - k)) a b (fun s => ψ j (s - k)) := by
    have := b2_angleFn_shift (hψ j) (k : ℝ)
    rw [zero_add] at this
    exact b2_angleFn_mono this hka (by linarith [hh.1])
  have hconst : b2_IsAngleFn (fun _ => (h : ℂ)) a b (fun _ => 0) := by
    refine ⟨continuousOn_const, fun _ _ => ?_⟩
    rw [Complex.norm_real, Real.norm_of_nonneg hh.1.le]
    simp
  have hmod := b2_angleFn_mul hconst hψs
  have := happ hab hΦ hmod (fun s hs => ?_)
  · simpa using this
  have hs01 : s - k ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2, hh.1]⟩
  have hder : deriv (c j) (s - k) = derivWithin (c j) (Icc 0 1) (s - k) :=
    (derivWithin_of_mem_nhds (Icc_mem_nhds hs01.1 hs01.2)).symm
  have hlow := hMle j (s - k) (Ioo_subset_Icc_self hs01)
  have hnorm : ‖(h : ℂ) * deriv (c j) (s - k)‖ = h * ‖derivWithin (c j) (Icc 0 1) (s - k)‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh.1.le, hder]
  refine ⟨?_, ?_⟩
  · refine mul_ne_zero (by exact_mod_cast hh.1.ne') ?_
    rw [hder]; exact hc.2.1 j _ (Ioo_subset_Icc_self hs01)
  · have := hch k s s (s + h) (by linarith [hs.1]) le_rfl (by linarith [hh.1])
      (by linarith [hs.2]) (by linarith [hh.2])
    rw [show s + h - s = h by ring] at this
    rw [hnorm, hder]
    calc ‖b2_loop c (s + h) - b2_loop c s - (h : ℂ) * derivWithin (c j) (Icc 0 1) (s - k)‖
        ≤ δ * M * h := this
      _ ≤ δ * (h * ‖derivWithin (c j) (Icc 0 1) (s - k)‖) := by
        rw [mul_assoc, mul_comm M h]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlow hh.1.le) hδ.le

/-- Summing over `n` consecutive integers read modulo `n` is summing over `Fin n`. -/
theorem b2_sum_reindex {n : ℕ} [NeZero n] (G : Fin n → ℝ) (a : ℤ) {N : ℕ} (hN : N = n) :
    ∑ i ∈ Finset.range N, G ((a + i : ℤ) : Fin n) = ∑ j, G j := by
  rw [hN, ← Fin.sum_univ_eq_sum_range (fun i => G ((a + i : ℤ) : Fin n)) n]
  have e : ∀ i : Fin n, (((a + ((i : ℕ) : ℤ)) : ℤ) : Fin n) = (a : Fin n) + i := by
    intro i
    push_cast
    simp
  simp_rw [e]
  exact Equiv.sum_comp (Equiv.addLeft (a : Fin n)) G

/-- Termwise closeness of two finite sums. -/
theorem b2_sum_close {N : ℕ} {a b : ℕ → ℝ} {e : ℝ} (h : ∀ i ∈ Finset.range N, |a i - b i| ≤ e) :
    |∑ i ∈ Finset.range N, a i - ∑ i ∈ Finset.range N, b i| ≤ N * e := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum h).trans ?_
  simp

/-- A function continuous on `[a, b]`, evaluated along a map `g` that tends to a point `x` of
`[a, b]` inside `[a, b]` as `h → 0⁺`, is eventually within `ε` of its value at `x`. -/
theorem b2_ev_cont {θ g : ℝ → ℝ} {a b x : ℝ} (hθ : ContinuousOn θ (Icc a b)) (hx : x ∈ Icc a b)
    (hg : Tendsto g (𝓝[>] 0) (𝓝 x)) (hgm : ∀ᶠ h in 𝓝[>] (0 : ℝ), g h ∈ Icc a b) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ h in 𝓝[>] (0 : ℝ), |θ (g h) - θ x| ≤ ε := by
  have hT : Tendsto (fun h => θ (g h)) (𝓝[>] 0) (𝓝 (θ x)) :=
    (hθ x hx).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hg, hgm⟩)
  filter_upwards [Metric.tendsto_nhds.1 hT ε hε] with h hh
  rw [Real.dist_eq] at hh
  exact hh.le

/-- **Hopf's Umlaufsatz** (orientation free).  For a corner loop and a smooth base point `Γ x₀`,
the total tangent turning (along the sides plus the exterior angles at the vertices) is twice the
boundary winding angle seen from the base point.  Proof: the angle change of the short chords
`Γ (s + h) - Γ s` is the sum over the two legs of the secant triangle (`b2_hopf_triangle`); as `h → 0`
it tends to the tangent turning (`b2_hopf_corner`, `b2_hopf_side`). -/
theorem b2_hopf_loop {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c) (x₀ : ℝ)
    (hx₀ : Int.fract x₀ ≠ 0)
    {Λ : ℝ → ℝ} (hΛ : b2_IsAngleFn (fun t => b2_loop c t - b2_loop c x₀) x₀ (x₀ + n) Λ)
    {ψ : Fin n → ℝ → ℝ} (hψ : ∀ j, b2_IsAngleFn (deriv (c j)) 0 1 (ψ j)) :
    ∑ j, (ψ j 1 - ψ j 0) + ∑ k, b2_extAngle c k = 2 * (Λ (x₀ + n) - Λ x₀) := by
  suffices hsuff : ∀ ε > 0,
      |∑ j, (ψ j 1 - ψ j 0) + ∑ k, b2_extAngle c k - 2 * (Λ (x₀ + n) - Λ x₀)| ≤ ε by
    by_contra hne
    have hpos := abs_pos.2 (sub_ne_zero.2 hne)
    have := hsuff _ (half_pos hpos)
    linarith
  intro ε hε
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  have hnR : (n : ℝ) = n' + 1 := by rw [hn']; push_cast; ring
  set ε' : ℝ := ε / (3 * n' + 7) with hε'def
  have hε' : 0 < ε' := div_pos hε (by positivity)
  have hεeq : ε = 3 * (n' * ε') + 7 * ε' := by rw [hε'def]; field_simp
  set k₀ : ℤ := ⌊x₀⌋ with hk₀
  set f : ℝ := Int.fract x₀ with hfdef
  have hf0 : 0 < f := lt_of_le_of_ne (Int.fract_nonneg x₀) (Ne.symm hx₀)
  have hf1 : f < 1 := Int.fract_lt_one x₀
  have hx₀eq : x₀ = k₀ + f := (Int.floor_add_fract x₀).symm
  set j₀ : Fin n := (k₀ : Fin n) with hj₀
  have hn1 : (1 : ℝ) ≤ n := by rw [hnR]; linarith [(Nat.cast_nonneg n' : (0 : ℝ) ≤ n')]
  -- the eventual estimates, as `h → 0⁺`
  have E1 : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.range (n' + 1), ∀ Φ : ℝ → ℝ,
      b2_IsAngleFn (fun s => b2_loop c (s + h) - b2_loop c s)
        (((k₀ + 1 + i : ℤ) : ℝ) - h) ((k₀ + 1 + i : ℤ) : ℝ) Φ →
      |(Φ ((k₀ + 1 + i : ℤ) : ℝ) - Φ (((k₀ + 1 + i : ℤ) : ℝ) - h)) -
        b2_extAngle c ((k₀ + 1 + i : ℤ) : Fin n)| ≤ ε' :=
    (Filter.eventually_all_finset _).2 (fun i _ => b2_hopf_corner hc (k₀ + 1 + i) hε')
  have E2 := b2_hopf_side hc hψ hε'
  have hsmall : ∀ {r : ℝ}, 0 < r → ∀ᶠ h in 𝓝[>] (0 : ℝ), h ∈ Ioo 0 r := fun hr => Ioo_mem_nhdsGT hr
  have E3 : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ j, |ψ j (1 - h) - ψ j 1| ≤ ε' := by
    refine Filter.eventually_all.2 (fun j => b2_ev_cont (hψ j).1 ⟨zero_le_one, le_rfl⟩ ?_ ?_ hε')
    · exact ((continuous_const.sub continuous_id).tendsto' 0 1 (by simp)).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [hsmall one_pos] with h hh
      exact ⟨by linarith [hh.2], by linarith [hh.1]⟩
  have E4 : ∀ᶠ h in 𝓝[>] (0 : ℝ), |ψ j₀ (f - h) - ψ j₀ f| ≤ ε' := by
    refine b2_ev_cont (hψ j₀).1 ⟨hf0.le, hf1.le⟩ ?_ ?_ hε'
    · exact ((continuous_const.sub continuous_id).tendsto' 0 f (by simp [hfdef])).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [hsmall hf0] with h hh
      exact ⟨by linarith [hh.2], by linarith [hh.1]⟩
  have E5 : ∀ᶠ h in 𝓝[>] (0 : ℝ), |Λ (x₀ + h) - Λ x₀| ≤ ε' := by
    refine b2_ev_cont hΛ.1 ⟨le_rfl, by linarith⟩ ?_ ?_ hε'
    · exact ((continuous_const.add continuous_id).tendsto' 0 x₀ (by simp)).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [hsmall one_pos] with h hh
      exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have E6 : ∀ᶠ h in 𝓝[>] (0 : ℝ), |Λ (x₀ + n - h) - Λ (x₀ + n)| ≤ ε' := by
    refine b2_ev_cont hΛ.1 ⟨by linarith, le_rfl⟩ ?_ ?_ hε'
    · exact ((continuous_const.sub continuous_id).tendsto' 0 (x₀ + n) (by simp)).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [hsmall one_pos] with h hh
      exact ⟨by linarith [hh.2], by linarith [hh.1]⟩
  have E7 := hsmall (lt_min hf0 (by linarith : 0 < 1 - f))
  obtain ⟨h, hE1, hE2, hE3, hE4, hE5, hE6, hE7⟩ :=
    (E1.and (E2.and (E3.and (E4.and (E5.and (E6.and E7)))))).exists
  have hh0 : 0 < h := hE7.1
  have hhf : h < f := lt_of_lt_of_le hE7.2 (min_le_left _ _)
  have hhf' : h < 1 - f := lt_of_lt_of_le hE7.2 (min_le_right _ _)
  -- the triangle identity for this `h`
  obtain ⟨Φ, hΦ, hΦeq⟩ := b2_hopf_triangle hc x₀ hx₀ hΛ hh0 (by linarith)
  -- the partition points `k₀ + 1 + i - h ≤ k₀ + 1 + i`, `i ≤ n'`
  have hQ : ∀ i : ℕ, ((k₀ + 1 + i : ℤ) : ℝ) = k₀ + 1 + i := fun i => by push_cast; ring
  have hmono : ∀ {a b : ℝ}, x₀ ≤ a → b ≤ x₀ + n - h →
      b2_IsAngleFn (fun s => b2_loop c (s + h) - b2_loop c s) a b Φ :=
    fun ha hb => b2_angleFn_mono hΦ ha hb
  -- corners
  have hC : |∑ i ∈ Finset.range (n' + 1),
      (Φ ((k₀ + 1 + i : ℤ) : ℝ) - Φ (((k₀ + 1 + i : ℤ) : ℝ) - h)) -
      ∑ i ∈ Finset.range (n' + 1), b2_extAngle c ((k₀ + 1 + i : ℤ) : Fin n)| ≤
      ((n' + 1 : ℕ) : ℝ) * ε' := by
    refine b2_sum_close (fun i hi => hE1 i hi Φ (hmono ?_ ?_))
    · rw [hQ, hx₀eq]; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    · have hi' : (i : ℝ) ≤ n' := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [hQ, hx₀eq, hnR]; linarith
  -- regular sides
  have hS : |∑ i ∈ Finset.range n',
      (Φ (((k₀ + 1 + (i + 1 : ℕ) : ℤ) : ℝ) - h) - Φ ((k₀ + 1 + i : ℤ) : ℝ)) -
      ∑ i ∈ Finset.range n', (ψ ((k₀ + 1 + i : ℤ) : Fin n) (1 - h) -
        ψ ((k₀ + 1 + i : ℤ) : Fin n) 0)| ≤ (n' : ℝ) * ε' := by
    refine b2_sum_close (fun i hi => ?_)
    have hi' : (i : ℝ) + 1 ≤ n' := by exact_mod_cast Finset.mem_range.1 hi
    have hQ1 : ((k₀ + 1 + (i + 1 : ℕ) : ℤ) : ℝ) = ((k₀ + 1 + i : ℤ) : ℝ) + 1 := by
      rw [hQ, hQ]; push_cast; ring
    have := hE2 (k₀ + 1 + i) ((k₀ + 1 + i : ℤ) : ℝ) (((k₀ + 1 + (i + 1 : ℕ) : ℤ) : ℝ) - h) le_rfl
      (by rw [hQ1]; linarith) (by rw [hQ1]; linarith) Φ (hmono ?_ ?_)
    · rwa [show ((k₀ + 1 + (i + 1 : ℕ) : ℤ) : ℝ) - h - ((k₀ + 1 + i : ℤ) : ℝ) = 1 - h by
        rw [hQ1]; ring, sub_self] at this
    · rw [hQ, hx₀eq]; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    · rw [hQ1, hQ, hx₀eq, hnR]; linarith
  have hS2 : |∑ i ∈ Finset.range n', (ψ ((k₀ + 1 + i : ℤ) : Fin n) (1 - h) -
        ψ ((k₀ + 1 + i : ℤ) : Fin n) 0) -
      ∑ i ∈ Finset.range n', (ψ ((k₀ + 1 + i : ℤ) : Fin n) 1 -
        ψ ((k₀ + 1 + i : ℤ) : Fin n) 0)| ≤ (n' : ℝ) * ε' := by
    refine b2_sum_close (fun i _ => ?_)
    have := hE3 ((k₀ + 1 + i : ℤ) : Fin n)
    rwa [show ψ ((k₀ + 1 + i : ℤ) : Fin n) (1 - h) - ψ ((k₀ + 1 + i : ℤ) : Fin n) 0 -
      (ψ ((k₀ + 1 + i : ℤ) : Fin n) 1 - ψ ((k₀ + 1 + i : ℤ) : Fin n) 0) =
      ψ ((k₀ + 1 + i : ℤ) : Fin n) (1 - h) - ψ ((k₀ + 1 + i : ℤ) : Fin n) 1 by ring]
  -- the side through the base point: its two pieces
  have hQ0 : ((k₀ + 1 + ((0 : ℕ) : ℤ) : ℤ) : ℝ) = k₀ + 1 := by rw [hQ]; push_cast; ring
  have hp₀ : |(Φ (((k₀ + 1 + ((0 : ℕ) : ℤ) : ℤ) : ℝ) - h) - Φ x₀) - (ψ j₀ (1 - h) - ψ j₀ f)| ≤
      ε' := by
    have := hE2 k₀ x₀ (((k₀ + 1 + ((0 : ℕ) : ℤ) : ℤ) : ℝ) - h) (Int.floor_le x₀)
      (by rw [hQ0, hx₀eq]; linarith) (by rw [hQ0]; linarith) Φ (hmono le_rfl ?_)
    · rwa [show ((k₀ + 1 + ((0 : ℕ) : ℤ) : ℤ) : ℝ) - h - k₀ = 1 - h by rw [hQ0]; ring,
        show x₀ - k₀ = f by rw [hx₀eq]; ring] at this
    · rw [hQ0, hx₀eq, hnR]; linarith [(Nat.cast_nonneg n' : (0 : ℝ) ≤ n')]
  have hidx : (((k₀ + 1 + n' : ℤ)) : Fin n) = j₀ := by
    rw [hj₀, show (k₀ + 1 + n' : ℤ) = k₀ + (n : ℤ) by rw [hn']; push_cast; ring, Int.cast_add,
      Int.cast_natCast, Fin.natCast_self, add_zero]
  have hQn : ((k₀ + 1 + n' : ℤ) : ℝ) = k₀ + n := by rw [hQ, hnR]; ring
  have hp₁ : |(Φ (x₀ + n - h) - Φ ((k₀ + 1 + n' : ℤ) : ℝ)) - (ψ j₀ (f - h) - ψ j₀ 0)| ≤ ε' := by
    have := hE2 (k₀ + 1 + n') ((k₀ + 1 + n' : ℤ) : ℝ) (x₀ + n - h) le_rfl
      (by rw [hQn, hx₀eq]; linarith) (by rw [hQn, hx₀eq]; linarith) Φ
      (hmono (by rw [hQn, hx₀eq]; linarith) le_rfl)
    rwa [hidx, show x₀ + n - h - ((k₀ + 1 + n' : ℤ) : ℝ) = f - h by rw [hQn, hx₀eq]; ring,
      sub_self] at this
  -- telescoping of the chord angle along the partition
  have htel : Φ (x₀ + n - h) - Φ x₀ = (Φ (((k₀ + 1 + ((0 : ℕ) : ℤ) : ℤ) : ℝ) - h) - Φ x₀) +
      ∑ i ∈ Finset.range (n' + 1), (Φ ((k₀ + 1 + i : ℤ) : ℝ) - Φ (((k₀ + 1 + i : ℤ) : ℝ) - h)) +
      ∑ i ∈ Finset.range n', (Φ (((k₀ + 1 + (i + 1 : ℕ) : ℤ) : ℝ) - h) - Φ ((k₀ + 1 + i : ℤ) : ℝ)) +
      (Φ (x₀ + n - h) - Φ ((k₀ + 1 + n' : ℤ) : ℝ)) := by
    have t2 : ∑ i ∈ Finset.range n', (Φ ((k₀ + 1 + i : ℤ) : ℝ) - Φ (((k₀ + 1 + i : ℤ) : ℝ) - h)) +
        ∑ i ∈ Finset.range n',
          (Φ (((k₀ + 1 + (i + 1 : ℕ) : ℤ) : ℝ) - h) - Φ ((k₀ + 1 + i : ℤ) : ℝ)) =
        Φ (((k₀ + 1 + n' : ℤ) : ℝ) - h) - Φ (((k₀ + 1 + ((0 : ℕ) : ℤ) : ℤ) : ℝ) - h) := by
      rw [← Finset.sum_add_distrib,
        ← Finset.sum_range_sub (fun i : ℕ => Φ (((k₀ + 1 + i : ℤ) : ℝ) - h))]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [Finset.sum_range_succ]
    linarith
  -- reindexing the target sums
  have hext : ∑ k, b2_extAngle c k =
      ∑ i ∈ Finset.range (n' + 1), b2_extAngle c ((k₀ + 1 + i : ℤ) : Fin n) :=
    (b2_sum_reindex (b2_extAngle c) (k₀ + 1) hn'.symm).symm
  have hpsi : ∑ j, (ψ j 1 - ψ j 0) = (ψ j₀ 1 - ψ j₀ 0) +
      ∑ i ∈ Finset.range n', (ψ ((k₀ + 1 + i : ℤ) : Fin n) 1 - ψ ((k₀ + 1 + i : ℤ) : Fin n) 0) := by
    rw [← b2_sum_reindex (fun j => ψ j 1 - ψ j 0) k₀ hn'.symm, Finset.sum_range_succ', add_comm]
    congr 1
    · simp [hj₀]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [show (k₀ + ((i + 1 : ℕ) : ℤ) : ℤ) = k₀ + 1 + i by push_cast; ring]
  -- collect the errors
  have hn'1 : (((n' + 1 : ℕ) : ℝ)) * ε' = n' * ε' + ε' := by push_cast; ring
  rw [hn'1] at hC
  rw [hext, hpsi]
  have a1 := abs_le.1 hC
  have a2 := abs_le.1 hS
  have a3 := abs_le.1 hS2
  have a4 := abs_le.1 hp₀
  have a5 := abs_le.1 hp₁
  have a6 := abs_le.1 (hE3 j₀)
  have a7 := abs_le.1 hE4
  have a8 := abs_le.1 hE5
  have a9 := abs_le.1 hE6
  rw [abs_le]
  constructor <;> linarith

end Loop

/-! ## Public per-side results (glue, proved from the stubs above) -/

/-- **Winding number one.**  The positively oriented boundary of `dom` winds once around every
interior point: the per-side angle changes of `c_j - p` add up to `2π`. -/
theorem b2_wind_in {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    {dom : Set ℂ} (hD : b2_IsPosBoundary c dom) {p : ℂ} (hp : p ∈ dom)
    {L : Fin n → ℝ → ℝ} (hL : ∀ j, b2_IsAngleFn (fun t => c j t - p) 0 1 (L j)) :
    ∑ j, (L j 1 - L j 0) = 2 * π := by
  obtain ⟨hdo, -, -, -, hfr, -⟩ := id hD
  have hpR : p ∉ range (b2_loop c) := by
    rw [b2_loop_range hc, ← hfr, hdo.frontier_eq]
    exact fun h => h.2 hp
  obtain ⟨Λ, hΛ⟩ := b2_exists_angleFn_loop hc ((0 : ℤ) : ℝ) (Or.inr hpR)
  rw [b2_angle_sum_eq hc 0 (fun t _ h => hpR ⟨t, h⟩) hL hΛ]
  exact b2_wind_loop_in hc hD hp _ hΛ

/-- **Winding number zero** around exterior points. -/
theorem b2_wind_out {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    {dom : Set ℂ} (hD : b2_IsPosBoundary c dom) {p : ℂ} (hp : p ∉ closure dom)
    {L : Fin n → ℝ → ℝ} (hL : ∀ j, b2_IsAngleFn (fun t => c j t - p) 0 1 (L j)) :
    ∑ j, (L j 1 - L j 0) = 0 := by
  obtain ⟨-, -, -, -, hfr, -⟩ := id hD
  have hpR : p ∉ range (b2_loop c) := by
    rw [b2_loop_range hc, ← hfr]
    exact fun h => hp (frontier_subset_closure h)
  obtain ⟨Λ, hΛ⟩ := b2_exists_angleFn_loop hc ((0 : ℤ) : ℝ) (Or.inr hpR)
  rw [b2_angle_sum_eq hc 0 (fun t _ h => hpR ⟨t, h⟩) hL hΛ]
  exact b2_wind_loop_out hc hD hp _ hΛ

/-- **Boundary winding angle at a vertex.**  Seen from the vertex `c k 0`, the positively oriented
boundary turns by the interior angle `π - b2_extAngle c k`. -/
theorem b2_bwa {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    {dom : Set ℂ} (hD : b2_IsPosBoundary c dom) (k : Fin n)
    {L : Fin n → ℝ → ℝ} (hL : ∀ j, b2_IsAngleFn (fun t => c j t - c k 0) 0 1 (L j)) :
    ∑ j, (L j 1 - L j 0) = π - b2_extAngle c k := by
  open Fin.CommRing in
  have hk : ((((k : ℕ) : ℤ)) : Fin n) = k := by simp
  have hq : c k 0 = b2_loop c (((k : ℕ) : ℤ) : ℝ) := by
    have := b2_loop_apply hc ((k : ℕ) : ℤ) (t := 0) ⟨le_rfl, zero_le_one⟩
    rw [add_zero, hk] at this
    exact this.symm
  obtain ⟨Λ, hΛ⟩ := b2_exists_angleFn_loop hc ((((k : ℕ) : ℤ)) : ℝ) (Or.inl hq)
  have hne : ∀ t ∈ Ioo ((((k : ℕ) : ℤ)) : ℝ) ((((k : ℕ) : ℤ)) + n), b2_loop c t ≠ c k 0 := by
    intro t ht h
    rw [hq, b2_loop_eq_iff hc] at h
    obtain ⟨m, hm⟩ := h
    generalize ((((k : ℕ) : ℤ)) : ℝ) = K at ht hm
    have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
    have h1 : (0 : ℝ) < -(m : ℝ) * n := by linarith [ht.1]
    have h2 : -(m : ℝ) * n < n := by linarith [ht.2]
    have hm0 : (0 : ℝ) < -(m : ℝ) := pos_of_mul_pos_left h1 hn.le
    have hm1 : -(m : ℝ) < 1 := by nlinarith
    have hm0' : (0 : ℤ) < -m := by exact_mod_cast hm0
    have hm1' : -m < (1 : ℤ) := by exact_mod_cast hm1
    omega
  rw [b2_angle_sum_eq hc (((k : ℕ) : ℤ)) hne hL hΛ]
  rw [hq] at hΛ
  rw [b2_bwa_loop hc hD _ hΛ, b2_tanR_int, b2_tanL_int, hk]
  rfl

/-- **Umlaufsatz** (Hopf).  For a positively oriented corner loop the tangent turning along the sides
plus the exterior angles at the vertices is `2π`. -/
theorem b2_umlaufsatz {n : ℕ} [NeZero n] {c : Fin n → ℝ → ℂ} (hc : b2_IsCornerLoop c)
    {dom : Set ℂ} (hD : b2_IsPosBoundary c dom)
    {ψ : Fin n → ℝ → ℝ} (hψ : ∀ j, b2_IsAngleFn (deriv (c j)) 0 1 (ψ j)) :
    ∑ j, (ψ j 1 - ψ j 0) = 2 * π - ∑ k, b2_extAngle c k := by
  have hx : Int.fract (1 / 2 : ℝ) ≠ 0 := by
    rw [Int.fract_eq_self.2 ⟨by norm_num, by norm_num⟩]; norm_num
  obtain ⟨Λ, hΛ⟩ := b2_exists_angleFn_loop hc (1 / 2) (Or.inl rfl)
  have hH := b2_hopf_loop hc (1 / 2) hx hΛ hψ
  have hB := b2_bwa_loop hc hD (1 / 2) hΛ
  obtain ⟨hLR, -⟩ := b2_tan_of_fract_ne_zero c hx
  have hR := (b2_tan_ne_zero hc (1 / 2)).1
  rw [hLR, div_self hR, arg_one, sub_zero] at hB
  rw [hB] at hH
  linarith

end LiZhongQC
