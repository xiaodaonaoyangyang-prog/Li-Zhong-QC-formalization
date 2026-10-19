import LiZhongQC.Lemmas.FoundationQuotient

/-! F1 B2a + B2b: subdivision of the central orbit circle into positively oriented `Circle.path` arcs,
and selection of the exposed arcs.

B2a: the vertex angles are the principal arguments of the cut points together with the two auxiliary
angles `0` and `π`; they are sorted, closed up by `+ 2π`, and each consecutive pair gives one arc.
B2b: an arc is selected when its midpoint is a frontier point. Frontier membership is constant on arc
interiors (intermediate value theorem), and a frontier vertex is never isolated (internal tangency of
two equal-radius hyperbolic circles is impossible). Headers of the two endpoints are byte-identical to
the frozen sub-interface F1BGraphIface_v1 (9195066a). -/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section
namespace LiZhongQC

/-- A positively traversed short angular interval gives the existing Circle.path,
even when the interval crosses the branch cut of the principal argument. -/
theorem ft1gb_circle_path_lift {α β : ℝ} (hab : α < β) (hlen : β - α < 2 * Real.pi)
    (t : unitInterval) :
    Circle.path (Circle.exp α) (Circle.exp β) t =
      Circle.exp (α + (β - α) * (t : ℝ)) := by
  have hexp : Circle.exp (Circle.angleDiff (Circle.exp α) (Circle.exp β)) =
      Circle.exp (β - α) := by
    have hprod : Circle.exp (Circle.angleDiff (Circle.exp α) (Circle.exp β)) * Circle.exp α =
        Circle.exp (β - α) * Circle.exp α := by
      rw [Circle.exp_angleDiff_mul, ← Circle.exp_add, sub_add_cancel]
    exact mul_right_cancel hprod
  have hangle : Circle.angleDiff (Circle.exp α) (Circle.exp β) = β - α :=
    Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by linarith)
      ⟨Circle.angleDiff_nonneg _ _, Circle.angleDiff_lt_two_pi _ _⟩
      ⟨(sub_pos.2 hab).le, hlen⟩ hexp
  calc
    Circle.path (Circle.exp α) (Circle.exp β) t =
        Circle.exp ((β - α) * (t : ℝ) + Complex.arg (Circle.exp α : ℂ)) := by
      rw [Circle.path_apply, Path.segment_apply, AffineMap.lineMap_apply_module, hangle]
      congr 1
      simp only [smul_eq_mul]
      ring
    _ = Circle.exp ((β - α) * (t : ℝ)) * Circle.exp α := by
      rw [Circle.exp_add, Circle.exp_arg]
    _ = Circle.exp (α + (β - α) * (t : ℝ)) := by
      rw [← Circle.exp_add]
      congr 1
      ring

/-- Consecutive closed intervals of a strictly increasing finite list cover the
interval from its first to its last entry. The witness is the last vertex below x. -/
theorem ft1gb_ordered_intervals_cover (n : ℕ) (hn : 0 < n)
    (θ : Fin (n + 1) → ℝ) (hθ : StrictMono θ) {x : ℝ}
    (hx : θ 0 ≤ x ∧ x ≤ θ (Fin.last n)) :
    ∃ i : Fin n, θ i.castSucc ≤ x ∧ x ≤ θ i.succ := by
  classical
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun j => θ j ≤ x)
  have hS : S.Nonempty := ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx.1⟩⟩
  let j : Fin (n + 1) := S.max' hS
  have hjS : j ∈ S := Finset.max'_mem S hS
  have hjx : θ j ≤ x := (Finset.mem_filter.1 hjS).2
  by_cases hlast : j = Fin.last n
  · let i : Fin n := ⟨n - 1, by omega⟩
    have hisucc : i.succ = Fin.last n := by apply Fin.ext; dsimp [i]; omega
    refine ⟨i, ?_, ?_⟩
    · have hle : θ i.castSucc ≤ θ (Fin.last n) := hθ.monotone (Fin.le_last _)
      rw [hlast] at hjx
      exact hle.trans hjx
    · rw [hisucc]
      exact hx.2
  · have hjn : (j : ℕ) < n := by
      by_contra h
      apply hlast
      apply Fin.ext
      have hjbound := j.isLt
      change (j : ℕ) = n
      omega
    let i : Fin n := ⟨j, hjn⟩
    have hicast : i.castSucc = j := by apply Fin.ext; rfl
    refine ⟨i, hicast ▸ hjx, ?_⟩
    by_contra h
    have hiS : i.succ ∈ S :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, (lt_of_not_ge h).le⟩
    have hle : i.succ ≤ j := Finset.le_max' S _ hiS
    have hval : (i : ℕ) + 1 ≤ (j : ℕ) := hle
    change (j : ℕ) + 1 ≤ (j : ℕ) at hval
    omega

/-- Every angle is congruent to a point of one of the closed arcs `[Θ i, Θ (i+1)]` of a
strictly increasing vertex list closed up by one full turn. -/
theorem ft1gb_angle_cover {m : ℕ} (Θ : Fin (m + 1) → ℝ) (hΘ : StrictMono Θ)
    (hper : Θ (Fin.last m) = Θ 0 + 2 * Real.pi) (hm : 0 < m) (x : ℝ) :
    ∃ (i : Fin m) (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧
      Circle.exp (Θ i.castSucc + (Θ i.succ - Θ i.castSucc) * t) = Circle.exp x := by
  have hp : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  set y := toIcoMod hp (Θ 0) x with hydef
  have hy := toIcoMod_mem_Ico hp (Θ 0) x
  rw [← hydef] at hy
  have hey : Circle.exp y = Circle.exp x := by
    rw [Circle.exp_eq_exp]
    refine ⟨-toIcoDiv hp (Θ 0) x, ?_⟩
    have h := toIcoMod_sub_self hp (Θ 0) x
    rw [← hydef, zsmul_eq_mul] at h
    push_cast at h ⊢
    linarith
  obtain ⟨i, h1, h2⟩ := ft1gb_ordered_intervals_cover m hm Θ hΘ ⟨hy.1, by rw [hper]; exact hy.2.le⟩
  have hΔ : 0 < Θ i.succ - Θ i.castSucc := sub_pos.2 (hΘ ((show i.castSucc < i.succ from Fin.castSucc_lt_succ)))
  refine ⟨i, (y - Θ i.castSucc) / (Θ i.succ - Θ i.castSucc), div_nonneg (by linarith) hΔ.le,
    (div_le_one hΔ).2 (by linarith), ?_⟩
  rw [mul_div_cancel₀ _ hΔ.ne', add_sub_cancel, hey]

/-- Interior points of the arcs of a closed-up strictly increasing vertex list are
represented exactly once, even against arc endpoints. -/
theorem ft1gb_angle_sep {m : ℕ} (Θ : Fin (m + 1) → ℝ) (hΘ : StrictMono Θ)
    (hper : Θ (Fin.last m) = Θ 0 + 2 * Real.pi) (i j : Fin m) (t s : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (heq : Circle.exp (Θ i.castSucc + (Θ i.succ - Θ i.castSucc) * t) =
      Circle.exp (Θ j.castSucc + (Θ j.succ - Θ j.castSucc) * s)) :
    i = j ∧ t = s := by
  have hΔi : 0 < Θ i.succ - Θ i.castSucc := sub_pos.2 (hΘ ((show i.castSucc < i.succ from Fin.castSucc_lt_succ)))
  have hΔj : 0 < Θ j.succ - Θ j.castSucc := sub_pos.2 (hΘ ((show j.castSucc < j.succ from Fin.castSucc_lt_succ)))
  set x := Θ i.castSucc + (Θ i.succ - Θ i.castSucc) * t with hx
  set y := Θ j.castSucc + (Θ j.succ - Θ j.castSucc) * s with hy
  have hxa : Θ i.castSucc < x := by rw [hx]; nlinarith
  have hxb : x < Θ i.succ := by rw [hx]; nlinarith
  have hya : Θ j.castSucc ≤ y := by rw [hy]; nlinarith
  have hyb : y ≤ Θ j.succ := by rw [hy]; nlinarith
  have hi0 : Θ 0 ≤ Θ i.castSucc := hΘ.monotone (Fin.zero_le _)
  have hil : Θ i.succ ≤ Θ (Fin.last m) := hΘ.monotone (Fin.le_last _)
  have hj0 : Θ 0 ≤ Θ j.castSucc := hΘ.monotone (Fin.zero_le _)
  have hjl : Θ j.succ ≤ Θ (Fin.last m) := hΘ.monotone (Fin.le_last _)
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.1 heq
  have hpi := Real.pi_pos
  have hk1 : (k : ℝ) < 1 := by nlinarith
  have hk2 : (-1 : ℝ) < k := by nlinarith
  have hk1' : k < 1 := by exact_mod_cast hk1
  have hk2' : -1 < k := by exact_mod_cast hk2
  have hk0 : k = 0 := by omega
  rw [hk0, Int.cast_zero, zero_mul, add_zero] at hk
  have hij : i = j := by
    rcases lt_trichotomy i j with h | h | h
    · have hle : i.succ ≤ j.castSucc := Fin.le_iff_val_le_val.2 (by
        simp only [Fin.val_succ, Fin.val_castSucc]
        exact h)
      have := hΘ.monotone hle
      linarith
    · exact h
    · have hle : j.succ ≤ i.castSucc := Fin.le_iff_val_le_val.2 (by
        simp only [Fin.val_succ, Fin.val_castSucc]
        exact h)
      have := hΘ.monotone hle
      linarith
  subst hij
  refine ⟨rfl, ?_⟩
  have h := hk
  rw [hx, hy] at h
  have h' : (Θ i.succ - Θ i.castSucc) * t = (Θ i.succ - Θ i.castSucc) * s := by linarith
  exact mul_left_cancel₀ hΔi.ne' h'

/-- B2a. Subdivide the actual central circle into at least two positively oriented
embedded Circle.path arcs. At most two auxiliary vertices are added to the supplied
finite cut set, so the whole-circle case is never represented by one interval.
This is a geometric construction, not an assumed graph. -/
theorem ft1gb_circle_subdivision (R : ℝ) (hR : 0 < R) (V : Finset UpperHalfPlane)
    (hV : ∀ p ∈ V, p ∈ sphere UpperHalfPlane.I R) :
    ∃ (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane),
      2 ≤ n ∧ n ≤ V.card + 2 ∧
      (∀ i, Topology.IsEmbedding (a i) ∧ Set.range (a i) ⊆ sphere UpperHalfPlane.I R ∧
      ∃ x y : Circle, x ≠ y ∧ ∀ t : unitInterval,
        (a i t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
          (Real.sinh R : ℂ) * (Circle.path x y t : ℂ)) ∧
      sphere UpperHalfPlane.I R = ⋃ i, Set.range (a i) ∧
      (∀ i j (t s : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
        a i t = a j s → i = j ∧ t = s) ∧
      (∀ i (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → a i t ∉ V) := by
  classical
  have _hV := hV
  set c : ℂ := (UpperHalfPlane.I.center R : ℂ) with hc
  set r : ℝ := Real.sinh R with hr
  have hr0 : 0 < r := Real.sinh_pos_iff.2 hR
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hcim : c.im = Real.cosh R := by
    rw [hc, UpperHalfPlane.coe_im, UpperHalfPlane.center_im, UpperHalfPlane.I_im, one_mul]
  have him : ∀ u : Circle, 0 < (c + (r : ℂ) * (u : ℂ)).im := by
    intro u
    have h1 : |(u : ℂ).im| ≤ 1 := by
      have := Complex.abs_im_le_norm (u : ℂ)
      rwa [Circle.norm_coe] at this
    have h2 : Real.sinh R < Real.cosh R := Real.sinh_lt_cosh R
    rw [Complex.add_im, Complex.im_ofReal_mul, hcim]
    nlinarith [abs_le.1 h1]
  let φ : Circle → UpperHalfPlane := fun u => ⟨c + (r : ℂ) * (u : ℂ), him u⟩
  have hcont0 : Continuous (fun u : Circle => c + (r : ℂ) * (u : ℂ)) :=
    continuous_const.add (continuous_const.mul continuous_subtype_val)
  have hφc : Continuous φ := UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff.2 hcont0
  have hφinj : Function.Injective φ := by
    intro u v h
    have h1 : c + (r : ℂ) * (u : ℂ) = c + (r : ℂ) * (v : ℂ) := by
      have h2 := congrArg (fun z : UpperHalfPlane => (z : ℂ)) h
      exact h2
    exact Circle.ext (mul_left_cancel₀ hrC (add_left_cancel h1))
  have hφsph : ∀ u, dist (φ u) UpperHalfPlane.I = R := by
    intro u
    rw [UpperHalfPlane.dist_eq_iff_dist_coe_center_eq, UpperHalfPlane.I_im, one_mul]
    show dist (c + (r : ℂ) * (u : ℂ)) c = r
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr0.le]
  have hφsurj : ∀ p : UpperHalfPlane, dist p UpperHalfPlane.I = R → ∃ u, φ u = p := by
    intro p hp
    rw [UpperHalfPlane.dist_eq_iff_dist_coe_center_eq, UpperHalfPlane.I_im, one_mul] at hp
    have hn : ‖((p : ℂ) - c) / (r : ℂ)‖ = 1 := by
      rw [norm_div, ← dist_eq_norm, hp, Complex.norm_real, Real.norm_of_nonneg hr0.le,
        div_self hr0.ne']
    refine ⟨⟨((p : ℂ) - c) / (r : ℂ), mem_sphere_zero_iff_norm.2 hn⟩, ?_⟩
    apply UpperHalfPlane.ext
    show c + (r : ℂ) * (((p : ℂ) - c) / (r : ℂ)) = p
    rw [mul_div_cancel₀ _ hrC]
    ring
  -- the vertex angles
  set f : UpperHalfPlane → ℝ := fun p => Complex.arg (((p : ℂ) - c) / (r : ℂ)) with hf
  set A : Finset ℝ := insert 0 (insert Real.pi (V.image f)) with hA
  have hAr : ∀ x ∈ A, -Real.pi < x ∧ x ≤ Real.pi := by
    intro x hx
    rw [hA, Finset.mem_insert, Finset.mem_insert, Finset.mem_image] at hx
    rcases hx with h | h | ⟨p, -, h⟩
    · rw [h]; exact ⟨by linarith [Real.pi_pos], Real.pi_pos.le⟩
    · rw [h]; exact ⟨by linarith [Real.pi_pos], le_rfl⟩
    · rw [← h]; exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have h0A : (0 : ℝ) ∈ A := Finset.mem_insert_self _ _
  have hπA : Real.pi ∈ A := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  set m := A.card with hm
  have hm2 : 2 ≤ m := by
    have hsub : ({0, Real.pi} : Finset ℝ) ⊆ A := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h
      · rw [h]; exact h0A
      · rw [h]; exact hπA
    have h2 : ({0, Real.pi} : Finset ℝ).card = 2 := Finset.card_pair Real.pi_pos.ne
    rw [← h2]
    exact Finset.card_le_card hsub
  have hmV : m ≤ V.card + 2 := by
    have h1 := Finset.card_insert_le (0 : ℝ) (insert Real.pi (V.image f))
    have h2 := Finset.card_insert_le Real.pi (V.image f)
    have h3 := Finset.card_image_le (s := V) (f := f)
    have h4 : A.card = (insert (0 : ℝ) (insert Real.pi (V.image f))).card := rfl
    omega
  have hm0 : 0 < m := by omega
  let θ : Fin m ↪o ℝ := A.orderEmbOfFin hm.symm
  have hθr : ∀ k, -Real.pi < θ k ∧ θ k ≤ Real.pi := fun k =>
    hAr _ (Finset.orderEmbOfFin_mem A hm.symm k)
  let Θ : Fin (m + 1) → ℝ := fun k =>
    if h : (k : ℕ) < m then θ ⟨k, h⟩ else θ ⟨0, hm0⟩ + 2 * Real.pi
  have hΘcs : ∀ k : Fin m, Θ k.castSucc = θ k := fun k => dif_pos k.isLt
  have hΘ0 : Θ 0 = θ ⟨0, hm0⟩ := dif_pos hm0
  have hΘl : Θ (Fin.last m) = Θ 0 + 2 * Real.pi := by
    rw [hΘ0]
    exact dif_neg (lt_irrefl m)
  have hΘ : StrictMono Θ := by
    refine Fin.strictMono_iff_lt_succ.2 fun k => ?_
    rw [hΘcs]
    by_cases hk : (k : ℕ) + 1 < m
    · have e2 : Θ k.succ = θ ⟨k + 1, hk⟩ := dif_pos hk
      rw [e2]
      exact θ.strictMono (Fin.mk_lt_mk.2 (by omega))
    · have e2 : Θ k.succ = θ ⟨0, hm0⟩ + 2 * Real.pi := dif_neg hk
      rw [e2]
      linarith [(hθr k).2, (hθr ⟨0, hm0⟩).1, Real.pi_pos]
  have hΔ : ∀ i : Fin m, 0 < Θ i.succ - Θ i.castSucc := fun i =>
    sub_pos.2 (hΘ ((show i.castSucc < i.succ from Fin.castSucc_lt_succ)))
  have hΔ2 : ∀ i : Fin m, Θ i.succ - Θ i.castSucc < 2 * Real.pi := by
    intro i
    have h0 : Θ 0 ≤ Θ i.castSucc := hΘ.monotone (Fin.zero_le _)
    have hl : Θ i.succ ≤ Θ (Fin.last m) := hΘ.monotone (Fin.le_last _)
    by_cases hi : (i : ℕ) = 0
    · have hlt : i.succ < Fin.last m := Fin.lt_def.2 (by
        simp only [Fin.val_succ, Fin.val_last]
        omega)
      have := hΘ hlt
      linarith
    · have hlt : (0 : Fin (m + 1)) < i.castSucc := Fin.lt_def.2 (by
        simp only [Fin.val_zero, Fin.val_castSucc]
        omega)
      have := hΘ hlt
      linarith
  have hne : ∀ i : Fin m, Circle.exp (Θ i.castSucc) ≠ Circle.exp (Θ i.succ) := by
    intro i h
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.1 h.symm
    have h1 := hΔ i
    have h2 := hΔ2 i
    have hpi := Real.pi_pos
    have hk1 : (k : ℝ) < 1 := by nlinarith
    have hk0 : (0 : ℝ) < k := by nlinarith
    have hk1' : k < 1 := by exact_mod_cast hk1
    have hk0' : 0 < k := by exact_mod_cast hk0
    omega
  have hlift : ∀ (i : Fin m) (t : unitInterval),
      Circle.path (Circle.exp (Θ i.castSucc)) (Circle.exp (Θ i.succ)) t =
        Circle.exp (Θ i.castSucc + (Θ i.succ - Θ i.castSucc) * (t : ℝ)) := fun i t =>
    ft1gb_circle_path_lift (hΘ ((show i.castSucc < i.succ from Fin.castSucc_lt_succ))) (hΔ2 i) t
  let a : Fin m → unitInterval → UpperHalfPlane := fun i t =>
    φ (Circle.path (Circle.exp (Θ i.castSucc)) (Circle.exp (Θ i.succ)) t)
  refine ⟨m, a, hm2, hmV, ?_, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_, ⟨Circle.exp (Θ i.castSucc), Circle.exp (Θ i.succ), hne i, fun t => rfl⟩⟩
    · exact ((hφc.comp (Circle.path _ _).continuous).isClosedEmbedding
        (hφinj.comp (Circle.path_injective_of_ne (hne i)))).isEmbedding
    · rintro _ ⟨t, rfl⟩
      exact hφsph _
  · ext p
    constructor
    · intro hp
      obtain ⟨u, rfl⟩ := hφsurj p hp
      obtain ⟨i, t, ht0, ht1, hexp⟩ := ft1gb_angle_cover Θ hΘ hΘl hm0 (Complex.arg (u : ℂ))
      refine mem_iUnion.2 ⟨i, ⟨⟨t, ht0, ht1⟩, ?_⟩⟩
      show φ (Circle.path (Circle.exp (Θ i.castSucc)) (Circle.exp (Θ i.succ)) ⟨t, ht0, ht1⟩) = φ u
      rw [hlift]
      exact congrArg φ (hexp.trans (Circle.exp_arg u))
    · intro hp
      obtain ⟨i, t, rfl⟩ := mem_iUnion.1 hp
      exact hφsph _
  · intro i j t s ht0 ht1 heq
    have h1 := hφinj heq
    rw [hlift, hlift] at h1
    obtain ⟨hij, hts⟩ := ft1gb_angle_sep Θ hΘ hΘl i j t s ht0 ht1 s.2.1 s.2.2 h1
    exact ⟨hij, Subtype.ext hts⟩
  · intro i t ht0 ht1 hV'
    have hmemA : f (a i t) ∈ A :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f hV'))
    have hcu : f (a i t) = Complex.arg
        ((Circle.path (Circle.exp (Θ i.castSucc)) (Circle.exp (Θ i.succ)) t : Circle) : ℂ) := by
      show Complex.arg (((c + (r : ℂ) * _) - c) / (r : ℂ)) = _
      rw [add_sub_cancel_left]
      congr 1
      field_simp
    rw [hcu] at hmemA
    have hrange : Set.range θ = (A : Set ℝ) := Finset.range_orderEmbOfFin A hm.symm
    obtain ⟨k, hk⟩ : Complex.arg
        ((Circle.path (Circle.exp (Θ i.castSucc)) (Circle.exp (Θ i.succ)) t : Circle) : ℂ) ∈
          Set.range θ := by
      rw [hrange]
      exact hmemA
    have he : Circle.exp (Θ k.castSucc + (Θ k.succ - Θ k.castSucc) * 0) =
        Circle.exp (Θ i.castSucc + (Θ i.succ - Θ i.castSucc) * (t : ℝ)) := by
      rw [mul_zero, add_zero, hΘcs, hk, Circle.exp_arg, hlift]
    obtain ⟨-, h⟩ := ft1gb_angle_sep Θ hΘ hΘl i k t 0 ht0 ht1 le_rfl zero_le_one he.symm
    linarith


variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- On the central sphere, frontier membership is the absence of a strictly closer orbit centre. -/
theorem ft1gb_sphere_frontier_iff {R : ℝ} {U : Set UpperHalfPlane}
    (hfront : frontier U = {p : UpperHalfPlane |
      (∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R) ∧
      ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I)})
    {q : UpperHalfPlane} (hq : q ∈ sphere UpperHalfPlane.I R) :
    q ∈ frontier U ↔ ∀ γ ∈ Γ, R ≤ dist q (γ • UpperHalfPlane.I) := by
  rw [hfront]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨⟨1, Γ.one_mem, ?_⟩, h⟩
    rw [one_smul]
    exact hq

/-- Along a sphere arc whose interior avoids the cut set, frontier membership of interior points is
constant (intermediate value theorem for the distance to each orbit centre). -/
theorem ft1gb_arc_interior_front {R : ℝ} {U : Set UpperHalfPlane}
    (hfront : frontier U = {p : UpperHalfPlane |
      (∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R) ∧
      ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I)})
    (V : Finset UpperHalfPlane) (hV : ∀ p : UpperHalfPlane, p ∈ V ↔ dist p UpperHalfPlane.I = R ∧
      ∃ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧ dist p (γ • UpperHalfPlane.I) = R)
    {b : unitInterval → UpperHalfPlane} (hb : Continuous b)
    (hbs : ∀ t, b t ∈ sphere UpperHalfPlane.I R)
    (havoid : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → b t ∉ V)
    {t₀ t₁ : unitInterval} (h00 : 0 < (t₀ : ℝ)) (h01 : (t₀ : ℝ) < 1)
    (h10 : 0 < (t₁ : ℝ)) (h11 : (t₁ : ℝ) < 1) (hf : b t₀ ∈ frontier U) :
    b t₁ ∈ frontier U := by
  rw [ft1gb_sphere_frontier_iff hfront (hbs t₁)]
  rw [ft1gb_sphere_frontier_iff hfront (hbs t₀)] at hf
  intro γ hγ
  by_contra hlt
  push_neg at hlt
  have hI : dist (b t₁) UpperHalfPlane.I = R := hbs t₁
  have hγI : γ • UpperHalfPlane.I ≠ UpperHalfPlane.I := by
    intro h
    rw [h] at hlt
    linarith
  have hne : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 →
      dist (b t) (γ • UpperHalfPlane.I) ≠ R := by
    intro t ht0 ht1 h
    exact havoid t ht0 ht1 ((hV _).2 ⟨hbs t, γ, hγ, hγI, h⟩)
  have h0gt : R < dist (b t₀) (γ • UpperHalfPlane.I) :=
    lt_of_le_of_ne (hf γ hγ) (hne t₀ h00 h01).symm
  let g : ℝ → ℝ := fun x => dist (b (Set.projIcc 0 1 zero_le_one x)) (γ • UpperHalfPlane.I) - R
  have hg : Continuous g :=
    ((hb.comp continuous_projIcc).dist continuous_const).sub continuous_const
  have hgt : ∀ t : unitInterval, g t = dist (b t) (γ • UpperHalfPlane.I) - R := by
    intro t
    show dist (b (Set.projIcc 0 1 zero_le_one (t : ℝ))) _ - R = _
    rw [Set.projIcc_val]
  have hg0 : 0 < g t₀ := by rw [hgt]; linarith
  have hg1 : g t₁ < 0 := by rw [hgt]; linarith
  have hzero : ∃ x : ℝ, (t₀ : ℝ) ⊓ t₁ ≤ x ∧ x ≤ (t₀ : ℝ) ⊔ t₁ ∧ g x = 0 := by
    rcases le_total (t₀ : ℝ) t₁ with h | h
    · obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc' h hg.continuousOn ⟨hg1.le, hg0.le⟩
      exact ⟨x, by rw [min_eq_left h]; exact hx.1, by rw [max_eq_right h]; exact hx.2, hgx⟩
    · obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc h hg.continuousOn ⟨hg1.le, hg0.le⟩
      exact ⟨x, by rw [min_eq_right h]; exact hx.1, by rw [max_eq_left h]; exact hx.2, hgx⟩
  obtain ⟨x, hx1, hx2, hgx⟩ := hzero
  have hx0 : 0 < x := lt_of_lt_of_le (lt_min h00 h10) hx1
  have hx1' : x < 1 := lt_of_le_of_lt hx2 (max_lt h01 h11)
  let s : unitInterval := ⟨x, hx0.le, hx1'.le⟩
  have hs : g x = dist (b s) (γ • UpperHalfPlane.I) - R := hgt s
  exact hne s hx0 hx1' (by linarith)

/-- If one interior point of a sphere arc avoiding the cut set is a frontier point, then the whole
closed arc is in the frontier. -/
theorem ft1gb_arc_front_closed {R : ℝ} {U : Set UpperHalfPlane}
    (hfront : frontier U = {p : UpperHalfPlane |
      (∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R) ∧
      ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I)})
    (V : Finset UpperHalfPlane) (hV : ∀ p : UpperHalfPlane, p ∈ V ↔ dist p UpperHalfPlane.I = R ∧
      ∃ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧ dist p (γ • UpperHalfPlane.I) = R)
    {b : unitInterval → UpperHalfPlane} (hb : Continuous b)
    (hbs : ∀ t, b t ∈ sphere UpperHalfPlane.I R)
    (havoid : ∀ t : unitInterval, 0 < (t : ℝ) → (t : ℝ) < 1 → b t ∉ V)
    {t₀ : unitInterval} (h00 : 0 < (t₀ : ℝ)) (h01 : (t₀ : ℝ) < 1) (hf : b t₀ ∈ frontier U) :
    Set.range b ⊆ frontier U := by
  let P : Set ℝ := {x | b (Set.projIcc 0 1 zero_le_one x) ∈ frontier U}
  have hP : IsClosed P := isClosed_frontier.preimage (hb.comp continuous_projIcc)
  have hIoo : Ioo (0 : ℝ) 1 ⊆ P := by
    intro x hx
    let s : unitInterval := ⟨x, hx.1.le, hx.2.le⟩
    have h := ft1gb_arc_interior_front (Γ := Γ) hfront V hV hb hbs havoid (t₁ := s) h00 h01 hx.1 hx.2 hf
    show b (Set.projIcc 0 1 zero_le_one x) ∈ frontier U
    rw [Set.projIcc_of_mem zero_le_one ⟨hx.1.le, hx.2.le⟩]
    exact h
  have hIcc : Icc (0 : ℝ) 1 ⊆ P := by
    rw [← closure_Ioo zero_ne_one]
    exact hP.closure_subset_iff.2 hIoo
  rintro _ ⟨t, rfl⟩
  have h := hIcc t.2
  show b t ∈ frontier U
  have e : Set.projIcc 0 1 zero_le_one (t : ℝ) = t := Set.projIcc_val zero_le_one t
  have h' : b (Set.projIcc 0 1 zero_le_one (t : ℝ)) ∈ frontier U := h
  rwa [e] at h'

/-- Euclidean step: if a closed hyperbolic ball of the same radius contains the closed central ball
with internal tangency (`r' = r + |c - c'|`), then the two centres coincide. -/
theorem ft1gb_center_tangent_eq {R : ℝ} (hR : 0 < R) (c' : UpperHalfPlane)
    (h : c'.im * Real.sinh R =
      Real.sinh R + ‖(UpperHalfPlane.I.center R : ℂ) - (c'.center R : ℂ)‖) :
    c' = UpperHalfPlane.I := by
  set y := c'.im with hy
  have hs : 0 < Real.sinh R := Real.sinh_pos_iff.2 hR
  have hcs : Real.sinh R < Real.cosh R := Real.sinh_lt_cosh R
  have him : |((UpperHalfPlane.I.center R : ℂ) - (c'.center R : ℂ)).im| ≤
      ‖(UpperHalfPlane.I.center R : ℂ) - (c'.center R : ℂ)‖ := Complex.abs_im_le_norm _
  have hime : ((UpperHalfPlane.I.center R : ℂ) - (c'.center R : ℂ)).im =
      Real.cosh R - y * Real.cosh R := by
    rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im, UpperHalfPlane.center_im,
      UpperHalfPlane.center_im, UpperHalfPlane.I_im, one_mul]
  rw [hime] at him
  have hn : ‖(UpperHalfPlane.I.center R : ℂ) - (c'.center R : ℂ)‖ = (y - 1) * Real.sinh R := by
    linarith
  rw [hn] at him
  have h1 := (abs_le.1 him).1
  have h2 := (abs_le.1 him).2
  have hy1 : y = 1 := by nlinarith
  have hn0 : ‖(UpperHalfPlane.I.center R : ℂ) - (c'.center R : ℂ)‖ = 0 := by
    rw [hn, hy1, sub_self, zero_mul]
  have hre : ((UpperHalfPlane.I.center R : ℂ) - (c'.center R : ℂ)).re = 0 := by
    have := Complex.abs_re_le_norm ((UpperHalfPlane.I.center R : ℂ) - (c'.center R : ℂ))
    rw [hn0] at this
    exact abs_nonpos_iff.1 this
  rw [Complex.sub_re, UpperHalfPlane.coe_re, UpperHalfPlane.coe_re, UpperHalfPlane.center_re,
    UpperHalfPlane.center_re] at hre
  apply UpperHalfPlane.ext
  apply Complex.ext
  · show c'.re = UpperHalfPlane.I.re
    linarith
  · show c'.im = UpperHalfPlane.I.im
    rw [UpperHalfPlane.I_im]
    exact hy1

/-- No point of the central sphere is an isolated point of `sphere ∩ frontier U`: near such a point
both sides of the circle would lie in one other orbit ball, forcing internal tangency of two
equal-radius hyperbolic circles. -/
theorem ft1gb_no_isolated_exposed_point {R : ℝ} (hR : 0 < R) {U : Set UpperHalfPlane}
    (hLf : ∀ L : Set UpperHalfPlane, IsCompact L →
      {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
        ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩ L).Nonempty}.Finite)
    (hlevel : ∀ τ : UpperHalfPlane,
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.Finite ∧
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.ncard ≤ 2)
    (hfr : ∀ q ∈ sphere UpperHalfPlane.I R,
      q ∈ frontier U ↔ ∀ γ ∈ Γ, R ≤ dist q (γ • UpperHalfPlane.I))
    {p : UpperHalfPlane} (hps : p ∈ sphere UpperHalfPlane.I R) (hpf : p ∈ frontier U)
    (hiso : ∀ᶠ q in 𝓝[≠] p, q ∈ sphere UpperHalfPlane.I R → q ∉ frontier U) : False := by
  classical
  set c : ℂ := (UpperHalfPlane.I.center R : ℂ) with hc
  set r : ℝ := Real.sinh R with hr
  have hr0 : 0 < r := Real.sinh_pos_iff.2 hR
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hcim : c.im = Real.cosh R := by
    rw [hc, UpperHalfPlane.coe_im, UpperHalfPlane.center_im, UpperHalfPlane.I_im, one_mul]
  have him : ∀ v : ℂ, ‖v‖ = 1 → 0 < (c + (r : ℂ) * v).im := by
    intro v hv
    have h1 : |v.im| ≤ 1 := by
      have := Complex.abs_im_le_norm v
      rwa [hv] at this
    have h2 : Real.sinh R < Real.cosh R := Real.sinh_lt_cosh R
    rw [Complex.add_im, Complex.im_ofReal_mul, hcim]
    nlinarith [abs_le.1 h1]
  have hpd : dist (p : ℂ) c = r := by
    have h := (UpperHalfPlane.dist_eq_iff_dist_coe_center_eq).1 (show dist p UpperHalfPlane.I = R from hps)
    rwa [UpperHalfPlane.I_im, one_mul] at h
  set u₀ : ℂ := ((p : ℂ) - c) / (r : ℂ) with hu₀
  have hu₀n : ‖u₀‖ = 1 := by
    rw [hu₀, norm_div, ← dist_eq_norm, hpd, Complex.norm_real, Real.norm_of_nonneg hr0.le,
      div_self hr0.ne']
  have hpu : (p : ℂ) = c + (r : ℂ) * u₀ := by
    rw [hu₀, mul_div_cancel₀ _ hrC]
    ring
  let e : ℝ → ℂ := fun ε => u₀ * Complex.exp (ε * Complex.I)
  have hen : ∀ ε, ‖e ε‖ = 1 := fun ε => by
    show ‖u₀ * Complex.exp (ε * Complex.I)‖ = 1
    rw [norm_mul, hu₀n, Complex.norm_exp_ofReal_mul_I, one_mul]
  let qf : ℝ → UpperHalfPlane := fun ε => ⟨c + (r : ℂ) * e ε, him _ (hen ε)⟩
  have hqcoe : ∀ ε, (qf ε : ℂ) = c + (r : ℂ) * (u₀ * Complex.exp (ε * Complex.I)) := fun ε => rfl
  have hq0 : qf 0 = p := by
    apply UpperHalfPlane.ext
    rw [hqcoe, hpu]
    simp
  have hqc : Continuous qf := by
    have h : Continuous (fun ε : ℝ => c + (r : ℂ) * (u₀ * Complex.exp (ε * Complex.I))) := by
      fun_prop
    exact UpperHalfPlane.isOpenEmbedding_coe.isEmbedding.continuous_iff.2 h
  have hqsph : ∀ ε, qf ε ∈ sphere UpperHalfPlane.I R := by
    intro ε
    show dist (qf ε) UpperHalfPlane.I = R
    rw [UpperHalfPlane.dist_eq_iff_dist_coe_center_eq, UpperHalfPlane.I_im, one_mul, hqcoe]
    show dist (c + (r : ℂ) * e ε) c = r
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, hen, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr0.le]
  have hqne : ∀ ε : ℝ, ε ≠ 0 → |ε| < Real.pi → qf ε ≠ p := by
    intro ε hε hεπ h
    have h1 : (r : ℂ) * (u₀ * Complex.exp (ε * Complex.I)) = (r : ℂ) * (u₀ * 1) := by
      have h2 := congrArg (fun z : UpperHalfPlane => (z : ℂ)) h
      simp only [hqcoe] at h2
      rw [mul_one]
      rw [hpu] at h2
      exact add_left_cancel h2
    have hu0 : u₀ ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hu₀n
      exact zero_ne_one hu₀n
    have h3 : Complex.exp (ε * Complex.I) = 1 :=
      mul_left_cancel₀ hu0 (mul_left_cancel₀ hrC h1)
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h3
    have h4 : (ε : ℂ) = ((n * (2 * Real.pi) : ℝ) : ℂ) := by
      push_cast
      have h5 : (ε : ℂ) * Complex.I = ((n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I := by
        rw [hn]
        ring
      exact mul_right_cancel₀ Complex.I_ne_zero h5
    have h6 : ε = n * (2 * Real.pi) := by exact_mod_cast h4
    have hpi := Real.pi_pos
    have hn1 : (n : ℝ) < 1 := by
      have := (abs_lt.1 hεπ).2
      nlinarith
    have hn2 : (-1 : ℝ) < n := by
      have := (abs_lt.1 hεπ).1
      nlinarith
    have hn1' : n < 1 := by exact_mod_cast hn1
    have hn2' : -1 < n := by exact_mod_cast hn2
    have hn0 : n = 0 := by omega
    rw [hn0, Int.cast_zero, zero_mul] at h6
    exact hε h6
  have htend' : Tendsto qf (𝓝[≠] (0 : ℝ)) (𝓝 p) := by
    have h := hqc.tendsto 0
    rw [hq0] at h
    exact h.mono_left nhdsWithin_le_nhds
  have htend : Tendsto qf (𝓝[≠] (0 : ℝ)) (𝓝[≠] p) := by
    refine tendsto_nhdsWithin_iff.2 ⟨htend', ?_⟩
    have hball : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |ε| < Real.pi := by
      have h : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < Real.pi :=
        Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℝ) Real.pi_pos) fun ε hε => by
          rw [mem_ball, Real.dist_eq, sub_zero] at hε
          exact hε
      exact h.filter_mono nhdsWithin_le_nhds
    filter_upwards [hball, self_mem_nhdsWithin] with ε h1 h2
    exact hqne ε h2 h1
  have hev1 : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), qf ε ∉ frontier U :=
    (htend.eventually hiso).mono fun ε h => h (hqsph ε)
  -- finitely many candidate centres
  let T : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) := {γ | γ ∈ Γ ∧
    ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩ closedBall p R).Nonempty}
  have hT : T.Finite := hLf _ (isCompact_closedBall p R)
  let T' : Set (Matrix.SpecialLinearGroup (Fin 2) ℝ) := {γ | γ ∈ T ∧ R < dist p (γ • UpperHalfPlane.I)}
  have hT' : T'.Finite := hT.subset fun γ hγ => hγ.1
  have hev2 : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ∀ γ ∈ T', R < dist (qf ε) (γ • UpperHalfPlane.I) := by
    refine (Filter.eventually_all_finite hT').2 fun γ hγ => ?_
    have h : Tendsto (fun ε => dist (qf ε) (γ • UpperHalfPlane.I)) (𝓝[≠] (0 : ℝ))
        (𝓝 (dist p (γ • UpperHalfPlane.I))) := htend'.dist tendsto_const_nhds
    exact h.eventually (lt_mem_nhds hγ.2)
  have hev3 : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), dist (qf ε) p ≤ R :=
    htend'.eventually (Metric.closedBall_mem_nhds p hR)
  have hgood : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ∃ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧
      dist p (γ • UpperHalfPlane.I) = R ∧ dist (qf ε) (γ • UpperHalfPlane.I) < R := by
    filter_upwards [hev1, hev2, hev3] with ε h1 h2 h3
    rw [hfr _ (hqsph ε)] at h1
    push_neg at h1
    obtain ⟨γ, hγ, hlt⟩ := h1
    have hγT : γ ∈ T := by
      refine ⟨hγ, qf ε, ⟨γ⁻¹ • qf ε, ?_, smul_inv_smul γ (qf ε)⟩, h3⟩
      show dist (γ⁻¹ • qf ε) UpperHalfPlane.I ≤ R
      have hd := (isometry_smul UpperHalfPlane γ).dist_eq (γ⁻¹ • qf ε) UpperHalfPlane.I
      rw [smul_inv_smul] at hd
      rw [← hd]
      exact hlt.le
    have hge : R ≤ dist p (γ • UpperHalfPlane.I) := (hfr p hps).1 hpf γ hγ
    have heq : dist p (γ • UpperHalfPlane.I) = R := by
      by_contra hne
      have hgt : R < dist p (γ • UpperHalfPlane.I) := lt_of_le_of_ne hge (Ne.symm hne)
      have := h2 γ ⟨hγT, hgt⟩
      linarith
    have hγI : γ • UpperHalfPlane.I ≠ UpperHalfPlane.I := by
      intro h
      rw [h] at hlt
      have := hqsph ε
      rw [mem_sphere] at this
      linarith
    exact ⟨γ, hγ, hγI, heq, hlt⟩
  obtain ⟨ε₀, γ₀, hγ₀, hγ₀I, hγ₀R, -⟩ := hgood.exists
  set c' := γ₀ • UpperHalfPlane.I with hc'
  have huniq : ∀ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I →
      dist p (γ • UpperHalfPlane.I) = R → γ • UpperHalfPlane.I = c' := by
    intro γ hγ hγI hγR
    by_contra hne
    obtain ⟨hfin, hcard⟩ := hlevel p
    have hsub : ({UpperHalfPlane.I, c', γ • UpperHalfPlane.I} : Set UpperHalfPlane) ⊆
        {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist p z = R} := by
      intro z hz
      rcases hz with h | h | h
      · rw [h]
        exact ⟨⟨1, Γ.one_mem, (one_smul _ _).symm⟩, hps⟩
      · rw [h]
        exact ⟨⟨γ₀, hγ₀, rfl⟩, hγ₀R⟩
      · rw [mem_singleton_iff] at h
        rw [h]
        exact ⟨⟨γ, hγ, rfl⟩, hγR⟩
    have h3 : ({UpperHalfPlane.I, c', γ • UpperHalfPlane.I} : Set UpperHalfPlane).ncard = 3 := by
      have hnot : UpperHalfPlane.I ∉ ({c', γ • UpperHalfPlane.I} : Set UpperHalfPlane) := by
        intro h
        rcases h with h | h
        · exact hγ₀I h.symm
        · rw [mem_singleton_iff] at h
          exact hγI h.symm
      rw [Set.ncard_insert_of_notMem hnot, Set.ncard_pair (Ne.symm hne)]
    have := Set.ncard_le_ncard hsub hfin
    omega
  have hev : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), dist (qf ε) c' < R := by
    filter_upwards [hgood] with ε h
    obtain ⟨γ, hγ, hγI, hγR, hlt⟩ := h
    rw [huniq γ hγ hγI hγR] at hlt
    exact hlt
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 hev
  -- Euclidean data of the second ball
  set c₂ : ℂ := (c'.center R : ℂ) with hc₂
  set r₂ : ℝ := c'.im * Real.sinh R with hr₂
  have hp2 : dist (p : ℂ) c₂ = r₂ := (UpperHalfPlane.dist_eq_iff_dist_coe_center_eq).1 hγ₀R
  have hlt2 : ∀ ε : ℝ, 0 < |ε| → |ε| < δ → dist (qf ε : ℂ) c₂ < r₂ := by
    intro ε h0 hd
    have hmem : ε ∈ ball (0 : ℝ) δ ∩ {0}ᶜ := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, Real.dist_eq, sub_zero]
        exact hd
      · intro h
        rw [mem_singleton_iff] at h
        rw [h, abs_zero] at h0
        exact lt_irrefl 0 h0
    exact (UpperHalfPlane.dist_lt_iff_dist_coe_center_lt).1 (hδs hmem)
  set w : ℂ := c - c₂ with hw
  set z : ℂ := w * (starRingEnd ℂ) u₀ with hz
  set A : ℝ := z.re with hA
  set B : ℝ := z.im with hB
  have hu1 : u₀.re ^ 2 + u₀.im ^ 2 = 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hu₀n
    rw [Complex.sq_norm, Complex.normSq_apply, one_pow] at h
    linear_combination h
  -- squared distance along the circle
  have hF : ∀ ε : ℝ, dist (qf ε : ℂ) c₂ ^ 2 - dist (p : ℂ) c₂ ^ 2 =
      2 * r * (A * Real.cos ε + B * Real.sin ε - A) := by
    intro ε
    rw [hqcoe, hpu, dist_eq_norm, dist_eq_norm, Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    have hcs := Real.cos_sq_add_sin_sq ε
    simp only [hA, hB, hz, hw, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    linear_combination (r ^ 2 * (u₀.re ^ 2 + u₀.im ^ 2)) * hcs - r ^ 2 * hu1 + r ^ 2 * hu1
  have hneg : ∀ ε : ℝ, 0 < ε → ε < δ →
      A * Real.cos ε + B * Real.sin ε < A ∧ A * Real.cos ε - B * Real.sin ε < A := by
    intro ε h0 hd
    have hpos : ∀ ε' : ℝ, 0 < |ε'| → |ε'| < δ → A * Real.cos ε' + B * Real.sin ε' < A := by
      intro ε' h0' hd'
      have h1 := hlt2 ε' h0' hd'
      have h2 : dist (qf ε' : ℂ) c₂ ^ 2 < dist (p : ℂ) c₂ ^ 2 := by
        rw [hp2]
        exact pow_lt_pow_left₀ h1 dist_nonneg two_ne_zero
      have h3 := hF ε'
      nlinarith
    refine ⟨hpos ε (by rw [abs_of_pos h0]; exact h0) (by rw [abs_of_pos h0]; exact hd), ?_⟩
    have h := hpos (-ε) (by rw [abs_neg, abs_of_pos h0]; exact h0)
      (by rw [abs_neg, abs_of_pos h0]; exact hd)
    rw [Real.cos_neg, Real.sin_neg] at h
    linarith
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  -- A > 0
  set ε₁ : ℝ := min (δ / 2) 1 with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by linarith) one_pos
  have hε₁δ : ε₁ < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  have hcos1 : Real.cos ε₁ < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) hε₁0
    rwa [Real.cos_zero] at this
  have hApos : 0 < A := by
    obtain ⟨h1, h2⟩ := hneg ε₁ hε₁0 hε₁δ
    nlinarith
  -- B = 0
  have hB0 : B = 0 := by
    by_contra hBne
    have hBabs : 0 < |B| := abs_pos.2 hBne
    set ε : ℝ := min ε₁ (|B| / (2 * A)) with hε
    have hε0 : 0 < ε := lt_min hε₁0 (div_pos hBabs (by linarith))
    have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) hε₁δ
    have hε1 : ε ≤ 1 := (min_le_left _ _).trans hε₁1
    have hεB : ε ≤ |B| / (2 * A) := min_le_right _ _
    obtain ⟨h1, h2⟩ := hneg ε hε0 hεδ
    have hsin : 2 / Real.pi * ε ≤ Real.sin ε := Real.mul_le_sin hε0.le (by linarith)
    have hcos : 1 - ε ^ 2 / 2 ≤ Real.cos ε := Real.one_sub_sq_div_two_le_cos
    have hsin0 : 0 < Real.sin ε := Real.sin_pos_of_pos_of_lt_pi hε0 (by linarith)
    have habs : |B| * Real.sin ε < A * (1 - Real.cos ε) := by
      rcases abs_cases B with hb | hb
      · rw [hb.1]; linarith
      · rw [hb.1]; linarith
    have hstep : |B| * (2 / Real.pi * ε) < A * (ε ^ 2 / 2) := by
      have h6 := mul_le_mul_of_nonneg_left hsin (abs_nonneg B)
      have h5 : A * (1 - Real.cos ε) ≤ A * (ε ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hApos.le
      linarith
    have hεB' : 2 * A * ε ≤ |B| := by
      rw [le_div_iff₀ (by linarith)] at hεB
      linarith
    have h1 : (2 * A * ε) * (2 / Real.pi * ε) ≤ |B| * (2 / Real.pi * ε) :=
      mul_le_mul_of_nonneg_right hεB' (by positivity)
    have h2 : (2 * A * ε) * (2 / Real.pi * ε) = A * ε ^ 2 * (4 / Real.pi) := by ring
    have h4 : (1 : ℝ) / 2 < 4 / Real.pi := by
      rw [lt_div_iff₀ hpi]
      linarith [Real.pi_le_four]
    have hA2 : 0 < A * ε ^ 2 := by positivity
    have h3 : A * ε ^ 2 * (1 / 2) < A * ε ^ 2 * (4 / Real.pi) := mul_lt_mul_of_pos_left h4 hA2
    linarith
  -- internal tangency
  have hzn : ‖z‖ = ‖w‖ := by
    rw [hz, norm_mul, Complex.norm_conj, hu₀n, mul_one]
  have hzA : ‖z‖ = A := by
    have hzre : z = (A : ℂ) := by
      apply Complex.ext
      · rw [Complex.ofReal_re, hA]
      · rw [Complex.ofReal_im, ← hB, hB0]
    rw [hzre, Complex.norm_real, Real.norm_of_nonneg hApos.le]
  have hr2sq : r₂ ^ 2 = (r + A) ^ 2 := by
    rw [← hp2, hpu, dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    have hwn : w.re ^ 2 + w.im ^ 2 = A ^ 2 := by
      have h := congrArg (fun x : ℝ => x ^ 2) (hzn.symm.trans hzA)
      rw [Complex.sq_norm, Complex.normSq_apply] at h
      linear_combination h
    have hAe : A = w.re * u₀.re + w.im * u₀.im := by
      simp only [hA, hz, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    have hsplit : c + (r : ℂ) * u₀ - c₂ = w + (r : ℂ) * u₀ := by rw [hw]; ring
    rw [hsplit]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im]
    linear_combination hwn + r ^ 2 * hu1 - 2 * r * hAe
  have hr2nn : 0 ≤ r₂ := by rw [← hp2]; exact dist_nonneg
  have hr2 : r₂ = r + ‖w‖ := by
    rw [← hzn, hzA]
    nlinarith [sq_nonneg (r₂ - (r + A)), sq_nonneg (r₂ + (r + A))]
  have hcI : c' = UpperHalfPlane.I := ft1gb_center_tangent_eq hR c' (by rw [← hr2])
  exact hγ₀I hcI

/-- B2b. Select actual subdivision arcs by exposure. The output includes every
exposed vertex as an endpoint of a selected arc; no isolated-vertex coverage is
silently discarded. Selection is an injection into the existing finite subdivision. -/
theorem ft1gb_select_exposed_arcs {R : ℝ} (hR : 0 < R) {U : Set UpperHalfPlane}
    (hU : U = ⋃ γ ∈ Γ, (fun τ : UpperHalfPlane => γ • τ) ''
      closedBall UpperHalfPlane.I R)
    (hLf : ∀ L : Set UpperHalfPlane, IsCompact L →
      {γ : Matrix.SpecialLinearGroup (Fin 2) ℝ | γ ∈ Γ ∧
        ((fun τ : UpperHalfPlane => γ • τ) '' closedBall UpperHalfPlane.I R ∩ L).Nonempty}.Finite)
    (hpair : ∀ γ ∈ Γ, ∀ δ ∈ Γ,
      γ • UpperHalfPlane.I ≠ δ • UpperHalfPlane.I →
        dist (γ • UpperHalfPlane.I) (δ • UpperHalfPlane.I) ≠ 2 * R)
    (hlevel : ∀ τ : UpperHalfPlane,
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.Finite ∧
      {z : UpperHalfPlane | (∃ γ ∈ Γ, z = γ • UpperHalfPlane.I) ∧ dist τ z = R}.ncard ≤ 2)
    (hfront : frontier U = {p : UpperHalfPlane |
      (∃ γ ∈ Γ, dist p (γ • UpperHalfPlane.I) = R) ∧
      ∀ γ ∈ Γ, R ≤ dist p (γ • UpperHalfPlane.I)})
    (V : Finset UpperHalfPlane) (hV : ∀ p : UpperHalfPlane, p ∈ V ↔ dist p UpperHalfPlane.I = R ∧
      ∃ γ ∈ Γ, γ • UpperHalfPlane.I ≠ UpperHalfPlane.I ∧ dist p (γ • UpperHalfPlane.I) = R)
    (n : ℕ) (a : Fin n → unitInterval → UpperHalfPlane)
    (hshape : (∀ i, Topology.IsEmbedding (a i) ∧ Set.range (a i) ⊆ sphere UpperHalfPlane.I R ∧
      ∃ x y : Circle, x ≠ y ∧ ∀ t : unitInterval,
        (a i t : ℂ) = (UpperHalfPlane.I.center R : ℂ) +
          (Real.sinh R : ℂ) * (Circle.path x y t : ℂ)))
    (hsep : ∀ i j (t s : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 →
      a i t = a j s → i = j ∧ t = s)
    (havoid : ∀ i (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → a i t ∉ V)
    (hcover : sphere UpperHalfPlane.I R = ⋃ i, Set.range (a i)) :
    ∃ (m : ℕ) (j : Fin m ↪ Fin n),
      (∀ i, Set.range (a (j i)) ⊆ frontier U) ∧
      sphere UpperHalfPlane.I R ∩ frontier U = ⋃ i, Set.range (a (j i)) := by
  classical
  have _hU := hU
  have _hpair := hpair
  have _hsep := hsep
  have hfr : ∀ q ∈ sphere UpperHalfPlane.I R,
      q ∈ frontier U ↔ ∀ γ ∈ Γ, R ≤ dist q (γ • UpperHalfPlane.I) := fun q hq =>
    ft1gb_sphere_frontier_iff hfront hq
  have hcont : ∀ i, Continuous (a i) := fun i => (hshape i).1.continuous
  have hsph : ∀ i t, a i t ∈ sphere UpperHalfPlane.I R := fun i t => (hshape i).2.1 ⟨t, rfl⟩
  let half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hhalf0 : 0 < ((half : unitInterval) : ℝ) := by show (0 : ℝ) < 1 / 2; norm_num
  have hhalf1 : ((half : unitInterval) : ℝ) < 1 := by show (1 / 2 : ℝ) < 1; norm_num
  have hsel : ∀ i, a i half ∈ frontier U → Set.range (a i) ⊆ frontier U := fun i h =>
    ft1gb_arc_front_closed hfront V hV (hcont i) (hsph i) (havoid i) hhalf0 hhalf1 h
  have hsel' : ∀ i (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → a i t ∈ frontier U →
      a i half ∈ frontier U := fun i t h0 h1 h =>
    ft1gb_arc_interior_front hfront V hV (hcont i) (hsph i) (havoid i) h0 h1 hhalf0 hhalf1 h
  let S : Finset (Fin n) := Finset.univ.filter (fun i => a i half ∈ frontier U)
  let j : Fin S.card ↪ Fin n := (S.orderEmbOfFin rfl).toEmbedding
  have hjS : ∀ k, j k ∈ S := fun k => Finset.orderEmbOfFin_mem S rfl k
  have hSj : ∀ i ∈ S, ∃ k, j k = i := by
    intro i hi
    have h : i ∈ Set.range (S.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hi
    obtain ⟨k, hk⟩ := h
    exact ⟨k, hk⟩
  have hjfront : ∀ k, Set.range (a (j k)) ⊆ frontier U := fun k =>
    hsel _ (Finset.mem_filter.1 (hjS k)).2
  refine ⟨S.card, j, hjfront, ?_⟩
  -- interior points of a selected-or-not arc
  have hint : ∀ i (t : unitInterval), 0 < (t : ℝ) → (t : ℝ) < 1 → a i t ∈ frontier U →
      a i t ∈ ⋃ k, Set.range (a (j k)) := by
    intro i t h0 h1 hf
    obtain ⟨k, hk⟩ := hSj i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hsel' i t h0 h1 hf⟩)
    exact mem_iUnion.2 ⟨k, t, by rw [hk]⟩
  have hend : ∀ t : unitInterval, ¬ (0 < (t : ℝ) ∧ (t : ℝ) < 1) → t = 0 ∨ t = 1 := by
    intro t ht
    by_cases h0 : 0 < (t : ℝ)
    · right
      apply Subtype.ext
      have : ¬ (t : ℝ) < 1 := fun h => ht ⟨h0, h⟩
      show (t : ℝ) = 1
      linarith [t.2.2]
    · left
      apply Subtype.ext
      show (t : ℝ) = 0
      linarith [t.2.1]
  ext p
  constructor
  · rintro ⟨hps, hpf⟩
    have hp' : p ∈ ⋃ i, Set.range (a i) := by rw [← hcover]; exact hps
    obtain ⟨i, t, rfl⟩ := mem_iUnion.1 hp'
    by_cases ht : 0 < (t : ℝ) ∧ (t : ℝ) < 1
    · exact hint i t ht.1 ht.2 hpf
    · by_contra hno
      set p := a i t with hpdef
      let Sel : Set UpperHalfPlane := ⋃ k, Set.range (a (j k))
      have hSelc : IsClosed Sel :=
        isClosed_iUnion_of_finite fun k => (isCompact_range (hcont (j k))).isClosed
      let E : Set UpperHalfPlane := (⋃ i', ({a i' 0, a i' 1} : Set UpperHalfPlane)) \ {p}
      have hEf : E.Finite :=
        (Set.finite_iUnion fun i' => (Set.toFinite ({a i' 0, a i' 1} : Set UpperHalfPlane))).diff
      have hK : (Sel ∪ E)ᶜ ∈ 𝓝 p := by
        refine (hSelc.union hEf.isClosed).isOpen_compl.mem_nhds ?_
        rintro (h | h)
        · exact hno h
        · exact h.2 rfl
      have hiso : ∀ᶠ q in 𝓝[≠] p, q ∈ sphere UpperHalfPlane.I R → q ∉ frontier U := by
        filter_upwards [nhdsWithin_le_nhds hK, self_mem_nhdsWithin] with q hq hqp hqs hqf
        have hq' : q ∈ ⋃ i, Set.range (a i) := by rw [← hcover]; exact hqs
        obtain ⟨k, s, hks⟩ := mem_iUnion.1 hq'
        by_cases hs : 0 < (s : ℝ) ∧ (s : ℝ) < 1
        · rw [← hks] at hqf
          apply hq
          left
          rw [← hks]
          exact hint k s hs.1 hs.2 hqf
        · apply hq
          right
          refine ⟨mem_iUnion.2 ⟨k, ?_⟩, hqp⟩
          rcases hend s hs with h | h
          · rw [← hks, h]
            exact Or.inl rfl
          · rw [← hks, h]
            exact Or.inr rfl
      exact ft1gb_no_isolated_exposed_point hR hLf hlevel hfr (hsph i t) hpf hiso
  · intro hp
    obtain ⟨k, t, rfl⟩ := mem_iUnion.1 hp
    exact ⟨hsph _ _, hjfront k ⟨t, rfl⟩⟩

end LiZhongQC
