import LiZhongQC.Ch01.S04_ModulusExtremalLength
import LiZhongQC.Lemmas.RectangleQuad
import LiZhongQC.Lemmas.Koebe

/-!
# §5 模的极值问题 — Extremal problems for the modulus

* Grötzsch domain `B_r`, Grötzsch function `μ(r)`      — `grotzschDomain`, `grotzschMu`
* Theorem 5.1 (Grötzsch extremal problem)             — `thm5_1_grotzsch`
* Teichmüller domain `T_R`                            — `teichmullerDomain`
* Theorem 5.2, (5.7), Theorem 5.2′                    — `thm5_2_teichmuller`,
                                                         `thm5_2_modulus_teichmullerDomain`,
                                                         `eq5_7`, `thm5_2'`
* Theorem 5.3 (Teichmüller's modulus theorem)         — `thm5_3_teichmuller_modulus_theorem`
* Mori domain `G_d`, Theorem 5.4, (5.15)              — `moriDomain`, `thm5_4_mori`,
                                                         `eq5_15`, `moriDomain_modulus`
* §5.5 the functions `Λ(ρ)` and `μ(r)`: (5.16)–(5.21)
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real

noncomputable section

namespace LiZhongQC

/-! ## The Grötzsch problem -/

/-- The Grötzsch domain `B_r = Δ ∖ [0, r]` (`0 < r < 1`). -/
def grotzschDomain (r : ℝ) : Set ℂ :=
  unitDisc \ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ r}

/-- The Grötzsch function `μ(r) = M(B_r)`. -/
def grotzschMu (r : ℝ) : ℝ := (dcModulus (grotzschDomain r)).toReal

private lemma grotzschDomain_mem_iff {r : ℝ} {z : ℂ} :
    z ∈ grotzschDomain r ↔ ‖z‖ < 1 ∧ ¬(z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ r) := by
  simp only [grotzschDomain, unitDisc, Set.mem_diff, mem_ball_zero_iff, Set.mem_setOf_eq]

private lemma mem_closure_upperHalfDisc {x : ℝ} (hx : x ^ 2 < 1) :
    (x : ℂ) ∈ closure {z : ℂ | ‖z‖ < 1 ∧ 0 < z.im} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have habs : |x| < 1 := by
    rw [← Real.sqrt_sq_eq_abs, Real.sqrt_lt' zero_lt_one]
    simpa using hx
  set c : ℝ := min (ε / 2) ((1 - |x|) / 2) with hc
  have hcpos : 0 < c := lt_min (by linarith) (by linarith)
  have hcε : c ≤ ε / 2 := min_le_left _ _
  have hc1 : c ≤ (1 - |x|) / 2 := min_le_right _ _
  have hnormx : ‖(x : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hnormc : ‖(c : ℂ)‖ = c := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
  set w : ℂ := (x : ℂ) + (c : ℂ) * I with hwdef
  refine ⟨w, ?_, ?_⟩
  · rw [hwdef]
    constructor
    · calc ‖(x : ℂ) + (c : ℂ) * I‖ ≤ ‖(x : ℂ)‖ + ‖(c : ℂ) * I‖ := norm_add_le _ _
        _ = |x| + c := by rw [norm_mul, Complex.norm_I, mul_one, hnormx, hnormc]
        _ ≤ |x| + (1 - |x|) / 2 := by linarith
        _ < 1 := by linarith
    · have him : ((x : ℂ) + (c : ℂ) * I).im = c := by
        simp [Complex.add_im]
      rw [him]
      exact hcpos
  · rw [hwdef, dist_comm, dist_eq_norm]
    have heq : (x : ℂ) + (c : ℂ) * I - (x : ℂ) = (c : ℂ) * I := by ring
    rw [heq, norm_mul, Complex.norm_I, mul_one, hnormc]
    linarith

private lemma mem_closure_lowerHalfDisc {x : ℝ} (hx : x ^ 2 < 1) :
    (x : ℂ) ∈ closure {z : ℂ | ‖z‖ < 1 ∧ z.im < 0} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have habs : |x| < 1 := by
    rw [← Real.sqrt_sq_eq_abs, Real.sqrt_lt' zero_lt_one]
    simpa using hx
  set c : ℝ := min (ε / 2) ((1 - |x|) / 2) with hc
  have hcpos : 0 < c := lt_min (by linarith) (by linarith)
  have hcε : c ≤ ε / 2 := min_le_left _ _
  have hc1 : c ≤ (1 - |x|) / 2 := min_le_right _ _
  have hnormx : ‖(x : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hnormc : ‖(c : ℂ)‖ = c := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
  set w : ℂ := (x : ℂ) - (c : ℂ) * I with hwdef
  refine ⟨w, ?_, ?_⟩
  · rw [hwdef]
    constructor
    · calc ‖(x : ℂ) - (c : ℂ) * I‖ ≤ ‖(x : ℂ)‖ + ‖(c : ℂ) * I‖ := norm_sub_le _ _
        _ = |x| + c := by rw [norm_mul, Complex.norm_I, mul_one, hnormx, hnormc]
        _ ≤ |x| + (1 - |x|) / 2 := by linarith
        _ < 1 := by linarith
    · have hsub : ((x : ℂ) - (c : ℂ) * I).im = -c := by
        simp
      rw [hsub]
      linarith
  · rw [hwdef, dist_comm, dist_eq_norm]
    have heq : (x : ℂ) - (c : ℂ) * I - (x : ℂ) = -((c : ℂ) * I) := by ring
    rw [heq, norm_neg, norm_mul, Complex.norm_I, mul_one, hnormc]
    linarith

/-- `B_r` is doubly connected with finite modulus. -/
theorem grotzschDomain_doublyConnected {r : ℝ} (h₀ : 0 < r) (h₁ : r < 1) :
    IsDoublyConnected (grotzschDomain r) ∧ dcModulus (grotzschDomain r) < ⊤ := by
  have hclosed : IsClosed {z : ℂ | z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ r} := by
    have h1 : IsClosed {z : ℂ | z.im = 0} := isClosed_eq Complex.continuous_im continuous_const
    have h2 : IsClosed {z : ℂ | 0 ≤ z.re} := isClosed_le continuous_const Complex.continuous_re
    have h3 : IsClosed {z : ℂ | z.re ≤ r} := isClosed_le Complex.continuous_re continuous_const
    have h4 : IsClosed {z : ℂ | z.im = 0 ∧ (0 ≤ z.re ∧ z.re ≤ r)} := by
      simpa only [Set.setOf_and] using h1.inter (h2.inter h3)
    exact h4
  have hDopen : IsOpen (grotzschDomain r) := by
    rw [grotzschDomain, unitDisc]
    exact IsOpen.sdiff isOpen_ball hclosed
  -- decomposition of the domain
  set A₁ : Set ℂ := {z : ℂ | ‖z‖ < 1 ∧ 0 < z.im} with hA₁def
  set A₂ : Set ℂ := {z : ℂ | ‖z‖ < 1 ∧ z.im < 0} with hA₂def
  set K : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Set.Ioo r 1 with hKdef
  set J : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Set.Ioo (-1) 0 with hJdef
  have hA₁pre : IsPreconnected A₁ := by
    have hconv : Convex ℝ A₁ := by
      have hset : A₁ = ball (0 : ℂ) 1 ∩ Complex.imLm ⁻¹' Set.Ioi (0 : ℝ) := by
        ext z
        simp [hA₁def]
      rw [hset]
      exact (convex_ball (0 : ℂ) 1).inter (Convex.linear_preimage (convex_Ioi 0) Complex.imLm)
    exact hconv.isPreconnected
  have hA₂pre : IsPreconnected A₂ := by
    have hconv : Convex ℝ A₂ := by
      have hset : A₂ = ball (0 : ℂ) 1 ∩ Complex.imLm ⁻¹' Set.Iio (0 : ℝ) := by
        ext z
        simp [hA₂def]
      rw [hset]
      exact (convex_ball (0 : ℂ) 1).inter (Convex.linear_preimage (convex_Iio 0) Complex.imLm)
    exact hconv.isPreconnected
  have hKsubA₁ : K ⊆ closure A₁ := by
    rintro _ ⟨t, ht, rfl⟩
    exact mem_closure_upperHalfDisc (by
      have ht0 : 0 < t := h₀.trans ht.1
      nlinarith [ht.2, ht0])
  have hKsubA₂ : K ⊆ closure A₂ := by
    rintro _ ⟨t, ht, rfl⟩
    exact mem_closure_lowerHalfDisc (by
      have hlt1 : t < 1 := by linarith [ht.2]
      nlinarith [ht.1, hlt1])
  have hJsubA₂ : J ⊆ closure A₂ := by
    rintro _ ⟨t, ht, rfl⟩
    exact mem_closure_lowerHalfDisc (by
      have hlt1 : t < 1 := by linarith [ht.2]
      nlinarith [ht.1, hlt1])
  have hA₁K : IsPreconnected (A₁ ∪ K) :=
    hA₁pre.subset_closure subset_union_left (union_subset subset_closure hKsubA₁)
  have hA₂K : IsPreconnected (A₂ ∪ K) :=
    hA₂pre.subset_closure subset_union_left (union_subset subset_closure hKsubA₂)
  have hA₂KJ : IsPreconnected ((A₂ ∪ K) ∪ J) :=
    hA₂K.subset_closure subset_union_left
      (union_subset subset_closure (hJsubA₂.trans (closure_mono subset_union_left)))
  have hInter : ((A₁ ∪ K) ∩ ((A₂ ∪ K) ∪ J)).Nonempty := by
    refine ⟨(((r + 1) / 2 : ℝ) : ℂ), ?_, ?_⟩
    · refine Or.inr ⟨(r + 1) / 2, ⟨by linarith, by linarith⟩, rfl⟩
    · refine Or.inl (Or.inr ⟨(r + 1) / 2, ⟨by linarith, by linarith⟩, rfl⟩)
  have hpre : IsPreconnected ((A₁ ∪ K) ∪ ((A₂ ∪ K) ∪ J)) := hA₁K.union' hInter hA₂KJ
  -- the four pieces lie in the Grötzsch domain
  have hA₁sub : A₁ ⊆ grotzschDomain r := by
    intro z hz
    rw [grotzschDomain_mem_iff]
    exact ⟨hz.1, fun h => by linarith [hz.2, h.1]⟩
  have hA₂sub : A₂ ⊆ grotzschDomain r := by
    intro z hz
    rw [grotzschDomain_mem_iff]
    exact ⟨hz.1, fun h => by linarith [hz.2, h.1]⟩
  have hKsub : K ⊆ grotzschDomain r := by
    rintro _ ⟨t, ht, rfl⟩
    rw [grotzschDomain_mem_iff]
    refine ⟨?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (h₀.trans ht.1)]
      exact ht.2
    · rintro ⟨-, -, hle⟩
      rw [Complex.ofReal_re] at hle
      linarith [ht.1]
  have hJsub : J ⊆ grotzschDomain r := by
    rintro _ ⟨t, ht, rfl⟩
    rw [grotzschDomain_mem_iff]
    refine ⟨?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg ht.2]
      linarith [ht.1]
    · rintro ⟨-, hge, -⟩
      rw [Complex.ofReal_re] at hge
      linarith [ht.2]
  -- the union is exactly the domain
  have hset : grotzschDomain r = (A₁ ∪ K) ∪ ((A₂ ∪ K) ∪ J) := by
    refine Subset.antisymm ?_ ?_
    · intro z hz
      rw [grotzschDomain_mem_iff] at hz
      obtain ⟨hz1, hz2⟩ := hz
      rcases lt_trichotomy z.im 0 with hlt | hzero | hgt
      · exact Or.inr (Or.inl (Or.inl ⟨hz1, hlt⟩))
      · have hz_eq : z = ((z.re : ℝ) : ℂ) := by
          refine Complex.ext ?_ ?_ <;> simp [Complex.ofReal_re, Complex.ofReal_im, hzero]
        have habs : |z.re| < 1 := by
          have hnorm : ‖((z.re : ℝ) : ℂ)‖ = |z.re| := by
            rw [Complex.norm_real, Real.norm_eq_abs]
          rwa [hz_eq, hnorm] at hz1
        have hnot : ¬(0 ≤ z.re ∧ z.re ≤ r) := fun h => hz2 ⟨hzero, h.1, h.2⟩
        rcases lt_or_ge z.re 0 with hneg | hnonneg
        · exact Or.inr (Or.inr ⟨z.re, ⟨(abs_lt.mp habs).1, hneg⟩, hz_eq.symm⟩)
        · have hrlt : r < z.re := by
            by_contra hcon
            exact hnot ⟨hnonneg, not_lt.mp hcon⟩
          exact Or.inl (Or.inr ⟨z.re, ⟨hrlt, (abs_lt.mp habs).2⟩, hz_eq.symm⟩)
      · exact Or.inl (Or.inl ⟨hz1, hgt⟩)
    · exact union_subset (union_subset hA₁sub hKsub)
        (union_subset (union_subset hA₂sub hKsub) hJsub)
  have hDconn : IsConnected (grotzschDomain r) := by
    have hpmem : (((1 / 2 : ℝ) : ℂ) * I) ∈ (A₁ ∪ K) ∪ ((A₂ ∪ K) ∪ J) := by
      refine Or.inl (Or.inl ⟨?_, ?_⟩)
      · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
        norm_num
      · have : (((1 / 2 : ℝ) : ℂ) * I).im = 1 / 2 := by
          simp
        rw [this]
        norm_num
    rw [hset]
    exact ⟨⟨_, hpmem⟩, hpre⟩
  -- the complement of the domain
  have hcomplD : (grotzschDomain r)ᶜ =
      {z : ℂ | 1 ≤ ‖z‖} ∪ ((fun t : ℝ => (t : ℂ)) '' Set.Icc (0 : ℝ) r) := by
    ext z
    rw [Set.mem_compl_iff, grotzschDomain_mem_iff]
    constructor
    · intro h
      by_cases hz : 1 ≤ ‖z‖
      · exact Or.inl hz
      · have hz' : ‖z‖ < 1 := not_le.mp hz
        have hslit : z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ r := by
          by_contra hc
          exact h ⟨hz', hc⟩
        have hz_eq : z = ((z.re : ℝ) : ℂ) := by
            refine Complex.ext ?_ ?_ <;> simp [Complex.ofReal_re, Complex.ofReal_im, hslit.1]
        exact Or.inr ⟨z.re, ⟨hslit.2.1, hslit.2.2⟩, hz_eq.symm⟩
    · rintro (hz | ⟨t, ht, rfl⟩) h
      · rw [Set.mem_setOf_eq] at hz
        linarith [h.1, hz]
      · exact h.2 ⟨by simp, by simpa using ht.1, by simpa using ht.2⟩
  set P : Set ExtPlane := toExt {z : ℂ | 1 ≤ ‖z‖} ∪ {extInf} with hPdef
  set Q : Set ExtPlane := toExt ((fun t : ℝ => (t : ℂ)) '' Set.Icc (0 : ℝ) r) with hQdef
  set X : Set ExtPlane := (toExt (grotzschDomain r))ᶜ with hXdef
  have himgunion : toExt ({z : ℂ | 1 ≤ ‖z‖} ∪ (fun t : ℝ => (t : ℂ)) '' Set.Icc (0 : ℝ) r) =
      toExt {z : ℂ | 1 ≤ ‖z‖} ∪ toExt ((fun t : ℝ => (t : ℂ)) '' Set.Icc (0 : ℝ) r) :=
    Set.image_union ((↑) : ℂ → ExtPlane) _ _
  have hXeq : X = P ∪ Q := by
    rw [hXdef, compl_toExt, hcomplD, hPdef, hQdef, himgunion, Set.union_right_comm]
  -- P and Q are closed, connected and disjoint
  have hcontc : Continuous (fun t : ℝ => ((t : ℂ) : ExtPlane)) :=
    OnePoint.continuous_coe.comp Complex.continuous_ofReal
  have hQimg : Q = (fun t : ℝ => ((t : ℂ) : ExtPlane)) '' Set.Icc (0 : ℝ) r := by
    rw [hQdef]
    change ((↑) : ℂ → ExtPlane) '' ((fun t : ℝ => (t : ℂ)) '' Set.Icc (0 : ℝ) r) =
      (fun t : ℝ => ((t : ℂ) : ExtPlane)) '' Set.Icc (0 : ℝ) r
    rw [Set.image_image]
  have hQclosed : IsClosed Q := by
    rw [hQimg]
    exact (isCompact_Icc.image hcontc).isClosed
  have hQpre : IsPreconnected Q := by
    rw [hQimg]
    exact isPreconnected_Icc.image _ hcontc.continuousOn
  have hP1pre : IsPreconnected {z : ℂ | 1 ≤ ‖z‖} := by
    have himg : (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I)) ''
        (Set.Ici (1 : ℝ) ×ˢ (Set.univ : Set ℝ)) = {z : ℂ | 1 ≤ ‖z‖} := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        have hp1 : (1 : ℝ) ≤ p.1 := hp.1
        rw [Set.mem_setOf_eq, Complex.norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans zero_le_one hp1)]
        exact hp1
      · intro hz
        refine ⟨(‖z‖, Complex.arg z), ⟨hz, Set.mem_univ _⟩, ?_⟩
        exact Complex.norm_mul_exp_arg_mul_I z
    rw [← himg]
    have hcont : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * I)) :=
      (Complex.continuous_ofReal.comp continuous_fst).mul
        (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const))
    exact (isPreconnected_Ici.prod isPreconnected_univ).image _ hcont.continuousOn
  have hunbdd : ¬ Bornology.IsBounded {z : ℂ | 1 ≤ ‖z‖} := by
    intro hbdd
    obtain ⟨R, hR⟩ := hbdd.subset_closedBall (0 : ℂ)
    have hRt : R < max R 1 + 1 := by linarith [le_max_left R 1]
    have h1t : (1 : ℝ) ≤ max R 1 + 1 := by linarith [le_max_right R 1]
    have htmem : ((max R 1 + 1 : ℝ) : ℂ) ∈ {z : ℂ | 1 ≤ ‖z‖} := by
      rw [Set.mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < max R 1 + 1)]
      exact h1t
    have hcl := hR htmem
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < max R 1 + 1)] at hcl
    linarith
  have hPpre : IsPreconnected P := by
    rw [hPdef]
    have h1 : IsPreconnected (toExt {z : ℂ | 1 ≤ ‖z‖}) :=
      hP1pre.image _ OnePoint.continuous_coe.continuousOn
    exact h1.subset_closure subset_union_left
      (union_subset subset_closure
        (singleton_subset_iff.2 (extInf_mem_closure_toExt_of_not_isBounded hunbdd)))
  have hPclosed : IsClosed P := by
    have hcomplBall : (ball (0 : ℂ) 1)ᶜ = {z : ℂ | 1 ≤ ‖z‖} := by
      ext z
      simp only [Set.mem_compl_iff, mem_ball_zero_iff, Set.mem_setOf_eq, not_lt]
    have hPeq2 : P = (toExt (ball (0 : ℂ) 1))ᶜ := by
      rw [hPdef, compl_toExt (ball (0 : ℂ) 1), hcomplBall]
    rw [hPeq2]
    exact isClosed_compl_toExt isOpen_ball
  have hPQdisj : Disjoint P Q := by
    rw [Set.disjoint_left]
    intro x hxP hxQ
    rw [hPdef] at hxP
    rw [hQdef] at hxQ
    rcases hxP with ⟨z, hz, rfl⟩ | hxinf
    · obtain ⟨w, ⟨t, ht, rfl⟩, hwx⟩ := hxQ
      have hwz : (t : ℂ) = z := OnePoint.coe_injective hwx
      have ht1 : (1 : ℝ) ≤ t := by
        rw [← hwz] at hz
        simpa [Set.mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ht.1] using hz
      linarith [ht1, ht.2, h₁]
    · rw [Set.mem_singleton_iff] at hxinf
      obtain ⟨w, ⟨t, _, rfl⟩, hwx⟩ := hxQ
      exact OnePoint.coe_ne_infty (t : ℂ) (hwx.trans hxinf)
  -- each component of X is P or Q
  have hsplit : ∀ x ∈ X, connectedComponentIn X x ⊆ P ∨ connectedComponentIn X x ⊆ Q := by
    intro x hx
    have hCpre : IsPreconnected (connectedComponentIn X x) := isPreconnected_connectedComponentIn
    have hCsub : connectedComponentIn X x ⊆ P ∪ Q := hXeq ▸ connectedComponentIn_subset X x
    have hCdisj : connectedComponentIn X x ∩ (P ∩ Q) = ∅ := by
      rw [hPQdisj.inter_eq, inter_empty]
    exact isPreconnected_iff_subset_of_disjoint_closed.mp hCpre P Q hPclosed hQclosed
      hCsub hCdisj
  have hsplitEq : ∀ x ∈ X, connectedComponentIn X x = P ∨ connectedComponentIn X x = Q := by
    intro x hx
    rcases hsplit x hx with h | h
    · left
      exact le_antisymm h (hPpre.subset_connectedComponentIn (h (mem_connectedComponentIn hx))
        (hXeq ▸ subset_union_left))
    · right
      exact le_antisymm h (hQpre.subset_connectedComponentIn (h (mem_connectedComponentIn hx))
        (hXeq ▸ subset_union_right))
  -- the two component classes
  have h2norm : ‖(2 : ℂ)‖ = 2 := by
    have := Complex.norm_natCast 2
    simp
  have h2memP1 : (2 : ℂ) ∈ {z : ℂ | 1 ≤ ‖z‖} := by
    rw [Set.mem_setOf_eq, h2norm]
    norm_num
  have hm2memP1 : (-2 : ℂ) ∈ {z : ℂ | 1 ≤ ‖z‖} := by
    rw [Set.mem_setOf_eq, norm_neg, h2norm]
    norm_num
  have h2memP : ((2 : ℂ) : ExtPlane) ∈ P := by
    rw [hPdef]
    exact Or.inl ⟨(2 : ℂ), h2memP1, rfl⟩
  have hm2memP : ((-2 : ℂ) : ExtPlane) ∈ P := by
    rw [hPdef]
    exact Or.inl ⟨(-2 : ℂ), hm2memP1, rfl⟩
  have h0memQ : ((0 : ℂ) : ExtPlane) ∈ Q := by
    rw [hQdef]
    refine ⟨(0 : ℂ), ⟨(0 : ℝ), ⟨le_refl 0, h₀.le⟩, ?_⟩, rfl⟩
    simp
  have hrmemQ : ((r : ℂ) : ExtPlane) ∈ Q := by
    rw [hQdef]
    refine ⟨(r : ℂ), ⟨r, ⟨h₀.le, le_refl r⟩, ?_⟩, rfl⟩
    simp
  have h2X : ((2 : ℂ) : ExtPlane) ∈ X := hXeq ▸ Or.inl h2memP
  have h0X : ((0 : ℂ) : ExtPlane) ∈ X := hXeq ▸ Or.inr h0memQ
  have hC2 : connectedComponentIn X ((2 : ℂ) : ExtPlane) = P := by
    rcases hsplitEq _ h2X with h | h
    · exact h
    · exfalso
      have : ((2 : ℂ) : ExtPlane) ∈ Q := h ▸ mem_connectedComponentIn h2X
      exact hPQdisj.le_bot ⟨h2memP, this⟩
  have hC0 : connectedComponentIn X ((0 : ℂ) : ExtPlane) = Q := by
    rcases hsplitEq _ h0X with h | h
    · exfalso
      have : ((0 : ℂ) : ExtPlane) ∈ P := h ▸ mem_connectedComponentIn h0X
      exact hPQdisj.le_bot ⟨this, h0memQ⟩
    · exact h
  have h2ne0 : ((2 : ℂ) : ExtPlane) ≠ ((0 : ℂ) : ExtPlane) := by
    intro h
    have h' : (2 : ℂ) = 0 := OnePoint.coe_injective h
    have : (2 : ℝ) = 0 := congrArg Complex.re h'
    norm_num at this
  have h2ne2m : ((2 : ℂ) : ExtPlane) ≠ ((-2 : ℂ) : ExtPlane) := by
    intro h
    have h' : (2 : ℂ) = -2 := OnePoint.coe_injective h
    have : (2 : ℝ) = -2 := congrArg Complex.re h'
    norm_num at this
  have h0ner : ((0 : ℂ) : ExtPlane) ≠ ((r : ℂ) : ExtPlane) := by
    intro h
    have h' : (0 : ℂ) = (r : ℂ) := OnePoint.coe_injective h
    have : (0 : ℝ) = r := by simpa using congrArg Complex.re h'
    linarith
  have hne : connectedComponentIn X ((2 : ℂ) : ExtPlane) ≠
      connectedComponentIn X ((0 : ℂ) : ExtPlane) := by
    rw [hC2, hC0]
    intro heq
    have : ((2 : ℂ) : ExtPlane) ∈ Q := heq ▸ h2memP
    exact hPQdisj.le_bot ⟨h2memP, this⟩
  have hcard : Nat.card (ConnectedComponents ↥X) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨ConnectedComponents.mk ⟨((2 : ℂ) : ExtPlane), h2X⟩,
      ConnectedComponents.mk ⟨((0 : ℂ) : ExtPlane), h0X⟩, ?_, ?_⟩
    · intro hmk
      rw [ConnectedComponents.coe_eq_coe] at hmk
      apply hne
      rw [connectedComponentIn_eq_image h2X, connectedComponentIn_eq_image h0X, hmk]
    · ext c
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      obtain ⟨⟨x, hx⟩, rfl⟩ := ConnectedComponents.surjective_coe c
      rcases hsplitEq x hx with h | h
      · left
        rw [ConnectedComponents.coe_eq_coe]
        apply Set.image_injective.2 Subtype.val_injective
        rw [← connectedComponentIn_eq_image hx, ← connectedComponentIn_eq_image h2X, h, hC2]
      · right
        rw [ConnectedComponents.coe_eq_coe]
        apply Set.image_injective.2 Subtype.val_injective
        rw [← connectedComponentIn_eq_image hx, ← connectedComponentIn_eq_image h0X, h, hC0]
  have hndX : ∀ x ∈ X, connectedComponentIn X x ≠ {x} := by
    intro x hx
    rcases hsplitEq x hx with h | h
    · rw [h]
      intro hsing
      have h2 : ((2 : ℂ) : ExtPlane) ∈ ({x} : Set ExtPlane) := by
        rw [← hsing]
        exact h2memP
      have hm2 : ((-2 : ℂ) : ExtPlane) ∈ ({x} : Set ExtPlane) := by
        rw [← hsing]
        exact hm2memP
      rw [Set.mem_singleton_iff] at h2 hm2
      exact h2ne2m (h2.trans hm2.symm)
    · rw [h]
      intro hsing
      have h0 : ((0 : ℂ) : ExtPlane) ∈ ({x} : Set ExtPlane) := by
        rw [← hsing]
        exact h0memQ
      have hr : ((r : ℂ) : ExtPlane) ∈ ({x} : Set ExtPlane) := by
        rw [← hsing]
        exact hrmemQ
      rw [Set.mem_singleton_iff] at h0 hr
      exact h0ner (h0.trans hr.symm)
  have hnd : ∀ x ∈ (toExt (grotzschDomain r))ᶜ,
      connectedComponentIn (toExt (grotzschDomain r))ᶜ x ≠ {x} := by
    intro x hx
    rw [← hXdef] at hx ⊢
    exact hndX x hx
  have hIsDC : IsDoublyConnected (grotzschDomain r) := by
    refine ⟨hDopen, hDconn, ?_⟩
    rw [hXdef] at hcard
    exact hcard
  obtain ⟨r₁, r₂, hr₁, hr₁₂, heq⟩ := thm2_1_canonical_form_annulus hIsDC hnd
  refine ⟨hIsDC, ?_⟩
  rw [dcModulus_eq_of_equiv (B := grotzschDomain r) hDopen hr₁ hr₁₂ heq]
  exact ENNReal.ofReal_lt_top

/-! ### Theorem 5.1 — helpers -/

open scoped ComplexConjugate


/-! ### Definitions -/

/-- `P(z) = (2z - r(1+z²)) / (r(1+z²) - 2r²z)`.  It maps the upper half-disc onto `ℍ` with
`-1, 0, r, 1 ↦ -1/r, -1, 1, 1/r`. -/
def gzP (r : ℝ) (z : ℂ) : ℂ := (2 * z - r * (1 + z ^ 2)) / (r * (1 + z ^ 2) - 2 * r ^ 2 * z)

/-- `W = F ∘ P`, `F = scMap r` the Schwarz–Christoffel map of modulus `r`. -/
def gzW (r : ℝ) (z : ℂ) : ℂ := scMap r (gzP r z)

/-- Folding into the closed upper half-plane. -/
def gzFold (z : ℂ) : ℂ := if 0 ≤ z.im then z else conj z

/-- The height function `Y = Im W ∘ fold`: `0` on `(-1,0)`, `b` on `(r,1)`. -/
def gzY (r : ℝ) (z : ℂ) : ℝ := (gzW r (gzFold z)).im

/-- The symmetric extremal density `ρ = |W' ∘ fold| / (2b)`, set to `∞` on the real axis. -/
def gzRho (r : ℝ) (z : ℂ) : ℝ≥0∞ :=
  if z.im = 0 then ⊤ else ENNReal.ofReal (‖deriv (gzW r) (gzFold z)‖ / (2 * scSideB r))

/-- The conformal map of the Grötzsch domain onto an annulus, glued along the real axis. -/
def gzG (r : ℝ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then exp (-((π / scSideB r : ℝ) : ℂ) * (gzW r z - scSideA r))
  else conj (exp (-((π / scSideB r : ℝ) : ℂ) * (gzW r (conj z) - scSideA r)))

/-! ### Piece A: the map `P` -/

/-- Membership in the unit disc in coordinates. -/
theorem gzA_mem_unitDisc_iff {z : ℂ} : z ∈ unitDisc ↔ z.re * z.re + z.im * z.im < 1 := by
  rw [unitDisc, Metric.mem_ball, dist_zero_right, ← Complex.normSq_apply, ← Complex.sq_norm]
  exact (sq_lt_one_iff₀ (norm_nonneg z)).symm

theorem gzP_den_ne_zero {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {z : ℂ} (hz : z ∈ unitDisc) :
    (r : ℂ) * (1 + z ^ 2) - 2 * (r : ℂ) ^ 2 * z ≠ 0 := by
  rw [gzA_mem_unitDisc_iff] at hz
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have h2 : z.im * (z.re - r) = 0 := by
    have : r * (2 * (z.im * (z.re - r))) = 0 := by linear_combination him
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hr₀.ne'
    · linarith
  rcases mul_eq_zero.mp h2 with h | h
  · rw [h] at hre
    nlinarith [sq_nonneg (z.re - r), mul_pos hr₀ (sub_pos.mpr hr₁)]
  · have hx : z.re = r := by linarith
    rw [hx] at hre hz
    nlinarith

theorem gzP_differentiableOn {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    DifferentiableOn ℂ (gzP r) unitDisc := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  show DifferentiableAt ℂ
    (fun z : ℂ => (2 * z - r * (1 + z ^ 2)) / (r * (1 + z ^ 2) - 2 * (r : ℂ) ^ 2 * z)) z
  exact DifferentiableAt.div (by fun_prop) (by fun_prop) (gzP_den_ne_zero hr₀ hr₁ hz)

theorem gzP_conj {r : ℝ} (z : ℂ) : gzP r (conj z) = conj (gzP r z) := by
  simp [gzP, map_div₀, map_sub, map_mul, map_add, map_pow, Complex.conj_ofReal, map_ofNat]

theorem gzP_im_pos {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {z : ℂ} (hz : z ∈ unitDisc)
    (him : 0 < z.im) : 0 < (gzP r z).im := by
  have hD := gzP_den_ne_zero hr₀ hr₁ hz
  rw [gzA_mem_unitDisc_iff] at hz
  have hDpos : 0 < Complex.normSq ((r : ℂ) * (1 + z ^ 2) - 2 * (r : ℂ) ^ 2 * z) :=
    Complex.normSq_pos.mpr hD
  have e : (2 * z - r * (1 + z ^ 2)).im * ((r : ℂ) * (1 + z ^ 2) - 2 * (r : ℂ) ^ 2 * z).re -
      (2 * z - r * (1 + z ^ 2)).re * ((r : ℂ) * (1 + z ^ 2) - 2 * (r : ℂ) ^ 2 * z).im =
      2 * r * (1 - r ^ 2) * z.im * (1 - (z.re * z.re + z.im * z.im)) := by
    simp [pow_two]; ring
  unfold gzP
  rw [Complex.div_im, ← sub_div, e]
  apply div_pos _ hDpos
  have h1 : 0 < 1 - r ^ 2 := by nlinarith
  have h2 : 0 < 1 - (z.re * z.re + z.im * z.im) := by linarith
  positivity

theorem gzP_zero {r : ℝ} (hr₀ : 0 < r) : gzP r 0 = -1 := by
  have : (r : ℂ) ≠ 0 := by exact_mod_cast hr₀.ne'
  simp [gzP, this]

theorem gzP_self {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) : gzP r r = 1 := by
  have h : ((r * (1 + r ^ 2) - 2 * r ^ 2 * r : ℝ) : ℂ) ≠ 0 := by
    have : 0 < r * (1 + r ^ 2) - 2 * r ^ 2 * r := by nlinarith [mul_pos hr₀ hr₀]
    exact_mod_cast this.ne'
  push_cast at h
  unfold gzP
  rw [div_eq_one_iff_eq h]
  ring

/-- On `(-1,1)` the map is real, with `(-1,0) → (-1/r,-1)`, `(0,r) → (-1,1)`, `(r,1) → (1,1/r)`. -/
theorem gzP_ofReal {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∃ y : ℝ, gzP r x = y ∧ (x < 0 → y ∈ Ioo (-1 / r) (-1)) ∧ (0 < x → x < r → y ∈ Ioo (-1) 1) ∧
      (r < x → y ∈ Ioo 1 (1 / r)) := by
  obtain ⟨hx₀, hx₁⟩ := hx
  have hD : 0 < r * (1 + x ^ 2) - 2 * r ^ 2 * x := by
    nlinarith [sq_nonneg (x - r), mul_pos hr₀ (sub_pos.mpr hr₁)]
  have hr2 : 0 < 1 - r ^ 2 := by nlinarith
  refine ⟨(2 * x - r * (1 + x ^ 2)) / (r * (1 + x ^ 2) - 2 * r ^ 2 * x), ?_, ?_, ?_, ?_⟩
  · simp [gzP]
  · intro hx0
    constructor
    · rw [div_lt_div_iff₀ hr₀ hD]
      nlinarith [mul_pos (sub_pos.mpr hr₁) (mul_pos (by linarith : 0 < x + 1) (by linarith : 0 < x + 1))]
    · rw [div_lt_iff₀ hD]
      nlinarith [mul_pos hr2 (by linarith : 0 < -x)]
  · intro hx0 hxr
    constructor
    · rw [lt_div_iff₀ hD]
      nlinarith [mul_pos hr2 hx0]
    · rw [div_lt_iff₀ hD]
      have : 0 < 1 - r * x := by nlinarith
      nlinarith [mul_pos this (sub_pos.mpr hxr)]
  · intro hxr
    constructor
    · rw [lt_div_iff₀ hD]
      have : 0 < 1 - r * x := by nlinarith
      nlinarith [mul_pos this (sub_pos.mpr hxr)]
    · rw [div_lt_div_iff₀ hD hr₀]
      nlinarith [mul_pos (mul_pos hr₀ (by linarith : (0:ℝ) < 1 + r))
        (mul_pos (by linarith : 0 < 1 - x) (by linarith : 0 < 1 - x))]

/-- For a root of `z² - 2wz + 1 = 0`: `Im z · (|z|² - 1) = 2 Im w · |z|²`. -/
theorem gzA_root_im {w z : ℂ} (h : z ^ 2 - 2 * w * z + 1 = 0) :
    z.im * (z.re * z.re + z.im * z.im - 1) = 2 * w.im * (z.re * z.re + z.im * z.im) := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  linear_combination (-z.im) * hre + z.re * him

/-- If `Im w < 0`, then `z² - 2wz + 1 = 0` has a root in the upper half-disc. -/
theorem gzA_exists_root {w : ℂ} (hw : w.im < 0) :
    ∃ z : ℂ, z ∈ unitDisc ∧ 0 < z.im ∧ z ^ 2 - 2 * w * z + 1 = 0 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (w ^ 2 - 1)
  have h0 : (w + s) ^ 2 - 2 * w * (w + s) + 1 = 0 := by linear_combination -hs
  have hne : w + s ≠ 0 := by
    intro h; rw [h] at h0; norm_num at h0
  -- a root of modulus `< 1`
  have key : ∃ z : ℂ, z.re * z.re + z.im * z.im < 1 ∧ z ^ 2 - 2 * w * z + 1 = 0 := by
    rcases lt_trichotomy (Complex.normSq (w + s)) 1 with hlt | heq | hgt
    · exact ⟨w + s, by rwa [← Complex.normSq_apply], h0⟩
    · exfalso
      have := gzA_root_im h0
      rw [← Complex.normSq_apply, heq] at this
      linarith
    · refine ⟨(w + s)⁻¹, ?_, ?_⟩
      · rw [← Complex.normSq_apply, Complex.normSq_inv]
        exact inv_lt_one_of_one_lt₀ hgt
      · field_simp
        linear_combination h0
  obtain ⟨z, hz1, hz⟩ := key
  refine ⟨z, gzA_mem_unitDisc_iff.mpr hz1, ?_, hz⟩
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; norm_num at hz
  have hn : 0 < z.re * z.re + z.im * z.im := by
    rw [← Complex.normSq_apply]; exact Complex.normSq_pos.mpr hz0
  have := gzA_root_im hz
  nlinarith [mul_pos (by linarith : 0 < -w.im) hn]

/-- `P` is a conformal bijection of the upper half-disc onto `ℍ`. -/
theorem gzP_isConformalOnto {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    IsConformalOnto (gzP r) (unitDisc ∩ upperHalf) upperHalf := by
  have hr : (r : ℂ) ≠ 0 := by exact_mod_cast hr₀.ne'
  have hr2 : ((1 - r ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < 1 - r ^ 2 := by nlinarith
    exact_mod_cast this.ne'
  push_cast at hr2
  refine ⟨(gzP_differentiableOn hr₀ hr₁).mono inter_subset_left, ?_, ?_⟩
  · intro z₁ hz₁ z₂ hz₂ h
    have hD₁ := gzP_den_ne_zero hr₀ hr₁ hz₁.1
    have hD₂ := gzP_den_ne_zero hr₀ hr₁ hz₂.1
    unfold gzP at h
    rw [div_eq_div_iff hD₁ hD₂] at h
    have hf : (2 * r * (1 - r ^ 2)) * ((z₁ - z₂) * (1 - z₁ * z₂)) = (0 : ℂ) := by
      linear_combination h
    have h2 : (2 * r * (1 - r ^ 2) : ℂ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hr) hr2
    rcases mul_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left h2) with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have h1 : z₁ * z₂ = 1 := by linear_combination -h
      have a₁ := gzA_mem_unitDisc_iff.mp hz₁.1
      have a₂ := gzA_mem_unitDisc_iff.mp hz₂.1
      rw [← Complex.normSq_apply] at a₁ a₂
      have := congrArg Complex.normSq h1
      rw [Complex.normSq_mul, Complex.normSq_one] at this
      nlinarith [Complex.normSq_nonneg z₁, Complex.normSq_nonneg z₂]
  · ext ζ
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact gzP_im_pos hr₀ hr₁ hz.1 hz.2
    · intro hζ
      have hζ' : 0 < ζ.im := hζ
      have h1ζ : (1 + ζ) ≠ 0 := by
        intro h; have := congrArg Complex.im h; simp at this; linarith
      obtain ⟨w, hwdef⟩ : ∃ w : ℂ, w = (1 + r ^ 2 * ζ) / (r * (1 + ζ)) := ⟨_, rfl⟩
      have hw : w.im < 0 := by
        have hden : (r * (1 + ζ) : ℂ) ≠ 0 := mul_ne_zero hr h1ζ
        have hpos := Complex.normSq_pos.mpr hden
        rw [hwdef, Complex.div_im, ← sub_div]
        apply div_neg_of_neg_of_pos _ hpos
        have e : (1 + (r : ℂ) ^ 2 * ζ).im * ((r : ℂ) * (1 + ζ)).re -
            (1 + (r : ℂ) ^ 2 * ζ).re * ((r : ℂ) * (1 + ζ)).im = r * ζ.im * (r ^ 2 - 1) := by
          simp [pow_two]; ring
        rw [e]
        have : r ^ 2 - 1 < 0 := by nlinarith
        have := mul_pos hr₀ hζ'
        nlinarith
      obtain ⟨z, hz, hzim, hzeq⟩ := gzA_exists_root hw
      refine ⟨z, ⟨hz, hzim⟩, ?_⟩
      have hD := gzP_den_ne_zero hr₀ hr₁ hz
      have hwr : (r : ℂ) * (1 + ζ) * w = 1 + r ^ 2 * ζ := by
        rw [hwdef]; field_simp
      unfold gzP
      rw [div_eq_iff hD]
      linear_combination (-(r : ℂ) * (1 + ζ)) * hzeq - 2 * z * hwr

/-! ### Piece B: the Schwarz–Christoffel side -/

/-- A ball around a real point whose radius is at most the distance to every prevertex lies in the
slit domain `scSlitDomain k`. -/
theorem gzB_ball_subset_slitDomain {k x ε : ℝ} (hε : ∀ j, ε ≤ |x - scPrevertex k j|) :
    ball (x : ℂ) ε ⊆ scSlitDomain k := by
  intro ζ hζ j s _ heq
  have h1 := hε j
  rw [mem_ball, heq, dist_eq_norm] at hζ
  have hre : |((scPrevertex k j : ℂ) - s * I - x).re| ≤ ‖(scPrevertex k j : ℂ) - s * I - x‖ :=
    abs_re_le_norm _
  have hre' : ((scPrevertex k j : ℂ) - s * I - x).re = scPrevertex k j - x := by simp
  rw [hre', abs_sub_comm] at hre
  linarith

/-- `scMap` continues holomorphically across every real non-prevertex. -/
theorem gz_scMap_local_ext {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) {x : ℝ}
    (hx : ∀ j, x ≠ scPrevertex k j) :
    ∃ ε > 0, ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball (x : ℂ) ε) ∧
      ∀ ζ ∈ ball (x : ℂ) ε, 0 ≤ ζ.im → H ζ = scMap k ζ := by
  obtain ⟨g, hg, hgeq⟩ := exists_scIntegrand_slitExt hk₀ hk₁
  set ε := min (min |x - scPrevertex k 0| |x - scPrevertex k 1|)
    (min |x - scPrevertex k 2| |x - scPrevertex k 3|) with hεdef
  have hpos : ∀ j, 0 < |x - scPrevertex k j| := fun j => abs_pos.2 (sub_ne_zero.2 (hx j))
  have hε : 0 < ε := lt_min (lt_min (hpos 0) (hpos 1)) (lt_min (hpos 2) (hpos 3))
  have hεle : ∀ j, ε ≤ |x - scPrevertex k j| := by
    intro j
    fin_cases j
    · exact (min_le_left _ _).trans (min_le_left _ _)
    · exact (min_le_left _ _).trans (min_le_right _ _)
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hsub := gzB_ball_subset_slitDomain hεle
  have hx0 : (x : ℂ) ∈ ball (x : ℂ) ε := mem_ball_self hε
  haveI : ContractibleSpace (ball (x : ℂ) ε) := (convex_ball (x : ℂ) ε).contractibleSpace ⟨_, hx0⟩
  obtain ⟨G, hG, hGd⟩ := RMT.exists_primitive_of_simplyConnected isOpen_ball
    ((convex_ball (x : ℂ) ε).isConnected ⟨_, hx0⟩) (hg.mono hsub)
  set U := ball (x : ℂ) ε ∩ upperHalf with hU
  have hUo : IsOpen U := isOpen_ball.inter isOpen_upperHalf'
  have hUc : IsPreconnected U := ((convex_ball (x : ℂ) ε).inter convex_upperHalf).isPreconnected
  have hderiv : ∀ z ∈ U, HasDerivAt (fun z => G z - scMap k z) 0 z := by
    intro z hz
    have hGz : HasDerivAt G (g z) z := by
      have h := (hG.differentiableAt (isOpen_ball.mem_nhds hz.1)).hasDerivAt
      rwa [hGd z hz.1] at h
    have hz' : 0 < z.im := hz.2
    have hne : ∀ j, z ≠ (scPrevertex k j : ℂ) := fun j h => by
      have := congrArg Complex.im h
      simp only [ofReal_im] at this
      linarith
    have h := hGz.sub (hasDerivAt_scMap hk₀ hk₁ hz.2)
    rwa [hgeq z hz'.le hne, sub_self] at h
  obtain ⟨c, hc⟩ := hUo.exists_is_const_of_deriv_eq_zero hUc
    (fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hderiv z hz).deriv)
  refine ⟨ε, hε, fun z => G z - c, hG.sub_const c, ?_⟩
  have hEq : EqOn (fun z => G z - c) (scMap k) U := fun z hz => by
    have := hc z hz
    simp only at this ⊢
    linear_combination this
  have hcl : ball (x : ℂ) ε ∩ {z | 0 ≤ z.im} ⊆ closure U := by
    intro z hz
    have ht : Tendsto (fun t : ℝ => z + (t : ℂ) * I) (𝓝[>] 0) (𝓝 z) := by
      have hcont : Continuous (fun t : ℝ => z + (t : ℂ) * I) := by fun_prop
      have h := hcont.tendsto 0
      simp only [ofReal_zero, zero_mul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    have h1 : ∀ᶠ (t : ℝ) in 𝓝[>] (0 : ℝ), z + (t : ℂ) * I ∈ ball (x : ℂ) ε :=
      ht.eventually (isOpen_ball.mem_nhds hz.1)
    filter_upwards [h1, self_mem_nhdsWithin] with t ht1 ht2
    refine ⟨ht1, ?_⟩
    show 0 < (z + (t : ℂ) * I).im
    have hz2 : 0 ≤ z.im := hz.2
    have ht2' : 0 < t := ht2
    simp only [add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul, add_zero]
    linarith
  intro ζ hζ hζim
  refine hEq.of_subset_closure ?_ ?_ ?_ hcl ⟨hζ, hζim⟩
  · exact (hG.sub_const c).continuousOn.mono inter_subset_left
  · exact (continuousOn_scMap hk₀ hk₁).mono inter_subset_right
  · exact fun z hz => ⟨hz.1, (show 0 < z.im from hz.2).le⟩

theorem gzW_differentiableAt {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {z : ℂ} (hz : z ∈ unitDisc)
    (him : 0 < z.im) : DifferentiableAt ℂ (gzW r) z := by
  have hDo : IsOpen unitDisc := Metric.isOpen_ball
  have hP := (gzP_differentiableOn hr₀ hr₁).differentiableAt (hDo.mem_nhds hz)
  exact (hasDerivAt_scMap hr₀ hr₁ (gzP_im_pos hr₀ hr₁ hz him)).differentiableAt.comp z hP

/-- `W` continues holomorphically across every real point of `Δ` other than `0` and `r`. -/
theorem gzW_local_ext {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1)
    (hx0 : x ≠ 0) (hxr : x ≠ r) :
    ∃ ε > 0, ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball (x : ℂ) ε) ∧ ball (x : ℂ) ε ⊆ unitDisc ∧
      ∀ z ∈ ball (x : ℂ) ε, 0 ≤ z.im → H z = gzW r z := by
  obtain ⟨y, hy, hyl, hym, hyr⟩ := gzP_ofReal hr₀ hr₁ hx
  have hDo : IsOpen unitDisc := Metric.isOpen_ball
  have hy_np : ∀ j, y ≠ scPrevertex r j := by
    intro j hj
    rcases lt_or_gt_of_ne hx0 with h0 | h0
    · exact scNoPrevertex_bottom hr₀ hr₁ j (by rw [← hj]; exact hyl h0)
    · rcases lt_or_gt_of_ne hxr with h1 | h1
      · exact scNoPrevertex_right hr₀ hr₁ j (by rw [← hj]; exact hym h0 h1)
      · exact scNoPrevertex_top hr₀ hr₁ j (by rw [← hj]; exact hyr h1)
  obtain ⟨ε₁, hε₁, H₁, hH₁, hH₁eq⟩ := gz_scMap_local_ext hr₀ hr₁ hy_np
  have hxD : (x : ℂ) ∈ unitDisc := by
    rw [unitDisc, mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    exact ⟨hx.1, hx.2⟩
  have hPd := gzP_differentiableOn hr₀ hr₁
  have hPc : ContinuousAt (gzP r) x := (hPd.differentiableAt (hDo.mem_nhds hxD)).continuousAt
  have hnhds : gzP r ⁻¹' ball (y : ℂ) ε₁ ∩ unitDisc ∈ 𝓝 (x : ℂ) := by
    refine Filter.inter_mem (hPc.preimage_mem_nhds ?_) (hDo.mem_nhds hxD)
    rw [hy]
    exact isOpen_ball.mem_nhds (mem_ball_self hε₁)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hnhds
  refine ⟨δ, hδ, H₁ ∘ gzP r, ?_, fun z hz => (hδsub hz).2, ?_⟩
  · exact hH₁.comp (hPd.mono fun z hz => (hδsub hz).2) fun z hz => (hδsub hz).1
  · intro z hz hzim
    have hzD := (hδsub hz).2
    have him : 0 ≤ (gzP r z).im := by
      rcases hzim.lt_or_eq with h | h
      · exact (gzP_im_pos hr₀ hr₁ hzD h).le
      · have hzr : z = (z.re : ℂ) := by
          apply Complex.ext <;> simp [← h]
        have hre : z.re ∈ Ioo (-1 : ℝ) 1 := by
          have h2 := hzD
          rw [unitDisc, mem_ball, dist_zero_right, hzr, Complex.norm_real, Real.norm_eq_abs,
            abs_lt] at h2
          exact ⟨h2.1, h2.2⟩
        obtain ⟨y', hy', -⟩ := gzP_ofReal hr₀ hr₁ hre
        rw [hzr, hy', ofReal_im]
    exact hH₁eq _ (hδsub hz).1 him

theorem gzW_isConformalOnto {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    IsConformalOnto (gzW r) (unitDisc ∩ upperHalf) (rectangle (scSideA r) (scSideB r)) := by
  exact IsConformalOnto.comp (isConformalOnto_scMap hr₀ hr₁) (gzP_isConformalOnto hr₀ hr₁)

/-- Boundary values of `W` on the real axis. -/
theorem gzW_ofReal {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {x : ℝ} :
    (x ∈ Ioo (-1 : ℝ) 0 → (gzW r x).im = 0 ∧ (gzW r x).re ∈ Ioo 0 (scSideA r)) ∧
    (x ∈ Ioo 0 r → (gzW r x).re = scSideA r) ∧
    (x ∈ Ioo r 1 → (gzW r x).im = scSideB r ∧ (gzW r x).re ∈ Ioo 0 (scSideA r)) := by
  have h1k : 1 < 1 / r := one_lt_one_div hr₀ hr₁
  have hlt : -1 / r < -1 := by rw [show -1 / r = -(1 / r) by ring]; linarith
  have hA : scSideA r = ∫ s in (-1 / r)..(-1), scDensity r s := by
    rw [integral_scDensity_bottom, scSideA_eq_integral_scDensity hr₀ hr₁]
  refine ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_⟩
  · have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨hx.1, hx.2.trans one_pos⟩
    obtain ⟨y, hy, hyl, -, -⟩ := gzP_ofReal hr₀ hr₁ hx'
    have hy1 := hyl hx.2
    have hW : gzW r x = ((∫ s in (-1 / r)..y, scDensity r s : ℝ) : ℂ) := by
      unfold gzW
      rw [hy, scMap_ofReal_bottom hr₀ hr₁ ⟨hy1.1.le, hy1.2.le⟩]
    rw [hW, ofReal_im, ofReal_re]
    refine ⟨rfl, ?_, ?_⟩
    · exact integral_scDensity_pos hr₀ hr₁ hy1.1 fun j hj =>
        scNoPrevertex_bottom hr₀ hr₁ j ⟨hj.1, hj.2.trans hy1.2⟩
    · rw [hA]
      exact integral_scDensity_strictMonoOn hr₀ hr₁ (scNoPrevertex_bottom hr₀ hr₁) _
        ⟨hy1.1.le, hy1.2.le⟩ ⟨hlt.le, le_rfl⟩ hy1.2
  · obtain ⟨y, hy, -, hym, -⟩ := gzP_ofReal hr₀ hr₁ ⟨by linarith [hx.1], hx.2.trans hr₁⟩
    have hy1 := hym hx.1 hx.2
    unfold gzW
    rw [hy, scMap_ofReal_right hr₀ hr₁ ⟨hy1.1.le, hy1.2.le⟩]
    simp
  · obtain ⟨y, hy, -, -, hyr⟩ := gzP_ofReal hr₀ hr₁ ⟨by linarith [hx.1], hx.2⟩
    have hy1 := hyr hx.1
    unfold gzW
    rw [hy, scMap_ofReal_top hr₀ hr₁ ⟨hy1.1.le, hy1.2.le⟩]
    have hlt' := integral_scDensity_strictMonoOn hr₀ hr₁ (scNoPrevertex_top hr₀ hr₁) 1
      ⟨hy1.1.le, hy1.2.le⟩ ⟨h1k.le, le_rfl⟩ hy1.2
    have hpos := integral_scDensity_pos hr₀ hr₁ hy1.1 fun j hj =>
      scNoPrevertex_top hr₀ hr₁ j ⟨hj.1, hj.2.trans hy1.2⟩
    simp only at hlt'
    rw [← scSideA_eq_integral_scDensity hr₀ hr₁] at hlt'
    simp only [sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_add, mem_Ioo]
    refine ⟨trivial, ?_, ?_⟩ <;> linarith

/-- `P` on the real axis, in real form. -/
theorem gzB_gzP_ofReal_eq (r x : ℝ) :
    gzP r x = (((2 * x - r * (1 + x ^ 2)) / (r * (1 + x ^ 2) - 2 * r ^ 2 * x) : ℝ) : ℂ) := by
  unfold gzP
  push_cast
  ring

/-- The denominator of `P` is positive on the real line. -/
theorem gzB_den_pos {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) (x : ℝ) :
    0 < r * (1 + x ^ 2) - 2 * r ^ 2 * x := by
  have h : r * (1 + x ^ 2) - 2 * r ^ 2 * x = r * ((x - r) ^ 2 + (1 - r ^ 2)) := by ring
  rw [h]
  apply mul_pos hr₀
  nlinarith [sq_nonneg (x - r)]

/-- `x ↦ W(x)` is continuous on the real line. -/
theorem gzB_continuous_W_ofReal {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    Continuous fun x : ℝ => gzW r x := by
  have hp : Continuous fun x : ℝ =>
      (2 * x - r * (1 + x ^ 2)) / (r * (1 + x ^ 2) - 2 * r ^ 2 * x) :=
    Continuous.div (by fun_prop) (by fun_prop) fun x => (gzB_den_pos hr₀ hr₁ x).ne'
  have h : (fun x : ℝ => gzW r x) = scMap r ∘ fun x : ℝ =>
      (((2 * x - r * (1 + x ^ 2)) / (r * (1 + x ^ 2) - 2 * r ^ 2 * x) : ℝ) : ℂ) := by
    funext x
    simp only [Function.comp, gzW, gzB_gzP_ofReal_eq]
  rw [h]
  exact (continuousOn_scMap hr₀ hr₁).comp_continuous (continuous_ofReal.comp hp) fun x =>
    (ofReal_im _).ge

/-- `W` maps `(-1,0)` onto the bottom side and `(r,1)` onto the top side. -/
theorem gzW_ofReal_surj {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {t : ℝ} (ht : t ∈ Ioo 0 (scSideA r)) :
    (∃ x ∈ Ioo (-1 : ℝ) 0, gzW r x = t) ∧
      (∃ x ∈ Ioo r 1, gzW r x = (t : ℂ) + (scSideB r : ℂ) * I) := by
  have hcre : Continuous fun x : ℝ => (gzW r x).re :=
    continuous_re.comp (gzB_continuous_W_ofReal hr₀ hr₁)
  have hval : ∀ x : ℝ, gzW r x =
      scMap r (((2 * x - r * (1 + x ^ 2)) / (r * (1 + x ^ 2) - 2 * r ^ 2 * x) : ℝ) : ℂ) := by
    intro x
    unfold gzW
    rw [gzB_gzP_ofReal_eq]
  have hr0 : r ≠ 0 := hr₀.ne'
  have hm1 : (gzW r ((-1 : ℝ) : ℂ)).re = 0 := by
    have h : (2 * (-1 : ℝ) - r * (1 + (-1) ^ 2)) / (r * (1 + (-1 : ℝ) ^ 2) - 2 * r ^ 2 * (-1)) =
        scPrevertex r 0 := by
      rw [div_eq_iff (gzB_den_pos hr₀ hr₁ _).ne', scPrevertex_zero]
      field_simp
      ring
    rw [hval, h, (scMap_prevertices hr₀ hr₁).1, zero_re]
  have h0 : (gzW r ((0 : ℝ) : ℂ)).re = scSideA r := by
    have h : (2 * (0 : ℝ) - r * (1 + 0 ^ 2)) / (r * (1 + (0 : ℝ) ^ 2) - 2 * r ^ 2 * 0) =
        scPrevertex r 1 := by
      rw [div_eq_iff (gzB_den_pos hr₀ hr₁ _).ne', scPrevertex_one]
      ring
    rw [hval, h, (scMap_prevertices hr₀ hr₁).2.1, ofReal_re]
  have hrr : (gzW r (r : ℂ)).re = scSideA r := by
    have h : (2 * r - r * (1 + r ^ 2)) / (r * (1 + r ^ 2) - 2 * r ^ 2 * r) =
        scPrevertex r 2 := by
      rw [div_eq_iff (gzB_den_pos hr₀ hr₁ _).ne', scPrevertex_two]
      ring
    rw [hval, h, (scMap_prevertices hr₀ hr₁).2.2.1]
    simp
  have h1 : (gzW r ((1 : ℝ) : ℂ)).re = 0 := by
    have h : (2 * (1 : ℝ) - r * (1 + 1 ^ 2)) / (r * (1 + (1 : ℝ) ^ 2) - 2 * r ^ 2 * 1) =
        scPrevertex r 3 := by
      rw [div_eq_iff (gzB_den_pos hr₀ hr₁ _).ne', scPrevertex_three]
      field_simp
      ring
    rw [hval, h, (scMap_prevertices hr₀ hr₁).2.2.2]
    simp
  constructor
  · have hivt := intermediate_value_Ioo (show (-1 : ℝ) ≤ 0 by norm_num) hcre.continuousOn
    rw [hm1, h0] at hivt
    obtain ⟨x, hx, hxt⟩ := hivt ht
    refine ⟨x, hx, Complex.ext ?_ ?_⟩
    · simpa using hxt
    · rw [((gzW_ofReal hr₀ hr₁).1 hx).1, ofReal_im]
  · have hivt := intermediate_value_Ioo' hr₁.le hcre.continuousOn
    rw [hrr, h1] at hivt
    obtain ⟨x, hx, hxt⟩ := hivt ht
    refine ⟨x, hx, Complex.ext ?_ ?_⟩
    · simpa using hxt
    · rw [((gzW_ofReal hr₀ hr₁).2.2 hx).1]
      simp

/-! ### Piece C: the height function `Y` -/

/-- The fold fixes real points. -/
theorem gzC_fold_ofReal (x : ℝ) : gzFold (x : ℂ) = x := by
  simp [gzFold]

theorem gzY_left {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 0) :
    gzY r x = 0 := by
  rw [gzY, gzC_fold_ofReal]
  exact ((gzW_ofReal hr₀ hr₁ (x := x)).1 hx).1

theorem gzY_right {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {x : ℝ} (hx : x ∈ Ioo r 1) :
    gzY r x = scSideB r := by
  rw [gzY, gzC_fold_ofReal]
  exact ((gzW_ofReal hr₀ hr₁ (x := x)).2.2 hx).1

/-- The fold is `z ↦ re z + i |im z|`. -/
theorem gzC_fold_re_im (z : ℂ) : (gzFold z).re = z.re ∧ (gzFold z).im = |z.im| := by
  unfold gzFold
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (not_le.mp h)]

/-- The fold lands in the closed upper half-plane. -/
theorem gzC_fold_im_nonneg (z : ℂ) : 0 ≤ (gzFold z).im := by
  rw [(gzC_fold_re_im z).2]; exact abs_nonneg _

/-- The fold is `1`-Lipschitz. -/
theorem gzC_fold_lipschitz : LipschitzWith 1 gzFold := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [NNReal.coe_one, one_mul, Complex.dist_eq_re_im, Complex.dist_eq_re_im,
    (gzC_fold_re_im z).1, (gzC_fold_re_im z).2, (gzC_fold_re_im w).1, (gzC_fold_re_im w).2]
  apply Real.sqrt_le_sqrt
  have h : (|z.im| - |w.im|) ^ 2 ≤ (z.im - w.im) ^ 2 :=
    sq_le_sq.mpr (abs_abs_sub_abs_le_abs_sub _ _)
  linarith

/-- The fold maps `Δ ∖ {0, r}` into itself. -/
theorem gzC_fold_mem {r : ℝ} {z : ℂ} (hz : z ∈ unitDisc \ {0, (r : ℂ)}) :
    gzFold z ∈ unitDisc \ {0, (r : ℂ)} := by
  unfold gzFold
  split_ifs with h
  · exact hz
  · refine ⟨?_, ?_⟩
    · have h1 := hz.1
      simp only [unitDisc, mem_ball_zero_iff] at h1 ⊢
      rwa [Complex.norm_conj]
    · rintro (h' | h')
      · exact hz.2 (Or.inl (by simpa using h'))
      · exact hz.2 (Or.inr (by rw [← conj_conj z, h', conj_ofReal]; exact mem_singleton _))

/-- Near every point of the closed upper half-disc other than `0, r`, `W` agrees on the closed
upper half-plane with a function holomorphic on a ball. -/
theorem gzC_local {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {w₀ : ℂ}
    (hw : w₀ ∈ unitDisc \ {0, (r : ℂ)}) (him : 0 ≤ w₀.im) :
    ∃ ε > 0, ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball w₀ ε) ∧
      ∀ w ∈ ball w₀ ε, 0 ≤ w.im → H w = gzW r w := by
  rcases him.lt_or_eq with hpos | hzero
  · have hn : ‖w₀‖ < 1 := mem_ball_zero_iff.1 hw.1
    refine ⟨min (1 - ‖w₀‖) w₀.im, lt_min (by linarith) hpos, gzW r, ?_, fun w _ _ => rfl⟩
    intro w hw'
    rw [mem_ball, dist_eq_norm] at hw'
    have h1 : ‖w - w₀‖ < 1 - ‖w₀‖ := hw'.trans_le (min_le_left _ _)
    have h2 : ‖w - w₀‖ < w₀.im := hw'.trans_le (min_le_right _ _)
    have hwD : w ∈ unitDisc := by
      show w ∈ ball (0 : ℂ) 1
      rw [mem_ball_zero_iff]
      have := norm_sub_norm_le w w₀
      linarith
    have him' : 0 < w.im := by
      have h3 := abs_im_le_norm (w - w₀)
      rw [sub_im] at h3
      have := (abs_le.1 h3).1
      linarith
    exact (gzW_differentiableAt hr₀ hr₁ hwD him').differentiableWithinAt
  · have hw₀ : w₀ = ((w₀.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hzero.symm])
    have hx : w₀.re ∈ Ioo (-1 : ℝ) 1 := by
      have h1 : ‖w₀‖ < 1 := mem_ball_zero_iff.1 hw.1
      rw [hw₀, Complex.norm_real, Real.norm_eq_abs] at h1
      exact abs_lt.1 h1
    have hx0 : w₀.re ≠ 0 := fun h => hw.2 (Or.inl (by rw [hw₀, h, ofReal_zero]))
    have hxr : w₀.re ≠ r := fun h => hw.2 (Or.inr (by rw [hw₀, h]; exact mem_singleton _))
    obtain ⟨ε, hε, H, hH, -, hHe⟩ := gzW_local_ext hr₀ hr₁ hx hx0 hxr
    rw [← hw₀] at hH hHe
    exact ⟨ε, hε, H, hH, hHe⟩

/-- `Im W` is Lipschitz near every point of the closed upper half-disc other than `0, r`,
relative to the closed upper half-plane. -/
theorem gzC_Wim_lip {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {w₀ : ℂ}
    (hw : w₀ ∈ unitDisc \ {0, (r : ℂ)}) (him : 0 ≤ w₀.im) :
    ∃ K : ℝ≥0, ∃ V ∈ 𝓝 w₀, LipschitzOnWith K (fun w => (gzW r w).im) (V ∩ {w | 0 ≤ w.im}) := by
  obtain ⟨ε, hε, H, hH, hHe⟩ := gzC_local hr₀ hr₁ hw him
  have hcd : ContDiffAt ℂ 1 H w₀ := (hH.analyticAt (ball_mem_nhds w₀ hε)).contDiffAt
  obtain ⟨K, V, hV, hlip⟩ := hcd.exists_lipschitzOnWith
  refine ⟨K, V ∩ ball w₀ ε, inter_mem hV (ball_mem_nhds w₀ hε), ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun w hw w' hw' => ?_
  rw [← hHe w hw.1.2 hw.2, ← hHe w' hw'.1.2 hw'.2, Real.dist_eq, ← sub_im]
  refine (abs_im_le_norm _).trans ?_
  rw [← dist_eq_norm]
  exact hlip.dist_le_mul w hw.1.1 w' hw'.1.1

theorem gzY_locallyLipschitzOn {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    LocallyLipschitzOn (unitDisc \ {0, (r : ℂ)}) (gzY r) := by
  intro z hz
  obtain ⟨K, V, hV, hlip⟩ := gzC_Wim_lip hr₀ hr₁ (gzC_fold_mem hz) (gzC_fold_im_nonneg z)
  refine ⟨K * 1, gzFold ⁻¹' V, mem_nhdsWithin_of_mem_nhds
    (gzC_fold_lipschitz.continuous.continuousAt.preimage_mem_nhds hV), ?_⟩
  exact hlip.comp gzC_fold_lipschitz.lipschitzOnWith (fun w hw => ⟨hw, gzC_fold_im_nonneg w⟩)

/-- Chain rule with zero inner derivative for an outer map that is only Lipschitz near the
image point. -/
theorem gzC_hasDerivAt_comp_zero {g : ℂ → ℝ} {h : ℝ → ℂ} {t : ℝ} {K : ℝ≥0} {U : Set ℂ}
    (hU : U ∈ 𝓝 (h t)) (hg : LipschitzOnWith K g U) (hh : HasDerivAt h 0 t) :
    HasDerivAt (g ∘ h) 0 t := by
  have hev : ∀ᶠ s in 𝓝 t, h s ∈ U := hh.continuousAt.preimage_mem_nhds hU
  rw [hasDerivAt_iff_isLittleO] at hh ⊢
  simp only [smul_zero, sub_zero, Function.comp_apply] at hh ⊢
  refine Asymptotics.IsBigO.trans_isLittleO ?_ hh
  refine Asymptotics.IsBigO.of_bound K ?_
  filter_upwards [hev] with s hs
  exact hg.norm_sub_le hs (mem_of_mem_nhds hU)

/-- The elementary estimate `|Im (a d)| ≤ 2b · (|a|/(2b)) · |c'|` when `|d| = |c'|`. -/
theorem gzC_enorm_im_le {b : ℝ} (hb : 0 < b) (a d c' : ℂ) (hd : ‖d‖ = ‖c'‖) :
    ‖(a * d).im‖ₑ ≤ ENNReal.ofReal (2 * b) * (ENNReal.ofReal (‖a‖ / (2 * b)) * ‖c'‖ₑ) := by
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs]
  refine (abs_im_le_norm _).trans (le_of_eq ?_)
  rw [norm_mul, hd]
  field_simp

/-- The pointwise bound `|(Y ∘ c)'| ≤ 2b ρ(c) |c'|` at a point where `c` is differentiable. -/
theorem gzC_deriv_bound {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {c : ℝ → ℂ} {u : ℝ} {c' : ℂ}
    (hc : HasDerivAt c c' u) (hmem : c u ∈ unitDisc \ {0, (r : ℂ)}) :
    ‖deriv (gzY r ∘ c) u‖ₑ ≤ ENNReal.ofReal (2 * scSideB r) * (gzRho r (c u) * ‖c'‖ₑ) := by
  have hb := (scSide_pos hr₀ hr₁).2
  rcases lt_trichotomy (c u).im 0 with hneg | hzero | hpos
  · have hwD : conj (c u) ∈ unitDisc := by
      have h1 := hmem.1
      simp only [unitDisc, mem_ball_zero_iff] at h1 ⊢
      rwa [Complex.norm_conj]
    have hwpos : 0 < (conj (c u)).im := by rw [conj_im]; linarith
    have hW := (gzW_differentiableAt hr₀ hr₁ hwD hwpos).hasDerivAt
    have hcc : HasDerivAt (fun s => conj (c s)) (conj c') u := by
      simpa using hc.star
    have h1 : HasDerivAt (fun s => (gzW r (conj (c s))).im)
        (deriv (gzW r) (conj (c u)) * conj c').im u :=
      hasDerivAt_im_of_hasDerivAt (HasDerivAt.comp (h₂ := gzW r) u hW hcc)
    have hev : (gzY r ∘ c) =ᶠ[𝓝 u] fun s => (gzW r (conj (c s))).im := by
      filter_upwards [hc.continuousAt.preimage_mem_nhds
        ((isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg)] with s hs
      have hs' : (c s).im < 0 := hs
      simp only [Function.comp_apply, gzY, gzFold, if_neg (not_le.mpr hs')]
    rw [(h1.congr_of_eventuallyEq hev).deriv]
    have hr : gzRho r (c u) =
        ENNReal.ofReal (‖deriv (gzW r) (conj (c u))‖ / (2 * scSideB r)) := by
      simp only [gzRho, if_neg hneg.ne, gzFold, if_neg (not_le.mpr hneg)]
    rw [hr]
    exact gzC_enorm_im_le hb _ _ _ (Complex.norm_conj _)
  · rw [show gzRho r (c u) = ⊤ from if_pos hzero]
    by_cases hc' : c' = 0
    · have hSopen : IsOpen (unitDisc \ {0, (r : ℂ)}) :=
        (show IsOpen (ball (0 : ℂ) 1) from isOpen_ball).sdiff
          ((finite_singleton _).insert _).isClosed
      obtain ⟨K, t, ht, hlip⟩ := gzY_locallyLipschitzOn hr₀ hr₁ hmem
      rw [hSopen.nhdsWithin_eq hmem] at ht
      rw [hc'] at hc
      rw [(gzC_hasDerivAt_comp_zero ht hlip hc).deriv]
      simp
    · rw [ENNReal.top_mul (enorm_ne_zero.2 hc'),
        ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
      exact le_top
  · have hW := (gzW_differentiableAt hr₀ hr₁ hmem.1 hpos).hasDerivAt
    have h1 : HasDerivAt (fun s => (gzW r (c s)).im) (deriv (gzW r) (c u) * c').im u :=
      hasDerivAt_im_of_hasDerivAt (HasDerivAt.comp (h₂ := gzW r) u hW hc)
    have hev : (gzY r ∘ c) =ᶠ[𝓝 u] fun s => (gzW r (c s)).im := by
      filter_upwards [hc.continuousAt.preimage_mem_nhds
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos)] with s hs
      have hs' : 0 < (c s).im := hs
      simp only [Function.comp_apply, gzY, gzFold, if_pos hs'.le]
    rw [(h1.congr_of_eventuallyEq hev).deriv]
    have hr : gzRho r (c u) = ENNReal.ofReal (‖deriv (gzW r) (c u)‖ / (2 * scSideB r)) := by
      simp only [gzRho, if_neg hpos.ne', gzFold, if_pos hpos.le]
    rw [hr]
    exact gzC_enorm_im_le hb _ _ _ rfl

/-- **The height estimate along a Lipschitz arc.** -/
theorem gz_Y_sub_le {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {c : ℝ → ℂ} {K : ℝ≥0} {s₀ s₁ : ℝ}
    (hs : s₀ ≤ s₁) (hc : LipschitzOnWith K c (Icc s₀ s₁))
    (hmem : ∀ t ∈ Icc s₀ s₁, c t ∈ unitDisc \ {0, (r : ℂ)}) :
    ENNReal.ofReal |gzY r (c s₁) - gzY r (c s₀)|
      ≤ ENNReal.ofReal (2 * scSideB r) * ∫⁻ t in Ioo s₀ s₁, gzRho r (c t) * ‖deriv c t‖ₑ := by
  have hYc : LocallyLipschitzOn (Icc s₀ s₁) (gzY r ∘ c) := by
    intro x hx
    obtain ⟨K', t, ht, hlip⟩ := gzY_locallyLipschitzOn hr₀ hr₁ (hmem x hx)
    refine ⟨K' * K, c ⁻¹' t ∩ Icc s₀ s₁,
      inter_mem ((hc.continuousOn x hx).tendsto_nhdsWithin hmem ht) self_mem_nhdsWithin, ?_⟩
    exact hlip.comp (hc.mono inter_subset_right) (fun s hs => hs.1)
  obtain ⟨L, hL⟩ := hYc.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hftc : ∫ u in s₀..s₁, deriv (gzY r ∘ c) u = gzY r (c s₁) - gzY r (c s₀) :=
    (hL.mono (uIcc_of_le hs).subset).absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have hA : ∀ᵐ u, u ∈ Ioo s₀ s₁ → DifferentiableAt ℝ c u := by
    filter_upwards [(hc.mono Ioo_subset_Icc_self).ae_differentiableWithinAt_of_mem_real]
      with u hu huI
    exact (hu huI).differentiableAt (Ioo_mem_nhds huI.1 huI.2)
  rw [← hftc, intervalIntegral.integral_of_le hs, ← Real.norm_eq_abs, ofReal_norm]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_of_le_of_eq ?_ (setLIntegral_congr Ioo_ae_eq_Ioc).symm
  refine setLIntegral_mono_ae' measurableSet_Ioc ?_
  filter_upwards [hA, compl_mem_ae_iff.2 (measure_singleton s₁)] with u hu hu1 huI
  have huo : u ∈ Ioo s₀ s₁ := ⟨huI.1, lt_of_le_of_ne huI.2 hu1⟩
  exact gzC_deriv_bound hr₀ hr₁ (hu huo).hasDerivAt (hmem u (Ioo_subset_Icc_self huo))

/-! ### Piece D: separating curves -/

theorem gz_notMem_of_sep {r : ℝ} {B : Set ℂ}
    (hsep : SeparatesSets B (toExt (sphere 0 1)) {((0 : ℂ) : ExtPlane), ((r : ℂ) : ExtPlane)}) :
    (0 : ℂ) ∉ B ∧ (r : ℂ) ∉ B := by
  obtain ⟨_, _, x₂, _, _, h2, _⟩ := hsep
  have hsub := connectedComponentIn_subset (toExt B)ᶜ x₂
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact hsub (h2 (by simp)) (mem_image_of_mem _ h)
  · exact hsub (h2 (by simp)) (mem_image_of_mem _ h)

/-- If no point of the closed trace of `γ` is a real number in `[a, b]`, then the real points `a` and
`b` lie in the same component of the complement of the trace in `ℂ̄`. -/
theorem gzD_cc_eq_of_avoid {γ : LRCurve} {a b : ℝ} (hab : a ≤ b)
    (hav : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc a b, γ.toFun t ≠ x) :
    connectedComponentIn (toExt γ.closedTrace)ᶜ (((a : ℂ)) : ExtPlane)
      = connectedComponentIn (toExt γ.closedTrace)ᶜ (((b : ℂ)) : ExtPlane) := by
  set S : Set ExtPlane := (fun x : ℝ => (((x : ℂ)) : ExtPlane)) '' Icc a b with hS
  have hSc : IsPreconnected S :=
    isPreconnected_Icc.image _ (OnePoint.continuous_coe.comp continuous_ofReal).continuousOn
  have haS : (((a : ℂ)) : ExtPlane) ∈ S := ⟨a, ⟨le_rfl, hab⟩, rfl⟩
  have hbS : (((b : ℂ)) : ExtPlane) ∈ S := ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  have hSF : S ⊆ (toExt γ.closedTrace)ᶜ := by
    rintro _ ⟨x, hx, rfl⟩ ⟨z, ⟨t, ht, rfl⟩, hz⟩
    exact hav t ht x hx (OnePoint.coe_injective hz)
  exact connectedComponentIn_eq (hSc.subset_connectedComponentIn haS hSF hbS)

/-- A separating curve meets both `(-1,0)` and `(r,1)`. -/
theorem gz_sep_meets {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {B : Set ℂ} (hsub : B ⊆ unitDisc)
    (hsep : SeparatesSets B (toExt (sphere 0 1)) {((0 : ℂ) : ExtPlane), ((r : ℂ) : ExtPlane)})
    {γ : LRCurve} (hγ : γ ∈ separatingCurves B) :
    (∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ Ioo (-1 : ℝ) 0, γ.toFun t = x) ∧
      (∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ Ioo r 1, γ.toFun t = x) := by
  obtain ⟨h0B, hrB⟩ := gz_notMem_of_sep hsep
  obtain ⟨x₁, _, x₂, _, h1, h2, hne⟩ := hsep
  obtain ⟨_, htr, hcc⟩ := hγ
  set E := (toExt B)ᶜ with hE
  have hm1 : (((-1 : ℝ) : ℂ) : ExtPlane) ∈ connectedComponentIn E x₁ :=
    h1 ⟨_, by simp, rfl⟩
  have hp1 : (((1 : ℝ) : ℂ) : ExtPlane) ∈ connectedComponentIn E x₁ :=
    h1 ⟨_, by simp, rfl⟩
  have hz0 : (((0 : ℝ) : ℂ) : ExtPlane) ∈ connectedComponentIn E x₂ := h2 (by simp)
  have hzr : (((r : ℝ) : ℂ) : ExtPlane) ∈ connectedComponentIn E x₂ := h2 (by simp)
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ B := fun t ht => htr (mem_image_of_mem _ ht)
  have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ.toFun t‖ < 1 := fun t ht => by
    have := hsub (hmem t ht)
    simpa [unitDisc, mem_ball, dist_zero_right] using this
  refine ⟨?_, ?_⟩
  · by_contra hno
    have hav : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc (-1 : ℝ) 0, γ.toFun t ≠ x := by
      intro t ht x hx hx'
      rcases eq_or_lt_of_le hx.1 with h | h
      · have := hnorm t ht
        rw [hx', ← h] at this
        simp at this
      rcases eq_or_lt_of_le hx.2 with h' | h'
      · exact h0B (by simpa [hx', h'] using hmem t ht)
      · exact hno ⟨t, ht, x, ⟨h, h'⟩, hx'⟩
    have heq := gzD_cc_eq_of_avoid (by norm_num) hav
    refine hcc _ (connectedComponentIn_subset _ _ hm1) _ (connectedComponentIn_subset _ _ hz0)
      ?_ heq
    rw [← connectedComponentIn_eq hm1, ← connectedComponentIn_eq hz0]
    exact hne
  · by_contra hno
    have hav : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc r 1, γ.toFun t ≠ x := by
      intro t ht x hx hx'
      rcases eq_or_lt_of_le hx.2 with h | h
      · have := hnorm t ht
        rw [hx', h] at this
        simp at this
      rcases eq_or_lt_of_le hx.1 with h' | h'
      · exact hrB (by simpa [hx', ← h'] using hmem t ht)
      · exact hno ⟨t, ht, x, ⟨h', h⟩, hx'⟩
    have heq := gzD_cc_eq_of_avoid hr₁.le hav
    refine hcc _ (connectedComponentIn_subset _ _ hzr) _ (connectedComponentIn_subset _ _ hp1)
      ?_ heq
    rw [← connectedComponentIn_eq hzr, ← connectedComponentIn_eq hp1]
    exact hne.symm

/-- The three consecutive pieces `(0,m)`, `(m,M)`, `(M,1)` together have integral at most that over
`(0,1)`. -/
theorem gzD_lintegral_three {f : ℝ → ℝ≥0∞} {m M : ℝ} (hm : 0 ≤ m) (hmM : m ≤ M) (hM : M ≤ 1) :
    (∫⁻ t in Ioo 0 m, f t) + (∫⁻ t in Ioo m M, f t) + (∫⁻ t in Ioo M 1, f t)
      ≤ ∫⁻ t in Ioo (0 : ℝ) 1, f t := by
  have hd1 : Disjoint (Ioo (0 : ℝ) m) (Ioo m M) :=
    Set.disjoint_left.2 fun t h1 h2 => lt_irrefl t (h1.2.trans h2.1)
  have hd2 : Disjoint (Ioo (0 : ℝ) m ∪ Ioo m M) (Ioo M 1) :=
    Set.disjoint_left.2 fun t h1 h2 => by
      rcases h1 with h1 | h1
      · exact lt_irrefl t (h1.2.trans (hmM.trans_lt h2.1))
      · exact lt_irrefl t (h1.2.trans h2.1)
  rw [← lintegral_union measurableSet_Ioo hd1, ← lintegral_union measurableSet_Ioo hd2]
  refine lintegral_mono_set ?_
  rintro t ((h | h) | h)
  · exact ⟨h.1, h.2.trans_le (hmM.trans hM)⟩
  · exact ⟨hm.trans_lt h.1, h.2.trans_le hM⟩
  · exact ⟨(hm.trans hmM).trans_lt h.1, h.2⟩

/-- **Admissibility**: every separating curve of `B` has `ρ`-length at least `1`. -/
theorem gz_one_le_rhoLength {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {B : Set ℂ}
    (hsub : B ⊆ unitDisc)
    (hsep : SeparatesSets B (toExt (sphere 0 1)) {((0 : ℂ) : ExtPlane), ((r : ℂ) : ExtPlane)})
    {γ : LRCurve} (hγ : γ ∈ separatingCurves B) : 1 ≤ γ.rhoLength (gzRho r) := by
  obtain ⟨⟨t₁, ht₁, x₁, hx₁, hγ₁⟩, ⟨t₂, ht₂, x₂, hx₂, hγ₂⟩⟩ := gz_sep_meets hr₀ hr₁ hsub hsep hγ
  obtain ⟨h0B, hrB⟩ := gz_notMem_of_sep hsep
  obtain ⟨⟨K, hK, h01⟩, htr, _⟩ := hγ
  have hb : 0 < scSideB r := (scSide_pos hr₀ hr₁).2
  set b := scSideB r with hbdef
  set c := ENNReal.ofReal (2 * b) with hc
  set f : ℝ → ℝ≥0∞ := fun t => gzRho r (γ.toFun t) * ‖deriv γ.toFun t‖ₑ with hf
  set Y : ℝ → ℝ := fun t => gzY r (γ.toFun t) with hY
  have hY₁ : Y t₁ = 0 := by simp only [hY, hγ₁]; exact gzY_left hr₀ hr₁ hx₁
  have hY₂ : Y t₂ = b := by simp only [hY, hγ₂]; exact gzY_right hr₀ hr₁ hx₂
  have hY01 : Y 0 = Y 1 := by simp only [hY, h01]
  have hmemB : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ unitDisc \ {0, (r : ℂ)} := by
    intro t ht
    have h := htr (mem_image_of_mem _ ht)
    refine ⟨hsub h, ?_⟩
    rintro (h' | h')
    · exact h0B (h' ▸ h)
    · exact hrB (h' ▸ h)
  have key : ∀ s₀ s₁ : ℝ, 0 ≤ s₀ → s₀ ≤ s₁ → s₁ ≤ 1 →
      ENNReal.ofReal |Y s₁ - Y s₀| ≤ c * ∫⁻ t in Ioo s₀ s₁, f t := by
    intro s₀ s₁ h0 h01' h1
    have hsub' : Icc s₀ s₁ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc h0 h1
    exact gz_Y_sub_le hr₀ hr₁ h01' (hK.mono hsub') fun t ht => hmemB t (hsub' ht)
  set m := min t₁ t₂ with hmdef
  set M := max t₁ t₂ with hMdef
  have hm0 : 0 ≤ m := le_min ht₁.1 ht₂.1
  have hmM : m ≤ M := min_le_max
  have hM1 : M ≤ 1 := max_le ht₁.2 ht₂.2
  have hmid : |Y M - Y m| = b := by
    rcases le_total t₁ t₂ with h | h
    · rw [hMdef, hmdef, max_eq_right h, min_eq_left h, hY₁, hY₂, sub_zero, abs_of_pos hb]
    · rw [hMdef, hmdef, max_eq_left h, min_eq_right h, hY₁, hY₂, zero_sub, abs_neg, abs_of_pos hb]
  have hout : b ≤ |Y m - Y 0| + |Y 1 - Y M| := by
    rw [← hmid, hY01]
    calc |Y M - Y m| = |-(Y 1 - Y M) + -(Y m - Y 1)| := by ring_nf
      _ ≤ |-(Y 1 - Y M)| + |-(Y m - Y 1)| := abs_add_le _ _
      _ = |Y m - Y 1| + |Y 1 - Y M| := by rw [abs_neg, abs_neg, add_comm]
  have hI2 : ENNReal.ofReal b ≤ c * ∫⁻ t in Ioo m M, f t := hmid ▸ key m M hm0 hmM hM1
  have hI13 : ENNReal.ofReal b ≤ c * ((∫⁻ t in Ioo 0 m, f t) + ∫⁻ t in Ioo M 1, f t) := by
    calc ENNReal.ofReal b ≤ ENNReal.ofReal (|Y m - Y 0| + |Y 1 - Y M|) := ENNReal.ofReal_le_ofReal hout
      _ = ENNReal.ofReal |Y m - Y 0| + ENNReal.ofReal |Y 1 - Y M| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ c * (∫⁻ t in Ioo 0 m, f t) + c * ∫⁻ t in Ioo M 1, f t :=
          add_le_add (key 0 m le_rfl hm0 (hmM.trans hM1)) (key M 1 (hm0.trans hmM) hM1 le_rfl)
      _ = _ := (mul_add _ _ _).symm
  have htot : c ≤ c * γ.rhoLength (gzRho r) := by
    calc c = ENNReal.ofReal b + ENNReal.ofReal b := by
          rw [hc, ← ENNReal.ofReal_add hb.le hb.le, two_mul]
      _ ≤ c * ((∫⁻ t in Ioo 0 m, f t) + ∫⁻ t in Ioo M 1, f t) + c * ∫⁻ t in Ioo m M, f t :=
          add_le_add hI13 hI2
      _ = c * ((∫⁻ t in Ioo 0 m, f t) + (∫⁻ t in Ioo m M, f t) + ∫⁻ t in Ioo M 1, f t) := by
          rw [← mul_add]; congr 1; ring
      _ ≤ c * ∫⁻ t in Ioo (0 : ℝ) 1, f t := by
          gcongr; exact gzD_lintegral_three hm0 hmM hM1
      _ = c * γ.rhoLength (gzRho r) := rfl
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  nth_rewrite 1 [← mul_one c] at htot
  exact (ENNReal.mul_le_mul_iff_right hc0 hctop).1 htot

/-! ### Piece E: the area -/

/-- The fold `z ↦ z` (`Im z ≥ 0`), `z ↦ z̄` (`Im z < 0`) is measurable. -/
theorem gzE_measurable_fold : Measurable gzFold := by
  unfold gzFold
  exact Measurable.ite (measurableSet_le measurable_const Complex.measurable_im) measurable_id
    Complex.continuous_conj.measurable

theorem gz_measurable_rho (r : ℝ) : Measurable (gzRho r) := by
  unfold gzRho
  refine Measurable.ite ?_ measurable_const ?_
  · exact measurableSet_eq_fun Complex.measurable_im measurable_const
  · exact (((measurable_deriv (gzW r)).comp gzE_measurable_fold).norm.div_const _).ennreal_ofReal

theorem gz_lintegral_deriv_sq {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    ∫⁻ z in unitDisc ∩ upperHalf, ‖deriv (gzW r) z‖ₑ ^ 2
      = ENNReal.ofReal (scSideA r * scSideB r) := by
  have hf := gzW_isConformalOnto hr₀ hr₁
  have hU : IsOpen (unitDisc ∩ upperHalf) := isOpen_ball.inter isOpen_upperHalf'
  have key := lintegral_image_conformal hU hf (fun _ => 1)
  simp only [mul_one, lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ,
    univ_inter] at key
  rw [← key, volume_rectangle, ENNReal.ofReal_mul (scSide_pos hr₀ hr₁).1.le]

/-- The real axis `{Im z = 0}` is Lebesgue-null in `ℂ`. -/
theorem gzE_volume_im_eq_zero : volume {z : ℂ | z.im = 0} = 0 := by
  have hpre : {z : ℂ | z.im = 0} = Complex.measurableEquivRealProd ⁻¹' (univ ×ˢ {0}) := by
    ext z; simp
  rw [hpre, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (MeasurableSet.univ.prod (measurableSet_singleton 0)).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod]
  simp

/-- Complex conjugation preserves the Lebesgue measure on `ℂ`. -/
theorem gzE_conj_measurePreserving :
    MeasurePreserving (fun z : ℂ => conj z) volume volume :=
  Complex.conjLIE.measurePreserving

theorem gz_rhoArea_le {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {B : Set ℂ} (hsub : B ⊆ unitDisc) :
    rhoArea (gzRho r) B ≤ ENNReal.ofReal (scSideA r / (2 * scSideB r)) := by
  have ha := (scSide_pos hr₀ hr₁).1
  have hb := (scSide_pos hr₀ hr₁).2
  set U : Set ℂ := unitDisc ∩ upperHalf with hUdef
  set g : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖deriv (gzW r) w‖ / (2 * scSideB r)) ^ 2 with hg
  have hUm : MeasurableSet U := (isOpen_ball.inter isOpen_upperHalf').measurableSet
  -- `g` on `U` in terms of `‖W'‖ₑ²`
  have hgU : ∫⁻ z in U, g z = ENNReal.ofReal (scSideA r / (4 * scSideB r)) := by
    have h1 : ∀ w, g w = ‖deriv (gzW r) w‖ₑ ^ 2 * ENNReal.ofReal (1 / (2 * scSideB r)) ^ 2 := by
      intro w
      simp only [hg]
      rw [← mul_pow, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _), mul_one_div]
    simp_rw [h1]
    rw [lintegral_mul_const' _ _ (by simp), gz_lintegral_deriv_sq hr₀ hr₁,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  -- the three pieces
  have hcover : unitDisc ⊆ (U ∪ (fun z => conj z) ⁻¹' U) ∪ {z : ℂ | z.im = 0} := by
    intro z hz
    rcases lt_trichotomy z.im 0 with h | h | h
    · left; right
      refine ⟨?_, ?_⟩
      · show conj z ∈ ball (0 : ℂ) 1
        have : z ∈ ball (0 : ℂ) 1 := hz
        simpa [mem_ball_zero_iff, Complex.norm_conj] using this
      · show 0 < (conj z).im
        rw [Complex.conj_im]; linarith
    · right; exact h
    · left; left; exact ⟨hz, h⟩
  have hup : ∫⁻ z in U, gzRho r z ^ 2 = ∫⁻ z in U, g z := by
    refine setLIntegral_congr_fun hUm fun z hz => ?_
    have him : 0 < z.im := hz.2
    simp only [gzRho, hg, if_neg him.ne', gzFold, if_pos him.le]
  have hlow : ∫⁻ z in (fun z => conj z) ⁻¹' U, gzRho r z ^ 2 = ∫⁻ z in U, g z := by
    have hm : MeasurableSet ((fun z : ℂ => conj z) ⁻¹' U) :=
      Complex.continuous_conj.measurable hUm
    rw [← gzE_conj_measurePreserving.setLIntegral_comp_preimage_emb
      Complex.conjLIE.toHomeomorph.measurableEmbedding g U]
    refine setLIntegral_congr_fun hm fun z hz => ?_
    have him : 0 < (conj z).im := hz.2
    have him' : z.im < 0 := by rw [Complex.conj_im] at him; linarith
    have hfold : gzFold z = conj z := by
      unfold gzFold; rw [if_neg (not_le.mpr him')]
    simp only [gzRho, hg, if_neg him'.ne, hfold]
  have hreal : ∫⁻ z in {z : ℂ | z.im = 0}, gzRho r z ^ 2 = 0 :=
    setLIntegral_measure_zero _ _ gzE_volume_im_eq_zero
  calc rhoArea (gzRho r) B = ∫⁻ z in B, gzRho r z ^ 2 := rfl
    _ ≤ ∫⁻ z in (U ∪ (fun z => conj z) ⁻¹' U) ∪ {z : ℂ | z.im = 0}, gzRho r z ^ 2 :=
        lintegral_mono_set (hsub.trans hcover)
    _ ≤ (∫⁻ z in U, gzRho r z ^ 2) + (∫⁻ z in (fun z => conj z) ⁻¹' U, gzRho r z ^ 2)
          + ∫⁻ z in {z : ℂ | z.im = 0}, gzRho r z ^ 2 := by
        refine (lintegral_union_le _ _ _).trans ?_
        gcongr
        exact lintegral_union_le _ _ _
    _ = ENNReal.ofReal (scSideA r / (2 * scSideB r)) := by
        rw [hup, hlow, hreal, add_zero, hgU, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        ring

/-! ### Piece F: the modulus of the Grötzsch domain -/

/-- If `Im w ∈ {0, -π}` then `exp w` is real, i.e. fixed by complex conjugation. -/
theorem gzF1_conj_exp_eq {w : ℂ} (hw : w.im = 0 ∨ w.im = -π) : conj (exp w) = exp w := by
  rw [Complex.conj_eq_iff_im, Complex.exp_im]
  rcases hw with h | h <;> simp [h]

/-- A property holding at all real points near a real point `x` holds frequently in the punctured
complex neighbourhood of `x`. -/
theorem gzF1_frequently_real {x : ℝ} {p : ℂ → Prop} (h : ∀ᶠ t : ℝ in 𝓝 x, p t) :
    ∃ᶠ z in 𝓝[≠] (x : ℂ), p z := by
  have hT : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto x).mono_left nhdsWithin_le_nhds) ?_
    exact eventually_nhdsWithin_of_forall fun t ht => by
      simpa [Complex.ofReal_inj] using ht
  exact hT.frequently (h.filter_mono nhdsWithin_le_nhds).frequently

/-- On the real points `(-1,0) ∪ (r,1)`, the exponent defining `gzG` has imaginary part `0` or `-π`. -/
theorem gzF1_im_exponent {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {t : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 0 ∪ Ioo r 1) :
    (-((π / scSideB r : ℝ) : ℂ) * (gzW r t - scSideA r)).im = 0 ∨
      (-((π / scSideB r : ℝ) : ℂ) * (gzW r t - scSideA r)).im = -π := by
  have hb : 0 < scSideB r := (scSide_pos hr₀ hr₁).2
  have him : (-((π / scSideB r : ℝ) : ℂ) * (gzW r t - scSideA r)).im =
      -(π / scSideB r) * (gzW r t).im := by
    simp [Complex.mul_im]
  rw [him]
  rcases ht with ht | ht
  · left; rw [((gzW_ofReal hr₀ hr₁).1 ht).1]; ring
  · right; rw [((gzW_ofReal hr₀ hr₁).2.2 ht).1]; field_simp

/-- `G` is holomorphic on the Grötzsch domain (across `(-1,0)` and `(r,1)` by the identity theorem). -/
theorem gzG_differentiableOn {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    DifferentiableOn ℂ (gzG r) (grotzschDomain r) := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have hzD : z ∈ unitDisc := hz.1
  rcases lt_trichotomy z.im 0 with him | him | him
  · -- lower half: `G = conj ∘ E ∘ conj` near `z`
    have hcD : conj z ∈ unitDisc := by
      simpa [unitDisc, mem_ball_zero_iff, Complex.norm_conj] using hzD
    have hcim : 0 < (conj z).im := by simp [him]
    have hW := gzW_differentiableAt hr₀ hr₁ hcD hcim
    have hE : DifferentiableAt ℂ
        (fun w => exp (-((π / scSideB r : ℝ) : ℂ) * (gzW r w - scSideA r))) (conj z) :=
      ((hW.sub_const _).const_mul _).cexp
    have hE' := hE.conj_conj
    rw [Complex.conj_conj] at hE'
    refine hE'.congr_of_eventuallyEq ?_
    filter_upwards [(Complex.continuous_im.isOpen_preimage _ isOpen_Iio).mem_nhds him] with w hw
    have hw' : ¬ 0 ≤ w.im := not_le.mpr hw
    simp only [gzG, if_neg hw', Function.comp_apply]
  · -- real axis: identity theorem
    have hzx : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
    set x := z.re with hxdef
    have hnorm : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hzD
    rw [hzx, Complex.norm_real, Real.norm_eq_abs] at hnorm
    have hx1 : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [(abs_lt.mp hnorm).1], (abs_lt.mp hnorm).2⟩
    have hnot : ¬ (0 ≤ x ∧ x ≤ r) := fun h => hz.2 ⟨him, h⟩
    have hU : x ∈ Ioo (-1 : ℝ) 0 ∪ Ioo r 1 := by
      by_cases h0 : 0 ≤ x
      · right; exact ⟨lt_of_not_ge fun h => hnot ⟨h0, h⟩, hx1.2⟩
      · left; exact ⟨hx1.1, lt_of_not_ge h0⟩
    have hx0 : x ≠ 0 := fun h => hnot ⟨h.ge, by rw [h]; exact hr₀.le⟩
    have hxr : x ≠ r := fun h => hnot ⟨by rw [h]; exact hr₀.le, h.le⟩
    obtain ⟨ε, hε, H, hHd, -, hHW⟩ := gzW_local_ext hr₀ hr₁ hx1 hx0 hxr
    have hcball : ∀ w ∈ ball (x : ℂ) ε, conj w ∈ ball (x : ℂ) ε := by
      intro w hw
      rw [mem_ball] at hw ⊢
      rwa [← Complex.conj_ofReal, Complex.dist_conj_conj]
    set E : ℂ → ℂ := fun w => exp (-((π / scSideB r : ℝ) : ℂ) * (H w - scSideA r)) with hEdef
    have hEd : DifferentiableOn ℂ E (ball (x : ℂ) ε) := fun w hw =>
      (((hHd w hw).sub_const _).const_mul _).cexp
    have hEd' : DifferentiableOn ℂ (conj ∘ E ∘ conj) (ball (x : ℂ) ε) := by
      intro w hw
      have h1 : DifferentiableAt ℂ E (conj w) :=
        hEd.differentiableAt (isOpen_ball.mem_nhds (hcball w hw))
      have h2 := h1.conj_conj
      rw [Complex.conj_conj] at h2
      exact h2.differentiableWithinAt
    have hfreq : ∃ᶠ w in 𝓝[≠] (x : ℂ), E w = (conj ∘ E ∘ conj) w := by
      apply gzF1_frequently_real
      have hUo : IsOpen (Ioo (-1 : ℝ) 0 ∪ Ioo r 1) := isOpen_Ioo.union isOpen_Ioo
      have hball : ∀ᶠ t : ℝ in 𝓝 x, (t : ℂ) ∈ ball (x : ℂ) ε :=
        (Complex.continuous_ofReal.tendsto x).eventually (isOpen_ball.mem_nhds (mem_ball_self hε))
      filter_upwards [hUo.mem_nhds hU, hball] with t ht htb
      have hHt : H t = gzW r t := hHW t htb (by simp)
      simp only [Function.comp_apply, Complex.conj_ofReal, hEdef, hHt]
      exact (gzF1_conj_exp_eq (gzF1_im_exponent hr₀ hr₁ ht)).symm
    have hEq : EqOn E (conj ∘ E ∘ conj) (ball (x : ℂ) ε) :=
      (hEd.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_frequently_eq
        (hEd'.analyticOnNhd isOpen_ball) (convex_ball _ _).isPreconnected (mem_ball_self hε) hfreq
    rw [hzx]
    refine (hEd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hε))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with w hw
    by_cases h : 0 ≤ w.im
    · simp only [gzG, if_pos h, hEdef, hHW w hw h]
    · have hcw := hcball w hw
      have hcim : 0 ≤ (conj w).im := by simp; linarith [not_le.mp h]
      simp only [gzG, if_neg h]
      rw [← hHW _ hcw hcim]
      exact (hEq hw).symm
  · -- upper half
    have hW := gzW_differentiableAt hr₀ hr₁ hzD him
    have hE : DifferentiableAt ℂ
        (fun w => exp (-((π / scSideB r : ℝ) : ℂ) * (gzW r w - scSideA r))) z :=
      ((hW.sub_const _).const_mul _).cexp
    refine hE.congr_of_eventuallyEq ?_
    filter_upwards [(Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds him] with w hw
    have hw' : 0 ≤ w.im := le_of_lt hw
    simp only [gzG, if_pos hw']

/-- Real part of the exponent `-c (ζ - a)` of `gzG`. -/
theorem gzF2_arg_re (r : ℝ) (ζ : ℂ) :
    (-((π / scSideB r : ℝ) : ℂ) * (ζ - scSideA r)).re = π / scSideB r * (scSideA r - ζ.re) := by
  simp [Complex.mul_re]
  ring

/-- Imaginary part of the exponent `-c (ζ - a)` of `gzG`. -/
theorem gzF2_arg_im (r : ℝ) (ζ : ℂ) :
    (-((π / scSideB r : ℝ) : ℂ) * (ζ - scSideA r)).im = -(π / scSideB r * ζ.im) := by
  simp [Complex.mul_im]

/-- For `u ∈ (0,a)`, the exponent `(π/b)(a - u)` lies in `(0, πa/b)`. -/
theorem gzF2_re_bounds {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {u : ℝ} (hu : u ∈ Ioo 0 (scSideA r)) :
    0 < π / scSideB r * (scSideA r - u) ∧
      π / scSideB r * (scSideA r - u) < π * scSideA r / scSideB r := by
  obtain ⟨ha, hb⟩ := scSide_pos hr₀ hr₁
  obtain ⟨hu0, hua⟩ := hu
  constructor
  · have : 0 < scSideA r - u := by linarith
    positivity
  · rw [div_mul_eq_mul_div, div_lt_div_iff_of_pos_right hb]
    nlinarith [Real.pi_pos]

/-- `exp w` lies in the target annulus when `Re w = (π/b)(a - u)` with `u ∈ (0,a)`. -/
theorem gzF2_exp_mem_annulus {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {u : ℝ}
    (hu : u ∈ Ioo 0 (scSideA r)) {w : ℂ} (hw : w.re = π / scSideB r * (scSideA r - u)) :
    exp w ∈ annulus 1 (Real.exp (π * scSideA r / scSideB r)) := by
  obtain ⟨h1, h2⟩ := gzF2_re_bounds hr₀ hr₁ hu
  refine ⟨?_, ?_⟩ <;> rw [Complex.norm_exp, hw]
  · exact Real.one_lt_exp_iff.2 h1
  · exact Real.exp_lt_exp.2 h2

/-- Upper half-disc: `G z` lies in the annulus with `Im G z < 0`, and the exponent has imaginary
part in `(-π, 0)`. -/
theorem gzF2_upper {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {z : ℂ} (hz : z ∈ unitDisc)
    (him : 0 < z.im) :
    gzG r z ∈ annulus 1 (Real.exp (π * scSideA r / scSideB r)) ∧ (gzG r z).im < 0 ∧
      -π < (-((π / scSideB r : ℝ) : ℂ) * (gzW r z - scSideA r)).im ∧
      (-((π / scSideB r : ℝ) : ℂ) * (gzW r z - scSideA r)).im < 0 := by
  obtain ⟨ha, hb⟩ := scSide_pos hr₀ hr₁
  have hW := mem_image_of_mem (gzW r) (show z ∈ unitDisc ∩ upperHalf from ⟨hz, him⟩)
  rw [(gzW_isConformalOnto hr₀ hr₁).2.2] at hW
  obtain ⟨h1, h2, h3, h4⟩ := hW
  have hG : gzG r z = exp (-((π / scSideB r : ℝ) : ℂ) * (gzW r z - scSideA r)) := by
    unfold gzG
    rw [if_pos him.le]
  have him1 : -π < -(π / scSideB r * (gzW r z).im) := by
    rw [neg_lt_neg_iff, div_mul_eq_mul_div, div_lt_iff₀ hb]
    nlinarith [Real.pi_pos]
  have him2 : -(π / scSideB r * (gzW r z).im) < 0 := by
    have : 0 < π / scSideB r * (gzW r z).im := by positivity
    linarith
  rw [gzF2_arg_im]
  refine ⟨hG ▸ gzF2_exp_mem_annulus hr₀ hr₁ ⟨h1, h2⟩ (gzF2_arg_re r _), ?_, him1, him2⟩
  rw [hG, Complex.exp_im, gzF2_arg_im]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) (Real.sin_neg_of_neg_of_neg_pi_lt him2 him1)

/-- In the lower half-plane, `G z = conj (G (conj z))`. -/
theorem gzF2_lower_eq {r : ℝ} {z : ℂ} (him : z.im < 0) : gzG r z = conj (gzG r (conj z)) := by
  have h : 0 ≤ (conj z).im := by rw [Complex.conj_im]; linarith
  unfold gzG
  rw [if_neg (not_le.2 him), if_pos h]

/-- `conj` preserves the unit disc. -/
theorem gzF2_conj_mem_unitDisc {z : ℂ} (hz : z ∈ unitDisc) : conj z ∈ unitDisc := by
  simpa [unitDisc, mem_ball_zero_iff, Complex.norm_conj] using hz

/-- Lower half-disc: `G z` lies in the annulus with `Im G z > 0`. -/
theorem gzF2_lower {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {z : ℂ} (hz : z ∈ unitDisc)
    (him : z.im < 0) :
    gzG r z ∈ annulus 1 (Real.exp (π * scSideA r / scSideB r)) ∧ 0 < (gzG r z).im := by
  have hc : 0 < (conj z).im := by rw [Complex.conj_im]; linarith
  obtain ⟨hA, hI, -, -⟩ := gzF2_upper hr₀ hr₁ (gzF2_conj_mem_unitDisc hz) hc
  rw [gzF2_lower_eq him]
  refine ⟨?_, ?_⟩
  · simpa [annulus, Complex.norm_conj] using hA
  · rw [Complex.conj_im]; linarith

/-- `G` on `(-1, 0)`: a positive real. -/
theorem gzF2_real_left {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 0) :
    gzG r x = ((Real.exp (π / scSideB r * (scSideA r - (gzW r x).re)) : ℝ) : ℂ) ∧
      (gzW r x).re ∈ Ioo 0 (scSideA r) := by
  obtain ⟨him, hre⟩ := (gzW_ofReal hr₀ hr₁).1 hx
  refine ⟨?_, hre⟩
  set u := (gzW r x).re with hu
  have hW : gzW r x = (u : ℂ) := Complex.ext (by simp [hu]) (by simp [him])
  unfold gzG
  rw [if_pos (by simp), hW, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- `G` on `(r, 1)`: a negative real. -/
theorem gzF2_real_right {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {x : ℝ} (hx : x ∈ Ioo r 1) :
    gzG r x = ((-Real.exp (π / scSideB r * (scSideA r - (gzW r x).re)) : ℝ) : ℂ) ∧
      (gzW r x).re ∈ Ioo 0 (scSideA r) := by
  obtain ⟨ha, hb⟩ := scSide_pos hr₀ hr₁
  obtain ⟨him, hre⟩ := (gzW_ofReal hr₀ hr₁).2.2 hx
  refine ⟨?_, hre⟩
  set u := (gzW r x).re with hu
  have hW : gzW r x = (u : ℂ) + (scSideB r : ℂ) * I :=
    Complex.ext (by simp [hu]) (by simp [him])
  have hb' : (scSideB r : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hexp : -((π / scSideB r : ℝ) : ℂ) * ((u : ℂ) + (scSideB r : ℂ) * I - scSideA r)
      = ((π / scSideB r * (scSideA r - u) : ℝ) : ℂ) - (π : ℂ) * I := by
    push_cast
    field_simp
    ring
  unfold gzG
  rw [if_pos (by simp), hW, hexp, Complex.exp_sub, Complex.exp_pi_mul_I, Complex.ofReal_neg,
    Complex.ofReal_exp]
  ring

/-- Real points of the Grötzsch domain lie on `(-1,0) ∪ (r,1)`. -/
theorem gzF2_real_cases {r : ℝ} {z : ℂ} (hz : z ∈ grotzschDomain r) (him : z.im = 0) :
    z = (z.re : ℂ) ∧ (z.re ∈ Ioo (-1 : ℝ) 0 ∨ z.re ∈ Ioo r 1) := by
  obtain ⟨hD, hS⟩ := hz
  refine ⟨Complex.ext (by simp) (by simp [him]), ?_⟩
  have hn : ‖z‖ < 1 := by simpa [unitDisc, mem_ball_zero_iff] using hD
  have habs : |z.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm z) hn
  obtain ⟨h1, h2⟩ := abs_lt.1 habs
  simp only [mem_setOf_eq, not_and, not_le] at hS
  rcases lt_or_ge z.re 0 with h | h
  · exact Or.inl ⟨h1, h⟩
  · exact Or.inr ⟨hS him h, h2⟩

/-- Real points of `(-1,0) ∪ (r,1)` lie in the Grötzsch domain. -/
theorem gzF2_real_mem {r : ℝ} (hr₀ : 0 < r) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 0 ∨ x ∈ Ioo r 1) :
    (x : ℂ) ∈ grotzschDomain r := by
  have h1 : x ∈ Ioo (-1 : ℝ) 1 := by
    rcases hx with h | h
    · exact ⟨h.1, by linarith [h.2]⟩
    · exact ⟨by linarith [h.1, h.2], h.2⟩
  refine ⟨?_, ?_⟩
  · simp [unitDisc, abs_lt]
    exact ⟨h1.1, h1.2⟩
  · simp only [mem_setOf_eq, Complex.ofReal_im, Complex.ofReal_re, true_and, not_and, not_le]
    intro h0
    rcases hx with h | h
    · linarith [h.2]
    · exact h.1

/-- Non-real points of the unit disc lie in the Grötzsch domain. -/
theorem gzF2_nonreal_mem {r : ℝ} {z : ℂ} (hz : z ∈ unitDisc) (him : z.im ≠ 0) :
    z ∈ grotzschDomain r :=
  ⟨hz, fun h => him h.1⟩

/-- `W` is injective on the real points of `(-1,1)`. -/
theorem gzF2_W_real_inj {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {x₁ x₂ : ℝ}
    (h₁ : x₁ ∈ Ioo (-1 : ℝ) 1) (h₂ : x₂ ∈ Ioo (-1 : ℝ) 1) (h : gzW r x₁ = gzW r x₂) :
    x₁ = x₂ := by
  obtain ⟨y₁, hy₁, -⟩ := gzP_ofReal hr₀ hr₁ h₁
  obtain ⟨y₂, hy₂, -⟩ := gzP_ofReal hr₀ hr₁ h₂
  have hy : y₁ = y₂ := by
    apply scMap_ofReal_injective hr₀ hr₁
    simp only
    rw [← hy₁, ← hy₂]
    exact h
  have hP : gzP r x₁ = gzP r x₂ := by rw [hy₁, hy₂, hy]
  have hm : ∀ x : ℝ, x ∈ Ioo (-1 : ℝ) 1 → (x : ℂ) ∈ unitDisc := by
    intro x hx
    simp [unitDisc, abs_lt]
    exact ⟨hx.1, hx.2⟩
  have d₁ := gzP_den_ne_zero hr₀ hr₁ (hm x₁ h₁)
  have d₂ := gzP_den_ne_zero hr₀ hr₁ (hm x₂ h₂)
  unfold gzP at hP
  rw [div_eq_div_iff d₁ d₂] at hP
  have key : ((-2 * r * (1 - r ^ 2) * (x₁ - x₂) * (x₁ * x₂ - 1) : ℝ) : ℂ) = 0 := by
    push_cast
    linear_combination hP
  have key' : -2 * r * (1 - r ^ 2) * (x₁ - x₂) * (x₁ * x₂ - 1) = 0 := by exact_mod_cast key
  have hr2 : 0 < 1 - r ^ 2 := by nlinarith
  have hxx : x₁ * x₂ - 1 < 0 := by
    nlinarith [mul_pos (by linarith [h₁.2] : (0 : ℝ) < 1 - x₁) (by linarith [h₂.1] : (0 : ℝ) < 1 + x₂),
      mul_pos (by linarith [h₁.1] : (0 : ℝ) < 1 + x₁) (by linarith [h₂.2] : (0 : ℝ) < 1 - x₂)]
  have hne : -2 * r * (1 - r ^ 2) * (x₁ * x₂ - 1) ≠ 0 := by
    have : 0 < -2 * r * (1 - r ^ 2) * (x₁ * x₂ - 1) := by
      have h3 : 0 < r * (1 - r ^ 2) := mul_pos hr₀ hr2
      nlinarith
    exact this.ne'
  have : (x₁ - x₂) * (-2 * r * (1 - r ^ 2) * (x₁ * x₂ - 1)) = 0 := by linear_combination key'
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)

/-- `G` is injective on the upper half-disc. -/
theorem gzF2_upper_inj {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ unitDisc)
    (h₁ : 0 < z₁.im) (hz₂ : z₂ ∈ unitDisc) (h₂ : 0 < z₂.im) (h : gzG r z₁ = gzG r z₂) :
    z₁ = z₂ := by
  obtain ⟨ha, hb⟩ := scSide_pos hr₀ hr₁
  obtain ⟨-, -, a₁, b₁⟩ := gzF2_upper hr₀ hr₁ hz₁ h₁
  obtain ⟨-, -, a₂, b₂⟩ := gzF2_upper hr₀ hr₁ hz₂ h₂
  unfold gzG at h
  rw [if_pos h₁.le, if_pos h₂.le] at h
  have hl := congrArg Complex.log h
  rw [Complex.log_exp a₁ (b₁.trans Real.pi_pos).le, Complex.log_exp a₂ (b₂.trans Real.pi_pos).le] at hl
  have hc : -((π / scSideB r : ℝ) : ℂ) ≠ 0 :=
    neg_ne_zero.2 (by exact_mod_cast (div_pos Real.pi_pos hb).ne')
  have hW : gzW r z₁ = gzW r z₂ := sub_left_inj.1 (mul_left_cancel₀ hc hl)
  exact (gzW_isConformalOnto hr₀ hr₁).2.1 ⟨hz₁, h₁⟩ ⟨hz₂, h₂⟩ hW

/-- `G` is injective on the real points of the Grötzsch domain. -/
theorem gzF2_real_inj {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {x₁ x₂ : ℝ}
    (h₁ : x₁ ∈ Ioo (-1 : ℝ) 0 ∨ x₁ ∈ Ioo r 1) (h₂ : x₂ ∈ Ioo (-1 : ℝ) 0 ∨ x₂ ∈ Ioo r 1)
    (h : gzG r x₁ = gzG r x₂) : x₁ = x₂ := by
  have hI : ∀ x : ℝ, (x ∈ Ioo (-1 : ℝ) 0 ∨ x ∈ Ioo r 1) → x ∈ Ioo (-1 : ℝ) 1 := by
    intro x hx
    rcases hx with h | h
    · exact ⟨h.1, by linarith [h.2]⟩
    · exact ⟨by linarith [h.1, h.2], h.2⟩
  apply gzF2_W_real_inj hr₀ hr₁ (hI x₁ h₁) (hI x₂ h₂)
  have hb := (scSide_pos hr₀ hr₁).2
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · obtain ⟨e₁, -⟩ := gzF2_real_left hr₀ hr₁ h₁
    obtain ⟨e₂, -⟩ := gzF2_real_left hr₀ hr₁ h₂
    obtain ⟨i₁, -⟩ := (gzW_ofReal hr₀ hr₁).1 h₁
    obtain ⟨i₂, -⟩ := (gzW_ofReal hr₀ hr₁).1 h₂
    rw [e₁, e₂, Complex.ofReal_inj, Real.exp_eq_exp] at h
    have hre : (gzW r x₁).re = (gzW r x₂).re := by
      have := mul_left_cancel₀ (div_pos Real.pi_pos hb).ne' h
      linarith
    exact Complex.ext hre (by rw [i₁, i₂])
  · obtain ⟨e₁, -⟩ := gzF2_real_left hr₀ hr₁ h₁
    obtain ⟨e₂, -⟩ := gzF2_real_right hr₀ hr₁ h₂
    rw [e₁, e₂, Complex.ofReal_inj] at h
    linarith [Real.exp_pos (π / scSideB r * (scSideA r - (gzW r x₁).re)),
      Real.exp_pos (π / scSideB r * (scSideA r - (gzW r x₂).re))]
  · obtain ⟨e₁, -⟩ := gzF2_real_right hr₀ hr₁ h₁
    obtain ⟨e₂, -⟩ := gzF2_real_left hr₀ hr₁ h₂
    rw [e₁, e₂, Complex.ofReal_inj] at h
    linarith [Real.exp_pos (π / scSideB r * (scSideA r - (gzW r x₁).re)),
      Real.exp_pos (π / scSideB r * (scSideA r - (gzW r x₂).re))]
  · obtain ⟨e₁, -⟩ := gzF2_real_right hr₀ hr₁ h₁
    obtain ⟨e₂, -⟩ := gzF2_real_right hr₀ hr₁ h₂
    obtain ⟨i₁, -⟩ := (gzW_ofReal hr₀ hr₁).2.2 h₁
    obtain ⟨i₂, -⟩ := (gzW_ofReal hr₀ hr₁).2.2 h₂
    rw [e₁, e₂, Complex.ofReal_inj, neg_inj, Real.exp_eq_exp] at h
    have hre : (gzW r x₁).re = (gzW r x₂).re := by
      have := mul_left_cancel₀ (div_pos Real.pi_pos hb).ne' h
      linarith
    exact Complex.ext hre (by rw [i₁, i₂])

/-- Location of `G z` according to the sign of `Im z`, for `z` in the Grötzsch domain. -/
theorem gzF2_sign {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {z : ℂ} (hz : z ∈ grotzschDomain r) :
    (0 < z.im → (gzG r z).im < 0) ∧ (z.im < 0 → 0 < (gzG r z).im) ∧
      (z.im = 0 → (gzG r z).im = 0) := by
  refine ⟨fun h => (gzF2_upper hr₀ hr₁ hz.1 h).2.1, fun h => (gzF2_lower hr₀ hr₁ hz.1 h).2,
    fun h => ?_⟩
  obtain ⟨hz', hc⟩ := gzF2_real_cases hz h
  rw [hz']
  rcases hc with hc | hc
  · rw [(gzF2_real_left hr₀ hr₁ hc).1, Complex.ofReal_im]
  · rw [(gzF2_real_right hr₀ hr₁ hc).1, Complex.ofReal_im]

/-- `G` maps the Grötzsch domain into the annulus. -/
theorem gzF2_mapsTo {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {z : ℂ} (hz : z ∈ grotzschDomain r) :
    gzG r z ∈ annulus 1 (Real.exp (π * scSideA r / scSideB r)) := by
  rcases lt_trichotomy z.im 0 with h | h | h
  · exact (gzF2_lower hr₀ hr₁ hz.1 h).1
  · obtain ⟨hz', hc⟩ := gzF2_real_cases hz h
    rw [hz']
    rcases hc with hc | hc
    · obtain ⟨e, hu⟩ := gzF2_real_left hr₀ hr₁ hc
      rw [e, Complex.ofReal_exp]
      exact gzF2_exp_mem_annulus hr₀ hr₁ hu (by rw [Complex.ofReal_re])
    · obtain ⟨e, hu⟩ := gzF2_real_right hr₀ hr₁ hc
      rw [e, Complex.ofReal_neg, Complex.ofReal_exp]
      have := gzF2_exp_mem_annulus hr₀ hr₁ hu
        (w := ((π / scSideB r * (scSideA r - (gzW r z.re).re) : ℝ) : ℂ)) (by rw [Complex.ofReal_re])
      simpa [annulus, norm_neg] using this
  · exact (gzF2_upper hr₀ hr₁ hz.1 h).1

/-- Every point of the annulus with negative imaginary part is `G z` for some `z` in the upper
half-disc. -/
theorem gzF2_surj_lower {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {w : ℂ}
    (hw : w ∈ annulus 1 (Real.exp (π * scSideA r / scSideB r))) (him : w.im < 0) :
    ∃ z ∈ unitDisc, 0 < z.im ∧ gzG r z = w := by
  obtain ⟨ha, hb⟩ := scSide_pos hr₀ hr₁
  obtain ⟨hw1, hw2⟩ := hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw1
    linarith
  have hc : 0 < π / scSideB r := div_pos Real.pi_pos hb
  have hc' : ((π / scSideB r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hL1 : 0 < Real.log ‖w‖ := Real.log_pos hw1
  have hL2 : Real.log ‖w‖ < π * scSideA r / scSideB r :=
    (Real.log_lt_iff_lt_exp (by linarith)).2 hw2
  have hA1 : -π < w.arg := Complex.neg_pi_lt_arg w
  have hA2 : w.arg < 0 := Complex.arg_neg_iff.2 him
  set ζ : ℂ := (scSideA r : ℂ) - Complex.log w / ((π / scSideB r : ℝ) : ℂ) with hζ
  have hζre : ζ.re = scSideA r - Real.log ‖w‖ / (π / scSideB r) := by
    rw [hζ, Complex.sub_re, Complex.div_ofReal_re, Complex.log_re, Complex.ofReal_re]
  have hζim : ζ.im = -(w.arg / (π / scSideB r)) := by
    rw [hζ, Complex.sub_im, Complex.div_ofReal_im, Complex.log_im, Complex.ofReal_im]
    ring
  have hmem : ζ ∈ rectangle (scSideA r) (scSideB r) := by
    have e : π * scSideA r / scSideB r = scSideA r * (π / scSideB r) := by ring
    have e' : π = scSideB r * (π / scSideB r) := by field_simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hζre, sub_pos, div_lt_iff₀ hc, ← e]; exact hL2
    · rw [hζre]
      have : 0 < Real.log ‖w‖ / (π / scSideB r) := div_pos hL1 hc
      linarith
    · rw [hζim, neg_pos]
      exact div_neg_of_neg_of_pos hA2 hc
    · rw [hζim, neg_lt, lt_div_iff₀ hc]
      linarith [e']
  rw [← (gzW_isConformalOnto hr₀ hr₁).2.2] at hmem
  obtain ⟨z, ⟨hzD, hzH⟩, hWz⟩ := hmem
  refine ⟨z, hzD, hzH, ?_⟩
  unfold gzG
  rw [if_pos (le_of_lt hzH), hWz, hζ]
  have : -((π / scSideB r : ℝ) : ℂ) * ((scSideA r : ℂ) -
      Complex.log w / ((π / scSideB r : ℝ) : ℂ) - scSideA r) = Complex.log w := by
    field_simp
    ring
  rw [this, Complex.exp_log hw0]

/-- A real point of the annulus is `G x` for a real `x` of the Grötzsch domain. -/
theorem gzF2_surj_real {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) {w : ℂ}
    (hw : w ∈ annulus 1 (Real.exp (π * scSideA r / scSideB r))) (him : w.im = 0) :
    ∃ x : ℝ, (x ∈ Ioo (-1 : ℝ) 0 ∨ x ∈ Ioo r 1) ∧ gzG r x = w := by
  obtain ⟨ha, hb⟩ := scSide_pos hr₀ hr₁
  obtain ⟨hw1, hw2⟩ := hw
  have hwr : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hn : ‖w‖ = |w.re| := by
    conv_lhs => rw [hwr]
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hn] at hw1 hw2
  have hc : 0 < π / scSideB r := div_pos Real.pi_pos hb
  have e : π * scSideA r / scSideB r = scSideA r * (π / scSideB r) := by ring
  set t := scSideA r - Real.log |w.re| / (π / scSideB r) with ht
  have hL1 : 0 < Real.log |w.re| := Real.log_pos hw1
  have hL2 : Real.log |w.re| < π * scSideA r / scSideB r :=
    (Real.log_lt_iff_lt_exp (by linarith)).2 hw2
  have htm : t ∈ Ioo 0 (scSideA r) := by
    refine ⟨?_, ?_⟩
    · rw [ht, sub_pos, div_lt_iff₀ hc, ← e]; exact hL2
    · have : 0 < Real.log |w.re| / (π / scSideB r) := div_pos hL1 hc
      linarith
  have hexp : Real.exp (π / scSideB r * (scSideA r - t)) = |w.re| := by
    have : π / scSideB r * (scSideA r - t) = Real.log |w.re| := by
      rw [ht]; field_simp; ring
    rw [this, Real.exp_log (by linarith)]
  obtain ⟨⟨x₁, hx₁, hW₁⟩, ⟨x₂, hx₂, hW₂⟩⟩ := gzW_ofReal_surj hr₀ hr₁ htm
  rcases lt_or_ge 0 w.re with hpos | hneg
  · refine ⟨x₁, Or.inl hx₁, ?_⟩
    rw [(gzF2_real_left hr₀ hr₁ hx₁).1, hW₁, Complex.ofReal_re, hexp, abs_of_pos hpos, ← hwr]
  · have hneg' : w.re < 0 := by
      rcases hneg.lt_or_eq with h | h
      · exact h
      · rw [h, abs_zero] at hw1; linarith
    refine ⟨x₂, Or.inr hx₂, ?_⟩
    have hre : (gzW r x₂).re = t := by rw [hW₂]; simp
    rw [(gzF2_real_right hr₀ hr₁ hx₂).1, hre, hexp, abs_of_neg hneg', neg_neg, ← hwr]

theorem gzG_injOn {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) : InjOn (gzG r) (grotzschDomain r) := by
  intro z₁ h₁ z₂ h₂ h
  obtain ⟨p₁, n₁, e₁⟩ := gzF2_sign hr₀ hr₁ h₁
  obtain ⟨p₂, n₂, e₂⟩ := gzF2_sign hr₀ hr₁ h₂
  rcases lt_trichotomy z₁.im 0 with c₁ | c₁ | c₁ <;>
    rcases lt_trichotomy z₂.im 0 with c₂ | c₂ | c₂
  · have hc₁ : 0 < (conj z₁).im := by rw [Complex.conj_im]; linarith
    have hc₂ : 0 < (conj z₂).im := by rw [Complex.conj_im]; linarith
    rw [gzF2_lower_eq c₁, gzF2_lower_eq c₂] at h
    have := gzF2_upper_inj hr₀ hr₁ (gzF2_conj_mem_unitDisc h₁.1) hc₁
      (gzF2_conj_mem_unitDisc h₂.1) hc₂ (star_injective h)
    simpa using congrArg conj this
  · have := n₁ c₁; rw [h, e₂ c₂] at this; exact absurd this (lt_irrefl 0)
  · have := n₁ c₁; rw [h] at this; linarith [p₂ c₂]
  · have := e₁ c₁; rw [h] at this; linarith [n₂ c₂]
  · obtain ⟨hz₁, hx₁⟩ := gzF2_real_cases h₁ c₁
    obtain ⟨hz₂, hx₂⟩ := gzF2_real_cases h₂ c₂
    rw [hz₁, hz₂] at h
    rw [hz₁, hz₂, gzF2_real_inj hr₀ hr₁ hx₁ hx₂ h]
  · have := e₁ c₁; rw [h] at this; linarith [p₂ c₂]
  · have := p₁ c₁; rw [h] at this; linarith [n₂ c₂]
  · have := p₁ c₁; rw [h, e₂ c₂] at this; exact absurd this (lt_irrefl 0)
  · exact gzF2_upper_inj hr₀ hr₁ h₁.1 c₁ h₂.1 c₂ h

theorem gzG_image {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    gzG r '' grotzschDomain r = annulus 1 (Real.exp (π * scSideA r / scSideB r)) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact gzF2_mapsTo hr₀ hr₁ hz
  · intro hw
    rcases lt_trichotomy w.im 0 with h | h | h
    · obtain ⟨z, hzD, hzH, hGz⟩ := gzF2_surj_lower hr₀ hr₁ hw h
      exact ⟨z, gzF2_nonreal_mem hzD hzH.ne', hGz⟩
    · obtain ⟨x, hx, hGx⟩ := gzF2_surj_real hr₀ hr₁ hw h
      exact ⟨x, gzF2_real_mem hr₀ hx, hGx⟩
    · have hw' : conj w ∈ annulus 1 (Real.exp (π * scSideA r / scSideB r)) := by
        simpa [annulus, Complex.norm_conj] using hw
      have h' : (conj w).im < 0 := by rw [Complex.conj_im]; linarith
      obtain ⟨z, hzD, hzH, hGz⟩ := gzF2_surj_lower hr₀ hr₁ hw' h'
      have hc : (conj z).im < 0 := by rw [Complex.conj_im]; linarith
      refine ⟨conj z, gzF2_nonreal_mem (gzF2_conj_mem_unitDisc hzD) hc.ne, ?_⟩
      rw [gzF2_lower_eq hc, Complex.conj_conj, hGz, Complex.conj_conj]

theorem gzG_isConformalOnto {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    IsConformalOnto (gzG r) (grotzschDomain r)
      (annulus 1 (Real.exp (π * scSideA r / scSideB r))) :=
  ⟨gzG_differentiableOn hr₀ hr₁, gzG_injOn hr₀ hr₁, gzG_image hr₀ hr₁⟩

theorem gz_dcModulus_grotzschDomain {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    dcModulus (grotzschDomain r) = ENNReal.ofReal (π * scSideA r / scSideB r) := by
  have ha := (scSide_pos hr₀ hr₁).1
  have hb := (scSide_pos hr₀ hr₁).2
  have hpos : 0 < π * scSideA r / scSideB r := by positivity
  rw [dcModulus_eq_of_equiv (grotzschDomain_doublyConnected hr₀ hr₁).1.1 one_pos
    (Real.one_lt_exp_iff.2 hpos) ⟨_, gzG_isConformalOnto hr₀ hr₁⟩, div_one, Real.log_exp]

/-! ### The target -/

-- (the target follows)

/-- **Theorem 5.1** (Grötzsch).  Every doubly connected domain in the unit disc separating the
unit circle from the pair of points `{0, r}` has modulus at most `M(B_r)`.

Proved (2026-09-23), following the book's symmetric-metric argument made explicit: `gzP` maps the
upper half-disc onto `ℍ` with `-1, 0, r, 1 ↦ -1/r, -1, 1, 1/r`, and the Schwarz–Christoffel map `scMap r`
sends `ℍ` onto a rectangle `(0,a) × (0,b)`; `W = scMap r ∘ gzP r` continues holomorphically across the
slit, so the height `Im W`, folded symmetrically, is locally Lipschitz on `Δ ∖ {0, r}` and every
separating curve of `B` (which meets both `(-1,0)` and `(r,1)`) has `ρ`-length `≥ 1` for the symmetric
density `ρ = |W'|/(2b)`; its area is `a/(2b)`, and `M(B_r) = πa/b` via the glued map `gzG` onto an
annulus. -/
theorem thm5_1_grotzsch {r : ℝ} (h₀ : 0 < r) (h₁ : r < 1) {B : Set ℂ} (hB : IsDoublyConnected B)
    (hsub : B ⊆ unitDisc)
    (hsep : SeparatesSets B (toExt (sphere 0 1)) {((0 : ℂ) : ExtPlane), ((r : ℂ) : ExtPlane)}) :
    dcModulus B ≤ dcModulus (grotzschDomain r) := by
  have ha := (scSide_pos h₀ h₁).1
  have hb := (scSide_pos h₀ h₁).2
  have hadm : ∀ γ ∈ separatingCurves B, 1 ≤ γ.rhoLength (gzRho r) :=
    fun γ hγ => gz_one_le_rhoLength h₀ h₁ hsub hsep hγ
  calc dcModulus B ≤ ENNReal.ofReal (2 * π) * rhoArea (gzRho r) B :=
        dcModulus_le_rhoArea hB (gz_measurable_rho r) hadm
    _ ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal (scSideA r / (2 * scSideB r)) := by
        gcongr
        exact gz_rhoArea_le h₀ h₁ hsub
    _ = ENNReal.ofReal (π * scSideA r / scSideB r) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ = dcModulus (grotzschDomain r) := (gz_dcModulus_grotzschDomain h₀ h₁).symm

/-! ### Monotonicity of the Grötzsch function — helpers -/

/-- `P_A(k,t)` is strictly increasing in `k` for `t ∈ (0,1)`. -/
theorem gm_PA_lt {k₁ k₂ t : ℝ} (h₁ : 0 < k₁) (h : k₁ < k₂) (ht : t ∈ Ioo (0 : ℝ) 1) :
    rq_PA k₁ t < rq_PA k₂ t := by
  unfold rq_PA
  obtain ⟨ht₀, ht₁⟩ := ht
  have hX : 0 < (1 - k₁) * t + 2 * k₁ := by nlinarith
  have hY : 0 < 1 + k₂ + (1 - k₂) * t := by nlinarith
  nlinarith [mul_pos (mul_pos (sub_pos.2 h) (by linarith : (0 : ℝ) < 2 - t)) hY,
    mul_pos hX (mul_pos (sub_pos.2 h) (by linarith : (0 : ℝ) < 1 - t))]

/-- `P_B(k,t)` is non-increasing in `k ≥ 0`. -/
theorem gm_PB_le {k₁ k₂ t : ℝ} (h₁ : 0 ≤ k₁) (h : k₁ ≤ k₂) :
    rq_PB k₂ t ≤ rq_PB k₁ t := by
  unfold rq_PB
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h) (by linarith : (0 : ℝ) ≤ k₁ + k₂))
    (sq_nonneg (2 * t - 1))]

/-- The side `a_k = K(k')` is strictly decreasing in `k`. -/
theorem gm_scSideA_strictAntiOn : StrictAntiOn scSideA (Ioo 0 1) := by
  rintro k₁ ⟨h₁, h₁'⟩ k₂ ⟨h₂, h₂'⟩ h
  rw [rq_scSideA_eq h₂ h₂', rq_scSideA_eq h₁ h₁']
  have hi : ∀ k, 0 < k → k < 1 →
      IntervalIntegrable (fun t => 1 / Real.sqrt (t * (1 - t) * rq_PA k t)) volume 0 1 :=
    fun k hk hk' => rq_intervalIntegrable (m := 2 * k * (1 + k)) (by positivity)
      (rq_measurable_PA k) fun t ht => rq_PA_ge hk hk' ht
  rw [← sub_pos, ← intervalIntegral.integral_sub (hi k₁ h₁ h₁') (hi k₂ h₂ h₂')]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ((hi k₁ h₁ h₁').sub (hi k₂ h₂ h₂'))
    (fun t ht => ?_) one_pos
  have hw : 0 < t * (1 - t) := mul_pos ht.1 (by linarith [ht.2])
  have hp : 0 < rq_PA k₁ t :=
    lt_of_lt_of_le (by positivity) (rq_PA_ge h₁ h₁' ⟨ht.1.le, ht.2.le⟩)
  rw [sub_pos]
  exact one_div_lt_one_div_of_lt (Real.sqrt_pos.2 (mul_pos hw hp))
    (Real.sqrt_lt_sqrt (mul_pos hw hp).le (mul_lt_mul_of_pos_left (gm_PA_lt h₁ h ht) hw))

/-- The side `b_k = 2K(k)` is non-decreasing in `k`. -/
theorem gm_scSideB_monotoneOn : MonotoneOn scSideB (Ioo 0 1) := by
  rintro k₁ ⟨h₁, h₁'⟩ k₂ ⟨h₂, h₂'⟩ h
  rw [rq_scSideB_eq, rq_scSideB_eq]
  have hi : ∀ k, 0 < k → k < 1 →
      IntervalIntegrable (fun t => 1 / Real.sqrt (t * (1 - t) * rq_PB k t)) volume 0 1 :=
    fun k hk hk' => rq_intervalIntegrable (m := (1 - k) ^ 2) (by nlinarith)
      (rq_measurable_PB k) fun t ht => rq_PB_ge hk.le hk' ht
  refine intervalIntegral.integral_mono_on zero_le_one (hi k₁ h₁ h₁') (hi k₂ h₂ h₂')
    fun t ht => ?_
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · simp [← h0]
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · simp [h1]
  have hw : 0 < t * (1 - t) := mul_pos h0 (by linarith)
  have hp : 0 < rq_PB k₂ t :=
    lt_of_lt_of_le (by nlinarith) (rq_PB_ge h₂.le h₂' ⟨h0.le, h1.le⟩)
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (mul_pos hw hp))
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (gm_PB_le h₁.le h) hw.le))

/-- `μ(r) = π a_r / b_r`. -/
theorem gm_grotzschMu_eq {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    grotzschMu r = π * scSideA r / scSideB r := by
  have ha := (scSide_pos hr₀ hr₁).1
  have hb := (scSide_pos hr₀ hr₁).2
  unfold grotzschMu
  rw [gz_dcModulus_grotzschDomain hr₀ hr₁, ENNReal.toReal_ofReal (by positivity)]

/-- The Grötzsch function is (strictly) decreasing on `(0,1)`.

Proved (2026-09-23): `μ(r) = π a_r / b_r` (`gz_dcModulus_grotzschDomain`), where by the substitutions
of `Lemmas/RectangleQuad` `a_k = ∫₀¹ dt/√(t(1-t)P_A(k,t))` with `P_A` strictly increasing in `k`, and
`b_k = ∫₀¹ dt/√(t(1-t)P_B(k,t))` with `P_B` non-increasing in `k`. -/
theorem grotzschMu_strictAntiOn : StrictAntiOn grotzschMu (Ioo 0 1) := by
  rintro r₁ ⟨h₁, h₁'⟩ r₂ ⟨h₂, h₂'⟩ h
  rw [gm_grotzschMu_eq h₁ h₁', gm_grotzschMu_eq h₂ h₂']
  have ha := gm_scSideA_strictAntiOn ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ h
  have hb := gm_scSideB_monotoneOn ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩ h.le
  have ha₂ := (scSide_pos h₂ h₂').1
  have hb₁ := (scSide_pos h₁ h₁').2
  calc π * scSideA r₂ / scSideB r₂ ≤ π * scSideA r₂ / scSideB r₁ :=
        div_le_div_of_nonneg_left (by positivity) hb₁ hb
    _ < π * scSideA r₁ / scSideB r₁ := by gcongr

/-! ## The Teichmüller problem -/

/-- The Teichmüller domain `T_R = ℂ ∖ ([-1, 0] ∪ [R, ∞))` (`R > 0`). -/
def teichmullerDomain (R : ℝ) : Set ℂ :=
  {z : ℂ | ¬ (z.im = 0 ∧ ((-1 ≤ z.re ∧ z.re ≤ 0) ∨ R ≤ z.re))}

/-! ### Theorem 5.2 — helpers -/

open scoped ComplexConjugate


/-! ### Definitions -/

/-- The modulus `k = (√(1+R) - 1)/(√(1+R) + 1)` of the Schwarz–Christoffel map used for `T_R`. -/
def tzK (R : ℝ) : ℝ := (Real.sqrt (1 + R) - 1) / (Real.sqrt (1 + R) + 1)

/-- `q = 2k/(1-k)`. -/
def tzQc (R : ℝ) : ℝ := 2 * tzK R / (1 - tzK R)

/-- The pole `z₀ = -2/(1-k)` of `Q`. -/
def tzPole (R : ℝ) : ℝ := -2 / (1 - tzK R)

/-- `Q(z) = (z - q)/(k z + q)`: `-1, 0, R, ∞ ↦ -1/k, -1, 1, 1/k`. -/
def tzQ (R : ℝ) (z : ℂ) : ℂ := (z - tzQc R) / ((tzK R : ℂ) * z + tzQc R)

/-- `W = scMap k ∘ Q`, with the value `scMapInfty k` at the pole. -/
def tzW (R : ℝ) (z : ℂ) : ℂ := if z = (tzPole R : ℂ) then scMapInfty (tzK R) else scMap (tzK R) (tzQ R z)

/-- The width function `X = Re W ∘ fold`: `0` on `(-∞,-1)`, `a` on `(0,R)`. -/
def tzX (R : ℝ) (z : ℂ) : ℝ := (tzW R (gzFold z)).re

/-- The symmetric extremal density `ρ = |W' ∘ fold|/(2a)`, `∞` on the real axis. -/
def tzRho (R : ℝ) (z : ℂ) : ℝ≥0∞ :=
  if z.im = 0 then ⊤ else ENNReal.ofReal (‖deriv (tzW R) (gzFold z)‖ / (2 * scSideA (tzK R)))

/-- The conformal map of `T_R` onto an annulus, glued along the real axis. -/
def tzG (R : ℝ) (z : ℂ) : ℂ :=
  if 0 ≤ z.im then exp (I * ((π / scSideA (tzK R) : ℝ) : ℂ) * tzW R z)
  else conj (exp (I * ((π / scSideA (tzK R) : ℝ) : ℂ) * tzW R (conj z)))

/-! ### Piece A: the parameters and the Möbius map `Q` -/

/-- `s = √(1+R)` satisfies `1 < s` and `s² = 1 + R`. -/
theorem tzA_sqrt {R : ℝ} (hR : 0 < R) :
    1 < Real.sqrt (1 + R) ∧ Real.sqrt (1 + R) ^ 2 = 1 + R := by
  refine ⟨?_, Real.sq_sqrt (by linarith)⟩
  exact (Real.lt_sqrt zero_le_one).2 (by linarith)

theorem tzK_pos {R : ℝ} (hR : 0 < R) : 0 < tzK R := by
  have hs := (tzA_sqrt hR).1
  unfold tzK
  exact div_pos (by linarith) (by linarith)

theorem tzK_lt_one {R : ℝ} (hR : 0 < R) : tzK R < 1 := by
  have hs := (tzA_sqrt hR).1
  unfold tzK
  rw [div_lt_one (by linarith)]
  linarith

theorem tzR_eq {R : ℝ} (hR : 0 < R) : R = 4 * tzK R / (1 - tzK R) ^ 2 := by
  obtain ⟨hs, hs2⟩ := tzA_sqrt hR
  have h1 : (1 - tzK R) ≠ 0 := (sub_pos.mpr (tzK_lt_one hR)).ne'
  have hs1 : Real.sqrt (1 + R) + 1 ≠ 0 := by linarith
  have hk : tzK R * (Real.sqrt (1 + R) + 1) = Real.sqrt (1 + R) - 1 := by
    unfold tzK; field_simp
  have h1k : (1 - tzK R) * (Real.sqrt (1 + R) + 1) = 2 := by linear_combination (-1 : ℝ) * hk
  rw [eq_div_iff (pow_ne_zero 2 h1)]
  apply mul_right_cancel₀ (pow_ne_zero 2 hs1)
  linear_combination R * ((1 - tzK R) * (Real.sqrt (1 + R) + 1) + 2) * h1k -
    4 * (Real.sqrt (1 + R) + 1) * hk - 4 * hs2

theorem tzPole_lt {R : ℝ} (hR : 0 < R) : tzPole R < -1 := by
  have hk0 := tzK_pos hR
  have hk1 := tzK_lt_one hR
  unfold tzPole
  rw [div_lt_iff₀ (by linarith)]
  linarith

theorem tzQ_conj (R : ℝ) (z : ℂ) : tzQ R (conj z) = conj (tzQ R z) := by
  simp [tzQ, map_div₀, map_sub, map_mul, map_add, Complex.conj_ofReal]

/-- The algebraic relations between `k`, `q`, the pole and `R`. -/
theorem tzA_rel {R : ℝ} (hR : 0 < R) :
    tzQc R * (1 - tzK R) = 2 * tzK R ∧ tzK R * tzPole R + tzQc R = 0 ∧
      R * (1 - tzK R) = 2 * tzQc R := by
  have hk0 := tzK_pos hR
  have hk1 := tzK_lt_one hR
  have h1 : (1 - tzK R) ≠ 0 := (sub_pos.mpr hk1).ne'
  have hRe := tzR_eq hR
  have hq : tzQc R * (1 - tzK R) = 2 * tzK R := by unfold tzQc; field_simp
  have h4 : R * (1 - tzK R) ^ 2 = 4 * tzK R := by
    rw [eq_div_iff (pow_ne_zero 2 h1)] at hRe; exact hRe
  refine ⟨hq, ?_, ?_⟩
  · unfold tzQc tzPole; field_simp; ring
  · apply mul_right_cancel₀ h1
    linear_combination h4 - 2 * hq

/-- The denominator `k z + q` vanishes only at the pole. -/
theorem tzA_den_ne_zero {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ≠ (tzPole R : ℂ)) :
    (tzK R : ℂ) * z + tzQc R ≠ 0 := by
  have hk0 := tzK_pos hR
  have hrel := (tzA_rel hR).2.1
  intro h
  apply hz
  have hk : (tzK R : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have h2 : (tzK R : ℂ) * (tzPole R : ℂ) + tzQc R = 0 := by exact_mod_cast hrel
  apply mul_left_cancel₀ hk
  linear_combination h - h2

theorem tzQ_differentiableAt {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ≠ (tzPole R : ℂ)) :
    DifferentiableAt ℂ (tzQ R) z := by
  show DifferentiableAt ℂ (fun z : ℂ => (z - tzQc R) / ((tzK R : ℂ) * z + tzQc R)) z
  exact DifferentiableAt.div (by fun_prop) (by fun_prop) (tzA_den_ne_zero hR hz)

theorem tzQ_im_pos {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : 0 < z.im) : 0 < (tzQ R z).im := by
  have hk0 := tzK_pos hR
  have hk1 := tzK_lt_one hR
  have hq : 0 < tzQc R := by unfold tzQc; exact div_pos (by linarith) (by linarith)
  have hzp : z ≠ (tzPole R : ℂ) := by
    intro h; rw [h] at hz; simp at hz
  have hD := tzA_den_ne_zero hR hzp
  have hDpos := Complex.normSq_pos.mpr hD
  have e : (z - tzQc R).im * ((tzK R : ℂ) * z + tzQc R).re -
      (z - tzQc R).re * ((tzK R : ℂ) * z + tzQc R).im = tzQc R * (1 + tzK R) * z.im := by
    simp; ring
  unfold tzQ
  rw [Complex.div_im, ← sub_div, e]
  apply div_pos _ hDpos
  have : 0 < 1 + tzK R := by linarith
  positivity

/-- `Q` on a real point, as a real number. -/
theorem tzA_Q_ofReal (R x : ℝ) :
    tzQ R (x : ℂ) = (((x - tzQc R) / (tzK R * x + tzQc R) : ℝ) : ℂ) := by
  unfold tzQ; push_cast; rfl

/-- The values at the vertices. -/
theorem tzQ_vertices {R : ℝ} (hR : 0 < R) :
    tzQ R (-1) = ((-1 / tzK R : ℝ) : ℂ) ∧ tzQ R 0 = -1 ∧ tzQ R R = 1 := by
  have hk0 := tzK_pos hR
  have hk1 := tzK_lt_one hR
  obtain ⟨hq, -, hRq⟩ := tzA_rel hR
  have hq0 : 0 < tzQc R := by unfold tzQc; exact div_pos (by linarith) (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · have hD : tzK R * (-1) + tzQc R ≠ 0 := by nlinarith
    have h : (-1 - tzQc R) / (tzK R * (-1) + tzQc R) = -1 / tzK R := by
      rw [div_eq_div_iff hD hk0.ne']
      linear_combination hq
    rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by push_cast; rfl, tzA_Q_ofReal, h]
  · have hD : tzK R * 0 + tzQc R ≠ 0 := by simp; exact hq0.ne'
    have h : (0 - tzQc R) / (tzK R * 0 + tzQc R) = -1 := by
      rw [div_eq_iff hD]; ring
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, tzA_Q_ofReal, h]
    push_cast; rfl
  · have hD : tzK R * R + tzQc R ≠ 0 := by positivity
    have h : (R - tzQc R) / (tzK R * R + tzQc R) = 1 := by
      rw [div_eq_one_iff_eq hD]
      linear_combination hRq
    rw [tzA_Q_ofReal, h]
    simp

/-- Sign identities for `Q` on the real axis. -/
theorem tzA_real_ident {R : ℝ} (hR : 0 < R) {x : ℝ} (hD : tzK R * x + tzQc R ≠ 0) :
    (x - tzQc R) / (tzK R * x + tzQc R) + 1 / tzK R = 2 * (x + 1) / (tzK R * x + tzQc R) ∧
    (x - tzQc R) / (tzK R * x + tzQc R) + 1 = x * (1 + tzK R) / (tzK R * x + tzQc R) ∧
    (x - tzQc R) / (tzK R * x + tzQc R) - 1 =
      (1 - tzK R) * (x - R) / (tzK R * x + tzQc R) ∧
    (x - tzQc R) / (tzK R * x + tzQc R) - 1 / tzK R =
      -(tzQc R * (1 + tzK R)) / (tzK R * (tzK R * x + tzQc R)) := by
  have hk0 := tzK_pos hR
  obtain ⟨hq, -, hRq⟩ := tzA_rel hR
  have hk : tzK R ≠ 0 := hk0.ne'
  have hD' : x * tzK R + tzQc R ≠ 0 := by rw [mul_comm]; exact hD
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp; linear_combination hq
  · field_simp; ring
  · field_simp; linear_combination hRq
  · field_simp; ring

/-- On the real axis (off the pole) `Q` is real, with `(-∞,-1) → {|y| > 1/k}`, `(-1,0) → (-1/k,-1)`,
`(0,R) → (-1,1)`, `(R,∞) → (1,1/k)`. -/
theorem tzQ_ofReal {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : x ≠ tzPole R) :
    ∃ y : ℝ, tzQ R x = y ∧ (x < -1 → 1 / tzK R < |y|) ∧ (-1 < x → x < 0 → y ∈ Ioo (-1 / tzK R) (-1)) ∧
      (0 < x → x < R → y ∈ Ioo (-1) 1) ∧ (R < x → y ∈ Ioo 1 (1 / tzK R)) := by
  have hk0 := tzK_pos hR
  have hk1 := tzK_lt_one hR
  have hq0 : 0 < tzQc R := by unfold tzQc; exact div_pos (by linarith) (by linarith)
  have hp := tzPole_lt hR
  have hrel := (tzA_rel hR).2.1
  -- `D = k (x - p)`
  have hDe : tzK R * x + tzQc R = tzK R * (x - tzPole R) := by linear_combination hrel
  have hD : tzK R * x + tzQc R ≠ 0 := by
    rw [hDe]; exact mul_ne_zero hk0.ne' (sub_ne_zero.mpr hx)
  obtain ⟨e1, e2, e3, e4⟩ := tzA_real_ident hR hD
  set y := (x - tzQc R) / (tzK R * x + tzQc R) with hy
  have hk1' : 0 < 1 + tzK R := by linarith
  have hkinv : 0 < 1 / tzK R := by positivity
  refine ⟨y, tzA_Q_ofReal R x, ?_, ?_, ?_, ?_⟩
  · intro hx1
    rcases lt_or_gt_of_ne hx with hxp | hxp
    · -- `x < p`: `D < 0`, so `y > 1/k`
      have hDn : tzK R * x + tzQc R < 0 := by rw [hDe]; nlinarith
      have : 0 < y - 1 / tzK R := by
        rw [e4]
        apply div_pos_of_neg_of_neg
        · have := mul_pos hq0 hk1'; linarith
        · nlinarith
      rw [abs_of_pos (by linarith)]
      linarith
    · -- `p < x < -1`: `D > 0`, so `y < -1/k`
      have hDp : 0 < tzK R * x + tzQc R := by rw [hDe]; nlinarith
      have : y + 1 / tzK R < 0 := by
        rw [e1]; exact div_neg_of_neg_of_pos (by linarith) hDp
      rw [abs_of_neg (by linarith)]
      linarith
  · intro hxm hx0
    have hDp : 0 < tzK R * x + tzQc R := by rw [hDe]; nlinarith
    constructor
    · have : 0 < y + 1 / tzK R := by rw [e1]; exact div_pos (by linarith) hDp
      have h' : -1 / tzK R = -(1 / tzK R) := by ring
      rw [h']; linarith
    · have : y + 1 < 0 := by
        rw [e2]; exact div_neg_of_neg_of_pos (by nlinarith) hDp
      linarith
  · intro hx0 hxR
    have hDp : 0 < tzK R * x + tzQc R := by rw [hDe]; nlinarith
    constructor
    · have : 0 < y + 1 := by rw [e2]; exact div_pos (by positivity) hDp
      linarith
    · have : y - 1 < 0 := by
        rw [e3]; exact div_neg_of_neg_of_pos (by nlinarith) hDp
      linarith
  · intro hxR
    have hDp : 0 < tzK R * x + tzQc R := by rw [hDe]; nlinarith
    constructor
    · have : 0 < y - 1 := by rw [e3]; exact div_pos (by nlinarith) hDp
      linarith
    · have : y - 1 / tzK R < 0 := by
        rw [e4]
        apply div_neg_of_neg_of_pos
        · have := mul_pos hq0 hk1'; linarith
        · positivity
      linarith

theorem tzQ_isConformalOnto {R : ℝ} (hR : 0 < R) : IsConformalOnto (tzQ R) upperHalf upperHalf := by
  have hk0 := tzK_pos hR
  have hk1 := tzK_lt_one hR
  have hq0 : 0 < tzQc R := by unfold tzQc; exact div_pos (by linarith) (by linarith)
  have hnp : ∀ z ∈ upperHalf, z ≠ (tzPole R : ℂ) := by
    intro z hz h; rw [h] at hz; simp [upperHalf] at hz
  refine ⟨fun z hz => (tzQ_differentiableAt hR (hnp z hz)).differentiableWithinAt, ?_, ?_⟩
  · intro z₁ hz₁ z₂ hz₂ h
    have hD₁ := tzA_den_ne_zero hR (hnp z₁ hz₁)
    have hD₂ := tzA_den_ne_zero hR (hnp z₂ hz₂)
    unfold tzQ at h
    rw [div_eq_div_iff hD₁ hD₂] at h
    have hf : ((tzQc R : ℂ) * (1 + tzK R)) * (z₁ - z₂) = 0 := by linear_combination h
    have hc : ((tzQc R : ℂ) * (1 + tzK R)) ≠ 0 := by
      have : (0 : ℝ) < tzQc R * (1 + tzK R) := mul_pos hq0 (by linarith)
      exact_mod_cast this.ne'
    exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_left hc)
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact tzQ_im_pos hR hz
    · intro hw
      have hw' : 0 < w.im := hw
      have hden : (1 - (tzK R : ℂ) * w) ≠ 0 := by
        intro h
        have h2 := congrArg Complex.im h
        simp at h2
        rcases h2 with h2 | h2
        · exact hk0.ne' h2
        · exact hw'.ne' h2
      have hden' : (1 - w * (tzK R : ℂ)) ≠ 0 := by rw [mul_comm]; exact hden
      have hdpos := Complex.normSq_pos.mpr hden
      refine ⟨((tzQc R : ℂ) * w + tzQc R) / (1 - (tzK R : ℂ) * w), ?_, ?_⟩
      · show 0 < (((tzQc R : ℂ) * w + tzQc R) / (1 - (tzK R : ℂ) * w)).im
        rw [Complex.div_im, ← sub_div]
        apply div_pos _ hdpos
        have e : ((tzQc R : ℂ) * w + tzQc R).im * (1 - (tzK R : ℂ) * w).re -
            ((tzQc R : ℂ) * w + tzQc R).re * (1 - (tzK R : ℂ) * w).im =
            tzQc R * (1 + tzK R) * w.im := by
          simp; ring
        rw [e]
        have : 0 < 1 + tzK R := by linarith
        positivity
      · have hq : (tzQc R : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
        have hk : (1 + (tzK R : ℂ)) ≠ 0 := by
          have : (0 : ℝ) < 1 + tzK R := by linarith
          exact_mod_cast this.ne'
        have hD : (tzK R : ℂ) * (((tzQc R : ℂ) * w + tzQc R) / (1 - (tzK R : ℂ) * w)) + tzQc R
            = tzQc R * (1 + tzK R) / (1 - (tzK R : ℂ) * w) := by
          field_simp; ring
        unfold tzQ
        rw [hD, div_eq_iff (div_ne_zero (mul_ne_zero hq hk) hden)]
        field_simp
        ring

/-! ### Piece B: the map `W` -/

/-- Off the pole, `W = scMap k ∘ Q`. -/
theorem tzB_W_of_ne {R : ℝ} {z : ℂ} (hz : z ≠ (tzPole R : ℂ)) :
    tzW R z = scMap (tzK R) (tzQ R z) := by
  unfold tzW
  rw [if_neg hz]

theorem tzW_differentiableAt {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ (tzW R) z := by
  have hk₀ := tzK_pos hR
  have hk₁ := tzK_lt_one hR
  have hne : ∀ w : ℂ, 0 < w.im → w ≠ (tzPole R : ℂ) := fun w hw h => by
    rw [h, ofReal_im] at hw
    exact lt_irrefl _ hw
  have hev : tzW R =ᶠ[𝓝 z] fun w => scMap (tzK R) (tzQ R w) := by
    filter_upwards [isOpen_upperHalf'.mem_nhds (show z ∈ upperHalf from hz)] with w hw
    exact tzB_W_of_ne (hne w hw)
  exact ((hasDerivAt_scMap hk₀ hk₁ (tzQ_im_pos hR hz)).differentiableAt.comp z
    (tzQ_differentiableAt hR (hne z hz))).congr_of_eventuallyEq hev

/-- `k z₀ + q = 0`. -/
theorem tzB_pole_eq {R : ℝ} (hR : 0 < R) : tzK R * tzPole R + tzQc R = 0 := by
  have hk₁ := tzK_lt_one hR
  have h : 1 - tzK R ≠ 0 := by linarith
  unfold tzPole tzQc
  field_simp
  ring

/-- `q > 0`. -/
theorem tzB_qc_pos {R : ℝ} (hR : 0 < R) : 0 < tzQc R := by
  have hk₀ := tzK_pos hR
  have hk₁ := tzK_lt_one hR
  unfold tzQc
  exact div_pos (by linarith) (by linarith)

/-- The denominator of `Q` vanishes only at the pole. -/
theorem tzB_den_ne {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ≠ (tzPole R : ℂ)) :
    (tzK R : ℂ) * z + tzQc R ≠ 0 := by
  have hk₀ := tzK_pos hR
  have hc : (tzK R : ℂ) * (tzPole R : ℂ) + (tzQc R : ℂ) = 0 := by exact_mod_cast tzB_pole_eq hR
  have h : (tzK R : ℂ) * z + tzQc R = tzK R * (z - tzPole R) := by linear_combination hc
  rw [h]
  exact mul_ne_zero (ofReal_ne_zero.2 hk₀.ne') (sub_ne_zero.2 hz)

/-- `Q` maps the closed upper half-plane minus the pole into the closed upper half-plane. -/
theorem tzB_Q_im_nonneg {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : 0 ≤ z.im)
    (hz₀ : z ≠ (tzPole R : ℂ)) : 0 ≤ (tzQ R z).im := by
  rcases hz.lt_or_eq with h | h
  · exact (tzQ_im_pos hR h).le
  · have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [← h])
    have hne : z.re ≠ tzPole R := fun he => hz₀ (by rw [hzr, he])
    obtain ⟨y, hy, -⟩ := tzQ_ofReal hR hne
    rw [hzr, hy, ofReal_im]

/-- `w ↦ -1/(kw)` preserves the closed upper half-plane. -/
theorem tzB_im_neg_inv {k : ℝ} (hk : 0 < k) {w : ℂ} (hw : 0 ≤ w.im) :
    0 ≤ (-1 / ((k : ℂ) * w)).im := by
  have h : -1 / ((k : ℂ) * w) = ((-1 / k : ℝ) : ℂ) * w⁻¹ := by
    push_cast
    ring
  rw [h, im_ofReal_mul, inv_im]
  refine mul_nonneg_of_nonpos_of_nonpos ?_ ?_
  · rw [neg_div]
    exact neg_nonpos.2 (by positivity)
  · rw [neg_div]
    exact neg_nonpos.2 (div_nonneg hw (normSq_nonneg w))

/-- `W` continues holomorphically across every real point other than `-1, 0, R` (the pole included). -/
theorem tzW_local_ext {R : ℝ} (hR : 0 < R) {x : ℝ} (hx₁ : x ≠ -1) (hx₀ : x ≠ 0) (hxR : x ≠ R) :
    ∃ ε > 0, ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball (x : ℂ) ε) ∧
      ∀ z ∈ ball (x : ℂ) ε, 0 ≤ z.im → H z = tzW R z := by
  have hk₀ := tzK_pos hR
  have hk₁ := tzK_lt_one hR
  have h1k : 1 < 1 / tzK R := one_lt_one_div hk₀ hk₁
  have hz₀ := tzPole_lt hR
  by_cases hxp : x = tzPole R
  swap
  · obtain ⟨y, hy, hyl, hyb, hym, hyt⟩ := tzQ_ofReal hR hxp
    have habs : ∀ j, |scPrevertex (tzK R) j| ≤ 1 / tzK R := by
      intro j
      fin_cases j
      · show |(-1 / tzK R)| ≤ 1 / tzK R
        rw [neg_div, abs_neg, abs_of_pos (by positivity)]
      · show |(-1 : ℝ)| ≤ 1 / tzK R
        rw [abs_neg, abs_one]
        exact h1k.le
      · show |(1 : ℝ)| ≤ 1 / tzK R
        rw [abs_one]
        exact h1k.le
      · show |1 / tzK R| ≤ 1 / tzK R
        rw [abs_of_pos (by positivity)]
    have hy_np : ∀ j, y ≠ scPrevertex (tzK R) j := by
      intro j hj
      rcases lt_or_gt_of_ne hx₁ with h1 | h1
      · have := hyl h1
        rw [hj] at this
        linarith [habs j]
      · rcases lt_or_gt_of_ne hx₀ with h0 | h0
        · exact scNoPrevertex_bottom hk₀ hk₁ j (by rw [← hj]; exact hyb h1 h0)
        · rcases lt_or_gt_of_ne hxR with h2 | h2
          · exact scNoPrevertex_right hk₀ hk₁ j (by rw [← hj]; exact hym h0 h2)
          · exact scNoPrevertex_top hk₀ hk₁ j (by rw [← hj]; exact hyt h2)
    obtain ⟨ε₁, hε₁, H₁, hH₁, hH₁eq⟩ := gz_scMap_local_ext hk₀ hk₁ hy_np
    have hx' : (x : ℂ) ≠ (tzPole R : ℂ) := by exact_mod_cast hxp
    have hQc : ContinuousAt (tzQ R) x := (tzQ_differentiableAt hR hx').continuousAt
    have hnhds : tzQ R ⁻¹' ball (y : ℂ) ε₁ ∩ {w : ℂ | w ≠ (tzPole R : ℂ)} ∈ 𝓝 (x : ℂ) := by
      refine Filter.inter_mem (hQc.preimage_mem_nhds ?_) (isOpen_ne.mem_nhds hx')
      rw [hy]
      exact isOpen_ball.mem_nhds (mem_ball_self hε₁)
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hnhds
    refine ⟨δ, hδ, H₁ ∘ tzQ R, ?_, ?_⟩
    · intro z hz
      have h1 := hδsub hz
      exact ((hH₁.differentiableAt (isOpen_ball.mem_nhds h1.1)).comp z
        (tzQ_differentiableAt hR h1.2)).differentiableWithinAt
    · intro z hz hzim
      have h1 := hδsub hz
      rw [Function.comp_apply, tzB_W_of_ne h1.2]
      exact hH₁eq _ h1.1 (tzB_Q_im_nonneg hR hzim h1.2)
  · -- the pole: use the inversion identity `scMap ζ = a + bi - scMap (-1/(kζ))`
    have hq := tzB_qc_pos hR
    have hc : (tzK R : ℂ) * (tzPole R : ℂ) + (tzQc R : ℂ) = 0 := by exact_mod_cast tzB_pole_eq hR
    have hk0 : (tzK R : ℂ) ≠ 0 := ofReal_ne_zero.2 hk₀.ne'
    have h0np : ∀ j, (0 : ℝ) ≠ scPrevertex (tzK R) j := by
      intro j
      fin_cases j
      · show (0 : ℝ) ≠ -1 / tzK R
        rw [neg_div]
        exact (neg_neg_of_pos (by positivity)).ne'
      · show (0 : ℝ) ≠ -1
        norm_num
      · show (0 : ℝ) ≠ 1
        norm_num
      · show (0 : ℝ) ≠ 1 / tzK R
        exact (show (0 : ℝ) < 1 / tzK R by positivity).ne
    obtain ⟨ε₁, hε₁, E, hE, hEeq⟩ := gz_scMap_local_ext hk₀ hk₁ h0np
    set Qt : ℂ → ℂ := fun z => -((tzK R : ℂ) * z + tzQc R) / ((tzK R : ℂ) * (z - tzQc R)) with hQt
    have hpq : (tzPole R : ℂ) ≠ (tzQc R : ℂ) := by
      intro h
      have := ofReal_injective h
      linarith
    have hQtd : ∀ z : ℂ, z ≠ (tzQc R : ℂ) → DifferentiableAt ℂ Qt z := by
      intro z hz
      have hden : (tzK R : ℂ) * (z - tzQc R) ≠ 0 := mul_ne_zero hk0 (sub_ne_zero.2 hz)
      exact DifferentiableAt.div (by fun_prop) (by fun_prop) hden
    have hQt0 : Qt (tzPole R) = 0 := by
      simp only [hQt, hc, neg_zero, zero_div]
    have hQteq : ∀ z : ℂ, z ≠ (tzPole R : ℂ) → z ≠ (tzQc R : ℂ) →
        Qt z = -1 / ((tzK R : ℂ) * tzQ R z) := by
      intro z hz hzq
      have hden := tzB_den_ne hR hz
      have hsub : z - (tzQc R : ℂ) ≠ 0 := sub_ne_zero.2 hzq
      simp only [hQt, tzQ]
      field_simp
    have hx' : (x : ℂ) = (tzPole R : ℂ) := by rw [hxp]
    have hQtc : ContinuousAt Qt (tzPole R) := (hQtd _ hpq).continuousAt
    have hnhds : Qt ⁻¹' ball ((0 : ℝ) : ℂ) ε₁ ∩ {w : ℂ | w ≠ (tzQc R : ℂ)} ∈ 𝓝 (x : ℂ) := by
      rw [hx']
      refine Filter.inter_mem (hQtc.preimage_mem_nhds ?_) (isOpen_ne.mem_nhds hpq)
      rw [hQt0, ← ofReal_zero]
      exact isOpen_ball.mem_nhds (mem_ball_self hε₁)
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hnhds
    have hF0 : scMap (tzK R) ((0 : ℝ) : ℂ) = scSideA (tzK R) + scSideB (tzK R) / 2 * I := by
      rw [scMap_ofReal_right hk₀ hk₁ ⟨by norm_num, by norm_num⟩,
        integral_scDensity_neg_one_zero hk₀ hk₁]
      push_cast
      ring
    refine ⟨δ, hδ, fun z => (scSideA (tzK R) + scSideB (tzK R) * I : ℂ) - E (Qt z), ?_, ?_⟩
    · intro z hz
      have h1 := hδsub hz
      exact ((differentiableAt_const _).sub ((hE.differentiableAt (isOpen_ball.mem_nhds h1.1)).comp z
        (hQtd z h1.2))).differentiableWithinAt
    · intro z hz hzim
      have h1 := hδsub hz
      by_cases hzp : z = (tzPole R : ℂ)
      · have hW : tzW R z = scMapInfty (tzK R) := by
          unfold tzW
          rw [if_pos hzp]
        rw [hW, scMapInfty_eq hk₀ hk₁]
        simp only
        rw [hzp, hQt0, ← ofReal_zero, hEeq _ (mem_ball_self hε₁) (by simp), hF0]
        ring
      · have hzq : z ≠ (tzQc R : ℂ) := h1.2
        have hQim := tzB_Q_im_nonneg hR hzim hzp
        have hQ0 : tzQ R z ≠ 0 := by
          unfold tzQ
          exact div_ne_zero (sub_ne_zero.2 hzq) (tzB_den_ne hR hzp)
        have hsum := scMap_add_inversion hk₀ hk₁ hQim hQ0
        rw [← hQteq z hzp hzq] at hsum
        have hQtim : 0 ≤ (Qt z).im := by
          rw [hQteq z hzp hzq]
          exact tzB_im_neg_inv hk₀ hQim
        simp only
        rw [hEeq _ h1.1 hQtim, tzB_W_of_ne hzp]
        linear_combination (-1 : ℂ) * hsum

theorem tzW_isConformalOnto {R : ℝ} (hR : 0 < R) :
    IsConformalOnto (tzW R) upperHalf (rectangle (scSideA (tzK R)) (scSideB (tzK R))) := by
  have hk₀ := tzK_pos hR
  have hk₁ := tzK_lt_one hR
  have hne : ∀ w : ℂ, w ∈ upperHalf → w ≠ (tzPole R : ℂ) := fun w hw h => by
    have hw' : 0 < w.im := hw
    rw [h, ofReal_im] at hw'
    exact lt_irrefl _ hw'
  have heq : EqOn (scMap (tzK R) ∘ tzQ R) (tzW R) upperHalf := fun w hw => by
    rw [Function.comp_apply, tzB_W_of_ne (hne w hw)]
  obtain ⟨hd, hi, hs⟩ := IsConformalOnto.comp (isConformalOnto_scMap hk₀ hk₁) (tzQ_isConformalOnto hR)
  exact ⟨hd.congr heq.symm, hi.congr heq, by rw [← heq.image_eq]; exact hs⟩

/-- Boundary values of `W` on the real axis. -/
theorem tzW_ofReal {R : ℝ} (hR : 0 < R) {x : ℝ} :
    (x < -1 → (tzW R x).re = 0 ∧ (tzW R x).im ∈ Ioo 0 (scSideB (tzK R))) ∧
    (x ∈ Ioo (-1 : ℝ) 0 → (tzW R x).im = 0) ∧
    (x ∈ Ioo 0 R → (tzW R x).re = scSideA (tzK R) ∧ (tzW R x).im ∈ Ioo 0 (scSideB (tzK R))) ∧
    (R < x → (tzW R x).im = scSideB (tzK R)) := by
  have hk₀ := tzK_pos hR
  have hk₁ := tzK_lt_one hR
  have hz₀ := tzPole_lt hR
  have hb := (scSide_pos hk₀ hk₁).2
  have hB := scSideB_eq_integral_scDensity hk₀ hk₁
  have hmid : ∀ u ∈ Ioo (-1 : ℝ) 1, 0 < ∫ s in (-1 : ℝ)..u, scDensity (tzK R) s ∧
      ∫ s in (-1 : ℝ)..u, scDensity (tzK R) s < scSideB (tzK R) := by
    intro u hu
    refine ⟨integral_scDensity_pos hk₀ hk₁ hu.1 fun j hj =>
      scNoPrevertex_right hk₀ hk₁ j ⟨hj.1, hj.2.trans hu.2⟩, ?_⟩
    rw [hB]
    exact integral_scDensity_strictMonoOn hk₀ hk₁ (scNoPrevertex_right hk₀ hk₁) (-1)
      ⟨hu.1.le, hu.2.le⟩ ⟨by norm_num, le_rfl⟩ hu.2
  refine ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_, fun hx => ?_⟩
  · by_cases hxp : x = tzPole R
    · have hW : tzW R x = scMapInfty (tzK R) := by
        unfold tzW
        rw [if_pos (by rw [hxp])]
      rw [hW, scMapInfty_eq hk₀ hk₁]
      simp only [mul_re, mul_im, div_re, div_im, ofReal_re, ofReal_im, I_re, I_im, mem_Ioo]
      norm_num
      constructor <;> linarith
    · obtain ⟨y, hy, hyl, -⟩ := tzQ_ofReal hR hxp
      have hy1 := hyl hx
      obtain ⟨-, -, hray⟩ := scMap_ofReal_ray hk₀ hk₁ hy1.le
      have hy0 : y ≠ 0 := by
        rintro rfl
        rw [abs_zero] at hy1
        linarith [(show (0 : ℝ) < 1 / tzK R by positivity)]
      have hu : -1 / (tzK R * y) ∈ Ioo (-1 : ℝ) 1 := by
        have hky : 1 < tzK R * |y| := by
          have h := (div_lt_iff₀ hk₀).1 hy1
          linarith [mul_comm |y| (tzK R)]
        have habs : |-1 / (tzK R * y)| < 1 := by
          rw [abs_div, abs_neg, abs_one, abs_mul, abs_of_pos hk₀,
            div_lt_one (mul_pos hk₀ (abs_pos.2 hy0))]
          exact hky
        exact abs_lt.1 habs
      rw [tzB_W_of_ne (by exact_mod_cast hxp), hy, hray]
      obtain ⟨h1, h2⟩ := hmid _ hu
      simp only [mul_re, mul_im, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im, mem_Ioo]
      refine ⟨by ring, by linarith, by linarith⟩
  · have hxp : x ≠ tzPole R := by linarith [hx.1]
    obtain ⟨y, hy, -, hyb, -⟩ := tzQ_ofReal hR hxp
    have hy1 := hyb hx.1 hx.2
    rw [tzB_W_of_ne (by exact_mod_cast hxp), hy,
      scMap_ofReal_bottom hk₀ hk₁ ⟨hy1.1.le, hy1.2.le⟩, ofReal_im]
  · have hxp : x ≠ tzPole R := by linarith [hx.1]
    obtain ⟨y, hy, -, -, hym, -⟩ := tzQ_ofReal hR hxp
    have hy1 := hym hx.1 hx.2
    rw [tzB_W_of_ne (by exact_mod_cast hxp), hy, scMap_ofReal_right hk₀ hk₁ ⟨hy1.1.le, hy1.2.le⟩]
    obtain ⟨h1, h2⟩ := hmid _ hy1
    simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, mem_Ioo]
    refine ⟨by ring, by linarith, by linarith⟩
  · have hxp : x ≠ tzPole R := by linarith
    obtain ⟨y, hy, -, -, -, hyt⟩ := tzQ_ofReal hR hxp
    have hy1 := hyt hx
    rw [tzB_W_of_ne (by exact_mod_cast hxp), hy, scMap_ofReal_top hk₀ hk₁ ⟨hy1.1.le, hy1.2.le⟩]
    simp

/-- The restriction of `W` to the real axis is continuous off the pole. -/
theorem tzB_continuousAt_ofReal {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : x ≠ tzPole R) :
    ContinuousAt (fun x : ℝ => tzW R x) x := by
  have hk₀ := tzK_pos hR
  have hk₁ := tzK_lt_one hR
  have hx' : (x : ℂ) ≠ (tzPole R : ℂ) := by exact_mod_cast hx
  have hev : (fun x : ℝ => scMap (tzK R) (tzQ R x)) =ᶠ[𝓝 x] fun x : ℝ => tzW R x := by
    filter_upwards [isOpen_ne.mem_nhds hx] with x' hx'
    rw [tzB_W_of_ne (by exact_mod_cast hx')]
  refine ContinuousAt.congr ?_ hev
  have hQ : ContinuousAt (fun x : ℝ => tzQ R x) x :=
    (tzQ_differentiableAt hR hx').continuousAt.comp continuous_ofReal.continuousAt
  have hmem : tzQ R x ∈ {z : ℂ | 0 ≤ z.im} := tzB_Q_im_nonneg hR (by simp) hx'
  have hT : Tendsto (fun x : ℝ => tzQ R x) (𝓝 x) (𝓝[{z : ℂ | 0 ≤ z.im}] (tzQ R x)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hQ, ?_⟩
    filter_upwards [isOpen_ne.mem_nhds hx] with x' hx'
    exact tzB_Q_im_nonneg hR (by simp) (by exact_mod_cast hx')
  exact (continuousOn_scMap hk₀ hk₁ _ hmem).tendsto.comp hT

/-- The restriction of `W` to the real axis is continuous (the pole included). -/
theorem tzB_continuous_ofReal {R : ℝ} (hR : 0 < R) : Continuous fun x : ℝ => tzW R x := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hxp : x = tzPole R
  · have hz₀ := tzPole_lt hR
    obtain ⟨ε, hε, H, hH, hHeq⟩ := tzW_local_ext hR (x := x) (by rw [hxp]; linarith)
      (by rw [hxp]; linarith) (by rw [hxp]; linarith)
    have hHc : ContinuousAt (fun x : ℝ => H x) x :=
      (hH.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hε))).comp
        continuous_ofReal.continuousAt
    refine hHc.congr ?_
    have hb : ∀ᶠ x' : ℝ in 𝓝 x, (x' : ℂ) ∈ ball (x : ℂ) ε :=
      continuous_ofReal.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hε))
    filter_upwards [hb] with x' hx'
    exact hHeq _ hx' (by simp)
  · exact tzB_continuousAt_ofReal hR hxp

/-- `Im W(x) → b` as `x → -∞`. -/
theorem tzB_tendsto_atBot {R : ℝ} (hR : 0 < R) :
    Tendsto (fun x : ℝ => (tzW R x).im) atBot (𝓝 (scSideB (tzK R))) := by
  have hk₀ := tzK_pos hR
  have hk₁ := tzK_lt_one hR
  have hc := tzB_pole_eq hR
  have hden : Tendsto (fun x : ℝ => tzK R * x + tzQc R) atBot atBot :=
    tendsto_atBot_add_const_right _ (tzQc R) (tendsto_id.const_mul_atBot hk₀)
  have hlim0 : Tendsto (fun x : ℝ => 1 / tzK R - (tzQc R + tzQc R / tzK R) / (tzK R * x + tzQc R))
      atBot (𝓝 (1 / tzK R - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atBot hden)
  rw [sub_zero] at hlim0
  have hreal : Tendsto (fun x : ℝ => (x - tzQc R) / (tzK R * x + tzQc R)) atBot
      (𝓝 (1 / tzK R)) := by
    refine hlim0.congr' ?_
    filter_upwards [eventually_lt_atBot (tzPole R)] with x hx
    have hne : tzK R * x + tzQc R ≠ 0 := by
      have : tzK R * x + tzQc R = tzK R * (x - tzPole R) := by linear_combination hc
      rw [this]
      exact mul_ne_zero hk₀.ne' (sub_ne_zero.2 hx.ne)
    field_simp
    ring
  have hT : Tendsto (fun x : ℝ => ((((x - tzQc R) / (tzK R * x + tzQc R)) : ℝ) : ℂ)) atBot
      (𝓝[{z : ℂ | 0 ≤ z.im}] ((1 / tzK R : ℝ) : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_ofReal.tendsto _).comp hreal,
      Filter.Eventually.of_forall fun x => (ofReal_im _).ge⟩
  have hsc := (continuousOn_scMap hk₀ hk₁ ((1 / tzK R : ℝ) : ℂ) (by simp)).tendsto.comp hT
  have hv : scMap (tzK R) ((1 / tzK R : ℝ) : ℂ) = scSideB (tzK R) * I :=
    (scMap_prevertices hk₀ hk₁).2.2.2
  rw [hv] at hsc
  have hsc' := (continuous_im.tendsto _).comp hsc
  simp only [mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul, add_zero] at hsc'
  refine hsc'.congr' ?_
  filter_upwards [eventually_lt_atBot (tzPole R)] with x hx
  have hxp : (x : ℂ) ≠ (tzPole R : ℂ) := by exact_mod_cast hx.ne
  simp only [Function.comp_apply]
  rw [tzB_W_of_ne hxp]
  congr 2
  unfold tzQ
  push_cast
  ring

/-- `W` maps `(-∞,-1)` onto the left side and `(0,R)` onto the right side. -/
theorem tzW_ofReal_surj {R : ℝ} (hR : 0 < R) {t : ℝ} (ht : t ∈ Ioo 0 (scSideB (tzK R))) :
    (∃ x : ℝ, x < -1 ∧ tzW R x = (t : ℂ) * I) ∧
      (∃ x ∈ Ioo 0 R, tzW R x = (scSideA (tzK R) : ℂ) + (t : ℂ) * I) := by
  have hk₀ := tzK_pos hR
  have hk₁ := tzK_lt_one hR
  have hz₀ := tzPole_lt hR
  have hcim : Continuous fun x : ℝ => (tzW R x).im := continuous_im.comp (tzB_continuous_ofReal hR)
  have hQv := tzQ_vertices hR
  have hpv := scMap_prevertices hk₀ hk₁
  have hm1 : tzW R ((-1 : ℝ) : ℂ) = 0 := by
    rw [tzB_W_of_ne (by exact_mod_cast (show (-1 : ℝ) ≠ tzPole R by linarith)),
      show ((-1 : ℝ) : ℂ) = -1 by push_cast; rfl, hQv.1]
    exact hpv.1
  have h0 : tzW R ((0 : ℝ) : ℂ) = scSideA (tzK R) := by
    rw [tzB_W_of_ne (by exact_mod_cast (show (0 : ℝ) ≠ tzPole R by linarith)), ofReal_zero,
      hQv.2.1]
    have h := hpv.2.1
    rwa [scPrevertex_one, ofReal_neg, ofReal_one] at h
  have hRv : tzW R (R : ℂ) = scSideA (tzK R) + scSideB (tzK R) * I := by
    rw [tzB_W_of_ne (by exact_mod_cast (show R ≠ tzPole R by linarith)), hQv.2.2]
    have h := hpv.2.2.1
    rwa [scPrevertex_two, ofReal_one] at h
  constructor
  · obtain ⟨X, hX1, hX2⟩ := (((tzB_tendsto_atBot hR).eventually (lt_mem_nhds ht.2)).and
      (eventually_lt_atBot (-1))).exists
    have hivt := intermediate_value_Ioo' hX2.le hcim.continuousOn
    simp only [hm1, zero_im] at hivt
    obtain ⟨x, hx, hxt⟩ := hivt ⟨ht.1, hX1⟩
    refine ⟨x, hx.2, Complex.ext ?_ ?_⟩
    · rw [((tzW_ofReal hR).1 hx.2).1]
      simp
    · simp only at hxt
      rw [hxt]
      simp
  · have hivt := intermediate_value_Ioo hR.le hcim.continuousOn
    simp only [h0, hRv, ofReal_im, add_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
      zero_add, add_zero] at hivt
    obtain ⟨x, hx, hxt⟩ := hivt ht
    refine ⟨x, hx, Complex.ext ?_ ?_⟩
    · rw [((tzW_ofReal hR).2.2.1 hx).1]
      simp
    · simp only at hxt
      rw [hxt]
      simp

/-! ### Piece C: the width function `X` -/

theorem tzX_left {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : x < -1) : tzX R x = 0 := by
  rw [tzX, gzC_fold_ofReal]
  exact ((tzW_ofReal hR (x := x)).1 hx).1

theorem tzX_right {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : x ∈ Ioo 0 R) : tzX R x = scSideA (tzK R) := by
  rw [tzX, gzC_fold_ofReal]
  exact ((tzW_ofReal hR (x := x)).2.2.1 hx).1

/-- The fold maps `ℂ ∖ {-1, 0, R}` into itself. -/
theorem tzC_fold_mem {R : ℝ} {z : ℂ} (hz : z ∈ ({-1, 0, (R : ℂ)}ᶜ : Set ℂ)) :
    gzFold z ∈ ({-1, 0, (R : ℂ)}ᶜ : Set ℂ) := by
  unfold gzFold
  split_ifs with h
  · exact hz
  · intro h'
    apply hz
    rcases h' with h' | h' | h'
    · exact Or.inl (by rw [← conj_conj z, h']; simp)
    · exact Or.inr (Or.inl (by rw [← conj_conj z, h']; simp))
    · exact Or.inr (Or.inr (by rw [← conj_conj z, h', conj_ofReal]; exact mem_singleton _))

/-- Near every point of the closed upper half-plane other than `-1, 0, R`, `W` agrees on the closed
upper half-plane with a function holomorphic on a ball. -/
theorem tzC_local {R : ℝ} (hR : 0 < R) {w₀ : ℂ}
    (hw : w₀ ∈ ({-1, 0, (R : ℂ)}ᶜ : Set ℂ)) (him : 0 ≤ w₀.im) :
    ∃ ε > 0, ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball w₀ ε) ∧
      ∀ w ∈ ball w₀ ε, 0 ≤ w.im → H w = tzW R w := by
  rcases him.lt_or_eq with hpos | hzero
  · refine ⟨w₀.im, hpos, tzW R, ?_, fun w _ _ => rfl⟩
    intro w hw'
    rw [mem_ball, dist_eq_norm] at hw'
    have him' : 0 < w.im := by
      have h3 := abs_im_le_norm (w - w₀)
      rw [sub_im] at h3
      have := (abs_le.1 h3).1
      linarith
    exact (tzW_differentiableAt hR him').differentiableWithinAt
  · have hw₀ : w₀ = ((w₀.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hzero.symm])
    have hx1 : w₀.re ≠ -1 := fun h => hw (Or.inl (by rw [hw₀, h]; simp))
    have hx0 : w₀.re ≠ 0 := fun h => hw (Or.inr (Or.inl (by rw [hw₀, h, ofReal_zero])))
    have hxR : w₀.re ≠ R := fun h => hw (Or.inr (Or.inr (by rw [hw₀, h]; exact mem_singleton _)))
    obtain ⟨ε, hε, H, hH, hHe⟩ := tzW_local_ext hR hx1 hx0 hxR
    rw [← hw₀] at hH hHe
    exact ⟨ε, hε, H, hH, hHe⟩

/-- `Re W` is Lipschitz near every point of the closed upper half-plane other than `-1, 0, R`,
relative to the closed upper half-plane. -/
theorem tzC_Wre_lip {R : ℝ} (hR : 0 < R) {w₀ : ℂ}
    (hw : w₀ ∈ ({-1, 0, (R : ℂ)}ᶜ : Set ℂ)) (him : 0 ≤ w₀.im) :
    ∃ K : ℝ≥0, ∃ V ∈ 𝓝 w₀, LipschitzOnWith K (fun w => (tzW R w).re) (V ∩ {w | 0 ≤ w.im}) := by
  obtain ⟨ε, hε, H, hH, hHe⟩ := tzC_local hR hw him
  have hcd : ContDiffAt ℂ 1 H w₀ := (hH.analyticAt (ball_mem_nhds w₀ hε)).contDiffAt
  obtain ⟨K, V, hV, hlip⟩ := hcd.exists_lipschitzOnWith
  refine ⟨K, V ∩ ball w₀ ε, inter_mem hV (ball_mem_nhds w₀ hε), ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun w hw w' hw' => ?_
  rw [← hHe w hw.1.2 hw.2, ← hHe w' hw'.1.2 hw'.2, Real.dist_eq, ← sub_re]
  refine (abs_re_le_norm _).trans ?_
  rw [← dist_eq_norm]
  exact hlip.dist_le_mul w hw.1.1 w' hw'.1.1

theorem tzX_locallyLipschitzOn {R : ℝ} (hR : 0 < R) :
    LocallyLipschitzOn ({-1, 0, (R : ℂ)}ᶜ) (tzX R) := by
  intro z hz
  obtain ⟨K, V, hV, hlip⟩ := tzC_Wre_lip hR (tzC_fold_mem hz) (gzC_fold_im_nonneg z)
  refine ⟨K * 1, gzFold ⁻¹' V, mem_nhdsWithin_of_mem_nhds
    (gzC_fold_lipschitz.continuous.continuousAt.preimage_mem_nhds hV), ?_⟩
  exact hlip.comp gzC_fold_lipschitz.lipschitzOnWith (fun w hw => ⟨hw, gzC_fold_im_nonneg w⟩)

/-- The elementary estimate `|Re (a d)| ≤ 2A · (|a|/(2A)) · |c'|` when `|d| = |c'|`. -/
theorem tzC_enorm_re_le {A : ℝ} (hA : 0 < A) (a d c' : ℂ) (hd : ‖d‖ = ‖c'‖) :
    ‖(a * d).re‖ₑ ≤ ENNReal.ofReal (2 * A) * (ENNReal.ofReal (‖a‖ / (2 * A)) * ‖c'‖ₑ) := by
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs]
  refine (abs_re_le_norm _).trans (le_of_eq ?_)
  rw [norm_mul, hd]
  field_simp

/-- The pointwise bound `|(X ∘ c)'| ≤ 2a ρ(c) |c'|` at a point where `c` is differentiable. -/
theorem tzC_deriv_bound {R : ℝ} (hR : 0 < R) {c : ℝ → ℂ} {u : ℝ} {c' : ℂ}
    (hc : HasDerivAt c c' u) (hmem : c u ∈ ({-1, 0, (R : ℂ)}ᶜ : Set ℂ)) :
    ‖deriv (tzX R ∘ c) u‖ₑ ≤ ENNReal.ofReal (2 * scSideA (tzK R)) * (tzRho R (c u) * ‖c'‖ₑ) := by
  have ha := (scSide_pos (tzK_pos hR) (tzK_lt_one hR)).1
  rcases lt_trichotomy (c u).im 0 with hneg | hzero | hpos
  · have hwpos : 0 < (conj (c u)).im := by rw [conj_im]; linarith
    have hW := (tzW_differentiableAt hR hwpos).hasDerivAt
    have hcc : HasDerivAt (fun s => conj (c s)) (conj c') u := by
      simpa using hc.star
    have h1 : HasDerivAt (fun s => (tzW R (conj (c s))).re)
        (deriv (tzW R) (conj (c u)) * conj c').re u :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (HasDerivAt.comp (h₂ := tzW R) u hW hcc)
    have hev : (tzX R ∘ c) =ᶠ[𝓝 u] fun s => (tzW R (conj (c s))).re := by
      filter_upwards [hc.continuousAt.preimage_mem_nhds
        ((isOpen_lt Complex.continuous_im continuous_const).mem_nhds hneg)] with s hs
      have hs' : (c s).im < 0 := hs
      simp only [Function.comp_apply, tzX, gzFold, if_neg (not_le.mpr hs')]
    rw [(h1.congr_of_eventuallyEq hev).deriv]
    have hr : tzRho R (c u) =
        ENNReal.ofReal (‖deriv (tzW R) (conj (c u))‖ / (2 * scSideA (tzK R))) := by
      simp only [tzRho, if_neg hneg.ne, gzFold, if_neg (not_le.mpr hneg)]
    rw [hr]
    exact tzC_enorm_re_le ha _ _ _ (Complex.norm_conj _)
  · rw [show tzRho R (c u) = ⊤ from if_pos hzero]
    by_cases hc' : c' = 0
    · have hSopen : IsOpen ({-1, 0, (R : ℂ)}ᶜ : Set ℂ) :=
        (((finite_singleton _).insert _).insert _).isClosed.isOpen_compl
      obtain ⟨K, t, ht, hlip⟩ := tzX_locallyLipschitzOn hR hmem
      rw [hSopen.nhdsWithin_eq hmem] at ht
      rw [hc'] at hc
      rw [(gzC_hasDerivAt_comp_zero ht hlip hc).deriv]
      simp
    · rw [ENNReal.top_mul (enorm_ne_zero.2 hc'),
        ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
      exact le_top
  · have hW := (tzW_differentiableAt hR hpos).hasDerivAt
    have h1 : HasDerivAt (fun s => (tzW R (c s)).re) (deriv (tzW R) (c u) * c').re u :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (HasDerivAt.comp (h₂ := tzW R) u hW hc)
    have hev : (tzX R ∘ c) =ᶠ[𝓝 u] fun s => (tzW R (c s)).re := by
      filter_upwards [hc.continuousAt.preimage_mem_nhds
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos)] with s hs
      have hs' : 0 < (c s).im := hs
      simp only [Function.comp_apply, tzX, gzFold, if_pos hs'.le]
    rw [(h1.congr_of_eventuallyEq hev).deriv]
    have hr : tzRho R (c u) = ENNReal.ofReal (‖deriv (tzW R) (c u)‖ / (2 * scSideA (tzK R))) := by
      simp only [tzRho, if_neg hpos.ne', gzFold, if_pos hpos.le]
    rw [hr]
    exact tzC_enorm_re_le ha _ _ _ rfl

/-- **The width estimate along a Lipschitz arc.** -/
theorem tz_X_sub_le {R : ℝ} (hR : 0 < R) {c : ℝ → ℂ} {K : ℝ≥0} {s₀ s₁ : ℝ}
    (hs : s₀ ≤ s₁) (hc : LipschitzOnWith K c (Icc s₀ s₁))
    (hmem : ∀ t ∈ Icc s₀ s₁, c t ∈ ({-1, 0, (R : ℂ)}ᶜ : Set ℂ)) :
    ENNReal.ofReal |tzX R (c s₁) - tzX R (c s₀)|
      ≤ ENNReal.ofReal (2 * scSideA (tzK R)) * ∫⁻ t in Ioo s₀ s₁, tzRho R (c t) * ‖deriv c t‖ₑ := by
  have hXc : LocallyLipschitzOn (Icc s₀ s₁) (tzX R ∘ c) := by
    intro x hx
    obtain ⟨K', t, ht, hlip⟩ := tzX_locallyLipschitzOn hR (hmem x hx)
    refine ⟨K' * K, c ⁻¹' t ∩ Icc s₀ s₁,
      inter_mem ((hc.continuousOn x hx).tendsto_nhdsWithin hmem ht) self_mem_nhdsWithin, ?_⟩
    exact hlip.comp (hc.mono inter_subset_right) (fun s hs => hs.1)
  obtain ⟨L, hL⟩ := hXc.exists_lipschitzOnWith_of_compact isCompact_Icc
  have hftc : ∫ u in s₀..s₁, deriv (tzX R ∘ c) u = tzX R (c s₁) - tzX R (c s₀) :=
    (hL.mono (uIcc_of_le hs).subset).absolutelyContinuousOnInterval.integral_deriv_eq_sub
  have hA : ∀ᵐ u, u ∈ Ioo s₀ s₁ → DifferentiableAt ℝ c u := by
    filter_upwards [(hc.mono Ioo_subset_Icc_self).ae_differentiableWithinAt_of_mem_real]
      with u hu huI
    exact (hu huI).differentiableAt (Ioo_mem_nhds huI.1 huI.2)
  rw [← hftc, intervalIntegral.integral_of_le hs, ← Real.norm_eq_abs, ofReal_norm]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_of_le_of_eq ?_ (setLIntegral_congr Ioo_ae_eq_Ioc).symm
  refine setLIntegral_mono_ae' measurableSet_Ioc ?_
  filter_upwards [hA, compl_mem_ae_iff.2 (measure_singleton s₁)] with u hu hu1 huI
  have huo : u ∈ Ioo s₀ s₁ := ⟨huI.1, lt_of_le_of_ne huI.2 hu1⟩
  exact tzC_deriv_bound hR (hu huo).hasDerivAt (hmem u (Ioo_subset_Icc_self huo))

/-! ### Piece D: separating curves -/

theorem tz_notMem_of_sep {R : ℝ} {B : Set ℂ}
    (hsep : SeparatesSets B {((-1 : ℂ) : ExtPlane), ((0 : ℂ) : ExtPlane)}
      {((R : ℂ) : ExtPlane), extInf}) :
    (-1 : ℂ) ∉ B ∧ (0 : ℂ) ∉ B ∧ (R : ℂ) ∉ B := by
  obtain ⟨x₁, _, x₂, _, h1, h2, _⟩ := hsep
  have hsub1 := connectedComponentIn_subset (toExt B)ᶜ x₁
  have hsub2 := connectedComponentIn_subset (toExt B)ᶜ x₂
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact hsub1 (h1 (by simp)) (mem_image_of_mem _ h)
  · exact hsub1 (h1 (by simp)) (mem_image_of_mem _ h)
  · exact hsub2 (h2 (by simp)) (mem_image_of_mem _ h)

/-- The closed real ray `(-∞, -1]` together with `∞` is preconnected in `ℂ̄`. -/
theorem tzD_isPreconnected_ray :
    IsPreconnected (toExt ((fun x : ℝ => (x : ℂ)) '' Iic (-1)) ∪ {extInf}) := by
  have hK : IsPreconnected (toExt ((fun x : ℝ => (x : ℂ)) '' Iic (-1))) :=
    (isPreconnected_Iic.image _ continuous_ofReal.continuousOn).image _
      OnePoint.continuous_coe.continuousOn
  refine hK.subset_closure subset_union_left ?_
  refine union_subset subset_closure (singleton_subset_iff.2 ?_)
  refine extInf_mem_closure_toExt_of_unbounded fun r =>
    ⟨((-(|r| + 1) : ℝ) : ℂ), ⟨-(|r| + 1), by simp only [mem_Iic]; linarith [abs_nonneg r], rfl⟩, ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  linarith [le_abs_self r]

/-- A separating curve meets both `(-∞,-1)` and `(0,R)`. -/
theorem tz_sep_meets {R : ℝ} (hR : 0 < R) {B : Set ℂ}
    (hsep : SeparatesSets B {((-1 : ℂ) : ExtPlane), ((0 : ℂ) : ExtPlane)}
      {((R : ℂ) : ExtPlane), extInf})
    {γ : LRCurve} (hγ : γ ∈ separatingCurves B) :
    (∃ t ∈ Icc (0 : ℝ) 1, ∃ x : ℝ, x < -1 ∧ γ.toFun t = x) ∧
      (∃ t ∈ Icc (0 : ℝ) 1, ∃ x ∈ Ioo 0 R, γ.toFun t = x) := by
  obtain ⟨hm1B, h0B, hRB⟩ := tz_notMem_of_sep hsep
  obtain ⟨x₁, _, x₂, _, h1, h2, hne⟩ := hsep
  obtain ⟨_, htr, hcc⟩ := hγ
  set E := (toExt B)ᶜ with hE
  have hm1 : ((-1 : ℂ) : ExtPlane) ∈ connectedComponentIn E x₁ := h1 (by simp)
  have hz0 : ((0 : ℂ) : ExtPlane) ∈ connectedComponentIn E x₁ := h1 (by simp)
  have hzR : ((R : ℂ) : ExtPlane) ∈ connectedComponentIn E x₂ := h2 (by simp)
  have hinf : extInf ∈ connectedComponentIn E x₂ := h2 (by simp)
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ B := fun t ht => htr (mem_image_of_mem _ ht)
  refine ⟨?_, ?_⟩
  · by_contra hno
    have hSC : toExt ((fun x : ℝ => (x : ℂ)) '' Iic (-1)) ∪ {extInf}
        ⊆ (toExt γ.closedTrace)ᶜ := by
      rintro p (⟨z, ⟨x, hx, rfl⟩, rfl⟩ | hp) ⟨w, ⟨t, ht, rfl⟩, hwz⟩
      · have hwz' : γ.toFun t = (x : ℂ) := OnePoint.coe_injective hwz
        rcases eq_or_lt_of_le (mem_Iic.1 hx) with h | h
        · exact hm1B (by simpa [hwz', h] using hmem t ht)
        · exact hno ⟨t, ht, x, h, hwz'⟩
      · rw [mem_singleton_iff] at hp
        exact OnePoint.coe_ne_infty _ (hwz.trans hp)
    have hm1S : ((-1 : ℂ) : ExtPlane) ∈ toExt ((fun x : ℝ => (x : ℂ)) '' Iic (-1)) ∪ {extInf} :=
      Or.inl ⟨-1, ⟨-1, mem_Iic.2 le_rfl, by simp⟩, rfl⟩
    have hinfS : extInf ∈ toExt ((fun x : ℝ => (x : ℂ)) '' Iic (-1)) ∪ {extInf} :=
      Or.inr (mem_singleton _)
    refine hcc _ (connectedComponentIn_subset _ _ hm1) _ (connectedComponentIn_subset _ _ hinf)
      ?_ (connectedComponentIn_eq
        (tzD_isPreconnected_ray.subset_connectedComponentIn hm1S hSC hinfS))
    rw [← connectedComponentIn_eq hm1, ← connectedComponentIn_eq hinf]
    exact hne
  · by_contra hno
    have hav : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ Icc (0 : ℝ) R, γ.toFun t ≠ x := by
      intro t ht x hx hx'
      rcases eq_or_lt_of_le hx.1 with h | h
      · exact h0B (by simpa [hx', ← h] using hmem t ht)
      rcases eq_or_lt_of_le hx.2 with h' | h'
      · exact hRB (by simpa [hx', h'] using hmem t ht)
      · exact hno ⟨t, ht, x, ⟨h, h'⟩, hx'⟩
    have heq := gzD_cc_eq_of_avoid hR.le hav
    have hz0' : (((0 : ℝ) : ℂ) : ExtPlane) ∈ connectedComponentIn E x₁ := by simpa using hz0
    refine hcc _ (connectedComponentIn_subset _ _ hz0') _ (connectedComponentIn_subset _ _ hzR)
      ?_ heq
    rw [← connectedComponentIn_eq hz0', ← connectedComponentIn_eq hzR]
    exact hne

/-- **Admissibility**: every separating curve of `B` has `ρ`-length at least `1`. -/
theorem tz_one_le_rhoLength {R : ℝ} (hR : 0 < R) {B : Set ℂ}
    (hsep : SeparatesSets B {((-1 : ℂ) : ExtPlane), ((0 : ℂ) : ExtPlane)}
      {((R : ℂ) : ExtPlane), extInf})
    {γ : LRCurve} (hγ : γ ∈ separatingCurves B) : 1 ≤ γ.rhoLength (tzRho R) := by
  obtain ⟨⟨t₁, ht₁, x₁, hx₁, hγ₁⟩, ⟨t₂, ht₂, x₂, hx₂, hγ₂⟩⟩ := tz_sep_meets hR hsep hγ
  obtain ⟨hm1B, h0B, hRB⟩ := tz_notMem_of_sep hsep
  obtain ⟨⟨K, hK, h01⟩, htr, _⟩ := hγ
  have hb : 0 < scSideA (tzK R) := (scSide_pos (tzK_pos hR) (tzK_lt_one hR)).1
  set b := scSideA (tzK R) with hbdef
  set c := ENNReal.ofReal (2 * b) with hc
  set f : ℝ → ℝ≥0∞ := fun t => tzRho R (γ.toFun t) * ‖deriv γ.toFun t‖ₑ with hf
  set Y : ℝ → ℝ := fun t => tzX R (γ.toFun t) with hY
  have hY₁ : Y t₁ = 0 := by simp only [hY, hγ₁]; exact tzX_left hR hx₁
  have hY₂ : Y t₂ = b := by simp only [hY, hγ₂]; exact tzX_right hR hx₂
  have hY01 : Y 0 = Y 1 := by simp only [hY, h01]
  have hmemB : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ ({-1, 0, (R : ℂ)}ᶜ : Set ℂ) := by
    intro t ht
    have h := htr (mem_image_of_mem _ ht)
    rintro (h' | h' | h')
    · exact hm1B (h' ▸ h)
    · exact h0B (h' ▸ h)
    · exact hRB (h' ▸ h)
  have key : ∀ s₀ s₁ : ℝ, 0 ≤ s₀ → s₀ ≤ s₁ → s₁ ≤ 1 →
      ENNReal.ofReal |Y s₁ - Y s₀| ≤ c * ∫⁻ t in Ioo s₀ s₁, f t := by
    intro s₀ s₁ h0 h01' h1
    have hsub' : Icc s₀ s₁ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc h0 h1
    exact tz_X_sub_le hR h01' (hK.mono hsub') fun t ht => hmemB t (hsub' ht)
  set m := min t₁ t₂ with hmdef
  set M := max t₁ t₂ with hMdef
  have hm0 : 0 ≤ m := le_min ht₁.1 ht₂.1
  have hmM : m ≤ M := min_le_max
  have hM1 : M ≤ 1 := max_le ht₁.2 ht₂.2
  have hmid : |Y M - Y m| = b := by
    rcases le_total t₁ t₂ with h | h
    · rw [hMdef, hmdef, max_eq_right h, min_eq_left h, hY₁, hY₂, sub_zero, abs_of_pos hb]
    · rw [hMdef, hmdef, max_eq_left h, min_eq_right h, hY₁, hY₂, zero_sub, abs_neg, abs_of_pos hb]
  have hout : b ≤ |Y m - Y 0| + |Y 1 - Y M| := by
    rw [← hmid, hY01]
    calc |Y M - Y m| = |-(Y 1 - Y M) + -(Y m - Y 1)| := by ring_nf
      _ ≤ |-(Y 1 - Y M)| + |-(Y m - Y 1)| := abs_add_le _ _
      _ = |Y m - Y 1| + |Y 1 - Y M| := by rw [abs_neg, abs_neg, add_comm]
  have hI2 : ENNReal.ofReal b ≤ c * ∫⁻ t in Ioo m M, f t := hmid ▸ key m M hm0 hmM hM1
  have hI13 : ENNReal.ofReal b ≤ c * ((∫⁻ t in Ioo 0 m, f t) + ∫⁻ t in Ioo M 1, f t) := by
    calc ENNReal.ofReal b ≤ ENNReal.ofReal (|Y m - Y 0| + |Y 1 - Y M|) := ENNReal.ofReal_le_ofReal hout
      _ = ENNReal.ofReal |Y m - Y 0| + ENNReal.ofReal |Y 1 - Y M| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ c * (∫⁻ t in Ioo 0 m, f t) + c * ∫⁻ t in Ioo M 1, f t :=
          add_le_add (key 0 m le_rfl hm0 (hmM.trans hM1)) (key M 1 (hm0.trans hmM) hM1 le_rfl)
      _ = _ := (mul_add _ _ _).symm
  have htot : c ≤ c * γ.rhoLength (tzRho R) := by
    calc c = ENNReal.ofReal b + ENNReal.ofReal b := by
          rw [hc, ← ENNReal.ofReal_add hb.le hb.le, two_mul]
      _ ≤ c * ((∫⁻ t in Ioo 0 m, f t) + ∫⁻ t in Ioo M 1, f t) + c * ∫⁻ t in Ioo m M, f t :=
          add_le_add hI13 hI2
      _ = c * ((∫⁻ t in Ioo 0 m, f t) + (∫⁻ t in Ioo m M, f t) + ∫⁻ t in Ioo M 1, f t) := by
          rw [← mul_add]; congr 1; ring
      _ ≤ c * ∫⁻ t in Ioo (0 : ℝ) 1, f t := by
          gcongr; exact gzD_lintegral_three hm0 hmM hM1
      _ = c * γ.rhoLength (tzRho R) := rfl
  have hc0 : c ≠ 0 := by rw [hc]; exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  nth_rewrite 1 [← mul_one c] at htot
  exact (ENNReal.mul_le_mul_iff_right hc0 hctop).1 htot

/-! ### Piece E: the area -/

theorem tz_measurable_rho (R : ℝ) : Measurable (tzRho R) := by
  unfold tzRho
  refine Measurable.ite ?_ measurable_const ?_
  · exact measurableSet_eq_fun Complex.measurable_im measurable_const
  · exact (((measurable_deriv (tzW R)).comp gzE_measurable_fold).norm.div_const _).ennreal_ofReal

theorem tz_lintegral_deriv_sq {R : ℝ} (hR : 0 < R) :
    ∫⁻ z in upperHalf, ‖deriv (tzW R) z‖ₑ ^ 2
      = ENNReal.ofReal (scSideA (tzK R) * scSideB (tzK R)) := by
  have hf := tzW_isConformalOnto hR
  have key := lintegral_image_conformal isOpen_upperHalf' hf (fun _ => 1)
  simp only [mul_one, lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ,
    univ_inter] at key
  rw [← key, volume_rectangle, ENNReal.ofReal_mul (scSide_pos (tzK_pos hR) (tzK_lt_one hR)).1.le]

theorem tz_rhoArea_le {R : ℝ} (hR : 0 < R) (B : Set ℂ) :
    rhoArea (tzRho R) B ≤ ENNReal.ofReal (scSideB (tzK R) / (2 * scSideA (tzK R))) := by
  have ha := (scSide_pos (tzK_pos hR) (tzK_lt_one hR)).1
  have hb := (scSide_pos (tzK_pos hR) (tzK_lt_one hR)).2
  set U : Set ℂ := upperHalf with hUdef
  set g : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (‖deriv (tzW R) w‖ / (2 * scSideA (tzK R))) ^ 2
    with hg
  have hUm : MeasurableSet U := isOpen_upperHalf'.measurableSet
  -- `g` on `U` in terms of `‖W'‖ₑ²`
  have hgU : ∫⁻ z in U, g z = ENNReal.ofReal (scSideB (tzK R) / (4 * scSideA (tzK R))) := by
    have h1 : ∀ w, g w = ‖deriv (tzW R) w‖ₑ ^ 2 * ENNReal.ofReal (1 / (2 * scSideA (tzK R))) ^ 2 := by
      intro w
      simp only [hg]
      rw [← mul_pow, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _), mul_one_div]
    simp_rw [h1]
    rw [lintegral_mul_const' _ _ (by simp), tz_lintegral_deriv_sq hR,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  -- the three pieces
  have hcover : (univ : Set ℂ) ⊆ (U ∪ (fun z => conj z) ⁻¹' U) ∪ {z : ℂ | z.im = 0} := by
    intro z _
    rcases lt_trichotomy z.im 0 with h | h | h
    · left; right
      show 0 < (conj z).im
      rw [Complex.conj_im]; linarith
    · right; exact h
    · left; left; exact h
  have hup : ∫⁻ z in U, tzRho R z ^ 2 = ∫⁻ z in U, g z := by
    refine setLIntegral_congr_fun hUm fun z hz => ?_
    have him : 0 < z.im := hz
    simp only [tzRho, hg, if_neg him.ne', gzFold, if_pos him.le]
  have hlow : ∫⁻ z in (fun z => conj z) ⁻¹' U, tzRho R z ^ 2 = ∫⁻ z in U, g z := by
    have hm : MeasurableSet ((fun z : ℂ => conj z) ⁻¹' U) :=
      Complex.continuous_conj.measurable hUm
    rw [← gzE_conj_measurePreserving.setLIntegral_comp_preimage_emb
      Complex.conjLIE.toHomeomorph.measurableEmbedding g U]
    refine setLIntegral_congr_fun hm fun z hz => ?_
    have him : 0 < (conj z).im := hz
    have him' : z.im < 0 := by rw [Complex.conj_im] at him; linarith
    have hfold : gzFold z = conj z := by
      unfold gzFold; rw [if_neg (not_le.mpr him')]
    simp only [tzRho, hg, if_neg him'.ne, hfold]
  have hreal : ∫⁻ z in {z : ℂ | z.im = 0}, tzRho R z ^ 2 = 0 :=
    setLIntegral_measure_zero _ _ gzE_volume_im_eq_zero
  calc rhoArea (tzRho R) B = ∫⁻ z in B, tzRho R z ^ 2 := rfl
    _ ≤ ∫⁻ z in (U ∪ (fun z => conj z) ⁻¹' U) ∪ {z : ℂ | z.im = 0}, tzRho R z ^ 2 :=
        lintegral_mono_set ((subset_univ B).trans hcover)
    _ ≤ (∫⁻ z in U, tzRho R z ^ 2) + (∫⁻ z in (fun z => conj z) ⁻¹' U, tzRho R z ^ 2)
          + ∫⁻ z in {z : ℂ | z.im = 0}, tzRho R z ^ 2 := by
        refine (lintegral_union_le _ _ _).trans ?_
        gcongr
        exact lintegral_union_le _ _ _
    _ = ENNReal.ofReal (scSideB (tzK R) / (2 * scSideA (tzK R))) := by
        rw [hup, hlow, hreal, add_zero, hgU, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        ring

/-! ### Piece F: the modulus of the Teichmüller domain -/

/-- If `Im w ∈ {0, π}` then `exp w` is real, i.e. fixed by complex conjugation. -/
theorem tzF1_conj_exp_eq {w : ℂ} (hw : w.im = 0 ∨ w.im = π) : conj (exp w) = exp w := by
  rw [Complex.conj_eq_iff_im, Complex.exp_im]
  rcases hw with h | h <;> simp [h]

/-- On the real points `(-∞,-1) ∪ (0,R)`, the exponent defining `tzG` has imaginary part `0` or `π`. -/
theorem tzF1_im_exponent {R : ℝ} (hR : 0 < R) {t : ℝ} (ht : t ∈ Iio (-1 : ℝ) ∪ Ioo 0 R) :
    (I * ((π / scSideA (tzK R) : ℝ) : ℂ) * tzW R t).im = 0 ∨
      (I * ((π / scSideA (tzK R) : ℝ) : ℂ) * tzW R t).im = π := by
  have ha : 0 < scSideA (tzK R) := (scSide_pos (tzK_pos hR) (tzK_lt_one hR)).1
  have him : (I * ((π / scSideA (tzK R) : ℝ) : ℂ) * tzW R t).im =
      (π / scSideA (tzK R)) * (tzW R t).re := by
    simp [Complex.mul_im, Complex.mul_re]
  rw [him]
  rcases ht with ht | ht
  · left; rw [((tzW_ofReal hR).1 ht).1]; ring
  · right; rw [((tzW_ofReal hR).2.2.1 ht).1]; field_simp

/-- `G` is holomorphic on `T_R` (across `(-∞,-1)` and `(0,R)` by the identity theorem). -/
theorem tzG_differentiableOn {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (tzG R) (teichmullerDomain R) := by
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  rcases lt_trichotomy z.im 0 with him | him | him
  · -- lower half: `G = conj ∘ E ∘ conj` near `z`
    have hcim : 0 < (conj z).im := by simp [him]
    have hW := tzW_differentiableAt hR hcim
    have hE : DifferentiableAt ℂ
        (fun w => exp (I * ((π / scSideA (tzK R) : ℝ) : ℂ) * tzW R w)) (conj z) :=
      (hW.const_mul _).cexp
    have hE' := hE.conj_conj
    rw [Complex.conj_conj] at hE'
    refine hE'.congr_of_eventuallyEq ?_
    filter_upwards [(Complex.continuous_im.isOpen_preimage _ isOpen_Iio).mem_nhds him] with w hw
    have hw' : ¬ 0 ≤ w.im := not_le.mpr hw
    simp only [tzG, if_neg hw', Function.comp_apply]
  · -- real axis: identity theorem
    have hzx : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
    set x := z.re with hxdef
    have hnot : ¬ ((-1 ≤ x ∧ x ≤ 0) ∨ R ≤ x) := fun h => hz ⟨him, h⟩
    have hU : x ∈ Iio (-1 : ℝ) ∪ Ioo 0 R := by
      by_cases h1 : -1 ≤ x
      · right
        exact ⟨lt_of_not_ge fun h => hnot (Or.inl ⟨h1, h⟩), lt_of_not_ge fun h => hnot (Or.inr h)⟩
      · left; exact lt_of_not_ge h1
    have hx1 : x ≠ -1 := fun h => hnot (Or.inl ⟨h.ge, by rw [h]; norm_num⟩)
    have hx0 : x ≠ 0 := fun h => hnot (Or.inl ⟨by rw [h]; norm_num, h.le⟩)
    have hxR : x ≠ R := fun h => hnot (Or.inr h.ge)
    obtain ⟨ε, hε, H, hHd, hHW⟩ := tzW_local_ext hR hx1 hx0 hxR
    have hcball : ∀ w ∈ ball (x : ℂ) ε, conj w ∈ ball (x : ℂ) ε := by
      intro w hw
      rw [mem_ball] at hw ⊢
      rwa [← Complex.conj_ofReal, Complex.dist_conj_conj]
    set E : ℂ → ℂ := fun w => exp (I * ((π / scSideA (tzK R) : ℝ) : ℂ) * H w) with hEdef
    have hEd : DifferentiableOn ℂ E (ball (x : ℂ) ε) := fun w hw =>
      ((hHd w hw).const_mul _).cexp
    have hEd' : DifferentiableOn ℂ (conj ∘ E ∘ conj) (ball (x : ℂ) ε) := by
      intro w hw
      have h1 : DifferentiableAt ℂ E (conj w) :=
        hEd.differentiableAt (isOpen_ball.mem_nhds (hcball w hw))
      have h2 := h1.conj_conj
      rw [Complex.conj_conj] at h2
      exact h2.differentiableWithinAt
    have hfreq : ∃ᶠ w in 𝓝[≠] (x : ℂ), E w = (conj ∘ E ∘ conj) w := by
      apply gzF1_frequently_real
      have hUo : IsOpen (Iio (-1 : ℝ) ∪ Ioo 0 R) := isOpen_Iio.union isOpen_Ioo
      have hball : ∀ᶠ t : ℝ in 𝓝 x, (t : ℂ) ∈ ball (x : ℂ) ε :=
        (Complex.continuous_ofReal.tendsto x).eventually (isOpen_ball.mem_nhds (mem_ball_self hε))
      filter_upwards [hUo.mem_nhds hU, hball] with t ht htb
      have hHt : H t = tzW R t := hHW t htb (by simp)
      simp only [Function.comp_apply, Complex.conj_ofReal, hEdef, hHt]
      exact (tzF1_conj_exp_eq (tzF1_im_exponent hR ht)).symm
    have hEq : EqOn E (conj ∘ E ∘ conj) (ball (x : ℂ) ε) :=
      (hEd.analyticOnNhd isOpen_ball).eqOn_of_preconnected_of_frequently_eq
        (hEd'.analyticOnNhd isOpen_ball) (convex_ball _ _).isPreconnected (mem_ball_self hε) hfreq
    rw [hzx]
    refine (hEd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hε))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hε)] with w hw
    by_cases h : 0 ≤ w.im
    · simp only [tzG, if_pos h, hEdef, hHW w hw h]
    · have hcw := hcball w hw
      have hcim : 0 ≤ (conj w).im := by simp; linarith [not_le.mp h]
      simp only [tzG, if_neg h]
      rw [← hHW _ hcw hcim]
      exact (hEq hw).symm
  · -- upper half
    have hW := tzW_differentiableAt hR him
    have hE : DifferentiableAt ℂ
        (fun w => exp (I * ((π / scSideA (tzK R) : ℝ) : ℂ) * tzW R w)) z :=
      (hW.const_mul _).cexp
    refine hE.congr_of_eventuallyEq ?_
    filter_upwards [(Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds him] with w hw
    have hw' : 0 ≤ w.im := le_of_lt hw
    simp only [tzG, if_pos hw']

/-- Real part of the exponent `i c ζ` of `tzG`. -/
theorem tzF2_arg_re (R : ℝ) (ζ : ℂ) :
    (I * ((π / scSideA (tzK R) : ℝ) : ℂ) * ζ).re = -(π / scSideA (tzK R) * ζ.im) := by
  simp [Complex.mul_re, Complex.mul_im]

/-- Imaginary part of the exponent `i c ζ` of `tzG`. -/
theorem tzF2_arg_im (R : ℝ) (ζ : ℂ) :
    (I * ((π / scSideA (tzK R) : ℝ) : ℂ) * ζ).im = π / scSideA (tzK R) * ζ.re := by
  simp [Complex.mul_re, Complex.mul_im]

/-- `exp w` lies in the target annulus when `Re w = -(π/a) v` with `v ∈ (0,b)`. -/
theorem tzF2_exp_mem_annulus {R : ℝ} (hR : 0 < R) {v : ℝ} (hv : v ∈ Ioo 0 (scSideB (tzK R)))
    {w : ℂ} (hw : w.re = -(π / scSideA (tzK R) * v)) :
    exp w ∈ annulus (Real.exp (-(π * scSideB (tzK R) / scSideA (tzK R)))) 1 := by
  obtain ⟨ha, hb⟩ := scSide_pos (tzK_pos hR) (tzK_lt_one hR)
  obtain ⟨hv0, hvb⟩ := hv
  refine ⟨?_, ?_⟩ <;> rw [Complex.norm_exp, hw]
  · apply Real.exp_lt_exp.2
    rw [neg_lt_neg_iff, div_mul_eq_mul_div, div_lt_div_iff_of_pos_right ha]
    nlinarith [Real.pi_pos]
  · apply Real.exp_lt_one_iff.2
    have : 0 < π / scSideA (tzK R) * v := mul_pos (div_pos Real.pi_pos ha) hv0
    linarith

/-- Upper half-plane: `G z` lies in the annulus with `Im G z > 0`, and the exponent has imaginary
part in `(0, π)`. -/
theorem tzF2_upper {R : ℝ} (hR : 0 < R) {z : ℂ} (him : 0 < z.im) :
    tzG R z ∈ annulus (Real.exp (-(π * scSideB (tzK R) / scSideA (tzK R)))) 1 ∧
      0 < (tzG R z).im ∧ 0 < (I * ((π / scSideA (tzK R) : ℝ) : ℂ) * tzW R z).im ∧
      (I * ((π / scSideA (tzK R) : ℝ) : ℂ) * tzW R z).im < π := by
  obtain ⟨ha, hb⟩ := scSide_pos (tzK_pos hR) (tzK_lt_one hR)
  have hW := mem_image_of_mem (tzW R) (show z ∈ upperHalf from him)
  rw [(tzW_isConformalOnto hR).2.2] at hW
  obtain ⟨h1, h2, h3, h4⟩ := hW
  have hG : tzG R z = exp (I * ((π / scSideA (tzK R) : ℝ) : ℂ) * tzW R z) := by
    unfold tzG
    rw [if_pos him.le]
  have him1 : 0 < π / scSideA (tzK R) * (tzW R z).re := mul_pos (div_pos Real.pi_pos ha) h1
  have him2 : π / scSideA (tzK R) * (tzW R z).re < π := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ ha]
    nlinarith [Real.pi_pos]
  rw [tzF2_arg_im]
  refine ⟨hG ▸ tzF2_exp_mem_annulus hR ⟨h3, h4⟩ (tzF2_arg_re R _), ?_, him1, him2⟩
  rw [hG, Complex.exp_im, tzF2_arg_im]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi him1 him2)

/-- In the lower half-plane, `G z = conj (G (conj z))`. -/
theorem tzF2_lower_eq {R : ℝ} {z : ℂ} (him : z.im < 0) : tzG R z = conj (tzG R (conj z)) := by
  have h : 0 ≤ (conj z).im := by rw [Complex.conj_im]; linarith
  unfold tzG
  rw [if_neg (not_le.2 him), if_pos h]

/-- Lower half-plane: `G z` lies in the annulus with `Im G z < 0`. -/
theorem tzF2_lower {R : ℝ} (hR : 0 < R) {z : ℂ} (him : z.im < 0) :
    tzG R z ∈ annulus (Real.exp (-(π * scSideB (tzK R) / scSideA (tzK R)))) 1 ∧
      (tzG R z).im < 0 := by
  have hc : 0 < (conj z).im := by rw [Complex.conj_im]; linarith
  obtain ⟨hA, hI, -, -⟩ := tzF2_upper hR hc
  rw [tzF2_lower_eq him]
  refine ⟨?_, ?_⟩
  · simpa [annulus, Complex.norm_conj] using hA
  · rw [Complex.conj_im]; linarith

/-- `G` on `(-∞, -1)`: a positive real `e^{-(π/a) v}`, `v = Im W x ∈ (0,b)`. -/
theorem tzF2_real_left {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : x < -1) :
    tzG R x = ((Real.exp (-(π / scSideA (tzK R) * (tzW R x).im)) : ℝ) : ℂ) ∧
      (tzW R x).im ∈ Ioo 0 (scSideB (tzK R)) := by
  obtain ⟨hre, him⟩ := (tzW_ofReal hR (x := x)).1 hx
  refine ⟨?_, him⟩
  set v := (tzW R x).im with hv
  have hW : tzW R x = (v : ℂ) * I := Complex.ext (by simp [hre]) (by simp [hv])
  unfold tzG
  rw [if_pos (by simp), hW, Complex.ofReal_exp]
  congr 1
  push_cast
  linear_combination ((π : ℂ) / (scSideA (tzK R) : ℂ) * (v : ℂ)) * Complex.I_sq

/-- `G` on `(0, R)`: a negative real `-e^{-(π/a) v}`, `v = Im W x ∈ (0,b)`. -/
theorem tzF2_real_right {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : x ∈ Ioo 0 R) :
    tzG R x = ((-Real.exp (-(π / scSideA (tzK R) * (tzW R x).im)) : ℝ) : ℂ) ∧
      (tzW R x).im ∈ Ioo 0 (scSideB (tzK R)) := by
  obtain ⟨ha, hb⟩ := scSide_pos (tzK_pos hR) (tzK_lt_one hR)
  obtain ⟨hre, him⟩ := (tzW_ofReal hR (x := x)).2.2.1 hx
  refine ⟨?_, him⟩
  set v := (tzW R x).im with hv
  have hW : tzW R x = (scSideA (tzK R) : ℂ) + (v : ℂ) * I :=
    Complex.ext (by simp [hre]) (by simp [hv])
  have ha' : (scSideA (tzK R) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hca : (π : ℂ) / (scSideA (tzK R) : ℂ) * (scSideA (tzK R) : ℂ) = π := div_mul_cancel₀ _ ha'
  have hexp : I * ((π / scSideA (tzK R) : ℝ) : ℂ) * ((scSideA (tzK R) : ℂ) + (v : ℂ) * I)
      = ((-(π / scSideA (tzK R) * v) : ℝ) : ℂ) + (π : ℂ) * I := by
    push_cast
    linear_combination ((π : ℂ) / (scSideA (tzK R) : ℂ) * (v : ℂ)) * Complex.I_sq + I * hca
  unfold tzG
  rw [if_pos (by simp), hW, hexp, Complex.exp_add, Complex.exp_pi_mul_I]
  push_cast
  ring

/-- Real points of the Teichmüller domain lie on `(-∞,-1) ∪ (0,R)`. -/
theorem tzF2_real_cases {R : ℝ} {z : ℂ} (hz : z ∈ teichmullerDomain R) (him : z.im = 0) :
    z = (z.re : ℂ) ∧ (z.re < -1 ∨ z.re ∈ Ioo 0 R) := by
  refine ⟨Complex.ext (by simp) (by simp [him]), ?_⟩
  have h := fun h' => hz ⟨him, h'⟩
  rcases lt_or_ge z.re (-1) with h1 | h1
  · exact Or.inl h1
  · right
    refine ⟨?_, ?_⟩
    · by_contra h2
      exact h (Or.inl ⟨h1, not_lt.1 h2⟩)
    · by_contra h2
      exact h (Or.inr (not_lt.1 h2))

/-- Real points of `(-∞,-1) ∪ (0,R)` lie in the Teichmüller domain. -/
theorem tzF2_real_mem {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : x < -1 ∨ x ∈ Ioo 0 R) :
    (x : ℂ) ∈ teichmullerDomain R := by
  rintro ⟨-, h⟩
  simp only [Complex.ofReal_re] at h
  rcases hx with hx | hx <;> rcases h with h | h
  · linarith [h.1]
  · linarith
  · linarith [hx.1, h.2]
  · linarith [hx.2]

/-- Non-real points lie in the Teichmüller domain. -/
theorem tzF2_nonreal_mem {R : ℝ} {z : ℂ} (him : z.im ≠ 0) : z ∈ teichmullerDomain R :=
  fun h => him h.1

/-- The denominator of `Q` at a real point off the pole is non-zero. -/
theorem tzF2_den_ne {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : x ≠ tzPole R) :
    (tzK R : ℂ) * x + tzQc R ≠ 0 := by
  have hk₀ := tzK_pos hR
  have hk₁ := tzK_lt_one hR
  have h1k : 1 - tzK R ≠ 0 := by linarith
  have e : tzK R * x + tzQc R = tzK R * (x - tzPole R) := by
    unfold tzQc tzPole
    field_simp
    ring
  have : tzK R * x + tzQc R ≠ 0 := by
    rw [e]
    exact mul_ne_zero hk₀.ne' (sub_ne_zero.2 hx)
  exact_mod_cast this

/-- `W` is injective on the real axis. -/
theorem tzF2_W_real_inj {R : ℝ} (hR : 0 < R) {x₁ x₂ : ℝ} (h : tzW R x₁ = tzW R x₂) : x₁ = x₂ := by
  have hk₀ := tzK_pos hR
  have hk₁ := tzK_lt_one hR
  by_cases p₁ : x₁ = tzPole R <;> by_cases p₂ : x₂ = tzPole R
  · rw [p₁, p₂]
  · exfalso
    obtain ⟨y₂, hy₂, -⟩ := tzQ_ofReal hR p₂
    unfold tzW at h
    rw [if_pos (by rw [p₁]), if_neg (by exact_mod_cast p₂), hy₂] at h
    exact scMap_ofReal_ne_infty hk₀ hk₁ y₂ h.symm
  · exfalso
    obtain ⟨y₁, hy₁, -⟩ := tzQ_ofReal hR p₁
    unfold tzW at h
    rw [if_neg (by exact_mod_cast p₁), if_pos (by rw [p₂]), hy₁] at h
    exact scMap_ofReal_ne_infty hk₀ hk₁ y₁ h
  · obtain ⟨y₁, hy₁, -⟩ := tzQ_ofReal hR p₁
    obtain ⟨y₂, hy₂, -⟩ := tzQ_ofReal hR p₂
    unfold tzW at h
    rw [if_neg (by exact_mod_cast p₁), if_neg (by exact_mod_cast p₂), hy₁, hy₂] at h
    have hy : y₁ = y₂ := scMap_ofReal_injective hk₀ hk₁ h
    have hQ : tzQ R x₁ = tzQ R x₂ := by rw [hy₁, hy₂, hy]
    unfold tzQ at hQ
    rw [div_eq_div_iff (tzF2_den_ne hR p₁) (tzF2_den_ne hR p₂)] at hQ
    have hq : 0 < tzQc R := by
      unfold tzQc
      exact div_pos (by linarith) (by linarith)
    have key : (((x₁ - x₂) * (tzQc R * (1 + tzK R)) : ℝ) : ℂ) = 0 := by
      push_cast
      linear_combination hQ
    have key' : (x₁ - x₂) * (tzQc R * (1 + tzK R)) = 0 := by exact_mod_cast key
    have hne : tzQc R * (1 + tzK R) ≠ 0 := mul_ne_zero hq.ne' (by linarith)
    exact sub_eq_zero.1 ((mul_eq_zero.1 key').resolve_right hne)

/-- `G` is injective on the upper half-plane. -/
theorem tzF2_upper_inj {R : ℝ} (hR : 0 < R) {z₁ z₂ : ℂ} (h₁ : 0 < z₁.im) (h₂ : 0 < z₂.im)
    (h : tzG R z₁ = tzG R z₂) : z₁ = z₂ := by
  obtain ⟨ha, hb⟩ := scSide_pos (tzK_pos hR) (tzK_lt_one hR)
  obtain ⟨-, -, a₁, b₁⟩ := tzF2_upper hR h₁
  obtain ⟨-, -, a₂, b₂⟩ := tzF2_upper hR h₂
  unfold tzG at h
  rw [if_pos h₁.le, if_pos h₂.le] at h
  have hl := congrArg Complex.log h
  rw [Complex.log_exp (by linarith [Real.pi_pos]) b₁.le,
    Complex.log_exp (by linarith [Real.pi_pos]) b₂.le] at hl
  have hc : I * ((π / scSideA (tzK R) : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero I_ne_zero (by exact_mod_cast (div_pos Real.pi_pos ha).ne')
  exact (tzW_isConformalOnto hR).2.1 h₁ h₂ (mul_left_cancel₀ hc hl)

/-- `G` is injective on the real points `(-∞,-1) ∪ (0,R)`. -/
theorem tzF2_real_inj {R : ℝ} (hR : 0 < R) {x₁ x₂ : ℝ}
    (h₁ : x₁ < -1 ∨ x₁ ∈ Ioo 0 R) (h₂ : x₂ < -1 ∨ x₂ ∈ Ioo 0 R)
    (h : tzG R x₁ = tzG R x₂) : x₁ = x₂ := by
  apply tzF2_W_real_inj hR
  have ha := (scSide_pos (tzK_pos hR) (tzK_lt_one hR)).1
  have hc : π / scSideA (tzK R) ≠ 0 := (div_pos Real.pi_pos ha).ne'
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · obtain ⟨e₁, -⟩ := tzF2_real_left hR h₁
    obtain ⟨e₂, -⟩ := tzF2_real_left hR h₂
    obtain ⟨i₁, -⟩ := (tzW_ofReal hR (x := x₁)).1 h₁
    obtain ⟨i₂, -⟩ := (tzW_ofReal hR (x := x₂)).1 h₂
    rw [e₁, e₂, Complex.ofReal_inj, Real.exp_eq_exp, neg_inj] at h
    exact Complex.ext (by rw [i₁, i₂]) (mul_left_cancel₀ hc h)
  · obtain ⟨e₁, -⟩ := tzF2_real_left hR h₁
    obtain ⟨e₂, -⟩ := tzF2_real_right hR h₂
    rw [e₁, e₂, Complex.ofReal_inj] at h
    linarith [Real.exp_pos (-(π / scSideA (tzK R) * (tzW R x₁).im)),
      Real.exp_pos (-(π / scSideA (tzK R) * (tzW R x₂).im))]
  · obtain ⟨e₁, -⟩ := tzF2_real_right hR h₁
    obtain ⟨e₂, -⟩ := tzF2_real_left hR h₂
    rw [e₁, e₂, Complex.ofReal_inj] at h
    linarith [Real.exp_pos (-(π / scSideA (tzK R) * (tzW R x₁).im)),
      Real.exp_pos (-(π / scSideA (tzK R) * (tzW R x₂).im))]
  · obtain ⟨e₁, -⟩ := tzF2_real_right hR h₁
    obtain ⟨e₂, -⟩ := tzF2_real_right hR h₂
    obtain ⟨i₁, -⟩ := (tzW_ofReal hR (x := x₁)).2.2.1 h₁
    obtain ⟨i₂, -⟩ := (tzW_ofReal hR (x := x₂)).2.2.1 h₂
    rw [e₁, e₂, Complex.ofReal_inj, neg_inj, Real.exp_eq_exp, neg_inj] at h
    exact Complex.ext (by rw [i₁, i₂]) (mul_left_cancel₀ hc h)

/-- Location of `G z` according to the sign of `Im z`, for `z` in the Teichmüller domain. -/
theorem tzF2_sign {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ teichmullerDomain R) :
    (0 < z.im → 0 < (tzG R z).im) ∧ (z.im < 0 → (tzG R z).im < 0) ∧
      (z.im = 0 → (tzG R z).im = 0) := by
  refine ⟨fun h => (tzF2_upper hR h).2.1, fun h => (tzF2_lower hR h).2, fun h => ?_⟩
  obtain ⟨hz', hc⟩ := tzF2_real_cases hz h
  rw [hz']
  rcases hc with hc | hc
  · rw [(tzF2_real_left hR hc).1, Complex.ofReal_im]
  · rw [(tzF2_real_right hR hc).1, Complex.ofReal_im]

theorem tzG_injOn {R : ℝ} (hR : 0 < R) : InjOn (tzG R) (teichmullerDomain R) := by
  intro z₁ h₁ z₂ h₂ h
  obtain ⟨p₁, n₁, e₁⟩ := tzF2_sign hR h₁
  obtain ⟨p₂, n₂, e₂⟩ := tzF2_sign hR h₂
  rcases lt_trichotomy z₁.im 0 with c₁ | c₁ | c₁ <;>
    rcases lt_trichotomy z₂.im 0 with c₂ | c₂ | c₂
  · have hc₁ : 0 < (conj z₁).im := by rw [Complex.conj_im]; linarith
    have hc₂ : 0 < (conj z₂).im := by rw [Complex.conj_im]; linarith
    rw [tzF2_lower_eq c₁, tzF2_lower_eq c₂] at h
    have := tzF2_upper_inj hR hc₁ hc₂ (star_injective h)
    simpa using congrArg conj this
  · have := n₁ c₁; rw [h, e₂ c₂] at this; exact absurd this (lt_irrefl 0)
  · have := n₁ c₁; rw [h] at this; linarith [p₂ c₂]
  · have := e₁ c₁; rw [h] at this; linarith [n₂ c₂]
  · obtain ⟨hz₁, hx₁⟩ := tzF2_real_cases h₁ c₁
    obtain ⟨hz₂, hx₂⟩ := tzF2_real_cases h₂ c₂
    rw [hz₁, hz₂] at h
    rw [hz₁, hz₂, tzF2_real_inj hR hx₁ hx₂ h]
  · have := e₁ c₁; rw [h] at this; linarith [p₂ c₂]
  · have := p₁ c₁; rw [h] at this; linarith [n₂ c₂]
  · have := p₁ c₁; rw [h, e₂ c₂] at this; exact absurd this (lt_irrefl 0)
  · exact tzF2_upper_inj hR c₁ c₂ h

/-- `G` maps the Teichmüller domain into the annulus. -/
theorem tzF2_mapsTo {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ teichmullerDomain R) :
    tzG R z ∈ annulus (Real.exp (-(π * scSideB (tzK R) / scSideA (tzK R)))) 1 := by
  rcases lt_trichotomy z.im 0 with h | h | h
  · exact (tzF2_lower hR h).1
  · obtain ⟨hz', hc⟩ := tzF2_real_cases hz h
    rw [hz']
    rcases hc with hc | hc
    · obtain ⟨e, hv⟩ := tzF2_real_left hR hc
      rw [e, Complex.ofReal_exp]
      exact tzF2_exp_mem_annulus hR hv (by rw [Complex.ofReal_re])
    · obtain ⟨e, hv⟩ := tzF2_real_right hR hc
      rw [e, Complex.ofReal_neg, Complex.ofReal_exp]
      have := tzF2_exp_mem_annulus hR hv
        (w := ((-(π / scSideA (tzK R) * (tzW R z.re).im) : ℝ) : ℂ)) (by rw [Complex.ofReal_re])
      simpa [annulus, norm_neg] using this
  · exact (tzF2_upper hR h).1

/-- Every point of the annulus with positive imaginary part is `G z` for some `z ∈ ℍ`. -/
theorem tzF2_surj_upper {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw : w ∈ annulus (Real.exp (-(π * scSideB (tzK R) / scSideA (tzK R)))) 1) (him : 0 < w.im) :
    ∃ z : ℂ, 0 < z.im ∧ tzG R z = w := by
  obtain ⟨ha, hb⟩ := scSide_pos (tzK_pos hR) (tzK_lt_one hR)
  obtain ⟨hw1, hw2⟩ := hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at him
  have hc : 0 < π / scSideA (tzK R) := div_pos Real.pi_pos ha
  have hc' : ((π / scSideA (tzK R) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hnpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hL1 : Real.log ‖w‖ < 0 := Real.log_neg hnpos hw2
  have hL2 : -(π * scSideB (tzK R) / scSideA (tzK R)) < Real.log ‖w‖ :=
    (Real.lt_log_iff_exp_lt hnpos).2 hw1
  have hA1 : 0 < w.arg := lt_of_le_of_ne (Complex.arg_nonneg_iff.2 him.le)
    (fun h => him.ne' (Complex.arg_eq_zero_iff.1 h.symm).2)
  have hA2 : w.arg < π := Complex.arg_lt_pi_iff.2 (Or.inr him.ne')
  set ζ : ℂ := -I * Complex.log w / ((π / scSideA (tzK R) : ℝ) : ℂ) with hζ
  have hζre : ζ.re = w.arg / (π / scSideA (tzK R)) := by
    rw [hζ, Complex.div_ofReal_re]
    simp [Complex.mul_re, Complex.log_im]
  have hζim : ζ.im = -(Real.log ‖w‖ / (π / scSideA (tzK R))) := by
    rw [hζ, Complex.div_ofReal_im]
    simp [Complex.mul_im, Complex.log_re]
    ring
  have hmem : ζ ∈ rectangle (scSideA (tzK R)) (scSideB (tzK R)) := by
    have e : π * scSideB (tzK R) / scSideA (tzK R) = scSideB (tzK R) * (π / scSideA (tzK R)) := by
      ring
    have e' : π = scSideA (tzK R) * (π / scSideA (tzK R)) := by field_simp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hζre]; exact div_pos hA1 hc
    · rw [hζre, div_lt_iff₀ hc]; linarith [e']
    · rw [hζim, neg_pos]; exact div_neg_of_neg_of_pos hL1 hc
    · rw [hζim, neg_lt, lt_div_iff₀ hc]; linarith [e]
  rw [← (tzW_isConformalOnto hR).2.2] at hmem
  obtain ⟨z, hzH, hWz⟩ := hmem
  refine ⟨z, hzH, ?_⟩
  unfold tzG
  rw [if_pos (le_of_lt hzH), hWz, hζ]
  have : I * ((π / scSideA (tzK R) : ℝ) : ℂ) *
      (-I * Complex.log w / ((π / scSideA (tzK R) : ℝ) : ℂ)) = Complex.log w := by
    calc I * ((π / scSideA (tzK R) : ℝ) : ℂ) *
          (-I * Complex.log w / ((π / scSideA (tzK R) : ℝ) : ℂ))
        = -(I * I) * Complex.log w *
          (((π / scSideA (tzK R) : ℝ) : ℂ) / ((π / scSideA (tzK R) : ℝ) : ℂ)) := by ring
      _ = Complex.log w := by rw [div_self hc', Complex.I_mul_I]; ring
  rw [this, Complex.exp_log hw0]

/-- A real point of the annulus is `G x` for a real `x ∈ (-∞,-1) ∪ (0,R)`. -/
theorem tzF2_surj_real {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw : w ∈ annulus (Real.exp (-(π * scSideB (tzK R) / scSideA (tzK R)))) 1) (him : w.im = 0) :
    ∃ x : ℝ, (x < -1 ∨ x ∈ Ioo 0 R) ∧ tzG R x = w := by
  obtain ⟨ha, hb⟩ := scSide_pos (tzK_pos hR) (tzK_lt_one hR)
  obtain ⟨hw1, hw2⟩ := hw
  have hwr : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hn : ‖w‖ = |w.re| := by
    conv_lhs => rw [hwr]
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hn] at hw1 hw2
  have hc : 0 < π / scSideA (tzK R) := div_pos Real.pi_pos ha
  have habs : 0 < |w.re| := lt_trans (Real.exp_pos _) hw1
  have hL1 : Real.log |w.re| < 0 := Real.log_neg habs hw2
  have hL2 : -(π * scSideB (tzK R) / scSideA (tzK R)) < Real.log |w.re| :=
    (Real.lt_log_iff_exp_lt habs).2 hw1
  set t := -(Real.log |w.re| / (π / scSideA (tzK R))) with ht
  have htm : t ∈ Ioo 0 (scSideB (tzK R)) := by
    have e : π * scSideB (tzK R) / scSideA (tzK R) = scSideB (tzK R) * (π / scSideA (tzK R)) := by
      ring
    refine ⟨?_, ?_⟩
    · rw [ht, neg_pos]; exact div_neg_of_neg_of_pos hL1 hc
    · rw [ht, neg_lt, lt_div_iff₀ hc]; linarith [e]
  have hexp : Real.exp (-(π / scSideA (tzK R) * t)) = |w.re| := by
    have : -(π / scSideA (tzK R) * t) = Real.log |w.re| := by
      rw [ht]
      field_simp
    rw [this, Real.exp_log habs]
  obtain ⟨⟨x₁, hx₁, hW₁⟩, ⟨x₂, hx₂, hW₂⟩⟩ := tzW_ofReal_surj hR htm
  rcases lt_or_ge 0 w.re with hpos | hneg
  · refine ⟨x₁, Or.inl hx₁, ?_⟩
    have him' : (tzW R x₁).im = t := by rw [hW₁]; simp
    rw [(tzF2_real_left hR hx₁).1, him', hexp, abs_of_pos hpos, ← hwr]
  · have hneg' : w.re < 0 := by
      rcases hneg.lt_or_eq with h | h
      · exact h
      · rw [h, abs_zero] at habs; exact absurd habs (lt_irrefl 0)
    refine ⟨x₂, Or.inr hx₂, ?_⟩
    have him' : (tzW R x₂).im = t := by rw [hW₂]; simp
    rw [(tzF2_real_right hR hx₂).1, him', hexp, abs_of_neg hneg', neg_neg, ← hwr]

theorem tzG_image {R : ℝ} (hR : 0 < R) :
    tzG R '' teichmullerDomain R =
      annulus (Real.exp (-(π * scSideB (tzK R) / scSideA (tzK R)))) 1 := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact tzF2_mapsTo hR hz
  · intro hw
    rcases lt_trichotomy w.im 0 with h | h | h
    · have hw' : conj w ∈ annulus (Real.exp (-(π * scSideB (tzK R) / scSideA (tzK R)))) 1 := by
        simpa [annulus, Complex.norm_conj] using hw
      have h' : 0 < (conj w).im := by rw [Complex.conj_im]; linarith
      obtain ⟨z, hzH, hGz⟩ := tzF2_surj_upper hR hw' h'
      have hc : (conj z).im < 0 := by rw [Complex.conj_im]; linarith
      refine ⟨conj z, tzF2_nonreal_mem hc.ne, ?_⟩
      rw [tzF2_lower_eq hc, Complex.conj_conj, hGz, Complex.conj_conj]
    · obtain ⟨x, hx, hGx⟩ := tzF2_surj_real hR hw h
      exact ⟨x, tzF2_real_mem hR hx, hGx⟩
    · obtain ⟨z, hzH, hGz⟩ := tzF2_surj_upper hR hw h
      exact ⟨z, tzF2_nonreal_mem hzH.ne', hGz⟩

theorem tzG_isConformalOnto {R : ℝ} (hR : 0 < R) :
    IsConformalOnto (tzG R) (teichmullerDomain R)
      (annulus (Real.exp (-(π * scSideB (tzK R) / scSideA (tzK R)))) 1) :=
  ⟨tzG_differentiableOn hR, tzG_injOn hR, tzG_image hR⟩

theorem tz_isOpen_teichmullerDomain (R : ℝ) : IsOpen (teichmullerDomain R) := by
  have hC : IsClosed {z : ℂ | z.im = 0 ∧ ((-1 ≤ z.re ∧ z.re ≤ 0) ∨ R ≤ z.re)} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const)).union
        (isClosed_le continuous_const Complex.continuous_re))
  exact hC.isOpen_compl

theorem tz_dcModulus_teichmullerDomain {R : ℝ} (hR : 0 < R) :
    dcModulus (teichmullerDomain R) = ENNReal.ofReal (π * scSideB (tzK R) / scSideA (tzK R)) := by
  have hk₀ := tzK_pos hR
  have hk₁ := tzK_lt_one hR
  have ha := (scSide_pos hk₀ hk₁).1
  have hb := (scSide_pos hk₀ hk₁).2
  have hpos : 0 < π * scSideB (tzK R) / scSideA (tzK R) := by positivity
  rw [dcModulus_eq_of_equiv (tz_isOpen_teichmullerDomain R) (Real.exp_pos _)
    (Real.exp_lt_one_iff.2 (neg_lt_zero.2 hpos)) ⟨_, tzG_isConformalOnto hR⟩, div_eq_mul_inv, one_mul,
    ← Real.exp_neg, neg_neg, Real.log_exp]

/-! ### The target -/

-- (the target follows)

/-- **Theorem 5.2** (Teichmüller).  A doubly connected domain separating `{-1, 0}` from `{R, ∞}`
has modulus at most `M(T_R)`.

Proved (2026-09-23) by the explicit symmetric-metric method of Theorem 5.1, without Koebe's theorems:
with `k = (√(1+R)-1)/(√(1+R)+1)` the real Möbius map `tzQ` sends `-1, 0, R, ∞` to `-1/k, -1, 1, 1/k`, and
`W = scMap k ∘ tzQ` maps `ℍ` onto a rectangle `(0,a) × (0,b)` with `(-∞,-1)` and `(0,R)` on the vertical sides;
`W` continues holomorphically across the real axis off `{-1, 0, R}` (at the pole of `tzQ` through the inversion
symmetry of `scMap`), so every separating curve of `B` has `ρ`-length `≥ 1` for `ρ = |W'|/(2a)` (folded
symmetrically); its area is `b/(2a)`, and `M(T_R) = πb/a` via the glued map `tzG` onto an annulus. -/
theorem thm5_2_teichmuller {R : ℝ} (hR : 0 < R) {B : Set ℂ} (hB : IsDoublyConnected B)
    (hsep : SeparatesSets B {((-1 : ℂ) : ExtPlane), ((0 : ℂ) : ExtPlane)}
      {((R : ℂ) : ExtPlane), extInf}) :
    dcModulus B ≤ dcModulus (teichmullerDomain R) := by
  have hk₀ := tzK_pos hR
  have hk₁ := tzK_lt_one hR
  have ha := (scSide_pos hk₀ hk₁).1
  have hb := (scSide_pos hk₀ hk₁).2
  have hadm : ∀ γ ∈ separatingCurves B, 1 ≤ γ.rhoLength (tzRho R) :=
    fun γ hγ => tz_one_le_rhoLength hR hsep hγ
  calc dcModulus B ≤ ENNReal.ofReal (2 * π) * rhoArea (tzRho R) B :=
        dcModulus_le_rhoArea hB (tz_measurable_rho R) hadm
    _ ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal (scSideB (tzK R) / (2 * scSideA (tzK R))) := by
        gcongr
        exact tz_rhoArea_le hR B
    _ = ENNReal.ofReal (π * scSideB (tzK R) / scSideA (tzK R)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ = dcModulus (teichmullerDomain R) := (tz_dcModulus_teichmullerDomain hR).symm

/-! ### The modulus of the Teichmüller domain — helpers -/

/-- `ψ(ζ) = -4Rζ/(1-ζ)²`. -/
def tmPsi (R : ℝ) (ζ : ℂ) : ℂ := -4 * (R : ℂ) * ζ / (1 - ζ) ^ 2

/-- `r₀ = 1 + 2R - √(4R + 4R²)`. -/
def tmR0 (R : ℝ) : ℝ := 1 + 2 * R - Real.sqrt (4 * R + 4 * R ^ 2)

theorem tmR0_pos {R : ℝ} (hR : 0 < R) : 0 < tmR0 R := by
  unfold tmR0
  have h : Real.sqrt (4 * R + 4 * R ^ 2) < 1 + 2 * R := by
    rw [Real.sqrt_lt' (by linarith)]; nlinarith
  linarith

theorem tmR0_lt_one {R : ℝ} (hR : 0 < R) : tmR0 R < 1 := by
  unfold tmR0
  have h : 2 * R < Real.sqrt (4 * R + 4 * R ^ 2) := by
    rw [Real.lt_sqrt (by linarith)]; nlinarith
  linarith

/-- On `Δ`, `1 - ζ ≠ 0`. -/
theorem tmA_one_sub_ne {ζ : ℂ} (hζ : ζ ∈ unitDisc) : 1 - ζ ≠ 0 := by
  intro h
  have h1 : ζ = 1 := by linear_combination -h
  rw [h1, gzA_mem_unitDisc_iff] at hζ
  norm_num at hζ

/-- `ψ` is holomorphic and injective on `Δ`. -/
theorem tmPsi_differentiableOn (R : ℝ) : DifferentiableOn ℂ (tmPsi R) unitDisc := by
  intro ζ hζ
  apply DifferentiableAt.differentiableWithinAt
  have hf : tmPsi R = fun ζ : ℂ => -4 * (R : ℂ) * ζ / (1 - ζ) ^ 2 := rfl
  rw [hf]
  exact ((differentiableAt_const _).mul differentiableAt_id).div
    (((differentiableAt_const _).sub differentiableAt_id).pow 2) (pow_ne_zero 2 (tmA_one_sub_ne hζ))

theorem tmPsi_injOn {R : ℝ} (hR : 0 < R) : InjOn (tmPsi R) unitDisc := by
  intro z hz w hw h
  have hz1 := tmA_one_sub_ne hz
  have hw1 := tmA_one_sub_ne hw
  have hR' : (-4 * (R : ℂ)) ≠ 0 := by
    have : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
    exact mul_ne_zero (by norm_num) this
  simp only [tmPsi] at h
  rw [div_eq_div_iff (pow_ne_zero 2 hz1) (pow_ne_zero 2 hw1)] at h
  have h2 : (z - w) * (1 - z * w) = 0 := by
    have h3 : (-4 * (R : ℂ)) * ((z - w) * (1 - z * w)) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h3).resolve_left hR'
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linear_combination h3
  · exfalso
    have hz' : ‖z‖ < 1 := by simpa [unitDisc] using hz
    have hw' : ‖w‖ < 1 := by simpa [unitDisc] using hw
    have hlt : ‖z * w‖ < 1 := by
      rw [norm_mul]; nlinarith [norm_nonneg z, norm_nonneg w]
    have h4 : z * w = 1 := by linear_combination -h3
    rw [h4] at hlt; simp at hlt

/-- `ψ` at a real point. -/
theorem tmA_psi_ofReal (R a : ℝ) : tmPsi R (a : ℂ) = ((-4 * R * a / (1 - a) ^ 2 : ℝ) : ℂ) := by
  simp only [tmPsi]; push_cast; ring

/-- For `a < 1`: `-1 ≤ ψ(a) ≤ 0 ↔ 0 ≤ a ≤ r₀`. -/
theorem tmA_real_iff {R a : ℝ} (hR : 0 < R) (ha1 : a < 1) :
    (-1 ≤ -4 * R * a / (1 - a) ^ 2 ∧ -4 * R * a / (1 - a) ^ 2 ≤ 0) ↔ (0 ≤ a ∧ a ≤ tmR0 R) := by
  have hpos : 0 < (1 - a) ^ 2 := by
    have : 0 < 1 - a := by linarith
    positivity
  have hs2 : Real.sqrt (4 * R + 4 * R ^ 2) ^ 2 = 4 * R + 4 * R ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt (4 * R + 4 * R ^ 2) := Real.sqrt_nonneg _
  have key : (1 - a) ^ 2 - 4 * R * a
      = (a - tmR0 R) * (a - (1 + 2 * R + Real.sqrt (4 * R + 4 * R ^ 2))) := by
    unfold tmR0; linear_combination hs2
  rw [le_div_iff₀ hpos, div_le_iff₀ hpos]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by nlinarith, ?_⟩
    by_contra hc
    have hc' : 0 < a - tmR0 R := by linarith
    have : (a - tmR0 R) * (a - (1 + 2 * R + Real.sqrt (4 * R + 4 * R ^ 2))) < 0 :=
      mul_neg_of_pos_of_neg hc' (by linarith)
    linarith
  · rintro ⟨h1, h2⟩
    have : 0 ≤ (a - tmR0 R) * (a - (1 + 2 * R + Real.sqrt (4 * R + 4 * R ^ 2))) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    constructor <;> nlinarith

/-- For `-1 < a < 1`: `ψ(a) < R`. -/
theorem tmA_not_ge {R a : ℝ} (hR : 0 < R) (ha0 : -1 < a) (ha1 : a < 1) :
    ¬ R ≤ -4 * R * a / (1 - a) ^ 2 := by
  have hpos : 0 < (1 - a) ^ 2 := by
    have : 0 < 1 - a := by linarith
    positivity
  rw [le_div_iff₀ hpos]
  intro h
  have : 0 < R * (1 + a) ^ 2 := by
    have : 0 < 1 + a := by linarith
    positivity
  nlinarith

/-- The equation `ψ(ζ) = w`, cleared of denominators. -/
theorem tmA_eq_iff {R : ℝ} {ζ w : ℂ} (h : 1 - ζ ≠ 0) :
    tmPsi R ζ = w ↔ w * (1 - ζ) ^ 2 = -4 * R * ζ := by
  rw [tmPsi, div_eq_iff (pow_ne_zero 2 h)]
  constructor <;> intro h' <;> linear_combination -h'

/-- If `ζ ∈ Δ` and `ψ(ζ)` is real, then `ζ` is real. -/
theorem tmA_im_eq_zero {R : ℝ} (hR : 0 < R) {ζ : ℂ} (hζ : ζ ∈ unitDisc)
    (h : (tmPsi R ζ).im = 0) : ζ.im = 0 := by
  have hn : ζ.re * ζ.re + ζ.im * ζ.im < 1 := gzA_mem_unitDisc_iff.mp hζ
  have heq : tmPsi R ζ * (1 - ζ) ^ 2 = -4 * R * ζ := (tmA_eq_iff (tmA_one_sub_ne hζ)).mp rfl
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  simp [pow_two, h] at hre him
  set u := (tmPsi R ζ).re
  set a := ζ.re
  set b := ζ.im
  by_contra hb
  have E1 : u * (1 - a) = 2 * R := by
    have h3 : b * (u * (1 - a) - 2 * R) = 0 := by linear_combination (-1/2 : ℝ) * him
    have := (mul_eq_zero.mp h3).resolve_left hb
    linear_combination this
  have h4 : 2 * R * (1 - a ^ 2 - b ^ 2) = 0 := by
    linear_combination (1 - a) * hre - ((1 - a) ^ 2 - b ^ 2) * E1
  have h5 : 1 - a ^ 2 - b ^ 2 = 0 := by
    rcases mul_eq_zero.mp h4 with h6 | h6
    · linarith
    · exact h6
  nlinarith

/-- `ψ(Δ) ⊇ ℂ ∖ [R, ∞)`. -/
theorem tmA_exists {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : ¬ (w.im = 0 ∧ R ≤ w.re)) :
    ∃ ζ ∈ unitDisc, tmPsi R ζ = w := by
  by_cases hw0 : w = 0
  · refine ⟨0, gzA_mem_unitDisc_iff.mpr (by simp), by simp [tmPsi, hw0]⟩
  set c : ℂ := 1 - 2 * R / w with hc
  have hcw : w * (1 - c) = 2 * R := by rw [hc]; field_simp; ring
  clear_value c
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (c ^ 2 - 1)
  have h0 : (c + s) ^ 2 - 2 * c * (c + s) + 1 = 0 := by linear_combination -hs
  have hne : c + s ≠ 0 := by
    intro h; rw [h] at h0; norm_num at h0
  have hroot : ∀ z : ℂ, z ^ 2 - 2 * c * z + 1 = 0 → tmPsi R z = w := by
    intro z hz
    have hz1 : 1 - z ≠ 0 := by
      intro h1
      have hz' : z = 1 := by linear_combination -h1
      rw [hz'] at hz
      have : (2 * R : ℂ) = 0 := by rw [← hcw]; linear_combination (w / 2) * hz
      have hR0 : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
      exact hR0 (by linear_combination this / 2)
    rw [tmA_eq_iff hz1]
    linear_combination w * hz - 2 * z * hcw
  rcases lt_trichotomy (Complex.normSq (c + s)) 1 with hlt | heq | hgt
  · exact ⟨c + s, gzA_mem_unitDisc_iff.mpr (by rwa [← Complex.normSq_apply]), hroot _ h0⟩
  · exfalso
    have hi := gzA_root_im h0
    rw [← Complex.normSq_apply, heq] at hi
    have hci : c.im = 0 := by linarith
    have hn : (c + s).re * (c + s).re + (c + s).im * (c + s).im = 1 := by
      rw [← Complex.normSq_apply, heq]
    generalize c + s = z at h0 hn
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp [pow_two, hci] at hre him
    set a := z.re with ha
    set b := z.im with hb
    have hcr : c.re = a := by
      have h7 : (a - c.re) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a * (a - c.re)), sq_nonneg (b * (a - c.re))]
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h7
      linarith
    have ha1 : a ≤ 1 := by nlinarith
    have ha0 : -1 ≤ a := by nlinarith
    have hwre := congrArg Complex.re hcw
    have hwim := congrArg Complex.im hcw
    simp [hci, hcr] at hwre hwim
    apply hw
    have hne1 : 1 - a ≠ 0 := by
      intro h8
      rw [h8] at hwre
      linarith
    have hwi : w.im = 0 := by
      rcases hwim with h9 | h9
      · exact h9
      · exact absurd h9 hne1
    refine ⟨hwi, ?_⟩
    have hpos : 0 < 1 - a := lt_of_le_of_ne (by linarith) (Ne.symm hne1)
    nlinarith
  · refine ⟨(c + s)⁻¹, gzA_mem_unitDisc_iff.mpr ?_, hroot _ ?_⟩
    · rw [← Complex.normSq_apply, Complex.normSq_inv]
      exact inv_lt_one_of_one_lt₀ hgt
    · field_simp
      linear_combination h0

/-- `ψ(B_{r₀}) = T_R`. -/
theorem tmPsi_image {R : ℝ} (hR : 0 < R) :
    tmPsi R '' grotzschDomain (tmR0 R) = teichmullerDomain R := by
  ext w
  constructor
  · rintro ⟨ζ, ⟨hζ, hζB⟩, rfl⟩
    rintro ⟨him, hcase⟩
    have hb := tmA_im_eq_zero hR hζ him
    have hn := gzA_mem_unitDisc_iff.mp hζ
    rw [hb] at hn
    have ha1 : ζ.re < 1 := by nlinarith
    have ha0 : -1 < ζ.re := by nlinarith
    have hζr : ζ = (ζ.re : ℂ) := Complex.ext (by simp) (by simp [hb])
    rw [hζr, tmA_psi_ofReal, Complex.ofReal_re] at hcase
    rcases hcase with h | h
    · exact hζB ⟨hb, (tmA_real_iff hR ha1).mp h⟩
    · exact tmA_not_ge hR ha0 ha1 h
  · intro hw
    have hw' : ¬ (w.im = 0 ∧ R ≤ w.re) := fun h => hw ⟨h.1, Or.inr h.2⟩
    obtain ⟨ζ, hζ, rfl⟩ := tmA_exists hR hw'
    refine ⟨ζ, ⟨hζ, ?_⟩, rfl⟩
    rintro ⟨hb, h0, hr⟩
    apply hw
    have hn := gzA_mem_unitDisc_iff.mp hζ
    rw [hb] at hn
    have ha1 : ζ.re < 1 := by nlinarith
    have hζr : ζ = (ζ.re : ℂ) := Complex.ext (by simp) (by simp [hb])
    rw [hζr, tmA_psi_ofReal, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨rfl, Or.inl ((tmA_real_iff hR ha1).mpr ⟨h0, hr⟩)⟩

theorem tmPsi_isConformalOnto {R : ℝ} (hR : 0 < R) :
    IsConformalOnto (tmPsi R) (grotzschDomain (tmR0 R)) (teichmullerDomain R) :=
  ⟨(tmPsi_differentiableOn R).mono diff_subset, (tmPsi_injOn hR).mono diff_subset, tmPsi_image hR⟩

/-- In the proof of Theorem 5.2: `M(T_R) = μ(1 + 2R - √(4R + 4R²))`.

Proved (2026-09-23), following the book's footnote: `ψ(ζ) = -4Rζ/(1-ζ)²` (`tmPsi`) maps `Δ` bijectively onto
`ℂ ∖ [R, ∞)` and `[0, r₀]` onto `[-1, 0]` (`r₀ = tmR0 R`, `4R r₀ = (1 - r₀)²`), hence `B_{r₀}` conformally onto `T_R`;
compose its inverse with the annulus map `gzG` of Theorem 5.1. -/
theorem thm5_2_modulus_teichmullerDomain {R : ℝ} (hR : 0 < R) :
    (dcModulus (teichmullerDomain R)).toReal =
      grotzschMu (1 + 2 * R - Real.sqrt (4 * R + 4 * R ^ 2)) := by
  have h₀ := tmR0_pos hR
  have h₁ := tmR0_lt_one hR
  have ha := (scSide_pos h₀ h₁).1
  have hb := (scSide_pos h₀ h₁).2
  have hpos : 0 < π * scSideA (tmR0 R) / scSideB (tmR0 R) := by positivity
  have hB : IsOpen (grotzschDomain (tmR0 R)) := (grotzschDomain_doublyConnected h₀ h₁).1.1
  have hequiv : ConformallyEquivalent (teichmullerDomain R)
      (annulus 1 (Real.exp (π * scSideA (tmR0 R) / scSideB (tmR0 R)))) :=
    (ConformallyEquivalent.symm ⟨_, tmPsi_isConformalOnto hR⟩ hB).trans ⟨_, gzG_isConformalOnto h₀ h₁⟩
  rw [dcModulus_eq_of_equiv (tz_isOpen_teichmullerDomain R) one_pos (Real.one_lt_exp_iff.2 hpos) hequiv,
    div_one, Real.log_exp, ENNReal.toReal_ofReal hpos.le]
  exact (gm_grotzschMu_eq h₀ h₁).symm

/-! ### (5.7): Landen's transformation — helpers -/

/-! ### Piece L: Landen's transformation -/

/-- Landen map `φ(x) = (1+t)x/(1+tx²)` and its derivative, integrand identity on `(-1,1)`:
`φ'(x)/√((1-φ²)(1-λ²φ²)) = (1+t)/√((1-x²)(1-t²x²))` with `λ = 2√t/(1+t)`. -/
theorem e57L_pointwise {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    |(1 + t) * (1 - t * x ^ 2) / (1 + t * x ^ 2) ^ 2| *
        (1 / Real.sqrt ((1 - ((1 + t) * x / (1 + t * x ^ 2)) ^ 2) *
          (1 - (2 * Real.sqrt t / (1 + t)) ^ 2 * ((1 + t) * x / (1 + t * x ^ 2)) ^ 2))) =
      (1 + t) * (1 / Real.sqrt ((1 - x ^ 2) * (1 - t ^ 2 * x ^ 2))) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hx2' : x ^ 2 < 1 := by nlinarith
  have hx0 : 0 ≤ x ^ 2 := sq_nonneg x
  have hD : 0 < 1 + t * x ^ 2 := by positivity
  have hc : 0 < 1 - t * x ^ 2 := by nlinarith
  have hP : 0 < (1 - x ^ 2) * (1 - t ^ 2 * x ^ 2) := by
    apply mul_pos <;> nlinarith [mul_pos ht₀ ht₀]
  have hlam : (2 * Real.sqrt t / (1 + t)) ^ 2 = 4 * t / (1 + t) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt ht₀.le]; ring
  have hid : (1 - ((1 + t) * x / (1 + t * x ^ 2)) ^ 2) *
          (1 - (2 * Real.sqrt t / (1 + t)) ^ 2 * ((1 + t) * x / (1 + t * x ^ 2)) ^ 2) =
        ((1 - x ^ 2) * (1 - t ^ 2 * x ^ 2)) * ((1 - t * x ^ 2) / (1 + t * x ^ 2) ^ 2) ^ 2 := by
    rw [hlam]
    have h1t : (1 + t) ≠ 0 := by positivity
    field_simp
    ring
  have hcq : 0 < (1 - t * x ^ 2) / (1 + t * x ^ 2) ^ 2 := by positivity
  rw [hid, Real.sqrt_mul hP.le, Real.sqrt_sq hcq.le]
  have habs : |(1 + t) * (1 - t * x ^ 2) / (1 + t * x ^ 2) ^ 2| =
      (1 + t) * (1 - t * x ^ 2) / (1 + t * x ^ 2) ^ 2 := abs_of_pos (by positivity)
  rw [habs]
  have hsP : 0 < Real.sqrt ((1 - x ^ 2) * (1 - t ^ 2 * x ^ 2)) := Real.sqrt_pos.2 hP
  field_simp

/-- The Landen map `φ(x) = (1+t)x/(1+tx²)` maps `(-1,1)` onto `(-1,1)` and is injective there. -/
theorem e57L_image {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    (fun x : ℝ => (1 + t) * x / (1 + t * x ^ 2)) '' Ioo (-1 : ℝ) 1 = Ioo (-1 : ℝ) 1 ∧
      InjOn (fun x : ℝ => (1 + t) * x / (1 + t * x ^ 2)) (Ioo (-1 : ℝ) 1) := by
  refine ⟨Subset.antisymm ?_ ?_, ?_⟩
  · rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
    have hD : 0 < 1 + t * x ^ 2 := by positivity
    simp only [mem_Ioo]
    constructor
    · rw [lt_div_iff₀ hD]; nlinarith [mul_pos ht₀ (mul_pos (by linarith : (0:ℝ) < 1 + x) (by linarith : (0:ℝ) < 1 + x))]
    · rw [div_lt_iff₀ hD]; nlinarith [mul_pos ht₀ (mul_pos (by linarith : (0:ℝ) < 1 - x) (by linarith : (0:ℝ) < 1 - x))]
  · have hc : ContinuousOn (fun x : ℝ => (1 + t) * x / (1 + t * x ^ 2)) (Icc (-1) 1) := by
      apply Continuous.continuousOn
      apply Continuous.div (by fun_prop) (by fun_prop)
      intro x; positivity
    have h := intermediate_value_Ioo (by norm_num : (-1 : ℝ) ≤ 1) hc
    have e1 : (1 + t) * (-1 : ℝ) / (1 + t * (-1) ^ 2) = -1 := by
      field_simp
    have e2 : (1 + t) * (1 : ℝ) / (1 + t * 1 ^ 2) = 1 := by
      field_simp
    simp only [e1, e2] at h
    exact h
  · intro x hx y hy hxy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    have hDx : 0 < 1 + t * x ^ 2 := by positivity
    have hDy : 0 < 1 + t * y ^ 2 := by positivity
    simp only at hxy
    rw [div_eq_div_iff hDx.ne' hDy.ne'] at hxy
    have hxy1 : t * (x * y) < 1 := by
      have : |x * y| < 1 := by
        rw [abs_mul]
        have := abs_lt.2 ⟨hx1, hx2⟩
        have := abs_lt.2 ⟨hy1, hy2⟩
        nlinarith [abs_nonneg x, abs_nonneg y]
      have := (abs_lt.1 this).2
      nlinarith
    have hfac : (1 + t) * ((x - y) * (1 - t * (x * y))) = 0 := by linear_combination hxy
    have h1t : (1 + t) ≠ 0 := by positivity
    rcases mul_eq_zero.1 hfac with h | h
    · exact absurd h h1t
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · linarith

theorem e57_landen {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    scSideB (2 * Real.sqrt t / (1 + t)) = (1 + t) * scSideB t := by
  obtain ⟨himg, hinj⟩ := e57L_image ht₀ ht₁
  have hder : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivWithinAt (fun x : ℝ => (1 + t) * x / (1 + t * x ^ 2))
      ((1 + t) * (1 - t * x ^ 2) / (1 + t * x ^ 2) ^ 2) (Ioo (-1 : ℝ) 1) x := by
    intro x _
    have hD : (1 + t * x ^ 2) ≠ 0 := by positivity
    have h1 : HasDerivAt (fun x : ℝ => (1 + t) * x) ((1 + t) * 1) x :=
      (hasDerivAt_id x).const_mul (1 + t)
    have h2 : HasDerivAt (fun x : ℝ => 1 + t * x ^ 2) (t * (↑2 * x ^ (2 - 1))) x :=
      ((hasDerivAt_pow 2 x).const_mul t).const_add 1
    refine (HasDerivAt.hasDerivWithinAt ?_)
    refine (h1.div h2 hD).congr_deriv ?_
    field_simp
    ring
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hder hinj
    (fun y => 1 / Real.sqrt ((1 - y ^ 2) * (1 - (2 * Real.sqrt t / (1 + t)) ^ 2 * y ^ 2)))
  rw [himg] at hcov
  unfold scSideB
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo, hcov,
    intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo ?_
  intro x hx
  simp only [smul_eq_mul]
  exact e57L_pointwise ht₀ ht₁ hx

/-! ### Piece K: the complementary modulus -/

/-- Evenness: `scSideB c = 2 ∫₀¹ dt/√((1-t²)(1-c²t²))` for `c ∈ (0,1)`. -/
theorem e57K_sideB_eq_two_mul {c : ℝ} (hc₀ : 0 < c) (hc₁ : c < 1) :
    scSideB c = 2 * ∫ t in (0 : ℝ)..1, 1 / Real.sqrt ((1 - t ^ 2) * (1 - c ^ 2 * t ^ 2)) := by
  set g : ℝ → ℝ := fun t => 1 / Real.sqrt ((1 - t ^ 2) * (1 - c ^ 2 * t ^ 2)) with hg
  have hB : scSideB c = ∫ t in (-1 : ℝ)..1, g t := rfl
  have hint : IntervalIntegrable g volume (-1) 1 :=
    intervalIntegral.intervalIntegrable_of_integral_ne_zero (hB ▸ (scSide_pos hc₀ hc₁).2.ne')
  have h1 : IntervalIntegrable g volume (-1) 0 :=
    hint.mono_set (Set.uIcc_subset_uIcc (by simp) (by simp))
  have h2 : IntervalIntegrable g volume 0 1 :=
    hint.mono_set (Set.uIcc_subset_uIcc (by simp) (by simp))
  have hneg : (∫ t in (-1 : ℝ)..0, g t) = ∫ t in (0 : ℝ)..1, g t := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) g
    simp only [neg_zero] at this
    rw [← this]
    congr 1
    ext t
    simp [hg]
  rw [hB, ← intervalIntegral.integral_add_adjacent_intervals h1 h2, hneg]
  ring

/-- Substitution `x = 1/√(1-(1-k²)t²)`: `scSideA k = ∫₀¹ dt/√((1-t²)(1-(1-k²)t²))`. -/
theorem e57K_sideA_eq_integral {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    scSideA k = ∫ t in (0 : ℝ)..1, 1 / Real.sqrt ((1 - t ^ 2) * (1 - (1 - k ^ 2) * t ^ 2)) := by
  set m : ℝ := 1 - k ^ 2 with hm
  have hm₀ : 0 < m := by nlinarith
  have hm₁ : m < 1 := by nlinarith
  have hk1 : 1 < 1 / k := one_lt_one_div hk₀ hk₁
  set φ : ℝ → ℝ := fun t => (Real.sqrt (1 - m * t ^ 2))⁻¹ with hφ
  set φ' : ℝ → ℝ := fun t => m * t / Real.sqrt (1 - m * t ^ 2) ^ 3 with hφ'
  have hu : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < 1 - m * t ^ 2 := fun t ht => by
    have : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
    nlinarith
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt φ (φ' t) (Ioo 0 1) t := by
    intro t ht
    have hut := hu t ht
    have hs : 0 < Real.sqrt (1 - m * t ^ 2) := Real.sqrt_pos.2 hut
    have h1 : HasDerivAt (fun t : ℝ => 1 - m * t ^ 2) (-(m * (2 * t))) t := by
      simpa using ((hasDerivAt_pow 2 t).const_mul m).const_sub 1
    have h2 := (h1.sqrt hut.ne').inv hs.ne'
    refine (h2.congr_deriv ?_).hasDerivWithinAt
    simp only [hφ']
    field_simp
  have hinj : InjOn φ (Ioo 0 1) := by
    intro s hs t ht hst
    simp only [hφ, inv_inj] at hst
    have h := (Real.sqrt_inj (hu s hs).le (hu t ht).le).1 hst
    have h2 : s ^ 2 = t ^ 2 := by
      have := mul_left_cancel₀ hm₀.ne' (by linarith : m * s ^ 2 = m * t ^ 2)
      exact this
    exact (pow_left_inj₀ hs.1.le ht.1.le two_ne_zero).1 h2
  have himage : φ '' Ioo 0 1 = Ioo 1 (1 / k) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hut := hu t ht
      have ht2 : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
      have hlt1 : 1 - m * t ^ 2 < 1 := by
        have := mul_pos hm₀ (pow_pos ht.1 2); linarith
      have hgt : k ^ 2 < 1 - m * t ^ 2 := by nlinarith
      have hs1 : Real.sqrt (1 - m * t ^ 2) < 1 := by
        rw [Real.sqrt_lt' one_pos]; linarith
      have hsk : k < Real.sqrt (1 - m * t ^ 2) := by
        rw [Real.lt_sqrt hk₀.le]; exact hgt
      have hs : 0 < Real.sqrt (1 - m * t ^ 2) := Real.sqrt_pos.2 hut
      refine ⟨?_, ?_⟩
      · simp only [hφ]
        exact (one_lt_inv₀ hs).2 hs1
      · simp only [hφ, one_div]
        exact (inv_lt_inv₀ hs hk₀).2 hsk
    · rintro ⟨hx1, hx2⟩
      have hx0 : 0 < x := by linarith
      have hkx : k * x < 1 := by
        have := (lt_div_iff₀ hk₀).1 hx2; linarith
      have hA : 0 < 1 - 1 / x ^ 2 := by
        have : 1 / x ^ 2 < 1 := by
          rw [div_lt_one (by positivity)]; nlinarith
        linarith
      have hB : 1 - 1 / x ^ 2 < m := by
        have : k ^ 2 < 1 / x ^ 2 := by
          have hkx0 : 0 < k * x := mul_pos hk₀ hx0
          have : (k * x) ^ 2 < 1 := by nlinarith
          rw [lt_div_iff₀ (by positivity)]; nlinarith
        linarith
      refine ⟨Real.sqrt ((1 - 1 / x ^ 2) / m), ⟨Real.sqrt_pos.2 (div_pos hA hm₀), ?_⟩, ?_⟩
      · rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one hm₀]; linarith
      · simp only [hφ]
        rw [Real.sq_sqrt (div_pos hA hm₀).le]
        have : 1 - m * ((1 - 1 / x ^ 2) / m) = (1 / x) ^ 2 := by
          field_simp; ring
        rw [this, Real.sqrt_sq (by positivity), one_div, inv_inv]
  have hcv := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun x : ℝ => 1 / Real.sqrt ((x ^ 2 - 1) * (1 - k ^ 2 * x ^ 2)))
  rw [himage] at hcv
  unfold scSideA
  rw [intervalIntegral.integral_of_le hk1.le, integral_Ioc_eq_integral_Ioo, hcv,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo ?_
  intro t ht
  have hut := hu t ht
  set s := Real.sqrt (1 - m * t ^ 2) with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hut
  have hs2 : s ^ 2 = 1 - m * t ^ 2 := Real.sq_sqrt hut.le
  have hw0 : 0 < 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  set w := Real.sqrt (1 - t ^ 2) with hwdef
  have hw : 0 < w := Real.sqrt_pos.2 hw0
  have hw2 : w ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hw0.le
  have hkey : ((s⁻¹) ^ 2 - 1) * (1 - k ^ 2 * (s⁻¹) ^ 2) = (m * t * w / s ^ 2) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, hw2]
    field_simp
    linear_combination (1 + k ^ 2 - s ^ 2 - (1 - m * t ^ 2)) * hs2 - m * t ^ 2 * hm
  have hrhs : Real.sqrt ((1 - t ^ 2) * (1 - m * t ^ 2)) = w * s := Real.sqrt_mul hw0.le _
  simp only [hφ, hφ', smul_eq_mul]
  rw [← hsdef, hkey, Real.sqrt_sq (by have := ht.1; positivity), hrhs,
    abs_of_pos (by have := ht.1; positivity)]
  have ht0 : t ≠ 0 := ht.1.ne'
  field_simp

theorem e57_sideA_eq {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    scSideA k = scSideB (Real.sqrt (1 - k ^ 2)) / 2 := by
  have hc₀ : 0 < Real.sqrt (1 - k ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hc₁ : Real.sqrt (1 - k ^ 2) < 1 := by
    rw [Real.sqrt_lt' one_pos]; nlinarith
  rw [e57K_sideB_eq_two_mul hc₀ hc₁, Real.sq_sqrt (by nlinarith), e57K_sideA_eq_integral hk₀ hk₁]
  ring

/-! ### Piece G: algebra -/

/-- For `u ∈ (0,1)` and `v = (1-u)/(1+u)`: `2√v/(1+v) = √(1-u²)` and `√(1-v²) = 2√u/(1+u)`. -/
theorem e57_landen_param {u : ℝ} (hu₀ : 0 < u) (hu₁ : u < 1) :
    2 * Real.sqrt ((1 - u) / (1 + u)) / (1 + (1 - u) / (1 + u)) = Real.sqrt (1 - u ^ 2) ∧
      Real.sqrt (1 - ((1 - u) / (1 + u)) ^ 2) = 2 * Real.sqrt u / (1 + u) := by
  have h1u : (0 : ℝ) < 1 + u := by linarith
  have h1u' : (0 : ℝ) < 1 - u := by linarith
  have ha := Real.sq_sqrt h1u'.le
  have hb := Real.sq_sqrt h1u.le
  have ha0 := Real.sqrt_pos.2 h1u'
  have hb0 := Real.sqrt_pos.2 h1u
  have hc := Real.sq_sqrt hu₀.le
  have hc0 := Real.sqrt_pos.2 hu₀
  constructor
  · rw [Real.sqrt_div' _ h1u.le, show 1 - u ^ 2 = (1 - u) * (1 + u) by ring,
      Real.sqrt_mul h1u'.le]
    rw [div_eq_iff (by positivity)]
    field_simp
    nlinarith
  · rw [show 1 - ((1 - u) / (1 + u)) ^ 2 = (2 * Real.sqrt u / (1 + u)) ^ 2 by
      rw [div_pow, div_pow, mul_pow, hc]; field_simp; ring]
    exact Real.sqrt_sq (by positivity)

/-- `r₀ = (1-u)/(1+u)` and `√(1/(1+R)) = √(1-u²)` for `u = √(R/(1+R))`, and `u ∈ (0,1)`. -/
theorem e57_R_param {R : ℝ} (hR : 0 < R) :
    0 < Real.sqrt (R / (1 + R)) ∧ Real.sqrt (R / (1 + R)) < 1 ∧
      1 + 2 * R - Real.sqrt (4 * R + 4 * R ^ 2) =
        (1 - Real.sqrt (R / (1 + R))) / (1 + Real.sqrt (R / (1 + R))) ∧
      Real.sqrt (1 / (1 + R)) = Real.sqrt (1 - Real.sqrt (R / (1 + R)) ^ 2) := by
  have h1R : (0 : ℝ) < 1 + R := by linarith
  have hs := Real.sq_sqrt hR.le
  have ht := Real.sq_sqrt h1R.le
  have hs0 := Real.sqrt_pos.2 hR
  have ht0 := Real.sqrt_pos.2 h1R
  have hu2 : Real.sqrt (R / (1 + R)) ^ 2 = R / (1 + R) := Real.sq_sqrt (by positivity)
  refine ⟨Real.sqrt_pos.2 (by positivity), ?_, ?_, ?_⟩
  · rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one h1R]; linarith
  · have h4 : Real.sqrt (4 * R + 4 * R ^ 2) = 2 * Real.sqrt R * Real.sqrt (1 + R) := by
      rw [show 4 * R + 4 * R ^ 2 = (2 * Real.sqrt R * Real.sqrt (1 + R)) ^ 2 by
        rw [mul_pow, mul_pow, hs, ht]; ring]
      exact Real.sqrt_sq (by positivity)
    rw [h4, Real.sqrt_div' _ h1R.le, eq_div_iff (by positivity)]
    field_simp
    linear_combination (-2 * Real.sqrt (1 + R)) * hs + (-2 * Real.sqrt R) * ht
  · congr 1
    rw [hu2]; field_simp; ring

/-! ### The target -/

/-- (5.7): `M(T_R) = 2 μ(√(1/(1+R)))`.

Proved (2026-09-23): `M(T_R) = μ(r₀)` (`thm5_2_modulus_teichmullerDomain`) and `μ(r) = π a_r / b_r`; with
`u = √(R/(1+R))`, `r₀ = (1-u)/(1+u)`, Landen's transformation `b(2√t/(1+t)) = (1+t) b(t)` (`e57_landen`, substitution
`y = (1+t)x/(1+tx²)`) and the complementary-modulus identity `a(k) = b(√(1-k²))/2` (`e57_sideA_eq`) give
`a(r₀)/b(r₀) = 2 a(s)/b(s)`, `s = √(1/(1+R))`. -/
theorem eq5_7 {R : ℝ} (hR : 0 < R) :
    (dcModulus (teichmullerDomain R)).toReal = 2 * grotzschMu (Real.sqrt (1 / (1 + R))) := by
  obtain ⟨hu₀, hu₁, hr₀, hs⟩ := e57_R_param hR
  set u := Real.sqrt (R / (1 + R)) with hu
  obtain ⟨hL1, hL2⟩ := e57_landen_param hu₀ hu₁
  have hv₀ : 0 < (1 - u) / (1 + u) := div_pos (by linarith) (by linarith)
  have hv₁ : (1 - u) / (1 + u) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hs₀ : 0 < Real.sqrt (1 - u ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hs₁ : Real.sqrt (1 - u ^ 2) < 1 := by
    rw [Real.sqrt_lt' one_pos]; nlinarith
  rw [thm5_2_modulus_teichmullerDomain hR, hr₀, hs, gm_grotzschMu_eq hv₀ hv₁,
    gm_grotzschMu_eq hs₀ hs₁, e57_sideA_eq hv₀ hv₁, e57_sideA_eq hs₀ hs₁, hL2]
  have hsq : Real.sqrt (1 - Real.sqrt (1 - u ^ 2) ^ 2) = u := by
    rw [Real.sq_sqrt (by nlinarith), sub_sub_cancel, Real.sqrt_sq hu₀.le]
  rw [hsq, e57_landen hu₀ hu₁]
  have hbs : scSideB (Real.sqrt (1 - u ^ 2)) = (1 + (1 - u) / (1 + u)) * scSideB ((1 - u) / (1 + u)) := by
    rw [← hL1, e57_landen hv₀ hv₁]
  rw [hbs]
  have hbv := (scSide_pos hv₀ hv₁).2
  have hbu := (scSide_pos hu₀ hu₁).2
  have h1u : (0 : ℝ) < 1 + u := by linarith
  field_simp
  ring

/-- **Theorem 5.2′**: a doubly connected domain separating `{-1, 0}` from `{R, ∞}` satisfies
`M(B) ≤ 2 μ(√(1/(1+R)))`. -/
theorem thm5_2' {R : ℝ} (hR : 0 < R) {B : Set ℂ} (hB : IsDoublyConnected B)
    (hsep : SeparatesSets B {((-1 : ℂ) : ExtPlane), ((0 : ℂ) : ExtPlane)}
      {((R : ℂ) : ExtPlane), extInf}) :
    dcModulus B ≤ ENNReal.ofReal (2 * grotzschMu (Real.sqrt (1 / (1 + R)))) := by
  have hfin : dcModulus (teichmullerDomain R) ≠ ⊤ := by
    rw [tz_dcModulus_teichmullerDomain hR]
    exact ENNReal.ofReal_ne_top
  rw [← eq5_7 hR, ENNReal.ofReal_toReal hfin]
  exact thm5_2_teichmuller hR hB hsep

/-- Multiplication by a unimodular constant maps the unit disc onto itself. -/
theorem t53_ta_image_mul_ball {c : ℂ} (hc : ‖c‖ = 1) :
    (fun w => c * w) '' ball (0 : ℂ) 1 = ball (0 : ℂ) 1 := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc
    exact zero_ne_one hc
  ext w
  simp only [mem_image, mem_ball_zero_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [norm_mul, hc, one_mul]
    exact hv
  · intro hw
    refine ⟨c⁻¹ * w, ?_, ?_⟩
    · rw [norm_mul, norm_inv, hc, inv_one, one_mul]
      exact hw
    · rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

/-- Koebe 1/4 + growth for a univalent `ψ` of the unit disc with `ψ 0 = 0` omitting `w`: if
`ψ t = z` with `0 < t < 1`, then `|z| ≤ 4|w| t/(1-t)²`. -/
theorem t53_ta_koebe_bound {ψ : ℂ → ℂ} (hψ : DifferentiableOn ℂ ψ (ball (0 : ℂ) 1))
    (hinj : InjOn ψ (ball (0 : ℂ) 1)) (h0 : ψ 0 = 0) {w z : ℂ} (hw : w ∉ ψ '' ball (0 : ℂ) 1)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hz : ψ t = z) :
    ‖z‖ ≤ 4 * ‖w‖ * (t / (1 - t) ^ 2) := by
  have hq : ‖deriv ψ 0‖ ≤ 4 * ‖w‖ := koebe_quarter_of_not_mem hψ hinj h0 hw
  have htn : ‖(t : ℂ)‖ = t := Complex.norm_of_nonneg ht0.le
  have htlt : ‖(t : ℂ)‖ < 1 := by rw [htn]; exact ht1
  have hg : ‖ψ t‖ ≤ ‖deriv ψ 0‖ * ‖(t : ℂ)‖ / (1 - ‖(t : ℂ)‖) ^ 2 :=
    koebe_growth_scaled hψ hinj h0 htlt
  rw [hz, htn, mul_div_assoc] at hg
  have h1t : 0 < 1 - t := by linarith
  have hpos : 0 ≤ t / (1 - t) ^ 2 := by positivity
  exact hg.trans (mul_le_mul_of_nonneg_right hq hpos)

/-- **Riemann map of `B ∪ C₁`, normalized, with the Koebe estimate.**  `A` is the component of
`ℂ̄ ∖ B` containing `0, z₁` (read in `ℂ`); `φ` maps `B ∪ A` conformally onto the unit disc with
`φ 0 = 0`, `φ z₁ = t ∈ (0,1)`; Koebe 1/4 + growth for `φ⁻¹` give `|z₁| ≤ 4|z₂| t/(1-t)²`. -/
theorem t53_riemann_koebe {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    {B : Set ℂ} (hB : IsDoublyConnected B)
    (hsep : SeparatesSets B {((0 : ℂ) : ExtPlane), (z₁ : ExtPlane)} {(z₂ : ExtPlane), extInf}) :
    ∃ (A : Set ℂ) (φ : ℂ → ℂ) (t : ℝ),
      IsCompact A ∧ IsConnected A ∧ Disjoint B A ∧ (0 : ℂ) ∈ A ∧ z₁ ∈ A ∧ IsOpen (B ∪ A) ∧
      DifferentiableOn ℂ φ (B ∪ A) ∧ InjOn φ (B ∪ A) ∧ φ '' (B ∪ A) = ball (0 : ℂ) 1 ∧
      φ 0 = 0 ∧ 0 < t ∧ t < 1 ∧ φ z₁ = t ∧ ‖z₁‖ ≤ 4 * ‖z₂‖ * (t / (1 - t) ^ 2) := by
  -- `z₂ ≠ 0` is not needed here: `z₂ ∉ B ∪ A ∋ 0` already
  have _ := hz₂
  obtain ⟨x₁, hx₁, x₂, hx₂, hE₁, hE₂, hne⟩ := hsep
  have hinf : extInf ∈ (toExt B)ᶜ := extInf_mem_compl_toExt B
  have hinf₂ : extInf ∈ connectedComponentIn (toExt B)ᶜ x₂ :=
    hE₂ (mem_insert_of_mem _ (mem_singleton _))
  have hx₂eq : connectedComponentIn (toExt B)ᶜ x₂ = connectedComponentIn (toExt B)ᶜ extInf :=
    connectedComponentIn_eq hinf₂
  have hne' : connectedComponentIn (toExt B)ᶜ x₁ ≠ connectedComponentIn (toExt B)ᶜ extInf := by
    rw [← hx₂eq]
    exact hne
  obtain ⟨hAcpt, hAconn, -, hAB⟩ := isCompact_isConnected_component_ne_extInf hB hx₁ hne'
  obtain ⟨hUopen, hUconn, hUcompl⟩ := fill_component hB hx₁ hne'
  set A : Set ℂ := {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x₁} with hAdef
  have h0A : (0 : ℂ) ∈ A := hE₁ (mem_insert _ _)
  have hz₁A : z₁ ∈ A := hE₁ (mem_insert_of_mem _ (mem_singleton _))
  have hz₂U : z₂ ∉ B ∪ A := by
    have h : ((z₂ : ℂ) : ExtPlane) ∈ (toExt (B ∪ A))ᶜ := by
      rw [hUcompl, ← hx₂eq]
      exact hE₂ (mem_insert _ _)
    exact coe_mem_compl_toExt_iff.mp h
  have h0U : (0 : ℂ) ∈ B ∪ A := Or.inr h0A
  have hz₁U : z₁ ∈ B ∪ A := Or.inr hz₁A
  have hUc' : IsConnected (toExt (B ∪ A))ᶜ := by
    rw [hUcompl]
    exact isConnected_connectedComponentIn_iff.mpr hinf
  obtain ⟨f, hf, hfb⟩ := RMT.exists_riemannMap_of_hasHolomorphicSqrt hUopen hUconn ⟨z₂, hz₂U⟩
    (hasHolomorphicSqrt_of_isConnected_compl hUopen hUconn hUc') h0U
  have hf0 : f 0 = 0 := hf.center
  have hfz₁ : f z₁ ≠ 0 := by
    intro h
    exact hz₁ (hf.injOn hz₁U h0U (h.trans hf0.symm))
  -- rotate so that `z₁ ↦ t = |f z₁|`
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = ‖f z₁‖ := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht]
    exact norm_pos_iff.mpr hfz₁
  have ht1 : t < 1 := by
    rw [ht]
    exact mem_ball_zero_iff.mp (hf.mapsTo hz₁U)
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = conj (f z₁) / (t : ℂ) := ⟨_, rfl⟩
  have hcn : ‖c‖ = 1 := by
    rw [hc, norm_div, Complex.norm_conj, Complex.norm_of_nonneg ht0.le, ← ht, div_self ht0.ne']
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hcn
    exact zero_ne_one hcn
  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, φ = fun z => c * f z := ⟨_, rfl⟩
  have hφd : DifferentiableOn ℂ φ (B ∪ A) := by
    rw [hφ]
    exact hf.diff.const_mul c
  have hφinj : InjOn φ (B ∪ A) := by
    intro x hx y hy h
    rw [hφ] at h
    exact hf.injOn hx hy (mul_left_cancel₀ hc0 h)
  have hφimg : φ '' (B ∪ A) = ball (0 : ℂ) 1 := by
    have h : φ '' (B ∪ A) = (fun w => c * w) '' (f '' (B ∪ A)) := by
      rw [image_image, hφ]
    rw [h, hfb.image_eq]
    exact t53_ta_image_mul_ball hcn
  have hφ0 : φ 0 = 0 := by
    rw [hφ]
    show c * f 0 = 0
    rw [hf0, mul_zero]
  have hφz₁ : φ z₁ = t := by
    rw [hφ]
    show c * f z₁ = t
    rw [hc, div_mul_eq_mul_div, Complex.conj_mul', ← ht, sq, mul_div_assoc, div_self htC,
      mul_one]
  -- the inverse map `ψ = φ⁻¹ : Δ → B ∪ A`
  have hφmaps : MapsTo φ (B ∪ A) (ball (0 : ℂ) 1) := fun z hz => hφimg ▸ mem_image_of_mem φ hz
  have hφb : BijOn φ (B ∪ A) RMT.disc := ⟨hφmaps, hφinj, hφimg.symm.subset⟩
  obtain ⟨hψd, hψb⟩ := RMT.invFunOn_riemannMap hUopen hφd hφinj hφb
  have hleft := hφinj.leftInvOn_invFunOn
  have hψ0 : Function.invFunOn φ (B ∪ A) 0 = 0 := by
    have h := hleft h0U
    rwa [hφ0] at h
  have hψt : Function.invFunOn φ (B ∪ A) t = z₁ := by
    have h := hleft hz₁U
    rwa [hφz₁] at h
  have hz₂ψ : z₂ ∉ Function.invFunOn φ (B ∪ A) '' ball (0 : ℂ) 1 := by
    rw [hψb.image_eq]
    exact hz₂U
  refine ⟨A, φ, t, hAcpt, hAconn, hAB, h0A, hz₁A, hUopen, hφd, hφinj, hφimg, hφ0, ht0, ht1, hφz₁,
    ?_⟩
  exact t53_ta_koebe_bound hψd hψb.injOn hψ0 hz₂ψ ht0 ht1 hψt

/-- At a real point `t`, the Koebe function takes the real value `t/(1-t)²`. -/
theorem t53_tb_koebeFn_ofReal (t : ℝ) : koebeFn (t : ℂ) = ((t / (1 - t) ^ 2 : ℝ) : ℂ) := by
  unfold koebeFn
  push_cast
  ring

/-- For `0 < t < 1`, `k(t) = t/(1-t)²` is a nonzero complex number. -/
theorem t53_tb_koebeFn_ofReal_ne_zero {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    koebeFn (t : ℂ) ≠ 0 := by
  rw [t53_tb_koebeFn_ofReal]
  have h : (0 : ℝ) < t / (1 - t) ^ 2 := div_pos ht₀ (pow_pos (by linarith) 2)
  exact_mod_cast h.ne'

/-- The Koebe function is complex differentiable at every point of the unit disc. -/
theorem t53_tb_koebeFn_differentiableAt {v : ℂ} (hv : v ∈ ball (0 : ℂ) 1) :
    DifferentiableAt ℂ koebeFn v := by
  have hv1 : (1 : ℂ) - v ≠ 0 := by
    intro h
    have hv' : v = 1 := (sub_eq_zero.1 h).symm
    rw [mem_ball_zero_iff, hv', norm_one] at hv
    exact lt_irrefl _ hv
  have h1 : DifferentiableAt ℂ (fun v : ℂ => (1 - v) ^ 2) v := by fun_prop
  have h2 : DifferentiableAt ℂ (fun v : ℂ => v / (1 - v) ^ 2) v :=
    differentiableAt_id.div h1 (pow_ne_zero 2 hv1)
  exact h2

/-- The scaled Koebe function `v ↦ -k(v)/k(t)` is holomorphic and injective on the unit disc. -/
theorem t53_koebe_scaled_conformal {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    DifferentiableOn ℂ (fun v => -koebeFn v / koebeFn t) (ball (0 : ℂ) 1) ∧
      InjOn (fun v => -koebeFn v / koebeFn t) (ball (0 : ℂ) 1) := by
  have hc : koebeFn (t : ℂ) ≠ 0 := t53_tb_koebeFn_ofReal_ne_zero ht₀ ht₁
  refine ⟨?_, ?_⟩
  · intro v hv
    exact ((t53_tb_koebeFn_differentiableAt hv).neg.div_const _).differentiableWithinAt
  · intro v₁ hv₁ v₂ hv₂ h
    have h' : -koebeFn v₁ / koebeFn t = -koebeFn v₂ / koebeFn t := h
    exact koebeFn_injOn hv₁ hv₂ (neg_inj.1 ((div_left_inj' hc).1 h'))

/-- The scaled Koebe function `v ↦ -k(v)/k(t)` maps the unit disc onto `ℂ ∖ [R, ∞)`,
`R = (1-t)²/(4t)`. -/
theorem t53_koebe_scaled_image {t : ℝ} (ht₀ : 0 < t) (ht₁ : t < 1) :
    (fun v => -koebeFn v / koebeFn t) '' ball (0 : ℂ) 1 =
      {w : ℂ | ¬ (w.im = 0 ∧ (1 - t) ^ 2 / (4 * t) ≤ w.re)} := by
  set c : ℝ := t / (1 - t) ^ 2 with hc_def
  set R : ℝ := (1 - t) ^ 2 / (4 * t) with hR_def
  have h1t : 0 < 1 - t := by linarith
  have hcpos : 0 < c := div_pos ht₀ (pow_pos h1t 2)
  have hkt : koebeFn (t : ℂ) = (c : ℂ) := t53_tb_koebeFn_ofReal t
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hcR : c * R = 1 / 4 := by
    rw [hc_def, hR_def]
    field_simp
  ext w
  simp only [mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hk : koebeFn v ∈ koebeFn '' ball (0 : ℂ) 1 := mem_image_of_mem _ hv
    rw [koebeFn_image] at hk
    rintro ⟨him, hre⟩
    apply hk
    rw [hkt, neg_div, Complex.neg_im, Complex.div_ofReal_im] at him
    rw [hkt, neg_div, Complex.neg_re, Complex.div_ofReal_re] at hre
    have him' : (koebeFn v).im = 0 := by
      have h := neg_eq_zero.1 him
      rwa [div_eq_zero_iff, or_iff_left hcpos.ne'] at h
    refine ⟨him', ?_⟩
    have h2 : c * R ≤ c * (-((koebeFn v).re / c)) := mul_le_mul_of_nonneg_left hre hcpos.le
    rw [hcR, mul_neg, mul_div_cancel₀ _ hcpos.ne'] at h2
    linarith
  · intro hw
    have hu : -((c : ℂ) * w) ∈ koebeFn '' ball (0 : ℂ) 1 := by
      rw [koebeFn_image]
      rintro ⟨him, hre⟩
      apply hw
      rw [Complex.neg_im, Complex.im_ofReal_mul] at him
      rw [Complex.neg_re, Complex.re_ofReal_mul] at hre
      have him' : w.im = 0 := by
        have h := neg_eq_zero.1 him
        rwa [mul_eq_zero, or_iff_right hcpos.ne'] at h
      refine ⟨him', ?_⟩
      have h2 : c * R ≤ c * w.re := by rw [hcR]; linarith
      exact le_of_mul_le_mul_left h2 hcpos
    obtain ⟨v, hv, hkv⟩ := hu
    refine ⟨v, hv, ?_⟩
    rw [hkv, hkt, neg_neg, mul_div_cancel_left₀ _ hcne]

/-- The ray `[R, ∞)` on the real axis is the image of `Ici R` under `ℝ → ℂ`. -/
theorem t53_tb_ray_eq_image (R : ℝ) :
    {w : ℂ | w.im = 0 ∧ R ≤ w.re} = ((↑) : ℝ → ℂ) '' Ici R := by
  ext w
  constructor
  · rintro ⟨him, hre⟩
    exact ⟨w.re, hre, Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im, him])⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Complex.ofReal_im x, by rw [Complex.ofReal_re]; exact hx⟩

/-- `∞` is a limit point in `ℂ̄` of the ray `[R, ∞)` on the real axis. -/
theorem t53_tb_extInf_mem_closure_ray (R : ℝ) :
    extInf ∈ closure (toExt {w : ℂ | w.im = 0 ∧ R ≤ w.re}) := by
  rw [mem_closure_iff_nhds_basis OnePoint.hasBasis_nhds_infty]
  rintro s ⟨-, hs⟩
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hs.isBounded
  set x : ℝ := |M| + |R| + 1 with hx
  have hxpos : 0 < x := by positivity
  have hnorm : ‖((x : ℝ) : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_of_nonneg hxpos.le]
  refine ⟨((x : ℂ) : ExtPlane), ⟨(x : ℂ), ?_, rfl⟩, Or.inl ⟨(x : ℂ), ?_, rfl⟩⟩
  · refine ⟨Complex.ofReal_im x, ?_⟩
    rw [Complex.ofReal_re]
    linarith [le_abs_self R, abs_nonneg M]
  · intro hmem
    have h := hM _ hmem
    rw [hnorm] at h
    linarith [le_abs_self M, abs_nonneg R]

/-- The complement in `ℂ̄` of the slit plane `ℂ ∖ [R, ∞)` is connected. -/
theorem t53_isConnected_compl_slit (R : ℝ) :
    IsConnected (toExt {w : ℂ | ¬ (w.im = 0 ∧ R ≤ w.re)})ᶜ := by
  have hS : {w : ℂ | ¬ (w.im = 0 ∧ R ≤ w.re)}ᶜ = {w : ℂ | w.im = 0 ∧ R ≤ w.re} := by
    ext w
    simp only [mem_compl_iff, mem_ofPred_eq, not_not]
  rw [compl_toExt, hS]
  have hc : IsConnected (toExt {w : ℂ | w.im = 0 ∧ R ≤ w.re}) := by
    rw [t53_tb_ray_eq_image R, toExt]
    exact (isConnected_Ici.image _ Complex.continuous_ofReal.continuousOn).image _
      OnePoint.continuous_coe.continuousOn
  exact hc.subset_closure subset_union_left
    (union_subset subset_closure (singleton_subset_iff.2 (t53_tb_extInf_mem_closure_ray R)))

/-- If a set `S` is the disjoint union of two closed connected sets, then `S` has exactly two
connected components (closed-pieces variant of `card_connectedComponents_eq_two_of_union`). -/
theorem t53_tc_card_components_eq_two_of_closed_union {X : Type*} [TopologicalSpace X]
    {S A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAc : IsConnected A)
    (hBc : IsConnected B) (hAB : Disjoint A B) (hS : S = A ∪ B) :
    Nat.card (ConnectedComponents ↥S) = 2 := by
  subst hS
  have hAsub : A ⊆ A ∪ B := subset_union_left
  have hBsub : B ⊆ A ∪ B := subset_union_right
  -- the preimages of `A` and `B` in the subtype are complementary, closed and preconnected
  have hAcl : IsClosed (Subtype.val ⁻¹' A : Set ↥(A ∪ B)) := hA.preimage continuous_subtype_val
  have hBcl : IsClosed (Subtype.val ⁻¹' B : Set ↥(A ∪ B)) := hB.preimage continuous_subtype_val
  have hcompl : (Subtype.val ⁻¹' A : Set ↥(A ∪ B))ᶜ = Subtype.val ⁻¹' B := by
    ext ⟨x, hx⟩
    simp only [mem_compl_iff, mem_preimage]
    rcases hx with hxA | hxB
    · exact ⟨fun h => absurd hxA h, fun hxB => absurd hxB (Set.disjoint_left.1 hAB hxA)⟩
    · exact ⟨fun _ => hxB, fun _ hxA => Set.disjoint_left.1 hAB hxA hxB⟩
  have hAclopen : IsClopen (Subtype.val ⁻¹' A : Set ↥(A ∪ B)) :=
    ⟨hAcl, by rw [← isClosed_compl_iff, hcompl]; exact hBcl⟩
  have hBclopen : IsClopen (Subtype.val ⁻¹' B : Set ↥(A ∪ B)) :=
    ⟨hBcl, by rw [← isClosed_compl_iff, ← hcompl, compl_compl]; exact hAcl⟩
  have hApre : IsPreconnected (Subtype.val ⁻¹' A : Set ↥(A ∪ B)) := by
    rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.2 hAsub]
    exact hAc.isPreconnected
  have hBpre : IsPreconnected (Subtype.val ⁻¹' B : Set ↥(A ∪ B)) := by
    rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
      inter_eq_right.2 hBsub]
    exact hBc.isPreconnected
  -- the connected components are exactly these two sets
  have hcompA : ∀ x : ↥(A ∪ B), (x : X) ∈ A → connectedComponent x = Subtype.val ⁻¹' A :=
    fun x hx =>
      Subset.antisymm (hAclopen.connectedComponent_subset hx) (hApre.subset_connectedComponent hx)
  have hcompB : ∀ x : ↥(A ∪ B), (x : X) ∈ B → connectedComponent x = Subtype.val ⁻¹' B :=
    fun x hx =>
      Subset.antisymm (hBclopen.connectedComponent_subset hx) (hBpre.subset_connectedComponent hx)
  obtain ⟨a, ha⟩ := hAc.nonempty
  obtain ⟨b, hb⟩ := hBc.nonempty
  rw [Nat.card_eq_two_iff]
  refine ⟨ConnectedComponents.mk ⟨a, hAsub ha⟩, ConnectedComponents.mk ⟨b, hBsub hb⟩, ?_, ?_⟩
  · intro h
    rw [ConnectedComponents.coe_eq_coe, hcompA _ ha, hcompB _ hb] at h
    have hbA : (⟨b, hBsub hb⟩ : ↥(A ∪ B)) ∈ Subtype.val ⁻¹' A := by
      rw [h]; exact hb
    exact Set.disjoint_left.1 hAB hbA hb
  · ext c
    simp only [mem_insert_iff, mem_singleton_iff, mem_univ, iff_true]
    obtain ⟨⟨x, hx⟩, rfl⟩ := ConnectedComponents.surjective_coe c
    rcases hx with hxA | hxB
    · left
      rw [ConnectedComponents.coe_eq_coe, hcompA _ hxA, hcompA _ ha]
    · right
      rw [ConnectedComponents.coe_eq_coe, hcompB _ hxB, hcompB _ hb]

/-- For `W` injective on `B ∪ A` with `B`, `A` disjoint, `W(B) = W(B ∪ A) ∖ W(A)`. -/
theorem t53_tc_image_eq_diff {B A : Set ℂ} {W : ℂ → ℂ} (hAB : Disjoint B A)
    (hWinj : InjOn W (B ∪ A)) : W '' B = W '' (B ∪ A) \ W '' A := by
  ext z
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨mem_image_of_mem W (subset_union_left hb), ?_⟩
    rintro ⟨a, ha, hab⟩
    have hba : a = b := hWinj (subset_union_right ha) (subset_union_left hb) hab
    exact Set.disjoint_left.1 hAB hb (hba ▸ ha)
  · rintro ⟨⟨x, hx, rfl⟩, hxA⟩
    rcases hx with hxB | hxA'
    · exact mem_image_of_mem W hxB
    · exact absurd (mem_image_of_mem W hxA') hxA

/-- `ℂ̄ ∖ W(B)` is the union of `W(A)` and `ℂ̄ ∖ W(B ∪ A)`, when `W(B) = W(B ∪ A) ∖ W(A)`. -/
theorem t53_tc_compl_eq_union {B A : Set ℂ} {W : ℂ → ℂ}
    (hWB : W '' B = W '' (B ∪ A) \ W '' A) :
    (toExt (W '' B))ᶜ = toExt (W '' A) ∪ (toExt (W '' (B ∪ A)))ᶜ := by
  ext y
  induction y using OnePoint.rec with
  | infty => exact iff_of_true (extInf_mem_compl_toExt _) (Or.inr (extInf_mem_compl_toExt _))
  | coe z =>
    rw [coe_mem_compl_toExt_iff, mem_union, coe_mem_toExt_iff, coe_mem_compl_toExt_iff, hWB,
      Set.mem_sdiff]
    tauto

/-- **Transport of double connectivity and separation.**  Let `A` be a compact connected set
disjoint from the domain `B`, and `W` continuous and injective on `B ∪ A` with open image `V` whose
complement in `ℂ̄` is connected.  Then `W(B)` is doubly connected, and it separates any two image
points of `A` from any two points of `ℂ̄ ∖ V`. -/
theorem t53_image_sep {B A : Set ℂ} {W : ℂ → ℂ} (hB : IsOpen B) (hBc : IsConnected B)
    (hA : IsCompact A) (hAc : IsConnected A) (hAB : Disjoint B A)
    (hW : ContinuousOn W (B ∪ A)) (hWinj : InjOn W (B ∪ A)) (hWo : IsOpen (W '' (B ∪ A)))
    (hVc : IsConnected (toExt (W '' (B ∪ A)))ᶜ) :
    IsDoublyConnected (W '' B) ∧
      ∀ p ∈ A, ∀ q ∈ A, ∀ P ∈ (toExt (W '' (B ∪ A)))ᶜ, ∀ Q ∈ (toExt (W '' (B ∪ A)))ᶜ,
        SeparatesSets (W '' B) {((W p : ℂ) : ExtPlane), ((W q : ℂ) : ExtPlane)} {P, Q} := by
  have _ := hB
  have hWA_sub : W '' A ⊆ W '' (B ∪ A) := image_mono subset_union_right
  have hWB_eq : W '' B = W '' (B ∪ A) \ W '' A := t53_tc_image_eq_diff hAB hWinj
  have hWAc : IsCompact (W '' A) := hA.image_of_continuousOn (hW.mono subset_union_right)
  have hWAconn : IsConnected (W '' A) := hAc.image W (hW.mono subset_union_right)
  have hWBo : IsOpen (W '' B) := by
    rw [hWB_eq]
    exact hWo.sdiff hWAc.isClosed
  have hWBc : IsConnected (W '' B) := hBc.image W (hW.mono subset_union_left)
  -- the two pieces `K₁ = W(A)` and `K₂ = ℂ̄ ∖ W(B ∪ A)` of `ℂ̄ ∖ W(B)`
  have hK₁c : IsCompact (toExt (W '' A)) := hWAc.image OnePoint.continuous_coe
  have hK₁cl : IsClosed (toExt (W '' A)) := hK₁c.isClosed
  have hK₂cl : IsClosed (toExt (W '' (B ∪ A)))ᶜ := isClosed_compl_toExt hWo
  have hK₁conn : IsConnected (toExt (W '' A)) :=
    hWAconn.image _ OnePoint.continuous_coe.continuousOn
  have hdisj : Disjoint (toExt (W '' A)) (toExt (W '' (B ∪ A)))ᶜ :=
    Set.disjoint_compl_right_iff_subset.2 (image_mono hWA_sub)
  have hcompl : (toExt (W '' B))ᶜ = toExt (W '' A) ∪ (toExt (W '' (B ∪ A)))ᶜ :=
    t53_tc_compl_eq_union hWB_eq
  have hcard : Nat.card (ConnectedComponents ↥(toExt (W '' B))ᶜ) = 2 :=
    t53_tc_card_components_eq_two_of_closed_union hK₁cl hK₂cl hK₁conn hVc hdisj hcompl
  refine ⟨⟨hWBo, hWBc, hcard⟩, ?_⟩
  intro p hp q hq P hP Q hQ
  have hK₁sub : toExt (W '' A) ⊆ (toExt (W '' B))ᶜ := by
    rw [hcompl]
    exact subset_union_left
  have hK₂sub : (toExt (W '' (B ∪ A)))ᶜ ⊆ (toExt (W '' B))ᶜ := by
    rw [hcompl]
    exact subset_union_right
  have hp' : ((W p : ℂ) : ExtPlane) ∈ toExt (W '' A) :=
    mem_image_of_mem _ (mem_image_of_mem W hp)
  have hq' : ((W q : ℂ) : ExtPlane) ∈ toExt (W '' A) :=
    mem_image_of_mem _ (mem_image_of_mem W hq)
  have h1 : toExt (W '' A) ⊆ connectedComponentIn (toExt (W '' B))ᶜ ((W p : ℂ) : ExtPlane) :=
    hK₁conn.isPreconnected.subset_connectedComponentIn hp' hK₁sub
  have h2 : (toExt (W '' (B ∪ A)))ᶜ ⊆ connectedComponentIn (toExt (W '' B))ᶜ P :=
    hVc.isPreconnected.subset_connectedComponentIn hP hK₂sub
  refine ⟨((W p : ℂ) : ExtPlane), hK₁sub hp', P, hK₂sub hP, ?_, ?_, ?_⟩
  · exact insert_subset (h1 hp') (singleton_subset_iff.2 (h1 hq'))
  · exact insert_subset (h2 hP) (singleton_subset_iff.2 (h2 hQ))
  · intro heq
    have hPmem : P ∈ connectedComponentIn (toExt (W '' B))ᶜ ((W p : ℂ) : ExtPlane) := by
      rw [heq]
      exact mem_connectedComponentIn (hK₂sub hP)
    have hpre : IsPreconnected
        (connectedComponentIn (toExt (W '' B))ᶜ ((W p : ℂ) : ExtPlane)) :=
      isPreconnected_connectedComponentIn
    have hsub : connectedComponentIn (toExt (W '' B))ᶜ ((W p : ℂ) : ExtPlane) ⊆
        toExt (W '' A) ∪ (toExt (W '' (B ∪ A)))ᶜ := by
      rw [← hcompl]
      exact connectedComponentIn_subset _ _
    obtain ⟨y, -, hy₁, hy₂⟩ := isPreconnected_closed_iff.1 hpre _ _ hK₁cl hK₂cl hsub
      ⟨_, mem_connectedComponentIn (hK₁sub hp'), hp'⟩ ⟨P, hPmem, hP⟩
    exact Set.disjoint_left.1 hdisj hy₁ hy₂

/-- **Theorem 5.3** (Teichmüller 模定理).  A doubly connected domain separating `{0, z₁}` from
`{z₂, ∞}` satisfies `M(B) ≤ 2 μ(√(|z₁|/(|z₁| + |z₂|)))`. -/
theorem thm5_3_teichmuller_modulus_theorem {z₁ z₂ : ℂ} (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0)
    {B : Set ℂ} (hB : IsDoublyConnected B)
    (hsep : SeparatesSets B {((0 : ℂ) : ExtPlane), (z₁ : ExtPlane)} {(z₂ : ExtPlane), extInf}) :
    dcModulus B ≤ ENNReal.ofReal (2 * grotzschMu (Real.sqrt (‖z₁‖ / (‖z₁‖ + ‖z₂‖)))) := by
  obtain ⟨A, φ, t, hAcpt, hAconn, hAB, h0A, hz₁A, -, hφd, hφinj, hφimg, hφ0, ht0, ht1, hφz₁,
    hkoebe⟩ := t53_riemann_koebe hz₁ hz₂ hB hsep
  obtain ⟨hkd, hkinj⟩ := t53_koebe_scaled_conformal ht0 ht1
  set K : ℂ → ℂ := fun v => -koebeFn v / koebeFn t with hK
  set W : ℂ → ℂ := fun z => K (φ z) with hW
  set R : ℝ := (1 - t) ^ 2 / (4 * t) with hR
  have h1t : 0 < 1 - t := by linarith
  have hR0 : 0 < R := by positivity
  have hmaps : MapsTo φ (B ∪ A) (ball (0 : ℂ) 1) := fun z hz => hφimg ▸ mem_image_of_mem φ hz
  have hWd : DifferentiableOn ℂ W (B ∪ A) := hkd.comp hφd hmaps
  have hWinj : InjOn W (B ∪ A) := hkinj.comp hφinj hmaps
  have hWimg : W '' (B ∪ A) = {w : ℂ | ¬ (w.im = 0 ∧ R ≤ w.re)} := by
    rw [show W '' (B ∪ A) = K '' (φ '' (B ∪ A)) from (image_image K φ (B ∪ A)).symm, hφimg]
    exact t53_koebe_scaled_image ht0 ht1
  have hVo : IsOpen (W '' (B ∪ A)) := by
    rw [hWimg]
    have hc : IsClosed {w : ℂ | w.im = 0 ∧ R ≤ w.re} :=
      (isClosed_eq continuous_im continuous_const).inter (isClosed_le continuous_const continuous_re)
    exact hc.isOpen_compl
  have hVc : IsConnected (toExt (W '' (B ∪ A)))ᶜ := by
    rw [hWimg]
    exact t53_isConnected_compl_slit R
  obtain ⟨hB', hsep'⟩ := t53_image_sep hB.1 hB.2.1 hAcpt hAconn hAB hWd.continuousOn hWinj hVo hVc
  have hk0 : koebeFn (t : ℂ) ≠ 0 := by
    have ht1' : (1 : ℂ) - t ≠ 0 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub]
      exact_mod_cast h1t.ne'
    have ht0' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    exact div_ne_zero ht0' (pow_ne_zero 2 ht1')
  have hW0 : W 0 = 0 := by
    simp only [hW, hK, hφ0, koebeFn, zero_div, neg_zero]
  have hWz₁ : W z₁ = -1 := by
    simp only [hW, hK, hφz₁, neg_div, div_self hk0]
  have hRmem : ((R : ℂ) : ExtPlane) ∈ (toExt (W '' (B ∪ A)))ᶜ := by
    rw [hWimg, coe_mem_compl_toExt_iff]
    simp
  have hsep'' := hsep' z₁ hz₁A 0 h0A _ hRmem extInf (extInf_mem_compl_toExt _)
  rw [hWz₁, hW0] at hsep''
  have hmod : dcModulus B = dcModulus (W '' B) :=
    thm2_2_dcModulus_conformal_invariant hB
      ⟨W, hWd.mono subset_union_left, hWinj.mono subset_union_left, rfl⟩
  rw [hmod]
  refine (thm5_2' hR0 hB' hsep'').trans (ENNReal.ofReal_le_ofReal ?_)
  -- `μ` is decreasing and `|z₁|/(|z₁| + |z₂|) ≤ 1/(1 + R)` by the Koebe estimate
  have ha : 0 < ‖z₁‖ := norm_pos_iff.2 hz₁
  have hb : 0 < ‖z₂‖ := norm_pos_iff.2 hz₂
  have hx0 : 0 < ‖z₁‖ / (‖z₁‖ + ‖z₂‖) := by positivity
  have hx1 : ‖z₁‖ / (‖z₁‖ + ‖z₂‖) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hy0 : 0 < 1 / (1 + R) := by positivity
  have hy1 : 1 / (1 + R) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hxy : ‖z₁‖ / (‖z₁‖ + ‖z₂‖) ≤ 1 / (1 + R) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have hk : ‖z₁‖ * (1 - t) ^ 2 ≤ 4 * ‖z₂‖ * t := by
      have h := mul_le_mul_of_nonneg_right hkoebe (sq_nonneg (1 - t))
      rwa [mul_assoc (4 * ‖z₂‖), div_mul_cancel₀ t (pow_ne_zero 2 h1t.ne')] at h
    have hRt : ‖z₁‖ * R ≤ ‖z₂‖ := by
      rw [hR, mul_div_assoc', div_le_iff₀ (by positivity)]
      linarith
    nlinarith
  have hsx : Real.sqrt (‖z₁‖ / (‖z₁‖ + ‖z₂‖)) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.sqrt_pos.2 hx0, by rw [Real.sqrt_lt' one_pos]; nlinarith⟩
  have hsy : Real.sqrt (1 / (1 + R)) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.sqrt_pos.2 hy0, by rw [Real.sqrt_lt' one_pos]; nlinarith⟩
  have hμ := grotzschMu_strictAntiOn.antitoneOn hsx hsy (Real.sqrt_le_sqrt hxy)
  linarith

/-! ## The Mori problem -/

/-- The arc `Γ_d` of the unit circle, symmetric about the negative real axis, whose chord
(= diameter) has length `d` (`0 < d ≤ 2`). -/
def moriArc (d : ℝ) : Set ℂ :=
  {z : ℂ | ∃ θ : ℝ, |θ| ≤ Real.arcsin (d / 2) ∧ z = -exp (θ * I)}

/-- The Mori domain `G_d = ℂ ∖ ([0, +∞) ∪ Γ_d)`. -/
def moriDomain (d : ℝ) : Set ℂ :=
  ({z : ℂ | z.im = 0 ∧ 0 ≤ z.re} ∪ moriArc d)ᶜ

/-- The Mori condition on a doubly connected `B`: one component of `ℂ̄ ∖ B` contains `0` and
`∞`, and the other component meets the closed unit disc in a set of diameter `≥ d`. -/
def MoriCondition (B : Set ℂ) (d : ℝ) : Prop :=
  ∃ x ∈ (toExt B)ᶜ, {((0 : ℂ) : ExtPlane), extInf} ⊆ connectedComponentIn (toExt B)ᶜ x ∧
    ∃ y ∈ (toExt B)ᶜ, connectedComponentIn (toExt B)ᶜ y ≠ connectedComponentIn (toExt B)ᶜ x ∧
      d ≤ diam ({z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ y} ∩ closedBall 0 1)

/-! ### Mori track interface (coordinator 553e2d) -/

/-- Squaring on `ℂ̄` (`∞ ↦ ∞`). -/
def mo_sqExt (p : ExtPlane) : ExtPlane := OnePoint.elim p extInf (fun z => ((z ^ 2 : ℂ) : ExtPlane))

/-- `mo_sqExt` on a finite point: `z ↦ z²`. -/
theorem mo_mb_sqExt_coe (z : ℂ) : mo_sqExt (z : ExtPlane) = ((z ^ 2 : ℂ) : ExtPlane) := rfl

/-- `mo_sqExt` fixes `∞`. -/
theorem mo_mb_sqExt_infty : mo_sqExt extInf = extInf := rfl

/-- Negation on `ℂ̄` (`∞ ↦ ∞`). -/
def mo_mb_negExt : ExtPlane → ExtPlane := OnePoint.map (fun z : ℂ => -z)

/-- `mo_mb_negExt` on a finite point: `z ↦ -z`. -/
theorem mo_mb_negExt_coe (z : ℂ) : mo_mb_negExt (z : ExtPlane) = ((-z : ℂ) : ExtPlane) := rfl

/-- Negation on `ℂ̄` is an involution. -/
theorem mo_mb_negExt_negExt (p : ExtPlane) : mo_mb_negExt (mo_mb_negExt p) = p := by
  induction p using OnePoint.rec with
  | infty => rfl
  | coe z => rw [mo_mb_negExt_coe, mo_mb_negExt_coe, neg_neg]

/-- Squaring on `ℂ̄` is invariant under negation. -/
theorem mo_mb_sqExt_negExt (p : ExtPlane) : mo_sqExt (mo_mb_negExt p) = mo_sqExt p := by
  induction p using OnePoint.rec with
  | infty => rfl
  | coe z => rw [mo_mb_negExt_coe, mo_mb_sqExt_coe, mo_mb_sqExt_coe, neg_sq]

/-- Negation on `ℂ̄` is continuous. -/
theorem mo_mb_continuous_negExt : Continuous mo_mb_negExt :=
  OnePoint.continuous_map continuous_neg (Homeomorph.neg ℂ).map_coclosedCompact.le

/-- Squaring on `ℂ̄` is continuous. -/
theorem mo_mb_continuous_sqExt : Continuous mo_sqExt := by
  have heq : mo_sqExt = OnePoint.map (fun z : ℂ => z ^ 2) := by
    funext p
    induction p using OnePoint.rec with
    | infty => rfl
    | coe z => rfl
  rw [heq]
  refine OnePoint.continuous_map (continuous_pow 2) ?_
  rw [coclosedCompact_eq_cocompact, ← cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  simp only [norm_pow]
  exact (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop

/-- Squaring on `ℂ̄` is surjective. -/
theorem mo_mb_sqExt_surjective : Function.Surjective mo_sqExt := by
  intro e
  induction e using OnePoint.rec with
  | infty => exact ⟨extInf, rfl⟩
  | coe w =>
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq w (by norm_num : 0 < 2)
    exact ⟨(z : ExtPlane), by rw [mo_mb_sqExt_coe, hz]⟩

/-- The fibres of squaring on `ℂ̄` are `{p, -p}`. -/
theorem mo_mb_sqExt_fiber {p q : ExtPlane} (h : mo_sqExt p = mo_sqExt q) :
    q = p ∨ q = mo_mb_negExt p := by
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec with
    | infty => exact Or.inl rfl
    | coe w =>
      rw [mo_mb_sqExt_infty, mo_mb_sqExt_coe] at h
      exact absurd h.symm (OnePoint.coe_ne_infty _)
  | coe z =>
    induction q using OnePoint.rec with
    | infty =>
      rw [mo_mb_sqExt_infty, mo_mb_sqExt_coe] at h
      exact absurd h (OnePoint.coe_ne_infty _)
    | coe w =>
      rw [mo_mb_sqExt_coe, mo_mb_sqExt_coe] at h
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 (OnePoint.coe_injective h).symm with hw | hw
      · exact Or.inl (by rw [hw])
      · exact Or.inr (by rw [hw, mo_mb_negExt_coe])

/-- `0 ∈ ℂ̄` lies in the squaring preimage of a set containing `0`. -/
theorem mo_mb_zero_mem_preimage {E : Set ExtPlane} (h0 : ((0 : ℂ) : ExtPlane) ∈ E) :
    ((0 : ℂ) : ExtPlane) ∈ mo_sqExt ⁻¹' E := by
  have h2 : ((0 : ℂ) ^ 2 : ℂ) = 0 := by norm_num
  rw [Set.mem_preimage, mo_mb_sqExt_coe, h2]
  exact h0

/-- Key step: if `sq⁻¹(E) ⊆ u ∪ v` with `u, v` closed and disjoint on `sq⁻¹(E)`, `E` preconnected
and `0 ∈ E`, and `0 ∈ u`, then `sq⁻¹(E) ⊆ u` (push the symmetric part `u ∩ -u` down to `E`). -/
theorem mo_mb_subset_of_zero_mem {E : Set ExtPlane} (hE : IsPreconnected E)
    (h0 : ((0 : ℂ) : ExtPlane) ∈ E) {u v : Set ExtPlane} (hu : IsClosed u) (hv : IsClosed v)
    (hYuv : mo_sqExt ⁻¹' E ⊆ u ∪ v) (hYuv0 : mo_sqExt ⁻¹' E ∩ (u ∩ v) = ∅)
    (hu0 : ((0 : ℂ) : ExtPlane) ∈ u) : mo_sqExt ⁻¹' E ⊆ u := by
  have hN : Continuous mo_mb_negExt := mo_mb_continuous_negExt
  have hcl : IsClosedMap mo_sqExt := mo_mb_continuous_sqExt.isClosedMap
  have hbad : ∀ x ∈ mo_sqExt ⁻¹' E, x ∈ u → x ∈ v → False := fun x hx hxu hxv =>
    (Set.eq_empty_iff_forall_notMem.1 hYuv0) x ⟨hx, hxu, hxv⟩
  set P : Set ExtPlane := mo_sqExt '' (u ∩ mo_mb_negExt ⁻¹' u) with hPdef
  set Q : Set ExtPlane := mo_sqExt '' (v ∪ mo_mb_negExt ⁻¹' v) with hQdef
  have hP : IsClosed P := hcl _ (hu.inter (hu.preimage hN))
  have hQ : IsClosed Q := hcl _ (hv.union (hv.preimage hN))
  have hEPQ : E ⊆ P ∪ Q := by
    intro e he
    obtain ⟨p, rfl⟩ := mo_mb_sqExt_surjective e
    have hpY : p ∈ mo_sqExt ⁻¹' E := he
    have hNpY : mo_mb_negExt p ∈ mo_sqExt ⁻¹' E := by
      rw [Set.mem_preimage, mo_mb_sqExt_negExt]
      exact he
    by_cases hpu : p ∈ u ∧ mo_mb_negExt p ∈ u
    · exact Or.inl ⟨p, hpu, rfl⟩
    · refine Or.inr ⟨p, ?_, rfl⟩
      rcases not_and_or.1 hpu with h | h
      · exact Or.inl ((hYuv hpY).resolve_left h)
      · exact Or.inr ((hYuv hNpY).resolve_left h)
  have hEPQ0 : E ∩ (P ∩ Q) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    rintro e ⟨he, ⟨p, ⟨hpu, hNpu⟩, rfl⟩, ⟨q, hq, hqp⟩⟩
    have hpY : p ∈ mo_sqExt ⁻¹' E := he
    have hNpY : mo_mb_negExt p ∈ mo_sqExt ⁻¹' E := by
      rw [Set.mem_preimage, mo_mb_sqExt_negExt]
      exact he
    rcases mo_mb_sqExt_fiber hqp.symm with rfl | rfl
    · rcases hq with h | h
      · exact hbad q hpY hpu h
      · exact hbad (mo_mb_negExt q) hNpY hNpu h
    · rcases hq with h | h
      · exact hbad (mo_mb_negExt p) hNpY hNpu h
      · rw [Set.mem_preimage, mo_mb_negExt_negExt] at h
        exact hbad p hpY hpu h
  rcases isPreconnected_iff_subset_of_disjoint_closed.1 hE P Q hP hQ hEPQ hEPQ0 with hEP | hEQ
  · intro y hy
    obtain ⟨p, ⟨hpu, hNpu⟩, hpy⟩ := hEP hy
    rcases mo_mb_sqExt_fiber hpy with rfl | rfl
    · exact hpu
    · exact hNpu
  · exfalso
    have h0Y : ((0 : ℂ) : ExtPlane) ∈ mo_sqExt ⁻¹' E := mo_mb_zero_mem_preimage h0
    obtain ⟨q, hq, hq0⟩ := hEQ h0
    have hsq0 : mo_sqExt ((0 : ℂ) : ExtPlane) = mo_sqExt q := by
      rw [hq0, mo_mb_sqExt_coe]
      norm_num
    have hq' : q = ((0 : ℂ) : ExtPlane) := by
      rcases mo_mb_sqExt_fiber hsq0 with h | h
      · exact h
      · rw [h, mo_mb_negExt_coe, neg_zero]
    subst hq'
    rcases hq with h | h
    · exact hbad _ h0Y hu0 h
    · rw [Set.mem_preimage, mo_mb_negExt_coe, neg_zero] at h
      exact hbad _ h0Y hu0 h

/-- **Lifting connectedness through `ζ ↦ ζ²`.**  On `ℂ̄`, the preimage under squaring of a
preconnected set containing `0` is preconnected. -/
theorem mo_isPreconnected_sqExt_preimage {E : Set ExtPlane} (hE : IsPreconnected E)
    (h0 : ((0 : ℂ) : ExtPlane) ∈ E) : IsPreconnected (mo_sqExt ⁻¹' E) := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hYuv hYuv0
  rcases hYuv (mo_mb_zero_mem_preimage h0) with hu0 | hv0
  · exact Or.inl (mo_mb_subset_of_zero_mem hE h0 hu hv hYuv hYuv0 hu0)
  · refine Or.inr (mo_mb_subset_of_zero_mem hE h0 hv hu ?_ ?_ hv0)
    · rw [Set.union_comm]
      exact hYuv
    · rw [Set.inter_comm v u]
      exact hYuv0

/-- The diameter of a compact set `K ⊆ ℂ` is attained: if `0 < d ≤ diam K`, then `K` contains two
points at distance `≥ d`. -/
theorem mo_me_exists_far_pair {K : Set ℂ} (hK : IsCompact K) {d : ℝ} (hd₀ : 0 < d)
    (hd : d ≤ Metric.diam K) : ∃ z₁ ∈ K, ∃ z₂ ∈ K, d ≤ ‖z₁ - z₂‖ := by
  have hKne : K.Nonempty := by
    rcases K.eq_empty_or_nonempty with h | h
    · rw [h, Metric.diam_empty] at hd
      linarith
    · exact h
  have hcont : ContinuousOn (fun p : ℂ × ℂ => dist p.1 p.2) (K ×ˢ K) :=
    continuous_dist.continuousOn
  obtain ⟨p, hp, hmax⟩ := (hK.prod hK).exists_isMaxOn (hKne.prod hKne) hcont
  have hle : Metric.diam K ≤ dist p.1 p.2 :=
    Metric.diam_le_of_forall_dist_le dist_nonneg fun x hx y hy =>
      isMaxOn_iff.mp hmax (x, y) (Set.mk_mem_prod hx hy)
  refine ⟨p.1, hp.1, p.2, hp.2, ?_⟩
  rw [← dist_eq_norm]
  linarith

/-- **Extraction from the Mori condition.**  `A` is the component of `ℂ̄ ∖ B` not containing `0, ∞`
(read in `ℂ`); it contains `z₁, z₂` with `|z_j| ≤ 1`, `|z₁ - z₂| ≥ d`; `B ∪ A` is a domain with
connected complement in `ℂ̄`, not containing `0`, on which the identity has a holomorphic square root. -/
theorem mo_extract {d : ℝ} (hd₀ : 0 < d) {B : Set ℂ} (hB : IsDoublyConnected B)
    (hMori : MoriCondition B d) :
    ∃ (A : Set ℂ) (z₁ z₂ : ℂ), IsCompact A ∧ IsConnected A ∧ Disjoint B A ∧ z₁ ∈ A ∧ z₂ ∈ A ∧
      ‖z₁‖ ≤ 1 ∧ ‖z₂‖ ≤ 1 ∧ d ≤ ‖z₁ - z₂‖ ∧ IsOpen (B ∪ A) ∧ IsConnected (B ∪ A) ∧
      IsConnected (toExt (B ∪ A))ᶜ ∧ (0 : ℂ) ∉ B ∪ A ∧
      ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (B ∪ A) ∧ ∀ z ∈ B ∪ A, r z ^ 2 = z := by
  obtain ⟨x, -, hsub, y, hy, hyx, hdiam⟩ := hMori
  have hinf : extInf ∈ (toExt B)ᶜ := extInf_mem_compl_toExt B
  have hxinf : extInf ∈ connectedComponentIn (toExt B)ᶜ x :=
    hsub (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have h0x : ((0 : ℂ) : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ x := hsub (Set.mem_insert _ _)
  have hxeq : connectedComponentIn (toExt B)ᶜ x = connectedComponentIn (toExt B)ᶜ extInf :=
    connectedComponentIn_eq hxinf
  have hne : connectedComponentIn (toExt B)ᶜ y ≠ connectedComponentIn (toExt B)ᶜ extInf := by
    rw [← hxeq]
    exact hyx
  obtain ⟨hAc, hAconn, -, hAB⟩ := isCompact_isConnected_component_ne_extInf hB hy hne
  obtain ⟨hΩo, hΩc, hΩcompl⟩ := fill_component hB hy hne
  set A : Set ℂ := {z : ℂ | (z : ExtPlane) ∈ connectedComponentIn (toExt B)ᶜ y} with hA
  have hC : IsConnected (toExt (B ∪ A))ᶜ := by
    rw [hΩcompl]
    exact isConnected_connectedComponentIn_iff.mpr hinf
  have h0 : (0 : ℂ) ∉ B ∪ A := by
    have h : ((0 : ℂ) : ExtPlane) ∈ (toExt (B ∪ A))ᶜ := by
      rw [hΩcompl, ← hxeq]
      exact h0x
    exact coe_mem_compl_toExt_iff.mp h
  obtain ⟨r, hr, hr2⟩ := hasHolomorphicSqrt_of_isConnected_compl hΩo hΩc hC id differentiableOn_id
    (fun z hz hz0 => h0 ((show z = 0 from hz0) ▸ hz))
  have hK : IsCompact (A ∩ closedBall 0 1) := hAc.inter_right isClosed_closedBall
  obtain ⟨z₁, hz₁, z₂, hz₂, hdz⟩ := mo_me_exists_far_pair hK hd₀ hdiam
  have hn₁ : ‖z₁‖ ≤ 1 := mem_closedBall_zero_iff.mp hz₁.2
  have hn₂ : ‖z₂‖ ≤ 1 := mem_closedBall_zero_iff.mp hz₂.2
  exact ⟨A, z₁, z₂, hAc, hAconn, hAB, hz₁.1, hz₂.1, hn₁, hn₂, hdz, hΩo, hΩc, hC, h0, r, hr,
    fun z hz => hr2 z hz⟩

/-- `mo_sqExt` on a finite point is squaring. -/
theorem mo_mc_sqExt_coe (ζ : ℂ) : mo_sqExt (ζ : ExtPlane) = ((ζ ^ 2 : ℂ) : ExtPlane) := rfl

/-- `mo_sqExt` fixes `∞`. -/
theorem mo_mc_sqExt_infty : mo_sqExt extInf = extInf := rfl

/-- Two preconnected sets `s, t` have preconnected union as soon as a point of `t` lies in the
closure of `s`. -/
theorem mo_mc_isPreconnected_union_of_mem_closure {α : Type*} [TopologicalSpace α] {s t : Set α}
    {q : α} (hs : IsPreconnected s) (ht : IsPreconnected t) (hqs : q ∈ closure s) (hqt : q ∈ t) :
    IsPreconnected (s ∪ t) := by
  have h1 : IsPreconnected (insert q s) :=
    hs.subset_closure (subset_insert q s) (insert_subset hqs subset_closure)
  have h2 : IsPreconnected (insert q s ∪ t) := h1.union q (mem_insert q s) hqt ht
  rwa [insert_union, insert_eq_of_mem (mem_union_right s hqt)] at h2

/-- A nonempty open subset of `ℂ̄` missing `∞` has a closure point outside it (`ℂ̄` is connected). -/
theorem mo_mc_exists_mem_closure_notMem {U : Set ExtPlane} (hU : IsOpen U) (hne : U.Nonempty)
    (hinf : extInf ∉ U) : ∃ q ∈ closure U, q ∉ U := by
  have hne' : U ≠ univ := fun h => hinf (by rw [h]; exact mem_univ _)
  obtain ⟨q, hq⟩ := nonempty_frontier_iff.2 ⟨hne, hne'⟩
  rw [hU.frontier_eq] at hq
  exact ⟨q, hq.1, hq.2⟩

/-- **Open mapping** for an injective holomorphic map on a domain `Ω`: it maps open subsets of `Ω`
onto open sets. -/
theorem mo_mc_isOpen_image {g : ℂ → ℂ} {Ω s : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsConnected Ω)
    (hg : DifferentiableOn ℂ g Ω) (hinj : InjOn g Ω) (hs : s ⊆ Ω) (hso : IsOpen s) :
    IsOpen (g '' s) := by
  rcases (hg.analyticOnNhd hΩ).is_constant_or_isOpen hΩc.isPreconnected with ⟨w, hw⟩ | hopen
  · exfalso
    obtain ⟨z₀, hz₀⟩ := hΩc.nonempty
    have hsub : Ω ⊆ {z₀} := fun z hz => hinj hz hz₀ ((hw z hz).trans (hw z₀ hz₀).symm)
    have heq : Ω = {z₀} := (hΩc.nonempty.subset_singleton_iff).1 hsub
    rw [heq] at hΩ
    exact not_isOpen_singleton z₀ hΩ
  · exact hopen s hs hso

/-- For a square root `r` of the identity on `A`: `ℂ̄ ∖ (r(A) ∪ -r(A))` is the `mo_sqExt`-preimage of
`ℂ̄ ∖ A`. -/
theorem mo_mc_compl_pm_image_eq {A : Set ℂ} {r : ℂ → ℂ} (hr2 : ∀ z ∈ A, r z ^ 2 = z) :
    (toExt (r '' A) ∪ toExt ((fun z => -r z) '' A))ᶜ = mo_sqExt ⁻¹' (toExt A)ᶜ := by
  ext p
  induction p using OnePoint.rec with
  | infty =>
    refine iff_of_true ?_ ?_
    · rintro (h | h) <;> exact extInf_notMem_toExt _ h
    · rw [mem_preimage, mo_mc_sqExt_infty]
      exact extInf_mem_compl_toExt A
  | coe ζ =>
    rw [mem_preimage, mo_mc_sqExt_coe, coe_mem_compl_toExt_iff, mem_compl_iff, mem_union,
      coe_mem_toExt_iff, coe_mem_toExt_iff]
    constructor
    · intro h hA
      apply h
      have hsq := hr2 _ hA
      have hprod : (ζ - r (ζ ^ 2)) * (ζ + r (ζ ^ 2)) = 0 := by linear_combination -hsq
      rcases mul_eq_zero.1 hprod with h1 | h1
      · exact Or.inl ⟨ζ ^ 2, hA, by linear_combination -h1⟩
      · exact Or.inr ⟨ζ ^ 2, hA, by show -r (ζ ^ 2) = ζ; linear_combination -h1⟩
    · rintro hA (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · exact hA (by rw [hr2 a ha]; exact ha)
      · exact hA (by show (-r a) ^ 2 ∈ A; rw [neg_sq, hr2 a ha]; exact ha)

/-- For a square root `r` of the identity on `Ω ∌ 0`: `ℂ̄ ∖ r(Ω)` is the `mo_sqExt`-preimage of
`ℂ̄ ∖ Ω` together with `-r(Ω)`. -/
theorem mo_mc_compl_image_eq {Ω : Set ℂ} {r : ℂ → ℂ} (h0 : (0 : ℂ) ∉ Ω)
    (hr2 : ∀ z ∈ Ω, r z ^ 2 = z) :
    (toExt (r '' Ω))ᶜ = mo_sqExt ⁻¹' (toExt Ω)ᶜ ∪ toExt ((fun z => -r z) '' Ω) := by
  ext p
  induction p using OnePoint.rec with
  | infty =>
    refine iff_of_true (extInf_mem_compl_toExt _) (Or.inl ?_)
    rw [mem_preimage, mo_mc_sqExt_infty]
    exact extInf_mem_compl_toExt Ω
  | coe ζ =>
    rw [mem_union, mem_preimage, mo_mc_sqExt_coe, coe_mem_compl_toExt_iff, coe_mem_compl_toExt_iff,
      coe_mem_toExt_iff]
    constructor
    · intro h
      by_cases hΩ : ζ ^ 2 ∈ Ω
      · right
        have hsq := hr2 _ hΩ
        have hprod : (ζ - r (ζ ^ 2)) * (ζ + r (ζ ^ 2)) = 0 := by linear_combination -hsq
        rcases mul_eq_zero.1 hprod with h1 | h1
        · exact (h ⟨ζ ^ 2, hΩ, by linear_combination -h1⟩).elim
        · exact ⟨ζ ^ 2, hΩ, by show -r (ζ ^ 2) = ζ; linear_combination -h1⟩
      · exact Or.inl hΩ
    · rintro (h | ⟨a, ha, rfl⟩) ⟨ω, hω, hωe⟩
      · exact h (by rw [← hωe, hr2 ω hω]; exact hω)
      · have hωe' : r ω = -r a := hωe
        have hωa : ω = a := by
          linear_combination (-1 : ℂ) * hr2 ω hω + hr2 a ha + (r ω - r a) * hωe'
        rw [hωa] at hωe'
        have hr0 : r a = 0 := by linear_combination hωe' / 2
        have ha0 : a = 0 := by linear_combination -(hr2 a ha) + r a * hr0
        exact h0 (ha0 ▸ ha)

/-- **The √-lift.**  For a holomorphic square root `r` of the identity on `Ω = B ∪ A` (`A` compact,
`0 ∉ Ω`, `ℂ̄ ∖ Ω` connected): the complement of `r(A) ∪ -r(A)` in `ℂ̄` is connected; `r(B)` is open with
`ℂ̄ ∖ r(B) = r(A) ∪ (ℂ̄ ∖ r(Ω))`, where `ℂ̄ ∖ r(Ω)` is closed, connected and contains `-r(A)`. -/
theorem mo_lift_structure {B A : Set ℂ} {r : ℂ → ℂ} (hB : IsOpen B) (hBc : IsConnected B)
    (hA : IsCompact A) (hAc : IsConnected A) (hAB : Disjoint B A) (hΩ : IsOpen (B ∪ A))
    (hΩc : IsConnected (B ∪ A)) (hC : IsConnected (toExt (B ∪ A))ᶜ) (h0 : (0 : ℂ) ∉ B ∪ A)
    (hr : DifferentiableOn ℂ r (B ∪ A)) (hr2 : ∀ z ∈ B ∪ A, r z ^ 2 = z) :
    IsConnected (toExt (r '' A) ∪ toExt ((fun z => -r z) '' A))ᶜ ∧
      IsOpen (toExt (r '' B)) ∧
      (toExt (r '' B))ᶜ = toExt (r '' A) ∪ (toExt (r '' (B ∪ A)))ᶜ ∧
      IsClosed (toExt (r '' (B ∪ A)))ᶜ ∧ IsConnected (toExt (r '' (B ∪ A)))ᶜ ∧
      toExt ((fun z => -r z) '' A) ⊆ (toExt (r '' (B ∪ A)))ᶜ := by
  have hAΩ : A ⊆ B ∪ A := subset_union_right
  have hBΩ : B ⊆ B ∪ A := subset_union_left
  have hrinj : InjOn r (B ∪ A) := fun a ha b hb hab => by
    rw [← hr2 a ha, ← hr2 b hb, hab]
  have hsinj : InjOn (fun z => -r z) (B ∪ A) := fun a ha b hb hab => by
    have hab' : -r a = -r b := hab
    exact hrinj ha hb (neg_inj.1 hab')
  have hsd : DifferentiableOn ℂ (fun z => -r z) (B ∪ A) := hr.neg
  -- open images (open mapping theorem)
  have hrBo : IsOpen (r '' B) := mo_mc_isOpen_image hΩ hΩc hr hrinj hBΩ hB
  have hrΩo : IsOpen (r '' (B ∪ A)) := mo_mc_isOpen_image hΩ hΩc hr hrinj subset_rfl hΩ
  have hsΩo : IsOpen ((fun z => -r z) '' (B ∪ A)) :=
    mo_mc_isOpen_image hΩ hΩc hsd hsinj subset_rfl hΩ
  -- the complement of `r(Ω)`
  have hEq := mo_mc_compl_image_eq h0 hr2
  have hNsub : toExt ((fun z => -r z) '' (B ∪ A)) ⊆ (toExt (r '' (B ∪ A)))ᶜ := by
    rw [hEq]
    exact subset_union_right
  refine ⟨?_, isOpen_toExt_iff.2 hrBo, ?_, isClosed_compl_toExt hrΩo, ?_, ?_⟩
  · -- (a) `ℂ̄ ∖ (r(A) ∪ -r(A))` is the lift of `ℂ̄ ∖ A = B ∪ (ℂ̄ ∖ Ω)`
    rw [mo_mc_compl_pm_image_eq (fun z hz => hr2 z (hAΩ hz))]
    have hsplit : (toExt A)ᶜ = toExt B ∪ (toExt (B ∪ A))ᶜ := by
      ext p
      induction p using OnePoint.rec with
      | infty => exact iff_of_true (extInf_mem_compl_toExt A) (Or.inr (extInf_mem_compl_toExt _))
      | coe z =>
        rw [coe_mem_compl_toExt_iff, mem_union, coe_mem_toExt_iff, coe_mem_compl_toExt_iff]
        constructor
        · intro hz
          by_cases hzB : z ∈ B
          · exact Or.inl hzB
          · exact Or.inr (fun hz' => hz'.elim hzB hz)
        · rintro (hzB | hzΩ) hzA
          · exact Set.disjoint_left.1 hAB hzB hzA
          · exact hzΩ (hAΩ hzA)
    have hBpc : IsPreconnected (toExt B) :=
      hBc.isPreconnected.image _ OnePoint.continuous_coe.continuousOn
    obtain ⟨q, hqcl, hqn⟩ := mo_mc_exists_mem_closure_notMem (isOpen_toExt_iff.2 hΩ)
      ((hAc.nonempty.mono hAΩ).image _) (extInf_notMem_toExt _)
    have hAcl : IsClosed (toExt A) := (hA.image OnePoint.continuous_coe).isClosed
    have hqB : q ∈ closure (toExt B) := by
      rw [toExt_union, closure_union, hAcl.closure_eq] at hqcl
      rcases hqcl with h | h
      · exact h
      · exact (hqn (by rw [toExt_union]; exact Or.inr h)).elim
    have hpre : IsPreconnected (toExt A)ᶜ := by
      rw [hsplit]
      exact mo_mc_isPreconnected_union_of_mem_closure hBpc hC.isPreconnected hqB hqn
    have h0A : ((0 : ℂ) : ExtPlane) ∈ (toExt A)ᶜ :=
      coe_mem_compl_toExt_iff.2 (fun h => h0 (hAΩ h))
    refine ⟨⟨extInf, ?_⟩, mo_isPreconnected_sqExt_preimage hpre h0A⟩
    rw [mem_preimage, mo_mc_sqExt_infty]
    exact extInf_mem_compl_toExt A
  · -- (c) `ℂ̄ ∖ r(B) = r(A) ∪ (ℂ̄ ∖ r(Ω))`
    ext p
    induction p using OnePoint.rec with
    | infty => exact iff_of_true (extInf_mem_compl_toExt _) (Or.inr (extInf_mem_compl_toExt _))
    | coe ζ =>
      rw [coe_mem_compl_toExt_iff, mem_union, coe_mem_toExt_iff, coe_mem_compl_toExt_iff]
      constructor
      · intro h
        by_cases hζ : ζ ∈ r '' (B ∪ A)
        · obtain ⟨ω, hω, rfl⟩ := hζ
          rcases hω with hωB | hωA
          · exact (h ⟨ω, hωB, rfl⟩).elim
          · exact Or.inl ⟨ω, hωA, rfl⟩
        · exact Or.inr hζ
      · rintro (⟨a, ha, rfl⟩ | h) ⟨b, hb, hba⟩
        · have hba' : b = a := hrinj (hBΩ hb) (hAΩ ha) hba
          rw [hba'] at hb
          exact Set.disjoint_left.1 hAB hb ha
        · exact h ⟨b, hBΩ hb, hba⟩
  · -- (e) `ℂ̄ ∖ r(Ω) = (lift of ℂ̄ ∖ Ω) ∪ -r(Ω)` is connected
    have hNpc : IsPreconnected (toExt ((fun z => -r z) '' (B ∪ A))) :=
      (hΩc.isPreconnected.image _ hsd.continuousOn).image _ OnePoint.continuous_coe.continuousOn
    obtain ⟨q, hqcl, hqn⟩ := mo_mc_exists_mem_closure_notMem (isOpen_toExt_iff.2 hsΩo)
      ((hΩc.nonempty.image _).image _) (extInf_notMem_toExt _)
    have hqP : q ∉ toExt (r '' (B ∪ A)) :=
      Set.disjoint_right.1 ((Set.subset_compl_iff_disjoint_right.1 hNsub).symm.closure_right
        (isOpen_toExt_iff.2 hrΩo)) hqcl
    have hqS : q ∈ mo_sqExt ⁻¹' (toExt (B ∪ A))ᶜ := by
      have hq' : q ∈ (toExt (r '' (B ∪ A)))ᶜ := hqP
      rw [hEq] at hq'
      rcases hq' with h | h
      · exact h
      · exact (hqn h).elim
    have hSpc : IsPreconnected (mo_sqExt ⁻¹' (toExt (B ∪ A))ᶜ) :=
      mo_isPreconnected_sqExt_preimage hC.isPreconnected (coe_mem_compl_toExt_iff.2 h0)
    refine ⟨⟨extInf, extInf_mem_compl_toExt _⟩, ?_⟩
    rw [hEq, Set.union_comm (mo_sqExt ⁻¹' (toExt (B ∪ A))ᶜ)]
    exact mo_mc_isPreconnected_union_of_mem_closure hNpc hSpc hqcl hqS
  · -- (f) `-r(A)` misses `r(Ω)`
    intro p hp
    apply hNsub
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hp
    exact ⟨_, ⟨a, hAΩ ha, rfl⟩, rfl⟩

/-- If `∞ ∉ T`, then `T ⊆ ℂ̄` is the image in `ℂ̄` of its finite part `{w : ℂ | w ∈ T}`. -/
theorem mo_md1_toExt_finitePart {T : Set ExtPlane} (hT : extInf ∉ T) :
    toExt {w : ℂ | (w : ExtPlane) ∈ T} = T := by
  ext y
  induction y using OnePoint.rec with
  | infty => exact iff_of_false (extInf_notMem_toExt _) hT
  | coe z => exact coe_mem_toExt_iff

/-- In a union `A ∪ B` of two disjoint closed sets with `A` preconnected, the connected component
of any point of `A` is `A`. -/
theorem mo_md1_connectedComponentIn_union_eq {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) (hAc : IsPreconnected A) (hAB : Disjoint A B) {x : X}
    (hx : x ∈ A) : connectedComponentIn (A ∪ B) x = A := by
  have hsub : connectedComponentIn (A ∪ B) x ⊆ A ∪ B := connectedComponentIn_subset _ _
  refine Subset.antisymm (fun y hy => ?_) (hAc.subset_connectedComponentIn hx subset_union_left)
  by_contra hyA
  have hyB : y ∈ B := Or.resolve_left (hsub hy) hyA
  obtain ⟨z, -, hz₁, hz₂⟩ := isPreconnected_closed_iff.1 isPreconnected_connectedComponentIn _ _
    hA hB hsub ⟨x, mem_connectedComponentIn (subset_union_left hx), hx⟩ ⟨y, hy, hyB⟩
  exact Set.disjoint_left.1 hAB hz₁ hz₂

/-- **Transport of a two-piece complement by a homeomorphism `H` of `ℂ̄`.**  If `S ⊆ ℂ̄` is open and
connected, `∞ ∉ H(S)`, and `ℂ̄ ∖ S = K₁ ∪ K₂` with `K₁, K₂` closed, connected and disjoint, then the
finite part `U` of `H(S)` is doubly connected with `ℂ̄ ∖ U = H(K₁) ∪ H(K₂)`, and these are its components. -/
theorem mo_transport_dc (H : ExtPlane ≃ₜ ExtPlane) {S K₁ K₂ : Set ExtPlane} (hSo : IsOpen S)
    (hSc : IsConnected S) (hinf : extInf ∉ H '' S) (hK : Sᶜ = K₁ ∪ K₂) (hK₁ : IsClosed K₁)
    (hK₂ : IsClosed K₂) (hK₁c : IsConnected K₁) (hK₂c : IsConnected K₂) (hK₁₂ : Disjoint K₁ K₂) :
    IsDoublyConnected {w : ℂ | (w : ExtPlane) ∈ H '' S} ∧
      (toExt {w : ℂ | (w : ExtPlane) ∈ H '' S})ᶜ = H '' K₁ ∪ H '' K₂ ∧
      (∀ x ∈ H '' K₁, connectedComponentIn (toExt {w : ℂ | (w : ExtPlane) ∈ H '' S})ᶜ x = H '' K₁) ∧
      (∀ x ∈ H '' K₂, connectedComponentIn (toExt {w : ℂ | (w : ExtPlane) ∈ H '' S})ᶜ x = H '' K₂) := by
  have hUext : toExt {w : ℂ | (w : ExtPlane) ∈ H '' S} = H '' S := mo_md1_toExt_finitePart hinf
  have hcompl : (toExt {w : ℂ | (w : ExtPlane) ∈ H '' S})ᶜ = H '' K₁ ∪ H '' K₂ := by
    rw [hUext, ← Set.image_compl_eq H.bijective, hK, Set.image_union]
  have hcl₁ : IsClosed (H '' K₁) := H.isClosedMap K₁ hK₁
  have hcl₂ : IsClosed (H '' K₂) := H.isClosedMap K₂ hK₂
  have hc₁ : IsConnected (H '' K₁) := hK₁c.image H H.continuous.continuousOn
  have hc₂ : IsConnected (H '' K₂) := hK₂c.image H H.continuous.continuousOn
  have hd : Disjoint (H '' K₁) (H '' K₂) := (Set.disjoint_image_iff H.injective).2 hK₁₂
  have hUo : IsOpen {w : ℂ | (w : ExtPlane) ∈ H '' S} :=
    (H.isOpenMap S hSo).preimage OnePoint.continuous_coe
  have hHSc : IsConnected (toExt {w : ℂ | (w : ExtPlane) ∈ H '' S}) := by
    rw [hUext]
    exact hSc.image H H.continuous.continuousOn
  have hUc : IsConnected {w : ℂ | (w : ExtPlane) ∈ H '' S} :=
    ⟨hHSc.nonempty.of_image,
      (OnePoint.isOpenEmbedding_coe.isInducing.isPreconnected_image).1 hHSc.isPreconnected⟩
  refine ⟨⟨hUo, hUc, t53_tc_card_components_eq_two_of_closed_union hcl₁ hcl₂ hc₁ hc₂ hd hcompl⟩,
    hcompl, fun x hx => ?_, fun x hx => ?_⟩
  · rw [hcompl]
    exact mo_md1_connectedComponentIn_union_eq hcl₁ hcl₂ hc₁.isPreconnected hd hx
  · rw [hcompl, union_comm]
    exact mo_md1_connectedComponentIn_union_eq hcl₂ hcl₁ hc₂.isPreconnected hd.symm hx

/-- **Separation from a two-piece complement.**  If `ℂ̄ ∖ U = P ∪ Q` with `P, Q` disjoint components,
then `U` separates any nonempty `E₁ ⊆ P` from any nonempty `E₂ ⊆ Q`. -/
theorem mo_separatesSets_of_pieces {U : Set ℂ} {P Q E₁ E₂ : Set ExtPlane}
    (hc : (toExt U)ᶜ = P ∪ Q) (hP : ∀ x ∈ P, connectedComponentIn (toExt U)ᶜ x = P)
    (hQ : ∀ x ∈ Q, connectedComponentIn (toExt U)ᶜ x = Q) (hPQ : Disjoint P Q)
    (hE₁ : E₁ ⊆ P) (hE₂ : E₂ ⊆ Q) (hE₁n : E₁.Nonempty) (hE₂n : E₂.Nonempty) :
    SeparatesSets U E₁ E₂ := by
  obtain ⟨x₁, hx₁⟩ := hE₁n
  obtain ⟨x₂, hx₂⟩ := hE₂n
  have hx₁P : x₁ ∈ P := hE₁ hx₁
  have hx₂Q : x₂ ∈ Q := hE₂ hx₂
  have hx₁U : x₁ ∈ (toExt U)ᶜ := by
    rw [hc]
    exact Set.mem_union_left Q hx₁P
  have hx₂U : x₂ ∈ (toExt U)ᶜ := by
    rw [hc]
    exact Set.mem_union_right P hx₂Q
  refine ⟨x₁, hx₁U, x₂, hx₂U, ?_, ?_, ?_⟩
  · rw [hP x₁ hx₁P]
    exact hE₁
  · rw [hQ x₂ hx₂Q]
    exact hE₂
  · rw [hP x₁ hx₁P, hQ x₂ hx₂Q]
    intro hPQeq
    have hx₁Q : x₁ ∈ Q := by
      rw [← hPQeq]
      exact hx₁P
    exact Set.disjoint_left.1 hPQ hx₁P hx₁Q

/-- **`SeparatesComplement` from two-piece complements.**  If `ℂ̄ ∖ V = P ∪ Q` (components `P, Q`)
and `ℂ̄ ∖ U = P' ∪ Q'` (disjoint components `P', Q'`) with `P ⊆ P'`, `Q ⊆ Q'`, then `U` separates the
two components of `ℂ̄ ∖ V`. -/
theorem mo_separatesComplement_of_pieces {U V : Set ℂ} {P Q P' Q' : Set ExtPlane}
    (hcV : (toExt V)ᶜ = P ∪ Q) (hPV : ∀ x ∈ P, connectedComponentIn (toExt V)ᶜ x = P)
    (hQV : ∀ x ∈ Q, connectedComponentIn (toExt V)ᶜ x = Q)
    (hcU : (toExt U)ᶜ = P' ∪ Q') (hPU : ∀ x ∈ P', connectedComponentIn (toExt U)ᶜ x = P')
    (hQU : ∀ x ∈ Q', connectedComponentIn (toExt U)ᶜ x = Q') (hPQ' : Disjoint P' Q')
    (hPP' : P ⊆ P') (hQQ' : Q ⊆ Q') (hPn : P.Nonempty) (hQn : Q.Nonempty) :
    SeparatesComplement U V := by
  intro x hx y hy hne
  rw [hcV] at hx hy
  rcases hx with hxP | hxQ
  · rcases hy with hyP | hyQ
    · exact absurd ((hPV x hxP).trans (hPV y hyP).symm) hne
    · rw [hPV x hxP, hQV y hyQ]
      exact mo_separatesSets_of_pieces hcU hPU hQU hPQ' hPP' hQQ' hPn hQn
  · rcases hy with hyP | hyQ
    · rw [hQV x hxQ, hPV y hyP]
      have hcU' : (toExt U)ᶜ = Q' ∪ P' := by
        rw [hcU, Set.union_comm]
      exact mo_separatesSets_of_pieces hcU' hQU hPU hPQ'.symm hQQ' hPP' hQn hPn
    · exact absurd ((hQV x hxQ).trans (hQV y hyQ).symm) hne

/-- The finite part of the Möbius image of a pole-free set `S ⊆ ℂ` is its image under the formula. -/
theorem mo_coe_preimage_mobius_image {a b c d : ℂ} (h : a * d - b * c ≠ 0) {S : Set ℂ}
    (hS : ∀ z ∈ S, c * z + d ≠ 0) :
    {w : ℂ | (w : ExtPlane) ∈ mobiusHomeomorph a b c d h '' toExt S} = mobiusFn a b c d '' S := by
  ext w
  constructor
  · rintro ⟨p, hp, hpw⟩
    obtain ⟨z, hz, rfl⟩ := hp
    refine ⟨z, hz, ?_⟩
    rw [mobiusHomeomorph_apply, mobiusExt_coe (hS z hz)] at hpw
    exact OnePoint.coe_injective hpw
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(z : ExtPlane), ⟨z, hz, rfl⟩, ?_⟩
    rw [mobiusHomeomorph_apply, mobiusExt_coe (hS z hz)]

/-- A Möbius transformation is holomorphic and injective on any set avoiding its pole. -/
theorem mo_mobiusFn_diff_inj {a b c d : ℂ} (h : a * d - b * c ≠ 0) {S : Set ℂ}
    (hS : ∀ z ∈ S, c * z + d ≠ 0) :
    DifferentiableOn ℂ (mobiusFn a b c d) S ∧ InjOn (mobiusFn a b c d) S := by
  constructor
  · intro z hz
    have h1 : DifferentiableAt ℂ (fun w : ℂ => a * w + b) z := by fun_prop
    have h2 : DifferentiableAt ℂ (fun w : ℂ => c * w + d) z := by fun_prop
    have h3 : DifferentiableAt ℂ (fun w : ℂ => (a * w + b) / (c * w + d)) z :=
      h1.fun_div h2 (hS z hz)
    exact h3.differentiableWithinAt
  · intro z hz z' hz' hzz'
    calc z = mobiusFn d (-b) (-c) a (mobiusFn a b c d z) := (mobiusFn_inv_apply h (hS z hz)).symm
      _ = mobiusFn d (-b) (-c) a (mobiusFn a b c d z') := by rw [hzz']
      _ = z' := mobiusFn_inv_apply h (hS z' hz')

/-- **(5.14)**: if `|ζ₁|, |ζ₂| ≤ 1` and `|ζ₁² - ζ₂²| ≥ d > 0`, then
`|(ζ₁ + ζ₂)/(ζ₁ - ζ₂)|² ≤ ((2 + √(4 - d²))/d)²`. -/
theorem mo_estimate {d : ℝ} (hd₀ : 0 < d) (hd₂ : d ≤ 2) {ζ₁ ζ₂ : ℂ} (h₁ : ‖ζ₁‖ ≤ 1)
    (h₂ : ‖ζ₂‖ ≤ 1) (hd : d ≤ ‖ζ₁ ^ 2 - ζ₂ ^ 2‖) :
    ‖(ζ₁ + ζ₂) / (ζ₁ - ζ₂)‖ ^ 2 ≤ ((2 + Real.sqrt (4 - d ^ 2)) / d) ^ 2 := by
  rw [norm_div]
  have hs0 : 0 ≤ Real.sqrt (4 - d ^ 2) := Real.sqrt_nonneg _
  have h4 : 0 ≤ 4 - d ^ 2 := by nlinarith
  have hss : Real.sqrt (4 - d ^ 2) ^ 2 = 4 - d ^ 2 := Real.sq_sqrt h4
  have ha0 : 0 ≤ ‖ζ₁ + ζ₂‖ := norm_nonneg _
  have hb0 : 0 ≤ ‖ζ₁ - ζ₂‖ := norm_nonneg _
  have hab : ‖ζ₁ ^ 2 - ζ₂ ^ 2‖ = ‖ζ₁ + ζ₂‖ * ‖ζ₁ - ζ₂‖ := by
    rw [← norm_mul]
    congr 1
    ring
  rw [hab] at hd
  have hbpos : 0 < ‖ζ₁ - ζ₂‖ := by
    rcases hb0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hd
      linarith
  have hpar : ‖ζ₁ + ζ₂‖ ^ 2 + ‖ζ₁ - ζ₂‖ ^ 2 = 2 * (‖ζ₁‖ ^ 2 + ‖ζ₂‖ ^ 2) :=
    parallelogram_law_with_norm ℝ ζ₁ ζ₂
  have hn₁ : ‖ζ₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ζ₁]
  have hn₂ : ‖ζ₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ζ₂]
  have hsum : ‖ζ₁ + ζ₂‖ ^ 2 + ‖ζ₁ - ζ₂‖ ^ 2 ≤ 4 := by linarith
  have hq : d * (‖ζ₁ + ζ₂‖ ^ 2 + ‖ζ₁ - ζ₂‖ ^ 2) ≤ 4 * (‖ζ₁ + ζ₂‖ * ‖ζ₁ - ζ₂‖) := by
    have h1 : d * (‖ζ₁ + ζ₂‖ ^ 2 + ‖ζ₁ - ζ₂‖ ^ 2) ≤
        (‖ζ₁ + ζ₂‖ * ‖ζ₁ - ζ₂‖) * (‖ζ₁ + ζ₂‖ ^ 2 + ‖ζ₁ - ζ₂‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hd (by positivity)
    have h2 : (‖ζ₁ + ζ₂‖ * ‖ζ₁ - ζ₂‖) * (‖ζ₁ + ζ₂‖ ^ 2 + ‖ζ₁ - ζ₂‖ ^ 2) ≤
        (‖ζ₁ + ζ₂‖ * ‖ζ₁ - ζ₂‖) * 4 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    linarith
  have hsq : (d * ‖ζ₁ + ζ₂‖ - 2 * ‖ζ₁ - ζ₂‖) ^ 2 ≤ (Real.sqrt (4 - d ^ 2) * ‖ζ₁ - ζ₂‖) ^ 2 := by
    have h1 : (Real.sqrt (4 - d ^ 2) * ‖ζ₁ - ζ₂‖) ^ 2 = (4 - d ^ 2) * ‖ζ₁ - ζ₂‖ ^ 2 := by
      rw [mul_pow, hss]
    have h2 := mul_le_mul_of_nonneg_left hq hd₀.le
    rw [h1]
    nlinarith [h2]
  have hlin : ‖ζ₁ + ζ₂‖ * d ≤ (2 + Real.sqrt (4 - d ^ 2)) * ‖ζ₁ - ζ₂‖ := by
    have h := (abs_le_of_sq_le_sq' hsq (mul_nonneg hs0 hb0)).2
    linarith
  have hdiv : ‖ζ₁ + ζ₂‖ / ‖ζ₁ - ζ₂‖ ≤ (2 + Real.sqrt (4 - d ^ 2)) / d := by
    rw [div_le_div_iff₀ hbpos hd₀]
    exact hlin
  exact pow_le_pow_left₀ (div_nonneg ha0 hb0) hdiv 2

/-- The Mori radius `d/(2√(2+√(4-d²)))` lies in `(0, 1)` for `0 < d ≤ 2`. -/
theorem mo_radius_mem {d : ℝ} (hd₀ : 0 < d) (hd₂ : d ≤ 2) :
    0 < d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2))) ∧
      d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2))) < 1 := by
  have hs : 0 ≤ Real.sqrt (4 - d ^ 2) := Real.sqrt_nonneg _
  have hu : 1 < Real.sqrt (2 + Real.sqrt (4 - d ^ 2)) := by
    rw [Real.lt_sqrt zero_le_one, one_pow]
    linarith
  have hden : 0 < 2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2)) := by linarith
  refine ⟨div_pos hd₀ hden, ?_⟩
  rw [div_lt_one hden]
  linarith

/-- The monotonicity step of (5.15): for `0 < W ≤ ((2+√(4-d²))/d)²`,
`μ(√(1/(1+W))) ≤ μ(d/(2√(2+√(4-d²))))`. -/
theorem mo_mu_le {d : ℝ} (hd₀ : 0 < d) (hd₂ : d ≤ 2) {W : ℝ} (hW₀ : 0 < W)
    (hW : W ≤ ((2 + Real.sqrt (4 - d ^ 2)) / d) ^ 2) :
    grotzschMu (Real.sqrt (1 / (1 + W))) ≤
      grotzschMu (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2)))) := by
  obtain ⟨hr₀, hr₁⟩ := mo_radius_mem hd₀ hd₂
  have hs0 : 0 ≤ Real.sqrt (4 - d ^ 2) := Real.sqrt_nonneg _
  have h4 : 0 ≤ 4 - d ^ 2 := by nlinarith
  have hss : Real.sqrt (4 - d ^ 2) ^ 2 = 4 - d ^ 2 := Real.sq_sqrt h4
  have huu : Real.sqrt (2 + Real.sqrt (4 - d ^ 2)) ^ 2 = 2 + Real.sqrt (4 - d ^ 2) :=
    Real.sq_sqrt (by linarith)
  have hy0 : 0 < 1 / (1 + W) := by positivity
  have hy1 : 1 / (1 + W) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hsy : Real.sqrt (1 / (1 + W)) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.sqrt_pos.2 hy0, by rw [Real.sqrt_lt' one_pos]; nlinarith⟩
  have hdW : d ^ 2 * W ≤ (2 + Real.sqrt (4 - d ^ 2)) ^ 2 := by
    rw [div_pow, le_div_iff₀ (by positivity)] at hW
    linarith
  have hle : d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2))) ≤ Real.sqrt (1 / (1 + W)) := by
    rw [Real.le_sqrt' hr₀, div_pow, mul_pow, huu,
      div_le_div_iff₀ (by positivity) (by linarith)]
    nlinarith [hdW, hss]
  exact grotzschMu_strictAntiOn.antitoneOn ⟨hr₀, hr₁⟩ hsy hle

/-- `cos (arcsin (d/2)) = √(4 - d²)/2` (valid for every real `d`). -/
theorem mo_ma1_cos_arcsin_half (d : ℝ) :
    Real.cos (Real.arcsin (d / 2)) = Real.sqrt (4 - d ^ 2) / 2 := by
  rw [Real.cos_arcsin]
  have h1 : 1 - (d / 2) ^ 2 = (4 - d ^ 2) / 4 := by ring
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h1, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4), h4]

/-- The Mori arc as a cap of the unit circle: `Γ_d = {|z| = 1, Re z ≤ -√(4-d²)/2}`. -/
theorem mo_moriArc_eq {d : ℝ} (hd₀ : 0 < d) (hd₂ : d ≤ 2) :
    moriArc d = {z : ℂ | ‖z‖ = 1 ∧ z.re ≤ -(Real.sqrt (4 - d ^ 2) / 2)} := by
  have _ := hd₂
  have hα0 : 0 ≤ Real.arcsin (d / 2) := Real.arcsin_nonneg.2 (by positivity)
  have hαpi : Real.arcsin (d / 2) ≤ π :=
    (Real.arcsin_le_pi_div_two _).trans (by linarith [Real.pi_pos])
  have hcosα : Real.cos (Real.arcsin (d / 2)) = Real.sqrt (4 - d ^ 2) / 2 :=
    mo_ma1_cos_arcsin_half d
  ext z
  simp only [moriArc, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    refine ⟨by rw [norm_neg, Complex.norm_exp_ofReal_mul_I], ?_⟩
    rw [Complex.neg_re, Complex.exp_ofReal_mul_I_re, ← hcosα, neg_le_neg_iff, ← Real.cos_abs θ]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ) hαpi hθ
  · rintro ⟨hz1, hzre⟩
    have hz0 : -z ≠ 0 := by
      intro h
      have h' : z = 0 := neg_eq_zero.1 h
      rw [h', norm_zero] at hz1
      exact zero_ne_one hz1
    have hcos : Real.cos (Complex.arg (-z)) = -z.re := by
      rw [Complex.cos_arg hz0, norm_neg, hz1, div_one, Complex.neg_re]
    refine ⟨Complex.arg (-z), not_lt.1 fun hlt => ?_, ?_⟩
    · have h1 : |Complex.arg (-z)| ≤ π :=
        abs_le.2 ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩
      have h2 := Real.cos_lt_cos_of_nonneg_of_le_pi hα0 h1 hlt
      rw [Real.cos_abs, hcos, hcosα] at h2
      linarith
    · have h := Complex.norm_mul_exp_arg_mul_I (-z)
      rw [norm_neg, hz1, Complex.ofReal_one, one_mul] at h
      rw [h, neg_neg]

/-- Restricting a conformal bijection `f : U → V` to `U ∖ K`, where `K` is the part of `U` that `f`
sends into `L`, gives a conformal bijection of `U ∖ K` onto `V ∖ L`. -/
theorem mo_ma2_isConformalOnto_diff {f : ℂ → ℂ} {U V K L : Set ℂ} (hf : IsConformalOnto f U V)
    (hKL : ∀ z ∈ U, f z ∈ L ↔ z ∈ K) : IsConformalOnto f (U \ K) (V \ L) := by
  obtain ⟨hd, hi, hs⟩ := hf
  refine ⟨hd.mono sdiff_subset, hi.mono sdiff_subset, ?_⟩
  ext y
  constructor
  · rintro ⟨z, ⟨hzU, hzK⟩, rfl⟩
    refine ⟨?_, fun h => hzK ((hKL z hzU).1 h)⟩
    rw [← hs]
    exact mem_image_of_mem f hzU
  · rintro ⟨hyV, hyL⟩
    rw [← hs] at hyV
    obtain ⟨z, hzU, rfl⟩ := hyV
    exact ⟨z, ⟨hzU, fun h => hyL ((hKL z hzU).2 h)⟩, rfl⟩

/-- The Cayley-type involution `u ↦ (i - u)/(1 - i u)`, a conformal map of `Δ` onto `ℍ`. -/
def mo_ma2_cay (u : ℂ) : ℂ := (I - u) / (1 - I * u)

/-- The denominator `1 - i u` of `mo_ma2_cay` vanishes only at `u = -i`. -/
theorem mo_ma2_cay_den_ne_zero {u : ℂ} (hu : u ≠ -I) : (1 : ℂ) - I * u ≠ 0 := by
  intro h
  apply hu
  linear_combination I * h + u * I_sq

/-- `mo_ma2_cay` is an involution (off its pole). -/
theorem mo_ma2_cay_cay {u : ℂ} (hu : (1 : ℂ) - I * u ≠ 0) : mo_ma2_cay (mo_ma2_cay u) = u := by
  have hc : mo_ma2_cay u * (1 - I * u) = I - u := div_mul_cancel₀ _ hu
  have hne : (1 : ℂ) - I * mo_ma2_cay u ≠ 0 := by
    apply mo_ma2_cay_den_ne_zero
    intro h
    rw [h] at hc
    have h2 : (2 : ℂ) * I = 0 := by linear_combination -hc + u * I_sq
    exact mul_ne_zero two_ne_zero I_ne_zero h2
  show (I - mo_ma2_cay u) / (1 - I * mo_ma2_cay u) = u
  rw [div_eq_iff hne]
  linear_combination -hc

/-- `mo_ma2_cay` maps the unit disc into the upper half-plane. -/
theorem mo_ma2_cay_im_pos {u : ℂ} (hu : ‖u‖ < 1) : 0 < (mo_ma2_cay u).im := by
  have hne : u ≠ -I := by
    intro h
    rw [h, norm_neg, norm_I] at hu
    exact lt_irrefl _ hu
  have hpos : 0 < normSq (1 - I * u) := normSq_pos.2 (mo_ma2_cay_den_ne_zero hne)
  have hu2 : u.re * u.re + u.im * u.im < 1 := by
    have := normSq_lt_one_iff.2 hu
    rwa [normSq_apply] at this
  have him : (mo_ma2_cay u).im = (1 - u.re * u.re - u.im * u.im) / normSq (1 - I * u) := by
    rw [mo_ma2_cay, div_im]
    simp only [sub_re, sub_im, I_re, I_im, mul_re, mul_im, one_re, one_im]
    field_simp
    ring
  rw [him]
  exact div_pos (by linarith) hpos

/-- `mo_ma2_cay` maps the upper half-plane into the unit disc. -/
theorem mo_ma2_cay_norm_lt_one {ζ : ℂ} (hζ : 0 < ζ.im) : ‖mo_ma2_cay ζ‖ < 1 := by
  have hne : ζ ≠ -I := by
    intro h
    rw [h, neg_im, I_im] at hζ
    linarith
  have hden := mo_ma2_cay_den_ne_zero hne
  rw [← normSq_lt_one_iff, mo_ma2_cay, normSq_div, div_lt_one (normSq_pos.2 hden)]
  simp only [normSq_apply, sub_re, sub_im, I_re, I_im, mul_re, mul_im, one_re, one_im]
  nlinarith

/-- **The Cayley-type map** `u ↦ (i - u)/(1 - i u)` is a conformal map of `Δ` onto `ℍ`. -/
theorem mo_ma2_isConformalOnto_cay : IsConformalOnto mo_ma2_cay unitDisc upperHalf := by
  have hden : ∀ u ∈ unitDisc, (1 : ℂ) - I * u ≠ 0 := fun u hu => by
    apply mo_ma2_cay_den_ne_zero
    intro h
    rw [unitDisc, mem_ball_zero_iff, h, norm_neg, norm_I] at hu
    exact lt_irrefl _ hu
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => I - w) u).div
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 1 - I * w) u)
      (hden u hu)).differentiableWithinAt
  · intro u₁ h₁ u₂ h₂ heq
    rw [← mo_ma2_cay_cay (hden u₁ h₁), ← mo_ma2_cay_cay (hden u₂ h₂), heq]
  · ext ζ
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact mo_ma2_cay_im_pos (mem_ball_zero_iff.1 hu)
    · intro hζ
      have hζ' : 0 < ζ.im := hζ
      refine ⟨mo_ma2_cay ζ, mem_ball_zero_iff.2 (mo_ma2_cay_norm_lt_one hζ'), ?_⟩
      apply mo_ma2_cay_cay
      apply mo_ma2_cay_den_ne_zero
      intro h
      rw [h, neg_im, I_im] at hζ'
      linarith

/-- **Squaring** `ζ ↦ ζ²` maps the upper half-plane conformally onto `ℂ ∖ [0, +∞)`. -/
theorem mo_ma2_isConformalOnto_sq :
    IsConformalOnto (fun ζ : ℂ => ζ ^ 2) upperHalf {z : ℂ | z.im = 0 ∧ 0 ≤ z.re}ᶜ := by
  refine ⟨(differentiable_pow 2).differentiableOn, ?_, ?_⟩
  · intro ζ₁ h₁ ζ₂ h₂ heq
    have h₁' : 0 < ζ₁.im := h₁
    have h₂' : 0 < ζ₂.im := h₂
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 heq with h | h
    · exact h
    · exfalso
      have h' := congrArg Complex.im h
      rw [neg_im] at h'
      linarith
  · ext z
    constructor
    · rintro ⟨ζ, hζ, rfl⟩ ⟨him, hre⟩
      have hζ' : 0 < ζ.im := hζ
      simp only [pow_two, mul_im, mul_re] at him hre
      have hre0 : ζ.re = 0 := by
        have h2 : ζ.re * (2 * ζ.im) = 0 := by linarith
        rcases mul_eq_zero.1 h2 with h | h
        · exact h
        · linarith
      rw [hre0] at hre
      nlinarith
    · intro hz
      have hz' : ¬(z.im = 0 ∧ 0 ≤ z.re) := hz
      set n := ‖z‖ with hn
      have hn2 : n ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        rw [hn, Complex.sq_norm, normSq_apply]
        ring
      have hnre : z.re ≤ n := Complex.re_le_norm z
      have hn0 : 0 ≤ n := norm_nonneg z
      have hpos : 0 < n - z.re := by
        rcases lt_or_eq_of_le hnre with h | h
        · linarith
        · exfalso
          have him2 : z.im ^ 2 = 0 := by rw [h] at hn2; linarith
          have him : z.im = 0 := pow_eq_zero_iff two_ne_zero |>.1 him2
          exact hz' ⟨him, h ▸ hn0⟩
      set b := Real.sqrt ((n - z.re) / 2) with hb
      have hb0 : 0 < b := Real.sqrt_pos.2 (by linarith)
      have hb2 : b ^ 2 = (n - z.re) / 2 := Real.sq_sqrt (by linarith)
      refine ⟨⟨z.im / (2 * b), b⟩, hb0, ?_⟩
      have ha2 : (z.im / (2 * b)) * (z.im / (2 * b)) = (n + z.re) / 2 := by
        rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by norm_num)]
        linear_combination (-4 * (n + z.re)) * hb2 - 2 * hn2
      apply Complex.ext
      · simp only [pow_two, mul_re]
        rw [ha2]
        nlinarith
      · simp only [pow_two, mul_im]
        field_simp
        ring

/-- On `[0, 1)`, `t ↦ 2t/(1+t²)` is strictly increasing: `2t/(1+t²) ≤ 2τ/(1+τ²) ↔ t ≤ τ`. -/
theorem mo_ma2_two_mul_div_le_iff {t τ : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t < 1) (hτ₁ : τ < 1) :
    2 * t / (1 + t ^ 2) ≤ 2 * τ / (1 + τ ^ 2) ↔ t ≤ τ := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 < 1 - t * τ := by nlinarith
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have : 0 < (t - τ) * (1 - t * τ) := mul_pos (by linarith) h1
    nlinarith
  · intro h
    have : 0 ≤ (τ - t) * (1 - t * τ) := mul_nonneg (by linarith) h1.le
    nlinarith

/-- For `0 < r < 1` there is `τ ∈ (0, 1)` with `2τ/(1+τ²) = r`. -/
theorem mo_ma2_exists_tau {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ 2 * τ / (1 + τ ^ 2) = r := by
  have h1r : 0 ≤ 1 - r ^ 2 := by nlinarith
  set s := Real.sqrt (1 - r ^ 2) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - r ^ 2 := Real.sq_sqrt h1r
  refine ⟨r / (1 + s), div_pos hr₀ (by linarith), (div_lt_one (by linarith)).2 (by linarith), ?_⟩
  rw [div_eq_iff (by positivity)]
  field_simp
  linear_combination -hs2

/-- The Mori radius satisfies `r² = (2 - √(4 - d²))/4`. -/
theorem mo_ma2_radius_sq {d : ℝ} (hd₀ : 0 < d) (hd₂ : d ≤ 2) :
    (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2)))) ^ 2 = (2 - Real.sqrt (4 - d ^ 2)) / 4 := by
  have h4 : 0 ≤ 4 - d ^ 2 := by nlinarith
  set c := Real.sqrt (4 - d ^ 2) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c ^ 2 = 4 - d ^ 2 := Real.sq_sqrt h4
  have h2c : 0 < 2 + c := by linarith
  have hs2 : Real.sqrt (2 + c) ^ 2 = 2 + c := Real.sq_sqrt h2c.le
  rw [div_pow, mul_pow, hs2, div_eq_div_iff (by positivity) (by norm_num)]
  linear_combination 4 * hc2

/-- `ζ² ∈ Γ_d` iff `ζ` lies on the unit circle with `|Re ζ| ≤ r`, `r = d/(2√(2+√(4-d²)))`. -/
theorem mo_ma2_sq_mem_moriArc {d : ℝ} (hd₀ : 0 < d) (hd₂ : d ≤ 2) (ζ : ℂ) :
    ζ ^ 2 ∈ moriArc d ↔
      ‖ζ‖ = 1 ∧ |ζ.re| ≤ d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2))) := by
  obtain ⟨hr₀, -⟩ := mo_radius_mem hd₀ hd₂
  have hr2 := mo_ma2_radius_sq hd₀ hd₂
  set r := d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2))) with hr
  have hre2 : (ζ ^ 2).re = ζ.re ^ 2 - ζ.im ^ 2 := by
    simp only [pow_two, mul_re]
  rw [mo_moriArc_eq hd₀ hd₂, mem_ofPred_eq, norm_pow,
    pow_eq_one_iff_of_nonneg (norm_nonneg ζ) two_ne_zero, hre2]
  have hn : ‖ζ‖ = 1 → ζ.re ^ 2 + ζ.im ^ 2 = 1 := fun h1 => by
    have h := Complex.sq_norm ζ
    rw [h1, normSq_apply] at h
    linarith
  constructor
  · rintro ⟨h1, hre⟩
    refine ⟨h1, ?_⟩
    have hn1 := hn h1
    have hsq : ζ.re ^ 2 ≤ r ^ 2 := by nlinarith
    rw [← abs_of_pos hr₀]
    exact sq_le_sq.1 hsq
  · rintro ⟨h1, hre⟩
    refine ⟨h1, ?_⟩
    have hn1 := hn h1
    have hsq : ζ.re ^ 2 ≤ r ^ 2 := sq_le_sq.2 (by rwa [abs_of_pos hr₀])
    nlinarith

/-- For `u ∈ Δ`: `mo_ma2_cay u` lies on the unit circle with `|Re| ≤ 2τ/(1+τ²)` iff `u ∈ [-τ, τ]`. -/
theorem mo_ma2_cay_mem {τ : ℝ} (hτ₁ : τ < 1) {u : ℂ} (hu : ‖u‖ < 1) :
    (‖mo_ma2_cay u‖ = 1 ∧ |(mo_ma2_cay u).re| ≤ 2 * τ / (1 + τ ^ 2)) ↔
      (u.im = 0 ∧ |u.re| ≤ τ) := by
  have hne : u ≠ -I := by
    intro h
    rw [h, norm_neg, norm_I] at hu
    exact lt_irrefl _ hu
  have hden := mo_ma2_cay_den_ne_zero hne
  have hpos : 0 < normSq (1 - I * u) := normSq_pos.2 hden
  have hu2 : u.re * u.re + u.im * u.im < 1 := by
    have := normSq_lt_one_iff.2 hu
    rwa [normSq_apply] at this
  have hnorm : ‖mo_ma2_cay u‖ = 1 ↔ u.im = 0 := by
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, Complex.sq_norm, mo_ma2_cay,
      normSq_div, div_eq_one_iff_eq hpos.ne']
    simp only [normSq_apply, sub_re, sub_im, I_re, I_im, mul_re, mul_im, one_re, one_im]
    constructor
    · intro h
      nlinarith
    · intro h
      rw [h]
      ring
  have hre : u.im = 0 → (mo_ma2_cay u).re = -(2 * u.re) / (1 + u.re ^ 2) := by
    intro h
    have hn : normSq (1 - I * u) = 1 + u.re ^ 2 := by
      rw [normSq_apply]
      simp only [sub_re, sub_im, I_re, I_im, mul_re, mul_im, one_re, one_im, h]
      ring
    rw [mo_ma2_cay, div_re, hn]
    simp only [sub_re, sub_im, I_re, I_im, mul_re, mul_im, one_re, one_im, h]
    have : (1 : ℝ) + u.re ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have habs : u.im = 0 → |(mo_ma2_cay u).re| = 2 * |u.re| / (1 + |u.re| ^ 2) := by
    intro h
    rw [hre h, abs_div, abs_neg, abs_mul, abs_two, sq_abs,
      abs_of_pos (show (0 : ℝ) < 1 + u.re ^ 2 by positivity)]
  have hlt : u.im = 0 → |u.re| < 1 := by
    intro h
    rw [h] at hu2
    have h' : u.re ^ 2 < 1 := by nlinarith
    rw [← abs_one]
    exact sq_lt_sq.1 (by rwa [one_pow])
  constructor
  · rintro ⟨h1, h2⟩
    have him := hnorm.1 h1
    refine ⟨him, ?_⟩
    rw [habs him] at h2
    exact (mo_ma2_two_mul_div_le_iff (abs_nonneg _) (hlt him) hτ₁).1 h2
  · rintro ⟨him, h2⟩
    refine ⟨hnorm.2 him, ?_⟩
    rw [habs him]
    exact (mo_ma2_two_mul_div_le_iff (abs_nonneg _) (hlt him) hτ₁).2 h2

/-- For `w ∈ Δ`: the Blaschke factor `M_τ(w) = (w - τ)/(1 - τ w)` lies in `[-τ, τ]` iff
`w ∈ [0, 2τ/(1+τ²)]`. -/
theorem mo_ma2_blaschke_mem {τ : ℝ} (hτ₀ : 0 < τ) (hτ₁ : τ < 1) {w : ℂ} (hw : ‖w‖ < 1) :
    ((blaschke (τ : ℂ) w).im = 0 ∧ |(blaschke (τ : ℂ) w).re| ≤ τ) ↔
      (w.im = 0 ∧ 0 ≤ w.re ∧ w.re ≤ 2 * τ / (1 + τ ^ 2)) := by
  have hτn : ‖(τ : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ₀]
  have hden := blaschke_den_ne_zero hτn hw
  rw [conj_ofReal] at hden
  have hpos : 0 < normSq (1 - (τ : ℂ) * w) := normSq_pos.2 hden
  have hw2 : w.re * w.re + w.im * w.im < 1 := by
    have := normSq_lt_one_iff.2 hw
    rwa [normSq_apply] at this
  have hb : blaschke (τ : ℂ) w = (w - τ) / (1 - (τ : ℂ) * w) := by
    rw [blaschke, conj_ofReal]
  have him : (blaschke (τ : ℂ) w).im = w.im * (1 - τ ^ 2) / normSq (1 - (τ : ℂ) * w) := by
    rw [hb, div_im]
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, mul_re, mul_im, one_re, one_im]
    field_simp
    ring
  have him0 : (blaschke (τ : ℂ) w).im = 0 ↔ w.im = 0 := by
    rw [him, div_eq_zero_iff, mul_eq_zero]
    have h1 : (1 : ℝ) - τ ^ 2 ≠ 0 := by nlinarith
    constructor
    · rintro ((h | h) | h)
      · exact h
      · exact absurd h h1
      · exact absurd h hpos.ne'
    · intro h
      exact Or.inl (Or.inl h)
  have hx1 : w.im = 0 → 0 < 1 - τ * w.re := by
    intro h
    rw [h] at hw2
    have : w.re * w.re < 1 := by linarith
    have hre1 : w.re < 1 := by nlinarith
    have hre2 : -1 < w.re := by nlinarith
    nlinarith
  have hre : w.im = 0 → (blaschke (τ : ℂ) w).re = (w.re - τ) / (1 - τ * w.re) := by
    intro h
    have hx := (hx1 h).ne'
    have hn : normSq (1 - (τ : ℂ) * w) = (1 - τ * w.re) ^ 2 := by
      rw [normSq_apply]
      simp only [sub_re, sub_im, ofReal_re, ofReal_im, mul_re, mul_im, one_re, one_im, h]
      ring
    rw [hb, div_re, hn]
    simp only [sub_re, sub_im, ofReal_re, ofReal_im, mul_re, mul_im, one_re, one_im, h]
    rw [← add_div, div_eq_div_iff (pow_ne_zero 2 hx) hx]
    ring
  rw [him0]
  constructor
  · rintro ⟨h, h2⟩
    refine ⟨h, ?_⟩
    have hx := hx1 h
    rw [hre h, abs_le, le_div_iff₀ hx, div_le_iff₀ hx] at h2
    obtain ⟨h2a, h2b⟩ := h2
    have hτ2 : 0 < 1 - τ ^ 2 := by nlinarith
    constructor
    · by_contra hneg
      push Not at hneg
      nlinarith
    · rw [le_div_iff₀ (by positivity)]
      nlinarith
  · rintro ⟨h, h2a, h2b⟩
    refine ⟨h, ?_⟩
    have hx := hx1 h
    rw [hre h, abs_le, le_div_iff₀ hx, div_le_iff₀ hx]
    rw [le_div_iff₀ (by positivity)] at h2b
    have hτ2 : 0 < 1 - τ ^ 2 := by nlinarith
    constructor
    · nlinarith
    · nlinarith

/-- **The Mori domain is a Grötzsch domain.**  `B_r`, `r = d/(2√(2+√(4-d²)))`, is conformally
equivalent to `G_d` (explicitly: a disc automorphism, `i·`, the inverse Cayley map `Δ → ℍ`, then `ζ ↦ ζ²`). -/
theorem mo_grotzsch_conformal_mori {d : ℝ} (hd₀ : 0 < d) (hd₂ : d ≤ 2) :
    ConformallyEquivalent (grotzschDomain (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2)))))
      (moriDomain d) := by
  obtain ⟨hr₀, hr₁⟩ := mo_radius_mem hd₀ hd₂
  have hC := mo_ma2_sq_mem_moriArc hd₀ hd₂
  set r := d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2))) with hr
  obtain ⟨τ, hτ₀, hτ₁, hτr⟩ := mo_ma2_exists_tau hr₀ hr₁
  have hτn : ‖(τ : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ₀]
  have hG := (mo_ma2_isConformalOnto_sq.comp mo_ma2_isConformalOnto_cay).comp
    (isConformalOnto_blaschke hτn)
  have hK : ∀ w ∈ unitDisc, (mo_ma2_cay (blaschke (τ : ℂ) w)) ^ 2 ∈ moriArc d ↔
      w ∈ {z : ℂ | z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ r} := by
    intro w hw
    have hwn : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    rw [hC, mem_ofPred_eq, ← hτr, mo_ma2_cay_mem hτ₁ (blaschke_mem_unitDisc hτn hwn),
      mo_ma2_blaschke_mem hτ₀ hτ₁ hwn]
  have hmain := mo_ma2_isConformalOnto_diff hG hK
  have hmd : moriDomain d = {z : ℂ | z.im = 0 ∧ 0 ≤ z.re}ᶜ \ moriArc d := by
    rw [moriDomain, compl_union, Set.sdiff_eq]
  rw [hmd]
  exact ⟨_, hmain⟩

/-- (5.15), stated before `thm5_4_mori` (which uses it): the √-lift `B₁ = T(r(B))`, `B₂ = T(-r(B))` of `B`
sits in the ring `D = T(ℂ̄ ∖ (r(A) ∪ -r(A)))`, so `2M(B) ≤ M(D)` (Theorem 4.11); `T` sends
`r(z₁), -r(z₁), -r(z₂), r(z₂)` to `∞, 0, -1, w₀`, so Theorem 5.3 bounds `M(D)`, and (5.14) bounds `|w₀|`. -/
theorem mo_eq5_15 {d : ℝ} (hd₀ : 0 < d) (hd₂ : d ≤ 2) {B : Set ℂ} (hB : IsDoublyConnected B)
    (hMori : MoriCondition B d) :
    dcModulus B ≤ ENNReal.ofReal (grotzschMu (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2))))) := by
  obtain ⟨A, z₁, z₂, hAc, hAconn, hAB, hz₁A, hz₂A, hz₁n, hz₂n, hdz, hΩo, hΩc, hC, h0, r, hrd, hr2⟩ :=
    mo_extract hd₀ hB hMori
  have hBo : IsOpen B := hB.1
  have hBc : IsConnected B := hB.2.1
  -- the two branches `r` and `s = -r`
  set s : ℂ → ℂ := fun z => -r z with hs
  have hsd : DifferentiableOn ℂ s (B ∪ A) := hrd.neg
  have hs2 : ∀ z ∈ B ∪ A, s z ^ 2 = z := fun z hz => by
    simp only [hs, neg_sq]
    exact hr2 z hz
  have hss : (fun z => -s z) = r := by
    funext z
    simp [hs]
  obtain ⟨hY, hS₁o, hS₁c, hX₁cl, hX₁c, hN₁⟩ :=
    mo_lift_structure hBo hBc hAc hAconn hAB hΩo hΩc hC h0 hrd hr2
  obtain ⟨-, hS₂o, hS₂c, hX₂cl, hX₂c, hN₂⟩ :=
    mo_lift_structure hBo hBc hAc hAconn hAB hΩo hΩc hC h0 hsd hs2
  rw [hss] at hN₂
  -- basic facts about the branches
  have hne0 : ∀ z ∈ B ∪ A, z ≠ 0 := fun z hz hz0 => h0 (hz0 ▸ hz)
  have hrinj : InjOn r (B ∪ A) := fun a ha b hb hab => by
    rw [← hr2 a ha, ← hr2 b hb, hab]
  have hsinj : InjOn s (B ∪ A) := fun a ha b hb hab => by
    rw [← hs2 a ha, ← hs2 b hb, hab]
  have hrs : ∀ a ∈ B ∪ A, ∀ b ∈ B ∪ A, r a ≠ s b := by
    intro a ha b hb hab
    have hab' : a = b := by
      rw [← hr2 a ha, ← hs2 b hb, hab]
    subst hab'
    have h2 : r a = 0 := by
      have : r a = -r a := hab
      linear_combination this / 2
    exact hne0 a ha (by rw [← hr2 a ha, h2]; ring)
  have hAΩ : A ⊆ B ∪ A := subset_union_right
  have hBΩ : B ⊆ B ∪ A := subset_union_left
  have hPAc : IsCompact (r '' A) := hAc.image_of_continuousOn (hrd.continuousOn.mono hAΩ)
  have hNAc : IsCompact (s '' A) := hAc.image_of_continuousOn (hsd.continuousOn.mono hAΩ)
  have hK₁cl : IsClosed (toExt (r '' A)) := (hPAc.image OnePoint.continuous_coe).isClosed
  have hK₂cl : IsClosed (toExt (s '' A)) := (hNAc.image OnePoint.continuous_coe).isClosed
  have hK₁c : IsConnected (toExt (r '' A)) :=
    (hAconn.image r (hrd.continuousOn.mono hAΩ)).image _ OnePoint.continuous_coe.continuousOn
  have hK₂c : IsConnected (toExt (s '' A)) :=
    (hAconn.image s (hsd.continuousOn.mono hAΩ)).image _ OnePoint.continuous_coe.continuousOn
  have hS₁conn : IsConnected (toExt (r '' B)) :=
    (hBc.image r (hrd.continuousOn.mono hBΩ)).image _ OnePoint.continuous_coe.continuousOn
  have hS₂conn : IsConnected (toExt (s '' B)) :=
    (hBc.image s (hsd.continuousOn.mono hBΩ)).image _ OnePoint.continuous_coe.continuousOn
  have hK₁X₁ : Disjoint (toExt (r '' A)) (toExt (r '' (B ∪ A)))ᶜ :=
    Set.disjoint_compl_right_iff_subset.2 (image_mono (image_mono hAΩ))
  have hK₂X₂ : Disjoint (toExt (s '' A)) (toExt (s '' (B ∪ A)))ᶜ :=
    Set.disjoint_compl_right_iff_subset.2 (image_mono (image_mono hAΩ))
  have hK₁K₂ : Disjoint (toExt (r '' A)) (toExt (s '' A)) :=
    Set.disjoint_of_subset_right hN₁ hK₁X₁
  -- the four points
  set ζ₁ : ℂ := r z₁ with hζ₁
  set ζ₂ : ℂ := r z₂ with hζ₂
  have hz₁Ω : z₁ ∈ B ∪ A := hAΩ hz₁A
  have hz₂Ω : z₂ ∈ B ∪ A := hAΩ hz₂A
  have hζ₁0 : ζ₁ ≠ 0 := fun h => hne0 z₁ hz₁Ω (by rw [← hr2 z₁ hz₁Ω, ← hζ₁, h]; ring)
  have hz₁₂ : z₁ ≠ z₂ := fun h => by
    rw [h, sub_self, norm_zero] at hdz
    linarith
  have hζ₁₂ : ζ₁ - ζ₂ ≠ 0 := fun h => hz₁₂ (hrinj hz₁Ω hz₂Ω (sub_eq_zero.1 h))
  have hζp : ζ₁ + ζ₂ ≠ 0 := by
    intro h
    have h' : ζ₂ = s z₁ := by
      simp only [hs, ← hζ₁]
      linear_combination h
    exact hrs z₂ hz₂Ω z₁ hz₁Ω h'
  set c : ℂ := (ζ₁ + ζ₂) / (ζ₁ - ζ₂) with hc
  have hc0 : c ≠ 0 := div_ne_zero hζp hζ₁₂
  have hcζ : c * (ζ₁ - ζ₂) = ζ₁ + ζ₂ := div_mul_cancel₀ _ hζ₁₂
  have hdet : c * -ζ₁ - c * ζ₁ * 1 ≠ 0 := by
    have : c * -ζ₁ - c * ζ₁ * 1 = -2 * c * ζ₁ := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hc0) hζ₁0
  set H : ExtPlane ≃ₜ ExtPlane := mobiusHomeomorph c (c * ζ₁) 1 (-ζ₁) hdet with hH
  have hHapp : ∀ p, H p = mobiusExt c (c * ζ₁) 1 (-ζ₁) p := fun p => rfl
  have hpole : ∀ z : ℂ, 1 * z + -ζ₁ = 0 ↔ z = ζ₁ := fun z => by
    constructor
    · intro h; linear_combination h
    · intro h; rw [h]; ring
  have hHζ₁ : H (ζ₁ : ExtPlane) = extInf := by
    rw [hHapp]
    exact mobiusExt_coe_of_eq_zero ((hpole ζ₁).2 rfl)
  have hHfin : ∀ z : ℂ, z ≠ ζ₁ → H (z : ExtPlane) = ((mobiusFn c (c * ζ₁) 1 (-ζ₁) z : ℂ) : ExtPlane) :=
    fun z hz => by
      rw [hHapp]
      exact mobiusExt_coe (fun h => hz ((hpole z).1 h))
  have hsz₁ : s z₁ = -ζ₁ := rfl
  have hsz₂ : s z₂ = -ζ₂ := rfl
  have hζ₁ne : -ζ₁ ≠ ζ₁ := fun h => hζ₁0 (by linear_combination -h / 2)
  have hζ₂ne' : -ζ₂ ≠ ζ₁ := fun h => hζp (by linear_combination -h)
  have hζ₂ne : ζ₂ ≠ ζ₁ := fun h => hζ₁₂ (by rw [h, sub_self])
  set w₀ : ℂ := -c ^ 2 with hw₀
  have hH0 : H ((s z₁ : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) := by
    rw [hsz₁, hHfin _ hζ₁ne]
    congr 1
    simp only [mobiusFn]
    ring
  have hHm1 : H ((s z₂ : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) := by
    rw [hsz₂, hHfin _ hζ₂ne']
    congr 1
    simp only [mobiusFn]
    have hden : 1 * -ζ₂ + -ζ₁ ≠ 0 := by
      intro h; apply hζp; linear_combination -h
    rw [div_eq_iff hden]
    linear_combination hcζ
  have hHw₀ : H ((ζ₂ : ℂ) : ExtPlane) = ((w₀ : ℂ) : ExtPlane) := by
    rw [hHfin _ hζ₂ne]
    congr 1
    simp only [mobiusFn, hw₀]
    have hden : 1 * ζ₂ + -ζ₁ ≠ 0 := by
      intro h; apply hζ₁₂; linear_combination -h
    rw [div_eq_iff hden]
    linear_combination (-c) * hcζ
  -- the ring `D` and the two lifts
  set S : Set ExtPlane := (toExt (r '' A) ∪ toExt (s '' A))ᶜ with hS
  have hSo : IsOpen S := (hK₁cl.union hK₂cl).isOpen_compl
  have hinfD : extInf ∉ H '' S := by
    rintro ⟨p, hp, hHp⟩
    have hp' : p = (ζ₁ : ExtPlane) := H.injective (hHp.trans hHζ₁.symm)
    exact hp (Or.inl ⟨ζ₁, ⟨z₁, hz₁A, rfl⟩, hp'.symm⟩)
  have hζ₁B : ∀ b ∈ B, r b ≠ ζ₁ := fun b hb h =>
    Set.disjoint_left.1 hAB hb ((hrinj (hBΩ hb) hz₁Ω h) ▸ hz₁A)
  have hζ₁B' : ∀ b ∈ B, s b ≠ ζ₁ := fun b hb h => hrs z₁ hz₁Ω b (hBΩ hb) h.symm
  have hinf₁ : extInf ∉ H '' toExt (r '' B) := by
    rintro ⟨p, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, hHp⟩
    exact hζ₁B b hb (OnePoint.coe_injective (H.injective (hHp.trans hHζ₁.symm)))
  have hinf₂ : extInf ∉ H '' toExt (s '' B) := by
    rintro ⟨p, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, hHp⟩
    exact hζ₁B' b hb (OnePoint.coe_injective (H.injective (hHp.trans hHζ₁.symm)))
  obtain ⟨hDdc, hDc, hDP, hDQ⟩ :=
    mo_transport_dc H hSo hY hinfD (compl_compl _) hK₁cl hK₂cl hK₁c hK₂c hK₁K₂
  obtain ⟨hB₁dc, hB₁c, hB₁P, hB₁Q⟩ :=
    mo_transport_dc H hS₁o hS₁conn hinf₁ hS₁c hK₁cl hX₁cl hK₁c hX₁c hK₁X₁
  obtain ⟨hB₂dc, hB₂c, hB₂P, hB₂Q⟩ :=
    mo_transport_dc H hS₂o hS₂conn hinf₂ hS₂c hK₂cl hX₂cl hK₂c hX₂c hK₂X₂
  set D : Set ℂ := {w : ℂ | (w : ExtPlane) ∈ H '' S} with hD
  set B₁ : Set ℂ := {w : ℂ | (w : ExtPlane) ∈ H '' toExt (r '' B)} with hB₁
  set B₂ : Set ℂ := {w : ℂ | (w : ExtPlane) ∈ H '' toExt (s '' B)} with hB₂
  -- inclusions and disjointness
  have hS₁S : toExt (r '' B) ⊆ S := by
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩ hmem
    rcases hmem with ⟨_, ⟨a, ha, rfl⟩, hpa⟩ | hmem
    · have := hrinj (hAΩ ha) (hBΩ hb) (OnePoint.coe_injective hpa)
      exact Set.disjoint_left.1 hAB hb (this ▸ ha)
    · exact hN₁ hmem ⟨r b, ⟨b, hBΩ hb, rfl⟩, rfl⟩
  have hS₂S : toExt (s '' B) ⊆ S := by
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩ hmem
    rcases hmem with hmem | ⟨_, ⟨a, ha, rfl⟩, hpa⟩
    · exact hN₂ hmem ⟨s b, ⟨b, hBΩ hb, rfl⟩, rfl⟩
    · have := hsinj (hAΩ ha) (hBΩ hb) (OnePoint.coe_injective hpa)
      exact Set.disjoint_left.1 hAB hb (this ▸ ha)
  have hsub₁ : B₁ ⊆ D := fun w hw => image_mono hS₁S hw
  have hsub₂ : B₂ ⊆ D := fun w hw => image_mono hS₂S hw
  have hdisj : Disjoint B₁ B₂ := by
    rw [Set.disjoint_left]
    rintro w ⟨_, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, h₁⟩ ⟨_, ⟨_, ⟨b', hb', rfl⟩, rfl⟩, h₂⟩
    exact hrs b (hBΩ hb) b' (hBΩ hb') (OnePoint.coe_injective (H.injective (h₁.trans h₂.symm)))
  -- separation
  have hHK₁n : (H '' toExt (r '' A)).Nonempty := ⟨_, mem_image_of_mem H ⟨ζ₁, ⟨z₁, hz₁A, rfl⟩, rfl⟩⟩
  have hHK₂n : (H '' toExt (s '' A)).Nonempty := ⟨_, mem_image_of_mem H ⟨s z₁, ⟨z₁, hz₁A, rfl⟩, rfl⟩⟩
  have hsepc₁ : SeparatesComplement B₁ D :=
    mo_separatesComplement_of_pieces hDc hDP hDQ hB₁c hB₁P hB₁Q
      ((Set.disjoint_image_iff H.injective).2 hK₁X₁) subset_rfl (image_mono hN₁) hHK₁n hHK₂n
  have hsepc₂ : SeparatesComplement B₂ D :=
    mo_separatesComplement_of_pieces hDc hDP hDQ (by rw [hB₂c, union_comm]) hB₂Q hB₂P
      ((Set.disjoint_image_iff H.injective).2 hK₂X₂).symm (image_mono hN₂) subset_rfl hHK₁n hHK₂n
  have hsepD : SeparatesSets D {((0 : ℂ) : ExtPlane), ((-1 : ℂ) : ExtPlane)}
      {((w₀ : ℂ) : ExtPlane), extInf} := by
    refine mo_separatesSets_of_pieces (P := H '' toExt (s '' A)) (Q := H '' toExt (r '' A))
      (by rw [hDc, union_comm]) hDQ hDP ((Set.disjoint_image_iff H.injective).2 hK₁K₂).symm ?_ ?_
      ⟨_, mem_insert _ _⟩ ⟨_, mem_insert _ _⟩
    · rintro _ (rfl | rfl)
      · exact ⟨_, ⟨s z₁, ⟨z₁, hz₁A, rfl⟩, rfl⟩, hH0⟩
      · exact ⟨_, ⟨s z₂, ⟨z₂, hz₂A, rfl⟩, rfl⟩, hHm1⟩
    · rintro _ (rfl | rfl)
      · exact ⟨_, ⟨ζ₂, ⟨z₂, hz₂A, rfl⟩, rfl⟩, hHw₀⟩
      · exact ⟨_, ⟨ζ₁, ⟨z₁, hz₁A, rfl⟩, rfl⟩, hHζ₁⟩
  -- the moduli of the lifts
  have hpole₁ : ∀ z ∈ r '' B, (1 : ℂ) * z + -ζ₁ ≠ 0 := by
    rintro _ ⟨b, hb, rfl⟩ h
    exact hζ₁B b hb ((hpole _).1 h)
  have hpole₂ : ∀ z ∈ s '' B, (1 : ℂ) * z + -ζ₁ ≠ 0 := by
    rintro _ ⟨b, hb, rfl⟩ h
    exact hζ₁B' b hb ((hpole _).1 h)
  have hB₁eq : B₁ = (fun z => mobiusFn c (c * ζ₁) 1 (-ζ₁) (r z)) '' B := by
    rw [hB₁, mo_coe_preimage_mobius_image hdet hpole₁, image_image]
  have hB₂eq : B₂ = (fun z => mobiusFn c (c * ζ₁) 1 (-ζ₁) (s z)) '' B := by
    rw [hB₂, mo_coe_preimage_mobius_image hdet hpole₂, image_image]
  have hmod₁ : dcModulus B₁ = dcModulus B := by
    obtain ⟨hmd, hmi⟩ := mo_mobiusFn_diff_inj hdet hpole₁
    refine (thm2_2_dcModulus_conformal_invariant hB ⟨_, ?_, ?_, hB₁eq.symm⟩).symm
    · exact hmd.comp (hrd.mono hBΩ) (mapsTo_image r B)
    · exact hmi.comp (hrinj.mono hBΩ) (mapsTo_image r B)
  have hmod₂ : dcModulus B₂ = dcModulus B := by
    obtain ⟨hmd, hmi⟩ := mo_mobiusFn_diff_inj hdet hpole₂
    refine (thm2_2_dcModulus_conformal_invariant hB ⟨_, ?_, ?_, hB₂eq.symm⟩).symm
    · exact hmd.comp (hsd.mono hBΩ) (mapsTo_image s B)
    · exact hmi.comp (hsinj.mono hBΩ) (mapsTo_image s B)
  -- Theorem 4.11 and Theorem 5.3
  have h411 := thm4_11_dcModulus_subadditive hDdc hB₁dc hB₂dc hsub₁ hsub₂ hdisj hsepc₁ hsepc₂
  rw [hmod₁, hmod₂] at h411
  have hw₀0 : w₀ ≠ 0 := neg_ne_zero.2 (pow_ne_zero 2 hc0)
  have h53 := thm5_3_teichmuller_modulus_theorem (by norm_num : (-1 : ℂ) ≠ 0) hw₀0 hDdc hsepD
  have hnw : ‖w₀‖ = ‖c‖ ^ 2 := by rw [hw₀, norm_neg, norm_pow]
  rw [norm_neg, norm_one, hnw] at h53
  -- (5.14) and the monotonicity of `μ`
  have hζn : ∀ z ∈ B ∪ A, ‖z‖ ≤ 1 → ‖r z‖ ≤ 1 := fun z hz hz1 => by
    have h := hr2 z hz
    have h' : ‖r z‖ ^ 2 ≤ 1 := by rw [← norm_pow, h]; exact hz1
    nlinarith [norm_nonneg (r z)]
  have hest := mo_estimate hd₀ hd₂ (hζn z₁ hz₁Ω hz₁n) (hζn z₂ hz₂Ω hz₂n)
    (by rw [hr2 z₁ hz₁Ω, hr2 z₂ hz₂Ω]; exact hdz)
  have hμ := mo_mu_le hd₀ hd₂ (pow_pos (norm_pos_iff.2 hc0) 2) hest
  set x : ℝ := grotzschMu (Real.sqrt (1 / (1 + ‖c‖ ^ 2))) with hx
  have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
  have h53' : dcModulus D ≤ ENNReal.ofReal x + ENNReal.ofReal x := by
    rw [← ENNReal.ofReal_add hx0 hx0, ← two_mul]
    exact h53
  have h2 : dcModulus B + dcModulus B ≤ ENNReal.ofReal x + ENNReal.ofReal x := h411.trans h53'
  have h3 : dcModulus B ≤ ENNReal.ofReal x :=
    not_lt.1 fun h => absurd h2 (not_le.2 (ENNReal.add_lt_add h h))
  exact h3.trans (ENNReal.ofReal_le_ofReal hμ)

/-- The modulus of the Mori domain, stated before `thm5_4_mori` (which uses it): `G_d` is conformally
equivalent to the Grötzsch domain `B_r`, `r = d/(2√(2+√(4-d²)))`. -/
theorem mo_moriDomain_modulus {d : ℝ} (hd₀ : 0 < d) (hd₂ : d ≤ 2) :
    (dcModulus (moriDomain d)).toReal =
      grotzschMu (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2)))) := by
  obtain ⟨hr₀, hr₁⟩ := mo_radius_mem hd₀ hd₂
  rw [← thm2_2_dcModulus_conformal_invariant (grotzschDomain_doublyConnected hr₀ hr₁).1
    (mo_grotzsch_conformal_mori hd₀ hd₂)]
  rfl

/-- **Theorem 5.4** (Mori 森).  Under the Mori condition, `M(B) ≤ M(G_d)`. -/
theorem thm5_4_mori {d : ℝ} (hd₀ : 0 < d) (hd₂ : d ≤ 2) {B : Set ℂ} (hB : IsDoublyConnected B)
    (hMori : MoriCondition B d) : dcModulus B ≤ dcModulus (moriDomain d) := by
  have h1 := mo_eq5_15 hd₀ hd₂ hB hMori
  have h2 := mo_moriDomain_modulus hd₀ hd₂
  obtain ⟨hr₀, hr₁⟩ := mo_radius_mem hd₀ hd₂
  have hμpos : 0 < grotzschMu (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2)))) := by
    rw [gm_grotzschMu_eq hr₀ hr₁]
    have ha := (scSide_pos hr₀ hr₁).1
    have hb := (scSide_pos hr₀ hr₁).2
    positivity
  have hne : dcModulus (moriDomain d) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at h2
    linarith
  calc dcModulus B ≤ ENNReal.ofReal (grotzschMu (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2))))) := h1
    _ = dcModulus (moriDomain d) := by rw [← h2, ENNReal.ofReal_toReal hne]

/-- (5.15): under the Mori condition, `M(B) ≤ μ(d / (2√(2 + √(4 - d²))))`. -/
theorem eq5_15 {d : ℝ} (hd₀ : 0 < d) (hd₂ : d ≤ 2) {B : Set ℂ} (hB : IsDoublyConnected B)
    (hMori : MoriCondition B d) :
    dcModulus B ≤ ENNReal.ofReal (grotzschMu (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2))))) := by
  exact mo_eq5_15 hd₀ hd₂ hB hMori

/-- The modulus of the Mori domain: `M(G_d) = μ(d / (2√(2 + √(4 - d²))))`. -/
theorem moriDomain_modulus {d : ℝ} (hd₀ : 0 < d) (hd₂ : d ≤ 2) :
    (dcModulus (moriDomain d)).toReal = grotzschMu (d / (2 * Real.sqrt (2 + Real.sqrt (4 - d ^ 2)))) := by
  exact mo_moriDomain_modulus hd₀ hd₂

/-! ## §5.5 The functions `Λ(ρ)` and `μ(r)` -/

/-- (5.16): `Λ(ρ) = M(ℍ(∞, -1, 0, ρ))`. -/
def quadLambda (ρ : ℝ) : ℝ :=
  quadModulusOf upperHalf ![extInf, (((-1 : ℝ) : ℂ) : ExtPlane), ((0 : ℂ) : ExtPlane),
    (((ρ : ℝ) : ℂ) : ExtPlane)]

/-! ### The upper half-plane as a Jordan domain -/

theorem isOpen_upperHalf : IsOpen upperHalf := isOpen_lt continuous_const continuous_im

theorem isConnected_upperHalf : IsConnected upperHalf :=
  ((convex_Ioi (0 : ℝ)).linear_preimage imLm).isConnected ⟨I, by simp⟩

theorem cayley_det : I * 1 - I * (-1) ≠ 0 := by simp

theorem cayley_inv_det : (1 : ℂ) * I - (-I) * 1 ≠ 0 := by simp

/-- The Cayley transform `w ↦ i(1+w)/(1-w)` and its inverse `z ↦ (z-i)/(z+i)`. -/
theorem cayley_apply_inv (v : ExtPlane) :
    mobiusExt I I (-1) 1 (mobiusExt 1 (-I) 1 I v) = v := by
  simpa using mobiusExt_inv_apply cayley_inv_det v

theorem cayley_im {w : ℂ} (hw : ‖w‖ < 1) : 0 < ((I * w + I) / (-1 * w + 1)).im := by
  have hb : (-1 : ℂ) * w + 1 ≠ 0 := by
    intro h
    have h1 : w = 1 := by linear_combination -h
    rw [h1, norm_one] at hw
    exact lt_irrefl _ hw
  have h2 : w.re * w.re + w.im * w.im < 1 := by
    have h := Complex.sq_norm w
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg w]
  rw [Complex.div_im, ← sub_div]
  refine div_pos ?_ (Complex.normSq_pos.2 hb)
  simp only [add_im, mul_im, I_re, I_im, add_re, mul_re, neg_re, one_re, neg_im, one_im]
  nlinarith

/-- The Cayley transform maps the unit disc onto the upper half-plane. -/
theorem cayley_image_disc : mobiusExt I I (-1) 1 '' toExt unitDisc = toExt upperHalf := by
  ext p
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hw' : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
    have hden : (-1 : ℂ) * w + 1 ≠ 0 := by
      intro h
      have h1 : w = 1 := by linear_combination -h
      rw [h1, norm_one] at hw'
      exact lt_irrefl _ hw'
    rw [mobiusExt_coe hden]
    exact ⟨_, cayley_im hw', rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hz' : 0 < z.im := hz
    have hden : (1 : ℂ) * z + I ≠ 0 := by
      intro h
      have h' := congrArg Complex.im h
      simp at h'
      linarith
    refine ⟨mobiusExt 1 (-I) 1 I (z : ExtPlane), ?_, cayley_apply_inv _⟩
    rw [mobiusExt_coe hden]
    refine ⟨_, ?_, rfl⟩
    show ((1 : ℂ) * z + -I) / (1 * z + I) ∈ ball (0 : ℂ) 1
    rw [mem_ball_zero_iff, norm_div, div_lt_one (norm_pos_iff.2 hden),
      ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [add_re, add_im, mul_re, mul_im, one_re, one_im, I_re, I_im, neg_re, neg_im]
    nlinarith

/-! ### The Cayley transform as a conformal map of plane domains

`cayley_image_disc` above states the Cayley correspondence in `ℂ̄` terms, as an image of
`toExt unitDisc` under `mobiusExt`.  The Poincaré metric of §14 needs it instead as an
`IsConformalOnto` between plain subsets of `ℂ`, and in the other direction, so the maps are
repackaged here as honest functions `ℂ → ℂ`. -/

/-- The Cayley transform `C(z) = (z - i)/(z + i)`, which maps the upper half-plane conformally
onto the unit disc. -/
def cayley (z : ℂ) : ℂ := (z - I) / (z + I)

/-- The inverse Cayley transform `C⁻¹(w) = i(1 + w)/(1 - w)`. -/
def cayleyInv (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

/-- `|z + i|² - |z - i|² = 4 Im z`: the Cayley transform contracts exactly on the upper
half-plane. -/
theorem normSq_cayley_key (z : ℂ) : normSq (z + I) - normSq (z - I) = 4 * z.im := by
  simp only [normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.I_re, Complex.I_im]
  ring

theorem cayley_den_ne_zero {z : ℂ} (hz : 0 < z.im) : z + I ≠ 0 := by
  intro hcon
  have him := congrArg Complex.im hcon
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
  linarith

theorem cayley_mem_unitDisc {z : ℂ} (hz : 0 < z.im) : cayley z ∈ unitDisc := by
  have hden := cayley_den_ne_zero hz
  have hpos : 0 < normSq (z + I) := normSq_pos.mpr hden
  have hlt : normSq (z - I) < normSq (z + I) := by
    have h := normSq_cayley_key z
    linarith
  rw [unitDisc, mem_ball_zero_iff, ← normSq_lt_one_iff, cayley, normSq_div, div_lt_one hpos]
  exact hlt

theorem cayleyInv_den_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : (1 : ℂ) - w ≠ 0 := by
  intro hcon
  rw [show w = 1 by linear_combination -hcon] at hw
  simp at hw

theorem cayleyInv_mem_upperHalf {w : ℂ} (hw : ‖w‖ < 1) : cayleyInv w ∈ upperHalf := by
  have hden := cayleyInv_den_ne_zero hw
  have hpos : 0 < normSq (1 - w) := normSq_pos.mpr hden
  have hws : normSq w < 1 := normSq_lt_one_iff.mpr hw
  have hval : (cayleyInv w).im = (1 - normSq w) / normSq (1 - w) := by
    rw [cayleyInv, Complex.div_im]
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
      normSq_apply]
    field_simp
    ring
  show 0 < (cayleyInv w).im
  rw [hval]
  exact div_pos (by linarith) hpos

theorem cayley_cayleyInv {w : ℂ} (hw : ‖w‖ < 1) : cayley (cayleyInv w) = w := by
  have hden := cayleyInv_den_ne_zero hw
  have h1 : cayleyInv w - I = I * (2 * w) / (1 - w) := by
    rw [cayleyInv]; field_simp; ring
  have h2 : cayleyInv w + I = I * 2 / (1 - w) := by
    rw [cayleyInv]; field_simp; ring
  have h2ne : cayleyInv w + I ≠ 0 := by
    rw [h2]
    exact div_ne_zero (by simp) hden
  rw [cayley, div_eq_iff h2ne, h1, h2]
  field_simp

theorem cayleyInv_cayley {z : ℂ} (hz : 0 < z.im) : cayleyInv (cayley z) = z := by
  have hden := cayley_den_ne_zero hz
  have h1 : (1 : ℂ) + cayley z = 2 * z / (z + I) := by
    rw [cayley]; field_simp; ring
  have h2 : (1 : ℂ) - cayley z = 2 * I / (z + I) := by
    rw [cayley]; field_simp; ring
  have h2ne : (1 : ℂ) - cayley z ≠ 0 := by
    rw [h2]
    exact div_ne_zero (by simp) hden
  rw [cayleyInv, div_eq_iff h2ne, h1, h2]
  field_simp

/-- **The Cayley transform maps the upper half-plane conformally onto the unit disc.** -/
theorem isConformalOnto_cayley : IsConformalOnto cayley upperHalf unitDisc := by
  refine ⟨fun z hz => ?_, fun z₁ h₁ z₂ h₂ heq => ?_, ?_⟩
  · exact ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => v - I) z).div
      (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => v + I) z)
      (cayley_den_ne_zero hz)).differentiableWithinAt
  · rw [← cayleyInv_cayley h₁, ← cayleyInv_cayley h₂, heq]
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact cayley_mem_unitDisc hz
    · intro hw
      exact ⟨cayleyInv w, cayleyInv_mem_upperHalf (mem_ball_zero_iff.mp hw),
        cayley_cayleyInv (mem_ball_zero_iff.mp hw)⟩

/-- The boundary of `ℍ` in `ℂ̄` is the Cayley image of the unit circle. -/
theorem frontier_toExt_upperHalf :
    frontier (toExt upperHalf) = mobiusExt I I (-1) 1 '' toExt (sphere (0 : ℂ) 1) := by
  rw [← cayley_image_disc,
    show mobiusExt I I (-1) 1 = ⇑(mobiusHomeomorph I I (-1) 1 cayley_det) from rfl,
    ← (mobiusHomeomorph I I (-1) 1 cayley_det).image_frontier,
    unitDisc, frontier_toExt_of_isBounded Metric.isBounded_ball isOpen_ball,
    frontier_ball 0 one_ne_zero]

theorem isJordanCurve_frontier_upperHalf : IsJordanCurve (frontier (toExt upperHalf)) := by
  refine ⟨fun w => mobiusHomeomorph I I (-1) 1 cayley_det ((w : ℂ) : ExtPlane), ?_, ?_, ?_⟩
  · exact (mobiusHomeomorph I I (-1) 1 cayley_det).continuous.comp
      (OnePoint.continuous_coe.comp continuous_subtype_val)
  · intro w₁ w₂ h
    exact Subtype.ext
      (OnePoint.coe_injective ((mobiusHomeomorph I I (-1) 1 cayley_det).injective h))
  · rw [frontier_toExt_upperHalf]
    ext p
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨_, ⟨(w : ℂ), w.2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩

theorem isJordanDomain_upperHalf : IsJordanDomain upperHalf :=
  ⟨isOpen_upperHalf, isConnected_upperHalf, isJordanCurve_frontier_upperHalf⟩

theorem mem_frontier_upperHalf_of_inv {v : ExtPlane}
    (hv : mobiusExt 1 (-I) 1 I v ∈ toExt (sphere (0 : ℂ) 1)) :
    v ∈ frontier (toExt upperHalf) := by
  rw [frontier_toExt_upperHalf, ← cayley_apply_inv v]
  exact mem_image_of_mem _ hv

theorem infty_mem_frontier_upperHalf : extInf ∈ frontier (toExt upperHalf) := by
  apply mem_frontier_upperHalf_of_inv
  rw [mobiusExt_infty_of_ne one_ne_zero, div_one]
  exact ⟨1, by simp, rfl⟩

theorem ofReal_mem_frontier_upperHalf (t : ℝ) :
    ((t : ℂ) : ExtPlane) ∈ frontier (toExt upperHalf) := by
  apply mem_frontier_upperHalf_of_inv
  have hne : (t : ℂ) + I ≠ 0 := fun h => by simpa using congrArg Complex.im h
  have hden : (1 : ℂ) * t + I ≠ 0 := by rwa [one_mul]
  rw [mobiusExt_coe hden]
  refine ⟨_, ?_, rfl⟩
  have h1 : ‖(t : ℂ) - I‖ = ‖(t : ℂ) + I‖ := by
    rw [← norm_conj ((t : ℂ) + I)]
    congr 1
    simp [sub_eq_add_neg]
  rw [mem_sphere_zero_iff_norm,
    show mobiusFn 1 (-I) 1 I (t : ℂ) = ((t : ℂ) - I) / ((t : ℂ) + I) by
      simp [mobiusFn, sub_eq_add_neg],
    norm_div, h1, div_self (norm_ne_zero_iff.2 hne)]

/-- The identity is its own boundary extension. -/
theorem isHomeoExtension_id (U : Set ℂ) : IsHomeoExtension id U U id :=
  ⟨fun _ _ => rfl, continuousOn_id, injOn_id _, image_id _⟩

/-- `ℍ(∞, -1, 0, ρ)` is a topological quadrilateral for `ρ > 0` (the Möbius map `z ↦ -1/(z+2)`
sends the vertices to `0, -1, -1/2, -1/(ρ+2)`). -/
theorem isTopQuad_upperHalf_lambda {ρ : ℝ} (hρ : 0 < ρ) :
    IsTopQuad upperHalf ![extInf, (((-1 : ℝ) : ℂ) : ExtPlane), ((0 : ℂ) : ExtPlane),
      (((ρ : ℝ) : ℂ) : ExtPlane)] := by
  refine ⟨isJordanDomain_upperHalf, fun i => ?_, ?_⟩
  · fin_cases i
    · exact infty_mem_frontier_upperHalf
    · exact ofReal_mem_frontier_upperHalf (-1)
    · simpa using ofReal_mem_frontier_upperHalf 0
    · exact ofReal_mem_frontier_upperHalf ρ
  · have hdet : (0 : ℝ) < 0 * 2 - (-1) * 1 := by norm_num
    have hS' : ((0 : ℝ) : ℂ) * ((2 : ℝ) : ℂ) - ((-1 : ℝ) : ℂ) * ((1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hdet.ne'
    set e := mobiusHomeomorph ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((2 : ℝ) : ℂ) hS'
      with he
    have heS : ∀ w ∈ upperHalf, e (w : ExtPlane) =
        ((mobiusFn ((0 : ℝ) : ℂ) ((-1 : ℝ) : ℂ) ((1 : ℝ) : ℂ) ((2 : ℝ) : ℂ) w : ℂ) : ExtPlane) :=
      fun w hw => by
        rw [he, mobiusHomeomorph_apply]
        exact mobiusExt_coe (mobiusFn_den_ne_zero_real hdet.ne' hw)
    have himgS : e '' toExt upperHalf = toExt upperHalf := by
      rw [he]
      exact mobiusExt_image_toExt_upperHalf hdet
    have h2 : (-1 / 2 : ℝ) < -1 / (ρ + 2) := by
      rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
      linarith
    have h3 : (-1 / (ρ + 2) : ℝ) < 0 := div_neg_of_neg_of_pos (by norm_num) (by linarith)
    refine ⟨_, _, ![0, -1, -1 / 2, -1 / (ρ + 2)],
      (isConformalOnto_mobius_upperHalf hdet).comp (isConformalOnto_id upperHalf),
      (isHomeoExtension_id upperHalf).comp_homeomorph (isConformalOnto_id upperHalf).mapsTo e
        heS himgS, ⟨1, Fin.strictMono_iff_lt_succ.2 fun i => ?_⟩, fun i => ?_⟩
    · fin_cases i
      · show (-1 : ℝ) < -1 / 2
        norm_num
      · exact h2
      · exact h3
    · fin_cases i
      · show e extInf = (((0 : ℝ) : ℂ) : ExtPlane)
        rw [he, mobiusHomeomorph_apply, mobiusExt_ofReal_infty one_ne_zero]
        norm_num
      · show e (((-1 : ℝ) : ℂ) : ExtPlane) = (((-1 : ℝ) : ℂ) : ExtPlane)
        rw [he, mobiusHomeomorph_apply, mobiusExt_ofReal_coe (by norm_num)]
        norm_num
      · show e ((0 : ℂ) : ExtPlane) = (((-1 / 2 : ℝ) : ℂ) : ExtPlane)
        rw [he, mobiusHomeomorph_apply, ← ofReal_zero, mobiusExt_ofReal_coe (by norm_num)]
        norm_num
      · show e (((ρ : ℝ) : ℂ) : ExtPlane) = (((-1 / (ρ + 2) : ℝ) : ℂ) : ExtPlane)
        rw [he, mobiusHomeomorph_apply, mobiusExt_ofReal_coe (ne_of_gt (by linarith))]
        congr 2
        ring

/-- The Schwarz–Christoffel half-plane quadrilateral `ℍ(-1/k, -1, 1, 1/k)` (`0 < k < 1`) of
`thm1_1_elliptic_modulus` is a topological quadrilateral: take the identity map of `ℍ`, the
prevertices `-1/k < -1 < 1 < 1/k` being increasing. -/
theorem lam_e517_isTopQuad_sc {k : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) :
    IsTopQuad upperHalf ![(((-1 / k : ℝ) : ℂ) : ExtPlane), (((-1 : ℝ) : ℂ) : ExtPlane),
      (((1 : ℝ) : ℂ) : ExtPlane), (((1 / k : ℝ) : ℂ) : ExtPlane)] := by
  refine ⟨isJordanDomain_upperHalf, fun i => ?_, id, id, scPrevertex k,
    ⟨differentiableOn_id, injOn_id _, image_id _⟩, isHomeoExtension_id upperHalf, ⟨0, ?_⟩,
    fun i => ?_⟩
  · fin_cases i <;> exact ofReal_mem_frontier_upperHalf _
  · simpa using scPrevertex_strictMono hk₀ hk₁
  · fin_cases i <;> rfl

/-- For `0 < k < 1`, `ρ > 0` and `ρ (1-k)² = 4k`: `Λ(ρ) = b_k / a_k` (`scSideB k / scSideA k`).
The real Möbius map `z ↦ (-(1-k) z - 2)/((1-k) z - 2k)` (determinant `2(1-k²) > 0`) sends
`∞, -1, 0, ρ` to `-1, 1, 1/k, -1/k`, i.e. `ℍ(∞, -1, 0, ρ)` conformally onto the rotation
`ℍ(-1, 1, 1/k, -1/k)` of the quadrilateral `ℍ(-1/k, -1, 1, 1/k)`, whose modulus is `a_k / b_k`
(`thm1_1_elliptic_modulus`); conclude by Theorems 1.3 and 1.2. -/
theorem lam_e517_quadLambda_eq {k ρ : ℝ} (hk₀ : 0 < k) (hk₁ : k < 1) (hρ : 0 < ρ)
    (hρk : ρ * (1 - k) ^ 2 = 4 * k) : quadLambda ρ = scSideB k / scSideA k := by
  set Q : TopQuad := ⟨upperHalf, _, isTopQuad_upperHalf_lambda hρ⟩
  set P : TopQuad := ⟨upperHalf, _, lam_e517_isTopQuad_sc hk₀ hk₁⟩
  have hconf : Q.ConfEquiv P.rotate := by
    have hdet : (0 : ℝ) < (-(1 - k)) * (-2 * k) - (-2) * (1 - k) := by nlinarith
    have hS' : ((-(1 - k) : ℝ) : ℂ) * ((-2 * k : ℝ) : ℂ) -
        ((-2 : ℝ) : ℂ) * ((1 - k : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hdet.ne'
    set e := mobiusHomeomorph ((-(1 - k) : ℝ) : ℂ) ((-2 : ℝ) : ℂ) ((1 - k : ℝ) : ℂ)
      ((-2 * k : ℝ) : ℂ) hS' with he
    have heS : ∀ w ∈ upperHalf, e (w : ExtPlane) = ((mobiusFn ((-(1 - k) : ℝ) : ℂ)
        ((-2 : ℝ) : ℂ) ((1 - k : ℝ) : ℂ) ((-2 * k : ℝ) : ℂ) w : ℂ) : ExtPlane) :=
      fun w hw => by
        rw [he, mobiusHomeomorph_apply]
        exact mobiusExt_coe (mobiusFn_den_ne_zero_real hdet.ne' hw)
    have himgS : e '' toExt upperHalf = toExt upperHalf := by
      rw [he]
      exact mobiusExt_image_toExt_upperHalf hdet
    refine ⟨_, _, (isConformalOnto_mobius_upperHalf hdet).comp (isConformalOnto_id upperHalf),
      (isHomeoExtension_id upperHalf).comp_homeomorph (isConformalOnto_id upperHalf).mapsTo e
        heS himgS, fun i => ?_⟩
    fin_cases i
    · show e extInf = (((-1 : ℝ) : ℂ) : ExtPlane)
      rw [he, mobiusHomeomorph_apply, mobiusExt_ofReal_infty (sub_pos.2 hk₁).ne']
      congr 2
      rw [div_eq_iff (sub_pos.2 hk₁).ne']
      ring
    · show e (((-1 : ℝ) : ℂ) : ExtPlane) = (((1 : ℝ) : ℂ) : ExtPlane)
      have hden : (1 - k) * (-1) + -2 * k ≠ 0 := by nlinarith
      rw [he, mobiusHomeomorph_apply, mobiusExt_ofReal_coe hden]
      congr 2
      rw [div_eq_one_iff_eq hden]
      ring
    · show e ((0 : ℂ) : ExtPlane) = (((1 / k : ℝ) : ℂ) : ExtPlane)
      have hden : (1 - k) * 0 + -2 * k ≠ 0 := by nlinarith
      rw [he, mobiusHomeomorph_apply, ← ofReal_zero, mobiusExt_ofReal_coe hden]
      congr 2
      rw [div_eq_div_iff hden hk₀.ne']
      ring
    · show e (((ρ : ℝ) : ℂ) : ExtPlane) = (((-1 / k : ℝ) : ℂ) : ExtPlane)
      have hden : (1 - k) * ρ + -2 * k ≠ 0 := by nlinarith
      rw [he, mobiusHomeomorph_apply, mobiusExt_ofReal_coe hden]
      congr 2
      rw [div_eq_div_iff hden hk₀.ne']
      linear_combination hρk
  have hPmod : P.modulus = scSideA k / scSideB k := thm1_1_elliptic_modulus hk₀ hk₁
  have hrot := thm1_2_modulus_rotate P
  have ha := (scSide_pos hk₀ hk₁).1
  have hb := (scSide_pos hk₀ hk₁).2
  have hm := modulus_pos P.rotate
  have h1 : quadLambda ρ = Q.modulus := rfl
  rw [h1, thm1_3_modulus_conformal_invariant hconf]
  rw [hPmod, div_eq_div_iff hb.ne' hm.ne'] at hrot
  rw [eq_div_iff ha.ne']
  linear_combination hrot

/-- (5.17): `Λ(ρ) = M(T_ρ)/π`. -/
theorem eq5_17 {ρ : ℝ} (hρ : 0 < ρ) :
    quadLambda ρ = (dcModulus (teichmullerDomain ρ)).toReal / π := by
  have hk₀ := tzK_pos hρ
  have hk₁ := tzK_lt_one hρ
  have ha := (scSide_pos hk₀ hk₁).1
  have hb := (scSide_pos hk₀ hk₁).2
  have hρk : ρ * (1 - tzK ρ) ^ 2 = 4 * tzK ρ :=
    (eq_div_iff (pow_ne_zero 2 (sub_pos.2 hk₁).ne')).1 (tzR_eq hρ)
  rw [lam_e517_quadLambda_eq hk₀ hk₁ hρ hρk, tz_dcModulus_teichmullerDomain hρ,
    ENNReal.toReal_ofReal (by positivity)]
  field_simp

/-- (5.18): `Λ(ρ) = (2/π) μ(√(1/(1+ρ)))`. -/
theorem eq5_18 {ρ : ℝ} (hρ : 0 < ρ) :
    quadLambda ρ = 2 / π * grotzschMu (Real.sqrt (1 / (1 + ρ))) := by
  rw [eq5_17 hρ, eq5_7 hρ]
  ring

/-- (5.19): `μ(√(1/(1+ρ))) · μ(√(ρ/(1+ρ))) = π²/4`. -/
theorem eq5_19 {ρ : ℝ} (hρ : 0 < ρ) :
    grotzschMu (Real.sqrt (1 / (1 + ρ))) * grotzschMu (Real.sqrt (ρ / (1 + ρ))) = π ^ 2 / 4 := by
  have h1ρ : (0 : ℝ) < 1 + ρ := by linarith
  have hr₀ : 0 < Real.sqrt (1 / (1 + ρ)) := Real.sqrt_pos.2 (by positivity)
  have hr₁ : Real.sqrt (1 / (1 + ρ)) < 1 := by
    rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one h1ρ]
    linarith
  have hs₀ : 0 < Real.sqrt (ρ / (1 + ρ)) := Real.sqrt_pos.2 (by positivity)
  have hs₁ : Real.sqrt (ρ / (1 + ρ)) < 1 := by
    rw [Real.sqrt_lt' one_pos, one_pow, div_lt_one h1ρ]
    linarith
  -- the two moduli are complementary: `r² + r'² = 1`
  have hrs : Real.sqrt (1 - Real.sqrt (1 / (1 + ρ)) ^ 2) = Real.sqrt (ρ / (1 + ρ)) := by
    rw [Real.sq_sqrt (by positivity)]
    congr 1
    field_simp
    ring
  have hsr : Real.sqrt (1 - Real.sqrt (ρ / (1 + ρ)) ^ 2) = Real.sqrt (1 / (1 + ρ)) := by
    rw [Real.sq_sqrt (by positivity)]
    congr 1
    field_simp
    ring
  have hbr := (scSide_pos hr₀ hr₁).2
  have hbs := (scSide_pos hs₀ hs₁).2
  -- `μ(r) = π a_r / b_r` and `a_r = b_{r'} / 2`
  rw [gm_grotzschMu_eq hr₀ hr₁, gm_grotzschMu_eq hs₀ hs₁, e57_sideA_eq hr₀ hr₁,
    e57_sideA_eq hs₀ hs₁, hrs, hsr]
  field_simp
  ring

/-- (5.20): `Λ(ρ) · Λ(1/ρ) = 1`.  (`ℍ(-1, 0, ρ, ∞)` is mapped onto `ℍ(∞, -1, 0, 1/ρ)` by
`z ↦ (z - ρ)/(ρz + ρ)`; then use Theorem 1.2.) -/
theorem eq5_20 {ρ : ℝ} (hρ : 0 < ρ) : quadLambda ρ * quadLambda (1 / ρ) = 1 := by
  set Q : TopQuad := ⟨upperHalf, _, isTopQuad_upperHalf_lambda hρ⟩ with hQ
  set Q' : TopQuad := ⟨upperHalf, _, isTopQuad_upperHalf_lambda (one_div_pos.2 hρ)⟩ with hQ'
  have hconf : Q.rotate.ConfEquiv Q' := by
    have hdet : (0 : ℝ) < 1 * ρ - (-ρ) * ρ := by nlinarith
    have hS' : ((1 : ℝ) : ℂ) * ((ρ : ℝ) : ℂ) - ((-ρ : ℝ) : ℂ) * ((ρ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hdet.ne'
    set e := mobiusHomeomorph ((1 : ℝ) : ℂ) ((-ρ : ℝ) : ℂ) ((ρ : ℝ) : ℂ) ((ρ : ℝ) : ℂ) hS' with he
    have heS : ∀ w ∈ upperHalf, e (w : ExtPlane) =
        ((mobiusFn ((1 : ℝ) : ℂ) ((-ρ : ℝ) : ℂ) ((ρ : ℝ) : ℂ) ((ρ : ℝ) : ℂ) w : ℂ) : ExtPlane) :=
      fun w hw => by
        rw [he, mobiusHomeomorph_apply]
        exact mobiusExt_coe (mobiusFn_den_ne_zero_real hdet.ne' hw)
    have himgS : e '' toExt upperHalf = toExt upperHalf := by
      rw [he]
      exact mobiusExt_image_toExt_upperHalf hdet
    refine ⟨_, _, (isConformalOnto_mobius_upperHalf hdet).comp (isConformalOnto_id upperHalf),
      (isHomeoExtension_id upperHalf).comp_homeomorph (isConformalOnto_id upperHalf).mapsTo e
        heS himgS, fun i => ?_⟩
    fin_cases i
    · show e (((-1 : ℝ) : ℂ) : ExtPlane) = extInf
      rw [he, mobiusHomeomorph_apply, mobiusExt_ofReal_coe_of_eq_zero (by ring)]
    · show e ((0 : ℂ) : ExtPlane) = (((-1 : ℝ) : ℂ) : ExtPlane)
      rw [he, mobiusHomeomorph_apply, ← ofReal_zero,
        mobiusExt_ofReal_coe (by simp [hρ.ne'])]
      congr 2
      field_simp
      ring
    · show e (((ρ : ℝ) : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane)
      rw [he, mobiusHomeomorph_apply, mobiusExt_ofReal_coe (by positivity)]
      congr 1
      simp
    · show e extInf = (((1 / ρ : ℝ) : ℂ) : ExtPlane)
      rw [he, mobiusHomeomorph_apply, mobiusExt_ofReal_infty hρ.ne']
  have h1 : quadLambda ρ = Q.modulus := rfl
  have h2 : quadLambda (1 / ρ) = Q'.modulus := rfl
  rw [h1, h2, ← thm1_3_modulus_conformal_invariant hconf, thm1_2_modulus_rotate Q, one_div,
    inv_mul_cancel₀ (modulus_pos Q.rotate).ne']

/-- (5.21): `μ(1/√2) = π/2`. -/
theorem eq5_21 : grotzschMu (1 / Real.sqrt 2) = π / 2 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hr₀ : 0 < 1 / Real.sqrt 2 := by positivity
  have hr₁ : 1 / Real.sqrt 2 < 1 := by
    rw [div_lt_one h2]
    exact Real.one_lt_sqrt_two
  -- `1/√2` is its own complementary modulus, so `a = b/2` and `μ = π a / b = π/2`
  have hs : Real.sqrt (1 - (1 / Real.sqrt 2) ^ 2) = 1 / Real.sqrt 2 := by
    rw [div_pow, Real.sq_sqrt two_pos.le, one_pow, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      Real.sqrt_div' 1 two_pos.le, Real.sqrt_one]
  have hb := (scSide_pos hr₀ hr₁).2
  rw [gm_grotzschMu_eq hr₀ hr₁, e57_sideA_eq hr₀ hr₁, hs]
  field_simp

end LiZhongQC
