import LiZhongQC.Ch01.S01_Quadrilateral
import LiZhongQC.Lemmas.Mobius
import LiZhongQC.Lemmas.Quadrilateral

/-!
# Winding-number and boundary cyclic-order machinery

Degree-free winding-number tools for Theorem 6.1 (the boundary correspondence of a conformal
self-map of a Jordan domain preserves cyclic order): homotopy-invariant logarithm lifts along
paths (`W1a`/`W1c`/`W1d`/`W1e`/`W3a`), the loop-winding contradiction ruling out an
order-reversing boundary correspondence with a fixed local orientation (`W6` /
`wn_false_of_strictAnti_boundary`), and the resulting cyclic-order preservation for a conformal
self-map of `ℍ` fixing `∞` (`W5core`).

Also proves, as a self-contained real-Möbius / `OnePoint ℝ` argument:
* (A) `dichotomy_onePoint_homeomorphism`: every self-homeomorphism of `OnePoint ℝ` is either
  cyclic-order preserving or cyclic-order reversing on every real `4`-tuple, transported to the
  boundary of `ℍ` in `ℂ̄` as `dichotomy_frontier_upperHalf`;
* (B) `automorphism_upperHalf_preserves_cyclicOrder`: automorphisms of `ℍ` (positive-determinant
  real Möbius maps) preserve boundary cyclic order.

Frozen interfaces: `W1a`, `W1c`, `W1e`, `W1d`, `W3a`, `W5core`, `wn_false_of_strictAnti_boundary`
match `sw_freeze.lean` (md5 `df1b25952c5c1c98a23da810dc6cf559`). Consolidated from session -f4's
working files 2026-09-16; the two independently-developed copies of the real-Möbius algebra
(`mobiusReal_sub_eq` etc.) and of the cyclic-chain helper `cyclicStrictMono_of_chain` (used by
both (A) and (B)) have been deduplicated.
-/

open Complex Set Metric Filter Topology Bornology
open scoped Real

set_option maxHeartbeats 1000000

noncomputable section

namespace LiZhongQC

-- ===== W1a, W1c, W1e, W1d, W3a, and the H2/H3/H4 wn_ arg helpers, plus W5core's anti-branch
-- reduction wn_false_of_strictAnti_boundary. =====


-- W1a (copied for self-containedness of this scratch assembly)
theorem exists_continuousOn_log_lift {γ : ℝ → ℂ} {w : ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hw : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w) :
    ∃ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) ∧ ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = γ t - w := by
  have h01 : (0:ℝ) ≤ 1 := zero_le_one
  set f : Icc (0:ℝ) 1 → ℂ := (Icc (0:ℝ) 1).restrict γ with hfdef
  have hfcont : Continuous f := continuousOn_iff_continuous_restrict.mp hγ
  set γext : ℝ → ℂ := Set.IccExtend h01 f with hγextdef
  have hγextcont : Continuous γext := continuous_IccExtend_iff.2 hfcont
  have hγexteq : ∀ t ∈ Icc (0:ℝ) 1, γext t = γ t := fun t ht => IccExtend_of_mem h01 f ht
  have hγextne : ∀ t : ℝ, γext t ≠ w := by
    intro t
    have : γext t ∈ range f := by
      rw [hγextdef]; exact mem_range_self _
    obtain ⟨s, hs⟩ := this
    rw [← hs]
    exact hw s.1 s.2
  have hIoo : IsOpen (Ioo (-1:ℝ) 2) := isOpen_Ioo
  have hIooconv : Convex ℝ (Ioo (-1:ℝ) 2) := convex_Ioo _ _
  have hIoone : (Ioo (-1:ℝ) 2).Nonempty := ⟨0, by norm_num⟩
  have hIoosc : IsSimplyConnected (Ioo (-1:ℝ) 2) := by
    have : ContractibleSpace ↥(Ioo (-1:ℝ) 2) := hIooconv.contractibleSpace hIoone
    exact SimplyConnectedSpace.ofContractible _
  have hgcont : ContinuousOn (fun t => γext t - w) (Ioo (-1:ℝ) 2) :=
    (hγextcont.sub continuous_const).continuousOn
  have hg0 : (0:ℂ) ∉ (fun t => γext t - w) '' (Ioo (-1:ℝ) 2) := by
    rintro ⟨t, -, ht⟩
    exact hγextne t (sub_eq_zero.mp ht)
  obtain ⟨L, hLcont, hLeq⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hIoosc hIoo hgcont hg0
  have hsub : Icc (0:ℝ) 1 ⊆ Ioo (-1:ℝ) 2 := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  refine ⟨L, hLcont.mono hsub, fun t ht => ?_⟩
  have hthis := hLeq (hsub ht)
  simp only [Function.comp_apply] at hthis
  rwa [hγexteq t ht] at hthis

-- W1c (copied)
theorem lift_change_eq_of_lifts {γ L M : ℝ → ℂ}
    (hL : ContinuousOn L (Icc 0 1)) (hM : ContinuousOn M (Icc 0 1))
    (hLe : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = γ t)
    (hMe : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (M t) = γ t) :
    L 1 - L 0 = M 1 - M 0 := by
  classical
  set D : ℝ → ℂ := fun t => L t - M t with hDdef
  have hDcont : ContinuousOn D (Icc (0:ℝ) 1) := hL.sub hM
  have hDexp : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (D t) = 1 := by
    intro t ht
    have hγne : γ t ≠ 0 := hMe t ht ▸ Complex.exp_ne_zero (M t)
    show Complex.exp (L t - M t) = 1
    rw [Complex.exp_sub, hLe t ht, hMe t ht, div_self hγne]
  have hDmem : ∀ t ∈ Icc (0:ℝ) 1, D t ∈ AddSubgroup.zmultiples (2 * π * I) := by
    intro t ht
    rw [AddSubgroup.mem_zmultiples_iff]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hDexp t ht)
    exact ⟨n, by rw [hn]; ring⟩
  let f : ℝ → AddSubgroup.zmultiples (2 * π * I) := fun t =>
    if h : t ∈ Icc (0:ℝ) 1 then ⟨D t, hDmem t h⟩ else 0
  have hfval : ∀ t ∈ Icc (0:ℝ) 1, (f t : ℂ) = D t := by
    intro t ht
    simp only [f, dif_pos ht]
  have hfcont : ContinuousOn f (Icc (0:ℝ) 1) := by
    have h1 : ContinuousOn (fun t => (f t : ℂ)) (Icc (0:ℝ) 1) := hDcont.congr hfval
    exact (Topology.IsEmbedding.subtypeVal.isInducing).continuousOn_iff.2 h1
  have heq : f 0 = f 1 :=
    IsPreconnected.constant (isPreconnected_Icc (a := (0:ℝ)) (b := 1)) hfcont
      (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  have heqv : (f 0 : ℂ) = (f 1 : ℂ) := congrArg Subtype.val heq
  rw [hfval 0 (Set.left_mem_Icc.2 zero_le_one), hfval 1 (Set.right_mem_Icc.2 zero_le_one)] at heqv
  have hD0 : D 0 = L 0 - M 0 := rfl
  have hD1 : D 1 = L 1 - M 1 := rfl
  rw [hD0, hD1] at heqv
  linear_combination -heqv

-- W1e (copied)
theorem lift_sub_eq_log_sub_log {γ L : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Icc a b)) (hL : ContinuousOn L (Icc a b))
    (hslit : ∀ t ∈ Icc a b, γ t ∈ slitPlane)
    (hexp : ∀ t ∈ Icc a b, Complex.exp (L t) = γ t) :
    L b - L a = Complex.log (γ b) - Complex.log (γ a) := by
  classical
  set D : ℝ → ℂ := fun t => L t - Complex.log (γ t) with hDdef
  have hγne : ∀ t ∈ Icc a b, γ t ≠ 0 := fun t ht => Complex.slitPlane_ne_zero (hslit t ht)
  have hDcont : ContinuousOn D (Icc a b) := by
    apply hL.sub
    exact ContinuousOn.clog hγ hslit
  have hDexp : ∀ t ∈ Icc a b, Complex.exp (D t) = 1 := by
    intro t ht
    show Complex.exp (L t - Complex.log (γ t)) = 1
    rw [Complex.exp_sub, hexp t ht, Complex.exp_log (hγne t ht), div_self (hγne t ht)]
  have hDmem : ∀ t ∈ Icc a b, D t ∈ AddSubgroup.zmultiples (2 * π * I) := by
    intro t ht
    rw [AddSubgroup.mem_zmultiples_iff]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hDexp t ht)
    exact ⟨n, by rw [hn]; ring⟩
  let f : ℝ → AddSubgroup.zmultiples (2 * π * I) := fun t =>
    if h : t ∈ Icc a b then ⟨D t, hDmem t h⟩ else 0
  have hfval : ∀ t ∈ Icc a b, (f t : ℂ) = D t := by
    intro t ht
    simp only [f, dif_pos ht]
  have hfcont : ContinuousOn f (Icc a b) := by
    have h1 : ContinuousOn (fun t => (f t : ℂ)) (Icc a b) := hDcont.congr hfval
    exact (Topology.IsEmbedding.subtypeVal.isInducing).continuousOn_iff.2 h1
  have heq : f a = f b :=
    IsPreconnected.constant (isPreconnected_Icc (a := a) (b := b)) hfcont
      (Set.left_mem_Icc.2 hab) (Set.right_mem_Icc.2 hab)
  have heqv : (f a : ℂ) = (f b : ℂ) := congrArg Subtype.val heq
  rw [hfval a (Set.left_mem_Icc.2 hab), hfval b (Set.right_mem_Icc.2 hab)] at heqv
  have hDa : D a = L a - Complex.log (γ a) := rfl
  have hDb : D b = L b - Complex.log (γ b) := rfl
  rw [hDa, hDb] at heqv
  linear_combination -heqv

-- W1d (copied)
theorem lift_change_eq_of_norm_sub_lt {γ β L M : ℝ → ℂ}
    (hγ : ContinuousOn γ (Icc 0 1)) (hβ : ContinuousOn β (Icc 0 1))
    (hγ1 : γ 1 = γ 0) (hβ1 : β 1 = β 0)
    (hlt : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - β t‖ < ‖β t‖)
    (hL : ContinuousOn L (Icc 0 1)) (hM : ContinuousOn M (Icc 0 1))
    (hLe : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = γ t)
    (hMe : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (M t) = β t) :
    L 1 - L 0 = M 1 - M 0 := by
  have hβne : ∀ t ∈ Icc (0:ℝ) 1, β t ≠ 0 := by
    intro t ht hβ0
    have := hlt t ht
    rw [hβ0] at this
    simp only [norm_zero] at this
    linarith [norm_nonneg (γ t - 0)]
  set q : ℝ → ℂ := fun t => γ t / β t with hqdef
  have hqcont : ContinuousOn q (Icc (0:ℝ) 1) := hγ.div hβ hβne
  have hqslit : ∀ t ∈ Icc (0:ℝ) 1, q t ∈ slitPlane := by
    intro t ht
    have hnorm : ‖q t - 1‖ < 1 := by
      have hb0 : β t ≠ 0 := hβne t ht
      rw [hqdef]
      show ‖γ t / β t - 1‖ < 1
      rw [div_sub_one hb0, norm_div]
      rw [div_lt_one (norm_pos_iff.2 hb0)]
      exact hlt t ht
    have := Complex.mem_slitPlane_of_norm_lt_one (z := q t - 1) hnorm
    simpa using this
  set N : ℝ → ℂ := fun t => L t - M t with hNdef
  have hNcont : ContinuousOn N (Icc (0:ℝ) 1) := hL.sub hM
  have hNexp : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (N t) = q t := by
    intro t ht
    show Complex.exp (L t - M t) = γ t / β t
    rw [Complex.exp_sub, hLe t ht, hMe t ht]
  have hkey := lift_sub_eq_log_sub_log (a := (0:ℝ)) (b := 1) zero_le_one hqcont hNcont hqslit hNexp
  have hq1 : q 1 = q 0 := by rw [hqdef]; simp only; rw [hγ1, hβ1]
  rw [hq1] at hkey
  have hN0 : N 0 = L 0 - M 0 := rfl
  have hN1 : N 1 = L 1 - M 1 := rfl
  rw [hN0, hN1, sub_self] at hkey
  linear_combination hkey

-- W3a (copied)
theorem lift_change_eq_of_homotopy {H : ℝ → ℝ → ℂ} {w : ℂ}
    (hH : ContinuousOn (Function.uncurry H) (Icc 0 1 ×ˢ Icc 0 1))
    (hper : ∀ s ∈ Icc (0 : ℝ) 1, H s 1 = H s 0)
    (hw : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, H s t ≠ w)
    {L₀ L₁ : ℝ → ℂ} (hL₀ : ContinuousOn L₀ (Icc 0 1)) (hL₁ : ContinuousOn L₁ (Icc 0 1))
    (hL₀e : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L₀ t) = H 0 t - w)
    (hL₁e : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L₁ t) = H 1 t - w) :
    L₀ 1 - L₀ 0 = L₁ 1 - L₁ 0 := by
  have hsq : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hnorm_cont : ContinuousOn (fun p : ℝ × ℝ => ‖H p.1 p.2 - w‖) (Icc 0 1 ×ˢ Icc 0 1) :=
    (hH.sub continuousOn_const).norm
  have hsqne : (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1).Nonempty := ⟨(0, 0), by simp⟩
  obtain ⟨p₀, hp₀mem, hp₀min⟩ := hsq.exists_isMinOn hsqne hnorm_cont
  set m : ℝ := ‖H p₀.1 p₀.2 - w‖ with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]
    exact norm_pos_iff.2 (sub_ne_zero.2 (hw p₀.1 hp₀mem.1 p₀.2 hp₀mem.2))
  have hmle : ∀ p ∈ Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1, m ≤ ‖H p.1 p.2 - w‖ := hp₀min
  have hUC : UniformContinuousOn (Function.uncurry H) (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) :=
    hsq.uniformContinuousOn_of_continuous hH
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.1 hUC m hmpos
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · exfalso
      rw [hN0, Nat.cast_zero] at hN
      have : 0 < 1 / δ := div_pos one_pos hδpos
      linarith
    · exact hNpos
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  have hstep : 1 / (N:ℝ) < δ := by
    rw [div_lt_iff₀ hNR]
    rw [div_lt_iff₀ hδpos] at hN
    linarith [hN]
  have hex : ∀ i : ℕ, ∃ Lᵢ : ℝ → ℂ, ContinuousOn Lᵢ (Icc 0 1) ∧
      ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (Lᵢ t) = H ((min i N : ℕ) / N) t - w := by
    intro i
    have hsi : ((min i N : ℕ):ℝ) / N ∈ Icc (0:ℝ) 1 := by
      constructor
      · positivity
      · rw [div_le_one hNR]; exact_mod_cast Nat.min_le_right i N
    apply exists_continuousOn_log_lift
    · have : ContinuousOn (fun t => Function.uncurry H
          (((min i N : ℕ) / N : ℝ), t)) (Icc (0:ℝ) 1) := by
        apply hH.comp (continuousOn_const.prodMk continuousOn_id)
        intro t ht
        exact ⟨hsi, ht⟩
      simpa [Function.uncurry] using this
    · exact fun t ht => hw _ hsi t ht
  choose L hLcont hLexp using hex
  have hLexp' : ∀ i : ℕ, i ≤ N → ∀ t ∈ Icc (0:ℝ) 1,
      Complex.exp (L i t) = H (i / N) t - w := by
    intro i hi t ht
    have hmin : (min i N : ℕ) = i := min_eq_left hi
    have hthis := hLexp i t ht
    rwa [hmin] at hthis
  have hLcont' : ∀ i : ℕ, ContinuousOn (L i) (Icc 0 1) := hLcont
  have hstepeq : ∀ i : ℕ, i < N → L i 1 - L i 0 = L (i+1) 1 - L (i+1) 0 := by
    intro i hiN
    have hi1 : i ≤ N := hiN.le
    have hi2 : i + 1 ≤ N := hiN
    have hsi : (i:ℝ) / N ∈ Icc (0:ℝ) 1 :=
      ⟨by positivity, by rw [div_le_one hNR]; exact_mod_cast hi1⟩
    have hsi1 : ((i:ℝ)+1) / N ∈ Icc (0:ℝ) 1 :=
      ⟨by positivity, by rw [div_le_one hNR]; exact_mod_cast hi2⟩
    have hdist : dist ((i:ℝ)/N) (((i:ℝ)+1)/N) < δ := by
      rw [Real.dist_eq]
      have : (i:ℝ)/N - ((i:ℝ)+1)/N = -(1/N) := by field_simp; ring
      rw [this, abs_neg, abs_of_pos (by positivity)]
      exact hstep
    have hclose : ∀ t ∈ Icc (0:ℝ) 1,
        ‖H (i/N) t - H (((i:ℝ)+1)/N) t‖ < m := by
      intro t ht
      have hdd : dist ((i/N : ℝ), t) (((i:ℝ)+1)/N, t) < δ := by
        rw [Prod.dist_eq]
        exact max_lt hdist (by simpa using hδpos)
      have := hδ ((i/N : ℝ), t) ⟨hsi, ht⟩ (((i:ℝ)+1)/N, t) ⟨hsi1, ht⟩ hdd
      simpa [Function.uncurry, Complex.dist_eq] using this
    have hlt : ∀ t ∈ Icc (0:ℝ) 1,
        ‖(H (i/N) t - w) - (H (((i:ℝ)+1)/N) t - w)‖ < ‖H (((i:ℝ)+1)/N) t - w‖ := by
      intro t ht
      have h1 : (H (i/N) t - w) - (H (((i:ℝ)+1)/N) t - w) = H (i/N) t - H (((i:ℝ)+1)/N) t := by
        ring
      rw [h1]
      exact lt_of_lt_of_le (hclose t ht) (hmle (((i:ℝ)+1)/N, t) ⟨hsi1, ht⟩)
    have hcast : ((i:ℝ)+1)/N = ((i+1 : ℕ) : ℝ)/N := by push_cast; ring
    have key := lift_change_eq_of_norm_sub_lt
      (γ := fun t => H (i/N) t - w) (β := fun t => H (((i:ℝ)+1)/N) t - w)
      (L := L i) (M := L (i+1))
      ((hH.comp (continuousOn_const.prodMk continuousOn_id)
          (fun t ht => ⟨hsi, ht⟩)).sub continuousOn_const)
      ((hH.comp (continuousOn_const.prodMk continuousOn_id)
          (fun t ht => ⟨hsi1, ht⟩)).sub continuousOn_const)
      (by show H (i/N) 1 - w = H (i/N) 0 - w; rw [hper _ hsi])
      (by show H (((i:ℝ)+1)/N) 1 - w = H (((i:ℝ)+1)/N) 0 - w; rw [hper _ hsi1])
      hlt (hLcont' i) (hLcont' (i+1))
      (hLexp' i hi1) (by rw [hcast]; exact hLexp' (i+1) hi2)
    exact key
  have hchain : ∀ i : ℕ, i ≤ N → L 0 1 - L 0 0 = L i 1 - L i 0 := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn1
      have hn : n ≤ N := Nat.le_of_succ_le hn1
      have hnN : n < N := hn1
      rw [ih hn, hstepeq n hnN]
  have key0 : L 0 1 - L 0 0 = L₀ 1 - L₀ 0 := by
    refine lift_change_eq_of_lifts (γ := fun t => H 0 t - w) (hLcont' 0) hL₀ ?_ hL₀e
    intro t ht
    have hthis := hLexp' 0 (Nat.zero_le N) t ht
    simpa using hthis
  have keyN : L N 1 - L N 0 = L₁ 1 - L₁ 0 := by
    refine lift_change_eq_of_lifts (γ := fun t => H 1 t - w) (hLcont' N) hL₁ ?_ hL₁e
    intro t ht
    have hthis := hLexp' N le_rfl t ht
    rwa [div_self (ne_of_gt hNR)] at hthis
  rw [← key0, ← keyN]
  exact hchain N le_rfl

-- H2/H3/H4 helpers (copied for self-containedness of this scratch assembly)
theorem norm_ofReal_sub_I_mul (u c : ℝ) : ‖(u:ℂ) - I*c‖ = Real.sqrt (u^2+c^2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp [pow_two]

theorem arg_ofReal_sub_I_mul_mem (c : ℝ) (hc : 0 < c) (u : ℝ) :
    -π < Complex.arg ((u:ℂ) - I*c) ∧ Complex.arg ((u:ℂ) - I*c) < 0 := by
  have hz : ((u:ℂ) - I*c).im = -c := by simp
  have hzlt : ((u:ℂ) - I*c).im < 0 := by rw [hz]; linarith
  rw [Complex.arg_of_im_neg hzlt]
  have hnorm : ‖(u:ℂ) - I*c‖ = Real.sqrt (u^2+c^2) := norm_ofReal_sub_I_mul u c
  have hnormpos : 0 < ‖(u:ℂ) - I*c‖ := by rw [hnorm]; positivity
  have hre : ((u:ℂ) - I*c).re = u := by simp
  rw [hre]
  have hlt1 : u / ‖(u:ℂ) - I*c‖ < 1 := by
    rw [div_lt_one hnormpos, hnorm]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ u^2+c^2 by positivity), Real.sqrt_nonneg (u^2+c^2),
      sq_nonneg (Real.sqrt (u^2+c^2) - u)]
  have hgtm1 : -1 < u / ‖(u:ℂ) - I*c‖ := by
    rw [lt_div_iff₀ hnormpos, hnorm]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ u^2+c^2 by positivity), Real.sqrt_nonneg (u^2+c^2),
      sq_nonneg (Real.sqrt (u^2+c^2) + u)]
  constructor
  · linarith [Real.arccos_lt_pi.2 hgtm1]
  · linarith [Real.arccos_pos.2 hlt1]

theorem arg_ofReal_sub_I_mul_strictMono (c : ℝ) (hc : 0 < c) (u₁ u₂ : ℝ) (h : u₂ < u₁) :
    Complex.arg ((u₂:ℂ) - I*c) < Complex.arg ((u₁:ℂ) - I*c) := by
  have hz1 : ((u₁:ℂ) - I*c).im = -c := by simp
  have hz2 : ((u₂:ℂ) - I*c).im = -c := by simp
  have hzlt1 : ((u₁:ℂ) - I*c).im < 0 := by rw [hz1]; linarith
  have hzlt2 : ((u₂:ℂ) - I*c).im < 0 := by rw [hz2]; linarith
  rw [Complex.arg_of_im_neg hzlt1, Complex.arg_of_im_neg hzlt2]
  have hnorm1 : ‖(u₁:ℂ) - I*c‖ = Real.sqrt (u₁^2+c^2) := norm_ofReal_sub_I_mul u₁ c
  have hnorm2 : ‖(u₂:ℂ) - I*c‖ = Real.sqrt (u₂^2+c^2) := norm_ofReal_sub_I_mul u₂ c
  have hre1 : ((u₁:ℂ) - I*c).re = u₁ := by simp
  have hre2 : ((u₂:ℂ) - I*c).re = u₂ := by simp
  rw [hnorm1, hnorm2, hre1, hre2]
  have hA : 0 < Real.sqrt (u₁^2+c^2) := by positivity
  have hB : 0 < Real.sqrt (u₂^2+c^2) := by positivity
  have hA2 : Real.sqrt (u₁^2+c^2)^2 = u₁^2+c^2 := Real.sq_sqrt (by positivity)
  have hB2 : Real.sqrt (u₂^2+c^2)^2 = u₂^2+c^2 := Real.sq_sqrt (by positivity)
  have key : u₂ * Real.sqrt (u₁^2+c^2) < u₁ * Real.sqrt (u₂^2+c^2) := by
    by_cases hu2 : 0 ≤ u₂
    · have hu1 : 0 < u₁ := by linarith
      have hsqlt : (u₂ * Real.sqrt (u₁^2+c^2))^2 < (u₁ * Real.sqrt (u₂^2+c^2))^2 := by
        have hcc : (0:ℝ) < c^2 := by positivity
        nlinarith [mul_pos hcc (mul_pos (sub_pos.2 h) (show (0:ℝ) < u₁+u₂ by linarith))]
      have h1 : 0 ≤ u₂ * Real.sqrt (u₁^2+c^2) := mul_nonneg hu2 hA.le
      have h2 : 0 ≤ u₁ * Real.sqrt (u₂^2+c^2) := mul_nonneg hu1.le hB.le
      have := Real.sqrt_lt_sqrt (sq_nonneg _) hsqlt
      rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at this
    · rw [not_le] at hu2
      by_cases hu1 : 0 ≤ u₁
      · have h1 : u₂ * Real.sqrt (u₁^2+c^2) < 0 := mul_neg_of_neg_of_pos hu2 hA
        have h2 : 0 ≤ u₁ * Real.sqrt (u₂^2+c^2) := mul_nonneg hu1 hB.le
        linarith
      · rw [not_le] at hu1
        have hcc : (0:ℝ) < c^2 := by positivity
        have hsqlt : (u₁ * Real.sqrt (u₂^2+c^2))^2 < (u₂ * Real.sqrt (u₁^2+c^2))^2 := by
          nlinarith [mul_pos hcc (mul_pos (sub_pos.2 h) (show (0:ℝ) < -u₁-u₂ by linarith))]
        have h1 : 0 ≤ -(u₂ * Real.sqrt (u₁^2+c^2)) := by
          have := mul_nonpos_of_nonpos_of_nonneg hu2.le hA.le
          linarith
        have h2 : 0 ≤ -(u₁ * Real.sqrt (u₂^2+c^2)) := by
          have := mul_nonpos_of_nonpos_of_nonneg hu1.le hB.le
          linarith
        have hsqlt' : (-(u₁ * Real.sqrt (u₂^2+c^2)))^2 < (-(u₂ * Real.sqrt (u₁^2+c^2)))^2 := by
          nlinarith [hsqlt]
        have := Real.sqrt_lt_sqrt (sq_nonneg _) hsqlt'
        rw [Real.sqrt_sq h1, Real.sqrt_sq h2] at this
        linarith
  have hfin : u₂ / Real.sqrt (u₂^2+c^2) < u₁ / Real.sqrt (u₁^2+c^2) := by
    rw [div_lt_div_iff₀ hB hA]
    linarith [key]
  have hmemA : u₁ / Real.sqrt (u₁^2+c^2) ∈ Icc (-1:ℝ) 1 := by
    constructor
    · rw [le_div_iff₀ hA]
      nlinarith [sq_nonneg (Real.sqrt (u₁^2+c^2) + u₁)]
    · rw [div_le_one hA]
      nlinarith [sq_nonneg (Real.sqrt (u₁^2+c^2) - u₁)]
  have hmemB : u₂ / Real.sqrt (u₂^2+c^2) ∈ Icc (-1:ℝ) 1 := by
    constructor
    · rw [le_div_iff₀ hB]
      nlinarith [sq_nonneg (Real.sqrt (u₂^2+c^2) + u₂)]
    · rw [div_le_one hB]
      nlinarith [sq_nonneg (Real.sqrt (u₂^2+c^2) - u₂)]
  linarith [Real.strictAntiOn_arccos hmemB hmemA hfin]

theorem norm_neg_ofReal_sub_I_mul (c u : ℝ) : ‖(-c:ℂ) - I*u‖ = Real.sqrt (c^2+u^2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp [pow_two]

theorem arccos_neg_div_norm_mem (c u : ℝ) (hc : 0 < c) (hu : u ≠ 0) :
    Real.arccos (-c / ‖(-c:ℂ) - I*u‖) ∈ Ioo (π/2) π := by
  have hnorm : ‖(-c:ℂ) - I*u‖ = Real.sqrt (c^2+u^2) := norm_neg_ofReal_sub_I_mul c u
  have hnormpos : 0 < ‖(-c:ℂ) - I*u‖ := by rw [hnorm]; positivity
  have hlt0 : -c / ‖(-c:ℂ) - I*u‖ < 0 := div_neg_of_neg_of_pos (by linarith) hnormpos
  have hu2pos : 0 < u^2 := by positivity
  have hgtm1 : -1 < -c / ‖(-c:ℂ) - I*u‖ := by
    rw [hnorm, lt_div_iff₀ (by positivity : (0:ℝ) < Real.sqrt (c^2+u^2))]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ c^2+u^2 by positivity), Real.sqrt_nonneg (c^2+u^2),
      sq_nonneg (Real.sqrt (c^2+u^2) - c)]
  constructor
  · rw [← not_le, Real.arccos_le_pi_div_two, not_le]
    exact hlt0
  · exact Real.arccos_lt_pi.2 hgtm1

theorem arg_neg_ofReal_sub_I_mul_mem_pos (c u : ℝ) (hc : 0 < c) (hu : 0 < u) :
    -π < Complex.arg (-c - I*u) ∧ Complex.arg (-c - I*u) < -π/2 := by
  have hz : ((-c:ℂ) - I*u).im = -u := by simp
  have hzlt : ((-c:ℂ) - I*u).im < 0 := by rw [hz]; linarith
  rw [Complex.arg_of_im_neg hzlt]
  have hre : ((-c:ℂ) - I*u).re = -c := by simp
  rw [hre]
  obtain ⟨h1, h2⟩ := arccos_neg_div_norm_mem c u hc hu.ne'
  constructor <;> linarith

theorem arg_neg_ofReal_sub_I_mul_mem_neg (c u : ℝ) (hc : 0 < c) (hu : u < 0) :
    π/2 < Complex.arg (-c - I*u) ∧ Complex.arg (-c - I*u) < π := by
  have hz : ((-c:ℂ) - I*u).im = -u := by simp
  have hzgt : 0 < ((-c:ℂ) - I*u).im := by rw [hz]; linarith
  rw [Complex.arg_of_im_pos hzgt]
  have hre : ((-c:ℂ) - I*u).re = -c := by simp
  rw [hre]
  exact arccos_neg_div_norm_mem c u hc hu.ne

theorem neg_I_mul_sub_mem_slitPlane (w w₀ : ℂ) (hw : 0 ≤ w.im) (hw₀ : 0 < w₀.im)
    (hnorm : ‖w₀‖ < ‖w‖) : -I * (w - w₀) ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  have hre : (-I * (w - w₀)).re = w.im - w₀.im := by simp
  have him : (-I * (w - w₀)).im = w₀.re - w.re := by simp
  by_contra hcon
  rw [not_or, not_lt] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [not_not] at h2
  rw [hre] at h1
  rw [him] at h2
  have hwim_le : w.im ≤ w₀.im := by linarith
  have hwre_eq : w.re = w₀.re := by linarith
  have hnormsq : ‖w‖^2 ≤ ‖w₀‖^2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hwre_eq]
    nlinarith
  have : ‖w‖ ≤ ‖w₀‖ := by
    nlinarith [norm_nonneg w, norm_nonneg w₀, hnormsq]
  linarith

-- W5core's anti-branch reduces to this: the hypotheses of that branch (extracted boundary
-- map `f`, strictly antitone, plus the local winding hypothesis) are jointly contradictory.
theorem wn_false_of_strictAnti_boundary {g : ℂ → ℂ} {G : ExtPlane → ExtPlane}
    (hG : IsHomeoExtension g upperHalf upperHalf G)
    (hgs : g '' upperHalf = upperHalf) (hinf : G extInf = extInf)
    {z₀ : ℂ} (hz₀ : z₀ ∈ upperHalf)
    (hloc : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = g (z₀ + ρ * Complex.exp (2 * π * I * t)) - g z₀) →
      L 1 - L 0 = 2 * π * I)
    (f : ℝ → ℝ) (hfcont : Continuous f) (hfinj : Function.Injective f)
    (hf : ∀ t : ℝ, G (((t:ℝ):ℂ):ExtPlane) = (((f t:ℝ):ℂ):ExtPlane))
    (hanti : StrictAnti f)
    (hFf : ∀ z ∈ upperHalf, G (z:ExtPlane) = ((g z:ℂ):ExtPlane))
    (hFc : ContinuousOn G (closure (toExt upperHalf)))
    (hFi : InjOn G (closure (toExt upperHalf)))
    (hFimg : G '' closure (toExt upperHalf) = closure (toExt upperHalf))
    (hUo : IsOpen upperHalf)
    (hfr_eq : frontier (toExt upperHalf) = toExt {z : ℂ | z.im = 0} ∪ {extInf})
    (hFfr : G '' frontier (toExt upperHalf) = frontier (toExt upperHalf))
    (hcl_eq : closure (toExt upperHalf) = toExt {z : ℂ | 0 ≤ z.im} ∪ {extInf}) :
    False := by
  -- f is surjective onto ℝ.
  have hfsurj : Function.Surjective f := by
    intro s
    have hsmem : (((s:ℝ):ℂ):ExtPlane) ∈ frontier (toExt upperHalf) := by
      rw [hfr_eq]; exact Or.inl ⟨(s:ℂ), rfl, rfl⟩
    have hsmem' : (((s:ℝ):ℂ):ExtPlane) ∈ G '' frontier (toExt upperHalf) := by
      rw [hFfr]; exact hsmem
    obtain ⟨p, hpmem, hpeq⟩ := hsmem'
    induction p using OnePoint.rec with
    | infty => rw [hinf] at hpeq; exact absurd hpeq (OnePoint.infty_ne_coe _)
    | coe z =>
      rw [hfr_eq] at hpmem
      rcases hpmem with ⟨z', hz', hzeq⟩ | hz'
      · refine ⟨z'.re, ?_⟩
        have hz're : z' = (z'.re : ℂ) := Complex.ext rfl (by simpa using hz')
        have := hf z'.re
        rw [← hz're, hzeq] at this
        exact Complex.ofReal_injective (OnePoint.coe_injective (this.symm.trans hpeq))
      · exact absurd hz' (OnePoint.coe_ne_infty _)
  -- G₀: the ℂ-valued extraction of G on the closed half-plane.
  have hG0ex : ∀ z : ℂ, ∃ w : ℂ, 0 ≤ z.im → G ((z:ℂ):ExtPlane) = ((w:ℂ):ExtPlane) := by
    intro z
    by_cases hz : 0 ≤ z.im
    · rcases eq_or_lt_of_le hz with heq | hlt
      · have hzre : z = (z.re : ℂ) := Complex.ext rfl heq.symm
        exact ⟨f z.re, fun _ => by rw [hzre]; exact hf z.re⟩
      · exact ⟨g z, fun _ => hFf z hlt⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose G₀ hG₀ using hG0ex
  have hmapsto : ∀ z : ℂ, 0 ≤ z.im → ((z:ℂ):ExtPlane) ∈ closure (toExt upperHalf) := by
    intro z hz
    rw [hcl_eq]; exact Or.inl ⟨z, hz, rfl⟩
  have hG0cont : ContinuousOn G₀ {z : ℂ | 0 ≤ z.im} := by
    have hcompcont : ContinuousOn (fun z : ℂ => G ((z:ℂ):ExtPlane)) {z : ℂ | 0 ≤ z.im} :=
      hFc.comp (OnePoint.continuous_coe.continuousOn) hmapsto
    have heq : EqOn (fun z => ((G₀ z:ℂ):ExtPlane)) (fun z : ℂ => G ((z:ℂ):ExtPlane))
        {z : ℂ | 0 ≤ z.im} := fun z hz => (hG₀ z hz).symm
    have hcompcont' : ContinuousOn (fun z : ℂ => ((G₀ z:ℂ):ExtPlane)) {z : ℂ | 0 ≤ z.im} :=
      hcompcont.congr heq
    exact OnePoint.isOpenEmbedding_coe.isInducing.continuousOn_iff.2 hcompcont'
  -- Basic quantities.
  set x₀ : ℝ := z₀.re with hx₀def
  set y₀ : ℝ := z₀.im with hy₀def
  have hy₀ : 0 < y₀ := hz₀
  set w₀ : ℂ := g z₀ with hw₀def
  have hw₀mem : w₀ ∈ upperHalf := hgs ▸ mem_image_of_mem g hz₀
  have hw₀ : 0 < w₀.im := hw₀mem
  obtain ⟨ρ₁, hρ₁pos, hlocρ⟩ := hloc
  -- H5, applied with K := ‖w₀‖ (needs G's continuity at ∞ restricted to the closed half-plane).
  have hH5 : ∃ M : ℝ, ∀ z : ℂ, 0 ≤ z.im → M < ‖z‖ →
      ∀ w : ℂ, G ((z:ℂ):ExtPlane) = ((w:ℂ):ExtPlane) → ‖w₀‖ < ‖w‖ := by
    have hinfcl : extInf ∈ closure (toExt upperHalf) := by rw [hcl_eq]; exact Or.inr rfl
    have hCWA : ContinuousWithinAt G (closure (toExt upperHalf)) extInf := hFc extInf hinfcl
    rw [ContinuousWithinAt, hinf] at hCWA
    have hmem : (toExt (closedBall (0:ℂ) ‖w₀‖))ᶜ ∪ {extInf} ∈ 𝓝 (extInf : ExtPlane) := by
      rw [OnePoint.nhds_infty_eq, mem_sup]
      refine ⟨?_, subset_union_right (mem_singleton _)⟩
      rw [Filter.mem_map]
      have hbase : (closedBall (0:ℂ) ‖w₀‖)ᶜ ∈ Filter.coclosedCompact ℂ :=
        (isCompact_closedBall (0:ℂ) ‖w₀‖).compl_mem_coclosedCompact_of_isClosed isClosed_closedBall
      filter_upwards [hbase] with z hz
      left
      intro hzmem
      obtain ⟨w, hw, hweq⟩ := hzmem
      exact hz (OnePoint.coe_injective hweq ▸ hw)
    have hpre : (G ⁻¹' ((toExt (closedBall (0:ℂ) ‖w₀‖))ᶜ ∪ {extInf})) ∈
        𝓝[closure (toExt upperHalf)] extInf := hCWA hmem
    rw [nhdsWithin, Filter.mem_inf_iff] at hpre
    obtain ⟨s, hs, t, ht, hst⟩ := hpre
    rw [OnePoint.nhds_infty_eq, Filter.mem_sup] at hs
    obtain ⟨hs1, -⟩ := hs
    rw [Filter.mem_map] at hs1
    obtain ⟨C, ⟨hCclosed, hCcompact⟩, hCsub⟩ := Filter.hasBasis_coclosedCompact.mem_iff.mp hs1
    obtain ⟨Mb, hMb⟩ := hCcompact.isBounded.subset_closedBall (0:ℂ)
    refine ⟨Mb, fun z hzmem hzM w hw => ?_⟩
    have hzC : z ∉ C := fun hzC0 => by
      have := hMb hzC0
      rw [mem_closedBall_iff_norm] at this
      simp only [sub_zero] at this
      linarith
    have hzs : (z:ExtPlane) ∈ s := hCsub hzC
    have hzt : (z:ExtPlane) ∈ t := mem_principal.mp ht (hmapsto z hzmem)
    have hzst : (z:ExtPlane) ∈ G ⁻¹' ((toExt (closedBall (0:ℂ) ‖w₀‖))ᶜ ∪ {extInf}) := by
      rw [hst]; exact ⟨hzs, hzt⟩
    simp only [mem_preimage, hw] at hzst
    rcases hzst with h | h
    · by_cases hwK : w ∈ closedBall (0:ℂ) ‖w₀‖
      · exact absurd ⟨w, hwK, rfl⟩ h
      · rw [mem_closedBall_iff_norm] at hwK
        simp only [sub_zero, not_le] at hwK
        linarith
    · exact absurd h (OnePoint.coe_ne_infty w)
  obtain ⟨M₀, hM₀⟩ := hH5
  set M : ℝ := max M₀ 0 with hMdef
  have hMnonneg : 0 ≤ M := le_max_right _ _
  have hM : ∀ z : ℂ, 0 ≤ z.im → M < ‖z‖ → ∀ w : ℂ, G ((z:ℂ):ExtPlane) = ((w:ℂ):ExtPlane) →
      ‖w₀‖ < ‖w‖ := fun z hz hzM w hw => hM₀ z hz (lt_of_le_of_lt (le_max_left _ _) hzM) w hw
  -- Surjectivity + anti-monotonicity of `f`: for `a` large, `f (x₀ - a) > Re w₀ > f (x₀ + a)`.
  have hfarleft : ∃ a₀ : ℝ, ∀ a : ℝ, a₀ < a → w₀.re < f (x₀ - a) := by
    obtain ⟨t, ht⟩ := hfsurj (w₀.re + 1)
    refine ⟨x₀ - t, fun a ha => ?_⟩
    have hlt : x₀ - a < t := by linarith
    have := hanti hlt
    rw [ht] at this
    linarith
  have hfarright : ∃ a₀ : ℝ, ∀ a : ℝ, a₀ < a → f (x₀ + a) < w₀.re := by
    obtain ⟨t, ht⟩ := hfsurj (w₀.re - 1)
    refine ⟨t - x₀, fun a ha => ?_⟩
    have hlt : t < x₀ + a := by linarith
    have := hanti hlt
    rw [ht] at this
    linarith
  obtain ⟨a₁, ha₁⟩ := hfarleft
  obtain ⟨a₂, ha₂⟩ := hfarright
  -- Choose `R` large enough for all of: `R > M + ‖z₀‖`, `√(R²-y₀²) > a₁`, `√(R²-y₀²) > a₂`.
  set c : ℝ := y₀ + M + ‖z₀‖ + |a₁| + |a₂| + 1 with hcdef
  have hcpos : 0 < c := by positivity
  have heq : (Real.sqrt (c^2+y₀^2))^2 - y₀^2 = c^2 := by
    rw [Real.sq_sqrt (by positivity)]; ring
  have hc_lt : c < Real.sqrt (c^2+y₀^2) := by
    have h1 : c^2 < c^2 + y₀^2 := by nlinarith
    have h2 : Real.sqrt (c^2) < Real.sqrt (c^2+y₀^2) := Real.sqrt_lt_sqrt (by positivity) h1
    rwa [Real.sqrt_sq hcpos.le] at h2
  obtain ⟨R, hRy₀, hRM, hRa₁, hRa₂⟩ : ∃ R : ℝ, y₀ < R ∧ M + ‖z₀‖ < R ∧
      a₁ < Real.sqrt (R^2 - y₀^2) ∧ a₂ < Real.sqrt (R^2 - y₀^2) := by
    refine ⟨Real.sqrt (c^2 + y₀^2), ?_, ?_, ?_, ?_⟩
    · have h1 : y₀^2 < c^2 + y₀^2 := by nlinarith
      have h2 : Real.sqrt (y₀^2) < Real.sqrt (c^2+y₀^2) := Real.sqrt_lt_sqrt (by positivity) h1
      rwa [Real.sqrt_sq hy₀.le] at h2
    · have hc' : M + ‖z₀‖ < c := by
        rw [hcdef]; have h1 := abs_nonneg a₁; have h2 := abs_nonneg a₂; linarith
      linarith
    · rw [heq, Real.sqrt_sq hcpos.le]
      have h1 : a₁ ≤ |a₁| := le_abs_self a₁
      have h2 : |a₁| < c := by
        rw [hcdef]; have h3 := abs_nonneg a₂; have h4 := norm_nonneg z₀; linarith
      linarith
    · rw [heq, Real.sqrt_sq hcpos.le]
      have h1 : a₂ ≤ |a₂| := le_abs_self a₂
      have h2 : |a₂| < c := by
        rw [hcdef]; have h3 := abs_nonneg a₁; have h4 := norm_nonneg z₀; linarith
      linarith
  set a : ℝ := Real.sqrt (R^2 - y₀^2) with hadef
  -- `ρ₀` small enough for both `hlocρ` and to stay below `y₀`.
  obtain ⟨ρ₀, hρ₀pos, hρ₀ρ₁, hρ₀y₀⟩ : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < ρ₁ ∧ ρ₀ < y₀ :=
    ⟨min (ρ₁/2) (y₀/2), lt_min (by linarith) (by linarith), lt_of_le_of_lt (min_le_left _ _)
      (by linarith), lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
  -- H1: the radius function.
  obtain ⟨ρR, hρRcont, hρRbd, hρRper, hρRhalf, hρRhi, hρRbdy⟩ :
      ∃ ρR : ℝ → ℝ, Continuous ρR ∧ (∀ t : ℝ, y₀ ≤ ρR t ∧ ρR t ≤ R) ∧ ρR 1 = ρR 0 ∧
        (∀ (t : ℝ) (r : ℝ), 0 ≤ r → r ≤ ρR t →
          0 ≤ ((r:ℂ) * Complex.exp (2 * π * I * (t:ℂ))).im + y₀) ∧
        (∀ t : ℝ, -Real.sin (2 * π * t) ≤ y₀ / R → ρR t = R) ∧
        (∀ t : ℝ, y₀ / R ≤ -Real.sin (2 * π * t) →
          ((ρR t : ℂ) * Complex.exp (2 * π * I * (t:ℂ))).im + y₀ = 0) := by
    set q : ℝ := y₀ / R with hqdef
    have hq0 : 0 < q := div_pos hy₀ (hy₀.trans hRy₀)
    have hq1 : q < 1 := (div_lt_one (hy₀.trans hRy₀)).2 hRy₀
    set ρR : ℝ → ℝ := fun t => y₀ / max (-Real.sin (2 * π * t)) q with hρdef
    have hmaxpos : ∀ t, 0 < max (-Real.sin (2 * π * t)) q := fun t => lt_max_of_lt_right hq0
    have hmaxle1 : ∀ t, max (-Real.sin (2 * π * t)) q ≤ 1 := by
      intro t
      apply max_le
      · linarith [Real.neg_one_le_sin (2 * π * t)]
      · linarith
    have him : ∀ t : ℝ, (Complex.exp (2 * π * I * (t:ℂ))).im = Real.sin (2 * π * t) := by
      intro t
      rw [show (2 * π * I * (t:ℂ) : ℂ) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.exp_ofReal_mul_I_im (2 * π * t)
    have himul : ∀ t r : ℝ,
        ((r:ℂ) * Complex.exp (2 * π * I * (t:ℂ))).im = r * Real.sin (2 * π * t) := by
      intro t r
      rw [Complex.mul_im]
      simp [him t]
    refine ⟨ρR, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply Continuous.div continuous_const
      · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).neg.max continuous_const
      · exact fun t => (hmaxpos t).ne'
    · intro t
      constructor
      · rw [hρdef]
        show y₀ ≤ y₀ / max (-Real.sin (2 * π * t)) q
        rw [le_div_iff₀ (hmaxpos t)]
        nlinarith [hmaxle1 t]
      · rw [hρdef]
        show y₀ / max (-Real.sin (2 * π * t)) q ≤ R
        rw [div_le_iff₀ (hmaxpos t)]
        have hqle : q ≤ max (-Real.sin (2 * π * t)) q := le_max_right _ _
        have hRpos : (0:ℝ) < R := hy₀.trans hRy₀
        have hR' : y₀ ≤ R * max (-Real.sin (2 * π * t)) q := by
          calc y₀ = R * q := by rw [hqdef]; field_simp
          _ ≤ R * max (-Real.sin (2 * π * t)) q := by
                apply mul_le_mul_of_nonneg_left hqle (le_of_lt hRpos)
        linarith
    · show ρR 1 = ρR 0
      rw [hρdef]
      have h1 : Real.sin (2 * π * 1) = 0 := by
        rw [mul_one]; exact Real.sin_two_pi
      have h0 : Real.sin (2 * π * 0) = 0 := by simp
      simp only [h1, h0, neg_zero]
    · intro t r hr0 hrρ
      rw [himul]
      by_cases hs : 0 ≤ Real.sin (2 * π * t)
      · nlinarith
      · rw [not_le] at hs
        have hrρ' : r * max (-Real.sin (2*π*t)) q ≤ y₀ := by
          rw [hρdef] at hrρ
          rw [le_div_iff₀ (hmaxpos t)] at hrρ
          linarith [hrρ]
        have hcomp : r * (-Real.sin (2*π*t)) ≤ r * max (-Real.sin (2*π*t)) q :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) hr0
        nlinarith
    · intro t ht
      rw [hρdef]
      show y₀ / max (-Real.sin (2 * π * t)) q = R
      have hmax : max (-Real.sin (2*π*t)) q = q := max_eq_right ht
      rw [hmax, hqdef]
      field_simp
    · intro t ht
      rw [himul]
      have hmeq : max (-Real.sin (2*π*t)) q = -Real.sin (2*π*t) := max_eq_left ht
      have hsne : Real.sin (2*π*t) ≠ 0 := by
        intro h0
        rw [h0] at ht
        linarith
      have hval : ρR t * Real.sin (2*π*t) = -y₀ := by
        rw [hρdef]
        show y₀ / max (-Real.sin (2 * π * t)) q * Real.sin (2 * π * t) = -y₀
        rw [hmeq]
        field_simp
      linarith [hval]
  -- H6: the chord endpoints.
  obtain ⟨t₁, t₂, ht₁pos, ht₁t₂, ht₂lt1, hsint₁, hsint₂, hcost₁, hcost₂, hhi, hlo⟩ :
      ∃ t₁ t₂ : ℝ, 0 < t₁ ∧ t₁ < t₂ ∧ t₂ < 1 ∧
        Real.sin (2 * π * t₁) = -(y₀/R) ∧ Real.sin (2 * π * t₂) = -(y₀/R) ∧
        Real.cos (2 * π * t₁) = -Real.sqrt (1 - (y₀/R)^2) ∧
        Real.cos (2 * π * t₂) = Real.sqrt (1 - (y₀/R)^2) ∧
        (∀ t ∈ Icc t₁ t₂, y₀/R ≤ -Real.sin (2 * π * t)) ∧
        (∀ t ∈ Icc (0:ℝ) t₁ ∪ Icc t₂ 1, -Real.sin (2 * π * t) ≤ y₀/R) := by
    set q : ℝ := y₀ / R with hqdef
    have hq0 : 0 < q := div_pos hy₀ (hy₀.trans hRy₀)
    have hq1 : q < 1 := (div_lt_one (hy₀.trans hRy₀)).2 hRy₀
    have harcsin_mem : Real.arcsin q ∈ Ioo (0:ℝ) (π/2) := by
      constructor
      · exact Real.arcsin_pos.2 hq0
      · exact Real.arcsin_lt_pi_div_two.2 hq1
    set α : ℝ := Real.arcsin q with hαdef
    have hα0 : 0 < α := harcsin_mem.1
    have hαp2 : α < π/2 := harcsin_mem.2
    have hsinα : Real.sin α = q := Real.sin_arcsin (by linarith) (by linarith)
    set t₁ : ℝ := 1/2 + α/(2*π) with ht1def
    set t₂ : ℝ := 1 - α/(2*π) with ht2def
    have hπpos : 0 < π := Real.pi_pos
    have hφ1 : 2*π*t₁ - π = α := by rw [ht1def]; field_simp; ring
    have hφ2 : 2*π*t₂ - π = π - α := by rw [ht2def]; field_simp; ring
    have hsinshift : ∀ t : ℝ, Real.sin (2*π*t) = -Real.sin (2*π*t - π) := by
      intro t
      linarith [Real.sin_sub_pi (2*π*t)]
    have hbound_hi : ∀ φ ∈ Icc α (π - α), q ≤ Real.sin φ := by
      intro φ hφ
      by_cases hle : φ ≤ π/2
      · have hαφ : α ≤ φ := hφ.1
        have hmono := Real.strictMonoOn_sin.monotoneOn ⟨by linarith, by linarith⟩
          ⟨by linarith, by linarith⟩ hαφ
        linarith [hsinα]
      · rw [not_le] at hle
        have hle2 : α ≤ π - φ := by linarith [hφ.2]
        have hsinref : Real.sin φ = Real.sin (π - φ) := (Real.sin_pi_sub φ).symm
        have hmono := Real.strictMonoOn_sin.monotoneOn
          (show α ∈ Icc (-(π/2)) (π/2) by constructor <;> linarith)
          (show π - φ ∈ Icc (-(π/2)) (π/2) by constructor <;> linarith) hle2
        rw [hsinref]
        linarith [hsinα]
    have hbound_lo_left : ∀ φ ∈ Icc (-π) α, Real.sin φ ≤ q := by
      intro φ hφ
      by_cases hge : -(π/2) ≤ φ
      · have hmono := Real.strictMonoOn_sin.monotoneOn
          (show φ ∈ Icc (-(π/2)) (π/2) by constructor <;> linarith [hφ.2])
          (show α ∈ Icc (-(π/2)) (π/2) by constructor <;> linarith) hφ.2
        linarith [hsinα]
      · rw [not_le] at hge
        have hsinneg : Real.sin φ = -Real.sin (φ + π) := by
          linarith [Real.sin_add_pi φ]
        have hmem : φ + π ∈ Icc (0:ℝ) (π/2) := ⟨by linarith [hφ.1], by linarith⟩
        have hnn : 0 ≤ Real.sin (φ + π) := Real.sin_nonneg_of_nonneg_of_le_pi hmem.1 (by linarith [hmem.2])
        rw [hsinneg]; linarith
    have hbound_lo_right : ∀ φ ∈ Icc (π - α) π, Real.sin φ ≤ q := by
      intro φ hφ
      have hsinref : Real.sin φ = Real.sin (π - φ) := (Real.sin_pi_sub φ).symm
      have hmem : π - φ ∈ Icc (0:ℝ) α := ⟨by linarith [hφ.2], by linarith [hφ.1]⟩
      have hmono := Real.strictMonoOn_sin.monotoneOn
        (show π - φ ∈ Icc (-(π/2)) (π/2) by constructor <;> linarith [hmem.1, hmem.2])
        (show α ∈ Icc (-(π/2)) (π/2) by constructor <;> linarith) hmem.2
      rw [hsinref]; linarith [hsinα]
    refine ⟨t₁, t₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ht1def]; positivity
    · rw [ht1def, ht2def]; nlinarith [hπpos]
    · rw [ht2def]; nlinarith [Real.pi_gt_three]
    · rw [hsinshift, hφ1, hsinα]
    · rw [hsinshift, hφ2, show Real.sin (π - α) = Real.sin α from Real.sin_pi_sub α, hsinα]
    · rw [show (2*π*t₁) = α + π by linarith [hφ1], Real.cos_add_pi,
        Real.cos_eq_sqrt_one_sub_sin_sq (by linarith) (by linarith), hsinα]
    · rw [show (2*π*t₂) = (π - α) + π by linarith [hφ2], Real.cos_add_pi,
        show Real.cos (π - α) = -Real.cos α from Real.cos_pi_sub α,
        Real.cos_eq_sqrt_one_sub_sin_sq (by linarith) (by linarith), hsinα]
      ring
    · intro t ht
      rw [hsinshift]
      have hφmem : 2*π*t - π ∈ Icc α (π - α) := ⟨by
        have hh := ht.1; rw [ht1def] at hh; nlinarith, by
        have hh := ht.2; rw [ht2def] at hh; nlinarith⟩
      linarith [hbound_hi _ hφmem]
    · rintro t (ht | ht)
      · rw [hsinshift]
        have hφmem : 2*π*t - π ∈ Icc (-π) α := ⟨by
          have hh := ht.1; nlinarith, by
          have hh := ht.2; rw [ht1def] at hh; nlinarith⟩
        linarith [hbound_lo_left _ hφmem]
      · rw [hsinshift]
        have hφmem : 2*π*t - π ∈ Icc (π - α) π := ⟨by
          have hh := ht.1; rw [ht2def] at hh; nlinarith, by
          have hh := ht.2; nlinarith⟩
        linarith [hbound_lo_right _ hφmem]
  -- The homotopy.
  set e : ℝ → ℂ := fun t => Complex.exp (2 * π * I * (t:ℂ)) with hedef
  set H : ℝ → ℝ → ℂ := fun s t => G₀ (z₀ + ((1-s) * ρ₀ + s * ρR t) * e t) with hHdef
  -- The homotopy stays in the closed half-plane, avoiding `w₀` after subtracting it.
  have hHmapsto : ∀ s ∈ Icc (0:ℝ) 1, ∀ t : ℝ, 0 ≤ (z₀ + ((1-s)*ρ₀+s*ρR t)*e t).im := by
    intro s hs t
    have hr0 : 0 ≤ (1-s)*ρ₀+s*ρR t := by
      have h1 : 0 ≤ (1-s)*ρ₀ := mul_nonneg (by linarith [hs.2]) hρ₀pos.le
      have h2 : 0 ≤ s*ρR t := mul_nonneg hs.1 (le_trans hy₀.le (hρRbd t).1)
      linarith
    have hrρR : (1-s)*ρ₀+s*ρR t ≤ ρR t := by
      have h1 : (1-s)*ρ₀ ≤ (1-s)*ρR t := mul_le_mul_of_nonneg_left
        (le_trans hρ₀y₀.le (hρRbd t).1) (by linarith [hs.2])
      nlinarith [hs.1, hs.2]
    have hkey := hρRhalf t ((1-s)*ρ₀+s*ρR t) hr0 hrρR
    have hcast : (((1-s)*ρ₀+s*ρR t : ℝ) : ℂ) = ((1-s)*ρ₀+s*ρR t : ℂ) := by push_cast; ring
    rw [hcast] at hkey
    have himeq : (z₀ + ((1-s)*ρ₀+s*ρR t : ℂ) * e t).im
        = (((1-s)*ρ₀+s*ρR t : ℂ) * e t).im + y₀ := by
      rw [Complex.add_im, hy₀def]; ring
    show 0 ≤ (z₀ + ((1-s)*ρ₀+s*ρR t : ℂ) * e t).im
    rw [himeq]
    exact hkey
  have hecont : Continuous e := by rw [hedef]; fun_prop
  have hHcont : ContinuousOn (Function.uncurry H) (Icc 0 1 ×ˢ Icc 0 1) := by
    have hpointcont : Continuous
        (fun p : ℝ × ℝ => z₀ + ((1-p.1)*ρ₀+p.1*ρR p.2) * e p.2) := by
      have h1 : Continuous (fun p : ℝ × ℝ => (1-p.1)*ρ₀+p.1*ρR p.2) := by fun_prop
      fun_prop
    have hmapsto2 : MapsTo (fun p : ℝ × ℝ => z₀ + ((1-p.1)*ρ₀+p.1*ρR p.2) * e p.2)
        (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) {z : ℂ | 0 ≤ z.im} :=
      fun p hp => hHmapsto p.1 hp.1 p.2
    have := hG0cont.comp hpointcont.continuousOn hmapsto2
    exact this
  have he1e0 : e 1 = e 0 := by
    rw [hedef]
    show Complex.exp (2 * π * I * (1:ℂ)) = Complex.exp (2 * π * I * (0:ℂ))
    rw [mul_zero, Complex.exp_zero, mul_one]
    rw [show (2 * (π:ℂ) * I : ℂ) = ((2*π:ℝ):ℂ) * I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I]
    simp [Real.cos_two_pi, Real.sin_two_pi]
  have hHper : ∀ s ∈ Icc (0:ℝ) 1, H s 1 = H s 0 := by
    intro s hs
    rw [hHdef]
    show G₀ (z₀ + ((1-s)*ρ₀+s*ρR 1) * e 1) = G₀ (z₀ + ((1-s)*ρ₀+s*ρR 0) * e 0)
    rw [hρRper, he1e0]
  have hG0z0 : G₀ z₀ = w₀ := by
    have h1 := hG₀ z₀ hz₀.le
    have h2 := hFf z₀ hz₀
    rw [h1] at h2
    exact OnePoint.coe_injective h2
  have hHavoid : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, H s t - w₀ ≠ 0 := by
    intro s hs t ht hcontra
    rw [sub_eq_zero] at hcontra
    simp only [hHdef] at hcontra
    -- hcontra : G₀ (z₀ + ((1-s)*ρ₀+s*ρR t) * e t) = w₀
    have hρRtpos : 0 < ρR t := lt_of_lt_of_le hy₀ (hρRbd t).1
    have hrpos : 0 < (1-s)*ρ₀+s*ρR t := by
      rcases lt_or_eq_of_le hs.2 with hs1 | hs1
      · have h1 : 0 < (1-s)*ρ₀ := mul_pos (by linarith) hρ₀pos
        have h2 : 0 ≤ s*ρR t := mul_nonneg hs.1 hρRtpos.le
        linarith
      · subst hs1
        nlinarith [hρRtpos]
    have hene : e t ≠ 0 := Complex.exp_ne_zero _
    have hrne : ((1-s)*ρ₀+s*ρR t : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have hprodne : ((1-s)*ρ₀+s*ρR t) * e t ≠ 0 := mul_ne_zero hrne hene
    have hzne : z₀ + ((1-s)*ρ₀+s*ρR t) * e t ≠ z₀ := by
      intro heq
      apply hprodne
      linear_combination heq
    have hmem1 : (0:ℝ) ≤ (z₀ + ((1-s)*ρ₀+s*ρR t) * e t).im := hHmapsto s hs t
    have hmem2 : (0:ℝ) ≤ z₀.im := hz₀.le
    have hGeq : G ((z₀ + ((1-s)*ρ₀+s*ρR t) * e t : ℂ):ExtPlane) = G ((z₀:ℂ):ExtPlane) := by
      rw [hG₀ _ hmem1, hG₀ _ hmem2, hcontra, hG0z0]
    have := hFi (hmapsto _ hmem1) (hmapsto _ hmem2) hGeq
    exact hzne (OnePoint.coe_injective this)
  -- W3a + hloc: the big loop (s=1) has the same total winding change as the small loop (s=0).
  have hbig : ∃ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) ∧
      (∀ t ∈ Icc (0:ℝ) 1, Complex.exp (L t) = H 1 t - w₀) ∧ L 1 - L 0 = 2 * π * I := by
    have hH0cont : ContinuousOn (fun t => H 0 t) (Icc (0:ℝ) 1) := by
      have hcomp : ContinuousOn (fun t : ℝ => Function.uncurry H (0, t)) (Icc (0:ℝ) 1) :=
        hHcont.comp (continuousOn_const.prodMk continuousOn_id)
          (fun t ht => ⟨left_mem_Icc.2 zero_le_one, ht⟩)
      simpa [Function.uncurry] using hcomp
    have hH1cont : ContinuousOn (fun t => H 1 t) (Icc (0:ℝ) 1) := by
      have hcomp : ContinuousOn (fun t : ℝ => Function.uncurry H (1, t)) (Icc (0:ℝ) 1) :=
        hHcont.comp (continuousOn_const.prodMk continuousOn_id)
          (fun t ht => ⟨right_mem_Icc.2 zero_le_one, ht⟩)
      simpa [Function.uncurry] using hcomp
    obtain ⟨L₀, hL₀cont, hL₀exp⟩ := exists_continuousOn_log_lift
      (γ := fun t => H 0 t) (w := w₀) hH0cont
      (fun t ht => sub_ne_zero.mp (hHavoid 0 (left_mem_Icc.2 zero_le_one) t ht))
    obtain ⟨L₁, hL₁cont, hL₁exp⟩ := exists_continuousOn_log_lift
      (γ := fun t => H 1 t) (w := w₀) hH1cont
      (fun t ht => sub_ne_zero.mp (hHavoid 1 (right_mem_Icc.2 zero_le_one) t ht))
    -- Connect `L₀`'s change to `hlocρ` via `H 0 t = g (z₀ + ρ₀ * e t)`.
    have hz0pos : ∀ t : ℝ, 0 < (z₀ + (ρ₀:ℂ) * Complex.exp (2 * π * I * (t:ℂ))).im := by
      intro t
      have him2 : (Complex.exp (2 * π * I * (t:ℂ))).im = Real.sin (2 * π * t) := by
        rw [show (2 * π * I * (t:ℂ) : ℂ) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring]
        exact Complex.exp_ofReal_mul_I_im (2 * π * t)
      have heqim : (z₀ + (ρ₀:ℂ) * Complex.exp (2 * π * I * (t:ℂ))).im
          = y₀ + ρ₀ * Real.sin (2 * π * t) := by
        rw [Complex.add_im, Complex.mul_im, him2]
        simp [hy₀def]
      rw [heqim]
      nlinarith [Real.neg_one_le_sin (2 * π * t), hρ₀y₀, hρ₀pos]
    have hG0eqg : ∀ t : ℝ,
        G₀ (z₀ + (ρ₀:ℂ) * Complex.exp (2 * π * I * (t:ℂ)))
          = g (z₀ + (ρ₀:ℂ) * Complex.exp (2 * π * I * (t:ℂ))) := by
      intro t
      have h1 := hG₀ _ (hz0pos t).le
      have h2 := hFf _ (hz0pos t)
      rw [h1] at h2
      exact OnePoint.coe_injective h2
    have hH0eq : ∀ t : ℝ, H 0 t = g (z₀ + (ρ₀:ℂ) * Complex.exp (2 * π * I * (t:ℂ))) := by
      intro t
      rw [hHdef]
      show G₀ (z₀ + ((1-(0:ℝ))*ρ₀+(0:ℝ)*ρR t) * e t)
          = g (z₀ + (ρ₀:ℂ) * Complex.exp (2 * π * I * (t:ℂ)))
      have harg : (z₀ + ((1-(0:ℝ))*ρ₀+(0:ℝ)*ρR t) * e t)
          = z₀ + (ρ₀:ℂ) * Complex.exp (2 * π * I * (t:ℂ)) := by
        rw [hedef]; push_cast; ring
      rw [harg]
      exact hG0eqg t
    have hL₀change : L₀ 1 - L₀ 0 = 2 * π * I := by
      apply hlocρ ρ₀ hρ₀pos hρ₀ρ₁ L₀ hL₀cont
      intro t ht
      rw [← hH0eq t]
      exact hL₀exp t ht
    have hkey := lift_change_eq_of_homotopy hHcont hHper
      (fun s hs t ht => sub_ne_zero.mp (hHavoid s hs t ht)) hL₀cont hL₁cont hL₀exp hL₁exp
    exact ⟨L₁, hL₁cont, hL₁exp, hkey.symm.trans hL₀change⟩
  obtain ⟨Γlift, hΓcont, hΓexp, hΓchange⟩ := hbig
  -- The three-piece split: chord [t₁,t₂] and arcs [0,t₁], [t₂,1].
  have hR0 : 0 < R := hy₀.trans hRy₀
  have him2 : ∀ s : ℝ, (Complex.exp (2 * π * I * (s:ℂ))).im = Real.sin (2 * π * s) := by
    intro s
    rw [show (2 * π * I * (s:ℂ) : ℂ) = ((2 * π * s : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.exp_ofReal_mul_I_im (2 * π * s)
  have hre2 : ∀ s : ℝ, (Complex.exp (2 * π * I * (s:ℂ))).re = Real.cos (2 * π * s) := by
    intro s
    rw [show (2 * π * I * (s:ℂ) : ℂ) = ((2 * π * s : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.exp_ofReal_mul_I_re (2 * π * s)
  have hG0real : ∀ z : ℂ, z.im = 0 → G₀ z = f z.re := by
    intro z hz
    have hzre : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hz]
    have h1 := hG₀ z hz.ge
    have h2 := hf z.re
    rw [← hzre] at h2
    rw [h1] at h2
    exact OnePoint.coe_injective h2
  have hρRt1 : ρR t₁ = R := hρRhi t₁ (by linarith [hsint₁])
  have hρRt2 : ρR t₂ = R := hρRhi t₂ (by linarith [hsint₂])
  have hRne : R ≠ 0 := hR0.ne'
  have hRa_eq : R * Real.sqrt (1 - (y₀/R)^2) = a := by
    have hnn : (0:ℝ) ≤ 1 - (y₀/R)^2 := by
      have hq2 : (y₀/R)^2 ≤ 1 := by
        rw [div_pow, div_le_one (by positivity)]
        nlinarith [hRy₀]
      linarith
    have hsq : (R * Real.sqrt (1 - (y₀/R)^2))^2 = R^2 - y₀^2 := by
      rw [mul_pow, Real.sq_sqrt hnn, div_pow]
      field_simp
    rw [hadef, ← hsq, Real.sqrt_sq (mul_nonneg hR0.le (Real.sqrt_nonneg _))]
  have hH1t1 : H 1 t₁ = (f (x₀ - a) : ℂ) := by
    have hH1eq : H 1 t₁ = G₀ (z₀ + (R:ℂ)*e t₁) := by
      rw [hHdef]
      show G₀ (z₀+((1-(1:ℝ))*ρ₀+(1:ℝ)*ρR t₁)*e t₁) = G₀ (z₀+(R:ℂ)*e t₁)
      congr 2; rw [hρRt1]; push_cast; ring
    have hzim0 : (z₀+(R:ℂ)*e t₁).im = 0 := by
      have hbd := hρRbdy t₁ (hhi t₁ ⟨le_refl t₁, ht₁t₂.le⟩)
      rw [hρRt1] at hbd
      rw [Complex.add_im, show e t₁ = Complex.exp (2*π*I*(t₁:ℂ)) from rfl]
      linarith [hy₀def]
    have hreeq : (z₀+(R:ℂ)*e t₁).re = x₀ - a := by
      rw [Complex.add_re, hedef]
      show z₀.re + ((R:ℂ)*Complex.exp (2*π*I*(t₁:ℂ))).re = x₀ - a
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hre2 t₁, hx₀def, hcost₁]
      ring_nf
      ring_nf at hRa_eq
      linarith [hRa_eq]
    rw [hH1eq, hG0real _ hzim0, hreeq]
  have hH1t2 : H 1 t₂ = (f (x₀ + a) : ℂ) := by
    have hH1eq : H 1 t₂ = G₀ (z₀ + (R:ℂ)*e t₂) := by
      rw [hHdef]
      show G₀ (z₀+((1-(1:ℝ))*ρ₀+(1:ℝ)*ρR t₂)*e t₂) = G₀ (z₀+(R:ℂ)*e t₂)
      congr 2; rw [hρRt2]; push_cast; ring
    have hzim0 : (z₀+(R:ℂ)*e t₂).im = 0 := by
      have hbd := hρRbdy t₂ (hhi t₂ ⟨ht₁t₂.le, le_refl t₂⟩)
      rw [hρRt2] at hbd
      rw [Complex.add_im, show e t₂ = Complex.exp (2*π*I*(t₂:ℂ)) from rfl]
      linarith [hy₀def]
    have hreeq : (z₀+(R:ℂ)*e t₂).re = x₀ + a := by
      rw [Complex.add_re, hedef]
      show z₀.re + ((R:ℂ)*Complex.exp (2*π*I*(t₂:ℂ))).re = x₀ + a
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hre2 t₂, hx₀def, hcost₂]
      ring_nf
      ring_nf at hRa_eq
      linarith [hRa_eq]
    rw [hH1eq, hG0real _ hzim0, hreeq]
  have hu1pos : 0 < f (x₀ - a) - w₀.re := by linarith [ha₁ a hRa₁]
  have hu2neg : f (x₀ + a) - w₀.re < 0 := by linarith [ha₂ a hRa₂]
  have hchord : (Γlift t₂ - Γlift t₁).im ∈ Ioo (-π) 0 := by
    have hγt1 : H 1 t₁ - w₀ = ((f (x₀-a) - w₀.re : ℝ):ℂ) - I*w₀.im := by
      rw [hH1t1]; apply Complex.ext <;> simp
    have hγt2 : H 1 t₂ - w₀ = ((f (x₀+a) - w₀.re : ℝ):ℂ) - I*w₀.im := by
      rw [hH1t2]; apply Complex.ext <;> simp
    have harg1 : -π < Complex.arg (H 1 t₁ - w₀) ∧ Complex.arg (H 1 t₁ - w₀) < 0 := by
      rw [hγt1]; exact arg_ofReal_sub_I_mul_mem w₀.im hw₀ _
    have harg2 : -π < Complex.arg (H 1 t₂ - w₀) ∧ Complex.arg (H 1 t₂ - w₀) < 0 := by
      rw [hγt2]; exact arg_ofReal_sub_I_mul_mem w₀.im hw₀ _
    have hargmono : Complex.arg (H 1 t₂ - w₀) < Complex.arg (H 1 t₁ - w₀) := by
      rw [hγt1, hγt2]
      exact arg_ofReal_sub_I_mul_strictMono w₀.im hw₀ _ _ (by linarith [hu1pos, hu2neg])
    have hslit : ∀ t ∈ Icc t₁ t₂, H 1 t - w₀ ∈ slitPlane := by
      intro t ht
      have hzim0 : (z₀+(ρR t:ℂ)*e t).im = 0 := by
        have hbd := hρRbdy t (hhi t ht)
        rw [Complex.add_im, show e t = Complex.exp (2*π*I*(t:ℂ)) from rfl]
        linarith [hy₀def]
      have hH1eq : H 1 t = G₀ (z₀+(ρR t:ℂ)*e t) := by
        rw [hHdef]
        show G₀ (z₀+((1-(1:ℝ))*ρ₀+(1:ℝ)*ρR t)*e t) = G₀ (z₀+(ρR t:ℂ)*e t)
        congr 2; push_cast; ring
      rw [hH1eq, hG0real _ hzim0]
      rw [Complex.mem_slitPlane_iff]
      right
      simp [hw₀.ne']
    have hH1cont' : ContinuousOn (fun t => H 1 t) (Icc t₁ t₂) := by
      have hcomp : ContinuousOn (fun t : ℝ => Function.uncurry H (1, t)) (Icc t₁ t₂) :=
        hHcont.comp (continuousOn_const.prodMk continuousOn_id)
          (fun t ht => ⟨right_mem_Icc.2 zero_le_one,
            ⟨ht₁pos.le.trans ht.1, ht.2.trans ht₂lt1.le⟩⟩)
      simpa [Function.uncurry] using hcomp
    have hΓcont' : ContinuousOn Γlift (Icc t₁ t₂) :=
      hΓcont.mono (fun t ht => ⟨ht₁pos.le.trans ht.1, ht.2.trans ht₂lt1.le⟩)
    have hΓexp' : ∀ t ∈ Icc t₁ t₂, Complex.exp (Γlift t) = H 1 t - w₀ := fun t ht =>
      hΓexp t ⟨ht₁pos.le.trans ht.1, ht.2.trans ht₂lt1.le⟩
    have hkey := lift_sub_eq_log_sub_log ht₁t₂.le
      (hH1cont'.sub continuousOn_const) hΓcont' hslit hΓexp'
    have himeq := congrArg Complex.im hkey
    simp only [Complex.sub_im, Complex.log_im, Pi.sub_apply] at himeq
    rw [← hw₀def] at himeq
    rw [Complex.sub_im, himeq]
    exact ⟨by linarith [harg2.1, harg1.2], by linarith [hargmono]⟩
  have harcs : (Γlift 1 - Γlift t₂ + (Γlift t₁ - Γlift 0)).im ∈ Ioo (-2*π) (-π) := by
    have hG0im : ∀ z : ℂ, 0 ≤ z.im → 0 ≤ (G₀ z).im := by
      intro z hz
      have h1 := hG₀ z hz
      have h2 : G ((z:ℂ):ExtPlane) ∈ closure (toExt upperHalf) := by
        rw [← hFimg]; exact mem_image_of_mem G (hmapsto z hz)
      rw [h1, hcl_eq] at h2
      rcases h2 with ⟨w, hw, hweq⟩ | h2
      · rw [← OnePoint.coe_injective hweq]; exact hw
      · exact absurd h2 (OnePoint.coe_ne_infty _)
    have henorm : ∀ t : ℝ, ‖e t‖ = 1 := by
      intro t
      rw [hedef]
      show ‖Complex.exp (2*π*I*(t:ℂ))‖ = 1
      rw [Complex.norm_exp]
      have h0 : (2*π*I*(t:ℂ)).re = 0 := by simp
      rw [h0, Real.exp_zero]
    have hH1im : ∀ t : ℝ, 0 ≤ (H 1 t).im := by
      intro t
      rw [hHdef]
      show 0 ≤ (G₀ (z₀ + ((1-(1:ℝ))*ρ₀+(1:ℝ)*ρR t) * e t)).im
      apply hG0im
      have harg : (z₀ + ((1-(1:ℝ))*ρ₀+(1:ℝ)*ρR t) * e t) = z₀ + (ρR t : ℂ) * e t := by
        push_cast; ring
      rw [harg, Complex.add_im]
      have hr0 : (0:ℝ) ≤ ρR t := le_trans hy₀.le (hρRbd t).1
      have hkey := hρRhalf t (ρR t) hr0 le_rfl
      linarith [hy₀def]
    have hzRnorm : ∀ t : ℝ, R - ‖z₀‖ ≤ ‖z₀ + (R:ℂ) * e t‖ := by
      intro t
      have h1 := norm_add_le (-z₀) (z₀ + (R:ℂ)*e t)
      have h2 : -z₀ + (z₀+(R:ℂ)*e t) = (R:ℂ)*e t := by ring
      rw [h2, norm_neg] at h1
      have h3 : ‖(R:ℂ)*e t‖ = R := by
        rw [norm_mul, Complex.norm_real, henorm t, mul_one, Real.norm_of_nonneg hR0.le]
      rw [h3] at h1
      linarith
    have hHarcfar : ∀ t : ℝ, -Real.sin (2*π*t) ≤ y₀/R → ‖w₀‖ < ‖H 1 t‖ := by
      intro t ht
      have hρReq : ρR t = R := hρRhi t ht
      have hH1eq : H 1 t = G₀ (z₀ + (R:ℂ)*e t) := by
        rw [hHdef]
        show G₀ (z₀+((1-(1:ℝ))*ρ₀+(1:ℝ)*ρR t)*e t) = G₀ (z₀+(R:ℂ)*e t)
        congr 2; rw [hρReq]; push_cast; ring
      rw [hH1eq]
      have hzim' : 0 ≤ (z₀+(R:ℂ)*e t).im := by
        rw [Complex.add_im]
        have hkey := hρRhalf t R (hy₀.le.trans hRy₀.le) (hρReq ▸ le_rfl)
        linarith [hy₀def]
      exact hM (z₀+(R:ℂ)*e t) hzim' (by linarith [hzRnorm t, hRM]) (G₀ (z₀+(R:ℂ)*e t)) (hG₀ _ hzim')
    have hL_exp : ∀ t ∈ Icc (0:ℝ) 1, Complex.exp (Γlift t - I*((π:ℝ)/2)) = -I*(H 1 t - w₀) := by
      intro t ht
      have hrw : Γlift t - I*((π:ℝ)/2) = Γlift t + (-(I*((π:ℝ)/2))) := by ring
      rw [hrw, Complex.exp_add, hΓexp t ht]
      have hexpi : Complex.exp (-(I*((π:ℝ)/2))) = -I := by
        rw [show (-(I*((π:ℝ)/2)):ℂ) = ((-(π:ℝ)/2:ℝ):ℂ)*I by push_cast; ring,
          Complex.exp_ofReal_mul_I]
        rw [neg_div, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
        simp
      rw [hexpi]
      ring
    have hΛslit_arc : ∀ t : ℝ, -Real.sin (2*π*t) ≤ y₀/R → -I*(H 1 t - w₀) ∈ slitPlane :=
      fun t ht => neg_I_mul_sub_mem_slitPlane (H 1 t) w₀ (hH1im t) hw₀ (hHarcfar t ht)
    have hH1cont_at : ∀ (S : Set ℝ), S ⊆ Icc (0:ℝ) 1 → ContinuousOn (fun t => H 1 t) S := by
      intro S hsub
      have hcomp : ContinuousOn (fun t : ℝ => Function.uncurry H (1, t)) S :=
        hHcont.comp (continuousOn_const.prodMk continuousOn_id)
          (fun t ht => ⟨right_mem_Icc.2 zero_le_one, hsub ht⟩)
      simpa [Function.uncurry] using hcomp
    have hsub1 : Icc (0:ℝ) t₁ ⊆ Icc (0:ℝ) 1 :=
      fun t ht => ⟨ht.1, ht.2.trans (ht₁t₂.le.trans ht₂lt1.le)⟩
    have hsub2 : Icc t₂ (1:ℝ) ⊆ Icc (0:ℝ) 1 :=
      fun t ht => ⟨(ht₁pos.le.trans ht₁t₂.le).trans ht.1, ht.2⟩
    have hkey1 := lift_sub_eq_log_sub_log ht₁pos.le
      (show ContinuousOn (fun t => -I*(H 1 t - w₀)) (Icc (0:ℝ) t₁) from
        continuousOn_const.mul ((hH1cont_at _ hsub1).sub continuousOn_const))
      (show ContinuousOn (fun t => Γlift t - I*((π:ℝ)/2)) (Icc (0:ℝ) t₁) from
        (hΓcont.mono hsub1).sub continuousOn_const)
      (fun t ht => hΛslit_arc t (hlo t (Or.inl ht)))
      (fun t ht => hL_exp t (hsub1 ht))
    have hkey2 := lift_sub_eq_log_sub_log ht₂lt1.le
      (show ContinuousOn (fun t => -I*(H 1 t - w₀)) (Icc t₂ (1:ℝ)) from
        continuousOn_const.mul ((hH1cont_at _ hsub2).sub continuousOn_const))
      (show ContinuousOn (fun t => Γlift t - I*((π:ℝ)/2)) (Icc t₂ (1:ℝ)) from
        (hΓcont.mono hsub2).sub continuousOn_const)
      (fun t ht => hΛslit_arc t (hlo t (Or.inr ht)))
      (fun t ht => hL_exp t (hsub2 ht))
    have hsimp1 : Γlift t₁ - Γlift 0
        = Complex.log (-I*(H 1 t₁ - w₀)) - Complex.log (-I*(H 1 0 - w₀)) := by
      linear_combination hkey1
    have hsimp2 : Γlift 1 - Γlift t₂
        = Complex.log (-I*(H 1 1 - w₀)) - Complex.log (-I*(H 1 t₂ - w₀)) := by
      linear_combination hkey2
    have hH11eq0 : H 1 1 = H 1 0 := hHper 1 (right_mem_Icc.2 zero_le_one)
    rw [hH11eq0] at hsimp2
    have hsum : (Γlift 1 - Γlift t₂) + (Γlift t₁ - Γlift 0)
        = Complex.log (-I*(H 1 t₁ - w₀)) - Complex.log (-I*(H 1 t₂ - w₀)) := by
      linear_combination hsimp1 + hsimp2
    have himeq2 : (Γlift 1 - Γlift t₂ + (Γlift t₁ - Γlift 0)).im
        = Complex.arg (-I*(H 1 t₁ - w₀)) - Complex.arg (-I*(H 1 t₂ - w₀)) := by
      have h := congrArg Complex.im hsum
      simpa [Complex.add_im, Complex.sub_im, Complex.log_im] using h
    rw [himeq2]
    have hγt1 : -I*(H 1 t₁ - w₀) = -(w₀.im:ℂ) - I*((f (x₀-a) - w₀.re : ℝ):ℂ) := by
      rw [hH1t1]; apply Complex.ext <;> simp
    have hγt2 : -I*(H 1 t₂ - w₀) = -(w₀.im:ℂ) - I*((f (x₀+a) - w₀.re : ℝ):ℂ) := by
      rw [hH1t2]; apply Complex.ext <;> simp
    have harg1 : -π < Complex.arg (-I*(H 1 t₁ - w₀)) ∧ Complex.arg (-I*(H 1 t₁ - w₀)) < -π/2 := by
      rw [hγt1]; exact arg_neg_ofReal_sub_I_mul_mem_pos w₀.im (f (x₀-a) - w₀.re) hw₀ hu1pos
    have harg2 : π/2 < Complex.arg (-I*(H 1 t₂ - w₀)) ∧ Complex.arg (-I*(H 1 t₂ - w₀)) < π := by
      rw [hγt2]; exact arg_neg_ofReal_sub_I_mul_mem_neg w₀.im (f (x₀+a) - w₀.re) hw₀ hu2neg
    exact ⟨by linarith [harg1.1, harg2.2], by linarith [harg1.2, harg2.1]⟩
  -- Total.
  have hcomplex_eq : Γlift 1 - Γlift 0 =
      (Γlift t₂ - Γlift t₁) + (Γlift 1 - Γlift t₂ + (Γlift t₁ - Γlift 0)) := by ring
  have htotal := congrArg Complex.im hcomplex_eq
  rw [Complex.add_im, hΓchange] at htotal
  have h2πI : ((2:ℂ) * (π:ℝ) * I).im = 2 * π := by simp
  rw [h2πI] at htotal
  linarith [hchord.1, hchord.2, harcs.1, harcs.2, htotal, Real.pi_pos]


-- ===== W6 =====

theorem not_cyclicStrictMono_of_cyclicStrictMono_neg {y : Fin 4 → ℝ} (hy : CyclicStrictMono y)
    (hy' : CyclicStrictMono (fun i => y (-i))) : False := by
  obtain ⟨k, hk⟩ := hy
  obtain ⟨k', hk'⟩ := hy'
  have h01 := hk (show (0:Fin 4) < 1 by decide)
  have h12 := hk (show (1:Fin 4) < 2 by decide)
  have h23 := hk (show (2:Fin 4) < 3 by decide)
  have h01' := hk' (show (0:Fin 4) < 1 by decide)
  have h12' := hk' (show (1:Fin 4) < 2 by decide)
  have h23' := hk' (show (2:Fin 4) < 3 by decide)
  have e1 : (-1 : Fin 4) = 3 := by decide
  have e2 : (-2 : Fin 4) = 2 := by decide
  have e3 : (-3 : Fin 4) = 1 := by decide
  fin_cases k <;> fin_cases k' <;> simp_all <;> linarith

-- ===== Shared cyclic-order helper (used by W5core, by (A), and by (B) further down) =====

theorem cyclicStrictMono_of_chain {y : Fin 4 → ℝ} (k' : Fin 4)
    (h1 : y (0 + k') < y (1 + k')) (h2 : y (1 + k') < y (2 + k'))
    (h3 : y (2 + k') < y (3 + k')) : CyclicStrictMono y := by
  refine ⟨k', Fin.strictMono_iff_lt_succ.2 fun i => ?_⟩
  fin_cases i
  · show y ((0 : Fin 4) + k') < y ((1 : Fin 4) + k')
    exact h1
  · show y ((1 : Fin 4) + k') < y ((2 : Fin 4) + k')
    exact h2
  · show y ((2 : Fin 4) + k') < y ((3 : Fin 4) + k')
    exact h3

-- ===== W5core =====

-- W5core
theorem cyclicOrder_preserved_of_isHomeoExtension_of_fixes_infty {g : ℂ → ℂ}
    {G : ExtPlane → ExtPlane} (hG : IsHomeoExtension g upperHalf upperHalf G)
    (hgs : g '' upperHalf = upperHalf) (hinf : G extInf = extInf)
    {z₀ : ℂ} (hz₀ : z₀ ∈ upperHalf)
    (hloc : ∃ ρ₁ > 0, ∀ ρ : ℝ, 0 < ρ → ρ < ρ₁ → ∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Complex.exp (L t) = g (z₀ + ρ * Complex.exp (2 * π * I * t)) - g z₀) →
      L 1 - L 0 = 2 * π * I) :
    ∀ x : Fin 4 → ℝ, CyclicStrictMono x → ∀ y : Fin 4 → ℝ,
      (∀ i, G (((x i : ℝ) : ℂ) : ExtPlane) = (((y i : ℝ) : ℂ) : ExtPlane)) →
        CyclicStrictMono y := by
  obtain ⟨hFf, hFc, hFi, hFimg⟩ := hG
  have hUo : IsOpen upperHalf := isOpen_lt continuous_const continuous_im
  have hFfr : G '' frontier (toExt upperHalf) = frontier (toExt upperHalf) :=
    IsHomeoExtension.image_frontier hUo hUo hgs ⟨hFf, hFc, hFi, hFimg⟩
  have hfr_eq : frontier (toExt upperHalf) = toExt {z : ℂ | z.im = 0} ∪ {extInf} :=
    scExt_frontier_toExt_upperHalf
  -- Extract `f : ℝ → ℝ`, the boundary correspondence.
  have hex : ∀ t : ℝ, ∃ s : ℝ, G (((t:ℝ):ℂ):ExtPlane) = (((s:ℝ):ℂ):ExtPlane) := by
    intro t
    have hmemfr : (((t:ℝ):ℂ):ExtPlane) ∈ frontier (toExt upperHalf) := by
      rw [hfr_eq]; exact Or.inl ⟨(t:ℂ), rfl, rfl⟩
    have : G (((t:ℝ):ℂ):ExtPlane) ∈ frontier (toExt upperHalf) := hFfr ▸ mem_image_of_mem G hmemfr
    rw [hfr_eq] at this
    rcases this with ⟨z, hz, hzeq⟩ | hz
    · refine ⟨z.re, ?_⟩
      have hzre : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hz)
      rw [← hzeq]
      exact congrArg (fun w : ℂ => (w : ExtPlane)) hzre
    · exfalso
      have hGinf : G (((t:ℝ):ℂ):ExtPlane) = G extInf := by rw [hz, hinf]
      have hmemcl : (((t:ℝ):ℂ):ExtPlane) ∈ closure (toExt upperHalf) := frontier_subset_closure hmemfr
      have hinfmemcl : extInf ∈ closure (toExt upperHalf) :=
        frontier_subset_closure (hfr_eq ▸ Or.inr rfl)
      have := hFi hmemcl hinfmemcl hGinf
      exact OnePoint.coe_ne_infty _ this
  choose f hf using hex
  have hmapsto : ∀ t : ℝ, (((t:ℝ):ℂ):ExtPlane) ∈ closure (toExt upperHalf) := fun t =>
    frontier_subset_closure (by rw [hfr_eq]; exact Or.inl ⟨(t:ℂ), rfl, rfl⟩)
  have hfinj : Function.Injective f := by
    intro t1 t2 heq
    have hG12 : G (((t1:ℝ):ℂ):ExtPlane) = G (((t2:ℝ):ℂ):ExtPlane) := by
      rw [hf t1, hf t2, heq]
    have hmem_eq := hFi (hmapsto t1) (hmapsto t2) hG12
    exact Complex.ofReal_injective (OnePoint.coe_injective hmem_eq)
  have hfcont : Continuous f := by
    have hιcont : Continuous (fun t : ℝ => (((t:ℝ):ℂ):ExtPlane)) :=
      OnePoint.continuous_coe.comp Complex.continuous_ofReal
    have hcompcont : Continuous (fun t => G (((t:ℝ):ℂ):ExtPlane)) := hFc.comp_continuous hιcont hmapsto
    have heq : (fun t => G (((t:ℝ):ℂ):ExtPlane)) = fun t => (((f t:ℝ):ℂ):ExtPlane) := funext hf
    rw [heq] at hcompcont
    have hemb : Topology.IsInducing (fun t : ℝ => (((t:ℝ):ℂ):ExtPlane)) :=
      (OnePoint.isOpenEmbedding_coe.isInducing).comp
        (Complex.isometry_ofReal.isEmbedding.isInducing)
    exact hemb.continuous_iff.2 hcompcont
  rcases hfcont.strictMono_of_inj hfinj with hmono | hanti
  · -- mono case
    refine fun x hx y hy => ?_
    have hyf : ∀ i, y i = f (x i) := by
      intro i
      have heq := hy i
      rw [hf] at heq
      exact_mod_cast (OnePoint.coe_injective heq).symm
    obtain ⟨k, hk⟩ := hx
    have h01 : x (0 + k) < x (1 + k) := hk (show (0 : Fin 4) < 1 by decide)
    have h12 : x (1 + k) < x (2 + k) := hk (show (1 : Fin 4) < 2 by decide)
    have h23 : x (2 + k) < x (3 + k) := hk (show (2 : Fin 4) < 3 by decide)
    refine cyclicStrictMono_of_chain k ?_ ?_ ?_
    · rw [hyf, hyf]; exact hmono h01
    · rw [hyf, hyf]; exact hmono h12
    · rw [hyf, hyf]; exact hmono h23
  · -- anti case: derive a contradiction using `hloc`.
    exfalso
    have hclosure_eq : closure (toExt upperHalf) = toExt {z : ℂ | 0 ≤ z.im} ∪ {extInf} :=
      scExt_closure_toExt_upperHalf
    exact wn_false_of_strictAnti_boundary ⟨hFf, hFc, hFi, hFimg⟩ hgs hinf hz₀ hloc
      f hfcont hfinj hf hanti hFf hFc hFi hFimg hUo hfr_eq hFfr hclosure_eq

-- ===== (A): dichotomy for self-homeomorphisms of `OnePoint R`, plus boundary transport =====

/-- `t ↦ -1/t`, extended to swap `0` and `∞`. -/
def onePointRealFlip (w : OnePoint ℝ) : OnePoint ℝ :=
  w.elim ((0 : ℝ) : OnePoint ℝ) (fun t => if t = 0 then (OnePoint.infty : OnePoint ℝ) else (((-1 / t : ℝ)) :
    OnePoint ℝ))

theorem onePointRealFlip_infty : onePointRealFlip OnePoint.infty = ((0 : ℝ) : OnePoint ℝ) := rfl

theorem onePointRealFlip_coe_of_ne {t : ℝ} (ht : t ≠ 0) :
    onePointRealFlip (t : OnePoint ℝ) = ((-1 / t : ℝ) : OnePoint ℝ) := by
  simp [onePointRealFlip, ht]

theorem onePointRealFlip_coe_zero : onePointRealFlip ((0 : ℝ) : OnePoint ℝ) = OnePoint.infty := by
  simp [onePointRealFlip]

theorem onePointRealFlip_involutive : Function.Involutive onePointRealFlip := by
  intro w
  induction w with
  | infty => rw [onePointRealFlip_infty, onePointRealFlip_coe_zero]
  | coe t =>
    by_cases ht : t = 0
    · subst ht; rw [onePointRealFlip_coe_zero, onePointRealFlip_infty]
    · rw [onePointRealFlip_coe_of_ne ht]
      have ht' : (-1 / t : ℝ) ≠ 0 := by
        simp only [ne_eq, div_eq_zero_iff, neg_eq_zero, one_ne_zero, false_or]
        exact ht
      rw [onePointRealFlip_coe_of_ne ht']
      congr 1
      field_simp

theorem continuous_onePointRealFlip : Continuous onePointRealFlip := by
  rw [OnePoint.continuous_iff]
  constructor
  · -- Tendsto at `∞`.
    rw [onePointRealFlip_infty, coclosedCompact_eq_cocompact, ← cobounded_eq_cocompact]
    have hne : ∀ᶠ t : ℝ in cobounded ℝ, t ≠ 0 := eventually_ne_cobounded 0
    have heq : (fun t : ℝ => onePointRealFlip (t : OnePoint ℝ)) =ᶠ[cobounded ℝ]
        fun t => ((-1 / t : ℝ) : OnePoint ℝ) := by
      filter_upwards [hne] with t ht
      exact onePointRealFlip_coe_of_ne ht
    have hlim : Tendsto (fun t : ℝ => (-1 / t : ℝ)) (cobounded ℝ) (𝓝 (0 : ℝ)) := by
      have h0 : Tendsto (fun t : ℝ => t⁻¹) (cobounded ℝ) (𝓝 (0 : ℝ)) := tendsto_inv₀_cobounded
      have h1 := h0.neg
      simpa [neg_div, one_div] using h1
    have hlim2 : Tendsto (fun t : ℝ => ((-1 / t : ℝ) : OnePoint ℝ)) (cobounded ℝ)
        (𝓝 (((0 : ℝ) : OnePoint ℝ))) := (OnePoint.continuous_coe.tendsto (0 : ℝ)).comp hlim
    exact hlim2.congr' heq.symm
  · -- Continuity on `ℝ`.
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    by_cases ht₀ : t₀ = 0
    · subst ht₀
      show Tendsto (fun t : ℝ => onePointRealFlip (t : OnePoint ℝ)) (𝓝 (0 : ℝ))
        (𝓝 (onePointRealFlip ((0 : ℝ) : OnePoint ℝ)))
      rw [onePointRealFlip_coe_zero, OnePoint.nhds_infty_eq, ← nhdsNE_sup_pure (0 : ℝ)]
      refine Tendsto.sup ?_ ?_
      · have heq : (fun t : ℝ => ((-1 / t : ℝ) : OnePoint ℝ)) =ᶠ[𝓝[≠] (0 : ℝ)]
            fun t => onePointRealFlip (t : OnePoint ℝ) := by
          filter_upwards [self_mem_nhdsWithin] with t ht
          exact (onePointRealFlip_coe_of_ne ht).symm
        have hpole : Tendsto (fun t : ℝ => (-1 / t : ℝ)) (𝓝[≠] (0 : ℝ)) (coclosedCompact ℝ) := by
          rw [coclosedCompact_eq_cocompact, ← cobounded_eq_cocompact,
            ← tendsto_norm_atTop_iff_cobounded]
          have heq : (fun t : ℝ => ‖(-1 / t : ℝ)‖) = fun t : ℝ => ‖t⁻¹‖ := by
            funext t; rw [norm_div, norm_neg, norm_one, one_div, norm_inv]
          rw [heq]
          exact tendsto_norm_inv_nhdsNE_zero_atTop
        exact ((tendsto_map.comp hpole).mono_right le_sup_left).congr' heq
      · exact tendsto_pure_left.2 fun s hs => by
          rw [onePointRealFlip_coe_zero]
          exact mem_pure.1 (mem_sup.1 hs).2
    · have hcontfn : ContinuousAt (fun t : ℝ => (-1 / t : ℝ)) t₀ := by
        exact continuousAt_const.div continuousAt_id ht₀
      have hcont : ContinuousAt (fun t : ℝ => ((-1 / t : ℝ) : OnePoint ℝ)) t₀ :=
        OnePoint.continuous_coe.continuousAt.comp hcontfn
      have hne : ∀ᶠ t in 𝓝 t₀, t ≠ 0 := eventually_ne_nhds ht₀
      have heq : (fun t : ℝ => ((-1 / t : ℝ) : OnePoint ℝ)) =ᶠ[𝓝 t₀]
          fun t => onePointRealFlip (t : OnePoint ℝ) := by
        filter_upwards [hne] with t ht
        exact (onePointRealFlip_coe_of_ne ht).symm
      exact hcont.congr heq

/-- `onePointRealFlip` as a self-homeomorphism of `OnePoint ℝ`. -/
def onePointRealFlipHomeomorph : OnePoint ℝ ≃ₜ OnePoint ℝ :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    { toFun := onePointRealFlip
      invFun := onePointRealFlip
      left_inv := onePointRealFlip_involutive
      right_inv := onePointRealFlip_involutive })
    continuous_onePointRealFlip

@[simp] theorem onePointRealFlipHomeomorph_apply (w : OnePoint ℝ) :
    onePointRealFlipHomeomorph w = onePointRealFlip w := rfl

/-- If `h` fixes `∞`, it restricts to a self-homeomorphism of `ℝ`. -/
theorem exists_real_of_fixes_infty {h : OnePoint ℝ ≃ₜ OnePoint ℝ}
    (hinf : h OnePoint.infty = OnePoint.infty) :
    ∃ f : ℝ → ℝ, Continuous f ∧ Function.Injective f ∧
      ∀ t : ℝ, h (t : OnePoint ℝ) = (f t : OnePoint ℝ) := by
  have hex : ∀ t : ℝ, ∃ s : ℝ, (s : OnePoint ℝ) = h (t : OnePoint ℝ) := by
    intro t
    apply OnePoint.ne_infty_iff_exists.mp
    intro heq
    exact OnePoint.coe_ne_infty t (h.injective (heq.trans hinf.symm))
  choose f hf using hex
  refine ⟨f, ?_, ?_, fun t => (hf t).symm⟩
  · have heq : ((↑) : ℝ → OnePoint ℝ) ∘ f = fun t : ℝ => h (t : OnePoint ℝ) := by
      funext t; exact hf t
    have hcont : Continuous (fun t : ℝ => h (t : OnePoint ℝ)) :=
      h.continuous.comp OnePoint.continuous_coe
    rw [← heq] at hcont
    exact OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff.2 hcont
  · intro t1 t2 ht
    have h1 : (t1 : OnePoint ℝ) = (t2 : OnePoint ℝ) := by
      apply h.injective; rw [← hf t1, ← hf t2, ht]
    exact OnePoint.coe_injective h1

/-- **(A) core**: the dichotomy for a self-homeomorphism of `OnePoint ℝ` that fixes `∞`, in the
same uniform (`∀ x y, …`) shape as the main theorem. -/
theorem dichotomy_fixInfty {h : OnePoint ℝ ≃ₜ OnePoint ℝ}
    (hinf : h OnePoint.infty = OnePoint.infty) :
    (∀ x : Fin 4 → ℝ, CyclicStrictMono x → ∀ y : Fin 4 → ℝ,
      (∀ i, h (x i : OnePoint ℝ) = (y i : OnePoint ℝ)) → CyclicStrictMono y) ∨
    (∀ x : Fin 4 → ℝ, CyclicStrictMono x → ∀ y : Fin 4 → ℝ,
      (∀ i, h (x i : OnePoint ℝ) = (y i : OnePoint ℝ)) → CyclicStrictMono (fun i => y (-i))) := by
  obtain ⟨f, hfcont, hfinj, hf⟩ := exists_real_of_fixes_infty hinf
  rcases hfcont.strictMono_of_inj hfinj with hmono | hanti
  · refine Or.inl fun x hx y hy => ?_
    have hyf : ∀ i, y i = f (x i) := by
      intro i
      have heq := hy i
      rw [hf] at heq
      exact_mod_cast (OnePoint.coe_injective heq).symm
    obtain ⟨k, hk⟩ := hx
    have h01 : x (0 + k) < x (1 + k) := hk (show (0 : Fin 4) < 1 by decide)
    have h12 : x (1 + k) < x (2 + k) := hk (show (1 : Fin 4) < 2 by decide)
    have h23 : x (2 + k) < x (3 + k) := hk (show (2 : Fin 4) < 3 by decide)
    refine cyclicStrictMono_of_chain k ?_ ?_ ?_
    · rw [hyf, hyf]; exact hmono h01
    · rw [hyf, hyf]; exact hmono h12
    · rw [hyf, hyf]; exact hmono h23
  · refine Or.inr fun x hx y hy => ?_
    have hyf : ∀ i, y i = f (x i) := by
      intro i
      have heq := hy i
      rw [hf] at heq
      exact_mod_cast (OnePoint.coe_injective heq).symm
    obtain ⟨k, hk⟩ := hx
    have h01 : x (0 + k) < x (1 + k) := hk (show (0 : Fin 4) < 1 by decide)
    have h12 : x (1 + k) < x (2 + k) := hk (show (1 : Fin 4) < 2 by decide)
    have h23 : x (2 + k) < x (3 + k) := hk (show (2 : Fin 4) < 3 by decide)
    refine cyclicStrictMono_of_chain (1 - k) ?_ ?_ ?_
    · have e1 : -((0 : Fin 4) + (1 - k)) = 3 + k := by fin_cases k <;> decide
      have e2 : -((1 : Fin 4) + (1 - k)) = 2 + k := by fin_cases k <;> decide
      show y (-((0 : Fin 4) + (1 - k))) < y (-((1 : Fin 4) + (1 - k)))
      rw [e1, e2, hyf, hyf]; exact hanti h23
    · have e1 : -((1 : Fin 4) + (1 - k)) = 2 + k := by fin_cases k <;> decide
      have e2 : -((2 : Fin 4) + (1 - k)) = 1 + k := by fin_cases k <;> decide
      show y (-((1 : Fin 4) + (1 - k))) < y (-((2 : Fin 4) + (1 - k)))
      rw [e1, e2, hyf, hyf]; exact hanti h12
    · have e1 : -((2 : Fin 4) + (1 - k)) = 1 + k := by fin_cases k <;> decide
      have e2 : -((3 : Fin 4) + (1 - k)) = 0 + k := by fin_cases k <;> decide
      show y (-((2 : Fin 4) + (1 - k))) < y (-((3 : Fin 4) + (1 - k)))
      rw [e1, e2, hyf, hyf]; exact hanti h01

/-! ### Reduction of the general case to the case fixing `∞`

We conjugate `h` by an explicit positive-determinant real Möbius self-map `M` of `OnePoint ℝ`
sending `∞` to the point `r` that `h` sends to `∞`; then `H := M.trans h` fixes `∞`. The algebra
below (`mobiusReal_sub_eq` / `mobiusReal_lt_of_same_side` / `mobiusReal_lt_of_opp_side`, shared
with theorem (B) further down in this file) shows `M⁻¹`, applied to the given cyclically-ordered
`x`, again produces a `CyclicStrictMono` tuple `x'` — never the reversed alternative, matching the
fact that a positive-determinant real Möbius map is never order-reversing. -/

theorem mobiusReal_sub_eq {a b c d : ℝ} (t₁ t₂ : ℝ) (h₁ : c * t₁ + d ≠ 0) (h₂ : c * t₂ + d ≠ 0) :
    (a * t₂ + b) / (c * t₂ + d) - (a * t₁ + b) / (c * t₁ + d) =
      (a * d - b * c) * (t₂ - t₁) / ((c * t₁ + d) * (c * t₂ + d)) := by
  rw [div_sub_div _ _ h₂ h₁, div_eq_div_iff (mul_ne_zero h₂ h₁) (mul_ne_zero h₁ h₂)]
  ring

theorem mobiusReal_lt_of_same_side {a b c d : ℝ} (hdet : 0 < a * d - b * c) {t₁ t₂ : ℝ}
    (h₁ : c * t₁ + d ≠ 0) (h₂ : c * t₂ + d ≠ 0) (hlt : t₁ < t₂)
    (hsame : 0 < (c * t₁ + d) * (c * t₂ + d)) :
    (a * t₁ + b) / (c * t₁ + d) < (a * t₂ + b) / (c * t₂ + d) := by
  have hpos : 0 < (a * d - b * c) * (t₂ - t₁) / ((c * t₁ + d) * (c * t₂ + d)) :=
    div_pos (mul_pos hdet (sub_pos.2 hlt)) hsame
  linarith [mobiusReal_sub_eq (a := a) (b := b) (c := c) (d := d) t₁ t₂ h₁ h₂, hpos]

theorem mobiusReal_lt_of_opp_side {a b c d : ℝ} (hdet : 0 < a * d - b * c) {t₁ t₂ : ℝ}
    (h₁ : c * t₁ + d ≠ 0) (h₂ : c * t₂ + d ≠ 0) (hlt : t₁ < t₂)
    (hopp : (c * t₁ + d) * (c * t₂ + d) < 0) :
    (a * t₂ + b) / (c * t₂ + d) < (a * t₁ + b) / (c * t₁ + d) := by
  have hneg : (a * d - b * c) * (t₂ - t₁) / ((c * t₁ + d) * (c * t₂ + d)) < 0 :=
    div_neg_of_pos_of_neg (mul_pos hdet (sub_pos.2 hlt)) hopp
  linarith [mobiusReal_sub_eq (a := a) (b := b) (c := c) (d := d) t₁ t₂ h₁ h₂, hneg]

/-- `x' i := 1 / (r - x i)` (the value of the positive-determinant real Möbius map with
coefficients `(0,1,-1,r)`, applied to `x i`) is again `CyclicStrictMono`, given `x` is and every
`x i ≠ r`. This is the real-only core of theorem (B)'s pole-location case split, specialized to
this one fixed map, and reproduced here so this file stays self-contained. -/
theorem cyclicStrictMono_invMap {r : ℝ} {x : Fin 4 → ℝ} (hx : CyclicStrictMono x)
    (hne : ∀ i, x i ≠ r) : CyclicStrictMono (fun i => 1 / (r - x i)) := by
  set x' : Fin 4 → ℝ := fun i => 1 / (r - x i) with hx'def
  have hdet : (0:ℝ) < 0 * r - 1 * (-1) := by norm_num
  have hden : ∀ i, (-1:ℝ) * x i + r ≠ 0 := by
    intro i hc
    exact hne i (by linarith)
  have hx'eq : ∀ i, x' i = (0 * x i + 1) / ((-1) * x i + r) := by
    intro i; rw [hx'def]; ring
  obtain ⟨k, hk⟩ := hx
  have h01 : x (0 + k) < x (1 + k) := hk (show (0 : Fin 4) < 1 by decide)
  have h12 : x (1 + k) < x (2 + k) := hk (show (1 : Fin 4) < 2 by decide)
  have h23 : x (2 + k) < x (3 + k) := hk (show (2 : Fin 4) < 3 by decide)
  set x0 := x (0 + k) with hx0def
  set x1 := x (1 + k) with hx1def
  set x2 := x (2 + k) with hx2def
  set x3 := x (3 + k) with hx3def
  have hd0 : (-1:ℝ) * x0 + r ≠ 0 := hden _
  have hd1 : (-1:ℝ) * x1 + r ≠ 0 := hden _
  have hd2 : (-1:ℝ) * x2 + r ≠ 0 := hden _
  have hd3 : (-1:ℝ) * x3 + r ≠ 0 := hden _
  have hy0eq : x' (0 + k) = (0 * x0 + 1) / ((-1) * x0 + r) := hx'eq _
  have hy1eq : x' (1 + k) = (0 * x1 + 1) / ((-1) * x1 + r) := hx'eq _
  have hy2eq : x' (2 + k) = (0 * x2 + 1) / ((-1) * x2 + r) := hx'eq _
  have hy3eq : x' (3 + k) = (0 * x3 + 1) / ((-1) * x3 + r) := hx'eq _
  have hsamepos : ∀ {t₁ t₂ : ℝ}, r < t₁ → r < t₂ → 0 < ((-1:ℝ) * t₁ + r) * ((-1) * t₂ + r) := by
    intro t₁ t₂ h1 h2; nlinarith
  have hsameneg : ∀ {t₁ t₂ : ℝ}, t₁ < r → t₂ < r → 0 < ((-1:ℝ) * t₁ + r) * ((-1) * t₂ + r) := by
    intro t₁ t₂ h1 h2; nlinarith
  have hopp : ∀ {t₁ t₂ : ℝ}, t₁ < r → r < t₂ → ((-1:ℝ) * t₁ + r) * ((-1) * t₂ + r) < 0 := by
    intro t₁ t₂ h1 h2; nlinarith
  rcases lt_or_gt_of_ne (hne (0 + k)) with h0 | h0
  · rcases lt_or_gt_of_ne (hne (1 + k)) with h1 | h1
    · rcases lt_or_gt_of_ne (hne (2 + k)) with h2 | h2
      · rcases lt_or_gt_of_ne (hne (3 + k)) with h3 | h3
        · -- m = 4 : all four values `< r`.
          have g1 : x' (0 + k) < x' (1 + k) := by
            rw [hy0eq, hy1eq]; exact mobiusReal_lt_of_same_side hdet hd0 hd1 h01 (hsameneg h0 h1)
          have g2 : x' (1 + k) < x' (2 + k) := by
            rw [hy1eq, hy2eq]; exact mobiusReal_lt_of_same_side hdet hd1 hd2 h12 (hsameneg h1 h2)
          have g3 : x' (2 + k) < x' (3 + k) := by
            rw [hy2eq, hy3eq]; exact mobiusReal_lt_of_same_side hdet hd2 hd3 h23 (hsameneg h2 h3)
          exact cyclicStrictMono_of_chain k g1 g2 g3
        · -- m = 3 : `x2 < r < x3`.
          have e1 : (0 : Fin 4) + (k + 3) = 3 + k := by fin_cases k <;> decide
          have e2 : (1 : Fin 4) + (k + 3) = 0 + k := by fin_cases k <;> decide
          have e3 : (2 : Fin 4) + (k + 3) = 1 + k := by fin_cases k <;> decide
          have e4 : (3 : Fin 4) + (k + 3) = 2 + k := by fin_cases k <;> decide
          have g1 : x' (0 + (k + 3)) < x' (1 + (k + 3)) := by
            rw [e1, e2, hy3eq, hy0eq]
            exact mobiusReal_lt_of_opp_side hdet hd0 hd3 (h01.trans (h12.trans h23)) (hopp h0 h3)
          have g2 : x' (1 + (k + 3)) < x' (2 + (k + 3)) := by
            rw [e2, e3, hy0eq, hy1eq]
            exact mobiusReal_lt_of_same_side hdet hd0 hd1 h01 (hsameneg h0 h1)
          have g3 : x' (2 + (k + 3)) < x' (3 + (k + 3)) := by
            rw [e3, e4, hy1eq, hy2eq]
            exact mobiusReal_lt_of_same_side hdet hd1 hd2 h12 (hsameneg h1 h2)
          exact cyclicStrictMono_of_chain (k + 3) g1 g2 g3
      · -- m = 2 : `x1 < r < x2`.
        have hx3p : r < x3 := h2.trans h23
        have e1 : (0 : Fin 4) + (k + 2) = 2 + k := by fin_cases k <;> decide
        have e2 : (1 : Fin 4) + (k + 2) = 3 + k := by fin_cases k <;> decide
        have e3 : (2 : Fin 4) + (k + 2) = 0 + k := by fin_cases k <;> decide
        have e4 : (3 : Fin 4) + (k + 2) = 1 + k := by fin_cases k <;> decide
        have g1 : x' (0 + (k + 2)) < x' (1 + (k + 2)) := by
          rw [e1, e2, hy2eq, hy3eq]
          exact mobiusReal_lt_of_same_side hdet hd2 hd3 h23 (hsamepos h2 hx3p)
        have g2 : x' (1 + (k + 2)) < x' (2 + (k + 2)) := by
          rw [e2, e3, hy3eq, hy0eq]
          exact mobiusReal_lt_of_opp_side hdet hd0 hd3 (h01.trans (h12.trans h23)) (hopp h0 hx3p)
        have g3 : x' (2 + (k + 2)) < x' (3 + (k + 2)) := by
          rw [e3, e4, hy0eq, hy1eq]
          exact mobiusReal_lt_of_same_side hdet hd0 hd1 h01 (hsameneg h0 h1)
        exact cyclicStrictMono_of_chain (k + 2) g1 g2 g3
    · -- m = 1 : `x0 < r < x1`.
      have hx2p : r < x2 := h1.trans h12
      have hx3p : r < x3 := hx2p.trans h23
      have e1 : (0 : Fin 4) + (k + 1) = 1 + k := by fin_cases k <;> decide
      have e2 : (1 : Fin 4) + (k + 1) = 2 + k := by fin_cases k <;> decide
      have e3 : (2 : Fin 4) + (k + 1) = 3 + k := by fin_cases k <;> decide
      have e4 : (3 : Fin 4) + (k + 1) = 0 + k := by fin_cases k <;> decide
      have g1 : x' (0 + (k + 1)) < x' (1 + (k + 1)) := by
        rw [e1, e2, hy1eq, hy2eq]
        exact mobiusReal_lt_of_same_side hdet hd1 hd2 h12 (hsamepos h1 hx2p)
      have g2 : x' (1 + (k + 1)) < x' (2 + (k + 1)) := by
        rw [e2, e3, hy2eq, hy3eq]
        exact mobiusReal_lt_of_same_side hdet hd2 hd3 h23 (hsamepos hx2p hx3p)
      have g3 : x' (2 + (k + 1)) < x' (3 + (k + 1)) := by
        rw [e3, e4, hy3eq, hy0eq]
        exact mobiusReal_lt_of_opp_side hdet hd0 hd3 (h01.trans (h12.trans h23)) (hopp h0 hx3p)
      exact cyclicStrictMono_of_chain (k + 1) g1 g2 g3
  · -- m = 0 : all four values `> r`.
    have hx1p : r < x1 := h0.trans h01
    have hx2p : r < x2 := hx1p.trans h12
    have hx3p : r < x3 := hx2p.trans h23
    have g1 : x' (0 + k) < x' (1 + k) := by
      rw [hy0eq, hy1eq]; exact mobiusReal_lt_of_same_side hdet hd0 hd1 h01 (hsamepos h0 hx1p)
    have g2 : x' (1 + k) < x' (2 + k) := by
      rw [hy1eq, hy2eq]; exact mobiusReal_lt_of_same_side hdet hd1 hd2 h12 (hsamepos hx1p hx2p)
    have g3 : x' (2 + k) < x' (3 + k) := by
      rw [hy2eq, hy3eq]; exact mobiusReal_lt_of_same_side hdet hd2 hd3 h23 (hsamepos hx2p hx3p)
    exact cyclicStrictMono_of_chain k g1 g2 g3

/-- **(A)**: a self-homeomorphism of `OnePoint ℝ` is either cyclic-order preserving on every
real 4-tuple, or cyclic-order reversing on every real 4-tuple. -/
theorem dichotomy_onePoint_homeomorphism (h : OnePoint ℝ ≃ₜ OnePoint ℝ) :
    (∀ x : Fin 4 → ℝ, CyclicStrictMono x → ∀ y : Fin 4 → ℝ,
      (∀ i, h (x i : OnePoint ℝ) = (y i : OnePoint ℝ)) → CyclicStrictMono y) ∨
    (∀ x : Fin 4 → ℝ, CyclicStrictMono x → ∀ y : Fin 4 → ℝ,
      (∀ i, h (x i : OnePoint ℝ) = (y i : OnePoint ℝ)) → CyclicStrictMono (fun i => y (-i))) := by
  by_cases hinf : h OnePoint.infty = OnePoint.infty
  · exact dichotomy_fixInfty hinf
  · have hsinf : h.symm OnePoint.infty ≠ OnePoint.infty := by
      intro heq
      apply hinf
      have hcg := congrArg h heq
      rw [h.apply_symm_apply] at hcg
      exact hcg.symm
    obtain ⟨r, hr⟩ := OnePoint.ne_infty_iff_exists.mp hsinf
    have hhr : h (r : OnePoint ℝ) = OnePoint.infty := by rw [hr, h.apply_symm_apply]
    set M : OnePoint ℝ ≃ₜ OnePoint ℝ :=
      onePointRealFlipHomeomorph.trans (Homeomorph.onePointCongr (Homeomorph.addRight r))
      with hMdef
    have hM_coe : ∀ {s : ℝ}, s ≠ 0 → M ((s : ℝ) : OnePoint ℝ) = ((-1 / s + r : ℝ) : OnePoint ℝ) := by
      intro s hs
      rw [hMdef, Homeomorph.trans_apply, onePointRealFlipHomeomorph_apply,
        onePointRealFlip_coe_of_ne hs]
      rfl
    have hM_inf : M OnePoint.infty = (r : OnePoint ℝ) := by
      rw [hMdef, Homeomorph.trans_apply, onePointRealFlipHomeomorph_apply, onePointRealFlip_infty]
      show (Homeomorph.onePointCongr (Homeomorph.addRight r)) (((0 : ℝ) : OnePoint ℝ)) = _
      simp
    set H : OnePoint ℝ ≃ₜ OnePoint ℝ := M.trans h with hHdef
    have hHinf : H OnePoint.infty = OnePoint.infty := by
      rw [hHdef, Homeomorph.trans_apply, hM_inf, hhr]
    have hMx' : ∀ (x : Fin 4 → ℝ), (∀ i, x i ≠ r) →
        ∀ i, M (((1 / (r - x i) : ℝ)) : OnePoint ℝ) = (x i : OnePoint ℝ) := by
      intro x hxr i
      have hs : (1 / (r - x i) : ℝ) ≠ 0 := by
        have : r - x i ≠ 0 := sub_ne_zero.2 (Ne.symm (hxr i))
        exact one_div_ne_zero this
      rw [hM_coe hs]
      congr 1
      have hne : r - x i ≠ 0 := sub_ne_zero.2 (Ne.symm (hxr i))
      field_simp
      ring
    rcases dichotomy_fixInfty hHinf with hmono | hanti
    · refine Or.inl fun x hx y hy => ?_
      have hxr : ∀ i, x i ≠ r := by
        intro i heq
        have hcontra := hy i
        rw [heq, hhr] at hcontra
        exact OnePoint.coe_ne_infty (y i) hcontra.symm
      have hx' : CyclicStrictMono (fun i => 1 / (r - x i)) := cyclicStrictMono_invMap hx hxr
      have hyH : ∀ i, H (((1 / (r - x i) : ℝ)) : OnePoint ℝ) = (y i : OnePoint ℝ) := by
        intro i
        rw [hHdef, Homeomorph.trans_apply, hMx' x hxr i]
        exact hy i
      exact hmono _ hx' _ hyH
    · refine Or.inr fun x hx y hy => ?_
      have hxr : ∀ i, x i ≠ r := by
        intro i heq
        have hcontra := hy i
        rw [heq, hhr] at hcontra
        exact OnePoint.coe_ne_infty (y i) hcontra.symm
      have hx' : CyclicStrictMono (fun i => 1 / (r - x i)) := cyclicStrictMono_invMap hx hxr
      have hyH : ∀ i, H (((1 / (r - x i) : ℝ)) : OnePoint ℝ) = (y i : OnePoint ℝ) := by
        intro i
        rw [hHdef, Homeomorph.trans_apply, hMx' x hxr i]
        exact hy i
      exact hanti _ hx' _ hyH

/-! ### Transport to the boundary of `ℍ` in `ℂ̄`

`frontier (toExt upperHalf) = toExt {z : ℂ | z.im = 0} ∪ {extInf}` (already proved, S01's import
chain via `scExt_frontier_toExt_upperHalf`). The real axis plus `∞` embeds into `ℂ̄` exactly onto
this set; transporting the dichotomy along this embedding gives the boundary-correspondence
version consumers actually need. -/

/-- The real axis (plus `∞`) embedded in `ℂ̄`. -/
def realToExtPlane : OnePoint ℝ → ExtPlane := OnePoint.map ((↑) : ℝ → ℂ)

theorem realToExtPlane_coe (t : ℝ) : realToExtPlane (t : OnePoint ℝ) = ((t : ℂ) : ExtPlane) := rfl

theorem realToExtPlane_infty : realToExtPlane OnePoint.infty = extInf := rfl

theorem realToExtPlane_injective : Function.Injective realToExtPlane := by
  intro w1 w2 heq
  induction w1 using OnePoint.rec with
  | infty =>
    induction w2 using OnePoint.rec with
    | infty => rfl
    | coe t2 =>
      rw [realToExtPlane_infty, realToExtPlane_coe] at heq
      exact absurd heq (OnePoint.infty_ne_coe _)
  | coe t1 =>
    induction w2 using OnePoint.rec with
    | infty =>
      rw [realToExtPlane_coe, realToExtPlane_infty] at heq
      exact absurd heq (OnePoint.coe_ne_infty _)
    | coe t2 =>
      rw [realToExtPlane_coe, realToExtPlane_coe] at heq
      have ht : t1 = t2 := Complex.ofReal_injective (OnePoint.coe_injective heq)
      rw [ht]

theorem continuous_realToExtPlane : Continuous realToExtPlane := by
  apply OnePoint.continuous_map Complex.continuous_ofReal
  rw [coclosedCompact_eq_cocompact, ← cobounded_eq_cocompact,
    show (coclosedCompact ℂ) = cocompact ℂ from coclosedCompact_eq_cocompact,
    ← cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
  have heq : (fun t : ℝ => ‖(t : ℂ)‖) = fun t : ℝ => ‖t‖ := by
    funext t; exact Complex.norm_real t
  rw [heq]
  exact tendsto_norm_cobounded_atTop

theorem range_realToExtPlane : range realToExtPlane = frontier (toExt upperHalf) := by
  rw [scExt_frontier_toExt_upperHalf]
  ext p
  constructor
  · rintro ⟨w, rfl⟩
    induction w using OnePoint.rec with
    | infty => exact Or.inr realToExtPlane_infty
    | coe t => exact Or.inl ⟨t, by simp, (realToExtPlane_coe t).symm⟩
  · rintro (⟨t, ht, rfl⟩ | rfl)
    · refine ⟨(t.re : OnePoint ℝ), ?_⟩
      rw [realToExtPlane_coe]
      congr 1
      exact Complex.ext_iff.2 ⟨by simp, ht.symm⟩
    · exact ⟨OnePoint.infty, realToExtPlane_infty⟩

theorem isClosedEmbedding_realToExtPlane : IsClosedEmbedding realToExtPlane :=
  continuous_realToExtPlane.isClosedEmbedding realToExtPlane_injective

/-- **(A), boundary transport**: `F` continuous and injective on `frontier (toExt upperHalf)`
and mapping it onto itself is either cyclic-order preserving or cyclic-order reversing on real
4-tuples on that boundary. (This is the shape a boundary correspondence built from
`IsHomeoExtension`s — e.g. `Φ' ∘ f ∘ Φ⁻¹` — actually has: continuous/injective only on
closures, not a global homeomorphism of `ℂ̄`.) -/
theorem dichotomy_frontier_upperHalf {F : ExtPlane → ExtPlane}
    (hFc : ContinuousOn F (frontier (toExt upperHalf)))
    (hFi : InjOn F (frontier (toExt upperHalf)))
    (hFs : F '' frontier (toExt upperHalf) = frontier (toExt upperHalf)) :
    (∀ x : Fin 4 → ℝ, CyclicStrictMono x → ∀ y : Fin 4 → ℝ,
      (∀ i, F (((x i : ℝ) : ℂ) : ExtPlane) = (((y i : ℝ) : ℂ) : ExtPlane)) → CyclicStrictMono y) ∨
    (∀ x : Fin 4 → ℝ, CyclicStrictMono x → ∀ y : Fin 4 → ℝ,
      (∀ i, F (((x i : ℝ) : ℂ) : ExtPlane) = (((y i : ℝ) : ℂ) : ExtPlane)) →
        CyclicStrictMono (fun i => y (-i))) := by
  have hrange : range realToExtPlane = frontier (toExt upperHalf) := range_realToExtPlane
  have hmapsTo : MapsTo realToExtPlane univ (frontier (toExt upperHalf)) := by
    intro w _; rw [← hrange]; exact mem_range_self w
  have hex : ∀ w : OnePoint ℝ, ∃ w' : OnePoint ℝ, realToExtPlane w' = F (realToExtPlane w) := by
    intro w
    have hmem : F (realToExtPlane w) ∈ frontier (toExt upperHalf) := by
      rw [← hFs]; exact ⟨realToExtPlane w, hmapsTo (mem_univ w), rfl⟩
    rw [← hrange] at hmem
    exact hmem
  choose g hg using hex
  have hginj : Function.Injective g := by
    intro w1 w2 heq
    apply realToExtPlane_injective
    apply hFi (hmapsTo (mem_univ w1)) (hmapsTo (mem_univ w2))
    rw [← hg, ← hg, heq]
  have hgsurj : Function.Surjective g := by
    intro w
    have hmem : realToExtPlane w ∈ F '' frontier (toExt upperHalf) := by
      rw [hFs]; exact hmapsTo (mem_univ w)
    obtain ⟨p, hp, hpeq⟩ := hmem
    rw [← hrange] at hp
    obtain ⟨w', hw'⟩ := hp
    refine ⟨w', realToExtPlane_injective ?_⟩
    rw [hg, hw', hpeq]
  have hgcont : Continuous g := by
    have heq : realToExtPlane ∘ g = F ∘ realToExtPlane := funext hg
    have hcont : Continuous (F ∘ realToExtPlane) :=
      hFc.comp_continuous continuous_realToExtPlane (fun w => hmapsTo (mem_univ w))
    rw [← heq] at hcont
    exact isClosedEmbedding_realToExtPlane.isInducing.continuous_iff.2 hcont
  set h : OnePoint ℝ ≃ₜ OnePoint ℝ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hginj, hgsurj⟩) hgcont with hhdef
  have hhg : ∀ w, h w = g w := fun w => rfl
  rcases dichotomy_onePoint_homeomorphism h with hcase | hcase
  · refine Or.inl fun x hx y hy => ?_
    refine hcase x hx y fun i => ?_
    apply realToExtPlane_injective
    rw [hhg, hg, realToExtPlane_coe, hy i]
    exact (realToExtPlane_coe (y i)).symm
  · refine Or.inr fun x hx y hy => ?_
    refine hcase x hx y fun i => ?_
    apply realToExtPlane_injective
    rw [hhg, hg, realToExtPlane_coe, hy i]
    exact (realToExtPlane_coe (y i)).symm


-- ===== (B): automorphisms of the upper half-plane preserve boundary cyclic order =====
--
-- `mobiusReal_sub_eq`, `mobiusReal_lt_of_same_side`, `mobiusReal_lt_of_opp_side` and
-- `cyclicStrictMono_of_chain` (used below) are already defined above, shared with (A)'s
-- `cyclicStrictMono_invMap` and with W5core / `dichotomy_fixInfty` — deduped from what were
-- originally two independently-developed copies (`_'`-suffixed and plain).

/-- (B) Automorphisms of `ℍ` (real Möbius transformations with positive determinant) preserve
cyclic order on the boundary `ℝ`, wherever the transformation stays finite. -/
theorem automorphism_upperHalf_preserves_cyclicOrder {a b c d : ℝ} (hdet : 0 < a * d - b * c)
    (x : Fin 4 → ℝ) (hx : CyclicStrictMono x) (y : Fin 4 → ℝ)
    (hy : ∀ i, mobiusExt (a : ℂ) (b : ℂ) (c : ℂ) (d : ℂ) (((x i : ℝ) : ℂ) : ExtPlane) =
      (((y i : ℝ) : ℂ) : ExtPlane)) :
    CyclicStrictMono y := by
  -- The transformation stays finite at each `x i`, and there `y i` is the usual formula.
  have hden : ∀ i, c * x i + d ≠ 0 := by
    intro i hcd
    have heq := hy i
    rw [mobiusExt_ofReal_coe_of_eq_zero hcd] at heq
    exact OnePoint.infty_ne_coe _ heq
  have hyx : ∀ i, y i = (a * x i + b) / (c * x i + d) := by
    intro i
    have heq := hy i
    rw [mobiusExt_ofReal_coe (hden i)] at heq
    have h2 := OnePoint.coe_injective heq
    exact_mod_cast h2.symm
  -- Unpack the cyclic order of `x` at shift `k`.
  obtain ⟨k, hk⟩ := hx
  have hx01 : x (0 + k) < x (1 + k) := hk (show (0 : Fin 4) < 1 by decide)
  have hx12 : x (1 + k) < x (2 + k) := hk (show (1 : Fin 4) < 2 by decide)
  have hx23 : x (2 + k) < x (3 + k) := hk (show (2 : Fin 4) < 3 by decide)
  set x0 := x (0 + k) with hx0def
  set x1 := x (1 + k) with hx1def
  set x2 := x (2 + k) with hx2def
  set x3 := x (3 + k) with hx3def
  have hd0 : c * x0 + d ≠ 0 := hden _
  have hd1 : c * x1 + d ≠ 0 := hden _
  have hd2 : c * x2 + d ≠ 0 := hden _
  have hd3 : c * x3 + d ≠ 0 := hden _
  have hy0eq : y (0 + k) = (a * x0 + b) / (c * x0 + d) := hyx _
  have hy1eq : y (1 + k) = (a * x1 + b) / (c * x1 + d) := hyx _
  have hy2eq : y (2 + k) = (a * x2 + b) / (c * x2 + d) := hyx _
  have hy3eq : y (3 + k) = (a * x3 + b) / (c * x3 + d) := hyx _
  by_cases hc0 : c = 0
  · -- Affine case: `t ↦ (a t + b)/d` is globally increasing (no pole in `ℝ`).
    have hd0' : d ≠ 0 := by intro hd; exact hdet.ne' (by rw [hc0, hd]; ring)
    have hsame_all : ∀ t₁ t₂ : ℝ, 0 < (c * t₁ + d) * (c * t₂ + d) := by
      intro t₁ t₂
      have e : (c * t₁ + d) * (c * t₂ + d) = d * d := by rw [hc0]; ring
      rw [e]; exact mul_self_pos.2 hd0'
    have hchain1 : y (0 + k) < y (1 + k) := by
      rw [hy0eq, hy1eq]
      exact mobiusReal_lt_of_same_side hdet hd0 hd1 hx01 (hsame_all x0 x1)
    have hchain2 : y (1 + k) < y (2 + k) := by
      rw [hy1eq, hy2eq]
      exact mobiusReal_lt_of_same_side hdet hd1 hd2 hx12 (hsame_all x1 x2)
    have hchain3 : y (2 + k) < y (3 + k) := by
      rw [hy2eq, hy3eq]
      exact mobiusReal_lt_of_same_side hdet hd2 hd3 hx23 (hsame_all x2 x3)
    exact cyclicStrictMono_of_chain k hchain1 hchain2 hchain3
  · -- Genuine pole `p = -d / c`.
    set p := -d / c with hpdef
    have hcp : c * p = -d := by rw [hpdef]; field_simp
    have heq : ∀ t : ℝ, c * t + d = c * (t - p) := fun t => by
      rw [mul_sub, hcp]; ring
    have hsq : 0 < c * c := mul_self_pos.2 hc0
    have hsamepos : ∀ {t₁ t₂ : ℝ}, p < t₁ → p < t₂ → 0 < (c * t₁ + d) * (c * t₂ + d) := by
      intro t₁ t₂ h1 h2
      rw [heq t₁, heq t₂, show c * (t₁ - p) * (c * (t₂ - p)) = c * c * ((t₁ - p) * (t₂ - p))
        from by ring]
      exact mul_pos hsq (mul_pos (by linarith) (by linarith))
    have hsameneg : ∀ {t₁ t₂ : ℝ}, t₁ < p → t₂ < p → 0 < (c * t₁ + d) * (c * t₂ + d) := by
      intro t₁ t₂ h1 h2
      rw [heq t₁, heq t₂, show c * (t₁ - p) * (c * (t₂ - p)) = c * c * ((t₁ - p) * (t₂ - p))
        from by ring]
      exact mul_pos hsq (mul_pos_of_neg_of_neg (by linarith) (by linarith))
    have hopp : ∀ {t₁ t₂ : ℝ}, t₁ < p → p < t₂ → (c * t₁ + d) * (c * t₂ + d) < 0 := by
      intro t₁ t₂ h1 h2
      rw [heq t₁, heq t₂, show c * (t₁ - p) * (c * (t₂ - p)) = c * c * ((t₁ - p) * (t₂ - p))
        from by ring]
      exact mul_neg_of_pos_of_neg hsq (mul_neg_of_neg_of_pos (by linarith) (by linarith))
    have hp0 : x0 ≠ p := fun h => hd0 (by rw [heq x0, h, sub_self, mul_zero])
    have hp1 : x1 ≠ p := fun h => hd1 (by rw [heq x1, h, sub_self, mul_zero])
    have hp2 : x2 ≠ p := fun h => hd2 (by rw [heq x2, h, sub_self, mul_zero])
    have hp3 : x3 ≠ p := fun h => hd3 (by rw [heq x3, h, sub_self, mul_zero])
    rcases lt_or_gt_of_ne hp0 with h0 | h0
    · -- `x0 < p`: locate `p` against `x1`.
      rcases lt_or_gt_of_ne hp1 with h1 | h1
      · -- `x1 < p`: locate `p` against `x2`.
        rcases lt_or_gt_of_ne hp2 with h2 | h2
        · -- `x2 < p`: locate `p` against `x3`.
          rcases lt_or_gt_of_ne hp3 with h3 | h3
          · -- `p > x3`: all four values `< p`, shift `k`.
            have hchain1 : y (0 + k) < y (1 + k) := by
              rw [hy0eq, hy1eq]
              exact mobiusReal_lt_of_same_side hdet hd0 hd1 hx01 (hsameneg h0 h1)
            have hchain2 : y (1 + k) < y (2 + k) := by
              rw [hy1eq, hy2eq]
              exact mobiusReal_lt_of_same_side hdet hd1 hd2 hx12 (hsameneg h1 h2)
            have hchain3 : y (2 + k) < y (3 + k) := by
              rw [hy2eq, hy3eq]
              exact mobiusReal_lt_of_same_side hdet hd2 hd3 hx23 (hsameneg h2 h3)
            exact cyclicStrictMono_of_chain k hchain1 hchain2 hchain3
          · -- `x2 < p < x3`: shift `k + 3`.
            have e1 : (0 : Fin 4) + (k + 3) = 3 + k := by omega
            have e2 : (1 : Fin 4) + (k + 3) = 0 + k := by omega
            have e3 : (2 : Fin 4) + (k + 3) = 1 + k := by omega
            have e4 : (3 : Fin 4) + (k + 3) = 2 + k := by omega
            have hchain1 : y (0 + (k + 3)) < y (1 + (k + 3)) := by
              rw [e1, e2, hy3eq, hy0eq]
              exact mobiusReal_lt_of_opp_side hdet hd0 hd3 (hx01.trans (hx12.trans hx23))
                (hopp h0 h3)
            have hchain2 : y (1 + (k + 3)) < y (2 + (k + 3)) := by
              rw [e2, e3, hy0eq, hy1eq]
              exact mobiusReal_lt_of_same_side hdet hd0 hd1 hx01 (hsameneg h0 h1)
            have hchain3 : y (2 + (k + 3)) < y (3 + (k + 3)) := by
              rw [e3, e4, hy1eq, hy2eq]
              exact mobiusReal_lt_of_same_side hdet hd1 hd2 hx12 (hsameneg h1 h2)
            exact cyclicStrictMono_of_chain (k + 3) hchain1 hchain2 hchain3
        · -- `x1 < p < x2`: shift `k + 2`.
          have hx3p : p < x3 := h2.trans hx23
          have e1 : (0 : Fin 4) + (k + 2) = 2 + k := by omega
          have e2 : (1 : Fin 4) + (k + 2) = 3 + k := by omega
          have e3 : (2 : Fin 4) + (k + 2) = 0 + k := by omega
          have e4 : (3 : Fin 4) + (k + 2) = 1 + k := by omega
          have hchain1 : y (0 + (k + 2)) < y (1 + (k + 2)) := by
            rw [e1, e2, hy2eq, hy3eq]
            exact mobiusReal_lt_of_same_side hdet hd2 hd3 hx23 (hsamepos h2 hx3p)
          have hchain2 : y (1 + (k + 2)) < y (2 + (k + 2)) := by
            rw [e2, e3, hy3eq, hy0eq]
            exact mobiusReal_lt_of_opp_side hdet hd0 hd3 (hx01.trans (hx12.trans hx23))
              (hopp h0 hx3p)
          have hchain3 : y (2 + (k + 2)) < y (3 + (k + 2)) := by
            rw [e3, e4, hy0eq, hy1eq]
            exact mobiusReal_lt_of_same_side hdet hd0 hd1 hx01 (hsameneg h0 h1)
          exact cyclicStrictMono_of_chain (k + 2) hchain1 hchain2 hchain3
      · -- `x0 < p < x1`: shift `k + 1`.
        have hx2p : p < x2 := h1.trans hx12
        have hx3p : p < x3 := hx2p.trans hx23
        have e1 : (0 : Fin 4) + (k + 1) = 1 + k := by omega
        have e2 : (1 : Fin 4) + (k + 1) = 2 + k := by omega
        have e3 : (2 : Fin 4) + (k + 1) = 3 + k := by omega
        have e4 : (3 : Fin 4) + (k + 1) = 0 + k := by omega
        have hchain1 : y (0 + (k + 1)) < y (1 + (k + 1)) := by
          rw [e1, e2, hy1eq, hy2eq]
          exact mobiusReal_lt_of_same_side hdet hd1 hd2 hx12 (hsamepos h1 hx2p)
        have hchain2 : y (1 + (k + 1)) < y (2 + (k + 1)) := by
          rw [e2, e3, hy2eq, hy3eq]
          exact mobiusReal_lt_of_same_side hdet hd2 hd3 hx23 (hsamepos hx2p hx3p)
        have hchain3 : y (2 + (k + 1)) < y (3 + (k + 1)) := by
          rw [e3, e4, hy3eq, hy0eq]
          exact mobiusReal_lt_of_opp_side hdet hd0 hd3 (hx01.trans (hx12.trans hx23))
            (hopp h0 hx3p)
        exact cyclicStrictMono_of_chain (k + 1) hchain1 hchain2 hchain3
    · -- `p < x0`: all four values `> p`, shift `k`.
      have hx1p : p < x1 := h0.trans hx01
      have hx2p : p < x2 := hx1p.trans hx12
      have hx3p : p < x3 := hx2p.trans hx23
      have hchain1 : y (0 + k) < y (1 + k) := by
        rw [hy0eq, hy1eq]
        exact mobiusReal_lt_of_same_side hdet hd0 hd1 hx01 (hsamepos h0 hx1p)
      have hchain2 : y (1 + k) < y (2 + k) := by
        rw [hy1eq, hy2eq]
        exact mobiusReal_lt_of_same_side hdet hd1 hd2 hx12 (hsamepos hx1p hx2p)
      have hchain3 : y (2 + k) < y (3 + k) := by
        rw [hy2eq, hy3eq]
        exact mobiusReal_lt_of_same_side hdet hd2 hd3 hx23 (hsamepos hx2p hx3p)
      exact cyclicStrictMono_of_chain k hchain1 hchain2 hchain3


end LiZhongQC
