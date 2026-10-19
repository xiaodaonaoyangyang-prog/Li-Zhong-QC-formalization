import LiZhongQC.Lemmas.FiniteGeodesicChain
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- Concatenation of the two finite oriented lists of sides. -/
def s25bj_append {n m : ℕ} (L : Fin n → ℝ → ℂ) (R : Fin m → ℝ → ℂ) :
    Fin (n + m) → ℝ → ℂ := Fin.append L R

/-- Reversal changes both the order of the sides and each side's parameter. -/
def s25bj_reverse {m : ℕ} (R : Fin m → ℝ → ℂ) : Fin m → ℝ → ℂ :=
  fun j t => R j.rev (1 - t)

/-- Increasing cuts for the reversed normalized interval. -/
def s25bj_reverseCuts {m : ℕ} (q : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  fun j => 1 - q j.rev

/-- Increasing parameter maps into the reversed normalized source curve. -/
def s25bj_reversePar {m : ℕ} (r : Fin m → ℝ → ℝ) : Fin m → ℝ → ℝ :=
  fun j t => 1 - r j.rev (1 - t)

theorem s25bj_append_left {n m : ℕ} (L : Fin n → ℝ → ℂ) (R : Fin m → ℝ → ℂ)
    (i : Fin n) : s25bj_append L R (i.castAdd m) = L i := by
  exact Fin.append_left L R i

theorem s25bj_append_right {n m : ℕ} (L : Fin n → ℝ → ℂ) (R : Fin m → ℝ → ℂ)
    (j : Fin m) : s25bj_append L R (j.natAdd n) = R j := by
  exact Fin.append_right L R j

/-- A tuple's consecutive values agree with those of its modular successor,
provided the successor is not the wraparound. -/
theorem s25bj_succ_of_val {N : ℕ} [NeZero N] {i j : Fin N}
    (h : i.val + 1 = j.val) : i + 1 = j := by
  apply Fin.ext
  have hv : (i + 1).val = (i.val + 1) % N := by
    simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [hv, h, Nat.mod_eq_of_lt j.isLt]

theorem s25bj_succ_last {N : ℕ} [NeZero N] {i : Fin N}
    (h : i.val + 1 = N) : i + 1 = 0 := by
  apply Fin.ext
  change (i + 1).val = 0
  have hv : (i + 1).val = (i.val + 1) % N := by
    simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [hv, h, Nat.mod_self]

/-- Joining a forward list and an already oriented return list.
The two seam equalities are explicit and no corner angle is assumed. -/
theorem s25bj_append_next {n m : ℕ} [NeZero (n + m)] (hn : 0 < n) (hm : 0 < m)
    {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    (hL : ∀ i j : Fin n, i.val + 1 = j.val → L i 1 = L j 0)
    (hR : ∀ i j : Fin m, i.val + 1 = j.val → R i 1 = R j 0)
    (hLR : L ⟨n - 1, by omega⟩ 1 = R ⟨0, hm⟩ 0)
    (hRL : R ⟨m - 1, by omega⟩ 1 = L ⟨0, hn⟩ 0) :
    ∀ k : Fin (n + m), s25bj_append L R k 1 = s25bj_append L R (k + 1) 0 := by
  refine Fin.addCases ?_ ?_
  · intro i
    by_cases hi : i.val + 1 < n
    · let j : Fin n := ⟨i.val + 1, hi⟩
      have he : i.castAdd m + 1 = j.castAdd m :=
        s25bj_succ_of_val (by rfl)
      rw [he, s25bj_append_left, s25bj_append_left]
      exact hL i j rfl
    · have hi' : i = (⟨n - 1, by omega⟩ : Fin n) := by
        apply Fin.ext
        change i.val = n - 1
        omega
      have he : i.castAdd m + 1 = (⟨0, hm⟩ : Fin m).natAdd n :=
        s25bj_succ_of_val (by change i.val + 1 = n + 0; omega)
      rw [he, s25bj_append_left, s25bj_append_right, hi']
      exact hLR
  · intro i
    by_cases hi : i.val + 1 < m
    · let j : Fin m := ⟨i.val + 1, hi⟩
      have he : i.natAdd n + 1 = j.natAdd n :=
        s25bj_succ_of_val (by change n + i.val + 1 = n + (i.val + 1); omega)
      rw [he, s25bj_append_right, s25bj_append_right]
      exact hR i j rfl
    · have hi' : i = (⟨m - 1, by omega⟩ : Fin m) := by
        apply Fin.ext
        change i.val = m - 1
        omega
      have he : i.natAdd n + 1 = (⟨0, hn⟩ : Fin n).castAdd m := by
        have hz : i.natAdd n + 1 = (0 : Fin (n + m)) :=
          s25bj_succ_last (by change n + i.val + 1 = n + m; omega)
        exact hz.trans (by apply Fin.ext; rfl)
      rw [he, s25bj_append_right, s25bj_append_left, hi']
      exact hRL

/-- Simplicity of the concatenation from simplicity within each list and
the actual half-open cross-disjointness. -/
theorem s25bj_append_simple {n m : ℕ}
    {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    (hL : ∀ i j, ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1,
      L i s = L j t → i = j ∧ s = t)
    (hR : ∀ i j, ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1,
      R i s = R j t → i = j ∧ s = t)
    (hcross : ∀ i j, ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1,
      L i s ≠ R j t) :
    ∀ i j : Fin (n + m), ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1,
      s25bj_append L R i s = s25bj_append L R j t → i = j ∧ s = t := by
  refine Fin.addCases ?_ ?_
  · intro i
    refine Fin.addCases ?_ ?_
    · intro j s hs t ht he
      rw [s25bj_append_left, s25bj_append_left] at he
      obtain ⟨hij, hst⟩ := hL i j s hs t ht he
      exact ⟨congrArg (Fin.castAdd m) hij, hst⟩
    · intro j s hs t ht he
      rw [s25bj_append_left, s25bj_append_right] at he
      exact False.elim (hcross i j s hs t ht he)
  · intro i
    refine Fin.addCases ?_ ?_
    · intro j s hs t ht he
      rw [s25bj_append_right, s25bj_append_left] at he
      exact False.elim (hcross j i t ht s hs he.symm)
    · intro j s hs t ht he
      rw [s25bj_append_right, s25bj_append_right] at he
      obtain ⟨hij, hst⟩ := hR i j s hs t ht he
      exact ⟨congrArg (Fin.natAdd n) hij, hst⟩

/-- Each parameter lies in its closed source gap. -/
theorem s25bj_parameter_closed {p : ℝ → ℝ} {a b : ℝ}
    (hp : StrictMonoOn p (Icc (0 : ℝ) 1)) (h0 : p 0 = a) (h1 : p 1 = b)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : p t ∈ Icc a b := by
  constructor
  · rw [← h0]
    exact hp.monotoneOn ⟨le_rfl, zero_le_one⟩ ht ht.1
  · rw [← h1]
    exact hp.monotoneOn ht ⟨zero_le_one, le_rfl⟩ ht.2

/-- A normalized increasing partition and its side parameter stay in [0,1). -/
theorem s25bj_partition_halfopen {n : ℕ} {p : Fin (n + 1) → ℝ}
    (hp : StrictMono p) (hp0 : p 0 = 0) (hp1 : p (Fin.last n) = 1)
    {par : Fin n → ℝ → ℝ}
    (hpar : ∀ j, StrictMonoOn (par j) (Icc (0 : ℝ) 1))
    (h0 : ∀ j, par j 0 = p j.castSucc) (h1 : ∀ j, par j 1 = p j.succ)
    (j : Fin n) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    par j t ∈ Ico (0 : ℝ) 1 := by
  have h := s25gb_parameter_halfopen (hpar j) (h0 j) (h1 j) ht
  constructor
  · have he := hp.monotone (Fin.zero_le j.castSucc)
    rw [hp0] at he
    exact he.trans h.1
  · have he := hp.monotone (Fin.le_last j.succ)
    rw [hp1] at he
    exact h.2.trans_le he

/-- The bigon condition excludes cross intersections of the half-open side
lists. At F(0), injectivity of G excludes G(1), which is omitted from its list. -/
theorem s25bj_bigon_cross {F G : ℝ → ℂ}
    (hGi : InjOn G (Icc (0 : ℝ) 1)) (hFG : F 0 = G 1)
    (hoff : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, F s ≠ G t)
    {a b : ℝ} (ha : a ∈ Ico (0 : ℝ) 1) (hb : b ∈ Ico (0 : ℝ) 1) :
    F a ≠ G b := by
  intro he
  rcases ha.1.eq_or_lt with h | h
  · have ha0 : a = 0 := h.symm
    rw [ha0, hFG] at he
    have he' := hGi ⟨zero_le_one, le_rfl⟩ ⟨hb.1, hb.2.le⟩ he
    linarith [hb.2]
  · exact hoff a ⟨h, ha.2⟩ b ⟨hb.1, hb.2.le⟩ he

/-- Extract the within-list join equalities directly from adjacent cuts. -/
theorem s25bj_partition_linear_next {n : ℕ} {p : Fin (n + 1) → ℝ}
    {F : ℝ → ℂ} {L : Fin n → ℝ → ℂ}
    (h0 : ∀ j, L j 0 = F (p j.castSucc)) (h1 : ∀ j, L j 1 = F (p j.succ)) :
    ∀ i j : Fin n, i.val + 1 = j.val → L i 1 = L j 0 := by
  intro i j he
  rw [h1, h0]
  exact congrArg F (congrArg p (Fin.ext he))

/-- All non-angular fields of the bigon chain. F and G are the two oriented
normalized embedded arcs (F(0)=G(1), F(1)=G(0)); their partitions are exactly
the flat side/par data supplied by s25cv_chain_fields after normalization. -/
theorem s25bj_oriented_partition_fields {φ : ℂ → ℂ} {n m : ℕ} [NeZero (n + m)]
    (hn : 0 < n) (hm : 0 < m)
    {F G : ℝ → ℂ} (hFi : InjOn F (Icc (0 : ℝ) 1))
    (hGi : InjOn G (Icc (0 : ℝ) 1))
    (hFG0 : F 0 = G 1) (hFG1 : F 1 = G 0)
    (hoff : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, F s ≠ G t)
    (hFm : ∀ t ∈ Icc (0 : ℝ) 1, F t ∈ unitDisc)
    (hGm : ∀ t ∈ Icc (0 : ℝ) 1, G t ∈ unitDisc)
    {p : Fin (n + 1) → ℝ} {q : Fin (m + 1) → ℝ}
    (hp : StrictMono p) (hq : StrictMono q)
    (hp0 : p 0 = 0) (hp1 : p (Fin.last n) = 1)
    (hq0 : q 0 = 0) (hq1 : q (Fin.last m) = 1)
    {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    {lpar : Fin n → ℝ → ℝ} {rpar : Fin m → ℝ → ℝ}
    (hlp : ∀ j, StrictMonoOn (lpar j) (Icc (0 : ℝ) 1))
    (hrp : ∀ j, StrictMonoOn (rpar j) (Icc (0 : ℝ) 1))
    (hl0 : ∀ j, lpar j 0 = p j.castSucc) (hl1 : ∀ j, lpar j 1 = p j.succ)
    (hr0 : ∀ j, rpar j 0 = q j.castSucc) (hr1 : ∀ j, rpar j 1 = q j.succ)
    (hLe : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, L j t = F (lpar j t))
    (hRe : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, R j t = G (rpar j t))
    (hLs : ∀ j, IsPhiStraightArc φ (L j) 0 1)
    (hRs : ∀ j, IsPhiStraightArc φ (R j) 0 1)
    (hLc : ∀ j, ContDiffOn ℝ 1 (L j) (Icc 0 1))
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1))
    (hLd : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (L j) (Icc 0 1) t ≠ 0)
    (hRd : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (R j) (Icc 0 1) t ≠ 0) :
    (∀ j, IsPhiStraightArc φ (s25bj_append L R j) 0 1) ∧
    (∀ j, ContDiffOn ℝ 1 (s25bj_append L R j) (Icc 0 1)) ∧
    (∀ j, s25bj_append L R j '' Icc (0 : ℝ) 1 ⊆ unitDisc) ∧
    (∀ j, s25bj_append L R j 1 = s25bj_append L R (j + 1) 0) ∧
    (∀ i j, ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1,
      s25bj_append L R i s = s25bj_append L R j t → i = j ∧ s = t) ∧
    (∀ j, derivWithin (s25bj_append L R j) (Icc 0 1) 0 ≠ 0) ∧
    (∀ j, derivWithin (s25bj_append L R j) (Icc 0 1) 1 ≠ 0) := by
  have hL0 : ∀ j, L j 0 = F (p j.castSucc) := by
    intro j
    rw [hLe j 0 ⟨le_rfl, zero_le_one⟩, hl0]
  have hL1 : ∀ j, L j 1 = F (p j.succ) := by
    intro j
    rw [hLe j 1 ⟨zero_le_one, le_rfl⟩, hl1]
  have hR0 : ∀ j, R j 0 = G (q j.castSucc) := by
    intro j
    rw [hRe j 0 ⟨le_rfl, zero_le_one⟩, hr0]
  have hR1 : ∀ j, R j 1 = G (q j.succ) := by
    intro j
    rw [hRe j 1 ⟨zero_le_one, le_rfl⟩, hr1]
  have hLsimple : ∀ i j, ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1,
      L i s = L j t → i = j ∧ s = t := by
    apply s25gb_partition_simple hp _ hlp hl0 hl1 hLe
    rw [hp0, hp1]
    exact hFi.mono Ico_subset_Icc_self
  have hRsimple : ∀ i j, ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1,
      R i s = R j t → i = j ∧ s = t := by
    apply s25gb_partition_simple hq _ hrp hr0 hr1 hRe
    rw [hq0, hq1]
    exact hGi.mono Ico_subset_Icc_self
  have hcross : ∀ i j, ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1,
      L i s ≠ R j t := by
    intro i j s hs t ht
    rw [hLe i s ⟨hs.1, hs.2.le⟩, hRe j t ⟨ht.1, ht.2.le⟩]
    exact s25bj_bigon_cross hGi hFG0 hoff
      (s25bj_partition_halfopen hp hp0 hp1 hlp hl0 hl1 i hs)
      (s25bj_partition_halfopen hq hq0 hq1 hrp hr0 hr1 j ht)
  have hLR : L ⟨n - 1, by omega⟩ 1 = R ⟨0, hm⟩ 0 := by
    rw [hL1, hR0,
      show (⟨n - 1, by omega⟩ : Fin n).succ = Fin.last n by apply Fin.ext; simp <;> omega,
      show (⟨0, hm⟩ : Fin m).castSucc = 0 by apply Fin.ext; rfl,
      hp1, hq0]
    exact hFG1
  have hRL : R ⟨m - 1, by omega⟩ 1 = L ⟨0, hn⟩ 0 := by
    rw [hR1, hL0,
      show (⟨m - 1, by omega⟩ : Fin m).succ = Fin.last m by apply Fin.ext; simp <;> omega,
      show (⟨0, hn⟩ : Fin n).castSucc = 0 by apply Fin.ext; rfl,
      hq1, hp0]
    exact hFG0.symm
  have hLmem : ∀ j, L j '' Icc (0 : ℝ) 1 ⊆ unitDisc := by
    intro j z hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [hLe j t ht]
    have h := s25bj_parameter_closed (hlp j) (hl0 j) (hl1 j) ht
    apply hFm
    constructor
    · have he := hp.monotone (Fin.zero_le j.castSucc)
      rw [hp0] at he
      exact he.trans h.1
    · have he := hp.monotone (Fin.le_last j.succ)
      rw [hp1] at he
      exact h.2.trans he
  have hRmem : ∀ j, R j '' Icc (0 : ℝ) 1 ⊆ unitDisc := by
    intro j z hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [hRe j t ht]
    have h := s25bj_parameter_closed (hrp j) (hr0 j) (hr1 j) ht
    apply hGm
    constructor
    · have he := hq.monotone (Fin.zero_le j.castSucc)
      rw [hq0] at he
      exact he.trans h.1
    · have he := hq.monotone (Fin.le_last j.succ)
      rw [hq1] at he
      exact h.2.trans he
  refine ⟨?_, ?_, ?_,
    s25bj_append_next hn hm (s25bj_partition_linear_next hL0 hL1)
      (s25bj_partition_linear_next hR0 hR1) hLR hRL,
    s25bj_append_simple hLsimple hRsimple hcross, ?_, ?_⟩
  · exact Fin.addCases (fun i => by rw [s25bj_append_left]; exact hLs i)
      (fun j => by rw [s25bj_append_right]; exact hRs j)
  · exact Fin.addCases (fun i => by rw [s25bj_append_left]; exact hLc i)
      (fun j => by rw [s25bj_append_right]; exact hRc j)
  · exact Fin.addCases (fun i => by rw [s25bj_append_left]; exact hLmem i)
      (fun j => by rw [s25bj_append_right]; exact hRmem j)
  · exact Fin.addCases
      (fun i => by rw [s25bj_append_left]; exact hLd i 0 ⟨le_rfl, zero_le_one⟩)
      (fun j => by rw [s25bj_append_right]; exact hRd j 0 ⟨le_rfl, zero_le_one⟩)
  · exact Fin.addCases
      (fun i => by rw [s25bj_append_left]; exact hLd i 1 ⟨zero_le_one, le_rfl⟩)
      (fun j => by rw [s25bj_append_right]; exact hRd j 1 ⟨zero_le_one, le_rfl⟩)

/-! Reversing the second list and its partition data. -/

theorem s25bj_reverse_derivWithin {m : ℕ} {R : Fin m → ℝ → ℂ}
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1))
    (j : Fin m) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    derivWithin (s25bj_reverse R j) (Icc 0 1) t =
      -derivWithin (R j.rev) (Icc 0 1) (1 - t) := by
  have hmap : ∀ u ∈ Icc (0 : ℝ) 1, 1 + (-1) * u ∈ Icc (0 : ℝ) 1 := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  change derivWithin (fun τ => R j.rev (1 - τ)) (Icc 0 1) t =
    -derivWithin (R j.rev) (Icc 0 1) (1 - t)
  simpa only [neg_one_mul, sub_eq_add_neg, Complex.ofReal_neg,
    Complex.ofReal_one] using
    fx_p2_derivWithin_affine (fx_p2_hasDerivWithinAt_of_contDiffOn (hRc j.rev))
      zero_lt_one hmap ht

theorem s25bj_reverse_smooth {m : ℕ} {R : Fin m → ℝ → ℂ}
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1)) :
    ∀ j, ContDiffOn ℝ 1 (s25bj_reverse R j) (Icc 0 1) := by
  intro j
  have hmap : ∀ u ∈ Icc (0 : ℝ) 1, 1 + (-1) * u ∈ Icc (0 : ℝ) 1 := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  change ContDiffOn ℝ 1 (fun τ => R j.rev (1 - τ)) (Icc 0 1)
  simpa only [neg_one_mul, sub_eq_add_neg] using
    fx_p2_contDiffOn_affine (hRc j.rev) hmap

theorem s25bj_reverse_straight {φ : ℂ → ℂ} {m : ℕ} {R : Fin m → ℝ → ℂ}
    (hRs : ∀ j, IsPhiStraightArc φ (R j) 0 1) :
    ∀ j, IsPhiStraightArc φ (s25bj_reverse R j) 0 1 := by
  intro j
  have hmap : ∀ u ∈ Ioo (0 : ℝ) 1, 1 + (-1) * u ∈ Ioo (0 : ℝ) 1 := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  change IsPhiStraightArc φ (fun τ => R j.rev (1 - τ)) 0 1
  simpa only [neg_one_mul, sub_eq_add_neg] using
    fx_p2_straight_affine (hRs j.rev) (by norm_num : (-1 : ℝ) ≠ 0) hmap

theorem s25bj_reverse_regular {m : ℕ} {R : Fin m → ℝ → ℂ}
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1))
    (hRd : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (R j) (Icc 0 1) t ≠ 0) :
    ∀ j, ∀ t ∈ Icc (0 : ℝ) 1,
      derivWithin (s25bj_reverse R j) (Icc 0 1) t ≠ 0 := by
  intro j t ht
  rw [s25bj_reverse_derivWithin hRc j ht]
  exact neg_ne_zero.2 (hRd j.rev (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩)

theorem s25bj_reverseCuts_mono {m : ℕ} {q : Fin (m + 1) → ℝ}
    (hq : StrictMono q) : StrictMono (s25bj_reverseCuts q) := by
  intro i j hij
  change 1 - q i.rev < 1 - q j.rev
  apply sub_lt_sub_left
  apply hq
  simpa only [Fin.rev_lt_rev] using hij

theorem s25bj_reverseCuts_ends {m : ℕ} {q : Fin (m + 1) → ℝ}
    (h0 : q 0 = 0) (h1 : q (Fin.last m) = 1) :
    s25bj_reverseCuts q 0 = 0 ∧ s25bj_reverseCuts q (Fin.last m) = 1 := by
  simp [s25bj_reverseCuts, h0, h1]

theorem s25bj_reversePar_mono {m : ℕ} {r : Fin m → ℝ → ℝ}
    (hr : ∀ j, StrictMonoOn (r j) (Icc (0 : ℝ) 1)) :
    ∀ j, StrictMonoOn (s25bj_reversePar r j) (Icc (0 : ℝ) 1) := by
  intro j s hs t ht hst
  change 1 - r j.rev (1 - s) < 1 - r j.rev (1 - t)
  apply sub_lt_sub_left
  exact hr j.rev ⟨by linarith [ht.2], by linarith [ht.1]⟩
    ⟨by linarith [hs.2], by linarith [hs.1]⟩ (by linarith)

theorem s25bj_reversePar_ends {m : ℕ} {q : Fin (m + 1) → ℝ}
    {r : Fin m → ℝ → ℝ}
    (h0 : ∀ j, r j 0 = q j.castSucc) (h1 : ∀ j, r j 1 = q j.succ) :
    (∀ j, s25bj_reversePar r j 0 = s25bj_reverseCuts q j.castSucc) ∧
    (∀ j, s25bj_reversePar r j 1 = s25bj_reverseCuts q j.succ) := by
  constructor
  · intro j
    simp only [s25bj_reversePar, sub_zero, h1, s25bj_reverseCuts, Fin.rev_castSucc]
  · intro j
    simp only [s25bj_reversePar, sub_self, h0, s25bj_reverseCuts, Fin.rev_succ]

theorem s25bj_reverse_trace_parameter {m : ℕ} {R : Fin m → ℝ → ℂ}
    {r : Fin m → ℝ → ℝ} {g : ℝ → ℂ}
    (he : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, R j t = g (r j t)) :
    ∀ j, ∀ t ∈ Icc (0 : ℝ) 1,
      s25bj_reverse R j t = (fun u => g (1 - u)) (s25bj_reversePar r j t) := by
  intro j t ht
  change R j.rev (1 - t) = g (1 - (1 - r j.rev (1 - t)))
  rw [sub_sub_cancel, he j.rev (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩]

/-- Reverse an embedded normalized arc using the existing affine injectivity
lemma, rather than rebuilding the topological extraction. -/
theorem s25bj_reverse_inj {g : ℝ → ℂ} (hg : InjOn g (Icc (0 : ℝ) 1)) :
    InjOn (fun t => g (1 - t)) (Icc (0 : ℝ) 1) := by
  simpa only [sub_self, zero_sub, neg_one_mul, sub_eq_add_neg, zero_add] using
    s25gb_affine_injective hg (u := 1) (v := 0)
      ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩ (by norm_num)

/-- The seven chain fields independent of corner-angle analysis. -/
def s25bj_BaseFields (φ : ℂ → ℂ) {N : ℕ} [NeZero N] (C : Fin N → ℝ → ℂ) : Prop :=
  (∀ j, IsPhiStraightArc φ (C j) 0 1) ∧
  (∀ j, ContDiffOn ℝ 1 (C j) (Icc 0 1)) ∧
  (∀ j, C j '' Icc (0 : ℝ) 1 ⊆ unitDisc) ∧
  (∀ j, C j 1 = C (j + 1) 0) ∧
  (∀ i j, ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1,
    C i s = C j t → i = j ∧ s = t) ∧
  (∀ j, derivWithin (C j) (Icc 0 1) 0 ≠ 0) ∧
  (∀ j, derivWithin (C j) (Icc 0 1) 1 ≠ 0)

/-- Forward first arc followed by the second arc in reverse. This is the
explicit Fin(n+m) construction for two normalized arcs with common endpoints. -/
theorem s25bj_forward_reverse_fields {φ : ℂ → ℂ} {n m : ℕ} [NeZero (n + m)]
    (hn : 0 < n) (hm : 0 < m)
    {f g : ℝ → ℂ} (hfi : InjOn f (Icc (0 : ℝ) 1)) (hgi : InjOn g (Icc (0 : ℝ) 1))
    (hfg0 : f 0 = g 0) (hfg1 : f 1 = g 1)
    (hoff : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, f s ≠ g t)
    (hfm : ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ unitDisc)
    (hgm : ∀ t ∈ Icc (0 : ℝ) 1, g t ∈ unitDisc)
    {p : Fin (n + 1) → ℝ} {q : Fin (m + 1) → ℝ}
    (hp : StrictMono p) (hq : StrictMono q)
    (hp0 : p 0 = 0) (hp1 : p (Fin.last n) = 1)
    (hq0 : q 0 = 0) (hq1 : q (Fin.last m) = 1)
    {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    {lpar : Fin n → ℝ → ℝ} {rpar : Fin m → ℝ → ℝ}
    (hlp : ∀ j, StrictMonoOn (lpar j) (Icc (0 : ℝ) 1))
    (hrp : ∀ j, StrictMonoOn (rpar j) (Icc (0 : ℝ) 1))
    (hl0 : ∀ j, lpar j 0 = p j.castSucc) (hl1 : ∀ j, lpar j 1 = p j.succ)
    (hr0 : ∀ j, rpar j 0 = q j.castSucc) (hr1 : ∀ j, rpar j 1 = q j.succ)
    (hLe : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, L j t = f (lpar j t))
    (hRe : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, R j t = g (rpar j t))
    (hLs : ∀ j, IsPhiStraightArc φ (L j) 0 1)
    (hRs : ∀ j, IsPhiStraightArc φ (R j) 0 1)
    (hLc : ∀ j, ContDiffOn ℝ 1 (L j) (Icc 0 1))
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1))
    (hLd : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (L j) (Icc 0 1) t ≠ 0)
    (hRd : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (R j) (Icc 0 1) t ≠ 0) :
    s25bj_BaseFields φ (s25bj_append L (s25bj_reverse R)) := by
  obtain ⟨hq0', hq1'⟩ := s25bj_reverseCuts_ends hq0 hq1
  obtain ⟨hr0', hr1'⟩ := s25bj_reversePar_ends hr0 hr1
  apply s25bj_oriented_partition_fields hn hm hfi (s25bj_reverse_inj hgi)
    (by simpa using hfg0) (by simpa using hfg1)
    (fun s hs t ht => hoff s hs (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    hfm (fun t ht => hgm (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    hp (s25bj_reverseCuts_mono hq) hp0 hp1 hq0' hq1'
    hlp (s25bj_reversePar_mono hrp) hl0 hl1 hr0' hr1' hLe
    (s25bj_reverse_trace_parameter hRe) hLs (s25bj_reverse_straight hRs)
    hLc (s25bj_reverse_smooth hRc) hLd (s25bj_reverse_regular hRc hRd)

/-! Normalize the raw side/par output on a subinterval. No side is changed,
so all actual straightness, smoothness and derivative data are retained. -/

def s25bj_normalizeCuts {n : ℕ} (p : Fin (n + 1) → ℝ) (a b : ℝ) :
    Fin (n + 1) → ℝ := fun i => (p i - a) / (b - a)

def s25bj_normalizePar {n : ℕ} (r : Fin n → ℝ → ℝ) (a b : ℝ) :
    Fin n → ℝ → ℝ := fun j t => (r j t - a) / (b - a)

theorem s25bj_normalizeCuts_mono {n : ℕ} {p : Fin (n + 1) → ℝ}
    (hp : StrictMono p) {a b : ℝ} (hab : a < b) :
    StrictMono (s25bj_normalizeCuts p a b) := by
  intro i j hij
  exact (div_lt_div_iff_of_pos_right (sub_pos.2 hab)).2 (sub_lt_sub_right (hp hij) a)

theorem s25bj_normalizeCuts_ends {n : ℕ} {p : Fin (n + 1) → ℝ}
    {a b : ℝ} (hab : a < b) (h0 : p 0 = a) (h1 : p (Fin.last n) = b) :
    s25bj_normalizeCuts p a b 0 = 0 ∧ s25bj_normalizeCuts p a b (Fin.last n) = 1 := by
  simp [s25bj_normalizeCuts, h0, h1, (sub_pos.2 hab).ne']

theorem s25bj_normalizePar_mono {n : ℕ} {r : Fin n → ℝ → ℝ}
    (hr : ∀ j, StrictMonoOn (r j) (Icc (0 : ℝ) 1)) {a b : ℝ} (hab : a < b) :
    ∀ j, StrictMonoOn (s25bj_normalizePar r a b j) (Icc (0 : ℝ) 1) := by
  intro j s hs t ht hst
  exact (div_lt_div_iff_of_pos_right (sub_pos.2 hab)).2
    (sub_lt_sub_right (hr j hs ht hst) a)

theorem s25bj_normalizePar_ends {n : ℕ} {p : Fin (n + 1) → ℝ}
    {r : Fin n → ℝ → ℝ} (a b : ℝ)
    (h0 : ∀ j, r j 0 = p j.castSucc) (h1 : ∀ j, r j 1 = p j.succ) :
    (∀ j, s25bj_normalizePar r a b j 0 = s25bj_normalizeCuts p a b j.castSucc) ∧
    (∀ j, s25bj_normalizePar r a b j 1 = s25bj_normalizeCuts p a b j.succ) := by
  constructor
  · intro j
    simp only [s25bj_normalizePar, s25bj_normalizeCuts, h0]
  · intro j
    simp only [s25bj_normalizePar, s25bj_normalizeCuts, h1]

theorem s25bj_normalize_trace {n : ℕ} {L : Fin n → ℝ → ℂ}
    {r : Fin n → ℝ → ℝ} {f : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (he : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, L j t = f (r j t)) :
    ∀ j, ∀ t ∈ Icc (0 : ℝ) 1,
      L j t = (fun u => f (a + (b - a) * u)) (s25bj_normalizePar r a b j t) := by
  intro j t ht
  rw [he j t ht]
  change f (r j t) = f (a + (b - a) * ((r j t - a) / (b - a)))
  congr 1
  field_simp [(sub_pos.2 hab).ne']
  <;> ring

/-- Adapter for raw increasing subinterval partitions with paired endpoints.
Both functions may be original globally injective geodesics; their actual
side/par data pass through unchanged, except for reversing the second list. -/
theorem s25bj_raw_forward_reverse_fields {φ : ℂ → ℂ} {n m : ℕ} [NeZero (n + m)]
    (hn : 0 < n) (hm : 0 < m)
    {f g : ℝ → ℂ} (hfi : InjOn f (Icc (0 : ℝ) 1)) (hgi : InjOn g (Icc (0 : ℝ) 1))
    {a b u v : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (hfg0 : f a = g u) (hfg1 : f b = g v)
    (hoff : ∀ s ∈ Ioo a b, ∀ t ∈ Icc (0 : ℝ) 1, f s ≠ g t)
    (hfm : ∀ t ∈ Icc a b, f t ∈ unitDisc)
    (hgm : ∀ t ∈ Icc u v, g t ∈ unitDisc)
    {p : Fin (n + 1) → ℝ} {q : Fin (m + 1) → ℝ}
    (hp : StrictMono p) (hq : StrictMono q)
    (hp0 : p 0 = a) (hp1 : p (Fin.last n) = b)
    (hq0 : q 0 = u) (hq1 : q (Fin.last m) = v)
    {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    {lpar : Fin n → ℝ → ℝ} {rpar : Fin m → ℝ → ℝ}
    (hlp : ∀ j, StrictMonoOn (lpar j) (Icc (0 : ℝ) 1))
    (hrp : ∀ j, StrictMonoOn (rpar j) (Icc (0 : ℝ) 1))
    (hl0 : ∀ j, lpar j 0 = p j.castSucc) (hl1 : ∀ j, lpar j 1 = p j.succ)
    (hr0 : ∀ j, rpar j 0 = q j.castSucc) (hr1 : ∀ j, rpar j 1 = q j.succ)
    (hLe : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, L j t = f (lpar j t))
    (hRe : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, R j t = g (rpar j t))
    (hLs : ∀ j, IsPhiStraightArc φ (L j) 0 1)
    (hRs : ∀ j, IsPhiStraightArc φ (R j) 0 1)
    (hLc : ∀ j, ContDiffOn ℝ 1 (L j) (Icc 0 1))
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1))
    (hLd : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (L j) (Icc 0 1) t ≠ 0)
    (hRd : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (R j) (Icc 0 1) t ≠ 0) :
    s25bj_BaseFields φ (s25bj_append L (s25bj_reverse R)) := by
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.le.trans hb⟩
  have hbI : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab.le, hb⟩
  have huI : u ∈ Icc (0 : ℝ) 1 := ⟨hu, huv.le.trans hv⟩
  have hvI : v ∈ Icc (0 : ℝ) 1 := ⟨hu.trans huv.le, hv⟩
  have hF := s25gb_affine_injective hfi haI hbI hab.ne
  have hG := s25gb_affine_injective hgi huI hvI huv.ne
  obtain ⟨hp0', hp1'⟩ := s25bj_normalizeCuts_ends hab hp0 hp1
  obtain ⟨hq0', hq1'⟩ := s25bj_normalizeCuts_ends huv hq0 hq1
  obtain ⟨hl0', hl1'⟩ := s25bj_normalizePar_ends a b hl0 hl1
  obtain ⟨hr0', hr1'⟩ := s25bj_normalizePar_ends u v hr0 hr1
  have hFm : ∀ t ∈ Icc (0 : ℝ) 1, f (a + (b - a) * t) ∈ unitDisc := by
    intro t ht
    apply hfm
    constructor <;> nlinarith [mul_nonneg (sub_pos.2 hab).le ht.1,
      mul_nonneg (sub_pos.2 hab).le (sub_nonneg.2 ht.2)]
  have hGm : ∀ t ∈ Icc (0 : ℝ) 1, g (u + (v - u) * t) ∈ unitDisc := by
    intro t ht
    apply hgm
    constructor <;> nlinarith [mul_nonneg (sub_pos.2 huv).le ht.1,
      mul_nonneg (sub_pos.2 huv).le (sub_nonneg.2 ht.2)]
  exact s25bj_forward_reverse_fields hn hm hF hG
    (by simpa using hfg0) (by simpa using hfg1)
    (fun s hs t ht => hoff _ (s25gb_affine_interior hab hs) _
      (s25gb_affine_mem huI hvI ht)) hFm hGm
    (s25bj_normalizeCuts_mono hp hab) (s25bj_normalizeCuts_mono hq huv)
    hp0' hp1' hq0' hq1' (s25bj_normalizePar_mono hlp hab)
    (s25bj_normalizePar_mono hrp huv) hl0' hl1' hr0' hr1'
    (s25bj_normalize_trace hab hLe) (s25bj_normalize_trace huv hRe)
    hLs hRs hLc hRc hLd hRd

/-- The opposite orientation of the raw bigon: the increasing second interval
already runs from the first arc's terminal point back to its starting point.
This covers the u > v branch of s25gb_bigon_parameters after naming the second
interval by its increasing endpoints. -/
theorem s25bj_raw_oriented_fields {φ : ℂ → ℂ} {n m : ℕ} [NeZero (n + m)]
    (hn : 0 < n) (hm : 0 < m)
    {f g : ℝ → ℂ} (hfi : InjOn f (Icc (0 : ℝ) 1)) (hgi : InjOn g (Icc (0 : ℝ) 1))
    {a b u v : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hu : 0 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (hfg0 : f a = g v) (hfg1 : f b = g u)
    (hoff : ∀ s ∈ Ioo a b, ∀ t ∈ Icc (0 : ℝ) 1, f s ≠ g t)
    (hfm : ∀ t ∈ Icc a b, f t ∈ unitDisc)
    (hgm : ∀ t ∈ Icc u v, g t ∈ unitDisc)
    {p : Fin (n + 1) → ℝ} {q : Fin (m + 1) → ℝ}
    (hp : StrictMono p) (hq : StrictMono q)
    (hp0 : p 0 = a) (hp1 : p (Fin.last n) = b)
    (hq0 : q 0 = u) (hq1 : q (Fin.last m) = v)
    {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    {lpar : Fin n → ℝ → ℝ} {rpar : Fin m → ℝ → ℝ}
    (hlp : ∀ j, StrictMonoOn (lpar j) (Icc (0 : ℝ) 1))
    (hrp : ∀ j, StrictMonoOn (rpar j) (Icc (0 : ℝ) 1))
    (hl0 : ∀ j, lpar j 0 = p j.castSucc) (hl1 : ∀ j, lpar j 1 = p j.succ)
    (hr0 : ∀ j, rpar j 0 = q j.castSucc) (hr1 : ∀ j, rpar j 1 = q j.succ)
    (hLe : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, L j t = f (lpar j t))
    (hRe : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, R j t = g (rpar j t))
    (hLs : ∀ j, IsPhiStraightArc φ (L j) 0 1)
    (hRs : ∀ j, IsPhiStraightArc φ (R j) 0 1)
    (hLc : ∀ j, ContDiffOn ℝ 1 (L j) (Icc 0 1))
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1))
    (hLd : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (L j) (Icc 0 1) t ≠ 0)
    (hRd : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, derivWithin (R j) (Icc 0 1) t ≠ 0) :
    s25bj_BaseFields φ (s25bj_append L R) := by
  have haI : a ∈ Icc (0 : ℝ) 1 := ⟨ha, hab.le.trans hb⟩
  have hbI : b ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hab.le, hb⟩
  have huI : u ∈ Icc (0 : ℝ) 1 := ⟨hu, huv.le.trans hv⟩
  have hvI : v ∈ Icc (0 : ℝ) 1 := ⟨hu.trans huv.le, hv⟩
  have hF := s25gb_affine_injective hfi haI hbI hab.ne
  have hG := s25gb_affine_injective hgi huI hvI huv.ne
  obtain ⟨hp0', hp1'⟩ := s25bj_normalizeCuts_ends hab hp0 hp1
  obtain ⟨hq0', hq1'⟩ := s25bj_normalizeCuts_ends huv hq0 hq1
  obtain ⟨hl0', hl1'⟩ := s25bj_normalizePar_ends a b hl0 hl1
  obtain ⟨hr0', hr1'⟩ := s25bj_normalizePar_ends u v hr0 hr1
  have hFm : ∀ t ∈ Icc (0 : ℝ) 1, f (a + (b - a) * t) ∈ unitDisc := by
    intro t ht
    apply hfm
    constructor <;> nlinarith [mul_nonneg (sub_pos.2 hab).le ht.1,
      mul_nonneg (sub_pos.2 hab).le (sub_nonneg.2 ht.2)]
  have hGm : ∀ t ∈ Icc (0 : ℝ) 1, g (u + (v - u) * t) ∈ unitDisc := by
    intro t ht
    apply hgm
    constructor <;> nlinarith [mul_nonneg (sub_pos.2 huv).le ht.1,
      mul_nonneg (sub_pos.2 huv).le (sub_nonneg.2 ht.2)]
  exact s25bj_oriented_partition_fields hn hm hF hG
    (by simpa using hfg0) (by simpa using hfg1)
    (fun s hs t ht => hoff _ (s25gb_affine_interior hab hs) _
      (s25gb_affine_mem huI hvI ht)) hFm hGm
    (s25bj_normalizeCuts_mono hp hab) (s25bj_normalizeCuts_mono hq huv)
    hp0' hp1' hq0' hq1' (s25bj_normalizePar_mono hlp hab)
    (s25bj_normalizePar_mono hrp huv) hl0' hl1' hr0' hr1'
    (s25bj_normalize_trace hab hLe) (s25bj_normalize_trace huv hRe)
    hLs hRs hLc hRc hLd hRd

/-! Explicit corner indices and tangent ratios. -/

theorem s25bj_left_predecessor {n m : ℕ} [NeZero (n + m)]
    (i : Fin n) (hi : 0 < i.val) :
    i.castAdd m - 1 = (⟨i.val - 1, by omega⟩ : Fin n).castAdd m := by
  have he : (⟨i.val - 1, by omega⟩ : Fin n).castAdd m + 1 = i.castAdd m :=
    s25bj_succ_of_val (by change i.val - 1 + 1 = i.val; omega)
  rw [← he, add_sub_cancel_right]

theorem s25bj_right_predecessor {n m : ℕ} [NeZero (n + m)]
    (j : Fin m) (hj : 0 < j.val) :
    j.natAdd n - 1 = (⟨j.val - 1, by omega⟩ : Fin m).natAdd n := by
  have he : (⟨j.val - 1, by omega⟩ : Fin m).natAdd n + 1 = j.natAdd n :=
    s25bj_succ_of_val (by change n + (j.val - 1) + 1 = n + j.val; omega)
  rw [← he, add_sub_cancel_right]

theorem s25bj_zero_predecessor {n m : ℕ} [NeZero (n + m)] (hm : 0 < m) :
    (0 : Fin (n + m)) - 1 = (⟨m - 1, by omega⟩ : Fin m).natAdd n := by
  have he : (⟨m - 1, by omega⟩ : Fin m).natAdd n + 1 = (0 : Fin (n + m)) :=
    s25bj_succ_last (by change n + (m - 1) + 1 = n + m; omega)
  rw [← he, add_sub_cancel_right]

theorem s25bj_seam_predecessor {n m : ℕ} [NeZero (n + m)] (hn : 0 < n) (hm : 0 < m) :
    (⟨n, by omega⟩ : Fin (n + m)) - 1 = (⟨n - 1, by omega⟩ : Fin n).castAdd m := by
  have he : (⟨n - 1, by omega⟩ : Fin n).castAdd m + 1 = (⟨n, by omega⟩ : Fin (n + m)) :=
    s25bj_succ_of_val (by change n - 1 + 1 = n; omega)
  rw [← he, add_sub_cancel_right]

theorem s25bj_reverse_first_index {m : ℕ} (hm : 0 < m) :
    (⟨0, hm⟩ : Fin m).rev = (⟨m - 1, by omega⟩ : Fin m) := by
  apply Fin.ext
  simp only [Fin.val_rev]

theorem s25bj_reverse_last_index {m : ℕ} (hm : 0 < m) :
    (⟨m - 1, by omega⟩ : Fin m).rev = (⟨0, hm⟩ : Fin m) := by
  have he := congrArg Fin.rev (s25bj_reverse_first_index hm)
  simpa only [Fin.rev_rev] using he.symm

/-- Interior vertices of the first block use the original adjacent sides. -/
theorem s25bj_left_corner_ratio {n m : ℕ} [NeZero (n + m)]
    (L : Fin n → ℝ → ℂ) (R : Fin m → ℝ → ℂ) (i : Fin n) (hi : 0 < i.val) :
    -derivWithin (s25bj_append L R (i.castAdd m - 1)) (Icc 0 1) 1 /
        derivWithin (s25bj_append L R (i.castAdd m)) (Icc 0 1) 0 =
      -derivWithin (L ⟨i.val - 1, by omega⟩) (Icc 0 1) 1 /
        derivWithin (L i) (Icc 0 1) 0 := by
  rw [s25bj_left_predecessor i hi, s25bj_append_left, s25bj_append_left]

/-- Interior return vertices expose the reversed adjacent original tangents.
This is the inverse-oriented ratio at the same original partition cut. -/
theorem s25bj_reverse_right_corner_ratio {n m : ℕ} [NeZero (n + m)]
    (L : Fin n → ℝ → ℂ) {R : Fin m → ℝ → ℂ}
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1)) (j : Fin m) (hj : 0 < j.val) :
    -derivWithin (s25bj_append L (s25bj_reverse R) (j.natAdd n - 1)) (Icc 0 1) 1 /
        derivWithin (s25bj_append L (s25bj_reverse R) (j.natAdd n)) (Icc 0 1) 0 =
      -derivWithin (R (⟨j.val - 1, by omega⟩ : Fin m).rev) (Icc 0 1) 0 /
        derivWithin (R j.rev) (Icc 0 1) 1 := by
  rw [s25bj_right_predecessor j hj, s25bj_append_right, s25bj_append_right,
    s25bj_reverse_derivWithin hRc _ ⟨zero_le_one, le_rfl⟩,
    s25bj_reverse_derivWithin hRc _ ⟨le_rfl, zero_le_one⟩]
  simp only [sub_self, sub_zero, neg_neg, div_neg, neg_div]

/-- At the first seam (the common starting point), the exact outgoing tangent
ratio is R_first'(0)/L_first'(0). -/
theorem s25bj_start_corner_ratio {n m : ℕ} [NeZero (n + m)] (hn : 0 < n) (hm : 0 < m)
    (L : Fin n → ℝ → ℂ) {R : Fin m → ℝ → ℂ}
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1)) :
    -derivWithin (s25bj_append L (s25bj_reverse R) (0 - 1)) (Icc 0 1) 1 /
        derivWithin (s25bj_append L (s25bj_reverse R) 0) (Icc 0 1) 0 =
      derivWithin (R ⟨0, hm⟩) (Icc 0 1) 0 /
        derivWithin (L ⟨0, hn⟩) (Icc 0 1) 0 := by
  have hz : (0 : Fin (n + m)) = (⟨0, hn⟩ : Fin n).castAdd m := by apply Fin.ext; rfl
  rw [s25bj_zero_predecessor hm, hz, s25bj_append_right, s25bj_append_left,
    s25bj_reverse_derivWithin hRc _ ⟨zero_le_one, le_rfl⟩,
    s25bj_reverse_last_index hm]
  simp

/-- At the second seam (the common terminal point), the ratio is
L_last'(1)/R_last'(1), with the reversal signs already cancelled. -/
theorem s25bj_end_corner_ratio {n m : ℕ} [NeZero (n + m)] (hn : 0 < n) (hm : 0 < m)
    (L : Fin n → ℝ → ℂ) {R : Fin m → ℝ → ℂ}
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1)) :
    -derivWithin (s25bj_append L (s25bj_reverse R) ((⟨n, by omega⟩ : Fin (n + m)) - 1))
        (Icc 0 1) 1 /
        derivWithin (s25bj_append L (s25bj_reverse R) ⟨n, by omega⟩) (Icc 0 1) 0 =
      derivWithin (L ⟨n - 1, by omega⟩) (Icc 0 1) 1 /
        derivWithin (R ⟨m - 1, by omega⟩) (Icc 0 1) 1 := by
  have hz : (⟨n, by omega⟩ : Fin (n + m)) = (⟨0, hm⟩ : Fin m).natAdd n := by
    apply Fin.ext
    simp
  rw [s25bj_seam_predecessor hn hm, hz, s25bj_append_left, s25bj_append_right,
    s25bj_reverse_derivWithin hRc _ ⟨le_rfl, zero_le_one⟩,
    s25bj_reverse_first_index hm]
  simp

/-- The only exceptional join indices are the start and the block boundary. -/
theorem s25bj_junction_card {n m : ℕ} [NeZero (n + m)] (hm : 0 < m) :
    ({(0 : Fin (n + m)), ⟨n, by omega⟩} : Finset (Fin (n + m))).card ≤ 2 := by
  classical
  by_cases h : (0 : Fin (n + m)) = ⟨n, by omega⟩
  · simp [h]
  · simp [Finset.card_pair h]

/-- Complete the chain from the seven proved fields, internal two-sided
corner bounds and the two separate seam non-cusp facts.
The angular hypotheses are precisely the work left to the geometry owner. -/
theorem s25bj_angle_completion {φ : ℂ → ℂ} {n m : ℕ} [NeZero (n + m)]
    (hm : 0 < m) {C : Fin (n + m) → ℝ → ℂ}
    (hbase : s25bj_BaseFields φ C)
    (hstart : arg (-derivWithin (C (0 - 1)) (Icc 0 1) 1 /
      derivWithin (C 0) (Icc 0 1) 0) ≠ 0)
    (hend : arg (-derivWithin (C ((⟨n, by omega⟩ : Fin (n + m)) - 1)) (Icc 0 1) 1 /
      derivWithin (C ⟨n, by omega⟩) (Icc 0 1) 0) ≠ 0)
    (hinterior : ∀ j : Fin (n + m), j ≠ 0 → j ≠ ⟨n, by omega⟩ →
      ∃ k : ℕ, meromorphicOrderAt φ (C j 0) = (k : ℤ) ∧
        2 * Real.pi / ((k : ℝ) + 2) ≤
          |arg (-derivWithin (C (j - 1)) (Icc 0 1) 1 / derivWithin (C j) (Icc 0 1) 0)| ∧
        2 * Real.pi / ((k : ℝ) + 2) ≤ 2 * Real.pi -
          |arg (-derivWithin (C (j - 1)) (Icc 0 1) 1 / derivWithin (C j) (Icc 0 1) 0)|) :
    fx_IsChain φ C ∧
      ∀ j, j ∉ ({0, ⟨n, by omega⟩} : Finset (Fin (n + m))) → fx_IsBlunt φ C j := by
  classical
  obtain ⟨hs, hc, hmC, hj, hi, hd0, hd1⟩ := hbase
  have hno : ∀ j, arg (-derivWithin (C (j - 1)) (Icc 0 1) 1 /
      derivWithin (C j) (Icc 0 1) 0) ≠ 0 := by
    intro j
    by_cases h0 : j = 0
    · simpa only [h0] using hstart
    by_cases hn : j = ⟨n, by omega⟩
    · simpa only [hn] using hend
    obtain ⟨k, _, hlo, _⟩ := hinterior j h0 hn
    exact s25gb_no_cusp_of_angle k hlo
  refine ⟨⟨hs, hc, hmC, hj, hi, hd0, hd1, hno⟩, ?_⟩
  intro j hjE
  have hj0 : j ≠ 0 := by intro he; apply hjE; simp [he]
  have hjn : j ≠ (⟨n, by omega⟩ : Fin (n + m)) := by intro he; apply hjE; simp [he]
  obtain ⟨k, hord, hlo, hhi⟩ := hinterior j hj0 hjn
  exact s25gb_blunt_of_angle j k hord hlo hhi

/-- Specialization exposing the two original tangent ratios to the geometry
owner. The interior conditions are on the explicitly constructed chain. -/
theorem s25bj_forward_reverse_angle_completion {φ : ℂ → ℂ} {n m : ℕ} [NeZero (n + m)]
    (hn : 0 < n) (hm : 0 < m)
    {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1))
    (hbase : s25bj_BaseFields φ (s25bj_append L (s25bj_reverse R)))
    (hstart : arg (derivWithin (R ⟨0, hm⟩) (Icc 0 1) 0 /
      derivWithin (L ⟨0, hn⟩) (Icc 0 1) 0) ≠ 0)
    (hend : arg (derivWithin (L ⟨n - 1, by omega⟩) (Icc 0 1) 1 /
      derivWithin (R ⟨m - 1, by omega⟩) (Icc 0 1) 1) ≠ 0)
    (hinterior : ∀ j : Fin (n + m), j ≠ 0 → j ≠ ⟨n, by omega⟩ →
      ∃ k : ℕ, meromorphicOrderAt φ (s25bj_append L (s25bj_reverse R) j 0) = (k : ℤ) ∧
        2 * Real.pi / ((k : ℝ) + 2) ≤
          |arg (-derivWithin (s25bj_append L (s25bj_reverse R) (j - 1)) (Icc 0 1) 1 /
            derivWithin (s25bj_append L (s25bj_reverse R) j) (Icc 0 1) 0)| ∧
        2 * Real.pi / ((k : ℝ) + 2) ≤ 2 * Real.pi -
          |arg (-derivWithin (s25bj_append L (s25bj_reverse R) (j - 1)) (Icc 0 1) 1 /
            derivWithin (s25bj_append L (s25bj_reverse R) j) (Icc 0 1) 0)|) :
    fx_IsChain φ (s25bj_append L (s25bj_reverse R)) ∧
      ∀ j, j ∉ ({0, ⟨n, by omega⟩} : Finset (Fin (n + m))) →
        fx_IsBlunt φ (s25bj_append L (s25bj_reverse R)) j := by
  apply s25bj_angle_completion hm hbase _ _ hinterior
  · rw [s25bj_start_corner_ratio hn hm L hRc]
    exact hstart
  · rw [s25bj_end_corner_ratio hn hm L hRc]
    exact hend

/-- The direct return-list orientation has the usual incoming/outgoing ratio
at its interior vertices. -/
theorem s25bj_right_corner_ratio {n m : ℕ} [NeZero (n + m)]
    (L : Fin n → ℝ → ℂ) (R : Fin m → ℝ → ℂ) (j : Fin m) (hj : 0 < j.val) :
    -derivWithin (s25bj_append L R (j.natAdd n - 1)) (Icc 0 1) 1 /
        derivWithin (s25bj_append L R (j.natAdd n)) (Icc 0 1) 0 =
      -derivWithin (R ⟨j.val - 1, by omega⟩) (Icc 0 1) 1 /
        derivWithin (R j) (Icc 0 1) 0 := by
  rw [s25bj_right_predecessor j hj, s25bj_append_right, s25bj_append_right]

/-- First seam when the increasing second source interval already has the
return orientation; no sign reversal is performed in this case. -/
theorem s25bj_oriented_start_corner_ratio {n m : ℕ} [NeZero (n + m)]
    (hn : 0 < n) (hm : 0 < m) (L : Fin n → ℝ → ℂ) (R : Fin m → ℝ → ℂ) :
    -derivWithin (s25bj_append L R (0 - 1)) (Icc 0 1) 1 /
        derivWithin (s25bj_append L R 0) (Icc 0 1) 0 =
      -derivWithin (R ⟨m - 1, by omega⟩) (Icc 0 1) 1 /
        derivWithin (L ⟨0, hn⟩) (Icc 0 1) 0 := by
  have hz : (0 : Fin (n + m)) = (⟨0, hn⟩ : Fin n).castAdd m := by apply Fin.ext; rfl
  rw [s25bj_zero_predecessor hm, hz, s25bj_append_right, s25bj_append_left]

theorem s25bj_oriented_end_corner_ratio {n m : ℕ} [NeZero (n + m)]
    (hn : 0 < n) (hm : 0 < m) (L : Fin n → ℝ → ℂ) (R : Fin m → ℝ → ℂ) :
    -derivWithin (s25bj_append L R ((⟨n, by omega⟩ : Fin (n + m)) - 1)) (Icc 0 1) 1 /
        derivWithin (s25bj_append L R ⟨n, by omega⟩) (Icc 0 1) 0 =
      -derivWithin (L ⟨n - 1, by omega⟩) (Icc 0 1) 1 /
        derivWithin (R ⟨0, hm⟩) (Icc 0 1) 0 := by
  have hz : (⟨n, by omega⟩ : Fin (n + m)) = (⟨0, hm⟩ : Fin m).natAdd n := by
    apply Fin.ext
    simp
  rw [s25bj_seam_predecessor hn hm, hz, s25bj_append_left, s25bj_append_right]

/-- The vertex at a reversed side is its original terminal point. This fixes
the point at which the geometry owner must supply the zero-order identity. -/
theorem s25bj_reverse_vertex {n m : ℕ} (L : Fin n → ℝ → ℂ)
    (R : Fin m → ℝ → ℂ) (j : Fin m) :
    s25bj_append L (s25bj_reverse R) (j.natAdd n) 0 = R j.rev 1 := by
  rw [s25bj_append_right]
  simp only [s25bj_reverse, sub_zero]

end LiZhongQC

