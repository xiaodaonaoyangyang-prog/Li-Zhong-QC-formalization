import LiZhongQC.Lemmas.GeodesicRegularSide
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- A two-sided local interval property has a finite strictly ordered
partition. The cover is constructed from the local windows; its finitely many
selected centers are inserted as cuts, so no final gap crosses its center. -/
theorem s25cv_partition_of_local_halves {R : ℝ → ℝ → Prop} {a b : ℝ} (hab : a < b)
    (hloc : ∀ x ∈ Icc a b, ∃ δ > 0, ∀ s t : ℝ,
      a ≤ s → s < t → t ≤ b → x - δ < s → t < x + δ →
        (t ≤ x ∨ x ≤ s) → R s t) :
    ∃ (n : ℕ) (p : Fin (n + 1) → ℝ), 0 < n ∧ StrictMono p ∧
      p 0 = a ∧ p (Fin.last n) = b ∧ (∀ i, p i ∈ Icc a b) ∧
      ∀ j : Fin n, R (p j.castSucc) (p j.succ) := by
  classical
  have hloc' : ∀ x : Icc a b, ∃ δ > 0, ∀ s t : ℝ,
      a ≤ s → s < t → t ≤ b → x.val - δ < s → t < x.val + δ →
        (t ≤ x.val ∨ x.val ≤ s) → R s t := fun x => hloc x.val x.property
  choose ε hε hgood using hloc'
  let C : Icc a b → Set (Icc a b) := fun x =>
    {y | x.val - ε x < y.val ∧ y.val < x.val + ε x}
  have hCo : ∀ x, IsOpen (C x) := fun x =>
    isOpen_Ioo.preimage continuous_subtype_val
  have hcover : (univ : Set (Icc a b)) ⊆ ⋃ x, C x := by
    intro x hx
    refine mem_iUnion.2 ⟨x, ?_⟩
    change x.val - ε x < x.val ∧ x.val < x.val + ε x
    constructor <;> linarith [hε x]
  obtain ⟨t, ht0, htm, ⟨m, hend⟩, hstep⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc hab.le hCo hcover
  choose center hcenter using hstep
  have htm' : (t m : ℝ) = b := hend m le_rfl
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    rw [hm0, ht0] at htm'
    exact hab.ne htm'
  let grid : Fin (m + 1) → ℝ := fun i => t i.val
  let tag : Fin m → ℝ := fun i => center i.val
  let Z : Set ℝ := range grid ∪ range tag
  have hZ : Z.Finite := (finite_range grid).union (finite_range tag)
  have hZa : a ∈ Z := Or.inl ⟨0, ht0⟩
  have hZb : b ∈ Z := Or.inl ⟨Fin.last m, htm'⟩
  have hZI : Z ⊆ Icc a b := by
    intro z hz
    rcases hz with hz | hz
    · obtain ⟨i, rfl⟩ := hz
      exact (t i.val).property
    · obtain ⟨i, rfl⟩ := hz
      exact (center i.val).property
  obtain ⟨n, p, hn, hp, hp0, hp1, hprange⟩ :=
    s25gb_ordered_breakpoints hZ hab hZa hZb hZI
  have hpI : ∀ i, p i ∈ Icc a b := fun i => hZI (hprange ▸ mem_range_self i)
  refine ⟨n, p, hn, hp, hp0, hp1, hpI, ?_⟩
  intro j
  let x := p j.castSucc
  let y := p j.succ
  have hxy : x < y := hp (show j.castSucc < j.succ from Fin.castSucc_lt_succ)
  have hxI : x ∈ Icc a b := hpI j.castSucc
  have hyI : y ∈ Icc a b := hpI j.succ
  have hgrid : ∀ k ≤ m, (t k : ℝ) ∈ range p := by
    intro k hk
    rw [hprange]
    exact Or.inl ⟨⟨k, by omega⟩, rfl⟩
  have htag : ∀ k < m, (center k : ℝ) ∈ range p := by
    intro k hk
    rw [hprange]
    exact Or.inr ⟨⟨k, hk⟩, rfl⟩
  have hxm : x < (t m : ℝ) := by rw [htm']; exact hxy.trans_le hyI.2
  have hex : ∃ k : ℕ, x < (t k : ℝ) := ⟨m, hxm⟩
  let N := Nat.find hex
  have hNx : x < (t N : ℝ) := Nat.find_spec hex
  have hNm : N ≤ m := Nat.find_min' hex hxm
  have hN : 0 < N := by
    by_contra h
    have hN0 : N = 0 := by omega
    rw [hN0, ht0] at hNx
    exact (not_lt_of_ge hxI.1) hNx
  let k := N - 1
  have hkN : k + 1 = N := by dsimp [k]; omega
  have hklt : k < N := by dsimp [k]; omega
  have hkm : k < m := by omega
  have hkx : (t k : ℝ) ≤ x := le_of_not_gt (Nat.find_min hex hklt)
  have hyN : y ≤ (t N : ℝ) := by
    by_contra h
    have hNy : (t N : ℝ) < y := lt_of_not_ge h
    exact s25gb_gap_avoids_breakpoints hp j ⟨hNx, hNy⟩ (hgrid N hNm)
  have hxC : (⟨x, hxI⟩ : Icc a b) ∈ C (center k) := by
    apply hcenter k
    constructor
    · exact hkx
    · change x ≤ (t (k + 1) : ℝ)
      rw [hkN]
      exact hNx.le
  have hyC : (⟨y, hyI⟩ : Icc a b) ∈ C (center k) := by
    apply hcenter k
    constructor
    · exact hkx.trans hxy.le
    · change y ≤ (t (k + 1) : ℝ)
      rw [hkN]
      exact hyN
  have hsplit : y ≤ (center k : ℝ) ∨ (center k : ℝ) ≤ x := by
    by_cases h : (center k : ℝ) ≤ x
    · exact Or.inr h
    · left
      apply le_of_not_gt
      intro h'
      exact s25gb_gap_avoids_breakpoints hp j ⟨lt_of_not_ge h, h'⟩ (htag k hkm)
  exact hgood (center k) x y hxI.1 hxy hyI.2 hxC.1 hyC.2 hsplit

/-- A straight side has no zero contact in the interior of its original time
interval. Thus the constructed partition automatically contains all zero times. -/
theorem s25cv_side_regular_interior {φ : ℂ → ℂ} {f : ℝ → ℂ} {a b : ℝ}
    (S : s25cv_Side φ f a b) {t : ℝ} (ht : t ∈ Ioo a b) : φ (f t) ≠ 0 := by
  obtain ⟨u, hu, hut⟩ := S.bij.2.2 (Ioo_subset_Icc_self ht)
  have hu0 : 0 < u := by
    apply (S.mono.lt_iff_lt (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) hu).1
    simpa only [S.first, hut] using ht.1
  have hu1 : u < 1 := by
    apply (S.mono.lt_iff_lt hu (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num)).1
    simpa only [S.last, hut] using ht.2
  obtain ⟨θ, hθ⟩ := S.straight
  have hne := (hθ u ⟨hu0, hu1⟩).2.2.1
  intro hz
  rw [S.trace u hu, hut, hz, zero_mul] at hne
  exact hne rfl

end LiZhongQC

