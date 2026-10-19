import LiZhongQC.Lemmas.GeodesicExtraction
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real
noncomputable section
namespace LiZhongQC

/-- Enumerate a finite subset of an interval in its actual increasing order.
The two endpoints ensure a nonempty family of nondegenerate gaps. -/
theorem s25gb_ordered_breakpoints {Z : Set ℝ} (hZ : Z.Finite)
    {a b : ℝ} (hab : a < b) (ha : a ∈ Z) (hb : b ∈ Z) (hsub : Z ⊆ Icc a b) :
    ∃ (n : ℕ) (p : Fin (n + 1) → ℝ), 0 < n ∧ StrictMono p ∧
      p 0 = a ∧ p (Fin.last n) = b ∧ Set.range p = Z := by
  classical
  let S := hZ.toFinset
  have haS : a ∈ S := hZ.mem_toFinset.2 ha
  have hbS : b ∈ S := hZ.mem_toFinset.2 hb
  have hcard : 2 ≤ S.card := by
    have hpair : ({a, b} : Finset ℝ) ⊆ S := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact haS
      · exact hbS
    have h := Finset.card_le_card hpair
    simpa [Finset.card_pair (ne_of_lt hab)] using h
  let n := S.card - 1
  have hN : S.card = n + 1 := by dsimp [n]; omega
  let p : Fin (n + 1) → ℝ := S.orderEmbOfFin hN
  have hp : StrictMono p := (S.orderEmbOfFin hN).strictMono
  have hrange : Set.range p = Z := by
    rw [show Set.range p = (↑S : Set ℝ) from Finset.range_orderEmbOfFin S hN]
    exact hZ.coe_toFinset
  have hmem : ∀ i, p i ∈ Icc a b := fun i => hsub (hrange ▸ mem_range_self i)
  have hpa : p 0 = a := by
    obtain ⟨i, hi⟩ := hrange.symm ▸ ha
    exact le_antisymm (by simpa [hi] using hp.monotone (show (0 : Fin (n + 1)) ≤ i from Fin.zero_le i))
      (hmem 0).1
  have hpb : p (Fin.last n) = b := by
    obtain ⟨i, hi⟩ := hrange.symm ▸ hb
    exact le_antisymm (hmem (Fin.last n)).2
      (by simpa [hi] using hp.monotone (Fin.le_last i))
  exact ⟨n, p, by dsimp [n]; omega, hp, hpa, hpb, hrange⟩

/-- No member of the enumerated breakpoint set lies strictly between two
consecutive cuts. -/
theorem s25gb_gap_avoids_breakpoints {n : ℕ} {p : Fin (n + 1) → ℝ}
    (hp : StrictMono p) (j : Fin n) {t : ℝ}
    (ht : t ∈ Ioo (p j.castSucc) (p j.succ)) : t ∉ Set.range p := by
  rintro ⟨k, hk⟩
  have h₁ : j.castSucc < k := hp.lt_iff_lt.1 (by simpa [hk] using ht.1)
  have h₂ : k < j.succ := hp.lt_iff_lt.1 (by simpa [hk] using ht.2)
  have h₁' : j.val < k.val := h₁
  have h₂' : k.val < j.val + 1 := h₂
  omega

/-- Actual finite zero contacts give an ordered partition of any nontrivial
subarc. Every open gap is regular, including subarcs extracted as loops or bigons. -/
theorem s25gb_regular_partition {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {γ : LRCurve} (hγ : IsPhiGeodesic φ unitDisc γ)
    (hpause : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 →
      ∃ u ∈ Icc s t, γ.toFun u ≠ γ.toFun s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ (n : ℕ) (p : Fin (n + 1) → ℝ), 0 < n ∧ StrictMono p ∧
      p 0 = a ∧ p (Fin.last n) = b ∧
      (∀ i, p i ∈ Icc a b) ∧
      ∀ j : Fin n, ∀ t ∈ Ioo (p j.castSucc) (p j.succ), φ (γ.toFun t) ≠ 0 := by
  classical
  let Z : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ φ (γ.toFun t) = 0}
  have hZ : Z.Finite := s25fc_zero_contacts_finite hφ hne hγ hpause
  let B := insert a (insert b (Z ∩ Icc a b))
  have hB : B.Finite := ((hZ.inter_of_left _).insert b).insert a
  have hsub : B ⊆ Icc a b := by
    intro t ht
    rcases ht with rfl | ht
    · exact ⟨le_rfl, hab.le⟩
    rcases ht with rfl | ht
    · exact ⟨hab.le, le_rfl⟩
    · exact ht.2
  obtain ⟨n, p, hn, hp, h0, h1, hr⟩ := s25gb_ordered_breakpoints hB hab
    (mem_insert _ _) (mem_insert_of_mem _ (mem_insert _ _)) hsub
  have hmem : ∀ i, p i ∈ Icc a b := fun i => hsub (hr ▸ mem_range_self i)
  refine ⟨n, p, hn, hp, h0, h1, hmem, ?_⟩
  intro j t ht hz
  have htB : t ∈ B := by
    have htab : t ∈ Icc a b :=
      ⟨(hmem j.castSucc).1.trans ht.1.le, ht.2.le.trans (hmem j.succ).2⟩
    exact mem_insert_of_mem _ (mem_insert_of_mem _ ⟨⟨⟨ha.trans htab.1, htab.2.trans hb⟩, hz⟩, htab⟩)
  exact s25gb_gap_avoids_breakpoints hp j ht (hr.symm ▸ htB)

/-- A monotone local parameter map sends half-open sides to half-open gaps. -/
theorem s25gb_parameter_halfopen {h : ℝ → ℝ} {a b : ℝ}
    (hh : StrictMonoOn h (Icc (0 : ℝ) 1)) (h0 : h 0 = a) (h1 : h 1 = b)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : h t ∈ Ico a b := by
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  constructor
  · rw [← h0]
    exact hh.monotoneOn ⟨le_rfl, zero_le_one⟩ htI ht.1
  · rw [← h1]
    exact hh htI ⟨zero_le_one, le_rfl⟩ ht.2

/-- The key chain simplicity proof. An injective half-open loop parameter
and increasing disjoint parameter gaps force both the side index and its
parameter to agree. No spatial disjointness premise is required. -/
theorem s25gb_partition_simple {n : ℕ} {p : Fin (n + 1) → ℝ}
    (hp : StrictMono p) {f : ℝ → ℂ}
    (hf : InjOn f (Ico (p 0) (p (Fin.last n))))
    {side : Fin n → ℝ → ℂ} {par : Fin n → ℝ → ℝ}
    (hpar : ∀ j, StrictMonoOn (par j) (Icc (0 : ℝ) 1))
    (h0 : ∀ j, par j 0 = p j.castSucc) (h1 : ∀ j, par j 1 = p j.succ)
    (heq : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, side j t = f (par j t)) :
    ∀ i j : Fin n, ∀ s ∈ Ico (0 : ℝ) 1, ∀ t ∈ Ico (0 : ℝ) 1,
      side i s = side j t → i = j ∧ s = t := by
  have hgap : ∀ j, ∀ t ∈ Ico (0 : ℝ) 1, par j t ∈ Ico (p j.castSucc) (p j.succ) :=
    fun j t ht => s25gb_parameter_halfopen (hpar j) (h0 j) (h1 j) ht
  have hwhole : ∀ j, ∀ t ∈ Ico (0 : ℝ) 1,
      par j t ∈ Ico (p 0) (p (Fin.last n)) := by
    intro j t ht
    have hjt := hgap j t ht
    exact ⟨(hp.monotone (Fin.zero_le _)).trans hjt.1,
      hjt.2.trans_le (hp.monotone (Fin.le_last _))⟩
  intro i j s hs t ht he
  have hepar : par i s = par j t := hf (hwhole i s hs) (hwhole j t ht)
    ((heq i s ⟨hs.1, hs.2.le⟩).symm.trans (he.trans (heq j t ⟨ht.1, ht.2.le⟩)))
  have hij : i = j := by
    rcases lt_trichotomy i j with hij | hij | hij
    · have hord : i.succ ≤ j.castSucc := by
        have h : i.val < j.val := hij
        change i.val + 1 ≤ j.val
        omega
      have hlt := (hgap i s hs).2.trans_le (hp.monotone hord)
      have hle := (hgap j t ht).1
      rw [hepar] at hlt
      exact False.elim ((not_lt_of_ge hle) hlt)
    · exact hij
    · have hord : j.succ ≤ i.castSucc := by
        have h : j.val < i.val := hij
        change j.val + 1 ≤ i.val
        omega
      have hlt := (hgap j t ht).2.trans_le (hp.monotone hord)
      have hle := (hgap i s hs).1
      rw [← hepar] at hlt
      exact False.elim ((not_lt_of_ge hle) hlt)
  subst j
  exact ⟨rfl, (hpar i).injOn ⟨hs.1, hs.2.le⟩ ⟨ht.1, ht.2.le⟩ hepar⟩

/-- Cyclic successor either advances one cut or wraps from the last cut
to the first. This isolates the `Fin n` arithmetic from chain assembly. -/
theorem s25gb_cyclic_cuts {n : ℕ} [NeZero n] (j : Fin n) :
    (j + 1).castSucc = j.succ ∨
      (j.succ = Fin.last n ∧ (j + 1).castSucc = (0 : Fin (n + 1))) := by
  have hn : 0 < n := NeZero.pos n
  have hv : (j + 1).val = (j.val + 1) % n := by
    simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  by_cases hj : j.val + 1 < n
  · left
    apply Fin.ext
    change (j + 1).val = j.val + 1
    rw [hv, Nat.mod_eq_of_lt hj]
  · right
    have hj' : j.val + 1 = n := by omega
    constructor
    · apply Fin.ext
      exact hj'
    · apply Fin.ext
      change (j + 1).val = 0
      rw [hv, hj', Nat.mod_self]

/-- Consecutive sides from a partition of a closed parameter interval join,
including the last-to-first join. -/
theorem s25gb_partition_next {n : ℕ} [NeZero n] {p : Fin (n + 1) → ℝ}
    {f : ℝ → ℂ} (hclosed : f (p 0) = f (p (Fin.last n)))
    {side : Fin n → ℝ → ℂ}
    (h0 : ∀ j, side j 0 = f (p j.castSucc))
    (h1 : ∀ j, side j 1 = f (p j.succ)) :
    ∀ j, side j 1 = side (j + 1) 0 := by
  intro j
  rw [h1, h0]
  rcases s25gb_cyclic_cuts j with h | h
  · rw [h]
  · rw [h.1, h.2]
    exact hclosed.symm

/-- Assemble a finite smooth chain on an extracted simple loop. All
geometric regularity and angle data are local side/corner inputs. Global
simplicity and cyclic joining are derived from the parameter partition. -/
theorem s25gb_chain_of_partition {φ : ℂ → ℂ} {n : ℕ} [NeZero n]
    {p : Fin (n + 1) → ℝ} (hp : StrictMono p) {f : ℝ → ℂ}
    (hf : InjOn f (Ico (p 0) (p (Fin.last n))))
    (hclosed : f (p 0) = f (p (Fin.last n)))
    (hmem : ∀ t ∈ Icc (p 0) (p (Fin.last n)), f t ∈ unitDisc)
    {side : Fin n → ℝ → ℂ} {par : Fin n → ℝ → ℝ}
    (hpar : ∀ j, StrictMonoOn (par j) (Icc (0 : ℝ) 1))
    (h0 : ∀ j, par j 0 = p j.castSucc) (h1 : ∀ j, par j 1 = p j.succ)
    (heq : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, side j t = f (par j t))
    (hstr : ∀ j, IsPhiStraightArc φ (side j) 0 1)
    (hsm : ∀ j, ContDiffOn ℝ 1 (side j) (Icc 0 1))
    (ht0 : ∀ j, derivWithin (side j) (Icc 0 1) 0 ≠ 0)
    (ht1 : ∀ j, derivWithin (side j) (Icc 0 1) 1 ≠ 0)
    (hcusp : ∀ j,
      arg (-derivWithin (side (j - 1)) (Icc 0 1) 1 / derivWithin (side j) (Icc 0 1) 0) ≠ 0) :
    fx_IsChain φ side := by
  refine ⟨hstr, hsm, ?_, ?_, s25gb_partition_simple hp hf hpar h0 h1 heq, ht0, ht1, hcusp⟩
  · intro j z hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [heq j t ht]
    apply hmem
    have hlow := (hpar j).monotoneOn ⟨le_rfl, zero_le_one⟩ ht ht.1
    have hupp := (hpar j).monotoneOn ht ⟨zero_le_one, le_rfl⟩ ht.2
    rw [h0] at hlow
    rw [h1] at hupp
    exact ⟨(hp.monotone (Fin.zero_le _)).trans hlow,
      hupp.trans (hp.monotone (Fin.le_last _))⟩
  · apply s25gb_partition_next hclosed
    · intro j
      rw [heq j 0 ⟨le_rfl, zero_le_one⟩, h0]
    · intro j
      rw [heq j 1 ⟨zero_le_one, le_rfl⟩, h1]

/-- The installed Teichmüller exclusion disallows a chain with at most two
exceptional corners. This is the common loop/bigon terminal consumer. -/
theorem s25gb_chain_excluded {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {n : ℕ} [NeZero n] {side : Fin n → ℝ → ℂ} (hchain : fx_IsChain φ side)
    (E : Finset (Fin n)) (hE : E.card ≤ 2)
    (hblunt : ∀ j, j ∉ E → fx_IsBlunt φ side j) : False := by
  have hthree := fx_chain_false hφ hne hchain
  have hsub : {j : Fin n | ¬ fx_IsBlunt φ side j} ⊆ (↑E : Set (Fin n)) := by
    intro j hj
    by_contra hjE
    exact hj (hblunt j hjE)
  have hbound := Set.ncard_le_ncard hsub (Set.toFinite _)
  have htwo : {j : Fin n | ¬ fx_IsBlunt φ side j}.ncard ≤ 2 := by
    exact hbound.trans (by simpa using hE)
  omega

/-- Convert the two unoriented angle bounds supplied by ZeroCorner into
the oriented corner interval used by FluxRoute, for either sign of arg. -/
theorem s25gb_oriented_angle {z : ℂ} {α : ℝ}
    (hlo : α ≤ |arg z|) (hhi : α ≤ 2 * Real.pi - |arg z|) :
    α ≤ (if 0 < arg z then arg z else arg z + 2 * Real.pi) ∧
      (if 0 < arg z then arg z else arg z + 2 * Real.pi) ≤ 2 * Real.pi - α := by
  by_cases hz : 0 < arg z
  · rw [if_pos hz]
    rw [abs_of_pos hz] at hlo hhi
    exact ⟨hlo, by linarith⟩
  · rw [if_neg hz]
    rw [abs_of_nonpos (le_of_not_gt hz)] at hlo hhi
    constructor <;> linarith

/-- A positive absolute corner-angle bound excludes a cusp. -/
theorem s25gb_no_cusp_of_angle (m : ℕ) {z : ℂ}
    (hlo : 2 * Real.pi / ((m : ℝ) + 2) ≤ |arg z|) : arg z ≠ 0 := by
  have hpos : 0 < 2 * Real.pi / ((m : ℝ) + 2) := by positivity
  intro hz
  rw [hz, abs_zero] at hlo
  exact (not_le_of_gt hpos) hlo

/-- The zero-order and absolute tangent-angle conclusions match the literal
FluxRoute blunt-corner predicate, without an orientation assumption. -/
theorem s25gb_blunt_of_angle {φ : ℂ → ℂ} {n : ℕ} [NeZero n]
    {side : Fin n → ℝ → ℂ} (j : Fin n) (m : ℕ)
    (hord : meromorphicOrderAt φ (side j 0) = (m : ℤ))
    (hlo : 2 * Real.pi / ((m : ℝ) + 2) ≤
      |arg (-derivWithin (side (j - 1)) (Icc 0 1) 1 / derivWithin (side j) (Icc 0 1) 0)|)
    (hhi : 2 * Real.pi / ((m : ℝ) + 2) ≤ 2 * Real.pi -
      |arg (-derivWithin (side (j - 1)) (Icc 0 1) 1 / derivWithin (side j) (Icc 0 1) 0)|) :
    fx_IsBlunt φ side j := by
  refine ⟨m, hord, ?_⟩
  exact s25gb_oriented_angle hlo hhi

end LiZhongQC

