import LiZhongQC.Lemmas.GeodesicBigonChain
open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold
noncomputable section
namespace LiZhongQC

/-- Recover the symmetric absolute angle interval from FluxRoute bluntness. -/
theorem s25bg_blunt_absolute {φ : ℂ → ℂ} {n : ℕ} [NeZero n]
    {side : Fin n → ℝ → ℂ} {j : Fin n} (h : fx_IsBlunt φ side j) :
    ∃ k : ℕ, meromorphicOrderAt φ (side j 0) = (k : ℤ) ∧
      2 * Real.pi / ((k : ℝ) + 2) ≤
        |arg (-derivWithin (side (j - 1)) (Icc 0 1) 1 / derivWithin (side j) (Icc 0 1) 0)| ∧
      2 * Real.pi / ((k : ℝ) + 2) ≤ 2 * Real.pi -
        |arg (-derivWithin (side (j - 1)) (Icc 0 1) 1 / derivWithin (side j) (Icc 0 1) 0)| := by
  obtain ⟨k, hord, hlo, hhi⟩ := h
  refine ⟨k, hord, ?_⟩
  unfold fx_chainAngle at hlo hhi
  split_ifs at hlo hhi with hpos
  · rw [abs_of_pos hpos]
    exact ⟨hlo, by linarith⟩
  · rw [abs_of_nonpos (le_of_not_gt hpos)]
    constructor <;> linarith

/-- Reversing an adjacent pair inverts its tangent ratio and preserves the
absolute argument. This is the symmetry needed for the return half of a bigon. -/
theorem s25bg_reverse_abs_arg (d e : ℂ) :
    |arg (-e / d)| = |arg (-d / e)| := by
  have he : -e / d = (-d / e)⁻¹ := by
    simp only [inv_div, div_neg]
    ring
  rw [he, Complex.abs_arg_inv]

theorem s25bc_blunt_no_cusp {φ : ℂ → ℂ} {N : ℕ} [NeZero N]
    {C : Fin N → ℝ → ℂ} {j : Fin N} (h : fx_IsBlunt φ C j) :
    arg (-derivWithin (C (j - 1)) (Icc 0 1) 1 /
      derivWithin (C j) (Icc 0 1) 0) ≠ 0 := by
  obtain ⟨k, _, hlo, _⟩ := s25bg_blunt_absolute h
  exact s25gb_no_cusp_of_angle k hlo

theorem s25bc_index_pos {N : ℕ} [NeZero N] {i : Fin N} (hi : i ≠ 0) :
    0 < i.val := by
  by_contra h
  apply hi
  apply Fin.ext
  change i.val = 0
  omega

theorem s25bc_index_pred {N : ℕ} [NeZero N] (i : Fin N) (hi : i ≠ 0) :
    i - 1 = (⟨i.val - 1, by omega⟩ : Fin N) := by
  apply Fin.ext
  exact Fin.val_sub_one_of_ne_zero hi

/-- The original internal corner corresponding to a reversed return corner
j is k=(j-1).rev, not j.rev. Its incoming original side is j.rev. -/
theorem s25bc_reverse_corner_index {m : ℕ} [NeZero m] (j : Fin m) (hj : j ≠ 0) :
    (⟨j.val - 1, by omega⟩ : Fin m).rev ≠ 0 ∧
      (⟨j.val - 1, by omega⟩ : Fin m).rev - 1 = j.rev := by
  have hjp := s25bc_index_pos hj
  let k : Fin m := (⟨j.val - 1, by omega⟩ : Fin m).rev
  have hv : j.rev.val + 1 = k.val := by
    dsimp [k]
    omega
  have hk : k ≠ 0 := by
    intro he
    have he' := congrArg Fin.val he
    change k.val = 0 at he'
    omega
  have hs : j.rev + 1 = k := s25bj_succ_of_val hv
  refine ⟨hk, ?_⟩
  change k - 1 = j.rev
  rw [← hs, add_sub_cancel_right]

/-- The order-evaluation points agree by a join already present in the
assembled chain. The caller does not have to reconstruct a source next proof. -/
theorem s25bc_reverse_vertex_join {n m : ℕ} [NeZero m] [NeZero (n + m)]
    (L : Fin n → ℝ → ℂ) (R : Fin m → ℝ → ℂ)
    (hnext : ∀ i, s25bj_append L (s25bj_reverse R) i 1 =
      s25bj_append L (s25bj_reverse R) (i + 1) 0)
    (j : Fin m) (hj : j ≠ 0) :
    R j.rev 1 = R (⟨j.val - 1, by omega⟩ : Fin m).rev 0 := by
  have hjp := s25bc_index_pos hj
  let q : Fin m := ⟨j.val - 1, by omega⟩
  have hs : q.natAdd n + 1 = j.natAdd n := s25bj_succ_of_val (by
    change n + (j.val - 1) + 1 = n + j.val
    omega)
  have he := hnext (q.natAdd n)
  rw [hs, s25bj_append_right, s25bj_append_right] at he
  change R q.rev (1 - 1) = R j.rev (1 - 0) at he
  simp only [sub_self, sub_zero] at he
  exact he.symm

/-- Bluntness of a first-list internal corner survives the finite append. -/
theorem s25bc_append_left_blunt {φ : ℂ → ℂ} {n m : ℕ}
    [NeZero n] [NeZero (n + m)]
    {L : Fin n → ℝ → ℂ} (R : Fin m → ℝ → ℂ)
    (i : Fin n) (hi : i ≠ 0) (hb : fx_IsBlunt φ L i) :
    fx_IsBlunt φ (s25bj_append L R) (i.castAdd m) := by
  obtain ⟨k, hord, hlo, hhi⟩ := s25bg_blunt_absolute hb
  apply s25gb_blunt_of_angle (i.castAdd m) k
  · simpa only [s25bj_append_left] using hord
  · rw [s25bj_left_corner_ratio L R i (s25bc_index_pos hi), ← s25bc_index_pred i hi]
    exact hlo
  · rw [s25bj_left_corner_ratio L R i (s25bc_index_pos hi), ← s25bc_index_pred i hi]
    exact hhi

theorem s25bc_append_right_blunt {φ : ℂ → ℂ} {n m : ℕ}
    [NeZero m] [NeZero (n + m)]
    (L : Fin n → ℝ → ℂ) {R : Fin m → ℝ → ℂ}
    (j : Fin m) (hj : j ≠ 0) (hb : fx_IsBlunt φ R j) :
    fx_IsBlunt φ (s25bj_append L R) (j.natAdd n) := by
  obtain ⟨k, hord, hlo, hhi⟩ := s25bg_blunt_absolute hb
  apply s25gb_blunt_of_angle (j.natAdd n) k
  · simpa only [s25bj_append_right] using hord
  · rw [s25bj_right_corner_ratio L R j (s25bc_index_pos hj), ← s25bc_index_pred j hj]
    exact hlo
  · rw [s25bj_right_corner_ratio L R j (s25bc_index_pos hj), ← s25bc_index_pred j hj]
    exact hhi

/-- Reverse-list interior bluntness, including all index and zero-order
transport. Its only geometric input is the original corner's fx_IsBlunt. -/
theorem s25bc_reverse_right_blunt {φ : ℂ → ℂ} {n m : ℕ}
    [NeZero m] [NeZero (n + m)]
    (L : Fin n → ℝ → ℂ) {R : Fin m → ℝ → ℂ}
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1))
    (hnext : ∀ i, s25bj_append L (s25bj_reverse R) i 1 =
      s25bj_append L (s25bj_reverse R) (i + 1) 0)
    (hR : ∀ j, j ≠ 0 → fx_IsBlunt φ R j) (j : Fin m) (hj : j ≠ 0) :
    fx_IsBlunt φ (s25bj_append L (s25bj_reverse R)) (j.natAdd n) := by
  let k : Fin m := (⟨j.val - 1, by omega⟩ : Fin m).rev
  obtain ⟨hk, hpred⟩ := s25bc_reverse_corner_index j hj
  obtain ⟨r, hord, hlo, hhi⟩ := s25bg_blunt_absolute (hR k hk)
  have hvertex : s25bj_append L (s25bj_reverse R) (j.natAdd n) 0 = R k 0 := by
    rw [s25bj_reverse_vertex L R j]
    exact s25bc_reverse_vertex_join L R hnext j hj
  have harg :
      |arg (-derivWithin (s25bj_append L (s25bj_reverse R) (j.natAdd n - 1)) (Icc 0 1) 1 /
        derivWithin (s25bj_append L (s25bj_reverse R) (j.natAdd n)) (Icc 0 1) 0)| =
      |arg (-derivWithin (R (k - 1)) (Icc 0 1) 1 / derivWithin (R k) (Icc 0 1) 0)| := by
    rw [s25bj_reverse_right_corner_ratio L hRc j (s25bc_index_pos hj)]
    change |arg (-derivWithin (R k) (Icc 0 1) 0 / derivWithin (R j.rev) (Icc 0 1) 1)| = _
    rw [show k - 1 = j.rev from hpred]
    exact s25bg_reverse_abs_arg _ _
  apply s25gb_blunt_of_angle (j.natAdd n) r
  · rw [hvertex]
    exact hord
  · rw [harg]
    exact hlo
  · rw [harg]
    exact hhi

/-- Every non-seam corner of the assembled reverse-return chain comes from
one of the original internal blunt corners. -/
theorem s25bc_reverse_interior_blunt {φ : ℂ → ℂ} {n m : ℕ}
    [NeZero n] [NeZero m] [NeZero (n + m)]
    (hm : 0 < m) {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1))
    (hbase : s25bj_BaseFields φ (s25bj_append L (s25bj_reverse R)))
    (hL : ∀ i, i ≠ 0 → fx_IsBlunt φ L i)
    (hR : ∀ j, j ≠ 0 → fx_IsBlunt φ R j) :
    ∀ j : Fin (n + m), j ≠ 0 → j ≠ ⟨n, by omega⟩ →
      fx_IsBlunt φ (s25bj_append L (s25bj_reverse R)) j := by
  refine Fin.addCases ?_ ?_
  · intro i h0 _
    have hi : i ≠ 0 := by
      intro he
      apply h0
      apply Fin.ext
      simp [he]
    exact s25bc_append_left_blunt (s25bj_reverse R) i hi (hL i hi)
  · intro j _ hn
    have hj : j ≠ 0 := by
      intro he
      apply hn
      apply Fin.ext
      simp [he]
    exact s25bc_reverse_right_blunt L hRc hbase.2.2.2.1 hR j hj

theorem s25bc_direct_interior_blunt {φ : ℂ → ℂ} {n m : ℕ}
    [NeZero n] [NeZero m] [NeZero (n + m)]
    (hm : 0 < m) {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    (hL : ∀ i, i ≠ 0 → fx_IsBlunt φ L i)
    (hR : ∀ j, j ≠ 0 → fx_IsBlunt φ R j) :
    ∀ j : Fin (n + m), j ≠ 0 → j ≠ ⟨n, by omega⟩ →
      fx_IsBlunt φ (s25bj_append L R) j := by
  refine Fin.addCases ?_ ?_
  · intro i h0 _
    have hi : i ≠ 0 := by
      intro he
      apply h0
      apply Fin.ext
      simp [he]
    exact s25bc_append_left_blunt R i hi (hL i hi)
  · intro j _ hn
    have hj : j ≠ 0 := by
      intro he
      apply hn
      apply Fin.ext
      simp [he]
    exact s25bc_append_right_blunt L j hj (hR j hj)

/-- Ready-to-use reversed-return consumer. Internal geometry is supplied
only as the original families' fx_IsBlunt facts. -/
theorem s25bc_forward_reverse_complete {φ : ℂ → ℂ} {n m : ℕ}
    [NeZero n] [NeZero m] [NeZero (n + m)]
    (hn : 0 < n) (hm : 0 < m)
    {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1))
    (hbase : s25bj_BaseFields φ (s25bj_append L (s25bj_reverse R)))
    (hL : ∀ i, i ≠ 0 → fx_IsBlunt φ L i)
    (hR : ∀ j, j ≠ 0 → fx_IsBlunt φ R j)
    (hstart : arg (derivWithin (R ⟨0, hm⟩) (Icc 0 1) 0 /
      derivWithin (L ⟨0, hn⟩) (Icc 0 1) 0) ≠ 0)
    (hend : arg (derivWithin (L ⟨n - 1, by omega⟩) (Icc 0 1) 1 /
      derivWithin (R ⟨m - 1, by omega⟩) (Icc 0 1) 1) ≠ 0) :
    fx_IsChain φ (s25bj_append L (s25bj_reverse R)) ∧
      ({(0 : Fin (n + m)), ⟨n, by omega⟩} : Finset (Fin (n + m))).card ≤ 2 ∧
      ∀ j, j ∉ ({0, ⟨n, by omega⟩} : Finset (Fin (n + m))) →
        fx_IsBlunt φ (s25bj_append L (s25bj_reverse R)) j := by
  have hi := s25bc_reverse_interior_blunt hm hRc hbase hL hR
  obtain ⟨hchain, hblunt⟩ := s25bj_forward_reverse_angle_completion hn hm hRc hbase
    hstart hend (fun j h0 hj => s25bg_blunt_absolute (hi j h0 hj))
  exact ⟨hchain, s25bj_junction_card hm, hblunt⟩

/-- Ready-to-use consumer when the second list already has the return
orientation. The physical seam ratios retain their incoming minus signs. -/
theorem s25bc_direct_complete {φ : ℂ → ℂ} {n m : ℕ}
    [NeZero n] [NeZero m] [NeZero (n + m)]
    (hn : 0 < n) (hm : 0 < m)
    {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    (hbase : s25bj_BaseFields φ (s25bj_append L R))
    (hL : ∀ i, i ≠ 0 → fx_IsBlunt φ L i)
    (hR : ∀ j, j ≠ 0 → fx_IsBlunt φ R j)
    (hstart : arg (-derivWithin (R ⟨m - 1, by omega⟩) (Icc 0 1) 1 /
      derivWithin (L ⟨0, hn⟩) (Icc 0 1) 0) ≠ 0)
    (hend : arg (-derivWithin (L ⟨n - 1, by omega⟩) (Icc 0 1) 1 /
      derivWithin (R ⟨0, hm⟩) (Icc 0 1) 0) ≠ 0) :
    fx_IsChain φ (s25bj_append L R) ∧
      ({(0 : Fin (n + m)), ⟨n, by omega⟩} : Finset (Fin (n + m))).card ≤ 2 ∧
      ∀ j, j ∉ ({0, ⟨n, by omega⟩} : Finset (Fin (n + m))) →
        fx_IsBlunt φ (s25bj_append L R) j := by
  have hi := s25bc_direct_interior_blunt hm hL hR
  have hs : arg (-derivWithin (s25bj_append L R (0 - 1)) (Icc 0 1) 1 /
      derivWithin (s25bj_append L R 0) (Icc 0 1) 0) ≠ 0 := by
    rw [s25bj_oriented_start_corner_ratio hn hm L R]
    exact hstart
  have he : arg (-derivWithin (s25bj_append L R ((⟨n, by omega⟩ : Fin (n + m)) - 1))
        (Icc 0 1) 1 /
      derivWithin (s25bj_append L R ⟨n, by omega⟩) (Icc 0 1) 0) ≠ 0 := by
    rw [s25bj_oriented_end_corner_ratio hn hm L R]
    exact hend
  obtain ⟨hchain, hblunt⟩ := s25bj_angle_completion hm hbase hs he
    (fun j h0 hj => s25bg_blunt_absolute (hi j h0 hj))
  exact ⟨hchain, s25bj_junction_card hm, hblunt⟩

/-- The finite-chain exclusion can now consume the original internal blunt
facts and the two actual seam non-cusp facts directly. This is a conditional
assembly endpoint, not a proof that the remaining seam geometry holds. -/
theorem s25bc_forward_reverse_false {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {n m : ℕ} [NeZero n] [NeZero m] [NeZero (n + m)]
    (hn : 0 < n) (hm : 0 < m)
    {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1))
    (hbase : s25bj_BaseFields φ (s25bj_append L (s25bj_reverse R)))
    (hL : ∀ i, i ≠ 0 → fx_IsBlunt φ L i)
    (hR : ∀ j, j ≠ 0 → fx_IsBlunt φ R j)
    (hstart : arg (derivWithin (R ⟨0, hm⟩) (Icc 0 1) 0 /
      derivWithin (L ⟨0, hn⟩) (Icc 0 1) 0) ≠ 0)
    (hend : arg (derivWithin (L ⟨n - 1, by omega⟩) (Icc 0 1) 1 /
      derivWithin (R ⟨m - 1, by omega⟩) (Icc 0 1) 1) ≠ 0) : False := by
  obtain ⟨hchain, hcard, hblunt⟩ :=
    s25bc_forward_reverse_complete hn hm hRc hbase hL hR hstart hend
  exact s25gb_chain_excluded hφ hne hchain {0, ⟨n, by omega⟩} hcard hblunt

theorem s25bc_direct_false {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ unitDisc) (hne : ∃ z ∈ unitDisc, φ z ≠ 0)
    {n m : ℕ} [NeZero n] [NeZero m] [NeZero (n + m)]
    (hn : 0 < n) (hm : 0 < m)
    {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    (hbase : s25bj_BaseFields φ (s25bj_append L R))
    (hL : ∀ i, i ≠ 0 → fx_IsBlunt φ L i)
    (hR : ∀ j, j ≠ 0 → fx_IsBlunt φ R j)
    (hstart : arg (-derivWithin (R ⟨m - 1, by omega⟩) (Icc 0 1) 1 /
      derivWithin (L ⟨0, hn⟩) (Icc 0 1) 0) ≠ 0)
    (hend : arg (-derivWithin (L ⟨n - 1, by omega⟩) (Icc 0 1) 1 /
      derivWithin (R ⟨0, hm⟩) (Icc 0 1) 0) ≠ 0) : False := by
  obtain ⟨hchain, hcard, hblunt⟩ := s25bc_direct_complete hn hm hbase hL hR hstart hend
  exact s25gb_chain_excluded hφ hne hchain {0, ⟨n, by omega⟩} hcard hblunt

/-- Exact forward/reverse completion contract for the geometry consumer.
The two original noninitial blunt families and the physical seam ratios are
the only angular inputs; all Fin and inverse-angle work is internal. -/
theorem s25bc_forward_reverse_completion {φ : ℂ → ℂ} {n m : ℕ}
    [NeZero n] [NeZero m] [NeZero (n + m)]
    (hn : 0 < n) (hm : 0 < m)
    {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    (hbase : s25bj_BaseFields φ (s25bj_append L (s25bj_reverse R)))
    (hRc : ∀ j, ContDiffOn ℝ 1 (R j) (Icc 0 1))
    (hL : ∀ i : Fin n, i ≠ 0 → fx_IsBlunt φ L i)
    (hR : ∀ j : Fin m, j ≠ 0 → fx_IsBlunt φ R j)
    (hstart : arg (derivWithin (R 0) (Icc 0 1) 0 /
      derivWithin (L 0) (Icc 0 1) 0) ≠ 0)
    (hend : arg (derivWithin (L ⟨n - 1, by omega⟩) (Icc 0 1) 1 /
      derivWithin (R ⟨m - 1, by omega⟩) (Icc 0 1) 1) ≠ 0) :
    fx_IsChain φ (s25bj_append L (s25bj_reverse R)) ∧
      ∀ j, j ∉ ({0, ⟨n, by omega⟩} : Finset (Fin (n + m))) →
        fx_IsBlunt φ (s25bj_append L (s25bj_reverse R)) j := by
  have hzL : (⟨0, hn⟩ : Fin n) = 0 := by apply Fin.ext; rfl
  have hzR : (⟨0, hm⟩ : Fin m) = 0 := by apply Fin.ext; rfl
  obtain ⟨hchain, _, hblunt⟩ := s25bc_forward_reverse_complete hn hm hRc hbase hL hR
    (by simpa only [hzL, hzR] using hstart) hend
  exact ⟨hchain, hblunt⟩

/-- Exact already-returning completion contract, with the original endpoint
derivatives and no supplementary vertex or angle-conversion premise. -/
theorem s25bc_direct_completion {φ : ℂ → ℂ} {n m : ℕ}
    [NeZero n] [NeZero m] [NeZero (n + m)]
    (hn : 0 < n) (hm : 0 < m)
    {L : Fin n → ℝ → ℂ} {R : Fin m → ℝ → ℂ}
    (hbase : s25bj_BaseFields φ (s25bj_append L R))
    (hL : ∀ i : Fin n, i ≠ 0 → fx_IsBlunt φ L i)
    (hR : ∀ j : Fin m, j ≠ 0 → fx_IsBlunt φ R j)
    (hstart : arg (-derivWithin (R ⟨m - 1, by omega⟩) (Icc 0 1) 1 /
      derivWithin (L 0) (Icc 0 1) 0) ≠ 0)
    (hend : arg (-derivWithin (L ⟨n - 1, by omega⟩) (Icc 0 1) 1 /
      derivWithin (R 0) (Icc 0 1) 0) ≠ 0) :
    fx_IsChain φ (s25bj_append L R) ∧
      ∀ j, j ∉ ({0, ⟨n, by omega⟩} : Finset (Fin (n + m))) →
        fx_IsBlunt φ (s25bj_append L R) j := by
  have hzL : (⟨0, hn⟩ : Fin n) = 0 := by apply Fin.ext; rfl
  have hzR : (⟨0, hm⟩ : Fin m) = 0 := by apply Fin.ext; rfl
  obtain ⟨hchain, _, hblunt⟩ := s25bc_direct_complete hn hm hbase hL hR
    (by simpa only [hzL] using hstart) (by simpa only [hzR] using hend)
  exact ⟨hchain, hblunt⟩

end LiZhongQC

