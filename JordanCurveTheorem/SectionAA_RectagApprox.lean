/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionZ_K33Nonplanar

/-!
# Section AA: Rectagon Approximation
## HOL Light: Section AA (Lines 50961–54218)

Bridge between continuous curves and combinatorial grid curves.
Key results:
- `simple_arc_conn_complement`: complement of a simple arc is connected
- `cut_arc` definition and properties
- `simple_closed_curve_cut_unique`: cut uniqueness on simple closed curves
- `simple_arc_infinite`: simple arcs are infinite sets
- `jordan_curve_access`: access lemma for the Jordan Curve Theorem
-/

open Set Finset Metric Filter Topology

namespace JordanCurveTheorem

section
-- Elevated heartbeats: proofs in this section use `fin_cases` on `Fin 3` arc indices and
-- repeated `norm_num`/`simp` on rational interval bounds (1/8, 3/8, 5/8, etc.); the
-- accumulated elaboration cost across the section exceeds the default heartbeat budget.
set_option linter.style.setOption false in
set_option maxHeartbeats 400000


-- §AA.1 Mathlib-level lemmas (real_div_denom, suc_div, etc.)
-- These HOL Light theorems correspond to existing Mathlib lemmas.
-- See CSV for Lean_Mathlib_Equivalent column.


-- 1286: real_div_denom → Mathlib: div_le_div_right
-- 1287: real_div_denom_lt → Mathlib: div_lt_div_right
-- 1289: euclid_scale_rinv → Mathlib: mul_inv_cancel₀ + one_smul
-- 1290: euclid_scale_bij → Mathlib: Function.Bijective via smul
-- 1291: euclid_scale_cont → Mathlib: continuous_const_smul
-- 1292: euclid_scale_inv → Mathlib: inv_smul_smul₀
-- 1293: euclid_scale_homeo → Mathlib: Homeomorph via smul
-- 1297: delta_pos_arch → Mathlib: exists_nat_gt / Archimedean
-- 1298: suc_div → Mathlib: add_div
-- 1306: int_range_finite → Mathlib: Set.Finite.ofFinset
-- 1307: subs_lemma → trivial logic
-- 1308/1309: int2_range_finite → Mathlib: Set.Finite for product
-- 1319: continuous_real_const → Mathlib: continuous_const
-- 1320: continuous_real_mul → Mathlib: continuous_mul_left
-- 1331: open_real_interval → Mathlib: isOpen_Ioo
-- 1333: infinite_closed_interval → Mathlib: Set.Infinite for Icc
-- 1334: infinite_image → Mathlib: Set.Infinite.image

/-! ## §AA.2 Not applicable to Lean -/

-- 1310: grid33_finite → grid33 returns Finset, finiteness by construction
-- 1330: simple_closed_curve_euclid → C : Set E2', so C ⊆ Set.univ is trivial

/-! ## §AA.3 Simple arc decomposition -/

/-- HOL Light: `simple_arc_constants` (line 50995).
Decompose a simple arc into sub-arcs with separation constants. -/
theorem simple_arc_constants {C : Set E2'} {p q : E2'}
    (hC : IsSimpleArc C) (hp : p ∉ C) (hq : q ∉ C) (_hpq : p ≠ q)
    (hinter : ∀ A : Set E2', IsSimpleArcEnd A p q → (C ∩ A).Nonempty) :
    ∃ (d d' : ℝ) (N : ℕ) (B : ℕ → Set E2') (a : ℕ → E2'),
      0 < d ∧ 0 < d' ∧ 0 < N ∧
      (∀ i, i < N → IsSimpleArcEnd (B i) (a i) (a (i + 1))) ∧
      C = ⋃ i ∈ Finset.range N, B i ∧
      (∀ x ∈ C, 8 * d ≤ dist x p ∧ 8 * d ≤ dist x q) ∧
      (∀ i j x y, i + 1 < j → j < N → x ∈ B i → y ∈ B j →
        16 * d' < dist x y) ∧
      (∀ i, i < N → ∃ x ∈ B i, B i ⊆ Metric.ball x d) := by
  obtain ⟨f, rfl, hcont, hinj⟩ := hC
  have hcompact := isSimpleArc_compact ⟨f, rfl, hcont, hinj⟩
  have hnonempty : (f '' Icc 0 1).Nonempty :=
    ⟨f 0, Set.mem_image_of_mem f ⟨le_refl 0, zero_le_one⟩⟩
  -- Step 1: Distance to p and q
  have hdp := (hcompact.isClosed.notMem_iff_infDist_pos hnonempty).mp hp
  have hdq := (hcompact.isClosed.notMem_iff_infDist_pos hnonempty).mp hq
  set dp := Metric.infDist p (f '' Icc 0 1)
  set dq := Metric.infDist q (f '' Icc 0 1)
  set ε := min dp dq / 8 with hε_def
  have hε_pos : 0 < ε := div_pos (lt_min hdp hdq) (by norm_num : (0 : ℝ) < 8)
  have h8d : ∀ x ∈ f '' Icc 0 1, 8 * ε ≤ dist x p ∧ 8 * ε ≤ dist x q := by
    intro x hx
    have h8ε : 8 * ε = min dp dq := by change 8 * (min dp dq / 8) = min dp dq; ring
    constructor <;> rw [h8ε]
    · calc min dp dq ≤ dp := min_le_left _ _
        _ = Metric.infDist p (f '' Icc 0 1) := rfl
        _ ≤ dist p x := Metric.infDist_le_dist_of_mem hx
        _ = dist x p := dist_comm _ _
    · calc min dp dq ≤ dq := min_le_right _ _
        _ = Metric.infDist q (f '' Icc 0 1) := rfl
        _ ≤ dist q x := Metric.infDist_le_dist_of_mem hx
        _ = dist x q := dist_comm _ _
  -- Step 2: Uniform continuity → δ
  have huc := simple_arc_uniformly_continuous f hcont hinj
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ_pos, hδ⟩ := huc ε hε_pos
  -- Step 3: Choose N > 1/δ and N ≥ 2
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / δ)
  set N := max N₀ 2 with hN_def
  have hNpos : 0 < N := by omega
  have hN_ge_2 : 2 ≤ N := le_max_right N₀ 2
  have hNR : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hNpos
  have hNδ : 1 / (↑N : ℝ) < δ := by
    rw [div_lt_iff₀ hNR]
    calc (1 : ℝ) = δ * (1 / δ) := by field_simp
      _ < δ * ↑N₀ := by nlinarith
      _ ≤ δ * ↑N := by nlinarith [show (↑N₀ : ℝ) ≤ ↑N from
          Nat.cast_le.mpr (le_max_left N₀ 2)]
  -- Define B and a
  set B : ℕ → Set E2' := fun i => f '' Icc (↑i / ↑N) (↑(i + 1) / ↑N)
  set a : ℕ → E2' := fun i => f (↑i / ↑N)
  have hi_Icc : ∀ i, i < N → (↑i / ↑N : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro i hi
    exact ⟨div_nonneg (Nat.cast_nonneg i) hNR.le,
      (div_le_one hNR).mpr (by exact_mod_cast hi.le)⟩
  have hi1_Icc : ∀ i, i < N → (↑(i + 1) / ↑N : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro i hi
    exact ⟨div_nonneg (by positivity) hNR.le,
      (div_le_one hNR).mpr (by exact_mod_cast (Nat.succ_le_of_lt hi))⟩
  have hi_lt : ∀ i, i < N → (↑i : ℝ) / ↑N < ↑(i + 1) / ↑N := by
    intro i _
    exact div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_of_le le_rfl) hNR
  have hIcc_sub : ∀ i, i < N → Icc (↑i / ↑N : ℝ) (↑(i + 1) / ↑N) ⊆ Icc 0 1 :=
    fun i hi => Icc_subset_Icc (hi_Icc i hi).1 (hi1_Icc i hi).2
  -- Step 4: Each B(i) is a simple arc end
  have hBi_arc : ∀ i, i < N → IsSimpleArcEnd (B i) (a i) (a (i + 1)) := by
    intro i hi
    obtain ⟨g, hgcont, hginj, hg0, hg1, hgimg⟩ :=
      arc_reparameter_gen hcont (hinj.mono (hIcc_sub i hi)) zero_lt_one (hi_lt i hi)
    exact ⟨g, hgimg, hgcont, hginj, hg0, hg1⟩
  -- Step 5: C = ⋃ B(i)
  have hunion : f '' Icc 0 1 = ⋃ i ∈ Finset.range N, B i := by
    ext x; simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_image, B]
    constructor
    · rintro ⟨t, ht, rfl⟩
      by_cases ht1 : t = 1
      · refine ⟨N - 1, Nat.sub_lt hNpos Nat.one_pos, t, ?_, rfl⟩
        subst ht1; constructor
        · rw [div_le_one hNR]; exact_mod_cast Nat.sub_le N 1
        · have : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos hNpos
          change (1 : ℝ) ≤ ↑(N - 1 + 1) / ↑N
          rw [this, div_self (ne_of_gt hNR)]
      · have ht1' : t < 1 := lt_of_le_of_ne ht.2 ht1
        set i := ⌊t * ↑N⌋₊ with hi_def
        have hiN : i < N :=
          hi_def ▸ (Nat.floor_lt (mul_nonneg ht.1 hNR.le)).mpr (by nlinarith)
        refine ⟨i, hiN, t, ?_, rfl⟩
        constructor
        · -- ↑i / ↑N ≤ t ← ⌊t*N⌋₊ ≤ t*N → ⌊t*N⌋₊/N ≤ t
          rw [div_le_iff₀ hNR]
          exact_mod_cast Nat.floor_le (mul_nonneg ht.1 hNR.le)
        · -- t ≤ ↑(i+1) / ↑N ← t*N < ⌊t*N⌋₊ + 1
          rw [le_div_iff₀ hNR]
          exact_mod_cast (Nat.lt_floor_add_one (t * ↑N)).le
    · rintro ⟨i, hi, t, ht, rfl⟩
      exact ⟨t, ⟨(hIcc_sub i hi ht).1, (hIcc_sub i hi ht).2⟩, rfl⟩
  -- Step 6: Ball cover (1/N < δ so diameter of each B(i) < ε)
  have hball : ∀ i, i < N → ∃ x ∈ B i, B i ⊆ Metric.ball x ε := by
    intro i hi
    refine ⟨a i, ⟨↑i / ↑N, ⟨le_refl _, (hi_lt i hi).le⟩, rfl⟩, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    rw [Metric.mem_ball, dist_comm]
    apply hδ (↑i / ↑N) (hi_Icc i hi) t (hIcc_sub i hi ht)
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.1)]
    calc -(↑i / ↑N - t) = t - ↑i / ↑N := by ring
      _ ≤ ↑(i + 1) / ↑N - ↑i / ↑N := by linarith [ht.2]
      _ = 1 / ↑N := by push_cast; ring
      _ < δ := hNδ
  -- Step 7: Non-adjacent B(i), B(j) are disjoint
  have hBi_compact : ∀ i, i < N → IsCompact (B i) :=
    fun i hi => isCompact_Icc.image_of_continuousOn (hcont.continuousOn.mono (hIcc_sub i hi))
  have hBi_nonempty : ∀ i, i < N → (B i).Nonempty :=
    fun i hi => ⟨a i, ⟨↑i / ↑N, ⟨le_refl _, (hi_lt i hi).le⟩, rfl⟩⟩
  have hBi_disj : ∀ i j, i + 1 < j → j < N → Disjoint (B i) (B j) := by
    intro i j hij hjN; rw [Set.disjoint_left]
    rintro x ⟨s, hs, hxs⟩ ⟨t, ht, hxt⟩
    have hst : s = t :=
      hinj (hIcc_sub i (by omega) hs) (hIcc_sub j hjN ht) (hxs.trans hxt.symm)
    have : (↑(i + 1) : ℝ) / ↑N < ↑j / ↑N :=
      div_lt_div_of_pos_right (by exact_mod_cast hij) hNR
    linarith [hs.2, ht.1, hst]
  -- Step 8: Non-adjacent separation d'
  have hsd_pos : ∀ i j, i + 1 < j → j < N → 0 < setDist (B i) (B j) := by
    intro i j hij hjN
    obtain ⟨p₀, hp₀, p₁, hp₁, heq⟩ := compact_distance
      (hBi_compact i (by omega)) (hBi_compact j hjN)
      (hBi_nonempty i (by omega)) (hBi_nonempty j hjN)
    rw [heq]; exact dist_pos.mpr
      (fun h => Set.disjoint_left.mp (hBi_disj i j hij hjN) hp₀ (h ▸ hp₁))
  -- Extract d' using Finset induction (avoids expensive Finset.min' unification)
  suffices ∃ d' > 0, ∀ i j, i + 1 < j → j < N →
      ∀ x ∈ B i, ∀ y ∈ B j, 16 * d' < dist x y by
    obtain ⟨d', hd', hbound⟩ := this
    exact ⟨ε, d', N, B, a, hε_pos, hd', hNpos, hBi_arc, hunion, h8d,
      fun i j x y hij hjN hxi hyj => hbound i j hij hjN x hxi y hyj, hball⟩
  set pairs := ((Finset.range N) ×ˢ (Finset.range N)).filter
    (fun p => p.1 + 2 ≤ p.2) with hpairs_def
  suffices h_gen : ∀ S : Finset (ℕ × ℕ),
      (∀ p ∈ S, p.1 + 1 < p.2 ∧ p.2 < N) →
      ∃ d' > 0, ∀ p ∈ S, ∀ x ∈ B p.1, ∀ y ∈ B p.2, 16 * d' < dist x y by
    obtain ⟨d', hd', hbound⟩ := h_gen pairs (fun p hp => by
      simp only [hpairs_def, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range] at hp; exact ⟨by omega, hp.1.2⟩)
    exact ⟨d', hd', fun i j hij hjN x hxi y hyj =>
      hbound (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr hjN⟩,
        by omega⟩) x hxi y hyj⟩
  intro S; refine Finset.induction_on S (fun _ => ⟨1, one_pos, fun _ h => absurd h (by simp)⟩) ?_
  intro a_new s_rest ha ih hS
  obtain ⟨d₁, hd₁, hd₁_bound⟩ := ih
    (fun p hp => hS p (Finset.mem_insert_of_mem hp))
  obtain ⟨hij₀, hjN₀⟩ := hS a_new (Finset.mem_insert_self a_new s_rest)
  have hsd₀ := hsd_pos a_new.1 a_new.2 hij₀ hjN₀
  refine ⟨min d₁ (setDist (B a_new.1) (B a_new.2) / 17),
    lt_min hd₁ (by positivity), fun p hp x hx y hy => ?_⟩
  rcases Finset.mem_insert.mp hp with rfl | hp
  · calc 16 * min d₁ (setDist (B p.1) (B p.2) / 17)
        ≤ 16 * (setDist (B p.1) (B p.2) / 17) := by
          nlinarith [min_le_right d₁ (setDist (B p.1) (B p.2) / 17)]
      _ < setDist (B p.1) (B p.2) := by nlinarith [hsd₀]
      _ ≤ dist x y := setDist_le_dist hx hy
  · calc 16 * min d₁ (setDist (B a_new.1) (B a_new.2) / 17)
        ≤ 16 * d₁ := by
          nlinarith [min_le_left d₁ (setDist (B a_new.1) (B a_new.2) / 17)]
      _ < dist x y := hd₁_bound p hp x hx y hy

/-! ## §AA.4 Scaling / homeomorphism lemmas -/

/-- HOL Light: `simple_arc_end_homeo` (line 51494).
Homeomorphism preserves simple_arc_end. -/
theorem isSimpleArcEnd_homeo {C : Set E2'} {a b : E2'} (f : E2' ≃ₜ E2')
    (hC : IsSimpleArcEnd C a b) :
    IsSimpleArcEnd (f '' C) (f a) (f b) := by
  obtain ⟨g, rfl, hcont, hinj, hg0, hg1⟩ := hC
  refine ⟨f ∘ g, by rw [Set.image_comp], f.continuous.comp hcont, ?_, by simp [hg0],
    by simp [hg1]⟩
  exact fun x hx y hy heq => hinj hx hy (f.injective heq)

/-- HOL Light: `simple_arc_homeo` (line 51528).
Homeomorphism preserves simple_arc. -/
theorem isSimpleArc_homeo {C : Set E2'} (f : E2' ≃ₜ E2')
    (hC : IsSimpleArc C) :
    IsSimpleArc (f '' C) := by
  obtain ⟨g, rfl, hcont, hinj⟩ := hC
  exact ⟨f ∘ g, by rw [Set.image_comp], f.continuous.comp hcont,
    fun x hx y hy heq => hinj hx hy (f.injective heq)⟩

/-- HOL Light: `euclid_scale_simple_arc_ver2` (line 51545).
Rescale arc configuration so d, d' ≥ 1. -/
theorem euclid_scale_simple_arc_ver2 {C : Set E2'} {p q : E2'}
    (hC : IsSimpleArc C) (hp : p ∉ C) (hq : q ∉ C) (hpq : p ≠ q)
    (hinter : ∀ A : Set E2', IsSimpleArcEnd A p q → (C ∩ A).Nonempty) :
    ∃ (C' : Set E2') (p' q' : E2') (d : ℝ) (N : ℕ)
      (B : ℕ → Set E2') (a : ℕ → E2') (d' : ℝ),
      IsSimpleArc C' ∧ p' ∉ C' ∧ q' ∉ C' ∧ p' ≠ q' ∧
      (∀ A : Set E2', IsSimpleArcEnd A p' q' → (C' ∩ A).Nonempty) ∧
      1 ≤ d ∧ 1 ≤ d' ∧ 0 < N ∧
      (∀ i, i < N → IsSimpleArcEnd (B i) (a i) (a (i + 1))) ∧
      C' = ⋃ i ∈ Finset.range N, B i ∧
      (∀ x ∈ C', 8 * d ≤ dist x p' ∧ 8 * d ≤ dist x q') ∧
      (∀ i j x y, i + 1 < j → j < N → x ∈ B i → y ∈ B j →
        16 * d' < dist x y) ∧
      (∀ i, i < N → ∃ x ∈ B i, B i ⊆ Metric.ball x d) := by
  -- Step 1: Get constants from simple_arc_constants
  obtain ⟨d₀, d₀', N, B₀, a₀, hd₀, hd₀', hNpos, hBi, hunion, h8d, hsep, hball⟩ :=
    simple_arc_constants hC hp hq hpq hinter
  -- Step 2: Scale by 1/r where r = min d₀ d₀'
  set r := min d₀ d₀'
  have hr : 0 < r := lt_min hd₀ hd₀'
  have hrinv : (0 : ℝ) < r⁻¹ := inv_pos.mpr hr
  set φ : E2' ≃ₜ E2' := Homeomorph.smulOfNeZero r⁻¹ hrinv.ne'
  have hφ_eq : ∀ z : E2', φ z = r⁻¹ • z :=
    fun z => congr_fun (Homeomorph.smulOfNeZero_apply r⁻¹ hrinv.ne') z
  have hdist : ∀ x y : E2', dist (φ x) (φ y) = r⁻¹ * dist x y := by
    intro x y; rw [hφ_eq, hφ_eq, dist_smul₀, Real.norm_eq_abs, abs_of_pos hrinv]
  -- Step 3: Package the result
  refine ⟨φ '' C, φ p, φ q, d₀ / r, N, fun i => φ '' B₀ i, fun i => φ (a₀ i), d₀' / r,
    isSimpleArc_homeo φ hC, ?_, ?_, fun h => hpq (φ.injective h), ?_,
    (le_div_iff₀ hr).mpr ?_, (le_div_iff₀ hr).mpr ?_, hNpos,
    fun i hi => isSimpleArcEnd_homeo φ (hBi i hi), ?_, ?_, ?_, ?_⟩
  -- p' ∉ C'
  · intro h; obtain ⟨z, hz, hze⟩ := h; exact hp (φ.injective hze ▸ hz)
  -- q' ∉ C'
  · intro h; obtain ⟨z, hz, hze⟩ := h; exact hq (φ.injective hze ▸ hz)
  -- Intersection property: ∀ A, IsSimpleArcEnd A p' q' → (C' ∩ A).Nonempty
  · intro A hA
    have hA' : IsSimpleArcEnd (φ.symm '' A) p q := by
      have := isSimpleArcEnd_homeo φ.symm hA
      simp only [Homeomorph.symm_apply_apply] at this; exact this
    obtain ⟨z, hzC, hzA'⟩ := hinter _ hA'
    obtain ⟨w, hwA, hwz⟩ := hzA'
    subst hwz
    exact ⟨w, ⟨⟨φ.symm w, hzC, φ.apply_symm_apply w⟩, hwA⟩⟩
  -- 1 ≤ d₀ / r (i.e. r ≤ d₀)
  · nlinarith [min_le_left d₀ d₀']
  -- 1 ≤ d₀' / r (i.e. r ≤ d₀')
  · nlinarith [min_le_right d₀ d₀']
  -- Union: C' = ⋃ i ∈ range N, B' i
  · rw [hunion, Set.image_iUnion₂]
  -- 8d separation
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨h1, h2⟩ := h8d z hz
    constructor <;> rw [hdist]
    · have := mul_le_mul_of_nonneg_left h1 hrinv.le
      linarith [show 8 * (d₀ / r) = r⁻¹ * (8 * d₀) from by ring]
    · have := mul_le_mul_of_nonneg_left h2 hrinv.le
      linarith [show 8 * (d₀ / r) = r⁻¹ * (8 * d₀) from by ring]
  -- 16d' separation
  · rintro i j _ _ hij hjN ⟨x₀, hx₀, rfl⟩ ⟨y₀, hy₀, rfl⟩
    rw [hdist]
    have := mul_lt_mul_of_pos_left (hsep i j x₀ y₀ hij hjN hx₀ hy₀) hrinv
    linarith [show 16 * (d₀' / r) = r⁻¹ * (16 * d₀') from by ring]
  -- Ball containment
  · intro i hi
    obtain ⟨x₀, hx₀, hball_i⟩ := hball i hi
    refine ⟨φ x₀, Set.mem_image_of_mem _ hx₀, fun y hy => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hy
    rw [Metric.mem_ball, hdist]
    have := mul_lt_mul_of_pos_left (Metric.mem_ball.mp (hball_i hz)) hrinv
    linarith [show d₀ / r = r⁻¹ * d₀ from by ring]

/-! ## §AA.5 Grid partition and cover (ver2) -/

/-- HOL Light: `delta_partition_lemma_ver2` (line 51812).
For any δ > 0, ∃ M such that ∀ N ≥ M, the grid {i/N} covers [0,1] within δ. -/
theorem delta_partition_lemma_ver2 (delta : ℝ) (hd : 0 < delta) :
    ∃ M : ℕ, 0 < M ∧ ∀ N : ℕ, M ≤ N → ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      ∃ i : ℕ, i ≤ N ∧ |↑i / ↑N - x| < delta := by
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / delta)
  have hMpos : 0 < M := by
    by_contra h; simp only [not_lt, Nat.le_zero] at h
    subst h; simp at hM; linarith [div_pos one_pos hd]
  refine ⟨M, hMpos, fun N hMN x hx0 hx1 => ?_⟩
  have hNpos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr (hMpos.trans_le hMN)
  have hNd : 1 ≤ ↑N * delta := by
    have : 1 / delta ≤ (↑M : ℝ) := hM.le
    have : (↑M : ℝ) ≤ ↑N := Nat.cast_le.mpr hMN
    calc (1 : ℝ) = delta * (1 / delta) := by field_simp
      _ ≤ delta * ↑N := by nlinarith
      _ = ↑N * delta := by ring
  use ⌊↑N * x⌋₊
  have hnn : (0 : ℝ) ≤ ↑N * x := mul_nonneg hNpos.le hx0
  have hfl : (↑⌊↑N * x⌋₊ : ℝ) ≤ ↑N * x := Nat.floor_le hnn
  have hlt : ↑N * x < ↑⌊↑N * x⌋₊ + 1 := Nat.lt_floor_add_one _
  have hfl_div : ↑⌊↑N * x⌋₊ / ↑N ≤ x := by
    rw [div_le_iff₀ hNpos]; linarith [mul_comm x (↑N : ℝ)]
  constructor
  · exact Nat.floor_le_of_le (by
      calc ↑N * x ≤ ↑N * 1 := by nlinarith
        _ = ↑N := by ring)
  · calc |↑⌊↑N * x⌋₊ / ↑N - x|
        = x - ↑⌊↑N * x⌋₊ / ↑N := by
          rw [abs_of_nonpos (by linarith)]; ring
      _ = (↑N * x - ↑⌊↑N * x⌋₊) / ↑N := by field_simp
      _ < 1 / ↑N :=
          div_lt_div_of_pos_right (by linarith) hNpos
      _ ≤ delta := by
          rw [div_le_iff₀ hNpos]
          linarith [mul_comm delta (↑N : ℝ)]

/-- HOL Light: `simple_arc_ball_cover_ver2` (line 51881).
For continuous injective f, ∃ M s.t. ∀ N ≥ M, ∀ x ∈ [0,1], ∃ i ≤ N
with f(x) ∈ ball(f(i/N), 1). -/
theorem simple_arc_ball_cover_ver2 (f : ℝ → E2)
    (hcont : Continuous f) (hinj : InjOn f (Icc 0 1)) :
    ∃ M : ℕ, 0 < M ∧ ∀ N : ℕ, M ≤ N → ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
      ∃ i : ℕ, i ≤ N ∧ dist (f (↑i / ↑N)) (f x) < 1 := by
  have huc := simple_arc_uniformly_continuous f hcont hinj
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδpos, hδ⟩ := huc 1 one_pos
  obtain ⟨M, hMpos, hM⟩ := delta_partition_lemma_ver2 δ hδpos
  refine ⟨M, hMpos, fun N hMN x hx0 hx1 => ?_⟩
  obtain ⟨i, hiN, hiδ⟩ := hM N hMN x hx0 hx1
  have hNpos : (0 : ℝ) < ↑N :=
    Nat.cast_pos.mpr (hMpos.trans_le hMN)
  have hiN_Icc : (↑i : ℝ) / ↑N ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (Nat.cast_nonneg' i) hNpos.le, ?_⟩
    rw [div_le_one hNpos]; exact_mod_cast hiN
  have hx_Icc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0, hx1⟩
  have hdist : dist ((↑i : ℝ) / ↑N) x < δ := by
    rw [Real.dist_eq]; exact hiδ
  exact ⟨i, hiN, hδ _ hiN_Icc _ hx_Icc hdist⟩

/-- HOL Light: `grid_image_bounded_ver2` (line 51926).
For continuous injective f, ∃ M s.t. ∀ N ≥ M, the image of f avoids the
unbounded set of grid f N. -/
theorem grid_image_bounded_ver2 (f : ℝ → E2)
    (hcont : Continuous f) (hinj : InjOn f (Icc 0 1)) :
    ∃ M : ℕ, 0 < M ∧ ∀ N : ℕ, M ≤ N →
      Disjoint (f '' Icc 0 1) {x | UnboundedSet (grid f N) x} := by
  obtain ⟨M, hM, hcover⟩ := simple_arc_ball_cover_ver2 f hcont hinj
  refine ⟨M, hM, fun N hMN => Set.disjoint_left.mpr fun y hy hunb => ?_⟩
  obtain ⟨x', hx'mem, rfl⟩ := hy
  obtain ⟨i, hiN, hdist⟩ := hcover N hMN x' hx'mem.1 hx'mem.2
  set m₀ := (⌊(f (↑i / ↑N)) 0⌋, ⌊(f (↑i / ↑N)) 1⌋) with hm₀_def
  have hE_sub : grid33 m₀ ⊆ grid f N := by
    intro e he; simp only [grid, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_range.mpr (by omega), he⟩
  have hcc : f x' ∉ ⋃₀ (curveCells (grid33 m₀) : Set (Set E2)) :=
    unbounded_set_curve_cell_empty (grid33 m₀) (grid f N) _ hunb hE_sub
  set m₁ := (⌊(f x') 0⌋, ⌊(f x') 1⌋) with hm₁_def
  have h0 := d_euclid_floor _ _ 0 hdist
  have h1 := d_euclid_floor _ _ 1 hdist
  have hE'_sub : rectangle_grid m₁ (m₁.1 + 1, m₁.2 + 1) ⊆ grid33 m₀ := by
    simp only [grid33]
    apply rectangle_grid_subset <;> simp only [hm₀_def, hm₁_def]
    · rw [abs_le] at h0; omega
    · rw [abs_le] at h1; omega
    · rw [abs_le] at h0; omega
    · rw [abs_le] at h1; omega
  obtain ⟨R, hR⟩ := rectagon_rectangle_grid_sq m₁
  have hcc' : f x' ∉ ⋃₀ (curveCells (R.edges) : Set (Set E2)) := by
    rw [hR]
    exact fun h => hcc (curveCells_sUnion_mono
      (hE'_sub.trans (by rfl : grid33 m₀ ⊆ grid33 m₀)) h)
  have hRsq := rectangle_grid_sq m₁
  have hh_in : hEdge m₁ ∈ R.edges := by
    rw [hR, hRsq]; exact Finset.mem_insert_self _ _
  have hv_in : vEdge m₁ ∈ R.edges := by
    rw [hR, hRsq]
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert_self _ _))))
  have hfx_squ : f x' ∈ squ m₁ := by
    simp only [squ, Set.mem_setOf_eq, hm₁_def, gt_iff_lt]
    refine ⟨?_, Int.lt_floor_add_one _, ?_, Int.lt_floor_add_one _⟩
    · by_contra hle; push Not at hle
      have heq0 : (f x') 0 = ↑⌊(f x') 0⌋ := le_antisymm hle (Int.floor_le _)
      exact hcc' <| by
        by_cases heq1 : (f x') 1 = ↑⌊(f x') 1⌋
        · exact Set.mem_sUnion.mpr ⟨{pointI m₁},
            (curveCells_cls R.toSegment m₁).mpr
              ⟨hEdge m₁, hh_in,
               (pointI_mem_closure_hEdge m₁ m₁).mpr ⟨rfl, Or.inl rfl⟩⟩,
            show f x' ∈ ({pointI m₁} : Set E2) from by
              rw [Set.mem_singleton_iff]; ext i; fin_cases i
              · exact heq0.trans (pointI_coord_fst m₁).symm
              · exact heq1.trans (pointI_coord_snd m₁).symm⟩
        · exact Set.mem_sUnion.mpr ⟨vEdge m₁,
            (curveCells_edge R.edges _ (Or.inr ⟨m₁, rfl⟩)).mpr hv_in,
            show f x' ∈ vEdge m₁ from ⟨heq0, lt_of_le_of_ne (Int.floor_le _)
              (Ne.symm heq1), Int.lt_floor_add_one _⟩⟩
    · by_contra hle; push Not at hle
      have heq1 : (f x') 1 = ↑⌊(f x') 1⌋ := le_antisymm hle (Int.floor_le _)
      exact hcc' <| by
        by_cases heq0 : (f x') 0 = ↑⌊(f x') 0⌋
        · exact Set.mem_sUnion.mpr ⟨{pointI m₁},
            (curveCells_cls R.toSegment m₁).mpr
              ⟨hEdge m₁, hh_in,
               (pointI_mem_closure_hEdge m₁ m₁).mpr ⟨rfl, Or.inl rfl⟩⟩,
            show f x' ∈ ({pointI m₁} : Set E2) from by
              rw [Set.mem_singleton_iff]; ext i; fin_cases i
              · exact heq0.trans (pointI_coord_fst m₁).symm
              · exact heq1.trans (pointI_coord_snd m₁).symm⟩
        · exact Set.mem_sUnion.mpr ⟨hEdge m₁,
            (curveCells_edge R.edges _ (Or.inl ⟨m₁, rfl⟩)).mpr hh_in,
            show f x' ∈ hEdge m₁ from ⟨lt_of_le_of_ne (Int.floor_le _)
              (Ne.symm heq0), Int.lt_floor_add_one _, heq1⟩⟩
  have hnum : numLower R.edges m₁ = 1 := by
    change numLower R.edges (m₁.1, m₁.2) = 1
    rw [numLower_step, if_pos (show hEdge (m₁.1, m₁.2) ∈ R.edges from hh_in)]
    suffices numLower R.edges (m₁.1, m₁.2 - 1) = 0 by omega
    unfold numLower; classical
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he; push Not; intro k hk hek
    rw [hek, hR, hRsq] at he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h | h
    · have := (hEdge_inj _ _).mp h; simp only [Prod.ext_iff] at this; omega
    · have heq := (hEdge_inj _ _).mp h
      unfold up at heq
      have hk2 : k = m₁.2 + 1 := (Prod.mk.inj heq).2
      linarith
    · exact absurd h (hEdge_ne_vEdge _ _)
    · exact absurd h (hEdge_ne_vEdge _ _)
  have hpar : parCell false R.edges (squ m₁) :=
    (parCell_squ R.toSegment m₁ false).mpr
      (by change false = decide (Even (numLower R.edges m₁)); rw [hnum]; decide)
  have hbnd_R : BoundedSet R.edges (f x') := by
    have hmem : f x' ∈ ⋃₀ {C | parCell false R.edges C} :=
      Set.mem_sUnion.mpr ⟨squ m₁, hpar, hfx_squ⟩
    rwa [odd_bounded R, Set.mem_setOf_eq] at hmem
  have hbnd_E := bounded_avoidance_subset R.edges (grid33 m₀) (f x')
    hbnd_R (hR ▸ hE'_sub) (grid33_edge m₀) (conn2_rectagon R) hcc
  exact bounded_unbounded_disj (grid f N) (f x')
    ⟨bounded_avoidance_subset (grid33 m₀) (grid f N) (f x') hbnd_E hE_sub
      (grid_edge f N) (grid33_conn2 m₀)
      (unbounded_set_curve_cell_empty (grid f N) (grid f N) _ hunb
        (fun a ha => ha)), hunb⟩

/-! ## §AA.6 Grid33 properties -/

/-- HOL Light: `grid33_h` (line 52087).
h_edge m ∈ grid33 m. -/
theorem grid33_h (m : ℤ × ℤ) : hEdge m ∈ grid33 m := by
  simp only [grid33, rectangle_grid]
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨m, Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
     Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩, rfl⟩

/-- HOL Light: `curve_cell_grid_unions` (line 52099).
curveCells distributes over grid construction. -/
theorem curveCells_grid_eq (f : ℝ → E2) (N : ℕ) :
    (curveCells (grid f N) : Set (Set E2)) =
      ⋃ i ∈ Finset.range (N + 1),
        (curveCells (grid33 (⌊f (↑i / ↑N) 0⌋, ⌊f (↑i / ↑N) 1⌋)) : Set (Set E2)) := by
  simp only [grid]
  exact thread_finite_union curveCells _ _ curveCells_union curveCells_empty

/-- HOL Light: `curve_cell_finite_union` (line 52119).
curveCells distributes over finite union. -/
theorem curveCells_biUnion {ι : Type*} (S : Finset ι)
    (G : ι → Finset (Set E2)) :
    (curveCells (S.biUnion G) : Set (Set E2)) = ⋃ i ∈ S, (curveCells (G i) : Set (Set E2)) := by
  classical exact thread_finite_union curveCells S G curveCells_union curveCells_empty

/-- HOL Light: `grid33_unions` (line 52130).
grid33 is the union of h-edges and v-edges in a range. -/
theorem grid33_unions (p : ℤ × ℤ) :
    ↑(grid33 p : Finset (Set E2)) =
      (hEdge '' {m | p.1 - 1 ≤ m.1 ∧ m.1 ≤ p.1 + 1 ∧
                      p.2 - 1 ≤ m.2 ∧ m.2 ≤ p.2 + 2}) ∪
      (vEdge '' {m | p.1 - 1 ≤ m.1 ∧ m.1 ≤ p.1 + 2 ∧
                      p.2 - 1 ≤ m.2 ∧ m.2 ≤ p.2 + 1}) := by
  ext e
  simp only [grid33, rectangle_grid, Finset.coe_union, Finset.coe_image]
  constructor
  · rintro (⟨⟨a, b⟩, ham, rfl⟩ | ⟨⟨a, b⟩, ham, rfl⟩)
    · left; refine ⟨⟨a, b⟩, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at ham
      exact ⟨by omega, by omega, by omega, by omega⟩
    · right; refine ⟨⟨a, b⟩, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at ham
      exact ⟨by omega, by omega, by omega, by omega⟩
  · rintro (⟨⟨a, b⟩, ⟨h1, h2, h3, h4⟩, rfl⟩ | ⟨⟨a, b⟩, ⟨h1, h2, h3, h4⟩, rfl⟩)
    · left; refine ⟨⟨a, b⟩, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · right; refine ⟨⟨a, b⟩, ?_, rfl⟩
      rw [Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-- HOL Light: `d_euclid_bound2` (line 52307).
If both coordinate differences are ≤ eps, then dist ≤ √2 · eps. -/
theorem dist_coord_bound {x y : E2} {eps : ℝ}
    (h0 : |x 0 - y 0| ≤ eps) (h1 : |x 1 - y 1| ≤ eps) :
    dist x y ≤ Real.sqrt 2 * eps := by
  have heps : 0 ≤ eps := le_trans (abs_nonneg _) h0
  rw [EuclideanSpace.dist_eq]
  calc Real.sqrt (∑ i : Fin 2, dist (x.ofLp i) (y.ofLp i) ^ 2)
      ≤ Real.sqrt (2 * eps ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Fin.sum_univ_two, Real.dist_eq]
        have h0' : |x 0 - y 0| ^ 2 ≤ eps ^ 2 :=
          sq_le_sq' (by linarith [abs_nonneg (x 0 - y 0)]) h0
        have h1' : |x 1 - y 1| ^ 2 ≤ eps ^ 2 :=
          sq_le_sq' (by linarith [abs_nonneg (x 1 - y 1)]) h1
        linarith
    _ = Real.sqrt 2 * eps := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq heps]

/-- HOL Light: `grid33_radius` (line 52325).
Points in curveCells(grid33 m) are within distance 4 of m's center. -/
theorem grid33_radius {x : E2} {y : E2}
    (_hx : True) -- euclid 2 x is trivial in Lean
    (hy : y ∈ ⋃₀ (curveCells (grid33 (⌊x 0⌋, ⌊x 1⌋)) : Set (Set E2))) :
    dist x y < 4 := by
  have hf0 : (↑⌊x 0⌋ : ℝ) ≤ x 0 := Int.floor_le _
  have hl0 : x 0 < ↑⌊x 0⌋ + 1 := Int.lt_floor_add_one _
  have hf1 : (↑⌊x 1⌋ : ℝ) ≤ x 1 := Int.floor_le _
  have hl1 : x 1 < ↑⌊x 1⌋ + 1 := Int.lt_floor_add_one _
  rw [← curve_closure_finset _ (grid33_edge (⌊x 0⌋, ⌊x 1⌋))] at hy
  suffices hsub : ⋃₀ ↑(grid33 (⌊x 0⌋, ⌊x 1⌋) : Finset (Set E2)) ⊆ closedBall x 3 by
    have hym := closure_minimal hsub Metric.isClosed_closedBall hy
    rw [mem_closedBall, dist_comm] at hym; linarith
  intro z hz
  rw [Set.mem_sUnion] at hz
  obtain ⟨e, he_mem, hz_e⟩ := hz
  rw [Finset.mem_coe] at he_mem
  simp only [grid33, rectangle_grid, Finset.mem_union, Finset.mem_image,
    Finset.mem_product, Finset.mem_Icc] at he_mem
  rw [mem_closedBall, dist_comm]
  rcases he_mem with ⟨⟨a, b⟩, ⟨⟨ha1, ha2⟩, hb1, hb2⟩, rfl⟩ |
      ⟨⟨a, b⟩, ⟨⟨ha1, ha2⟩, hb1, hb2⟩, rfl⟩
  · simp only [hEdge, Set.mem_setOf_eq] at hz_e
    obtain ⟨hza0, hza1, hzb⟩ := hz_e
    have ha1r : ↑⌊x 0⌋ - 1 ≤ (↑a : ℝ) := by exact_mod_cast ha1
    have ha2r : (↑a : ℝ) ≤ ↑⌊x 0⌋ + 1 := by exact_mod_cast (show a ≤ ⌊x 0⌋ + 1 by omega)
    have hb1r : ↑⌊x 1⌋ - 1 ≤ (↑b : ℝ) := by exact_mod_cast hb1
    have hb2r : (↑b : ℝ) ≤ ↑⌊x 1⌋ + 2 := by exact_mod_cast hb2
    calc dist x z ≤ Real.sqrt 2 * 2 :=
          dist_coord_bound (by rw [abs_le]; constructor <;> linarith)
            (by rw [abs_le]; constructor <;> linarith)
      _ ≤ 3 := by nlinarith [Real.sq_sqrt (show (2 : ℝ) ≥ 0 from by norm_num)]
  · simp only [vEdge, Set.mem_setOf_eq] at hz_e
    obtain ⟨hza, hzb0, hzb1⟩ := hz_e
    have ha1r : ↑⌊x 0⌋ - 1 ≤ (↑a : ℝ) := by exact_mod_cast ha1
    have ha2r : (↑a : ℝ) ≤ ↑⌊x 0⌋ + 2 := by exact_mod_cast ha2
    have hb1r : ↑⌊x 1⌋ - 1 ≤ (↑b : ℝ) := by exact_mod_cast hb1
    have hb2r : (↑b : ℝ) ≤ ↑⌊x 1⌋ + 1 := by exact_mod_cast (show b ≤ ⌊x 1⌋ + 1 by omega)
    calc dist x z ≤ Real.sqrt 2 * 2 :=
          dist_coord_bound (by rw [abs_le]; constructor <;> linarith)
            (by rw [abs_le]; constructor <;> linarith)
      _ ≤ 3 := by nlinarith [Real.sq_sqrt (show (2 : ℝ) ≥ 0 from by norm_num)]

/-! ## §AA.7 Main grid properties theorem -/

/-- HOL Light: `simple_arc_grid_properties` (line 52402).
For a simple arc end C from a to b, there exists an edge set E with:
conn2, C avoids the unbounded set, E contains h-edges at a and b,
and every point in curveCells(E) is within distance 4 of some point of C. -/
theorem simple_arc_grid_properties {C : Set E2'} {a b : E2'}
    (hC : IsSimpleArcEnd C a b) :
    ∃ E : Finset (Set E2),
      (∀ e ∈ E, isEdge e) ∧
      Disjoint C {x | UnboundedSet E x} ∧
      conn2 E ∧
      hEdge (⌊a 0⌋, ⌊a 1⌋) ∈ E ∧
      hEdge (⌊b 0⌋, ⌊b 1⌋) ∈ E ∧
      (∀ y ∈ ⋃₀ (curveCells E : Set (Set E2)),
        ∃ x ∈ C, dist x y < 4) := by
  obtain ⟨f, rfl, hcont, hinj, hf0, hf1⟩ := hC
  -- uniform continuity gives δ for ε = 1
  have huc := simple_arc_uniformly_continuous f hcont hinj
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδpos, hδ⟩ := huc 1 one_pos
  -- N from Archimedean: 1/N < δ
  obtain ⟨N, hN_arch⟩ := exists_nat_gt (1 / δ)
  have hNpos : 0 < N := by
    by_contra h; simp only [not_lt, Nat.le_zero] at h
    subst h; simp at hN_arch; linarith [div_pos one_pos hδpos]
  -- M from grid_image_bounded_ver2
  obtain ⟨M, hMpos, hM⟩ := grid_image_bounded_ver2 f hcont hinj
  -- n = N + M
  set n := N + M
  have hnpos : 0 < n := by omega
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hnpos
  -- consecutive grid distances < 1
  have hdist : ∀ i, i < n → dist (f (↑i / ↑n)) (f (↑(i + 1) / ↑n)) < 1 := by
    intro i hi
    have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hNpos
    have h_icc1 : (↑i : ℝ) / ↑n ∈ Set.Icc 0 1 :=
      ⟨div_nonneg (Nat.cast_nonneg' i) hn_pos.le,
       (div_le_one hn_pos).mpr (by exact_mod_cast hi.le)⟩
    have h_icc2 : (↑(i + 1) : ℝ) / ↑n ∈ Set.Icc 0 1 :=
      ⟨div_nonneg (by positivity) hn_pos.le,
       (div_le_one hn_pos).mpr (by push_cast; exact_mod_cast hi)⟩
    apply hδ _ h_icc1 _ h_icc2
    have h_diff : (↑i : ℝ) / ↑n - ↑(i + 1) / ↑n = -(1 / ↑n) := by
      field_simp; push_cast; ring
    rw [Real.dist_eq, h_diff, abs_neg, abs_of_pos (div_pos one_pos hn_pos),
      div_lt_iff₀ hn_pos]
    have h1 : 1 < ↑N * δ := by rwa [div_lt_iff₀ hδpos] at hN_arch
    have h2 : (↑N : ℝ) ≤ ↑n := by exact_mod_cast (show N ≤ n by omega)
    nlinarith
  -- E = grid f n
  refine ⟨grid f n, grid_edge f n, hM n (by omega), grid_conn2 f n hdist, ?_, ?_, ?_⟩
  -- hEdge at a = f 0
  · rw [← hf0]; simp only [grid, Finset.mem_biUnion]
    refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    simp only [Nat.cast_zero, zero_div]; exact grid33_h _
  -- hEdge at b = f 1
  · rw [← hf1]; simp only [grid, Finset.mem_biUnion]
    refine ⟨n, Finset.mem_range.mpr (by omega), ?_⟩
    have hnn : (↑n : ℝ) / ↑n = 1 := div_self (ne_of_gt hn_pos)
    simp only [hnn]; exact grid33_h _
  -- proximity of curveCells to C
  · intro y hy
    rw [curveCells_grid_eq] at hy
    simp only [Set.mem_sUnion, Set.mem_iUnion, exists_prop, Finset.mem_range] at hy
    obtain ⟨s, ⟨i, hi, hs⟩, hys⟩ := hy
    refine ⟨f (↑i / ↑n), ?_, ?_⟩
    · exact Set.mem_image_of_mem _ ⟨div_nonneg (Nat.cast_nonneg' i) hn_pos.le,
        (div_le_one hn_pos).mpr (Nat.cast_le.mpr (by omega))⟩
    · exact grid33_radius trivial (Set.mem_sUnion.mpr ⟨s, hs, hys⟩)

/-! ## §AA.8 Unbounded set machinery -/

/-- HOL Light: `unbounded_set_lemma` (line 52527).
Characterize unbounded set via arcs to far-away points on the x-axis. -/
theorem unboundedSet_lemma (E : Finset (Set E2))
    (_hfin : True) -- Finset is finite by definition in Lean
    (hedge : ∀ e ∈ E, isEdge e) (p : E2) :
    UnboundedSet E p ↔
      ∃ r : ℝ, ∀ s : ℝ, r ≤ s →
        ∃ C : Set E2', IsSimpleArcEnd C p (point (s, 0)) ∧
          C ∩ ⋃₀ (curveCells E : Set (Set E2)) = ∅ := by
  simp only [UnboundedSet, Unbounded]
  constructor
  · -- Forward: component membership → arc existence
    intro ⟨r, hr⟩
    refine ⟨max r (p 0 + 1), fun s hs => ?_⟩
    have hrs : r ≤ s := le_trans (le_max_left _ _) hs
    have hne : p ≠ point (s, 0) := by
      intro heq
      have : p 0 = point (s, 0) 0 := by rw [heq]
      simp only [point_coord_zero] at this; linarith [le_max_right r (p 0 + 1)]
    exact (component_simple_arc E hedge p (point (s, 0)) hne).mp (hr s hrs)
  · -- Backward: arc existence → component membership
    intro ⟨r, hr⟩
    refine ⟨max r (p 0 + 1), fun s hs => ?_⟩
    have hrs : r ≤ s := le_trans (le_max_left _ _) hs
    have hne : p ≠ point (s, 0) := by
      intro heq
      have : p 0 = point (s, 0) 0 := by rw [heq]
      simp only [point_coord_zero] at this; linarith [le_max_right r (p 0 + 1)]
    exact (component_simple_arc E hedge p (point (s, 0)) hne).mpr (hr s hrs)

/-- HOL Light: `simple_arc_end_subset_trans_lemma` (line 52582). -/
theorem isSimpleArcEnd_subset_trans_lemma {C : Set E2'} {a b c : E2'}
    (hC : IsSimpleArcEnd C a b) (hcC : c ∈ C) (hca : c ≠ a) :
    ∃ C' : Set E2', C' ⊆ C ∧ IsSimpleArcEnd C' a c := by
  by_cases hbc : b = c
  · exact ⟨C, Set.Subset.refl _, hbc ▸ hC⟩
  · obtain ⟨C₁, C₂, hC₁, _, _, hunion⟩ := isSimpleArcEnd_cut hC hcC hca (Ne.symm hbc)
    exact ⟨C₁, hunion ▸ Set.subset_union_left, hC₁⟩

/-- HOL Light: `simple_arc_end_subset_trans` (line 52599).
Given arcs C from a to b, C' from b to c with a ≠ c,
there exists an arc from a to c inside C ∪ C'. -/
theorem isSimpleArcEnd_subset_trans {C C' : Set E2'} {a b c : E2'}
    (hC : IsSimpleArcEnd C a b) (hC' : IsSimpleArcEnd C' b c)
    (hac : a ≠ c) :
    ∃ U : Set E2', IsSimpleArcEnd U a c ∧ U ⊆ C ∪ C' := by
  by_cases haC' : a ∈ C'
  · obtain ⟨D, hDsub, hD⟩ := isSimpleArcEnd_subset_trans_lemma
      (isSimpleArcEnd_symm hC') haC' hac
    exact ⟨D, isSimpleArcEnd_symm hD, hDsub.trans Set.subset_union_right⟩
  · have hdisjoint : C ∩ {a} ∩ C' = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨⟨_, rfl⟩, hxC'⟩; exact haC' hxC'
    have hCK : (C ∩ {a}).Nonempty :=
      ⟨a, isSimpleArcEnd_mem_left hC, Set.mem_singleton a⟩
    have hCK' : (C ∩ C').Nonempty :=
      ⟨b, isSimpleArcEnd_mem_right hC, isSimpleArcEnd_mem_left hC'⟩
    obtain ⟨D, v, v', hDsub, hD, hvD, hv'D⟩ :=
      isSimpleArcEnd_restriction (isSimpleArcEnd_isSimpleArc hC)
        isClosed_singleton (isSimpleArcEnd_isClosed hC')
        hdisjoint hCK hCK'
    have hva : v = a := by
      have hv : v ∈ ({v} : Set E2') := Set.mem_singleton v
      rw [← hvD] at hv; exact hv.2
    subst hva
    by_cases hv'c : v' = c
    · subst hv'c
      exact ⟨D, hD, hDsub.trans Set.subset_union_left⟩
    · have hv'C' : v' ∈ C' := by
        have hv' : v' ∈ ({v'} : Set E2') := Set.mem_singleton v'
        rw [← hv'D] at hv'; exact hv'.2
      obtain ⟨D', hD'sub, hD'⟩ :=
        isSimpleArcEnd_subset_trans_lemma
          (isSimpleArcEnd_symm hC') hv'C' hv'c
      have hinter : D ∩ D' = {v'} := by
        apply Set.Subset.antisymm
        · calc D ∩ D' ⊆ D ∩ C' :=
              Set.inter_subset_inter_right D hD'sub
            _ = {v'} := hv'D
        · exact Set.singleton_subset_iff.mpr
            ⟨isSimpleArcEnd_mem_right hD,
             isSimpleArcEnd_mem_right hD'⟩
      exact ⟨D ∪ D',
        isSimpleArcEnd_trans hD
          (isSimpleArcEnd_symm hD') hinter,
        Set.union_subset_union hDsub hD'sub⟩

/-- HOL Light: `unbounded_set_trans_lemma` (line 52669).
Transfer unboundedness along an arc that avoids a closed ball. -/
theorem unboundedSet_trans_lemma {E : Finset (Set E2)} {p q x : E2} {r : ℝ}
    (hedge : ∀ e ∈ E, isEdge e)
    (hunbnd : UnboundedSet E p)
    (hball : ⋃₀ (E : Set (Set E2)) ⊆ Metric.closedBall x r)
    (hC : ∃ C : Set E2', IsSimpleArcEnd C p q ∧
      C ∩ Metric.closedBall x r = ∅) :
    UnboundedSet E q := by
  obtain ⟨C, hCarc, hCball⟩ := hC
  -- Step 1: curveCells E ⊆ closedBall x r (via closure)
  have hcurve : ⋃₀ (curveCells E : Set (Set E2)) ⊆ Metric.closedBall x r := by
    rw [← curve_closure_finset E hedge]
    exact closure_minimal hball Metric.isClosed_closedBall
  -- Step 2: C avoids curveCells E
  have hCcc : C ∩ ⋃₀ (curveCells E : Set (Set E2)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z ⟨hzC, hzcc⟩
    have hzball : z ∈ Metric.closedBall x r := hcurve hzcc
    exact Set.eq_empty_iff_forall_notMem.mp hCball z ⟨hzC, hzball⟩
  -- Step 3: Use unboundedSet_lemma on p
  rw [unboundedSet_lemma E trivial hedge] at hunbnd
  obtain ⟨r', hr'⟩ := hunbnd
  -- Step 4: Show UnboundedSet E q
  rw [unboundedSet_lemma E trivial hedge]
  refine ⟨max r' (q 0 + 1), fun s hs => ?_⟩
  have hrs : r' ≤ s := le_trans (le_max_left _ _) hs
  have hqne : q ≠ point (s, 0) := by
    intro heq
    have : q 0 = point (s, 0) 0 := by rw [heq]
    simp only [point_coord_zero] at this; linarith [le_max_right r' (q 0 + 1)]
  obtain ⟨C', hC'arc, hC'cc⟩ := hr' s hrs
  -- Compose arcs: q →[C⁻¹] p →[C'] point(s,0)
  obtain ⟨U, hUarc, hUsub⟩ :=
    isSimpleArcEnd_subset_trans (isSimpleArcEnd_symm hCarc) hC'arc hqne
  exact ⟨U, hUarc, by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z ⟨hzU, hzcc⟩
    rcases hUsub hzU with hzC | hzC'
    · exact Set.eq_empty_iff_forall_notMem.mp hCcc z ⟨hzC, hzcc⟩
    · exact Set.eq_empty_iff_forall_notMem.mp hC'cc z ⟨hzC', hzcc⟩⟩

/-- HOL Light: `unbounded_set_empty` (line 52736).
The unbounded set of the empty edge set is all of E2. -/
theorem unboundedSet_empty : {x : E2 | UnboundedSet ∅ x} = Set.univ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  change Unbounded (connectedComponentIn (complementCurve ∅) x)
  have h1 : complementCurve (∅ : Finset (Set E2)) = Set.univ := by
    simp [complementCurve, curveCells_empty, Set.sUnion_empty]
  rw [h1, connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]
  rw [Unbounded]
  exact ⟨0, fun s _ => Set.mem_univ _⟩

/-- HOL Light: `polar_curve_lemma` (line 52813).
Circular arc from x + (r,0) to x + r·cis(θ) at constant distance r from x. -/
theorem polar_curve_lemma {x : E2'} {theta r : ℝ}
    (htheta_pos : 0 < theta) (htheta_lt : theta < 2 * Real.pi) (hr : 0 < r) :
    ∃ C : Set E2', IsSimpleArcEnd C (x + point (r, 0))
        (x + r • cis theta) ∧
      ∀ y ∈ C, dist x y = r := by
  -- Parametric curve G(t) = x + r • cis(θ * t) for t ∈ [0,1]
  set G : ℝ → E2' := fun t => x + r • cis (theta * t) with hG_def
  set C := G '' Set.Icc 0 1 with hC_def
  have hG0 : G 0 = x + point (r, 0) := by
    simp [hG_def, cis_zero, point_smul]
  have hG1 : G 1 = x + r • cis theta := by simp [hG_def]
  refine ⟨C, ⟨G, rfl, ?_, ?_, hG0, hG1⟩, ?_⟩
  · -- Continuity
    exact continuous_polar continuous_const (continuous_const.mul continuous_id')
  · -- Injectivity on [0,1]
    intro t₁ ht₁ t₂ ht₂ heq
    simp only [hG_def] at heq
    have heq' : r • cis (theta * t₁) = r • cis (theta * t₂) := by
      have := congr_arg (· - x) heq
      simpa [add_sub_cancel_left] using this
    have ht₁_range : theta * t₁ ∈ Set.Ico 0 (2 * Real.pi) := by
      constructor
      · exact mul_nonneg (le_of_lt htheta_pos) ht₁.1
      · calc theta * t₁ ≤ theta * 1 := by nlinarith [ht₁.2]
          _ = theta := mul_one _
          _ < 2 * Real.pi := htheta_lt
    have ht₂_range : theta * t₂ ∈ Set.Ico 0 (2 * Real.pi) := by
      constructor
      · exact mul_nonneg (le_of_lt htheta_pos) ht₂.1
      · calc theta * t₂ ≤ theta * 1 := by nlinarith [ht₂.2]
          _ = theta := mul_one _
          _ < 2 * Real.pi := htheta_lt
    rcases polar_inj (le_of_lt hr) (le_of_lt hr) ht₁_range ht₂_range heq' with
      ⟨h, _⟩ | ⟨_, h⟩
    · linarith
    · exact mul_left_cancel₀ (ne_of_gt htheta_pos) h
  · -- Distance property
    intro y hy
    obtain ⟨t, _, rfl⟩ := hy
    simp only [hG_def]
    have hdist : dist x (x + r • cis (theta * t)) = ‖r • cis (theta * t)‖ := by
      rw [dist_comm, dist_eq_norm, add_sub_cancel_left]
    rw [hdist, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have : ‖cis (theta * t)‖ = 1 := by
      unfold cis; rw [EuclideanSpace.norm_eq]
      norm_num [Fin.sum_univ_two, point, sq_abs]
    rw [this, mul_one]

/-- HOL Light: `unbounded_set_ball` (line 52899).
Points outside a closed ball containing all edges are unbounded. -/
theorem unboundedSet_ball {E : Finset (Set E2)} {x : E2} {r : ℝ} {p : E2}
    (hr : 0 < r) (hedge : ∀ e ∈ E, isEdge e)
    (hball : ⋃₀ (E : Set (Set E2)) ⊆ Metric.closedBall x r)
    (hp : p ∉ Metric.closedBall x r) :
    UnboundedSet E p := by
  -- Coordinate projection lower bound: |a 0 - b 0| ≤ dist a b
  have coord0_le_dist : ∀ (a b : E2), |a 0 - b 0| ≤ dist a b := by
    intro a b; rw [EuclideanSpace.dist_eq]
    calc |a 0 - b 0|
        = Real.sqrt ((a 0 - b 0) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (∑ i : Fin 2, dist (a.ofLp i) (b.ofLp i) ^ 2) := by
          apply Real.sqrt_le_sqrt; rw [Fin.sum_univ_two]
          simp only [Real.dist_eq, sq_abs]
          linarith [sq_nonneg (a 1 - b 1)]
  -- r < dist x p
  have hdist : r < dist x p := by
    have h : ¬ dist p x ≤ r := mt Metric.mem_closedBall.mpr hp
    rw [not_le] at h; linarith [dist_comm x p]
  -- Polar decomposition: p - x = R • cis θ
  obtain ⟨R, θ, ⟨hθ_lo, hθ_hi⟩, hR0, hpx⟩ := polar_exist (p - x)
  have hp_eq : p = x + R • cis θ := by
    rw [sub_eq_iff_eq_add] at hpx; rwa [add_comm] at hpx
  have hR_gt : r < R := by
    have : dist x p = R := by
      rw [hp_eq, dist_comm, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg hR0]
      have : ‖cis θ‖ = 1 := by
        unfold cis; rw [EuclideanSpace.norm_eq]
        norm_num [Fin.sum_univ_two, point, sq_abs]
      rw [this, mul_one]
    linarith
  have hR_pos : 0 < R := lt_trans hr hR_gt
  -- Far x-axis points are unbounded
  obtain ⟨r', hr'⟩ := unboundedSet_x_axis E hedge
  set s := max r' (x 0 + R + 1) with hs_def
  have hs_gt : x 0 + R < s := by linarith [le_max_right r' (x 0 + R + 1)]
  have hunbnd_s := hr' s (le_max_left _ _)
  -- Helper: segment from point(s,0) to point(x 0 + R, 0) avoids closedBall x r
  have hseg_h_avoids : segment ℝ (point (s, 0)) (point (x 0 + R, 0)) ∩
      Metric.closedBall x r = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]; rintro z ⟨hmem, hzball⟩
    obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_param.mp hmem
    rw [Metric.mem_closedBall, dist_comm] at hzball
    have hz0 : (t • point (s, 0) + (1 - t) • point (x 0 + R, 0)) 0 =
        t * s + (1 - t) * (x 0 + R) := by simp [point_smul, point_add, point_coord_zero]
    have hu_ge : x 0 + R ≤ t * s + (1 - t) * (x 0 + R) := by nlinarith [hs_gt.le]
    have : R ≤ |x 0 - (t * s + (1 - t) * (x 0 + R))| := by
      rw [abs_of_nonpos (by linarith)]; linarith
    have h_coord := coord0_le_dist x (t • point (s, 0) + (1 - t) • point (x 0 + R, 0))
    rw [hz0] at h_coord
    linarith
  -- Step 1: point(x₀ + R, 0) is unbounded
  have hne_h : point (s, (0 : ℝ)) ≠ point (x 0 + R, (0 : ℝ)) := by
    intro h
    have : (point (s, (0 : ℝ))) 0 = (point (x 0 + R, (0 : ℝ))) 0 := congrArg (· 0) h
    simp [point_coord_zero] at this; linarith
  have hunbnd_xr0 : UnboundedSet E (point (x 0 + R, 0)) :=
    unboundedSet_trans_lemma hedge hunbnd_s hball
      ⟨_, segment_isSimpleArcEnd hne_h, hseg_h_avoids⟩
  -- Step 2: x + point(R, 0) is unbounded
  have hxR_eq : x + point (R, 0) = point (x 0 + R, x 1) := by
    rw [point_surjective x]; simp [point_add]
  have hunbnd_xR : UnboundedSet E (x + point (R, 0)) := by
    rw [hxR_eq]
    by_cases hx1 : x 1 = 0
    · rw [hx1]; exact hunbnd_xr0
    · apply unboundedSet_trans_lemma hedge hunbnd_xr0 hball
      have hne_v : point (x 0 + R, (0 : ℝ)) ≠ point (x 0 + R, x 1) := by
        intro h; apply hx1
        have : (point (x 0 + R, (0 : ℝ))) 1 = (point (x 0 + R, x 1)) 1 := congrArg (· 1) h
        simp only [point_coord_one] at this; linarith
      refine ⟨_, segment_isSimpleArcEnd hne_v, ?_⟩
      rw [Set.eq_empty_iff_forall_notMem]; rintro z ⟨hmem_v, hzball⟩
      obtain ⟨t, ht0, ht1, rfl⟩ := mem_segment_iff_param.mp hmem_v
      rw [Metric.mem_closedBall, dist_comm] at hzball
      have hz0 : (t • point (x 0 + R, 0) + (1 - t) • point (x 0 + R, x 1)) 0 =
          x 0 + R := by simp [point_smul, point_add, point_coord_zero]; ring
      have : R ≤ dist x (t • point (x 0 + R, 0) + (1 - t) • point (x 0 + R, x 1)) := by
        have h0 := coord0_le_dist x (t • point (x 0 + R, 0) + (1 - t) • point (x 0 + R, x 1))
        rw [hz0] at h0; rw [show x 0 - (x 0 + R) = -R from by ring] at h0
        rwa [abs_neg, abs_of_nonneg (le_of_lt hR_pos)] at h0
      linarith
  -- Step 3: p is unbounded
  by_cases hθ : θ = 0
  · -- θ = 0: p = x + R • cis 0 = x + point(R, 0)
    rw [hp_eq, hθ, cis_zero, point_smul, mul_one, mul_zero]; exact hunbnd_xR
  · -- θ > 0: circular arc from x + point(R, 0) to p
    have hθ_pos : 0 < θ := lt_of_le_of_ne hθ_lo (Ne.symm hθ)
    obtain ⟨C, hCarc, hCdist⟩ := polar_curve_lemma hθ_pos hθ_hi hR_pos
    rw [hp_eq]
    apply unboundedSet_trans_lemma hedge hunbnd_xR hball
    refine ⟨C, hCarc, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]; rintro z ⟨hzC, hzball⟩
    rw [Metric.mem_closedBall, dist_comm] at hzball
    have := hCdist z hzC -- dist x z = R
    linarith

/-- HOL Light: `unbounded_connect` (line 53065).
Two unbounded points can be connected by an arc in the unbounded set. -/
theorem unbounded_connect {E : Finset (Set E2)} {p q : E2}
    (hedge : ∀ e ∈ E, isEdge e) (hpq : p ≠ q)
    (hp : UnboundedSet E p) (hq : UnboundedSet E q) :
    ∃ C : Set E2', C ⊆ {x | UnboundedSet E x} ∧
      IsSimpleArcEnd C p q := by
  -- Use unboundedSet_lemma to get arcs from p and q
  rw [unboundedSet_lemma E trivial hedge] at hp hq
  obtain ⟨rp, hrp⟩ := hp; obtain ⟨rq, hrq⟩ := hq
  set r := max rp rq with hr_def
  obtain ⟨Cp, hCparc, hCpcc⟩ := hrp r (le_max_left _ _)
  obtain ⟨Cq, hCqarc, hCqcc⟩ := hrq r (le_max_right _ _)
  -- Compose: p →[Cp] point(r,0) →[Cq⁻¹] q
  obtain ⟨U, hUarc, hUsub⟩ :=
    isSimpleArcEnd_subset_trans hCparc (isSimpleArcEnd_symm hCqarc) hpq
  refine ⟨U, ?_, hUarc⟩
  -- U ⊆ C_p ∪ C_q, both avoid curveCells, so U avoids curveCells
  have hUcc : U ∩ ⋃₀ (curveCells E : Set (Set E2)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z ⟨hzU, hzcc⟩
    rcases hUsub hzU with hzCp | hzCq
    · exact Set.eq_empty_iff_forall_notMem.mp hCpcc z ⟨hzCp, hzcc⟩
    · exact Set.eq_empty_iff_forall_notMem.mp hCqcc z ⟨hzCq, hzcc⟩
  -- U ⊆ componentOf p (via rectagon_curve)
  have hU_comp := rectagon_curve E hedge U p q hUarc hUcc
  intro z hz
  simp only [Set.mem_setOf_eq]
  exact unboundedSet_comp_elt E hedge
    ((unboundedSet_lemma E trivial hedge p).mpr ⟨rp, hrp⟩) (hU_comp hz)

/-! ## §AA.9 Complement of simple arc is connected -/

/-- HOL Light: `simple_arc_conn_complement` (line 53105).
The complement of a simple arc in E2 is path-connected:
for any two points not on the arc, there is an arc connecting them
that avoids the original arc. -/
theorem simple_arc_conn_complement {C : Set E2'} {p q : E2'}
    (hC : IsSimpleArc C) (hp : p ∉ C) (hq : q ∉ C) (hpq : p ≠ q) :
    ∃ A : Set E2', IsSimpleArcEnd A p q ∧ Disjoint C A := by
  -- By contradiction: assume every arc from p to q meets C
  by_contra hcontra; push Not at hcontra
  have hinter : ∀ A : Set E2', IsSimpleArcEnd A p q → (C ∩ A).Nonempty := by
    intro A hA; by_contra h
    exact hcontra A hA (Set.disjoint_left.mpr fun x hxC hxA => h ⟨x, hxC, hxA⟩)
  -- Scale to get d, d' ≥ 1
  obtain ⟨C', p', q', d, N, B, a, d', hC'arc, hp', hq', hpq', hinter',
    hd, hd', hNpos, hBi, hunion, h8d, hsep, hball⟩ :=
    euclid_scale_simple_arc_ver2 hC hp hq hpq hinter
  -- Grid properties for each segment (total function G : ℕ → Finset)
  have hgp : ∀ i, ∃ Gi : Finset (Set E2), i < N →
      (∀ e ∈ Gi, isEdge e) ∧ Disjoint (B i) {x | UnboundedSet Gi x} ∧
      conn2 Gi ∧ hEdge (⌊(a i) 0⌋, ⌊(a i) 1⌋) ∈ Gi ∧
      hEdge (⌊(a (i + 1)) 0⌋, ⌊(a (i + 1)) 1⌋) ∈ Gi ∧
      (∀ y ∈ ⋃₀ (curveCells Gi : Set (Set E2)), ∃ x ∈ B i, dist x y < 4) := by
    intro i; by_cases hi : i < N
    · obtain ⟨Gi, h⟩ := simple_arc_grid_properties (hBi i hi); exact ⟨Gi, fun _ => h⟩
    · exact ⟨∅, fun h => absurd h hi⟩
  choose G hGprop using hgp
  have hGedge : ∀ i, i < N → ∀ e ∈ G i, isEdge e := fun i hi => (hGprop i hi).1
  have hGdisj : ∀ i, i < N → Disjoint (B i) {x | UnboundedSet (G i) x} :=
    fun i hi => (hGprop i hi).2.1
  have hGconn : ∀ i, i < N → conn2 (G i) := fun i hi => (hGprop i hi).2.2.1
  have hGa : ∀ i, i < N → hEdge (⌊(a i) 0⌋, ⌊(a i) 1⌋) ∈ G i :=
    fun i hi => (hGprop i hi).2.2.2.1
  have hGab : ∀ i, i < N → hEdge (⌊(a (i + 1)) 0⌋, ⌊(a (i + 1)) 1⌋) ∈ G i :=
    fun i hi => (hGprop i hi).2.2.2.2.1
  have hGcc : ∀ i, i < N → ∀ y ∈ ⋃₀ (curveCells (G i) : Set (Set E2)),
      ∃ x ∈ B i, dist x y < 4 := fun i hi => (hGprop i hi).2.2.2.2.2
  -- Union of edge sets
  set E' := (Finset.range N).biUnion G
  have hE'edge : ∀ e ∈ E', isEdge e := by
    intro e he; rw [Finset.mem_biUnion] at he
    obtain ⟨i, hi, hei⟩ := he; exact hGedge i (Finset.mem_range.mp hi) e hei
  -- C' disjoint from unbounded(E')
  have hC'unbnd : Disjoint C' {x | UnboundedSet E' x} := by
    rw [Set.disjoint_left]; intro x hxC' hxunbnd
    rw [hunion] at hxC'; simp only [Set.mem_iUnion, Finset.mem_range] at hxC'
    obtain ⟨i, hi, hxBi⟩ := hxC'
    exact Set.disjoint_left.mp (hGdisj i hi) hxBi
      (unbounded_avoidance_subset_ver2 (G i) E' x hxunbnd
        (Finset.subset_biUnion_of_mem G (Finset.mem_range.mpr hi))
        hE'edge (hGconn i hi))
  -- Helper: edges of G k fit in closedBall c (7d) for any c ∈ B k
  have hedge_ball : ∀ k, k < N → ∀ c ∈ B k,
      ⋃₀ (G k : Set (Set E2)) ⊆ Metric.closedBall c (7 * d) := by
    intro k hk c hcBk y hy
    -- y is in some edge, hence in curveCells
    have hy_cc : y ∈ ⋃₀ (curveCells (G k) : Set (Set E2)) := by
      rw [Set.mem_sUnion] at hy ⊢; obtain ⟨e, he, hye⟩ := hy
      exact ⟨e, (curveCells_edge (G k) e (hGedge k hk e he)).mpr he, hye⟩
    obtain ⟨x, hxBk, hd_xy⟩ := hGcc k hk y hy_cc
    obtain ⟨center, hcenter, hball_k⟩ := hball k hk
    rw [Metric.mem_closedBall, dist_comm]
    calc dist c y ≤ dist c x + dist x y := dist_triangle _ _ _
      _ ≤ (dist c center + dist center x) + dist x y := by linarith [dist_triangle c center x]
      _ ≤ 7 * d := by
          linarith [Metric.mem_ball.mp (hball_k hcBk), Metric.mem_ball.mp (hball_k hxBk),
                    dist_comm center x]
  -- Helper: any point with 8d-separation from C' is unbounded for E'
  suffices h_unbnd : ∀ pt, (∀ x ∈ C', 8 * d ≤ dist x pt) → UnboundedSet E' pt by
    -- Derive contradiction
    obtain ⟨U, hUsub, hU_arc⟩ := unbounded_connect hE'edge hpq'
      (h_unbnd p' (fun x hx => (h8d x hx).1)) (h_unbnd q' (fun x hx => (h8d x hx).2))
    obtain ⟨z, hzC', hzU⟩ := hinter' U hU_arc
    exact absurd (hUsub hzU) (Set.disjoint_left.mp hC'unbnd hzC')
  -- Prove the suffices: any 8d-distant point is unbounded for E'
  intro pt hpt_dist
  -- Any c ∈ B k ⊆ C' satisfies dist pt c > 7d
  have hpt_far : ∀ k, k < N → ∀ c ∈ B k, pt ∉ Metric.closedBall c (7 * d) := by
    intro k hk c hcBk hmem; rw [Metric.mem_closedBall] at hmem
    linarith [hpt_dist c (hunion ▸ Set.mem_biUnion (Finset.mem_range.mpr hk) hcBk),
              dist_comm pt c]
  have hpt_unbnd_single : ∀ k, k < N → UnboundedSet (G k) pt := by
    intro k hk; obtain ⟨c, hcBk, _⟩ := hball k hk
    exact unboundedSet_ball (by linarith) (hGedge k hk) (hedge_ball k hk c hcBk)
      (hpt_far k hk c hcBk)
  by_cases hN1 : N = 1
  · -- N = 1: E' = G 0
    rw [show E' = G 0 from by simp [E', hN1]]; exact hpt_unbnd_single 0 (by omega)
  · -- N ≥ 2: use conn2_sequence
    have hN2 : 2 ≤ N := by omega
    have ha_right : ∀ i, i < N → a (i + 1) ∈ B i :=
      fun i hi => isSimpleArcEnd_mem_right (hBi i hi)
    have ha_left : ∀ i, i < N → a i ∈ B i :=
      fun i hi => isSimpleArcEnd_mem_left (hBi i hi)
    have := conn2_sequence G (N - 1) pt (by omega)
      (fun i hi => hGconn i (by omega)) (fun i hi => hGedge i (by omega))
      -- Shared edges: hEdge at floor(a(i+1)) is in both G i and G (i+1)
      (fun i hi => ⟨hEdge (⌊(a (i + 1)) 0⌋, ⌊(a (i + 1)) 1⌋),
        Finset.mem_inter.mpr ⟨hGab i (by omega), hGa (i + 1) (by omega)⟩⟩)
      -- Disjoint curve cells for non-adjacent
      (by intro i j hij hjN hneq
          rw [Set.disjoint_left]; intro c hci hcj
          have hc_cell := curveCells_subset_cell (G i) (hGedge i (by omega)) c hci
          obtain ⟨u, hu⟩ := cell_nonempty hc_cell
          obtain ⟨x, hxBi, hd_xu⟩ := hGcc i (by omega) u (Set.mem_sUnion.mpr ⟨c, hci, hu⟩)
          obtain ⟨y, hyBj, hd_yu⟩ := hGcc j (by omega) u (Set.mem_sUnion.mpr ⟨c, hcj, hu⟩)
          linarith [hsep i j x y (by omega) (by omega) hxBi hyBj,
                    dist_triangle x u y, dist_comm u y])
      -- Unbounded for each consecutive pair
      (by intro i hi
          apply unboundedSet_ball (by linarith : (0 : ℝ) < 7 * d)
            (by intro e he; rw [Finset.mem_union] at he
                rcases he with h | h
                · exact hGedge i (by omega) e h
                · exact hGedge (i + 1) (by omega) e h)
            (by rw [Finset.coe_union, Set.sUnion_union]
                exact Set.union_subset
                  (hedge_ball i (by omega) (a (i + 1)) (ha_right i (by omega)))
                  (hedge_ball (i + 1) (by omega) (a (i + 1)) (ha_left (i + 1) (by omega))))
            (hpt_far i (by omega) (a (i + 1)) (ha_right i (by omega))))
    rwa [show Finset.range (N - 1 + 1) = Finset.range N from by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ N)]] at this

/-! ## §AA.10 cut_arc definition and lemmas -/

/-- HOL Light: `cut_arc` (line 53442).
The sub-arc of C from v to w, chosen by Hilbert's epsilon. -/
noncomputable def cutArc (C : Set E2') (v w : E2') : Set E2' :=
  Classical.epsilon (fun B => IsSimpleArcEnd B v w ∧ B ⊆ C)

/-- HOL Light: `cut_arc_symm` (line 53445). -/
theorem cutArc_symm (C : Set E2') (v w : E2') :
    cutArc C v w = cutArc C w v := by
  unfold cutArc
  congr 1
  ext B
  constructor <;> (intro ⟨h, hs⟩; exact ⟨isSimpleArcEnd_symm h, hs⟩)

/-- HOL Light: `cut_arc_simple` (line 53455).
cutArc of a simple arc at two of its distinct points is a simple arc end. -/
theorem cutArc_isSimpleArcEnd {C : Set E2'} {v w : E2'}
    (hC : IsSimpleArc C) (hv : v ∈ C) (hw : w ∈ C) (hvw : v ≠ w) :
    IsSimpleArcEnd (cutArc C v w) v w := by
  unfold cutArc
  have ⟨C', hC'sub, hC'arc⟩ := isSimpleArcEnd_select hC hv hw hvw
  exact (Classical.epsilon_spec
    (show ∃ B, IsSimpleArcEnd B v w ∧ B ⊆ C from ⟨C', hC'arc, hC'sub⟩)).1

/-- HOL Light: `cut_arc_subset` (line 53466).
cutArc is a subset of the original arc. -/
theorem cutArc_subset {C : Set E2'} {v w : E2'}
    (hC : IsSimpleArc C) (hv : v ∈ C) (hw : w ∈ C) (hvw : v ≠ w) :
    cutArc C v w ⊆ C := by
  unfold cutArc
  have ⟨C', hC'sub, hC'arc⟩ := isSimpleArcEnd_select hC hv hw hvw
  exact (Classical.epsilon_spec
    (show ∃ B, IsSimpleArcEnd B v w ∧ B ⊆ C from ⟨C', hC'arc, hC'sub⟩)).2

/-- HOL Light: `cut_arc_unique` (line 53477).
If B is a sub-arc of C from v to w, then cutArc C v w = B (by injectivity). -/
theorem cutArc_unique {C B : Set E2'} {v w : E2'}
    (hC : IsSimpleArc C) (hBC : B ⊆ C) (hB : IsSimpleArcEnd B v w) :
    cutArc C v w = B := by
  have hvw := isSimpleArcEnd_distinct hB
  have hv : v ∈ C := hBC (isSimpleArcEnd_mem_left hB)
  have hw : w ∈ C := hBC (isSimpleArcEnd_mem_right hB)
  exact isSimpleArcEnd_inj (cutArc_isSimpleArcEnd hC hv hw hvw) hB hC
    (cutArc_subset hC hv hw hvw) hBC

/-- HOL Light: `cut_arc_inter` (line 53503).
Cutting a simple arc end C at an interior point u: the two pieces
intersect at {u} and their union is C. -/
theorem cutArc_inter {C : Set E2'} {v w u : E2'}
    (hC : IsSimpleArcEnd C v w) (hu : u ∈ C)
    (huv : u ≠ v) (huw : u ≠ w) :
    cutArc C v u ∩ cutArc C u w = {u} ∧
    cutArc C v u ∪ cutArc C u w = C := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hinter, hunion⟩ := isSimpleArcEnd_cut hC hu huv huw
  have hCsimp : IsSimpleArc C := isSimpleArcEnd_isSimpleArc hC
  have hC₁sub : C₁ ⊆ C := hunion ▸ Set.subset_union_left
  have hC₂sub : C₂ ⊆ C := hunion ▸ Set.subset_union_right
  rw [cutArc_unique hCsimp hC₁sub hC₁, cutArc_unique hCsimp hC₂sub hC₂]
  exact ⟨hinter, hunion⟩

/-! ## §AA.11 Closed curve cut uniqueness -/

/-- HOL Light: `simple_closed_curve_cut_unique` (line 53561).
On a simple closed curve, any sub-arc between two points must be
one of the two canonical halves. -/
theorem isSimpleClosedCurve_cut_unique {A A' A'' C : Set E2'} {v w : E2'}
    (hC : IsSimpleClosedCurve C)
    (hA : IsSimpleArcEnd A v w)
    (hA' : IsSimpleArcEnd A' v w)
    (hA'' : IsSimpleArcEnd A'' v w)
    (hne : A' ≠ A'')
    (hAsub : A ⊆ C) (hA'sub : A' ⊆ C) (hA''sub : A'' ⊆ C) :
    A = A' ∨ A = A'' := by
  have hvw : v ≠ w := isSimpleArcEnd_distinct hA
  have hvC : v ∈ C := hA'sub (isSimpleArcEnd_mem_left hA')
  have hwC : w ∈ C := hA'sub (isSimpleArcEnd_mem_right hA')
  -- Cut C into two canonical halves
  obtain ⟨C₁, C₂, hC₁, hC₂, hunion, hinter⟩ := isSimpleClosedCurve_cut hC hvC hwC hvw
  -- Closedness of halves
  have hC₁closed : IsClosed C₁ :=
    (isSimpleArc_compact (isSimpleArcEnd_isSimpleArc hC₁)).isClosed
  have hC₂closed : IsClosed C₂ :=
    (isSimpleArc_compact (isSimpleArcEnd_isSimpleArc hC₂)).isClosed
  -- Endpoints are in both halves (from C₁ ∩ C₂ = {v, w})
  have hv_C₁ : v ∈ C₁ := by
    have : {v, w} ⊆ C₁ ∩ C₂ := hinter ▸ Subset.rfl
    exact (this (Set.mem_insert v {w})).1
  have hw_C₁ : w ∈ C₁ := by
    have : {v, w} ⊆ C₁ ∩ C₂ := hinter ▸ Subset.rfl
    exact (this (Set.mem_insert_of_mem v rfl)).1
  have hv_C₂ : v ∈ C₂ := by
    have : {v, w} ⊆ C₁ ∩ C₂ := hinter ▸ Subset.rfl
    exact (this (Set.mem_insert v {w})).2
  have hw_C₂ : w ∈ C₂ := by
    have : {v, w} ⊆ C₁ ∩ C₂ := hinter ▸ Subset.rfl
    exact (this (Set.mem_insert_of_mem v rfl)).2
  -- Key claim: any simple arc end from v to w contained in C must be C₁ or C₂
  suffices key : ∀ B : Set E2', IsSimpleArcEnd B v w → B ⊆ C →
      B = C₁ ∨ B = C₂ by
    have hA_eq := key A hA hAsub
    have hA'_eq := key A' hA' hA'sub
    have hA''_eq := key A'' hA'' hA''sub
    -- Pigeonhole: A' ≠ A'' so they occupy different halves, A must be one of them
    rcases hA'_eq with rfl | rfl <;> rcases hA''_eq with rfl | rfl
    · exact absurd rfl hne
    · exact hA_eq
    · exact hA_eq.elim Or.inr Or.inl
    · exact absurd rfl hne
  -- Proof of key claim
  intro B hB hBsub
  obtain ⟨g, hBimg, hgcont, hginj, hg0, hg1⟩ := hB
  -- Preimages of C₁, C₂ under g are closed
  have hgC₁ : IsClosed (g ⁻¹' C₁) := hC₁closed.preimage hgcont
  have hgC₂ : IsClosed (g ⁻¹' C₂) := hC₂closed.preimage hgcont
  -- Ioo 0 1 ⊆ g⁻¹(C₁) ∪ g⁻¹(C₂)
  have hIoo_sub : Ioo (0 : ℝ) 1 ⊆ g ⁻¹' C₁ ∪ g ⁻¹' C₂ := by
    intro s hs
    have hgs : g s ∈ B := hBimg ▸ Set.mem_image_of_mem g (Ioo_subset_Icc_self hs)
    have hgsC : g s ∈ C := hBsub hgs
    rw [← hunion] at hgsC; exact hgsC
  -- g⁻¹(C₁ ∩ C₂) ∩ Ioo 0 1 = ∅
  have hIoo_disj : (Ioo (0 : ℝ) 1 ∩ (g ⁻¹' C₁ ∩ g ⁻¹' C₂)) = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro ⟨s, hs, hgsC₁, hgsC₂⟩
    have hgs_inter : g s ∈ C₁ ∩ C₂ := ⟨hgsC₁, hgsC₂⟩
    rw [hinter] at hgs_inter
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgs_inter
    rcases hgs_inter with hgs_eq | hgs_eq
    · have hscc : s ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs
      have := hginj hscc (left_mem_Icc.mpr zero_le_one) (by rw [hgs_eq, hg0])
      linarith [hs.1]
    · have hscc : s ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs
      have := hginj hscc (right_mem_Icc.mpr zero_le_one) (by rw [hgs_eq, hg1])
      linarith [hs.2]
  -- By connectedness of Ioo, one preimage must be empty on Ioo
  have key2 : Ioo (0 : ℝ) 1 ∩ g ⁻¹' C₁ = ∅ ∨ Ioo (0 : ℝ) 1 ∩ g ⁻¹' C₂ = ∅ := by
    by_contra h
    push Not at h
    have := (isPreconnected_closed_iff.mp isPreconnected_Ioo) _ _ hgC₁ hgC₂ hIoo_sub h.1 h.2
    rw [hIoo_disj] at this
    exact this.ne_empty rfl
  -- From key2, deduce B ⊆ C₁ or B ⊆ C₂
  have hBsub_half : B ⊆ C₁ ∨ B ⊆ C₂ := by
    rcases key2 with hempty | hempty
    · -- Ioo ∩ g⁻¹(C₁) = ∅ → B ⊆ C₂
      right; rw [hBimg]; rintro _ ⟨s, hs, rfl⟩
      rcases hs.1.eq_or_lt with rfl | h0
      · exact hg0 ▸ hv_C₂
      · rcases hs.2.eq_or_lt with h1 | h1s
        · exact h1 ▸ hg1 ▸ hw_C₂
        · have hsC₁ : g s ∉ C₁ := fun habs =>
            (Set.eq_empty_iff_forall_notMem.mp hempty) s ⟨⟨h0, h1s⟩, habs⟩
          have hsC : g s ∈ C₁ ∪ C₂ :=
            hunion ▸ hBsub (hBimg ▸ ⟨s, hs, rfl⟩)
          exact hsC.resolve_left hsC₁
    · -- Ioo ∩ g⁻¹(C₂) = ∅ → B ⊆ C₁
      left; rw [hBimg]; rintro _ ⟨s, hs, rfl⟩
      rcases hs.1.eq_or_lt with rfl | h0
      · exact hg0 ▸ hv_C₁
      · rcases hs.2.eq_or_lt with h1 | h1s
        · exact h1 ▸ hg1 ▸ hw_C₁
        · have hsC₂ : g s ∉ C₂ := fun habs =>
            (Set.eq_empty_iff_forall_notMem.mp hempty) s ⟨⟨h0, h1s⟩, habs⟩
          have hsC : g s ∈ C₁ ∪ C₂ :=
            hunion ▸ hBsub (hBimg ▸ ⟨s, hs, rfl⟩)
          exact hsC.resolve_right hsC₂
  -- By isSimpleArcEnd_inj, B = C₁ or B = C₂
  rcases hBsub_half with hB₁ | hB₂
  · left
    have hBarc : IsSimpleArcEnd B v w :=
      ⟨g, hBimg, hgcont, hginj, hg0, hg1⟩
    exact isSimpleArcEnd_inj hBarc hC₁ (isSimpleArcEnd_isSimpleArc hC₁) hB₁ Subset.rfl
  · right
    have hBarc : IsSimpleArcEnd B v w :=
      ⟨g, hBimg, hgcont, hginj, hg0, hg1⟩
    exact isSimpleArcEnd_inj hBarc hC₂ (isSimpleArcEnd_isSimpleArc hC₂) hB₂ Subset.rfl

/-! ## §AA.12 Infinite arcs -/

/-- HOL Light: `simple_arc_infinite` (line 53955).
A simple arc is an infinite set. -/
theorem isSimpleArc_infinite {C : Set E2'} (hC : IsSimpleArc C) :
    C.Infinite := by
  obtain ⟨f, rfl, _, hinj⟩ := hC
  exact (Set.infinite_image_iff hinj).mpr (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1))

/-- HOL Light: `simple_closed_curve_cut_unique_inter` (line 53968).
Variant of cut uniqueness where A' ∩ A'' = {v, w}. -/
theorem isSimpleClosedCurve_cut_unique_inter {A A' A'' C : Set E2'} {v w : E2'}
    (hC : IsSimpleClosedCurve C)
    (hA : IsSimpleArcEnd A v w)
    (hA' : IsSimpleArcEnd A' v w)
    (hA'' : IsSimpleArcEnd A'' v w)
    (hinter : A' ∩ A'' = {v, w})
    (hAsub : A ⊆ C) (hA'sub : A' ⊆ C) (hA''sub : A'' ⊆ C) :
    A = A' ∨ A = A'' := by
  apply isSimpleClosedCurve_cut_unique hC hA hA' hA'' ?_ hAsub hA'sub hA''sub
  intro heq
  rw [← heq, Set.inter_self] at hinter
  exact absurd (hinter ▸ Set.toFinite _)
    (isSimpleArc_infinite (isSimpleArcEnd_isSimpleArc hA'))

/-! ## §AA.13 Jordan curve access lemma -/

/-- HOL Light: `jordan_curve_access` (line 53996).
Given a simple closed curve C, a sub-arc A of C, a point x interior to A,
and a point p not on C that cannot be separated from some q by C,
there exists an arc E from p to x such that E ∩ C ⊆ A, and
for any non-C point e on E (other than p), the initial segment of E
from p to e avoids C entirely. -/
theorem jordan_curve_access {A C : Set E2'} {v w x p : E2'}
    (hC : IsSimpleClosedCurve C)
    (hA : IsSimpleArcEnd A v w)
    (hAsub : A ⊆ C) (hx : x ∈ A) (_hxv : x ≠ v) (_hxw : x ≠ w)
    (hpC : p ∉ C)
    (hq : ∃ q : E2', p ≠ q ∧ q ∉ C ∧
      ∀ B : Set E2', IsSimpleArcEnd B p q → (B ∩ C).Nonempty) :
    ∃ E : Set E2',
      IsSimpleArcEnd E p x ∧
      E ∩ C ⊆ A ∧
      (∀ e, e ∈ E → e ∉ C → p ≠ e →
        Disjoint (cutArc E p e) C) := by
  obtain ⟨q, hpq, hqC, hqinter⟩ := hq
  have hvC : v ∈ C := hAsub (isSimpleArcEnd_mem_left hA)
  have hwC : w ∈ C := hAsub (isSimpleArcEnd_mem_right hA)
  have hvw : v ≠ w := isSimpleArcEnd_distinct hA
  -- Cut the closed curve into two arcs
  obtain ⟨C₁, C₂, hC₁, hC₂, hunion, hinter_vw⟩ :=
    isSimpleClosedCurve_cut hC hvC hwC hvw
  -- A must equal one of C₁, C₂; define B as the other
  obtain ⟨B, hB, hAB_union, hAB_inter⟩ :
      ∃ B, IsSimpleArcEnd B v w ∧ A ∪ B = C ∧ A ∩ B = {v, w} := by
    rcases isSimpleClosedCurve_cut_unique_inter hC hA hC₁ hC₂ hinter_vw
      hAsub (hunion ▸ Set.subset_union_left) (hunion ▸ Set.subset_union_right) with rfl | rfl
    · exact ⟨C₂, hC₂, hunion, hinter_vw⟩
    · exact ⟨C₁, hC₁, Set.union_comm _ _ ▸ hunion, Set.inter_comm _ _ ▸ hinter_vw⟩
  have hBsub : B ⊆ C := hAB_union ▸ Set.subset_union_right
  -- Connect p and q avoiding B (the "other" arc)
  obtain ⟨F, hF_arc, hF_disj⟩ := simple_arc_conn_complement
    (isSimpleArcEnd_isSimpleArc hB) (fun h => hpC (hBsub h))
    (fun h => hqC (hBsub h)) hpq
  -- F ∩ C ⊆ A (since F avoids B and C = A ∪ B)
  have hFC_sub_A : F ∩ C ⊆ A := by
    intro z ⟨hzF, hzC⟩; rw [← hAB_union] at hzC
    exact hzC.elim id fun hb => absurd hzF (Set.disjoint_left.mp hF_disj hb)
  -- F meets A (since F meets C by hqinter)
  have hFA_ne : (F ∩ A).Nonempty := by
    obtain ⟨z, hzF, hzC⟩ := hqinter F hF_arc
    exact ⟨z, hzF, hFC_sub_A ⟨hzF, hzC⟩⟩
  -- Restrict F: get sub-arc C' from p to first contact w' with A
  have hdisj : F ∩ {p} ∩ A = ∅ := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
      iff_false, not_and]; rintro ⟨_, rfl⟩; exact fun h => hpC (hAsub h)
  obtain ⟨C', v', w', hC'sub, hC'arc, hC'p, hC'A⟩ :=
    isSimpleArcEnd_restriction (isSimpleArcEnd_isSimpleArc hF_arc) isClosed_singleton
      (isSimpleArcEnd_isClosed hA) hdisj
      ⟨p, isSimpleArcEnd_mem_left hF_arc, Set.mem_singleton p⟩ hFA_ne
  -- v' = p (the contact with {p})
  have hv'p : v' = p := by
    have h := (Set.eq_singleton_iff_unique_mem.mp hC'p).1
    exact Set.mem_singleton_iff.mp h.2
  subst hv'p
  -- w' ∈ A
  have hw'A : w' ∈ A := ((Set.eq_singleton_iff_unique_mem.mp hC'A).1).2
  -- C' avoids B (since C' ⊆ F and F avoids B)
  have hC'B : Disjoint C' B := Disjoint.mono_left hC'sub hF_disj.symm
  -- C' ∩ C = {w'}
  have hC'C : C' ∩ C = {w'} := by
    rw [← hAB_union, Set.inter_union_distrib_left,
        Set.disjoint_iff_inter_eq_empty.mp hC'B, hC'A, Set.union_empty]
  -- Key lemma: cutArc C' v' e is disjoint from C for e ∈ C' \ C
  have hC'_disj : ∀ e, e ∈ C' → e ∉ C → v' ≠ e →
      Disjoint (cutArc C' v' e) C := by
    intro e he heC hpe
    have hew' : e ≠ w' := by intro h; subst h; exact heC (hAsub hw'A)
    have hC'_sa := isSimpleArcEnd_isSimpleArc hC'arc
    have hp_C' := isSimpleArcEnd_mem_left hC'arc
    have hw'_C' := isSimpleArcEnd_mem_right hC'arc
    have hcut_sub := cutArc_subset hC'_sa hp_C' he hpe
    obtain ⟨hinter_e, _⟩ := cutArc_inter hC'arc he (Ne.symm hpe) hew'
    rw [Set.disjoint_left]
    intro z hz hzC
    have hzw' : z = w' := by
      have h : z ∈ C' ∩ C := ⟨hcut_sub hz, hzC⟩
      rw [hC'C, Set.mem_singleton_iff] at h; exact h
    subst hzw'
    have : z ∈ cutArc C' v' e ∩ cutArc C' e z :=
      ⟨hz, isSimpleArcEnd_mem_right
        (cutArc_isSimpleArcEnd hC'_sa he hw'_C' hew')⟩
    rw [hinter_e] at this
    exact hew' ((Set.mem_singleton_iff.mp this).symm)
  -- Case split on x = w' or x ≠ w'
  by_cases hxw' : x = w'
  · -- Case x = w': take E = C'
    refine ⟨C', ?_, ?_, hC'_disj⟩
    · rw [hxw']; exact hC'arc
    · intro z ⟨hzC', hzC⟩
      have h : z ∈ C' ∩ C := ⟨hzC', hzC⟩
      rw [hC'C, Set.mem_singleton_iff] at h; subst h; exact hw'A
  · -- Case x ≠ w': take E = C' ∪ cutArc A w' x
    have hw'x : w' ≠ x := Ne.symm hxw'
    have hA_sa := isSimpleArcEnd_isSimpleArc hA
    have hcutvx_arc := cutArc_isSimpleArcEnd hA_sa hw'A hx hw'x
    have hcutvx_sub := cutArc_subset hA_sa hw'A hx hw'x
    have hC'_cutvx : C' ∩ cutArc A w' x = {w'} := by
      ext z; constructor
      · rintro ⟨hzC', hzcutvx⟩
        have h : z ∈ C' ∩ A := ⟨hzC', hcutvx_sub hzcutvx⟩
        rw [hC'A] at h; exact h
      · intro hz; rw [Set.mem_singleton_iff] at hz; subst hz
        exact ⟨(Set.eq_singleton_iff_unique_mem.mp hC'A).1.1,
               isSimpleArcEnd_mem_left hcutvx_arc⟩
    have hE_arc := isSimpleArcEnd_trans hC'arc hcutvx_arc hC'_cutvx
    refine ⟨C' ∪ cutArc A w' x, hE_arc, ?_, ?_⟩
    · intro z ⟨hzE, hzC⟩
      rcases hzE with hzC' | hzcutvx
      · have h : z ∈ C' ∩ C := ⟨hzC', hzC⟩
        rw [hC'C, Set.mem_singleton_iff] at h; subst h; exact hw'A
      · exact hcutvx_sub hzcutvx
    · intro e he heC hpe
      have heC' : e ∈ C' := by
        rcases he with h | h
        · exact h
        · exact absurd (hAsub (hcutvx_sub h)) heC
      have hC'_sa := isSimpleArcEnd_isSimpleArc hC'arc
      have hp_C' := isSimpleArcEnd_mem_left hC'arc
      have hcut_eq : cutArc (C' ∪ cutArc A w' x) v' e =
          cutArc C' v' e :=
        cutArc_unique (isSimpleArcEnd_isSimpleArc hE_arc)
          ((cutArc_subset hC'_sa hp_C' heC' hpe).trans
            Set.subset_union_left)
          (cutArc_isSimpleArcEnd hC'_sa hp_C' heC' hpe)
      rw [hcut_eq]
      exact hC'_disj e heC' heC hpe

end -- section

end JordanCurveTheorem
