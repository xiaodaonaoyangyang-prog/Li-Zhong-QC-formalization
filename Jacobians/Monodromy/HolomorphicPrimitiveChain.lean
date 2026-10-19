/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Primitive chains along paths (Wall A, step 1 — discrete analytic continuation)

The discrete continuation of a local primitive of a holomorphic 1-form `η` along a continuous
path `γ : [0,1] → X`, with **no integration**: a `PrimitiveChain` is a partition
`0 = t₀ ≤ t₁ ≤ … ≤ tₙ = 1` together with local primitives `Fᵢ` on opens `Uᵢ ⊇ γ([tᵢ, tᵢ₊₁])`;
its `value` is the telescoping sum `∑ᵢ Fᵢ(γ(tᵢ₊₁)) − Fᵢ(γ(tᵢ))` — classically `∫_γ η`.

* `exists_primitiveChain` — chains exist (Mathlib's subdivision lemma
  `exists_monotone_Icc_subset_open_cover_Icc` against the cover by primitive neighbourhoods);
* `value_eq_of_chains` — the value does **not** depend on the chain: the capped partial value
  `partialValue s = ∑ᵢ Fᵢ(γ(min s tᵢ₊₁)) − Fᵢ(γ(min s tᵢ))` of two chains has locally constant
  difference on `[0,1]` (block-wise, two primitives differ by a constant near each path point —
  step 0's rigidity), hence constant difference (`IsLocallyConstant` on the preconnected
  interval), and the difference vanishes at `s = 0`.

Reference: Forster, *Lectures on Riemann Surfaces*, §10.4–10.5 (primitive along a curve);
the classical Cauchy-theory "analytic continuation along paths" argument.
-/
import Jacobians.Monodromy.HolomorphicPrimitiveLocal

noncomputable section

open scoped Manifold ContDiff Topology
open Set Metric Filter

namespace Jacobians


variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Helpers -/

/-- Restricting a primitive to a smaller set. -/
theorem IsLocalPrimitiveOn.mono {η : HolomorphicOneForms X} {F : X → ℂ} {U V : Set X}
    (h : IsLocalPrimitiveOn η F U) (hVU : V ⊆ U) : IsLocalPrimitiveOn η F V :=
  fun y hy => h y (hVU hy)

/-- Every neighbourhood contains a path-connected open neighbourhood (the chart-ball preimage —
the manifold is locally path-connected in the strong chart sense used throughout). -/
theorem exists_isPathConnected_open_mem_nhds {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] {x : X} {V : Set X} (hV : V ∈ 𝓝 x) :
    ∃ B : Set X, IsOpen B ∧ IsPathConnected B ∧ x ∈ B ∧ B ⊆ V := by
  set e := chartAt ℂ x with he
  have hT : IsOpen (e.target ∩ e.symm ⁻¹' interior V) :=
    e.isOpen_inter_preimage_symm isOpen_interior
  have hz₀ : e x ∈ e.target ∩ e.symm ⁻¹' interior V :=
    ⟨e.map_source (mem_chart_source ℂ x), by
      rw [Set.mem_preimage, e.left_inv (mem_chart_source ℂ x)]
      exact mem_interior_iff_mem_nhds.mpr hV⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds hz₀)
  have hsub : ball (e x) r ⊆ e.target := fun z hz => (hball hz).1
  refine ⟨e.symm '' ball (e x) r, ?_, ?_, ?_, ?_⟩
  · rw [e.symm_image_eq_source_inter_preimage hsub]
    exact e.isOpen_inter_preimage isOpen_ball
  · exact ((convex_ball _ _).isPathConnected ⟨e x, mem_ball_self hr⟩).image'
      (e.continuousOn_symm.mono hsub)
  · exact ⟨e x, mem_ball_self hr, e.left_inv (mem_chart_source ℂ x)⟩
  · rintro y ⟨z, hz, rfl⟩
    exact interior_subset (hball hz).2

/-! ### Primitive chains -/

/-- A **primitive chain** along `γ`: a stabilized monotone partition of `[0,1]` together with a
local primitive of `η` on an open set containing each sub-arc of `γ`. -/
structure PrimitiveChain (η : HolomorphicOneForms X) (γ : ℝ → X) where
  /-- number of blocks -/
  n : ℕ
  /-- the partition points (constant `= 1` from index `n` on) -/
  t : ℕ → ℝ
  t_zero : t 0 = 0
  t_stab : ∀ k, n ≤ k → t k = 1
  mono : Monotone t
  /-- the block opens -/
  U : ℕ → Set X
  /-- the block primitives -/
  F : ℕ → X → ℂ
  isOpen : ∀ i, IsOpen (U i)
  prim : ∀ i, IsLocalPrimitiveOn η (F i) (U i)
  covers : ∀ i, ∀ s ∈ Icc (t i) (t (i + 1)), γ s ∈ U i

namespace PrimitiveChain

variable {η : HolomorphicOneForms X} {γ : ℝ → X} (C : PrimitiveChain η γ)

theorem t_nonneg (k : ℕ) : 0 ≤ C.t k := by
  have h := C.mono (Nat.zero_le k)
  rwa [C.t_zero] at h

theorem t_le_one (k : ℕ) : C.t k ≤ 1 := by
  rcases Nat.lt_or_ge k C.n with h | h
  · have hm := C.mono h.le
    rwa [C.t_stab C.n le_rfl] at hm
  · exact (C.t_stab k h).le

theorem n_pos : 0 < C.n := by
  rcases Nat.eq_zero_or_pos C.n with h | h
  · have h0 := C.t_stab 0 h.le
    rw [C.t_zero] at h0
    norm_num at h0
  · exact h

/-- The chain **value**: the telescoping sum `∑ᵢ Fᵢ(γ(tᵢ₊₁)) − Fᵢ(γ(tᵢ))`. -/
def value : ℂ :=
  ∑ i ∈ Finset.range C.n, (C.F i (γ (C.t (i + 1))) - C.F i (γ (C.t i)))

/-- The **capped partial value** at time `s`: each block is capped at `s`
(`min`-form; for `s = 1` this is `value`, for `s = 0` it vanishes). -/
def partialValue (s : ℝ) : ℂ :=
  ∑ i ∈ Finset.range C.n, (C.F i (γ (min s (C.t (i + 1)))) - C.F i (γ (min s (C.t i))))

theorem partialValue_zero : C.partialValue 0 = 0 := by
  rw [partialValue]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [min_eq_left (C.t_nonneg (i + 1)), min_eq_left (C.t_nonneg i), sub_self]

theorem partialValue_one : C.partialValue 1 = C.value := by
  rw [partialValue, value]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [min_eq_right (C.t_le_one (i + 1)), min_eq_right (C.t_le_one i)]

/-- **The block formula**: for `s` in block `k`, the partial value is the full sum of the first
`k` blocks plus the capped `k`-th block. -/
theorem partialValue_eq (k : ℕ) (hk : k < C.n) {s : ℝ} (hs : s ∈ Icc (C.t k) (C.t (k + 1))) :
    C.partialValue s
      = (∑ i ∈ Finset.range k, (C.F i (γ (C.t (i + 1))) - C.F i (γ (C.t i))))
        + (C.F k (γ s) - C.F k (γ (C.t k))) := by
  rw [partialValue, ← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hk),
    Finset.sum_range_succ]
  have hzero : ∑ i ∈ Finset.Ico (k + 1) C.n,
      (C.F i (γ (min s (C.t (i + 1)))) - C.F i (γ (min s (C.t i)))) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hki : k + 1 ≤ i := (Finset.mem_Ico.mp hi).1
    have h1 : s ≤ C.t i := hs.2.trans (C.mono hki)
    have h2 : s ≤ C.t (i + 1) := h1.trans (C.mono (Nat.le_succ i))
    rw [min_eq_left h2, min_eq_left h1, sub_self]
  rw [hzero, add_zero]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hik : i + 1 ≤ k := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
    have h1 : C.t (i + 1) ≤ s := (C.mono hik).trans hs.1
    have h2 : C.t i ≤ s := (C.mono (Nat.le_succ i)).trans h1
    rw [min_eq_right h1, min_eq_right h2]
  · rw [min_eq_left hs.2, min_eq_right hs.1]

/-- For `s, s'` in a common block `k`, the partial values differ by the `Fₖ`-increment. -/
theorem partialValue_sub (k : ℕ) (hk : k < C.n) {s s' : ℝ}
    (hs : s ∈ Icc (C.t k) (C.t (k + 1))) (hs' : s' ∈ Icc (C.t k) (C.t (k + 1))) :
    C.partialValue s' - C.partialValue s = C.F k (γ s') - C.F k (γ s) := by
  rw [C.partialValue_eq k hk hs, C.partialValue_eq k hk hs']
  ring

/-- **Right block**: every `s ∈ [0,1)` lies in a block `[tₖ, tₖ₊₁)` open on the right. -/
theorem exists_block_right {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    ∃ k < C.n, C.t k ≤ s ∧ s < C.t (k + 1) := by
  classical
  have hex : ∃ m, s < C.t m := ⟨C.n, by rw [C.t_stab C.n le_rfl]; exact h1⟩
  have hms : s < C.t (Nat.find hex) := Nat.find_spec hex
  have hmpos : Nat.find hex ≠ 0 := by
    intro h0'
    rw [h0', C.t_zero] at hms
    exact absurd hms (not_lt.mpr h0)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmpos
  rw [hk] at hms
  have hks : C.t k ≤ s := by
    by_contra hlt
    exact Nat.find_min hex (by rw [hk]; exact Nat.lt_succ_self k) (not_le.mp hlt)
  refine ⟨k, ?_, hks, hms⟩
  by_contra hkn
  push Not at hkn
  rw [C.t_stab k hkn] at hks
  exact absurd (lt_of_le_of_lt hks h1) (lt_irrefl _)

/-- **Left block**: every `s ∈ (0,1]` lies in a block `(tₖ, tₖ₊₁]` open on the left. -/
theorem exists_block_left {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1) :
    ∃ k < C.n, C.t k < s ∧ s ≤ C.t (k + 1) := by
  classical
  have hex : ∃ m, s ≤ C.t m := ⟨C.n, by rw [C.t_stab C.n le_rfl]; exact h1⟩
  have hms : s ≤ C.t (Nat.find hex) := Nat.find_spec hex
  have hmpos : Nat.find hex ≠ 0 := by
    intro h0'
    rw [h0', C.t_zero] at hms
    exact absurd hms (not_le.mpr h0)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmpos
  rw [hk] at hms
  have hks : C.t k < s := by
    by_contra hle
    exact Nat.find_min hex (by rw [hk]; exact Nat.lt_succ_self k) (not_lt.mp hle)
  refine ⟨k, ?_, hks, hms⟩
  by_contra hkn
  push Not at hkn
  rw [C.t_stab k hkn] at hks
  linarith

end PrimitiveChain

/-! ### Chain existence -/

/-- **Primitive chains exist** along every continuous path: refine the open cover of `[0,1]` by
preimages of primitive neighbourhoods (Mathlib's monotone-subdivision lemma). -/
theorem exists_primitiveChain (η : HolomorphicOneForms X) {γ : ℝ → X}
    (hγ : ContinuousOn γ (Icc 0 1)) : Nonempty (PrimitiveChain η γ) := by
  classical
  -- the chart-ball primitive data at every path point
  have hdata : ∀ x : X, ∃ (U : Set X) (F : X → ℂ), IsOpen U ∧ x ∈ U ∧
      IsLocalPrimitiveOn η F U := by
    intro x
    obtain ⟨U, F, hUo, hxU, _, hprim⟩ := exists_isLocalPrimitiveOn η x
    exact ⟨U, F, hUo, hxU, hprim⟩
  choose Ud Fd hUo hmem hprim using hdata
  -- the open cover of the subtype `[0,1]` by `γ⁻¹` of the primitive neighbourhoods
  set γ' : Icc (0 : ℝ) 1 → X := fun s => γ s with hγ'
  have hγ'c : Continuous γ' := hγ.restrict
  set c : Icc (0 : ℝ) 1 → Set (Icc (0 : ℝ) 1) := fun τ => γ' ⁻¹' (Ud (γ' τ)) with hc
  have hc₁ : ∀ τ, IsOpen (c τ) := fun τ => (hUo _).preimage hγ'c
  have hc₂ : (univ : Set (Icc (0 : ℝ) 1)) ⊆ ⋃ τ, c τ := fun τ _ =>
    Set.mem_iUnion.mpr ⟨τ, hmem _⟩
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, hblocks⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc zero_le_one hc₁ hc₂
  choose τ hτ using hblocks
  -- assemble the chain
  refine ⟨{
    n := m + 1
    t := fun k => (t k : ℝ)
    t_zero := by exact_mod_cast ht0
    t_stab := fun k hk => by exact_mod_cast hm k (le_trans (Nat.le_succ m) hk)
    mono := fun a b hab => Subtype.coe_le_coe.mpr (htmono hab)
    U := fun i => Ud (γ' (τ i))
    F := fun i => Fd (γ' (τ i))
    isOpen := fun i => hUo _
    prim := fun i => hprim _
    covers := fun i s hs => ?_ }⟩
  -- block membership transfers through the subtype
  have hs01 : s ∈ Icc (0 : ℝ) 1 :=
    ⟨le_trans (t i).2.1 hs.1, le_trans hs.2 (t (i + 1)).2.2⟩
  have hmem' : (⟨s, hs01⟩ : Icc (0 : ℝ) 1) ∈ Icc (t i) (t (i + 1)) := ⟨hs.1, hs.2⟩
  have := hτ i hmem'
  rw [hc] at this
  exact this

/-! ### Chain-independence of the value -/

/-- **The chain value is chain-independent** (uniqueness of the discrete continuation,
Forster §10.4): the difference of the two capped partial values is locally constant on `[0,1]`
(one-sided block arguments + the step-0 rigidity near each path point), hence constant on the
preconnected interval; it vanishes at `0` and reads `value − value` at `1`. -/
theorem PrimitiveChain.value_eq_of_chains {η : HolomorphicOneForms X} {γ : ℝ → X}
    (hγ : ContinuousOn γ (Icc 0 1)) (C C' : PrimitiveChain η γ) : C.value = C'.value := by
  classical
  set d : ℝ → ℂ := fun s => C.partialValue s - C'.partialValue s with hd
  -- the common one-sided step: fixed blocks `k`, `k'` containing `s` and (eventually) `s'`
  have hstep : ∀ {s : ℝ}, s ∈ Icc (0:ℝ) 1 →
      ∀ {k k' : ℕ}, k < C.n → k' < C'.n →
      s ∈ Icc (C.t k) (C.t (k + 1)) → s ∈ Icc (C'.t k') (C'.t (k' + 1)) →
      ∀ s' : ℝ, s' ∈ Icc (C.t k) (C.t (k + 1)) → s' ∈ Icc (C'.t k') (C'.t (k' + 1)) →
      (C.F k (γ s') - C'.F k' (γ s')) = (C.F k (γ s) - C'.F k' (γ s)) → d s' = d s := by
    intro s _ k k' hkn hk'n hsb hsb' s' hs'b hs'b' hWconst
    have e1 := C.partialValue_sub k hkn hsb hs'b
    have e2 := C'.partialValue_sub k' hk'n hsb' hs'b'
    have : d s' - d s = (C.F k (γ s') - C'.F k' (γ s')) - (C.F k (γ s) - C'.F k' (γ s)) := by
      rw [hd]
      simp only
      rw [show C.partialValue s' - C'.partialValue s' - (C.partialValue s - C'.partialValue s)
          = (C.partialValue s' - C.partialValue s) - (C'.partialValue s' - C'.partialValue s)
        from by ring, e1, e2]
      ring
    rw [hWconst, sub_self] at this
    exact sub_eq_zero.mp this
  -- local constancy of `d` within the interval
  have hloc : ∀ s ∈ Icc (0:ℝ) 1, ∀ᶠ s' in 𝓝[Icc (0:ℝ) 1] s, d s' = d s := by
    intro s hs
    have hsplit : Icc (0:ℝ) 1 = Icc 0 s ∪ Icc s 1 := (Icc_union_Icc_eq_Icc hs.1 hs.2).symm
    rw [hsplit, nhdsWithin_union, eventually_sup]
    constructor
    · -- LEFT: `s' ≤ s`
      rcases eq_or_lt_of_le hs.1 with h0 | h0
      · -- `s = 0`: the left piece is `{0}`
        filter_upwards [self_mem_nhdsWithin] with s' hs'
        have hs'0 : s' = s := le_antisymm hs'.2 (h0 ▸ hs'.1)
        rw [hs'0]
      · obtain ⟨k, hkn, hk1, hk2⟩ := C.exists_block_left h0 hs.2
        obtain ⟨k', hk'n, hk'1, hk'2⟩ := C'.exists_block_left h0 hs.2
        have hsb : s ∈ Icc (C.t k) (C.t (k + 1)) := ⟨hk1.le, hk2⟩
        have hsb' : s ∈ Icc (C'.t k') (C'.t (k' + 1)) := ⟨hk'1.le, hk'2⟩
        have hγs : γ s ∈ C.U k ∩ C'.U k' :=
          ⟨C.covers k s hsb, C'.covers k' s hsb'⟩
        obtain ⟨W, hWo, hWpc, hγsW, hWsub⟩ := exists_isPathConnected_open_mem_nhds
          (((C.isOpen k).inter (C'.isOpen k')).mem_nhds hγs)
        have hconst : ∀ a ∈ W, C.F k a - C'.F k' a = C.F k (γ s) - C'.F k' (γ s) := by
          intro a ha
          exact isLocalPrimitiveOn_sub_const hWo (IsPathConnected.isConnected hWpc).isPreconnected
            ((C.prim k).mono fun w hw => (hWsub hw).1)
            ((C'.prim k').mono fun w hw => (hWsub hw).2) ha hγsW
        have hW' : γ ⁻¹' W ∈ 𝓝[Icc (0:ℝ) 1] s :=
          (hγ s hs).preimage_mem_nhdsWithin (hWo.mem_nhds hγsW)
        have hsubl : Icc (0:ℝ) s ⊆ Icc (0:ℝ) 1 := fun u hu => ⟨hu.1, hu.2.trans hs.2⟩
        have hWl : γ ⁻¹' W ∈ 𝓝[Icc (0:ℝ) s] s := nhdsWithin_mono s hsubl hW'
        have hgt1 : ∀ᶠ s' in 𝓝[Icc (0:ℝ) s] s, C.t k < s' :=
          eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hk1)
        have hgt2 : ∀ᶠ s' in 𝓝[Icc (0:ℝ) s] s, C'.t k' < s' :=
          eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds hk'1)
        filter_upwards [hWl, hgt1, hgt2, self_mem_nhdsWithin] with s' hWs' h1' h2' hs'mem
        have hs'b : s' ∈ Icc (C.t k) (C.t (k + 1)) := ⟨h1'.le, hs'mem.2.trans hk2⟩
        have hs'b' : s' ∈ Icc (C'.t k') (C'.t (k' + 1)) := ⟨h2'.le, hs'mem.2.trans hk'2⟩
        exact hstep hs hkn hk'n hsb hsb' s' hs'b hs'b' (hconst _ hWs')
    · -- RIGHT: `s ≤ s'`
      rcases eq_or_lt_of_le hs.2 with h1 | h1
      · -- `s = 1`: the right piece is `{1}`
        filter_upwards [self_mem_nhdsWithin] with s' hs'
        have hs'1 : s' = s := le_antisymm (h1 ▸ hs'.2) hs'.1
        rw [hs'1]
      · obtain ⟨k, hkn, hk1, hk2⟩ := C.exists_block_right hs.1 h1
        obtain ⟨k', hk'n, hk'1, hk'2⟩ := C'.exists_block_right hs.1 h1
        have hsb : s ∈ Icc (C.t k) (C.t (k + 1)) := ⟨hk1, hk2.le⟩
        have hsb' : s ∈ Icc (C'.t k') (C'.t (k' + 1)) := ⟨hk'1, hk'2.le⟩
        have hγs : γ s ∈ C.U k ∩ C'.U k' :=
          ⟨C.covers k s hsb, C'.covers k' s hsb'⟩
        obtain ⟨W, hWo, hWpc, hγsW, hWsub⟩ := exists_isPathConnected_open_mem_nhds
          (((C.isOpen k).inter (C'.isOpen k')).mem_nhds hγs)
        have hconst : ∀ a ∈ W, C.F k a - C'.F k' a = C.F k (γ s) - C'.F k' (γ s) := by
          intro a ha
          exact isLocalPrimitiveOn_sub_const hWo (IsPathConnected.isConnected hWpc).isPreconnected
            ((C.prim k).mono fun w hw => (hWsub hw).1)
            ((C'.prim k').mono fun w hw => (hWsub hw).2) ha hγsW
        have hW' : γ ⁻¹' W ∈ 𝓝[Icc (0:ℝ) 1] s :=
          (hγ s hs).preimage_mem_nhdsWithin (hWo.mem_nhds hγsW)
        have hsubr : Icc s 1 ⊆ Icc (0:ℝ) 1 := fun u hu => ⟨hs.1.trans hu.1, hu.2⟩
        have hWr : γ ⁻¹' W ∈ 𝓝[Icc s 1] s := nhdsWithin_mono s hsubr hW'
        have hlt1 : ∀ᶠ s' in 𝓝[Icc s 1] s, s' < C.t (k + 1) :=
          eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hk2)
        have hlt2 : ∀ᶠ s' in 𝓝[Icc s 1] s, s' < C'.t (k' + 1) :=
          eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hk'2)
        filter_upwards [hWr, hlt1, hlt2, self_mem_nhdsWithin] with s' hWs' h1' h2' hs'mem
        have hs'b : s' ∈ Icc (C.t k) (C.t (k + 1)) := ⟨hk1.trans hs'mem.1, h1'.le⟩
        have hs'b' : s' ∈ Icc (C'.t k') (C'.t (k' + 1)) := ⟨hk'1.trans hs'mem.1, h2'.le⟩
        exact hstep hs hkn hk'n hsb hsb' s' hs'b hs'b' (hconst _ hWs')
  -- transfer to the subtype interval and conclude by preconnectedness
  haveI : PreconnectedSpace (Icc (0:ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  have hlc : IsLocallyConstant (fun p : Icc (0:ℝ) 1 => d p) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro p
    have h := hloc p p.2
    rw [← map_nhds_subtype_val] at h
    exact h
  have h01 : d 0 = d 1 := by
    have h := hlc.apply_eq_of_preconnectedSpace
      (⟨0, by norm_num⟩ : Icc (0:ℝ) 1) (⟨1, by norm_num⟩ : Icc (0:ℝ) 1)
    simpa using h
  have hz : d 0 = 0 := by
    rw [hd]
    simp only
    rw [C.partialValue_zero, C'.partialValue_zero, sub_self]
  have ho : d 1 = C.value - C'.value := by
    rw [hd]
    simp only
    rw [C.partialValue_one, C'.partialValue_one]
  have hfin : C.value - C'.value = 0 := by rw [← ho, ← h01, hz]
  exact sub_eq_zero.mp hfin

end Jacobians
