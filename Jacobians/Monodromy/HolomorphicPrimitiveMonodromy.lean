/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# The monodromy theorem (Wall A, step 2 — homotopy invariance of the path value)

The chain-independent path value `pathPrimValue η γ` (the discrete `∫_γ η`) is invariant under
endpoint-fixed homotopies: for a continuous `H : ℝ → ℝ → X` with `H s 0 = x₀`, `H s 1 = x₁`
for all `s`, the value along `H s` is constant in `s`.

Proof: fix `s₀` and a chain for `H s₀`; by compactness ("tube"), for `s` near `s₀` the SAME
partition/primitive data is a chain for `H s` (`IsCompact.eventually_forall_of_forall_eventually`).
Abel summation rewrites the value as boundary terms (fixed, the endpoints are constant in `s`)
minus interior-node terms `(Fₖ − Fₖ₋₁)(H s (tₖ))`, each locally constant in `s` because two
primitives differ by a constant on a path-connected neighbourhood of the node (step-0 rigidity).
So the value is a locally constant function of `s` on ℝ, hence constant.

Reference: Forster, *Lectures on Riemann Surfaces*, §10.5; the classical monodromy theorem of
Cauchy theory.
-/
import Jacobians.Monodromy.HolomorphicPrimitiveChain

noncomputable section

open scoped Manifold ContDiff Topology
open Set Metric Filter Function

namespace Jacobians


variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Abel summation for the telescoping value -/

/-- **Abel summation**: a telescoping sum with block-dependent summands equals the boundary
terms minus the interior-node defects. -/
theorem sum_telescope_abel {n : ℕ} (hn : 0 < n) (G : ℕ → ℕ → ℂ) :
    ∑ k ∈ Finset.range n, (G k (k + 1) - G k k)
      = G (n - 1) n - G 0 0 - ∑ k ∈ Finset.Ico 1 n, (G k k - G (k - 1) k) := by
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · rw [Finset.sum_range_succ, ih hm,
        Finset.sum_Ico_succ_top (by omega : 1 ≤ m) (fun k => G k k - G (k - 1) k)]
      have h1 : m + 1 - 1 = m := by omega
      rw [h1]
      ring

/-! ### The path value -/

/-- **The path value** `∫_γ η` in its discrete incarnation: the value of any primitive chain
along `γ` (chain-independent by `value_eq_of_chains`). -/
def pathPrimValue (η : HolomorphicOneForms X) (γ : ℝ → X)
    (hγ : ContinuousOn γ (Icc 0 1)) : ℂ :=
  (exists_primitiveChain η hγ).some.value

theorem pathPrimValue_eq (η : HolomorphicOneForms X) {γ : ℝ → X}
    (hγ : ContinuousOn γ (Icc 0 1)) (C : PrimitiveChain η γ) :
    pathPrimValue η γ hγ = C.value :=
  PrimitiveChain.value_eq_of_chains hγ _ C

/-! ### The monodromy theorem -/

/-- **The monodromy theorem**: the path value is invariant under endpoint-fixed continuous
homotopies (stated over all of `ℝ` — the homotopy is totalized, e.g. via `projIcc`). -/
theorem pathPrimValue_eq_of_homotopy (η : HolomorphicOneForms X) {H : ℝ → ℝ → X}
    (hH : Continuous (uncurry H)) {x₀ x₁ : X}
    (h0 : ∀ s, H s 0 = x₀) (h1 : ∀ s, H s 1 = x₁) :
    pathPrimValue η (H 0) ((hH.comp (continuous_const.prodMk continuous_id)).continuousOn)
      = pathPrimValue η (H 1)
        ((hH.comp (continuous_const.prodMk continuous_id)).continuousOn) := by
  classical
  -- the per-parameter continuity and value function
  have hHs : ∀ s : ℝ, Continuous (H s) := fun s =>
    hH.comp (continuous_const.prodMk continuous_id)
  set v : ℝ → ℂ := fun s => pathPrimValue η (H s) (hHs s).continuousOn with hv
  -- `v` is locally constant on ℝ
  have hloc : ∀ s₀ : ℝ, ∀ᶠ s in 𝓝 s₀, v s = v s₀ := by
    intro s₀
    obtain ⟨C⟩ := exists_primitiveChain η (hHs s₀).continuousOn
    -- the tube: nearby parameters keep every block inside its primitive open
    have htube : ∀ᶠ s in 𝓝 s₀, ∀ k ∈ Finset.range C.n,
        ∀ τ ∈ Icc (C.t k) (C.t (k + 1)), H s τ ∈ C.U k := by
      rw [eventually_all_finset]
      intro k _
      refine IsCompact.eventually_forall_of_forall_eventually isCompact_Icc fun τ hτ => ?_
      have hmem : H s₀ τ ∈ C.U k := C.covers k τ hτ
      have hcont : ContinuousAt (uncurry H) (s₀, τ) := hH.continuousAt
      exact hcont.preimage_mem_nhds ((C.isOpen k).mem_nhds hmem)
    -- the interior-node constancy data (proof-independent `W` for the finite conjunction)
    have hnode : ∀ k, ∃ W : Set X, k ∈ Finset.Ico 1 C.n →
        IsOpen W ∧ H s₀ (C.t k) ∈ W ∧
        (∀ a ∈ W, C.F k a - C.F (k - 1) a
          = C.F k (H s₀ (C.t k)) - C.F (k - 1) (H s₀ (C.t k))) := by
      intro k
      by_cases hk : k ∈ Finset.Ico 1 C.n
      swap
      · exact ⟨∅, fun h => absurd h hk⟩
      obtain ⟨hk1, hkn⟩ := Finset.mem_Ico.mp hk
      have hmem1 : H s₀ (C.t k) ∈ C.U (k - 1) := by
        have := C.covers (k - 1) (C.t k)
          ⟨C.mono (Nat.sub_le k 1), by rw [Nat.sub_add_cancel hk1]⟩
        exact this
      have hmem2 : H s₀ (C.t k) ∈ C.U k :=
        C.covers k (C.t k) ⟨le_rfl, C.mono (Nat.le_succ k)⟩
      obtain ⟨W, hWo, hWpc, hxW, hWsub⟩ := exists_isPathConnected_open_mem_nhds
        (((C.isOpen k).inter (C.isOpen (k - 1))).mem_nhds ⟨hmem2, hmem1⟩)
      refine ⟨W, fun _ => ⟨hWo, hxW, fun a ha => ?_⟩⟩
      exact isLocalPrimitiveOn_sub_const hWo (IsPathConnected.isConnected hWpc).isPreconnected
        ((C.prim k).mono fun w hw => (hWsub hw).1)
        ((C.prim (k - 1)).mono fun w hw => (hWsub hw).2) ha hxW
    choose W hW using hnode
    -- nearby parameters keep every node inside its constancy disk
    have hnodes : ∀ᶠ s in 𝓝 s₀, ∀ k ∈ Finset.Ico 1 C.n, H s (C.t k) ∈ W k := by
      rw [eventually_all_finset]
      intro k hk
      have hcont : Continuous fun s => H s (C.t k) :=
        hH.comp (continuous_id.prodMk continuous_const)
      exact hcont.continuousAt.preimage_mem_nhds
        (((hW k hk).1).mem_nhds (hW k hk).2.1)
    filter_upwards [htube, hnodes] with s hs hns
    -- the same data is a chain for `H s`
    set Cs : PrimitiveChain η (H s) :=
      ⟨C.n, C.t, C.t_zero, C.t_stab, C.mono, C.U, C.F, C.isOpen, C.prim,
        fun k τ hτ => by
          rcases Nat.lt_or_ge k C.n with hkn | hkn
          · exact hs k (Finset.mem_range.mpr hkn) τ hτ
          · -- beyond the stabilization the block is the fixed endpoint `x₁`
            have ht1 : C.t k = 1 := C.t_stab k hkn
            have ht2 : C.t (k + 1) = 1 := C.t_stab (k + 1) (hkn.trans (Nat.le_succ k))
            have hτ1 : τ = 1 := le_antisymm (ht2 ▸ hτ.2) (ht1 ▸ hτ.1)
            have h1s : H s τ = H s₀ τ := by rw [hτ1, h1 s, h1 s₀]
            rw [h1s]
            exact C.covers k τ hτ⟩ with hCs
    -- evaluate both values by Abel summation
    have hvals : v s = Cs.value := pathPrimValue_eq η (hHs s).continuousOn Cs
    have hval₀ : v s₀ = C.value := pathPrimValue_eq η (hHs s₀).continuousOn C
    rw [hvals, hval₀]
    have habel_s := sum_telescope_abel C.n_pos (fun k j => C.F k (H s (C.t j)))
    have habel₀ := sum_telescope_abel C.n_pos (fun k j => C.F k (H s₀ (C.t j)))
    have hCsval : Cs.value = ∑ k ∈ Finset.range C.n,
        (C.F k (H s (C.t (k + 1))) - C.F k (H s (C.t k))) := rfl
    have hCval : C.value = ∑ k ∈ Finset.range C.n,
        (C.F k (H s₀ (C.t (k + 1))) - C.F k (H s₀ (C.t k))) := rfl
    rw [hCsval, hCval, habel_s, habel₀]
    -- boundary terms are parameter-independent (fixed endpoints)
    have hb1 : H s (C.t C.n) = H s₀ (C.t C.n) := by
      rw [C.t_stab C.n le_rfl, h1 s, h1 s₀]
    have hb0 : H s (C.t 0) = H s₀ (C.t 0) := by
      rw [C.t_zero, h0 s, h0 s₀]
    rw [hb1, hb0]
    -- node terms are equal via the constancy disks
    have hsum : ∑ k ∈ Finset.Ico 1 C.n,
        (C.F k (H s (C.t k)) - C.F (k - 1) (H s (C.t k)))
        = ∑ k ∈ Finset.Ico 1 C.n,
          (C.F k (H s₀ (C.t k)) - C.F (k - 1) (H s₀ (C.t k))) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [(hW k hk).2.2 _ (hns k hk), (hW k hk).2.2 _ (hW k hk).2.1]
    rw [hsum]
  -- locally constant on the (preconnected) line ⟹ constant
  have hlc : IsLocallyConstant v := IsLocallyConstant.iff_eventually_eq v |>.mpr hloc
  exact hlc.apply_eq_of_preconnectedSpace 0 1

end Jacobians
