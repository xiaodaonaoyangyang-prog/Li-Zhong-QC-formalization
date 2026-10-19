/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# The holomorphic Poincaré lemma on simply connected surfaces (Wall A, final assembly)

`hasHolomorphicPrimitives`: on a simply connected compact Riemann surface every holomorphic
1-form has a global holomorphic primitive — the last input of the genus-0 backward headline
(`genus_zero_of_nonempty_homeo_sphere`).

Assembly of the discrete-continuation machinery:
* path-choice independence of `pathPrimValue` from simple connectivity (`paths_homotopic` +
  the monodromy theorem, with the `Path.Homotopy` totalized to `ℝ × ℝ` via `projIcc`);
* `F x := pathPrimValue η (somePath x₀ x).extend` is then well defined;
* near any point, `F = (local primitive) + constant`: appending a small in-disk path to the
  chosen path adds exactly the local-primitive increment (`pathPrimValue_trans_primitive_block` —
  the chain of the concatenation is the half-scaled chain plus one disk block);
* hence `F` is `MDifferentiable` with `dF = η` (the step-0 frame data transported along
  `Filter.EventuallyEq.mfderiv_eq`).

Reference: Forster, *Lectures on Riemann Surfaces*, §10.5; Miranda Ch. IV §1.
-/
import Jacobians.Monodromy.HolomorphicPrimitiveMonodromy
import Jacobians.SphereTopology.GenusZeroOfSphere
noncomputable section

open scoped Manifold ContDiff Topology unitInterval
open Set Metric Filter Function

namespace Jacobians


variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Transport of the path value along function equality -/

theorem pathPrimValue_congr (η : HolomorphicOneForms X) {γ₁ γ₂ : ℝ → X}
    (h₁ : ContinuousOn γ₁ (Icc 0 1)) (h₂ : ContinuousOn γ₂ (Icc 0 1)) (h : γ₁ = γ₂) :
    pathPrimValue η γ₁ h₁ = pathPrimValue η γ₂ h₂ := by
  subst h
  rfl

/-! ### Path-choice independence on a simply connected surface -/

/-- **Homotopic paths have equal path values** (monodromy + `projIcc`-totalization of the
`Path.Homotopy`). -/
theorem pathPrimValue_eq_of_homotopic (η : HolomorphicOneForms X) {x y : X}
    {p q : Path x y} (h : p.Homotopic q) :
    pathPrimValue η p.extend p.continuous_extend.continuousOn
      = pathPrimValue η q.extend q.continuous_extend.continuousOn := by
  obtain ⟨Hom⟩ := h
  set H : ℝ → ℝ → X := fun s t =>
    Hom (projIcc 0 1 zero_le_one s, projIcc 0 1 zero_le_one t) with hHdef
  have hH : Continuous (uncurry H) := by
    have : (uncurry H) = Hom.toContinuousMap ∘
        (Prod.map (projIcc 0 1 zero_le_one) (projIcc 0 1 zero_le_one)) := rfl
    rw [this]
    exact Hom.continuous.comp (continuous_projIcc.prodMap continuous_projIcc)
  have h0 : ∀ s, H s 0 = x := fun s => by
    rw [hHdef]
    simp only [projIcc_left]
    exact Hom.source _
  have h1 : ∀ s, H s 1 = y := fun s => by
    rw [hHdef]
    simp only [projIcc_right]
    exact Hom.target _
  have hmono := pathPrimValue_eq_of_homotopy η hH h0 h1
  have hp : H 0 = p.extend := by
    funext t
    rw [hHdef]
    simp only [projIcc_left]
    exact Hom.apply_zero _
  have hq : H 1 = q.extend := by
    funext t
    rw [hHdef]
    simp only [projIcc_right]
    exact Hom.apply_one _
  calc pathPrimValue η p.extend p.continuous_extend.continuousOn
      = pathPrimValue η (H 0) _ := pathPrimValue_congr η _ _ hp.symm
    _ = pathPrimValue η (H 1) _ := hmono
    _ = pathPrimValue η q.extend q.continuous_extend.continuousOn :=
        pathPrimValue_congr η _ _ hq

/-! ### The concatenation identity for a single in-disk block -/

/-- Evaluating the extension of a concatenation, left half. -/
theorem trans_extend_left {X : Type*} [TopologicalSpace X] {x₀ x y : X}
    (p : Path x₀ x) (q : Path x y) {s : ℝ}
    (h0 : 0 ≤ s) (h2 : s ≤ 1 / 2) :
    (p.trans q).extend s = p.extend (2 * s) := by
  have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨h0, h2.trans (by norm_num)⟩
  have h2s : 2 * s ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  rw [Path.extend_apply _ hs1, Path.extend_apply _ h2s, Path.trans_apply,
    dif_pos (show ((⟨s, hs1⟩ : I) : ℝ) ≤ 1 / 2 from h2)]

/-- Evaluating the extension of a concatenation, right half. -/
theorem trans_extend_right {X : Type*} [TopologicalSpace X] {x₀ x y : X}
    (p : Path x₀ x) (q : Path x y) {s : ℝ}
    (h2 : 1 / 2 < s) (h1 : s ≤ 1) :
    (p.trans q).extend s = q.extend (2 * s - 1) := by
  have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨by linarith, h1⟩
  have h2s : 2 * s - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  rw [Path.extend_apply _ hs1, Path.extend_apply _ h2s, Path.trans_apply,
    dif_neg (not_le.mpr (show (1 / 2 : ℝ) < ((⟨s, hs1⟩ : I) : ℝ) from h2))]

/-- **The in-disk concatenation identity**: appending a path that stays inside a primitive
disk `(B, G)` adds exactly the primitive increment `G y − G x` to the path value.  (The chain
for the concatenation is the half-scaled chain of `p` plus the single block `(B, G)`.) -/
theorem pathPrimValue_trans_primitive_block (η : HolomorphicOneForms X) {x₀ x y : X}
    (p : Path x₀ x) {B : Set X} {G : X → ℂ} (hBo : IsOpen B)
    (hG : IsLocalPrimitiveOn η G B) (q : Path x y) (hq : ∀ τ : I, q τ ∈ B) :
    pathPrimValue η (p.trans q).extend (p.trans q).continuous_extend.continuousOn
      = pathPrimValue η p.extend p.continuous_extend.continuousOn + (G y - G x) := by
  classical
  obtain ⟨C⟩ := exists_primitiveChain η (γ := p.extend) p.continuous_extend.continuousOn
  -- the in-disk endpoints
  have hxB : x ∈ B := by
    have := hq 0
    rwa [q.source] at this
  have hyB : y ∈ B := by
    have := hq 1
    rwa [q.target] at this
  have hqB : ∀ s : ℝ, q.extend s ∈ B := fun s => by
    by_cases h0 : s ≤ 0
    · rw [Path.extend_of_le_zero _ h0]; exact hxB
    by_cases h1 : 1 ≤ s
    · rw [Path.extend_of_one_le _ h1]; exact hyB
    · rw [Path.extend_apply _ ⟨le_of_not_ge h0, le_of_not_ge h1⟩]; exact hq _
  -- the concatenated chain: half-scaled `C` plus one `(B, G)` block
  set Ct : PrimitiveChain η (p.trans q).extend :=
    ⟨C.n + 1,
      fun k => if k ≤ C.n then C.t k / 2 else 1,
      by
        show (if 0 ≤ C.n then C.t 0 / 2 else 1) = 0
        rw [if_pos (Nat.zero_le C.n), C.t_zero]
        norm_num,
      fun k hk => by
        show (if k ≤ C.n then C.t k / 2 else 1) = 1
        rw [if_neg (by omega)],
      by
        intro a b hab
        show (if a ≤ C.n then C.t a / 2 else 1) ≤ (if b ≤ C.n then C.t b / 2 else 1)
        by_cases hb : b ≤ C.n
        · rw [if_pos (hab.trans hb), if_pos hb]
          have := C.mono hab
          linarith
        · rw [if_neg hb]
          by_cases ha : a ≤ C.n
          · rw [if_pos ha]
            have := C.t_le_one a
            linarith
          · rw [if_neg ha],
      fun k => if k < C.n then C.U k else B,
      fun k => if k < C.n then C.F k else G,
      fun k => by
        show IsOpen (if k < C.n then C.U k else B)
        by_cases hk : k < C.n
        · rw [if_pos hk]; exact C.isOpen k
        · rw [if_neg hk]; exact hBo,
      fun k => by
        show IsLocalPrimitiveOn η (if k < C.n then C.F k else G) (if k < C.n then C.U k else B)
        by_cases hk : k < C.n
        · rw [if_pos hk, if_pos hk]; exact C.prim k
        · rw [if_neg hk, if_neg hk]; exact hG,
      by
        intro k s hs
        show (p.trans q).extend s ∈ (if k < C.n then C.U k else B)
        have hs' : s ∈ Icc (if k ≤ C.n then C.t k / 2 else 1)
            (if k + 1 ≤ C.n then C.t (k + 1) / 2 else 1) := hs
        by_cases hk : k < C.n
        · rw [if_pos hk]
          rw [if_pos hk.le, if_pos (Nat.succ_le_of_lt hk)] at hs'
          have h0s : 0 ≤ s := (by linarith [C.t_nonneg k] : (0:ℝ) ≤ C.t k / 2).trans hs'.1
          have h2s : s ≤ 1 / 2 := hs'.2.trans (by linarith [C.t_le_one (k + 1)])
          rw [trans_extend_left p q h0s h2s]
          exact C.covers k (2 * s) ⟨by linarith [hs'.1], by linarith [hs'.2]⟩
        · rw [if_neg hk]
          push Not at hk
          rcases Nat.lt_or_ge k (C.n + 1) with hk1 | hk1
          · -- the single `(B, G)` block `[1/2, 1]`
            have hkeq : k = C.n := by omega
            subst hkeq
            rw [if_pos le_rfl, C.t_stab C.n le_rfl, if_neg (by omega)] at hs'
            rcases eq_or_lt_of_le hs'.1 with heq | hlt
            · rw [← heq, trans_extend_left p q (by norm_num) (by norm_num)]
              have h21 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
              rw [h21, Path.extend_one]
              exact hxB
            · rw [trans_extend_right p q hlt hs'.2]
              exact hqB _
          · -- degenerate blocks beyond stabilization
            rw [if_neg (by omega), if_neg (by omega)] at hs'
            have hseq : s = 1 := le_antisymm hs'.2 hs'.1
            rw [hseq, trans_extend_right p q (by norm_num) le_rfl]
            have h21 : (2 : ℝ) * 1 - 1 = 1 := by norm_num
            rw [h21, Path.extend_one]
            exact hyB⟩ with hCt
  -- evaluate the two values
  rw [pathPrimValue_eq η _ Ct, pathPrimValue_eq η _ C]
  have hval : Ct.value
      = (∑ k ∈ Finset.range C.n,
          (C.F k (p.extend (C.t (k + 1))) - C.F k (p.extend (C.t k)))) + (G y - G x) := by
    rw [show Ct.value = ∑ k ∈ Finset.range (C.n + 1),
        (Ct.F k ((p.trans q).extend (Ct.t (k + 1))) - Ct.F k ((p.trans q).extend (Ct.t k)))
      from rfl, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k < C.n := Finset.mem_range.mp hk
      have hFk : Ct.F k = C.F k := if_pos hkn
      have htk : Ct.t k = C.t k / 2 := if_pos hkn.le
      have htk1 : Ct.t (k + 1) = C.t (k + 1) / 2 := if_pos (Nat.succ_le_of_lt hkn)
      rw [hFk, htk, htk1,
        trans_extend_left p q (by linarith [C.t_nonneg (k + 1)])
          (by linarith [C.t_le_one (k + 1)]),
        trans_extend_left p q (by linarith [C.t_nonneg k]) (by linarith [C.t_le_one k])]
      have e1 : 2 * (C.t (k + 1) / 2) = C.t (k + 1) := by ring
      have e2 : 2 * (C.t k / 2) = C.t k := by ring
      rw [e1, e2]
    · have hFn : Ct.F C.n = G := if_neg (lt_irrefl C.n)
      have htn : Ct.t C.n = 1 / 2 := by
        rw [show Ct.t C.n = if C.n ≤ C.n then C.t C.n / 2 else 1 from rfl,
          if_pos le_rfl, C.t_stab C.n le_rfl]
      have htn1 : Ct.t (C.n + 1) = 1 := by
        rw [show Ct.t (C.n + 1) = if C.n + 1 ≤ C.n then C.t (C.n + 1) / 2 else 1 from rfl,
          if_neg (by omega)]
      rw [hFn, htn, htn1, trans_extend_right p q (by norm_num) le_rfl,
        trans_extend_left p q (by norm_num) le_rfl]
      have e1 : (2 : ℝ) * 1 - 1 = 1 := by norm_num
      have e2 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
      rw [e1, e2, Path.extend_one, Path.extend_one]
  rw [hval]
  rfl

/-! ### The holomorphic Poincaré lemma -/

/-- **`HasHolomorphicPrimitives` holds** (the monodromy theorem / holomorphic Poincaré lemma):
on a simply connected compact Riemann surface, every holomorphic 1-form has a global
holomorphic primitive. -/
theorem hasHolomorphicPrimitives : HasHolomorphicPrimitives X := by
  intro hSC η
  haveI : LocPathConnectedSpace X := ChartedSpace.locPathConnectedSpace (H := ℂ) X
  haveI : PathConnectedSpace X := PathConnectedSpace.of_locPathConnectedSpace
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  -- the global primitive: the path value from the basepoint
  set F : X → ℂ := fun z =>
    pathPrimValue η (PathConnectedSpace.somePath x₀ z).extend
      (PathConnectedSpace.somePath x₀ z).continuous_extend.continuousOn with hFdef
  -- the local identity: on a primitive disk, `F` is the local primitive up to a constant
  have hkey : ∀ (B : Set X) (G : X → ℂ), IsOpen B → IsPathConnected B →
      IsLocalPrimitiveOn η G B → ∀ x ∈ B, ∀ z ∈ B, F z = G z + (F x - G x) := by
    intro B G hBo hBpc hG x hxB z hzB
    -- an in-disk path from `x` to `z`
    obtain hjoin := hBpc.joinedIn x hxB z hzB
    set q : Path x z := hjoin.somePath with hqdef
    have hqB : ∀ τ : I, q τ ∈ B := hjoin.somePath_mem
    -- the concatenation is homotopic to the chosen path to `z` (simple connectivity)
    have hhom : ((PathConnectedSpace.somePath x₀ x).trans q).Homotopic
        (PathConnectedSpace.somePath x₀ z) := SimplyConnectedSpace.paths_homotopic _ _
    have h1 := pathPrimValue_eq_of_homotopic η hhom
    have h2 := pathPrimValue_trans_primitive_block η (PathConnectedSpace.somePath x₀ x)
      hBo hG q hqB
    rw [hFdef]
    simp only
    rw [← h1, h2]
    ring
  -- conclude: `F` is differentiable with `dF = η` at every point
  refine ⟨F, ?_, ?_⟩
  · intro x
    obtain ⟨B, G, hBo, hxB, hBpc, hG⟩ := exists_isLocalPrimitiveOn η x
    have hloc : F =ᶠ[𝓝 x] (G + fun _ => (F x - G x)) := by
      filter_upwards [hBo.mem_nhds hxB] with z hz
      exact hkey B G hBo hBpc hG x hxB z hz
    exact ((hG x hxB).1.add mdifferentiableAt_const).congr_of_eventuallyEq hloc
  · intro x v
    obtain ⟨B, G, hBo, hxB, hBpc, hG⟩ := exists_isLocalPrimitiveOn η x
    have hloc : F =ᶠ[𝓝 x] (G + fun _ => (F x - G x)) := by
      filter_upwards [hBo.mem_nhds hxB] with z hz
      exact hkey B G hBo hBpc hG x hxB z hz
    have hmf : mfderiv 𝓘(ℂ) 𝓘(ℂ) F x
        = mfderiv 𝓘(ℂ) 𝓘(ℂ) (G + fun _ => (F x - G x)) x := hloc.mfderiv_eq
    have hmfG : mfderiv 𝓘(ℂ) 𝓘(ℂ) (G + fun _ => (F x - G x)) x
        = mfderiv 𝓘(ℂ) 𝓘(ℂ) G x := by
      rw [mfderiv_add (hG x hxB).1 mdifferentiableAt_const, mfderiv_const]
      exact add_zero _
    rw [hmf, hmfG]
    exact (hG x hxB).2 v

end Jacobians
