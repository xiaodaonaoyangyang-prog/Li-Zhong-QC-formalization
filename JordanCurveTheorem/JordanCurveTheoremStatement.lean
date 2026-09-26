/-
Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL
-/
import JordanCurveTheorem.SectionDD_JordanCurveTheorem

/-!
# Jordan Curve Theorem — Standalone Statement

This file contains the final Jordan Curve Theorem statement together with
every custom (non-Mathlib) definition it depends on, so that the statement
can be audited in isolation.

The only import beyond Mathlib is the file that contains the proof.
-/

open Set EuclideanSpace AddCircle Function

namespace JordanCurveTheorem

/-! ## Custom definitions (not in Mathlib)

### `E2` — The Euclidean plane

```
abbrev E2 := EuclideanSpace ℝ (Fin 2)
```

### `E2'` — Alias for `E2`

```
abbrev E2' := E2
```

### `IsSimpleClosedCurve` — Simple closed curve (Jordan curve)

```
def IsSimpleClosedCurve (C : Set E2') : Prop :=
  ∃ f : ℝ → E2',
    C = f '' Icc 0 1 ∧
    Continuous f ∧
    Set.InjOn f (Ico 0 1) ∧
    f 0 = f 1
```

A simple closed curve in ℝ² is the image of a continuous function
`f : [0,1] → ℝ²` that is injective on `[0,1)` and satisfies `f(0) = f(1)`.

### `jordan_curve_theorem`

```
theorem jordan_curve_theorem {C : Set (EuclideanSpace ℝ (Fin 2))}
    (hC : IsSimpleClosedCurve C) :
    ∃ A B : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen A ∧ IsOpen B ∧
      IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      A ∪ B ∪ C = Set.univ
```

Every simple closed curve `C` in the Euclidean plane separates the
plane into exactly two connected open regions whose union with `C` is
the whole plane.
-/

/-! ## Type-level verification

The following checks confirm that the definitions unfold to exactly
what we expect, with no hidden axioms beyond Mathlib. -/

-- E2' is definitionally EuclideanSpace ℝ (Fin 2)
example : E2' = EuclideanSpace ℝ (Fin 2) := rfl

-- The theorem, fully expanded with no custom type aliases:
example : ∀ C : Set (EuclideanSpace ℝ (Fin 2)),
    IsSimpleClosedCurve C →
    ∃ A B : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen A ∧ IsOpen B ∧
      IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      A ∪ B ∪ C = Set.univ :=
  fun _ hC => jordan_curve_theorem hC

/-- Alternative characterization of a simple closed curve as a subset of ℝ² that is
    homeomorphic to the unit circle (i.e., `UnitAddCircle`). -/
def IsSimpleClosedCurve2 (C : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  Nonempty (C ≃ₜ UnitAddCircle)

example : ∀ C, IsSimpleClosedCurve2 C = IsSimpleClosedCurve C := by
  intro C; apply propext; constructor
  · -- ⇒: Nonempty (C ≃ₜ UnitAddCircle) → IsSimpleClosedCurve C
    rintro ⟨e⟩
    refine ⟨fun t => ↑(e.symm (↑t : UnitAddCircle)), ?_, ?_, ?_, ?_⟩
    · -- C = f '' Icc 0 1
      ext c; simp only [mem_image]; constructor
      · intro hc
        set q := e ⟨c, hc⟩; have ht := (equivIco 1 0 q).2
        refine ⟨(equivIco 1 0 q).1, Ico_subset_Icc_self (by simpa using ht), ?_⟩
        change (e.symm (↑(equivIco 1 0 q).1 : UnitAddCircle) : E2') = c
        rw [(equivIco 1 0).injective ((equivIco_coe_eq ht).trans rfl)]
        exact congrArg Subtype.val (e.symm_apply_apply ⟨c, hc⟩)
      · rintro ⟨t, _, rfl⟩; exact (e.symm (↑t : UnitAddCircle)).2
    · exact continuous_subtype_val.comp (e.symm.continuous.comp (AddCircle.continuous_mk' 1))
    · -- InjOn f (Ico 0 1)
      intro a ha b hb hab
      exact (coe_eq_coe_iff_of_mem_Ico ⟨ha.1, by linarith [ha.2]⟩ ⟨hb.1, by linarith [hb.2]⟩).mp
        (e.symm.injective (Subtype.val_injective hab))
    · -- f 0 = f 1
      change (e.symm (↑(0 : ℝ) : UnitAddCircle) : E2') =
        (e.symm (↑(1 : ℝ) : UnitAddCircle) : E2')
      exact congrArg (fun x => (e.symm x : E2')) (by simp [coe_period])
  · -- ⇐: IsSimpleClosedCurve C → Nonempty (C ≃ₜ UnitAddCircle)
    rintro ⟨f, hCf, hcont, hinj, hf01⟩
    have hg_cont := liftIco_zero_continuous hf01 hcont.continuousOn
    have hg_inj : Injective (liftIco 1 0 f) := by
      intro x y hxy
      have hx := (equivIco 1 0 x).2; have hy := (equivIco 1 0 y).2
      simp only [zero_add, mem_Ico] at hx hy
      exact (equivIco 1 0).injective (Subtype.val_injective (hinj hx hy hxy))
    have hg_range : range (liftIco 1 0 f) = C := by
      rw [hCf]; ext c; constructor
      · rintro ⟨x, rfl⟩
        have hx := (equivIco 1 0 x).2; simp only [zero_add, mem_Ico] at hx
        exact ⟨_, Ico_subset_Icc_self hx, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        by_cases ht1 : t = 1
        · exact ⟨↑(0 : ℝ), by
            rw [liftIco_coe_apply (by norm_num : (0:ℝ) ∈ Ico 0 (0+1)), ht1, hf01]⟩
        · exact ⟨↑t, liftIco_coe_apply ⟨ht.1, by linarith [lt_of_le_of_ne ht.2 ht1]⟩⟩
    have hmem : ∀ x, liftIco 1 0 f x ∈ C := fun x => hg_range ▸ mem_range_self x
    let g' : UnitAddCircle → C := fun x => ⟨_, hmem x⟩
    have hg'_cont : Continuous g' := continuous_induced_rng.mpr hg_cont
    exact ⟨(Continuous.homeoOfEquivCompactToT2
      (f := .ofBijective g' ⟨fun x y h => hg_inj (congrArg Subtype.val h),
        fun ⟨c, hc⟩ => (hg_range ▸ hc).elim fun x hx => ⟨x, Subtype.val_injective hx⟩⟩)
      hg'_cont).symm⟩

end JordanCurveTheorem
