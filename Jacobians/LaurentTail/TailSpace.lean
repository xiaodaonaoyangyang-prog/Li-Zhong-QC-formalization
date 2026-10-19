/-
  Laurent tail divisors `𝒯[D](X)` and their truncation maps (Miranda Ch. VI §2, pp. 178–181).

  A *Laurent tail divisor* assigns to finitely many points `p` a Laurent *polynomial* tail in the
  canonical coordinate at `p`.  We represent all tails at once by one flat `Finsupp`

      `TailSpace X := (X × ℤ) →₀ ℂ`,

  the entry at `(p, n)` being the coefficient of `(z − c_p)^n`.  The Miranda space `𝒯[D](X)`
  (tails with all terms of degree `< −D(p)`) is the Mathlib submodule `Finsupp.supported` on the
  degree window `{(p, n) | n < −D(p)}` (`tailSubspace`).  This file is pure Finsupp combinatorics
  (no manifold structure on `X`):

  * `tailTruncate D₁ D₂ : 𝒯[D₁] →ₗ 𝒯[D₂]` — the truncation `t^{D₁}_{D₂}` (kill all terms of
    degree `≥ −D₂(p)`), surjective when `D₁ ≤ D₂`;
  * `finrank_ker_tailTruncate` — **the monomial count** (Miranda p. 181):
    `dim ker t^{D₁}_{D₂} = deg D₂ − deg D₁` (the kernel is spanned by the monomials in the finite
    window `−D₂(p) ≤ n < −D₁(p)`);
  * `tailCutoff A Z` — a divisor `B ≥ A` with `t^{A}_{B} Z = 0` (every tail dies under a deep
    enough truncation; used for Miranda Lemma 2.6).
-/
import Jacobians.Meromorphic.Abel
open Module

namespace Jacobians.LaurentTail

open Jacobians

variable {X : Type*}

/-! ### The tail space and its degree-window subspaces -/

/-- The ambient space of **Laurent tails** on `X`: finitely supported families of coefficients,
the entry at `(p, n)` being the coefficient of `(z − c_p)^n` in the tail at `p`. -/
abbrev TailSpace (X : Type*) : Type _ := (X × ℤ) →₀ ℂ

/-! Shortcut instances pinning ONE derivation of the algebraic structure on `TailSpace X`.
Without these, `Submodule` types over the Finsupp bake in the synthesized
`AddCommMonoid ((X × ℤ) →₀ ℂ)` (whose inner `AddCommMonoid ℂ` comes through the
`NonUnitalNonAssocSemiring` chain), while `Submodule.addCommGroup` on a *nested* submodule
(e.g. `ker (tailTruncate …)`) derives it by projection from `AddCommGroup` (through
`Complex.addCommGroup`) — defeq but not syntactically equal, so instance resolution fails
(the recurring ℂ instance-diamond, here in Finsupp form).  Pinning the monoid to the
projection of the pinned group makes every later search resolve to the same constants. -/

noncomputable instance (priority := 1100) instTailSpaceAddCommGroup :
    AddCommGroup (TailSpace X) := Finsupp.instAddCommGroup

noncomputable instance (priority := 1100) instTailSpaceAddCommMonoid :
    AddCommMonoid (TailSpace X) := instTailSpaceAddCommGroup.toAddCommMonoid

noncomputable instance (priority := 1100) instTailSpaceModule :
    Module ℂ (TailSpace X) := Finsupp.module (X × ℤ) ℂ

/-- The degree window of a divisor `D`: the index pairs `(p, n)` with `n < −D(p)`. -/
def tailDegreeSet (D : Divisor X) : Set (X × ℤ) := {q | q.2 < -(D q.1)}

theorem mem_tailDegreeSet {D : Divisor X} {q : X × ℤ} :
    q ∈ tailDegreeSet D ↔ q.2 < -(D q.1) := Iff.rfl

/-- **Miranda's `𝒯[D](X)`** — the space of Laurent tail divisors for `D`: tails whose terms all
have degree `< −D(p)`.  A `ℂ`-submodule of `TailSpace X` (`Finsupp.supported`). -/
noncomputable def tailSubspace (D : Divisor X) : Submodule ℂ (TailSpace X) :=
  Finsupp.supported ℂ ℂ (tailDegreeSet D)

theorem mem_tailSubspace_iff {D : Divisor X} {Z : TailSpace X} :
    Z ∈ tailSubspace D ↔ ∀ q : X × ℤ, ¬ q.2 < -(D q.1) → Z q = 0 :=
  Finsupp.mem_supported' ℂ Z

/-- The tail spaces are **antitone** in the divisor: a deeper cutoff (larger `D`) allows fewer
terms. -/
theorem tailSubspace_anti {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    tailSubspace (X := X) D₂ ≤ tailSubspace D₁ :=
  Finsupp.supported_mono fun q hq =>
    mem_tailDegreeSet.mpr (lt_of_lt_of_le (mem_tailDegreeSet.mp hq) (neg_le_neg (h q.1)))

/-! ### Truncation -/

/-- Truncation at depth `D` on the ambient tail space: kill all entries of degree `≥ −D(p)`
(`Finsupp.filter`, which is `ℂ`-linear). -/
noncomputable def truncateRaw (D : Divisor X) : TailSpace X →ₗ[ℂ] TailSpace X where
  toFun Z := Finsupp.filter (fun q => q.2 < -(D q.1)) Z
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

@[simp] theorem truncateRaw_apply (D : Divisor X) (Z : TailSpace X) (q : X × ℤ) :
    truncateRaw D Z q = if q.2 < -(D q.1) then Z q else 0 := rfl

theorem truncateRaw_mem_tailSubspace (D : Divisor X) (Z : TailSpace X) :
    truncateRaw D Z ∈ tailSubspace D := by
  rw [mem_tailSubspace_iff]
  intro q hq
  rw [truncateRaw_apply, if_neg hq]

/-- A tail already supported in the window of `D` is unchanged by truncation at `D`. -/
theorem truncateRaw_eq_self_of_mem {D : Divisor X} {Z : TailSpace X} (hZ : Z ∈ tailSubspace D) :
    truncateRaw D Z = Z :=
  (Finsupp.filter_eq_self_iff _ _).mpr fun q hq => by
    by_contra hcon
    exact hq (mem_tailSubspace_iff.mp hZ q hcon)

/-- **Miranda's truncation map `t^{D₁}_{D₂} : 𝒯[D₁] → 𝒯[D₂]`** — keep only the terms of degree
`< −D₂(p)`.  (Defined for any pair of divisors; it is surjective when `D₁ ≤ D₂`.) -/
noncomputable def tailTruncate (D₁ D₂ : Divisor X) :
    ↥(tailSubspace (X := X) D₁) →ₗ[ℂ] ↥(tailSubspace (X := X) D₂) :=
  (truncateRaw D₂).restrict fun Z _ => truncateRaw_mem_tailSubspace D₂ Z

@[simp] theorem tailTruncate_coe (D₁ D₂ : Divisor X) (Z : ↥(tailSubspace (X := X) D₁)) :
    (tailTruncate D₁ D₂ Z : TailSpace X) = truncateRaw D₂ (Z : TailSpace X) := rfl

/-- Truncation is **surjective** for `D₁ ≤ D₂` (a `D₂`-tail is in particular a `D₁`-tail, and is
fixed by the truncation). -/
theorem tailTruncate_surjective {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    Function.Surjective (tailTruncate (X := X) D₁ D₂) := by
  intro Z₂
  refine ⟨⟨(Z₂ : TailSpace X), tailSubspace_anti h Z₂.2⟩, Subtype.ext ?_⟩
  exact truncateRaw_eq_self_of_mem Z₂.2

/-! ### The kernel of truncation: the finite monomial window

The kernel of `t^{D₁}_{D₂}` consists of the tails supported in the finite window
`−D₂(p) ≤ n < −D₁(p)`; its dimension is the monomial count `∑_p (D₂(p) − D₁(p)) = deg D₂ − deg D₁`
(Miranda p. 181). -/

section Window

variable [DecidableEq X]

/-- The (finite) window of degrees killed by `t^{D₁}_{D₂}`: pairs `(p, n)` with
`−D₂(p) ≤ n < −D₁(p)`.  Nonempty windows force `p` into `supp D₁ ∪ supp D₂`. -/
noncomputable def windowFinset (D₁ D₂ : Divisor X) : Finset (X × ℤ) :=
  (D₁.support ∪ D₂.support).biUnion fun p =>
    (Finset.Ico (-(D₂ p)) (-(D₁ p))).image fun n => (p, n)

theorem mem_windowFinset {D₁ D₂ : Divisor X} {q : X × ℤ} :
    q ∈ windowFinset D₁ D₂ ↔ -(D₂ q.1) ≤ q.2 ∧ q.2 < -(D₁ q.1) := by
  obtain ⟨p, n⟩ := q
  simp only [windowFinset, Finset.mem_biUnion, Finset.mem_union, Finset.mem_image,
    Finset.mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨p', _, n', ⟨h1, h2⟩, rfl, rfl⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨p, ?_, n, ⟨h1, h2⟩, rfl, rfl⟩
    by_contra hcon
    rw [not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff] at hcon
    rw [hcon.1] at h2
    rw [hcon.2] at h1
    omega

/-- The monomial count: `#window = ∑_{p ∈ supp D₁ ∪ supp D₂} (D₂(p) − D₁(p))⁺`. -/
theorem card_windowFinset (D₁ D₂ : Divisor X) :
    (windowFinset D₁ D₂).card
      = ∑ p ∈ D₁.support ∪ D₂.support, (-(D₁ p) - -(D₂ p)).toNat := by
  rw [windowFinset, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.injEq _ _ _ _).mp hab |>.2),
      Int.card_Ico]
  · intro p _ p' _ hpp'
    simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_Ico]
    rintro _ ⟨n, _, rfl⟩ ⟨n', _, h⟩
    exact hpp' ((Prod.mk.injEq _ _ _ _).mp h).1.symm

end Window

/-- `finrank` of `Finsupp.supported` over (the coercion of) a `Finset`: the cardinality. -/
theorem finrank_supported_finset {α : Type*} (s : Finset α) :
    finrank ℂ ↥(Finsupp.supported ℂ ℂ (↑s : Set α)) = s.card := by
  rw [(Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ) (↑s : Set α)).finrank_eq,
    Module.finrank_finsupp_self]
  exact Fintype.card_coe s

instance finiteDimensional_supported_finset {α : Type*} (s : Finset α) :
    FiniteDimensional ℂ ↥(Finsupp.supported ℂ ℂ (↑s : Set α)) :=
  Module.Finite.equiv (Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ) (↑s : Set α)).symm

variable [DecidableEq X] in
/-- The kernel of `t^{D₁}_{D₂}` is exactly the window-supported tails, read inside `𝒯[D₁]`. -/
theorem ker_tailTruncate_eq (D₁ D₂ : Divisor X) :
    LinearMap.ker (tailTruncate (X := X) D₁ D₂)
      = (Finsupp.supported ℂ ℂ (↑(windowFinset D₁ D₂) : Set (X × ℤ))).comap
          (tailSubspace (X := X) D₁).subtype := by
  ext Z
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype, Finsupp.mem_supported']
  constructor
  · intro hker q hq
    rw [Finset.mem_coe, mem_windowFinset, not_and_or, not_le, not_lt] at hq
    rcases hq with hq | hq
    · -- the entry is killed by the truncation, which is zero
      have := congrArg (fun (W : ↥(tailSubspace (X := X) D₂)) => (W : TailSpace X) q) hker
      simpa [truncateRaw_apply, if_pos hq] using this
    · -- the entry is outside the `D₁` window, where `Z` is supported
      exact mem_tailSubspace_iff.mp Z.2 q (not_lt.mpr hq)
  · intro hsupp
    apply Subtype.ext
    rw [tailTruncate_coe]
    ext q
    rw [truncateRaw_apply]
    split_ifs with hq
    · -- degree `< −D₂(p)` lies outside the window, so `Z` vanishes there
      refine (hsupp q ?_).trans rfl
      rw [Finset.mem_coe, mem_windowFinset, not_and_or, not_le]
      exact Or.inl hq
    · rfl

/-- The kernel of `t^{D₁}_{D₂}` is linearly equivalent to the window-supported tail space. -/
noncomputable def kerTailTruncateEquiv [DecidableEq X] (D₁ D₂ : Divisor X) :
    ↥(LinearMap.ker (tailTruncate (X := X) D₁ D₂))
      ≃ₗ[ℂ] ↥(Finsupp.supported ℂ ℂ (↑(windowFinset D₁ D₂) : Set (X × ℤ))) :=
  (LinearEquiv.ofEq _ _ (ker_tailTruncate_eq D₁ D₂)).trans
    (Submodule.comapSubtypeEquivOfLe
      (Finsupp.supported_mono fun _q hq =>
        mem_tailDegreeSet.mpr (mem_windowFinset.mp hq).2))

instance finiteDimensional_ker_tailTruncate (D₁ D₂ : Divisor X) :
    FiniteDimensional ℂ ↥(LinearMap.ker (tailTruncate (X := X) D₁ D₂)) := by
  classical
  exact Module.Finite.equiv (kerTailTruncateEquiv D₁ D₂).symm

/-- **The monomial count (Miranda Ch. VI, proof of Lemma 2.3, p. 181):** for `D₁ ≤ D₂`,

    `dim ker t^{D₁}_{D₂} = deg D₂ − deg D₁`. -/
theorem finrank_ker_tailTruncate {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    (finrank ℂ ↥(LinearMap.ker (tailTruncate (X := X) D₁ D₂)) : ℤ)
      = Divisor.deg X D₂ - Divisor.deg X D₁ := by
  classical
  rw [(kerTailTruncateEquiv D₁ D₂).finrank_eq, finrank_supported_finset, card_windowFinset]
  -- `∑ (D₂ − D₁)⁺ = ∑ D₂ − ∑ D₁` over the union of the supports
  rw [Nat.cast_sum]
  have hdeg : ∀ D : Divisor X, D.support ⊆ D₁.support ∪ D₂.support →
      Divisor.deg X D = ∑ p ∈ D₁.support ∪ D₂.support, D p := by
    intro D hsub
    rw [show Divisor.deg X D = Finsupp.degree D from rfl, Finsupp.degree_apply]
    exact Finset.sum_subset hsub fun p _ hp => Finsupp.notMem_support_iff.mp hp
  rw [hdeg D₁ Finset.subset_union_left, hdeg D₂ Finset.subset_union_right,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Int.toNat_of_nonneg (by have := h p; omega)]
  omega

/-! ### Deep truncations kill any given tail (towards Miranda Lemma 2.6)

Given a tail `Z` and a base divisor `A`, the divisor `tailCutoff A Z ≥ A` truncates `Z` to zero:
its coefficient at `p` exceeds `−n` for every `(p, n)` in the support of `Z`. -/

/-- A divisor `B ≥ A` deep enough that `t^{A}_{B} Z = 0`: add to `A` the (effective) divisor
`∑_{(p,n) ∈ supp Z} (−n − A(p))⁺ · p`. -/
noncomputable def tailCutoff (A : Divisor X) (Z : TailSpace X) : Divisor X :=
  A + ∑ q ∈ Z.support, Finsupp.single q.1 ((-q.2 - A q.1).toNat : ℤ)

/-- Evaluations of effective (`toNat`-coefficient) singles are nonnegative. -/
private theorem single_toNat_apply_nonneg (a : X) (v : ℤ) (b : X) :
    (0 : ℤ) ≤ (Finsupp.single a (v.toNat : ℤ)) b := by
  rcases eq_or_ne a b with rfl | hne
  · rw [Finsupp.single_eq_same]
    positivity
  · rw [Finsupp.single_eq_of_ne' hne]

theorem le_tailCutoff (A : Divisor X) (Z : TailSpace X) : A ≤ tailCutoff A Z := by
  rw [tailCutoff]
  refine le_add_of_nonneg_right fun p => ?_
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun q _ => single_toNat_apply_nonneg q.1 _ p

/-- Every entry of `Z` has degree `≥ −(tailCutoff A Z)(p)`: the cutoff is deep enough. -/
theorem neg_tailCutoff_le_of_mem_support (A : Divisor X) (Z : TailSpace X) {q : X × ℤ}
    (hq : q ∈ Z.support) : -(tailCutoff A Z q.1) ≤ q.2 := by
  have hterm : -q.2 - A q.1
      ≤ (∑ r ∈ Z.support, Finsupp.single r.1 ((-r.2 - A r.1).toNat : ℤ)) q.1 := by
    rw [Finsupp.finsetSum_apply]
    calc -q.2 - A q.1 ≤ ((-q.2 - A q.1).toNat : ℤ) := Int.self_le_toNat _
      _ = (Finsupp.single q.1 ((-q.2 - A q.1).toNat : ℤ)) q.1 := Finsupp.single_eq_same.symm
      _ ≤ ∑ r ∈ Z.support, (Finsupp.single r.1 ((-r.2 - A r.1).toNat : ℤ)) q.1 :=
          Finset.single_le_sum (fun r _ => single_toNat_apply_nonneg r.1 _ q.1) hq
  have happly : tailCutoff A Z q.1 = A q.1
      + (∑ r ∈ Z.support, Finsupp.single r.1 ((-r.2 - A r.1).toNat : ℤ)) q.1 := by
    rw [tailCutoff, Finsupp.add_apply]
  omega

/-- **Deep truncation kills the tail**: `t^{A}_{tailCutoff A Z} Z = 0`. -/
theorem truncateRaw_tailCutoff (A : Divisor X) (Z : TailSpace X) :
    truncateRaw (tailCutoff A Z) Z = 0 := by
  ext q
  rw [truncateRaw_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs with hq
  · by_contra hZq
    exact absurd (neg_tailCutoff_le_of_mem_support A Z (Finsupp.mem_support_iff.mpr hZq))
      (not_le.mpr hq)
  · rfl

/-- Sanity: the residue tail `z⁻¹ ↦ 1` at any point lies in `𝒯[0]`. -/
example (p : X) : Finsupp.single (p, (-1 : ℤ)) (1 : ℂ) ∈ tailSubspace (X := X) 0 := by
  rw [mem_tailSubspace_iff]
  intro q hq
  rw [Finsupp.single_apply_eq_zero]
  rintro rfl
  simp at hq

end Jacobians.LaurentTail
