/-
  The truncation-of-Laurent-series map `α_D : ℳ(X) → 𝒯[D](X)` and the Mittag-Leffler
  obstruction space `H¹(D)` (Miranda Ch. VI §2, pp. 180–182).

  For a meromorphic function `f` on the compact Riemann surface `X`, `tailMap D f` records the
  Laurent coefficients of `f` (in the canonical chart at each point) in all degrees `< −D(p)` —
  Miranda's truncation `α_D(f)` of the full Laurent series.  The two pillars proved here:

  * **`L(D) = ker α_D`** (`ker_tailMap`, Miranda p. 181): `f` has `orderW f p ≥ −D(p)` everywhere
    iff all its tail coefficients below the cutoff vanish — by the order↔coefficients anchor
    lemmas of `LaurentCoeff`.  In particular the germ-zero junk submodule is contained in
    every kernel, so `α_D` descends to the junk-free quotients.
  * **`H¹(D) := 𝒯[D] ⧸ range α_D`** (`mittagLefflerH1`, Miranda Def. 2.4): the Mittag-Leffler
    obstruction space, with its induced truncations `H¹(D₁) → H¹(D₂)` (`D₁ ≤ D₂`), surjective
    because tail truncation is.

  Finite support of `tailMap D f` is where compactness enters: a nonzero coefficient at `(p, n)`
  forces `orderW f p ≤ n < −D(p)`, which confines `p` to `supp (div f) ∪ supp D` (finite, by
  `MeromorphicFunction.div`) and `n` to the finite window `[div f p, −D(p))`.
-/
import Jacobians.LaurentTail.LaurentCoeff
import Jacobians.LaurentTail.TailSpace
import Jacobians.Meromorphic.LinearSystem

open scoped Manifold ContDiff Topology
open Module

namespace Jacobians.LaurentTail

open Jacobians

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ### Laurent coefficients at a point of `X` -/

/-- The **`n`-th Laurent coefficient of `f` at `p`**, read in the canonical chart at `p`
(centre `c_p = chartAt ℂ p p`): the coefficient of `(z − c_p)^n` of the chart pullback
`f ∘ (chartAt ℂ p).symm`. -/
noncomputable def laurentCoeffAt (f : X → ℂ) (p : X) (n : ℤ) : ℂ :=
  laurentCoeff (f ∘ (chartAt (H := ℂ) p).symm) ((chartAt (H := ℂ) p) p) n

/-- Coefficients below the order vanish (`orderW` *is* the chart-pullback meromorphic order). -/
theorem laurentCoeffAt_eq_zero_of_lt_orderW (f : MeromorphicFunction X) {p : X} {n : ℤ}
    (hn : (n : WithTop ℤ) < f.orderW p) : laurentCoeffAt f.toFun p n = 0 :=
  laurentCoeff_eq_zero_of_lt_order (f.meromorphic p) hn

/-- **The order↔coefficients bridge at a point** (Miranda p. 181): `orderW f p ≥ k` iff all
Laurent coefficients of `f` at `p` below `k` vanish. -/
theorem le_orderW_iff_laurentCoeffAt (f : MeromorphicFunction X) (p : X) (k : ℤ) :
    (k : WithTop ℤ) ≤ f.orderW p ↔ ∀ n : ℤ, n < k → laurentCoeffAt f.toFun p n = 0 :=
  le_order_iff_laurentCoeff_eq_zero (f.meromorphic p) k

theorem laurentCoeffAt_add (f g : MeromorphicFunction X) (p : X) (n : ℤ) :
    laurentCoeffAt (f + g).toFun p n
      = laurentCoeffAt f.toFun p n + laurentCoeffAt g.toFun p n :=
  laurentCoeff_add (f.meromorphic p) (g.meromorphic p) n

theorem laurentCoeffAt_smul (a : ℂ) (f : MeromorphicFunction X) (p : X) (n : ℤ) :
    laurentCoeffAt (a • f).toFun p n = a * laurentCoeffAt f.toFun p n :=
  laurentCoeff_smul a (f.meromorphic p) n

/-- Germ-zero functions have vanishing Laurent coefficients in every degree. -/
theorem laurentCoeffAt_eq_zero_of_germZero [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] {f : MeromorphicFunction X}
    (hf : f ∈ germZeroSubmodule (X := X)) (p : X) (n : ℤ) :
    laurentCoeffAt f.toFun p n = 0 :=
  laurentCoeffAt_eq_zero_of_lt_orderW f (by rw [hf p]; exact WithTop.coe_lt_top n)

/-! ### The truncation map `α_D` -/

/-- The divisor of `f` evaluates to the (`untop₀`-read) order: `div f p = (orderW f p)⁰`.
(NB `div` takes `X` explicitly *first*, so `f.div` must be type-ascribed before
application — `f.div p` would feed `p` into the `X` slot.) -/
theorem div_apply [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (f : MeromorphicFunction X) (p : X) :
    (f.div : Divisor X) p = (f.orderW p).untop₀ := by
  show (Finsupp.ofSupportFinite _ _) p = _
  rw [Finsupp.ofSupportFinite_coe]
  rfl

/-- **Finite support of the truncated tail**: a nonzero entry at `(p, n)` with `n < −D(p)` forces
`div f p ≤ n < −D(p)`, confining `(p, n)` to finitely many pairs. -/
theorem tailEntries_support_finite [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X) (f : MeromorphicFunction X) :
    (Function.support fun q : X × ℤ =>
      if q.2 < -(D q.1) then laurentCoeffAt f.toFun q.1 q.2 else 0).Finite := by
  classical
  set Df : Divisor X := f.div with hDf
  apply Set.Finite.subset (Set.Finite.biUnion ((Df.support ∪ D.support).finite_toSet)
    fun p _ => (Set.finite_Ico (Df p) (-(D p))).image fun n => (p, n))
  rintro ⟨p, n⟩ hq
  rw [Function.mem_support] at hq
  by_cases hlt : n < -(D p)
  swap
  · rw [if_neg hlt] at hq
    exact absurd rfl hq
  rw [if_pos hlt] at hq
  -- a nonzero coefficient bounds the order: `orderW f p ≤ n`
  have horder : f.orderW p ≤ (n : WithTop ℤ) := by
    by_contra hcon
    exact hq (laurentCoeffAt_eq_zero_of_lt_orderW f (not_le.mp hcon))
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top (WithTop.coe_ne_top) horder)
  have hdiv : Df p = m := by rw [hDf, div_apply, ← hm, WithTop.untop₀_coe]
  have hmn : m ≤ n := by
    rw [← hm] at horder
    exact_mod_cast horder
  -- `p` lies in the union of the supports (otherwise the window `[0, 0)` is empty)
  have hp : p ∈ Df.support ∪ D.support := by
    by_contra hcon
    rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.notMem_support_iff] at hcon
    rw [hcon.1] at hdiv
    rw [hcon.2] at hlt
    omega
  exact Set.mem_biUnion hp ⟨n, ⟨by omega, hlt⟩, rfl⟩

/-- The underlying tail of `α_D f`: the Laurent coefficients of `f` in degrees `< −D(p)`. -/
noncomputable def tailEntries [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (D : Divisor X) (f : MeromorphicFunction X) : TailSpace X :=
  Finsupp.ofSupportFinite
    (fun q => if q.2 < -(D q.1) then laurentCoeffAt f.toFun q.1 q.2 else 0)
    (tailEntries_support_finite D f)

@[simp] theorem tailEntries_apply [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X) (f : MeromorphicFunction X) (q : X × ℤ) :
    tailEntries D f q = if q.2 < -(D q.1) then laurentCoeffAt f.toFun q.1 q.2 else 0 := rfl

/-- **Miranda's truncation map `α_D : ℳ(X) → 𝒯[D](X)`** (Ch. VI p. 180), as a `ℂ`-linear map
into the ambient tail space: truncate the full Laurent series of `f` to the degrees `< −D(p)`. -/
noncomputable def tailMap [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (D : Divisor X) : MeromorphicFunction X →ₗ[ℂ] TailSpace X where
  toFun := tailEntries D
  map_add' f g := by
    ext q
    rw [Finsupp.add_apply, tailEntries_apply, tailEntries_apply, tailEntries_apply]
    split_ifs with h
    · exact laurentCoeffAt_add f g q.1 q.2
    · exact (add_zero 0).symm
  map_smul' a f := by
    ext q
    rw [RingHom.id_apply, Finsupp.smul_apply, tailEntries_apply, tailEntries_apply]
    split_ifs with h
    · rw [laurentCoeffAt_smul, smul_eq_mul]
    · rw [smul_zero]

@[simp] theorem tailMap_apply [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (D : Divisor X) (f : MeromorphicFunction X) (q : X × ℤ) :
    tailMap D f q = if q.2 < -(D q.1) then laurentCoeffAt f.toFun q.1 q.2 else 0 := rfl

theorem tailMap_mem_tailSubspace [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X) (f : MeromorphicFunction X) :
    tailMap D f ∈ tailSubspace D := by
  rw [mem_tailSubspace_iff]
  intro q hq
  rw [tailMap_apply, if_neg hq]

/-- `α_D` co-restricted to its natural target `𝒯[D](X)`. -/
noncomputable def tailMapCo [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (D : Divisor X) :
    MeromorphicFunction X →ₗ[ℂ] ↥(tailSubspace (X := X) D) :=
  (tailMap D).codRestrict (tailSubspace D) (tailMap_mem_tailSubspace D)

@[simp] theorem tailMapCo_coe [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (D : Divisor X) (f : MeromorphicFunction X) :
    (tailMapCo D f : TailSpace X) = tailMap D f := rfl

/-! ### The kernel bridge `L(D) = ker α_D` -/

/-- **`L(D) = ker α_D`** (Miranda Ch. VI, p. 181): a meromorphic function lies in the complete
linear system `L(D)` iff its `D`-truncated Laurent tail vanishes.  This is the central bridge
between the order-theoretic `linearSystem` and the Laurent-tail calculus. -/
theorem ker_tailMap [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (D : Divisor X) :
    LinearMap.ker (tailMap (X := X) D) = linearSystem (X := X) D := by
  ext f
  rw [LinearMap.mem_ker]
  constructor
  · intro h0 x
    rw [show (-(D x) : WithTop ℤ) = ((-(D x) : ℤ) : WithTop ℤ) from rfl,
      le_orderW_iff_laurentCoeffAt]
    intro n hn
    have hq := DFunLike.congr_fun h0 (x, n)
    rwa [tailMap_apply, if_pos hn, Finsupp.coe_zero, Pi.zero_apply] at hq
  · intro hmem
    ext q
    rw [tailMap_apply, Finsupp.coe_zero, Pi.zero_apply]
    split_ifs with hq
    · refine (le_orderW_iff_laurentCoeffAt f q.1 (-(D q.1))).mp ?_ q.2 hq
      exact_mod_cast hmem q.1
    · rfl

/-- The germ-zero junk submodule is contained in `ker α_D` for every `D` (so `α_D` descends to
the junk-free quotient `lSysModule`). -/
theorem germZeroSubmodule_le_ker_tailMap [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X) :
    germZeroSubmodule (X := X) ≤ LinearMap.ker (tailMap (X := X) D) := by
  intro f hf
  rw [LinearMap.mem_ker]
  ext q
  rw [tailMap_apply, Finsupp.coe_zero, Pi.zero_apply]
  split_ifs with hq
  · exact laurentCoeffAt_eq_zero_of_germZero hf q.1 q.2
  · rfl

/-! ### Compatibility with truncation: `t^{D₁}_{D₂} ∘ α_{D₁} = α_{D₂}` -/

theorem truncateRaw_tailMap [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) (f : MeromorphicFunction X) :
    truncateRaw D₂ (tailMap D₁ f) = tailMap D₂ f := by
  ext q
  rw [truncateRaw_apply, tailMap_apply, tailMap_apply]
  by_cases h2 : q.2 < -(D₂ q.1)
  · rw [if_pos h2, if_pos h2, if_pos (lt_of_lt_of_le h2 (neg_le_neg (h q.1)))]
  · rw [if_neg h2, if_neg h2]

theorem tailTruncate_tailMapCo [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) (f : MeromorphicFunction X) :
    tailTruncate D₁ D₂ (tailMapCo D₁ f) = tailMapCo D₂ f :=
  Subtype.ext (truncateRaw_tailMap h f)

/-! ### The Mittag-Leffler obstruction space `H¹(D)` -/

/-- **Miranda's `H¹(D)`** (Ch. VI Def. 2.4, p. 182): the cokernel of the truncation map,
`𝒯[D](X) ⧸ range α_D` — the space of Laurent tail divisors modulo those realized by global
meromorphic functions. -/
abbrev mittagLefflerH1 [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (D : Divisor X) : Type _ :=
  ↥(tailSubspace (X := X) D) ⧸ LinearMap.range (tailMapCo (X := X) D)

/-- `h¹(D) := dim_ℂ H¹(D)` (finite for every `D` — Miranda Prop. 2.7, proved in `Finiteness`). -/
noncomputable def h1TailDim [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
    (D : Divisor X) : ℕ := finrank ℂ (mittagLefflerH1 (X := X) D)

/-- The truncation `t^{D₁}_{D₂}` descends to the Mittag-Leffler quotients
`H¹(D₁) → H¹(D₂)` (it maps realized tails to realized tails). -/
noncomputable def mittagLefflerTruncate [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    mittagLefflerH1 (X := X) D₁ →ₗ[ℂ] mittagLefflerH1 (X := X) D₂ :=
  Submodule.mapQ _ _ (tailTruncate D₁ D₂) (by
    rintro Z ⟨f, rfl⟩
    exact Submodule.mem_comap.mpr ⟨f, (tailTruncate_tailMapCo h f).symm⟩)

@[simp] theorem mittagLefflerTruncate_mk [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂)
    (Z : ↥(tailSubspace (X := X) D₁)) :
    mittagLefflerTruncate h (Submodule.Quotient.mk Z)
      = Submodule.Quotient.mk (tailTruncate D₁ D₂ Z) :=
  Submodule.mapQ_apply _ _ _ Z

/-- The induced truncation `H¹(D₁) → H¹(D₂)` is **surjective** (Miranda p. 182). -/
theorem mittagLefflerTruncate_surjective [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    Function.Surjective (mittagLefflerTruncate (X := X) h) := by
  intro z
  obtain ⟨Z₂, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨Z₁, rfl⟩ := tailTruncate_surjective h Z₂
  exact ⟨Submodule.Quotient.mk Z₁, mittagLefflerTruncate_mk h Z₁⟩

end Jacobians.LaurentTail
