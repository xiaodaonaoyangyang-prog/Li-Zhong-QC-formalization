/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# The residue map on Laurent tail divisors (Miranda Ch. VI pp. 186–188)

For a meromorphic pair-form `ω = h·dg₀` whose local order is bounded below by a divisor `D`
(Miranda's `ω ∈ L^(1)(−D)`), the **residue map**

  `Res_ω : 𝒯[D](X) → ℂ`,  `Res_ω(∑ r_p·p) = ∑_p Res_p(r_p·ω)`

is a finite sum of Laurent-coefficient pairings — pure coefficient algebra.  Its key property
(Miranda p. 187) is the **vanishing on realized tails**: for any global meromorphic `f`,

  `Res_ω(α_D f) = ∑_p Res_p(f·ω) = 0`

by the genus-free 1-form residue theorem (`residueSum_pairForm_mul_eq_zero_unconditional`,
the planar-Stokes ledger) — the residue of `f·ω` at `p` depends only on `f`'s Laurent tail
below `−D(p)`, because the rest of `f` against `ω` has order ≥ `−D(p) + D(p) = 0`.  Hence
`Res_ω` descends to the Mittag-Leffler obstruction space `H¹(D) = 𝒯[D]/im(α_D)` — the
functional `tailResidueH1` that feeds the Serre duality pairing — in every genus.

The planar core is `resAt_mul_eq_sum_tailPairing`: a *uniform window* form of "the residue of a
product reads only the tail" (the window may be empty, subsuming the no-pole case).
-/
import Jacobians.LaurentTail.TailMap
import Jacobians.ResidueTheorem.ResidueTheoremStokes
open scoped Manifold ContDiff Topology
open Filter Set
open Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace

namespace Jacobians.LaurentTail

/-! ### §1 Planar core -/

/-- `Res_c((·−c)^e) = δ_{e,−1}` for every integer exponent. -/
theorem resAt_monomial (c : ℂ) (e : ℤ) :
    resAt (fun z => (z - c) ^ e) c = if e = -1 then 1 else 0 := by
  rcases le_or_gt 0 e with he | he
  · -- nonnegative exponent: analytic, residue `0`
    lift e to ℕ using he
    have hfun : (fun z : ℂ => (z - c) ^ (e : ℤ)) = fun z => (z - c) ^ e := by
      funext z; rw [zpow_natCast]
    have hana : AnalyticAt ℂ (fun z : ℂ => (z - c) ^ e) c :=
      (analyticAt_id.sub analyticAt_const).pow e
    rw [hfun, Jacobians.Dolbeault.resAt_eq_zero_of_analyticAt hana, if_neg (by omega)]
  · -- negative exponent `e = −k`, `k ≥ 1`
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, e = -(k : ℤ) := ⟨e.natAbs, by omega⟩
    by_cases h1 : k = 1
    · subst h1
      rw [if_pos (by norm_num)]
      exact resAt_zpow_neg_one c
    · rw [resAt_zpow_neg_of_ne h1, if_neg (by omega)]

/-- `resAt` of a constant multiple of a monomial against the residue-extraction monomial:
the Laurent coefficient of `a·(·−c)^k` at degree `j` is `a·δ_{k,j}`. -/
theorem laurentCoeff_const_mul_monomial (a c : ℂ) (k j : ℤ) :
    laurentCoeff (fun z => a * (z - c) ^ k) c j = if k = j then a else 0 := by
  rw [laurentCoeff_def]
  have hev : (fun z => (a * (z - c) ^ k) * (z - c) ^ (-j - 1))
      =ᶠ[𝓝[≠] c] fun z => a * (z - c) ^ (k + (-j - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzc : z - c ≠ 0 := sub_ne_zero.mpr hz
    rw [zpow_add₀ hzc]
    ring
  rw [resAt_congr hev]
  have hsmul : (fun z => a * (z - c) ^ (k + (-j - 1)))
      = a • fun z : ℂ => (z - c) ^ (k + (-j - 1)) := rfl
  have hpunct : HoloPunctured (fun z : ℂ => (z - c) ^ (k + (-j - 1))) c :=
    (meromorphicAt_monomial c _).holoPunctured
  rw [hsmul, resAt_smul a hpunct, resAt_monomial, smul_eq_mul]
  by_cases hkj : k = j
  · rw [if_pos hkj, if_pos (by omega), mul_one]
  · rw [if_neg hkj, if_neg (by omega), mul_zero]

/-- Finite sums of meromorphic germs are meromorphic. -/
theorem meromorphicAt_finset_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℂ) {c : ℂ}
    (hg : ∀ i ∈ s, MeromorphicAt (g i) c) :
    MeromorphicAt (fun z => ∑ i ∈ s, g i z) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [(analyticAt_const (v := (0 : ℂ))).meromorphicAt]
  | insert a s ha ih =>
    have hfun : (fun z => ∑ i ∈ insert a s, g i z)
        = fun z => g a z + ∑ i ∈ s, g i z := by
      funext z; exact Finset.sum_insert ha
    rw [hfun]
    exact (hg a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

/-- Laurent coefficients of a finite sum of meromorphic germs. -/
theorem laurentCoeff_finset_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ → ℂ) {c : ℂ}
    (hg : ∀ i ∈ s, MeromorphicAt (g i) c) (j : ℤ) :
    laurentCoeff (fun z => ∑ i ∈ s, g i z) c j = ∑ i ∈ s, laurentCoeff (g i) c j := by
  have hsum := resAt_finset_sum s (fun i => fun w => g i w * (w - c) ^ (-j - 1))
    (fun i hi => holoPunctured_mul_monomial (hg i hi) (-j - 1))
  have hfun : (fun z => (∑ i ∈ s, g i z) * (z - c) ^ (-j - 1))
      = fun z => ∑ i ∈ s, g i z * (z - c) ^ (-j - 1) := by
    funext z
    rw [Finset.sum_mul]
  rw [laurentCoeff_def, hfun, hsum]
  exact Finset.sum_congr rfl fun i _ => (laurentCoeff_def _ _ _).symm

/-- The residue of a monomial against a meromorphic factor extracts a Laurent coefficient:
`Res_c((·−c)^n · W) = W_{−1−n}`. -/
theorem resAt_monomial_mul {W : ℂ → ℂ} {c : ℂ} (n : ℤ) :
    resAt (fun z => (z - c) ^ n * W z) c = laurentCoeff W c (-1 - n) := by
  rw [laurentCoeff_def]
  refine resAt_congr (Eventually.of_forall fun z => ?_)
  rw [show (-(-1 - n) - 1 : ℤ) = n by ring]
  ring

/-- **The local tail-pairing identity** (Miranda Ch. VI p. 187, planar core, uniform-window
form).  Suppose `W` has meromorphic order ≥ `e` at `c`, and `S` is a finite window of degrees
`< −e` capturing every nonvanishing Laurent coefficient of `F` below `−e`.  Then

  `Res_c(F·W) = ∑_{n ∈ S} F_n · W_{−1−n}` :

only `F`'s tail below `−e` pairs nontrivially against `W` (the rest has order ≥ 0).  With
`S = ∅` this is the no-pole vanishing `Res_c(F·W) = 0` for `ord F ≥ −e`. -/
theorem resAt_mul_eq_sum_tailPairing {F W : ℂ → ℂ} {c : ℂ} {e : ℤ}
    (hF : MeromorphicAt F c) (hW : MeromorphicAt W c)
    (hWord : (e : WithTop ℤ) ≤ meromorphicOrderAt W c)
    (S : Finset ℤ) (_hSlt : ∀ n ∈ S, n < -e)
    (hScap : ∀ n : ℤ, n < -e → laurentCoeff F c n ≠ 0 → n ∈ S) :
    resAt (fun z => F z * W z) c
      = ∑ n ∈ S, laurentCoeff F c n * laurentCoeff W c (-1 - n) := by
  classical
  -- the tail polynomial of `F` over the window
  set T : ℂ → ℂ := fun z => ∑ n ∈ S, laurentCoeff F c n * (z - c) ^ n with hT
  have hTmero : MeromorphicAt T c :=
    meromorphicAt_finset_sum S _ fun n _ =>
      (analyticAt_const.meromorphicAt).mul (meromorphicAt_monomial c n)
  -- coefficients of the tail polynomial
  have hcoeffT : ∀ j : ℤ, laurentCoeff T c j = if j ∈ S then laurentCoeff F c j else 0 := by
    intro j
    rw [hT, laurentCoeff_finset_sum S (fun n => fun z => laurentCoeff F c n * (z - c) ^ n)
      (fun n _ => (analyticAt_const.meromorphicAt).mul (meromorphicAt_monomial c n)) j]
    rw [Finset.sum_congr rfl fun n _ => laurentCoeff_const_mul_monomial _ c n j]
    exact Finset.sum_ite_eq' S j _
  -- the remainder `F − T` has order ≥ −e
  set R : ℂ → ℂ := (fun z => F z - T z) with hR
  have hFT : MeromorphicAt R c := hF.sub hTmero
  have hcoeffFT : ∀ j : ℤ, laurentCoeff R c j
      = laurentCoeff F c j - laurentCoeff T c j := by
    intro j
    have hnegT : laurentCoeff (-T) c j = -laurentCoeff T c j := by
      have hT' : (-T) = (-1 : ℂ) • T := by funext z; simp
      rw [hT', laurentCoeff_smul (-1 : ℂ) hTmero]
      ring
    have hfun : R = F + -T := by
      funext z
      simp only [hR, Pi.add_apply, Pi.neg_apply]
      ring
    rw [hfun, laurentCoeff_add hF hTmero.neg, hnegT]
    ring
  have hrest_ord : ((-e : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt R c := by
    rw [le_order_iff_laurentCoeff_eq_zero hFT]
    intro n hn
    rw [hcoeffFT n, hcoeffT n]
    split_ifs with hmem
    · exact sub_self _
    · rw [sub_zero]
      by_contra hne
      exact hmem (hScap n hn hne)
  -- split the product
  have hsplit : (fun z => F z * W z) = (T * W) + (R * W) := by
    funext z
    simp only [hR, hT, Pi.add_apply, Pi.mul_apply]
    ring
  rw [hsplit, resAt_add ((hTmero.mul hW).holoPunctured) ((hFT.mul hW).holoPunctured)]
  -- the remainder term has nonnegative order, hence residue 0
  have hzero : resAt (R * W) c = 0 := by
    refine resAt_eq_zero_of_nonneg_order (hFT.mul hW) ?_
    rw [meromorphicOrderAt_mul hFT hW]
    calc ((0 : ℤ) : WithTop ℤ) = ((-e : ℤ) : WithTop ℤ) + ((e : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]; norm_num
      _ ≤ _ := add_le_add hrest_ord hWord
  -- the tail term is the coefficient pairing
  have htail : resAt (T * W) c
      = ∑ n ∈ S, laurentCoeff F c n * laurentCoeff W c (-1 - n) := by
    have hfun : (T * W)
        = fun z => ∑ n ∈ S, (fun w => laurentCoeff F c n * ((w - c) ^ n * W w)) z := by
      funext z
      simp only [hT, Pi.mul_apply]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun n _ => by ring
    have hterm : ∀ n ∈ S, HoloPunctured
        (fun z => laurentCoeff F c n * ((z - c) ^ n * W z)) c := by
      intro n _
      exact ((analyticAt_const.meromorphicAt).mul
        ((meromorphicAt_monomial c n).mul hW)).holoPunctured
    rw [hfun, resAt_finset_sum S (fun n => fun z =>
      laurentCoeff F c n * ((z - c) ^ n * W z)) hterm]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hsmul : (fun z => laurentCoeff F c n * ((z - c) ^ n * W z))
        = laurentCoeff F c n • fun z => (z - c) ^ n * W z := rfl
    have hp : HoloPunctured (fun z => (z - c) ^ n * W z) c :=
      ((meromorphicAt_monomial c n).mul hW).holoPunctured
    rw [hsmul, resAt_smul _ hp, resAt_monomial_mul n, smul_eq_mul]
  rw [hzero, htail, add_zero]

/-! ### §2 The pair-form local coefficient on the surface -/

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The local coefficient function of the meromorphic pair-form `ω = h·dg₀` in the canonical
chart at `p` — the integrand of `Jacobians.Dolbeault.pairFormResidue`. -/
noncomputable def pairCoeffFun (g₀ h : MeromorphicFunction X) (p : X) : ℂ → ℂ :=
  fun z => h.toFun ((chartAt (H := ℂ) p).symm z)
    * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) p).symm w)) z

theorem meromorphicAt_pairCoeffFun (g₀ h : MeromorphicFunction X) (p : X) :
    MeromorphicAt (pairCoeffFun g₀ h p) ((chartAt (H := ℂ) p) p) :=
  (h.meromorphic p).mul ((g₀.meromorphic p).deriv)

/-- **Miranda's `ω ∈ L^(1)(−D)`** (Ch. VI p. 187): the pair-form `h·dg₀` has local order at
least `D(p)` at every point, computed in the canonical chart. -/
def PairOrderBounded (g₀ h : MeromorphicFunction X) (D : Divisor X) : Prop :=
  ∀ p : X, (D p : WithTop ℤ)
    ≤ meromorphicOrderAt (pairCoeffFun g₀ h p) ((chartAt (H := ℂ) p) p)

/-! ### §3 The residue map on tails and its descent to `H¹(D)` -/

/-- The residue pairing of a single tail monomial `(p, n)` against `ω = h·dg₀`:
`Res_p((z−c_p)^n·ω) = ω_{−1−n}`, the `(−1−n)`-th Laurent coefficient of `ω` at `p`. -/
noncomputable def tailResidueWeight (g₀ h : MeromorphicFunction X) (q : X × ℤ) : ℂ :=
  laurentCoeff (pairCoeffFun g₀ h q.1) ((chartAt (H := ℂ) q.1) q.1) (-1 - q.2)

/-- **Miranda's residue map `Res_ω : 𝒯(X) → ℂ`** (Ch. VI p. 187) for `ω = h·dg₀`: the finite
sum of local residues `∑_p Res_p(r_p·ω)`, i.e. the coefficient pairing of each tail entry
against `ω` — ℂ-linear by construction. -/
noncomputable def tailResidue (g₀ h : MeromorphicFunction X) : TailSpace X →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun q => LinearMap.toSpanSingleton ℂ ℂ (tailResidueWeight g₀ h q)

theorem tailResidue_apply (g₀ h : MeromorphicFunction X) (Z : TailSpace X) :
    tailResidue g₀ h Z = ∑ q ∈ Z.support, Z q * tailResidueWeight g₀ h q := by
  simp [tailResidue, Finsupp.lsum_apply, LinearMap.toSpanSingleton_apply, smul_eq_mul,
    Finsupp.sum]

/-- **The residue of `f·ω` at `p` reads only `f`'s tail below `−D(p)`** (Miranda p. 187): the
per-point pairing identity, with the window taken from the support of the truncated tail. -/
theorem resAt_pullback_mul_pairCoeff [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] (D : Divisor X) (g₀ h f : MeromorphicFunction X)
    (hord : PairOrderBounded g₀ h D) (p : X) (W : Finset ℤ)
    (hWlt : ∀ n ∈ W, n < -(D p))
    (hWcap : ∀ n : ℤ, n < -(D p) → laurentCoeffAt f.toFun p n ≠ 0 → n ∈ W) :
    resAt (fun z => f.toFun ((chartAt (H := ℂ) p).symm z) * pairCoeffFun g₀ h p z)
        ((chartAt (H := ℂ) p) p)
      = ∑ n ∈ W, tailMap D f (p, n) * tailResidueWeight g₀ h (p, n) := by
  have hF' : MeromorphicAt (fun z => f.toFun ((chartAt (H := ℂ) p).symm z))
      ((chartAt (H := ℂ) p) p) := f.meromorphic p
  have hWcap' : ∀ n : ℤ, n < -(D p)
      → laurentCoeff (fun z => f.toFun ((chartAt (H := ℂ) p).symm z))
          ((chartAt (H := ℂ) p) p) n ≠ 0
      → n ∈ W := fun n hn hne => hWcap n hn hne
  have hpair := resAt_mul_eq_sum_tailPairing hF'
    (meromorphicAt_pairCoeffFun g₀ h p) (hord p) W hWlt hWcap'
  rw [hpair]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [tailMap_apply, if_pos (hWlt n hn)]
  rfl

/-- **The vanishing of `Res_ω` on realized tails** (Miranda Ch. VI p. 187, every genus): for any
global meromorphic `f`, `Res_ω(α_D f) = ∑_p Res_p(f·ω) = 0` by the genus-free pair-form residue
theorem.  This is exactly what lets the residue map descend to the Mittag-Leffler `H¹(D)`. -/
theorem tailResidue_tailMap_eq_zero [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [IsManifold 𝓘(ℂ) ω X] [Nonempty X] {D : Divisor X}
    (g₀ h : MeromorphicFunction X) (hord : PairOrderBounded g₀ h D)
    (f : MeromorphicFunction X) :
    tailResidue g₀ h (tailMap D f) = 0 := by
  classical
  set P : Finset X := (tailMap D f).support.image Prod.fst with hP
  set S : Finset X := P ∪ ((f * h).finite_nonAnalyticAt.toFinset
    ∪ g₀.finite_nonAnalyticAt.toFinset) with hS
  -- regroup the tail sum by base points, then apply the per-point pairing identity
  have hregroup : tailResidue g₀ h (tailMap D f)
      = ∑ p ∈ S, resAt (fun z => f.toFun ((chartAt (H := ℂ) p).symm z)
          * pairCoeffFun g₀ h p z) ((chartAt (H := ℂ) p) p) := by
    rw [tailResidue_apply]
    rw [← Finset.sum_fiberwise_of_maps_to (s := (tailMap D f).support) (t := S)
      (g := Prod.fst)
      (fun q hq => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq))
      (fun q => tailMap D f q * tailResidueWeight g₀ h q)]
    refine Finset.sum_congr rfl fun p _ => ?_
    set Wp : Finset ℤ :=
      ((tailMap D f).support.filter (fun q : X × ℤ => q.1 = p)).image Prod.snd with hWp
    have hWlt : ∀ n ∈ Wp, n < -(D p) := by
      intro n hn
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨hsupp, hfst⟩ := Finset.mem_filter.mp hq
      by_contra hge
      apply Finsupp.mem_support_iff.mp hsupp
      rw [show q = (p, q.2) from Prod.ext hfst rfl, tailMap_apply]
      exact if_neg hge
    have hWcap : ∀ n : ℤ, n < -(D p) → laurentCoeffAt f.toFun p n ≠ 0 → n ∈ Wp := by
      intro n hn hne
      refine Finset.mem_image.mpr ⟨(p, n), Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
      rw [Finsupp.mem_support_iff, tailMap_apply, if_pos hn]
      exact hne
    rw [resAt_pullback_mul_pairCoeff D g₀ h f hord p Wp hWlt hWcap]
    rw [hWp, Finset.sum_image (fun (q : X × ℤ) hq (q' : X × ℤ) hq' hqq' => by
      have h1 := (Finset.mem_filter.mp hq).2
      have h2 := (Finset.mem_filter.mp hq').2
      exact Prod.ext (h1.trans h2.symm) hqq')]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hfst := (Finset.mem_filter.mp hq).2
    rw [show ((p, q.2) : X × ℤ) = q from Prod.ext hfst.symm rfl]
  -- the total is the pair-form residue sum, which vanishes
  have hpoint : ∀ p ∈ S, resAt (fun z => f.toFun ((chartAt (H := ℂ) p).symm z)
      * pairCoeffFun g₀ h p z) ((chartAt (H := ℂ) p) p)
      = pairFormResidue g₀ (f * h) p := by
    intro p _
    refine resAt_congr (Eventually.of_forall fun z => ?_)
    show f.toFun ((chartAt (H := ℂ) p).symm z) * pairCoeffFun g₀ h p z
      = (f * h).toFun ((chartAt (H := ℂ) p).symm z)
        * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) p).symm w)) z
    rw [MeromorphicFunction.mul_toFun, Pi.mul_apply, pairCoeffFun]
    ring
  rw [hregroup, Finset.sum_congr rfl hpoint]
  refine residueSum_pairForm_mul_eq_zero_unconditional g₀ f h S fun x hx => ?_
  -- off `S` both factors are honestly analytic
  have hfh : AnalyticAt ℂ (fun z => (f * h).toFun ((chartAt (H := ℂ) x).symm z))
      ((chartAt (H := ℂ) x) x) := by
    by_contra hbad
    exact hx (Finset.mem_union_right _ (Finset.mem_union_left _
      ((f * h).finite_nonAnalyticAt.mem_toFinset.mpr hbad)))
  have hg₀ : AnalyticAt ℂ (fun z => g₀.toFun ((chartAt (H := ℂ) x).symm z))
      ((chartAt (H := ℂ) x) x) := by
    by_contra hbad
    exact hx (Finset.mem_union_right _ (Finset.mem_union_right _
      (g₀.finite_nonAnalyticAt.mem_toFinset.mpr hbad)))
  exact hfh.mul hg₀.deriv

end Jacobians.LaurentTail
