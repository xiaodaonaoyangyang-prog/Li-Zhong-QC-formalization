/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Serre duality for the tail `H¹`, the injective half (Miranda Ch. VI Thm 3.3, p. 188)

For genus ≥ 1 we run Miranda's duality in the **ω₀-frame**: fix `0 ≠ ω₀ ∈ Ω(X)` and represent
meromorphic 1-forms as `h·ω₀` with `h` meromorphic.  The local coefficient of `h·ω₀` in the
canonical chart at `p` is `coeffAt ω₀ p · (h ∘ chart⁻¹)` — exactly the integrand of the
residue theorem `residueTheorem_formFn_unconditional`, so the residue map's vanishing on
realized tails needs no factorization detour.

Contents:
* `canonicalDivisorOf ω₀ hω₀` — the divisor of zeros of `ω₀` (finite support by
  `finite_localRep_self_eq_zero`); this is the canonical divisor `K = div ω₀`.
* the order bridge `omegaOrderBounded_iff_mem`: `h·ω₀ ∈ L^(1)(−D) ⟺ h ∈ L(K−D)`.
* the residue functional `omegaTailResidue ω₀ h` on tails; its vanishing on realized tails
  (`omegaTailResidue_tailMap_eq_zero`, via `residueTheorem_formFn_unconditional` with the
  analytic-bad-set enlargement); the descended **duality pairing**
  `omegaDualMap : lSysModule (K−D) →ₗ (H¹(D))*`.
* **Injectivity** (Miranda p. 188): a nonzero class `[h]` pairs against the single-monomial tail
  `z^{−1−o}·p` (`o` the local order of `h·ω₀` at a point where `h`'s germ survives) to the
  *leading Laurent coefficient*, nonzero by the anchor lemma `laurentCoeff_order_ne_zero`.
  Hence the easy half of duality: `lDim (K − D) ≤ h1TailDim D`.

The surjective half (Miranda pp. 189–191) is built separately.
-/
import Jacobians.LaurentTail.Finiteness
import Jacobians.ResidueTheorem.ResidueTheoremFormFn
import Jacobians.SerrePairing.SerreDuality
import Jacobians.TailDuality.TailResidue
open scoped Manifold ContDiff Topology
open Filter Set
open Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace

namespace Jacobians.LaurentTail

/-! ### §0 A planar helper: analytic germs have no negative Laurent coefficients -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §1 The ω₀-frame integrand, the order of `ω₀`, and the canonical divisor -/

/-- The local coefficient of the 1-form `h·ω₀` in the canonical chart at `p` — the integrand of
`formFnResidue ω₀ h.toFun p` (with `coeffAt` as the first factor). -/
noncomputable def omegaCoeffFun (ω₀ : HolomorphicOneForms X) (h : MeromorphicFunction X)
    (p : X) : ℂ → ℂ :=
  fun z => coeffAt ω₀ p z * h.toFun ((chartAt (H := ℂ) p).symm z)

theorem analyticAt_coeffAt_self (ω₀ : HolomorphicOneForms X) (p : X) :
    AnalyticAt ℂ (fun z => coeffAt ω₀ p z) ((chartAt (H := ℂ) p) p) :=
  coeffAt_analyticAt ω₀ p ((chartAt (H := ℂ) p).map_source (mem_chart_source ℂ p))

theorem meromorphicAt_omegaCoeffFun (ω₀ : HolomorphicOneForms X) (h : MeromorphicFunction X)
    (p : X) :
    MeromorphicAt (omegaCoeffFun ω₀ h p) ((chartAt (H := ℂ) p) p) :=
  (analyticAt_coeffAt_self ω₀ p).meromorphicAt.mul (h.meromorphic p)

/-- The order of `ω₀` at `p`: the meromorphic (= analytic) order of the canonical-chart
coefficient. -/
noncomputable def omegaOrderAt (ω₀ : HolomorphicOneForms X) (p : X) : WithTop ℤ :=
  meromorphicOrderAt (fun z => coeffAt ω₀ p z) ((chartAt (H := ℂ) p) p)

/-- For `ω₀ ≠ 0`, the order is finite at every point (the coefficient is not eventually zero —
the identity-theorem atom `coeffAt_eventually_ne_zero`). -/
theorem omegaOrderAt_ne_top (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) (p : X) :
    omegaOrderAt ω₀ p ≠ ⊤ := by
  rw [omegaOrderAt, Ne, meromorphicOrderAt_eq_top_iff]
  intro hev
  obtain ⟨z, hz0, hzne⟩ := (hev.and (coeffAt_eventually_ne_zero ω₀ hω₀ p)).exists
  exact hzne hz0

/-- The chart-centre value of `coeffAt` is `localRep` on the diagonal. -/
theorem coeffAt_self_eq_localRep (ω₀ : HolomorphicOneForms X) (p : X) :
    coeffAt ω₀ p ((chartAt (H := ℂ) p) p) = Jacobians.Montel.localRep ω₀ p p := by
  rw [coeffAt, (chartAt (H := ℂ) p).left_inv (mem_chart_source ℂ p)]

/-- A nonzero chart-centre value forces order `0` (continuity + the order-zero criterion). -/
theorem omegaOrderAt_eq_zero_of_localRep_ne_zero (ω₀ : HolomorphicOneForms X) (p : X)
    (hval : Jacobians.Montel.localRep ω₀ p p ≠ 0) :
    omegaOrderAt ω₀ p = 0 := by
  rw [omegaOrderAt, ← tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero
    (analyticAt_coeffAt_self ω₀ p).meromorphicAt]
  refine ⟨Jacobians.Montel.localRep ω₀ p p, hval, ?_⟩
  rw [← coeffAt_self_eq_localRep ω₀ p]
  exact ((analyticAt_coeffAt_self ω₀ p).continuousAt.tendsto).mono_left nhdsWithin_le_nhds

/-- **The canonical divisor `K = div ω₀`** (Miranda p. 191; Forster 17.4): the zero divisor of a
nonzero holomorphic 1-form, supported on its finite zero set. -/
noncomputable def canonicalDivisorOf (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) : Divisor X :=
  Finsupp.onFinset (finite_localRep_self_eq_zero ω₀ hω₀).toFinset
    (fun p => WithTop.untopD 0 (omegaOrderAt ω₀ p))
    (fun p hne => by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      by_contra hval
      apply hne
      show WithTop.untopD 0 (omegaOrderAt ω₀ p) = 0
      rw [omegaOrderAt_eq_zero_of_localRep_ne_zero ω₀ p hval]
      rfl)

theorem canonicalDivisorOf_apply (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) (p : X) :
    canonicalDivisorOf ω₀ hω₀ p = WithTop.untopD 0 (omegaOrderAt ω₀ p) := rfl

/-- The canonical divisor reads the order: `(K p : WithTop ℤ) = omegaOrderAt ω₀ p`. -/
theorem coe_canonicalDivisorOf (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) (p : X) :
    ((canonicalDivisorOf ω₀ hω₀ p : ℤ) : WithTop ℤ) = omegaOrderAt ω₀ p := by
  rw [canonicalDivisorOf_apply]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (omegaOrderAt_ne_top ω₀ hω₀ p)
  rw [← hk]
  rfl

/-! ### §2 The order bridge: `h·ω₀ ∈ L^(1)(−D) ⟺ h ∈ L(K−D)` -/

/-- **Miranda's `ω ∈ L^(1)(−D)`** in the ω₀-frame: the form `h·ω₀` has local order at least
`D(p)` at every point. -/
def OmegaOrderBounded (ω₀ : HolomorphicOneForms X) (h : MeromorphicFunction X)
    (D : Divisor X) : Prop :=
  ∀ p : X, (D p : WithTop ℤ)
    ≤ meromorphicOrderAt (omegaCoeffFun ω₀ h p) ((chartAt (H := ℂ) p) p)

/-- The order of the integrand is the order of `ω₀` plus the order of `h`. -/
theorem meromorphicOrderAt_omegaCoeffFun (ω₀ : HolomorphicOneForms X)
    (h : MeromorphicFunction X) (p : X) :
    meromorphicOrderAt (omegaCoeffFun ω₀ h p) ((chartAt (H := ℂ) p) p)
      = omegaOrderAt ω₀ p + h.orderW p :=
  meromorphicOrderAt_mul (analyticAt_coeffAt_self ω₀ p).meromorphicAt (h.meromorphic p)

/-- **The order bridge** (Miranda p. 187): `h·ω₀` has order ≥ `D` everywhere iff
`h ∈ L(K − D)` for the canonical divisor `K = div ω₀`. -/
theorem omegaOrderBounded_iff_mem (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0)
    (h : MeromorphicFunction X) (D : Divisor X) :
    OmegaOrderBounded ω₀ h D
      ↔ h ∈ linearSystem (X := X) (canonicalDivisorOf ω₀ hω₀ - D) := by
  have hmem : ∀ p : X, ((canonicalDivisorOf ω₀ hω₀ - D) p : ℤ) =
      canonicalDivisorOf ω₀ hω₀ p - D p := fun p => Finsupp.sub_apply _ _ _
  constructor
  · intro hbd p
    have h1 := hbd p
    rw [meromorphicOrderAt_omegaCoeffFun] at h1
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (omegaOrderAt_ne_top ω₀ hω₀ p)
    have hKp : canonicalDivisorOf ω₀ hω₀ p = k := by
      have hc := coe_canonicalDivisorOf ω₀ hω₀ p
      rw [← hk] at hc
      exact_mod_cast hc
    rcases eq_or_ne (h.orderW p) ⊤ with htop | hne
    · rw [htop]; exact le_top
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hk, ← hm, ← WithTop.coe_add] at h1
    have h2 : (D p : ℤ) ≤ k + m := by exact_mod_cast h1
    rw [← hm]
    have h3 : (-((canonicalDivisorOf ω₀ hω₀ - D) p) : ℤ) ≤ m := by
      rw [hmem p, hKp]; omega
    exact_mod_cast h3
  · intro hLS p
    have h1 : (-((canonicalDivisorOf ω₀ hω₀ - D) p) : WithTop ℤ) ≤ h.orderW p := hLS p
    rw [meromorphicOrderAt_omegaCoeffFun]
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (omegaOrderAt_ne_top ω₀ hω₀ p)
    have hKp : canonicalDivisorOf ω₀ hω₀ p = k := by
      have hc := coe_canonicalDivisorOf ω₀ hω₀ p
      rw [← hk] at hc
      exact_mod_cast hc
    rcases eq_or_ne (h.orderW p) ⊤ with htop | hne
    · rw [htop, ← hk, WithTop.add_top]; exact le_top
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hm] at h1
    have h2 : (-((canonicalDivisorOf ω₀ hω₀ - D) p) : ℤ) ≤ m := by exact_mod_cast h1
    rw [hmem p, hKp] at h2
    rw [← hk, ← hm, ← WithTop.coe_add]
    exact_mod_cast (by omega : (D p : ℤ) ≤ k + m)

/-! ### §3 The residue functional in the ω₀-frame and its descent -/

/-- The residue pairing of a single tail monomial `(p, n)` against `h·ω₀`. -/
noncomputable def omegaTailWeight (ω₀ : HolomorphicOneForms X) (h : MeromorphicFunction X)
    (q : X × ℤ) : ℂ :=
  laurentCoeff (omegaCoeffFun ω₀ h q.1) ((chartAt (H := ℂ) q.1) q.1) (-1 - q.2)

/-- **Miranda's residue map `Res_ω : 𝒯(X) → ℂ`** in the ω₀-frame. -/
noncomputable def omegaTailResidue (ω₀ : HolomorphicOneForms X) (h : MeromorphicFunction X) :
    TailSpace X →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun q => LinearMap.toSpanSingleton ℂ ℂ (omegaTailWeight ω₀ h q)

theorem omegaTailResidue_apply (ω₀ : HolomorphicOneForms X) (h : MeromorphicFunction X)
    (Z : TailSpace X) :
    omegaTailResidue ω₀ h Z = ∑ q ∈ Z.support, Z q * omegaTailWeight ω₀ h q := by
  simp [omegaTailResidue, Finsupp.lsum_apply, LinearMap.toSpanSingleton_apply, smul_eq_mul,
    Finsupp.sum]

/-- The per-point pairing identity in the ω₀-frame (mirror of
`resAt_pullback_mul_pairCoeff`, same planar core). -/
theorem resAt_pullback_mul_omegaCoeff (D : Divisor X) (ω₀ : HolomorphicOneForms X)
    (h f : MeromorphicFunction X) (hord : OmegaOrderBounded ω₀ h D) (p : X) (W : Finset ℤ)
    (hWlt : ∀ n ∈ W, n < -(D p))
    (hWcap : ∀ n : ℤ, n < -(D p) → laurentCoeffAt f.toFun p n ≠ 0 → n ∈ W) :
    resAt (fun z => f.toFun ((chartAt (H := ℂ) p).symm z) * omegaCoeffFun ω₀ h p z)
        ((chartAt (H := ℂ) p) p)
      = ∑ n ∈ W, tailMap D f (p, n) * omegaTailWeight ω₀ h (p, n) := by
  have hF' : MeromorphicAt (fun z => f.toFun ((chartAt (H := ℂ) p).symm z))
      ((chartAt (H := ℂ) p) p) := f.meromorphic p
  have hpair := resAt_mul_eq_sum_tailPairing hF'
    (meromorphicAt_omegaCoeffFun ω₀ h p) (hord p) W hWlt
    (fun n hn hne => hWcap n hn hne)
  rw [hpair]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [tailMap_apply, if_pos (hWlt n hn)]
  rfl

/-- **The vanishing of `Res_ω` on realized tails, ω₀-frame** (Miranda p. 187): direct from
`residueTheorem_formFn_unconditional` at the numerator `f·h`, with the analytic-bad-set
enlargement. -/
theorem omegaTailResidue_tailMap_eq_zero {D : Divisor X} (ω₀ : HolomorphicOneForms X)
    (h : MeromorphicFunction X) (hord : OmegaOrderBounded ω₀ h D)
    (f : MeromorphicFunction X) :
    omegaTailResidue ω₀ h (tailMap D f) = 0 := by
  classical
  set P : Finset X := (tailMap D f).support.image Prod.fst with hP
  set S : Finset X := P ∪ (f * h).finite_nonAnalyticAt.toFinset with hS
  -- regroup by base points and apply the per-point identity
  have hregroup : omegaTailResidue ω₀ h (tailMap D f)
      = ∑ p ∈ S, resAt (fun z => f.toFun ((chartAt (H := ℂ) p).symm z)
          * omegaCoeffFun ω₀ h p z) ((chartAt (H := ℂ) p) p) := by
    rw [omegaTailResidue_apply]
    rw [← Finset.sum_fiberwise_of_maps_to (s := (tailMap D f).support) (t := S)
      (g := Prod.fst)
      (fun q hq => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq))
      (fun q => tailMap D f q * omegaTailWeight ω₀ h q)]
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
    rw [resAt_pullback_mul_omegaCoeff D ω₀ h f hord p Wp hWlt hWcap]
    rw [hWp, Finset.sum_image (fun (q : X × ℤ) hq (q' : X × ℤ) hq' hqq' => by
      have h1 := (Finset.mem_filter.mp hq).2
      have h2 := (Finset.mem_filter.mp hq').2
      exact Prod.ext (h1.trans h2.symm) hqq')]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hfst := (Finset.mem_filter.mp hq).2
    rw [show ((p, q.2) : X × ℤ) = q from Prod.ext hfst.symm rfl]
  -- identify with the residue-theorem terms and sum to zero
  have hpoint : ∀ p ∈ S, resAt (fun z => f.toFun ((chartAt (H := ℂ) p).symm z)
      * omegaCoeffFun ω₀ h p z) ((chartAt (H := ℂ) p) p)
      = formFnResidue ω₀ (f * h).toFun p := by
    intro p _
    refine resAt_congr (Eventually.of_forall fun z => ?_)
    show f.toFun ((chartAt (H := ℂ) p).symm z) * omegaCoeffFun ω₀ h p z
      = coeffAt ω₀ p z * (f * h).toFun ((chartAt (H := ℂ) p).symm z)
    rw [MeromorphicFunction.mul_toFun, Pi.mul_apply, omegaCoeffFun]
    ring
  rw [hregroup, Finset.sum_congr rfl hpoint]
  refine residueTheorem_formFn_unconditional ω₀ (f * h) S fun x hx => ?_
  by_contra hbad
  exact hx (Finset.mem_union_right _ ((f * h).finite_nonAnalyticAt.mem_toFinset.mpr hbad))

/-! ### §4 The duality pairing and injectivity (Miranda p. 188) -/

/-- The weight is additive in `h`. -/
theorem omegaTailWeight_add (ω₀ : HolomorphicOneForms X) (h₁ h₂ : MeromorphicFunction X)
    (q : X × ℤ) :
    omegaTailWeight ω₀ (h₁ + h₂) q = omegaTailWeight ω₀ h₁ q + omegaTailWeight ω₀ h₂ q := by
  rw [omegaTailWeight, omegaTailWeight, omegaTailWeight,
    ← laurentCoeff_add (meromorphicAt_omegaCoeffFun ω₀ h₁ q.1)
      (meromorphicAt_omegaCoeffFun ω₀ h₂ q.1)]
  refine laurentCoeff_congr (Eventually.of_forall fun z => ?_) _
  show omegaCoeffFun ω₀ (h₁ + h₂) q.1 z
    = omegaCoeffFun ω₀ h₁ q.1 z + omegaCoeffFun ω₀ h₂ q.1 z
  simp only [omegaCoeffFun, MeromorphicFunction.add_toFun, Pi.add_apply]
  ring

/-- The weight is homogeneous in `h`. -/
theorem omegaTailWeight_smul (ω₀ : HolomorphicOneForms X) (a : ℂ)
    (h : MeromorphicFunction X) (q : X × ℤ) :
    omegaTailWeight ω₀ (a • h) q = a * omegaTailWeight ω₀ h q := by
  rw [omegaTailWeight, omegaTailWeight,
    ← laurentCoeff_smul a (meromorphicAt_omegaCoeffFun ω₀ h q.1)]
  refine laurentCoeff_congr (Eventually.of_forall fun z => ?_) _
  show omegaCoeffFun ω₀ (a • h) q.1 z = (a • omegaCoeffFun ω₀ h q.1) z
  simp only [omegaCoeffFun, MeromorphicFunction.smul_toFun, Pi.smul_apply, smul_eq_mul]
  ring

/-- The weight vanishes for germ-zero `h`. -/
theorem omegaTailWeight_eq_zero_of_germZero (ω₀ : HolomorphicOneForms X)
    {h : MeromorphicFunction X} (hh : ∀ x, h.orderW x = ⊤) (q : X × ℤ) :
    omegaTailWeight ω₀ h q = 0 := by
  have hev : (fun _ : ℂ => (0 : ℂ)) =ᶠ[𝓝[≠] ((chartAt (H := ℂ) q.1) q.1)]
      omegaCoeffFun ω₀ h q.1 := by
    have h0 := meromorphicOrderAt_eq_top_iff.mp (hh q.1)
    filter_upwards [h0] with z hz
    show (0 : ℂ) = coeffAt ω₀ q.1 z * h.toFun ((chartAt (H := ℂ) q.1).symm z)
    rw [show h.toFun ((chartAt (H := ℂ) q.1).symm z)
      = (h.toFun ∘ (chartAt (H := ℂ) q.1).symm) z from rfl, hz, mul_zero]
  rw [omegaTailWeight, ← laurentCoeff_congr hev, laurentCoeff_def]
  have h0 : (fun z => (fun _ : ℂ => (0 : ℂ)) z
      * (z - ((chartAt (H := ℂ) q.1) q.1)) ^ (-(-1 - q.2) - 1)) = fun _ : ℂ => (0 : ℂ) := by
    funext z
    ring
  rw [h0]
  exact Jacobians.Dolbeault.resAt_eq_zero_of_analyticAt analyticAt_const

/-- **The Serre duality pairing, on representatives**: for `h ∈ L(K−D)` the descended residue
functional on `H¹(D)`. -/
noncomputable def omegaDualFun (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) (D : Divisor X)
    (h : ↥(linearSystem (X := X) (canonicalDivisorOf ω₀ hω₀ - D))) :
    Module.Dual ℂ (mittagLefflerH1 (X := X) D) :=
  Submodule.liftQ _ ((omegaTailResidue ω₀ h.1).comp (Submodule.subtype _)) (by
    rintro Z ⟨f, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, tailMapCo_coe]
    exact omegaTailResidue_tailMap_eq_zero ω₀ h.1
      ((omegaOrderBounded_iff_mem ω₀ hω₀ h.1 D).mpr h.2) f)

@[simp] theorem omegaDualFun_mk (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) (D : Divisor X)
    (h : ↥(linearSystem (X := X) (canonicalDivisorOf ω₀ hω₀ - D)))
    (Z : ↥(tailSubspace (X := X) D)) :
    omegaDualFun ω₀ hω₀ D h (Submodule.Quotient.mk Z)
      = omegaTailResidue ω₀ h.1 (Z : TailSpace X) :=
  rfl

/-- The pairing bundled as a linear map `L(K−D) →ₗ (H¹(D))*` (linearity in `h` from the weight
linearity). -/
noncomputable def omegaDualMapAux (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) (D : Divisor X) :
    ↥(linearSystem (X := X) (canonicalDivisorOf ω₀ hω₀ - D))
      →ₗ[ℂ] Module.Dual ℂ (mittagLefflerH1 (X := X) D) where
  toFun := omegaDualFun ω₀ hω₀ D
  map_add' h₁ h₂ := by
    refine LinearMap.ext fun ξ => ?_
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    rw [LinearMap.add_apply, omegaDualFun_mk, omegaDualFun_mk, omegaDualFun_mk,
      omegaTailResidue_apply, omegaTailResidue_apply, omegaTailResidue_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show ((h₁ + h₂ : ↥(linearSystem (X := X) (canonicalDivisorOf ω₀ hω₀ - D)))
        : MeromorphicFunction X) = (h₁ : MeromorphicFunction X) + h₂ from rfl,
      omegaTailWeight_add, mul_add]
  map_smul' a h := by
    refine LinearMap.ext fun ξ => ?_
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    rw [RingHom.id_apply, LinearMap.smul_apply, omegaDualFun_mk, omegaDualFun_mk,
      omegaTailResidue_apply, omegaTailResidue_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show ((a • h : ↥(linearSystem (X := X) (canonicalDivisorOf ω₀ hω₀ - D)))
        : MeromorphicFunction X) = a • (h : MeromorphicFunction X) from rfl,
      omegaTailWeight_smul]
    ring

/-- **The Serre duality pairing** `ι : L(K−D)/germ0 →ₗ (H¹(D))*` (Miranda Thm 3.3's map, on the
junk-free quotient that defines `lDim`). -/
noncomputable def omegaDualMap (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) (D : Divisor X) :
    (↥(linearSystem (X := X) (canonicalDivisorOf ω₀ hω₀ - D))
        ⧸ (germZeroSubmodule (X := X)).submoduleOf
            (linearSystem (X := X) (canonicalDivisorOf ω₀ hω₀ - D)))
      →ₗ[ℂ] Module.Dual ℂ (mittagLefflerH1 (X := X) D) :=
  Submodule.liftQ _ (omegaDualMapAux ω₀ hω₀ D) (by
    intro h hmem
    have hger : ∀ x, (h : MeromorphicFunction X).orderW x = ⊤ := hmem
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun ξ => ?_
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    show omegaDualFun ω₀ hω₀ D h (Submodule.Quotient.mk Z) = 0
    rw [omegaDualFun_mk, omegaTailResidue_apply]
    exact Finset.sum_eq_zero fun q _ => by
      rw [omegaTailWeight_eq_zero_of_germZero ω₀ hger q, mul_zero])

/-- **Injectivity of the duality pairing** (Miranda Thm 3.3, p. 188): a class `[h] ≠ 0` pairs
against the single-monomial tail `z^{−1−o}·p` (at a point `p` where `h`'s germ survives, `o` the
local order of `h·ω₀`) to the leading Laurent coefficient — nonzero by
`laurentCoeff_order_ne_zero`. -/
theorem omegaDualMap_injective (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) (D : Divisor X) :
    Function.Injective (omegaDualMap ω₀ hω₀ D) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero]
  by_contra hcon
  -- a point where the germ of `h` survives
  have hex : ∃ p : X, (h : MeromorphicFunction X).orderW p ≠ ⊤ := by
    by_contra hall
    push Not at hall
    exact hcon fun x => hall x
  obtain ⟨p, hp⟩ := hex
  -- the (finite) order of the integrand `h·ω₀` at `p`
  have hfin : meromorphicOrderAt (omegaCoeffFun ω₀ (h : MeromorphicFunction X) p)
      ((chartAt (H := ℂ) p) p) ≠ ⊤ := by
    rw [meromorphicOrderAt_omegaCoeffFun]
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (omegaOrderAt_ne_top ω₀ hω₀ p)
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hp
    rw [← hk, ← hm, ← WithTop.coe_add]
    exact WithTop.coe_ne_top
  obtain ⟨o, ho⟩ := WithTop.ne_top_iff_exists.mp hfin
  -- membership gives `D p ≤ o`
  have hDo : D p ≤ o := by
    have hbd := (omegaOrderBounded_iff_mem ω₀ hω₀ (h : MeromorphicFunction X) D).mpr h.2 p
    rw [← ho] at hbd
    exact_mod_cast hbd
  -- the witness tail `z^{−1−o}·p`
  have hmemtail : Finsupp.single ((p, -1 - o) : X × ℤ) (1 : ℂ) ∈ tailSubspace (X := X) D := by
    rw [mem_tailSubspace_iff]
    intro q hq
    rcases eq_or_ne q (p, -1 - o) with rfl | hne
    · exact absurd (by omega : (-1 - o : ℤ) < -(D p)) (by simpa using hq)
    · exact Finsupp.single_eq_of_ne hne
  -- the pairing value at the witness is the leading Laurent coefficient
  have hval : omegaTailResidue ω₀ (h : MeromorphicFunction X)
      (Finsupp.single ((p, -1 - o) : X × ℤ) (1 : ℂ))
      = laurentCoeff (omegaCoeffFun ω₀ (h : MeromorphicFunction X) p)
          ((chartAt (H := ℂ) p) p) o := by
    rw [omegaTailResidue_apply, Finsupp.support_single _ one_ne_zero,
      Finset.sum_singleton, Finsupp.single_eq_same, one_mul, omegaTailWeight]
    congr 1
    omega
  -- the leading coefficient is nonzero
  have hne0 : laurentCoeff (omegaCoeffFun ω₀ (h : MeromorphicFunction X) p)
      ((chartAt (H := ℂ) p) p) o ≠ 0 :=
    laurentCoeff_order_ne_zero (meromorphicAt_omegaCoeffFun ω₀ _ p) ho.symm
  -- but the functional vanishes on the witness class
  have happ : omegaDualMap ω₀ hω₀ D (Submodule.Quotient.mk h)
      (Submodule.Quotient.mk ⟨Finsupp.single ((p, -1 - o) : X × ℤ) (1 : ℂ), hmemtail⟩)
      = 0 := by
    rw [hx]
    rfl
  rw [show omegaDualMap ω₀ hω₀ D (Submodule.Quotient.mk h)
      = omegaDualFun ω₀ hω₀ D h from rfl, omegaDualFun_mk] at happ
  exact hne0 (hval ▸ happ)

end Jacobians.LaurentTail
