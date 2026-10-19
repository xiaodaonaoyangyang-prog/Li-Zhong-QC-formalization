/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Serre duality for the tail `H¹`, the injective half — meromorphic pair frame
(Miranda Ch. VI Thm 3.3, p. 188)

Miranda runs the duality with a **meromorphic** 1-form `ω = h·dg₀` (`g₀` the nonconstant
meromorphic function of `exists_nonconstant_meromorphic`).  This file is the pair-frame port of
`TailDualityInjective` (the genus ≥ 1 holomorphic-ω₀ specialization): the local coefficient
of `h·dg₀` in the canonical chart at `p` is
`pairCoeffFun g₀ h p = (h ∘ chart⁻¹) · (g₀ ∘ chart⁻¹)'` — the integrand of the genus-free
pair-form residue theorem, so the whole chain runs in every genus.

Contents:
* `pairOrderAt g₀ p` — the local order of `dg₀` (= `formOrderW (differentialForm g₀)`, the
  order bridge `pairOrderAt_eq_formOrderW`); finite everywhere for nonconstant `g₀`.
* `pairCanonicalDivisor g₀ hg₀` — the canonical divisor `K = div (dg₀)`
  (from `exists_differentialForm_divisor`).
* the order bridge `pairOrderBounded_iff_mem`: `h·dg₀ ∈ L^(1)(−D) ⟺ h ∈ L(K−D)`.
* the residue-weight linearity lemmas and the descended **duality pairing**
  `pairDualMap : lSysModule (K−D) →ₗ (H¹(D))*` (descent input = the genus-free
  `tailResidue_tailMap_eq_zero`).
* **Injectivity** (Miranda p. 188): a nonzero class `[h]` pairs against the single-monomial tail
  `z^{−1−o}·p` to the *leading Laurent coefficient*, nonzero by `laurentCoeff_order_ne_zero`.
  Hence the easy half of duality: `lDim (K − D) ≤ h1TailDim D` — no genus hypothesis.

The surjective half (Miranda pp. 189–191) is built separately in `PairDualitySurjective`.
-/
import Jacobians.CanonicalForms.CanonicalFormDifferential
import Jacobians.LaurentTail.Finiteness
import Jacobians.SerrePairing.SerreDuality
import Jacobians.TailDuality.TailResidue
open scoped Manifold ContDiff Topology
open Filter Set
open Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace

namespace Jacobians.LaurentTail

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ### §1 The order of `dg₀` and the canonical divisor `K = div (dg₀)` -/

/-- The order of the canonical 1-form `dg₀` at `p`: the meromorphic order of the chart-pullback
derivative `(g₀ ∘ chart⁻¹)'` at the chart centre (the pair-frame analog of `omegaOrderAt`). -/
noncomputable def pairOrderAt (g₀ : MeromorphicFunction X) (p : X) : WithTop ℤ :=
  meromorphicOrderAt (deriv (g₀.toFun ∘ (chartAt (H := ℂ) p).symm)) ((chartAt (H := ℂ) p) p)

/-- The order of the pair integrand is the order of `dg₀` plus the order of `h`. -/
theorem meromorphicOrderAt_pairCoeffFun (g₀ h : MeromorphicFunction X) (p : X) :
    meromorphicOrderAt (pairCoeffFun g₀ h p) ((chartAt (H := ℂ) p) p)
      = pairOrderAt g₀ p + h.orderW p := by
  rw [show meromorphicOrderAt (pairCoeffFun g₀ h p) ((chartAt (H := ℂ) p) p)
        = h.orderW p + pairOrderAt g₀ p from
      meromorphicOrderAt_mul (h.meromorphic p) ((g₀.meromorphic p).deriv),
    add_comm]

/-- The weight vanishes for germ-zero `h`. -/
theorem tailResidueWeight_eq_zero_of_germZero (g₀ : MeromorphicFunction X)
    {h : MeromorphicFunction X} (hh : ∀ x, h.orderW x = ⊤) (q : X × ℤ) :
    tailResidueWeight g₀ h q = 0 := by
  have hev : (fun _ : ℂ => (0 : ℂ)) =ᶠ[𝓝[≠] ((chartAt (H := ℂ) q.1) q.1)]
      pairCoeffFun g₀ h q.1 := by
    have h0 := meromorphicOrderAt_eq_top_iff.mp (hh q.1)
    filter_upwards [h0] with z hz
    show (0 : ℂ) = h.toFun ((chartAt (H := ℂ) q.1).symm z)
      * deriv (fun w => g₀.toFun ((chartAt (H := ℂ) q.1).symm w)) z
    rw [show h.toFun ((chartAt (H := ℂ) q.1).symm z)
      = (h.toFun ∘ (chartAt (H := ℂ) q.1).symm) z from rfl, hz, zero_mul]
  rw [tailResidueWeight, ← laurentCoeff_congr hev, laurentCoeff_def]
  have h0 : (fun z => (fun _ : ℂ => (0 : ℂ)) z
      * (z - ((chartAt (H := ℂ) q.1) q.1)) ^ (-(-1 - q.2) - 1)) = fun _ : ℂ => (0 : ℂ) := by
    funext z
    ring
  rw [h0]
  exact Jacobians.Dolbeault.resAt_eq_zero_of_analyticAt analyticAt_const

/-- `pairOrderAt` is the form order of the genuine meromorphic 1-form `dg₀`
(`CanonicalFormDifferential.formOrderW_differentialForm`). -/
theorem pairOrderAt_eq_formOrderW [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (g₀ : MeromorphicFunction X) (p : X) :
    pairOrderAt g₀ p = (differentialForm g₀).formOrderW p :=
  (formOrderW_differentialForm g₀ p).symm

/-- For nonconstant `g₀`, the order of `dg₀` is finite at every point: `dg₀ ≠ 0` somewhere
(`differentialForm_ne_zero`) and the form identity theorem spreads it everywhere. -/
theorem pairOrderAt_ne_top [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (g₀ : MeromorphicFunction X) (hg₀ : ¬ IsGermConstant g₀) (p : X) :
    pairOrderAt g₀ p ≠ ⊤ := by
  rw [pairOrderAt_eq_formOrderW]
  exact MeromorphicOneForm.formOrderW_ne_top_of_exists (differentialForm g₀)
    (differentialForm_ne_zero hg₀) p

/-- **The canonical divisor `K = div (dg₀)`** (Miranda p. 186; Forster 17.4): the divisor of the
nonzero meromorphic 1-form `dg₀`, via `exists_differentialForm_divisor`. -/
noncomputable def pairCanonicalDivisor [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (g₀ : MeromorphicFunction X)
    (hg₀ : ¬ IsGermConstant g₀) : Divisor X :=
  (exists_differentialForm_divisor g₀ (differentialForm_ne_zero hg₀)).choose

/-- `K = div (dg₀)` reads the form order of `dg₀` (the defining property, for the §17.4 datum). -/
theorem formOrderW_pairCanonicalDivisor [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (g₀ : MeromorphicFunction X)
    (hg₀ : ¬ IsGermConstant g₀) (p : X) :
    (differentialForm g₀).formOrderW p = ((pairCanonicalDivisor g₀ hg₀ p : ℤ) : WithTop ℤ) :=
  (exists_differentialForm_divisor g₀ (differentialForm_ne_zero hg₀)).choose_spec p

/-- The canonical divisor reads the order: `(K p : WithTop ℤ) = pairOrderAt g₀ p`. -/
theorem coe_pairCanonicalDivisor [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (g₀ : MeromorphicFunction X) (hg₀ : ¬ IsGermConstant g₀)
    (p : X) :
    ((pairCanonicalDivisor g₀ hg₀ p : ℤ) : WithTop ℤ) = pairOrderAt g₀ p := by
  rw [pairOrderAt_eq_formOrderW]
  exact (formOrderW_pairCanonicalDivisor g₀ hg₀ p).symm

/-! ### §2 The order bridge: `h·dg₀ ∈ L^(1)(−D) ⟺ h ∈ L(K−D)` -/

/-- **The order bridge** (Miranda p. 187): `h·dg₀` has order ≥ `D` everywhere iff
`h ∈ L(K − D)` for the canonical divisor `K = div (dg₀)`. -/
theorem pairOrderBounded_iff_mem [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (g₀ : MeromorphicFunction X) (hg₀ : ¬ IsGermConstant g₀)
    (h : MeromorphicFunction X) (D : Divisor X) :
    PairOrderBounded g₀ h D
      ↔ h ∈ linearSystem (X := X) (pairCanonicalDivisor g₀ hg₀ - D) := by
  have hmem : ∀ p : X, ((pairCanonicalDivisor g₀ hg₀ - D) p : ℤ) =
      pairCanonicalDivisor g₀ hg₀ p - D p := fun p => Finsupp.sub_apply _ _ _
  constructor
  · intro hbd p
    have h1 := hbd p
    rw [meromorphicOrderAt_pairCoeffFun] at h1
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (pairOrderAt_ne_top g₀ hg₀ p)
    have hKp : pairCanonicalDivisor g₀ hg₀ p = k := by
      have hc := coe_pairCanonicalDivisor g₀ hg₀ p
      rw [← hk] at hc
      exact_mod_cast hc
    rcases eq_or_ne (h.orderW p) ⊤ with htop | hne
    · rw [htop]; exact le_top
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hk, ← hm, ← WithTop.coe_add] at h1
    have h2 : (D p : ℤ) ≤ k + m := by exact_mod_cast h1
    rw [← hm]
    have h3 : (-((pairCanonicalDivisor g₀ hg₀ - D) p) : ℤ) ≤ m := by
      rw [hmem p, hKp]; omega
    exact_mod_cast h3
  · intro hLS p
    have h1 : (-((pairCanonicalDivisor g₀ hg₀ - D) p) : WithTop ℤ) ≤ h.orderW p := hLS p
    rw [meromorphicOrderAt_pairCoeffFun]
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (pairOrderAt_ne_top g₀ hg₀ p)
    have hKp : pairCanonicalDivisor g₀ hg₀ p = k := by
      have hc := coe_pairCanonicalDivisor g₀ hg₀ p
      rw [← hk] at hc
      exact_mod_cast hc
    rcases eq_or_ne (h.orderW p) ⊤ with htop | hne
    · rw [htop, ← hk, WithTop.add_top]; exact le_top
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [← hm] at h1
    have h2 : (-((pairCanonicalDivisor g₀ hg₀ - D) p) : ℤ) ≤ m := by exact_mod_cast h1
    rw [hmem p, hKp] at h2
    rw [← hk, ← hm, ← WithTop.coe_add]
    exact_mod_cast (by omega : (D p : ℤ) ≤ k + m)

/-! ### §3 Linearity of the residue weight in `h` -/

/-- The weight is additive in `h`. -/
theorem tailResidueWeight_add [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (g₀ h₁ h₂ : MeromorphicFunction X) (q : X × ℤ) :
    tailResidueWeight g₀ (h₁ + h₂) q
      = tailResidueWeight g₀ h₁ q + tailResidueWeight g₀ h₂ q := by
  rw [tailResidueWeight, tailResidueWeight, tailResidueWeight,
    ← laurentCoeff_add (meromorphicAt_pairCoeffFun g₀ h₁ q.1)
      (meromorphicAt_pairCoeffFun g₀ h₂ q.1)]
  refine laurentCoeff_congr (Eventually.of_forall fun z => ?_) _
  show pairCoeffFun g₀ (h₁ + h₂) q.1 z
    = pairCoeffFun g₀ h₁ q.1 z + pairCoeffFun g₀ h₂ q.1 z
  simp only [pairCoeffFun, MeromorphicFunction.add_toFun, Pi.add_apply]
  ring

/-- The weight is homogeneous in `h`. -/
theorem tailResidueWeight_smul [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (g₀ : MeromorphicFunction X) (a : ℂ)
    (h : MeromorphicFunction X) (q : X × ℤ) :
    tailResidueWeight g₀ (a • h) q = a * tailResidueWeight g₀ h q := by
  rw [tailResidueWeight, tailResidueWeight,
    ← laurentCoeff_smul a (meromorphicAt_pairCoeffFun g₀ h q.1)]
  refine laurentCoeff_congr (Eventually.of_forall fun z => ?_) _
  show pairCoeffFun g₀ (a • h) q.1 z = (a • pairCoeffFun g₀ h q.1) z
  simp only [pairCoeffFun, MeromorphicFunction.smul_toFun, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### §4 The duality pairing and injectivity (Miranda p. 188) -/

/-- **The Serre duality pairing, on representatives**: for `h ∈ L(K−D)` the descended residue
functional on `H¹(D)` (descent = the genus-free `tailResidue_tailMap_eq_zero`). -/
noncomputable def pairDualFun [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (g₀ : MeromorphicFunction X) (hg₀ : ¬ IsGermConstant g₀)
    (D : Divisor X)
    (h : ↥(linearSystem (X := X) (pairCanonicalDivisor g₀ hg₀ - D))) :
    Module.Dual ℂ (mittagLefflerH1 (X := X) D) :=
  Submodule.liftQ _ ((tailResidue g₀ h.1).comp (Submodule.subtype _)) (by
    rintro Z ⟨f, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, tailMapCo_coe]
    exact tailResidue_tailMap_eq_zero g₀ h.1
      ((pairOrderBounded_iff_mem g₀ hg₀ h.1 D).mpr h.2) f)

@[simp] theorem pairDualFun_mk [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (g₀ : MeromorphicFunction X) (hg₀ : ¬ IsGermConstant g₀)
    (D : Divisor X)
    (h : ↥(linearSystem (X := X) (pairCanonicalDivisor g₀ hg₀ - D)))
    (Z : ↥(tailSubspace (X := X) D)) :
    pairDualFun g₀ hg₀ D h (Submodule.Quotient.mk Z)
      = tailResidue g₀ h.1 (Z : TailSpace X) :=
  rfl

/-- The pairing bundled as a linear map `L(K−D) →ₗ (H¹(D))*` (linearity in `h` from the weight
linearity). -/
noncomputable def pairDualMapAux [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (g₀ : MeromorphicFunction X) (hg₀ : ¬ IsGermConstant g₀)
    (D : Divisor X) :
    ↥(linearSystem (X := X) (pairCanonicalDivisor g₀ hg₀ - D))
      →ₗ[ℂ] Module.Dual ℂ (mittagLefflerH1 (X := X) D) where
  toFun := pairDualFun g₀ hg₀ D
  map_add' h₁ h₂ := by
    refine LinearMap.ext fun ξ => ?_
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    rw [LinearMap.add_apply, pairDualFun_mk, pairDualFun_mk, pairDualFun_mk,
      tailResidue_apply, tailResidue_apply, tailResidue_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show ((h₁ + h₂ : ↥(linearSystem (X := X) (pairCanonicalDivisor g₀ hg₀ - D)))
        : MeromorphicFunction X) = (h₁ : MeromorphicFunction X) + h₂ from rfl,
      tailResidueWeight_add, mul_add]
  map_smul' a h := by
    refine LinearMap.ext fun ξ => ?_
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    rw [RingHom.id_apply, LinearMap.smul_apply, pairDualFun_mk, pairDualFun_mk,
      tailResidue_apply, tailResidue_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show ((a • h : ↥(linearSystem (X := X) (pairCanonicalDivisor g₀ hg₀ - D)))
        : MeromorphicFunction X) = a • (h : MeromorphicFunction X) from rfl,
      tailResidueWeight_smul]
    ring

/-- **The Serre duality pairing** `ι : L(K−D)/germ0 →ₗ (H¹(D))*` (Miranda Thm 3.3's map, on the
junk-free quotient that defines `lDim`). -/
noncomputable def pairDualMap [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (g₀ : MeromorphicFunction X) (hg₀ : ¬ IsGermConstant g₀)
    (D : Divisor X) :
    (↥(linearSystem (X := X) (pairCanonicalDivisor g₀ hg₀ - D))
        ⧸ (germZeroSubmodule (X := X)).submoduleOf
            (linearSystem (X := X) (pairCanonicalDivisor g₀ hg₀ - D)))
      →ₗ[ℂ] Module.Dual ℂ (mittagLefflerH1 (X := X) D) :=
  Submodule.liftQ _ (pairDualMapAux g₀ hg₀ D) (by
    intro h hmem
    have hger : ∀ x, (h : MeromorphicFunction X).orderW x = ⊤ := hmem
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun ξ => ?_
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    show pairDualFun g₀ hg₀ D h (Submodule.Quotient.mk Z) = 0
    rw [pairDualFun_mk, tailResidue_apply]
    exact Finset.sum_eq_zero fun q _ => by
      rw [tailResidueWeight_eq_zero_of_germZero g₀ hger q, mul_zero])

/-- **Injectivity of the duality pairing** (Miranda Thm 3.3, p. 188): a class `[h] ≠ 0` pairs
against the single-monomial tail `z^{−1−o}·p` (at a point `p` where `h`'s germ survives, `o` the
local order of `h·dg₀`) to the leading Laurent coefficient — nonzero by
`laurentCoeff_order_ne_zero`. -/
theorem pairDualMap_injective [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] (g₀ : MeromorphicFunction X) (hg₀ : ¬ IsGermConstant g₀)
    (D : Divisor X) :
    Function.Injective (pairDualMap g₀ hg₀ D) := by
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
  -- the (finite) order of the integrand `h·dg₀` at `p`
  have hfin : meromorphicOrderAt (pairCoeffFun g₀ (h : MeromorphicFunction X) p)
      ((chartAt (H := ℂ) p) p) ≠ ⊤ := by
    rw [meromorphicOrderAt_pairCoeffFun]
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (pairOrderAt_ne_top g₀ hg₀ p)
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hp
    rw [← hk, ← hm, ← WithTop.coe_add]
    exact WithTop.coe_ne_top
  obtain ⟨o, ho⟩ := WithTop.ne_top_iff_exists.mp hfin
  -- membership gives `D p ≤ o`
  have hDo : D p ≤ o := by
    have hbd := (pairOrderBounded_iff_mem g₀ hg₀ (h : MeromorphicFunction X) D).mpr h.2 p
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
  have hval : tailResidue g₀ (h : MeromorphicFunction X)
      (Finsupp.single ((p, -1 - o) : X × ℤ) (1 : ℂ))
      = laurentCoeff (pairCoeffFun g₀ (h : MeromorphicFunction X) p)
          ((chartAt (H := ℂ) p) p) o := by
    rw [tailResidue_apply, Finsupp.support_single _ one_ne_zero,
      Finset.sum_singleton, Finsupp.single_eq_same, one_mul, tailResidueWeight]
    congr 1
    omega
  -- the leading coefficient is nonzero
  have hne0 : laurentCoeff (pairCoeffFun g₀ (h : MeromorphicFunction X) p)
      ((chartAt (H := ℂ) p) p) o ≠ 0 :=
    laurentCoeff_order_ne_zero (meromorphicAt_pairCoeffFun g₀ _ p) ho.symm
  -- but the functional vanishes on the witness class
  have happ : pairDualMap g₀ hg₀ D (Submodule.Quotient.mk h)
      (Submodule.Quotient.mk ⟨Finsupp.single ((p, -1 - o) : X × ℤ) (1 : ℂ), hmemtail⟩)
      = 0 := by
    rw [hx]
    rfl
  rw [show pairDualMap g₀ hg₀ D (Submodule.Quotient.mk h)
      = pairDualFun g₀ hg₀ D h from rfl, pairDualFun_mk] at happ
  exact hne0 (hval ▸ happ)

end Jacobians.LaurentTail
