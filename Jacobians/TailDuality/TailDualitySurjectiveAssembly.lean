/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Serre duality for the tail `H¹`, the surjectivity assembly (Miranda Thm 3.3, pp. 189–191)

The pigeonhole half of Serre duality, Forster 17.9's count on Miranda's tail spaces.  Given
`0 ≠ φ : H¹(D)* `, fix a base point `P` and compare, inside `V_n := H¹(D − nP)*`, the two
subspaces

* `Λ_n` — the functionals `φ ∘ T̄_ψ` for `ψ ∈ L(nP)` (the multiplication action of
  `TailMultiplicationH1`); `Λ_n ≅ L(nP)/germ0` since `φ ∘ T̄_ψ ≠ 0` for surviving `ψ`
  (`comp_tailMulH1_ne_zero`), so `dim Λ_n ≥ n + 1 − h¹(0)` by RR-I;
* `I_n` — the residue functionals `Res_{h·ω₀}`, `h ∈ L(K − (D − nP))` (the range of
  `omegaDualMap` at `D − nP`); `dim I_n = l(K − D + nP) ≥ deg K − deg D + n + 1 − h¹(0)` by RR-I.

For `n > deg D` RR-I pins `dim V_n = n − deg D − 1 + h¹(0)` (negative degree kills `l`), so for
`n` large the two subspaces meet in a nonzero functional `φ ∘ T̄_ψ = Res_{h·ω₀}`.  The recovery
step (Miranda pp. 190–191) then pulls `φ` back along `μ_{ψ⁻¹}`: the composite identity turns
`T̄_ψ ∘ μ̄_{ψ⁻¹}` into the truncation, μ-compatibility turns `Res_{h·ω₀} ∘ μ_{ψ⁻¹}` into
`Res_{(ψ⁻¹h)·ω₀}`,
and Miranda Lemma 3.6 (`omegaOrderBounded_of_vanishing`) downgrades the order bound of
`ψ⁻¹h` from the fine level to `D` — exhibiting `φ = Res_{(ψ⁻¹h)·ω₀}` with `ψ⁻¹h ∈ L(K − D)`.

Headlines: `omegaDualMap_surjective` and the dimension identity
`h1TailDim_eq_lDim_canonical_sub : h¹(D) = l(K − D)`.
-/
import Jacobians.LaurentTail.RiemannRochFirstForm
import Jacobians.TailDuality.TailDualitySurjective
import Jacobians.ProperDegree.LinearSystemDegree

open scoped Manifold ContDiff Topology
open Filter Set Module
open Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace

namespace Jacobians.LaurentTail

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ### §1 The multiplication operator is linear in the multiplier -/

/-- `μ_ψ(Z)` is **additive in the multiplier** `ψ`: the Laurent coefficients of
`(ψ₁ + ψ₂)·(tail polynomial)` split (`laurentCoeff_add`). -/
theorem tailMul_add_multiplier (ψ₁ ψ₂ : MeromorphicFunction X) (E : Divisor X)
    (Z : TailSpace X) :
    tailMul (ψ₁ + ψ₂) E Z = tailMul ψ₁ E Z + tailMul ψ₂ E Z := by
  classical
  ext q
  rw [Finsupp.add_apply, tailMul_apply, tailMul_apply, tailMul_apply]
  split_ifs with hlt
  · have hfun : (fun z => (ψ₁ + ψ₂).toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z)
        = (fun z => ψ₁.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z)
          + (fun z => ψ₂.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z) := by
      funext z
      show (ψ₁ + ψ₂).toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z
        = ψ₁.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z
          + ψ₂.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z
      rw [MeromorphicFunction.add_toFun, Pi.add_apply]
      ring
    rw [hfun, laurentCoeff_add (meromorphicAt_psi_mul_tailFnAt ψ₁ Z q.1)
      (meromorphicAt_psi_mul_tailFnAt ψ₂ Z q.1)]
  · rw [add_zero]

/-- `μ_ψ(Z)` is **homogeneous in the multiplier** `ψ`. -/
theorem tailMul_smul_multiplier (a : ℂ) (ψ : MeromorphicFunction X) (E : Divisor X)
    (Z : TailSpace X) :
    tailMul (a • ψ) E Z = a • tailMul ψ E Z := by
  classical
  ext q
  rw [Finsupp.smul_apply, tailMul_apply, tailMul_apply]
  split_ifs with hlt
  · have hfun : (fun z => (a • ψ).toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z)
        = a • fun z => ψ.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z := by
      funext z
      show (a • ψ).toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z
        = a * (ψ.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z)
      rw [MeromorphicFunction.smul_toFun, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun, laurentCoeff_smul a (meromorphicAt_psi_mul_tailFnAt ψ Z q.1), smul_eq_mul]
  · rw [smul_zero]

/-- For a **germ-zero multiplier** the operator vanishes: `ψ·(tail polynomial)` is eventually `0`
on every punctured chart neighbourhood, so all its Laurent coefficients vanish. -/
theorem tailMul_eq_zero_of_germZero {ψ : MeromorphicFunction X}
    (hψ : ∀ x, ψ.orderW x = ⊤) (E : Divisor X) (Z : TailSpace X) :
    tailMul ψ E Z = 0 := by
  classical
  ext q
  rw [Finsupp.coe_zero, Pi.zero_apply, tailMul_apply]
  split_ifs with hlt
  · have h0 : (fun z => ψ.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z)
        =ᶠ[𝓝[≠] ((chartAt (H := ℂ) q.1) q.1)] (0 : ℂ → ℂ) := by
      have hev := meromorphicOrderAt_eq_top_iff.mp (hψ q.1)
      filter_upwards [hev] with z hz
      show ψ.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z = 0
      rw [show ψ.toFun ((chartAt (H := ℂ) q.1).symm z)
        = (ψ.toFun ∘ (chartAt (H := ℂ) q.1).symm) z from rfl, hz, zero_mul]
    rw [laurentCoeff_congr h0, laurentCoeff_zero]
  · rfl

variable [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §2 The Λ-side dual map `ψ ↦ φ ∘ T̄_ψ` on `L(C)/germ0` -/

section LambdaSide

variable {B : Divisor X} (φ : Module.Dual ℂ (mittagLefflerH1 (X := X) B)) (C : Divisor X)

/-- The Λ-side assignment on representatives: `ψ ∈ L(C) ↦ φ ∘ T̄_ψ : H¹(B − C) → ℂ`
(`T̄_ψ : H¹(B − C) → H¹(B)` by the level condition `mulLevelLE_of_mem`).  Linear in `ψ`
because `μ_ψ` is (`tailMul_add_multiplier`/`tailMul_smul_multiplier`). -/
noncomputable def tailMulDual :
    ↥(linearSystem (X := X) C) →ₗ[ℂ] Module.Dual ℂ (mittagLefflerH1 (X := X) (B - C)) where
  toFun ψ := φ.comp (tailMulH1 (ψ : MeromorphicFunction X) (mulLevelLE_of_mem ψ.2 B))
  map_add' ψ₁ ψ₂ := by
    refine LinearMap.ext fun ξ => ?_
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    have hco : tailMulCo ((ψ₁ + ψ₂ : ↥(linearSystem (X := X) C)) : MeromorphicFunction X)
        (B - C) B Z
        = tailMulCo (ψ₁ : MeromorphicFunction X) (B - C) B Z
          + tailMulCo (ψ₂ : MeromorphicFunction X) (B - C) B Z := by
      refine Subtype.ext ?_
      simp only [AddMemClass.coe_add, tailMulCo_coe]
      exact tailMul_add_multiplier (ψ₁ : MeromorphicFunction X) (ψ₂ : MeromorphicFunction X)
        B (Z : TailSpace X)
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      tailMulH1_mk, tailMulH1_mk, tailMulH1_mk, hco, ← map_add φ, ← Submodule.Quotient.mk_add]
  map_smul' a ψ := by
    refine LinearMap.ext fun ξ => ?_
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    have hco : tailMulCo ((a • ψ : ↥(linearSystem (X := X) C)) : MeromorphicFunction X)
        (B - C) B Z
        = a • tailMulCo (ψ : MeromorphicFunction X) (B - C) B Z := by
      refine Subtype.ext ?_
      simp only [SetLike.val_smul, tailMulCo_coe]
      exact tailMul_smul_multiplier a (ψ : MeromorphicFunction X) B (Z : TailSpace X)
    rw [RingHom.id_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      tailMulH1_mk, tailMulH1_mk, hco, ← map_smul φ, ← Submodule.Quotient.mk_smul]

@[simp] theorem tailMulDual_apply (ψ : ↥(linearSystem (X := X) C)) :
    tailMulDual φ C ψ
      = φ.comp (tailMulH1 (ψ : MeromorphicFunction X) (mulLevelLE_of_mem ψ.2 B)) := rfl

/-- A germ-zero multiplier is sent to the zero functional. -/
theorem tailMulDual_eq_zero_of_germZero (ψ : ↥(linearSystem (X := X) C))
    (hψ : ∀ x, (ψ : MeromorphicFunction X).orderW x = ⊤) :
    tailMulDual φ C ψ = 0 := by
  refine LinearMap.ext fun ξ => ?_
  obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [tailMulDual_apply, LinearMap.comp_apply, tailMulH1_mk, LinearMap.zero_apply]
  have hco : tailMulCo (ψ : MeromorphicFunction X) (B - C) B Z = 0 := by
    refine Subtype.ext ?_
    rw [tailMulCo_coe, tailMul_eq_zero_of_germZero hψ B (Z : TailSpace X)]
    rfl
  rw [hco, Submodule.Quotient.mk_zero, map_zero]

/-- The Λ-side dual map **descended to the junk-free quotient** `L(C)/germ0` (the space whose
`finrank` is `lDim C`). -/
noncomputable def tailMulDualQ :
    lSysModule (X := X) C →ₗ[ℂ] Module.Dual ℂ (mittagLefflerH1 (X := X) (B - C)) :=
  Submodule.liftQ _ (tailMulDual φ C) (by
    intro ψ hψ
    rw [LinearMap.mem_ker]
    exact tailMulDual_eq_zero_of_germZero φ C ψ fun x => hψ x)

@[simp] theorem tailMulDualQ_mk (ψ : ↥(linearSystem (X := X) C)) :
    tailMulDualQ φ C (Submodule.Quotient.mk ψ) = tailMulDual φ C ψ :=
  Submodule.liftQ_apply _ _ ψ

/-- For `φ ≠ 0` the Λ-side dual map is **injective** (Forster 17.8: `φ ∘ T̄_ψ ≠ 0` whenever the
germ of `ψ` survives). -/
theorem tailMulDualQ_injective (hφ : φ ≠ 0) :
    Function.Injective (tailMulDualQ φ C) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero]
  by_contra hcon
  have hex : ∃ p : X, (ψ : MeromorphicFunction X).orderW p ≠ ⊤ := by
    by_contra hall
    push Not at hall
    exact hcon fun x => hall x
  rw [tailMulDualQ_mk, tailMulDual_apply] at hx
  exact comp_tailMulH1_ne_zero φ hφ (ψ : MeromorphicFunction X) hex
    (mulLevelLE_of_mem ψ.2 B) hx

/-- `dim Λ = l(C)` for `φ ≠ 0`. -/
theorem finrank_range_tailMulDualQ (hφ : φ ≠ 0) :
    finrank ℂ ↥(LinearMap.range (tailMulDualQ φ C)) = lDim (X := X) C :=
  LinearMap.finrank_range_of_inj (tailMulDualQ_injective φ C hφ)

end LambdaSide

/-- `dim I = l(K − D)`: the range of the (injective) residue pairing has the dimension of its
source `L(K − D)/germ0`. -/
theorem finrank_range_omegaDualMap (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0)
    (D : Divisor X) :
    finrank ℂ ↥(LinearMap.range (omegaDualMap ω₀ hω₀ D))
      = lDim (X := X) (canonicalDivisorOf ω₀ hω₀ - D) :=
  LinearMap.finrank_range_of_inj (omegaDualMap_injective ω₀ hω₀ D)

/-! ### §3 The recovery step (Miranda pp. 190–191) -/

/-- **The recovery step** (Miranda Thm 3.3, surjectivity, second half): if `φ ∘ T̄_ψ` is the
residue functional of `h·ω₀` at the finer level `D − C` (with `ψ ∈ L(C)` of surviving germ),
then `φ` itself is the residue functional of `(ψ⁻¹h)·ω₀` at level `D`:

* the composite identity turns `T̄_ψ ∘ μ_{ψ⁻¹}` into the truncation `𝒯[D−C−div ψ] → 𝒯[D]`,
* μ-compatibility (`omegaTailResidue_tailMul`) turns `Res_{h·ω₀} ∘ μ_{ψ⁻¹}` into
  `Res_{(ψ⁻¹h)·ω₀}`,
* Miranda Lemma 3.6 downgrades the order bound of `(ψ⁻¹h)·ω₀` from the fine level to `D`. -/
theorem omegaDualMap_recovery (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) {D C : Divisor X}
    (φ : Module.Dual ℂ (mittagLefflerH1 (X := X) D))
    (ψ : ↥(linearSystem (X := X) C))
    (hψ : ∃ p : X, (ψ : MeromorphicFunction X).orderW p ≠ ⊤)
    (h : ↥(linearSystem (X := X) (canonicalDivisorOf ω₀ hω₀ - (D - C))))
    (heq : φ.comp (tailMulH1 (ψ : MeromorphicFunction X) (mulLevelLE_of_mem ψ.2 D))
      = omegaDualFun ω₀ hω₀ (D - C) h) :
    ∃ g : ↥(linearSystem (X := X) (canonicalDivisorOf ω₀ hω₀ - D)),
      omegaDualMap ω₀ hω₀ D (Submodule.Quotient.mk g) = φ := by
  classical
  have hψfin : ∀ p : X, (ψ : MeromorphicFunction X).orderW p ≠ ⊤ :=
    MeromorphicFunction.orderW_ne_top_of_exists _ hψ
  -- the level condition for `μ_{ψ⁻¹} : 𝒯[D − C − div ψ] → 𝒯[D − C]` (an exact shift)
  have hlev' : MulLevelLE ((ψ : MeromorphicFunction X)⁻¹)
      (D - C - ((ψ : MeromorphicFunction X).div : Divisor X)) (D - C) := by
    intro p
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (hψfin p)
    have hdiv : (((ψ : MeromorphicFunction X).div : Divisor X)) p = m := by
      rw [div_apply, ← hm, WithTop.untop₀_coe]
    have hpt : (D - C - ((ψ : MeromorphicFunction X).div : Divisor X)) p - (D - C) p = -m := by
      rw [Finsupp.sub_apply, hdiv]
      ring
    have hinv : ((ψ : MeromorphicFunction X)⁻¹).orderW p = ((-m : ℤ) : WithTop ℤ) := by
      rw [MeromorphicFunction.orderW_inv, ← hm]
      rfl
    rw [hpt, hinv]
  have hordh : OmegaOrderBounded ω₀ (h : MeromorphicFunction X) (D - C) :=
    (omegaOrderBounded_iff_mem ω₀ hω₀ _ (D - C)).mpr h.2
  have hordg : OmegaOrderBounded ω₀
      ((ψ : MeromorphicFunction X)⁻¹ * (h : MeromorphicFunction X))
      (D - C - ((ψ : MeromorphicFunction X).div : Divisor X)) :=
    omegaOrderBounded_mul ω₀ (h : MeromorphicFunction X) ((ψ : MeromorphicFunction X)⁻¹)
      hordh hlev'
  -- the fine level sits below `D`: `div ψ ≥ −C` pointwise
  have hD'le : (D - C - ((ψ : MeromorphicFunction X).div : Divisor X)) ≤ D := by
    intro p
    have hψm : ((-(C p) : ℤ) : WithTop ℤ) ≤ (ψ : MeromorphicFunction X).orderW p := ψ.2 p
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (hψfin p)
    have hdiv : (((ψ : MeromorphicFunction X).div : Divisor X)) p = m := by
      rw [div_apply, ← hm, WithTop.untop₀_coe]
    rw [← hm] at hψm
    have hCm : -(C p) ≤ m := by exact_mod_cast hψm
    have hpt : (D - C - ((ψ : MeromorphicFunction X).div : Divisor X)) p
        = D p - C p - m := by
      rw [Finsupp.sub_apply, Finsupp.sub_apply, hdiv]
    rw [hpt]
    omega
  -- the bridge: `φ` reads through the truncation as the `(ψ⁻¹h)`-residue on the fine tails
  have hkey : ∀ V : TailSpace X,
      V ∈ tailSubspace (X := X) (D - C - ((ψ : MeromorphicFunction X).div : Divisor X)) →
      φ (Submodule.Quotient.mk
        ⟨truncateRaw (X := X) D V, truncateRaw_mem_tailSubspace D V⟩)
        = omegaTailResidue ω₀
            ((ψ : MeromorphicFunction X)⁻¹ * (h : MeromorphicFunction X)) V := by
    intro V hV
    have hZmem : tailMul ((ψ : MeromorphicFunction X)⁻¹) (D - C) V
        ∈ tailSubspace (X := X) (D - C) := tailMulRaw_mem _ _ _
    have h1 := LinearMap.congr_fun heq
      (Submodule.Quotient.mk (⟨tailMul ((ψ : MeromorphicFunction X)⁻¹) (D - C) V, hZmem⟩ :
        ↥(tailSubspace (X := X) (D - C))))
    rw [LinearMap.comp_apply, tailMulH1_mk, omegaDualFun_mk] at h1
    -- left side: the composite `μ_ψ ∘ μ_{ψ⁻¹}` is the truncation
    have hcls : tailMulCo (ψ : MeromorphicFunction X) (D - C) D
        ⟨tailMul ((ψ : MeromorphicFunction X)⁻¹) (D - C) V, hZmem⟩
        = ⟨truncateRaw (X := X) D V, truncateRaw_mem_tailSubspace D V⟩ := by
      refine Subtype.ext ?_
      rw [tailMulCo_coe]
      exact tailMul_tailMul_inv_trunc (ψ : MeromorphicFunction X) hψ
        (mulLevelLE_of_mem ψ.2 D) V
    rw [hcls] at h1
    -- right side: μ-compatibility turns the `μ_{ψ⁻¹}`-image residue into the `ψ⁻¹h`-residue
    rw [show ((⟨tailMul ((ψ : MeromorphicFunction X)⁻¹) (D - C) V, hZmem⟩ :
        ↥(tailSubspace (X := X) (D - C))) : TailSpace X)
        = tailMul ((ψ : MeromorphicFunction X)⁻¹) (D - C) V from rfl,
      omegaTailResidue_tailMul ω₀ (h : MeromorphicFunction X)
        ((ψ : MeromorphicFunction X)⁻¹) hordh hlev' hV] at h1
    exact h1
  -- Miranda Lemma 3.6: the order bound downgrades to `D`
  have hordgD : OmegaOrderBounded ω₀
      ((ψ : MeromorphicFunction X)⁻¹ * (h : MeromorphicFunction X)) D := by
    refine omegaOrderBounded_of_vanishing ω₀ _ hordg fun Z hZ h0 => ?_
    have hk := hkey Z hZ
    rw [← hk]
    have hzero : (⟨truncateRaw (X := X) D Z, truncateRaw_mem_tailSubspace D Z⟩ :
        ↥(tailSubspace (X := X) D)) = 0 := Subtype.ext h0
    rw [hzero, Submodule.Quotient.mk_zero, map_zero]
  have hgmem : (ψ : MeromorphicFunction X)⁻¹ * (h : MeromorphicFunction X)
      ∈ linearSystem (X := X) (canonicalDivisorOf ω₀ hω₀ - D) :=
    (omegaOrderBounded_iff_mem ω₀ hω₀ _ D).mp hordgD
  -- conclusion: `φ = Res_{(ψ⁻¹h)·ω₀}` on every class
  refine ⟨⟨_, hgmem⟩, ?_⟩
  refine LinearMap.ext fun ξ => ?_
  obtain ⟨W, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  show omegaDualFun ω₀ hω₀ D ⟨_, hgmem⟩ (Submodule.Quotient.mk W)
    = φ (Submodule.Quotient.mk W)
  rw [omegaDualFun_mk]
  have hWD' : (W : TailSpace X)
      ∈ tailSubspace (X := X) (D - C - ((ψ : MeromorphicFunction X).div : Divisor X)) :=
    tailSubspace_anti hD'le W.2
  have h2 := hkey (W : TailSpace X) hWD'
  have hWtr : (⟨truncateRaw (X := X) D (W : TailSpace X),
      truncateRaw_mem_tailSubspace D (W : TailSpace X)⟩ : ↥(tailSubspace (X := X) D)) = W :=
    Subtype.ext (truncateRaw_eq_self_of_mem W.2)
  rw [hWtr] at h2
  exact h2.symm

/-! ### §4 Surjectivity (Miranda Thm 3.3 / Forster 17.9) -/

/-- **Serre duality for the tail `H¹`, the surjective half** (Miranda Thm 3.3, pp. 189–191;
Forster 17.9): every functional on the Mittag-Leffler `H¹(D)` is a residue functional
`Res_{h·ω₀}` with `h ∈ L(K − D)`.  Pigeonhole on `H¹(D − nP)*` between the multiplication
functionals `φ ∘ T̄_ψ` (`ψ ∈ L(nP)`) and the residue functionals, with the RR-I counts; then
the recovery step pulls the matched functional back to level `D`. -/
theorem omegaDualMap_surjective (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0) (D : Divisor X) :
    Function.Surjective (omegaDualMap ω₀ hω₀ D) := by
  classical
  intro φ
  rcases eq_or_ne φ 0 with rfl | hφ
  · exact ⟨0, map_zero _⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty X)
  -- the pole budget `n`: large enough for both RR-I counts
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, Divisor.deg X D < (n : ℤ)
      ∧ 3 * (h1TailDim (X := X) 0 : ℤ) - 3
          - Divisor.deg X (canonicalDivisorOf ω₀ hω₀) < (n : ℤ) := by
    refine ⟨(max (Divisor.deg X D) (3 * (h1TailDim (X := X) 0 : ℤ) - 3
      - Divisor.deg X (canonicalDivisorOf ω₀ hω₀))).toNat + 1, ?_, ?_⟩
    · have h1 := Int.self_le_toNat (max (Divisor.deg X D)
        (3 * (h1TailDim (X := X) 0 : ℤ) - 3 - Divisor.deg X (canonicalDivisorOf ω₀ hω₀)))
      have h2 : Divisor.deg X D ≤ max (Divisor.deg X D)
          (3 * (h1TailDim (X := X) 0 : ℤ) - 3
            - Divisor.deg X (canonicalDivisorOf ω₀ hω₀)) := le_max_left _ _
      push_cast
      omega
    · have h1 := Int.self_le_toNat (max (Divisor.deg X D)
        (3 * (h1TailDim (X := X) 0 : ℤ) - 3 - Divisor.deg X (canonicalDivisorOf ω₀ hω₀)))
      have h2 : 3 * (h1TailDim (X := X) 0 : ℤ) - 3
          - Divisor.deg X (canonicalDivisorOf ω₀ hω₀)
          ≤ max (Divisor.deg X D) (3 * (h1TailDim (X := X) 0 : ℤ) - 3
            - Divisor.deg X (canonicalDivisorOf ω₀ hω₀)) := le_max_right _ _
      push_cast
      omega
  -- dimension bookkeeping for the two subspaces of `H¹(D − nP)*`
  have hΛ := finrank_range_tailMulDualQ φ (Finsupp.single P (n : ℤ)) hφ
  have hI := finrank_range_omegaDualMap ω₀ hω₀ (D - Finsupp.single P (n : ℤ))
  have hdegC : Divisor.deg X (Finsupp.single P (n : ℤ)) = n := by
    rw [Divisor.deg_single]
  have hdegDn : Divisor.deg X (D - Finsupp.single P (n : ℤ)) = Divisor.deg X D - n := by
    rw [Divisor.deg_sub, hdegC]
  have hdegKDn : Divisor.deg X (canonicalDivisorOf ω₀ hω₀ - (D - Finsupp.single P (n : ℤ)))
      = Divisor.deg X (canonicalDivisorOf ω₀ hω₀) - Divisor.deg X D + n := by
    rw [Divisor.deg_sub, hdegDn]
    ring
  -- RR-I three times: the `Λ`-count, the `I`-count, and the ambient count
  have hRRC := riemannRoch_tailForm (X := X) (Finsupp.single P (n : ℤ))
  have hRRK := riemannRoch_tailForm (X := X)
    (canonicalDivisorOf ω₀ hω₀ - (D - Finsupp.single P (n : ℤ)))
  have hRRDn := riemannRoch_tailForm (X := X) (D - Finsupp.single P (n : ℤ))
  have hlDn : lDim (X := X) (D - Finsupp.single P (n : ℤ)) = 0 :=
    lDim_eq_zero_of_deg_neg _ (by omega)
  -- the pigeonhole: the two subspaces meet in a nonzero functional
  have hgt : finrank ℂ ↥(LinearMap.range (tailMulDualQ φ (Finsupp.single P (n : ℤ))))
      + finrank ℂ ↥(LinearMap.range (omegaDualMap ω₀ hω₀ (D - Finsupp.single P (n : ℤ))))
      > finrank ℂ (Module.Dual ℂ (mittagLefflerH1 (X := X)
          (D - Finsupp.single P (n : ℤ)))) := by
    rw [hΛ, hI, Subspace.dual_finrank_eq]
    have e1 : (0 : ℤ) ≤ (h1TailDim (X := X) (Finsupp.single P (n : ℤ)) : ℤ) :=
      Int.natCast_nonneg _
    have e2 : (0 : ℤ) ≤ (h1TailDim (X := X)
        (canonicalDivisorOf ω₀ hω₀ - (D - Finsupp.single P (n : ℤ))) : ℤ) :=
      Int.natCast_nonneg _
    have hcount : (h1TailDim (X := X) (D - Finsupp.single P (n : ℤ)) : ℤ)
        < (lDim (X := X) (Finsupp.single P (n : ℤ)) : ℤ)
          + (lDim (X := X)
              (canonicalDivisorOf ω₀ hω₀ - (D - Finsupp.single P (n : ℤ))) : ℤ) := by
      omega
    exact_mod_cast hcount
  have hne := SerreDuality.subspaces_inf_ne_bot_of_finrank_add_gt _ _ hgt
  obtain ⟨χ, hχmem, hχne⟩ := (Submodule.ne_bot_iff _).mp hne
  obtain ⟨hχΛ, hχI⟩ := Submodule.mem_inf.mp hχmem
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hχΛ
  obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨d, hd⟩ := LinearMap.mem_range.mp hχI
  obtain ⟨h, rfl⟩ := Submodule.Quotient.mk_surjective _ d
  -- the germ of `ψ` survives (else the matched functional were `0`)
  have hψex : ∃ p : X, (ψ : MeromorphicFunction X).orderW p ≠ ⊤ := by
    by_contra hall
    push Not at hall
    apply hχne
    rw [← hc, tailMulDualQ_mk]
    exact tailMulDual_eq_zero_of_germZero φ _ ψ hall
  -- the matched functional equation, and the recovery
  have heq : φ.comp (tailMulH1 (ψ : MeromorphicFunction X) (mulLevelLE_of_mem ψ.2 D))
      = omegaDualFun ω₀ hω₀ (D - Finsupp.single P (n : ℤ)) h := by
    have h1 : tailMulDualQ φ (Finsupp.single P (n : ℤ)) (Submodule.Quotient.mk ψ)
        = omegaDualMap ω₀ hω₀ (D - Finsupp.single P (n : ℤ)) (Submodule.Quotient.mk h) := by
      rw [hc, hd]
    rw [tailMulDualQ_mk, tailMulDual_apply] at h1
    exact h1
  obtain ⟨g, hg⟩ := omegaDualMap_recovery ω₀ hω₀ φ ψ hψex h heq
  exact ⟨Submodule.Quotient.mk g, hg⟩

/-! ### §5 The dimension identity `h¹(D) = l(K − D)` -/

/-- **Serre duality for the tail `H¹` as a dimension identity** (Miranda Thm 3.3):
`h¹(D) = l(K − D)` for the canonical divisor `K = div ω₀` of any nonzero holomorphic 1-form. -/
theorem h1TailDim_eq_lDim_canonical_sub (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0)
    (D : Divisor X) :
    h1TailDim (X := X) D = lDim (X := X) (canonicalDivisorOf ω₀ hω₀ - D) := by
  have e := LinearEquiv.ofBijective (omegaDualMap ω₀ hω₀ D)
    ⟨omegaDualMap_injective ω₀ hω₀ D, omegaDualMap_surjective ω₀ hω₀ D⟩
  have h := e.finrank_eq
  rw [Subspace.dual_finrank_eq] at h
  exact h.symm

end Jacobians.LaurentTail
