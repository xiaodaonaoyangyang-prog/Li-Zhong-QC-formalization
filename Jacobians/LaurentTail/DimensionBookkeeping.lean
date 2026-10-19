/-
  Miranda's Lemma 2.3 (Ch. VI §2, p. 181): the five-term exact chain

      `0 → L(D₁) → L(D₂) →^{α_{D₁}} ker t^{D₁}_{D₂} → H¹(D₁) → H¹(D₂) → 0`

  built by hand (no general snake lemma), with exactness at each spot, and the resulting
  **dimension identity** for `D₁ ≤ D₂`

      `dim ker(H¹(D₁) → H¹(D₂)) = (deg D₂ − l(D₂)) − (deg D₁ − l(D₁))`

  (`finrank_ker_mittagLefflerTruncate`).  Only the *finite-dimensional* pieces enter the
  rank–nullity bookkeeping — `ker t` (the monomial window) and the `L(D)`s (the Čech bridge);
  no finiteness of `H¹` is assumed.  The relative kernel `ker(H¹(D₁) → H¹(D₂))` is finite-
  dimensional *because* it is the image of the window (`finiteDimensional_ker_mittagLeffler-
  Truncate`), which is what later makes Miranda 2.6/2.7 (h¹ < ∞) and RR-I run.

  The maps (on the junk-free `lSysModule D = L(D)/germZero`, where `lDim` lives):
  inclusion; `α_{D₁}` (lands in `ker t` because `t ∘ α_{D₁} = α_{D₂}` kills `L(D₂)`); class-of;
  the induced truncation.
-/
import Jacobians.LaurentTail.TailMap
import Jacobians.LaurentTail.LinearSystemFiniteDimensional

open scoped Manifold ContDiff Topology
open Module

namespace Jacobians.LaurentTail

open Jacobians Jacobians.Dolbeault

/-! ### The chain maps -/

section LightInstances

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- `L(D)` is monotone in `D`: a deeper allowed pole set is a weaker constraint. -/
theorem linearSystem_mono {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    linearSystem (X := X) D₁ ≤ linearSystem (X := X) D₂ := by
  intro f hf x
  refine le_trans ?_ (hf x)
  exact_mod_cast neg_le_neg (h x)

/-- The inclusion `L(D₁)/germZero → L(D₂)/germZero` (first map of the chain). -/
noncomputable def lSysInclusion {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    lSysModule (X := X) D₁ →ₗ[ℂ] lSysModule (X := X) D₂ :=
  Submodule.mapQ _ _ (Submodule.inclusion (linearSystem_mono h)) fun _ hf => hf

@[simp] theorem lSysInclusion_mk {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂)
    (f : ↥(linearSystem (X := X) D₁)) :
    lSysInclusion h (Submodule.Quotient.mk f)
      = Submodule.Quotient.mk (Submodule.inclusion (linearSystem_mono h) f) :=
  Submodule.mapQ_apply _ _ _ f

/-- **Exactness at `L(D₁)`**: the inclusion of junk-free linear systems is injective. -/
theorem lSysInclusion_injective {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    Function.Injective (lSysInclusion (X := X) h) := by
  intro a b hab
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [lSysInclusion_mk, lSysInclusion_mk, Submodule.Quotient.eq] at hab
  rw [Submodule.Quotient.eq]
  exact hab

end LightInstances

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- `α_D` vanishes on an element iff it lies in `L(D)` (subtype form of `ker_tailMap`). -/
theorem tailMapCo_eq_zero_iff (D : Divisor X) (f : MeromorphicFunction X) :
    tailMapCo (X := X) D f = 0 ↔ f ∈ linearSystem (X := X) D := by
  rw [← ker_tailMap, LinearMap.mem_ker]
  exact ⟨fun h0 => congrArg Subtype.val h0, fun h0 => Subtype.ext h0⟩

/-- `α_{D₁}` restricted to `L(D₂)` lands in `ker t^{D₁}_{D₂}` (since `t ∘ α_{D₁} = α_{D₂}`
kills `L(D₂)`). -/
noncomputable def lSysToTailKernelAux {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    ↥(linearSystem (X := X) D₂) →ₗ[ℂ] ↥(LinearMap.ker (tailTruncate (X := X) D₁ D₂)) :=
  LinearMap.codRestrict _ ((tailMapCo D₁).comp (linearSystem (X := X) D₂).subtype) fun f => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
      tailTruncate_tailMapCo h]
    exact (tailMapCo_eq_zero_iff D₂ (f : MeromorphicFunction X)).mpr f.2

@[simp] theorem lSysToTailKernelAux_coe {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂)
    (f : ↥(linearSystem (X := X) D₂)) :
    ((lSysToTailKernelAux h f : ↥(tailSubspace (X := X) D₁)) : TailSpace X)
      = tailMap D₁ (f : MeromorphicFunction X) := rfl

/-- The second map of the chain: `α_{D₁} : L(D₂)/germZero → ker t^{D₁}_{D₂}` (well defined on
the junk-free quotient because germ-zero functions have no tail). -/
noncomputable def lSysToTailKernel {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    lSysModule (X := X) D₂ →ₗ[ℂ] ↥(LinearMap.ker (tailTruncate (X := X) D₁ D₂)) :=
  Submodule.liftQ _ (lSysToTailKernelAux h) fun f hf => by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    apply Subtype.ext
    rw [lSysToTailKernelAux_coe]
    exact LinearMap.mem_ker.mp (germZeroSubmodule_le_ker_tailMap D₁ hf)

@[simp] theorem lSysToTailKernel_mk {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂)
    (f : ↥(linearSystem (X := X) D₂)) :
    lSysToTailKernel h (Submodule.Quotient.mk f) = lSysToTailKernelAux h f :=
  Submodule.liftQ_apply _ _ f

/-- The third map of the chain: `ker t^{D₁}_{D₂} → H¹(D₁)`, the class-of map. -/
noncomputable def tailKernelToH1 (D₁ D₂ : Divisor X) :
    ↥(LinearMap.ker (tailTruncate (X := X) D₁ D₂)) →ₗ[ℂ] mittagLefflerH1 (X := X) D₁ :=
  (LinearMap.range (tailMapCo (X := X) D₁)).mkQ.comp
    (LinearMap.ker (tailTruncate (X := X) D₁ D₂)).subtype

@[simp] theorem tailKernelToH1_apply (D₁ D₂ : Divisor X)
    (Z : ↥(LinearMap.ker (tailTruncate (X := X) D₁ D₂))) :
    tailKernelToH1 D₁ D₂ Z
      = Submodule.Quotient.mk (Z : ↥(tailSubspace (X := X) D₁)) := rfl

/-! ### Exactness of the chain (Miranda Lemma 2.3, the five spots) -/

/-- **Exactness at `L(D₂)`**: `ker (α_{D₁}|_{L(D₂)}) = range (L(D₁) → L(D₂))` — a function in
`L(D₂)` has vanishing `D₁`-tail iff it already lies in `L(D₁)`. -/
theorem ker_lSysToTailKernel {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    LinearMap.ker (lSysToTailKernel (X := X) h)
      = LinearMap.range (lSysInclusion (X := X) h) := by
  ext a
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro h0
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    rw [lSysToTailKernel_mk] at h0
    have hf1 : (f : MeromorphicFunction X) ∈ linearSystem (X := X) D₁ := by
      rw [← ker_tailMap, LinearMap.mem_ker, ← lSysToTailKernelAux_coe h f, h0]
      rfl
    refine ⟨Submodule.Quotient.mk ⟨(f : MeromorphicFunction X), hf1⟩, ?_⟩
    rw [lSysInclusion_mk]
    rfl
  · rintro ⟨b, rfl⟩
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [lSysInclusion_mk, lSysToTailKernel_mk]
    apply Subtype.ext
    apply Subtype.ext
    rw [lSysToTailKernelAux_coe]
    exact LinearMap.mem_ker.mp (by rw [ker_tailMap]; exact g.2)

/-- **Exactness at `ker t^{D₁}_{D₂}`**: a window tail maps to `0` in `H¹(D₁)` iff it is the
`D₁`-tail of a global meromorphic function — which then automatically lies in `L(D₂)`. -/
theorem ker_tailKernelToH1 {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    LinearMap.ker (tailKernelToH1 (X := X) D₁ D₂)
      = LinearMap.range (lSysToTailKernel (X := X) h) := by
  ext Z
  rw [LinearMap.mem_ker, LinearMap.mem_range, tailKernelToH1_apply,
    Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨f, hf⟩
    have hf2 : f ∈ linearSystem (X := X) D₂ := by
      rw [← tailMapCo_eq_zero_iff D₂ f, ← tailTruncate_tailMapCo h, hf]
      exact LinearMap.mem_ker.mp Z.2
    refine ⟨Submodule.Quotient.mk ⟨f, hf2⟩, ?_⟩
    rw [lSysToTailKernel_mk]
    apply Subtype.ext
    exact hf
  · rintro ⟨b, rfl⟩
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [lSysToTailKernel_mk]
    exact ⟨(g : MeromorphicFunction X), rfl⟩

/-- **Exactness at `H¹(D₁)`**: a class dies under the truncation `H¹(D₁) → H¹(D₂)` iff it is
represented by a window tail (correct the representative by a global function). -/
theorem ker_mittagLefflerTruncate_eq {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    LinearMap.ker (mittagLefflerTruncate (X := X) h)
      = LinearMap.range (tailKernelToH1 (X := X) D₁ D₂) := by
  ext z
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro h0
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [mittagLefflerTruncate_mk, Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨f, hf⟩ := h0
    have hW : tailTruncate D₁ D₂ (Z - tailMapCo D₁ f) = 0 := by
      rw [map_sub, tailTruncate_tailMapCo h, hf, sub_self]
    refine ⟨⟨Z - tailMapCo D₁ f, LinearMap.mem_ker.mpr hW⟩, ?_⟩
    rw [tailKernelToH1_apply]
    show Submodule.Quotient.mk (Z - tailMapCo D₁ f) = Submodule.Quotient.mk Z
    rw [Submodule.Quotient.eq, sub_sub_cancel_left]
    exact Submodule.neg_mem _ ⟨f, rfl⟩
  · rintro ⟨W, rfl⟩
    rw [tailKernelToH1_apply, mittagLefflerTruncate_mk, LinearMap.mem_ker.mp W.2]
    exact Submodule.Quotient.mk_zero _

-- (Exactness at `H¹(D₂)` is `mittagLefflerTruncate_surjective`, proved in `TailMap`.)

/-! ### The dimension identity -/

/-- The relative kernel `ker (H¹(D₁) → H¹(D₂))` is **finite-dimensional** — it is the image of
the finite monomial window, with no finiteness assumption on the `H¹`s themselves. -/
theorem finiteDimensional_ker_mittagLefflerTruncate {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    FiniteDimensional ℂ ↥(LinearMap.ker (mittagLefflerTruncate (X := X) h)) := by
  rw [ker_mittagLefflerTruncate_eq h]
  infer_instance

/-- **Miranda Lemma 2.3** (Ch. VI §2, p. 181): for `D₁ ≤ D₂`,

    `dim ker (H¹(D₁) → H¹(D₂)) = (deg D₂ − l(D₂)) − (deg D₁ − l(D₁))`.

Rank–nullity walked down the explicit chain: `dim ker t = deg D₂ − deg D₁` monomials, of which
`α_{D₁}(L(D₂))` (dimension `l(D₂) − l(D₁)`) are realized; the rest is the relative kernel. -/
theorem finrank_ker_mittagLefflerTruncate {D₁ D₂ : Divisor X} (h : D₁ ≤ D₂) :
    (finrank ℂ ↥(LinearMap.ker (mittagLefflerTruncate (X := X) h)) : ℤ)
      = (Divisor.deg X D₂ - lDim (X := X) D₂) - (Divisor.deg X D₁ - lDim (X := X) D₁) := by
  have hγ := LinearMap.finrank_range_add_finrank_ker (tailKernelToH1 (X := X) D₁ D₂)
  have hβ := LinearMap.finrank_range_add_finrank_ker (lSysToTailKernel (X := X) h)
  have hι := LinearMap.finrank_range_add_finrank_ker (lSysInclusion (X := X) h)
  rw [LinearMap.ker_eq_bot.mpr (lSysInclusion_injective h), finrank_bot] at hι
  rw [ker_tailKernelToH1 h] at hγ
  rw [ker_lSysToTailKernel h] at hβ
  have hK := finrank_ker_tailTruncate h
  rw [ker_mittagLefflerTruncate_eq h,
    lDim_eq_finrank_lSysModule, lDim_eq_finrank_lSysModule]
  omega

end Jacobians.LaurentTail
