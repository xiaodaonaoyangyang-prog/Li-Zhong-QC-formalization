import References.Lehto1987.Ch01.S02_GeometricDefinitionOfQuasiconformalMappings
import References.LehtoVirtanen1973.Ch01.S09_LocalCharacterization

/-!
# Lehto, Chapter I §3: Analytic definition of quasiconformal mappings

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. I §3 (`full.md`
P1:793–932).

Conventions (see §1–§2): derivatives are taken at finite points with finite values, as in Lehto–Virtanen (I.9):
`∂f`, `∂̄f` are `LiZhongQC.dz`, `LiZhongQC.dzbar`, the directional derivative `∂_α f` is `LehtoVirtanen1973.dirDeriv`
and the dilatation quotient `D_f` is `LehtoVirtanen1973.dilQuotient` of the finite function
`LehtoVirtanen1973.finiteMap f`; a sense-preserving diffeomorphism of a domain of `ℂ̄` (in the charts at `∞` and at
the poles) with `D_f ≤ K` is LV's regular `K`-quasiconformal mapping. "Almost everywhere in `A`" refers to the area
measure on the finite part of `A`.

* Definition (`∂f`, `∂̄f`, `∂_α f`, the dilatation quotient `D_f`; `∂_α f = ∂f + ∂̄f e^{−2iα}` and the formulas for
  `max_α |∂_α f|`, `min_α |∂_α f|`, §3.1) — exists: `LiZhongQC.dz`, `LiZhongQC.dzbar`, `LehtoVirtanen1973.dirDeriv`,
  `LehtoVirtanen1973.dilQuotient`, `LehtoVirtanen1973.dirDeriv_eq_dz_add_dzbar`, `LehtoVirtanen1973.eq1_9_5`
  (OCR: the book prints |∂f(z)|⁴ for |∂f(z)| in the maximum)
* Unlabelled (§3.1, P1:829): the dilatation quotient is conformally invariant, `D_f(z) = D_w(g⁻¹(z))` for
  `w = h ∘ f ∘ g` — `para1_3_1`
* Theorem 3.1 (§3.2) — `thm1_3_1`
* Theorem 3.2 (§3.2) — `thm1_3_2`
* Unlabelled (§3.2, P1:863): a sense-preserving diffeomorphism is `K`-quasiconformal iff `D_f ≤ K` everywhere —
  omitted: the combination of Theorems 3.1 and 3.2, not cited separately
* Definition (ACL, §3.3) — exists: `LiZhongQC.IsACL`, `LehtoVirtanen1973.IsACLExt` (for plane functions, and for
  homeomorphisms of domains of the plane read off ∞ and its preimage)
* Theorem 3.3 (§3.3) — exists: `LehtoVirtanen1973.lemma4_1_1` (a quasiconformal mapping is ACL)
* Unlabelled (§3.3, P1:881, Gehring–Lehto): a continuous open mapping with finite partial derivatives a.e. is
  differentiable a.e. — `para1_3_3`
* Theorem 3.4 (§3.3) — exists: `LehtoVirtanen1973.thm4_1_1` (differentiability and the dilatation condition (3.1)
  at almost all points of A)
* Definition (`L^p`-derivatives, §3.4) — exists: `LehtoVirtanen1973.HasLpDerivatives`,
  `LehtoVirtanen1973.HasLpDerivativesExt`
* Unlabelled (§3.4, P1:895): a quasiconformal mapping has `L²`-derivatives — exists: `LehtoVirtanen1973.thm4_1_2`
* Unlabelled (§3.4, P1:898): `max_α |∂_α f|² ≤ K J` a.e. — exists: `LehtoVirtanen1973.eq4_1_6`
* Unlabelled (§3.4, P1:903): quasiconformal mappings are absolutely continuous and carry measurable sets onto
  measurable sets — exists: `LehtoVirtanen1973.thm4_1_3`, `LehtoVirtanen1973.qc_image_measurable`
* Formula (3.2) (§3.4) — exists: `LehtoVirtanen1973.eq4_1_8` (the integral of J over a measurable E ⊂ A is the area
  of f(E))
* Unlabelled (§3.4, P1:909): `J > 0` a.e. for a quasiconformal mapping — `para1_3_4_d`
* Theorem 3.5 (§3.5, analytic definition) — exists: `LehtoVirtanen1973.analytic_definition` (the same statement;
  K ≥ 1 is the book's standing convention; the dilatation condition is required at the points of
  differentiability, which are almost all points by the ACL property, as the book's proof notes)

Not stated (inventory U−): "`f` is conformal iff `D_f ≡ 1`" (P1:825); the `p > 2` remark (P1:911, proved in §4.4);
the Cantor-function counterexample (P1:915, quoted); the invariance of `L^p`-derivatives under `C¹` changes of
coordinates (P1:891, quoted).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt)
open References (IsDomainExt finitePart)
open LehtoVirtanen1973 (IsKQuasiconformal IsQuasiconformalMap finiteMap dirDeriv dilQuotient
  IsRegularKQuasiconformal partialJacobian)

/-! ## §3.1 Dilatation quotient -/

/-- **Unlabelled** (Ch. I §3.1, P1:829). The dilatation quotient is conformally invariant: if `g` and `h` are
conformal mappings such that `w = h ∘ f ∘ g` is defined, then `D_f(z) = D_w(g⁻¹(z))`.
Modelling: stated at one point, `z = g(ζ)`: `g` is conformal at `ζ` (complex differentiable with `g′(ζ) ≠ 0`), `h`
at `f(z)`, and `f` is differentiable at `z` with positive Jacobian (the book's `f` is a sense-preserving
diffeomorphism). The local hypotheses are implied by the book's, so the pointwise form implies its claim. -/
theorem para1_3_1 {f g h : ℂ → ℂ} {ζ : ℂ} (hg : DifferentiableAt ℂ g ζ) (hg' : deriv g ζ ≠ 0)
    (hh : DifferentiableAt ℂ h (f (g ζ))) (hh' : deriv h (f (g ζ)) ≠ 0) (hf : DifferentiableAt ℝ f (g ζ))
    (hJ : 0 < LinearMap.det (fderiv ℝ f (g ζ) : ℂ →ₗ[ℝ] ℂ)) :
    dilQuotient f (g ζ) = dilQuotient (h ∘ f ∘ g) ζ := by
  sorry

/-! ## §3.2 Quasiconformal diffeomorphisms -/

/-- **Theorem 3.1** (Ch. I §3.2, Grötzsch). Let `f : A → A′` be a sense-preserving diffeomorphism with the property
`D_f(z) ≤ K` for every `z ∈ A`. Then `f` is a `K`-quasiconformal mapping.
Modelling: a sense-preserving diffeomorphism of the domain `A` of `ℂ̄` with `D_f ≤ K` is LV's regular
`K`-quasiconformal mapping (`IsRegularKQuasiconformal`: a sense-preserving homeomorphism whose local
representations, in the charts at `∞` and at the poles, are continuously differentiable with nonzero Jacobian — the
inverse is then continuously differentiable too — and whose dilatation quotient is at most `K`). -/
theorem thm1_3_1 {f : ExtPlane → ExtPlane} {A : Set ExtPlane} {K : ℝ} (hf : IsRegularKQuasiconformal f A K) :
    IsKQuasiconformal f A K := by
  sorry

/-- **Theorem 3.2** (Ch. I §3.2). Let `f : A → A′` be a `K`-quasiconformal mapping. If `f` is differentiable at
`z₀ ∈ A`, then `max_α |∂_α f(z₀)| ≤ K min_α |∂_α f(z₀)|` (3.1).
Modelling: `z₀` and `f(z₀)` are finite (LV's convention I.9 for derivatives), and differentiability is that of the
finite function `finiteMap f` at `z₀`. -/
theorem thm1_3_2 {f : ExtPlane → ExtPlane} {A : Set ExtPlane} {K : ℝ} (hf : IsKQuasiconformal f A K) {z₀ : ℂ}
    (hz₀ : (z₀ : ExtPlane) ∈ A) (hfin : f z₀ ≠ extInf) (hd : DifferentiableAt ℝ (finiteMap f) z₀) :
    (⨆ α : ℝ, ‖dirDeriv (finiteMap f) z₀ α‖) ≤ K * ⨅ α : ℝ, ‖dirDeriv (finiteMap f) z₀ α‖ := by
  sorry

/-! ## §3.3 Absolute continuity and differentiability -/

/-- **Unlabelled** (Ch. I §3.3, P1:881, Gehring–Lehto). Let `f` be a complex-valued, continuous and open mapping of a
plane domain `A` which has finite partial derivatives a.e. in `A`. Then `f` is differentiable a.e. in `A`.
Modelling: `A` is a domain of the finite plane; "open" means that `f` maps the open subsets of `A` onto open sets;
the partial derivatives are the derivatives of `t ↦ f(z + t)` and `t ↦ f(z + it)` at `t = 0`. -/
theorem para1_3_3 {f : ℂ → ℂ} {A : Set ℂ} (hA : IsOpen A ∧ IsConnected A) (hc : ContinuousOn f A)
    (hopen : ∀ U ⊆ A, IsOpen U → IsOpen (f '' U))
    (hpart : ∀ᵐ z ∂(volume.restrict A), (∃ a : ℂ, HasDerivAt (fun t : ℝ => f (z + t)) a 0) ∧
      ∃ b : ℂ, HasDerivAt (fun t : ℝ => f (z + t * I)) b 0) :
    ∀ᵐ z ∂(volume.restrict A), DifferentiableAt ℝ f z := by
  sorry

/-! ## §3.4 Generalized derivatives -/

/-- **Unlabelled** (Ch. I §3.4, P1:909). For a quasiconformal mapping `f` of a domain `A`, `J(z) > 0` almost
everywhere (obtained by applying (3.2) to `f⁻¹`).
Modelling: `J` is LV's Jacobian `partialJacobian` of the finite function `finiteMap f` (built from the partial
derivatives, which exist almost everywhere); the point `f⁻¹(∞)` is null. -/
theorem para1_3_4_d {f : ExtPlane → ExtPlane} {A : Set ExtPlane} (hf : IsQuasiconformalMap f A) :
    ∀ᵐ z ∂(volume.restrict (finitePart A)), 0 < partialJacobian (finiteMap f) z := by
  sorry

end Lehto1987
