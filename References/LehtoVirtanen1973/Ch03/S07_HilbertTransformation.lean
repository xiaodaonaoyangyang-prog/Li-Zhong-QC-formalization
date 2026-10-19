import References.LehtoVirtanen1973.Ch03.S06_LpDerivatives
import LiZhongQC.Ch02.S11_IntegralOperators

/-!
# Lehto–Virtanen, Chapter III §7: Hilbert transformation

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. III §7
(pp. 154–160; `full.md` P1:4733–5018).

Conventions (see also §5–§6). In §7.1 `f` has `L¹`-derivatives in a domain `G` of the finite plane and `D`, `D̄ ⊂ G`,
is a Jordan domain with rectifiable boundary (P1:4737), modelled as in §6; `∂D` is positively oriented and
`∫_{∂D} f(ζ)/(ζ − z) dζ` is the Stieltjes integral of §6.2 with `g(ζ) = ζ` (`HasBoundaryIntegral`). The derivatives
`f_z`, `f_{z̄}` of functions with `L^p`-derivatives are `LiZhongQC.genDz`, `LiZhongQC.genDzbar` of the partial
derivatives (§6). The operator `T_D` is a Cauchy principal value (P1:4763–4769): `HasCauchyTPV` asserts that the
truncated integrals over `D − D_r` exist and converge as `r → 0`. From §7.2 on the book works with the class `C_0^∞`
of the finite plane `Ω` (`ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ∧ HasCompactSupport`) and with `L²(Ω)`; there the
operators `T` and `S` are the project's: `LiZhongQC.cauchyT` (the integral (11.1), which for `ω ∈ C_0^∞` is the
book's `Tω`), `LiZhongQC.hilbertHSmooth` (the principal value (7.9), which exists for `ω ∈ C_0^∞`) and, on `L²`,
`LiZhongQC.hilbertH`. The book's `Sω` for `ω ∈ L²` is an element of `L²`, determined only up to a null set;
`LiZhongQC.hilbertH ω` is a representative of it (the `L²`-limit of the transforms of `C_0^∞` approximants of `ω`), so
every statement about `S` on `L²` is an almost-everywhere statement. For `C¹` functions `f_z`, `f_{z̄}` are
`LiZhongQC.dz`, `LiZhongQC.dzbar`. The exponents of `L^p` are real, `1 ≤ p < ∞` (H6).

* Definition (the Cauchy integral `W_D f`, formula (7.2), §7.1) — `cauchyIntegralW`
* Definition (the operator `T_D ω`, a Cauchy principal value, §7.1) — `HasCauchyTPV`, `cauchyTPV` (a new notion:
  the project's LiZhongQC.cauchyTOn is the plain Lebesgue integral over D, which is not LV's principal value when
  the integrand is not integrable)
* Lemma 7.1 (§7.1, the generalized Cauchy integral formula) — `lemma3_7_1`
* Formula (7.3) (§7.1) — `eq3_7_3`
* Formula (7.4) (§7.1) — exists: `LiZhongQC.eq11_19` (the same formula for the disc of radius R about the origin
  and a point z of it; the integrand is integrable, so the integral is the book's)
* Definition (the operator `T` on `C_0^∞`, §7.2) — exists: `LiZhongQC.cauchyT` (the book's operator: for ω of class
  C_0^∞ the integrand is integrable, so the Lebesgue integral is the book's integral)
* Definition (the Hilbert transformation `S` on `C_0^∞`, the Hilbert transform `Sω`, formula (7.9), §7.2) — exists:
  `LiZhongQC.hilbertHSmooth` (the book's operator: the pointwise Cauchy principal value, with the same truncation
  of the plane outside the disc of radius r about z)
* Unlabelled (§7.2, P1:4857–4863): for ω of class `C_0^∞` the Cauchy principal value (7.9) exists — exists:
  `LiZhongQC.eq11_15` (the truncated integrals converge as r → 0 at every point; this makes the values used in
  the pointers for (7.10)–(7.13) the book's limits)
* Formula (7.10) (§7.3) — exists: `LiZhongQC.eq11_17` (for ω of class C_0^∞: Tω is continuously differentiable,
  its z̄-derivative is ω and its z-derivative is Sω)
* Formula (7.11) (§7.3) — exists: `LiZhongQC.i1_hilbertH_eq_cauchyT_dz` (its first conjunct: Sω = T applied to the
  z-derivative of ω, for ω of class C_0^∞)
* Formula (7.12) (§7.3) — exists: `LiZhongQC.i1_hilbertH_eq_cauchyT_dz` (its second and third conjuncts: Sω is
  continuously differentiable and its z̄-derivative is the z-derivative of ω)
* Formula (7.13) (§7.4) — exists: `LiZhongQC.i4_eLpNorm_eq` (for ω of class C_0^∞, the L² norms of Sω and ω are
  equal, which is (7.13) after taking square roots)
* Definition (Cauchy sequence in `L^p`, §7.5) — exists: `CauchySeq` (in the metric space MeasureTheory.Lp of the
  area measure, whose distance is the L^p metric of §4.4)
* Unlabelled (§7.5, P1:4937, quoted from Munroe): `L^p`, `p ≥ 1`, is complete — exists:
  `MeasureTheory.Lp.instCompleteSpace` (for every exponent at least 1; stated on classes of functions equal almost
  everywhere, which LV identifies, P1:4025; a function sequence enters via MeasureTheory.MemLp.toLp)
* Unlabelled (§7.5, P1:4939–4945, quoted from Munroe): a sequence converging in `L^p` has a subsequence converging
  almost everywhere — `exists_subseq_ae_of_Lp`
* Definition (the Hilbert transformation `S` extended to `L²`, §7.6) — exists: `LiZhongQC.hilbertH` (the book's Sω
  is the element of L² which is the L²-limit of the transforms of C_0^∞ functions converging to ω in L²;
  the project's operator is a representative of it: the approximants are of class C_0^∞ and tend to ω in L²
  (LiZhongQC.hilbertHApprox_contDiff, LiZhongQC.hilbertHApprox_hasCompactSupport, LiZhongQC.hilbertHApprox_tendsto
  at p = 2), their transforms tend in L² to the project's value (LiZhongQC.hilbertH_tendsto_of_smooth_bound at
  p = 2, A = 1, with the bound LiZhongQC.i4_eLpNorm_eq, as in LiZhongQC.hilbertH_memLp_two), and LV's limit does not
  depend on the approximating sequence, by (7.13); the operator is well defined on classes
  (LiZhongQC.hilbertH_congr_ae), and on C_0^∞ it agrees almost everywhere with the principal value, by
  LiZhongQC.hilbertH_eq_ae_smooth; statements about S on L² are made almost everywhere)
* Unlabelled (§7.6, P1:4969–4973): the Hilbert transformation is an isometry of `L²` — exists:
  `LiZhongQC.thm11_3_isometry` (the L² norms of Sω and ω are equal for every ω in L²)
* Unlabelled (§7.6, P1:4967; linearity used P1:5003, P2:492, 510, 545; the norm cited as "III.7.6" at P2:563): the
  extended `S` is a continuous linear operator of `L²(Ω)` with the integral representation (7.9) on `C_0^∞` —
  exists: `LiZhongQC.hilbertH_add_ae`, `LiZhongQC.hilbertH_smul_ae`, `LiZhongQC.hilbertH_eq_ae_smooth`,
  `LiZhongQC.thm11_3_cor1` (additivity and homogeneity almost everywhere for ω in L²; continuity follows from
  linearity and LiZhongQC.thm11_3_isometry; on C_0^∞ it agrees almost everywhere with the principal value; the
  operator norm is 1)
* Footnote 39 (§7.7, P1:4981–4995: Beurling's L² principal value and the Calderón–Zygmund almost everywhere
  convergence) — omitted: quoted results of which the book says that it will not make use of them
* Lemma 7.2 (§7.7) — `lemma3_7_2`

Not stated (inventory: omitted): the formula (7.1) (the derivation of Lemma 7.1, which states it); the derivation
(7.5)–(7.8) of the principal value (7.9); the remark of §7.3 that `Tω`, `Sω` are of class `C^∞` and analytic
outside the support of `ω` (P1:4889, not cited later); the remark of §7.5 that a convergent sequence in `L^p` is a
Cauchy sequence; the steps (7.14)–(7.18) of proofs.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal Real

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (toExt IsACL partialX partialY genDz genDzbar hilbertH)
open References (IsJordanDomainExt)

/-! ## §7.1 Generalization of Cauchy's integral formula -/

/-- **Definition** (the Cauchy integral `W_D f`, Ch. III §7.1, (7.2)).
`W_D f(z) = (2πi)⁻¹ ∫_{∂D} f(ζ)/(ζ − z) dζ` for a point `z` of the Jordan domain `D`, the integral being taken over
the positively oriented boundary of `D` (§6.2).
Modelling: `boundaryIntegral` with `g(ζ) = ζ`; its junk value `0` (the integral not existing) is outside the book's
domain, and the statements assert the existence of the integral. -/
def cauchyIntegralW (D : Set ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 * π * I)⁻¹ * boundaryIntegral D (fun ζ => f ζ / (ζ - z)) id

/-- **Definition** (the operator `T_D` as a Cauchy principal value, Ch. III §7.1). `T_D ω(z) = L`:
`T_D ω(z) = −(1/π) lim_{r → 0} ∬_{D − D_r} ω(ζ)/(ζ − z) dσ`, `D_r = {ζ | |ζ − z| < r}`, "even if the integral exists
only as a Cauchy principal value": the integrals over `D − D_r` exist for `r > 0` and `−1/π` times them tend to `L`
as `r → 0`. -/
def HasCauchyTPV (D : Set ℂ) (ω : ℂ → ℂ) (z L : ℂ) : Prop :=
  (∀ r : ℝ, 0 < r → IntegrableOn (fun ζ => ω ζ / (ζ - z)) (D \ Metric.ball z r)) ∧
    Tendsto (fun r : ℝ => -(1 / π : ℂ) * ∫ ζ in D \ Metric.ball z r, ω ζ / (ζ - z)) (𝓝[>] 0) (𝓝 L)

open Classical in
/-- The value `T_D ω(z)` (Ch. III §7.1): the limit `L` of `HasCauchyTPV`, unique when it exists. Junk value `0` when
the principal value does not exist; statements assert its existence through `HasCauchyTPV`. -/
def cauchyTPV (D : Set ℂ) (ω : ℂ → ℂ) (z : ℂ) : ℂ :=
  if h : ∃ L, HasCauchyTPV D ω z L then h.choose else 0

/-- **Lemma 7.1** (Ch. III §7.1, the generalized Cauchy integral formula). Let `f` have `L¹`-derivatives in the
domain `G` and let `D`, `D̄ ⊂ G`, be a Jordan domain with rectifiable boundary. Then `f` has the representation
`f = W_D f + T_D f_{z̄}` in `D`, where `W_D f` is analytic.
Modelling: the first conjunct asserts that the Cauchy integrals (7.2) exist at the points of `D`, so that the value
of `cauchyIntegralW` is the book's; the last conjunct asserts that the principal value `T_D f_{z̄}(z)` exists and
equals `f(z) − W_D f(z)`. -/
theorem lemma3_7_1 {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {f : ℂ → ℂ} (hf : HasLpDerivatives f G 1)
    {D : Set ℂ} (hD : IsJordanDomainExt (toExt D)) (hDG : closure (toExt D) ⊆ toExt G)
    (hDr : IsRectifiableJordanCurve (frontier D)) :
    (∀ z ∈ D, ∃ L : ℂ, HasBoundaryIntegral D (fun ζ => f ζ / (ζ - z)) id L) ∧
      DifferentiableOn ℂ (cauchyIntegralW D f) D ∧
      ∀ z ∈ D, HasCauchyTPV D (genDzbar (partialX f) (partialY f)) z (f z - cauchyIntegralW D f z) := by
  sorry

/-- **Formula (7.3)** (Ch. III §7.1). If, under the hypotheses of Lemma 7.1, `f` is identically zero on the boundary
of `D`, then `W_D f` vanishes in `D` and `f = T_D f_{z̄}` (7.3) in `D`.
Modelling: the Cauchy integral (7.2) exists and vanishes at every point of `D`, and the principal value
`T_D f_{z̄}(z)` exists and equals `f(z)`. -/
theorem eq3_7_3 {G : Set ℂ} (hG : IsOpen G ∧ IsConnected G) {f : ℂ → ℂ} (hf : HasLpDerivatives f G 1)
    {D : Set ℂ} (hD : IsJordanDomainExt (toExt D)) (hDG : closure (toExt D) ⊆ toExt G)
    (hDr : IsRectifiableJordanCurve (frontier D)) (hf₀ : ∀ ζ ∈ frontier D, f ζ = 0) :
    ∀ z ∈ D, HasBoundaryIntegral D (fun ζ => f ζ / (ζ - z)) id 0 ∧
      HasCauchyTPV D (genDzbar (partialX f) (partialY f)) z (f z) := by
  sorry

/-! ## §7.5 Completeness of `L^p`-spaces -/

/-- **Unlabelled** (Ch. III §7.5, P1:4939–4945, quoted from Munroe). If the functions `fₙ` converge to `f` in the
space `L^p`, then there is a subsequence `f_{n_k}` of `fₙ` such that `lim_{k → ∞} f_{n_k}(z) = f(z)` for almost all
`z`.
Modelling: `L^p(A)` for a measurable set `A` of the finite plane and the area measure (§4.4), `1 ≤ p < ∞` with a
real exponent; the functions are finite `ℂ`-valued (D2); the subsequence is `fn ∘ φ`, `φ` strictly increasing. -/
theorem exists_subseq_ae_of_Lp {A : Set ℂ} (hA : NullMeasurableSet A volume) {p : ℝ} (hp : 1 ≤ p)
    {fn : ℕ → ℂ → ℂ} {f : ℂ → ℂ} (hfn : ∀ n, MemLp (fn n) (ENNReal.ofReal p) (volume.restrict A))
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict A))
    (hconv : Tendsto (fun n => eLpNorm (fn n - f) (ENNReal.ofReal p) (volume.restrict A)) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ z ∂(volume.restrict A), Tendsto (fun k => fn (φ k) z) atTop (𝓝 (f z)) := by
  -- Riesz: convergence in `L^p` gives convergence in measure, which has an a.e. convergent subsequence
  have _ := hA
  have _ := hfn
  have _ := hf
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  exact (tendstoInMeasure_of_tendsto_eLpNorm hp0 hconv).exists_seq_tendsto_ae

/-! ## §7.7 Application to functions with `L²`-derivatives -/

/-- **Lemma 7.2** (Ch. III §7.7). If the function `f` is absolutely continuous on lines in the finite plane `Ω` and
has square integrable derivatives over `Ω`, then `f_z(z) = S f_{z̄}(z)` almost everywhere.
Modelling: `f_z`, `f_{z̄}` are built from the partial derivatives, and `f_{z̄} ∈ L²(Ω)`; `S` on `L²` is
`LiZhongQC.hilbertH` (module docstring), so the identity is an almost-everywhere equality, as in the book. -/
theorem lemma3_7_2 {f : ℂ → ℂ} (hf : IsACL f univ) (hfx : MemLp (partialX f) 2 volume)
    (hfy : MemLp (partialY f) 2 volume) :
    genDz (partialX f) (partialY f) =ᵐ[volume] hilbertH (genDzbar (partialX f) (partialY f)) := by
  sorry

end LehtoVirtanen1973
