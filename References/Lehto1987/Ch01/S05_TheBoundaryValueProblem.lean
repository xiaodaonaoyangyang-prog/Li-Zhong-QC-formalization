import References.Lehto1987.Ch01.S04_BeltramiDifferentialEquation
import LiZhongQC.Ch04.S17_BoundaryValues

/-!
# Lehto, Chapter I §5: The boundary value problem

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. I §5 (`full.md`
P1:1205–1435).

Conventions (see §1–§4): `H` is the upper half-plane `toExt LiZhongQC.upperHalf` of `ℂ̄`, whose boundary is the
extended real line `ℝ̄`. A homeomorphism `h` of `ℝ̄` is given as a map `ℂ̄ → ℂ̄` whose values on `ℝ̄` are those of `h`
(the other values are never used); a normalized one (`h(∞) = ∞`) is an increasing homeomorphism `h : ℝ → ℝ` of `ℝ`
onto `ℝ`, and `realExt h` is the corresponding map of `ℂ̄`. `k`-quasisymmetric functions are the project's
`LiZhongQC.IsQuasisymmetric` (an increasing homeomorphism of `ℝ` onto `ℝ` with the double inequality). A self-map `f`
of `H` has the boundary values `h` (`LehtoVirtanen1973.HasRealBoundaryValues f h`) when it extends to a homeomorphism
of `H̄` fixing `∞` and equal to `h` on `ℝ`. The Beurling–Ahlfors extension (5.4) is `LiZhongQC.beurlingAhlfors h 2`
(the project's parameter `r` multiplies the imaginary part by `r/2`), read on `ℂ̄` through `OnePoint.map`.

* Unlabelled (§5.1, P1:1207–1211): the boundary function of a quasiconformal mapping between Jordan domains; the
  boundary value problem — omitted: the setting (the extension to the closures is the unlabelled claim of §2.1
  stated in the §2 file)
* Definition (maximal dilatation of a homeomorphism `h` of `ℝ̄`; (`K`-)quasiconformal `h`, §5.1) —
  `boundaryMaxDil`, `realExt`
* Unlabelled (§5.1, P1:1221): inverses and compositions of quasiconformal `h` — omitted: immediate from the
  definition, not cited
* Unlabelled (§5.1, P1:1223): the boundary function of a `K`-quasiconformal self-mapping of `H` is `K`-quasiconformal
  — `para1_5_1`
* Theorem 5.1 (§5.1) — exists: `LehtoVirtanen1973.thm2_6_2` (the double inequality (5.1) for the boundary values of
  a K-quasiconformal self-mapping of H fixing ∞, multiplied out)
* Theorem 5.1, sharpness (§5.1) — `thm1_5_1_sharp`
* Definition (`k`-quasisymmetric, quasisymmetric function, §5.2) — exists: `LiZhongQC.IsQuasisymmetric`
* Definition (quasisymmetry constant; normalized quasisymmetric function, §5.2) — `qsConstant`,
  `IsNormalizedQuasisymmetric`
* Unlabelled (§5.2, P1:1251): a `K`-quasiconformal `h` with `h(∞) = ∞` is `λ(K)`-quasisymmetric — `para1_5_2_a`
* Lemma 5.1 (§5.2) — `lemma1_5_1`
* Unlabelled (§5.2, P1:1275): the normalized `k`-quasisymmetric functions form a normal family closed under locally
  uniform limits — `para1_5_2_b`
* Lemma 5.2 (§5.2) — `lemma1_5_2`
* Theorem 5.2 (§5.3, Beurling–Ahlfors) — `thm1_5_2`
* Definition (Beurling–Ahlfors extension (5.4), §5.3) — exists: `LiZhongQC.beurlingAhlfors` (with the parameter
  r = 2, for which the imaginary part is the book's integral without the factor ½)
* Formula (5.5) (§5.3) — omitted: notation of the proof
* Unlabelled (§5.3, P1:1313): for every increasing homeomorphism `h` of `ℝ` the extension (5.4) is a continuously
  differentiable bijection of `H` with positive Jacobian — `para1_5_3_a`
* Unlabelled (§5.3, P1:1331): with a suitable factor in its imaginary part the extension (5.4) has maximal
  dilatation at most `k²` — `para1_5_3_b`
* Unlabelled (§5.3, P1:1323, 1333): compatibility of (5.4) with real affine maps; Lehtinen's bound
  `min(k^{3/2}, 2k − 1)` — omitted: proof step and quoted remark
* Lemma 5.3 (§5.4) — `lemma1_5_3`
* Lemma 5.4 (§5.5) — `lemma1_5_4`
* Unlabelled (§5.6, P1:1389): singular `k`-quasisymmetric functions exist — omitted: quoted, not cited
* Theorem 5.3 (§5.6) — `thm1_5_3`
* Definition (the family `F_h`, §5.7) — `qcExtensionsOf`, `extremalDilatation`
* Unlabelled (§5.7, P1:1409): `F_h` contains an extremal mapping — `para1_5_7_a`
* Unlabelled (§5.7, P1:1411–1413, Strebel): an `F_h` can contain two extremal mappings — `para1_5_7_b`
* Unlabelled (§5.7, P1:1417–1419): Lehtinen's bound `≥ k` for (5.4) and the example with the boundary values of the
  extremal map of §2.4 — omitted: quoted remarks, not cited
* Lemma 5.5 (§5.7) — `lemma1_5_5`
* Formula (5.10) (§5.7) — `eq1_5_10`

Helpers (not book notions): `realExt` (a real function read on `ℂ̄`), `extremalDilatation` (the smallest maximal
dilatation in `F_h`).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt upperHalf lambdaInv IsQuasisymmetric beurlingAhlfors)
open References (IsDomainExt finitePart)
open LehtoVirtanen1973 (IsKQuasiconformal IsQuasiconformalMap IsHomeoOn Quadrilateral quadModule maxDilatationK
  HasRealBoundaryValues finiteMap)

/-! ## §5.1 Boundary function of a quasiconformal mapping -/

/-- **Definition** (maximal dilatation of a homeomorphism `h` of `ℝ̄`, Ch. I §5.1). The supremum of
`M(H(h(x₁), h(x₂), h(x₃), h(x₄))) / M(H(x₁, x₂, x₃, x₄))` over the sequences `x₁, x₂, x₃, x₄` of points of `ℝ̄`
determining the positive orientation with respect to `H`; `h` is `K`-quasiconformal if this is `≤ K`.
Modelling: the sequences are the vertex sequences of the quadrilaterals with domain `H` (`ℝ̄` is the boundary of
`H`); `ℝ≥0∞`-valued, as LV's `maxDilatationK`. Junk: for an `h` reversing the orientation of `ℝ̄` the image
vertices are not positively ordered and `quadModule` has the value `0`; the book's `h` preserve orientation
(P1:1211), and every statement assumes it. -/
def boundaryMaxDil (h : ExtPlane → ExtPlane) : ℝ≥0∞ :=
  ⨆ (Q : Quadrilateral) (_ : Q.dom = toExt upperHalf),
    ENNReal.ofReal (quadModule (toExt upperHalf) (h ∘ Q.vert) / Q.module)

/-- The map of `ℂ̄` given by a real function `h` on `ℝ̄ = ℝ ∪ {∞}`: `x ↦ h(x)` for real `x`, `∞ ↦ ∞` (a normalized
homeomorphism of `ℝ̄`). Junk: the identity off `ℝ̄`, never used (`boundaryMaxDil` reads only the values on `ℝ̄`). -/
def realExt (h : ℝ → ℝ) (p : ExtPlane) : ExtPlane :=
  OnePoint.elim p extInf fun z => if z.im = 0 then ((h z.re : ℂ) : ExtPlane) else (z : ExtPlane)

/-- **Unlabelled** (Ch. I §5.1, P1:1223). If `h` is the boundary function of a `K`-quasiconformal mapping
`f : H → H`, then `h` itself is `K`-quasiconformal.
Modelling: the boundary function is the restriction to `ℝ̄` of a homeomorphic extension `W` of `f` to the closure of
`H` (it exists by `para1_2_1_d`). -/
theorem para1_5_1 {f W : ExtPlane → ExtPlane} {K : ℝ} (hf : IsKQuasiconformal f (toExt upperHalf) K)
    (hfH : f '' toExt upperHalf = toExt upperHalf) (hW : EqOn W f (toExt upperHalf))
    (hWh : IsHomeoOn W (closure (toExt upperHalf)) (closure (toExt upperHalf))) :
    boundaryMaxDil W ≤ ENNReal.ofReal K := by
  sorry

/-- **Theorem 5.1** (Ch. I §5.1), sharpness. The inequality (5.1),
`1/λ(K) ≤ (h(x + t) − h(x))/(h(x) − h(x − t)) ≤ λ(K)`, is sharp for any given `K`, `x` and `t`: both bounds are
attained by the boundary values `h` of `K`-quasiconformal self-mappings of `H` fixing `∞`.
Modelling: `1 ≤ K`, `t > 0`; the equalities are multiplied out. -/
theorem thm1_5_1_sharp {K : ℝ} (hK : 1 ≤ K) (x t : ℝ) (ht : 0 < t) :
    (∃ (f : ExtPlane → ExtPlane) (h : ℝ → ℝ), IsKQuasiconformal f (toExt upperHalf) K ∧
      f '' toExt upperHalf = toExt upperHalf ∧ HasRealBoundaryValues f h ∧
      h (x + t) - h x = lambdaInv K * (h x - h (x - t))) ∧
    ∃ (f : ExtPlane → ExtPlane) (h : ℝ → ℝ), IsKQuasiconformal f (toExt upperHalf) K ∧
      f '' toExt upperHalf = toExt upperHalf ∧ HasRealBoundaryValues f h ∧
      h x - h (x - t) = lambdaInv K * (h (x + t) - h x) := by
  sorry

/-! ## §5.2 Quasisymmetric functions -/

/-- **Definition** (quasisymmetry constant, Ch. I §5.2): the smallest `k` for which `h` is `k`-quasisymmetric.
Junk: `0` (`sInf ∅`) when `h` is not quasisymmetric; every statement uses it for quasisymmetric `h`. -/
def qsConstant (h : ℝ → ℝ) : ℝ := sInf {k : ℝ | IsQuasisymmetric h k}

/-- **Definition** (normalized quasisymmetric function, Ch. I §5.2): a `k`-quasisymmetric function which fixes `0`
and `1`. -/
def IsNormalizedQuasisymmetric (h : ℝ → ℝ) (k : ℝ) : Prop := IsQuasisymmetric h k ∧ h 0 = 0 ∧ h 1 = 1

/-- **Unlabelled** (Ch. I §5.2, P1:1251). If `h` is `K`-quasiconformal and `h(∞) = ∞`, then `h` is
`λ(K)`-quasisymmetric.
Modelling: `h` is an increasing homeomorphism of `ℝ` onto `ℝ` (a homeomorphism of `ℝ̄` fixing `∞` and preserving the
orientation, P1:1211, 1225), read on `ℂ̄` by `realExt`. -/
theorem para1_5_2_a {h : ℝ → ℝ} (hmono : StrictMono h) (hc : Continuous h) (htop : Tendsto h atTop atTop)
    (hbot : Tendsto h atBot atBot) {K : ℝ} (hK : boundaryMaxDil (realExt h) ≤ ENNReal.ofReal K) :
    IsQuasisymmetric h (lambdaInv K) := by
  sorry

/-- **Lemma 5.1** (Ch. I §5.2). The family of `k`-quasisymmetric functions `h` which keep `0` and `1` fixed is
equicontinuous at every point of the real axis. -/
theorem lemma1_5_1 (k x₀ : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ → ℝ, IsNormalizedQuasisymmetric h k → ∀ x : ℝ, |x - x₀| < δ →
      |h x - h x₀| < ε := by
  sorry

/-- **Unlabelled** (Ch. I §5.2, P1:1275). Every infinite sequence `(hₙ)` of normalized `k`-quasisymmetric functions
contains a subsequence which is locally uniformly convergent on the real axis, and the limit is also a normalized
`k`-quasisymmetric function. -/
theorem para1_5_2_b {k : ℝ} {hn : ℕ → ℝ → ℝ} (hhn : ∀ n, IsNormalizedQuasisymmetric (hn n) k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ h : ℝ → ℝ, IsNormalizedQuasisymmetric h k ∧
      TendstoLocallyUniformly (fun n => hn (φ n)) h atTop := by
  sorry

/-- **Lemma 5.2** (Ch. I §5.2). Let `[a, b]` be a closed interval on the real axis, and `ε > 0`. Then there is a
`δ > 0` such that for a normalized quasisymmetric function `h`, `|h(x) − x| < ε`, `x ∈ [a, b]`, whenever `h` is
`(1 + δ)`-quasisymmetric. -/
theorem lemma1_5_2 (a b : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ → ℝ, IsNormalizedQuasisymmetric h (1 + δ) → ∀ x ∈ Icc a b, |h x - x| < ε := by
  sorry

/-! ## §5.3 Solution of the boundary value problem -/

/-- **Theorem 5.2** (Ch. I §5.3, Beurling–Ahlfors). Let `h` be `k`-quasisymmetric. Then there exists a quasiconformal
self-mapping of the upper half-plane which has the boundary values `h` and whose maximal dilatation is bounded by a
number `K(k)` which depends only on `k` and tends to `1` as `k → 1`.
Modelling: `K(k)` is a function of `k` alone, chosen before `h`; `k → 1` from above (every quasisymmetry constant is
at least `1`). -/
theorem thm1_5_2 :
    ∃ Kf : ℝ → ℝ, Tendsto Kf (𝓝[>] 1) (𝓝 1) ∧ ∀ (k : ℝ) (h : ℝ → ℝ), IsQuasisymmetric h k →
      ∃ f : ExtPlane → ExtPlane, IsKQuasiconformal f (toExt upperHalf) (Kf k) ∧
        f '' toExt upperHalf = toExt upperHalf ∧ HasRealBoundaryValues f h := by
  sorry

/-- **Unlabelled** (Ch. I §5.3, P1:1313). For every increasing homeomorphism `h` of the real axis onto itself (no
quasisymmetry needed), the Beurling–Ahlfors extension (5.4) is a continuously differentiable bijective self-mapping
of `H` whose Jacobian is positive throughout `H`. -/
theorem para1_5_3_a {h : ℝ → ℝ} (hmono : StrictMono h) (hc : Continuous h) (htop : Tendsto h atTop atTop)
    (hbot : Tendsto h atBot atBot) :
    ContDiffOn ℝ 1 (beurlingAhlfors h 2) upperHalf ∧ BijOn (beurlingAhlfors h 2) upperHalf upperHalf ∧
      ∀ z ∈ upperHalf, 0 < LinearMap.det (fderiv ℝ (beurlingAhlfors h 2) z : ℂ →ₗ[ℝ] ℂ) := by
  sorry

/-- **Unlabelled** (Ch. I §5.3, P1:1331, Beurling–Ahlfors). If the imaginary part of (5.4) is multiplied by an
appropriate positive constant, the maximal dilatation `K` of the modified extension satisfies `K ≤ k²`.
Modelling: the modified extension is `beurlingAhlfors h r` for some `r > 0` (the book's constant is `r/2`); it still
has the boundary values `h`. -/
theorem para1_5_3_b {h : ℝ → ℝ} {k : ℝ} (hh : IsQuasisymmetric h k) :
    ∃ r : ℝ, 0 < r ∧ IsKQuasiconformal (OnePoint.map (beurlingAhlfors h r)) (toExt upperHalf) (k ^ 2) ∧
      HasRealBoundaryValues (OnePoint.map (beurlingAhlfors h r)) h := by
  sorry

/-! ## §5.4 Composition of Beurling–Ahlfors extensions -/

/-- **Lemma 5.3** (Ch. I §5.4). Let `h₁` and `h₂` be `k`-quasisymmetric functions and `f₁` and `f₂` their
Beurling–Ahlfors extensions. If the quasisymmetry constant of `h₂ ∘ h₁⁻¹` tends to `1`, then the maximal dilatation
of `f₂ ∘ f₁⁻¹` converges to `1`.
Modelling: sequential form (the proof's): for sequences `h₁ₙ`, `h₂ₙ` of `k`-quasisymmetric functions; `f₁⁻¹` is the
inverse of `f₁` on `H` (a bijection of `H`, `para1_5_3_a`), and the maximal dilatation is taken in `H`. -/
theorem lemma1_5_3 {k : ℝ} {h₁ h₂ : ℕ → ℝ → ℝ} (hh₁ : ∀ n, IsQuasisymmetric (h₁ n) k)
    (hh₂ : ∀ n, IsQuasisymmetric (h₂ n) k)
    (hlim : Tendsto (fun n => qsConstant (h₂ n ∘ Function.invFun (h₁ n))) atTop (𝓝 1)) :
    Tendsto (fun n => maxDilatationK (OnePoint.map (beurlingAhlfors (h₂ n) 2) ∘
        Function.invFunOn (OnePoint.map (beurlingAhlfors (h₁ n) 2)) (toExt upperHalf)) (toExt upperHalf))
      atTop (𝓝 1) := by
  sorry

/-! ## §5.5 Quasi-isometry -/

/-- **Lemma 5.4** (Ch. I §5.5, Ahlfors). The Beurling–Ahlfors extension `f` of a `k`-quasisymmetric function is a
quasi-isometry in the hyperbolic metric of the upper half-plane:
`(1/c) |dz|/Im z ≤ |df(z)|/Im f(z) ≤ c |dz|/Im z` (5.7) with a constant `c` depending only on `k`.
Modelling: `∀ k, ∃ c > 0`; `|df(z)|` is the length of the image `f′(z)v` of the tangent vector `v = dz`. -/
theorem lemma1_5_4 (k : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ h : ℝ → ℝ, IsQuasisymmetric h k → ∀ z ∈ upperHalf, ∀ v : ℂ,
      c⁻¹ * (‖v‖ / z.im) ≤ ‖fderiv ℝ (beurlingAhlfors h 2) z v‖ / (beurlingAhlfors h 2 z).im ∧
        ‖fderiv ℝ (beurlingAhlfors h 2) z v‖ / (beurlingAhlfors h 2 z).im ≤ c * (‖v‖ / z.im) := by
  sorry

/-! ## §5.6 Smoothness of solutions -/

/-- **Theorem 5.3** (Ch. I §5.6). For every quasisymmetric function, the boundary value problem has a real-analytic
solution: a quasiconformal self-mapping of `H` with the boundary values `h` which is real-analytic in `H`. -/
theorem thm1_5_3 {h : ℝ → ℝ} {k : ℝ} (hh : IsQuasisymmetric h k) :
    ∃ f : ExtPlane → ExtPlane, IsQuasiconformalMap f (toExt upperHalf) ∧ f '' toExt upperHalf = toExt upperHalf ∧
      HasRealBoundaryValues f h ∧ AnalyticOnNhd ℝ (finiteMap f) upperHalf := by
  sorry

/-! ## §5.7 Extremal solutions -/

/-- **Definition** (the family `F_h`, Ch. I §5.7): the quasiconformal self-mappings of `H` whose boundary values agree
with the given quasisymmetric `h`. -/
def qcExtensionsOf (h : ℝ → ℝ) : Set (ExtPlane → ExtPlane) :=
  {f | IsQuasiconformalMap f (toExt upperHalf) ∧ f '' toExt upperHalf = toExt upperHalf ∧ HasRealBoundaryValues f h}

/-- The smallest maximal dilatation in `F_h` (`K` of Lemma 5.5), as an infimum in `ℝ≥0∞` (`⊤` if `F_h` is empty,
which does not happen for quasisymmetric `h`, Theorem 5.2). -/
def extremalDilatation (h : ℝ → ℝ) : ℝ≥0∞ := ⨅ f ∈ qcExtensionsOf h, maxDilatationK f (toExt upperHalf)

/-- **Unlabelled** (Ch. I §5.7, P1:1409). In the class `F_h` there always exists an extremal mapping, which has the
smallest maximal dilatation in `F_h`. -/
theorem para1_5_7_a {h : ℝ → ℝ} {k : ℝ} (hh : IsQuasisymmetric h k) :
    ∃ f ∈ qcExtensionsOf h, maxDilatationK f (toExt upperHalf) = extremalDilatation h := by
  sorry

/-- **Unlabelled** (Ch. I §5.7, P1:1411–1413, Strebel). There is a quasisymmetric `h` for which `F_h` contains more
than one extremal mapping. -/
theorem para1_5_7_b :
    ∃ (h : ℝ → ℝ) (k : ℝ), IsQuasisymmetric h k ∧ ∃ f₁ ∈ qcExtensionsOf h, ∃ f₂ ∈ qcExtensionsOf h,
      (∃ z ∈ toExt upperHalf, f₁ z ≠ f₂ z) ∧ maxDilatationK f₁ (toExt upperHalf) = extremalDilatation h ∧
        maxDilatationK f₂ (toExt upperHalf) = extremalDilatation h := by
  sorry

/-- **Lemma 5.5** (Ch. I §5.7). Let `K*` be the maximal dilatation of the quasisymmetric function `h` and `K` the
minimal maximal dilatation of the quasiconformal self-mappings of `H` with boundary values `h`. Then `K → 1` as
`K* → 1`.
Modelling: `ε`–`δ` form, uniform in `h`; `K* = boundaryMaxDil (realExt h)`, `K = extremalDilatation h`. -/
theorem lemma1_5_5 :
    ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ → ℝ, (∃ k, IsQuasisymmetric h k) →
      boundaryMaxDil (realExt h) ≤ ENNReal.ofReal (1 + δ) → extremalDilatation h ≤ ENNReal.ofReal (1 + ε) := by
  sorry

/-- **Formula (5.10)** (Ch. I §5.7). `K* ≤ K ≤ λ(K*)^{3/2}`.
Modelling: `h` quasisymmetric, `K*`, `K` as in `lemma1_5_5`; the conclusion also asserts that `K*` is finite, so
that `λ(K*)` is the book's value. -/
theorem eq1_5_10 {h : ℝ → ℝ} {k : ℝ} (hh : IsQuasisymmetric h k) :
    boundaryMaxDil (realExt h) < ⊤ ∧ boundaryMaxDil (realExt h) ≤ extremalDilatation h ∧
      extremalDilatation h ≤ ENNReal.ofReal (lambdaInv (boundaryMaxDil (realExt h)).toReal ^ (3 / 2 : ℝ)) := by
  sorry

end Lehto1987
