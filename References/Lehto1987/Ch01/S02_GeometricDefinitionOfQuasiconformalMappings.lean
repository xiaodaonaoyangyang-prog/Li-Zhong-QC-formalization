import References.Lehto1987.Ch01.S01_ConformalInvariants
import References.LehtoVirtanen1973.Ch02.S09_CircularDilatation

/-!
# Lehto, Chapter I §2: Geometric definition of quasiconformal mappings

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. I §2 (`full.md`
P1:597–792).

Conventions (see §1 and the root file): quasiconformality is the geometric definition of Lehto–Virtanen, to which
the book refers throughout (`LehtoVirtanen1973.maxDilatationK`, `IsKQuasiconformal`, `IsQuasiconformalMap`); a
"`K`-quasiconformal mapping of the plane" is `IsKQuasiconformal f univ K` with `f : ℂ̄ → ℂ̄`; every `K` is `≥ 1`
(P1:607). Spherical distances are LV's `sphericalDist`; convergence is spherical. The distortion function `λ(K)` is
`LiZhongQC.lambdaInv`, which is LV's `λ` (`LehtoVirtanen1973.eq2_6_4`), and `μ(r)` is `LiZhongQC.grotzschMu`. The
real axis of the plane is the extended real line `LiZhongQC.extRealLine`. Finite values of a mapping of the plane
fixing `∞` are read through `LehtoVirtanen1973.finiteMap`.

* Definition (maximal dilatation; quasiconformal and `K`-quasiconformal mappings, §2.1) — exists:
  `LehtoVirtanen1973.maxDilatationK`, `LehtoVirtanen1973.IsQuasiconformalMap`,
  `LehtoVirtanen1973.IsKQuasiconformal`
* Unlabelled (§2.1, P1:615): `f` is `1`-quasiconformal if and only if `f` is conformal — exists:
  `LehtoVirtanen1973.thm1_5_1`, `LehtoVirtanen1973.conformal_isKQuasiconformal_one` (the two directions)
* Unlabelled (§2.1, P1:615): `f` and `f⁻¹` are simultaneously `K`-quasiconformal; `g ∘ f` is
  `K₁K₂`-quasiconformal — exists: `LehtoVirtanen1973.kqc_inv`, `LehtoVirtanen1973.kqc_comp`
* Formula (2.1) (§2.1) — exists: `LehtoVirtanen1973.isKQuasiconformal_iff_ring` (the same characterization by the
  modules of the ring domains with closure in A)
* Unlabelled (§2.1, P1:627): isolated boundary points are removable — exists: `LehtoVirtanen1973.thm1_8_1` (a
  K-quasiconformal mapping extends K-quasiconformally to an isolated boundary point)
* Unlabelled (§2.1, P1:629): a quasiconformal mapping of a Jordan domain onto a Jordan domain extends to a
  homeomorphism of the closures — `para1_2_1_d`
* Formula (2.2) (§2.1, Väisälä) — omitted: quoted as a possible definition and not cited; its form for families of
  arcs is stated in LV Ch. IV §3
* Definition (normal family, §2.2) — exists: `LehtoVirtanen1973.IsNormalFamilySph`
* Unlabelled (§2.2, P1:643–645): equicontinuous families are normal; Montel's theorem — omitted: quoted classics,
  used only in motivation
* Lemma 2.1 (§2.2) — exists: `LehtoVirtanen1973.thm2_4_1` (applied with d/2: two omitted values at spherical
  distance at least d have distance greater than d/2; the conclusion is the same equicontinuity)
* Theorem 2.1 (§2.2) — exists: `LehtoVirtanen1973.thm2_4_2_ii`, `LehtoVirtanen1973.thm2_5_1_iii` (equicontinuity
  and normality when the three distances exceed a fixed d > 0, which is "uniformly bounded away from zero")
* Theorem 2.2 (§2.3) — `thm1_2_2`
* Theorem 2.3 (§2.3) — exists: `LehtoVirtanen1973.thm2_5_5` (the same statement: pointwise convergence in A)
* Definition (the distortion function `λ(K)`, §2.4; its expression `λ(K) = (μ⁻¹(πK/2))⁻² − 1`, P1:717) — exists:
  `LiZhongQC.lambdaInv`, `LehtoVirtanen1973.eq2_6_4` (LV's λ satisfies μ(1/√(1 + λ(K))) = πK/2, which is the book's
  expression)
* Formula (2.3) (§2.4) — `eq1_2_3`
* Formula (2.4) (§2.4) — omitted: the step t = f(1) ≤ (μ⁻¹(πK/2))⁻² − 1 of the derivation of λ, whose value is
  stated in (2.3); likewise `M(H(−1, 0, 1, ∞)) = 1` (P1:697)
* Unlabelled (§2.4, P1:709): a homeomorphism has the same maximal dilatation in `A` and in `A \ I` for a closed
  segment `I` — exists: `LehtoVirtanen1973.thm1_8_3` (for a closed analytic arc, of which a segment is a case; for
  sense-preserving homeomorphisms, for which the maximal dilatation is defined)
* Unlabelled (§2.4, P1:709): the reflection principle for `K`-quasiconformal mappings — exists:
  `LehtoVirtanen1973.reflection_principle`
* Formula (2.5) (§2.4) — exists: `LiZhongQC.eq5_21` (μ(1/√2) = π/2)
* Formula (2.6) (§2.4) — exists: `LehtoVirtanen1973.eq2_6_10` (the remainder is O(e^{−πK}), hence o(1), and
  positive for K ≥ 1)
* Unlabelled (§2.4, P1:733–739): `λ(1) = 1` and `λ` is continuous on `[1, ∞)` — `para1_2_4_c`
* Theorem 2.4 (§2.5) — `thm1_2_4`
* Unlabelled (§2.5, P1:761): (2.7) holds with `c(K) = λ(K)`, and `λ(K)` is the maximum of `|f|` on the unit circle
  for the `K`-quasiconformal mappings fixing `−1, 0, ∞` — `para1_2_5`
* Formula (2.8) (§2.5) — `eq1_2_8`
* Formula (2.9) (§2.5) — `eq1_2_9`
* Unlabelled (§2.5, P1:785–787): characterization of `K`-quasiconformality by the circular distortion `H` —
  omitted: the book says it will not use it (LV Ch. II §9, IV §4)

Not stated (inventory U−): "the maximal dilatation is always `≥ 1`" and `M(f(Q)) ≥ M(Q)/K` (P1:607, 615,
immediate); the Beurling–Ahlfors bound `λ(K) ≤ exp(4.39(K − 1))` (P1:733, quoted, used only for the continuity of
`λ` at `1`, which is stated); the proof of (2.7) with `c(K) = e^{πK}` (P1:755).
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve unitDisc lambdaInv extRealLine)
open References (IsDomainExt IsJordanDomainExt finitePart)
open LehtoVirtanen1973 (IsConformalMap IsHomeoOn IsKQuasiconformal IsQuasiconformalMap sphericalDist finiteMap
  finiteValue TendstoUniformlyOnCompactsSph)

/-! ## §2.1 Definitions of quasiconformality -/

/-- **Unlabelled** (Ch. I §2.1, P1:629). A quasiconformal mapping of a Jordan domain onto another Jordan domain can
be extended to a homeomorphism between the closures of the domains. -/
theorem para1_2_1_d {f : ExtPlane → ExtPlane} {A A' : Set ExtPlane} (hA : IsJordanDomainExt A)
    (hA' : IsJordanDomainExt A') (hf : IsQuasiconformalMap f A) (hfA : f '' A = A') :
    ∃ F : ExtPlane → ExtPlane, EqOn F f A ∧ IsHomeoOn F (closure A) (closure A') := by
  sorry

/-! ## §2.3 Compactness of quasiconformal mappings -/

/-- **Theorem 2.2** (Ch. I §2.3). The limit function `f` of a sequence `(fₙ)` of `K`-quasiconformal mappings of a
domain `A`, locally uniformly convergent in `A`, is either a constant or a `K`-quasiconformal mapping.
Modelling: local uniform convergence is uniform convergence in the spherical metric on the compact subsets of `A`;
"constant" means constant on `A`. -/
theorem thm1_2_2 {fn : ℕ → ExtPlane → ExtPlane} {f : ExtPlane → ExtPlane} {A : Set ExtPlane} {K : ℝ}
    (hA : IsDomainExt A) (hfn : ∀ n, IsKQuasiconformal (fn n) A K) (hlim : TendstoUniformlyOnCompactsSph fn f A) :
    (∃ c : ExtPlane, ∀ z ∈ A, f z = c) ∨ IsKQuasiconformal f A K := by
  sorry

/-! ## §2.4 A distortion function -/

/-- **Formula (2.3)** (Ch. I §2.4). Let `F` be the family of `K`-quasiconformal mappings of the plane which map the
real axis onto itself and fix the points `−1`, `0` and `∞`. Then `λ(K) = max {f(1) | f ∈ F}`.
Modelling: `1 ≤ K` (the family is empty for `K < 1`); the real axis is the extended real line, so `f(1)` is real;
the maximum is `IsGreatest` of the set of the real values `f(1)`. -/
theorem eq1_2_3 {K : ℝ} (hK : 1 ≤ K) :
    IsGreatest {t : ℝ | ∃ f : ExtPlane → ExtPlane, IsKQuasiconformal f univ K ∧ f '' extRealLine = extRealLine ∧
      f ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) ∧ f ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      f extInf = extInf ∧ f ((1 : ℂ) : ExtPlane) = ((t : ℂ) : ExtPlane)} (lambdaInv K) := by
  sorry

/-- **Unlabelled** (Ch. I §2.4, P1:733–739). `λ(1) = 1` (P1:719, "the obvious result"), and `λ` is continuous on
`[1, ∞)`: at `K = 1` by the Beurling–Ahlfors bound, at an arbitrary `K` by the continuity of `r ↦ μ(r)`. -/
theorem para1_2_4_c : lambdaInv 1 = 1 ∧ ContinuousOn lambdaInv (Ici 1) := by
  sorry

/-! ## §2.5 Circular distortion -/

/-- **Theorem 2.4** (Ch. I §2.5). Let `f` be a `K`-quasiconformal mapping of the plane fixing `0` and `∞`. Then for
every `r > 0`, `max_φ |f(re^{iφ})| / min_φ |f(re^{iφ})| ≤ c(K)` (2.7), where the constant `c(K)` depends only on
`K`.
Modelling: `∀ K, ∃ c, ∀ f, …`; the quotient of the maximum and the minimum is bounded by `c` if and only if
`|f(re^{iφ₁})| ≤ c |f(re^{iφ₂})|` for all `φ₁, φ₂` (the minimum is positive, `f` being injective and fixing `0`). The
values at finite points are finite, `f` fixing `∞`. -/
theorem thm1_2_4 (K : ℝ) :
    ∃ c : ℝ, ∀ f : ExtPlane → ExtPlane, IsKQuasiconformal f univ K → f ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) →
      f extInf = extInf → ∀ r : ℝ, 0 < r → ∀ φ₁ φ₂ : ℝ,
        ‖finiteMap f (circleMap 0 r φ₁)‖ ≤ c * ‖finiteMap f (circleMap 0 r φ₂)‖ := by
  sorry

/-- **Unlabelled** (Ch. I §2.5, P1:761, Lehto–Virtanen–Väisälä). The sharp bound in (2.7) is `λ(K)`: (2.7) holds
with `c(K) = λ(K)`, and `λ(K)` is the maximum of `|f(z)|` on the unit circle in the family of `K`-quasiconformal
mappings of the plane which fix `−1`, `0` and `∞`.
Modelling: `1 ≤ K`; (2.7) is written as in `thm1_2_4`; the maximum is `IsGreatest` of the set of the values
`|f(z)|`, `|z| = 1`, over this family (it gives the sharpness: `|f(−1)| = 1`). -/
theorem para1_2_5 {K : ℝ} (hK : 1 ≤ K) :
    (∀ f : ExtPlane → ExtPlane, IsKQuasiconformal f univ K → f ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) →
      f extInf = extInf → ∀ r : ℝ, 0 < r → ∀ φ₁ φ₂ : ℝ,
        ‖finiteMap f (circleMap 0 r φ₁)‖ ≤ lambdaInv K * ‖finiteMap f (circleMap 0 r φ₂)‖) ∧
    IsGreatest {s : ℝ | ∃ f : ExtPlane → ExtPlane, IsKQuasiconformal f univ K ∧
      f ((-1 : ℂ) : ExtPlane) = ((-1 : ℂ) : ExtPlane) ∧ f ((0 : ℂ) : ExtPlane) = ((0 : ℂ) : ExtPlane) ∧
      f extInf = extInf ∧ ∃ z : ℂ, ‖z‖ = 1 ∧ s = ‖finiteMap f z‖} (lambdaInv K) := by
  sorry

/-- **Formula (2.8)** (Ch. I §2.5). Let `f` be a `K`-quasiconformal mapping of the plane fixing `∞`. If
`|z₂ − z₀| ≤ |z₁ − z₀|`, then `|f(z₂) − f(z₀)| ≤ c(K) |f(z₁) − f(z₀)|`.
Modelling: `c(K)` is the constant of (2.7), which a statement cannot name; `∀ K, ∃ c` (the property passes to
larger constants, so one constant serves (2.7), (2.8) and (2.9)). The points are finite and so are their images. -/
theorem eq1_2_8 (K : ℝ) :
    ∃ c : ℝ, ∀ f : ExtPlane → ExtPlane, IsKQuasiconformal f univ K → f extInf = extInf →
      ∀ z₀ z₁ z₂ : ℂ, ‖z₂ - z₀‖ ≤ ‖z₁ - z₀‖ →
        ‖finiteMap f z₂ - finiteMap f z₀‖ ≤ c * ‖finiteMap f z₁ - finiteMap f z₀‖ := by
  sorry

/-- **Formula (2.9)** (Ch. I §2.5). If `|z₂ − z₀| ≤ n |z₁ − z₀|`, where `n ≥ 1` is an integer, then
`|f(z₂) − f(z₀)| ≤ n c(K)ⁿ |f(z₁) − f(z₀)|`.
Modelling: as in `eq1_2_8`. -/
theorem eq1_2_9 (K : ℝ) :
    ∃ c : ℝ, ∀ f : ExtPlane → ExtPlane, IsKQuasiconformal f univ K → f extInf = extInf →
      ∀ (n : ℕ), 1 ≤ n → ∀ z₀ z₁ z₂ : ℂ, ‖z₂ - z₀‖ ≤ n * ‖z₁ - z₀‖ →
        ‖finiteMap f z₂ - finiteMap f z₀‖ ≤ n * c ^ n * ‖finiteMap f z₁ - finiteMap f z₀‖ := by
  sorry

end Lehto1987
