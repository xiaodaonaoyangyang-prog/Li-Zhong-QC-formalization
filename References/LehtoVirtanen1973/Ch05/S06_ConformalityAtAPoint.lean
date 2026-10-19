import References.LehtoVirtanen1973.Ch01.S06_ModuleRingDomain
import References.LehtoVirtanen1973.Ch04.S05_ComplexDilatation

/-!
# Lehto–Virtanen, Chapter V §6: Conformality at a point

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. V §6
(pp. 219–233; `full.md` P2:763–1327).

Conventions. The module estimates of §6.3 concern a quasiconformal mapping `w : G → G′` of a domain of `ℂ̄`; its
dilatation quotient `D` is Ch. I's `dilQuot` (read in the charts at `∞` and at `w⁻¹(∞)`), the book's `D` at the
regular points of `w`, i.e. almost everywhere (Theorem IV.1.4); the junk values at the other points lie on a null set
and are not seen by the integrals `∫⁻`. The module of a family of arcs or curves is that of III.4 (`arcFamilyModule`,
on point-set families of `ℂ̄`, with the admissible functions `IsAdmissibleFor`), and the image family of `𝒞` is the
family of the images `w(C)`, `C ∈ 𝒞`. Areas and integrals over sets of `ℂ̄` are taken over their finite parts
(`References.finitePart`, III.4.1). From §6.4 on, `w` is a quasiconformal mapping of the plane `ℂ̄` fixing `0` and `∞`
(or of the finite plane onto itself), i.e. `OnePoint.map f` for a finite `f : ℂ → ℂ`; "conformal at `0`" is the
existence of a finite non-zero complex derivative of `f` at `0` (§6.1). A function `ε` of `|z|` with
`ε(|z|) → 0` as `z → 0` is a function `ε : ℝ → ℝ` tending to `0` at `0⁺`. "`ε` depends only on `K` and `I`" is
expressed by the quantifier order: `ε` is chosen after `K` and the function `I : ℝ → [0, ∞]`, before the mapping.
The book proves (6.14), Lemma 6.2 and Theorem 6.1 for small `|z|`; the bounds are stated for all `z ≠ 0` (leader
decision: LV's (6.14) has no range restriction, and for large `|z|` a bound depending only on `K`, `I` and `|z|`
follows from the Hölder continuity (6.11) in the logarithmic plane).

* Definition (conformal at a point `z₀ ≠ ∞`, §6.1) — exists: `HasDerivAt` (a homeomorphism w of a neighbourhood of a
  finite point z₀ is conformal at z₀ when the difference quotient tends to a finite non-zero limit, i.e. its finite
  map has a non-zero complex derivative c at z₀, HasDerivAt f c z₀ with c ≠ 0)
* Unlabelled (§6.2, P2:849; recalled P2:1332, used in the proofs of the theorems of §7): the integral (6.5) of
  `(D(z) − 1)/|z|²` over `|z| < R` is finite if and only if that of `|κ(z)|/|z|²` is — `dilQuot_integral_lt_top_iff`
* Formula (6.6) (§6.3) — `eq5_6_6`
* Formula (6.7) (§6.3) — `eq5_6_7`
* Formula (6.9) (§6.3), with its one-sided half (6.8) — `eq5_6_9`
* Formula (6.10) (§6.4): the transition to the logarithmic plane `f(ζ) = log w(e^ζ)` — `eq5_6_10`
* Formula (6.11) (§6.4) — `eq5_6_11`
* Definition (the dilatation integral `I(r)` of (6.12), §6.5) — `dilatationIntegral`
* Lemma 6.1 (§6.5, Teichmüller, Wittich) — `lemma5_6_1`
* Lemma 6.2 (§6.6, cf. Belinskij) — `lemma5_6_2`
* Theorem 6.1 (§6.7), with (6.37) — `thm5_6_1`
* Unlabelled (§6.7, P2:1312, first Remark; cited P2:1458 as "the first remark at the end of 6.7"): the conclusions of
  Theorem 6.1 hold with `ε` depending only on `K` and a majorant `Δ(r) → 0` of `I(r)` — `thm5_6_1_uniform`

Not stated (inventory: omitted): the claim of 6.1 that regularity at `z₀` depends only on the complex dilatation near
`z₀` (P2:769, immediate from the Uniqueness theorem); the normalization (6.1); the examples of 6.2, (6.2)–(6.4), with
the radial mappings and `z/(1 − log |z|)` (P2:781–839); the steps (6.15)–(6.36) of the proofs of Lemmas 6.1 and 6.2
(among them the use of (9.1) of II.9.2, P2:1034); the elementary inequality `|z₁ − z₂| ≤ |r₁ − r₂| + r₂ |φ₁ − φ₂|` and
the values `w_z(0) = c e^{iα}`, `w_{\bar z}(0) = 0` in the derivation of Theorem 6.1 (P2:1286–1292); the second Remark
after Theorem 6.1 (the sharpening `|w_z(0)| ≤ 4 min |w| e^{I(1)}` by Koebe's one-quarter theorem, P2:1314–1326, not
cited); the intermediate module bounds of 6.3 (P2:867–909, steps of (6.7) and (6.9)), the equicontinuity and
pointwise Hölder continuity of the family `𝓕` (P2:931–937, steps of (6.11)), and the single-valuedness of `arg(w/z)`
for `z ≠ 0, ∞` (P2:929; absorbed by the modelling of Lemma 6.2). Footnote 51 is bibliographic.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane extInf toExt IsJordanCurve)
open References (IsDomainExt finitePart)

/-! ## §6.2 Examples: the integral (6.5) -/

/-- **Unlabelled** (Ch. V §6.2, P2:849; recalled at P2:1332 and used in the proofs of Theorems 7.1 and 7.2). Let `w` be
a `K`-quasiconformal mapping of `G` with complex dilatation `κ` and dilatation quotient `D`, and `U = {z | |z| < R}` a
disc in `G`. Since `D(z) − 1 = 2|κ(z)|/(1 − |κ(z)|)`, the convergence of the integral
`∬_U (D(z) − 1)/|z|² dσ` (6.5) is equivalent to `∬_U |κ(z)|/|z|² dσ < ∞`.
Modelling: the book's setting (6.1–6.2): the point under study is the origin, `U` a disc about it in `G`. `κ` is
IV.5's `complexDilatationLV` and `D` is `dilQuot`, the book's values at the regular points of `w`, i.e. almost
everywhere in `U` (at most one point of `U` is mapped to `∞`, where both are read in the charts);
`|κ| ≤ (K − 1)/(K + 1)` almost everywhere, the bound `sup |κ| < 1` of 6.1. The integrals are taken in `[0, ∞]`; the
integrand `(D − 1)/|z|²` is non-negative at the regular points, where `D ≥ 1`. -/
theorem dilQuot_integral_lt_top_iff {w : ExtPlane → ExtPlane} {G : Set ExtPlane} {K : ℝ}
    (hw : IsKQuasiconformal w G K) {R : ℝ} (hR : 0 < R) (hUG : toExt (Metric.ball (0 : ℂ) R) ⊆ G) :
    ∫⁻ z in Metric.ball (0 : ℂ) R, ENNReal.ofReal ((dilQuot w z - 1) / ‖z‖ ^ 2) < ⊤ ↔
      ∫⁻ z in Metric.ball (0 : ℂ) R, ENNReal.ofReal (‖complexDilatationLV w z‖ / ‖z‖ ^ 2) < ⊤ := by
  sorry

/-! ## §6.3 Module estimations in terms of the means of `D` -/

/-- **Formula (6.6)** (Ch. V §6.3). Let `w : G → G′` be a quasiconformal mapping with dilatation quotient `D`, `𝒞` a
family of arcs or curves `C ⊂ G` and `𝒞′` the family of their images `w(C)`. Then `M(𝒞′) ≤ ∬_G D ρ² dσ` (6.6) for
every `ρ` admissible for `𝒞`. (The book obtains it by applying (3.8) of IV.3.3 to the inverse of `w`.)
Modelling: the arcs and curves are Jordan arcs and Jordan curves of `ℂ̄` contained in `G`; the families are point-set
families and the module is `arcFamilyModule` (III.4), for which the images of non-rectifiable arcs are admitted like
any other point sets; the integral is taken over the finite part of `G`, in `[0, ∞]`. -/
theorem eq5_6_6 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G)
    {𝒞 : Set (Set ExtPlane)} (h𝒞 : ∀ C ∈ 𝒞, (IsJordanArc C ∨ IsJordanCurve C) ∧ C ⊆ G) {ρ : ℂ → ℝ≥0∞}
    (hρ : IsAdmissibleFor 𝒞 ρ) :
    arcFamilyModule ((fun C => w '' C) '' 𝒞) ≤ ∫⁻ z in finitePart G, ENNReal.ofReal (dilQuot w z) * ρ z ^ 2 := by
  sorry

/-- **Formula (6.7)** (Ch. V §6.3). Let `w : G → G′` be quasiconformal and `Q = {x + iy | a < x < b, c < y < d}` a
horizontal rectangle with `Q̄ ⊂ G`. Then `M(w(Q))/M(Q) ≤ (1/m(Q)) ∬_Q D dσ` (6.7), where `m(Q)` is the area of `Q`;
the same upper bound holds for `M(Q)/M(w(Q))`.
Modelling: `Q` is a quadrilateral which is a horizontal rectangle (`Quadrilateral.IsHorizontalRectangle`, IV.1.1);
`M(w(Q))` is the module of the image domain with the image vertices, the book's module since `w` is
sense-preserving. The inequalities are multiplied out by `M(Q) > 0`, `M(w(Q)) > 0` and `0 < m(Q) < ∞`. -/
theorem eq5_6_7 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) (Q : Quadrilateral)
    (hQ : Q.IsHorizontalRectangle) (hQG : closure Q.dom ⊆ G) :
    ENNReal.ofReal (quadModule (w '' Q.dom) (w ∘ Q.vert)) * Q.area ≤
        ENNReal.ofReal Q.module * ∫⁻ z in finitePart Q.dom, ENNReal.ofReal (dilQuot w z) ∧
      ENNReal.ofReal Q.module * Q.area ≤
        ENNReal.ofReal (quadModule (w '' Q.dom) (w ∘ Q.vert)) *
          ∫⁻ z in finitePart Q.dom, ENNReal.ofReal (dilQuot w z) := by
  sorry

/-- **Formula (6.9)** (Ch. V §6.3), with (6.8). Let `w : G → G′` be quasiconformal and `B = {z | r < |z| < R}` an
annulus with `B̄ ⊂ G` and `M(B) < ∞`. Then `|M(w(B)) − M(B)| ≤ (1/2π) ∬_B (D(z) − 1)/|z|² dσ` (6.9); the first half,
`M(w(B)) − M(B) ≤ (1/2π) ∬_B (D(z) − 1)/|z|² dσ`, is (6.8).
Modelling: `0 < r < R < ∞`, so that `M(B) = log (R/r)` is finite, as the book's derivation of (6.9) requires
(P2:899). The absolute value is written as two inequalities in `[0, ∞]` (`ringModule` is `[0, ∞]`-valued); the
integrand `(D − 1)/|z|²` is non-negative at the regular points, where `D ≥ 1`. -/
theorem eq5_6_9 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (hBG : closure (annulusExt r (ENNReal.ofReal R)) ⊆ G) :
    ringModule (w '' annulusExt r (ENNReal.ofReal R)) ≤ ringModule (annulusExt r (ENNReal.ofReal R)) +
        ENNReal.ofReal (1 / (2 * Real.pi)) *
          ∫⁻ z in {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}, ENNReal.ofReal ((dilQuot w z - 1) / ‖z‖ ^ 2) ∧
      ringModule (annulusExt r (ENNReal.ofReal R)) ≤ ringModule (w '' annulusExt r (ENNReal.ofReal R)) +
        ENNReal.ofReal (1 / (2 * Real.pi)) *
          ∫⁻ z in {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}, ENNReal.ofReal ((dilQuot w z - 1) / ‖z‖ ^ 2) := by
  sorry

/-! ## §6.4 Transition to the logarithmic plane -/

/-- **Formula (6.10)** (Ch. V §6.4). Let `w` be a `K`-quasiconformal mapping of the plane with `w(0) = 0`,
`w(∞) = ∞`. The mapping `f(ζ) = log w(e^ζ)` of the strip `0 < Im ζ < 2π` extends to the whole finite plane as a
continuous function `f = u + iv` with `f(ζ + 2nπi) = f(ζ) + 2nπi`, `n = 0, ±1, …` (6.10), so that `v(ζ)` is a branch
of `arg w(e^ζ)`; `f` is a homeomorphism of the plane, it is `K`-quasiconformal, and at the points `ζ = log z + 2nπi`
the dilatation quotient of `f` has the same value as that of `w` at `z`, provided that `w` is regular at `z`.
Modelling: `w = OnePoint.map g` (a quasiconformal mapping of `ℂ̄` fixing `∞` is of this form); `f` is a logarithm of
`g ∘ exp`, i.e. `e^{f(ζ)} = w(e^ζ)`, and `f` is continuous (it is `K`-quasiconformal), so `v = Im f` is a continuous
branch of `arg w(e^ζ)`; "homeomorphism of the plane" is `K`-quasiconformality in the finite plane together with
surjectivity; the points `log z + 2nπi` are the `ζ` with `e^ζ = z`. -/
theorem eq5_6_10 {g : ℂ → ℂ} {K : ℝ} (hg : IsKQuasiconformal (OnePoint.map g) univ K) (hg0 : g 0 = 0) :
    ∃ f : ℂ → ℂ, (∀ ζ, g (Complex.exp ζ) = Complex.exp (f ζ)) ∧
      (∀ (ζ : ℂ) (n : ℤ), f (ζ + 2 * Real.pi * n * I) = f ζ + 2 * Real.pi * n * I) ∧
      Function.Surjective f ∧ IsKQuasiconformal (OnePoint.map f) (toExt univ) K ∧
      ∀ ζ : ℂ, IsRegularPointOf (OnePoint.map g) univ ((Complex.exp ζ : ℂ) : ExtPlane) →
        dilQuot (OnePoint.map f) (ζ : ExtPlane) = dilQuot (OnePoint.map g) ((Complex.exp ζ : ℂ) : ExtPlane) := by
  sorry

/-- **Formula (6.11)** (Ch. V §6.4). Let `𝓕` be the family of all `K`-quasiconformal mappings `f` of the plane
satisfying (6.10). There are two positive numbers `C` and `d`, depending only on `K`, such that
`|f(ζ) − f(ζ₀)| ≤ C |ζ − ζ₀|^{1/K}` (6.11) for all `f ∈ 𝓕`, all finite `ζ₀` and `|ζ − ζ₀| ≤ d`.
Modelling: the members of `𝓕` are the `K`-quasiconformal homeomorphisms `f` of the finite plane onto itself with
(6.10), as in `eq5_6_10`; `C`, `d` are chosen after `K` and before `f`, `ζ₀`. `1 ≤ K` is the book's standing
`K ≥ 1` (H8); for `K < 1` the family is empty (and `1/K` would be a junk value at `K = 0`). -/
theorem eq5_6_11 {K : ℝ} (hK : 1 ≤ K) :
    ∃ C d : ℝ, 0 < C ∧ 0 < d ∧ ∀ f : ℂ → ℂ, IsKQuasiconformal (OnePoint.map f) (toExt univ) K →
      Function.Surjective f → (∀ (ζ : ℂ) (n : ℤ), f (ζ + 2 * Real.pi * n * I) = f ζ + 2 * Real.pi * n * I) →
        ∀ ζ₀ ζ : ℂ, ‖ζ - ζ₀‖ ≤ d → ‖f ζ - f ζ₀‖ ≤ C * ‖ζ - ζ₀‖ ^ (1 / K) := by
  sorry

/-! ## §6.5 Convergence of the absolute value -/

/-- **Definition** (the dilatation integral `I(r)`, Ch. V §6.5, (6.12)).
`I(r) = (1/2π) ∬_{|z| < r} (D(z) − 1)/|z|² dσ`, where `D` is the dilatation quotient of the mapping `w`.
Modelling: `[0, ∞]`-valued (the integral may diverge). The integrand is the book's at the regular points of `w`
(where `D ≥ 1`), i.e. almost everywhere for a quasiconformal `w`; the junk values of `dilQuot` at the other points and
the value `x/0 = 0` at `z = 0` lie on a null set, which the integral does not see. -/
def dilatationIntegral (w : ExtPlane → ExtPlane) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) *
    ∫⁻ z in Metric.ball (0 : ℂ) r, ENNReal.ofReal ((dilQuot w z - 1) / ‖z‖ ^ 2)

/-- **Lemma 6.1** (Ch. V §6.5, Teichmüller, Wittich). Let `w` be a `K`-quasiconformal mapping of the plane with
`w(0) = 0`, `w(∞) = ∞`, and `I(r) < ∞` for `r < ∞` (6.12). Then there exists a constant `c` with
`min_{|z|=1} |w(z)| e^{−I(1)} ≤ c ≤ max_{|z|=1} |w(z)| e^{I(1)}` (6.13) such that `||w(z)/z| − c| ≤ c ε(|z|)` (6.14),
where `ε(|z|) → 0` as `z → 0` and the function `ε` depends only on `K` and `I`.
Modelling: `w = OnePoint.map f`; the book's function `r ↦ I(r)` is a given `I : ℝ → [0, ∞]`, finite for `r > 0`, and
the hypothesis is that the dilatation integral of `w` equals `I(r)` for every `r > 0`; `ε` is chosen after `K` and
`I` and before `w` (see the module docstring for the range `z ≠ 0`). `I(1) < ∞`, so `(I 1).toReal` is `I(1)`; the
minimum and the maximum of the continuous `|w|` over the circle `|z| = 1` are the infimum and the supremum over the
circle as a subtype (bounded and nonempty). -/
theorem lemma5_6_1 (K : ℝ) (I : ℝ → ℝ≥0∞) (hI : ∀ r : ℝ, 0 < r → I r < ⊤) :
    ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∀ f : ℂ → ℂ, IsKQuasiconformal (OnePoint.map f) univ K → f 0 = 0 →
      (∀ r : ℝ, 0 < r → dilatationIntegral (OnePoint.map f) r = I r) →
        ∃ c : ℝ, (⨅ z : Metric.sphere (0 : ℂ) 1, ‖f z‖) * Real.exp (-(I 1).toReal) ≤ c ∧
          c ≤ (⨆ z : Metric.sphere (0 : ℂ) 1, ‖f z‖) * Real.exp (I 1).toReal ∧
          ∀ z : ℂ, z ≠ 0 → |‖f z‖ / ‖z‖ - c| ≤ c * ε ‖z‖ := by
  sorry

/-! ## §6.6 Convergence of the argument -/

/-- **Lemma 6.2** (Ch. V §6.6, cf. Belinskij). Under the hypotheses of Lemma 6.1, `arg w(z) − arg z` tends to a limit
`α` as `z → 0`. The rate of convergence depends on `K` and `I` but not otherwise on the mapping `w`.
Modelling: `arg w(z) − arg z` is the book's branch of `arg (w(z)/z)`, fixed in 6.4 through (6.10): a single-valued
continuous function `θ` on `z ≠ 0` with `w(z)/z = |w(z)/z| e^{iθ(z)}`. Any two such branches differ by a constant
multiple of `2π`, so the statement is made for every continuous branch `θ` (one exists, by `eq5_6_10`), with a limit
`α` depending on the branch; `Complex.arg` is not used. The rate of convergence is a function `ε` of `|z|`, chosen
after `K` and `I` and before `w`, with `|θ(z) − α| ≤ ε(|z|)`. -/
theorem lemma5_6_2 (K : ℝ) (I : ℝ → ℝ≥0∞) (hI : ∀ r : ℝ, 0 < r → I r < ⊤) :
    ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∀ f : ℂ → ℂ, IsKQuasiconformal (OnePoint.map f) univ K → f 0 = 0 →
      (∀ r : ℝ, 0 < r → dilatationIntegral (OnePoint.map f) r = I r) →
        ∀ θ : ℂ → ℝ, ContinuousOn θ {0}ᶜ →
          (∀ z : ℂ, z ≠ 0 → f z / z = (‖f z / z‖ : ℂ) * Complex.exp ((θ z : ℂ) * Complex.I)) →
            ∃ α : ℝ, ∀ z : ℂ, z ≠ 0 → |θ z - α| ≤ ε ‖z‖ := by
  sorry

/-! ## §6.7 Summary of the results -/

/-- **Theorem 6.1** (Ch. V §6.7). Let `w` be a `K`-quasiconformal mapping of the finite plane onto itself with
`w(0) = 0` and `I(r) = (1/2π) ∬_{|z|<r} (D(z) − 1)/|z|² dσ < ∞` for `r < ∞`. Then `w` is conformal at `z = 0` and
`|w(z)/z − w_z(0)| < |w_z(0)| ε(|z|)`, `lim_{|z| → 0} ε(|z|) = 0`, where the function `ε` depends only on `K` and `I`
and not otherwise on the mapping `w`. The derivative `w_z(0)` satisfies
`min_{|z|=1} |w(z)| e^{−I(1)} ≤ |w_z(0)| ≤ max_{|z|=1} |w(z)| e^{I(1)}` (6.37).
Modelling: `w = OnePoint.map f` with `f` onto; conformality at `0` is a non-zero complex derivative `a` of `f` at
`0`, which is `w_z(0)` (and `w_{\bar z}(0) = 0`); `I`, `ε` and the minimum and maximum over `|z| = 1` as in
`lemma5_6_1`. -/
theorem thm5_6_1 (K : ℝ) (I : ℝ → ℝ≥0∞) (hI : ∀ r : ℝ, 0 < r → I r < ⊤) :
    ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∀ f : ℂ → ℂ, IsKQuasiconformal (OnePoint.map f) (toExt univ) K →
      Function.Surjective f → f 0 = 0 → (∀ r : ℝ, 0 < r → dilatationIntegral (OnePoint.map f) r = I r) →
        ∃ a : ℂ, a ≠ 0 ∧ HasDerivAt f a 0 ∧ (∀ z : ℂ, z ≠ 0 → ‖f z / z - a‖ < ‖a‖ * ε ‖z‖) ∧
          (⨅ z : Metric.sphere (0 : ℂ) 1, ‖f z‖) * Real.exp (-(I 1).toReal) ≤ ‖a‖ ∧
          ‖a‖ ≤ (⨆ z : Metric.sphere (0 : ℂ) 1, ‖f z‖) * Real.exp (I 1).toReal := by
  sorry

/-- **Unlabelled** (Ch. V §6.7, P2:1312, first Remark after Theorem 6.1; cited P2:1458). From the proofs of Lemmas 6.1
and 6.2 our result can be expressed in a slightly more general form: if `I(r) ≤ Δ(r)`, where `Δ(r) → 0` as `r → 0`,
then the conclusions of Theorem 6.1 hold for a function `ε` depending only on `K` and `Δ`.
Modelling: [OCR or misprint] P2:1312 reads "the proofs of Lemmas 1 and 2", i.e. of Lemmas 6.1 and 6.2. As in
`thm5_6_1`, with `ε` chosen after `K` and `Δ : ℝ → [0, ∞]`. The hypothesis `I(r) < ∞` of Theorem 6.1 is not assumed,
since it follows: `Δ(r₀) < ∞` for some `r₀ > 0` (as `Δ(r) → 0`), so `I(r₀) ≤ Δ(r₀) < ∞`, and for `r > r₀` the rest of
the integral, over `r₀ ≤ |z| < r`, is finite because `D ≤ K` almost everywhere. The conclusions that involve `ε` are
stated; (6.37), which does not involve `ε`, is `thm5_6_1`. -/
theorem thm5_6_1_uniform (K : ℝ) (Δ : ℝ → ℝ≥0∞) (hΔ : Tendsto Δ (𝓝[>] 0) (𝓝 0)) :
    ∃ ε : ℝ → ℝ, Tendsto ε (𝓝[>] 0) (𝓝 0) ∧ ∀ f : ℂ → ℂ, IsKQuasiconformal (OnePoint.map f) (toExt univ) K →
      Function.Surjective f → f 0 = 0 → (∀ r : ℝ, 0 < r → dilatationIntegral (OnePoint.map f) r ≤ Δ r) →
        ∃ a : ℂ, a ≠ 0 ∧ HasDerivAt f a 0 ∧ ∀ z : ℂ, z ≠ 0 → ‖f z / z - a‖ < ‖a‖ * ε ‖z‖ := by
  sorry

end LehtoVirtanen1973
