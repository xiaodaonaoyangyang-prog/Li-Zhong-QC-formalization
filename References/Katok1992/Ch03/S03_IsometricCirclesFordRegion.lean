import References.Katok1992.Ch03.S02_DirichletRegion
import LiZhongQC.Lemmas.Mobius

/-!
# Katok 1992, Ch. 3 §3.3 Isometric circles and the Ford fundamental region

S. Katok, *Fuchsian Groups* (1992), Chapter 3, §3.3; source `full.md` of `Fuchsian groups (Katok, Svetlana)
…-3766f6b7…`, lines 1374–1557.

* Definition (isometric circle `I(T)`, its inside and outside; l. 1390–1408) — `mobAct`, `cOf`, `cdFun`, `isometricCircle`
* Theorem 3.3.1 (`T` increases lengths and areas inside `I(T)`, decreases them outside; l. 1410) — `thm3_3_1`
* Theorem 3.3.2 (`I(T)` and `I(T⁻¹)` have the same radius and `T` carries one to the other; l. 1416) —
  `isometricCircle_eq_sphere`, `thm3_3_2`
* Theorem 3.3.3 (isometric circles are geodesics of `ℍ`; l. 1420) — `thm3_3_3`
* Definition (inversion in a circle, (3.3.3)–(3.3.6); l. 1428–1464) — `circleInversion`
* Theorem 3.3.4 (an isometry of the disc is an inversion in `I(T)` followed by a reflection; l. 1466) — `discAct`,
  `reflectBisector`, `thm3_3_4`
* Definition (the isometric circle in the disc; the Ford fundamental region `R₀`; l. 1488–1492) — `discA`, `discC`,
  `discIsometricCircle`, `discIsometricCircle_eq_deriv`, `fordRegionDisc`
* Theorem 3.3.5 (`R₀` is a fundamental region, equal to the Dirichlet region; l. 1494) — `thm3_3_5`
* Lemma 3.3.6 (distances from the centre; l. 1498) — `lemma3_3_6`
* Theorem 3.3.7 (radii of isometric circles tend to zero; l. 1548) — `thm3_3_7`

**Conventions.** `T ∈ PSL(2, ℝ)` acts on `ℂ` by the Möbius map of any lift (`mobAct`, the choice of the lift does not
matter: `−g` gives the same map). The *isometric circle* of `T = ±[a b; c d]` with `c ≠ 0` is `{z | |c z + d| = 1}`
(the book's definition); at the pole `z = −d/c` the value is `0`, so the pole is never on the circle. **Disc model.** The
statements 3.3.4, 3.3.5, 3.3.7 and Lemma 3.3.6 are in the unit disc `𝔘`; the disc group is the conjugate of `Γ` by
Katok's Cayley map `f = cayleyK` (§1.2): the disc matrix of `T` is `[a c̄; c ā]` with `a, c` the explicit entries
`discA T`, `discC T` (the matrix `C A C⁻¹` for the Cayley matrix `C`), `discAct T z = (az + c̄)/(cz + ā)`. This avoids the
pole of `f⁻¹` (computing `f ∘ T ∘ f⁻¹` as functions would have a junk point on the principal circle). The isometric circle of
`T` in `𝔘` is `{z | |cz + ā| = 1}` for `c ≠ 0` (the book excludes `c = 0`: then `T` is a rotation); it is also the locus
`‖(discAct T)′(z)‖ = 1` (`discIsometricCircle_eq_deriv`; the derivative is the junk `0` at the pole, never `1`). Areas in Theorem 3.3.1 scale by the square of the factor of lengths and are not restated.

**Near miss.** `GardinerLakic2000.fordDomain` (formula (2.28)) and `Hubbard2006.prop3_9_12` (the Ford domain of a group
with a parabolic element normalized at `∞` is a fundamental domain, for the topological notion
`IsFundamentalDomainTop`): different normalization, different notion of fundamental domain.
-/

open Set Metric Filter Complex
open scoped UpperHalfPlane MatrixGroups Real Topology

noncomputable section

namespace Katok1992

/-- **The Möbius map of a transformation** (§3.3, (3.3.1)). `T = ±g` acts on `ℂ` by `z ↦ (az + b)/(cz + d)`; the lift is
`Quotient.out T`, and the map does not depend on it (`−g` gives the same function). Near miss: `Nag1988.mobAct` (the same map
for an element of `SL(2, ℝ)`, not of `PSL(2, ℝ)`). -/
def mobAct (T : PSL(2, ℝ)) : ℂ → ℂ :=
  fun z => LiZhongQC.mobiusFn ((Quotient.out T : SL(2, ℝ)) 0 0) ((Quotient.out T : SL(2, ℝ)) 0 1)
    ((Quotient.out T : SL(2, ℝ)) 1 0) ((Quotient.out T : SL(2, ℝ)) 1 1) z

/-- The bottom row of a lift: `c` and `d` of `T = ±[a b; c d]` (`cOf T = c`; the sign of the lift is irrelevant below). -/
def cOf (T : PSL(2, ℝ)) : ℝ := (Quotient.out T : SL(2, ℝ)) 1 0

/-- The linear form `c z + d` of a lift of `T` (the derivative of `T` is `(c z + d)⁻²`). -/
def cdFun (T : PSL(2, ℝ)) (z : ℂ) : ℂ :=
  ((cOf T : ℝ) : ℂ) * z + (((Quotient.out T : SL(2, ℝ)) 1 1 : ℝ) : ℂ)

/-- **Definition** (§3.3; l. 1390–1408). The *isometric circle* of `T = ±[a b; c d]`, `c ≠ 0`: `I(T) = {z | |c z + d| = 1}`,
the circle with centre `−d/c` and radius `1/|c|` (`isometricCircle_eq_sphere`). Defined by the lift `Quotient.out T`
(the set does not depend on the sign of the lift); for `c = 0` the set is empty (the book excludes this case). -/
def isometricCircle (T : PSL(2, ℝ)) : Set ℂ :=
  {z | cOf T ≠ 0 ∧ ‖cdFun T z‖ = 1}

/-- **Unlabelled** (§3.3; l. 1391–1396, the formula for the isometric circle). For `c ≠ 0`, `I(T)` is the Euclidean
circle with centre `−d/c` and radius `1/|c|`. -/
theorem isometricCircle_eq_sphere {T : PSL(2, ℝ)} (hc : cOf T ≠ 0) :
    isometricCircle T = sphere (-(((Quotient.out T : SL(2, ℝ)) 1 1 : ℝ) : ℂ) / (cOf T : ℝ)) (1 / |cOf T|) := by
  sorry

/-- **Theorem 3.3.1** (§3.3; l. 1410). The transformation `T` (`c ≠ 0`) increases Euclidean lengths inside the isometric
circle `I(T)` and decreases them outside it: for `z` not the pole, `|T′(z)| > 1` if `|cz + d| < 1` and `|T′(z)| < 1` if
`|cz + d| > 1`. (Areas are multiplied by `|T′(z)|²`.) -/
theorem thm3_3_1 {T : PSL(2, ℝ)} (hc : cOf T ≠ 0) (z : ℂ) :
    (cdFun T z ≠ 0 → ‖cdFun T z‖ < 1 → 1 < ‖deriv (mobAct T) z‖) ∧
      (1 < ‖cdFun T z‖ → ‖deriv (mobAct T) z‖ < 1) := by
  sorry

/-- **Theorem 3.3.2** (§3.3; l. 1416). The isometric circles `I(T)` and `I(T⁻¹)` have the same radius, and `T` carries
`I(T)` onto `I(T⁻¹)`. -/
theorem thm3_3_2 {T : PSL(2, ℝ)} (hc : cOf T ≠ 0) :
    (∃ (c₁ c₂ : ℂ) (r : ℝ), isometricCircle T = sphere c₁ r ∧ isometricCircle T⁻¹ = sphere c₂ r) ∧
      mobAct T '' isometricCircle T = isometricCircle T⁻¹ := by
  sorry

/-- **Theorem 3.3.3** (§3.3; l. 1420). Isometric circles are geodesics in `ℍ`: for `c ≠ 0`, the part of `I(T)` in `ℍ` is
a geodesic (a semicircle orthogonal to the real axis, as its centre `−d/c` is real). -/
theorem thm3_3_3 {T : PSL(2, ℝ)} (hc : cOf T ≠ 0) :
    IsGeodesic {z : ℍ | (z : ℂ) ∈ isometricCircle T} := by
  sorry

/-- **Inversion in a circle** (§3.3; l. 1428–1464, (3.3.3)–(3.3.5)). For the circle with centre `k` and radius `r`, the
inverse of `z ≠ k` is `z₁ = k + r²/(z̄ − k̄)` (on the ray from `k` through `z`, with `|z₁ − k||z − k| = r²`). *Junk:* at
`z = k` the value is `k`. -/
def circleInversion (k : ℂ) (r : ℝ) (z : ℂ) : ℂ := k + (r : ℂ) ^ 2 / (starRingEnd ℂ) (z - k)

/-- **Reflection in the perpendicular bisector of the segment `[p, q]`** (Euclidean). For `u = (q − p)/|q − p|` it is
`w ↦ w − 2 Re((w − (p + q)/2) ū) u`. *Junk:* for `p = q` the vector `u` is `0` and the map is the identity. -/
def reflectBisector (p q w : ℂ) : ℂ :=
  w - 2 * (((w - (p + q) / 2) * (starRingEnd ℂ) ((q - p) / ‖q - p‖)).re : ℝ) * ((q - p) / ‖q - p‖)

/-- **The disc matrix of a transformation, entry `a`** (§3.3; l. 1397–1405, Remark 2). With Katok's Cayley map
`f(z) = (iz + 1)/(z + i)` (matrix `C = [i 1; 1 i]`), the conjugate `f ∘ T ∘ f⁻¹` of `T = ±[α β; γ δ]` has the matrix
`C A C⁻¹ ∼ [a c̄; c ā]` with `a = (−(α + δ) + i(γ − β))/2` and `c = (−(β + γ) + i(α − δ))/2`, `|a|² − |c|² = 1`: the
form `T(z) = (az + c̄)/(cz + ā)` of (3.3.2). The lift is `Quotient.out T`; `−g` changes the sign of `a` and `c`
together (the map and the circle below do not change). -/
def discA (T : PSL(2, ℝ)) : ℂ :=
  ((-((Quotient.out T : SL(2, ℝ)) 0 0 + (Quotient.out T : SL(2, ℝ)) 1 1) / 2 : ℝ) : ℂ) +
    Complex.I * (((((Quotient.out T : SL(2, ℝ)) 1 0 - (Quotient.out T : SL(2, ℝ)) 0 1) / 2 : ℝ)) : ℂ)

/-- The entry `c` of the disc matrix of `T` (see `discA`); `c = 0` iff `T` fixes `i`, i.e. `T(0) = 0` in the disc. -/
def discC (T : PSL(2, ℝ)) : ℂ :=
  ((-((Quotient.out T : SL(2, ℝ)) 0 1 + (Quotient.out T : SL(2, ℝ)) 1 0) / 2 : ℝ) : ℂ) +
    Complex.I * (((((Quotient.out T : SL(2, ℝ)) 0 0 - (Quotient.out T : SL(2, ℝ)) 1 1) / 2 : ℝ)) : ℂ)

/-- **The disc model of a transformation** (§3.3; l. 1397–1405, Remark 2): the Möbius map `z ↦ (az + c̄)/(cz + ā)` of the
unit disc `𝔘 = f(ℍ)` corresponding to `T` (it is `f ∘ T ∘ f⁻¹` where defined). Defined from the matrix entries, so the only
junk point is its own pole `−ā/c`, which lies outside the closed disc (`|a|² − |c|² = 1`). -/
def discAct (T : PSL(2, ℝ)) : ℂ → ℂ :=
  LiZhongQC.mobiusFn (discA T) ((starRingEnd ℂ) (discC T)) (discC T) ((starRingEnd ℂ) (discA T))

/-- **Theorem 3.3.4** (§3.3; l. 1466). Any orientation-preserving isometry `T(z) = (az + c̄)/(cz + ā)`,
`a, c ∈ ℂ`, `|a|² − |c|² = 1`, `c ≠ 0`, of the unit disc is an inversion in its isometric circle `I(T)` (centre
`−ā/c`, radius `1/|c|`) followed by the Euclidean reflection in the bisector `L` of the centres `−ā/c` of `I(T)` and
`a/c` of `I(T⁻¹)`. *Correction:* the hypothesis `Re a ≠ 0` is added: the two centres coincide iff `a + ā = 0`, and then the
bisector is undefined (`reflectBisector` is the identity there and the formula is false, e.g. `a = i√2`, `c = 1`, `z = 1`). -/
theorem thm3_3_4 {a c : ℂ} (hc : c ≠ 0) (ha : a.re ≠ 0) (h : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1) (z : ℂ) (hz : z ≠ -(starRingEnd ℂ) a / c) :
    (a * z + (starRingEnd ℂ) c) / (c * z + (starRingEnd ℂ) a) =
      reflectBisector (-(starRingEnd ℂ) a / c) (a / c) (circleInversion (-(starRingEnd ℂ) a / c) (1 / ‖c‖) z) := by
  sorry

/-- **The isometric circle in the disc** (§3.3; l. 1488–1492). For `T` with `c ≠ 0` (equivalently `T(0) ≠ 0`), the circle
`I(T) = {z | |c z + ā| = 1}` of centre `−ā/c` and radius `1/|c|`, where `T` acts as a Euclidean isometry. -/
def discIsometricCircle (T : PSL(2, ℝ)) : Set ℂ :=
  {z | discC T ≠ 0 ∧ ‖discC T * z + (starRingEnd ℂ) (discA T)‖ = 1}

/-- **Unlabelled** (§3.3; l. 1486). In the disc, `I(T)` is the locus where `T` acts as a Euclidean isometry:
`‖(discAct T)′(z)‖ = 1` for `c ≠ 0` (the derivative is `(cz + ā)⁻²`; at the pole it is the junk `0`, never `1`). -/
theorem discIsometricCircle_eq_deriv {T : PSL(2, ℝ)} (hc : discC T ≠ 0) :
    discIsometricCircle T = {z | ‖deriv (discAct T) z‖ = 1} := by
  sorry

/-- **Definition** (the Ford fundamental region; §3.3, l. 1488–1492). For `Γ` acting on the unit disc with `c ≠ 0` for
all non-identity elements, `R₀` is the closure in `𝔘` of the set of points of `𝔘` exterior to the isometric circles
`I(T)` (`‖T′(z)‖ < 1`) of all `T ∈ Γ` with `c ≠ 0` (`‖c w + ā‖ > 1`). -/
def fordRegionDisc (Γ : Subgroup PSL(2, ℝ)) : Set ℂ :=
  {z | ‖z‖ < 1 ∧ z ∈ closure {w : ℂ | ‖w‖ < 1 ∧ ∀ T ∈ Γ, discC T ≠ 0 → 1 < ‖discC T * w + (starRingEnd ℂ) (discA T)‖}}

/-- **Theorem 3.3.5** (§3.3; l. 1494). Let `Γ` be a Fuchsian group such that `0` is not an elliptic fixed point of the disc
group (`T(i) ≠ i` for `T ≠ Id`, i.e. `c ≠ 0`). Then the Ford region `R₀` is a fundamental region for `Γ` (transported
to `ℍ` by `f = cayleyK`); it is the Dirichlet region `D_0(Γ)`, i.e. `D_i(Γ)` in `ℍ`. -/
theorem thm3_3_5 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (h0 : ∀ T ∈ Γ, T ≠ 1 → T • UpperHalfPlane.I ≠ UpperHalfPlane.I) :
    IsFundamentalRegion Γ {z : ℍ | cayleyK (z : ℂ) ∈ fordRegionDisc Γ} ∧
      {z : ℍ | cayleyK (z : ℂ) ∈ fordRegionDisc Γ} = dirichletRegion Γ UpperHalfPlane.I := by
  sorry

/-- **Lemma 3.3.6** (§3.3; l. 1498–1546). Let `T` act on the unit disc `𝔘` with `T(0) ≠ 0`, and let `h = |z|`,
`h′ = |T(z)|` be the Euclidean distances from the centre of the principal circle `Σ = ∂𝔘`. For `z ∈ 𝔘 ∪ Σ`:
(i) `h′ = h` if `z ∈ I(T)` or `z ∈ Σ`; (ii) `h′ < h` if `z` is inside `I(T)`; (iii) `h′ > h` if `z` is outside `I(T)`. -/
theorem lemma3_3_6 {T : PSL(2, ℝ)} (hT : discC T ≠ 0) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ((‖discC T * z + (starRingEnd ℂ) (discA T)‖ = 1 ∨ ‖z‖ = 1) → ‖discAct T z‖ = ‖z‖) ∧
      (‖z‖ < 1 → ‖discC T * z + (starRingEnd ℂ) (discA T)‖ < 1 → ‖discAct T z‖ < ‖z‖) ∧
      (‖z‖ < 1 → 1 < ‖discC T * z + (starRingEnd ℂ) (discA T)‖ → ‖z‖ < ‖discAct T z‖) := by
  sorry

/-- **Theorem 3.3.7** (§3.3; l. 1548). Let `Γ` be a Fuchsian group (acting on the disc) and `I_n` an infinite sequence of
distinct isometric circles of transformations `T_n ∈ Γ`, with radii `r_n`. Then `lim r_n = 0`. -/
theorem thm3_3_7 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (T : ℕ → PSL(2, ℝ)) (hT : ∀ n, T n ∈ Γ)
    (k : ℕ → ℂ) (r : ℕ → ℝ) (hI : ∀ n, discIsometricCircle (T n) = sphere (k n) (r n))
    (hne : ∀ n, discC (T n) ≠ 0) (hdist : Pairwise fun m n => discIsometricCircle (T m) ≠ discIsometricCircle (T n)) :
    Tendsto r atTop (𝓝 0) := by
  sorry

end Katok1992
