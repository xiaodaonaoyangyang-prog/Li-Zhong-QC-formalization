import References.Pommerenke1992.Ch09.S02_ModuleOfACurveFamily
import References.GarnettMarshall2005.Ch03.S04_EquilibriumDistribution

/-!
# Pommerenke 1992, Ch. 9 §9.3 Capacity and Green's Function

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), Chapter 9 *Curve Families and Capacity*, §9.3; source
`full.md` of `boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-798face3…` (P2), lines 749–1162.

* Definition (the outer domain of a compact set `E`, P2 l. 751: "the component of `Ĉ ∖ E` with `∞ ∈ G`"; index "outer
  domain 203") — exists: `GarnettMarshall2005.unboundedComponentExt` (the connected component of the complement of E
  in the extended plane that contains ∞, literally the book's definition)
* Definition (`Δ_n(E)`, (9.3.1), P2 l. 751–755; used in (9.3.3), (9.3.6), (9.3.7) and at P2 l. 1051) — `feketeDelta`
* Definition (Fekete points, (9.3.2), P2 l. 757–763; used in the proofs of Theorem 9.7, Proposition 9.16 and at P2
  l. 1841) — `IsFeketeSystem`
* Unlabelled (§9.3, P2 l. 757: "The maximum is assumed for the Fekete points"; every statement on Fekete points
  presupposes it) — `exists_isFeketeSystem`
* Definition (the `n`th Fekete polynomial `q_n`, (9.3.4), P2 l. 769–775; cited "(9.3.4)" at P2 l. 1203, used in
  (9.3.13), (9.3.21) and at P2 l. 1841) — `feketePoly`
* Definition (`γ_n`, (9.3.5), P2 l. 775–779; used in (9.3.6), (9.3.13), (9.3.21) and at P2 l. 975) — `feketeGamma`
* Formula (9.3.6) (P2 l. 781–791; cited "(6)" at P2 l. 867) — `eq9_3_6`
* Unlabelled (§9.3, P2 l. 793: "`Δ_n^{1/[n(n−1)]}` is decreasing"; the definition (9.3.7) rests on it) —
  `feketeDelta_rpow_antitone`
* Definition (the (logarithmic) capacity of a compact set, the "transfinite diameter", (9.3.7), P2 l. 793–799; index
  "capacity", "logarithmic capacity 203", "transfinite diameter 203") — exists: `GarnettMarshall2005.capacityCompact`
  (leader ruling QD1: one capacity for Pommerenke and GM; GM III (1.3) defines it through Robin's constant along
  smooth exhaustions, with the same normalization, a disc of radius r having capacity r; values in [0, ∞];
  Pommerenke's defining formula is the theorem eq9_3_7 below)
* Formula (9.3.7) (P2 l. 793–797; Pommerenke's definition of capacity, stated as the equality with GM's capacity, the
  Fekete–Szegő theorem; U+ by the leader ruling QD1) — `eq9_3_7`
* Formula (9.3.10) (printed with the tag "(11)" [OCR]; cited "(10)" at P2 l. 995, 1053 and "(9.3.10)" at P2 l. 1477)
  — `eq9_3_10`
* Formula (9.3.11) (printed untagged [OCR]; cited "(11)" at P2 l. 1035 and "(9.3.11)" at P2 l. 1477; the contraction
  of (6.2.9)) — exists: `GarnettMarshall2005.thm3_4_5_a` `GarnettMarshall2005.eq3_1_5` (GM III Theorem 4.5: for
  compact E and a map with the contraction property on E, the capacity of the image is at most that of E; GM states
  it for the capacity (4.8), which on compact sets is the compact capacity (1.3) of this file, the supremum over the
  compact subsets being attained at E itself by the monotonicity (1.5))
* Proposition 9.6 ((9.3.12), (9.3.13); cited at P2 l. 909, "(13)" at P2 l. 947, 975, 1117, 1204 and at P2 l. 1841) —
  `prop9_6_a`, `prop9_6_b`, `prop9_6_c`
* Definition (probability measure on the compact set `E`, P2 l. 875) — exists: `GarnettMarshall2005.probMeasuresOn`
  (the probability measures on ℂ that vanish off E, which are the book's measures on E extended by zero)
* Theorem 9.7 (Myr33, Lej34; (9.3.17)–(9.3.19); cited at P2 l. 977, 1059, 1123, 1135, 1181, 1254, 1284) — `thm9_7`
* Definition (equilibrium measure; the (extended) Green's function with pole at `∞`, P2 l. 897; index "equilibrium
  measure 205", "Green's function 205") — `IsEquilibriumMeasure`, `greenFnInf`
* Formula (9.3.20) (cited "by (20)" at P2 l. 953; index "semicontinuous 205") — `eq9_3_20`
* Theorem 9.8 ((9.3.27); cited at P2 l. 993, 1065) — `thm9_8_a`, `thm9_8_b`
* Corollary 9.9 ((9.3.28), (9.3.29); cited at P2 l. 995, 1007, 1570) — `cor9_9`
* Formula (9.3.30) (an example's claim, cited as a result "(30)" at P2 l. 1035; U+) — `eq9_3_30`
* Formula (9.3.31) with "In particular `cap D̄ = cap 𝕋 = 1`" (an example's claim, cited "(9.3.31)" and `cap 𝕋 = 1` at
  P2 l. 1531; U+) — `eq9_3_31`
* Corollary 9.10, (9.3.32) (Pól28, AhBeu50; index "projection 207") — `cor9_10_a`
* Corollary 9.10, (9.3.33) (cited "(9.3.33)" at P2 l. 1225; Exercise 9.3.2) — exists:
  `GarnettMarshall2005.example3_1_2` (GM Example III.1.2: for compact E on the unit circle, the capacity is at least
  sin(|E|/4); GM's arc-length measure arcMeasure, the image of Lebesgue measure on (0, 2π], agrees on Borel sets with
  the arc length circleMeasure of Ch. 4, the image of Lebesgue measure on [0, 2π))
* Proposition 9.11 ((9.3.34); cited "(34)" at P2 l. 1103 and at P2 l. 1187) — `prop9_11_a`, `prop9_11_b`
* Definition (the (inner) capacity of an arbitrary set, (9.3.36), P2 l. 1067–1071; cited at P2 l. 1103, 1225, 1274;
  index "inner capacity 208") — exists: `GarnettMarshall2005.capacity` (GM III (4.8): the supremum of the compact
  capacity over the compact subsets, values in [0, ∞], literally (9.3.36))
* Theorem 9.12 (Choquet's capacitability theorem, Cho55, quoted; cited at P2 l. 1091, 1312 and in Exercise 9.3.3) —
  `thm9_12`
* Corollary 9.13 ((9.3.38) and "the union of countably many sets of capacity zero has again capacity zero"; cited at
  P2 l. 1203 and in Exercise 10.2.3; index "subadditivity 208") — `cor9_13_a`, `cor9_13_b`
* Definition ("nearly all `ζ ∈ E`", "nearly everywhere", P2 l. 1105 (first mentioned at P2 l. 415); used in
  Proposition 9.15, Theorem 9.19, P2 l. 1397 and Exercise 9.3.7) — `NearlyEverywhereOn`
* Theorem 9.14 (Frostman, Fro35; (9.3.40); cited at P2 l. 1187 and in Exercise 9.3.7) — `thm9_14`

Helper: `IsPosHarmonicLogGrowth` (the positive harmonic functions `u` in `G` with `u(z) = log |z| + O(1)` at `∞`, the
class of (9.3.19)).

Not items (DESIGN §3): "this system of points is not always uniquely determined" and "the maximum principle shows that
`z_{nk} ∈ ∂G`" (P2 l. 763, not cited); (9.3.3) (the Vandermonde form of `Δ_n`, used only in the proof of Proposition
9.6; Mathlib's `Matrix.det_vandermonde`); the first expression of (9.3.5), `min_k |q_n'(z_{nk})|` (equal to the second
by the product rule); (9.3.8) `cap E = cap ∂G` and the monotonicity (9.3.9) (the OCR prints a lone "(9)" and tags the
monotonicity "(10)"; U−: "follow at once" from (9.3.1), not cited by number; they are GM's
`GarnettMarshall2005.eq3_1_4` and `GarnettMarshall2005.eq3_1_5`); (9.3.14)–(9.3.16) and Hadamard's determinant
inequality (9.3.15) (the proof of Proposition 9.6); (9.3.21)–(9.3.26), the Lagrange interpolation formula and the weak
compactness of the probability measures (HayKe76, quoted inside the proof of Theorem 9.7); the recall of `𝔻*` (P2
l. 979); the maps `ζ + ζ⁻¹` and `ζ(aζ + 1)/(ζ + a)` of the examples (steps of the arguments for (9.3.30), (9.3.31));
"These examples are extremal in the following result" (a remark); the proof of (9.3.32) and "See AhBeu50 or Pom75"
for (9.3.33); "Note that `cap A ≤ cap E ≤ Δ₂^{1/2} ≤ diam E < b`" (P2 l. 1051; U−, immediate from (9.3.1), (9.3.6));
(9.3.35) and the proof of Proposition 9.11; "`E₁ ⊆ E₂` implies `cap E₁ ≤ cap E₂`" (P2 l. 1073; U−, "It is clear");
"capacitable" (P2 l. 1081, the word naming the property of Theorem 9.12); (9.3.39) and the proof of Corollary 9.13;
"a set of capacity zero has linear measure zero and even `α`-dimensional Hausdorff measure zero" (P2 l. 1105; U−, a
forward reference to (10.1.3), not cited; false as literally stated for non-Borel sets under the inner capacity: a
Bernstein set of `𝕋`); (9.3.41), (9.3.42) and the proof of Theorem 9.14; the remark on further results on Green's
function (P2 l. 1143); Exercises 9.3.1–9.3.7.

**Conventions.** As in §9.1. Part 1 (P2 l. 751): `E ⊆ ℂ` is compact and `G` is its outer domain
(`GarnettMarshall2005.unboundedComponentExt E`). Part 2 (P2 l. 875) introduces the equilibrium measure and the Green's
function, part 3 (P2 l. 1067) arbitrary sets. The capacity of a compact set is `GarnettMarshall2005.capacityCompact`,
that of an arbitrary set the inner capacity `GarnettMarshall2005.capacity`, both in `[0, ∞]` (leader ruling QD1). The
Fekete quantities `Δ_n`, `γ_n` and `|q_n|` are `[0, ∞]`-valued (`‖·‖ₑ`), so that their `n`th roots are `ENNReal`
powers and "`max_E`" is a supremum `⨆ z ∈ E` (attained for compact nonempty `E`). A domain `G ∋ ∞` is
`G : Set ExtPlane` with `References.IsDomainExt G` and `extInf ∈ G`; `E = ∂G` is the compact plane set
`References.finitePart (frontier G)`; "harmonic in `G ∖ {∞}`" is `InnerProductSpace.HarmonicOnNhd` on the plane
open set `finitePart G`; "`z → ∂G`" is `z → ζ` within `finitePart G` for each `ζ ∈ ∂G`. The potential
`∫_E log |z − ζ| dμ(ζ)` is `−GarnettMarshall2005.logPotential μ z` (`EReal`, `−∞` where the integral diverges), and
the Green's function (9.3.17) is `greenFnInf E μ` (`EReal`). Pommerenke speaks of "an" equilibrium measure; the
statements about "the" Green's function hold for every equilibrium measure (Theorem 9.7: the values in `G` do not
depend on the choice). `log(b/cap)` and `1/log(b/cap)` are written without the junk values of `Real.log 0` or `x/0`:
positivity hypotheses where the book needs them, and the book's convention `1/log(b/0) = 0` through
`ENNReal.log` (`log ∞ = ∞`) and the inverse of `[0, ∞]` in Corollary 9.13.
-/

open Complex Set Metric Filter Topology MeasureTheory Asymptotics
open scoped ENNReal NNReal Real ComplexConjugate Polynomial

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc)
open References (IsDomainExt finitePart)
open GarnettMarshall2005 (capacityCompact capacity unboundedComponentExt probMeasuresOn logPotential)

/-! ## 1. Compact sets -/

/-- **Definition (9.3.1)** (§9.3; P2 l. 751–755; used in (9.3.3), (9.3.6), (9.3.7) and at P2 l. 1051). For a compact
set `E ⊆ ℂ` and `n = 2, 3, …`, `Δ_n = Δ_n(E) = max_{z_1, …, z_n ∈ E} ∏_{k ≠ j} |z_k − z_j|`.
Modelling: the set-level quantity `Δ_n(E)`: the supremum, over all point systems `z : Fin n → ℂ` with values in `E`,
of the product over the ordered pairs `(k, j)` with `k ≠ j` (`n(n − 1)` factors; the crop of (9.3.1) prints the double
product with `k ≠ j`). Values in `[0, ∞]` (`‖·‖ₑ`). For compact nonempty `E` the supremum is attained
(`exists_isFeketeSystem`), so it is the book's maximum. Values outside the book's range `n ≥ 2`, `E` compact nonempty,
which no statement uses: `Δ_0(E) = 1` for every `E` (the empty system, an empty product) and `Δ_1(E) = 1` for
nonempty `E` (empty inner products); `Δ_n(∅) = 0` for `n ≥ 1` (there is no system: the supremum of the empty family);
for unbounded `E` and `n ≥ 2` the value is `∞` (a genuine supremum); for bounded non-compact `E` it is a supremum that
need not be attained. -/
def feketeDelta (E : Set ℂ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ (z : Fin n → ℂ) (_ : ∀ k, z k ∈ E), ∏ k, ∏ j ∈ Finset.univ.erase k, ‖z k - z j‖ₑ

/-- **Definition (9.3.2)** (§9.3; the Fekete points; P2 l. 757–763; index "Fekete points 203"; used in the proofs of
Theorem 9.7, Proposition 9.16 and Theorem 10.3). The maximum (9.3.1) is assumed for the Fekete points
`z_k = z_{nk} ∈ E` (`k = 1, …, n`).
Modelling: a point system `z : Fin n → ℂ` in `E` whose product over the ordered pairs `k ≠ j` equals `Δ_n(E)`. Fekete
points are not always uniquely determined (P2 l. 763), so every statement about "the" Fekete points, "the" Fekete
polynomial and `γ_n` holds for every Fekete system (Q9.5). -/
def IsFeketeSystem (E : Set ℂ) {n : ℕ} (z : Fin n → ℂ) : Prop :=
  (∀ k, z k ∈ E) ∧ ∏ k, ∏ j ∈ Finset.univ.erase k, ‖z k - z j‖ₑ = feketeDelta E n

/-- **Unlabelled claim** (§9.3, P2 l. 757: "The maximum is assumed for the Fekete points"; every statement on Fekete
points presupposes it). If `E ⊆ ℂ` is compact (and nonempty), then for `n = 2, 3, …` there is a Fekete system of `n`
points of `E`. -/
theorem exists_isFeketeSystem {E : Set ℂ} (hE : IsCompact E) (hne : E.Nonempty) {n : ℕ} (hn : 2 ≤ n) :
    ∃ z : Fin n → ℂ, IsFeketeSystem E z := by
  have _hn := hn  -- the existence of a maximizer does not need `n ≥ 2`
  set P : (Fin n → ℂ) → ℝ := fun z => ∏ k, ∏ j ∈ Finset.univ.erase k, ‖z k - z j‖ with hPdef
  have hPc : Continuous P := by
    simp only [hPdef]
    fun_prop
  have hPe : ∀ z : Fin n → ℂ, ∏ k, ∏ j ∈ Finset.univ.erase k, ‖z k - z j‖ₑ = ENNReal.ofReal (P z) := fun z => by
    simp only [hPdef]
    rw [ENNReal.ofReal_prod_of_nonneg fun k _ => Finset.prod_nonneg fun j _ => norm_nonneg _]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_prod_of_nonneg fun j _ => norm_nonneg _]
    exact Finset.prod_congr rfl fun j _ => (ofReal_norm _).symm
  have hK : IsCompact (Set.pi univ fun _ : Fin n => E) := isCompact_univ_pi fun _ => hE
  obtain ⟨e, he⟩ := hne
  have hKne : (Set.pi univ fun _ : Fin n => E).Nonempty := ⟨fun _ => e, fun _ _ => he⟩
  obtain ⟨z, hzK, hmax⟩ := hK.exists_isMaxOn hKne hPc.continuousOn
  have hzE : ∀ k, z k ∈ E := fun k => hzK k (mem_univ k)
  refine ⟨z, hzE, le_antisymm (le_iSup₂_of_le z hzE le_rfl) (iSup₂_le fun z' hz' => ?_)⟩
  rw [hPe, hPe]
  exact ENNReal.ofReal_le_ofReal (hmax fun k _ => hz' k)

/-- **Definition (9.3.4)** (§9.3; the `n`th Fekete polynomial; P2 l. 769–775; cited "(9.3.4)" at P2 l. 1203, used in
(9.3.13), (9.3.21) and at P2 l. 1841). `q_n(z) = ∏_{k=1}^{n} (z − z_{nk})`.
Modelling: the polynomial of a given point system `z` (a Fekete system in every use); its value at `w` is
`(feketePoly z).eval w`. -/
def feketePoly {n : ℕ} (z : Fin n → ℂ) : ℂ[X] :=
  ∏ k, (Polynomial.X - Polynomial.C (z k))

/-- **Definition (9.3.5)** (§9.3; P2 l. 775–779; used in (9.3.6), (9.3.13), (9.3.21) and at P2 l. 975).
`γ_n = γ_n(E) = min_k |q_n'(z_{nk})| = min_k ∏_{j ≠ k} |z_{nk} − z_{nj}|`.
Modelling: the second expression, for a given point system `z` (a Fekete system in every use; the book's notation
`γ_n(E)` notwithstanding, `γ_n` may depend on the choice of the Fekete points, Q9.5); the first expression equals it
by the product rule. Values in `[0, ∞]`; for `n = 0` the minimum over no index is `∞` (junk, never used: every
statement has `n ≥ 2`). -/
def feketeGamma {n : ℕ} (z : Fin n → ℂ) : ℝ≥0∞ :=
  ⨅ k, ∏ j ∈ Finset.univ.erase k, ‖z k - z j‖ₑ

/-- Helper for §9.3 (Fekete points): a product over `Fin (m + 1)` with one index `x` removed is the product over
`Fin m` read through `x.succAbove`. -/
theorem p93_erase {m : ℕ} (x : Fin (m + 1)) (g : Fin (m + 1) → ℝ≥0∞) :
    ∏ j ∈ Finset.univ.erase x, g j = ∏ i : Fin m, g (x.succAbove i) := by
  rw [Fin.univ_succAbove m x, Finset.erase_cons, Finset.prod_map]
  rfl

/-- Helper for (9.3.6) and the monotonicity of `Δ_n^{1/(n(n−1))}` (§9.3). Deleting the point `z_k` from a system of
`m + 1` points: `∏_{i ≠ j} |z_i − z_j| = (∏_{j ≠ k} |z_k − z_j|)² · ∏_{i ≠ j; i, j ≠ k} |z_i − z_j|`. -/
theorem p93_split {m : ℕ} (z : Fin (m + 1) → ℂ) (k : Fin (m + 1)) :
    ∏ i, ∏ j ∈ Finset.univ.erase i, ‖z i - z j‖ₑ =
      (∏ j ∈ Finset.univ.erase k, ‖z k - z j‖ₑ) ^ 2 *
        ∏ i : Fin m, ∏ j ∈ Finset.univ.erase i, ‖z (k.succAbove i) - z (k.succAbove j)‖ₑ := by
  have hG : ∀ i : Fin m, ∏ j ∈ Finset.univ.erase (k.succAbove i), ‖z (k.succAbove i) - z j‖ₑ =
      ‖z (k.succAbove i) - z k‖ₑ * ∏ j ∈ Finset.univ.erase i, ‖z (k.succAbove i) - z (k.succAbove j)‖ₑ := by
    intro i
    rw [← Finset.mul_prod_erase (Finset.univ.erase (k.succAbove i)) _
      (Finset.mem_erase.2 ⟨Fin.ne_succAbove k i, Finset.mem_univ k⟩)]
    congr 1
    have hset : (Finset.univ.erase (k.succAbove i)).erase k = (Finset.univ.erase i).map k.succAboveEmb := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_map, Fin.coe_succAboveEmb]
      constructor
      · rintro ⟨hxk, hxi⟩
        obtain ⟨y, rfl⟩ := Fin.exists_succAbove_eq hxk
        exact ⟨y, fun e => hxi (by rw [e]), rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨Fin.succAbove_ne k y, fun e => hy (Fin.succAbove_right_injective e)⟩
    rw [hset, Finset.prod_map]
    rfl
  rw [Fin.prod_univ_succAbove _ k]
  simp only [hG, Finset.prod_mul_distrib]
  have hsym : ∏ i : Fin m, ‖z (k.succAbove i) - z k‖ₑ = ∏ j ∈ Finset.univ.erase k, ‖z k - z j‖ₑ := by
    rw [p93_erase k (fun j => ‖z k - z j‖ₑ)]
    exact Finset.prod_congr rfl fun i _ => enorm_sub_rev _ _
  rw [hsym]
  ring

/-- **Formula (9.3.6)** (§9.3; P2 l. 781–791; cited "(6)" at P2 l. 867 in the proof of Proposition 9.6). For a
Fekete system of `n` points of the compact set `E`: `(Δ_n/Δ_{n−1})^{n/2} ≤ γ_n^n ≤ Δ_n`.
Modelling: `n ≥ 3`, so that `Δ_{n−1}` is one of the book's quantities (`n − 1 ≥ 2`); the first inequality is
multiplied out, `Δ_n^{n/2} ≤ γ_n^n Δ_{n−1}^{n/2}` (the book derives it from `Δ_n ≤ γ_n² Δ_{n−1}`, P2 l. 784), so that
no quotient `0/0` occurs when `Δ_{n−1} = 0` (then also `Δ_n = 0`). -/
theorem eq9_3_6 {E : Set ℂ} (hE : IsCompact E) {n : ℕ} (hn : 3 ≤ n) {z : Fin n → ℂ} (hz : IsFeketeSystem E z) :
    feketeDelta E n ^ ((n : ℝ) / 2) ≤ feketeGamma z ^ n * feketeDelta E (n - 1) ^ ((n : ℝ) / 2) ∧
      feketeGamma z ^ n ≤ feketeDelta E n := by
  have _hE := hE  -- compactness is not needed: `z` is a Fekete system
  obtain ⟨hzE, hzΔ⟩ := hz
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- the point `z_k` realizing `γ`
  obtain ⟨k, hk⟩ := Finite.exists_min fun k : Fin (m + 1) => ∏ j ∈ Finset.univ.erase k, ‖z k - z j‖ₑ
  have hγ : feketeGamma z = ∏ j ∈ Finset.univ.erase k, ‖z k - z j‖ₑ :=
    le_antisymm (iInf_le _ k) (le_iInf hk)
  refine ⟨?_, ?_⟩
  · -- `Δ_n ≤ γ² Δ_{n−1}`
    have hle : feketeDelta E (m + 1) ≤ feketeGamma z ^ 2 * feketeDelta E m := by
      rw [← hzΔ, p93_split z k, ← hγ]
      gcongr
      exact le_iSup₂_of_le (fun i => z (k.succAbove i)) (fun i => hzE _) le_rfl
    rw [show m + 1 - 1 = m by omega]
    have h2 : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) / 2 := by positivity
    calc feketeDelta E (m + 1) ^ (((m + 1 : ℕ) : ℝ) / 2)
        ≤ (feketeGamma z ^ 2 * feketeDelta E m) ^ (((m + 1 : ℕ) : ℝ) / 2) := ENNReal.rpow_le_rpow hle h2
      _ = feketeGamma z ^ (m + 1) * feketeDelta E m ^ (((m + 1 : ℕ) : ℝ) / 2) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h2, ← ENNReal.rpow_natCast (feketeGamma z) 2, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_natCast (feketeGamma z) (m + 1)]
        congr 2
        push_cast
        ring
  · -- `γ^n ≤ ∏_k ∏_{j ≠ k} |z_k − z_j| = Δ_n`
    rw [← hzΔ]
    calc feketeGamma z ^ (m + 1) = ∏ _k : Fin (m + 1), feketeGamma z := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ k : Fin (m + 1), ∏ j ∈ Finset.univ.erase k, ‖z k - z j‖ₑ :=
          Finset.prod_le_prod fun k _ => iInf_le _ k

/-- **Unlabelled claim** (§9.3, P2 l. 793: "We conclude that `Δ_n^{1/[n(n−1)]}` is decreasing"; the definition (9.3.7)
rests on it). For compact `E`, the sequence `Δ_n(E)^{1/(n(n−1))}`, `n = 2, 3, …`, is decreasing.
Modelling: "decreasing" is non-increasing (`AntitoneOn` on `n ≥ 2`). -/
theorem feketeDelta_rpow_antitone {E : Set ℂ} (hE : IsCompact E) :
    AntitoneOn (fun n : ℕ => feketeDelta E n ^ (1 / ((n : ℝ) * ((n : ℝ) - 1)))) (Ici 2) := by
  have _hE := hE  -- the monotonicity holds for every set `E`
  refine antitoneOn_nat_Ici_of_succ_le fun n hn => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  -- `Δ_{m+2}^m ≤ Δ_{m+1}^{m+2}`: average over the deleted point
  have key : ∀ z : Fin (m + 1 + 1) → ℂ, (∀ k, z k ∈ E) →
      (∏ i, ∏ j ∈ Finset.univ.erase i, ‖z i - z j‖ₑ) ^ m ≤ feketeDelta E (m + 1) ^ (m + 2) := by
    intro z hzE
    set P := ∏ i, ∏ j ∈ Finset.univ.erase i, ‖z i - z j‖ₑ with hPdef
    set Q : Fin (m + 1 + 1) → ℝ≥0∞ := fun k =>
      ∏ i : Fin (m + 1), ∏ j ∈ Finset.univ.erase i, ‖z (k.succAbove i) - z (k.succAbove j)‖ₑ with hQdef
    have hQ : ∀ k, Q k ≤ feketeDelta E (m + 1) := fun k =>
      le_iSup₂_of_le (fun i => z (k.succAbove i)) (fun i => hzE _) le_rfl
    have hprod : P ^ (m + 2) = P ^ 2 * ∏ k, Q k := by
      have h1 : P ^ (m + 2) = ∏ _k : Fin (m + 1 + 1), P := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have h2 : ∏ _k : Fin (m + 1 + 1), P =
          ∏ k : Fin (m + 1 + 1), (∏ j ∈ Finset.univ.erase k, ‖z k - z j‖ₑ) ^ 2 * Q k :=
        Finset.prod_congr rfl fun k _ => p93_split z k
      rw [h1, h2, Finset.prod_mul_distrib, Finset.prod_pow]
    have hPtop : P ≠ ⊤ := ENNReal.prod_ne_top fun i _ => ENNReal.prod_ne_top fun j _ => enorm_ne_top
    have hQle : ∏ k, Q k ≤ feketeDelta E (m + 1) ^ (m + 2) := by
      calc ∏ k, Q k ≤ ∏ _k : Fin (m + 1 + 1), feketeDelta E (m + 1) := Finset.prod_le_prod fun k _ => hQ k
        _ = feketeDelta E (m + 1) ^ (m + 2) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rcases eq_or_ne P 0 with h0 | h0
    · rw [h0, zero_pow (by omega)]
      exact bot_le
    · have hP2 : P ^ 2 ≠ 0 := pow_ne_zero 2 h0
      have hP2t : P ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hPtop
      have : P ^ m = ∏ k, Q k := by
        rw [← ENNReal.mul_right_inj hP2 hP2t, ← hprod]
        ring
      rw [this]
      exact hQle
  -- hence `Δ_{m+2} ≤ (Δ_{m+1}^{m+2})^{1/m}`
  have hΔ : feketeDelta E (m + 1 + 1) ≤ (feketeDelta E (m + 1) ^ (m + 2)) ^ ((m : ℝ)⁻¹) := by
    refine iSup₂_le fun z hz => ?_
    calc (∏ i, ∏ j ∈ Finset.univ.erase i, ‖z i - z j‖ₑ)
        = ((∏ i, ∏ j ∈ Finset.univ.erase i, ‖z i - z j‖ₑ) ^ m) ^ ((m : ℝ)⁻¹) :=
          (ENNReal.pow_rpow_inv_natCast (by omega) _).symm
      _ ≤ (feketeDelta E (m + 1) ^ (m + 2)) ^ ((m : ℝ)⁻¹) := ENNReal.rpow_le_rpow (key z hz) (by positivity)
  -- raise to the power `1/((m + 2)(m + 1))`
  have he : (0 : ℝ) ≤ 1 / (((m + 1 + 1 : ℕ) : ℝ) * (((m + 1 + 1 : ℕ) : ℝ) - 1)) := by
    refine one_div_nonneg.2 ?_
    push_cast
    nlinarith [hm0]
  calc feketeDelta E (m + 1 + 1) ^ (1 / (((m + 1 + 1 : ℕ) : ℝ) * (((m + 1 + 1 : ℕ) : ℝ) - 1)))
      ≤ ((feketeDelta E (m + 1) ^ (m + 2)) ^ ((m : ℝ)⁻¹)) ^
          (1 / (((m + 1 + 1 : ℕ) : ℝ) * (((m + 1 + 1 : ℕ) : ℝ) - 1))) := ENNReal.rpow_le_rpow hΔ he
    _ = feketeDelta E (m + 1) ^ (1 / (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) - 1))) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      congr 1
      have hmne : (m : ℝ) ≠ 0 := hm0.ne'
      push_cast
      have h1 : (m : ℝ) + 1 + 1 - 1 = m + 1 := by ring
      have h2 : (m : ℝ) + 1 - 1 = m := by ring
      rw [h1, h2]
      field_simp
      ring

/-- **Formula (9.3.7)** (§9.3; P2 l. 793–799; the book's definition of the (logarithmic) capacity, the "transfinite
diameter"; U+ by the leader ruling QD1). For compact `E ⊆ ℂ`, `cap E = lim_{n → ∞} Δ_n(E)^{1/(n(n−1))}`.
Modelling: (9.3.7) is Pommerenke's definition of capacity; with GM's Robin capacity (one notion) it is the
Fekete–Szegő equality, stated here: the limit of `Δ_n(E)^{1/(n(n−1))}` in `[0, ∞]` is
`GarnettMarshall2005.capacityCompact E`. The only hypothesis is compactness: for `E = ∅` both sides are `0`
(`Δ_n(∅) = 0` for `n ≥ 1`, and GM's compact capacity of `∅` is the supremum of an empty set of limits, since the
extended plane has no exhaustion by domains with nonempty boundary), and the leader asked for minimal hypotheses
(GM App. E, Theorem E.1, is to point here). -/
theorem eq9_3_7 {E : Set ℂ} (hE : IsCompact E) :
    Tendsto (fun n : ℕ => feketeDelta E n ^ (1 / ((n : ℝ) * ((n : ℝ) - 1)))) atTop (𝓝 (capacityCompact E)) := by
  sorry

/-- **Formula (9.3.10)** (§9.3; P2 l. 815–817, printed with the tag "(11)" [OCR]; cited "(10)" at P2 l. 995, 1053
and "(9.3.10)" at P2 l. 1477). `cap φ(E) = |a| cap E` if `φ(z) = az + b`.
Modelling: `E` compact (for `E = ∅` both sides are `0`); `a, b ∈ ℂ` arbitrary (for `a = 0`, `φ(E)` is a point, of
capacity `0`); capacities of compact sets in `[0, ∞]`. The crops carry no tags; the tag reading comes from the
citations "(10)" at P2 l. 995, 1053 and "(11)" at P2 l. 1035. -/
theorem eq9_3_10 {E : Set ℂ} (hE : IsCompact E) (a b : ℂ) :
    capacityCompact ((fun z => a * z + b) '' E) = ENNReal.ofReal ‖a‖ * capacityCompact E := by
  sorry

/-- **Proposition 9.6** (§9.3; (9.3.12); P2 l. 823–829; cited at P2 l. 909, 1117, 1204 and at P2 l. 1841), first part.
If `E ⊆ ℂ` is compact then (9.3.12) `cap E ≤ max_{z ∈ E} |p(z)|^{1/N}` for every polynomial `p(z) = z^N + …`.
Modelling: `p` monic of degree `N ≥ 1` (for `N = 0`, `p = 1`, the book's exponent `1/N` has no value);
the maximum is the supremum over `E` in `[0, ∞]`, attained for compact nonempty `E` (for `E = ∅` both sides are `0`). -/
theorem prop9_6_a {E : Set ℂ} (hE : IsCompact E) {p : ℂ[X]} (hp : p.Monic)
    (hN : 1 ≤ p.natDegree) :
    capacityCompact E ≤ (⨆ z ∈ E, ‖p.eval z‖ₑ) ^ (1 / (p.natDegree : ℝ)) := by
  sorry

/-- **Proposition 9.6** (§9.3; (9.3.13); P2 l. 831–833; cited "(13)" at P2 l. 947, 975), second part, first
equality. If `E ⊆ ℂ` is compact then `cap E = lim_{n → ∞} γ_n^{1/n}`.
Modelling: for every choice of Fekete systems `z_n` of `n` points, `n ≥ 2` (Q9.5); the limit is taken in `[0, ∞]`. -/
theorem prop9_6_b {E : Set ℂ} (hE : IsCompact E) {zs : (n : ℕ) → Fin n → ℂ}
    (hzs : ∀ n : ℕ, 2 ≤ n → IsFeketeSystem E (zs n)) :
    Tendsto (fun n : ℕ => feketeGamma (zs n) ^ (1 / (n : ℝ))) atTop (𝓝 (capacityCompact E)) := by
  sorry

/-- **Proposition 9.6** (§9.3; (9.3.13); P2 l. 831–833; cited "(13)" at P2 l. 947 and at P2 l. 1841), second part,
second equality. If `E ⊆ ℂ` is compact [CORRECTION: and infinite] then `cap E = lim_{n → ∞} max_{z ∈ E} |q_n(z)|^{1/n}`.
[CORRECTION] (leader ruling) As printed the equality fails for finite `E`: for `E = {0, 1}` and `n ≥ 3` every system
of `n` points of `E` repeats a point, so `Δ_n = 0` and every system is a Fekete system, among them `z_{nk} = 0` for all
`k`, with `q_n(z) = zⁿ`; then `max_E |q_n|^{1/n} = 1` while `cap E = 0`. The proof divides by `Δ_n` ((9.3.16)), which
is positive exactly when `E` has at least `n` points; so `E` is assumed infinite.
Modelling: for every choice of Fekete systems `z_n`, `n ≥ 2`; the maximum over `E` is the supremum in `[0, ∞]`. -/
theorem prop9_6_c {E : Set ℂ} (hE : IsCompact E) (hinf : E.Infinite) {zs : (n : ℕ) → Fin n → ℂ}
    (hzs : ∀ n : ℕ, 2 ≤ n → IsFeketeSystem E (zs n)) :
    Tendsto (fun n : ℕ => (⨆ w ∈ E, ‖(feketePoly (zs n)).eval w‖ₑ) ^ (1 / (n : ℝ))) atTop
      (𝓝 (capacityCompact E)) := by
  sorry

/-! ## 2. The Green's function -/

/-- The positive harmonic functions `u` in the domain `G ∋ ∞` with `u(z) = log |z| + O(1)` as `z → ∞` (helper, the
class of (9.3.19), P2 l. 889; used in `IsEquilibriumMeasure` and Theorem 9.7).
Modelling: `u` is real-valued and harmonic on the plane open set `finitePart G` (the book's "harmonic in `G`" for a
function with a logarithmic pole at `∞`), positive there, and `u(z) − log |z|` is bounded for large `|z|`. -/
def IsPosHarmonicLogGrowth (G : Set ExtPlane) (u : ℂ → ℝ) : Prop :=
  InnerProductSpace.HarmonicOnNhd u (finitePart G) ∧ (∀ z ∈ finitePart G, 0 < u z) ∧
    (fun z => u z - Real.log ‖z‖) =O[cocompact ℂ] (fun _ => (1 : ℝ))

/-- **Definition** (the (extended) Green's function with pole at `∞`, (9.3.17), §9.3, P2 l. 897; index "Green's
function 205–207, 209, 210"). For a probability measure `μ` on the compact set `E`,
`g(z) = ∫_E log |z − ζ| dμ(ζ) − log cap E`, `z ∈ ℂ`.
Modelling: values in `EReal`; the integral is `−GarnettMarshall2005.logPotential μ z` (GM's potential
`U_μ(z) = ∫ log (1/|ζ − z|) dμ(ζ)`, genuinely `EReal`-valued: `∫ log |z − ζ| dμ` is `−∞` where it diverges, e.g. at an
atom of `μ`), and `log cap E` is `ENNReal.log` of the compact capacity. It is used only for equilibrium measures, for
which `0 < cap E < ∞`, so that `log cap E` is a real number; GM's `GarnettMarshall2005.greenFunctionLim` (a limit
along exhaustions, defined only on the outer domain) is the related notion (Q9.4). -/
def greenFnInf (E : Set ℂ) (μ : Measure ℂ) (z : ℂ) : EReal :=
  -logPotential μ z - ENNReal.log (capacityCompact E)

/-- **Definition** (equilibrium measure, §9.3, P2 l. 897: "We call `μ` an equilibrium measure of `E`"; index
"equilibrium measure 205, 208, 210, 215"; used in Propositions 9.11, 9.15, Corollary 9.13 and Theorem 9.14). Let
`E ⊆ ℂ` be compact with `cap E > 0` and `G` its outer domain. A probability measure `μ` on `E` is an equilibrium
measure of `E` if its Green's function `g` of (9.3.17) satisfies (9.3.18) `g(z) ≥ 0` for `z ∈ Ḡ`, `g(z) = 0` for
`z ∈ ℂ ∖ Ḡ`, and (9.3.19) `u(z) ≥ g(z) > 0` for `z ∈ G`, for every positive harmonic function `u` in `G` with
`u(z) = log |z| + O(1)` as `z → ∞`.
Modelling (Q9.4, leader ruling QD4): Pommerenke's own notion. The other properties of Theorem 9.7 (the expansion
(9.3.17), subharmonicity in `ℂ`, harmonicity in `G ∖ {∞}`) hold for every probability measure on a compact set and are
stated in `thm9_7`; `g > 0` in `G` is stated separately from the comparison with `u`. `Ḡ` is the closure in `ℂ̂`, read
at the finite points; `G` is `GarnettMarshall2005.unboundedComponentExt E` (for `E = ∂G` of Theorem 9.7 it is that
`G`). GM's `GarnettMarshall2005.equilibriumMeasure` (the weak-star limit of the harmonic measures of smooth
approximations, characterized by GM III Theorem 4.1 as the unique energy minimizer) is the related notion: GM states
no item giving it the properties (9.3.18), (9.3.19), so it is not used as a pointer; mathematically the two
agree (the equilibrium measure of a compact set of positive capacity is unique), which is not stated here.
Existence is Theorem 9.7,
uniqueness for `E ⊆ 𝕋` Proposition 9.15 (a). -/
def IsEquilibriumMeasure (E : Set ℂ) (μ : Measure ℂ) : Prop :=
  IsCompact E ∧ 0 < capacityCompact E ∧ μ ∈ probMeasuresOn E ∧
    (∀ z : ℂ, (z : ExtPlane) ∈ closure (unboundedComponentExt E) → 0 ≤ greenFnInf E μ z) ∧
    (∀ z : ℂ, (z : ExtPlane) ∉ closure (unboundedComponentExt E) → greenFnInf E μ z = 0) ∧
    (∀ z ∈ finitePart (unboundedComponentExt E), 0 < greenFnInf E μ z) ∧
    ∀ u : ℂ → ℝ, IsPosHarmonicLogGrowth (unboundedComponentExt E) u →
      ∀ z ∈ finitePart (unboundedComponentExt E), greenFnInf E μ z ≤ (u z : EReal)

/-- **Theorem 9.7** (§9.3; Myr33, Lej34; (9.3.17)–(9.3.19); P2 l. 877–895; cited at P2 l. 977, 1059, 1123, 1135, 1181,
1254, 1284). Let `G` be a domain with `∞ ∈ G` and let `E = ∂G` and `cap E > 0`. Then there is a probability measure
`μ` on `E` with the following properties: the function (9.3.17)
`g(z) = ∫_E log |z − ζ| dμ(ζ) − log cap E = log |z| − log cap E + O(1/|z|)` is subharmonic in `ℂ` and harmonic in
`G ∖ {∞}`. It satisfies (9.3.18) `g(z) ≥ 0` for `z ∈ Ḡ`, `g(z) = 0` for `z ∈ ℂ ∖ Ḡ`. If `u` is any positive harmonic
function in `G` with `u(z) = log |z| + O(1)` as `z → ∞` then (9.3.19) `u(z) ≥ g(z) > 0` for `z ∈ G`, and this
property uniquely determines `g` in `G`.
Modelling: `g = greenFnInf E μ`; the conclusion includes that `μ` is an equilibrium measure (the book's naming,
P2 l. 897). `g` is finite on `G ∖ {∞}` (so harmonicity is that of the real function there), and the expansion is
`g(z) − (log |z| − log cap E) = O(1/|z|)` as `z → ∞` (`g` is finite for large `|z|`; `cap E` is finite for compact
`E`). "Subharmonic in `ℂ`" is `References.IsSubharmonicOn g univ`. The last conjunct is the uniqueness: a function
`v` of the class of (9.3.19) that is `≤` every function of the class equals `g` in `G`. -/
theorem thm9_7 {G : Set ExtPlane} (hG : IsDomainExt G) (hinf : extInf ∈ G) {E : Set ℂ}
    (hE : E = finitePart (frontier G)) (hcap : 0 < capacityCompact E) :
    ∃ μ : Measure ℂ, μ ∈ probMeasuresOn E ∧ IsEquilibriumMeasure E μ ∧
      (fun z => (greenFnInf E μ z).toReal - (Real.log ‖z‖ - Real.log (capacityCompact E).toReal))
        =O[cocompact ℂ] (fun z => ‖z‖⁻¹) ∧
      References.IsSubharmonicOn (greenFnInf E μ) univ ∧
      (∀ z ∈ finitePart G, greenFnInf E μ z ≠ ⊥ ∧ greenFnInf E μ z ≠ ⊤) ∧
      InnerProductSpace.HarmonicOnNhd (fun z => (greenFnInf E μ z).toReal) (finitePart G) ∧
      (∀ z : ℂ, (z : ExtPlane) ∈ closure G → 0 ≤ greenFnInf E μ z) ∧
      (∀ z : ℂ, (z : ExtPlane) ∉ closure G → greenFnInf E μ z = 0) ∧
      (∀ u : ℂ → ℝ, IsPosHarmonicLogGrowth G u →
        ∀ z ∈ finitePart G, greenFnInf E μ z ≤ (u z : EReal) ∧ 0 < greenFnInf E μ z) ∧
      ∀ v : ℂ → ℝ, IsPosHarmonicLogGrowth G v →
        (∀ u : ℂ → ℝ, IsPosHarmonicLogGrowth G u → ∀ z ∈ finitePart G, v z ≤ u z) →
        ∀ z ∈ finitePart G, (v z : EReal) = greenFnInf E μ z := by
  sorry

/-- **Formula (9.3.20)** (§9.3; P2 l. 897–901; cited "by (20)" at P2 l. 953 in the proof of Theorem 9.7; index
"semicontinuous 205"). Since `g` is subharmonic and thus upper semicontinuous,
`g(ζ) = limsup_{z → ζ} g(z)` for `ζ ∈ ℂ`.
Modelling: `g = greenFnInf E μ` for an equilibrium measure `μ`; the `limsup` is taken in `EReal` over `z → ζ`,
`z ≠ ζ` (`𝓝[≠] ζ`): with `z = ζ` allowed the equality would be upper semicontinuity alone, whereas the book uses it
to pass from `g ≥ 0` off `E` to `g ≥ 0` on `E` (P2 l. 953), which needs the punctured `limsup`. -/
theorem eq9_3_20 {E : Set ℂ} {μ : Measure ℂ} (hμ : IsEquilibriumMeasure E μ) (ζ : ℂ) :
    greenFnInf E μ ζ = limsup (greenFnInf E μ) (𝓝[≠] ζ) := by
  sorry

/-- **Theorem 9.8** (§9.3; (9.3.27); P2 l. 961–967; cited at P2 l. 993, 1065), first part. Let `u` be positive and
harmonic in the domain `G` and let (9.3.27) `u(z) = log |z| + a + O(|z|⁻¹)` as `z → ∞`. Then
`cap E ≥ e^{−a} > 0` where `E = ∂G`.
Modelling: `G ∋ ∞` (the expansion at `∞` presupposes it), `u` harmonic and positive on `finitePart G`; `E = ∂G` is
compact. -/
theorem thm9_8_a {G : Set ExtPlane} (hG : IsDomainExt G) (hinf : extInf ∈ G) {E : Set ℂ}
    (hE : E = finitePart (frontier G)) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u (finitePart G))
    (hpos : ∀ z ∈ finitePart G, 0 < u z) {a : ℝ}
    (hexp : (fun z => u z - Real.log ‖z‖ - a) =O[cocompact ℂ] (fun z => ‖z‖⁻¹)) :
    ENNReal.ofReal (Real.exp (-a)) ≤ capacityCompact E ∧ 0 < capacityCompact E := by
  sorry

/-- **Theorem 9.8** (§9.3; P2 l. 967), second part. If furthermore `u(z) → 0` as `z → ∂G` then `u = g` and
`cap E = e^{−a}`.
Modelling: as in `thm9_8_a`; "`z → ∂G`" is `z → ζ` within `finitePart G` for every `ζ ∈ ∂G`; `u = g` in `G` for every
equilibrium measure of `E` (the Green's function `g` exists by the first part and Theorem 9.7). -/
theorem thm9_8_b {G : Set ExtPlane} (hG : IsDomainExt G) (hinf : extInf ∈ G) {E : Set ℂ}
    (hE : E = finitePart (frontier G)) {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u (finitePart G))
    (hpos : ∀ z ∈ finitePart G, 0 < u z) {a : ℝ}
    (hexp : (fun z => u z - Real.log ‖z‖ - a) =O[cocompact ℂ] (fun z => ‖z‖⁻¹))
    (hbd : ∀ ζ ∈ E, Tendsto u (𝓝[finitePart G] ζ) (𝓝 0)) :
    (∀ μ : Measure ℂ, IsEquilibriumMeasure E μ → ∀ z ∈ finitePart G, greenFnInf E μ z = (u z : EReal)) ∧
      capacityCompact E = ENNReal.ofReal (Real.exp (-a)) := by
  sorry

/-- **Corollary 9.9** (§9.3; (9.3.28), (9.3.29); P2 l. 981–993; cited at P2 l. 995, 1007, 1570). If (9.3.28)
`h(ζ) = cζ + c₀ + c₁ζ⁻¹ + …` maps `𝔻*` conformally onto `G`, then `cap ∂G = |c|` and (9.3.29)
`g(z) = log |h⁻¹(z)|` for `z ∈ G`, `g(z) = 0` for `z ∈ ℂ ∖ G`.
Modelling (Q9.12): `h = c g₁` with `g₁ ∈ Σ` (`IsClassSigma`: univalent in `|ζ| > 1` with `g₁(ζ) = ζ + b₀ + b₁ζ⁻¹ + …`)
and `c ≠ 0`, which is exactly the class (9.3.28); `G = h({|ζ| > 1}) ∪ {∞}`; `g(z) = log |h⁻¹(z)|` is written at
`z = h(ζ)`; `g` is the Green's function of any equilibrium measure of `E = ∂G`. -/
theorem cor9_9 {g₁ : ℂ → ℂ} (hg₁ : IsClassSigma g₁) {c : ℂ} (hc : c ≠ 0) {G : Set ExtPlane}
    (hG : G = toExt ((fun ζ => c * g₁ ζ) '' {ζ : ℂ | 1 < ‖ζ‖}) ∪ {extInf}) {E : Set ℂ}
    (hE : E = finitePart (frontier G)) :
    capacityCompact E = ENNReal.ofReal ‖c‖ ∧
      ∀ μ : Measure ℂ, IsEquilibriumMeasure E μ →
        (∀ ζ : ℂ, 1 < ‖ζ‖ → greenFnInf E μ (c * g₁ ζ) = (Real.log ‖ζ‖ : EReal)) ∧
          ∀ z : ℂ, (z : ExtPlane) ∉ G → greenFnInf E μ z = 0 := by
  sorry

/-- **Formula (9.3.30)** (§9.3; an example, P2 l. 995–999: "Hence it follows from (10) and Corollary 9.9"; U+, cited
"(30)" at P2 l. 1035). `cap [a, b] = |b − a|/4` for `a, b ∈ ℂ`.
Modelling: `[a, b]` is the segment `segment ℝ a b` of `ℂ` (a point for `a = b`, of capacity `0`). -/
theorem eq9_3_30 (a b : ℂ) : capacityCompact (segment ℝ a b) = ENNReal.ofReal (‖b - a‖ / 4) := by
  sorry

/-- **Formula (9.3.31)** (§9.3; an example, P2 l. 1001–1013; U+, cited "(9.3.31)" and "`cap 𝕋 = 1`" at P2 l. 1531).
`cap {e^{iϑ} : −α ≤ ϑ ≤ α} = sin(α/2)` (`0 < α ≤ π`). In particular `cap D̄ = cap 𝕋 = 1`.
Modelling: the arc is `arcT (−α) α` (Ch. 4); `D̄` is the closed unit disc. -/
theorem eq9_3_31 :
    (∀ α : ℝ, 0 < α → α ≤ π → capacityCompact (arcT (-α) α) = ENNReal.ofReal (Real.sin (α / 2))) ∧
      capacityCompact (closedBall (0 : ℂ) 1) = 1 ∧ capacityCompact (sphere (0 : ℂ) 1) = 1 := by
  sorry

/-- **Corollary 9.10** (§9.3; Pól28, AhBeu50; (9.3.32); P2 l. 1017–1021; index "projection 207"), first part. If `P`
is the orthogonal projection of the compact set `E` onto some line then (9.3.32) `Λ(P) ≤ 4 cap P ≤ 4 cap E`.
Modelling: the line is `{c + t e^{iθ} : t ∈ ℝ}` and the projection `z ↦ c + Re((z − c) e^{−iθ}) e^{iθ}`; `Λ(P)` is the
linear measure `μH[1]` of the plane set `P` (for `E = ∅` all three sides are `0`). -/
theorem cor9_10_a {E : Set ℂ} (hE : IsCompact E) (c : ℂ) (θ : ℝ) :
    μH[1] ((fun z => c + (((z - c) * exp (-(θ * I))).re : ℂ) * exp (θ * I)) '' E) ≤
        4 * capacityCompact ((fun z => c + (((z - c) * exp (-(θ * I))).re : ℂ) * exp (θ * I)) '' E) ∧
      4 * capacityCompact ((fun z => c + (((z - c) * exp (-(θ * I))).re : ℂ) * exp (θ * I)) '' E) ≤
        4 * capacityCompact E := by
  sorry

/-- **Proposition 9.11** (§9.3; (9.3.34); P2 l. 1043–1047; cited "(34)" at P2 l. 1103 and at P2 l. 1187), first part.
Let `E ⊆ ℂ` be compact and `cap E > 0`. If `diam E < b` and if `μ` is an equilibrium measure of `E` then (9.3.34)
`μ(A) ≤ log(b/cap E)/log(b/cap A)` for compact `A ⊆ E`.
Modelling: stated for `cap A > 0` (the case `cap A = 0` is `prop9_11_b`); the capacities of compact sets are finite
(`cap A ≤ cap E ≤ diam E < b`, P2 l. 1051), so their real values are used, and both logarithms are positive. -/
theorem prop9_11_a {E : Set ℂ} (hE : IsCompact E) (hcap : 0 < capacityCompact E) {b : ℝ} (hb : diam E < b)
    {μ : Measure ℂ} (hμ : IsEquilibriumMeasure E μ) {A : Set ℂ} (hA : IsCompact A) (hAE : A ⊆ E)
    (hcapA : 0 < capacityCompact A) :
    μ A ≤ ENNReal.ofReal (Real.log (b / (capacityCompact E).toReal) / Real.log (b / (capacityCompact A).toReal)) := by
  sorry

/-- **Proposition 9.11** (§9.3; P2 l. 1049), second part. In particular `μ(A) = 0` if `cap A = 0`.
Modelling: `E` compact with `cap E > 0`, `μ` an equilibrium measure of `E`, `A ⊆ E` compact (the bound `b` of the
first part plays no role). -/
theorem prop9_11_b {E : Set ℂ} (hE : IsCompact E) (hcap : 0 < capacityCompact E) {μ : Measure ℂ}
    (hμ : IsEquilibriumMeasure E μ) {A : Set ℂ} (hA : IsCompact A) (hAE : A ⊆ E) (hcapA : capacityCompact A = 0) :
    μ A = 0 := by
  sorry

/-! ## 3. Arbitrary sets -/

/-- **Theorem 9.12** (§9.3; Choquet's capacitability theorem, Cho55, quoted: "See e.g. HayKe76 for the proof"; (9.3.37);
P2 l. 1075–1081; cited at P2 l. 1091, 1312 and in Exercise 9.3.3; index "capacitable 208", "Souslin set 208"). If `E`
is a Borel or Souslin set [CORRECTION: with `cap E < ∞`] then, for every `ε > 0`, there is an open set `H` with
(9.3.37) `E ⊆ H`, `cap H < cap E + ε`.
[CORRECTION] (leader ruling) The capacity is the inner capacity (9.3.36), with values in `[0, ∞]`. For the Borel set
`E = ℝ`, `cap E = ∞` (it contains segments of every length, (9.3.30)), and the failure comes from the strict form
"`< cap E + ε`" at `cap E = ∞`: every `H ⊇ ℝ` has `cap H = ∞`, and `∞ < ∞ + ε` is false. So `cap E < ∞` is assumed;
every use in the book has bounded `E` (Corollary 9.13, Theorem 9.17).
Modelling: "Borel" is `MeasurableSet`, "Souslin" is `MeasureTheory.AnalyticSet` (Part C, (6.2.19)); capacities are
`GarnettMarshall2005.capacity`. -/
theorem thm9_12 {E : Set ℂ} (hE : MeasurableSet E ∨ AnalyticSet E) (hfin : capacity E < ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : Set ℂ, IsOpen H ∧ E ⊆ H ∧ capacity H < capacity E + ENNReal.ofReal ε := by
  sorry

/-- **Corollary 9.13** (§9.3; (9.3.38); P2 l. 1083–1087; cited at P2 l. 1203 and in Exercise 10.2.3; index
"subadditivity 208"), first part. Let `E_n` be Borel sets and `E = ⋃_{n=1}^∞ E_n`. If `diam E < b` then (9.3.38)
`1/log(b/cap E) ≤ Σ_n 1/log(b/cap E_n)`.
Modelling: `diam E < b` with the extended diameter (`Metric.ediam`, so that `E` is bounded); `1/log(b/c)` is written
`((ENNReal.log (b/c)).toENNReal)⁻¹` in `[0, ∞]`: for `0 < c < b` it is the real number `1/log(b/c) > 0`, and for
`c = 0` it is `0`, the book's convention `1/log(b/0) = 0` (`b/0 = ∞`, `log ∞ = ∞`, `1/∞ = 0`), used in the "In
particular" (every capacity here is `≤ cap E ≤ diam E < b`); the sum is taken in `[0, ∞]`. -/
theorem cor9_13_a {E : ℕ → Set ℂ} (hE : ∀ n, MeasurableSet (E n)) {b : ℝ}
    (hb : Metric.ediam (⋃ n, E n) < ENNReal.ofReal b) :
    ((ENNReal.log (ENNReal.ofReal b / capacity (⋃ n, E n))).toENNReal)⁻¹ ≤
      ∑' n, ((ENNReal.log (ENNReal.ofReal b / capacity (E n))).toENNReal)⁻¹ := by
  sorry

/-- **Corollary 9.13** (§9.3; P2 l. 1089), second part. In particular the union of countably many sets of capacity
zero has again capacity zero.
Modelling: for Borel sets `E_n` (the sets of the corollary), with no bound on the diameter (a union of countably many
sets of capacity zero is the union of its bounded pieces `E_n ∩ D(0, m)`, to which the first part applies). -/
theorem cor9_13_b {E : ℕ → Set ℂ} (hE : ∀ n, MeasurableSet (E n)) (h0 : ∀ n, capacity (E n) = 0) :
    capacity (⋃ n, E n) = 0 := by
  sorry

/-- **Definition** (§9.3, P2 l. 1105; first mentioned at P2 l. 415; index "nearly everywhere 195, 196, 209, 210, 215";
used in Proposition 9.15, Theorem 9.19, P2 l. 1397 and Exercise 9.3.7). A property holds for nearly all `ζ ∈ E` if it
holds for all `ζ ∈ E` except for a set of zero capacity.
Modelling: the set of the `ζ ∈ E` where it fails has (inner) capacity `0`; this is equivalent to the book's wording
since the inner capacity is monotone. -/
def NearlyEverywhereOn (E : Set ℂ) (P : ℂ → Prop) : Prop :=
  capacity {ζ ∈ E | ¬ P ζ} = 0

/-- **Theorem 9.14** (§9.3; Frostman, Fro35; (9.3.40); P2 l. 1107–1115; cited at P2 l. 1187 and in Exercise 9.3.7;
index "Fσ-set 209"). Let `G` be a domain with `∞ ∈ G` and `cap ∂G > 0`. Then (9.3.40) `g(z) → 0` as `z → ζ`,
`z ∈ G`, for `ζ ∈ ∂G ∖ X`, where `X` is an `F_σ`-set with `cap X = 0`.
Modelling: `g` is the Green's function of any equilibrium measure of `E = ∂G` (its values in `G` do not depend on the
choice, Theorem 9.7), and the set `X` does not depend on it; the limit is taken in `EReal`, within `finitePart G`;
`F_σ` is `IsFSigma` (Part C, §6.2); `cap X` is the inner capacity. -/
theorem thm9_14 {G : Set ExtPlane} (hG : IsDomainExt G) (hinf : extInf ∈ G) {E : Set ℂ}
    (hE : E = finitePart (frontier G)) (hcap : 0 < capacityCompact E) :
    ∃ X : Set ℂ, IsFSigma X ∧ capacity X = 0 ∧
      ∀ μ : Measure ℂ, IsEquilibriumMeasure E μ →
        ∀ ζ ∈ E \ X, Tendsto (greenFnInf E μ) (𝓝[finitePart G] ζ) (𝓝 0) := by
  sorry

end Pommerenke1992
