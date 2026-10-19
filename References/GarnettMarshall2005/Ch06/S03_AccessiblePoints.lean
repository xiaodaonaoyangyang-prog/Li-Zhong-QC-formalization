import References.GarnettMarshall2005.Ch06.S02_PrivalovPlessner

/-!
# Garnett–Marshall, Chapter VI §3: Accessible points

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Ch. VI §3 (pp. 205–207;
`full.md` of the second part, P2:883–938).

Conventions of the section, as modelled here. Standing assumption (P2:885): `Ω ⊆ ℂ` is a simply connected domain
(`Gehring1978.IsHypSimplyConnectedExt (toExt Ω)`, which excludes `Ω = ℂ`) and `φ : 𝔻 → Ω` is a conformal mapping
(`LiZhongQC.IsConformalOnto φ unitDisc Ω`); `∂Ω` need not be a Jordan curve. Where a statement needs only `φ`, the
hypothesis `IsConformalOnto φ unitDisc Ω` carries the setting (a conformal image of `𝔻` is simply connected). The
boundary function `φ(ζ)` is the finite nontangential limit of `φ` at `ζ ∈ ∂𝔻` where it exists (P2:891); it enters only
through the predicate `HasNontangentialLimit φ ζ w` (leader ruling C6), and `φ(S)`, `φ⁻¹(E)` are the helper sets
`bdryImage φ S`, `bdryPreimage φ E` (the set of the limits at points of `S`, the set of `ζ ∈ ∂𝔻` with a limit in
`E`). Boundary points are finite: `∂Ω` is the frontier in `ℂ` (for unbounded `Ω` the point `∞` of `ℂ*` carries no
harmonic measure, and the nontangential limits are finite). Harmonic measure of `Ω` is Wiener's harmonic measure
`harmonicMeasureWiener` of Ch. III §5 (the most general `ω` of the book at this point, leader rulings D1, B5, C6; the
proof of Theorem 3.2 uses "the definition of harmonic measure" through the exhaustion `φ(|z| < r_n)`), and harmonic
measure of `𝔻` is `harmonicMeasureDisc`; `|·|` on `∂𝔻` is `arcMeasure`.

* Unlabelled (§3, P2:885): a conformal map `φ : 𝔻 → Ω` has a nontangential limit at almost every `ζ ∈ ∂𝔻` —
  `ae_hasNontangentialLimit_of_conformal`
* Definition (accessible point of `∂Ω`; the set `A` of accessible points, §3, P2:897, 905–909) — `IsAccessiblePoint`,
  `accessiblePoints`
* Lemma 3.1 (§3) — `lemma6_3_1_a`, `lemma6_3_1_b` (B-cand. Pommerenke1992.prop2_14, preimages of curves ending at a
  boundary point, a different statement)
* Theorem 3.2 (§3; (3.2), (3.3)) — `thm6_3_2_a_borel`, `thm6_3_2_a`, `thm6_3_2_b`, `thm6_3_2_c`

Helpers (not book notions, the notation `φ(S)`, `φ⁻¹(E)` of P2:891–911 and §4–§6): `bdryImage`, `bdryPreimage`. Near
miss: Pommerenke1992.radialImage and Pommerenke1992.radialPreimage ((6.2.16), (6.2.20)) are the sets of radial limits
of a map with values in the extended plane; for a conformal map radial and nontangential limits agree (by
Lindelöf's theorem, a result and not a renaming), so the helpers use nontangential limits, as GM defines `φ(ζ)`.

Not stated (inventory U−): "(3.1) `∫₀¹ |φ′(rζ)| dr < ∞` except on a set of capacity zero (Corollary V.3.6); then `φ`
has a radial limit and, by Lindelöf's theorem, a nontangential limit, so `φ(ζ)` is defined off a set of capacity and
Hausdorff dimension zero" (P2:891–897, a remark, not cited); "`A` is the range of the boundary function and `A` is dense
in `∂Ω`" (P2:911; the range is Lemma 3.1, the density is not cited).
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt unitDisc IsConformalOnto)
open Gehring1978 (IsHypSimplyConnectedExt)

/-- The set `φ(S)` of boundary values (helper, Ch. VI §3, P2:891; used in §4–§6): the finite nontangential limits
`w = φ(ζ)` of `φ` at the points `ζ ∈ S` where they exist. -/
def bdryImage (φ : ℂ → ℂ) (S : Set ℂ) : Set ℂ :=
  {w | ∃ ζ ∈ S, HasNontangentialLimit φ ζ w}

/-- The set `φ⁻¹(E)` (helper, Ch. VI §3, (3.3); used in §4–§6): the points `ζ ∈ ∂𝔻` at which `φ` has a finite
nontangential limit `φ(ζ) ∈ E`. -/
def bdryPreimage (φ : ℂ → ℂ) (E : Set ℂ) : Set ℂ :=
  {ζ ∈ sphere (0 : ℂ) 1 | ∃ w ∈ E, HasNontangentialLimit φ ζ w}

/-- **Unlabelled** (Ch. VI §3, P2:885; used as a result in the proofs of Lemma 3.1, P2:903, "Because `φ` has
nontangential limits a.e.", of Theorem 4.1, P2:965, and of Lemma 5.3, P2:1187, and throughout the later chapters as
the boundary function `φ(ζ)`). Let `Ω` be a simply connected domain and `φ : 𝔻 → Ω` a conformal mapping; `∂Ω` need
not be a Jordan curve. Nevertheless `φ` has a nontangential limit `φ(ζ)` at almost every `ζ ∈ ∂𝔻`, because
`z/(φ(z) − φ(0))` is bounded and analytic on `𝔻`.
Modelling: the limit is finite (`w ∈ ℂ`; "when `φ` has a finite nontangential limit at `ζ` we define `φ(ζ)` to be
that nontangential limit", P2:891); `Ω ⊆ ℂ` is the image, simply connected and different from `ℂ`. Near miss:
Pommerenke1992.thm1_7 (radial limits of a conformal map of `𝔻` into `ℂ`). -/
theorem ae_hasNontangentialLimit_of_conformal {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ unitDisc Ω) :
    ∀ᵐ ζ ∂arcMeasure, ∃ w : ℂ, HasNontangentialLimit φ ζ w := by
  sorry

/-- **Definition** (accessible point, Ch. VI §3, P2:897; used in Lemma 3.1, Theorem 3.2, Lemma 5.3, P2:1170, the
proof of Theorem 6.1, P2:1386, the cone points of §4, P2:967, and Exercise VI.13, P2:1798). We say `w ∈ ∂Ω` is an
accessible point of `∂Ω` if `w` is the endpoint of an open arc `σ ⊆ Ω`.
Modelling: `Ω ⊆ ℂ` and `w ∈ ℂ` a finite point of the frontier in `ℂ`; the open arc is `σ = f((0, 1))` for a map
`f` continuous and one-to-one on `[0, 1]` (a closed Jordan arc with the endpoints removed) with `σ ⊆ Ω`, and `w`
is its endpoint `f(1)`. Only the end at `w` matters: an arc from a point of `Ω` to `w` contains such a subarc, and a
closed arc of this form is homeomorphic to `[0, 1]`. -/
def IsAccessiblePoint (Ω : Set ℂ) (w : ℂ) : Prop :=
  w ∈ frontier Ω ∧ ∃ f : ℝ → ℂ, ContinuousOn f (Icc 0 1) ∧ InjOn f (Icc 0 1) ∧ f '' Ioo 0 1 ⊆ Ω ∧ f 1 = w

/-- **Definition** (the set `A` of accessible points, Ch. VI §3, P2:905–909; used in Theorem 3.2, Lemma 5.3, P2:1170,
and the proof of Theorem 6.1, P2:1386). `A = {accessible points of ∂Ω}`. -/
def accessiblePoints (Ω : Set ℂ) : Set ℂ :=
  {w | IsAccessiblePoint Ω w}

/-- **Lemma 3.1** (Ch. VI §3), first part (cited at P2:931 in the proof of Theorem 3.2). If `φ` has a nontangential
limit `φ(ζ)` at `ζ ∈ ∂𝔻`, then `φ(ζ) ∈ ∂Ω` and `φ(ζ)` is an accessible point of `∂Ω`.
Modelling: standing assumption (module docstring) through `IsConformalOnto φ unitDisc Ω`; `ζ ∈ ∂𝔻` is part of
`HasNontangentialLimit`; `φ(ζ) = w` is finite; `w ∈ ∂Ω` is part of `IsAccessiblePoint`. -/
theorem lemma6_3_1_a {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ unitDisc Ω) {ζ w : ℂ}
    (hw : HasNontangentialLimit φ ζ w) :
    IsAccessiblePoint Ω w := by
  sorry

/-- **Lemma 3.1** (Ch. VI §3), second part. Conversely, every accessible `w ∈ ∂Ω` is a nontangential limit
`w = φ(ζ)`.
Modelling: as in the first part; "`w = φ(ζ)`" is: `φ` has the nontangential limit `w` at some `ζ ∈ ∂𝔻`. -/
theorem lemma6_3_1_b {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ unitDisc Ω) {w : ℂ}
    (hw : IsAccessiblePoint Ω w) :
    ∃ ζ : ℂ, HasNontangentialLimit φ ζ w := by
  sorry

/-- **Theorem 3.2** (Ch. VI §3), first part, the Borel claim (cited in the proof of Lemma 5.3, P2:1195, and in
Exercise VI.7, P2:1690). Let `Ω` be a simply connected domain. Then the set `A` of accessible points is a Borel
subset of `∂Ω`.
Modelling: `Ω ⊆ ℂ` with `Gehring1978.IsHypSimplyConnectedExt (toExt Ω)`; `A ⊆ ∂Ω` holds by definition; Borel is
`MeasurableSet` in `ℂ`: the book's "Clearly, `A` is a Borel set" (P2:931), asserted as printed (leader ruling
C12(e)). Audit note: not certified. `A = φ(R)` for the Borel set `R` of points with a nontangential limit (Lemma
3.1), so `A` is analytic; the fibres `φ⁻¹(w)` can be uncountable (a flower of countably many petal loops at `w`
ordered like the gaps of a Cantor set), so Lusin–Souslin does not apply directly. (3.2) in `thm6_3_2_a` does not use
this claim. -/
theorem thm6_3_2_a_borel {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) :
    MeasurableSet (accessiblePoints Ω) := by
  sorry

/-- **Theorem 3.2** (Ch. VI §3), first part, (3.2) (cited in the proof of Lemma 5.3, P2:1195, and in Exercise VI.7,
P2:1690). Let `Ω` be a simply connected domain. Then for all `z ∈ Ω`, (3.2) `ω(z, A, Ω) = 1`.
Modelling: `Ω ⊆ ℂ` with `Gehring1978.IsHypSimplyConnectedExt (toExt Ω)`; `ω(z, ·, Ω)` is
`harmonicMeasureWiener (toExt Ω) z` (module docstring), and `ω(z, A, Ω)` is the value of the measure on `A` (inner
and outer values agree: compact `K ⊆ R` on which `φ` is continuous give compact `φ(K) ⊆ A` of harmonic measure
`≥ |K|/2π`, by the second part); the Borel claim is split off as `thm6_3_2_a_borel`, which (3.2) does not depend on.
The formula (3.2) was checked against the equation image. -/
theorem thm6_3_2_a {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) :
    ∀ z ∈ Ω, harmonicMeasureWiener (toExt Ω) (z : ExtPlane) (toExt (accessiblePoints Ω)) = 1 := by
  sorry

/-- **Theorem 3.2** (Ch. VI §3), second part, (3.3) (cited in the proof of Lemma 5.3, P2:1195). Let `Ω` be a simply
connected domain and `φ : 𝔻 → Ω` a conformal mapping. If `E ⊆ A`, then
(3.3) `ω(z, E, Ω) = ω(φ⁻¹(z), φ⁻¹(E), 𝔻)`.
Modelling: `E` is a Borel set (the book's proof: "each side of (3.3) defines a Borel measure", P2:937); every
`z ∈ Ω` is `φ(w)` with `w = φ⁻¹(z) ∈ 𝔻`, so (3.3) is stated for all `w ∈ 𝔻` at `z = φ(w)`; `φ⁻¹(E)` is
`bdryPreimage φ E`; `ω(·, ·, 𝔻)` is `harmonicMeasureDisc`. The formula (3.3) was checked against the equation
image. -/
theorem thm6_3_2_b {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ unitDisc Ω) {E : Set ℂ} (hEA : E ⊆ accessiblePoints Ω) (hE : MeasurableSet E) :
    ∀ w ∈ unitDisc,
      harmonicMeasureWiener (toExt Ω) (φ w : ExtPlane) (toExt E) = harmonicMeasureDisc w (bdryPreimage φ E) := by
  sorry

/-- **Theorem 3.2** (Ch. VI §3), third part. In particular, for `E ⊆ A`,
`ω(z, E, Ω) = 0 ⟺ |φ⁻¹(E)| = 0`.
Modelling: as in the second part (`E` Borel, `φ⁻¹(E)` is `bdryPreimage φ E`), for every `z ∈ Ω`; `|·|` is
`arcMeasure`. The formula was checked against the equation image. -/
theorem thm6_3_2_c {Ω : Set ℂ} (hΩ : IsHypSimplyConnectedExt (toExt Ω)) {φ : ℂ → ℂ}
    (hφ : IsConformalOnto φ unitDisc Ω) {E : Set ℂ} (hEA : E ⊆ accessiblePoints Ω) (hE : MeasurableSet E) :
    ∀ z ∈ Ω, (harmonicMeasureWiener (toExt Ω) (z : ExtPlane) (toExt E) = 0 ↔ arcMeasure (bdryPreimage φ E) = 0) := by
  sorry

end GarnettMarshall2005
