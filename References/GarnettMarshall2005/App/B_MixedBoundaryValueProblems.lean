import References.GarnettMarshall2005.Ch02.S04_BoundarySmoothness

/-!
# Garnett–Marshall, Appendix B: Mixed boundary value problems

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Appendix B (pp. 441–447;
`full.md` P3:2535–2775: the main text to P3:2742, the Notes paragraph at P3:2744, Exercises B.1–B.3 at
P3:2746–2775).

Conventions (leader rulings Fa1, Fa2). App. B's standing domain (P3:2539) is a bounded plane domain `Ω : Set ℂ` with
`∂Ω = Γ₁ ∪ … ∪ Γ_m`, the `Γ_j` pairwise disjoint Jordan curves of class `C^{1+α}` (Ch. II §4's `IsCurveOfClass 1 α`,
with `0 < α < 1`, the range of the class), bundled with the curves named as `IsBoundedSmoothFCDomain Ω Γ α`.
Theorems B.1 and B.4 repeat "finitely connected Jordan domain with `∂Ω ∈ C^{1+α}`" without "bounded" and without
naming the curves; the standing sentence supplies both. Boundaries and closures are taken in `ℂ` (for bounded `Ω` the
boundary in `ℂ*` is the image of the plane boundary). Functions are real and planar, `ℂ → ℝ`; where a predicate of
Ch. II on `ℂ*` is applied, a function `v` is lifted by `fun w => w.elim 0 v` (Mathlib's `OnePoint.elim`), whose value
at `∞` is never read. `C¹(Ω ∪ S)` is `IsC1UpTo Ω S`: `v` is `C¹` on `Ω`, and `v` and its derivative extend
continuously to `Ω ∪ S` (the extension of the values is a separate function, so that no junk boundary value is read);
`C¹(Ω̄)` is the case `S = ∂Ω`. The normal derivative `∂v/∂n` is Ch. II §2's predicate `HasOuterNormalDeriv` (outer
unit normal; it reads only values of `v` inside `Ω`, and for a `C¹(Ω̄)` function it is `∇v · n`). A boundary
condition that reads `u`'s own values on `∂Ω` ("`u = f₁` on `∂Ω \ J`") comes with `u ∈ C(Ω̄)`, as
`ContinuousOn u (closure Ω)` (leader ruling Fa2). `ds` on `∂Ω` is `arcLengthOn` (`μH[1]` on the boundary), and on one
curve `Γ_k` it is `μH[1]` restricted to `Γ_k` (leader ruling C2); `f ∈ C^β(∂Ω)` is `C^{0+β}` as a function of arc
length on each `Γ_j` (`MemCkAlphaOnCurve 0 β`, P1:2884); `ω_j(z) = ω(z, Γ_j, Ω)` is the finitely connected harmonic
measure `harmonicMeasureFC` (the explicit finitely connected setting, leader ruling D1). "Harmonic" is Mathlib's
`InnerProductSpace.HarmonicOnNhd`.

* Definition (the Neumann problem: find `v ∈ C¹(Ω̄)` harmonic on `Ω` with `∂v/∂n = f` on `∂Ω`; the classes `C¹(Ω̄)`
  and `C¹(Ω ∪ J)` of Theorem B.4, App. B, P3:2545, 2707) — `IsNeumannSolution`, `IsC1UpTo`
* Formula (B.1) (App. B, P3:2545–2549; the necessary condition `∫_{∂Ω} f ds = 0`) — `eqB_1`
* Theorem B.1 (App. B; (B.2)) — `thmB_1`
* Lemma B.2 (App. B) — `lemmaB_2`
* Lemma B.3 (App. B; the matrix (B.4)) — `lemmaB_3`
* Theorem B.4 (App. B; (B.6), (B.7)) — `thmB_4_a`, `thmB_4_b`
* Definition (the doubled Riemann surface `Ω_d = (Ω ∪ J ∪ τ(Ω ∪ J))/∼` with its local coordinates `Φ`, Figure B.1,
  App. B, P3:2723–2736) — omitted: a device of the proof of Theorem B.4 (leader ruling Fa4); no statement of the book
  uses it; the proof of Theorem IV.4.2 (P1:6244) and App. H (P3:4568, 4622) point to or rebuild the construction
  inside proofs, and App. H defines its own double

Helper (not a book notion): `IsBoundedSmoothFCDomain` (App. B's standing domain with its boundary curves named).

Not stated (inventory U−, remarks and proof steps): the heat-flow interpretation (`v` the steady-state temperature, the
loss of heat `∫_J ∂v/∂n ds` through an arc `J`, P3:2539–2545); "Except for issues of smoothness, (B.1) is the only
condition necessary for the Neumann problem" (P3:2551, it announces Theorem B.1); the weaker conclusion for continuous
`f` with (B.1), pointing to Exercise B.1 (P3:2561); the proof of Theorem B.1 (uniqueness through local maps onto a
half-disc and the reflection (B.3); existence for simply connected `Ω` through `F(γ(s)) = ∫₀^s f` and
Corollaries II.4.5, II.4.6, P3:2563–2597); the proof of Lemma B.2 (the criterion `∫_γ ∂ũ/∂s ds = 0`, the periods
`P_j(ũ)` with `Σ P_j(ũ) = 0`, the reflection of `ω_j`, P3:2607–2649; the matrix (B.4) is written inline in Lemma B.3);
the existence proof of Theorem B.1 for `m > 1` (the `b_j` with (B.5), `F` on each `Γ_j`, `u₁`, `u₂ = Re H`,
`v₂ = −Im H`, P3:2661–2703); "The solutions to the Neumann and Dirichlet problems combine to solve mixed boundary
value problems" (P3:2705, it announces Theorem B.4); the claims of the proof of Theorem B.4 about the double (the
example `Ω = 𝔻`, `Ω_d ≅ ℂ* \ (∂𝔻 \ J)`; a symmetric harmonic `v` has `∂v/∂n = 0` on `J`; "the Dirichlet problem can
be solved on `Ω_d`" by the Schwarz alternating method, P3:2736–2738, borderline: the proof of Theorem IV.4.2,
P1:6244, points to it from a proof); the existence (`u₁ + u₂`) and uniqueness (maximum principle on `Ω_d`) steps of
the proof of Theorem B.4 (P3:2740–2742). (B.3) and (B.5) are proof steps. The Notes paragraph (P3:2744) and
Exercises B.1–B.3 (the Herglotz-type `H`, the Neumann kernel `N(z, ζ)`, the symmetry of (B.4)) are not items.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real References

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (ExtPlane toExt IsJordanCurve)
open InnerProductSpace (HarmonicOnNhd)

/-- App. B's standing domain (helper, App. B, P3:2537–2539): "Let `Ω` be a bounded finitely connected Jordan domain
with `∂Ω = ⋃_{j=1}^m Γ_j` where each `Γ_j` is of class `C^{1+α}` and `Γ_j ∩ Γ_k = ∅` if `j ≠ k`."
Modelling (leader ruling Fa1): `Ω` is a bounded, open and connected subset of `ℂ` whose plane boundary is the union
of the curves `Γ_j`, `j ∈ Fin m`, pairwise disjoint and of class `C^{1+α}` in the sense of Ch. II §4
(`IsCurveOfClass 1 α`: a Jordan curve of `ℂ` with a `C^{1+α}` arc length parametrization); `0 < α < 1` is the range
of the class (P1:2820; a curve of class `C^{1+α}` for a larger `α` is of class `C^{1+α'}` for every `α' < 1`). Such
an `Ω` is a finitely connected Jordan domain, and `m ≥ 1` is automatic (a bounded non-empty open set has non-empty
boundary). -/
def IsBoundedSmoothFCDomain (Ω : Set ℂ) {m : ℕ} (Γ : Fin m → Set ℂ) (α : ℝ) : Prop :=
  IsOpen Ω ∧ IsConnected Ω ∧ Bornology.IsBounded Ω ∧ 0 < α ∧ α < 1 ∧ (∀ j, IsCurveOfClass 1 α (Γ j)) ∧
    (Pairwise fun i j => Disjoint (Γ i) (Γ j)) ∧ frontier Ω = ⋃ j, Γ j

/-- **Definition** (the classes `C¹(Ω̄)` and `C¹(Ω ∪ J)`, App. B, P3:2545 and Theorem B.4, P3:2707; used for
`C¹(Ω)` in App. H, Corollary H.2). `v ∈ C¹(Ω ∪ S)`: `v` is continuously differentiable on `Ω`, and `v` and its
first partial derivatives extend continuously to `Ω ∪ S`. `C¹(Ω̄)` is the case `S = ∂Ω`.
Modelling (leader ruling Fa2): the continuous extensions are separate functions `V` (of the values) and `G` (of the
derivative `fderiv ℝ v`, which contains both partial derivatives); they agree with `v` and its derivative on `Ω`
only, so the predicate never reads `v`'s own values on `S` (a statement that needs them, such as a Dirichlet
condition, carries `ContinuousOn v (closure Ω)` itself). -/
def IsC1UpTo (Ω S : Set ℂ) (v : ℂ → ℝ) : Prop :=
  ContDiffOn ℝ 1 v Ω ∧ (∃ V : ℂ → ℝ, ContinuousOn V (Ω ∪ S) ∧ EqOn V v Ω) ∧
    ∃ G : ℂ → (ℂ →L[ℝ] ℝ), ContinuousOn G (Ω ∪ S) ∧ EqOn G (fderiv ℝ v) Ω

/-- **Definition** (the Neumann problem, App. B, P3:2545; "Neumann problem" also in IV Notes, P1:6500, and App. H,
P3:4584). Given a function `f` on `∂Ω`, the Neumann problem is to find `v ∈ C¹(Ω̄)` such that `v` is harmonic on
`Ω` and `∂v/∂n = f` on `∂Ω`; such a `v` is a solution of the Neumann problem for `f`.
Modelling (leader ruling Fa2): `f` is read on the plane boundary `∂Ω`; `C¹(Ω̄)` is `IsC1UpTo Ω (frontier Ω)`;
`∂v/∂n = f` is Ch. II §2's `HasOuterNormalDeriv` for the domain `Ω ⊆ ℂ*` and the lift of `v` (for bounded `Ω` the
value at `∞` is never read); for `v ∈ C¹(Ω̄)` it is `∇v · n`, `n` the unit outer normal. -/
def IsNeumannSolution (Ω : Set ℂ) (f v : ℂ → ℝ) : Prop :=
  HarmonicOnNhd v Ω ∧ IsC1UpTo Ω (frontier Ω) v ∧
    ∀ ζ ∈ frontier Ω, HasOuterNormalDeriv (toExt Ω) (fun w => w.elim 0 v) ζ (f ζ)

/-- **Formula (B.1)** (App. B, P3:2545–2549; cited at P3:2551, 2561, and in substance in the existence proof of
Theorem B.1, P3:2673). Let `Ω` be App. B's standing domain. If `v ∈ C¹(Ω̄)` is harmonic on `Ω` with `∂v/∂n = f` on
`∂Ω`, then by Green's theorem `f` must satisfy the necessary condition (B.1)
`∫_{∂Ω} f ds = ∫_{∂Ω} ∂v/∂n ds = 0`.
Modelling: `ds` is `arcLengthOn` (the middle term is the left one, since `∂v/∂n = f` on `∂Ω`); `f = ∂v/∂n` is
continuous on `∂Ω` for `v ∈ C¹(Ω̄)` and a `C^{1+α}` boundary, hence integrable for the finite measure `ds`, so the
integral is not a junk value. (B.1) was checked against the equation image. -/
theorem eqB_1 {Ω : Set ℂ} {m : ℕ} {Γ : Fin m → Set ℂ} {α : ℝ} (hΩ : IsBoundedSmoothFCDomain Ω Γ α)
    {f v : ℂ → ℝ} (hv : IsNeumannSolution Ω f v) :
    ∫ ζ, f ζ ∂(arcLengthOn (toExt Ω)) = 0 := by
  sorry

/-- **Theorem B.1** (App. B; cited at P3:2561, in the proof of Lemma B.3 (its uniqueness part, P3:2659), at P3:2661, in
the proof of Theorem B.4, P3:2740, and in Exercises B.1, B.2). Suppose `Ω` is a finitely connected Jordan domain such
that `∂Ω ∈ C^{1+α}` for some `α > 0`. Let `β > 0`, and suppose `f ∈ C^β(∂Ω)` satisfies `∫_{∂Ω} f ds = 0`. Then there is
a harmonic function `v ∈ C¹(Ω̄)` such that (B.2) `∂v/∂n = f` on `∂Ω`, and `v` is unique up to an additive constant.
Modelling: `Ω` is App. B's standing domain (bounded, with the boundary curves named; leader ruling Fa1); `f ∈ C^β(∂Ω)`
is `C^{0+β}` as a function of arc length on each `Γ_j`; `β ≥ 1` is allowed, as printed (`β = 1` is the Lipschitz
condition; only `β > 1` makes `f` constant on each `Γ_j`); "unique up to an additive constant" is: every solution `w`
equals `v + c` on `Ω` for a real constant `c`. One declaration for existence and uniqueness (the `thm2_1_1` precedent).
(B.2) was checked against the equation image. -/
theorem thmB_1 {Ω : Set ℂ} {m : ℕ} {Γ : Fin m → Set ℂ} {α : ℝ} (hΩ : IsBoundedSmoothFCDomain Ω Γ α) {β : ℝ}
    (hβ : 0 < β) {f : ℂ → ℝ} (hf : ∀ j, MemCkAlphaOnCurve 0 β (Γ j) f)
    (h0 : ∫ ζ, f ζ ∂(arcLengthOn (toExt Ω)) = 0) :
    ∃ v : ℂ → ℝ, IsNeumannSolution Ω f v ∧
      ∀ w : ℂ → ℝ, IsNeumannSolution Ω f w → ∃ c : ℝ, ∀ z ∈ Ω, w z = v z + c := by
  sorry

/-- **Lemma B.2** (App. B; cited at P3:2643, 2649 and in the proof of Theorem B.1, P3:2679). Let `Ω` be a bounded,
finitely connected Jordan domain. Write `∂Ω = ⋃_{j=1}^m Γ_j`, where `Γ_j ∩ Γ_k = ∅` for `j ≠ k` and each `Γ_j` is a
Jordan curve. Let `ω_j(z) = ω(z, Γ_j, Ω)`. If `u` is a harmonic function on `Ω`, then there exist unique
`a₁, …, a_{m−1}` such that `u(z) + Σ_{j=1}^{m−1} a_j ω_j(z)` has a single valued conjugate function on `Ω`.
Modelling: `Ω` is a bounded, open and connected subset of `ℂ`; the curves are indexed by `Fin (n + 1)` (`m = n + 1`,
and `m ≥ 1` is automatic for a bounded non-empty open set), the last curve `Γ_m` being the one left out of the sum;
the `Γ_j` are Jordan curves of `ℂ*` lying in `ℂ`; `ω_j` is the finitely connected harmonic measure
`harmonicMeasureFC` (the lemma is set in a finitely connected Jordan domain, leader ruling D1), read as the real
number `ω(z, Γ_j, Ω)`; "has a single valued conjugate function on `Ω`" is "is the real part of a function analytic on
`Ω`". -/
theorem lemmaB_2 {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : Bornology.IsBounded Ω) {n : ℕ}
    {Γ : Fin (n + 1) → Set ℂ} (hΓ : ∀ j, IsJordanCurve (toExt (Γ j)))
    (hdisj : Pairwise fun i j => Disjoint (Γ i) (Γ j)) (hΩΓ : frontier Ω = ⋃ j, Γ j) {u : ℂ → ℝ}
    (hu : HarmonicOnNhd u Ω) :
    ∃! a : Fin n → ℝ, ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧
      ∀ z ∈ Ω, (F z).re = u z + ∑ j, a j * (harmonicMeasureFC (toExt Ω) z (toExt (Γ j.castSucc))).toReal := by
  sorry

/-- **Lemma B.3** (App. B, in the proof of Lemma B.2; cited at P3:2649, in the proof of Theorem B.1, P3:2661, and in
Exercise B.3). The matrix `{α_{k,j}}_{j,k=1}^{m−1}`, where (B.4) `α_{k,j} = ∫_{Γ_k} ∂ω_j/∂n ds`, is nonsingular.
Modelling: a labelled lemma inside a proof (leader ruling C10), stated in the context of App. B's standing domain:
the proof of Lemma B.2 applies it after reducing to analytic boundary curves (which are of class `C^{1+α}`), and the
proof of Theorem B.1 applies it to the `C^{1+α}` domain itself (P3:2661). The curves are indexed by `Fin (n + 1)`
and `j, k` range over the first `n = m − 1` of them (`Fin.castSucc`); for `m = 1` the matrix is empty and its
determinant is `1`, as in the book. (B.4) is written inline (defined in the proof of Lemma B.2, used only here and in
Exercise B.3); `ds` on `Γ_k` is `μH[1]` restricted to `Γ_k`; `∂ω_j/∂n` is the value `outerNormalDeriv` for the
function `ω_j` on `ℂ*` (read only inside `Ω`). Its junk value `0` is not read: by Corollary II.4.6 (boundary data
constant on each `C^{1+α}` curve) `ω_j` and its derivatives extend continuously to `Ω̄`, so the normal derivative
exists at every point of `∂Ω`. (B.4) was checked against the equation image. -/
theorem lemmaB_3 {Ω : Set ℂ} {n : ℕ} {Γ : Fin (n + 1) → Set ℂ} {α : ℝ} (hΩ : IsBoundedSmoothFCDomain Ω Γ α) :
    (Matrix.of fun k j : Fin n => ∫ ζ in Γ k.castSucc,
      outerNormalDeriv (toExt Ω) (fun w => (harmonicMeasureFC (toExt Ω) w (toExt (Γ j.castSucc))).toReal) ζ
        ∂μH[1]).det ≠ 0 := by
  sorry

/-- **Theorem B.4** (App. B; cited in the second proof of Corollary C.4, P3:3157, 3161, and, for the construction of
`Ω_d` in its proof, in the proof of Theorem IV.4.2, P1:6244), existence. Let `Ω` be a finitely connected Jordan domain
with `∂Ω ∈ C^{1+α}` for some `α > 0`. Let `f₁ ∈ C(∂Ω)`, let `β > 0`, and let `f₂ ∈ C^β(∂Ω)` be such that
`∫_{∂Ω} f₂ ds = 0`. Let `J` be a finite union of open arcs in `∂Ω` with pairwise disjoint closures. Then there is a
harmonic function `u ∈ C¹(Ω ∪ J) ∩ C(Ω̄)` such that (B.6) `u = f₁` on `∂Ω \ J` and (B.7) `∂u/∂n = f₂` on `J`.
Modelling: `Ω` is App. B's standing domain (leader ruling Fa1); "a finite union of open arcs in `∂Ω` with pairwise
disjoint closures" is `J = ⋃_{i<k} s_i` for `k ≥ 1` open Jordan arcs `s_i ⊆ ∂Ω` (`LehtoVirtanen1973.IsOpenJordanArc`)
with pairwise disjoint closures ("a finite union" of arcs has at least one member, the reading of Ch. IV §4's
`IsFiniteUnionOf`, which is not used here because the closures of the members must be named); `C¹(Ω ∪ J)` is
`IsC1UpTo Ω J` and `C(Ω̄)` is `ContinuousOn u (closure Ω)`, and (B.6) reads `u`'s own values on `∂Ω \ J`, which are
those of the continuous extension (leader ruling Fa2); (B.7) is `HasOuterNormalDeriv`. (B.6) and (B.7) were checked
against the equation images. -/
theorem thmB_4_a {Ω : Set ℂ} {m : ℕ} {Γ : Fin m → Set ℂ} {α : ℝ} (hΩ : IsBoundedSmoothFCDomain Ω Γ α)
    {f₁ f₂ : ℂ → ℝ} (hf₁ : ContinuousOn f₁ (frontier Ω)) {β : ℝ} (hβ : 0 < β)
    (hf₂ : ∀ j, MemCkAlphaOnCurve 0 β (Γ j) f₂) (h0 : ∫ ζ, f₂ ζ ∂(arcLengthOn (toExt Ω)) = 0) {J : Set ℂ}
    (hJ : ∃ (k : ℕ) (s : Fin k → Set ℂ), 0 < k ∧
      (∀ i, LehtoVirtanen1973.IsOpenJordanArc (toExt (s i)) ∧ s i ⊆ frontier Ω) ∧
      (Pairwise fun i i' => Disjoint (closure (s i)) (closure (s i'))) ∧ J = ⋃ i, s i) :
    ∃ u : ℂ → ℝ, HarmonicOnNhd u Ω ∧ IsC1UpTo Ω J u ∧ ContinuousOn u (closure Ω) ∧
      EqOn u f₁ (frontier Ω \ J) ∧
      ∀ ζ ∈ J, HasOuterNormalDeriv (toExt Ω) (fun w => w.elim 0 u) ζ (f₂ ζ) := by
  sorry

/-- **Theorem B.4** (App. B), uniqueness. In the situation of `thmB_4_a`: if `∂Ω \ J ≠ ∅`, the function `u` is unique.
Modelling: two harmonic functions `u, u' ∈ C¹(Ω ∪ J) ∩ C(Ω̄)` that both satisfy (B.6) and (B.7) agree on `Ω̄` (the
only values the conditions see). [OCR] the clause is printed "I f ∂Ω \ J ≠ ∅" (P3:2719), read "If". [reading] Under
the literal reading of `J` (finitely many open arcs, at least one, with pairwise disjoint closures) the hypothesis
`∂Ω \ J ≠ ∅` always holds: each boundary curve `Γ` is connected, the arcs of `J` inside `Γ` are disjoint relatively
open subsets of `Γ`, and an open arc is not a closed curve, so they cannot cover `Γ`. The book's clause is aimed at a
`J` containing whole boundary curves (as in the proof of Theorem IV.4.2 and in App. H), which the printed statement
does not cover; the hypothesis is kept as printed. -/
theorem thmB_4_b {Ω : Set ℂ} {m : ℕ} {Γ : Fin m → Set ℂ} {α : ℝ} (hΩ : IsBoundedSmoothFCDomain Ω Γ α)
    {f₁ f₂ : ℂ → ℝ} (hf₁ : ContinuousOn f₁ (frontier Ω)) {β : ℝ} (hβ : 0 < β)
    (hf₂ : ∀ j, MemCkAlphaOnCurve 0 β (Γ j) f₂) (h0 : ∫ ζ, f₂ ζ ∂(arcLengthOn (toExt Ω)) = 0) {J : Set ℂ}
    (hJ : ∃ (k : ℕ) (s : Fin k → Set ℂ), 0 < k ∧
      (∀ i, LehtoVirtanen1973.IsOpenJordanArc (toExt (s i)) ∧ s i ⊆ frontier Ω) ∧
      (Pairwise fun i i' => Disjoint (closure (s i)) (closure (s i'))) ∧ J = ⋃ i, s i)
    (hne : (frontier Ω \ J).Nonempty) {u u' : ℂ → ℝ}
    (hu : HarmonicOnNhd u Ω ∧ IsC1UpTo Ω J u ∧ ContinuousOn u (closure Ω) ∧ EqOn u f₁ (frontier Ω \ J) ∧
      ∀ ζ ∈ J, HasOuterNormalDeriv (toExt Ω) (fun w => w.elim 0 u) ζ (f₂ ζ))
    (hu' : HarmonicOnNhd u' Ω ∧ IsC1UpTo Ω J u' ∧ ContinuousOn u' (closure Ω) ∧ EqOn u' f₁ (frontier Ω \ J) ∧
      ∀ ζ ∈ J, HasOuterNormalDeriv (toExt Ω) (fun w => w.elim 0 u') ζ (f₂ ζ)) :
    EqOn u u' (closure Ω) := by
  sorry

end GarnettMarshall2005
