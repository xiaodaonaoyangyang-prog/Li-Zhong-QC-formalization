import LiZhongQC.Ch08.S30_ModularGroupDiscontinuity

/-!
# §31 有限型 Riemann 曲面 — Riemann surfaces of finite type

* §31.1 surfaces of finite type `(g, n, m)`: a compact surface minus `n` punctures and `m`
  holes; punctures vs. holes; the Schottky double `S^d`; the exceptional types; the double of a
  non-exceptional surface has hyperbolic universal covering
                                      — `FiniteTypeStructure`, `IsSchottkyDouble`, `IsExceptionalType`
* §31.2 admissible quadratic differentials `Q̃(S₀)` (simple poles at punctures, real on the
  boundary curves); the symmetric extension to `S^d`; (31.1), the decomposition `Ω ⊕ Ω'`; Theorem
  31.1: `dim_ℝ Q̃(S₀) = 6g - 6 + 2n + 3m` (31.2)
                                      — `admissibleQDSpace`, `thm31_1_admissibleQD_finrank`
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace LiZhongQC

universe u

/-! ## §31.1 Basic notions -/

/-- A closed Jordan disc in a Riemann surface with smooth boundary: the closure of a bounded Jordan
domain in a chart, whose boundary is a `C¹` Jordan curve. -/
def IsClosedDiscIn {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] (D : Set X) : Prop :=
  ∃ x : X, D ⊆ (chartAt ℂ x).source ∧ ∃ J : Set ℂ, IsJordanDomain J ∧ Bornology.IsBounded J ∧
    closure J ⊆ (chartAt ℂ x).target ∧ chartAt ℂ x '' D = closure J ∧
    ∃ c : ℝ → ℂ, ContDiff ℝ 1 c ∧ (∀ t, deriv c t ≠ 0) ∧ (∀ t, c (t + 1) = c t) ∧
      InjOn c (Ico 0 1) ∧ c '' Ico 0 1 = frontier J

/-- **§31.1 (有限型曲面).**  `S` is a Riemann surface of type `(g, n, m)`: there are a closed
surface `X` of genus `g`, `n` points `P` and `m` pairwise disjoint closed discs `D j` (with smooth
boundary) such that `S` is conformally `X ∖ (P ∪ ⋃ D j)` (via the open holomorphic embedding `ι`).
The points of `P` are the punctures (穿孔点), the boundaries of the `D j` the holes (洞). -/
structure FiniteTypeStructure (S : Type u) [TopologicalSpace S] [ChartedSpace ℂ S] (g n m : ℕ) where
  X : ClosedRS.{u}
  P : Finset X.carrier
  D : Fin m → Set X.carrier
  ι : S → X.carrier
  genus : HasGenus X.carrier g
  card_P : P.card = n
  disc : ∀ j, IsClosedDiscIn (D j)
  disjoint : Pairwise fun i j => Disjoint (D i) (D j)
  disjoint_P : ∀ j, Disjoint (D j) ↑P
  embedding : Topology.IsOpenEmbedding ι
  holomorphic : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ι
  range_ι : range ι = (↑P ∪ ⋃ j, D j)ᶜ

/-- `S` is a Riemann surface of type `(g, n, m)` (the type of `S` is determined by `S`). -/
def IsFiniteType (S : Type u) [TopologicalSpace S] [ChartedSpace ℂ S] (g n m : ℕ) : Prop :=
  Nonempty (FiniteTypeStructure S g n m)

/-- §31.1: the type `(g, n, m)` of a surface of finite type is well defined; the puncture
neighbourhoods are punctured discs and the hole neighbourhoods are annuli. -/
theorem finiteType_type_unique {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m g' n' m' : ℕ} (h : IsFiniteType S g n m)
    (h' : IsFiniteType S g' n' m') : g = g' ∧ n = n' ∧ m = m' := by
  sorry

/-- §31.1 (例外型): the exceptional types
`(0,0,0), (0,1,0), (1,0,0), (0,2,0); (0,0,1), (0,1,1), (0,0,2)`: the surface or its Schottky double
does not have hyperbolic universal covering. -/
def IsExceptionalType (g n m : ℕ) : Prop :=
  (g, n, m) = (0, 0, 0) ∨ (g, n, m) = (0, 1, 0) ∨ (g, n, m) = (1, 0, 0) ∨ (g, n, m) = (0, 2, 0) ∨
    (g, n, m) = (0, 0, 1) ∨ (g, n, m) = (0, 1, 1) ∨ (g, n, m) = (0, 0, 2)

/-- The complement of a finite set of points of a Riemann surface, as an open subset (again a
Riemann surface). -/
def puncturedOpens {X : Type u} [TopologicalSpace X] [T2Space X] (P : Finset X) : TopologicalSpace.Opens X :=
  ⟨(↑P : Set X)ᶜ, P.finite_toSet.isClosed.isOpen_compl⟩

/-- An anti-conformal involution `J` of a Riemann surface. -/
def IsAnticonformalInvolution {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] (J : X ≃ₜ X) : Prop :=
  (∀ p, J (J p) = p) ∧ ∀ x : X, DifferentiableOn ℂ (fun z => conj (localMapExpr J x z)) (localMapDomain J x)

/-- **§31.1 (Schottky 二倍面).**  `(Xd, J, ιd)` is a Schottky double `S^d` of the surface `S` of type
`(g, n, m)` with structure `F`: `Xd` is a closed surface of genus `2g + m - 1` with an anti-conformal
involution `J`, `ιd : S → Xd` is a holomorphic open embedding, `ιd(S)` and `J(ιd(S))` (the mirror
image) are disjoint, and `Xd` is `ιd(S) ∪ J(ιd(S))` together with the fixed curves of `J` (the
`m` boundary curves) and the `2n` punctures (images of `P` and their mirror images). -/
structure IsSchottkyDouble {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}
    (F : FiniteTypeStructure S g n m) (Xd : ClosedRS.{u}) (J : Xd.carrier ≃ₜ Xd.carrier) (ιd : S → Xd.carrier)
    (Pd : Finset Xd.carrier) : Prop where
  genus : HasGenus Xd.carrier (2 * g + m - 1)
  involution : IsAnticonformalInvolution J
  embedding : Topology.IsOpenEmbedding ιd
  holomorphic : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ιd
  disjoint : Disjoint (range ιd) (range (J ∘ ιd))
  card_Pd : Pd.card = 2 * n
  Pd_invariant : J '' ↑Pd = ↑Pd
  cover : range ιd ∪ range (J ∘ ιd) ∪ {x | J x = x} ∪ ↑Pd = univ
  fixed_curves : {x | J x = x} = frontier (range ιd) \ ↑Pd

/-- §31.1: every surface of finite type with `m ≠ 0` holes has a Schottky double (obtained by gluing
`S` to its mirror image along the boundary curves). -/
theorem exists_schottkyDouble {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (hm : m ≠ 0) (F : FiniteTypeStructure S g n m) :
    ∃ (Xd : ClosedRS.{u}) (J : Xd.carrier ≃ₜ Xd.carrier) (ιd : S → Xd.carrier) (Pd : Finset Xd.carrier),
      IsSchottkyDouble F Xd J ιd Pd := by
  sorry

/-- §31.1: a non-exceptional surface of type `(g, n, 0)` has hyperbolic universal covering
(`ℍ/Γ` with `Γ` a torsion free Fuchsian group), and so has the Schottky double of a non-exceptional
surface of type `(g, n, m)`, `m ≠ 0`; hence their Poincaré metrics are defined. -/
theorem finiteType_hyperbolic {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] [T2Space S]
    [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S] {g n m : ℕ} (F : FiniteTypeStructure S g n m)
    (hex : ¬ IsExceptionalType g n m) :
    (m = 0 → ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → S),
      IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p) ∧
    (m ≠ 0 → ∀ (Xd : ClosedRS.{u}) (J : Xd.carrier ≃ₜ Xd.carrier) (ιd : S → Xd.carrier) (Pd : Finset Xd.carrier),
      IsSchottkyDouble F Xd J ιd Pd →
      ∃ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) (p : UpperHalfPlane → puncturedOpens Pd),
        IsFuchsian Γ ∧ ActsFreely Γ ∧ IsUniformization Γ p) := by
  sorry

/-- §31.1: positivity of the dimension (31.2) is *sufficient* for non-exceptionality — every
exceptional type has `6g - 6 + 2n + 3m ≤ 0`. -/
theorem not_exceptional_of_pos {g n m : ℕ} (h : 0 < 6 * (g : ℤ) - 6 + 2 * n + 3 * m) :
    ¬ IsExceptionalType g n m := by
  simp only [IsExceptionalType, Prod.mk.injEq]
  omega

/-- §31.1: conversely, a non-exceptional type has `6g - 6 + 2n + 3m ≥ 0`, so the dimension (31.2)
of `Q̃(S₀)` is never negative off the exceptional list.

**Correction.**  These two implications replace a previous `not_exceptional_iff` asserting
`¬ IsExceptionalType g n m ↔ 0 < 6g - 6 + 2n + 3m`, which is **false**.  `(0,3,0)` — the
thrice-punctured sphere — is not among the book's seven exceptional types, yet
`6·0 - 6 + 2·3 + 3·0 = 0`, so the left side holds and the right side fails; it is the unique
counterexample.  Weakening to `0 ≤ …` does not repair it either, because the value-`0` fibre is
mixed: `(1,0,0)` and `(0,0,2)` are exceptional and also give `0`.  Hence **no inequality in
`6g - 6 + 2n + 3m` characterises the exceptional list**, and the two implications here are
exactly its true content.

The book (§31.1) gives the exceptional types only as the explicit list
`(0,0,0), (0,1,0), (1,0,0), (0,2,0); (0,0,1), (0,1,1), (0,0,2)`, justified by the surface or its
Schottky double lacking a hyperbolic universal covering, and uses `6g - 6 + 2n + 3m` only in
(31.2), as `dim_ℝ Q̃(S₀)`.  It never states the equivalence.  The underlying conflation is between
*hyperbolic* and *positive-dimensional Teichmüller space*: the thrice-punctured sphere is
hyperbolic — it is the standard example — but rigid, so its Teichmüller space is a point. -/
theorem dim_nonneg_of_not_exceptional {g n m : ℕ} (h : ¬ IsExceptionalType g n m) :
    0 ≤ 6 * (g : ℤ) - 6 + 2 * n + 3 * m := by
  by_contra hlt
  rw [not_le] at hlt
  refine h ?_
  simp only [IsExceptionalType, Prod.mk.injEq]
  omega

/-! ## §31.2 Admissible quadratic differentials -/

variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] {g n m : ℕ}

/-- **§31.2 (允许二次微分).**  A meromorphic quadratic differential `q` on the closed surface `X` of
`F` is admissible for `S₀ = S` if (i) it is holomorphic except for at most simple poles at the
punctures `P`, and (ii) it extends continuously to the non-puncture boundary (the curves `∂(D j)`)
and takes real values along each such curve: `q(c(t)) c'(t)² ∈ ℝ` for the `C¹` parametrizations
`c` of the boundary curves in charts.  (The coefficients are normalized to vanish at the poles.) -/
def IsAdmissibleQD (F : FiniteTypeStructure S g n m) (q : F.X.carrier → ℂ → ℂ) : Prop :=
  IsDiffFamily 2 0 q ∧
  (∀ x : F.X.carrier, DifferentiableOn ℂ (q x) ((chartAt ℂ x).target ∩ chartAt ℂ x '' range F.ι)) ∧
  (∀ x : F.X.carrier, ∀ p ∈ F.P, p ∈ (chartAt ℂ x).source → q x (chartAt ℂ x p) = 0 ∧
    ∃ c : ℂ, ∃ r : ℂ → ℂ, AnalyticAt ℂ r (chartAt ℂ x p) ∧
      ∀ᶠ z in 𝓝[≠] (chartAt ℂ x p), q x z = c / (z - chartAt ℂ x p) + r z) ∧
  (∀ (x : F.X.carrier) (j : Fin m),
    ContinuousOn (q x) ((chartAt ℂ x).target ∩ chartAt ℂ x '' (range F.ι ∪ frontier (F.D j)))) ∧
  ∀ (x : F.X.carrier) (j : Fin m) (c : ℝ → ℂ) (a b : ℝ), ContDiffOn ℝ 1 c (Icc a b) →
    c '' Icc a b ⊆ (chartAt ℂ x).target ∩ chartAt ℂ x '' frontier (F.D j) →
    ∀ t ∈ Ioo a b, (q x (c t) * deriv c t ^ 2).im = 0

/-- §31.2: the admissible quadratic differentials form a real vector space `Q̃(S₀)`. -/
def admissibleQDSpace (F : FiniteTypeStructure S g n m) : Submodule ℝ (F.X.carrier → ℂ → ℂ) where
  carrier := {q | IsAdmissibleQD F q}
  add_mem' := by
    rintro q₁ q₂ ⟨h₁, d₁, p₁, c₁, r₁⟩ ⟨h₂, d₂, p₂, c₂, r₂⟩
    refine ⟨(diffFamilySubmodule _ 2 0).add_mem h₁ h₂, fun x => (d₁ x).add (d₂ x), ?_, ?_, ?_⟩
    · intro x p hp hs
      obtain ⟨z₁, a₁, s₁, hs₁, e₁⟩ := p₁ x p hp hs
      obtain ⟨z₂, a₂, s₂, hs₂, e₂⟩ := p₂ x p hp hs
      refine ⟨by simp [z₁, z₂], a₁ + a₂, fun z => s₁ z + s₂ z, hs₁.add hs₂, ?_⟩
      filter_upwards [e₁, e₂] with z hz₁ hz₂
      simp only [Pi.add_apply, hz₁, hz₂]
      ring
    · intro x j
      exact (c₁ x j).add (c₂ x j)
    · intro x j c a b hc hsub t ht
      have := r₁ x j c a b hc hsub t ht
      have := r₂ x j c a b hc hsub t ht
      simp only [Pi.add_apply, add_mul, Complex.add_im]
      linarith
  zero_mem' :=
    ⟨(diffFamilySubmodule _ 2 0).zero_mem, fun _ => differentiableOn_const 0,
      fun _ _ _ _ => ⟨rfl, 0, fun _ => 0, analyticAt_const, Filter.Eventually.of_forall fun _ => by simp⟩,
      fun _ _ => continuousOn_const, fun _ _ _ _ _ _ _ _ _ => by simp⟩
  smul_mem' := by
    rintro c q ⟨h, d, p, cont, r⟩
    refine ⟨(diffFamilySubmodule _ 2 0).smul_mem c h, fun x => (d x).const_smul c, ?_, ?_, ?_⟩
    · intro x p' hp hs
      obtain ⟨z, a, s, hs', e⟩ := p x p' hp hs
      refine ⟨by simp [z], c * a, fun w => c * s w, ?_, ?_⟩
      · exact analyticAt_const.mul hs'
      · filter_upwards [e] with w hw
        simp only [Pi.smul_apply, Complex.real_smul, hw]
        ring
    · intro x j
      exact (cont x j).const_smul c
    · intro x j c' a b hc hsub t ht
      have := r x j c' a b hc hsub t ht
      simp only [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, this, mul_zero]

/-- §31.2: for `m = 0` (no holes) the admissible differentials also form a complex vector space,
of complex dimension `3g - 3 + n` (Riemann–Roch, as for compact surfaces). -/
theorem admissibleQD_complex_finrank [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n 0) (hex : ¬ IsExceptionalType g n 0) :
    (∀ (c : ℂ) (q : F.X.carrier → ℂ → ℂ), IsAdmissibleQD F q → IsAdmissibleQD F (c • q)) ∧
      (Module.finrank ℝ (admissibleQDSpace F) : ℤ) = 2 * (3 * g - 3 + n) := by
  sorry

/-- §31.2: an admissible differential has at most one horizontal trajectory ending at a puncture
where it has a simple pole, and the non-puncture boundary curves consist of horizontal and vertical
trajectory arcs of `q` (as `q dz²` is real along them). -/
theorem admissibleQD_boundary_trajectories [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) {q : F.X.carrier → ℂ → ℂ} (hq : IsAdmissibleQD F q) (x : F.X.carrier)
    (j : Fin m) (c : ℝ → ℂ) (a b : ℝ) (hc : ContDiffOn ℝ 1 c (Icc a b)) (hc' : ∀ t ∈ Ioo a b, deriv c t ≠ 0)
    (hsub : c '' Icc a b ⊆ (chartAt ℂ x).target ∩ chartAt ℂ x '' frontier (F.D j))
    (hne : ∀ t ∈ Ioo a b, q x (c t) ≠ 0) :
    ∀ t ∈ Ioo a b, 0 < (q x (c t) * deriv c t ^ 2).re ∨ (q x (c t) * deriv c t ^ 2).re < 0 := by
  sorry

/-- §31.2: for `m ≠ 0` every admissible differential `q ∈ Q̃(S₀)` extends symmetrically (by
reflection through `J`) to an admissible differential `q^d` on the double `S^d` (a meromorphic
quadratic differential with at most `2n` simple poles); `q ↦ q^d` is injective and real linear. -/
theorem admissibleQD_symmetric_extension [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) {Xd : ClosedRS.{u}} {J : Xd.carrier ≃ₜ Xd.carrier}
    {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    (Fd : FiniteTypeStructure (puncturedOpens Pd) (2 * g + m - 1) (2 * n) 0) :
    ∃ ext : admissibleQDSpace F →ₗ[ℝ] admissibleQDSpace Fd, Function.Injective ext := by
  sorry

/-- (31.1): the double `S^d` is of type `(2g + m - 1, 2n, 0)`, so
`dim_ℝ Q̃(S^d) = 12g + 6m - 12 + 4n = 2(6g - 6 + 2n + 3m)`. -/
theorem eq31_1_double_finrank [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    (Fd : FiniteTypeStructure (puncturedOpens Pd) (2 * g + m - 1) (2 * n) 0) :
    (Module.finrank ℝ (admissibleQDSpace Fd) : ℤ) = 2 * (6 * g - 6 + 2 * n + 3 * m) := by
  sorry

/-- §31.2: the reflection `T : ω ↦ ω*` of `Q̃(S^d)` (`ω*` at `p` is the conjugate of `ω` at the mirror
point `p̄`, in the conjugate parameter) is a real linear involution, anti-linear over `ℂ`; the
symmetric differentials `Ω = {½(I + T)ω}` (identified with `Q̃(S₀)`) and the anti-symmetric ones
`Ω' = {½(I - T)ω} = iΩ` give `Q̃(S^d) = Ω ⊕ Ω'`, so `dim Ω = ½ dim Q̃(S^d)`. -/
theorem admissibleQD_double_decomposition [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hm : m ≠ 0) (hex : ¬ IsExceptionalType g n m) {Xd : ClosedRS.{u}}
    {J : Xd.carrier ≃ₜ Xd.carrier} {ιd : S → Xd.carrier} {Pd : Finset Xd.carrier} (hd : IsSchottkyDouble F Xd J ιd Pd)
    (Fd : FiniteTypeStructure (puncturedOpens Pd) (2 * g + m - 1) (2 * n) 0) :
    ∃ T : admissibleQDSpace Fd →ₗ[ℝ] admissibleQDSpace Fd, (∀ q, T (T q) = q) ∧
      (∀ (q : admissibleQDSpace Fd) (hq : (I : ℂ) • (q : Fd.X.carrier → ℂ → ℂ) ∈ admissibleQDSpace Fd),
        (T ⟨(I : ℂ) • (q : Fd.X.carrier → ℂ → ℂ), hq⟩ : Fd.X.carrier → ℂ → ℂ) =
          -((I : ℂ) • (T q : Fd.X.carrier → ℂ → ℂ))) ∧
      Module.finrank ℝ (LinearMap.ker (T - LinearMap.id)) = Module.finrank ℝ (admissibleQDSpace F) ∧
      Module.finrank ℝ (admissibleQDSpace Fd) = 2 * Module.finrank ℝ (LinearMap.ker (T - LinearMap.id)) := by
  sorry

/-- **Theorem 31.1** (31.2): for a non-exceptional surface `S₀` of type `(g, n, m)`,
`dim_ℝ Q̃(S₀) = 6g - 6 + 2n + 3m`. -/
theorem thm31_1_admissibleQD_finrank [T2Space S] [ConnectedSpace S] [IsManifold 𝓘(ℂ) ω S]
    (F : FiniteTypeStructure S g n m) (hex : ¬ IsExceptionalType g n m) :
    (Module.finrank ℝ (admissibleQDSpace F) : ℤ) = 6 * g - 6 + 2 * n + 3 * m := by
  sorry

end LiZhongQC
