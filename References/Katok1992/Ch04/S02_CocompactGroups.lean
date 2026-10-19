import References.Katok1992.Ch04.S01_GeometricallyFiniteGroups

/-!
# Katok 1992, Ch. 4 §4.2 Cocompact Fuchsian groups

S. Katok, *Fuchsian Groups* (1992), Chapter 4, §4.2; source `full.md` of `Fuchsian groups (Katok, Svetlana)
…-3766f6b7…`, lines 1909–2022.

* Definition (cocompact; l. 1911) — `IsCocompact`
* Theorem 4.2.1 (a compact Dirichlet region excludes parabolic elements; l. 1915) — `thm4_2_1`
* Theorem 4.2.2 (a non-compact Dirichlet region; l. 1937) — `idealBoundary`, `thm4_2_2_i`, `thm4_2_2_ii`
* Corollary 4.2.3 (`Γ\ℍ` is compact iff every Dirichlet region is; l. 1945) — `cor4_2_3`
* Definition (horocycles, Exercise 4.2; l. 1947–1955) — `horocycleThrough`
* Theorem 4.2.4 (parabolic iff it preserves each horocycle; l. 1957) — `thm4_2_4`
* Theorem 4.2.5 (vertices at infinity are parabolic fixed points; l. 1963) — `thm4_2_5_i`, `thm4_2_5_ii`
* Definition (maximal parabolic subgroups, their conjugacy classes; l. 2017) — `IsMaxParabolic`, `maxParabolicClasses`
* Corollary 4.2.6 (vertices at infinity ↔ conjugacy classes of maximal parabolic subgroups; l. 2017) — `cor4_2_6`
* Corollary 4.2.7 (cocompact iff finite area and no parabolic elements; l. 2021) — `cor4_2_7`

**Conventions.** Cocompact means `Γ\ℍ` compact (the orbit space with the quotient topology). A point `p` is *regular* if no
non-identity element of `Γ` fixes it; Dirichlet regions are `dirichletRegion Γ p` for regular `p`. The *vertices at
infinity* of a region `F` are the points of the Euclidean closure of `F` in `ℂ̂` lying on the principal circle,
`idealBoundary F ⊆ ℝ ∪ {∞}` (the set `∂₀F` of the book; for a Dirichlet region of finite area these are the vertices
where two sides meet, by Theorem 4.2.5). A *horocycle* at `ξ ∈ ℝ ∪ {∞}` through `p` is the level set through `p` of `|z − ξ|²/Im z` (`Im z` for `ξ = ∞`) (the limit of the circles `B_t(p)`, Euclidean circles tangent to `ℝ` at `ξ`, or the
horizontal lines for `ξ = ∞`). A *maximal parabolic subgroup* of `Γ` is a maximal subgroup of `Γ`, different from
`{Id}`, whose non-identity elements are all parabolic (the stabilizer in `Γ` of a parabolic fixed point).

**Corrections.** Theorem 4.2.4 [CORRECTION]: `S ≠ Id` is added (the identity fixes every point and preserves every horocycle but is
not parabolic).

**Near misses.** `LiZhongQC.IsCocompact` (the same for subgroups of `SL(2, ℝ)`), `LiZhongQC.cocompact_elements_hyperbolic`
(the covering group of a compact surface has only hyperbolic elements: the "no parabolic" direction of 4.2.7 for the
project's `IsFuchsian`).
-/

open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane MatrixGroups ENNReal Pointwise

noncomputable section

namespace Katok1992

open LiZhongQC (ExtPlane)

/-- **Definition** (§4.2; l. 1911). A Fuchsian group is *cocompact* if the quotient space `Γ\ℍ` is compact. -/
def IsCocompact (Γ : Subgroup PSL(2, ℝ)) : Prop := CompactSpace (MulAction.orbitRel.Quotient Γ ℍ)

/-- **Theorem 4.2.1** (§4.2; l. 1915). If a Fuchsian group `Γ` has a compact Dirichlet region, then `Γ` contains no parabolic
elements. -/
theorem thm4_2_1 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {p : ℍ} (hp : ∀ T ∈ Γ, T ≠ 1 → T • p ≠ p)
    (hc : IsCompact (dirichletRegion Γ p)) : ∀ T ∈ Γ, ¬ IsParabolic T := by
  sorry

/-- **The vertices at infinity of a region** (§4.2; `∂₀F`): the points of the principal circle `ℝ ∪ {∞}` in the Euclidean
closure of `F` in `ℂ̂`. -/
def idealBoundary (F : Set ℍ) : Set (OnePoint ℝ) := {ξ | boundaryToExt ξ ∈ closure (toExtH '' F)}

/-- **Theorem 4.2.2 (i)** (§4.2; l. 1937). If `Γ` has a non-compact Dirichlet region, then `Γ\ℍ` is not compact. -/
theorem thm4_2_2_i {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {p : ℍ} (hp : ∀ T ∈ Γ, T ≠ 1 → T • p ≠ p)
    (hc : ¬ IsCompact (dirichletRegion Γ p)) : ¬ IsCocompact Γ := by
  sorry

/-- **Theorem 4.2.2 (ii)** (§4.2; l. 1937). If a Dirichlet region `F = D_p(Γ)` has finite hyperbolic area but is not
compact, then it has at least one vertex at infinity. -/
theorem thm4_2_2_ii {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {p : ℍ} (hp : ∀ T ∈ Γ, T ≠ 1 → T • p ≠ p)
    (hμ : volume (dirichletRegion Γ p) < ⊤) (hc : ¬ IsCompact (dirichletRegion Γ p)) :
    (idealBoundary (dirichletRegion Γ p)).Nonempty := by
  sorry

/-- **Corollary 4.2.3** (§4.2; l. 1945). The quotient space `Γ\ℍ` of a Fuchsian group is compact if and only if any (every)
Dirichlet region for `Γ` is compact. -/
theorem cor4_2_3 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) :
    IsCocompact Γ ↔ ∀ p : ℍ, (∀ T ∈ Γ, T ≠ 1 → T • p ≠ p) → IsCompact (dirichletRegion Γ p) := by
  sorry

/-- **Definition** (§4.2; l. 1947–1955, Exercise 4.2). The *horocycle* at `ξ ∈ ℝ ∪ {∞}` through `p ∈ ℍ`: the level set through `p`
of `z ↦ |z − x|²/Im z` (`x ∈ ℝ`; a Euclidean circle tangent to `ℝ` at `x`) or of `z ↦ Im z` (`ξ = ∞`, a horizontal line):
the level sets of the Busemann function `References.busemann ξ`, which is not imported (module cycle with GL Ch. 10). -/
def horocycleThrough (ξ : OnePoint ℝ) (p : ℍ) : Set ℍ :=
  {z | OnePoint.elim ξ ((z : ℂ).im = (p : ℂ).im)
    (fun x => ‖(z : ℂ) - x‖ ^ 2 / (z : ℂ).im = ‖(p : ℂ) - x‖ ^ 2 / (p : ℂ).im)}

/-- **Theorem 4.2.4** (§4.2; l. 1957). Let `S ≠ Id` be a transformation in `PSL(2, ℝ)` fixing a point `s ∈ ℝ ∪ {∞}`. Then `S`
is parabolic if and only if every horocycle through `s` is mapped onto itself: `S(ω(s)) = ω(s)`. -/
theorem thm4_2_4 {S : PSL(2, ℝ)} (hS : S ≠ 1) {s : OnePoint ℝ} (hs : S • s = s) :
    IsParabolic S ↔ ∀ p : ℍ, S • horocycleThrough s p = horocycleThrough s p := by
  sorry

/-- **Theorem 4.2.5 (i)** (§4.2; l. 1963). Suppose `Γ` has a non-compact Dirichlet region `F = D_p(Γ)` with `μ(F) < ∞`. Then
each vertex of `F` at infinity is a parabolic fixed point for some `T ∈ Γ`. -/
theorem thm4_2_5_i {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {p : ℍ} (hp : ∀ T ∈ Γ, T ≠ 1 → T • p ≠ p)
    (hμ : volume (dirichletRegion Γ p) < ⊤) (hc : ¬ IsCompact (dirichletRegion Γ p)) :
    ∀ ξ ∈ idealBoundary (dirichletRegion Γ p), ∃ T ∈ Γ, IsParabolic T ∧ T • ξ = ξ := by
  sorry

/-- **Theorem 4.2.5 (ii)** (§4.2; l. 1963). In the situation of 4.2.5 (i), if `ξ` is a fixed point of some parabolic element
of `Γ`, then there exists `T ∈ Γ` such that `T(ξ) ∈ ∂₀(F)`. -/
theorem thm4_2_5_ii {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {p : ℍ} (hp : ∀ T ∈ Γ, T ≠ 1 → T • p ≠ p)
    (hμ : volume (dirichletRegion Γ p) < ⊤) (hc : ¬ IsCompact (dirichletRegion Γ p)) {ξ : OnePoint ℝ}
    (hξ : ∃ T ∈ Γ, IsParabolic T ∧ T • ξ = ξ) : ∃ S ∈ Γ, S • ξ ∈ idealBoundary (dirichletRegion Γ p) := by
  sorry

/-- **Maximal parabolic subgroups** (§4.2; l. 2017, used again in §5.5): a maximal subgroup of `Λ` different from `{Id}`
all of whose non-identity elements are parabolic. -/
def IsMaxParabolic (Λ : Subgroup PSL(2, ℝ)) (H : Subgroup PSL(2, ℝ)) : Prop :=
  H ≤ Λ ∧ H ≠ ⊥ ∧ (∀ T ∈ H, T ≠ 1 → IsParabolic T) ∧
    ∀ K : Subgroup PSL(2, ℝ), H ≤ K → K ≤ Λ → K ≠ ⊥ → (∀ T ∈ K, T ≠ 1 → IsParabolic T) → K = H

/-- **The classes of maximal parabolic subgroups** of `Λ` under conjugation by `Λ` (the quotient by the generated
relation `K = g H g⁻¹`, `g ∈ Λ`). -/
def maxParabolicClasses (Λ : Subgroup PSL(2, ℝ)) : Type :=
  Quot fun H K : {H : Subgroup PSL(2, ℝ) // IsMaxParabolic Λ H} =>
    ∃ g ∈ Λ, (K : Subgroup PSL(2, ℝ)) = (H : Subgroup PSL(2, ℝ)).map (MulAut.conj g).toMonoidHom

/-- **Corollary 4.2.6** (§4.2; l. 2017). Let `Γ` be non-cocompact with `μ(Γ\ℍ) < ∞` and `F` a Dirichlet region. There is a
one-to-one correspondence between the non-congruent vertices at infinity of `F` and the conjugacy classes of maximal
parabolic subgroups of `Γ`, given by `ξ ↦ class of the stabilizer of ξ`. -/
theorem cor4_2_6 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (hnc : ¬ IsCocompact Γ) (hμ : quotientArea Γ < ⊤) {p : ℍ}
    (hp : ∀ T ∈ Γ, T ≠ 1 → T • p ≠ p) :
    ∃ hmem : ∀ ξ : idealBoundary (dirichletRegion Γ p),
        IsMaxParabolic Γ ((MulAction.stabilizer Γ (ξ : OnePoint ℝ)).map Γ.subtype),
      ∃ e : (Quot fun ξ ζ : idealBoundary (dirichletRegion Γ p) => ∃ T ∈ Γ, T • (ξ : OnePoint ℝ) = ζ) ≃
          maxParabolicClasses Γ,
        ∀ ξ : idealBoundary (dirichletRegion Γ p),
          e (Quot.mk _ ξ) = Quot.mk _ ⟨(MulAction.stabilizer Γ (ξ : OnePoint ℝ)).map Γ.subtype, hmem ξ⟩ := by
  sorry

/-- **Corollary 4.2.7** (§4.2; l. 2021). A Fuchsian group `Γ` is cocompact if and only if `μ(Γ\ℍ) < ∞` and `Γ` contains no
parabolic elements. -/
theorem cor4_2_7 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) :
    IsCocompact Γ ↔ quotientArea Γ < ⊤ ∧ ∀ T ∈ Γ, ¬ IsParabolic T := by
  sorry

end Katok1992
