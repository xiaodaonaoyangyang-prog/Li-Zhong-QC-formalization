import References.Katok1992.Ch03.S03_IsometricCirclesFordRegion

/-!
# Katok 1992, Ch. 3 §3.4 The limit set of Γ

S. Katok, *Fuchsian Groups* (1992), Chapter 3, §3.4; source `full.md` of `Fuchsian groups (Katok, Svetlana)
…-3766f6b7…`, lines 1558–1619.

* Definition (the limit set `Λ(Γ)`, ordinary points; l. 1560, from §2.2) — exists: `Katok1992.limitSet`
* Definition (the set `Λ₀(Γ)` of limit points of the centres of the isometric circles; l. 1562–1564) — `isoCenters`,
  `isoCenterLimits`
* Theorem 3.4.1 (`Λ₀(Γ) ⊆ Σ`; l. 1564) — `thm3_4_1`
* Theorem 3.4.2 (`Λ(Γ) = Λ₀(Γ)`; l. 1568) — `discPoint`, `thm3_4_2`
* Lemma 3.4.3 (l. 1586) — `IsBoundaryLimit`, `lemma3_4_3`
* Theorem 3.4.4 (`Λ(Γ)` is the closure of the fixed points of the hyperbolic elements; l. 1592) — `thm3_4_4`
* Theorem 3.4.5 (`Λ(Γ)` is `Γ`-invariant; l. 1598) — `thm3_4_5`
* Theorem 3.4.6 (`Λ(Γ) = Σ`, or perfect and nowhere dense; l. 1602) — `limitSetOnCircle`, `thm3_4_6`
* Definition (Fuchsian groups of the first and second kind; l. 1612–1618) — `IsFirstKind`, `IsSecondKind`

**Conventions.** The group is `Γ ≤ PSL(2, ℝ)`; the principal circle `Σ` is `ℝ ∪ {∞}` in the upper half-plane model
(`OnePoint ℝ`, with the scoped action `pslActionBoundary`) and the unit circle in the disc. The limit set is
`Katok1992.limitSet Γ ⊆ ℂ̂`, which lies in `ℝ ∪ {∞}` (`limitSet_subset_boundary`); `limitSetOnCircle Γ` is the same
set as a subset of `OnePoint ℝ`, the principal circle. Theorems 3.4.1 and 3.4.2 are statements of the disc model: the
centres of the isometric circles are those of `discIsometricCircle`, and the disc point corresponding to a point at
infinity `α` is `discPoint α` (`f(α)` for Katok's Cayley map `f = cayleyK`, and `f(∞) = i`). Lemma 3.4.3 and the
theorems after it are stated in the upper half-plane model, as the book remarks (l. 1590) that the lemma holds in
both models.

**Near misses.** `GardinerLakic2000.IsFirstKind` (limit set `= ℝ̂`, for subgroups of `SL(2, ℝ)`),
`FarkasKra1992.IsFuchsianFirstKind` (for Kleinian groups with an invariant disc), `LiZhongQC.IsQuasiFuchsianFirstKind`;
the notion of a limit set is `Katok1992.limitSet`.
-/

open Set Metric Filter Topology
open scoped UpperHalfPlane MatrixGroups

noncomputable section

namespace Katok1992

open LiZhongQC (ExtPlane)

/-- **Definition** (§3.4; l. 1562). The centres of the isometric circles of the elements of `Γ` in the unit disc:
`k` is a centre if `discIsometricCircle T = sphere k r` for some `T ∈ Γ` with `c ≠ 0` and some radius `r`. -/
def isoCenters (Γ : Subgroup PSL(2, ℝ)) : Set ℂ :=
  {k | ∃ T ∈ Γ, ∃ r : ℝ, discC T ≠ 0 ∧ discIsometricCircle T = sphere k r}

/-- **Definition** (§3.4; l. 1562–1564). `Λ₀(Γ)`: the set of limit points (accumulation points) of the set of centres of
the isometric circles of the elements of `Γ`. -/
def isoCenterLimits (Γ : Subgroup PSL(2, ℝ)) : Set ℂ :=
  {α | AccPt α (𝓟 (isoCenters Γ))}

/-- **Theorem 3.4.1** (§3.4; l. 1564). In the unit disc model, `Λ₀(Γ)` is a subset of the principal circle `Σ`. -/
theorem thm3_4_1 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) : isoCenterLimits Γ ⊆ sphere (0 : ℂ) 1 := by
  sorry

/-- **The disc point of a point at infinity** (§1.2, (1.2.2), used in §3.4): `f(α)` for Katok's Cayley map
`f = cayleyK`, and `f(∞) = i`. -/
def discPoint : ExtPlane → ℂ := fun α => OnePoint.elim α Complex.I cayleyK

/-- **Theorem 3.4.2** (§3.4; l. 1568). `Λ(Γ) = Λ₀(Γ)`: the limit set (transported to the unit disc by the Cayley map) is
the set of limit points of the centres of the isometric circles. -/
theorem thm3_4_2 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) :
    isoCenterLimits Γ = discPoint '' limitSet Γ := by
  sorry

/-- **Limit point of an orbit on the boundary** (§3.4; l. 1586). `α ∈ ℝ ∪ {∞}` is a limit point for `Γβ` if `α = lim T_n β`
for a sequence of distinct elements `T_n ∈ Γ`. -/
def IsBoundaryLimit (Γ : Subgroup PSL(2, ℝ)) (β α : OnePoint ℝ) : Prop :=
  ∃ T : ℕ → Γ, Function.Injective T ∧ Tendsto (fun n => (T n : PSL(2, ℝ)) • β) atTop (𝓝 α)

/-- **Lemma 3.4.3** (§3.4; l. 1586, and the Remark l. 1590 for the upper half-plane). Let `α, β, δ ∈ Σ` be three distinct
points with `α ∈ Λ(Γ)`. Then `α` is a limit point either for `Γβ` or for `Γδ`. -/
theorem lemma3_4_3 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {α β δ : OnePoint ℝ} (hαβ : α ≠ β) (hαδ : α ≠ δ)
    (hβδ : β ≠ δ) (hα : boundaryToExt α ∈ limitSet Γ) : IsBoundaryLimit Γ β α ∨ IsBoundaryLimit Γ δ α := by
  sorry

/-- **Theorem 3.4.4** (§3.4; l. 1592). If `Λ(Γ)` contains more than one point, it is the closure of the set of fixed points
of the hyperbolic transformations of `Γ`. -/
theorem thm3_4_4 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (h : (limitSet Γ).Nontrivial) :
    limitSet Γ = closure (boundaryToExt '' {ξ : OnePoint ℝ | ∃ T ∈ Γ, IsHyperbolic T ∧ T • ξ = ξ}) := by
  sorry

/-- **Theorem 3.4.5** (§3.4; l. 1598). The limit set `Λ(Γ)` is `Γ`-invariant. -/
theorem thm3_4_5 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) {T : PSL(2, ℝ)} (hT : T ∈ Γ) {α : OnePoint ℝ}
    (hα : boundaryToExt α ∈ limitSet Γ) : boundaryToExt (T • α) ∈ limitSet Γ := by
  sorry

/-- **The limit set as a subset of the principal circle** (§3.4): `{α ∈ ℝ ∪ {∞} | α ∈ Λ(Γ)}`, a subset of `OnePoint ℝ`. -/
def limitSetOnCircle (Γ : Subgroup PSL(2, ℝ)) : Set (OnePoint ℝ) := {α | boundaryToExt α ∈ limitSet Γ}

/-- **Theorem 3.4.6** (§3.4; l. 1602). If `Λ(Γ)` contains more than two points, then either (i) `Λ(Γ) = Σ`, or (ii) `Λ(Γ)`
is a perfect nowhere dense subset of `Σ`. -/
theorem thm3_4_6 {Γ : Subgroup PSL(2, ℝ)} (hΓ : IsFuchsian Γ) (h : 2 < (limitSetOnCircle Γ).encard) :
    limitSetOnCircle Γ = univ ∨ (Perfect (limitSetOnCircle Γ) ∧ IsNowhereDense (limitSetOnCircle Γ)) := by
  sorry

/-- **Definition** (§3.4; l. 1612). A Fuchsian group is of the *first kind* if every point of the principal circle is a
limit point: `Λ(Γ) = Σ`. -/
def IsFirstKind (Γ : Subgroup PSL(2, ℝ)) : Prop := limitSetOnCircle Γ = univ

/-- **Definition** (§3.4; l. 1613). A Fuchsian group is of the *second kind* if its limit points are nowhere dense on the
principal circle. -/
def IsSecondKind (Γ : Subgroup PSL(2, ℝ)) : Prop := IsNowhereDense (limitSetOnCircle Γ)

end Katok1992
