import References.Pommerenke1992.Ch02.S04_CrosscutsAndPrimeEnds

/-!
# Pommerenke 1992, Ch. 2 §2.5 Limits and Cluster Sets

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §2.5; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 1433–1548.

* Definition (impression `I(p)` of a prime end, (2.5.1); degenerate prime end) — `impression`, `IsDegenerate`
* Unlabelled (§2.5, l. 1441: `I(p)` is a non-empty compact connected set, independent of the null-chain representing
  `p`; the definition (2.5.1) rests on it) — `impression_spec`
* Definition (principal point; `Π(p)`, §2.5) — `principalPoints`
* Definition (the cluster set `C(f, ζ)`, (2.5.2)) — `clusterSet`
* Unlabelled (§2.5, l. 1462: formula (2.5.3); cited in the proof of Theorem 2.16) — `eq2_5_3`
* Definition (the cluster set `C_E(f, ζ)` along `E`, (2.5.4); the radius `[0, ζ)`; radial limit) — `clusterSetAlong`,
  `radius`, `HasRadialLimit`
* Theorem 2.16 — `thm2_16`
* Corollary 2.17 — `cor2_17_i`, `cor2_17_ii`

Not items (DESIGN §3): the compactness and connectedness of the cluster sets of continuous functions (l. 1466, 1474,
not cited); "the cluster set reduces to a point if and only if the corresponding limit exists" (l. 1530, immediate);
"`f` is continuous at `ζ` if and only if `f̂(ζ)` is degenerate" and "`f` has a finite angular limit almost everywhere"
(l. 1540, the first is `cor2_17_ii`, the second follows from Theorem 1.7; not cited); the results quoted from GaPo67,
NaRuSh82 and Two86 (l. 1542–1548, not cited).

**Conventions.** As in §2.4. Functions "in `𝔻` with values in `Ĉ`" are `f : ℂ → Ĉ` (their values off `𝔻` are never
used); a conformal map `f : Ĉ → Ĉ` of `𝔻` enters as `fun z : ℂ => f z`. A curve in `𝔻` ending at `ζ` is a half-open
curve (§1.1) in `𝔻` ending at `ζ`. The prime end `f̂(ζ)` of Theorem 2.15 is given by a correspondence `f̂` with
`IsPrimeEndCorrespondence` (it is unique).
-/

open Complex Set Metric Filter Topology
open scoped ENNReal NNReal Real

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane toExt unitDisc)
open LehtoVirtanen1973 (IsSimplyConnectedDomain IsConformalMap)

/-- **Definition (2.5.1)** (§2.5; cited as (2.5.1)). The impression `I(p) = ⋂_{n ≥ 1} V̄_n` of a prime end `p`
represented by the null-chain `(C_n)`; the prime end is degenerate if `I(p)` is a single point.
Modelling: the intersection is also taken over all the null-chains representing `p`; it does not depend on the
representative (`impression_spec`). -/
def impression (G : Set ExtPlane) (P : Set (ℕ → Set ExtPlane)) : Set ExtPlane :=
  ⋂ C ∈ P, ⋂ n ∈ Ici 1, closure (nullChainDomain G C n)

/-- **Definition** (§2.5). The prime end `p` is degenerate: its impression is a single point. -/
def IsDegenerate (G : Set ExtPlane) (P : Set (ℕ → Set ExtPlane)) : Prop :=
  ∃ a, impression G P = {a}

/-- **Unlabelled claim** (§2.5, l. 1441). For a prime end `p` of a simply connected domain `G`, the sets `V̄_n` of a
representing null-chain decrease, their intersection `I(p)` is a non-empty compact connected set (thus either a single
point or a continuum), and equivalent null-chains lead to the same intersection. -/
theorem impression_spec {G : Set ExtPlane} (hG : IsSimplyConnectedDomain G) {P : Set (ℕ → Set ExtPlane)}
    (hP : P ∈ primeEnds G) :
    (∀ C ∈ P, ∀ n, 1 ≤ n → closure (nullChainDomain G C (n + 1)) ⊆ closure (nullChainDomain G C n)) ∧
      (∀ C ∈ P, ⋂ n ∈ Ici 1, closure (nullChainDomain G C n) = impression G P) ∧
      IsCompact (impression G P) ∧ IsConnected (impression G P) := by
  sorry

/-- **Definition** (§2.5). `ω ∈ Ĉ` is a principal point of the prime end `p`: `p` can be represented by a null-chain
`(C_n)` with `C_n ⊆ D(ω, ε)` for `ε > 0`, `n > n₀(ε)`; `Π(p)` is the set of principal points.
Modelling: the discs are chordal discs, so that `ω = ∞` is allowed. -/
def principalPoints (P : Set (ℕ → Set ExtPlane)) : Set ExtPlane :=
  {ω | ∃ C ∈ P, ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, C n ⊆ {z | chordalDist ω z < ε}}

/-- **Definition (2.5.2)** (§2.5; cited as (2.5.2)). The (unrestricted) cluster set `C(f, ζ)` of a function `f` in `𝔻`
with values in `Ĉ` at `ζ ∈ 𝕋`: the `ω ∈ Ĉ` for which there are `z_n ∈ 𝔻` with `z_n → ζ` and `f(z_n) → ω`. -/
def clusterSet (f : ℂ → ExtPlane) (ζ : ℂ) : Set ExtPlane :=
  {ω | ∃ z : ℕ → ℂ, (∀ n, z n ∈ unitDisc) ∧ Tendsto z atTop (𝓝 ζ) ∧ Tendsto (f ∘ z) atTop (𝓝 ω)}

/-- **Unlabelled claim (2.5.3)** (§2.5, l. 1462; cited in the proof of Theorem 2.16).
`C(f, ζ) = ⋂_{r > 0} clos {f(z) : z ∈ 𝔻, |z - ζ| < r}` (closure in `Ĉ`). -/
theorem eq2_5_3 (f : ℂ → ExtPlane) {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) :
    clusterSet f ζ = ⋂ r > (0 : ℝ), closure (f '' (unitDisc ∩ ball ζ r)) := by
  sorry

/-- **Definition (2.5.4)** (§2.5). The cluster set `C_E(f, ζ)` of `f` at `ζ` along `E ⊆ 𝔻`: the `ω ∈ Ĉ` such that
`f(z_n) → ω` for some `z_n ∈ E`, `z_n → ζ`. -/
def clusterSetAlong (f : ℂ → ExtPlane) (E : Set ℂ) (ζ : ℂ) : Set ExtPlane :=
  {ω | ∃ z : ℕ → ℂ, (∀ n, z n ∈ E) ∧ Tendsto z atTop (𝓝 ζ) ∧ Tendsto (f ∘ z) atTop (𝓝 ω)}

/-- **Definition** (§2.5). The radius `[0, ζ) = {rζ : 0 ≤ r < 1}`. -/
def radius (ζ : ℂ) : Set ℂ :=
  {z | ∃ r ∈ Ico (0 : ℝ) 1, z = r * ζ}

/-- **Definition** (§2.5). `f` has the radial limit `a` at `ζ ∈ 𝕋`: `f(rζ) → a` as `r → 1-`. -/
def HasRadialLimit (f : ℂ → ExtPlane) (ζ : ℂ) (a : ExtPlane) : Prop :=
  Tendsto (fun r : ℝ => f (r * ζ)) (𝓝[<] 1) (𝓝 a)

/-- A curve `Γ` in `𝔻` ending at `ζ` (§1.1.4, as used in §2.5): the point set of a half-open curve in `𝔻` ending at
`ζ`. -/
def IsCurveEndingAt (Γ : Set ℂ) (ζ : ℂ) : Prop :=
  ∃ C : HalfOpenCurve, C.toFun '' Ico C.α C.β ⊆ unitDisc ∧ C.EndsAt ζ ∧ Γ = C.toFun '' Ico C.α C.β

/-- **Theorem 2.16** (§2.5; Carathéodory, Lindelöf). Let `f` map `𝔻` conformally onto `G ⊆ Ĉ`. If `ζ ∈ 𝕋`, then
(2.5.5) `I(f̂(ζ)) = C(f, ζ)` and (2.5.6) `Π(f̂(ζ)) = ⋂_Γ C_Γ(f, ζ) = C_{[0,ζ)}(f, ζ) = C_Δ(f, ζ)`, where `Γ` runs
through all curves in `𝔻` ending at `ζ` and where `Δ` is any Stolz angle at `ζ`. -/
theorem thm2_16 {G : Set ExtPlane} {f : ExtPlane → ExtPlane} (hf : IsConformalMap f (toExt unitDisc))
    (hfG : f '' toExt unitDisc = G) {fhat : ℂ → Set (ℕ → Set ExtPlane)} (hfhat : IsPrimeEndCorrespondence G f fhat)
    {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) :
    impression G (fhat ζ) = clusterSet (fun z : ℂ => f z) ζ ∧
      principalPoints (fhat ζ) = ⋂ Γ ∈ {Γ : Set ℂ | IsCurveEndingAt Γ ζ}, clusterSetAlong (fun z : ℂ => f z) Γ ζ ∧
      principalPoints (fhat ζ) = clusterSetAlong (fun z : ℂ => f z) (radius ζ) ζ ∧
      ∀ α ρ : ℝ, 0 < α → α < π / 2 → 0 < ρ → ρ < 2 * Real.cos α →
        principalPoints (fhat ζ) = clusterSetAlong (fun z : ℂ => f z) (stolzAngleP ζ α ρ) ζ := by
  sorry

/-- **Corollary 2.17** (§2.5), part (i). If `f` maps `𝔻` conformally onto `G ⊆ Ĉ`, then: `f` has the angular limit
`a` at `ζ` ⇔ `f` has the radial limit `a` at `ζ` ⇔ `f` has the limit `a` along some curve ending at `ζ` ⇔
`Π(f̂(ζ)) = {a}`. -/
theorem cor2_17_i {G : Set ExtPlane} {f : ExtPlane → ExtPlane} (hf : IsConformalMap f (toExt unitDisc))
    (hfG : f '' toExt unitDisc = G) {fhat : ℂ → Set (ℕ → Set ExtPlane)} (hfhat : IsPrimeEndCorrespondence G f fhat)
    {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) (a : ExtPlane) :
    List.TFAE
      [HasAngularLimit (fun z : ℂ => f z) ζ a,
        HasRadialLimit (fun z : ℂ => f z) ζ a,
        ∃ C : HalfOpenCurve, C.toFun '' Ico C.α C.β ⊆ unitDisc ∧ C.EndsAt ζ ∧
          Tendsto (fun t => f (C.toFun t)) (𝓝[<] C.β) (𝓝 a),
        principalPoints (fhat ζ) = {a}] := by
  sorry

/-- **Corollary 2.17** (§2.5), part (ii). `f` has the unrestricted limit `a` at `ζ` ⇔ `I(f̂(ζ)) = {a}`. -/
theorem cor2_17_ii {G : Set ExtPlane} {f : ExtPlane → ExtPlane} (hf : IsConformalMap f (toExt unitDisc))
    (hfG : f '' toExt unitDisc = G) {fhat : ℂ → Set (ℕ → Set ExtPlane)} (hfhat : IsPrimeEndCorrespondence G f fhat)
    {ζ : ℂ} (hζ : ζ ∈ sphere (0 : ℂ) 1) (a : ExtPlane) :
    HasUnrestrictedLimit (fun z : ℂ => f z) ζ a ↔ impression G (fhat ζ) = {a} := by
  sorry

end Pommerenke1992
