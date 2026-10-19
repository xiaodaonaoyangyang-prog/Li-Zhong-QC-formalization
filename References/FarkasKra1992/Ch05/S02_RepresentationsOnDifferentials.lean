import References.FarkasKra1992.Ch05.S01b_WeierstrassPointsAndAutomorphisms
import References.FarkasKra1992.Ch02.S05_MeromorphicFunctionsAndDifferentials

/-!
# Farkas–Kra, Chapter V §2: Representations of the automorphism group on spaces of differentials

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. V §2 (`full.md` FK2:3784–4595).

Conventions: as in `Ch05/S01_HurwitzTheorem` and `Ch05/S01b_WeierstrassPointsAndAutomorphisms`: `M` is a compact Riemann
surface of genus `g` (`LiZhongQC.HasGenus M g`), `Aut M` is the set of `T : M ≃ₜ M` with `LiZhongQC.IsBiholomorphic (T : M → M)`,
`ν(T)` is `fixedPointCount T`, the quotient `M/H` and its genus are `IsQuotientGenus H γ`, the set of Weierstrass points is
`weierstrassSet M g`. A `q`-differential is a family of coefficients `c x : ℂ → ℂ` in the preferred chart at each point
(`LiZhongQC.IsDiffFamily`, `IsMeroQDiff`, `ordQDiff`, Ch. II §5.2); `ℋ^q(M)` is the span of the holomorphic ones (`holQDiffSpan`). The action
`Tφ = φ ∘ T⁻¹` is the relation `IsQDiffPushforward q T φ (Tφ)` (the transformation law of `q`-differentials under `T⁻¹`).

* V.2.1 (holomorphic `q`-differential, the graded algebra) — exists: `FarkasKra1992.IsHolQDiff`, `FarkasKra1992.holQDiffSpan`
* V.2.1 (the action `Tφ = φ ∘ T⁻¹`) — `IsQDiffPushforward`
* V.2.1, property (b) and (d) — `prop5_2_1_a`
* V.2.1, property (a) — `prop5_2_1_b`
* V.2.1, property (b) (linearity) — `prop5_2_1_c`
* V.2.1, property (c) — `prop5_2_1_d`
* Proposition V.2.1 (the representation is faithful for `q ≥ 1`) — `IsHyperellipticInvolution`, `prop5_2_1_e`
* V.2.2 (`G`-invariant `q`-differentials) — `invHolQDiffSpace`, `stabilizerCard`, `IsQDiffPushforwardGerm`, `IsQDiffLift`
* Proposition V.2.2 (2.2.2) — `prop5_2_2`
* Corollary V.2.2 (2.2.3) — `cor5_2_2_a`
* Corollary V.2.2 (2.2.4) — `cor5_2_2_b`
* Proposition V.2.3 (`T` is diagonalizable) — `prop5_2_3`
* V.2.4 (eigenspaces of a fixed point free `⟨T⟩`) — `eigenQDiffSpace`, `prop5_2_4_a`, `prop5_2_4_b`, `prop5_2_4_c`
* V.2.5–V.2.8 (derivation of the eigenspace dimensions and of the trace formula) — omitted: U− (intermediate computations; the result is V.2.9)
* Theorem V.2.9 (Eichler trace formula) — `HasFixedPointRotations`, `thm5_2_9_a`, `thm5_2_9_b`
* Corollary V.2.9 (Lefschetz fixed point formula) — `cor5_2_9`
* Theorem V.2.10 — `thm5_2_10`
* Theorem V.2.11 — `thm5_2_11`
* III.5.9 (`q`-Weierstrass point) — `IsQWeierstrass`
* Theorem V.2.12 — `thm5_2_12`
* Corollary V.2.12 — `cor5_2_12`
* Theorem V.2.13, part 1 (involutions) — `thm5_2_13_a`
* Theorem V.2.13, part 2 (prime order) — `thm5_2_13_b`
* Corollary V.2.13 — `cor5_2_13`
* Proposition V.2.14 — `prop5_2_14`

Omitted (U−): the Remark after Corollary V.2.2 (`dim ℋ²_G = 3g̃ − 3 + n`, a special case of (2.2.4)), the Remark after V.2.3, the
Remarks after V.2.9, V.2.11, V.2.13, the description of the matrix of `T` in V.2.10 and V.2.12.
**Readings:** (i) in V.2.4 `⟨T⟩` is assumed to act fixed point freely: `T^k` has no fixed point for `0 < k < n`; (ii) the group
`G` of V.2.2 is finite and consists of automorphisms (it is a subgroup of the finite `Aut M`, `g ≥ 2`).
-/

open scoped Manifold ContDiff Topology References ComplexConjugate
open Set Filter

noncomputable section

namespace FarkasKra1992

open LiZhongQC (IsBiholomorphic HasGenus)

section Defs

variable {M N : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
  [TopologicalSpace N] [ChartedSpace ℂ N]

/-- **The action of an automorphism on `q`-differentials** (Ch. V §2.1). `c'` represents `Tφ = φ ∘ T⁻¹` for `c` representing `φ`:
`c'` vanishes off the chart targets (as a coefficient family, `LiZhongQC.IsDiffFamily`), and in the preferred chart at `x`, for
`z` in its target, with the moving point `p = T⁻¹(φ_x⁻¹ z)` and `ψ = (chart at p) ∘ T⁻¹ ∘ (chart at x)⁻¹` (defined near `z`),
`c' x z = c p (φ_p p) · ψ'(z)^q`. [CORRECTION, FK-fix2] The chart is taken at the moving point `p`, as in
`Forster1981.Form1.pullback`; the earlier chart at `T⁻¹x` does not contain `T⁻¹(φ_x⁻¹ z)` in general (AUDIT5_FK F3). -/
def IsQDiffPushforward (q : ℕ) (T : M ≃ₜ M) (c c' : M → ℂ → ℂ) : Prop :=
  (∀ x z, z ∉ (chartAt ℂ x).target → c' x z = 0) ∧
    ∀ x, ∀ z ∈ (chartAt ℂ x).target,
      c' x z = c (T.symm ((chartAt ℂ x).symm z))
          (chartAt ℂ (T.symm ((chartAt ℂ x).symm z)) (T.symm ((chartAt ℂ x).symm z))) *
        (deriv (fun u => chartAt ℂ (T.symm ((chartAt ℂ x).symm z)) (T.symm ((chartAt ℂ x).symm u))) z) ^ q

/-- **Hyperelliptic involution** (Ch. V §2.1, Ch. V §1.2). A non-trivial automorphism `J` with `π ∘ J = π` for a holomorphic
double covering `π : M → ℂ̂`. -/
def IsHyperellipticInvolution (J : M ≃ₜ M) : Prop :=
  J ≠ 1 ∧ IsBiholomorphic (J : M → M) ∧
    ∃ π : M → References.RiemannSphere, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π ∧ Forster1981.IsHolomorphicCovering π 2 ∧ ∀ x, π (J x) = π x

/-- **The number `ν(P) = ord G_P`** (Ch. V §2.2). The order of the isotropy group of `P` in the group `G` of automorphisms. -/
def stabilizerCard (G : Subgroup (M ≃ₜ M)) (P : M) : ℕ := Nat.card {h : G // (h : M ≃ₜ M) P = P}

/-- **The `G`-invariant holomorphic `q`-differentials `ℋ^q_G(M)`** (Ch. V §2.2): `Tφ = φ` for all `T ∈ G`. -/
def invHolQDiffSpace (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] (q : ℕ) (G : Subgroup (M ≃ₜ M)) : Submodule ℂ (M → ℂ → ℂ) :=
  Submodule.span ℂ {c | IsHolQDiff q c ∧ ∀ h ∈ G, IsQDiffPushforward q h c c}

/-- **Germ form of the action** (Ch. V §2.2, helper for `prop5_2_2`). Like `IsQDiffPushforward`, but the relation
`c' x u = c(p) · ψ'(u)^q` (`p = T⁻¹(φ_x⁻¹ u)`, `ψ = (chart at p) ∘ T⁻¹ ∘ (chart at x)⁻¹`) is required on a punctured
neighbourhood of every point `z` of the chart target, so the values of `c, c'` at isolated points (poles, removable points,
branch points of a quotient map) are not read. Equivalent to `IsQDiffPushforward` for holomorphic `c, c'`. -/
def IsQDiffPushforwardGerm (q : ℕ) (T : M ≃ₜ M) (c c' : M → ℂ → ℂ) : Prop :=
  (∀ x z, z ∉ (chartAt ℂ x).target → c' x z = 0) ∧
    ∀ x, ∀ z ∈ (chartAt ℂ x).target, ∀ᶠ u in 𝓝[≠] z,
      c' x u = c (T.symm ((chartAt ℂ x).symm u))
          (chartAt ℂ (T.symm ((chartAt ℂ x).symm u)) (T.symm ((chartAt ℂ x).symm u))) *
        (deriv (fun v => chartAt ℂ (T.symm ((chartAt ℂ x).symm u)) (T.symm ((chartAt ℂ x).symm v))) u) ^ q
/-- **Lift of a `q`-differential** (Ch. V §2.2, III.4.12). `c` is the lift to `M` under the holomorphic map `π : M → N` of the
`q`-differential `c̃` on `N`: `c` vanishes off the chart targets, and in the preferred chart at `x`, for `u` near a point `z` of its
target (`u ≠ z`), with the moving point `p = π(φ_x⁻¹ u)` and `ψ = (chart at p) ∘ π ∘ (chart at x)⁻¹` (defined near `u`),
`c x u = c̃ p (φ_p p) · ψ'(u)^q`.
[CORRECTION, FK-fix2] Off-target clause added and the chart taken at the moving point (AUDIT5_FK F2, F3).
[CORRECTION, FK-fix3] The relation is an equality of germs on punctured neighbourhoods. At a ramification point `ψ' = 0`, so the
pointwise relation forced `c = 0` there, while a genuine lift can have a non-zero coefficient (`(dx/y)²` at a Weierstrass point of a
genus 2 surface, `q = 2`; AUDITR2_FK R2FK-1). -/
def IsQDiffLift (q : ℕ) (π : M → N) (ct : N → ℂ → ℂ) (c : M → ℂ → ℂ) : Prop :=
  (∀ x z, z ∉ (chartAt ℂ x).target → c x z = 0) ∧
    ∀ x, ∀ z ∈ (chartAt ℂ x).target, ∀ᶠ u in 𝓝[≠] z,
      c x u = ct (π ((chartAt ℂ x).symm u)) (chartAt ℂ (π ((chartAt ℂ x).symm u)) (π ((chartAt ℂ x).symm u))) *
        (deriv (fun v => chartAt ℂ (π ((chartAt ℂ x).symm u)) (π ((chartAt ℂ x).symm v))) u) ^ q
/-- **The eigenspace `E_λ`** (Ch. V §2.4): the holomorphic `q`-differentials with `Tφ = λφ`. -/
def eigenQDiffSpace (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] (q : ℕ) (T : M ≃ₜ M) (lam : ℂ) : Submodule ℂ (M → ℂ → ℂ) :=
  Submodule.span ℂ {c | IsHolQDiff q c ∧ IsQDiffPushforward q T c (lam • c)}

/-- **`q`-Weierstrass point** (Ch. III §5.9, used in Ch. V §2.12). `P` is a `q`-Weierstrass point if its weight with respect to
`ℋ^q(M)` is positive, i.e. the orders `ord_P φ`, `0 ≠ φ ∈ ℋ^q(M)` (which take `d = dim ℋ^q(M)` distinct values) are not
`0, 1, …, d − 1`. -/
def IsQWeierstrass (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] (q : ℕ) (P : M) : Prop :=
  ¬ ∀ k : ℕ, k < dimHolQ M q → ∃ c, IsHolQDiff q c ∧ ordQDiff c P = (k : ℤ)

/-- **Local rotations at the fixed points** (Ch. V §2.9). The fixed points of `T` (of order `n`) are `P_1, …, P_t`, and for each
`m` there is a local coordinate `z = e_m` vanishing at `P_m` and an integer `ν_m`, `1 ≤ ν_m ≤ n − 1`, such that `T⁻¹` is
`z ↦ ε^{ν_m} z` near `P_m`, `ε = exp(2πi/n)`. -/
def HasFixedPointRotations (T : M ≃ₜ M) (t : ℕ) (P : Fin t → M) (e : Fin t → OpenPartialHomeomorph M ℂ)
    (ν : Fin t → ℕ) : Prop :=
  Function.Injective P ∧ {x : M | T x = x} = Set.range P ∧
    ∀ m, e m ∈ (contDiffGroupoid ω 𝓘(ℂ)).maximalAtlas M ∧ P m ∈ (e m).source ∧ e m (P m) = 0 ∧ 1 ≤ ν m ∧
      ν m + 1 ≤ orderOf T ∧
      ∀ᶠ x in 𝓝 (P m), e m (T.symm x) = Complex.exp (2 * Real.pi * Complex.I / (orderOf T : ℂ)) ^ ν m * e m x

end Defs

variable {M N : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **V.2.1, properties (b) and (d)** (Ch. V §2.1). For `T ∈ Aut M` and a holomorphic `q`-differential `φ`, the differential
`Tφ` exists, is a holomorphic `q`-differential, and `ord_{TP} Tφ = ord_P φ`. -/
theorem prop5_2_1_a {q : ℕ} (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M)) {c : M → ℂ → ℂ} (hc : IsHolQDiff q c) :
    ∃ c', IsQDiffPushforward q T c c' ∧ IsHolQDiff q c' ∧ ∀ P, ordQDiff c' (T P) = ordQDiff c P := by
  sorry

/-- **V.2.1, property (a)** (Ch. V §2.1). `(T₁ ∘ T₂)φ = T₁(T₂φ)` for `T₁, T₂ ∈ Aut M`.
Modelling: `T₁, T₂` are biholomorphic (as in the book, where `T ∈ Aut M`); `IsQDiffPushforward` uses `deriv` of the chart expression of `T`,
which is junk `0` where it is not differentiable, so the chain rule (and this statement) can fail for an arbitrary homeomorphism. -/
theorem prop5_2_1_b {q : ℕ} (T₁ T₂ : M ≃ₜ M) (hT₁ : IsBiholomorphic (T₁ : M → M)) (hT₂ : IsBiholomorphic (T₂ : M → M))
    {c c₁ c₂ : M → ℂ → ℂ} (h₂ : IsQDiffPushforward q T₂ c c₁)
    (h₁ : IsQDiffPushforward q T₁ c₁ c₂) : IsQDiffPushforward q (T₁ * T₂) c c₂ := by
  sorry

/-- **V.2.1, property (b)** (Ch. V §2.1). The action of `T` is `ℂ`-linear: if `Tφ₁ = φ₁'`, `Tφ₂ = φ₂'`, then
`T(aφ₁ + bφ₂) = aφ₁' + bφ₂'`. -/
theorem prop5_2_1_c {q : ℕ} (T : M ≃ₜ M) {c₁ c₂ c₁' c₂' : M → ℂ → ℂ} (h₁ : IsQDiffPushforward q T c₁ c₁')
    (h₂ : IsQDiffPushforward q T c₂ c₂') (a b : ℂ) :
    IsQDiffPushforward q T (a • c₁ + b • c₂) (a • c₁' + b • c₂') := by
  sorry

/-- **V.2.1, property (c)** (Ch. V §2.1). `T(φ₁φ₂) = (Tφ₁)(Tφ₂)` for `φ_j` of degree `q_j`: the product is a `(q₁ + q₂)`-differential. -/
theorem prop5_2_1_d {q₁ q₂ : ℕ} (T : M ≃ₜ M) {c₁ c₂ c₁' c₂' : M → ℂ → ℂ} (h₁ : IsQDiffPushforward q₁ T c₁ c₁')
    (h₂ : IsQDiffPushforward q₂ T c₂ c₂') :
    IsQDiffPushforward (q₁ + q₂) T (fun x z => c₁ x z * c₂ x z) (fun x z => c₁' x z * c₂' x z) := by
  sorry

/-- **Proposition V.2.1** (Ch. V §2.1). Let `g ≥ 2`. For `q ≥ 1` the representation of `Aut M` on `ℋ^q(M)` is faithful, except for
`g = 2 = q`, in which case the kernel is precisely `⟨J⟩`, `J` the hyperelliptic involution: `T` acts as the identity on
`ℋ^q(M)` if and only if `T = 1` or (`g = q = 2` and `T = J`). -/
theorem prop5_2_1_e {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) {q : ℕ} (hq : 1 ≤ q) (T : M ≃ₜ M)
    (hT : IsBiholomorphic (T : M → M)) :
    (∀ c, IsHolQDiff q c → IsQDiffPushforward q T c c) ↔ T = 1 ∨ (g = 2 ∧ q = 2 ∧ IsHyperellipticInvolution T) := by
  sorry

/-- **Proposition V.2.2** (Ch. V §2.2, (2.2.2)). Let `G` be a finite group of automorphisms and `π : M → N = M/G` the projection.
The lifts of `q`-differentials on `N` are the `G`-invariant `q`-differentials on `M`, every `G`-invariant meromorphic
`q`-differential is such a lift, `ord_P φ = ν(P) ord_{π(P)} φ̃ + q(ν(P) − 1)`, and hence `φ` is holomorphic iff
`ord_{π(P)} φ̃ ≥ −[q(1 − 1/ν(P))]` for all `P`, which is `ℋ^q_G(M) ≅ ℋ^q(M̃; Z^{(q)})`.
Modelling (FK-fix2): `N = M/G` carries the Riemann-surface binders (the orders `ord_{π(P)} φ̃` are read in its charts).
[CORRECTION, FK-fix3] Lifts and invariance are read as equalities of germs on punctured neighbourhoods (`IsQDiffLift`,
`IsQDiffPushforwardGerm`), so the values at the isolated branch points are free; `c` is a meromorphic `q`-differential
(`IsMeroQDiff`) in the first and third parts, and "holomorphic" is `0 ≤ ord_P c` for all `P` (for a meromorphic `q`-differential this
is `IsHolQDiff` after correcting the values at removable points; AUDITR2_FK R2FK-1). -/
theorem prop5_2_2 [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N] {q : ℕ}
    (G : Subgroup (M ≃ₜ M)) (hG : (G : Set (M ≃ₜ M)).Finite)
    (hGa : ∀ h ∈ G, IsBiholomorphic (h : M → M)) {π : M → N}
    (hπ : IsRelProjection π fun x y => ∃ h ∈ G, h x = y) :
    (∀ ct c, IsMeroQDiff (q : ℤ) ct → IsMeroQDiff (q : ℤ) c → IsQDiffLift q π ct c →
      (∀ h ∈ G, IsQDiffPushforwardGerm q h c c) ∧
        ∀ P, (ordQDiff ct (π P) = ⊤ ↔ ordQDiff c P = ⊤) ∧
          ∀ k : ℤ, ordQDiff ct (π P) = k → ordQDiff c P = ((stabilizerCard G P : ℤ) * k + q * (stabilizerCard G P - 1) : ℤ)) ∧
    (∀ c, IsMeroQDiff (q : ℤ) c → (∀ h ∈ G, IsQDiffPushforwardGerm q h c c) →
      ∃ ct, IsMeroQDiff (q : ℤ) ct ∧ IsQDiffLift q π ct c) ∧
    (∀ ct c, IsMeroQDiff (q : ℤ) ct → IsMeroQDiff (q : ℤ) c → IsQDiffLift q π ct c →
      ((∀ P, 0 ≤ ordQDiff c P) ↔ ∀ P, ∀ k : ℤ, ordQDiff ct (π P) = k →
        -((q * (stabilizerCard G P - 1) / stabilizerCard G P : ℕ) : ℤ) ≤ k)) := by
  sorry
/-- **Corollary V.2.2, part 1** (Ch. V §2.2, (2.2.3)). Let `g̃` be the genus of `M̃ = M/G`. Then `dim ℋ¹_G(M) = g̃`. -/
theorem cor5_2_2_a {g g' : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (G : Subgroup (M ≃ₜ M))
    (hGa : ∀ h ∈ G, IsBiholomorphic (h : M → M)) (hG : IsQuotientGenus G g') :
    Module.finrank ℂ (invHolQDiffSpace M 1 G) = g' := by
  sorry

/-- **Corollary V.2.2, part 2** (Ch. V §2.2, (2.2.4)). For `q ≥ 2`,
`dim ℋ^q_G(M) = (2q − 1)(g̃ − 1) + Σ_{P̃ ∈ M̃} [q(1 − 1/ν(P̃))]`.
Modelling: the sum over `M̃` is the sum over `P ∈ M` of `[q(1 − 1/ν(P))] · ν(P)/|G|` (the orbit of `P` has `|G|/ν(P)` points). -/
theorem cor5_2_2_b {g g' : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (G : Subgroup (M ≃ₜ M))
    (hGa : ∀ h ∈ G, IsBiholomorphic (h : M → M)) (hG : IsQuotientGenus G g') {q : ℕ} (hq : 2 ≤ q) :
    (Module.finrank ℂ (invHolQDiffSpace M q G) : ℚ) = (2 * q - 1) * ((g' : ℚ) - 1) +
      (∑ᶠ P : M, ((q * (stabilizerCard G P - 1) / stabilizerCard G P : ℕ) : ℚ) * stabilizerCard G P) / Nat.card G := by
  sorry

/-- **Proposition V.2.3** (Ch. V §2.3). There is a basis of `ℋ^q(M)` (`q ≥ 1`) such that the action of `T` is represented by a
diagonal matrix, whose entries are `n`-th roots of unity, `n = ord T`. -/
theorem prop5_2_3 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) {q : ℕ} (hq : 1 ≤ q) (T : M ≃ₜ M)
    (hT : IsBiholomorphic (T : M → M)) :
    ∃ (d : ℕ) (b : Fin d → M → ℂ → ℂ), LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = holQDiffSpan M q ∧
      ∀ i, IsHolQDiff q (b i) ∧ ∃ lam : ℂ, lam ^ orderOf T = 1 ∧ IsQDiffPushforward q T (b i) (lam • b i) := by
  sorry

/-- **V.2.4, the eigenvalues** (Ch. V §2.4). Let `T ∈ Aut M` have order `n > 1` and let `⟨T⟩` act fixed point freely. Every
`n`-th root of unity is an eigenvalue of `T` on `ℋ^q(M)`, and there are no other eigenvalues (`E_λ = 0` if `λⁿ ≠ 1`). -/
theorem prop5_2_4_a {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) {q : ℕ} (hq : 1 ≤ q) (T : M ≃ₜ M)
    (hT : IsBiholomorphic (T : M → M)) (hn : 1 < orderOf T) (hfree : ∀ k, 0 < k → k < orderOf T → ∀ x, (T ^ k) x ≠ x)
    (lam : ℂ) : (lam ^ orderOf T = 1 → eigenQDiffSpace M q T lam ≠ ⊥) ∧ (lam ^ orderOf T ≠ 1 → eigenQDiffSpace M q T lam = ⊥) := by
  sorry

/-- **V.2.4, the multiplicities for `q > 1`** (Ch. V §2.4). In the situation of `prop5_2_4_a`, with `g̃` the genus of
`M/⟨T⟩`: for `q > 1` and `λⁿ = 1`, `dim E_λ = (2q − 1)(g̃ − 1)`. -/
theorem prop5_2_4_b {g g' : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) {q : ℕ} (hq : 2 ≤ q) (T : M ≃ₜ M)
    (hT : IsBiholomorphic (T : M → M)) (hn : 1 < orderOf T) (hfree : ∀ k, 0 < k → k < orderOf T → ∀ x, (T ^ k) x ≠ x)
    (hquot : IsQuotientGenus (Subgroup.zpowers T) g') {lam : ℂ} (hl : lam ^ orderOf T = 1) :
    Module.finrank ℂ (eigenQDiffSpace M q T lam) = (2 * q - 1) * (g' - 1) := by
  sorry

/-- **V.2.4, the multiplicities for `q = 1`** (Ch. V §2.4). In the situation of `prop5_2_4_a`: `dim E_1 = g̃`, and
`dim E_λ = g̃ − 1` for `λ ≠ 1`, `λⁿ = 1`. -/
theorem prop5_2_4_c {g g' : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (hn : 1 < orderOf T) (hfree : ∀ k, 0 < k → k < orderOf T → ∀ x, (T ^ k) x ≠ x)
    (hquot : IsQuotientGenus (Subgroup.zpowers T) g') {lam : ℂ} (hl : lam ^ orderOf T = 1) :
    Module.finrank ℂ (eigenQDiffSpace M 1 T lam) = if lam = 1 then g' else g' - 1 := by
  sorry

/-- **Theorem V.2.9, `q = 1`** (Eichler trace formula, Ch. V §2.9). Let `T` be an automorphism of order `n > 1` of a compact
surface of genus `g > 1`, with `t` fixed points `P_m` and local rotations `T⁻¹ : z ↦ ε^{ν_m} z` (`HasFixedPointRotations`). If
`ρ` is the linear map of `ℋ¹(M)` induced by `T`, then `tr ρ = 1 + Σ_m ε^{ν_m}/(1 − ε^{ν_m})` (the empty sum is `0`). -/
theorem thm5_2_9_a {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (hn : 1 < orderOf T) {t : ℕ} {P : Fin t → M} {e : Fin t → OpenPartialHomeomorph M ℂ} {ν : Fin t → ℕ}
    (hrot : HasFixedPointRotations T t P e ν) (ρ : holQDiffSpan M 1 →ₗ[ℂ] holQDiffSpan M 1)
    (hρ : ∀ φ : holQDiffSpan M 1, IsQDiffPushforward 1 T φ.1 (ρ φ).1) :
    LinearMap.trace ℂ (holQDiffSpan M 1) ρ =
      1 + ∑ m, Complex.exp (2 * Real.pi * Complex.I / (orderOf T : ℂ)) ^ ν m /
        (1 - Complex.exp (2 * Real.pi * Complex.I / (orderOf T : ℂ)) ^ ν m) := by
  sorry

/-- **Theorem V.2.9, `q > 1`** (Eichler trace formula, Ch. V §2.9). In the situation of `thm5_2_9_a`, for `q > 1`,
`tr ρ = Σ_m ε^{ν_m ν}/(1 − ε^{ν_m})`, where `0 < ν ≤ n` is the integer with `q = μn + ν`, `μ ∈ ℤ`. -/
theorem thm5_2_9_b {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) {q : ℕ} (hq : 2 ≤ q) (T : M ≃ₜ M)
    (hT : IsBiholomorphic (T : M → M)) (hn : 1 < orderOf T) {t : ℕ} {P : Fin t → M}
    {e : Fin t → OpenPartialHomeomorph M ℂ} {ν : Fin t → ℕ} (hrot : HasFixedPointRotations T t P e ν)
    (ρ : holQDiffSpan M q →ₗ[ℂ] holQDiffSpan M q) (hρ : ∀ φ : holQDiffSpan M q, IsQDiffPushforward q T φ.1 (ρ φ).1) :
    LinearMap.trace ℂ (holQDiffSpan M q) ρ =
      ∑ m, Complex.exp (2 * Real.pi * Complex.I / (orderOf T : ℂ)) ^ (ν m * ((q - 1) % orderOf T + 1)) /
        (1 - Complex.exp (2 * Real.pi * Complex.I / (orderOf T : ℂ)) ^ ν m) := by
  sorry

/-- **Corollary V.2.9** (Lefschetz fixed point formula, Ch. V §2.9). For `q = 1`, `tr T + conj (tr T) = 2 − t`, `t` the number of
fixed points of `T`. -/
theorem cor5_2_9 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (hn : 1 < orderOf T) {t : ℕ} {P : Fin t → M} {e : Fin t → OpenPartialHomeomorph M ℂ} {ν : Fin t → ℕ}
    (hrot : HasFixedPointRotations T t P e ν) (ρ : holQDiffSpan M 1 →ₗ[ℂ] holQDiffSpan M 1)
    (hρ : ∀ φ : holQDiffSpan M 1, IsQDiffPushforward 1 T φ.1 (ρ φ).1) :
    LinearMap.trace ℂ (holQDiffSpan M 1) ρ + conj (LinearMap.trace ℂ (holQDiffSpan M 1) ρ) = 2 - t := by
  sorry

/-- **Theorem V.2.10** (Ch. V §2.10). Let `T ∈ Aut M` be of prime order `n` and assume that `T` fixes a non-Weierstrass point.
Then `2 ≤ ν(T) ≤ 4`, the genus `g̃` of `M/⟨T⟩` is `[g/n]`, and, with `g = g̃n + r` (`0 ≤ r ≤ n − 1`), exactly one of:
(a) `r = 0`, `ν(T) = 2`; (b) `r = (n − 1)/2`, i.e. `2g + 1 = (2g̃ + 1)n`, `ν(T) = 3`; (c) `r = n − 1`, i.e. `g + 1 = (g̃ + 1)n`,
`ν(T) = 4`. -/
theorem thm5_2_10 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (hp : (orderOf T).Prime) (hfix : ∃ P, T P = P ∧ P ∉ weierstrassSet M g) :
    2 ≤ fixedPointCount T ∧ fixedPointCount T ≤ 4 ∧
      ∃ g', IsQuotientGenus (Subgroup.zpowers T) g' ∧ g' = g / orderOf T ∧
        ((g = g' * orderOf T ∧ fixedPointCount T = 2) ∨
          (2 * g + 1 = (2 * g' + 1) * orderOf T ∧ fixedPointCount T = 3) ∨
          (g + 1 = (g' + 1) * orderOf T ∧ fixedPointCount T = 4)) := by
  sorry

/-- **Theorem V.2.11** (Ch. V §2.11). Let `T ∈ Aut M` be of prime order `n`. If `T` has a fixed point, it has at least two. -/
theorem thm5_2_11 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (hp : (orderOf T).Prime) (hfix : ∃ P, T P = P) : 2 ≤ fixedPointCount T := by
  sorry

/-- **Theorem V.2.12** (Ch. V §2.12). Let `T ∈ Aut M` be of prime order `n` with `ν(T) > 2`. Then every fixed point of `T` is a
`q`-Weierstrass point for every `q > 1`, `q ≡ 1 mod n`. -/
theorem thm5_2_12 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (hp : (orderOf T).Prime) (hv : 2 < fixedPointCount T) :
    ∀ x, T x = x → ∀ q : ℕ, 1 < q → q % orderOf T = 1 → IsQWeierstrass M q x := by
  sorry

/-- **Corollary V.2.12** (Ch. V §2.12). Let `1 ≠ T ∈ Aut M`. If `ν(T) > 2`, then every fixed point of `T` is a `q`-Weierstrass
point for some `q`. -/
theorem cor5_2_12 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M)) (h1 : T ≠ 1)
    (hv : 2 < fixedPointCount T) : ∀ x, T x = x → ∃ q : ℕ, 1 < q ∧ IsQWeierstrass M q x := by
  sorry

/-- **Theorem V.2.13, part 1** (Ch. V §2.13). Let `M` be hyperelliptic of genus `g ≥ 2`. A conformal involution of `M` has only
non-Weierstrass fixed points (possibly none), or is the hyperelliptic involution `J`. -/
theorem thm5_2_13_a {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (hh : Forster1981.IsHyperelliptic M) (T : M ≃ₜ M)
    (hT : IsBiholomorphic (T : M → M)) (h1 : T ≠ 1) (hinv : T * T = 1) :
    (∀ x, T x = x → x ∉ weierstrassSet M g) ∨ IsHyperellipticInvolution T := by
  sorry

/-- **Theorem V.2.13, part 2** (Ch. V §2.13). Let `M` be hyperelliptic of genus `g ≥ 2` and `T` an automorphism of prime order `n`,
`2 < n < 2g`, that fixes a Weierstrass point `P₀`; let `g̃` be the genus of `M/⟨T⟩`. Then either (a) `g = g̃n`, `ν(T) = 2`, and
both fixed points are Weierstrass points; or (b) `n(2g̃ + 1) = 2g + 1` (`g̃ ≥ 1`), `ν(T) = 3`, and the other fixed points are `P`
and `J(P)`, with `P` not a Weierstrass point. -/
theorem thm5_2_13_b {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (hh : Forster1981.IsHyperelliptic M) (T : M ≃ₜ M)
    (hT : IsBiholomorphic (T : M → M)) (hp : (orderOf T).Prime) (h2 : 2 < orderOf T) (h2g : orderOf T < 2 * g)
    {P₀ : M} (hP₀ : T P₀ = P₀) (hW : P₀ ∈ weierstrassSet M g) :
    ∃ g', IsQuotientGenus (Subgroup.zpowers T) g' ∧
      ((g = g' * orderOf T ∧ fixedPointCount T = 2 ∧ ∀ x, T x = x → x ∈ weierstrassSet M g) ∨
        (1 ≤ g' ∧ orderOf T * (2 * g' + 1) = 2 * g + 1 ∧ fixedPointCount T = 3 ∧
          ∃ (J : M ≃ₜ M) (P : M), IsHyperellipticInvolution J ∧ P ∉ weierstrassSet M g ∧ J P ≠ P ∧
            {x : M | T x = x} = {P₀, P, J P})) := by
  sorry

/-- **Corollary V.2.13** (Ch. V §2.13). If `1 ≠ T ∈ Aut M` fixes a Weierstrass point on the hyperelliptic surface `M` of genus
`g ≥ 2`, and `ord T` is prime and `< 2g`, then `ord T ≤ g`. -/
theorem cor5_2_13 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (hh : Forster1981.IsHyperelliptic M) (T : M ≃ₜ M)
    (hT : IsBiholomorphic (T : M → M)) (h1 : T ≠ 1) (hp : (orderOf T).Prime) (h2g : orderOf T < 2 * g)
    (hfix : ∃ P ∈ weierstrassSet M g, T P = P) : orderOf T ≤ g := by
  sorry

/-- **Proposition V.2.14** (Ch. V §2.14). If `T ∈ Aut M` is of prime order `n > g`, then `n = g + 1` or `n = 2g + 1`, and in both
cases `M/⟨T⟩` has genus `0`; for `n = g + 1`, `ν(T) = 4`, and for `n = 2g + 1`, `ν(T) = 3`. -/
theorem prop5_2_14 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (hp : (orderOf T).Prime) (hn : g < orderOf T) :
    (orderOf T = g + 1 ∨ orderOf T = 2 * g + 1) ∧ IsQuotientGenus (Subgroup.zpowers T) 0 ∧
      (orderOf T = g + 1 → fixedPointCount T = 4) ∧ (orderOf T = 2 * g + 1 → fixedPointCount T = 3) := by
  sorry

end FarkasKra1992
