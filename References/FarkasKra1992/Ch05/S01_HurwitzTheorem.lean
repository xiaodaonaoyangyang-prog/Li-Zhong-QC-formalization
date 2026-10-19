import References.FarkasKra1992.Ch04.S09_DiscontinuousGroups
import References.Forster1981.Ch01.S04_BranchedAndUnbranchedCoverings

/-!
# Farkas–Kra, Chapter V §1: Hurwitz's theorem

Source: H. M. Farkas, I. Kra, *Riemann Surfaces*, 2nd ed., GTM 71, Ch. V §1 (`full.md` FK2:3202–3783).

Conventions: `M` is a compact Riemann surface of genus `g` (`LiZhongQC.HasGenus M g`, which includes compactness), and
`Aut M` is the set of homeomorphisms `T : M ≃ₜ M` with `LiZhongQC.IsBiholomorphic T`. A meromorphic function
`f ∈ 𝒦(M) ∖ ℂ` of degree `n` is a holomorphic map `f : M → ℂ̂` with `Forster1981.IsHolomorphicCovering f n` (a non-constant
proper holomorphic map taking every value `n` times; `deg f = deg D` for `D = f⁻¹(∞)`). `ord T` is `orderOf T` and
`ν(T)` is `fixedPointCount T` (the number of fixed points, `Set.ncard`; it is finite for `T ≠ 1`, which is part of the
conclusions where it enters arithmetic). The quotient `M/H` by a group `H` of automorphisms and its genus are
expressed by `IsQuotientGenus H γ`. The hyperelliptic notion of FK is `IsGammaHyperelliptic M 0` (V.1.9).
Items that need Weierstrass points (V.1.2 Proposition and Corollary 1, V.1.7) wait for `Forster1981` Part B.

* Proposition V.1.1 — `fixedPointCount`, `prop5_1_1`
* Corollary V.1.2, part 2 (Schwarz) — exists: `LiZhongQC.hurwitz_finite`
* Theorem V.1.3 (Hurwitz) — exists: `LiZhongQC.hurwitz`
* Proposition V.1.4 — `prop5_1_4`
* Proposition V.1.5 — `IsQuotientGenus`, `prop5_1_5`
* Corollary V.1.5, part 1 — `cor5_1_5_a`
* V.1.5 Remark — `para5_1_5`
* Corollary V.1.5, part 2 — `cor5_1_5_b`
* Theorem V.1.8 (1.8.1) — `thm5_1_8_a`
* Theorem V.1.8 (1.8.2) — `thm5_1_8_b`
* Theorem V.1.8 (1.8.3) — `thm5_1_8_c`
* Theorem V.1.8 (1.8.4) — `thm5_1_8_d`
* V.1.9 (`γ`-hyperelliptic) — `IsGammaHyperelliptic`
* V.1.9 (the `γ`-hyperelliptic involution) — `para5_1_9`
* Theorem V.1.9 (1.9.1) — `thm5_1_9_a`
* Theorem V.1.9 (1.9.2) — `thm5_1_9_b`
* Theorem V.1.9 (1.9.3) — `thm5_1_9_c`
* Corollary V.1.9, part 1 — `cor5_1_9_a`
* Corollary V.1.9, part 2 — `cor5_1_9_b`
* Proposition V.1.10 (Accola) — `prop5_1_10`
* Corollary V.1.10 — `cor5_1_10`
* Theorem V.1.10 — `thm5_1_10`
* Proposition V.1.11 — `prop5_1_11`

Omitted (U−): the examples V.1.6 and the Exercises, Remarks after V.1.8, V.1.9 (Example), V.1.11.
Waiting for Forster Part B (Weierstrass points): V.1.2 Proposition, V.1.2 Corollary 1, V.1.7 Theorem.
**Reading (misprint):** V.1.11 prints "genus `g ≤ 2`"; the proof and the Remark use `g ≥ 2` (for tori the bound is false).
-/

open scoped Manifold ContDiff MatrixGroups Topology References
open Set Filter

noncomputable section

namespace FarkasKra1992

open LiZhongQC (IsBiholomorphic HasGenus)
open References (RiemannSphere)

variable {M : Type} [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]

/-- **Number of fixed points** `ν(T)` (Ch. V §1.4). The number of fixed points of the homeomorphism `T`.
Modelling: `Set.ncard`, with junk value `0` for an infinite set; in the statements where `ν(T)` enters arithmetic the
finiteness of the fixed point set is a conclusion. -/
def fixedPointCount (T : M ≃ₜ M) : ℕ := {x : M | T x = x}.ncard

/-- **The genus of a quotient** (Ch. V §1, helper). The quotient `M/H` of `M` by a group `H` of homeomorphisms is a
compact Riemann surface of genus `γ`: there is a holomorphic open surjection `π : M → N` onto a Riemann surface `N`
of genus `γ` whose fibres are the `H`-orbits. -/
def IsQuotientGenus (H : Subgroup (M ≃ₜ M)) (γ : ℕ) : Prop :=
  ∃ (N : Type) (_ : TopologicalSpace N) (_ : ChartedSpace ℂ N), References.IsRiemannSurface N ∧ HasGenus N γ ∧
    ∃ π : M → N, IsRelProjection π fun x y => ∃ h ∈ H, h x = y

/-- **`γ`-hyperelliptic** (Ch. V §1.9). A compact Riemann surface `M` is *`γ`-hyperelliptic* (`γ ∈ ℤ`, `γ ≥ 0`)
provided there is a compact Riemann surface `M̃` of genus `γ` and a holomorphic mapping of degree 2 `π : M → M̃`.
Near miss: `Forster1981.IsHyperelliptic` (Part B, pending install) is the case `γ = 0`; `IsGammaHyperelliptic M 0` is
FK's "hyperelliptic". -/
def IsGammaHyperelliptic (M : Type) [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] (γ : ℕ) : Prop :=
  CompactSpace M ∧ ∃ (N : Type) (_ : TopologicalSpace N) (_ : T2Space N) (_ : ConnectedSpace N)
    (_ : ChartedSpace ℂ N) (_ : IsManifold 𝓘(ℂ) ω N), HasGenus N γ ∧ ∃ π : M → N, Forster1981.IsHolomorphicCovering π 2

/-- **Proposition V.1.1** (Ch. V §1.1). If `1 ≠ T ∈ Aut M`, then `T` has at most `2g + 2` fixed points. -/
theorem prop5_1_1 {g : ℕ} (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M)) (h1 : T ≠ 1) :
    {x : M | T x = x}.Finite ∧ fixedPointCount T ≤ 2 * g + 2 := by
  sorry

/-- **Proposition V.1.4** (Ch. V §1.4). Let `f ∈ 𝒦(M) ∖ ℂ` and `1 ≠ T ∈ Aut M`. Assume that `ν(T) > 2 deg f`. Then
`f = f ∘ T` and `deg f` is a multiple of `ord T`. If in addition `deg f` is prime, then `ord T` is prime and
`M/⟨T⟩ ≅ ℂ ∪ {∞}`.
Modelling: `deg f = n` is `IsHolomorphicCovering f n`; the finiteness of the order of `T` (the Remark after the
proof) is a conclusion (`0 < orderOf T`); "`M/⟨T⟩ ≅ ℂ̂`" is the existence of an orbit projection `M → ℂ̂` for the
group `⟨T⟩`. -/
theorem prop5_1_4 [CompactSpace M] {f : M → RiemannSphere} {n : ℕ} (hf : Forster1981.IsHolomorphicCovering f n)
    (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M)) (h1 : T ≠ 1) (hv : 2 * n < fixedPointCount T) :
    f ∘ T = f ∧ 0 < orderOf T ∧ orderOf T ∣ n ∧
      (n.Prime → (orderOf T).Prime ∧
        ∃ π : M → RiemannSphere, IsRelProjection π fun x y => ∃ h ∈ Subgroup.zpowers T, h x = y) := by
  sorry

/-- **Proposition V.1.5** (Ch. V §1.5). Let `M` be a compact surface of genus `g ≥ 2`. For `1 ≠ T ∈ Aut M`,
`ν(T) ≤ 2 + 2g/(ord T − 1)`.
Modelling: the finiteness of the order of `T` and of the fixed point set are conclusions. -/
theorem prop5_1_5 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (h1 : T ≠ 1) :
    IsOfFinOrder T ∧ {x : M | T x = x}.Finite ∧
      (fixedPointCount T : ℚ) ≤ 2 + 2 * g / ((orderOf T : ℚ) - 1) := by
  sorry

/-- **Corollary V.1.5(a)** (Ch. V §1.5, Corollary 1). Let `g ≥ 2` and `1 ≠ T ∈ Aut M` of prime order `n = ord T`, and
`γ` the genus of `M/⟨T⟩`. Then `ν(T) = 2 + (2g − 2γn)/(n − 1)`. In this case, equality holds in (1.5.1) if and only
if `γ = 0`. -/
theorem cor5_1_5_a {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (h1 : T ≠ 1) (hp : (orderOf T).Prime) {γ : ℕ} (hγ : IsQuotientGenus (Subgroup.zpowers T) γ) :
    (fixedPointCount T : ℚ) = 2 + (2 * g - 2 * γ * orderOf T) / ((orderOf T : ℚ) - 1) ∧
      ((fixedPointCount T : ℚ) = 2 + 2 * g / ((orderOf T : ℚ) - 1) ↔ γ = 0) := by
  sorry

/-- **Unlabelled** (Ch. V §1.5, Remark after Corollary 1, FK2:3460). In general (even if `ord T` is not prime), if
equality holds in (1.5.1), then `γ = 0`. -/
theorem para5_1_5 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (h1 : T ≠ 1) {γ : ℕ} (hγ : IsQuotientGenus (Subgroup.zpowers T) γ)
    (heq : (fixedPointCount T : ℚ) = 2 + 2 * g / ((orderOf T : ℚ) - 1)) : γ = 0 := by
  sorry

/-- **Corollary V.1.5(b)** (Ch. V §1.5, Corollary 2). In general, `ν(T) ≤ 2g − 1` if `M` is not hyperelliptic
(`g ≥ 2`, `1 ≠ T ∈ Aut M`). -/
theorem cor5_1_5_b {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (hh : ¬ IsGammaHyperelliptic M 0) (T : M ≃ₜ M)
    (hT : IsBiholomorphic (T : M → M)) (h1 : T ≠ 1) : fixedPointCount T ≤ 2 * g - 1 := by
  sorry

/-- **Theorem V.1.8(a)** (Ch. V §1.8, (1.8.1)). Let `M` be a compact surface of genus `g ≥ 2` and `1 ≠ T̃ ∈ Aut M`
with `n = ord T̃` a prime; let `g̃` be the genus of `M̃ = M/⟨T̃⟩`. Suppose that `g > n² g̃ + (n − 1)²` and that there is
a `1 ≠ T ∈ Aut M` with `ν(T) > 2n(g̃ + 1)`. Then each fixed point of `T̃` is a fixed point of `T` and
`ord T ≤ ord T̃ = n`. -/
theorem thm5_1_8_a {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (Tt : M ≃ₜ M) (hTt : IsBiholomorphic (Tt : M → M))
    (h1 : Tt ≠ 1) (hn : (orderOf Tt).Prime) {gt : ℕ} (hgt : IsQuotientGenus (Subgroup.zpowers Tt) gt)
    (hbig : g > orderOf Tt ^ 2 * gt + (orderOf Tt - 1) ^ 2) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (hT1 : T ≠ 1) (hv : 2 * orderOf Tt * (gt + 1) < fixedPointCount T) :
    (∀ x, Tt x = x → T x = x) ∧ orderOf T ≤ orderOf Tt := by
  sorry

/-- **Theorem V.1.8(b)** (Ch. V §1.8, (1.8.2)). In the situation of `thm5_1_8_a`: if `ord T = n`, then
`T ∈ ⟨T̃⟩`. -/
theorem thm5_1_8_b {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (Tt : M ≃ₜ M) (hTt : IsBiholomorphic (Tt : M → M))
    (h1 : Tt ≠ 1) (hn : (orderOf Tt).Prime) {gt : ℕ} (hgt : IsQuotientGenus (Subgroup.zpowers Tt) gt)
    (hbig : g > orderOf Tt ^ 2 * gt + (orderOf Tt - 1) ^ 2) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (hT1 : T ≠ 1) (hv : 2 * orderOf Tt * (gt + 1) < fixedPointCount T) (hord : orderOf T = orderOf Tt) :
    T ∈ Subgroup.zpowers Tt := by
  sorry

/-- **Theorem V.1.8(c)** (Ch. V §1.8, (1.8.3)). In the situation of `thm5_1_8_a`: `⟨T̃⟩` is a normal subgroup of
`Aut M`: for every `B ∈ Aut M`, `B⁻¹ T̃ B ∈ ⟨T̃⟩`. -/
theorem thm5_1_8_c {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (Tt : M ≃ₜ M) (hTt : IsBiholomorphic (Tt : M → M))
    (h1 : Tt ≠ 1) (hn : (orderOf Tt).Prime) {gt : ℕ} (hgt : IsQuotientGenus (Subgroup.zpowers Tt) gt)
    (hbig : g > orderOf Tt ^ 2 * gt + (orderOf Tt - 1) ^ 2) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (hT1 : T ≠ 1) (hv : 2 * orderOf Tt * (gt + 1) < fixedPointCount T) (B : M ≃ₜ M)
    (hB : IsBiholomorphic (B : M → M)) : B⁻¹ * Tt * B ∈ Subgroup.zpowers Tt := by
  sorry

/-- **Theorem V.1.8(d)** (Ch. V §1.8, (1.8.4)). In the situation of `thm5_1_8_a`: if `n = 2`, `T̃` is in the center of
`Aut M`: `B T̃ = T̃ B` for every `B ∈ Aut M`. -/
theorem thm5_1_8_d {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (Tt : M ≃ₜ M) (hTt : IsBiholomorphic (Tt : M → M))
    (h1 : Tt ≠ 1) (hn : (orderOf Tt).Prime) {gt : ℕ} (hgt : IsQuotientGenus (Subgroup.zpowers Tt) gt)
    (hbig : g > orderOf Tt ^ 2 * gt + (orderOf Tt - 1) ^ 2) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (hT1 : T ≠ 1) (hv : 2 * orderOf Tt * (gt + 1) < fixedPointCount T) (h2 : orderOf Tt = 2) (B : M ≃ₜ M)
    (hB : IsBiholomorphic (B : M → M)) : B * Tt = Tt * B := by
  sorry

/-- **Unlabelled** (Ch. V §1.9, FK2:3666–3670). On every `γ`-hyperelliptic surface `M` of genus `g` there is a
`γ`-hyperelliptic involution: for a holomorphic mapping `π : M → M̃` of degree 2 onto a surface of genus `γ` there is a
`J_γ ∈ Aut M` with `π ∘ J_γ = π`, `ord J_γ = 2` and `ν(J_γ) = 2g + 2 − 4γ`. -/
theorem para5_1_9 {g γ : ℕ} (hM : HasGenus M g) {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N]
    [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N] (hN : HasGenus N γ) {π : M → N}
    (hπ : Forster1981.IsHolomorphicCovering π 2) :
    ∃ J : M ≃ₜ M, IsBiholomorphic (J : M → M) ∧ π ∘ J = π ∧ orderOf J = 2 ∧
      (fixedPointCount J : ℤ) = 2 * g + 2 - 4 * γ := by
  sorry

/-- **Theorem V.1.9(a)** (Ch. V §1.9, (1.9.1)). Let `M` be a `γ`-hyperelliptic surface of genus `g > 4γ + 1`, via the
degree 2 map `π : M → M̃`. If `1 ≠ T ∈ Aut M` with `ν(T) > 4(γ + 1)`, then `T = J_γ`: `T` interchanges the sheets of `π`
(`π ∘ T = π`). -/
theorem thm5_1_9_a {g γ : ℕ} (hM : HasGenus M g) (hg : g > 4 * γ + 1) {N : Type} [TopologicalSpace N] [T2Space N]
    [ConnectedSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N] (hN : HasGenus N γ) {π : M → N}
    (hπ : Forster1981.IsHolomorphicCovering π 2) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M)) (h1 : T ≠ 1)
    (hv : 4 * (γ + 1) < fixedPointCount T) : π ∘ T = π := by
  sorry

/-- **Theorem V.1.9(b)** (Ch. V §1.9, (1.9.2)). In the situation of `thm5_1_9_a`, `J_γ` is in the center of `Aut M`:
every `J ≠ 1` in `Aut M` with `π ∘ J = π` commutes with every element of `Aut M`. -/
theorem thm5_1_9_b {g γ : ℕ} (hM : HasGenus M g) (hg : g > 4 * γ + 1) {N : Type} [TopologicalSpace N] [T2Space N]
    [ConnectedSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N] (hN : HasGenus N γ) {π : M → N}
    (hπ : Forster1981.IsHolomorphicCovering π 2) (J : M ≃ₜ M) (hJ : IsBiholomorphic (J : M → M)) (hJ1 : J ≠ 1)
    (hJπ : π ∘ J = π) (B : M ≃ₜ M) (hB : IsBiholomorphic (B : M → M)) : B * J = J * B := by
  sorry

/-- **Theorem V.1.9(c)** (Ch. V §1.9, (1.9.3)). In the situation of `thm5_1_9_a`: if `f ∈ 𝒦(M) ∖ ℂ` and
`deg f < g + 1 − 2γ`, then `deg f` is even. -/
theorem thm5_1_9_c {g γ : ℕ} (hM : HasGenus M g) (hg : g > 4 * γ + 1) {N : Type} [TopologicalSpace N] [T2Space N]
    [ConnectedSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N] (hN : HasGenus N γ) {π : M → N}
    (hπ : Forster1981.IsHolomorphicCovering π 2) {f : M → RiemannSphere} {n : ℕ}
    (hf : Forster1981.IsHolomorphicCovering f n) (hn : (n : ℤ) < g + 1 - 2 * γ) : Even n := by
  sorry

/-- **Corollary V.1.9(a)** (Ch. V §1.9, Corollary 1). The `γ`-hyperelliptic involution on a surface of genus `g` is
unique (if it exists) provided `g > 4γ + 1`: if `π : M → M̃` and `π' : M → M̃'` are degree 2 maps onto surfaces of
genus `γ`, and `J`, `J'` are non-trivial automorphisms with `π ∘ J = π`, `π' ∘ J' = π'`, then `J = J'`. -/
theorem cor5_1_9_a {g γ : ℕ} (hM : HasGenus M g) (hg : g > 4 * γ + 1) {N N' : Type} [TopologicalSpace N]
    [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ) ω N] [TopologicalSpace N'] [T2Space N']
    [ConnectedSpace N'] [ChartedSpace ℂ N'] [IsManifold 𝓘(ℂ) ω N'] (hN : HasGenus N γ) (hN' : HasGenus N' γ)
    {π : M → N} {π' : M → N'} (hπ : Forster1981.IsHolomorphicCovering π 2)
    (hπ' : Forster1981.IsHolomorphicCovering π' 2) (J J' : M ≃ₜ M) (hJ : IsBiholomorphic (J : M → M))
    (hJ' : IsBiholomorphic (J' : M → M)) (hJ1 : J ≠ 1) (hJ1' : J' ≠ 1) (hJπ : π ∘ J = π) (hJπ' : π' ∘ J' = π') :
    J = J' := by
  sorry

/-- **Corollary V.1.9(b)** (Ch. V §1.9, Corollary 2). If `γ`, `r` are non-negative integers with `r > 0` and
`g > 4γ + 1 + 2r`, then a surface of genus `g` cannot be both `γ`-hyperelliptic and `(γ + r)`-hyperelliptic. In
particular for `g > 3`, a surface of genus `g` cannot be both hyperelliptic and `1`-hyperelliptic (`γ = 0`, `r = 1`). -/
theorem cor5_1_9_b {g γ r : ℕ} (hM : HasGenus M g) (hr : 0 < r) (hg : g > 4 * γ + 1 + 2 * r) :
    ¬ (IsGammaHyperelliptic M γ ∧ IsGammaHyperelliptic M (γ + r)) := by
  sorry

/-- **Proposition V.1.10** (Ch. V §1.10, Accola). Let `M` be a compact surface of genus `g ≥ 2`. Let `G`, `G_j`
(`j = 1, …, k`) be subgroups of `Aut M` such that `G = ⋃_{j=1}^k G_j` and `G_i ∩ G_j = {1}` for `i ≠ j`. Assume
`ord G_j = n_j`, `ord G = n`, and let `γ` be the genus of `M/G`, `γ_j` the genus of `M/G_j`. Then
`(k − 1) g + n γ = Σ_{j=1}^k n_j γ_j`.
Modelling: the groups are finite (automatic for `g ≥ 2` by V.1.2 Corollary 2; stated as `Finite` so that
`Nat.card` is the order). -/
theorem prop5_1_10 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) {k : ℕ} (G : Subgroup (M ≃ₜ M))
    (Gj : Fin k → Subgroup (M ≃ₜ M)) (hG : ∀ h ∈ G, IsBiholomorphic (h : M → M))
    (hGj : ∀ j, ∀ h ∈ Gj j, IsBiholomorphic (h : M → M)) [Finite G] [∀ j, Finite (Gj j)]
    (hcov : (G : Set (M ≃ₜ M)) = ⋃ j, (Gj j : Set (M ≃ₜ M))) (hint : ∀ i j, i ≠ j → Gj i ⊓ Gj j = ⊥) {γ : ℕ}
    {γj : Fin k → ℕ} (hγ : IsQuotientGenus G γ) (hγj : ∀ j, IsQuotientGenus (Gj j) (γj j)) :
    ((k : ℤ) - 1) * g + Nat.card G * γ = ∑ j, (Nat.card (Gj j) : ℤ) * γj j := by
  sorry

/-- **Corollary V.1.10** (Ch. V §1.10, Corollary of Accola's proposition). Let `M` be a surface of genus 3. Assume
there is a subgroup `G` of `Aut M` with `G ≅ ℤ₂ ⊕ ℤ₂` and `M/G` of genus zero. If one element of `G ∖ {1}` operates
fixed point freely, then `M` is hyperelliptic. -/
theorem cor5_1_10 (hM : HasGenus M 3) (G : Subgroup (M ≃ₜ M)) (hG : ∀ h ∈ G, IsBiholomorphic (h : M → M))
    (hiso : Nonempty (G ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) (hγ : IsQuotientGenus G 0)
    (hfree : ∃ h ∈ G, h ≠ 1 ∧ ∀ x, h x ≠ x) : IsGammaHyperelliptic M 0 := by
  sorry

/-- **Theorem V.1.10** (Ch. V §1.10). A smooth (unbranched) two-sheeted holomorphic cover of a surface of genus 2 is
hyperelliptic. -/
theorem thm5_1_10 {N : Type} [TopologicalSpace N] [T2Space N] [ConnectedSpace N] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ) ω N] (hN : HasGenus N 2) {π : M → N} (hπ : Forster1981.IsHolomorphicCovering π 2)
    (hu : Forster1981.IsUnbranched π) : IsGammaHyperelliptic M 0 := by
  sorry

/-- **Proposition V.1.11** (Ch. V §1.11). Let `M` be a compact Riemann surface of genus `g ≥ 2`. If `T ∈ Aut M` is of
prime order `n`, then `n ≤ 2g + 1`.
**[reading]** printed "`g ≤ 2`"; the proof and the Remark use `g ≥ 2`. -/
theorem prop5_1_11 {g : ℕ} (hg : 2 ≤ g) (hM : HasGenus M g) (T : M ≃ₜ M) (hT : IsBiholomorphic (T : M → M))
    (hp : (orderOf T).Prime) : orderOf T ≤ 2 * g + 1 := by
  sorry

end FarkasKra1992
