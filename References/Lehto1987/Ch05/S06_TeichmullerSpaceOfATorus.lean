import References.Lehto1987.Ch05.S05_ComplexStructuresOnTeichmullerSpaces

/-!
# Lehto, Chapter V §6: Teichmüller space of a torus

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. V §6 (`full.md`
P2:734–993).

Conventions (see §1–§2; decision B0.5).
- **Tori.** A torus `S` is a compact Riemann surface with an analytic covering `π : ℂ → S` whose fibres are the cosets
  of a lattice `L` (`IsTorusCovering`, as in `LiZhongQC.thm22_3_classification`). The covering group `G` is the group
  of the translations by `L`, so a base of `G` is a base of `L`.
- **Teichmüller space.** The plane is the universal covering surface, so the Teichmüller space is Lehto's general one
  (§2.1), defined here (`TeichmullerSpace`). Its points are classes of quasiconformal mappings `f : S → Y` onto bundled
  surfaces; `f₁ ∼ f₂` when `f₂` is homotopic to `c ∘ f₁` for a conformal `c`. There is no border, so plain homotopy
  is used. Its distance (2.1) is `teichDistRS`.
- **Lifts.** A normalized lift of `φ : S → S′` is a lift `f : ℂ → ℂ` with `f(0) = 0` for coverings `π`, `π′`.
- **Metrics.** The elliptic modular group `Γ` is Mathlib's `SL(2, ℤ)`. The hyperbolic metric of `H` and of the disc is
  Lehto's (`|dz|/2y`, `|dz|/(1 − |z|²)`), written by its closed formula.

* Definition (base and normalized base of the covering group, §6.1) — `IsLatticeBase`, `IsNormalizedBase` (near miss:
  Mathlib's PeriodPair, which carries no normalization)
* Lemma 6.1 (§6.1) — `lemma5_6_1`
* Formula (6.1) (§6.1) — `lemma5_6_1`
* Formula (6.2) (§6.1) — `lemma5_6_1`
* Formula (6.3) (§6.1) — `lemma5_6_1`
* Definition (the elliptic modular group, §6.1) — exists: `Matrix.SpecialLinearGroup` (SL(2, ℤ) acting on ℍ)
* Unlabelled (§6.1, P2:772–780): elliptic elements of `Γ`; proper discontinuity; `H/Γ` a Riemann surface — omitted:
  quoted (Lehner)
* Unlabelled (§6.1, P2:782): `(λω₁′, λω₂′)` is a normalized base for some `λ ≠ 0` iff `ω₁′/ω₂′` and `ω₁/ω₂` are
  `Γ`-equivalent — `para5_6_1`
* Lemma 6.2 (§6.2) — `lemma5_6_2`
* Definition (normalized lift, §6.2) — `IsNormalizedLiftTorus`
* Theorem 6.1 (§6.2) — `thm5_6_1`
* Formula (6.4) (§6.2) — omitted: a step of the proof of Theorem 6.1
* Formula (6.5) (§6.2) — omitted: a step of the proof of Theorem 6.1 (used in Lemma 6.3)
* Unlabelled (§6.2, P2:800–814): `φ` is sense-preserving iff `Im(f(ω₁)/f(ω₂)) > 0` — `para5_6_2_a`
* Unlabelled (§6.2, P2:816): all tori are quasiconformally equivalent; every sense-preserving homeomorphism is
  homotopic to a quasiconformal one — `para5_6_2_b`
* Unlabelled (§6.3, P2:820–822): tori are conformally equivalent iff `(λω₁, λω₂)` is a base of `G′` for some `λ ≠ 0` —
  `para5_6_3`
* Theorem 6.2 (§6.3) — `thm5_6_2`
* Unlabelled (§6.3, P2:828–836): the model `H/Γ` of `R_S`, the modular function `J`, symmetric tori — omitted: quoted
  or not cited
* Definition (Teichmüller space of a surface covered by the plane, §2.1 for tori) — `TeichmullerSpace`, `teichDistRS`
* Theorem 6.3 (§6.4, Teichmüller) — `thm5_6_3`
* Formula (6.6) (§6.4) — omitted: a step of the proof of Theorem 6.3
* Formula (6.7) (§6.4) — omitted: a step of the proof of Theorem 6.3
* Formula (6.8) (§6.4) — omitted: a step of the proof of Theorem 6.3
* Formula (6.9) (§6.4) — omitted: a step of the proof of Theorem 6.3
* Definition (the distance `δ_θ` of an isomorphism from the identity, §6.5) — `deltaTheta`
* Unlabelled (§6.5, P2:910): `δ_θ` depends only on `θ` — `para5_6_5`
* Lemma 6.3 (§6.5) — `lemma5_6_3`
* Formula (6.10) (§6.5) — `lemma5_6_3`
* Definition (the map `ψ`, (6.11), §6.6) — `IsTorusPsi`
* Unlabelled (§6.6, P2:936–938): `ψ` is well defined, with values in `H`; a change of base replaces `ψ` by `h ∘ ψ`,
  `h ∈ Γ` — `para5_6_6`
* Theorem 6.4 (§6.6) — `thm5_6_4`
* Formula (6.11) (§6.6) — `thm5_6_4`
* Formula (6.12) (§6.6) — `eq5_6_12`
* Theorem 6.5 (§6.6) — `thm5_6_5`
* Formula (6.13) (§6.6) — `IsTorusTeichChart`
* Definition (the complex structure of `T_S` given by (6.13), §6.7) — `IsTorusTeichChart`
* Theorem 6.6 (§6.7) — `thm5_6_6` [misprint, root Corrections: T_S onto T_{S′}]
* Unlabelled (§6.7, P2:988): `h ↦ ψ⁻¹ ∘ h ∘ ψ` is an isomorphism of `Γ` onto `Mod(S)` — `para5_6_7`
* Unlabelled (§6.7, P2:990–992): discontinuity of `Mod(S)`; `Mod(S)` is a proper subgroup of the automorphisms —
  omitted: quoted or not cited

Helper (not a book notion): `IsTorusCovering` (a torus with its covering by the plane).
-/

open Complex Set Filter Topology
open scoped ENNReal ComplexConjugate ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace Lehto1987

universe u

open LiZhongQC (IsQCRS IsBiholomorphic HasGenus RSConformallyEquivalent IsOrientationPreservingRS maxDilatationRS
  unitDisc upperHalf IsKQCRS)
open GardinerLakic2000 (RSBundle)

/-! ## §6.1 Covering group of a torus -/

/-- **Definition** (base of the covering group of a torus, Ch. V §6.1): `G` consists of the translations by
`mω₁ + nω₂`, `m, n ∈ ℤ`, with `Im(ω₁/ω₂) ≠ 0`.
Modelling: `G` is given by its set of translation vectors `L`. -/
def IsLatticeBase (L : Set ℂ) (ω₁ ω₂ : ℂ) : Prop :=
  (ω₁ / ω₂).im ≠ 0 ∧ L = {w | ∃ m n : ℤ, w = m * ω₁ + n * ω₂}

/-- **Definition** (normalized base, Ch. V §6.1): a base with `Im(ω₁/ω₂) > 0`. -/
def IsNormalizedBase (L : Set ℂ) (ω₁ ω₂ : ℂ) : Prop := IsLatticeBase L ω₁ ω₂ ∧ 0 < (ω₁ / ω₂).im

/-- **Lemma 6.1** (Ch. V §6.1). Let `(ω₁, ω₂)` be a base of `G`. Then `(ω₁′, ω₂′)` is a base of `G` if and only if
`ω₁′ = aω₁ + bω₂`, `ω₂′ = cω₁ + dω₂` (6.1) with integers `a, b, c, d` and `ad − bc = ±1` (6.2); then
`Im(ω₁′/ω₂′) = (ad − bc) Im(ω₁/ω₂)/|cω₁/ω₂ + d|²` (6.3). If `(ω₁, ω₂)` is normalized, `(ω₁′, ω₂′)` is normalized if
and only if `ad − bc = 1`. -/
theorem lemma5_6_1 {L : Set ℂ} {ω₁ ω₂ : ℂ} (h : IsLatticeBase L ω₁ ω₂) (ω₁' ω₂' : ℂ) :
    (IsLatticeBase L ω₁' ω₂' ↔ ∃ a b c d : ℤ, ω₁' = a * ω₁ + b * ω₂ ∧ ω₂' = c * ω₁ + d * ω₂ ∧
      (a * d - b * c = 1 ∨ a * d - b * c = -1)) ∧
    (∀ a b c d : ℤ, ω₁' = a * ω₁ + b * ω₂ → ω₂' = c * ω₁ + d * ω₂ → (a * d - b * c = 1 ∨ a * d - b * c = -1) →
      (ω₁' / ω₂').im = (a * d - b * c) * (ω₁ / ω₂).im / ‖c * (ω₁ / ω₂) + d‖ ^ 2 ∧
      (0 < (ω₁ / ω₂).im → (0 < (ω₁' / ω₂').im ↔ a * d - b * c = 1))) := by
  sorry

/-- **Unlabelled** (Ch. V §6.1, P2:782). Let `(ω₁, ω₂)` be a normalized base of `G` and `ω₁′, ω₂′` non-zero with
`Im(ω₁′/ω₂′) > 0`. Then `(λω₁′, λω₂′)` is a normalized base of `G` for some `λ ≠ 0` if and only if `ω₁′/ω₂′` is
equivalent to `ω₁/ω₂` under the elliptic modular group.
Modelling: `g ∈ SL(2, ℤ)` acting by `z ↦ (az + b)/(cz + d)`. -/
theorem para5_6_1 {L : Set ℂ} {ω₁ ω₂ : ℂ} (h : IsNormalizedBase L ω₁ ω₂) {ω₁' ω₂' : ℂ} (h₁ : ω₁' ≠ 0)
    (h₂ : ω₂' ≠ 0) (him : 0 < (ω₁' / ω₂').im) :
    (∃ c : ℂ, c ≠ 0 ∧ IsNormalizedBase L (c * ω₁') (c * ω₂')) ↔
      ∃ g : SL(2, ℤ), ((g 0 0 : ℂ) * (ω₁' / ω₂') + g 0 1) / ((g 1 0 : ℂ) * (ω₁' / ω₂') + g 1 1) = ω₁ / ω₂ := by
  sorry

/-- Helper. `π : ℂ → S` exhibits the compact Riemann surface `S` as the torus `ℂ/G`, `G` the translations by `L`:
an analytic covering whose fibres are the cosets of `L`. -/
def IsTorusCovering {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (π : ℂ → S) (L : Set ℂ) : Prop :=
  IsCoveringMap π ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) π ∧ Function.Surjective π ∧ ∀ z w : ℂ, π z = π w ↔ z - w ∈ L

/-! ## §6.2 Generation of group isomorphisms -/

/-- **Lemma 6.2** (Ch. V §6.2). Let `S` be a torus and `p`, `q` points of `S`. Then there is a conformal mapping
`f : S → S` homotopic to the identity with `f(p) = q`. -/
theorem lemma5_6_2 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] (hS : HasGenus S 1) (p q : S) :
    ∃ f : S ≃ₜ S, IsBiholomorphic f ∧ ContinuousMap.Homotopic (f : C(S, S)) (ContinuousMap.id S) ∧ f p = q := by
  sorry

/-- **Definition** (normalized lift, Ch. V §6.2): for coverings `π : ℂ → S`, `π′ : ℂ → S′`, a lift `f` of `φ`
(`π′ ∘ f = φ ∘ π`) with `f(0) = 0`. -/
def IsNormalizedLiftTorus {S S' : Type u} (π : ℂ → S) (π' : ℂ → S') (φ : S → S') (f : ℂ → ℂ) : Prop :=
  Continuous f ∧ (∀ z, π' (f z) = φ (π z)) ∧ f 0 = 0

/-- **Theorem 6.1** (Ch. V §6.2). Let `S = ℂ/G` and `S′ = ℂ/G′` be tori and `θ : G → G′` an isomorphism. Then there is
a homeomorphism of `S` onto `S′` which induces `θ`.
Modelling: `G`, `G′` are given by the lattices `L`, `L′` (additive subgroups) and `θ` by an additive isomorphism; `φ`
induces `θ` through a normalized lift: `f(z + ω) = f(z) + θ(ω)`. -/
theorem thm5_6_1 {S S' : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S'] [ChartedSpace ℂ S']
    [IsManifold 𝓘(ℂ) ω S'] {L L' : AddSubgroup ℂ} {π : ℂ → S} {π' : ℂ → S'} (hπ : IsTorusCovering π L)
    (hπ' : IsTorusCovering π' L') (hb : ∃ ω₁ ω₂, IsLatticeBase L ω₁ ω₂) (θ : L ≃+ L') :
    ∃ (φ : S ≃ₜ S') (f : ℂ → ℂ), IsNormalizedLiftTorus π π' φ f ∧ ∀ (l : L) (z : ℂ), f (z + l) = f z + θ l := by
  sorry

/-- **Unlabelled** (Ch. V §6.2, P2:800–814). Let `(ω₁, ω₂)` be a normalized base of `G` and `φ : S → S′` a
homeomorphism of tori with normalized lift `f`. Then `φ` is sense-preserving if and only if `Im(f(ω₁)/f(ω₂)) > 0`. -/
theorem para5_6_2_a {S S' : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S'] [ChartedSpace ℂ S']
    [IsManifold 𝓘(ℂ) ω S'] {L L' : Set ℂ} {π : ℂ → S} {π' : ℂ → S'} (hπ : IsTorusCovering π L)
    (hπ' : IsTorusCovering π' L') {ω₁ ω₂ : ℂ} (hb : IsNormalizedBase L ω₁ ω₂) (φ : S ≃ₜ S') {f : ℂ → ℂ}
    (hf : IsNormalizedLiftTorus π π' φ f) : IsOrientationPreservingRS φ ↔ 0 < (f ω₁ / f ω₂).im := by
  sorry

/-- **Unlabelled** (Ch. V §6.2, P2:816). Any two tori are quasiconformally equivalent, and every sense-preserving
homeomorphism between tori is homotopic to a quasiconformal mapping. -/
theorem para5_6_2_b {S S' : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S']
    [ChartedSpace ℂ S'] [IsManifold 𝓘(ℂ) ω S'] [CompactSpace S'] (hS : HasGenus S 1) (hS' : HasGenus S' 1) :
    (∃ φ : S ≃ₜ S', IsQCRS φ) ∧ ∀ φ : S ≃ₜ S', IsOrientationPreservingRS φ →
      ∃ ψ : S ≃ₜ S', IsQCRS ψ ∧ ContinuousMap.Homotopic (ψ : C(S, S')) (φ : C(S, S')) := by
  sorry

/-! ## §6.3 Conformal equivalence of tori -/

/-- **Unlabelled** (Ch. V §6.3, P2:820–822). The tori `S = ℂ/G` and `S′ = ℂ/G′` are conformally equivalent if and only
if `(λω₁, λω₂)` is a base of `G′` for some `λ ≠ 0`, `(ω₁, ω₂)` a base of `G`. -/
theorem para5_6_3 {S S' : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S'] [ChartedSpace ℂ S']
    [IsManifold 𝓘(ℂ) ω S'] {L L' : Set ℂ} {π : ℂ → S} {π' : ℂ → S'} (hπ : IsTorusCovering π L)
    (hπ' : IsTorusCovering π' L') {ω₁ ω₂ : ℂ} (hb : IsLatticeBase L ω₁ ω₂) :
    RSConformallyEquivalent S S' ↔ ∃ c : ℂ, c ≠ 0 ∧ IsLatticeBase L' (c * ω₁) (c * ω₂) := by
  sorry

/-- **Theorem 6.2** (Ch. V §6.3). Let `S = ℂ/G`, `S′ = ℂ/G′` be tori with normalized bases `(ω₁, ω₂)`, `(ω₁′, ω₂′)`.
Then `S` and `S′` are conformally equivalent if and only if `ω₁/ω₂` and `ω₁′/ω₂′` are equivalent under the elliptic
modular group. -/
theorem thm5_6_2 {S S' : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S'] [ChartedSpace ℂ S']
    [IsManifold 𝓘(ℂ) ω S'] {L L' : Set ℂ} {π : ℂ → S} {π' : ℂ → S'} (hπ : IsTorusCovering π L)
    (hπ' : IsTorusCovering π' L') {ω₁ ω₂ ω₁' ω₂' : ℂ} (hb : IsNormalizedBase L ω₁ ω₂)
    (hb' : IsNormalizedBase L' ω₁' ω₂') :
    RSConformallyEquivalent S S' ↔
      ∃ g : SL(2, ℤ), ((g 0 0 : ℂ) * (ω₁ / ω₂) + g 0 1) / ((g 1 0 : ℂ) * (ω₁ / ω₂) + g 1 1) = ω₁' / ω₂' := by
  sorry

/-! ## §6.4 Extremal mappings of tori -/

/-- **Definition** (Teichmüller space, Ch. V §2.1, for surfaces without border): the classes of quasiconformal mappings
`f` of `S` onto Riemann surfaces, `f₁ ∼ f₂` when `f₂ ∘ f₁⁻¹` is homotopic to a conformal mapping of `f₁(S)` onto
`f₂(S)`.
Modelling: target surfaces bundled (`GardinerLakic2000.RSBundle`, universe of `S`); `f₂` homotopic to `c ∘ f₁`, `c`
biholomorphic; used for tori (plane as universal covering surface), where `GardinerLakic2000.TeichSpace` (through a
uniformization by `ℍ`) does not apply. -/
def TeichmullerSpace (S : Type u) [TopologicalSpace S] [ChartedSpace ℂ S] : Type (u + 1) :=
  Quot fun (a b : {a : Σ Y : RSBundle.{u}, S ≃ₜ Y.carrier // IsQCRS a.2}) =>
    ∃ c : a.1.1.carrier ≃ₜ b.1.1.carrier, IsBiholomorphic c ∧
      ContinuousMap.Homotopic ((a.1.2.trans c : S ≃ₜ b.1.1.carrier) : C(S, b.1.1.carrier))
        (b.1.2 : C(S, b.1.1.carrier))

/-- **Definition** (the Teichmüller distance (2.1) of `TeichmullerSpace`, Ch. V §2.2):
`τ(p, q) = ½ inf {log K_{g ∘ f⁻¹} | f ∈ p, g ∈ q}` (not `GardinerLakic2000.teichDist`, the distance of the model
uniformized by `ℍ`). -/
def teichDistRS {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (p q : TeichmullerSpace S) : ℝ :=
  (1 / 2) * sInf {d | ∃ a b : {a : Σ Y : RSBundle.{u}, S ≃ₜ Y.carrier // IsQCRS a.2}, Quot.mk _ a = p ∧
    Quot.mk _ b = q ∧ d = Real.log (maxDilatationRS (b.1.2 ∘ a.1.2.symm : a.1.1.carrier → b.1.1.carrier)).toReal}

/-- **Theorem 6.3** (Ch. V §6.4, Teichmüller). In each homotopy class of sense-preserving homeomorphisms between tori
there is a mapping whose lifts are affine and which is extremal (smallest maximal dilatation). Having affine lifts, or
being extremal, determines the mapping uniquely up to conformal mappings homotopic to the identity.
Modelling: affine lift: `f(z) = az + b z̄ + c` with `|b| < |a|`; uniqueness: any extremal (or affine-lifted) `ψ` in
the class is `c ∘ φ` with `c` conformal and homotopic to the identity. -/
theorem thm5_6_3 {S S' : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S'] [ChartedSpace ℂ S']
    [IsManifold 𝓘(ℂ) ω S'] {L L' : Set ℂ} {π : ℂ → S} {π' : ℂ → S'} (hπ : IsTorusCovering π L)
    (hπ' : IsTorusCovering π' L') (hb : ∃ ω₁ ω₂, IsLatticeBase L ω₁ ω₂) (φ₀ : S ≃ₜ S')
    (hφ₀ : IsOrientationPreservingRS φ₀) :
    ∃ φ : S ≃ₜ S', IsQCRS φ ∧ ContinuousMap.Homotopic (φ : C(S, S')) (φ₀ : C(S, S')) ∧
      (∃ (f : ℂ → ℂ) (a b c : ℂ), ‖b‖ < ‖a‖ ∧ (∀ z, π' (f z) = φ (π z)) ∧ ∀ z, f z = a * z + b * conj z + c) ∧
      (∀ ψ : S ≃ₜ S', IsQCRS ψ → ContinuousMap.Homotopic (ψ : C(S, S')) (φ₀ : C(S, S')) →
        maxDilatationRS φ ≤ maxDilatationRS ψ) ∧
      ∀ ψ : S ≃ₜ S', IsQCRS ψ → ContinuousMap.Homotopic (ψ : C(S, S')) (φ₀ : C(S, S')) →
        (maxDilatationRS ψ = maxDilatationRS φ ∨
          ∃ (f : ℂ → ℂ) (a b c : ℂ), ‖b‖ < ‖a‖ ∧ (∀ z, π' (f z) = ψ (π z)) ∧ ∀ z, f z = a * z + b * conj z + c) →
        ∃ κ : S' ≃ₜ S', IsBiholomorphic κ ∧ ContinuousMap.Homotopic (κ : C(S', S')) (ContinuousMap.id S') ∧
          ⇑ψ = κ ∘ φ := by
  sorry

/-! ## §6.5 Distance of group isomorphisms from the identity -/

/-- **Definition** (the distance `δ_θ`, Ch. V §6.5): the hyperbolic distance in the upper half-plane between
`ω₁/ω₂` and `f(ω₁)/f(ω₂) = θ(ω₁)/θ(ω₂)`.
Modelling: Lehto's metric `|dz|/2y`: `h(τ, τ′) = ½ log((|τ′ − τ̄| + |τ′ − τ|)/(|τ′ − τ̄| − |τ′ − τ|))`, written for the
two bases. -/
def deltaTheta (ω₁ ω₂ ω₁' ω₂' : ℂ) : ℝ :=
  (1 / 2) * Real.log ((‖ω₁' / ω₂' - conj (ω₁ / ω₂)‖ + ‖ω₁' / ω₂' - ω₁ / ω₂‖) /
    (‖ω₁' / ω₂' - conj (ω₁ / ω₂)‖ - ‖ω₁' / ω₂' - ω₁ / ω₂‖))

/-- **Unlabelled** (Ch. V §6.5, P2:910). `δ_θ` depends only on the isomorphism `θ`, not on the normalized base of `G`.
-/
theorem para5_6_5 {L L' : AddSubgroup ℂ} (θ : L ≃+ L') {ω₁ ω₂ η₁ η₂ : L}
    (hω : IsNormalizedBase L (ω₁ : ℂ) ω₂) (hη : IsNormalizedBase L (η₁ : ℂ) η₂) :
    deltaTheta ω₁ ω₂ (θ ω₁) (θ ω₂) = deltaTheta η₁ η₂ (θ η₁) (θ η₂) := by
  sorry

/-- **Lemma 6.3** (Ch. V §6.5). Let `θ : G → G′` be generated by a normalized `K`-quasiconformal mapping `f`. Then
`δ_θ ≤ ½ log K` (6.10), with equality if and only if `f` is the affine transformation generating `θ`.
Modelling: `f` is a `K`-quasiconformal self-map of the plane with `f(0) = 0` and `f(z + ω) = f(z) + θ(ω)`.
[reading] The equality case is for `K` the maximal dilatation of `f`, as in the proof (P2:920); for a larger `K` the
affine `f` gives a strict inequality. -/
theorem lemma5_6_3 {L L' : AddSubgroup ℂ} (θ : L ≃+ L') {ω₁ ω₂ : L} (hω : IsNormalizedBase L (ω₁ : ℂ) ω₂)
    {f : ℂ → ℂ} {K : ℝ} (hf : LiZhongQC.IsKQC f univ K) (hsurj : f '' univ = univ) (h0 : f 0 = 0)
    (hθ : ∀ (l : L) (z : ℂ), f (z + l) = f z + θ l) :
    deltaTheta ω₁ ω₂ (θ ω₁) (θ ω₂) ≤ (1 / 2) * Real.log K ∧
      (LiZhongQC.maxDilatation f univ = ENNReal.ofReal K →
        (deltaTheta ω₁ ω₂ (θ ω₁) (θ ω₂) = (1 / 2) * Real.log K ↔ ∃ a b : ℂ, ∀ z, f z = a * z + b * conj z)) := by
  sorry

/-! ## §6.6 Representation of the Teichmüller space of a torus -/

/-- **Definition** (the map `ψ : T_S → H`, (6.11), Ch. V §6.6): `ψ([φ]) = f(ω₁)/f(ω₂)`, `f` the normalized lift of
`φ`.
Modelling: relational: the value at the class of `φ : S → Y` is `f(ω₁)/f(ω₂)` for every covering `π_Y` of `Y` by
the plane and every normalized lift `f`. -/
def IsTorusPsi {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (π : ℂ → S) (ω₁ ω₂ : ℂ)
    (ψ : TeichmullerSpace S → ℂ) : Prop :=
  ∀ (a : {a : Σ Y : RSBundle.{u}, S ≃ₜ Y.carrier // IsQCRS a.2}) (πY : ℂ → a.1.1.carrier) (LY : Set ℂ)
    (f : ℂ → ℂ), IsTorusCovering πY LY → IsNormalizedLiftTorus π πY a.1.2 f → ψ (Quot.mk _ a) = f ω₁ / f ω₂

/-- **Unlabelled** (Ch. V §6.6, P2:936–938). `ψ` is well defined, with values in the upper half-plane; replacing the
normalized base `(ω₁, ω₂)` by `(aω₁ + bω₂, cω₁ + dω₂)`, `ad − bc = 1`, replaces `ψ` by `h ∘ ψ`,
`h(z) = (az + b)/(cz + d)`. -/
theorem para5_6_6 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {L : Set ℂ} {π : ℂ → S} (hπ : IsTorusCovering π L) {ω₁ ω₂ : ℂ}
    (hb : IsNormalizedBase L ω₁ ω₂) :
    (∃ ψ : TeichmullerSpace S → ℂ, IsTorusPsi π ω₁ ω₂ ψ ∧ ∀ p, 0 < (ψ p).im) ∧
      ∀ (ψ ψ' : TeichmullerSpace S → ℂ) (g : SL(2, ℤ)), IsTorusPsi π ω₁ ω₂ ψ →
        IsTorusPsi π (g 0 0 * ω₁ + g 0 1 * ω₂) (g 1 0 * ω₁ + g 1 1 * ω₂) ψ' →
        ∀ p, ψ' p = ((g 0 0 : ℂ) * ψ p + g 0 1) / ((g 1 0 : ℂ) * ψ p + g 1 1) := by
  sorry

/-- **Theorem 6.4** (Ch. V §6.6). The mapping `ψ` (6.11) is a bijective isometry of `T_S` onto the upper half-plane
with the hyperbolic metric (Lehto's `|dz|/2y`, closed formula as in `deltaTheta`). -/
theorem thm5_6_4 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {L : Set ℂ} {π : ℂ → S} (hπ : IsTorusCovering π L) {ω₁ ω₂ : ℂ}
    (hb : IsNormalizedBase L ω₁ ω₂) {ψ : TeichmullerSpace S → ℂ} (hψ : IsTorusPsi π ω₁ ω₂ ψ) :
    BijOn ψ univ upperHalf ∧ ∀ p q, teichDistRS p q =
      (1 / 2) * Real.log ((‖ψ q - conj (ψ p)‖ + ‖ψ q - ψ p‖) / (‖ψ q - conj (ψ p)‖ - ‖ψ q - ψ p‖)) := by
  sorry

/-- **Formula (6.12)** (Ch. V §6.6). Every class has a representative whose normalized lift is affine,
`ζ ↦ ζ + z ζ̄` with `|z| < 1`; for this class `[z]`, `ψ([z]) = (ω₁ + ω̄₁ z)/(ω₂ + ω̄₂ z)`. -/
theorem eq5_6_12 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {L : Set ℂ} {π : ℂ → S} (hπ : IsTorusCovering π L) {ω₁ ω₂ : ℂ}
    (hb : IsNormalizedBase L ω₁ ω₂) {ψ : TeichmullerSpace S → ℂ} (hψ : IsTorusPsi π ω₁ ω₂ ψ) :
    (∀ p : TeichmullerSpace S, ∃ (a : {a : Σ Y : RSBundle.{u}, S ≃ₜ Y.carrier // IsQCRS a.2})
      (πY : ℂ → a.1.1.carrier) (LY : Set ℂ) (z : ℂ), Quot.mk _ a = p ∧ ‖z‖ < 1 ∧ IsTorusCovering πY LY ∧
      IsNormalizedLiftTorus π πY a.1.2 (fun ζ => ζ + z * conj ζ)) ∧
    ∀ (a : {a : Σ Y : RSBundle.{u}, S ≃ₜ Y.carrier // IsQCRS a.2}) (πY : ℂ → a.1.1.carrier) (LY : Set ℂ) (z : ℂ),
      ‖z‖ < 1 → IsTorusCovering πY LY → IsNormalizedLiftTorus π πY a.1.2 (fun ζ => ζ + z * conj ζ) →
      ψ (Quot.mk _ a) = (ω₁ + conj ω₁ * z) / (ω₂ + conj ω₂ * z) := by
  sorry

/-- **Definition** (the map (6.13) and the complex structure of `T_S`, Ch. V §6.6–§6.7): `[z] ↦ z`, where `[z]` is the
class with the normalized affine lift `ζ ↦ ζ + z ζ̄`.
Modelling: relational, as `IsTorusPsi`. -/
def IsTorusTeichChart {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S] (π : ℂ → S)
    (χ : TeichmullerSpace S → ℂ) : Prop :=
  ∀ (a : {a : Σ Y : RSBundle.{u}, S ≃ₜ Y.carrier // IsQCRS a.2}) (πY : ℂ → a.1.1.carrier) (LY : Set ℂ) (z : ℂ),
    ‖z‖ < 1 → IsTorusCovering πY LY → IsNormalizedLiftTorus π πY a.1.2 (fun ζ => ζ + z * conj ζ) →
    χ (Quot.mk _ a) = z

/-- **Theorem 6.5** (Ch. V §6.6). The mapping `[z] ↦ z` (6.13) is a bijective isometry of the Teichmüller space `T_S`
onto the hyperbolic unit disc (Lehto's metric `|dz|/(1 − |z|²)`, closed formula). -/
theorem thm5_6_5 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {L : Set ℂ} {π : ℂ → S} (hπ : IsTorusCovering π L) (hb : ∃ ω₁ ω₂, IsNormalizedBase L ω₁ ω₂)
    {χ : TeichmullerSpace S → ℂ} (hχ : IsTorusTeichChart π χ) :
    BijOn χ univ unitDisc ∧ ∀ p q, teichDistRS p q =
      (1 / 2) * Real.log ((‖1 - conj (χ p) * χ q‖ + ‖χ p - χ q‖) / (‖1 - conj (χ p) * χ q‖ - ‖χ p - χ q‖)) := by
  sorry

/-! ## §6.7 Complex structure of the Teichmüller space of a torus -/

/-- **Theorem 6.6** (Ch. V §6.7). Let `S`, `S′` be tori and `w : S → S′` a quasiconformal mapping. Then the bijective
isometry `[φ] ↦ [φ ∘ w⁻¹]` of `T_S` onto `T_{S′}` is biholomorphic: in the charts (6.13) it is a conformal self-map
`z ↦ e^{iθ}(z − μ)/(1 − μ̄z)` of the disc.
[misprint, root Corrections] The book prints "onto `T_S`" for "onto `T_{S′}`".
Modelling: the map is given on representatives (`[φ] ↦ [φ ∘ w⁻¹]`). -/
theorem thm5_6_6 {S S' : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [TopologicalSpace S'] [T2Space S'] [ConnectedSpace S'] [ChartedSpace ℂ S']
    [IsManifold 𝓘(ℂ) ω S'] {L L' : Set ℂ} {π : ℂ → S} {π' : ℂ → S'} (hπ : IsTorusCovering π L)
    (hπ' : IsTorusCovering π' L') (hb : ∃ ω₁ ω₂, IsNormalizedBase L ω₁ ω₂)
    (hb' : ∃ ω₁ ω₂, IsNormalizedBase L' ω₁ ω₂) {w : S ≃ₜ S'} (hw : IsQCRS w)
    {Φ : TeichmullerSpace S → TeichmullerSpace S'}
    (hΦ : ∀ (Y : RSBundle.{u}) (f : S ≃ₜ Y.carrier) (hf : IsQCRS f) (hg : IsQCRS (w.symm.trans f)),
      Φ (Quot.mk _ ⟨⟨Y, f⟩, hf⟩) = Quot.mk _ ⟨⟨Y, w.symm.trans f⟩, hg⟩)
    {χ : TeichmullerSpace S → ℂ} {χ' : TeichmullerSpace S' → ℂ} (hχ : IsTorusTeichChart π χ)
    (hχ' : IsTorusTeichChart π' χ') :
    Function.Bijective Φ ∧ (∀ p q, teichDistRS (Φ p) (Φ q) = teichDistRS p q) ∧
      ∃ (θ : ℝ) (μ : ℂ), ‖μ‖ < 1 ∧ ∀ p, χ' (Φ p) = exp (θ * I) * (χ p - μ) / (1 - conj μ * χ p) := by
  sorry

/-- **Unlabelled** (Ch. V §6.7, P2:988). Two points `p₁`, `p₂` of `T_S` are equivalent under `Mod(S)` if and only if
`ψ(p₁)` and `ψ(p₂)` are equivalent under the elliptic modular group: `h ↦ ψ⁻¹ ∘ h ∘ ψ` is an isomorphism of `Γ` onto
`Mod(S)`.
Modelling: equivalence under `Mod(S)` is conformal equivalence of the image surfaces (Theorem 2.7). -/
theorem para5_6_7 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {L : Set ℂ} {π : ℂ → S} (hπ : IsTorusCovering π L) {ω₁ ω₂ : ℂ}
    (hb : IsNormalizedBase L ω₁ ω₂) {ψ : TeichmullerSpace S → ℂ} (hψ : IsTorusPsi π ω₁ ω₂ ψ)
    (a b : {a : Σ Y : RSBundle.{u}, S ≃ₜ Y.carrier // IsQCRS a.2}) :
    RSConformallyEquivalent a.1.1.carrier b.1.1.carrier ↔
      ∃ g : SL(2, ℤ), ψ (Quot.mk _ b) =
        ((g 0 0 : ℂ) * ψ (Quot.mk _ a) + g 0 1) / ((g 1 0 : ℂ) * ψ (Quot.mk _ a) + g 1 1) := by
  sorry

end Lehto1987
