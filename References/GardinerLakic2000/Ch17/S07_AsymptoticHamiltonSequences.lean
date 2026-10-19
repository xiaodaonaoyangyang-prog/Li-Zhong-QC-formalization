import References.GardinerLakic2000.Ch17.S06_LocalBoundaryDilatation

/-!
# Gardiner–Lakic 2000, Ch. 17 §17.7 Asymptotic Hamilton sequences

Source `teichmuller.txt`, lines 13084–13198 (Chapter 17, §17.7; substantial points also in the introduction,
l. 12671).

* Theorem 6 (l. 13087) — `thm17_6`
* Definition (substantial point, infinitesimally substantial point, l. 13148, 12671) — `IsSubstantialPoint`,
  `IsInfSubstantialPoint`
* Corollary 1 (l. 13150) — `cor17_6_1`
* Definition (extremal coefficient on the plane, `k₀(τ)`, (degenerating) Hamilton sequence, non-Strebel point, used in
  Corollary 2, l. 13159; batch B §4.7 on surfaces) — `kZeroPlane`, `IsDegHamiltonSeqPlane`
* Corollary 2 (l. 13159) — `cor17_6_2`

Not items: (17.8) (proof); "the substantial set coincides with the infinitesimally substantial set" (l. 13148, it is
Theorem 6); "these sets are closed" (U−); the exercises (l. 13178–13197). Modelling: as §17.1. In Theorem 6, (1)
`H(τ) = H_p(τ)` is `h = h_p`; (2) `G(τ) = G_p(τ)` is "`g(τ)` is the value of `g_p(τ)`" (`IsGpValue`); (3), (4) for the
functional `v` of `μ`. The substantial set of Corollary 2 is the set of substantial points in the frontier of `Ω`; a
degenerating Hamilton sequence "degenerates toward a subset of it" when `∬_{Ω∖U} |φₙ| → 0` for every open `U`
containing it. Near misses: batch B's `IsStrebelPoint`, `IsDegHamiltonSeq` (surface level).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (toExt phiArea)

/-- **Theorem 6** (§17.7, l. 13087). For a boundary point `p` and an asymptotically extremal representative `μ` of
`τ ∈ T(Ω)` (with functional `v`), the following are equivalent: (1) `H(τ) = H_p(τ)`; (2) `G(τ) = G_p(τ)`;
(3) `b(v) = b_p(v)`; (4) `β(v) = β_p(v)`; (5) there is an asymptotic Hamilton sequence for `μ` degenerating toward
`p`.
[CORRECTION] (AUDIT5_GL1518 G15-3) (5) reads "`h(τ) = 0` or there is an asymptotic Hamilton sequence degenerating
toward `p`": no sequence degenerates toward an isolated point of `Ωᶜ` (or at all when `A(Ω)` is finite dimensional),
while (1)–(4) hold there when `h(τ) = 0`. -/
theorem thm17_6 {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsConnected Ω) (h3 : 2 ≤ Ωᶜ.encard) {μ : ℂ → ℂ}
    (hμ : IsAsymExtremalPlane Ω μ) {p : ℂ} (hp' : p ∈ frontier Ω) :
    List.TFAE [hPlane Ω μ = hp Ω p μ, IsGpValue Ω p μ (gPlane Ω μ),
      bPlane Ω (fun φ => ∫ z, μ z * φ z) = bp Ω p (fun φ => ∫ z, μ z * φ z),
      betaSeminormOpen (toExt Ω) (fun φ => ∫ z, μ z * φ z) = betaP Ω p (fun φ => ∫ z, μ z * φ z),
      hPlane Ω μ = 0 ∨ ∃ φ : ℕ → ℂ → ℂ, IsAsymHamiltonSeq Ω μ φ ∧ IsDegTowardSeq Ω p φ] := by
  sorry

/-- **Definition** (substantial point, §17.7, l. 13148). `H([μ]) = H_p([μ])`. -/
def IsSubstantialPoint (Ω : Set ℂ) (μ : ℂ → ℂ) (p : ℂ) : Prop := p ∈ frontier Ω ∧ hPlane Ω μ = hp Ω p μ

/-- **Definition** (infinitesimally substantial point, §17.7, l. 13148). `b([μ]) = b_p([μ])`. -/
def IsInfSubstantialPoint (Ω : Set ℂ) (μ : ℂ → ℂ) (p : ℂ) : Prop :=
  p ∈ frontier Ω ∧ bPlane Ω (fun φ => ∫ z, μ z * φ z) = bp Ω p (fun φ => ∫ z, μ z * φ z)

/-- **Corollary 1** (§17.7, l. 13150). For all `τ ∈ T(Ω)`, `H(τ) = max_{p ∈ ∂Ω} H_p(τ)`: substantial points exist.
[CORRECTION] (AUDIT5_GL1518 G15-4) `∂Ω` is the boundary in `ℂ̂`: for unbounded `Ω` the point `∞` (with `h_∞` written out
with the neighbourhoods `{|z| > R}`) may be the only substantial point (`Ω = ℍ`, `h(x) = x` for `x ≤ 0`, `Kx` for
`x ≥ 1`, smooth in between). -/
theorem cor17_6_1 {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsConnected Ω) (h3 : 2 ≤ Ωᶜ.encard) {μ : ℂ → ℂ}
    (hμ : μ ∈ beltramiPlane Ω) :
    ((∃ p, IsSubstantialPoint Ω μ p) ∨
        (¬ Bornology.IsBounded Ω ∧ (⨅ (ν : ℂ → ℂ) (_ : ν ∈ beltramiPlane Ω ∧ teichRelPlane Ω μ ν) (R : ℝ),
        eLpNorm ν ⊤ (volume.restrict (Ω ∩ {z | R < ‖z‖}))) = hPlane Ω μ)) ∧
      ∀ q ∈ frontier Ω, hp Ω q μ ≤ hPlane Ω μ := by
  sorry

/-- Helper (§17.7, l. 13159). `k₀(τ)`: the infimum of `‖ν‖∞` over the `ν` equivalent to `μ`. -/
def kZeroPlane (Ω : Set ℂ) (μ : ℂ → ℂ) : ℝ≥0∞ :=
  ⨅ (ν : ℂ → ℂ) (_ : ν ∈ beltramiPlane Ω ∧ teichRelPlane Ω μ ν), eLpNorm ν ⊤ (volume.restrict Ω)

/-- Helper (§17.7, l. 13159). A degenerating Hamilton sequence for `μ`: a degenerating sequence of unit vectors with
`Re ∬ μ φₙ → ‖μ‖∞`. -/
def IsDegHamiltonSeqPlane (Ω : Set ℂ) (μ : ℂ → ℂ) (φ : ℕ → ℂ → ℂ) : Prop :=
  IsDegeneratingSeqOpen (toExt Ω) φ ∧
    Tendsto (fun n => (∫ z, μ z * φ n z).re) atTop (𝓝 (eLpNorm μ ⊤ (volume.restrict Ω)).toReal)

/-- **Corollary 2** (§17.7, l. 13159). Let `μ` be an extremal representative of a non-Strebel point of `T(Ω)`. Then
every degenerating Hamilton sequence for `μ` degenerates toward a subset of the set of substantial points.
[CORRECTION] (AUDIT5_GL1518 G15-7) The substantial set includes `∞` when `Ω` is unbounded and `h_∞ = h` (as in
Corollary 1); then `U` must contain a neighbourhood `{|z| > R}` of `∞`. -/
theorem cor17_6_2 {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsConnected Ω) (h3 : 2 ≤ Ωᶜ.encard) {μ : ℂ → ℂ}
    (hμ : μ ∈ beltramiPlane Ω) (hext : eLpNorm μ ⊤ (volume.restrict Ω) = kZeroPlane Ω μ)
    (hns : hPlane Ω μ = kZeroPlane Ω μ) {φ : ℕ → ℂ → ℂ} (hφ : IsDegHamiltonSeqPlane Ω μ φ) {U : Set ℂ}
    (hU : IsOpen U) (hsub : {p | IsSubstantialPoint Ω μ p} ⊆ U)
    (hsubInf : ¬ Bornology.IsBounded Ω → (⨅ (ν : ℂ → ℂ) (_ : ν ∈ beltramiPlane Ω ∧ teichRelPlane Ω μ ν) (R : ℝ),
          eLpNorm ν ⊤ (volume.restrict (Ω ∩ {z | R < ‖z‖}))) = hPlane Ω μ →
      ∃ R : ℝ, {z | R < ‖z‖} ⊆ U) :
    Tendsto (fun n => phiArea (φ n) (Ω \ U)) atTop (𝓝 0) := by
  sorry

end GardinerLakic2000
