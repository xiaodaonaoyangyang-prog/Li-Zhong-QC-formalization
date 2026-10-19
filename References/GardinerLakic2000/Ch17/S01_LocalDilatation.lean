import References.GardinerLakic2000.Ch16.S08_GlobalCoordinates

/-!
# Gardiner–Lakic 2000, Ch. 17 §17.1 Local dilatation (with the chapter introduction)

Source `teichmuller.txt`, lines 12669–12746 (Chapter 17, introduction and §17.1).

* Definition (`M(Ω)`, the coefficients `μ` on the plane domain `Ω`, extended by `0`, l. 12678) — `beltramiPlane`
* Definition (`T(Ω)`: the isotopy relation rel the ideal boundary, equal to frontier equivalence, l. 12690–12699) —
  `teichRelPlane`
* Definition (boundary dilatations `h*`, `b*` on the plane, l. 12704, 12720) — exists:
  `GardinerLakic2000.bStarOmega` (batch D, with the trivial group: `h*(μ) = b*(μ)`)
* Definition (`h(τ)`, `b(v)` on the plane; representatives of `v ∈ Z(Ω)`, l. 12704, 12720) — `RepresentsPlane`,
  `hPlane`, `bPlane`
* Definition (`h*_p`, `h_p`, `H*_p`, `H_p`, l. 12704–12710) — `hpStar`, `hp`
* Definition ((17.2) `b*_p`, `b_p`, l. 12716) — `bp` (`b*_p = h*_p`, the same quantity: `hpStar`)
* Definition (degenerating toward `p`, l. 12725) — `IsDegTowardSeq`
* Definition ((17.3) `β_p`, l. 12733) — `betaP`; `β` — exists: `GardinerLakic2000.betaSeminormOpen`
* Definition (asymptotically extremal coefficient on the plane; asymptotic Hamilton sequence, l. 12737–12739) —
  `IsAsymExtremalPlane`, `IsAsymHamiltonSeq`
* Unlabelled (the asymptotic Hamilton–Krushkal / Reich–Strebel criterion (17.4), l. 12739–12745; used in §17.3,
  §17.7) — `para17_1_asym_criterion`

Not items: the introduction's claims (l. 12671–12675, restated in Corollary 17.1); upper semicontinuity of `H_p`,
`b_p` in `p` (l. 12723, U−); the existence of maximizing sequences (l. 12735, U−). Modelling (leader calibration of
Part E, E0.5): plane domains `Ω ⊆ ℂ`; `M(Ω)` are the coefficients `μ : ℂ → ℂ` with `‖μ‖∞ < 1` vanishing off `Ω`; the
map `f^μ` is `LiZhongQC.normalizedSolution μ`, and `T(Ω)` is the relation of batch B's frontier equivalence
`IsFrontierEquiv` (the book's l. 12699; a class `τ = [μ]` is handled through its representatives). `A(Ω)`, `Z(Ω)`,
degenerating sequences, `β` are batch A's `aSpaceOpen`, `zSpaceOpen`, `IsDegeneratingSeqOpen`, `betaSeminormOpen`
(for `Ω` seen in `ℂ̂`); `μ` represents `v ∈ Z(Ω)` when `v(φ) = ∬ μ φ` on `A(Ω)`. The essential supremum of `|μ|` on
`S` is `eLpNorm μ ⊤ (volume.restrict S)`. `H = (1 + h)/(1 − h)` and `G`, `G_p` are not separate definitions (the
statements compare `h`, `g`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

open LiZhongQC (normalizedSolution toExt IsBeltramiCoeff phiArea)

/-- **Definition** (`M(Ω)`, §17.1, l. 12678). Beltrami coefficients on the plane domain `Ω`, zero off `Ω`. -/
def beltramiPlane (Ω : Set ℂ) : Set (ℂ → ℂ) := {μ | (∃ k < 1, IsBeltramiCoeff μ univ k) ∧ ∀ z ∉ Ω, μ z = 0}

/-- **Definition** (`T(Ω)`, §17.1, l. 12690–12699). `μ₀ ~ μ₁`: the induced maps are frontier equivalent. -/
def teichRelPlane (Ω : Set ℂ) (μ ν : ℂ → ℂ) : Prop :=
  IsFrontierEquiv Ω (normalizedSolution μ) (normalizedSolution ν)

/-- Helper (§17.1). `μ ∈ L∞(Ω)` represents `v ∈ Z(Ω)`: `v(φ) = ∬ μ φ` for `φ ∈ A(Ω)`. -/
def RepresentsPlane (Ω : Set ℂ) (μ : ℂ → ℂ) (V : (ℂ → ℂ) → ℂ) : Prop :=
  (∃ k : ℝ, IsBeltramiCoeff μ univ k) ∧ (∀ z ∉ Ω, μ z = 0) ∧ ∀ φ ∈ aSpaceOpen (toExt Ω), V φ = ∫ z, μ z * φ z

/-- **Definition** (`h(τ)`, §17.1, l. 12704–12710). The infimum of `h*(ν) = b*(ν)` over the `ν` equivalent to `μ`. -/
def hPlane (Ω : Set ℂ) (μ : ℂ → ℂ) : ℝ≥0∞ :=
  ⨅ (ν : ℂ → ℂ) (_ : ν ∈ beltramiPlane Ω ∧ teichRelPlane Ω μ ν), bStarOmega {fun z => z} Ω ν

/-- **Definition** (`b(v)`, §17.1, l. 12720). The infimum of `b*(μ)` over the representatives `μ` of `v`. -/
def bPlane (Ω : Set ℂ) (V : (ℂ → ℂ) → ℂ) : ℝ≥0∞ :=
  ⨅ (μ : ℂ → ℂ) (_ : RepresentsPlane Ω μ V), bStarOmega {fun z => z} Ω μ

/-- **Definition** (`h*_p = b*_p`, §17.1, l. 12704, (17.2) l. 12716). The infimum over neighbourhoods `U` of the
boundary point `p` of `‖μ|_{Ω ∩ U}‖∞`. -/
def hpStar (Ω : Set ℂ) (p : ℂ) (μ : ℂ → ℂ) : ℝ≥0∞ := ⨅ U ∈ 𝓝 p, eLpNorm μ ⊤ (volume.restrict (Ω ∩ U))

/-- **Definition** (`h_p(τ)`, §17.1, l. 12706). The infimum of `h*_p(ν)` over the `ν` equivalent to `μ`. -/
def hp (Ω : Set ℂ) (p : ℂ) (μ : ℂ → ℂ) : ℝ≥0∞ :=
  ⨅ (ν : ℂ → ℂ) (_ : ν ∈ beltramiPlane Ω ∧ teichRelPlane Ω μ ν), hpStar Ω p ν

/-- **Definition** (`b_p(v)`, (17.2), §17.1, l. 12716). The infimum of `b*_p(μ)` over the representatives of `v`. -/
def bp (Ω : Set ℂ) (p : ℂ) (V : (ℂ → ℂ) → ℂ) : ℝ≥0∞ :=
  ⨅ (μ : ℂ → ℂ) (_ : RepresentsPlane Ω μ V), hpStar Ω p μ

/-- **Definition** (§17.1, l. 12725). A degenerating sequence of unit vectors of `A(Ω)` degenerates toward `p`:
`∬_U |φₙ| → 1` for every open `U ∋ p`. -/
def IsDegTowardSeq (Ω : Set ℂ) (p : ℂ) (φ : ℕ → ℂ → ℂ) : Prop :=
  IsDegeneratingSeqOpen (toExt Ω) φ ∧ ∀ U : Set ℂ, IsOpen U → p ∈ U → Tendsto (fun n => phiArea (φ n) U) atTop (𝓝 1)

/-- **Definition** (`β_p`, (17.3), §17.1, l. 12733). `β_p(v) = sup limsup |v(φₙ)|` over sequences degenerating toward
`p`. -/
def betaP (Ω : Set ℂ) (p : ℂ) (V : (ℂ → ℂ) → ℂ) : ℝ≥0∞ :=
  ⨆ (φ : ℕ → ℂ → ℂ) (_ : IsDegTowardSeq Ω p φ), limsup (fun n => (‖V (φ n)‖₊ : ℝ≥0∞)) atTop

/-- **Definition** (§17.1, l. 12739). `μ` is asymptotically extremal: `h*(μ) = h([μ])`. -/
def IsAsymExtremalPlane (Ω : Set ℂ) (μ : ℂ → ℂ) : Prop :=
  μ ∈ beltramiPlane Ω ∧ bStarOmega {fun z => z} Ω μ = hPlane Ω μ

/-- **Definition** (asymptotic Hamilton sequence, §17.1, l. 12737). A degenerating sequence `φₙ` with
`∬ μ φₙ → β([μ])`. -/
def IsAsymHamiltonSeq (Ω : Set ℂ) (μ : ℂ → ℂ) (φ : ℕ → ℂ → ℂ) : Prop :=
  IsDegeneratingSeqOpen (toExt Ω) φ ∧ Tendsto (fun n => ∫ z, μ z * φ n z) atTop
    (𝓝 (((betaSeminormOpen (toExt Ω) fun ψ => ∫ z, μ z * ψ z).toReal : ℝ) : ℂ))

/-- **Unlabelled** (the asymptotic Hamilton–Krushkal, Reich–Strebel criterion, §17.1, l. 12739–12745). `μ` is
asymptotically extremal iff some degenerating sequence satisfies (17.4): `∬ μ φₙ → h*(μ)`.
[CORRECTION] (AUDIT5_GL1518 G15-3) The case `h*(μ) = 0` is added as a disjunct: when `A(Ω)` has no unit vectors
degenerating (e.g. `Ω = ℂ ∖ {0, 1}`, where `A(Ω) = 0`) no sequence exists, while `μ = 0` is asymptotically extremal;
the book silently assumes asymptotic Hamilton sequences exist. -/
theorem para17_1_asym_criterion {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsConnected Ω) (h2 : 2 ≤ (frontier Ω).encard)
    {μ : ℂ → ℂ} (hμ : μ ∈ beltramiPlane Ω) :
    IsAsymExtremalPlane Ω μ ↔ bStarOmega {fun z => z} Ω μ = 0 ∨ ∃ φ : ℕ → ℂ → ℂ, IsDegeneratingSeqOpen (toExt Ω) φ ∧
      Tendsto (fun n => ∫ z, μ z * φ n z) atTop (𝓝 (((bStarOmega {fun z => z} Ω μ).toReal : ℝ) : ℂ)) := by
  sorry

end GardinerLakic2000
