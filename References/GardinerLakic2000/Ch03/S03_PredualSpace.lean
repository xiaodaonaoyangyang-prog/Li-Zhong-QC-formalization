import References.GardinerLakic2000.Ch03.S02_PoincareThetaSeries

/-!
# Gardiner–Lakic 2000, Ch. 3 §3.3 Predual space

Source `teichmuller.txt`, lines 2338–2402 (Chapter 3, §3.3).

* Definition 2 (`β(V) = sup limsup |V(φₙ)|` over degenerating sequences, l. 2369; cited in Ch. 14, l. 9927) —
  `betaSeminorm`
* Definition (`Z₀(R) = {V ∈ Z(R) : β(V) = 0}`, l. 2376; used in Ch. 8, 14) — `zZeroSpace`
* Theorem 5 (`Z₀(R)* ≅ A(R)`, l. 2378) — `thm3_5`
* Remark (`b*(μ)` and the infinitesimal boundary dilatation `b(V)`, l. 2400–2401; used in Ch. 4, 14) —
  `boundaryDilatationStar`, `infBoundaryDilatation`
* Unlabelled (`β(V) ≤ b(V)`, l. 2401) — `para3_3_beta_le_b`

Not items: the `l₁`, `l∞`, `c₀` paragraph (l. 2339–2367, background); "`Z₀(R)` is a closed subspace" (l. 2376, U−).
Modelling: `Z₀(R)` carries the dual norm of `Z(R)`; a bounded functional `L` on `Z₀(R)` is a map on functionals,
restricted by `IsBoundedFunctionalOn`. `b*(μ)`: the infimum over compact `C ⊆ R` of the essential supremum of `|μ|`
on `R ∖ C` (read in charts).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

noncomputable section

namespace GardinerLakic2000

universe u

open LiZhongQC (quadDiffNorm)

variable {R : Type u} [TopologicalSpace R] [ChartedSpace ℂ R]

/-- **Definition 2** (§3.3, l. 2369). `β(V) = sup_{φₙ} limsup_n |V(φₙ)|` over all degenerating sequences in `A(R)`. -/
def betaSeminorm (V : (R → ℂ → ℂ) → ℂ) : ℝ≥0∞ :=
  ⨆ (φ : ℕ → R → ℂ → ℂ) (_ : IsDegeneratingSeq φ), limsup (fun n => (‖V (φ n)‖₊ : ℝ≥0∞)) atTop

/-- **Definition** (§3.3, l. 2376). `Z₀(R)`: the elements of `Z(R)` with vanishing boundary oscillation `β(V) = 0`. -/
def zZeroSpace (R : Type u) [TopologicalSpace R] [ChartedSpace ℂ R] : Set ((R → ℂ → ℂ) → ℂ) :=
  {V | V ∈ zSpace R ∧ betaSeminorm V = 0}

/-- **[CORRECTION/modelling]** (AUDIT4 G1) The binders `[T2Space R] [ConnectedSpace R]` (a Riemann surface; by Radó it is then second
countable and has chart partitions) are added: without them an uncountable disjoint union of discs has no chart partition,
`integrableHolQDSet R = ∅`, and the zero functional `L` has no representing `φ`.
**Theorem 5** (§3.3, l. 2378). The pairing (3.6) restricted to `Z₀(R)` induces an isometric isomorphism of
`Z₀(R)*` onto `A(R)`: for `φ ∈ A(R)` the functional `V ↦ V(φ)` on `Z₀(R)` has norm `‖φ‖`, and every bounded linear
functional on `Z₀(R)` is of this form for a unique `φ ∈ A(R)`. -/
theorem thm3_5 [T2Space R] [ConnectedSpace R] [IsManifold 𝓘(ℂ) ω R] :
    (∀ φ ∈ integrableHolQDSet R,
      ENNReal.ofReal (dualNormOn (zZeroSpace R)
        (fun V => ENNReal.ofReal (dualNormOn (integrableHolQDSet R) quadDiffNorm V)) (fun V => V φ)) =
        quadDiffNorm φ) ∧
    ∀ L : ((R → ℂ → ℂ) → ℂ) → ℂ,
      IsBoundedFunctionalOn (zZeroSpace R)
        (fun V => ENNReal.ofReal (dualNormOn (integrableHolQDSet R) quadDiffNorm V)) L →
      ∃ φ ∈ integrableHolQDSet R, (∀ V ∈ zZeroSpace R, L V = V φ) ∧
        ∀ ψ ∈ integrableHolQDSet R, (∀ V ∈ zZeroSpace R, L V = V ψ) → quadDiffNorm (φ - ψ) = 0 := by
  sorry

/-- **Remark** (§3.3, l. 2400). `b*(μ)`: the infimum over compact subsets `C` of `R` of the essential supremum of
`|μ|` on `R ∖ C`. -/
def boundaryDilatationStar (μ : R → ℂ → ℂ) : ℝ≥0∞ :=
  ⨅ (C : Set R) (_ : IsCompact C),
    ⨆ x : R, eLpNorm (μ x) ⊤ (volume.restrict ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Cᶜ))

/-- **Remark** (§3.3, l. 2401). The infinitesimal boundary dilatation `b(V)` of `V ∈ Z(R)`: the infimum of `b*(μ)`
over the Beltrami differentials `μ` representing `V`. -/
def infBoundaryDilatation (V : (R → ℂ → ℂ) → ℂ) : ℝ≥0∞ :=
  ⨅ (μ : R → ℂ → ℂ) (_ : μ ∈ beltramiSpace R ∧ ∀ φ ∈ integrableHolQDSet R, V φ = pairingRS φ μ),
    boundaryDilatationStar μ

/-- **Unlabelled** (§3.3, l. 2401; Exercise 16, equality in Ch. 14). `β(V) ≤ b(V)`. -/
theorem para3_3_beta_le_b [IsManifold 𝓘(ℂ) ω R] {V : (R → ℂ → ℂ) → ℂ} (hV : V ∈ zSpace R) :
    betaSeminorm V ≤ infBoundaryDilatation V := by
  -- `V ∈ Z(R)` is not needed: the bound holds for every representative `μ` of any functional `V` (and `b(V) = ⊤`
  -- when `V` has none); the statement stays true without `hV`
  have _hV := hV
  unfold betaSeminorm infBoundaryDilatation
  refine iSup₂_le fun φ hφ => le_iInf₂ fun μ hμ => ?_
  unfold boundaryDilatationStar
  refine le_iInf₂ fun C hC => ?_
  -- `‖V φₙ‖ ≤ ‖μ‖∞ ∬_C |φₙ| + ‖μ|_{R∖C}‖∞` for every `n`, and `∬_C |φₙ| → 0`
  have hμfin : beltramiNormRS μ ≠ ⊤ := by
    obtain ⟨k, -, hbd⟩ := hμ.1
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal k) ENNReal.ofReal_ne_top (iSup_le fun x => ?_)
    rw [eLpNorm_exponent_top (hbd x).1]
    exact eLpNormEssSup_le_of_ae_bound (hbd x).2
  have hbound : ∀ n, (‖V (φ n)‖₊ : ℝ≥0∞) ≤ beltramiNormRS μ *
      LiZhongQC.surfaceIntegral (φ n) (fun y z => C.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z)) +
      ⨆ x : R, eLpNorm (μ x) ⊤ (volume.restrict ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Cᶜ)) := by
    intro n
    have h1 := gl31_pairingRS_split (hφ.1 n).1 hμ.1 C
    rw [(hφ.1 n).2, mul_one, ← hμ.2 (φ n) (hφ.1 n).1] at h1
    exact h1
  have hlim : Tendsto (fun n => beltramiNormRS μ *
      LiZhongQC.surfaceIntegral (φ n) (fun y z => C.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z)) +
      ⨆ x : R, eLpNorm (μ x) ⊤ (volume.restrict ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Cᶜ))) atTop
      (𝓝 (beltramiNormRS μ * 0 +
        ⨆ x : R, eLpNorm (μ x) ⊤ (volume.restrict ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Cᶜ)))) :=
    (ENNReal.Tendsto.const_mul (gl31_degenerating_cpt hφ hC) (Or.inr hμfin)).add tendsto_const_nhds
  rw [mul_zero, zero_add] at hlim
  calc limsup (fun n => (‖V (φ n)‖₊ : ℝ≥0∞)) atTop
      ≤ limsup (fun n => beltramiNormRS μ *
          LiZhongQC.surfaceIntegral (φ n) (fun y z => C.indicator (fun _ => (1 : ℝ≥0∞)) ((chartAt ℂ y).symm z)) +
          ⨆ x : R, eLpNorm (μ x) ⊤ (volume.restrict ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Cᶜ))) atTop :=
        limsup_le_limsup (Eventually.of_forall hbound)
    _ = ⨆ x : R, eLpNorm (μ x) ⊤ (volume.restrict ((chartAt ℂ x).target ∩ (chartAt ℂ x).symm ⁻¹' Cᶜ)) :=
        hlim.limsup_eq

end GardinerLakic2000
