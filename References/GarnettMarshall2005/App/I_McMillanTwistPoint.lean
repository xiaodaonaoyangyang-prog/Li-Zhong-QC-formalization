import References.GarnettMarshall2005.Ch06.S06_PommerenkeExtension

/-!
# Garnett–Marshall, Appendix I: McMillan's twist point theorem

Source: J. B. Garnett, D. E. Marshall, *Harmonic Measure*, Cambridge University Press 2005, Appendix I (pp. 497–503;
`full.md` of the third part, P3:4921–5200). The appendix has no sections, Notes or exercises.

Conventions of the appendix, as modelled here (those of Chapter VI, leader ruling C6). `φ` is a conformal map of `𝔻`
onto a simply connected domain `Ω ⊆ ℂ`, `LiZhongQC.IsConformalOnto φ unitDisc Ω`; `φ(ζ)` is the nontangential limit
(`HasNontangentialLimit`, Ch. I §2) and `Γ_α(ζ)` the cone `LiZhongQC.stolzAngle ζ α`; "almost every" is for
`arcMeasure`. A continuous branch of `arg q` on `𝔻` is `IsArgBranch v q unitDisc` (Ch. II §4). The book notes that
neither (I.1) nor (I.2) depends on the branches chosen (two continuous branches on the connected `𝔻` differ by a
constant multiple of `2π`), and it normalizes a branch `Arg` for Lemma I.3 (P3:5074–5084); so the hypotheses assume
some branch and the conclusions hold for every branch (leader ruling Fb5). Theorem I.1 and the twist point are those of
Chapter VI §4, which point to Pommerenke's (leader ruling Fb5: App. I follows VI.4's final form).

* Theorem I.1 (McMillan's twist point theorem, App. I) — exists: `Pommerenke1992.thm6_18` (the pointer of Chapter VI
  §4: for f analytic and injective in the disc, at almost every t either f is conformal at e^{it}, which is the book's
  finite non-zero angular derivative (a), or f is twisting at e^{it}; twisting asks the argument to be unbounded
  above and below along every curve in the disc ending at the point, which contains the book's (b) on every arc; the
  angular limit it asks for is the nontangential limit φ(ζ) that (b) presupposes; almost every t of the line is almost
  every ζ for arcMeasure; the hypotheses are weaker than a conformal map onto Ω)
* Unlabelled (App. I, P3:4929): since `φ(z) − φ(ζ) ≠ 0`, continuous branches of `arg(φ(z) − φ(ζ))` are defined in `𝔻`
  — omitted: immediate
* Unlabelled (App. I, P3:4929): if `φ(ζ₁) = φ(ζ₂)` and (a) holds at `ζ₁`, then `φ(ζ₁)` is a cone point and (b) cannot
  hold at `ζ₂` — omitted: the consistency claim, not cited (its Chapter VI twin (4.4) is omitted for the same reason)
* Definition (twist point, recalled, App. I, P3:4929: "it is consistent to call `φ(ζ)` a twist point if (b) holds at
  `ζ`") — exists: `Pommerenke1992.IsTwistingAt` (the definition of Chapter VI §4, attached to ζ; App. I's condition
  (b) on every arc is the same as the condition on every curve: an arc is a curve, and a curve in the disc ending at
  ζ contains an arc ending at ζ, a half-open arc of the Peano continuum formed by the curve and ζ)
* Unlabelled (App. I, P3:4929–4943): by Theorem VI.6.1, (a) holds almost everywhere on the preimage of the cone
  points; `ω ≪ Λ₁ ≪ ω` on `φ({(a) holds})` and `ω ⊥ Λ₁` on the twist points; `Λ₁` of the twist points need not be `0`;
  by Theorem VI.4.1 the twisting occurs at almost every Plessner point of `φ′`; the sources of the lemmas — omitted:
  restatements of Theorems VI.4.1 and VI.6.1 and remarks, not cited
* Lemma I.2 (App. I; (I.1), (I.2)) — `lemmaI_2`
* Unlabelled (App. I, P3:4957–4981): the function `h(z, w)`, the estimate
  `|(φ(w) − φ(z))/((1 − |z|²)φ′(z))| ≤ |τ|/(1 − |τ|²)`, `τ = (w − z)/(1 − z̄w)`, from "the conformally invariant form of
  inequality (4.14) of Chapter I", and (I.3) — omitted: devices of the proof of Lemma I.2, used only there; the printed
  denominator 1 − |τ|² of the estimate is a misprint for the square (1 − |τ|)² of the invariant growth theorem (I.4.16),
  as printed the estimate is false for the Koebe function [misprint?] (recorded with cor1_4_4, Ch. I §4)
* Unlabelled (App. I, P3:4983–5072): the proof of Lemma I.2 (the sets `E₁`, the density point, `T_n`, `J_n`, `ψ_n`,
  (I.4), (I.5)) — omitted: steps of a proof
* Unlabelled (App. I, P3:5074–5084): the branch `Arg(φ(z) − φ(ζ))` normalized by `0 ≤ Arg(φ(0) − φ(ζ)) ≤ 2π` —
  omitted: a normalization; Lemma I.3 is stated for every continuous branch (two branches differ by a constant, so
  (I.6) and (I.7) are unaffected)
* Lemma I.3 (App. I; (I.6), (I.7)) — `lemmaI_3`
* Unlabelled (App. I, P3:5100–5199): the proofs of Lemma I.3 ((I.8)–(I.11), Lindelöf's theorem) and of Theorem I.1
  ("(a) holds whenever `φ′` has a non-zero finite nontangential limit", Plessner points of `φ′`) — omitted: steps of
  proofs

Near miss in Pommerenke1992 Ch. 6 (not a pointer): Proposition 6.17 (`prop6_17`, twisting is equivalent to the
unboundedness of the argument in one Stolz angle), related to Lemma I.3 but a different statement.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Real

noncomputable section

namespace GarnettMarshall2005

open LiZhongQC (unitDisc stolzAngle IsConformalOnto)

/-- **Lemma I.2** (App. I; cited in the proof of Theorem I.1, P3:5199, and in Chapter X, P3:1474, "By Lemma I.2 from
Appendix I and Plessner's theorem"). Fix `α > 2`, and let `E` be the set of `ζ ∈ ∂𝔻` such that the nontangential
limit `φ(ζ)` exists and (I.1) `sup_{Γ_α(ζ)} |arg(φ(z) − φ(ζ))| < ∞`. Then almost everywhere on `E`,
(I.2) `sup_{Γ_α(ζ)} arg(φ′(z)) < ∞`.
Modelling: `φ` is the conformal map of `𝔻` onto a simply connected `Ω` (the standing assumption of Theorem I.1);
"Fix `α > 2`" as printed (the inline OCR is doubtful, "F i x α > 2", but the proof needs every point of the arc `J_n`
in `Γ_α(T_n(ζ_n))`, which `α > 2` gives; leader ruling Fb5); (I.1) holds for some continuous branch of
`arg(φ(z) − φ(ζ))` on `𝔻`, and (I.2) is asserted for every continuous branch of `arg φ′(z)` (module docstring; (I.2)
is one-sided, crops checked); "almost everywhere on `E`" is `∀ᵐ ζ ∂arcMeasure, ζ ∈ E → …`. -/
theorem lemmaI_2 {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ unitDisc Ω) {α : ℝ} (hα : 2 < α) :
    ∀ᵐ ζ ∂arcMeasure, (∃ w : ℂ, HasNontangentialLimit φ ζ w ∧ ∃ a : ℂ → ℝ,
        IsArgBranch a (fun z => φ z - w) unitDisc ∧ BddAbove ((fun z => |a z|) '' stolzAngle ζ α)) →
      ∀ b : ℂ → ℝ, IsArgBranch b (deriv φ) unitDisc → BddAbove (b '' stolzAngle ζ α) := by
  sorry

/-- **Lemma I.3** (App. I; McMillan [1969]; cited in the proof of Theorem I.1, P3:5199). If `φ(z)` has nontangential
limit `φ(ζ)` at `ζ` and if `σ ⊂ 𝔻` is an arc with endpoint `ζ` such that (I.6) `sup_{z ∈ σ} Arg(φ(z) − φ(ζ)) ≤ M < ∞`,
then (I.7) `limsup_{𝔻 ∋ z → ζ} Arg(φ(z) − φ(ζ)) < ∞`.
Modelling: `φ` as in Lemma I.2; the arc `σ` is `γ([0, 1))` for `γ` continuous and injective on `[0, 1)` with values in
`𝔻` and `γ(t) → ζ` as `t → 1`; `Arg` is any continuous branch `a` of `arg(φ(z) − φ(ζ))` on `𝔻` (module docstring);
(I.6) is "bounded above on `σ`", and (I.7), a finite upper limit, is "bounded above on `𝔻` near `ζ`" (an eventual bound
along `𝓝[𝔻] ζ`, which avoids the junk of a real `limsup`). -/
theorem lemmaI_3 {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : IsConformalOnto φ unitDisc Ω) {ζ w : ℂ}
    (hw : HasNontangentialLimit φ ζ w) {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Ico 0 1)) (hγi : InjOn γ (Ico 0 1))
    (hγD : γ '' Ico 0 1 ⊆ unitDisc) (hγζ : Tendsto γ (𝓝[<] 1) (𝓝 ζ)) {a : ℂ → ℝ}
    (ha : IsArgBranch a (fun z => φ z - w) unitDisc) (hM : BddAbove (a '' (γ '' Ico 0 1))) :
    ∃ M' : ℝ, ∀ᶠ z in 𝓝[unitDisc] ζ, a z ≤ M' := by
  sorry

end GarnettMarshall2005
