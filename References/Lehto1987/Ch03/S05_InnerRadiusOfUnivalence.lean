import References.Lehto1987.Ch03.S04_SpaceOfSchwarzianDerivatives

/-!
# Lehto, Chapter III §5: Inner radius of univalence

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. III §5 (`full.md`
P1:4339–4737).

Conventions (see §1–§4 and Chapter II §1). Domains are subsets of `ℂ̄`; "simply connected with more than one boundary
point" is `Gehring1978.IsHypSimplyConnectedExt`; meromorphic functions are read as in Chapter II
(`IsLocUnivMeroExt`, `Gehring1978.IsConformalExt`, `Gehring1978.imageExt`); the norm `‖φ‖_A` is
`Gehring1978.hypNorm` with Lehto's density `η_A` (`Gehring1978.hypDensity`); quasidiscs are
`References.IsQuasidiskExt`; quasiconformal extensions to the plane are `IsQCExtensionOf`.

The half-planes are mirrored as in §4 (decision B0.2): `f_μ` is conformal in the lower half-plane `H′`, the space
`Q_H` is `LiZhongQC.bersSpaceL`, `U_H` is `LiZhongQC.schwarzianUnivalentSet`, and `T_H(1)` is the range of the Bers
map `LiZhongQC.bersMapU`. Accordingly the quasidisc `A` of §5.2 is a normalized quasidisc in the sense of §1.5
(`IsNormalizedQuasidisc`, the image `f_{μ₀}(H′)`), and the Beltrami coefficients of `T_A` live in the complement of
the closure of `A`. Elements of `Q_A` are compared on `A`; the sets `U_A`, `T_A(1)` hold the Schwarzians restricted to
`A` (`Set.indicator`, as `LiZhongQC.schwarzianUnivalentSet`).

Helpers (not book notions): `beltramiQD` (the Beltrami coefficients of `T_A`) and `teichRelQD` (their equivalence).

* Definition (inner radius of univalence `σ_I(A)`, §5.1) — `innerRadius`
* Unlabelled (§5.1, P1:4355): `a = 0` is admissible — omitted: immediate from (1.2) of II.1.1 (U−)
* Unlabelled (§5.1, P1:4355): `σ_I` is invariant under Möbius transformations — `para3_5_1_a`
* Unlabelled (§5.1, P1:4357): the set `U_A` is closed, and `‖S_f‖_A = σ_I(A)` implies that `f` is univalent —
  `para3_5_1_b`
* Unlabelled (§5.1, P1:4359): `σ_I(A) > 0` if and only if `A` is a quasidisc — `para3_5_1_c`
* Unlabelled (§5.1, P1:4361–4366): `σ_I(A) = 2` for a disc — `para3_5_1_d`
* Definition (the universal Teichmüller space `T_A`, §5.2) — `univTeichQD`
* Definition (the Teichmüller distance of `T_A`, §5.2) — `teichDistQD`
* Unlabelled (§5.2, P1:4377): Theorem 1.2 holds for `A`: the points of `T_A` are represented by the conformal
  mappings of `A` — `para3_5_2`
* Unlabelled (§5.2, P1:4379): `A` is a point of `T_H` — omitted: restates (1.3) (`eq3_1_3`)
* Formula (5.1) (§5.2) — `eq3_5_1`
* Definition (the spaces `Q_A`, `U_A` and `T_A(1)`, §5.2) — `QA`, `UA`, `TA1`
* Unlabelled (§5.2, P1:4389): `U_A ⊂ Q_A` — omitted: Theorem II.2.3 (`thm2_2_3`)
* Unlabelled (§5.2, P1:4393–4397): the two-sided estimate of `‖S_w‖_A` — omitted: a step of the proof of (5.2)
* Formula (5.2) (§5.2) — `eq3_5_2`
* Formula (5.3) (§5.3) — `eq3_5_3`
* Formula (5.4) (§5.3) — `eq3_5_4`
* Unlabelled (§5.3, P1:4426–4435): `‖S_f‖_A < σ_I(A)` implies that `f` is univalent and has a quasiconformal
  extension to the plane — `para3_5_3_a`
* Formula (5.5) (§5.3) — `eq3_5_5`
* Unlabelled (§5.3, P1:4443): `B(0, σ_I(A))` is the largest open ball of `Q_A` about the origin in `T_A(1)` — omitted:
  a restatement of (5.5) (U−)
* Unlabelled (§5.3, P1:4443): `σ_I(A)` is the distance from `S_h` to `∂T_H(1)` — `para3_5_3_b`
* Theorem 5.1 (§5.3) — `thm3_5_1`
* Unlabelled (§5.3, P1:4451): `δ(A)` is the distance from `S_h` to the origin — omitted: the definition of `δ`
  (`discDistance`, U−)
* Lemma 5.1 (§5.4) — `lemma3_5_1`
* Formula (5.6) (§5.4) — `lemma3_5_1` (the conclusion of Lemma 5.1)
* Formula (5.7) (§5.4) — omitted: a step of the proof of Lemma 5.1
* Remark (§5.4, P1:4507) — `rem3_5_4`
* Unlabelled (§5.4, P1:4513–4523): the half-plane, the disc and the ellipse in (5.6) — omitted: examples, not cited
* Theorem 5.2 (§5.5) — `thm3_5_2`
* Formula (5.8) (§5.5) — `thm3_5_2` (the statement of Theorem 5.2)
* Formula (5.9) (§5.5) — omitted: a step of the proof of Theorem 5.2
* Lemma 5.2 (§5.6) — `lemma3_5_2`
* Lemma 5.3 (§5.6) — `lemma3_5_3`
* Unlabelled (§5.6, P1:4656–4672): estimates for the exterior of an ellipse — omitted: an application, not cited
* Formula (5.10) (§5.6) — omitted: an application of Lemma 5.2 to polygons, not cited
* Formula (5.11) (§5.6) — omitted: quoted (Lehtinen, Calvis), not cited
* Formula (5.12) (§5.6) — omitted: quoted (Lehtinen, Calvis), not cited
* Unlabelled (§5.7, P1:4692–4697): `2 ≤ δ(A) + σ_I(A) ≤ 6` — `para3_5_7`
* Unlabelled (§5.7, P1:4699–4704): extremal domains for the left-hand inequality — omitted: examples, not cited
* Theorem 5.3 (§5.7) — `thm3_5_3_a`, `thm3_5_3_b`
* Formula (5.13) (§5.7) — `thm3_5_3_a` (the statement of Theorem 5.3)
* Unlabelled (§5.7, P1:4728–4736): distances in `T_H(1)` below 2, `K`-quasidiscs, open questions — omitted: a remark
  and open problems (U−)
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace Lehto1987

open LiZhongQC (ExtPlane extInf toExt lowerHalf BeltramiH UniversalTeichmuller teichSetoid normalizedSolution
  bersSpaceL bersMapU schwarzianUnivalentSet schwarzian maxDilatation complexDilatation dz dzbar IsMobius mobiusExt)
open References (finitePart IsQuasidiskExt)
open Gehring1978 (hypNorm hypDensity IsHypSimplyConnectedExt IsConformalExt imageExt)

/-! ## §5.1 Definition of the inner radius of univalence -/

/-- **Definition** (inner radius of univalence, Ch. III §5.1):
`σ_I(A) = sup {a | ‖S_f‖_A ≤ a ⇒ f univalent in A}`, `f` meromorphic in `A`.
Modelling: the admissible `a` are those for which `A` is an `a`-Schwarzian domain (II.4.4, `IsEpsSchwarzianDomain`:
`f` locally injective meromorphic, univalence = `Gehring1978.IsConformalExt`); `[0, ∞]`-valued. Junk: `0` for a set
that is not a simply connected domain with more than one boundary point (not a domain of the book). Near miss:
`LiZhongQC.innerUnivalenceRadius` (plane domains, Li Zhong's norm, a quarter of Lehto's). -/
def innerRadius (A : Set ExtPlane) : ℝ≥0∞ :=
  ⨆ (a : ℝ) (_ : IsEpsSchwarzianDomain A a), ENNReal.ofReal a

/-- **Unlabelled** (Ch. III §5.1, P1:4355). The inner radius of univalence is invariant under Möbius
transformations: Möbius equivalent domains have the same `σ_I`. -/
theorem para3_5_1_a {A B : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) (hAB : IsMobiusEquivalent A B) :
    innerRadius A = innerRadius B := by
  sorry

/-- **Unlabelled** (Ch. III §5.1, P1:4357). The set `{S_f | f univalent in A}` is closed for the hyperbolic sup norm,
and the supremum in the definition of `σ_I(A)` is a maximum: if `‖S_f‖_A = σ_I(A)`, then `f` is univalent.
Modelling: closedness: a holomorphic `φ` which is the `‖·‖_A`-limit of Schwarzians of univalent functions is the
Schwarzian of a univalent function; the maximum: `‖S_f‖_A ≤ σ_I(A)` suffices. -/
theorem para3_5_1_b {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) :
    (∀ (fn : ℕ → ℂ → ℂ) (φ : ℂ → ℂ), (∀ n, IsConformalExt (fn n) A) → DifferentiableOn ℂ φ (finitePart A) →
      Tendsto (fun n => hypNorm (fun z => schwarzian (fn n) z - φ z) A) atTop (𝓝 0) →
      ∃ f : ℂ → ℂ, IsConformalExt f A ∧ EqOn (schwarzian f) φ (finitePart A)) ∧
    ∀ f : ℂ → ℂ, IsLocUnivMeroExt f A → hypNorm (schwarzian f) A ≤ innerRadius A → IsConformalExt f A := by
  sorry

/-- **Unlabelled** (Ch. III §5.1, P1:4359; Theorems II.4.1 and II.4.2). `σ_I(A) > 0` if and only if `A` is a
quasidisc. -/
theorem para3_5_1_c {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) : 0 < innerRadius A ↔ IsQuasidiskExt A := by
  sorry

/-- **Unlabelled** (Ch. III §5.1, P1:4361–4366; Theorem II.5.2). For a disc `A`, `σ_I(A) = 2`. -/
theorem para3_5_1_d {A : Set ExtPlane} (hA : IsDiscExt A) : innerRadius A = 2 := by
  sorry

/-! ## §5.2 Isomorphic Teichmüller spaces -/

/-- Helper (Beltrami coefficients for `T_A`, Ch. III §5.2): measurable `μ` with `‖μ‖∞ < 1` vanishing
on the closure of `A` (the coefficients of the quasiconformal self-maps of the complement of `A`, extended by `0`), as
`LiZhongQC.BeltramiH` for `A = H′`. -/
def beltramiQD (A : Set ExtPlane) : Type :=
  {μ : ℂ → ℂ // (∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ LiZhongQC.IsBeltramiCoeff μ univ k) ∧ ∀ z ∈ finitePart (closure A), μ z = 0}

/-- Helper (equivalence for `T_A`, Ch. III §5.2): the normalized solutions `f_μ`, `f_ν` (fixing `0`,
`1`, `∞`) agree on the boundary of `A`, as `LiZhongQC.teichSetoid` for `A = H′`. -/
def teichRelQD (A : Set ExtPlane) (μ ν : beltramiQD A) : Prop :=
  ∀ z ∈ finitePart (frontier A), normalizedSolution μ.1 z = normalizedSolution ν.1 z

/-- **Definition** (the universal Teichmüller space `T_A` of a normalized quasidisc `A`, Ch. III §5.2): defined by
the quasiconformal self-maps of the complement of `A` fixing `0`, `1`, `∞`, exactly as `T` in 1.1.
Modelling: the classes of `beltramiQD A` under `teichRelQD A` (as `LiZhongQC.UniversalTeichmuller` for `A = H′`). -/
def univTeichQD (A : Set ExtPlane) : Type := Quot (teichRelQD A)

/-- **Definition** (the Teichmüller distance of `T_A`, Ch. III §5.2): `τ_A(p, q) = ½ inf log K`, the infimum of the
maximal dilatations of `f_ν ∘ f_μ⁻¹` in `f_μ(A*)` over representatives `μ ∈ p`, `ν ∈ q`, `A*` the complement of the
closure of `A` (as `teichDist` for `A = H′`). -/
def teichDistQD (A : Set ExtPlane) (p q : univTeichQD A) : ℝ :=
  (1 / 2) * sInf {d | ∃ μ ν : beltramiQD A, Quot.mk (teichRelQD A) μ = p ∧ Quot.mk (teichRelQD A) ν = q ∧
    d = Real.log (maxDilatation (normalizedSolution ν.1 ∘ Function.invFunOn (normalizedSolution μ.1) univ)
      (normalizedSolution μ.1 '' finitePart (closure A)ᶜ)).toReal}

/-- **Unlabelled** (Ch. III §5.2, P1:4377). Theorem 1.2 holds for a normalized quasidisc `A`: two coefficients are
equivalent if and only if their normalized solutions agree in `A`, so that the points of `T_A` are represented by the
conformal mappings `f_μ|A`. -/
theorem para3_5_2 {A : Set ExtPlane} (hA : IsNormalizedQuasidisc A) (μ ν : beltramiQD A) :
    teichRelQD A μ ν ↔ EqOn (normalizedSolution μ.1) (normalizedSolution ν.1) (finitePart A) := by
  sorry

/-- **Formula (5.1)** (Ch. III §5.2). For `A = f_{μ₀}(H′)`, the transformation `f_μ ↦ f_μ ∘ (f_{μ₀}⁻¹|A)` is a
bijective isometry of `T_H` onto `T_A`; it maps `[μ₀]` to the origin of `T_A`, and `[μ]` to the point represented by
the complex dilatation of `f_μ ∘ f_{μ₀}⁻¹`.
Modelling: a map `Φ`; the origin of `T_A` is the class of the zero coefficient; distances are `teichDist` and
`teichDistQD`. -/
theorem eq3_5_1 (μ₀ : BeltramiH) {A : Set ExtPlane} (hA : A = toExt (normalizedSolution μ₀.1 '' lowerHalf)) :
    ∃ Φ : UniversalTeichmuller → univTeichQD A, Function.Bijective Φ ∧
      (∀ p q, teichDistQD A (Φ p) (Φ q) = teichDist p q) ∧
      (∀ ν : beltramiQD A, ν.1 = 0 → Φ (Quotient.mk teichSetoid μ₀) = Quot.mk (teichRelQD A) ν) ∧
      ∀ (μ : BeltramiH) (ν : beltramiQD A),
        (∀ᵐ z : ℂ, ν.1 z = complexDilatation (normalizedSolution μ.1 ∘
          Function.invFunOn (normalizedSolution μ₀.1) univ) z) →
        Φ (Quotient.mk teichSetoid μ) = Quot.mk (teichRelQD A) ν := by
  sorry

/-- **Definition** (the space `Q_A`, Ch. III §5.2): the functions `φ` holomorphic in `A` with finite norm
`sup |φ| η_A⁻²`.
Modelling: holomorphic at the finite points of `A` (at `∞ ∈ A` the finite norm forces the zero of order `≥ 4`), as
`LiZhongQC.bersSpaceL` for `A = H′`. -/
def QA (A : Set ExtPlane) : Set (ℂ → ℂ) := {φ | DifferentiableOn ℂ φ (finitePart A) ∧ hypNorm φ A < ⊤}

/-- **Definition** (the set `U_A`, Ch. III §5.2): `U_A = {S_f | f univalent in A}`.
Modelling: the Schwarzians restricted to `A` (`Set.indicator`), as `LiZhongQC.schwarzianUnivalentSet`. -/
def UA (A : Set ExtPlane) : Set (ℂ → ℂ) :=
  {φ | ∃ f : ℂ → ℂ, IsConformalExt f A ∧ φ = (finitePart A).indicator (schwarzian f)}

/-- **Definition** (the set `T_A(1)`, Ch. III §5.2): `T_A(1) = {S_f ∈ U_A | f has a quasiconformal extension to the
plane}`. -/
def TA1 (A : Set ExtPlane) : Set (ℂ → ℂ) :=
  {φ | ∃ f : ℂ → ℂ, IsConformalExt f A ∧ (∃ F : ExtPlane → ExtPlane, IsQCExtensionOf F f A) ∧
    φ = (finitePart A).indicator (schwarzian f)}

/-- **Formula (5.2)** (Ch. III §5.2). For `A = f_{μ₀}(H′)`, `S_f ↦ S_{f ∘ f_{μ₀}⁻¹|A}` is a bijective isometry of
`Q_H` onto `Q_A` which maps `U_H` onto `U_A` and `T_H(1)` onto `T_A(1)`; (5.1) followed by `[ν] ↦ S_{f_ν|A}` is
`[μ] ↦ S_{f_μ|H′}` followed by (5.2).
Modelling: stated for the inverse map `Λ : S_w ↦ S_{w ∘ f_{μ₀}}` of `Q_A` onto `Q_H` (it avoids `f_{μ₀}⁻¹`), on the
representatives restricted to the domains; the commutation for `[μ] ↦ [ν]` with `f_ν = f_μ ∘ f_{μ₀}⁻¹` in `A`. -/
theorem eq3_5_2 (μ₀ : BeltramiH) {A : Set ExtPlane} (hA : A = toExt (normalizedSolution μ₀.1 '' lowerHalf)) :
    ∃ Λ : (ℂ → ℂ) → ℂ → ℂ,
      (∀ w : ℂ → ℂ, IsLocUnivMeroExt w A →
        Λ ((finitePart A).indicator (schwarzian w)) = lowerHalf.indicator (schwarzian (w ∘ normalizedSolution μ₀.1))) ∧
      BijOn Λ ((finitePart A).indicator '' QA A) (lowerHalf.indicator '' bersSpaceL) ∧
      (∀ φ ∈ QA A, ∀ ψ ∈ QA A, hypNorm (Λ ((finitePart A).indicator φ) - Λ ((finitePart A).indicator ψ))
        (toExt lowerHalf) = hypNorm (φ - ψ) A) ∧
      Λ '' UA A = schwarzianUnivalentSet ∧ Λ '' TA1 A = range bersMapU ∧
      ∀ (μ : BeltramiH) (ν : beltramiQD A), EqOn (normalizedSolution ν.1)
        (normalizedSolution μ.1 ∘ Function.invFunOn (normalizedSolution μ₀.1) lowerHalf) (finitePart A) →
        Λ ((finitePart A).indicator (schwarzian (normalizedSolution ν.1))) =
          bersMapU (Quotient.mk teichSetoid μ) := by
  sorry

/-! ## §5.3 Inner radius and quasiconformal extensions -/

/-- **Formula (5.3)** (Ch. III §5.3). Let `A` be a quasidisc and `h : H′ → A` a conformal mapping. Then
`S_f ↦ S_{f ∘ h⁻¹}` is a bijective isometry of `Q_H` onto `Q_A` (mapping `U_H` onto `U_A` and `T_H(1)` onto
`T_A(1)`).
Modelling: as `eq3_5_2`, for the inverse map `Λ : S_w ↦ S_{w ∘ h}`; the correspondence of `U` and `T(1)` is the
book's "generalizing (5.2)". -/
theorem eq3_5_3 {A : Set ExtPlane} (hA : IsQuasidiskExt A) {h : ℂ → ℂ} (hh : IsConformalExt h (toExt lowerHalf))
    (himg : imageExt h (toExt lowerHalf) = A) :
    ∃ Λ : (ℂ → ℂ) → ℂ → ℂ,
      (∀ w : ℂ → ℂ, IsLocUnivMeroExt w A →
        Λ ((finitePart A).indicator (schwarzian w)) = lowerHalf.indicator (schwarzian (w ∘ h))) ∧
      BijOn Λ ((finitePart A).indicator '' QA A) (lowerHalf.indicator '' bersSpaceL) ∧
      (∀ φ ∈ QA A, ∀ ψ ∈ QA A, hypNorm (Λ ((finitePart A).indicator φ) - Λ ((finitePart A).indicator ψ))
        (toExt lowerHalf) = hypNorm (φ - ψ) A) ∧
      Λ '' UA A = schwarzianUnivalentSet ∧ Λ '' TA1 A = range bersMapU := by
  sorry

/-- **Formula (5.4)** (Ch. III §5.3). For every quasidisc `A`, `T_A(1) = int U_A`.
Modelling: the interior in `Q_A`: the points of `U_A` about which a `‖·‖_A`-ball of `Q_A` lies in `U_A`. -/
theorem eq3_5_4 {A : Set ExtPlane} (hA : IsQuasidiskExt A) :
    TA1 A = {φ | φ ∈ UA A ∧ ∃ ε > (0 : ℝ), ∀ ψ ∈ QA A, hypNorm (ψ - φ) A < ENNReal.ofReal ε →
      (finitePart A).indicator ψ ∈ UA A} := by
  sorry

/-- **Unlabelled** (Ch. III §5.3, P1:4426–4435). Let `A` be a quasidisc. If `‖S_f‖_A < σ_I(A)`, then `f` is
univalent in `A` and has a quasiconformal extension to the plane. -/
theorem para3_5_3_a {A : Set ExtPlane} (hA : IsQuasidiskExt A) {f : ℂ → ℂ} (hf : IsLocUnivMeroExt f A)
    (hS : hypNorm (schwarzian f) A < innerRadius A) :
    IsConformalExt f A ∧ ∃ F : ExtPlane → ExtPlane, IsQCExtensionOf F f A := by
  sorry

/-- **Formula (5.5)** (Ch. III §5.3). For a quasidisc `A`,
`σ_I(A) = inf {‖S_f‖_A | f univalent in A, f(A) not a quasidisc}`. -/
theorem eq3_5_5 {A : Set ExtPlane} (hA : IsQuasidiskExt A) :
    innerRadius A = ⨅ (f : ℂ → ℂ) (_ : IsConformalExt f A ∧ ¬ IsQuasidiskExt (imageExt f A)),
      hypNorm (schwarzian f) A := by
  sorry

/-- **Unlabelled** (Ch. III §5.3, P1:4443). If `h` is a conformal mapping of `H′` onto a quasidisc `A`, then
`σ_I(A)` is the distance from the point `S_h` to the boundary of `T_H(1)` in `Q_H`.
Modelling: the boundary points are the `φ ∈ Q_H` outside `T_H(1)` (the range of `LiZhongQC.bersMapU`) which are limits
of points of `T_H(1)`. -/
theorem para3_5_3_b {A : Set ExtPlane} (hA : IsQuasidiskExt A) {h : ℂ → ℂ} (hh : IsConformalExt h (toExt lowerHalf))
    (himg : imageExt h (toExt lowerHalf) = A) :
    innerRadius A = ⨅ (φ : ℂ → ℂ) (_ : φ ∈ bersSpaceL ∧ lowerHalf.indicator φ ∉ range bersMapU ∧
      ∀ ε > (0 : ℝ), ∃ ψ ∈ bersSpaceL, lowerHalf.indicator ψ ∈ range bersMapU ∧
        hypNorm (ψ - φ) (toExt lowerHalf) < ENNReal.ofReal ε),
      hypNorm (φ - schwarzian h) (toExt lowerHalf) := by
  sorry

/-- **Theorem 5.1** (Ch. III §5.3). The largest open ball of `Q_H` which is centred at the point `S_{f_μ|H}` and lies
in `T_H(1)` has the radius `σ_I(f_μ(H))`.
Modelling: mirrored (`H′`, decision B0.2): the ball of radius `σ_I(f_μ(H′))` about `S_{f_μ|H′}` lies in `T_H(1)`, and
every larger ball does not. -/
theorem thm3_5_1 (μ : BeltramiH) :
    (∀ ψ ∈ bersSpaceL, hypNorm (ψ - bersMapU (Quotient.mk teichSetoid μ)) (toExt lowerHalf) <
      innerRadius (toExt (normalizedSolution μ.1 '' lowerHalf)) → lowerHalf.indicator ψ ∈ range bersMapU) ∧
    ∀ r : ℝ≥0∞, innerRadius (toExt (normalizedSolution μ.1 '' lowerHalf)) < r →
      ∃ ψ ∈ bersSpaceL, hypNorm (ψ - bersMapU (Quotient.mk teichSetoid μ)) (toExt lowerHalf) < r ∧
        lowerHalf.indicator ψ ∉ range bersMapU := by
  sorry

/-! ## §5.4 Inner radius and quasiconformal reflections -/

/-- **Lemma 5.1** (Ch. III §5.4). Let `A` be a bounded quasidisc which can be exhausted by the domains
`A_r = {rz | z ∈ A}`, `0 < r < 1`, and `λ` a quasiconformal reflection in `∂A` which is continuously differentiable
off `∂A`. Let `A′ = A ∖ {λ⁻¹(∞)}`. Then
`σ_I(A) ≥ 2 inf_{z ∈ A′} (|∂̄λ(z)| − |∂λ(z)|)/(|λ(z) − z|² η_A(z)²)` (5.6).
Modelling: `A` is a bounded set of the finite plane; the exhaustion is `r · cl A ⊂ A` for `0 < r < 1`; `λ` is a
`K`-quasiconformal reflection (`IsKQCReflection`) of `ℂ̄` with finite part `l`, continuously differentiable at the
finite points off `∂A` where `λ` is finite. -/
theorem lemma3_5_1 {A : Set ℂ} (hA : IsQuasidiskExt (toExt A)) (hAb : Bornology.IsBounded A)
    (hex : ∀ r : ℝ, 0 < r → r < 1 → (fun z : ℂ => (r : ℂ) * z) '' closure A ⊆ A) {K : ℝ}
    {Λ : ExtPlane → ExtPlane} (hΛ : IsKQCReflection (frontier (toExt A)) (toExt A) (closure (toExt A))ᶜ K Λ)
    {l : ℂ → ℂ} (hl : ∀ z : ℂ, Λ (z : ExtPlane) ≠ extInf → Λ (z : ExtPlane) = ((l z : ℂ) : ExtPlane))
    (hC1 : ContDiffOn ℝ 1 l {z : ℂ | (z : ExtPlane) ∉ frontier (toExt A) ∧ Λ (z : ExtPlane) ≠ extInf}) :
    2 * ⨅ z ∈ {z ∈ A | Λ (z : ExtPlane) ≠ extInf},
        ENNReal.ofReal ((‖dzbar l z‖ - ‖dz l z‖) / (‖l z - z‖ ^ 2 * hypDensity (toExt A) z ^ 2)) ≤
      innerRadius (toExt A) := by
  sorry

/-- **Remark** (Ch. III §5.4, P1:4507). Let `h` be a Möbius transformation, `φ = h ∘ λ ∘ h⁻¹` and `ζ = h(z)`. Then
`(|∂̄λ(z)| − |∂λ(z)|)/(|λ(z) − z|² η_A(z)²) = (|∂̄φ(ζ)| − |∂φ(ζ)|)/(|φ(ζ) − ζ|² η_{h(A)}(ζ)²)`.
Modelling: `h(w) = (aw + b)/(cw + d)`; at a point `z` of `A` where `λ` is `C¹`, with `z`, `λ(z)` off the pole of `h`;
`φ ∘ h = h ∘ λ` near `z`. -/
theorem rem3_5_4 {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) {a b c d : ℂ} (had : a * d - b * c ≠ 0)
    {l φ : ℂ → ℂ} {z : ℂ} (hz : (z : ExtPlane) ∈ A) (hl : ContDiffAt ℝ 1 l z) (hlz : l z ≠ z)
    (hcz : c * z + d ≠ 0) (hcl : c * l z + d ≠ 0)
    (hφ : ∀ᶠ w in 𝓝 z, φ ((a * w + b) / (c * w + d)) = (a * l w + b) / (c * l w + d)) :
    (‖dzbar l z‖ - ‖dz l z‖) / (‖l z - z‖ ^ 2 * hypDensity A z ^ 2) =
      (‖dzbar φ ((a * z + b) / (c * z + d))‖ - ‖dz φ ((a * z + b) / (c * z + d))‖) /
        (‖φ ((a * z + b) / (c * z + d)) - (a * z + b) / (c * z + d)‖ ^ 2 *
          hypDensity (mobiusExt a b c d '' A) ((a * z + b) / (c * z + d)) ^ 2) := by
  sorry

/-! ## §5.5 Inner radius of sectors -/

/-- **Theorem 5.2** (Ch. III §5.5, Lehto, Lehtinen). Let `A` be the sector `{z | 0 < arg z < kπ}`, `0 < k < 2`. Then
`σ_I(A) = 2k²` if `0 < k ≤ 1` and `σ_I(A) = 4k − 2k²` if `1 < k < 2` (5.8).
Modelling: the sector is `{r e^{iθ} | r > 0, 0 < θ < kπ}` (the angle may exceed `π`). -/
theorem thm3_5_2 {k : ℝ} (hk0 : 0 < k) (hk2 : k < 2) :
    (k ≤ 1 → innerRadius (toExt {z : ℂ | ∃ r θ : ℝ, 0 < r ∧ 0 < θ ∧ θ < k * Real.pi ∧ z = r * exp (θ * I)}) =
      ENNReal.ofReal (2 * k ^ 2)) ∧
    (1 < k → innerRadius (toExt {z : ℂ | ∃ r θ : ℝ, 0 < r ∧ 0 < θ ∧ θ < k * Real.pi ∧ z = r * exp (θ * I)}) =
      ENNReal.ofReal (4 * k - 2 * k ^ 2)) := by
  sorry

/-! ## §5.6 Inner radius of ellipses and polygons -/

/-- **Lemma 5.2** (Ch. III §5.6, Lehtinen). Let `A` be a quasidisc contained in a domain `B_k` Möbius equivalent to the
sector `A_k = {z | |arg z| < kπ/2}`. If `0 < k ≤ 1` and a vertex of `B_k` lies on `∂A`, then `σ_I(A) ≤ 2k²`. If
`1 < k < 2` and there are points `z₁, z₂ ∈ ∂A` with `g(z₁) = e^{ikπ/2}`, `g(z₂) = e^{−ikπ/2}` for a Möbius
transformation `g` of `B_k` onto `A_k`, then `σ_I(A) ≤ 4k − 2k²`.
Modelling: `B_k = M(A_k)` for a Möbius `M` (`= g⁻¹`); its vertices are `M(0)`, `M(∞)`, and `z ↦ 1/z` maps `A_k` onto
itself, so the vertex may be taken to be `M(0)`. [proof slip] P1:4644 prints `4k − k²` for `4k − 2k²`. -/
theorem lemma3_5_2 {A : Set ExtPlane} (hA : IsQuasidiskExt A) {k : ℝ} (hk0 : 0 < k) (hk2 : k < 2) :
    (k ≤ 1 → (∃ M : ExtPlane → ExtPlane, IsMobius M ∧
        A ⊆ M '' toExt {z : ℂ | z ≠ 0 ∧ |arg z| < k * Real.pi / 2} ∧ M ((0 : ℂ) : ExtPlane) ∈ frontier A) →
      innerRadius A ≤ ENNReal.ofReal (2 * k ^ 2)) ∧
    (1 < k → (∃ M : ExtPlane → ExtPlane, IsMobius M ∧
        A ⊆ M '' toExt {z : ℂ | z ≠ 0 ∧ |arg z| < k * Real.pi / 2} ∧
        M ((exp ((k * Real.pi / 2 : ℝ) * I) : ℂ) : ExtPlane) ∈ frontier A ∧
        M ((exp ((-(k * Real.pi / 2) : ℝ) * I) : ℂ) : ExtPlane) ∈ frontier A) →
      innerRadius A ≤ ENNReal.ofReal (4 * k - 2 * k ^ 2)) := by
  sorry

/-- **Lemma 5.3** (Ch. III §5.6, Lehtinen). Let `A` be a quasidisc. If every two-point subset of `A` is contained in
the closure of a quasidisc `B ⊂ A` for which `σ_I(B) ≥ m`, then `σ_I(A) ≥ m`. -/
theorem lemma3_5_3 {A : Set ExtPlane} (hA : IsQuasidiskExt A) {m : ℝ≥0∞}
    (hm : ∀ z₁ ∈ A, ∀ z₂ ∈ A, z₁ ≠ z₂ → ∃ B : Set ExtPlane, IsQuasidiskExt B ∧ B ⊆ A ∧ z₁ ∈ closure B ∧
      z₂ ∈ closure B ∧ m ≤ innerRadius B) :
    m ≤ innerRadius A := by
  sorry

/-! ## §5.7 General estimates for the inner radius -/

/-- **Unlabelled** (Ch. III §5.7, P1:4692–4697). For all domains `A` conformally equivalent to a disc,
`2 ≤ δ(A) + σ_I(A) ≤ 6`. -/
theorem para3_5_7 {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) :
    2 ≤ discDistance A + innerRadius A ∧ discDistance A + innerRadius A ≤ 6 := by
  sorry

/-- **Theorem 5.3** (Ch. III §5.7, Lehtinen), the bound. For all domains `A` conformally equivalent to a disc,
`σ_I(A) ≤ 2` (5.13). -/
theorem thm3_5_3_a {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) : innerRadius A ≤ 2 := by
  sorry

/-- **Theorem 5.3** (Ch. III §5.7, Lehtinen), the equality case. `σ_I(A) = 2` if and only if `A` is a disc. -/
theorem thm3_5_3_b {A : Set ExtPlane} (hA : IsHypSimplyConnectedExt A) : innerRadius A = 2 ↔ IsDiscExt A := by
  sorry

end Lehto1987
