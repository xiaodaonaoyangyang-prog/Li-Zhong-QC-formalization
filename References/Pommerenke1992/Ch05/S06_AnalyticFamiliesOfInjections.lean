import References.Pommerenke1992.Ch05.S05_QuasiconformalExtension

/-!
# Pommerenke 1992, Ch. 5 §5.6 Analytic Families of Injections

Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §5.6; source `full.md` of
`boundary-behaviour-of-conformal-maps-pommerenke--annas-archive.pdf-6de0179f…`, lines 5190–5379.

* Theorem 5.22 (Mañé–Sad–Sullivan, MaSaSu83) — `thm5_22`
* Schottky's theorem ((5.6.1); named; used in the proof of Theorem 5.22) — `schottky_theorem`
* Corollary 5.23 (Becker's univalence criterion, Bec72) — `cor5_23`
* Corollary 5.24 (Nehari's univalence criterion, AhWe62) — `cor5_24`
* Embedding theorem (Ahlfors–Bers, AhBer60, quoted; (5.6.9) used in the proofs of Theorems 5.25 and 5.26) —
  `embedding_theorem`
* Theorem 5.25 — `thm5_25`
* Definition (analytic functional on `S`, §5.6) — `IsAnalyticFunctional`
* Theorem 5.26 (the Lehto majorant principle, (5.6.10); cited at P2 l. 2687) — `thm5_26`

Not items (DESIGN §3): "`f_λ` is an analytic family of injections" and "the continuity of `f_λ` is a conclusion"
(l. 5204, a remark; not cited); the results of BeRo86, SuThu86 (l. 5206, quoted, "we do not need"); the bounds (5.6.2)
(Hem80, Hem88, "which we will however not need"); (5.6.3), (5.6.5), (5.6.7), (5.6.8) (proof steps); the Möbius
remark after Corollary 5.24 and the univalence criteria for quasidisks (l. 5264, 5286; not cited); the analyticity of
`f_λ^{(k)}(z)` by Vitali's theorem (l. 5318, a remark); the applications (5.6.11)–(5.6.13) (Küh69b, Gru32, Küh71; not
cited).

**Conventions.** As in §5.4, §5.5. A family `f_λ` (`λ ∈ 𝔻`) is a function `f : ℂ → ℂ → ℂ`, `f_λ(z) = f λ z`; the
parameter is named `lam` (`λ` is a Lean keyword). "Analytic in `λ ∈ 𝔻`" is complex differentiability on `𝔻`. The
class `S` is the project's `LiZhongQC.knHyp` (§1.3). The quasiconformal maps of (5.6.9) are those of (5.1.2),
(5.1.3) (`IsKappaQC`, built on `LiZhongQC.IsGenHomeoSolution`); a quasiconformal map of `Ĉ` onto `Ĉ` keeping `∞` fixed
is a quasiconformal map of `ℂ` onto `ℂ` (`IsQCPlane`, resp. `IsKappaQC`).
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace Pommerenke1992

open LiZhongQC (ExtPlane extInf toExt unitDisc IsConformalOnto IsLocUnivMero schwarzian knHyp)

/-- **Theorem 5.22** (§5.6; Mañé–Sad–Sullivan, MaSaSu83). Suppose that (i) `f_λ : 𝔻 → ℂ` is injective for each
`λ ∈ 𝔻`, (ii) `f_λ(z)` is analytic in `λ ∈ 𝔻` for each fixed `z ∈ 𝔻`, (iii) `f₀(z) = z` for `z ∈ 𝔻`. Then each
`f_λ` (`λ ∈ 𝔻`) can be extended to a homeomorphism of `𝔻̄` onto a closed quasidisk in `ℂ`.
Modelling: no continuity or analyticity in `z` is assumed (as in the book); the extension `F` is continuous and
injective on the compact `𝔻̄`, and `F(𝔻̄)` is the closure of a quasidisk. -/
theorem thm5_22 {f : ℂ → ℂ → ℂ} (hinj : ∀ lam ∈ unitDisc, InjOn (f lam) unitDisc)
    (han : ∀ z ∈ unitDisc, DifferentiableOn ℂ (fun lam => f lam z) unitDisc) (hid : ∀ z ∈ unitDisc, f 0 z = z) :
    ∀ lam ∈ unitDisc, ∃ F : ℂ → ℂ, ContinuousOn F (closedBall 0 1) ∧ InjOn F (closedBall 0 1) ∧
      EqOn F (f lam) unitDisc ∧ ∃ G : Set ℂ, IsQuasidisk G ∧ F '' closedBall 0 1 = closure G := by
  sorry

/-- **Schottky's theorem** (§5.6, named; (5.6.1) used in the proof of Theorem 5.22). If `h` is analytic and `≠ 0, 1`
in `𝔻`, then (5.6.1) `|h(λ)| ≤ Φ(|h(0)|, (1 + |λ|)/(1 - |λ|))` for `|λ| < 1`, where `Φ(x, t)` (`0 ≤ x < +∞`) is a
(universal) strictly increasing continuous function with `Φ(0, t) = 0`.
Modelling: `Φ` is continuous on `[0, ∞) × [1, ∞)` (the values `t = (1 + |λ|)/(1 - |λ|) ≥ 1`) and strictly increasing
in `x`. -/
theorem schottky_theorem :
    ∃ Φ : ℝ → ℝ → ℝ, ContinuousOn (Function.uncurry Φ) (Ici 0 ×ˢ Ici 1) ∧
      (∀ t : ℝ, 1 ≤ t → StrictMonoOn (fun x => Φ x t) (Ici 0) ∧ Φ 0 t = 0) ∧
      ∀ h : ℂ → ℂ, DifferentiableOn ℂ h unitDisc → (∀ lam ∈ unitDisc, h lam ≠ 0 ∧ h lam ≠ 1) →
        ∀ lam ∈ unitDisc, ‖h lam‖ ≤ Φ ‖h 0‖ ((1 + ‖lam‖) / (1 - ‖lam‖)) := by
  sorry

/-- **Corollary 5.23** (§5.6; Becker's univalence criterion, Bec72). Let `f` be analytic and locally univalent in
`𝔻`. If (5.6.4) `(1 - |z|²)|z f''(z)/f'(z)| ≤ κ < 1` for `z ∈ 𝔻`, then `f` maps `𝔻` conformally onto a quasidisk. -/
theorem cor5_23 {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f unitDisc) (hloc : ∀ z ∈ unitDisc, deriv f z ≠ 0) {κ : ℝ}
    (hκ : κ < 1) (hB : ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) * ‖z * deriv (deriv f) z / deriv f z‖ ≤ κ) :
    IsConformalOnto f unitDisc (f '' unitDisc) ∧ IsQuasidisk (f '' unitDisc) := by
  sorry

/-- **Corollary 5.24** (§5.6; Nehari's univalence criterion, AhWe62). Let `f` be meromorphic and locally univalent in
`𝔻` and let (5.6.6) `(1 - |z|²)²|S_f(z)| ≤ 2κ < 2` for `z ∈ 𝔻`. If `f(0) ∈ ℂ` and `f''(0) = 0`, then `f` maps `𝔻`
conformally onto a (bounded) quasidisk.
Modelling: meromorphic and locally univalent is `LiZhongQC.IsLocUnivMero`, `S_f` is `LiZhongQC.schwarzian` (§1.2);
`f(0) ∈ ℂ` is analyticity at `0`; a quasidisk is bounded by definition. -/
theorem cor5_24 {f : ℂ → ℂ} (hf : IsLocUnivMero f unitDisc) {κ : ℝ} (hκ : κ < 1)
    (hS : ∀ z ∈ unitDisc, (1 - ‖z‖ ^ 2) ^ 2 * ‖schwarzian f z‖ ≤ 2 * κ) (h0 : AnalyticAt ℂ f 0)
    (h2 : deriv (deriv f) 0 = 0) :
    IsConformalOnto f unitDisc (f '' unitDisc) ∧ IsQuasidisk (f '' unitDisc) := by
  sorry

/-- **Embedding theorem** (§5.6; Ahlfors–Bers, AhBer60; Leh87, p. 70; quoted). Let `h` be a quasiconformal map of `Ĉ`
onto `Ĉ` that keeps `0`, `1` and `∞` fixed. For `λ ∈ 𝔻` let `h_λ` be the quasiconformal map that satisfies (5.6.9)
`∂h_λ/∂z̄ / ∂h_λ/∂z = (λ/κ) μ(z)` for almost all `z ∈ ℂ`, `|μ(z)| ≤ κ < 1` (see (5.1.2), (5.1.3)), and keeps
`0, 1, ∞` fixed. Then `h_κ = h`, and `h_λ(z)` depends analytically on `λ ∈ 𝔻` for each `z ∈ 𝔻`.
Modelling: `h` is `κ`-quasiconformal with the Beltrami coefficient `μ` (`0 < κ`, so that `λ/κ` is defined); the maps
`h_λ` exist, and every choice of them (normalized solutions of (5.6.9)) satisfies the conclusion. The analyticity is
stated "for each `z ∈ 𝔻`" as the (OCR) text reads; this is what Theorems 5.25 and 5.26 use. -/
theorem embedding_theorem {h μ : ℂ → ℂ} {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hμ : LiZhongQC.IsBeltramiCoeff μ univ κ) (hh : LiZhongQC.IsGenHomeoSolution h μ univ 2) (hhu : h '' univ = univ)
    (h0 : h 0 = 0) (h1 : h 1 = 1) :
    (∃ H : ℂ → ℂ → ℂ, ∀ lam ∈ unitDisc, LiZhongQC.IsGenHomeoSolution (H lam) (fun z => lam / κ * μ z) univ 2 ∧
      H lam '' univ = univ ∧ H lam 0 = 0 ∧ H lam 1 = 1) ∧
    ∀ H : ℂ → ℂ → ℂ, (∀ lam ∈ unitDisc, LiZhongQC.IsGenHomeoSolution (H lam) (fun z => lam / κ * μ z) univ 2 ∧
      H lam '' univ = univ ∧ H lam 0 = 0 ∧ H lam 1 = 1) →
      H κ = h ∧ ∀ z ∈ unitDisc, DifferentiableOn ℂ (fun lam => H lam z) unitDisc := by
  sorry

/-- **Theorem 5.25** (§5.6). If `h` is a quasiconformal map of `Ĉ` onto `Ĉ` that keeps `∞` fixed, then `h(𝕋)` is a
quasicircle.
Modelling: a quasiconformal map of `ℂ` onto `ℂ` (`IsQCPlane`, (5.1.2), (5.1.3)). -/
theorem thm5_25 {h : ℂ → ℂ} (hh : IsQCPlane h) : IsQuasicircle (h '' sphere 0 1) := by
  obtain ⟨κ, hκ0, hκ1, hsurj, μ, hμ, hsol⟩ := hh
  -- the analytic definition gives Li Zhong's geometric `K`-quasiconformality (Theorem 10.2)
  have hK : LiZhongQC.IsKQC h univ ((1 + κ) / (1 - κ)) :=
    LiZhongQC.thm10_2_isKQC_of_genHomeoSolution isOpen_univ hκ0 hκ1 hμ hsol
  obtain ⟨M, hM⟩ := LiZhongQC.thm18_1_boundedTurning_of_quasicircle hK.2.1
  refine ⟨M, hM _ ⟨h, hK, hsurj, LiZhongQC.mobiusExt 1 0 0 1, ⟨1, 0, 0, 1, by norm_num, rfl⟩, ?_⟩ ?_⟩
  · -- `h(𝕋)`, read in `ℂ̄`, is the image of `𝕋` under the identity Möbius map
    have hid : ∀ w : ExtPlane, LiZhongQC.mobiusExt 1 0 0 1 w = w := fun w => by
      induction w using OnePoint.rec with
      | infty => exact LiZhongQC.mobiusExt_infty_of_eq rfl
      | coe x =>
        rw [LiZhongQC.mobiusExt_coe (show (0 : ℂ) * x + 1 ≠ 0 by simp)]
        show (((1 * x + 0) / (0 * x + 1) : ℂ) : ExtPlane) = x
        rw [one_mul, add_zero, zero_mul, zero_add, div_one]
    have hmap : OnePoint.map h '' toExt (sphere 0 1) = toExt (h '' sphere 0 1) := by
      show OnePoint.map h '' ((↑) '' sphere (0 : ℂ) 1) = (↑) '' (h '' sphere (0 : ℂ) 1)
      rw [← image_comp, ← image_comp]
      rfl
    rw [hmap]
    exact (Set.image_congr fun w _ => hid w).trans (image_id' _) |>.symm
  · rintro ⟨w, -, hw⟩
    exact OnePoint.coe_ne_infty w hw

/-- **Definition** (§5.6, l. 5318). `Φ : S → ℂ` is an analytic functional: `Φ(f_λ)` is an analytic function whenever
`f_λ ∈ S` depends analytically on `λ`.
Modelling: `λ` ranges over an open set `U ⊆ ℂ`; "depends analytically on `λ`" is analyticity of `λ ↦ f_λ(z)` for
each `z ∈ 𝔻`. -/
def IsAnalyticFunctional (Φ : (ℂ → ℂ) → ℂ) : Prop :=
  ∀ U : Set ℂ, IsOpen U → ∀ F : ℂ → ℂ → ℂ, (∀ lam ∈ U, knHyp (F lam)) →
    (∀ z ∈ unitDisc, DifferentiableOn ℂ (fun lam => F lam z) U) → DifferentiableOn ℂ (fun lam => Φ (F lam)) U

/-- **Theorem 5.26** (§5.6; the Lehto majorant principle; Leh87, p. 77). Let `Φ : S → ℂ` be an analytic functional that
vanishes for the identity and satisfies (5.6.10) `|Φ(f)| ≤ M` for all `f ∈ S`. If `f ∈ S` and if `f` has a
`κ`-quasiconformal extension to `Ĉ` keeping `∞` fixed, then `|Φ(f)| ≤ κ M`.
Modelling: the extension is a `κ`-quasiconformal map of `ℂ` onto `ℂ` (`IsKappaQC`) equal to `f` on `𝔻`. -/
theorem thm5_26 {Φ : (ℂ → ℂ) → ℂ} (hΦ : IsAnalyticFunctional Φ) (hid : Φ (fun z => z) = 0) {M : ℝ}
    (hM : ∀ f : ℂ → ℂ, knHyp f → ‖Φ f‖ ≤ M) {f : ℂ → ℂ} (hf : knHyp f) {κ : ℝ}
    (hext : ∃ h : ℂ → ℂ, IsKappaQC h κ ∧ EqOn h f unitDisc) : ‖Φ f‖ ≤ κ * M := by
  sorry

end Pommerenke1992
