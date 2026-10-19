import References.LehtoVirtanen1973.Ch04.S05_ComplexDilatation

/-!
# Lehto–Virtanen, Chapter V §4: Approximation of a quasiconformal mapping

Source: O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed., Springer 1973, Ch. V §4
(pp. 207–211; `full.md` second part P2:309–438).

Conventions as in §1: quasiconformal mappings of domains of `ℂ̄`, complex dilatation `complexDilatationLV` (IV.5.1),
good approximation `IsGoodApproximation` (IV.5.4: a common bound `K` for the approximating mappings, the limit
quasiconformal, locally uniform spherical convergence and almost everywhere convergence of the complex dilatations).
From §4.2 on the book considers *finite* domains and *finite* mappings: a finite domain `G` is `toExt G` for a domain
`G : Set ℂ` of the finite plane, and a finite mapping of it is `OnePoint.map f` for `f : ℂ → ℂ` (the point `∞` is
fixed and lies outside the domain; every finite mapping of a finite domain has this form there). Its complex
dilatation is then `LiZhongQC.complexDilatation f z`, the quotient `w_{\bar z}/w_z` of the finite function (equal to
`complexDilatationLV (OnePoint.map f) z`, the local representation at a finite point with a finite value being
`ζ ↦ f(z + ζ) - f(z)`). A regular (`K`-)quasiconformal mapping is one of Grötzsch's class (I.3.3).

* Theorem 4.1 (§4.1, cf. Bers) — `thm5_4_1`
* Definition (real-analytic function in a domain of the finite plane, §4.2) — exists: `AnalyticOnNhd` (over the real
  field: a power series in z - z₀ and its conjugate converging absolutely near z₀ is a power series in x - x₀ and
  y - y₀ after a real linear substitution, and conversely)
* Lemma 4.1 (§4.2) — `lemma5_4_1`
* Unlabelled (§4.3, P2:433; announced in the Introduction, P1:5953): every finite `K`-quasiconformal mapping is locally
  the limit of a sequence of regular real-analytic `K`-quasiconformal mappings — `qc_local_limit_regular_realAnalytic`
* Unlabelled (§4.3, P2:435; with the previous item the characterization announced in the Introduction, P1:5953): a
  function which in every domain `D`, `D̄ ⊂ G`, is a locally uniform limit of `K`-quasiconformal mappings is either a
  `K`-quasiconformal mapping of `G` or a constant — `isKQuasiconformal_or_const_of_approx`
* Theorem 4.2 (§4.3) — `thm5_4_2`

Not stated (inventory: omitted): the remark after Theorem 4.1 (P2:325–327: `D = G` is possible for simply connected
`G`, by the Mapping theorem; a caveat for other `G`); the remark that a real-analytic function is of class `C^∞`
(P2:331, Mathlib `AnalyticOnNhd.contDiffOn`); the formulas (4.1)–(4.7) of the proof of Lemma 4.1 (P2:337–421); and the
approximation of `κ` by polynomials in 4.3 (P2:423, by III.5.3; [OCR] `|z| ≤ (K - 1)/(K + 1)` is `|κ(z)|`). The
consequence of Lemma 4.1 used in the examples of §6.2 (P2:781: `w` is conformal at `0` when `κ` is a polynomial with
`κ(0) = 0`) follows at once, the complex dilatation of the regular real-analytic `w` being `P` at every point.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace LehtoVirtanen1973

open LiZhongQC (ExtPlane toExt)
open References (IsDomainExt finitePart)

/-! ## §4.1 Approximation by mappings with prescribed complex dilatation -/

/-- **Theorem 4.1** (Ch. V §4.1, cf. Bers). Let `w : G → G′` be a quasiconformal mapping with complex dilatation `κ`.
Let `κₙ`, `n = 1, 2, …`, be a sequence of measurable functions in `G` with `sup_z |κₙ(z)| ≤ k < 1`, which converges to
`κ` almost everywhere in `G`. Then given a domain `D`, `D̄ ⊂ G`, there exists a sequence `n_ν` of positive integers and
a sequence `w_{n_ν}` of quasiconformal mappings of `D`, `ν = 1, 2, …`, with the following two properties: 1. The
mappings `w_{n_ν}` give a good approximation to `w` in `D`. 2. The complex dilatation of `w_{n_ν}` coincides with
`κ_{n_ν}` almost everywhere in `D`.
Modelling: `G` and `D` are domains of `ℂ̄`, the closure taken in `ℂ̄`; the `κₙ` are given on the finite part of `G`
with the common bound `k` there. The indices `n_ν` form a subsequence (the proof extracts a convergent subsequence):
`StrictMono` makes this explicit (leader decision); `wν ν` is the book's `w_{n_ν}`. -/
theorem thm5_4_1 {w : ExtPlane → ExtPlane} {G : Set ExtPlane} (hw : IsQuasiconformalMap w G) {κn : ℕ → ℂ → ℂ}
    (hκm : ∀ n, AEStronglyMeasurable (κn n) (volume.restrict (finitePart G))) {k : ℝ} (hk : k < 1)
    (hκk : ∀ n, ∀ z ∈ finitePart G, ‖κn n z‖ ≤ k)
    (hκlim : ∀ᵐ z : ℂ ∂(volume.restrict (finitePart G)),
      Tendsto (fun n => κn n z) atTop (𝓝 (complexDilatationLV w z)))
    {D : Set ExtPlane} (hD : IsDomainExt D) (hDG : closure D ⊆ G) :
    ∃ nν : ℕ → ℕ, StrictMono nν ∧ ∃ wν : ℕ → ExtPlane → ExtPlane, (∀ ν, IsQuasiconformalMap (wν ν) D) ∧
      IsGoodApproximation wν w D ∧
      ∀ ν, ∀ᵐ z : ℂ ∂(volume.restrict (finitePart D)), complexDilatationLV (wν ν) z = κn (nν ν) z := by
  sorry

/-! ## §4.2 Mappings whose complex dilatation is a polynomial -/

/-- **Lemma 4.1** (Ch. V §4.2). Let `G` and `G′` be finite domains and `w : G → G′` a quasiconformal mapping whose
complex dilatation coincides almost everywhere in `G` with a polynomial `P` in `z` and `z̄`. Then `w` is regular and
real-analytic.
Modelling: finite regime (module docstring): `w = OnePoint.map f` on `toExt G`, so that `G′ = w(G)` is finite; the
polynomial is `P(z) = Σ_{m, n ≤ N} a_{mn} z^m z̄^n`. "Regular" is regular quasiconformal (I.3.3; so the book uses
the lemma in 4.3), and "real-analytic" is analyticity of `f` over `ℝ` at every point of `G`. -/
theorem lemma5_4_1 {f : ℂ → ℂ} {G : Set ℂ} (hf : IsQuasiconformalMap (OnePoint.map f) (toExt G)) {N : ℕ}
    {a : ℕ → ℕ → ℂ}
    (hP : ∀ᵐ z ∂(volume.restrict G), LiZhongQC.complexDilatation f z =
      ∑ m ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (N + 1), a m n * z ^ m * conj z ^ n) :
    IsRegularQuasiconformal (OnePoint.map f) (toExt G) ∧ AnalyticOnNhd ℝ f G := by
  sorry

/-! ## §4.3 Quasiconformal mappings as limits of regular mappings -/

/-- **Unlabelled** (Ch. V §4.3, P2:423–433). Every finite `K`-quasiconformal mapping is locally the limit of a
sequence of regular real-analytic `K`-quasiconformal mappings: if `w : G → G′` (`G`, `G′` finite domains) is
`K`-quasiconformal, then in every domain `D`, `D̄ ⊂ G`, there is a good approximation of `w` by regular real-analytic
`K`-quasiconformal mappings of `D` (whose complex dilatations are polynomials in `z` and `z̄`).
Modelling: finite regime (module docstring); the approximating mappings are finite, as real-analyticity requires
(for a locally uniform approximation of the finite `w` on `D̄` this holds for all large indices); the polynomial form
of their complex dilatations is a detail of the proof and is not asserted. -/
theorem qc_local_limit_regular_realAnalytic {f : ℂ → ℂ} {G : Set ℂ} {K : ℝ}
    (hf : IsKQuasiconformal (OnePoint.map f) (toExt G) K) {D : Set ℂ} (hD : IsDomainExt (toExt D))
    (hDG : closure (toExt D) ⊆ toExt G) :
    ∃ fn : ℕ → ℂ → ℂ, (∀ n, IsRegularKQuasiconformal (OnePoint.map (fn n)) (toExt D) K ∧
        AnalyticOnNhd ℝ (fn n) D) ∧
      IsGoodApproximation (fun n => OnePoint.map (fn n)) (OnePoint.map f) (toExt D) := by
  sorry

/-- **Unlabelled** (Ch. V §4.3, P2:435). Conversely, it follows from Theorem II.5.3 that a function defined in `G`
which can be uniformly approximated by a sequence of `K`-quasiconformal mappings in every domain `D`, `D̄ ⊂ G`, is
either a `K`-quasiconformal mapping of `G` or a constant.
Modelling: `G = toExt G₀` is the finite domain of 4.3 (module docstring); the function `w` is arbitrary (only its
values in `G` matter, and it need not be finite); the approximating mappings are `K`-quasiconformal mappings of `D`,
unrestricted as in Theorem 4.2. "Uniformly approximated in `D`" is taken as uniform convergence on the compact subsets
of `D` in the spherical metric (`TendstoUniformlyOnCompactsSph`), the convergence of a good approximation (IV.5.4).
Over all `D`, `D̄ ⊂ G`, this is equivalent to uniform convergence in `D`: the closure of such a `D` lies in a larger
such domain `D′`, and the mappings for `D′`, restricted to `D`, converge uniformly on the compact set `D̄`. The constant
may be `∞`. With `qc_local_limit_regular_realAnalytic` this gives the characterization of quasiconformal mappings as
non-constant limits of regular ones announced in the Introduction (P1:5953), and it is the "if" half of Theorem 4.2
with only the convergence of the approximation used. -/
theorem isKQuasiconformal_or_const_of_approx {G : Set ℂ} (hG : IsDomainExt (toExt G)) {K : ℝ}
    {w : ExtPlane → ExtPlane}
    (happrox : ∀ D : Set ExtPlane, IsDomainExt D → closure D ⊆ toExt G →
      ∃ wn : ℕ → ExtPlane → ExtPlane, (∀ n, IsKQuasiconformal (wn n) D K) ∧ TendstoUniformlyOnCompactsSph wn w D) :
    IsKQuasiconformal w (toExt G) K ∨ ∃ c : ExtPlane, ∀ z ∈ toExt G, w z = c := by
  sorry

/-- **Theorem 4.2** (Ch. V §4.3). A non-constant finite function `w` in a finite domain `G` is a `K`-quasiconformal
mapping of `G` if and only if in every domain `D`, `D̄ ⊂ G`, there exists a good approximation of `w` by regular
`K`-quasiconformal mappings.
Modelling: finite regime (module docstring): `w = OnePoint.map f`, non-constant on `G`. The domains `D` and the
approximating regular mappings are unrestricted (domains and mappings of `ℂ̄`, as in the book). The book's good
approximation presupposes that the approximated mapping is quasiconformal (IV.5.4, `IsGoodApproximation`); the
equivalence is stated literally (leader decision), so the right side also asserts that `w` is quasiconformal in
every such `D` and nothing is read from the complex dilatation of a mapping which is not quasiconformal. The "if"
direction needs only the locally uniform convergence (P2:435, `isKQuasiconformal_or_const_of_approx`). -/
theorem thm5_4_2 {f : ℂ → ℂ} {G : Set ℂ} {K : ℝ} (hG : IsDomainExt (toExt G))
    (hnc : ∃ a ∈ G, ∃ b ∈ G, f a ≠ f b) :
    IsKQuasiconformal (OnePoint.map f) (toExt G) K ↔
      ∀ D : Set ExtPlane, IsDomainExt D → closure D ⊆ toExt G →
        ∃ wn : ℕ → ExtPlane → ExtPlane, (∀ n, IsRegularKQuasiconformal (wn n) D K) ∧
          IsGoodApproximation wn (OnePoint.map f) D := by
  sorry

end LehtoVirtanen1973
