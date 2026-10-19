import References.Lehto1987.Ch05.S03_TeichmullerSpaceAndLiftedMappings

/-!
# Lehto, Chapter V §4: Teichmüller space and Schwarzian derivatives

Source: O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109, Springer 1987, Ch. V §4 (`full.md`
P2:120–495).

Conventions (see §3, and III §4). The half-planes are mirrored (decision B0.2):
- the Schwarzians `s_μ = S_{f_μ|H}` live in `𝕃` (`LiZhongQC.bersFunction`, `LiZhongQC.bersMapGamma`);
- `Q(G)` is `LiZhongQC.automorphicQD Γ ∩ LiZhongQC.bersSpaceL`, the `Γ`-automorphic holomorphic functions of finite
  norm on `𝕃`; `G` acts on `𝕃` by the same formula, so its Dirichlet regions there are the mirror images of those in
  `ℍ`;
- `U(G)` is `LiZhongQC.schwarzianUnivalentSet ∩ LiZhongQC.automorphicQD Γ` (the book's own remark `U(G) = U(1) ∩ Q(G)`);
- `T(G)` is `LiZhongQC.bersImage Γ`, and `T(1)` is the range of `LiZhongQC.bersMapU`.

The norm is Lehto's `‖φ‖ = sup 4y²|φ|`, i.e. `Gehring1978.hypNorm` on `𝕃`. `β` is `betaDist` of III.2.2 and
`β_S` the project's `LiZhongQC.teichDeltaGamma`. Elements of `Q` are compared through their restrictions to `𝕃`.

* Formula (4.1) (§4.1) — `para5_4_1`
* Unlabelled (§4.1, P2:127–132): for `f` conformal in `H`, `S_f` is a quadratic differential for `G` if and only if
  each `f ∘ g ∘ f⁻¹` is Möbius in `f(H)` — `para5_4_1`
* Lemma 4.1 (§4.1) — `lemma5_4_1`
* Definition (the space `Q(G)`, §4.2) — exists: `LiZhongQC.automorphicQD`, `LiZhongQC.bersSpaceL` (jointly: their
  intersection)
* Formula (4.2) (§4.2) — `eq5_4_2`
* Unlabelled (§4.2, P2:166): for compact `S`, all holomorphic quadratic differentials for `G` have finite norm —
  `para5_4_2_a`
* Unlabelled (§4.2, P2:170): `Q(G)` is a closed subspace of `Q(1)` — `para5_4_2_b`
* Definition (the set `U(G)`, §4.3) — exists: `LiZhongQC.schwarzianUnivalentSet`, `LiZhongQC.automorphicQD` (jointly:
  U(G) = U(1) ∩ Q(G))
* Unlabelled (§4.3, P2:182–186): `U(G)` is closed in `Q(1)` — `para5_4_3`
* Unlabelled (§4.3, P2:190): the second characterization of `U(G)` — omitted: a restatement of `para5_4_1`
* Definition (the image `T(G)` of `T_S`, (4.3), §4.3) — exists: `LiZhongQC.bersImage`
* Formula (4.3) (§4.3) — exists: `LiZhongQC.bersMapGamma`
* Unlabelled (§4.3, P2:198–200): groups `G_f` for `S_f ∈ ∂T(G)`; open questions — omitted: remarks
* Theorem 4.1 (§4.4) — `thm5_4_1`
* Formula (4.4) (§4.4) — `thm5_4_1` (the statement of Theorem 4.1, reconstructed: root Corrections, OCR gap)
* Formula (4.5) (§4.4) — omitted: a step of the proof of Theorem 4.1
* Theorem 4.2 (§4.4) — `thm5_4_2`
* Theorem 4.3 (§4.4) — exists: `LiZhongQC.thm33_1_bers` (its second conjunct)
* Remark (§4.4, P2:244): `Q(G) = 0` for the sphere minus three points — omitted: not cited
* Theorem 4.4 (§4.5) — exists: `LiZhongQC.lemma33_3` (with the project's norm, a quarter of Lehto's: 1/2 there is 2)
* Formula (4.6) (§4.5) — exists: `LiZhongQC.lemma33_3` (the explicit inverse z ↦ −2y²φ(z̄))
* Formula (4.7) (§4.5) — `eq5_4_7`
* Unlabelled (§4.5, P2:276): `B(0, 2)` is the largest ball for subgroups of `{az, −a/z}` — omitted: not cited
* Theorem 4.5 (§4.5) — `thm5_4_5`
* Theorem 4.6 (§4.5) — `thm5_4_6`
* Theorem 4.7 (§4.6) — `thm5_4_7_a`, `thm5_4_7_b`, `thm5_4_7_c`
* Formula (4.8) (§4.6) — `thm5_4_7_b`
* Formula (4.9) (§4.6) — `thm5_4_7_c`
* Formula (4.10) (§4.6) — omitted: the case `q = 0` of (4.12)
* Definition (the maps `α̃_μ`, `α_μ`, (4.11), §4.6) — `alphaTilde`
* Formula (4.11) (§4.6) — `para5_4_6`
* Unlabelled (§4.6, P2:346–348): `α_μ` is an isometric bijection of `T` and of `T_S` onto `T_{S^μ}` — `para5_4_6`
* Formula (4.12) (§4.6) — `eq5_4_12`
* Formula (4.13) (§4.6) — `eq5_4_13`
* Formula (4.14) (§4.6) — omitted: a step of the proof of Theorem 4.7
* Theorem 4.8 (§4.7, Bers imbedding) — `thm5_4_8`
* Unlabelled (§4.7, P2:412–428): direct proofs of openness and closedness; `T(G)` the component of `Q(G) ∩ T(1)` —
  omitted: reproofs
* Formula (4.15) (§4.7) — `thm5_4_8` (the Bers imbedding)
* Formula (4.16) (§4.7) — omitted: quoted (Bers, Abikoff)
* Formula (4.17) (§4.8) — omitted: a relation of §3.5 (`para5_3_5`), restated
* Formula (4.18) (§4.8) — omitted: a step of the proof of the supplement
* Unlabelled (§4.8, P2:442–456): the Ahlfors extension is compatible with `G_μ` — `para5_4_8`
-/

open Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff Manifold MatrixGroups UpperHalfPlane

noncomputable section

namespace Lehto1987

universe u

open LiZhongQC (ExtPlane toExt upperHalf lowerHalf IsUniformization IsFuchsian ActsFreely BeltramiH BeltramiGamma
  TeichGamma teichSetoidGamma teichDistanceGamma teichDeltaGamma fMuSym normalizedSolution UniversalTeichmuller
  teichSetoid automorphicQD bersSpaceL bersFunction bersMapGamma bersImage bersMapU schwarzianUnivalentSet schwarzian
  IsUnivMero IsMobius meroToExt mobiusFn mobiusSL slRealToComplex dz)
open Gehring1978 (hypNorm hypDensity)

/-! ## §4.1 Schwarzian derivatives and quadratic differentials -/

/-- **Formula (4.1)** (Ch. V §4.1) and the remark following it. Let `f` be a conformal mapping of the half-plane.
Then `S_f` is a quadratic differential for `G` if and only if `f ∘ g ∘ f⁻¹` agrees with a Möbius transformation in
`f(H)` for every `g ∈ G`.
Modelling: mirrored: `f` univalent meromorphic in `𝕃`; `S_f|𝕃` in `LiZhongQC.automorphicQD Γ`; the agreement read in
`ℂ̄` (`LiZhongQC.meroToExt`). -/
theorem para5_4_1 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) {f : ℂ → ℂ} (hf : IsUnivMero f lowerHalf) :
    lowerHalf.indicator (schwarzian f) ∈ automorphicQD Γ ↔
      ∀ γ ∈ Γ, ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∀ z ∈ lowerHalf,
        meroToExt f (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) = M (meroToExt f z) := by
  sorry

/-- **Lemma 4.1** (Ch. V §4.1). For `[μ] ∈ T` the following are equivalent:
1° `S_{f_μ|H}` is a quadratic differential for `G`;
2° `f_μ ∘ g ∘ f_μ⁻¹` agrees with a Möbius transformation in `f_μ(H)` for `g ∈ G`;
3° `f^μ ∘ g ∘ (f^μ)⁻¹` agrees with a Möbius transformation on `ℝ` for `g ∈ G`.
Modelling: mirrored (`𝕃`, decision B0.2); 3° as `f^μ ∘ g = M ∘ f^μ` on `ℝ` off the pole of `g`, `M` real (near miss:
`LiZhongQC.lemma33_4_earle`, 1° ⇔ 3°). -/
theorem lemma5_4_1 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (μ : BeltramiH) :
    (bersFunction μ.1 ∈ automorphicQD Γ ↔
      ∀ γ ∈ Γ, ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∀ z ∈ lowerHalf,
        ((normalizedSolution μ.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) : ℂ) : ExtPlane) =
          M (normalizedSolution μ.1 z)) ∧
    ((∀ γ ∈ Γ, ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∀ z ∈ lowerHalf,
        ((normalizedSolution μ.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) : ℂ) : ExtPlane) =
          M (normalizedSolution μ.1 z)) ↔
      ∀ γ ∈ Γ, ∃ a b c d : ℝ, a * d - b * c ≠ 0 ∧ ∀ x : ℝ, γ 1 0 * x + γ 1 1 ≠ 0 →
        c * (fMuSym μ.1 x).re + d ≠ 0 →
        fMuSym μ.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) x) = mobiusFn a b c d (fMuSym μ.1 x)) := by
  sorry

/-! ## §4.2 Spaces of quadratic differentials -/

/-- **Formula (4.2)** (Ch. V §4.2). For `φ ∈ Q(G)`, the norm can be computed over a Dirichlet region `N` of `G`:
`‖φ‖ = sup_{z ∈ N} 4y²|φ(z)|`.
Modelling: mirrored: `N` is the mirror image in `𝕃` of the Dirichlet region `GardinerLakic2000.dirichletDomain Γ z₀`
of `ℍ`. -/
theorem eq5_4_2 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (z₀ : ℍ) {φ : ℂ → ℂ}
    (hφ : φ ∈ automorphicQD Γ) :
    hypNorm φ (toExt lowerHalf) = ⨆ z ∈ conj '' GardinerLakic2000.dirichletDomain Γ z₀,
      ENNReal.ofReal (‖φ z‖ / hypDensity (toExt lowerHalf) z ^ 2) := by
  sorry

/-- **Unlabelled** (Ch. V §4.2, P2:166). If `S` is compact, all holomorphic quadratic differentials for `G` have finite
norm. -/
theorem para5_4_2_a {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] [CompactSpace S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ)
    (hfree : ActsFreely Γ) (hp : IsUniformization Γ p) {φ : ℂ → ℂ} (hφ : φ ∈ automorphicQD Γ) :
    hypNorm φ (toExt lowerHalf) < ⊤ := by
  sorry

/-- **Unlabelled** (Ch. V §4.2, P2:170). `Q(G)` is a closed subspace of `Q(1)`, hence a Banach space. -/
theorem para5_4_2_b {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) {φn : ℕ → ℂ → ℂ} {φ : ℂ → ℂ}
    (hφn : ∀ n, φn n ∈ automorphicQD Γ ∧ φn n ∈ bersSpaceL) (hφ : φ ∈ bersSpaceL)
    (hlim : Tendsto (fun n => hypNorm (φn n - φ) (toExt lowerHalf)) atTop (𝓝 0)) :
    lowerHalf.indicator φ ∈ automorphicQD Γ := by
  sorry

/-! ## §4.3 Schwarzian derivatives of univalent functions -/

/-- **Unlabelled** (Ch. V §4.3, P2:182–186). `U(G) = U(1) ∩ Q(G)` is a closed subset of `Q(1)`. -/
theorem para5_4_3 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) {φn : ℕ → ℂ → ℂ} {φ : ℂ → ℂ}
    (hφn : ∀ n, φn n ∈ schwarzianUnivalentSet ∧ φn n ∈ automorphicQD Γ) (hφ : φ ∈ bersSpaceL)
    (hlim : Tendsto (fun n => hypNorm (φn n - φ) (toExt lowerHalf)) atTop (𝓝 0)) :
    lowerHalf.indicator φ ∈ schwarzianUnivalentSet ∧ lowerHalf.indicator φ ∈ automorphicQD Γ := by
  sorry

/-! ## §4.4 Connection between Teichmüller spaces and the universal space -/

/-- **Theorem 4.1** (Ch. V §4.4) and (4.4). `T(G) = Q(G) ∩ T(1)`.
[OCR gap, root Corrections] The statement is lost in the text layer; it is reconstructed from its proof (P2:212) and
its uses (P2:230–236). -/
theorem thm5_4_1 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) :
    bersImage Γ = (automorphicQD Γ : Set (ℂ → ℂ)) ∩ range bersMapU := by
  sorry

/-- **Theorem 4.2** (Ch. V §4.4). The set `T(G)` is closed in `T(1)`. -/
theorem thm5_4_2 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {φn : ℕ → ℂ → ℂ} {φ : ℂ → ℂ}
    (hφn : ∀ n, φn n ∈ bersImage Γ) (hφ : φ ∈ range bersMapU)
    (hlim : Tendsto (fun n => hypNorm (φn n - φ) (toExt lowerHalf)) atTop (𝓝 0)) : φ ∈ bersImage Γ := by
  sorry

/-! ## §4.5 Distance to the boundary -/

/-- **Formula (4.7)** (Ch. V §4.5). Since `‖s_μ‖ ≤ 6 β([μ], 0)`, the set `{[μ] ∈ T_S | β([μ], 0) < 1/3}` is contained
in the preimage of `B(0, 2)`. -/
theorem eq5_4_7 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (μ : BeltramiGamma Γ)
    (hβ : betaDist (Quotient.mk teichSetoid μ.1) UniversalTeichmuller.origin < 1 / 3) :
    hypNorm (bersFunction μ.1.1) (toExt lowerHalf) < 2 := by
  sorry

/-- **Theorem 4.5** (Ch. V §4.5). Every point of the Teichmüller space `T_S` can be represented by a real analytic
Beltrami differential and by a real analytic quasiconformal mapping.
Modelling: one representative `μ` with `μ` and `f^μ` real analytic in `ℍ` (as `thm3_1_1`). -/
theorem thm5_4_5 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (p : TeichGamma Γ) :
    ∃ μ : BeltramiGamma Γ, Quotient.mk (teichSetoidGamma Γ) μ = p ∧ AnalyticOnNhd ℝ μ.1.1 upperHalf ∧
      AnalyticOnNhd ℝ (fMuSym μ.1.1) upperHalf := by
  sorry

/-- **Theorem 4.6** (Ch. V §4.5). For every `s_μ ∈ T(G)`, the ball `B(s_μ, σ_I(A_μ)) = {φ ∈ Q(G) | q(s_μ, φ) <
σ_I(A_μ)}` is contained in `T(G)`, where `A_μ = f_μ(H)` and `σ_I` is the inner radius of univalence (III.5.1).
Modelling: mirrored: `A_μ = f_μ(𝕃)`. -/
theorem thm5_4_6 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (μ : BeltramiGamma Γ)
    {φ : ℂ → ℂ} (hφ : φ ∈ automorphicQD Γ)
    (hd : hypNorm (φ - bersFunction μ.1.1) (toExt lowerHalf) <
      innerRadius (toExt (normalizedSolution μ.1.1 '' lowerHalf))) :
    φ ∈ bersImage Γ := by
  sorry

/-! ## §4.6 Equivalence of metrics -/

/-- **Theorem 4.7** (Ch. V §4.6), uniform equivalence. The metric `τ_S` of `T_S` is uniformly equivalent to the metric
`τ|T_S` induced by the universal Teichmüller space.
Modelling: one direction is (3.1) (`eq5_3_1`); the other in `ε–δ` form on representatives. -/
theorem thm5_4_7_a {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) :
    ∀ ε > 0, ∃ δ > 0, ∀ μ ν : BeltramiGamma Γ,
      teichDist (Quotient.mk teichSetoid μ.1) (Quotient.mk teichSetoid ν.1) < δ →
      teichDistanceGamma (Quotient.mk (teichSetoidGamma Γ) μ) (Quotient.mk (teichSetoidGamma Γ) ν) < ε := by
  sorry

/-- **Theorem 4.7** (Ch. V §4.6), (4.8). For every `p ∈ T_S`, `limsup_{q → p} τ_S(p, q)/τ(p, q) ≤ 3`.
Modelling: for every `ε > 0`, `τ_S ≤ (3 + ε) τ` near `p` (on representatives). -/
theorem thm5_4_7_b {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (μ : BeltramiGamma Γ) :
    ∀ ε > 0, ∃ δ > 0, ∀ ν : BeltramiGamma Γ,
      teichDist (Quotient.mk teichSetoid μ.1) (Quotient.mk teichSetoid ν.1) < δ →
      teichDistanceGamma (Quotient.mk (teichSetoidGamma Γ) μ) (Quotient.mk (teichSetoidGamma Γ) ν) ≤
        (3 + ε) * teichDist (Quotient.mk teichSetoid μ.1) (Quotient.mk teichSetoid ν.1) := by
  sorry

/-- **Theorem 4.7** (Ch. V §4.6), (4.9). On every bounded set `A ⊂ T_S`, `τ_S(p, q) ≤ 3(1 + dia A) τ(p, q)`, where
`dia A` is the `τ_S`-diameter of `A`.
Modelling: for any bound `D` of the `τ_S`-distances in `A` (the statement for `D = dia A` is the sharpest). -/
theorem thm5_4_7_c {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) {A : Set (TeichGamma Γ)}
    {D : ℝ} (hD : ∀ p ∈ A, ∀ q ∈ A, teichDistanceGamma p q ≤ D) {μ ν : BeltramiGamma Γ}
    (hμ : Quotient.mk (teichSetoidGamma Γ) μ ∈ A) (hν : Quotient.mk (teichSetoidGamma Γ) ν ∈ A) :
    teichDistanceGamma (Quotient.mk (teichSetoidGamma Γ) μ) (Quotient.mk (teichSetoidGamma Γ) ν) ≤
      3 * (1 + D) * teichDist (Quotient.mk teichSetoid μ.1) (Quotient.mk teichSetoid ν.1) := by
  sorry

/-- **Definition** (the map `α̃_μ`, Ch. V §4.6, (5.3) of §5.4): `f^{α̃_μ(ν)} = f^ν ∘ (f^μ)⁻¹`, explicitly
`α̃_μ(ν) = ((ν − μ)/(1 − μ̄ν) · (∂f^μ/|∂f^μ|)²) ∘ (f^μ)⁻¹`.
Modelling: on `ℍ` with `f^μ = LiZhongQC.fMuSym μ` (decision B0.2), `0` off `ℍ`. -/
def alphaTilde (μ ν : ℂ → ℂ) : ℂ → ℂ :=
  upperHalf.indicator fun w =>
    (ν (Function.invFun (fMuSym μ) w) - μ (Function.invFun (fMuSym μ) w)) /
        (1 - conj (μ (Function.invFun (fMuSym μ) w)) * ν (Function.invFun (fMuSym μ) w)) *
      (dz (fMuSym μ) (Function.invFun (fMuSym μ) w) / (‖dz (fMuSym μ) (Function.invFun (fMuSym μ) w)‖ : ℂ)) ^ 2

/-- **Unlabelled** (Ch. V §4.6, P2:346–348) and (4.11). The map `α_μ([ν]) = [α̃_μ(ν)]` is an isometric bijection of
the universal Teichmüller space onto itself mapping `[μ]` to the origin; it maps `T_S` onto `T_{S^μ}`, `S^μ = H′/G^μ`,
isometrically for `τ_S` and `τ_{S^μ}`.
Modelling: `α_μ` given by its values on the coefficients `ν′` a.e. equal to `α̃_μ(ν)`; `G^μ` is any group with
`f^μ ∘ g = g′ ∘ f^μ` relating its elements to those of `G` (as in `LiZhongQC.exists_deformation_group`). -/
theorem para5_4_6 {Γ Γμ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (μ : BeltramiGamma Γ)
    (hΓμ : (∀ γ ∈ Γ, ∃ γ' ∈ Γμ, ∀ z ∈ upperHalf,
        fMuSym μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
          mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ.1.1 z)) ∧
      ∀ γ' ∈ Γμ, ∃ γ ∈ Γ, ∀ z ∈ upperHalf,
        fMuSym μ.1.1 (mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) =
          mobiusFn (γ' 0 0) (γ' 0 1) (γ' 1 0) (γ' 1 1) (fMuSym μ.1.1 z)) :
    (∃ α : UniversalTeichmuller → UniversalTeichmuller, Function.Bijective α ∧
      (∀ p q, teichDist (α p) (α q) = teichDist p q) ∧
      α (Quotient.mk teichSetoid μ.1) = UniversalTeichmuller.origin ∧
      ∀ ν ν' : BeltramiH, (∀ᵐ z : ℂ, ν'.1 z = alphaTilde μ.1.1 ν.1 z) →
        α (Quotient.mk teichSetoid ν) = Quotient.mk teichSetoid ν') ∧
    ∃ α : TeichGamma Γ → TeichGamma Γμ, Function.Bijective α ∧
      (∀ p q, teichDistanceGamma (α p) (α q) = teichDistanceGamma p q) ∧
      ∀ (ν : BeltramiGamma Γ) (ν' : BeltramiGamma Γμ), (∀ᵐ z : ℂ, ν'.1.1 z = alphaTilde μ.1.1 ν.1.1 z) →
        α (Quotient.mk (teichSetoidGamma Γ) ν) = Quotient.mk (teichSetoidGamma Γμ) ν' := by
  sorry

/-- **Formula (4.12)** (Ch. V §4.6). `β(p, q) ≤ β_S(p, q) ≤ 3 β(p, q)` for all `p, q ∈ T_S`. -/
theorem eq5_4_12 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (μ ν : BeltramiGamma Γ) :
    betaDist (Quotient.mk teichSetoid μ.1) (Quotient.mk teichSetoid ν.1) ≤
        teichDeltaGamma (Quotient.mk (teichSetoidGamma Γ) μ) (Quotient.mk (teichSetoidGamma Γ) ν) ∧
      teichDeltaGamma (Quotient.mk (teichSetoidGamma Γ) μ) (Quotient.mk (teichSetoidGamma Γ) ν) ≤
        3 * betaDist (Quotient.mk teichSetoid μ.1) (Quotient.mk teichSetoid ν.1) := by
  sorry

/-- **Formula (4.13)** (Ch. V §4.6). `β_S = tanh τ_S`.
Modelling: the project's `τ_S` is defined from `β_S` (`LiZhongQC.teichDistanceGamma`), so the content is the bridge
to the Teichmüller distance (2.1) of the surface model: for lifts `μ′`, `ν′` of `μ`, `ν`,
`β_S([μ′], [ν′]) = tanh τ_S([μ], [ν])`. -/
theorem eq5_4_13 {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [ChartedSpace ℂ S]
    [IsManifold 𝓘(ℂ) ω S] {Γ : Subgroup SL(2, ℝ)} {p : ℍ → S} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ)
    (hp : IsUniformization Γ p) {μ ν : GardinerLakic2000.beltramiBall S} {μ' ν' : BeltramiGamma Γ}
    (hμ' : ∀ᵐ z ∂(volume.restrict upperHalf), μ'.1.1 z = GardinerLakic2000.liftBeltrami p μ.1 z)
    (hν' : ∀ᵐ z ∂(volume.restrict upperHalf), ν'.1.1 z = GardinerLakic2000.liftBeltrami p ν.1 z) :
    teichDeltaGamma (Quotient.mk (teichSetoidGamma Γ) μ') (Quotient.mk (teichSetoidGamma Γ) ν') =
      Real.tanh (GardinerLakic2000.teichDist p (Quot.mk (GardinerLakic2000.teichRel p) μ)
        (Quot.mk (GardinerLakic2000.teichRel p) ν)) := by
  sorry

/-! ## §4.7 Bers imbedding -/

/-- **Theorem 4.8** (Ch. V §4.7, Bers). The mapping `[μ] ↦ S_{f_μ|H}` (4.15) is a homeomorphism of `(T_S, τ_S)` onto
`(T(G), q)`.
Modelling: `LiZhongQC.bersMapGamma` (mirrored, `𝕃`) is injective, and it and its inverse are continuous for `τ_S` and
Lehto's norm (`ε–δ`) (near miss: `LiZhongQC.lemma33_2`, one direction). -/
theorem thm5_4_8 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) :
    Function.Injective (bersMapGamma Γ) ∧
      (∀ p, ∀ ε > 0, ∃ δ > 0, ∀ q, teichDistanceGamma p q < δ →
        hypNorm (bersMapGamma Γ p - bersMapGamma Γ q) (toExt lowerHalf) < ENNReal.ofReal ε) ∧
      ∀ p, ∀ ε > 0, ∃ δ > 0, ∀ q, hypNorm (bersMapGamma Γ p - bersMapGamma Γ q) (toExt lowerHalf) < ENNReal.ofReal δ →
        teichDistanceGamma p q < ε := by
  sorry

/-! ## §4.8 Quasiconformal extensions compatible with a group -/

/-- **Unlabelled** (Ch. V §4.8, P2:442–456). For every point `S_{f_μ}` of `T(G)` there is an `ε > 0` such that every
function `f` univalent in `A_μ` and compatible with `G_μ` (its Schwarzian a quadratic differential for `G_μ`) with
`‖S_f‖ < ε` has a quasiconformal extension `F` to the plane compatible with `G_μ`: `F ∘ g_μ ∘ F⁻¹` is a Möbius
transformation for every `g_μ ∈ G_μ`.
Modelling: mirrored (`A_μ = f_μ(𝕃)`), `G_μ` as in `thm5_3_3`; compatibility of `f`: `f ∘ g_μ = M ∘ f` on `A_μ` with
`M` Möbius; the norm is `Gehring1978.hypNorm` of `A_μ`. -/
theorem para5_4_8 {Γ : Subgroup SL(2, ℝ)} (hΓ : IsFuchsian Γ) (hfree : ActsFreely Γ) (μ : BeltramiGamma Γ)
    {Gμ : Subgroup SL(2, ℂ)}
    (hG : ∀ g : SL(2, ℂ), g ∈ Gμ ↔ ∃ γ ∈ Γ, ∀ z : ExtPlane,
      OnePoint.map (normalizedSolution μ.1.1) (mobiusSL (slRealToComplex γ) z) =
        mobiusSL g (OnePoint.map (normalizedSolution μ.1.1) z)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ f : ℂ → ℂ, IsUnivMero f (normalizedSolution μ.1.1 '' lowerHalf) →
      (∀ g ∈ Gμ, ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∀ z ∈ normalizedSolution μ.1.1 '' lowerHalf,
        meroToExt f (mobiusFn (g 0 0) (g 0 1) (g 1 0) (g 1 1) z) = M (meroToExt f z)) →
      hypNorm (schwarzian f) (toExt (normalizedSolution μ.1.1 '' lowerHalf)) < ENNReal.ofReal ε →
      ∃ F : ExtPlane → ExtPlane, IsQCExtensionOf F f (toExt (normalizedSolution μ.1.1 '' lowerHalf)) ∧
        ∀ g ∈ Gμ, ∃ M : ExtPlane → ExtPlane, IsMobius M ∧ ∀ z : ExtPlane, F (mobiusSL g z) = M (F z) := by
  sorry

end Lehto1987
