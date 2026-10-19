import References.Hubbard2006.Ch01.S01_TwoStatements
import References.Hubbard2006.Ch01.S02_SubharmonicHarmonic
import References.Hubbard2006.Ch01.S03_Rado
import References.Hubbard2006.Ch01.S04_Exhaustion
import References.Hubbard2006.Ch01.S05_GreenFunctions
import References.Hubbard2006.Ch01.S06_SimplyConnectedPieces
import References.Hubbard2006.Ch01.S08_FirstClassification
import References.Hubbard2006.Ch02.S01_PlaneHyperbolicGeometry
import References.Hubbard2006.Ch02.S02_CurvatureOfConformalMetrics
import References.Hubbard2006.Ch02.S04_HyperboloidModel
import References.Hubbard2006.Ch03.S01_FuchsianGroups
import References.Hubbard2006.Ch03.S02_ClassificationOfAnnuli
import References.Hubbard2006.Ch03.S03_HyperbolicMetric
import References.Hubbard2006.Ch03.S04_LimitSets
import References.Hubbard2006.Ch03.S05_Trousers
import References.Hubbard2006.Ch03.S06_TrouserDecomposition
import References.Hubbard2006.Ch03.S07_IdealBoundaries
import References.Hubbard2006.Ch03.S08_CollaringTheorem
import References.Hubbard2006.Ch03.S09_FundamentalDomains
import References.Hubbard2006.Ch04.S02_SobolevSpaces
import References.Hubbard2006.Ch04.S03_GroetzschTheorem
import References.Hubbard2006.Ch04.S04_NormalFamilies
import References.Hubbard2006.Ch04.S05_GeometricCharacterizations
import References.Hubbard2006.Ch04.S06_MappingTheorem
import References.Hubbard2006.Ch04.S07_DependenceOnParameters
import References.Hubbard2006.Ch04.S08_BeltramiForms
import References.Hubbard2006.Ch04.S09_BoundaryValues
import References.Hubbard2006.Ch05.S01_DouadyEarleExtension
import References.Hubbard2006.Ch05.S02_HolomorphicMotions
import References.Hubbard2006.Ch05.S04_QuadraticDifferentials
import References.Hubbard2006.Ch06.S03_SchwarzianDerivative
import References.Hubbard2006.Ch06.S07_ContinuousSection
import References.Hubbard2006.Ch06.S10_KobayashiMetric
import References.Hubbard2006.Ch06.S11_BersEmbeddingOpen
import References.Hubbard2006.Ch06.S12_QuasiFuchsian
import References.Hubbard2006.Ch07.S01_FiniteDimensionalTeichmuller
import References.Hubbard2006.Ch07.S02_TeichmullerTheorem
import References.Hubbard2006.Ch07.S03_MumfordCompactness
import References.Hubbard2006.Ch07.S04_RoydenTheorem
import References.Hubbard2006.Ch07.S05_AnalyticSections
import References.Hubbard2006.Ch07.S06_FenchelNielsen
import References.Hubbard2006.AppA3_RiemannHurwitz
import References.Hubbard2006.AppA6_CompactPerturbations
import References.Hubbard2006.AppA10_RiemannRoch

/-!
# Hubbard 2006, *Teichmüller Theory*, Vol. 1 (statement level)

J. H. Hubbard, *Teichmüller Theory and Applications to Geometry, Topology, and Dynamics*, Vol. 1: *Teichmüller Theory*,
Matrix Editions, 2006. OCR sources (MinerU `full.md`): `…-d20b3cc3-…` (front matter – Ch. 4), `…-4880e2ce-…` (Ch. 5 –
A6), `…-43ab0746-…` (A7 – index). Namespace `Hubbard2006`. Statements only: every definition is genuine, every theorem
is `:= by sorry`. Written by Lane B (W1 and W2, 2026-10).

**Status: batches 2a–5, W2a–W2e (Chapter 1; Chapter 2 §2.1, 2.2, 2.4; Chapter 3 §3.1–3.9; Chapter 4 §4.2–4.9; Chapter 5
§5.1, 5.2, 5.4; Chapter 6 §6.3, 6.7, 6.8, 6.10–6.12; Chapter 7 §7.1–7.6; Appendices A3, A6, A10). Vol. 1 is closed.**
§2.3 (geodesic curvature, the canoeing theorem; cited only in Vol. 2) is omitted (scope); §7.7–7.8 (Petersson–Weil,
Wolpert) and Appendix A2 (Dehn twists) are deferred; Appendix A6.2 and Appendices A7–A9, A11 are omitted (scope) and the
line-bundle statements of A10 are deferred; Chapters 4 §4.1, 5 §5.3 and 6 §6.4–6.5 are concordances (all `exists:`
pointers in the inventory); Appendices A1 (partitions of unity, Mathlib), A4 (higher-dimensional almost-complex
structures, cited only in remarks) and A5 (Banach analytic maps: Hartogs, the implicit function theorem; general
analysis,
the only users in Hubbard being the deferred analytic families) are omitted (scope).

**Deferred items of Chapters 4–6 (one per line, with the reason).**
- Prop. 4.8.13, 4.8.14, Lemma 4.8.15, Prop. 4.8.17, 4.8.19: universal curve over `ℳ(X)`, analytic dependence —
    Banach-analytic
  manifolds on `ℳ(X)` and `ℳ(X) × X`.
- Thm 5.1.12: extension of quasisymmetric maps `S¹ → ℙ¹` — Möbius-normalized modulus (5.1.24) and the topology on
    maps of `ℙ¹`.
- Thm 5.3.3–5.3.5: Gauss–Bonnet for quadratic differentials, cylinder decomposition — flat metrics with cone points.
- §6.1, §6.2 (quasiconformal surfaces, analytic families of Riemann surfaces): Banach-analytic families.
- Def. 6.4.7, Prop. 6.4.9: `QC⁰(S)`, ideal boundary rel `I(S)` — the ideal boundary is not modelled.
- Thm 6.6.1, Prop. 6.6.2, Lemma 6.6.3, Cor. 6.6.4, Thm 6.6.5: tangent and cotangent spaces, Finsler metric — tangent
    spaces
  of `𝒯_S` (Banach-analytic structure, the differential of the Bers chart).
- Cor. 6.7.2: `𝒯_S` contractible — no bundled topology on `LiZhongQC.TeichGamma`.
- Cor. 6.8.2, Prop. 6.8.3–6.8.7: `QC⁰(S)` contractible, universal curve `Ξ_S` and its universal property —
    Banach-analytic
  manifolds and `I(S)`.
- Prop. 6.9.3, Cor. 6.9.4: Bers construction of the universal Teichmüller curve — `Ξ_S` (as above); Prop. 6.9.1, Def.
    6.9.2
  (the Bers fibre space) are `exists:` pointers to the installed `Nag1988` / `LiZhongQC.BersFiberSpace`.
- Prop. 7.4.2, Lemmas 7.4.3, 7.4.5, Prop. 7.4.4, Def. 7.4.6–7.4.10, Prop. 7.4.11, 7.4.14: derivative of Royden's
  isometry and the flag
  machinery — tangent spaces of `𝒯_S` (7.4.2); proof steps of 7.4.15 (the others).
- Prop. 7.5.3, Cor. 7.5.4, Prop. 7.5.5: derivative of an analytic section, norm one projectors — tangent spaces and
  Kobayashi
  balls of `Ξ_S`.
- Thm 6.10.6, Cor. 6.10.7, 6.10.8: infinitesimal Kobayashi = Teichmüller, contraction by analytic self-maps, the
    universal
  curve — tangent spaces of `𝒯_S` and the Banach-analytic structure.
- Thm 6.11.1: the Bers embedding is open — analytic structure on `𝒯_S` for a general quasiconformal surface.
- Prop. 6.12.4 (2), Thm 6.12.5: analyticity of `QF`, quasi-Fuchsian reciprocity — Banach-analytic `𝒯_X × 𝒯_{X*}` and the
  derivative of the Bers embedding.

**Conventions.**
(1) Riemann surface: `[TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]`, no
  second countability (Radó's theorem is `thm1_3_3`). `ℙ¹ = References.RiemannSphere` (scoped charts, `open scoped
  References`), `𝔻 = LiZhongQC.unitDiscOpens`.
(2) `H¹(X, ℝ)` is `Hom(π₁(X), ℝ)` (`HasTrivialH1`), the book's own reading (H1:364); hyperbolic Riemann surfaces and
  Fuchsian uniformizations are written with `ℍ` (`IsHyperbolicRS`, the project's `IsUniformization Γ p`).
(3) The shared notions are in `References/Common/`: harmonic functions and Perron families (`RiemannSurfaceHarmonic`),
  hyperbolic geometry (`HyperbolicSurface`), Fenchel–Nielsen lengths and twists (`FenchelNielsen`).
(4) Hyperbolic metric (Chapter 3): curvature `−1`, `ρ_ℍ = |dz| / Im z`, relative to a uniformization `p : ℍ → X` by a
  torsion-free Fuchsian group (`hypNormSurf`, `hypDistSurf`); closed geodesics are the algebraic ones (`p '' axisH g`).

**Conventions of Chapter 7 and the appendices.**
(5) *Teichmüller distance.* Hubbard's `d` is `inf ln K` (display (6.4.2)), the installed `LiZhongQC.teichDistance` and
  `teichDistanceFT` are `½ inf ln K`; so Hubbard's `d` is `2 · teichDistance(FT)` and the statements use that factor.
  The Teichmüller spaces are the project's `TeichSpace S₀` and `TeichSpaceFiniteType S₀ g n 0` (no ideal boundary).
(6) *Moduli space.* `Moduli(S)` carries the quotient Teichmüller topology, which is metrizable, so compactness is stated
  as sequential compactness with `ModuliConverges` (quasiconformal homeomorphisms `f_n : X_n → X` with `K(f_n) → 1`);
  `HasSystoleAtLeast` uses the Poincaré metric `|dz|/Im z`, where a simple closed geodesic `p '' axisH g` has length
  `translationLength g`.
(7) *Fenchel–Nielsen.* The lengths and twists are `References.lengthOf` and `References.twistOf`; the topological datum
  is the installed `ImayoshiTaniguchi1992.IsDecomposingSystemLoops` / `IsAdjacentPantsDatum` (closed surfaces of genus
  `≥ 2`); the case with punctures is deferred.
(8) *Euler characteristic.* `eulerCharTop` is the alternating sum of the dimensions of the singular homology groups with
  real coefficients (`finsum` and `Module.finrank`: junk `0` for infinitely many non-zero or infinite dimensional
  groups, excluded by the finiteness hypotheses of the statements).

(9) *Appendices A6 and A10.* Operators are continuous linear maps of Banach spaces over `𝕜` (`RCLike`);
  quasi-isomorphisms are Mathlib's `ContinuousLinearMap.IsFredholm` and `LinearMap.index`; `transposeCLM f` is the dual
  map `f^⊤`. The Cauchy transform `(1/πz) ∗ f` is `cauchyTransform f`, the Hölder seminorm `holderSemi α f` is valued in
  `[0, ∞]`. In A10 the groups `H⁰`, `H¹` are those of `Forster1981` (§12) for the sheaves `𝒪`, `Ω`; `HasGenus` is the
  topological genus (Hubbard's `½ dim_ℝ H¹(X, ℝ)`), whereas Forster's `genus` is `dim H¹(X, 𝒪)`.

**Readings of the book approved by the leader (2026-10-09).**
(a) `lemma1_1_5`: "the structure coincides with the standard one on `𝔻`" is "the inclusion `𝔻 → 𝔻 ∪ {∞}` is
  holomorphic".
(b) `prop1_5_1`, `prop1_6_1`: the pieces are connected with non-empty boundary (the standing situation of Prop. 1.4.1);
  "`ℝ₊`" in Prop. 1.5.1 is read as `G ≥ 0` (strict positivity on the boundary would contradict vanishing there).
(c) `prop1_2_3` is stated for Farkas–Kra's Perron families (`References.IsPerronFamily`), a larger class than Hubbard's.
(d) `IsKleinianGroup` is `DiscreteTopology Γ` (near miss `Lehto1987.IsKleinian`); Prop. 1.8.14 is an `exists:` pointer
  to `GardinerLakic2000.thm2_2_c`, `thm2_2_d`.
(e) Chapter 3: a trouser has no funnels (`IsTrouserCore`); isometry of surfaces with geodesic boundary is conjugacy of
  the pairs `(Γ, C)` by an isometry of `ℍ`; Prop. 3.3.9 (2) and Def. 3.3.10 (minimal position) are deferred (no
  intersection counts of curves on a surface); the manifold-with-boundary part of Prop. 3.7.1 is deferred.

(f) Chapter 4 §4.2: `ℋ¹(U)` is defined through distributional derivatives (`IsH1With`), `Cℋ¹(U)` is its continuous
  part; Prop. 4.2.4 states the existence of the integer `d` in the Jacobian formula (the degree through `H_c²` is not
  modelled; `d` is determined by the formula); in Prop. 4.2.11 (2) the formulas for `f ∘ h` assume that `h` has no
  critical points (so the a.e. values of the partials of `f` at `h(z)` are well defined).
(g) Chapter 4 §4.3: the cylinder `A_m = B_m / ℤ` is the round annulus `{1 < |w| < e^{2πm}}`
  (`References.roundAnnulus m`)
  with the covering `covA : z ↦ e^{−2πi z}` (Exercise 3.2.4); a lift of a map of cylinders is read through `covA`
  (`IsCylinderLift`). Chapter 4 §4.4: surfaces are quantified over `Type`.

(h) Chapter 4 §4.7: the hydrodynamically normalized solution `w^μ` (`IsWMu`) is not the installed `IsNormalizedSolution`
  (fixing `0`, `1`, `∞`), which is Notation 4.7.5; analyticity is stated as continuity plus analyticity of
  `μ ↦ w^μ(z)` in the norm topology of `L^∞` (`AnalyticOn` within the ball for supports in a compact set).
(i') Chapter 4 §4.8: one-dimensional complex vector spaces are modelled by `ℂ` through `u(z) = a z + b z̄`; the Riemann
  surface `X_μ` is stated by its universal property (a quasiconformal map onto a Riemann surface with Beltrami form `μ`,
  unique up to biholomorphism), the Beltrami forms are the installed `IsBeltramiDifferential`. Chapter 4 §4.9: the
  extension and Carathéodory statements assume the boundary extension where the book proves it (Prop. 4.9.14); a
  reflection is a global involution (`IsCurveReflection`); bounded hyperbolic distance uses `discPoincareDist`.

(j) Chapter 5 §5.1–5.2: the Douady–Earle extension is the installed `Pommerenke1992.douadyEarleExt` with the modulus
  `λ` of `IsQuasisymmetricWith`; Thm 5.1.12 (extension of quasisymmetric maps `S¹ → ℙ¹`) is deferred (the
  Möbius-normalized modulus (5.1.24) and the topology on maps of `ℙ¹` are not modelled); holomorphic motions are maps
  `Λ × X → ℙ¹` over a complex manifold `Λ` modelled on a Banach space (`IsHolMotionP1`), the quasiconformality of
  `φ_λ|_X` on a subset `X` is read as "restriction of a quasiconformal homeomorphism of `ℙ¹`" (`IsKQCP1`).
(k) Chapter 5 §5.4: quadratic differentials of `X = ℍ/Γ` are read on the universal cover (`IsAutomorphicQD`,
  installed `integrableAutomorphicQD` for `Q¹`); finite type is read as finite hyperbolic area; the pairing of
  `Q¹(X)` and `Q^∞(X*)` is `∬_F q(z) p(z̄) (Im z)² dx dy`; the direct image is the sum over coset representatives.
  Chapter 6 §6.3: `D³` in Definition 6.3.2 is the cubic Taylor coefficient (so that (6.3.6) holds).

(l) Chapter 6 §6.7–6.12 are read in the Fuchsian model of the project: `ℳ(X) = LiZhongQC.BeltramiGamma Γ`,
  `𝒯_X = LiZhongQC.TeichGamma Γ` with the pseudo-distance `teichDistanceGamma` (`= ½ ·` Hubbard's `d`, D18);
  continuity in
  `ℳ(X)` is for the `L^∞` norm; the ideal boundary is not modelled (Prop. 6.8.1 is stated for non-elementary groups).
  Kobayashi balls of Riemann surfaces use tangent vectors in the preferred chart and the factor `½` of Definition
  6.10.1;
  the quasi-Fuchsian representation is recorded by the relation `IsQFConj` (`f ∘ γ = g ∘ f`).

(m) Chapter 7 §7.4–7.5 are read in the Fuchsian model: Royden's theorem is stated for finite type with punctures (the
  closed
  case is the installed `ImayoshiTaniguchi1992.thm6_20_a`, `thm6_20_b`); an analytic section of the universal curve
  `V(Γ) = F(Γ)/Γ` is a section that lifts locally to a holomorphic function on an open set of `B(Γ)` (Nag's `IsBHolOn`);
  the trivialization statement 7.5.2 is stated through the infinitely many analytic sections it would give.

**Corrections to the book.**
(i) Thm 3.6.2 and Cor. 3.6.3 (`thm3_6_2`, `cor3_6_3`): the hypothesis "`X` is not simply connected" does not exclude `X
  = 𝔻*`, which has no simple closed geodesic, so no trouser decomposition (its only complementary component is `X`,
  whose lift is the punctured-disc model `IsPuncturedDiscModel`, not a trouser, half-annulus or half-plane). The
  hypothesis "`X` is not `𝔻*`" is added (`hnp`: `Γ` is not generated by one parabolic element). Prop. 3.7.3 and Cor.
  3.6.4 stay true without it (both sides are false for `𝔻*`).

(ii) Prop. 3.9.10 (`prop3_9_10`): the presentation (3.9.6) of the triangle group lists only `R_α^p, R_β^q, R_γ^r`, but
  with `R_i = r_{i+1} r_{i+2}` one has `R_0 R_1 R_2 = 1`, a relation that does not follow from the powers (the group
  generated subject to the powers alone is the free product `ℤ/p * ℤ/q * ℤ/r`); the relation `R_0 R_1 R_2` is added, and
  the presentation is read in `PSL(2, ℝ)` (`R_i ∈ SL(2, ℝ)` has `R_i ^ p_i = −I`) through `toPSL ∘ R` (H1:2823–2833).

(iii) A3.3 [misprint]: the sum (A3.5) defining the Euler characteristic starts at `i = 1`; formula (A3.4) and the text
  need `i = 0`, which is used.
(iv) A2.3 [defect, not stated: Appendix A2 is deferred]: Lemma A2.3 as printed is false for `S = ℝ²`: two homotopic
  embeddings `γ₀`, `γ₁` of opposite orientation cannot differ by an orientation preserving diffeomorphism `f` with `f ∘
  γ₁ = γ₀`. The proof uses a hyperbolic structure and a geodesic representative of `γ₀`, so the lemma needs `S`
  hyperbolic and `γ₀` essential. Also the printed `f ∘ γ₁ = γ₂` should read `f ∘ γ₁ = γ₀`.

(v) A6.3.5 [imprecision]: the printed `‖f‖_α` is a seminorm (it vanishes on constants) and "the `0`-Hölder norm is the
  sup-norm" is false for the printed formula (it gives the oscillation); `‖f‖_0` is read as the sup norm and `‖f‖_α` as
  the printed seminorm, and then Thms A6.3.2, A6.3.4 are true as stated.
(vi) A6.3.1 [missing hypothesis]: no regularity of `f` is stated; for merely continuous `f` the identity `∂̄ T f = f`
  holds only in the sense of distributions, so the statement takes `f` of class `C¹` with compact support.
(vii) A10.1.1 [identification]: Hubbard's genus is topological; the equality with `dim H¹(X, 𝒪)` is the content of the
  proposition (Forster takes it as the definition of the genus).

(viii) Thm 4.3.2 (Grötzsch), equality case (`thm4_3_2_b`): the book says that equality in (4.3.2) forces a lift of
  the form
  `x + i y ↦ x + x₀ + i (m'/m) y`. The orientation-preserving map that lifts to the boundary-swapping affine map
  `x + i y ↦ x₀ − x + i (m' − (m'/m) y)` (for `m = m'`, `w ↦ R / w` on `{1 < |w| < R}`) is also extremal and is not of
  the
  stated form; the statement gives both forms (`affA`, `affB`) and `thm4_3_2_c` shows both are quasiconformal.

(ix) Thm 4.5.4 (`thm4_5_4_a`): "a quasisymmetric homeomorphism is quasiconformal" needs the hypothesis that it
  preserves orientation: the conjugation `z ↦ z̄` is quasisymmetric with modulus `h = id`, but Definition 4.1.1
  (`|∂f/∂z̄| ≤ k |∂f/∂z|`) excludes it. `IsSensePreserving f U` is added (in `cor4_5_11` the book states it).
(x) Prop. 4.5.14: labeled quasisymmetry (Definition 4.5.13, "for any three points of `W`") must be read locally for
  homeomorphisms of open sets (`IsLocallyLabeledQS`); the global notion fails for the conformal map of a disc onto a
  slit disc, which Remark 4.5.2 (2) itself describes. Cor. 4.5.11: the printed "skew `(a, b, d) ≤ 3`" is a misprint
  for the triple `(a, b, c)`.
(xi) Prop. 5.4.17 (`prop5_4_17`): "the image of the unit ball of `Q¹(Y)` contains the ball of radius `3` of `Q¹(X)`"
  contradicts `‖π_*‖ ≤ 1` (Prop. 5.4.16: a `ψ` with `‖ψ‖_1 = 3` would need `‖φ‖_1 ≤ 1` and
  `3 = ‖π_* φ‖_1 ≤ ‖φ‖_1`). The proof (5.4.60) gives `‖φ‖_1 ≤ 3 ‖ψ‖_1`, i.e. the ball of radius `1/3`; this is what is
  stated. Both statements on `π_*` also need `−1 ∈ Γ_X → −1 ∈ Γ_Y` (otherwise `π_*` counts every preimage twice, e.g.
  `Γ_X = Γ_Y ∪ −Γ_Y`, `π_* φ = 2 φ`).
(xii) Thm 6.3.10 / equation (6.3.24) (`ahlforsWeillCoeff`): the printed `μ_q = 2 y² q(z̄) dz̄/dz` has the wrong sign;
  the
  book's own extension (6.3.25) has `∂̄f/∂f = (z − z̄)² q(z̄)/2 = −2 y² q(z̄)`, and with `+2 y² q(z̄)` one gets
  `S{f, z} = −q`. The sign `−` (as in `LiZhongQC.lemma33_3`) is used.

(xiii) Prop. 6.10.4 (`prop6_10_4`): the Kobayashi ball of the unit ball `B` of a Banach space at `0` is the *closed*
  ball of
  radius `1/2` (the maps `t ↦ t ξ` with `‖ξ‖ = 1` take `𝔻` into `B` and attain the boundary), not `½ B` for the open
  ball.

(xiv) Thm 7.4.1 (`thm7_4_1`): "the group of automorphisms of `𝒯_S` is `MCG(S)`" holds only modulo the kernel of the action:
  the hyperelliptic involution acts trivially on `𝒯_S` for `(g, n) = (2, 0)` and `(1, 2)` (the quotient `MCG/ℤ₂`), and the
  kernel is trivial otherwise (`dim 𝒯_S > 1`). Moreover for `(g, n) = (1, 2)` the map `MCG(S) → Aut(𝒯_S)` is not onto:
  `𝒯_{1,2} ≅ 𝒯_{0,5}` (Patterson, Earle–Kra), whose automorphism group `MCG(0, 5)` contains the image with index `5`;
  surjectivity is therefore not claimed for `(1, 2)`.

(xv) Thm 3.5.8 (`thm3_5_8`): for three cusps the orientation of the cusps is not recorded by `IsTrouserCoreWithLengths`,
  and the triples `(A, B, C)`, `(A⁻¹, B⁻¹, BA)` of `Γ(2)` are not `SL(2, ℝ)`-conjugate; the `SL(2, ℝ)` uniqueness is
  stated when some boundary length is positive and, for all lengths, with conjugation in `GL(2, ℝ)` (the book's "unique
  up to isometry").

(xvi) Prop. 4.2.11 (1) (`prop4_2_11_a'`): `f ∘ k ∈ Cℋ¹` for an arbitrary `C¹` map `k` is false (restriction to a line);
  `jacobian k ≠ 0` is added.

(xvii) Prop. 4.5.3 (1) (`prop4_5_3_a`): the inverse of `g ∘ f` has modulus `h₁ ∘ h₂`, so the composite has the modulus
  `max (h₂ ∘ h₁) (h₁ ∘ h₂)`.

(xviii) Prop. 3.3.8 (`prop3_3_8`): the book's alternative "`α` null-homotopic" is excluded by the primitivity assumption
  as modelled; the hypothesis is read as "`α` null-homotopic or primitive".

**Counts (batches 2a–5, W2a–W2e).**

| File | definitions | statements | exists | omitted / deferred |
|---|---|---|---|---|
| `Ch01/S01_TwoStatements` | 1 | 4 | 1 | 0 |
| `Ch01/S02_SubharmonicHarmonic` | 2 | 2 | 2 | 1 |
| `Ch01/S03_Rado` | 0 | 3 | 0 | 2 |
| `Ch01/S04_Exhaustion` | 0 | 1 | 0 | 3 |
| `Ch01/S05_GreenFunctions` | 1 | 1 | 0 | 0 |
| `Ch01/S06_SimplyConnectedPieces` | 0 | 1 | 0 | 0 |
| `Ch01/S08_FirstClassification` | 3 | 6 | 3 | 7 |
| `Ch02/S01_PlaneHyperbolicGeometry` | 1 | 8 | 2 | 1 |
| `Ch02/S02_CurvatureOfConformalMetrics` | 1 | 2 | 1 | 1 |
| `Ch02/S04_HyperboloidModel` | 3 | 2 | 4 | 1 |
| `Ch03/S01_FuchsianGroups` | 2 | 4 | 0 | 1 |
| `Ch03/S02_ClassificationOfAnnuli` | 3 | 4 | 0 | 3 |
| `Ch03/S03_HyperbolicMetric` | 3 | 13 | 0 | 3 |
| `Ch03/S04_LimitSets` | 3 | 5 | 1 | 1 |
| `Ch03/S05_Trousers` | 7 | 4 | 2 | 1 |
| `Ch03/S06_TrouserDecomposition` | 4 | 3 | 1 | 0 |
| `Ch03/S07_IdealBoundaries` | 1 | 2 | 1 | 2 |
| `Ch03/S08_CollaringTheorem` | 3 | 6 | 0 | 3 |
| `Ch03/S09_FundamentalDomains` | 18 | 7 | 1 | 4 |
| `Ch04/S02_SobolevSpaces` | 7 | 8 | 1 | 1 |
| `Ch04/S03_GroetzschTheorem` | 5 | 5 | 0 | 2 |
| `Ch04/S04_NormalFamilies` | 0 | 4 | 0 | 2 |
| `Ch04/S05_GeometricCharacterizations` | 5 | 9 | 0 | 2 |
| `Ch04/S06_MappingTheorem` | 0 | 2 | 0 | 1 |
| `Ch04/S07_DependenceOnParameters` | 5 | 3 | 1 | 1 |
| `Ch04/S08_BeltramiForms` | 6 | 7 | 1 | 2 |
| `Ch04/S09_BoundaryValues` | 8 | 10 | 3 | 2 |
| `Ch05/S01_DouadyEarleExtension` | 0 | 2 | 5 | 2 |
| `Ch05/S02_HolomorphicMotions` | 4 | 4 | 2 | 2 |
| `Ch05/S04_QuadraticDifferentials` | 10 | 10 | 1 | 1 |
| `Ch06/S03_SchwarzianDerivative` | 3 | 8 | 0 | 1 |
| `Ch06/S07_ContinuousSection` | 0 | 2 | 0 | 2 |
| `Ch06/S10_KobayashiMetric` | 2 | 6 | 0 | 1 |
| `Ch06/S11_BersEmbeddingOpen` | 1 | 1 | 0 | 1 |
| `Ch06/S12_QuasiFuchsian` | 3 | 2 | 0 | 1 |
| `Ch07/S01_FiniteDimensionalTeichmuller` | 0 | 0 | 1 | 2 |
| `Ch07/S02_TeichmullerTheorem` | 0 | 2 | 1 | 2 |
| `Ch07/S03_MumfordCompactness` | 2 | 2 | 0 | 3 |
| `Ch07/S04_RoydenTheorem` | 1 | 2 | 0 | 2 |
| `Ch07/S05_AnalyticSections` | 1 | 3 | 0 | 1 |
| `Ch07/S06_FenchelNielsen` | 0 | 5 | 3 | 1 |
| `AppA3_RiemannHurwitz` | 3 | 2 | 0 | 1 |
| `AppA6_CompactPerturbations` | 7 | 11 | 1 | 2 |
| `AppA10_RiemannRoch` | 2 | 3 | 1 | 4 |
-/
