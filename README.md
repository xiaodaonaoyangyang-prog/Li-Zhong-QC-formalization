# 李忠《拟共形映射及其在黎曼曲面论中的应用》— Lean 4 formalization (statement level)

A statement-level ("skeleton") formalization of

> 李忠, *拟共形映射及其在黎曼曲面论中的应用* (Li Zhong, *Quasiconformal Mappings and
> Teichmüller Spaces*).

Every definition of the book is a genuine Lean definition, and every theorem, lemma,
corollary and numbered formula is stated.
- Proofs are being filled in section by section; the statements still open carry a `sorry`.
- As of 2026-09-26, 130 remain, mostly in the compact-surface chapters §25–§32.
- Chapters 1–2 are complete apart from one item of §7.
- Where the book quotes a result it does not prove (uniformization, Riemann–Roch), the dependent statements
  stay open, and their content is proved as `…_of_uniformization` companions (see *Modelling conventions*).

## Building

The project uses Lean `v4.35.0-rc2` (`lean-toolchain`) and Mathlib at commit
`2f3d8f63005779e9d708eb9adf3feca54aa24ceb` (2026-09-22).

`lakefile.toml` points to a local checkout of that commit (`D:/lean/mathlib4-latest`). To build elsewhere:
1. Replace that `[[require]]` block by

   ```toml
   [[require]]
   name = "mathlib"
   git = "https://github.com/leanprover-community/mathlib4"
   rev = "2f3d8f63005779e9d708eb9adf3feca54aa24ceb"
   ```

2. Run `lake update mathlib`.
3. Optionally run `lake exe cache get`, if prebuilt Mathlib files exist for that commit.

```
lake build            # builds the whole library (root module `LiZhongQC`)
```

The build succeeds with `declaration uses 'sorry'` warnings only.

**Statistics** (2026-09-14, after Theorem 19.3, Lemmas 35.4 and 35.6, and the §14, §25, §26 and §27
items listed below):
* 36 section files, `Basic.lean`, `RiemannMapping.lean`, `ClusterSets.lean` and the auxiliary
  `Lemmas/` folder (57 files).
  * Registered on 2026-09-13, all without `sorry`: `RiemannMapping.lean` (namespace `RMT`, the
    Riemann mapping theorem via the extremal problem), `Lemmas/ConnectedComplement.lean` (Cauchy's
    theorem for polygons, primitives, logarithms and square roots on domains with connected
    complement) and `Lemmas/CanonicalForm.lean` (Theorem 2.1, cases (i) and (ii)).
  * Registered on 2026-09-14 by the user's decision, through the new import of
    `Lemmas/RectangleRigidity.lean` in `Ch01/S01_Quadrilateral.lean`:
    `Lemmas/RectangleRigidity.lean` (rigidity of conformal maps between rectangles, no `sorry`),
    `ClusterSets.lean` (Schwarz reflection, the Hahn–Mazurkiewicz theorem, cluster sets; 3 `sorry`)
    and `Lemmas/Caratheodory.lean` (Carathéodory's theorem and prime ends; 7 `sorry`).  Each of
    these 10 `sorry`s needs a classical theorem that Mathlib lacks, such as the Jordan curve
    theorem, the Hahn–Mazurkiewicz theorem, harmonic-measure estimates or prime-end theory.
  * New on 2026-09-14: `Lemmas/LocalRoots.lean` (local square roots, primitives, the descent
    through the squaring map and factorization of analytic functions near a point; no `sorry`),
    a leaf imported by S25 and S32.
  * New on 2026-09-14: `Lemmas/SchwarzChristoffelRect.lean` (the Schwarz–Christoffel map of the
    upper half-plane onto a rectangle and its boundary correspondence; no `sorry`), imported by S01.
  * New on 2026-09-14: `Lemmas/RectangleQuad.lean` (every rectangle is a topological quadrilateral:
    the elliptic side integrals depend continuously on the modulus `k` and their ratio sweeps
    `(0, ∞)`, so the intermediate value theorem and the inverse Schwarz–Christoffel map give the
    conformal map onto `ℍ`; no `sorry`), which entered the root build through S09.
  * New on 2026-09-14: `Lemmas/KrausNehari.lean` (the Kraus–Nehari coefficient bound
    `|a₃ - a₂²| ≤ 1` for univalent functions, via an area theorem proved with a two-mode Bessel
    inequality, the change of variables formula and a pointwise ellipse containment; Mathlib only,
    with no degree theory and no Jordan curve theorem; no `sorry`), which entered the root build
    through S19.
* 466 definitions, structures and instances, none of which contains `sorry`.
* 1809 top-level theorems and lemmas:
  * 361 still have a `sorry` proof;
  * 1448 are proved.
* These source counts ignore comments and include declarations written with an attribute on the
  same line, such as `@[simp] theorem`.  Measured that way, the tree of 2026-09-13 had 399
  definitions and 1127 top-level theorems.  The figures of 402 and 1125 published on 2026-09-13
  came from a cruder count that matched three declaration-like lines inside comments and missed
  five one-line attribute declarations.
* Counting every theorem, including those inside nested namespaces, there are 2025, and they
  partition exactly: **1646 are axiom-clean**, 361 are the `sorry` statements themselves, and the
  remaining **18 have complete proofs that nevertheless depend on a statement which is still
  `sorry`**.  A finished proof is therefore not by itself a guarantee: check with `#print axioms`.
  (The root `Audit.lean` counts the `LiZhongQC` namespace only and prints 1593 + 361 + 18 = 1972;
  the other 53 theorems live in namespace `RMT` and are all axiom-clean.)
* Compared with 2026-09-13, the `sorry` column first grew by 10: `thm1_1_rectangle_unique` left
  it, and the 11 `sorry`s of `ClusterSets.lean` and `Lemmas/Caratheodory.lean` entered the root
  build.  Later the same day `eq19_2_ode` (S19) and `iversen_gross` (`ClusterSets.lean`) were
  proved, which brought the column to 413, and the proofs of `thm19_1_unique` (S19),
  `eq30_7_annulus_modulus` (S30) and `project_admissibleQD_order` (S32) brought it to 410.
  Then the §14 Poincaré-distance cluster (`eq14_3`, `poincareDist_upperHalf` and
  `upperHalf_geodesic`) and the §25 natural-parameter batch ((25.2), (25.3), (25.5), (25.6),
  (25.8) and (25.9): `eq25_2_natural_parameter`, …, `eq25_9_natural_parameter_double_pole`) brought
  it to 401.  None of these had carriers depending on it.
  Finally the proofs of `thm1_1_exists_rectangle` and `thm1_1_elliptic_modulus` (S01), `eq14_8` and
  `eq14_9` (S14), `eq35_1_radii_finite_length` and `circular_arcs_short` (S35), and four items from
  the parallel session (`hasGenus_of_homeomorph` in S28, `thm22_1_monodromy` and
  `mobius_classification_trace` in S22, `pairing_eq_norm_imp_teichmuller` in S36) brought it to 391.
  Then Lemma 9.2 in both directions (`lemma9_2_isACL_of_genPartials`,
  `lemma9_2_genPartials_of_isACL`) and Theorems 9.1 and 9.2 (`thm9_1_isACL`, `thm9_2_partials_ae`)
  brought it to 387.  The carriers that used them still wait on other §9 statements.
  Then these brought it to 376:
  * the §11 batch (`eq11_8`, `eq11_11_pompeiu_gen`, `eq11_15`, `eq11_17`);
  * the §14 modular identities (`eq14_4`, `eq14_5`, `eq14_12`);
  * `translationLength_eq_inf_dist` (S30);
  * from the parallel session, Theorem 20.1 (`thm20_1_disc_isSchwarz`, `thm20_1_not_isSchwarz`,
    `thm20_1`).
  Then these brought it to 372:
  * `cocompact_elements_hyperbolic`, `lengthSpectrum_discrete` and `parabolic_horoball_disjoint`
    (S30);
  * from the parallel session, Theorem 19.2 (`thm19_2_nehari`, S19), which also retired the
    carrier `eq19_5`.
  Then these brought it to 361:
  * `eq26_5_injective`, `teichStretchZero_localHomeomorph` and
    `teichmullerBeltrami_isBeltramiDifferential` (S26);
  * `hyperbolic_normal_form` (S27);
  * `lemma35_4` and `lemma35_6` (S35);
  * from the parallel session, Theorem 19.3 and its corollary (`thm19_3`, `thm19_3_cor`, S19),
    `horizontal_vertical_isPhiStraight` and `local_shortest_regular` (S25), and
    `modularPhi_gamma2_invariant` (S14).
* **Corrections** (2026-09-14):
  * Four statements about `C₀^∞` functions were written with `ContDiff ℝ ⊤`.  In current Mathlib
    that means real-analytic, so together with compact support they only covered the zero function.
    They now use `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`, i.e. `C^∞`: `eq11_15`, `zygmund_calderon`
    and `eq11_17` in S11, and `thm12_1_smooth_case` in S12.
  * `parabolic_horoball_disjoint` (S30) was false as stated.  For `Γ = ⟨z ↦ z + 1/2⟩`, the
    translation `γ₁ : z ↦ z + 1` lies in `Γ`, and `z ↦ z + 1/2` is not a power of `γ₁` but has
    `c = 0`.  The hypothesis that `γ₁` generates the stabilizer of `∞` in `Γ` (up to sign), implicit
    in the book, was added, and the statement is now Shimizu's lemma.
  * `lemma35_5` (S35) was false as stated, and so is the book's Lemma 35.5.  Its hypothesis (35.11),
    `∬_E |φₙ| |κ|²/(1 - |κ|²) → 0` for `E = {|κ| ≤ k'}`, does not force `∬_E |φₙ| → 0`.  For
    `κ = ½·1_{Re z > 0}` and `φₙ ≡ 1/π` the integrals over the left half-disc `E` vanish, yet
    `∬ |φₙ| |κ|²/(1 - |κ|²) = 1/6 ≠ 1/3 = k²/(1 - k²)`.  The hypothesis is now (35.10),
    `∬_E |φₙ| → 0`, which is what the book's proof uses, and measurability of `κ` is assumed.  The
    book also misprints the limit as `k/(1 - k²)`.
* Those 18 carriers are not scattered — each traces back to one of five blocked groups, and
  clearing a blocker retires its whole group at once (measured 2026-09-14, figures below verified
  against the environment, not maintained by hand):
  * **9 via the §9 cluster** (`lemma9_1_menchoff`, `thm9_4_dilatation_ae`,
    `thm9_6_absolutelyContinuous`, `thm7_2_inv`; `thm9_1_isACL`, `thm9_2_partials_ae` and Lemma 9.2
    have been proved since the previous count) — `thm9_3_differentiable_ae`,
    `thm9_5_L2_derivatives`, `thm9_6_cor1_null`/`cor2_jacobian_pos`, and both halves of
    Theorem 10.2.
  * **3 via §11** (`thm11_3_isometry`, `hilbertNorm_continuousOn`) — `thm11_3_cor1` (isometry
    only), `thm11_3_cor2` and `eq12_1_exists_exponent` (both).
  * **3 via the classical theorems behind Carathéodory's theorem**, new in the root build since
    2026-09-14: `frontier_locallyConnected_iff_isCurve` and `hahn_mazurkiewicz_subset` via
    `hahn_mazurkiewicz`, and `locallyConnected_iff_clusterSet_subsingleton` via
    `caratheodory_continuous_iff`.
  * **2 via `thm6_1_modulus_quasi_invariance`**: `ellipse_isKQuasicircle` and
    `isKQC_of_isC1Quasiconformal`.
  * **1 via `thm2_1_canonical_form_annulus`** (Theorem 2.1, case (iii): the annulus map for two
    nondegenerate complementary components): `thm2_1_canonical_form` itself, proved by cases from
    `Lemmas/CanonicalForm.lean`.
  * Retired on 2026-09-14: `eq19_5` ((19.4)–(19.5), `‖S_f‖_Δ ≤ 3/2` for univalent `f`), now that
    Theorem 19.2 (`thm19_2_nehari`) is proved.
  * Retired on 2026-09-14: the 25 carriers of `thm1_1_exists_rectangle`, nearly the whole
    modulus/Rengel layer of §1, §4 and §5 (`thm4_2_rengel`, `thm4_5_modulus_mono`,
    `thm4_8_modulus_continuous`, `thm1_3_modulus_conformal_invariant`, `isQCRS_refl`, `modulus_pos`,
    the `rengel_*` and other `modulus_*` lemmas), now that Theorem 1.1 is proved
    (`Lemmas/SchwarzChristoffelRect.lean`).
  * Retired on 2026-09-14: `thm19_1_exists`, now that `eq19_2_ode` is proved.  Its holomorphic
    solutions come from Picard iteration on the domain itself, estimated along the images of
    radii under an inverse Riemann map, so no analytic continuation or monodromy is needed.
  * Retired on 2026-09-14: `thm1_1_rectangle_unique` is now proved.  Reflection in the sides
    extends the map between the rectangles to an entire function with doubly periodic derivative,
    and Liouville's theorem makes it a similarity (`Lemmas/RectangleRigidity.lean`).  This retired
    the 4 carriers that needed uniqueness only: `modulus_eq_of_equivRect`,
    `TopQuad.IsRectangle.exists_data`, `rengel_right_eq_of_isRectangle` and
    `subadditive_eq_of_rect`.  The other 25 of the former group of 29 still need existence.
  * Retired on 2026-09-13: `dcModulus_annulus` and `dcModulus_eq_of_equiv`, via
    `annulus_conformallyEquivalent_iff`, which is now proved in S04 from the extremal length of the
    separating curves of an annulus.
  Note that the biggest remaining group sits behind the hardest blockers: the §9 cluster needs
  Menchoff's lemma (invariance of domain), Theorem 9.4 (orientation at points of differentiability,
  i.e. `J ≥ 0`, which needs degree theory) and Theorem 9.6 (the area enclosed by a Jordan curve).
* To re-measure rather than trust the numbers above, run **`Audit.lean`** in the repository root
  (`lake env lean Audit.lean`); it prints the three-way partition for the `LiZhongQC` namespace and
  is not part of the library, so `lake build` ignores it.  It reproduces the 1972-figure above exactly.  The method, for reference:
  iterate `env.constants` for `.thmInfo` with
  the `LiZhongQC` prefix, dropping `n.isInternal` and any name with a `_`-prefixed component, and
  classify with `Lean.collectAxioms`.  A declaration is a *carrier* rather than a `sorry` itself
  exactly when `collectAxioms` yields `sorryAx` but `ConstantInfo.getUsedConstantsAsSet` does not.
  Do **not** use `ConstantInfo.value?` for this: imported theorem bodies are loaded lazily, so it
  returns `none` and every carrier looks unblocked.

## Proof pass

Proofs are added in file order, following the book's own arguments.  A proof may use earlier
theorems that are themselves still `sorry`.  A statement is skipped when its proof needs a
classical theorem that the book does not prove and Mathlib does not provide, or when the book
leaves it to the reader; in that case the reason is recorded in the theorem's docstring as
"Not proved (kept as `sorry`): …".  The recurring blockers are the Riemann mapping theorem
with boundary correspondence (needed whenever a statement asserts that an image or preimage *is* a
quadrilateral), invariance of domain and Jordan-curve topology, Arzelà–Ascoli in normal-family
form, and the Zygmund–Calderón and Riesz–Thorin theorems of §11.

Chapter 1 is complete under that policy: §6 (including Grötzsch's theorem and its equality case)
is proved except Theorem 6.1, and §§7–10 are proved except the statements listed above.

In §9, Theorem 9.1 (`thm9_1_isACL`), Theorem 9.2 (`thm9_2_partials_ae`) and Lemma 9.2 in both
directions are proved.  Lemma 9.2 (⇐) passes to the limit segment by segment: by Fatou's lemma the
`L¹` errors of the approximating derivatives have `liminf = 0` on almost every segment.  Lemma 9.2
(⇒) uses mollifiers.  Mathlib lacks the fact that mollifiers form an approximate identity in `L_p`,
so it is proved here from Jensen's inequality and the density of compactly supported continuous
functions (`tendsto_eLpNorm_convolution_normed_sub`).  Rectangles are quadrilaterals by
`Lemmas/RectangleQuad.lean`.  Still open in §9:
* Menchoff's lemma (invariance of domain);
* Theorem 9.4 (orientation at points of differentiability, i.e. `J ≥ 0`, which needs degree theory);
* `area_image_square_deriv` (its lower bound needs degree theory as well);
* Theorem 9.6 (the area enclosed by a Jordan curve).

Theorem 1.1 is proved in full.  Uniqueness comes from the rigidity of conformal maps between
rectangles (`Lemmas/RectangleRigidity.lean`).  Existence, together with the elliptic-integral formula
for the modulus of `ℍ(-1/k, -1, 1, 1/k)`, comes from the Schwarz–Christoffel map
`F(z) = ∫ dζ/√((1-ζ²)(1-k²ζ²))` in `Lemmas/SchwarzChristoffelRect.lean`.  The book's injectivity
step, which uses the argument principle, is replaced by a covering-map argument: `F` is a proper
local homeomorphism from `ℍ` onto the rectangle, hence a covering map, hence a homeomorphism because
the rectangle is simply connected.  Continuity of `F` at `∞` comes from the inversion `ω ↦ -1/(kω)`,
which permutes the four prevertices.

In Chapter 2, §11 proves Lemmas 11.1 and 11.2 — Hölder's inequality together with the
potential-theoretic estimates `∬_{|ζ| ≤ R} |ζ - z|^{-q} ≤ C(q, R)` and
`∬ dξ dη/(|ζ - z₁|^q |ζ - z₂|^q) ≤ C_q |z₁ - z₂|^{2-2q}` for the conjugate exponent
`q = p/(p-1) < 2` — and the identity `∬_{r < |ζ - z| < R} (ζ - z)^{-2} = 0` of §11.3, which is
obtained from rotation invariance instead of the book's Green formula; §12 proves the choice of
the exponent `p` in §12.1.  Later passes proved:
* the complex Green formulas (11.9) and (11.10) on a disc, via polar coordinates, since Mathlib's
  divergence theorem is available for boxes only (`Lemmas/GreenDisc.lean`,
  `Lemmas/GreenPolar.lean`);
* Pompeiu's formula (11.11), via a cutoff that smooths the Cauchy kernel (`Lemmas/Pompeiu.lean`);
* (11.19);
* (11.8), by differentiation under the integral sign;
* Pompeiu's formula for `L_p` generalized derivatives, as a limit controlled by Hölder's inequality
  against the Cauchy kernel;
* the existence of the principal value (11.15);
* (11.17), `∂_z̄ T(ω) = ω` and `∂_z T(ω) = H(ω)` for `ω ∈ C₀^∞`.  Here `T(ω)` is a convolution
  with a locally integrable kernel, and `∂_z` comes from Green's formula for `∂_z` applied twice
  to one cutoff function.

None of these needs Calderón–Zygmund theory.  The rest of §§11–13 is blocked by the results listed
above and by the covering-space argument of Lemma 12.1.

Two remarks on Lemma 11.2.  The two-singularity estimate is obtained not by the book's scaling and
rotation argument but by splitting the plane according to which singularity is the nearer one,
which needs only translations and the two radial integrals `∬_{|w| < ρ} |w|^{-a}`,
`∬_{|w| > ρ} |w|^{-a}` (proved by polar coordinates).  And since the statement assumes only
`ω ∈ L_p(ℂ)`, the individual integrals `∫ ω(ζ)/(ζ - z)` need not converge; the proof therefore
never subtracts them, but uses that the *difference* kernel is integrable, so that the two
integrands are integrable together or not at all — and when neither is, both sides vanish.

Chapters 3–11 were swept section by section.  Almost everything there rests on the existence and
representation theory of §§12–13, on the elliptic modular function of §§14.2–14.3, or on classical
results the book quotes (uniformization, Riemann–Roch, the theorems of Ahlfors and Gehring), and is
kept as `sorry`.  What is proved: (14.2), the Poincaré length of a segment; (17.13), the bounds
`1/(1+ρ) ≤ h(1/2) ≤ ρ/(1+ρ)` for a normalized `ρ`-quasisymmetric function; that horizontal and
vertical segments are the trajectories of `dz²` (§25.1); and that the identity map of a Riemann
surface is quasiconformal (§27.1).  A further obstacle in the later chapters is that many
statements bundle several claims into one theorem — for instance `teichDistance_metric` conjoins
all five metric axioms, of which only the separation axiom is out of reach — so the provable parts
cannot be discharged without splitting the statement away from the book's own form.

A second pass added three more results.  An ellipse `x²/a² + y²/b² = 1` with `a ≥ b > 0` is an
`a/b`-quasicircle (§16.1): it is the image of the unit circle under the affine map
`z ↦ ((a+b)/2) z + ((a-b)/2) z̄`, whose complex dilatation is the constant `(a-b)/(a+b)`, so that
`K = a/b`.  The order computation of §32.1 for the lift `4ζ²φ(ζ²)` to the branched double cover
gives `2N + 2`, using Mathlib's order-under-composition lemma for a meromorphic function composed
with an analytic one (`MeromorphicAt.meromorphicOrderAt_comp`) together with additivity of the
order under products.  And the equivalence of marked Riemann surfaces (§27.1) is an equivalence
relation; for it, `IsBiholomorphic` is shown in §22 to be closed under the identity, under the
inverse of a homeomorphism and under composition (`isBiholomorphic_id`,
`IsBiholomorphic.homeomorph_symm`, `IsBiholomorphic.comp`).

`hasGenus_of_homeomorph` (§28) is proved as well.  `HasGenus` is defined through
`FundamentalGroup`, and Mathlib provides only basepoint-change isomorphisms
(`fundamentalGroupMulEquivOfPath`), so the proof builds the transport of the fundamental group along
a homeomorphism itself (`fundamentalGroupMulEquivOfHomeomorph`).

Later passes in Chapters 3–11 added, among others:
* §14:
  * all of §14.1: the invariance of the disc metric, the geodesic property (14.3), the density of
    a simply connected domain, and the Poincaré distance and geodesics of the upper half-plane;
  * from §14.3, the lattice identities (14.8) and (14.9) of `℘`, and the modular identities
    (14.4), (14.5) and (14.12);
  * from §14.2, the invariance of the elliptic modular function under `Γ(2)`
    (`modularPhi_gamma2_invariant`).
  * (14.11) stays `sorry`: it needs `e₂ ≠ e₃`, i.e. that `℘` takes each value only twice in a
    period parallelogram, which Mathlib does not provide.
* §19:
  * Theorem 19.1, existence and uniqueness (`eq19_2_ode`, `thm19_1_exists`, `thm19_1_unique`);
  * Theorem 19.2 (`thm19_2_nehari`), which the book only cites.  An omitted value, a disc
    automorphism and an affine normalization reduce it to the Kraus–Nehari coefficient bound of
    `Lemmas/KrausNehari.lean`.
  * Theorem 19.3 (Lehto, `thm19_3`: `σ₂(D) = 3/2 + σ₁(D)`) and its corollary `σ₂(D) ≤ 3`
    (`thm19_3_cor`), via a conformal map onto the disc, the chain rule for the Schwarzian,
    Theorem 19.2 and the Koebe function.  §19 is now free of `sorry`.
* §20: Theorem 20.1 (`thm20_1_disc_isSchwarz`, `thm20_1_not_isSchwarz`, `thm20_1`), by Nehari's
  classical argument with the Hardy inequality instead of the book's route through quasiconformal
  extension.  Theorem 20.4 stays `sorry`: it needs Koebe's ¼-theorem in the form (20.14) and a
  Janiszewski-type planar separation step that the book asserts without proof.
* §22: `thm22_1_monodromy` and `mobius_classification_trace`.
* §25:
  * (25.2), (25.3), (25.5), (25.6), (25.8) and (25.9) (`Lemmas/LocalRoots.lean`);
  * horizontal and vertical trajectory arcs are `φ`-straight (`horizontal_vertical_isPhiStraight`),
    and near a regular point the `φ`-straight segment is the unique shortest connection
    (`local_shortest_regular`).
* §26:
  * the injectivity (26.5) of the new parameter at a zero (`eq26_5_injective`).  For
    `p = (ζ/|ζ|)^{m+2}`, comparing the `(m+2)`-th powers and their moduli gives
    `(1 - k²)(p₁ - p₂) = 0`, so no roots of unity are needed;
  * that this parameter is a homeomorphism of `ℂ` fixing `0` (`teichStretchZero_localHomeomorph`),
    without invariance of domain: it is continuous, proper (`|ζ| ≤ |ζ'|`) and hence closed, and
    surjective by an explicit preimage;
  * that `k φ̄/|φ|` is a Beltrami differential with `‖μ‖_∞ ≤ k`
    (`teichmullerBeltrami_isBeltramiDifferential`).
* §27: the normal form of a hyperbolic element of `SL(2, ℝ)` at its fixed points, and that the
  fixed points and the multiplier determine it up to sign (`hyperbolic_normal_form`).  (27.12)
  (`eq27_12_d_ne_one`) is deferred: the relation (27.4) holds in `SL(2, ℝ)` only up to `±I`, and in
  the `-I` case the book's argument does not exclude `d = 1`.
* §30:
  * (30.7);
  * the translation length as the minimal displacement (`translationLength_eq_inf_dist`).  It
    rests on the identity `|cτ² + (d - a)τ - b|² = (Im τ)² (tr² - 4) + (c|τ|² + (d - a) Re τ - b)²`,
    which avoids diagonalizing the matrix;
  * `cocompact_elements_hyperbolic` and `lengthSpectrum_discrete`;
  * `parabolic_horoball_disjoint`, which is Shimizu's lemma after the correction above.
  * The docstrings had named the normal form of parabolic elements as a blocker.  None of these
    proofs needs it: the displacement formula behind `translationLength_eq_inf_dist` suffices.
* §32: `project_admissibleQD_order`.
* §35:
  * `eq35_1_radii_finite_length` and `circular_arcs_short`;
  * Lemma 35.4 (`lemma35_4`), with no measurability assumption on `κ`.  `Δ` is split along a
    measurable version of `{|F| ≤ |φ| g(k')}`, and a non-measurable integrand has the junk integral
    `0`, for which the estimate is trivial;
  * Lemma 35.6 (`lemma35_6`: `I[κ] = k/(1 - k²)` iff `H[κ] = k`).  A nonzero integral makes `κ`
    measurable, and each supremum is approached along phase-rotated admissible functions, to which
    Lemma 35.4 and the book's comparison estimate apply.
  * Theorems 35.3–35.5 stay `sorry`: they need the main inequality (35.6) or Hamilton's theorem
    (§36).  Their statements are sound, since a quasiconformal `f₀` has `‖κ‖_∞ < 1`, but that bound
    comes from the §9 results that are still `sorry`.
* §36: `pairing_eq_norm_imp_teichmuller`.

## Layout

| File | Book section |
|---|---|
| `LiZhongQC/Basic.lean` | common notions: `ℂ̄ = OnePoint ℂ`, Jordan domains, conformal maps and boundary extensions, standard domains, Möbius maps, formal derivatives `∂_z`, `∂_z̄`, complex dilatation |
| `Ch01/S01_Quadrilateral` | §1 topological quadrilaterals and their modulus (Thms 1.1–1.3) |
| `Ch01/S02_DoublyConnected` | §2 doubly connected domains (Thms 2.1–2.2) |
| `Ch01/S03_ExtremalLength` | §3 extremal length, comparison and composition principles (Thms 3.1–3.3) |
| `Ch01/S04_ModulusExtremalLength` | §4 modulus = extremal length, Rengel, monotonicity, continuity (Thms 4.1–4.11) |
| `Ch01/S05_ExtremalProblems` | §5 Grötzsch, Teichmüller and Mori extremal problems, `μ(r)`, `Λ(ρ)` (Thms 5.1–5.4) |
| `Ch01/S06_C1Quasiconformal` | §6 `C¹` quasiconformal maps, Grötzsch's theorem (Thms 6.1–6.2) |
| `Ch01/S07_GeometricDefinition` | §7 geometric definition (Def 7.1, Thms 7.1–7.4) |
| `Ch01/S08_Compactness` | §8 normal families (Thms 8.1–8.2) |
| `Ch01/S09_AnalyticProperties` | §9 A.C.L., differentiability, generalized derivatives, absolute continuity (Thms 9.1–9.6) |
| `Ch01/S10_AnalyticDefinition` | §10 analytic definition, Beltrami equation (Thms 10.1–10.2) |
| `Ch02/S11_IntegralOperators` | §11 the operators `T` and `H`, Pompeiu, Zygmund–Calderón, Riesz–Thorin (Thms 11.1–11.3) |
| `Ch02/S12_Existence` | §12 existence theorem (Lemma 12.1, Thms 12.1–12.2) |
| `Ch02/S13_Representation` | §13 representation, similarity principle, measurable Riemann mapping theorem, Ahlfors–Bers (Thms 13.1–13.8) |
| `Ch03/S14_PoincareMetric` | §14 Poincaré metric, elliptic modular function, (14.1)–(14.27) |
| `Ch03/S15_Distortion` | §15 distortion theorems, Mori, Teichmüller (Thms 15.1–15.4) |
| `Ch04/S16_Quasicircles` | §16 quasicircles, reflections, welding (Thms 16.1–16.3) |
| `Ch04/S17_BoundaryValues` | §17 quasisymmetry, Beurling–Ahlfors extension (Thms 17.1–17.2) |
| `Ch04/S18_BoundedTurning` | §18 bounded turning (Thm 18.1) |
| `Ch05/S19_Schwarzian` | §19 Schwarzian derivative, Nehari (Thms 19.1–19.3) |
| `Ch05/S20_SchwarzDomains` | §20 Schwarz domains, Ahlfors, Gehring (Thms 20.1–20.5) |
| `Ch05/S21_UniversalTeichmuller` | §21 universal Teichmüller space, Bers embedding (Thms 21.1–21.4) |
| `Ch06/S22_RiemannSurfaces` | §22 Riemann surfaces, uniformization, differentials, Riemann–Roch (Thms 22.1–22.5) |
| `Ch06/S23_QCOnSurfaces` | §23 quasiconformal maps of Riemann surfaces, lifting (Thm 23.1) |
| `Ch06/S24_QuasiFuchsian` | §24 quasi-Fuchsian groups, simultaneous uniformization (Thm 24.1) |
| `Ch07/S25_QuadraticDifferentials` | §25 quadratic differentials, trajectories, `φ`-metric (Thms 25.1–25.4), §25.3 the space `Q(S)` |
| `Ch07/S26_TeichmullerUniqueness` | §26 extremal problem (Thm 26.1), Teichmüller deformations `S_{ω,k}` (26.4)–(26.6), Teichmüller maps, Lemmas 26.1–26.2, uniqueness theorem (Thm 26.2, (26.7)–(26.16)) |
| `Ch07/S27_TeichmullerExistence` | §27 marked surfaces, normalized lifts (Thm 27.1), standard generators (27.4)–(27.5), Fricke space and coordinates (27.6)–(27.14), Lemmas 27.1–27.3, existence theorem (Thm 27.2) |
| `Ch08/S28_Moduli` | §28 moduli of tori, `R_g`, the modular group, (28.1) `R_g = T(S₀)/Mod(S₀)` |
| `Ch08/S29_TeichmullerMetric` | §29 Teichmüller metric `½ ln K`, (29.1)–(29.8), Thm 29.1 (ball topology), Thm 29.2 (completeness), isometry of modular transformations |
| `Ch08/S30_ModularGroupDiscontinuity` | §30 length spectrum, Lemmas 30.1–30.3 (Wolpert), Thms 30.1–30.4, Hurwitz |
| `Ch09/S31_FiniteType` | §31 surfaces of type `(g,n,m)`, Schottky double, admissible quadratic differentials, (31.1), Thm 31.1 |
| `Ch09/S32_FiniteTypeTeichmuller` | §32 Teichmüller's theorems for finite type (Thms 32.1–32.4, (32.1)–(32.3)), `T_{g,n,m}` |
| `Ch10/S33_BersEmbedding` | §33 models of `T_g` (33.1)–(33.12), Lemmas 33.1–33.4 (Earle), Bers embedding theorem (Thm 33.1) |
| `Ch10/S34_BersFiberSpace` | §34 holomorphic families, Bers fiber space `F(G₀)`, `V(G₀)`, Bers' theorem (Thm 34.1) |
| `Ch11/S35_DiscTeichmullerMaps` | §35 trajectories of finite-norm differentials (Lemmas 35.1–35.3), Reich–Strebel main inequality (35.3)–(35.5), Thms 35.1–35.8, Lemmas 35.4–35.6, Hamilton sequences, Strebel's frame criterion |
| `Ch11/S36_Hamilton` | §36 homotopy modulo the boundary (Thm 36.1), Hamilton's theorem (Thm 36.2), Corollary 36.1, Lemmas 36.1–36.3 |
| `Lemmas/UniformizedTeichmuller` | not a book section: companions `<name>_of_uniformization` of the §23/§26 uniqueness statements (`thm23_1_cor`, `conformal_unique_extremal`, Lemmas 26.1–26.2, Thm 26.2, (26.15)–(26.16), `teichmullerMap_isExtremal`) and of the §27 existence statements (Lemma 27.1, Lemma 27.3's bound, the bijection `Φ`, Thm 27.2 for quasiconformal classes), proved for surfaces given as `ℍ/Γ` (see Modelling conventions) |

Theorem names carry the book's numbering, e.g. `thm4_1_modulus_eq_inv_extremalLength`,
`eq5_19`, `lemma20_3`, `thm26_2_uniqueness`, `eq27_9_14_last_determined`.

## Sources and caveats

* All chapters (§1–§36) were formalized from the text of the book; the historical notes at the
  end of Chapter 9 contain no mathematical statements and are not represented.
* **Corrections.**
  * Theorem 13.8: the book asserts holomorphic dependence on parameters for the normalized
    self-maps of the disc.  That fails in general, because the disc solution also involves the
    reflected, conjugated coefficient.  It is stated instead for the normalized solutions of the
    whole plane.
  * (4.22): the book writes `M(B) = 2π∬ρ₀² ≤ …`; the first `=` is `≤`.
  * Theorem 16.1 needs `z₂` to lie between `z₁` and `z₃` on the curve, as in the book's proof.
  * §32.1 (`lift_admissibleQD_order`): the hypothesis `MeromorphicAt φ 0` is added.  It is implicit
    in the book, where `φ` is the coefficient of a meromorphic quadratic differential, and without
    it the statement is false: Mathlib gives `meromorphicOrderAt` the junk value `0` at a point
    where the function is not meromorphic, so a non-meromorphic `φ` satisfies the hypothesis with
    `N = 0` while the conclusion asks for the order `2`.
  * Theorem 1.1: the book gives the side of the rectangle as
    `a = ∫_{-1/k}^{-1} dx/√((1-x²)(1-k²x²))`.  On `(-1/k, -1)` one has `1-x² < 0` while
    `1-k²x² > 0`, so that integrand is imaginary.  The real form, used here, is
    `a = ∫_{1}^{1/k} dx/√((x²-1)(1-k²x²))` (substitute `x ↦ -x` and take the positive root).
    The second side `b = ∫_{-1}^{1} dx/√((1-x²)(1-k²x²))` is unaffected.
  * §6.3, the example `w = z/(1-|z|²)`: the book prints `∂_z̄ f = |z|²/(1-|z|²)²` and hence
    `μ_f(z) = |z|²`.  The correct values are `∂_z̄ f = z²/(1-|z|²)²` and `μ_f(z) = z²`; the book
    has substituted the modulus for the value.  Only `|μ_f|` enters the dilatation quotient, so
    the conclusion `D_f = (1+|z|²)/(1-|z|²)` — and with it the point of the example — stands.
    (`discMap_dz_dzbar`, `discMap_dilatationQuotient` prove the corrected values.)
  * (35.7): the book prints `I[κ] ≤ k₀/(1-k₀) + Δ[κ]`, but its own derivation ends at
    `k₀/(1+k₀)`, and (35.9) — and Theorem 35.3, which needs `k/(1+k) ≤ k₀/(1+k₀)` to conclude
    `k ≤ k₀` — uses `k₀/(1+k₀)`.  The printed `k₀/(1-k₀)` is a true but weaker inequality that
    does not yield (35.9), so `eq35_7` states the sharper `k₀/(1+k₀)`.

  * Theorem 4.8 (`thm4_8_modulus_continuous`): the book's definition of "`Qₙ` tends to `Q` from
    the inside" — `Qₙ ⊆ Q`, the vertices converge, and `∂Qₙ` lies within `ε` of `∂Q` — is too
    weak, and with it the theorem is **false**.  Let `Q` be the unit square with its corners as
    vertices and let `Qₙ` be the collar `{z ∈ Q : d(z, ∂Q) < 1/n}` cut along the segment from
    `1/2` to `1/2 + i/n`, again with the corners as vertices; every hypothesis holds.  But the
    first side of `Qₙ` is then the long arc running through the cut and round the inner
    boundary, so it comes within `1/n` of the third side, while the cut forces the second and
    fourth sides a distance close to `1` apart; Rengel's inequality gives
    `M(Qₙ) ≥ (1 - 2/n)²/(4/n - 4/n²) → ∞`, not `M(Q) = 1`.  `TendsFromInside` therefore also
    asks that each side of `Qₙ` converge to the corresponding side of `Q`, which is what the
    book's Figure 1.4.3 shows and what its proof uses when it reads `d₁ ≥ b - 2η` off the
    `η`-frame.
  * §19.1 (`schwarzian`): the Schwarzian of a meromorphic function is branched on the *order* of
    the germ, `if 0 ≤ meromorphicOrderAt f z`, and both branches are computed from the normal
    form `toMeromorphicNFAt f z`.  Branching on `AnalyticAt ℂ f z` — the direct reading of the
    book — is not faithful, because a Lean function may have a removable singularity at `z` and
    still fail `AnalyticAt` through a wrong value `f z` alone.  Such a germ was sent to the pole
    branch, where the reciprocal of the normal form is singular and `deriv` returns its junk
    value `0`.  With `u w = w + w³` and `f = Function.update u 0 1` this gives `S_f(0) = 0` in
    place of `6`, and it makes `schwarzian_mobius_comp` false: for `f` with a pole at `z` and
    `a = 0`, `M ∘ f` has a simple zero there, so the old definition compared `S_f` against the
    junk value.  Branching on the order also makes the Schwarzian depend only on the germ of `f`
    on a punctured neighbourhood (`schwarzian_congr`), which is what the Möbius-invariance and
    chain-rule proofs use; on germs already in normal form — in particular on every function
    analytic at `z` — the two definitions agree.

  * `meroToExt` (§20.3): this branched on `AnalyticAt ℂ f z` to decide whether `f` has a pole at
    `z`.  That is the wrong test — a Lean function can fail `AnalyticAt` at `z` purely because its
    value there is wrong (a removable singularity), and such a germ was then sent to `∞`.  With
    `f = Function.update (fun w => w) 0 1` the old definition gave `meroToExt f 0 = ∞` although `f`
    has no pole at `0`, which silently weakened `HasQCExtensionExt` and hence Theorems 20.2, 20.3
    and (20.20).  It now branches on the sign of `meromorphicOrderAt f z` and reads the value off
    `toMeromorphicNFAt`, so it depends only on the germ; it agrees with the old definition on every
    germ already in normal form.

  * §14.1 (`poincareDensity_well_defined`): the hypothesis `IsOpen D` is added.  The book's `D` is
    a *domain*, so this is implicit there, but the Lean statement needs it: without openness the
    unrestricted `deriv f z` bears no relation to `f` on `D`, and `IsConformalOnto.symm` — which
    supplies the conformal inverse the proof runs through — requires an open domain.  No other
    file used the lemma, so nothing downstream changed.

  * §31.1 (`not_exceptional_iff`, now removed): the Lean file asserted
    `¬ IsExceptionalType g n m ↔ 0 < 6g - 6 + 2n + 3m`, which is **false**.  `(0,3,0)` — the
    thrice-punctured sphere — is not among the book's seven exceptional types, yet
    `6·0 - 6 + 2·3 + 3·0 = 0`, so the left side holds and the right side fails; it is the unique
    counterexample.  Weakening to `0 ≤ …` does not repair it, because the value-`0` fibre is
    mixed: `(1,0,0)` and `(0,0,2)` are exceptional and also give `0`.  **No inequality in
    `6g - 6 + 2n + 3m` characterises the exceptional list.**  The book states the exceptional
    types only as the explicit list `(0,0,0), (0,1,0), (1,0,0), (0,2,0); (0,0,1), (0,1,1),
    (0,0,2)` — which `IsExceptionalType` matches faithfully — justified by the surface or its
    Schottky double lacking a hyperbolic universal covering, and it uses `6g - 6 + 2n + 3m` only
    in (31.2), as `dim_ℝ Q̃(S₀)`; the equivalence is not the book's claim.  The underlying
    conflation is between *hyperbolic* and *positive-dimensional Teichmüller space*: the
    thrice-punctured sphere is hyperbolic — the standard example — but rigid, so its Teichmüller
    space is a point.  The two true implications, `not_exceptional_of_pos` and
    `dim_nonneg_of_not_exceptional`, replace it and are proved.  Nothing used the old statement.

  * §35.2 (`main_inequality_pointwise`): the factor `w = φ/|φ|` was missing from the `κ₁τ` term,
    and the statement was **false**.  At `κ = κ₁ = 3/4`, `τ = i`, `w = -i` — where all four
    hypotheses `‖κ‖, ‖κ₁‖ < 1`, `‖τ‖ = ‖w‖ = 1` hold — the right-hand side is exactly `1`
    (the two factors are `25/7` and `7/25`) while the left-hand side is `≈ 16.18`, because
    `|μ_g| ≈ 0.9243`.  Both halves of that were checked in Lean, not merely numerically.
    The book (§35.2, the display before 因此) writes the second factor as
    `|1 + κ₁τ(φ/|φ|)(1 + κ̄φ̄/|φ|)/(1 + κφ/|φ|)|²`, i.e. **with** `φ/|φ|` present; omitting it
    shifts one argument, since `LHS(κ,κ₁,τ,w) = RHS(κ,κ₁,τw,w)` identically.  The reason the
    omission is not harmless is that the two unimodular parameters are not independent in the
    Reich–Strebel argument: `τ = ∂_z̄f₀/∂_zf₀` and `w = φ/|φ|` are evaluated at the same point, so
    quantifying over them separately is what breaks the inequality.  With the factor restored the
    relation is in fact an **identity** — both sides equal
    `|(1 + κw) + κ₁τw(1 + κ̄w̄)|²/((1-|κ|²)(1-|κ₁|²))`, by the composition identity
    `1 - |μ_g|² = (1-|κ|²)(1-|κ₁|²)/|1 + κ̄κ₁τ|²` on the left and cancelling `|1 + κw|²` on the
    right — which is recorded as `main_inequality_pointwise_eq` and is what makes the book's
    inequality provable.  The book states only `≤`, obtained by bounding the exact denominator
    below, so `main_inequality_pointwise` keeps that form.

  * §36.3 (`lemma36_1_hilbert`): the norm equality was taken as a hypothesis quantified over
    **all** closed `A` annihilated by `T`, and in that form the statement was **vacuous**.
    `A = ⊥` is closed, its side condition `∀ y ∈ T, ∀ a ∈ ⊥, ⟪y, a⟫ = 0` holds trivially for
    every `T` since `a = 0`, and the restricted functional lives on the zero space and so has
    norm `0`; instantiating the hypothesis there reads `0 = ‖x‖` and forces `x = 0`.  The
    statement was thus true but said only "if `x = 0` then `x ⊥ T`", and a three-line proof of it
    would have retired a `sorry` while encoding none of the content.  (Checked in Lean: the
    hypothesis as written provably implies `x = 0`.)  The book quantifies `A` nowhere — it is the
    subspace fixed by Lemma 36.1, whose own statement takes `A` as a parameter and concludes about
    that same `A` — and its Hilbert remark is just "由 `‖x|_A‖ = ‖x‖` 推出 `x ∈ A`".  So `A` is now
    a parameter carrying the annihilation hypothesis, and the book's step is recorded separately as
    `mem_of_norm_comp_subtypeL_eq` (proved by Riesz on `A`, which is complete because closed,
    then Pythagoras).  Both are proved.

  * §35.2 (`eq35_8`): the statement took a bare `(κ : ℂ → ℂ)` with no bound on `‖κ‖_∞`, and was
    **false**.  The bound needs `t ↦ t²/(1-t²)` monotone, which holds on `[0,1)` but not across
    `1` — it runs to `+∞` as `t → 1⁻` and reappears at `-∞` beyond.  With `κ = 0` on part of `Δ`
    and `κ = 2` on a set `S` of positive measure, `k = 2` and the right-hand side is
    `4/(1-4) = -4/3 < 0`, while the integrand vanishes off `S`, so a `φ` with little mass on `S`
    makes the integral nearly `0`, above `-4/3`.  The `k = 1` case fails separately: `1 - k² = 0`
    makes the right-hand side the junk value `0` against a supremum of non-negative integrals.
    In the book (35.8) appears *inside the proof of Theorem 35.3*, where `κ` is the complex
    dilatation of a quasiconformal `f₀ : Δ → Δ`, so `‖κ‖_∞ < 1` is ambient and never stated; the
    siblings `lemma35_4`/`lemma35_5`/`lemma35_6` do state it.  This is the same kind of gap as
    `IsOpen D` in `poincareDensity_well_defined` and `MeromorphicAt φ 0` in
    `lift_admissibleQD_order`: an ambient hypothesis the book's prose carries.
    **The hypothesis had to be the essential supremum in `ℝ≥0∞`, not `beltramiNormDisc κ < 1`.**
    `beltramiNormDisc` is a `.toReal` and `(⊤ : ℝ≥0∞).toReal = 0`, so `beltramiNormDisc κ < 1` is
    satisfied by an *unbounded* `κ` with value `0`; such a `κ` equal to `1/2` on a set of positive
    measure still gives a positive left-hand side against a right-hand side of `0`, so that
    weaker form would not have repaired the statement.  (Four further statements carried the weaker
    form — `lemma35_4`, `lemma35_5`, `lemma35_6`, `eq35_14` — and are now restated in the `ℝ≥0∞`
    form too.  They are still `sorry`, so nothing false was proved, but `lemma35_5`, `lemma35_6`
    and `eq35_14` would have been genuinely suspect — with `‖κ‖_∞ = ⊤` the junk value makes them
    assert something about an unbounded `κ` — while `lemma35_4` was merely vacuous, its two bounds
    on the auxiliary constant contradicting each other.)  With `essSup … < 1` the theorem is
    proved: `‖κ z‖ ≤ k` a.e., monotonicity of `t²/(1-t²)` on `[0,k]`, and `∫_Δ ‖φ‖ = 1` from the
    area normalisation via
    `ofReal_integral_eq_lintegral_ofReal`.

The junk-value hypothesis defect behind the `eq35_8` entry was then **swept project-wide**, not
only fixed where it was found: every definition whose value is a `.toReal` of an `ℝ≥0∞`
(`grotzschMu`, `dilatationDiffNorm`, `dilatationNorm`, `beltramiNormDisc`, `beltramiNormH`,
`beltramiPoincareDist`) was checked in hypothesis position.  The pattern occurred exactly five
times, all in §35 (`eq35_8`, `lemma35_4`, `lemma35_5`, `lemma35_6`, `eq35_14`), and all five are
now stated on the essential supremum in `ℝ≥0∞`.  Everywhere else these definitions appear only in
conclusions, where the denominators are safe: `1 + k ≥ 1` for `dilatationNorm`, and for
`dilatationDiffNorm` the two subtype bounds give `‖(μ-ν)/(1-ν̄μ)‖_∞ ≤ (k₁+k₂)/(1+k₁k₂) < 1`, so no
`x/0 = 0` can arise.  The general shape of the defect: **a hypothesis phrased on the *defined*
answer of a total function silently readmits the degenerate case it was meant to exclude**
(`(⊤ : ℝ≥0∞).toReal = 0`, `sSup ∅ = 0`, `x/0 = 0`, `meromorphicOrderAt` off its set).


  * §19.1 (`IsLocUnivMero`): the pole test `¬ AnalyticAt ℂ f z` is replaced by
    `meromorphicOrderAt f z < 0`.  With the former, a removable singularity carrying a wrong value
    counted as a pole: the identity with two such values was `IsLocUnivMero` on `Δ` with
    `‖S_f‖_Δ = 0`, yet not `IsUnivMero` (its pole set must be a subsingleton).  Hence
    `IsSchwarzDomain unitDisc a` was false for every `a > 0`, `innerUnivalenceRadius unitDisc` was
    the junk `sSup ∅ = 0`, and Theorem 20.1 was false as stated.  Same family as the `schwarzian`
    and `meroToExt` corrections; found by the 2026-09-13 definition-soundness audit.
  * §25.4 (`phiLengthOn`): the length of a path on a Riemann surface is now the *infimum* over chart
    partitions whose chart expressions are *Lipschitz* on each piece, rather than the supremum over
    all chart partitions.  A `Path a b` is only continuous, so a singular reparametrisation (a
    Cantor-function change of variable) has `deriv = 0` almost everywhere and every piece integrated
    to `0`: every path had length `0` and `phiDistRS ≡ 0`, making Theorem 25.4 and its corollary
    vacuous.  Non-rectifiable paths now have length `⊤`, as they should; for rectifiable paths all
    admissible partitions agree, so the infimum is the length.
  * §30.1 (`poincareLengthLoop`): the same defect — the lift `c` was only `ContinuousOn`, so
    `hypLength c = 0` for a singular reparametrisation and `freeHomotopyLength ≡ 0`, making
    Lemma 30.2 and the length-spectrum results false or vacuous.  Repaired by requiring the lift to
    be Lipschitz on `[0,1]`.
  * §30.2 (`parabolic_horoball_disjoint`, the proof of Lemma 30.1): the hypothesis that `γ₁`
    generates the stabilizer of `∞` (up to sign) is added.  Without it the statement fails for
    `Γ = ⟨z ↦ z + 1/2⟩`.
  * §35.4 (`lemma35_5`): the book's Lemma 35.5 is false as printed (`κ = ½·1_{Re z > 0}`,
    `φₙ ≡ 1/π`).  Its hypothesis is replaced by (35.10), and measurability of `κ` is added.
  * §22.4 (`IsKleinGroup`), recorded, not a defect: the book's literal definition (a "真间断群" is
    one with `Λ(Γ) ≠ ℂ̄`; a Klein group is such a group with more than two limit points) would admit
    non-discrete groups.  The Lean definition additionally requires proper discontinuity on
    `ℂ̄ ∖ Λ(Γ)`, which is the standard meaning and what the book's arguments use.
  * §36.3 (`discPoincareDist`), recorded, not a defect: the book defines `d(z,w) = ½ ln((1+r)/(1−r))`
    here, while §14 uses the density `2/(1−|z|²)`, whose distance is `ln((1+r)/(1−r))` — the book
    uses both normalisations, differing by a factor `2`, and even states `ρ_Δ = 2/(1−|z|²)` within
    §36.  Each Lean definition follows its own section; the `½` is load-bearing in
    `½ ln D_{f∘g⁻¹} = d(ν, π)`.
  * §13 (2026-09-24, user decisions): `qc_reflection_extension` was **false** as stated — a
    quasiconformal self-map of `ℍ` may move `∞` (e.g. `z ↦ -1/z`), and then no plane homeomorphism
    agrees with it on `ℍ`; the hypothesis `f z → ∞` as `z → ∞` in `ℍ` is added.
    `qc_extension_across_arc` was **false** for arbitrary Jordan arcs (there are non-removable
    curves for quasiconformal maps); `γ` is now an open line segment, with the book's injectivity of
    `fⱼ` on `Dⱼ ∪ γ`.  `thm12_2_unique` moved unchanged from S12 to the end of S13, where its tools
    live.
  * §21.1 (`UniversalTeichmuller.dist`) and (21.4) (`eq21_4`), and §33.4 (`teichDeltaGamma`)
    (2026-09-25): the infimum over the classes was written `⨅ μ ν (_ : [μ] = p ∧ [ν] = q), …`.  In
    `ℝ` this is **identically `0`**: for a pair outside the classes the innermost infimum ranges over
    an empty proposition and is `sInf ∅ = 0`, and all values are `≥ 0`.  So the Teichmüller distance
    was `0`, `eq_of_dist_eq_zero`, (21.1), the Lipschitz half of Theorem 21.2,
    `teichDistanceGamma_eq` and Lemma 33.2 were false, and the rest of §21.1 was trivial.  All three
    are now `sInf {d | ∃ μ ν, [μ] = p ∧ [ν] = q ∧ d = …}` over a nonempty set bounded below by `0`.
  * §21.4 (`thm21_4_gehring`, 2026-09-25): "interior of `𝓕*`" was stated without `φ ∈ A(𝕃)`, and
    was **false**: an infinite-norm `φ` (e.g. `(Im z)⁻³` on `𝕃`) is vacuously interior, since
    `‖ψ - φ‖ = ∞` for every `ψ ∈ A(𝕃)`, and so is a non-holomorphic `φ` near `0`.  The left side now
    also requires `φ ∈ bersSpaceL`.
  * §20.3 (`thm20_2`, Ahlfors–Weill), **known false, left unchanged by decision (2026-09-25)**.
    - The statement bounds the dilatation by `(1 + ½‖S_f‖_Δ)/(1 - ½‖S_f‖_Δ)`, copying the display in the book's §20.3.
    - The book's own derivation (20.7) gives `|μ_n| ≤ 2‖S_f‖_Δ`, i.e. `K = (1 + 2‖S_f‖)/(1 - 2‖S_f‖)`, which also
      matches the hypothesis `‖S_f‖ < 1/2`.
    - Kühnau's theorem (`|S_f|(1-|z|²)² ≤ 6k` for univalent `f` with a `k`-q.c. extension) shows that any extension needs
      `|μ| ≥ (2/3)‖S_f‖_Δ` in this norm (`η_Δ = 2/(1-|z|²)`). That exceeds `½‖S_f‖_Δ` whenever `S_f ≠ 0`, e.g. for
      `f = exp(εz)`.
    - So the statement as written is false. It is kept as a `sorry`, and no proof track targets it.
  * §23.1 (`eq23_1_beltrami_differential`, `eq23_4`, 2026-09-25, user decision): (23.1) defined the Beltrami
    family as the dilatation of the preferred-chart expression `localMapExpr f x`, cut off where `f` leaves the
    chart at `f(x)`, and was **false**, even for holomorphic atlases.
    - Counterexample: take `ℂ` with the unit discs around each point as charts (all transitions are identities),
      `f(z) = z + z̄/2` (`μ = ½`), and the charts at `0` and `1`.
    - For `p` near `0.1` in both discs, `f(p)` lies in the chart at `f(0) = 0` but not in the one at `f(1) = 3/2`.
    - There `μ₁ = 0` but `μ₀ = ½` on a set of positive measure, so the `(-1, 1)` law fails.
    - Fix: the dilatation at `z = φ_x(p)` is computed with the chart at the image point `f(p)` (chart-independent for
      holomorphic atlases), and `[IsManifold 𝓘(ℂ) ω S₀] [IsManifold 𝓘(ℂ) ω S₁]` are assumed.
    - (23.4) also gained the holomorphic-atlas instances (`S₀, S₁, S₂`): the local expressions of `f ∘ g` pass
      through non-preferred charts, and without holomorphic transitions quasiconformality is not preserved.
  * §34.2 (`bersFiber_holomorphic_dependence`, 2026-09-25, user decision): the second conjunct claimed that
    `t ↦ γ_{φ_t}(z)` is holomorphic on all of `P` for **every** `z`, and was **false**.
    - `γ_{φ_t} = f_t ∘ γ ∘ f_t⁻¹` is a Möbius map whose pole `f_t(-d/c)` moves holomorphically, and non-constantly, with `t`.
    - So for an open set of `z`, some `t₀ ∈ P` puts `z` on the pole. There Lean's junk value `0` sits next to values
      tending to `∞`, and the map is not differentiable.
    - The book means points of the fibre. The conjunct is now taken over `{t ∈ P | z ∈ D_{φ_t}}`, where `γ_{φ_t}(z)`
      is finite.
  * §29.1 (`teichDistance`) and §32.3 (`teichDistanceFT`) (2026-09-25, user decision): the same defect as §21.1's `dist`.
    - Both were written `⨅ m₁ m₂ g (_ : [m₁] = p ∧ [m₂] = q ∧ …), ½ ln K[g]`, which is **identically `0`** in `ℝ`.
    - Consequently `teichDistance_metric` ("`= 0 → p = q`") and `teichDistanceFT_complete_metric` were false, and S30's
      convergence hypotheses were automatic.
    - After the §33.4 fix, `teichDistanceGamma_eq` equated a genuine distance with `0`, and was false too.
    - Both definitions are now `sInf {d | ∃ m₁ m₂ g, … ∧ d = ½ ln K[g]}`.
    - Found by a multi-line re-scan for the nested-`⨅` pattern; the other nested infima in the tree take values in
      `ℝ≥0∞`, where an empty infimum is `⊤` and harmless.
  * §28.1 (`torus_map_lift`, 2026-09-25, user decision): the statement was **false** on bare `ChartedSpace ℂ X`, `X'`.
    - Mathlib's `MDifferentiableAt f x` only asks that `chartAt (f x) ∘ f ∘ (chartAt x)⁻¹` be differentiable at the
      single point `chartAt x x`. Without `IsManifold`, the preferred charts need not be compatible.
    - Counterexample: tori `ℂ/(ℤ + iℤ)` and `ℂ/(ℤ + 2iℤ)` with charts `p(v) ↦ ρ(v - w₀)` resp.
      `p'(v') ↦ ρ(φ⁻¹(v') - φ⁻¹(w₀'))`, where `ρ(u) = u|u|` and `φ(x + iy) = x + 2iy`.
      - Both projections are "holomorphic" (derivative `0` at the centres).
      - The map induced by `φ` is "biholomorphic": its chart expressions are the identity.
      - Its lifts are `φ` plus a lattice translation, not complex-affine; these two tori are not even conformally
        equivalent.
    - Fix: `[IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω X']` added, as `torus_conformal_iff` already has.
  * §20.4 (`lemma20_3`, 2026-09-25, user decision): the clause `IsPlanarQCReflection (closure D)ᶜ D g K₁` was **false**.
    - It asks for a homeomorphism of the exterior of a bounded Jordan domain onto `D`. The exterior is doubly connected
      in `ℂ` and `D` is simply connected, so no such map exists.
    - The worker refuted the literal statement in Lean (`D = Δ`, `K = 1`; standard axioms), and the leader re-compiled it.
    - In the book the reflection lives on `A₁ ∪ {∞}` with `g(∞) = p ∈ D`. The clause is now
      `∃ p ∈ D, IsPlanarQCReflection (closure D)ᶜ (D \ {p}) g K₁`; the `C¹` condition and (20.18) are unchanged.
  * §33.4 (`lemma33_4_earle`, `translatedBeltrami`, `eq33_12_translation`, 2026-09-25, user decision): two statements
    were **false**.
    - Earle's lemma inverted `f^μ` with `Function.invFunOn (fMuSym μ) upperHalf x` at a **real** `x`. Since `f^μ` maps
      `ℍ` onto `ℍ` (`fMuSym_upperHalf`), a real point has no preimage in `ℍ`, and `invFunOn` returns one fixed
      arbitrary value for every `x`.
      - The right side then equates a constant with a non-constant real Möbius map, and is false already for `γ = 1`.
      - With `μ = 0` the left side (`φ₀ = 0 ∈ Q(G₀, 𝕃)`) is true, so the statement read `True ↔ False`.
      - Fix: the inverse is taken on the real line, `invFunOn (fMuSym μ) {z | z.im = 0}`, the book's `(f^μ)⁻¹|ℝ`.
    - The translation `χ` of the proof of Theorem 33.1 had two independent defects.
      - `translatedBeltrami μ₀ μ` was the dilatation of `f^μ ∘ (f^{μ₀})⁻¹` on all of `ℂ`, which is symmetric and so
        nonzero on `𝕃`. `bersFunction` fed it whole to `normalizedSolution`, whose result is then not holomorphic on
        `𝕃`, and `schwarzian` of a non-meromorphic germ is the junk value `0`.
      - Consequently `χ(Ψ(T)) = Ψ(T)` failed. With `μ₀ = 0`, hitting a nonzero `φ_ν` would force `f^μ` holomorphic on
        `𝕃`, so `μ = 0` and `S = 0`.
      - Fix: `translatedBeltrami` is the `ℍ`-restriction (`upperHalf.indicator …`), as its docstring's "`λ ∈ M(G^{μ₀})`"
        already said.
      - The hypothesis on `Γμ₀` only said that every `γ ∈ G₀` has a conjugate **in** `Γμ₀`. Counterexample: `G₀`
        trivial, `μ₀ = 0`, `Γμ₀ = SL(2, ℝ)`.
        - `Q(SL(2, ℝ), 𝕃) = {0}`, by translation and dilation invariance.
        - The `Q`-membership clause then said `φ_μ ∈ Q(G₀, 𝕃) ⇔ φ_μ = 0`, which Lemma 33.3 refutes.
      - Fix: the hypothesis is two-way, so `Γμ₀ = f^{μ₀} G₀ (f^{μ₀})⁻¹` exactly.
  * §36.3 (`lemma36_2_right_inverse`, `bersDerivative_eq_cauchyT_third`, 2026-09-25, user decision): two statements
    were **false** because of divergent Bochner integrals, whose Lean value is `0`.
    - `lemma36_2_right_inverse` quantified over all of `automorphicQD Γ`, which has no norm bound.
      - With `Γ = {1}` and `φ = 1_𝕃 e^{iz}`, the integrand of `P(c y² φ(z̄))` grows like `y² e^{y}` on `ℍ`.
      - So `P(Fφ) = 0 ≠ φ` for every `c`.
      - Fix: the hypothesis `bersNormL φ < ⊤` is added. That is the book's Banach space `Q(G, 𝕃)`, and it holds
        automatically for compact surfaces. Then the statement is Bers' reproducing formula.
    - `bersDerivative_eq_cauchyT_third` used `cauchyTOn upperHalf μ`, i.e. `T(μ) = -(1/π)∬_ℍ μ(ζ)/(ζ - z)`. For
      bounded `μ` this integral diverges, so `T‴ = 0`.
      - Counterexample: `μ = k·1_ℍ + k·1_{B(i,1/2)}`, where `P(μ) = -(6/π)·k·(π/4)·(i - z)⁻⁴ ≠ 0`.
      - Fix: the new def `normalizedCauchyTOn`, the normalized transform
        `V(μ)(z) = -(z(z - 1)/π)∬ μ(ζ)/(ζ(ζ - 1)(ζ - z))`. It is the first variation of the maps fixing `0, 1, ∞`,
        converges for bounded `μ`, and differs from `T(μ)` by a term linear in `z`.
      - The statement is now `P(μ) = V(μ)‴` on `𝕃`.
  * §35.2 (`thm35_2_main_inequality`, 2026-09-25, user decision): the two-factor Reich–Strebel main inequality was
    **false**.
    - The `κ₁` term lacked the factor `φ/|φ|`, the same omission already corrected in the pointwise helper
      `main_inequality_pointwise`.
    - Counterexample:
      - For `f₀ = id` the integrand becomes `|φ| |1 + κ₁|²/(1 - |κ₁|²)`, with `κ₁ = μ_{f⁻¹}`.
      - For `f⁻¹ = z + εV` its integral is `∬|φ| - 2ε Re ∬ ∂_z̄|φ| · V + O(ε²)`.
      - This is `< ∬|φ|` for suitable `V` whenever `|φ|` is not constant, e.g. `φ = 1 + z/2`.
    - Fix: in the file's `1 - κφ/|φ|` convention the factor is now
      `|1 - κ₁τ(φ/|φ|)(1 - κ̄φ̄/|φ|)/(1 - κφ/|φ|)|²/(1 - |κ₁|²)`.
      - With the first factor, this is exactly `|1 - μ_g φ/|φ||²/(1 - |μ_g|²)` for `g = f⁻¹ ∘ f₀`.
      - `main_inequality_simplified` and `eq35_6` were already true and are unchanged.
  * §36.3 (`lemma36_1`, 2026-09-25, user decision): Lemma 36.1 assumed only that the tangent space `T` annihilates
    `A` (`T ⊆ A^⊥`), and was **false**.
    - Counterexample: `M = {x}` with `x ≠ 0`, `T = ⊥`, `A = ⊥`. Every hypothesis holds, but `‖x|_⊥‖ = 0`.
    - The book needs `T = A^⊥`; Hamilton's theorem applies the lemma with `T₀N = A(S)^⊥`.
    - Fix: the hypothesis `hann : A^⊥ ⊆ T` is added.
    - Proof idea for the corrected statement: Hahn–Banach gives `y ∈ A^⊥` with `‖x − y‖ = ‖x|_A‖`. Then a path in
      `M` with velocity `∓y` changes the norm to first order, by convexity.
  * Carathéodory's Theorem C2 (`caratheodory_jordan`, 2026-09-25, user decision): the statement is unchanged but was
    **moved** from `Lemmas/Caratheodory.lean` to the end of `Lemmas/CaratheodoryJordan.lean`.
    - There it is proved as `caratheodory_jordan_clean`, which has the identical statement and is axiom-clean.
    - The θ-curve-free chain `C1`–`C10` proving it lives in that module, and `Lemmas/Caratheodory.lean` cannot
      import it.
  * §35.5 (`annulus_extension_extends`, 2026-09-26, user decision): the statement was **false**.
    - Nothing forced the boundary map `h` to send the unit circle onto itself.
    - Counterexample, Lean-checked: `r = 1/2`, `g z = z/2`, `h = G = ẑ/2`.
    - Fix: added `hh : ∃ f, HasBoundaryValues f h`, so `h` is a boundary correspondence of `Δ`.
  * §26.3 (`eq26_13`, 2026-09-26, user decision): the equality clause of `λ² ≤ D_f J_f` was **false** at zeros of
    `q'`.
    - There `λ = J = 0`, so equality holds, but the alignment condition need not.
    - Counterexample: `q ≡ 1`, `q' ≡ 0`, `f z = z - z̄/2`.
    - Fix: added `hq' : q' (f x) (localMapExpr f x z) ≠ 0`.
  * §25 (`thm25_1_geodesics`, `thm25_2_polygon`, `thm25_3_unique_geodesic`, `thm25_4_cor_unique_geodesic`,
    2026-09-26, user decisions): four statements were **false**. The first three were refuted by axiom-clean Lean
    probes.
    - **Pause loophole.** `IsPhiGeodesic` / `IsPhiGeodesicRS` only constrain short windows around each time, so a
      curve may go out, pause, and come back.
      - A spike from `0` to `0` and the constant curve at `0` are both "geodesics", with different traces.
      - A constant curve is a "geodesic" but no straight arc.
      - Fix: no-pause **hypotheses** (`∀ s < t, ∃ u ∈ [s, t], γ u ≠ γ s`) in thm25_1, thm25_3 and the uniqueness half
        of thm25_4_cor.
      - The definitions are unchanged, so the existence results, which must allow constant paths, stay true.
      - In thm25_1 the reparametrization `h` must also map `[a, b]` onto itself.
    - **Unoriented polygons.** `PhiPolygon` had no orientation, so a clockwise square with `φ ≡ 1` has all angles
      `3π/2`.
      - Fix: fields `positive` (the domain lies to the left of every side) and `simple` (sides meet only at
        consecutive vertices).
  * §26 (2026-09-26, user decisions, batch 1): four statements were **false**; three have Lean refutations.
    - `teichmullerMap_beltrami`: with no connectedness, `IsTeichmullerMap` puts no constraint on components where
      `q ≡ 0` (`S₀ = {Re z ≠ 0}`, `f = 2x + iy`). Fix: `[ConnectedSpace S₀]`.
    - `grotzsch_generalized`: `IsImageUnder` reads the raw vertex values of `f`, and `invFunOn` at rectangle vertices is
      junk. Fix: the vertex correspondence goes through a boundary extension (`IsHomeoExtension` + `F (Q.vert i) =
      Q'.vert i`), in the hypothesis and for the extremal map.
    - `eq26_9`: λ uses the full derivative, which a q.c. map need not have on a (null) arc
      (`f = z + i max(Im z, 0)`), and `phiLengthOn` needs Lipschitz pieces. Fix: Lipschitz, a.e. differentiability
      along the arc, and `f '' range α` inside the chart at `f x`.
    - `lambdaStretch` / `jacobianQD` evaluated `q'` in the chart at the centre image `f x`, which is junk inside
      `surfaceIntegral`'s infimum over partitions. That made `lemma26_2` and `eq26_14` (second conjunct) false.
      - Fix: the new def `localMapExprAt f x z` (the chart at the actual image point `f p`).
      - `eq26_13` was restated accordingly and re-proved.
  * §26 / §35 (2026-09-26, user decisions, batch 2):
    - `lemma26_1` was **false**: `phiLengthPath` counts only Lipschitz chart pieces, so a `p + L√t` arc has length
      `⊤` while a q.c. `f` straightens it. Fix: only arcs with `phiLengthPath q α < ⊤`.
    - `lemma26_2_averaging` was **vacuous**: each `α_p` could be a `Loop` with nothing required, and the averaging
      identity was missing. It is strengthened:
      - `α` is total, and the arc clause holds off `E`;
      - `E` is outer-null in every chart;
      - the identity `∬ l_q(f(α_p)) dA_q = 2L ∬ λ_f dA_q` is stated with the new `phiLengthPathInv`, the true length
        (the infimum over reparametrizations).
    - `eq35_2_crossing_arcs`: the redundant hypotheses `hne`, `h₁`, `h₂` were dropped. The statement is slightly
      stronger than the book's (35.2) and still true.
  * §23 / §27 / §33 / §36 (`IsManifold`, 2026-09-26, user decision): six statements lacked holomorphic
    compatibility of the atlas and were **false**.
    - They are `lift_isKQC_automorphic` (S23), `exists_normalizedLift` and `normalizedLift_unique` (S27),
      `normalizedLift_beltrami_mem` (S33), and `qc_extends_to_border` and `thm36_1` (S36).
    - `ChartedSpace ℂ` alone gives only topologically compatible charts, so `IsQCRS`/`IsKQCRS` and
      `IsUniformization` do not control the lift.
    - Counterexample, Lean-checked for S23 and S36: a copy of `ℍ` charted by the radial stretches
      `w ↦ (w - x)|w - x|`, with a Lipschitz self-map that has no homeomorphic extension to the boundary.
    - Fix: `[IsManifold 𝓘(ℂ) ω _]` on the surfaces involved.
  * §27.1 (`markedRS_equiv_same_surface`, 2026-09-26, user decision): the `⇒` half of the iff was **false**.
    - Counterexample: genus `2`, `f = id`, `f₁ = ι` the hyperelliptic involution. Then `(X, id) ~ (X, ι)` via
      `c = ι`, but `ι` is not homotopic to the identity.
    - Fix: only `f ≃ f₁ → (X, f) ~ (X, f₁)` is kept.
  * §36 (F1–F7, 2026-09-26, user decisions): seven statements were **false** or **vacuous**; most have Lean
    refutations.
    - **F1**, `IsFundamentalDomainH`: `F` could have empty interior (`F = {z ∈ ℍ | Re z ∉ ℚ}` for
      `⟨z ↦ z + √2⟩`, where `hamiltonNorm ≡ 0`), or a boundary of positive measure that is counted twice.
      - This made `thm36_2_hamilton`, `hamilton_contradiction`, `strebel_hamilton_sufficient` and
        `lemma36_2_kernel_orthogonal` false.
      - Fix: the definition gains `volume (F \ interior F) = 0`.
    - **F2**, `poincare_series_surjective`: `∑' γ : Γ` runs over `Γ ⊆ SL(2, ℝ)`, so when `-1 ∈ Γ` every Möbius
      map is counted twice (counterexample `Γ = {±1}`, `F = ℍ`).
      - Fix: the pairing identity carries the multiplicity `Nat.card ↥(Γ ⊓ Subgroup.zpowers (-1))`.
    - **F3**, `qc_extends_to_border`, `thm36_1`: the `IsManifold` entry above.
      - Only the `⇐` half of `thm36_1` is proved so far, as the helper `h36_thm36_1_mpr`.
    - **F4**, `lift_homotopy_agrees_on_limitSet`: `H` was arbitrary, so a homotopy constant in space
      (`H(x, t) = σ(t)` on `Δ* = ℍ/⟨z ↦ z + 1⟩`) broke it, even with holomorphic charts.
      - Fix: `H(·, 0)` is a homeomorphism `f₀` (`hH₀`), and `Γ` is Fuchsian.
    - **F5**, `hamilton_sequence_exists`: for `μ = 0` and a group with no integrable automorphic forms
      (e.g. `SL(2, ℤ)`) no unit `φ` exists.
      - Fix: the hypothesis `hA : ∃ φ ∈ integrableAutomorphicQD Γ F, phiArea φ F = 1`.
    - **F6**, `thm36_2_finite_type` was **vacuous**. `hfin` asked for a finite span of
      `integrableAutomorphicQD Γ F`, whose elements are unconstrained off `ℍ`, so it never held.
      - Fix: `hfin` now concerns the restrictions `upperHalf.indicator φ`.
    - **F7**, `cor36_1`: for a compact surface one may take `K = F`, which makes the left side `0`.
      - Fix: the hypothesis `hvol : volume (F \ K) ≠ 0`.
    - The non-book `c36_d_*` helper block was moved up, verbatim, to before `thm36_1`.
  * §29.1 (`eq29_3`, `eq29_7`, 2026-09-26, user decisions): both statements were **false**, with the same
    junk-chart cause as the §26 `lambdaStretch` correction.
    - They read `fₙ ∘ f⁻¹` through a chart of `Sₙ` that need not contain the image point. An
      `OpenPartialHomeomorph` is an arbitrary total function outside its source.
    - Counterexamples take `f = fₙ = id` and give `Sₙ` a holomorphic atlas of small balls with junk values
      off each ball.
      - `eq29_3` (unconditional Lean refutation on the flat torus): the left side is `1`, the right side `0`.
      - `eq29_7`: since `surfaceIntegral` is an infimum over chart partitions, the right side drops below the
        left side `1`. The Lean refutation assumes a closed surface of genus `g > 1`, which the project
        cannot build yet.
      - Adding `IsManifold` alone does not help, since the twisted atlas is holomorphic.
    - Fix: both statements read `fₙ ∘ f⁻¹` in the chart at the image point (`localMapExprAt`).
      - `eq29_3` also gains `[IsManifold 𝓘(ℂ) ω S]` and `[IsManifold 𝓘(ℂ) ω Sn]`, as `eq29_7` already had.
      - `eq29_7` is then Teichmüller's main inequality for `fₙ ∘ f⁻¹ ≃ gₙ⁻¹`.
  * §26.4 (`lemma26_1`, `lemma26_1_track_length_continuous`, 2026-09-26, user decisions): two statements were
    true but did not say what the book's proof uses.
    - `lemma26_1` measured the image arc `f(α)` with `phiLengthPath`, which counts only Lipschitz chart pieces.
      - A quasiconformal image is generally not Lipschitz-parametrized, so the right side was `⊤` on exactly the
        arcs of the averaging argument, and Lemma 26.2 did not follow.
      - Fix: the image is measured by the true length `phiLengthPathInv`. The new statement is stronger, and the
        definition moved up within S26.
    - `lemma26_1_track_length_continuous`, first conjunct: it stated continuity of the φ-distance from `p` to
      `f(p)`.
      - The book's proof (and the docstring) needs continuity of the length of the shortest curve in the
        homotopy class of the track `t ↦ F(p, t)`.
      - Fix: it now states that.
  * §29.1 (`teichDistance_metric`, 2026-09-26, user decision): the five metric axioms were one conjunction.
    - The third, `d_T(τ₁, τ₂) = 0 → τ₁ = τ₂`, needs the existence of extremal maps. It is now its own
      declaration, `teichDistance_eq_of_eq_zero`, placed right after.
    - The other four stay under the old name. The total content is unchanged.
  * §27.1 (`normalizedLift_unique`, `StandardGenerators`, 2026-09-26, user decisions): five statements were
    **false**.
    - `normalizedLift_unique` concluded `G₁ = G₂` for the boundary extensions, which `IsNormalizedLift` pins down only on
      the closed upper half-plane (unconditional Lean refutation). Fix: `G₁ = G₂` on `closure ℍ`.
    - `exists_standardGenerators` and `exists_inducedGenerators`: the field `generate` asked for the matrix group `Γ`
      exactly.
      - A uniformization's `Γ` may contain `-1`, and a standard system never generates `-1`: surface groups are
        Hopfian, and the lifted relation (27.4) is `+1` by Euler-class parity.
      - Fix: generation modulo `±1`, i.e. of the Fuchsian group as Möbius maps.
    - `eq27_9_14_last_determined` and `eq27_12_d_ne_one`: nothing tied the number of generator pairs to the genus.
      - A standard system could be padded with a trivial last pair `(1, δ_g)` (Lean refutation, conditional on some
        cocompact torsion-free Fuchsian group having a standard system).
      - Fix: the new field `alternate`, the book's remark after (27.5) that the fixed points of `γ_g` and `δ_g`
        alternate on `ℝ̂`.
    - In the same file, the block of facts about hyperbolic elements (`attractingFixedPoint` … `hyperbolic_normal_form`)
      moved up, verbatim, before `fuchsianFixedPoints`, which uses it.
  * §30.1 (`lemma30_1`, 2026-09-26, user decision): Lemma 30.1 was **false** (unconditional Lean refutation on
    `Δ* = ℍ/⟨z ↦ z + 1⟩`, the project's first concrete uniformization).
    - The right-hand side allowed the power `n = 0`: a null-homotopic loop, covered by `γ = 1`, qualified, and `1` is
      not parabolic.
    - It described the puncture curve by its image, `φ '' range β = sphere 0 r`. A loop going out and back along the
      circle has that image but is null-homotopic, so adding `n ≠ 0` alone is still false (also refuted in Lean).
    - Fix: `β` traverses the circle `|ζ| = r` once (`φ(β t) = r e^{2πit}`), and `n ≠ 0`.
  * §30.5 (`hurwitz`, 2026-09-26, user decision): Hurwitz's theorem is also stated in part, as `hurwitz_finite`
    (finitely many conformal automorphisms), so that this part can be proved for surfaces given as `ℍ/Γ`.
    - `hurwitz` itself is unchanged. The `84(g−1)` bound keeps the finiteness conjunct, because `Set.ncard` of an
      infinite set is `0` in Lean.

## Modelling conventions

* **Extended plane.** Plane domains are subsets of `ℂ`; points at infinity live in
  `ℂ̄ = OnePoint ℂ`.  A Jordan domain never contains `∞`, but may have it on its boundary.
* **Quadrilaterals.** The positive order of the vertices of a quadrilateral is encoded by a
  conformal map onto `ℍ` sending the vertices to cyclically increasing reals.  A map is
  *sense preserving* when images of quadrilaterals are again quadrilaterals.
* **Curves.** Locally rectifiable curves are maps that are locally Lipschitz on `(0,1)` (the
  arc-length reparametrization).  `ρ`-length is `∫ ρ(γ)|γ'|`.
* **Formal derivatives and qc maps.** `∂_z`, `∂_z̄` are defined through the real Fréchet
  derivative.  Almost-everywhere statements about quasiconformal maps rely on their a.e.
  differentiability (Theorem 9.3); generalized solutions of the Beltrami equation use `L_p`
  generalized derivatives (Definition 9.2).
* **`C^∞` versus analytic.**  In current Mathlib `ContDiff ℝ ⊤ f` means that `f` is real-analytic.
  `C^∞` is `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f`, with notation `∞` in the scope `ContDiff`,
  which is not opened in files that use `ω` as a variable name.  The book's `C₀^∞` is written in
  the second form (§11, §12).  In the first form, compact support would force the function to
  vanish and make the statements degenerate.
* **Riemann surfaces.** A Riemann surface is a Mathlib complex manifold
  (`ChartedSpace ℂ S`, `IsManifold 𝓘(ℂ) ω S`, connected, Hausdorff).
  * Differentials of type `(m, n)` are chart-compatible coefficient families.
  * The genus is defined through the surface-group presentation of `π₁`.
  * Teichmüller spaces are quotients of marked surfaces (or of Beltrami coefficients).
  * Integrals over a surface with respect to `|φ| dx dy` (`surfaceIntegral`, `quadDiffNorm`) are
    computed on a countable measurable chart partition; the `φ`-length of a path
    (`phiLengthPath`) by cutting the path into pieces lying in charts.
  * A Teichmüller deformation `S_{ω,k}` (§26.2) is a closed Riemann surface `X` with a
    homeomorphism `e : S₀ ≃ₜ X` (the identity of the point set in the book) whose local
    expressions in natural parameters are the stretches `teichStretch`, `teichStretchZero`;
    its existence is the theorem `exists_teichDeformation`.
  * Standard generators of a Fuchsian group (§27.1) are bundled in `StandardGenerators`; the
    relation (27.4) holds in `SL(2, ℝ)` up to sign.  The Fricke coordinates of a marked surface
    are described by the relation `IsFrickeCoords` (the choices of lifts being existential).
  * Surfaces of finite type `(g, n, m)` are modelled by their interiors together with a
    `FiniteTypeStructure` (a closed surface, `n` punctures and `m` closed discs); admissible
    quadratic differentials live on the closed surface (`admissibleQDSpace`, a real subspace),
    the Schottky double is an anticonformal involution on a closed surface (`IsSchottkyDouble`).
  * In §33–§36 the Fuchsian model `ℍ/Γ` is used throughout; `f^μ` (`fMuSym`) and `f_μ`
    (`normalizedSolution`) are the two normalized maps of §33.1.
  * "Homotopic modulo the boundary" (§36.1, `HomotopicModBoundary`) is expressed through lifts. The lifted
    homotopy extends continuously to `ℂ̄ × [0, 1]` and is constant in `t` on **all** of `ℝ̂`, whereas the book
    fixes only the ideal boundary `b(G) = ℝ̂ ∖ Λ(G)`.
    - The two notions are equivalent by the book's own lemma (`lift_homotopy_agrees_on_limitSet`): a lifted
      homotopy is automatically constant on the limit set `Λ(G)`.
    - With this definition, the `⇒` half of `thm36_1` does not need that lemma, which remains a separate
      statement.
  * **Uniformization companions** (user decision, 2026-09-26). The book quotes the uniformization theorem
    (§22, sorried here).
    - Book statements on an abstract closed surface whose proofs need `S = ℍ/Γ` stay exactly as the book states
      them, and stay `sorry`: `thm23_1_cor`, `conformal_unique_extremal`, `thm26_2_uniqueness`, `eq26_15_16`,
      `teichmullerMap_isExtremal`, `lemma26_1`, `lemma26_2`.
    - Their mathematical content is proved in companion theorems `<name>_of_uniformization`. Each takes the book
      statement's hypotheses plus explicit `IsUniformization` data and has the same conclusion.
    - A book statement then follows from its companion together with the uniformization theorem.
    - Status (2026-09-26): all seven companions are proved and axiom-clean, in `Lemmas/UniformizedTeichmuller.lean`.
      Among them is Teichmüller's uniqueness theorem for surfaces given as `ℍ/Γ`
      (`thm26_2_uniqueness_of_uniformization`).
    - Also proved (2026-09-26): companions of `lemma27_3_dilatation_bound`, `lemma27_1_injective` and
      `teichSpace_deformation_bijection`.
      - Teichmüller's existence theorem is proved in the variant `thm27_2_existence_qc_of_uniformization` (user
        decision), for homotopy classes containing a quasiconformal map.
      - The book's `thm27_2_existence` covers every homotopy class of homeomorphisms, and so needs S24's
        `exists_qc_in_homotopy_class` as well.
* **Notation.** `ω` is Mathlib's notation for analytic smoothness (`IsManifold 𝓘(ℂ) ω S`), so the
  quadratic differential `ω` of the book is called `q` in Lean; `π` is `Real.pi`, so projections
  are called `p`, `pr`.
