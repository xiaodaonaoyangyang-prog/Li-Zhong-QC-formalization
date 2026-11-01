# 李忠《拟共形映射与Teichmuller空间》— Lean 4 formalization

A complete, machine-checked formalization of

> 李忠, *拟共形映射及其在黎曼曲面论中的应用* (Li Zhong, *Quasiconformal Mappings and
> Teichmüller Spaces*).

Every definition of the book is a genuine Lean definition, and every theorem, lemma,
corollary and numbered formula is stated and proved.
- **As of 2026-10-18 every statement of `LiZhongQC` is proved.** After a full clean rebuild, `Audit.lean`
  reports 10857 theorems, all depending only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`):
  0 `sorry`, 0 carriers.
- A second library, `References`, states the books and papers the project draws on, one work after another (see
  *References* below).
- A third library, `DouadyEarle`, is a vendored snapshot (2026-10-06) of the sorry-free, Mathlib-only part (Sections
  1–4: the conformal barycenter and the Douady–Earle extension) of the sister project
  `Conformally_natural_extension_of_homeomorphisms_of_the_circle`; see `DouadyEarle/PROVENANCE.md`.

## Building

The project uses Lean `v4.36.0-rc2` (`lean-toolchain`) and Mathlib at tag `v4.36.0-rc2`
(commit `9d581dff`, 2026-10-27).

`lakefile.toml` points to a local checkout of that tag (`D:/lean/mathlib4-v436rc2`). To build elsewhere:
1. Replace that `[[require]]` block by

   ```toml
   [[require]]
   name = "mathlib"
   git = "https://github.com/leanprover-community/mathlib4"
   rev = "v4.36.0-rc2"
   ```

2. Run `lake update mathlib`.
3. Run `lake exe cache get` to download the prebuilt Mathlib files for that tag.

```
lake build            # builds the default libraries (root modules `LiZhongQC`, `References`, `DouadyEarle`)
```

The build succeeds (rebuild on Mathlib `v4.36.0-rc2`, 2026-11-01: all libraries, 0 errors). `LiZhongQC` has no `sorry` warning. The
remaining warnings are the `sorry` warnings of the statements of `References` (by design, see below), and some
deprecation and linter hints.

**Statistics** (2026-10-18):
* The project's modules contain 10857 theorems, auxiliary lemmas included.
  - All 10857 depend only on the standard axioms.
  - No statement is `sorry`.
  - None is a *carrier*, i.e. a complete proof that goes through an open statement.
* In general a finished proof is not by itself a guarantee: check it with `#print axioms`.
* To re-measure, run `lake env lean Audit.lean` in the repository root.
  - It is not part of the library, so `lake build` ignores it.
  - It walks the dependency graph of every theorem defined in the project's modules, stopping at Mathlib (which contains
    no `sorry`), and prints the partition above.
  - A theorem is a carrier when it depends on `sorryAx` but its own body does not mention it.
  - Bodies must be read with `ConstantInfo.getUsedConstantsAsSet`. `ConstantInfo.value?` returns `none` for imported
    theorems, whose bodies are loaded lazily, and would make every carrier look clean.

## Proof status

Proofs follow the book's arguments where they can. Where the book quotes a result, leaves a step to the reader, or
argues in a way that is hard to formalize, the step is either proved here, often by a different route (see *Notes on
selected proofs* below), or the statement stays `sorry` and its docstring says why ("Not proved (kept as `sorry`):
…").

Every proof installed in the current workflow is checked with `#print axioms` to depend only on the three standard
axioms (`propext`, `Classical.choice`, `Quot.sound`); a proof is never installed if it goes through a statement that is
still `sorry`. Earlier passes allowed that, but no such *carrier* is left: the last two
(`hahn_mazurkiewicz_subset`, `frontier_locallyConnected_iff_isCurve`) became clean when the Hahn–Mazurkiewicz
theorem was proved (see *Statistics*).

**By chapter** (written 2026-10-09, when 81 statements were open; all of them have since been proved, the last one,
Strebel's sufficiency criterion `strebel_hamilton_sufficient` of §36, on 2026-10-18; see *Statistics*):

* **Chapter 1 (§1–§10): complete.** The last statement proved is `isKQC_of_dcModulus_bound` (§7), the converse of
  Theorem 7.4 (the ring characterization), for which the book refers to Lehto–Virtanen. Its proof goes through the
  analytic definition of §§9–13, so the statement lives in `Lemmas/RingCharacterization.lean` (user decision,
  2026-09-27). Proved, among others:
  * Theorem 1.1;
  * Theorem 2.1 in all three cases;
  * Theorem 4.9 in its general form, with its corollaries;
  * the extremal problems of §5, Grötzsch's theorem and Theorem 6.1;
  * Theorems 7.1–7.4 and the ring characterization of `K`-quasiconformality;
  * the normal-family theorems 8.1–8.2;
  * all of §9 (Menchoff's lemma, Lusin's property (N), Theorems 9.1–9.6);
  * Theorems 10.1–10.2.
* **Chapter 2 (§11–§13): complete.** This includes:
  * the `L_p` bound for the Beurling–Ahlfors transform, through the Riesz–Thorin theorem;
  * the existence theorem of §12;
  * the measurable Riemann mapping theorem and holomorphic dependence on parameters;
  * the similarity principle;
  * Theorems 13.1–13.8.
* **Chapter 3 (§14–§15): complete.** §15 includes the sharpness of Mori's constant and of Theorem 15.3. In §14 the
  product expansions (14.23)–(14.24) are proved without the Jacobi triple product (see *Notes on selected proofs*).
* **Chapter 4 (§16–§18): complete.** It includes the Beurling–Ahlfors extension with `K ≤ ρ²`, Ahlfors' theorem that
  a Jordan curve is a quasicircle iff it has bounded turning, quasiconformal reflections and welding, and the remark
  that a quasicircle can have Hausdorff dimension arbitrarily close to 2 (a generalized Koch curve; the statement
  lives in `Lemmas/KochQuasicircle.lean` because its proof uses Theorem 18.1, user decision 2026-09-27).
* **Chapter 5 (§19–§21): §19 is complete.** §20 is complete except `thm20_2`, which is false as stated and left
  unchanged by decision (see *Corrections*). §20 includes:
  * Ahlfors' Theorem 20.3;
  * Theorem 20.4;
  * Gehring's Theorem 20.5;
  * the equivalence of Schwarz domains and quasidiscs.

  §21 (the universal Teichmüller space and the Bers embedding, Theorems 21.1–21.4, including Gehring's Theorem 21.4) is
  complete except Gehring's remark that the closure of `T*` is smaller than `𝓕*`, and Thurston's theorem that `𝓕*`
  has isolated points.
* **Chapters 6–9 (§22–§32): in progress again (from 2026-10-06; Wolpert's lemma `lemma30_3_wolpert`, Lemma 30.1
  Theorem 25.1 and the local shortest-neighbourhood lemma of §25 proved 2026-10-08; shortest curves are geodesics, 2026-10-09).** They need the foundations of Riemann-surface theory:
  uniformization, Riemann–Roch, and fundamental groups of glued surfaces. 74 statements are open there. Much of the
  machinery is proved, and Teichmüller's uniqueness and existence theorems are proved for surfaces given as `ℍ/Γ` (see
  *Modelling conventions*).
* **Chapter 10 (§33–§34):** the Bers embedding theorem for Fuchsian groups (Theorem 33.1) and Earle's lemmas are
  proved, and so is `teichDistanceGamma_eq` (2026-10-08). Three finite-dimensional statements are open (one in §33, two in §34).
* **Chapter 11 (§35–§36): §35 is complete** (the Reich–Strebel main inequality, Theorems 35.1–35.8, Lemmas 35.1–35.6).
  §36 is complete except Strebel's sufficiency criterion `strebel_hamilton_sufficient`.
* **Supporting files: complete.** Prime-end theory, the Hahn–Mazurkiewicz theorem and Lindelöf's theorem.
  - Carathéodory's theorem for Jordan domains (`Lemmas/CaratheodoryJordan.lean`) and the Hahn–Mazurkiewicz theorem
    (`hahn_mazurkiewicz`, `ClusterSets.lean`), by a chain refinement on uniform grids with no Cantor set and no
    paths.
  - In `Lemmas/PrimeEnds.lean`: Carathéodory's continuity theorem (`caratheodory_continuous_iff`),
    `crosscut_separates`, `locallyConnectedSpace_frontier_iff` (the boundary is locally connected iff every
    null-chain has a one-point impression, by a chain of circle arcs along Wolff radii chosen off a Jensen–Fatou null
    set), Lindelöf's theorem (`lindelof`, by Lindelöf's reflection argument with a half-disc and a quarter-disc
    harmonic majorant), and Carathéodory's prime-end theorem (`caratheodory_primeEnd`,
    `caratheodory_primeEnd_principal`, `principalPoints_isCompact_isConnected`): prime ends are the classes of
    circular chains along Wolff radii, surjectivity follows Pommerenke's Theorem 2.15 (c) without the length–area
    lemma, and principal points are radial cluster points (Koebe distortion along the radius).
  - These statements were moved to `Lemmas/PrimeEnds.lean`, unchanged, because their proofs need tools of §20 (user
    decision, 2026-09-27).

### Notes on selected proofs

**§1, Theorem 1.1** is proved in full.
- Uniqueness comes from the rigidity of conformal maps between rectangles (`Lemmas/RectangleRigidity.lean`).
- Existence, together with the elliptic-integral formula for the modulus of `ℍ(-1/k, -1, 1, 1/k)`, comes from the
  Schwarz–Christoffel map `F(z) = ∫ dζ/√((1-ζ²)(1-k²ζ²))` in `Lemmas/SchwarzChristoffelRect.lean`.
- The book's injectivity step, which uses the argument principle, is replaced by a covering-map argument: `F` is a
  proper local homeomorphism from `ℍ` onto the rectangle, hence a covering map, hence a homeomorphism because the
  rectangle is simply connected.
- Continuity of `F` at `∞` comes from the inversion `ω ↦ -1/(kω)`, which permutes the four prevertices.

**§7, the ring characterization** (`isKQC_of_dcModulus_bound`, the converse of Theorem 7.4) is proved through the
analytic definition rather than by Lehto–Virtanen's geometric argument (I, Theorem 7.2).
- The hypothesis `M(B) ≤ K M(f(B))` is applied to slit-rectangle rings `β + α Ξ_h`, where `Ξ_h` is the box
  `(-1, 1) × (-h, h)` minus a central slit; averaging over rectangular loops gives `M(Ξ_h) ≥ πh/(2(1 + 3h))`.
- Small such rings give the per-rectangle estimate of the §9 ACL argument, so `f` is ACL.
- At a point of differentiability, sense preservation (local winding `+1`) gives `|∂_{z̄} f| ≤ |∂_z f|`, and a ring
  with its slit along the direction of maximal stretch gives `|∂_z f| + |∂_{z̄} f| ≤ K (|∂_z f| - |∂_{z̄} f|)`.
- Theorem 10.1 then gives `K`-quasiconformality.

**§9, Lemma 9.2** (⇐) passes to the limit segment by segment: by Fatou's lemma, the `L¹` errors of the approximating
derivatives have `liminf = 0` on almost every segment. Lemma 9.2 (⇒) uses mollifiers. Mathlib lacks the fact that
mollifiers form an approximate identity in `L_p`, so it is proved here from Jensen's inequality and the density of
compactly supported continuous functions (`tendsto_eLpNorm_convolution_normed_sub`).

**§11.**
- The complex Green formulas (11.9) and (11.10) are proved on a disc via polar coordinates, since Mathlib's divergence
  theorem is available for boxes only (`Lemmas/GreenDisc.lean`, `Lemmas/GreenPolar.lean`).
- Pompeiu's formula (11.11) uses a cutoff that smooths the Cauchy kernel (`Lemmas/Pompeiu.lean`).
- (11.17), `∂_z̄ T(ω) = ω` and `∂_z T(ω) = H(ω)` for `ω ∈ C₀^∞`: `T(ω)` is a convolution with a locally integrable
  kernel, and `∂_z` comes from Green's formula applied twice to one cutoff function.

**Lemma 11.2.**
- The two-singularity estimate is obtained not by the book's scaling and rotation argument but by splitting the plane
  according to which singularity is the nearer one. This needs only translations and the two radial integrals
  `∬_{|w| < ρ} |w|^{-a}` and `∬_{|w| > ρ} |w|^{-a}`.
- Since the statement assumes only `ω ∈ L_p(ℂ)`, the individual integrals `∫ ω(ζ)/(ζ - z)` need not converge. The
  proof therefore never subtracts them; it uses that the *difference* kernel is integrable, so the two integrands are
  integrable together or not at all, and when neither is, both sides vanish.

**§14.**
- (14.11) is proved, using the value distribution of `℘` from `Lemmas/WeierstrassValues.lean`.
- (14.23)–(14.24) are proved through the σ-product `F(z) = sin(πz) ∏ (1 - q^{2n} e^{2πiz})(1 - q^{2n} e^{-2πiz})`
  of the lattice `ℤ + τℤ`, where `q = e^{iπτ}`. Liouville's theorem for elliptic functions gives the addition
  formula `℘(z) - ℘(u) = -F'(0)² F(z + u) F(z - u) / (F(z)² F(u)²)`. At the half periods, together with (14.21),
  it gives both products, so the Jacobi triple product is not needed.

**§15.**
- The sharpness of Theorem 15.3 is proved through an elliptic descent. The affine map between the lattices `⟨1, τ₀⟩` and
  `⟨1, τ₁⟩`, where `τ₀, τ₁` are lifts at hyperbolic distance `ln K`, descends through the normalized `℘` to a
  `K`-quasiconformal map of the sphere fixing `0, 1, ∞`.
- The minimizing lift exists by compactness, and paths are lifted through the modular covering.
- The sharpness of Mori's constant uses an explicit extremal family.

**§16, Theorem 16.2** (quasicircle ⇔ quasiconformal reflection). The direction (⇐) glues a Riemann map and the
reflection across the real line, i.e. on the preimage side. This needs only the removability of `ℝ`, not of the curve.

**§16, the remark on dimension** (`quasicircle_hausdorff_dim_near_two`, in `Lemmas/KochQuasicircle.lean`).
- The quasicircle is a generalized Koch curve: for `c = cos θ ∈ (0, 1/2]` four similarities of ratio
  `r = 1/(2 + 2c)` map `[0, 1]` onto the sides of the polygon `0, r, r + r e^{iθ}, 1 - r, 1`, and the arc is the
  fixed point of the Read operator on curves from `0` to `1`.
- The pieces stay in the triangle `conv {0, 1, (1 + i)/2}` and meet only at common vertices at angles proportional to
  `c`, so the arc has bounded turning (constant `64/c`) and a co-Hölder parametrization with exponent
  `log 4 / log (2 + 2c)`, which bounds its Hausdorff dimension from below.
- Closed by the tent `t ↦ t - i min(t, 1 - t)`, it is a Jordan curve of bounded turning, hence a quasicircle by
  Ahlfors' Theorem 18.1; the choice `c = min(ε, 1) log 2 / 2` gives dimension above `2 - ε`.

**§17, (17.7).** The Beurling–Ahlfors extension with parameter `r = 2` is `ρ²`-quasiconformal for every
`ρ`-quasisymmetric `h`; this uniform statement is `s17p_beurlingAhlfors_two`. The dilatation is convex in each
normalized variable, so it suffices to check the eight corners of a box.

**§18, Theorem 18.1** (Ahlfors). A curve of bounded turning is a quasicircle.
- The welding of the curve is shown to be quasisymmetric by a modulus-only argument: quadrilaterals of modulus `1` and
  `Λ(ρ)` are compared through annulus and disc bounds.
- Then the welding theorem finishes.
- A separate winding-number argument shows that the welding is *increasing*: the glued plane homeomorphism cannot have
  local degree `+1` near `i` and `-1` near `-i`.

**§20.**
- Theorem 20.1 uses Nehari's classical argument with the Hardy inequality instead of the book's route through
  quasiconformal extension.
- Theorem 20.4 uses Koebe's ¼-theorem in the form (20.14). The planar separation step, which the book asserts without
  proof, is replaced by an analytic argument (a Cousin splitting and Cauchy's theorem for polygons) instead of
  Janiszewski-type topology.
- The proof of Theorem 20.5 (Gehring) shows that a `k`-locally connected domain (Theorem 20.4) is a Jordan domain,
  through Carathéodory continuity and injectivity under a qualitative local connectivity and a crossing theorem in
  the disc. Its boundary has bounded turning with constant `2(2k² + 1)`, so Theorem 18.1 applies.

**§21, Theorem 21.4** (Gehring). An interior point of `𝓕*` gives a Schwarz domain, hence a quasidisc (Theorem 20.5),
and the conformal map onto a quasidisc extends quasiconformally.

**§25.**
- (25.2), (25.3), (25.5), (25.6), (25.8) and (25.9) are proved in `Lemmas/LocalRoots.lean`.
- Horizontal and vertical trajectory arcs are `φ`-straight (`horizontal_vertical_isPhiStraight`).
- Teichmüller's lemma (`thm25_2_polygon`) is proved through the Umlaufsatz of `Lemmas/Umlaufsatz.lean`.

**§26.**
- The injectivity (26.5) of the new parameter at a zero needs no roots of unity: for `p = (ζ/|ζ|)^{m+2}`, comparing the
  `(m+2)`-th powers and their moduli gives `(1 - k²)(p₁ - p₂) = 0`.
- That this parameter is a homeomorphism of `ℂ` needs no invariance of domain: it is continuous, proper and surjective.

**§28.** `hasGenus_of_homeomorph` transports the fundamental group along a homeomorphism
(`fundamentalGroupMulEquivOfHomeomorph`); Mathlib provides only basepoint-change isomorphisms.

**§30.** The translation length is the minimal displacement (`translationLength_eq_inf_dist`). This rests on the
identity `|cτ² + (d - a)τ - b|² = (Im τ)² (tr² - 4) + (c|τ|² + (d - a) Re τ - b)²`, which avoids diagonalizing the
matrix.

**§35.**
- The Reich–Strebel main inequality (35.5) and Theorems 35.1–35.8 go through the flux route of `Lemmas/FluxRoute.lean`
  and Teichmüller's lemma.
- Lemma 35.1, (35.2) and the endpoints of trajectories replace the book's boundary-uniqueness step by Jensen's formula
  on Riemann maps of sector pieces (`Lemmas/BoundaryJensen.lean`). A horizontal ray that did not converge would cross a
  sector in arcs of `φ`-length tending to `0`, which Jensen's formula forbids.
- Lemma 35.4 needs no measurability assumption on `κ`. `Δ` is split along a measurable version of `{|F| ≤ |φ| g(k')}`,
  and a non-measurable integrand has the junk integral `0`, for which the estimate is trivial.

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
| `Lemmas/UniformizedUniqueness` | not a book section: companions `<name>_of_uniformization` of the §23/§26 uniqueness statements (`thm23_1_cor`, `conformal_unique_extremal`, Lemmas 26.1–26.2, Thm 26.2, (26.15)–(26.16), `teichmullerMap_isExtremal`), proved for surfaces given as `ℍ/Γ` (see Modelling conventions) |
| `Lemmas/UniformizedTeichmuller` | not a book section: companions `<name>_of_uniformization` of the §27 existence statements (Lemma 27.1, Lemma 27.3's bound, the bijection `Φ`, Thm 27.2 for quasiconformal classes) and of §29/§30 statements (the third metric axiom of `d_T`, finiteness of the automorphism group, proper discontinuity of `Mod(S₀)`, Thm 30.3, Thm 30.4) and of (32.2), proved for surfaces given as `ℍ/Γ` |
| `Lemmas/RingCharacterization` | §7: the converse of Theorem 7.4 (`isKQC_of_dcModulus_bound`), placed after §13 because its proof uses the analytic definition (Theorem 10.1), with slit-rectangle ring estimates |
| `Lemmas/KochQuasicircle` | §16: the remark that quasicircles can have Hausdorff dimension close to `2` (`quasicircle_hausdorff_dim_near_two`), placed after §18 because its proof uses Theorem 18.1 |
| `Lemmas/PrimeEnds` | not a book section: the prime-end theory that needs §20 — Carathéodory's continuity theorem, `crosscut_separates`, `locallyConnectedSpace_frontier_iff`, Lindelöf's theorem and Carathéodory's prime-end theorem (moved from `Lemmas/Caratheodory.lean` and `ClusterSets.lean`); all proved |

Theorem names carry the book's numbering, e.g. `thm4_1_modulus_eq_inv_extremalLength`,
`eq5_19`, `lemma20_3`, `thm26_2_uniqueness`, `eq27_9_14_last_determined`.

## References

A second library, `References` (root module `References.lean`), formalizes at statement level the books and papers
the project draws on, one work after another (user order, 2026-09-28).
- Definitions are genuine Lean definitions. Every labelled result of a work (theorem, lemma, proposition, corollary),
  and every numbered formula or unlabelled claim that the work cites later, is stated with a `sorry` proof by design:
  these files state the literature, they do not prove it.
- An item already in the project or in Mathlib is not restated. The module docstring of each file indexes every item
  of the work in the work's order and points to the existing declaration (`exists:`).
- One namespace per work (`Gehring1978`, …) and one file per section of the work (`References/<Key>/…`). The work's
  root file `References/<Key>.lean` gives the source, coverage, conventions and counts. Notions shared by several works
  live in `References/Common/`, namespace `References`.
- The counts of `LiZhongQC` above are unaffected: `Audit.lean` counts only `LiZhongQC.*`. For `References`, run
  `lake env lean AuditRefs.lean`. It prints, per work, the definitions, the statements, and every definition that
  depends on `sorry`; that list must be empty.

| Work | Root module | New definitions | New statements | `exists` | Installed |
|---|---|---|---|---|---|
| F. W. Gehring, *Spirals and the universal Teichmüller space*, Acta Math. 141 (1978) | `References.Gehring1978` | 19 (+4 helpers) | 16 (3 proved 2026-10-06: §2 (5), Propositions 1, 2) | 8 | 2026-09-28 |
| O. Lehto, K. I. Virtanen, *Quasiconformal Mappings in the Plane*, 2nd ed. (1973): complete (Chapters I–VI) | `References.LehtoVirtanen1973` | 189 (helpers included) | 391 (93 proved: `eq2_6_5` 2026-09-30; 25 on 2026-10-04 in Ch. I §2.4 and Ch. II §2 (complete), §3, §6, §7; 62 on 2026-10-06, 4 on 2026-10-08 (the reflection principle, §8; existence of canonical maps of quadrilaterals and the Riemann mapping theorem, both now in §5) and 1 on 2026-10-09 (Theorem 7.1: `M(B)/K ≤ M(B′) ≤ K M(B)`, §7) in Ch. I §1.1, §1.2 (invariance of domain), §3 (`kqc_inv`, `kqc_comp`, conformal ⇒ 1-q.c., now in §5), §5, §9 (incl. `thm1_9_1`), Ch. II §3, §6 (incl. the sharp Beurling–Ahlfors extension `thm2_6_3`), §7 (quasisymmetric ⇔ q.c. boundary values) and §9 (incl. Mori's bound), Ch. III §1, §4, §5, §7 (Egorov, Fubini, Lusin, module monotonicity), Ch. IV §1, §2 (analytic definition), §4 and §5 (incl. the uniqueness theorem), Ch. V §1 (existence theorem, mapping theorem), via the LV↔LiZhongQC bridges in both directions) | 126 | 2026-09-28 |
| O. Lehto, *Univalent Functions and Teichmüller Spaces*, GTM 109 (1987): complete (Chapters I–V) | `References.Lehto1987` | 161 (helpers included) | 376 | 242 | 2026-10-06 |
| K. Astala, F. W. Gehring, *Crickets, zippers, and the Bers universal Teichmüller space*, Proc. AMS 110 (1990) | `References.AstalaGehring1990` | 19 | 14 (1 proved 2026-10-06: Möbius invariance of T̄) | 3 | 2026-09-28 |
| Ch. Pommerenke, *Boundary Behaviour of Conformal Maps* (1992): complete (Chapters 1–11) | `References.Pommerenke1992` | 223 (helpers included) | 420 (29 proved: 17 on 2026-10-04/05 in Ch. 1 §1.2, §1.3, §1.5; 12 on 2026-10-06 in Ch. 5 §5.3–§5.6 (quasidisks) and Ch. 9 §9.2–§9.3 (curve families, Fekete points)) | 90 | 2026-09-29 |
| J. B. Garnett, D. E. Marshall, *Harmonic Measure* (2005): Chapters I–VI and Appendices A–D, F–I (of I–X and Appendices A–M) | `References.GarnettMarshall2005` | 180 (helpers included) | 332 (37 proved: 9 on 2026-10-06, Ch. IV §2 uniqueness of extremal metrics and §3 the four rules incl. the serial and parallel rules; 27 on 2026-10-08, Ch. II §2 (2.7), §3 (3.3)–(3.6), Lipschitz ≤ Zygmund norm and Zygmund's exponential integrability of the conjugate, §4 the C^{k+α} inverse-function lemma, Ch. III §2 the logarithmic potential is superharmonic, §3 a Dirichlet-integral estimate, §4 equilibrium-distribution lemmas, Ch. IV §1 conformal invariance, the rectangle and annulus examples, the extremal distance of a quadrilateral and (1.7) d·d* = 1, §3 the symmetry rule, §4 slit rectangles and slit annuli, Ch. V §4 Teichmüller's Modulsatz and (4.1) mod Ω₁ + mod Ω₂ ≤ mod A; 1 on 2026-10-09, Ch. V Theorem 4.1, the stability form of the Modulsatz) | 74 | 2026-09-30 (Ch. I–VI, App. A–D, F–I) |
| S. Katok, *Fuchsian Groups* (1992): Chapters 1–2 (of 1–5) | `References.Katok1992` | 49 (helpers included) | 71 (70 proved, 2026-10-04/06; all but Ch. 1 Theorem 1.4.2 (Gauss–Bonnet); Ch. 2 complete) | 54 | 2026-09-30 (Ch. 1–2) |
| F. P. Gardiner, N. Lakic, *Quasiconformal Teichmüller Theory* (2000): complete (Chapters 1–18) | `References.GardinerLakic2000` | 389 (helpers included) | 368 (126 proved, 242 open; 2026-10-08) | 139 | 2026-09-30 |

Shared layer: `References/Common/ExtendedPlane` (domains and Jordan domains of `ℂ̄`, the finite part of a set of
`ℂ̄`), `References/Common/Quasidisk` (quasidisks of `ℂ̄`), `References/Common/ExtPlaneBorel` (the Borel
σ-algebra of `ℂ̄` as a scoped instance: `open scoped References`) and `References/Common/Subharmonic`
(`EReal`-valued subharmonic and superharmonic functions on open sets of `ℂ`) and `References/Common/RiemannSurface`
(`IsRiemannSurface`, the propositional form of the project's Riemann-surface convention).

Lehto–Virtanen's Chapter I definitions (homeomorphisms, Jordan arcs, orientation and sense-preserving maps, conformal
maps and quadrilaterals of `ℂ̄`, the maximal dilatation, `K`-quasiconformal maps) are the reference definitions for
maps of domains of `ℂ̄`; later works reuse them. Statements that are false as printed are stated in corrected form and
listed under *Corrections* in the work's root file.

## Sources and caveats

* All chapters (§1–§36) were formalized from the text of the book; the historical notes at the
  end of Chapter 9 contain no mathematical statements and are not represented.
* **Corrections.**
  * §11–§12 (`eq11_15`, `zygmund_calderon`, `eq11_17`, `thm12_1_smooth_case`, 2026-09-14): four statements about
    `C₀^∞` functions were written with `ContDiff ℝ ⊤`, which in current Mathlib means real-analytic, so together
    with compact support they only covered the zero function. They now use `C^∞` (see *Modelling conventions*).
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
  * §30.4 ((30.1), `eq30_1_generators_determined`, 2026-09-26, user decision): the statement was **false**, for
    orientation reasons.
    - The mirror representation `J ρ J` (`J = diag(1, −1)`) has the same traces as `ρ` but is never
      `SL(2, ℝ)`-conjugate to it (Lean refutation, conditional on one faithful cocompact Fuchsian surface group).
    - Traces cannot see orientation, and the book works inside `T(S)` of one oriented surface.
    - Restoring only the (27.5) normalization of the last generator pair (`δ_g(z) = λz`, `λ > 1`; `γ_g(1) = 1`)
      does **not** repair it: conjugating by `diag(1/q, 1)` gives a mirror that satisfies the normalization.
    - Fix: the normalization plus the orientation clause that `1` is the **attracting** fixed point of `γ_g`.
      - A convention check (argument + numerics on the regular octagon group) showed that this holds exactly
        for correctly oriented systems (`a_g · b_g = +1`), so the hypothesis is not vacuous.
      - The conclusion is `ρ₂ = ±ρ₁` elementwise.
    - The statement remains unproved (trace rigidity).
  * §31.1–§31.2 (`IsClosedDiscIn`, `IsAdmissibleQD`, 2026-09-27, user decisions): the admissible quadratic
    differentials were defined with three defects, and five statements of §31 were **false** as a result.
    - Chart images: the conditions used `chartAt x '' A`, which contains the chart's arbitrary values off its source.
      A stray value on a puncture forbade the pole there (and forced a zero), so the dimension statements failed
      for `n ≥ 1` (Lean refutations). Fix: `(chartAt x).target ∩ (chartAt x).symm ⁻¹' A`.
    - Holes: nothing constrained `q` inside the removed discs, so `Q̃(S₀)` was infinite-dimensional (`finrank = 0`)
      whenever `m ≠ 0` (Lean refutation). Fix: `q = 0` over `interior (D j)`.
    - Boundary regularity: the hole boundaries were only `C¹`. For a `C¹` curve whose tangent is not
      Dini-continuous the conformal collar map has unbounded derivative at a point, and continuity in the charts
      of `X` then cuts one dimension off `Q̃(S₀)` (analytic argument, via the failure of Kellogg–Warschawski).
      Fix: `C^∞` boundaries (the book's "smooth").
    - False before the fixes: `thm31_1_admissibleQD_finrank`, `eq31_1_double_finrank`,
      `admissibleQD_complex_finrank` (dimension conjunct), `admissibleQD_symmetric_extension`,
      `admissibleQD_double_decomposition`. All five remain unproved (they need Riemann–Roch).
    - `admissibleQD_boundary_trajectories` is proved, but formalizes only the boundary half of the book's remark,
      pointwise (user decision: no restatement). The claim that one horizontal trajectory ends at a simple pole is
      not stated.
    - Recorded faithfulness gap: `admissibleQD_symmetric_extension` and `admissibleQD_double_decomposition`
      assert that some injective map, resp. some involution, exists, not that the book's reflection has the
      property; they should be restated before anyone proves them by counting dimensions.
  * §32 (2026-09-27, user decisions): one definition and four statements were corrected.
    - `pullbackQD` read `q` in the chart at `ι x` even where the image point had left that chart, and was not `0`
      off the chart target. In some legal atlases no nonzero pull-back was a quadratic differential, so no
      admissible Teichmüller map existed (Lean refutations of `admissibleQDInterior_holomorphic`,
      `thm32_2_existence_gn`, `thm32_4_existence_gnm`, `markedFiniteType_teichmuller_data`). Fix: the chart at the
      image point and `0` off the target, as in §29.1. `admissibleQDInterior_holomorphic` is now proved.
    - `exists_branched_double_cover` was **false** at `(g, n) = (0, 0)`: the genus `2g + n − 1` is `0` in `ℕ`, and
      the sphere has no connected double cover. Fix: the hypothesis `g ≠ 0 ∨ n ≠ 0`.
    - `lift_teichmullerMap_double_cover` was **false**: the covers were not tied to the punctures (constant maps
      passed `ncard ≤ 2`, since an infinite fibre has `ncard = 0`, and the two covering surfaces need not even be
      homeomorphic). Fix: `pr₀` is the double cover branched exactly at the punctures of `F₀`, and the target cover
      and the lifting relations are produced in the conclusion.
    - `symmetric_extension_properties` was **false** for the exceptional types `(0,0,1)`, `(0,0,2)`: an
      orientation-reversing map is homotopic to the identity on the disc, but not on the doubled sphere. Fix: the
      hypothesis `¬ IsExceptionalType g n m` (the book's setting in §32.2).
    - `eq32_3_teichmuller_commutes_reflection` was **false** for `n ≥ 1`: it used the closed Schottky double, which
      forgets the `2n` punctures (pushing a puncture gives a counterexample). Fix: it is stated, as in the book, on
      the punctured doubles of type `(2g + m − 1, 2n, 0)`, for an admissible Teichmüller map homotopic to the
      restriction of `f^d`.
    - Recorded faithfulness gap: the second conjunct of `teichSpaceFiniteType_ball` is a bare bijection of the ball
      onto `T_{g,n,m}`, not tied to the Teichmüller data `(k, ω)`.
  * `dcModulus_mul_dirichletIntegral` (`Lemmas/DirichletModulus`, not a book statement; 2026-09-27, user decision): the
    identity `mod(B) · D[u] = 2π` was **false** for unbounded `B`.
    - For `B = ℍ ∖` (a closed disc), adding to the harmonic measure a positive harmonic function that vanishes on the
      whole finite boundary keeps every hypothesis. Its Dirichlet integral is infinite, Lean's integral of a
      non-integrable function is `0`, and the identity read `0 = 2π`.
    - Fix: the hypothesis `Bornology.IsBounded B`. The identity is now proved, through the annulus uniformization
      `thm2_1_canonical_form_annulus`.
  * `IsPrincipalPoint` (`Lemmas/Caratheodory`, prime ends; 2026-09-27, user decision): the definition was wrong.
    - It asked, for each `ε > 0`, only for one crosscut (of any index) of some chain representing the prime end inside
      `B(w, ε)`. The first crosscuts of a chain can be changed without changing the prime end, so every point of the
      impression was "principal" (a comb domain gives an explicit example), and `caratheodory_primeEnd_principal` was
      false.
    - Fix: the standard definition. `w` is principal if some chain representing the prime end has crosscuts that
      eventually lie in every ball around `w`.
    - Both statements that use the definition remain unproved (prime-end theory).

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
    - Status (2026-09-26): all seven companions are proved and axiom-clean, in `Lemmas/UniformizedUniqueness.lean`.
      Among them is Teichmüller's uniqueness theorem for surfaces given as `ℍ/Γ`
      (`thm26_2_uniqueness_of_uniformization`).
    - Also proved (2026-09-26), in `Lemmas/UniformizedTeichmuller.lean`: companions of
      `lemma27_3_dilatation_bound`, `lemma27_1_injective` and `teichSpace_deformation_bijection`.
      - Teichmüller's existence theorem is proved in the variant `thm27_2_existence_qc_of_uniformization` (user
        decision), for homotopy classes containing a quasiconformal map.
      - The book's `thm27_2_existence` covers every homotopy class of homeomorphisms, and so needs S24's
        `exists_qc_in_homotopy_class` as well.
    - Also proved (2026-09-27), in `Lemmas/UniformizedTeichmuller.lean`: companions of
      - `teichDistance_eq_of_eq_zero` (the third metric axiom of `d_T`);
      - `hurwitz_finite` (the automorphism group of a closed surface of genus `g > 1` is finite);
      - `modAction_properly_discontinuous`;
      - `thm30_3` (the discontinuity of `Mod(S₀)`);
      - `thm30_4_hausdorff` (`R_g` is Hausdorff).
    - Also proved (2026-09-27), in `Lemmas/UniformizedTeichmuller.lean`: the companion of (32.2)
      `eq32_2_symmetric_lift` (the lifted Teichmüller map commutes with the covering transformations of the double
      covers), for a target surface given as `ℍ/Γ`.
* **Notation.** `ω` is Mathlib's notation for analytic smoothness (`IsManifold 𝓘(ℂ) ω S`), so the
  quadratic differential `ω` of the book is called `q` in Lean; `π` is `Real.pi`, so projections
  are called `p`, `pr`.

## License

Copyright 2026 Wu Xiaobin. Licensed under the Apache License, Version 2.0 (see `LICENSE`).

The vendored folders keep their upstream licenses and notices: `JordanCurveTheorem/`, `Jacobians/`, `RMT4/`,
`RiemannDynamics/` and the subfolders of `LiZhongExternal/` (see the `LICENSE*`, `NOTICE*` and `PROVENANCE.md` files
in each).
