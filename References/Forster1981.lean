import References.Forster1981.Ch01.S01_DefinitionOfRiemannSurfaces
import References.Forster1981.Ch01.S02_ElementaryPropertiesOfHolomorphicMappings
import References.Forster1981.Ch01.S03_HomotopyOfCurvesTheFundamentalGroup
import References.Forster1981.Ch01.S04_BranchedAndUnbranchedCoverings
import References.Forster1981.Ch01.S05_TheUniversalCoveringAndCoveringTransformations
import References.Forster1981.Ch01.S06_Sheaves
import References.Forster1981.Ch01.S07_AnalyticContinuation
import References.Forster1981.Ch01.S08_AlgebraicFunctions
import References.Forster1981.Ch01.S09_DifferentialForms
import References.Forster1981.Ch01.S10_TheIntegrationOfDifferentialForms
import References.Forster1981.Ch01.S11_LinearDifferentialEquations
import References.Forster1981.Ch02.S12_CohomologyGroups
import References.Forster1981.Ch02.S13_DolbeaultsLemma
import References.Forster1981.Ch02.S14_AFinitenessTheorem
import References.Forster1981.Ch02.S15_TheExactCohomologySequence
import References.Forster1981.Ch02.S16_TheRiemannRochTheorem
import References.Forster1981.Ch02.S17_TheSerreDualityTheorem
import References.Forster1981.Ch02.S18_FunctionsAndDifferentialFormsWithPrescribedPrincipalParts
import References.Forster1981.Ch02.S19_HarmonicDifferentialForms
import References.Forster1981.Ch02.S20_AbelsTheorem
import References.Forster1981.Ch02.S21_TheJacobiInversionProblem

/-!
# Forster, *Lectures on Riemann Surfaces* (1981)

O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, New York 1981 (translated by
B. Gilligan). Statement-level formalization: genuine definitions, every result of the book stated with a `sorry` proof;
results already in Mathlib, the project or the References are passed with an `exists:` pointer in the file's item index.

## Sources

The Mathpix text `full.md` of `Lectures on Riemann Surfaces (Otto Forster) (…)\b77137c6-…` (cited `F1:<line>`), whose
text ends in the middle of §24, and the second OCR `…\f2e2b440-…` (cited `F2:<line>`), which repeats §24 from the
distribution examples on and continues with §25 ff. Doubtful formulas were checked against the page-image crops of the
first OCR.

## Coverage

Delivered so far (Part A): Chapter I *Riemann surfaces*, §1–§11, one file per section in book order: §1 Definition of
Riemann surfaces, §2 Elementary properties of holomorphic mappings, §3 Homotopy of curves, the fundamental group,
§4 Branched and unbranched coverings, §5 The universal covering and covering transformations, §6 Sheaves, §7 Analytic
continuation, §8 Algebraic functions, §9 Differential forms, §10 The integration of differential forms, §11 Linear
differential equations. Every numbered definition, theorem, lemma, corollary, example and numbered paragraph is an item;
exercises are not items.

Delivered (Part B): Chapter II *Compact Riemann surfaces*, §12–§21, one file per section in book order (`Ch02/`): §12 Cohomology
groups, §13 Dolbeault's lemma, §14 A finiteness theorem, §15 The exact cohomology sequence, §16 The Riemann–Roch theorem,
§17 The Serre duality theorem, §18 Functions and differential forms with prescribed principal parts, §19 Harmonic
differential forms, §20 Abel's theorem, §21 The Jacobi inversion problem. Chapter III (§22–§31) and the appendices are not
covered.

## Standing conventions and their modelling (leader calibration of Part A, rulings A0.1–A0.12)

- **Riemann surfaces** are Mathlib charted spaces over `ℂ`, `X : Type`, with the binders `[TopologicalSpace X]`
  `[T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]`; the bundle `References.IsRiemannSurface` is
  used in existential positions. Holomorphic maps are `MDifferentiable 𝓘(ℂ) 𝓘(ℂ)`; the complex structure is the
  maximal atlas (`IsManifold.maximalAtlas 𝓘(ℂ) ω X`). The Riemann sphere is the shared `References.RiemannSphere`
  (`Common/RiemannSphere.lean`: an `abbrev` of `LiZhongQC.ExtPlane = OnePoint ℂ`; its two charts and the proved `IsManifold`
  instance are `scoped` instances, active under `open scoped References`).
- **Tori** (1.5(d), 2.12–2.13, 5.7(c), 10.14) are the predicate `IsTorusProjection L π` on a Riemann surface `X`
  (`π : ℂ → X` holomorphic covering whose fibres are the cosets of the lattice `L.lattice`), the fallback (B) of A0.8: the
  quotient `ℂ/Γ` as a manifold would need an `IsManifold` instance on `AddAction` quotients that Mathlib does not
  provide for `ω`; the statements hold for every surface carrying such a projection.
- **Meromorphic functions** `𝓜(X)` are the subalgebra `meroFun X` of the germs along `Filter.codiscrete X` of functions
  which are meromorphic in every chart; being a field is the statement `rem1_16_b` (so there is no `Field` instance).
  The algebra structure on germs (`germAlgebra`) is `scoped`.
- **Sheaves** are `TopCat.Sheaf` built with `TopCat.subsheafToTypes` from the generic `pointwiseLocalPredicate`
  (`sheafO`, `sheafOStar`, `sheafM`, `sheafMStar`, `sheafLocConst`, `sheafE`); the étalé space is Mathlib's
  `TopCat.Presheaf.EtaleSpace`. Sheaves of forms (`ℰ^(1)`, `ℰ^{1,0}`, `ℰ^{0,1}`, `Ω`, `𝓜^(1)`, `ℰ^(2)`) are
  module-valued presheaves built in Part B by the generic `localRepPresheaf`.
- **Fundamental group**: Mathlib's `FundamentalGroup` (opposite multiplication to Forster's); every statement affected is
  insensitive to the order (isomorphisms, homomorphisms into commutative groups, factors of automorphy indexed by
  `Deck(X̃/X)`). "The universal covering" quantifies over every universal covering `p : X̃ → X` with `X̃` a Riemann
  surface and `p` holomorphic.
- **Differential forms** (A0.5, variant B): the cotangent spaces `T_a^(1) = 𝔪_a/𝔪_a²`, `d_a f` and `T_a^(2) = Λ² T_a^(1)`
  are faithful (9.2–9.5, 9.11); the working forms are the coefficient pairs `Form1 X` of `dz`, `dz̄` (and the coefficient
  `Form2 X` of `dz ∧ dz̄`) in the preferred charts, with the transformation laws of `LiZhongQC.IsDiffFamily` as the
  predicates `Form1.IsForm`, `Form2.IsForm`; `∂/∂z`, `∂/∂z̄` are `LiZhongQC.dz`, `LiZhongQC.dzbar`. Normalizations
  recorded: `dz ∧ dz̄ = −2i dx ∧ dy`, `ω = f dx ∧ dy = (i/2) f dz ∧ dz̄` and `∬ ω := ∬ f dx dy`, `d′d″f = f_{zz̄} dz ∧ dz̄ =
  (1/2i)(f_xx + f_yy) dx ∧ dy`.
- **Integrals and residues** are relations with the book's well-definedness claims as separate statements
  (`HasCurveIntegralRS`, `HasClosedFormIntegral`, `HasIntegral2`, `HasResidue`); the value functions `curveIntegralRS`,
  `period` take the junk value `0` where the relation has no solution.
- **Matrix exponential** is `NormedSpace.exp`; `z^ρ := exp (ρ log z)` on the universal covering of the punctured disc.

## Part B conventions (leader calibration of Part B, rulings B0.1–B0.14)

- **Sheaves of modules and `H¹`** (B0.1, B0.2, B0.14): a sheaf of `R`-modules on `X` is a presheaf
  `F : TopCat.Presheaf (ModuleCat.{0} R) (TopCat.of X)` (with `F.IsSheaf` in the general statements). The universe of
  `ModuleCat` is pinned to `0`, as `R : Type` and `X : Type`, so that the Čech groups lie in `Type`. The cochain groups
  `CechC0/1/2 F U` are Pi-modules over an arbitrary family of opens (the family need not cover; §14 uses non-covering
  families). `H¹(Y, F)` is `H1 F Y`, the inductive limit of the `H¹(𝔘, F)` over the coverings `𝔘 : CechCover X Y`, presented as
  the quotient of `⨁ Z¹(𝔘)` by the relations of refinement and of coboundaries (`cechRel`); it lies in `Type 1` because a
  covering carries its index type, and it is an `abbrev` so that the `Module` instances resolve. A quotient of the direct sum
  over the subtypes `Z¹(𝔘)` does not synthesize its instances, so `H1` is realised as the image of `⨁ Z¹` in `⨁ C¹ ⧸ cechRel`
  (the same module, as the relations lie in `⨁ Z¹`). `finrank`, `≃ₗ` and `Module.Dual` are unaffected by the universe.
- **The concrete sheaves** `ℰ, ℰ^(1), ℰ^{1,0}, ℰ^{0,1}, ℰ^(2), ℂ, ℤ, 𝒪, 𝒪*, Ω, 𝓩, 𝓜, 𝓜^(1), 𝒪_D, Ω_D, ℂ_P` are built by one
  generic `localRepPresheaf R p n` (sections over `U` are the representatives with the pointwise property `p` at every point
  of `U`, modulo those with the pointwise property `n`); the sheaf definitions `mod…` are `abbrev`s so that `IsInducedBy`
  unifies with it. They are module-valued, next to the type-valued sheaves of Part A (§6, §9), which have no module structure.
  The functor laws of `localRepPresheaf` are the only proofs in Part B (`rfl`-level, B0.2 (A)).
- **Maps between cohomology groups and sheaves** (B0.3) are relations: `IsInducedBy α Φ` (a sheaf homomorphism induced by a
  map of representatives), `IsH1Induced` (`α¹`), `IsConnectingHom` (`δ*`), `IsResH1` (`Res`), `IsFormTimesClass` and
  `IsSerreDuality` (the Serre pairing); statements say "there is a map with the property" or "every map with the property". The
  book's "well defined" sentences are `∃!` statements. Sheaf homomorphisms are morphisms of presheaves of modules (`F ⟶ G`);
  exactness is stalkwise (`TopCat.Presheaf.stalkFunctor`, B0.5).
- **Forms on a set**: Part A's `Form1.IsForm` is global, so the sheaves of forms use the transformation law on a set,
  `Form1.IsFormOn` (with `Form2.IsFormOn`, `Form1.IsType10On`, `Form1.IsType01On`, `Form1.VanishOn`).
- **Analysis** (B0.4, §13–§14): smoothness is `ContMDiff … ∞`; `‖f‖_{L²(D)}` is `eLpNorm f 2 (volume.restrict D)` in `ℝ≥0∞`;
  "closed subspace" is sequential closedness; `V ⋐ U` is `IsRelCompactIn`; cochain `L²` norms read representatives through
  `Quotient.out`; `genus X := finrank ℂ (H1 (modO X) ⊤)` (junk `0` never occurs on a compact surface; near miss
  `LiZhongQC.HasGenus`, a topological definition).
- **Divisors** (B0.6): `Div X` is Mathlib's `Function.locallyFinsupp X ℤ` (locally finite support, as the book needs; near miss
  `LiZhongQC.Divisor`, a finitely supported function); `divSingle P n` is the point divisor (Mathlib's
  `Function.locallyFinsuppWithin.single` with classical decidability); `ord_a f` is `LiZhongQC.ordRS`; `(f) = D` is the relation
  `IsDivisorOf` (a function would need the identity theorem); `divDeg D := ∑ᶠ x, D x` (junk `0` only for infinite support, never
  on a compact surface).
- **Duality, Hurwitz, ℙᴺ** (B0.7): Riemann–Hurwitz is stated in `ℚ`; `b(f, x) := (multiplicity f x).toNat − 1`; ℙᴺ is Mathlib's
  `Projectivization ℂ (Fin (N + 1) → ℂ)` with charts defined through `.rep`, and "holomorphic into ℙᴺ" is chartwise with
  `IsOpen (F⁻¹ U_j)` as a conjunct (ℙᴺ is not given a topology).
- **Prescribed principal parts and harmonic forms** (B0.8, B0.9): Mittag-Leffler distributions are at the level of
  representatives; the Wronskian is the determinant of `iteratedDeriv` (near miss `Polynomial.wronskian`); the conjugate `ω̄`, the
  star `*ω` and the real part `Re ω` of a 1-form are the relations `Form1.IsConjOf`, `Form1.IsStarOf`, `Form1.IsRealPartOf`;
  `Harm¹(X)` and `Ω̄(X)` are spans; the scalar product `⟨ω₁, ω₂⟩` occurs only inside `HasIntegral2` (`FormsOrthogonal`).
- **Abel and Jacobi** (B0.10, B0.11): `Chain1 X := C(unitInterval, X) →₀ ℤ`; `∂c = D` is the relation `IsChainBoundary`;
  `∫_c` is `HasChainIntegral`, built on Part A's `HasClosedFormIntegral`. Forster's lattice definition is the new
  `IsLattice` (Mathlib's `IsZLattice` is a characterization, so 21.1 would be a tautology); `Per(ω₁, …, ω_g)` is `periodLattice`, an
  `AddSubgroup.closure` of Part A `period` vectors; `Jac`, `Pic`, `Pic₀` are the quotients `jacobiVariety`, `picardGroup`,
  `picardGroup0`; `Φ`, `j`, `J` are existential with their
  defining property.
- **Names** (B0.12): an unnumbered theorem or lemma inside the numbered paragraph `n.m` is `thmN_M` / `lemmaN_M`; claims of a
  numbered paragraph are `paraN_M`, of a remark `remN_M`, of an example `exampleN_M`. Names of the book that are illegal in Lean
  identifiers are renamed as in Part A, and the book's binder `ω` is `s` in Lean because `ω` is a scoped token.

## Corrections and readings

Each marked in the declaration's docstring or, for proof-only slips, here:
- 3.4(ii): "inverse curve `u⁻` from `a` to `b`" is read from `b` to `a` [misprint].
- 4.23: "`m = Σ_{x ∈ p⁻¹(c)} v(f, x)`" is read with `f⁻¹(c)` [misprint].
- 2.10 proof: "Riemann's Removable Singularities Theorem (2.8)" is (1.8); 10.15 proof: "By (10.3), F has summands of
  automorphy 0" is (10.13) [misprints, proofs only].
- 11.10: "`w′ = (1/z) B w*`": the stray mark is a print speck; read `w′ = (1/z) B w` [crop checked].
- Proof of 10.13(a): "`= F(z₀) − F(σ⁻¹(z₀)) = −a_σ`" with "`−a_σ := σF − F`" gives `+a_σ`; the statement (summands =
  periods) is consistent with `+a_σ` [sign slip in the proof].
- 9.13 [reading]: the independence of `d′ω = Σ d′f_k ∧ dg_k`, `d″ω = Σ d″f_k ∧ dg_k` of the representation fails in general.
  Counterexample: `ω = dg` with `g = |z|²`. The representation `(f, g) = (1, g)` gives `d′ω = d′1 ∧ dg = 0`, while
  `dg = g_z dz + g_z̄ dz̄ = z̄ dz + z dz̄` (representation `(g_z, z), (g_z̄, z̄)`) gives `d′ω = d′g_z ∧ dz + d′g_z̄ ∧ dz̄ =
  g_{z̄z} dz ∧ dz̄ ≠ 0` (here `g_{zz̄} = 1`). The independence holds for representations `ω = f₁ dz + f₂ dz̄`, and
  `Form1.dHol`, `Form1.dBar` are defined by the chart formulas (`d′(a dz + b dz̄) = b_z dz ∧ dz̄`, `d″ = −a_z̄ dz ∧ dz̄`),
  for which 9.14 (i)–(iv) hold as printed. (Confirmed by the leader against F1:2609–2648.)
- 17.7 [misprint]: the hypothesis `ω ∈ H⁰(X, Ω_{−D})` is read `ω ∈ H⁰(X, Ω_{−D′})` (`ι_{D′}` is defined only on
  `H⁰(Ω_{−D′})`; the conclusion and the proof need this reading).
- 20.1 [misprint]: "the product `f₁/f₂` is not defined" is read "`f₁f₂`".
- 16.12 [reading]: "Riemann surface of genus `g`" means a *compact* Riemann surface.
- OCR only (crops checked): 21.2 `∫_x` = `∫_α`; `D′ ∈ D`, `Y ∈ X` = `⋐` (14.3, 14.9, 14.12); `t^u_R` = `t^𝔘_𝔙` (12.2);
  `δ^{(1)}(X)` = `ℰ^{(1)}(X)` (15.15); `t_D` = `ι_D` (17.7 diagram); `𝕆_{D′}` = `𝒪_{D′}` (21.9 proof).
- Proof-only slips: 13.1 proof `∂f/∂ζ` for `∂f/∂ζ̄` (three times); 14.3 proof `ρ^{2n+2}` for `ρ^{2ν+2}` (printed so);
  14.7 proof `ξ + ση₀` for `ξ + δη₀`; 21.4 proof `ω_j` for `ω_i`; 17.20 `U_n` for `U_N`.

## Counts

| Chapter | new definitions (incl. helpers) | new statements | `exists` bullets |
|---|---|---|---|
| I §1 Definition of Riemann surfaces | 9 | 7 | 8 |
| I §2 Elementary properties of holomorphic mappings | 2 | 10 | 4 |
| I §3 Homotopy of curves, the fundamental group | 1 | 3 | 15 |
| I §4 Branched and unbranched coverings | 8 | 16 | 7 |
| I §5 The universal covering and covering transformations | 8 | 12 | 3 |
| I §6 Sheaves | 8 | 4 | 5 |
| I §7 Analytic continuation | 5 | 6 | 0 |
| I §8 Algebraic functions | 7 | 22 | 0 |
| I §9 Differential forms | 41 | 12 | 1 |
| I §10 The integration of differential forms | 16 | 25 | 1 |
| I §11 Linear differential equations | 17 | 15 | 2 |
| II §12 Cohomology groups | 45 | 12 | 0 |
| II §13 Dolbeault's lemma | 4 | 5 | 0 |
| II §14 A finiteness theorem | 12 | 15 | 0 |
| II §15 The exact cohomology sequence | 20 | 19 | 2 |
| II §16 The Riemann–Roch theorem | 10 | 11 | 2 |
| II §17 The Serre duality theorem | 19 | 21 | 0 |
| II §18 Functions and differential forms with prescribed principal parts | 10 | 13 | 0 |
| II §19 Harmonic differential forms | 12 | 21 | 0 |
| II §20 Abel's theorem | 6 | 8 | 0 |
| II §21 The Jacobi inversion problem | 8 | 7 | 0 |
-/
