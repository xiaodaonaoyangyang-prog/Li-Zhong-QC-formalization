import References.AstalaGehring1990.S1_Introduction
import References.AstalaGehring1990.S2_ClosureOfT
import References.AstalaGehring1990.S3_ComplementOfAQuasiarc
import References.AstalaGehring1990.S4_Examples
import References.AstalaGehring1990.S5_ACounterexample

/-!
# Astala–Gehring 1990: *Crickets, zippers, and the Bers universal Teichmüller space*

K. Astala, F. W. Gehring, *Crickets, zippers, and the Bers universal Teichmüller space*, Proc. Amer. Math. Soc. 110
(1990), 675–687. Statement-level formalization: definitions are genuine, and the paper's results are theorem
statements with `sorry` proofs.

**Source:** `refs\Astala-CricketsZippersBers-1990.pdf-e9a341c8-e720-42b7-82f7-0ddefa331439\full.md` (MinerU OCR, 595
lines, one folder).

**Coverage:**
- The paper is complete: §1 Introduction, §2 Closure of `T`, §3 The complement of a quasiarc, §4 Examples, §5 A
  counterexample, and the references.
- There are no gaps. OCR defects inside statements: "`f(α) ⊂ α` for some `a`" in Corollary 4.5 means the homothety
  `f(z) = az` of l. 335.

**Conventions and modelling:**
- **Disc model.** The paper uses the unit disc `U`. The project's universal Teichmüller space is in the lower
  half-plane and it has no disc-model Bers space, so §1 defines the paper's objects:
  - `E` (`spaceE`, with the norm (1.1) `normU`), `S`, `T`, and the closure `T̄ = closureE setT`;
  - elements are functions on `ℂ` vanishing off `U`.
- **The domain norm.** The density `ρ_D` of curvature `-4` and the norm (2.1) are `Gehring1978.hypDensity` and
  `Gehring1978.hypNorm` (the same normalization).
- **"Conformal mapping of `U`"** is `LiZhongQC.IsUnivMero`, with image `LiZhongQC.meroToExt f '' U` in `ℂ̄`.
- **Maps of domains of `ℂ̄`** use the Lehto–Virtanen reference notions (FOUNDATIONS.md), all sense preserving:
  - (`K`-)quasiconformal maps, including self-mappings of `ℂ̄` (`G = univ`):
    `LehtoVirtanen1973.IsKQuasiconformal`, `LehtoVirtanen1973.IsQuasiconformalMap`;
  - homeomorphisms: `LehtoVirtanen1973.IsHomeoOn`;
  - arcs: `LehtoVirtanen1973.IsClosedJordanArc`, `LehtoVirtanen1973.IsArcFromTo`.
  A "quasiconformal extension to `ℂ̄`" of `f` is such a self-mapping agreeing with `f` in `U`.
- **Quasidisks of `ℂ̄`** are the shared `References.IsQuasidiskExt` (new file `References/Common/Quasidisk.lean`,
  delivered with this work).
- **Disks.** A "disk `B` in `D`" is an open euclidean disk, as in the proofs.
- **Lines** are the euclidean lines of `ℂ`.
- **`s`-quasisymmetry** includes injectivity (Väisälä's embeddings) and is stated with its denominator cleared.
- **Acute exterior angles** mean outward normals with negative inner product.
- **Interlocking sequences** are indexed from `1`, and their diameters are taken in `ℝ≥0∞`.
- **Corrections.**
  - [CORRECTION] Lemma 3.8 has an added hypothesis: `g` is sense preserving. Literally, under the convention of l. 49,
    it fails for the reflection `z ↦ z̄` of a disk. The only application, in the proof of 3.1, satisfies the
    hypothesis.
  - [CORRECTION] Theorem 4.3 has an added hypothesis: `∞ ∉ α`, or `∞` is an endpoint of `α` (the cases of the
    proof, l. 289). With `∞` an interior point it is false (a self-similar stepped arc whose image under `1/z`
    is a graph in no direction; see the docstring). Corollary 4.5 is unchanged: under its homothety hypothesis `∞`
    is not an interior point.
- **Remarks and unlabelled claims kept as items (DESIGN §3):**
  - Remark 2.3 (`rem2_3`, used in the proofs of 2.4 and 3.1);
  - the Möbius invariance of `T̄` (l. 109, `isInTbar_of_mobius`, cited in the proof of 2.4; U+).
- **Examples.** Example 4.12 is not an item (an example), though it is the paper's explicit domain in `S ∖ T̄`.

**Counts** (items of the paper; no helper definitions):

| File | new definitions | new statements | `exists` | omitted | deferred |
|---|---|---|---|---|---|
| `S1_Introduction` | 5 | 0 | 1 | 0 | 0 |
| `S2_ClosureOfT` | 1 | 4 (Remark 2.3, 1 unlabelled) | 2 | 0 | 0 |
| `S3_ComplementOfAQuasiarc` | 3 | 4 | 0 | 0 | 0 |
| `S4_Examples` | 4 | 4 | 0 | 0 | 0 |
| `S5_ACounterexample` | 6 | 2 | 0 | 0 | 0 |
| total | 19 | 14 | 3 | 0 | 0 |

The shared layer file `References/Common/Quasidisk.lean` adds one definition, `IsQuasidiskExt`, delivered with this
work.
-/
