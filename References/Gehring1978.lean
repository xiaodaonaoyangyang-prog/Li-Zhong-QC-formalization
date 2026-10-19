import References.Gehring1978.S1_Introduction
import References.Gehring1978.S2_Spirals
import References.Gehring1978.S3_ProofOfTheorem2

/-!
# Gehring 1978: *Spirals and the universal Teichmüller space*

F. W. Gehring, *Spirals and the universal Teichmüller space*, Acta Math. 141 (1978), 99–113. Statement-level
formalization: definitions are genuine, and the paper's results are theorem statements with `sorry` proofs.

**Source:** `refs\Spirals and the universal Teichmüller space.pdf-602096dc-59ef-4c94-97de-d7b253b98c77\full.md`
(MinerU OCR, 654 lines, one folder).

**Coverage:**
- The paper is complete: §1 Introduction, §2 Spirals, §3 Proof of Theorem 2, and the references.
- There are no gaps or seams.
- Three OCR errors are corrected. `e^{(-a+t)t}` in §1 (twice) is read as `e^{(-a+i)t}`, as in §3. `Ū` in Lemma 7 is
  read as `ℂ̄`, as in its proof.

**Conventions and modelling:**
- **Domains of `ℂ̄`.** Domains are subsets of `ℂ̄ = LiZhongQC.ExtPlane`; the paper's own `D = ℂ̄ - γ` contains `∞`.
  The project's density, norm and Jordan-domain notions are for plane domains only, so §1 defines the paper's
  versions: `hypDensity` `ϱ_D`, `hypNorm` `‖φ‖_D`, `IsConformalExt`, `imageExt` and `IsHypSimplyConnectedExt`.
  The generic notions (domain and Jordan domain of `ℂ̄`, finite part) come from the shared layer
  `References.Common.ExtendedPlane`: `References.IsDomainExt`, `References.IsJordanDomainExt`,
  `References.finitePart`. They were delivered with this work.
- **Normalization.** Gehring's normalization is kept: `ϱ_D = |g'|/(1 - |g|²)`, of curvature `-4`. So `‖φ‖_D` is four
  times the project's `LiZhongQC.schwarzianNorm` and `LiZhongQC.bersNormL` for plane domains. The pointers of §1 (`B₂`,
  Theorem 1, Corollary) keep the project's norm; no stated constant depends on the factor.
- **"Conformal in `D`"** means univalent meromorphic (values in `ℂ̄`, through `LiZhongQC.meroToExt`). The image
  `f(D)` includes `f(∞)`.
- **Arcs and curvature (§2).**
  - Arcs are embeddings of `(0, ∞)`, and an analytic arc has a regular real-analytic parametrization.
  - The curvature `k = Im(z''/z')/|z'|` is signed, and `dk/ds = (dk/dt)/|z'|`, both in the direction of increasing
    parameter.
  - Rectifiable means an embedding parametrization of bounded variation.
- **Quantifiers (§3).**
  - Lemmas 6 and 9 are stated for `a > 0`; the paper's `a < 1/8π` is needed only in Lemma 8.
  - The limits `f_j(0)` of the Remark after Lemma 6 (`lemma6_remark`) appear as `∃ w, Tendsto …` in the conclusions
    of Lemmas 8 and 9, in place of the bounds `δ₂, δ₃ ≤ δ₁`.
  - In Lemma 8, `b*` is uniform in `f`.
- **Unlabelled claims kept as items (U+, DESIGN §3).** Three are stated, all in `S3_ProofOfTheorem2`:
  - the explicit form of Theorem 2 (§1, l. 69–75, proved in §3), as `thm2_explicit`;
  - the properties of `β` and `D` (§3, l. 447), as `betaCurve_separates`;
  - the limits of the Remark after Lemma 6 (§3, l. 483), as `lemma6_remark`.

**Counts** (items of the paper; helper definitions in parentheses):

| File | new definitions | new statements | `exists` | omitted | deferred |
|---|---|---|---|---|---|
| `S1_Introduction` | 5 (+1) | 1 | 8 | 0 | 0 |
| `S2_Spirals` | 7 (+3) | 8 | 0 | 0 | 0 |
| `S3_ProofOfTheorem2` | 7 | 7 (3 unlabelled) | 0 | 0 | 0 |
| total | 19 (+4) | 16 | 8 | 0 | 0 |

The shared layer file `References/Common/ExtendedPlane.lean` adds 3 definitions, delivered with this work:
`IsDomainExt`, `IsJordanDomainExt` and `finitePart`. The `exists` item "Jordan domain in `ℂ̄`" points to it.
-/
