import References.Miyachi2008.S02_AsymptoticBersMap
import References.Miyachi2008.S03_NecessaryCondition
import References.Miyachi2008.S04_QuasiregularExtension
import References.Miyachi2008.S07_FailureOfDensity
import References.Miyachi2008.S08_ClosureOfImage

/-!
# Miyachi 2008, *Image of asymptotic Bers map* (statement level)

H. Miyachi, *Image of asymptotic Bers map*, J. Math. Soc. Japan **60** (2008), no. 4, 1255–1276
(`refs/Miyachi2008_asymptotic_Bers_map.pdf`, read from the rendered pages; `p. n` are journal pages). Namespace `Miyachi2008`.
Statements only: every definition is genuine, every theorem is `:= by sorry`, results already installed are reused.

**Coverage.** All results of the paper: the necessary condition for an arbitrary Fuchsian group (Prop. 1.1), the characterization
of the image of the asymptotic Bers map for the unit disk (Theorem 1, Props. 4.1–4.2, Corollaries 1–2), the failure of density
(Props. 7.1–7.2, Theorem 2) and the characterization of the closure (Theorems 3–4). The introduction, the notation of §2, the proofs
and the open problems of §9 are not items; Lemmas 4.1, 4.2, 7.1, 8.1 (steps of proofs) and the Remark of §5 are omitted (U−).

**Conventions and modelling.**
(1) *Half-plane model.* The paper's unit disk `D` and `D*` are replaced by `ℍ` and `𝕃 = LiZhongQC.lowerHalf` (Cayley transform; every
  notion is Möbius invariant), and `Γ` is a Fuchsian group `Γ ≤ SL(2, ℝ)` (`LiZhongQC.IsFuchsian`), so that the project's Bers
  embedding `LiZhongQC.bersMapGamma` and the Gardiner–Lakic spaces are used literally; the unit circle `S¹` is `ℝ ∪ {∞}`.
(2) `B(Γ)`, `B₀(Γ)`, the norm: `GardinerLakic2000.cuspFormsL`, `boundedCuspForms0`, `cuspNorm` (curvature `−4`, as in the paper);
  `B̂(Γ) = B(Γ)/B₀(Γ)` is the genuine quotient `bHat` with the quotient norm `hatNorm` and the closure `hatClosure`.
(3) The image `𝒜𝒯_Γ` of the asymptotic Bers map is defined directly as the image of the Bers image in `B̂(Γ)` (`asymBersImage`, (2.3) of the
  paper); the existence and injectivity of the map `AT(D/Γ) → B̂(Γ)` (Earle–Gardiner–Lakic, Earle–Markovic–Šarić) is the theorem `thm2_2_2`.
(4) Developing mappings `f_φ` are locally univalent meromorphic functions with Schwarzian derivative `φ` (`IsDevelopingMap`); statements are
  made for every developing mapping (they differ by Möbius transformations).

**Corrections and readings.** Reading of "the Bers boundary" (Prop. 7.1) and of `D` for `D*` in Corollary 2 (see the files).

## Coverage

| Part | new definitions (book notions; helpers in parentheses) | new statements | `exists` bullets |
|---|---|---|---|
| §2 The Bers embedding and the asymptotic Bers map | 3 (+4) | 2 | 3 |
| §1.3, §3 Necessary condition for arbitrary Γ | 1 (+1) | 1 | 0 |
| §4–§6 Characterization of the image for the unit disk | 4 (+0) | 5 | 0 |
| §7 Failure of density | 5 (+1) | 3 | 0 |
| §8 Closure of the image | 0 | 2 | 0 |
-/
