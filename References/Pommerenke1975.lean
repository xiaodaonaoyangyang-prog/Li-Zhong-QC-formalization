import References.Pommerenke1975.Ch03.S01_GrunskyInequality
import References.Pommerenke1975.Ch09.S04_QuasiconformalCurves

/-!
# Pommerenke 1975, *Univalent Functions* (statement level, Teichmüller-relevant part)

Ch. Pommerenke, *Univalent Functions*, with a chapter on quadratic differentials by G. Jensen, Studia Mathematica /
Mathematische Lehrbücher XXV, Vandenhoeck & Ruprecht, Göttingen 1975. OCR sources (MinerU `full.md`): part 1 (Ch. 1–7) and
part 2 (Ch. 8–11, index); line numbers `P1 l. n`, `P2 l. n`. Namespace `Pommerenke1975`. Statements only: every definition is
genuine, every theorem is `:= by sorry`, results already installed are passed by `exists:` pointers.

**Scope (BRIEF_W2, leader ruling 2026-10-09).** Only the parts related to Teichmüller theory and only new items:
Ch. 3 §3.1 *The Grunsky inequality* (Faber polynomials, Grunsky coefficients and operator, Theorems 3.1–3.2, Corollaries
3.1–3.2) and Ch. 9 §9.4 *Quasiconformal curves* (the classes `Σ(κ)`, Lemmas 9.8–9.10, Theorems 9.12–9.14, Corollary 9.6).
Chapters 1–2 are covered by `Pommerenke1992` (Ch. 1, 3) and are not restated; the rest of Ch. 3 (Golusin, Fitzgerald, Milin
inequalities) and Chapters 4–8, 10–11 are out of scope.

**Conventions.**
(1) The class `Σ`, its coefficients `b_n`, are `Pommerenke1992.IsClassSigma`, `Pommerenke1992.sigmaCoeff`; the exterior set
  `E(g) = ℂ ∖ g(Δ)` is `sigmaE`; `Δ = {|z| > 1}`, `D = {|z| < 1}`.
(2) Faber polynomials are defined by the recursion (3.1.5) (`faberPoly`), the Grunsky coefficients by the contour integral
  of (3.1.11) (`grunskyCoeff`); the book's identities (3.1.2)–(3.1.13) are stated for `g ∈ Σ` (the case used everywhere).
(3) Quasiconformal curves are `LiZhongQC.IsBoundedTurning` (the arc condition (9.4.1)), see `Ch09/S04`.

**Corrections and readings.** (none in the delivered parts; the inventory records the book errors found in the proofs of
Ch. 3.)

## Coverage

| Chapter | new definitions (book notions; helpers in parentheses) | new statements | `exists` bullets |
|---|---|---|---|
| 3 §3.1 The Grunsky inequality | 4 (+2) | 17 | 0 |
| 9 §9.4 Quasiconformal curves | 2 (+1) | 12 | 1 |
-/
