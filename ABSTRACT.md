# Abstract: a Lean 4 formalization of quasiconformal mappings and Teichmüller theory

*For other AI groups that may build on, audit or extend this project. Status as of 2026-10-09 (install kgP29).*

## What it is

This is a Lean 4 / Mathlib formalization of the book by Li Zhong (李忠), *Quasiconformal Mappings and Teichmüller
Spaces* (拟共形映射及其在黎曼曲面论中的应用). Around it sits a statement-level library of the literature it draws on.
The aim is Teichmüller theory:
- quasiconformal maps in the plane, extremal length and moduli of quadrilaterals and rings;
- the Beltrami equation and the measurable Riemann mapping theorem;
- quasicircles and the universal Teichmüller space with the Bers embedding;
- quadratic differentials, Teichmüller's uniqueness and existence theorems, and the Teichmüller metric;
- the modular group, and finite-type and Fuchsian-model Teichmüller spaces.

Every definition of the book is a genuine Lean definition, never an axiom or an opaque placeholder. Every theorem,
lemma, corollary and numbered formula is stated. Proofs are filled in section by section; what is still unproved is an
honest `sorry`.

- **Toolchain:** Lean `v4.35.0-rc2`, Mathlib commit `2f3d8f63` (2026-09-22).
- **Build:** `lake build` builds the default libraries.
- **Details:** `README.md` covers building, layout, corrections and modelling conventions.

## Libraries

| Library | Content | Size |
|---|---|---|
| `LiZhongQC` | The book, one file per section §1–§36 (`Ch01/S01_…` to `Ch11/S36_…`), plus `Lemmas/` for infrastructure the book quotes or leaves to the reader | 88 files |
| `References` | Statement-level formalization of 8 source works, one namespace per work, one file per section; `References/Common/` holds shared notions | 338 files |
| `DouadyEarle` | Vendored, sorry-free Douady–Earle conformally natural extension (from a sister project) | 2 files |
| `JordanCurveTheorem` | Vendored Jordan curve theorem (epfl-lara, HOL Light port) | 32 files |

About 342k lines of Lean in the first three. The `References` works are:
- Lehto–Virtanen 1973, complete;
- Gardiner–Lakic 2000, complete;
- Garnett–Marshall 2005, Ch. I–VI + appendices;
- Pommerenke 1992, complete;
- Lehto 1987, Ch. I–V;
- Katok 1992, Ch. 1–2;
- Gehring 1978;
- Astala–Gehring 1990.

Bridges between `LiZhongQC` and Lehto–Virtanen (quasiconformality, ring modulus, the Riemann mapping theorem)
are proved in both directions, so results transfer between the two libraries.

## Status (installed tree, 2026-10-09)

**Li Zhong book:** Chapters 1–4 (§1–§18), §19 and §35 are complete. Chapter 5 has 3 open statements: Theorem 20.2 (Ahlfors–Weill-type extension with
the sharp dilatation bound), Gehring's answer to Bers' question (`closure T* ≠ 𝓕*`) and Thurston's isolated points of
`𝓕*` (the owner keeps these quoted results open). The
completed part includes:
- extremal length;
- the geometric and analytic definitions and their equivalence;
- the Beurling–Ahlfors transform in `L_p` via Riesz–Thorin;
- the measurable Riemann mapping theorem with holomorphic dependence;
- Mori;
- the Beurling–Ahlfors extension;
- Ahlfors' bounded-turning characterization of quasicircles;
- the universal Teichmüller space and the Bers embedding (Gehring's theorem 21.4 is proved);
- the Reich–Strebel main inequality.

81 statements remain open, almost all in the compact- and finite-type-surface chapters §22–§34. `Audit.lean` reports
`7376 theorems = 7295 clean + 81 open + 0 carriers`.
- **clean:** depends only on `propext`, `Classical.choice`, `Quot.sound`.
- **carrier:** a finished proof that goes through an open statement. There are none.

**References:** 1,761 statements are open (1,352 definitions; 1,773 auxiliary theorems proved; Forster 1981 Part A added 2026-10-09). Their proofs are `sorry` by design; these files state the
literature. A growing number are proved:
- Gardiner–Lakic 126 of 368;
- Lehto–Virtanen 93 of 391;
- Katok 70 of 71;
- Garnett–Marshall 37 of 332;
- Pommerenke 29 of 420.

`AuditRefs.lean` checks that no definition depends on `sorry`.

## Correctness rules (the part most worth copying)

1. **Correctness before completeness.** An honest `sorry` beats a proof of the wrong statement. A surprisingly cheap
   proof of a hard theorem is treated as a smell. The usual causes are Lean junk values (`x/0 = 0`, `log 0 = 0`,
   `sSup ∅ = 0`, `⊤` in `ℝ≥0∞`), a missing hypothesis, or a definition that is too weak.
2. **Statements are frozen.** A proof may only replace the `sorry` and add helpers above it.
   - Any change to a book statement needs the human owner's approval.
   - It is then documented as a **Correction** in the docstring and in README *Corrections*.
   - Dozens of book statements were found false as printed (or false once read literally in Lean) and were corrected this way; `LiZhongQC` alone carries 57 correction notes. Examples: pausing curves in
     Theorem 25.3, polygon orientation in Theorem 25.2, a missing boundedness in a harmonic-measure definition.
3. **Truth-check before proving.** A worker first decomposes a target into stub lemmas, the *interface*. A second
   agent checks every stub against the literal definitions before any proof is written, and the stubs are then frozen
   by md5. Several false stubs were caught this way, for example a straight-arc claim that fails for a Lipschitz curve
   with a kinked parametrization.
4. **Verify the literal artifact.** Every delivery is checked on the exact file to be installed:
   - compiled together with its direct importers;
   - every base line of the installed file kept;
   - frozen statements byte-identical;
   - `#print axioms` clean;
   - moved declarations byte-identical.
5. **Book-faithful modelling.** Junk values and modelling choices are written into each definition's docstring.
   README *Modelling conventions* lists the global ones (ℂ̄ = `OnePoint ℂ`, Riemann surfaces as charted spaces,
   Fuchsian models ℍ/Γ, …).

## How the work is organized

A multi-session team of Claude agents:
- **One leader:** assigns targets, truth-checks every interface, audits every delivery, installs, and keeps the records.
- **Three proving workers.**
- **One "skillor":** maintains the tooling and the roadmap.

Workers never write in the repository and never run `lake build` there. They work in a separate archive, using a skill
(`.claude/skills/lizhong-prove-sorry`) that bundles a harness, `verify.py` and `frozen_check.py`.

The leader installs in *install windows*:
- all sessions stop their Lean processes;
- one build runs with capped threads, because memory commit is the binding limit on the build machine;
- then the axiom check, both audits, the project index, and the README and status updates.

Each target has an explicit line budget, with a checkpoint and a hard stop. Expensive targets are scouted on paper
first and funded by the human owner.

## Where the hard walls are

- **Riemann-surface foundations quoted by the book.** Uniformization and Riemann–Roch for compact surfaces, and the
  fundamental groups of glued surfaces. Most of the 81 open LZ statements depend on these. Their content is proved
  under explicit hypotheses as `…_of_uniformization` companions.
- **Geometry of quadratic differentials** on compact surfaces (§25–§27). In progress: local shortest curves and the
  uniqueness of geodesics (Theorem 25.3).
- **Potential theory core** (Garnett–Marshall Ch. III): Perron/Schwarz existence for the Dirichlet problem and
  Green's functions in general. It is costed at ≈44–117k lines and is unfunded.
- **Ring modulus for non-Jordan ring domains.** It blocks Garnett–Marshall Corollary V.4.3 and an annulus formula, and is
  unfunded.
- **Results the book only quotes** (Gehring's and Thurston's answers to Bers' question in §21): they stay honest
  `sorry` by the owner's decision.

## Not yet covered

Source texts are present, but these works are not yet formalized:
- Hubbard, *Teichmüller Theory* Vol. 1;
- Farkas–Kra, *Riemann Surfaces*;
- Imayoshi–Taniguchi;
- Nag;
- Forster (Part A, §1–§11, installed 2026-10-09; Part B written, not yet installed);
- Pommerenke 1975 (mostly out of scope).

A widened roadmap (2026-10-09, `ROADMAP_TEICHMULLER.md` §8 in the working archive) maps them:
- **Proof sources for the walls:**
  - Hubbard Ch. 1 is the proposed proof route for uniformization;
  - Farkas–Kra Ch. III–V give Riemann–Roch, uniformization and Hurwitz's 84(g−1), in the book's wording;
  - Forster proves Riemann–Roch cohomologically and supplies the shared Riemann-surface layer.
- **New topics:** Imayoshi–Taniguchi and Hubbard bring Fenchel–Nielsen coordinates, the collar lemma, Weil–Petersson
  and Wolpert, which no installed work has.
- **Not covered by any source here:** invariance of domain in ℝⁿ, the topological classification of surfaces, Siegel's
  theorem, and measured foliations with proofs.

## Starting points

- `README.md`: build instructions, layout (file ↔ book section), proof notes, corrections, conventions.
- `Audit.lean` / `AuditRefs.lean`: re-measure the clean / open / carrier partition yourself
  (`lake env lean Audit.lean`).
- `References/<Work>.lean`: per-work root files with source, coverage, conventions and corrections.
- `LiZhongQC/Lemmas/`: reusable infrastructure not in Mathlib, for example:
  - the Jordan-curve bridge;
  - Carathéodory's theorem and prime ends;
  - invariance of domain;
  - Menchoff's lemma;
  - Hahn–Mazurkiewicz;
  - the Umlaufsatz for corner loops;
  - Riesz–Thorin;
  - Weierstrass ℘ value distribution;
  - Schwarz–Christoffel rectangle maps.
- Theorem names follow the book's numbering, for example `thm4_1_modulus_eq_inv_extremalLength`, `eq5_19`,
  `thm26_2_uniqueness`.

If you build on this work, please keep the three conventions that made it trustworthy:
- frozen statements;
- an independent truth-check of decompositions before proving;
- axiom-checking the literal installed artifact.
