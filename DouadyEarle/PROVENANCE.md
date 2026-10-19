# Provenance of the vendored DouadyEarle library

- Source: `D:/lean/Conformally_natural_extension_of_homeomorphisms_of_the_circle/DouadyEarleExt/` (the user's
  sister project; same toolchain leanprover/lean4:v4.35.0-rc2 and the same Mathlib checkout D:/lean/mathlib4-latest).
- Vendored 2026-10-06 by leader -ea on the user's approval, for Pommerenke §5.5 (Douady–Earle).
- `Basic.lean`: byte-identical copy (CRLF kept), md5 f4f4771f413c04bf75c57e9b64b64cb0.
- `Extension.lean`: copy of md5 c46a3521a64eefee9fa1399cce70e8f7 (CRLF kept) with one line changed (`import DouadyEarleExt.Basic` ->
  `import DouadyEarle.Basic`); vendored md5 be708cb5c158a1a84c0c33d2bccc5cb9.
- Module prefix renamed `DouadyEarleExt` -> `DouadyEarle` because the sister project requires this repository:
  the same module name in both packages would clash in its workspace. Declarations keep their names.
- Not vendored: AhlforsBers, Quasiconformal, Teichmuller, Analytic, Estimates, ImplicitZero, HigherDim (they
  import this repository or still contain `sorry`).
- Lean options as upstream (no package options there): autoImplicit and relaxedAutoImplicit at Lean's defaults.
