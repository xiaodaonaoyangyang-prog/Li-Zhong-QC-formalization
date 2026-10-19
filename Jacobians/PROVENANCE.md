# Jacobians archived source integration candidate

Upstream: https://github.com/rkirov/jacobian-claude, commit `73212f7ef2bb46a7884710b18fe1e18b8509e3e5`. License: upstream Apache-2.0 LICENSE preserved verbatim.
Selected modules: 194. This is the accepted recursive theorem import closure,
not a claim that every module in the upstream repository was migrated.

Target compiler: Lean v4.35.0-rc2, SHA256 `16e2c9c597d71fbbadd2b909c3fad5ea7830a4b7aa0123b93e0f3b19de7b959e`.
Target Mathlib: `2f3d8f63005779e9d708eb9adf3feca54aa24ceb`.
MIGRATION.patch records the source changes from the pinned upstream bytes; its diff text
uses LF, while all delivered Lean sources retain their previously accepted literal bytes.
REUSE_VENDOR_MANIFEST.json records original/migrated source hashes and prior output hashes.

Both original book targets and all 96 new public helpers passed the fixed three-axiom checks.
The 136 original S22 model Expr records are byte-identical; all 322 affected modules passed sequential literal Lean compilation.
Strict acceptance also checked the original main/reference audits. See REUSE_INTEGRATION.md and the leader archive.
No main-project Lake build or complete upstream migration is claimed.

Eleven additional modules for the actual Abel pairing and zero-pairing ∂bar solvability
were migrated at the same pinned commit. ABEL_MIGRATION.patch records the only
additional API changes (three files, twelve added and five removed lines).
All 381 origin declarations passed literal pinned compilation and the standard
three-axiom audit; the independent review is captured by the leader's
abel_extension_v2/ACCEPTANCE.json. Existing 183 sources remain byte-identical.
