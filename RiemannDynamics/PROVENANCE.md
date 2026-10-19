# RiemannDynamics archived source integration candidate

Upstream: https://github.com/will1491/RiemannDynamics, commit `b3fa37cc0f18a23ea66b654ea3f73eb472129010`. License: upstream Apache-2.0 LICENSE preserved verbatim.
Selected modules: 38. This is the accepted recursive theorem import closure,
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
