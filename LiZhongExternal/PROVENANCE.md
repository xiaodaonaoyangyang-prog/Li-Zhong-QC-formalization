# Brouwer and invariance of domain

The five `Harfe` modules adapt the Brouwer proof from
[harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838),
commit `770940ddf9878cf61952ed53d910b92bca841838`. Copyright (c) 2026 harfe;
the original MIT text is preserved in `Harfe/LICENSE.harfe`.

`Topology/ConditionalInvarianceOfDomain.lean` adapts only original lines 1014–1440
of `Mathlib/AlgebraicTopology/InvarianceOfDomain.lean` from
[Xmask19/mathlib4](https://github.com/Xmask19/mathlib4/tree/230d75acb32d80e7d7c4f4cd028b139f3dc28be7),
commit `230d75acb32d80e7d7c4f4cd028b139f3dc28be7` (PR36770).
Copyright (c) 2026 Kai Lam; the source author notice and the Apache 2.0 license
are retained in the module and `Topology/LICENSE.mathlib`.

Local adaptations, 2026-10-14, target Lean `v4.35.0-rc2` and the project's Mathlib:

- Add the `LiZhongExternal` namespaces and local import paths.
- Replace obsolete instance/choice references; explicitly mark two classical
  combinatorial constructions noncomputable.
- Repair finite-index transports and membership elaboration. A local
  `backward.isDefEq.respectTransparency false` option retains the older elaboration
  behavior for one Sperner proof; kernel checking remains enabled.
- Replace the unproved upstream Brouwer class with an ordinary internal premise.
  The two wrapper modules discharge that premise using the proved Brouwer theorem.
- Repair coordinate, topology and continuity API uses, replace a failed broad
  `grind` call with its direct argument, and increase the local heartbeat allowance
  for the interior theorem.

All eight modules compiled in the project toolchain. The Brouwer endpoint and
the unconditional finite-dimensional invariance-of-domain endpoint were checked
to depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The full unfinished upstream PR is not part of this library. No module imports
`LiZhongQC`; the project imports the proved external endpoints.
