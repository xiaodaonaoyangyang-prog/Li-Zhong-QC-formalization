# Topological classification of compact surfaces

The modules `SchottkyClassification01` … `SchottkyClassification28` bundle the import closure of
`ClassificationOfSurfaces.EvalStatement` from
[mccorvie/classification-of-surfaces](https://github.com/mccorvie/classification-of-surfaces/tree/e3c7230fe78d7b056a415d9ecae6f77887046b32),
commit `e3c7230fe78d7b056a415d9ecae6f77887046b32` (Apache License 2.0, `LICENSE.Apache-2.0`;
attribution and modifications in `NOTICE.Classification`).

The public endpoint used by LiZhongQC is
`LeanEval.Topology.ClassificationOfSurfaces.classification_of_surfaces` (bundle 28): every compact connected
Hausdorff topological 2-manifold with boundary is homeomorphic to the sphere, an orientable normal form
`Quot (OrientableRel p n)` or a non-orientable normal form `Quot (NonOrientableRel p n)`.
Its consumers are `LiZhongQC.Lemmas.SchottkyClosedGenus` (`closed_surface_has_genus`, §22.1); the bundles are
also imported by the genus-bridge and surface modules `SchottkyGenusBridge2`, `SchottkyClosedSurface1`,
`SchottkyNonOrientableSmall`, `SchottkyCoreIntrinsicBoundary` and the boundary-rank modules
`SchottkyBoundaryRank*` (`SchottkyBoundaryRankModel`, `SchottkyBoundaryRankDisc`, …).

Each bundle keeps every upstream file as one block `BEGIN <module> | <sha256 of the upstream file>` with
its original header. Local adaptations to Lean `v4.35.0-rc2` and the project's Mathlib are proof repairs plus
elaboration-only edits that change no statement type and no definition value: four `@[reducible]` attributes
(`PartialTriangulation.toIntrinsic`, `PartialTriangulation.refine` in bundle 17;
`ChartInductionGeometry.n`, `ChartInductionGeometry.subdivision` in bundle 18), `letI … := inferInstance` in the
bodies of `ofOneFaceWordPreHomeomorph` (bundle 22) and `twoMonogonPreHomeomorph` (bundle 23), and an explicit
`Decidable` instance argument in `chartHalfDiamondMesh` and the private theorem `restrictedRightDiamond_support`
(bundle 14); see `NOTICE.Classification`. The per-bundle maps (`BUNDLE_MAP.json`) and compile receipts are in the archive
(`prove/claude_r78_cls*`, `prove/leader_gpt_20261013/c78_cls*`). All 28 bundles compiled in the project
toolchain with standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).
