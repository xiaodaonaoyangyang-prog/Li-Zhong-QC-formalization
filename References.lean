/-
# References — statement-level formalization of the works used by the project

The books and papers of the project's reference shelf, one work per namespace (`Gehring1978`,
`LehtoVirtanen1973`, …). Their definitions are genuine Lean definitions, and every labelled result is stated with a
`sorry` proof, by design. Items that the project (`LiZhongQC`) or Mathlib already contains are not restated: each
file's module docstring indexes every item of the work, with `exists:` pointers to the existing declarations.
`References/Common/` holds notions shared by several works (namespace `References`).

See README.md, section *References*, and run `lake env lean AuditRefs.lean` for the counts.
-/
-- Shared notions
import References.Common.ExtendedPlane
import References.Common.Quasidisk
import References.Common.ExtPlaneBorel
import References.Common.Subharmonic
import References.Common.RiemannSurface
import References.Common.RiemannSphere
import References.Common.HypConvex
import References.Common.RiemannSurfaceHarmonic
import References.Common.HyperbolicSurface
import References.Common.FenchelNielsen
-- Works, in the order of the program
import References.Gehring1978
import References.LehtoVirtanen1973
import References.Lehto1987
import References.AstalaGehring1990
import References.Pommerenke1992
import References.GarnettMarshall2005
import References.Katok1992
import References.GardinerLakic2000
import References.Forster1981
import References.Nag1988
import References.FarkasKra1992
import References.Hubbard2006
import References.ImayoshiTaniguchi1992
import References.Pommerenke1975
import References.Miyachi2008
