import LiZhongQC

open Lean Elab Command

/-- Drop compiler-internal and `_`-prefixed auxiliary declarations. -/
def auxName (n : Name) : Bool :=
  n.isInternal || n.components.any (fun c => c.toString.startsWith "_")

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut clean := 0
  let mut own := 0
  let mut carrier := 0
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo _ =>
        if (`LiZhongQC).isPrefixOf n && !auxName n then
          let ax : Array Name ← collectAxioms n
          if ax.contains ``sorryAx then
            if (ci.getUsedConstantsAsSet).contains ``sorryAx then
              own := own + 1
            else
              carrier := carrier + 1
          else
            clean := clean + 1
        else pure ()
    | _ => pure ()
  logInfo m!"axiom-clean {clean} + own-sorry {own} + carriers {carrier} = {clean + own + carrier}"
