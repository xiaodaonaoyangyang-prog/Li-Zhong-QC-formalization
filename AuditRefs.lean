import References

/-
Audit of the `References` library (not part of the library; `lake build` ignores it).

    lake env lean AuditRefs.lean

`References` is the statement-level formalization of the books and papers used by the project: genuine definitions,
and theorem statements whose proofs are `sorry` by design. For every work `References.<Key>` this prints how many
definitions (`def`/`structure`/`inductive`, instances included), statements (theorems whose own body uses `sorry`) and
auxiliary proved theorems it has, and it lists every definition that depends on `sorryAx`, directly or through
another constant. That list must be empty: definitions are genuine.

Method as in `Audit.lean`: a reverse dependency graph over the constants of the `LiZhongQC.*` and `References.*`
modules (`ConstantInfo.getUsedConstantsAsSet`), then reachability from the constants that use `sorryAx` directly.
Compiler-generated auxiliary constants (`proof_n`, matchers `match_n` and `match_n_m`, equation lemmas, `_`-prefixed
names, a structure's projections and its `mk.inj`/`mk.injEq`/`mk.sizeOf_spec`, and the auxiliary recursors and
no-confusion definitions of a structure or inductive type: `casesOn`, `recOn`, `brecOn`, `binductionOn`, `below`,
`ibelow`, `noConfusionType`, `noConfusion`, `mk.noConfusion`) are not counted.
-/
open Lean Elab Command

def refsAux (n : Name) : Bool :=
  n.isInternal || n.components.any (fun c => c.toString.startsWith "_") ||
    (match n with
     | .str _ s => s.startsWith "proof_" || s.startsWith "match_" || s.startsWith "eq_" || s == "eq_def" ||
        s == "sizeOf_spec" || s == "injEq" || s == "inj" ||
        -- generated with every `structure`/`inductive` (2026-10-06): before, each structure added 5 "definitions"
        s == "casesOn" || s == "recOn" || s == "brecOn" || s == "binductionOn" || s == "below" || s == "ibelow" ||
        s == "noConfusionType" || s == "noConfusion"
     | _ => false)

/-- The work key of a `References.*` module (`References.<Key>.…` ↦ `<Key>`). -/
def refsKey (m : Name) : String :=
  match m.components with
  | _ :: k :: _ => k.toString
  | _ => "References"

#eval show CommandElabM Unit from do
  let env ← getEnv
  let modIdx : Array (Option String) := env.header.moduleNames.map (fun m =>
    if (`References).isPrefixOf m then some (refsKey m)
    else if (`LiZhongQC).isPrefixOf m then some "" else none)
  -- constants of the two libraries, with their work key ("" for LiZhongQC)
  let mut owner : NameMap String := {}
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if let some k := modIdx[idx.toNat]! then owner := owner.insert n k
  let mut rev : NameMap (List Name) := {}
  let mut direct : List Name := []
  for (n, _) in owner.toList do
    if let some ci := env.find? n then
      for d in ci.getUsedConstantsAsSet.toList do
        if d == ``sorryAx then direct := n :: direct
        else if owner.contains d then rev := rev.insert d (n :: (rev.getD d []))
  let mut seen : NameSet := {}
  let mut work := direct
  while !work.isEmpty do
    match work with
    | [] => pure ()
    | n :: rest =>
      work := rest
      if !seen.contains n then
        seen := seen.insert n
        work := (rev.getD n []) ++ work
  let directSet : NameSet := direct.foldl (fun s n => s.insert n) {}
  let mut stats : Std.HashMap String (Nat × Nat × Nat) := {}
  let mut bad : Array Name := #[]
  for (n, k) in owner.toList do
    if k == "" || refsAux n || (env.getProjectionFnInfo? n).isSome then continue
    let (d, s, p) := stats.getD k (0, 0, 0)
    match env.find? n with
    | some (.thmInfo _) =>
        stats := stats.insert k (if directSet.contains n then (d, s + 1, p) else (d, s, p + 1))
        if !directSet.contains n && seen.contains n then bad := bad.push n
    | some (.defnInfo _) | some (.inductInfo _) =>
        stats := stats.insert k (d + 1, s, p)
        if seen.contains n then bad := bad.push n
    | _ => pure ()
  let keys := stats.toList.map (·.1) |>.toArray.qsort (· < ·)
  let mut total := (0, 0, 0)
  for k in keys do
    let (d, s, p) := stats.getD k (0, 0, 0)
    total := (total.1 + d, total.2.1 + s, total.2.2 + p)
    logInfo m!"{k}: definitions {d}, statements {s}, auxiliary proved theorems {p}"
  logInfo m!"References total: definitions {total.1}, statements {total.2.1}, auxiliary proved theorems {total.2.2}"
  logInfo m!"constants depending on sorry other than the statements themselves (must be empty): {bad}"
