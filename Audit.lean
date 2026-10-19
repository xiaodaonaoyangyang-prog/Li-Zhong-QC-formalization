import LiZhongQC

/-
Audit of the proof status (not part of the library; `lake build` ignores it).

    lake env lean Audit.lean

Prints, for the theorems defined in the project's modules (`LiZhongQC` and `LiZhongQC.*`; compiler-internal and
`_`-prefixed auxiliary names are dropped): how many depend only on the standard axioms, how many are open statements
(their own bodies use `sorry`), and how many are *carriers* (complete proofs that go through an open statement), and
lists the carriers.

Method: a reverse dependency graph inside the project, built from `ConstantInfo.getUsedConstantsAsSet` (which forces
lazily loaded theorem bodies; `ConstantInfo.value?` would return `none` for imported theorems), then reachability from
the constants that use `sorryAx` directly.  Mathlib and core contain no `sorry`, so the walk stops at them.  Persistent
`NameSet`/`NameMap` structures keep the interpreted `#eval` fast (about a minute including the import).
-/
open Lean Elab Command

def auxName (n : Name) : Bool :=
  n.isInternal || n.components.any (fun c => c.toString.startsWith "_")

/-- Project constants (defined in `LiZhongQC.*` modules). The module table is read once. -/
def projectConstants (env : Environment) : NameSet := Id.run do
  let isProjMod : Array Bool := env.header.moduleNames.map (fun m => (`LiZhongQC).isPrefixOf m)
  let mut s : NameSet := {}
  for (n, _) in env.constants.map₁.toList do
    if let some idx := env.getModuleIdxFor? n then
      if isProjMod[idx.toNat]! then s := s.insert n
  return s

/-- Reverse edges `d ↦ users` inside the project, and the constants that use `sorryAx` directly. -/
def reverseGraph (env : Environment) (proj : NameSet) : NameMap (List Name) × List Name := Id.run do
  let mut rev : NameMap (List Name) := {}
  let mut direct : List Name := []
  for n in proj.toList do
    if let some ci := env.find? n then
      for d in ci.getUsedConstantsAsSet.toList do
        if d == ``sorryAx then direct := n :: direct
        else if proj.contains d then rev := rev.insert d (n :: (rev.getD d []))
  return (rev, direct)

/-- All constants reachable from `seeds` along reverse edges (worklist over persistent sets). -/
def reach (rev : NameMap (List Name)) (seeds : List Name) (fuel : Nat) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut work : List Name := seeds
  let mut k := fuel
  while k > 0 do
    k := k - 1
    match work with
    | [] => k := 0
    | n :: rest =>
      work := rest
      if !seen.contains n then
        seen := seen.insert n
        work := (rev.getD n []) ++ work
  return seen

#eval show CommandElabM Unit from do
  let env ← getEnv
  let proj := projectConstants env
  let (rev, direct) := reverseGraph env proj
  let bad := reach rev direct 10000000
  let thms := proj.toList.filter (fun n => !auxName n && (match env.find? n with | some (.thmInfo _) => true | _ => false))
  let directSet : NameSet := direct.foldl (fun s n => s.insert n) {}
  let own := thms.filter (fun n => directSet.contains n)
  let carriers := thms.filter (fun n => bad.contains n && !directSet.contains n)
  let clean := thms.length - own.length - carriers.length
  logInfo m!"theorems {thms.length}: axiom-clean {clean} + open (sorry) {own.length} + carriers {carriers.length}"
  logInfo m!"carriers: {carriers}"
