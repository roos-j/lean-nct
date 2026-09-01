import Lean

/-!
# Quick Palomar Comparator

This reusable helper is run from the root of a target Lean repository with

    lake build
    lake env lean <path-to-this-file>

It reads comparator.json and loads Challenge and Solution into isolated Lean
environments. It is a fast local fallback, not a replacement for Palomar's
secure Comparator run.
-/

open Lean

namespace QuickComparator

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

structure Config where
  challenge_module : String
  solution_module : String
  theorem_names : Array String
  definition_names : Option (Array String) := none
  permitted_axioms : Array String
  deriving FromJson

private def loadConfig : IO Config := do
  let text ← IO.FS.readFile "comparator.json"
  let json ← IO.ofExcept <| Json.parse text
  IO.ofExcept <| FromJson.fromJson? json

private def loadModule (name : String) : IO Environment :=
  importModules #[{ module := name.toName }] {}

private def getConst (side : String) (env : Environment) (name : Name) : IO ConstantInfo := do
  let some info := env.find? name
    | throw <| IO.userError s!"{side} does not contain {name}"
  return info

private def infoDeps : ConstantInfo → Array Name
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors

private partial def compareReachable (challenge solution : Environment) (ignored : NameSet)
    (work : List Name) (seen : NameSet := {}) : IO Unit := do
  match work with
  | [] => pure ()
  | name :: work =>
    if seen.contains name then
      compareReachable challenge solution ignored work seen
    else
      let seen := seen.insert name
      let challengeInfo ← getConst "Challenge" challenge name
      let solutionInfo ← getConst "Solution" solution name
      if ignored.contains name then
        compareReachable challenge solution ignored
          (challengeInfo.type.getUsedConstants.toList ++ work) seen
      else
        unless challengeInfo == solutionInfo do
          throw <| IO.userError s!"reachable declaration differs: {name}"
        compareReachable challenge solution ignored ((infoDeps challengeInfo).toList ++ work) seen

private def solutionAxioms (env : Environment) (name : Name) : IO (Array Name) := do
  let ctx : Core.Context := {
    options := {}
    fileName := "<QuickComparator>"
    fileMap := default
  }
  let state : Core.State := { env := env }
  let action : CoreM (Array Name) := collectAxioms name
  action.toIO' ctx state

private def checkTheorem (challenge solution : Environment) (name : Name) : IO (Array Name) := do
  let challengeInfo ← getConst "Challenge" challenge name
  let solutionInfo ← getConst "Solution" solution name
  let (challengeVal, solutionVal) ←
    match challengeInfo, solutionInfo with
    | .thmInfo c, .thmInfo s => pure (c.toConstantVal, s.toConstantVal)
    | .axiomInfo c, .axiomInfo s => pure (c.toConstantVal, s.toConstantVal)
    | _, _ => throw <| IO.userError s!"{name} is not a theorem or axiom on both sides"
  unless challengeVal == solutionVal do
    throw <| IO.userError s!"theorem type differs: {name}"
  let pp := PPContext.mk challenge {} {} {} .anonymous []
  unless ← pp.runMetaM (Meta.isDefEq challengeInfo.type solutionInfo.type) do
    throw <| IO.userError s!"theorem types are not definitionally equal: {name}"
  return challengeInfo.type.getUsedConstants

private def checkDefinition (challenge solution : Environment) (name : Name) : IO (Array Name) := do
  let challengeInfo ← getConst "Challenge" challenge name
  let solutionInfo ← getConst "Solution" solution name
  let (.defnInfo challengeDef) := challengeInfo
    | throw <| IO.userError s!"Challenge definition target {name} is not a definition"
  let (.defnInfo solutionDef) := solutionInfo
    | throw <| IO.userError s!"Solution definition target {name} is not a definition"
  unless challengeDef.toConstantVal == solutionDef.toConstantVal
      && challengeDef.safety == solutionDef.safety do
    throw <| IO.userError s!"definition target has a different signature: {name}"
  return challengeDef.type.getUsedConstants

private def palomarPermittedAxioms : Array Name :=
  #["propext".toName, "Quot.sound".toName, "Classical.choice".toName]

private def validateConfig (cfg : Config) : IO Unit := do
  unless !cfg.challenge_module.isEmpty do
    throw <| IO.userError "challenge_module must be nonempty"
  unless !cfg.solution_module.isEmpty do
    throw <| IO.userError "solution_module must be nonempty"
  unless cfg.challenge_module != cfg.solution_module do
    throw <| IO.userError "Challenge and Solution must be distinct modules"
  unless !cfg.theorem_names.isEmpty do
    throw <| IO.userError "theorem_names must be nonempty"
  for axiomName in cfg.permitted_axioms.map String.toName do
    unless palomarPermittedAxioms.contains axiomName do
      throw <| IO.userError s!"permitted_axioms contains non-Palomar axiom {axiomName}"

def main : IO Unit := do
  let cfg ← loadConfig
  validateConfig cfg
  let challenge ← loadModule cfg.challenge_module
  let solution ← loadModule cfg.solution_module
  let theorems := cfg.theorem_names.map String.toName
  let definitions := cfg.definition_names.getD #[] |>.map String.toName
  let ignored := (theorems ++ definitions).foldl (init := {}) fun s n => s.insert n
  let mut roots := #[]
  for target in theorems do
    roots := roots ++ (← checkTheorem challenge solution target)
  for target in definitions do
    roots := roots ++ (← checkDefinition challenge solution target)
  compareReachable challenge solution ignored roots.toList
  let legal := cfg.permitted_axioms.map String.toName
  for target in theorems do
    for axiomName in ← solutionAxioms solution target do
      unless legal.contains axiomName do
        throw <| IO.userError s!"solution theorem {target} uses forbidden axiom {axiomName}"
  IO.println "Quick Comparator passed."

#eval! main

end QuickComparator
