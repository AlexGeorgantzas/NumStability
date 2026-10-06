/-
Read the kernel-accepted target's *proof term*, not its type. Follow proof-local
helper declarations from the compiled Candidate module. Emit direct library
constants encountered on that proof path, stopping at external declarations.

Usage: lean --run design33_proof_dependencies.lean Candidate HighamBenchCandidate.target
-/

import Lean

open Lean

namespace Pilot33ProofDependencies

private def ownerModule? (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  return env.header.moduleNames[index]!

private def bodyConstants : ConstantInfo → NameSet
  | .defnInfo info => info.value.getUsedConstantsAsSet
  | .thmInfo info => info.value.getUsedConstantsAsSet
  | .opaqueInfo info => info.value.getUsedConstantsAsSet
  | .recInfo info => info.rules.foldl (init := {}) fun names rule =>
      names ++ rule.rhs.getUsedConstantsAsSet
  | _ => {}

private unsafe def scan (moduleName targetName : Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  withImportModules #[{ module := moduleName }] {} fun env => do
    let some info := env.find? targetName
      | IO.eprintln s!"unknown theorem: {targetName}"; return 3
    let .thmInfo theoremInfo := info
      | IO.eprintln s!"target is not a theorem: {targetName}"; return 4
    let initial := theoremInfo.value.getUsedConstantsAsSet
    let mut queue := initial.toArray
    let mut cursor := 0
    let mut seen : NameSet := {}
    let mut library : NameSet := {}
    while cursor < queue.size do
      let name := queue[cursor]!
      cursor := cursor + 1
      if !seen.contains name then
        seen := seen.insert name
        if let some declaration := env.find? name then
          if let some owner := ownerModule? env name then
            let rendered := owner.toString
            if rendered == "NumStability" || rendered.startsWith "NumStability." then
              library := library.insert name
            else if owner == moduleName then
              for child in (bodyConstants declaration).toArray do
                if !seen.contains child then
                  queue := queue.push child
    for name in library.toArray.qsort (fun left right => left.toString < right.toString) do
      IO.println s!"proof-library\t{name}"
    IO.println s!"summary\t{library.size}\t{seen.size}"
    return 0

unsafe def run (args : List String) : IO UInt32 := do
  match args with
  | [moduleText, targetText] => scan moduleText.toName targetText.toName
  | _ =>
      IO.eprintln "usage: lean --run design33_proof_dependencies.lean MODULE TARGET"
      return 2

end Pilot33ProofDependencies

unsafe def main (args : List String) : IO UInt32 :=
  Pilot33ProofDependencies.run args
