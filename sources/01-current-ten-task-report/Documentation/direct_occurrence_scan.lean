/-
Offline post-run scanner for the frozen ten-task report. Given an already
compiled accepted Candidate module, count occurrences of NumStability
constants in the elaborated target type/proof and in reachable Candidate-local
declaration bodies. Each local body is visited once. External definitions are
not unfolded. This is expression-node frequency, not source-token frequency.

Usage: lean --run direct_occurrence_scan.lean Candidate HighamBenchCandidate.target
-/

import Lean

open Lean

namespace DirectOccurrenceScan

private def ownerModule? (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  return env.header.moduleNames[index]!

private partial def collectConstants (expr : Expr) (names : Array Name) : Array Name :=
  match expr with
  | .const name _ => names.push name
  | .app fn arg => collectConstants arg (collectConstants fn names)
  | .lam _ type body _ => collectConstants body (collectConstants type names)
  | .forallE _ type body _ => collectConstants body (collectConstants type names)
  | .letE _ type value body _ =>
      collectConstants body (collectConstants value (collectConstants type names))
  | .mdata _ body => collectConstants body names
  | .proj _ _ body => collectConstants body names
  | _ => names

private def constants (expr : Expr) : Array Name :=
  collectConstants expr #[]

private def localExprs (info : ConstantInfo) : Array Expr :=
  match info with
  | .defnInfo decl => #[decl.type, decl.value]
  | .thmInfo decl => #[decl.type, decl.value]
  | .opaqueInfo decl => #[decl.type, decl.value]
  | .recInfo decl => #[decl.type] ++ decl.rules.map (·.rhs)
  | .axiomInfo decl => #[decl.type]
  | .quotInfo decl => #[decl.type]
  | .inductInfo decl => #[decl.type]
  | .ctorInfo decl => #[decl.type]

private def countSurface (env : Environment) (moduleName : Name)
    (root : Expr) : Std.HashMap Name Nat := Id.run do
  let mut counts : Std.HashMap Name Nat := {}
  let mut queue := constants root
  let mut seenLocals : NameSet := {}
  let mut cursor := 0
  while cursor < queue.size do
    let name := queue[cursor]!
    cursor := cursor + 1
    if let some owner := ownerModule? env name then
      let rendered := owner.toString
      if rendered == "NumStability" || rendered.startsWith "NumStability." then
        counts := counts.insert name ((counts[name]?).getD 0 + 1)
      else if owner == moduleName && !seenLocals.contains name then
        seenLocals := seenLocals.insert name
        if let some info := env.find? name then
          for expr in localExprs info do
            for child in constants expr do
              queue := queue.push child
  return counts

private unsafe def scan (moduleName targetName : Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  withImportModules #[{ module := moduleName }] {} fun env => do
    let some info := env.find? targetName
      | IO.eprintln s!"unknown theorem: {targetName}"; return 3
    let .thmInfo theoremInfo := info
      | IO.eprintln s!"target is not a theorem: {targetName}"; return 4
    for (surface, expr) in #[("statement", theoremInfo.type),
                             ("proof", theoremInfo.value)] do
      let counts := countSurface env moduleName expr
      let names := counts.toArray.qsort (fun a b => a.1.toString < b.1.toString)
      for (name, count) in names do
        IO.println s!"name\t{surface}\t{name}\t{count}"
      let total := names.foldl (fun n pair => n + pair.2) 0
      IO.println s!"summary\t{surface}\t{names.size}\t{total}"
    return 0

unsafe def run (args : List String) : IO UInt32 := do
  match args with
  | [moduleText, targetText] => scan moduleText.toName targetText.toName
  | _ =>
      IO.eprintln "usage: lean --run direct_occurrence_scan.lean MODULE TARGET"
      return 2

end DirectOccurrenceScan

unsafe def main (args : List String) : IO UInt32 :=
  DirectOccurrenceScan.run args
