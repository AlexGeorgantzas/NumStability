/-
# NumStability declaration dependency extractor

This program loads the compiled `NumStability` environment and emits a tab-separated stream.
It deliberately keeps dependencies occurring in declaration signatures separate from dependencies
occurring in values/proofs.  The Python baseline generator consumes this stream and computes the
architecture metrics.

Run it through `tools/architecture/generate_baseline.py`; the TSV format is an implementation
detail and is not intended to be checked in.
-/

import Lean

open Lean

namespace NumStabilityArchitecture

private def isProjectModule (moduleName : Name) : Bool :=
  let text := moduleName.toString
  text == "NumStability" || text.startsWith "NumStability."

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def declarationVisibility (name : Name) : String :=
  if isPrivateName name then
    "private"
  else if name.isInternalDetail then
    "internal"
  else
    "public"

private def bodyConstants : ConstantInfo → NameSet
  | .defnInfo value => value.value.getUsedConstantsAsSet
  | .thmInfo value => value.value.getUsedConstantsAsSet
  | .opaqueInfo value => value.value.getUsedConstantsAsSet
  | .recInfo value => value.rules.foldl (init := {}) fun names rule =>
      names ++ rule.rhs.getUsedConstantsAsSet
  | _ => {}

private structure ProjectDeclaration where
  name : Name
  moduleName : Name
  info : ConstantInfo

private def sanitizeField (value : String) : String :=
  value.replace "\t" " " |>.replace "\r" " " |>.replace "\n" " "

private def writeFields (handle : IO.FS.Handle) (fields : Array String) : IO Unit :=
  handle.putStrLn <| String.intercalate "\t" (fields.toList.map sanitizeField)

private def collectProjectDeclarations (env : Environment) : Array ProjectDeclaration := Id.run do
  let mut result := #[]
  -- Iterating `env.constants` walks every declaration imported from Mathlib.  `moduleData` already
  -- partitions the same constants by owning module, so selecting project modules first is much
  -- faster and avoids realizing unrelated constants.
  for h : moduleIdx in *...env.header.moduleData.size do
    let moduleName := env.header.moduleNames[moduleIdx]!
    if isProjectModule moduleName then
      let data := env.header.moduleData[moduleIdx]
      for name in data.constNames, info in data.constants do
        -- Module data may repeat a declaration re-exported through a legacy module.  The
        -- environment's ownership index identifies the unique originating module.
        if env.getModuleIdxFor? name == some moduleIdx then
          result := result.push { name, moduleName, info }
  return result.qsort fun left right => left.name.toString < right.name.toString

private def writeEdges
    (handle : IO.FS.Handle)
    (projectNames : NameSet)
    (edgeKind : String)
    (source : ProjectDeclaration)
    (targets : NameSet) : IO Unit := do
  for target in targets.toArray.qsort (·.toString < ·.toString) do
    if projectNames.contains target then
      writeFields handle #[
        "edge",
        edgeKind,
        source.name.toString,
        target.toString
      ]

private unsafe def extract (outputPath : System.FilePath) : IO Unit := do
  initSearchPath (← findSysroot)
  withImportModules #[{ module := `NumStability }] {} fun env => do
    let declarations := collectProjectDeclarations env
    let projectNames : NameSet := declarations.foldl (init := {}) fun names declaration =>
      names.insert declaration.name
    IO.FS.withFile outputPath IO.FS.Mode.write fun handle => do
      writeFields handle #["format", "2"]
      for declaration in declarations do
        writeFields handle #[
          "declaration",
          declaration.name.toString,
          declaration.moduleName.toString,
          declarationKind declaration.info,
          declarationVisibility declaration.name
        ]
      for declaration in declarations do
        writeEdges handle projectNames "signature" declaration
          declaration.info.type.getUsedConstantsAsSet
        writeEdges handle projectNames "body" declaration
          (bodyConstants declaration.info)

unsafe def run (args : List String) : IO UInt32 := do
  match args with
  | [outputPath] =>
      extract outputPath
      return 0
  | _ =>
      IO.eprintln "usage: lake env lean --run tools/architecture/declaration_dependencies.lean OUTPUT.tsv"
      return 2

end NumStabilityArchitecture

unsafe def main (args : List String) : IO UInt32 :=
  NumStabilityArchitecture.run args
