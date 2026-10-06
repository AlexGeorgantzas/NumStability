import NumStability
import Lean

/-!
Extract the declaration and module dependency facts needed by the NumStability
library audit. This command is deliberately read-only with respect to Lean
sources; it only writes CSV files below `NUMSTABILITY_AUDIT_OUT`.
-/

open Lean Elab Command

namespace NumStabilityAudit

private def projectPrefix : Name := `NumStability

private def isProjectModule (moduleName : Name) : Bool :=
  projectPrefix.isPrefixOf moduleName

private def csvCell (value : String) : String :=
  "\"" ++ value.replace "\"" "\"\"" ++ "\""

private def csvRow (values : Array String) : String :=
  String.intercalate "," (values.toList.map csvCell)

private def boolString (value : Bool) : String :=
  if value then "true" else "false"

private def constantKind : ConstantInfo -> String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def moduleNameFor? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx <- env.getModuleIdxFor? declName
  env.header.moduleNames[moduleIdx.toNat]?

private def dependencyScope (moduleName? : Option Name) : String :=
  match moduleName? with
  | some moduleName =>
      if isProjectModule moduleName then "project"
      else if (`Mathlib).isPrefixOf moduleName then "mathlib"
      else if (`Lean).isPrefixOf moduleName then "lean"
      else if (`Std).isPrefixOf moduleName then "std"
      else if (`Batteries).isPrefixOf moduleName then "batteries"
      else "external"
  | none => "unknown"

private def refsInType (info : ConstantInfo) : NameSet :=
  info.type.getUsedConstantsAsSet

private def refsInBody (info : ConstantInfo) : NameSet :=
  match info.value? true with
  | some value => value.getUsedConstantsAsSet
  | none => {}

private def writeDeclarations
    (env : Environment) (outDir : System.FilePath) : IO (Nat × Nat) := do
  let declarationsPath := outDir / "declarations.csv"
  let dependenciesPath := outDir / "direct_dependencies.csv"
  let declarationsHandle <- IO.FS.Handle.mk declarationsPath .write
  let dependenciesHandle <- IO.FS.Handle.mk dependenciesPath .write
  declarationsHandle.putStrLn <| csvRow #[
    "name", "module", "kind", "is_internal", "is_private",
    "has_body", "type_direct_count", "body_direct_count"
  ]
  dependenciesHandle.putStrLn <| csvRow #[
    "source", "source_module", "target", "target_module", "target_scope",
    "occurs_in_type", "occurs_in_body", "same_module"
  ]

  let mut declarationCount := 0
  let mut edgeCount := 0
  for moduleIdx in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[moduleIdx]!
    if isProjectModule moduleName then
      let moduleData := env.header.moduleData[moduleIdx]!
      for declName in moduleData.constNames do
        -- Generated auxiliary names can be repeated in more than one module's
        -- serialized data. Keep only the owner selected by the final imported
        -- environment so every graph node has exactly one source module.
        if moduleNameFor? env declName != some moduleName then
          continue
        let some info := env.find? declName | continue
        let typeRefs := refsInType info |>.erase declName
        let bodyRefs := refsInBody info |>.erase declName
        declarationsHandle.putStrLn <| csvRow #[
          declName.toString,
          moduleName.toString,
          constantKind info,
          boolString declName.isInternal,
          boolString (isPrivateName declName),
          boolString (info.value? true).isSome,
          toString typeRefs.size,
          toString bodyRefs.size
        ]
        declarationCount := declarationCount + 1

        let allRefs := NameSet.append typeRefs bodyRefs
        for targetName in allRefs do
          let targetModule? := moduleNameFor? env targetName
          let targetModuleString := targetModule?.map (toString .) |>.getD ""
          dependenciesHandle.putStrLn <| csvRow #[
            declName.toString,
            moduleName.toString,
            targetName.toString,
            targetModuleString,
            dependencyScope targetModule?,
            boolString (typeRefs.contains targetName),
            boolString (bodyRefs.contains targetName),
            boolString (targetModule? == some moduleName)
          ]
          edgeCount := edgeCount + 1

  declarationsHandle.flush
  dependenciesHandle.flush
  return (declarationCount, edgeCount)

private def writeModuleImports (env : Environment) (outDir : System.FilePath) : IO Nat := do
  let outputPath := outDir / "module_imports.csv"
  let handle <- IO.FS.Handle.mk outputPath .write
  handle.putStrLn <| csvRow #["source_module", "target_module", "target_scope"]
  let mut edgeCount := 0
  for moduleIdx in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[moduleIdx]!
    if isProjectModule moduleName then
      let moduleData := env.header.moduleData[moduleIdx]!
      for importInfo in moduleData.imports do
        handle.putStrLn <| csvRow #[
          moduleName.toString,
          importInfo.module.toString,
          dependencyScope (some importInfo.module)
        ]
        edgeCount := edgeCount + 1
  handle.flush
  return edgeCount

private def runAudit (env : Environment) : IO Unit := do
  let outDirString <- IO.getEnv "NUMSTABILITY_AUDIT_OUT"
  let outDir : System.FilePath := outDirString.getD "audit/latest"
  IO.FS.createDirAll outDir
  let (declarationCount, directEdgeCount) <- writeDeclarations env outDir
  let importEdgeCount <- writeModuleImports env outDir
  IO.println <| s!"Extracted {declarationCount} NumStability declarations, " ++
    s!"{directEdgeCount} direct declaration edges, and {importEdgeCount} direct module imports."
  IO.println s!"Raw audit data: {outDir}"

elab "run_numstability_declaration_audit" : command => do
  runAudit (← getEnv)

end NumStabilityAudit

run_numstability_declaration_audit
