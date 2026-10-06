import NumStability
import Lean
import Lean.Meta.Eqns

/-!
Emit Lean's reserved-name signal for declarations owned by NumStability modules.
This distinguishes compiler-reserved public-looking machinery from ordinary
non-reserved declarations without relying on a name regex.
-/

open Lean Elab Command

namespace NumStabilityReorganization

private def projectPrefix : Name := `NumStability

private def isProjectModule (moduleName : Name) : Bool :=
  projectPrefix.isPrefixOf moduleName

private def csvCell (value : String) : String :=
  "\"" ++ value.replace "\"" "\"\"" ++ "\""

private def csvRow (values : Array String) : String :=
  String.intercalate "," (values.toList.map csvCell)

private def boolString (value : Bool) : String :=
  if value then "true" else "false"

private def moduleNameFor? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx <- env.getModuleIdxFor? declName
  env.header.moduleNames[moduleIdx.toNat]?

private def equationParent?
    (env : Environment) (declName : Name) : CommandElabM (Option Name) := do
  if !isReservedName env declName then return none
  let candidate := declName.getPrefix
  if !env.contains candidate then return none
  let eqns? ← liftTermElabM <| Meta.getEqnsFor? candidate
  if eqns?.getD #[] |>.contains declName then return some candidate
  return none

private def writeOrigins (env : Environment) : CommandElabM Unit := do
  let outDirString ← liftIO <| IO.getEnv "NUMSTABILITY_AUDIT_OUT"
  let outDir : System.FilePath := outDirString.getD "audit/latest"
  liftIO <| IO.FS.createDirAll outDir
  let outputPath := outDir / "declaration_origins.csv"
  let handle ← liftIO <| IO.FS.Handle.mk outputPath .write
  liftIO <| handle.putStrLn <| csvRow #[
    "name", "module", "is_reserved_name", "equation_parent"
  ]
  let mut count := 0
  let mut reservedCount := 0
  for moduleIdx in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[moduleIdx]!
    if isProjectModule moduleName then
      let moduleData := env.header.moduleData[moduleIdx]!
      for declName in moduleData.constNames do
        if moduleNameFor? env declName != some moduleName then
          continue
        let reserved := isReservedName env declName
        let equationParent ← equationParent? env declName
        liftIO <| handle.putStrLn <| csvRow #[
          declName.toString,
          moduleName.toString,
          boolString reserved,
          equationParent.map Name.toString |>.getD ""
        ]
        count := count + 1
        if reserved then reservedCount := reservedCount + 1
  liftIO <| handle.flush
  liftIO <| IO.println <| s!"Recorded origin signals for {count} declarations " ++
    s!"({reservedCount} Lean-reserved names): {outputPath}"

elab "run_numstability_declaration_origins" : command => do
  writeOrigins (← getEnv)

end NumStabilityReorganization

run_numstability_declaration_origins
