import NumStability
import Lean

/-!
Export lightweight structural fingerprints for duplicate-statement triage.
Fingerprints produce candidates only; they are not semantic equivalence proofs.
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

private def runFingerprints (env : Environment) : IO Unit := do
  let outDirString <- IO.getEnv "NUMSTABILITY_AUDIT_OUT"
  let outDir : System.FilePath := outDirString.getD "audit/latest"
  IO.FS.createDirAll outDir
  let handle <- IO.FS.Handle.mk (outDir / "statement_fingerprints.csv") .write
  handle.putStrLn <| csvRow #[
    "name", "module", "kind", "is_internal", "is_private",
    "type_hash", "type_equivalence_id", "type_reference_count"
  ]
  let mut count := 0
  let mut nextTypeId := 0
  let mut typeBuckets : Std.HashMap UInt64 (Array (Expr × Nat)) := {}
  for moduleIdx in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[moduleIdx]!
    if isProjectModule moduleName then
      let moduleData := env.header.moduleData[moduleIdx]!
      for declName in moduleData.constNames do
        if moduleNameFor? env declName != some moduleName then
          continue
        let some info := env.find? declName | continue
        let typeHash := hash info.type
        let bucket := typeBuckets.getD typeHash #[]
        let mut typeId? : Option Nat := none
        for (existingType, existingId) in bucket do
          if existingType == info.type then
            typeId? := some existingId
            break
        let typeId <- match typeId? with
          | some existingId => pure existingId
          | none => do
              let newId := nextTypeId
              nextTypeId := nextTypeId + 1
              typeBuckets := typeBuckets.insert typeHash (bucket.push (info.type, newId))
              pure newId
        handle.putStrLn <| csvRow #[
          declName.toString,
          moduleName.toString,
          constantKind info,
          boolString declName.isInternal,
          boolString (isPrivateName declName),
          toString typeHash,
          toString typeId,
          toString info.type.getUsedConstantsAsSet.size
        ]
        count := count + 1
  handle.flush
  IO.println <| s!"Exported {count} NumStability statement fingerprints across " ++
    s!"{nextTypeId} exact expression-equivalence classes to {outDir}."

elab "run_numstability_statement_fingerprints" : command => do
  runFingerprints (← getEnv)

end NumStabilityAudit

run_numstability_statement_fingerprints
