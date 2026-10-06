import NumStability
import Lean
import Lean.DeclarationRange
import Lean.DocString
import Lean.Class
import Lean.Structure
import Lean.Meta.Instances

/-!
Schema `numstability-declaration-metadata/v1`.

This read-only extractor augments the byte-recovered declaration graph with
Lean's reserved-name flag, safety metadata, direct declaration source ranges,
and raw docstring presence. It deliberately does not equate a non-reserved
name or source range with explicit human authorship; a companion classifier
checks the exact source token at the exported selection range.
-/

open Lean Elab Command

namespace NumStabilityAuditCurrent

private def projectPrefix : Name := `NumStability

private def isProjectModule (moduleName : Name) : Bool :=
  projectPrefix.isPrefixOf moduleName

private def csvCell (value : String) : String :=
  "\"" ++ value.replace "\"" "\"\"" ++ "\""

private def csvRow (values : Array String) : String :=
  String.intercalate "," (values.toList.map csvCell)

private def boolString (value : Bool) : String :=
  if value then "true" else "false"

private def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def reducibilityKind : ConstantInfo → String
  | .defnInfo info =>
      match info.hints with
      | .abbrev => "abbrev"
      | .opaque => "opaque_hint"
      | .regular _ => "regular"
  | _ => "not_definition"

private def moduleNameFor? (env : Environment) (declName : Name) : Option Name := do
  let moduleIdx ← env.getModuleIdxFor? declName
  env.header.moduleNames[moduleIdx.toNat]?

private def rangeFields (ranges? : Option DeclarationRanges) : Array String :=
  match ranges? with
  | none => #["", "", "", "", "", "", "", ""]
  | some ranges => #[
      toString ranges.range.pos.line,
      toString ranges.range.pos.column,
      toString ranges.range.endPos.line,
      toString ranges.range.endPos.column,
      toString ranges.selectionRange.pos.line,
      toString ranges.selectionRange.pos.column,
      toString ranges.selectionRange.endPos.line,
      toString ranges.selectionRange.endPos.column
    ]

private def writeMetadata (env : Environment) : CommandElabM Unit := do
  let outDirString ← liftIO <| IO.getEnv "NUMSTABILITY_AUDIT_OUT"
  let outDir : System.FilePath := outDirString.getD "audit/latest"
  liftIO <| IO.FS.createDirAll outDir
  let outputPath := outDir / "declaration_metadata.csv"
  let handle ← liftIO <| IO.FS.Handle.mk outputPath .write
  liftIO <| handle.putStrLn <| csvRow #[
    "name", "module", "kind", "is_internal", "is_private",
    "is_reserved_name", "has_body", "is_unsafe", "is_partial",
    "is_instance", "is_structure", "is_class", "reducibility_kind",
    "has_docstring", "range_start_line", "range_start_column",
    "range_end_line", "range_end_column", "selection_start_line",
    "selection_start_column", "selection_end_line", "selection_end_column"
  ]
  let mut count := 0
  let mut reservedCount := 0
  let mut documentedCount := 0
  for moduleIdx in [0:env.header.moduleNames.size] do
    let moduleName := env.header.moduleNames[moduleIdx]!
    if isProjectModule moduleName then
      let moduleData := env.header.moduleData[moduleIdx]!
      for declName in moduleData.constNames do
        if moduleNameFor? env declName != some moduleName then
          continue
        let some info := env.find? declName | continue
        let reserved := isReservedName env declName
        let directRanges? ← findDeclarationRangesCore? declName
        let hasDocstring := (← liftIO <| findSimpleDocString? env declName).isSome
        let fields := #[
          declName.toString,
          moduleName.toString,
          constantKind info,
          boolString declName.isInternal,
          boolString (isPrivateName declName),
          boolString reserved,
          boolString (info.value? true).isSome,
          boolString info.isUnsafe,
          boolString info.isPartial,
          boolString (Meta.isInstanceCore env declName),
          boolString (Lean.isStructure env declName),
          boolString (Lean.isClass env declName),
          reducibilityKind info,
          boolString hasDocstring
        ] ++ rangeFields directRanges?
        liftIO <| handle.putStrLn <| csvRow fields
        count := count + 1
        if reserved then reservedCount := reservedCount + 1
        if hasDocstring then documentedCount := documentedCount + 1
  liftIO <| handle.flush
  liftIO <| IO.println <| s!"Metadata schema numstability-declaration-metadata/v1: " ++
    s!"{count} declarations, {reservedCount} reserved, " ++
    s!"{documentedCount} documented; output {outputPath}."

elab "run_numstability_declaration_metadata" : command => do
  writeMetadata (← getEnv)

end NumStabilityAuditCurrent

run_numstability_declaration_metadata
