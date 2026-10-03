import Verification.Solution
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/- Transitive axiom audit of every declaration owned by a project module, including private/generated
names and vendored Sturm declarations whose namespaces are not QuantumBehaviors. -/
open Lean Elab Command
set_option maxRecDepth 32768
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let roots := (env.constants.toList.map Prod.fst).filter fun name =>
    match env.getModuleIdxFor? name with
    | none => false
    | some idx =>
      let moduleName := env.header.moduleNames[idx.toNat]!
      moduleName == `QuantumBehaviors || moduleName.toString.startsWith "QuantumBehaviors." ||
        moduleName == `Verification.Solution
  unless roots.length > 0 do
    throwError "No project declarations were loaded"
  for name in roots do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration is missing from the checked kernel environment: {name}"
    match env.find? name with
    | some (.axiomInfo _) => throwError "Project-owned axiom declaration: {name}"
    | _ => pure ()
  let action : CollectAxioms.M Unit := roots.forM CollectAxioms.collect
  let (_, result) := (action.run env).run {}
  let unexpected := result.axioms.filter fun name =>
    name != ``propext && name != ``Classical.choice && name != ``Quot.sound
  unless unexpected.isEmpty do
    throwError "Unexpected transitive axioms: {unexpected}"
  let names := roots.toArray.qsort Name.lt
  let rows := names.toList.map fun name =>
    let idx := (env.getModuleIdxFor? name).get!
    s!"{env.header.moduleNames[idx.toNat]!}\t{name}"
  liftIO <| IO.FS.createDirAll ".verification"
  liftIO <| IO.FS.writeFile ".verification/axiom-roots.tsv"
    (String.intercalate "\n" rows ++ "\n")
  logInfo m!"GLOBAL_AXIOM_AUDIT_PASS roots={roots.length} axioms={(result.axioms.qsort Name.lt).toList}"
