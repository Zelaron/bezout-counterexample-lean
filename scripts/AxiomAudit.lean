import BezoutCounterexample
import Lean.Util.CollectAxioms

/-! Audit all constants defined in project modules, including generated helpers.
This file inspects the environment; it does not add mathematical assumptions. -/

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut used : Array Name := #[]
  let mut rows : Array Json := #[]
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := moduleNames[idx.toNat]!
      if (`BezoutCounterexample).isPrefixOf mod then
        if ci matches .axiomInfo _ then
          throwError "Project axiom: {name}"
        let axioms ← collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Unexpected axiom {ax} in {name}"
          unless used.contains ax do
            used := used.push ax
        checked := checked + 1
        rows := rows.push (Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson mod.toString),
          ("axioms", toJson (axioms.map Name.toString))])
  unless checked > 1000 do
    throwError "Only {checked} project declarations found; incomplete import?"
  liftIO <| IO.FS.writeFile "verification/declaration-axioms.json" (Json.pretty (toJson rows))
  logInfo m!"PASS: audited {checked} project declarations. Axioms used: {used}"

#print axioms BezoutCounterexample.main_theorem
#print axioms BezoutCounterexample.key_obstruction
#print axioms BezoutCounterexample.ReesData.quotientSRingEquiv
#print axioms BezoutCounterexample.inv_map_eq_of_localization_polynomial
#check BezoutCounterexample.main_theorem
#check BezoutCounterexample.key_obstruction
