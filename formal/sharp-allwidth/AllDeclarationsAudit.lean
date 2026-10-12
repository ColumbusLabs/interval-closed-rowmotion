import RowmotionSharpAllWidthFinalReviewed
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let whitelist : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if moduleName.toString.startsWith "Rowmotion" then
        checked := checked + 1
        if info.isUnsafe then throwError "Unsafe project declaration: {name}"
        if info matches .axiomInfo _ then throwError "Project axiom: {name}"
        let deps ← collectAxioms name
        for ax in deps do
          unless whitelist.contains ax do throwError "Disallowed axiom {ax} used by {name}"
        logInfo m!"AUDIT|{moduleName}|{name}|{deps}"
  logInfo m!"PASS: {checked} imported project declarations checked"
