import LeanChecker

/-! Sequential wrapper around the Lean distribution’s kernel replay tool.
This checks precisely the modules listed by scripts/check.py, one at a time.
No mathematical declarations or assumptions are introduced. -/

open Lean

unsafe def replayProject : IO Unit := do
  initSearchPath (← findSysroot)
  let modules ← IO.FS.lines "verification/module-order.txt"
  for mod in modules do
    IO.println s!"Replaying {mod}"
    replayFromImports mod.toName
  IO.println s!"PASS: kernel replay of {modules.size} project modules"

#eval replayProject
