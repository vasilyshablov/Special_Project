import Lean
open Lean

/-- Per-constant flags needing environment extensions:
`name \t isInstance \t isProjection \t isClass \t typeObjs`. -/
unsafe def main (args : List String) : IO Unit := do
  let root := (args.headD "Mathlib").toName
  let out := args.getD 1 "flags.tsv"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := root }] {} (trustLevel := 1024) (loadExts := true)
  let h ← IO.FS.Handle.mk out .write
  for (nm, ci) in env.constants.map₁.toList do
    let inst := Meta.isInstanceCore env nm
    let proj := (env.getProjectionFnInfo? nm).isSome
    let cls := isClass env nm
    let tobjs ← ci.type.numObjs
    h.putStrLn s!"{nm}\t{if inst then 1 else 0}\t{if proj then 1 else 0}\t{if cls then 1 else 0}\t{tobjs}"
