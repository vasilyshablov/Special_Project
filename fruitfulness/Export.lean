import Lean
open Lean

/-- Export the constant-dependency graph of an imported environment.
One line per constant:
`name \t kind \t module \t valueObjs \t valueDeps \t typeDeps` (deps space-separated). -/
def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "ax"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "ind"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def main (args : List String) : IO Unit := do
  let root := (args.headD "Mathlib").toName
  let out := args.getD 1 "graph.tsv"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := root }] {} (trustLevel := 1024)
  let h ← IO.FS.Handle.mk out .write
  let mut n := 0
  for (nm, ci) in env.constants.map₁.toList do
    let mod := match env.getModuleIdxFor? nm with
      | some i => (env.header.moduleNames[i.toNat]!).toString
      | none => "?"
    let (objs, vdeps) ← match ci.value? (allowOpaque := true) with
      | some v => do pure ((← v.numObjs), v.getUsedConstants)
      | none => pure (0, #[])
    let tdeps := ci.type.getUsedConstants
    let ss (a : Array Name) := " ".intercalate (a.toList.map toString)
    h.putStrLn s!"{nm}\t{kindOf ci}\t{mod}\t{objs}\t{ss vdeps}\t{ss tdeps}"
    n := n + 1
  IO.println s!"exported {n} constants"
