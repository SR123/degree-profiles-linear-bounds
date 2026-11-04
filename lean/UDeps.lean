/-
Claude, 27 Sep 2026.  A small dependency checker for the audit: `#uses a b` reports whether the
constant `b` occurs in the transitive closure of the constants used by the type or value of `a`.
-/
import Lean

open Lean Elab Command

namespace ClaudeUndec

/-- The transitive closure of constants used by the type and value of `root`. -/
def depClosure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if visited.contains n then continue
    visited := visited.insert n
    match env.find? n with
    | some ci =>
      for c in ci.type.getUsedConstants do
        unless visited.contains c do stack := stack.push c
      match ci.value? (allowOpaque := true) with
      | some v =>
        for c in v.getUsedConstants do
          unless visited.contains c do stack := stack.push c
      | none => pure ()
    | none => pure ()
  return visited

/-- `#uses a b`: does `a` depend (transitively) on `b`? -/
elab "#uses " a:ident b:ident : command => do
  let env ← getEnv
  let na ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo a
  let nb ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
  let cl := depClosure env na
  logInfo m!"{na} uses {nb}: {cl.contains nb}   (closure size {cl.size})"

end ClaudeUndec
