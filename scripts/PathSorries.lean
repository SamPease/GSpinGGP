import GSpinGGP

/-!
Lists the declarations containing `sorry` that the main theorem `local_ggp` depends on, one per
line, prefixed by `PATH_SORRY`. Used by `scripts/check-assumptions.sh`.
-/

open Lean Elab Command

namespace GSpinGGP.PathSorries

/-- The user-facing declaration an auxiliary constant (`foo._proof_1`, `foo.match_1`, …) belongs to. -/
partial def root (n : Name) : Name :=
  let n := (privateToUserName? n).getD n
  if n.isInternalDetail && !n.getPrefix.isAnonymous then root n.getPrefix else n

partial def visit (env : Environment) (n : Name) : StateM (NameSet × NameSet) Unit := do
  if (← get).1.contains n then return
  modify fun s => (s.1.insert n, s.2)
  let some ci := env.find? n | return
  let mut used := ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then
    used := used ++ v.getUsedConstants
  if used.contains ``sorryAx then modify fun s => (s.1, s.2.insert (root n))
  for c in used do visit env c

run_cmd do
  let env ← getEnv
  let (_, (_, found)) := (visit env `GSpinGGP.local_ggp).run ({}, {})
  for n in found.toList.map toString |>.mergeSort do
    logInfo m!"PATH_SORRY {n}"

end GSpinGGP.PathSorries
