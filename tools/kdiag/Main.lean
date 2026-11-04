import Export.Parse
import Lean
open Lean

-- The official replay (Lean.Replay) with one change: every declaration the
-- kernel checks is timed and its kernel unfold counter (Kernel.Diagnostics)
-- is printed: DIAG name us=.. unfolds=.. top=c1:n1,c2:n2,...
-- (the 6 most unfolded constants; KDIAG_TOP=n for n of them)
namespace Diag

structure Context where
  newConstants : Std.HashMap Name ConstantInfo

structure State where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}

abbrev M := ReaderT Context <| StateRefT State IO

def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

def addDecl (name : Name) (d : Declaration) : M Unit := do
  let env0 := (← get).env.resetDiag
  let t0 ← IO.monoNanosNow
  match env0.addDeclCore 0 0 d (cancelTk? := none) with
  | .ok env =>
    let t1 ← IO.monoNanosNow
    let dg := env.getDiagnostics
    let mut tot := 0
    let mut arr : Array (Name × Nat) := #[]
    for (n, c) in dg.unfoldCounter.toList do
      tot := tot + c
      arr := arr.push (n, c)
    let srt := arr.qsort (fun a b => a.2 > b.2)
    let k := ((← IO.getEnv "KDIAG_TOP").bind String.toNat?).getD 6
    let top := String.intercalate "," ((srt.toList.take k).map fun (n, c) => s!"{n}:{c}")
    IO.println s!"DIAG {name} us={(t1 - t0) / 1000} unfolds={tot} top={top}"
    modify fun s => { s with env := env }
  | .error ex => throw <| .userError (← ex.toMessageData {} |>.toString)

mutual
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    if (← get).pending.contains name then
      match ci with
      | .defnInfo   info => addDecl name (Declaration.defnDecl   info)
      | .thmInfo    info => addDecl name (Declaration.thmDecl    info)
      | .axiomInfo  info => addDecl name (Declaration.axiomDecl  info)
      | .opaqueInfo info => addDecl name (Declaration.opaqueDecl info)
      | .inductInfo info =>
        let lparams := info.levelParams
        let nparams := info.numParams
        let all ← info.all.mapM fun n => do pure <| ((← read).newConstants[n]!)
        for o in all do
          modify fun s =>
            { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
            pure ((← read).newConstants[n]!))
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstantsAsSet
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name
            type := ci.type
            ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        addDecl name (Declaration.inductDecl lparams nparams types false)
      | .ctorInfo _ => pure ()
      | .recInfo _ => pure ()
      | .quotInfo _ =>
        replayConstant `Eq
        addDecl name Declaration.quotDecl
      modify fun s => { s with pending := s.pending.erase name }

partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n
end

end Diag

def main (args : List String) : IO Unit := do
  let [inputPath] := args | throw <| .userError "Expected input file path."
  let handle ← IO.FS.Handle.mk inputPath .read
  let solution ← Export.parseStream (.ofHandle handle)
  let env ← Lean.mkEmptyEnvironment
  let mut constMap := solution.constMap
  constMap := constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  let kenv := env.toKernelEnv.enableDiag true
  let mut remaining : NameSet := {}
  for (n, _) in constMap.toList do
    remaining := remaining.insert n
  let act : Diag.M Unit := do
    for (n, _) in constMap.toList do
      Diag.replayConstant n
  let _ ← (act.run { newConstants := constMap }).run' { env := kenv, remaining }
  IO.println s!"Checked {constMap.size} declarations."
