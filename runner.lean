import Lean.Elab.Frontend


open Lean Elab

set_option linter.unusedVariables false
set_option diagnostics false


unsafe def checkProof (leanCode: String) (opts : Options := {})  : IO (Command.State × List Message × List InfoTree) := do

  -- search path for lean modules
  initSearchPath (← Lean.findSysroot)
  enableInitializersExecution

  -- a data structure containing the lean code to be executed
  let inputCtx := Parser.mkInputContext leanCode "<temp_execu_file>"

  -- obtains file headers and loads olean binary of imports
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx

  -- environments
  let commandState := (Command.mkState env messages opts)
  let commandState := { commandState with infoState.enabled := true }

  --  turn compiler outputs into useful into for the frontend
  let frontendState ← IO.processCommands inputCtx parserState commandState
  let s :=  Frontend.State.commandState frontendState

  pure (s, s.messages.toList, s.infoState.trees.toList)

unsafe def getMessage : IO Unit := do
  -- IO.println (← IO.Process.getPID)
  IO.println (← IO.getTID)
  IO.println "canceled?"
  IO.println (← IO.checkCanceled)


  let leanCode := "import Mathlib.Topology.Basic\n#check TopologicalSpace"
    -- Lean.Message contains rich compiler feedback
  let (cmdState, messages, trees) ← checkProof leanCode

  let messages ← messages.mapM fun m => do pure (← m.data.toString).trim

  IO.println messages


unsafe def runMultipleGetMessages : IO Unit := do
  -- Create array with 3 copies of getMessage
  let tasks ← (List.range 3).toArray.mapM fun i => do
    IO.println s!"Creating task {i + 1}"
    IO.asTask getMessage Task.Priority.dedicated

  for t in tasks do

    let a ← IO.hasFinished t
    let b ← IO.getTaskState t
    IO.println s!"Task has finished? {a}"
    IO.println s!"Task state {b}"
  -- Wait for all tasks to complete
  let results ← IO.wait <| ← IO.mapTasks (·.mapM (pure ·)) tasks.toList

  -- Process results
  match results with
  | .ok taskResults =>
    -- Handle successful completion of all tasks
    taskResults.forM fun result => match result with
      | .ok _ => IO.println "Task completed successfully"
      | .error e => IO.eprintln s!"Task error: {e}"
  | .error e =>
    IO.eprintln s!"Error waiting for tasks: {e}"

  IO.println "All tasks completed."

-- unsafe def main (_ : List String) : IO Unit := do
--   IO.println (← IO.Process.getPID)
--   let t ← IO.asTask (runMultipleGetMessages)
--   match t.get with
--   | .ok _ => pure ()
--   | .error e => IO.eprintln s!"Error: {e}"

  -- IO.println "+++++++++start"
  -- trees.forM fun t => do IO.println (← t.format)
  -- IO.println "+++++++++end"


-- #eval main []

unsafe def main (_ : List String) : IO Unit := do

  let stdin ← IO.getStdin
  let stdout ← IO.getStdout


    let arr ←   stdin.read 1000000
    let leanCode := String.fromUTF8! arr

    let (cmdState, messages, trees) ← checkProof leanCode

    let messages ← messages.mapM fun m => do pure (← m.data.toString).trim
    -- stdout.write (s!"{msg}".toUTF8)

    stdout.write s!"\n\n\n-----Question-----\n\n\n{leanCode}\n\n\n-----Result-----\n\n\n{messages}\n\n\n".toUTF8
