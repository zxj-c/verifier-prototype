import Lean.Elab.Frontend
import Lean.Data.Json
import Mathlib

open Lean Elab

set_option linter.unusedVariables false

-- unsafe def checkProofCore (leanCode: String) (opts : Options := {})  : IO (Command.State × List Message × List InfoTree) := do

--   /-
--     Core function for proof checking
--   -/

--   -- search path for lean modules
--   initSearchPath (← Lean.findSysroot)
--   enableInitializersExecution

--   -- a data structure containing the lean code to be executed
--   let inputCtx := Parser.mkInputContext leanCode "<temp_execu_file>"

--   -- obtains file headers and loads olean binary of imports
--   let (header, parserState, messages) ← Parser.parseHeader inputCtx
--   let (env, messages) ← processHeader header opts messages inputCtx

--   -- environments
--   let commandState := (Command.mkState env messages opts)
--   let commandState := { commandState with infoState.enabled := true }

--   --  turn compiler outputs into useful into for the frontend
--   let frontendState ← IO.processCommands inputCtx parserState commandState
--   let s :=  Frontend.State.commandState frontendState

--   pure (s, s.messages.toList, s.infoState.trees.toList)


def initHeader (header: String := "import Mathlib\n") (opts : Options := {}) : IO (Parser.ModuleParserState × Command.State) := do
  -- initSearchPath (← Lean.findSysroot)
  -- enableInitializersExecution

  -- a data structure containing the lean code to be executed
  let inputCtx := Parser.mkInputContext header "<temp_execu_file>"

  -- obtains file headers and loads olean binary of imports
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx

  -- environments
  let commandState := (Command.mkState env messages opts)
  let commandState := { commandState with infoState.enabled := true }

  --  turn compiler outputs into useful into for the frontend
  -- let frontendState ← IO.processCommands inputCtx parserState commandState
  -- let s :=  Frontend.State.commandState frontendState

  -- pure s

  pure (parserState, commandState)

def runCode (leanCode: String) (headerInitialization: IO (Parser.ModuleParserState × Command.State))  : IO String := do

  -- create a context for lean code
  let inputCtx := Parser.mkInputContext leanCode "<temp_execu_file>"
  let (parserState, commandState) ← headerInitialization

  let frontendState ← IO.processCommands inputCtx parserState commandState
  let s :=  Frontend.State.commandState frontendState

  let messages ← s.messages.toList.mapM fun m => do pure (← m.data.toString).trim
  let tid ← IO.getTID
  return s!"{messages} from {tid}"


unsafe def getAllMessages (leanCodeList : List String) : IO (List String) := do
  let headerInitialization ← initHeader "import Mathlib"

  let tasks ← leanCodeList.mapM (fun c => IO.asTask <| runCode c (pure headerInitialization))
  let result := ← IO.wait <| ← IO.mapTasks (·.mapM' (pure ·)) tasks

  match result with
     | .ok results => {
       let leanFeedbacks : List String ← results.mapM
         (fun res => do
           match res with
           | .ok ⟨m⟩ => return (String.mk m)
           | .error _ => return "Exception error from getAllMessages function!"
         )
       return leanFeedbacks
     }
     | .error _ => return []

unsafe def main (_ : List String) : IO Unit := do

  initSearchPath (← Lean.findSysroot)
  enableInitializersExecution

  let stdout ← IO.getStdout

  -- let leanCode := "import Mathlib.Topology.Basic\n#check TopologicalSpace"
  let leanCode := "import Mathlib\n #check TopologicalSpace"


  -- let a ← Json.arr (← infoTrees.mapM fun t => t.toJson none).toArray


  let mut leanList ← pure (List.replicate 3 leanCode)
  let msg ← getAllMessages leanList --[leanCode, leanCode]
  stdout.write (String.toUTF8 s!"\n{msg}\n")
  -- stdout.write (String.toUTF8 s!"\n{l}\n")

#eval! main []
