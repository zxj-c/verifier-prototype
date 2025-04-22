import Lean.Elab.Frontend
import Lean.Data.Json
import Lean.Language.Basic

open Lean Elab

set_option linter.unusedVariables false
set_option diagnostics true


def checkProof (leanCode: String) (opts : Options := {})  : IO (List Message) := do


  initSearchPath (← Lean.findSysroot)
  -- let mathlibCtx = "import Mathlib"


  -- a data structure containing the lean code to be executed
  let inputCtx := Parser.mkInputContext leanCode "<temporary file>"

  -- obtains file headers and loads olean binary of imports
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header opts messages inputCtx

  -- environments
  let commandState := (Command.mkState env messages opts)
  let commandState := { commandState with infoState.enabled := true }

  --  turn compiler outputs into useful into for the frontend
  let frontendState ← IO.processCommands inputCtx parserState commandState
  let s :=  Frontend.State.commandState frontendState

  -- pure (s, s.messages.toList, s.infoState.trees.toList)
  pure s.messages.toList




def main : IO Unit := do

  let leanCode := "import Mathlib.Topology.Basic \n #check TopologicalSpace \n #check 2+2 \n \n \n \n  #check 2+20"
  -- let messages ← checkProof leanCode
  -- let messages ← messages.mapM fun m => do pure (← m.data.toString).trim

  -- IO.println messages

  let inputCtx := Parser.mkInputContext leanCode "temp_execu.file"

  -- IO.println "------"
  -- IO.println inputCtx.input
  -- IO.println "------"
  -- IO.println inputCtx.fileName
  -- IO.println "------"
  -- IO.println inputCtx.fileMap.source
  -- IO.println "------"
  -- IO.println inputCtx.fileMap.positions
  -- IO.println "------"
  -- IO.println "------"

  let (header, parserState, messages) ← Parser.parseHeader inputCtx

  -- IO.println "------"
  -- IO.println header
  -- IO.println "------"
  -- IO.println parserState.pos
  -- IO.println parserState.recovering
  -- let strs ← messages.reported.toList.mapM (·.toString)
  -- IO.println strs
  -- IO.println ( messages.reported.toList.)

  let (env, messages) ← processHeader header {} messages inputCtx
  -- IO.println "------"

  -- IO.println env.imports
  -- IO.println env.allImportedModuleNames
  -- env.displayStats

  let commandState := (Command.mkState env messages {})
  let commandState := { commandState with infoState.enabled := true }

  -- IO.println "===="
  -- IO.println commandState.infoState.trees.stats
  -- IO.println "===="
  -- IO.println s!"Info trees: {commandState.infoState.trees.size} trees"
  let frontendState ← IO.processCommands inputCtx parserState commandState
  IO.println frontendState.cmdPos
  IO.println frontendState.commands
  -- IO.println frontendState.commandState

    let s :=  Frontend.State.commandState frontendState

  let t := s.infoState.trees.toList
  -- for tree in s.infoState.trees.toList do
  --     let fmt ← tree.format
  --     IO.println fmt.pretty
  --     IO.println "---"


  let messages ← s.messages.toList.mapM fun m => do pure (← m.data.toString).trim

  IO.println messages


#eval! main
