import REPL
import Lean.Elab.Frontend

open Lean Elab

-- TacticInfo contains before and after goals

def getMessageList (state: Command.State) : IO (List String) := do

    state.messages.toList.mapM (λ x => do pure (← x.data.toString).trim)

def ppMessages (state: Command.State) : IO Unit := do

    let messages: List String ← getMessageList state

    for msg in messages do
        IO.println s!"-----"
        IO.println msg

def ppInfoTree (infoTree: InfoTree) : IO Unit := do

    /-

    InfoTree documentation
    https://leanprover-community.github.io/mathlib4_docs/Lean/Elab/InfoTree/Types.html#Lean.Elab.InfoTree

    -/

    let json ← infoTree.toJson none
    IO.println (toString json)

def initHeader (codeString : String): IO Command.State := do

    let options := {}

    let inputCtx := Parser.mkInputContext codeString "header file"

    -- let (header, parserState, messages) ← Parser.parseHeader inputCtx
    let (header, _, messages) ← Parser.parseHeader inputCtx
    let (headerEnvironment, messages) ← processHeader header options messages inputCtx
    let headerState := Command.mkState headerEnvironment messages options
    let headerState := { headerState with infoState.enabled := true } -- header state

    return headerState
    -- process data
    -- pure (← IO.processCommands inputCtx parserState commandState <&> Frontend.State.commandState)

def verify (codeString : String) (headerState: Command.State) : IO Command.State := do

    let inputCtx := Parser.mkInputContext codeString "code file"
    let parserState : Parser.ModuleParserState := {}

    pure (← IO.processCommands inputCtx parserState headerState <&> Frontend.State.commandState)


def run (id: Nat) : IO Unit := do

    let codeStringList := ["import Mathlib", "import Mathlib.Topology.Basic \n #check TopologicalSpace", "#eval 1+1",  "theorem a: 1 = 1 :=by sorry", "theorem a: 1 = 1 :=by rfl", "#ev 2+"]
    let codeString := codeStringList[id]!
    let options := {}

    let inputCtx := Parser.mkInputContext codeString "file"
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    let (env, messages) ← processHeader header options messages inputCtx
    let commandState := Command.mkState env messages options
    let commandState := { commandState with infoState.enabled := true }

    let state ← IO.processCommands inputCtx parserState commandState <&> Frontend.State.commandState

    -- for m in state.messages.toList do
    --     IO.println s!"----- Severity -----"
    --     match m.severity with
    --     | MessageSeverity.error => IO.println "Error"
    --     | MessageSeverity.warning => IO.println "Warning"
    --     | MessageSeverity.information => IO.println "Info"
    --     IO.println (← m.data.toString).trim


    let mut c := 0
    let L := state.infoState.trees.toList.length
    for tree in state.infoState.trees.toList do

        c := c + 1
        IO.println s!"----- InfoTree {c} of {L} -----"

        -- env.header.imports.toList.forM (λ x => do
        --     IO.println s!"{x}")
        IO.println env.header.imports.toList

        tree.findTacticNodes.toArray.forM (λ (p, q, r) => do
            IO.println (toString (← q.ppGoals r)))

        IO.println s!"----------"
        ppInfoTree tree

def run1 : IO Unit := do
    let id := 2
    let codeStringList := ["import Mathlib.Topology.Basic \n #check TopologicalSpace", "#check TopologicalSpace", "#eval 1+1", "theorem a: 1 = 1 :=by rfl", "#ev 2+"]
    let codeString := codeStringList[id]!

    let headerState ← initHeader "import Mathlib"

    let state ← verify codeString headerState

    ppMessages state


#eval timeit "Main function" (run 1)
