import Lean.Data.Json

open Lean

structure ProofBatch where
  id: Option Nat
  length: Option Nat
  batch: List String
deriving Inhabited, Repr, FromJson, ToJson

def main: IO Unit := do

  let startTime ← IO.monoMsNow

  let maxBytes := 1000000000

  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  -- let inputJson :=  (Json.parse (String.fromUTF8! (← stdin.read maxBytes))).toOption.get!
  let inputJson ← stdin.readJson maxBytes
  let inputProofs: ProofBatch := (fromJson? inputJson).toOption.get!


  IO.println s!"----Received proofs-----"
  IO.println (toString inputJson)
  IO.println "--------"


  for proof in inputProofs.batch do
    IO.println proof

  stdout.putStr "Output\n"
  stdout.writeJson (toJson inputProofs)
  stdout.flush

  let endTime ← IO.monoMsNow
  IO.println (s!"Time taken: {endTime - startTime} ms")
