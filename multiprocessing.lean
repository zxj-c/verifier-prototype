-- set_option diagnostics true

-- def multiple (ms: List String): IO (List String) := do
--   ms.mapM fun m => do
--     let task ← IO.asTask (single m)
--     let res ← IO.wait task
--     match res with
--     | Except.ok v => pure v
--     | Except.error e => throw e

-- def multiple (ms : List String) : IO (List String) := do
--   -- Spawn all tasks concurrently
--   let tasks ← ms.mapM fun m => IO.asTask (single m)
--   -- Wait for all tasks to complete and collect their results
--   tasks.mapM fun task => do
--     let res ← IO.wait task
--     match res with
--     | Except.ok v => pure v
--     | Except.error e => throw e

def single (m: String): IO String := do
  let a ← IO.getTID
  IO.sleep (1000)
  return s!"tid {a} says {m}"

def multiple (ms : List String) : IO (List String) := do
  let tasks ← ms.mapM (fun m => IO.asTask <| single m)
  let result := ← IO.wait <| ← IO.mapTasks (·.mapM' (pure ·)) tasks

  match result with
     | .ok results => {
       let leanFeedbacks : List String ← results.mapM
         (fun res => do
           match res with
           | .ok ⟨m⟩ => return (String.mk m)
           | .error _ => return "error"
         )
       return leanFeedbacks
     }
     | .error _ => return []


def main : IO Unit := do
  let a ← multiple (List.range 100 |>.map toString)
  IO.println s!"{a}"

-- #eval! main
