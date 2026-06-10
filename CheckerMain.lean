import Consensus.Checker

open Consensus.Checker

/-- Parse a comma-separated list of naturals (blanks dropped). -/
def parseNats (s : String) : List Nat :=
  (s.splitOn ",").filterMap (fun t => t.toNat?)

/-- Parse "a=value,b=value" into a vote record. -/
def parseVotes (s : String) : Votes :=
  (s.splitOn ",").filterMap (fun kv =>
    match kv.splitOn "=" with
    | [a, v] => (a.toNat?).map (fun n => (n, v))
    | _ => none)

/-- args: <members> <votes> <value> <voters>. Prints ALLOW or DENY (fail-closed). -/
def main (args : List String) : IO Unit := do
  match args with
  | [m, vs, value, voters] =>
    let ok := validB (parseNats m) (parseVotes vs) ⟨value, parseNats voters⟩
    IO.println (if ok then "ALLOW" else "DENY")
  | _ => IO.println "DENY"
