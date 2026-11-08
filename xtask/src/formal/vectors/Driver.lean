/-
The driver of `cargo xtask formal vectors` for the replay module
`KrepiVectorsReplay`, whose name xtask writes in each place of this file:
a plain file that the stage of a comparison holds as `Vectors.lean`. For
each vector of the vector file, its first argument, it writes the id and
the output of `replay` for the input to the result file, its second; for
a line that is not an id, an input and an output, it writes an empty line,
so that the comparison names that vector.
-/
import KrepiVectorsReplay

def main (args : List String) : IO UInt32 := do
  let [vectors, results] := args | return 2
  let mut out := ""
  for line in ← IO.FS.lines vectors do
    if line.startsWith "#" then continue
    match line.splitOn "\t" with
    | [id, input, _] => out := out ++ id ++ "\t" ++ KrepiVectorsReplay.replay input ++ "\n"
    | _ => out := out ++ "\n"
  IO.FS.writeFile results out
  return 0
