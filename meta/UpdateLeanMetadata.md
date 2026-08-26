Here are instructions on how to update Lean metadata in the blueprint.

- First make sure meta/Status.md is up to date with the formalization, see meta/Instructions.md.
- Then go through each entry in meta/Status.md and find it in `blueprint/blueprint.tex`.
Then you update the \lean and \leanok commands next to that label in the latex file as follows (these commands may or may not be present already):
If the status is "ToDo", then remove \lean and \leanok commands from that label if they are present (even if there are Lean names listed in meta/Status.md).
If the status is not "ToDo", the do the following:
  - If Lean names are listed in meta/Status.md for that label, then make sure there is exactly one \lean{..} command after the label is defined in the tex file which must contain the exact Lean names as a comma-separated list in the argument (i.e. add it if its not there).
  - If the status is "Proof completed" (i.e. it is a theorem with a complete proof) then there should be a \leanok command. If the status is not "Proof completed", then there should not be a \leanok command.
- Generate a diagonstic report file with the current date and time stamp in the filename that details any issues you ran into and what action you took in those cases (something was unclear). If everything was clear with no issues, you do not need to generate this report file.


