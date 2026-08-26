# Instructions for the NCT formalization

This document records the general instructions for continuing the
formalization in `LeanNct`. User's instructions given in the chat may override these instructions.

## Scope and file organization

- The `blueprint` folder contains the draft manuscript which forms the basis of the formalization.
  The canonical manuscript file is `blueprint/blueprint.tex`.
- Treat the manuscript's terms *theorem*, *lemma*, and *proposition* as
  synonymous.  Every corresponding Lean result must be declared with
  `theorem`.
- Formalize the manuscript's Introduction only as follows: define the
  twisted averages and state the main twisted theorem.  Ignore all other
  material in the Introduction.
- Skip the sections “from real to ergodic” and “overview” for now.
- Leave the main twisted theorem in `Introduction.lean` as `sorry`; do not
  delete it.  
- Formalize the top-level sections “Preliminaries” and “The main argument” and "Reduction to the main argument" in
  their existing respective folders.
- Work through each subsection in turn, reflecting the subsection structure with subfolder structure and
  creating one Lean file per leaf subsection, each
  with a reasonable CamelCase filename derived from its title (omitting
  articles), and put that subsection's formalization entirely in that file.
- Every new non-temporary Lean source file under `LeanNct/` must be added as an
  explicit import in `LeanNct.lean` when it is created. Temporary scratch files
  must not be imported there.
- All new work must be contained in the single flat namespace `Auto`.
  Choose names that stay unambiguous
  across the whole `Auto` namespace.  Sub-namespaces are for structure
  projections and dot-notation only.
- A lot of work has already been done, make sure to inspect the state of the formalization first and continue at the appropriate point.

## Faithfulness to the manuscript

- Define only notions occurring in the manuscript.  Do not invent new
  mathematical definitions.
- Stay as close and direct as possible to the manuscript's mathematical
  wording.  Conditions needed to avoid unintented weakening of statements due to Lean junk-value behaviour 
  should be added conservatively.
- The manuscript is not expected to contain errors at this point, but if you do find an error, fix it and continue formalizing, but
  report the error in the file 'meta/ErrorReport.md'.
  Put date and timestamp on the errors found and specify which source line in blueprint.tex they occur in. Small gaps and omitted details in the reasoning
  that any beginning graduate student would be able to fill in do not qualify as errors. This is only about substantial definitive mathematical errors.
- When a displayed absolute constant or cardinality cannot be justified exactly but a directly proved bound is only slightly worse
  (normally by at most a factor of two), retain the proved Lean bound, record the discrepancy in `meta/ErrorReport.md`, and continue.
  Do not hold up the formalization for a sharper constant unless it is needed by a later stated estimate.
- Ignore LaTeX comments and author annotations. 
- Each labeled manuscript definition and theorem must correspond to one, or
  where justified by multiple claims, several Lean definitions/theorems.
- Use reasonable Lean names based on the source labels and names.  If one
  source theorem is split into several Lean theorems, make the split clear by
  suitable suffixes and matching docstrings.
- Use a mathlib definition or theorem when it already supplies the intended
  general notion or result.  Searching is only expected when that is a
  reasonable expectation, such as for a very general fact.
- Explicit constants in estimates must be defined as
  `def C_<lean theorem name> := ...`, with the specified recursive constants
  expressed as in the manuscript.
- Operators should generally be implemented as raw maps from functions to functions, not mathlib linear
  operators.  State needed operator properties propositionally. 
- Implement Lp norms as `eLpNorm` wherever possible.
- Do not add assumptions except those necessary for faithful Lean semantics;
  common justified additions include `MemLp` and measurability hypotheses.
- If an unexpectedly needed prerequisite is missing, formalize it first under
  these same rules.  If an instruction is unclear, choose a reasonable
  interpretation and continue.

## Proof obligations

- Formalize every theorem in scope completely, including a Lean proof.
- The final theorem at the end of the main induction section, especially the
  induction-on-positive-terms result, must be sorry-free when finished.
- You may formalize the statements of theorems first and leave them as sorry while working.
- A theorem counts as proof-complete only when its proof is sorry-free and
  depends on standard axioms only.

## Docstrings and auxiliary material

- For a source definition, its Lean definition may have the copied LaTeX
  definition in its docstring.
- Put the copied LaTeX **statement only**, never the proof, in the docstring
  of the Lean theorem that actually formalizes the source theorem. Same for definitions.
- Do not put a theorem statement in a related definition's docstring.
  Instead, a related definition's docstring should name the relevant LaTeX
  label and refer to the Lean theorem that formalizes it.
- The same rule applies to constants associated with a theorem.
- Reasonable auxiliary definitions and theorems are permitted only when they
  genuinely help the formalization.  Prefix their Lean names with `aux_`.
  Their docstrings must explain what they are for; if related to a source
  result, they should reference its source label and the actual public Lean
  theorem rather than copying that theorem's statement.

## Preliminaries-specific requirements

- In `Preliminaries/Notation`, do not formalize notation when mathlib has an
  appropriate notation.  In particular, use mathlib's tensor product if it
  is available; otherwise define it ad hoc only for this formalization.
- Define the Gaussian and the bracket-bump notation exactly as in the
  manuscript.  Auxiliary bracket-bump lemmas may be introduced as needed and
  must stay in the Notation file.

## Status tracking

- Maintain `meta/Status.md` continuously as work
  progresses.
- Include one entry for every labeled LaTeX definition and theorem in the
  scoped manuscript, organized by section and subsection.  Do not list
  `aux_` Lean names.
- Separate definitions from theorems.
- Every entry has exactly this shape:
  `\label{Manuscript label}: [Status] (Lean: [lean name]) (Date and time of update)`.
- Definitions use status `Todo` or `Completed`.
- Theorems use `Todo`, `Statement completed`, or `Proof completed`.
  Use `Proof completed` only for a sorry-free proof depending on standard
  axioms; otherwise use the appropriate earlier status.
- If you find errors/inconsistencies in `meta/Status.md`, fix them.
- Entries should be organized by the sections and subsections they occur in. After every section/subsection heading also include a line
for local path (treating LeanNct directory as home, and including filename if applicable) of the formalization of that section/subsection.
The format should be:
Lean file: PATH HERE

## Blueprint Lean metadata update

- Whenever you update a `meta/Status.md` entry, you should also update the corresponding Lean metadata in `blueprint/blueprint.tex` as follows:
find the appropriate label and inside of the def/thm environment update the metadata commands according to the instructions in `meta/UpdateLeanMetadata.md`.

## Workflow

- Before beginning, make sure you are aware of the current state of the formalization as recorded in `meta/Status.md`. Also familiarize yourself with the Lean files and the auxiliary setup left behind by previous agents. You should pick the work back up and avoid duplication of effort as much as possible.
- Then the first stage is to formalize all the statements and definitions, and where proofs are still missing and leave proofs as sorry. Update `meta/Status.md` appropriately.
- Once all statements and definitions are formalized, you should focus on proving the theorems one by one, in the order they appear in the manuscript. You may locally parallelize independent pieces, but you should not try to do the whole formalization at once. Move on to the next theorem, or batch of theorems only when the previous is completely formalized.
