# Instructions for the NCT formalization

This document records the general instructions for continuing the
formalization in `LeanNct`. User's instructions given in the chat may override these instructions.

## Scope and file organization

- The `blueprint` folder contains the draft manuscript which forms the basis of the formalization.
  It contains multiple versions in the format `blueprint-passN.tex` with different pass numbers `N`. You should only use the latest version, with the highest pass number `N`. Do not consult previous versions unless explicitly instructed to do so and in that case only for comparison, never as basis for formalization.
- Treat the manuscript's terms *theorem*, *lemma*, and *proposition* as
  synonymous.  Every corresponding Lean result must be declared with
  `theorem`.
- Formalize the manuscript's Introduction only as follows: define the
  twisted averages and state the main twisted theorem.  Ignore all other
  material in the Introduction.
- Skip the sections “from real to ergodic” and “overview” for now.
- Leave the main twisted theorem in `Introduction.lean` as `sorry`; do not
  delete it.  This is the sole intentionally unproved theorem.
- Formalize the top-level sections “Preliminaries” and “The main argument” and "Reduction to the main argument" in
  their existing respective folders.
- Work through each subsection in turn, reflecting the subsection structure with subfolder structure and
  creating one Lean file per leaf subsection, each
  with a reasonable CamelCase filename derived from its title (omitting
  articles), and put that subsection's formalization entirely in that file.
- All new work must be contained in a namespace beginning with `Codex` and
  mirroring the file structure, for example `Codex.Preliminaries.KKernels`.
- A lot of work has already been done, make sure to inspect the state of the formalization first and continue at the appropriate point.

## Faithfulness to the manuscript

- Define only notions occurring in the manuscript.  Do not invent new
  mathematical definitions.
- Stay as close and direct as possible to the manuscript's mathematical
  wording.  Conditions needed to avoid unintented weakening of statements due to Lean junk-value behaviour 
  should be added conservatively.
- The manuscript is not expected to contain errors at this point, but if you do find an error, fix it and continue formalizing, but
  report the error in the file 'ErrorReport.md'.
  Put date and timestamp on the errors found and specify which source line in blueprint.tex they occur in. Small gaps and omitted details in the reasoning
  that any beginning graduate student would be able to fill in do not qualify as errors. This is only about substantial definitive mathematical errors.
- Ignore LaTeX comments.  Resolve author annotations and mildly unfinished
  passages in the most reasonable way; often this means simply removing the
  annotation.
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
- Routine results whose manuscript proofs refer to a missing appendix must be
  proved directly; generate the routine proof as needed.
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

- Maintain `Status.md` continuously as work
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
- If you find errors/inconsistencies in `Status.md`, fix them.

## Workflow

- The first stage is to formalize all the statements and definitions, and where proofs are still missing and leave proofs as sorry. Update `Status.md` appropriately.
- Once all statements and definitions are formalized, you should focus on proving the theorems one by one, in the order they appear in the manuscript. You may locally parallelize independent pieces, but you should not try to do the whole formalization at once. Move on to the next theorem, or batch of theorems only when the previous is completely formalized.

## Verbatim user directives

The following preserves verbatim user messages from a previous pass for future reference. They are partially outdated and the above instructions have been user-updated, so the above instructions take precendence. You should not look at the following.

> Note in the following we use the terms theorem/lemma/proposition
> synonymously. In the lean formalization everythign should be "theorem".
> In the attached manuscript, faithfully formalize the following in the
> HarmonicAnalysis/nct folder: Introduction, in file Introduction.lean: defn
> of twisted averages, main twisted theorem (following the rules/conventions
> below), ignore everything else in the introduction. Skip "from real to
> ergodic". Skip "overview". Then formalize each of the top level sections
> "Preliminaries" and "The main argument" in their own respective folder
> (the folders exist already) and each file's code should be in a namespace
> beginning with "Codex" and then mirroring the file structure, for example
> Codex.Preliminaries.Kkernels.
>
> You should go through the subsections one by one, create a new lean file
> (resonably convert the subsection title to CamelCase, skip articles) for
> each subsection and place the formalization of that subsection entirely
> within that file. Your work should entirely be contained in the Codex
> namespace. You must only make definitions ocurring in the manuscript, do
> not make up your own definitions and stick as closely and directly as
> possible to the mathematical content of the manuscript wording (you may
> insert conditions needed to deal with Lean's junk values). When there are
> errors/inconsistencies, fix them conservatively obeying the style of the
> manuscript. Latex comments can be ignored, for author annotataions and
> slightly unfinished parts, choose the most reasonable way to resolve them
> (often author annotations can just be removed). Each definition, theorem
> (or proposition/lemma) must correspond to one or in some cases more than
> one lean definition/lean theorem. Create reasonable lean names for the
> definitions and theorems that are based on the labels of the corresponding
> manuscript definitions and theorems (or prop/lemma). Each lean statement or
> thm/lemma should have as its docstring the copy-pasted latex that it
> formalizes (removing any latex comments or author annotations). In cases
> where definitions/theorems are split into multiple lean statements, do it
> reasonably and only split as justified by the manuscript (i.e. if a theorem
> has multiple claims, you may split them into multiple theorems, appending a
> suitable suffix to the lean names for each piece and making the split
> absolutely clear in the docstrings). In reasonable cases, you may also
> introduce your own auxiliary theorems, in that case you must prepend the
> lean name with "aux_" and then whatever seems reasonable to you (use mathlib
> naming style or manuscript style). For those you must explain in the
> docstring what they are good for. If a definition or lemma is in mathlib
> (this will be very rarely the case, you don't need to search for it unless
> it is a very general defn or lemma and you reasaonbly expect it to be there),
> use the mathlib version. Many estimates come with explicit constants in this
> manuscript, for those constants define them as def C_(lean name of the
> theorem it relates to) := and then in terms of the recursive constants as
> specified.
>
> Here are specific instructions for some subsections:
> Preliminaries/Notation: Dont formalize notations where there is an
> appropriate mathlib notation, instead use that where possible. (in
> particular, check if tensor product is in mathlib, otherwise define it ad
> hoc for this formalization). The Gaussian and the notation for the Bracket
> bump you should define as in the manuscript. You are free to prove some
> "aux_" lemmas about the bracket bump as needed later on, but place them in
> this file.
>
> Preliminaries/WienerSpace: Skip this one, use the existing file
> HarmonicAnalysis/WienerSpace.lean (that file is not written with the above
> conventions yet though; please go back and insert the appropriate docstrings
> into that file for definitions and theorems that correspond to manuscript
> ones, and rename authors to "aux_" explaining why they are needed; you may
> slightly adjust implementations to match what you need in the remaining
> formalization, but the function space must remain as a predicate)
>
> Finally: For operators, avoid mathlibs linear operator machinery, instead
> define them as raw maps mapping functions to functions and describe the
> needed properties Prop-based. Lp norms should be implemented as eLpNorm
> whenever possible. Make sure to faithfully map the mathematical content of
> the statements into Lean, do not add assumptions other than those needed.
> Sometimes additional assumptions/conditions are needed to faithfully mirror
> the mathematical statements because of junk value semantics, the additional
> conditions needed are often MemLp sth, or that something is measurable. Make
> sure you add these when they are needed. Work through the entire manuscript
> and do not stop before you are completely finished (note the "main twisted
> theorem" is not proved yet on purpose, you may leave it as sorry, everything
> else is to be proved, for some routine statements proofs we refer to a
> missing appendix, those proofs were AI-generated, so please just generate
> them for yourself). If instructions are unclear, choose an interpretation.
> If you are missing some prerequisites unexpectedly, formalize them first,
> obeying the above rules.

> In the docstrings ONLY COPY-PASTE THE STATEMENTS, NOT THE PROOFS!

> hey here is some feedback: in many cases you made definitions and placed
> theorem statements in the docstring, that doesnt make sense. You should put
> the theorem statement into the docstring of the lean theorem only, in the
> docstrings of related definitions and auxiliary lemmas only put both the
> latex label of the related theorem and reference the lean name of the actual
> theorem.
> Also, to be clear, you must formalize every theorem in the manuscript
> completely with its proof! You made many files, but many of the key theorems
> are actually still missing, maybe you're planning to add them, just make sure
> you finish everything. The main theorem at the end of the main induction
> section should be sorry free when you are finished.

> IGNORE MAIN TWISTED THEOREM, FOCUS ON INDUCT POSITIVE TERMS

> by ignore i dont mean delete it.. i meant leave the main twisted theorem as
> sorry.

> I've added nct/blueprint.tex which also contains the draft i gave you
> initially in case you forget details due to compacting. In the manuscript
> there also sections "Reduction ..", "Supplements .." and "old .." you can
> ignore those for now. Also you should create a separate file "Status.md" in
> the nct folder: for each labeled latex deifnition and theorem in the
> manuscript it should state in one line its current status as "Todo" or
> "Complete" and insert the lean names for the corresponding formalization (do
> not include aux_ names). update this as you go. Organize the status file
> entries by section and subsection.

> "Completed" means the proof is complete in case of theorems, i.e.
> sorry-free, otherwise it is "Todo".

> The status md file entries should follow the following format:
> [Manuscript label]: [Status] (Lean: [lean name])
> it should also separate theorems from definitions. for theroems there are
> three possible status: Todo, Statement completed, Proof completed (apply the
> latter only if the proof is sorry free and depdns on standard axioms only).

> Also make a file nct/Instructions.md where you faithfully reproduce all
> instructions I have told you in a way that future agents (or yourself after
> compacting) can pick up the work.

> I need you to work more focusedly on actually completing theorems in the
> manuscript rather than getting carried away with building "foundations".
> Move one by one from top to bottom, follow the argument in the manuscript.

> The M level positivity and Cauchy--Schwarz results should be very easy
> applications of the K level ones; do not overthink them.
