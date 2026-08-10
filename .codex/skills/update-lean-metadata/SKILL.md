---
name: update-lean-metadata
description: Synchronize label-adjacent `\\lean{...}` and `\\leanok` commands in the latest LaTeX blueprint from the formalization statuses in `Status.md`. Use when asked to update, refresh, or reconcile Lean metadata in a repository containing `Status.md`, `Instructions.md`, and `blueprint/`.
---

# Update Lean Metadata

## Preconditions

Run from the repository root. Confirm that `Status.md`, `Instructions.md`, and `blueprint/` exist. Treat existing working-tree changes as user-owned: inspect the relevant diffs and avoid changing unrelated files.

Before editing the blueprint, make sure `Status.md` reflects the current formalization state according to `Instructions.md`. Do not infer a status from existing LaTeX metadata or from Lean declarations. If `Status.md` is stale, malformed, or inconsistent and the discrepancy cannot be resolved confidently, stop and create a diagnostic report instead of guessing.

The repository's canonical status spelling is:

- Definitions: `Todo` or `Completed`.
- Theorems: `Todo`, `Statement completed`, or `Proof completed`.

The source note uses `ToDo` in one place; interpret that as the repository's `Todo` status and preserve the canonical spelling in reports.

## Workflow

### 1. Select the source blueprint

Enumerate the `.tex` files in `blueprint/`.

- If filenames contain pass numbers such as `blueprint-pass5.tex`, select the file with the highest pass number. If multiple files have the same highest pass number, select the most recently modified one.
- If no filename contains a pass number, select the most recently modified `.tex` file.
- If no `.tex` file exists, stop; do not modify `Status.md` or create a metadata report without an input blueprint.

Record the selected path and selection rule. Treat an unclear filename, an unexpected tie, or a missing source label as a diagnostic issue.

### 2. Parse and match status entries

Read every entry in `Status.md` with the form:

```text
\\label{manuscript label}: [Status] (Lean: leanName, anotherLeanName) (date and time)
```

Use the exact label text between braces for matching. Do not match by substring, theorem title, or Lean name. Exclude `aux_` names from the Lean-name list; if they appear in `Status.md`, record the inconsistency and do not silently invent a replacement.

For each status entry, verify that the selected blueprint contains exactly one corresponding `\\label{...}`. Record missing or duplicate labels as issues.

### 3. Normalize label-adjacent metadata

Update only the metadata commands associated with each matched label. Do not change theorem statements, proofs, formatting outside the metadata, or the macro definitions at the top of the blueprint.

For each label, remove any existing adjacent `\\lean{...}` and `\\leanok` commands, then apply the canonical form:

- For `Todo`, add neither command, even if Lean names are listed in `Status.md`.
- For a non-`Todo` status with one or more Lean names, add exactly one `\\lean{...}` command containing the exact names from `Status.md` as a comma-separated list. Preserve names verbatim and do not add `aux_` names.
- For a non-`Todo` status with no Lean names, add no `\\lean` command.
- For `Proof completed`, add exactly one `\\leanok` command.
- For `Completed` or `Statement completed`, add no `\\leanok` command.

Place the resulting commands immediately after the label definition, preserving the surrounding LaTeX structure. Remove only commands attached to the current label; do not remove the global definitions such as `\\newcommand{\\lean}[1]{}` or `\\newcommand{\\leanok}{}`.

If a label's adjacent-command boundary is ambiguous, or if existing commands cannot be safely associated with one label, stop that edit and record the ambiguity rather than risking metadata for a neighboring label.

### 4. Verify the synchronization

Re-read the edited blueprint and verify every `Status.md` entry:

- `Todo` labels have no attached `\\lean` or `\\leanok` commands.
- Non-`Todo` labels have exactly the expected single `\\lean{...}` command when names are present.
- Only `Proof completed` labels have `\\leanok`.
- Every status label matched exactly once in the selected blueprint.

Check the diff to ensure only the selected blueprint's label-adjacent metadata changed. Do not run a broad formatter over the LaTeX file.

## Diagnostic reports

Create a report only when an issue was encountered. Write it at the repository root as `lean-metadata-diagnostic-YYMMDD-HHmm.md` using the current local date and time. Include:

- the selected blueprint and the status source;
- commands or editing actions performed;
- missing, duplicate, malformed, or ambiguous entries;
- the action taken or the reason processing stopped; and
- whether metadata changes were made and whether verification completed.

Do not create an empty report when synchronization is clear and successful. Summarize the selected blueprint, number of labels checked, metadata changes, and any report path at completion.
