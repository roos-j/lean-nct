---
name: quick-comparator
description: Validate a Lean project's Challenge/Solution comparator pair locally with the bundled QuickComparator helper. Use for a fast declaration and axiom compatibility check; it does not replace the official Comparator.
---

# Quick Comparator

Run the bundled `assets/QuickComparator.lean` from the root of the target Lean project. The helper reads `comparator.json` from the working directory and dynamically imports the configured Challenge and Solution modules into separate Lean environments.

## Workflow

1. Confirm that the target directory contains `comparator.json`, then read its `challenge_module` and `solution_module` values.
2. Build both named modules so their `.olean` files are current. For example, a configuration naming `Challenge` and `Solution` requires:

   ```powershell
   lake build Challenge Solution
   ```

3. From that same target directory, run:

   ```powershell
   lake env lean "<this-skill-directory>/assets/QuickComparator.lean"
   ```

4. Treat `Quick Comparator passed.` as a successful local check. Report build or helper errors directly, including any unavailable Lean toolchain or dependencies.

## Boundaries

- Use this skill's bundled asset; do not invoke or depend on the `prepare-for-palomar` skill at run time.
- The helper compares configured theorem signatures, reachable statement declarations, and Solution axioms against `comparator.json`.
- This is advisory local validation only. It does not replace the official Comparator, its sandbox, or NanoDa replay.
