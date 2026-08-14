# Lean metadata diagnostic — 2026-08-14 08:10 PDT

Sources checked: `Status.md` and `blueprint/blueprint.tex`.

I updated the unambiguous completed entry for
`lem:shortlongftc_reduction` to `Proof completed` with Lean declaration
`shortLongFtcReduction`, and inserted its adjacent `\leanok` marker in the
blueprint.  The label occurs exactly once in the blueprint and its resulting
metadata is verified.

I also audited all 209 status labels for exact blueprint-label occurrence and
adjacent metadata.  Most reported textual differences are harmless formatting:
the status file separates multiple Lean names with `, ` while existing
blueprint commands use `,`.  Three pre-existing entries require a separate
decision before a global synchronization can safely rewrite them:

- `standard bump properties` is marked `Proof completed` with Lean names in
  `Status.md`, but has no adjacent `\lean{...}` or `\leanok` in the blueprint.
- `lem:cpair` is marked `Proof completed` with Lean name `existsUniversalPair`,
  but has no adjacent metadata commands in the blueprint.
- `lem:bumpbasic` is marked `Proof completed` with Lean name `bumpBasic`, but
  has no adjacent metadata commands in the blueprint.

No unrelated metadata was changed.  A future full metadata reconciliation
should resolve whether those three omissions are intentional before modifying
their blueprint entries.
