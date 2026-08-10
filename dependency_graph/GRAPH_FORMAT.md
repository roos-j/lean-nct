# NCT dependency graph JSON format 2.0.0

`graph.json` is the only interchange document between the LaTeX extractor and the HTML renderer. The renderer does not read the LaTeX source.

The normative machine-readable definition is [`graph.schema.json`](graph.schema.json), using JSON Schema Draft 2020-12. This document states the additional semantic invariants that JSON Schema alone does not express.

## Top-level object

```json
{
  "schema": "nct-dependency-graph",
  "schema_version": "2.0.0",
  "source": {},
  "settings": {},
  "special_sections": {},
  "status_catalog": [],
  "reference_catalog": {},
  "sections": [],
  "nodes": [],
  "edges": [],
  "diagnostics": {},
  "statistics": {}
}
```

## Source and reference numbering

`source` records the input file name and SHA-256 hash, extractor version, generation time, and the mechanism used to obtain LaTeX reference numbers.

```json
{
  "latex_file": "blueprint.tex",
  "sha256": "…",
  "generated_at": "2026-08-10T00:00:00+00:00",
  "parser": {
    "name": "latex_to_graph_json",
    "version": "2.0.0"
  },
  "reference_numbering": {
    "mode": "compile",
    "engine": "latexmk",
    "succeeded": true,
    "aux_file": "blueprint.aux",
    "labels_total": 751,
    "return_code": 0
  }
}
```

Unless `--aux-file` is supplied, the extractor runs `latexmk`, reads the generated `.aux` file, and stores every `\newlabel` entry in `reference_catalog`. A catalog entry has:

```json
{
  "number": "4.17",
  "number_latex": "4.17",
  "page": "31",
  "title": "Displayed title",
  "anchor": "theorem.4.17",
  "extra": "",
  "node_id": "lem:example"
}
```

`node_id` is the exact graph node label when the LaTeX label identifies a theorem or definition node; otherwise it is `null`.

## Settings

```json
{
  "grouping_granularity": "subsection",
  "include_definitions": false,
  "rank_direction": "BT",
  "public_opacity": 1.0,
  "private_opacity": 0.5,
  "section_opacity": 0.15,
  "subsection_opacity": 0.09,
  "show_sidebar": true,
  "show_legend": true,
  "show_document_hierarchy": true,
  "default_status": "can_state"
}
```

`grouping_granularity` is one of `none`, `section`, or `subsection`. The HTML renderer computes a different node layout for every hierarchy value and for both definition-visibility values. Changing the setting therefore switches geometry rather than merely hiding cluster rectangles.

## Section hierarchy

`sections` is a recursive array. Each entry has an exact internal ID, heading level, plain and LaTeX titles, LaTeX-generated number, optional `\label`, source line, and child headings.

```json
{
  "id": "section:sec:prelim",
  "kind": "section",
  "level": 1,
  "title_tex": "Preliminaries",
  "title": "Preliminaries",
  "display_title": "4. Preliminaries",
  "number": "4",
  "label": "sec:prelim",
  "synthetic": false,
  "starred": false,
  "role": null,
  "ordinal": 7,
  "source_line": 1240,
  "children": []
}
```

`special_sections.introduction_section_id` identifies the first actual section. Its `role` is `introduction`. Every node in this section is public by convention, and the hierarchical renderer places the Introduction section strictly above all other section boxes.

In subsection view, the subsection cells form a rectangular partition of the usable interior of the section box. Outer padding and fixed gutters are left between cells. Material directly under a section is assigned to a synthetic cell whose visible caption is empty.

## Nodes

A theorem-like environment is normalized to `kind: "theorem"`; a definition is `kind: "definition"`. The `environment` field preserves the source environment name.

```json
{
  "id": "lem:example",
  "label": "lem:example",
  "number": "4.17",
  "kind": "theorem",
  "environment": "lemma",
  "environment_name": "Lemma",
  "title_tex": "Example lemma",
  "title": "Example lemma",
  "status": "can_state",
  "visibility": "public",
  "visibility_reason": "used outside its section",
  "lean_names": [],
  "uses": ["def:input"],
  "used_by": ["thm:output"],
  "location_id": "section:sec:prelim",
  "section_id": "section:sec:prelim",
  "subsection_id": null,
  "section_path": ["section:sec:prelim"],
  "section_titles": ["Preliminaries"],
  "section_numbers": ["4"],
  "statement_latex": "…",
  "statement_html": "…",
  "statement_references": [],
  "statement_custom_macros_expanded": [],
  "statement_unexpanded_custom_macros": [],
  "source": {
    "line_start": 1260,
    "line_end": 1278
  }
}
```

The node ID and label are the exact `\label{...}` contents from the source. `lean_names` is an ordered list and may contain zero, one, or several Lean declaration names.

### Visibility invariant

A node is `public` precisely when either:

1. it belongs to the Introduction section; or
2. at least one node in a different top-level section uses it.

Every other node is `private`, including an unused node. The entire rendered node group—not merely its border—receives the corresponding opacity.

### Statement fields

`statement_latex` contains the theorem or definition body after recursively expanding project macros declared through supported `\newcommand`, `\renewcommand`, `\providecommand`, `\def`, and `\DeclareMathOperator` declarations. Graph metadata commands, labels, and author annotations are omitted.

`statement_html` is a presentation form for the detail panel. Mathematical fragments remain as `\(...\)` and `\[...\]` for MathJax. Every `\ref` and `\eqref` is replaced by the number read from the compiled `.aux` file:

- when the target is a graph node, the number is an `nct-node:` link;
- otherwise the same generated number appears as ordinary unlinked text.

A statement reference entry is:

```json
{
  "command": "ref",
  "label": "lem:input",
  "number": "4.12",
  "display": "4.12",
  "target_node_id": "lem:input"
}
```

For `\eqref`, `display` includes parentheses. `target_node_id` is `null` for non-node references.

## Edges

Each `\using{dependency}` annotation yields one edge:

```json
{
  "id": "edge:17",
  "source": "dependency label",
  "target": "label of the node containing the annotation",
  "kind": "uses",
  "annotation_ordinal": 1
}
```

Thus every arrow points in implication order:

```text
dependency -> result that uses it
```

`uses` and `used_by` on nodes must agree with the edge list.

## Status catalog

The supported status IDs are:

| ID | Caption |
|---|---|
| `not_ready` | Not ready to be formalized |
| `can_state` | Ready to be formalized |
| `stated` | Statement formalized |
| `can_prove` | Proof ready to be formalized |
| `proved` | Proof formalized |
| `defined` | Definition formalized |
| `fully_proved` | Node and ancestors formalized |
| `external_dependency` | External dependency |

All nodes extracted from the supplied manuscript currently have status `can_state`.

## Diagnostics and strict mode

The extractor records duplicate or missing node labels, unresolved dependencies, duplicate edges, cycles, missing reference numbers, and unexpanded custom statement macros. With `--strict`, any such condition—or a failed LaTeX numbering build—causes a nonzero exit status after the JSON has been written for inspection.
