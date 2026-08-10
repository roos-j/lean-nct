# Relation to the Lean Carleson dependency graph

The visual vocabulary follows the Lean Carleson/Lean blueprint dependency graph conventions:

- theorem-like results are ellipses;
- definitions are boxes;
- arrows point from prerequisites to results that use them;
- status is encoded by border and fill styling;
- blue denotes a statement ready to be formalized;
- orange and green status families remain available;
- dependencies supplied outside this blueprint use `external_dependency` / “External dependency”.

This implementation is not a vendored copy of `plastexdepgraph`. It is a Python pipeline specialized for this manuscript and for the requested JSON boundary:

```text
LaTeX -> rigid JSON -> independently rendered standalone HTML
```

Extensions beyond the upstream graph include:

- exact extraction from `\using` annotations;
- public/private visibility inferred from top-level section use, with the Introduction forced public;
- section and subsection hierarchy layouts, including true subsection partition cells;
- six separately computed geometries rather than CSS-only hierarchy switching;
- compiled LaTeX reference numbers in statements;
- links from statement references to graph nodes;
- recursive expansion of project macros in stored statements;
- MathJax-rendered node details and copyable expanded LaTeX;
- live search filtering, clickable hierarchy filters, optional sidebar/legend/hierarchy panels, and viewport SVG/PNG export;
- an ordered `lean_names` array allowing zero or several Lean declarations per node.
