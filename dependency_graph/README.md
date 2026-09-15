# NCT dependency graph

The graph implementation lives on the `nct` branch of [roos-j/yaddag](https://github.com/roos-j/yaddag/tree/nct). It is an unchanged snapshot of this repository's graph scripts.

`yaddag-revision.txt` pins the full commit used by both GitHub workflows and the local graph-update skill. `run_yaddag.py` fetches that commit into `.lake/yaddag/<SHA>` on first use and reuses it thereafter. The branch tip is never used. Git and network access are required for the initial fetch.

## Run from the repository root

Requirements: Python 3.10+, Git, LaTeX/`latexmk`, Graphviz (`dot` and `neato`), and a local MathJax 3.2.2 `tex-svg-full.js` bundle.

```sh
python dependency_graph/run_yaddag.py extract blueprint/blueprint.tex dependency_graph/graph.json
python dependency_graph/run_yaddag.py render dependency_graph/graph.json dependency_graph/index.html --mathjax-js /path/to/tex-svg-full.js --lean-url-pattern 'https://roos-j.github.io/lean-nct/docs/find/?pattern={lean_name}&strict=false#doc'
```

Arguments after `extract` or `render` pass directly to the original scripts. Use `extract --help` or `render --help` for all options. Extraction supports `--aux-file` to reuse compiled numbering. The local update skill retains timestamped outputs and updates `index.html` only after successful rendering.

The source, schema, format specification, and detailed renderer documentation are in `dependency_graph/` at the pinned yaddag commit. Generated project artifacts remain here.

## Update the pin

Commit and push graph changes on yaddag's `nct` branch, then replace `yaddag-revision.txt` with that tested commit's full SHA. Review and commit the pin change in lean-nct. Reverting the pin selects the previous implementation.
