---
name: update-dependency-graph
description: Regenerate the repository's dependency-graph JSON and standalone HTML from the LaTeX blueprint, using timestamped artifacts and an issue report when the workflow encounters ambiguity or failure. Use when asked to update, rebuild, or refresh the dependency graph in a repository containing `blueprint/` and `dependency_graph/`.
---

# Update Dependency Graph

## Workflow

Run this workflow from the repository root. Confirm that `blueprint/`, `dependency_graph/latex_to_graph_json.py`, and `dependency_graph/graph_json_to_html.py` exist before doing any work.

### 1. Select the source blueprint

Choose the file `blueprint/blueprint.tex`.

If this file is not found, abort and report it.

### 2. Create timestamped paths

Use the current local date and time in `YYMMDD-HHmm` format. Put both generated artifacts in `dependency_graph/`:

- `dependency_graph/graph-(datetime).json`
- `dependency_graph/dependencygraph-(datetime).html`

For PowerShell, initialize the timestamp and paths as follows:

```powershell
$stamp = Get-Date -Format 'yyMMdd-HHmm'
$blueprint = 'blueprint/blueprint.tex'
$graph = "dependency_graph/graph-$stamp.json"
$html = "dependency_graph/dependencygraph-$stamp.html"
```

Use the equivalent local-time command when working in another shell. Check for existing files with the same timestamp before running the pipeline and call out any overwrite in the summary.

### 3. Extract the graph JSON

Invoke the extractor with the selected blueprint and timestamped JSON path:

```powershell
python dependency_graph/latex_to_graph_json.py $blueprint $graph
```

Preserve the extractor's stdout and stderr while diagnosing failures. The extractor may require LaTeX tooling because it normally compiles the source to resolve references.

Do not continue to HTML generation if extraction fails or the JSON file is absent. If the extractor reports structural, dependency, numbering, or macro issues, record the message and the action taken; use the extractor's `--strict` option when strict validation is specifically requested.

### 4. Render the standalone HTML

Feed the generated JSON into the renderer:

```powershell
python dependency_graph/graph_json_to_html.py $graph $html
```

If rendering fails because Graphviz or MathJax is unavailable, locate the required executable or MathJax bundle and rerun with the renderer's `--dot-binary`, `--neato-binary`, or `--mathjax-js` option as appropriate. Do not silently substitute an incomplete HTML artifact.

### 5. Verify and report

Verify that both timestamped files exist and that the JSON can be parsed. Report the blueprint file path, exact output paths, and any warnings or failures.

Create a diagnostic report only when an issue was encountered. Name it `dependency_graph/diagnostic-(datetime).md` using the same timestamp, and include:

- the blueprint and commands run;
- the issue or ambiguity, including relevant tool output;
- the action taken or the reason the pipeline stopped; and
- whether either output artifact was successfully produced.

Do not create an empty diagnostic report when the workflow completes clearly and successfully.
