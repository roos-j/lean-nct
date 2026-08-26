Here are instructions on how to update the dependency graph.

- Use the canonical blueprint file `blueprint/blueprint.tex`.
- Invoke the python script `dependency_graph/latex_to_graph_json.py` on that file.
- Feed the output of that script into `dependency_graph/graph_json_to_html.py` to generate the final output.
- The output files we are interested in are the graph json and the final html. Name them "graph-(datetime).json" and "dependencygraph-(datetime).html" with (datetime) replaced by the current date and time in the format YYMMDD-hhmm.
- Generate a diagonstic report file with the current date and time stamp in the filename that details any issues you ran into and what action you took in those cases (something was unclear). If everything was clear with no issues, you do not need to generate this report file.


