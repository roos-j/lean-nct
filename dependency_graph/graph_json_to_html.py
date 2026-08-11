#!/usr/bin/env python3
"""Render an NCT dependency-graph JSON document as standalone interactive HTML.

The renderer consumes only the JSON interchange file.  It computes independent
node layouts for each hierarchy mode (none, section, subsection) and for both
values of the definition-visibility setting, then embeds all six layouts in one
self-contained page.
"""

from __future__ import annotations

import argparse
import html
import json
import math
import re
import shlex
import shutil
import subprocess
import sys
import textwrap
import xml.etree.ElementTree as ET
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, Sequence

SCHEMA_NAME = "nct-dependency-graph"
SCHEMA_VERSION = "2.0.0"
SVG_NS = "http://www.w3.org/2000/svg"
ET.register_namespace("", SVG_NS)

PT_PER_INCH = 72.0
GLOBAL_MARGIN = 34.0
SECTION_GUTTER_X = 28.0
SECTION_GUTTER_Y = 34.0
SECTION_PAD_X = 20.0
SECTION_PAD_BOTTOM = 20.0
SECTION_TITLE_HEIGHT = 34.0
CELL_GUTTER_X = 14.0
CELL_GUTTER_Y = 14.0
CELL_PAD_X = 14.0
CELL_PAD_BOTTOM = 14.0
CELL_TITLE_HEIGHT = 28.0

# Statuses shared by theorem and definition nodes use one combined progress total.
# The remaining built-in statuses are theorem-only except for ``defined``.
STATUS_KIND_SCOPES: dict[str, tuple[str, ...]] = {
    "not_ready": ("theorem", "definition"),
    "can_state": ("theorem", "definition"),
    "stated": ("theorem",),
    "can_prove": ("theorem",),
    "proved": ("theorem",),
    "defined": ("definition",),
    "fully_proved": ("theorem", "definition"),
    "external_dependency": ("theorem",),
}


class GraphFormatError(ValueError):
    pass


@dataclass
class NodeGeometry:
    x: float
    y: float
    width: float
    height: float


@dataclass
class LocalLayout:
    nodes: dict[str, NodeGeometry]
    width: float
    height: float


@dataclass
class ClusterGeometry:
    kind: str
    level: int
    section_id: str
    subsection_id: str | None
    title: str
    aria_label: str
    synthetic: bool
    x: float
    y: float
    width: float
    height: float
    member_ids: list[str]
    clickable: bool = True


@dataclass
class SectionGeometry:
    section: dict[str, Any]
    nodes: dict[str, NodeGeometry]
    clusters: list[ClusterGeometry]
    width: float
    height: float


@dataclass
class LayoutGeometry:
    key: str
    mode: str
    include_definitions: bool
    nodes: dict[str, NodeGeometry]
    clusters: list[ClusterGeometry]
    width: float
    height: float
    svg: str = ""


# ---------------------------------------------------------------------------
# Validation and hierarchy utilities
# ---------------------------------------------------------------------------

def validate_graph(graph: dict[str, Any]) -> None:
    if graph.get("schema") != SCHEMA_NAME:
        raise GraphFormatError(f"expected schema {SCHEMA_NAME!r}")
    if graph.get("schema_version") != SCHEMA_VERSION:
        raise GraphFormatError(f"expected schema version {SCHEMA_VERSION!r}")
    for key in ("settings", "status_catalog", "sections", "nodes", "edges", "reference_catalog"):
        if key not in graph:
            raise GraphFormatError(f"missing top-level field {key!r}")
    status_ids = [entry.get("id") for entry in graph["status_catalog"]]
    if len(status_ids) != len(set(status_ids)):
        raise GraphFormatError("status IDs are not unique")
    node_ids = [node.get("id") for node in graph["nodes"]]
    if any(not isinstance(node_id, str) or not node_id for node_id in node_ids):
        raise GraphFormatError("every node must have a nonempty string ID")
    if len(node_ids) != len(set(node_ids)):
        raise GraphFormatError("node IDs are not unique")
    node_id_set = set(node_ids)
    for node in graph["nodes"]:
        if node.get("status") not in status_ids:
            raise GraphFormatError(f"unknown status on node {node['id']!r}")
        if node.get("kind") not in {"theorem", "definition"}:
            raise GraphFormatError(f"unknown node kind on {node['id']!r}")
        if node.get("visibility") not in {"public", "private"}:
            raise GraphFormatError(f"unknown visibility on {node['id']!r}")
        if not isinstance(node.get("lean_names"), list):
            raise GraphFormatError(f"lean_names must be a list on {node['id']!r}")
        for field in ("statement_latex", "statement_html", "statement_references"):
            if field not in node:
                raise GraphFormatError(f"node {node['id']!r} is missing {field!r}")
    for edge in graph["edges"]:
        if edge.get("source") not in node_id_set or edge.get("target") not in node_id_set:
            raise GraphFormatError(f"edge {edge.get('id')!r} has an unknown endpoint")


def flatten_sections(
    sections: Iterable[dict[str, Any]],
    parent_id: str | None = None,
    result: dict[str, dict[str, Any]] | None = None,
) -> dict[str, dict[str, Any]]:
    if result is None:
        result = {}
    for section in sections:
        record = dict(section)
        record["parent_id"] = parent_id
        result[section["id"]] = record
        flatten_sections(section.get("children", []), section["id"], result)
    return result


def ordered_top_sections(graph: dict[str, Any]) -> list[dict[str, Any]]:
    sections = sorted(graph["sections"], key=lambda item: item.get("ordinal", 0))
    introduction_id = graph.get("special_sections", {}).get("introduction_section_id")
    return sorted(sections, key=lambda item: (0 if item["id"] == introduction_id else 1, item.get("ordinal", 0)))


def node_tokens(graph: dict[str, Any]) -> tuple[dict[str, str], dict[str, dict[str, Any]]]:
    node_to_token: dict[str, str] = {}
    token_to_node: dict[str, dict[str, Any]] = {}
    for index, node in enumerate(graph["nodes"]):
        token = f"n{index:04d}"
        node_to_token[node["id"]] = token
        token_to_node[token] = node
    return node_to_token, token_to_node


# ---------------------------------------------------------------------------
# Graphviz helpers and local layouts
# ---------------------------------------------------------------------------

def dot_quote(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'


def wrapped_label(value: str, width: int = 27) -> str:
    return "\n".join(
        textwrap.wrap(
            value,
            width=width,
            break_long_words=True,
            break_on_hyphens=True,
            replace_whitespace=False,
        )
        or [value]
    )


def run_graphviz(source: str, binary: str, output_format: str, *, engine_args: Sequence[str] = ()) -> str:
    executable = shutil.which(binary)
    if executable is None:
        raise RuntimeError(f"Graphviz executable not found: {binary!r}")
    process = subprocess.run(
        [executable, *engine_args, f"-T{output_format}"],
        input=source,
        text=True,
        encoding="utf-8",
        errors="replace",
        capture_output=True,
        check=False,
    )
    if process.returncode != 0:
        raise RuntimeError(f"Graphviz failed with exit code {process.returncode}:\n{process.stderr}")
    return process.stdout


def local_dot_source(
    nodes: list[dict[str, Any]],
    edges: list[dict[str, Any]],
    statuses: dict[str, dict[str, Any]],
    node_to_token: dict[str, str],
) -> str:
    visible_ids = {node["id"] for node in nodes}
    lines = [
        "digraph local_layout {",
        "  graph [rankdir=BT, bgcolor=transparent, margin=0, pad=0, nodesep=0.20, ranksep=0.46, splines=spline, pack=8, packmode=\"array\", outputorder=edgesfirst];",
        "  node [fontname=\"Helvetica\", fontsize=9, margin=\"0.10,0.06\"];",
        "  edge [color=\"#64748B\", penwidth=0.8, arrowsize=0.55, arrowhead=vee];",
    ]
    for node in nodes:
        token = node_to_token[node["id"]]
        style = statuses[node["status"]]["style"]
        shape = "box" if node["kind"] == "definition" else "ellipse"
        node_style = "rounded,filled" if node["kind"] == "definition" else "filled"
        lines.append(
            f"  {token} [label={dot_quote(wrapped_label(node['label']))}, shape={shape}, style={dot_quote(node_style)}, "
            f"color={dot_quote(style['border'])}, fillcolor={dot_quote(style['fill'])}, fontcolor={dot_quote(style['text'])}, "
            f"penwidth={style['border_width']}];"
        )
    for edge in edges:
        if edge["source"] in visible_ids and edge["target"] in visible_ids:
            lines.append(f"  {node_to_token[edge['source']]} -> {node_to_token[edge['target']]};")
    lines.append("}")
    return "\n".join(lines) + "\n"


def parse_plain_layout(plain: str, token_to_id: dict[str, str]) -> LocalLayout:
    raw_nodes: dict[str, NodeGeometry] = {}
    for line in plain.splitlines():
        if not line.startswith("node "):
            continue
        fields = shlex.split(line)
        if len(fields) < 6:
            continue
        token = fields[1]
        if token not in token_to_id:
            continue
        raw_nodes[token_to_id[token]] = NodeGeometry(
            x=float(fields[2]) * PT_PER_INCH,
            y=float(fields[3]) * PT_PER_INCH,
            width=float(fields[4]) * PT_PER_INCH,
            height=float(fields[5]) * PT_PER_INCH,
        )
    if not raw_nodes:
        return LocalLayout({}, 0.0, 0.0)
    min_x = min(node.x - node.width / 2 for node in raw_nodes.values())
    max_x = max(node.x + node.width / 2 for node in raw_nodes.values())
    min_y = min(node.y - node.height / 2 for node in raw_nodes.values())
    max_y = max(node.y + node.height / 2 for node in raw_nodes.values())
    normalized = {
        node_id: NodeGeometry(node.x - min_x, node.y - min_y, node.width, node.height)
        for node_id, node in raw_nodes.items()
    }
    return LocalLayout(normalized, max_x - min_x, max_y - min_y)


def compute_local_layout(
    nodes: list[dict[str, Any]],
    edges: list[dict[str, Any]],
    statuses: dict[str, dict[str, Any]],
    node_to_token: dict[str, str],
    dot_binary: str,
) -> LocalLayout:
    if not nodes:
        return LocalLayout({}, 0.0, 0.0)
    source = local_dot_source(nodes, edges, statuses, node_to_token)
    token_to_id = {node_to_token[node["id"]]: node["id"] for node in nodes}
    return parse_plain_layout(run_graphviz(source, dot_binary, "plain"), token_to_id)


def translated_nodes(nodes: dict[str, NodeGeometry], dx: float, dy: float) -> dict[str, NodeGeometry]:
    return {
        node_id: NodeGeometry(node.x + dx, node.y + dy, node.width, node.height)
        for node_id, node in nodes.items()
    }


# ---------------------------------------------------------------------------
# Hierarchical geometry
# ---------------------------------------------------------------------------

def choose_grid(requirements: list[tuple[float, float]]) -> tuple[int, list[float], list[float]]:
    count = len(requirements)
    if count == 0:
        return 1, [], []
    best: tuple[float, int, list[float], list[float]] | None = None
    for columns in range(1, min(count, 5) + 1):
        rows = math.ceil(count / columns)
        column_widths = [0.0] * columns
        row_heights = [0.0] * rows
        for index, (width, height) in enumerate(requirements):
            row, column = divmod(index, columns)
            column_widths[column] = max(column_widths[column], width)
            row_heights[row] = max(row_heights[row], height)
        total_width = sum(column_widths) + CELL_GUTTER_X * max(0, columns - 1)
        total_height = sum(row_heights) + CELL_GUTTER_Y * max(0, rows - 1)
        aspect = total_width / max(total_height, 1.0)
        score = total_width * total_height * (1.0 + 0.16 * abs(math.log(max(aspect, 1e-6) / 1.35)))
        candidate = (score, columns, column_widths, row_heights)
        if best is None or candidate[0] < best[0]:
            best = candidate
    assert best is not None
    return best[1], best[2], best[3]


def section_mode_geometry(
    section: dict[str, Any],
    section_nodes: list[dict[str, Any]],
    edges: list[dict[str, Any]],
    statuses: dict[str, dict[str, Any]],
    node_to_token: dict[str, str],
    dot_binary: str,
) -> SectionGeometry:
    local = compute_local_layout(section_nodes, edges, statuses, node_to_token, dot_binary)
    width = local.width + 2 * SECTION_PAD_X
    height = local.height + SECTION_PAD_BOTTOM + SECTION_TITLE_HEIGHT
    nodes = translated_nodes(local.nodes, SECTION_PAD_X, SECTION_PAD_BOTTOM)
    cluster = ClusterGeometry(
        kind="section",
        level=1,
        section_id=section["id"],
        subsection_id=None,
        title=section.get("display_title") or section["title"],
        aria_label=f"Filter to section {section['title']}",
        synthetic=bool(section.get("synthetic")),
        x=0.0,
        y=0.0,
        width=width,
        height=height,
        member_ids=[node["id"] for node in section_nodes],
    )
    return SectionGeometry(section, nodes, [cluster], width, height)


def subsection_mode_geometry(
    section: dict[str, Any],
    section_nodes: list[dict[str, Any]],
    edges: list[dict[str, Any]],
    statuses: dict[str, dict[str, Any]],
    node_to_token: dict[str, str],
    dot_binary: str,
) -> SectionGeometry:
    nodes_by_subsection: dict[str | None, list[dict[str, Any]]] = defaultdict(list)
    for node in section_nodes:
        nodes_by_subsection[node.get("subsection_id")].append(node)

    groups: list[dict[str, Any]] = []
    direct_nodes = nodes_by_subsection.get(None, [])
    if direct_nodes:
        groups.append({
            "id": None,
            "title": "",
            "aria": f"Filter to direct material in {section['title']}",
            "synthetic": True,
            "nodes": direct_nodes,
        })
    for child in sorted(section.get("children", []), key=lambda item: item.get("ordinal", 0)):
        if child.get("level") != 2:
            continue
        child_nodes = nodes_by_subsection.get(child["id"], [])
        if child_nodes:
            groups.append({
                "id": child["id"],
                "title": child.get("display_title") or child["title"],
                "aria": f"Filter to subsection {child['title']}",
                "synthetic": False,
                "nodes": child_nodes,
            })
    assigned = {node["id"] for group in groups for node in group["nodes"]}
    leftovers = [node for node in section_nodes if node["id"] not in assigned]
    if leftovers:
        groups.append({"id": None, "title": "", "aria": f"Filter to other direct material in {section['title']}", "synthetic": True, "nodes": leftovers})

    sole_section_level_group = (
        len(groups) == 1
        and groups[0]["id"] is None
        and groups[0]["synthetic"]
    )
    for group in groups:
        group["clickable"] = not (sole_section_level_group and group is groups[0])
        if not group["clickable"]:
            group["aria"] = f"Section-level material in {section['title']}"

    for group in groups:
        group["layout"] = compute_local_layout(group["nodes"], edges, statuses, node_to_token, dot_binary)
        group["required_width"] = group["layout"].width + 2 * CELL_PAD_X
        group["required_height"] = group["layout"].height + CELL_PAD_BOTTOM + CELL_TITLE_HEIGHT

    columns, column_widths, row_heights = choose_grid(
        [(group["required_width"], group["required_height"]) for group in groups]
    )
    grid_width = sum(column_widths) + CELL_GUTTER_X * max(0, len(column_widths) - 1)
    grid_height = sum(row_heights) + CELL_GUTTER_Y * max(0, len(row_heights) - 1)
    width = grid_width + 2 * SECTION_PAD_X
    height = grid_height + SECTION_PAD_BOTTOM + SECTION_TITLE_HEIGHT

    result_nodes: dict[str, NodeGeometry] = {}
    clusters: list[ClusterGeometry] = [
        ClusterGeometry(
            kind="section", level=1, section_id=section["id"], subsection_id=None,
            title=section.get("display_title") or section["title"],
            aria_label=f"Filter to section {section['title']}", synthetic=bool(section.get("synthetic")),
            x=0.0, y=0.0, width=width, height=height,
            member_ids=[node["id"] for node in section_nodes],
        )
    ]

    grid_top = height - SECTION_TITLE_HEIGHT
    row_tops: list[float] = []
    running_y = grid_top
    for row_height in row_heights:
        row_tops.append(running_y)
        running_y -= row_height + CELL_GUTTER_Y

    # Every row spans the complete grid width.  A final incomplete row is not
    # left with empty column-shaped space: its existing cells are widened
    # proportionally while the configured gutters remain unchanged.
    cell_rectangles: dict[int, tuple[float, float, float, float]] = {}
    for row, row_height in enumerate(row_heights):
        first = row * columns
        row_count = min(columns, len(groups) - first)
        base_widths = column_widths[:row_count]
        usable_width = grid_width - CELL_GUTTER_X * max(0, row_count - 1)
        base_total = sum(base_widths)
        if base_total > 0:
            row_widths = [width * usable_width / base_total for width in base_widths]
        else:
            row_widths = [usable_width / max(row_count, 1)] * row_count
        running_x = SECTION_PAD_X
        cell_y = row_tops[row] - row_height
        for offset, cell_width in enumerate(row_widths):
            cell_rectangles[first + offset] = (running_x, cell_y, cell_width, row_height)
            running_x += cell_width + CELL_GUTTER_X

    for index, group in enumerate(groups):
        cell_x, cell_y, cell_width, cell_height = cell_rectangles[index]
        local: LocalLayout = group["layout"]
        content_bottom = cell_y + CELL_PAD_BOTTOM
        content_top = cell_y + cell_height - CELL_TITLE_HEIGHT
        dx = cell_x + (cell_width - local.width) / 2
        dy = content_bottom + max(0.0, (content_top - content_bottom - local.height) / 2)
        result_nodes.update(translated_nodes(local.nodes, dx, dy))
        clusters.append(
            ClusterGeometry(
                kind="subsection", level=2, section_id=section["id"], subsection_id=group["id"],
                title=group["title"], aria_label=group["aria"], synthetic=group["synthetic"],
                x=cell_x, y=cell_y, width=cell_width, height=cell_height,
                member_ids=[node["id"] for node in group["nodes"]],
                clickable=group["clickable"],
            )
        )
    return SectionGeometry(section, result_nodes, clusters, width, height)


def choose_section_rows(sections: list[SectionGeometry]) -> tuple[list[list[SectionGeometry]], float, float]:
    if not sections:
        return [], 0.0, 0.0
    best: tuple[float, list[list[SectionGeometry]], float, float] | None = None
    for columns in range(1, min(len(sections), 4) + 1):
        rows = [sections[index : index + columns] for index in range(0, len(sections), columns)]
        row_widths = [sum(item.width for item in row) + SECTION_GUTTER_X * max(0, len(row) - 1) for row in rows]
        row_heights = [max(item.height for item in row) for row in rows]
        total_width = max(row_widths)
        total_height = sum(row_heights) + SECTION_GUTTER_Y * max(0, len(rows) - 1)
        aspect = total_width / max(total_height, 1.0)
        score = total_width * total_height * (1.0 + 0.20 * abs(math.log(max(aspect, 1e-6) / 1.45)))
        candidate = (score, rows, total_width, total_height)
        if best is None or candidate[0] < best[0]:
            best = candidate
    assert best is not None
    return best[1], best[2], best[3]


def translate_section(section: SectionGeometry, dx: float, dy: float) -> tuple[dict[str, NodeGeometry], list[ClusterGeometry]]:
    nodes = translated_nodes(section.nodes, dx, dy)
    clusters = [
        ClusterGeometry(
            kind=cluster.kind,
            level=cluster.level,
            section_id=cluster.section_id,
            subsection_id=cluster.subsection_id,
            title=cluster.title,
            aria_label=cluster.aria_label,
            synthetic=cluster.synthetic,
            x=cluster.x + dx,
            y=cluster.y + dy,
            width=cluster.width,
            height=cluster.height,
            member_ids=cluster.member_ids,
            clickable=cluster.clickable,
        )
        for cluster in section.clusters
    ]
    return nodes, clusters


def hierarchy_layout_geometry(
    graph: dict[str, Any],
    mode: str,
    include_definitions: bool,
    dot_binary: str,
    node_to_token: dict[str, str],
) -> LayoutGeometry:
    statuses = {entry["id"]: entry for entry in graph["status_catalog"]}
    visible_nodes = [node for node in graph["nodes"] if include_definitions or node["kind"] != "definition"]
    visible_ids = {node["id"] for node in visible_nodes}
    visible_edges = [edge for edge in graph["edges"] if edge["source"] in visible_ids and edge["target"] in visible_ids]
    key = f"{mode}-{'definitions' if include_definitions else 'theorems'}"

    if mode == "none":
        local = compute_local_layout(visible_nodes, visible_edges, statuses, node_to_token, dot_binary)
        nodes = translated_nodes(local.nodes, GLOBAL_MARGIN, GLOBAL_MARGIN)
        return LayoutGeometry(key, mode, include_definitions, nodes, [], local.width + 2 * GLOBAL_MARGIN, local.height + 2 * GLOBAL_MARGIN)

    nodes_by_section: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for node in visible_nodes:
        nodes_by_section[node["section_id"]].append(node)

    section_geometries: list[SectionGeometry] = []
    for section in ordered_top_sections(graph):
        section_nodes = nodes_by_section.get(section["id"], [])
        if not section_nodes:
            continue
        if mode == "section":
            geometry = section_mode_geometry(section, section_nodes, visible_edges, statuses, node_to_token, dot_binary)
        else:
            geometry = subsection_mode_geometry(section, section_nodes, visible_edges, statuses, node_to_token, dot_binary)
        section_geometries.append(geometry)

    introduction_id = graph.get("special_sections", {}).get("introduction_section_id")
    introduction = next((item for item in section_geometries if item.section["id"] == introduction_id), None)
    others = [item for item in section_geometries if item is not introduction]
    rows, others_width, others_height = choose_section_rows(others)
    overall_width = max(others_width, introduction.width if introduction else 0.0)
    overall_height = others_height
    if introduction:
        overall_height += (SECTION_GUTTER_Y if others else 0.0) + introduction.height

    all_nodes: dict[str, NodeGeometry] = {}
    all_clusters: list[ClusterGeometry] = []
    y_top = others_height
    for row in rows:
        row_height = max(item.height for item in row)
        row_width = sum(item.width for item in row) + SECTION_GUTTER_X * max(0, len(row) - 1)
        row_bottom = y_top - row_height
        x = (overall_width - row_width) / 2
        for section in row:
            nodes, clusters = translate_section(section, x, row_bottom + (row_height - section.height) / 2)
            all_nodes.update(nodes)
            all_clusters.extend(clusters)
            x += section.width + SECTION_GUTTER_X
        y_top = row_bottom - SECTION_GUTTER_Y

    if introduction:
        intro_y = others_height + (SECTION_GUTTER_Y if others else 0.0)
        intro_x = (overall_width - introduction.width) / 2
        nodes, clusters = translate_section(introduction, intro_x, intro_y)
        all_nodes.update(nodes)
        all_clusters.extend(clusters)

    all_nodes = translated_nodes(all_nodes, GLOBAL_MARGIN, GLOBAL_MARGIN)
    translated_clusters = [
        ClusterGeometry(
            kind=cluster.kind, level=cluster.level, section_id=cluster.section_id,
            subsection_id=cluster.subsection_id, title=cluster.title, aria_label=cluster.aria_label,
            synthetic=cluster.synthetic, x=cluster.x + GLOBAL_MARGIN, y=cluster.y + GLOBAL_MARGIN,
            width=cluster.width, height=cluster.height, member_ids=cluster.member_ids,
            clickable=cluster.clickable,
        )
        for cluster in all_clusters
    ]
    return LayoutGeometry(
        key, mode, include_definitions, all_nodes, translated_clusters,
        overall_width + 2 * GLOBAL_MARGIN, overall_height + 2 * GLOBAL_MARGIN,
    )


# ---------------------------------------------------------------------------
# Fixed-position SVG generation
# ---------------------------------------------------------------------------

def fixed_dot_source(
    graph: dict[str, Any],
    layout: LayoutGeometry,
    node_to_token: dict[str, str],
) -> str:
    statuses = {entry["id"]: entry for entry in graph["status_catalog"]}
    node_by_id = {node["id"]: node for node in graph["nodes"]}
    visible_ids = set(layout.nodes)
    visible_edges = [edge for edge in graph["edges"] if edge["source"] in visible_ids and edge["target"] in visible_ids]
    lines = [
        "digraph fixed_layout {",
        "  graph [layout=neato, overlap=true, splines=line, notranslate=true, outputorder=edgesfirst, bgcolor=transparent, margin=0, pad=0.04, fontname=\"Helvetica\"];",
        "  node [fontname=\"Helvetica\", fontsize=9, margin=0, fixedsize=true];",
        "  edge [color=\"#64748B\", penwidth=0.9, arrowsize=0.62, arrowhead=vee];",
        f"  bounds_min [pos={dot_quote('0,0!')}, shape=point, width=0.01, height=0.01, label=\"\", style=invis];",
        f"  bounds_max [pos={dot_quote(f'{layout.width:.3f},{layout.height:.3f}!')}, shape=point, width=0.01, height=0.01, label=\"\", style=invis];",
    ]
    for node_id, geometry in layout.nodes.items():
        node = node_by_id[node_id]
        token = node_to_token[node_id]
        style = statuses[node["status"]]["style"]
        shape = "box" if node["kind"] == "definition" else "ellipse"
        node_style = "rounded,filled" if node["kind"] == "definition" else "filled"
        lines.append(
            f"  {token} [pos={dot_quote(f'{geometry.x:.3f},{geometry.y:.3f}!')}, "
            f"width={geometry.width / PT_PER_INCH:.6f}, height={geometry.height / PT_PER_INCH:.6f}, "
            f"label={dot_quote(wrapped_label(node['label']))}, shape={shape}, style={dot_quote(node_style)}, "
            f"color={dot_quote(style['border'])}, fillcolor={dot_quote(style['fill'])}, fontcolor={dot_quote(style['text'])}, "
            f"penwidth={style['border_width']}, tooltip={dot_quote(node['label'])}];"
        )
    for edge in visible_edges:
        lines.append(
            f"  {node_to_token[edge['source']]} -> {node_to_token[edge['target']]} "
            f"[tooltip={dot_quote(edge['source'] + ' → ' + edge['target'])}];"
        )
    lines.append("}")
    return "\n".join(lines) + "\n"


def svg_element(tag: str, attributes: dict[str, str] | None = None, text: str | None = None) -> ET.Element:
    element = ET.Element(f"{{{SVG_NS}}}{tag}", attributes or {})
    element.text = text
    return element


def cluster_svg_group(cluster: ClusterGeometry, index: int) -> ET.Element:
    classes = ["dep-cluster", f"cluster-level-{cluster.level}"]
    if cluster.synthetic:
        classes.append("cluster-synthetic")
    if not cluster.clickable:
        classes.append("cluster-noninteractive")
    attributes = {
        "class": " ".join(classes),
        "id": f"cluster-{index:04d}",
        "data-cluster-kind": cluster.kind,
        "data-cluster-title": cluster.title,
        "data-section-id": cluster.section_id,
        "data-member-count": str(len(cluster.member_ids)),
        "data-cluster-clickable": "true" if cluster.clickable else "false",
    }
    if cluster.subsection_id is not None:
        attributes["data-subsection-id"] = cluster.subsection_id
    else:
        attributes["data-subsection-id"] = ""
    if not cluster.clickable:
        # A sole synthetic section-level cell is purely structural.  Disable
        # pointer targeting on the complete SVG group, not just its caption,
        # so it cannot highlight, change cursors, or show a native SVG tooltip.
        attributes["pointer-events"] = "none"
    group = svg_element("g", attributes)
    y = -(cluster.y + cluster.height)
    group.append(
        svg_element(
            "rect",
            {
                "class": "cluster-box",
                "x": f"{cluster.x:.3f}",
                "y": f"{y:.3f}",
                "width": f"{cluster.width:.3f}",
                "height": f"{cluster.height:.3f}",
                "rx": "10" if cluster.level == 1 else "7",
                "ry": "10" if cluster.level == 1 else "7",
            },
        )
    )
    caption_height = SECTION_TITLE_HEIGHT if cluster.level == 1 else CELL_TITLE_HEIGHT
    caption_attributes = {
        "class": "cluster-caption" if cluster.clickable else "cluster-caption cluster-caption-static",
        "data-cluster-kind": cluster.kind,
        "data-section-id": cluster.section_id,
        "data-subsection-id": cluster.subsection_id or "",
    }
    if cluster.clickable:
        caption_attributes.update({
            "data-cluster-caption": "true",
            "role": "button",
            "tabindex": "0",
            "aria-label": cluster.aria_label,
        })
    else:
        caption_attributes["aria-hidden"] = "true"
    caption = svg_element("g", caption_attributes)
    if cluster.clickable:
        # Keep the native tooltip on the interactive caption only.  Attaching
        # it to the outer cluster group would make the whole box react to
        # hover, including a sole noninteractive section-level cell layered
        # over its containing section.
        caption.append(svg_element("title", text=cluster.aria_label))
    caption.append(
        svg_element(
            "rect",
            {
                "class": "cluster-caption-hit",
                "fill": "none",
                "stroke": "none",
                "pointer-events": "all" if cluster.clickable else "none",
                "x": f"{cluster.x + 3:.3f}",
                "y": f"{y + 3:.3f}",
                "width": f"{max(1.0, cluster.width - 6):.3f}",
                "height": f"{max(1.0, caption_height - 5):.3f}",
                "rx": "6",
                "ry": "6",
            },
        )
    )
    if cluster.title:
        max_chars = max(16, min(68, int((cluster.width - 26) / 6.3)))
        lines = textwrap.wrap(cluster.title, width=max_chars, break_long_words=False, break_on_hyphens=False)[:2] or [cluster.title]
        text = svg_element(
            "text",
            {
                "class": "cluster-caption-text",
                "x": f"{cluster.x + 13:.3f}",
                "y": f"{y + 18:.3f}",
                "text-anchor": "start",
            },
        )
        for line_index, line in enumerate(lines):
            text.append(
                svg_element(
                    "tspan",
                    {
                        "x": f"{cluster.x + 13:.3f}",
                        "dy": "0" if line_index == 0 else "13",
                    },
                    line,
                )
            )
        caption.append(text)
    group.append(caption)
    return group


def postprocess_svg(
    svg_text: str,
    graph: dict[str, Any],
    layout: LayoutGeometry,
    token_to_node: dict[str, dict[str, Any]],
) -> str:
    root = ET.fromstring(svg_text)
    root.set("id", f"dependency-svg-{layout.key}")
    root.set("class", "dependency-svg")
    root.set("width", "100%")
    root.set("height", "100%")
    root.set("preserveAspectRatio", "xMidYMid meet")
    root.set("data-layout-key", layout.key)
    root.set("data-hierarchy", layout.mode)
    root.set("data-include-definitions", "true" if layout.include_definitions else "false")
    root.attrib.pop("style", None)
    # Standalone SVGs need their own cluster and visibility styling.  CSS
    # custom-property fallbacks preserve the same defaults outside the HTML,
    # while the interactive page can still update the inherited variables.
    embedded_style = svg_element(
        "style",
        {"type": "text/css"},
        text=(
            ".dep-node{opacity:var(--public-opacity,1);}"
            ".dep-node.visibility-private{opacity:var(--private-opacity,.5);}"
            ".dep-edge{--edge-opacity:var(--public-edge-opacity,.48);}"
            ".dep-edge.visibility-private{--edge-opacity:var(--private-edge-opacity,.24);}"
            ".dep-edge path{stroke-opacity:var(--edge-opacity);}"
            ".dep-edge polygon{fill-opacity:var(--edge-opacity);stroke-opacity:var(--edge-opacity);}"
            ".dep-cluster.cluster-level-1>.cluster-box{fill:#cbd5e1;fill-opacity:var(--section-opacity,.15);stroke:#94a3b8;stroke-opacity:.78;stroke-width:1.1;}"
            ".dep-cluster.cluster-level-2>.cluster-box{fill:#dbeafe;fill-opacity:var(--subsection-opacity,.09);stroke:#cbd5e1;stroke-opacity:.72;stroke-width:.9;stroke-dasharray:4 3;}"
            ".dep-cluster.cluster-noninteractive,.dep-cluster.cluster-noninteractive *{pointer-events:none!important;}"
            ".cluster-caption-hit{fill:transparent;stroke:none;}"
            ".cluster-caption-text{font-family:Helvetica,Arial,sans-serif;fill:#334155;font-size:11px;font-weight:600;opacity:.82;}"
            ".cluster-level-2 .cluster-caption-text{font-size:9px;font-weight:500;fill:#475569;}"
        ),
    )
    root.insert(0, embedded_style)

    graph_group = root.find(f".//{{{SVG_NS}}}g[@class='graph']")
    if graph_group is None:
        raise RuntimeError("Graphviz SVG has no graph group")

    groups_to_remove: list[ET.Element] = []
    for group in graph_group.findall(f"{{{SVG_NS}}}g"):
        classes = group.get("class", "").split()
        title_element = group.find(f"{{{SVG_NS}}}title")
        title = title_element.text.strip() if title_element is not None and title_element.text else ""
        if title in {"bounds_min", "bounds_max"}:
            groups_to_remove.append(group)
            continue
        if "node" in classes and title in token_to_node:
            node = token_to_node[title]
            group.set("class", " ".join(classes + ["dep-node", f"status-{node['status']}", f"visibility-{node['visibility']}", f"kind-{node['kind']}"]))
            group.set("id", f"{layout.key}-{title}")
            group.set("data-node-id", node["id"])
            group.set("data-status", node["status"])
            group.set("data-visibility", node["visibility"])
            group.set("data-kind", node["kind"])
            group.set("data-section-id", node["section_id"])
            group.set("data-subsection-id", node.get("subsection_id") or "")
            group.set("tabindex", "0")
            group.set("role", "button")
            group.set("aria-label", node["label"])
            if title_element is not None:
                number = f" {node['number']}" if node.get("number") else ""
                title_element.text = f"{node['environment_name']}{number}: {node['label']}"
        elif "edge" in classes:
            match = re.fullmatch(r"\s*(n\d+)\s*->\s*(n\d+)\s*", title)
            if match and match.group(1) in token_to_node and match.group(2) in token_to_node:
                source_node = token_to_node[match.group(1)]
                target_node = token_to_node[match.group(2)]
                source = source_node["id"]
                target = target_node["id"]
                edge_visibility = "private" if "private" in {source_node["visibility"], target_node["visibility"]} else "public"
                group.set("class", " ".join(classes + ["dep-edge", f"visibility-{edge_visibility}"]))
                group.set("data-source", source)
                group.set("data-target", target)
                group.set("data-visibility", edge_visibility)
                if title_element is not None:
                    title_element.text = f"{source} → {target}"
    for group in groups_to_remove:
        graph_group.remove(group)

    # Make Graphviz's background transparent.
    children = list(graph_group)
    for child in children:
        if child.tag == f"{{{SVG_NS}}}polygon" and child.get("fill") == "white":
            child.set("fill", "transparent")
            child.set("stroke", "none")
            break

    insertion_index = 1
    if len(graph_group) > 1 and graph_group[1].tag == f"{{{SVG_NS}}}polygon":
        insertion_index = 2
    for offset, cluster in enumerate(sorted(layout.clusters, key=lambda item: item.level)):
        graph_group.insert(insertion_index + offset, cluster_svg_group(cluster, offset))
    return ET.tostring(root, encoding="unicode")


def render_layout_svg(
    graph: dict[str, Any],
    layout: LayoutGeometry,
    node_to_token: dict[str, str],
    token_to_node: dict[str, dict[str, Any]],
    neato_binary: str,
) -> tuple[str, str]:
    dot_source = fixed_dot_source(graph, layout, node_to_token)
    raw_svg = run_graphviz(dot_source, neato_binary, "svg", engine_args=("-n2",))
    svg = postprocess_svg(raw_svg, graph, layout, token_to_node)
    layout.svg = svg
    return svg, dot_source


# ---------------------------------------------------------------------------
# HTML fragments
# ---------------------------------------------------------------------------

def percentage_label(count: int, total: int) -> str:
    percentage = 100.0 * count / total if total else 0.0
    return f"{percentage:.1f}".rstrip("0").rstrip(".") + "%"


def status_legend_html(status_catalog: list[dict[str, Any]], nodes: list[dict[str, Any]]) -> str:
    totals = {
        kind: sum(node["kind"] == kind for node in nodes)
        for kind in ("theorem", "definition")
    }
    counts: dict[tuple[str, str], int] = defaultdict(int)
    for node in nodes:
        counts[(node["kind"], node["status"])] += 1

    items: list[str] = []
    for status in status_catalog:
        style = status["style"]
        scopes = STATUS_KIND_SCOPES.get(status["id"])
        if scopes is None:
            observed = tuple(
                kind for kind in ("theorem", "definition")
                if counts[(kind, status["id"])]
            )
            scopes = observed or ("theorem",)
        count = sum(counts[(kind, status["id"])] for kind in scopes)
        total = sum(totals[kind] for kind in scopes)
        count_summary = f"{count}/{total} ({percentage_label(count, total)})"
        items.append(
            '<div class="legend-status">'
            f'<span class="status-swatch" style="--swatch-border:{html.escape(style["border"])};--swatch-fill:{html.escape(style["fill"])};--swatch-text:{html.escape(style["text"])}"></span>'
            '<span>'
            f'<strong>{html.escape(status["name"])} <span class="legend-status-count">{html.escape(count_summary)}</span></strong>'
            f'<small>{html.escape(status["meaning"])}</small>'
            '</span></div>'
        )
    return "".join(items)


def hierarchy_html(sections: list[dict[str, Any]], node_counts: dict[str, int]) -> str:
    def render(items: list[dict[str, Any]]) -> str:
        if not items:
            return ""
        pieces = ["<ul>"]
        for section in items:
            count = node_counts.get(section["id"], 0)
            display = section.get("display_title") or section["title"]
            pieces.append(
                "<li>"
                f'<button type="button" class="hierarchy-filter" data-hierarchy-section="{html.escape(section["id"], quote=True)}" data-hierarchy-level="{section.get("level", 1)}">'
                f'<span>{html.escape(display)}</span><small>{count}</small></button>'
                f'{render(section.get("children", []))}'
                "</li>"
            )
        pieces.append("</ul>")
        return "".join(pieces)
    return render(sections)


def find_mathjax_bundle(explicit: Path | None) -> Path:
    candidates = [
        explicit,
        Path("/opt/nvm/versions/node/v22.16.0/lib/node_modules/mathjax-full/es5/tex-svg-full.js"),
        Path("/usr/local/lib/node_modules/mathjax-full/es5/tex-svg-full.js"),
    ]
    for candidate in candidates:
        if candidate and candidate.is_file():
            return candidate
    raise RuntimeError("a local MathJax tex-svg-full.js bundle is required; pass --mathjax-js")


def validate_lean_url_pattern(pattern: str | None) -> None:
    if pattern is not None and "{lean_name}" not in pattern:
        raise ValueError("--lean-url-pattern must contain the {lean_name} placeholder")


def build_html(
    graph: dict[str, Any],
    layouts: dict[str, LayoutGeometry],
    mathjax_source: str,
    lean_url_pattern: str | None = None,
) -> str:
    settings = graph["settings"]
    stats = graph["statistics"]
    section_counts: dict[str, int] = defaultdict(int)
    for node in graph["nodes"]:
        for section_id in dict.fromkeys(node["section_path"]):
            section_counts[section_id] += 1

    graph_data = json.dumps(graph, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    lean_url_pattern_json = json.dumps(lean_url_pattern, ensure_ascii=False).replace("</", "<\\/")
    legend = status_legend_html(graph["status_catalog"], graph["nodes"])
    hierarchy = hierarchy_html(graph["sections"], section_counts)
    layout_markup = "\n".join(
        f'<div class="layout-slot" data-layout-key="{html.escape(key, quote=True)}">{layout.svg}</div>'
        for key, layout in layouts.items()
    )
    default_key = f"{settings['grouping_granularity']}-{'definitions' if settings['include_definitions'] else 'theorems'}"
    source_name = html.escape(graph["source"]["latex_file"])

    template = r'''<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>NCT blueprint dependency graph</title>
<style>
:root {
  --private-opacity: $private_opacity;
  --public-opacity: $public_opacity;
  --private-edge-opacity: $private_edge_opacity;
  --public-edge-opacity: $public_edge_opacity;
  --section-opacity: $section_opacity;
  --subsection-opacity: $subsection_opacity;
  --ink: #0f172a;
  --muted: #64748b;
  --line: #cbd5e1;
  --panel: #ffffff;
  --canvas: #f8fafc;
  --accent: #2563eb;
  --toolbar-h: 64px;
  --left-w: 294px;
  --right-w: 420px;
}
* { box-sizing: border-box; }
html, body { width: 100%; height: 100%; margin: 0; overflow: hidden; }
body { font-family: Inter, ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif; color: var(--ink); background: var(--canvas); }
button, input, select { font: inherit; }
button { border: 1px solid var(--line); background: #fff; color: var(--ink); border-radius: 7px; padding: 7px 10px; cursor: pointer; }
button:hover { border-color: #94a3b8; background: #f8fafc; }
button:focus-visible, input:focus-visible, select:focus-visible, .dep-node:focus-visible, .cluster-caption:focus-visible { outline: 3px solid rgba(37,99,235,.30); outline-offset: 2px; }
[hidden] { display: none !important; }
#toolbar { position: fixed; z-index: 30; inset: 0 0 auto 0; height: var(--toolbar-h); display: flex; align-items: center; gap: 12px; padding: 9px 14px; background: rgba(255,255,255,.96); border-bottom: 1px solid var(--line); backdrop-filter: blur(8px); }
.brand { min-width: 250px; }
.brand h1 { font-size: 16px; line-height: 1.2; margin: 0; }
.brand p { font-size: 11px; color: var(--muted); margin: 3px 0 0; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; max-width: 330px; }
.search-wrap { display: flex; align-items: center; gap: 8px; flex: 1 1 420px; max-width: 760px; }
.search-input-wrap { position: relative; flex: 1 1 auto; min-width: 120px; }
#search { width: 100%; border: 1px solid var(--line); border-radius: 8px; padding: 9px 100px 9px 12px; color: var(--ink); background: #fff; }
#search-count { position: absolute; right: 10px; top: 50%; transform: translateY(-50%); font-size: 11px; color: var(--muted); pointer-events: none; }
.inverse-search { display: inline-flex; align-items: center; gap: 5px; white-space: nowrap; color: #475569; font-size: 11px; }
.inverse-search input { margin: 0; }
.toolbar-actions { display: flex; gap: 6px; margin-left: auto; }
.toolbar-icon { min-width: 36px; }
.stat-chip { border: 1px solid #dbeafe; background: #eff6ff; color: #1e3a8a; border-radius: 999px; padding: 6px 9px; font-size: 11px; white-space: nowrap; }
#left-panel { position: fixed; z-index: 12; left: 0; top: var(--toolbar-h); bottom: 0; width: var(--left-w); background: rgba(255,255,255,.97); border-right: 1px solid var(--line); overflow: auto; padding: 14px; transition: transform .18s ease; }
body.sidebar-hidden #left-panel { transform: translateX(-100%); }
.panel-section { margin-bottom: 18px; }
.panel-section h2 { font-size: 12px; text-transform: uppercase; letter-spacing: .08em; color: #475569; margin: 0 0 9px; }
.panel-note { font-size: 11px; line-height: 1.45; color: var(--muted); margin: 8px 0; }
.shape-row, .visibility-row { display: grid; grid-template-columns: 32px minmax(0,1fr); gap: 8px; align-items: center; font-size: 12px; margin: 8px 0; }
.legend-caption strong { display: block; font-size: 12px; font-weight: 600; }
.legend-caption small { display: block; color: #94a3b8; font-size: 10px; line-height: 1.25; margin-top: 1px; }
.shape { width: 30px; height: 18px; border: 2px solid var(--accent); background: #fff; display: inline-block; }
.shape.ellipse { border-radius: 999px; }
.shape.box { border-radius: 3px; }
.opacity-sample { width: 31px; height: 18px; border-radius: 999px; border: 2px solid var(--accent); background: #fff; display: inline-block; opacity: var(--public-opacity); }
.opacity-sample.private { opacity: var(--private-opacity); }
.legend-status { display: grid; grid-template-columns: 31px 1fr; gap: 8px; align-items: start; margin: 8px 0; }
.status-swatch { width: 31px; height: 18px; margin-top: 1px; border-radius: 999px; border: 2px solid var(--swatch-border); background: var(--swatch-fill); color: var(--swatch-text); }
.legend-status strong { display: block; font-size: 11px; font-weight: 650; line-height: 1.2; }
.legend-status-count { color: #94a3b8; font-size: 9px; font-weight: 400; margin-left: 3px; }
.legend-status small { display: block; color: var(--muted); font-size: 10px; line-height: 1.28; margin-top: 2px; }
.hierarchy ul { list-style: none; margin: 0; padding-left: 12px; border-left: 1px solid #e2e8f0; }
.hierarchy > ul { padding-left: 0; border-left: 0; }
.hierarchy li { margin: 4px 0; }
.hierarchy-filter { display: grid; grid-template-columns: minmax(0,1fr) auto; gap: 8px; width: 100%; border: 0; padding: 3px 4px; text-align: left; background: transparent; font-size: 11px; color: #334155; }
.hierarchy-filter:hover { background: #f1f5f9; }
.hierarchy-filter span { overflow-wrap: anywhere; }
.hierarchy-filter small { color: #94a3b8; }
.hierarchy-filter.active { background: #dbeafe; color: #1e3a8a; }
#viewport { position: fixed; left: var(--left-w); right: 0; top: var(--toolbar-h); bottom: 0; overflow: hidden; background: radial-gradient(circle at 1px 1px, #e2e8f0 1px, transparent 1px); background-size: 22px 22px; transition: left .18s ease, right .18s ease; }
body.sidebar-hidden #viewport { left: 0; }
#viewport.details-open { right: var(--right-w); }
#graph-host { width: 100%; height: 100%; touch-action: none; user-select: none; }
.layout-slot { width: 100%; height: 100%; display: none; }
.layout-slot.active { display: block; }
.dependency-svg { display: block; width: 100%; height: 100%; cursor: grab; }
.dependency-svg.panning { cursor: grabbing; }
.dep-cluster.cluster-level-1 > .cluster-box { fill: #cbd5e1; fill-opacity: var(--section-opacity); stroke: #94a3b8; stroke-opacity: .78; stroke-width: 1.1; vector-effect: non-scaling-stroke; }
.dep-cluster.cluster-level-2 > .cluster-box { fill: #dbeafe; fill-opacity: var(--subsection-opacity); stroke: #cbd5e1; stroke-opacity: .72; stroke-width: .9; stroke-dasharray: 4 3; vector-effect: non-scaling-stroke; }
.cluster-caption { cursor: pointer; }
.cluster-caption-static { cursor: default; pointer-events: none; }
.dep-cluster.cluster-noninteractive, .dep-cluster.cluster-noninteractive * { pointer-events: none !important; }
.cluster-caption-hit { fill: transparent; stroke: none; pointer-events: all; }
.cluster-caption[data-cluster-caption="true"]:hover .cluster-caption-hit, .cluster-caption.active .cluster-caption-hit { fill: #2563eb; fill-opacity: .08; }
.cluster-caption-text { font-family: Helvetica, Arial, sans-serif; fill: #334155; font-size: 11px; font-weight: 600; opacity: .82; pointer-events: none; }
.cluster-level-2 .cluster-caption-text { font-size: 9px; font-weight: 500; fill: #475569; }
.dep-node { cursor: pointer; opacity: var(--public-opacity); transition: opacity .15s ease; }
.dep-node.visibility-private { opacity: var(--private-opacity); }
.dep-node:hover > ellipse, .dep-node:hover > polygon, .dep-node:hover > path { stroke-width: 2.8px !important; }
.dep-node.search-match > ellipse, .dep-node.search-match > polygon, .dep-node.search-match > path { stroke: #f59e0b !important; stroke-width: 4px !important; }
.dep-node.selected > ellipse, .dep-node.selected > polygon, .dep-node.selected > path { stroke: #dc2626 !important; stroke-width: 4px !important; }
.dep-edge { --edge-opacity: var(--public-edge-opacity); }
.dep-edge.visibility-private { --edge-opacity: var(--private-edge-opacity); }
.dep-edge path { stroke: #64748b; stroke-opacity: var(--edge-opacity); shape-rendering: geometricPrecision; }
.dep-edge polygon { fill: #64748b; stroke: #64748b; fill-opacity: var(--edge-opacity); stroke-opacity: var(--edge-opacity); shape-rendering: geometricPrecision; }
.dep-edge.incident { --edge-opacity: var(--public-opacity); }
.dep-edge.visibility-private.incident { --edge-opacity: var(--private-opacity); }
.dep-edge.incident path { stroke: #dc2626; stroke-width: 1.8px; }
.dep-edge.incident polygon { fill: #dc2626; stroke: #dc2626; }
.filtered-out { display: none !important; }
#details { position: fixed; z-index: 18; right: 0; top: var(--toolbar-h); bottom: 0; width: var(--right-w); transform: translateX(100%); transition: transform .18s ease; background: rgba(255,255,255,.99); border-left: 1px solid var(--line); overflow: auto; box-shadow: -8px 0 24px rgba(15,23,42,.08); }
#details.open { transform: translateX(0); }
.details-header { position: sticky; top: 0; z-index: 2; display: flex; align-items: start; gap: 8px; padding: 14px; background: rgba(255,255,255,.98); border-bottom: 1px solid var(--line); }
.details-header h2 { margin: 0; font-size: 14px; line-height: 1.35; overflow-wrap: anywhere; flex: 1; }
#close-details { padding: 4px 8px; }
.details-body { padding: 14px; }
.meta-grid { display: grid; grid-template-columns: 96px minmax(0,1fr); gap: 8px 10px; font-size: 12px; }
.meta-grid dt { color: var(--muted); }
.meta-grid dd { margin: 0; overflow-wrap: anywhere; }
.lean-name-links { display: flex; flex-wrap: wrap; gap: 4px 8px; }
.lean-name-link { color: #1d4ed8; text-decoration: underline; text-underline-offset: 2px; }
.lean-name-link:hover { color: #1e40af; }
.statement-panel { margin-top: 18px; border-top: 1px solid #e2e8f0; padding-top: 14px; }
.statement-panel h3, .dep-list h3 { font-size: 11px; text-transform: uppercase; letter-spacing: .08em; color: #475569; margin: 0 0 9px; }
.statement-content { font-family: Georgia, "Times New Roman", serif; font-size: 14px; line-height: 1.55; overflow-wrap: anywhere; }
.statement-content .statement-display { overflow-x: auto; margin: 10px 0; padding: 2px 0; }
.statement-content .statement-ref { color: #1d4ed8; text-decoration: underline; text-underline-offset: 2px; cursor: pointer; }
.statement-content .statement-list { padding-left: 22px; }
.statement-footnote { color: #475569; font-size: .9em; }
.latex-details { margin-top: 14px; border: 1px solid #e2e8f0; border-radius: 8px; background: #f8fafc; }
.latex-details summary { cursor: pointer; padding: 9px 11px; font-size: 11px; font-weight: 600; color: #334155; }
.latex-tools { display: flex; justify-content: flex-end; padding: 0 9px 6px; }
.copy-latex { display: inline-flex; align-items: center; gap: 6px; padding: 5px 7px; font-size: 10px; }
.copy-latex svg { width: 15px; height: 15px; }
.latex-details pre { margin: 0; border-top: 1px solid #e2e8f0; padding: 10px; max-height: 330px; overflow: auto; white-space: pre-wrap; overflow-wrap: anywhere; font-size: 10px; line-height: 1.45; background: #fff; }
.dep-list { margin-top: 16px; }
.dep-list button { display: block; width: 100%; text-align: left; overflow-wrap: anywhere; margin: 4px 0; padding: 6px 8px; font-size: 11px; }
.empty { color: #94a3b8; font-size: 11px; font-style: italic; }
#help { position: absolute; right: 12px; bottom: 10px; padding: 7px 9px; font-size: 10px; color: #64748b; background: rgba(255,255,255,.86); border: 1px solid #e2e8f0; border-radius: 7px; pointer-events: none; }
#settings-menu { position: fixed; z-index: 40; top: calc(var(--toolbar-h) - 3px); right: 14px; width: 340px; max-height: calc(100vh - var(--toolbar-h) - 12px); overflow: auto; background: rgba(255,255,255,.99); border: 1px solid var(--line); border-radius: 10px; box-shadow: 0 14px 40px rgba(15,23,42,.18); padding: 13px; }
.settings-header { display: flex; align-items: center; justify-content: space-between; margin-bottom: 10px; }
.settings-header h2 { margin: 0; font-size: 14px; }
.settings-group { padding: 10px 0; border-top: 1px solid #e2e8f0; }
.settings-group:first-of-type { border-top: 0; }
.settings-group h3 { margin: 0 0 8px; font-size: 10px; text-transform: uppercase; letter-spacing: .08em; color: #64748b; }
.setting-row { display: grid; grid-template-columns: minmax(0,1fr) auto; align-items: center; gap: 10px; margin: 8px 0; font-size: 12px; }
.setting-row select { min-width: 138px; border: 1px solid var(--line); border-radius: 6px; padding: 6px; background: #fff; }
.setting-row input[type=range] { width: 150px; }
.setting-row.checkbox { grid-template-columns: auto minmax(0,1fr); justify-content: start; }
.setting-row.checkbox input { margin: 0; }
.setting-value { color: #64748b; font-variant-numeric: tabular-nums; min-width: 36px; text-align: right; }
.range-wrap { display: flex; align-items: center; gap: 7px; }
.export-row { display: grid; grid-template-columns: 1fr 1fr; gap: 8px; }
.export-row button { width: 100%; }
.settings-note { margin: 6px 0 0; color: #94a3b8; font-size: 10px; line-height: 1.35; }
@media (max-width: 1050px) {
  .stat-chip { display: none; }
  .brand { min-width: 180px; }
  :root { --left-w: 250px; --right-w: 390px; }
}
</style>
<script>
window.MathJax = {
  loader: {load: ['[tex]/html']},
  tex: {
    packages: {'[+]': ['html']},
    inlineMath: [['\\(', '\\)']],
    displayMath: [['\\[', '\\]']],
    processEscapes: true
  },
  svg: {fontCache: 'global'},
  startup: {typeset: false}
};
</script>
<script>$mathjax_source</script>
</head>
<body>
<header id="toolbar">
  <div class="brand"><h1>NCT dependency graph</h1><p>$source_name</p></div>
  <div class="search-wrap">
    <div class="search-input-wrap">
      <input id="search" type="search" autocomplete="off" spellcheck="false" placeholder="Search labels, titles, statements, or Lean names…" aria-label="Search graph nodes">
      <span id="search-count"></span>
    </div>
    <label class="inverse-search" title="Show nodes that do not match the search term"><input id="search-inverse" type="checkbox"><span>Inverse</span></label>
  </div>
  <span class="stat-chip">$node_count nodes</span>
  <span class="stat-chip">$edge_count dependencies</span>
  <div class="toolbar-actions">
    <button id="zoom-in" class="toolbar-icon" title="Zoom in" aria-label="Zoom in">+</button>
    <button id="zoom-out" class="toolbar-icon" title="Zoom out" aria-label="Zoom out">−</button>
    <button id="fit" title="Fit graph">Fit</button>
    <button id="clear" title="Clear search, selection, and box filter">Clear</button>
    <button id="settings-toggle" title="Open settings" aria-label="Open settings" aria-expanded="false">Settings</button>
  </div>
</header>
<aside id="left-panel">
  <section id="legend-section" class="panel-section">
    <h2>Legend</h2>
    <div class="shape-row"><span class="shape ellipse"></span><span class="legend-caption"><strong>Theorem</strong></span></div>
    <div class="shape-row"><span class="shape box"></span><span class="legend-caption"><strong>Definition</strong></span></div>
    <div class="visibility-row"><span class="opacity-sample"></span><span class="legend-caption"><strong>Public</strong><small>Used outside its section; all Introduction nodes are public.</small></span></div>
    <div class="visibility-row"><span class="opacity-sample private"></span><span class="legend-caption"><strong>Private</strong><small>Used only within its own section.</small></span></div>
    <p class="panel-note">Arrows point from a dependency to the result that uses it.</p>
    $legend
  </section>
  <section id="hierarchy-section" class="panel-section">
    <h2>Document hierarchy</h2>
    <div class="hierarchy">$hierarchy</div>
  </section>
</aside>
<main id="viewport">
  <div id="graph-host">$layout_markup</div>
  <div id="help">Wheel to zoom · drag to pan · click a node or box caption</div>
</main>
<aside id="details" aria-live="polite">
  <div class="details-header"><h2 id="details-title">Node details</h2><button id="close-details" aria-label="Close details">×</button></div>
  <div id="details-body" class="details-body"></div>
</aside>
<div id="settings-menu" hidden>
  <div class="settings-header"><h2>Graph settings</h2><button id="settings-close" aria-label="Close settings">×</button></div>
  <section class="settings-group">
    <h3>Layout</h3>
    <label class="setting-row"><span>Hierarchy visibility</span><select id="setting-hierarchy"><option value="none">None</option><option value="section">Section</option><option value="subsection">Subsection</option></select></label>
    <label class="setting-row checkbox"><input id="setting-definitions" type="checkbox"><span>Include definitions</span></label>
  </section>
  <section class="settings-group">
    <h3>Opacity</h3>
    <label class="setting-row"><span>Public nodes</span><span class="range-wrap"><input id="setting-public-opacity" type="range" min="0" max="100" step="1"><span id="public-opacity-value" class="setting-value"></span></span></label>
    <label class="setting-row"><span>Private nodes</span><span class="range-wrap"><input id="setting-private-opacity" type="range" min="0" max="100" step="1"><span id="private-opacity-value" class="setting-value"></span></span></label>
    <label class="setting-row"><span>Section boxes</span><span class="range-wrap"><input id="setting-section-opacity" type="range" min="0" max="100" step="1"><span id="section-opacity-value" class="setting-value"></span></span></label>
    <label class="setting-row"><span>Subsection boxes</span><span class="range-wrap"><input id="setting-subsection-opacity" type="range" min="0" max="100" step="1"><span id="subsection-opacity-value" class="setting-value"></span></span></label>
  </section>
  <section class="settings-group">
    <h3>Sidebar</h3>
    <label class="setting-row checkbox"><input id="setting-sidebar" type="checkbox"><span>Show sidebar</span></label>
    <label class="setting-row checkbox"><input id="setting-legend" type="checkbox"><span>Show legend</span></label>
    <label class="setting-row checkbox"><input id="setting-document-hierarchy" type="checkbox"><span>Show document hierarchy</span></label>
  </section>
  <section class="settings-group">
    <h3>Export current graph view</h3>
    <div class="export-row"><button id="export-svg">Export SVG</button><button id="export-png">Export PNG</button></div>
    <p class="settings-note">Exports use the active zoom, hierarchy mode, search, box filter, and opacity settings.</p>
  </section>
</div>
<script id="graph-data" type="application/json">$graph_data</script>
<script>
(() => {
  'use strict';
  const data = JSON.parse(document.getElementById('graph-data').textContent);
  const leanUrlPattern = $lean_url_pattern;
  const nodes = new Map(data.nodes.map(node => [node.id, node]));
  const statuses = new Map(data.status_catalog.map(status => [status.id, status]));
  const viewport = document.getElementById('viewport');
  const graphHost = document.getElementById('graph-host');
  const details = document.getElementById('details');
  const detailsTitle = document.getElementById('details-title');
  const detailsBody = document.getElementById('details-body');
  const search = document.getElementById('search');
  const searchInverse = document.getElementById('search-inverse');
  const searchCount = document.getElementById('search-count');
  const settingsMenu = document.getElementById('settings-menu');
  const settingsToggle = document.getElementById('settings-toggle');
  const layoutSlots = new Map([...document.querySelectorAll('.layout-slot')].map(slot => [slot.dataset.layoutKey, slot]));
  const viewStates = new Map();
  const initialViews = new Map();
  for (const [key, slot] of layoutSlots) {
    const svg = slot.querySelector('svg');
    const values = svg.getAttribute('viewBox').trim().split(/\s+/).map(Number);
    const state = {x: values[0], y: values[1], w: values[2], h: values[3]};
    viewStates.set(key, {...state});
    initialViews.set(key, {...state});
  }

  const state = {
    hierarchy: data.settings.grouping_granularity,
    includeDefinitions: Boolean(data.settings.include_definitions),
    publicOpacity: Number(data.settings.public_opacity),
    privateOpacity: Number(data.settings.private_opacity),
    sectionOpacity: Number(data.settings.section_opacity),
    subsectionOpacity: Number(data.settings.subsection_opacity),
    showSidebar: data.settings.show_sidebar !== false,
    showLegend: data.settings.show_legend !== false,
    showDocumentHierarchy: data.settings.show_document_hierarchy !== false,
    inverseSearch: false,
    selectedId: null,
    clusterFilter: null,
    drag: null
  };

  const control = {
    hierarchy: document.getElementById('setting-hierarchy'),
    definitions: document.getElementById('setting-definitions'),
    publicOpacity: document.getElementById('setting-public-opacity'),
    privateOpacity: document.getElementById('setting-private-opacity'),
    sectionOpacity: document.getElementById('setting-section-opacity'),
    subsectionOpacity: document.getElementById('setting-subsection-opacity'),
    sidebar: document.getElementById('setting-sidebar'),
    legend: document.getElementById('setting-legend'),
    documentHierarchy: document.getElementById('setting-document-hierarchy')
  };

  const layoutKey = () => `${state.hierarchy}-${state.includeDefinitions ? 'definitions' : 'theorems'}`;
  const activeSlot = () => layoutSlots.get(layoutKey());
  const activeSvg = () => activeSlot().querySelector('svg');
  const currentView = () => viewStates.get(layoutKey());
  const applyView = () => {
    const view = currentView();
    activeSvg().setAttribute('viewBox', `${view.x} ${view.y} ${view.w} ${view.h}`);
  };
  const nodeElement = id => [...activeSvg().querySelectorAll('[data-node-id]')].find(element => element.dataset.nodeId === id);
  const clamp = (value, minimum, maximum) => Math.max(minimum, Math.min(maximum, value));

  function syncControls() {
    control.hierarchy.value = state.hierarchy;
    control.definitions.checked = state.includeDefinitions;
    control.publicOpacity.value = Math.round(state.publicOpacity * 100);
    control.privateOpacity.value = Math.round(state.privateOpacity * 100);
    control.sectionOpacity.value = Math.round(state.sectionOpacity * 100);
    control.subsectionOpacity.value = Math.round(state.subsectionOpacity * 100);
    control.sidebar.checked = state.showSidebar;
    control.legend.checked = state.showLegend;
    control.documentHierarchy.checked = state.showDocumentHierarchy;
    searchInverse.checked = state.inverseSearch;
    document.getElementById('public-opacity-value').textContent = `${Math.round(state.publicOpacity * 100)}%`;
    document.getElementById('private-opacity-value').textContent = `${Math.round(state.privateOpacity * 100)}%`;
    document.getElementById('section-opacity-value').textContent = `${Math.round(state.sectionOpacity * 100)}%`;
    document.getElementById('subsection-opacity-value').textContent = `${Math.round(state.subsectionOpacity * 100)}%`;
  }

  function applyPresentationSettings() {
    const root = document.documentElement;
    root.style.setProperty('--public-opacity', state.publicOpacity);
    root.style.setProperty('--private-opacity', state.privateOpacity);
    root.style.setProperty('--public-edge-opacity', state.publicOpacity * .48);
    root.style.setProperty('--private-edge-opacity', state.privateOpacity * .48);
    root.style.setProperty('--section-opacity', state.sectionOpacity);
    root.style.setProperty('--subsection-opacity', state.subsectionOpacity);
    document.body.classList.toggle('sidebar-hidden', !state.showSidebar);
    document.getElementById('legend-section').hidden = !state.showLegend;
    document.getElementById('hierarchy-section').hidden = !state.showDocumentHierarchy;
    syncControls();
  }

  function activateLayout({preserveSelection = true} = {}) {
    for (const [key, slot] of layoutSlots) slot.classList.toggle('active', key === layoutKey());
    applyView();
    applyFilters();
    if (preserveSelection && state.selectedId && nodeElement(state.selectedId)) {
      nodeElement(state.selectedId).classList.add('selected');
      markIncidentEdges(state.selectedId);
    }
  }

  function resetView() {
    viewStates.set(layoutKey(), {...initialViews.get(layoutKey())});
    applyView();
  }

  function zoomAt(factor, clientX = null, clientY = null) {
    const svg = activeSvg();
    const view = currentView();
    const initial = initialViews.get(layoutKey());
    const rect = svg.getBoundingClientRect();
    const px = clientX === null ? .5 : clamp((clientX - rect.left) / Math.max(rect.width, 1), 0, 1);
    const py = clientY === null ? .5 : clamp((clientY - rect.top) / Math.max(rect.height, 1), 0, 1);
    const newW = clamp(view.w * factor, initial.w * .002, initial.w * 8);
    const newH = clamp(view.h * factor, initial.h * .002, initial.h * 8);
    view.x += (view.w - newW) * px;
    view.y += (view.h - newH) * py;
    view.w = newW;
    view.h = newH;
    applyView();
  }

  function clusterContains(node, filter) {
    if (!filter) return true;
    if (filter.kind === 'section') return node.section_id === filter.sectionId;
    return node.section_id === filter.sectionId && (node.subsection_id || '') === (filter.subsectionId || '');
  }

  const searchBlob = new Map(data.nodes.map(node => [
    node.id,
    [node.label, node.title, node.statement_latex || '', ...(node.lean_names || [])].join('\n').toLowerCase()
  ]));

  function applyFilters() {
    const svg = activeSvg();
    const query = search.value.trim().toLowerCase();
    const presentIds = new Set([...svg.querySelectorAll('.dep-node')].map(group => group.dataset.nodeId));
    const visibleIds = new Set();
    for (const group of svg.querySelectorAll('.dep-node')) {
      const node = nodes.get(group.dataset.nodeId);
      const containsQuery = searchBlob.get(node.id).includes(query);
      const matchesSearch = !query || (state.inverseSearch ? !containsQuery : containsQuery);
      const matchesCluster = clusterContains(node, state.clusterFilter);
      const visible = matchesSearch && matchesCluster;
      group.classList.toggle('filtered-out', !visible);
      group.classList.toggle('search-match', Boolean(query) && visible);
      if (visible) visibleIds.add(node.id);
    }
    for (const edge of svg.querySelectorAll('.dep-edge')) {
      const visible = visibleIds.has(edge.dataset.source) && visibleIds.has(edge.dataset.target);
      edge.classList.toggle('filtered-out', !visible);
    }
    for (const cluster of svg.querySelectorAll('.dep-cluster')) {
      let visible = true;
      if (state.clusterFilter) {
        if (state.clusterFilter.kind === 'section') {
          visible = cluster.dataset.sectionId === state.clusterFilter.sectionId;
        } else {
          const exact = cluster.dataset.clusterKind === 'subsection' && cluster.dataset.sectionId === state.clusterFilter.sectionId && (cluster.dataset.subsectionId || '') === (state.clusterFilter.subsectionId || '');
          visible = exact;
        }
      }
      cluster.classList.toggle('filtered-out', !visible);
      const caption = cluster.querySelector('.cluster-caption');
      if (caption) {
        const active = state.clusterFilter && cluster.dataset.clusterKind === state.clusterFilter.kind && cluster.dataset.sectionId === state.clusterFilter.sectionId && (cluster.dataset.subsectionId || '') === (state.clusterFilter.subsectionId || '');
        caption.classList.toggle('active', Boolean(active));
      }
    }
    for (const button of document.querySelectorAll('.hierarchy-filter')) {
      button.classList.toggle('active', Boolean(state.clusterFilter && state.clusterFilter.kind === 'section' && button.dataset.hierarchySection === state.clusterFilter.sectionId));
    }
    searchCount.textContent = query ? `${visibleIds.size} shown` : '';
    if (state.selectedId && (!presentIds.has(state.selectedId) || !visibleIds.has(state.selectedId))) clearSelection();
    return [...visibleIds];
  }

  function toggleClusterFilter(filter) {
    const current = state.clusterFilter;
    const same = current && current.kind === filter.kind && current.sectionId === filter.sectionId && (current.subsectionId || '') === (filter.subsectionId || '');
    state.clusterFilter = same ? null : filter;
    applyFilters();
  }

  function element(tag, text = null, className = null) {
    const item = document.createElement(tag);
    if (text !== null) item.textContent = text;
    if (className) item.className = className;
    return item;
  }

  function leanDocumentationUrl(name) {
    if (!leanUrlPattern) return null;
    return leanUrlPattern.split('{lean_name}').join(encodeURIComponent(name));
  }

  function dependencyList(title, ids) {
    const section = element('section', null, 'dep-list');
    section.appendChild(element('h3', `${title} (${ids.length})`));
    if (!ids.length) {
      section.appendChild(element('div', 'None', 'empty'));
      return section;
    }
    ids.forEach(id => {
      const button = element('button', id);
      button.type = 'button';
      button.addEventListener('click', () => selectNode(id, true));
      section.appendChild(button);
    });
    return section;
  }

  function markIncidentEdges(id) {
    const svg = activeSvg();
    svg.querySelectorAll('.dep-edge.incident').forEach(edge => edge.classList.remove('incident'));
    svg.querySelectorAll('.dep-edge').forEach(edge => {
      if (edge.dataset.source === id || edge.dataset.target === id) edge.classList.add('incident');
    });
  }

  async function typesetStatement(container) {
    if (!window.MathJax || !MathJax.startup) return;
    try {
      await MathJax.startup.promise;
      if (MathJax.typesetClear) MathJax.typesetClear([container]);
      await MathJax.typesetPromise([container]);
    } catch (error) {
      console.error('MathJax statement rendering failed', error);
    }
  }

  const copyIcon = `<svg viewBox="0 0 24 24" aria-hidden="true" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round"><rect x="8" y="8" width="11" height="11" rx="2"></rect><path d="M16 8V6a2 2 0 0 0-2-2H6a2 2 0 0 0-2 2v8a2 2 0 0 0 2 2h2"></path></svg>`;

  function fallbackCopy(text) {
    const textarea = document.createElement('textarea');
    textarea.value = text;
    textarea.style.position = 'fixed';
    textarea.style.opacity = '0';
    document.body.appendChild(textarea);
    textarea.select();
    document.execCommand('copy');
    textarea.remove();
  }

  function addStatement(node) {
    const panel = element('section', null, 'statement-panel');
    panel.appendChild(element('h3', 'Statement'));
    const content = element('div', null, 'statement-content');
    content.innerHTML = node.statement_html || '<span class="empty">Statement unavailable.</span>';
    panel.appendChild(content);

    const latexDetails = element('details', null, 'latex-details');
    latexDetails.appendChild(element('summary', 'Expanded LaTeX'));
    const tools = element('div', null, 'latex-tools');
    const copy = element('button', null, 'copy-latex');
    copy.type = 'button';
    copy.title = 'Copy expanded LaTeX';
    copy.setAttribute('aria-label', 'Copy expanded LaTeX');
    copy.innerHTML = `${copyIcon}<span>Copy</span>`;
    copy.addEventListener('click', async event => {
      event.preventDefault();
      event.stopPropagation();
      try {
        if (navigator.clipboard && window.isSecureContext) await navigator.clipboard.writeText(node.statement_latex || '');
        else fallbackCopy(node.statement_latex || '');
        copy.querySelector('span').textContent = 'Copied';
        setTimeout(() => { if (copy.isConnected) copy.querySelector('span').textContent = 'Copy'; }, 1200);
      } catch (error) {
        fallbackCopy(node.statement_latex || '');
      }
    });
    tools.appendChild(copy);
    latexDetails.appendChild(tools);
    const pre = element('pre');
    pre.appendChild(element('code', node.statement_latex || ''));
    latexDetails.appendChild(pre);
    panel.appendChild(latexDetails);
    detailsBody.appendChild(panel);
    typesetStatement(content);
  }

  function ensureNodeVisible(node) {
    let changedLayout = false;
    if (node.kind === 'definition' && !state.includeDefinitions) {
      state.includeDefinitions = true;
      changedLayout = true;
    }
    if (changedLayout) activateLayout({preserveSelection: false});
    else applyFilters();
    syncControls();
  }

  function selectNode(id, focus = false, toggle = false) {
    const node = nodes.get(id);
    if (!node) return;
    if (toggle && state.selectedId === id) {
      clearSelection();
      return;
    }
    ensureNodeVisible(node);
    const group = nodeElement(id);
    if (!group) return;
    activeSvg().querySelectorAll('.dep-node.selected').forEach(element => element.classList.remove('selected'));
    group.classList.add('selected');
    markIncidentEdges(id);
    state.selectedId = id;
    detailsTitle.textContent = node.label;
    detailsBody.replaceChildren();
    const dl = element('dl', null, 'meta-grid');
    const kindLabel = `${node.environment_name}${node.number ? ` ${node.number}` : ''}`;
    const rows = [
      ['Kind', kindLabel],
      ['Status', statuses.get(node.status)?.name || node.status],
      ['Visibility', `${node.visibility} — ${node.visibility_reason || ''}`],
      ['Section', node.section_titles.join(' › ')],
      ['Source', `${data.source.latex_file}:${node.source.line_start}–${node.source.line_end}`],
      ['Lean names', node.lean_names]
    ];
    rows.forEach(([key, value]) => {
      dl.appendChild(element('dt', key));
      const description = element('dd');
      if (key === 'Lean names' && Array.isArray(value)) {
        if (!value.length) {
          description.textContent = '(none yet)';
        } else if (!leanUrlPattern) {
          description.textContent = value.join(', ');
        } else {
          const links = element('span', null, 'lean-name-links');
          value.forEach(name => {
            const link = element('a', name, 'lean-name-link');
            link.href = leanDocumentationUrl(name);
            link.title = `Open Lean API documentation for ${name}`;
            links.appendChild(link);
          });
          description.appendChild(links);
        }
      } else {
        description.textContent = value;
      }
      dl.appendChild(description);
    });
    detailsBody.appendChild(dl);
    addStatement(node);
    detailsBody.appendChild(dependencyList('Uses', node.uses));
    detailsBody.appendChild(dependencyList('Used by', node.used_by));
    details.classList.add('open');
    viewport.classList.add('details-open');
    if (focus && !group.classList.contains('filtered-out')) focusNode(id);
  }

  function focusNode(id) {
    const group = nodeElement(id);
    const svg = activeSvg();
    if (!group) return;
    const screenBox = group.getBoundingClientRect();
    const ctm = svg.getScreenCTM();
    if (!ctm || !screenBox.width || !screenBox.height) return;
    const inverse = ctm.inverse();
    const topLeft = new DOMPoint(screenBox.left, screenBox.top).matrixTransform(inverse);
    const bottomRight = new DOMPoint(screenBox.right, screenBox.bottom).matrixTransform(inverse);
    const box = {
      x: Math.min(topLeft.x, bottomRight.x),
      y: Math.min(topLeft.y, bottomRight.y),
      width: Math.abs(bottomRight.x - topLeft.x),
      height: Math.abs(bottomRight.y - topLeft.y)
    };
    const initial = initialViews.get(layoutKey());
    const aspect = Math.max(.2, svg.clientWidth / Math.max(1, svg.clientHeight));
    let w = Math.max(box.width * 8, initial.w * .055);
    let h = Math.max(box.height * 12, initial.h * .055);
    if (w / h < aspect) w = h * aspect; else h = w / aspect;
    viewStates.set(layoutKey(), {x: box.x + box.width / 2 - w / 2, y: box.y + box.height / 2 - h / 2, w, h});
    applyView();
  }

  function clearSelection() {
    state.selectedId = null;
    for (const slot of layoutSlots.values()) slot.querySelectorAll('.selected, .incident').forEach(element => element.classList.remove('selected', 'incident'));
    details.classList.remove('open');
    viewport.classList.remove('details-open');
  }

  function clearAll() {
    search.value = '';
    state.clusterFilter = null;
    clearSelection();
    applyFilters();
  }

  function openSettings(open) {
    settingsMenu.hidden = !open;
    settingsToggle.setAttribute('aria-expanded', String(open));
  }

  function exportClone() {
    const source = activeSvg();
    const clone = source.cloneNode(true);
    clone.removeAttribute('id');
    clone.querySelectorAll('.filtered-out').forEach(element => element.remove());
    const viewBox = source.getAttribute('viewBox');
    const [x, y, width, height] = viewBox.trim().split(/\s+/).map(Number);
    const viewportRect = viewport.getBoundingClientRect();
    clone.setAttribute('viewBox', viewBox);
    clone.setAttribute('width', String(Math.max(1, Math.round(viewportRect.width))));
    clone.setAttribute('height', String(Math.max(1, Math.round(viewportRect.height))));
    clone.setAttribute('xmlns', 'http://www.w3.org/2000/svg');
    const style = document.createElementNS('http://www.w3.org/2000/svg', 'style');
    style.textContent = `
      .dep-node{opacity:${state.publicOpacity}}
      .dep-node.visibility-private{opacity:${state.privateOpacity}}
      .dep-cluster.cluster-level-1>.cluster-box{fill:#cbd5e1;fill-opacity:${state.sectionOpacity};stroke:#94a3b8;stroke-opacity:.78;stroke-width:1.1}
      .dep-cluster.cluster-level-2>.cluster-box{fill:#dbeafe;fill-opacity:${state.subsectionOpacity};stroke:#cbd5e1;stroke-opacity:.72;stroke-width:.9;stroke-dasharray:4 3}
      .cluster-caption-hit{fill:transparent;stroke:none}.cluster-caption-text{font-family:Helvetica,Arial,sans-serif;fill:#334155;font-size:11px;font-weight:600;opacity:.82}.cluster-level-2 .cluster-caption-text{font-size:9px;font-weight:500;fill:#475569}
      .dep-edge{--edge-opacity:${state.publicOpacity * .48}}.dep-edge.visibility-private{--edge-opacity:${state.privateOpacity * .48}}.dep-edge path{stroke:#64748b;stroke-opacity:var(--edge-opacity)}.dep-edge polygon{fill:#64748b;stroke:#64748b;fill-opacity:var(--edge-opacity);stroke-opacity:var(--edge-opacity)}.dep-edge.incident{--edge-opacity:${state.publicOpacity}}.dep-edge.visibility-private.incident{--edge-opacity:${state.privateOpacity}}.dep-edge.incident path{stroke:#dc2626;stroke-width:1.8px}.dep-edge.incident polygon{fill:#dc2626;stroke:#dc2626}
      .dep-node.search-match>ellipse,.dep-node.search-match>polygon,.dep-node.search-match>path{stroke:#f59e0b!important;stroke-width:4px!important}.dep-node.selected>ellipse,.dep-node.selected>polygon,.dep-node.selected>path{stroke:#dc2626!important;stroke-width:4px!important}
    `;
    clone.insertBefore(style, clone.firstChild);
    const background = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
    background.setAttribute('x', String(x));
    background.setAttribute('y', String(y));
    background.setAttribute('width', String(width));
    background.setAttribute('height', String(height));
    background.setAttribute('fill', '#f8fafc');
    clone.insertBefore(background, style.nextSibling);
    return new XMLSerializer().serializeToString(clone);
  }

  function downloadBlob(blob, filename) {
    const url = URL.createObjectURL(blob);
    const anchor = document.createElement('a');
    anchor.href = url;
    anchor.download = filename;
    document.body.appendChild(anchor);
    anchor.click();
    anchor.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }

  function exportSvg() {
    const source = `<?xml version="1.0" encoding="UTF-8"?>\n${exportClone()}`;
    downloadBlob(new Blob([source], {type: 'image/svg+xml;charset=utf-8'}), 'nct-dependency-current-view.svg');
  }

  function exportPng() {
    const source = exportClone();
    const svgBlob = new Blob([source], {type: 'image/svg+xml;charset=utf-8'});
    const url = URL.createObjectURL(svgBlob);
    const image = new Image();
    image.onload = () => {
      const rect = viewport.getBoundingClientRect();
      const scale = 2;
      const canvas = document.createElement('canvas');
      canvas.width = Math.max(1, Math.round(rect.width * scale));
      canvas.height = Math.max(1, Math.round(rect.height * scale));
      const context = canvas.getContext('2d');
      context.setTransform(scale, 0, 0, scale, 0, 0);
      context.drawImage(image, 0, 0, rect.width, rect.height);
      canvas.toBlob(blob => {
        if (blob) downloadBlob(blob, 'nct-dependency-current-view.png');
        URL.revokeObjectURL(url);
      }, 'image/png');
    };
    image.onerror = () => URL.revokeObjectURL(url);
    image.src = url;
  }

  graphHost.addEventListener('wheel', event => {
    event.preventDefault();
    zoomAt(Math.exp(event.deltaY * .00125), event.clientX, event.clientY);
  }, {passive: false});

  graphHost.addEventListener('pointerdown', event => {
    const svg = activeSvg();
    if (event.target.closest('[data-node-id], [data-cluster-caption]')) return;
    const view = currentView();
    state.drag = {id: event.pointerId, x: event.clientX, y: event.clientY, vx: view.x, vy: view.y, svg};
    svg.setPointerCapture(event.pointerId);
    svg.classList.add('panning');
  });

  graphHost.addEventListener('pointermove', event => {
    if (!state.drag || state.drag.id !== event.pointerId) return;
    const rect = state.drag.svg.getBoundingClientRect();
    const view = currentView();
    view.x = state.drag.vx - (event.clientX - state.drag.x) * view.w / Math.max(rect.width, 1);
    view.y = state.drag.vy - (event.clientY - state.drag.y) * view.h / Math.max(rect.height, 1);
    applyView();
  });

  function endDrag(event) {
    if (!state.drag || state.drag.id !== event.pointerId) return;
    state.drag.svg.classList.remove('panning');
    state.drag = null;
  }
  graphHost.addEventListener('pointerup', endDrag);
  graphHost.addEventListener('pointercancel', endDrag);

  graphHost.addEventListener('click', event => {
    const nodeGroup = event.target.closest('[data-node-id]');
    if (nodeGroup) {
      event.stopPropagation();
      selectNode(nodeGroup.dataset.nodeId, false, true);
      return;
    }
    const caption = event.target.closest('[data-cluster-caption]');
    if (caption) {
      event.stopPropagation();
      toggleClusterFilter({kind: caption.dataset.clusterKind, sectionId: caption.dataset.sectionId, subsectionId: caption.dataset.subsectionId || ''});
    }
  });

  graphHost.addEventListener('keydown', event => {
    const nodeGroup = event.target.closest('[data-node-id]');
    if (nodeGroup && (event.key === 'Enter' || event.key === ' ')) {
      event.preventDefault();
      selectNode(nodeGroup.dataset.nodeId, true, true);
      return;
    }
    const caption = event.target.closest('[data-cluster-caption]');
    if (caption && (event.key === 'Enter' || event.key === ' ')) {
      event.preventDefault();
      toggleClusterFilter({kind: caption.dataset.clusterKind, sectionId: caption.dataset.sectionId, subsectionId: caption.dataset.subsectionId || ''});
    }
  });

  details.addEventListener('click', event => {
    const anchor = event.target.closest('a');
    if (!anchor) return;
    const href = anchor.getAttribute('href') || '';
    if (href.startsWith('nct-node:')) {
      event.preventDefault();
      selectNode(decodeURIComponent(href.slice('nct-node:'.length)), true);
    }
  });

  search.addEventListener('input', applyFilters);
  searchInverse.addEventListener('change', () => {
    state.inverseSearch = searchInverse.checked;
    applyFilters();
  });
  search.addEventListener('keydown', event => {
    if (event.key === 'Enter') {
      const matches = applyFilters();
      if (matches.length) selectNode(matches[0], true);
    }
    if (event.key === 'Escape') clearAll();
  });

  document.querySelectorAll('.hierarchy-filter').forEach(button => {
    button.addEventListener('click', () => toggleClusterFilter({kind: 'section', sectionId: button.dataset.hierarchySection, subsectionId: ''}));
  });

  control.hierarchy.addEventListener('change', () => {
    state.hierarchy = control.hierarchy.value;
    activateLayout();
  });
  control.definitions.addEventListener('change', () => {
    state.includeDefinitions = control.definitions.checked;
    activateLayout();
  });
  for (const [input, property, cssProperty, outputId] of [
    [control.publicOpacity, 'publicOpacity', '--public-opacity', 'public-opacity-value'],
    [control.privateOpacity, 'privateOpacity', '--private-opacity', 'private-opacity-value'],
    [control.sectionOpacity, 'sectionOpacity', '--section-opacity', 'section-opacity-value'],
    [control.subsectionOpacity, 'subsectionOpacity', '--subsection-opacity', 'subsection-opacity-value']
  ]) {
    input.addEventListener('input', () => {
      state[property] = Number(input.value) / 100;
      document.documentElement.style.setProperty(cssProperty, state[property]);
      if (property === 'publicOpacity') document.documentElement.style.setProperty('--public-edge-opacity', state[property] * .48);
      if (property === 'privateOpacity') document.documentElement.style.setProperty('--private-edge-opacity', state[property] * .48);
      document.getElementById(outputId).textContent = `${input.value}%`;
    });
  }
  control.sidebar.addEventListener('change', () => { state.showSidebar = control.sidebar.checked; applyPresentationSettings(); });
  control.legend.addEventListener('change', () => { state.showLegend = control.legend.checked; applyPresentationSettings(); });
  control.documentHierarchy.addEventListener('change', () => { state.showDocumentHierarchy = control.documentHierarchy.checked; applyPresentationSettings(); });

  settingsToggle.addEventListener('click', event => {
    event.stopPropagation();
    openSettings(settingsMenu.hidden);
  });
  document.getElementById('settings-close').addEventListener('click', () => openSettings(false));
  document.addEventListener('pointerdown', event => {
    if (!settingsMenu.hidden && !settingsMenu.contains(event.target) && event.target !== settingsToggle) openSettings(false);
  });
  document.addEventListener('keydown', event => { if (event.key === 'Escape' && !settingsMenu.hidden) openSettings(false); });

  document.getElementById('zoom-in').addEventListener('click', () => zoomAt(.72));
  document.getElementById('zoom-out').addEventListener('click', () => zoomAt(1.38));
  document.getElementById('fit').addEventListener('click', resetView);
  document.getElementById('clear').addEventListener('click', clearAll);
  document.getElementById('close-details').addEventListener('click', clearSelection);
  document.getElementById('export-svg').addEventListener('click', exportSvg);
  document.getElementById('export-png').addEventListener('click', exportPng);

  applyPresentationSettings();
  activateLayout({preserveSelection: false});
})();
</script>
</body>
</html>
'''

    replacements = {
        '$private_opacity': str(float(settings['private_opacity'])),
        '$public_opacity': str(float(settings['public_opacity'])),
        '$private_edge_opacity': str(float(settings['private_opacity']) * 0.48),
        '$public_edge_opacity': str(float(settings['public_opacity']) * 0.48),
        '$section_opacity': str(float(settings['section_opacity'])),
        '$subsection_opacity': str(float(settings['subsection_opacity'])),
        '$mathjax_source': mathjax_source,
        '$source_name': source_name,
        '$node_count': str(stats['nodes_total']),
        '$edge_count': str(stats['edges_total']),
        '$legend': legend,
        '$hierarchy': hierarchy,
        '$layout_markup': layout_markup,
        '$graph_data': graph_data,
        '$lean_url_pattern': lean_url_pattern_json,
    }
    for marker, value in replacements.items():
        template = template.replace(marker, value)
    return template


# ---------------------------------------------------------------------------
# Command line
# ---------------------------------------------------------------------------

def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("graph_json", type=Path, help="input graph JSON")
    parser.add_argument("output_html", type=Path, help="standalone output HTML")
    parser.add_argument("--dot-binary", default="dot", help="Graphviz dot executable used for local layouts")
    parser.add_argument("--neato-binary", default="neato", help="Graphviz neato executable used for fixed-position SVG output")
    parser.add_argument("--mathjax-js", type=Path, help="local MathJax tex-svg-full.js bundle")
    parser.add_argument(
        "--lean-url-pattern",
        help="URL template containing {lean_name}; each name is URL-encoded and inserted into its link",
    )
    parser.add_argument("--dot-output", type=Path, help="optional fixed-position DOT for the default layout")
    parser.add_argument("--svg-output", type=Path, help="optional SVG for the default layout")
    parser.add_argument("--layout-metadata-output", type=Path, help="optional JSON containing computed node and cluster geometry")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if not args.graph_json.is_file():
        print(f"error: graph JSON not found: {args.graph_json}", file=sys.stderr)
        return 2
    try:
        validate_lean_url_pattern(args.lean_url_pattern)
        graph = json.loads(args.graph_json.read_text(encoding="utf-8"))
        validate_graph(graph)
        node_to_token, token_to_node = node_tokens(graph)
        layouts: dict[str, LayoutGeometry] = {}
        dot_sources: dict[str, str] = {}
        for mode in ("none", "section", "subsection"):
            for include_definitions in (False, True):
                print(f"computing layout {mode} / definitions={include_definitions}", flush=True)
                geometry = hierarchy_layout_geometry(graph, mode, include_definitions, args.dot_binary, node_to_token)
                _, dot_source = render_layout_svg(graph, geometry, node_to_token, token_to_node, args.neato_binary)
                layouts[geometry.key] = geometry
                dot_sources[geometry.key] = dot_source
        mathjax_path = find_mathjax_bundle(args.mathjax_js)
        mathjax_source = mathjax_path.read_text(encoding="utf-8")
        output = build_html(graph, layouts, mathjax_source, args.lean_url_pattern)
    except (OSError, json.JSONDecodeError, GraphFormatError, RuntimeError, ET.ParseError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    args.output_html.parent.mkdir(parents=True, exist_ok=True)
    args.output_html.write_text(output, encoding="utf-8")
    default_key = f"{graph['settings']['grouping_granularity']}-{'definitions' if graph['settings']['include_definitions'] else 'theorems'}"
    if args.dot_output:
        args.dot_output.parent.mkdir(parents=True, exist_ok=True)
        args.dot_output.write_text(dot_sources[default_key], encoding="utf-8")
    if args.svg_output:
        args.svg_output.parent.mkdir(parents=True, exist_ok=True)
        args.svg_output.write_text(layouts[default_key].svg, encoding="utf-8")
    if args.layout_metadata_output:
        metadata = {
            key: {
                "mode": layout.mode,
                "include_definitions": layout.include_definitions,
                "width": layout.width,
                "height": layout.height,
                "nodes": {node_id: vars(geometry) for node_id, geometry in layout.nodes.items()},
                "clusters": [vars(cluster) for cluster in layout.clusters],
            }
            for key, layout in layouts.items()
        }
        args.layout_metadata_output.parent.mkdir(parents=True, exist_ok=True)
        args.layout_metadata_output.write_text(json.dumps(metadata, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"wrote {args.output_html}: six independent layouts, {len(graph['nodes'])} JSON nodes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
