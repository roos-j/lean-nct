#!/usr/bin/env python3
"""Extract a rigid dependency-graph JSON document from a LaTeX blueprint.

The extractor reads theorem-like environments, definitions, section hierarchy,
legacy ``\\using`` annotations, typed ``\\uses``/``\\usesdefs`` annotations,
and Lean metadata supplied by ``\\lean`` and ``\\leanok``.  It also compiles the
source (unless an auxiliary file is supplied) so that every ``\\ref`` and
``\\eqref`` appearing in a statement is resolved to the exact number produced by
LaTeX.  User-defined macros are expanded before statement data is written to JSON.

Metadata is validated conservatively.  An invalid dependency, Lean name entry, or
status annotation is omitted while parsing continues.  Every omission is reported
with the source line and the involved node labels.
"""

from __future__ import annotations

import argparse
import bisect
import hashlib
import html
import json
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.parse
from collections import Counter, defaultdict, deque
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Sequence

SCHEMA_NAME = "nct-dependency-graph"
SCHEMA_VERSION = "2.0.0"
PARSER_NAME = "latex_to_graph_json"
PARSER_VERSION = "2.1.1"

THEOREM_ENVIRONMENTS = {
    "theorem",
    "theorem*",
    "exttheorem",
    "lemma",
    "prop",
    "proposition",
    "corollary",
}
DEFINITION_ENVIRONMENTS = {"definition"}
NODE_ENVIRONMENTS = THEOREM_ENVIRONMENTS | DEFINITION_ENVIRONMENTS

ENVIRONMENT_DISPLAY_NAMES = {
    "theorem": "Theorem",
    "theorem*": "Theorem",
    "exttheorem": "External Theorem",
    "lemma": "Lemma",
    "prop": "Proposition",
    "proposition": "Proposition",
    "corollary": "Corollary",
    "definition": "Definition",
}

STATUS_CATALOG: list[dict[str, Any]] = [
    {
        "id": "not_ready",
        "name": "Not ready to be formalized",
        "meaning": "The mathematical statement is not yet ready to be stated in Lean.",
        "style": {"border": "#FFAA33", "fill": "#FFFFFF", "text": "#111827", "border_width": 2.2},
    },
    {
        "id": "can_state",
        "name": "Ready to be formalized",
        "meaning": "The mathematical statement is ready to be stated in Lean.",
        "style": {"border": "#2563EB", "fill": "#FFFFFF", "text": "#111827", "border_width": 2.2},
    },
    {
        "id": "stated",
        "name": "Statement formalized",
        "meaning": "The statement has been formalized, but its proof is not yet ready.",
        "style": {"border": "#16A34A", "fill": "#FFFFFF", "text": "#111827", "border_width": 2.2},
    },
    {
        "id": "can_prove",
        "name": "Proof ready to be formalized",
        "meaning": "The statement is formalized and the proof is ready to be formalized.",
        "style": {"border": "#2563EB", "fill": "#A3D6FF", "text": "#111827", "border_width": 2.2},
    },
    {
        "id": "proved",
        "name": "Proof formalized",
        "meaning": "The statement and proof have been formalized.",
        "style": {"border": "#16A34A", "fill": "#9CEC8B", "text": "#111827", "border_width": 2.2},
    },
    {
        "id": "defined",
        "name": "Definition formalized",
        "meaning": "The definition has been formalized.",
        "style": {"border": "#16A34A", "fill": "#B0ECA3", "text": "#111827", "border_width": 2.2},
    },
    {
        "id": "fully_proved",
        "name": "Proof complete",
        "meaning": "The proof and all its dependencies are fully formalized.",
        "style": {"border": "#0B6B3A", "fill": "#1CAC78", "text": "#FFFFFF", "border_width": 2.2},
    },
    {
        "id": "external_dependency",
        "name": "External dependency",
        "meaning": "The statement is supplied outside this blueprint.",
        "style": {"border": "#006400", "fill": "#FFFFFF", "text": "#111827", "border_width": 2.2},
    },
]
STATUS_IDS = {entry["id"] for entry in STATUS_CATALOG}
HEADING_LEVELS = {"section": 1, "subsection": 2, "subsubsection": 3}
AUTHOR_ANNOTATION_COMMANDS = {"jr", "pd", "ls", "ct", "comment"}
ARGUMENT_METADATA_COMMANDS = {"using", "uses", "usesdefs", "lean"}
FLAG_METADATA_COMMANDS = {"leanok"}
VERBATIM_ENVIRONMENTS = {"verbatim", "verbatim*", "lstlisting", "minted"}
REMOVED_METADATA_COMMANDS = {
    "label",
    "using",
    "uses",
    "usesdefs",
    "lean",
    "index",
} | AUTHOR_ANNOTATION_COMMANDS


@dataclass
class Heading:
    id: str
    kind: str
    level: int
    title_tex: str
    title: str
    label: str | None
    synthetic: bool
    starred: bool
    ordinal: int
    start: int
    line: int
    number: str | None = None
    role: str | None = None
    parent_id: str | None = None
    children: list[str] = field(default_factory=list)


@dataclass
class ParsedEnvironment:
    environment: str
    start: int
    end: int
    content_start: int
    content_end: int
    title_tex: str | None
    label: str | None
    metadata_commands: list["MetadataCommand"]
    metadata_parse_diagnostics: list[dict[str, Any]]
    line_start: int
    line_end: int


@dataclass(frozen=True)
class MetadataCommand:
    """A metadata command occurring inside one theorem/definition environment."""

    name: str
    source_line: int
    raw_argument: str | None
    values: tuple[str, ...]
    empty_item_count: int = 0


@dataclass
class MacroDefinition:
    name: str
    argument_count: int
    body: str
    optional_default: str | None
    source_line: int
    declaration: str


# ---------------------------------------------------------------------------
# Basic TeX scanning
# ---------------------------------------------------------------------------

def strip_comments_preserve_layout(text: str) -> str:
    """Mask unescaped TeX comments with spaces while preserving offsets."""
    chars = list(text)
    i = 0
    while i < len(chars):
        if chars[i] == "%":
            backslashes = 0
            j = i - 1
            while j >= 0 and chars[j] == "\\":
                backslashes += 1
                j -= 1
            if backslashes % 2 == 0:
                while i < len(chars) and chars[i] not in "\r\n":
                    chars[i] = " "
                    i += 1
                continue
        i += 1
    return "".join(chars)


def skip_space(text: str, pos: int) -> int:
    while pos < len(text) and text[pos].isspace():
        pos += 1
    return pos


def is_escaped(text: str, pos: int) -> bool:
    count = 0
    pos -= 1
    while pos >= 0 and text[pos] == "\\":
        count += 1
        pos -= 1
    return count % 2 == 1


def read_balanced(text: str, pos: int, opener: str = "{", closer: str = "}") -> tuple[str, int]:
    if pos >= len(text) or text[pos] != opener:
        raise ValueError(f"expected {opener!r} at offset {pos}")
    depth = 0
    start = pos + 1
    i = pos
    while i < len(text):
        char = text[i]
        if char == "\\":
            i += 2
            continue
        if char == opener:
            depth += 1
        elif char == closer:
            depth -= 1
            if depth == 0:
                return text[start:i], i + 1
        i += 1
    raise ValueError(f"unterminated {opener}{closer} group at offset {pos}")


def read_command_name(text: str, pos: int) -> tuple[str, int] | None:
    if pos >= len(text) or text[pos] != "\\":
        return None
    if pos + 1 >= len(text):
        return "", pos + 1
    if text[pos + 1].isalpha() or text[pos + 1] == "@":
        end = pos + 2
        while end < len(text) and (text[end].isalpha() or text[end] == "@"):
            end += 1
        return text[pos + 1 : end], end
    return text[pos + 1], pos + 2


def parse_command_group(text: str, command_end: int) -> tuple[str, int] | None:
    pos = skip_space(text, command_end)
    if pos >= len(text) or text[pos] != "{":
        return None
    return read_balanced(text, pos)


def split_top_level_commas(value: str) -> list[str]:
    parts: list[str] = []
    depth = 0
    start = 0
    i = 0
    while i < len(value):
        char = value[i]
        if char == "\\":
            i += 2
            continue
        if char in "{[(":
            depth += 1
        elif char in "}])":
            depth = max(0, depth - 1)
        elif char == "," and depth == 0:
            item = value[start:i].strip()
            if item:
                parts.append(item)
            start = i + 1
        i += 1
    item = value[start:].strip()
    if item:
        parts.append(item)
    return parts


def split_top_level_commas_with_empty_count(value: str) -> tuple[list[str], int]:
    """Split a metadata list and count empty top-level entries.

    Empty entries are not returned.  They are counted so that valid neighboring
    entries can still be retained while the malformed entries are diagnosed and
    omitted conservatively.
    """

    raw_parts: list[str] = []
    depth = 0
    start = 0
    i = 0
    while i < len(value):
        char = value[i]
        if char == "\\":
            i += 2
            continue
        if char in "{[(":
            depth += 1
        elif char in "}])":
            depth = max(0, depth - 1)
        elif char == "," and depth == 0:
            raw_parts.append(value[start:i].strip())
            start = i + 1
        i += 1
    raw_parts.append(value[start:].strip())
    values = [item for item in raw_parts if item]
    empty_count = sum(1 for item in raw_parts if not item)
    return values, empty_count


def make_line_starts(text: str) -> list[int]:
    starts = [0]
    starts.extend(match.end() for match in re.finditer("\n", text))
    return starts


def line_number(line_starts: Sequence[int], offset: int) -> int:
    return bisect.bisect_right(line_starts, offset)


def remove_one_argument_commands(text: str, commands: set[str]) -> str:
    """Remove complete one-argument commands, including nested argument text."""
    output: list[str] = []
    i = 0
    while i < len(text):
        parsed = read_command_name(text, i)
        if parsed and parsed[0] in commands:
            name, end = parsed
            pos = skip_space(text, end)
            if pos < len(text) and text[pos] == "{":
                try:
                    _, i = read_balanced(text, pos)
                    continue
                except ValueError:
                    pass
        output.append(text[i])
        i += 1
    return "".join(output)


def mask_command_arguments_preserve_layout(text: str, commands: set[str], start: int = 0) -> str:
    chars = list(text)
    i = start
    while i < len(text):
        parsed = read_command_name(text, i)
        if parsed and parsed[0] in commands:
            _, end = parsed
            pos = skip_space(text, end)
            if pos < len(text) and text[pos] == "{":
                try:
                    _, arg_end = read_balanced(text, pos)
                except ValueError:
                    i += 1
                    continue
                for index in range(i, arg_end):
                    if chars[index] not in "\r\n":
                        chars[index] = " "
                i = arg_end
                continue
        i += 1
    return "".join(chars)


# ---------------------------------------------------------------------------
# Plain-text labels and hierarchy
# ---------------------------------------------------------------------------

def replace_texorpdfstring(text: str) -> str:
    command = "\\texorpdfstring"
    while True:
        index = text.find(command)
        if index < 0:
            return text
        pos = skip_space(text, index + len(command))
        try:
            first, pos = read_balanced(text, pos)
            pos = skip_space(text, pos)
            second, end = read_balanced(text, pos)
        except ValueError:
            return text.replace(command, "")
        text = text[:index] + (second.strip() or first.strip()) + text[end:]


def latex_to_plain(value: str | None) -> str:
    if not value:
        return ""
    text = replace_texorpdfstring(value)
    text = remove_one_argument_commands(text, AUTHOR_ANNOTATION_COMMANDS)
    text = re.sub(r"\\(?:auto|cgpt|cjr|cpd|cls)\b", "", text)
    replacements = {
        r"\\Lambda_1": "Λ₁", r"\\Lambda": "Λ", r"\\Theta": "Θ", r"\\Phi": "Φ",
        r"\\Psi": "Ψ", r"\\phi": "φ", r"\\theta": "θ", r"\\gamma": "γ",
        r"\\alpha": "α", r"\\R": "ℝ", r"\\N": "ℕ", r"\\Z": "ℤ",
        r"\\C": "ℂ", r"\\ell": "ℓ", r"\\infty": "∞", r"\\leq": "≤",
        r"\\geq": "≥", r"\\to": "→",
    }
    for pattern, replacement in replacements.items():
        text = re.sub(pattern + r"(?![A-Za-z])", replacement, text)
    formatting = (
        "text", "textrm", "textit", "textbf", "texttt", "mathrm", "mathbf",
        "mathcal", "mathfrak", "mathscr", "operatorname", "emph",
    )
    pattern = re.compile(r"\\(?:" + "|".join(formatting) + r")\s*\{([^{}]*)\}")
    for _ in range(12):
        new = pattern.sub(r"\1", text)
        if new == text:
            break
        text = new
    text = text.replace("~", " ").replace("$", "")
    text = re.sub(r"\\[a-zA-Z@]+\*?", "", text)
    text = text.replace("\\", "").replace("{", "").replace("}", "")
    return re.sub(r"\s+", " ", text).strip(" .;:")


def slugify(value: str) -> str:
    slug = re.sub(r"[^a-z0-9]+", "-", latex_to_plain(value).lower()).strip("-")
    return slug or "untitled"


def find_immediate_label(text: str, start: int, limit: int = 500) -> str | None:
    end = min(len(text), start + limit)
    fragment = text[start:end]
    stops = [m.start() for m in re.finditer(r"\n\s*\n|\\begin\s*\{|\\(?:sub)*section\b", fragment)]
    if stops:
        fragment = fragment[: min(stops)]
    match = re.search(r"\\label\s*\{", fragment)
    if not match:
        return None
    try:
        label, _ = read_balanced(text, start + match.end() - 1)
    except ValueError:
        return None
    return label.strip() or None


def parse_headings(text: str, body_start: int, line_starts: Sequence[int]) -> tuple[list[Heading], list[str]]:
    command_re = re.compile(r"\\(section|subsection|subsubsection)(\*)?")
    raw: list[tuple[int, str, int, bool, str, str | None, int]] = []
    diagnostics: list[str] = []
    ordinal = 0
    for match in command_re.finditer(text, body_start):
        command = match.group(1)
        starred = bool(match.group(2))
        pos = skip_space(text, match.end())
        if pos < len(text) and text[pos] == "[":
            try:
                _, pos = read_balanced(text, pos, "[", "]")
            except ValueError as exc:
                diagnostics.append(str(exc))
                continue
            pos = skip_space(text, pos)
        if pos >= len(text) or text[pos] != "{":
            continue
        try:
            title_tex, title_end = read_balanced(text, pos)
        except ValueError as exc:
            diagnostics.append(str(exc))
            continue
        ordinal += 1
        raw.append((match.start(), command, HEADING_LEVELS[command], starred, title_tex, find_immediate_label(text, title_end), ordinal))

    front = Heading(
        id="section:frontmatter", kind="section", level=1, title_tex="Front matter",
        title="Front matter", label=None, synthetic=True, starred=True, ordinal=0,
        start=body_start, line=line_number(line_starts, body_start),
    )
    headings: list[Heading] = [front]
    used_ids = {front.id}
    stack: list[Heading] = []
    counters = [0, 0, 0, 0]
    first_real_section_seen = False
    for start, kind, level, starred, title_tex, label, ordinal in raw:
        base_id = f"section:{label}" if label else f"section:auto:{ordinal}:{slugify(title_tex)}"
        heading_id = base_id
        suffix = 2
        while heading_id in used_ids:
            heading_id = f"{base_id}:{suffix}"
            suffix += 1
        used_ids.add(heading_id)
        if starred:
            number = None
        else:
            counters[level] += 1
            for deeper in range(level + 1, len(counters)):
                counters[deeper] = 0
            number = ".".join(str(counters[i]) for i in range(1, level + 1))
        role = None
        if level == 1 and not first_real_section_seen:
            role = "introduction"
            first_real_section_seen = True
        heading = Heading(
            id=heading_id, kind=kind, level=level, title_tex=title_tex.strip(),
            title=latex_to_plain(title_tex) or f"Untitled {kind}", label=label,
            synthetic=False, starred=starred, ordinal=ordinal, start=start,
            line=line_number(line_starts, start), number=number, role=role,
        )
        while stack and stack[-1].level >= level:
            stack.pop()
        if level == 1:
            heading.parent_id = None
        elif stack:
            heading.parent_id = stack[-1].id
            stack[-1].children.append(heading.id)
        else:
            heading.parent_id = front.id
            front.children.append(heading.id)
        headings.append(heading)
        stack.append(heading)
    return headings, diagnostics


def heading_tree(headings: Sequence[Heading]) -> list[dict[str, Any]]:
    by_id = {heading.id: heading for heading in headings}

    def serialize(heading: Heading) -> dict[str, Any]:
        display_title = f"{heading.number}. {heading.title}" if heading.number else heading.title
        return {
            "id": heading.id,
            "kind": heading.kind,
            "level": heading.level,
            "title_tex": heading.title_tex,
            "title": heading.title,
            "display_title": display_title,
            "number": heading.number,
            "label": heading.label,
            "synthetic": heading.synthetic,
            "starred": heading.starred,
            "role": heading.role,
            "ordinal": heading.ordinal,
            "source_line": heading.line,
            "children": [serialize(by_id[child]) for child in heading.children],
        }

    return [serialize(heading) for heading in headings if heading.parent_id is None]


def heading_ancestry(heading_id: str, by_id: dict[str, Heading]) -> list[Heading]:
    chain: list[Heading] = []
    current = by_id[heading_id]
    while True:
        chain.append(current)
        if current.parent_id is None:
            break
        current = by_id[current.parent_id]
    chain.reverse()
    return chain


def active_heading_for_offset(offset: int, headings: Sequence[Heading], heading_starts: Sequence[int]) -> Heading:
    index = bisect.bisect_right(heading_starts, offset) - 1
    return headings[max(index, 0)]


# ---------------------------------------------------------------------------
# Environments and dependencies
# ---------------------------------------------------------------------------

def find_first_label(text: str, start: int, end: int) -> str | None:
    match = re.search(r"\\label\s*\{", text[start:end])
    if not match:
        return None
    try:
        value, _ = read_balanced(text, start + match.end() - 1)
    except ValueError:
        return None
    return value.strip() or None


def make_metadata_diagnostic(
    *,
    code: str,
    message: str,
    source_line: int,
    node: str | None,
    command: str,
    involved_nodes: Sequence[str] = (),
    value: str | None = None,
) -> dict[str, Any]:
    """Create a stable, machine-readable metadata diagnostic."""

    nodes = [item for item in dict.fromkeys(([node] if node else []) + list(involved_nodes)) if item]
    diagnostic: dict[str, Any] = {
        "category": "metadata",
        "severity": "warning",
        "code": code,
        "message": message,
        "source_line": source_line,
        "node": node,
        "involved_nodes": nodes,
        "command": f"\\{command}",
    }
    if value is not None:
        diagnostic["value"] = value
    return diagnostic


def parse_environment_metadata(
    text: str,
    start: int,
    end: int,
    line_starts: Sequence[int],
    node_label: str | None,
) -> tuple[list[MetadataCommand], list[dict[str, Any]]]:
    """Parse graph metadata commands inside one node environment.

    Commands with missing or unterminated arguments are omitted and diagnosed.
    Empty comma-list entries are omitted individually while valid neighboring
    entries are retained.
    """

    commands: list[MetadataCommand] = []
    diagnostics: list[dict[str, Any]] = []
    i = start
    while i < end:
        parsed = read_command_name(text, i)
        if not parsed:
            i += 1
            continue
        name, command_end = parsed

        # Metadata-looking text inside verbatim constructs is literal text, not
        # an annotation.  Skip it before interpreting any command names.
        if name == "verb":
            delimiter_pos = command_end
            if delimiter_pos < end and text[delimiter_pos] == "*":
                delimiter_pos += 1
            if delimiter_pos >= end:
                i = command_end
                continue
            delimiter = text[delimiter_pos]
            closing = text.find(delimiter, delimiter_pos + 1, end)
            i = end if closing < 0 else closing + 1
            continue

        if name == "begin":
            group = parse_command_group(text, command_end)
            if group is not None:
                environment_name, group_end = group
                environment_name = environment_name.strip()
                if environment_name in VERBATIM_ENVIRONMENTS:
                    end_pattern = re.compile(
                        r"\\end\s*\{" + re.escape(environment_name) + r"\}"
                    )
                    end_match = end_pattern.search(text, group_end, end)
                    i = end if end_match is None else end_match.end()
                    continue

        if name in FLAG_METADATA_COMMANDS:
            commands.append(
                MetadataCommand(
                    name=name,
                    source_line=line_number(line_starts, i),
                    raw_argument=None,
                    values=(),
                )
            )
            i = command_end
            continue
        if name not in ARGUMENT_METADATA_COMMANDS:
            i = command_end
            continue

        source_line = line_number(line_starts, i)
        argument_start = skip_space(text, command_end)
        if argument_start >= end or text[argument_start] != "{":
            diagnostics.append(
                make_metadata_diagnostic(
                    code="missing_metadata_argument",
                    message=f"\\{name} has no braced argument; the command was ignored.",
                    source_line=source_line,
                    node=node_label,
                    command=name,
                )
            )
            i = command_end
            continue
        try:
            raw_argument, argument_end = read_balanced(text, argument_start)
        except ValueError:
            diagnostics.append(
                make_metadata_diagnostic(
                    code="unterminated_metadata_argument",
                    message=f"\\{name} has an unterminated argument; the command was ignored.",
                    source_line=source_line,
                    node=node_label,
                    command=name,
                )
            )
            i = command_end
            continue
        if argument_end > end:
            diagnostics.append(
                make_metadata_diagnostic(
                    code="metadata_argument_crosses_environment",
                    message=(
                        f"\\{name} closes outside the containing environment; "
                        "the command was ignored."
                    ),
                    source_line=source_line,
                    node=node_label,
                    command=name,
                )
            )
            i = command_end
            continue

        values, empty_item_count = split_top_level_commas_with_empty_count(raw_argument)
        commands.append(
            MetadataCommand(
                name=name,
                source_line=source_line,
                raw_argument=raw_argument,
                values=tuple(values),
                empty_item_count=empty_item_count,
            )
        )
        if empty_item_count:
            diagnostics.append(
                make_metadata_diagnostic(
                    code="empty_metadata_list_entry",
                    message=(
                        f"\\{name} contains {empty_item_count} empty comma-list "
                        f"entr{'y' if empty_item_count == 1 else 'ies'}; "
                        "the empty entries were ignored."
                    ),
                    source_line=source_line,
                    node=node_label,
                    command=name,
                    value=raw_argument,
                )
            )
        i = argument_end
    return commands, diagnostics


def parse_environment_title(text: str, begin_end: int) -> tuple[str | None, int]:
    pos = skip_space(text, begin_end)
    if pos < len(text) and text[pos] == "[":
        try:
            title, end = read_balanced(text, pos, "[", "]")
            return title.strip() or None, end
        except ValueError:
            pass
    return None, pos


def parse_node_environments(text: str, body_start: int, line_starts: Sequence[int]) -> list[ParsedEnvironment]:
    begin_re = re.compile(r"\\begin\s*\{([^{}]+)\}")
    result: list[ParsedEnvironment] = []
    for match in begin_re.finditer(text, body_start):
        env = match.group(1).strip()
        if env not in NODE_ENVIRONMENTS:
            continue
        end_match = re.compile(r"\\end\s*\{" + re.escape(env) + r"\}").search(text, match.end())
        if not end_match:
            label = find_first_label(text, match.end(), len(text))
            metadata_commands, metadata_diagnostics = parse_environment_metadata(
                text,
                match.end(),
                len(text),
                line_starts,
                label,
            )
            result.append(
                ParsedEnvironment(
                    environment=env,
                    start=match.start(),
                    end=len(text),
                    content_start=match.end(),
                    content_end=len(text),
                    title_tex=None,
                    label=label,
                    metadata_commands=metadata_commands,
                    metadata_parse_diagnostics=metadata_diagnostics,
                    line_start=line_number(line_starts, match.start()),
                    line_end=line_number(line_starts, len(text) - 1),
                )
            )
            continue
        title_tex, content_start = parse_environment_title(text, match.end())
        label = find_first_label(text, content_start, end_match.start())
        metadata_commands, metadata_diagnostics = parse_environment_metadata(
            text,
            content_start,
            end_match.start(),
            line_starts,
            label,
        )
        result.append(
            ParsedEnvironment(
                environment=env,
                start=match.start(),
                end=end_match.end(),
                content_start=content_start,
                content_end=end_match.start(),
                title_tex=title_tex,
                label=label,
                metadata_commands=metadata_commands,
                metadata_parse_diagnostics=metadata_diagnostics,
                line_start=line_number(line_starts, match.start()),
                line_end=line_number(line_starts, end_match.end()),
            )
        )
    return result


# ---------------------------------------------------------------------------
# Macro definitions and expansion
# ---------------------------------------------------------------------------

def parse_macro_definitions(text: str, line_starts: Sequence[int]) -> dict[str, MacroDefinition]:
    macros: dict[str, MacroDefinition] = {}
    command_re = re.compile(r"\\(newcommand|renewcommand|providecommand|DeclareMathOperator\*?|def)\b")
    for match in command_re.finditer(text):
        declaration = match.group(1)
        pos = skip_space(text, match.end())
        name = ""
        arg_count = 0
        optional_default: str | None = None
        body = ""
        try:
            if declaration == "def":
                parsed = read_command_name(text, pos)
                if not parsed or not parsed[0]:
                    continue
                name, pos = parsed
                body_open = text.find("{", pos)
                if body_open < 0:
                    continue
                parameter_spec = text[pos:body_open]
                numbers = [int(item) for item in re.findall(r"#([1-9])", parameter_spec)]
                arg_count = max(numbers, default=0)
                body, _ = read_balanced(text, body_open)
            else:
                if pos < len(text) and text[pos] == "{":
                    raw_name, pos = read_balanced(text, pos)
                    parsed = read_command_name(raw_name.strip(), 0)
                    if not parsed:
                        continue
                    name = parsed[0]
                else:
                    parsed = read_command_name(text, pos)
                    if not parsed:
                        continue
                    name, pos = parsed
                pos = skip_space(text, pos)
                if declaration.startswith("DeclareMathOperator"):
                    if pos >= len(text) or text[pos] != "{":
                        continue
                    operator_body, _ = read_balanced(text, pos)
                    star = "*" if declaration.endswith("*") else ""
                    body = f"\\operatorname{star}{{{operator_body}}}"
                else:
                    if pos < len(text) and text[pos] == "[":
                        raw_count, pos = read_balanced(text, pos, "[", "]")
                        arg_count = int(raw_count.strip() or "0")
                        pos = skip_space(text, pos)
                        if arg_count and pos < len(text) and text[pos] == "[":
                            optional_default, pos = read_balanced(text, pos, "[", "]")
                            pos = skip_space(text, pos)
                    if pos >= len(text) or text[pos] != "{":
                        continue
                    body, _ = read_balanced(text, pos)
        except (ValueError, TypeError):
            continue
        if name:
            macros[name] = MacroDefinition(
                name=name,
                argument_count=arg_count,
                body=body,
                optional_default=optional_default,
                source_line=line_number(line_starts, match.start()),
                declaration=declaration,
            )
    return macros


def read_macro_argument(text: str, pos: int) -> tuple[str, int] | None:
    pos = skip_space(text, pos)
    if pos >= len(text):
        return None
    if text[pos] == "{":
        return read_balanced(text, pos)
    parsed = read_command_name(text, pos)
    if parsed:
        return text[pos : parsed[1]], parsed[1]
    return text[pos], pos + 1


def expand_custom_macros(text: str, macros: dict[str, MacroDefinition], max_passes: int = 40) -> tuple[str, list[str], list[str]]:
    used: set[str] = set()
    current = text
    for _ in range(max_passes):
        output: list[str] = []
        changed = False
        i = 0
        while i < len(current):
            parsed = read_command_name(current, i)
            if not parsed or parsed[0] not in macros:
                output.append(current[i])
                i += 1
                continue
            name, pos = parsed
            macro = macros[name]
            arguments: list[str] = []
            valid = True
            if macro.optional_default is not None:
                option_pos = skip_space(current, pos)
                if option_pos < len(current) and current[option_pos] == "[":
                    try:
                        option, pos = read_balanced(current, option_pos, "[", "]")
                    except ValueError:
                        valid = False
                    else:
                        arguments.append(option)
                else:
                    arguments.append(macro.optional_default)
            required = macro.argument_count - len(arguments)
            for _argument_index in range(required):
                if not valid:
                    break
                try:
                    argument = read_macro_argument(current, pos)
                except ValueError:
                    argument = None
                if argument is None:
                    valid = False
                    break
                value, pos = argument
                arguments.append(value)
            if not valid:
                output.append(current[i])
                i += 1
                continue
            replacement = macro.body
            for index, value in enumerate(arguments, start=1):
                replacement = replacement.replace(f"#{index}", value)
            output.append(replacement)
            used.add(name)
            i = pos
            changed = True
        current = "".join(output)
        if not changed:
            break
    remaining = sorted({name for name in macros if re.search(r"\\" + re.escape(name) + r"(?![A-Za-z@])", current)})
    return current, sorted(used), remaining


# ---------------------------------------------------------------------------
# LaTeX reference numbers
# ---------------------------------------------------------------------------

def parse_aux_labels(aux_text: str) -> dict[str, dict[str, str]]:
    catalog: dict[str, dict[str, str]] = {}
    i = 0
    marker = "\\newlabel"
    while True:
        index = aux_text.find(marker, i)
        if index < 0:
            break
        pos = skip_space(aux_text, index + len(marker))
        try:
            label, pos = read_balanced(aux_text, pos)
            pos = skip_space(aux_text, pos)
            payload, pos = read_balanced(aux_text, pos)
        except ValueError:
            i = index + len(marker)
            continue
        fields: list[str] = []
        p = 0
        while len(fields) < 5:
            p = skip_space(payload, p)
            if p >= len(payload) or payload[p] != "{":
                break
            try:
                value, p = read_balanced(payload, p)
            except ValueError:
                break
            fields.append(value)
        fields.extend([""] * (5 - len(fields)))
        number_raw, page_raw, title_raw, anchor_raw, extra_raw = fields[:5]
        catalog[label] = {
            "number": latex_to_plain(number_raw) or number_raw.strip(),
            "number_latex": number_raw.strip(),
            "page": latex_to_plain(page_raw) or page_raw.strip(),
            "title": latex_to_plain(title_raw),
            "anchor": anchor_raw.strip(),
            "extra": extra_raw.strip(),
        }
        i = pos
    return catalog


def compile_or_read_aux(latex_path: Path, aux_file: Path | None, latexmk_binary: str) -> tuple[dict[str, dict[str, str]], dict[str, Any]]:
    if aux_file is not None:
        if not aux_file.is_file():
            raise FileNotFoundError(f"auxiliary file not found: {aux_file}")
        text = aux_file.read_text(encoding="utf-8", errors="replace")
        catalog = parse_aux_labels(text)
        return catalog, {"mode": "supplied_aux", "succeeded": True, "aux_file": aux_file.name, "labels_total": len(catalog), "log_tail": ""}

    executable = shutil.which(latexmk_binary)
    if executable is None:
        return {}, {"mode": "compile", "succeeded": False, "aux_file": None, "labels_total": 0, "log_tail": f"{latexmk_binary!r} was not found"}
    with tempfile.TemporaryDirectory(prefix="nct-graph-latex-") as temporary:
        outdir = Path(temporary)
        command = [
            executable,
            "-pdf",
            "-interaction=nonstopmode",
            "-halt-on-error",
            f"-outdir={outdir}",
            str(latex_path.resolve()),
        ]
        process = subprocess.run(command, cwd=latex_path.parent, text=True, encoding="utf-8", errors="replace", capture_output=True, check=False)
        aux_path = outdir / f"{latex_path.stem}.aux"
        if not aux_path.is_file():
            # latexmk may normalize a path-like job name to the final basename.
            candidates = sorted(outdir.glob("*.aux"))
            aux_path = candidates[0] if candidates else aux_path
        succeeded = process.returncode == 0 and aux_path.is_file()
        log = (process.stdout + "\n" + process.stderr).strip().splitlines()
        catalog = parse_aux_labels(aux_path.read_text(encoding="utf-8", errors="replace")) if aux_path.is_file() else {}
        metadata: dict[str, Any] = {
            "mode": "compile",
            "engine": Path(executable).name,
            "succeeded": succeeded,
            "aux_file": aux_path.name if aux_path.is_file() else None,
            "labels_total": len(catalog),
            "return_code": process.returncode,
        }
        # Keep successful output deterministic: temporary directory paths from
        # latexmk are useful only when compilation fails.
        if not succeeded:
            metadata["log_tail"] = "\n".join(log[-40:])
        return catalog, metadata


# ---------------------------------------------------------------------------
# Statement conversion
# ---------------------------------------------------------------------------

TEXT_FORMAT_COMMANDS = {
    "emph": "em", "textit": "em", "textbf": "strong", "texttt": "code",
    "textrm": "span", "text": "span", "mbox": "span", "mathrm": "span",
}
DISPLAY_ENVIRONMENTS = {"equation", "equation*", "align", "align*", "gather", "gather*", "multline", "multline*", "displaymath"}
LIST_ENVIRONMENTS = {"itemize": "ul", "enumerate": "ol"}


class StatementConverter:
    def __init__(self, reference_catalog: dict[str, dict[str, Any]], node_ids: set[str]):
        self.reference_catalog = reference_catalog
        self.node_ids = node_ids
        self.references: list[dict[str, Any]] = []
        self.missing_numbers: list[str] = []

    def reference(self, command: str, label: str, math_mode: bool) -> str:
        info = self.reference_catalog.get(label)
        number = (info or {}).get("number") or "??"
        if number == "??":
            self.missing_numbers.append(label)
        display = f"({number})" if command == "eqref" else number
        target = label if label in self.node_ids else None
        self.references.append({
            "command": command,
            "label": label,
            "number": number,
            "display": display,
            "target_node_id": target,
        })
        if target:
            destination = "nct-node:" + urllib.parse.quote(target, safe="")
            if math_mode:
                safe_display = display.replace("\\", "").replace("{", "").replace("}", "")
                return f"\\href{{{destination}}}{{{safe_display}}}"
            return f'<a class="statement-ref" href="{html.escape(destination, quote=True)}" data-node-id="{html.escape(target, quote=True)}">{html.escape(display)}</a>'
        return html.escape(display) if not math_mode else display

    def replace_math_commands(self, text: str) -> str:
        output: list[str] = []
        i = 0
        while i < len(text):
            parsed = read_command_name(text, i)
            if not parsed:
                output.append(text[i])
                i += 1
                continue
            name, end = parsed
            if name in {"ref", "eqref"}:
                pos = skip_space(text, end)
                if pos < len(text) and text[pos] == "{":
                    try:
                        label, i = read_balanced(text, pos)
                    except ValueError:
                        output.append(text[i]); i += 1
                    else:
                        output.append(self.reference(name, label.strip(), True))
                    continue
            if name == "hyperref":
                pos = skip_space(text, end)
                if pos < len(text) and text[pos] == "[":
                    try:
                        label, pos = read_balanced(text, pos, "[", "]")
                        pos = skip_space(text, pos)
                        body, i = read_balanced(text, pos)
                    except ValueError:
                        output.append(text[i]); i += 1
                    else:
                        body = self.replace_math_commands(body)
                        if label.strip() in self.node_ids:
                            destination = "nct-node:" + urllib.parse.quote(label.strip(), safe="")
                            output.append(f"\\href{{{destination}}}{{{body}}}")
                        else:
                            output.append(body)
                    continue
            if name in REMOVED_METADATA_COMMANDS:
                pos = skip_space(text, end)
                if pos < len(text) and text[pos] == "{":
                    try:
                        _, i = read_balanced(text, pos)
                    except ValueError:
                        output.append(text[i]); i += 1
                    continue
            output.append(text[i:end])
            i = end
        result = "".join(output)
        # Presentation equivalents for source-only or unsupported commands.
        result = re.sub(r"\{*\(\{*\\tiny\s*\\faCar\s*\}\*\)\}*", r"\\text{(automated)}", result)
        result = re.sub(r"\\(?:tiny|scriptsize|footnotesize|small|normalsize)\b", "", result)
        result = re.sub(r"\\faCar\b", r"\\text{automated}", result)
        result = re.sub(r"\\widecheck\b", r"\\widehat", result)
        result = re.sub(r"\\textcolor\s*\{[^{}]*\}\s*\{([^{}]*)\}", r"\1", result)
        result = re.sub(r"\\color\s*\{[^{}]*\}", "", result)
        return result.strip()

    def text_fragment(self, text: str) -> str:
        output: list[str] = []
        i = 0
        pending_space = False
        while i < len(text):
            char = text[i]
            if char.isspace():
                run_start = i
                while i < len(text) and text[i].isspace():
                    i += 1
                run = text[run_start:i]
                if run.count("\n") >= 2:
                    output.append("<br><br>")
                    pending_space = False
                else:
                    pending_space = True
                continue
            if pending_space:
                output.append(" ")
                pending_space = False
            if char == "~":
                output.append("&nbsp;")
                i += 1
                continue
            if char == "{":
                try:
                    body, i = read_balanced(text, i)
                except ValueError:
                    output.append("{"); i += 1
                else:
                    output.append(self.text_fragment(body))
                continue
            parsed = read_command_name(text, i)
            if not parsed:
                output.append(html.escape(char))
                i += 1
                continue
            name, end = parsed
            if name in {"ref", "eqref"}:
                pos = skip_space(text, end)
                if pos < len(text) and text[pos] == "{":
                    try:
                        label, i = read_balanced(text, pos)
                    except ValueError:
                        output.append(html.escape(text[i:end])); i = end
                    else:
                        output.append(self.reference(name, label.strip(), False))
                    continue
            if name == "hyperref":
                pos = skip_space(text, end)
                if pos < len(text) and text[pos] == "[":
                    try:
                        label, pos = read_balanced(text, pos, "[", "]")
                        pos = skip_space(text, pos)
                        body, i = read_balanced(text, pos)
                    except ValueError:
                        output.append(html.escape(text[i:end])); i = end
                    else:
                        body_html = self.text_fragment(body)
                        if label.strip() in self.node_ids:
                            destination = "nct-node:" + urllib.parse.quote(label.strip(), safe="")
                            output.append(f'<a class="statement-ref" href="{html.escape(destination, quote=True)}" data-node-id="{html.escape(label.strip(), quote=True)}">{body_html}</a>')
                        else:
                            output.append(body_html)
                    continue
            if name in REMOVED_METADATA_COMMANDS:
                pos = skip_space(text, end)
                if pos < len(text) and text[pos] == "{":
                    try:
                        _, i = read_balanced(text, pos)
                    except ValueError:
                        i = end
                    continue
            if name in TEXT_FORMAT_COMMANDS:
                pos = skip_space(text, end)
                if pos < len(text) and text[pos] == "{":
                    try:
                        body, i = read_balanced(text, pos)
                    except ValueError:
                        output.append(html.escape(text[i:end])); i = end
                    else:
                        tag = TEXT_FORMAT_COMMANDS[name]
                        output.append(f"<{tag}>{self.text_fragment(body)}</{tag}>")
                    continue
            if name in {"cite", "citep", "citet"}:
                pos = skip_space(text, end)
                optional = ""
                if pos < len(text) and text[pos] == "[":
                    try:
                        optional, pos = read_balanced(text, pos, "[", "]")
                    except ValueError:
                        optional = ""
                pos = skip_space(text, pos)
                if pos < len(text) and text[pos] == "{":
                    try:
                        keys, i = read_balanced(text, pos)
                    except ValueError:
                        output.append("[citation]"); i = end
                    else:
                        label = keys if not optional else f"{optional}; {keys}"
                        output.append(f"[{html.escape(label)}]")
                    continue
            if name == "href":
                pos = skip_space(text, end)
                try:
                    url, pos = read_balanced(text, pos)
                    pos = skip_space(text, pos)
                    body, i = read_balanced(text, pos)
                except ValueError:
                    output.append(html.escape(text[i:end])); i = end
                else:
                    output.append(f'<a href="{html.escape(url, quote=True)}" target="_blank" rel="noreferrer">{self.text_fragment(body)}</a>')
                continue
            if name == "url":
                pos = skip_space(text, end)
                try:
                    url, i = read_balanced(text, pos)
                except ValueError:
                    output.append(html.escape(text[i:end])); i = end
                else:
                    output.append(f'<a href="{html.escape(url, quote=True)}" target="_blank" rel="noreferrer">{html.escape(url)}</a>')
                continue
            if name == "footnote":
                pos = skip_space(text, end)
                try:
                    body, i = read_balanced(text, pos)
                except ValueError:
                    i = end
                else:
                    output.append(f'<span class="statement-footnote">({self.text_fragment(body)})</span>')
                continue
            symbol_map = {
                "S": "§", "ldots": "…", "dots": "…", "LaTeX": "LaTeX", "TeX": "TeX",
                "%": "%", "&": "&amp;", "_": "_", "#": "#", "$": "$", "{": "{", "}": "}",
                "\\": "<br>", "newline": "<br>", "par": "<br><br>", "noindent": "",
                "smallskip": "<br>", "medskip": "<br>", "bigskip": "<br>", ",": " ", ";": " ", ":": " ",
                "quad": " ", "qquad": " ", "enspace": " ", "!": "", " ": " ",
            }
            if name in symbol_map:
                output.append(symbol_map[name])
                i = end
                continue
            if name in {"rm", "it", "bf", "em", "normalfont", "tiny", "scriptsize", "small", "large", "Large"}:
                i = end
                continue
            # Preserve an unknown standard text command visibly instead of silently deleting it.
            output.append(html.escape(text[i:end]))
            i = end
        if pending_space:
            output.append(" ")
        return "".join(output)

    @staticmethod
    def find_environment_end(text: str, pos: int, environment: str) -> tuple[str, int] | None:
        begin_token = f"\\begin{{{environment}}}"
        end_token = f"\\end{{{environment}}}"
        depth = 1
        i = pos
        while i < len(text):
            next_begin = text.find(begin_token, i)
            next_end = text.find(end_token, i)
            if next_end < 0:
                return None
            if 0 <= next_begin < next_end:
                depth += 1
                i = next_begin + len(begin_token)
            else:
                depth -= 1
                if depth == 0:
                    return text[pos:next_end], next_end + len(end_token)
                i = next_end + len(end_token)
        return None

    @staticmethod
    def split_items(text: str) -> list[str]:
        items: list[str] = []
        positions: list[int] = []
        depth = 0
        i = 0
        while i < len(text):
            if text.startswith("\\begin{", i):
                depth += 1
            elif text.startswith("\\end{", i):
                depth = max(0, depth - 1)
            elif depth == 0 and text.startswith("\\item", i) and (i + 5 == len(text) or not text[i + 5].isalpha()):
                positions.append(i)
            i += 1
        if not positions:
            return [text]
        positions.append(len(text))
        for index in range(len(positions) - 1):
            start = positions[index] + len("\\item")
            start = skip_space(text, start)
            if start < len(text) and text[start] == "[":
                try:
                    _, start = read_balanced(text, start, "[", "]")
                except ValueError:
                    pass
            items.append(text[start : positions[index + 1]].strip())
        return items

    def document(self, text: str) -> str:
        output: list[str] = []
        text_buffer: list[str] = []

        def flush_text() -> None:
            if text_buffer:
                rendered = self.text_fragment("".join(text_buffer))
                if rendered:
                    output.append(rendered)
                text_buffer.clear()

        i = 0
        while i < len(text):
            # Display and list environments.
            begin_match = re.match(r"\\begin\s*\{([^{}]+)\}", text[i:])
            if begin_match:
                environment = begin_match.group(1).strip()
                begin_end = i + begin_match.end()
                if environment in DISPLAY_ENVIRONMENTS or environment in LIST_ENVIRONMENTS:
                    found = self.find_environment_end(text, begin_end, environment)
                    if found:
                        body, i = found
                        flush_text()
                        if environment in LIST_ENVIRONMENTS:
                            tag = LIST_ENVIRONMENTS[environment]
                            items = "".join(f"<li>{self.document(item)}</li>" for item in self.split_items(body))
                            output.append(f"<{tag} class=\"statement-list\">{items}</{tag}>")
                        else:
                            math_body = self.replace_math_commands(remove_one_argument_commands(body, REMOVED_METADATA_COMMANDS))
                            if environment.startswith("align") or environment.startswith("multline"):
                                math_body = f"\\begin{{aligned}}{math_body}\\end{{aligned}}"
                            elif environment.startswith("gather"):
                                math_body = f"\\begin{{gathered}}{math_body}\\end{{gathered}}"
                            output.append(f'<div class="statement-display">\\[{math_body}\\]</div>')
                        continue
            if text.startswith("\\[", i):
                end = text.find("\\]", i + 2)
                if end >= 0:
                    flush_text()
                    output.append(f'<div class="statement-display">\\[{self.replace_math_commands(text[i + 2:end])}\\]</div>')
                    i = end + 2
                    continue
            if text.startswith("\\(", i):
                end = text.find("\\)", i + 2)
                if end >= 0:
                    flush_text()
                    output.append(f"\\({self.replace_math_commands(text[i + 2:end])}\\)")
                    i = end + 2
                    continue
            if text.startswith("$$", i) and not is_escaped(text, i):
                end = text.find("$$", i + 2)
                if end >= 0:
                    flush_text()
                    output.append(f'<div class="statement-display">\\[{self.replace_math_commands(text[i + 2:end])}\\]</div>')
                    i = end + 2
                    continue
            if text[i] == "$" and not is_escaped(text, i):
                end = i + 1
                while end < len(text):
                    if text[end] == "$" and not is_escaped(text, end):
                        break
                    end += 1
                if end < len(text):
                    flush_text()
                    output.append(f"\\({self.replace_math_commands(text[i + 1:end])}\\)")
                    i = end + 1
                    continue
            text_buffer.append(text[i])
            i += 1
        flush_text()
        return "".join(output).strip()


def clean_statement_source(raw: str) -> str:
    cleaned = remove_one_argument_commands(raw, REMOVED_METADATA_COMMANDS)
    cleaned = re.sub(r"\\leanok(?![A-Za-z@])", "", cleaned)
    cleaned = re.sub(r"\\(?:cgpt|cjr|cpd|cls)\b", "", cleaned)
    cleaned = re.sub(r"^[ \t]+|[ \t]+$", "", cleaned, flags=re.MULTILINE)
    cleaned = re.sub(r"\n{3,}", "\n\n", cleaned)
    return cleaned.strip()


# ---------------------------------------------------------------------------
# Graph algorithms
# ---------------------------------------------------------------------------

def find_cycles(node_ids: Iterable[str], edges: Sequence[dict[str, Any]]) -> list[list[str]]:
    adjacency: dict[str, list[str]] = defaultdict(list)
    for edge in edges:
        adjacency[edge["source"]].append(edge["target"])
    color = {node_id: 0 for node_id in node_ids}
    stack: list[str] = []
    stack_pos: dict[str, int] = {}
    cycles: list[list[str]] = []
    seen: set[tuple[str, ...]] = set()

    def canonical(cycle: list[str]) -> tuple[str, ...]:
        body = cycle[:-1]
        rotations = [tuple(body[i:] + body[:i]) for i in range(len(body))]
        best = min(rotations)
        return best + (best[0],)

    def visit(node: str) -> None:
        color[node] = 1
        stack_pos[node] = len(stack)
        stack.append(node)
        for nxt in adjacency.get(node, []):
            if color.get(nxt, 0) == 0:
                visit(nxt)
            elif color.get(nxt) == 1:
                key = canonical(stack[stack_pos[nxt] :] + [nxt])
                if key not in seen:
                    seen.add(key)
                    cycles.append(list(key))
        stack.pop()
        stack_pos.pop(node, None)
        color[node] = 2

    for node_id in node_ids:
        if color[node_id] == 0:
            visit(node_id)
    return cycles


def topological_order(node_ids: Iterable[str], edges: Sequence[dict[str, Any]]) -> list[str]:
    ids = list(node_ids)
    indegree = {node_id: 0 for node_id in ids}
    adjacency: dict[str, list[str]] = defaultdict(list)
    for edge in edges:
        adjacency[edge["source"]].append(edge["target"])
        indegree[edge["target"]] += 1
    queue = deque(sorted(node for node, degree in indegree.items() if degree == 0))
    order: list[str] = []
    while queue:
        node = queue.popleft()
        order.append(node)
        for target in sorted(adjacency.get(node, [])):
            indegree[target] -= 1
            if indegree[target] == 0:
                queue.append(target)
    return order


# ---------------------------------------------------------------------------
# Graph construction
# ---------------------------------------------------------------------------


def node_kind_for_environment(environment: str) -> str:
    return "definition" if environment in DEFINITION_ENVIRONMENTS else "theorem"


def resolve_node_metadata(
    env: ParsedEnvironment,
    node_kind_by_label: dict[str, str],
    default_status: str,
) -> tuple[list[str], list[str], str, list[dict[str, Any]]]:
    """Validate and resolve all metadata attached to one node.

    The returned dependency list is ordered by first valid occurrence and contains
    no duplicates.  ``\\uses`` accepts theorem labels only, ``\\usesdefs`` accepts
    definition labels only, and legacy ``\\using`` remains untyped for backward
    compatibility.  Invalid individual entries are diagnosed and omitted without
    affecting the remaining metadata.
    """

    node_label = env.label
    if not node_label:
        return [], [], default_status, list(env.metadata_parse_diagnostics)

    node_kind = node_kind_for_environment(env.environment)
    diagnostics = list(env.metadata_parse_diagnostics)
    dependencies: list[str] = []
    dependency_first_occurrence: dict[str, MetadataCommand] = {}
    lean_names: list[str] = []
    lean_name_first_occurrence: dict[str, MetadataCommand] = {}
    leanok_commands: list[MetadataCommand] = []

    expected_dependency_kind = {
        "uses": "theorem",
        "usesdefs": "definition",
    }

    for command in env.metadata_commands:
        if command.name in {"using", "uses", "usesdefs"}:
            expected_kind = expected_dependency_kind.get(command.name)
            for dependency in command.values:
                if dependency == node_label:
                    diagnostics.append(
                        make_metadata_diagnostic(
                            code="self_dependency",
                            message=(
                                f"Node {node_label!r} lists itself in \\{command.name}; "
                                "the dependency was ignored."
                            ),
                            source_line=command.source_line,
                            node=node_label,
                            command=command.name,
                            involved_nodes=[dependency],
                            value=dependency,
                        )
                    )
                    continue

                actual_kind = node_kind_by_label.get(dependency)
                if actual_kind is None:
                    diagnostics.append(
                        make_metadata_diagnostic(
                            code="unknown_dependency_label",
                            message=(
                                f"\\{command.name} refers to unknown node label "
                                f"{dependency!r}; the dependency was ignored."
                            ),
                            source_line=command.source_line,
                            node=node_label,
                            command=command.name,
                            involved_nodes=[dependency],
                            value=dependency,
                        )
                    )
                    continue

                if expected_kind is not None and actual_kind != expected_kind:
                    diagnostics.append(
                        make_metadata_diagnostic(
                            code="dependency_kind_mismatch",
                            message=(
                                f"\\{command.name} requires a {expected_kind} label, but "
                                f"{dependency!r} is a {actual_kind}; the dependency was ignored."
                            ),
                            source_line=command.source_line,
                            node=node_label,
                            command=command.name,
                            involved_nodes=[dependency],
                            value=dependency,
                        )
                    )
                    continue

                previous = dependency_first_occurrence.get(dependency)
                if previous is not None:
                    diagnostics.append(
                        make_metadata_diagnostic(
                            code="duplicate_dependency_metadata",
                            message=(
                                f"Dependency {dependency!r} is repeated in \\{command.name}; "
                                f"the repeated entry was ignored (first occurrence: line "
                                f"{previous.source_line})."
                            ),
                            source_line=command.source_line,
                            node=node_label,
                            command=command.name,
                            involved_nodes=[dependency],
                            value=dependency,
                        )
                    )
                    continue

                dependency_first_occurrence[dependency] = command
                dependencies.append(dependency)
            continue

        if command.name == "lean":
            for lean_name in command.values:
                previous = lean_name_first_occurrence.get(lean_name)
                if previous is not None:
                    diagnostics.append(
                        make_metadata_diagnostic(
                            code="duplicate_lean_name",
                            message=(
                                f"Lean name {lean_name!r} is repeated; the repeated entry "
                                f"was ignored (first occurrence: line {previous.source_line})."
                            ),
                            source_line=command.source_line,
                            node=node_label,
                            command=command.name,
                            value=lean_name,
                        )
                    )
                    continue
                lean_name_first_occurrence[lean_name] = command
                lean_names.append(lean_name)
            continue

        if command.name == "leanok":
            leanok_commands.append(command)

    if len(leanok_commands) > 1:
        first_line = leanok_commands[0].source_line
        for duplicate in leanok_commands[1:]:
            diagnostics.append(
                make_metadata_diagnostic(
                    code="duplicate_leanok",
                    message=(
                        f"\\leanok is repeated; the repeated flag was ignored "
                        f"(first occurrence: line {first_line})."
                    ),
                    source_line=duplicate.source_line,
                    node=node_label,
                    command="leanok",
                )
            )

    leanok_requested = bool(leanok_commands)
    leanok_valid = leanok_requested and bool(lean_names)
    if leanok_requested and not lean_names:
        diagnostics.append(
            make_metadata_diagnostic(
                code="leanok_without_lean",
                message=(
                    "\\leanok requires a nonempty \\lean{...} annotation; "
                    "the \\leanok status was ignored."
                ),
                source_line=leanok_commands[0].source_line,
                node=node_label,
                command="leanok",
            )
        )

    if env.environment == "exttheorem":
        status = "external_dependency"
        if leanok_valid:
            diagnostics.append(
                make_metadata_diagnostic(
                    code="leanok_on_external_dependency",
                    message=(
                        "An exttheorem always has status 'external_dependency'; "
                        "the \\leanok status was ignored."
                    ),
                    source_line=leanok_commands[0].source_line,
                    node=node_label,
                    command="leanok",
                )
            )
    elif leanok_valid:
        status = "fully_proved"
    elif lean_names:
        status = "defined" if node_kind == "definition" else "stated"
    else:
        status = default_status

    return dependencies, lean_names, status, diagnostics

def build_graph(
    latex_path: Path,
    *,
    granularity: str,
    include_definitions: bool,
    default_status: str,
    aux_file: Path | None,
    latexmk_binary: str,
) -> dict[str, Any]:
    original = latex_path.read_text(encoding="utf-8")
    masked = strip_comments_preserve_layout(original)
    line_starts = make_line_starts(masked)
    document_match = re.search(r"\\begin\s*\{document\}", masked)
    body_start = document_match.end() if document_match else 0
    semantic_text = mask_command_arguments_preserve_layout(masked, AUTHOR_ANNOTATION_COMMANDS, body_start)

    reference_catalog, reference_build = compile_or_read_aux(latex_path, aux_file, latexmk_binary)
    macros = parse_macro_definitions(masked, line_starts)
    headings, heading_diagnostics = parse_headings(semantic_text, body_start, line_starts)
    # Prefer LaTeX's own numbering where a heading has a label.
    for heading in headings:
        if heading.label and heading.label in reference_catalog and reference_catalog[heading.label].get("number"):
            heading.number = reference_catalog[heading.label]["number"]
    heading_by_id = {heading.id: heading for heading in headings}
    heading_starts = [heading.start for heading in headings]
    environments = parse_node_environments(semantic_text, body_start, line_starts)

    duplicate_labels: list[dict[str, Any]] = []
    missing_node_labels: list[dict[str, Any]] = []
    environment_by_label: dict[str, ParsedEnvironment] = {}
    for env in environments:
        if not env.label:
            missing_node_labels.append({"environment": env.environment, "source_line": env.line_start})
        elif env.label in environment_by_label:
            duplicate_labels.append({
                "label": env.label,
                "first_source_line": environment_by_label[env.label].line_start,
                "duplicate_source_line": env.line_start,
            })
        else:
            environment_by_label[env.label] = env

    node_ids = set(environment_by_label)
    node_kind_by_label = {
        label: node_kind_for_environment(env.environment)
        for label, env in environment_by_label.items()
    }
    nodes: list[dict[str, Any]] = []
    node_by_id: dict[str, dict[str, Any]] = {}
    missing_reference_numbers: list[dict[str, Any]] = []
    statement_unexpanded_macros: list[dict[str, Any]] = []
    metadata_diagnostics: list[dict[str, Any]] = []

    for env in environments:
        if not env.label or env.label in node_by_id:
            continue
        active = active_heading_for_offset(env.start, headings, heading_starts)
        ancestry = heading_ancestry(active.id, heading_by_id)
        top_section = next((item for item in ancestry if item.level == 1), headings[0])
        subsection = next((item for item in reversed(ancestry) if item.level == 2), None)
        kind = node_kind_for_environment(env.environment)
        display_name = ENVIRONMENT_DISPLAY_NAMES.get(env.environment, env.environment.title())
        title_plain = latex_to_plain(env.title_tex)

        uses, lean_names, status, node_metadata_diagnostics = resolve_node_metadata(
            env,
            node_kind_by_label,
            default_status,
        )
        metadata_diagnostics.extend(node_metadata_diagnostics)

        raw_statement = original[env.content_start : env.content_end]
        cleaned_statement = clean_statement_source(raw_statement)
        expanded_statement, expanded_macro_names, remaining_macros = expand_custom_macros(cleaned_statement, macros)
        converter = StatementConverter(reference_catalog, node_ids)
        statement_html = converter.document(expanded_statement)
        if converter.missing_numbers:
            for label in dict.fromkeys(converter.missing_numbers):
                missing_reference_numbers.append({"node": env.label, "reference": label})
        if remaining_macros:
            statement_unexpanded_macros.append({"node": env.label, "macros": remaining_macros})

        reference_info = reference_catalog.get(env.label, {})
        node = {
            "id": env.label,
            "label": env.label,
            "number": reference_info.get("number") or None,
            "kind": kind,
            "environment": env.environment,
            "environment_name": display_name,
            "title_tex": env.title_tex,
            "title": title_plain or f"{display_name}: {env.label}",
            "status": status,
            "visibility": "private",
            "visibility_reason": "used only within its section",
            "lean_names": lean_names,
            "uses": uses,
            "used_by": [],
            "location_id": active.id,
            "section_id": top_section.id,
            "subsection_id": subsection.id if subsection else None,
            "section_path": [item.id for item in ancestry],
            "section_titles": [item.title for item in ancestry],
            "section_numbers": [item.number for item in ancestry],
            "statement_latex": expanded_statement,
            "statement_html": statement_html,
            "statement_references": converter.references,
            "statement_custom_macros_expanded": expanded_macro_names,
            "statement_unexpanded_custom_macros": remaining_macros,
            "source": {"line_start": env.line_start, "line_end": env.line_end},
        }
        nodes.append(node)
        node_by_id[env.label] = node

    # Add target information to the global reference catalog after node IDs are fixed.
    catalog_output: dict[str, dict[str, Any]] = {}
    for label, info in reference_catalog.items():
        catalog_output[label] = {**info, "node_id": label if label in node_by_id else None}

    unresolved_dependencies: list[dict[str, Any]] = [
        {
            "dependency": diagnostic.get("value"),
            "used_by": diagnostic.get("node"),
            "source_line": diagnostic.get("source_line"),
            "command": diagnostic.get("command"),
        }
        for diagnostic in metadata_diagnostics
        if diagnostic.get("code") == "unknown_dependency_label"
    ]
    edges: list[dict[str, Any]] = []
    reverse: dict[str, list[str]] = defaultdict(list)
    annotation_ordinal = 0
    for node in nodes:
        for local_ordinal, dependency in enumerate(node["uses"], start=1):
            annotation_ordinal += 1
            # Dependency metadata has already been validated conservatively.
            if dependency not in node_by_id:
                continue
            edges.append({
                "id": f"edge:{annotation_ordinal}",
                "source": dependency,
                "target": node["id"],
                "kind": "uses",
                "annotation_ordinal": local_ordinal,
            })
            reverse[dependency].append(node["id"])

    introduction_section_id = next((heading.id for heading in headings if heading.role == "introduction"), None)
    for node in nodes:
        node["used_by"] = list(dict.fromkeys(reverse.get(node["id"], [])))
        cross_section = any(node_by_id[user]["section_id"] != node["section_id"] for user in node["used_by"])
        if node["section_id"] == introduction_section_id:
            node["visibility"] = "public"
            node["visibility_reason"] = "the Introduction is public by convention"
        elif cross_section:
            node["visibility"] = "public"
            node["visibility_reason"] = "used outside its section"
        else:
            node["visibility"] = "private"
            node["visibility_reason"] = "used only within its section"

    cycles = find_cycles(node_by_id, edges)
    topo = topological_order(node_by_id, edges)
    is_dag = len(topo) == len(nodes)
    duplicate_edges = [
        {"source": source, "target": target, "count": count}
        for (source, target), count in Counter((edge["source"], edge["target"]) for edge in edges).items()
        if count > 1
    ]

    frontmatter_used = any(node["section_id"] == headings[0].id for node in nodes) or bool(headings[0].children)
    output_headings = headings if frontmatter_used else headings[1:]
    status_counts = Counter(node["status"] for node in nodes)
    visibility_counts = Counter(node["visibility"] for node in nodes)
    kind_counts = Counter(node["kind"] for node in nodes)
    rendered_nodes = [node for node in nodes if include_definitions or node["kind"] != "definition"]
    rendered_ids = {node["id"] for node in rendered_nodes}
    rendered_edges = [edge for edge in edges if edge["source"] in rendered_ids and edge["target"] in rendered_ids]

    return {
        "schema": SCHEMA_NAME,
        "schema_version": SCHEMA_VERSION,
        "source": {
            "latex_file": latex_path.name,
            "sha256": hashlib.sha256(original.encode("utf-8")).hexdigest(),
            "generated_at": datetime.now(timezone.utc).replace(microsecond=0).isoformat(),
            "parser": {"name": PARSER_NAME, "version": PARSER_VERSION},
            "reference_numbering": reference_build,
        },
        "settings": {
            "grouping_granularity": granularity,
            "include_definitions": include_definitions,
            "rank_direction": "BT",
            "public_opacity": 1.0,
            "private_opacity": 0.5,
            "section_opacity": 0.15,
            "subsection_opacity": 0.09,
            "show_sidebar": True,
            "show_legend": True,
            "show_document_hierarchy": True,
            "default_status": default_status,
        },
        "special_sections": {"introduction_section_id": introduction_section_id},
        "status_catalog": STATUS_CATALOG,
        "reference_catalog": catalog_output,
        "sections": heading_tree(output_headings),
        "nodes": nodes,
        "edges": edges,
        "diagnostics": {
            # Keep format-version 2.0 compatibility: the existing parse-message
            # array also carries structured metadata diagnostics.  They are
            # additionally printed to stderr by main().
            "heading_parse_messages": [*heading_diagnostics, *metadata_diagnostics],
            "duplicate_labels": duplicate_labels,
            "missing_node_labels": missing_node_labels,
            "unresolved_dependencies": unresolved_dependencies,
            "duplicate_edges": duplicate_edges,
            "cycles": cycles,
            "missing_reference_numbers": missing_reference_numbers,
            "statement_unexpanded_macros": statement_unexpanded_macros,
        },
        "statistics": {
            "nodes_total": len(nodes),
            "theorem_nodes": kind_counts["theorem"],
            "definition_nodes": kind_counts["definition"],
            "edges_total": len(edges),
            "using_annotations_total": sum(len(node["uses"]) for node in nodes),
            "rendered_nodes": len(rendered_nodes),
            "rendered_edges": len(rendered_edges),
            "public_nodes": visibility_counts["public"],
            "private_nodes": visibility_counts["private"],
            "sections": sum(1 for heading in output_headings if heading.level == 1),
            "subsections": sum(1 for heading in output_headings if heading.level == 2),
            "subsubsections": sum(1 for heading in output_headings if heading.level == 3),
            "reference_labels": len(catalog_output),
            "statement_references": sum(len(node["statement_references"]) for node in nodes),
            "status_counts": dict(sorted(status_counts.items())),
            "is_dag": is_dag,
            "topological_order": topo if is_dag else [],
        },
    }


def validate_graph_shape(graph: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if graph.get("schema") != SCHEMA_NAME:
        errors.append(f"schema must be {SCHEMA_NAME!r}")
    if graph.get("schema_version") != SCHEMA_VERSION:
        errors.append(f"schema_version must be {SCHEMA_VERSION!r}")
    node_ids = [node.get("id") for node in graph.get("nodes", [])]
    if len(node_ids) != len(set(node_ids)):
        errors.append("node IDs are not unique")
    for node in graph.get("nodes", []):
        if node.get("status") not in STATUS_IDS:
            errors.append(f"node {node.get('id')!r} has unknown status {node.get('status')!r}")
        if node.get("visibility") not in {"public", "private"}:
            errors.append(f"node {node.get('id')!r} has invalid visibility")
        if not isinstance(node.get("lean_names"), list):
            errors.append(f"node {node.get('id')!r} lean_names must be a list")
        for field in ("statement_latex", "statement_html", "statement_references"):
            if field not in node:
                errors.append(f"node {node.get('id')!r} is missing {field}")
    return errors


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("latex", type=Path, help="input LaTeX file")
    parser.add_argument("output", type=Path, help="output JSON file")
    parser.add_argument("--granularity", choices=("none", "section", "subsection"), default="subsection", help="default hierarchy view")
    parser.add_argument("--include-definitions", action=argparse.BooleanOptionalAction, default=False, help="default visibility of definition nodes")
    parser.add_argument("--status", choices=sorted(STATUS_IDS), default="can_state", help="initial status assigned to every extracted node")
    parser.add_argument("--aux-file", type=Path, help="use an existing .aux file instead of compiling the LaTeX source")
    parser.add_argument("--latexmk-binary", default="latexmk", help="latexmk executable used to obtain reference numbers")
    parser.add_argument("--strict", action="store_true", help="exit nonzero on structural, dependency, numbering, or macro-expansion diagnostics")
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    if not args.latex.is_file():
        print(f"error: LaTeX file not found: {args.latex}", file=sys.stderr)
        return 2
    try:
        graph = build_graph(
            args.latex,
            granularity=args.granularity,
            include_definitions=args.include_definitions,
            default_status=args.status,
            aux_file=args.aux_file,
            latexmk_binary=args.latexmk_binary,
        )
    except (OSError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    shape_errors = validate_graph_shape(graph)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(graph, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    diagnostics = graph["diagnostics"]
    metadata_diagnostics = [
        item
        for item in diagnostics["heading_parse_messages"]
        if isinstance(item, dict) and item.get("category") == "metadata"
    ]
    strict_failures = (
        shape_errors
        or diagnostics["duplicate_labels"]
        or diagnostics["missing_node_labels"]
        or diagnostics["unresolved_dependencies"]
        or diagnostics["cycles"]
        or diagnostics["missing_reference_numbers"]
        or diagnostics["statement_unexpanded_macros"]
        or metadata_diagnostics
        or not graph["source"]["reference_numbering"].get("succeeded")
    )
    stats = graph["statistics"]
    print(
        f"wrote {args.output}: {stats['nodes_total']} nodes, {stats['edges_total']} edges, "
        f"{stats['sections']} sections, {stats['statement_references']} statement references, DAG={stats['is_dag']}"
    )
    for error in shape_errors:
        print(f"validation error: {error}", file=sys.stderr)
    for diagnostic in metadata_diagnostics:
        line = diagnostic.get("source_line", "?")
        node = diagnostic.get("node")
        node_text = repr(node) if node else "<unlabeled node>"
        involved = diagnostic.get("involved_nodes") or []
        involved_text = ", ".join(repr(item) for item in involved)
        suffix = f"; involved nodes: {involved_text}" if involved_text else ""
        print(
            f"metadata warning: line {line}, node {node_text}: "
            f"{diagnostic.get('message', diagnostic.get('code', 'inconsistent metadata'))}{suffix}",
            file=sys.stderr,
        )
    if args.strict and strict_failures:
        print("strict validation failed; inspect diagnostics in the JSON output", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
