#!/usr/bin/env python3
r"""Validate and report formalization progress against the Lean blueprint.

The blueprint is treated as a dependency graph. ``\uses{...}`` declares edges,
and ``\leanok``/``\mathlibok`` mark completed nodes. The default report ranks
the dependency frontier toward Morley's theorem; named milestones can restrict
that view to one proof direction.

Examples::

    python3 scripts/blueprint_status.py
    python3 scripts/blueprint_status.py --milestone omega_stability --top 5
    python3 scripts/blueprint_status.py --milestones
    python3 scripts/blueprint_status.py --why thm:two-cardinal-transfer
    python3 scripts/blueprint_status.py --json
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

NODE_ENVIRONMENTS = ("definition", "theorem", "lemma", "proposition", "corollary")
FORMALIZED_MARKERS = ("\\leanok", "\\mathlibok")
DEFAULT_GOAL = "cor:morley-categoricity"
MILESTONES = {
    "omega_stability": "thm:uncountable-categoricity-implies-omega-stable",
    "no_vaughtian_pairs": "thm:uncountable-categoricity-no-vaughtian-pairs",
    "reverse_direction": "thm:omega-stable-no-vaughtian-pairs-implies-uncountably-categorical",
    "morley": DEFAULT_GOAL,
}

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_TEX = REPO_ROOT / "blueprint/src/content.tex"

_NODE_RE = re.compile(
    r"\\begin\{(" + "|".join(NODE_ENVIRONMENTS) + r")\}"
    r"(\[[^\]]*\])?(.*?)\\end\{\1\}",
    re.S,
)
_LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
_USES_RE = re.compile(r"\\uses\{([^}]*)\}")
_PROOF_RE = re.compile(
    r"\A(?:\s|%[^\n]*(?:\n|$))*\\begin\{proof\}(.*?)\\end\{proof\}", re.S
)


@dataclass
class Node:
    label: str
    kind: str
    title: str | None
    formalized: bool
    statement_uses: set[str] = field(default_factory=set)
    proof_uses: set[str] = field(default_factory=set)
    line: int = 0

    @property
    def uses(self) -> set[str]:
        return self.statement_uses | self.proof_uses


@dataclass(frozen=True)
class Diagnostic:
    code: str
    message: str
    label: str | None = None
    line: int | None = None


@dataclass
class Analysis:
    nodes: list[Node]
    formalized: set[str]
    frontier: list[Node]
    blocked_by_definitions: list[tuple[Node, set[str]]]
    blocked: list[tuple[Node, set[str]]]
    dangling: list[tuple[Node, set[str]]]

    @property
    def pending(self) -> list[Node]:
        return [node for node in self.nodes if not node.formalized]


@dataclass(frozen=True)
class Metrics:
    label: str
    kind: str
    on_goal_path: bool
    new_ready: int
    goal_reach: int
    distance: int | None
    unlocks: int


def _mask_comments(text: str) -> str:
    """Mask TeX comments without changing offsets or line numbers."""
    chars = list(text)
    escaped = False
    comment = False
    for i, char in enumerate(chars):
        if char == "\n":
            comment = False
            escaped = False
        elif comment:
            chars[i] = " "
        elif char == "%" and not escaped:
            comment = True
            chars[i] = " "
        elif char == "\\":
            escaped = not escaped
        else:
            escaped = False
    return "".join(chars)


def _labels(text: str) -> set[str]:
    found: set[str] = set()
    for group in _USES_RE.findall(text):
        found.update(part.strip() for part in group.split(",") if part.strip())
    return found


def validate_source(tex: str) -> list[Diagnostic]:
    """Return source-level errors that would otherwise disappear during parsing."""
    diagnostics: list[Diagnostic] = []
    masked = _mask_comments(tex)
    for match in _NODE_RE.finditer(masked):
        body = masked[match.start(3):match.end(3)]
        label_match = _LABEL_RE.search(body)
        if label_match is None or not label_match.group(1).strip():
            diagnostics.append(
                Diagnostic(
                    "missing-label",
                    f"{match.group(1)} has no non-empty \\label",
                    line=tex.count("\n", 0, match.start()) + 1,
                )
            )
    return diagnostics


def parse_blueprint(tex: str, include_proof_uses: bool = True) -> list[Node]:
    """Extract blueprint nodes from one TeX document in document order."""
    nodes: list[Node] = []
    masked = _mask_comments(tex)
    for match in _NODE_RE.finditer(masked):
        kind, raw_title = match.group(1), match.group(2)
        body = tex[match.start(3):match.end(3)]
        clean_body = _mask_comments(body)
        label_match = _LABEL_RE.search(clean_body)
        if label_match is None or not label_match.group(1).strip():
            continue
        proof_uses: set[str] = set()
        if include_proof_uses:
            proof_match = _PROOF_RE.match(masked[match.end():])
            if proof_match is not None:
                proof_uses = _labels(proof_match.group(1))
        nodes.append(
            Node(
                label=label_match.group(1).strip(),
                kind=kind,
                title=raw_title[1:-1].strip() if raw_title else None,
                formalized=any(marker in clean_body for marker in FORMALIZED_MARKERS),
                statement_uses=_labels(clean_body),
                proof_uses=proof_uses,
                line=tex.count("\n", 0, match.start()) + 1,
            )
        )
    return nodes


def _known(nodes: list[Node]) -> dict[str, Node]:
    result: dict[str, Node] = {}
    for node in nodes:
        result.setdefault(node.label, node)
    return result


def _dependencies(nodes: list[Node]) -> dict[str, set[str]]:
    known = _known(nodes)
    return {
        label: {dep for dep in node.uses if dep in known}
        for label, node in known.items()
    }


def _dependents(nodes: list[Node]) -> dict[str, set[str]]:
    dependencies = _dependencies(nodes)
    result = {label: set() for label in dependencies}
    for label, deps in dependencies.items():
        for dep in deps:
            result[dep].add(label)
    return result


def validate_graph(nodes: list[Node]) -> list[Diagnostic]:
    """Return duplicate-label, dangling-use, self-dependency, and cycle errors."""
    diagnostics: list[Diagnostic] = []
    occurrences: dict[str, list[Node]] = {}
    for node in nodes:
        occurrences.setdefault(node.label, []).append(node)
    for label, items in occurrences.items():
        if len(items) > 1:
            diagnostics.append(
                Diagnostic("duplicate-label", f"label appears {len(items)} times", label, items[0].line)
            )

    known = set(occurrences)
    for node in nodes:
        unknown = node.uses - known
        if unknown:
            diagnostics.append(
                Diagnostic(
                    "dangling-use",
                    "\\uses has no matching node: " + ", ".join(sorted(unknown)),
                    node.label,
                    node.line,
                )
            )
        if node.label in node.uses:
            diagnostics.append(
                Diagnostic("self-dependency", "node depends on itself", node.label, node.line)
            )

    graph = _dependencies(nodes)
    state = {label: 0 for label in graph}
    stack: list[str] = []
    reported: set[frozenset[str]] = set()
    known_nodes = _known(nodes)

    def visit(label: str) -> None:
        state[label] = 1
        stack.append(label)
        for dep in graph[label]:
            if state[dep] == 0:
                visit(dep)
            elif state[dep] == 1:
                start = stack.index(dep)
                cycle = stack[start:] + [dep]
                key = frozenset(cycle)
                if key not in reported:
                    reported.add(key)
                    diagnostics.append(
                        Diagnostic(
                            "dependency-cycle",
                            " -> ".join(cycle),
                            label,
                            known_nodes[label].line,
                        )
                    )
        stack.pop()
        state[label] = 2

    for label in graph:
        if state[label] == 0:
            visit(label)
    return diagnostics


def analyse(nodes: list[Node]) -> Analysis:
    """Classify pending nodes. Unknown dependencies are blockers, never frontier."""
    known = _known(nodes)
    formalized = {node.label for node in nodes if node.formalized}
    frontier: list[Node] = []
    definition_blocked: list[tuple[Node, set[str]]] = []
    blocked: list[tuple[Node, set[str]]] = []
    dangling: list[tuple[Node, set[str]]] = []

    for node in nodes:
        unknown = node.uses - known.keys()
        if unknown:
            dangling.append((node, unknown))
        if node.formalized:
            continue
        missing_known = {dep for dep in node.uses if dep in known and dep not in formalized}
        missing = missing_known | unknown
        if not missing:
            frontier.append(node)
        elif not unknown and all(known[dep].kind == "definition" for dep in missing_known):
            definition_blocked.append((node, missing_known))
        else:
            blocked.append((node, missing))
    return Analysis(nodes, formalized, frontier, definition_blocked, blocked, dangling)


def _reachable(label: str, adjacency: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    stack = list(adjacency.get(label, ()))
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        stack.extend(adjacency.get(current, ()))
    return seen


def _required(goal: str, dependencies: dict[str, set[str]]) -> set[str]:
    result = {goal}
    stack = [goal]
    while stack:
        current = stack.pop()
        for dep in dependencies.get(current, ()):
            if dep not in result:
                result.add(dep)
                stack.append(dep)
    return result


def _distance_to_goal(
    label: str,
    goal: str,
    dependents: dict[str, set[str]],
    formalized: set[str],
    memo: dict[str, int | None],
) -> int | None:
    if label in memo:
        return memo[label]
    if label == goal:
        memo[label] = 0
        return 0
    candidates: list[int] = []
    for child in dependents.get(label, ()):
        tail = _distance_to_goal(child, goal, dependents, formalized, memo)
        if tail is not None:
            candidates.append((0 if child in formalized else 1) + tail)
    memo[label] = min(candidates) if candidates else None
    return memo[label]


def compute_metrics(
    analysis: Analysis,
    goal: str | None = DEFAULT_GOAL,
) -> dict[str, Metrics]:
    known = _known(analysis.nodes)
    pending = analysis.pending
    pending_labels = {node.label for node in pending}
    frontier_labels = {node.label for node in analysis.frontier}
    dependents = _dependents(analysis.nodes)
    dependencies = _dependencies(analysis.nodes)
    required = _required(goal, dependencies) if goal in known else set()
    distance_memo: dict[str, int | None] = {}

    metrics: dict[str, Metrics] = {}
    for node in pending:
        reach = _reachable(node.label, dependents) & pending_labels
        done = analysis.formalized | {node.label}
        new_ready = sum(
            1
            for other in pending
            if other.label != node.label
            and other.label not in frontier_labels
            and not (other.uses - known.keys())
            and all(dep in done for dep in other.uses)
        )
        metrics[node.label] = Metrics(
            label=node.label,
            kind=node.kind,
            on_goal_path=node.label in required,
            new_ready=new_ready,
            goal_reach=len(reach & required),
            distance=(
                _distance_to_goal(
                    node.label, goal, dependents, analysis.formalized, distance_memo
                )
                if goal
                else None
            ),
            unlocks=sum(1 for other in pending if node.label in other.uses),
        )
    return metrics


def _none_high(value: int | None) -> int:
    return value if value is not None else 10**9


def priority_key(item: Metrics) -> tuple[object, ...]:
    """Order frontier nodes by goal relevance, immediate progress, then proximity."""
    return (
        -int(item.on_goal_path),
        -item.new_ready,
        -item.goal_reach,
        _none_high(item.distance),
        -item.unlocks,
        item.label,
    )


HEADERS = ("#", "node", "kind", "goal", "new", "g-reach", "dist", "unlks")


def _format_table(headers: tuple[str, ...], rows: list[tuple[str, ...]]) -> list[str]:
    widths = [len(header) for header in headers]
    for row in rows:
        for i, cell in enumerate(row):
            widths[i] = max(widths[i], len(cell))
    lines = ["  " + "  ".join(h.ljust(widths[i]) for i, h in enumerate(headers)).rstrip()]
    lines += ["  " + "  ".join(c.ljust(widths[i]) for i, c in enumerate(row)).rstrip() for row in rows]
    return lines


def _select_frontier_metrics(
    analysis: Analysis,
    metrics: dict[str, Metrics],
    top: int | None,
    restrict_to_goal: bool,
) -> tuple[list[Metrics], int]:
    items = [metrics[node.label] for node in analysis.frontier]
    if restrict_to_goal:
        items = [item for item in items if item.on_goal_path]
    candidate_count = len(items)
    items.sort(key=priority_key)
    if top is not None:
        items = items[:top]
    return items, candidate_count


def _priority_rows(items: list[Metrics]) -> list[tuple[str, ...]]:
    return [
        (
            str(i),
            item.label,
            item.kind,
            "yes" if item.on_goal_path else "-",
            str(item.new_ready),
            str(item.goal_reach),
            "-" if item.distance is None else str(item.distance),
            str(item.unlocks),
        )
        for i, item in enumerate(items, 1)
    ]


def milestone_rows(
    analysis: Analysis,
    milestones: dict[str, str] | None = None,
) -> list[tuple[str, ...]]:
    milestones = MILESTONES if milestones is None else milestones
    dependencies = _dependencies(analysis.nodes)
    frontier = {node.label for node in analysis.frontier}
    rows: list[tuple[str, ...]] = []
    for name, goal in milestones.items():
        required = _required(goal, dependencies)
        pending = required - analysis.formalized
        rows.append(
            (
                name,
                goal,
                str(len(required) - len(pending)),
                str(len(pending)),
                str(len(pending & frontier)),
            )
        )
    return rows


def format_milestones(
    analysis: Analysis,
    milestones: dict[str, str] | None = None,
) -> str:
    rows = milestone_rows(analysis, milestones)
    if not rows:
        return "No milestones configured."
    return "Milestones\n" + "\n".join(
        _format_table(("milestone", "goal", "done", "pending", "ready"), rows)
    )


def format_why(label: str, analysis: Analysis) -> str:
    known = _known(analysis.nodes)
    if label not in known:
        return f"unknown node: {label}"
    lines = [f"Why {label}?"]

    def walk(current: str, prefix: str, seen: set[str]) -> None:
        node = known[current]
        if current in analysis.formalized:
            lines.append(f"{prefix}{current}  [done]")
            return
        unknown = sorted(node.uses - known.keys())
        missing = sorted(dep for dep in node.uses if dep in known and dep not in analysis.formalized)
        if not unknown and not missing:
            lines.append(f"{prefix}{current}  [ready]")
            return
        lines.append(f"{prefix}{current}  [blocked]")
        if current in seen:
            lines.append(f"{prefix}  <cycle>")
            return
        for dep in unknown:
            lines.append(f"{prefix}  ? {dep}  [missing label]")
        for dep in missing:
            walk(dep, prefix + "  ", seen | {current})

    walk(label, "  ", set())
    return "\n".join(lines)


def format_text(
    analysis: Analysis,
    metrics: dict[str, Metrics],
    tex_path: Path,
    show_all: bool,
    goal: str | None,
    top: int | None,
    restrict_to_goal: bool,
    include_proof_uses: bool = True,
) -> str:
    lines = [
        f"Blueprint status for {tex_path}",
        f"  {len(analysis.nodes)} nodes: {len(analysis.formalized)} formalized, {len(analysis.pending)} pending",
        f"  {len(analysis.frontier)} pending nodes on the dependency frontier",
        (
            "  statement/proof dependencies are merged"
            if include_proof_uses
            else "  statement dependencies only"
        ),
        "",
    ]

    if show_all:
        known = _known(analysis.nodes)
        lines.append(f"Pending nodes in document order ({len(analysis.pending)}):")
        for node in analysis.pending:
            missing = sorted(dep for dep in node.uses if dep not in analysis.formalized)
            text = f"  {node.label:<62} [{node.kind}] line {node.line}"
            if missing:
                text += "  needs " + ", ".join(missing)
            if any(dep not in known for dep in missing):
                text += "  [invalid dependency]"
            lines.append(text)
        return "\n".join(lines)

    selected, candidate_count = _select_frontier_metrics(
        analysis, metrics, top, restrict_to_goal
    )
    lines.append(
        f"Goal-aware frontier ({candidate_count} candidates; goal={goal or 'none'})"
    )
    rows = _priority_rows(selected)
    lines += _format_table(HEADERS, rows) if rows else ["  (none)"]
    lines += [
        "  goal=yes: node lies on a path to the selected goal",
        "  new: blocked nodes becoming ready; g-reach: pending goal-path descendants",
        "  dist: shortest pending distance to goal; unlks: direct pending dependents",
        "",
        f"Blocked only by pending definitions ({len(analysis.blocked_by_definitions)}):",
    ]
    if analysis.blocked_by_definitions:
        lines += [
            f"  {node.label:<62} [{node.kind}] needs {', '.join(sorted(missing))}"
            for node, missing in analysis.blocked_by_definitions
        ]
    else:
        lines.append("  (none)")
    lines += ["", f"Blocked by pending results ({len(analysis.blocked)}); pass --all for details"]
    return "\n".join(lines)


def format_json(
    analysis: Analysis,
    metrics: dict[str, Metrics],
    tex_path: Path,
    goal: str | None,
    top: int | None = None,
    restrict_to_goal: bool = False,
) -> str:
    def node_entry(node: Node) -> dict[str, object]:
        return {
            "label": node.label,
            "kind": node.kind,
            "title": node.title,
            "line": node.line,
            "formalized": node.formalized,
            "missing": sorted(dep for dep in node.uses if dep not in analysis.formalized),
            "statement_uses": sorted(node.statement_uses),
            "proof_uses": sorted(node.proof_uses),
        }

    def metric_entry(item: Metrics) -> dict[str, object]:
        return {
            "label": item.label,
            "kind": item.kind,
            "on_goal_path": item.on_goal_path,
            "new_ready": item.new_ready,
            "goal_reach": item.goal_reach,
            "distance": item.distance,
            "unlocks": item.unlocks,
        }

    selected, candidate_count = _select_frontier_metrics(
        analysis, metrics, top, restrict_to_goal
    )
    frontier_by_label = {node.label: node for node in analysis.frontier}
    payload = {
        "tex": str(tex_path),
        "goal": goal,
        "milestones": MILESTONES,
        "selection": {
            "top": top,
            "restrict_to_goal": restrict_to_goal,
        },
        "counts": {
            "nodes": len(analysis.nodes),
            "formalized": len(analysis.formalized),
            "pending": len(analysis.pending),
            "frontier": len(selected),
            "frontier_candidates": candidate_count,
            "frontier_total": len(analysis.frontier),
        },
        "priority": [metric_entry(item) for item in selected],
        "frontier": [node_entry(frontier_by_label[item.label]) for item in selected],
        "pending": [node_entry(node) for node in analysis.pending],
        "metrics": {node.label: metric_entry(metrics[node.label]) for node in analysis.pending},
        "dangling_uses": [
            {"label": node.label, "missing": sorted(unknown)}
            for node, unknown in analysis.dangling
        ],
    }
    return json.dumps(payload, indent=2, ensure_ascii=False)


def _diagnostic(item: Diagnostic) -> str:
    location = f"line {item.line}: " if item.line else ""
    label = f"{item.label}: " if item.label else ""
    return f"{location}{item.code}: {label}{item.message}"


def _print_dangling_warnings(diagnostics: list[Diagnostic]) -> None:
    dangling = [item for item in diagnostics if item.code == "dangling-use"]
    if not dangling:
        return
    print("\nWarnings:", file=sys.stderr)
    for item in dangling:
        print("  " + _diagnostic(item), file=sys.stderr)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Validate the blueprint dependency graph and report a goal-aware frontier."
    )
    parser.add_argument(
        "--tex",
        type=Path,
        default=DEFAULT_TEX,
        help="blueprint source to parse (default: blueprint/src/content.tex)",
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="list every pending node in document order instead of the frontier",
    )
    goal_options = parser.add_mutually_exclusive_group()
    goal_options.add_argument(
        "--goal",
        default=None,
        help="goal label for ranking; pass an empty string to disable goal-aware metrics",
    )
    goal_options.add_argument(
        "--milestone",
        help="restrict the frontier to a named milestone path",
    )
    output_options = parser.add_mutually_exclusive_group()
    output_options.add_argument(
        "--milestones",
        action="store_true",
        help="show progress for configured milestones and exit",
    )
    output_options.add_argument(
        "--why",
        metavar="LABEL",
        help="explain why LABEL is blocked or ready and exit",
    )
    output_options.add_argument(
        "--json",
        action="store_true",
        help="emit machine-readable JSON",
    )
    parser.add_argument(
        "--top",
        type=int,
        help="show at most N ranked frontier nodes",
    )
    parser.add_argument(
        "--statement-only",
        action="store_true",
        help="ignore \\uses commands inside proofs",
    )
    parser.add_argument(
        "--allow-dangling",
        action="store_true",
        help="allow missing dependency labels while keeping them as blockers",
    )
    args = parser.parse_args(argv)

    if args.top is not None and args.top <= 0:
        parser.error("--top must be positive")
    if args.milestones and (
        args.goal is not None or args.milestone or args.all or args.top is not None
    ):
        parser.error("--milestones cannot be combined with --goal, --milestone, --all, or --top")
    if args.why and (
        args.goal is not None or args.milestone or args.all or args.top is not None
    ):
        parser.error("--why cannot be combined with --goal, --milestone, --all, or --top")
    if args.all and (args.json or args.milestone or args.top is not None):
        parser.error("--all cannot be combined with --json, --milestone, or --top")
    if not args.tex.is_file():
        print(f"error: blueprint source not found: {args.tex}", file=sys.stderr)
        return 2

    try:
        tex = args.tex.read_text(encoding="utf-8")
    except OSError as error:
        print(f"error: {error}", file=sys.stderr)
        return 2
    nodes = parse_blueprint(tex, not args.statement_only)

    diagnostics = validate_source(tex) + validate_graph(nodes)
    fatal = [
        item
        for item in diagnostics
        if item.code != "dangling-use" or not args.allow_dangling
    ]
    if fatal:
        print("Blueprint graph validation failed:", file=sys.stderr)
        for item in fatal:
            print("  " + _diagnostic(item), file=sys.stderr)
        return 2

    known = {node.label for node in nodes}
    if args.milestone and args.milestone not in MILESTONES:
        print(f"error: unknown milestone: {args.milestone}", file=sys.stderr)
        return 2

    analysis = analyse(nodes)
    if args.milestones:
        bad_milestones = {
            name: label for name, label in MILESTONES.items() if label not in known
        }
        if bad_milestones:
            print("Milestone validation failed:", file=sys.stderr)
            for name, label in sorted(bad_milestones.items()):
                print(f"  {name}: unknown goal {label}", file=sys.stderr)
            return 2
        print(format_milestones(analysis))
        if diagnostics and args.allow_dangling:
            _print_dangling_warnings(diagnostics)
        return 0

    if args.why:
        print(format_why(args.why, analysis))
        if diagnostics and args.allow_dangling:
            _print_dangling_warnings(diagnostics)
        return 0 if args.why in known else 2

    if args.all:
        goal = args.goal or None
        if goal is not None and goal not in known:
            print(f"error: goal label not found in blueprint: {goal}", file=sys.stderr)
            return 2
        print(
            format_text(
                analysis,
                {},
                args.tex,
                True,
                goal,
                None,
                False,
                not args.statement_only,
            )
        )
        if diagnostics and args.allow_dangling:
            _print_dangling_warnings(diagnostics)
        return 0

    goal = args.goal
    restrict = False
    if args.milestone:
        goal = MILESTONES[args.milestone]
        restrict = True
    elif goal is None:
        goal = DEFAULT_GOAL
    goal = goal or None
    if goal is not None and goal not in known:
        print(f"error: goal label not found in blueprint: {goal}", file=sys.stderr)
        return 2

    metrics = compute_metrics(analysis, goal)
    if args.json:
        print(format_json(analysis, metrics, args.tex, goal, args.top, restrict))
    else:
        print(
            format_text(
                analysis,
                metrics,
                args.tex,
                args.all,
                goal,
                args.top,
                restrict,
                not args.statement_only,
            )
        )

    if diagnostics and args.allow_dangling:
        _print_dangling_warnings(diagnostics)
    return 0


if __name__ == "__main__":
    sys.exit(main())
