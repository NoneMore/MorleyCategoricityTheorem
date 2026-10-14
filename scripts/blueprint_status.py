#!/usr/bin/env python3
"""Validate and plan formalization progress against the Lean blueprint.

Nodes are labelled theorem-like LaTeX environments. ``\\uses{...}`` declares
edges, and ``\\leanok``/``\\mathlibok`` mark completed nodes. The default
report ranks the dependency frontier with a goal-aware planning order.

Examples::

    python3 scripts/blueprint_status.py
    python3 scripts/blueprint_status.py --milestone omega_stability --top 5
    python3 scripts/blueprint_status.py --milestones
    python3 scripts/blueprint_status.py --why thm:two-cardinal-transfer
    python3 scripts/blueprint_status.py --unlocks lem:pair-relativization
    python3 scripts/blueprint_status.py --plan morley
    python3 scripts/blueprint_status.py --json
"""

from __future__ import annotations

import argparse
import heapq
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

try:
    import tomllib
except ModuleNotFoundError:  # pragma: no cover - Python < 3.11
    tomllib = None  # type: ignore[assignment]

NODE_ENVIRONMENTS = ("definition", "theorem", "lemma", "proposition", "corollary")
FORMALIZED_MARKERS = ("\\leanok", "\\mathlibok")
EFFORT_BY_KIND = {
    "definition": 1,
    "lemma": 2,
    "proposition": 2,
    "corollary": 2,
    "theorem": 3,
}
DEFAULT_GOAL = "cor:morley-categoricity"
REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_TEX = REPO_ROOT / "blueprint/src/content.tex"
DEFAULT_CONFIG = REPO_ROOT / "scripts/blueprint_status.toml"

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
class PlannerConfig:
    milestones: dict[str, str] = field(default_factory=dict)
    effort: dict[str, int] = field(default_factory=dict)
    risk: dict[str, str] = field(default_factory=dict)


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


@dataclass
class Metrics:
    label: str
    kind: str
    unlocks: int
    reach: int
    new_ready: int
    on_goal_path: bool
    goal_reach: int
    distance: int | None
    critical_depth: int | None
    effort: int
    risk: str | None

    @property
    def score(self) -> float:
        leverage = self.new_ready + self.goal_reach + int(self.on_goal_path)
        return leverage / self.effort


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


def parse_blueprint(tex: str, include_proof_uses: bool = True) -> list[Node]:
    """Extract blueprint nodes from one TeX document in document order."""
    nodes: list[Node] = []
    masked = _mask_comments(tex)
    for match in _NODE_RE.finditer(masked):
        kind, raw_title = match.group(1), match.group(2)
        body = tex[match.start(3):match.end(3)]
        clean_body = _mask_comments(body)
        label_match = _LABEL_RE.search(clean_body)
        if label_match is None:
            continue
        proof_uses: set[str] = set()
        if include_proof_uses:
            proof_match = _PROOF_RE.match(tex[match.end():])
            if proof_match is not None:
                proof_uses = _labels(_mask_comments(proof_match.group(1)))
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


def load_config(path: Path | None) -> PlannerConfig:
    if path is None or not path.is_file():
        return PlannerConfig()
    if tomllib is None:
        raise RuntimeError("planner config requires Python 3.11+ (tomllib)")
    data = tomllib.loads(path.read_text(encoding="utf-8"))
    milestones = {str(k): str(v) for k, v in data.get("milestones", {}).items()}
    effort: dict[str, int] = {}
    risk: dict[str, str] = {}
    for label, metadata in data.get("nodes", {}).items():
        if not isinstance(metadata, dict):
            raise ValueError(f"node metadata must be a table: {label}")
        if "effort" in metadata:
            value = int(metadata["effort"])
            if value <= 0:
                raise ValueError(f"effort must be positive for {label}")
            effort[str(label)] = value
        if "risk" in metadata:
            risk[str(label)] = str(metadata["risk"])
    return PlannerConfig(milestones, effort, risk)


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
                        Diagnostic("dependency-cycle", " -> ".join(cycle), label, _known(nodes)[label].line)
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
        if node.formalized:
            continue
        unknown = node.uses - known.keys()
        if unknown:
            dangling.append((node, unknown))
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


def _required_dangling(goal: str, nodes: list[Node]) -> set[str]:
    """Return unknown labels referenced anywhere in the known dependency closure."""
    known = _known(nodes)
    required = _required(goal, _dependencies(nodes))
    return {
        dep
        for label in required
        for dep in known[label].uses
        if dep not in known
    }


def _chain_bounds(
    label: str,
    goal: str,
    dependents: dict[str, set[str]],
    formalized: set[str],
    memo: dict[str, tuple[int, int] | None],
) -> tuple[int, int] | None:
    if label in memo:
        return memo[label]
    if label == goal:
        memo[label] = (0, 0)
        return (0, 0)
    paths: list[tuple[int, int]] = []
    for child in dependents.get(label, ()):
        tail = _chain_bounds(child, goal, dependents, formalized, memo)
        if tail is not None:
            step = 0 if child in formalized else 1
            paths.append((step + tail[0], step + tail[1]))
    memo[label] = None if not paths else (
        min(path[0] for path in paths),
        max(path[1] for path in paths),
    )
    return memo[label]


def _effort(node: Node, config: PlannerConfig) -> int:
    return config.effort.get(node.label, EFFORT_BY_KIND.get(node.kind, 2))


def compute_metrics(
    analysis: Analysis,
    goal: str | None = DEFAULT_GOAL,
    config: PlannerConfig | None = None,
) -> dict[str, Metrics]:
    config = config or PlannerConfig()
    known = _known(analysis.nodes)
    pending = analysis.pending
    pending_labels = {node.label for node in pending}
    frontier_labels = {node.label for node in analysis.frontier}
    dependents = _dependents(analysis.nodes)
    dependencies = _dependencies(analysis.nodes)
    required = _required(goal, dependencies) if goal in known else set()
    memo: dict[str, tuple[int, int] | None] = {}
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
        bounds = _chain_bounds(node.label, goal, dependents, analysis.formalized, memo) if goal else None
        metrics[node.label] = Metrics(
            node.label,
            node.kind,
            sum(1 for other in pending if node.label in other.uses),
            len(reach),
            new_ready,
            node.label in required,
            len(reach & required),
            None if bounds is None else bounds[0],
            None if bounds is None else bounds[1],
            _effort(node, config),
            config.risk.get(node.label),
        )
    return metrics


def _none_high(value: int | None) -> int:
    return value if value is not None else 10**9


def sort_key(name: str, item: Metrics) -> tuple[object, ...]:
    if name == "plan":
        return (
            -int(item.on_goal_path),
            -item.new_ready,
            -item.goal_reach,
            item.effort,
            _none_high(item.distance),
            -item.unlocks,
            item.label,
        )
    if name == "score":
        return (-item.score, item.effort, item.label)
    if name == "unlocks":
        return (-item.unlocks, item.effort, item.label)
    if name == "reach":
        return (-item.reach, item.effort, item.label)
    if name == "goal-reach":
        return (-item.goal_reach, item.effort, item.label)
    if name == "new":
        return (-item.new_ready, item.effort, item.label)
    if name == "distance":
        return (_none_high(item.distance), item.effort, item.label)
    if name == "critical":
        return (-(item.critical_depth if item.critical_depth is not None else -1), item.effort, item.label)
    if name == "effort":
        return (item.effort, -item.goal_reach, item.label)
    raise ValueError(name)


SORT_KEYS = ("plan", "score", "unlocks", "reach", "goal-reach", "new", "distance", "critical", "effort")
SORT_DESCRIPTIONS = {
    "plan": "goal path, immediate unlocks, goal reach, then effort",
    "score": "goal leverage / effort",
    "unlocks": "direct pending dependents",
    "reach": "transitive pending dependents",
    "goal-reach": "pending dependents on goal paths",
    "new": "blocked nodes becoming ready",
    "distance": "shortest pending distance to the goal",
    "critical": "longest pending chain to the goal",
    "effort": "estimated effort (cheapest first)",
}
HEADERS = ("#", "node", "kind", "goal", "new", "g-reach", "dist", "crit", "eff", "risk", "score")


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
    sort_name: str,
    top: int | None,
    restrict_to_goal: bool,
) -> tuple[list[Metrics], int]:
    items = [metrics[node.label] for node in analysis.frontier]
    if restrict_to_goal:
        items = [item for item in items if item.on_goal_path]
    candidate_count = len(items)
    items.sort(key=lambda item: sort_key(sort_name, item))
    if top is not None:
        items = items[:top]
    return items, candidate_count


def _priority_rows(items: list[Metrics]) -> list[tuple[str, ...]]:
    return [
        (
            str(i), item.label, item.kind, "yes" if item.on_goal_path else "-",
            str(item.new_ready), str(item.goal_reach),
            "-" if item.distance is None else str(item.distance),
            "-" if item.critical_depth is None else str(item.critical_depth),
            str(item.effort), item.risk or "-", f"{item.score:.2f}",
        )
        for i, item in enumerate(items, 1)
    ]


def _resolve_target(value: str, config: PlannerConfig, known: set[str]) -> str | None:
    label = config.milestones.get(value, value)
    return label if label in known else None


def milestone_rows(analysis: Analysis, config: PlannerConfig) -> list[tuple[str, ...]]:
    known = _known(analysis.nodes)
    dependencies = _dependencies(analysis.nodes)
    frontier = {node.label for node in analysis.frontier}
    rows: list[tuple[str, ...]] = []
    for name, goal in config.milestones.items():
        required = _required(goal, dependencies)
        pending = required - analysis.formalized
        rows.append(
            (name, goal, str(len(required) - len(pending)), str(len(pending)),
             str(len(pending & frontier)), str(sum(_effort(known[label], config) for label in pending)))
        )
    return rows


def format_milestones(analysis: Analysis, config: PlannerConfig) -> str:
    rows = milestone_rows(analysis, config)
    if not rows:
        return "No milestones configured."
    return "Milestones\n" + "\n".join(
        _format_table(("milestone", "goal", "done", "pending", "ready", "effort"), rows)
    )


def format_why(label: str, analysis: Analysis, config: PlannerConfig) -> str:
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
            lines.append(f"{prefix}{current}  [ready, effort={_effort(node, config)}]")
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


def format_unlocks(label: str, analysis: Analysis) -> str:
    known = _known(analysis.nodes)
    if label not in known:
        return f"unknown node: {label}"
    dependents = _dependents(analysis.nodes)
    pending = {node.label for node in analysis.pending}
    direct = sorted(dependents[label] & pending)
    transitive = sorted(_reachable(label, dependents) & pending)
    lines = [
        f"Unlocks for {label}",
        f"  direct pending dependents ({len(direct)}): " + (", ".join(direct) or "none"),
        f"  transitive pending dependents ({len(transitive)}):",
    ]
    return "\n".join(lines + [f"    {item}" for item in transitive])


def plan_dangling(target: str, analysis: Analysis, config: PlannerConfig) -> set[str]:
    known = _known(analysis.nodes)
    resolved = _resolve_target(target, config, set(known))
    if resolved is None:
        return set()
    return _required_dangling(resolved, analysis.nodes)


def format_plan(target: str, analysis: Analysis, config: PlannerConfig) -> str:
    known = _known(analysis.nodes)
    resolved = _resolve_target(target, config, set(known))
    if resolved is None:
        return f"unknown milestone or node: {target}"
    dangling = _required_dangling(resolved, analysis.nodes)
    if dangling:
        return "\n".join(
            [f"Plan for {target} -> {resolved} is blocked by missing dependency labels:"]
            + [f"  ? {label}" for label in sorted(dangling)]
        )

    dependencies = _dependencies(analysis.nodes)
    pending = _required(resolved, dependencies) - analysis.formalized
    indegree = {label: len(dependencies[label] & pending) for label in pending}
    children = {label: set() for label in pending}
    for label in pending:
        for dep in dependencies[label] & pending:
            children[dep].add(label)
    heap = [(_effort(known[label], config), label) for label, degree in indegree.items() if degree == 0]
    heapq.heapify(heap)
    ordered: list[str] = []
    while heap:
        _, label = heapq.heappop(heap)
        ordered.append(label)
        for child in children[label]:
            indegree[child] -= 1
            if indegree[child] == 0:
                heapq.heappush(heap, (_effort(known[child], config), child))
    lines = [f"Plan for {target} -> {resolved} ({len(ordered)} pending nodes)"]
    for i, label in enumerate(ordered, 1):
        node = known[label]
        risk = f" risk={config.risk[label]}" if label in config.risk else ""
        lines.append(f"  {i:>2}. {label} effort={_effort(node, config)}{risk} line={node.line}")
    return "\n".join(lines)


def format_text(
    analysis: Analysis,
    metrics: dict[str, Metrics],
    tex_path: Path,
    show_all: bool,
    sort_name: str,
    goal: str | None,
    top: int | None,
    restrict_to_goal: bool,
) -> str:
    lines = [
        f"Blueprint status for {tex_path}",
        f"  {len(analysis.nodes)} nodes: {len(analysis.formalized)} formalized, {len(analysis.pending)} pending",
        f"  {len(analysis.frontier)} pending nodes on the dependency frontier",
        "  graph validation passed; statement/proof dependencies are merged",
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
        analysis, metrics, sort_name, top, restrict_to_goal
    )
    rows = _priority_rows(selected)
    lines.append(
        f"Frontier by {SORT_DESCRIPTIONS[sort_name]} ({candidate_count} candidates; goal={goal or 'none'})"
    )
    lines += _format_table(HEADERS, rows) if rows else ["  (none)"]
    lines += [
        "  goal=yes: node lies on a path to the selected goal; g-reach: pending goal-path descendants",
        "  dist/crit: shortest/longest pending distance to goal; effort: TOML override or kind fallback",
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


def format_json((
    analysis: Analysis,
    metrics: dict[str, Metrics],
    tex_path: Path,
    goal: str | None,
    config: PlannerConfig,
    sort_name: str = "plan",
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
            "unlocks": item.unlocks,
            "reach": item.reach,
            "new_ready": item.new_ready,
            "on_goal_path": item.on_goal_path,
            "goal_reach": item.goal_reach,
            "distance": item.distance,
            "critical_depth": item.critical_depth,
            "effort": item.effort,
            "risk": item.risk,
            "score": round(item.score, 3),
        }

    selected, candidate_count = _select_frontier_metrics(
        analysis, metrics, sort_name, top, restrict_to_goal
    )
    payload = {
        "tex": str(tex_path),
        "goal": goal,
        "milestones": config.milestones,
        "selection": {
            "sort": sort_name,
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
        "frontier": [
            node_entry({node.label: node for node in analysis.frontier}[item.label])
            for item in selected
        ],
        "pending": [node_entry(node) for node in analysis.pending],
        "metrics": {node.label: metric_entry(metrics[node.label]) for node in analysis.pending},
        "dangling_uses": [
            {"label": node.label, "missing": sorted(unknown)} for node, unknown in analysis.dangling
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
    parser = argparse.ArgumentParser(description="Validate and plan blueprint formalization progress.")
    parser.add_argument("--tex", type=Path, default=DEFAULT_TEX)
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG)
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--sort", choices=SORT_KEYS, default="plan")
    parser.add_argument("--goal", default=None)
    parser.add_argument("--milestone")
    parser.add_argument("--milestones", action="store_true")
    parser.add_argument("--why", metavar="LABEL")
    parser.add_argument("--unlocks", metavar="LABEL")
    parser.add_argument("--plan", metavar="MILESTONE_OR_LABEL")
    parser.add_argument("--top", type=int)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--statement-only", action="store_true")
    parser.add_argument("--allow-dangling", action="store_true")
    args = parser.parse_args(argv)

    if args.top is not None and args.top <= 0:
        parser.error("--top must be positive")
    if not args.tex.is_file():
        print(f"error: blueprint source not found: {args.tex}", file=sys.stderr)
        return 2
    try:
        config = load_config(args.config)
        nodes = parse_blueprint(args.tex.read_text(encoding="utf-8"), not args.statement_only)
    except (OSError, RuntimeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    diagnostics = validate_graph(nodes)
    fatal = [item for item in diagnostics if item.code != "dangling-use" or not args.allow_dangling]
    if fatal:
        print("Blueprint graph validation failed:", file=sys.stderr)
        for item in fatal:
            print("  " + _diagnostic(item), file=sys.stderr)
        return 2

    known = {node.label for node in nodes}
    bad_milestones = {name: label for name, label in config.milestones.items() if label not in known}
    bad_metadata = sorted((set(config.effort) | set(config.risk)) - known)
    if bad_milestones or bad_metadata:
        print("Planner config validation failed:", file=sys.stderr)
        for name, label in sorted(bad_milestones.items()):
            print(f"  milestone {name}: unknown goal {label}", file=sys.stderr)
        for label in bad_metadata:
            print(f"  node metadata: unknown label {label}", file=sys.stderr)
        return 2
    if args.milestone and args.milestone not in config.milestones:
        print(f"error: unknown milestone: {args.milestone}", file=sys.stderr)
        return 2

    goal = args.goal
    restrict = False
    if args.milestone:
        goal = config.milestones[args.milestone]
        restrict = True
    elif goal is None:
        goal = config.milestones.get("morley", DEFAULT_GOAL)
    goal = goal or None
    if goal is not None and goal not in known:
        print(f"error: goal label not found in blueprint: {goal}", file=sys.stderr)
        return 2

    analysis = analyse(nodes)
    metrics = compute_metrics(analysis, goal, config)
    exit_code = 0
    if args.milestones:
        print(format_milestones(analysis, config))
    elif args.why:
        print(format_why(args.why, analysis, config))
        exit_code = 0 if args.why in known else 2
    elif args.unlocks:
        print(format_unlocks(args.unlocks, analysis))
        exit_code = 0 if args.unlocks in known else 2
    elif args.plan:
        print(format_plan(args.plan, analysis, config))
        resolved = _resolve_target(args.plan, config, known)
        if resolved is None or plan_dangling(args.plan, analysis, config):
            exit_code = 2
    elif args.json:
        print(format_json(analysis, metrics, args.tex, goal, config, args.sort, args.top, restrict))
    else:
        print(format_text(analysis, metrics, args.tex, args.all, args.sort, goal, args.top, restrict))

    if diagnostics and args.allow_dangling:
        _print_dangling_warnings(diagnostics)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
