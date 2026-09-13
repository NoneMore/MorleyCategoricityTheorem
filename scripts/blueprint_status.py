#!/usr/bin/env python3
"""Report formalization progress against the Lean blueprint.

The blueprint in ``blueprint/src/content.tex`` is a dependency graph: every
``definition``, ``theorem``, ``lemma``, ``proposition`` and ``corollary``
carries a ``\\label`` and declares the nodes it builds on with ``\\uses{...}``.
A node is marked as syntactic sugar for "already formalized" by ``\\leanok``
(proved in this repository) or ``\\mathlibok`` (supplied by Mathlib).

This script parses that graph and answers two questions:

1. *What can be formalized next?* The **dependency frontier** is the pending
   nodes whose dependencies are all already formalized; the nodes that are held
   up only by a missing definition are listed separately.
2. *Which frontier node should be done first?* For every node the script
   computes leverage metrics on the dependency graph and ranks the frontier by
   a composite priority score:

       score = (unlocks + reach + new_ready + critical) / effort

   where ``unlocks`` is the number of pending nodes that directly depend on the
   node, ``reach`` the number that depend on it transitively, ``new_ready`` the
   number of currently blocked nodes that become frontier as soon as it is
   done, ``critical`` the length of the longest remaining chain of pending
   nodes from it to the goal, and ``effort`` a coarse cost proxy taken from the
   node kind. The components are printed alongside the score, and ``--sort``
   ranks by any single metric instead.

``\\uses`` commands inside a node's attached proof are counted as dependencies
too, because they are the lemmas the proof actually invokes.

The script only reads the blueprint. It never writes to ``blueprint/`` and it
is not a substitute for the ``leanblueprint`` build.

Usage::

    python3 scripts/blueprint_status.py            # frontier by priority
    python3 scripts/blueprint_status.py --all      # every pending node
    python3 scripts/blueprint_status.py --sort reach
    python3 scripts/blueprint_status.py --json     # machine-readable output
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

NODE_ENVIRONMENTS = ("definition", "theorem", "lemma", "proposition", "corollary")

# Markers that count a node as formalized.
FORMALIZED_MARKERS = ("\\leanok", "\\mathlibok")

# Coarse cost proxy by node kind: definitions are usually short, theorems are
# usually the hard part. Only used as a divisor in the priority score.
EFFORT_BY_KIND = {
    "definition": 1,
    "lemma": 2,
    "proposition": 2,
    "corollary": 2,
    "theorem": 3,
}

# The blueprint's final result, used to measure critical paths.
DEFAULT_GOAL = "cor:morley-categoricity"

_NODE_RE = re.compile(
    r"\\begin\{(" + "|".join(NODE_ENVIRONMENTS) + r")\}"
    r"(\[[^\]]*\])?"
    r"(.*?)"
    r"\\end\{\1\}",
    re.S,
)
_LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
_USES_RE = re.compile(r"\\uses\{([^}]*)\}")
# A proof attaches to its node only if it starts immediately after the node's
# environment (comments and blank lines aside).
_PROOF_RE = re.compile(r"\A\s*\\begin\{proof\}(.*?)\\end\{proof\}", re.S)

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_TEX = REPO_ROOT / "blueprint/src/content.tex"


@dataclass
class Node:
    """One labelled blueprint node."""

    label: str
    kind: str
    title: str | None
    formalized: bool
    statement_uses: set[str] = field(default_factory=set)
    proof_uses: set[str] = field(default_factory=set)
    line: int = 0

    @property
    def uses(self) -> set[str]:
        """All dependencies declared by the node, statement and proof alike."""
        return self.statement_uses | self.proof_uses


def _labels(text: str) -> set[str]:
    """Collect the labels of every ``\\uses{...}`` command in ``text``."""
    found: set[str] = set()
    for group in _USES_RE.findall(text):
        found.update(part.strip() for part in group.split(",") if part.strip())
    return found


def parse_blueprint(tex: str, include_proof_uses: bool = True) -> list[Node]:
    """Extract the nodes of a blueprint document, in document order."""
    nodes: list[Node] = []
    for match in _NODE_RE.finditer(tex):
        kind, raw_title, body = match.group(1), match.group(2), match.group(3)
        label_match = _LABEL_RE.search(body)
        if label_match is None:
            continue
        proof_uses: set[str] = set()
        if include_proof_uses:
            proof_match = _PROOF_RE.match(tex[match.end():])
            if proof_match is not None:
                proof_uses = _labels(proof_match.group(1))
        nodes.append(
            Node(
                label=label_match.group(1).strip(),
                kind=kind,
                title=raw_title[1:-1].strip() if raw_title else None,
                formalized=any(marker in body for marker in FORMALIZED_MARKERS),
                statement_uses=_labels(body),
                proof_uses=proof_uses,
                line=tex.count("\n", 0, match.start()) + 1,
            )
        )
    return nodes


@dataclass
class Analysis:
    """The dependency analysis of a blueprint."""

    nodes: list[Node]
    formalized: set[str]
    frontier: list[Node]
    blocked_by_definitions: list[tuple[Node, set[str]]]
    blocked: list[tuple[Node, set[str]]]
    dangling: list[tuple[Node, set[str]]]

    @property
    def pending(self) -> list[Node]:
        return [node for node in self.nodes if not node.formalized]


def analyse(nodes: list[Node]) -> Analysis:
    """Split the pending nodes into frontier and blocked groups."""
    known = {node.label: node for node in nodes}
    formalized = {node.label for node in nodes if node.formalized}
    frontier: list[Node] = []
    blocked_by_definitions: list[tuple[Node, set[str]]] = []
    blocked: list[tuple[Node, set[str]]] = []
    dangling: list[tuple[Node, set[str]]] = []
    for node in nodes:
        if node.formalized:
            continue
        unknown = node.uses - known.keys()
        if unknown:
            dangling.append((node, unknown))
        missing = {label for label in node.uses if label in known and label not in formalized}
        if not missing:
            frontier.append(node)
        elif all(known[label].kind == "definition" for label in missing):
            blocked_by_definitions.append((node, missing))
        else:
            blocked.append((node, missing))
    return Analysis(nodes, formalized, frontier, blocked_by_definitions, blocked, dangling)


@dataclass
class Metrics:
    """Leverage metrics of one pending node on the blueprint dependency graph."""

    label: str
    kind: str
    unlocks: int  # pending nodes that directly \use this node
    reach: int  # pending nodes that transitively \use this node
    new_ready: int  # blocked nodes that become frontier once this one is done
    critical: int | None  # longest pending chain to the goal; None if off-goal
    effort: int  # coarse cost proxy by node kind

    @property
    def score(self) -> float:
        """Composite priority: leverage per unit of (heuristic) effort."""
        critical = self.critical if self.critical is not None else 0
        return (self.unlocks + self.reach + self.new_ready + critical) / self.effort


def _dependents(nodes: list[Node]) -> dict[str, set[str]]:
    """Reverse dependency edges: label -> nodes that ``\\use`` it."""
    known = {node.label for node in nodes}
    dependents: dict[str, set[str]] = {node.label: set() for node in nodes}
    for node in nodes:
        for dep in node.uses:
            if dep in known:
                dependents[dep].add(node.label)
    return dependents


def _reachable(label: str, dependents: dict[str, set[str]], memo: dict[str, set[str]]) -> set[str]:
    """Transitive closure of the dependents relation, memoized per label."""
    if label in memo:
        return memo[label]
    seen: set[str] = set()
    stack = list(dependents.get(label, ()))
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        stack.extend(dependents.get(current, ()))
    memo[label] = seen
    return seen


def _longest_chain(
    label: str,
    dependents: dict[str, set[str]],
    formalized: set[str],
    goal: str,
    memo: dict[str, int | None],
    visiting: set[str],
) -> int | None:
    """Longest chain of pending nodes from ``label`` (exclusive) to ``goal``.

    Returns ``None`` when the node lies on no path to the goal at all, for
    example a standalone result the blueprint never reuses.
    """
    if label in memo:
        return memo[label]
    if label == goal:
        memo[label] = 0
        return 0
    if label in visiting:  # defensive: the blueprint graph should be acyclic
        return None
    visiting.add(label)
    best: int | None = None
    for dependent in dependents.get(label, ()):
        tail = _longest_chain(dependent, dependents, formalized, goal, memo, visiting)
        if tail is None:
            continue
        steps = (0 if dependent in formalized else 1) + tail
        best = steps if best is None else max(best, steps)
    visiting.discard(label)
    memo[label] = best
    return best


def compute_metrics(
    analysis: Analysis, goal: str | None = DEFAULT_GOAL
) -> dict[str, Metrics]:
    """Compute leverage metrics for every pending node."""
    known = {node.label: node for node in analysis.nodes}
    pending = analysis.pending
    pending_labels = {node.label for node in pending}
    frontier_labels = {node.label for node in analysis.frontier}
    dependents = _dependents(analysis.nodes)
    if goal is not None and goal not in known:
        goal = None

    reach_memo: dict[str, set[str]] = {}
    chain_memo: dict[str, int | None] = {}
    metrics: dict[str, Metrics] = {}
    for node in pending:
        reach = _reachable(node.label, dependents, reach_memo) & pending_labels
        done = analysis.formalized | {node.label}
        new_ready = sum(
            1
            for other in pending
            if other.label != node.label
            and other.label not in frontier_labels
            and not {dep for dep in other.uses if dep in known and dep not in done}
        )
        critical = (
            _longest_chain(node.label, dependents, analysis.formalized, goal, chain_memo, set())
            if goal is not None
            else None
        )
        metrics[node.label] = Metrics(
            label=node.label,
            kind=node.kind,
            unlocks=sum(1 for other in pending if node.label in other.uses),
            reach=len(reach),
            new_ready=new_ready,
            critical=critical,
            effort=EFFORT_BY_KIND.get(node.kind, 2),
        )
    return metrics


SORT_KEYS = {
    "score": lambda m: (-m.score, m.label),
    "unlocks": lambda m: (-m.unlocks, -m.score, m.label),
    "reach": lambda m: (-m.reach, -m.score, m.label),
    "new": lambda m: (-m.new_ready, -m.score, m.label),
    "critical": lambda m: (-(m.critical if m.critical is not None else -1), -m.score, m.label),
    "effort": lambda m: (m.effort, -m.score, m.label),
}

SORT_DESCRIPTIONS = {
    "score": "score = (unlocks + reach + new_ready + critical) / effort",
    "unlocks": "unlocks (direct pending dependents)",
    "reach": "reach (transitive pending dependents)",
    "new": "new_ready (blocked nodes unblocked)",
    "critical": "critical (longest pending chain to the goal)",
    "effort": "effort (cheapest first)",
}

HEADERS = ("#", "node", "kind", "unlks", "reach", "crit", "new", "eff", "score")


def _priority_rows(metrics: list[Metrics], sort_key: str) -> list[tuple[str, ...]]:
    rows = []
    for rank, item in enumerate(sorted(metrics, key=SORT_KEYS[sort_key]), start=1):
        rows.append(
            (
                str(rank),
                item.label,
                item.kind,
                str(item.unlocks),
                str(item.reach),
                "-" if item.critical is None else str(item.critical),
                str(item.new_ready),
                str(item.effort),
                f"{item.score:.1f}",
            )
        )
    return rows


def _format_table(headers: tuple[str, ...], rows: list[tuple[str, ...]]) -> list[str]:
    widths = [len(header) for header in headers]
    for row in rows:
        for i, cell in enumerate(row):
            widths[i] = max(widths[i], len(cell))
    lines = ["  " + "  ".join(h.ljust(widths[i]) for i, h in enumerate(headers)).rstrip()]
    for row in rows:
        lines.append("  " + "  ".join(c.ljust(widths[i]) for i, c in enumerate(row)).rstrip())
    return lines


def format_text(
    analysis: Analysis,
    metrics: dict[str, Metrics],
    tex_path: Path,
    show_all: bool,
    sort_key: str,
    goal: str | None,
    warn_off_goal: bool = True,
) -> str:
    total = len(analysis.nodes)
    done = len(analysis.formalized)
    lines = [
        f"Blueprint status for {tex_path}",
        f"  {total} nodes: {done} formalized, {total - done} pending",
        f"  {len(analysis.frontier)} pending nodes on the dependency frontier",
        "  dependencies merged from statements and proofs;"
        " \\leanok and \\mathlibok count as formalized",
        "",
    ]
    if show_all:
        lines.append(f"Pending nodes in document order ({len(analysis.pending)}):")
        for node in analysis.pending:
            missing = node.uses - analysis.formalized
            missing = {m for m in missing if m in {n.label for n in analysis.nodes}}
            head = f"{node.label:<62} [{node.kind}]"
            if missing:
                head += "  needs " + ", ".join(sorted(missing))
            lines.append("  " + head)
    else:
        frontier_metrics = [metrics[node.label] for node in analysis.frontier]
        lines.append(
            f"Frontier by priority ({len(frontier_metrics)} pending nodes;"
            f" ranked by {SORT_DESCRIPTIONS[sort_key]})"
        )
        if frontier_metrics:
            lines += _format_table(HEADERS, _priority_rows(frontier_metrics, sort_key))
            lines += [
                "  unlks = pending nodes directly using this one"
                " | reach = transitively using it"
                " | new = blocked nodes becoming ready once it is done",
                "  crit  = longest remaining chain of pending nodes to the goal"
                f" ({goal or 'none'}); '-' means off-goal"
                " | eff = cost proxy (definition 1, lemma/proposition/corollary 2, theorem 3)",
            ]
        else:
            lines.append("  (none)")
        lines += [
            "",
            f"Blocked only by pending definitions ({len(analysis.blocked_by_definitions)}):",
        ]
        if analysis.blocked_by_definitions:
            for node, missing in analysis.blocked_by_definitions:
                head = f"{node.label:<62} [{node.kind}]"
                head += "  needs " + ", ".join(sorted(missing))
                lines.append("  " + head)
        else:
            lines.append("  (none)")
        lines += [
            "",
            f"Blocked by pending results ({len(analysis.blocked)}); "
            "pass --all to list every pending node",
        ]
    off_goal = (
        [
            node.label
            for node in analysis.pending
            if metrics[node.label].critical is None
        ]
        if warn_off_goal and goal is not None
        else []
    )
    warnings: list[str] = []
    for node, unknown in analysis.dangling:
        warnings.append(f"  {node.label}: \\uses with no matching node: {', '.join(sorted(unknown))}")
    if off_goal:
        warnings.append(f"  off-goal (no path to {goal}): {', '.join(off_goal)}")
    if warnings:
        lines += ["", "Warnings:"] + warnings
    return "\n".join(lines)


def format_json(
    analysis: Analysis,
    metrics: dict[str, Metrics],
    tex_path: Path,
    goal: str | None,
) -> str:
    known = {node.label for node in analysis.nodes}

    def entry(node: Node) -> dict[str, object]:
        missing = sorted(
            label
            for label in node.uses
            if label in known and label not in analysis.formalized
        )
        return {
            "label": node.label,
            "kind": node.kind,
            "title": node.title,
            "line": node.line,
            "formalized": node.formalized,
            "missing": missing,
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
            "critical": item.critical,
            "effort": item.effort,
            "score": round(item.score, 3),
        }

    payload = {
        "tex": str(tex_path),
        "goal": goal,
        "counts": {
            "nodes": len(analysis.nodes),
            "formalized": len(analysis.formalized),
            "pending": len(analysis.pending),
            "frontier": len(analysis.frontier),
        },
        "priority": [
            metric_entry(metrics[node.label])
            for node in sorted(
                analysis.frontier, key=lambda n: SORT_KEYS["score"](metrics[n.label])
            )
        ],
        "frontier": [entry(node) for node in analysis.frontier],
        "metrics": {
            node.label: metric_entry(metrics[node.label]) for node in analysis.pending
        },
        "blocked_by_definitions": [
            {"label": node.label, "missing": sorted(missing)}
            for node, missing in analysis.blocked_by_definitions
        ],
        "pending": [entry(node) for node in analysis.pending],
        "dangling_uses": [
            {"label": node.label, "missing": sorted(unknown)}
            for node, unknown in analysis.dangling
        ],
    }
    return json.dumps(payload, indent=2, ensure_ascii=False)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Report blueprint formalization progress, dependency frontier, and priority.",
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
    parser.add_argument(
        "--sort",
        choices=tuple(SORT_KEYS),
        default="score",
        help="metric used to rank the frontier (default: score)",
    )
    parser.add_argument(
        "--goal",
        default=DEFAULT_GOAL,
        help="label used as the goal for critical-path lengths"
        f" (default: {DEFAULT_GOAL}; pass an empty string to disable)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="emit machine-readable JSON",
    )
    parser.add_argument(
        "--statement-only",
        action="store_true",
        help="ignore \\uses commands inside proofs",
    )
    args = parser.parse_args(argv)

    if not args.tex.is_file():
        print(f"error: blueprint source not found: {args.tex}", file=sys.stderr)
        return 2
    nodes = parse_blueprint(args.tex.read_text(encoding="utf-8"), not args.statement_only)
    goal = args.goal or None
    if goal is not None and goal not in {node.label for node in nodes}:
        print(f"error: goal label not found in blueprint: {goal}", file=sys.stderr)
        return 2
    analysis = analyse(nodes)
    metrics = compute_metrics(analysis, goal)
    if args.json:
        print(format_json(analysis, metrics, args.tex, goal))
    else:
        print(
            format_text(
                analysis,
                metrics,
                args.tex,
                args.all,
                args.sort,
                goal,
                warn_off_goal=not args.statement_only,
            )
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
