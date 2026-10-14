from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

MODULE_PATH = Path(__file__).resolve().parents[1] / "blueprint_status.py"
spec = importlib.util.spec_from_file_location("blueprint_status", MODULE_PATH)
assert spec and spec.loader
bs = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = bs
spec.loader.exec_module(bs)


class BlueprintStatusTests(unittest.TestCase):
    def test_proof_uses_after_tex_comment_are_attached(self) -> None:
        tex = r"""
\begin{lemma}[A]\label{lem:a}\end{lemma}
% explanatory comment
\begin{proof}
\uses{lem:b}
Done.
\end{proof}
\begin{lemma}[B]\label{lem:b}\leanok\end{lemma}
"""
        nodes = bs.parse_blueprint(tex)
        self.assertEqual(nodes[0].proof_uses, {"lem:b"})

    def test_dangling_dependency_is_not_frontier(self) -> None:
        tex = r"""
\begin{lemma}\label{lem:a}\uses{lem:missing}\end{lemma}
"""
        nodes = bs.parse_blueprint(tex)
        analysis = bs.analyse(nodes)
        self.assertEqual(analysis.frontier, [])
        diagnostics = bs.validate_graph(nodes)
        self.assertEqual([item.code for item in diagnostics], ["dangling-use"])

    def test_duplicate_self_and_cycle_are_reported(self) -> None:
        tex = r"""
\begin{lemma}\label{lem:a}\uses{lem:b}\end{lemma}
\begin{lemma}\label{lem:b}\uses{lem:a}\end{lemma}
\begin{lemma}\label{lem:c}\uses{lem:c}\end{lemma}
\begin{lemma}\label{lem:c}\end{lemma}
"""
        codes = {item.code for item in bs.validate_graph(bs.parse_blueprint(tex))}
        self.assertEqual(
            codes,
            {"duplicate-label", "self-dependency", "dependency-cycle"},
        )

    def test_commented_nodes_and_uses_are_ignored(self) -> None:
        tex = r"""
% \begin{lemma}\label{lem:fake}\end{lemma}
\begin{lemma}\label{lem:real}\leanok\end{lemma}
\begin{lemma}\label{lem:user}
% \uses{lem:missing}
\uses{lem:real}
\end{lemma}
"""
        nodes = bs.parse_blueprint(tex)
        self.assertEqual([node.label for node in nodes], ["lem:real", "lem:user"])
        self.assertEqual(nodes[1].statement_uses, {"lem:real"})

    def test_effort_override_and_goal_metrics(self) -> None:
        tex = r"""
\begin{lemma}\label{lem:done}\leanok\end{lemma}
\begin{lemma}\label{lem:a}\uses{lem:done}\end{lemma}
\begin{theorem}\label{thm:goal}\uses{lem:a}\end{theorem}
"""
        nodes = bs.parse_blueprint(tex)
        analysis = bs.analyse(nodes)
        config = bs.PlannerConfig(effort={"lem:a": 8})
        metrics = bs.compute_metrics(analysis, "thm:goal", config)
        self.assertEqual(metrics["lem:a"].effort, 8)
        self.assertTrue(metrics["lem:a"].on_goal_path)
        self.assertEqual(metrics["lem:a"].distance, 1)
        self.assertEqual(metrics["lem:a"].goal_reach, 1)

    def test_milestone_summary_counts_required_nodes(self) -> None:
        tex = r"""
\begin{lemma}\label{lem:done}\leanok\end{lemma}
\begin{lemma}\label{lem:a}\uses{lem:done}\end{lemma}
\begin{theorem}\label{thm:goal}\uses{lem:a}\end{theorem}
\begin{lemma}\label{lem:off-goal}\end{lemma}
"""
        nodes = bs.parse_blueprint(tex)
        analysis = bs.analyse(nodes)
        config = bs.PlannerConfig(milestones={"demo": "thm:goal"})
        rows = bs.milestone_rows(analysis, config)
        self.assertEqual(rows[0][:5], ("demo", "thm:goal", "1", "2", "1"))

    def test_json_respects_milestone_sort_and_top(self) -> None:
        tex = r"""
\begin{lemma}\label{lem:a}\end{lemma}
\begin{lemma}\label{lem:b}\end{lemma}
\begin{lemma}\label{lem:off-goal}\end{lemma}
\begin{lemma}\label{lem:a-child}\uses{lem:a}\end{lemma}
\begin{theorem}\label{thm:goal}\uses{lem:a-child,lem:b}\end{theorem}
"""
        nodes = bs.parse_blueprint(tex)
        analysis = bs.analyse(nodes)
        config = bs.PlannerConfig(milestones={"demo": "thm:goal"})
        metrics = bs.compute_metrics(analysis, "thm:goal", config)
        payload = json.loads(
            bs.format_json(
                analysis,
                metrics,
                Path("demo.tex"),
                "thm:goal",
                config,
                sort_name="reach",
                top=1,
                restrict_to_goal=True,
            )
        )
        self.assertEqual([item["label"] for item in payload["priority"]], ["lem:a"])
        self.assertEqual([item["label"] for item in payload["frontier"]], ["lem:a"])
        self.assertEqual(payload["counts"]["frontier"], 1)
        self.assertEqual(payload["counts"]["frontier_candidates"], 2)
        self.assertEqual(payload["selection"]["sort"], "reach")

    def test_plan_is_blocked_by_dangling_dependency(self) -> None:
        tex = r"""
\begin{theorem}\label{thm:goal}\uses{lem:missing}\end{theorem}
"""
        analysis = bs.analyse(bs.parse_blueprint(tex))
        output = bs.format_plan("thm:goal", analysis, bs.PlannerConfig())
        self.assertIn("blocked by missing dependency labels", output)
        self.assertIn("lem:missing", output)
        self.assertEqual(bs.plan_dangling("thm:goal", analysis, bs.PlannerConfig()), {"lem:missing"})

    def test_allow_dangling_plan_returns_error_and_prints_warning(self) -> None:
        tex = r"""
\begin{theorem}\label{thm:goal}\uses{lem:missing}\end{theorem}
"""
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "content.tex"
            path.write_text(tex, encoding="utf-8")
            stdout = io.StringIO()
            stderr = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                result = bs.main(
                    [
                        "--tex",
                        str(path),
                        "--config",
                        str(Path(tmp) / "missing.toml"),
                        "--allow-dangling",
                        "--goal",
                        "",
                        "--plan",
                        "thm:goal",
                    ]
                )
        self.assertEqual(result, 2)
        self.assertIn("blocked by missing dependency labels", stdout.getvalue())
        self.assertIn("dangling-use", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
