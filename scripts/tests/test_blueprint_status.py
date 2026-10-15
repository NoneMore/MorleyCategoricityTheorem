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

    def test_commented_proof_end_does_not_truncate_uses(self) -> None:
        tex = r"""
\begin{lemma}[A]\label{lem:a}\end{lemma}
\begin{proof}
% \end{proof}
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

    def test_unlabelled_nodes_are_reported(self) -> None:
        tex = r"""
\begin{lemma}[Missing]\uses{lem:a}\end{lemma}
\begin{lemma}\label{   }\end{lemma}
\begin{lemma}\label{lem:a}\leanok\end{lemma}
"""
        diagnostics = bs.validate_source(tex)
        self.assertEqual([item.code for item in diagnostics], ["missing-label", "missing-label"])
        self.assertEqual([item.line for item in diagnostics], [2, 3])
        self.assertEqual([node.label for node in bs.parse_blueprint(tex)], ["lem:a"])

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

    def test_goal_metrics_are_structural_only(self) -> None:
        tex = r"""
\begin{lemma}\label{lem:done}\leanok\end{lemma}
\begin{lemma}\label{lem:a}\uses{lem:done}\end{lemma}
\begin{theorem}\label{thm:goal}\uses{lem:a}\end{theorem}
"""
        analysis = bs.analyse(bs.parse_blueprint(tex))
        metrics = bs.compute_metrics(analysis, "thm:goal")
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
        analysis = bs.analyse(bs.parse_blueprint(tex))
        rows = bs.milestone_rows(analysis, {"demo": "thm:goal"})
        self.assertEqual(rows[0], ("demo", "thm:goal", "1", "2", "1"))

    def test_builtin_milestone_alias_matches_blueprint_architecture(self) -> None:
        self.assertEqual(
            bs.MILESTONES["no_vaughtian_pairs"],
            "thm:uncountable-categoricity-no-vaughtian-pairs",
        )

    def test_json_respects_goal_restriction_and_top(self) -> None:
        tex = r"""
\begin{lemma}\label{lem:a}\end{lemma}
\begin{lemma}\label{lem:b}\end{lemma}
\begin{lemma}\label{lem:off-goal}\end{lemma}
\begin{lemma}\label{lem:a-child}\uses{lem:a}\end{lemma}
\begin{theorem}\label{thm:goal}\uses{lem:a-child,lem:b}\end{theorem}
"""
        analysis = bs.analyse(bs.parse_blueprint(tex))
        metrics = bs.compute_metrics(analysis, "thm:goal")
        payload = json.loads(
            bs.format_json(
                analysis,
                metrics,
                Path("demo.tex"),
                "thm:goal",
                top=1,
                restrict_to_goal=True,
            )
        )
        self.assertEqual([item["label"] for item in payload["priority"]], ["lem:a"])
        self.assertEqual([item["label"] for item in payload["frontier"]], ["lem:a"])
        self.assertEqual(payload["counts"]["frontier"], 1)
        self.assertEqual(payload["counts"]["frontier_candidates"], 2)

    def test_custom_tex_does_not_require_repository_milestones(self) -> None:
        tex = r"""
\begin{theorem}\label{thm:goal}\end{theorem}
"""
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "content.tex"
            path.write_text(tex, encoding="utf-8")
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                result = bs.main(["--tex", str(path), "--all"])
        self.assertEqual(result, 0)

    def test_why_custom_tex_does_not_require_default_goal(self) -> None:
        tex = r"""
\begin{theorem}\label{thm:goal}\end{theorem}
"""
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "content.tex"
            path.write_text(tex, encoding="utf-8")
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                result = bs.main(["--tex", str(path), "--why", "thm:goal"])
        self.assertEqual(result, 0)
        self.assertIn("Why thm:goal?", stdout.getvalue())

    def test_conflicting_cli_modes_are_rejected(self) -> None:
        for argv in (
            ["--json", "--why", "thm:goal"],
            ["--goal", "thm:goal", "--milestone", "morley"],
            ["--milestones", "--milestone", "morley"],
            ["--why", "thm:goal", "--top", "1"],
            ["--all", "--top", "1"],
            ["--all", "--json"],
        ):
            with self.subTest(argv=argv):
                with contextlib.redirect_stderr(io.StringIO()):
                    with self.assertRaises(SystemExit) as error:
                        bs.main(argv)
                self.assertEqual(error.exception.code, 2)

    def test_help_describes_goal_aware_options(self) -> None:
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            with self.assertRaises(SystemExit) as error:
                bs.main(["--help"])
        self.assertEqual(error.exception.code, 0)
        help_text = stdout.getvalue()
        self.assertIn("restrict the frontier to a named milestone path", help_text)
        self.assertIn("show at most N ranked frontier nodes", help_text)
        self.assertIn("allow missing dependency labels", help_text)

    def test_allow_dangling_is_an_explicit_escape_hatch(self) -> None:
        tex = r"""
\begin{theorem}\label{thm:goal}\uses{lem:missing}\end{theorem}
"""
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "content.tex"
            path.write_text(tex, encoding="utf-8")
            stdout = io.StringIO()
            stderr = io.StringIO()
            with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
                original = bs.MILESTONES
                bs.MILESTONES = {"morley": "thm:goal"}
                try:
                    result = bs.main(
                        [
                            "--tex",
                            str(path),
                            "--allow-dangling",
                            "--goal",
                            "",
                            "--all",
                        ]
                    )
                finally:
                    bs.MILESTONES = original
        self.assertEqual(result, 0)
        self.assertIn("dangling-use", stderr.getvalue())
        self.assertNotIn("graph validation passed", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
