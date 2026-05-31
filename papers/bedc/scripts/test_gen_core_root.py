from __future__ import annotations

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import gen_core_root


MAIN_BODY = "\n".join(
    [
        r"\documentclass{book}",
        r"\input{preamble.tex}",
        r"\begin{document}",
        r"\frontmatter",
        r"\tableofcontents",
        r"\mainmatter",
        r"\part{Finite Kernel Theory}",
        r"\input{parts/core.tex}",
        r"\part{Concrete Instances}",
        r"\input{parts/concrete_instances/a.tex}",
        r"\input{parts/concrete_instances/b.tex}",
        r"\input{parts/concrete_instances/c.tex}",
        r"\part{Concrete Hardening}",
        r"\input{parts/concrete_hardening.tex}",
        r"\part{Appendices}",
        r"\input{appendices/lean_scaffold.tex}",
        r"\end{document}",
    ]
)


class GenCoreRootTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name) / "papers" / "bedc"
        self.root.mkdir(parents=True)
        (self.root / "main.tex").write_text(MAIN_BODY + "\n", encoding="utf-8")

        self.old_values = {
            "ROOT": gen_core_root.ROOT,
            "MAIN": gen_core_root.MAIN,
            "CORE": gen_core_root.CORE,
            "DERIVED_DIR": gen_core_root.DERIVED_DIR,
            "DERIVED_ROOT": gen_core_root.DERIVED_ROOT,
            "MANIFEST_CHUNK_SIZE": gen_core_root.MANIFEST_CHUNK_SIZE,
            "MAX_TEX_LINES": gen_core_root.MAX_TEX_LINES,
        }
        gen_core_root.ROOT = self.root
        gen_core_root.MAIN = self.root / "main.tex"
        gen_core_root.CORE = self.root / "main_core.tex"
        gen_core_root.DERIVED_DIR = self.root / "derived"
        gen_core_root.DERIVED_ROOT = gen_core_root.DERIVED_DIR / "concrete_instances.tex"
        gen_core_root.MANIFEST_CHUNK_SIZE = 3
        gen_core_root.MAX_TEX_LINES = 24

    def tearDown(self) -> None:
        for name, value in self.old_values.items():
            setattr(gen_core_root, name, value)
        self.tmp.cleanup()

    def run_main(self, *args: str) -> int:
        old_argv = sys.argv
        sys.argv = ["gen_core_root.py", *args]
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                return gen_core_root.main()
        finally:
            sys.argv = old_argv

    def test_read_main_shape_preserves_order_and_suffix(self) -> None:
        shape = gen_core_root.read_main_shape()

        self.assertEqual(
            [part.title for part in shape.parts],
            [
                "Finite Kernel Theory",
                "Concrete Instances",
                "Concrete Hardening",
                "Appendices",
            ],
        )
        self.assertEqual(shape.suffix, [r"\end{document}"])

    def test_core_and_derived_partition_route_selected_parts(self) -> None:
        shape = gen_core_root.read_main_shape()
        core_text = "\n".join(gen_core_root.core_lines(shape))
        manifest_text = "\n".join(line for block in gen_core_root.manifest_blocks(shape) for line in block)

        self.assertIn(r"\part{Finite Kernel Theory}", core_text)
        self.assertIn(r"\part{Appendices}", core_text)
        self.assertNotIn(r"\part{Concrete Instances}", core_text)
        self.assertNotIn(r"\part{Concrete Hardening}", core_text)
        self.assertIn(r"\part{Concrete Instances}", manifest_text)
        self.assertIn(r"\part{Concrete Hardening}", manifest_text)
        self.assertNotIn(r"\part{Finite Kernel Theory}", manifest_text)

    def test_manifest_chunks_are_numbered_and_validated_under_line_cap(self) -> None:
        shape = gen_core_root.read_main_shape()
        blocks = gen_core_root.manifest_blocks(shape)
        paths = gen_core_root.manifest_paths(blocks)

        self.assertEqual(
            [path.name for path in paths],
            ["concrete_instances_inputs_01.tex", "concrete_instances_inputs_02.tex"],
        )
        for path, lines in zip(paths, blocks, strict=True):
            candidate = [*gen_core_root.banner(), *lines]
            self.assertLessEqual(len(candidate), gen_core_root.MAX_TEX_LINES)
            gen_core_root.validate(path, candidate)

    def test_validation_rejects_files_over_line_cap(self) -> None:
        lines = [r"\input{parts/core.tex}"] * (gen_core_root.MAX_TEX_LINES + 1)

        with self.assertRaises(SystemExit) as raised:
            gen_core_root.validate(gen_core_root.CORE, lines)

        self.assertIn("cap 24", str(raised.exception))

    def test_missing_derived_part_fails_with_clear_message(self) -> None:
        (self.root / "main.tex").write_text(
            MAIN_BODY.replace(
                r"\part{Concrete Hardening}" + "\n" + r"\input{parts/concrete_hardening.tex}" + "\n",
                "",
            )
            + "\n",
            encoding="utf-8",
        )

        with self.assertRaises(SystemExit) as raised:
            self.run_main("--check")

        self.assertIn("missing derived part(s): Concrete Hardening", str(raised.exception))

    def test_check_mode_writes_nothing_and_keeps_existing_manifest(self) -> None:
        gen_core_root.DERIVED_DIR.mkdir()
        stale = gen_core_root.DERIVED_DIR / "concrete_instances_inputs_99.tex"
        stale.write_text("old\n", encoding="utf-8")

        self.assertEqual(self.run_main("--check"), 0)

        self.assertFalse(gen_core_root.CORE.exists())
        self.assertFalse(gen_core_root.DERIVED_ROOT.exists())
        self.assertEqual(stale.read_text(encoding="utf-8"), "old\n")

    def test_generation_removes_stale_manifest_and_writes_current_roots(self) -> None:
        gen_core_root.DERIVED_DIR.mkdir()
        stale = gen_core_root.DERIVED_DIR / "concrete_instances_inputs_99.tex"
        stale.write_text("old\n", encoding="utf-8")

        self.assertEqual(self.run_main(), 0)

        self.assertFalse(stale.exists())
        self.assertTrue(gen_core_root.CORE.exists())
        self.assertTrue(gen_core_root.DERIVED_ROOT.exists())
        self.assertTrue((gen_core_root.DERIVED_DIR / "concrete_instances_inputs_01.tex").exists())
        self.assertTrue((gen_core_root.DERIVED_DIR / "concrete_instances_inputs_02.tex").exists())


if __name__ == "__main__":
    unittest.main()
