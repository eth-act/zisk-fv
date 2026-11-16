import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import faithfulness


class ExtractorSelectionTests(unittest.TestCase):
    def test_existing_debug_cli_cannot_bypass_current_source_build(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            stale = root / "tools/pil-extract/target/debug/pil-extract"
            stale.parent.mkdir(parents=True)
            stale.write_text("#!/bin/sh\nexit 99\n")
            stale.chmod(0o755)
            with patch.object(faithfulness, "ROOT", root), patch.dict(os.environ):
                os.environ.pop("PIL_EXTRACT", None)
                self.assertEqual(faithfulness.extractor_command(), [
                    "cargo", "run", "--quiet", "--manifest-path",
                    str(root / "tools/pil-extract/Cargo.toml"), "--",
                ])

    def test_explicit_extractor_is_retained(self):
        with patch.dict(os.environ, {"PIL_EXTRACT": "/immutable/extractor"}):
            self.assertEqual(faithfulness.extractor_command(), ["/immutable/extractor"])


if __name__ == "__main__":
    unittest.main()
