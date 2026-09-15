#!/usr/bin/env python3
"""Run the frozen NCT graph scripts from yaddag; cache the checkout in .lake."""

import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "https://github.com/roos-j/yaddag.git"
SCRIPTS = {
    "extract": "latex_to_graph_json.py",
    "render": "graph_json_to_html.py",
}


def main() -> int:
    if len(sys.argv) < 2 or sys.argv[1] not in SCRIPTS:
        print("usage: python dependency_graph/run_yaddag.py {extract,render} [arguments...]", file=sys.stderr)
        return 2
    revision = (ROOT / "dependency_graph/yaddag-revision.txt").read_text().strip()
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        print("error: yaddag-revision.txt must contain a full commit SHA", file=sys.stderr)
        return 2
    checkout = ROOT / ".lake/yaddag" / revision
    try:
        if not (checkout / ".git").exists():
            checkout.mkdir(parents=True, exist_ok=True)
            subprocess.run(["git", "init", "--quiet", str(checkout)], check=True)
        available = subprocess.run(
            ["git", "-C", str(checkout), "rev-parse", "--verify", "HEAD"],
            capture_output=True, text=True,
        )
        if available.returncode != 0 or available.stdout.strip() != revision:
            subprocess.run(["git", "-C", str(checkout), "fetch", "--depth=1", REPOSITORY, revision], check=True)
            subprocess.run(["git", "-C", str(checkout), "checkout", "--detach", revision], check=True)
        return subprocess.run([
            sys.executable, str(checkout / "dependency_graph" / SCRIPTS[sys.argv[1]]),
            *sys.argv[2:],
        ]).returncode
    except (OSError, subprocess.CalledProcessError) as exc:
        print(f"error: cannot run pinned yaddag: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
