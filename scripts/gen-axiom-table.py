#!/usr/bin/env python3
"""Emit the axiom-table HTML fragment for the OpenCSV formal page from the
CI baseline `axiom-audit.txt` (lines like

    'OpenCsv.theorem_name' depends on axioms: [a, b, c]

produced by scripts/axiom-audit.sh from the Lean build's `#print axioms`
output).

Dependency-free (python3 stdlib only), deterministic, no network. The Lean
toolchain is NOT required: the baseline is checked in. Pass --rebuild to
refresh it from the build first (scripts/axiom-audit.sh --write; needs
elan/lake).

Usage:
  gen-axiom-table.py [--input axiom-audit.txt] [--output fragment.html]
                     [--rebuild]
Defaults: --input <repo>/axiom-audit.txt (repo = the script's parent
directory), output to stdout.
"""

import argparse
import html
import re
import subprocess
import sys
from pathlib import Path

LINE_RE = re.compile(r"^'([^']+)' depends on axioms: \[(.*)\]$")
LINE_NONE_RE = re.compile(r"^'([^']+)' does not depend on any axioms$")


def git(repo, *args):
    """Best-effort git query; '' on any failure (not a repo, no git)."""
    try:
        return subprocess.run(
            ["git", "-C", str(repo), *args],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return ""


def parse_audit(text):
    """[(theorem, [axiom, ...])] in file order; fails loudly on bad lines."""
    theorems = []
    for n, line in enumerate(text.splitlines(), 1):
        line = line.strip()
        if not line:
            continue
        m = LINE_RE.match(line)
        if m:
            axioms = [a.strip() for a in m.group(2).split(",") if a.strip()]
            theorems.append((m.group(1), axioms))
            continue
        m = LINE_NONE_RE.match(line)
        if m:
            theorems.append((m.group(1), []))
            continue
        sys.exit(f"error: axiom-audit line {n} is malformed: {line!r}")
    if not theorems:
        sys.exit("error: no theorems found in the audit file")
    return theorems


def render(theorems, audited, sha):
    def code(s):
        return f"<code>{html.escape(s)}</code>"

    out = ["<table>",
           "  <thead><tr><th>Theorem</th><th>Axiom dependencies</th></tr></thead>",
           "  <tbody>"]
    for name, axioms in theorems:
        deps = ", ".join(code(a) for a in axioms) if axioms else "<em>none</em>"
        out.append(f"    <tr><td>{code(name)}</td><td>{deps}</td></tr>")
    out += ["  </tbody>", "</table>"]
    stamp = f" @ {sha}" if sha else ""
    out.append(
        f'<p class="gen-summary">{len(theorems)} theorems, audited {audited} '
        f"from <code>axiom-audit.txt</code>{stamp}</p>"
    )
    return "\n".join(out)


def main():
    repo = Path(__file__).resolve().parent.parent
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--input", default=str(repo / "axiom-audit.txt"),
                    help="audit baseline (default: <repo>/axiom-audit.txt)")
    ap.add_argument("--output", help="HTML fragment path (default: stdout)")
    ap.add_argument("--rebuild", action="store_true",
                    help="regenerate the baseline from the Lean build first "
                         "(scripts/axiom-audit.sh --write; needs elan/lake)")
    args = ap.parse_args()

    audit_path = Path(args.input)
    if args.rebuild:
        subprocess.run(
            ["bash", str(repo / "scripts" / "axiom-audit.sh"), "--write"],
            cwd=repo, check=True,
        )

    theorems = parse_audit(audit_path.read_text())
    # Deterministic stamps: the baseline's last commit date / HEAD sha,
    # falling back to file mtime when outside a checkout.
    audited = git(repo, "log", "-1", "--format=%cs", "--", str(audit_path))
    if not audited:
        import datetime

        audited = datetime.datetime.fromtimestamp(
            audit_path.stat().st_mtime, tz=datetime.timezone.utc
        ).strftime("%Y-%m-%d")
    sha = git(repo, "rev-parse", "--short", "HEAD")

    fragment = render(theorems, audited, sha)
    if args.output:
        Path(args.output).write_text(fragment + "\n")
        print(f"wrote {args.output}", file=sys.stderr)
    else:
        print(fragment)


if __name__ == "__main__":
    main()
