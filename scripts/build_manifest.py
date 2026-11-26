"""Build or verify MANIFEST.sha256 for EX-K3-C5-CERT-1.0."""

from __future__ import annotations

import hashlib
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

TRACKED_GLOBS = [
    "CITATION.cff",
    "LICENSE",
    "README.md",
    "lean/lean-toolchain",
    "lean/lakefile.toml",
    "lean/TrianglesNoPentagonsCert.lean",
    "src/__init__.py",
    "src/ex_k3_c5_verifier.py",
    "scripts/generate_certificates.py",
    "scripts/generate_figures.py",
    "scripts/build_manifest.py",
    "tests/test_verifier.py",
    "paper/main.tex",
    "paper/references.bib",
    "paper/main.pdf",
    "paper/figures/*.pdf",
    "paper/figures/*.png",
    "certificates/*.json",
]


def _collect_files() -> list[pathlib.Path]:
    found: set[pathlib.Path] = set()
    for pat in TRACKED_GLOBS:
        for p in ROOT.glob(pat):
            if p.is_file():
                found.add(p)
    return sorted(found, key=lambda p: p.relative_to(ROOT).as_posix())


def _sha256(p: pathlib.Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main() -> int:
    manifest = ROOT / "MANIFEST.sha256"
    if "--check" in sys.argv:
        lines = [ln.strip() for ln in manifest.read_text(encoding="utf-8").splitlines() if ln.strip()]
        ok = 0
        for ln in lines:
            digest, rel = ln.split("  ", 1)
            p = ROOT / rel
            if not p.is_file():
                print(f"MISSING: {rel}", file=sys.stderr)
                return 1
            actual = _sha256(p)
            if actual != digest:
                print(f"MISMATCH: {rel}", file=sys.stderr)
                return 1
            ok += 1
        print(f"MANIFEST.sha256 OK: {ok}/{len(lines)} files match.")
        return 0

    files = _collect_files()
    out_lines = [f"{_sha256(p)}  {p.relative_to(ROOT).as_posix()}" for p in files]
    manifest.write_text("\n".join(out_lines) + "\n", encoding="utf-8", newline="\n")
    print(f"Wrote MANIFEST.sha256 with {len(out_lines)} files.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
