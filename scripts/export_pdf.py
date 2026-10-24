#!/usr/bin/env python3
"""Build, snapshot, and typeset the proof with native macOS PDF frameworks."""
from __future__ import annotations

import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
WORK = ROOT / ".tools" / "pdf"
OUTPUT = ROOT / "research_context_lean_proof.pdf"
ORDER = [
    ("Basic", "Production and unique labor accounts"),
    ("Productivity", "Neumann series and positive witnesses"),
    ("Spectral", "Spectral productivity criteria"),
    ("Accounting", "Projects, inventories, and boundaries"),
    ("Capabilities", "Boolean and missing-project closures"),
    ("Support", "Inverse entries and graph reachability"),
    ("BooleanBoundary", "Exact Boolean boundary elimination"),
    ("Conversion", "Normalized labor-type conversion"),
    ("Units", "Physical and occupational unit changes"),
    ("Blocks", "Terminal activities and block systems"),
    ("Sensitivity", "Differentiability and error bounds"),
    ("Truncation", "Certified Neumann truncation"),
    ("Theorems", "Combined spectral and conversion results"),
    ("Model", "Contexts and the unified specification"),
    ("Examples", "Exact examples and counterexamples"),
    ("Audit", "Transitive axiom dependency audit"),
]


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    WORK.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env["PATH"] = str(Path.home() / ".elan" / "bin") + os.pathsep + env["PATH"]
    paths = [ROOT / "MarxLeanProof.lean"] + [ROOT / "MarxLeanProof" / f"{n}.lean" for n, _ in ORDER]
    actual = {p.resolve() for p in (ROOT / "MarxLeanProof").glob("*.lean")}
    if actual != set(paths[1:]):
        raise SystemExit("The PDF module order must include every Lean source module.")
    snapshots = {p: p.read_bytes() for p in paths}
    built = subprocess.run(
        ["lake", "--wfail", "build"], cwd=ROOT, env=env,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    (WORK / "build.log").write_text(built.stdout)
    if built.returncode:
        raise SystemExit("Lean verification failed. See .tools/pdf/build.log")
    if any(p.read_bytes() != data for p, data in snapshots.items()):
        raise SystemExit("Source changed during verification; retry the export.")
    audit = re.search(r"Axiom audit passed: (\d+) project declarations", built.stdout)
    if not audit:
        raise SystemExit("The successful axiom audit was not present in the build output.")
    titles = {"MarxLeanProof.lean": "Library entry point"}
    titles.update({f"MarxLeanProof/{n}.lean": t for n, t in ORDER})
    sources = []
    for p, data in snapshots.items():
        path = p.relative_to(ROOT).as_posix()
        sources.append({"path": path, "title": titles[path], "text": data.decode(), "sha256": sha(data)})
    count = sum(len(re.findall(r"^(?:theorem|lemma)\s+", s["text"], re.M)) for s in sources)
    bundle_hash = sha(b"".join(p.relative_to(ROOT).as_posix().encode() + b"\0" + snapshots[p] + b"\0" for p in paths))
    config = []
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        data = (ROOT / name).read_bytes()
        config.append({"path": name, "title": "Reproducible project configuration", "text": data.decode(), "sha256": sha(data)})
    payload = {
        "title": "Research as Production Context",
        "date": datetime.datetime.now(datetime.timezone.utc).strftime("%d %B %Y (UTC)"),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "statementCount": count,
        "auditCount": int(audit.group(1)),
        "lineCount": sum(len(s["text"].splitlines()) for s in sources),
        "bundleHash": bundle_hash,
        "paperHash": sha((ROOT / "research_context_formula_audited.pdf").read_bytes()),
        "readme": (ROOT / "README.md").read_text(),
        "sources": sources,
        "config": config,
    }
    data_path = WORK / "input.json"
    data_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2))
    subprocess.run([
        "swift", "-module-cache-path", str(WORK / "swift-cache"),
        str(ROOT / "scripts" / "render_pdf.swift"), str(data_path), str(OUTPUT), str(WORK),
    ], cwd=ROOT, env=env, check=True)
    print(f"Created {OUTPUT.name}: {count} theorems/lemmas, {len(sources)} Lean source files.")


if __name__ == "__main__":
    main()
