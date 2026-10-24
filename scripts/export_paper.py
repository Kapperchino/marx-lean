#!/usr/bin/env python3
"""Export the conventional article using local KaTeX and macOS CoreText.

The .tex file is also a standalone LaTeX source. This exporter supports the
small article subset used there and fails on unrecognized markup.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
WORK = ROOT / ".tools" / "paper"
SOURCE = ROOT / "research_context_mathematical_paper.tex"
OUTPUT = ROOT / "research_context_mathematical_paper.pdf"


def parse_article(source):
    body = source.split(r"\maketitle", 1)[1].split(r"\end{document}", 1)[0]
    blocks = [
        {"kind": "title", "text": "Research as Production Context"},
        {"kind": "subtitle", "text": "Conditional labor requirements, reusable capabilities,\nand normalized occupational conversion"},
        {"kind": "date", "text": "24 October 2026"},
    ]
    token = re.compile(
        r"\\begin\{equation\}(.*?)\\end\{equation\}"
        r"|\\section\{([^{}]+)\}"
        r"|\\begin\{(theorem|proposition|corollary|definition|example)\}(?:\[([^\]]+)\])?"
        r"|\\end\{(?:theorem|proposition|corollary|definition|example)\}"
        r"|\\(begin|end)\{(abstract|proof)\}", re.S)
    section = statement = equation = 0
    abstract = False

    def prose(text):
        for para in re.split(r"\n\s*\n", text.strip()):
            if not para.strip():
                continue
            para = " ".join(para.split())
            # Commands outside math would require explicit support here.
            for part in re.split(r"\$[^$]*\$", para):
                if "\\" in part or "{" in part or "}" in part:
                    raise ValueError(f"Unsupported prose markup: {part}")
            blocks.append({"kind": "abstract" if abstract else "paragraph", "text": para})

    last = 0
    for match in token.finditer(body):
        prose(body[last:match.start()])
        eq, heading, env, name, edge, simple = match.groups()
        if eq is not None:
            equation += 1
            blocks.append({"kind": "equation", "text": eq.strip(), "number": str(equation)})
        elif heading is not None:
            section += 1
            statement = 0
            blocks.append({"kind": "section", "text": f"{section}. {heading}"})
        elif env:
            statement += 1
            label = f"{env.capitalize()} {section}.{statement}"
            if name:
                label += f" ({name})"
            blocks.append({"kind": "statement", "text": label + "."})
        elif simple == "abstract":
            abstract = edge == "begin"
            if abstract:
                blocks.append({"kind": "abstract_heading", "text": "Abstract"})
        elif simple == "proof":
            blocks.append({"kind": "proof" if edge == "begin" else "qed", "text": "Proof." if edge == "begin" else "□"})
        last = match.end()
    prose(body[last:])
    return blocks


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    source = SOURCE.read_text()
    payload = {"blocks": parse_article(source), "sourceSHA256": hashlib.sha256(source.encode()).hexdigest()}
    input_path = WORK / "article.json"
    input_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2))
    subprocess.run(["node", str(ROOT / "scripts/paper_mathml.js"), str(input_path)], check=True)
    subprocess.run([
        "swift", "-module-cache-path", str(WORK / "swift-cache"),
        str(ROOT / "scripts/render_paper.swift"), str(input_path), str(OUTPUT), str(WORK)
    ], check=True, cwd=ROOT)
    print(f"Created {OUTPUT}")


if __name__ == "__main__":
    main()
