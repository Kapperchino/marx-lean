#!/usr/bin/env python3
"""Export the conventional article using local KaTeX and macOS CoreText.

The .tex file is also a standalone LaTeX source. This exporter supports the
small article subset used there and fails on unrecognized markup.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
WORK = ROOT / ".tools" / "paper"
SOURCE = ROOT / "research_context_mathematical_paper.tex"


def parse_article(source):
    body = source.split(r"\maketitle", 1)[1].split(r"\end{document}", 1)[0]
    title = re.search(r"\\title\{([^{}]+)\}", source)
    date = re.search(r"\\date\{([^{}]*)\}", source)
    if not title or not date:
        raise ValueError("The article needs a plain-text title and date.")
    title_lines = re.split(r"\\\\(?:\[[^\]]*\])?", title.group(1))
    title_lines = [line.replace(r"\large", "").strip() for line in title_lines]
    blocks = [
        {"kind": "title", "text": title_lines[0]},
        {"kind": "subtitle", "text": "\n".join(title_lines[1:])},
        {"kind": "date", "text": date.group(1)},
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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", nargs="?", type=Path, default=SOURCE)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    source_path = args.source.resolve()
    output = args.output.resolve() if args.output else source_path.with_suffix(".pdf")
    work = WORK if source_path == SOURCE else WORK / source_path.stem
    work.mkdir(parents=True, exist_ok=True)
    source = source_path.read_text()
    payload = {"blocks": parse_article(source), "sourceSHA256": hashlib.sha256(source.encode()).hexdigest()}
    input_path = work / "article.json"
    input_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2))
    subprocess.run(["node", str(ROOT / "scripts/paper_mathml.js"), str(input_path)], check=True)
    subprocess.run([
        "swift", "-module-cache-path", str(WORK / "swift-cache"),
        str(ROOT / "scripts/render_paper.swift"), str(input_path), str(output), str(work)
    ], check=True, cwd=ROOT)
    print(f"Created {output}")


if __name__ == "__main__":
    main()
