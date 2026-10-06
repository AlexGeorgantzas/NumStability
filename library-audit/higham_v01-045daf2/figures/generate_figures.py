#!/usr/bin/env python3
"""Generate dependency figures using only the Python standard library.

Schema: numstability-audit-figures/1.0.0
All arrows use the audit contract's consumer -> dependency orientation.
"""

from __future__ import annotations

import csv
import hashlib
import json
import math
import re
from pathlib import Path
from xml.sax.saxutils import escape


AUDIT_ROOT = Path(__file__).resolve().parents[1]
METRICS = AUDIT_ROOT / "current_graph" / "metrics"
CHAINS = AUDIT_ROOT / "current_graph" / "chains"
OUT = AUDIT_ROOT / "figures"
COMMIT = "045daf28056a6e4358d5de7c22c7a9d7acc2e80e"
ORIENTATION = "consumer → dependency"


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def svg_header(width: int, height: int, title: str, desc: str) -> list[str]:
    return [
        '<?xml version="1.0" encoding="UTF-8"?>',
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img" aria-labelledby="title desc">',
        f"<title id=\"title\">{escape(title)}</title>",
        f"<desc id=\"desc\">{escape(desc)}</desc>",
        "<defs>",
        '<marker id="arrow-blue" markerWidth="10" markerHeight="10" refX="9" refY="3" orient="auto" markerUnits="strokeWidth"><path d="M0,0 L0,6 L9,3 z" fill="#2463A5"/></marker>',
        '<marker id="arrow-green" markerWidth="10" markerHeight="10" refX="9" refY="3" orient="auto" markerUnits="strokeWidth"><path d="M0,0 L0,6 L9,3 z" fill="#21835A"/></marker>',
        '<marker id="arrow-red" markerWidth="10" markerHeight="10" refX="9" refY="3" orient="auto" markerUnits="strokeWidth"><path d="M0,0 L0,6 L9,3 z" fill="#B43A3A"/></marker>',
        '<linearGradient id="heat" x1="0" x2="1"><stop offset="0%" stop-color="#F7FBFF"/><stop offset="45%" stop-color="#9ECAE1"/><stop offset="100%" stop-color="#084594"/></linearGradient>',
        "</defs>",
        f'<rect x="0" y="0" width="{width}" height="{height}" fill="#FFFFFF"/>',
        '<g font-family="Inter, Helvetica, Arial, sans-serif" fill="#172433">',
    ]


def svg_footer() -> list[str]:
    return ["</g>", "</svg>"]


def label(lines: list[str], x: float, y: float, parts: list[str], *, size: int = 18,
          weight: int = 400, anchor: str = "middle", color: str = "#172433",
          leading: int | None = None) -> None:
    leading = leading or int(size * 1.25)
    for index, part in enumerate(parts):
        line_y = y + index * leading
        lines.append(
            f'<text x="{x}" y="{line_y}" text-anchor="{anchor}" font-size="{size}" '
            f'font-weight="{weight}" fill="{color}">{escape(part)}</text>'
        )


def wrap_identifier(text: str, width: int = 58) -> list[str]:
    chunks = re.split(r"(?<=[._])", text)
    lines: list[str] = []
    current = ""
    for chunk in chunks:
        if current and len(current) + len(chunk) > width:
            lines.append(current.rstrip("."))
            current = chunk.lstrip(".")
        else:
            current += chunk
    if current:
        lines.append(current.rstrip("."))
    return lines or [text]


def number_short(value: int) -> str:
    if value >= 100_000:
        return f"{value / 1000:.0f}k"
    if value >= 10_000:
        return f"{value / 1000:.1f}k"
    if value >= 1_000:
        return f"{value / 1000:.1f}k"
    return str(value)


def heat_color(value: int, maximum: int) -> tuple[str, str]:
    if value <= 0:
        return "#FFFFFF", "#6B7785"
    t = math.log10(value + 1) / math.log10(maximum + 1)
    stops = [(247, 251, 255), (158, 202, 225), (8, 69, 148)]
    if t <= 0.45:
        u = t / 0.45
        a, b = stops[0], stops[1]
    else:
        u = (t - 0.45) / 0.55
        a, b = stops[1], stops[2]
    rgb = tuple(round(a[i] + (b[i] - a[i]) * u) for i in range(3))
    fill = "#" + "".join(f"{component:02X}" for component in rgb)
    return fill, "#FFFFFF" if t > 0.68 else "#172433"


def generate_layer_diagram() -> Path:
    source = METRICS / "layer_dependency_matrix.csv"
    rows = read_csv(source)
    edges = {(r["consumer_category"], r["dependency_category"]): int(r["unique_declaration_pairs"]) for r in rows}
    inventory = {
        "Examples": 0,
        "Source": 48663,
        "Algorithms": 13775,
        "Analysis": 14414,
        "FloatingPoint": 140,
    }
    internal = {layer: edges.get((layer, layer), 0) for layer in inventory}
    width, height = 2100, 1180
    lines = svg_header(
        width,
        height,
        "NumStability elaborated layer-dependency architecture",
        "Unique declaration-pair edges at the audited commit. Arrows point from consuming declarations to referenced declarations.",
    )
    label(lines, width / 2, 64, ["NumStability elaborated layer dependencies"], size=34, weight=700)
    label(lines, width / 2, 102, [f"Commit {COMMIT[:12]} · {ORIENTATION} · unique project declaration pairs"], size=18, color="#536273")

    xs = {"Examples": 70, "Source": 450, "Algorithms": 830, "Analysis": 1210, "FloatingPoint": 1590}
    box_y, box_w, box_h = 270, 290, 142
    colors = {
        "Examples": ("#F4F5F7", "#99A2AD"),
        "Source": ("#FFF2CC", "#C89B2C"),
        "Algorithms": ("#DDF3E7", "#26855B"),
        "Analysis": ("#DCEBFA", "#2463A5"),
        "FloatingPoint": ("#E8E0F6", "#6E4FA3"),
    }
    for layer, x in xs.items():
        fill, stroke = colors[layer]
        dash = ' stroke-dasharray="9 7"' if layer == "Examples" else ""
        lines.append(f'<rect x="{x}" y="{box_y}" width="{box_w}" height="{box_h}" rx="18" fill="{fill}" stroke="{stroke}" stroke-width="3"{dash}/>')
        label(lines, x + box_w / 2, box_y + 42, [layer], size=24, weight=700)
        note = "not present as a layer" if layer == "Examples" else f"{inventory[layer]:,} declarations"
        label(lines, x + box_w / 2, box_y + 78, [note], size=16, color="#44515F")
        label(lines, x + box_w / 2, box_y + 108, [f"{internal[layer]:,} within-layer edges"], size=15, color="#44515F")

    expected_adjacent = [("Examples", "Source", None), ("Source", "Algorithms", 49424), ("Algorithms", "Analysis", 13507), ("Analysis", "FloatingPoint", 4128)]
    for consumer, dependency, value in expected_adjacent:
        x1 = xs[consumer] + box_w
        x2 = xs[dependency]
        y = box_y + box_h / 2
        dashed = ' stroke-dasharray="8 7"' if value is None else ""
        lines.append(f'<line x1="{x1 + 8}" y1="{y}" x2="{x2 - 30}" y2="{y}" stroke="#21835A" stroke-width="5"{dashed}/>')
        lines.append(f'<polygon points="{x2 - 12},{y} {x2 - 34},{y - 12} {x2 - 34},{y + 12}" fill="#21835A"/>')
        text = "intended only" if value is None else f"{value:,}"
        label(lines, (x1 + x2) / 2, y - 18, [text], size=16, weight=650, color="#1D714F")

    label(lines, 70, 495, ["Additional edges in the intended direction"], size=22, weight=700, anchor="start")
    intended_skip = [("Source", "Analysis", 71085), ("Source", "FloatingPoint", 18562), ("Algorithms", "FloatingPoint", 4508)]
    for index, (a, b, value) in enumerate(intended_skip):
        x = 85 + index * 635
        lines.append(f'<rect x="{x}" y="535" width="580" height="85" rx="12" fill="#F1F8F4" stroke="#86BDA2"/>')
        label(lines, x + 290, 569, [f"{a} → {b}"], size=18, weight=650, color="#1D714F")
        label(lines, x + 290, 600, [f"{value:,} declaration-pair edges"], size=16, color="#44515F")

    label(lines, 70, 705, ["Residual edges against the intended direction"], size=22, weight=700, anchor="start", color="#9D2F2F")
    inversions = [("Algorithms", "Source", 1114), ("Analysis", "Algorithms", 13998), ("Analysis", "Source", 791), ("FloatingPoint", "Analysis", 146)]
    for index, (a, b, value) in enumerate(inversions):
        x = 70 + index * 500
        lines.append(f'<rect x="{x}" y="745" width="455" height="100" rx="12" fill="#FFF0F0" stroke="#D88989" stroke-width="2"/>')
        label(lines, x + 227.5, 784, [f"{a} → {b}"], size=18, weight=650, color="#9D2F2F")
        label(lines, x + 227.5, 817, [f"{value:,} declaration-pair edges"], size=16, color="#6E3A3A")

    notes = [
        "Counts combine type and body/proof references after deduplicating ordered declaration pairs.",
        "A red edge is an architectural review signal, not by itself a defect; generated/private ownership can create apparent inversions.",
        "The Root layer (254 declarations; 1 cross-layer edge Source → Root) is omitted for visual clarity.",
    ]
    lines.append('<rect x="70" y="915" width="1960" height="170" rx="14" fill="#F7F8FA" stroke="#CDD3DA"/>')
    for i, note in enumerate(notes):
        label(lines, 105, 958 + i * 38, [f"• {note}"], size=17, anchor="start", color="#44515F")
    label(lines, width - 70, height - 32, ["Raw data: current_graph/metrics/layer_dependency_matrix.csv"], size=14, anchor="end", color="#66717E")
    lines.extend(svg_footer())
    target = OUT / "layer_dependency_diagram.svg"
    target.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return target


def generate_domain_heatmap() -> Path:
    source = METRICS / "domain_dependency_matrix.csv"
    rows = read_csv(source)
    domains = sorted({r["consumer_category"] for r in rows} | {r["dependency_category"] for r in rows})
    values = {(r["consumer_category"], r["dependency_category"]): int(r["unique_declaration_pairs"]) for r in rows}
    maximum = max(values.values())
    cell = 67
    left, top, right, bottom = 380, 330, 95, 185
    width = left + cell * len(domains) + right
    height = top + cell * len(domains) + bottom
    lines = svg_header(
        width,
        height,
        "NumStability domain dependency heatmap",
        "Log-scaled unique declaration-pair counts. Rows consume columns; empty cells have no elaborated project declaration edge.",
    )
    label(lines, width / 2, 58, ["Domain-level elaborated dependency matrix"], size=34, weight=700)
    label(lines, width / 2, 98, [f"Rows consume columns ({ORIENTATION}); cell area is uniform, color is log10(count + 1)"], size=18, color="#536273")
    label(lines, left + cell * len(domains) / 2, 148, ["Dependency domain"], size=20, weight=650, color="#344454")
    axis_y = top + cell * len(domains) / 2
    lines.append(
        f'<text x="40" y="{axis_y}" transform="rotate(-90 40 {axis_y})" '
        'text-anchor="middle" font-size="20" font-weight="650" fill="#344454">Consumer domain</text>'
    )

    for index, domain in enumerate(domains):
        x = left + index * cell + cell / 2
        y = top - 18
        lines.append(f'<text x="{x}" y="{y}" font-size="13" font-weight="600" fill="#344454" text-anchor="start" transform="rotate(-55 {x} {y})">{escape(domain)}</text>')
        label(lines, left - 16, top + index * cell + 42, [domain], size=14, weight=550, anchor="end", color="#344454")

    for row_index, consumer in enumerate(domains):
        for col_index, dependency in enumerate(domains):
            value = values.get((consumer, dependency), 0)
            fill, text_color = heat_color(value, maximum)
            x = left + col_index * cell
            y = top + row_index * cell
            stroke = "#46596B" if consumer == dependency else "#D6DCE2"
            stroke_width = 1.8 if consumer == dependency else 0.75
            lines.append(f'<g><title>{escape(consumer)} → {escape(dependency)}: {value:,} unique declaration pairs</title>')
            lines.append(f'<rect x="{x}" y="{y}" width="{cell}" height="{cell}" fill="{fill}" stroke="{stroke}" stroke-width="{stroke_width}"/>')
            if value:
                label(lines, x + cell / 2, y + 39, [number_short(value)], size=10, weight=650, color=text_color)
            lines.append("</g>")

    legend_x = left
    legend_y = top + cell * len(domains) + 72
    lines.append(f'<rect x="{legend_x}" y="{legend_y}" width="500" height="24" fill="url(#heat)" stroke="#9AA5B1"/>')
    label(lines, legend_x, legend_y + 52, ["0"], size=13, anchor="start", color="#536273")
    label(lines, legend_x + 250, legend_y + 52, ["log-scaled edge count"], size=13, color="#536273")
    label(lines, legend_x + 500, legend_y + 52, [f"max {maximum:,}"], size=13, anchor="end", color="#536273")
    label(lines, width - 95, legend_y + 8, ["Exact counts and type/body splits:"], size=14, anchor="end", color="#536273")
    label(lines, width - 95, legend_y + 34, ["current_graph/metrics/domain_dependency_matrix.csv"], size=14, anchor="end", color="#536273")
    label(lines, width - 95, height - 30, [f"Audited commit {COMMIT}"], size=13, anchor="end", color="#66717E")
    lines.extend(svg_footer())
    target = OUT / "domain_dependency_heatmap.svg"
    target.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return target


def generate_chain_diagram() -> Path:
    nodes_all = read_csv(CHAINS / "representative_chain_nodes.csv")
    edges_all = read_csv(CHAINS / "representative_chain_edges.csv")
    branches_all = read_csv(CHAINS / "representative_chain_branch_edges.csv")
    nodes = sorted((r for r in nodes_all if r["chain_id"] == "C06"), key=lambda r: int(r["position"]))
    edges = sorted((r for r in edges_all if r["chain_id"] == "C06"), key=lambda r: int(r["step"]))
    branch = next(r for r in branches_all if r["chain_id"] == "C06" and r["target"] == "NumStability.higham12_1_SolverWBound")
    width, height = 2200, 1660
    lines = svg_header(
        width,
        height,
        "CrossChapter LU/solver dependency chain",
        "A verified seven-edge body-proof spine from a CrossChapter solver theorem through Chapter 9 Doolittle results to gamma calculus, plus its direct Chapter 12 semantic branch.",
    )
    label(lines, width / 2, 56, ["Verified CrossChapter LU/solver reuse chain"], size=34, weight=700)
    label(lines, width / 2, 96, [f"Every arrow is a raw elaborated edge; {ORIENTATION}"], size=18, color="#536273")

    box_x, box_w, box_h = 820, 1260, 125
    start_y, gap = 160, 158
    node_positions: dict[str, tuple[float, float]] = {}
    for index, node in enumerate(nodes):
        y = start_y + index * gap
        node_positions[node["name"]] = (box_x, y)
        layer = node["architectural_layer"]
        fill = "#FFF2CC" if layer == "Source" else "#DCEBFA"
        stroke = "#C89B2C" if layer == "Source" else "#2463A5"
        lines.append(f'<rect x="{box_x}" y="{y}" width="{box_w}" height="{box_h}" rx="13" fill="{fill}" stroke="{stroke}" stroke-width="2.5"/>')
        name_lines = wrap_identifier(node["name"], 78)
        label(lines, box_x + 24, y + 31, name_lines[:2], size=16, weight=700, anchor="start", leading=20)
        detail_y = y + 77 if len(name_lines) == 1 else y + 92
        module_short = node["module"].removeprefix("NumStability.")
        label(lines, box_x + 24, detail_y, [f'{node["kind"]} · {layer} · {module_short}:{node["source_line"]}'], size=13, anchor="start", color="#4D5A67")

    for edge in edges:
        sx, sy = node_positions[edge["source"]]
        tx, ty = node_positions[edge["target"]]
        x = sx + box_w / 2
        lines.append(f'<line x1="{x}" y1="{sy + box_h + 3}" x2="{x}" y2="{ty - 30}" stroke="#2463A5" stroke-width="3.5"/>')
        lines.append(f'<polygon points="{x},{ty - 10} {x - 11},{ty - 31} {x + 11},{ty - 31}" fill="#2463A5"/>')
        label(lines, x + 28, (sy + box_h + ty) / 2 + 4, [edge["edge_class"]], size=13, anchor="start", color="#2463A5")

    # The direct Chapter 12 semantic branch from the CrossChapter endpoint.
    branch_x, branch_y, branch_w, branch_h = 60, 215, 635, 180
    lines.append(f'<rect x="{branch_x}" y="{branch_y}" width="{branch_w}" height="{branch_h}" rx="13" fill="#FFF2CC" stroke="#C89B2C" stroke-width="2.5"/>')
    label(lines, branch_x + 22, branch_y + 34, wrap_identifier(branch["target"], 52), size=16, weight=700, anchor="start", leading=20)
    label(lines, branch_x + 22, branch_y + 100, ["theorem · Source · Chapter 12", "solver-error weight predicate"], size=14, anchor="start", color="#4D5A67", leading=22)
    sx, sy = node_positions[branch["source"]]
    branch_tip_x = branch_x + branch_w + 10
    branch_mid_y = branch_y + branch_h / 2
    lines.append(f'<path d="M {sx} {sy + box_h / 2} C 755 {sy + box_h / 2}, 755 {branch_mid_y}, {branch_tip_x + 20} {branch_mid_y}" fill="none" stroke="#2463A5" stroke-width="3.5"/>')
    lines.append(f'<polygon points="{branch_tip_x},{branch_mid_y} {branch_tip_x + 22},{branch_mid_y - 11} {branch_tip_x + 22},{branch_mid_y + 11}" fill="#2463A5"/>')
    label(lines, 752, branch_y + branch_h / 2 - 13, ["type + body"], size=13, anchor="end", color="#2463A5")

    callout_y = 1420
    lines.append(f'<rect x="60" y="{callout_y}" width="635" height="190" rx="14" fill="#F7F8FA" stroke="#CDD3DA"/>')
    label(lines, 82, callout_y + 36, ["Ownership re-check"], size=19, weight=700, anchor="start")
    label(lines, 82, callout_y + 72, ["96 Chapter-12-owned starts →", "6,081 Chapter-9-owned targets:", "0 direct or transitive paths."], size=16, anchor="start", color="#44515F", leading=26)
    label(lines, 82, callout_y + 164, ["The verified composition is CrossChapter-owned."], size=15, weight=650, anchor="start", color="#9D5C14")

    lines.append(f'<rect x="820" y="{callout_y}" width="1260" height="190" rx="14" fill="#EEF5FB" stroke="#AFC8E3"/>')
    label(lines, 846, callout_y + 36, ["Interpretation"], size=19, weight=700, anchor="start")
    label(lines, 846, callout_y + 72, [
        "The endpoint formally consumes a Chapter 9 factorization/solve chain and the Chapter 12",
        "solver-bound predicate; the Chapter 9 proof spine reaches the reusable gamma_mul lemma",
        "(81 direct and 4,739 transitive downstream project consumers). This proves formal reuse,",
        "not source faithfulness, numerical sharpness, or universal API convenience.",
    ], size=15, anchor="start", color="#44515F", leading=25)
    label(lines, width - 120, height - 32, ["Raw rows: current_graph/chains/representative_chain_edges.csv and representative_chain_branch_edges.csv"], size=13, anchor="end", color="#66717E")
    lines.extend(svg_footer())
    target = OUT / "crosschapter_lu_solver_chain.svg"
    target.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return target


def main() -> None:
    OUT.mkdir(parents=True, exist_ok=True)
    outputs = [generate_layer_diagram(), generate_domain_heatmap(), generate_chain_diagram()]
    inputs = [
        METRICS / "layer_dependency_matrix.csv",
        METRICS / "domain_dependency_matrix.csv",
        CHAINS / "representative_chain_nodes.csv",
        CHAINS / "representative_chain_edges.csv",
        CHAINS / "representative_chain_branch_edges.csv",
    ]
    manifest = {
        "schema_version": "numstability-audit-figures/1.0.0",
        "audited_commit": COMMIT,
        "edge_orientation": ORIENTATION,
        "generator": {"path": str(Path(__file__).resolve()), "sha256": sha256(Path(__file__))},
        "inputs": [{"path": str(path.resolve()), "sha256": sha256(path)} for path in inputs],
        "outputs": [{"path": str(path.resolve()), "sha256": sha256(path)} for path in outputs],
        "rendering": "Deterministic UTF-8 SVG generated with Python standard library only; vector format is suitable for A4 scaling.",
    }
    manifest_path = OUT / "manifest.json"
    manifest_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    checksum_lines = [f"{sha256(path)}  figures/{path.name}" for path in outputs + [Path(__file__), manifest_path]]
    (OUT / "SHA256SUMS").write_text("\n".join(checksum_lines) + "\n", encoding="utf-8")
    print(json.dumps({"outputs": [str(path) for path in outputs], "manifest": str(manifest_path)}, indent=2))


if __name__ == "__main__":
    main()
