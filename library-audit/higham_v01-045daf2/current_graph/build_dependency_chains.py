#!/usr/bin/env python3
"""Build a checked, stratified set of concrete NumStability dependency chains."""

from __future__ import annotations

import argparse
import csv
import gzip
import hashlib
import json
import re
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path


SCHEMA_VERSION = "numstability-representative-dependency-chains/1.1.0"
EDGE_DIRECTION = "consumer -> dependency"


@dataclass(frozen=True)
class Chain:
    chain_id: str
    title: str
    area: str
    nodes: tuple[str, ...]
    evidence_class: str
    why_reuse: str
    does_not_establish: str
    extra_edges: tuple[tuple[str, str, str], ...] = ()


CHAINS = (
    Chain(
        "C01",
        "Dot-product proof directly reuses the summation error theorem",
        "dot products / summation",
        (
            "NumStability.dotProduct_error_bound",
            "NumStability.fl_sum_error_init",
        ),
        "short direct cross-module and cross-layer reuse",
        "The dot-product forward-error proof has a body edge to the separately owned summation error result.",
        "One direct reference does not establish that the statement is faithful to Higham or that the API is universally convenient.",
    ),
    Chain(
        "C02",
        "Triangular-solve error proof reaches the reusable gamma foundation",
        "triangular solves / rounding",
        (
            "NumStability.forwardSub_backward_error",
            "NumStability.gamma_nonneg",
            "NumStability.FPModel.u_nonneg",
        ),
        "cross-layer chain through a broad-fan-out theorem",
        "The algorithmic backward-error result consumes gamma_nonneg, which itself consumes the floating-point model's unit-roundoff nonnegativity law.",
        "High fan-in measures internal consumption, not user-interface quality or mathematical-source faithfulness.",
    ),
    Chain(
        "C03",
        "Matrix multiplication composes mat-vec, dot-product, summation, and rounding results",
        "matrix multiplication",
        (
            "NumStability.matMul_error_bound",
            "NumStability.matVec_error_bound",
            "NumStability.dotProduct_error_bound",
            "NumStability.fl_sum_error_init",
            "NumStability.FPModel.model_add",
        ),
        "multi-module Algorithms -> Analysis -> FloatingPoint chain",
        "Each adjacent compiled edge shows an algorithmic level reusing the immediately lower error-analysis result, ultimately reaching the primitive addition model.",
        "This selected spine does not enumerate every premise or branch used by the matrix-multiplication theorem.",
    ),
    Chain(
        "C04",
        "Matrix-inversion residual bound reuses mat-vec and dot-product stability",
        "matrix inversion",
        (
            "NumStability.inversion_residual_bound",
            "NumStability.matVec_backward_error",
            "NumStability.dotProduct_backward_stable_x",
            "NumStability.dotProduct_backward_error",
            "NumStability.fl_sum_error_init",
            "NumStability.FPModel.model_add",
        ),
        "deep algorithm-to-rounding chain",
        "The high-level inversion residual result is connected by actual proof edges to reusable mat-vec, dot-product, summation, and primitive-rounding results.",
        "The path proves syntactic proof-term reuse in this elaborated environment, not numerical sharpness or Higham fidelity.",
    ),
    Chain(
        "C05",
        "QR solve bound descends through factorization, Householder, norm, and square-root analyses",
        "QR factorization and solve",
        (
            "NumStability.fl_householderQR_solve_backward_error_gammaHigham_closedInputBounds_of_global_gammaValid",
            "NumStability.fl_householderQR_R_frobNorm_le_gammaHigham_of_global_gammaValid",
            "NumStability.fl_householderQR_witness_explicit_backward_error_gammaHigham_of_global_gammaValid",
            "NumStability.fl_householderQR_witness_explicit_backward_error_of_global_gammaValid",
            "NumStability.fl_householderQRPanel_R_explicit_backward_error",
            "NumStability.fl_householder_first_column_panel_step_error",
            "NumStability.fl_householderConstructApply_matrix_step_error_rect",
            "NumStability.fl_householderConstructApply_appError",
            "NumStability.fl_householderVectorError",
            "NumStability.fl_householderConstructionError",
            "NumStability.fl_householderVector_zero_relative_error",
            "NumStability.fl_householderScale_relative_error",
            "NumStability.fl_norm2_relative_error",
            "NumStability.fl_norm2_relative_error_sqrt_factor",
            "NumStability.FPModel.model_sqrt",
        ),
        "deep 14-edge multi-module algorithmic chain",
        "The endpoint consumes a factorization-error branch whose compiled path crosses QRSolve, Householder QR, matrix-step, one-step, reflector, norm, and floating-point model modules.",
        "It is one dependency spine and does not alone establish completeness of the QR development or external usability.",
        (
            (
                "NumStability.fl_householderQR_solve_backward_error_gammaHigham_closedInputBounds_of_global_gammaValid",
                "NumStability.fl_householderQR_solve_backward_error_gammaHigham_rhsClosedGrowth_of_global_gammaValid",
                "independent right-hand-side/back-substitution proof branch",
            ),
        ),
    ),
    Chain(
        "C06",
        "CrossChapter LU-solver bridge connects Chapter 12 semantics to Chapter 9 Doolittle bounds",
        "LU factorization and solves / Higham Chapters 9 and 12",
        (
            "NumStability.higham12_6_rectRoundedLoop_lu_solve_SolverWBound_source",
            "NumStability.higham9_4_rectRoundedLoop_square_lu_solve_backward_error_source",
            "NumStability.higham9_3_rectRoundedLoop_square_to_LUBackwardError_source",
            "NumStability.higham9_3_rectRoundedLoop_source_backward_error",
            "NumStability.higham9_2_rectRoundedLoopSourceCertificate",
            "NumStability.higham9_2_rectFlDoolittleLEntry_source_residual_abs_le",
            "NumStability.higham9_2_flMulSubFold_div_source_residual_abs_le",
            "NumStability.gamma_mul",
        ),
        "cross-chapter bridge plus seven-edge proof spine",
        "The CrossChapter theorem has a body edge into the Chapter 9 Doolittle closure and a separate type/body edge to the Chapter 12 SolverWBound predicate; the Chapter 9 branch then reaches shared gamma calculus.",
        "There is no path from a Chapter12-owned declaration to a Chapter09-owned declaration; the genuine composition is intentionally owned by CrossChapter, and this says nothing by itself about book faithfulness.",
        (
            (
                "NumStability.higham12_6_rectRoundedLoop_lu_solve_SolverWBound_source",
                "NumStability.higham12_1_SolverWBound",
                "Chapter 12 solver-bound predicate branch",
            ),
            (
                "NumStability.higham12_6_lu_solve_SolverWBound",
                "NumStability.higham9_4_lu_solve_backward_error",
                "parallel abstract-factorization bridge",
            ),
            (
                "NumStability.higham12_6_lu_solve_SolverWBound",
                "NumStability.higham12_1_SolverWBound",
                "parallel bridge's Chapter 12 predicate branch",
            ),
        ),
    ),
    Chain(
        "C07",
        "Chapter 22 refinement reuses a canonical derivative-evaluation error bound",
        "polynomial derivative evaluation / Chapters 22 and 5 provenance",
        (
            "NumStability.Ch22B.ch22b_horner_derivative_error_via_higham5_7",
            "NumStability.fl_hornerDerivativeDesc_snd_forward_error_bound_coupled",
            "NumStability.gamma_nonneg",
        ),
        "Source -> Algorithms -> Analysis reuse",
        "A Chapter 22 source-layer theorem directly delegates to the algorithmic derivative error bound associated by name with Higham 5.7, which consumes the shared gamma theorem.",
        "The target's source-labelled declaration name is a discoverability/ownership review signal; it does not make the result redundant.",
    ),
    Chain(
        "C08",
        "Cholesky solve stability reuses triangular solve and gamma results",
        "Cholesky factorization and solve",
        (
            "NumStability.cholesky_solve_spd_backward_stable",
            "NumStability.cholesky_solve_backward_error",
            "NumStability.cholesky_solve_backward_error_expanded",
            "NumStability.backSub_backward_error",
            "NumStability.backSub_row_tight",
            "NumStability.gamma_mul",
        ),
        "factorization-solver composition across modules",
        "The SPD Cholesky solve endpoint is proved through the generic Cholesky solve bound and then the separately owned back-substitution analysis and gamma product lemma.",
        "This path does not show that every Cholesky result is reused or that all constants are source-faithful.",
    ),
    Chain(
        "C09",
        "Normal equations endpoint composes orthogonality and norm nonnegativity branches",
        "least squares",
        (
            "NumStability.RectLSNormalEquations.isLeastSquaresMinimizer",
            "NumStability.RectLSNormalEquations.residual_orthogonal",
            "NumStability.RectLSNormalEquations.iff_residual_orthogonal",
        ),
        "high-level endpoint with independent lower-result branches",
        "The minimizer theorem directly consumes the normal-equation orthogonality theorem; a separate body edge consumes vecNorm2Sq_nonneg in the matrix-algebra layer.",
        "The two branches document composition for this proof only, not optimal API design.",
        (
            (
                "NumStability.RectLSNormalEquations.isLeastSquaresMinimizer",
                "NumStability.vecNorm2Sq_nonneg",
                "independent squared-norm nonnegativity branch",
            ),
        ),
    ),
    Chain(
        "C10",
        "Condition-number theorem consumes the LAPACK estimator lower bound",
        "condition estimation",
        (
            "NumStability.condOneNumber_ge_scaled_estimator",
            "NumStability.lapackNormEstimator_lower_bound",
        ),
        "direct cross-module use and layer-direction review case",
        "The compiled proof body directly uses the separately owned LAPACK estimator bound.",
        "Because an Analysis-owned theorem depends on an Algorithms-owned theorem, this is also evidence of a residual edge against the intended layer direction, not an architectural strength by itself.",
    ),
    Chain(
        "C11",
        "Matrix norm bound reuses vector norm inequalities and definitions",
        "matrix and vector norms",
        (
            "NumStability.complexMatrixLpNorm_upper_bound_by_columnMax_lpNorm",
            "NumStability.complexVecOneNorm_le_card_rpow_mul_complexVecLpNorm",
            "NumStability.complexVecLpNorm",
        ),
        "cross-module Analysis-layer reuse",
        "The matrix-norm theorem consumes a vector-norm inequality, which in turn references the canonical complex vector p-norm definition.",
        "This local chain does not quantify whether the norm API is discoverable to external users.",
    ),
    Chain(
        "C12",
        "Chapter 24 circulant/FFT endpoint reaches complex arithmetic and primitive rounding",
        "FFT and circulant solvers / Higham Chapter 24",
        (
            "NumStability.higham24_theorem24_3_literal_forward_error_multiple_kappa_u",
            "NumStability.higham24_theorem24_3_literal_quadraticRemainder",
            "NumStability.higham24_theorem24_3_literal_firstOrder",
            "NumStability.higham24_theorem24_3_literal_exactRadii",
            "NumStability.higham24_literalGeneratorPerturbation_norm_le",
            "NumStability.higham24_literalScalingInverse_norm_le",
            "NumStability.higham24_diagonalSolveRelativeError_spec",
            "NumStability.fl_complexDiv_rel_error_model",
            "NumStability.fl_complexDiv_error_bound",
            "NumStability.fl_complexDiv_normSq_error_le",
            "NumStability.fl_complexDiv_im_exact_error_le_gamma4",
            "NumStability.fl_complexDiv_im_error_le_gamma4",
            "NumStability.fl_complexDivDen_error_le_gamma2",
            "NumStability.fl_mul_add_error_le_gamma2",
            "NumStability.FPModel.model_add",
        ),
        "deep Source -> Analysis -> FloatingPoint chain",
        "The Chapter 24 endpoint's proof spine successively reuses structured-stability results, a diagonal-solve specification, reusable complex arithmetic error lemmas, and the primitive floating-point addition law.",
        "The path is evidence of integration, not a validation of Chapter 24 translation accuracy.",
    ),
)


def role(name: str) -> str:
    lower = name.lower()
    if "solverwbound" in lower:
        return "solver error-weight predicate or bound"
    if "lu_solve" in lower or "doolittle" in lower or "lubackwarderror" in lower:
        return "LU/Doolittle factorization or solve backward-error result"
    if "householderqr_solve" in lower:
        return "Householder QR solve backward-error endpoint"
    if "householderqr" in lower:
        return "Householder QR factorization error result"
    if "householder" in lower:
        return "Householder construction/application error result"
    if "cholesky" in lower:
        return "Cholesky factorization/solve stability result"
    if "backsub" in lower or "forwardsub" in lower:
        return "triangular substitution error result"
    if "inversion" in lower:
        return "matrix-inversion residual endpoint"
    if "matmul" in lower:
        return "matrix multiplication error result"
    if "matvec" in lower:
        return "matrix-vector multiplication error result"
    if "dotproduct" in lower:
        return "dot-product computation/error result"
    if "sum_error" in lower:
        return "summation error result"
    if "gamma" in lower:
        return "rounding-error gamma calculus result"
    if "fpmodel.model" in lower or "u_nonneg" in lower:
        return "primitive floating-point model law"
    if "norm" in lower:
        return "vector/matrix norm definition or inequality"
    if "least" in lower or "residual_orthogonal" in lower:
        return "least-squares optimality/orthogonality result"
    if "condition" in lower or "estimator" in lower:
        return "condition-estimator result"
    if "horner" in lower or "derivative" in lower:
        return "polynomial derivative-evaluation error result"
    if "complexdiv" in lower or "mul_add_error" in lower:
        return "complex/scalar arithmetic rounding-error result"
    if "higham24" in lower:
        return "Chapter 24 structured FFT/circulant result"
    return "supporting formal result"


def source_item(name: str, chapter: str) -> str:
    matches = re.findall(r"(?:higham|chapter|ch)(\d{1,2})", name, flags=re.I)
    if matches:
        return ";".join(sorted({f"Higham Chapter {int(x)}" for x in matches}))
    if chapter != "Unassigned":
        return "Higham " + chapter.replace("Chapter", "Chapter ")
    return ""


def excerpt(meta: dict[str, str], worktree: Path) -> str:
    path = meta.get("source_path", "")
    start_text = meta.get("selection_start_line", "")
    if not path or not start_text:
        return ""
    try:
        lines = (worktree / path).read_text(encoding="utf-8").splitlines()
        start = int(start_text) - 1
        pieces: list[str] = []
        for line in lines[start : min(len(lines), start + 7)]:
            pieces.append(line.strip())
            joined = " ".join(pieces)
            if ":= by" in joined or re.search(r":=\s*$", joined) or " where" in joined:
                break
        joined = re.sub(r"\s+", " ", " ".join(pieces)).strip()
        if len(joined) > 360:
            joined = joined[:357] + "..."
        return joined
    except (OSError, ValueError, IndexError):
        return ""


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        while block := handle.read(1024 * 1024):
            digest.update(block)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--metrics", type=Path, required=True)
    parser.add_argument("--edges", type=Path, required=True)
    parser.add_argument("--compiled-raw-edges", type=Path, required=True)
    parser.add_argument("--metadata", type=Path, required=True)
    parser.add_argument("--worktree", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--top-level-report", type=Path)
    args = parser.parse_args()
    if not re.fullmatch(r"[0-9a-f]{40}", args.source_commit):
        raise ValueError("--source-commit must be a lowercase 40-hex Git object id")
    args.output.mkdir(parents=True, exist_ok=True)

    metrics: dict[str, dict[str, str]] = {}
    with gzip.open(args.metrics, "rt", newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            metrics[row["name"]] = row
    metadata: dict[str, dict[str, str]] = {}
    with args.metadata.open(newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            metadata[row["name"]] = row
    edges: dict[tuple[str, str], dict[str, str]] = {}
    adjacency: dict[str, set[str]] = defaultdict(set)
    with gzip.open(args.edges, "rt", newline="", encoding="utf-8") as handle:
        for row in csv.DictReader(handle):
            pair = (row["source"], row["target"])
            if pair in edges:
                raise ValueError(f"duplicate project pair {pair}")
            edges[pair] = row
            adjacency[pair[0]].add(pair[1])

    needed_nodes = {name for chain in CHAINS for name in chain.nodes}
    needed_nodes.update(source for chain in CHAINS for source, _, _ in chain.extra_edges)
    needed_nodes.update(target for chain in CHAINS for _, target, _ in chain.extra_edges)
    missing_nodes = sorted(needed_nodes - set(metrics))
    if missing_nodes:
        raise ValueError(f"chain nodes missing from graph: {missing_nodes}")
    for chain in CHAINS:
        for pair in zip(chain.nodes, chain.nodes[1:]):
            if pair not in edges:
                raise ValueError(f"{chain.chain_id}: missing direct edge {pair}")
        for source, target, _ in chain.extra_edges:
            if (source, target) not in edges:
                raise ValueError(f"{chain.chain_id}: missing extra edge {(source, target)}")

    selected_pair_keys = {
        pair for chain in CHAINS for pair in zip(chain.nodes, chain.nodes[1:])
    }
    selected_pair_keys.update(
        (source, target)
        for chain in CHAINS
        for source, target, _ in chain.extra_edges
    )
    compiled_raw_rows: dict[tuple[str, str], tuple[int, dict[str, str]]] = {}
    with gzip.open(
        args.compiled_raw_edges, "rt", newline="", encoding="utf-8"
    ) as handle:
        for data_row_number, row in enumerate(csv.DictReader(handle), 1):
            pair = (row["source"], row["target"])
            if row["target_scope"] == "project" and pair in selected_pair_keys:
                if pair in compiled_raw_rows:
                    raise ValueError(f"duplicate selected pair in compiled raw graph: {pair}")
                compiled_raw_rows[pair] = (data_row_number, row)
    missing_raw_pairs = selected_pair_keys - set(compiled_raw_rows)
    if missing_raw_pairs:
        raise ValueError(
            f"selected pairs missing from compiled raw graph: {sorted(missing_raw_pairs)}"
        )
    for pair in selected_pair_keys:
        processed = edges[pair]
        _, raw = compiled_raw_rows[pair]
        for column in (
            "source", "source_module", "target", "target_module",
            "occurs_in_type", "occurs_in_body", "same_module",
        ):
            if processed[column] != raw[column]:
                raise ValueError(
                    f"processed/raw mismatch for {pair}, column {column}: "
                    f"{processed[column]!r} != {raw[column]!r}"
                )

    summary_fields = [
        "chain_id", "title", "area", "evidence_class", "path_length_edges",
        "path_node_count", "start_declaration", "end_declaration", "modules_spanned",
        "layers_spanned", "domains_spanned", "chapters_spanned",
        "start_total_transitive_downstream_consumer_declarations",
        "start_total_transitive_downstream_consumer_modules",
        "start_downstream_domains", "start_downstream_chapters", "why_formal_reuse",
        "what_it_does_not_establish", "edge_direction", "raw_edge_artifact",
    ]
    node_fields = [
        "chain_id", "position", "name", "kind", "refined_kind", "module",
        "source_path", "source_line", "architectural_layer", "domain", "chapter",
        "associated_source_item", "authorship_class", "mathematical_role",
        "normalized_statement_excerpt", "direct_consumer_declarations",
        "transitive_downstream_consumer_declarations", "transitive_downstream_consumer_modules",
        "transitive_downstream_domains", "transitive_downstream_chapters",
    ]
    edge_fields = [
        "chain_id", "step", "source", "source_module", "target", "target_module",
        "occurs_in_type", "occurs_in_body", "edge_class", "same_module",
        "cross_layer", "cross_domain", "cross_chapter", "dependency_relation",
        "raw_artifact", "raw_row_key",
    ]
    extra_fields = edge_fields + ["branch_role"]
    raw_edge_fields = [
        "chain_id", "edge_role", "step", "source", "source_module", "target",
        "target_module", "target_scope", "occurs_in_type", "occurs_in_body",
        "same_module", "compiled_raw_artifact", "compiled_raw_data_row_number",
    ]
    summary_rows: list[dict[str, object]] = []
    node_rows: list[dict[str, object]] = []
    edge_rows: list[dict[str, object]] = []
    extra_rows: list[dict[str, object]] = []
    raw_edge_rows: list[dict[str, object]] = []
    for chain in CHAINS:
        chain_metrics = [metrics[name] for name in chain.nodes]
        start = chain_metrics[0]
        summary_rows.append({
            "chain_id": chain.chain_id,
            "title": chain.title,
            "area": chain.area,
            "evidence_class": chain.evidence_class,
            "path_length_edges": len(chain.nodes) - 1,
            "path_node_count": len(chain.nodes),
            "start_declaration": chain.nodes[0],
            "end_declaration": chain.nodes[-1],
            "modules_spanned": len({row["module"] for row in chain_metrics}),
            "layers_spanned": ";".join(sorted({row["layer"] for row in chain_metrics})),
            "domains_spanned": ";".join(sorted({row["domain"] for row in chain_metrics})),
            "chapters_spanned": ";".join(sorted({row["chapter"] for row in chain_metrics if row["chapter"] != "Unassigned"})),
            "start_total_transitive_downstream_consumer_declarations": start["transitive_downstream_consumer_count"],
            "start_total_transitive_downstream_consumer_modules": start["transitive_downstream_module_count"],
            "start_downstream_domains": start["transitive_downstream_domains"],
            "start_downstream_chapters": start["transitive_downstream_chapters"],
            "why_formal_reuse": chain.why_reuse,
            "what_it_does_not_establish": chain.does_not_establish,
            "edge_direction": EDGE_DIRECTION,
            "raw_edge_artifact": str(args.edges),
        })
        for position, (name, row) in enumerate(zip(chain.nodes, chain_metrics), 0):
            node_rows.append({
                "chain_id": chain.chain_id,
                "position": position,
                "name": name,
                "kind": row["kind"],
                "refined_kind": row["refined_kind"],
                "module": row["module"],
                "source_path": row["source_path"],
                "source_line": row["source_line"],
                "architectural_layer": row["layer"],
                "domain": row["domain"],
                "chapter": row["chapter"],
                "associated_source_item": source_item(name, row["chapter"]),
                "authorship_class": row["authorship_class"],
                "mathematical_role": role(name),
                "normalized_statement_excerpt": excerpt(
                    {**metadata[name], "source_path": row["source_path"]}, args.worktree
                ),
                "direct_consumer_declarations": row["direct_project_consumer_count"],
                "transitive_downstream_consumer_declarations": row["transitive_downstream_consumer_count"],
                "transitive_downstream_consumer_modules": row["transitive_downstream_module_count"],
                "transitive_downstream_domains": row["transitive_downstream_domains"],
                "transitive_downstream_chapters": row["transitive_downstream_chapters"],
            })
        for step, pair in enumerate(zip(chain.nodes, chain.nodes[1:]), 1):
            row = edges[pair]
            edge_rows.append({
                "chain_id": chain.chain_id,
                "step": step,
                "source": pair[0],
                "source_module": row["source_module"],
                "target": pair[1],
                "target_module": row["target_module"],
                "occurs_in_type": row["occurs_in_type"],
                "occurs_in_body": row["occurs_in_body"],
                "edge_class": row["edge_class"],
                "same_module": row["same_module"],
                "cross_layer": row["cross_layer"],
                "cross_domain": row["cross_domain"],
                "cross_chapter": row["cross_chapter"],
                "dependency_relation": "direct adjacent edge; chain start-to-later node is transitive when step > 1",
                "raw_artifact": str(args.edges),
                "raw_row_key": pair[0] + " -> " + pair[1],
            })
            raw_number, raw = compiled_raw_rows[pair]
            raw_edge_rows.append({
                "chain_id": chain.chain_id,
                "edge_role": "path",
                "step": step,
                **{column: raw[column] for column in (
                    "source", "source_module", "target", "target_module",
                    "target_scope", "occurs_in_type", "occurs_in_body", "same_module",
                )},
                "compiled_raw_artifact": str(args.compiled_raw_edges),
                "compiled_raw_data_row_number": raw_number,
            })
        for source, target, branch_role in chain.extra_edges:
            row = edges[(source, target)]
            extra_rows.append({
                "chain_id": chain.chain_id,
                "step": "branch",
                "source": source,
                "source_module": row["source_module"],
                "target": target,
                "target_module": row["target_module"],
                "occurs_in_type": row["occurs_in_type"],
                "occurs_in_body": row["occurs_in_body"],
                "edge_class": row["edge_class"],
                "same_module": row["same_module"],
                "cross_layer": row["cross_layer"],
                "cross_domain": row["cross_domain"],
                "cross_chapter": row["cross_chapter"],
                "dependency_relation": "direct branch edge",
                "raw_artifact": str(args.edges),
                "raw_row_key": source + " -> " + target,
                "branch_role": branch_role,
            })
            raw_number, raw = compiled_raw_rows[(source, target)]
            raw_edge_rows.append({
                "chain_id": chain.chain_id,
                "edge_role": "branch",
                "step": "branch",
                **{column: raw[column] for column in (
                    "source", "source_module", "target", "target_module",
                    "target_scope", "occurs_in_type", "occurs_in_body", "same_module",
                )},
                "compiled_raw_artifact": str(args.compiled_raw_edges),
                "compiled_raw_data_row_number": raw_number,
            })

    for filename, fields, rows in (
        ("representative_dependency_chains.csv", summary_fields, summary_rows),
        ("representative_chain_nodes.csv", node_fields, node_rows),
        ("representative_chain_edges.csv", edge_fields, edge_rows),
        ("representative_chain_branch_edges.csv", extra_fields, extra_rows),
        ("representative_chain_raw_compiled_rows.csv", raw_edge_fields, raw_edge_rows),
    ):
        with (args.output / filename).open("w", newline="", encoding="utf-8") as handle:
            writer = csv.DictWriter(handle, fieldnames=fields)
            writer.writeheader()
            writer.writerows(rows)

    chapter12 = {
        name for name, row in metrics.items()
        if row["module"].startswith("NumStability.Source.Higham.Chapter12")
    }
    chapter09 = {
        name for name, row in metrics.items()
        if row["module"].startswith("NumStability.Source.Higham.Chapter09")
    }
    queue = deque(sorted(chapter12))
    reached = set(chapter12)
    found: str | None = None
    while queue and found is None:
        source = queue.popleft()
        for target in adjacency[source]:
            if target in chapter09:
                found = target
                break
            if target not in reached:
                reached.add(target)
                queue.append(target)
    chapter_check = {
        "schema_version": SCHEMA_VERSION,
        "source_commit": args.source_commit,
        "edge_direction": EDGE_DIRECTION,
        "chapter12_owned_start_declarations": len(chapter12),
        "chapter09_owned_target_declarations": len(chapter09),
        "union_reachable_from_chapter12_owned_declarations": len(reached),
        "union_reachable_excluding_chapter12_starts": len(reached - chapter12),
        "chapter09_owned_target_reached": found,
        "direct_or_transitive_paths_found": 0 if found is None else 1,
        "interpretation": "No direct/transitive consumer-to-dependency path from a Chapter12-owned declaration to a Chapter09-owned declaration was found. The verified LU/solver bridge is owned by Source.Higham.CrossChapter.LUSolverWeights.",
    }
    (args.output / "chapter09_chapter12_path_recheck.json").write_text(
        json.dumps(chapter_check, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    strongest = next(chain for chain in CHAINS if chain.chain_id == "C06")
    with (args.output / "strongest_chain.dot").open("w", encoding="utf-8") as handle:
        handle.write('digraph "CrossChapter LU solver reuse" {\n  rankdir="LR";\n')
        handle.write('  graph [bgcolor="white"]; node [shape=box, style="rounded,filled", fillcolor="#EEF4FB", fontname="Helvetica", fontsize=9];\n')
        for index, name in enumerate(strongest.nodes):
            row = metrics[name]
            label = name.replace("NumStability.", "", 1) + "\\n" + row["module"].replace("NumStability.", "", 1)
            handle.write(f'  n{index} [label="{label}"];\n')
        for index in range(len(strongest.nodes) - 1):
            edge = edges[(strongest.nodes[index], strongest.nodes[index + 1])]
            handle.write(f'  n{index} -> n{index + 1} [label="{edge["edge_class"]}"];\n')
        handle.write("}\n")

    lines = [
        "# Concrete dependency chains",
        "",
        f"Schema: `{SCHEMA_VERSION}`. Every arrow is `{EDGE_DIRECTION}`: the declaration on the left directly references the declaration on the right in its elaborated type and/or body. Every adjacent edge below was validated against the compiled raw graph; start-to-later-node relationships are transitive when the path has more than one edge.",
        "",
        "These paths establish formal reuse and compositional typechecking in the recorded Lean environment. They do not independently establish faithfulness to Higham, correctness of an informal translation, numerical sharpness, or universal API convenience.",
        "",
        "## Stratified summary",
        "",
        "| ID | Area | Edges | Modules | Layers | Evidence |",
        "|---|---|---:|---:|---|---|",
    ]
    for row in summary_rows:
        lines.append(
            f"| {row['chain_id']} | {row['area']} | {row['path_length_edges']} | {row['modules_spanned']} | {row['layers_spanned']} | {row['evidence_class']} |"
        )
    lines += [
        "",
        "The strongest high-level endpoint spine is C05: it composes a QR-solve bound with a separate right-hand-side/back-substitution proof branch and a 14-edge factorization/Householder/norm/rounding path. C06 is the strongest cross-chapter example: a CrossChapter-owned theorem has independent direct branches into the Chapter 9 factorization development and the Chapter 12 solver-bound predicate.",
        "",
        "## Compact downstream-reach table",
        "",
        "Counts are for the chain's first declaration. Domain and chapter names are given in full in `representative_dependency_chains.csv`; this table reports their counts to remain readable.",
        "",
        "| ID | Downstream declarations | Downstream modules | Downstream domains | Downstream chapters |",
        "|---|---:|---:|---:|---:|",
    ]
    for row in summary_rows:
        domains = [value for value in str(row["start_downstream_domains"]).split(";") if value]
        chapters = [value for value in str(row["start_downstream_chapters"]).split(";") if value]
        lines.append(
            f"| {row['chain_id']} | {row['start_total_transitive_downstream_consumer_declarations']} | {row['start_total_transitive_downstream_consumer_modules']} | {len(domains)} | {len(chapters)} |"
        )
    lines += ["", "## Chapter 9 / Chapter 12 re-check", "", chapter_check["interpretation"], ""]
    for chain in CHAINS:
        lines += [f"## {chain.chain_id}: {chain.title}", "", f"Why this is reuse: {chain.why_reuse}", "", "```text"]
        for index, name in enumerate(chain.nodes):
            prefix = "" if index == 0 else "  -> "
            lines.append(prefix + name)
        lines += ["```", "", f"What it does not establish: {chain.does_not_establish}", ""]
        relevant_edges = [row for row in edge_rows if row["chain_id"] == chain.chain_id]
        lines += ["| Step | Edge class | Consumer module | Dependency module |", "|---:|---|---|---|"]
        for row in relevant_edges:
            lines.append(f"| {row['step']} | {row['edge_class']} | `{row['source_module']}` | `{row['target_module']}` |")
        branches = [row for row in extra_rows if row["chain_id"] == chain.chain_id]
        if branches:
            lines += ["", "Additional direct branches:", ""]
            for row in branches:
                lines.append(f"- `{row['source']}` -> `{row['target']}` ({row['edge_class']}): {row['branch_role']}.")
        lines.append("")
    lines += [
        "## Raw evidence",
        "",
        "`representative_chain_nodes.csv` is the normative per-node table satisfying the declaration-kind, module, current file/line, layer, chapter/source-item, mathematical-role, normalized-statement, authorship, and downstream-reach fields. `representative_chain_edges.csv` is the normative per-edge table for direct/transitive status and type/body/both flags. `representative_chain_raw_compiled_rows.csv` preserves the exact selected rows and data-row numbers from the validated compiled raw graph. `representative_chain_branch_edges.csv` records the independent proof branches used in the interpretation.",
        "",
    ]
    dependency_chains_text = "\n".join(lines)
    (args.output / "DEPENDENCY_CHAINS.md").write_text(
        dependency_chains_text, encoding="utf-8"
    )
    if args.top_level_report is not None:
        args.top_level_report.write_text(dependency_chains_text, encoding="utf-8")

    summary = {
        "schema_version": SCHEMA_VERSION,
        "source_commit": args.source_commit,
        "builder_sha256": sha256(Path(__file__)),
        "input_sha256": {
            str(path): sha256(path)
            for path in (args.metrics, args.edges, args.compiled_raw_edges, args.metadata)
        },
        "edge_direction": EDGE_DIRECTION,
        "chains": len(CHAINS),
        "selected_path_edges": len(edge_rows),
        "selected_branch_edges": len(extra_rows),
        "all_selected_nodes_exist": True,
        "all_selected_edges_directly_verified": True,
        "all_selected_edges_exactly_matched_to_compiled_raw_rows": True,
        "chapter09_chapter12_recheck": chapter_check,
        "limitations": [
            "Selection is stratified and evidence-driven but not a random sample.",
            "A path is formal reuse, not source-faithfulness evidence.",
            "Downstream counts include all project declarations, including generated/private names; authorship is reported separately.",
            "Path/domain/chapter labels are deterministic ownership classifications and source-name signals.",
        ],
    }
    (args.output / "summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    checksums = []
    for path in sorted(args.output.iterdir()):
        if path.is_file() and path.name != "SHA256SUMS":
            checksums.append(f"{sha256(path)}  {path.name}")
    (args.output / "SHA256SUMS").write_text("\n".join(checksums) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
