# Reproducible figures

These vector figures summarize compiled declaration dependencies for commit
`045daf28056a6e4358d5de7c22c7a9d7acc2e80e`. In every figure, an arrow or
matrix cell uses the audit orientation **consumer → dependency**: declaration
`A → B` means `A` directly references `B` in its elaborated type or body/proof.

The files are designed for an A4 thesis page. SVG preserves text and line
quality under scaling; no optional plotting library is required.

## Files

- `layer_dependency_diagram.svg`: compiled cross-layer declaration pairs,
  including intended-direction edges and residual reverse-direction signals.
- `domain_dependency_heatmap.svg`: the complete 22-by-22 domain matrix. Color
  encodes `log10(unique declaration-pair count + 1)`; displayed values are
  compact labels and exact values remain in the raw CSV.
- `crosschapter_lu_solver_chain.svg`: the verified CrossChapter-owned bridge
  from Chapter 12 solver semantics through Chapter 9 Doolittle results to
  `NumStability.gamma_mul`.
- Matching `.png` files are convenience previews rendered from the canonical
  SVGs with macOS `sips`; the SVGs remain the reproducible primary figures.
- `manifest.json`: schema, input/output hashes, commit, and orientation.
- `SHA256SUMS`: hashes of generated figures, generator, and manifest.

## Reproduction

From the audit root:

```sh
python3 figures/generate_figures.py
shasum -a 256 -c figures/SHA256SUMS
```

Optional PNG previews on macOS can be recreated with:

```sh
for figure in figures/*.svg; do sips -s format png "$figure" --out "${figure%.svg}.png"; done
```

The generator uses only Python's standard library. Source artifacts are
`current_graph/metrics/layer_dependency_matrix.csv`,
`current_graph/metrics/domain_dependency_matrix.csv`, and the three selected
chain CSV files under `current_graph/chains/`.

## Interpretation limits

The matrices count elaborated declaration-pair edges, not imports. A reverse
layer edge is a review signal, not automatically an architectural defect.
Connectedness and high fan-in are evidence of internal integration and
consumption, not source faithfulness or public-interface quality.
