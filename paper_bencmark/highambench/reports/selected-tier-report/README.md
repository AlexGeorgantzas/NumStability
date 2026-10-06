# Selected-tier N/L results report

The LaTeX report uses:

- T1 and T2 task and tier means from `../live-r11/`;
- T3 task and tier means from `../combined-r09-r10/`.

`report.tex` is the source and `report.pdf` is the compiled report. The PNGs in
`assets/` are lossless, high-resolution crops of the corresponding source SVG
diagrams. P16-T3 is omitted from the T3 task diagrams and tier mean because its
target is documented false.

All selected token records are incomplete, so every reported token value is an
observed lower bound.

Task attempts are isolated from one another: each uses fresh agent and workspace
state and sees only its own task context, never another task's prompt,
conversation, search trace, or solution.

Some T1 L runs finish sooner yet use more observed tokens because NumStability
search and read outputs enlarge the context processed again on later model
calls, including cached input, while theorem reuse shortens proof development
and Lean checking.

The report includes elapsed time, observed tokens, and submitted physical LOC;
proof-region LOC is intentionally omitted.
