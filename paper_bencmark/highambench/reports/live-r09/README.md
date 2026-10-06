# Live N/L measurement charts

Generated 2026-09-20 17:23 UTC from **117 fully sealed pairs**: 84 with two accepted proofs, 3 with at least one scored failure, and 30 affected by infrastructure. **24/39 tasks** have three accepted N/L repetitions and a plotted mean.

Each diagram has T1, T2, and T3 sections. A task gets adjacent N/L bars only when all three repetitions in both conditions have accepted proofs and all metric values are present. Bars show separate arithmetic means of those three runs, not L-minus-N differences; incomplete, failed, and infrastructure-affected tasks show why no mean is plotted. Each task panel has its own scale. See [task averages](task_averages.csv) and [raw completed pairs](completed_pairs.csv) for absolute values.

- [Elapsed time](time.svg)
- [Observed tokens](tokens.svg)
- [Final source lines](physical_loc.svg)
- [Proof-region LOC](proof_loc.svg)

Observed token totals are incomplete for 195 sealed attempts; any mean containing one is a lower bound, not exact total spending. Time is to first accepted proof. Physical and proof-region LOC are measured lexically from the submitted accepted-proof file only: an import command counts as one submitted line, while no internal line from an imported Mathlib or NumStability module or declaration is included. Infrastructure incidents and scored failures are not averaged.

Scored-failure pairs: `P16-T3-rep-01`, `P16-T3-rep-02`, `P16-T3-rep-03`.

Infrastructure-affected pairs: `P09-T3-rep-01`, `P14-T1-rep-02`, `P15-T2-rep-01`, `P15-T3-rep-02`, `P29-T1-rep-01`, `P29-T1-rep-03`, `P29-T2-rep-02`, `P32-T3-rep-01`, `P32-T3-rep-03`, `P33-T1-rep-01`, `P33-T1-rep-02`, `P33-T1-rep-03`, `P34-T3-rep-01`, `P34-T3-rep-02`, `P34-T3-rep-03`, `P35-T3-rep-01`, `P35-T3-rep-02`, `P35-T3-rep-03`, `P36-T3-rep-01`, `P36-T3-rep-02`, `P36-T3-rep-03`, `P37-T3-rep-01`, `P37-T3-rep-02`, `P37-T3-rep-03`, `P39-T3-rep-01`, `P39-T3-rep-02`, `P39-T3-rep-03`, `P40-T3-rep-01`, `P40-T3-rep-02`, `P40-T3-rep-03`. These need fresh attempts before comparison.

`P16-T3` has a documented false target. Its failed attempts remain in the raw pair CSV and are not interpreted as ordinary proof performance or averaged.

Task-validity and library-use caveats are tracked separately in [measurement progress](../../MEASUREMENT_PROGRESS.md).
