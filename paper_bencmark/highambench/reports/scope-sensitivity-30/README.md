# Thirty-task scope sensitivity

This directory is a **post-run sensitivity copy** of the preserved [38-task tier-colored report](../metric-comparison/tier_metric_comparison.pdf), not a new benchmark run. It removes every task from papers P02, P17, P20, P33, P35, and P40, while retaining all three P15 tasks, including P15-T3. The exact eight excluded task IDs, the original PDF hash, and the reason for the sensitivity check are pinned in [scope_manifest.json](scope_manifest.json).

The [PDF](scope_sensitivity_30.pdf) contains the 30-task tier-colored versions of all 12 usage measures, a full-versus-filtered comparison, and source notes. [retained_tasks.csv](retained_tasks.csv) lists all plotted points; [association_change.csv](association_change.csv) gives full and filtered correlations for every usage measure and outcome. Rebuild with `python3 make_report.py` from this directory. The builder verifies the source CSV hashes via the preserved analysis code and verifies the preserved original PDF hash before writing the copy.

The pooled correlations and median gains rise after filtering, but that does not validate the exclusion: the papers were chosen after observing results. Unexpected tier fit is a reason to inspect mathematical scope, not proof of exclusion. T1/T2 and T3 were also measured with different runners, so tier and campaign remain confounded.
