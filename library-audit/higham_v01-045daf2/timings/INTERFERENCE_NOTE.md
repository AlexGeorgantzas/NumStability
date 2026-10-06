# Timing interference and replacement rule

An unrelated, read-only Python source-range scan overlapped the conservative
window `2026-09-03 12:05:30–12:06:40 EEST (+03:00)`.  Original timing rows 25
and 26 overlapped that window.  They remain in `fresh_module_timings.csv` for a
complete audit trail but are excluded from all reported percentiles and
hotspots.  Both modules were rerun after a quiet period using identical fresh
output commands.  `fresh_module_timings_effective.csv` replaces only those two
rows with the quiet reruns from `fresh_module_timing_reruns.csv`.

The rerun harness used the same deterministic diagnostic filenames as the
first attempts, so the two original stderr/stdout logs were overwritten by the
authoritative quiet reruns. The original timing values remain in
`fresh_module_timings.csv`; the effective rerun logs and all other original
logs remain available. This logging limitation does not affect the effective
values, but is recorded rather than concealed.
