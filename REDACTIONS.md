# Public-release redactions

This branch is the public copy of the private branch `ten_task_benchmark` (commit
`06e2dda52`), published as a single commit without history. Its content is
identical except for the systematic replacements below, made so that no
local path, host name, user name or IP address appears. Only text files were
edited; no binary file contained any of these strings.

| Replaced | Placeholder | Occurrences |
|---|---|---:|
| user directory on the data drive (`/hdd/<user>`) | `<data-drive>` | 2,181 |
| per-user runtime directory (`/run/user/<uid>`) | `<run-user>` | 578 |
| temporary directory (`/tmp`, `/private/tmp`) | `<tmp>` | 523 |
| host name of the execution machine | `<host>` | 463 |
| IP address in the download banner of source PDFs | `<ip>` | 125 |
| SSH user and address of the execution machine | `<user>@<host-ip>` | 2 |

541 files were edited. SHA-256 digests recorded inside the run records
refer to the original files and therefore do not match the edited ones, and
helper scripts that connected to the execution machine need its address
supplied again. Generic paths inside the benchmark sandbox (for example
`/workspace`, `/home/bench`, `/run/highambench`) and standard system paths
were kept.

## Files left out

65 files are not included in this public copy. They contain text
extracted from the source PDFs (publisher pages, including pages of Higham's
book for task H20-8), which may not be redistributed. They remain in the
private archive. No file cited by the thesis is among them.

- `benchmark/runs/P14-SHIFTED-SOFTMAX/R0/audits/83a46baa94f0f181320d669336ade132663e8f3793e0d9afaa2dba36b90c1dc0/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-SHIFTED-SOFTMAX/R0/audits/83a46baa94f0f181320d669336ade132663e8f3793e0d9afaa2dba36b90c1dc0/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-SHIFTED-SOFTMAX/R1/audits/0428d21fdf7f7cf54e969d8287a58088432a2900ea247b3c7beeb1b99fc65857/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-SHIFTED-SOFTMAX/R1/audits/0428d21fdf7f7cf54e969d8287a58088432a2900ea247b3c7beeb1b99fc65857/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-SHIFTED-SOFTMAX/R0/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/CAST08-FIXED3/R0/audits/7bff89f19177d2c5cb56e2565dcc1d051a36c3db401bb32b3c284d202964d1cc/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-SHIFTED-SOFTMAX/R1/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/CAST08-FIXED3/R0/audits/7bff89f19177d2c5cb56e2565dcc1d051a36c3db401bb32b3c284d202964d1cc/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/CAST08-FIXED3/R0/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/CAST08-FIXED3/R1/audits/dc50fc3f0795ba6edc8cfa1d1ca8af805b95b4db3c95c8316b829e9906b2c314/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/CAST08-FIXED3/R1/audits/dc50fc3f0795ba6edc8cfa1d1ca8af805b95b4db3c95c8316b829e9906b2c314/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/CAST08-FIXED3/R1/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/CAST08-PROP3.2/R0/audits/59a03e84f4317ecb81f46adce83009b757e2e40b01db3812a0fee008d26f2ca0/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/CAST08-PROP3.2/R0/audits/59a03e84f4317ecb81f46adce83009b757e2e40b01db3812a0fee008d26f2ca0/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/CAST08-PROP3.2/R1/audits/93d32619dac894beb5b8ff69ea7810e49d893da3ef60b4f082a5f690344e4291/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/CAST08-PROP3.2/R0/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/CAST08-PROP3.2/R1/audits/93d32619dac894beb5b8ff69ea7810e49d893da3ef60b4f082a5f690344e4291/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/CAST08-PROP3.2/R1/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/RUMP12-THM3.4/R0/audits/75eafe5473b57767917edd6103db8a36a05cf8a413f7cfe887f8827c12994f01/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/RUMP12-THM3.4/R0/audits/75eafe5473b57767917edd6103db8a36a05cf8a413f7cfe887f8827c12994f01/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/RUMP12-THM3.4/R0/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/RUMP12-THM3.4/R0/proof-submissions/01/formalizer/events.jsonl`
- `benchmark/runs/RUMP12-THM3.4/R1/audits/d8cd9dc706b7967499c6d1ff5efa290fb3496b3a7408e724d7332d0a725f9120/roles/adjudicator/try-01/artifacts/events.jsonl`
- `benchmark/runs/RUMP12-THM3.4/R1/audits/d8cd9dc706b7967499c6d1ff5efa290fb3496b3a7408e724d7332d0a725f9120/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/RUMP12-THM3.4/R1/audits/d8cd9dc706b7967499c6d1ff5efa290fb3496b3a7408e724d7332d0a725f9120/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/RUMP12-THM3.4/R1/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/P14-T2/R0/audits/e856f8e9f5d5d74b9e6e1cf2ca5f1c46b2dc52559be09925968fe578cdeba3ee/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-T2/R0/audits/e856f8e9f5d5d74b9e6e1cf2ca5f1c46b2dc52559be09925968fe578cdeba3ee/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-T2/R0/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/P14-T2/R1/audits/b9345a25220702bc210e984ec696289aedd645027f3ad56a9f55f6a48acf2b54/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-T2/R1/audits/b9345a25220702bc210e984ec696289aedd645027f3ad56a9f55f6a48acf2b54/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-T2/R1/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/HI21-LEM2.2/R0/audits/49902039bc2e5b353a2622b2d8d0cee6951a9a5debc3c4286b4370fc37737bd8/roles/adjudicator/try-02/artifacts/events.jsonl`
- `benchmark/runs/HI21-LEM2.2/R0/audits/49902039bc2e5b353a2622b2d8d0cee6951a9a5debc3c4286b4370fc37737bd8/roles/adjudicator/try-01/artifacts/events.jsonl`
- `benchmark/runs/HI21-LEM2.2/R0/audits/49902039bc2e5b353a2622b2d8d0cee6951a9a5debc3c4286b4370fc37737bd8/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/HI21-LEM2.2/R0/audits/49902039bc2e5b353a2622b2d8d0cee6951a9a5debc3c4286b4370fc37737bd8/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/HI21-LEM2.2/R0/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/HI21-LEM2.2/R1/audits/5c0403080bb47f7cc2e48243ca3d3f227d5c6c44d1fb8363122e5e3eb05681db/roles/adjudicator/try-01/artifacts/events.jsonl`
- `benchmark/runs/HI21-LEM2.2/R1/audits/5c0403080bb47f7cc2e48243ca3d3f227d5c6c44d1fb8363122e5e3eb05681db/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/HI21-LEM2.2/R1/audits/5c0403080bb47f7cc2e48243ca3d3f227d5c6c44d1fb8363122e5e3eb05681db/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/HI21-LEM2.2/R1/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/P14-LOGSUMEXP/R0/audits/f23c39c11d95ea8a4ce0c780375e0e5202e3f918f1e3cd342d9113727fe5a6ac/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-LOGSUMEXP/R0/audits/f23c39c11d95ea8a4ce0c780375e0e5202e3f918f1e3cd342d9113727fe5a6ac/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-LOGSUMEXP/R0/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/P14-LOGSUMEXP/R1/audits/370e23a8f53b7bae366e660ed395c636c51edd95aac91c5a429f3ea2a9ad491a/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-LOGSUMEXP/R1/audits/370e23a8f53b7bae366e660ed395c636c51edd95aac91c5a429f3ea2a9ad491a/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-LOGSUMEXP/R1/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/H20-8/R0/audits/a8354776d5dd54b81282b58cb2a939b4452f8f429d79138aac14db34a619849e/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/H20-8/R0/audits/a8354776d5dd54b81282b58cb2a939b4452f8f429d79138aac14db34a619849e/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/H20-8/R0/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/H20-8/R1/audits/d4c37db5b3d9bd52e307f234b023ea7e368b86979bd2df7f5635ea5cb8fbd671/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/H20-8/R1/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/CAST08-PROP3.1/R0/audits/27cd07a743c3530342c561f10f1bbfbc6d750caf3c3751251ad9ae4e4059f2f7/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/H20-8/R1/audits/d4c37db5b3d9bd52e307f234b023ea7e368b86979bd2df7f5635ea5cb8fbd671/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/CAST08-PROP3.1/R0/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/CAST08-PROP3.1/R1/audits/bc39b5a8c08f2afd761113e7cfdd562c3a7cd52917022ed402d3404692dce7dc/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/CAST08-PROP3.1/R0/audits/27cd07a743c3530342c561f10f1bbfbc6d750caf3c3751251ad9ae4e4059f2f7/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/CAST08-PROP3.1/R1/audits/bc39b5a8c08f2afd761113e7cfdd562c3a7cd52917022ed402d3404692dce7dc/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/CAST08-PROP3.1/R1/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/P14-T1/R0/audits/365fe6f80abf57f2fd3d592a28e86c517c55d144e219d5be7d6385138b3fd5bc/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-T1/R0/submissions/01/formalizer/events.jsonl`
- `benchmark/runs/P14-T1/R0/audits/365fe6f80abf57f2fd3d592a28e86c517c55d144e219d5be7d6385138b3fd5bc/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-T1/R1/audits/4598172610655576a604f93f9444c561248061092309cc58788c1d7c650c23eb/roles/roundtrip-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-T1/R1/audits/4598172610655576a604f93f9444c561248061092309cc58788c1d7c650c23eb/roles/direct-judge/try-01/artifacts/events.jsonl`
- `benchmark/runs/P14-T1/R1/submissions/01/formalizer/events.jsonl`
