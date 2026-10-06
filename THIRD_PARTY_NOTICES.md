# Third-party notices

This file records attribution for code adapted or backported from other
projects. It does not replace the applicable license texts.

The files listed below carry Apache-2.0 notices. The Apache License,
Version 2.0 is available at
[`LICENSES/Apache-2.0.txt`](LICENSES/Apache-2.0.txt).

## mathlib4: Lindemann–Weierstrass development

The following files state that they were adapted from mathlib4 PR #28013 at
commit `5abb7c68488b527e4d7ecf5d7bbe085db8d2a388`:

- `NumStability/Upstream/Lindemann/AlgebraicPart.lean`
- `NumStability/Upstream/Lindemann/Basic.lean`
- `NumStability/Upstream/Lindemann/FinsuppQuotient.lean`
- `NumStability/Upstream/Lindemann/SymmetricEval.lean`

They retain:

> Copyright (c) 2022 Yuyang Zhao. All rights reserved.
> Authors: Yuyang Zhao

Upstream: <https://github.com/leanprover-community/mathlib4/pull/28013>

## mathlib4: monoid-algebra compatibility API

`NumStability/Upstream/Lindemann/MonoidAlgebraCompat.lean` states that it
backports APIs from:

- mathlib4 PR #36762,
  <https://github.com/leanprover-community/mathlib4/pull/36762>,
  commit `cbdf82d6b083de3a961936dbea002185060b46c3`;
- mathlib4 PR #37797,
  <https://github.com/leanprover-community/mathlib4/pull/37797>,
  commit `d8255d64167683fc82500473c77d08285b6804ed`.

The file identifies mathlib4 PR #28013 at commit
`5abb7c68488b527e4d7ecf5d7bbe085db8d2a388` as its compatibility target.

It retains:

> Copyright (c) 2017 Johannes Hölzl. All rights reserved.
> Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
