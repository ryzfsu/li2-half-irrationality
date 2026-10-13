# Third-party notices

Mathlib is the only direct external Lake dependency; it brings its own pinned
dependencies, including Batteries. This package also includes vendored or
adapted local Lean source, described below. The full Apache-2.0 license text
is in `LICENSES/Apache-2.0.txt`.

## 1. PrimeNumberTheoremAnd

- Upstream: https://github.com/AlexKontorovich/PrimeNumberTheoremAnd
- Commit: `c39a751132c88b6e8080b74c74023fd95b3d8be0`
- Authors: organized by Alex Kontorovich and Terence Tao, with contributors
- License: Apache-2.0 (upstream `LICENSE`, copied unmodified to
  `Li2Lean/Vendor/PNT/LICENSE` and `LICENSES/Apache-2.0.txt`); upstream has no
  NOTICE file.
- Purpose: `chebyshev_asymptotic : θ ~[atTop] id`, consumed only by
  `Li2Lean/Kit/PNTAdapter.lean` to discharge the `hPNT` contract.

Vendored files (copied and modified):

| Upstream path | Local path |
|---|---|
| `PrimeNumberTheoremAnd/Consequences.lean` | `Li2Lean/Vendor/PNT/Consequences.lean` |
| `PrimeNumberTheoremAnd/Wiener.lean` | `Li2Lean/Vendor/PNT/Wiener.lean` |
| `PrimeNumberTheoremAnd/Fourier.lean` | `Li2Lean/Vendor/PNT/Fourier.lean` |
| `PrimeNumberTheoremAnd/Sobolev.lean` | `Li2Lean/Vendor/PNT/Sobolev.lean` |
| `PrimeNumberTheoremAnd/SmoothExistence.lean` | `Li2Lean/Vendor/PNT/SmoothExistence.lean` |
| `PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean` | `Li2Lean/Vendor/PNT/Mathlib/Algebra/Notation/Support.lean` |
| `PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean` | `Li2Lean/Vendor/PNT/Mathlib/Analysis/Asymptotics/Asymptotics.lean` |
| `PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` | `Li2Lean/Vendor/PNT/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` |

Modifications (2026-10-10):

- module paths and imports renamed from `PrimeNumberTheoremAnd.*` to
  `Li2Lean.Vendor.PNT.*`;
- `import Architect` removed, with every `@[blueprint ...]` attribute and
  `blueprint_comment` block (documentation metadata only);
- `Consequences.lean` truncated after `chebyshev_asymptotic`; its unused
  `import PrimeNumberTheoremAnd.Defs` removed (`Defs.lean` is not vendored);
- `Wiener.lean` truncated after `WeakPNT`; `prelim_decay_2`,
  `AbsolutelyContinuous`, `prelim_decay_3`, `decay_alt` removed (the two
  `prelim_decay_*` theorems have no proof upstream and unused by `WeakPNT`);
- a provenance header added to each file.

Retained declarations keep their upstream names (root namespace), statements
and proofs. See also `Li2Lean/Vendor/PNT/NOTICE`.

## 2. openai/math (Catalan 005)

- Upstream: https://github.com/openai/math
- Commit: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
- License: Apache-2.0 (repository-level; the source files carry no per-file
  copyright header)
- No upstream openai/math module is imported. `LogMonomial.lean` is adapted
  local source on the final theorem's import path; the other listed files are
  local work informed by the cited patterns, not imported upstream modules.

| Local file | Relation | Upstream reference |
|---|---|---|
| `Li2Lean/Kit/LogMonomial.lean` | adapted (generic power-log moment lemma `integral_pow_neg_log`) | `lean/OAI/NumberTheory/Catalan/Analysis/LogMonomial.lean` |
| `Li2Lean/Kit/GlobalApproximation.lean` | organization informed by the evaluator pattern; no source copied | Catalan 005 finite potential and interval soundness layers |
| `Li2Lean/P0/PinnedResidualEvaluator.lean` | shape of positive-log cell and interval composition informed; no source copied | `BarrierChebyshevLogFormula.lean`, `BarrierLogRatConstants.lean`, `ManuscriptBarrierFieldIntervals.lean` |
| `Li2Lean/P0/Tube.lean` | generic measure/integral packaging pattern informed (`sweptMeasure`); no source copied | Catalan 005 measure/integral packaging |

Modifications to the adapted file: restricted to the single generic lemma
(with its integrability helper), placed in namespace `Li2Lean.Kit`. The source
has no per-file copyright header; the local file carries the author and
adaptation headers, and this inventory records the upstream path.

## Additional source and technique references

- `Li2Lean/P0/ConfigData.lean:23-29` says its recursive finite-certificate
  packaging pattern was inspired by
  `OAI.Algebra.AuslanderReiten.Cocycles.CocycleCertificate`. The source does
  not record a revision or license for that reference; no code is claimed as
  copied from it.
- `Li2Lean/Kit/ContourKit.lean:7-12,413-419` identifies
  `bjbraams/lean-codes@2b8cba1d0201:Carlson/Jacobi/EllipseContour.lean` and
  Bastiaan J Braams (Apache-2.0) as the source of general technique. The file
  says its Li2 statements and proofs are independently written.
- `Li2Lean/Vendor/PNT/Wiener.lean:2165-2169` retains a source comment saying
  the `WeakPNT` proof was extracted from the `EulerProducts` project for
  adaptation to the Wiener-Ikehara theorem used there. This is transitive
  provenance inherited through PrimeNumberTheoremAnd; the local source does
  not record an EulerProducts revision, URL, or separate license, and this
  package has no direct EulerProducts dependency.

## Build-time tools (not part of the proof build)

`leanprover/comparator` (commit `ca04cfc72b550331658ec314bf47685281bfd4bf`)
is an acceptance-checking tool for `Challenge`/`Solution`; it is no longer a
`require` of `lakefile.toml` and no project file imports it.
